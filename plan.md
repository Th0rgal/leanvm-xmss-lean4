# LeanVM XMSS 1400 — plan d’exécution Maxwell / Hindsight

## 1. Mission et contrat de réussite

Réimplémenter en Lean 4 le chemin complet de production de preuve nécessaire à :

```sh
cargo leanvm aggregate --xmss 1400 --log-inv-rate 1 --repeat 3
```

Compiler le code Lean via `lean-native` de `Th0rgal/turbo-lean`, puis optimiser automatiquement les sources et les transformations du compilateur avec Turbo-Lean MCP. Cible CPU x86-64 uniquement, avec chemins AVX2 et AVX-512 ; aucun GPU, TPU ou accélérateur distant dans le calcul mesuré.

Le travail est une réimplémentation du prouveur, pas un appel à son implémentation Rust depuis Lean. Rust reste l’oracle différentiel et le vérifieur indépendant. Un adaptateur de fichiers/processus et le runtime générique sont permis ; déplacer le calcul cryptographique vers un FFI Rust/C écrit à la main ne satisfait pas la mission.

### Référence fournie

| Mesure | Référence |
|---|---:|
| Proving time | 1.15 s |
| Peak memory | 8.633 GiB |
| Proof size | 359.5 KiB |
| Verifying | 7.449 ms |
| Cycles VM | 1 569 346 |
| MEMORY | 2^23.109 cellules réellement utilisées |
| BYTECODE | 2^18.467 instructions non paddées |
| TOTAL_COMMITTED | 2^26.801 mots avant padding logique |

Les parts d’instructions sont XOR 26.7 %, SET 18.9 %, MUL 18.3 %, KECCAK 16.6 %, DEREF 12.3 %, JUMP 7.2 %. Ce ne sont PAS des parts de temps hôte : ne pas en déduire un budget Amdahl sans profilage.

**Contrat principal :** prouveur Lean complet accepté par le vérifieur Rust de référence non modifié ; temps moyen et RSS strictement inférieurs à 1.15 s et 8.633 GiB, et supériorité reproductible face au Rust relancé sur la même machine. Taille de preuve et temps de vérification sont des garde-fous sans régression significative, pas des gains à fabriquer en modifiant le protocole. Avec format et paramètres fixes, une taille identique est normale ; accélérer le prouveur n’accélère pas automatiquement un vérifieur inchangé. Rapporter séparément toute demande de domination stricte des quatre mesures : elle n’est ni présumée possible ni implicitement satisfaite.

Objectifs de marge, non promesses : <= 1.0 s et <= 8.0 GiB, puis poursuite sur le front de Pareto. Ne jamais annoncer ces objectifs comme atteints sans artefacts et mesures.

## 2. Périmètre exact et invariants

- 1400 signatures leanXMSS ; leanSPHINCS = 0, blobs = 0, children = [], aucune récursion de preuves enfants à implémenter pour ce workload.
- Garder le guest unifié, son bytecode, son digest et sa compilation à point fixe identiques à la révision Rust gelée. L’absence d’enfants ne permet pas de remplacer le programme par un guest XMSS simplifié incompatible.
- Réimplémenter les opérations et chemins effectivement exécutés et tous les sous-protocoles nécessaires à leur preuve. Les tables de six instructions et les règles de layout publiques restent identiques.
- Garder `log_inv_rate = 1`, sécurité 128 bits, constantes WHIR, grinding, transcript, ordre des challenges, domaines de séparation, Merkle, sérialisation et public statement inchangés.
- Aucune réduction de sécurité, suppression de contrôles, sous-comptage de signataires, preuve précalculée ou réutilisation du résultat d’une itération précédente.
- La génération de clés/signatures de benchmark et la compilation initiale du guest sont hors chronométrage comme dans Rust. Un export initial du bytecode, des signatures et des constantes publiques est permis. Les hints, l’exécution et le witness dépendant des signatures sont recalculés dans chaque appel chronométré.
- Accepter d’autres entrées de même forme : tester des signatures et messages distincts du cache public. Spécialiser les paramètres est permis ; coder les réponses du benchmark en dur ne l’est pas.
- Les clés `mock` du cache Rust sont un mécanisme de génération restreint à une plage de feuilles ; ne pas transformer leur présence en permission de contourner la vérification XMSS.

## 3. État réellement observé

### Sources locales inspectées

Racine des dépôts de recherche :

```text
/var/lib/sandboxed-node/.scratch/8b709be6-05d7-42fb-9b3f-0437c98643ac/opencode/
  repos/leanVM/
  repos/turbo-lean/
  prior/flock-fast/Orchestrator/
  prior/snark-fast-lean/
  refs/maxwell/docs/flows/
  refs/orb-library/skill/maxwell/references/
```

Ces chemins sont des ressources de cette session, pas des dépendances portables pour les workers. Au démarrage, matérialiser les sources requises dans le workspace durable de l’implémentation et enregistrer les commits exacts, sous-modules, versions et hashes des fixtures. Ne pas utiliser une branche mobile comme oracle.

Hindsight : consultation réussie de la banque `thomas`, notes Maxwell et antécédents SIMD/LeanNative, complétées par les playbooks et projets antérieurs ci-dessus. Réutiliser leurs méthodes, pas leurs hypothèses cryptographiques. Lire les secrets uniquement par les outils autorisés et ne jamais les copier dans les artefacts, prompts de workers ou snapshots.

### État d’avancement vérifié (`xmss-hub-unified` et profil Amdahl P0)

- **Hub unifié acquis (`0 sorryAx`, `audit-spec PASS`)** dans `/var/lib/sandboxed-node/.scratch/b2c1c0b9-4d89-47e7-ab06-c94b999a4cce/opencode/xmss-hub-unified/LeanVmXmss` : `Field`, `Transcript`, `Merkle`, `Keccak` (primitif), `Vm` (1 146 537 cycles exacts), `Xmss`, `Layout`, `Pcs/{Ntt,Commit}`, `Witness` + engagement WHIR L0 exact sur `xmss1400` (`5fc4b406...` / `ce8a26e0...`), ainsi que **`Bus` + `Constraints`** (`Model/Bus/Scalar.lean`, `Proofs/Bus/Refinement.lean`, `Tests/Bus/Check.lean`) prouvés et validés sur les 4 cas synthétiques (`syn_tiny`, `syn_jump`, `syn_deref`, `syn_keccak`).
- **Deux seules briques protocolaires manquantes avant le premier `verify() == OK` bout-en-bout** :
  1. `Keccak GKR` (`crates/keccak_gkr` + réduction `crates/leanvm_core/src/keccak` + RMFE + `q_keccak`),
  2. `RingSwitch + StackOpen WHIR + Wire Codec` (`ring_switch.rs`, `stack_open.rs`, WHIR multi-rondes + sérialisation `EthereumProof` + CLI `aggregate`).
- **Profil Rust P0 mesuré sur Boat `xlarge` (`leanVM@59c2984`, moyenne `1.624 s`, RSS `5.896 GiB`) — priorités Amdahl ($f \ge 10\%$)** :
  - `prove_bus` : `448.0 ms` (27.0 %)
  - `keccak_reduction` : `438.0 ms` (26.4 %)
  - `pcs_open` : `269.0 ms` (16.2 %)
  - `commit_ntt_merkle` : `198.0 ms` (11.9 %)
  - `execute_program` : `193.0 ms` (11.6 %)
  - `prove_constraints` : `58.5 ms` (3.5 %) et `build_witness` : `53.8 ms` (3.2 %) — hors cible de passes compilateur dédiées (élimination de copies uniquement).

### Matériel Boat vérifié empiriquement

Une VM Boat `xlarge` a exposé `AMD EPYC 4585PX 16-Core Processor`, 16 CPU logiques, un thread par cœur visible, un socket et un nœud NUMA. RAM visible ~31 GiB, ~28 GiB disponibles. Tarif observé : 0.20 USD/h. VM d’inspection détruite, destruction confirmée.

Flags observés : AVX2, AVX512F/BW/VL/DQ, AVX512VBMI/VBMI2, VPCLMULQDQ, PCLMULQDQ, GFNI, VAES, BMI2, SHA, AVX512BITALG/VPOPCNTDQ. Zen 5 constitue la cible principale ; vérifier à nouveau sur chaque VM, car le placement futur peut différer.

`lscpu` a annoncé L1d 1 MiB, L1i 1 MiB, L2 8 MiB, L3 256 MiB, avec 16 instances. **Ce sont des données de topologie virtualisée à confirmer**, pas la preuve qu’un bloc contigu de 256 MiB constitue un cache partagé exploitable. Mesurer la résidence, la bande passante et les tailles de tuiles ; ne pas fonder le plan mémoire sur cette seule annonce.

Utiliser `provisioning_mode="worker"`, snapshot `light` ou snapshot doré contrôlé. Le mode raw sans image propre explicite a été refusé. L’image inspectée fournissait turbo-lean 0.1.0 et lean-native v0.5.0 ; `maxwell` n’était pas installé. Vérifier les versions réelles et les commandes `--help` avant exécution. L’hôte local inspecté n’a pas AVX-512 : y faire l’analyse et les contrôles légers, pas les mesures SIMD finales.

## 4. Cartographie du pipeline à porter

### Références leanVM prioritaires

| Domaine | Sources relatives au dépôt leanVM |
|---|---|
| CLI, mesures, RSS, taille | `bins/leanvm/src/benchmark.rs`, `report.rs`, `crates/bench/src/lib.rs` |
| Agrégation et hints | `crates/rec_aggregation/src/aggregation/node.rs`, `guest.rs`, `proof.rs`, `statement.rs`, `deferred.rs` |
| Fixtures de signatures | `crates/rec_aggregation/src/signers_cache.rs`, `crates/signatures/src/lean_xmss/` |
| Exécution et preuve | `crates/leanvm_core/src/cpu/mod.rs`, `witness.rs`, `tables.rs`, `constraints.rs`, modules bus/leaf et layout |
| Arithmétique | `crates/primitives/src/field/gf2_64.rs`, `gf2_64x3.rs`, `f192x8.rs` |
| Keccak GKR | `crates/keccak_gkr/src/{lib,prover,witness,rmfe,basis,power,kernels,products_gfni,table_gfni}.rs` |
| PCS | `crates/leanvm_core/src/pcs.rs`, `crates/pcs/src/{stack_open,ring_switch,whir,whir_config,merkle}.rs`, `ntt/` |
| Vérification indépendante | `crates/verifier/`, `python-verifier/verifier.py`, vecteurs EthLib vendored |

### Séquence obligatoire

1. Charger les 1400 `(pubkey, message, signature)` et le bytecode gelé ; construire le statement trié/dédupliqué et les hints comme `aggregate_with_stats`.
2. Exécuter le guest : PC/frame pointer, mémoire write-once, flux de hints, états et opérations XOR/MUL/SET/DEREF/JUMP/KECCAK. Rejeter les lectures non contraintes et les entrées invalides.
3. Construire directement le stack `q` de colonnes K, les tables, bus et données Keccak. Conserver les placements, hauteurs et colonnes virtuelles publiques.
4. Amorcer Fiat–Shamir avec le digest du programme et l’entrée publique ; annoncer tailles et rate avant tout engagement/challenge concerné.
5. Engager `q` via WHIR : NTT additive binaire, codeword entrelacé et Merkle Keccak.
6. Prouver l’équilibre des bus MEMORY/STATE/BYTECODE, puis le sumcheck groupé des six tables. Préserver les plages disjointes de puissances pour contraintes et les trois puissances partagées pour bus.
7. Lier l’entrée publique et les claims de colonnes ; réduire les permutations Keccak-f[1600] avec GKR, RMFE et arithmétique binaire. Les états intermédiaires segmentés et le layout `q_keccak` font partie du protocole.
8. Ring-switcher les claims nécessaires et effectuer **une unique ouverture WHIR empilée**, incluant les claims Keccak. Ne pas ajouter un PCS séparé pour simplifier le portage.
9. Sérialiser la preuve et son enveloppe `EthereumProof` ; recalculer correctement le deferred bytecode claim ; faire accepter la preuve par le vérifieur de référence.

### Arithmétique exacte

- K = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1), réduction basse `0x1B`. Addition = XOR, multiplication = produit sans retenue puis réduction. Ce n’est ni un corps premier ni la tour GF(2^128) de projets antérieurs.
- E = K[y] / (y^3 + y + 1), trois mots de 64 bits. Définir embeddings, bases, ordre des limbs et encodage little-endian explicitement.
- Reproduire les produits mixtes E×K, carrés, inverses, interpolation, tables eq, produits non réduits et accumulateurs paresseux avec leurs bornes exactes.
- Le référence F192x8 utilise disposition planaire, Karatsuba à six produits K sans retenue et réduction différée. Porter cette structure après le modèle scalaire, avec preuve de correspondance ; ne pas supposer qu’un port scalaire auto-vectorisé retrouvera son débit.
- Les twiddles et domaines NTT restent dans K ; les niveaux WHIR profonds sont E-valués et utilisent les produits mixtes.

## 5. Architecture Maxwell : quatre couches et preuves de raffinement

Organisation proposée, à adapter aux conventions du dépôt d’implémentation sans créer de doublons :

```text
LeanVmXmss/
  Spec/        Field, Keccak, Xmss, VM, Layout, Transcript, Bus, Sumcheck, PCS, Aggregate
  Model/       versions exécutables pures et sérialisation
  Flat/        slices, colonnes, bitplanes, buffers et ordonnancement
  Native/      noyaux Lean compilables lean-native et dispatch CPU
  Proofs/      raffinements, invariants et contrats de traduction
  Tests/       vecteurs et mutants
  Bench/       Tier A et pilote complet Tier B
```

- **S1 Spec :** contrats indépendants de l’implémentation optimisée, relations d’exécution et fonctions mathématiques. Définir l’entrée attendue, pas seulement « le vérifieur accepte quelque chose ».
- **S2 Executable Model :** code Lean pur de référence, avec preuve S2 ≃ S1 et tests différentiels Rust/Python.
- **S3 Flat Layout :** représentations compactes et mutations contrôlées, preuve de décodage vers S2, indices/bornes, disjonction, initialisation, durée de vie et absence de lecture non écrite.
- **S4 Native/SIMD :** noyaux et ordonnancement parallèles, équivalence lane par lane et réduction déterministe vers S3 ; compilation native avec artefacts inspectables.

La preuve de raffinement de l’implémentation n’est pas une nouvelle preuve complète de sécurité cryptographique du protocole. Documenter les hypothèses reprises de leanVM et les frontières de confiance : kernel Lean, frontend, runtime, LLVM/assembleur, matériel. Ne pas présenter des tests machine comme un théorème sur le binaire.

### Audit de spécification à trois portes

Avant optimisation de chaque composant :

1. `posWitness` : exemple non trivial satisfaisant le contrat, plus cas limites.
2. `negWitness` : mutants rejetés — bit de signature/message/public key, opcode/PC, colonne, sortie Keccak, ordre de transcript, racine Merkle, point deferred, index/longueur et trailing bytes.
3. `turbo_audit_spec` / `turbo-lean audit-spec`, puis revue indépendante/quorum : non-vacuité, aucune hypothèse qui contient déjà la conclusion, aucun prédicat artificiellement affaibli.

Zéro `sorryAx`, zéro `native_decide` dans les preuves acceptées, zéro axiome ad hoc/trustCompiler. Auditer transitivement les dépendances des théorèmes, pas uniquement les fichiers modifiés. Les évaluations natives de test sont distinctes des preuves.

## 6. LeanNative : réutiliser, puis combler les écarts démontrés

### État constaté, à ne pas sur-vendre

- **LNIR et reconnaissance d’intrinsèques (`trustedGfSimdIntrinsicOp` / `canonClmul64Repr`)** : `lean-native` possède déjà `clmul64`, `clmul64Hi`, `gf2Affine`, `eor3` et abaisse en **~1.6 s** des définitions externes `clmul64`/`clmul64Hi` de forme canonique en `@llvm.x86.pclmulqdq` ! Attention : `==` sur `UInt64` dans `Init.Data.UInt.Package` tire `Classical.choice` via `instLinearOrderPackageUInt64` si `import Lean` est actif (alors que `decide (x = 1)` ou l’audit autorisant `[propext, Quot.sound, Classical.choice]` standard Lean, ou un découpage `@[noinline]` granulaire, évite le blocage).
- **Anti-pattern n°1 (interdit) : dépliage `@[inline]` monolithique dans un seul module `lean-native`** : empiler 64/63 `nativeSelect` `@[inline]` (`nativeClmulLo`/`Hi`) dans 14–18 déclarations chaînées (`nativeTestInv`, Karatsuba) fait exploser quadratiquement l’arbre LCNF/LNIR (>15 min CPU à 99 %). Toujours : (a) privilégier les intrinsèques canoniques reconnues par `lean-native` (`pclmulqdq`), ou (b) marquer `@[noinline]` les briques atomiques (`mul`, `square`, `clmulLo`, `clmulHi`) pour compiler chaque déclaration en quelques secondes.
- Le backend texte `Backend/LLVM.lean` émet du PCLMUL scalaire x86 pour clmul bas/haut. Cela ne garantit pas une émission VPCLMUL 512 bits.
- `gf2Affine` y est une implémentation logicielle sur l’octet bas ; son nom ne prouve pas l’émission GFNI.
- L’opérateur binaire `eor3 a b` a actuellement une convention empaquetée (`a XOR (b >> 32) XOR (b & 0xffffffff)`), pas trois opérandes arbitraires UInt64. Ne pas l’utiliser comme contrat pour Keccak 64 bits sans extension correcte. Des peepholes XOR sont un chemin distinct.
- Le lowering typé `Backend/LLVMLower.lean` rejette ces opérations crypto dans le fragment inspecté. Les garanties de ce lowering ne s’étendent donc pas automatiquement au backend texte plus large.
- Les flags x86 de base incluent AVX2/PCLMUL ; un profil de coût Zen 5 n’est pas une preuve que tous les flags, vecteurs, ABI et chemins de linkage sont activés.
- `Driver/BuildExe.lean` passe notamment par l’émission C Lean puis LLVM et applique un gate de support des appels. Il faut démontrer que les symboles du binaire final exécutent réellement les noyaux optimisés attendus, pas simplement produire un fichier LNIR non lié.
- La règle sans `import Lean` concerne les spécifications/gates autonomes et les nouvelles sémantiques vérifiées ; les drivers frontend existants importent légitimement Lean. Ne pas prétendre que tout le dépôt est actuellement indépendant du frontend.

### Preuve de faisabilité précoce obligatoire

Avant de porter tout le protocole, compiler depuis une source Lean réelle : produit K avec réduction, produit E, boucle sur buffer, partition parallèle et petite sérialisation. Inspecter ABI, symboles liés, LLVM et désassemblage, puis exécuter sur Boat. Rejeter tout fallback silencieux, appel non résolu ou export non utilisé. Si le compilateur ne couvre pas le chemin nécessaire, ouvrir une tâche bloquante explicite avec contrat et test minimal ; ne pas cacher le problème derrière un wrapper Rust.

### Extensions candidates, seulement justifiées par le profil

1. CLMUL vectoriel 128/256/512 avec extraction bas/haut et recombinaison : VPCLMULQDQ effectue des produits dans des lanes 128 bits ; 512 bits ne signifie pas huit produits 64×64 indépendants dans une seule instruction. Définir le packing et compter le coût réel.
2. Types/ops vectoriels LNIR et lowering typé, preuves de raffinement lane par lane, gestion du tail et fallback AVX2.
3. GFNI affine pour transpositions, tables RMFE et transformations linéaires binaires déjà chaudes dans `keccak_gkr`. Une affine GFNI 8×8 ne calcule pas à elle seule une transformation arbitraire 64×64 ni une multiplication générale GF(2^64) : prouver la décomposition en blocs et permutations.
4. Véritable opérateur ternaire bitvector / reconnaissance prouvée de XOR et chi pour `vpternlogq`, constantes immédiates, rotations et permutations Keccak.
5. Slices exclusives, alignement, élimination des bornes/RC, fusion de boucles et allocation réutilisée, uniquement sous invariants prouvés.
6. Runtime parallèle générique avec partition disjointe, ordonnancement déterministe et barrières minimales ; aucune logique spécifique de preuve cryptographique cachée dans le runtime.

Pour chaque extension : sémantique pure totale, support codec/évaluation/coûts, théorème de transformation ou validation symbolique sound, preuves des contrats backend pris en charge, mutants, tests différentiels et inspection des instructions réellement émises. Pour les passes, employer `validateTranslationDecl` et les mécanismes existants ; `evalCode` sur 64 états et `declScalarCost` sont des filtres supplémentaires, jamais une preuve universelle. Un état « testé » ne devient pas « prouvé » par changement d’étiquette.

Interdire les passes spéculatives hors corpus : `corpus_hits > 0`, hot path réellement mesuré, part f >= 10 % ou justification de goulot global mesuré. Avec accélération locale s, gain maximal attendu = 1 / ((1-f) + f/s). Revenir au pipeline après chaque gain local.

## 7. Plan performance CPU et mémoire

### Priorité 1 : trafic mémoire et représentation

Le stack brut correspond déjà à environ 0.87 GiB de mots K avant arrondis de lanes ; ce n’est pas 8.633 GiB de trace minimale. Mesurer les autres résidents et leurs chevauchements : image mémoire VM, tables virtuelles, bitplanes Keccak, colonnes E de sumcheck, codeword NTT, arbres Merkle, poids d’ouverture, scratch et copies de signatures.

- Écrire les colonnes directement à leur placement final, sans construire puis recopier des tableaux complets.
- Garder les colonnes K en mots de 8 octets ; ne promouvoir en E que les états réellement nécessaires aux tours actifs.
- Conserver les colonnes virtuelles comme telles ; ne pas matérialiser une deuxième copie des lanes Keccak déjà dans q.
- Exploiter le padding logique absent et les lanes réellement engagées exactement comme Rust, avec zéros de tête corrects au hashing.
- Réutiliser des arenas par phase, slices disjointes et buffers de capacité bornée ; libérer les structures au dernier lecteur. Mesurer le high-water RSS du processus, y compris warmup et rétention d’allocateur.
- Comparer conservation/reconstruction des codewords, NTT par tuiles/cosets et arbres Merkle coupés. Rust possède déjà `Keep::BeforeDeep` / `Keep::Nothing` et un seuil de 1 GiB : ce sont des éléments à égaler et calibrer, pas des nouveautés à créditer au port.
- Fusionner production NTT et absorption Merkle quand l’ordre de données le permet ; n’émettre les openings qu’après les challenges correspondants.
- Objectif de scratch par worker, budget global et tableau de vie des allocations obligatoires ; aucun swap, compression opaque ou processus auxiliaire cachant le RSS.

### Priorité 2 : noyaux arithmétiques et Keccak

- K/E : comparer multiplication scalaire, Karatsuba, accumulation différée et versions planaires x8 ; produits E×K spécialisés ; inversion batch si le protocole autorise la réorganisation locale.
- Sumchecks : fusion message/fold quand compatible avec la dépendance du challenge ; accumulations sans réduction répétée ; regroupement des produits partageant une colonne comme la référence.
- Keccak VM et Merkle : plusieurs états en parallèle, XOR/chi ternaires, rotations et layout adapté au nombre de registres. Mesurer la pression des 25 lanes et les spills.
- Keccak GKR : bitplanes, packs RMFE, produits GFNI et folding des premières rondes sont distincts de la permutation Keccak classique ; porter et profiler les deux familles.
- NTT additive : tuilage, twiddles K, produits mixtes des niveaux E et chemin de reconstruction pour requêtes ; ne pas substituer une FFT de corps premier.

### Priorité 3 : parallélisme

Balayer 1/2/4/8/16 workers ; blocs de travail suffisamment gros, réduction déterministe XOR et pas de parallélisme imbriqué incontrôlé. Épinglage et politique CPU identiques entre Rust et Lean. Comparer AVX2 et AVX-512, fréquence effective et débit bout en bout : ne pas supposer un facteur deux par largeur. Dispatch AVX-512 seulement si toutes les features requises sont présentes ; tester explicitement le chemin AVX2. La victoire principale est certifiée sur Boat, la portabilité AVX2 sur machine compatible.

## 8. Boucle Turbo-Lean MCP, hygiène des gates et mémoire Hindsight

### Hygiène stricte de la boucle chaude (éliminer les goulots de la gate avant ceux du code)

Les campagnes P1 ont démontré que le premier goulot d’étranglement n’est pas le calcul cryptographique mais **l’infrastructure de vérification elle-même** quand un script Python recompile 4 fois le même graphe à froid. Règles obligatoires pour toute gate (`verify.py`, `build_native.py`, scripts de shard et d’intégration) :

1. **100 % `turbo-lean` / `lean-native` en boucle chaude — zéro `lake` froid ni `shutil.rmtree` sur `.lake/build`** : conserver un **unique cache `.olean` + `.c.o.export` incrémental** dans la racine du projet Lean. Ne jamais copier l’arbre source vers un répertoire temporaire vidé à chaque passe (`prepare_mcp_checked.py` destructif interdit en boucle d’itération ; n’effectuer un rebuild propre en salle blanche qu’une seule fois à la certification finale d’une phase).
2. **Un seul démon `turbo-lean mcp` persistant par session de gate** : ouvrir un unique processus JSON-RPC stdio (`initialize` une fois) et enchaîner tous les appels (`turbo_fast_check`, `turbo_agent_step`, `turbo_audit_spec`, `turbo_check`, `turbo_pr_verify`, `turbo_status`) sur ce même canal chaud. Interdiction de spawner/tuer un processus `turbo-lean mcp` neuf par déclaration ou par fichier.
3. **Découpage modulaire `@[noinline]` et intrinsèques canoniques pour `lean-native`** :
   - Garder tous les fichiers compilés **sous la racine du projet** (`lean-native` rejette légitimement les fichiers hors racine comme `/tmp/...`).
   - Ne jamais empiler des chaînes profondes de fonctions `@[inline]` bit-à-bit (ex. 64 `nativeSelect` inlinés dans 18 étapes d’inversion ou Karatsuba) dans une seule unité LNIR : marquer `@[noinline]` les briques atomiques (`clmulLo`, `clmulHi`, `mul`, `square`, `karatsuba`) **ou** exposer la forme canonique reconnue par `trustedGfSimdIntrinsicOp` (`clmul64` / `clmul64Hi` -> `@llvm.x86.pclmulqdq`), afin que `lean-native build-exe` termine en **1.5–7 s** par binaire au lieu de >15 min.
   - Dans les audits d’axiomes (`collectAxioms`), attention au piège Lean 4.35 : `==` (`BEq`) sur `UInt64` lorsque `Init.Data.UInt.Package` est chargé tire `Classical.choice` via `instLinearOrderPackageUInt64` ; utiliser `decide (x = y)` (`instDecidableEqUInt64`, zéro axiome) dans le code devant rester strictement dans `[propext, Quot.sound]`, et exclure les wrappers `run_cmd` de test qui importent `Lean` du périmètre des théorèmes du modèle.
4. **Pas de triple compilation redondante** : produire `.olean` + `.c` + `.c.o.export` incrémentalement une seule fois par module modifié (hash SHA-256 des sources + dépendances), puis appeler `lean-native build-exe` directement sur la cible native.

### Outils MCP et séquence automatisée

Démarrer le serveur MCP stdio fourni par la version gelée, découvrir ses schémas réels et employer :

- `turbo_fast_check` pour les rejets rapides/counterexamples ;
- `turbo_agent_step` pour la boucle ciblée déclaration par déclaration ;
- `turbo_audit_spec` pour les portes de spécification ;
- `turbo_check` pour validation kernel et fermeture des dépendances ;
- `turbo_pr_verify` pour la vérification intégrée lorsqu’elle s’applique au workflow ;
- `turbo_status` et `AgentAnalyticsLedger` pour erreurs, couverture, coûts et convergence.

Le serveur MCP ne remplace pas le pilote de mesure : le contrôleur automatise la séquence suivante, sans demander une décision humaine à chaque candidat :

```text
profil et hypothèse -> candidat source/passe -> fast-check -> preuve/kernel (MCP persistant, cache chaud)
-> build lean-native (unités @[noinline] / intrinsèques canoniques, <= quelques secondes) -> différentiel natif
-> Tier A -> Tier B -> conserver si gain robuste et aucun recul de validité/sécurité -> enregistrer
```

Toute proposition garde son parent de référence. Stocker hash des sources, outil, flags, preuve, layout, seed, dimensions et artefacts binaires ; résultats et échecs non sélectionnés restent consultables. Relancer les candidats gagnants indépendamment pour limiter le biais de sélection. `verified=false`, timeout ou résultat incomplet = rejet/attente, jamais succès.

Utiliser exclusivement turbo-lean pour la boucle de vérification/build Lean et lean-native pour le natif ; pas de `lake` en boucle interne. Les builds Rust de référence peuvent employer Cargo et les changements Rust de turbo-lean leurs contrôles prescrits. Découvrir les commandes exactes dans les README/AGENTS et `--help`, sans inventer des options.

Hindsight avant chaque lot : rappeler les décisions, erreurs similaires et contraintes du composant. Après un résultat reproductible : mémoriser hypothèse, contre-exemple ou gain, environnement, hashes et raison de rejet/acceptation via `save_source` (`is_agent_summary=true`, `auteur="agent:..."`, `type_de_source="agent_summary"`), sans jamais altérer les pages de notes manuscrites de Thomas ni présenter une synthèse d’agent comme une décision de Thomas. Ne pas utiliser le souvenir d’un succès passé comme preuve de réussite du candidat courant.

## 9. Protocole expérimental

### Geler et reproduire avant optimisation

1. Sur Boat xlarge, enregistrer commits Rust/Turbo-Lean, toolchain Lean/Rust/LLVM, OS, CPU/features/topologie/caches, limites cgroup, RAM, affinité, nombre de threads, flags et environnement.
2. Exécuter la commande Rust exacte et sauvegarder stdout/stderr, échantillons non arrondis, preuve finale et taille exacte en octets. Générer le cache une fois et en vérifier intégrité/distinctivité.
3. Faire une campagne tracée séparée pour Execute/Build witness/Commit/Bus/Constraints/Keccak/PCS open ; profiler cycles, instructions, cache misses et bande passante si les permissions le permettent. Le tracing change le coût : distinguer diagnostic et résultat officiel.
4. Si les chiffres Rust diffèrent des valeurs fournies, publier les deux. Ne pas prétendre battre l’implémentation par simple différence de matériel ou de révision.

### Mesures à reproduire exactement

- Proving = appel complet `aggregate_with_stats`, y compris clones/entrée et travail de préparation interne, pas uniquement `cpu::prove` ou un noyau.
- Initialisation pool, warmup bytecode et chargement/génération signatures sont hors timer dans Rust ; appliquer le même périmètre à Lean.
- Un warmup complet écarté puis trois passes mesurées ; moyenne arithmétique, pas minimum ou médiane. Reprendre le cooldown de la CLI de la révision gelée (défaut inspecté : 2 s), hors timer.
- Vérification : trois passes sur la preuve retenue finale, sans warmup supplémentaire ni cooldown, même vérifieur portable et mêmes contrôles d’agrégation.
- RSS = `ru_maxrss` du processus complet, y compris setup, warmup et vérification. Lancer chaque campagne dans un processus frais ; mesurer aussi le RSS de phase pour diagnostiquer, sans le substituer au chiffre officiel. Si plusieurs processus sont utilisés, publier le pic agrégé de leur arbre/cgroup.
- Taille = sérialisation de la preuve VM seule via `proof_size()`, pas enveloppe entière ni simple compteur de scalaires. Publier également l’enveloppe totale, mais ne pas la confondre avec 359.5 KiB.
- Les affichages 1.15/8.633/359.5/7.449 sont arrondis : comparer en secondes/octets exacts dès que la référence locale est disponible.

### Deux niveaux de preuve de performance

**Tier A :** noyaux isolés sur dimensions réellement extraites de XMSS 1400, données variées et tails ; CV <= 3 %, taille d’échantillon adaptée ; vérification de sortie à chaque lot, désassemblage et trafic mémoire. Un microbench ne valide pas le workload complet.

**Tier B :** prouveur natif complet pour 1400 entrées, export de preuve, vérification Rust indépendante inchangée, checks négatifs et mesures ci-dessus. Alterner Rust/Lean sans concurrents sur la VM ; au moins cinq paires de campagnes finales, chacune avec repeat 3. Présenter toutes les moyennes, dispersion et intervalle de confiance du gain ; demander une amélioration supérieure au bruit, pas un record isolé. Aucun déchargement distant pendant le timer.

Le vérifieur Python doit être employé sur un corpus interopérable avec l’export de la révision gelée ; confirmer son schéma avant usage. À défaut d’adaptateur compatible, annoncer cette limitation et ne pas revendiquer une double validation. Le Rust portable reste le gate d’acceptation indispensable.

## 10. Orchestration multi-agents massive sur Boat.dev (`builtin/smart` + `ethereumfoundation/*`)

Le contrôleur (`builtin/smart`) agit en **Orchestrateur pur** : zéro compilation ni preuve lourde sur le nœud coordinateur, maintien d’un *open-file ownership ledger* strict dans `campaign-state.json`, gel de `Spec/` avant chaque vague parallèle, et intégration séquentielle uniquement d’archives vérifiées (`exit 0`). Consulter systématiquement `list_managed_machines` / `get_budget` (`spent_today_usd`, `committed_usd`, `daily_cap_usd`) avant chaque vague et détruire immédiatement (`destroy_managed_machine`) toute VM terminée ou perdante dès récolte de son archive.

### Golden Snapshot Boat obligatoire par vague

1. Assembler et préchauffer sur une VM `boat:xlarge` le cône complet sous `/var/lib/orb-node/work/caches/<wave-sha>/` (jamais `/tmp` ni `~/.cache`, que les snapshots Boat ne conservent pas) : `xmss-hub-unified`, `leanVM@59c2984` compilé avec exporteurs différentiels, `turbo-lean@29d85f7` patché P0 (`lean-native` 4.35, ABI `UInt64` 64 bits, ordre de link LLVM), fixtures et cache `.olean` + `.c.o.export` chaud.
2. Vérifier l’absence totale de secrets, exécuter `sync`, appeler `snapshot_managed_machine(name="xmss-hub-v3-<sha>")` et attendre `status == "ready"` avant d’éventrer la vague parallèle.
3. Récolter systématiquement les bundles `.tar.gz` + manifestes SHA-256 **avant** expiration du bail VM ou appel à `destroy_managed_machine`. Sans autorisation explicite, ne faire ni commit, ni push, ni PR/merge.

### Répartition des modèles (`backend="opencode"`) et parallélisme par vagues (6 à 10 VMs Boat simultanées)

- **`builtin/smart` (`boat:large` / `boat:xlarge`)** : architecture, intégration, verrous protocolaires durs (`KeccakGkr`, `RingSwitch/StackOpen WHIR`), déboxage S3 (`Flat/`), extensions et noyaux SIMD `lean-native` (`VPCLMULQDQ`, `GFNI`, `vpternlogq`), preuves de raffinement S3/S4 délicates et certification finale Tier B.
- **`ethereumfoundation/glm-5.3` (`boat:default` / `boat:large`)** : traductions Rust -> Lean (`Spec`/`Model`) guidées par oracle, preuves de raffinement structurées, CLI `aggregate` / sérialisation `EthereumProof`, et second candidat en Best-of-2/3 avec `builtin/smart` sur les verrous isolés (destruction immédiate des perdants dès qu’un candidat franchit la gate objective).
- **`ethereumfoundation/qwen3.8-27b` (`boat:default`, `writer=false`)** : revue indépendante Maxwell, audits `turbo_audit_spec` / `collectAxioms` transitifs (`0 sorryAx`, `0 native_decide`), génération de vecteurs différentiels Rust/Python et matrice des 10 mutants négatifs (`negWitness`).
- **`ethereumfoundation/deepseek-v4.1-flash` (`boat:default`)** : scouts rapides, triage de divergences Fiat–Shamir challenge-par-challenge, et balayages de paramètres Tier A/B (threads `1/2/4/8/16`, tailles de tuiles L2, seuils `Keep::BeforeDeep`).

### Topologie des deux vagues d’exécution depuis `xmss-hub-unified`

- **Vague 1 — Gate E2E P2 (`verify() == OK` sur synthétiques + `--xmss 4` + `--xmss 16`, 5–6 shards à fichiers disjoints depuis `xmss-hub-v3-<sha>`)** :
  1. **W1 (`boat:large`, `builtin/smart` + binôme `ethereumfoundation/glm-5.3`)** : `{Spec,Model,Proofs,Tests}/KeccakGkr/**` — témoin segmenté `q_keccak`, RMFE, GKR Keccak-f[1600], `into_pcs_claims`, parité exacte contre `keccak_reduction.prove`.
  2. **W2 (`boat:large`, `builtin/smart` + binôme `ethereumfoundation/glm-5.3`)** : `{Spec,Model,Proofs,Tests}/Pcs/{RingSwitch,StackOpen,Whir}/**` + `Aggregate/Wire.lean` — `finish_claims`, `bind_pi_claim`, ring-switch, ouverture WHIR empilée unique, sérialisation `EthereumProof` acceptée par `verifier` Rust.
  3. **W3 (`boat:xlarge`, `builtin/smart`)** : `Flat/Bus/**` + `Native/Bus/**` — déboxage de `E` en tableaux `UInt64` planaires SoA sans allocation par tour pour faire passer `prove_bus` + `prove_constraints` à l’échelle `xmss1400`.
  4. **W4 (`boat:default`, `ethereumfoundation/glm-5.3`)** : `Cli/Aggregate.lean`, exporteur Rust challenge-par-challenge sur `--xmss 4` et `--xmss 16`, et runner de benchmark Tier B (`ru_maxrss`, `proof_size()`, alternance Rust/Lean).
  5. **W5 (`boat:default`, `ethereumfoundation/qwen3.8-27b` + `ethereumfoundation/deepseek-v4.1-flash`, `writer=false`)** : audit indépendant S1/S2, axiomes transitifs, suite de mutants rejetés et triage de transcript.
- **Vague 2 — Sprint performance Amdahl P3–P5 sur `xmss1400` (`boat:xlarge` depuis snapshot `xmss-e2e-green-<sha>`, strictement focalisé sur les 5 phases $f \ge 10\%$)** :
  1. **K1 (`prove_bus` — 27.0 %)** : Karatsuba planaire `F192x8` + `VPCLMULQDQ` + réduction différée + sumcheck fusionné (`builtin/smart` + `ethereumfoundation/glm-5.3` en Best-of-2).
  2. **K2 (`keccak_reduction` — 26.4 %)** : bitplanes Keccak GKR + packs RMFE + `GFNI` / ternaire `vpternlogq` prouvés dans `lean-native` (`builtin/smart`).
  3. **K3 (`pcs_open` 16.2 % + `commit_ntt_merkle` 11.9 % = 28.1 %)** : NTT additive binaire tuilée en place, produits mixtes `E×K`, fusion NTT -> feuilles Merkle Keccak multi-états, calibration `Keep::BeforeDeep` pour tenir le RSS sous `5.5 GiB` (`builtin/smart` + `ethereumfoundation/glm-5.3`).
  4. **K4 (`execute_program` 11.6 % + `build_witness` 3.2 %)** : écriture directe de `w.q` à ses placements finaux sans copies intermédiaires, arènes réutilisées et libération immédiate des colonnes virtuelles (`ethereumfoundation/glm-5.3`).
  5. **K5 (Tuning Pareto & certification Tier B sur `boat:xlarge` isolée)** : sweep threads/tuiles (`ethereumfoundation/deepseek-v4.1-flash`) puis >= 5 campagnes finales alternées Rust/Lean sur la **même instance `boat:xlarge` isolée** (`builtin/smart`), sans jamais mesurer deux candidats en concurrence (attention à la variance d’hôte physique entre `EPYC 4585PX` et `Ryzen 9950X`).

Chaque tâche reçoit entrées, sorties, fichiers exclusivement possédés, théorèmes à fermer, test différentiel, gate natif et condition de fin. Pour les tâches longues : `start_workspace_job`, `get_fleet_sweep` et `schedule_wakeup` plutôt que boucles de polling agressives. Un statut mission « completed » n’est jamais une certification sans ré-exécution de la gate à l’intégration.

## 11. Phases et portes de sortie

### P0 — Reproductibilité et faisabilité

- Geler les deux dépôts et les toolchains, reproduire Rust, profiler les phases et exporter fixtures publiques.
- Compiler et exécuter les probes LeanNative réels ; établir la liste exacte des écarts backend/runtime.
- Produire les contrats d’interface et la comptabilité mémoire.

**Sortie :** baseline traçable, preuve Rust vérifiée, environnement reconstructible, premier noyau Lean réellement lié. *(Acquis.)*

### P1 — Fondations et audit S1/S2

- K/E, Keccak, transcript, encoding, XMSS/hints et sémantique VM.
- Vecteurs Rust/Python/EthLib, cas frontières et mutants ; portes Spec avant optimisations.

**Sortie :** modèles exécutables non triviaux, équivalences et dépendances d’axiomes auditées ; parité différentielle des primitives. *(Acquis dans `xmss-hub-unified`, avec `Layout`, `Pcs/{Ntt,Commit}`, `Witness` et `Bus+Constraints` également validés.)*

### P2 — Roundtrip E2E vérifié par Rust sur petits lots (règle Hindsight `kp-18069005`)

- Hints -> exécution -> witness -> engagement -> bus/contraintes -> Keccak GKR -> ring-switch -> WHIR empilé unique -> sérialisation `EthereumProof`.
- **Règle Hindsight stricte** : établir d’abord le roundtrip complet jusqu’au vérifieur Rust inchangé (`verify() == OK`) sur les 4 cas synthétiques **et** sur `--xmss 4` et `--xmss 16` (avec journal Fiat–Shamir challenge-par-challenge aux frontières de phase et zéro étape déléguée à Rust).
- **Interdiction de bloquer P2 en exécutant `Model/` (tableaux d’`E` boxés) sur `--xmss 1400`** : le passage à l’échelle `1400` s’effectue directement sur les représentations plates déboxées S3/S4 (`Flat/` + `Native/`) sur `boat:xlarge`.

**Sortie :** première preuve E2E générée 100 % par Lean et acceptée par le vérifieur Rust inchangé sur synthétiques + `--xmss 4` + `--xmss 16`, rejet des mutants vérifié, et golden snapshot `xmss-e2e-green-<sha>` publié.

### P3 — Layout plat déboxé et passage à l’échelle XMSS 1400

- Tableaux `UInt64` planaires SoA (`Flat/`), slices/arènes/bitplanes sans boxage par élément chaud, remplissage direct de `w.q`, gestion du padding, états `E` tardifs, codewords reconstruits (`Keep::BeforeDeep`).
- Preuves S3 -> S2 et gates natifs différentiels ; bilan des allocations et du RSS par phase avant/après sur `boat:xlarge`.

**Sortie :** pipeline Lean natif complet `verify() == OK` sur `--xmss 1400 --log-inv-rate 1`, sans OOM, RSS borné (< 8.633 GiB) et profil de temps natif par phase mesuré.

### P4 — SIMD et compilation guidée par le corpus

- Étendre LeanNative seulement pour les goulots mesurés ; AVX2 puis AVX-512/GFNI/VPCLMUL et ternaire correctement spécifié.
- Preuves de transformation/lowering, audit des symboles réellement utilisés, Tier A et Tier B à chaque promotion.

**Sortie :** améliorations bout en bout reproductibles sans nouvelle hypothèse de confiance cachée.

### P5 — Recherche automatique et certification

- Balayer tuiles, threads, ordre local, conservation/reconstruction, fusion et seuils ; conserver le front de Pareto.
- Refaire audits, tests négatifs, vérification indépendante et campagnes finales isolées.
- Reproduire depuis un workspace/VM fraîche avec sources et versions gelées.

**Sortie :** contrat principal satisfait avec preuve et chiffres exacts, ou rapport honnête des écarts restant à résoudre. Ne pas clore sur un microbench gagnant, une preuve vide ou un résultat invérifié.

## 12. Risques et décisions de repli

| Risque | Décision |
|---|---|
| Couverture LeanNative insuffisante | Probe P0, extension minimale prouvée, pas de FFI crypto de secours masquée |
| Preuves d’algorithmes optimisés trop coûteuses | Décomposition S1/S2/S3/S4, lemmes de représentation et noyaux petits ; rester correct avant rapide |
| Divergence de transcript | Journal challenge par challenge et première différence ; ordre de parallélisme indépendant de l’émission |
| RSS dominé par représentation Lean | Layout plat, exclusivité/RC, arènes et durées de vie ; ne pas stocker des objets Lean par élément chaud |
| Gain SIMD annulé par bande passante/spills | Tuilage, trafic mesuré, comparaison AVX2/AVX-512 et score Tier B |
| Référence déjà très optimisée | Porter ses optimisations existantes avant de revendiquer une innovation ; benchmark plutôt qu’intuition |
| Taille/vérification inchangées | Les publier comme non-régression, ne pas changer le protocole pour satisfaire artificiellement un tableau |
| Métadonnées CPU/cache virtuelles trompeuses | Mesures empiriques, capture topologie, pas de promesse de résidence sur 256 MiB |
| Outil MCP propose native_decide ou un fallback testé | Refuser pour les preuves acceptées, vérifier le statut/kernel et les axiomes transitifs |
| Variance / biais de sélection | Campagnes alternées, multiples processus frais, confirmation indépendante des gagnants |

## 13. Artefacts d’acceptation à produire pendant l’implémentation

1. Sources Lean des quatre couches et preuves fermées ; diff compilateur séparé et minimal si nécessaire.
2. Manifest des commits/toolchains/flags/matériel, hash des fixtures et commandes réellement exécutées.
3. Preuve finale en octets avec statement attendu de 1400 claims distincts, validation Rust et logs de rejet des mutants.
4. Artefacts de compilation et preuve de liaison des noyaux optimisés : symboles, LLVM, désassemblage et dispatch features.
5. Résultats Tier A/Tier B bruts, tableau mémoire et comparaison Rust/Lean non arrondie ; gains locaux distingués du gain global.
6. Audit des spécifications, des raffinements et des axiomes, avec frontière de confiance explicitée.
7. Instructions de reproduction depuis une VM neuve et bilan des ressources ; aucun secret ni instance oubliée.

Les journaux/artefacts futurs sont à créer au besoin dans l’espace durable d’implémentation ; ce document n’autorise pas une implémentation, un commit ou un succès fictif.

## 14. Instruction `/goal` alignée au contrôleur

```text
/goal Agis en Orchestrateur Maxwell/Hindsight pur (`builtin/smart`) pour livrer le prouveur Lean 4 natif complet XMSS 1400 (`leanVM@59c2984`, `turbo-lean@29d85f7`, zéro FFI crypto Rust/C), accepté par le vérifieur Rust inchangé et reproductiblement plus rapide avec moins de RSS que `1.15 s` / `8.633 GiB` ET que Rust relancé en passes alternées sur la même VM `boat:xlarge`.

Principes Hindsight obligatoires :
1. Zéro compilation lourde sur le coordinateur et interdiction d’exécuter `Model/` (tableaux `E` boxés) sur `xmss1400`. Repars de `xmss-hub-unified` (`Field`, `Transcript`, `Merkle`, `Vm`, `Xmss`, `Layout`, `Pcs/{Ntt,Commit}`, `Witness`, `Bus+Constraints` acquis).
2. Crée d’abord sur `boat:xlarge` un golden snapshot chaud sous `/var/lib/orb-node/work/caches/xmss-hub-v3/` (sources, binaires oracles Rust, `turbo-lean` patché P0, `.olean/.c.o.export` chauds ; `sync`, `snapshot_managed_machine`, attendre `status=="ready"`). Boucle chaude 100 % `turbo-lean mcp` persistant + `lean-native` (`@[noinline]` ou intrinsèques canoniques, <10 s/build-exe, zéro `lake` froid).
3. Exploite massivement `boat` en vagues parallèles (6–10 VMs simultanées depuis le golden snapshot, propriété de fichiers disjointe, récolte `.tar.gz`+SHA256 avant bail, `destroy_managed_machine` immédiat dès fin de tâche) avec un mix `backend="opencode"` :
   - `builtin/smart` (`boat:large`/`xlarge`) : verrous durs protocolaires et noyaux S3/S4/SIMD ;
   - `ethereumfoundation/glm-5.3` (`boat:default`/`large`) : implémentations S1/S2/CLI guidées par oracle, preuves structurées et candidats Best-of-2 ;
   - `ethereumfoundation/qwen3.8-27b` (`boat:default`, `writer=false`) : vecteurs différentiels, 10 mutants négatifs, audits `turbo_audit_spec` et axiomes (`0 sorryAx`, `0 native_decide`) ;
   - `ethereumfoundation/deepseek-v4.1-flash` (`boat:default`) : triage Fiat–Shamir challenge-par-challenge et sweeps de paramètres Tier A/B.
4. Vague 1 (Gate E2E P2) : lance en parallèle (a) `KeccakGkr+RMFE+q_keccak`, (b) `RingSwitch+StackOpen WHIR+Wire EthereumProof`, (c) déboxage S3 SoA de `Bus`, (d) CLI `aggregate` + traces `--xmss 4/16`, (e) audit/mutants en lecture seule. Valide `verify() == OK` sur synthétiques + `--xmss 4` + `--xmss 16`, puis snapshot `xmss-e2e-green`.
5. Vague 2 (Gate Perf P3–P5 sur `boat:xlarge`) : parallélise uniquement les 5 phases Amdahl >=10 % (`prove_bus` 27 %, `keccak_reduction` 26 %, `pcs_open` 16 %, `commit_ntt_merkle` 12 %, `execute_program` 12 %) : layout plat sans copie dans `w.q`, Karatsuba planaire `F192x8`/`VPCLMULQDQ`, `GFNI`/bitplanes/ternaire prouvés dans `lean-native`, NTT tuilée fusionnée à Merkle, arènes/`Keep::BeforeDeep` et scaling 1..16 threads. Certifie sur `boat:xlarge` isolée avec >=5 paires alternées Rust/Lean (`--xmss 1400 --log-inv-rate 1 --repeat 3`).
```
