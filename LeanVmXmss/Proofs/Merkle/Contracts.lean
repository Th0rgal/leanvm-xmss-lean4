import Model.Merkle.Heap
import Proofs.Field.Codecs

namespace LeanVmXmss.Proofs.Merkle.Contracts

open Spec.Merkle

theorem wordBytes_size (word : UInt64) : (Spec.Keccak.wordBytes word).size = 8 := by
  simp [Spec.Keccak.wordBytes, ByteArray.size]

theorem wordsBytes_size (words : Array UInt64) :
    (Spec.Keccak.wordsBytes words).size = 8 * words.size := by
  have foldSize (values : List UInt64) (initial : Array UInt8) :
      (values.foldl (fun bytes word => bytes ++ (Spec.Keccak.wordBytes word).data)
        initial).size = initial.size + 8 * values.length := by
    induction values generalizing initial with
    | nil => simp
    | cons word rest ih =>
      simp only [List.foldl_cons, ih, Array.size_append, List.length_cons]
      have width := wordBytes_size word
      change (Spec.Keccak.wordBytes word).data.size = 8 at width
      rw [width]
      omega
  change (words.foldl (fun bytes word => bytes ++ (Spec.Keccak.wordBytes word).data)
    #[]).size = _
  simpa only [Array.foldl_toList, Array.length_toList, Array.size_empty,
    Nat.zero_add] using foldSize words.toList #[]

theorem digest32_toBytes_size (digest : Model.Merkle.Digest32) :
    digest.toBytes.size = 32 := by
  unfold Model.Merkle.Digest32.toBytes
  rw [wordsBytes_size]
  rfl

theorem digest32_fromBytes_domain (bytes : ByteArray) :
    (Model.Merkle.Digest32.fromBytes bytes).isSome = true ↔ bytes.size = 32 := by
  unfold Model.Merkle.Digest32.fromBytes
  split <;> simp_all

theorem digest32_serialized_accepted (digest : Model.Merkle.Digest32) :
    (Model.Merkle.Digest32.fromBytes digest.toBytes).isSome = true := by
  exact (digest32_fromBytes_domain _).mpr (digest32_toBytes_size digest)

theorem checked_leaf_domain (row : Array UInt64) (leafWords : Nat) :
    (checkedLeafImage row leafWords).isSome = true ↔ row.size ≤ leafWords := by
  unfold checkedLeafImage
  split <;> simp_all

theorem checked_digest_domain (bytes : ByteArray) :
    (checkedDigest bytes).isSome = true ↔ bytes.size = 32 := by
  unfold checkedDigest
  split <;> simp_all

theorem digest32_checked_spec (digest : Model.Merkle.Digest32) :
    checkedDigest digest.toBytes = some (toDigest digest.toBytes) := by
  unfold checkedDigest
  rw [digest32_toBytes_size]
  rfl

theorem heap_build_domain (depth : Nat) (leaves : Array Model.Merkle.Digest32) :
    (Model.Merkle.buildHeap depth leaves).isSome = true ↔ leaves.size = 2^depth := by
  unfold Model.Merkle.buildHeap
  split <;> simp_all

theorem heap_path_domain (tree : Model.Merkle.HeapTree) (index : Nat) :
    (Model.Merkle.heapPath tree index).isSome = true ↔
      index < 2^tree.depth ∧ tree.nodes.size = 2 * 2^tree.depth := by
  unfold Model.Merkle.heapPath
  split <;> simp_all

theorem expand_exact_consumption (proof : PrunedMerklePaths) (depth : Nat)
    (queries : Array Nat) (rowWords leafWords : Nat) (root : Digest) (paths : Array MerklePath)
    (h : expandPruned proof depth queries rowWords leafWords = some (root, paths)) :
    let initial := (sortedUnique queries).mapIdx (fun i index =>
      MerklePath.mk index (Array.replicate (leafWords - rowWords) 0 ++ proof.rows[i]!) #[])
    ∃ nodes consumed accumulated,
      expandLevels depth (initial.mapIdx (fun i path =>
        ActiveNode.mk path.index (hashLeaf (Spec.Keccak.wordsBytes path.leaf)) #[i])).toList
        0 proof.siblings initial =
          some (nodes, consumed, accumulated) ∧ consumed = proof.siblings.size := by
  unfold expandPruned at h
  dsimp only at h ⊢
  split at h
  · simp at h
  · rename_i shape
    generalize he : expandLevels depth _ 0 proof.siblings _ = result at h
    cases result with
    | none => simp at h
    | some p =>
      rcases p with ⟨nodes, consumed, accumulated⟩
      dsimp only [Bind.bind, Option.bind] at h
      split at h
      · simp at h
      · rename_i exactSize
        refine ⟨nodes, consumed, accumulated, ?_, ?_⟩
        · rfl
        · by_cases e : consumed = proof.siblings.size
          · exact e
          · exact False.elim (exactSize (by simpa only [bne_iff_ne] using e))

theorem climb_preserves_size (count : Nat) (nodes : Array Model.Merkle.Digest32) :
    (Model.Merkle.climb count nodes).size = nodes.size := by
  induction count generalizing nodes with
  | zero => rfl
  | succ count ih =>
    simp only [Model.Merkle.climb_succ, ih, Array.size_set!]

theorem built_heap_shape (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (built : Model.Merkle.buildHeap depth leaves = some tree) :
    tree.depth = depth ∧ tree.nodes.size = 2 * 2^depth := by
  unfold Model.Merkle.buildHeap at built
  split at built
  · rename_i size
    cases built
    simp only [climb_preserves_size, Array.size_append, Array.size_replicate]
    constructor
    · trivial
    · omega
  · simp at built

theorem built_heap_path_exists (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (index : Nat)
    (built : Model.Merkle.buildHeap depth leaves = some tree) (bound : index < 2^depth) :
    (Model.Merkle.heapPath tree index).isSome = true := by
  obtain ⟨height, size⟩ := built_heap_shape depth leaves tree built
  apply (heap_path_domain tree index).mpr
  rw [height]
  exact ⟨bound, size⟩

theorem heap_path_length (tree : Model.Merkle.HeapTree) (index : Nat)
    (path : Array Model.Merkle.Digest32)
    (found : Model.Merkle.heapPath tree index = some path) : path.size = tree.depth := by
  unfold Model.Merkle.heapPath at found
  split at found
  · cases found
    simp only [Array.size_map, Array.size_range]
  · simp at found

theorem built_heap_root_exists (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (built : Model.Merkle.buildHeap depth leaves = some tree) :
    (Model.Merkle.heapRoot tree).isSome = true := by
  obtain ⟨_, size⟩ := built_heap_shape depth leaves tree built
  have positive : 0 < 2^depth := Nat.two_pow_pos depth
  have bound : 1 < tree.nodes.size := by omega
  simp [Model.Merkle.heapRoot, bound]

theorem built_heap_path_length (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (index : Nat)
    (built : Model.Merkle.buildHeap depth leaves = some tree) (bound : index < 2^depth) :
    ((Model.Merkle.heapPath tree index).map Array.size) = some depth := by
  have existsPath := built_heap_path_exists depth leaves tree index built bound
  obtain ⟨height, _⟩ := built_heap_shape depth leaves tree built
  cases found : Model.Merkle.heapPath tree index with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at existsPath
  | some path =>
    simp only [Option.map_some]
    rw [heap_path_length tree index path found, height]

theorem climb_preserves_above (count : Nat) (nodes : Array Model.Merkle.Digest32)
    (index : Nat) (above : count < index) :
    (Model.Merkle.climb count nodes)[index]! = nodes[index]! := by
  induction count generalizing nodes with
  | zero => rfl
  | succ count ih =>
    rw [Model.Merkle.climb_succ, ih _ (by omega)]
    exact Array.getElem!_set!_ne _ _ _ _ (by omega)

theorem climb_parent_equations (count : Nat) (nodes : Array Model.Merkle.Digest32)
    (bound : count < nodes.size) (index : Nat) (positive : 0 < index)
    (processed : index ≤ count) :
    (Model.Merkle.climb count nodes)[index]! = Model.Merkle.Digest32.hashPair
      (Model.Merkle.climb count nodes)[2 * index]!
      (Model.Merkle.climb count nodes)[2 * index + 1]! := by
  induction count generalizing nodes with
  | zero => omega
  | succ count ih =>
    by_cases top : index = count + 1
    · subst index
      rw [Model.Merkle.climb_succ]
      rw [climb_preserves_above count _ (count + 1) (by omega),
        climb_preserves_above count _ (2 * (count + 1)) (by omega),
        climb_preserves_above count _ (2 * (count + 1) + 1) (by omega)]
      rw [Array.getElem!_set!_self _ _ _ bound,
        Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega)]
    · rw [Model.Merkle.climb_succ]
      apply ih
      · simp only [Array.size_set!]; omega
      · omega

theorem built_heap_parent_equations (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (built : Model.Merkle.buildHeap depth leaves = some tree)
    (index : Nat) (positive : 0 < index) (internal : index < 2^depth) :
    tree.nodes[index]! = Model.Merkle.Digest32.hashPair
      tree.nodes[2 * index]! tree.nodes[2 * index + 1]! := by
  unfold Model.Merkle.buildHeap at built
  split at built
  · rename_i size
    cases built
    apply climb_parent_equations
    · simp only [Array.size_append, Array.size_replicate]
      have nonempty : 0 < leaves.size := by rw [size]; exact Nat.two_pow_pos depth
      omega
    · exact positive
    · rw [← size] at internal
      omega
  · simp at built

theorem built_heap_leaf (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (built : Model.Merkle.buildHeap depth leaves = some tree)
    (index : Nat) (bound : index < leaves.size) :
    tree.nodes[2^depth + index]! = leaves[index]! := by
  unfold Model.Merkle.buildHeap at built
  split at built
  · rename_i size
    cases built
    rw [climb_preserves_above _ _ _ (by omega), ← size]
    simp [bound]
  · simp at built

theorem climb_refines_heap (count : Nat) (nodes target : Array Model.Merkle.Digest32)
    (sameSize : nodes.size = target.size) (bound : count < nodes.size)
    (parents : ∀ i, 0 < i → i ≤ count →
      target[i]! = Model.Merkle.Digest32.hashPair target[2 * i]! target[2 * i + 1]!)
    (upper : ∀ i, count < i → nodes[i]! = target[i]!) :
    ∀ i, 0 < i → (Model.Merkle.climb count nodes)[i]! = target[i]! := by
  induction count generalizing nodes with
  | zero => exact upper
  | succ count ih =>
    rw [Model.Merkle.climb_succ]
    apply ih
    · simpa only [Array.size_set!] using sameSize
    · simpa only [Array.size_set!] using (show count < nodes.size by omega)
    · intro i positive processed
      exact parents i positive (by omega)
    · intro i above
      by_cases top : i = count + 1
      · subst i
        rw [Array.getElem!_set!_self _ _ _ bound,
          upper _ (by omega), upper _ (by omega)]
        exact (parents _ (by omega) (by omega)).symm
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        exact upper i (by omega)

theorem built_heap_refines_target (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (target : Array Model.Merkle.Digest32)
    (built : Model.Merkle.buildHeap depth leaves = some tree)
    (targetSize : target.size = 2 * 2^depth)
    (parents : ∀ i, 0 < i → i < 2^depth →
      target[i]! = Model.Merkle.Digest32.hashPair target[2 * i]! target[2 * i + 1]!)
    (leavesMatch : ∀ i, i < leaves.size → target[2^depth + i]! = leaves[i]!) :
    ∀ i, 0 < i → tree.nodes[i]! = target[i]! := by
  unfold Model.Merkle.buildHeap at built
  split at built
  · rename_i size
    cases built
    apply climb_refines_heap
    · simp only [Array.size_append, Array.size_replicate]
      omega
    · simp only [Array.size_append, Array.size_replicate]
      have nonempty : 0 < leaves.size := by rw [size]; exact Nat.two_pow_pos depth
      omega
    · intro i positive processed
      apply parents i positive
      have nonempty : 0 < leaves.size := by rw [size]; exact Nat.two_pow_pos depth
      omega
    · intro i above
      by_cases inside : i < 2 * leaves.size
      · have lower : leaves.size ≤ i := by omega
        have leafBound : i - leaves.size < leaves.size := by omega
        have position : leaves.size + (i - leaves.size) = i := by omega
        have matched := leavesMatch (i - leaves.size) leafBound
        rw [← size, position] at matched
        calc
          _ = leaves[i - leaves.size]! := by
            have lookup := congrArg (fun j =>
              (Array.replicate leaves.size (default : Model.Merkle.Digest32) ++ leaves)[j]!) position
            simpa [leafBound] using lookup.symm
          _ = target[i]! := matched.symm
      · have outsideNodes : (Array.replicate leaves.size (default : Model.Merkle.Digest32) ++ leaves).size ≤ i := by
          simp only [Array.size_append, Array.size_replicate]; omega
        have outsideTarget : target.size ≤ i := by omega
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none outsideNodes, Array.getElem?_eq_none outsideTarget]
  · simp at built

theorem built_heap_root_refines_target (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (target : Array Model.Merkle.Digest32)
    (built : Model.Merkle.buildHeap depth leaves = some tree)
    (targetSize : target.size = 2 * 2^depth)
    (parents : ∀ i, 0 < i → i < 2^depth →
      target[i]! = Model.Merkle.Digest32.hashPair target[2 * i]! target[2 * i + 1]!)
    (leavesMatch : ∀ i, i < leaves.size → target[2^depth + i]! = leaves[i]!) :
    Model.Merkle.heapRoot tree = some target[1]! := by
  have shape := built_heap_shape depth leaves tree built
  have positive := Nat.two_pow_pos depth
  have bound : 1 < tree.nodes.size := by omega
  have matched := built_heap_refines_target depth leaves tree target built targetSize parents leavesMatch 1 (by omega)
  unfold Model.Merkle.heapRoot
  rw [Array.getElem?_eq_getElem bound]
  have lookup : tree.nodes[1]! = tree.nodes[1] := getElem!_pos tree.nodes 1 bound
  rw [← lookup, matched]

theorem expandLevels_composition (first second : Nat) (nodes : List Spec.Merkle.ActiveNode)
    (cursor : Nat) (siblings : Array Spec.Merkle.Digest) (paths : Array Spec.Merkle.MerklePath) :
    Spec.Merkle.expandLevels (first + second) nodes cursor siblings paths =
      (Spec.Merkle.expandLevels first nodes cursor siblings paths).bind (fun result =>
        Spec.Merkle.expandLevels second result.1 result.2.1 siblings result.2.2) := by
  induction first generalizing nodes cursor paths with
  | zero => simp only [Nat.zero_add, Spec.Merkle.expandLevels_zero, Option.bind_some]
  | succ first ih =>
    rw [Nat.succ_add]
    change ((Spec.Merkle.expandLevel cursor nodes siblings paths).bind (fun result =>
      Spec.Merkle.expandLevels (first + second) result.1 result.2.1 siblings result.2.2)) = _
    cases step : Spec.Merkle.expandLevel cursor nodes siblings paths with
    | none => simp only [Option.bind_none, Spec.Merkle.expandLevels_succ, step]
    | some result =>
      rcases result with ⟨next, offset, updated⟩
      simpa only [Spec.Merkle.expandLevels_succ, step, Option.bind_some] using ih next offset updated

theorem expandLevels_acceptance_split (first second : Nat) (nodes : List Spec.Merkle.ActiveNode)
    (cursor : Nat) (siblings : Array Spec.Merkle.Digest) (paths : Array Spec.Merkle.MerklePath)
    (result : List Spec.Merkle.ActiveNode × Nat × Array Spec.Merkle.MerklePath) :
    Spec.Merkle.expandLevels (first + second) nodes cursor siblings paths = some result ↔
      ∃ middle, Spec.Merkle.expandLevels first nodes cursor siblings paths = some middle ∧
        Spec.Merkle.expandLevels second middle.1 middle.2.1 siblings middle.2.2 = some result := by
  rw [expandLevels_composition]
  cases step : Spec.Merkle.expandLevels first nodes cursor siblings paths with
  | none => simp only [Option.bind_none, reduceCtorEq, false_iff, not_exists, not_and, false_implies, implies_true]
  | some middle =>
    simp only [Option.bind_some, Option.some.injEq]
    constructor
    · intro accepted
      exact ⟨middle, rfl, accepted⟩
    · rintro ⟨other, same, accepted⟩
      cases same
      exact accepted

theorem sibling_index (index : Nat) :
    index ^^^ 1 = if index % 2 = 0 then index + 1 else index - 1 := by
  change Nat.bitwise bne index 1 = _
  rw [Nat.bitwise]
  by_cases zero : index = 0
  · simp [zero]
  · simp only [zero, ite_false]
    have base : Nat.bitwise bne (index / 2) 0 = index / 2 := by
      rw [Nat.bitwise]
      by_cases h : index / 2 = 0 <;> simp [h]
    rw [base]
    have parity := Nat.mod_two_eq_zero_or_one index
    rcases parity with even | odd
    · simp [even]
      omega
    · simp [odd]
      omega

set_option backward.isDefEq.respectTransparency false in
theorem ofFn_go_lookup {α : Type} {n : Nat} (f : Fin n → α)
    (count : Nat) (acc : Array α) (remaining : count ≤ n) (index : Nat)
    (bound : index < acc.size + count) :
    (Array.ofFn.go f acc count remaining)[index]'(by simpa using bound) =
      if h : index < acc.size then acc[index] else
        f ⟨n - count + index - acc.size, by omega⟩ := by
  induction count generalizing acc index with
  | zero =>
    have inside : index < acc.size := by omega
    simp only [Array.ofFn.go, inside, dite_true]
  | succ count ih =>
    unfold Array.ofFn.go
    rw [ih _ _ _ (by simp only [Array.size_push]; omega)]
    · simp only [Array.size_push]
      split <;> rename_i h
      · rw [Array.getElem_push]
        split
        · rfl
        · apply congrArg f
          apply Fin.ext
          change n - count - 1 = n - (count + 1) + index - acc.size
          omega
      · split
        · exfalso
          omega
        · apply congrArg f
          apply Fin.ext
          change n - count + index - (acc.size + 1) = n - (count + 1) + index - acc.size
          omega

set_option backward.isDefEq.respectTransparency false in
theorem ofFn_lookup {α : Type} {n : Nat} (f : Fin n → α)
    (index : Nat) (bound : index < (Array.ofFn f).size) :
    (Array.ofFn f)[index] = f ⟨index, by simpa only [Array.size_ofFn] using bound⟩ := by
  unfold Array.ofFn
  have emptySize : (Array.emptyWithCapacity n : Array α).size = 0 := rfl
  rw [ofFn_go_lookup]
  · simp only [emptySize, Nat.not_lt_zero, dite_false,
      Nat.sub_self, Nat.zero_add, Nat.sub_zero]
  · simpa only [emptySize, Nat.zero_add, Array.size_ofFn] using bound

theorem built_heap_path_refines_target (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (target : Array Model.Merkle.Digest32) (index : Nat)
    (built : Model.Merkle.buildHeap depth leaves = some tree)
    (targetSize : target.size = 2 * 2^depth)
    (parents : ∀ i, 0 < i → i < 2^depth →
      target[i]! = Model.Merkle.Digest32.hashPair target[2 * i]! target[2 * i + 1]!)
    (leavesMatch : ∀ i, i < leaves.size → target[2^depth + i]! = leaves[i]!)
    (bound : index < 2^depth) :
    Model.Merkle.heapPath tree index = some ((Array.range depth).map fun level =>
      target[((2^depth + index) / 2^level) ^^^ 1]!) := by
  obtain ⟨height, size⟩ := built_heap_shape depth leaves tree built
  have matched := built_heap_refines_target depth leaves tree target built targetSize parents leavesMatch
  unfold Model.Merkle.heapPath
  rw [height]
  rw [ite_eq_left ⟨bound, size⟩]
  congr 1
  apply Array.ext
  · simp only [Array.size_map]
  · intro i left right
    simp only [Array.getElem_map, Array.range]
    rw [ofFn_lookup]
    apply matched
    have levelBound : i < depth := by
      simpa only [Array.size_map, Array.size_range] using left
    have powerBound : 2 * 2^i ≤ 2^depth := by
      have h := Nat.pow_le_pow_right (by omega : 0 < 2) (show i + 1 ≤ depth by omega)
      simpa only [Nat.pow_succ, Nat.mul_comm] using h
    have quotientBound : 2 ≤ (2^depth + index) / 2^i :=
      (Nat.le_div_iff_mul_le (Nat.two_pow_pos i)).mpr (by omega)
    change 0 < ((2^depth + index) / 2^i) ^^^ 1
    rw [sibling_index]
    split <;> omega

set_option backward.isDefEq.respectTransparency false in
theorem parentLevel_path_step (nodes : Array Digest) (index : Nat)
    (bound : index < 2 * (nodes.size / 2)) :
    (if index % 2 == 0 then compress nodes[index]! nodes[index ^^^ 1]!
      else compress nodes[index ^^^ 1]! nodes[index]!) =
      (parentLevel nodes)[index / 2]! := by
  have parentBound : index / 2 < nodes.size / 2 := by omega
  have lookup : (parentLevel nodes)[index / 2]! =
      compress nodes[2 * (index / 2)]! nodes[2 * (index / 2) + 1]! := by
    have mappedBound : index / 2 < (parentLevel nodes).size := by
      simpa only [parentLevel, Array.size_map, Array.size_range] using parentBound
    rw [getElem!_pos (parentLevel nodes) (index / 2) mappedBound]
    simp only [parentLevel, Array.getElem_map]
    simp only [Array.range]
    rw [ofFn_lookup]
  rw [lookup]
  rw [sibling_index]
  by_cases parity : index % 2 = 0
  · have even : 2 * (index / 2) = index := by omega
    simp only [beq_iff_eq, parity, ite_true, even]
  · have odd : 2 * (index / 2) = index - 1 := by omega
    have predecessor : index - 1 + 1 = index := by omega
    simp only [beq_iff_eq, parity, ite_false, odd, predecessor]

theorem pathRoot_append (index : Nat) (leaf : Digest) (first rest : List Digest) :
    pathRoot index leaf (first ++ rest) =
      pathRoot (index / 2^first.length) (pathRoot index leaf first) rest := by
  induction first generalizing index leaf with
  | nil => simp only [List.nil_append, pathRoot_nil, List.length_nil, Nat.pow_zero, Nat.div_one]
  | cons sibling first ih =>
    simp only [List.cons_append, pathRoot_cons, ih, List.length_cons]
    rw [Nat.div_div_eq_div_mul]
    congr 1
    simp [Nat.pow_succ, Nat.mul_comm]

theorem pathRoot_level_chain (count index : Nat) (node sibling : Nat → Digest)
    (steps : ∀ level, level < count →
      node (level + 1) =
        if (index / 2^level) % 2 == 0 then compress (node level) (sibling level)
        else compress (sibling level) (node level)) :
    pathRoot index (node 0) ((List.range count).map sibling) = node count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.range_succ, List.map_append, pathRoot_append]
    simp only [List.length_map, List.length_range, List.map_singleton, pathRoot_cons, pathRoot_nil]
    rw [ih (fun level bound => steps level (by omega))]
    exact (steps count (by omega)).symm

theorem range_toList (count : Nat) : (Array.range count).toList = List.range count := by
  apply List.ext_getElem
  · simp only [Array.length_toList, Array.size_range, List.length_range]
  · intro index left right
    simp only [Array.getElem_toList, Array.range]
    rw [ofFn_lookup]
    simp only [List.getElem_range]

theorem inclusionPath_complete_of_levels (tree : Array (Array Digest)) (depth index : Nat)
    (height : tree.size = depth + 1) (bound : index < 2^depth)
    (parents : ∀ level, level < depth → tree[level + 1]! = parentLevel tree[level]!)
    (width : ∀ level, level < depth →
      index / 2^level < 2 * (tree[level]!.size / 2)) :
    pathRoot index tree[0]![index]! (inclusionPath tree index).toList = tree[depth]![0]! := by
  have chain := pathRoot_level_chain depth index
    (fun level => tree[level]![index / 2^level]!)
    (fun level => tree[level]![(index / 2^level) ^^^ 1]!) (by
      intro level levelBound
      rw [parents level levelBound]
      have division : index / 2^(level + 1) = index / 2^level / 2 := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      rw [division]
      exact (parentLevel_path_step _ _ (width level levelBound)).symm)
  simpa only [inclusionPath, height, Nat.add_sub_cancel, Array.toList_map, range_toList,
    Nat.pow_zero, Nat.div_one,
    Nat.div_eq_of_lt bound] using chain

theorem levels_power_shape (depth fuel : Nat) (nodes : Array Digest)
    (enough : depth ≤ fuel) (size : nodes.size = 2^depth) :
    (levels fuel nodes).size = depth + 1 ∧
      ∀ level, level ≤ depth → (levels fuel nodes)[level]!.size = 2^(depth - level) := by
  induction depth generalizing fuel nodes with
  | zero =>
    have singleton : nodes.size = 1 := by simpa using size
    cases fuel <;> simp [levels_zero, levels_succ, singleton]
  | succ depth ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have large : ¬nodes.size ≤ 1 := by
        rw [size, Nat.pow_succ]
        have positive := Nat.two_pow_pos depth
        omega
      have parentSize : (parentLevel nodes).size = 2^depth := by
        simp [parentLevel, size, Nat.pow_succ]
      obtain ⟨height, widths⟩ := ih fuel (parentLevel nodes) (by omega) parentSize
      simp only [levels_succ, large, ite_false, Array.size_append, Array.size_singleton, height]
      refine ⟨by omega, ?_⟩
      intro level levelBound
      cases level with
      | zero => simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_append] using size
      | succ level =>
        simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_append] using widths level (by omega)

theorem levels_parent_equations (depth fuel : Nat) (nodes : Array Digest)
    (enough : depth ≤ fuel) (size : nodes.size = 2^depth)
    (level : Nat) (bound : level < depth) :
    (levels fuel nodes)[level + 1]! = parentLevel (levels fuel nodes)[level]! := by
  induction depth generalizing fuel nodes level with
  | zero => omega
  | succ depth ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have large : ¬nodes.size ≤ 1 := by
        rw [size, Nat.pow_succ]
        have positive := Nat.two_pow_pos depth
        omega
      have parentSize : (parentLevel nodes).size = 2^depth := by
        simp [parentLevel, size, Nat.pow_succ]
      have first : (levels fuel (parentLevel nodes))[0]! = parentLevel nodes := by
        cases fuel <;>
          simp only [levels_zero, levels_succ] <;>
          (try split) <;>
          simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append]
      simp only [levels_succ, large, ite_false]
      cases level with
      | zero =>
        simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_append] using first
      | succ level =>
        have step := ih fuel (parentLevel nodes) (by omega) parentSize level (by omega)
        simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_append, Nat.add_assoc] using step

theorem build_inclusion_complete (depth : Nat) (leaves : Array Digest)
    (size : leaves.size = 2^depth) (index : Nat) (bound : index < leaves.size) :
    pathRoot index leaves[index]! (inclusionPath (build leaves) index).toList =
      (build leaves)[depth]![0]! := by
  have enough : depth ≤ leaves.size := by
    rw [size]
    have growth : depth < 2^depth := Nat.lt_two_pow_self
    omega
  obtain ⟨height, widths⟩ := levels_power_shape depth leaves.size leaves enough size
  have first : (build leaves)[0]! = leaves := by
    unfold build
    cases leaves.size <;>
      simp only [levels_zero, levels_succ] <;>
      (try split) <;>
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append]
  suffices result : pathRoot index (build leaves)[0]![index]!
      (inclusionPath (build leaves) index).toList = (build leaves)[depth]![0]! by
    simpa only [first] using result
  apply inclusionPath_complete_of_levels (build leaves) depth index height
  · omega
  · exact fun level levelBound =>
      levels_parent_equations depth leaves.size leaves enough size level levelBound
  · intro level levelBound
    have width := widths level (by omega)
    change index / 2^level < 2 * ((levels leaves.size leaves)[level]!.size / 2)
    rw [width]
    have diff : depth - level = (depth - level - 1) + 1 := by omega
    rw [diff, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    have product : 2^level * (2 * 2^(depth - level - 1)) = 2^depth := by
      rw [Nat.mul_comm 2, ← Nat.pow_succ, ← Nat.pow_add]
      congr 1
      omega
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos level)).mpr
    rw [Nat.mul_comm, product]
    omega

theorem build_verifyPath_complete (depth : Nat) (leaves : Array Digest)
    (size : leaves.size = 2^depth) (index : Nat) (bound : index < leaves.size) :
    verifyPath (treeRoot (build leaves)) leaves[index]! index
      (inclusionPath (build leaves) index).toList = true := by
  have enough : depth ≤ leaves.size := by
    rw [size]
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have height := (levels_power_shape depth leaves.size leaves enough size).1
  have root : treeRoot (build leaves) = (build leaves)[depth]![0]! := by
    simp [treeRoot, Array.back!, build, height]
  have pathLength : (inclusionPath (build leaves) index).toList.length = depth := by
    simp only [inclusionPath, Array.length_toList, Array.size_map, Array.size_range,
      build, height, Nat.add_sub_cancel]
  unfold verifyPath
  apply decide_eq_true
  constructor
  · rw [pathLength, ← size]
    exact bound
  · rw [root]
    exact build_inclusion_complete depth leaves size index bound

def digest32ToSpec (d : Model.Merkle.Digest32) : Digest := toDigest d.toBytes

theorem vector_toArray_ofFn_get {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (hi : i < n) :
    (Vector.ofFn f).toArray[i]'(by simpa using hi) = f ⟨i, hi⟩ := by
  simp only [Vector.toArray_ofFn]
  exact ofFn_lookup f i (by simpa using hi)

theorem digestBytes_toDigest_eq (b : ByteArray) (h : b.size = 32) :
    digestBytes (toDigest b) = b := by
  unfold digestBytes toDigest
  apply ByteArray.ext
  apply Array.ext
  · exact (Vector.size_toArray _).trans h.symm
  · intro i hi hj
    have bound : i < 32 := by simpa using hi
    have hb : i < b.size := by omega
    rw [vector_toArray_ofFn_get _ i bound]
    exact getElem!_pos b i hb

theorem digest32ToSpec_bytes (d : Model.Merkle.Digest32) :
    digestBytes (digest32ToSpec d) = d.toBytes :=
  digestBytes_toDigest_eq d.toBytes (digest32_toBytes_size d)

theorem range8_list : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide

theorem range8_array : Array.range 8 = #[0, 1, 2, 3, 4, 5, 6, 7] := by decide

theorem wordBytes_eq_encodeBytesK (w : UInt64) :
    Spec.Keccak.wordBytes w = Model.Field.encodeBytesK w := by
  unfold Spec.Keccak.wordBytes Model.Field.encodeBytesK
  rw [range8_array]
  apply ByteArray.ext
  apply Array.ext
  · simp
  · intro i hi hj
    have hb : i < 8 := by simpa using hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [← UInt8.ofNat_uInt64ToNat, UInt64.toNat_shiftRight]

theorem nat_or_mul_256 (a b k : Nat) (hb : b < 2 ^ (8 * k)) :
    b ||| (a <<< (8 * k)) = b + a * 2 ^ (8 * k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 8 * k
  · have hnb : ¬ i ≥ 8 * k := by omega
    have hmod : (b + a * 2 ^ (8 * k)) % 2 ^ (8 * k) = b := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
    have htb : (b + a * 2 ^ (8 * k)).testBit i = b.testBit i := by
      have h1 := Nat.testBit_mod_two_pow (b + a * 2 ^ (8 * k)) (8 * k) i
      rw [hmod] at h1
      simpa [hi] using h1.symm
    simp [hnb, htb]
  · have hge : i ≥ 8 * k := by omega
    have hbt : b.testBit i = false := by
      have hpow : b < 2 ^ i := Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hge)
      exact Nat.testBit_lt_two_pow (i := i) (x := b) (lt := hpow)
    have heq : i = (i - 8 * k) + 8 * k := by omega
    have hdiv : (b + a * 2 ^ (8 * k)) / 2 ^ (8 * k) = a := by
      have hpos : 0 < 2 ^ (8 * k) := Nat.two_pow_pos _
      rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hb, Nat.zero_add]
    have htb : (b + a * 2 ^ (8 * k)).testBit i = a.testBit (i - 8 * k) := by
      conv => lhs; rw [heq]
      rw [Nat.testBit_add, hdiv]
    simp [hge, hbt, htb]

theorem uint64_or_byte_shift (acc : UInt64) (x : UInt8) (k : Nat)
    (hk : k < 8) (hacc : acc.toNat < 2 ^ (8 * k)) :
    (acc ||| (UInt64.ofNat x.toNat <<< UInt64.ofNat (8 * k))).toNat =
      acc.toNat + (x.toNat <<< (8 * k)) := by
  have hx : x.toNat < 256 := x.toNat_lt
  have hshift_mod : (UInt64.ofNat (8 * k)).toNat % 64 = 8 * k := by
    have hk64 : 8 * k < 64 := by omega
    have hk264 : 8 * k < 2 ^ 64 := by omega
    simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hk264, Nat.mod_eq_of_lt hk64]
  have hx64 : (UInt64.ofNat x.toNat).toNat = x.toNat := by
    have hx264 : x.toNat < 2 ^ 64 := by omega
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hx264]
  have hshl_lt : x.toNat <<< (8 * k) < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    have hle : 2 ^ 8 * 2 ^ (8 * k) ≤ 2 ^ 64 := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hmul : x.toNat * 2 ^ (8 * k) < 2 ^ 8 * 2 ^ (8 * k) :=
      Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
    exact Nat.lt_of_lt_of_le hmul hle
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, hshift_mod, hx64,
    Nat.mod_eq_of_lt hshl_lt, nat_or_mul_256 x.toNat acc.toNat k hacc, Nat.shiftLeft_eq]

theorem byte_getD_eq_list_getElem! (b : ByteArray) (j : Nat) :
    (b.data[j]?.getD 0).toNat = b.data.toList[j]!.toNat := by
  rw [List.getElem!_eq_getElem?_getD]
  cases h : b.data[j]? <;> simp [h] <;> rfl

theorem pack8_or_eq_readLimb_val (x0 x1 x2 x3 x4 x5 x6 x7 : UInt8) :
    (((0 : UInt64) ||| UInt64.ofNat x0.toNat <<< UInt64.ofNat (8 * 0) |||
      UInt64.ofNat x1.toNat <<< UInt64.ofNat (8 * 1) |||
      UInt64.ofNat x2.toNat <<< UInt64.ofNat (8 * 2) |||
      UInt64.ofNat x3.toNat <<< UInt64.ofNat (8 * 3) |||
      UInt64.ofNat x4.toNat <<< UInt64.ofNat (8 * 4) |||
      UInt64.ofNat x5.toNat <<< UInt64.ofNat (8 * 5) |||
      UInt64.ofNat x6.toNat <<< UInt64.ofNat (8 * 6) |||
      UInt64.ofNat x7.toNat <<< UInt64.ofNat (8 * 7))) =
    UInt64.ofNat (x0.toNat + (x1.toNat <<< 8) + (x2.toNat <<< 16) + (x3.toNat <<< 24) +
      (x4.toNat <<< 32) + (x5.toNat <<< 40) + (x6.toNat <<< 48) + (x7.toNat <<< 56)) := by
  apply UInt64.toNat_inj.mp
  have h0 := x0.toNat_lt
  have h1 := x1.toNat_lt
  have h2 := x2.toNat_lt
  have h3 := x3.toNat_lt
  have h4 := x4.toNat_lt
  have h5 := x5.toNat_lt
  have h6 := x6.toNat_lt
  have h7 := x7.toNat_lt
  let w0 : UInt64 := (0 : UInt64) ||| UInt64.ofNat x0.toNat <<< UInt64.ofNat (8 * 0)
  have e0 : w0.toNat = x0.toNat := by
    simp [w0]
  let w1 : UInt64 := w0 ||| UInt64.ofNat x1.toNat <<< UInt64.ofNat (8 * 1)
  have e1 : w1.toNat = x0.toNat + (x1.toNat <<< 8) := by
    simpa [w1, e0] using uint64_or_byte_shift w0 x1 1 (by decide) (by rw [e0]; omega)
  let w2 : UInt64 := w1 ||| UInt64.ofNat x2.toNat <<< UInt64.ofNat (8 * 2)
  have e2 : w2.toNat = x0.toNat + (x1.toNat <<< 8) + (x2.toNat <<< 16) := by
    simpa [w2, e1] using uint64_or_byte_shift w1 x2 2 (by decide) (by rw [e1, Nat.shiftLeft_eq]; omega)
  let w3 : UInt64 := w2 ||| UInt64.ofNat x3.toNat <<< UInt64.ofNat (8 * 3)
  have e3 : w3.toNat = x0.toNat + (x1.toNat <<< 8) + (x2.toNat <<< 16) + (x3.toNat <<< 24) := by
    simpa [w3, e2] using uint64_or_byte_shift w2 x3 3 (by decide)
      (by rw [e2]; simp only [Nat.shiftLeft_eq]; omega)
  let w4 : UInt64 := w3 ||| UInt64.ofNat x4.toNat <<< UInt64.ofNat (8 * 4)
  have e4 : w4.toNat = x0.toNat + (x1.toNat <<< 8) + (x2.toNat <<< 16) + (x3.toNat <<< 24) +
      (x4.toNat <<< 32) := by
    simpa [w4, e3] using uint64_or_byte_shift w3 x4 4 (by decide)
      (by rw [e3]; simp only [Nat.shiftLeft_eq]; omega)
  let w5 : UInt64 := w4 ||| UInt64.ofNat x5.toNat <<< UInt64.ofNat (8 * 5)
  have e5 : w5.toNat = x0.toNat + (x1.toNat <<< 8) + (x2.toNat <<< 16) + (x3.toNat <<< 24) +
      (x4.toNat <<< 32) + (x5.toNat <<< 40) := by
    simpa [w5, e4] using uint64_or_byte_shift w4 x5 5 (by decide)
      (by rw [e4]; simp only [Nat.shiftLeft_eq]; omega)
  let w6 : UInt64 := w5 ||| UInt64.ofNat x6.toNat <<< UInt64.ofNat (8 * 6)
  have e6 : w6.toNat = x0.toNat + (x1.toNat <<< 8) + (x2.toNat <<< 16) + (x3.toNat <<< 24) +
      (x4.toNat <<< 32) + (x5.toNat <<< 40) + (x6.toNat <<< 48) := by
    simpa [w6, e5] using uint64_or_byte_shift w5 x6 6 (by decide)
      (by rw [e5]; simp only [Nat.shiftLeft_eq]; omega)
  let w7 : UInt64 := w6 ||| UInt64.ofNat x7.toNat <<< UInt64.ofNat (8 * 7)
  have e7 : w7.toNat = x0.toNat + (x1.toNat <<< 8) + (x2.toNat <<< 16) + (x3.toNat <<< 24) +
      (x4.toNat <<< 32) + (x5.toNat <<< 40) + (x6.toNat <<< 48) + (x7.toNat <<< 56) := by
    simpa [w7, e6] using uint64_or_byte_shift w6 x7 7 (by decide)
      (by rw [e6]; simp only [Nat.shiftLeft_eq]; omega)
  have hsum_lt : x0.toNat + (x1.toNat <<< 8) + (x2.toNat <<< 16) + (x3.toNat <<< 24) +
      (x4.toNat <<< 32) + (x5.toNat <<< 40) + (x6.toNat <<< 48) + (x7.toNat <<< 56) < 2 ^ 64 := by
    simp only [Nat.shiftLeft_eq]
    omega
  change w7.toNat = _
  rw [e7, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hsum_lt]

theorem wordAt_eq_readLimb (b : ByteArray) (offset : Nat) :
    Spec.Keccak.wordAt b offset = Model.Field.readLimb b offset := by
  unfold Spec.Keccak.wordAt Model.Field.readLimb
  rw [range8_list]
  simp only [List.foldl_cons, List.foldl_nil, Nat.add_zero, byte_getD_eq_list_getElem!]
  exact pack8_or_eq_readLimb_val _ _ _ _ _ _ _ _

theorem wordBytes_wordAt_extract (b : ByteArray) (offset : Nat) (h : offset + 8 ≤ b.size) :
    Spec.Keccak.wordBytes (Spec.Keccak.wordAt b offset) = Proofs.Field.byteSlice b offset 8 := by
  rw [wordBytes_eq_encodeBytesK, wordAt_eq_readLimb]
  exact Proofs.Field.encode_readLimb_extract b offset h

theorem wordsBytes_four_roundtrip (b : ByteArray) (h : b.size = 32) :
    Spec.Keccak.wordsBytes #[Spec.Keccak.wordAt b 0, Spec.Keccak.wordAt b 8,
      Spec.Keccak.wordAt b 16, Spec.Keccak.wordAt b 24] = b := by
  unfold Spec.Keccak.wordsBytes
  simp only [← Array.foldl_toList, List.foldl_cons, List.foldl_nil, Array.empty_append]
  have s0 := congrArg ByteArray.data (wordBytes_wordAt_extract b 0 (by omega))
  have s1 := congrArg ByteArray.data (wordBytes_wordAt_extract b 8 (by omega))
  have s2 := congrArg ByteArray.data (wordBytes_wordAt_extract b 16 (by omega))
  have s3 := congrArg ByteArray.data (wordBytes_wordAt_extract b 24 (by omega))
  rw [s0, s1, s2, s3]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [Array.toList_append, Proofs.Field.byteSlice, List.drop_zero]
  have hl : b.data.toList.length = 32 := by simpa only [Array.length_toList, ByteArray.size] using h
  have hlast : (b.data.toList.drop 24).take 8 = b.data.toList.drop 24 :=
    List.take_of_length_le (by simp only [List.length_drop, hl]; decide)
  rw [hlast, List.append_assoc, List.append_assoc]
  have hd24 : b.data.toList.drop 24 = (b.data.toList.drop 16).drop 8 := by simp only [List.drop_drop]
  have hd16 : b.data.toList.drop 16 = (b.data.toList.drop 8).drop 8 := by simp only [List.drop_drop]
  rw [hd24, List.take_append_drop, hd16, List.take_append_drop, List.take_append_drop]

theorem round_size (a : Spec.Keccak.State) (r : UInt64) :
    (Spec.Keccak.round a r).size = 25 := by
  simp only [Spec.Keccak.round, Spec.Keccak.iota, Spec.Keccak.chi,
    Array.size_set!, Array.size_map, Array.size_range]

theorem permute_size (a : Spec.Keccak.State) (ha : a.size = 25) :
    (Spec.Keccak.permute a).size = 25 := by
  unfold Spec.Keccak.permute
  rw [← Array.foldl_toList]
  generalize Spec.Keccak.rc.toList = rs
  induction rs generalizing a with
  | nil => exact ha
  | cons r rs ih =>
    simp only [List.foldl_cons]
    exact ih _ (round_size a r)

theorem absorbBlock_size (a : Spec.Keccak.State) (b : ByteArray) :
    (Spec.Keccak.absorbBlock a b).size = 25 := by
  unfold Spec.Keccak.absorbBlock
  exact permute_size _ (by simp)

theorem foldl_absorb_size (bs : List ByteArray) (a : Spec.Keccak.State) (ha : a.size = 25) :
    (bs.foldl Spec.Keccak.absorbBlock a).size = 25 := by
  induction bs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih _ (absorbBlock_size a x)

theorem keccak256_size (b : ByteArray) : (Spec.Keccak.keccak256 b).size = 32 := by
  unfold Spec.Keccak.keccak256 Spec.Keccak.hashWithDomain
  rw [wordsBytes_size]
  have h := foldl_absorb_size (Spec.Keccak.blocks b).toList Spec.Keccak.zero (by simp [Spec.Keccak.zero])
  have he : (Array.foldl Spec.Keccak.absorbBlock Spec.Keccak.zero (Spec.Keccak.blocks b)).size = 25 := by
    simpa [Array.foldl_toList] using h
  simp [Array.size_extract, he]

theorem hashPair_toSpec (left right : Model.Merkle.Digest32) :
    digest32ToSpec (Model.Merkle.Digest32.hashPair left right) =
      compress (digest32ToSpec left) (digest32ToSpec right) := by
  unfold compress
  rw [digest32ToSpec_bytes, digest32ToSpec_bytes]
  unfold digest32ToSpec hashLeaf Model.Merkle.Digest32.hashPair Model.Merkle.Digest32.toBytes
  exact congrArg toDigest
    (wordsBytes_four_roundtrip (Spec.Keccak.keccak256 (left.toBytes ++ right.toBytes))
      (keccak256_size _))

theorem heap_refines_levels (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree)
    (built : Model.Merkle.buildHeap depth leaves = some tree) :
    let specLeaves := leaves.map digest32ToSpec
    ∀ level, level ≤ depth → ∀ index, index < 2^(depth - level) →
      digest32ToSpec tree.nodes[(2^(depth - level)) + index]! =
        (levels specLeaves.size specLeaves)[level]![index]! := by
  intro specLeaves level levelBound index indexBound
  have leafCount : leaves.size = 2^depth := (heap_build_domain depth leaves).mp
    (by simp [built])
  have size : specLeaves.size = 2^depth := by simpa [specLeaves] using leafCount
  have enough : depth ≤ specLeaves.size := by
    rw [size]
    exact Nat.le_of_lt Nat.lt_two_pow_self
  induction level generalizing index with
  | zero =>
    have leafBound : index < leaves.size := by
      rw [leafCount]
      simpa using indexBound
    have pos : 2^(depth - 0) + index = 2^depth + index := by simp
    rw [pos, built_heap_leaf depth leaves tree built index leafBound]
    have first : (levels specLeaves.size specLeaves)[0]! = specLeaves := by
      cases specLeaves.size <;>
        simp only [levels_zero, levels_succ] <;>
        (try split) <;>
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append]
    rw [first]
    simp [specLeaves, leafBound]
  | succ level ih =>
    have diff : depth - level = (depth - (level + 1)) + 1 := by omega
    have width : 2^(depth - level) = 2 * 2^(depth - (level + 1)) := by
      rw [diff, Nat.pow_succ, Nat.mul_comm]
    have childLeft : 2 * (2^(depth - (level + 1)) + index) =
        2^(depth - level) + 2 * index := by
      rw [Nat.mul_add, ← width]
    have childRight : 2 * (2^(depth - (level + 1)) + index) + 1 =
        2^(depth - level) + (2 * index + 1) := by
      rw [childLeft, Nat.add_assoc]
    have leftChildBound : 2 * index < 2^(depth - level) := by omega
    have rightChildBound : 2 * index + 1 < 2^(depth - level) := by omega
    have internal : 2^(depth - (level + 1)) + index < 2^depth := by
      have lePow : 2 * 2^(depth - (level + 1)) ≤ 2^depth := by
        rw [← width]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have posNode : 0 < 2^(depth - (level + 1)) + index := by
      have h := Nat.two_pow_pos (depth - (level + 1))
      omega
    have parent := built_heap_parent_equations depth leaves tree built
      (2^(depth - (level + 1)) + index) posNode internal
    rw [parent, hashPair_toSpec, childRight, childLeft]
    rw [ih (by omega) (2 * index) leftChildBound,
      ih (by omega) (2 * index + 1) rightChildBound]
    have step := levels_parent_equations depth specLeaves.size specLeaves enough size level (by omega)
    rw [step]
    have levelWidth := (levels_power_shape depth specLeaves.size specLeaves enough size).2 level (by omega)
    have mappedBound : index < (parentLevel (levels specLeaves.size specLeaves)[level]!).size := by
      simp only [parentLevel, Array.size_map, Array.size_range, levelWidth, width]
      omega
    rw [getElem!_pos (parentLevel (levels specLeaves.size specLeaves)[level]!) index mappedBound]
    simp only [parentLevel, Array.getElem_map]
    simp only [Array.range]
    rw [ofFn_lookup]

theorem heapRoot_refines_spec (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree)
    (built : Model.Merkle.buildHeap depth leaves = some tree) :
    (Model.Merkle.heapRoot tree).map digest32ToSpec =
      some (treeRoot (build (leaves.map digest32ToSpec))) := by
  have leafCount : leaves.size = 2^depth := (heap_build_domain depth leaves).mp (by simp [built])
  have size : (leaves.map digest32ToSpec).size = 2^depth := by simpa using leafCount
  have enough : depth ≤ (leaves.map digest32ToSpec).size := by
    rw [size]
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have height := (levels_power_shape depth (leaves.map digest32ToSpec).size
    (leaves.map digest32ToSpec) enough size).1
  obtain ⟨_, nodesSize⟩ := built_heap_shape depth leaves tree built
  have bound : 1 < tree.nodes.size := by
    have pos := Nat.two_pow_pos depth
    omega
  have rootEq := heap_refines_levels depth leaves tree built depth (Nat.le_refl depth) 0 (by simp)
  unfold Model.Merkle.heapRoot
  rw [Array.getElem?_eq_getElem bound]
  simp only [Option.map_some, Option.some.injEq]
  have lookup : tree.nodes[1] = tree.nodes[1]! := (getElem!_pos tree.nodes 1 bound).symm
  rw [lookup]
  have idxOne : 2^(depth - depth) + 0 = 1 := by simp
  rw [← idxOne, rootEq]
  unfold treeRoot Array.back! build
  rw [height]
  rfl

theorem heapPath_refines_spec (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (index : Nat)
    (built : Model.Merkle.buildHeap depth leaves = some tree)
    (bound : index < 2^depth) :
    (Model.Merkle.heapPath tree index).map (fun p => p.map digest32ToSpec) =
      some (inclusionPath (build (leaves.map digest32ToSpec)) index) := by
  have leafCount : leaves.size = 2^depth := (heap_build_domain depth leaves).mp (by simp [built])
  have size : (leaves.map digest32ToSpec).size = 2^depth := by simpa using leafCount
  have enough : depth ≤ (leaves.map digest32ToSpec).size := by
    rw [size]
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have height := (levels_power_shape depth (leaves.map digest32ToSpec).size
    (leaves.map digest32ToSpec) enough size).1
  obtain ⟨treeDepth, nodesSize⟩ := built_heap_shape depth leaves tree built
  unfold Model.Merkle.heapPath inclusionPath build
  rw [treeDepth, ite_eq_left ⟨bound, nodesSize⟩, height]
  simp only [Option.map_some, Option.some.injEq, Nat.add_sub_cancel]
  apply Array.toList_inj.mp
  simp only [Array.toList_map, range_toList, List.map_map, Function.comp_def]
  apply List.ext_getElem
  · simp
  · intro level hl hr
    have levelBound : level < depth := by simpa using hl
    simp only [List.getElem_map, List.getElem_range]
    have divShift : (2^depth + index) / 2^level = 2^(depth - level) + index / 2^level := by
      have splitPow : 2^depth = 2^(depth - level) * 2^level := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      rw [splitPow, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos level), Nat.add_comm]
    have qBound : index / 2^level < 2^(depth - level) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos level)).mpr
      have splitPow : 2^(depth - level) * 2^level = 2^depth := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      rw [splitPow]
      exact bound
    have evenBase : 2^(depth - level) % 2 = 0 := by
      have diff : depth - level = (depth - level - 1) + 1 := by omega
      rw [diff, Nat.pow_succ]
      omega
    have sibHelper (q w : Nat) (hq : q < w) (hw : w % 2 = 0) :
        (q ^^^ 1) < w ∧ ((w + q) ^^^ 1) = w + (q ^^^ 1) := by
      rw [sibling_index, sibling_index]
      have hm : (w + q) % 2 = q % 2 := by omega
      rw [hm]
      rcases Nat.mod_two_eq_zero_or_one q with hpar | hpar
      · rw [ite_eq_left hpar, ite_eq_left hpar]
        constructor <;> omega
      · have hne : q % 2 ≠ 0 := by omega
        rw [ite_eq_right hne, ite_eq_right hne]
        constructor <;> omega
    obtain ⟨sibBound, xorAdd⟩ := sibHelper (index / 2^level) (2^(depth - level)) qBound evenBase
    rw [divShift, xorAdd]
    exact heap_refines_levels depth leaves tree built level (by omega)
      ((index / 2^level) ^^^ 1) sibBound

theorem heap_verifyPath_complete (depth : Nat) (leaves : Array Model.Merkle.Digest32)
    (tree : Model.Merkle.HeapTree) (root : Model.Merkle.Digest32)
    (path : Array Model.Merkle.Digest32) (index : Nat)
    (built : Model.Merkle.buildHeap depth leaves = some tree)
    (hasRoot : Model.Merkle.heapRoot tree = some root)
    (hasPath : Model.Merkle.heapPath tree index = some path) :
    verifyPath (digest32ToSpec root) (digest32ToSpec leaves[index]!) index
      (path.map digest32ToSpec).toList = true := by
  obtain ⟨treeDepth, _⟩ := built_heap_shape depth leaves tree built
  have dom := (heap_path_domain tree index).mp (by simp [hasPath])
  have bound : index < 2^depth := by simpa [treeDepth] using dom.1
  have leafCount : leaves.size = 2^depth := (heap_build_domain depth leaves).mp (by simp [built])
  have leafBound : index < leaves.size := by rw [leafCount]; exact bound
  have specSize : (leaves.map digest32ToSpec).size = 2^depth := by simpa using leafCount
  have specBound : index < (leaves.map digest32ToSpec).size := by simpa using leafBound
  have rootSpec := heapRoot_refines_spec depth leaves tree built
  rw [hasRoot] at rootSpec
  simp only [Option.map_some, Option.some.injEq] at rootSpec
  have pathSpec := heapPath_refines_spec depth leaves tree index built bound
  rw [hasPath] at pathSpec
  simp only [Option.map_some, Option.some.injEq] at pathSpec
  have leafLookup : (leaves.map digest32ToSpec)[index]! = digest32ToSpec leaves[index]! := by
    simp [leafBound]
  rw [rootSpec, pathSpec, ← leafLookup]
  exact build_verifyPath_complete depth (leaves.map digest32ToSpec) specSize index specBound

end LeanVmXmss.Proofs.Merkle.Contracts
