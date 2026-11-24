import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1660

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_prefix (gs : List Gate) (w : List Bool) : w <+: gs.foldl step w := by
  induction gs generalizing w with
  | nil => exact List.prefix_refl w
  | cons g gs ih =>
    rw [List.foldl_cons]
    exact (List.prefix_append w _).trans (ih (step w g))

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma getD_of_prefix {l1 l2 : List Bool} (h : l1 <+: l2) {i : ℕ} (hi : i < l1.length) :
    l2.getD i false = l1.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    ((C.gates.take j).foldl step x) <+: C.wires x ∧
      ((C.gates.take j).foldl step x).length = x.length + j ∧
      (C.wires x).getD (x.length + j) false =
        (C.gates[j]).op.eval ((C.gates[j]).inputs.map
          fun i => ((C.gates.take j).foldl step x).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by
    rw [List.getElem_cons_drop]
    exact (List.take_append_drop j C.gates).symm
  have hlen : ((C.gates.take j).foldl step x).length = x.length + j := by
    rw [foldl_length, List.length_take]
    omega
  have hW : C.wires x = (C.gates.drop (j + 1)).foldl step
      (step ((C.gates.take j).foldl step x) C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpre : step ((C.gates.take j).foldl step x) C.gates[j] <+: C.wires x := by
    rw [hW]
    exact foldl_prefix _ _
  refine ⟨(List.prefix_append _ _).trans hpre, hlen, ?_⟩
  rw [getD_of_prefix hpre (by simp [step, hlen])]
  rw [← hlen]
  simp [step]

def front (C : Circuit) (n : ℕ) (j : ℕ) : Finset ℕ :=
  if h : C.gates.length ≤ j then {C.output}
  else
    if n + j ∈ front C n (j + 1) then
      ((front C n (j + 1)).erase (n + j)) ∪
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.toFinset
    else front C n (j + 1)
termination_by C.gates.length - j

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]

lemma card_front (C : Circuit) (n : ℕ) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ m j, C.gates.length - j = m → (front C n j).card ≤ m + 1 := by
  intro m
  induction m with
  | zero =>
    intro j hj
    rw [front, dif_pos (by omega)]
    simp
  | succ m ih =>
    intro j hj
    have hlt : j < C.gates.length := by omega
    have ih' := ih (j + 1) (by omega)
    rw [front, dif_neg (by omega)]
    split_ifs with hmem
    · have h1 := Finset.card_union_le ((front C n (j + 1)).erase (n + j))
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.toFinset
      have h2 := Finset.card_erase_of_mem hmem
      have h3 : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.toFinset.card ≤ 2 := by
        rw [gateAt_eq C j hlt]
        exact (List.toFinset_card_le _).trans (hfan _ (List.getElem_mem hlt))
      have h4 : 0 < (front C n (j + 1)).card := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    · omega

lemma bound_front (C : Circuit) (n : ℕ)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) :
    ∀ m j, C.gates.length - j = m → j ≤ C.gates.length →
      ∀ w ∈ front C n j, w < n + j ∨ n + C.gates.length ≤ w := by
  intro m
  induction m with
  | zero =>
    intro j hj hjl w hw
    rw [front, dif_pos (by omega)] at hw
    simp at hw
    omega
  | succ m ih =>
    intro j hj hjl w hw
    have hlt : j < C.gates.length := by omega
    have ih' := ih (j + 1) (by omega) (by omega)
    rw [front, dif_neg (by omega)] at hw
    split_ifs at hw with hmem
    · rcases Finset.mem_union.mp hw with h | h
      · have hne := Finset.ne_of_mem_erase h
        rcases ih' w (Finset.mem_of_mem_erase h) with h' | h'
        · left; omega
        · right; exact h'
      · left
        exact hrb j hlt w (List.mem_toFinset.mp h)
    · rcases ih' w hw with h' | h'
      · have : w ≠ n + j := fun e => hmem (e ▸ hw)
        left; omega
      · right; exact h'

lemma sem_front (C : Circuit) (n : ℕ)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n) :
    ∀ m j, C.gates.length - j = m →
      (∀ w ∈ front C n j, (C.wires x).getD w false = (C.wires y).getD w false) →
      C.eval x = C.eval y := by
  intro m
  induction m with
  | zero =>
    intro j hj hag
    have := hag C.output (by rw [front, dif_pos (by omega)]; simp)
    exact this
  | succ m ih =>
    intro j hj hag
    have hlt : j < C.gates.length := by omega
    apply ih (j + 1) (by omega)
    intro w hw
    rw [front, dif_neg (by omega)] at hag
    by_cases hmem : n + j ∈ front C n (j + 1)
    · rw [if_pos hmem] at hag
      by_cases hwj : w = n + j
      · subst hwj
        obtain ⟨px, lx, ex⟩ := wires_gate C x j hlt
        obtain ⟨py, ly, ey⟩ := wires_gate C y j hlt
        rw [hx] at ex lx
        rw [hy] at ey ly
        rw [ex, ey]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hib : i < n + j := by
          have := hrb j hlt i (by rw [gateAt_eq C j hlt]; exact hi)
          exact this
        rw [← getD_of_prefix px (by omega), ← getD_of_prefix py (by omega)]
        apply hag
        apply Finset.mem_union_right
        rw [gateAt_eq C j hlt]
        exact List.mem_toFinset.mpr hi
      · exact hag w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwj, hw⟩))
    · rw [if_neg hmem] at hag
      exact hag w hw

lemma size_bound (n : ℕ) (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hsens : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) : n ≤ C.size + 1 := by
  have hsub : Finset.range n ⊆ front C n 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_contra hnot
    obtain ⟨x, y, hxy, hne⟩ := hsens ⟨i, hi⟩
    apply hne
    apply sem_front C n hrb (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ 0 rfl
    intro w hw
    have hwi : w ≠ i := fun e => hnot (e ▸ hw)
    rcases bound_front C n hrb _ 0 rfl (Nat.zero_le _) w hw with h | h
    · have hwn : w < n := by omega
      rw [wires_eq, wires_eq, getD_of_prefix (foldl_prefix C.gates (List.ofFn x)) (by simpa using hwn),
        getD_of_prefix (foldl_prefix C.gates (List.ofFn y)) (by simpa using hwn)]
      have hk : (⟨w, hwn⟩ : Fin n) ≠ ⟨i, hi⟩ := fun e => hwi (Fin.mk.inj e)
      have := hxy ⟨w, hwn⟩ hk
      simp [List.getD_eq_getElem?_getD, hwn, this]
    · have lx : (C.wires (List.ofFn x)).length ≤ w := by
        rw [wires_eq, foldl_length]; simp; omega
      have ly : (C.wires (List.ofFn y)).length ≤ w := by
        rw [wires_eq, foldl_length]; simp; omega
      rw [List.getD_eq_default _ _ lx, List.getD_eq_default _ _ ly]
  have h1 := Finset.card_le_card hsub
  have h2 := card_front C n hfan _ 0 rfl
  simp at h1
  unfold Circuit.size
  omega

end PEqualNP.Outside.L_meta_1660

theorem PEqualNP.Outside.L_meta_1660 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1) → (∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z1 = false) → 2 * N ≤ C.size + 1 := by
  intro q N I _ C hq hN hline hunique hmono hrb hacc hsound
  have hN2 : 2 ≤ N := by subst hN; nlinarith
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hmono g hg).2
  have hcf : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = C.eval (List.ofFn z) := fun z => rfl
  have hcn : ∀ a b : Fin N, Fin.castAdd N a ≠ Fin.natAdd N b := by
    intro a b e
    have := congrArg Fin.val e
    simp at this
    omega
  have key := PEqualNP.Outside.L_meta_1660.size_bound (N + N) C hfan hrb ?_
  · omega
  intro i
  obtain ⟨p, rfl⟩ | ⟨l, rfl⟩ : (∃ p : Fin N, i = Fin.castAdd N p) ∨
      (∃ l : Fin N, i = Fin.natAdd N l) := by
    by_cases hi : i.val < N
    · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · exact Or.inr ⟨⟨i.val - N, by omega⟩, Fin.ext (by simp; omega)⟩
  · -- a point: a line through it, the pair is accepted, the line alone is rejected
    let pb : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hpb : p ≠ pb := by
      intro e
      have := congrArg Fin.val e
      by_cases h0 : p.val = 0 <;> simp [pb, h0] at this <;> omega
    obtain ⟨l, ⟨hpl, -⟩, -⟩ := hunique p pb hpb
    refine ⟨fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l),
      fun k => decide (k = Fin.natAdd N l), ?_, ?_⟩
    · intro k hk
      simp [hk]
    · rw [← hcf, ← hcf, hacc p l hpl]
      have hfalse := hsound (fun k => decide (k = Fin.natAdd N l)) ?_ ?_
      · rw [hfalse]; decide
      · refine le_trans ?_ (show 1 ≤ q by omega)
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hb
        have h1 := congrArg Fin.val ha
        have h2 := congrArg Fin.val hb
        simp at h1 h2
        exact Fin.ext (by omega)
      · rintro ⟨p1c, l1c, -, hp, -⟩
        simp only [decide_eq_true_eq] at hp
        exact hcn _ _ hp
  · -- a line: a point on it, the pair is accepted, the point alone is rejected
    have hpos : 0 < (Finset.univ.filter (fun p0 => I p0 l)).card := by
      rw [hline l]; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have hpl : I p l := by simpa using hp
    refine ⟨fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l),
      fun k => decide (k = Fin.castAdd N p), ?_, ?_⟩
    · intro k hk
      simp only [show ¬ (k = Fin.natAdd N l) from hk, or_false]
    · rw [← hcf, ← hcf, hacc p l hpl]
      have hfalse := hsound (fun k => decide (k = Fin.castAdd N p)) ?_ ?_
      · rw [hfalse]; decide
      · refine le_trans (le_of_eq ?_) (Nat.zero_le q)
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro b _ hb
        simp only [decide_eq_true_eq] at hb
        exact hcn p b hb.symm
      · rintro ⟨p1c, l1c, -, -, hl⟩
        simp only [decide_eq_true_eq] at hl
        exact hcn p l1c hl.symm
