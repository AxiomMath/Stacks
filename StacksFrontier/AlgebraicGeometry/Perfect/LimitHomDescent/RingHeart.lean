module

public import StacksFrontier.Homology.HomotopyCategory.FilteredColimitHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent

/-!
# Maps in the homotopy category into a filtered colimit of complexes, with a degree bound

Let `N` be a directed system of complexes of `R`-modules whose degreewise filtered colimit is
`P`, and let `E` be a complex of finitely presented `R`-modules. Suppose that outside a finite set
`W` of degrees either `E` vanishes, or `P` vanishes in degrees `n` and `n - 1` and every `N j`
vanishes in degrees `n` and `n + 1`. Then `Hom_{K(R)}(E, P)` is the filtered colimit of the
`Hom_{K(R)}(E, N j)`. This covers a bounded `E` (take `W` the support of `E`) and a bounded above
`E` against a uniformly bounded system (take `W` an interval around the common support of the
`N j` and `P`).

## Main results

* `Stacks.LimitHomDescent.isStagesColimit_homotopy`: the statement.
-/

@[expose] public section

universe u v

open _root_.CategoryTheory _root_.CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open Stacks.FilteredColimitHom (Qh exists_lift exists_le_comp_eq t_comp_ι t_comp_t)

namespace Stacks.LimitHomDescent

variable {R : Type u} [Ring R] {J : Type v} [Preorder J] [IsDirected J (· ≤ ·)]
  {N : J → CochainComplex (ModuleCat.{u} R) ℤ}
  {t : ∀ ⦃i j : J⦄, i ≤ j → (N i ⟶ N j)}
  {P : CochainComplex (ModuleCat.{u} R) ℤ} {ιN : ∀ j, N j ⟶ P}
  {E : CochainComplex (ModuleCat.{u} R) ℤ}
  (htrans : ∀ ⦃i j k : J⦄ (h : i ≤ j) (h' : j ≤ k), t h ≫ t h' = t (h.trans h'))
  (hcompat : ∀ ⦃i j : J⦄ (h : i ≤ j), t h ≫ ιN j = ιN i)
  (hsurj : ∀ (n : ℤ) (x : P.X n), ∃ (j : J) (y : (N j).X n), (ιN j).f n y = x)
  (hzero : ∀ (n : ℤ) (j : J) (y : (N j).X n), (ιN j).f n y = 0 →
    ∃ (k : J) (h : j ≤ k), (t h).f n y = 0)
  (W : Finset ℤ)
  (hW : ∀ n : ℤ, n ∉ W → IsZero (E.X n) ∨
    (IsZero (P.X n) ∧ IsZero (P.X (n - 1)) ∧ ∀ j, IsZero ((N j).X n) ∧ IsZero ((N j).X (n + 1))))
  (hfp : ∀ n : ℤ, Module.FinitePresentation R (E.X n))

/-- A finite family of stages indexed by `W` has a common upper bound above a given stage. -/
private theorem exists_ge_forall_mem_image {J : Type v} [Preorder J] [IsDirected J (· ≤ ·)]
    (W : Finset ℤ) (b : ℤ → J) (j : J) : ∃ K, j ≤ K ∧ ∀ n ∈ W, b n ≤ K := by
  classical
  have : Nonempty J := ⟨j⟩
  obtain ⟨K, hK⟩ := Finset.exists_le (insert j (W.image b))
  exact ⟨K, hK j (Finset.mem_insert_self _ _), fun n hn =>
    hK _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn))⟩

include htrans hcompat hsurj hzero hW hfp in
/-- Surjectivity: every map in the homotopy category from `E` into the colimit factors through
some stage. -/
theorem exists_descends_homotopy' (g : (Qh R).obj E ⟶ (Qh R).obj P) :
    ∃ (j : J) (ψ : (Qh R).obj E ⟶ (Qh R).obj (N j)), ψ ≫ (Qh R).map (ιN j) = g := by
  classical
  obtain ⟨φ, rfl⟩ := (Qh R).map_surjective g
  have hlift : ∀ n : ℤ, ∃ (j : J) (ψ : E.X n ⟶ (N j).X n), ψ ≫ (ιN j).f n = φ.f n := by
    intro n
    have := hfp n
    exact exists_lift htrans hcompat hsurj hzero n n (φ.f n)
  choose a ψa hψa using hlift
  obtain ⟨j₀, -, haj⟩ := exists_ge_forall_mem_image W a (a 0)
  obtain ⟨u, hu_pos, hu_neg⟩ : ∃ u : ∀ n : ℤ, E.X n ⟶ (N j₀).X n,
      (∀ (n : ℤ) (hn : n ∈ W), u n = ψa n ≫ (t (haj n hn)).f n) ∧ ∀ n : ℤ, n ∉ W → u n = 0 :=
    ⟨fun n => if hn : n ∈ W then ψa n ≫ (t (haj n hn)).f n else 0,
      fun n hn => by simp [hn], fun n hn => by simp [hn]⟩
  have hu : ∀ n : ℤ, u n ≫ (ιN j₀).f n = φ.f n := by
    intro n
    by_cases hn : n ∈ W
    · rw [hu_pos n hn, Category.assoc, t_comp_ι hcompat, hψa n]
    · rcases hW n hn with h | h
      · exact h.eq_of_src _ _
      · exact h.1.eq_of_tgt _ _
  have hfix : ∀ n : ℤ, ∃ (k : J) (h : j₀ ≤ k),
      (u n ≫ (N j₀).d n (n + 1)) ≫ (t h).f (n + 1) =
        (E.d n (n + 1) ≫ u (n + 1)) ≫ (t h).f (n + 1) := by
    intro n
    by_cases hn : n ∈ W
    · have := hfp n
      refine exists_le_comp_eq htrans hzero n (n + 1) _ _ ?_
      have h1 : (u n ≫ (N j₀).d n (n + 1)) ≫ (ιN j₀).f (n + 1) = φ.f n ≫ P.d n (n + 1) := by
        rw [Category.assoc, ← (ιN j₀).comm n (n + 1), ← Category.assoc, hu n]
      have h2 : (E.d n (n + 1) ≫ u (n + 1)) ≫ (ιN j₀).f (n + 1) =
          E.d n (n + 1) ≫ φ.f (n + 1) := by
        rw [Category.assoc, hu (n + 1)]
      rw [h1, h2]
      exact φ.comm n (n + 1)
    · rcases hW n hn with h | h
      · exact ⟨j₀, le_rfl, h.eq_of_src _ _⟩
      · exact ⟨j₀, le_rfl, ((h.2.2 j₀).2).eq_of_tgt _ _⟩
  choose b hb hbeq using hfix
  obtain ⟨K, hj₀K, hbK⟩ := exists_ge_forall_mem_image W b j₀
  have hcomm : ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      (u i ≫ (t hj₀K).f i) ≫ (N K).d i j = E.d i j ≫ (u j ≫ (t hj₀K).f j) := by
    intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    by_cases hi : i ∈ W
    · have key := congrArg (fun w => w ≫ (t (hbK i hi)).f (i + 1)) (hbeq i)
      simp only [Category.assoc, t_comp_t htrans] at key
      have g1 : (u i ≫ (t hj₀K).f i) ≫ (N K).d i (i + 1)
          = (u i ≫ (N j₀).d i (i + 1)) ≫ (t hj₀K).f (i + 1) := by
        rw [Category.assoc, (t hj₀K).comm i (i + 1), ← Category.assoc]
      have g2 : E.d i (i + 1) ≫ (u (i + 1) ≫ (t hj₀K).f (i + 1))
          = (E.d i (i + 1) ≫ u (i + 1)) ≫ (t hj₀K).f (i + 1) := (Category.assoc _ _ _).symm
      rw [g1, g2]
      exact key
    · rcases hW i hi with h | h
      · exact h.eq_of_src _ _
      · exact ((h.2.2 K).2).eq_of_tgt _ _
  refine ⟨K, (Qh R).map { f := fun n => u n ≫ (t hj₀K).f n, comm' := hcomm }, ?_⟩
  rw [← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine (Category.assoc (u n) ((t hj₀K).f n) ((ιN K).f n)).trans ?_
  rw [t_comp_ι hcompat]
  exact hu n

include htrans hcompat hsurj hzero hW hfp in
/-- Injectivity at one stage: two maps in the homotopy category out of `E` into one stage which
become equal in the colimit are equal at a later stage. -/
theorem exists_le_eq_of_eq_homotopy_same' {j : J}
    (ψ₁ ψ₂ : (Qh R).obj E ⟶ (Qh R).obj (N j))
    (h : ψ₁ ≫ (Qh R).map (ιN j) = ψ₂ ≫ (Qh R).map (ιN j)) :
    ∃ (k : J) (hjk : j ≤ k), ψ₁ ≫ (Qh R).map (t hjk) = ψ₂ ≫ (Qh R).map (t hjk) := by
  classical
  obtain ⟨φ₁, rfl⟩ := (Qh R).map_surjective ψ₁
  obtain ⟨φ₂, rfl⟩ := (Qh R).map_surjective ψ₂
  have hH : (Qh R).map (φ₁ ≫ ιN j) = (Qh R).map (φ₂ ≫ ιN j) := by
    rw [Functor.map_comp, Functor.map_comp]; exact h
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy (φ₁ ≫ ιN j) (φ₂ ≫ ιN j)
    (HomotopyCategory.homotopyOfEq _ _ hH)
  have hlift : ∀ (p q : ℤ) (hpq : p + (-1) = q), ∃ (cc : J) (ww : E.X p ⟶ (N cc).X q),
      ww ≫ (ιN cc).f q = z.v p q hpq := by
    intro p q hpq
    have := hfp p
    exact exists_lift htrans hcompat hsurj hzero p q (z.v p q hpq)
  choose c w hw using hlift
  obtain ⟨l, hjl, hl⟩ := exists_ge_forall_mem_image W (fun p => c p (p - 1) (by omega)) j
  have hcl : ∀ (p q : ℤ) (hpq : p + (-1) = q), p ∈ W → c p q hpq ≤ l := by
    intro p q hpq hp
    obtain rfl : q = p - 1 := by omega
    exact hl p hp
  set z' : Cochain E (N l) (-1) := Cochain.mk (fun p q hpq =>
    if hp : p ∈ W then w p q hpq ≫ (t (hcl p q hpq hp)).f q else 0) with hz'
  have hz'v : ∀ (p q : ℤ) (hpq : p + (-1) = q), z'.v p q hpq ≫ (ιN l).f q = z.v p q hpq := by
    intro p q hpq
    by_cases hp : p ∈ W
    · rw [hz']
      simp only [Cochain.mk_v, hp, dite_true, Category.assoc, t_comp_ι hcompat]
      exact hw p q hpq
    · rcases hW p hp with h | h
      · exact h.eq_of_src _ _
      · obtain rfl : q = p - 1 := by omega
        exact h.2.1.eq_of_tgt _ _
  have hz'comp : z'.comp (Cochain.ofHom (ιN l)) (add_zero _) = z := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    rw [Cochain.comp_v _ _ _ p q q hpq (add_zero q), Cochain.ofHom_v]
    exact hz'v p q hpq
  have hcolim : ∀ p : ℤ,
      ((φ₁ ≫ t hjl).f p) ≫ (ιN l).f p =
        ((δ (-1) 0 z').v p p (add_zero p) + (φ₂ ≫ t hjl).f p) ≫ (ιN l).f p := by
    intro p
    have hzp := Cochain.congr_v hz p p (add_zero p)
    simp only [Cochain.ofHom_v, Cochain.add_v] at hzp
    have hδ : (δ (-1) 0 z').v p p (add_zero p) ≫ (ιN l).f p =
        (δ (-1) 0 z).v p p (add_zero p) := by
      rw [← hz'comp, δ_comp_ofHom, Cochain.comp_v _ _ _ p p p (add_zero p) (add_zero p),
        Cochain.ofHom_v]
    rw [Preadditive.add_comp, hδ]
    simp only [HomologicalComplex.comp_f, Category.assoc, t_comp_ι hcompat]
    simpa only [HomologicalComplex.comp_f] using hzp
  have hfix : ∀ p : ℤ, ∃ (k : J) (hlk : l ≤ k),
      ((φ₁ ≫ t hjl).f p) ≫ (t hlk).f p =
        ((δ (-1) 0 z').v p p (add_zero p) + (φ₂ ≫ t hjl).f p) ≫ (t hlk).f p := by
    intro p
    by_cases hp : p ∈ W
    · have := hfp p
      exact exists_le_comp_eq htrans hzero p p _ _ (hcolim p)
    · rcases hW p hp with h | h
      · exact ⟨l, le_rfl, h.eq_of_src _ _⟩
      · exact ⟨l, le_rfl, ((h.2.2 l).1).eq_of_tgt _ _⟩
  choose b hb hbeq using hfix
  obtain ⟨k, hlk, hbk⟩ := exists_ge_forall_mem_image W b l
  have hstage : ∀ p : ℤ,
      ((φ₁ ≫ t hjl).f p) ≫ (t hlk).f p =
        ((δ (-1) 0 z').v p p (add_zero p) + (φ₂ ≫ t hjl).f p) ≫ (t hlk).f p := by
    intro p
    by_cases hp : p ∈ W
    · have key := congrArg (fun v => v ≫ (t (hbk p hp)).f p) (hbeq p)
      simpa only [Category.assoc, t_comp_t htrans] using key
    · rcases hW p hp with h | h
      · exact h.eq_of_src _ _
      · exact ((h.2.2 k).1).eq_of_tgt _ _
  have hfinal : Cochain.ofHom (φ₁ ≫ t (hjl.trans hlk))
      = δ (-1) 0 (z'.comp (Cochain.ofHom (t hlk)) (add_zero _))
        + Cochain.ofHom (φ₂ ≫ t (hjl.trans hlk)) := by
    refine Cochain.ext₀ _ _ fun p => ?_
    rw [Cochain.add_v, δ_comp_ofHom, Cochain.comp_v _ _ _ p p p (add_zero p) (add_zero p),
      Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v]
    have hs := hstage p
    simp only [HomologicalComplex.comp_f, Category.assoc, t_comp_t htrans,
      Preadditive.add_comp] at hs ⊢
    exact hs
  refine ⟨k, hjl.trans hlk, ?_⟩
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact HomotopyCategory.eq_of_homotopy _ _ ((Cochain.equivHomotopy _ _).symm ⟨_, hfinal⟩)

include htrans hcompat hsurj hzero hW hfp in
/-- **`Hom_{K(R)}(E, P)` is the filtered colimit of the `Hom_{K(R)}(E, N j)`.** -/
theorem isStagesColimit_homotopy :
    Stacks.IsStagesColimit
      (fun i j (h : i ≤ j) (ψ : (Qh R).obj E ⟶ (Qh R).obj (N i)) => ψ ≫ (Qh R).map (t h))
      (fun j (ψ : (Qh R).obj E ⟶ (Qh R).obj (N j)) => ψ ≫ (Qh R).map (ιN j)) where
  ι_trans i j h ψ := by rw [Category.assoc, ← Functor.map_comp, hcompat h]
  exists_stage g := exists_descends_homotopy' htrans hcompat hsurj hzero W hW hfp g
  exists_trans_eq i ψ ψ' hψ :=
    exists_le_eq_of_eq_homotopy_same' htrans hcompat hsurj hzero W hW hfp ψ ψ' hψ

end Stacks.LimitHomDescent
