module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.FibresInStabilizer
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.StabilizerRepresentable
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs

/-!
# The right stabiliser of functions is a subgroup

Let `G` be a geometrically irreducible group scheme over a field `k`, `U` a nonempty open of `G`
and `f ∈ Γ(G, U)`.  This file proves that the right stabiliser of `f`
(`AlgebraicGeometry.RightStabilises`) is a subgroup functor: it contains `1`, is stable under
inverses (directly, through the shearing automorphism) and under products, provided `U` is
affine and satisfies Perrin's content hypothesis (every zero divisor of every `Γ(U) ⊗[k] κ` is
nilpotent; automatic in characteristic zero by
`AlgebraicGeometry.zeroDivisorsNilpotent_tensor_of_isAffineOpen`).  Consequently a closed
subscheme representing the right stabiliser of a family of functions is a closed subgroup scheme
(`AlgebraicGeometry.exists_closedSubgroupScheme_of_rightStabilises`).

## Main results

* `AlgebraicGeometry.RightStabilises.inv` and `AlgebraicGeometry.RightStabilises.mul`.
* `AlgebraicGeometry.exists_closedSubgroupScheme_of_rightStabilises`: `V(K)` is a closed subgroup
  scheme when `K` represents a right stabiliser.

## Implementation notes

For `h, h'` stabilising `f`, on the open of `G ×_k T` where `x`, `x · h(t)` and `x · h(t) h'(t)`
all lie in `U` the translate of `f` by `h h'` equals `f`.  This open meets every fibre of
`G ×_k T ⟶ T` (the fibres are irreducible), so it is schematically dense in the stabiliser locus
of `h h'` by Perrin's content lemma (`AlgebraicGeometry.injective_res_of_forall_exists_mem`).

## References

* D. Perrin, *Schémas en groupes quasi-compacts sur un corps*, thèse, I §2 and IV §1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct

namespace AlgebraicGeometry

universe u

/-- Pulling back an equality of two pullbacks of a section along a morphism. -/
theorem Scheme.Hom.appLE_eq_appLE_of_comp {X Y Z : Scheme.{u}} (s : X ⟶ Y) {a c : Y ⟶ Z}
    {a' c' : X ⟶ Z} (ha : s ≫ a = a') (hc : s ≫ c = c') {U : Z.Opens} {O : Y.Opens}
    {O' : X.Opens} (ea : O ≤ a ⁻¹ᵁ U) (ec : O ≤ c ⁻¹ᵁ U) (e : O' ≤ s ⁻¹ᵁ O)
    (ea' : O' ≤ a' ⁻¹ᵁ U) (ec' : O' ≤ c' ⁻¹ᵁ U) (x : Γ(Z, U))
    (h : a.appLE U O ea x = c.appLE U O ec x) : a'.appLE U O' ea' x = c'.appLE U O' ec' x := by
  rw [← Scheme.Hom.appLE_appLE_of_comp_eq ha ea e ea',
    ← Scheme.Hom.appLE_appLE_of_comp_eq hc ec e ec', h]

/-- Restricting an equality of two pullbacks of a section to a smaller open. -/
theorem Scheme.Hom.appLE_eq_appLE_of_le {X Y : Scheme.{u}} {a c : X ⟶ Y} {U : Y.Opens}
    {O O' : X.Opens} (hO : O' ≤ O) (ea : O ≤ a ⁻¹ᵁ U) (ec : O ≤ c ⁻¹ᵁ U)
    (ea' : O' ≤ a ⁻¹ᵁ U) (ec' : O' ≤ c ⁻¹ᵁ U) (x : Γ(Y, U))
    (h : a.appLE U O ea x = c.appLE U O ec x) : a.appLE U O' ea' x = c.appLE U O' ec' x := by
  have := congrArg (X.presheaf.map (homOfLE hO).op).hom h
  simpa only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map] using this

variable {k : Type u} [Field k] {G T : Over (Spec (.of k))} [GrpObj G]

/-! ### Fibres of `G ×_k T ⟶ T` -/

/-- The fibre of `G ×_k T` over `t` meets `(rightTranslate g)⁻¹ U` for every nonempty `U`. -/
theorem exists_rightTranslate_mem_of_snd_eq (g : T ⟶ G) {U : G.left.Opens}
    (hne : (U : Set G.left).Nonempty) (t : T.left) :
    ∃ b ∈ (rightTranslate g).left ⁻¹ᵁ U, (snd G T).left b = t := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨a, ha₁, ha₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := T.hom)
    u t (Subsingleton.elim _ _)
  have hfa : (fst G T).left a = u := ha₁
  have hsa : (snd G T).left a = t := ha₂
  let b := (rightShear g).inv.left a
  have hb : (rightShear g).hom.left b = a := by
    change ((rightShear g).inv ≫ (rightShear g).hom).left a = a
    rw [Iso.inv_hom_id]
    rfl
  refine ⟨b, ?_, ?_⟩
  · change (rightTranslate g).left b ∈ U
    rw [← rightShear_hom_fst, Over.comp_left, Scheme.Hom.comp_apply, hb, hfa]
    exact hu
  · change ((rightShear g).inv ≫ snd G T).left a = t
    rw [rightShear_inv_snd, hsa]

omit [GrpObj G] in
/-- Over a geometrically irreducible `G`, two opens of `G ×_k T` which meet the fibre over `t`
meet it in a common point. -/
theorem exists_mem_inf_of_snd_eq [GeometricallyIrreducible G.hom] (t : T.left)
    {A B : (G ⊗ T).left.Opens} (hA : ∃ a ∈ A, (snd G T).left a = t)
    (hB : ∃ b ∈ B, (snd G T).left b = t) : ∃ w ∈ A ⊓ B, (snd G T).left w = t := by
  have hopen : IsOpenMap (pullback.snd G.hom T.hom).base :=
    (pullback.snd G.hom T.hom).isOpenMap
  have hirr := Scheme.Hom.isIrreducible_preimage (pullback.snd G.hom T.hom) hopen
    (isIrreducible_singleton (x := t))
  obtain ⟨a, haA, hat⟩ := hA
  obtain ⟨b, hbB, hbt⟩ := hB
  obtain ⟨w, hwt, hwA, hwB⟩ := hirr.2 _ _ A.isOpen B.isOpen ⟨a, hat, haA⟩ ⟨b, hbt, hbB⟩
  exact ⟨w, ⟨hwA, hwB⟩, hwt⟩

/-! ### The stabiliser is a subgroup -/

/-- Shearing by `h` and then translating by `h'` is translating by `h * h'`:
`(x · h(t)) · h'(t) = x · (h * h')(t)`. -/
theorem rightShear_hom_rightTranslate (h h' : T ⟶ G) :
    (rightShear h).hom ≫ rightTranslate h' = rightTranslate (h * h') := by
  simp [rightShear, rightTranslate, MonObj.comp_mul, mul_assoc]

/-- Right translation by `h⁻¹ * h` is the first projection `G ×_k T ⟶ G`. -/
theorem rightTranslate_inv_mul (h : T ⟶ G) : rightTranslate (h⁻¹ * h) = fst G T := by
  rw [inv_mul_cancel, rightTranslate_one]

/-- **The right stabiliser is stable under inverses.** -/
theorem RightStabilises.inv {h : T ⟶ G} {U : G.left.Opens} {f : Γ(G.left, U)}
    (hst : RightStabilises h U f) : RightStabilises h⁻¹ U f := by
  have hfst : (rightShear h⁻¹).hom.left ≫ (fst G T).left = (rightTranslate h⁻¹).left := by
    rw [← Over.comp_left, rightShear_hom_fst]
  have hρ : (rightShear h⁻¹).hom.left ≫ (rightTranslate h).left = (fst G T).left := by
    rw [← Over.comp_left, rightShear_hom_rightTranslate, rightTranslate_inv_mul]
  have e : rightStabilizerLocus h⁻¹ U ≤
      (rightShear h⁻¹).hom.left ⁻¹ᵁ rightStabilizerLocus h U := by
    intro x hx
    refine ⟨?_, ?_⟩
    · change ((rightShear h⁻¹).hom.left ≫ (fst G T).left) x ∈ U
      rw [hfst]
      exact hx.2
    · change ((rightShear h⁻¹).hom.left ≫ (rightTranslate h).left) x ∈ U
      rw [hρ]
      exact hx.1
  exact (Scheme.Hom.appLE_eq_appLE_of_comp _ hfst hρ _ _ e
    (rightStabilizerLocus_le_rightTranslate h⁻¹ U) (rightStabilizerLocus_le_fst h⁻¹ U) f
    hst).symm

/-- **The right stabiliser is stable under products** (Perrin, thesis I §2): if `h` and `h'`
right-stabilise `f`, so does `h * h'`, provided the open `U` is affine and satisfies Perrin's
content hypothesis (automatic in characteristic zero). -/
theorem RightStabilises.mul [GeometricallyIrreducible G.hom]
    {U : G.left.Opens} (hU : IsAffineOpen U)
    (hC : letI := sectionsAlgebra G.hom U
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, U) ⊗[k] κ) → IsNilpotent z)
    {h h' : T ⟶ G} (hne : (U : Set G.left).Nonempty) {f : Γ(G.left, U)}
    (hst : RightStabilises h U f) (hst' : RightStabilises h' U f) :
    RightStabilises (h * h') U f := by
  let L := rightStabilizerLocus (h * h') U
  let L' := L ⊓ (rightTranslate h).left ⁻¹ᵁ U
  have hL'L : L' ≤ L := inf_le_left
  have hL'fst : L' ≤ (fst G T).left ⁻¹ᵁ U := hL'L.trans (rightStabilizerLocus_le_fst _ U)
  have hL'ρ : L' ≤ (rightTranslate h).left ⁻¹ᵁ U := inf_le_right
  have hL'ρ' : L' ≤ (rightTranslate (h * h')).left ⁻¹ᵁ U :=
    hL'L.trans (rightStabilizerLocus_le_rightTranslate _ U)
  -- on `L'`: `f ∘ pr₁ = f ∘ ρ_h`
  have e₁ : (fst G T).left.appLE U L' hL'fst f = (rightTranslate h).left.appLE U L' hL'ρ f :=
    Scheme.Hom.appLE_eq_appLE_of_le (le_inf hL'fst hL'ρ) _ _ _ _ f hst
  -- on `L'`: `f ∘ ρ_h = f ∘ ρ_{h h'}`, pulling back the condition for `h'` along the shear
  have hfst : (rightShear h).hom.left ≫ (fst G T).left = (rightTranslate h).left := by
    rw [← Over.comp_left, rightShear_hom_fst]
  have hρ : (rightShear h).hom.left ≫ (rightTranslate h').left =
      (rightTranslate (h * h')).left := by
    rw [← Over.comp_left, rightShear_hom_rightTranslate]
  have e : L' ≤ (rightShear h).hom.left ⁻¹ᵁ rightStabilizerLocus h' U := by
    intro x hx
    refine ⟨?_, ?_⟩
    · change ((rightShear h).hom.left ≫ (fst G T).left) x ∈ U
      rw [hfst]
      exact hL'ρ hx
    · change ((rightShear h).hom.left ≫ (rightTranslate h').left) x ∈ U
      rw [hρ]
      exact hL'ρ' hx
  have e₂ : (rightTranslate h).left.appLE U L' hL'ρ f =
      (rightTranslate (h * h')).left.appLE U L' hL'ρ' f :=
    Scheme.Hom.appLE_eq_appLE_of_comp _ hfst hρ _ _ e _ _ f hst'
  -- `L'` meets every fibre over `T`, hence is schematically dense in `L`
  have hfib : ∀ t : T.left, ∃ a ∈ L', (snd G T).left a = t := by
    intro t
    obtain ⟨a, ha⟩ := (surjective_rightStabilizerLocus (h * h') hne).surj t
    exact exists_mem_inf_of_snd_eq t ⟨_, a.2, ha⟩ (exists_rightTranslate_mem_of_snd_eq h hne t)
  refine injective_res_of_forall_exists_mem hU hC hL'L (rightStabilizerLocus_le_fst _ U) hfib ?_
  simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  exact e₁.trans e₂

/-- A family of functions stabilised by `h` and `h'` is stabilised by `h * h'`. -/
theorem rightStabilises_mul_of_forall [GeometricallyIrreducible G.hom]
    {U : G.left.Opens} (hU : IsAffineOpen U)
    (hC : letI := sectionsAlgebra G.hom U
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.left, U) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.left, U) ⊗[k] κ) → IsNilpotent z)
    {h h' : T ⟶ G} (hne : (U : Set G.left).Nonempty) {n : Type*}
    {f : n → Γ(G.left, U)} (hst : ∀ i, RightStabilises h U (f i))
    (hst' : ∀ i, RightStabilises h' U (f i)) : ∀ i, RightStabilises (h * h') U (f i) :=
  fun i ↦ (hst i).mul hU hC hne (hst' i)

/-- **A closed subscheme representing a right stabiliser is a closed subgroup scheme.**  Let `G`
be a geometrically irreducible group scheme over a field `k`, `U` a nonempty affine open
satisfying Perrin's content hypothesis (automatic in characteristic zero), `f` a family
of functions on `U`, and `K` an ideal sheaf on `G` such that a `T`-point `h` right-stabilises
every `f i` if and only if `K ≤ ker h`.  Then the closed subscheme `V(K)` is (the carrier of) a
closed subgroup scheme of `G`. -/
theorem exists_closedSubgroupScheme_of_rightStabilises (G : Grp (Over (Spec (.of k))))
    [GeometricallyIrreducible G.X.hom]
    {U : G.X.left.Opens} (hU : IsAffineOpen U)
    (hC : letI := sectionsAlgebra G.X.hom U
      ∀ (κ : Type u) [Field κ] [Algebra k κ] (z : Γ(G.X.left, U) ⊗[k] κ),
        z ∉ nonZeroDivisors (Γ(G.X.left, U) ⊗[k] κ) → IsNilpotent z)
    (hne : (U : Set G.X.left).Nonempty) {n : Type*}
    (f : n → Γ(G.X.left, U)) (K : G.X.left.IdealSheafData)
    (hK : ∀ (T : Over (Spec (.of k))) (h : T ⟶ G.X),
      (∀ i, RightStabilises h U (f i)) ↔ K ≤ h.left.ker) :
    ∃ H : ClosedSubgroupScheme G,
      ∃ e : Over.mk (K.subschemeι ≫ G.X.hom) ≅ H.carrier.X,
        Over.homMk K.subschemeι = e.hom ≫ H.ι.hom.hom := by
  let Z : Over (Spec (.of k)) := Over.mk (K.subschemeι ≫ G.X.hom)
  let j : Z ⟶ G.X := Over.homMk K.subschemeι rfl
  have : IsClosedImmersion j.left := by
    change IsClosedImmersion K.subschemeι
    infer_instance
  have hj : ∀ i, RightStabilises j U (f i) := by
    refine (hK Z j).mpr ?_
    change K ≤ K.subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
  have hlift : ∀ {Y : Over (Spec (.of k))} (g : Y ⟶ G.X), (∀ i, RightStabilises g U (f i)) →
      ∃ g' : Y ⟶ Z, g' ≫ j = g := by
    intro Y g hg
    have hle : K.subschemeι.ker ≤ g.left.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact (hK Y g).mp hg
    refine ⟨Over.homMk (IsClosedImmersion.lift K.subschemeι g.left hle) ?_, ?_⟩
    · change IsClosedImmersion.lift K.subschemeι g.left hle ≫ K.subschemeι ≫ G.X.hom = Y.hom
      rw [IsClosedImmersion.lift_fac_assoc]
      exact Over.w g
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  have hmul : (j ⊗ₘ j) ≫ μ[G.X] = (fst Z Z ≫ j) * (snd Z Z ≫ j) := by
    rw [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
  exact (isClosedSubgroupScheme_iff_factor G j).2
    ⟨hlift η[G.X] fun i ↦ by
        rw [MonObj.one_eq_one]
        exact rightStabilises_one U (f i),
      hlift ((j ⊗ₘ j) ≫ μ[G.X]) (by
        rw [hmul]
        exact rightStabilises_mul_of_forall hU hC hne (fun i ↦ (hj i).comp _)
          (fun i ↦ (hj i).comp _)),
      hlift (j ≫ ι[G.X]) (by
        rw [← CategoryTheory.Hom.inv_def]
        exact fun i ↦ (hj i).inv)⟩

end AlgebraicGeometry

end
