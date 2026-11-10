module

public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp

namespace Stacks.Blowup.C1573
end Stacks.Blowup.C1573

/-!
# The strict transform along a blowup centred off an open

Let `b : Z' ⟶ Z` be the blowup of `Z` in a quasi-coherent ideal `K` whose support is the
complement of an open `D ⊆ Z`, and let `g : P ⟶ Z` be a morphism. Over `D` the blowup is an
isomorphism, so it has a section `σ : D ⟶ Z'`. If `w₀ : W ⟶ P` is an open immersion onto `g⁻¹D`,
the lift `w : W ⟶ P ×_Z Z'` of `w₀` and `σ` is an isomorphism onto the complement of the inverse
image of the exceptional divisor. Consequently its kernel ideal sheaf is the ideal of the strict
transform of `P` (Stacks 080D): the strict transform is the scheme-theoretic image of `W`.

## Main definitions

* `Stacks.Blowup.C1573.sectionOver`: the section `σ : D ⟶ Z'` of the blowup over the complement of
  its centre.
* `Stacks.Blowup.C1573.liftOver`: the lift `w : W ⟶ P ×_Z Z'`.

## Main results

* `Stacks.Blowup.C1573.ker_liftOver`: the kernel ideal sheaf of the lift is the ideal of the strict
  transform.

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Blowup

open _root_.Stacks.Blowup.C1573
variable {Z : Scheme.{u}} (D : Z.Opens) (K : Z.IdealSheafData)
  (hK : K.supportSet = (D : Set Z)ᶜ)

/-- Points of `W` map into `U` under `w₀ ≫ g` when `w₀` has range `g⁻¹U`. -/
private theorem comp_mem_of_range_eq {X Y T : Scheme.{u}} (U : X.Opens) (g : Y ⟶ X) (w₀ : T ⟶ Y)
    (hw₀ : Set.range w₀.base = (g ⁻¹ᵁ U : Set Y)) (t : T) : g.base (w₀.base t) ∈ U := by
  have : w₀.base t ∈ (g ⁻¹ᵁ U : Set Y) := hw₀ ▸ ⟨t, rfl⟩
  exact this

/-- A morphism whose image lies in an open `U` has image contained in the range of `U.ι`. -/
private theorem range_subset_range_ι_of_forall_mem {X T : Scheme.{u}} (U : X.Opens) (f : T ⟶ X)
    (h : ∀ t, f.base t ∈ U) : Set.range f.base ⊆ Set.range U.ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨t, rfl⟩
  exact h t

include hK in
/-- The blowup is an isomorphism over the complement `D` of the support of its centre. -/
theorem C1573.isIso_blowUpToBase_restrict : IsIso (blowUpToBase K ∣_ D) :=
  isIso_blowUpToBase_restrict_of_subset_compl_support K D fun z hz hzK => by
    have : z ∈ K.supportSet := hzK
    rw [hK] at this
    exact this hz

/-- The section of the blowup over the complement of its centre. -/
def C1573.sectionOver : D.toScheme ⟶ blowUp K :=
  haveI := isIso_blowUpToBase_restrict D K hK
  inv (blowUpToBase K ∣_ D) ≫ (blowUpToBase K ⁻¹ᵁ D).ι

/-- The section over `D` composed with the blowup is the inclusion of `D`. -/
@[reassoc]
theorem C1573.sectionOver_comp : sectionOver D K hK ≫ blowUpToBase K = D.ι := by
  have := isIso_blowUpToBase_restrict D K hK
  rw [sectionOver, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]

/-- A morphism to the blowup landing over `D` factors through the section over `D`. -/
theorem C1573.eq_comp_sectionOver {T : Scheme.{u}} (x : T ⟶ blowUp K) (y : T ⟶ D.toScheme)
    (hxy : x ≫ blowUpToBase K = y ≫ D.ι) : x = y ≫ sectionOver D K hK := by
  have := isIso_blowUpToBase_restrict D K hK
  have hr : Set.range x.base ⊆ Set.range (blowUpToBase K ⁻¹ᵁ D).ι.base :=
    range_subset_range_ι_of_forall_mem _ x fun t => by
      change (x ≫ blowUpToBase K).base t ∈ D
      rw [hxy]
      exact (y.base t).2
  set x' := IsOpenImmersion.lift (blowUpToBase K ⁻¹ᵁ D).ι x hr
  have hx' : x' ≫ (blowUpToBase K ⁻¹ᵁ D).ι = x := IsOpenImmersion.lift_fac _ _ _
  have hy : x' ≫ (blowUpToBase K ∣_ D) = y := by
    rw [← cancel_mono D.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hx', hxy]
  rw [sectionOver, ← hy, Category.assoc, IsIso.hom_inv_id_assoc, hx']

include hK in
/-- The complement of the inverse image of the exceptional divisor is the inverse image of
`D`. -/
theorem C1573.mem_exceptionalComplement_iff {P : Scheme.{u}} (g : P ⟶ Z)
    (q : Stacks.StrictTransform.baseChange g (blowUpToBase K)) :
    q ∈ Stacks.StrictTransform.exceptionalComplement g (blowUpToBase K) (exceptionalIdeal K) ↔
      g.base ((pullback.fst g (blowUpToBase K)).base q) ∈ D := by
  change (pullback.snd g (blowUpToBase K)).base q ∉ (K.comap (blowUpToBase K)).support ↔ _
  rw [Scheme.IdealSheafData.support_comap]
  change (blowUpToBase K).base ((pullback.snd g (blowUpToBase K)).base q) ∉ K.supportSet ↔ _
  rw [hK, Set.notMem_compl_iff, ← Scheme.Hom.comp_apply, ← pullback.condition,
    Scheme.Hom.comp_apply]
  rfl

variable {P W : Scheme.{u}} (g : P ⟶ Z) (w₀ : W ⟶ P)
  (hw₀ : Set.range w₀.base = (g ⁻¹ᵁ D : Set P))

include hw₀ in
/-- The image of `w₀ ≫ g` is contained in `D`. -/
theorem C1573.range_comp_subset : Set.range (w₀ ≫ g).base ⊆ Set.range D.ι.base :=
  range_subset_range_ι_of_forall_mem _ _ (comp_mem_of_range_eq D g w₀ hw₀)

/-- The morphism `W ⟶ D` induced by `w₀`. -/
def C1573.toOpen : W ⟶ D.toScheme :=
  IsOpenImmersion.lift D.ι (w₀ ≫ g) (range_comp_subset D g w₀ hw₀)

/-- The lift `W ⟶ P ×_Z Z'` of `w₀` and of the section of the blowup over `D`. -/
def C1573.liftOver : W ⟶ pullback g (blowUpToBase K) :=
  pullback.lift w₀ (toOpen D g w₀ hw₀ ≫ sectionOver D K hK)
    (by rw [Category.assoc, sectionOver_comp, toOpen, IsOpenImmersion.lift_fac])

/-- **The kernel ideal sheaf of the lift is the ideal of the strict transform**, when `w₀` is an
open immersion onto `g⁻¹D`. -/
theorem C1573.ker_liftOver [IsOpenImmersion w₀] :
    (liftOver D K hK g w₀ hw₀).ker =
      Stacks.StrictTransform.ideal g (blowUpToBase K) (exceptionalIdeal K) := by
  rw [Stacks.StrictTransform.ideal_eq_ker_ι]
  set O := Stacks.StrictTransform.exceptionalComplement g (blowUpToBase K) (exceptionalIdeal K)
  set w := liftOver D K hK g w₀ hw₀
  have hwf : w ≫ pullback.fst g (blowUpToBase K) = w₀ := pullback.lift_fst _ _ _
  have hwO : Set.range w.base ⊆ Set.range O.ι.base :=
    range_subset_range_ι_of_forall_mem _ _ fun t => by
      rw [mem_exceptionalComplement_iff D K hK g]
      have h2 : (pullback.fst g (blowUpToBase K)).base (w.base t) = w₀.base t := by
        rw [← Scheme.Hom.comp_apply, hwf]
      rw [h2]
      exact comp_mem_of_range_eq D g w₀ hw₀ t
  set w' := IsOpenImmersion.lift O.ι w hwO
  have hw' : w' ≫ O.ι = w := IsOpenImmersion.lift_fac _ _ _
  have hOr : Set.range (O.ι ≫ pullback.fst g (blowUpToBase K)).base ⊆ Set.range w₀.base := by
    rw [hw₀]
    rintro _ ⟨o, rfl⟩
    exact (mem_exceptionalComplement_iff D K hK g (O.ι.base o)).1 o.2
  set r := IsOpenImmersion.lift w₀ (O.ι ≫ pullback.fst g (blowUpToBase K)) hOr
  have hr : r ≫ w₀ = O.ι ≫ pullback.fst g (blowUpToBase K) := IsOpenImmersion.lift_fac _ _ _
  have hrw : r ≫ w = O.ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, hwf, hr]
    · have h1 : O.ι ≫ pullback.snd g (blowUpToBase K) =
          (r ≫ toOpen D g w₀ hw₀) ≫ sectionOver D K hK := by
        refine eq_comp_sectionOver D K hK _ _ ?_
        rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← hr, Category.assoc,
          Category.assoc, toOpen, IsOpenImmersion.lift_fac]
      rw [h1, Category.assoc]
      simp only [w, liftOver, pullback.lift_snd, Category.assoc]
  have e1 : w' ≫ r = 𝟙 W := by
    rw [← cancel_mono w₀, Category.assoc, hr, ← Category.assoc, hw', hwf,
      Category.id_comp]
  have e2 : r ≫ w' = 𝟙 O.toScheme := by
    rw [← cancel_mono O.ι, Category.assoc, hw', hrw, Category.id_comp]
  have : IsIso w' := ⟨r, e1, e2⟩
  rw [← hw', Scheme.Hom.ker_comp_of_isIso]

end Stacks.Blowup

end
