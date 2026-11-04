module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalCupStatements

/-!
# The two claims of the diagonal argument from their cup product forms

Through [Stacks, Tag 0G8C] on ambient classes
(`Stacks.DeRham.CohomologicalGysin.gysinCohomologyMap_formRestriction`), the Gysin maps of the
diagonal `Δ`, of `j = (σ ∘ f, id)` and of `j' = (id, σ ∘ f)` on a class `θ` of `X` are, up to the
common sign `(-1)^{n·n}`, the cup products of the ambient copy of `θ` with the Gysin classes
`η = γ_Δ(1)`, `γ_j(1) = p₁^*ξ` and `γ_{j'}(1) = p₂^*ξ`. So the diagonal claim is the identity
`(★)` and top-degree injectivity is the injectivity of `x ↦ p₂^*x ∪ p₁^*ξ`.

## Main results

* `Stacks.WeilDeRham.diagonalClaim_of_starIdentity`.
* `Stacks.WeilDeRham.topInjective_of_cupTopInjective`.
* `Stacks.WeilDeRham.cupOnProduct_fstPullback_diagonalClass`: `p₁^*θ ∪ η = p₂^*θ ∪ η`, both being
  the Gysin map of the diagonal at `θ` up to the same sign.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Gysin Stacks.DeRham.GysinCohomologyBaseChange
open AlgebraicGeometry.Scheme.Hom Stacks.DeRham.CohomologicalGysin
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ConormalEquations
open Stacks.DeRham.GysinCupHodge
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.WeilDeRham

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
  (e : ℕ) [SmoothOfRelativeDimension (e + 1) f]

/-- The ambient copy along a retraction, applied to a class: the pullback followed by the
restriction of forms. -/
theorem ambientCopy_apply {W S : Scheme.{u}} (g : X ⟶ S) (πW : W ⟶ S) (i : X ⟶ W) (G : W ⟶ X)
    (wG : G ≫ g = πW ≫ 𝟙 S) (p q : ℕ)
    (θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ q (relativeDifferentialForms g (p : ℤ))) :
    (ambientCopy g πW i G wG p q).hom θ =
      ((Hfunctor (structureSheafRing W.toRingedSpace) ⊤ q).map
        (formRestriction i πW (p : ℤ))).hom
        ((pullbackHgroup (CohomologyPullbackComparison.canonical G.toLRSHom.toShHom) 0 (q : ℤ) q
          (by simp) (formsBaseChangeHom G g πW (𝟙 S) wG (p : ℤ))).hom θ) :=
  rfl

/-- [Stacks, Tag 0G8C] on the ambient classes of `W = Y ×_B Y`, for any Koszul-regular closed
immersion `i` of conormal rank `n` into `W` whose Gysin class is `c`. -/
private theorem shift_formsGysinMap_formRestriction {B : Type u} [CommRing B] {Y Z : Scheme.{u}}
    (g : Y ⟶ Spec (.of B)) [IsProper g] [Smooth (prodStructure g)] (n : ℕ)
    (i : Z ⟶ pullback g g) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (hK : IsKoszulRegularImmersion i) (hE : ConormalRank i n) (p : ℕ)
    (α : Hgroup (structureSheafRing (pullback g g).toRingedSpace) ⊤ n
      (relativeDifferentialForms (prodStructure g) (p : ℤ)))
    (c : Hgroup (structureSheafRing (pullback g g).toRingedSpace) ⊤ (0 + n)
      (relativeDifferentialForms (prodStructure g) (((0 : ℕ) : ℤ) + (n : ℤ))))
    (hc : c = gysinUnitClass i (prodStructure g) hK hE) :
    (hgroupModuleShiftIso (X := (pullback g g).toRingedSpace)
        (relativeDifferentialForms (prodStructure g) ((p : ℤ) + (n : ℤ))) 0 (n + n)
        ((n : ℤ) + (n : ℤ)) (by push_cast; ring)).hom
      ((formsGysinMap i (prodStructure g) hK hE p n).hom
        (((Hfunctor (structureSheafRing (pullback g g).toRingedSpace) ⊤ n).map
          (formRestrictionModules i (prodStructure g) (p : ℤ))).hom α)) =
    (((n : ℤ)) * ((n : ℤ))).negOnePow • cupOnProduct g p n n α c := by
  rw [hc]
  exact gysinCohomologyMap_formRestriction i (prodStructure g) hK hE p n α

/-- **The Gysin map of the diagonal through [Stacks, Tag 0G8C]**: on `θ ∈ Hⁿ(X, Ω^e)`, read
through `hgroupModuleShiftIso`, it is `(-1)^{n·n}` times `p₁^*θ ∪ η`. -/
theorem shift_diagonalGysin (θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
      (relativeDifferentialForms f (e : ℤ))) :
    (hgroupModuleShiftIso (X := (pullback f f).toRingedSpace)
        (relativeDifferentialForms (prodStructure f) ((e : ℤ) + ((e + 1 : ℕ) : ℤ))) 0
        ((e + 1) + (e + 1)) (((e + 1 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)) (by push_cast; ring)).hom
      ((diagonalGysin f (e + 1) e (e + 1)).hom θ) =
    ((((e + 1 : ℕ) : ℤ)) * (((e + 1 : ℕ) : ℤ))).negOnePow •
      cupOnProduct f e (e + 1) (e + 1) ((fstPullback f e (e + 1)).hom θ) (diagonalClass f e) := by
  have := smooth_prodStructure f (e + 1)
  exact shift_formsGysinMap_formRestriction f (e + 1) (pullback.diagonal f)
    (diagonal_koszul_and_conormalRank f (e + 1)).1 (diagonal_koszul_and_conormalRank f (e + 1)).2
    e _ _ rfl

variable (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ f = 𝟙 _) [IsClosedImmersion σ]
  [LocallyOfFinitePresentation σ] [Smooth (σ ≫ f)] [FormallyUnramified (σ ≫ f)]

/-- **The Gysin map of `j' = (id, σ ∘ f)` through [Stacks, Tag 0G8C]**: on `θ ∈ Hⁿ(X, Ω^e)` it is
`(-1)^{n·n}` times `p₁^*θ ∪ p₂^*ξ`, since `γ_{j'}(1) = p₂^*ξ`. -/
theorem shift_sectionSndGysin (θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
      (relativeDifferentialForms f (e : ℤ))) :
    (hgroupModuleShiftIso (X := (pullback f f).toRingedSpace)
        (relativeDifferentialForms (prodStructure f) ((e : ℤ) + ((e + 1 : ℕ) : ℤ))) 0
        ((e + 1) + (e + 1)) (((e + 1 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)) (by push_cast; ring)).hom
      ((sectionSndGysin f (e + 1) σ hσ e (e + 1)).hom θ) =
    ((((e + 1 : ℕ) : ℤ)) * (((e + 1 : ℕ) : ℤ))).negOnePow •
      cupOnProduct f e (e + 1) (e + 1) ((fstPullback f e (e + 1)).hom θ)
        (sndSectionClass f e σ) := by
  have := smooth_prodStructure f (e + 1)
  exact shift_formsGysinMap_formRestriction f (e + 1) (sectionSnd f σ hσ)
    (sectionSnd_koszul_and_conormalRank f (e + 1) σ hσ).1
    (sectionSnd_koszul_and_conormalRank f (e + 1) σ hσ).2 e _ _
    (pullbackHgroup_sectionGysinClass_snd f (e + 1) σ hσ)

/-- **The Gysin map of `j = (σ ∘ f, id)` through [Stacks, Tag 0G8C]**: on `θ ∈ Hⁿ(X, Ωᵖ)` it is
`(-1)^{n·n}` times `p₂^*θ ∪ p₁^*ξ`, since `γ_j(1) = p₁^*ξ`. -/
theorem shift_sectionFstGysin (p : ℕ) (θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤ (e + 1)
      (relativeDifferentialForms f (p : ℤ))) :
    (hgroupModuleShiftIso (X := (pullback f f).toRingedSpace)
        (relativeDifferentialForms (prodStructure f) ((p : ℤ) + ((e + 1 : ℕ) : ℤ))) 0
        ((e + 1) + (e + 1)) (((e + 1 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)) (by push_cast; ring)).hom
      ((sectionFstGysin f (e + 1) σ hσ p (e + 1)).hom θ) =
    ((((e + 1 : ℕ) : ℤ)) * (((e + 1 : ℕ) : ℤ))).negOnePow •
      cupOnProduct f p (e + 1) (e + 1) ((sndPullback f p (e + 1)).hom θ)
        (fstSectionClass f e σ) := by
  have := smooth_prodStructure f (e + 1)
  exact shift_formsGysinMap_formRestriction f (e + 1) (sectionFst f σ hσ)
    (sectionFst_koszul_and_conormalRank f (e + 1) σ hσ).1
    (sectionFst_koszul_and_conormalRank f (e + 1) σ hσ).2 p _ _
    (pullbackHgroup_sectionGysinClass_fst f (e + 1) σ hσ)

/-- Cancelling a unit and an injective additive map, at variables. -/
private lemma eq_of_shift_eq {M T : Type*} [AddCommGroup M] [AddCommGroup T] (φ : M →+ T)
    (hφ : Function.Injective φ) (s : ℤˣ) {x y z : M} {a b c : T} (hx : φ x = s • a)
    (hy : φ y = s • b) (hz : φ z = s • c) (habc : a = b + c) : x = y + z := by
  refine hφ ?_
  rw [map_add, hx, hy, hz, habc, smul_add]

/-- **The diagonal claim from the identity `(★)`.** -/
theorem diagonalClaim_of_starIdentity (h : StarIdentity f e σ) : DiagonalClaim f e σ hσ := by
  intro θ
  refine eq_of_shift_eq (hgroupModuleShiftIso (X := (pullback f f).toRingedSpace)
      (relativeDifferentialForms (prodStructure f) ((e : ℤ) + ((e + 1 : ℕ) : ℤ))) 0
      ((e + 1) + (e + 1)) (((e + 1 : ℕ) : ℤ) + ((e + 1 : ℕ) : ℤ)) (by push_cast; ring)).hom.hom
    (ConcreteCategory.bijective_of_isIso _).1 _ (shift_diagonalGysin f e θ)
    (shift_sectionSndGysin f e σ hσ θ) (shift_sectionFstGysin f e σ hσ e θ) (h θ)

/-- **Top-degree injectivity from its cup form.** -/
theorem topInjective_of_cupTopInjective (h : CupTopInjective f e σ) : TopInjective f e σ hσ := by
  intro x hx
  refine h x ?_
  have hs := shift_sectionFstGysin f e σ hσ (e + 1) x
  rw [hx, map_zero] at hs
  exact (smul_eq_zero_iff_eq _).mp hs.symm

/-- **`p₁^*θ ∪ η = p₂^*θ ∪ η`**: by [Stacks, Tag 0G8C] both are `(-1)^{n·n}` times the Gysin map
of the diagonal at the ambient copy of `θ`, which does not depend on the retraction `p₁` or `p₂`
of the diagonal (`formRestriction_comp_retraction_eq`). -/
theorem cupOnProduct_fstPullback_diagonalClass (θ : Hgroup (structureSheafRing X.toRingedSpace) ⊤
      (e + 1) (relativeDifferentialForms f (e : ℤ))) :
    cupOnProduct f e (e + 1) (e + 1) ((fstPullback f e (e + 1)).hom θ) (diagonalClass f e) =
      cupOnProduct f e (e + 1) (e + 1) ((sndPullback f e (e + 1)).hom θ) (diagonalClass f e) := by
  have := smooth_prodStructure f (e + 1)
  have key := shift_formsGysinMap_formRestriction f (e + 1) (pullback.diagonal f)
    (diagonal_koszul_and_conormalRank f (e + 1)).1 (diagonal_koszul_and_conormalRank f (e + 1)).2 e
  have hr := congrArg (fun φ => φ.hom θ)
    (formRestriction_comp_retraction_eq (pullback.diagonal f) (prodStructure f) f
      (pullback.fst f f) (fst_comp_eq_prodStructure f) (pullback.diagonal_fst f)
      (by rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]) (pullback.snd f f)
      (snd_comp_eq_prodStructure f) (pullback.diagonal_snd f) 0 ((e + 1 : ℕ) : ℤ) (e + 1) (by simp)
      e)
  have h : _ = _ := (key ((fstPullback f e (e + 1)).hom θ) _ rfl).symm.trans
    (Eq.trans ?_ (key ((sndPullback f e (e + 1)).hom θ) _ rfl))
  · exact MulAction.injective _ h
  · congr 2

end Stacks.WeilDeRham

end
