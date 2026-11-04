module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.CoefficientMap
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackReduction
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.GlobalSmulPullbackUnit

/-!
# Naturality of the difference of lifts along a morphism of split thickenings

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` and `h₂ : T ⟶ T'₂` split
first order thickenings with retractions `r`, `r₂`, and `g : T'₂ ⟶ T'` a morphism under `T`
compatible with the retractions, `r₂ = g ≫ r`. Pulling back lifts along `g` corresponds, under the
identifications `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference` of the lifts
with `Ext¹(𝒢, 𝒢 ⊗ f_T^*𝒥)`, to composition with the map of coefficients induced by `g`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningCoefficientMap`). This is the functoriality
of `T_x(M) = Ext¹(𝒢, 𝒢 ⊗ M)` in `M` in the proofs of Stacks 08W8 and Stacks 08WA (Stacks 0CYE for
the deformations of modules).

## Main results

* `Stacks.Homology.extConj_extClass_naturality`: naturality of the class of an extension read
  through isomorphisms of its outer terms.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 0CYE](https://stacks.math.columbia.edu/tag/0CYE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian

universe e u

namespace Stacks.Homology

universe w v₁ v₂ v₃ u₁ u₂ u₃

/-- **The class of an extension, read through isomorphisms of its outer terms, is natural**: for a
morphism `φ : S ⟶ S'` of short exact sequences inducing `α'⁻¹ ∘ α` on the third terms and
`β' ∘ κ ∘ β⁻¹`, read backwards, on the first, the class of `S'` read through `α'`, `β'` is the
class of `S` read through `α`, `β` followed by `κ`. -/
theorem extConj_extClass_naturality {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') {X K K' : C}
    (α : X ≅ S.X₃) (α' : X ≅ S'.X₃) (β : S.X₁ ≅ K) (β' : S'.X₁ ≅ K') (κ : K ⟶ K')
    (h₁ : φ.τ₁ = β.hom ≫ κ ≫ β'.inv) (h₃ : φ.τ₃ = α.inv ≫ α'.hom) :
    extConj α'.hom β'.hom hS'.extClass =
      (extConj α.hom β.hom hS.extClass).comp (Abelian.Ext.mk₀ κ) (add_zero 1) := by
  have hn := hS.extClass_naturality hS' φ
  rw [h₁, h₃] at hn
  have hn' := congrArg (fun x => (Abelian.Ext.mk₀ α.hom).comp (x.comp (Abelian.Ext.mk₀ β'.hom)
    (add_zero 1)) (zero_add 1)) hn
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] at hn'
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id_assoc] at hn'
  simp only [extConj, Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  exact hn'.symm


/-- **A split short exact sequence has class zero**: if the cokernel map `S.g` has a section `s`,
then the class of `S` is zero. -/
theorem extClass_eq_zero_of_comp_g_eq_id {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) :
    hS.extClass = 0 := by
  have h := congrArg (fun x => (Abelian.Ext.mk₀ s).comp x (zero_add 1)) hS.comp_extClass
  simp only [Abelian.Ext.comp_zero] at h
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, hs, Abelian.Ext.mk₀_id_comp] at h
  exact h

/-- **The class of an extension read through exact functors and isomorphisms, along a morphism of
extensions.** Let `R₁ : C₁ ⥤ X`, `R₂ : C₂ ⥤ X` be exact, `P : C₂ ⥤ C₁` with `c : P ⋙ R₁ ≅ R₂`,
and `τ : S₁ ⟶ P(S₂)` a morphism of short complexes from a short exact `S₁` to the image of a
short exact `S₂`. If `R₁(τ₃)` is `α₁⁻¹ ≫ α₂` and `R₁(τ₁)` is `β₁ ≫ κ ≫ β₂⁻¹` (through `c`), the
class of `S₂` read through `R₂`, `α₂`, `β₂` is the class of `S₁` read through `R₁`, `α₁`, `β₁`
followed by `κ`. -/
theorem extConj_mapExactFunctor_extClass_naturality {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] {X : Type u₃} [Category.{v₃} X] [Abelian X]
    [HasExt.{w} C₁] [HasExt.{w} C₂] [HasExt.{w} X]
    (R₁ : C₁ ⥤ X) [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    (R₂ : C₂ ⥤ X) [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (P : C₂ ⥤ C₁) (c : P ⋙ R₁ ≅ R₂) {S₁ : ShortComplex C₁} {S₂ : ShortComplex C₂}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (τ₁ : S₁.X₁ ⟶ P.obj S₂.X₁)
    (τ₂ : S₁.X₂ ⟶ P.obj S₂.X₂) (τ₃ : S₁.X₃ ⟶ P.obj S₂.X₃) (comm₁₂ : S₁.f ≫ τ₂ = τ₁ ≫ P.map S₂.f)
    (comm₂₃ : S₁.g ≫ τ₃ = τ₂ ≫ P.map S₂.g) {Y K₁ K₂ : X} (α₁ : Y ≅ R₁.obj S₁.X₃)
    (α₂ : Y ≅ R₂.obj S₂.X₃) (β₁ : R₁.obj S₁.X₁ ≅ K₁) (β₂ : R₂.obj S₂.X₁ ≅ K₂) (κ : K₁ ⟶ K₂)
    (h₁ : R₁.map τ₁ ≫ c.hom.app S₂.X₁ = β₁.hom ≫ κ ≫ β₂.inv)
    (h₃ : R₁.map τ₃ ≫ c.hom.app S₂.X₃ = α₁.inv ≫ α₂.hom) :
    extConj α₂.hom β₂.hom ((hS₂.extClass).mapExactFunctor R₂) =
      (extConj α₁.hom β₁.hom ((hS₁.extClass).mapExactFunctor R₁)).comp (Abelian.Ext.mk₀ κ)
        (add_zero 1) := by
  rw [Abelian.Ext.mapExactFunctor_extClass, Abelian.Ext.mapExactFunctor_extClass]
  let φ : S₁.map R₁ ⟶ S₂.map R₂ :=
    { τ₁ := R₁.map τ₁ ≫ c.hom.app S₂.X₁
      τ₂ := R₁.map τ₂ ≫ c.hom.app S₂.X₂
      τ₃ := R₁.map τ₃ ≫ c.hom.app S₂.X₃
      comm₁₂ := by
        dsimp
        rw [← Category.assoc, ← R₁.map_comp, comm₁₂, R₁.map_comp, Category.assoc,
          Category.assoc]
        exact congrArg (R₁.map τ₁ ≫ ·) (c.hom.naturality S₂.f).symm
      comm₂₃ := by
        dsimp
        rw [← Category.assoc, ← R₁.map_comp, comm₂₃, R₁.map_comp, Category.assoc,
          Category.assoc]
        exact congrArg (R₁.map τ₂ ≫ ·) (c.hom.naturality S₂.g).symm }
  exact extConj_extClass_naturality (hS₁.map_of_exact R₁) (hS₂.map_of_exact R₂) φ α₁ α₂ β₁ β₂ κ
    h₁ h₃

end Stacks.Homology

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}

end AlgebraicGeometry.Space.CoherentSituation

end
