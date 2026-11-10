module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentability
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsLocalizing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherenceOnAChaoticSite
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftUniversalArrow
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# Quasi-coherent objects on a chaotic site along a ring transport

Let `e : C ≌ D` be an equivalence of categories, regarded as chaotic sites, and let
`T : RingTransport e O O'` be a ring transport from a presheaf of rings `O` on `C` to a presheaf
of rings `O'` on `D` (ring isomorphisms `O'(Y) ≃+* O(e⁻¹ Y)`, natural in `Y`, the two
presheaves of rings possibly in different universes). The induced equivalence of presheaves of
modules is exact, so it descends to an equivalence of derived categories `D(O) ≌ D(O')`. This file
shows that this equivalence restricts to the subcategories of quasi-coherent objects of
Stacks 0GYV (`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.QC`): an object `K` of `D(O)`
has invertible base-change comparisons along every arrow exactly when its transport does.

The point is the compatibility of the derived transport with the canonical derived restriction
maps (`restrictionMap_dFunctor`): the derived sections of the transport of `K` over `Y` are the
derived sections of `K` over `e⁻¹ Y`, read through `O'(Y) ≃+* O(e⁻¹ Y)`, and under this
identification the restriction maps of the transport are those of `K`. Invertibility of the
comparison along an arrow is the universality of the derived restriction map
(`CategoryTheory.Functor.isUniversalArrow_iff_isIso`), and universal arrows are transported along
equivalences (`CategoryTheory.Functor.IsUniversalArrow.of_equivalence`). The converse is the
same statement for the opposite ring transport.

## Main definitions

* `Stacks.UniverseLift.RingTransport.dFunctorCompRGamma`: the derived sections of the derived
  transport.
* `Stacks.UniverseLift.RingTransport.dRestrictSquare`: the square of derived restrictions of
  scalars attached to an arrow of `Dᵒᵖ`.
* `Stacks.UniverseLift.RingTransport.qcEquivalence`: **the equivalence `QC(O) ≌ QC(O')`.**
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData.toMax`: a base-change
  datum at the parameter `w`, read at the parameter `max u v r w`, with
  `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData.qcToMaxEquivalence`.

## Main results

* `Stacks.UniverseLift.RingTransport.restrictionMap_dFunctor`: the compatibility of the derived
  transport with the canonical derived restriction maps.
* `Stacks.UniverseLift.RingTransport.isQC_functor_mapDerivedCategory_obj_iff`: an object is
  quasi-coherent exactly when its transport is.

## Implementation notes

The module universe of both derived categories is `max u v r u' v' r' t`, the smallest one
containing both sites and both ring universes; the derived categories are
`DMod.{max u' v' r' t} O` and `DMod.{max u v r t} O'`, which name that universe. The base-change
data on the two sides are arbitrary: quasi-coherence does not depend on them
(`Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.isQC_iff_of_baseChangeData`).

Every instance stated at the module universe of the derived categories would leave its universe
parameter `t` undetermined by the goal, so instance search would stall on a universe constraint
of the form `max … t … =?= max … ?t`; the exactness and equivalence facts needed are therefore
supplied by name at the point of use.

## References

* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.DerivedCategoryComparisons (mapDerivedCategoryCompIso mapDerivedCategoryIsoOfNatIso)

universe w t u v r u' v' r'


namespace Stacks.UniverseLift

section Bookkeeping

universe s₁ t₁

variable {𝔼 : Type t₁} [Category.{s₁} 𝔼]

/-- The bookkeeping behind the compatibility of the derived transport with the canonical
derived restriction maps (`Stacks.UniverseLift.RingTransport.restrictionMap_dFunctor_Q`): each
hypothesis is one of the canonical factorizations or naturality squares met in the chase, and
the four cancelling pairs are inverse factorizations. Stating it over an abstract category is
what lets `exact` supply the definitionally equal spellings of the objects involved. -/
theorem restrictionMap_chase
    {x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ y₁ y₂ y₅ z₀ z₁ : 𝔼}
    {L₁ : x₀ ⟶ x₁} {a : x₀ ⟶ x₂} {m' : x₂ ⟶ x₃} {p : x₁ ⟶ x₃}
    {A : x₂ ⟶ x₄} {q' : x₄ ⟶ x₅} {B : x₅ ⟶ x₆} {c : x₆ ⟶ x₃} {c' : x₃ ⟶ x₆}
    {σU : x₁ ⟶ x₇} {d : x₆ ⟶ x₈} {k : x₈ ⟶ x₇} {β₀ : x₇ ⟶ z₀} {β₁ : x₈ ⟶ z₁} {n : z₁ ⟶ z₀}
    {d' : x₈ ⟶ x₆} {B' : x₆ ⟶ x₅} {s : x₅ ⟶ x₉} {G : x₉ ⟶ y₅} {h : y₅ ⟶ z₁}
    {σV : x₀ ⟶ y₁} {G₂ : x₄ ⟶ y₂} {i : y₂ ⟶ y₁} {i' : y₁ ⟶ y₂} {ΨrM : y₁ ⟶ z₀}
    {Ψres : y₂ ⟶ y₅} {qρ : x₄ ⟶ x₉}
    (h₁ : a ≫ m' = L₁ ≫ p)
    (h₂ : m' = A ≫ q' ≫ B ≫ c)
    (h₃ : σU = p ≫ c' ≫ d ≫ k)
    (h₄ : k ≫ β₀ = β₁ ≫ n)
    (h₅ : β₁ = d' ≫ B' ≫ s ≫ G ≫ h)
    (h₆ : σV = a ≫ A ≫ G₂ ≫ i)
    (h₇ : ΨrM = i' ≫ Ψres ≫ h ≫ n)
    (h₈ : G₂ ≫ Ψres = qρ ≫ G)
    (h₉ : q' ≫ s = qρ)
    (hc : c ≫ c' = 𝟙 _) (hd : d ≫ d' = 𝟙 _) (hB : B ≫ B' = 𝟙 _) (hi : i ≫ i' = 𝟙 _) :
    L₁ ≫ σU ≫ β₀ = σV ≫ ΨrM := by
  subst h₃ h₆ h₇
  have e₁ : L₁ ≫ p ≫ c' ≫ d ≫ k ≫ β₀ = a ≫ A ≫ q' ≫ s ≫ G ≫ h ≫ n := by
    rw [h₄, h₅, ← Category.assoc L₁ p, ← h₁, h₂]
    simp only [Category.assoc]
    rw [reassoc_of% hc, reassoc_of% hd, reassoc_of% hB]
  simp only [Category.assoc]
  rw [e₁, reassoc_of% hi, reassoc_of% h₈, ← reassoc_of% h₉]

/-- Cancelling a pair of mutually inverse morphisms in the middle of a composite. Stating it over
an abstract category is what lets `exact` supply definitionally equal spellings of the objects
involved. -/
theorem comp_cancel_mid {w x y y' z₁ z₂ : 𝔼} (a : w ⟶ x) (b : x ⟶ y) (c : y ⟶ y') (c' : y' ⟶ y)
    (d : y ⟶ z₁) (f : z₁ ⟶ z₂) (h : c ≫ c' = 𝟙 y) :
    (a ≫ b ≫ c) ≫ c' ≫ d ≫ f = a ≫ b ≫ d ≫ f := by
  simp only [Category.assoc]
  rw [reassoc_of% h]

/-- Cancelling two pairs of mutually inverse morphisms inside a composite. -/
theorem comp_cancel_two {x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : 𝔼} (a : x₀ ⟶ x₁) (b : x₁ ⟶ x₂)
    (i : x₂ ⟶ x₃) (i' : x₃ ⟶ x₂) (c : x₂ ⟶ x₄) (j : x₄ ⟶ x₅) (j' : x₅ ⟶ x₄) (d : x₄ ⟶ x₆)
    (f : x₆ ⟶ x₇) (hi : i ≫ i' = 𝟙 x₂) (hj : j ≫ j' = 𝟙 x₄) :
    a ≫ b ≫ i ≫ i' ≫ c ≫ j ≫ j' ≫ d ≫ f = a ≫ b ≫ c ≫ d ≫ f := by
  rw [reassoc_of% hi, reassoc_of% hj]

/-- A functor applied to a composite of four morphisms. -/
theorem map_comp_four {𝔸 : Type*} [Category 𝔸] (G : 𝔸 ⥤ 𝔼) {a₀ a₁ a₂ a₃ a₄ : 𝔸}
    (f₁ : a₀ ⟶ a₁) (f₂ : a₁ ⟶ a₂) (f₃ : a₂ ⟶ a₃) (f₄ : a₃ ⟶ a₄) :
    G.map (f₁ ≫ f₂ ≫ f₃ ≫ f₄) = G.map f₁ ≫ G.map f₂ ≫ G.map f₃ ≫ G.map f₄ := by
  simp

end Bookkeeping

end Stacks.UniverseLift

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-- A derived base-change datum at the parameter `w`, read at the parameter `max u v r w`: the
module universe of both is `max u v r w`, so the fields are the same. This is how a datum such as
`AlgebraicGeometry.Stack.affineBaseChangeData` is fed to a statement whose base-change data are
indexed by the module universe itself. -/
def toMax (bc : BaseChangeData.{w} O) : BaseChangeData.{max u v r w} O where
  baseChange := bc.baseChange
  baseChangeAdj := bc.baseChangeAdj
  baseChangeComp := bc.baseChangeComp

/-- Reading a base-change datum at the module universe does not change the cartesian
condition. -/
theorem isQC_toMax_iff (bc : BaseChangeData.{w} O) (K : DMod.{w} O) :
    IsQC.{max u v r w} bc.toMax K ↔ IsQC.{w} bc K :=
  Iff.rfl

/-- Reading a base-change datum at the module universe does not change the category of
quasi-coherent objects. -/
noncomputable def qcToMaxEquivalence (bc : BaseChangeData.{w} O) :
    QC.{w} bc ≌ QC.{max u v r w} bc.toMax :=
  CategoryTheory.Equivalence.refl

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData

namespace Stacks.UniverseLift.RingTransport

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {e : C ≌ D}
  {O : Cᵒᵖ ⥤ RingCat.{r}} {O' : Dᵒᵖ ⥤ RingCat.{r'}} (T : RingTransport e O O')

/-- Derived sections of the derived transport over `Y` are derived sections over `e⁻¹ Y`, read
through the ring isomorphism `O'(Y) ≃+* O(e⁻¹ Y)`. -/
noncomputable def dFunctorCompRGamma (Y : Dᵒᵖ) :
    (T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _).mapDerivedCategory ⋙
        RGamma.{max u v r u' v' r' t} O' Y ≅
      RGamma.{max u v r u' v' r' t} O (e.inverse.op.obj Y) ⋙
        (T.modEquiv.{max u v r u' v' r' t} Y).functor.mapDerivedCategory :=
  (mapDerivedCategoryCompIso (T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _)
    (PresheafOfModules.evaluation.{max u v r u' v' r' t} O' Y)).symm ≪≫
  mapDerivedCategoryCompIso (PresheafOfModules.evaluation.{max u v r u' v' r' t} O
    (e.inverse.op.obj Y)) (T.modEquiv.{max u v r u' v' r' t} Y).functor

/-- The comparison `dFunctorCompRGamma` evaluated at the image of a cochain complex: the
canonical factorizations of the transport, of evaluation at `Y` over `D`, of restriction of
scalars along `O'(Y) ≃+* O(e⁻¹ Y)` and of evaluation at `e⁻¹ Y` over `C`. -/
theorem dFunctorCompRGamma_hom_app_Q (Y : Dᵒᵖ)
    (P : CochainComplex (PresheafOfModules.{max u v r u' v' r' t} O) ℤ) :
    letI : HasDerivedCategory.{max u v r u' v' r' t}
        (PresheafOfModules.{max u v r u' v' r' t} O) :=
      derivedPresheafCategory.{max u v r u' v' r' t} O
    letI : HasDerivedCategory.{max u v r u' v' r' t}
        (PresheafOfModules.{max u v r u' v' r' t} O') :=
      derivedPresheafCategory.{max u v r u' v' r' t} O'
    (T.dFunctorCompRGamma.{t} Y).hom.app (DerivedCategory.Q.obj P) =
      (RGamma.{max u v r u' v' r' t} O' Y).map
          ((T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤
            _).mapDerivedCategoryFactors.hom.app P) ≫
        (PresheafOfModules.evaluation.{max u v r u' v' r' t} O' Y).mapDerivedCategoryFactors.hom.app
          (((T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (T.modEquiv.{max u v r u' v' r' t} Y).functor.mapDerivedCategoryFactors.inv.app
          (((PresheafOfModules.evaluation.{max u v r u' v' r' t} O
            (e.inverse.op.obj Y)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (T.modEquiv.{max u v r u' v' r' t} Y).functor.mapDerivedCategory.map
          ((PresheafOfModules.evaluation.{max u v r u' v' r' t} O
            (e.inverse.op.obj Y)).mapDerivedCategoryFactors.inv.app P) := by
  let _ : HasDerivedCategory.{max u v r u' v' r' t}
      (PresheafOfModules.{max u v r u' v' r' t} O) :=
    derivedPresheafCategory.{max u v r u' v' r' t} O
  let _ : HasDerivedCategory.{max u v r u' v' r' t}
      (PresheafOfModules.{max u v r u' v' r' t} O') :=
    derivedPresheafCategory.{max u v r u' v' r' t} O'
  let F := (T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _)
  let ev' := PresheafOfModules.evaluation.{max u v r u' v' r' t} O' Y
  let ev := PresheafOfModules.evaluation.{max u v r u' v' r' t} O (e.inverse.op.obj Y)
  let ρ := (T.modEquiv.{max u v r u' v' r' t} Y).functor
  change (mapDerivedCategoryCompIso F ev').inv.app (DerivedCategory.Q.obj P) ≫
    (mapDerivedCategoryCompIso ev ρ).hom.app (DerivedCategory.Q.obj P) = _
  rw [Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q]
  exact comp_cancel_mid _ _ _ _ _ _ (Iso.inv_hom_id_app (F ⋙ ev').mapDerivedCategoryFactors P)

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- The square of derived restrictions of scalars attached to `a' : V' ⟶ U'` in `Dᵒᵖ`, the
descent of `restrictScalarsSquare`. -/
noncomputable def dRestrictSquare {U' V' : Dᵒᵖ} (a' : V' ⟶ U') :
    (T.modEquiv.{max u v r u' v' r' t} U').functor.mapDerivedCategory ⋙
        DRestrict.{max u v r u' v' r' t} O' a' ≅
      DRestrict.{max u v r u' v' r' t} O (e.inverse.op.map a') ⋙
        (T.modEquiv.{max u v r u' v' r' t} V').functor.mapDerivedCategory :=
  letI := rsPreservesFiniteLimits.{max u v r u' v' r' t} O' a'
  letI := rsPreservesFiniteColimits.{max u v r u' v' r' t} O' a'
  letI := rsPreservesFiniteLimits.{max u v r u' v' r' t} O (e.inverse.op.map a')
  letI := rsPreservesFiniteColimits.{max u v r u' v' r' t} O (e.inverse.op.map a')
  (mapDerivedCategoryCompIso (T.modEquiv.{max u v r u' v' r' t} U').functor
      (ModuleCat.restrictScalars.{max u v r u' v' r' t} (O'.map a').hom)).symm ≪≫
    mapDerivedCategoryIsoOfNatIso _ _ (T.restrictScalarsSquare.{max u v r u' v' r' t} a') ≪≫
    mapDerivedCategoryCompIso
      (ModuleCat.restrictScalars.{max u v r u' v' r' t} (O.map (e.inverse.op.map a')).hom)
      (T.modEquiv.{max u v r u' v' r' t} V').functor

/-- The square `dRestrictSquare` evaluated at the image of a cochain complex: the canonical
factorizations of the two transports and of the two restrictions of scalars. -/
private theorem dRestrictSquare_hom_app_Q {U' V' : Dᵒᵖ} (a' : V' ⟶ U')
    (Y : CochainComplex (ModuleCat.{max u v r u' v' r' t} (O.obj (e.inverse.op.obj U'))) ℤ) :
    letI := rsPreservesFiniteLimits.{max u v r u' v' r' t} O' a'
    letI := rsPreservesFiniteColimits.{max u v r u' v' r' t} O' a'
    letI := rsPreservesFiniteLimits.{max u v r u' v' r' t} O (e.inverse.op.map a')
    letI := rsPreservesFiniteColimits.{max u v r u' v' r' t} O (e.inverse.op.map a')
    (T.dRestrictSquare.{t} a').hom.app (DerivedCategory.Q.obj Y) =
      (ModuleCat.restrictScalars.{max u v r u' v' r' t} (O'.map a').hom).mapDerivedCategory.map
          ((T.modEquiv.{max u v r u' v' r' t} U').functor.mapDerivedCategoryFactors.hom.app Y) ≫
        (ModuleCat.restrictScalars.{max u v r u' v' r' t}
          (O'.map a').hom).mapDerivedCategoryFactors.hom.app
          (((T.modEquiv.{max u v r u' v' r' t} U').functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Y) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (T.restrictScalarsSquare.{max u v r u' v' r' t} a') (ComplexShape.up ℤ)).hom.app Y) ≫
        (T.modEquiv.{max u v r u' v' r' t} V').functor.mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{max u v r u' v' r' t}
            (O.map (e.inverse.op.map a')).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
        (T.modEquiv.{max u v r u' v' r' t} V').functor.mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{max u v r u' v' r' t}
            (O.map (e.inverse.op.map a')).hom).mapDerivedCategoryFactors.inv.app Y) := by
  let := rsPreservesFiniteLimits.{max u v r u' v' r' t} O' a'
  let := rsPreservesFiniteColimits.{max u v r u' v' r' t} O' a'
  let := rsPreservesFiniteLimits.{max u v r u' v' r' t} O (e.inverse.op.map a')
  let := rsPreservesFiniteColimits.{max u v r u' v' r' t} O (e.inverse.op.map a')
  let ρV := (T.modEquiv.{max u v r u' v' r' t} V').functor
  let ρU := (T.modEquiv.{max u v r u' v' r' t} U').functor
  let rs' := ModuleCat.restrictScalars.{max u v r u' v' r' t} (O'.map a').hom
  let rs := ModuleCat.restrictScalars.{max u v r u' v' r' t} (O.map (e.inverse.op.map a')).hom
  change (mapDerivedCategoryCompIso ρU rs').inv.app (DerivedCategory.Q.obj Y) ≫
    (mapDerivedCategoryIsoOfNatIso _ _
      (T.restrictScalarsSquare.{max u v r u' v' r' t} a')).hom.app
      (DerivedCategory.Q.obj Y) ≫
    (mapDerivedCategoryCompIso rs ρV).hom.app (DerivedCategory.Q.obj Y) = _
  rw [Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q]
  simp only [Category.assoc]
  exact comp_cancel_two _ _ _ _ _ _ _ _ _ (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _)

/-- **The derived transport is compatible with the canonical derived restriction maps**, on the
image of a cochain complex. -/
theorem restrictionMap_dFunctor_Q {U' V' : Dᵒᵖ} (a' : V' ⟶ U')
    (P : CochainComplex (PresheafOfModules.{max u v r u' v' r' t} O) ℤ) :
    restrictionMap.{max u v r u' v' r' t} O' a'
        ((T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _).mapDerivedCategory.obj
          (DerivedCategory.Q.obj P)) ≫
      (DRestrict.{max u v r u' v' r' t} O' a').map
        ((T.dFunctorCompRGamma.{t} U').hom.app (DerivedCategory.Q.obj P)) ≫
      (T.dRestrictSquare.{t} a').hom.app
        ((RGamma.{max u v r u' v' r' t} O (e.inverse.op.obj U')).obj (DerivedCategory.Q.obj P)) =
    (T.dFunctorCompRGamma.{t} V').hom.app (DerivedCategory.Q.obj P) ≫
      (T.modEquiv.{max u v r u' v' r' t} V').functor.mapDerivedCategory.map
        (restrictionMap.{max u v r u' v' r' t} O (e.inverse.op.map a')
          (DerivedCategory.Q.obj P)) := by
  let _ : HasDerivedCategory.{max u v r u' v' r' t}
      (PresheafOfModules.{max u v r u' v' r' t} O) :=
    derivedPresheafCategory.{max u v r u' v' r' t} O
  let _ : HasDerivedCategory.{max u v r u' v' r' t}
      (PresheafOfModules.{max u v r u' v' r' t} O') :=
    derivedPresheafCategory.{max u v r u' v' r' t} O'
  let := rsPreservesFiniteLimits.{max u v r u' v' r' t} O' a'
  let := rsPreservesFiniteColimits.{max u v r u' v' r' t} O' a'
  let := rsPreservesFiniteLimits.{max u v r u' v' r' t} O (e.inverse.op.map a')
  let := rsPreservesFiniteColimits.{max u v r u' v' r' t} O (e.inverse.op.map a')
  let F := (T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _)
  let evU' := PresheafOfModules.evaluation.{max u v r u' v' r' t} O' U'
  let evV := PresheafOfModules.evaluation.{max u v r u' v' r' t} O (e.inverse.op.obj V')
  let evU := PresheafOfModules.evaluation.{max u v r u' v' r' t} O (e.inverse.op.obj U')
  let ρV := (T.modEquiv.{max u v r u' v' r' t} V').functor
  let ρU := (T.modEquiv.{max u v r u' v' r' t} U').functor
  let rs := ModuleCat.restrictScalars.{max u v r u' v' r' t} (O.map (e.inverse.op.map a')).hom
  let Y := (evU.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let FP := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  -- the restriction map of the transport, moved to the image of the transported complex
  have h₁ := (restrictionNatTrans.{max u v r u' v' r' t} O' a').naturality
    (F.mapDerivedCategoryFactors.hom.app P)
  rw [restrictionNatTrans_app, restrictionNatTrans_app] at h₁
  simp only [Functor.comp_obj, Functor.comp_map] at h₁
  -- the comparison of the derived restriction squares, on the image of a complex
  have h₅ := T.dRestrictSquare_hom_app_Q.{t} a' Y
  have h₃ : (DRestrict.{max u v r u' v' r' t} O' a').map
      ((T.dFunctorCompRGamma.{t} U').hom.app (DerivedCategory.Q.obj P)) =
      (DRestrict.{max u v r u' v' r' t} O' a').map
          ((RGamma.{max u v r u' v' r' t} O' U').map (F.mapDerivedCategoryFactors.hom.app P)) ≫
        (DRestrict.{max u v r u' v' r' t} O' a').map (evU'.mapDerivedCategoryFactors.hom.app FP) ≫
        (DRestrict.{max u v r u' v' r' t} O' a').map (ρU.mapDerivedCategoryFactors.inv.app Y) ≫
        (DRestrict.{max u v r u' v' r' t} O' a').map
          (ρU.mapDerivedCategory.map (evU.mapDerivedCategoryFactors.inv.app P)) := by
    rw [T.dFunctorCompRGamma_hom_app_Q.{t} U' P]
    exact map_comp_four _ _ _ _ _
  have h₄ := (T.dRestrictSquare.{t} a').hom.naturality (evU.mapDerivedCategoryFactors.inv.app P)
  simp only [Functor.comp_map] at h₄
  have h₇ : ρV.mapDerivedCategory.map
      (restrictionMap.{max u v r u' v' r' t} O (e.inverse.op.map a') (DerivedCategory.Q.obj P)) =
      ρV.mapDerivedCategory.map (evV.mapDerivedCategoryFactors.hom.app P) ≫
        ρV.mapDerivedCategory.map (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (PresheafOfModules.restriction O (e.inverse.op.map a')) (ComplexShape.up ℤ)).app P)) ≫
        ρV.mapDerivedCategory.map (rs.mapDerivedCategoryFactors.inv.app Y) ≫
        ρV.mapDerivedCategory.map
          ((DRestrict.{max u v r u' v' r' t} O (e.inverse.op.map a')).map
            (evU.mapDerivedCategoryFactors.inv.app P)) := by
    rw [restrictionMap_Q]
    exact map_comp_four _ _ _ _ _
  have h₈ := (ρV.mapDerivedCategoryFactors.inv.naturality ((NatTrans.mapHomologicalComplex
    (PresheafOfModules.restriction O (e.inverse.op.map a')) (ComplexShape.up ℤ)).app P)).symm
  simp only [Functor.comp_map] at h₈
  have h₉ : DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (PresheafOfModules.restriction O' a') (ComplexShape.up ℤ)).app FP) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (T.restrictScalarsSquare.{max u v r u' v' r' t} a') (ComplexShape.up ℤ)).hom.app Y) =
      DerivedCategory.Q.map ((ρV.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O (e.inverse.op.map a'))
          (ComplexShape.up ℤ)).app P)) := by
    refine (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map ?_)
    ext n x
    rfl
  have h₂ := restrictionMap_Q.{max u v r u' v' r' t} O' a' FP
  have h₆ := T.dFunctorCompRGamma_hom_app_Q.{t} V' P
  exact restrictionMap_chase h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
    ((DRestrict.{max u v r u' v' r' t} O' a').mapIso
      (evU'.mapDerivedCategoryFactors.app FP)).inv_hom_id
    ((DRestrict.{max u v r u' v' r' t} O' a').mapIso
      (ρU.mapDerivedCategoryFactors.app Y)).inv_hom_id
    (Iso.inv_hom_id_app _ _)
    (ρV.mapDerivedCategory.mapIso (evV.mapDerivedCategoryFactors.app P)).inv_hom_id

/-- **The derived transport is compatible with the canonical derived restriction maps.** For
`a' : V' ⟶ U'` in `Dᵒᵖ` and `K` in `D(O)`, the derived restriction map of the transport of `K`
along `a'` is, through the computation `dFunctorCompRGamma` of its derived sections and the
square `dRestrictSquare`, the derived restriction map of `K` along `e⁻¹(a')`, read through the
ring isomorphisms. -/
theorem restrictionMap_dFunctor {U' V' : Dᵒᵖ} (a' : V' ⟶ U') (K : DMod.{max u' v' r' t} O) :
    restrictionMap.{max u v r t} O' a'
        ((T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _).mapDerivedCategory.obj K) ≫
      (DRestrict.{max u v r t} O' a').map ((T.dFunctorCompRGamma.{t} U').hom.app K) ≫
      (T.dRestrictSquare.{t} a').hom.app
        ((RGamma.{max u' v' r' t} O (e.inverse.op.obj U')).obj K) =
    (T.dFunctorCompRGamma.{t} V').hom.app K ≫
      (T.modEquiv.{max u v r u' v' r' t} V').functor.mapDerivedCategory.map
        (restrictionMap.{max u' v' r' t} O (e.inverse.op.map a') K) := by
  let _ : HasDerivedCategory.{max u v r u' v' r' t} (PresheafOfModules.{max u v r u' v' r' t} O) :=
    derivedPresheafCategory.{max u v r u' v' r' t} O
  let _ : HasDerivedCategory.{max u v r u' v' r' t} (PresheafOfModules.{max u v r u' v' r' t} O') :=
    derivedPresheafCategory.{max u v r u' v' r' t} O'
  let F := (T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _)
  have key : Functor.whiskerLeft F.mapDerivedCategory
        (restrictionNatTrans.{max u v r u' v' r' t} O' a') ≫
      Functor.whiskerRight (T.dFunctorCompRGamma.{t} U').hom
        (DRestrict.{max u v r u' v' r' t} O' a') ≫
      Functor.whiskerLeft (RGamma.{max u v r u' v' r' t} O (e.inverse.op.obj U'))
        (T.dRestrictSquare.{t} a').hom =
    (T.dFunctorCompRGamma.{t} V').hom ≫
      Functor.whiskerRight (restrictionNatTrans.{max u v r u' v' r' t} O (e.inverse.op.map a'))
        (T.modEquiv.{max u v r u' v' r' t} V').functor.mapDerivedCategory :=
    Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (PresheafOfModules.{max u v r u' v' r' t} O) (ComplexShape.up ℤ))
      fun P ↦ T.restrictionMap_dFunctor_Q.{t} a' P
  exact congr_app key K

/-- The derived restriction of scalars along a ring isomorphism `O'(Y) ≃+* O(e⁻¹ Y)` is an
equivalence of derived categories. This is not an instance: its universe parameter `t` is not
determined by the functor, whose module universe is `max u v r u' v' r' t`. -/
theorem isEquivalence_modEquiv_mapDerivedCategory (Y : Dᵒᵖ) :
    (T.modEquiv.{max u v r u' v' r' t} Y).functor.mapDerivedCategory.IsEquivalence :=
  (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence
    (T.modEquiv.{max u v r u' v' r' t} Y)).isEquivalence_functor

variable (bc : BaseChangeData.{max u' v' r' t} O) (bc' : BaseChangeData.{max u v r t} O')

/-- **The derived transport carries quasi-coherent objects to quasi-coherent objects.** If `K` in
`D(O)` is quasi-coherent in the sense of Stacks 0GYV (for every arrow its canonical base-change
comparison is invertible), then so is its transport in `D(O')`: the comparison along `a'` is
identified, by `restrictionMap_dFunctor`, with the comparison of `K` along `e⁻¹(a')` read through
the ring isomorphisms, and invertibility of a comparison is the universality of the restriction
map, which equivalences preserve. -/
theorem isQC_functor_mapDerivedCategory_obj (K : DMod.{max u' v' r' t} O)
    (hK : IsQC.{max u' v' r' t} bc K) :
    IsQC.{max u v r t} bc'
      ((T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _).mapDerivedCategory.obj K) := by
  intro U' V' a'
  have hK' := (Functor.isUniversalArrow_iff_isIso (bc.baseChangeAdj (e.inverse.op.map a'))
    (restrictionMap.{max u' v' r' t} O (e.inverse.op.map a') K)).2 (hK _)
  refine (Functor.isUniversalArrow_iff_isIso (bc'.baseChangeAdj a') _).1 ?_
  have := T.isEquivalence_modEquiv_mapDerivedCategory.{t} U'
  have := T.isEquivalence_modEquiv_mapDerivedCategory.{t} V'
  exact Functor.IsUniversalArrow.of_equivalence (T.dRestrictSquare.{t} a')
    ((T.dFunctorCompRGamma.{t} V').app K) ((T.dFunctorCompRGamma.{t} U').app K)
    (T.restrictionMap_dFunctor.{t} a' K) hK'

/-- **Quasi-coherence is invariant under the derived transport.** An object `K` of `D(O)` is
quasi-coherent exactly when its transport to `D(O')` is: one direction is
`isQC_functor_mapDerivedCategory_obj`, the other is the same statement for the opposite ring
transport, applied to the transport of `K`, which comes back to `K` up to isomorphism. -/
theorem isQC_functor_mapDerivedCategory_obj_iff (K : DMod.{max u' v' r' t} O) :
    IsQC.{max u v r t} bc'
        ((T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _).mapDerivedCategory.obj K) ↔
      IsQC.{max u' v' r' t} bc K := by
  refine ⟨fun h ↦ ?_, T.isQC_functor_mapDerivedCategory_obj.{t} bc bc' K⟩
  let _ : HasDerivedCategory.{max u v r u' v' r' t} (PresheafOfModules.{max u v r u' v' r' t} O) :=
    derivedPresheafCategory.{max u' v' r' t} O
  let _ : HasDerivedCategory.{max u v r u' v' r' t} (PresheafOfModules.{max u v r u' v' r' t} O') :=
    derivedPresheafCategory.{max u v r t} O'
  let E := Dualizing.mapDerivedCategoryEquivalenceOfEquivalence
    (T.equivalence : PresheafOfModules.{max u v r u' v' r' t} O ≌
      PresheafOfModules.{max u v r u' v' r' t} O')
  exact @ObjectProperty.prop_of_iso _ _ (IsQC.{max u' v' r' t} bc) _ _ _ (E.unitIso.app K).symm
    (T.symm.isQC_functor_mapDerivedCategory_obj.{t} bc' bc _ (by exact h))

/-- **The equivalence of the categories of quasi-coherent objects induced by a ring transport.**
For a ring transport `T` along an equivalence `e : C ≌ D` of categories regarded as chaotic sites,
the derived transport `D(O) ≌ D(O')` restricts to an equivalence `QC(O) ≌ QC(O')` of the full
subcategories of the objects satisfying the cartesian condition of Stacks 0GYV, whatever
derived base-change data are used on the two sides. -/
noncomputable def qcEquivalence : QC.{max u' v' r' t} bc ≌ QC.{max u v r t} bc' :=
  let _ : HasDerivedCategory.{max u v r u' v' r' t} (PresheafOfModules.{max u v r u' v' r' t} O) :=
    derivedPresheafCategory.{max u' v' r' t} O
  let _ : HasDerivedCategory.{max u v r u' v' r' t} (PresheafOfModules.{max u v r u' v' r' t} O') :=
    derivedPresheafCategory.{max u v r t} O'
  (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence
    (T.equivalence : PresheafOfModules.{max u v r u' v' r' t} O ≌
      PresheafOfModules.{max u v r u' v' r' t} O')).congrFullSubcategory
    (by
      ext K
      exact T.isQC_functor_mapDerivedCategory_obj_iff.{t} bc bc' K)

/-- The functor of `qcEquivalence` is the derived transport. -/
lemma qcEquivalence_functor_obj_obj (K : QC.{max u' v' r' t} bc) :
    ((T.qcEquivalence.{t} bc bc').functor.obj K).obj =
      (T.functor : PresheafOfModules.{max u v r u' v' r' t} O ⥤ _).mapDerivedCategory.obj K.obj :=
  rfl

end Stacks.UniverseLift.RingTransport
