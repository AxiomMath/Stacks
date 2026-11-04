module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens

/-!
# The comparison functor is an equivalence on every affine scheme

Let `X` be a scheme. The comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of
[Stacks, Tag 06VT] is the derived functor of the exact inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)`,
factored through the complexes with quasi-coherent cohomology. [Stacks, Tag 06Z0] asserts that
`i_X` is an equivalence when `X` is affine. For `X = Spec R` on the nose, and at the locally small
model of both derived categories, this is
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence`. The conclusion holds for an
*arbitrary* affine scheme and at an *arbitrary* choice of the two derived categories.

Both generalisations come from one transport statement. An isomorphism of schemes `e : X ≅ Y`
restricts `𝒪_Y`-modules to `𝒪_X`-modules and back, giving an equivalence `Mod(𝒪_X) ≌ Mod(𝒪_Y)`
which is exact and carries quasi-coherent modules to quasi-coherent modules in both directions.
It therefore restricts to `QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` and induces equivalences of the two derived
categories which again preserve quasi-coherence of cohomology in both directions, hence restrict
to `D_QCoh(𝒪_X) ≌ D_QCoh(𝒪_Y)`. Composing `i_X` with the inclusion of `D_QCoh` recovers the
derived functor of `ι`, so the four equivalences fit into a square
`i_X ∘ (restriction on QCoh) ≅ (restriction on D_QCoh) ∘ i_Y` after composing with the fully
faithful inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)`; a functor isomorphic to a composite of equivalences
with an equivalence on the right is an equivalence. Nothing in that argument constrains the models
of the derived categories, so the two sides may be read at different ones, and taking `e` to be
the identity isomorphism gives the comparison of two models of a single scheme.

For an affine `X` the isomorphism to transport along is `X.isoSpec : X ≅ Spec Γ(X, ⊤)`.

## Main results

* `Stacks.DerivedQCoh.isEquivalence_derivedQuasicoherentComparison_of_schemeIso` — the comparison
  functor of [Stacks, Tag 06VT] is an equivalence for `X` as soon as it is one for a scheme
  isomorphic to `X`, with the two sides read at independently chosen derived categories.
* `Stacks.DerivedQCoh.isEquivalence_derivedQuasicoherentComparison_of_model` — whether the
  comparison functor is an equivalence does not depend on the chosen models of `D(𝒪_X)` and
  `D(QCoh(𝒪_X))`.
* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isAffine_atModel` —
  **[Stacks, Tag 06Z0]**: the comparison functor is an equivalence for every affine scheme, at
  every model of the two derived categories.

## Implementation notes

**The two models and the explicit instance arguments.** `HasDerivedCategory.{w} C` is a *chosen*
localization of `CochainComplex C ℤ` at the quasi-isomorphisms, so two instances of it for the
same `C` give two categories `DerivedCategory C` and a statement about one says nothing about the
other. The comparison functor of
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/WeakSerre/DerivedComparison.lean` accordingly leaves
both derived categories as instance arguments, and the statements here do the same. In
`Stacks.DerivedQCoh.isEquivalence_derivedQuasicoherentComparison_of_model` two instances of each
class for the same category are in scope at once, so instance resolution cannot be used to pick
between them: the four choices are plain explicit arguments and the comparison functor is applied
with `@`. In the other two statements the models are genuine instance arguments, and the universe
levels `w` of the hypothesis and of the conclusion are distinct universe variables, which is what
keeps the globally available locally small instances
`AlgebraicGeometry.SheafOfModules.hasDerivedCategory` and
`Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent` from competing with the binders.

**Crossing `AlgebraicGeometry.Scheme.Modules` and `AlgebraicGeometry.SheafOfModules`.** The
comparison functor is stated over `SheafOfModules X.ringCatSheaf`, since that is the spelling of
`SheafOfModules.isQuasicoherent`, whereas Mathlib's restriction of modules along a morphism of
schemes is stated over `AlgebraicGeometry.Scheme.Modules`. The two are definitionally equal but
carry separately declared `Category`, `Preadditive` and `Abelian` instances, so instance search
does not cross between them. `Stacks.DerivedQCoh.restrictSheaves` and the exactness, additivity,
quasi-coherence and coherence statements beside it are `AlgebraicGeometry.Scheme.Modules`'
restriction API read once at the first spelling by term-level ascription, which is checked at
default transparency; everything after that stays on one side of the barrier.

**Why `Stacks.DerivedQCoh.liftEquivalence` is needed rather than only `ObjectProperty.lift`.** The
restriction equivalences have to be cut down twice: once from `Mod(𝒪_X)` to `QCoh(𝒪_X)` and once
from `D(𝒪_X)` to `D_QCoh(𝒪_X)`. Both cuts are the same formal step — an equivalence preserving a
pair of object properties in both directions restricts to their full subcategories, the unit and
counit being transported along the fully faithful inclusions — so it is recorded once, with no
additive or abelian structure involved.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe w w' v₁ v₂ u₁ u₂ u

namespace Stacks.DerivedQCoh

/-! ### Restricting an equivalence to a pair of full subcategories -/

/-- An equivalence `E : A ≌ B` carrying an object property `P` of `A` into an object property `Q`
of `B` and carrying `Q` back into `P` restricts to an equivalence `P.FullSubcategory ≌
Q.FullSubcategory`.

The two functors are the liftings of `P.ι ⋙ E.functor` and `Q.ι ⋙ E.inverse`, and the unit and
counit are those of `E` read through the fully faithful inclusions of the subcategories. -/
private def liftEquivalence {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (E : A ≌ B) (P : ObjectProperty A) (Q : ObjectProperty B)
    (hF : ∀ M, P M → Q (E.functor.obj M)) (hG : ∀ N, Q N → P (E.inverse.obj N)) :
    P.FullSubcategory ≌ Q.FullSubcategory :=
  CategoryTheory.Equivalence.mk (Q.lift (P.ι ⋙ E.functor) fun M => hF M.obj M.property)
    (P.lift (Q.ι ⋙ E.inverse) fun N => hG N.obj N.property)
    (Functor.fullyFaithfulCancelRight P.ι (Functor.isoWhiskerLeft P.ι E.unitIso))
    (Functor.fullyFaithfulCancelRight Q.ι (Functor.isoWhiskerLeft Q.ι E.counitIso))

/-! ### Restriction of modules along an open immersion, over `SheafOfModules` -/

/-- Restriction of modules along an open immersion `f : X ⟶ Y` of schemes, with source and target
spelled `AlgebraicGeometry.SheafOfModules _.ringCatSheaf` rather than
`AlgebraicGeometry.Scheme.Modules`.

The underlying functor is `AlgebraicGeometry.Scheme.Modules.restrictFunctor f`: on sections over
an open `U ⊆ X` it is the module of sections of the pullback presheaf over `f(U)`. -/
private def restrictSheaves {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules.{u} Y.ringCatSheaf ⥤ SheafOfModules.{u} X.ringCatSheaf :=
  Scheme.Modules.restrictFunctor f

/-- Restriction of modules along an open immersion is additive, being computed on sections. -/
private instance additive_restrictSheaves {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictSheaves f).Additive :=
  Scheme.Modules.additive_restrictFunctor f

/-- Restriction of modules along an open immersion is left exact. -/
private instance preservesFiniteLimits_restrictSheaves {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteLimits (restrictSheaves f) :=
  Scheme.Modules.restrictFunctor_preservesFiniteLimits f

/-- Restriction of modules along an open immersion is right exact, being a left adjoint. -/
private instance preservesFiniteColimits_restrictSheaves {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteColimits (restrictSheaves f) :=
  inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor f))

/-- The restriction of a quasi-coherent module along an open immersion is quasi-coherent: a
presentation of the module pulls back to a presentation of its restriction. -/
private theorem isQuasicoherent_restrictSheaves {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : SheafOfModules.{u} Y.ringCatSheaf)
    (hM : SheafOfModules.isQuasicoherent Y.ringCatSheaf M) :
    SheafOfModules.isQuasicoherent X.ringCatSheaf ((restrictSheaves f).obj M) :=
  have : M.IsQuasicoherent := hM
  Scheme.Modules.isQuasicoherent_restrictFunctor f M

/-- Restriction along the identity of a scheme is the identity functor on its modules. -/
private def restrictSheavesId (X : Scheme.{u}) : restrictSheaves (𝟙 X) ≅ 𝟭 _ :=
  Scheme.Modules.restrictFunctorId

/-- Restriction along a composite of open immersions is the composite of the restrictions, in the
reverse order. -/
private def restrictSheavesComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f]
    [IsOpenImmersion g] : restrictSheaves (f ≫ g) ≅ restrictSheaves g ⋙ restrictSheaves f :=
  Scheme.Modules.restrictFunctorComp f g

/-- Equal open immersions have isomorphic restriction functors. -/
private def restrictSheavesCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] : restrictSheaves f ≅ restrictSheaves g :=
  Scheme.Modules.restrictFunctorCongr hf

/-- **An isomorphism of schemes induces an equivalence of their categories of modules.**
Restriction along `e.inv` and restriction along `e.hom` are mutually quasi-inverse, the unit and
counit coming from the compatibility of restriction with composition and with identities applied
to `e.hom ≫ e.inv = 𝟙 X` and `e.inv ≫ e.hom = 𝟙 Y`. -/
private def restrictSheavesEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    SheafOfModules.{u} X.ringCatSheaf ≌ SheafOfModules.{u} Y.ringCatSheaf :=
  CategoryTheory.Equivalence.mk (restrictSheaves e.inv) (restrictSheaves e.hom)
    ((restrictSheavesId X).symm ≪≫ (restrictSheavesCongr e.hom_inv_id).symm ≪≫
      restrictSheavesComp e.hom e.inv)
    ((restrictSheavesComp e.inv e.hom).symm ≪≫ restrictSheavesCongr e.inv_hom_id ≪≫
      restrictSheavesId Y)

/-! ### Transport of the comparison equivalence -/

/-- An exact additive functor between abelian categories carrying `P` into `Q` induces a functor
of derived categories carrying complexes with cohomology in `P` to complexes with cohomology in
`Q`. -/
private theorem derivedCategoryB_mapDerivedCategory {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (P : ObjectProperty A) (Q : ObjectProperty B)
    [Q.IsClosedUnderIsomorphisms] (hF : ∀ M, P M → Q (F.obj M)) (K : DerivedCategory A)
    (hK : DerivedCategoryB.derivedCategoryB P K) :
    DerivedCategoryB.derivedCategoryB Q (F.mapDerivedCategory.obj K) := fun n =>
  Q.prop_of_iso ((F.mapDerivedCategoryHomologyIso n).app K).symm (hF _ (hK n))

/-- **The comparison functor of [Stacks, Tag 06VT] is an equivalence for `X` as soon as it is one
for an isomorphic scheme `Y`.** The two sides are read at independently chosen derived categories:
`D(𝒪_X)` and `D(QCoh(𝒪_X))` at a model with morphisms in `Type w`, `D(𝒪_Y)` and `D(QCoh(𝒪_Y))` at
one with morphisms in `Type w'`.

Restriction along `e` is an exact equivalence `Mod(𝒪_X) ≌ Mod(𝒪_Y)` preserving quasi-coherence in
both directions, hence restricts to `QCoh(𝒪_X) ≌ QCoh(𝒪_Y)`; it induces an equivalence of the
unbounded derived categories of modules, and that equivalence commutes with cohomology, so it too
preserves quasi-coherence of cohomology in both directions and restricts to
`D_QCoh(𝒪_X) ≌ D_QCoh(𝒪_Y)`. Because the comparison functor becomes the derived functor of
`ι : QCoh ⥤ Mod` after composing with the inclusion of `D_QCoh`, and that inclusion is fully
faithful, the four equivalences make `i_X` followed by restriction isomorphic to restriction
followed by `i_Y`. The latter is an equivalence by hypothesis, and cancelling the equivalence on
the right leaves `i_X`. -/
theorem isEquivalence_derivedQuasicoherentComparison_of_schemeIso {X Y : Scheme.{u}} (e : X ≅ Y)
    [hX : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    [hXq : HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory]
    [hY : HasDerivedCategory.{w'} (SheafOfModules.{u} Y.ringCatSheaf)]
    [hYq : HasDerivedCategory.{w'} (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory]
    (h : (derivedQuasicoherentComparison.{w'} Y).IsEquivalence) :
    (derivedQuasicoherentComparison.{w} X).IsEquivalence := by
  let E := restrictSheavesEquivalence e
  have : E.functor.Additive := additive_restrictSheaves e.inv
  have : E.inverse.Additive := additive_restrictSheaves e.hom
  have : PreservesFiniteLimits E.functor := preservesFiniteLimits_restrictSheaves e.inv
  have : PreservesFiniteColimits E.functor := preservesFiniteColimits_restrictSheaves e.inv
  have : PreservesFiniteLimits E.inverse := preservesFiniteLimits_restrictSheaves e.hom
  have : PreservesFiniteColimits E.inverse := preservesFiniteColimits_restrictSheaves e.hom
  have hF : ∀ M, SheafOfModules.isQuasicoherent X.ringCatSheaf M →
      SheafOfModules.isQuasicoherent Y.ringCatSheaf (E.functor.obj M) := fun M hM =>
    isQuasicoherent_restrictSheaves e.inv M hM
  have hG : ∀ N, SheafOfModules.isQuasicoherent Y.ringCatSheaf N →
      SheafOfModules.isQuasicoherent X.ringCatSheaf (E.inverse.obj N) := fun N hN =>
    isQuasicoherent_restrictSheaves e.hom N hN
  let Eqc := liftEquivalence E (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf) hF hG
  have : Eqc.functor.IsEquivalence := Eqc.isEquivalence_functor
  have : Eqc.functor.Additive := Functor.additive_of_preserves_binary_products _
  let ED := Equivalence.mapDerivedCategory E
  have hDF := derivedCategoryB_mapDerivedCategory E.functor
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
    hF
  have hDG := derivedCategoryB_mapDerivedCategory E.inverse
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf) (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    hG
  let EDqc := liftEquivalence ED
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf))
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) hDF hDG
  let sq : Eqc.functor.mapDerivedCategory ⋙ derivedQuasicoherentComparison.{w'} Y ≅
      derivedQuasicoherentComparison.{w} X ⋙ EDqc.functor :=
    Functor.fullyFaithfulCancelRight
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι
      (Functor.isoWhiskerLeft Eqc.functor.mapDerivedCategory
          (derivedQuasicoherentComparisonCompι.{w'} Y) ≪≫
        Stacks.DerivedGlueing.mapDerivedCategoryCompIso Eqc.functor
          (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ≪≫
        Stacks.DerivedGlueing.mapDerivedCategoryCongr
          (Iso.refl (Eqc.functor ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι)) ≪≫
        (Stacks.DerivedGlueing.mapDerivedCategoryCompIso
          (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι E.functor).symm ≪≫
        Functor.isoWhiskerRight (derivedQuasicoherentComparisonCompι.{w} X).symm
          E.functor.mapDerivedCategory)
  have : Eqc.functor.mapDerivedCategory.IsEquivalence :=
    (Equivalence.mapDerivedCategory Eqc).isEquivalence_functor
  have : (derivedQuasicoherentComparison.{w} X ⋙ EDqc.functor).IsEquivalence :=
    Functor.isEquivalence_of_iso sq
  have : EDqc.functor.IsEquivalence := EDqc.isEquivalence_functor
  exact Functor.isEquivalence_of_comp_right (derivedQuasicoherentComparison.{w} X) EDqc.functor

/-- **Whether the comparison functor of [Stacks, Tag 06VT] is an equivalence is independent of the
chosen models of the two derived categories.** If it is an equivalence for the choices `h₁` of
`D(𝒪_X)` and `h₂` of `D(QCoh(𝒪_X))`, with morphisms in `Type w`, then it is an equivalence for any
other pair of choices `h₃`, `h₄`, with morphisms in `Type w'`.

This is the transport along an isomorphism of schemes applied to the identity isomorphism of `X`:
the equivalence of modules is the identity, and all the content is in the comparison of the two
localizations of the cochain complexes.

The four choices are explicit arguments and the comparison functor is applied with `@`, since two
instances of each class for the same category are in scope and instance resolution cannot
distinguish them. -/
theorem isEquivalence_derivedQuasicoherentComparison_of_model (X : Scheme.{u})
    (h₁ : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf))
    (h₂ : HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (h₃ : HasDerivedCategory.{w'} (SheafOfModules.{u} X.ringCatSheaf))
    (h₄ : HasDerivedCategory.{w'} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    (h : (@derivedQuasicoherentComparison X h₁ h₂).IsEquivalence) :
    (@derivedQuasicoherentComparison X h₃ h₄).IsEquivalence :=
  isEquivalence_derivedQuasicoherentComparison_of_schemeIso (hX := h₃) (hXq := h₄) (hY := h₁)
    (hYq := h₂) (Iso.refl X) h

/-- **[Stacks, Tag 06Z0].** For every affine scheme `X` the comparison functor
`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of [Stacks, Tag 06VT] is an equivalence of triangulated
categories, at every choice of the two derived categories.

`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence` is this statement for `Spec R`
at the locally small model. An affine scheme is isomorphic to `Spec Γ(X, ⊤)` by
`AlgebraicGeometry.Scheme.isoSpec`, and transporting along that isomorphism simultaneously changes
the scheme and the model.

`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isAffine` is this statement
at the locally small model alone, that is the case `w = u`. -/
@[stacks 06Z0 "comparison equivalence, any affine scheme at any model"]
theorem derivedQuasicoherentComparison_isEquivalence_of_isAffine_atModel (X : Scheme.{u})
    [IsAffine X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
    [HasDerivedCategory.{w} (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory] :
    (derivedQuasicoherentComparison.{w} X).IsEquivalence :=
  isEquivalence_derivedQuasicoherentComparison_of_schemeIso X.isoSpec
    (derivedQuasicoherentComparison_isEquivalence Γ(X, ⊤))

end Stacks.DerivedQCoh

end
