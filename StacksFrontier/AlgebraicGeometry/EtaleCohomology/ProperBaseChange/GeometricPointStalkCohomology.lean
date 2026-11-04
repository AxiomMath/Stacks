module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.DirectImageGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerivedOfIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange

/-!
# Stalks of higher direct images at a geometric point, from base change

Let `f : X ⟶ Y` be a morphism of schemes and `ȳ : Spec Ω ⟶ Y` a geometric point, `Ω` a
separably closed field, with geometric fibre `X_ȳ = X ×_Y Spec Ω` and projections
`g' : X_ȳ ⟶ X`, `f' : X_ȳ ⟶ Spec Ω`. For an object `E` of the unbounded derived category of
abelian sheaves on `X_étale` there is a chain of canonical identifications

`(Hⁿ(Rf_* E))_ȳ ≅ (ȳ⁻¹ Hⁿ(Rf_* E))_{can} ≅ Hⁿ(ȳ⁻¹ Rf_* E)_{can}`
`  ≅ Hⁿ(Rf'_* (g')⁻¹ E)_{can} ≅ Hⁿ(RΓ(X_ȳ, (g')⁻¹ E))`

in which the third step is the base change map of the cartesian square of the geometric fibre and
every other step holds for every morphism `f`. So as soon as the base change map is invertible at
`E`, the stalk at `ȳ` of the `n`-th cohomology sheaf of `Rf_* E` is the `n`-th étale
hypercohomology of the fibre. This file proves exactly that, and specializes it to the two
situations of [Stacks, Tag 0DDF]: a torsion abelian sheaf, when cohomology commutes with base
change for `f` (the conclusion of [Stacks, Tag 095T] for proper `f`), and a bounded below complex
with torsion cohomology sheaves, through the derived step of [Stacks, Tag 0DDE].

The other steps are these. The stalk at `ȳ` is the stalk of the inverse image along `ȳ` at the
canonical point of `Spec Ω` (`Stacks.EtaleCohomology.etaleAbelianInverseImageSheafFiberIso`).
Inverse image and stalk functors are exact, so they commute with the cohomology of complexes
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`). Over the spectrum of a separably closed
field the étale neighbourhoods of the canonical point have an initial object, so the stalk there is
global sections; hence the stalk at the canonical point composed with `f'_*` is global sections on
`X_ȳ`, and since the stalk is exact it passes through the derived direct image
(`Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIsoOfIso`), giving
`RΓ(X_ȳ, −)`.

## Main definitions

* `Stacks.EtaleCohomology.isInitialPointSmallEtaleUliftIdElement` — the identity lift of the
  canonical point of `Spec Ω` is initial among the étale neighbourhoods of the universe-lifted
  point.
* `Stacks.EtaleCohomology.sheafFiberUliftIdIsoGamma` — **the stalk of an abelian sheaf at the
  canonical point of the spectrum of a separably closed field is its group of global sections.**
* `Stacks.EtaleCohomology.etaleAbelianSheafFiberIsoInverseImageGamma` — the stalk of an abelian
  sheaf at a geometric point `ȳ` is the group of global sections of its inverse image along `ȳ`.
* `Stacks.EtaleCohomology.etaleAbelianSheafFiberCompDirectImageIsoGamma` — the stalk at the
  canonical point of `Spec Ω` of a direct image along `f' : X' ⟶ Spec Ω` is the group of global
  sections on `X'`.
* `Stacks.EtaleCohomology.etaleAbelianSheafFiberMapDerivedCategoryDerivedDirectImageIso` —
  `(Rf'_* L)_{can} ≅ RΓ(X', L)` for `f' : X' ⟶ Spec Ω`, on the whole unbounded derived category.
* `Stacks.EtaleCohomology.etaleAbelianSheafFiberHomologyDerivedDirectImageIsoOfIsIso` — **the
  stalk at `ȳ` of `Hⁿ(Rf_* E)` is `Hⁿ(RΓ(X_ȳ, E|_{X_ȳ}))`**, granted that the base change map of
  the geometric fibre square is invertible at `E`.
* `Stacks.EtaleCohomology.etaleAbelianSheafFiberHomologyDerivedDirectImageIso` — the same for `E`
  bounded below with torsion cohomology sheaves, when cohomology commutes with base change for `f`
  (the derived half of Stacks 0DDF).
* `Stacks.EtaleCohomology.etaleAbelianSheafFiberRightDerivedDirectImageIso` — for a torsion abelian
  sheaf `F`, when cohomology commutes with base change for `f`,
  `(Rⁿf_* F)_ȳ ≅ Hⁿ_étale(X_ȳ, F|_{X_ȳ})` with Mathlib's sheaf cohomology `CategoryTheory.Sheaf.H`
  (the sheaf half of Stacks 0DDF).

## Implementation notes

The stalk at a geometric point `ȳ` of an abelian sheaf with coefficients in
`AddCommGrpCat.{max (u + 1) v}` is the fibre functor of the universe lift
`(pointSmallEtale ȳ).ulift.{max (u + 1) v}` of Mathlib's point of the small étale site, as in
`Stacks.EtaleCohomology.etaleAbelianInverseImageSheafFiberIso`.

The cohomology sheaf `Hⁿ(Rf_* E)` is `DerivedCategory.homologyFunctor` of the unbounded derived
direct image `Stacks.EtaleCohomology.etaleAbelianDerivedDirectImage`, the functor that the
condition `Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange` is phrased in; for a sheaf
`Rⁿf_* F` is Mathlib's `CategoryTheory.Functor.rightDerived`, compared with the unbounded one by
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso`. Étale cohomology of a sheaf is
`CategoryTheory.Sheaf.H`, compared with the right derived functors of global sections by
`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`; the hypercohomology of a complex is
the cohomology of the unbounded derived global sections
`Stacks.DerivedFunctor.totalRightDerived (Sheaf.Γ X_ȳ.smallEtaleTopology _)`.

The base change hypothesis is taken in the form the source takes it: the statements are the
specialisation of [Stacks, Tag 095T] and [Stacks, Tag 0DDE] to `Spec Ω ⟶ Y`, so they carry
`CohomologyCommutesWithBaseChange f` and nothing else; for `f` proper that condition is Tag 095T.
Nothing here is registered under Tag 0DDF itself, because that tag asserts the result for proper
`f` without the condition.

## References

* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- Global sections of abelian sheaves on a small étale site, with coefficients in
`AddCommGrpCat.{max (u + 1) v}`, form an additive functor: it is a right adjoint, so it preserves
binary products. -/
local instance additive_globalSections_smallEtale (Z : Scheme.{u}) :
    (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The stalk functor of a point of the small étale site relative to the coefficient universe is
left exact: it is a filtered colimit, and filtered colimits of abelian groups are exact. -/
local instance preservesFiniteLimits_sheafFiber_smallEtale {Z : Scheme.{u}}
    (Φ : GrothendieckTopology.Point.{max (u + 1) v} Z.smallEtaleTopology) :
    PreservesFiniteLimits (Φ.sheafFiber (A := AddCommGrpCat.{max (u + 1) v})) :=
  inferInstance

/-- The stalk functor of a point of the small étale site is additive, being left exact. -/
local instance additive_sheafFiber_smallEtale {Z : Scheme.{u}}
    (Φ : GrothendieckTopology.Point.{max (u + 1) v} Z.smallEtaleTopology) :
    (Φ.sheafFiber (A := AddCommGrpCat.{max (u + 1) v})).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The stalk functor of a point of the small étale site is right exact, being a left adjoint. -/
local instance preservesFiniteColimits_sheafFiber_smallEtale {Z : Scheme.{u}}
    (Φ : GrothendieckTopology.Point.{max (u + 1) v} Z.smallEtaleTopology) :
    PreservesFiniteColimits (Φ.sheafFiber (A := AddCommGrpCat.{max (u + 1) v})) :=
  inferInstance

/-! ### The stalk at the canonical point of the spectrum of a separably closed field -/

section CanonicalPoint

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- The identity, viewed as a lift of the canonical point of `Spec Ω` to the final object of the
small étale site of `Spec Ω`, for the universe lift of that point. -/
def pointSmallEtaleUliftIdElement :
    ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).fiber.obj
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) :=
  ULift.up (pointSmallEtaleIdElement Ω)

/-- The final object of the small étale site of `Spec Ω` with its identity lift is an initial
étale neighbourhood of the universe lift of the canonical point: the category of elements of the
lifted fibre functor is that of the original one (`CategoryTheory.Functor.Elements.uliftEquiv`),
where the identity lift is initial (`Stacks.EtaleCohomology.isInitialPointSmallEtaleIdElement`). -/
def isInitialPointSmallEtaleUliftIdElement :
    IsInitial (show ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).fiber.Elements from
      ⟨Scheme.Etale.mk (𝟙 (Spec (.of Ω))), pointSmallEtaleUliftIdElement.{u, v} Ω⟩) :=
  (isInitialPointSmallEtaleIdElement Ω).isInitialObj
    (Functor.Elements.uliftEquiv.{max (u + 1) v} (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber).functor

variable (A : Type*) [Category A] [HasColimitsOfSize.{max (u + 1) v, max (u + 1) v} A]

/-- **The fibre at the universe lift of the canonical point of the spectrum of a separably closed
field is evaluation at the final object**, for presheaves with values in any category with the
colimits computing it: the étale neighbourhoods of that point have an initial object, so the
colimit computing the fibre is attained there. -/
def presheafFiberUliftIdIsoSections :
    (evaluation (Spec (.of Ω)).Etaleᵒᵖ A).obj (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ≅
      ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).presheafFiber := by
  let Φ := (pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}
  let τ := Φ.toPresheafFiberNatTrans (A := A) (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
    (pointSmallEtaleUliftIdElement.{u, v} Ω)
  letI : ∀ P, IsIso (τ.app P) := fun P ↦
    (Φ.isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal
      (op ⟨Scheme.Etale.mk (𝟙 (Spec (.of Ω))), pointSmallEtaleUliftIdElement.{u, v} Ω⟩)
      (isInitialPointSmallEtaleUliftIdElement.{u, v} Ω).op
  letI := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- **The stalk of an abelian sheaf at the canonical point of the spectrum of a separably closed
field is its group of global sections.** Both are evaluation at the final object of the small
étale site, the stalk because the identity lift is an initial étale neighbourhood. -/
def sheafFiberUliftIdIsoGamma :
    ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v}) ≅
      Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  (Functor.isoWhiskerLeft
      (sheafToPresheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (presheafFiberUliftIdIsoSections.{u, v} Ω AddCommGrpCat.{max (u + 1) v})).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}
      (isTerminalEtaleMkId (Spec (.of Ω)))).symm

end CanonicalPoint

/-! ### The stalk at a geometric point as global sections of an inverse image -/

section GeometricPoint

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)

/-- **The stalk of an abelian sheaf at a geometric point `ȳ` is the stalk of its inverse image
along `ȳ` at the canonical point of `Spec Ω`.** This is
`Stacks.EtaleCohomology.etaleAbelianInverseImageSheafFiberIso` at the canonical point, whose
composite with `ȳ` is `ȳ`. -/
def etaleAbelianSheafFiberIsoInverseImageSheafFiber :
    ((pointSmallEtale y).ulift.{max (u + 1) v}).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v}) ≅
      etaleAbelianInverseImage.{u, v} y ⋙
        ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber :=
  eqToIso (congrArg (fun z : Spec (.of Ω) ⟶ Y ↦
      ((pointSmallEtale z).ulift.{max (u + 1) v}).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})) (Category.id_comp y).symm) ≪≫
    (etaleAbelianInverseImageSheafFiberIso.{u, v} y (𝟙 (Spec (.of Ω)))).symm

/-- **The stalk of an abelian sheaf at a geometric point `ȳ` is the group of global sections of
its inverse image along `ȳ`**: the stalk of the inverse image at the canonical point of `Spec Ω`,
which over a separably closed field is global sections. -/
def etaleAbelianSheafFiberIsoInverseImageGamma :
    ((pointSmallEtale y).ulift.{max (u + 1) v}).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v}) ≅
      etaleAbelianInverseImage.{u, v} y ⋙
        Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  etaleAbelianSheafFiberIsoInverseImageSheafFiber.{u, v} y ≪≫
    Functor.isoWhiskerLeft _ (sheafFiberUliftIdIsoGamma.{u, v} Ω)

end GeometricPoint

/-! ### The derived direct image to a separably closed point -/

section DerivedSections

variable {X' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (f' : X' ⟶ Spec (.of Ω))

/-- **The stalk at the canonical point of `Spec Ω` of a direct image along `f' : X' ⟶ Spec Ω` is
the group of global sections on `X'`**: the stalk there is global sections on `Spec Ω`, and global
sections of a direct image are global sections upstairs. -/
def etaleAbelianSheafFiberCompDirectImageIsoGamma :
    etaleAbelianDirectImage.{u, v} f' ⋙
        ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v}) ≅
      Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  Functor.isoWhiskerLeft _ (sheafFiberUliftIdIsoGamma.{u, v} Ω) ≪≫
    etaleAbelianDirectImageCompΓIso.{u, v} f'

/-- **`(Rf'_* L)_{can} ≅ RΓ(X', L)` for `f' : X' ⟶ Spec Ω`**, naturally in `L` on the unbounded
derived category: the stalk at the canonical point is exact, so it passes through the derived
direct image, and the composite of the stalk with `f'_*` is global sections on `X'`. -/
def etaleAbelianSheafFiberMapDerivedCategoryDerivedDirectImageIso :
    etaleAbelianDerivedDirectImage.{u, v} f' ⋙
        (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})).mapDerivedCategory ≅
      Stacks.DerivedFunctor.totalRightDerived
        (Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIsoOfIso
    (etaleAbelianDirectImage.{u, v} f')
    (((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v}))
    (Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (etaleAbelianSheafFiberCompDirectImageIsoGamma.{u, v} f')

end DerivedSections

/-! ### The stalk of a derived direct image at a geometric point -/

section Stalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

/-- **The stalk at a geometric point of a cohomology sheaf of a derived direct image, granted
base change.** Let `f : X ⟶ Y` be a morphism of schemes, `ȳ : Spec Ω ⟶ Y` a geometric point and
`X_ȳ = X ×_Y Spec Ω` the geometric fibre, with projection `g' : X_ȳ ⟶ X`. If the base change map
`ȳ⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` of the cartesian square of the fibre is invertible at an object `E`
of the unbounded derived category of abelian sheaves on `X_étale`, then
`(Hⁿ(Rf_* E))_ȳ ≅ Hⁿ(RΓ(X_ȳ, (g')⁻¹ E))` for every `n`. -/
def etaleAbelianSheafFiberHomologyDerivedDirectImageIsoOfIsIso
    (E : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (hbc : IsIso ((etaleAbelianDerivedBaseChange.{u, v} f y (pullback.fst f y) (pullback.snd f y)
      pullback.condition).app E)) (n : ℤ) :
    (((pointSmallEtale y).ulift.{max (u + 1) v}).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj
      ((DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        n).obj ((etaleAbelianDerivedDirectImage.{u, v} f).obj E)) ≅
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max (u + 1) v} n).obj
      ((Stacks.DerivedFunctor.totalRightDerived
        (Sheaf.Γ (pullback f y).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})).obj
        ((etaleAbelianDerivedInverseImage.{u, v} (pullback.fst f y)).obj E)) :=
  let S := ((pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{max (u + 1) v}).sheafFiber
    (A := AddCommGrpCat.{max (u + 1) v})
  (etaleAbelianSheafFiberIsoInverseImageSheafFiber.{u, v} y).app _ ≪≫
    S.mapIso (((etaleAbelianInverseImage.{u, v} y).mapDerivedCategoryHomologyIso n).app
      ((etaleAbelianDerivedDirectImage.{u, v} f).obj E)).symm ≪≫
    S.mapIso ((DerivedCategory.homologyFunctor _ n).mapIso (asIso
      ((etaleAbelianDerivedBaseChange.{u, v} f y (pullback.fst f y) (pullback.snd f y)
        pullback.condition).app E))) ≪≫
    ((S.mapDerivedCategoryHomologyIso n).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso
      ((etaleAbelianSheafFiberMapDerivedCategoryDerivedDirectImageIso.{u, v}
        (pullback.snd f y)).app _)

/-- **The stalk at a geometric point of a cohomology sheaf of a derived direct image of a bounded
below complex with torsion cohomology sheaves** (the derived half of Stacks 0DDF, granted base
change). Suppose that cohomology commutes with base change for `f : X ⟶ Y`. For a geometric point
`ȳ : Spec Ω ⟶ Y` with geometric fibre `X_ȳ = X ×_Y Spec Ω`, projection `g' : X_ȳ ⟶ X`, and an
object `E` of `D^+(X_étale)` with torsion cohomology sheaves,
`(Hⁿ(Rf_* E))_ȳ ≅ Hⁿ(RΓ(X_ȳ, E|_{X_ȳ}))` for every `n`.

For `f` proper the hypothesis is Stacks 095T. -/
def etaleAbelianSheafFiberHomologyDerivedDirectImageIso
    (hf : CohomologyCommutesWithBaseChange.{u, v} f)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) (m : ℤ)
    (hE : E.IsGE m)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} X.smallEtaleTopology E)
    (n : ℤ) :
    (((pointSmallEtale y).ulift.{max (u + 1) v}).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj
      ((DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
        n).obj ((etaleAbelianDerivedDirectImage.{u, v} f).obj E)) ≅
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max (u + 1) v} n).obj
      ((Stacks.DerivedFunctor.totalRightDerived
        (Sheaf.Γ (pullback f y).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})).obj
        ((etaleAbelianDerivedInverseImage.{u, v} (pullback.fst f y)).obj E)) :=
  etaleAbelianSheafFiberHomologyDerivedDirectImageIsoOfIsIso.{u, v} f y E
    (isIso_etaleAbelianDerivedBaseChange_of_cohomologyCommutesWithBaseChange.{u, v} hf
      (IsPullback.of_hasPullback f y) E m hE hT) n

/-- **The stalk at a geometric point of a higher direct image of a torsion sheaf** (the sheaf half
of Stacks 0DDF, granted base change). Suppose that cohomology commutes with base change for
`f : X ⟶ Y`. For a geometric point `ȳ : Spec Ω ⟶ Y` with geometric fibre `X_ȳ = X ×_Y Spec Ω`,
projection `g' : X_ȳ ⟶ X`, and a torsion abelian sheaf `F` on `X_étale`,
`(Rⁿf_* F)_ȳ ≅ Hⁿ_étale(X_ȳ, F_ȳ)` for every `n`, where `F_ȳ = (g')⁻¹ F`.

For `f` proper the hypothesis is Stacks 095T. -/
def etaleAbelianSheafFiberRightDerivedDirectImageIso
    (hf : CohomologyCommutesWithBaseChange.{u, v} f)
    [HasExt.{max (u + 1) v}
      (Sheaf (pullback f y).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (n : ℕ) :
    (((pointSmallEtale y).ulift.{max (u + 1) v}).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).obj
      (((etaleAbelianDirectImage.{u, v} f).rightDerived n).obj F) ≅
    AddCommGrpCat.of
      (Sheaf.H.{max (u + 1) v} ((etaleAbelianInverseImage.{u, v} (pullback.fst f y)).obj F) n) :=
  let S := ((pointSmallEtale y).ulift.{max (u + 1) v}).sheafFiber
    (A := AddCommGrpCat.{max (u + 1) v})
  let g' := pullback.fst f y
  S.mapIso (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (etaleAbelianDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f)
      (etaleAbelianDerivedDirectImageUnit.{u, v} f)
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective F n).symm ≪≫
    etaleAbelianSheafFiberHomologyDerivedDirectImageIsoOfIsIso.{u, v} f y _
      (hf y g' (pullback.snd f y) (IsPullback.of_hasPullback f y) F hF) n ≪≫
    (DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
      ((Stacks.DerivedFunctor.totalRightDerived
        (Sheaf.Γ (pullback f y).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})).mapIso
        (((etaleAbelianInverseImage.{u, v} g').mapDerivedCategorySingleFunctor 0).app F)) ≪≫
    Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (Sheaf.Γ (pullback f y).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (Stacks.DerivedFunctor.totalRightDerived
        (Sheaf.Γ (pullback f y).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
      ((Stacks.DerivedFunctor.homotopyMap (Sheaf.Γ (pullback f y).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v})).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective _ n ≪≫
    (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{v}
      (pullback f y).smallEtaleTopology n).app _

end Stalk

end Stacks.EtaleCohomology

end
