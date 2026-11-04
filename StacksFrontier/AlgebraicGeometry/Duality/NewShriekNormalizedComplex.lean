module

public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexes

/-!
# The normalized complex is the new twisted inverse image of the complex downstairs

Fix a Noetherian scheme `S` with a dualizing complex `ω_S^•` — Situation [Stacks, Tag 0AU4],
carried by `Stacks.Duality.DualizingBase` — and for each scheme `X` of finite type over `S` the
complex `ω_X^•` normalized relative to it, [Stacks, Tag 0AU5]. Write `D_X(-) = R𝓗om(-, ω_X^•)`
for `Stacks.Duality.relativeDual` and

`f_new^! M = D_X(Lf^* D_Y(M))`

for `Stacks.Duality.fNewShriek`, the functor of
`StacksFrontier/AlgebraicGeometry/Duality/GlueingDualizingComplexes.lean`.

This file proves parts (2) and (4) of [Stacks, Tag 0AUE]: the normalized complex upstairs is
what `f_new^!` does to the complex downstairs,

`ω_X^• = f_new^! ω_Y^•`,

for any morphism `f : X ⟶ Y` of schemes of finite type over `S`, and in particular
`ω_X^• = (X → S)_new^! ω_S^•` for the structure morphism. The proof is the source's own
three-step computation,

`f_new^! ω_Y^• = D_X(Lf^* D_Y(ω_Y^•)) = D_X(Lf^* 𝒪_Y) = D_X(𝒪_X) = ω_X^•`,

whose last step is the only one with content beyond the two inputs: `R𝓗om(𝒪_X, ω_X^•) ≅ ω_X^•`
holds in any closed monoidal category because both `R𝓗om(𝟙, -)` and the identity functor are
right adjoint to `𝟙 ⊗ -`, which is `CategoryTheory.MonoidalClosed.unitIsoSelf`.

Neither statement is an equality by definition: `Stacks.Duality.fNewShriek` is defined by the
displayed formula, so `(f_new^! ω_Y^•)` unfolds to `R𝓗om(Lf^* R𝓗om(ω_Y^•, ω_Y^•), ω_X^•)`, and
identifying that with `ω_X^•` is the computation above.

## Main definitions

All in the namespace `Stacks.Duality`.

* `relativeDualObjUnit` — `D_X(𝒪_X) ≅ ω_X^•`, the duality functor evaluated at the monoidal
  unit.

## Main results

* `Stacks.Duality.fNewShriekObjIsoDualizing` — **[Stacks, Tag 0AUE] part (4)**:
  `f_new^! ω_Y^• ≅ ω_X^•` for a morphism `f : X ⟶ Y` of schemes of finite type over the base.
* `Stacks.Duality.fNewShriekStructureObjIsoDualizing` — **[Stacks, Tag 0AUE] part (2)**: the
  same for the structure morphism `X → S`, giving `ω_X^• ≅ (X → S)_new^! ω_S^•`, stated in the
  vocabulary of `Stacks.Duality.DualizingBase` and `Stacks.Duality.FiniteTypeOverBase`.

## Implementation notes

*The two inputs.* Exactly the two ingredients the source names are hypotheses.

* `D_Y(ω_Y^•) ≅ 𝒪_Y`, written `(relativeDual ωY).obj (op ωY) ≅ 𝟙_ _`. This is the homothety
  condition in the definition of a dualizing complex, [Stacks, Tag 0A7B] at the ring level and
  [Stacks, Tag 0A87] at the sheaf level; `Stacks.Duality.IsDualizingComplex` is the
  affine-local form of the latter, and the sheaf-level identification
  `R𝓗om_{𝒪_Y}(ω_Y^•, ω_Y^•) ≅ 𝒪_Y` that it yields is not available in this repository at the
  model of the derived category this file works at. It says nothing about `X` or `f`, so it is
  an input and not a piece of either conclusion.
* `Lf^* 𝒪_Y ≅ 𝒪_X`, written `(derivedPullback f).obj (𝟙_ _) ≅ 𝟙_ _`. This is the unit half of
  the monoidality of `Lf^*`, [Stacks, Tag 0B54]; it enters in exactly the shape the `ea` and
  `eb` hypotheses of `Stacks.Duality.fNewShriekBaseTwistIso` already use.

*The closed monoidal structure.* As in
`StacksFrontier/AlgebraicGeometry/Duality/GlueingDualizingComplexes.lean`, the monoidal structure
`- ⊗^L -` of [Stacks, Tag 06YU] and the derived internal hom of [Stacks, Tag 08DH] on
`D(𝒪_X)` are instance arguments, because `Stacks.SheafOfModules.derivedSheafHom` is available
only at `CategoryTheory.HasDerivedCategory.standard` while
`Stacks.Duality.derivedPullback` forces the locally small model. No braiding is needed here.

*What is left of [Stacks, Tag 0AUE].* Parts (1), (3), (5) and (6) are not in this file, and no
unqualified attribute for the tag appears: each attribute below names the part it carries.

## References

* [Stacks Project, Tag 0AU4](https://stacks.math.columbia.edu/tag/0AU4)
* [Stacks Project, Tag 0AU5](https://stacks.math.columbia.edu/tag/0AU5)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed Opposite

universe u

namespace Stacks.Duality

section NormalizedComplex

variable {X Y : Scheme.{u}}
  [MonoidalCategory (DerivedCategory X.Modules)] [MonoidalClosed (DerivedCategory X.Modules)]
  [MonoidalCategory (DerivedCategory Y.Modules)] [MonoidalClosed (DerivedCategory Y.Modules)]

/-- `D_X(𝒪_X) ≅ ω_X^•`: the duality functor `R𝓗om(-, ω_X^•)` of [Stacks, Tag 0AUE] evaluated at
the monoidal unit returns the complex it dualizes against.

This holds in any closed monoidal category: `R𝓗om(𝟙, -)` and the identity functor are both
right adjoint to `𝟙 ⊗ -`. -/
def relativeDualObjUnit (ω : DerivedCategory X.Modules) :
    (relativeDual ω).obj (op (𝟙_ (DerivedCategory X.Modules))) ≅ ω :=
  MonoidalClosed.unitIsoSelf (X := ω)

/-- **Stacks Project, Tag 0AUE, part (4).** Let `f : X ⟶ Y` be a morphism of schemes of finite
type over the base of [Stacks, Tag 0AU4] and let `ω_X^•` and `ω_Y^•` be the complexes
normalized relative to `ω_S^•`, [Stacks, Tag 0AU5]. Then

`f_new^! ω_Y^• ≅ ω_X^•`.

The computation is the source's: `D_Y(ω_Y^•) ≅ 𝒪_Y` because `ω_Y^•` is dualizing, `Lf^*` carries
the unit to the unit, and `D_X(𝒪_X) ≅ ω_X^•` by `Stacks.Duality.relativeDualObjUnit`. The
statement is not an identity by definition: `Stacks.Duality.fNewShriek` unfolds the left hand
side to `R𝓗om(Lf^* R𝓗om(ω_Y^•, ω_Y^•), ω_X^•)`, and the three steps above are what turn that
into `ω_X^•`. -/
@[stacks 0AUE "part (4): omega_X is f_new^! of omega_Y for a finite-type morphism over the base.
RESTRICTED: the closed monoidal structure on the derived categories is an instance argument, and
the two inputs the source names are hypotheses -- the identification R Hom(omega_Y, omega_Y) =
O_Y coming from omega_Y being dualizing, and the unit half Lf^* O_Y = O_X of the monoidality of
the derived pullback"]
def fNewShriekObjIsoDualizing (f : X ⟶ Y) (ωX : DerivedCategory X.Modules)
    (ωY : DerivedCategory Y.Modules)
    (eY : (relativeDual ωY).obj (op ωY) ≅ 𝟙_ (DerivedCategory Y.Modules))
    (ef : (derivedPullback f).obj (𝟙_ (DerivedCategory Y.Modules)) ≅
      𝟙_ (DerivedCategory X.Modules)) :
    (fNewShriek f ωX ωY).obj ωY ≅ ωX :=
  ((relativeDual ωX).mapIso ((derivedPullback f).mapIso eY ≪≫ ef).op).symm ≪≫
    relativeDualObjUnit ωX

end NormalizedComplex

section OverBase

variable {B : DualizingBase.{u}} (Xb : FiniteTypeOverBase B)
  [MonoidalCategory (DerivedCategory Xb.scheme.Modules)]
  [MonoidalClosed (DerivedCategory Xb.scheme.Modules)]
  [MonoidalCategory (DerivedCategory B.scheme.Modules)]
  [MonoidalClosed (DerivedCategory B.scheme.Modules)]

/-- **Stacks Project, Tag 0AUE, part (2).** For a scheme `X` of finite type over the base of
[Stacks, Tag 0AU4], with structure morphism `π : X ⟶ S`, the complex normalized relative to
`ω_S^•` is what `π_new^!` does to `ω_S^•`:

`ω_X^• ≅ (X → S)_new^! ω_S^•`.

This is `Stacks.Duality.fNewShriekObjIsoDualizing` at the structure morphism, read in the
vocabulary of the Situation: the two inputs become `D_S(ω_S^•) ≅ 𝒪_S`, which is the homothety
condition of the dualizing complex `B.isDualizing` names, and `Lπ^* 𝒪_S ≅ 𝒪_X`. -/
@[stacks 0AUE "part (2): omega_X is the new twisted inverse image of omega_S along the structure
morphism. RESTRICTED: the closed monoidal structure on the derived categories is an instance
argument, and the identification R Hom(omega_S, omega_S) = O_S implied by B.isDualizing together
with the unit half Lpi^* O_S = O_X of the monoidality of the derived pullback are hypotheses"]
def fNewShriekStructureObjIsoDualizing
    (eS : (relativeDual B.dualizing).obj (op B.dualizing) ≅
      𝟙_ (DerivedCategory B.scheme.Modules))
    (ep : (derivedPullback Xb.str).obj (𝟙_ (DerivedCategory B.scheme.Modules)) ≅
      𝟙_ (DerivedCategory Xb.scheme.Modules)) :
    (fNewShriek Xb.str Xb.dualizing B.dualizing).obj B.dualizing ≅ Xb.dualizing :=
  fNewShriekObjIsoDualizing Xb.str Xb.dualizing B.dualizing eS ep

end OverBase

end Stacks.Duality

end
