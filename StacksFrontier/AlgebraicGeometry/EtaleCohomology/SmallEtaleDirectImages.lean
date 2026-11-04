module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct images and higher direct images on the small étale site

Let `f : X ⟶ Y` be a morphism of schemes. Base change
`Stacks.EtaleCohomology.smallEtaleBaseChange f : Y.Etale ⥤ X.Etale` is a continuous functor of
small étale sites, so precomposition with it sends a sheaf on `X_étale` to a sheaf on `Y_étale`:
this is the direct image, or pushforward, `f_*`, and its sections over an étale `Y`-scheme `V`
are the sections of the given sheaf over the base change `V ×_Y X`. This file records that
functor for sheaves of sets, and, for abelian coefficients, the higher direct images `R^p f_*`,
the right derived functors of `f_* : Ab(X_étale) ⥤ Ab(Y_étale)`.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleDirectImage` — the direct image `f_*` on sheaves of sets of
  the small étale sites.
* `Stacks.EtaleCohomology.etaleAbelianHigherDirectImage` — the higher direct images `R^p f_*` on
  abelian sheaves of the small étale sites.

## Main results

* `Stacks.EtaleCohomology.smallEtaleDirectImage_obj_obj` — the sections of `f_* F` over an étale
  `Y`-scheme `V` are the sections of `F` over the base change `V ×_Y X`.
* `Stacks.EtaleCohomology.isZero_etaleAbelianHigherDirectImage_injective_succ` — the higher
  direct images of an injective abelian sheaf vanish in positive degrees.

## Implementation notes

That the presheaf `V ↦ F(V ×_Y X)` is again a sheaf is built into
`CategoryTheory.Functor.sheafPushforwardContinuous`, which lands in the category of sheaves;
the input is continuity of base change,
`Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous`. No limits in the coefficient
category are needed, the functor being precomposition, so the sections formula holds on the
nose.

The higher direct images are `CategoryTheory.Functor.rightDerived` applied to the abelian direct
image `Stacks.EtaleCohomology.etaleAbelianDirectImage`, which is legitimate because that functor
is additive and abelian sheaves on the small étale site have enough injectives. They are defined
for every `p : ℕ`; the source reserves the name *higher direct images* for the family with
`p ≥ 1`, the degree-zero functor being `f_*` itself.

## References

* [Stacks Project, Tag 03PY](https://stacks.math.columbia.edu/tag/03PY)
* [Stacks Project, Tag 04I2](https://stacks.math.columbia.edu/tag/04I2)
* [Stacks Project, Tag 03PX](https://stacks.math.columbia.edu/tag/03PX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The direct image, or pushforward, `f_*` along `f : X ⟶ Y`** on sheaves of sets of the
small étale sites: the sheaf `f_* F` on `Y_étale` sends an étale `Y`-scheme `V` to `F(V ×_Y X)`,
that is, `f_*` is precomposition with base change along `f`. -/
@[stacks 03PY, sga "4½ Arcata 2.3" "f_* definition", sga "4 VII 1.4"]
abbrev smallEtaleDirectImage :
    Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)) ⥤
      Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v)) :=
  (smallEtaleBaseChange f).sheafPushforwardContinuous
    (Type (max (u + 1) v)) (smallEtaleTopology Y) (smallEtaleTopology X)

/-- The sections of `f_* F` over an étale `Y`-scheme `V` are the sections of `F` over the base
change `V ×_Y X`. -/
theorem smallEtaleDirectImage_obj_obj
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) (V : Y.Etale) :
    ((smallEtaleDirectImage.{u, v} f).obj F).obj.obj (op V) =
      F.obj.obj (op ((smallEtaleBaseChange f).obj V)) :=
  rfl

/-- **The higher direct images `R^p f_*` along `f : X ⟶ Y`**: the right derived functors of the
direct image `f_* : Ab(X_étale) ⥤ Ab(Y_étale)` on abelian sheaves of the small étale sites. The
family with `p ≥ 1` is what the source calls the higher direct images. -/
@[stacks 04I2,
  sga "4½ Arcata 2.3" "R^p f_* definition",
  sga "4½ Arcata 2.3.3" "higher direct images"]
abbrev etaleAbelianHigherDirectImage (p : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  (etaleAbelianDirectImage.{u, v} f).rightDerived p

/-- The higher direct images of an injective abelian sheaf on the small étale site vanish in
positive degrees: an injective object is its own injective resolution. -/
theorem isZero_etaleAbelianHigherDirectImage_injective_succ (p : ℕ)
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) [Injective I] :
    IsZero ((etaleAbelianHigherDirectImage.{u, v} f (p + 1)).obj I) :=
  Functor.isZero_rightDerived_obj_injective_succ _ _ _

end Stacks.EtaleCohomology

end
