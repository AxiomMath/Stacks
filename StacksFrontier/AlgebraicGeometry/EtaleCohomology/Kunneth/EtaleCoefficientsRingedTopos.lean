module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The small étale ringed topos with constant coefficients

Let `X` be a scheme and `Λ` a commutative ring. Sheaves of `Λ`-modules on `X_étale` are the
modules over the constant sheaf of rings `Λ̲` on the small étale site. This file realises the
ringed topos `(X_étale, Λ̲)` as a `RingedTopos.{u + 1, u + 1, u + 1}` whose site is *small*, and
a morphism of schemes `f : X ⟶ Y` as a morphism of ringed topoi `(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)`.

## Implementation notes

For `X : Scheme.{u}` the small étale site `X.Etale` has its objects in `Type (u + 1)` and its
morphisms in `Type u`, and it is essentially small at `u + 1`. Its small model
`SmallModel.{u + 1} X.Etale`, with the induced topology, is a site whose objects, morphisms and
ring sections share one universe, and its sheaves with values in any category are those of
`X_étale` (`sheafEquiv`).

## Main definitions

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `Site X`, `toEtale X`, `topology X` — the small model of `X_étale`, its comparison functor to
  `X.Etale`, and the induced topology.
* `sheafEquiv X A` — restriction along the comparison, an equivalence
  `Sheaf (smallEtaleTopology X) A ≌ Sheaf (topology X) A`.
* `baseChange f` — base change along `f : X ⟶ Y` read on the small models.
* `ringedTopos X Λ` — **the ringed topos `(X_étale, Λ̲)`**.
* `ringedToposHom f Λ` — **the morphism of ringed topoi `(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)`**. Its
  structure map `Λ̲ ⟶ f_*Λ̲` is the one induced by the unit of the sheafification of the
  constant presheaf.
* `baseChangeComp f g` — base change along `f ≫ g` is base change along `g` followed by base
  change along `f`, on the small models.

## Main results

* `isMorphismOfSites_baseChange` — base change on the small models is a morphism of sites,
  Stacks 00X1: it is continuous, and its pullback on sheaves of sets is exact.
* `isMorphismOfSites_ringedToposHom` — the morphism of ringed topoi of a morphism of schemes is a
  morphism of sites.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 00X5](https://stacks.math.columbia.edu/tag/00X5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe t₂ t₁ u

namespace Stacks.EtaleCohomology.EtaleCoefficients

/-! ### The small model of the small étale site -/

section Site

variable (X : Scheme.{u})

/-- **The small model of the small étale site of `X`**: a category whose objects and morphisms
both lie in `Type (u + 1)`, equivalent to `X.Etale`. -/
def Site : Type (u + 1) := SmallModel.{u + 1} X.Etale

/-- The small model is a small category at `u + 1`. -/
instance : SmallCategory.{u + 1} (Site X) :=
  inferInstanceAs (SmallCategory (SmallModel.{u + 1} X.Etale))

/-- The equivalence between the small étale site and its small model. -/
def equiv : X.Etale ≌ Site X := equivSmallModel.{u + 1} X.Etale

/-- The comparison of the small model with the small étale site. -/
abbrev toEtale : Site X ⥤ X.Etale := (equiv X).inverse

/-- The comparison of the small étale site with its small model. -/
abbrev fromEtale : X.Etale ⥤ Site X := (equiv X).functor

/-- The étale topology on the small model: the topology induced by the comparison. -/
abbrev topology : GrothendieckTopology (Site X) :=
  (toEtale X).inducedTopology (smallEtaleTopology X)

/-- **The small model carries the sheaves of the small étale site**, with values in an arbitrary
category: restriction along the comparison is an equivalence. -/
def sheafEquiv (A : Type t₁) [Category.{t₂} A] :
    Sheaf (smallEtaleTopology X) A ≌ Sheaf (topology X) A :=
  (equiv X).sheafCongr (smallEtaleTopology X) (topology X) A

/-- The comparison of the small étale site with its small model is continuous. -/
instance isContinuous_fromEtale :
    (fromEtale X).IsContinuous (smallEtaleTopology X) (topology X) :=
  inferInstance

/-- The comparison of the small model with the small étale site is continuous. -/
instance isContinuous_toEtale :
    (toEtale X).IsContinuous (topology X) (smallEtaleTopology X) :=
  inferInstance

end Site

/-! ### Base change on the small models -/

section BaseChange

variable {X Y Z : Scheme.{u}}

/-- **Base change along `f : X ⟶ Y`, read on the small models**: the comparison to `Y.Etale`,
base change `smallEtaleBaseChange f`, and the comparison back to the small model of `X`. -/
abbrev baseChange (f : X ⟶ Y) : Site Y ⥤ Site X :=
  toEtale Y ⋙ smallEtaleBaseChange f ⋙ fromEtale X

/-- Base change on the small models is continuous. -/
instance isContinuous_baseChange (f : X ⟶ Y) :
    (baseChange f).IsContinuous (topology Y) (topology X) :=
  have : (smallEtaleBaseChange f ⋙ fromEtale X).IsContinuous (smallEtaleTopology Y)
      (topology X) :=
    Functor.isContinuous_comp _ _ _ (smallEtaleTopology X) _
  Functor.isContinuous_comp _ _ _ (smallEtaleTopology Y) _

/-- Base change on the small models is representably flat. -/
instance representablyFlat_baseChange (f : X ⟶ Y) : RepresentablyFlat (baseChange f) :=
  inferInstance

/-- **Base change on the small models is a morphism of sites** (Stacks 00X1): it is continuous,
and its pullback on sheaves of sets is exact. -/
theorem isMorphismOfSites_baseChange (f : X ⟶ Y) :
    (baseChange f).IsMorphismOfSites (topology Y) (topology X) :=
  Functor.isMorphismOfSites_of_representablyFlat _ _ _

/-- **Base change along a composite**, on the small models: base change along `f ≫ g` is base
change along `g` followed by base change along `f`. It is the associativity isomorphism of
fibre products of `smallEtaleBaseChangeComp`, with the unit of the comparison with the small
model of `Y` inserted in the middle. -/
def baseChangeComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f :=
  Functor.isoWhiskerLeft (toEtale Z)
      (Functor.isoWhiskerRight (smallEtaleBaseChangeComp f g) (fromEtale X)) ≪≫
    Functor.isoWhiskerLeft (toEtale Z ⋙ smallEtaleBaseChange g)
      (Functor.isoWhiskerRight (equiv Y).unitIso
        (smallEtaleBaseChange f ⋙ fromEtale X))

end BaseChange

/-! ### The constant ringed topos and the morphism of a morphism of schemes -/

section Ringed

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The small étale ringed topos `(X_étale, Λ̲)` with constant coefficients `Λ`**, on the small
model of the small étale site: its structure sheaf is the constant sheaf of commutative rings
on `Λ`, the sheafification of the constant presheaf. -/
abbrev ringedTopos (X : Scheme.{u}) : RingedTopos.{u + 1, u + 1, u + 1} where
  C := Site X
  J := topology X
  O := (constantSheaf (topology X) CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

variable {X Y : Scheme.{u}}

/-- The structure map `Λ̲ ⟶ f_*Λ̲` of the morphism of ringed topoi of `f`: through the
adjunction between sheafification and the inclusion of sheaves, the map of presheaves which is,
over `V`, the sheafification unit `Λ ⟶ Λ̲(f⁻¹V)` of the constant presheaf on `X`. -/
def structureMap (f : X ⟶ Y) :
    (ringedTopos Λ Y).O ⟶
      ((baseChange f).sheafPushforwardContinuous CommRingCat.{u + 1} (topology Y)
        (topology X)).obj (ringedTopos Λ X).O :=
  ((sheafificationAdjunction (topology Y) CommRingCat.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft (baseChange f).op
      (toSheafify (topology X) ((Functor.const _).obj (CommRingCat.of Λ))))

/-- **The morphism of ringed topoi `(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)` of a morphism of schemes
`f : X ⟶ Y`**, on the small models: base change of étale schemes over `Y` along `f`, with the
structure map `structureMap`. -/
abbrev ringedToposHom (f : X ⟶ Y) : RingedToposSiteHom (ringedTopos Λ X) (ringedTopos Λ Y) where
  u := baseChange f
  isContinuous := inferInstanceAs ((baseChange f).IsContinuous (topology Y) (topology X))
  fSharp := structureMap Λ f

/-- The underlying functor of the morphism of ringed topoi of `f` is base change. -/
@[simp]
theorem ringedToposHom_u (f : X ⟶ Y) : (ringedToposHom Λ f).u = baseChange f := rfl

/-- **The morphism of ringed topoi of a morphism of schemes is a morphism of sites.** -/
theorem isMorphismOfSites_ringedToposHom (f : X ⟶ Y) :
    (ringedToposHom Λ f).u.IsMorphismOfSites (ringedTopos Λ Y).J (ringedTopos Λ X).J :=
  isMorphismOfSites_baseChange f

end Ringed

end Stacks.EtaleCohomology.EtaleCoefficients

end
