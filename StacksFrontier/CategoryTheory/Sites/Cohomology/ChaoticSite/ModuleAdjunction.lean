module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackContinuousUnivLE
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.LowerShriekAsAColimit
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Category.ULift
import StacksCore.Tactic.StacksAttribute

/-! # Lower shriek of modules along the point of a chaotic site

Let `C` carry the chaotic topology, let `p : C ⥤ *` be the unique functor to the one-object
category and let `R` be a sheaf of rings on the chaotic point. Restriction of sheaves of
`R`-modules along `p` — the functor `p^*`, which is `SheafOfModules.pushforward` for the
identity map of the constant sheaf of rings `p^{-1} R` — has a left adjoint `p_!`, with the
universes of `C`, of its morphisms, of the sheaf of rings and of the module sections
independent.

The second half of the file does the same for the *lifted presentation* of a chaotic site, in
which an arbitrary category `C : Type u` with `Category.{v} C` and a ring `B : Type w` are
replaced by `AsSmall C` and `ULift B` in one common universe. That is the presentation Stacks
08Q6 works in, and it is where `p_!` of a module sheaf becomes writable.

## Main definitions

* `Stacks.ChaoticSite.pointInverseImageRing`: the constant sheaf of rings `p^{-1} R` on `C`,
  that is, the restriction of `R` along the point functor.
* `Stacks.ChaoticSite.LiftedPresentation.constantRing`: the constant sheaf of rings at a ring
  on a chaotic site.
* `Stacks.ChaoticSite.LiftedPresentation.pointLowerShriek` and `.pointRestriction`: `p_!` and
  `p^*` between sheaves of modules on the lifted site and on the lifted point.

## Main results

* `Stacks.ChaoticSite.presheafPointModule_isRightAdjoint` and
  `Stacks.ChaoticSite.pointModule_isRightAdjoint`: restriction of presheaves, respectively
  sheaves, of modules along the point functor has a left adjoint.
* `Stacks.ChaoticSite.pointModuleAdjunction`: the resulting adjunction `p_! ⊣ p^*`, with no
  adjointness hypothesis.
* `Stacks.ChaoticSite.LiftedPresentation.pointRestriction_isRightAdjoint` and
  `.pointLowerShriekAdjunction`: the same two statements at the constant-ring spelling of the
  lifted presentation.

## Implementation notes

The mathematical content is `PresheafOfModules.isRightAdjoint_pushforward_of_univLE` together
with Mathlib's sheafification construction on top of it; nothing new is proved. What is new is
the **shape**, and the shape is the whole obstruction. Mathlib's own instance for
`(SheafOfModules.pushforward φ).IsRightAdjoint` is stated for two sites that are small in the
universe of the module sections, and the point of a chaotic site is never of that form: for
`C : Type u` the point is `Discrete PUnit.{u + 1}`, one universe up. So the univLE
generalisation is what makes the instance available here at all.

Even with it available, instance *search* does not find it at the spelling the tagged statements
use. Both
Stacks 08PF's module half and Stacks 08Q6 write the structure map of `p^*` as `𝟙 (p^{-1} R)`,
and the implicit sheaves of rings of `SheafOfModules.pushforward` would then have to be read
off that identity: the goal is `pushforward (𝟙 (p^{-1} R))` while the available conclusion is
`pushforward φ` for `φ : ?S ⟶ (p.sheafPushforwardContinuous RingCat _ _).obj ?R`, and a
projection applied to a metavariable has no unifier. The instances below therefore *restate*
the result with `R` and `S` given explicitly and the identity type-ascribed, which pins them;
`Stacks.Sites.ExtensionByZero.presheafRestrictionIsRightAdjoint_of_univLE` performs exactly the
same step for `Over.forget U`, for the same reason.

**The restatement has to be redone per spelling of the constant ring sheaf.**
`pointRestriction_isRightAdjoint` below is *not* derived from
`pointModule_isRightAdjoint`: the two differ by `constantRing (liftedSite C B) (LiftedRing C B)`
against `(Functor.star _).sheafPushforwardContinuous _ _ _ |>.obj (pointRing C B)`, which are
equal by `rfl` — `constantRing_eq_pointInverseImageRing` records that — but only at default
transparency, while instance search runs below it. Supplying the general instance as a local
`have` does not help either, and neither does making `constantRing` an `abbrev`, because
`Functor.sheafPushforwardContinuous` is a semireducible Mathlib `def` and will not unfold.
What works is applying the presheaf-level theorem again at the new spelling, which is what the
lifted section does.

`GrothendieckTopology.WEqualsLocallyBijective` on the point is carried as an instance
hypothesis in the general section rather than derived. Mathlib's instance for it asks the values
to lie in the universe `max u v` of the site, and the point's universe is `u + 1`, so it does
not fire at an arbitrary module universe. It *is* found by search in the lifted presentation,
where the site's object universe has been made equal to the module universe, so nothing is
narrowed by carrying it. Sheafification itself needs no hypothesis: every presheaf is a sheaf
for the chaotic topology, which is `trivialHasSheafify`.

Additivity of `p_!` is taken from the adjunction — a left adjoint of an additive functor is
additive — rather than from preservation of binary biproducts. The latter route
needs the file-level
`backward.isDefEq.respectTransparency` option, because `PreservesZeroMorphisms` for `p_!` is
not found by search at these spellings.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ChaoticSite

universe m v r w u

section PointModules

variable (C : Type u) [Category.{w} C]
  (R : Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 1})) RingCat.{r})

/-- The constant sheaf of rings `p^{-1} R` on a chaotic site: the restriction along the point
functor of a sheaf of rings `R` on the chaotic point. -/
abbrev pointInverseImageRing : Sheaf (GrothendieckTopology.trivial C) RingCat.{r} :=
  ((Functor.star C).sheafPushforwardContinuous RingCat.{r}
    (GrothendieckTopology.trivial C)
    (GrothendieckTopology.trivial (Discrete PUnit.{u + 1}))).obj R

variable [UnivLE.{r, v}] [UnivLE.{w, v}] [UnivLE.{u, v}]

/-- **Restriction of presheaves of modules along the point functor of a chaotic site has a left
adjoint**, with the universes of the site, of its morphisms, of the sheaf of rings and of the
module sections independent. Stated with the structure map spelled as the identity of
`p^{-1} R`, which is the form Stacks 08PF's module half and Stacks 08Q6 ask for; see the
implementation notes for why the restatement is needed. -/
@[sga "4 Vbis 1.3.7" "special case"]
instance presheafPointModule_isRightAdjoint :
    (PresheafOfModules.pushforward.{v} (F := Functor.star C) (R := R.obj)
      (S := (pointInverseImageRing C R).obj)
      (𝟙 (pointInverseImageRing C R) :
        pointInverseImageRing C R ⟶ pointInverseImageRing C R).hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{v}
    (F := Functor.star C) (R := R.obj) (S := (pointInverseImageRing C R).obj)
    (𝟙 (pointInverseImageRing C R) :
      pointInverseImageRing C R ⟶ pointInverseImageRing C R).hom

variable [(GrothendieckTopology.trivial (Discrete PUnit.{u + 1})).WEqualsLocallyBijective
  AddCommGrpCat.{v}]

/-- **Restriction of sheaves of modules along the point functor of a chaotic site has a left
adjoint**, namely lower shriek, with the universes of the site, of its morphisms, of the sheaf
of rings and of the module sections independent. -/
@[sga "4 Vbis 1.3.7" "special case"]
instance pointModule_isRightAdjoint :
    (SheafOfModules.pushforward.{v} (F := Functor.star C) (R := R)
      (S := pointInverseImageRing C R)
      (𝟙 (pointInverseImageRing C R) :
        pointInverseImageRing C R ⟶ pointInverseImageRing C R)).IsRightAdjoint :=
  have := presheafPointModule_isRightAdjoint.{v} C R
  (SheafOfModules.PullbackConstruction.adjunction.{v} (F := Functor.star C) (R := R)
    (S := pointInverseImageRing C R)
    (𝟙 (pointInverseImageRing C R) :
      pointInverseImageRing C R ⟶ pointInverseImageRing C R)).isRightAdjoint

/-- **Stacks 03D7 at the point of a chaotic site**: lower shriek of sheaves of modules along
the point functor is left adjoint to restriction, at independent universes. The adjunction
supplies the natural bijection between morphisms out of `p_! M` and morphisms into `p^* N`. -/
@[stacks 03D7 "chaotic site over its point, at independent universes"]
def pointModuleAdjunction :
    SheafOfModules.pullback.{v} (F := Functor.star C) (R := R)
        (S := pointInverseImageRing C R)
        (𝟙 (pointInverseImageRing C R) :
          pointInverseImageRing C R ⟶ pointInverseImageRing C R) ⊣
      SheafOfModules.pushforward.{v} (F := Functor.star C) (R := R)
        (S := pointInverseImageRing C R)
        (𝟙 (pointInverseImageRing C R) :
          pointInverseImageRing C R ⟶ pointInverseImageRing C R) :=
  SheafOfModules.pullbackPushforwardAdjunction.{v} (F := Functor.star C) (R := R)
    (S := pointInverseImageRing C R)
    (𝟙 (pointInverseImageRing C R) :
      pointInverseImageRing C R ⟶ pointInverseImageRing C R)

end PointModules

/-! ## The lifted presentation of a chaotic site -/

namespace LiftedPresentation

/-- The constant sheaf of rings at a ring `B` on a chaotic site: every presheaf is a sheaf for
the chaotic topology, so this is the constant presheaf at `B`. -/
def constantRing (C : Type u) [Category.{w} C] (B : Type r) [Ring B] :
    Sheaf (GrothendieckTopology.trivial C) RingCat.{r} :=
  (sheafBotEquivalence RingCat.{r}).inverse.obj ((Functor.const Cᵒᵖ).obj (RingCat.of B))

/-- A small presentation of the site in the common universe. -/
abbrev LiftedSite (C : Type u) [Category.{w} C] (_ : Type r) := AsSmall.{max m r} C

/-- The coefficient ring lifted to the common universe. -/
abbrev LiftedRing (C : Type u) [Category.{w} C] (B : Type r) := ULift.{max m r u w} B

variable (C : Type u) [Category.{w} C] (B : Type r) [Ring B]

/-- The constant structure sheaf on the lifted chaotic point. -/
abbrev pointRing :=
  constantRing (Discrete PUnit.{max m r u w + 1}) (LiftedRing.{m} C B)

/-- The constant structure sheaf on the lifted chaotic site. -/
abbrev siteRing := constantRing (LiftedSite.{m} C B) (LiftedRing.{m} C B)

/-- The constant sheaf of rings on the lifted site **is** the restriction of the one on the
lifted point along the point functor, on the nose. The two spellings agree only at default
transparency, which is why the instances below are reproved rather than transported; see the
implementation notes. -/
theorem constantRing_eq_pointInverseImageRing :
    siteRing.{m} C B = pointInverseImageRing (LiftedSite.{m} C B) (pointRing.{m} C B) := rfl

/-- **Restriction of presheaves of modules along the point functor of the lifted chaotic site
has a left adjoint**, at the constant-ring spelling. -/
instance presheafPointRestriction_isRightAdjoint :
    (PresheafOfModules.pushforward.{max m r u w} (F := Functor.star (LiftedSite.{m} C B))
      (R := (pointRing.{m} C B).obj) (S := (siteRing.{m} C B).obj)
      (𝟙 (siteRing.{m} C B) : siteRing.{m} C B ⟶ siteRing.{m} C B).hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{max m r u w}
    (F := Functor.star (LiftedSite.{m} C B))
    (R := (pointRing.{m} C B).obj) (S := (siteRing.{m} C B).obj)
    (𝟙 (siteRing.{m} C B) : siteRing.{m} C B ⟶ siteRing.{m} C B).hom

/-- **Restriction of sheaves of modules along the point functor of the lifted chaotic site has
a left adjoint**, at the constant-ring spelling. This is the instance that
`SheafOfModules.pullback` needs before the lower shriek of Stacks 08Q6 can be written down. -/
instance pointRestriction_isRightAdjoint :
    (SheafOfModules.pushforward.{max m r u w} (F := Functor.star (LiftedSite.{m} C B))
      (R := pointRing.{m} C B) (S := siteRing.{m} C B)
      (𝟙 (siteRing.{m} C B) : siteRing.{m} C B ⟶ siteRing.{m} C B)).IsRightAdjoint :=
  have := presheafPointRestriction_isRightAdjoint.{m} C B
  (SheafOfModules.PullbackConstruction.adjunction.{max m r u w}
    (F := Functor.star (LiftedSite.{m} C B))
    (R := pointRing.{m} C B) (S := siteRing.{m} C B)
    (𝟙 (siteRing.{m} C B) : siteRing.{m} C B ⟶ siteRing.{m} C B)).isRightAdjoint

/-- Lower shriek `p_!` from module sheaves on the lifted site to module sheaves on the lifted
point: the left adjoint of restriction. -/
abbrev pointLowerShriek : SheafOfModules.{max m r u w} (siteRing.{m} C B) ⥤
    SheafOfModules.{max m r u w} (pointRing.{m} C B) :=
  SheafOfModules.pullback (F := Functor.star (LiftedSite.{m} C B)) (𝟙 (siteRing.{m} C B))

/-- Restriction `p^*` from the lifted chaotic point to the lifted chaotic site. -/
abbrev pointRestriction : SheafOfModules.{max m r u w} (pointRing.{m} C B) ⥤
    SheafOfModules.{max m r u w} (siteRing.{m} C B) :=
  SheafOfModules.pushforward (F := Functor.star (LiftedSite.{m} C B)) (𝟙 (siteRing.{m} C B))

/-- Restriction along the point functor is additive: it is computed on sections. -/
instance pointRestriction_additive : (pointRestriction.{m} C B).Additive where
  map_add {_ _ p q} := by
    ext V z
    rfl

/-- **The lower-shriek adjunction of Stacks 08Q6's lifted presentation**: `p_! ⊣ p^*`. -/
def pointLowerShriekAdjunction : pointLowerShriek.{m} C B ⊣ pointRestriction.{m} C B :=
  Adjunction.ofIsRightAdjoint (pointRestriction.{m} C B)

/-- Lower shriek is additive, being a left adjoint of an additive functor. -/
instance pointLowerShriek_additive : (pointLowerShriek.{m} C B).Additive :=
  (pointLowerShriekAdjunction.{m} C B).left_adjoint_additive

end LiftedPresentation

end Stacks.ChaoticSite

end
