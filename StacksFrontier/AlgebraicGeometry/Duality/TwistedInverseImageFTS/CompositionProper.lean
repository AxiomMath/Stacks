module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition

/-!
# The upper shriek of a composite whose first factor is proper

Let `S` be a Noetherian scheme and `f : X ⟶ Y`, `g : Y ⟶ Z` morphisms of `FTS S` with `f`
proper. For compactifications `cg` of `g` and `cfg` of `f ≫ g`, and `K` in `D⁺_QCoh(𝒪_Z)`,

  `(f ≫ g)^! K ≅ f^!(g^! K)`,

with `f^!` computed at the identity compactification of the proper morphism `f`, that is
`f^! = a_f` the right adjoint of `Rf_*` (`Stacks.Duality.upperShriekProperIso`). This is a case
of [Stacks, Tag 0ATX].

## Main results

* `Stacks.Duality.CompCompactification.upperShriekCompProperObjIso`: `(f ≫ g)^! K ≅ f^!(g^! K)`.
* `Stacks.Duality.CompCompactification.upperShriekCompProperTwistedObjIso`: the same with `f^!`
  written as the twisted inverse image `a_f`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality.CompCompactification

open DominatingCompactification

variable {S : Scheme.{u}} [IsNoetherian S] {X Y Z : FTS S}
  (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f.left] (cg : CompactificationOf (Over.mk g.left))
  (cfg : CompactificationOf (Over.mk (f ≫ g).left))

/-- **`(f ≫ g)^! K ≅ f^!(g^! K)` for `f` proper and `K` bounded below**, with `f^!` at the identity
compactification of `f` and `g^!`, `(f ≫ g)^!` at arbitrary compactifications. -/
def upperShriekCompProperObjIso (K : quasiCoherentDerivedCategory Z.left)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    (upperShriek (f ≫ g) cfg).obj K ≅
      (upperShriek f (properCompactification f)).obj ((upperShriek g cg).obj K) :=
  haveI hgK := isBoundedBelow_upperShriek_obj g cg K hK
  haveI : IsIso ((restrictionMapFst (f ≫ g) cfg (compactification f g cg cfg)).app
      ((twistedInverseImage cfg.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs cfg.toBase)).obj K)) :=
    isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _
      (isPullback_fst (f ≫ g) cfg (compactification f g cg cfg)) _
      (isBoundedBelow_twistedInverseImage_obj _ _ hK)
  haveI : IsIso ((restrictionMapSnd (f ≫ g) cfg (compactification f g cg cfg)).app
      ((twistedInverseImage (compactification f g cg cfg).toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) :=
    isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _
      (isPullback_snd (f ≫ g) cfg (compactification f g cg cfg)) _
      (isBoundedBelow_twistedInverseImage_obj _ _ hK)
  haveI : IsIso ((restrictionMap f g cg cfg).app ((twistedInverseImage cg.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs cg.toBase)).obj K)) :=
    isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _
      (IsPullback.of_hasPullback _ _) _ (isBoundedBelow_twistedInverseImage_obj _ _ hK)
  haveI : IsIso ((restrictionMapFst f (restrictCompactification f g cg cfg)
      (properCompactification f)).app
      ((twistedInverseImage (restrictCompactification f g cg cfg).toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          ((upperShriek g cg).obj K))) :=
    isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _
      (isPullback_fst f (restrictCompactification f g cg cfg) (properCompactification f)) _
      (isBoundedBelow_twistedInverseImage_obj _ _ hgK)
  haveI : IsIso ((restrictionMapSnd f (restrictCompactification f g cg cfg)
      (properCompactification f)).app
      ((twistedInverseImage (properCompactification f).toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          ((upperShriek g cg).obj K))) :=
    isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _
      (isPullback_snd f (restrictCompactification f g cg cfg) (properCompactification f)) _
      (isBoundedBelow_twistedInverseImage_obj _ _ hgK)
  upperShriekCompObjIsoOfIsIso f g cg cfg (properCompactification f) K

/-- **`(f ≫ g)^! K ≅ a_f(g^! K)` for `f` proper and `K` bounded below**, where `a_f` is the right
adjoint of `Rf_*` ([Stacks, Tag 0A9E]): `upperShriekCompProperObjIso` followed by
`Stacks.Duality.upperShriekProperIso`. -/
def upperShriekCompProperTwistedObjIso (K : quasiCoherentDerivedCategory Z.left)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    (upperShriek (f ≫ g) cfg).obj K ≅
      (twistedInverseImage f.left (isQuasicoherent_homology_derivedPushforward_of_qcqs f.left)).obj
        ((upperShriek g cg).obj K) :=
  upperShriekCompProperObjIso f g cg cfg K hK ≪≫ (upperShriekProperIso f).app _

end Stacks.Duality.CompCompactification

end
