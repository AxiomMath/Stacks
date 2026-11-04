module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Morphisms of big Zariski topoi

A morphism `f : T ⟶ S` in a big Zariski site induces a functor from the big Zariski category
over `T` to the one over `S`, by composing structure morphisms with `f`. This functor is
cocontinuous, and it has a continuous right adjoint given by base change along `f`. The two
functors determine the *same* morphism from the big Zariski topos of `T` to that of `S`, so
that morphism can be described from either side:

* inverse image is restriction along composition, `f⁻¹(G)(U / T) ≅ G(U / S)`;
* direct image is restriction along base change, `f_*(F)(U / S) ≅ F(U ×_S T / T)`.

Since composition with `f` preserves fibre products and equalizers, the inverse image also
has a left adjoint `f_!`, itself left exact.

## Main definitions

* `CategoryTheory.Over.map` — composition with `f`.
* `CategoryTheory.Over.pullback` — its base-change right adjoint.
* `AlgebraicGeometry.bigZariskiMorphism` — the induced morphism of big Zariski topoi.

## Main results

* `AlgebraicGeometry.bigZariskiOver_topology_eq` — the slice topology is the localized
  topology, which is what makes the general slice machinery applicable.
* `AlgebraicGeometry.bigZariskiMap_isCocontinuous`,
  `AlgebraicGeometry.bigZariskiMap_isContinuous` and
  `AlgebraicGeometry.bigZariskiPullback_isContinuous` — the continuity properties of
  composition and of base change.
* `AlgebraicGeometry.bigZariskiLowerShriekAdjunction` — the lower shriek, with the two
  preservation instances giving its left exactness.

## Implementation notes

The big Zariski category over a scheme is a slice category, so composition, base change and
their adjunction are Mathlib's `Over.map`, `Over.pullback` and `Over.mapPullbackAdj`, and are
referenced rather than redefined. Identifying the slice topology with the localized topology
goes through two descriptions of the precoverages as `Precoverage.comap`: the big site's
precoverage is the Zariski pretopology of all schemes comapped along its inclusion, and the
slice's is the site's comapped along the slice forgetful functor. Stability under base change
is then inherited rather than reproved.

The formulas on sections are the general natural isomorphisms with restriction functors,
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous` and
`CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso`, which retain naturality in both
the sheaf and the object; the second of them also expresses that the two descriptions of the
morphism of topoi agree, following the treatment of morphisms of topoi elsewhere in the
library. Closure of the size-bounded category under fibre products supplies the base-change
functor.

## References

* [Stacks Project, Lemma 34.3.7 (Tag 0210)](https://stacks.math.columbia.edu/tag/0210)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 0210 "the postcomposition functor" CategoryTheory.Over.map
add_to_stacks 0210 "the base-change functor" CategoryTheory.Over.pullback
add_to_stacks 0210 "the base-change adjunction" CategoryTheory.Over.mapPullbackAdj
add_to_stacks 0210 "the inverse-image formula"
  CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous
add_to_stacks 0210 "the direct-image formula and agreement of morphisms"
  CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso

/-- The topology of the big Zariski category over `S` is the localization of the site's
topology at `S`. -/
public theorem bigZariskiOver_topology_eq
    (B : BigZariskiSite.{u}) (S : B.Schemes) :
    BigZariskiOver.topology B S.1 S.property =
      B.grothendieckTopology.over (⟨S.1, S.property⟩ : B.Schemes) := by
  show (BigZariskiOver.precoverage B S.1 S.property).toGrothendieck =
    (B.precoverage.toGrothendieck).over (⟨S.1, S.property⟩ : B.Schemes)
  let : B.precoverage.IsStableUnderBaseChange := bigZariskiPrecoverage_stableUnderBaseChange B
  rw [bigZariskiOver_precoverage_eq_comap B S]
  exact (over_toGrothendieck_eq_toGrothendieck_comap_forget
    B.precoverage (⟨S.1, S.property⟩ : B.Schemes)).symm

variable (B : BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S)

include f

/-- **Stacks 0210.** Postcomposition with `f` is cocontinuous for the big Zariski
topologies. -/
@[stacks 0210 "cocontinuity"]
public instance bigZariskiMap_isCocontinuous :
    (Over.map f).IsCocontinuous
      (BigZariskiOver.topology B T.1 T.property)
      (BigZariskiOver.topology B S.1 S.property) := by
  rw [bigZariskiOver_topology_eq B T, bigZariskiOver_topology_eq B S]
  infer_instance

/-- **Stacks 0210.** Postcomposition with `f` is continuous as well. This is the continuity
used to identify inverse image with restriction and to construct the lower shriek. -/
@[stacks 0210 "continuity"]
public instance bigZariskiMap_isContinuous :
    (Over.map f).IsContinuous
      (BigZariskiOver.topology B T.1 T.property)
      (BigZariskiOver.topology B S.1 S.property) := by
  rw [bigZariskiOver_topology_eq B T, bigZariskiOver_topology_eq B S]
  infer_instance

/-- **Stacks 0210.** Base change along `f`, sending `U / S` to the canonical fibre product
`U ×_S T / T`, is continuous. -/
@[stacks 0210 "continuity of the base-change right adjoint"]
public instance bigZariskiPullback_isContinuous :
    (Over.pullback f).IsContinuous
      (BigZariskiOver.topology B S.1 S.property)
      (BigZariskiOver.topology B T.1 T.property) := by
  rw [bigZariskiOver_topology_eq B S, bigZariskiOver_topology_eq B T]
  infer_instance

/-- **Stacks 0210.** The morphism of big Zariski topoi induced by postcomposition. -/
@[stacks 0210 "the morphism of topoi"]
public noncomputable def bigZariskiMorphism :
    MorphismOfTopoi
      (Sheaf (BigZariskiOver.topology B T.1 T.property) (Type (u + 1)))
      (Sheaf (BigZariskiOver.topology B S.1 S.property) (Type (u + 1))) :=
  { pushforward := (Over.map f).sheafPushforwardCocontinuous
      (Type (u + 1)) (BigZariskiOver.topology B T.1 T.property)
      (BigZariskiOver.topology B S.1 S.property)
    inverseImage := (Over.map f).sheafPullbackCocontinuous
      (Type (u + 1)) (BigZariskiOver.topology B T.1 T.property)
      (BigZariskiOver.topology B S.1 S.property)
    adj := (Over.map f).sheafAdjunctionPullbackCocontinuous
      (Type (u + 1)) (BigZariskiOver.topology B T.1 T.property)
      (BigZariskiOver.topology B S.1 S.property)
    preservesFiniteLimits := by infer_instance }

/-- **Stacks 0210.** The sheaf pullback along postcomposition is the lower shriek, left
adjoint to inverse image. -/
@[stacks 0210 "existence of lower shriek"]
public noncomputable def bigZariskiLowerShriekAdjunction :
    (Over.map f).sheafPullback (Type (u + 1))
      (BigZariskiOver.topology B T.1 T.property)
      (BigZariskiOver.topology B S.1 S.property) ⊣
        (bigZariskiMorphism B T S f).inverseImage :=
  (((Over.map f).sheafAdjunctionLowerShriek (Type (u + 1))
      (BigZariskiOver.topology B T.1 T.property)
      (BigZariskiOver.topology B S.1 S.property)).ofNatIsoLeft
      (Functor.sheafPullbackConstruction.sheafPullbackIso (Over.map f)
        (Type (u + 1)) (BigZariskiOver.topology B T.1 T.property)
        (BigZariskiOver.topology B S.1 S.property)).symm).ofNatIsoRight
    ((Over.map f).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      (Type (u + 1)) (BigZariskiOver.topology B T.1 T.property)
      (BigZariskiOver.topology B S.1 S.property)).symm

/-- **Stacks 0210.** The lower shriek commutes with fibre products. -/
@[stacks 0210 "lower shriek preserves fibre products"]
public instance bigZariskiLowerShriek_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      ((Over.map f).sheafPullback (Type (u + 1))
        (BigZariskiOver.topology B T.1 T.property)
        (BigZariskiOver.topology B S.1 S.property)) := by
  let : HasEqualizers (Over T) := bigZariskiOver_hasEqualizers B T
  let : HasEqualizers (Over S) := bigZariskiOver_hasEqualizers B S
  let : PreservesLimitsOfShape WalkingCospan (Over.map f) :=
    overMap_preservesLimitsOfShape_of_isConnected (f := f)
  exact Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (BigZariskiOver.topology B T.1 T.property)
    (BigZariskiOver.topology B S.1 S.property) (I := WalkingCospan)

/-- **Stacks 0210.** The lower shriek commutes with equalizers. -/
@[stacks 0210 "lower shriek preserves equalizers"]
public instance bigZariskiLowerShriek_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.map f).sheafPullback (Type (u + 1))
        (BigZariskiOver.topology B T.1 T.property)
        (BigZariskiOver.topology B S.1 S.property)) := by
  let : HasEqualizers (Over T) := bigZariskiOver_hasEqualizers B T
  let : HasEqualizers (Over S) := bigZariskiOver_hasEqualizers B S
  let : PreservesLimitsOfShape WalkingParallelPair (Over.map f) :=
    overMap_preservesLimitsOfShape_of_isConnected (f := f)
  exact Functor.preservesLimitsOfShape_sheafPullback (Over.map f)
    (BigZariskiOver.topology B T.1 T.property)
    (BigZariskiOver.topology B S.1 S.property) (I := WalkingParallelPair)

end AlgebraicGeometry

end
