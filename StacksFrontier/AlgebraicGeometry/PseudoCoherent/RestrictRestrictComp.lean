module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictRestrictUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Double restriction followed by the comparison is single restriction

Let `X` be a ringed space, let `U` be an open of `X` and let `D` be a pair of corresponding opens
(`AlgebraicGeometry.RingedSpace.CorrespondingOpens`): an open `W ≤ U` of `X` together with the
open `V` of `X|U` corresponding to it. Restricting `𝒪_X`-modules to `U`, then to `V`, and then
comparing along `Φ = AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare` is restricting
them to `W`:

`restrictModules X U ⋙ restrictModules (X|U) V ⋙ Φ ≅ restrictModules X W`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.doubleOpens` and
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleOpens` are the functors on opens that
  the two-fold and three-fold composites push forward along.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.doubleData` and
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleData` are the morphisms of sheaves of
  rings they push forward along.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleOpensIso` identifies the inclusion of
  the opens of `W` into the opens of `X` with `tripleOpens`.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleRestrictIso` is the compatibility
  isomorphism itself.

## Main results

* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.double_eq`,
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.triple_eq` and
  `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleRestrict_eq`: each of the composites is
  a *single* pushforward of sheaves of modules.
* `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleData_eq`: transporting `tripleData`
  along `tripleOpensIso` gives the identity of `𝒪_{X|W}`.

## References

* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] isContinuous_restrictOpensInclusion

/-- **Restriction to an open subspace is a pushforward of sheaves of modules**, along the
inclusion of the opens of the subspace into the opens of `X` and the identity of `𝒪_{X|U}`. -/
public theorem restrictModules_eq_pushforward (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    restrictModules X U = SheafOfModules.pushforward.{u} (F := restrictOpensInclusion X U)
      (𝟙 (structureSheafOfRings (X.restrict U.isOpenEmbedding))) :=
  rfl

namespace CorrespondingOpens

variable {X : RingedSpace.{u, u}} {U : Opens X.carrier} (D : CorrespondingOpens X U)

/-! ### Double restriction as a single pushforward -/

/-- `Z ↦ ι_U(ι_V Z)`, the functor `Opens V ⥤ Opens X` that the composite of the two restrictions
`(·)|_U` and `(·)|_V` pushes forward along. -/
public def doubleOpens : Opens (D.subspace).carrier ⥤ Opens X.carrier :=
  restrictOpensInclusion (X.restrict U.isOpenEmbedding) D.sub ⋙ restrictOpensInclusion X U

/-- `AlgebraicGeometry.RingedSpace.CorrespondingOpens.doubleOpens` is continuous for the
open-cover topologies, being a composite of two inclusions of opens of subspaces. -/
@[sga "4 III 1.9.2" "special case"]
public instance isContinuous_doubleOpens :
    (D.doubleOpens).IsContinuous
      (Opens.grothendieckTopology (D.subspace).carrier)
      (Opens.grothendieckTopology X.carrier) :=
  @Functor.isContinuous_comp _ _ _ _ _ _
    (restrictOpensInclusion (X.restrict U.isOpenEmbedding) D.sub) (restrictOpensInclusion X U)
    (Opens.grothendieckTopology (D.subspace).carrier)
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
    (Opens.grothendieckTopology X.carrier)
    (isContinuous_restrictOpensInclusion (X.restrict U.isOpenEmbedding) D.sub)
    (isContinuous_restrictOpensInclusion X U)

/-- The morphism of sheaves of rings on `V` that the composite of the two restrictions pushes
forward along: two identities, one of them pushed forward. -/
public def doubleData :
    structureSheafOfRings (D.subspace) ⟶
      ((D.doubleOpens).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (D.subspace).carrier)
        (Opens.grothendieckTopology X.carrier)).obj (structureSheafOfRings X) :=
  𝟙 (structureSheafOfRings (D.subspace)) ≫
    ((restrictOpensInclusion (X.restrict U.isOpenEmbedding) D.sub).sheafPushforwardContinuous
      RingCat.{u} (Opens.grothendieckTopology (D.subspace).carrier)
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)).map
      (𝟙 (structureSheafOfRings (X.restrict U.isOpenEmbedding)))

/-- **Restricting to `U` and then to `V` is one pushforward**, along
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.doubleOpens` and the datum
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.doubleData`. -/
public theorem double_eq :
    restrictModules X U ⋙ restrictModules (X.restrict U.isOpenEmbedding) D.sub =
      SheafOfModules.pushforward.{u} (F := D.doubleOpens) (D.doubleData) :=
  rfl

/-! ### The three-fold composite as a single pushforward -/

/-- `Z ↦ ι_U(ι_V(h⁻¹Z))`, the functor `Opens W ⥤ Opens X` that the composite of the two
restrictions with the comparison pushes forward along. -/
public def tripleOpens : Opens (D.basespace).carrier ⥤ Opens X.carrier :=
  Opens.map D.homToBase ⋙ D.doubleOpens

/-- **The inclusion of the opens of `W` into the opens of `X` is
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleOpens`.** -/
public def tripleOpensIso : restrictOpensInclusion X D.base ≅ D.tripleOpens :=
  NatIso.ofComponents
    (fun Z => ⟨homOfLE (le_of_eq (D.image_eq_base Z).symm), D.opensCompare.app Z,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩)
    fun _ => Subsingleton.elim _ _

/-- `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleOpens` is continuous for the
open-cover topologies, being isomorphic to the inclusion of the opens of `W`. -/
public instance isContinuous_tripleOpens :
    (D.tripleOpens).IsContinuous
      (Opens.grothendieckTopology (D.basespace).carrier)
      (Opens.grothendieckTopology X.carrier) :=
  letI := isContinuous_restrictOpensInclusion X D.base
  Functor.isContinuous_of_iso (D.tripleOpensIso)
    (Opens.grothendieckTopology (D.basespace).carrier)
    (Opens.grothendieckTopology X.carrier)

/-- The morphism of sheaves of rings on `W` that the composite of the two restrictions with the
comparison pushes forward along: the comparison of structure sheaves of rings followed by the
pushforward of `AlgebraicGeometry.RingedSpace.CorrespondingOpens.doubleData`. -/
public def tripleData :
    structureSheafOfRings (D.basespace) ⟶
      ((D.tripleOpens).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology (D.basespace).carrier)
        (Opens.grothendieckTopology X.carrier)).obj (structureSheafOfRings X) :=
  D.structureSheafCompare ≫
    ((Opens.map D.homToBase).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (D.basespace).carrier)
      (Opens.grothendieckTopology (D.subspace).carrier)).map (D.doubleData)

/-- **The double restriction followed by the comparison is one pushforward**, along
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleOpens` and the datum
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleData`. -/
public theorem triple_eq :
    SheafOfModules.pushforward.{u} (F := D.doubleOpens) (D.doubleData) ⋙ D.compare =
      SheafOfModules.pushforward.{u} (F := D.tripleOpens) (D.tripleData) :=
  rfl

/-- **The three-fold composite is one pushforward**: restricting to `U`, then to `V`, and then
comparing is the pushforward along `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleOpens`
and the datum `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleData`. -/
public theorem tripleRestrict_eq :
    restrictModules X U ⋙ restrictModules (X.restrict U.isOpenEmbedding) D.sub ⋙ D.compare =
      SheafOfModules.pushforward.{u} (F := D.tripleOpens) (D.tripleData) :=
  (congrArg (fun G => G ⋙ D.compare) D.double_eq).trans D.triple_eq

/-! ### The compatibility isomorphism -/

/-- **Transporting `AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleData` along
`AlgebraicGeometry.RingedSpace.CorrespondingOpens.tripleOpensIso` gives the identity of
`𝒪_{X|W}`.** -/
public theorem tripleData_eq :
    D.tripleData ≫ (Functor.sheafPushforwardContinuousNatTrans (D.tripleOpensIso).hom RingCat.{u}
        (Opens.grothendieckTopology (D.basespace).carrier)
        (Opens.grothendieckTopology X.carrier)).app (structureSheafOfRings X) =
      𝟙 (structureSheafOfRings (D.basespace)) := by
  ext : 2
  funext Z
  show (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map _) ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map (X.presheaf.map _) = 𝟙 _
  refine (map_presheaf_comp _ _ (𝟙 _)).symm.trans ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-- **`(·)|_U ⋙ (·)|_V ⋙ Φ ≅ (·)|_W`**: restricting `𝒪_X`-modules to `U`, then to the open `V`
of `X|U`, and then comparing along `Φ = AlgebraicGeometry.RingedSpace.CorrespondingOpens.compare`
is restricting them to the open `W` of `X` corresponding to `V`. -/
public def tripleRestrictIso :
    restrictModules X U ⋙ restrictModules (X.restrict U.isOpenEmbedding) D.sub ⋙ D.compare ≅
      restrictModules X D.base :=
  eqToIso (D.tripleRestrict_eq) ≪≫
    SheafOfModules.pushforwardCongr₂ (D.tripleData) (D.tripleOpensIso) (D.tripleData_eq) ≪≫
    eqToIso (restrictModules_eq_pushforward X D.base).symm

end CorrespondingOpens

end AlgebraicGeometry.RingedSpace

end
