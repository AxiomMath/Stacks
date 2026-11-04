module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FlatnessAtPoint
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatPoint
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Flatness along a fibre spreads after an elementary étale base change

Let `f : X ⟶ S` be of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite type, and
let `s : S` be a point over which `F` is flat over `S` at every point of the fibre `X_s`. Stacks
Tag 05KV produces an elementary étale neighbourhood `(S', s')` of `(S, s)` and an open subscheme
`V ⊆ X ×_S Spec 𝒪_{S', s'}` containing the whole fibre `X_s = X ×_S s'` on which the pullback of
`F` is flat over `Spec 𝒪_{S', s'}`.

This is Stacks Tag 05KU with the finite presentation hypothesis on `f` weakened to finite type,
at the cost of dropping the finite presentation conclusion on the pullback of `F`.

## Main results

* `exists_elementaryEtaleNeighborhood_open_flat_along_fibre`, in the namespace
  `AlgebraicGeometry.ElementaryEtaleFlatness`, is **Stacks Tag 05KV**.

## Implementation notes

Finite type of `f` is expressed as `AlgebraicGeometry.LocallyOfFiniteType` together with
`AlgebraicGeometry.QuasiCompact`, and the fibre is the scheme `f.fiber s`, which is therefore
quasi-compact. Tag 05KT gives, for each point of that fibre, an elementary étale neighbourhood of
`(S, s)` and an open of the corresponding fibre product on which the pullback of `F` is flat; the
fibres of those opens cover `X_s`, so finitely many suffice, and by Tag 057B — the category of
elementary étale neighbourhoods is cofiltered — one elementary neighbourhood dominates all of
them. The union over the finitely many chosen points of the inverse images of those opens is the
required open.

The fibre is related to the fibre product by `fiberToLocalPullback`, the morphism
`X_s ⟶ X ×_S Spec 𝒪_{U, u}` induced by the inclusion of the fibre and by the map of `Spec κ(s)`
into `Spec 𝒪_{U, u}` coming from the residue field isomorphism of an *elementary* neighbourhood.
Its image is exactly the fibre of the second projection over the closed point:
`exists_fiberToLocalPullback_eq` and `closedFiberPoint_ext` identify that fibre, using that the
structure morphism of an elementary neighbourhood induces an isomorphism on residue fields at the
closed point.

Flatness is transported along the refinement morphisms by base change
(`AlgebraicGeometry.modulePullback_isFlatOver`) and along the inclusions of the members of the
union by `AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt`, which applies because
an open immersion is flat.

## References

* [Stacks Project, Tag 05KV](https://stacks.math.columbia.edu/tag/05KV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ElementaryEtaleFlatness

section ProofHelpers

open Opposite
open RingedSpaceModuleAdjunction

private noncomputable def pointOfElementary {S : Scheme.{u}} {s : S}
    (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary) :
    Spec (S.residueField s) ⟶ U.scheme :=
  Spec.map ((asIso U.residueFieldMap).inv) ≫ U.scheme.fromSpecResidueField U.point

private theorem pointOfElementary_over {S : Scheme.{u}} {s : S}
    (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary) :
    pointOfElementary U hU ≫ U.toBase = S.fromSpecResidueField s := by
  dsimp [pointOfElementary]
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
    (f := U.toBase) (x := U.point)]
  simp [AlgebraicGeometry.EtaleNeighborhood.residueFieldMap]

private noncomputable def localBasePointMap {S : Scheme.{u}} {s : S}
    (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary) :
    Spec (S.residueField s) ⟶ Spec (U.scheme.presheaf.stalk U.point) :=
  Spec.map ((asIso U.residueFieldMap).inv) ≫ Spec.map (U.scheme.residue U.point)

private theorem localBasePointMap_over {S : Scheme.{u}} {s : S}
    (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary) :
  localBasePointMap U hU ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase =
      S.fromSpecResidueField s := by
  show Spec.map ((asIso U.residueFieldMap).inv) ≫
      U.scheme.fromSpecResidueField U.point ≫ U.toBase = _
  exact pointOfElementary_over U hU

private theorem localBasePointMap_closedPoint {S : Scheme.{u}} {s : S}
    (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary) :
    localBasePointMap U hU (IsLocalRing.closedPoint (S.residueField s)) =
      IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point) := by
  show Spec.map (U.scheme.residue U.point)
      (Spec.map ((asIso U.residueFieldMap).inv)
        (IsLocalRing.closedPoint (S.residueField s))) = _
  have : IsLocalHom ((asIso U.residueFieldMap).inv).hom := by infer_instance
  rw [Spec_closedPoint]
  exact Scheme.SpecMap_residue_apply U.point _

/-- The canonical morphism from the spectrum of a stalk is an isomorphism on the residue field at
the closed point. -/
theorem fromSpecStalk_residueFieldMap_closedPoint_isIso
    (X : Scheme.{u}) (x : X) :
    IsIso ((X.fromSpecStalk x).residueFieldMap
      (IsLocalRing.closedPoint (X.presheaf.stalk x))) := by
  let z := IsLocalRing.closedPoint (X.presheaf.stalk x)
  have h : IsIso ((X.fromSpecStalk x).stalkMap z) := by
    have hi : IsIso ((X.fromSpecStalk x).stalkMap z ≫
        (stalkClosedPointIso (X.presheaf.stalk x)).hom) := by
      rw [← Scheme.stalkClosedPointTo, Scheme.stalkClosedPointTo_fromSpecStalk]
      infer_instance
    exact IsIso.of_isIso_comp_right
      ((X.fromSpecStalk x).stalkMap z) (stalkClosedPointIso (X.presheaf.stalk x)).hom
  have : IsLocalRing ((Spec (X.presheaf.stalk x)).presheaf.stalk z) :=
    (Spec (X.presheaf.stalk x)).isLocalRing z
  exact (IsLocalRing.ResidueField.mapEquiv
    (asIso ((X.fromSpecStalk x).stalkMap z)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

private theorem elementaryBase_residueFieldMap_closedPoint_core {S : Scheme.{u}} {s : S}
    (U : AlgebraicGeometry.EtaleNeighborhood S s) [U.IsElementary] :
    IsIso ((U.scheme.fromSpecStalk U.point ≫ U.toBase).residueFieldMap
      (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))) := by
  have hUres : IsIso (U.toBase.residueFieldMap U.point) := by
    have h : IsIso U.residueFieldMap := inferInstance
    unfold AlgebraicGeometry.EtaleNeighborhood.residueFieldMap at h
    exact IsIso.of_isIso_comp_left (S.residueFieldCongr U.map_point).inv
      (U.toBase.residueFieldMap U.point)
  have hbase : IsIso (U.toBase.residueFieldMap
      (U.scheme.fromSpecStalk U.point
        (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)))) := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hUres
  have h2 : IsIso (U.toBase.residueFieldMap
      (U.scheme.fromSpecStalk U.point
        (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))) ≫
      (U.scheme.fromSpecStalk U.point).residueFieldMap
        (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))) :=
    IsIso.comp_isIso' hbase (fromSpecStalk_residueFieldMap_closedPoint_isIso U.scheme U.point)
  exact (Scheme.residueFieldMap_comp (U.scheme.fromSpecStalk U.point) U.toBase
    (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))).symm ▸ h2

private theorem elementaryBase_residueFieldMap_closedPoint {S : Scheme.{u}} {s : S}
    (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary) :
    IsIso ((U.scheme.fromSpecStalk U.point ≫ U.toBase).residueFieldMap
      (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))) := by
  let : U.IsElementary := hU
  exact elementaryBase_residueFieldMap_closedPoint_core U

private noncomputable def fiberToLocalPullback {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary) :
    f.fiber s ⟶ pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase) := by
  let q := U.scheme.fromSpecStalk U.point ≫ U.toBase
  refine pullback.lift (f.fiberι s)
    (f.fiberToSpecResidueField s ≫ localBasePointMap U hU) ?_
  calc
    f.fiberι s ≫ f =
        f.fiberToSpecResidueField s ≫ S.fromSpecResidueField s :=
      Scheme.Hom.fiber_fac f s
    _ = (f.fiberToSpecResidueField s ≫ localBasePointMap U hU) ≫ q := by
      simp [q, localBasePointMap_over]

private theorem fiberToLocalPullback_fst {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary)
    (y : f.fiber s) :
    pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase)
        (fiberToLocalPullback f s U hU y) = f.fiberι s y := by
  show ((pullback.lift _ _ _ ≫
    pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase)) y) = _
  rw [pullback.lift_fst]


private theorem localBase_closedPoint_over {S : Scheme.{u}} {s : S}
    (U : AlgebraicGeometry.EtaleNeighborhood S s) :
    (U.scheme.fromSpecStalk U.point ≫ U.toBase)
        (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)) = s :=
  have h1 : U.scheme.fromSpecStalk U.point
      (IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)) = U.point :=
    Scheme.fromSpecStalk_closedPoint
  (congrArg (fun y : U.scheme => U.toBase y) h1).trans U.map_point

private theorem fiberToLocalPullback_snd_closedPoint {X S : Scheme.{u}}
    (f : X ⟶ S) (s : S) (U : AlgebraicGeometry.EtaleNeighborhood S s)
    (hU : U.IsElementary) (y : f.fiber s) :
    pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)
        (fiberToLocalPullback f s U hU y) =
      IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point) := by
  show ((pullback.lift (f.fiberι s)
      (f.fiberToSpecResidueField s ≫ localBasePointMap U hU) _ ≫
      pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)) y) = _
  rw [pullback.lift_snd]
  simp [Scheme.Hom.fiberToSpecResidueField_apply, localBasePointMap_closedPoint]
  rfl

private theorem closedFiberPoint_ext {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary)
    (p q : ↥(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)))
    (hp : pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase) p =
      IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))
    (hq : pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase) q =
      IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))
    (hfst : pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) p =
      pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) q) : p = q := by
  let T := Spec (U.scheme.presheaf.stalk U.point)
  let t : T := IsLocalRing.closedPoint _
  let a := U.scheme.fromSpecStalk U.point ≫ U.toBase
  have : IsIso (a.residueFieldMap t) := elementaryBase_residueFieldMap_closedPoint U hU
  let j := baseChangeFiberMap f a t
  let pf : (pullback.snd f a).fiber t := (pullback.snd f a).fiberHomeo t |>.symm ⟨p, hp⟩
  let qf : (pullback.snd f a).fiber t := (pullback.snd f a).fiberHomeo t |>.symm ⟨q, hq⟩
  have hp' : (pullback.snd f a).fiberι t pf = p :=
    pullback.snd f a |>.fiberι_fiberHomeo_symm t ⟨p, hp⟩
  have hq' : (pullback.snd f a).fiberι t qf = q :=
    pullback.snd f a |>.fiberι_fiberHomeo_symm t ⟨q, hq⟩
  have hcoord : f.fiberι (a t) (j pf) = f.fiberι (a t) (j qf) := by
    have hfib := baseChangeFiberMap_comp_fiberι f a t
    calc
      f.fiberι (a t) (j pf) = pullback.fst f a p := by
        simpa [j, Scheme.Hom.comp_apply, hp'] using congrArg (fun k => k pf) hfib
      _ = pullback.fst f a q := hfst
      _ = f.fiberι (a t) (j qf) := by
        symm
        simpa [j, Scheme.Hom.comp_apply, hq'] using congrArg (fun k => k qf) hfib
  have hj : j pf = j qf := (f.fiberι (a t)).isEmbedding.injective hcoord
  have : IsIso j := isIso_baseChangeFiberMap f a t
  rw [← hp', ← hq', (Scheme.homeoOfIso (asIso j)).injective hj]

private theorem exists_fiberToLocalPullback_eq {X S : Scheme.{u}}
    (f : X ⟶ S) (s : S) (U : AlgebraicGeometry.EtaleNeighborhood S s)
    (hU : U.IsElementary)
    (z : ↥(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)))
    (hz : pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase) z =
      IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point)) :
    ∃ y : f.fiber s, fiberToLocalPullback f s U hU y = z := by
  let T := Spec (U.scheme.presheaf.stalk U.point)
  let t : T := IsLocalRing.closedPoint _
  let a := U.scheme.fromSpecStalk U.point ≫ U.toBase
  have hat : a t = s := localBase_closedPoint_over U
  have : IsIso (a.residueFieldMap t) := elementaryBase_residueFieldMap_closedPoint U hU
  let j := baseChangeFiberMap f a t
  let zf : (pullback.snd f a).fiber t := (pullback.snd f a).fiberHomeo t |>.symm ⟨z, hz⟩
  let y0 : f.fiber (a t) := j zf
  have hyPoint : f (f.fiberι (a t) y0) = s := (f.fiberHomeo (a t) y0).property.trans hat
  let y : f.fiber s := (f.fiberHomeo s).symm ⟨f.fiberι (a t) y0, hyPoint⟩
  have hyfst : pullback.fst f a (fiberToLocalPullback f s U hU y) =
      pullback.fst f a z := by
    have hcoord := congrArg (fun k => k zf)
      (baseChangeFiberMap_comp_fiberι f a t)
    have hfz : (pullback.snd f a).fiberι t zf = z :=
      pullback.snd f a |>.fiberι_fiberHomeo_symm t ⟨z, hz⟩
    have hy0 : f.fiberι (a t) y0 = pullback.fst f a z := by
      simpa [j, y0, Scheme.Hom.comp_apply, hfz] using hcoord
    have hy : f.fiberι s y = f.fiberι (a t) y0 := by
      simp [y]
    rw [fiberToLocalPullback_fst, hy, hy0]
  exact ⟨y, closedFiberPoint_ext f s U hU _ _
    (fiberToLocalPullback_snd_closedPoint f s U hU y) hz hyfst⟩
private def LocalFlatNeighborhoodData {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (s : S) (x : X) : Prop :=
  ∃ (U : AlgebraicGeometry.EtaleNeighborhood S s) (_ : U.IsElementary),
    let g := U.scheme.fromSpecStalk U.point ≫ U.toBase
    let P : Scheme.{u} := pullback f g
    ∃ (z : P) (_ : pullback.fst f g z = x)
      (_ : ∀ z' : P, pullback.fst f g z' = x → z' = z)
      (V : P.Opens), z ∈ V ∧
        AlgebraicGeometry.IsFlatOver
          (((V.ι : V.toScheme ⟶ P) ≫ pullback.snd f g).toLRSHom.toShHom)
          ((Scheme.Modules.pullback ((V.ι : V.toScheme ⟶ P) ≫ pullback.fst f g)).obj F)

private theorem exists_local_flat_open_containing_fibrePoint {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (s : S)
    (hF : ∀ x : X, f x = s → AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x)
    (y : f.fiber s) :
    ∃ (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary)
      (z : ↥(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)))
      (_ : pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) z = f.fiberι s y)
      (_ : ∀ z' : ↥(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)),
        pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) z' = f.fiberι s y → z' = z)
      (V : (pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).Opens),
      z ∈ V ∧
        AlgebraicGeometry.IsFlatOver
          (((V.ι : V.toScheme ⟶ pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)) ≫
            pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).toLRSHom.toShHom)
          ((Scheme.Modules.pullback
            ((V.ι : V.toScheme ⟶ pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)) ≫
              pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F) ∧
    fiberToLocalPullback f s U hU y ∈ V := by
  classical
  let x : X := f.fiberι s y
  have hys : f x = s := by
    simpa using (f.fiberHomeo s y).property
  have hres₀ : LocalFlatNeighborhoodData f F (f x) x :=
    exists_elementaryEtaleNeighborhood_open_flat f F x (hF x hys)
  have hres : LocalFlatNeighborhoodData f F s x := hys ▸ hres₀
  change ∃ (U : AlgebraicGeometry.EtaleNeighborhood S s) (_ : U.IsElementary),
      let g := U.scheme.fromSpecStalk U.point ≫ U.toBase
      let P : Scheme.{u} := pullback f g
      ∃ (z : P) (_ : pullback.fst f g z = x)
        (_ : ∀ z' : P, pullback.fst f g z' = x → z' = z)
        (V : P.Opens), z ∈ V ∧
          AlgebraicGeometry.IsFlatOver
            (((V.ι : V.toScheme ⟶ P) ≫ pullback.snd f g).toLRSHom.toShHom)
            ((Scheme.Modules.pullback ((V.ι : V.toScheme ⟶ P) ≫ pullback.fst f g)).obj F) at hres
  obtain ⟨U, hU, z, hz, huniq, V, hzV, hflat⟩ := hres
  refine ⟨U, hU, z, hz, huniq, V, hzV, hflat, ?_⟩
  have hfst : pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase)
      (fiberToLocalPullback f s U hU y) = x := by
    simpa [x] using fiberToLocalPullback_fst f s U hU y
  simpa [huniq _ hfst] using hzV

private noncomputable def identityElementaryNeighborhood (S : Scheme.{u}) (s : S) :
    AlgebraicGeometry.ElementaryEtaleNeighborhood S s := by
  refine ⟨⟨S, s, 𝟙 S, rfl⟩, ?_⟩
  change IsIso ((𝟙 S : S ⟶ S).residueFieldMap s)
  infer_instance

private theorem exists_common_elementary_refinement (S : Scheme.{u}) (s : S)
    (l : List (AlgebraicGeometry.ElementaryEtaleNeighborhood S s)) :
    ∃ W : AlgebraicGeometry.ElementaryEtaleNeighborhood S s,
      ∀ U, U ∈ l → Nonempty (W ⟶ U) := by
  classical
  have : IsCofiltered (AlgebraicGeometry.ElementaryEtaleNeighborhood S s) :=
    CategoryTheory.isCofiltered_of_isFiltered_op _
  induction l with
  | nil =>
      exact ⟨identityElementaryNeighborhood S s, by simp⟩
  | cons U l ih =>
      obtain ⟨W, hW⟩ := ih
      obtain ⟨Z, hZW, hZU, _⟩ := IsCofilteredOrEmpty.cone_objs W U
      refine ⟨Z, fun V hV => ?_⟩
      rcases List.mem_cons.mp hV with rfl | h
      · exact ⟨hZU⟩
      · exact ⟨hZW ≫ (hW V h).some⟩

private noncomputable def localTransition {S : Scheme.{u}} {s : S}
    {W U : AlgebraicGeometry.ElementaryEtaleNeighborhood S s} (φ : W ⟶ U) :
    Spec (W.obj.scheme.presheaf.stalk W.obj.point) ⟶
      Spec (U.obj.scheme.presheaf.stalk U.obj.point) :=
  Spec.map ((U.obj.scheme.presheaf.stalkCongr (.of_eq φ.hom.map_point)).inv ≫
    φ.hom.hom.stalkMap W.obj.point)

private theorem specMap_stalkCongr_inv_fromSpecStalk {Y : Scheme.{u}}
    (x x' : Y) (h : x = x') :
    Spec.map ((Y.presheaf.stalkCongr (.of_eq h)).inv) ≫ Y.fromSpecStalk x' =
      Y.fromSpecStalk x := by
  cases h
  simp

private theorem localTransition_over {S : Scheme.{u}} {s : S}
    {W U : AlgebraicGeometry.ElementaryEtaleNeighborhood S s} (φ : W ⟶ U) :
    localTransition φ ≫ U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase =
      W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase := by
  calc
    localTransition φ ≫ U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase =
        Spec.map (φ.hom.hom.stalkMap W.obj.point) ≫
          (Spec.map ((U.obj.scheme.presheaf.stalkCongr
            (.of_eq φ.hom.map_point)).inv) ≫ U.obj.scheme.fromSpecStalk U.obj.point) ≫
            U.obj.toBase := by
          simp only [localTransition, Spec.map_comp, Category.assoc]
    _ = Spec.map (φ.hom.hom.stalkMap W.obj.point) ≫
          U.obj.scheme.fromSpecStalk (φ.hom.hom W.obj.point) ≫ U.obj.toBase := by
          rw [specMap_stalkCongr_inv_fromSpecStalk _ _ φ.hom.map_point]
    _ = W.obj.scheme.fromSpecStalk W.obj.point ≫ φ.hom.hom ≫ U.obj.toBase :=
          congrArg (fun g => g ≫ U.obj.toBase)
            (Scheme.SpecMap_stalkMap_fromSpecStalk (f := φ.hom.hom) (x := W.obj.point))
    _ = W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase :=
          congrArg (fun g => W.obj.scheme.fromSpecStalk W.obj.point ≫ g) φ.hom.over

private noncomputable def refinementPullbackMap {X S : Scheme.{u}} (f : X ⟶ S)
    {s : S} {W U : AlgebraicGeometry.ElementaryEtaleNeighborhood S s} (φ : W ⟶ U) :
    pullback f (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase) ⟶
      pullback f (U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase) := by
  refine pullback.lift (pullback.fst f _) (pullback.snd f _ ≫ localTransition φ) ?_
  calc
    pullback.fst f _ ≫ f = pullback.snd f _ ≫
        (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase) := pullback.condition
    _ = pullback.snd f _ ≫
        (localTransition φ ≫ U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase) := by
          rw [localTransition_over]
    _ = (pullback.snd f _ ≫ localTransition φ) ≫
        (U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase) := by
          simp [Category.assoc]

private theorem refinementPullbackMap_fst {X S : Scheme.{u}} (f : X ⟶ S)
    {s : S} {W U : AlgebraicGeometry.ElementaryEtaleNeighborhood S s} (φ : W ⟶ U) :
    refinementPullbackMap f φ ≫ pullback.fst f
      (U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase) =
      pullback.fst f (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase) := by
  show (pullback.lift _ _ _ ≫ _) = _
  rw [pullback.lift_fst]

private theorem refinementPullbackMap_snd {X S : Scheme.{u}} (f : X ⟶ S)
    {s : S} {W U : AlgebraicGeometry.ElementaryEtaleNeighborhood S s} (φ : W ⟶ U) :
    refinementPullbackMap f φ ≫ pullback.snd f
      (U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase) =
      pullback.snd f (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase) ≫
        localTransition φ := by
  show (pullback.lift _ _ _ ≫ _) = _
  rw [pullback.lift_snd]

private theorem localTransition_closedPoint {S : Scheme.{u}} {s : S}
    {W U : AlgebraicGeometry.ElementaryEtaleNeighborhood S s} (φ : W ⟶ U) :
    localTransition φ (IsLocalRing.closedPoint
      (W.obj.scheme.presheaf.stalk W.obj.point)) =
      IsLocalRing.closedPoint (U.obj.scheme.presheaf.stalk U.obj.point) := by
  have : IsLocalHom
      ((U.obj.scheme.presheaf.stalkCongr (.of_eq φ.hom.map_point)).inv ≫
        φ.hom.hom.stalkMap W.obj.point).hom := by infer_instance
  rw [localTransition, Spec_closedPoint]

private theorem refinementPullbackMap_fiberToLocalPullback {X S : Scheme.{u}}
    (f : X ⟶ S) {s : S} {W U : AlgebraicGeometry.ElementaryEtaleNeighborhood S s}
    (φ : W ⟶ U) (y : f.fiber s) :
    refinementPullbackMap f φ
      (fiberToLocalPullback f s W.obj W.property y) =
    fiberToLocalPullback f s U.obj U.property y := by
  apply closedFiberPoint_ext f s U.obj U.property _ _
  · have hs := congrArg (fun k => k (fiberToLocalPullback f s W.obj W.property y))
      (refinementPullbackMap_snd f φ)
    simpa [Scheme.Hom.comp_apply, fiberToLocalPullback_snd_closedPoint,
      localTransition_closedPoint] using hs
  · exact fiberToLocalPullback_snd_closedPoint f s U.obj U.property y
  · have hf := congrArg (fun k => k (fiberToLocalPullback f s W.obj W.property y))
      (refinementPullbackMap_fst f φ)
    simpa [Scheme.Hom.comp_apply, fiberToLocalPullback_fst] using hf

/-- Relative flatness on the whole space only depends on the isomorphism class of the module. -/
private theorem flatOver_iff_of_iso {X S : Scheme.{u}} (f : X ⟶ S) {F G : X.Modules}
    (e : F ≅ G) :
    AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F ↔
      AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom G :=
  ⟨fun h x => (flatOverAt_iff_of_iso f e x).mp (h x),
    fun h x => (flatOverAt_iff_of_iso f e x).mpr (h x)⟩

private theorem refinementPullbackMap_isPullback {X S : Scheme.{u}}
    (f : X ⟶ S) {s : S} {W U : AlgebraicGeometry.ElementaryEtaleNeighborhood S s}
    (φ : W ⟶ U) :
    IsPullback (refinementPullbackMap f φ)
      (pullback.snd f (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase))
      (pullback.snd f (U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase))
      (localTransition φ) := by
  refine IsPullback.of_right ?_ (refinementPullbackMap_snd f φ) (IsPullback.of_hasPullback _ _)
  rw [refinementPullbackMap_fst, localTransition_over]
  exact IsPullback.of_hasPullback _ _

/-- Pulling back along `k` and then `p` is pulling back along any `q` equal to `k ≫ p`. -/
private noncomputable def modulePullbackCompIso {X Y Z : Scheme.{u}} {k : X ⟶ Y} {p : Y ⟶ Z}
    {q : X ⟶ Z} (h : k ≫ p = q) (F : Z.Modules) :
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback p).obj F) ≅
      (Scheme.Modules.pullback q).obj F := by
  subst h
  exact (Scheme.Modules.pullbackComp k p).app F

private theorem flatOnRefinementPreimage {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] {s : S}
    {W U : AlgebraicGeometry.ElementaryEtaleNeighborhood S s} (φ : W ⟶ U)
    (V : (pullback f (U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase)).Opens)
    (hV : AlgebraicGeometry.IsFlatOver
      (((V.ι : V.toScheme ⟶ pullback f
        (U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase)) ≫
          pullback.snd f (U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase)).toLRSHom.toShHom)
      ((Scheme.Modules.pullback
        ((V.ι : V.toScheme ⟶ pullback f
          (U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase)) ≫
            pullback.fst f (U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase))).obj F)) :
    let P := pullback f (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase)
    let m := refinementPullbackMap f φ
    let V' := m ⁻¹ᵁ V
    AlgebraicGeometry.IsFlatOver
      (((V'.ι : V'.toScheme ⟶ P) ≫ pullback.snd f
        (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase)).toLRSHom.toShHom)
      ((Scheme.Modules.pullback
        ((V'.ι : V'.toScheme ⟶ P) ≫ pullback.fst f
          (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase))).obj F) := by
  let qU := U.obj.scheme.fromSpecStalk U.obj.point ≫ U.obj.toBase
  let qW := W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase
  let P_U := pullback f qU
  let P_W := pullback f qW
  let m := refinementPullbackMap f φ
  let V' : P_W.Opens := m ⁻¹ᵁ V
  let k : V'.toScheme ⟶ V.toScheme := m ∣_ V
  let a : V.toScheme ⟶ Spec (U.obj.scheme.presheaf.stalk U.obj.point) :=
    V.ι ≫ pullback.snd f qU
  let b : V'.toScheme ⟶ Spec (W.obj.scheme.presheaf.stalk W.obj.point) :=
    V'.ι ≫ pullback.snd f qW
  have hsq : IsPullback k b a (localTransition φ) := by
    dsimp [k, a, b, V', P_U, P_W, qU, qW]
    exact (isPullback_morphismRestrict m V).paste_vert
      (refinementPullbackMap_isPullback f φ)
  let p := (V.ι : V.toScheme ⟶ P_U) ≫ pullback.fst f qU
  let M := (Scheme.Modules.pullback p).obj F
  have hMq : M.IsQuasicoherent := by
    show ((modulePullback p.toLRSHom.toShHom).obj F).IsQuasicoherent
    exact @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (p.toLRSHom.toShHom) F (‹F.IsQuasicoherent›)
  have hbc := @AlgebraicGeometry.modulePullback_isFlatOver
    V.toScheme (Spec (U.obj.scheme.presheaf.stalk U.obj.point))
    (Spec (W.obj.scheme.presheaf.stalk W.obj.point)) V'.toScheme
    (V.ι ≫ pullback.snd f qU) (localTransition φ) k b hsq M hMq hV
  have hp : k ≫ p = V'.ι ≫ pullback.fst f qW := by
    dsimp [k, p, V', P_U, P_W, qU, qW, m]
    rw [← Category.assoc, morphismRestrict_ι]
    simp only [Category.assoc]
    rw [refinementPullbackMap_fst]
  have hbc' := (flatOver_iff_of_iso b (modulePullbackCompIso hp F)).mp hbc
  simpa [b, a, M, P_U, P_W, qU, qW, V'] using hbc'

end ProofHelpers

/-- **Stacks Project, Tag 05KV.** Flatness of a finite type quasi-coherent module along
a fibre spreads to an open neighbourhood of that fibre after passing to the local scheme
of an elementary étale neighbourhood of the base point. -/
@[stacks 05KV]
theorem exists_elementaryEtaleNeighborhood_open_flat_along_fibre
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (hF : ∀ x : X, f x = s → AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (U : AlgebraicGeometry.EtaleNeighborhood S s) (_ : U.IsElementary),
      let g := U.scheme.fromSpecStalk U.point ≫ U.toBase
      let P : Scheme.{u} := pullback f g
      ∃ (V : P.Opens),
        (∀ z : P, pullback.snd f g z = IsLocalRing.closedPoint _ → z ∈ V) ∧
          AlgebraicGeometry.IsFlatOver
            (((V.ι : V.toScheme ⟶ P) ≫ pullback.snd f g).toLRSHom.toShHom)
            ((Scheme.Modules.pullback
              ((V.ι : V.toScheme ⟶ P) ≫ pullback.fst f g)).obj F) :=
  by
    classical
    let T : Scheme := f.fiber s
    have hdata : ∀ y : T,
        ∃ (U : AlgebraicGeometry.EtaleNeighborhood S s) (hU : U.IsElementary)
          (z : ↥(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)))
          (_ : pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) z = f.fiberι s y)
          (_ : ∀ z' : ↥(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)),
            pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) z' = f.fiberι s y → z' = z)
          (V : (pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).Opens),
          z ∈ V ∧
            AlgebraicGeometry.IsFlatOver
              (((V.ι : V.toScheme ⟶ pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)) ≫
                pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).toLRSHom.toShHom)
              ((Scheme.Modules.pullback
                ((V.ι : V.toScheme ⟶ pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)) ≫
                  pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F) ∧
            fiberToLocalPullback f s U hU y ∈ V := by
      intro y
      exact exists_local_flat_open_containing_fibrePoint f F s hF y
    choose U hU z hz huniq V hzV hflat hmem using hdata
    let O : ∀ y : T, T.Opens := fun y =>
      (fiberToLocalPullback f s (U y) (hU y)) ⁻¹ᵁ (V y)
    have hcover : ∀ y : T, y ∈ O y := by
      intro y
      show fiberToLocalPullback f s (U y) (hU y) y ∈ V y
      exact hmem y
    let : CompactSpace T := inferInstance
    obtain ⟨I, hI⟩ := (isCompact_univ : IsCompact (Set.univ : Set T)).elim_finite_subcover
      (fun y : T => (O y : Set T)) (fun y => (O y).2)
      (by
        intro y hy
        exact Set.mem_iUnion.mpr ⟨y, hcover y⟩)
    let E : ∀ y : T, AlgebraicGeometry.ElementaryEtaleNeighborhood S s :=
      fun y => ⟨U y, hU y⟩
    let l : List (AlgebraicGeometry.ElementaryEtaleNeighborhood S s) :=
      I.toList.map E
    obtain ⟨W, hW⟩ := exists_common_elementary_refinement S s l
    have hW' : ∀ y : T, y ∈ I → Nonempty (W ⟶ E y) := by
      intro y hy
      apply hW
      apply List.mem_map.mpr
      exact ⟨y, Finset.mem_toList.mpr hy, rfl⟩
    let φ : ∀ i : {y : T // y ∈ I}, W ⟶ E i.1 := fun i =>
      Classical.choice (hW' i.1 i.2)
    let Vref : ∀ i : {y : T // y ∈ I},
        (pullback f (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase)).Opens :=
      fun i => (refinementPullbackMap f (φ i)) ⁻¹ᵁ V i.1
    let Vunion : (pullback f (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase)).Opens :=
      ⨆ i : {y : T // y ∈ I}, Vref i
    refine ⟨W.obj, W.property, ?_⟩
    dsimp only
    refine ⟨Vunion, ?_, ?_⟩
    · intro z hzclosed
      obtain ⟨y, rfl⟩ := exists_fiberToLocalPullback_eq f s W.obj W.property z hzclosed
      have hycov : y ∈ ⋃ i ∈ I, O i := hI (Set.mem_univ y)
      rcases Set.mem_iUnion.mp hycov with ⟨i, hycov⟩
      rcases Set.mem_iUnion.mp hycov with ⟨hi, hyO⟩
      let iI : {y : T // y ∈ I} := ⟨i, hi⟩
      apply TopologicalSpace.Opens.mem_iSup.mpr
      refine ⟨iI, ?_⟩
      show refinementPullbackMap f (φ iI)
        (fiberToLocalPullback f s W.obj W.property y) ∈ V i
      rw [refinementPullbackMap_fiberToLocalPullback]
      exact hyO
    · intro z
      obtain ⟨i, hzi⟩ := TopologicalSpace.Opens.mem_iSup.mp z.2
      let Vi := Vref i
      let P := pullback f (W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase)
      let qW := W.obj.scheme.fromSpecStalk W.obj.point ≫ W.obj.toBase
      let j : Vunion.toScheme ⟶ P := Vunion.ι
      let ji : Vi.toScheme ⟶ P := Vi.ι
      let k : Vi.toScheme ⟶ Vunion.toScheme := P.homOfLE (le_iSup Vref i)
      let wi : Vi.toScheme := ⟨z.1, hzi⟩
      have hkw : k wi = z := by
        show (P.homOfLE (le_iSup Vref i)) ⟨z.1, hzi⟩ = z
        exact Scheme.homOfLE_apply' (le_iSup Vref i) z.1 hzi
      have : IsOpenImmersion k := by infer_instance
      have hkflat : AlgebraicGeometry.IsFlatAt k.toLRSHom.toShHom wi := by
        have hFlat : Flat k := inferInstance
        exact (AlgebraicGeometry.Flat.iff_flat_stalkMap k).mp hFlat wi
      let qV : Vunion.toScheme ⟶ Spec (W.obj.scheme.presheaf.stalk W.obj.point) :=
        j ≫ pullback.snd f qW
      let qi : Vi.toScheme ⟶ Spec (W.obj.scheme.presheaf.stalk W.obj.point) :=
        ji ≫ pullback.snd f qW
      let pV : Vunion.toScheme ⟶ X := j ≫ pullback.fst f qW
      let pi : Vi.toScheme ⟶ X := ji ≫ pullback.fst f qW
      let NV := (Scheme.Modules.pullback pV).obj F
      let Ni := (Scheme.Modules.pullback pi).obj F
      have hki : k ≫ j = ji := by
        show P.homOfLE (le_iSup Vref i) ≫ Vunion.ι = Vi.ι
        exact Scheme.homOfLE_ι P (le_iSup Vref i)
      have hq : k ≫ qV = qi := by
        simp [qV, qi, ← Category.assoc, hki]
      have hp : k ≫ pV = pi := by
        simp [pV, pi, ← Category.assoc, hki]
      have hNi : AlgebraicGeometry.IsFlatOver qi.toLRSHom.toShHom Ni := by
        exact flatOnRefinementPreimage f F (φ i) (V i.1)
          (by
            simpa [Vref, Vi] using hflat i.1)
      have hpull : AlgebraicGeometry.IsFlatOverAt (k ≫ qV).toLRSHom.toShHom
          ((Scheme.Modules.pullback k).obj NV) wi :=
        (flatOverAt_iff_of_iso (k ≫ qV) (modulePullbackCompIso hp F).symm wi).mp
          (by simpa [hq] using hNi wi)
      have hVpoint : AlgebraicGeometry.IsFlatOverAt qV.toLRSHom.toShHom NV (k wi) :=
        (AlgebraicGeometry.isFlatOverAt_iff_modulePullback_isFlatOverAt
          k qV NV wi hkflat).mpr hpull
      simpa [qV, NV, pV, j, P, qW, hkw] using hVpoint


end AlgebraicGeometry.ElementaryEtaleFlatness

end
