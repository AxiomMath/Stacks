module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.ElementaryDevissage
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.PurelyTranscendental
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap

/-!
# Base change of an elementary dévissage

An elementary dévissage of `F/X/S` at `x` has a base neighbourhood `V` of `(S, f x)`. Base
changing the whole diagram along a morphism `b : T ⟶ V` hitting the distinguished point of `V`
with trivial residue field extension again produces an elementary dévissage: of the pullback of
`F` to `X ×_S T` along `X ×_S T ⟶ T`, at a point lying over `x` and over the distinguished
point of `T`. Its base neighbourhood is `T` itself.

The case `T = Spec 𝒪_{V, v}` is the replacement of `S` by the spectrum of a local ring which the
first proof of Stacks 05I5 performs before applying Stacks 057T and Stacks 057U.

## Main definitions

* `AlgebraicGeometry.ElementaryDevissage.BaseChangeData`: the base-changed dévissage, its
  distinguished point, and the identification of its relative dimension and of its base
  neighbourhood.
* `AlgebraicGeometry.ElementaryDevissage.baseChange`: the construction of that data.
* `AlgebraicGeometry.ElementaryDevissage.baseChangeStalk`: its specialization to the spectrum
  of the local ring of the base neighbourhood at its distinguished point.

## Main results

* `AlgebraicGeometry.isIso_fiberMapOfIsPullback`: the comparison of fibres attached to a
  cartesian square is an isomorphism when the base change induces an isomorphism of residue
  fields at the point.
* `AlgebraicGeometry.topologicalKrullDimAt_fiberSupp_of_isPullback`: under that hypothesis the
  local dimension of the support of the fibre module is unchanged by the base change.

## Implementation notes

Every one of the schemes of the dévissage is base changed along `b`, and all of them along the
*base* neighbourhood rather than along `S`: the new source neighbourhood is `U ×_V T`, not
`U ×_X (X ×_S T)`. That the resulting morphism `U ×_V T ⟶ X ×_S T` is still étale is
`AlgebraicGeometry.etale_etaleBaseChangeMap`, the general form of Stacks 05H2.

The distinguished points are produced from the bottom of the diagram upwards, each as the unique
point of a fibre product above a trivial residue field extension
(`AlgebraicGeometry.pullbackPointOfIsIsoResidueFieldMap`): first the point of `Y ×_V T`, then the
point of `Z ×_Y (Y ×_V T)`, and then the points of `U ×_V T` and of `X ×_S T` as its images. So
the equation `i z = U.point` of the base-changed dévissage holds by construction rather than
having to be matched up with an independently chosen point, and no uniqueness statement about the
point of `X ×_S T` is needed.

The two fields needing an argument beyond stability of a morphism property under base change are
the singleton fibre of the finite morphism, where uniqueness of the point of `Z ×_Y (Y ×_V T)` is
used, and the local dimension of the support of the fibre module, which is invariant because the
residue field hypothesis makes the comparison of fibres an isomorphism of schemes and the two
supports correspond under it.

## References

* [Stacks Project, Tag 057S](https://stacks.math.columbia.edu/tag/057S)
* [Stacks Project, Tag 05H2](https://stacks.math.columbia.edu/tag/05H2)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Fibres and fibre-module supports under a residue-field-trivial base change -/

/-- The comparison of fibres attached to a cartesian square is an isomorphism as soon as the
lower horizontal morphism induces an isomorphism of residue fields at the point: the comparison
is the base change of `Spec κ(s') ⟶ Spec κ(h s')`. -/
theorem isIso_fiberMapOfIsPullback {Y Y' S S' : Scheme.{u}} {pY : Y' ⟶ Y} {g' : Y' ⟶ S'}
    {g : Y ⟶ S} {h : S' ⟶ S} (hsq : IsPullback pY g' g h) (s' : S')
    [IsIso (h.residueFieldMap s')] : IsIso (fiberMapOfIsPullback hsq s') := by
  have hspec : IsIso (Spec.map (h.residueFieldMap s')) :=
    (Scheme.Spec.mapIso (asIso (h.residueFieldMap s')).op).isIso_hom
  have H := isPullback_fiberToSpecResidueField_of_isPullback hsq s'
  have hhp : HasPullback (g.fiberToSpecResidueField (h s'))
      (Spec.map (h.residueFieldMap s')) :=
    hasPullback_of_right_iso _ _
  have hfst : IsIso (pullback.fst (g.fiberToSpecResidueField (h s'))
      (Spec.map (h.residueFieldMap s'))) :=
    pullback_fst_iso_of_right_iso _ _
  have hh : H.isoPullback.hom ≫ pullback.fst (g.fiberToSpecResidueField (h s'))
      (Spec.map (h.residueFieldMap s')) = fiberMapOfIsPullback hsq s' := H.isoPullback_hom_fst
  rw [← hh]
  exact IsIso.comp_isIso' H.isoPullback.isIso_hom hfst

/-- The local dimension of the support of the fibre module is unchanged by a base change whose
lower horizontal morphism induces an isomorphism of residue fields at the image of the chosen
point: the comparison of fibres is then an isomorphism of schemes, and the two supports
correspond under it. -/
theorem topologicalKrullDimAt_fiberSupp_of_isPullback {X X' S S' : Scheme.{u}}
    {pX : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {h : S' ⟶ S} (hsq : IsPullback pX f' f h)
    (F : X.Modules) [F.IsFiniteType] (x' : X') [IsIso (h.residueFieldMap (f' x'))]
    (hx : f.asFiber (pX x') ∈ SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι (f (pX x')))).obj F)) :
    ∃ hx' : f'.asFiber x' ∈ SheafOfModules.supp
        ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj
          ((Scheme.Modules.pullback pX).obj F)),
      topologicalKrullDimAt (SheafOfModules.supp
          ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj
            ((Scheme.Modules.pullback pX).obj F))) ⟨f'.asFiber x', hx'⟩ =
        topologicalKrullDimAt (SheafOfModules.supp
          ((Scheme.Modules.pullback (f.fiberι (f (pX x')))).obj F))
          ⟨f.asFiber (pX x'), hx⟩ := by
  have hbase : h (f' x') = f (pX x') :=
    (congrArg (fun k : X' ⟶ S => k x') hsq.w).symm
  have hFT : ((Scheme.Modules.pullback pX).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType pX.toLRSHom.toShHom F
  have hmapIso : IsIso (fiberMapOfIsPullback hsq (f' x')) := isIso_fiberMapOfIsPullback hsq _
  let q : f'.fiber (f' x') ⟶ f.fiber (f (pX x')) :=
    fiberMapOfIsPullback hsq (f' x') ≫ (fiberIsoOfEq f hbase).hom
  have hqiso : IsIso q := inferInstanceAs (IsIso (_ ≫ _))
  have hq : q ≫ f.fiberι (f (pX x')) = f'.fiberι (f' x') ≫ pX := by
    change (fiberMapOfIsPullback hsq (f' x') ≫ (fiberIsoOfEq f hbase).hom) ≫ _ = _
    rw [Category.assoc, fiberIsoOfEq_hom_fiberι, fiberMapOfIsPullback_comp_fiberι]
  have hqw : ∀ w, f.fiberι (f (pX x')) (q w) = pX (f'.fiberι (f' x') w) := fun w =>
    congrArg (fun k : f'.fiber (f' x') ⟶ X => k w) hq
  have hqOpen : Topology.IsOpenEmbedding (fun w : f'.fiber (f' x') => q w) := q.isOpenEmbedding
  set T : Set (f.fiber (f (pX x'))) :=
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f (pX x')))).obj F) with hTdef
  have hTT : SheafOfModules.supp ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj
      ((Scheme.Modules.pullback pX).obj F)) = (q : _ → _) ⁻¹' T := by
    rw [hTdef, Stacks.Modules.supp_pullback (f'.fiberι (f' x')),
      Stacks.Modules.supp_pullback pX F, Stacks.Modules.supp_pullback (f.fiberι (f (pX x'))) F]
    ext w
    simp only [Set.mem_preimage]
    exact Iff.of_eq (congrArg (fun p : X => p ∈ SheafOfModules.supp F) (hqw w)).symm
  have hqpt : q (f'.asFiber x') = f.asFiber (pX x') := by
    refine (f.fiberι (f (pX x'))).isEmbedding.injective ?_
    rw [hqw, Scheme.Hom.fiberι_asFiber, Scheme.Hom.fiberι_asFiber]
  have hmem' : f'.asFiber x' ∈ (q : _ → _) ⁻¹' T := by
    change q (f'.asFiber x') ∈ T
    rwa [hqpt]
  refine ⟨hTT ▸ hmem', ?_⟩
  calc
    topologicalKrullDimAt (SheafOfModules.supp
          ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj
            ((Scheme.Modules.pullback pX).obj F))) ⟨f'.asFiber x', hTT ▸ hmem'⟩ =
        topologicalKrullDimAt ((q : _ → _) ⁻¹' T) ⟨f'.asFiber x', hmem'⟩ :=
      topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hTT) _
    _ = topologicalKrullDimAt T ⟨q (f'.asFiber x'), hmem'⟩ :=
      ((hqOpen.restrictPreimage T).topologicalKrullDimAt_eq ⟨f'.asFiber x', hmem'⟩).symm
    _ = topologicalKrullDimAt T ⟨f.asFiber (pX x'), hx⟩ :=
      congrArg (topologicalKrullDimAt T) (Subtype.ext hqpt)

namespace ElementaryDevissage

/-! ### The base-changed elementary dévissage -/

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
  {hx : f.asFiber x ∈
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)}

/-- The elementary dévissage obtained by base changing an elementary dévissage along a morphism
`b : T ⟶ V` to its base neighbourhood, together with its distinguished point and the
identifications of its relative dimension and of its base neighbourhood. -/
structure BaseChangeData (D : ElementaryDevissage f F x hx) {T : Scheme.{u}}
    (b : T ⟶ D.V.scheme) (t : T) where
  /-- The distinguished point of the base-changed source. -/
  point : (pullback f (b ≫ D.V.toBase) : Scheme.{u})
  /-- It lies over the original distinguished point. -/
  fst_point : pullback.fst f (b ≫ D.V.toBase) point = x
  /-- It lies over the distinguished point of the new base. -/
  snd_point : pullback.snd f (b ≫ D.V.toBase) point = t
  /-- It belongs to the support of the pulled-back module on its fibre. -/
  mem_fiber_support : (pullback.snd f (b ≫ D.V.toBase)).asFiber point ∈
    SheafOfModules.supp ((Scheme.Modules.pullback
        ((pullback.snd f (b ≫ D.V.toBase)).fiberι
          (pullback.snd f (b ≫ D.V.toBase) point))).obj
      ((Scheme.Modules.pullback (pullback.fst f (b ≫ D.V.toBase))).obj F))
  /-- The base-changed dévissage. -/
  devissage : ElementaryDevissage (pullback.snd f (b ≫ D.V.toBase))
    ((Scheme.Modules.pullback (pullback.fst f (b ≫ D.V.toBase))).obj F) point mem_fiber_support
  /-- Its relative dimension is the original one. -/
  dimension_eq : devissage.n = D.n
  /-- Its base neighbourhood is the new base itself, with the identity structure morphism. -/
  base_neighborhood : devissage.V =
    EtaleNeighborhood.self T (pullback.snd f (b ≫ D.V.toBase) point)

/-- **Base change of an elementary dévissage.** An elementary dévissage of `F/X/S` at `x` base
changes, along any morphism `b : T ⟶ V` from an affine scheme to its base neighbourhood which
carries a point `t` to the distinguished point of `V` with trivial residue field extension, to
an elementary dévissage of the pullback of `F` to `X ×_S T` at a point over `x` and over `t`,
whose base neighbourhood is `T` itself.

This is the step with which the first proof of Stacks 05I5 replaces `S` by the spectrum of a
local ring before applying Stacks 057T and Stacks 057U. -/
def baseChange (D : ElementaryDevissage f F x hx) [F.IsQuasicoherent] [F.IsFiniteType]
    {T : Scheme.{u}} [IsAffine T] (b : T ⟶ D.V.scheme) (t : T) (hb : b t = D.V.point)
    (hres : IsIso (b.residueFieldMap t)) : D.BaseChangeData b t := by
  classical
  have hUaff : IsAffine D.U.scheme := D.affine_U
  have hVaff : IsAffine D.V.scheme := D.affine_V
  have hZaff : IsAffine D.Z := D.affine_Z
  have hYaff : IsAffine D.Y := D.affine_Y
  have hGq : D.G.IsQuasicoherent := D.quasicoherent_G
  have hGt : D.G.IsFiniteType := D.finiteType_G
  have hiCl : IsClosedImmersion D.i := D.closedImmersion
  -- the new base over `S`
  set bS : T ⟶ S := b ≫ D.V.toBase with hbS
  set XT : Scheme.{u} := pullback f bS
  set pX : XT ⟶ X := pullback.fst f bS with hpX
  set fT : XT ⟶ T := pullback.snd f bS with hfT
  have hsqX : IsPullback pX fT f bS := IsPullback.of_hasPullback f bS
  -- the base changes of the source neighbourhood, the smooth scheme and the closed subscheme
  set UT : Scheme.{u} := pullback D.toBase b
  set pU : UT ⟶ D.U.scheme := pullback.fst D.toBase b with hpU
  set toBaseT : UT ⟶ T := pullback.snd D.toBase b with htoBaseT
  have hsqU : IsPullback pU toBaseT D.toBase b := IsPullback.of_hasPullback _ _
  set YT : Scheme.{u} := pullback D.h b
  set pY : YT ⟶ D.Y := pullback.fst D.h b
  set hT : YT ⟶ T := pullback.snd D.h b with hhT
  have hsqY : IsPullback pY hT D.h b := IsPullback.of_hasPullback _ _
  set ZT : Scheme.{u} := pullback D.π pY
  set pZ : ZT ⟶ D.Z := pullback.fst D.π pY
  set πT : ZT ⟶ YT := pullback.snd D.π pY
  have hsqZ : IsPullback pZ πT D.π pY := IsPullback.of_hasPullback _ _
  -- the base-changed closed immersion
  have hover : (pZ ≫ D.i) ≫ D.toBase = (πT ≫ hT) ≫ b := by
    rw [Category.assoc, D.commutes_closed, ← Category.assoc, hsqZ.w, Category.assoc,
      Category.assoc, hsqY.w]
  set iT : ZT ⟶ UT := pullback.lift (pZ ≫ D.i) (πT ≫ hT) hover
  have hiTfst : iT ≫ pU = pZ ≫ D.i := pullback.lift_fst _ _ _
  have hiTsnd : iT ≫ toBaseT = πT ≫ hT := pullback.lift_snd _ _ _
  have hsqI : IsPullback pZ iT D.i pU := by
    refine (hsqU.paste_vert_iff hiTfst.symm).1 ?_
    have hc := hsqZ.paste_vert hsqY
    rwa [← D.commutes_closed, ← hiTsnd] at hc
  -- the base-changed étale neighbourhood of the source
  set uTtoX : UT ⟶ XT :=
    etaleBaseChangeMap D.toBase D.U.toBase D.V.toBase f D.commutes_base b with huTtoX
  have hEt : Etale uTtoX :=
    etale_etaleBaseChangeMap D.toBase D.U.toBase D.V.toBase f D.commutes_base b
  have huXfst : uTtoX ≫ pX = pU ≫ D.U.toBase := by
    rw [huTtoX, hpX, hpU]
    dsimp only [etaleBaseChangeMap, pullback.map]
    rw [pullback.lift_fst]
  have huXsnd : uTtoX ≫ fT = toBaseT := by
    rw [huTtoX, hfT, htoBaseT]
    dsimp only [etaleBaseChangeMap, pullback.map]
    rw [pullback.lift_snd, Category.comp_id]
  -- the distinguished points, from the bottom of the diagram upwards
  have hbIso : IsIso ((D.V.scheme.residueFieldCongr hb).inv ≫ b.residueFieldMap t) :=
    inferInstance
  set yT : YT := pullbackPointOfIsIsoResidueFieldMap D.h b (D.π D.z) t D.V.point
    D.point_base hb hbIso
  have hyTfst : pY yT = D.π D.z :=
    pullbackPointOfIsIsoResidueFieldMap_fst D.h b _ _ _ D.point_base hb hbIso
  have hyTsnd : hT yT = t :=
    pullbackPointOfIsIsoResidueFieldMap_snd D.h b _ _ _ D.point_base hb hbIso
  have hpYres : IsIso (pY.residueFieldMap yT) :=
    isIso_residueFieldMap_pullback_fst_of_right D.h b yT (by rwa [← hhT, hyTsnd])
  have hpYres' : IsIso ((D.Y.residueFieldCongr hyTfst).inv ≫ pY.residueFieldMap yT) :=
    inferInstance
  set zT : ZT := pullbackPointOfIsIsoResidueFieldMap D.π pY D.z yT (D.π D.z) rfl hyTfst
    hpYres'
  have hzTfst : pZ zT = D.z :=
    pullbackPointOfIsIsoResidueFieldMap_fst D.π pY _ _ _ rfl hyTfst hpYres'
  have hzTsnd : πT zT = yT :=
    pullbackPointOfIsIsoResidueFieldMap_snd D.π pY _ _ _ rfl hyTfst hpYres'
  set uT : UT := iT zT with huTdef
  have huTfst : pU uT = D.U.point := by
    have h1 := congrArg (fun k : ZT ⟶ D.U.scheme => k zT) hiTfst
    change pU (iT zT) = D.i (pZ zT) at h1
    rw [huTdef, h1, hzTfst, D.point_closed]
  have huTsnd : toBaseT uT = t := by
    have h1 := congrArg (fun k : ZT ⟶ T => k zT) hiTsnd
    change toBaseT (iT zT) = hT (πT zT) at h1
    rw [huTdef, h1, hzTsnd, hyTsnd]
  set xT : XT := uTtoX uT with hxTdef
  have hxTfst : pX xT = x := by
    have h1 := congrArg (fun k : UT ⟶ X => k uT) huXfst
    change pX (uTtoX uT) = D.U.toBase (pU uT) at h1
    rw [hxTdef, h1, huTfst, D.U.map_point]
  have hxTsnd : fT xT = t := by
    have h1 := congrArg (fun k : UT ⟶ T => k uT) huXsnd
    change fT (uTtoX uT) = toBaseT uT at h1
    rw [hxTdef, h1, huTsnd]
  -- the residue fields of the two new distinguished points of the top row
  have hVres : IsIso (D.V.toBase.residueFieldMap (b t)) := by
    rw [hb]
    exact (EtaleNeighborhood.isElementary_iff D.V).1 D.elementary_V
  have hbSres : IsIso (bS.residueFieldMap t) := by
    rw [hbS]
    exact isIso_residueFieldMap_comp b D.V.toBase t hres hVres
  have hpXres : IsIso (pX.residueFieldMap xT) :=
    isIso_residueFieldMap_pullback_fst_of_right f bS xT (by rwa [← hfT, hxTsnd])
  have hpUres : IsIso (pU.residueFieldMap uT) :=
    isIso_residueFieldMap_pullback_fst_of_right D.toBase b uT
      (by rwa [← htoBaseT, huTsnd])
  have hUres : IsIso (D.U.toBase.residueFieldMap (pU uT)) := by
    rw [huTfst]
    exact (EtaleNeighborhood.isElementary_iff D.U).1 D.elementary_U
  have huTtoXres : IsIso (uTtoX.residueFieldMap uT) := by
    have hcomp : IsIso ((uTtoX ≫ pX).residueFieldMap uT) := by
      rw [huXfst]
      exact isIso_residueFieldMap_comp pU D.U.toBase uT hpUres hUres
    rw [Scheme.residueFieldMap_comp] at hcomp
    have hpx : IsIso (pX.residueFieldMap (uTtoX uT)) := hpXres
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (pX.residueFieldMap (uTtoX uT))
      (uTtoX.residueFieldMap uT) hpx hcomp
  -- the base-changed finiteness properties
  have hFTq : ((Scheme.Modules.pullback pX).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ pX.toLRSHom.toShHom F ‹F.IsQuasicoherent›
  have hFTt : ((Scheme.Modules.pullback pX).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType pX.toLRSHom.toShHom F
  have hGTq : ((Scheme.Modules.pullback pZ).obj D.G).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ pZ.toLRSHom.toShHom D.G hGq
  have hGTt : ((Scheme.Modules.pullback pZ).obj D.G).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType pZ.toLRSHom.toShHom D.G
  -- the dimension of the support of the fibre module
  have hresAt : IsIso (bS.residueFieldMap (fT xT)) := by rwa [hxTsnd]
  have hxBase : f.asFiber (pX xT) ∈ SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι (f (pX xT)))).obj F) := by
    rwa [hxTfst]
  have hdimEx :=
    @topologicalKrullDimAt_fiberSupp_of_isPullback _ _ _ _ pX fT f bS hsqX F _ xT hresAt hxBase
  have hdimBase : ∀ (y : X) (_ : y = x) (hmy : f.asFiber y ∈ SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι (f y))).obj F)),
      topologicalKrullDimAt (SheafOfModules.supp
        ((Scheme.Modules.pullback (f.fiberι (f y))).obj F)) ⟨f.asFiber y, hmy⟩ = D.n := by
    intro y hy hmy
    subst hy
    exact D.dimension
  have hpointBase : hT (πT zT) = fT xT := by rwa [hzTsnd, hxTsnd]
  -- the base-changed module comparison
  have hbcIso : IsIso ((AffinePushforward.baseChangeNatTrans hsqI.w).app D.G) :=
    AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hsqI D.G
  refine
    { point := xT
      fst_point := hxTfst
      snd_point := hxTsnd
      mem_fiber_support := hdimEx.choose
      devissage :=
        { n := D.n
          dimension := hdimEx.choose_spec.trans (hdimBase (pX xT) hxTfst hxBase)
          U := { scheme := UT, point := uT, toBase := uTtoX, map_point := rfl }
          V := EtaleNeighborhood.self T (fT xT)
          elementary_U := (EtaleNeighborhood.isElementary_iff _).2 huTtoXres
          elementary_V := EtaleNeighborhood.isElementary_self T (fT xT)
          Z := ZT
          Y := YT
          toBase := toBaseT
          i := iT
          π := πT
          h := hT
          z := zT
          G := (Scheme.Modules.pullback pZ).obj D.G
          commutes_base := huXsnd.trans (Category.comp_id toBaseT).symm
          commutes_closed := hiTsnd
          point_closed := rfl
          point_base := hpointBase
          affine_U := inferInstance
          affine_V := (inferInstance : IsAffine T)
          affine_Z := inferInstance
          affine_Y := inferInstance
          closedImmersion :=
            MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqI D.closedImmersion
          finitePresentation :=
            ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqI
                D.finitePresentation.1,
              MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqI
                D.finitePresentation.2.1,
              MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqI
                D.finitePresentation.2.2⟩
          sheafIso :=
            (asIso ((AffinePushforward.baseChangeNatTrans hsqI.w).app D.G)).symm ≪≫
              (Scheme.Modules.pullback pU).mapIso D.sheafIso ≪≫
              (Scheme.Modules.pullbackComp pU D.U.toBase).app F ≪≫
              (Scheme.Modules.pullbackCongr huXfst.symm).app F ≪≫
              ((Scheme.Modules.pullbackComp uTtoX pX).app F).symm
          finiteType_G := hGTt
          quasicoherent_G := hGTq
          finite_π := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqZ D.finite_π
          singleton_fiber := ?_
          pureTranscendental := ?_
          smooth := ?_
          integral_fibers := ?_ }
      dimension_eq := rfl
      base_neighborhood := rfl }
  · -- the fibre of the base-changed finite morphism through the new point is a single point
    intro w
    refine ⟨fun hw => ?_, fun hw => by rw [hw]⟩
    have hwy : πT w = yT := by rw [hw, hzTsnd]
    have hwz : pZ w = D.z := by
      refine (D.singleton_fiber (pZ w)).1 ?_
      have h1 := congrArg (fun k : ZT ⟶ D.Y => k w) hsqZ.w
      change D.π (pZ w) = pY (πT w) at h1
      rw [h1, hwy, hyTfst]
    exact pullback_point_eq_of_isIso_residueFieldMap D.π pY D.z yT hyTfst.symm
      hpYres' w zT hwz hwy hzTfst hzTsnd
  · -- pure transcendence of the residue field of the new point of the smooth scheme
    have hbx : b (fT xT) = D.V.point := by rwa [hxTsnd]
    have hxy : pY (πT zT) = D.π D.z := by rwa [hzTsnd]
    have hE : IsIso ((D.Y.residueFieldCongr hxy).inv ≫ pY.residueFieldMap (πT zT)) := by
      have : IsIso (pY.residueFieldMap (πT zT)) :=
        (pY.isIso_residueFieldMap_congr hzTsnd).2 hpYres
      infer_instance
    have hbxIso : IsIso ((D.V.scheme.residueFieldCongr hbx).inv ≫
        b.residueFieldMap (fT xT)) := by
      have := (b.isIso_residueFieldMap_congr hxTsnd).2 hres
      infer_instance
    let instOld : Algebra (D.V.scheme.residueField D.V.point)
        (D.Y.residueField (D.π D.z)) :=
      ((D.V.scheme.residueFieldCongr D.point_base).inv ≫
        D.h.residueFieldMap (D.π D.z)).hom.toAlgebra
    let instNew : Algebra (T.residueField (fT xT)) (YT.residueField (πT zT)) :=
      ((T.residueFieldCongr hpointBase).inv ≫ hT.residueFieldMap (πT zT)).hom.toAlgebra
    change @PurelyTranscendental _ _ _ _ instNew
    refine @PurelyTranscendental.of_ringEquiv_square _ _ _ _ _ _ _ _ instOld instNew
      (asIso ((D.V.scheme.residueFieldCongr hbx).inv ≫
        b.residueFieldMap (fT xT))).commRingCatIsoToRingEquiv
      (asIso ((D.Y.residueFieldCongr hxy).inv ≫
        pY.residueFieldMap (πT zT))).commRingCatIsoToRingEquiv ?_ D.pureTranscendental
    exact congrArg CommRingCat.Hom.hom
      (residueFieldMap_square D.h hT pY b hsqY.w (πT zT) (D.π D.z) (fT xT) D.V.point hxy hbx
        D.point_base hpointBase).symm
  · -- the base-changed structure morphism is smooth of the same relative dimension
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension D.n) :=
      smoothOfRelativeDimension_isStableUnderBaseChange D.n
    exact MorphismProperty.of_isPullback hsqY D.smooth
  · -- the fibres of the base-changed structure morphism stay geometrically integral
    have hGI : GeometricallyIntegral D.h :=
      (GeometricallyIntegral.iff_geometricallyIntegral_fiber D.h).2 D.integral_fibers
    exact (GeometricallyIntegral.iff_geometricallyIntegral_fiber hT).1
      (MorphismProperty.of_isPullback hsqY hGI)

/-- The base change of an elementary dévissage to the spectrum of the local ring of its base
neighbourhood at the distinguished point. This is literally the replacement of `S` by
`Spec 𝒪_{S', s'}` made in the first proof of Stacks 05I5. -/
def baseChangeStalk (D : ElementaryDevissage f F x hx) [F.IsQuasicoherent] [F.IsFiniteType] :
    D.BaseChangeData (D.V.scheme.fromSpecStalk D.V.point)
      (IsLocalRing.closedPoint (D.V.scheme.presheaf.stalk D.V.point)) :=
  D.baseChange _ _ Scheme.fromSpecStalk_closedPoint
    (isIso_residueFieldMap_of_isPreimmersion _ _)

end ElementaryDevissage

end AlgebraicGeometry

end
