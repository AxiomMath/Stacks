module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.BaseChange
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Base change of a complete dévissage

A complete dévissage stays complete after an arbitrary change of pointed base schemes with
affine new base. The resulting stages, modules and free-module maps are the base changes of
the original ones.

## Main definitions

* `AlgebraicGeometry.DevissageStage.baseChange`: the base change of a stage of a complete
  dévissage, along a one-step dévissage of the base-changed situation realizing the base
  change of the given one.
* `AlgebraicGeometry.StageIsBaseChange`: the cartesian diagrams and the compatibility of the
  free-module map with affine base change, exhibiting one stage as a base change of another.
* `AlgebraicGeometry.ChainIsBaseChange`: the same at every stage of a chain.

## Main results

* `AlgebraicGeometry.cokernelIsoOfAlphaComparison`: the comparison of the cokernels of the
  free-module maps of two stages whose finite morphisms sit in a cartesian square and whose
  free-module maps correspond.
* `AlgebraicGeometry.cokernelIsoOfStageIsBaseChange`: the cokernel of the free-module map of a
  base-changed stage is the base change of the cokernel of the original one.
* `AlgebraicGeometry.exists_completeDevissage_baseChange`: a complete dévissage base-changes
  to a complete dévissage, stagewise.

## Implementation notes

The base-changed module is the inverse image of the original module, up to a prescribed
isomorphism, and the comparison of the direct images is the canonical base-change morphism
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, which is invertible here
because the finite morphism of a stage is affine. The free-module comparison is the canonical
identification `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso` of the inverse image of a
free module with a free module of the same rank.

Nothing is tied to the canonical fibre product `X ×_S S'`: the construction takes the
base-changed source as an arbitrary scheme sitting in a cartesian square, and likewise takes
an arbitrary one-step dévissage of the base-changed situation realizing the base change of
the given one. This is what makes the induction over a chain go through without transporting
the tail along an isomorphism of the ambient scheme: the inductive step applies the
hypothesis to the smooth scheme of the base-changed stage directly.

The generic point of the distinguished fibre of the base-changed stage is the generic point
of that fibre, which exists because the smooth structure morphism is geometrically
irreducible; it maps to the generic point of the original fibre because the comparison of
fibres attached to a cartesian square is surjective.

## References

* [Stacks Project, Tag 05HJ](https://stacks.math.columbia.edu/tag/05HJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section Stage

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {F : X.Modules} {F' : X'.Modules}
  {s : S} {s' : S'} {h : S' ⟶ S}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
  [LocallyOfFiniteType f'] [F'.IsQuasicoherent] [F'.IsFiniteType]

/-- The free-module map of the base change of a stage: the inverse image of the original
free-module map, read through the canonical identification of the inverse image of a free
module and through the base-change comparison of the direct images. -/
def baseChangedAlpha (D : DevissageStage f F s) (E : OneStepDevissage f' F' s')
    {pY : E.Y ⟶ D.oneStep.Y} {pZ : E.Z ⟶ D.oneStep.Z}
    (hz : IsPullback pZ E.π D.oneStep.π pY)
    (hG : E.G = (Scheme.Modules.pullback pZ).obj D.oneStep.G) :
    SheafOfModules.free (R := E.Y.ringCatSheaf) (ULift.{u} (Fin D.rank)) ⟶
      (Scheme.Modules.pushforward E.π).obj E.G :=
  (Scheme.Modules.pullbackFreeIso pY (ULift.{u} (Fin D.rank))).inv ≫
    (Scheme.Modules.pullback pY).map D.alpha ≫
    (AffinePushforward.baseChangeNatTrans hz.w).app D.oneStep.G ≫
    (Scheme.Modules.pushforward E.π).map (eqToHom hG.symm)

/-- The point of the smooth scheme of a base-changed stage lying under the generic point of
its distinguished fibre maps to the corresponding point of the original stage. -/
lemma pY_fiberι_genericPoint (hs : h s' = s) (D : DevissageStage f F s)
    (E : OneStepDevissage f' F' s') {pY : E.Y ⟶ D.oneStep.Y}
    (hy : IsPullback pY E.g D.oneStep.g h) {η : E.g.fiber s'}
    (hη : IsGenericPoint η Set.univ) :
    pY (E.g.fiberι s' η) = D.oneStep.g.fiberι s D.genericPoint := by
  have : GeometricallyIrreducible D.oneStep.g := D.oneStep.geometrically_irreducible
  have : GeometricallyIrreducible E.g := E.geometrically_irreducible
  have hcomm := congrArg (fun k : E.g.fiber s' ⟶ D.oneStep.Y => k.base η)
    (fiberMapOfIsPullback_comp_fiberι hy s')
  calc
    pY (E.g.fiberι s' η) =
        D.oneStep.g.fiberι (h s') (fiberMapOfIsPullback hy s' η) := by
      simpa using hcomm.symm
    _ = D.oneStep.g.fiberι s D.genericPoint := by
      rw [fiberMapOfIsPullback_genericPoint hy hs hη D.genericPoint_spec]
      cases hs
      simp [fiberIsoOfEq]

/-- The free-module map of a base-changed stage is an isomorphism over the residue field of any
point of the base-changed smooth scheme lying over the generic point of the distinguished fibre
of the original stage. -/
lemma isIso_baseChangedAlpha_of_map_eq (D : DevissageStage f F s)
    (E : OneStepDevissage f' F' s') {pY : E.Y ⟶ D.oneStep.Y} {pZ : E.Z ⟶ D.oneStep.Z}
    (hz : IsPullback pZ E.π D.oneStep.π pY)
    (hG : E.G = (Scheme.Modules.pullback pZ).obj D.oneStep.G) {η : E.g.fiber s'}
    (hη : pY (E.g.fiberι s' η) = D.oneStep.g.fiberι s D.genericPoint) :
    IsIso ((Scheme.Modules.pullback (E.Y.fromSpecResidueField (E.g.fiberι s' η))).map
      (baseChangedAlpha D E hz hG)) := by
  have : D.oneStep.G.IsQuasicoherent := D.oneStep.quasi_coherent_G
  have : IsFinite D.oneStep.π := D.oneStep.finite
  have : IsAffineHom D.oneStep.π := D.oneStep.finite.toIsAffineHom
  have hpt : IsIso ((Scheme.Modules.pullback
      (D.oneStep.Y.fromSpecResidueField (pY (E.g.fiberι s' η)))).map D.alpha) := by
    rw [hη]
    exact D.genericFiber_isIso
  have := isIso_pullback_map_fromSpecResidueField pY D.alpha (E.g.fiberι s' η) hpt
  have : IsIso ((AffinePushforward.baseChangeNatTrans hz.w).app D.oneStep.G) :=
    AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hz D.oneStep.G
  suffices hiso : IsIso ((Scheme.Modules.pullback
      (E.Y.fromSpecResidueField (E.g.fiberι s' η))).map
        ((Scheme.Modules.pullbackFreeIso pY (ULift.{u} (Fin D.rank))).inv ≫
          (Scheme.Modules.pullback pY).map D.alpha ≫
          (AffinePushforward.baseChangeNatTrans hz.w).app D.oneStep.G ≫
          (Scheme.Modules.pushforward E.π).map (eqToHom hG.symm))) from hiso
  have : IsIso (Scheme.Modules.pullbackFreeIso pY (ULift.{u} (Fin D.rank))).inv :=
    Iso.isIso_inv _
  refine Functor.isIso_map_comp _ _ _ (Functor.map_isIso _ _) ?_
  refine Functor.isIso_map_comp _ _ _ inferInstance ?_
  exact Functor.isIso_map_comp _ _ _ (Functor.map_isIso _ _) (Functor.map_isIso _ _)

/-- The free-module map of a base-changed stage is again an isomorphism over the residue
field of the generic point of the distinguished fibre. -/
lemma isIso_baseChangedAlpha_genericFiber (hs : h s' = s) (D : DevissageStage f F s)
    (E : OneStepDevissage f' F' s') {pY : E.Y ⟶ D.oneStep.Y} {pZ : E.Z ⟶ D.oneStep.Z}
    (hy : IsPullback pY E.g D.oneStep.g h) (hz : IsPullback pZ E.π D.oneStep.π pY)
    (hG : E.G = (Scheme.Modules.pullback pZ).obj D.oneStep.G) {η : E.g.fiber s'}
    (hη : IsGenericPoint η Set.univ) :
    IsIso ((Scheme.Modules.pullback (E.Y.fromSpecResidueField (E.g.fiberι s' η))).map
      (baseChangedAlpha D E hz hG)) :=
  isIso_baseChangedAlpha_of_map_eq D E hz hG (pY_fiberι_genericPoint hs D E hy hη)

/-- The generic point of the distinguished fibre of a one-step dévissage: the fibre is
irreducible because the smooth structure morphism is geometrically irreducible. -/
def OneStepDevissage.fiberGenericPoint (E : OneStepDevissage f' F' s') : E.g.fiber s' :=
  have : GeometricallyIrreducible E.g := E.geometrically_irreducible
  genericPoint (E.g.fiber s')

/-- `OneStepDevissage.fiberGenericPoint` is the generic point of the distinguished fibre. -/
lemma OneStepDevissage.isGenericPoint_fiberGenericPoint (E : OneStepDevissage f' F' s') :
    IsGenericPoint E.fiberGenericPoint Set.univ :=
  have : GeometricallyIrreducible E.g := E.geometrically_irreducible
  genericPoint_spec _

/-- The base change of a stage of a complete dévissage along a one-step dévissage of the
base-changed situation realizing the base change of the given one. The rank is unchanged and
the free-module map is `AlgebraicGeometry.baseChangedAlpha`. -/
def DevissageStage.baseChange (hs : h s' = s) (D : DevissageStage f F s)
    (E : OneStepDevissage f' F' s') {pY : E.Y ⟶ D.oneStep.Y} {pZ : E.Z ⟶ D.oneStep.Z}
    (hy : IsPullback pY E.g D.oneStep.g h) (hz : IsPullback pZ E.π D.oneStep.π pY)
    (hG : E.G = (Scheme.Modules.pullback pZ).obj D.oneStep.G) :
    DevissageStage f' F' s' where
  oneStep := E
  rank := D.rank
  alpha := baseChangedAlpha D E hz hG
  genericPoint := E.fiberGenericPoint
  genericPoint_spec := E.isGenericPoint_fiberGenericPoint
  genericFiber_isIso :=
    isIso_baseChangedAlpha_genericFiber hs D E hy hz hG E.isGenericPoint_fiberGenericPoint

/-- One stage of a complete dévissage is the base change of another: the three cartesian
squares, the identification of the modules and the compatibility of the free-module maps with
affine base change. -/
structure StageIsBaseChange (h : S' ⟶ S) (pX : X' ⟶ X) (D : DevissageStage f F s)
    (D' : DevissageStage f' F' s') where
  /-- The base-changed smooth scheme. -/
  pY : D'.oneStep.Y ⟶ D.oneStep.Y
  /-- The base-changed closed subscheme. -/
  pZ : D'.oneStep.Z ⟶ D.oneStep.Z
  y_square : IsPullback pY D'.oneStep.g D.oneStep.g h
  x_square : IsPullback pZ D'.oneStep.i D.oneStep.i pX
  z_square : IsPullback pZ D'.oneStep.π D.oneStep.π pY
  G_eq : D'.oneStep.G = (Scheme.Modules.pullback pZ).obj D.oneStep.G
  rank_eq : D'.rank = D.rank
  /-- The free-module map of the second stage is the base change of that of the first. -/
  alpha_baseChange :
    (Scheme.Modules.pullback pY).map D.alpha ≫
        (AffinePushforward.baseChangeNatTrans z_square.w).app D.oneStep.G ≫
        (Scheme.Modules.pushforward D'.oneStep.π).map (eqToHom G_eq.symm) =
      (Scheme.Modules.pullbackFreeIso pY (ULift.{u} (Fin D.rank))).hom ≫
      SheafOfModules.freeMap (R := D'.oneStep.Y.ringCatSheaf)
        (fun i : ULift.{u} (Fin D.rank) => ULift.up (Fin.cast rank_eq.symm i.down)) ≫
        D'.alpha

/-- The free-module map of a base change is the base change of the free-module map. -/
lemma baseChangedAlpha_comp (D : DevissageStage f F s) (E : OneStepDevissage f' F' s')
    {pY : E.Y ⟶ D.oneStep.Y} {pZ : E.Z ⟶ D.oneStep.Z}
    (hz : IsPullback pZ E.π D.oneStep.π pY)
    (hG : E.G = (Scheme.Modules.pullback pZ).obj D.oneStep.G) :
    (Scheme.Modules.pullback pY).map D.alpha ≫
        (AffinePushforward.baseChangeNatTrans hz.w).app D.oneStep.G ≫
        (Scheme.Modules.pushforward E.π).map (eqToHom hG.symm) =
      (Scheme.Modules.pullbackFreeIso pY (ULift.{u} (Fin D.rank))).hom ≫
        SheafOfModules.freeMap (R := E.Y.ringCatSheaf)
          (fun i : ULift.{u} (Fin D.rank) => ULift.up (Fin.cast rfl i.down)) ≫
        baseChangedAlpha D E hz hG := by
  symm
  refine Eq.trans (congrArg
    (fun k => (Scheme.Modules.pullbackFreeIso pY (ULift.{u} (Fin D.rank))).hom ≫ k ≫
      baseChangedAlpha D E hz hG) SheafOfModules.freeMap_finCast_rfl) ?_
  refine Eq.trans (congrArg
    (fun k => (Scheme.Modules.pullbackFreeIso pY (ULift.{u} (Fin D.rank))).hom ≫ k)
    (Category.id_comp (baseChangedAlpha D E hz hG))) ?_
  exact Iso.hom_inv_id_assoc (Scheme.Modules.pullbackFreeIso pY (ULift.{u} (Fin D.rank))) _

/-- The base change of a stage is a base change of it. -/
def DevissageStage.isBaseChange_baseChange (hs : h s' = s) (D : DevissageStage f F s)
    (E : OneStepDevissage f' F' s') (pX : X' ⟶ X) {pY : E.Y ⟶ D.oneStep.Y}
    {pZ : E.Z ⟶ D.oneStep.Z} (hy : IsPullback pY E.g D.oneStep.g h)
    (hx : IsPullback pZ E.i D.oneStep.i pX) (hz : IsPullback pZ E.π D.oneStep.π pY)
    (hG : E.G = (Scheme.Modules.pullback pZ).obj D.oneStep.G) :
    StageIsBaseChange h pX D (D.baseChange hs E hy hz hG) where
  pY := pY
  pZ := pZ
  y_square := hy
  x_square := hx
  z_square := hz
  G_eq := hG
  rank_eq := rfl
  alpha_baseChange := baseChangedAlpha_comp D E hz hG

/-- The comparison of cokernels available whenever the square of the finite morphisms of two
stages is cartesian, the module on the second closed subscheme is the inverse image of the
first, the ranks agree and the free-module maps correspond: the cokernel of the second stage is
the inverse image of the cokernel of the first. Both the base change and the standard
restriction of a stage supply this data. -/
def cokernelIsoOfAlphaComparison {D : DevissageStage f F s} {D' : DevissageStage f' F' s'}
    {pY : D'.oneStep.Y ⟶ D.oneStep.Y} {pZ : D'.oneStep.Z ⟶ D.oneStep.Z}
    (hz : IsPullback pZ D'.oneStep.π D.oneStep.π pY)
    (hG : D'.oneStep.G = (Scheme.Modules.pullback pZ).obj D.oneStep.G)
    (hrank : D'.rank = D.rank)
    (halpha : (Scheme.Modules.pullback pY).map D.alpha ≫
        (AffinePushforward.baseChangeNatTrans hz.w).app D.oneStep.G ≫
        (Scheme.Modules.pushforward D'.oneStep.π).map (eqToHom hG.symm) =
      (Scheme.Modules.pullbackFreeIso pY (ULift.{u} (Fin D.rank))).hom ≫
      SheafOfModules.freeMap (R := D'.oneStep.Y.ringCatSheaf)
        (fun i : ULift.{u} (Fin D.rank) => ULift.up (Fin.cast hrank.symm i.down)) ≫ D'.alpha) :
    (Scheme.Modules.pullback pY).obj D.coker ≅ D'.coker := by
  have : D.oneStep.G.IsQuasicoherent := D.oneStep.quasi_coherent_G
  have : IsFinite D.oneStep.π := D.oneStep.finite
  have : IsAffineHom D.oneStep.π := D.oneStep.finite.toIsAffineHom
  have : IsIso ((AffinePushforward.baseChangeNatTrans hz.w).app D.oneStep.G) :=
    AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom hz D.oneStep.G
  exact PreservesCokernel.iso (Scheme.Modules.pullback pY) D.alpha ≪≫
    cokernel.mapIso ((Scheme.Modules.pullback pY).map D.alpha) D'.alpha
      (Scheme.Modules.pullbackFreeIso pY (ULift.{u} (Fin D.rank)) ≪≫
        eqToIso (congrArg (fun k => SheafOfModules.free
          (R := D'.oneStep.Y.ringCatSheaf) (ULift.{u} (Fin k))) hrank.symm))
      (asIso ((AffinePushforward.baseChangeNatTrans hz.w).app D.oneStep.G) ≪≫
        (Scheme.Modules.pushforward D'.oneStep.π).mapIso (eqToIso hG.symm))
      (halpha.trans
        ((congrArg (fun k => (Scheme.Modules.pullbackFreeIso pY
              (ULift.{u} (Fin D.rank))).hom ≫ k ≫ D'.alpha)
            (SheafOfModules.freeMap_finCast_eq_eqToHom hrank.symm)).trans
          (Category.assoc _ _ _).symm))

/-- The cokernel of the free-module map of a base-changed stage is the inverse image of the
cokernel of the free-module map of the original stage. -/
def cokernelIsoOfStageIsBaseChange {pX : X' ⟶ X} {D : DevissageStage f F s}
    {D' : DevissageStage f' F' s'} (hstage : StageIsBaseChange h pX D D') :
    (Scheme.Modules.pullback hstage.pY).obj D.coker ≅ D'.coker :=
  cokernelIsoOfAlphaComparison hstage.z_square hstage.G_eq hstage.rank_eq
    hstage.alpha_baseChange

/-- A stage whose free-module map has zero cokernel base-changes to a stage whose
free-module map has zero cokernel. -/
lemma isZero_coker_of_stageIsBaseChange {pX : X' ⟶ X} {D : DevissageStage f F s}
    {D' : DevissageStage f' F' s'} (hstage : StageIsBaseChange h pX D D')
    (hz : IsZero D.coker) : IsZero D'.coker :=
  ((Scheme.Modules.pullback hstage.pY).map_isZero hz).of_iso
    (cokernelIsoOfStageIsBaseChange hstage).symm

/-- A one-step dévissage base-changes along an arbitrary cartesian square over an affine new
base: Stacks 05H7 produces it over the canonical fibre product, and it is carried from there
to the given source by `AlgebraicGeometry.OneStepDevissage.ofSourceIso`. -/
theorem OneStepDevissage.exists_baseChange_of_isPullback (hs : h s' = s) [IsAffine S']
    (D : OneStepDevissage f F s) {pX : X' ⟶ X} (hX : IsPullback pX f' f h)
    (eF : (Scheme.Modules.pullback pX).obj F ≅ F') :
    ∃ (E : OneStepDevissage f' F' s') (pY : E.Y ⟶ D.Y) (pZ : E.Z ⟶ D.Z),
      IsPullback pY E.g D.g h ∧ IsPullback pZ E.i D.i pX ∧ IsPullback pZ E.π D.π pY ∧
        E.G = (Scheme.Modules.pullback pZ).obj D.G := by
  let B := OneStepDevissage.baseChange f F s s' h hs D
  have := B.locallyOfFiniteType
  have := B.quasicoherent
  have := B.finiteType
  have hfst : hX.isoPullback.hom ≫ Limits.pullback.fst f h = pX := hX.isoPullback_hom_fst
  refine ⟨OneStepDevissage.ofSourceIso hX.isoPullback hX.isoPullback_hom_snd
      ((Scheme.Modules.pullbackComp hX.isoPullback.hom (Limits.pullback.fst f h)).app F ≪≫
        (Scheme.Modules.pullbackCongr hfst).app F ≪≫ eF) B.devissage,
    B.pY, B.pZ, B.y_square, ?_, B.z_square, B.module_eq⟩
  rw [OneStepDevissage.ofSourceIso_i]
  refine B.x_square.of_iso (Iso.refl _) (Iso.refl _) hX.isoPullback.symm (Iso.refl _)
    ?_ ?_ ?_ ?_ <;> simp

/-- A stage of a complete dévissage base-changes to a stage over an affine new base, along any
cartesian square. -/
private theorem exists_stageIsBaseChange (hs : h s' = s) [IsAffine S'] (D : DevissageStage f F s)
    {pX : X' ⟶ X} (hX : IsPullback pX f' f h) (eF : (Scheme.Modules.pullback pX).obj F ≅ F') :
    ∃ D' : DevissageStage f' F' s', Nonempty (StageIsBaseChange h pX D D') := by
  obtain ⟨E, pY, pZ, hy, hx, hzq, hG⟩ :=
    OneStepDevissage.exists_baseChange_of_isPullback hs D.oneStep hX eF
  exact ⟨_, ⟨D.isBaseChange_baseChange hs E pX hy hx hzq hG⟩⟩

end Stage

/-- Every stage of a complete dévissage chain is a base change of the corresponding stage of
another one. -/
inductive ChainIsBaseChange {S S' : Scheme.{u}} {s : S} {s' : S'} (h : S' ⟶ S) :
    {X : Scheme.{u}} → {f : X ⟶ S} → {F : X.Modules} → {hl : LocallyOfFiniteType f} →
      {hq : F.IsQuasicoherent} → {ht : F.IsFiniteType} →
      {X' : Scheme.{u}} → {f' : X' ⟶ S'} → {F' : X'.Modules} →
      {hl' : LocallyOfFiniteType f'} → {hq' : F'.IsQuasicoherent} →
      {ht' : F'.IsFiniteType} → (pX : X' ⟶ X) →
      DevissageChain s X f F hl hq ht → DevissageChain s' X' f' F' hl' hq' ht' → Prop where
  /-- The final stages correspond. -/
  | last {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {X' : Scheme.{u}} {f' : X' ⟶ S'}
      {F' : X'.Modules} [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent]
      [ht : F.IsFiniteType] [hl' : LocallyOfFiniteType f'] [hq' : F'.IsQuasicoherent]
      [ht' : F'.IsFiniteType] {pX : X' ⟶ X}
      {D : @DevissageStage X S f F s hl hq ht}
      {D' : @DevissageStage X' S' f' F' s' hl' hq' ht'}
      (hstage : @StageIsBaseChange X S X' S' f f' F F' s s' hl hq ht hl' hq' ht' h pX D D')
      (hz : IsZero D.coker) (hz' : IsZero D'.coker) :
      ChainIsBaseChange h pX (.last D hz) (.last D' hz')
  /-- A nonfinal stage corresponds, and so does the dévissage of its cokernel. -/
  | more {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {X' : Scheme.{u}} {f' : X' ⟶ S'}
      {F' : X'.Modules} [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent]
      [ht : F.IsFiniteType] [hl' : LocallyOfFiniteType f'] [hq' : F'.IsQuasicoherent]
      [ht' : F'.IsFiniteType] {pX : X' ⟶ X}
      {D : @DevissageStage X S f F s hl hq ht}
      {D' : @DevissageStage X' S' f' F' s' hl' hq' ht'}
      {hqC : D.coker.IsQuasicoherent} {htC : D.coker.IsFiniteType}
      {hlY : LocallyOfFiniteType D.oneStep.g} {hqC' : D'.coker.IsQuasicoherent}
      {htC' : D'.coker.IsFiniteType} {hlY' : LocallyOfFiniteType D'.oneStep.g}
      {tail : DevissageChain s D.oneStep.Y D.oneStep.g D.coker hlY hqC htC}
      {tail' : DevissageChain s' D'.oneStep.Y D'.oneStep.g D'.coker hlY' hqC' htC'}
      (hstage : @StageIsBaseChange X S X' S' f f' F F' s s' hl hq ht hl' hq' ht' h pX D D')
      (htail : ChainIsBaseChange h hstage.pY tail tail') :
      ChainIsBaseChange h pX (.more D hqC htC hlY tail) (.more D' hqC' htC' hlY' tail')

section Chain

variable {S S' : Scheme.{u}} {s : S} {s' : S'} {h : S' ⟶ S}

/-- Stagewise base change of a complete dévissage chain: the inductive step applies the
hypothesis to the smooth scheme of the base-changed stage, whose structure morphism sits in a
cartesian square over the smooth scheme of the original stage. -/
private theorem exists_devissageChain_baseChange (hs : h s' = s) [IsAffine S']
    {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {hl : LocallyOfFiniteType f}
    {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} (C : DevissageChain s X f F hl hq ht) :
    ∀ {X' : Scheme.{u}} {f' : X' ⟶ S'} (pX : X' ⟶ X), IsPullback pX f' f h →
      ∀ {F' : X'.Modules} (hl' : LocallyOfFiniteType f') (hq' : F'.IsQuasicoherent)
        (ht' : F'.IsFiniteType), ((Scheme.Modules.pullback pX).obj F ≅ F') →
        ∃ C' : DevissageChain s' X' f' F' hl' hq' ht', ChainIsBaseChange h pX C C' := by
  induction C with
  | last D hz =>
    intro X' f' pX hX F' hl' hq' ht' eF
    have := hl'
    have := hq'
    have := ht'
    obtain ⟨D', ⟨hstage⟩⟩ := exists_stageIsBaseChange hs D hX eF
    have hz' := isZero_coker_of_stageIsBaseChange hstage hz
    exact ⟨.last D' hz', .last hstage hz hz'⟩
  | more D hqC htC hlY tail ih =>
    intro X' f' pX hX F' hl' hq' ht' eF
    have := hl'
    have := hq'
    have := ht'
    obtain ⟨D', ⟨hstage⟩⟩ := exists_stageIsBaseChange hs D hX eF
    have hqC' : D'.coker.IsQuasicoherent :=
      SheafOfModules.isQuasicoherent_of_iso (cokernelIsoOfStageIsBaseChange hstage)
        (Stacks.Modules.isQuasicoherent_pullback hstage.pY D.coker hqC)
    have htC' : D'.coker.IsFiniteType := by
      have := htC
      exact SheafOfModules.isFiniteType_of_iso (cokernelIsoOfStageIsBaseChange hstage)
        (SheafOfModules.pullback_isFiniteType hstage.pY.toLRSHom.toShHom D.coker)
    have hlY' : LocallyOfFiniteType D'.oneStep.g :=
      have := D'.oneStep.smooth
      inferInstanceAs (LocallyOfFiniteType D'.oneStep.g)
    obtain ⟨tail', htail⟩ := ih hstage.pY hstage.y_square hlY' hqC' htC'
      (cokernelIsoOfStageIsBaseChange hstage)
    exact ⟨.more D' hqC' htC' hlY' tail', .more hstage htail⟩

/-- **Stacks 05HJ.** A complete dévissage of `F/X/S` over `s` base-changes, stage by stage, to
a complete dévissage of the base-changed module over `s'`, for any cartesian square whose
new base is affine. -/
@[stacks 05HJ]
theorem exists_completeDevissage_baseChange {X X' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {F : X.Modules} {F' : X'.Modules} (hs : h s' = s) [IsAffine S'] [LocallyOfFiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType] [LocallyOfFiniteType f'] [F'.IsQuasicoherent]
    [F'.IsFiniteType] (D : NonemptyCompleteDevissage f F s) (pX : X' ⟶ X)
    (hX : IsPullback pX f' f h) (eF : (Scheme.Modules.pullback pX).obj F ≅ F') :
    ∃ D' : NonemptyCompleteDevissage f' F' s', ChainIsBaseChange h pX D.chain D'.chain := by
  obtain ⟨C', hC'⟩ := exists_devissageChain_baseChange hs D.chain pX hX _ _ _ eF
  exact ⟨⟨C'⟩, hC'⟩

/-- The base change of a complete dévissage along the canonical fibre product `X ×_S S'`,
together with the finiteness properties of the base-changed module that the construction
needs. -/
theorem exists_completeDevissage_baseChange_pullback {X : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (hs : h s' = s) [IsAffine S'] [LocallyOfFiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType] (D : NonemptyCompleteDevissage f F s) :
    ∃ (hl' : LocallyOfFiniteType (Limits.pullback.snd f h))
      (hq' : ((Scheme.Modules.pullback (Limits.pullback.fst f h)).obj F).IsQuasicoherent)
      (ht' : ((Scheme.Modules.pullback (Limits.pullback.fst f h)).obj F).IsFiniteType),
      ∃ D' : @NonemptyCompleteDevissage (Limits.pullback f h) S' (Limits.pullback.snd f h)
        ((Scheme.Modules.pullback (Limits.pullback.fst f h)).obj F) s' hl' hq' ht',
        ChainIsBaseChange h (Limits.pullback.fst f h) D.chain D'.chain := by
  have hX : IsPullback (Limits.pullback.fst f h) (Limits.pullback.snd f h) f h :=
    IsPullback.of_hasPullback f h
  have hl' : LocallyOfFiniteType (Limits.pullback.snd f h) :=
    MorphismProperty.of_isPullback hX (P := @LocallyOfFiniteType) inferInstance
  have hq' : ((Scheme.Modules.pullback (Limits.pullback.fst f h)).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (Limits.pullback.fst f h) F inferInstance
  have ht' : ((Scheme.Modules.pullback (Limits.pullback.fst f h)).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (Limits.pullback.fst f h).toLRSHom.toShHom F
  have := hl'
  have := hq'
  have := ht'
  obtain ⟨D', hD'⟩ := exists_completeDevissage_baseChange hs D (Limits.pullback.fst f h) hX
    (Iso.refl _)
  exact ⟨hl', hq', ht', D', hD'⟩

end Chain

end AlgebraicGeometry

end
