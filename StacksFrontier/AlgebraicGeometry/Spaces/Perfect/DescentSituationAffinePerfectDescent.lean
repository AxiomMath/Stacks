module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituationSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsStagesColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsStagesModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StagesColimitRingCocone
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelAffinePointTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointTensorDescent

/-!
# Perfect objects descend along a limit of algebraic spaces over an affine stage

Let `X = lim Xᵢ` be a limit of quasi-compact and quasi-separated algebraic spaces with affine
transition morphisms (Situation 09RH, `AlgebraicGeometry.Space.DescentSituation`) whose charts are
bounded in size (`AlgebraicGeometry.Space.ChartsBounded`), and suppose the chosen stage `X₀` is
affine. Then every perfect object `E` of `D(𝒪_X)` (on the model of the spaces-étale site) is
`Lfᵢ^* Eᵢ` for some stage `i ≥ 0` and some perfect object `Eᵢ` of `D(𝒪_{Xᵢ})`.

This is the affine case of the essential surjectivity half of Stacks 09RJ. The proof is the
source's: the limit `X` is affine, its projection to `X₀` being affine
(`AlgebraicGeometry.Space.DescentSituation.isAffineHom_limitCone_π_of_chartsBounded`); `E` is
`𝒪_X ⊗_A C` for a bounded complex `C` of finite projective modules over `A = Γ(X, 𝒪_X)`
(`AlgebraicGeometry.Space.exists_finiteProjective_pointTensor_iso_of_isPerfect_of_iso`);
`A = colim Γ(Xᵢ, 𝒪_{Xᵢ})` (Stacks 07SI for the structure sheaf,
`AlgebraicGeometry.Space.LimitSituation.isStagesColimit_globalFunctions_of_chartsBounded`, with
the chart `X₀ ≅ h_{T₀}` of the affine stage); so `C` descends to a stage (Stacks 0BC7), and
`𝒪_{Xᵢ} ⊗_{Aᵢ} Cᵢ` pulls back to `𝒪_X ⊗_A C`
(`AlgebraicGeometry.Space.exists_isPerfect_derivedPullback_iso_of_pointTensor`).

## Main results

* `AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_derivedPullback_iso_of_isAffineSpace`.

## References

* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 0BC7](https://stacks.math.columbia.edu/tag/0BC7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace AlgebraicGeometry.Space

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

namespace LimitSituation

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : LimitSituation B S hS hZ X)

/-- **The rings of global functions of the stages above the chosen one**, shrunk to the universe
of the site, as a functor on the stages. -/
def stagesGlobalFunctions : A.Stages ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (Shrink.{u} (globalFunctions' B S hS (A.stage i.1).1))
  map {i j} h := CommRingCat.ofHom ((Shrink.ringEquiv _).symm.toRingHom.comp
    ((globalFunctionsMap B S hS (A.transition (leOfHom h))).comp (Shrink.ringEquiv _).toRingHom))
  map_id i := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change (Shrink.ringEquiv _).symm (globalFunctionsMap B S hS (A.transition (le_refl i.1))
      (Shrink.ringEquiv _ x)) = x
    rw [transition_self, globalFunctionsMap_id, RingHom.id_apply, RingEquiv.symm_apply_apply]
  map_comp {i j k} h h' := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    change (Shrink.ringEquiv _).symm (globalFunctionsMap B S hS
        (A.transition (leOfHom (h ≫ h'))) (Shrink.ringEquiv _ x)) =
      (Shrink.ringEquiv _).symm (globalFunctionsMap B S hS (A.transition (leOfHom h'))
        (Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm
          (globalFunctionsMap B S hS (A.transition (leOfHom h)) (Shrink.ringEquiv _ x)))))
    rw [RingEquiv.apply_symm_apply, ← A.transition_comp (leOfHom h) (leOfHom h')
      (leOfHom (h ≫ h')), globalFunctionsMap_comp, RingHom.comp_apply]

end LimitSituation

namespace DescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)

/-- **Stacks 09RJ, essential surjectivity, over an affine stage.** In Situation 09RH with charts
bounded in size and the chosen stage `X₀` affine, every perfect object `E` of `D(𝒪_X)` on the
limit is `Lfᵢ^* Eᵢ` for some stage `i ≥ 0` and some perfect object `Eᵢ` of `D(𝒪_{Xᵢ})`, where
`fᵢ : X ⟶ Xᵢ` is the projection. -/
theorem exists_isPerfect_derivedPullback_iso_of_isAffineSpace
    (hb : ChartsBounded B S hS D.system)
    (hbase : IsAffineSpace B S hS (D.system.obj (op D.base)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).O)))
    (hE : (spacesEtaleModelRingedSite B S hS ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).IsPerfect E) :
    ∃ (i : I) (_ : D.base ≤ i) (Eᵢ : DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelRingedTopos B S hS ⟨D.system.obj (op i), D.algebraicSpace i⟩).O))),
      (spacesEtaleModelRingedSite B S hS ⟨D.system.obj (op i), D.algebraicSpace i⟩).IsPerfect Eᵢ ∧
        Nonempty ((derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E) := by
  let L := D.toLimitSituation
  let hX := D.limitAlgebraicSpace
  -- the limit is affine
  obtain ⟨T, hT, ⟨eT⟩⟩ :=
    (D.isAffineHom_limitCone_π_of_chartsBounded hb (op D.base)).isAffineSpace_source hbase
  obtain ⟨A, _, hA, p, ⟨eA⟩⟩ := exists_iso_mk_spec B S hS T hT
  let g : (⟨D.limitCone.pt, hX⟩ : AlgebraicSpaces B S hS) ≅
      ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩ :=
    ObjectProperty.isoMk _ (eT ≪≫ yoneda.mapIso eA)
  -- `E` is `𝒪_X ⊗_A C`
  obtain ⟨C, hbd, hfin, hproj, ⟨eE⟩⟩ :=
    exists_finiteProjective_pointTensor_iso_of_isPerfect_of_iso B S hS hA p g E hE
  let ψ₀ := representedTildeOfIsoPointRingHom B S hS hA p g
  let σ := RingEquiv.ofBijective ψ₀ (bijective_pointRingHomOfModel B S hS _
    (bijective_representedTildeOfIsoBaseRingHom B S hS hA p g))
  -- the chart of the affine stage
  obtain ⟨T₀, hT₀, ⟨e₀⟩⟩ := hbase
  let U₀ : BigAffineFppf B S hS := ⟨T₀, hT₀⟩
  let f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ L.system.obj (op L.base) :=
    e₀.inv
  have : IsIso f₀ := Iso.isIso_inv e₀
  have hf₀ : IsEtaleChart B S hS (L.system.obj (op L.base)) (CostructuredArrow.mk f₀) :=
    isEtaleChart_of_isIso (B := B) (S := S) (hS := hS) (f := f₀)
  have hsurj : IsSurjective B S hS f₀ := isSurjective_of_isIso B S hS f₀
  have hpb : IsPullback (𝟙 _) (yoneda.map (𝟙 ((BigAffineFppf.inclusion B S hS).obj U₀))) f₀ f₀ := by
    rw [yoneda.map_id]
    exact @IsKernelPair.id_of_mono _ _ _ _ f₀ (IsIso.mono_of_iso f₀)
  have hcol := L.isStagesColimit_globalFunctions_of_chartsBounded (U₀ := U₀) (R₀ := U₀) hX hb hf₀
    hsurj hpb
  -- the colimit of rings
  let R := L.stagesGlobalFunctions
  let c : Cocone R :=
    { pt := CommRingCat.of A
      ι :=
        { app := fun i => CommRingCat.ofHom (σ.symm.toRingHom.comp
            ((globalFunctionsMap B S hS (L.projection hX i.1)).comp (Shrink.ringEquiv _).toRingHom))
          naturality := fun i j h => by
            refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
            show σ.symm (globalFunctionsMap B S hS (L.projection hX j.1)
              (Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm (globalFunctionsMap B S hS
                (L.transition (leOfHom h)) (Shrink.ringEquiv _ x))))) =
              σ.symm (globalFunctionsMap B S hS (L.projection hX i.1) (Shrink.ringEquiv _ x))
            rw [RingEquiv.apply_symm_apply, ← RingHom.comp_apply, ← globalFunctionsMap_comp,
              L.projection_comp_transition hX (leOfHom h)] } }
  have hc' : Stacks.IsStagesColimit (G := fun i => R.obj i) (T := c.pt)
      (fun i j hij x => R.map (homOfLE hij) x) (fun i x => c.ι.app i x) :=
    Stacks.IsStagesColimit.ofEquiv _ _ (fun i => (Shrink.ringEquiv _).toEquiv) σ.toEquiv
      (fun i j h s => by
        show Shrink.ringEquiv _ ((Shrink.ringEquiv _).symm (globalFunctionsMap B S hS
          (L.transition (leOfHom (homOfLE h))) (Shrink.ringEquiv _ s))) = _
        rw [RingEquiv.apply_symm_apply]
        rfl)
      (fun i s => by
        show σ (σ.symm _) = _
        rw [RingEquiv.apply_symm_apply]
        rfl) hcol
  obtain ⟨hc⟩ := Stacks.IsStagesColimit.nonempty_isColimit R c hc'
  -- the bounds of `C`
  obtain ⟨a, ha⟩ := hbd.bddBelow
  obtain ⟨b, hb'⟩ := hbd.bddAbove
  have hCa : C.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    by_contra hz
    exact (not_lt.2 (ha hz)) hn
  have hCb : C.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    by_contra hz
    exact (not_lt.2 (hb' hz)) hn
  let ψs : ∀ i : L.Stages, R.obj i →+* (SpacesEtale.structurePresheaf B S hS (L.stage i.1)).obj
      (op (SpacesEtale.idObj B S hS (L.stage i.1))) := fun i =>
    (Shrink.ringEquiv (globalFunctions' B S hS (L.stage i.1).1)).toRingHom
  let gs : ∀ i : L.Stages, (⟨D.limitCone.pt, hX⟩ : AlgebraicSpaces B S hS) ⟶ L.stage i.1 :=
    fun i => L.projection hX i.1
  have hψ : ∀ (i : L.Stages) (x : R.obj i), globalFunctionsMap B S hS (gs i) (ψs i x) =
      ψ₀ (c.ι.app i x) := fun i x => by
    show _ = σ (σ.symm _)
    exact (σ.apply_symm_apply _).symm
  obtain ⟨i, Eᵢ, hEᵢ, eᵢ⟩ := exists_isPerfect_derivedPullback_iso_of_pointTensor B S hS R c hc
    (X := ⟨D.limitCone.pt, hX⟩) ψ₀ (fun i => L.stage i.1) gs ψs hψ E C a b hCa hCb hfin hproj eE
  exact ⟨i.1, i.2, Eᵢ, hEᵢ, eᵢ⟩

end DescentSituation

end AlgebraicGeometry.Space

end
