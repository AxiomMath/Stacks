module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeNeighborhood
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Flatness and finite presentation of a finite type scheme near a flat point

Let `f : X ⟶ S` be locally of finite type and let `x ∈ X` be a point at which `X` is flat over
`S`. Then there is an elementary étale neighbourhood `(S', s')` of `(S, f x)` and an open
subscheme of `X ×_S Spec 𝒪_{S', s'}` containing the unique point over `x` which is flat and of
finite presentation over `Spec 𝒪_{S', s'}`. This is Stacks 05I6, the structure-sheaf case of
Stacks 05I5 read as a statement about a morphism of schemes rather than about a module.

The proof is the source's embedding into affine space. An affine open `Vo ⊆ X` containing `x`
embeds by a closed immersion `i` into an affine space `A` over an affine open of `S`, and
`p : A ⟶ S` is locally of finite presentation, so Stacks 05I5 applies to `p`, to the direct
image `i_* 𝒪_{Vo}` and to the point `i x`. It returns an elementary étale neighbourhood
`(S', s')` and an open `W ⊆ A ×_S Spec 𝒪_{S', s'}` on which the inverse image of `i_* 𝒪_{Vo}`
is of finite presentation and flat over `𝒪_{S', s'}`.

The base change of `i` along `A ×_S Spec 𝒪_{S', s'} ⟶ A` is again a closed immersion; write
`j : WR ⟶ W` for its restriction over `W`. Affine base change (Stacks 02KG) identifies the
inverse image of `i_* 𝒪_{Vo}` to `W` with the direct image `j_* 𝒪_{WR}`. Finite presentation of
that direct image bounds the ideal sheaf of `j` (Stacks 01BP), hence makes `j` of finite
presentation (Stacks 01TV); and its flatness over `𝒪_{S', s'}` is flatness of `WR` over
`𝒪_{S', s'}`, because the stalk of a direct image along a closed immersion at the image of a
point is the stalk there (Stacks 05B8). Transporting along the open immersion of `WR` into
`X ×_S Spec 𝒪_{S', s'}` and shrinking to an affine open makes the morphism quasi-compact and
quasi-separated as well, hence of finite presentation.

## Main results

* `AlgebraicGeometry.finitePresentation_of_isFinitePresentation_pushforward_unit`: a closed
  immersion whose direct image of the structure sheaf of the source is of finite presentation is
  itself of finite presentation.
* `AlgebraicGeometry.exists_open_flat_finitePresentation_of_closedImmersion` is the conclusion
  of Stacks 05I6 at `x`, from the data of a closed immersion of an open neighbourhood of `x`
  into a scheme locally of finite presentation over `S`.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_flat_finitePresentation` is
  **Stacks 05I6**.

## Implementation notes

The open subscheme is shrunk to an affine one before the conclusion is drawn. The statement asks
only for some open containing the point over `x`, and affineness of the open is what supplies the
quasi-compactness and quasi-separatedness halves of finite presentation, the base
`Spec 𝒪_{S', s'}` being affine too.

Uniqueness of the point of `X ×_S Spec 𝒪_{S', s'}` over `x` is automatic for an elementary étale
neighbourhood, by `AlgebraicGeometry.EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq`, so
only a point lying over `x` has to be produced.

## References

* [Stacks Project, Tag 05I6](https://stacks.math.columbia.edu/tag/05I6)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **A closed immersion is of finite presentation as soon as the direct image of the structure
sheaf of its source is.** Its ideal sheaf is the kernel of a surjection from the structure sheaf
of the target onto that direct image, so it is of finite type. -/
theorem finitePresentation_of_isFinitePresentation_pushforward_unit
    {Z Y : Scheme.{u}} (j : Z ⟶ Y) [IsClosedImmersion j]
    (hj : ((Scheme.Modules.pushforward j).obj
      (SheafOfModules.unit Z.ringCatSheaf)).IsFinitePresentation) :
    FinitePresentation j := by
  have hci : Stacks.ClosedImmersion.IsClosedImmersion j.toLRSHom.toShHom :=
    ((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae j).out 1 6).mp
      (inferInstance : IsClosedImmersion j)
  have hepi := hci.structureSheafMap_epi
  have hfp : ((SheafOfModules.pushforward (structureSheafHom j.toLRSHom.toShHom)).obj
      (SheafOfModules.unit (structureSheafRing Z.toSheafedSpace))).IsFinitePresentation := hj
  have hft : (SheafOfModules.unit (structureSheafRing Y.toSheafedSpace)).IsFiniteType :=
    inferInstanceAs (SheafOfModules.unit Y.ringCatSheaf).IsFiniteType
  rw [finitePresentation_iff_isFiniteType_idealSheaf j]
  exact Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType
    (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toLRSHom.toShHom))

/-- **Stacks Project, Tag 05I6 at a point, from an embedding into a scheme locally of finite
presentation.** Let `Vo` be an open of `X` containing a point `x` at which `X` is flat over `S`,
let `i : Vo ⟶ A` be a closed immersion and let `p : A ⟶ S` be locally of finite presentation
with `i ≫ p` the restriction of `f`. Then an open subscheme of `X ×_S Spec 𝒪_{S', s'}`
containing the unique point over `x` is flat and of finite presentation over
`Spec 𝒪_{S', s'}`, for a suitable elementary étale neighbourhood `(S', s')` of `(S, f x)`. -/
theorem exists_open_flat_finitePresentation_of_closedImmersion {X S A : Scheme.{u}}
    (f : X ⟶ S) {x : X} {Vo : X.Opens} (hx : x ∈ Vo) (i : Vo.toScheme ⟶ A)
    [IsClosedImmersion i] (p : A ⟶ S) [LocallyOfFinitePresentation p]
    (hcomp : i ≫ p = Vo.ι ≫ f) (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary),
      let b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
        U.scheme.fromSpecStalk U.point ≫ U.toBase
      ∃ (V : (pullback f b).Opens) (v : V),
        (pullback.fst f b ⁻¹' {x} = {V.ι v}) ∧
        Flat (V.ι ≫ pullback.snd f b) ∧
        FinitePresentation (V.ι ≫ pullback.snd f b) := by
  classical
  set xV : Vo.toScheme := ⟨x, hx⟩
  have hιxV : Vo.ι xV = x := rfl
  set F₀ : Vo.toScheme.Modules := SheafOfModules.unit Vo.toScheme.ringCatSheaf
  have hF₀qc : F₀.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _
  have hF₀ft : F₀.IsFiniteType := inferInstance
  set M : A.Modules := (Scheme.Modules.pushforward i).obj F₀
  have hMqc : M.IsQuasicoherent := inferInstance
  have hMft : M.IsFiniteType :=
    Stacks.AlgebraicGeometry.FinitePushforwardCoherent.isFiniteType_pushforward i F₀
  -- `X` is flat over `S` at `x`, hence `i_* 𝒪_{Vo}` is flat over `S` at `i x`
  have hFlatX : IsFlatOverAt f.toLRSHom.toShHom (SheafOfModules.unit X.ringCatSheaf) x :=
    (isFlatOverAt_unit_iff_isFlatAt f x).mpr hflat
  have hF₀flat : IsFlatOverAt (i ≫ p).toLRSHom.toShHom F₀ xV := by
    rw [hcomp]
    exact isFlatOverAt_of_moduleIso (Vo.ι ≫ f).toLRSHom.toShHom
      (Scheme.Modules.pullbackUnitIso Vo.ι) xV
      ((isFlatOverAt_pullback_iff_of_isFlatAt Vo.ι f (SheafOfModules.unit X.ringCatSheaf)
        xV (Flat.stalkMap Vo.ι xV)).mp hFlatX)
  have hMflat : IsFlatOverAt p.toLRSHom.toShHom M (i xV) :=
    (isFlatOverAt_pushforward_finite_iff i p F₀ xV
      (preimage_singleton_of_isClosedImmersion i xV)).mp hF₀flat
  have hpoint : p (i xV) = f x := by
    simpa only [Scheme.Hom.comp_apply, hιxV] using congrArg (fun m : Vo.toScheme ⟶ S ↦ m xV) hcomp
  obtain ⟨N, hN, W, w, hwfiber, hWfp, hWflat⟩ :=
    (show ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u} from
          @existsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u}) p M (i xV) hMflat
  refine ⟨N.congrPoint hpoint, hN.congrPoint hpoint, ?_⟩
  set b : Spec (N.scheme.presheaf.stalk N.point) ⟶ S :=
    N.scheme.fromSpecStalk N.point ≫ N.toBase
  -- the base change of `i` along `A ×_S Spec 𝒪_{N, n} ⟶ A`
  set gBase : pullback i (pullback.fst p b) ⟶ Vo.toScheme := pullback.fst i (pullback.fst p b)
  set iBase : pullback i (pullback.fst p b) ⟶ pullback p b := pullback.snd i (pullback.fst p b)
  have hiPb : IsPullback gBase iBase i (pullback.fst p b) := IsPullback.of_hasPullback _ _
  have hsq : IsPullback gBase (iBase ≫ pullback.snd p b) (Vo.ι ≫ f) b := by
    rw [← hcomp]
    exact hiPb.paste_vert (IsPullback.of_hasPullback p b)
  -- the open immersion of `Vo ×_S Spec 𝒪_{N, n}` into `X ×_S Spec 𝒪_{N, n}`
  set kR : pullback i (pullback.fst p b) ⟶ pullback f b :=
    (IsPullback.of_hasPullback f b).lift (gBase ≫ Vo.ι) (iBase ≫ pullback.snd p b)
      (by rw [Category.assoc, hsq.w])
  have hkRfst : kR ≫ pullback.fst f b = gBase ≫ Vo.ι :=
    (IsPullback.of_hasPullback f b).lift_fst _ _ _
  have hkRsnd : kR ≫ pullback.snd f b = iBase ≫ pullback.snd p b :=
    (IsPullback.of_hasPullback f b).lift_snd _ _ _
  have hkRPb : IsPullback gBase kR Vo.ι (pullback.fst f b) :=
    hsq.of_bot' (IsPullback.of_hasPullback f b)
  have hkRopen : IsOpenImmersion kR := MorphismProperty.of_isPullback hkRPb inferInstance
  -- the closed immersion of the part of `Vo ×_S Spec 𝒪_{N, n}` lying over `W`
  set WR : (pullback i (pullback.fst p b)).Opens := iBase ⁻¹ᵁ W
  set j : WR.toScheme ⟶ W.toScheme := iBase ∣_ W
  have hjPb : IsPullback (WR.ι ≫ gBase) j i (W.ι ≫ pullback.fst p b) :=
    (isPullback_morphismRestrict iBase W).flip.paste_horiz hiPb
  have hjclosed : IsClosedImmersion j := MorphismProperty.of_isPullback hjPb inferInstance
  -- the inverse image of `i_* 𝒪_{Vo}` to `W` is the direct image of `𝒪_{WR}`
  set eBC : (Scheme.Modules.pullback (W.ι ≫ pullback.fst p b)).obj M ≅
      (Scheme.Modules.pushforward j).obj (SheafOfModules.unit WR.toScheme.ringCatSheaf) :=
    affinePushforwardBaseChangeIso hjPb F₀ ≪≫ (Scheme.Modules.pushforward j).mapIso
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (WR.ι ≫ gBase))
  set pW : W.toScheme ⟶ Spec (N.scheme.presheaf.stalk N.point) := W.ι ≫ pullback.snd p b with hpW
  have hjfp : FinitePresentation j :=
    finitePresentation_of_isFinitePresentation_pushforward_unit j
      ((SheafOfModules.isFinitePresentation W.toScheme.ringCatSheaf).prop_of_iso eBC hWfp)
  have hjflat : Flat (j ≫ pW) := by
    rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
    intro y
    have hMy := isFlatOverAt_of_moduleIso pW.toLRSHom.toShHom eBC (j y) (hWflat (j y))
    have hunit := (isFlatOverAt_pushforward_finite_iff j pW
      (SheafOfModules.unit WR.toScheme.ringCatSheaf) y
      (preimage_singleton_of_isClosedImmersion j y)).mpr hMy
    exact (isFlatOverAt_unit_iff_isFlatAt (j ≫ pW) y).mp hunit
  have hjlfp : LocallyOfFinitePresentation (j ≫ pW) := by
    have h₁ : LocallyOfFinitePresentation j := hjfp.1
    infer_instance
  have hbase : j ≫ pW = WR.ι ≫ kR ≫ pullback.snd f b := by
    rw [hpW, morphismRestrict_ι_assoc, hkRsnd]
  -- the open subscheme of `X ×_S Spec 𝒪_{N, n}` and its point over `x`
  set Vout : (pullback f b).Opens := kR ''ᵁ WR
  set eV : WR.toScheme ≅ Vout.toScheme := kR.isoImage WR
  have hVoutι : eV.inv ≫ WR.ι ≫ kR = Vout.ι := kR.isoImage_inv_ι WR
  have hwfst : pullback.fst p b (W.ι w) = i xV := by
    have : W.ι w ∈ pullback.fst p b ⁻¹' ({i xV} : Set A) := by rw [hwfiber]; rfl
    simpa using this
  obtain ⟨qC, hqCf, hqCs⟩ :=
    Scheme.Pullback.exists_preimage_pullback xV (W.ι w) hwfst.symm
  have hqCW : qC ∈ WR := by
    change iBase qC ∈ W
    rw [hqCs]
    exact w.2
  have hzVout : kR qC ∈ Vout := ⟨qC, hqCW, rfl⟩
  have hzfst : pullback.fst f b (kR qC) = x := by
    have hgq : gBase qC = xV := hqCf
    simpa only [Scheme.Hom.comp_apply, hgq, hιxV] using
      congrArg (fun m : pullback i (pullback.fst p b) ⟶ X ↦ m qC) hkRfst
  -- an affine open neighbourhood inside it is quasi-compact and quasi-separated over the base
  obtain ⟨V, hVaff, hzV, hVVout⟩ :=
    exists_isAffineOpen_mem_and_subset (X := pullback f b) (x := kR qC) hzVout
  have hVle : V ≤ Vout := hVVout
  have hVaff' : IsAffine V.toScheme := hVaff
  -- `V` maps into `WR`, so flatness and finite presentation transfer from `WR`
  have hVeq : V.ι ≫ pullback.snd f b =
      ((pullback f b).homOfLE hVle ≫ eV.inv) ≫ WR.ι ≫ kR ≫ pullback.snd f b := by
    rw [← Scheme.homOfLE_ι (pullback f b) hVle, ← hVoutι]
    simp
  have hflatV : Flat (V.ι ≫ pullback.snd f b) := by
    have h₁ : Flat (WR.ι ≫ kR ≫ pullback.snd f b) := hbase ▸ hjflat
    rw [hVeq]
    infer_instance
  have hlfpV : LocallyOfFinitePresentation (V.ι ≫ pullback.snd f b) := by
    have h₁ : LocallyOfFinitePresentation (WR.ι ≫ kR ≫ pullback.snd f b) := hbase ▸ hjlfp
    rw [hVeq]
    infer_instance
  have hqcV : QuasiCompact (V.ι ≫ pullback.snd f b) := inferInstance
  have hqsV : QuasiSeparated (V.ι ≫ pullback.snd f b) := inferInstance
  exact ⟨V, ⟨kR qC, hzV⟩,
    EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq f x (N.congrPoint hpoint)
      (hN.congrPoint hpoint) hzfst,
    hflatV, hlfpV, hqcV, hqsV⟩

/-- **Stacks Project, Tag 05I6.** Let `X` be locally of finite type over `S` and let `x ∈ X` be a
point at which `X` is flat over `S`. Then there is an elementary étale neighbourhood `(S', s')`
of `(S, f x)` and an open subscheme of `X ×_S Spec 𝒪_{S', s'}` containing the unique point over
`x` which is flat and of finite presentation over `Spec 𝒪_{S', s'}`. -/
@[stacks 05I6]
theorem exists_elementaryEtaleNeighborhood_flat_finitePresentation {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) (hflat : IsFlatAt f.toLRSHom.toShHom x) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary),
      let b : Spec (U.scheme.presheaf.stalk U.point) ⟶ S :=
        U.scheme.fromSpecStalk U.point ≫ U.toBase
      ∃ (V : (pullback f b).Opens) (v : V),
        (pullback.fst f b ⁻¹' {x} = {V.ι v}) ∧
        Flat (V.ι ≫ pullback.snd f b) ∧
        FinitePresentation (V.ι ≫ pullback.snd f b) := by
  obtain ⟨Vo, hx, A, hA, i, p, hi, hp, hcomp⟩ :=
    exists_closedImmersion_affineSpace_of_locallyOfFiniteType f x
  exact exists_open_flat_finitePresentation_of_closedImmersion f hx i p hcomp hflat

end AlgebraicGeometry

end
