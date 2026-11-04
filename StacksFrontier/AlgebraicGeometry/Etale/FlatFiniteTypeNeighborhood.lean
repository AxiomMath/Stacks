module

public import Mathlib.RingTheory.FiniteType
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FlatnessStalkTransfer
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeModules
public import StacksFrontier.AlgebraicGeometry.FinitePushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Flatness near a point of a finite type module over a morphism of finite type

Let `f : X ⟶ S` be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite
type, and let `x` be a point at which `F` is flat over `S`. Then there is an elementary étale
neighbourhood `(S', s')` of `(S, f x)` and an open `V ⊆ X ×_S Spec 𝒪_{S', s'}` containing the
unique point over `x` on which the pullback of `F` is flat over `𝒪_{S', s'}`.

## Main definitions

* `AlgebraicGeometry.affinePushforwardBaseChangeIso` is the affine base-change isomorphism
  `g^* f_* F ≅ f'_* (g')^* F`.

## Main results

* `AlgebraicGeometry.isFlatOverAt_pushforward_finite_iff`: a quasi-coherent module is flat over the
  base at `z` exactly when its direct image along a finite morphism `i` whose fibre over `i z` is
  `{z}` is flat over the base at `i z`.
* `AlgebraicGeometry.exists_closedImmersion_affineSpace_of_locallyOfFiniteType`: for `f` locally of
  finite type, an affine neighbourhood of `x` admits a closed immersion into affine space over an
  affine open of `S`, compatibly with `f`.
* `AlgebraicGeometry.isFlatOverAt_pullback_of_isFlatOverAt_pullback_pushforward`: the same transfer
  of flatness after a base change of a closed immersion.
* `AlgebraicGeometry.existsElementaryEtaleNeighborhoodFlatOverAt_of_closedImmersion`: the statement
  at `x`, given a closed immersion of a neighbourhood of `x` into a scheme locally of finite
  presentation over `S`.
* `AlgebraicGeometry.existsElementaryEtaleNeighborhoodFlatOver`: the statement for every `f`
  locally of finite type.
* `AlgebraicGeometry.isOpen_isFlatOverAt_fiber_of_locallyOfFiniteType`: in every fibre of a
  morphism locally of finite type, the locus where a quasi-coherent module of finite type is flat
  over the base is open.

## Implementation notes

For an elementary étale neighbourhood the uniqueness of the point of `X ×_S Spec 𝒪_{S', s'}` over
`x` is `AlgebraicGeometry.EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq`.

Affine space over an affine open `U ⊆ S` is `Spec Γ(S, U)[x_1, …, x_n]`, and its structure
morphism to `S` is `Spec` of the inclusion of coefficients followed by
`AlgebraicGeometry.IsAffineOpen.fromSpec`, landing in `S` rather than in `U`.

## References

* [Stacks Project, Tag 05KT](https://stacks.math.columbia.edu/tag/05KT)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 05M9](https://stacks.math.columbia.edu/tag/05M9)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 05B8](https://stacks.math.columbia.edu/tag/05B8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The inverse image of a module along a morphism of schemes, formed as a morphism of ringed
spaces, is its inverse image formed in the category of modules on a scheme. -/
theorem modulePullback_obj_eq_pullback_obj {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules) :
    (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).obj F =
      (Scheme.Modules.pullback g).obj F :=
  rfl

/-- **Flatness over the base at a point passes to the inverse image along a flat morphism.** For
`g : W ⟶ X` flat at `w`, a module is flat over `S` at `g w` exactly when its inverse image is flat
over `S` at `w`. -/
theorem isFlatOverAt_pullback_iff_of_isFlatAt {W X S : Scheme.{u}} (g : W ⟶ X) (h : X ⟶ S)
    (G : X.Modules) (w : W) (hg : IsFlatAt g.toLRSHom.toShHom w) :
    IsFlatOverAt h.toLRSHom.toShHom G (g w) ↔
      IsFlatOverAt (g ≫ h).toLRSHom.toShHom ((Scheme.Modules.pullback g).obj G) w := by
  simpa only [modulePullback_obj_eq_pullback_obj] using
    isFlatOverAt_iff_modulePullback_isFlatOverAt g h G w hg

/-- **The affine base-change isomorphism.** For a cartesian square whose right-hand morphism `f` is
affine and a quasi-coherent module `F` on its source, the canonical comparison
`g^* f_* F ⟶ f'_* (g')^* F` is an isomorphism. -/
def affinePushforwardBaseChangeIso {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (hw : IsPullback g' f' f g) [IsAffineHom f] (F : X.Modules)
    [F.IsQuasicoherent] :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F) ≅
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F) :=
  haveI := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    hw F
  asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hw.w).app F)

/-- **A closed immersion has singleton fibres.** The fibre of a closed immersion over the image
of a point is that single point. -/
theorem preimage_singleton_of_isClosedImmersion {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (z : Z) : i ⁻¹' ({i z} : Set Y) = {z} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨fun hy ↦ i.isClosedEmbedding.injective hy, fun hy ↦ hy ▸ rfl⟩

/-- **Flatness over the base at a point transfers across a finite morphism with a singleton
fibre.** For `i : Z ⟶ Y` finite whose fibre over `i z` is `{z}` and `q : Y ⟶ S`, a quasi-coherent
`𝒪_Z`-module is flat over `S` at `z` exactly when its direct image is flat over `S` at `i z`. -/
theorem isFlatOverAt_pushforward_finite_iff {Z Y S : Scheme.{u}} (i : Z ⟶ Y) [IsFinite i]
    (q : Y ⟶ S) (G : Z.Modules) [G.IsQuasicoherent] (z : Z)
    (hfiber : i ⁻¹' ({i z} : Set Y) = {z}) :
    IsFlatOverAt (i ≫ q).toLRSHom.toShHom G z ↔
      IsFlatOverAt q.toLRSHom.toShHom ((Scheme.Modules.pushforward i).obj G) (i z) := by
  let e := Classical.choice (stalk_isomorphic_pushforward_of_finite_singleton_fiber i z hfiber G)
  let Mz := TopCat.Presheaf.stalk G.val.presheaf z
  let My := TopCat.Presheaf.stalk ((Scheme.Modules.pushforward i).obj G).val.presheaf (i z)
  let R := S.presheaf.stalk (q (i z))
  let A := Y.presheaf.stalk (i z)
  let α := (q.stalkMap (i z)).hom
  let β := (i.stalkMap z).hom
  let : Algebra R A := α.toAlgebra
  let : Module (Z.presheaf.stalk z) Mz :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Z.presheaf) G.val z
  let : Module A Mz := Module.compHom _ β
  let : Module (Y.presheaf.stalk (i z)) My :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) ((Scheme.Modules.pushforward i).obj G).val (i z)
  let : Module R Mz := Module.compHom _ ((i ≫ q).stalkMap z).hom
  let : Module R My := Module.compHom _ α
  let : IsScalarTower R A Mz := IsScalarTower.of_algebraMap_smul fun r m ↦ by
    show β (α r) • m = ((i ≫ q).stalkMap z).hom r • m
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  let : IsScalarTower R A My := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : LinearMap.CompatibleSMul Mz My R A := ⟨by
    intro g r m
    rw [← IsScalarTower.algebraMap_smul (R := R) (A := A) (M := My) r (g m),
      ← IsScalarTower.algebraMap_smul (R := R) (A := A) (M := Mz) r m]
    exact g.map_smul _ _⟩
  show Module.Flat R Mz ↔ Module.Flat R My
  exact Module.Flat.equiv_iff (e.toLinearEquiv.restrictScalars R)

/-- Let `i : V ⟶ A` be a closed immersion, let `pr : P ⟶ A` be any morphism, and let the square
`gBase, iBase, i, pr` be cartesian. If the inverse image along `pr` of the direct image `i_* G`
of a quasi-coherent module is flat over `T` at `iBase r`, then the inverse image of `G` along
`gBase` is flat over `T` at `r`. -/
theorem isFlatOverAt_pullback_of_isFlatOverAt_pullback_pushforward
    {V A P R₀ T : Scheme.{u}} (i : V ⟶ A) [IsClosedImmersion i] (pr : P ⟶ A) (pBase : P ⟶ T)
    (gBase : R₀ ⟶ V) (iBase : R₀ ⟶ P) (hpb : IsPullback gBase iBase i pr) (G : V.Modules)
    [G.IsQuasicoherent] (r : R₀)
    (h : IsFlatOverAt pBase.toLRSHom.toShHom
      ((Scheme.Modules.pullback pr).obj ((Scheme.Modules.pushforward i).obj G)) (iBase r)) :
    IsFlatOverAt (iBase ≫ pBase).toLRSHom.toShHom
      ((Scheme.Modules.pullback gBase).obj G) r := by
  have : IsClosedImmersion iBase := MorphismProperty.of_isPullback hpb inferInstance
  have hGqc : G.IsQuasicoherent := inferInstance
  have : ((Scheme.Modules.pullback gBase).obj G).IsQuasicoherent := by
    rw [← modulePullback_obj_eq_pullback_obj]
    exact @SheafOfModules.modulePullback_isQuasicoherent _ _ gBase.toLRSHom.toShHom G hGqc
  exact (isFlatOverAt_pushforward_finite_iff iBase pBase
    ((Scheme.Modules.pullback gBase).obj G) r
    (preimage_singleton_of_isClosedImmersion iBase r)).mpr
    (isFlatOverAt_of_moduleIso pBase.toLRSHom.toShHom
      (affinePushforwardBaseChangeIso hpb G) (iBase r) h)

/-- **An affine chart of a morphism locally of finite type.** A point of the source lies in an
affine open mapping into an affine open of the target, on which the morphism induces a ring map
of finite type. -/
alias exists_affineChart_finiteType := ElementaryEtaleFlatness.exists_affineChart_finiteType

/-- **An embedding into affine space.** For `f : X ⟶ S` locally of finite type and a point `x`,
there is an affine open `V ⊆ X` containing `x`, an affine space `𝔸 = Spec Γ(S, U)[x_1, …, x_n]`
over an affine open `U ⊆ S`, a closed immersion `i : V ⟶ 𝔸`, and a morphism `p : 𝔸 ⟶ S` locally of
finite presentation, with `i ≫ p` the restriction of `f`. -/
theorem exists_closedImmersion_affineSpace_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    ∃ (V : X.affineOpens) (_ : x ∈ V.1) (A : Scheme.{u}) (_ : IsAffine A)
      (i : V.1.toScheme ⟶ A) (p : A ⟶ S),
      IsClosedImmersion i ∧ LocallyOfFinitePresentation p ∧ i ≫ p = V.1.ι ≫ f := by
  obtain ⟨U, V, hx, hVU, hft⟩ := exists_affineChart_finiteType f x
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen V.1 := V.2
  let _ : Algebra Γ(S, U.1) Γ(X, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(S, U.1) Γ(X, V.1) := hft
  obtain ⟨n, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  refine ⟨V, hx, Spec (.of (MvPolynomial (Fin n) Γ(S, U.1))), inferInstance,
    hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom),
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U.1) (MvPolynomial (Fin n) Γ(S, U.1)))) ≫
      hU.fromSpec, ?_, ?_, ?_⟩
  · exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion hV.isoSpec.hom
      (Spec.map (CommRingCat.ofHom ψ.toRingHom))).mpr
      (IsClosedImmersion.spec_of_surjective _ hψ)
  · have : LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(S, U.1) (MvPolynomial (Fin n) Γ(S, U.1))))) := by
      rw [LocallyOfFinitePresentation.SpecMap_iff]
      simp only [CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
      infer_instance
    have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
    infer_instance
  · have hc : ψ.toRingHom.comp (algebraMap Γ(S, U.1) (MvPolynomial (Fin n) Γ(S, U.1))) =
        (f.appLE U.1 V.1 hVU).hom := by
      ext r
      show ψ (algebraMap Γ(S, U.1) (MvPolynomial (Fin n) Γ(S, U.1)) r) =
        algebraMap Γ(S, U.1) Γ(X, V.1) r
      rw [ψ.commutes r]
    calc (hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap Γ(S, U.1) (MvPolynomial (Fin n) Γ(S, U.1)))) ≫ hU.fromSpec
        = hV.isoSpec.hom ≫ (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap Γ(S, U.1) (MvPolynomial (Fin n) Γ(S, U.1))))) ≫ hU.fromSpec := by
          simp [Category.assoc]
      _ = hV.isoSpec.hom ≫ Spec.map (f.appLE U.1 V.1 hVU) ≫ hU.fromSpec := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
          simp only [CommRingCat.ofHom_hom]
      _ = V.1.ι ≫ f := by
          rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, ← Category.assoc,
            hV.isoSpec_hom_fromSpec]

/-- Let `f : X ⟶ S` carry a quasi-coherent `𝒪_X`-module `F` of finite type which is flat over `S`
at `x`, let `Vo` be an open of `X` containing `x`, let `i : Vo ⟶ A` be a closed immersion and let
`p : A ⟶ S` be locally of finite presentation with `i ≫ p` the restriction of `f`. Then there is an
elementary étale neighbourhood `(S', s')` of `(S, f x)` and an open subscheme of
`X ×_S Spec 𝒪_{S', s'}` containing the unique point over `x` on which the pullback of `F` is flat
over `𝒪_{S', s'}`. -/
theorem existsElementaryEtaleNeighborhoodFlatOverAt_of_closedImmersion {X S A : Scheme.{u}}
    (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] {x : X} {Vo : X.Opens}
    (hx : x ∈ Vo) (i : Vo.toScheme ⟶ A) [IsClosedImmersion i] (p : A ⟶ S)
    [LocallyOfFinitePresentation p] (hcomp : i ≫ p = Vo.ι ≫ f)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x) :
    ExistsElementaryEtaleNeighborhoodFlatOverAt f F x := by
  classical
  have hap {P Q : Scheme.{u}} {a b : P ⟶ Q} (h : a = b) (p : P) : a p = b p := by rw [h]
  set xV : Vo.toScheme := ⟨x, hx⟩ with hxV
  have hιxV : Vo.ι xV = x := rfl
  set G : Vo.toScheme.Modules := (Scheme.Modules.pullback Vo.ι).obj F with hG
  have hGqc : G.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion Vo.ι F
  have hGft : G.IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType Vo.ι.toLRSHom.toShHom F
  set M : A.Modules := (Scheme.Modules.pushforward i).obj G with hM
  have hMqc : M.IsQuasicoherent := inferInstance
  have hMft : M.IsFiniteType :=
    Stacks.AlgebraicGeometry.FinitePushforwardCoherent.isFiniteType_pushforward i G
  have hGflat : IsFlatOverAt (i ≫ p).toLRSHom.toShHom G xV := by
    rw [hcomp]
    exact (isFlatOverAt_pullback_iff_of_isFlatAt Vo.ι f F xV (Flat.stalkMap Vo.ι xV)).mp hF
  have hMflat : IsFlatOverAt p.toLRSHom.toShHom M (i xV) :=
    (isFlatOverAt_pushforward_finite_iff i p G xV
      (preimage_singleton_of_isClosedImmersion i xV)).mp hGflat
  have hpoint : p (i xV) = f x := by
    simpa only [Scheme.Hom.comp_apply, hιxV] using hap hcomp xV
  obtain ⟨N, hN, W, w, hwfiber, -, hWflat⟩ :=
    (show ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u} from
          @existsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u}) p M (i xV) hMflat
  refine ⟨N.congrPoint hpoint, hN.congrPoint hpoint, ?_⟩
  set b : Spec (N.scheme.presheaf.stalk N.point) ⟶ S :=
    N.scheme.fromSpecStalk N.point ≫ N.toBase with hb
  set gBase : pullback i (pullback.fst p b) ⟶ Vo.toScheme := pullback.fst i (pullback.fst p b)
    with hgBase
  set iBase : pullback i (pullback.fst p b) ⟶ pullback p b := pullback.snd i (pullback.fst p b)
    with hiBase
  set pBase : pullback p b ⟶ Spec (N.scheme.presheaf.stalk N.point) := pullback.snd p b with hpBase
  set kQ : pullback Vo.ι (pullback.fst f b) ⟶ pullback f b :=
    pullback.snd Vo.ι (pullback.fst f b) with hkQ
  set eC : pullback i (pullback.fst p b) ≅ pullback (Vo.ι ≫ f) b :=
    pullbackRightPullbackFstIso p b i ≪≫ pullback.congrHom hcomp rfl with heC
  set eO : pullback Vo.ι (pullback.fst f b) ≅ pullback (Vo.ι ≫ f) b :=
    pullbackRightPullbackFstIso f b Vo.ι with heO
  set eIso : pullback Vo.ι (pullback.fst f b) ≅ pullback i (pullback.fst p b) :=
    eO ≪≫ eC.symm with heIso
  set lQ : pullback Vo.ι (pullback.fst f b) ⟶ pullback p b := eIso.hom ≫ iBase with hlQ
  have heCfst : eC.hom ≫ pullback.fst (Vo.ι ≫ f) b = gBase := by
    rw [heC, hgBase, Iso.trans_hom, Category.assoc, pullback.congrHom_hom]
    simp only [pullback.map, pullback.lift_fst, Category.comp_id]
    exact pullbackRightPullbackFstIso_hom_fst p b i
  have heOfst : eO.hom ≫ pullback.fst (Vo.ι ≫ f) b = pullback.fst Vo.ι (pullback.fst f b) :=
    pullbackRightPullbackFstIso_hom_fst f b Vo.ι
  have heIsoFst : eIso.hom ≫ gBase = pullback.fst Vo.ι (pullback.fst f b) := by
    rw [heIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← heCfst, Iso.inv_hom_id_assoc,
      heOfst]
  have hBaseMap : lQ ≫ pBase = kQ ≫ pullback.snd f b := by
    have h₁ : eC.inv ≫ iBase ≫ pBase = pullback.snd (Vo.ι ≫ f) b := by
      rw [heC, hiBase, hpBase, Iso.trans_inv, pullback.congrHom_inv, Category.assoc,
        pullbackRightPullbackFstIso_inv_snd_snd]
      simp only [pullback.map, pullback.lift_snd, Category.comp_id]
    have h₂ : eO.hom ≫ pullback.snd (Vo.ι ≫ f) b = kQ ≫ pullback.snd f b :=
      pullbackRightPullbackFstIso_hom_snd f b Vo.ι
    rw [hlQ, heIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc, h₁, h₂]
  have hwfst : pullback.fst p b (W.ι w) = i xV := by
    have : W.ι w ∈ pullback.fst p b ⁻¹' ({i xV} : Set A) := by rw [hwfiber]; rfl
    simpa using this
  obtain ⟨qC, hqCf, hqCs⟩ :=
    Scheme.Pullback.exists_preimage_pullback xV (W.ι w) hwfst.symm
  obtain ⟨q₀, heIsoq₀⟩ : ∃ q : ↥(pullback Vo.ι (pullback.fst f b)), eIso.hom q = qC :=
    ⟨eIso.inv qC, by simp⟩
  have hlQq₀ : lQ q₀ = W.ι w := by
    rwa [hlQ, Scheme.Hom.comp_apply, heIsoq₀, hiBase]
  have hq₀fst : pullback.fst Vo.ι (pullback.fst f b) q₀ = xV := by
    simpa only [Scheme.Hom.comp_apply, heIsoq₀, hgBase, hqCf] using
      (hap heIsoFst q₀).symm
  have hzfst : pullback.fst f b (kQ q₀) = x := by
    simpa only [Scheme.Hom.comp_apply, hq₀fst, hιxV] using
      hap pullback.condition.symm q₀
  set WQ : (pullback Vo.ι (pullback.fst f b)).Opens := lQ ⁻¹ᵁ W with hWQ
  have hq₀W : q₀ ∈ WQ := by rw [hWQ]; change lQ q₀ ∈ W; rw [hlQq₀]; exact w.2
  set Vout : (pullback f b).Opens :=
    ⟨kQ '' (WQ : Set ↥(pullback Vo.ι (pullback.fst f b))),
      kQ.isOpenEmbedding.isOpenMap _ WQ.2⟩ with hVout
  have hzVout : kQ q₀ ∈ Vout := ⟨q₀, hq₀W, rfl⟩
  set PF : (pullback f b).Modules := (Scheme.Modules.pullback (pullback.fst f b)).obj F with hPF
  have hMaps : kQ ≫ pullback.fst f b = (eIso.hom ≫ gBase) ≫ Vo.ι := by
    rw [heIsoFst]; exact (pullback.condition).symm
  set eTarget : (Scheme.Modules.pullback kQ).obj PF ≅
      (Scheme.Modules.pullback eIso.hom).obj ((Scheme.Modules.pullback gBase).obj G) :=
    (Scheme.Modules.pullbackComp kQ (pullback.fst f b)).app F ≪≫
      (Scheme.Modules.pullbackCongr hMaps).app F ≪≫
      ((Scheme.Modules.pullbackComp (eIso.hom ≫ gBase) Vo.ι).app F).symm ≪≫
      ((Scheme.Modules.pullbackComp eIso.hom gBase).app G).symm with heTarget
  have hFlatQ : ∀ q : ↥(pullback Vo.ι (pullback.fst f b)), q ∈ WQ →
      IsFlatOverAt (pullback.snd f b).toLRSHom.toShHom PF (kQ q) := by
    intro q hq
    have hqW : lQ q ∈ W := hq
    have hW₁ : IsFlatOverAt (W.ι ≫ pBase).toLRSHom.toShHom
        ((Scheme.Modules.pullback W.ι).obj
          ((Scheme.Modules.pullback (pullback.fst p b)).obj M)) ⟨lQ q, hqW⟩ :=
      isFlatOverAt_of_moduleIso (W.ι ≫ pBase).toLRSHom.toShHom
        ((Scheme.Modules.pullbackComp W.ι (pullback.fst p b)).app M).symm _ (hWflat ⟨lQ q, hqW⟩)
    have hW₂ : IsFlatOverAt pBase.toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst p b)).obj M) (iBase (eIso.hom q)) := by
      simpa only [hlQ, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using
        (isFlatOverAt_pullback_ι_iff pBase W
          ((Scheme.Modules.pullback (pullback.fst p b)).obj M) ⟨lQ q, hqW⟩).mp hW₁
    have hG₁ : IsFlatOverAt (iBase ≫ pBase).toLRSHom.toShHom
        ((Scheme.Modules.pullback gBase).obj G) (eIso.hom q) :=
      isFlatOverAt_pullback_of_isFlatOverAt_pullback_pushforward i (pullback.fst p b) pBase
        gBase iBase (IsPullback.of_hasPullback i (pullback.fst p b)) G (eIso.hom q) hW₂
    have hG₂ : IsFlatOverAt (eIso.hom ≫ iBase ≫ pBase).toLRSHom.toShHom
        ((Scheme.Modules.pullback eIso.hom).obj ((Scheme.Modules.pullback gBase).obj G)) q :=
      (isFlatOverAt_pullback_iff_of_isFlatAt eIso.hom (iBase ≫ pBase)
        ((Scheme.Modules.pullback gBase).obj G) q (Flat.stalkMap eIso.hom q)).mp hG₁
    have hG₃ : IsFlatOverAt (kQ ≫ pullback.snd f b).toLRSHom.toShHom
        ((Scheme.Modules.pullback kQ).obj PF) q := by
      have hassoc : eIso.hom ≫ iBase ≫ pBase = kQ ≫ pullback.snd f b := by
        rw [← Category.assoc, ← hlQ, hBaseMap]
      rw [← hassoc]
      exact isFlatOverAt_of_moduleIso (eIso.hom ≫ iBase ≫ pBase).toLRSHom.toShHom
        eTarget.symm q hG₂
    exact (isFlatOverAt_pullback_iff_of_isFlatAt kQ (pullback.snd f b) PF q
      (Flat.stalkMap kQ q)).mpr hG₃
  refine ⟨Vout, ⟨kQ q₀, hzVout⟩, ?_, ?_⟩
  · exact EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq f x (N.congrPoint hpoint)
      (hN.congrPoint hpoint) hzfst
  · intro v
    obtain ⟨q, hq, hqv⟩ : (Vout.ι v : ↥(pullback f b)) ∈
        kQ '' (WQ : Set ↥(pullback Vo.ι (pullback.fst f b))) := v.2
    have hP : IsFlatOverAt (pullback.snd f b).toLRSHom.toShHom PF (Vout.ι v) :=
      hqv ▸ hFlatQ q hq
    exact isFlatOverAt_of_moduleIso (Vout.ι ≫ pullback.snd f b).toLRSHom.toShHom
      ((Scheme.Modules.pullbackComp Vout.ι (pullback.fst f b)).app F) v
      ((isFlatOverAt_pullback_ι_iff (pullback.snd f b) Vout PF v).mpr hP)

/-- For a morphism `f : X ⟶ S` locally of finite type and a quasi-coherent `𝒪_X`-module `F` of
finite type which is flat over `S` at `x`, there is an elementary étale neighbourhood `(S', s')` of
`(S, f x)` and an open subscheme of `X ×_S Spec 𝒪_{S', s'}` containing the unique point over `x` on
which the pullback of `F` is flat over `𝒪_{S', s'}`. -/
@[stacks 05KT]
theorem existsElementaryEtaleNeighborhoodFlatOver :
    ExistsElementaryEtaleNeighborhoodFlatOver.{u} := by
  intro X S f hft F hqc hfty x hF
  obtain ⟨V, hx, A, hA, i, p, hi, hp, hcomp⟩ :=
    exists_closedImmersion_affineSpace_of_locallyOfFiniteType f x
  exact existsElementaryEtaleNeighborhoodFlatOverAt_of_closedImmersion f F hx i p hcomp hF

/-- In every fibre of a morphism locally of finite type, the locus where a quasi-coherent module of
finite type is flat over the base is open. -/
@[stacks 05M9]
theorem isOpen_isFlatOverAt_fiber_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S) :
    IsOpen {w : f.fiber s | IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s w)} :=
  isOpen_isFlatOverAt_fiber_of_exists existsElementaryEtaleNeighborhoodFlatOver f F s

end AlgebraicGeometry

end
