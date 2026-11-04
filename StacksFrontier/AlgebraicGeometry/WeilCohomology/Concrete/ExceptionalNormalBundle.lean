module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExceptionalProjectionPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupExcess
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassCupVanishing
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilChernData
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.PresentationTwistIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BlowupExceptionalBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Pullback

/-!
# The normal bundle of the exceptional divisor

Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over `k`, with blowing up
`b : X' ⟶ X`, exceptional divisor `j : E ⟶ X'` and `π : E ⟶ Z`. By Tag 0FUT, `E` is, over `Z`, the
projective bundle `𝐏(𝒞)` of the conormal sheaf of the centre, and the twist `𝒪(1)` of that bundle
structure is `𝒪_{X'}(-E)|_E`. So `𝒪_{X'}(E)|_E ≅ 𝒪_{𝐏(𝒞)}(-1)`, and for data satisfying (A2) the
pullback to `𝐏(𝒞)` of `c₁^H(𝒪_{X'}(E))` is `-c₁^H(𝒪_{𝐏(𝒞)}(1))`. This is an input of the proof of
Tag 0FIT.

Tag 0FUT's twist is the twisting sheaf of the relative `Proj` situation of `Sym(𝒞)`, while
`c₁^H(𝒪_P(1))` in axiom (A3) is that of the tautological twist of `Stacks.Chow.bundle`. The scheme
level statement and the helper `exists_iso_bundle_exceptionalObj_c₁_of_twistIso` are stated for an
arbitrary agreement `hT` of these two twists along the comparison of presentations
(`Stacks.ProjectiveBundle.presInv`); the agreement is
`Stacks.ProjectiveBundle.nonempty_presentationTwistIso`, which gives the statement itself.

## Main results

* `Stacks.AlgebraicGeometry.exists_iso_bundle_pullbackSnd_blowUpToBase_twist`: `E ≅ 𝐏(𝒞)` over
  `Z`, with `j^*𝒪_{X'}(-E)` carried to the tautological twist.
* `Stacks.WeilCohomology.picardClassOf_pullback_divisorSheaf_eq_neg`: `[g^*𝒪(D)] = -[g^*𝒪(-D)]`.
* `Stacks.WeilCohomology.WeilChernData.exists_iso_bundle_exceptionalObj_c₁_of_twistIso`: the
  statement in the category of smooth projective schemes, with `c₁^H`, from `hT`.
* `Stacks.WeilCohomology.WeilChernData.exists_iso_bundle_exceptionalObj_c₁`: **the statement**.

## References

* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u w

namespace Stacks.AlgebraicGeometry

variable {S X Z : Scheme.{u}} (f : X ⟶ S) [Smooth f]

/-- Inverting `i.toImage` and composing with `i` gives the inclusion of the kernel subscheme. -/
private theorem inv_toImage_comp_eq_subschemeι (i : Z ⟶ X) [IsClosedImmersion i] :
    inv i.toImage ≫ i = i.ker.subschemeι :=
  (IsIso.inv_comp_eq _).mpr (Scheme.Hom.toImage_imageι i).symm

/-- If `i ≫ g` is smooth, so is the composite of the kernel subscheme inclusion with `g`. -/
private theorem smooth_subschemeι_comp {T : Scheme.{u}} (g : X ⟶ T) (i : Z ⟶ X)
    [IsClosedImmersion i] [Smooth (i ≫ g)] : Smooth (i.ker.subschemeι ≫ g) := by
  rw [← inv_toImage_comp_eq_subschemeι, Category.assoc]
  infer_instance

/-- **`E ≅ 𝐏(𝒞)` over `Z`, with `𝒪_{X'}(-E)|_E` the twist `𝒪(1)`**, in the presentation
`Stacks.Chow.bundle`, given that the two twists of the projective bundle agree (`hT`). The
identification is the one of `Stacks.AlgebraicGeometry.exists_iso_bundle_pullbackSnd_blowUpToBase`;
the twist is carried by Tag 0FUT (`Stacks.AlgebraicGeometry.exceptionalTwistOneIso`), `hT` and the
base change of the tautological twist (`Stacks.RelativeProj.symTwistBaseChangeIso`). -/
theorem exists_iso_bundle_pullbackSnd_blowUpToBase_twist (i : Z ⟶ X) [IsClosedImmersion i]
    [Smooth (i ≫ f)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback i.toImage).obj
        (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι))]
    (hT : ∀ {Y : Scheme.{u}} (M : Y.Modules) [M.IsQuasicoherent]
      (hqc : Stacks.SymGraded.IsQuasicoherentPieces M),
      Nonempty ((Scheme.Modules.pullback (Stacks.ProjectiveBundle.presInv M hqc)).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist M hqc) ≅
        Stacks.RelativeProj.Situation.twistSheaf (Stacks.SymGraded.symSituation M)
          ((1 : ℕ) : ℤ))) :
    ∃ φ : Limits.pullback (Stacks.Blowup.blowUpToBase i.ker) i ≅
        Stacks.Chow.bundle ((Scheme.Modules.pullback i.toImage).obj
          (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι)),
      φ.hom ≫ Stacks.Chow.bundleProj _ = pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i ∧
      Nonempty ((Scheme.Modules.pullback φ.inv).obj
          ((modulePullback (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i).toLRSHom.toShHom).obj
            (Stacks.ClosedImmersion.idealSheaf
              (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i).toLRSHom.toShHom)) ≅
        Stacks.Chow.bundleTwist ((Scheme.Modules.pullback i.toImage).obj
          (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι))) := by
  set M : (i.ker.subscheme : Scheme.{u}).Modules :=
    Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι with hM
  set M' : Z.Modules := (Scheme.Modules.pullback i.toImage).obj M with hM'
  have hinv := inv_toImage_comp_eq_subschemeι i
  have := smooth_subschemeι_comp f i
  have hqc := Stacks.Chow.bundlePieces M
  have hqc' := Stacks.Chow.bundlePieces M'
  have : M.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M
  have : M'.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M'
  have h' : IsPullback ((exceptionalIdeal i.ker).subschemeι ≫
        (AlgebraicGeometry.blowUpIso i.ker).hom)
      (Scheme.IdealSheafData.subschemeMap (exceptionalIdeal i.ker) i.ker (blowUpToBase i.ker)
        (i.ker.le_map_comap (blowUpToBase i.ker)) ≫ inv i.toImage)
      (Stacks.Blowup.blowUpToBase i.ker) i :=
    (isPullback_exceptionalDivisor_toCentre i.ker).of_iso (Iso.refl _)
      (AlgebraicGeometry.blowUpIso i.ker) (asIso (inv i.toImage)) (Iso.refl X)
      (by simp) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id, AlgebraicGeometry.blowUpIso_hom_blowUpToBase])
      (by rw [Iso.refl_hom, Category.comp_id, asIso_hom, hinv])
  have hβ := Stacks.ProjectiveBundle.isPullback_baseChangeHom i.toImage M hqc M' hqc' (Iso.refl _)
  have : IsIso (Stacks.ProjectiveBundle.baseChangeHom i.toImage M hqc M' hqc' (Iso.refl _)) :=
    hβ.isIso_snd_of_isIso
  set β := Stacks.ProjectiveBundle.baseChangeHom i.toImage M hqc M' hqc' (Iso.refl _)
  set κ := h'.isoPullback
  set δ := exceptionalDivisorIsoProjectiveBundle f i.ker
  set ε := Stacks.ProjectiveBundle.presentationIso M hqc
  refine ⟨κ.symm ≪≫ δ ≪≫ ε.symm ≪≫ (asIso β).symm, ?_, ?_⟩
  · have hb : Stacks.Chow.bundleProj M' ≫ i.toImage =
        β ≫ Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProjToBase
          (Stacks.SymGraded.situationSheafGradedAlgebra M hqc).toGradedAlgebra :=
      (Stacks.ProjectiveBundle.baseChangeHom_toBase i.toImage M hqc M' hqc' _).symm
    have hε : ε.inv ≫ Stacks.AlgebraicGeometry.RelativeProjGlue.relativeProjToBase
        (Stacks.SymGraded.situationSheafGradedAlgebra M hqc).toGradedAlgebra =
          Stacks.RelativeProj.projectiveBundleToBase _ M := by
      rw [← Stacks.ProjectiveBundle.presentationIso_hom_toBase M hqc, Iso.inv_hom_id_assoc]
    have hκ : κ.inv ≫ Scheme.IdealSheafData.subschemeMap (exceptionalIdeal i.ker) i.ker
        (blowUpToBase i.ker) (i.ker.le_map_comap (blowUpToBase i.ker)) =
          pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i ≫ i.toImage := by
      rw [← cancel_epi κ.hom, Iso.hom_inv_id_assoc, ← Category.assoc, h'.isoPullback_hom_snd,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← cancel_mono i.toImage]
    show (κ.inv ≫ δ.hom ≫ ε.inv ≫ inv β) ≫ Stacks.Chow.bundleProj M' ≫ i.toImage = _
    refine (congrArg _ hb).trans ?_
    refine (Category.assoc _ _ _).trans (congrArg (κ.inv ≫ ·) ?_) |>.trans hκ
    refine (Category.assoc _ _ _).trans (congrArg (δ.hom ≫ ·) ?_) |>.trans
      (exceptionalDivisorIsoProjectiveBundle_hom_toCentre f i.ker)
    exact (Category.assoc _ _ _).trans
      ((congrArg (ε.inv ≫ ·) (IsIso.inv_hom_id_assoc β _)).trans hε)
  · -- the twist
    have hφ₁ := h'.isoPullback_hom_fst
    have hfst : h'.isoPullback.symm.hom ≫
        ((exceptionalIdeal i.ker).subschemeι ≫ (AlgebraicGeometry.blowUpIso i.ker).hom) =
          pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i :=
      (Iso.inv_comp_eq _).mpr hφ₁.symm
    let Q :=
      Stacks.Conormal.AffineCotangent.SourceTransport.modulePullbackIdealSheafIsoOfIsoSourceOfCompEq
        h'.isoPullback.symm _ _ hfst ≪≫
      (modulePullback h'.isoPullback.inv.toLRSHom.toShHom).mapIso
        (Stacks.Conormal.AffineCotangent.Transport.idealSheafPullbackIsoOfIsoTarget
          (exceptionalIdeal i.ker).subschemeι (AlgebraicGeometry.blowUpIso i.ker) _ rfl)
    obtain ⟨G⟩ := hT M hqc
    have heq : (κ.symm ≪≫ δ ≪≫ ε.symm ≪≫ (asIso β).symm).inv ≫ κ.inv ≫ δ.hom = β ≫ ε.hom := by
      simp
    have heq' : β ≫ ε.hom ≫ Stacks.ProjectiveBundle.presInv M hqc = β :=
      (congrArg (β ≫ ·) ε.hom_inv_id).trans (Category.comp_id β)
    exact ⟨(Scheme.Modules.pullback _).mapIso Q ≪≫
      (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullback κ.inv).mapIso
        (exceptionalTwistOneIso f i.ker).symm) ≪≫
      (Scheme.Modules.pullbackComp _ κ.inv).app _ ≪≫
      (Scheme.Modules.pullbackComp _ δ.hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr heq).app _ ≪≫
      (Scheme.Modules.pullback (β ≫ ε.hom)).mapIso G.symm ≪≫
      (Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr ((Category.assoc _ _ _).trans heq')).app _ ≪≫
      Stacks.RelativeProj.symTwistBaseChangeIso i.toImage M M' (Iso.refl _)⟩

end Stacks.AlgebraicGeometry

namespace Stacks.WeilCohomology

/-- **The pullback of `𝒪(D)` has the negative class of the pullback of `𝒪(-D)`.** For an effective
Cartier divisor `D` on `X` and `g : P ⟶ X`, if `g^*𝒪_X(-D) ≅ ℒ` then `[g^*𝒪_X(D)] = -[ℒ]` in
`Pic(P)`. -/
theorem picardClassOf_pullback_divisorSheaf_eq_neg {P X : Scheme.{u}} (g : P ⟶ X)
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] (L : P.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L)
    (e : (Scheme.Modules.pullback g).obj (Stacks.Divisors.negativeTwist' D) ≅ L)
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (Stacks.Divisors.divisorSheaf D))) :
    picardClassOf P ((Scheme.Modules.pullback g).obj (Stacks.Divisors.divisorSheaf D)) h =
      -picardClassOf P L hL := by
  have hO := Stacks.Divisors.isInvertible_invertibleSheaf_picard D
  have hN := Stacks.Divisors.isInvertible_negativeTwist_picard D
  have hLN := Stacks.SheafOfModules.isInvertible_schemeTensor X _ _ hO hN
  have htriv : Stacks.SheafOfModules.IsTrivial X.presheaf X.ringCatIsSheaf
      (Stacks.SheafOfModules.schemeTensor X (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.negativeTwist' D)) := by
    have := Stacks.Divisors.isTensorInvertible_negativeTwist D
    exact ⟨Stacks.SheafOfModules.Scheme.evaluationIso X (Stacks.Divisors.negativeTwist' D)⟩
  have key :=
    Stacks.SheafOfModules.pullbackPicardClass_eq_neg_of_isTrivial_tensorSheaf g _ _ hO hN hLN htriv
  have hc : Stacks.SheafOfModules.pullbackPicardClass g (Stacks.Divisors.negativeTwist' D) hN =
      picardClassOf P L hL :=
    (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e⟩
  show Stacks.SheafOfModules.pullbackPicardClass g (Stacks.Divisors.invertibleSheaf' D) hO = _
  rw [← hc, key, neg_neg]

end Stacks.WeilCohomology

namespace Stacks.WeilCohomology.WeilChernData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **The normal bundle of the exceptional divisor** (the input `𝒪_{X'}(E)|_E = 𝒪_E(-1)` of the
proof of Tag 0FIT). Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over `k`,
equidimensional of dimensions `e < n`, with blowing up `X'`, exceptional divisor `j : E ⟶ X'` and
`π : E ⟶ Z`. Then `E` is, over `Z`, the projective bundle `𝐏(ℳ)` of a module of rank `n - e`,
and for data satisfying (A1)–(A7) the pullback to `𝐏(ℳ)` of `c₁^H(𝒪_{X'}(E))` is
`-c₁^H(𝒪_{𝐏(ℳ)}(1)) + p^*w` for some `w ∈ H^2(Z)(1)`. -/
theorem exists_iso_bundle_exceptionalObj_c₁_of_twistIso
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    {n e : ℕ} (hX : RelativeDimension X.obj.hom n)
    (hZ : RelativeDimension Z.obj.hom e) (he : e < n)
    (hT : ∀ {Y : Scheme.{u}} (M : Y.Modules) [M.IsQuasicoherent]
        (hqc : Stacks.SymGraded.IsQuasicoherentPieces M),
        Nonempty ((Scheme.Modules.pullback (Stacks.ProjectiveBundle.presInv M hqc)).obj
            (Stacks.ProjectiveBundleSplitting.tautologicalTwist M hqc) ≅
          Stacks.RelativeProj.Situation.twistSheaf (Stacks.SymGraded.symSituation M)
            ((1 : ℕ) : ℤ))) :
    ∃ (M : Z.obj.left.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M
        (n - e - 1 + 1))
      (φ : exceptionalObj i ⟶ SmoothProjectiveScheme.bundle Z M (n - e - 1))
      (ψ : SmoothProjectiveScheme.bundle Z M (n - e - 1) ⟶ exceptionalObj i),
      φ ≫ ψ = 𝟙 _ ∧ ψ ≫ φ = 𝟙 _ ∧
        φ ≫ SmoothProjectiveScheme.bundleProj Z M (n - e - 1) = exceptionalProj i ∧
        ∃ w : tateTwist F 𝔚.tate (𝔚.H Z) 1,
          𝔚.pullTw (ψ ≫ exceptionalHom i) 1
              (𝔚.c₁ (blowupObj i)
                (haveI : Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalDivisor i) :=
                  isEffectiveCartierDivisor_exceptionalIdeal i
                picardClassOf _
                (Stacks.Divisors.divisorSheaf (exceptionalDivisor i))
                (Stacks.Divisors.isInvertible_divisorSheaf (exceptionalDivisor i)))) =
            -𝔚.bundleClass Z M (n - e - 1) +
              𝔚.pullTw (SmoothProjectiveScheme.bundleProj Z M (n - e - 1)) 1 w := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  have hinv := Stacks.AlgebraicGeometry.inv_toImage_comp_eq_subschemeι i.hom.left
  have := Stacks.AlgebraicGeometry.smooth_subschemeι_comp X.obj.hom i.hom.left
  have hV : RelativeDimension (i.hom.left.ker.subschemeι ≫ X.obj.hom) e :=
    RelativeDimension.of_isPullback (IsPullback.of_horiz_isIso
      (fst := inv i.hom.left.toImage) (g := 𝟙 (Spec (.of k)))
      (snd := i.hom.left.ker.subschemeι ≫ X.obj.hom) (f := Z.obj.hom)
      ⟨by rw [Category.comp_id, ← hinv, Category.assoc, Over.w i.hom]⟩) hZ
  have hC := Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_relativeDimension
    i.hom.left.ker.subschemeι X.obj.hom n e hX hV
  have hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne i.hom.left.ker.subschemeι) (n - e - 1 + 1) := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n - e)]
    exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (Stacks.Conormal.conormalDegreeOneIso _) hC
  have hM' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback i.hom.left.toImage).obj
        (Stacks.Conormal.conormalSheafDegreeOne i.hom.left.ker.subschemeι)) (n - e - 1 + 1) :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ _
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (Stacks.Conormal.conormalSheafDegreeOne i.hom.left.ker.subschemeι) (n - e - 1 + 1)
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    ((Scheme.Modules.pullback i.hom.left.toImage).obj
      (Stacks.Conormal.conormalSheafDegreeOne i.hom.left.ker.subschemeι)) (n - e - 1 + 1)
  obtain ⟨φ, hφ, ⟨Θ⟩⟩ := Stacks.AlgebraicGeometry.exists_iso_bundle_pullbackSnd_blowUpToBase_twist
    X.obj.hom i.hom.left hT
  have hφ' : φ.hom ≫ Stacks.Chow.bundleProj _ ≫ Z.obj.hom = pullback.snd _ _ ≫ Z.obj.hom := by
    rw [reassoc_of% hφ]
  refine ⟨_, hM', SmoothProjectiveScheme.homMk φ.hom ?_, SmoothProjectiveScheme.homMk φ.inv ?_,
    SmoothProjectiveScheme.hom_ext' φ.hom_inv_id, SmoothProjectiveScheme.hom_ext' φ.inv_hom_id,
    SmoothProjectiveScheme.hom_ext' hφ, 0, ?_⟩
  · exact hφ'
  · show φ.inv ≫ pullback.snd _ _ ≫ Z.obj.hom = Stacks.Chow.bundleProj _ ≫ Z.obj.hom
    exact (congrArg (φ.inv ≫ ·) hφ').symm.trans (Iso.inv_hom_id_assoc φ _)
  · have : Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalDivisor i) :=
      isEffectiveCartierDivisor_exceptionalIdeal i
    rw [map_zero, add_zero]
    refine (𝔚.pullback _ _ _).trans ?_
    unfold FirstChernClassData.bundleClass
    refine Eq.trans ?_ (map_neg _ _)
    refine congrArg _ ?_
    exact @Stacks.WeilCohomology.picardClassOf_pullback_divisorSheaf_eq_neg _ _
      (φ.inv ≫ pullback.fst _ _) (exceptionalDivisor i)
      (isEffectiveCartierDivisor_exceptionalIdeal i) _ _
      (((Scheme.Modules.pullbackComp φ.inv (pullback.fst _ _)).app _).symm ≪≫
        (Scheme.Modules.pullback φ.inv).mapIso
          ((Scheme.Modules.pullback (pullback.fst _ _)).mapIso
            (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSourceOfCompEq
              (asIso (exceptionalToSubscheme i)) _ _
              (exceptionalToSubscheme_subschemeι i)).symm) ≪≫
        Θ) _

/-- **The normal bundle of the exceptional divisor** (the input `𝒪_{X'}(E)|_E = 𝒪_E(-1)` of the
proof of Tag 0FIT). Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over `k`,
equidimensional of dimensions `e < n`, with blowing up `X'`, exceptional divisor `j : E ⟶ X'` and
`π : E ⟶ Z`. Then `E` is, over `Z`, the projective bundle `𝐏(ℳ)` of a module `ℳ` finite locally
free of rank `n - e`, by mutually inverse morphisms `φ`, `ψ` with `φ ≫ p = π`, and for data
satisfying (A1)–(A7) the pullback along `ψ ≫ j` of `c₁^H(𝒪_{X'}(E))` is
`-c₁^H(𝒪_{𝐏(ℳ)}(1)) + p^*w` for some `w ∈ H^2(Z)(1)` (here `w = 0`).

`𝒪_{X'}(-E)|_E` is the twist `𝒪(1)` of the bundle structure by Tag 0FUT, read on the
presentation of the projective bundle the axioms are stated at through
`Stacks.ProjectiveBundle.nonempty_presentationTwistIso`; then (A2) and additivity of `c₁^H`. -/
theorem exists_iso_bundle_exceptionalObj_c₁
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    {n e : ℕ}
    (hX : RelativeDimension X.obj.hom n) (hZ : RelativeDimension Z.obj.hom e) (he : e < n) :
    ∃ (M : Z.obj.left.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M
        (n - e - 1 + 1))
      (φ : exceptionalObj i ⟶ SmoothProjectiveScheme.bundle Z M (n - e - 1))
      (ψ : SmoothProjectiveScheme.bundle Z M (n - e - 1) ⟶ exceptionalObj i),
      φ ≫ ψ = 𝟙 _ ∧ ψ ≫ φ = 𝟙 _ ∧
        φ ≫ SmoothProjectiveScheme.bundleProj Z M (n - e - 1) = exceptionalProj i ∧
        ∃ w : tateTwist F 𝔚.tate (𝔚.H Z) 1,
          𝔚.pullTw (ψ ≫ exceptionalHom i) 1
              (𝔚.c₁ (blowupObj i)
                (haveI : Stacks.Divisors.IsEffectiveCartierDivisor (exceptionalDivisor i) :=
                  isEffectiveCartierDivisor_exceptionalIdeal i
                picardClassOf _
                (Stacks.Divisors.divisorSheaf (exceptionalDivisor i))
                (Stacks.Divisors.isInvertible_divisorSheaf (exceptionalDivisor i)))) =
            -𝔚.bundleClass Z M (n - e - 1) +
              𝔚.pullTw (SmoothProjectiveScheme.bundleProj Z M (n - e - 1)) 1 w :=
  𝔚.exists_iso_bundle_exceptionalObj_c₁_of_twistIso i hX hZ he
    (fun M _ hqc => Stacks.ProjectiveBundle.nonempty_presentationTwistIso M hqc)

end Stacks.WeilCohomology.WeilChernData

end
