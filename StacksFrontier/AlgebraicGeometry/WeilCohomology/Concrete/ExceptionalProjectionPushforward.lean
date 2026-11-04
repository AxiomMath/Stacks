module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundlePushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionZeroPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoheightOfEquidimensional
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassPushforwardGrassmannian
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimensionParts
public import StacksFrontier.AlgebraicGeometry.Chow.BlowupExceptionalBundle

/-!
# `γ` commutes with pushforward along the projection of the exceptional divisor

Let `i : Z ⟶ X` be a closed immersion of nonempty smooth projective schemes over `k`,
equidimensional of dimensions `e < n`, `b : X' ⟶ X` the blowing up in `Z` and `π : E ⟶ Z` the
projection of its exceptional divisor. By Tag 0FUT, `E` is, over `Z`, the projective bundle
`𝐏(𝒞)` of the conormal sheaf of the centre, which is finite locally free of rank `n - e`. Hence,
for data (D0), (D1), (D2') satisfying (A1)–(A7), `γ` commutes with pushforward along `π`: the
isomorphism `E ≅ 𝐏(𝒞)` is an open and closed immersion with a retraction, along which `γ`
commutes with pushforward (codimension `0`, and Lemma 0FIP's retraction argument), and along the
projection of `𝐏(𝒞)` it commutes with pushforward by Lemma 0FIN.

This is the input "`π_*γ(j^!θ) = γ(π_*j^!θ)` by Lemma 0FIN because `π` is a projective space
bundle" of the proof of Tag 0FIT.

## Main results

* `Stacks.AlgebraicGeometry.exists_iso_bundle_pullbackSnd_blowUpToBase`: `E ≅ 𝐏(𝒞)` over `Z`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.exists_iso_bundle_exceptionalObj`: the same in
  the category of smooth projective schemes over `k`.
* `Stacks.WeilCohomology.WeilChernData.pushforwardCompatible_exceptionalProj`.

## References

* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
* [Stacks Project, Tag 0FIN](https://stacks.math.columbia.edu/tag/0FIN)
* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.AlgebraicGeometry

variable {S X Z : Scheme.{u}} (f : X ⟶ S) [Smooth f]

/-- The inverse of `toImage` followed by `i` is the inclusion of the subscheme `ker i`. -/
private theorem inv_toImage_comp_eq_subschemeι (i : Z ⟶ X) [IsClosedImmersion i] :
    inv i.toImage ≫ i = i.ker.subschemeι :=
  (IsIso.inv_comp_eq _).mpr (Scheme.Hom.toImage_imageι i).symm

/-- If `i ≫ g` is smooth, then so is `i.ker.subschemeι ≫ g`. -/
private theorem smooth_subschemeι_comp {T : Scheme.{u}} (g : X ⟶ T) (i : Z ⟶ X)
    [IsClosedImmersion i] [Smooth (i ≫ g)] : Smooth (i.ker.subschemeι ≫ g) := by
  rw [← inv_toImage_comp_eq_subschemeι, Category.assoc]
  infer_instance

/-- **The exceptional divisor `E = X' ×_X Z` of the blowing up along a closed immersion
`i : Z ⟶ X` of schemes smooth over `S` is, over `Z`, the projective bundle of the pullback to `Z`
of the conormal sheaf `ℐ/ℐ²` of the centre** (Tag 0FUT), in the presentation
`Stacks.Chow.bundle` the projective bundle formula and axiom (A3) are stated for. -/
theorem exists_iso_bundle_pullbackSnd_blowUpToBase (i : Z ⟶ X) [IsClosedImmersion i]
    [Smooth (i ≫ f)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback i.toImage).obj
        (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι))] :
    ∃ φ : Limits.pullback (Stacks.Blowup.blowUpToBase i.ker) i ≅
        Stacks.Chow.bundle ((Scheme.Modules.pullback i.toImage).obj
          (Stacks.Conormal.conormalSheafDegreeOne i.ker.subschemeι)),
      φ.hom ≫ Stacks.Chow.bundleProj _ = pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i := by
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
  -- `E ≅ V(ℐ')`, the exceptional divisor of `AlgebraicGeometry.blowUp`
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
  -- the base change of the projective bundle along the isomorphism `Z ≅ V(ℐ)`
  have hβ := Stacks.ProjectiveBundle.isPullback_baseChangeHom i.toImage M hqc M' hqc' (Iso.refl _)
  have : IsIso (Stacks.ProjectiveBundle.baseChangeHom i.toImage M hqc M' hqc' (Iso.refl _)) :=
    hβ.isIso_snd_of_isIso
  set β := Stacks.ProjectiveBundle.baseChangeHom i.toImage M hqc M' hqc' (Iso.refl _)
  set κ := h'.isoPullback
  set δ := exceptionalDivisorIsoProjectiveBundle f i.ker
  set ε := Stacks.ProjectiveBundle.presentationIso M hqc
  refine ⟨κ.symm ≪≫ δ ≪≫ ε.symm ≪≫ (asIso β).symm, ?_⟩
  have hb : Stacks.Chow.bundleProj M' ≫ i.toImage =
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
  exact (Category.assoc _ _ _).trans ((congrArg (ε.inv ≫ ·) (IsIso.inv_hom_id_assoc β _)).trans hε)

end Stacks.AlgebraicGeometry

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

/-- **The exceptional divisor is a projective bundle over the centre**, in the category of smooth
projective schemes over `k`: for `X`, `Z` equidimensional of dimensions `n > e`, there are a
module `𝒞` on `Z`, finite locally free of rank `n - e`, and mutually inverse morphisms
`E ⇄ 𝐏(𝒞)` over `Z`. -/
theorem exists_iso_bundle_exceptionalObj {n e : ℕ} (hX : RelativeDimension X.obj.hom n)
    (hZ : RelativeDimension Z.obj.hom e) (he : e < n) :
    ∃ (M : Z.obj.left.Modules)
      (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M
        (n - e - 1 + 1))
      (φ : exceptionalObj i ⟶ SmoothProjectiveScheme.bundle Z M (n - e - 1))
      (ψ : SmoothProjectiveScheme.bundle Z M (n - e - 1) ⟶ exceptionalObj i),
      φ ≫ ψ = 𝟙 _ ∧ ψ ≫ φ = 𝟙 _ ∧
        φ ≫ SmoothProjectiveScheme.bundleProj Z M (n - e - 1) = exceptionalProj i := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by rw [Over.w i.hom]; infer_instance
  have hinv := Stacks.AlgebraicGeometry.inv_toImage_comp_eq_subschemeι i.hom.left
  have := Stacks.AlgebraicGeometry.smooth_subschemeι_comp X.obj.hom i.hom.left
  have hV : RelativeDimension (i.hom.left.ker.subschemeι ≫ X.obj.hom) e := by
    have h := RelativeDimension.of_isPullback (IsPullback.of_horiz_isIso
      (fst := inv i.hom.left.toImage) (g := 𝟙 (Spec (.of k)))
      (snd := i.hom.left.ker.subschemeι ≫ X.obj.hom) (f := Z.obj.hom)
      ⟨by rw [Category.comp_id, ← hinv, Category.assoc, Over.w i.hom]⟩) hZ
    exact h
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
  obtain ⟨φ, hφ⟩ :=
    Stacks.AlgebraicGeometry.exists_iso_bundle_pullbackSnd_blowUpToBase X.obj.hom i.hom.left
  have hφ' : φ.hom ≫ Stacks.Chow.bundleProj _ ≫ Z.obj.hom = pullback.snd _ _ ≫ Z.obj.hom := by
    rw [reassoc_of% hφ]
  refine ⟨_, hM', SmoothProjectiveScheme.homMk φ.hom ?_, SmoothProjectiveScheme.homMk φ.inv ?_,
    SmoothProjectiveScheme.hom_ext' φ.hom_inv_id, SmoothProjectiveScheme.hom_ext' φ.inv_hom_id,
    SmoothProjectiveScheme.hom_ext' hφ⟩
  · exact hφ'
  · show φ.inv ≫ pullback.snd _ _ ≫ Z.obj.hom = Stacks.Chow.bundleProj _ ≫ Z.obj.hom
    exact (congrArg (φ.inv ≫ ·) hφ').symm.trans (Iso.inv_hom_id_assoc φ _)

end Stacks.WeilCohomology.SmoothProjectiveScheme


namespace Stacks.WeilCohomology.WeilChernData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **`γ` commutes with pushforward along an isomorphism** of smooth projective schemes, given by
mutually inverse morphisms `φ`, `ψ`: `φ` is an open and closed immersion with retraction `ψ`. -/
theorem pushforwardCompatible_of_inverse {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (φ : X ⟶ Y) (ψ : Y ⟶ X) (hφψ : φ ≫ ψ = 𝟙 X) (hψφ : ψ ≫ φ = 𝟙 Y) :
    𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing φ := by
  have : IsIso φ.hom.left := ⟨ψ.hom.left, congrArg (fun g ↦ g.hom.left) hφψ,
    congrArg (fun g ↦ g.hom.left) hψφ⟩
  have : IsIso ψ.hom.left := ⟨φ.hom.left, congrArg (fun g ↦ g.hom.left) hψφ,
    congrArg (fun g ↦ g.hom.left) hφψ⟩
  intro d d' hX hY p q hq α
  have := hX.nonempty
  have := hY.nonempty
  obtain rfl : d = d' := le_antisymm
    (le_of_relativeDimension φ hY.relativeDimension hX.relativeDimension)
    (le_of_relativeDimension ψ hX.relativeDimension hY.relativeDimension)
  obtain rfl : q = p + 0 := by omega
  exact 𝔚.toWeilData.cycleClass_pushforward_of_closedImmersion_of_retraction 𝔚.perfectPairing
    𝔚.cycleClassPullback 𝔚.cycleClassMul (𝔚.cycleClass_congr Y) φ ψ hφψ hX hY 0 (by omega)
    (𝔚.pushforward_unitTw_eq_cycleClass_of_isOpenImmersion φ hX hY) p α

/-- **`γ` commutes with pushforward along the projection `π : E ⟶ Z` of the exceptional divisor**
of the blowing up of `X` in `Z`, for `X`, `Z` equidimensional of dimensions `n > e`: `π` is the
projective bundle of a module of rank `n - e` up to isomorphism over `Z` (Tag 0FUT), and `γ`
commutes with pushforward along projective bundles (Lemma 0FIN) and along isomorphisms. -/
theorem pushforwardCompatible_exceptionalProj {Z X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : Z ⟶ X) [IsClosedImmersion i.hom.left] {n e : ℕ} (hX : RelativeDimension X.obj.hom n)
    (hZ : RelativeDimension Z.obj.hom e) (he : e < n) :
    𝔚.toWeilData.PushforwardCompatible 𝔚.perfectPairing (exceptionalProj i) := by
  obtain ⟨M, hM, φ, ψ, hφψ, hψφ, hφp⟩ := exists_iso_bundle_exceptionalObj i hX hZ he
  rw [← hφp]
  intro d c hE hZ' p q hq α
  exact WeilData.PushforwardCompatible.comp
    (isNonemptyEquidimensional_bundle Z M (n - e - 1) hZ') (𝔚.cycleClass_congr Z)
    (𝔚.pushforwardCompatible_of_inverse φ ψ hφψ hψφ)
    (fun d e hB hZ'' p q h α ↦ 𝔚.cycleClass_equidimensionalPushforward_bundleProj hZ'' hB p q h α)
    d c hE hZ' p q hq α

end Stacks.WeilCohomology.WeilChernData

end
