module

public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.NonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerInterfaces
public import StacksFrontier.AlgebraicGeometry.SectionExtension.NilpotentRestrict
public import StacksFrontier.Deformation.Artin.Versality.OpennessObstruction

/-!
# Stacks 0CXU with condition (4) for special towers only

The proof of Stacks 0CXU (openness of versality) applies its condition (4) to one tower: the tower
of Stacks 0G2S (`Deformation.Artin.exists_sequence_firstOrderThickenings_without_localRetraction`)
over an affine scheme `U` of finite type over `S`, at finite type points `uₙ` with no
specializations among them, whose `n`-th step has ideal the residue field `κ(uₙ)`. When `S` is
Jacobson so is `U`, the `uₙ` are pairwise distinct closed points, and the ring tower `Γ(Uₙ)` is
special (`AlgebraicGeometry.C1590Private.IsSpecialTower`): the kernel of its `n`-th step is
killed by the functions vanishing at `uₙ`. So condition (4) for special towers
(`AlgebraicGeometry.C1590Private.IsSpecialSquareZeroTowerEffectiveOnClasses`) suffices.

The proofs are those of `Deformation.Artin.exists_cocone_of_isSquareZeroTowerEffectiveOnClasses`,
`Deformation.Artin.exists_open_isVersalAt_of_isAffine_of_hasLocalRetractions`,
`Deformation.Artin.isOpenVersality_of_hasLocalRetractions` and
`Deformation.Artin.isOpenVersality_of_isSquareZeroTowerEffectiveOnClasses`, with the hypothesis
on towers replaced by the one for special towers, and the specialness of the tower of Stacks 0G2S
checked where it is built.

## Main results

* `AlgebraicGeometry.C1590Private.mul_eq_zero_of_kernel_iso_residueField`: a step whose ideal
  sheaf is the residue field sheaf at `y` has its kernel on global functions killed by the
  functions vanishing at `y`.
* `AlgebraicGeometry.C1590Private.isOpenVersality_of_isSpecialSquareZeroTowerEffectiveOnClasses`:
  openness of versality from local retractions, descent along first-order thickenings and
  effectivity of special towers.
* `AlgebraicGeometry.C1590Private.specialTowerOpenVersality`: (A), Stacks 0CXU with condition
  (4) for special towers, over a locally Noetherian Jacobson base.

## References

* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0G2S](https://stacks.math.columbia.edu/tag/0G2S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin
open Stacks.AlgebraicGeometry.ClosedImmersionTFAE

universe u v w

namespace AlgebraicGeometry.C1590Private

/-! ### The step kernels of the tower of Stacks 0G2S -/

/-- A global function vanishing at `y` restricts to `0` on the spectrum of `κ(y)`. -/
theorem fromSpecResidueField_app_top_eq_zero {Y : Scheme.{u}} (y : Y) (r : Γ(Y, ⊤))
    (hr : y ∉ Y.basicOpen r) : (Y.fromSpecResidueField y).app ⊤ r = 0 := by
  apply (basicOpen_eq_bot_iff _).1
  rw [← Scheme.preimage_basicOpen]
  ext t
  simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
    TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  rwa [Scheme.fromSpecResidueField_apply]

/-- **Global functions vanishing at `y` kill the ideal `κ(y)`.** Let the kernel of the structure
map `𝒪_{Y'} → i_* 𝒪_Y` of `i : Y ⟶ Y'` be isomorphic to the residue field sheaf at `y ∈ Y'`. If
`r ∈ Γ(Y', 𝒪)` vanishes at `y` and `z ∈ Γ(Y', 𝒪)` restricts to `0` on `Y`, then `r z = 0`. -/
theorem mul_eq_zero_of_kernel_iso_residueField {Y Y' : Scheme.{u}} (i : Y ⟶ Y') (y : Y')
    (e : kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) ≅
      (Scheme.Modules.pushforward (Y'.fromSpecResidueField y)).obj
        (SheafOfModules.unit (Spec (Y'.residueField y)).ringCatSheaf))
    (r : Γ(Y', ⊤)) (hr : y ∉ Y'.basicOpen r) (z : Γ(Y', ⊤)) (hz : i.appTop z = 0) :
    r * z = 0 := by
  let φ := SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
  let ev := SheafOfModules.evaluation Y'.ringCatSheaf (op ⊤)
  have hex : (ShortComplex.mk (ev.map (kernel.ι φ)) (ev.map φ)
      (by rw [← ev.map_comp, kernel.condition, ev.map_zero])).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ (kernelIsKernel φ) ev)
  obtain ⟨z', hz'⟩ : ∃ z' : ev.obj (kernel φ), (ev.map (kernel.ι φ)).hom z' = z :=
    (ShortComplex.moduleCat_exact_iff _).1 hex z (by
      change (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom).val.app (op ⊤) z = 0
      exact hz)
  let r' : Y'.ringCatSheaf.obj.obj (op ⊤) := r
  have hleft : Function.LeftInverse (ev.map e.inv).hom (ev.map e.hom).hom := fun w =>
    (ev.mapIso e).hom_inv_id_apply w
  have h1 : (ev.map e.hom).hom (r' • z') = 0 := by
    rw [(ev.map e.hom).hom.map_smul r' z']
    exact Scheme.Modules.smul_pushforward_eq_zero_of_app_eq_zero (Y'.fromSpecResidueField y)
      (SheafOfModules.unit _) ⊤ r (fromSpecResidueField_app_top_eq_zero y r hr)
      ((ev.map e.hom).hom z')
  have hz0 : (r' • z' : ev.obj (kernel φ)) = 0 :=
    (hleft (r' • z')).symm.trans ((congrArg (ev.map e.inv).hom h1).trans (map_zero _))
  have h := congrArg (ev.map (kernel.ι φ)).hom hz0
  rwa [LinearMap.map_smul, LinearMap.map_zero, hz'] at h

/-- **Closed immersions through a homeomorphism.** If `j.base` is a homeomorphism, `j ≫ i` is a
closed immersion and `𝒪 → i_* 𝒪` is an epimorphism, then `i` is a closed immersion. -/
theorem isClosedImmersion_of_isHomeomorph_comp {X Y Z : Scheme.{u}} (j : X ⟶ Y) (i : Y ⟶ Z)
    (hj : IsHomeomorph j.base) [IsClosedImmersion (j ≫ i)]
    (hepi : Epi (SheafOfModules.unitToPushforwardObjUnit
      (RingedSpaceModuleAdjunction.structureSheafHom i.toLRSHom.toShHom))) :
    IsClosedImmersion i := by
  let e := hj.homeomorph
  have hie : (i.base : _ → _) = (j ≫ i).base ∘ e.symm := by
    funext y
    have hy : j.base (e.symm y) = y := e.apply_symm_apply y
    conv_lhs => rw [← hy]
    rfl
  exact isClosedImmersion_of_epi_unitToPushforwardObjUnit i
    ⟨hie ▸ (j ≫ i).isClosedEmbedding.comp e.symm.isClosedEmbedding, hepi⟩

/-- A morphism of `BigFppfOver B S hS` commutes with the structure maps in `Scheme`. -/
private theorem toScheme_map_comp_inclusion_map_hom {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {Y Z : BigFppfOver B S hS} (f : Y ⟶ Z) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map Z.hom =
      B.inclusion.map Y.hom := by
  have h := congrArg B.inclusion.map (Over.w f)
  rwa [B.inclusion.map_comp] at h

/-! ### Special towers of first-order thickenings -/

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)

/-- **A cocone over a special tower of first-order thickenings from lift classes.** Let
`obj 0 ⟶ obj 1 ⟶ ⋯` be a tower in `𝒳` over closed immersions, with composites `c m` lying over
first-order thickenings of an affine scheme with Noetherian ring of functions `A` and image in an
affine open of `S`, such that the kernel of the `n`-th step on global functions is killed by the
functions whose image in `A` lies in `𝔪 n`, for pairwise distinct maximal ideals `𝔪 n` of `A`. If
special towers are effective on lift classes, the tower has arrows `ι m : obj m ⟶ ξ` with
`c m ≫ ι m = ι 0`, and `ι 0` lies over a first-order thickening. This is
`Deformation.Artin.exists_cocone_of_isSquareZeroTowerEffectiveOnClasses` for special towers. -/
theorem exists_cocone_of_isSpecialSquareZeroTowerEffectiveOnClasses
    (hE : IsSpecialSquareZeroTowerEffectiveOnClasses B S hS p hp)
    (obj : ℕ → X) (a : ∀ m, obj m ⟶ obj (m + 1)) (c : ∀ m, obj 0 ⟶ obj m)
    (hc0 : c 0 = 𝟙 _) (hc : ∀ m, c (m + 1) = c m ≫ a m)
    (haff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj (obj 0))))
    (W : S.Opens) (hWaff : IsAffineOpen W)
    (hW : Set.range (B.inclusion.map (p.obj (obj 0)).hom).base ⊆ (W : Set S))
    (hthick : ∀ m, Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (c m))))
    (hcl : ∀ m, IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (a m))))
    (hnoeth : IsNoetherianRing
      Γ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj (obj 0)), ⊤))
    (𝔪 : ℕ → Ideal Γ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj (obj 0)), ⊤))
    (h𝔪 : ∀ n, (𝔪 n).IsMaximal) (h𝔪ne : Pairwise fun n m => 𝔪 n ≠ 𝔪 m)
    (hann : ∀ n
      (r : Γ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj (obj (n + 1))), ⊤)),
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (c (n + 1)))).appTop r ∈ 𝔪 n →
      ∀ z, ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (a n))).appTop z = 0 →
        r * z = 0) :
    ∃ (ξ : X) (ι : ∀ m, obj m ⟶ ξ), (∀ m, c m ≫ ι m = ι 0) ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (ι 0))) := by
  classical
  let VS := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let Y : ℕ → AlgebraicGeometry.BigFppfOver B S hS := fun m => p.obj (obj m)
  have hYaff : ∀ m, IsAffine (VS.obj (Y m)) := fun m =>
    Stacks.Thickenings.isAffine_of_isThickening (hthick m).isThickening
  let R : ℕ → Type u := fun m => Γ(VS.obj (Y m), ⊤)
  let fm : ∀ m, R (m + 1) →+* R m := fun m => (VS.map (p.map (a m))).appTop.hom
  have hf : ∀ m, Function.Surjective (fm m) := fun m => by
    have := hcl m
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine (VS.map (p.map (a m)))).2
  have htoBase : ∀ m, SquareZeroTower.toBase fm m = (VS.map (p.map (c m))).appTop.hom := by
    intro m
    induction m with
    | zero =>
      rw [hc0]
      simp only [CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
      rfl
    | succ m ih =>
      rw [SquareZeroTower.toBase, ih, hc, Functor.map_comp, Functor.map_comp,
        Scheme.Hom.comp_appTop]
      rfl
  have hsq : ∀ m, RingHom.ker (SquareZeroTower.toBase fm m) ^ 2 = ⊥ := fun m => by
    rw [htoBase]
    exact ker_appTop_sq_of_isFirstOrderThickening _ (hthick m)
  have hR : ∀ m, B.Contains (Spec (.of (R m))) := fun m =>
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion (VS.obj (Y m)).isoSpec.inv) (Y m).left.2
  -- the structure morphisms factor through `W`
  have hYS : ∀ m, VS.map (p.map (c m)) ≫ B.inclusion.map (Y m).hom =
      B.inclusion.map (Y 0).hom := fun m => toScheme_map_comp_inclusion_map_hom (p.map (c m))
  have hYW : ∀ m, Set.range (B.inclusion.map (Y m).hom).base ⊆ Set.range W.ι.base := by
    intro m
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    obtain ⟨t₀, rfl⟩ := (hthick m).isThickening.2 t
    rw [← Scheme.Hom.comp_apply, hYS]
    exact hW ⟨t₀, rfl⟩
  let τ : ∀ m, VS.obj (Y m) ⟶ W := fun m =>
    IsOpenImmersion.lift W.ι (B.inclusion.map (Y m).hom) (hYW m)
  have hτ : ∀ m, τ m ≫ W.ι = B.inclusion.map (Y m).hom := fun m => IsOpenImmersion.lift_fac _ _ _
  have hτa : ∀ m, VS.map (p.map (a m)) ≫ τ (m + 1) = τ m := fun m => by
    rw [← cancel_mono W.ι, Category.assoc, hτ, hτ]
    exact toScheme_map_comp_inclusion_map_hom (p.map (a m))
  have : IsAffine W := hWaff
  have hWc : B.Contains W := lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion W.ι) hS
  have hΛc : B.Contains (Spec Γ(W, ⊤)) :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion (W : Scheme.{u}).isoSpec.inv) hWc
  let toS : Spec (.of (R 0)) ⟶ S := (VS.obj (Y 0)).isoSpec.inv ≫ B.inclusion.map (Y 0).hom
  let β : ∀ m, Γ(W, ⊤) →+* R m := fun m => (τ m).appTop.hom
  have hspec : ∀ m, Spec.map (CommRingCat.ofHom (β m)) ≫ (W : Scheme.{u}).isoSpec.inv ≫ W.ι =
      (VS.obj (Y m)).isoSpec.inv ≫ B.inclusion.map (Y m).hom := fun m => by
    change Spec.map (τ m).appTop ≫ _ = _
    rw [Scheme.isoSpec_inv_naturality_assoc, hτ]
  let Λ : AugmentedSiteRing (R 0) B S hS toS (hR 0) :=
    { ring := Γ(W, ⊤)
      contains := hΛc
      structureMap := ObjectProperty.homMk ((W : Scheme.{u}).isoSpec.inv ≫ W.ι)
      aug := β 0
      arrow := Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (β 0)))) (by
        apply ObjectProperty.hom_ext
        exact hspec 0)
      arrow_eq := rfl }
  have hβ : ∀ m, (fm m).comp (β (m + 1)) = β m := fun m => by
    change ((VS.map (p.map (a m))).appTop.hom).comp ((τ (m + 1)).appTop.hom) = (τ m).appTop.hom
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hτa]
  have hU : MapsIntoAffineOpen S toS := by
    refine ⟨W, hWaff, fun t => ?_⟩
    have h : (B.inclusion.map (Y 0).hom).base ((VS.obj (Y 0)).isoSpec.inv.base t) ∈
        Set.range W.ι.base := hYW 0 ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at h
  let L := SquareZeroTower.level fm Λ β hβ rfl hR
  let A₀ := algebraOver (R 0) B S hS toS (hR 0)
  let isoA : A₀ ⟶ Y 0 := Over.homMk (ObjectProperty.homMk (VS.obj (Y 0)).isoSpec.inv) rfl
  let isoL : ∀ m, (L m).siteOver ⟶ Y m := fun m =>
    Over.homMk (ObjectProperty.homMk (VS.obj (Y m)).isoSpec.inv) (by
      apply ObjectProperty.hom_ext
      exact (hspec m).symm)
  have : IsIso isoA := by
    have : IsIso (VS.map isoA) := inferInstanceAs (IsIso (VS.obj (Y 0)).isoSpec.inv)
    exact isIso_of_reflects_iso isoA VS
  have hisoL : ∀ m, IsIso (isoL m) := fun m => by
    have : IsIso (VS.map (isoL m)) := inferInstanceAs (IsIso (VS.obj (Y m)).isoSpec.inv)
    exact isIso_of_reflects_iso (isoL m) VS
  have harrow : ∀ m, isoA ≫ p.map (c m) = (L m).arrow ≫ isoL m := fun m => by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change (VS.obj (Y 0)).isoSpec.inv ≫ VS.map (p.map (c m)) =
      Spec.map (CommRingCat.ofHom (SquareZeroTower.toBase fm m)) ≫ (VS.obj (Y m)).isoSpec.inv
    rw [htoBase, CommRingCat.ofHom_hom, Scheme.isoSpec_inv_naturality]
  obtain ⟨x', φx, hφx⟩ := hp.exists_lift isoA (obj 0) rfl
  have hx' : p.obj x' = A₀ := IsHomLift.domain_eq p isoA φx
  choose y ψ hψ using fun m => hp.exists_lift (isoL m) (obj m) rfl
  have hy : ∀ m, p.obj (y m) = (L m).siteOver := fun m => IsHomLift.domain_eq p (isoL m) (ψ m)
  have : IsIso φx := by
    have := hp.isStronglyCartesian_homLift isoA φx
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso p isoA φx
  have hψiso : ∀ m, IsIso (ψ m) := fun m => by
    have := hp.isStronglyCartesian_homLift (isoL m) (ψ m)
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (isoL m) (ψ m)
  have hφxmap : p.map φx = eqToHom hx' ≫ isoA := by
    rw [IsHomLift.fac' p isoA φx]
    simp
  have hψmap : ∀ m, p.map (ψ m) = eqToHom (hy m) ≫ isoL m := fun m => by
    rw [IsHomLift.fac' p (isoL m) (ψ m)]
    simp
  let d : ∀ m, x' ⟶ y m := fun m => φx ≫ c m ≫ inv (ψ m)
  have hdmap : ∀ m, p.map (d m) ≫ eqToHom (hy m) = eqToHom hx' ≫ (L m).arrow := fun m => by
    simp only [d, Functor.map_comp, Functor.map_inv, hφxmap, hψmap, IsIso.inv_comp, inv_eqToHom,
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← Category.assoc isoA, harrow, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  let D : ∀ m, (Under.post p).Fiber (Under.mk (eqToHom hx' ≫ (L m).arrow)) := fun m =>
    ⟨Under.mk (d m), under_mk_eq_of_comp_eqToHom _ _ (hy m) (hdmap m)⟩
  let b : ∀ m, BasedSiteRing.classes p x' hx' (L m) := fun m => Quotient.mk _ (D m)
  have hb : ∀ m, BasedSiteRing.map p x' hx' hp (SquareZeroTower.transition fm Λ β hβ rfl hR m)
      (b (m + 1)) = b m := by
    intro m
    let T := (SquareZeroTower.transition fm Λ β hβ rfl hR m).toHom
    let θ : y m ⟶ y (m + 1) := ψ m ≫ a m ≫ inv (ψ (m + 1))
    have hstep : isoL m ≫ p.map (a m) = T.right ≫ isoL (m + 1) := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change (VS.obj (Y m)).isoSpec.inv ≫ VS.map (p.map (a m)) =
        Spec.map (CommRingCat.ofHom (fm m)) ≫ (VS.obj (Y (m + 1))).isoSpec.inv
      rw [CommRingCat.ofHom_hom, Scheme.isoSpec_inv_naturality]
    have hθ : p.IsHomLift T.right θ := by
      refine IsHomLift.of_fac' p T.right θ (hy m) (hy (m + 1)) ?_
      simp only [θ, Functor.map_comp, Functor.map_inv, hψmap, IsIso.inv_comp, inv_eqToHom,
        Category.assoc]
      rw [reassoc_of% hstep]
      simp only [IsIso.hom_inv_id_assoc]
    have hcart := hp.isStronglyCartesian_homLift T.right θ
    refine AugmentedSiteRing.map_eq_of_lift p x' hx' hp T (D (m + 1)) (D m) θ hcart ?_
    change d m ≫ θ = d (m + 1)
    simp only [d, θ, Category.assoc, IsIso.inv_hom_id_assoc, hc]
  have hspecial : IsSpecialTower fm := by
    refine ⟨hnoeth, 𝔪, h𝔪, h𝔪ne, fun n r hr z hz => hann n r ?_ z (RingHom.mem_ker.mp hz)⟩
    rwa [htoBase] at hr
  obtain ⟨ξc, hξc⟩ := hE R fm hf hsq hspecial toS (hR 0) Λ β hβ rfl hR hU x' hx' b hb
  induction ξc using Quotient.inductionOn with
  | h Dξ =>
  obtain ⟨Q, hQ⟩ := Dξ
  have hm : ∀ m, ∃ μ : y m ⟶ Q.right, d m ≫ μ = Q.hom := by
    intro m
    obtain ⟨e, φ, -, hφ, hmap⟩ := AugmentedSiteRing.representative_map p x' hx' hp
      (SquareZeroTower.limitProj fm Λ β hβ rfl hR m).toHom ⟨Q, hQ⟩
    have h := hξc m
    change AugmentedSiteRing.map p x' hx' hp _ (Quotient.mk _ ⟨Q, hQ⟩) = Quotient.mk _ (D m) at h
    rw [hmap] at h
    obtain ⟨ε⟩ := Quotient.exact h
    refine ⟨ε.inv.1.right ≫ φ, ?_⟩
    have hw := Under.w ε.inv.1
    change d m ≫ ε.inv.1.right = e.1.hom at hw
    rw [← Category.assoc, hw, hφ]
  choose μ hμ using hm
  have h₀ : inv (ψ 0) ≫ μ 0 = inv φx ≫ Q.hom := by
    rw [show inv (ψ 0) = inv φx ≫ d 0 by simp [d, hc0], Category.assoc, hμ]
  refine ⟨Q.right, fun m => inv (ψ m) ≫ μ m, ?_, ?_⟩
  · intro m
    dsimp only
    have h₁ : c m ≫ inv (ψ m) = inv φx ≫ d m := by
      simp only [d, IsIso.inv_hom_id_assoc]
    rw [reassoc_of% h₁, hμ, h₀]
  · dsimp only
    rw [h₀]
    have hDhom := under_hom_eq_of_eq_mk _ hQ
    change p.map Q.hom = _ at hDhom
    rw [Functor.map_comp, Functor.map_comp]
    refine isFirstOrderThickening_iso_comp _ _ ?_
    rw [hDhom]
    refine isFirstOrderThickening_map_eqToHom_comp _ _ _ ?_
    change Stacks.Thickenings.IsFirstOrderThickening
      (Spec.map (CommRingCat.ofHom (SquareZeroTower.limitBase fm)))
    exact Stacks.Smooth.isFirstOrderThickening_specMap
      (CommRingCat.ofHom (SquareZeroTower.limitBase fm))
      (SquareZeroTower.limitBase_surjective fm hf) (SquareZeroTower.ker_limitBase_sq fm hsq)

/-- **Weak effectivity of a special tower of first-order thickenings.** The form in which the
proof of Stacks 0CXU uses its condition (4): let `x ⟶ x₁ ⟶ x₂ ⟶ ⋯` be a tower over first-order
thickenings `U ⟶ Uₙ` of an affine scheme `U` with image in an affine open of `S`, whose steps
lie over closed immersions, and whose `n`-th step has kernel killed by the functions vanishing at
the `n`-th of pairwise distinct maximal ideals of the Noetherian ring `Γ(U)`. If special towers
are effective on lift classes, the members of the tower map compatibly to one object over a
first-order thickening of `U`. -/
theorem exists_weakCocone_of_isSpecialSquareZeroTowerEffectiveOnClasses
    (hE : IsSpecialSquareZeroTowerEffectiveOnClasses B S hS p hp) (x : X) (xs : ℕ → X)
    (step : ∀ n, xs n ⟶ xs (n + 1)) (fromX : ∀ n, x ⟶ xs n)
    (hzero : ∃ hzero : xs 0 = x, fromX 0 = eqToHom hzero.symm)
    (hfromS : ∀ n, fromX (n + 1) = fromX n ≫ step n)
    (haff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x)))
    (hW : ∃ W : S.Opens, IsAffineOpen W ∧
      Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (W : Set S))
    (hthick : ∀ n, Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (fromX (n + 1)))))
    (hstep : ∀ n, IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (step (n + 1)))))
    (hnoeth : IsNoetherianRing
      Γ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤))
    (𝔪 : ℕ → Ideal Γ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x), ⊤))
    (h𝔪 : ∀ n, (𝔪 n).IsMaximal) (h𝔪ne : Pairwise fun n m => 𝔪 n ≠ 𝔪 m)
    (hann : ∀ n
      (r : Γ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj (xs (n + 1))), ⊤)),
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (fromX (n + 1)))).appTop r ∈
        𝔪 n →
      ∀ z, ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (step n))).appTop z = 0 →
        r * z = 0) :
    ∃ (ξ : X) (ι : ∀ n, xs (n + 1) ⟶ ξ), (∀ n, fromX (n + 1) ≫ ι n = fromX 1 ≫ ι 0) ∧
      Stacks.Thickenings.IsFirstOrderThickening
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (fromX 1 ≫ ι 0))) := by
  obtain ⟨hzero, hfrom0⟩ := hzero
  obtain ⟨W, hWaff, hxW⟩ := hW
  subst hzero
  have hc0 : fromX 0 = 𝟙 _ := by rw [hfrom0, eqToHom_refl]
  have hthick' : ∀ m, Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (fromX m))) := by
    rintro (_ | m)
    · rw [hc0, CategoryTheory.Functor.map_id]
      exact isFirstOrderThickening_map_id _
    · exact hthick m
  have hcl : ∀ m, IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (step m))) := by
    rintro (_ | m)
    · have h := (hthick 0).1
      rwa [hfromS 0, hc0, Category.id_comp] at h
    · exact hstep m
  obtain ⟨ξ, ι, hι, hι0⟩ := exists_cocone_of_isSpecialSquareZeroTowerEffectiveOnClasses hp hE xs
    step fromX hc0 hfromS haff W hWaff hxW hthick' hcl hnoeth 𝔪 h𝔪 h𝔪ne hann
  refine ⟨ξ, fun n => ι (n + 1), fun n => ?_, ?_⟩
  · rw [hι, hι]
  · rwa [hι]

end Tower

/-! ### Openness of versality -/

section Openness

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS)

/-- **Stacks 0CXU, the affine case, for special towers.** Let `S` be locally Noetherian and
Jacobson, let `𝒳` satisfy (RS*), have local retractions and descent along first-order
thickenings, with special towers effective on lift classes. Let `x` lie over an affine scheme `U`
locally of finite type over `S`, with image in an affine open `G` of `S`. If `x` is versal at the
finite type point `u₀`, then `x` is versal at every finite type point of an open neighbourhood of
`u₀`. The tower of Stacks 0G2S built in the proof is special: its points are closed, `U` being
Jacobson. -/
theorem exists_open_isVersalAt_of_isAffine_of_isSpecialSquareZeroTowerEffectiveOnClasses
    (hp : p.IsFiberedInGroupoids) [IsLocallyNoetherian S] [JacobsonSpace S]
    (hRS : SatisfiesRSStar B S hS p hp)
    (hL : HasLocalRetractions B S hS p) (hD : HasThickeningDescent B S hS p)
    (hE : IsSpecialSquareZeroTowerEffectiveOnClasses B S hS p hp) (x : F)
    [IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))]
    [LocallyOfFiniteType (B.inclusion.map (p.obj x).hom)]
    (G : S.Opens) (hGaff : IsAffineOpen G)
    (hxG : Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (G : Set S))
    (u₀ : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))
    (hu₀ : IsFiniteTypePoint u₀)
    (hvers : IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion)
      u₀ x rfl) :
    ∃ W : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x)).Opens, u₀ ∈ W ∧
      ∀ u ∈ W, IsFiniteTypePoint u →
        IsVersalAt ((Over.post B.inclusion).obj (p.obj x)) (p ⋙ Over.post B.inclusion) u x
          rfl := by
  classical
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let q := p ⋙ Over.post B.inclusion
  let X := V.obj (p.obj x)
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hS)) := ‹IsLocallyNoetherian S›
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map (p.obj x).hom)
  have : IsNoetherian X := {}
  have : LocallyOfFiniteType (q.obj x).hom :=
    inferInstanceAs (LocallyOfFiniteType (B.inclusion.map (p.obj x).hom))
  have : IsAffine (q.obj x).left :=
    ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))›
  have : IsAffine (B.inclusion.obj (p.obj x).left) :=
    ‹IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj x))›
  have : QuasiCompact (q.obj x).hom :=
    quasiCompact_of_range_subset_isAffineOpen (B.inclusion.map (p.obj x).hom) hGaff hxG
  have hW : ∃ W : S.Opens, IsAffineOpen W ∧
      Set.range (B.inclusion.map (p.obj x).hom).base ⊆ (W : Set S) := ⟨G, hGaff, hxG⟩
  by_contra hcon
  push Not at hcon
  let E : Set X := {u | IsFiniteTypePoint u ∧ ¬ IsVersalAt (q.obj x) q u x rfl}
  have hgen : ∀ e ∈ E, ¬ e ⤳ u₀ := fun e he hspec =>
    he.2 (isVersalAt_of_specializes_of_hasLocalRetractions B S hS p hp hRS hL hD x hW he.1 hu₀
      hspec hvers)
  have hcl : u₀ ∈ closure E := by
    rw [mem_closure_iff]
    intro O hO hu₀O
    obtain ⟨u, hu, hft, hnv⟩ := hcon ⟨O, hO⟩ hu₀O
    exact ⟨u, hu, hft, hnv⟩
  obtain ⟨v, hvE, hinc, hclv⟩ := exists_seq_of_mem_closure X hcl hgen
  -- the tower of Stacks 0G2S at the points `v n`
  obtain ⟨xs, step, fromX, hzero, hfrom0, hfromS, hprops⟩ :=
    exists_sequence_firstOrderThickenings_without_localRetraction B S hS p hp hRS (q.obj x) x
      rfl v (fun n => (hvE n).1) hinc (fun n => (hvE n).2)
  have hthick : ∀ n, Stacks.Thickenings.IsFirstOrderThickening
      (V.map (p.map (fromX (n + 1)))) := fun n => by
    have h := (hprops n).1
    simp only [eqToHom_refl, Category.id_comp] at h
    exact h
  have hstep : ∀ n, IsClosedImmersion (V.map (p.map (step (n + 1)))) := fun n => by
    have := (hthick n).1
    have : IsClosedImmersion (V.map (p.map (fromX (n + 1))) ≫ V.map (p.map (step (n + 1)))) := by
      have h := (hthick (n + 1)).1
      rwa [hfromS (n + 1), Functor.map_comp, Functor.map_comp] at h
    exact isClosedImmersion_of_isHomeomorph_comp _ _
      (isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨(V.map (p.map (fromX (n + 1)))).isClosedEmbedding.isEmbedding,
          (hthick n).isThickening.2⟩)
      (hprops (n + 1)).2.1.1
  -- the tower is special: its points are pairwise distinct closed points of the Jacobson `U`
  have : JacobsonSpace (B.inclusion.obj (B.obj hS)) := ‹JacobsonSpace S›
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (B.inclusion.map (p.obj x).hom)
  let 𝔪 : ℕ → Ideal Γ(X, ⊤) := fun n => ((isAffineOpen_top X).primeIdealOf ⟨v n, trivial⟩).asIdeal
  have h𝔪 : ∀ n, (𝔪 n).IsMaximal := fun n =>
    (isAffineOpen_top X).primeIdealOf_isMaximal_of_isClosed ⟨v n, trivial⟩
      (isClosed_singleton_iff_locallyOfFiniteType.mpr (hvE n).1.1)
  have h𝔪ne : Pairwise fun n m => 𝔪 n ≠ 𝔪 m := by
    intro n m hnm heq
    have h₁ := (isAffineOpen_top X).fromSpec_primeIdealOf ⟨v n, trivial⟩
    have h₂ := (isAffineOpen_top X).fromSpec_primeIdealOf ⟨v m, trivial⟩
    rw [PrimeSpectrum.ext heq, h₂] at h₁
    have h : v m = v n := h₁
    apply hinc n m hnm
    rw [h]
  have hann : ∀ n (r : Γ(V.obj (p.obj (xs (n + 1))), ⊤)),
      (V.map (p.map (fromX (n + 1)))).appTop r ∈ 𝔪 n →
      ∀ z, (V.map (p.map (step n))).appTop z = 0 → r * z = 0 := by
    intro n r hr z hz
    obtain ⟨e⟩ := (hprops n).2.1.2
    refine mul_eq_zero_of_kernel_iso_residueField _ _ e r (fun hmem => ?_) z hz
    simp only [eqToHom_refl, Category.id_comp] at hmem
    have hv : v n ∈ X.basicOpen ((V.map (p.map (fromX (n + 1)))).appTop r) := by
      rwa [← Scheme.preimage_basicOpen_top]
    exact ((isAffineOpen_top X).mem_basicOpen_iff_notMem_primeIdealOf _ trivial).mp hv hr
  obtain ⟨ξ, ι, hcomp, hthick₁⟩ := exists_weakCocone_of_isSpecialSquareZeroTowerEffectiveOnClasses
    hp hE x xs step fromX ⟨hzero, hfrom0⟩ hfromS inferInstance ⟨G, hGaff, hxG⟩ hthick hstep
    (IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩) 𝔪 h𝔪 h𝔪ne hann
  -- descent and the local retraction
  obtain ⟨ξ', e, -, hlft', hthick'⟩ := hD ξ (p.obj x) (p.map (fromX 1 ≫ ι 0)) inferInstance
    inferInstance hthick₁ hW
  obtain ⟨O', hO'₀, hO'⟩ := exists_open_localRetraction_comp_of_hasLocalRetractions B S hS p hp
    hL x ξ ξ' inferInstance hlft' (fromX 1 ≫ ι 0) e (by rwa [Functor.map_comp, Functor.map_comp])
    u₀ hu₀ hvers
  -- a point of the sequence inside the neighbourhood
  let OU : X.Opens := (V.map (p.map ((fromX 1 ≫ ι 0) ≫ e))) ⁻¹ᵁ O'
  obtain ⟨_, hmO, ⟨n, rfl⟩⟩ := mem_closure_iff.mp hclv OU OU.isOpen hO'₀
  obtain ⟨y, rW, z, t, s, hopen, hrange, hts, hpb⟩ := exists_open_restriction_square B S hS p hp
    (fromX (n + 1)) ((V.map (p.map (ι n ≫ e))) ⁻¹ᵁ O')
  have hmem : (V.map (p.map (fromX (n + 1)))).base (v n) ∈
      (V.map (p.map (ι n ≫ e))) ⁻¹ᵁ O' := by
    change (V.map (p.map (ι n ≫ e))).base ((V.map (p.map (fromX (n + 1)))).base (v n)) ∈ O'
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
      hcomp n]
    exact hmO
  obtain ⟨β, hβ⟩ := hO' y (rW ≫ ι n) (by
    rintro _ ⟨a, rfl⟩
    rw [Category.assoc, Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply]
    have ha : (V.map (p.map rW)).base a ∈ Set.range (V.map (p.map rW)).base := ⟨a, rfl⟩
    rwa [hrange] at ha)
  have hpt : ∃ z' : (q.obj y).left, (q.map rW).left z' =
      (eqToHom (congrArg Over.left (rfl : q.obj x = q.obj x)).symm ≫
        (q.map (fromX (n + 1))).left) (v n) := by
    have h : (V.map (p.map (fromX (n + 1)))).base (v n) ∈ Set.range (V.map (p.map rW)).base := by
      rwa [hrange]
    obtain ⟨z', hz'⟩ := h
    refine ⟨z', ?_⟩
    simp only [eqToHom_refl, Category.id_comp]
    exact hz'
  exact (hprops n).2.2 y rW hopen hpt z t s hpb ⟨β, hβ z t s (by
    rw [← hcomp n, ← Category.assoc, hts, Category.assoc]), hts⟩

/-- **Stacks 0CXU for special towers, from local retractions.** Let `S` be locally Noetherian
and Jacobson, and let `𝒳` satisfy (RS*), have local retractions and descent along first-order
thickenings, with special towers effective on lift classes. Then `𝒳` satisfies openness of
versality. -/
theorem isOpenVersality_of_isSpecialSquareZeroTowerEffectiveOnClasses
    (hp : p.IsFiberedInGroupoids) [IsLocallyNoetherian S] [JacobsonSpace S]
    (hRS : SatisfiesRSStar B S hS p hp)
    (hL : HasLocalRetractions B S hS p) (hD : HasThickeningDescent B S hS p)
    (hE : IsSpecialSquareZeroTowerEffectiveOnClasses B S hS p hp) :
    ∀ (U : Over S), LocallyOfFiniteType U.hom →
      ∀ (x : F) (hx : (p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left),
        IsFiniteTypePoint u₀ →
        IsVersalAt U (p ⋙ Over.post B.inclusion) u₀ x hx →
        ∃ W : U.left.Opens, u₀ ∈ W.1 ∧
          ∀ u ∈ W.1, IsFiniteTypePoint u →
            IsVersalAt U (p ⋙ Over.post B.inclusion) u x hx := by
  classical
  intro U hU x hx u₀ hu₀ hvers
  subst hx
  let V := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let q := p ⋙ Over.post B.inclusion
  let fS := B.inclusion.map (p.obj x).hom
  obtain ⟨G, -, hGaff, hu₀G⟩ := exists_isAffineOpen_mem S (fS.base u₀)
  obtain ⟨U₁, hU₁aff, hu₀U₁, hU₁G⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V.obj (p.obj x)) (U := fS ⁻¹ᵁ G) (x := u₀) hu₀G
  have hU₁c : B.Contains U₁ :=
    lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion U₁.ι) (p.obj x).left.2
  let T₁ := AlgebraicGeometry.BigFppfOver.siteObjectOver B S hS (p.obj x) hU₁c U₁.ι
  let j₁ : T₁ ⟶ p.obj x := AlgebraicGeometry.BigFppfOver.siteMapOver B S hS (p.obj x) hU₁c U₁.ι
  obtain ⟨x₁, ρ, hρ⟩ := hp.exists_lift j₁ x rfl
  have hx₁ : p.obj x₁ = T₁ := IsHomLift.domain_eq p j₁ ρ
  let jρ := V.map (p.map ρ)
  have hjρ : jρ = eqToHom (congrArg V.obj hx₁) ≫ V.map j₁ := by
    change V.map (p.map ρ) = _
    rw [IsHomLift.fac' p j₁ ρ]
    simp [eqToHom_map]
  have : IsOpenImmersion (V.map j₁) := inferInstanceAs (IsOpenImmersion U₁.ι)
  have : IsOpenImmersion jρ := by
    rw [hjρ]
    infer_instance
  have : IsAffine (V.obj T₁) := hU₁aff
  have : IsAffine (V.obj (p.obj x₁)) := IsAffine.of_isIso (eqToHom (congrArg V.obj hx₁))
  have hS₁ : B.inclusion.map (p.obj x₁).hom = jρ ≫ fS :=
    (toScheme_map_comp_inclusion_map_hom (p.map ρ)).symm
  have : LocallyOfFiniteType fS := hU
  have : LocallyOfFiniteType (B.inclusion.map (p.obj x₁).hom) := by
    rw [hS₁]
    infer_instance
  have hrange₁ : Set.range jρ.base = (U₁ : Set _) := by
    rw [hjρ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg V.obj hx₁)).base).2.range_eq,
      Set.image_univ]
    exact U₁.range_ι
  have hjρU : ∀ t, jρ.base t ∈ (U₁ : Set _) := fun t => hrange₁ ▸ ⟨t, rfl⟩
  have hx₁G : Set.range (B.inclusion.map (p.obj x₁).hom).base ⊆ (G : Set S) := by
    rintro _ ⟨t, rfl⟩
    rw [hS₁, Scheme.Hom.comp_apply]
    exact hU₁G (hjρU t)
  -- versality at a point of `U₁` is versality at its image in `U`
  have hiff : ∀ t : V.obj (p.obj x₁),
      IsVersalAt (q.obj x₁) q t x₁ rfl ↔ IsVersalAt (q.obj x) q (jρ.base t) x rfl := by
    intro t
    refine isVersalAt_iff_restrict B S hS p hp hGaff.fromSpec rfl rfl ρ jρ ‹_›
      (by simp only [schemeMap, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl) t ?_ ?_
    · rw [hGaff.range_fromSpec]
      rintro _ ⟨k, rfl⟩
      change fS.base (((q.obj x).left.fromSpecResidueField (jρ.base t)).base k) ∈ G
      have hk : ((q.obj x).left.fromSpecResidueField (jρ.base t)).base k = jρ.base t := by
        have := Scheme.range_fromSpecResidueField (X := (q.obj x).left) (jρ.base t)
        exact (Set.ext_iff.mp this _).mp ⟨k, rfl⟩
      rw [hk]
      exact hU₁G (hjρU t)
    · rw [hGaff.range_fromSpec]
      rintro _ ⟨k, rfl⟩
      change (B.inclusion.map (p.obj x₁).hom).base
        (((q.obj x₁).left.fromSpecResidueField t).base k) ∈ G
      exact hx₁G ⟨_, rfl⟩
  obtain ⟨u₀', hu₀'⟩ : u₀ ∈ Set.range jρ.base := hrange₁ ▸ hu₀U₁
  obtain ⟨W₁, hu₀W₁, hW₁⟩ :=
    exists_open_isVersalAt_of_isAffine_of_isSpecialSquareZeroTowerEffectiveOnClasses B S hS p hp
      hRS hL hD hE x₁ G hGaff hx₁G u₀' (isFiniteTypePoint_of_isOpenImmersion jρ u₀'
        (by rwa [hu₀'])) ((hiff u₀').mpr (by rwa [hu₀']))
  refine ⟨jρ.opensFunctor.obj W₁, ⟨u₀', hu₀W₁, hu₀'⟩, ?_⟩
  rintro _ ⟨t, htW, rfl⟩ hft
  exact (hiff t).mp (hW₁ t htW (isFiniteTypePoint_of_isOpenImmersion jρ t hft))

end Openness

/-- **(A): Stacks 0CXU with condition (4) for special towers.** Let `𝒳` be a category fibred in
groupoids over the big fppf site of a locally Noetherian Jacobson scheme `S`, with diagonal
representable by algebraic spaces, satisfying (RS*) and limit preserving, in which special towers
are effective on lift classes. Then `𝒳` satisfies openness of versality. -/
theorem specialTowerOpenVersality : SpecialTowerOpenVersality.{u} := by
  intro B S hS _ _ 𝒳 h1 h2 h3 h4
  exact isOpenVersality_of_isSpecialSquareZeroTowerEffectiveOnClasses B S hS 𝒳.val.p
    𝒳.isFiberedInGroupoids h2
    (hasLocalRetractions_of_hasRepresentableDiagonal B S hS 𝒳 h1
      (Stack.isLocallyOfFiniteType_isom_of_isLimitPreserving B S hS 𝒳 h1 h3)
      (satisfiesRS_of_satisfiesRSStar B S hS _ _ h2))
    (hasThickeningDescent_of_isLimitPreserving B S hS 𝒳 h3) h4

end AlgebraicGeometry.C1590Private

end
