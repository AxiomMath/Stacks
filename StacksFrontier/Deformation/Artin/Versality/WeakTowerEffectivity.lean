module

public import StacksFrontier.Deformation.Artin.FormalObject.SquareZeroTowerObstruction
public import StacksFrontier.Deformation.Artin.Versality.OpennessCriterion

/-!
# Towers of first-order thickenings from lift classes over a square-zero tower

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S`, and let
`x = x₀ ⟶ x₁ ⟶ x₂ ⟶ ⋯` be a tower in `𝒳` over first-order thickenings `U ⟶ Uₙ` of an affine
scheme `U` lying over an affine open of `S`, whose steps lie over closed immersions. The rings
`Rₙ = Γ(Uₙ)` form a tower of square-zero thickenings of `R₀ = Γ(U)`, and the arrows `x ⟶ xₙ`
are compatible lift classes of `x` over the `Rₙ`. If every such compatible system of lift
classes comes from one lift class over `lim Rₙ`, the tower maps to one object `ξ` over
`Spec (lim Rₙ)`, compatibly with the arrows out of `x`, and `U ⟶ Spec (lim Rₙ)` is a first-order
thickening.

## Main results

* `Deformation.Artin.SquareZeroTower.limitBase_surjective`,
  `Deformation.Artin.SquareZeroTower.ker_limitBase_sq`: `lim Rₙ → R₀` is surjective with
  square-zero kernel.
* `Deformation.Artin.exists_cocone_of_isSquareZeroTowerEffectiveOnClasses`.
* `Deformation.Artin.hasWeaklyEffectiveThickeningTowers_of_isSquareZeroTowerEffectiveOnClasses`:
  effectivity on lift classes gives the weak effectivity of towers used in the proof of
  Stacks 0CXU.

## References

* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin

namespace SquareZeroTower

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] (f : ∀ n, R (n + 1) →+* R n)

/-- With surjective transition maps, `lim Rₙ → R₀` is surjective. -/
theorem limitBase_surjective (hf : ∀ n, Function.Surjective (f n)) :
    Function.Surjective (limitBase f) := by
  intro a
  let r : ∀ n, R n := fun n => Nat.rec (motive := fun n => R n) a
    (fun k rk => (hf k rk).choose) n
  exact ⟨⟨r, fun n => (hf n (r n)).choose_spec⟩, rfl⟩

/-- When every `Rₙ → R₀` has square-zero kernel, so does `lim Rₙ → R₀`. -/
theorem ker_limitBase_sq (hsq : ∀ n, RingHom.ker (toBase f n) ^ 2 = ⊥) :
    RingHom.ker (limitBase f) ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  have hmem : ∀ c : limit f, c ∈ RingHom.ker (limitBase f) →
      ∀ n, (c : ∀ n, R n) n ∈ RingHom.ker (toBase f n) := by
    intro c hc n
    rw [RingHom.mem_ker] at hc ⊢
    rwa [limit_le_sameBase f c.2 n]
  refine Subtype.ext (funext fun n => ?_)
  exact mul_eq_zero_of_sq (hsq n) (hmem a ha n) (hmem b hb n)

end SquareZeroTower

section Tower

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS}

/-- An object of the slice under `X` with a structure morphism followed by an `eqToHom`. -/
lemma under_mk_eq_of_comp_eqToHom {C : Type*} [Category C] {A Y Y' : C} (f : A ⟶ Y)
    (g : A ⟶ Y') (h : Y = Y') (hfg : f ≫ eqToHom h = g) : Under.mk f = Under.mk g := by
  subst h
  simp only [eqToHom_refl, Category.comp_id] at hfg
  rw [hfg]

/-- The structure morphism of an object of the slice under `X` equal to `Under.mk g`. -/
lemma under_hom_eq_of_eq_mk {C : Type*} [Category C] {A Y : C} {Q : Under A} (g : A ⟶ Y)
    (h : Q = Under.mk g) : Q.hom = g ≫ eqToHom (congrArg Comma.right h).symm := by
  subst h
  simp

/-- An arrow of the site over a first-order thickening, framed by two `eqToHom`s, still lies over
a first-order thickening. -/
lemma isFirstOrderThickening_map_eqToHom_comp {a a' b b' : AlgebraicGeometry.BigFppfOver B S hS}
    (h₁ : a = a') (g : a' ⟶ b) (h₂ : b = b')
    (hg : Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map g)) :
    Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map ((eqToHom h₁ ≫ g) ≫ eqToHom h₂)) := by
  subst h₁ h₂
  simpa using hg

variable (hp : p.IsFiberedInGroupoids)

/-- **A cocone over a tower of first-order thickenings from lift classes.** Let
`obj 0 ⟶ obj 1 ⟶ ⋯` be a tower in `𝒳` over closed immersions, with composites `c m` lying over
first-order thickenings of an affine scheme with image in an affine open of `S`. If compatible
systems of lift classes over square-zero towers come from lift classes over the limit, the tower
has arrows `ι m : obj m ⟶ ξ` with `c m ≫ ι m = ι 0`, and `ι 0` lies over a first-order
thickening. -/
theorem exists_cocone_of_isSquareZeroTowerEffectiveOnClasses
    (hE : IsSquareZeroTowerEffectiveOnClasses B S hS p hp)
    (obj : ℕ → X) (a : ∀ m, obj m ⟶ obj (m + 1)) (c : ∀ m, obj 0 ⟶ obj m)
    (hc0 : c 0 = 𝟙 _) (hc : ∀ m, c (m + 1) = c m ≫ a m)
    (haff : IsAffine ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (p.obj (obj 0))))
    (W : S.Opens) (hWaff : IsAffineOpen W)
    (hW : Set.range (B.inclusion.map (p.obj (obj 0)).hom).base ⊆ (W : Set S))
    (hthick : ∀ m, Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (c m))))
    (hcl : ∀ m, IsClosedImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (p.map (a m)))) :
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
  have hw : ∀ {P P' : AlgebraicGeometry.BigFppfOver B S hS} (g : P ⟶ P'),
      VS.map g ≫ B.inclusion.map P'.hom = B.inclusion.map P.hom := fun g => by
    have h := congrArg B.inclusion.map (Over.w g)
    rwa [B.inclusion.map_comp] at h
  have hYW : ∀ m, Set.range (B.inclusion.map (Y m).hom).base ⊆ Set.range W.ι.base := by
    intro m
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    obtain ⟨t₀, rfl⟩ := (hthick m).isThickening.2 t
    rw [← Scheme.Hom.comp_apply, hw (p.map (c m))]
    exact hW ⟨t₀, rfl⟩
  let τ : ∀ m, VS.obj (Y m) ⟶ W := fun m =>
    IsOpenImmersion.lift W.ι (B.inclusion.map (Y m).hom) (hYW m)
  have hτ : ∀ m, τ m ≫ W.ι = B.inclusion.map (Y m).hom := fun m => IsOpenImmersion.lift_fac _ _ _
  have hτa : ∀ m, VS.map (p.map (a m)) ≫ τ (m + 1) = τ m := fun m => by
    rw [← cancel_mono W.ι, Category.assoc, hτ, hτ, hw]
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
  obtain ⟨ξc, hξc⟩ := hE R fm hf hsq toS (hR 0) Λ β hβ rfl hR hU x' hx' b hb
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

/-- An identity lies over a first-order thickening. -/
lemma isFirstOrderThickening_map_id (Z : AlgebraicGeometry.BigFppfOver B S hS) :
    Stacks.Thickenings.IsFirstOrderThickening
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝟙 Z)) := by
  rw [CategoryTheory.Functor.map_id]
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.Hom.ker_eq_bot_of_isIso]
  exact zero_pow two_ne_zero

/-- **Weak effectivity of towers from effectivity on lift classes.** If compatible systems of
lift classes over square-zero towers come from lift classes over the limit, towers of first-order
thickenings over affine opens of `S` are weakly effective. -/
theorem hasWeaklyEffectiveThickeningTowers_of_isSquareZeroTowerEffectiveOnClasses
    (hE : IsSquareZeroTowerEffectiveOnClasses B S hS p hp) :
    HasWeaklyEffectiveThickeningTowers B S hS p IsAffineOpen := by
  intro x xs step fromX ⟨hzero, hfrom0⟩ hfromS haff _ ⟨W, hWaff, hxW⟩ hthick hstep
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
  obtain ⟨ξ, ι, hι, hι0⟩ := exists_cocone_of_isSquareZeroTowerEffectiveOnClasses hp hE xs step
    fromX hc0 hfromS haff W hWaff hxW hthick' hcl
  refine ⟨ξ, fun n => ι (n + 1), fun n => ?_, ?_⟩
  · rw [hι, hι]
  · rwa [hι]

end Tower

end Deformation.Artin

end
