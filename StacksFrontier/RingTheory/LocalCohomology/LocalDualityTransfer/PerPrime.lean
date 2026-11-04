module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapUniformPrimes
public import StacksFrontier.RingTheory.LocalCohomology.LocalDualityTransfer.AtPrime
public import
  StacksFrontier.RingTheory.LocalCohomology.LocalDualityTransfer.LocalizationCompletionDescent
import all StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator

/-!
# The per-prime local duality transfer

For a Noetherian ring `A` with a dualizing complex `ω`, a prime `𝔮` and a degree `i`, vanishing,
equality of images and injectivity on images for maps of `N ↦ H^i_{𝔮A_𝔮}(N_𝔮)` (`N` finite) are
equivalent to the dual statements for `N ↦ Ŝ ⊗_A Extʲ_A(N, ω)`, where `Ŝ` is the completion of
`A_𝔮` and `j` is a suitable degree. This is [Stacks, Tag 0AAK] at a prime, read on maps, in the
form consumed by the uniformization step of [Stacks, Tag 0EFX]
(`Stacks.Algebraization.proZero_and_eventually_injective_of_perPrimeDualityTransfer`).

It is the transfer over `Ŝ` (`Stacks.LocalCohomology.LocalDualityTransfer.transfer_Sq`)
conjugated by the natural descent of local cohomology from `Ŝ` to `A_𝔮`
(`Stacks.LocalCohomology.localizationCompletionDescentIso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology.LocalDualityTransfer

section Conjugation

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type*} [AddCommGroup X₀] [AddCommGroup X₁] [AddCommGroup X₂]
  [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup Y₂]
  (θ₀ : X₀ ≃+ Y₀) (θ₁ : X₁ ≃+ Y₁) (θ₂ : X₂ ≃+ Y₂)

/-- Vanishing is invariant under conjugation by additive equivalences. -/
theorem conj_eq_zero_iff (p : X₀ →+ X₁) (l : Y₀ →+ Y₁) (h : ∀ x, θ₁ (p x) = l (θ₀ x)) :
    p = 0 ↔ l = 0 := by
  constructor
  · intro hp; ext y; obtain ⟨x, rfl⟩ := θ₀.surjective y; rw [← h, hp]; simp
  · intro hl; ext x; apply θ₁.injective; rw [h, hl]; simp

/-- Membership in the range of a map transports along conjugation by additive equivalences. -/
private theorem mem_range_iff_of_conj {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (θ : X ≃+ Y) (θ₂ : X₂ ≃+ Y₂) (p : X →+ X₂) (l : Y →+ Y₂) (h : ∀ x, θ₂ (p x) = l (θ x))
    (z : X₂) : z ∈ Set.range p ↔ θ₂ z ∈ Set.range l := by
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨θ x, (h x).symm⟩
  · rintro ⟨y, hy⟩; obtain ⟨x, rfl⟩ := θ.surjective y
    exact ⟨x, θ₂.injective ((h x).trans hy)⟩

/-- Equality of images is invariant under conjugation by additive equivalences. -/
theorem conj_range_eq_iff (p : X₀ →+ X₂) (p' : X₁ →+ X₂) (l : Y₀ →+ Y₂) (l' : Y₁ →+ Y₂)
    (h : ∀ x, θ₂ (p x) = l (θ₀ x)) (h' : ∀ x, θ₂ (p' x) = l' (θ₁ x)) :
    Set.range p = Set.range p' ↔ Set.range l = Set.range l' := by
  have key z := mem_range_iff_of_conj θ₀ θ₂ p l h z
  have key' z := mem_range_iff_of_conj θ₁ θ₂ p' l' h' z
  constructor
  · intro e; ext w; obtain ⟨z, rfl⟩ := θ₂.surjective w
    rw [← key, e, key']
  · intro e; ext z; rw [key, e, key']

/-- Injectivity on an image is invariant under conjugation by additive equivalences. -/
theorem conj_forall_ker_iff (t : X₀ →+ X₁) (w : X₁ →+ X₂) (lt : Y₀ →+ Y₁) (lw : Y₁ →+ Y₂)
    (ht : ∀ x, θ₁ (t x) = lt (θ₀ x)) (hw : ∀ x, θ₂ (w x) = lw (θ₁ x)) :
    (∀ x, w (t x) = 0 → t x = 0) ↔ (∀ y, lw (lt y) = 0 → lt y = 0) := by
  constructor
  · intro H y hy
    obtain ⟨x, rfl⟩ := θ₀.surjective y
    rw [← ht] at hy ⊢
    rw [← hw, AddEquiv.map_eq_zero_iff] at hy
    rw [H x hy, map_zero]
  · intro H x hx
    have h1 : lw (lt (θ₀ x)) = 0 := by rw [← ht, ← hw, hx, map_zero]
    have h2 := H _ h1
    rw [← ht, AddEquiv.map_eq_zero_iff] at h2
    exact h2

end Conjugation

section Descent

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (q : PrimeSpectrum A) (e : ℤ)

/-- `H^e_𝔪(Ŝ ⊗ᴸ N)` (the object `locSq`) is the local cohomology module of `Ŝ ⊗_A N`. -/
def locSqIso (N : ModuleCat.{u} A) :
    locSq q e N ≅ (localCohomologyModuleFunctor (Sq q) e).obj
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).obj N) :=
  letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))) :=
    extendScalars_preservesFiniteLimits_of_flat' _ (flat_algebraMap_Sq q)
  (DerivedCategory.homologyFunctor (ModuleCat.{u} (Sq q)) e).mapIso
    ((Dualizing.derivedPowerTorsionProperty (Sq q) (maximalIdeal (Sq q))
        (IsNoetherian.noetherian _)).ι.mapIso
      ((Dualizing.localCohomologyFunctor (Sq q) (maximalIdeal (Sq q))
        (IsNoetherian.noetherian _)).mapIso
        (((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).mapDerivedCategorySingleFunctor
          0).app N)))

/-- The isomorphism `locSqIso` is natural in `N`. -/
theorem locSqIso_naturality {N N' : ModuleCat.{u} A} (g : N ⟶ N') :
    locSqMap q e g ≫ (locSqIso q e N').hom =
      (locSqIso q e N).hom ≫ (localCohomologyModuleFunctor (Sq q) e).map
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).map g) := by
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))) :=
    extendScalars_preservesFiniteLimits_of_flat' _ (flat_algebraMap_Sq q)
  have h := ((ModuleCat.extendScalars.{u, u, u}
    (algebraMap A (Sq q))).mapDerivedCategorySingleFunctor 0).hom.naturality g
  have h' : (flatDerived (algebraMap A (Sq q)) (flat_algebraMap_Sq q)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g) ≫
      (((ModuleCat.extendScalars.{u, u, u}
        (algebraMap A (Sq q))).mapDerivedCategorySingleFunctor 0).app N').hom =
      (((ModuleCat.extendScalars.{u, u, u}
        (algebraMap A (Sq q))).mapDerivedCategorySingleFunctor 0).app N).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Sq q)) 0).map
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).map g) := h
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (Sq q)) e
  let ι := (Dualizing.derivedPowerTorsionProperty (Sq q) (maximalIdeal (Sq q))
    (IsNoetherian.noetherian _)).ι
  let G := Dualizing.localCohomologyFunctor (Sq q) (maximalIdeal (Sq q))
    (IsNoetherian.noetherian _)
  have e1 : locSqMap q e g ≫ (locSqIso q e N').hom =
      H.map (ι.map (G.map ((flatDerived (algebraMap A (Sq q)) (flat_algebraMap_Sq q)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map g) ≫
      (((ModuleCat.extendScalars.{u, u, u}
        (algebraMap A (Sq q))).mapDerivedCategorySingleFunctor 0).app N').hom))) := by
    simp only [H, ι, G, Functor.map_comp]; rfl
  have e2 : (locSqIso q e N).hom ≫ (localCohomologyModuleFunctor (Sq q) e).map
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).map g) =
      H.map (ι.map (G.map ((((ModuleCat.extendScalars.{u, u, u}
        (algebraMap A (Sq q))).mapDerivedCategorySingleFunctor 0).app N).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Sq q)) 0).map
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).map g)))) := by
    simp only [H, ι, G, Functor.map_comp]; rfl
  rw [e1, e2, h']

/-- The descent isomorphism from `H^e_𝔪(Ŝ ⊗ -)` to `H^e_{𝔮A_𝔮}((-)_𝔮)`. -/
def descIso (N : ModuleCat.{u} A) :
    (Stacks.Algebraization.perPrimeLocalCohomology A q e).obj N ≅
      (ModuleCat.restrictScalars.{u} (algebraMap (Bq q) (Sq q))).obj (locSq q e N) :=
  (localizationCompletionDescentIso q e).app N ≪≫
    (ModuleCat.restrictScalars.{u} (algebraMap (Bq q) (Sq q))).mapIso (locSqIso q e N).symm

/-- The descent isomorphism `descIso` is natural in `N`. -/
theorem descIso_naturality {N N' : ModuleCat.{u} A} (g : N ⟶ N') :
    (Stacks.Algebraization.perPrimeLocalCohomology A q e).map g ≫ (descIso q e N').hom =
      (descIso q e N).hom ≫
        (ModuleCat.restrictScalars.{u} (algebraMap (Bq q) (Sq q))).map (locSqMap q e g) := by
  have h1 := (localizationCompletionDescentIso q e).hom.naturality g
  have h2 := locSqIso_naturality q e g
  have h2' : (locSqIso q e N).inv ≫ locSqMap q e g =
      (localCohomologyModuleFunctor (Sq q) e).map
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A (Sq q))).map g) ≫
        (locSqIso q e N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact h2
  simp only [descIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Category.assoc]
  rw [← Functor.map_comp, h2', Functor.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1

end Descent

/-- A morphism of modules vanishes exactly when its underlying additive map does. -/
theorem moduleCat_eq_zero_iff {R : Type*} [Ring R] {X Y : ModuleCat.{u} R} (f : X ⟶ Y) :
    f = 0 ↔ f.hom.toAddMonoidHom = 0 :=
  ⟨fun h ↦ by subst h; ext; simp, fun h ↦ by ext x; exact DFunLike.congr_fun h x⟩

/-- Equality of the images of two linear maps is equality of their set-theoretic ranges. -/
theorem linearMap_range_eq_iff {R : Type*} [Semiring R] {M M' N : Type*} [AddCommMonoid M]
    [AddCommMonoid M'] [AddCommMonoid N] [Module R M] [Module R M'] [Module R N]
    (f : M →ₗ[R] N) (g : M' →ₗ[R] N) :
    LinearMap.range f = LinearMap.range g ↔ Set.range f = Set.range g := by
  rw [← LinearMap.coe_range, ← LinearMap.coe_range, SetLike.coe_set_eq]

section PerPrime

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (q : PrimeSpectrum A) (e : ℤ)

/-- A choice of natural isomorphisms from `H^e_{𝔮A_𝔮}((-)_𝔮)` to `H^e_𝔪(Ŝ ⊗ -)`, together
with their naturality. The package is extracted by choice so that later proofs only see its two
properties, never its (large) construction. -/
def descNat : {θ : ∀ N : ModuleCat.{u} A,
    (Stacks.Algebraization.perPrimeLocalCohomology A q e).obj N ≅
      (ModuleCat.restrictScalars.{u} (algebraMap (Bq q) (Sq q))).obj (locSq q e N) //
    ∀ {N N' : ModuleCat.{u} A} (g : N ⟶ N'),
      (Stacks.Algebraization.perPrimeLocalCohomology A q e).map g ≫ (θ N').hom =
        (θ N).hom ≫ (ModuleCat.restrictScalars.{u} (algebraMap (Bq q) (Sq q))).map
          (locSqMap q e g)} :=
  Classical.choice ⟨⟨fun N ↦ descIso q e N, fun g ↦ descIso_naturality q e g⟩⟩

/-- The descent isomorphism as an additive equivalence. -/
def descAddEquiv (N : ModuleCat.{u} A) :
    (Stacks.Algebraization.perPrimeLocalCohomology A q e).obj N ≃+
      (ModuleCat.restrictScalars.{u} (algebraMap (Bq q) (Sq q))).obj (locSq q e N) :=
  ((descNat q e).1 N).toLinearEquiv.toAddEquiv

/-- `locSqMap`, restricted to `A_𝔮`. -/
abbrev resMap {N N' : ModuleCat.{u} A} (g : N ⟶ N') :=
  ((ModuleCat.restrictScalars.{u} (algebraMap (Bq q) (Sq q))).map (locSqMap q e g)).hom

/-- The additive equivalence `descAddEquiv` intertwines the map induced by `g` on
`H^e_{𝔮A_𝔮}((-)_𝔮)` with `resMap q e g`. -/
theorem descAddEquiv_naturality {N N' : ModuleCat.{u} A} (g : N ⟶ N') (x) :
    descAddEquiv q e N' (((Stacks.Algebraization.perPrimeLocalCohomology A q e).map g).hom x) =
      resMap q e g (descAddEquiv q e N x) :=
  ConcreteCategory.congr_hom ((descNat q e).2 g) x

/-- `resMap q e g` acts on elements as `locSqMap q e g`. -/
theorem resMap_apply {N N' : ModuleCat.{u} A} (g : N ⟶ N') (x) :
    resMap q e g x = (locSqMap q e g).hom x :=
  ModuleCat.restrictScalars.map_apply _ _ _

/-- `resMap q e g` vanishes if and only if `locSqMap q e g` does. -/
theorem resMap_eq_zero_iff {N N' : ModuleCat.{u} A} (g : N ⟶ N') :
    (resMap q e g).toAddMonoidHom = 0 ↔ (locSqMap q e g).hom.toAddMonoidHom = 0 := by
  constructor
  · intro h
    refine AddMonoidHom.ext fun (x : locSq q e N) ↦ ?_
    let y : (ModuleCat.restrictScalars.{u} (algebraMap (Bq q) (Sq q))).obj (locSq q e N) := x
    have h' : resMap q e g y = 0 := DFunLike.congr_fun h y
    exact (resMap_apply q e g y).symm.trans h'
  · intro h
    refine AddMonoidHom.ext fun
      (x : (ModuleCat.restrictScalars.{u} (algebraMap (Bq q) (Sq q))).obj (locSq q e N)) ↦ ?_
    have h' : (locSqMap q e g).hom x = 0 := DFunLike.congr_fun h x
    exact (resMap_apply q e g x).trans h'

/-- The map induced by `g` on `H^e_{𝔮A_𝔮}((-)_𝔮)` vanishes if and only if `locSqMap q e g`
vanishes. -/
theorem perPrime_eq_zero_iff {N₀ N₁ : ModuleCat.{u} A} (g : N₀ ⟶ N₁) :
    (Stacks.Algebraization.perPrimeLocalCohomology A q e).map g = 0 ↔ locSqMap q e g = 0 := by
  rw [moduleCat_eq_zero_iff, moduleCat_eq_zero_iff, ← resMap_eq_zero_iff]
  exact conj_eq_zero_iff (descAddEquiv q e N₀) (descAddEquiv q e N₁) _
    (resMap q e g).toAddMonoidHom (descAddEquiv_naturality q e g)

/-- The maps induced by `a ≫ b` and `b` on `H^e_{𝔮A_𝔮}((-)_𝔮)` have the same image if and only
if `locSqMap q e (a ≫ b)` and `locSqMap q e b` have the same image. -/
theorem perPrime_range_eq_iff {N₀ N₁ N₂ : ModuleCat.{u} A} (a : N₀ ⟶ N₁) (b : N₁ ⟶ N₂) :
    LinearMap.range ((Stacks.Algebraization.perPrimeLocalCohomology A q e).map (a ≫ b)).hom =
        LinearMap.range ((Stacks.Algebraization.perPrimeLocalCohomology A q e).map b).hom ↔
      LinearMap.range (locSqMap q e (a ≫ b)).hom = LinearMap.range (locSqMap q e b).hom := by
  rw [linearMap_range_eq_iff, linearMap_range_eq_iff]
  have h := conj_range_eq_iff (descAddEquiv q e N₀) (descAddEquiv q e N₁) (descAddEquiv q e N₂)
    ((Stacks.Algebraization.perPrimeLocalCohomology A q e).map (a ≫ b)).hom.toAddMonoidHom
    ((Stacks.Algebraization.perPrimeLocalCohomology A q e).map b).hom.toAddMonoidHom
    (resMap q e (a ≫ b)).toAddMonoidHom (resMap q e b).toAddMonoidHom
    (descAddEquiv_naturality q e (a ≫ b)) (descAddEquiv_naturality q e b)
  have e1 : ∀ {N N' : ModuleCat.{u} A} (g : N ⟶ N'),
      Set.range ⇑(resMap q e g).toAddMonoidHom = Set.range ⇑(locSqMap q e g).hom := fun g ↦ by
    ext y; simp only [LinearMap.toAddMonoidHom_coe, resMap_apply, Set.mem_range]; exact Iff.rfl
  rwa [e1, e1] at h

/-- The map induced by `w` on `H^e_{𝔮A_𝔮}((-)_𝔮)` is injective on the image of the map induced
by `t` if and only if `locSqMap q e w` is injective on the image of `locSqMap q e t`. -/
theorem perPrime_forall_ker_iff {N₀ N₁ N₂ : ModuleCat.{u} A} (t : N₀ ⟶ N₁) (w : N₁ ⟶ N₂) :
    (∀ x, ((Stacks.Algebraization.perPrimeLocalCohomology A q e).map t).hom x ∈
        LinearMap.ker ((Stacks.Algebraization.perPrimeLocalCohomology A q e).map w).hom →
      ((Stacks.Algebraization.perPrimeLocalCohomology A q e).map t).hom x = 0) ↔
    (∀ x, (locSqMap q e t).hom x ∈ LinearMap.ker (locSqMap q e w).hom →
      (locSqMap q e t).hom x = 0) := by
  simp only [LinearMap.mem_ker]
  have h := conj_forall_ker_iff (descAddEquiv q e N₀) (descAddEquiv q e N₁) (descAddEquiv q e N₂)
    ((Stacks.Algebraization.perPrimeLocalCohomology A q e).map t).hom.toAddMonoidHom
    ((Stacks.Algebraization.perPrimeLocalCohomology A q e).map w).hom.toAddMonoidHom
    (resMap q e t).toAddMonoidHom (resMap q e w).toAddMonoidHom
    (descAddEquiv_naturality q e t) (descAddEquiv_naturality q e w)
  simp only [LinearMap.toAddMonoidHom_coe, resMap_apply] at h
  exact h

end PerPrime

/-- **The per-prime local duality transfer** ([Stacks, Tag 0AAK] at a prime, read on maps):
the hypothesis `PerPrimeDualityTransfer` of the uniformization step of [Stacks, Tag 0EFX] holds
for every Noetherian ring with a dualizing complex. -/
theorem perPrimeDualityTransfer {A : Type u} [CommRing A] [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω) :
    Stacks.Algebraization.PerPrimeDualityTransfer A ω := by
  intro q i
  have hω' : ∃ b : ℤ, ω.IsGE b := Stacks.LocalCohomology.boundedBelow_of_isDualizingComplex A ω hω
  obtain ⟨n, rfl⟩ : ∃ n, hullDeg q ω hω - n = i := ⟨hullDeg q ω hω - i, by omega⟩
  obtain ⟨hZ, hI, hK⟩ := transfer_Sq q ω hω hω' n
  refine ⟨n, Sq q, inferInstance, inferInstance, inferInstance, fun N₀ N₁ _ _ g ↦ ?_,
    fun N₀ N₁ N₂ _ _ _ a b ↦ ?_, fun N₀ N₁ N₂ _ _ _ t w ↦ ?_⟩
  · exact (perPrime_eq_zero_iff q _ g).trans (hZ N₀ N₁ g)
  · exact (perPrime_range_eq_iff q _ a b).trans (hI N₀ N₁ N₂ a b)
  · exact (perPrime_forall_ker_iff q _ t w).trans (hK N₀ N₁ N₂ t w)

end Stacks.LocalCohomology.LocalDualityTransfer
