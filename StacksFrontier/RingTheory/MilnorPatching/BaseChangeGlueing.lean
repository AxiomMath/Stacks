module

public import StacksFrontier.RingTheory.MilnorPatching.ModuleProperties
public import StacksFrontier.RingTheory.MilnorPatching.Adjunction
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.RingHom.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Gluing modules along a ring fibre square

For a ring map `φ : R →+* S`, a `φ`-semilinear map `f : M → N` exhibits `N` as the base change
of `M` along `φ` when the induced `S`-linear map `S ⊗_R M ⟶ N` is bijective. Let
`B' = B ×_A A'` be a ring fibre product with `A' ⟶ A` surjective, and let `M = N ×_K N'` be the
fibre product of a `B`-module `N` and an `A'`-module `N'` whose base changes to `A` are both `K`.
Then `N` and `N'` are the base changes of `M`, and `M` is flat over `B'` when `N` and `N'` are
flat. A flat `B'`-module embeds into its two base changes, and a `B'`-module whose base changes
generate `N` and `N'` maps onto `M`. The same statements hold for a relative Milnor square, the
base change of the fibre square along a ring map `B' ⟶ D'`.

## Main definitions

* `MilnorPatching.liftAlong`: the `S`-linear map `S ⊗_R M ⟶ N`, `s ⊗ m ↦ s • f m`, of a
  `φ`-semilinear map `f`.
* `MilnorPatching.IsBaseChangeAlong`: `f` exhibits `N` as the base change of `M` along `φ`.
* `MilnorPatching.IsFibreSquare`: `B'` is the ring fibre product `B ×_A A'`, with `A' ⟶ A`
  surjective.
* `MilnorPatching.IsGlued`: `M` is the fibre product `N ×_K N'`.
* `MilnorPatching.glueDatum`: the object of the categorical pullback of module categories defined
  by two base changes into the same `A`-module.
* `MilnorPatching.IsRelativeSquare`: the relative Milnor square.

## Main results

* `MilnorPatching.isBaseChangeAlong_iff_of_isPushout`: a base change along one side of a
  cocartesian square of rings is a base change along the opposite side.
* `MilnorPatching.isBaseChangeAlong_of_isGlued`: `N` and `N'` are the base changes of
  `M = N ×_K N'`.
* `MilnorPatching.flat_of_isGlued`: the fibre product of two flat base changes is flat.
* `MilnorPatching.eq_zero_of_flat`: a flat `B'`-module embeds into its two base changes.
* `MilnorPatching.exists_eq_of_surjective`: a module whose base changes generate `N` and `N'`
  maps onto `N ×_K N'`.
* `MilnorPatching.IsRelativeSquare.isBaseChangeAlong_of_isGlued`,
  `MilnorPatching.IsRelativeSquare.flat_of_isGlued`,
  `MilnorPatching.IsRelativeSquare.eq_zero_of_flat` and
  `MilnorPatching.IsRelativeSquare.exists_eq_of_surjective`: the same statements for a relative
  Milnor square.

## References

* [Stacks Project, Tag 07RU](https://stacks.math.columbia.edu/tag/07RU)
* [Stacks Project, Tag 0D2I](https://stacks.math.columbia.edu/tag/0D2I)
* [Stacks Project, Tag 08IG](https://stacks.math.columbia.edu/tag/08IG)
* [Stacks Project, Tag 08KJ](https://stacks.math.columbia.edu/tag/08KJ)
* [Stacks Project, Tag 08KK](https://stacks.math.columbia.edu/tag/08KK)
* [Stacks Project, Tag 08KM](https://stacks.math.columbia.edu/tag/08KM)
* [Stacks Project, Tag 07RW](https://stacks.math.columbia.edu/tag/07RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u

namespace MilnorPatching

section BaseChangeAlong

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- A `φ`-semilinear map read as an `R`-linear map, `N` carrying the `R`-module structure
obtained by restricting scalars along `φ`. -/
@[ega "II 1.7.2" "partial"]
def semilinearToLinear (f : M →ₛₗ[φ] N) :
    letI : Module R N := Module.compHom N φ
    M →ₗ[R] N :=
  letI : Module R N := Module.compHom N φ
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun r m => f.map_smulₛₗ r m }

/-- The `S`-linear map `S ⊗_R M ⟶ N`, `s ⊗ m ↦ s • f m`, of a `φ`-semilinear map. -/
def liftAlong (f : M →ₛₗ[φ] N) :
    letI := φ.toAlgebra
    S ⊗[R] M →ₗ[S] N :=
  letI := φ.toAlgebra
  letI : Module R N := Module.compHom N φ
  haveI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  (semilinearToLinear φ f).liftBaseChange S

/-- `liftAlong φ f` sends `s ⊗ m` to `s • f m`. -/
theorem liftAlong_tmul (f : M →ₛₗ[φ] N) (s : S) (m : M) :
    letI := φ.toAlgebra
    liftAlong φ f (s ⊗ₜ m) = s • f m := rfl

/-- `liftAlong φ f` sends `1 ⊗ m` to `f m`. -/
theorem liftAlong_one_tmul (f : M →ₛₗ[φ] N) (m : M) :
    letI := φ.toAlgebra
    liftAlong φ f (1 ⊗ₜ m) = f m := by
  let := φ.toAlgebra
  exact (liftAlong_tmul φ f 1 m).trans (one_smul S (f m))

/-- **`f` exhibits `N` as the base change of `M` along `φ`**: the `S`-linear map
`S ⊗_R M ⟶ N`, `s ⊗ m ↦ s • f m`, is bijective. -/
abbrev IsBaseChangeAlong (f : M →ₛₗ[φ] N) : Prop :=
  Function.Bijective (liftAlong φ f)

variable {φ}

/-- A base change along `φ` is Mathlib's `IsBaseChange` for the algebra structure of `φ`. -/
theorem isBaseChangeAlong_iff_isBaseChange (f : M →ₛₗ[φ] N) :
    IsBaseChangeAlong φ f ↔
      letI := φ.toAlgebra
      letI : Module R N := Module.compHom N φ
      haveI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      IsBaseChange S (semilinearToLinear φ f) := by
  let := φ.toAlgebra
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine ⟨fun h => IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h)
    fun m => liftAlong_one_tmul φ f m, fun h => ?_⟩
  have e : liftAlong φ f = h.equiv.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun s m => ?_
    rw [liftAlong_tmul, LinearEquiv.coe_coe, IsBaseChange.equiv_tmul]
    rfl
  change Function.Bijective (liftAlong φ f)
  rw [e]
  exact h.equiv.bijective

/-- Post-composing `liftAlong φ f` with an `S`-linear `g` gives `liftAlong φ f'` when
`g ∘ f = f'`. -/
private theorem comp_liftAlong_eq {f : M →ₛₗ[φ] N} {N' : Type u} [AddCommGroup N'] [Module S N']
    {f' : M →ₛₗ[φ] N'} (g : N →ₗ[S] N') (hg : ∀ m, g (f m) = f' m) :
    letI := φ.toAlgebra
    ⇑g ∘ liftAlong φ f = liftAlong φ f' := by
  let := φ.toAlgebra
  refine funext fun t => ?_
  induction t using TensorProduct.inductionOn with
  | tmul s m =>
    change g (s • f m) = s • f' m
    rw [map_smul, hg]
  | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]

/-- A base change followed by a bijective linear map is a base change. -/
theorem IsBaseChangeAlong.comp_bijective {f : M →ₛₗ[φ] N} (hf : IsBaseChangeAlong φ f)
    {N' : Type u} [AddCommGroup N'] [Module S N'] (g : N →ₗ[S] N')
    (hg : Function.Bijective g) : IsBaseChangeAlong φ (g.comp f) := by
  let := φ.toAlgebra
  change Function.Bijective (liftAlong φ (g.comp f))
  rw [← comp_liftAlong_eq g fun _ => rfl]
  exact hg.comp hf

/-- A linear map between two base changes of the same module, compatible with the two
structure maps, is bijective. -/
theorem IsBaseChangeAlong.bijective_of_comp {f : M →ₛₗ[φ] N} (hf : IsBaseChangeAlong φ f)
    {N' : Type u} [AddCommGroup N'] [Module S N'] {f' : M →ₛₗ[φ] N'}
    (hf' : IsBaseChangeAlong φ f') (g : N →ₗ[S] N') (hg : ∀ m, g (f m) = f' m) :
    Function.Bijective g :=
  (Function.Bijective.of_comp_iff (⇑g) hf).1 (comp_liftAlong_eq g hg ▸ hf')

end BaseChangeAlong

section Pushout

variable {R' S' R S : Type u} [CommRing R'] [CommRing S'] [CommRing R] [CommRing S]
  (σ : R' →+* S') (ρ : R' →+* R) (β : S' →+* S) (δ : R →+* S)
  {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- The `σ`-semilinear map underlying a `δ`-semilinear map, when `M` and `N` are restricted to
`R'` and `S'` along the two other sides of a commutative square `δ ∘ ρ = β ∘ σ`. -/
def restrictSquare (hw : δ.comp ρ = β.comp σ) (f : M →ₛₗ[δ] N) :
    letI : Module R' M := Module.compHom M ρ
    letI : Module S' N := Module.compHom N β
    M →ₛₗ[σ] N :=
  letI : Module R' M := Module.compHom M ρ
  letI : Module S' N := Module.compHom N β
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun r m => by
      change f (ρ r • m) = β (σ r) • f m
      rw [f.map_smulₛₗ]
      exact congrArg (· • f m) (DFunLike.congr_fun hw r) }

/-- `restrictSquare σ ρ β δ hw f` has the same underlying function as `f`. -/
theorem restrictSquare_apply (hw : δ.comp ρ = β.comp σ) (f : M →ₛₗ[δ] N) (m : M) :
    (letI : Module R' M := Module.compHom M ρ
     letI : Module S' N := Module.compHom N β
     restrictSquare σ ρ β δ hw f) m = f m := rfl

/-- **Extending scalars along one side of a cocartesian square is extending them along the
opposite side.**  For a cocartesian square `δ ∘ ρ = β ∘ σ` with base `R'` and a `δ`-semilinear map
`f : M → N`, the map `S ⊗_R M ⟶ N` of `f` is the map `S' ⊗_{R'} M ⟶ N` of its restriction, read
through the identification `Algebra.IsPushout.cancelBaseChange` of the two tensor products. -/
theorem exists_equiv_liftAlong_of_isPushout
    (h : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom ρ) (CommRingCat.ofHom β)
      (CommRingCat.ofHom δ)) (f : M →ₛₗ[δ] N) :
    letI := δ.toAlgebra
    letI := σ.toAlgebra
    letI : Module R' M := Module.compHom M ρ
    letI : Module S' N := Module.compHom N β
    ∃ c : S ⊗[R] M ≃ S' ⊗[R'] M, ∀ x, liftAlong δ f x =
      liftAlong σ (restrictSquare σ ρ β δ (congrArg CommRingCat.Hom.hom h.w.symm) f) (c x) := by
  have hw : δ.comp ρ = β.comp σ := congrArg CommRingCat.Hom.hom h.w.symm
  let : Algebra R' S' := σ.toAlgebra
  let : Algebra R' R := ρ.toAlgebra
  let : Algebra S' S := β.toAlgebra
  let : Algebra R S := δ.toAlgebra
  let : Algebra R' S := (δ.comp ρ).toAlgebra
  let : Module R' M := Module.compHom M ρ
  let : Module S' N := Module.compHom N β
  have : IsScalarTower R' R S := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R' S' S := IsScalarTower.of_algebraMap_eq' hw
  have : IsScalarTower R' R M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower S' S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Algebra.IsPushout R' S' R S := CommRingCat.isPushout_iff_isPushout.mp h
  let c : S ⊗[R] M ≃ₗ[S'] S' ⊗[R'] M := Algebra.IsPushout.cancelBaseChange R' S' R S M
  let L1 : S ⊗[R] M →ₗ[S] N := liftAlong δ f
  let L2 : S' ⊗[R'] M →ₗ[S'] N := liftAlong σ (restrictSquare σ ρ β δ hw f)
  have hL1 : ∀ (s' : S') (x : S ⊗[R] M), L1 (s' • x) = s' • L1 x := fun s' x => by
    rw [← algebraMap_smul S s' x, L1.map_smul]
    rfl
  have key : ∀ y : S' ⊗[R'] M, L1 (c.symm y) = L2 y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul s' m =>
      rw [show s' ⊗ₜ[R'] m = s' • ((1 : S') ⊗ₜ[R'] m) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        c.symm.map_smul, hL1, L2.map_smul,
        Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one]
      exact congrArg (s' • ·) ((liftAlong_one_tmul δ f m).trans
        (liftAlong_one_tmul σ (restrictSquare σ ρ β δ hw f) m).symm)
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  exact ⟨c.toEquiv, fun x => by
    change L1 x = L2 (c x)
    rw [← key, LinearEquiv.symm_apply_apply]⟩

/-- **A base change along one side of a cocartesian square of rings is a base change along the
opposite side.**  For a cocartesian square `δ ∘ ρ = β ∘ σ` with base `R'`, a `δ`-semilinear map
`f : M → N` from an `R`-module to an `S`-module exhibits `N` as `S ⊗_R M` exactly when, with `M`
and `N` restricted to `R'` and `S'`, it exhibits `N` as `S' ⊗_{R'} M`. -/
theorem isBaseChangeAlong_iff_of_isPushout
    (h : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom ρ) (CommRingCat.ofHom β)
      (CommRingCat.ofHom δ)) (f : M →ₛₗ[δ] N) :
    IsBaseChangeAlong δ f ↔
      letI : Module R' M := Module.compHom M ρ
      letI : Module S' N := Module.compHom N β
      IsBaseChangeAlong σ (restrictSquare σ ρ β δ
        (congrArg CommRingCat.Hom.hom h.w.symm) f) := by
  obtain ⟨c, hc⟩ := exists_equiv_liftAlong_of_isPushout σ ρ β δ h f
  change Function.Bijective _ ↔ Function.Bijective _
  rw [show ⇑(liftAlong δ f) = _ ∘ ⇑c from funext hc]
  exact Function.Bijective.of_comp_iff _ c.bijective

/-- The surjectivity half of `MilnorPatching.isBaseChangeAlong_iff_of_isPushout`. -/
theorem surjective_liftAlong_iff_of_isPushout
    (h : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom ρ) (CommRingCat.ofHom β)
      (CommRingCat.ofHom δ)) (f : M →ₛₗ[δ] N) :
    Function.Surjective (liftAlong δ f) ↔
      letI : Module R' M := Module.compHom M ρ
      letI : Module S' N := Module.compHom N β
      Function.Surjective (liftAlong σ (restrictSquare σ ρ β δ
        (congrArg CommRingCat.Hom.hom h.w.symm) f)) := by
  obtain ⟨c, hc⟩ := exists_equiv_liftAlong_of_isPushout σ ρ β δ h f
  rw [show ⇑(liftAlong δ f) = _ ∘ ⇑c from funext hc]
  exact Function.Surjective.of_comp_iff _ c.surjective

end Pushout


section Glue

variable {B' B A' A : Type u} [CommRing B'] [CommRing B] [CommRing A'] [CommRing A]
  (σ : B' →+* B) (σ' : B' →+* A') (τ : B →+* A) (π : A' →+* A)

/-- **`B'` is the ring fibre product `B ×_A A'`, with `A' ⟶ A` surjective**, presented by the four
maps of the square. -/
structure IsFibreSquare : Prop where
  comm : τ.comp σ = π.comp σ'
  injective : ∀ x y : B', σ x = σ y → σ' x = σ' y → x = y
  exists_lift : ∀ (b : B) (a : A'), τ b = π a → ∃ x : B', σ x = b ∧ σ' x = a
  surjective : Function.Surjective π

variable {σ σ' τ π}
variable {N N' K M : Type u} [AddCommGroup N] [Module B N] [AddCommGroup N'] [Module A' N']
  [AddCommGroup K] [Module A K] [AddCommGroup M] [Module B' M]

/-- **`M` is the fibre product `N ×_K N'`** through `p` and `p'`. -/
structure IsGlued (α : N →ₛₗ[τ] K) (β : N' →ₛₗ[π] K) (p : M →ₛₗ[σ] N) (p' : M →ₛₗ[σ'] N') :
    Prop where
  comm : ∀ m, α (p m) = β (p' m)
  injective : ∀ m₁ m₂, p m₁ = p m₂ → p' m₁ = p' m₂ → m₁ = m₂
  exists_mk : ∀ (n : N) (n' : N'), α n = β n' → ∃ m, p m = n ∧ p' m = n'

/-- The object of the categorical pullback of module categories which two base changes into the
same `A`-module define: the two modules, identified after extension of scalars to `A` through
their common base change. -/
def glueDatum {α : N →ₛₗ[τ] K} {β : N' →ₛₗ[π] K} (hα : IsBaseChangeAlong τ α)
    (hβ : IsBaseChangeAlong π β) :
    CategoricalPullback (ModuleCat.extendScalars.{u, u, u} τ)
      (ModuleCat.extendScalars.{u, u, u} π) where
  fst := ModuleCat.of B N
  snd := ModuleCat.of A' N'
  iso := ((LinearEquiv.ofBijective _ hα).trans (LinearEquiv.ofBijective _ hβ).symm).toModuleIso

/-- The identification of `glueDatum hα hβ` sends `1 ⊗ n` to the preimage of `α n` under the
bijection `A ⊗_{A'} N' ⟶ K` of `β`. -/
theorem glueDatum_iso_hom_one_tmul {α : N →ₛₗ[τ] K} {β : N' →ₛₗ[π] K}
    (hα : IsBaseChangeAlong τ α) (hβ : IsBaseChangeAlong π β) (n : N) :
    (glueDatum hα hβ).iso.hom ((1 : A) ⊗ₜ[B,τ] n) = (LinearEquiv.ofBijective _ hβ).symm (α n) :=
  congrArg (LinearEquiv.ofBijective _ hβ).symm (liftAlong_one_tmul τ α n)

/-- A pair is compatible in `glueDatum` exactly when its two images in `K` agree. -/
theorem glueDatum_compatible_iff {α : N →ₛₗ[τ] K} {β : N' →ₛₗ[π] K}
    (hα : IsBaseChangeAlong τ α) (hβ : IsBaseChangeAlong π β) (n : N) (n' : N') :
    (glueDatum hα hβ).iso.hom ((1 : A) ⊗ₜ[B,τ] n) = (1 : A) ⊗ₜ[A',π] n' ↔ α n = β n' := by
  let := π.toAlgebra
  let e := LinearEquiv.ofBijective (liftAlong π β) hβ
  have h1 : (glueDatum hα hβ).iso.hom ((1 : A) ⊗ₜ[B,τ] n) = e.symm (α n) :=
    glueDatum_iso_hom_one_tmul hα hβ n
  have h2 : e ((1 : A) ⊗ₜ[A'] n') = β n' := liftAlong_one_tmul π β n'
  rw [h1]
  exact e.symm_apply_eq.trans ⟨fun h => h.trans h2, fun h => h.trans h2.symm⟩

/-- In a ring fibre square the map to the ring pullback is surjective. -/
theorem IsFibreSquare.surjective_toPullback (hsq : IsFibreSquare σ σ' τ π) :
    Function.Surjective (RingHom.codRestrict (σ.prod σ') (RingHom.pullback τ π)
      (fun x => DFunLike.congr_fun hsq.comm x)) := by
  rintro ⟨⟨b, a⟩, hba⟩
  obtain ⟨x, hx, hx'⟩ := hsq.exists_lift b a hba
  exact ⟨x, Subtype.ext (Prod.ext hx hx')⟩

/-- **A right adjoint of the comparison functor sends `glueDatum` to the fibre product.**  Let
`R₀` be a ring over which `ModuleGlueing.extensionOfScalarsToPullback` has a right adjoint `F`
described on elements by `hform`, and let `κ : B' ⟶ R₀` be compatible with the projections. Then
`F (glueDatum hα hβ)` is the fibre product `M = N ×_K N'` by an additive bijection which is
`κ`-semilinear and whose two components are the two components of the counit on the elements
`1 ⊗ l`. -/
theorem exists_addEquiv_of_isGlued {R₀ : Type u} [CommRing R₀] (toB : R₀ →+* B)
    (toA' : R₀ →+* A') (comm₀ : τ.comp toB = π.comp toA')
    {F : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} τ)
      (ModuleCat.extendScalars.{u, u, u} π) ⥤ ModuleCat.{u} R₀}
    (e : ∀ X, F.obj X ≃ CompatiblePairs τ π X)
    (adj : ModuleGlueing.extensionOfScalarsToPullback toB toA' τ π comm₀ ⊣ F)
    (hform : ∀ (L : ModuleCat.{u} R₀) (X) (h : L ⟶ F.obj X) (l : L),
      (e X (h l)).1.1 = ((adj.homEquiv L X).symm h).fst ((1 : B) ⊗ₜ[R₀,toB] l) ∧
        (e X (h l)).1.2 = ((adj.homEquiv L X).symm h).snd ((1 : A') ⊗ₜ[R₀,toA'] l))
    {α : N →ₛₗ[τ] K} {β : N' →ₛₗ[π] K} (hα : IsBaseChangeAlong τ α) (hβ : IsBaseChangeAlong π β)
    {p : M →ₛₗ[σ] N} {p' : M →ₛₗ[σ'] N'} (hM : IsGlued α β p p')
    (κ : B' →+* R₀) (hκ : toB.comp κ = σ) (hκ' : toA'.comp κ = σ') :
    ∃ ψ : F.obj (glueDatum hα hβ) ≃+ M,
      (∀ l, p (ψ l) = (adj.counit.app (glueDatum hα hβ)).fst ((1 : B) ⊗ₜ[R₀,toB] l) ∧
        p' (ψ l) = (adj.counit.app (glueDatum hα hβ)).snd ((1 : A') ⊗ₜ[R₀,toA'] l)) ∧
      ∀ (b : B') l, ψ (κ b • l) = b • ψ l := by
  let X := glueDatum hα hβ
  let L := F.obj X
  have hc : ∀ l : L, (e X l).1.1 = (adj.counit.app X).fst ((1 : B) ⊗ₜ[R₀,toB] l) ∧
      (e X l).1.2 = (adj.counit.app X).snd ((1 : A') ⊗ₜ[R₀,toA'] l) := fun l => by
    have h := hform L X (𝟙 L) l
    rw [adj.homEquiv_symm_id] at h
    exact h
  have hcond : ∀ l : L, α (e X l).1.1 = β (e X l).1.2 := fun l =>
    (glueDatum_compatible_iff hα hβ _ _).mp (e X l).2
  have hψ : ∀ l : L, ∃ m : M, p m = (e X l).1.1 ∧ p' m = (e X l).1.2 := fun l =>
    hM.exists_mk _ _ (hcond l)
  choose ψ hψ using hψ
  let u₁ := ((ModuleCat.extendRestrictScalarsAdj toB).homEquiv _ _ (adj.counit.app X).fst).hom
  let u₂ := ((ModuleCat.extendRestrictScalarsAdj toA').homEquiv _ _ (adj.counit.app X).snd).hom
  have hu₁ : ∀ l : L, (e X l).1.1 = u₁ l := fun l => (hc l).1
  have hu₂ : ∀ l : L, (e X l).1.2 = u₂ l := fun l => (hc l).2
  have hadd : ∀ l₁ l₂ : L, ψ (l₁ + l₂) = ψ l₁ + ψ l₂ := fun l₁ l₂ => by
    refine hM.injective _ _ ?_ ?_
    · rw [map_add, (hψ _).1, (hψ _).1, (hψ _).1, hu₁, hu₁, hu₁]
      exact u₁.map_add l₁ l₂
    · rw [map_add, (hψ _).2, (hψ _).2, (hψ _).2, hu₂, hu₂, hu₂]
      exact u₂.map_add l₁ l₂
  have hsmul : ∀ (b : B') (l : L), ψ (κ b • l) = b • ψ l := fun b l => by
    refine hM.injective _ _ ?_ ?_
    · rw [p.map_smulₛₗ, (hψ _).1, (hψ _).1, hu₁, hu₁, ← hκ]
      exact u₁.map_smul (κ b) l
    · rw [p'.map_smulₛₗ, (hψ _).2, (hψ _).2, hu₂, hu₂, ← hκ']
      exact u₂.map_smul (κ b) l
  have hψbij : Function.Bijective ψ := by
    refine ⟨fun l₁ l₂ h => (e X).injective (Subtype.ext (Prod.ext ?_ ?_)), fun m => ?_⟩
    · rw [← (hψ l₁).1, ← (hψ l₂).1]
      exact congrArg p h
    · rw [← (hψ l₁).2, ← (hψ l₂).2]
      exact congrArg p' h
    · let q : CompatiblePairs τ π X :=
        ⟨(p m, p' m), (glueDatum_compatible_iff hα hβ _ _).mpr (hM.comm m)⟩
      refine ⟨(e X).symm q, hM.injective _ _ ?_ ?_⟩
      · rw [(hψ _).1, Equiv.apply_symm_apply]
      · rw [(hψ _).2, Equiv.apply_symm_apply]
  have hzero : ψ 0 = 0 := by
    refine hM.injective _ _ ?_ ?_
    · rw [map_zero, (hψ _).1, hu₁]
      exact map_zero u₁
    · rw [map_zero, (hψ _).2, hu₂]
      exact map_zero u₂
  let ψh : L →+ M := { toFun := ψ, map_zero' := hzero, map_add' := hadd }
  exact ⟨AddEquiv.ofBijective ψh hψbij, fun l => ⟨(hψ l).1.trans (hu₁ l),
    (hψ l).2.trans (hu₂ l)⟩, hsmul⟩

/-- **The fibre product of two base changes recovers them** (the counit half of Stacks 07RU): if
`M` is the fibre product `N ×_K N'` of a `B`-module and an `A'`-module whose base changes to `A`
are both `K`, then `B ⊗_{B'} M = N` and `A' ⊗_{B'} M = N'` through the two projections. -/
theorem isBaseChangeAlong_of_isGlued (hsq : IsFibreSquare σ σ' τ π)
    {α : N →ₛₗ[τ] K} {β : N' →ₛₗ[π] K} (hα : IsBaseChangeAlong τ α) (hβ : IsBaseChangeAlong π β)
    {p : M →ₛₗ[σ] N} {p' : M →ₛₗ[σ'] N'} (hM : IsGlued α β p p') :
    IsBaseChangeAlong σ p ∧ IsBaseChangeAlong σ' p' := by
  obtain ⟨F, e, adj, hform, hcounit⟩ :=
    compatiblePairsRightAdjoint_counit_isIso_of_surjective τ π σ σ' hsq.comm hsq.surjective
      hsq.surjective_toPullback
  let X := glueDatum hα hβ
  let L := F.obj X
  obtain ⟨ψ, hψ, hψs⟩ := exists_addEquiv_of_isGlued σ σ' hsq.comm e adj hform hα hβ hM
    (RingHom.id B') rfl rfl
  let Ψ : L ≃ₗ[B'] M := ψ.toLinearEquiv fun b l => hψs b l
  have : IsIso (adj.counit.app X) := inferInstance
  let c₁ := ((CategoricalPullback.π₁ _ _).mapIso (asIso (adj.counit.app X))).toLinearEquiv
  let c₂ := ((CategoricalPullback.π₂ _ _).mapIso (asIso (adj.counit.app X))).toLinearEquiv
  let lift₁ : (ModuleCat.extendScalars σ).obj (ModuleCat.of B' M) ⟶ ModuleCat.of B N :=
    ModuleCat.ofHom (X := (ModuleCat.extendScalars σ).obj (ModuleCat.of B' M))
      (Y := ModuleCat.of B N) (liftAlong σ p)
  let lift₂ : (ModuleCat.extendScalars σ').obj (ModuleCat.of B' M) ⟶ ModuleCat.of A' N' :=
    ModuleCat.ofHom (X := (ModuleCat.extendScalars σ').obj (ModuleCat.of B' M))
      (Y := ModuleCat.of A' N') (liftAlong σ' p')
  let Ψc : L ≅ ModuleCat.of B' M := Ψ.toModuleIso
  have key₁ : (ModuleCat.extendScalars σ).map Ψc.hom ≫ lift₁ = (adj.counit.app X).fst := by
    refine ModuleCat.ExtendScalars.hom_ext fun l => ?_
    change liftAlong σ p ((1 : B) ⊗ₜ[B',σ] ψ l) = _
    rw [liftAlong_one_tmul]
    exact (hψ l).1
  have key₂ : (ModuleCat.extendScalars σ').map Ψc.hom ≫ lift₂ = (adj.counit.app X).snd := by
    refine ModuleCat.ExtendScalars.hom_ext fun l => ?_
    change liftAlong σ' p' ((1 : A') ⊗ₜ[B',σ'] ψ l) = _
    rw [liftAlong_one_tmul]
    exact (hψ l).2
  have hb₁ : Function.Bijective ((ModuleCat.extendScalars σ).map Ψc.hom ≫ lift₁) := by
    rw [key₁]
    exact c₁.bijective
  have hb₂ : Function.Bijective ((ModuleCat.extendScalars σ').map Ψc.hom ≫ lift₂) := by
    rw [key₂]
    exact c₂.bijective
  have hm₁ : Function.Bijective ((ModuleCat.extendScalars σ).map Ψc.hom) :=
    ConcreteCategory.bijective_of_isIso _
  have hm₂ : Function.Bijective ((ModuleCat.extendScalars σ').map Ψc.hom) :=
    ConcreteCategory.bijective_of_isIso _
  exact ⟨(Function.Bijective.of_comp_iff _ hm₁).mp (by exact hb₁),
    (Function.Bijective.of_comp_iff _ hm₂).mp (by exact hb₂)⟩

/-- **The fibre product of two flat base changes is flat** (Stacks 0D2I): in the situation of
`MilnorPatching.isBaseChangeAlong_of_isGlued`, if `N` is flat over `B` and `N'` is flat over `A'`
then `M = N ×_K N'` is flat over `B'`. -/
theorem flat_of_isGlued (hsq : IsFibreSquare σ σ' τ π)
    {α : N →ₛₗ[τ] K} {β : N' →ₛₗ[π] K} (hα : IsBaseChangeAlong τ α) (hβ : IsBaseChangeAlong π β)
    {p : M →ₛₗ[σ] N} {p' : M →ₛₗ[σ'] N'} (hM : IsGlued α β p p') [Module.Flat B N]
    [Module.Flat A' N'] : Module.Flat B' M := by
  let base : RingFibreProduct.Situation τ π (RingHom.ker π) := ⟨hsq.surjective, rfl⟩
  have H := flatModulesEquivalenceOverFibreProduct τ π (RingHom.ker π) base
  obtain ⟨F, e, adj, hform, -, hflat, -⟩ := H
  let X := glueDatum hα hβ
  have hfX : Module.Flat base.fibreProduct (F.obj X) := hflat X
    ⟨(inferInstance : Module.Flat B N), (inferInstance : Module.Flat A' N')⟩
  let κ : B' →+* base.fibreProduct :=
    RingHom.codRestrict (σ.prod σ') (RingHom.pullback τ π) (fun x => DFunLike.congr_fun hsq.comm x)
  have hκ : Function.Bijective κ := ⟨fun x y h => hsq.injective x y
    (congrArg (fun z : base.fibreProduct => z.1.1) h)
    (congrArg (fun z : base.fibreProduct => z.1.2) h), hsq.surjective_toPullback⟩
  obtain ⟨ψ, -, hψs⟩ := exists_addEquiv_of_isGlued _ _ _ e adj hform hα hβ hM κ rfl rfl
  let : Algebra B' base.fibreProduct := κ.toAlgebra
  let : Module B' (F.obj X) := Module.compHom _ κ
  have : IsScalarTower B' base.fibreProduct (F.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat B' base.fibreProduct := RingHom.Flat.of_bijective hκ
  have : Module.Flat B' (F.obj X) := Module.Flat.trans B' base.fibreProduct (F.obj X)
  exact Module.Flat.of_linearEquiv (ψ.toLinearEquiv fun b l => hψs b l).symm

/-- **A flat module embeds into its two base changes** (the injectivity half of the unit of
Stacks 07RU for a flat module): if `L` is flat over `B' = B ×_A A'`, an element of `L` vanishing
in both base changes `B ⊗_{B'} L` and `A' ⊗_{B'} L` is zero, because `B' ⟶ B × A'` is injective. -/
theorem eq_zero_of_flat (hinj : ∀ x y : B', σ x = σ y → σ' x = σ' y → x = y)
    {L : Type u} [AddCommGroup L] [Module B' L] [Module.Flat B' L]
    {q : L →ₛₗ[σ] N} {q' : L →ₛₗ[σ'] N'} (hq : IsBaseChangeAlong σ q)
    (hq' : IsBaseChangeAlong σ' q') (l : L) (h₁ : q l = 0) (h₂ : q' l = 0) : l = 0 := by
  let := σ.toAlgebra
  let := σ'.toAlgebra
  have e₁ : (1 : B) ⊗ₜ[B'] l = 0 :=
    hq.1 ((liftAlong_one_tmul σ q l).trans (h₁.trans (map_zero _).symm))
  have e₂ : (1 : A') ⊗ₜ[B'] l = 0 :=
    hq'.1 ((liftAlong_one_tmul σ' q' l).trans (h₂.trans (map_zero _).symm))
  let j : B' →ₗ[B'] B × A' := (Algebra.linearMap B' B).prod (Algebra.linearMap B' A')
  have hj : Function.Injective j := fun x y h =>
    hinj x y (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hjt := Module.Flat.rTensor_preserves_injective_linearMap (M := L) j hj
  have h₃ : j.rTensor L ((1 : B') ⊗ₜ[B'] l) = 0 := by
    apply (TensorProduct.prodLeft B' B' B A' L).injective
    rw [LinearMap.rTensor_tmul, map_zero]
    change (TensorProduct.prodLeft B' B' B A' L) ((algebraMap B' B 1, algebraMap B' A' 1) ⊗ₜ l) = 0
    rw [TensorProduct.prodLeft_tmul, map_one, map_one, e₁, e₂]
    rfl
  have h₄ : (1 : B') ⊗ₜ[B'] l = 0 := hjt (h₃.trans (map_zero _).symm)
  have h₅ := congrArg (TensorProduct.lid B' L) h₄
  rwa [TensorProduct.lid_tmul, one_smul, map_zero] at h₅

/-- **Any module maps onto the fibre product of two quotients of its base changes** (Stacks 08IG
and 08KJ): if `q : L ⟶ N` and `q' : L ⟶ N'` generate `N` over `B` and `N'` over `A'` and agree in
`K`, then every compatible pair `(n, n')` comes from an element of `L`. -/
theorem exists_eq_of_surjective (hsq : IsFibreSquare σ σ' τ π)
    {α : N →ₛₗ[τ] K} {β : N' →ₛₗ[π] K} (hβ : IsBaseChangeAlong π β)
    {L : Type u} [AddCommGroup L] [Module B' L] (q : L →ₛₗ[σ] N) (q' : L →ₛₗ[σ'] N')
    (hq : Function.Surjective (liftAlong σ q)) (hq' : Function.Surjective (liftAlong σ' q'))
    (n : N) (n' : N') (hnn : α n = β n') (hqq : ∀ l, α (q l) = β (q' l)) :
    ∃ l, q l = n ∧ q' l = n' := by
  let := σ.toAlgebra
  let := σ'.toAlgebra
  have hσ : Function.Surjective σ := fun b => by
    obtain ⟨a, ha⟩ := hsq.surjective (τ b)
    obtain ⟨x, hx, -⟩ := hsq.exists_lift b a ha.symm
    exact ⟨x, hx⟩
  have hrange : ∀ x : B ⊗[B'] L, ∃ l, q l = liftAlong σ q x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b l =>
      obtain ⟨b', rfl⟩ := hσ b
      exact ⟨b' • l, by rw [q.map_smulₛₗ, liftAlong_tmul]⟩
    | add x y hx hy =>
      obtain ⟨l₁, h₁⟩ := hx
      obtain ⟨l₂, h₂⟩ := hy
      exact ⟨l₁ + l₂, by rw [map_add, map_add, h₁, h₂]⟩
  obtain ⟨x, hx⟩ := hq n
  obtain ⟨l₀, hl₀⟩ := hrange x
  rw [hx] at hl₀
  have hker : ∀ m ∈ RingHom.ker π • (⊤ : Submodule A' N'), ∃ l, q l = 0 ∧ q' l = m := by
    intro m hm
    refine Submodule.smul_induction_on (p := fun m => ∃ l, q l = 0 ∧ q' l = m) hm ?_ ?_
    · rintro a ha y -
      obtain ⟨z, rfl⟩ := hq' y
      induction z using TensorProduct.inductionOn with
      | tmul a' l =>
        have hz : π (a * a') = τ 0 := by
          rw [map_mul, RingHom.mem_ker.mp ha, zero_mul, map_zero]
        obtain ⟨r, hr, hr'⟩ := hsq.exists_lift 0 (a * a') hz.symm
        refine ⟨r • l, by rw [q.map_smulₛₗ, hr, zero_smul], ?_⟩
        rw [q'.map_smulₛₗ, hr', liftAlong_tmul, smul_smul]
      | add z₁ z₂ h₁ h₂ =>
        obtain ⟨l₁, h₁q, h₁q'⟩ := h₁
        obtain ⟨l₂, h₂q, h₂q'⟩ := h₂
        exact ⟨l₁ + l₂, by rw [map_add, h₁q, h₂q, add_zero], by
          rw [map_add, h₁q', h₂q', map_add, smul_add]⟩
    · rintro m₁ m₂ ⟨l₁, h₁q, h₁q'⟩ ⟨l₂, h₂q, h₂q'⟩
      exact ⟨l₁ + l₂, by rw [map_add, h₁q, h₂q, add_zero], by rw [map_add, h₁q', h₂q']⟩
  have hβm : β (n' - q' l₀) = 0 := by
    rw [map_sub, ← hnn, ← hl₀, hqq, sub_self]
  have hmem : n' - q' l₀ ∈ RingHom.ker π • (⊤ : Submodule A' N') := by
    let := π.toAlgebra
    rw [← ker_tensorProductMk_of_surjective π hsq.surjective]
    refine hβ.1 ?_
    change liftAlong π β (1 ⊗ₜ (n' - q' l₀)) = liftAlong π β 0
    rw [liftAlong_one_tmul, hβm, map_zero]
  obtain ⟨l₁, hl₁, hl₁'⟩ := hker _ hmem
  exact ⟨l₀ + l₁, by rw [map_add, hl₀, hl₁, add_zero], by rw [map_add, hl₁', add_sub_cancel]⟩

end Glue

section Relative

variable {B' B A' A D' D C' C : Type u} [CommRing B'] [CommRing B] [CommRing A'] [CommRing A]
  [CommRing D'] [CommRing D] [CommRing C'] [CommRing C]
  (σ : B' →+* B) (σ' : B' →+* A') (τ : B →+* A) (π : A' →+* A)
  (ρ : B' →+* D') (δ : D' →+* D) (βD : B →+* D) (γ : D' →+* C') (αC : A' →+* C')
  (ε : D →+* C) (ε' : C' →+* C) (κ : A →+* C)

/-- **The relative Milnor square** (the situation of Stacks 08KK): a ring fibre square
`B' = B ×_A A'` with `A' ⟶ A` surjective, a ring map `B' ⟶ D'`, and the three base changes
`D = D' ⊗_{B'} B`, `C' = D' ⊗_{B'} A'` and `C = D ⊗_B A`, each given as a cocartesian square of
rings, with the two maps into `C` compatible. -/
structure IsRelativeSquare : Prop where
  fibre : IsFibreSquare σ σ' τ π
  pushD : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom ρ) (CommRingCat.ofHom βD)
    (CommRingCat.ofHom δ)
  pushC' : IsPushout (CommRingCat.ofHom σ') (CommRingCat.ofHom ρ) (CommRingCat.ofHom αC)
    (CommRingCat.ofHom γ)
  pushC : IsPushout (CommRingCat.ofHom τ) (CommRingCat.ofHom βD) (CommRingCat.ofHom κ)
    (CommRingCat.ofHom ε)
  commC : ε.comp δ = ε'.comp γ
  commA : ε'.comp αC = κ.comp π

variable {σ σ' τ π ρ δ βD γ αC ε ε' κ}

/-- In a relative Milnor square `C` is also `C' ⊗_{A'} A`: paste the two squares through `D` and
cancel the square through `C'`. -/
theorem IsRelativeSquare.pushC₂ (h : IsRelativeSquare σ σ' τ π ρ δ βD γ αC ε ε' κ) :
    IsPushout (CommRingCat.ofHom π) (CommRingCat.ofHom αC) (CommRingCat.ofHom κ)
      (CommRingCat.ofHom ε') := by
  have outer := h.pushD.paste_horiz h.pushC
  have e₁ : CommRingCat.ofHom σ ≫ CommRingCat.ofHom τ =
      CommRingCat.ofHom σ' ≫ CommRingCat.ofHom π := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h.fibre.comm]
  have e₂ : CommRingCat.ofHom δ ≫ CommRingCat.ofHom ε =
      CommRingCat.ofHom γ ≫ CommRingCat.ofHom ε' := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h.commC]
  rw [e₁, e₂] at outer
  refine IsPushout.of_left outer ?_ h.pushC'
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h.commA]

/-- In a relative Milnor square, `δ ∘ ρ = βD ∘ σ`. -/
theorem IsRelativeSquare.wD (h : IsRelativeSquare σ σ' τ π ρ δ βD γ αC ε ε' κ) :
    δ.comp ρ = βD.comp σ := congrArg CommRingCat.Hom.hom h.pushD.w.symm

/-- In a relative Milnor square, `γ ∘ ρ = αC ∘ σ'`. -/
theorem IsRelativeSquare.wC' (h : IsRelativeSquare σ σ' τ π ρ δ βD γ αC ε ε' κ) :
    γ.comp ρ = αC.comp σ' := congrArg CommRingCat.Hom.hom h.pushC'.w.symm

/-- In a relative Milnor square, `ε ∘ βD = κ ∘ τ`. -/
theorem IsRelativeSquare.wC (h : IsRelativeSquare σ σ' τ π ρ δ βD γ αC ε ε' κ) :
    ε.comp βD = κ.comp τ := congrArg CommRingCat.Hom.hom h.pushC.w.symm

variable {N N' K M : Type u} [AddCommGroup N] [Module D N] [AddCommGroup N'] [Module C' N']
  [AddCommGroup K] [Module C K] [AddCommGroup M] [Module D' M]

/-- **The relative gluing recovers its two pieces** (Stacks 08KM): in a relative Milnor square,
the fibre product `M = N ×_K N'` of a `D`-module and a `C'`-module whose base changes to `C` are
both `K` satisfies `D ⊗_{D'} M = N` and `C' ⊗_{D'} M = N'`. -/
theorem IsRelativeSquare.isBaseChangeAlong_of_isGlued
    (h : IsRelativeSquare σ σ' τ π ρ δ βD γ αC ε ε' κ)
    {α : N →ₛₗ[ε] K} {β : N' →ₛₗ[ε'] K} (hα : IsBaseChangeAlong ε α)
    (hβ : IsBaseChangeAlong ε' β) {p : M →ₛₗ[δ] N} {p' : M →ₛₗ[γ] N'}
    (hM : IsGlued α β p p') : IsBaseChangeAlong δ p ∧ IsBaseChangeAlong γ p' := by
  let : Module B N := Module.compHom N βD
  let : Module A' N' := Module.compHom N' αC
  let : Module A K := Module.compHom K κ
  let : Module B' M := Module.compHom M ρ
  have hα₀ := (isBaseChangeAlong_iff_of_isPushout τ βD κ ε h.pushC α).mp hα
  have hβ₀ := (isBaseChangeAlong_iff_of_isPushout π αC κ ε' h.pushC₂ β).mp hβ
  obtain ⟨h₁, h₂⟩ := MilnorPatching.isBaseChangeAlong_of_isGlued h.fibre hα₀ hβ₀
    (p := restrictSquare σ ρ βD δ h.wD p) (p' := restrictSquare σ' ρ αC γ h.wC' p')
    ⟨hM.comm, hM.injective, hM.exists_mk⟩
  exact ⟨(isBaseChangeAlong_iff_of_isPushout σ ρ βD δ h.pushD p).mpr h₁,
    (isBaseChangeAlong_iff_of_isPushout σ' ρ αC γ h.pushC' p').mpr h₂⟩

/-- **The relative gluing of flat pieces is flat** (Stacks 07RW): in the situation of
`MilnorPatching.IsRelativeSquare.isBaseChangeAlong_of_isGlued`, if `N` is flat over `B` and `N'`
over `A'` then `M` is flat over `B'`. -/
theorem IsRelativeSquare.flat_of_isGlued (h : IsRelativeSquare σ σ' τ π ρ δ βD γ αC ε ε' κ)
    {α : N →ₛₗ[ε] K} {β : N' →ₛₗ[ε'] K} (hα : IsBaseChangeAlong ε α)
    (hβ : IsBaseChangeAlong ε' β) {p : M →ₛₗ[δ] N} {p' : M →ₛₗ[γ] N'}
    (hM : IsGlued α β p p') (hN : @Module.Flat B N _ _ (Module.compHom N βD))
    (hN' : @Module.Flat A' N' _ _ (Module.compHom N' αC)) :
    @Module.Flat B' M _ _ (Module.compHom M ρ) := by
  let : Module B N := Module.compHom N βD
  let : Module A' N' := Module.compHom N' αC
  let : Module A K := Module.compHom K κ
  let : Module B' M := Module.compHom M ρ
  have hα₀ := (isBaseChangeAlong_iff_of_isPushout τ βD κ ε h.pushC α).mp hα
  have hβ₀ := (isBaseChangeAlong_iff_of_isPushout π αC κ ε' h.pushC₂ β).mp hβ
  exact MilnorPatching.flat_of_isGlued h.fibre hα₀ hβ₀
    (p := restrictSquare σ ρ βD δ h.wD p) (p' := restrictSquare σ' ρ αC γ h.wC' p')
    ⟨hM.comm, hM.injective, hM.exists_mk⟩

/-- **A relatively flat module embeds into its two base changes**: an element of a `D'`-module
`L` flat over `B'` vanishing in `D ⊗_{D'} L` and in `C' ⊗_{D'} L` is zero. -/
theorem IsRelativeSquare.eq_zero_of_flat (h : IsRelativeSquare σ σ' τ π ρ δ βD γ αC ε ε' κ)
    {L : Type u} [AddCommGroup L] [Module D' L] (hL : @Module.Flat B' L _ _ (Module.compHom L ρ))
    {q : L →ₛₗ[δ] N} {q' : L →ₛₗ[γ] N'} (hq : IsBaseChangeAlong δ q)
    (hq' : IsBaseChangeAlong γ q') (l : L) (h₁ : q l = 0) (h₂ : q' l = 0) : l = 0 := by
  let : Module B N := Module.compHom N βD
  let : Module A' N' := Module.compHom N' αC
  let : Module B' L := Module.compHom L ρ
  exact MilnorPatching.eq_zero_of_flat h.fibre.injective
    ((isBaseChangeAlong_iff_of_isPushout σ ρ βD δ h.pushD q).mp hq)
    ((isBaseChangeAlong_iff_of_isPushout σ' ρ αC γ h.pushC' q').mp hq') l h₁ h₂

/-- **A module maps onto the relative gluing of two quotients of its base changes** (Stacks 08IG
and 08KJ, relative form). -/
theorem IsRelativeSquare.exists_eq_of_surjective
    (h : IsRelativeSquare σ σ' τ π ρ δ βD γ αC ε ε' κ)
    {α : N →ₛₗ[ε] K} {β : N' →ₛₗ[ε'] K} (hβ : IsBaseChangeAlong ε' β)
    {L : Type u} [AddCommGroup L] [Module D' L] (q : L →ₛₗ[δ] N) (q' : L →ₛₗ[γ] N')
    (hq : Function.Surjective (liftAlong δ q)) (hq' : Function.Surjective (liftAlong γ q'))
    (n : N) (n' : N') (hnn : α n = β n') (hqq : ∀ l, α (q l) = β (q' l)) :
    ∃ l, q l = n ∧ q' l = n' := by
  let : Module B N := Module.compHom N βD
  let : Module A' N' := Module.compHom N' αC
  let : Module A K := Module.compHom K κ
  let : Module B' L := Module.compHom L ρ
  exact MilnorPatching.exists_eq_of_surjective h.fibre
    (α := restrictSquare τ βD κ ε h.wC α)
    ((isBaseChangeAlong_iff_of_isPushout π αC κ ε' h.pushC₂ β).mp hβ)
    (restrictSquare σ ρ βD δ h.wD q) (restrictSquare σ' ρ αC γ h.wC' q')
    ((surjective_liftAlong_iff_of_isPushout σ ρ βD δ h.pushD q).mp hq)
    ((surjective_liftAlong_iff_of_isPushout σ' ρ αC γ h.pushC' q').mp hq') n n' hnn hqq

end Relative

end MilnorPatching
