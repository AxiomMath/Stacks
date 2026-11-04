module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.Algebra.Module.Injective

/-!
# Epimorphisms of rings and restriction of scalars

Let `R → S` be a homomorphism of commutative rings. Three properties of it are shown
equivalent.

1. **Epimorphism of rings.** `R → S` is an *epimorphism* in the category of commutative rings:
   for every commutative ring `T` and every pair of ring homomorphisms `ψ₁, ψ₂ : S → T` that agree
   on the image of `R`, `ψ₁ = ψ₂`.

2. **The Hom comparison.** Every `S`-module is an `R`-module by restriction of scalars, and
   every `S`-linear map is `R`-linear, giving a canonical inclusion
   `Hom_S(N₁, N₂) ⊆ Hom_R(N₁, N₂)`; statement (2) asserts this inclusion is an equality.

3. **Fully faithful restriction.** The restriction-of-scalars functor `Mod_S → Mod_R` is fully
   faithful.

As an application, injectivity of a module descends along an epimorphism of rings: an `S`-module
that is injective as an `R`-module is an injective `S`-module, since every `R`-linear map between
`S`-modules is already `S`-linear, so an extension produced over `R` is an extension over `S`.

## Main results

* `CommRingCat.epi_tfae_restrictScalars`: the equivalence of (1), (2) and (3).
* `Module.Injective.of_isEpi`: along an epimorphism of rings `R → S`, an `S`-module injective
  over `R` is injective over `S`.

## Implementation notes

The ring map is `algebraMap R S`, so that the restricted `R`-module structure on an `S`-module `N`
can be any `[Module R N]` with `[IsScalarTower R S N]` rather than one fixed construction. The
epimorphism property is `CategoryTheory.Epi` in `CommRingCat`; the proof passes through Mathlib's
`Algebra.IsEpi` by `CommRingCat.epi_iff_epi`, which characterises it by the identity
`1 ⊗ s = s ⊗ 1` in `S ⊗[R] S`. The Hom comparison is surjectivity of
`LinearMap.restrictScalars R : (N₁ →ₗ[S] N₂) → (N₁ →ₗ[R] N₂)`, and full faithfulness is
`Functor.FullyFaithful` of `ModuleCat.restrictScalars`.

Modules live in `Type (max u v)`, where `u` is the universe of `R` and `S`: the proof of (2) ⇒ (1)
tests (2) on `S ⊗[R] S`, which has to fit.
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v

namespace Algebra.IsEpi

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsEpi R S]
  {N₁ N₂ : Type*} [AddCommGroup N₁] [AddCommGroup N₂] [Module R N₁] [Module R N₂]
  [Module S N₁] [Module S N₂] [IsScalarTower R S N₁] [IsScalarTower R S N₂]

/-- Along an epimorphism of rings `R → S`, an `R`-linear map between `S`-modules is `S`-linear.

The `R`-bilinear map `(s, t) ↦ s • f (t • n)` factors through `S ⊗[R] S`, where
`1 ⊗ s = s ⊗ 1`; evaluating on both sides gives `f (s • n) = s • f n`. -/
theorem map_smul_of_linearMap (f : N₁ →ₗ[R] N₂) (s : S) (n : N₁) : f (s • n) = s • f n := by
  let B : S →ₗ[R] S →ₗ[R] N₂ := LinearMap.mk₂ R (fun s t => s • f (t • n))
    (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
    (fun _ _ _ => by rw [add_smul, map_add, smul_add])
    (fun _ _ _ => by rw [smul_assoc, map_smul, smul_comm])
  simpa [B] using congrArg (_root_.TensorProduct.lift B)
    ((Algebra.isEpi_iff_forall_one_tmul_eq R S).mp ‹_› s)

/-- Along an epimorphism of rings `R → S`, every `R`-linear map between `S`-modules is the
restriction of an `S`-linear map. -/
theorem restrictScalars_surjective :
    Function.Surjective (LinearMap.restrictScalars R : (N₁ →ₗ[S] N₂) → N₁ →ₗ[R] N₂) :=
  fun f => ⟨{ f with map_smul' := map_smul_of_linearMap f }, rfl⟩

end Algebra.IsEpi

/-- Every `S`-module is an `R`-module through `R → S`, compatibly with the `S`-action. -/
private theorem exists_module_isScalarTower (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (N : Type*) [AddCommGroup N] [Module S N] :
    ∃ i : Module R N, letI := i; IsScalarTower R S N :=
  let _ := Module.compHom N (algebraMap R S)
  ⟨_, .of_algebraMap_smul fun _ _ => rfl⟩

/-- Let `R → S` be an epimorphism of rings and let `E` be an `S`-module. If `E` is injective as
an `R`-module, then `E` is an injective `S`-module.

An `S`-linear map into `E` out of an `S`-module is in particular `R`-linear, so it extends
`R`-linearly along an injective `S`-linear map, and that extension is `S`-linear because
`R → S` is an epimorphism. -/
@[stacks 08YV]
theorem Module.Injective.of_isEpi (R : Type*) {S E : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsEpi R S] [AddCommGroup E] [Module R E] [Module S E]
    [IsScalarTower R S E] (h : Module.Injective R E) : Module.Injective S E where
  out X Y _ _ _ _ f hf g := by
    obtain ⟨_, _⟩ := exists_module_isScalarTower R S X
    obtain ⟨_, _⟩ := exists_module_isScalarTower R S Y
    obtain ⟨φ, hφ⟩ := h.out (f.restrictScalars R) hf (g.restrictScalars R)
    exact ⟨{ φ with map_smul' := Algebra.IsEpi.map_smul_of_linearMap φ }, hφ⟩

namespace CommRingCat

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The restriction-of-scalars functor along `R → S` is full as soon as every additive map
between `S`-modules that commutes with the action of the image of `R` commutes with the action of
`S`. -/
private theorem full_restrictScalars
    (h : ∀ (N₁ N₂ : Type (max u v)) [AddCommGroup N₁] [AddCommGroup N₂] [Module S N₁]
      [Module S N₂] (f : N₁ →+ N₂), (∀ (r : R) (n : N₁), f (algebraMap R S r • n) =
        algebraMap R S r • f n) → ∀ (s : S) (n : N₁), f (s • n) = s • f n) :
    (ModuleCat.restrictScalars.{max u v} (algebraMap R S)).Full where
  map_surjective g :=
    ⟨ModuleCat.ofHom
      { toFun := g
        map_add' := map_add g.hom
        map_smul' := h _ _ g.hom.toAddMonoidHom fun r n => g.hom.map_smul r n },
      rfl⟩

/-- For a homomorphism `R → S` of commutative rings, the following are equivalent:

1. `R → S` is an epimorphism of (commutative) rings;
2. for all `S`-modules `N₁, N₂`, every `R`-linear map is `S`-linear, i.e.
   `Hom_S(N₁,N₂) = Hom_R(N₁,N₂)`;
3. the restriction-of-scalars functor `Mod_S → Mod_R` is fully faithful. -/
@[stacks 08YS]
theorem epi_tfae_restrictScalars :
    [ Epi (CommRingCat.ofHom (algebraMap R S)),
      ∀ (N₁ N₂ : Type (max u v)) [AddCommGroup N₁] [AddCommGroup N₂] [Module R N₁]
        [Module R N₂] [Module S N₁] [Module S N₂] [IsScalarTower R S N₁]
        [IsScalarTower R S N₂],
        Function.Surjective (LinearMap.restrictScalars R : (N₁ →ₗ[S] N₂) → N₁ →ₗ[R] N₂),
      Nonempty (ModuleCat.restrictScalars.{max u v} (algebraMap R S)).FullyFaithful
    ].TFAE := by
  tfae_have 1 → 2 := by
    rw [CommRingCat.epi_iff_epi]
    intro _ N₁ N₂ _ _ _ _ _ _ _ _
    exact Algebra.IsEpi.restrictScalars_surjective
  tfae_have 2 → 1 := by
    -- Test (2) on the swap of `S ⊗[R] S`, with `S` acting on the left factor: it is `R`-linear,
    -- and `S`-linear exactly when `1 ⊗ s = s ⊗ 1`.
    intro h
    rw [CommRingCat.epi_iff_epi, Algebra.isEpi_iff_forall_one_tmul_eq]
    intro s
    let e : ULift.{v} (S ⊗[R] S) ≃ₗ[R] S ⊗[R] S := ULift.moduleEquiv
    obtain ⟨g, hg⟩ := h _ _ (e.symm.toLinearMap ∘ₗ (TensorProduct.comm R S S).toLinearMap ∘ₗ
      e.toLinearMap)
    have hgx (x) : g x = ULift.up (TensorProduct.comm R S S x.down) := LinearMap.congr_fun hg x
    simpa [hgx, TensorProduct.smul_tmul'] using congrArg ULift.down
      (g.map_smul s (ULift.up (1 ⊗ₜ[R] 1)))
  tfae_have 2 → 3 := by
    intro h
    have := full_restrictScalars R S fun N₁ N₂ _ _ _ _ f hf => by
      obtain ⟨_, _⟩ := exists_module_isScalarTower R S N₁
      obtain ⟨_, _⟩ := exists_module_isScalarTower R S N₂
      obtain ⟨g, hg⟩ := h N₁ N₂ { f with
        map_smul' := fun r n => by simpa [algebraMap_smul] using hf r n }
      have hgx (x : N₁) : g x = f x := LinearMap.congr_fun hg x
      intro s n
      rw [← hgx, ← hgx, map_smul]
    exact ⟨.ofFullyFaithful _⟩
  tfae_have 3 → 2 := by
    rintro ⟨hF⟩ N₁ N₂ _ _ _ _ _ _ _ _ f
    have hf (r : R) (n : N₁) : f (algebraMap R S r • n) = algebraMap R S r • f n := by
      rw [algebraMap_smul, algebraMap_smul, map_smul]
    let F := ModuleCat.restrictScalars.{max u v} (algebraMap R S)
    let f' : F.obj (.of S N₁) ⟶ F.obj (.of S N₂) :=
      ModuleCat.ofHom (X := F.obj (.of S N₁)) (Y := F.obj (.of S N₂))
      { toFun := f
        map_add' := f.map_add
        map_smul' := hf }
    exact ⟨(hF.preimage f').hom,
      LinearMap.ext fun n => ConcreteCategory.congr_hom (hF.map_preimage f') n⟩
  tfae_finish

end CommRingCat
