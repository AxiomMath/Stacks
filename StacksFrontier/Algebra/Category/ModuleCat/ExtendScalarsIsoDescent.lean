module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.RingTheory.Descent.AmitsurComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of isomorphisms of module-valued functors along a faithfully flat ring map

Let `f : R →+* C` be faithfully flat.  A `C`-linear map `φ : C ⊗_R M ⟶ C ⊗_R N` whose values on
the elements `1 ⊗ m` are killed by the degree-zero Amitsur differential (the two images of
`C ⊗_R N` in `C ⊗_R C ⊗_R N` agree on them) is the base change of a unique `R`-linear map
`M ⟶ N` (`Module.Descent.existsUnique_baseChange_eq`), by exactness of the Amitsur complex in
degree zero.

Applied objectwise this descends an isomorphism of functors
`θ : F ⋙ extendScalars f ≅ G ⋙ extendScalars f` satisfying that compatibility to an isomorphism
`e : F ≅ G` with `extendScalars f` of `e` equal to `θ`
(`ModuleCat.descendIsoOfFaithfullyFlat`); if `F` and `G` are monoidal and `θ` is monoidal, so is
`e` (`ModuleCat.isMonoidal_descendIsoOfFaithfullyFlat`), because `extendScalars f` is faithful
and monoidal.

## Main results

* `Module.Descent.existsUnique_baseChange_eq`: descent of linear maps.
* `ModuleCat.extendScalars_map_injective_of_faithfullyFlat`: `extendScalars f` is faithful.
* `ModuleCat.descendIsoOfFaithfullyFlat` and `ModuleCat.extendScalars_map_descendIso_hom_app`.
* `ModuleCat.isMonoidal_descendIsoOfFaithfullyFlat`.

## References

* [Stacks Project, Tag 023F](https://stacks.math.columbia.edu/tag/023F)
* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public section

open TensorProduct CategoryTheory MonoidalCategory

universe u

namespace Module.Descent

variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C] [Module.FaithfullyFlat R C]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Descent of linear maps along a faithfully flat ring map.**  A `C`-linear map
`φ : C ⊗_R M →ₗ[C] C ⊗_R N` whose values on the elements `1 ⊗ m` are killed by the degree-zero
Amitsur differential of `N` is the base change of a unique `R`-linear map `M →ₗ[R] N`. -/
@[sga "1 VIII 1.4"]
theorem existsUnique_baseChange_eq (φ : C ⊗[R] M →ₗ[C] C ⊗[R] N)
    (hφ : ∀ m, amitsurDiff₀ R C N (φ ((1 : C) ⊗ₜ[R] m)) = 0) :
    ∃! g : M →ₗ[R] N, g.baseChange C = φ := by
  have hinj := Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := C) N
  have hex : ∀ m, ∃ n, (1 : C) ⊗ₜ[R] n = φ ((1 : C) ⊗ₜ[R] m) := fun m ↦
    ((exact_amitsur_degree_zero R C N) _).1 (hφ m)
  choose g hg using hex
  let g' : M →ₗ[R] N :=
    { toFun := g
      map_add' := fun a b ↦ hinj (by
        simp only [TensorProduct.mk_apply, tmul_add, hg, map_add])
      map_smul' := fun r a ↦ hinj (by
        simp only [TensorProduct.mk_apply, hg, RingHom.id_apply, tmul_smul]
        rw [← algebraMap_smul C r ((1 : C) ⊗ₜ[R] a), map_smul, ← hg, algebraMap_smul]) }
  have hg' : g'.baseChange C = φ := by
    refine TensorProduct.AlgebraTensorModule.ext fun c m ↦ ?_
    rw [show c ⊗ₜ[R] m = c • ((1 : C) ⊗ₜ[R] m) by rw [smul_tmul', smul_eq_mul, mul_one],
      map_smul, map_smul, LinearMap.baseChange_tmul]
    exact congrArg (c • ·) (hg m)
  refine ⟨g', hg', fun g₂ hg₂ ↦ LinearMap.ext fun m ↦ hinj ?_⟩
  show (1 : C) ⊗ₜ[R] g₂ m = (1 : C) ⊗ₜ[R] g m
  rw [hg, ← hg₂, LinearMap.baseChange_tmul]

/-- **The degree-zero Amitsur differential vanishes exactly on the elements whose two images in
`(S ⊗_R S) ⊗_R M` agree**, the images along the two inclusions `S → S ⊗_R S`. Reassociating,
`(S ⊗_R S) ⊗_R M = S ⊗_R (S ⊗_R M)` carries the image along the first inclusion to the first term
of the differential and the one along the second inclusion to the second. -/
theorem amitsurDiff₀_eq_zero_iff {S : Type*} [CommRing S] [Algebra R S] (x : S ⊗[R] M) :
    amitsurDiff₀ R S M x = 0 ↔
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S).toLinearMap.rTensor M x =
        (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toLinearMap.rTensor M x := by
  have key : ∀ (ι : S →ₐ[R] S ⊗[R] S) (L : S ⊗[R] M →ₗ[R] S ⊗[R] (S ⊗[R] M)),
      (∀ s m, TensorProduct.assoc R S S M (ι s ⊗ₜ[R] m) = L (s ⊗ₜ[R] m)) →
        ∀ x, TensorProduct.assoc R S S M (ι.toLinearMap.rTensor M x) = L x :=
    fun ι L h x ↦ LinearMap.congr_fun
      (TensorProduct.ext' h : (TensorProduct.assoc R S S M).toLinearMap ∘ₗ ι.toLinearMap.rTensor M
        = L) x
  have h₁ := key Algebra.TensorProduct.includeLeft (LinearMap.lTensor S (TensorProduct.mk R S M 1))
    fun s m ↦ by simp
  have h₂ := key Algebra.TensorProduct.includeRight (TensorProduct.mk R S (S ⊗[R] M) 1)
    fun s m ↦ by simp
  rw [amitsurDiff₀, LinearMap.sub_apply, sub_eq_zero, ← h₁, ← h₂,
    (TensorProduct.assoc R S S M).injective.eq_iff]

end Module.Descent

namespace ModuleCat

variable {R C : Type u} [CommRing R] [CommRing C] (f : R →+* C) (hf : f.FaithfullyFlat)

include hf in
/-- **Extension of scalars along a faithfully flat ring map is faithful.** -/
@[ega "IV 4.8.3" "special case", sga "4 XVII 6.3.29" "special case"]
theorem extendScalars_map_injective_of_faithfullyFlat {M N : ModuleCat.{u} R} {g₁ g₂ : M ⟶ N}
    (h : (extendScalars f).map g₁ = (extendScalars f).map g₂) : g₁ = g₂ := by
  let := f.toAlgebra
  have : Module.FaithfullyFlat R C := hf
  ext m
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := C) N
    (congrArg (fun φ ↦ φ.hom ((1 : C) ⊗ₜ[R] m)) h)

variable {𝒞 : Type*} [Category 𝒞] {F G : 𝒞 ⥤ ModuleCat.{u} R}
  (θ : F ⋙ extendScalars f ≅ G ⋙ extendScalars f)
  (hθ : letI := f.toAlgebra
    ∀ X (m : F.obj X), Module.Descent.amitsurDiff₀ R C (G.obj X)
      ((θ.hom.app X).hom ((1 : C) ⊗ₜ[R] m)) = 0)

/-- **The compatibility of `ModuleCat.descendIsoOfFaithfullyFlat` from a gluing over `C ⊗_R C`.**
If for every `X` and `m ∈ F X` the two images of `θ_X(1 ⊗ m)` in `(C ⊗_R C) ⊗_R G X`, along the
two inclusions `C → C ⊗_R C`, agree — which is what the agreement of the two base changes of `θ`
to `C ⊗_R C` says on the generators `1 ⊗ 1 ⊗ m` — then `θ` satisfies the descent compatibility
`hθ` of `ModuleCat.descendIsoOfFaithfullyFlat`. -/
theorem amitsurDiff₀_hom_app_eq_zero_of_rTensor_eq
    (θ : F ⋙ extendScalars f ≅ G ⋙ extendScalars f)
    (h : letI := f.toAlgebra
      ∀ X (m : F.obj X),
        (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C).toLinearMap.rTensor (G.obj X)
            ((θ.hom.app X).hom ((1 : C) ⊗ₜ[R] m)) =
          (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C).toLinearMap.rTensor (G.obj X)
            ((θ.hom.app X).hom ((1 : C) ⊗ₜ[R] m))) :
    letI := f.toAlgebra
    ∀ X (m : F.obj X), Module.Descent.amitsurDiff₀ R C (G.obj X)
      ((θ.hom.app X).hom ((1 : C) ⊗ₜ[R] m)) = 0 :=
  let := f.toAlgebra
  fun X m ↦ (Module.Descent.amitsurDiff₀_eq_zero_iff _).2 (h X m)

/-- The `R`-linear map `F X ⟶ G X` whose base change is the component `θ_X`. -/
noncomputable def descendHomOfFaithfullyFlat (X : 𝒞) : F.obj X ⟶ G.obj X :=
  letI := f.toAlgebra
  haveI : Module.FaithfullyFlat R C := hf
  ofHom (Module.Descent.existsUnique_baseChange_eq (θ.hom.app X).hom (hθ X)).exists.choose

/-- The base change of `descendHomOfFaithfullyFlat` is the component of `θ`. -/
theorem extendScalars_map_descendHomOfFaithfullyFlat (X : 𝒞) :
    (extendScalars f).map (descendHomOfFaithfullyFlat f hf θ hθ X) = θ.hom.app X := by
  let := f.toAlgebra
  have : Module.FaithfullyFlat R C := hf
  exact ModuleCat.hom_ext
    (Module.Descent.existsUnique_baseChange_eq (θ.hom.app X).hom (hθ X)).exists.choose_spec

/-- `descendHomOfFaithfullyFlat` is bijective: its base change along the faithfully flat `f` is the
isomorphism `θ_X`, and base change along a faithfully flat ring map reflects bijectivity. -/
theorem bijective_descendHomOfFaithfullyFlat (X : 𝒞) :
    Function.Bijective (descendHomOfFaithfullyFlat f hf θ hθ X) := by
  let := f.toAlgebra
  have : Module.FaithfullyFlat R C := hf
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective R C]
  have h := ConcreteCategory.bijective_of_isIso (θ.hom.app X)
  rwa [← extendScalars_map_descendHomOfFaithfullyFlat f hf θ hθ X] at h

/-- **Descent of an isomorphism of module-valued functors along a faithfully flat ring map.**
Let `f : R →+* C` be faithfully flat and `θ : F ⋙ extendScalars f ≅ G ⋙ extendScalars f` an
isomorphism whose components send each `1 ⊗ m` into the kernel of the degree-zero Amitsur
differential (the descent compatibility of `θ` over `C ⊗_R C`).  Then `θ` is the base change of
an isomorphism `F ≅ G` (`ModuleCat.extendScalars_map_descendIso_hom_app`). -/
noncomputable def descendIsoOfFaithfullyFlat : F ≅ G :=
  NatIso.ofComponents (fun X ↦ (LinearEquiv.ofBijective _
      (bijective_descendHomOfFaithfullyFlat f hf θ hθ X)).toModuleIso)
    fun {X Y} φ ↦ extendScalars_map_injective_of_faithfullyFlat f hf (by
      change (extendScalars f).map (F.map φ ≫ descendHomOfFaithfullyFlat f hf θ hθ Y) =
        (extendScalars f).map (descendHomOfFaithfullyFlat f hf θ hθ X ≫ G.map φ)
      rw [Functor.map_comp, Functor.map_comp, extendScalars_map_descendHomOfFaithfullyFlat,
        extendScalars_map_descendHomOfFaithfullyFlat]
      exact θ.hom.naturality φ)

/-- The component of `descendIsoOfFaithfullyFlat` at `X` is `descendHomOfFaithfullyFlat` at `X`. -/
theorem descendIsoOfFaithfullyFlat_hom_app (X : 𝒞) :
    (descendIsoOfFaithfullyFlat f hf θ hθ).hom.app X = descendHomOfFaithfullyFlat f hf θ hθ X :=
  rfl

/-- The base change of `descendIsoOfFaithfullyFlat` is `θ`. -/
theorem extendScalars_map_descendIso_hom_app (X : 𝒞) :
    (extendScalars f).map ((descendIsoOfFaithfullyFlat f hf θ hθ).hom.app X) = θ.hom.app X :=
  extendScalars_map_descendHomOfFaithfullyFlat f hf θ hθ X

open Functor.LaxMonoidal in
/-- **The descended isomorphism is monoidal when `θ` is.**  If `F` and `G` are monoidal and
`θ` is an isomorphism of monoidal functors, then so is `descendIsoOfFaithfullyFlat`: both
conditions hold after the faithful monoidal functor `extendScalars f`. -/
theorem isMonoidal_descendIsoOfFaithfullyFlat [MonoidalCategory 𝒞] [F.Monoidal] [G.Monoidal]
    [NatTrans.IsMonoidal θ.hom] :
    NatTrans.IsMonoidal (descendIsoOfFaithfullyFlat f hf θ hθ).hom where
  unit := extendScalars_map_injective_of_faithfullyFlat f hf (by
    rw [Functor.map_comp, extendScalars_map_descendIso_hom_app]
    have h := NatTrans.IsMonoidal.unit (τ := θ.hom)
    rw [comp_ε, comp_ε, Category.assoc] at h
    exact (cancel_epi (ε (extendScalars f))).1 h)
  tensor X Y := extendScalars_map_injective_of_faithfullyFlat f hf (by
    have h := NatTrans.IsMonoidal.tensor (τ := θ.hom) X Y
    rw [comp_μ, comp_μ, ← extendScalars_map_descendIso_hom_app f hf θ hθ (X ⊗ Y),
      ← extendScalars_map_descendIso_hom_app f hf θ hθ X,
      ← extendScalars_map_descendIso_hom_app f hf θ hθ Y, Category.assoc,
      ← Category.assoc (_ ⊗ₘ _), μ_natural, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp] at h
    exact (cancel_epi _).1 h)

end ModuleCat
