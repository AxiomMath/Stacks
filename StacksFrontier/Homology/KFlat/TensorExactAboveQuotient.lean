module

public import StacksFrontier.Homology.KFlat.TensorExactAbove

/-!
# K-flatness from exactness of the tensor products with cyclic modules in high degrees

Let `C` be a cochain complex of flat `R`-modules and `m` an integer such that, for every ideal
`I` of `R`, the termwise tensor product `C ⊗_R R/I` is exact in every degree `> m`. Then `C` is
K-flat. This sharpens `CochainComplex.KFlat.kFlat_of_rTensor_exact`, which asks for the
exactness of `C ⊗_R M` for every `R`-module `M`: flatness of a module is detected by its tensor
products with the inclusions of ideals (`Module.Flat.iff_lTensor_injective'`), and in the
dimension-shifting step of that proof the test module is then the cyclic module `R/I`.

The sharpening matters when the complexes `C ⊗_R M` are only accessible for `M` in a restricted
class: for the Čech complex of the structure sheaf of an algebraic space over `Spec R`, the
complex `C ⊗_R R/I` is the Čech complex of the closed fibre over `Spec R/I`, whereas `C ⊗_R M`
for an arbitrary `M` has no such reading inside a fixed big site.

## Main results

* `CochainComplex.KFlat.flat_quotient_of_rTensor_quotient_subtype_injective`: the cokernel of a
  submodule of a flat module is flat once the inclusion stays injective after tensoring with every
  cyclic module.
* `CochainComplex.KFlat.kFlat_of_rTensor_quotient_exact`: the K-flatness criterion.

No declaration of this file carries a `stacks` attribute.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CochainComplex.KFlat

variable {R : Type u} [CommRing R]

/-- **The cokernel of a submodule of a flat module is flat** once the inclusion of the submodule
stays injective after tensoring with every cyclic module `R/I`. -/
theorem flat_quotient_of_rTensor_quotient_subtype_injective {D : Type u} [AddCommGroup D]
    [Module R D] (Z : Submodule R D) [Module.Flat R D]
    (hinj : ∀ I : Ideal R, Function.Injective (LinearMap.rTensor (R ⧸ I) Z.subtype)) :
    Module.Flat R (D ⧸ Z) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have h := hinj I
  rw [← Submodule.range_subtype I] at h
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (LinearMap.exact_subtype_mkQ Z)
    (Submodule.mkQ_surjective Z)
    (LinearMap.exact_map_mkQ_range I.subtype)
    (Submodule.mkQ_surjective (LinearMap.range I.subtype))
    h
    (Module.Flat.lTensor_preserves_injective_linearMap I.subtype I.injective_subtype)

/-- A submodule equal to the kernel of a surjection between flat modules is flat. -/
private theorem flat_of_eq_ker_of_surjective {A B : Type u} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Flat R A] [Module.Flat R B] (f : A →ₗ[R] B)
    (hf : Function.Surjective f) (N : Submodule R A) (h : N = LinearMap.ker f) :
    Module.Flat R N := by
  have := flat_ker_of_surjective f hf
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofEq _ _ h)

/-- **The cycles are flat**, from exactness of `C ⊗ R/I` at `k` for every ideal `I`. -/
theorem flat_cycles_of_rTensor_quotient_exact (C : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Flat R (C.X i)] (k : ℤ)
    (hk : ∀ I : Ideal R, Function.Exact (LinearMap.rTensor (R ⧸ I) (C.d (k - 1) k).hom)
        (LinearMap.rTensor (R ⧸ I) (C.d k (k + 1)).hom)) :
    Module.Flat R (C.cycles k) := by
  set g := (C.d k (k + 1)).hom with hg
  have hinj : ∀ I : Ideal R,
      Function.Injective (LinearMap.rTensor (R ⧸ I) (LinearMap.range g).subtype) := by
    intro I
    refine StacksDraft.TorAmplitude.Termwise.rTensor_range_subtype_injective_of_exact
      (C.d (k - 1) k).hom g ?_ (R ⧸ I) (hk I)
    rw [hg, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero]
  have hQ : Module.Flat R ((C.X (k + 1) : Type u) ⧸ LinearMap.range g) :=
    flat_quotient_of_rTensor_quotient_subtype_injective (LinearMap.range g) hinj
  have hrange : Module.Flat R (LinearMap.range g) :=
    flat_of_eq_ker_of_surjective (LinearMap.range g).mkQ (Submodule.mkQ_surjective _) _
      (Submodule.ker_mkQ _).symm
  have hker : Module.Flat R (LinearMap.ker g) :=
    flat_of_eq_ker_of_surjective g.rangeRestrict g.surjective_rangeRestrict _
      (LinearMap.ker_rangeRestrict g).symm
  let e : C.cycles k ≅ ModuleCat.of R (LinearMap.ker g) :=
    (C.cyclesIsKernel k (k + 1) (by simp)).conePointUniqueUpToIso (kernelIsKernel _) ≪≫
      ModuleCat.kernelIsoKer (C.d k (k + 1))
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- **K-flatness from exactness of the tensor products with cyclic modules in high degrees.** A
complex `C` of flat `R`-modules such that `C ⊗_R R/I` is exact in every degree `> m`, for every
ideal `I` of `R`, is K-flat: it is the colimit of its good truncations `τ_{≤ k} C`, `k > m`,
which are bounded above with flat terms. -/
theorem kFlat_of_rTensor_quotient_exact (C : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Flat R (C.X i)] (m : ℤ)
    (hC : ∀ (I : Ideal R) (k : ℤ), m < k →
      Function.Exact (LinearMap.rTensor (R ⧸ I) (C.d (k - 1) k).hom)
        (LinearMap.rTensor (R ⧸ I) (C.d k (k + 1)).hom)) :
    C.KFlat := by
  have hseq : ∀ k : ℕ, ((truncLEFromSequence C (m + 1)).obj k).KFlat := by
    intro k
    show (C.truncLE (m + 1 + k)).KFlat
    have := flat_cycles_of_rTensor_quotient_exact C (m + 1 + k)
      (fun I => hC I (m + 1 + k) (by omega))
    have : ∀ i, Module.Flat R ((C.truncLE (m + 1 + k)).X i) :=
      flat_truncLE_X C (m + 1 + k)
    exact kFlat_of_flat (C.truncLE (m + 1 + k)) (m + 1 + k)
  exact kFlat_of_iso ((colimit.isColimit _).coconePointUniqueUpToIso
    (truncLEFromCocone_isColimit C (m + 1))) (kFlat_colimit.{u, 0, 0, u} _ hseq)

end CochainComplex.KFlat

end
