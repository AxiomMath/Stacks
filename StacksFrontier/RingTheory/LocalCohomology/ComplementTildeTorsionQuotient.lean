module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PrincipalFactorization
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# Killing a scalar on the complement of a zero locus

Let `A` be a commutative ring, `I ⊆ A` an ideal, `U = Spec A ∖ V(I)` and `f ∈ A`. If `f` acts as
zero on `M_𝔭` for every prime `𝔭 ∈ U`, then the quotient map `M ⟶ M/fM` becomes an isomorphism
after passing to quasi-coherent modules on `U`: the module `M̃|_U` does not see the difference
between `M` and `M/fM`.

The proof is the exactness of `M ↦ M̃|_U`. That functor is a composite of two left adjoints —
the associated-sheaf functor on `Spec A` and restriction along the open immersion `U ⟶ Spec A` —
so it preserves finite colimits, and `M/fM` is the cokernel of multiplication by `f` on `M`.
The hypothesis says precisely that multiplication by `f` becomes the zero endomorphism of
`M̃|_U`, and the cokernel of a zero morphism is its target.

Two forms of the hypothesis are provided and are proved to be interchangeable. The pointwise one
asks that the image of `f` in `A_𝔭` kill `M_𝔭` for every `𝔭 ∈ U`; the global one asks that
`Stacks.Coherent.mulSection` of the image of `f` in `Γ(U, 𝒪_U)` vanish on `M̃|_U`, the image
being taken along `Stacks.LocalCohomology.complementTopSectionsRingHom`, the structure map of `U`
as a scheme over `Spec A`.

## Main definitions

* `Stacks.LocalCohomology.complementTildeFunctor` — the functor `M ↦ M̃|_U`, whose value on
  objects is `Stacks.LocalCohomology.complementTilde`.
* `Stacks.LocalCohomology.complementTopSectionsRingHom` — the canonical ring map
  `A →+* Γ(U, 𝒪_U)`.

## Main results

* `Stacks.LocalCohomology.mulSection_complementTopSectionsRingHom` — multiplication by the image of
  `f` in `Γ(U, 𝒪_U)` is the restriction to `U` of the associated sheaf of multiplication by `f`.
* `Stacks.LocalCohomology.nonempty_iso_complementTilde_quotient_smul` — if `f` kills `M_𝔭` for
  every prime `𝔭` not containing `I`, then `M̃|_U ≅ (M/fM)̃|_U`.
* `Stacks.LocalCohomology.nonempty_iso_complementTilde_quotient_smul_of_mulSection_eq_zero` — the
  same conclusion from the vanishing of multiplication by `f` as an endomorphism of `M̃|_U`.

## References

* [Stacks Project, Tag 0EKZ](https://stacks.math.columbia.edu/tag/0EKZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Pointwise

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- The functor sending an `A`-module `M` to the restriction of `M̃` to `U = Spec A ∖ V(I)`: the
associated-sheaf functor on `Spec A` followed by restriction along the open immersion
`U ⟶ Spec A`. -/
def complementTildeFunctor (A : Type u) [CommRing A] (I : Ideal A) :
    ModuleCat.{u} A ⥤ (complementZeroLocus A I : Scheme).Modules :=
  AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙
    Scheme.Modules.restrictFunctor (complementZeroLocus A I).ι

/-- On objects `Stacks.LocalCohomology.complementTildeFunctor` is
`Stacks.LocalCohomology.complementTilde`. -/
theorem complementTildeFunctor_obj (I : Ideal A) (M : ModuleCat.{u} A) :
    (complementTildeFunctor A I).obj M = complementTilde A I M := rfl

/-- The functor `M ↦ M̃|_U` preserves finite colimits, being a composite of two left adjoints. -/
instance preservesFiniteColimits_complementTildeFunctor (I : Ideal A) :
    PreservesFiniteColimits (complementTildeFunctor A I) :=
  haveI := Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of A)
  inferInstanceAs (PreservesFiniteColimits
    (AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙
      Scheme.Modules.restrictFunctor (complementZeroLocus A I).ι))

/-- The canonical ring map from `A` to the global sections of the structure sheaf of
`U = Spec A ∖ V(I)`, namely the map on global sections induced by the structure morphism
`U ⟶ Spec A` composed with the identification of `A` with `Γ(Spec A, 𝒪)`.

This is the same ring map as `Stacks.LocalCohomology.complementSectionsRingHom`, which reads its
target as the sections of the structure sheaf of `Spec A` over the open `U` rather than as the
global sections of the structure sheaf of the open subscheme; the two spellings of that ring are
not interchangeable for the elaborator, and multiplication by a global section
(`Stacks.Coherent.mulSection`) asks for the second. -/
def complementTopSectionsRingHom (I : Ideal A) :
    A →+* (complementZeroLocus A I : Scheme).presheaf.obj (op ⊤) :=
  ((complementZeroLocus A I).ι.appTop.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- A prime in the complement of the zero locus of `I` does not contain `I`. -/
theorem not_le_of_mem_complementZeroLocus (I : Ideal A) {p : PrimeSpectrum A}
    (hp : p ∈ complementZeroLocus A I) : ¬ I ≤ p.asIdeal :=
  fun h => hp ((PrimeSpectrum.mem_zeroLocus _ _).2 h)

/-- Multiplication by `f` on a localization of `M` is the localization of multiplication by `f`
on `M`. -/
private theorem isLocalizedModule_map_smul_id (f : A) (M : ModuleCat.{u} A)
    (p : PrimeSpectrum A) (z : LocalizedModule p.asIdeal.primeCompl (M : Type u)) :
    IsLocalizedModule.map p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (M : Type u))
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (M : Type u))
      (f • (LinearMap.id : (M : Type u) →ₗ[A] M)) z = f • z := by
  rw [map_smul, IsLocalizedModule.map_id]
  rfl

/-- **Multiplication by a scalar is the tilde of multiplication by that scalar.** The
endomorphism `Stacks.Coherent.mulSection` of `M̃|_U` given by the image of `f` in `Γ(U, 𝒪_U)` is
the restriction to `U` of the associated sheaf of multiplication by `f` on `M`. -/
theorem mulSection_complementTopSectionsRingHom (I : Ideal A) (f : A) (M : ModuleCat.{u} A) :
    Stacks.Coherent.mulSection (complementTopSectionsRingHom I f)
        ((complementTildeFunctor A I).obj M) =
      (complementTildeFunctor A I).map
        (ModuleCat.ofHom (f • (LinearMap.id : (M : Type u) →ₗ[A] M))) := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  rw [Stacks.Coherent.mulSection_app]
  have hinv : ∀ (r : (complementZeroLocus A I : Scheme).presheaf.obj (op V)),
      ((complementZeroLocus A I).ι.appIso V).inv r = r := by
    rw [Scheme.Opens.ι_appIso]
    intro r
    rfl
  have main : ∀ (r : (complementZeroLocus A I : Scheme).presheaf.obj (op V))
      (z : Γ((complementTildeFunctor A I).obj M, V)),
      r • z = ((((complementZeroLocus A I).ι.appIso V).inv r) •
        (((AlgebraicGeometry.tilde M).restrictAppIso (complementZeroLocus A I).ι V).hom z)
          : Γ(AlgebraicGeometry.tilde M, (complementZeroLocus A I).ι ''ᵁ V)) := fun _ _ => rfl
  rw [main, hinv]
  refine Subtype.ext (funext fun y => ?_)
  refine Eq.trans ?_ (isLocalizedModule_map_smul_id f M y.1 _).symm
  exact IsScalarTower.algebraMap_smul
    (LocalizedModule y.1.asIdeal.primeCompl A) f _

/-- If `f` kills every localization of `M` at a prime of `U`, then multiplication by `f` is the
zero endomorphism of `M̃|_U`. -/
private theorem complementTildeFunctor_map_smul_id_eq_zero (I : Ideal A) (f : A)
    (M : ModuleCat.{u} A)
    (hM : ∀ p : PrimeSpectrum A, p ∈ complementZeroLocus A I →
      ∀ z : LocalizedModule p.asIdeal.primeCompl (M : Type u), f • z = 0) :
    (complementTildeFunctor A I).map
      (ModuleCat.ofHom (f • (LinearMap.id : (M : Type u) →ₗ[A] M))) = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  refine Subtype.ext (funext fun y => ?_)
  exact (isLocalizedModule_map_smul_id f M y.1 _).trans
    (hM y.1 ((complementZeroLocus A I).ι_image_le V y.2) _)

/-- The range of multiplication by `f` on `M` is the submodule `f • M`. -/
private theorem range_smul_id (f : A) (M : ModuleCat.{u} A) :
    LinearMap.range (f • (LinearMap.id : (M : Type u) →ₗ[A] M)) =
      f • (⊤ : Submodule A (M : Type u)) := by
  rw [Submodule.pointwise_smul_def, Submodule.map_top]
  rfl

/-- The cokernel of multiplication by `f` on `M` is `M/fM`. -/
private def cokernelSmulIdIso (f : A) (M : ModuleCat.{u} A) :
    cokernel (ModuleCat.ofHom (f • (LinearMap.id : (M : Type u) →ₗ[A] M))) ≅
      ModuleCat.of A ((M : Type u) ⧸ (f • (⊤ : Submodule A (M : Type u)))) :=
  ModuleCat.cokernelIsoRangeQuotient _ ≪≫
    (Submodule.quotEquivOfEq _ _ (range_smul_id f M)).toModuleIso

/-- If multiplication by `f` vanishes on `M̃|_U`, then `M ⟶ M/fM` becomes an isomorphism on
`U`. -/
private theorem nonempty_iso_of_map_smul_id_eq_zero (I : Ideal A) (f : A) (M : ModuleCat.{u} A)
    (h : (complementTildeFunctor A I).map
      (ModuleCat.ofHom (f • (LinearMap.id : (M : Type u) →ₗ[A] M))) = 0) :
    Nonempty ((complementTildeFunctor A I).obj M ≅
      (complementTildeFunctor A I).obj
        (ModuleCat.of A ((M : Type u) ⧸ (f • (⊤ : Submodule A (M : Type u)))))) :=
  ⟨cokernelZeroIsoTarget.symm ≪≫ cokernelIsoOfEq h.symm ≪≫
    (PreservesCokernel.iso (complementTildeFunctor A I) _).symm ≪≫
      (complementTildeFunctor A I).mapIso (cokernelSmulIdIso f M)⟩

/-- **A module on the punctured spectrum killed by `f` is the restriction of a module killed by
`f`.** If `f` acts as zero on `M_𝔭` for every prime `𝔭` not containing `I`, then the quotient map
`M ⟶ M/fM` induces an isomorphism of the associated sheaves restricted to
`U = Spec A ∖ V(I)`. -/
theorem nonempty_iso_complementTilde_quotient_smul
    (I : Ideal A) (f : A) (M : ModuleCat.{u} A)
    (hM : ∀ (p : PrimeSpectrum A), ¬ I ≤ p.asIdeal →
      ∀ x : LocalizedModule p.asIdeal.primeCompl (M : Type u),
        (algebraMap A (Localization.AtPrime p.asIdeal) f) • x = 0) :
    Nonempty (complementTilde A I M ≅
      complementTilde A I (ModuleCat.of A ((M : Type u) ⧸ (f • (⊤ : Submodule A (M : Type u)))))) :=
  nonempty_iso_of_map_smul_id_eq_zero I f M
    (complementTildeFunctor_map_smul_id_eq_zero I f M fun p hp z =>
      (IsScalarTower.algebraMap_smul (Localization.AtPrime p.asIdeal) f z).symm.trans
        (hM p (not_le_of_mem_complementZeroLocus I hp) z))

/-- **A module on the punctured spectrum killed by `f` is the restriction of a module killed by
`f`.** If multiplication by the image of `f` in `Γ(U, 𝒪_U)` is the zero endomorphism of `M̃|_U`,
then the quotient map `M ⟶ M/fM` induces an isomorphism of the associated sheaves restricted to
`U = Spec A ∖ V(I)`. -/
theorem nonempty_iso_complementTilde_quotient_smul_of_mulSection_eq_zero
    (I : Ideal A) (f : A) (M : ModuleCat.{u} A)
    (hzero : Stacks.Coherent.mulSection (complementTopSectionsRingHom I f) (complementTilde A I M) =
      (0 : complementTilde A I M ⟶ complementTilde A I M)) :
    Nonempty (complementTilde A I M ≅
      complementTilde A I (ModuleCat.of A ((M : Type u) ⧸ (f • (⊤ : Submodule A (M : Type u)))))) :=
  nonempty_iso_of_map_smul_id_eq_zero I f M
    ((mulSection_complementTopSectionsRingHom I f M).symm.trans hzero)

end Stacks.LocalCohomology

end
