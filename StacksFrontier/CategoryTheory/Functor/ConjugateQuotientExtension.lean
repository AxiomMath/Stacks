module

public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotient
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.Opposite

/-!
# Extending a quotient along a left adjoint whose counit is invertible

Let `L ⊣ R` be an adjunction between abelian categories, with `L : C ⥤ D` preserving
monomorphisms, let `M` be an object of `C` and let `e : L M ≅ N` identify `L M` with an object
`N` of `D`.  Given a quotient `N ⟶ N/K` of `N`, its adjoint transpose is a morphism
`φ : M ⟶ R(N/K)`, and the image of `φ` is a quotient of `M`: the quotient by the kernel `K₀`
of `φ`.  If the counit `L R (N/K) ⟶ N/K` is invertible, this quotient extends the given one:
applying `L` to `M ⟶ M/K₀` and reading the source through `e` gives back the kernel `K`.

## Main definitions

* `CategoryTheory.Adjunction.extensionMap`: the adjoint transpose `M ⟶ R(N/K)` of the projection
  `L M ≅ N ⟶ N/K`.
* `CategoryTheory.Adjunction.extensionKernel`: the kernel `K₀` of that transpose, read on its
  factorisation through its image.
* `CategoryTheory.Adjunction.extensionQuotientIso`: the quotient `M/K₀` is the image of the
  transpose.

## Main results

* `CategoryTheory.Adjunction.kernelSubobject_extensionKernel`: if `L` preserves monomorphisms
  and the counit is invertible at `N/K`, the kernel of `L M ≅ N ⟶ ... ⟶ L(M/K₀)`, read through
  `e`, is `K`.
* `CategoryTheory.Adjunction.extensionKernel_eq_kernelSubobject`: `K₀` is the kernel subobject
  of the transpose itself.
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {C : Type*} {D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {M : C} {N : D} (e : L.obj M ≅ N) (K : Subobject N)

/-- The adjoint transpose `M ⟶ R(N/K)` of the projection `L M ≅ N ⟶ N/K` of `L M` onto the
quotient of `N` by `K`. -/
noncomputable def extensionMap : M ⟶ R.obj (cokernel K.arrow) :=
  adj.homEquiv _ _ (e.hom ≫ cokernel.π K.arrow)

/-- The extension of the quotient `N/K` of `N ≅ L M` to a quotient of `M`, recorded by its
kernel: the kernel of the factorisation of `CategoryTheory.Adjunction.extensionMap` through its
image, which is the kernel of the transpose itself
(`CategoryTheory.Adjunction.extensionKernel_eq_kernelSubobject`). -/
noncomputable def extensionKernel : Subobject M :=
  kernelSubobject (factorThruImage (adj.extensionMap e K))

/-- The kernel of the factorisation through the image is the kernel of the transpose. -/
theorem extensionKernel_eq_kernelSubobject :
    adj.extensionKernel e K = kernelSubobject (adj.extensionMap e K) :=
  (kernelSubobject_eq_of_comp_mono _ _ (image.ι (adj.extensionMap e K))
    (image.fac (adj.extensionMap e K))).symm

/-- **The extended quotient is the image of the transpose.** -/
noncomputable def extensionQuotientIso :
    cokernel (adj.extensionKernel e K).arrow ≅ image (adj.extensionMap e K) :=
  Abelian.cokernelKernelSubobjectIso (factorThruImage (adj.extensionMap e K))

/-- The projection onto the extended quotient, read through
`CategoryTheory.Adjunction.extensionQuotientIso`, is the factorisation of the transpose through
its image. -/
theorem cokernel_π_extensionQuotientIso_hom :
    cokernel.π (adj.extensionKernel e K).arrow ≫ (adj.extensionQuotientIso e K).hom =
      factorThruImage (adj.extensionMap e K) :=
  (Iso.eq_comp_inv _).1
    (Abelian.cokernelKernelSubobjectIso_inv_comp (factorThruImage (adj.extensionMap e K))).symm

/-- The embedding of the extended quotient into `R(N/K)`: the isomorphism with the image followed
by the inclusion of the image. -/
noncomputable def extensionQuotientι :
    cokernel (adj.extensionKernel e K).arrow ⟶ R.obj (cokernel K.arrow) :=
  (adj.extensionQuotientIso e K).hom ≫ image.ι (adj.extensionMap e K)

/-- The embedding of the extended quotient into `R(N/K)` is a monomorphism. -/
instance mono_extensionQuotientι : Mono (adj.extensionQuotientι e K) :=
  mono_comp _ _

/-- The projection onto the extended quotient followed by its embedding into `R(N/K)` is the
transpose. -/
theorem cokernel_π_extensionQuotientι :
    cokernel.π (adj.extensionKernel e K).arrow ≫ adj.extensionQuotientι e K =
      adj.extensionMap e K := by
  rw [extensionQuotientι, ← Category.assoc, cokernel_π_extensionQuotientIso_hom, image.fac]

/-- **The extended quotient restricts to the given one.**  If `L` preserves monomorphisms and
the counit of `L ⊣ R` is invertible at `N/K`, then the kernel of the projection
`N ≅ L M ⟶ L(M/K₀)` is `K`. -/
theorem kernelSubobject_extensionKernel [L.PreservesMonomorphisms]
    [IsIso (adj.counit.app (cokernel K.arrow))] :
    kernelSubobject (e.inv ≫ L.map (cokernel.π (adj.extensionKernel e K).arrow)) = K := by
  have hfac : (e.inv ≫ L.map (cokernel.π (adj.extensionKernel e K).arrow)) ≫
      (L.map (adj.extensionQuotientι e K) ≫ adj.counit.app (cokernel K.arrow)) =
      cokernel.π K.arrow := by
    rw [Category.assoc, ← Category.assoc (L.map _), ← L.map_comp,
      cokernel_π_extensionQuotientι, extensionMap,
      ← homEquiv_counit adj (g := adj.homEquiv _ _ (e.hom ≫ cokernel.π K.arrow)),
      Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
  rw [← kernelSubobject_eq_of_comp_mono _ _ _ hfac, kernelSubobject_cokernel_π]

end CategoryTheory.Adjunction

end
