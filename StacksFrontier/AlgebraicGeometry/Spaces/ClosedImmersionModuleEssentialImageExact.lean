module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExact

/-!
# Modules supported on a closed subspace which are built from direct images

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`.  The existence
assertion of **Stacks 07U0** says that a module `F` on `X` whose scheme-theoretic support lies in
`Z` is a direct image: there is a module `G` on `Z` with `i_*G ≅ F`.  Equivalently, `F` lies in
the essential image of `i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)`.

This file determines how much of that essential image is reachable from the two unconditional
facts now available about `i_*`:

* it is **fully faithful** — Stacks 04CJ, part (2), as
  `AlgebraicGeometry.Space.fullyFaithfulModulePushforward`;
* it is **exact** (its right-exactness half is the new input) — in `AlgebraicGeometry.Space`,
  `exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity`.

Together they make the essential image a subcategory closed under finite limits and finite
colimits: for a morphism `φ : M ⟶ N` between modules that are direct images, the kernel, the
cokernel and the image of `φ` are direct images again.  So the existence assertion of Stacks 07U0
holds for every module obtained from direct images by these operations, and that is what is
proved here.

## Main results

* `AlgebraicGeometry.Space.essImage_modulePushforward_cokernel_map` and
  `AlgebraicGeometry.Space.essImage_modulePushforward_kernel_map`: the cokernel, resp. the
  kernel, of the direct image of a morphism of `𝒪_Z`-modules is a direct image.
* `AlgebraicGeometry.Space.essImage_modulePushforward_cokernel`,
  `AlgebraicGeometry.Space.essImage_modulePushforward_kernel` and
  `AlgebraicGeometry.Space.essImage_modulePushforward_image`: the cokernel, kernel and image of a
  morphism between two modules lying in the essential image of `i_*` lie in it again.
* `AlgebraicGeometry.Space.exists_modulePushforward_iso_of_cokernel`: a module isomorphic to the
  cokernel of a morphism between direct images is itself a direct image.

## Implementation notes

**What this file proves, and what proves more.**  The general existence assertion of Stacks 07U0
is not proved here, but it is proved in this tree, unconditionally: the essential-image assertion
of **Stacks 04E5, part (2)** — equivalently of Stacks 04CJ, part (3) — is
`AlgebraicGeometry.Space.essImage_modulePushforward_of_annihilatedByKerIdeal` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleEssentialImage.lean`, proved
fibrewise rather than through the topos theory, and its quasi-coherent refinement is
`AlgebraicGeometry.Space.isQuasicoherentEssImagePushforward_of_isClosedImmersion`, which makes
`AlgebraicGeometry.Space.exists_module_on_schemeTheoreticSupport` unconditional.  So the results
below are subsumed for the modules they are about; they are kept because they reach the
essential image from full faithfulness and exactness alone, with no fibrewise input, and because
they are stated for cokernels, kernels and images rather than for annihilated modules.

**Why the counit isomorphism does not give the existence assertion.**  The
`AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit` and
`AlgebraicGeometry.Space.modulePullbackCounitIso` invert the counit `i^*i_*G ⟶ G`, whose source
and target are modules on `Z`.  The map that must be inverted to produce `G` from `F` is the
*unit* `F ⟶ i_*i^*F`, whose invertibility at `F` is equivalent to `F` lying in the essential
image (`CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage`, used below).  The counit
isomorphism says only that `i_*` is fully faithful, which fixes `G` once it exists.

**Why the closure stops at finite colimits.**  The essential image is *not* closed under
extensions, so the dévissage of a coherent module cannot be completed by these means.  For
`X = Spec k[t]/t²` and `Z = Spec k` the sequence `0 → i_*𝒪_Z → 𝒪_X → i_*𝒪_Z → 0` has both ends in
the essential image while `𝒪_X` is not annihilated by the defining ideal `(t)`, hence by
`AlgebraicGeometry.Space.annihilatedByKerIdeal_of_essImage_modulePushforward` is not in the
essential image.  Formally the obstruction appears as the left exactness of `i^*`, which is not
available: right exactness of `i_* i^*` gives that the unit at the middle term is an epimorphism,
and nothing gives that it is a monomorphism.

## References

* [Stacks Project, Lemma 67.15.3 (Tag 07U0)](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS}

/-- **The cokernel of a direct image is a direct image.**  For a closed immersion `i : Z ⟶ X` of
algebraic spaces and a morphism `φ` of `𝒪_Z`-modules, `coker(i_*φ)` lies in the essential image
of `i_*`, being `i_*(coker φ)`.

This is right exactness of `i_*`, in the form
`AlgebraicGeometry.Space.modulePushforwardCokernelIso`. -/
theorem essImage_modulePushforward_cokernel_map (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) :
    (modulePushforward B S hS i).essImage
      (cokernel (C := Modules.{u, u} B S hS X.1 X.2) ((modulePushforward B S hS i).map φ)) :=
  ⟨cokernel (C := Modules.{u, u} B S hS Z.1 Z.2) φ,
    ⟨(modulePushforwardCokernelIso B S hS i hi φ).symm⟩⟩

/-- **The kernel of a direct image is a direct image.**  For a morphism `φ` of `𝒪_Z`-modules,
`ker(i_*φ)` lies in the essential image of `i_*`, being `i_*(ker φ)`.

No hypothesis on `i` is needed: `i_*` is the right adjoint of the adjunction of Stacks 03LU, so
it preserves all limits. -/
theorem essImage_modulePushforward_kernel_map (i : Z ⟶ X)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N) :
    (modulePushforward B S hS i).essImage
      (kernel (C := Modules.{u, u} B S hS X.1 X.2) ((modulePushforward B S hS i).map φ)) :=
  have : PreservesLimits (modulePushforward B S hS i) :=
    (modulePullbackAdjunction B S hS i).rightAdjoint_preservesLimits
  ⟨kernel (C := Modules.{u, u} B S hS Z.1 Z.2) φ,
    ⟨PreservesKernel.iso (modulePushforward B S hS i) φ⟩⟩

/-- A morphism between direct images is, read through the chosen isomorphisms, the direct image
of a morphism of the witnesses, by full faithfulness. -/
private theorem exists_modulePushforward_map_eq_of_essImage (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {M N : Modules.{u, u} B S hS X.1 X.2}
    (hM : (modulePushforward B S hS i).essImage M)
    (hN : (modulePushforward B S hS i).essImage N) (φ : M ⟶ N) :
    ∃ φ' : hM.witness ⟶ hN.witness,
      (modulePushforward B S hS i).map φ' = hM.getIso.hom ≫ φ ≫ hN.getIso.inv :=
  have hff := fullyFaithfulModulePushforward B S hS i hi
  ⟨hff.preimage _, hff.map_preimage _⟩

/-- **The essential image of the direct image along a closed immersion is closed under
cokernels.**  If two `𝒪_X`-modules `M` and `N` are direct images along `i`, then so is the
cokernel of any morphism `M ⟶ N`.

By full faithfulness (Stacks 04CJ, part (2)) the morphism, read through the chosen isomorphisms,
is the direct image of a morphism of `𝒪_Z`-modules, and the cokernel of that direct image is one
by `AlgebraicGeometry.Space.essImage_modulePushforward_cokernel_map`. -/
theorem essImage_modulePushforward_cokernel (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {M N : Modules.{u, u} B S hS X.1 X.2}
    (hM : (modulePushforward B S hS i).essImage M)
    (hN : (modulePushforward B S hS i).essImage N) (φ : M ⟶ N) :
    (modulePushforward B S hS i).essImage (cokernel φ) := by
  obtain ⟨φ', hφ'⟩ := exists_modulePushforward_map_eq_of_essImage B S hS i hi hM hN φ
  refine Functor.essImage.ofIso
    (cokernel.mapIso (f := (modulePushforward B S hS i).map φ') φ hM.getIso hN.getIso ?_)
    (essImage_modulePushforward_cokernel_map B S hS i hi φ')
  rw [hφ']
  simp

/-- **The essential image of the direct image along a closed immersion is closed under
kernels.**  If two `𝒪_X`-modules `M` and `N` are direct images along `i`, then so is the kernel
of any morphism `M ⟶ N`.

The argument is that of the cokernel statement, with left exactness — preservation of limits by
a right adjoint — in place of right exactness. -/
theorem essImage_modulePushforward_kernel (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {M N : Modules.{u, u} B S hS X.1 X.2}
    (hM : (modulePushforward B S hS i).essImage M)
    (hN : (modulePushforward B S hS i).essImage N) (φ : M ⟶ N) :
    (modulePushforward B S hS i).essImage (kernel φ) := by
  obtain ⟨φ', hφ'⟩ := exists_modulePushforward_map_eq_of_essImage B S hS i hi hM hN φ
  refine Functor.essImage.ofIso
    (kernel.mapIso (f := (modulePushforward B S hS i).map φ') φ hM.getIso hN.getIso ?_)
    (essImage_modulePushforward_kernel_map B S hS i φ')
  rw [hφ']
  simp

/-- **The essential image of the direct image along a closed immersion is closed under images.**
The image `ker(N ⟶ coker φ)` of a morphism `φ : M ⟶ N` between `𝒪_X`-modules that are direct
images along `i` is a direct image again.

The cokernel is one by the cokernel statement, and the kernel of the projection `N ⟶ coker φ` is
one by the kernel statement. -/
theorem essImage_modulePushforward_image (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {M N : Modules.{u, u} B S hS X.1 X.2}
    (hM : (modulePushforward B S hS i).essImage M)
    (hN : (modulePushforward B S hS i).essImage N) (φ : M ⟶ N) :
    (modulePushforward B S hS i).essImage (kernel (cokernel.π φ)) :=
  essImage_modulePushforward_kernel B S hS i hi hN
    (essImage_modulePushforward_cokernel B S hS i hi hM hN φ) (cokernel.π φ)

/-- **A module presented as a cokernel of a morphism between direct images is a direct
image.**  Let `i : Z ⟶ X` be a closed immersion of algebraic spaces, let `M` and `N` be
`𝒪_X`-modules that are direct images along `i`, let `φ : M ⟶ N`, and let `F` be an `𝒪_X`-module
isomorphic to `coker φ`.  Then there is an `𝒪_Z`-module `G` with `i_*G ≅ F`.

The conclusion is reached here from full faithfulness and exactness of `i_*` alone.  The
existence assertion of Stacks 07U0 — for `F` of
finite type, on its scheme-theoretic support — is
`AlgebraicGeometry.Space.exists_module_on_schemeTheoreticSupport`, which carries that tag and
needs no presentation of `F`; see the implementation notes. -/
theorem exists_modulePushforward_iso_of_cokernel (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {M N F : Modules.{u, u} B S hS X.1 X.2}
    (hM : (modulePushforward B S hS i).essImage M)
    (hN : (modulePushforward B S hS i).essImage N) (φ : M ⟶ N) (e : cokernel φ ≅ F) :
    ∃ G : Modules.{u, u} B S hS Z.1 Z.2,
      Nonempty ((modulePushforward B S hS i).obj G ≅ F) :=
  Functor.essImage.ofIso e (essImage_modulePushforward_cokernel B S hS i hi hM hN φ)

/-- **Stacks 07U0, existence, read through the unit of the adjunction of Stacks 03LU.**  For `F`
a cokernel of a morphism between direct images along the closed immersion `i`, the unit
`F ⟶ i_*i^*F` is an isomorphism, so the module on `Z` may be taken to be `i^*F`.

This is the previous statement in the form in which the unit is the data: the direct image is
fully faithful, so the unit is invertible at `F` exactly when `F` is a direct image. -/
theorem isIso_unit_modulePullbackAdjunction_of_cokernel (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {M N F : Modules.{u, u} B S hS X.1 X.2}
    (hM : (modulePushforward B S hS i).essImage M)
    (hN : (modulePushforward B S hS i).essImage N) (φ : M ⟶ N) (e : cokernel φ ≅ F) :
    IsIso ((modulePullbackAdjunction B S hS i).unit.app F) := by
  have hff := fullyFaithfulModulePushforward B S hS i hi
  have := hff.full
  have := hff.faithful
  exact (modulePullbackAdjunction B S hS i).isIso_unit_app_iff_mem_essImage.2
    (Functor.essImage.ofIso e (essImage_modulePushforward_cokernel B S hS i hi hM hN φ))

end AlgebraicGeometry.Space

end
