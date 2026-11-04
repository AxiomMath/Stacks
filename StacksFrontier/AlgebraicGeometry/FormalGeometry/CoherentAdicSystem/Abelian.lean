module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictColimit
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# The category of coherent adic systems is abelian

Let `X` be a Noetherian scheme and `ℐ` a quasi-coherent ideal sheaf on `X`. This file proves that
`Coh(X, ℐ)` is an abelian category, which is the remaining half of part (1) of Tag 087X.

The criterion used is the one the Stacks Project takes as the definition: a preadditive category
with kernels, cokernels and finite products in which the coimage-image comparison
`CategoryTheory.Abelian.coimageImageComparison` is always invertible is abelian. Of the five
hypotheses, preadditivity is inherited from the ambient functor category, kernels come from
`Stacks.Coherent.coherentAdicKernel`, cokernels are levelwise and finite products are levelwise.
Only the invertibility of the comparison is work, and it is proved locally on `X`.

On an affine Noetherian scheme every quasi-coherent ideal sheaf comes from an ideal of the global
sections, and Tag 087W identifies `Coh(X, ℐ)` with the category of finite modules over the
completion of that ring. The completion of a Noetherian ring is Noetherian by Tag 0316, and
finite modules over a Noetherian ring form an abelian category, where the comparison is
invertible; the inverse of the equivalence preserves kernels and cokernels, so it carries that
comparison to the comparison of the original morphism up to an isomorphism of arrows. This is the
affine case.

Invertibility in `Coh(X, ℐ)` is local on `X` by
`Stacks.Coherent.isIso_of_isIso_restrictFunctor_map_system`, and a Noetherian scheme is covered by
its affine opens. What remains is that restriction commutes with the comparison, which holds
because restriction is exact: it preserves cokernels by
`Stacks.Coherent.restrictFunctor_preservesColimitParallelPair`, and it preserves kernels because
`Stacks.Coherent.coherentAdicKernel_restrict` exhibits the restricted kernel as the kernel of the
restricted morphism. The transport itself is
`CategoryTheory.Abelian.PreservesCoimage.hom_coimageImageComparison`.

## Main definitions

* `Stacks.Coherent.abelian_coherentAdicSystems` — **`Coh(X, ℐ)` is abelian.**

## Main results

* `Stacks.Coherent.restrictFunctor_preservesLimitParallelPair` — **restriction along an open
  immersion preserves kernels of morphisms of coherent adic systems**, and
  `Stacks.Coherent.restrictFunctor_preservesFiniteLimits` — hence all finite limits.
* `Stacks.Coherent.isIso_coimageImageComparison_of_isAffine` — on an affine Noetherian scheme the
  coimage-image comparison is invertible, by transport along Tag 087W.
* `Stacks.Coherent.isIso_coimageImageComparison` — the coimage-image comparison of a morphism of
  coherent adic systems is invertible.

## Implementation notes

The kernel in `Coh(X, ℐ)` is not the levelwise kernel, so preservation of kernels by restriction
is not inherited from the ambient functor category; it is deduced from the explicit comparison of
`Stacks.Coherent.coherentAdicKernel_restrict` by transporting the limiting kernel fork along it.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0316](https://stacks.math.columbia.edu/tag/0316)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Coherent

/-! ### Restriction along an open immersion is left exact -/

/-- **Restriction along an open immersion preserves the kernel of a morphism of coherent adic
systems.** Equivalently, the kernel in `Coh(X, ℐ)` may be computed after restricting to an open
subscheme — the local half of part (2) of Tag 087X for kernels.

The kernel is not levelwise, so this does not follow from exactness of termwise restriction;
instead `Stacks.Coherent.coherentAdicKernel_restrict` identifies the restriction of the kernel
with the kernel of the restricted morphism over the inclusions into the source, and that
identification carries the limiting kernel fork to the limiting kernel fork. -/
public instance restrictFunctor_preservesLimitParallelPair {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {F G : CoherentAdicSystems I} (α : F ⟶ G) :
    PreservesLimit (parallelPair α 0) (restrictFunctor I f) := by
  have hY : IsNoetherian Y := isNoetherian_of_isOpenImmersion f
  obtain ⟨e, he⟩ := coherentAdicKernel_restrict I f α
  refine preservesLimit_of_preserves_limit_cone (coherentAdicKernelIsLimit I α) ?_
  refine (isLimitMapConeForkEquiv' (restrictFunctor I f)
    (coherentAdicKernelι_comp I α)).symm ?_
  refine IsLimit.ofIsoLimit (coherentAdicKernelIsLimit (I.comap f)
    ((restrictFunctor I f).map α)) (Cone.ext e ?_).symm
  rintro (_ | _)
  · exact he.symm
  · exact (congrArg (fun z => z ≫ (restrictFunctor I f).map α) he.symm).trans
      (Category.assoc _ _ _)

/-- **Restriction along an open immersion preserves finite limits of coherent adic systems.**

`Coh(X, ℐ)` is preadditive with finite products, cokernels and kernels, so it has equalizers and a
zero object; a functor between such categories which preserves kernels preserves every finite
limit. -/
public instance restrictFunctor_preservesFiniteLimits {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    PreservesFiniteLimits (restrictFunctor I f) :=
  have _h₁ : HasFiniteBiproducts (CoherentAdicSystems I) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have _h₂ : HasFiniteBiproducts (CoherentAdicSystems (I.comap f)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasBinaryBiproducts (CoherentAdicSystems I) :=
    hasBinaryBiproducts_of_finite_biproducts _
  have : HasBinaryBiproducts (CoherentAdicSystems (I.comap f)) :=
    hasBinaryBiproducts_of_finite_biproducts _
  have : HasZeroObject (CoherentAdicSystems I) := hasZeroObject_of_hasFiniteBiproducts _
  have : HasZeroObject (CoherentAdicSystems (I.comap f)) :=
    hasZeroObject_of_hasFiniteBiproducts _
  have : HasEqualizers (CoherentAdicSystems I) := Preadditive.hasEqualizers_of_hasKernels
  Functor.preservesFiniteLimits_of_preservesKernels (restrictFunctor I f)

/-! ### The affine case -/

/-- **On an affine Noetherian scheme the coimage-image comparison of a morphism of coherent adic
systems is invertible.**

Every quasi-coherent ideal sheaf on an affine scheme is the one attached to an ideal of the global
sections, and Tag 087W identifies `Coh(Y, 𝒥)` with the finite modules over the completion of that
ring, which is Noetherian by Tag 0316; finite modules over a Noetherian ring form an abelian
category, so there the comparison is invertible. The inverse of the equivalence preserves kernels
and cokernels, hence carries that comparison to the comparison of the original morphism up to an
isomorphism of arrows. -/
public theorem isIso_coimageImageComparison_of_isAffine {Y : Scheme.{u}} [IsAffine Y]
    [IsNoetherian Y] (J : Y.IdealSheafData) {H K : CoherentAdicSystems J} (α : H ⟶ K) :
    IsIso (Abelian.coimageImageComparison α) := by
  have hring : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  obtain ⟨L, rfl⟩ := (Scheme.IdealSheafData.equivOfIsAffine (X := Y)).symm.surjective J
  have hequiv : (coherentSystemToFGModuleFunctor Y L).IsEquivalence :=
    coherentSystemToFGModuleFunctor_isEquivalence Y L
  let Φ := coherentSystemToFGModuleFunctor Y L
  let Ψ := Φ.inv
  let i : Φ ⋙ Ψ ≅ 𝟭 (CoherentAdicSystems (Scheme.IdealSheafData.ofIdealTop L)) :=
    Φ.asEquivalence.unitIso.symm
  let arrowIso : Arrow.mk (Ψ.map (Φ.map α)) ≅ Arrow.mk α :=
    ((Functor.mapArrowFunctor _ _).mapIso i).app (Arrow.mk α)
  let iso : Arrow.mk (Ψ.map (Abelian.coimageImageComparison (Φ.map α))) ≅
      Arrow.mk (Abelian.coimageImageComparison α) :=
    Abelian.PreservesCoimageImageComparison.iso Ψ (Φ.map α) ≪≫
      Abelian.coimageImageComparisonFunctor.mapIso arrowIso
  exact (Arrow.isIso_iff_isIso_of_isIso iso.inv).mpr inferInstance

/-! ### The coimage-image comparison -/

/-- **The coimage-image comparison of a morphism of coherent adic systems is invertible.**

Invertibility is local on `X`, and a scheme is covered by its affine opens. Restriction along an
open immersion preserves kernels and cokernels, hence carries the comparison of `α` to the
comparison of the restricted morphism up to isomorphisms of its source and target, and on an
affine Noetherian open the comparison is invertible by
`Stacks.Coherent.isIso_coimageImageComparison_of_isAffine`. -/
public instance isIso_coimageImageComparison {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {F G : CoherentAdicSystems I} (α : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison α) := by
  refine isIso_of_isIso_restrictFunctor_map_system I (Abelian.coimageImageComparison α)
    (fun U : X.affineOpens => U.1) (iSup_affineOpens_eq_top X) fun U => ?_
  have hY : IsNoetherian U.1.toScheme := isNoetherian_of_isOpenImmersion U.1.ι
  have hAff : IsAffine U.1.toScheme := U.2
  have hcomp := Abelian.PreservesCoimage.hom_coimageImageComparison
    (restrictFunctor I U.1.ι) α
  have h1 : IsIso (Abelian.coimageImageComparison ((restrictFunctor I U.1.ι).map α)) :=
    isIso_coimageImageComparison_of_isAffine (I.comap U.1.ι) _
  have hbig : IsIso ((Abelian.PreservesCoimage.iso (restrictFunctor I U.1.ι) α).hom ≫
      Abelian.coimageImageComparison ((restrictFunctor I U.1.ι).map α) ≫
        (Abelian.PreservesImage.iso (restrictFunctor I U.1.ι) α).inv) := inferInstance
  have heq : (restrictFunctor I U.1.ι).map (Abelian.coimageImageComparison α) =
      (Abelian.PreservesCoimage.iso (restrictFunctor I U.1.ι) α).hom ≫
        Abelian.coimageImageComparison ((restrictFunctor I U.1.ι).map α) ≫
          (Abelian.PreservesImage.iso (restrictFunctor I U.1.ι) α).inv :=
    (Category.comp_id _).symm.trans
      ((congrArg (fun z => (restrictFunctor I U.1.ι).map
            (Abelian.coimageImageComparison α) ≫ z)
          (Abelian.PreservesImage.iso (restrictFunctor I U.1.ι) α).hom_inv_id.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫
              (Abelian.PreservesImage.iso (restrictFunctor I U.1.ι) α).inv)
            hcomp.symm).trans (Category.assoc _ _ _))))
  exact Eq.mpr (congrArg (fun z => IsIso z) heq) hbig

/-! ### The abelian structure -/

/-- **Part (1) of Tag 087X: the category of coherent adic systems on a Noetherian scheme is
abelian.** It is preadditive, has kernels, cokernels and finite products, and its coimage-image
comparisons are invertible. -/
@[stacks 087X "the category is abelian"]
public instance abelian_coherentAdicSystems {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : Abelian (CoherentAdicSystems I) :=
  Abelian.ofCoimageImageComparisonIsIso

/-- **Part (2) of Tag 087X: restriction to an open subscheme is exact on coherent adic systems.**
Restriction preserves finite limits, being compatible with the kernel construction, and finite
colimits, being a left adjoint computed termwise. -/
@[stacks 087X "restriction to an open is exact"]
public theorem restrictFunctor_exact {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    PreservesFiniteLimits (restrictFunctor I f) ∧
      PreservesFiniteColimits (restrictFunctor I f) :=
  ⟨restrictFunctor_preservesFiniteLimits I f, restrictFunctor_preservesFiniteColimits I f⟩

end Stacks.Coherent

end
