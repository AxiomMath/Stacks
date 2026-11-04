module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Topology.Sheaves.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.AffineSource
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.RightExact
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Abelian
public import StacksFrontier.Topology.Sheaves.Modules.Flat.PullbackTensorExact

/-!
# Exact integral transforms and their kernels

Let `R` be a commutative ring and let `X` and `Y` be schemes over `R` with `X` quasi-compact and
with affine diagonal.  A quasi-coherent kernel `K` on `X ×_R Y` has the integral transform
`F ↦ pr_{2,*}(pr_1^*F ⊗_{𝒪_{X ×_R Y}} K)` of Tag 0FZB, which is `R`-linear and commutes with
arbitrary direct sums.  Tag 0FZH asserts that `K ↦ F_K` is an equivalence from the kernels which
are flat over `X` and whose integrand has no higher direct images along the second projection
onto the `R`-linear **exact** functors `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` commuting with arbitrary direct
sums.

This file states both categories and proves the direction from kernels to functors: flatness of
the kernel over `X` makes the integral transform left exact, and the vanishing of the first
higher direct image makes it right exact, through the long exact sequence of the right derived
functors of direct image.  The equivalence itself is
`AlgebraicGeometry.isEquivalence_integralTransformExactKernelFunctor`, in
`IntegralTransformQcoh.ExactKernelEquivalence`.

## Main definitions

* `AlgebraicGeometry.exactLinearCoproductFunctor` is category (1) of Tag 0FZH: the `R`-linear
  exact functors `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` commuting with arbitrary direct sums.
* `AlgebraicGeometry.integralTransformIntegrand` is `F ↦ pr_1^*F ⊗_{𝒪_{X ×_R Y}} K`, the
  integrand of the integral transform, as a functor of `F`.
* `AlgebraicGeometry.integralTransformExactKernel` is category (2) of Tag 0FZH: the kernels `K`
  which are flat over `X` and for which `R^q pr_{2,*}(pr_1^*F ⊗ K) = 0` for all `q > 0` and all
  quasi-coherent `F` on `X`.
* `AlgebraicGeometry.integralTransformExactKernelFunctor` is the functor from (2) to (1).

## Main results

* `AlgebraicGeometry.exactFunctor_integralTransformIntegrand`: condition (2)(a) alone makes
  the integrand exact.  This is Tag 0GMU at the kernel, and it is the only use of flatness.
* `AlgebraicGeometry.preservesFiniteLimits_integralTransformFormula`: flatness of the kernel
  over `X` makes the pullback--tensor--pushforward formula left exact, because direct image is a
  right adjoint.
* `AlgebraicGeometry.shortExact_map_pushforward_of_isZero_rightDerived_one`: direct image keeps
  a short exact sequence short exact when its first term has no first higher direct image.
* `AlgebraicGeometry.exactLinearCoproductFunctor_quasicoherentIntegralTransform`: the direction
  (2) ⇒ (1) of Tag 0FZH.

## Implementation notes

Condition (2)(b) is written with `CategoryTheory.Functor.rightDerived`, the `ℕ`-indexed right
derived functors of direct image; this is the spelling in which the vanishing of positive higher
direct images is already stated elsewhere in this library.

The right exactness half of the direction (2) ⇒ (1) goes through
`CategoryTheory.Functor.preservesFiniteColimits_tfae`, whose first clause asks exactly for the
image of a short exact sequence to be exact with epimorphic second map.  The use of condition
(2)(b) is at the first term of a short exact sequence of quasi-coherent modules on `X`, which is
why the condition is quantified over all of `QCoh(𝒪_X)` and not just over the module whose
transform is being computed.

## References

* [Stacks Project, Tag 0FZH](https://stacks.math.columbia.edu/tag/0FZH)
* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))

/-! ### The two categories of Tag 0FZH -/

/-- **Category (1) of Tag 0FZH.**  The property of a functor between the categories of
quasi-coherent modules of being `R`-linear, exact, and commuting with arbitrary direct sums. -/
def exactLinearCoproductFunctor :
    ObjectProperty
      ((SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory) :=
  fun F =>
    letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
    letI : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
    (F.Additive ∧ F.Linear R) ∧ exactFunctor _ _ F ∧
      ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F

/-- An exact functor is right exact, so category (1) of Tag 0FZH is contained in the category of
`R`-linear right exact direct-sum-preserving functors of Tag 0FZD. -/
theorem exactLinearCoproductFunctor_le_rightExactLinearCoproductFunctor :
    exactLinearCoproductFunctor R X Y ≤ rightExactLinearCoproductFunctor R X Y := by
  intro F hF
  exact ⟨hF.1, ((exactFunctor_iff F).mp hF.2.1).2, hF.2.2⟩

/-- **The integrand of an integral transform**: the quasi-coherent module
`pr_1^*F ⊗_{𝒪_{X ×_R Y}} K` on `X ×_R Y`, as a functor of the quasi-coherent module `F` on
`X`. -/
def integralTransformIntegrand
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
      (pullback X.hom Y.hom).Modules :=
  ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf) ⋙
    Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨(pullback X.hom Y.hom).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
          (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj (K.obj))

/-- The pullback--tensor--pushforward formula of Tag 0FZB is the integrand followed by direct
image along the second projection. -/
theorem integralTransformIntegrand_comp_pushforward
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    integralTransformIntegrand R X Y K ⋙
        Scheme.Modules.pushforward (pullback.snd X.hom Y.hom) =
      integralTransformFormula R X Y K.obj := rfl

/-- **Category (2) of Tag 0FZH.**  A quasi-coherent kernel `K` on `X ×_R Y` satisfies the two
conditions of the tag when `K` is flat over `X` and the positive higher direct images
`R^q pr_{2,*}(pr_1^*F ⊗_{𝒪_{X ×_R Y}} K)` vanish for every quasi-coherent module `F` on `X`. -/
def integralTransformExactKernel :
    ObjectProperty
      ((SheafOfModules.isQuasicoherent
        (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :=
  fun K =>
    IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj ∧
      ∀ (F : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory) (q : ℕ),
        0 < q →
          IsZero (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived q).obj
            ((integralTransformIntegrand R X Y K).obj F))

/-! ### Flatness of the kernel and exactness of the integrand -/

/-- **Condition (2)(a) of Tag 0FZH makes the integrand exact.**  A kernel flat over `X` makes
`F ↦ pr_1^*F ⊗_{𝒪_{X ×_R Y}} K` an exact functor from quasi-coherent modules on `X` to modules
on `X ×_R Y`; this is Tag 0GMU, after the symmetry of the tensor product and the inclusion of
the quasi-coherent modules, both of which are exact. -/
theorem exactFunctor_integralTransformIntegrand
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (hK : IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj) :
    exactFunctor _ _ (integralTransformIntegrand R X Y K) := by
  have h : exactFunctor X.left.Modules (pullback X.hom Y.hom).Modules
      (Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨(pullback X.hom Y.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
              (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj
              (K.obj))) :=
    (exactFunctor _ _).prop_of_iso
      (Functor.isoWhiskerLeft (Scheme.Modules.pullback (pullback.fst X.hom Y.hom))
        ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
          ((pullback X.hom Y.hom)).presheaf ((pullback X.hom Y.hom)).ringCatSheaf.2
          (K.obj)))).symm
      (Stacks.SheafOfModules.pullbackTensorFunctor_exact
        (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj hK)
  have hlim : PreservesFiniteLimits
      (Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨(pullback X.hom Y.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
              (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj
              (K.obj))) := ((exactFunctor_iff _).mp h).1
  have hcolim : PreservesFiniteColimits
      (Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨(pullback X.hom Y.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
              (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj
              (K.obj))) := ((exactFunctor_iff _).mp h).2
  refine (exactFunctor_iff _).mpr ⟨?_, ?_⟩
  · exact @comp_preservesFiniteLimits _ _ _ _ _ _
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf))
      (Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨(pullback X.hom Y.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
              (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj
              (K.obj))) inferInstance hlim
  · exact @comp_preservesFiniteColimits _ _ _ _ _ _
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf))
      (Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          ⟨(pullback X.hom Y.hom).presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((pullback X.hom Y.hom).presheaf)
              (forget₂ CommRingCat RingCat) ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj
              (K.obj))) inferInstance hcolim

/-- The integrand preserves zero morphisms: it preserves initial objects, being right exact. -/
theorem preservesZeroMorphisms_integralTransformIntegrand
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (hK : IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj) :
    (integralTransformIntegrand R X Y K).PreservesZeroMorphisms := by
  have hcolim : PreservesFiniteColimits (integralTransformIntegrand R X Y K) :=
    ((exactFunctor_iff _).mp (exactFunctor_integralTransformIntegrand R X Y K hK)).2
  have : PreservesColimit (Functor.empty.{0} _) (integralTransformIntegrand R X Y K) :=
    inferInstance
  exact Functor.preservesZeroMorphisms_of_preserves_initial_object
    (F := integralTransformIntegrand R X Y K)

/-- **The left exact half of the direction (2) ⇒ (1) of Tag 0FZH.**  Flatness of the kernel over
`X` alone makes the pullback--tensor--pushforward formula left exact: the integrand is then
exact, and direct image along the second projection, being a right adjoint, preserves all
limits. -/
theorem preservesFiniteLimits_integralTransformFormula
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (hK : IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj) :
    PreservesFiniteLimits (integralTransformFormula R X Y K.obj) := by
  have hint : PreservesFiniteLimits (integralTransformIntegrand R X Y K) :=
    ((exactFunctor_iff _).mp (exactFunctor_integralTransformIntegrand R X Y K hK)).1
  have hpf : PreservesFiniteLimits
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) := inferInstance
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ (integralTransformIntegrand R X Y K)
    (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)) hint hpf

/-- The pullback--tensor--pushforward formula is additive, as the integral transform of Tag 0FZB
is and the inclusion of the quasi-coherent modules of the target is. -/
theorem additive_integralTransformFormula [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory) :
    (integralTransformFormula R X Y K.obj).Additive := by
  have hiota : (ObjectProperty.ι
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf)).Additive := ⟨by intros; rfl⟩
  have hq : (quasicoherentIntegralTransform R X Y K).Additive :=
    quasicoherentIntegralTransform_additive R X Y K
  have hcomp : (quasicoherentIntegralTransform R X Y K ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf)).Additive :=
    inferInstance
  exact @Functor.additive_of_iso _ _ _ _ _ _ _ hcomp _
    (quasicoherentIntegralTransformData R X Y K).comparison

/-! ### Direct image of a short exact sequence -/

/-- **Direct image keeps a short exact sequence short exact when the first term has no first
higher direct image.**  For a morphism of schemes `f` and a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` of modules on the source with `R¹f_* A = 0`, the sequence
`0 ⟶ f_* A ⟶ f_* B ⟶ f_* C ⟶ 0` is short exact.  Direct image is a right adjoint, so it is
left exact, and the long exact sequence of its right derived functors makes `f_* B ⟶ f_* C` an
epimorphism; both halves are
`Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one`, of which this is the case of a
direct image. -/
theorem shortExact_map_pushforward_of_isZero_rightDerived_one {Z W : Scheme.{u}} (f : Z ⟶ W)
    {S : ShortComplex Z.Modules} (hS : S.ShortExact)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj S.X₁)) :
    (S.map (Scheme.Modules.pushforward f)).ShortExact :=
  Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one _ hS h

/-- **The right exact half of the direction (2) ⇒ (1) of Tag 0FZH.**  For a kernel satisfying
the two conditions of the tag, the pullback--tensor--pushforward formula is right exact: the
integrand carries a short exact sequence of quasi-coherent modules on `X` to a short exact
sequence, whose first term has no first higher direct image by condition (2)(b), so direct
image along the second projection keeps it short exact. -/
theorem preservesFiniteColimits_integralTransformFormula
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (hK : integralTransformExactKernel R X Y K) :
    PreservesFiniteColimits (integralTransformFormula R X Y K.obj) := by
  have hadd : (integralTransformFormula R X Y K.obj).Additive :=
    additive_integralTransformFormula R X Y K
  have hzero : (integralTransformIntegrand R X Y K).PreservesZeroMorphisms :=
    preservesZeroMorphisms_integralTransformIntegrand R X Y K hK.1
  have hilim : PreservesFiniteLimits (integralTransformIntegrand R X Y K) :=
    ((exactFunctor_iff _).mp (exactFunctor_integralTransformIntegrand R X Y K hK.1)).1
  have hicolim : PreservesFiniteColimits (integralTransformIntegrand R X Y K) :=
    ((exactFunctor_iff _).mp (exactFunctor_integralTransformIntegrand R X Y K hK.1)).2
  refine ((Functor.preservesFiniteColimits_tfae
    (integralTransformFormula R X Y K.obj)).out 1 4).mp ?_
  intro S hS
  have h1 : (S.map (integralTransformIntegrand R X Y K)).ShortExact :=
    hS.map_of_exact (integralTransformIntegrand R X Y K)
  have h2 : (S.map (integralTransformFormula R X Y K.obj)).ShortExact :=
    shortExact_map_pushforward_of_isZero_rightDerived_one (pullback.snd X.hom Y.hom) h1
      (hK.2 S.X₁ 1 Nat.one_pos)
  exact ⟨h2.exact, h2.epi_g⟩

/-- **The direction (2) ⇒ (1) of Tag 0FZH.**  The integral transform of a quasi-coherent kernel
which is flat over `X` and whose integrand has no positive higher direct images along the second
projection is `R`-linear, exact, and commutes with arbitrary direct sums.  Linearity and the
direct sums are Tag 0FZB; left exactness is flatness of the kernel; right exactness is the
vanishing of the first higher direct image, through the long exact sequence. -/
theorem exactLinearCoproductFunctor_quasicoherentIntegralTransform
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (hK : integralTransformExactKernel R X Y K) :
    exactLinearCoproductFunctor R X Y (quasicoherentIntegralTransform R X Y K) := by
  refine ⟨⟨quasicoherentIntegralTransform_additive R X Y K,
      quasicoherentIntegralTransform_isLinearOverBase R X Y K⟩, ?_,
    fun I => quasicoherentIntegralTransform_preservesDirectSums R X Y K I⟩
  have hlim : PreservesFiniteLimits (integralTransformFormula R X Y K.obj) :=
    preservesFiniteLimits_integralTransformFormula R X Y K hK.1
  have hcolim : PreservesFiniteColimits (integralTransformFormula R X Y K.obj) :=
    preservesFiniteColimits_integralTransformFormula R X Y K hK
  have hlim' : PreservesFiniteLimits (quasicoherentIntegralTransform R X Y K ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf)) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (quasicoherentIntegralTransformData R X Y K).comparison.symm hlim
  have hcolim' : PreservesFiniteColimits (quasicoherentIntegralTransform R X Y K ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf)) :=
    @preservesFiniteColimits_of_natIso _ _ _ _ _ _
      (quasicoherentIntegralTransformData R X Y K).comparison.symm hcolim
  refine (exactFunctor_iff _).mpr ⟨⟨?_⟩, ⟨?_⟩⟩
  · intro J _ _
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (quasicoherentIntegralTransform R X Y K)
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf))
  · intro J _ _
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (quasicoherentIntegralTransform R X Y K)
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf))

/-! ### The functor from kernels to functors, and the equivalence -/

/-- **The functor of Tag 0FZH from the kernels of (2) to the functors of (1)**, sending a
quasi-coherent kernel on `X ×_R Y` to its integral transform. -/
def integralTransformExactKernelFunctor
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    (integralTransformExactKernel R X Y).FullSubcategory ⥤
      (exactLinearCoproductFunctor R X Y).FullSubcategory :=
  ObjectProperty.lift (exactLinearCoproductFunctor R X Y)
    (ObjectProperty.ι (integralTransformExactKernel R X Y) ⋙
      integralTransformQcohFunctor R X Y)
    (fun K => exactLinearCoproductFunctor_quasicoherentIntegralTransform R X Y
      K.obj K.property)

end AlgebraicGeometry

end
