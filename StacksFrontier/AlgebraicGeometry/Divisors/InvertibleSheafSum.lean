module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors

/-!
# The invertible sheaf of a sum of effective Cartier divisors

Let `X` be a scheme and let `D` and `D'` be effective Cartier divisors on `X`. The sum `D + D'`
is the closed subscheme cut out by the product `ℐ_D · ℐ_{D'}` of their ideal sheaves, and it is
again an effective Cartier divisor ([Stacks, Tag 01WU]). This file identifies its invertible
sheaf with the tensor product of the two invertible sheaves,

`𝒪_X(D) ⊗_{𝒪_X} 𝒪_X(D') ≅ 𝒪_X(D + D')`,

by the unique isomorphism carrying `1_D ⊗ 1_{D'}` to `1_{D + D'}`.

## Main definitions

* `Stacks.Divisors.sumSheaf`: the tensor product `𝒪_X(D) ⊗ 𝒪_X(D')`.
* `Stacks.Divisors.canonicalSectionTensor`: the global section `1_D ⊗ 1_{D'}` of `sumSheaf`.
* `Stacks.Divisors.invertibleSheafSumIso`: the identification
  `𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')`.
* `Stacks.Divisors.generatorSectionsOfDualBasisOne`: the dual coordinate of a rank-one dual
  basis of `ℐ_D`, as a trivializing section of `𝒪_X(D)`.
* `Stacks.Divisors.dualBasisOneLam`: that coordinate at the index `X.Modules` is written over.

## Main results

* `Stacks.Divisors.invertibleSheafSumIso_canonicalSection`: the identification carries
  `1_D ⊗ 1_{D'}` to `1_{D + D'}`.
* `Stacks.Divisors.invertibleSheafSumIso_unique`: the distinguished-section condition
  determines the identification.
* `Stacks.Divisors.existsUnique_invertibleSheafSumIso_symm`: the two halves at once, as the
  unique isomorphism `𝒪_X(D + D') ≅ 𝒪_X(D) ⊗ 𝒪_X(D')` carrying `1_{D + D'}` to
  `1_D ⊗ 1_{D'}`.
* `Stacks.Divisors.zeroScheme_canonicalSectionTensor`: the zero scheme of `1_D ⊗ 1_{D'}` is
  `D + D'`.
* `Stacks.Divisors.isRegularSection_canonicalSectionTensor`: `1_D ⊗ 1_{D'}` is a
  nonzerodivisor section.

## References

* [Stacks Project, Tag 02OP](https://stacks.math.columbia.edu/tag/02OP)
* [Stacks Project, Tag 01WU](https://stacks.math.columbia.edu/tag/01WU)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 02ON](https://stacks.math.columbia.edu/tag/02ON)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open Stacks.SheafOfModules (dualEval DualBasisOne)
open Stacks.Cohomology.Generators (GeneratorSections)

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-! ### `𝒪_X(D)` is free of rank one where `ℐ_D` is -/

/-- **Multiplication by the dual coordinate of a rank-one dual basis of `ℐ_D` is bijective on
the sections of `𝒪_X(D)`.** -/
theorem bijective_smulSectionMap_dualBasisOne_lam (D : X.IdealSheafData) {U : X.Opens}
    (b : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' D) U) :
    Function.Bijective (Stacks.SheafOfModules.smulSectionMap
      (𝒪 := X.presheaf) (h𝒪 := (structureSheafRing X.toRingedSpace).property)
      (L := invertibleSheaf' D) b.lam) := by
  refine ⟨fun r r' h => ?_, fun μ => ⟨dualEval μ b.e, eq_smul_dualBasisOne_lam D b μ⟩⟩
  have key : r * dualEval b.lam b.e = r' * dualEval b.lam b.e :=
    (Stacks.SheafOfModules.evalSection_smul_left _ _ _ _ r b.lam b.e).symm.trans
      ((congrArg (fun ν => dualEval ν b.e) h).trans
        (Stacks.SheafOfModules.evalSection_smul_left _ _ _ _ r' b.lam b.e))
  rwa [b.eval_self, mul_one, mul_one] at key

/-- **A rank-one dual basis of `ℐ_D` over `U` makes its dual coordinate a trivializing section
of `𝒪_X(D)` over `U`.** -/
def generatorSectionsOfDualBasisOne (D : X.IdealSheafData) {U : X.Opens}
    (b : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' D) U) :
    GeneratorSections X.toRingedSpace (invertibleSheaf' D) U :=
  ⟨b.lam, fun _ hVU =>
    bijective_smulSectionMap_dualBasisOne_lam D (b.restrict (homOfLE hVU))⟩

/-- The dual coordinate of a rank-one dual basis of `ℐ_D`, read as a section of `𝒪_X(D)` at the
index `AlgebraicGeometry.Scheme.Modules` is written over. -/
def dualBasisOneLam (D : X.IdealSheafData) {U : X.Opens}
    (b : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' D) U) :
    Γ(divisorSheaf D, U) :=
  b.lam

/-- **The component of `1_D` over an open carrying a rank-one dual basis of `ℐ_D`** is the
generator the basis determines times the dual coordinate. -/
theorem canonicalSection_eq_smul_dualBasisOne_lam (D : X.IdealSheafData) {U : X.Opens}
    (b : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' D) U) :
    ((canonicalSection' D).val (op U) : Γ(divisorSheaf D, U)) =
      idealSheafSection D b.e • dualBasisOneLam D b :=
  (eq_smul_dualBasisOne_lam D b _).symm

/-! ### The tensor product and its distinguished section -/

variable (D D' : X.IdealSheafData)

/-- The tensor product `𝒪_X(D) ⊗_{𝒪_X} 𝒪_X(D')` of the invertible sheaves of two closed
subschemes, read at the index that `AlgebraicGeometry.Scheme.Modules` is written over. -/
abbrev sumSheaf : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (invertibleSheaf' D)).obj
    (invertibleSheaf' D')

/-- `𝒪_X(D) ⊗ 𝒪_X(D')` is invertible, at the index that
`AlgebraicGeometry.Scheme.Modules` is written over: the tensor product of two invertible sheaves
is invertible ([Stacks, Tag 01CT] (1)). -/
instance isInvertible_sumSheaf [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (sumSheaf D D') :=
  haveI := isTensorInvertible_invertibleSheaf D
  haveI := isTensorInvertible_invertibleSheaf D'
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ (invertibleSheaf' D) (invertibleSheaf' D'))

/-- **The distinguished section `1_D ⊗ 1_{D'}`** of `𝒪_X(D) ⊗ 𝒪_X(D')`: the pure tensor of the
two canonical sections, over the whole space. -/
def canonicalSectionTensor : Γ(sumSheaf D D', (⊤ : X.Opens)) :=
  toTensorSheafSection X.toRingedSpace (invertibleSheaf' D) (invertibleSheaf' D') (op ⊤)
    ((canonicalSection' D).val (op ⊤) ⊗ₜ[X.presheaf.obj (op ⊤)] (canonicalSection' D').val (op ⊤))

/-- The component of `1_D ⊗ 1_{D'}` over an open is the pure tensor of the components of `1_D`
and `1_{D'}` there. -/
theorem canonicalSectionTensor_restrict (U : X.Opens) :
    (sumSheaf D D').presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (canonicalSectionTensor D D') =
      toTensorSheafSection X.toRingedSpace (invertibleSheaf' D) (invertibleSheaf' D') (op U)
        ((canonicalSection' D).val (op U) ⊗ₜ[X.presheaf.obj (op U)]
          (canonicalSection' D').val (op U)) := by
  refine (Stacks.Cohomology.Generators.toTensorSheafSection_restrict X.toRingedSpace
    (invertibleSheaf' D) (invertibleSheaf' D') (le_top : U ≤ ⊤) _ _).trans ?_
  exact congrArg₂ (fun x y => toTensorSheafSection X.toRingedSpace
      (invertibleSheaf' D) (invertibleSheaf' D') (op U)
      (x ⊗ₜ[X.presheaf.obj (op U)] y))
    (Scheme.Modules.map_eval_top (divisorSheaf D) (canonicalSection' D) U)
    (Scheme.Modules.map_eval_top (divisorSheaf D') (canonicalSection' D') U)

/-! ### The zero scheme of the distinguished section -/

/-- **The local equation of `Z(1_D ⊗ 1_{D'})`.** On an affine open carrying rank-one dual bases
of `ℐ_D` and of `ℐ_{D'}`, the ideal of the zero scheme of `1_D ⊗ 1_{D'}` is generated by the
product `f * g` of the two generators the bases determine. -/
theorem zeroScheme_ideal_canonicalSectionTensor
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] (U : X.affineOpens)
    (b : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' D) (U : X.Opens))
    (b' : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' D') (U : X.Opens))
    (f g : Γ(X, (U : X.Opens))) (hf : idealSheafSection D b.e = f)
    (hg : idealSheafSection D' b'.e = g) :
    (zeroScheme X (sumSheaf D D') (canonicalSectionTensor D D')).ideal U =
      Ideal.span ({f * g} : Set Γ(X, (U : X.Opens))) := by
  subst hf hg
  set lam : Γ(sumSheaf D D', (U : X.Opens)) :=
    toTensorSheafSection X.toRingedSpace (invertibleSheaf' D) (invertibleSheaf' D')
      (op (U : X.Opens)) (dualBasisOneLam D b ⊗ₜ[X.presheaf.obj (op (U : X.Opens))]
        dualBasisOneLam D' b') with hlam
  have hbij : Function.Bijective
      (fun r : Γ(X, (U : X.Opens)) => r • lam) :=
    Stacks.Cohomology.Generators.bijective_smul_toTensorSheafSection X.toRingedSpace
      (invertibleSheaf' D) (invertibleSheaf' D') (U : X.Opens)
      (generatorSectionsOfDualBasisOne D b) (generatorSectionsOfDualBasisOne D' b')
  set e : Γ(sumSheaf D D', (U : X.Opens)) ≃ₗ[Γ(X, (U : X.Opens))] Γ(X, (U : X.Opens)) :=
    (LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton Γ(X, (U : X.Opens)) Γ(sumSheaf D D', (U : X.Opens)) lam)
      hbij).symm with he
  have hleft : toTensorSheafSection X.toRingedSpace (invertibleSheaf' D) (invertibleSheaf' D')
        (op (U : X.Opens))
        ((idealSheafSection D b.e • dualBasisOneLam D b)
          ⊗ₜ[X.presheaf.obj (op (U : X.Opens))]
          (idealSheafSection D' b'.e • dualBasisOneLam D' b')) =
      @SMul.smul Γ(X, (U : X.Opens)) Γ(sumSheaf D D', (U : X.Opens)) _
          (idealSheafSection D b.e)
        (toTensorSheafSection X.toRingedSpace (invertibleSheaf' D) (invertibleSheaf' D')
          (op (U : X.Opens))
          (dualBasisOneLam D b ⊗ₜ[X.presheaf.obj (op (U : X.Opens))]
            (idealSheafSection D' b'.e • dualBasisOneLam D' b'))) :=
    Stacks.Cohomology.Generators.toTensorSheafSection_smul_left _ _ _ _ _ _ _
  have hright : toTensorSheafSection X.toRingedSpace (invertibleSheaf' D) (invertibleSheaf' D')
        (op (U : X.Opens))
        (dualBasisOneLam D b ⊗ₜ[X.presheaf.obj (op (U : X.Opens))]
          (idealSheafSection D' b'.e • dualBasisOneLam D' b')) =
      @SMul.smul Γ(X, (U : X.Opens)) Γ(sumSheaf D D', (U : X.Opens)) _
          (idealSheafSection D' b'.e)
        (toTensorSheafSection X.toRingedSpace (invertibleSheaf' D) (invertibleSheaf' D')
          (op (U : X.Opens))
          (dualBasisOneLam D b ⊗ₜ[X.presheaf.obj (op (U : X.Opens))] dualBasisOneLam D' b')) :=
    Stacks.Cohomology.Generators.toTensorSheafSection_smul_right _ _ _ _ _ _ _
  have hcomp : (sumSheaf D D').presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op
      (canonicalSectionTensor D D') =
      (idealSheafSection D b.e * idealSheafSection D' b'.e) • lam := by
    have h1 := canonicalSectionTensor_restrict D D' (U : X.Opens)
    rw [canonicalSection_eq_smul_dualBasisOne_lam D b,
      canonicalSection_eq_smul_dualBasisOne_lam D' b'] at h1
    rw [h1, hleft, hright, hlam]
    exact smul_smul _ _ _
  refine zeroScheme_ideal_of_trivialization X (sumSheaf D D') (canonicalSectionTensor D D') U e
    _ ?_
  rw [hcomp, he]
  exact (LinearEquiv.ofBijective _ hbij).symm_apply_apply _

/-- A generator `a` of `ℐ_D` over an affine open, regular in the sections there, is the generator
determined by a rank-one dual basis of `ℐ_D`. -/
private theorem exists_dualBasisOne_idealSheafSection (I : X.IdealSheafData) (U : X.affineOpens)
    {a : Γ(X, (U : X.Opens))} (hI : I.ideal U = Ideal.span {a}) (ha : IsRegular a) :
    ∃ b : DualBasisOne X.presheaf (structureSheafRing X.toRingedSpace).property
      (negativeTwist' I) (U : X.Opens), idealSheafSection I b.e = a := by
  obtain ⟨y, hy⟩ := (mem_ideal_iff_exists_idealSheafSection I U a).1
    (hI ▸ Ideal.mem_span_singleton_self a)
  exact ⟨Stacks.SheafOfModules.DualBasisOne.ofSmulBijective (U : X.Opens) y
    (bijective_smulSectionMap_resSection I U hI ha.mem_nonZeroDivisors hy), hy⟩

/-- **The zero scheme of `1_D ⊗ 1_{D'}` is `D + D'`.** -/
theorem zeroScheme_canonicalSectionTensor
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] :
    zeroScheme X (sumSheaf D D') (canonicalSectionTensor D D') = D * D' := by
  classical
  choose U hU hxU a b ha hb hgen hgen' using
    exists_affineOpen_ideal_eq_span_pair D D' ‹_› ‹_›
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun x : X => ⟨U x, hU x⟩)
    (eq_top_iff.2 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hxU z⟩) fun x => ?_
  obtain ⟨c, hc⟩ := exists_dualBasisOne_idealSheafSection D ⟨U x, hU x⟩ (hgen x) (ha x)
  obtain ⟨c', hc'⟩ := exists_dualBasisOne_idealSheafSection D' ⟨U x, hU x⟩ (hgen' x) (hb x)
  refine (zeroScheme_ideal_canonicalSectionTensor D D' ⟨U x, hU x⟩ c c' (a x) (b x) hc hc').trans ?_
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hgen x, hgen' x,
    Ideal.span_singleton_mul_span_singleton]

/-- The zero scheme of `1_D ⊗ 1_{D'}`, read through `Stacks.Divisors.sectionsOfTop`, is
`D + D'`. -/
theorem zeroScheme_sectionsOfTop_canonicalSectionTensor
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] :
    zeroScheme X (sumSheaf D D')
        ((sectionsOfTop (sumSheaf D D') (canonicalSectionTensor D D')).eval (op ⊤)) = D * D' :=
  (congrArg (fun z => zeroScheme X (sumSheaf D D') z)
      (sectionsOfTop_eval_top (sumSheaf D D') (canonicalSectionTensor D D'))).trans
    (zeroScheme_canonicalSectionTensor D D')

/-- **`1_D ⊗ 1_{D'}` is a nonzerodivisor section.** -/
theorem isRegularSection_canonicalSectionTensor
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] :
    IsRegularSection X.sheaf.obj X.ringCatSheaf.property
      (sectionsOfTop (sumSheaf D D') (canonicalSectionTensor D D')) :=
  have : IsEffectiveCartierDivisor (D * D') := isEffectiveCartierDivisor_mul D D' ‹_› ‹_›
  (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X (sumSheaf D D') _).1
    (isEffectiveCartierDivisor_of_eq (zeroScheme_sectionsOfTop_canonicalSectionTensor D D'))

/-! ### The identification -/

/-- **The correspondence of [Stacks, Tag 01X0] (2) at a known zero scheme and a known section.**
A nonzerodivisor section `s` of an invertible module `M` with zero scheme `E` and value `x` over
the whole space gives a unique isomorphism `𝒪_X(E) ≅ M` carrying `1_E` to `x`. -/
private theorem existsUnique_invertibleSheafIso_of_eq {M : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (s : M.sections) (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    {E : X.IdealSheafData} {x : Γ(M, (⊤ : X.Opens))}
    (hE : zeroScheme X M (s.eval (op ⊤)) = E) (hx : s.eval (op ⊤) = x) :
    ∃! e : invertibleSheaf' E ≅ M,
      Scheme.Modules.Hom.app e.hom ⊤ ((canonicalSection' E).val (op ⊤)) = x := by
  cases hE
  cases hx
  exact existsUnique_invertibleSheafIso_zeroScheme X M s hs

/-- Applying the inverse of an isomorphism of sheaves of modules to sections undoes applying the
isomorphism. -/
private theorem app_inv_app_hom {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (z : Γ(M, U)) :
    Scheme.Modules.Hom.app e.inv U (Scheme.Modules.Hom.app e.hom U z) = z :=
  congrArg (fun f : M ⟶ M => Scheme.Modules.Hom.app f U z) e.hom_inv_id

/-- Turning an isomorphism round exchanges the two forms of the distinguished-section
condition. -/
private theorem symm_app_eq {M N : X.Modules} (e : M ≅ N) {U : X.Opens} {z : Γ(M, U)}
    {w : Γ(N, U)} (h : Scheme.Modules.Hom.app e.hom U z = w) :
    Scheme.Modules.Hom.app e.symm.hom U w = z :=
  (congrArg (Scheme.Modules.Hom.app e.inv U) h).symm.trans (app_inv_app_hom e U z)

/-- **The correspondence of [Stacks, Tag 01X0] (2) at `1_D ⊗ 1_{D'}`**: there is exactly one
isomorphism `𝒪_X(D + D') ≅ 𝒪_X(D) ⊗ 𝒪_X(D')` carrying `1_{D + D'}` to `1_D ⊗ 1_{D'}`. -/
theorem existsUnique_invertibleSheafSumIso_symm
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] :
    ∃! e : invertibleSheaf' (D * D') ≅ sumSheaf D D',
      Scheme.Modules.Hom.app e.hom ⊤ ((canonicalSection' (D * D')).val (op ⊤)) =
        canonicalSectionTensor D D' :=
  existsUnique_invertibleSheafIso_of_eq
    (sectionsOfTop (sumSheaf D D') (canonicalSectionTensor D D'))
    (isRegularSection_canonicalSectionTensor D D')
    (zeroScheme_sectionsOfTop_canonicalSectionTensor D D')
    (sectionsOfTop_eval_top (sumSheaf D D') (canonicalSectionTensor D D'))

/-- **There is an identification `𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')` carrying `1_D ⊗ 1_{D'}` to
`1_{D + D'}`.** -/
theorem exists_invertibleSheafSumIso
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] :
    ∃ e : sumSheaf D D' ≅ invertibleSheaf' (D * D'),
      Scheme.Modules.Hom.app e.hom ⊤ (canonicalSectionTensor D D') =
        (canonicalSection' (D * D')).val (op ⊤) := by
  obtain ⟨i, hi, -⟩ := existsUnique_invertibleSheafSumIso_symm D D'
  exact ⟨i.symm, symm_app_eq i hi⟩

/-- The canonical identification `𝒪_X(D) ⊗_{𝒪_X} 𝒪_X(D') ≅ 𝒪_X(D + D')` of the tensor product
of the invertible sheaves of two effective Cartier divisors with the invertible sheaf of their
sum, carrying the pure tensor `1_D ⊗ 1_{D'}` of the canonical sections to the canonical section
`1_{D + D'}`. -/
@[stacks 02OP "existence and distinguished-section compatibility",
  ega "IV 21.2.8" "(21.2.8.3), special case"]
def invertibleSheafSumIso [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] :
    sumSheaf D D' ≅ invertibleSheaf' (D * D') :=
  Classical.choose (exists_invertibleSheafSumIso D D')

/-- Under `Stacks.Divisors.invertibleSheafSumIso` the pure tensor `1_D ⊗ 1_{D'}` of the canonical
sections of `𝒪_X(D)` and `𝒪_X(D')` is the canonical section `1_{D + D'}` of `𝒪_X(D + D')`. -/
@[stacks 02OP "existence and distinguished-section compatibility"]
theorem invertibleSheafSumIso_canonicalSection
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] :
    Scheme.Modules.Hom.app (invertibleSheafSumIso D D').hom ⊤ (canonicalSectionTensor D D') =
      (canonicalSection' (D * D')).val (op ⊤) :=
  Classical.choose_spec (exists_invertibleSheafSumIso D D')

/-- An isomorphism `𝒪_X(D) ⊗ 𝒪_X(D') ≅ 𝒪_X(D + D')` carrying `1_D ⊗ 1_{D'}` to `1_{D + D'}` is
`Stacks.Divisors.invertibleSheafSumIso`. -/
@[stacks 02OP "uniqueness"]
theorem invertibleSheafSumIso_unique
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D']
    (e : sumSheaf D D' ≅ invertibleSheaf' (D * D'))
    (he : Scheme.Modules.Hom.app e.hom ⊤ (canonicalSectionTensor D D') =
      (canonicalSection' (D * D')).val (op ⊤)) :
    e = invertibleSheafSumIso D D' := by
  obtain ⟨i, -, huniq⟩ := existsUnique_invertibleSheafSumIso_symm D D'
  exact Iso.symm_eq_iff.1 ((huniq e.symm (symm_app_eq e he)).trans
    (huniq (invertibleSheafSumIso D D').symm
      (symm_app_eq (invertibleSheafSumIso D D')
        (invertibleSheafSumIso_canonicalSection D D'))).symm)

end Stacks.Divisors

end
