module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# An open `D(g)` of the affine line is a smooth geometrically connected curve

For a field `k` and a nonzero `g ∈ k[X]`, the open `D(g) = Spec k[X]_g` of the affine line
`𝔸¹_k` is smooth of relative dimension one over `k`, a curve over `k`, and geometrically
connected: for every field extension `K` of `k`, `D(g)_K` is a nonempty open of
`𝔸¹_K = Spec K[X]`, which is irreducible. These are the hypotheses under which the curve case of
the weight bound of Weil II on opens of the affine line
(`Stacks.EtaleCohomology.WeilIICurveBoundOpenAffineLine`) applies to `D(g)`.

## Main results

* `Stacks.GenericFiniteEtale.smoothOfRelativeDimension_specMap_away`.
* `Stacks.GenericFiniteEtale.isCurve_specMap_away`.
* `Stacks.GenericFiniteEtale.connectedSpace_pullback_specMap_away`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace Stacks.GenericFiniteEtale

variable (k : Type u) [Field k]

/-- The polynomial ring in one variable is standard smooth of relative dimension one. -/
theorem isStandardSmoothOfRelativeDimension_polynomial :
    Algebra.IsStandardSmoothOfRelativeDimension 1 k k[X] :=
  .of_algEquiv 1 (MvPolynomial.uniqueAlgEquiv k (Fin 1))

/-- `k[X]_g` is standard smooth of relative dimension one over `k`. -/
theorem isStandardSmoothOfRelativeDimension_away (g : k[X]) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 k (Localization.Away g) := by
  have := isStandardSmoothOfRelativeDimension_polynomial k
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 k[X] (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away g
  simpa using Algebra.IsStandardSmoothOfRelativeDimension.trans 1 0 k k[X] (Localization.Away g)

/-- **`D(g) ⊆ 𝔸¹_k` is smooth of relative dimension one over `k`.** -/
theorem smoothOfRelativeDimension_specMap_away (g : k[X]) :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  show (algebraMap k (Localization.Away g)).IsStandardSmoothOfRelativeDimension 1
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact isStandardSmoothOfRelativeDimension_away k g

/-- `k[X]_g` is a domain for `g ≠ 0`. -/
theorem isDomain_away {g : k[X]} (hg : g ≠ 0) : IsDomain (Localization.Away g) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hg)

/-- **`D(g) ⊆ 𝔸¹_k` is a curve over `k`** for `g ≠ 0`: it is integral, affine, of finite type,
and of dimension one, being nonempty and smooth of relative dimension one. -/
theorem isCurve_specMap_away {g : k[X]} (hg : g ≠ 0) :
    IsCurve k (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g)))) := by
  have := isDomain_away k hg
  have := smoothOfRelativeDimension_specMap_away k g
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g)))) :=
    SmoothOfRelativeDimension.smooth 1 _
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1
    (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g))))
  refine (isCurve_iff k _).2 ⟨
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance }, ?_⟩
  simpa using hdim

/-- `k[X] ⊗_k K` is a domain: it is `K[X]`. -/
theorem isDomain_polynomial_tensorProduct (K : Type u) [Field K] [Algebra k K] :
    IsDomain (TensorProduct k k[X] K) :=
  MulEquiv.isDomain (B := K[X])
    ((Algebra.TensorProduct.comm k k[X] K).trans (polyEquivTensor k K).symm).toMulEquiv

/-- A scheme isomorphic to an irreducible scheme is irreducible. -/
private theorem irreducibleSpace_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f]
    [IrreducibleSpace Y] : IrreducibleSpace X :=
  haveI : Nonempty X := ⟨(inv f).base (Nonempty.some inferInstance)⟩
  f.isOpenEmbedding.irreducibleSpace

/-- **`D(g) ⊆ 𝔸¹_k` is geometrically connected** for `g ≠ 0`: for every field extension `K` of `k`
the base change `D(g)_K` is a nonempty open of `𝔸¹_K = Spec K[X]`, which is irreducible. -/
theorem connectedSpace_pullback_specMap_away {g : k[X]} (hg : g ≠ 0) (K : Type u) [Field K]
    [Algebra k K] :
    ConnectedSpace ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g))))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have := isDomain_away k hg
  have := isDomain_polynomial_tensorProduct k K
  set e := Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away g)))
  set h := Spec.map (CommRingCat.ofHom (algebraMap k k[X]))
  set kb := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g))) = e ≫ h := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [hcomp]
  -- `𝔸¹_K` is irreducible
  have : IrreducibleSpace ↥(Spec (.of (TensorProduct k k[X] K))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum _))
  have : IrreducibleSpace ↥(pullback h kb) :=
    irreducibleSpace_of_isIso (pullbackSpecIso k k[X] K).hom
  -- `D(g)_K` is nonempty: `D(g)_K ⟶ D(g)` is surjective
  have : Nonempty ↥(Spec (.of (Localization.Away g))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  have : Surjective kb := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : Nonempty ↥(pullback (e ≫ h) kb) := by
    obtain ⟨z, -⟩ := (pullback.fst (e ≫ h) kb).surjective (Nonempty.some inferInstance)
    exact ⟨z⟩
  have : Nonempty ↥(pullback e (pullback.fst h kb)) :=
    ⟨(pullbackRightPullbackFstIso h kb e).inv.base (Nonempty.some inferInstance)⟩
  have : IrreducibleSpace ↥(pullback e (pullback.fst h kb)) :=
    (pullback.snd e (pullback.fst h kb)).isOpenEmbedding.irreducibleSpace
  have : IrreducibleSpace ↥(pullback (e ≫ h) kb) :=
    irreducibleSpace_of_isIso (pullbackRightPullbackFstIso h kb e).inv
  infer_instance

end Stacks.GenericFiniteEtale
