module

public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.ConstantAction
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionQuotientAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionQuotientComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RationalGaloisQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RationalGaloisQuotientBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TwistedLineQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsQuotientOfSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeSchemePointExtensions

/-!
# A residual gerbe which is not an isomorphism (Stacks 06MS)

**Stacks 06MR** attaches to every algebraic stack `𝒵` over `S` which is reduced with a
singleton space of points a unique strictly full algebraic subcategory `𝒵' ⊂ 𝒵` satisfying the
equivalent conditions of **Stacks 06MP**, together with its inclusion `𝒵' ⟶ 𝒵`. **Stacks 06MS**
is the example showing that this inclusion need not be an isomorphism, which is why
**Definition 06MU** requires residual gerbes to be locally Noetherian; the example is even an
algebraic space.

Let `ℚ̄` be an algebraic closure of `ℚ`, let `G = Gal(ℚ̄/ℚ)` be its absolute Galois group, and
let `U = Spec(ℚ̄) ×_{Spec(ℚ)} Spec(ℚ̄)`, viewed over its second factor. The group `G` acts on `U`
over `Spec(ℚ̄)` through the first factor, freely and transitively. The quotient `X = U/G` of
**Spaces, Definition 02Z3** is a reduced algebraic space over `Spec(ℚ̄)` with exactly one point,
which is not Noetherian — indeed not even locally Noetherian, because `ℚ̄ ⊗_ℚ ℚ̄` is not a
Noetherian ring. The composite `x : Spec(ℚ̄) ⟶ U ⟶ X` of the diagonal with the projection is a
finite type point of `X` (every point of `U` is closed) and a monomorphism. The substack of `X`
it cuts out is the one Stacks 06MR constructs for `X`, and its inclusion — equivalently `x`
itself — is not an isomorphism; and `Spec(ℚ̄) ⟶ X` is the residual gerbe of `X` at `x`.

## Main definitions

* `AlgebraicGeometry.RationalGaloisQuotient.selfFiberProduct` is `U`, the self-fibre-product of
  `Spec(ℚ̄)` over `Spec(ℚ)`, as a scheme over `Spec(ℚ̄)` through its second projection.
* `AlgebraicGeometry.RationalGaloisQuotient.selfFiberProductAction` is the action of
  `Gal(ℚ̄/ℚ)` on `U` over `Spec(ℚ̄)`, the base change of the Galois action on `Spec(ℚ̄)` along
  the structure morphism of `Spec(ℚ̄)`, and
  `AlgebraicGeometry.RationalGaloisQuotient.constantGaloisGroupScheme` is the acting group as a
  constant group scheme over `Spec(ℚ̄)` (**Stacks 03YW**).
* `AlgebraicGeometry.RationalGaloisQuotient.galoisSelfProductQuotient` is `X = U/G`, the
  library's quotient `AlgebraicGeometry.Space.actionQuotient` of **Stacks 02Z3**, and
  `AlgebraicGeometry.RationalGaloisQuotient.quotientProjection` is `U ⟶ X`.
* `AlgebraicGeometry.RationalGaloisQuotient.canonicalPoint` is the composite
  `x : Spec(ℚ̄) ⟶ U ⟶ X` of the diagonal with the projection, and
  `AlgebraicGeometry.RationalGaloisQuotient.canonicalFieldPoint` is the corresponding
  field-valued point of `X`.
* `AlgebraicGeometry.RationalGaloisQuotient.quotientStack` is `X` regarded as an algebraic
  stack over `Spec(ℚ̄)`, `AlgebraicGeometry.RationalGaloisQuotient.canonicalPointStack` is `x` as
  a 1-morphism of algebraic stacks, `AlgebraicGeometry.RationalGaloisQuotient.canonicalStackPoint`
  is the point `x ∈ |X|`, and `AlgebraicGeometry.RationalGaloisQuotient.canonicalPointSubstack`
  is the strictly full subcategory of `X` cut out by `x`, its essential image.

## Main results

* `…constantGaloisGroupSchemeAction_eq`, `…isFreeAction_constantGaloisGroupSchemeAction` and
  `…exists_smul_eq_constantGaloisGroupSchemeAction`: the constant group scheme `G` acts on `U`
  through the Galois action, freely and transitively.
* `…galoisGroupEquivSelfFiberProduct`: the points of `U` are in bijection with `Gal(ℚ̄/ℚ)`, the
  source's `U = Gal(ℚ̄/ℚ) × Spec(ℚ̄)` on underlying sets.
* `…selfFiberProductAction_actsFreely` and `…selfFiberProductAction_transitive`: `G` acts
  freely and transitively on `U`.
* `…isAlgebraicSpace_galoisSelfProductQuotient`, `…isReduced_galoisSelfProductQuotient`,
  `…not_isNoetherian_galoisSelfProductQuotient`,
  `…not_isLocallyNoetherian_galoisSelfProductQuotient` and
  `…nonempty_unique_points_galoisSelfProductQuotient`: `X` is a reduced, non-Noetherian (not even
  locally Noetherian) algebraic space with exactly one point, the class of `x`
  (`…eq_class_canonicalFieldPoint`).
* `…isClosed_singleton_selfFiberProduct`, `…isFiniteTypePoint_canonicalFieldPoint`,
  `…mono_canonicalPoint` and `…isMonomorphism_canonicalPointStack`: every point of `U` is closed,
  `x` is a finite type point of `X`, and `x` is a monomorphism, of sheaves and of algebraic stacks.
* `…not_isIso_canonicalPoint`: `x : Spec(ℚ̄) ⟶ X` is not an isomorphism.
* `…isReducedWithUniquePoint_quotientStack`: `X` as an algebraic stack satisfies the hypothesis
  of Stacks 06MR.
* `…isReducedLocallyNoetherianUniquePointSubstack_canonicalPointSubstack`,
  `…isReducedLocallyNoetherianUniquePointSubstack_iff_eq_canonicalPointSubstack` and
  `…le_canonicalPointSubstack`: **`x` is the morphism of Stacks 06MR** — the substack cut out by
  `x` is the unique strictly full subcategory of `X` with the properties of Lemma 06MR, `x`
  factors through its inclusion by an equivalence, and that inclusion is not an equivalence.
* `…isLocallyOfFiniteType_canonicalPoint`: `x : Spec(ℚ̄) ⟶ X` is locally of finite type.
* `…ne_and_isReducedUniquePointSubstackAt_canonicalPointSubstack_top`: **local Noetherianity is
  necessary in Definition 06MU** — without it, the substack cut out by `x` and all of `X` are two
  distinct reduced one-point substacks over `x` with monomorphic inclusions.
* `…not_isEquivalence_substackInclusion`: no substack inclusion of the kind Stacks 06MR produces
  for `X` is an equivalence.
* `…isResidualGerbeAt_canonicalPointSubstack`: **`Spec(ℚ̄) ⟶ X` is the residual gerbe of `X` at
  `x`** — it exists in the sense of Stacks 06MU (1) and the substack cut out by `x` meets the
  specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of Stacks 06MU (2).

## Implementation notes

`U` is the literal fibre product `(Over.pullback cover.hom).obj cover`, whose structure morphism
over `Spec(ℚ̄)` is the second projection and on which the Galois action therefore moves the first
projection. Everything about the scheme `U` itself is read off from the identification
`U ≅ Spec(ℚ̄ ⊗_ℚ ℚ̄)` of `AlgebraicGeometry.pullbackSpecIso`: reducedness from separability of
`ℚ̄/ℚ`, closedness of every point and failure of Noetherianity from integrality of `ℚ̄ ⊗_ℚ ℚ̄`
over `ℚ̄`, which makes every prime maximal. The primes of `ℚ̄ ⊗_ℚ ℚ̄` are exactly the kernels of
`x ⊗ y ↦ σ(x) y` for `σ ∈ Gal(ℚ̄/ℚ)`, distinct for distinct `σ` — this is the source's
`U = Gal(ℚ̄/ℚ) × Spec(ℚ̄)` on points — and `σ` acts on `U` as `Spec(σ⁻¹ ⊗ 1)`, which moves the
prime of `τ` to the prime of `τ σ⁻¹`; transitivity follows. A Noetherian ring of Krull dimension
zero is Artinian, hence has finitely many primes, while the group `Gal(ℚ̄/ℚ)` is infinite.

**Spaces, Definition 02Z3**, which the source cites for `U/G`, is formulated for an abstract
group `G` together with a homomorphism `G ⟶ Aut_S(U)` satisfying the freeness condition (*) of
**Stacks 02Z2**; that homomorphism is `selfFiberProductAction`, the library's quotient of 02Z3 is
`AlgebraicGeometry.Space.actionQuotient`, and freeness is (*) in the equivalent form
`AlgebraicGeometry.Space.actsFreelyOnNonemptyPoints_iff`. The source also views `G` as the
constant group scheme of Groupoids, Example 03YW, `constantGaloisGroupScheme`: the homomorphism
induces an action of that group scheme on `U` (`AlgebraicGeometry.constantGroupSchemeModObj`,
recorded here as `constantGaloisGroupSchemeAction`), which on the summand of `G ×_{Spec(ℚ̄)} U`
indexed by `σ` is `selfFiberProductAction σ`, and which is free in the sense of **Stacks 07S1**
and transitive on points. Freeness of the abstract action needs no computation with
`ℚ̄ ⊗_ℚ ℚ̄`: the first projection is equivariant for the Galois action on `Spec(ℚ̄)`, and freeness
on nonempty points pulls back along any equivariant morphism, so this library's **Stacks 02Z6**
already supplies it.

At the level of algebraic stacks, `x` is the 1-morphism of categories of elements induced by the
monomorphism of sheaves `x`, which is full and faithful. Its essential image is therefore the
substack of Stacks 06MR
(`AlgebraicGeometry.Stack.exists_isEquivalence_essImage_of_full_of_faithful`) and the residual
gerbe at the image of the point of `Spec(ℚ̄)`
(`AlgebraicGeometry.Stack.isResidualGerbeAt_essImage_of_full_of_faithful`). That it is the only
candidate is the uniqueness argument of Stacks 06MR, which needs the inclusions of strictly full
algebraic substacks of `X` to be monomorphisms; they are, as for every algebraic stack
(`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion`).

Sheafification on the big fppf site of `Spec(ℚ̄)`, which the quotient `X = U/G` needs, is not
assumed: it is `AlgebraicGeometry.hasSheafify_bigFppfOver`, used as a local instance.

## References

* [Stacks Project, Tag 06MS](https://stacks.math.columbia.edu/tag/06MS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.RationalGaloisQuotient

/-- **Stacks 06MS.** The self-fibre-product `U = Spec(ℚ̄) ×_{Spec(ℚ)} Spec(ℚ̄)`, as a scheme
over `Spec(ℚ̄)` through its second projection. -/
@[stacks 06MS "the self-fibre-product U of Spec(ℚ̄) over Spec(ℚ), over its second factor"]
abbrev selfFiberProduct : Over cover.left := (Over.pullback cover.hom).obj cover

/-- The coordinate ring `ℚ̄ ⊗_ℚ ℚ̄` of the self-fibre-product. -/
abbrev qbarTensor : Type := AlgebraicClosure ℚ ⊗[ℚ] AlgebraicClosure ℚ

/-- Evaluation of `ℚ̄ ⊗_ℚ ℚ̄` along a Galois element: `x ⊗ y ↦ σ(x) y`. It is the identity on
the second factor, the one the structure morphism to `Spec(ℚ̄)` comes from. -/
def tensorEval (σ : galoisGroup) : qbarTensor →ₐ[ℚ] AlgebraicClosure ℚ :=
  Algebra.TensorProduct.lift σ.toAlgHom (AlgHom.id ℚ (AlgebraicClosure ℚ))
    (fun _ _ ↦ .all _ _)

/-- `tensorEval σ` sends `x ⊗ y` to `σ(x) y`. -/
@[simp]
theorem tensorEval_tmul (σ : galoisGroup) (x y : AlgebraicClosure ℚ) :
    tensorEval σ (x ⊗ₜ[ℚ] y) = σ x * y := by
  simp [tensorEval]

/-- The prime ideal of `ℚ̄ ⊗_ℚ ℚ̄` cut out by a Galois element. -/
def tensorPrime (σ : galoisGroup) : PrimeSpectrum qbarTensor :=
  ⟨RingHom.ker (tensorEval σ).toRingHom, RingHom.ker_isPrime _⟩

/-- Distinct Galois elements cut out distinct primes of `ℚ̄ ⊗_ℚ ℚ̄`. -/
theorem tensorPrime_injective : Function.Injective tensorPrime := by
  intro σ τ h
  refine AlgEquiv.ext fun x ↦ ?_
  have hx : (x ⊗ₜ[ℚ] (1 : AlgebraicClosure ℚ)) -
      ((1 : AlgebraicClosure ℚ) ⊗ₜ[ℚ] σ x) ∈ (tensorPrime σ).asIdeal := by
    simp [tensorPrime, RingHom.mem_ker, tensorEval_tmul]
  rw [h] at hx
  exact (sub_eq_zero.mp (by simpa [tensorPrime, RingHom.mem_ker, tensorEval_tmul] using hx)).symm

/-- `ℚ̄ ⊗_ℚ ℚ̄` is integral over its left factor `ℚ̄`. -/
private theorem isIntegral_qbarTensor : Algebra.IsIntegral (AlgebraicClosure ℚ) qbarTensor := by
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isIntegral
  exact Algebra.IsIntegral.tensorProduct ℚ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)

/-- Every prime of `ℚ̄ ⊗_ℚ ℚ̄` is maximal, as it is integral over the field `ℚ̄`. -/
private theorem isMaximal_qbarTensor {q : Ideal qbarTensor} (hq : q.IsPrime) : q.IsMaximal := by
  have := isIntegral_qbarTensor
  exact Ideal.Quotient.maximal_of_isField q
    (isField_of_isIntegral_of_isField' (Field.toIsField (AlgebraicClosure ℚ)))

private theorem not_isNoetherianRing_qbarTensor : ¬ IsNoetherianRing qbarTensor := by
  intro h
  have := isIntegral_qbarTensor
  have hdim : Ring.KrullDimLE 0 qbarTensor :=
    Ring.krullDimLE_zero_iff.mpr fun q hq ↦ isMaximal_qbarTensor hq
  let : IsArtinianRing qbarTensor := isArtinianRing_iff_krullDimLE_zero.mpr hdim
  exact (not_finite_iff_infinite.mpr infinite_galoisGroup)
    (Finite.of_injective tensorPrime tensorPrime_injective)

/-- The self-fibre-product is the spectrum of `ℚ̄ ⊗_ℚ ℚ̄`. -/
def selfFiberProductIsoSpec :
    selfFiberProduct.left ≅ Spec (.of qbarTensor) :=
  pullbackSpecIso ℚ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)

/-- **Stacks 06MS.** The self-fibre-product `U` is not locally Noetherian: `ℚ̄ ⊗_ℚ ℚ̄` is a
ring of Krull dimension zero, so a Noetherian one would be Artinian and have finitely many
primes, whereas the infinite group `Gal(ℚ̄/ℚ)` injects into its primes. -/
@[stacks 06MS "the cover U is not locally Noetherian, the source's non-noetherianity of X \
read on its atlas"]
theorem not_isLocallyNoetherian_selfFiberProduct :
    ¬ IsLocallyNoetherian selfFiberProduct.left := by
  intro h
  have hspec : IsLocallyNoetherian (Spec (.of qbarTensor)) :=
    isLocallyNoetherian_of_isOpenImmersion selfFiberProductIsoSpec.inv
  exact not_isNoetherianRing_qbarTensor (isLocallyNoetherian_Spec.mp hspec)

/-- The self-fibre-product `U` is reduced, because `ℚ̄` is separable over `ℚ` and therefore
geometrically reduced. -/
theorem isReduced_selfFiberProduct : IsReduced selfFiberProduct.left := by
  have : _root_.IsReduced qbarTensor := isReduced_algebraicClosure_tensorProduct_rat
  have : IsReduced (Spec (.of qbarTensor)) := (affine_isReduced_iff _).mpr inferInstance
  exact isReduced_of_isOpenImmersion selfFiberProductIsoSpec.hom

/-- **Stacks 06MS.** Every point of the self-fibre-product `U` is closed: `ℚ̄ ⊗_ℚ ℚ̄` is
integral over the field `ℚ̄`, so each of its primes is maximal. -/
@[stacks 06MS "every point of U is closed"]
theorem isClosed_singleton_selfFiberProduct (x : selfFiberProduct.left) :
    IsClosed ({x} : Set selfFiberProduct.left) := by
  have := isIntegral_qbarTensor
  let e := Scheme.homeoOfIso selfFiberProductIsoSpec
  let q : PrimeSpectrum qbarTensor := e x
  let := q.2
  rw [← e.isClosed_image, Set.image_singleton]
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).2 (isMaximal_qbarTensor q.2)

/-- Every prime of `ℚ̄ ⊗_ℚ ℚ̄` is cut out by a Galois element: `ℚ̄ ⊗_ℚ ℚ̄` is integral over its
left factor, so the residue ring at a prime is a domain integral over the algebraically closed
field `ℚ̄`, hence equal to it; the right factor then maps to it by a `ℚ`-embedding `σ` of `ℚ̄`,
which is an automorphism, and the prime is the kernel of `x ⊗ y ↦ σ⁻¹(x) y`. -/
theorem tensorPrime_surjective : Function.Surjective tensorPrime := by
  intro q
  let := q.2
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have := isIntegral_qbarTensor
  let e : AlgebraicClosure ℚ ≃+* qbarTensor ⧸ q.asIdeal :=
    RingEquiv.ofBijective (algebraMap _ _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let χ : qbarTensor →ₐ[ℚ] AlgebraicClosure ℚ :=
    (e.symm.toRingHom.comp (Ideal.Quotient.mk q.asIdeal)).toRatAlgHom
  have hχ : ∀ a, χ a = 0 ↔ a ∈ q.asIdeal := fun a ↦ by
    change e.symm (Ideal.Quotient.mk q.asIdeal a) = 0 ↔ _
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hleft : ∀ x : AlgebraicClosure ℚ, χ (x ⊗ₜ[ℚ] 1) = x := fun x ↦
    e.symm_apply_eq.mpr rfl
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ :=
    χ.comp Algebra.TensorProduct.includeRight
  let σ : galoisGroup := AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)
  have hχσ : (σ⁻¹ : galoisGroup).toAlgHom.comp χ = tensorEval σ⁻¹ := by
    refine Algebra.TensorProduct.ext' fun x y ↦ ?_
    have hxy : x ⊗ₜ[ℚ] y = (x ⊗ₜ[ℚ] (1 : AlgebraicClosure ℚ)) *
        ((1 : AlgebraicClosure ℚ) ⊗ₜ[ℚ] y) := by
      simp
    have hy : χ ((1 : AlgebraicClosure ℚ) ⊗ₜ[ℚ] y) = σ y := rfl
    rw [tensorEval_tmul, AlgHom.comp_apply, hxy, map_mul, hleft, hy]
    simp
  refine ⟨σ⁻¹, PrimeSpectrum.ext (Ideal.ext fun a ↦ ?_)⟩
  change a ∈ RingHom.ker (tensorEval σ⁻¹).toRingHom ↔ a ∈ q.asIdeal
  rw [RingHom.mem_ker, ← hχ, ← hχσ]
  change (σ⁻¹ : galoisGroup) (χ a) = 0 ↔ χ a = 0
  exact map_eq_zero_iff _ (σ⁻¹ : galoisGroup).injective

/-- The ring automorphism `σ⁻¹ ⊗ 1` of `ℚ̄ ⊗_ℚ ℚ̄`, through which a Galois element `σ` acts on
the spectrum of `ℚ̄ ⊗_ℚ ℚ̄` under the identification with `U`. -/
private def tensorAut (σ : galoisGroup) : qbarTensor →ₐ[ℚ] qbarTensor :=
  Algebra.TensorProduct.map (σ⁻¹ : galoisGroup).toAlgHom (AlgHom.id ℚ (AlgebraicClosure ℚ))

/-- Pulling the prime of `τ` back along `σ⁻¹ ⊗ 1` gives the prime of `τ σ⁻¹`. -/
private theorem comap_tensorAut_tensorPrime (σ τ : galoisGroup) :
    PrimeSpectrum.comap (tensorAut σ).toRingHom (tensorPrime τ) = tensorPrime (τ * σ⁻¹) := by
  have h : (tensorEval τ).comp (tensorAut σ) = tensorEval (τ * σ⁻¹) :=
    Algebra.TensorProduct.ext' fun x y ↦ by
      simp [tensorAut, tensorEval_tmul]
  refine PrimeSpectrum.ext (Ideal.ext fun a ↦ ?_)
  change tensorAut σ a ∈ RingHom.ker (tensorEval τ).toRingHom ↔
    a ∈ RingHom.ker (tensorEval (τ * σ⁻¹)).toRingHom
  rw [RingHom.mem_ker, RingHom.mem_ker, ← h]
  rfl

/-- **Stacks 06MS.** The points of `U = Spec(ℚ̄) ×_{Spec(ℚ)} Spec(ℚ̄)` are in bijection with
`Gal(ℚ̄/ℚ)`: `σ` goes to the point cut out by the kernel of `x ⊗ y ↦ σ(x) y`. This is the source's
`U = Gal(ℚ̄/ℚ) × Spec(ℚ̄)` on underlying sets. -/
@[stacks 06MS "U = Gal(ℚ̄/ℚ) × Spec(ℚ̄) on points: the points of U are in bijection with the \
absolute Galois group"]
def galoisGroupEquivSelfFiberProduct : galoisGroup ≃ selfFiberProduct.left :=
  (Equiv.ofBijective tensorPrime ⟨tensorPrime_injective, tensorPrime_surjective⟩).trans
    (Scheme.homeoOfIso selfFiberProductIsoSpec).symm.toEquiv

universe w

variable (B₀ : BigFppfSite.{0}) (hQ : B₀.Contains base) (hK : B₀.Contains cover.left)

/-- **Stacks 06MS.** The action of `Gal(ℚ̄/ℚ)` on the self-fibre-product `U` over `Spec(ℚ̄)`:
the base change along the structure morphism of `Spec(ℚ̄)` of the Galois action on `Spec(ℚ̄)`,
so it moves the first projection and fixes the second. -/
@[stacks 06MS "the action of the absolute Galois group on U over Spec(ℚ̄)"]
def selfFiberProductAction : galoisGroup →* Aut selfFiberProduct :=
  ((Over.pullback cover.hom).mapAut cover).comp (galoisAction B₀ hQ hK)

/-- **Stacks 06MS.** The absolute Galois group of `ℚ` with the discrete topology, viewed as a
constant group scheme over `Spec(ℚ̄)` as in **Stacks 03YW**. This is the group scheme `G` the
source lets act on `U`. -/
@[stacks 06MS "G: the absolute Galois group with the discrete topology as a constant group \
scheme over Spec(ℚ̄)"]
abbrev constantGaloisGroupScheme : Grp (Over cover.left) :=
  constantGroupScheme galoisGroup cover.left

private theorem selfFiberProductAction_hom_left_fst (σ : galoisGroup) :
    (selfFiberProductAction B₀ hQ hK σ).hom.left ≫ pullback.fst cover.hom cover.hom =
      pullback.fst cover.hom cover.hom ≫ (galoisAction B₀ hQ hK σ).hom.left :=
  pullback.lift_fst _ _ _

/-- **Stacks 06MS.** The Galois group acts freely on the self-fibre-product `U`: the first
projection `U ⟶ Spec(ℚ̄)` is equivariant, and the Galois action on `Spec(ℚ̄)` is already free by
this library's **Stacks 02Z6**. -/
@[stacks 06MS "G acts freely on U"]
theorem selfFiberProductAction_actsFreely :
    Space.ActsFreelyOnNonemptyPoints selfFiberProduct galoisGroup
      (selfFiberProductAction B₀ hQ hK) := by
  have hbase : Space.ActsFreelyOnNonemptyPoints _ galoisGroup (galoisAction B₀ hQ hK) :=
    (Space.actsFreelyOnNonemptyPoints_iff _ galoisGroup (galoisAction B₀ hQ hK)).mpr
      (galoisAction_nontrivialOnFixedResidueFields B₀ hQ hK)
  intro T hT x g g' h
  refine hbase (Over.mk ((x.left ≫ pullback.fst cover.hom cover.hom) ≫ cover.hom)) hT
    (Over.homMk (x.left ≫ pullback.fst cover.hom cover.hom)) g g' ?_
  apply Over.OverMorphism.ext
  have hcongr := congrArg
    (fun φ : T ⟶ selfFiberProduct ↦ φ.left ≫ pullback.fst cover.hom cover.hom) h
  simp only [Over.comp_left, Category.assoc, selfFiberProductAction_hom_left_fst] at hcongr
  simp only [Over.comp_left, Over.homMk_left]
  exact hcongr

private theorem selfFiberProductAction_hom_left_snd (σ : galoisGroup) :
    (selfFiberProductAction B₀ hQ hK σ).hom.left ≫ pullback.snd cover.hom cover.hom =
      pullback.snd cover.hom cover.hom :=
  Over.w (selfFiberProductAction B₀ hQ hK σ).hom

/-- Under the identification `U ≅ Spec(ℚ̄ ⊗_ℚ ℚ̄)`, a Galois element `σ` acts on `U` as `Spec` of
`σ⁻¹ ⊗ 1`: both are morphisms to a fibre product, and they agree after either projection. -/
private theorem selfFiberProductAction_hom_left_eq (σ : galoisGroup) :
    (selfFiberProductAction B₀ hQ hK σ).hom.left =
      selfFiberProductIsoSpec.hom ≫ Spec.map (CommRingCat.ofHom (tensorAut σ).toRingHom) ≫
        selfFiberProductIsoSpec.inv := by
  have hinvfst : selfFiberProductIsoSpec.inv ≫ pullback.fst cover.hom cover.hom =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ℚ) (A := AlgebraicClosure ℚ) (B := AlgebraicClosure ℚ))) :=
    pullbackSpecIso_inv_fst ℚ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)
  have hinvsnd : selfFiberProductIsoSpec.inv ≫ pullback.snd cover.hom cover.hom =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := ℚ) (A := AlgebraicClosure ℚ) (B := AlgebraicClosure ℚ)).toRingHom) :=
    pullbackSpecIso_inv_snd ℚ (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)
  have hgal : (galoisAction B₀ hQ hK σ).hom.left =
      Spec.map (CommRingCat.ofHom (σ⁻¹ : galoisGroup).toRingEquiv.toRingHom) := rfl
  apply pullback.hom_ext
  · rw [selfFiberProductAction_hom_left_fst, Category.assoc, Category.assoc, hinvfst,
      ← Spec.map_comp, hgal]
    have hring : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
        CommRingCat.ofHom (tensorAut σ).toRingHom =
        CommRingCat.ofHom (σ⁻¹ : galoisGroup).toRingEquiv.toRingHom ≫
          CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := ℚ) (A := AlgebraicClosure ℚ) (B := AlgebraicClosure ℚ)) := by
      ext x
      simp [tensorAut]
    rw [hring, Spec.map_comp, ← hinvfst]
    exact congrArg (· ≫ _) (Iso.hom_inv_id_assoc selfFiberProductIsoSpec _).symm
  · rw [selfFiberProductAction_hom_left_snd, Category.assoc, Category.assoc, hinvsnd,
      ← Spec.map_comp]
    have hring : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := ℚ) (A := AlgebraicClosure ℚ) (B := AlgebraicClosure ℚ)).toRingHom ≫
        CommRingCat.ofHom (tensorAut σ).toRingHom =
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := ℚ) (A := AlgebraicClosure ℚ) (B := AlgebraicClosure ℚ)).toRingHom := by
      ext x
      simp [tensorAut]
    rw [hring, ← hinvsnd, Iso.hom_inv_id_assoc]

/-- **Stacks 06MS.** The Galois group acts transitively on the points of `U`: every prime of
`ℚ̄ ⊗_ℚ ℚ̄` is the kernel of `x ⊗ y ↦ τ(x) y` for some Galois element `τ`, and `σ` moves the
prime of `τ` to the prime of `τ σ⁻¹`. -/
@[stacks 06MS "G acts transitively on U"]
theorem selfFiberProductAction_transitive (x y : selfFiberProduct.left) :
    ∃ σ : galoisGroup, (selfFiberProductAction B₀ hQ hK σ).hom.left x = y := by
  let e := selfFiberProductIsoSpec
  obtain ⟨τ₁, h₁⟩ := tensorPrime_surjective (e.hom x)
  obtain ⟨τ₂, h₂⟩ := tensorPrime_surjective (e.hom y)
  refine ⟨τ₂⁻¹ * τ₁, ?_⟩
  rw [selfFiberProductAction_hom_left_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← h₁]
  change e.inv (PrimeSpectrum.comap (tensorAut (τ₂⁻¹ * τ₁)).toRingHom (tensorPrime τ₁)) = y
  rw [comap_tensorAut_tensorPrime, mul_inv_rev, inv_inv, mul_inv_cancel_left, h₂]
  exact (Scheme.homeoOfIso e).symm_apply_apply y

section ConstantGroupSchemeAction

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

/-- **Stacks 06MS.** The action of `G`, viewed as the constant group scheme over `Spec(ℚ̄)` of
**Stacks 03YW**, on `U` (**Stacks 022Z**): the action map `G ×_{Spec(ℚ̄)} U ⟶ U` which on the
summand of `G ×_{Spec(ℚ̄)} U` indexed by `σ` is the automorphism `selfFiberProductAction σ`. -/
@[stacks 06MS "the action of G, as the constant group scheme over Spec(ℚ̄), on U"]
abbrev constantGaloisGroupSchemeAction : ModObj constantGaloisGroupScheme.X selfFiberProduct :=
  constantGroupSchemeModObj selfFiberProduct (selfFiberProductAction B₀ hQ hK)

/-- **Stacks 06MS.** The action of the constant group scheme `G` on `U` restricts, on the summand
of `G ×_{Spec(ℚ̄)} U` indexed by `σ ∈ Gal(ℚ̄/ℚ)`, to the automorphism `selfFiberProductAction σ`;
and the constant `T`-point `σ` of `G` acts on the `T`-points of `U` by composition with it. -/
@[stacks 06MS "the action of the constant group scheme G on U is the Galois action on summands \
and on constant points"]
theorem constantGaloisGroupSchemeAction_eq (σ : galoisGroup) :
    letI := constantGaloisGroupSchemeAction B₀ hQ hK
    constantGroupSchemeLeg selfFiberProduct σ ≫ γ[constantGaloisGroupScheme.X, selfFiberProduct] =
        (selfFiberProductAction B₀ hQ hK σ).hom ∧
      ∀ {T : Over cover.left} (x : T ⟶ selfFiberProduct),
        (toUnit T ≫ constantGroupSchemePoint galoisGroup cover.left σ :
            T ⟶ constantGaloisGroupScheme.X) • x =
          x ≫ (selfFiberProductAction B₀ hQ hK σ).hom :=
  ⟨constantGroupSchemeLeg_smul _ _ σ, fun x ↦ constantGroupSchemePoint_smul _ _ σ x⟩

/-- **Stacks 06MS.** The constant group scheme `G` acts freely on `U`, in the sense of
**Stacks 07S1**: for every scheme `T` over `Spec(ℚ̄)` the group `G(T)` of locally constant maps
`T → Gal(ℚ̄/ℚ)` acts freely on `U(T)`. -/
@[stacks 06MS "the constant group scheme G acts freely on U"]
theorem isFreeAction_constantGaloisGroupSchemeAction :
    letI := constantGaloisGroupSchemeAction B₀ hQ hK
    IsFreeAction constantGaloisGroupScheme.X selfFiberProduct :=
  isFreeAction_constantGroupSchemeModObj _ _ (selfFiberProductAction_actsFreely B₀ hQ hK)

/-- **Stacks 06MS.** The constant group scheme `G` acts transitively on `U`: for any two points
`u, v` of `U` some point of `G ×_{Spec(ℚ̄)} U` lies over `u` under the projection and over `v`
under the action map. -/
@[stacks 06MS "the constant group scheme G acts transitively on U"]
theorem exists_smul_eq_constantGaloisGroupSchemeAction (u v : selfFiberProduct.left) :
    letI := constantGaloisGroupSchemeAction B₀ hQ hK
    ∃ z : (constantGaloisGroupScheme.X ⊗ selfFiberProduct).left,
      (snd constantGaloisGroupScheme.X selfFiberProduct).left z = u ∧
        (γ[constantGaloisGroupScheme.X, selfFiberProduct]).left z = v :=
  exists_smul_eq_constantGroupSchemeModObj _ _ (selfFiberProductAction_transitive B₀ hQ hK) u v

end ConstantGroupSchemeAction

/-- The condition (*) of **Stacks 02Z2** for the Galois action on `U`, the form the quotient
constructions consume. -/
theorem selfFiberProductAction_actsNontrivially :
    Space.ActsNontriviallyOnFixedResidueFields selfFiberProduct galoisGroup
      (selfFiberProductAction B₀ hQ hK) :=
  (Space.actsFreelyOnNonemptyPoints_iff selfFiberProduct galoisGroup
    (selfFiberProductAction B₀ hQ hK)).mp (selfFiberProductAction_actsFreely B₀ hQ hK)

section Quotient

variable (B : BigFppfSite.{0}) (hS : B.Contains cover.left)
  (hU : B.Contains selfFiberProduct.left)

/-- The self-fibre-product `U` as an object of a big fppf site over `Spec(ℚ̄)`. -/
def siteSelfFiberProduct : BigFppfOver B cover.left hS :=
  Over.mk (ObjectProperty.homMk selfFiberProduct.hom : B.obj hU ⟶ B.obj hS)

/-- The diagonal `Spec(ℚ̄) ⟶ U`, a section of the second projection. -/
def siteDiagonal : Space.baseTerminal B cover.left hS ⟶ siteSelfFiberProduct B hS hU :=
  Over.homMk (ObjectProperty.homMk (pullback.diagonal cover.hom))
    (ObjectProperty.hom_ext _ (pullback.diagonal_snd cover.hom))

include B₀ hQ hK in
private theorem contains_relationScheme :
    B.Contains (Space.actionRelationScheme
      (Space.underlyingOver B hS (siteSelfFiberProduct B hS hU)) galoisGroup).left :=
  Space.contains_actionRelationScheme galoisGroup B hS (siteSelfFiberProduct B hS hU)
    (selfFiberProductAction B₀ hQ hK) (selfFiberProductAction_actsNontrivially B₀ hQ hK)

/-- The source map of the graph relation of the Galois action on `U`. -/
private def relSource : Space.siteActionRelationScheme galoisGroup B hS
    (siteSelfFiberProduct B hS hU) (contains_relationScheme B₀ hQ hK B hS hU) ⟶
      siteSelfFiberProduct B hS hU :=
  Space.siteActionRelationSource galoisGroup B hS (siteSelfFiberProduct B hS hU)
    (contains_relationScheme B₀ hQ hK B hS hU)

/-- The target map of the graph relation of the Galois action on `U`. -/
private def relTarget : Space.siteActionRelationScheme galoisGroup B hS
    (siteSelfFiberProduct B hS hU) (contains_relationScheme B₀ hQ hK B hS hU) ⟶
      siteSelfFiberProduct B hS hU :=
  Space.siteActionRelationTarget galoisGroup B hS (siteSelfFiberProduct B hS hU)
    (contains_relationScheme B₀ hQ hK B hS hU) (selfFiberProductAction B₀ hQ hK)

private theorem relation_eq_actionRelation :
    Space.relation B cover.left hS (relSource B₀ hQ hK B hS hU)
        (relTarget B₀ hQ hK B hS hU) =
      Space.actionRelation (Space.underlyingOver B hS (siteSelfFiberProduct B hS hU))
        galoisGroup (selfFiberProductAction B₀ hQ hK) := rfl

private theorem isEtaleEquivalenceRelation_relation :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (Space.relation B cover.left hS (relSource B₀ hQ hK B hS hU)
        (relTarget B₀ hQ hK B hS hU)) := by
  rw [relation_eq_actionRelation]
  exact Space.actionRelation_isEtaleEquivalenceRelation _ galoisGroup
    (selfFiberProductAction B₀ hQ hK) (selfFiberProductAction_actsNontrivially B₀ hQ hK)

/- Sheafification on the big fppf site of `Spec(ℚ̄)` exists: the site is essentially small. -/
attribute [local instance] hasSheafify_bigFppfOver

/-- **Stacks 06MS.** The algebraic space `X = U/G` of the example: the fppf sheaf quotient of
the self-fibre-product by the Galois action, as in **Stacks 02Z3**. -/
@[stacks 06MS "X = U/G, the fppf sheaf quotient"]
abbrev galoisSelfProductQuotient : (BigFppfOver B cover.left hS)ᵒᵖ ⥤ Type 0 :=
  Space.actionQuotient galoisGroup B hS (siteSelfFiberProduct B hS hU)
    (selfFiberProductAction B₀ hQ hK)

/-- **Stacks 06MS.** `X = U/G` is an algebraic space over `Spec(ℚ̄)`; this is the source's
remark that the example is even an algebraic space. -/
@[stacks 06MS "X is an algebraic space"]
theorem isAlgebraicSpace_galoisSelfProductQuotient :
    IsAlgebraicSpace B cover.left hS (galoisSelfProductQuotient B₀ hQ hK B hS hU) :=
  Space.isAlgebraicSpace_actionQuotient_unconditional galoisGroup B hS
    (siteSelfFiberProduct B hS hU) (selfFiberProductAction B₀ hQ hK)
    (selfFiberProductAction_actsNontrivially B₀ hQ hK)

/-- The projection `U ⟶ X` of the self-fibre-product onto its Galois quotient. -/
abbrev quotientProjection :
    yoneda.obj (siteSelfFiberProduct B hS hU) ⟶ galoisSelfProductQuotient B₀ hQ hK B hS hU :=
  Space.actionProjection galoisGroup B hS (siteSelfFiberProduct B hS hU)
    (selfFiberProductAction B₀ hQ hK)

private theorem quotientProjection_eq :
    quotientProjection B₀ hQ hK B hS hU =
      Space.quotientMap B cover.left hS (relSource B₀ hQ hK B hS hU)
        (relTarget B₀ hQ hK B hS hU) :=
  (Space.quotientMap_eq_actionProjection galoisGroup B hS (siteSelfFiberProduct B hS hU)
    (selfFiberProductAction B₀ hQ hK) (contains_relationScheme B₀ hQ hK B hS hU)).symm

/-- The projection `U ⟶ X` is étale, by **Stacks 02WW**. -/
theorem etale_quotientProjection :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{0} : MorphismProperty Scheme.{0})
      (BigFppfOver.toScheme B cover.left hS))) (quotientProjection B₀ hQ hK B hS hU) := by
  have := isEtaleEquivalenceRelation_relation B₀ hQ hK B hS hU
  rw [quotientProjection_eq]
  exact Space.quotientMap_etale_unconditional B cover.left hS
    (relSource B₀ hQ hK B hS hU) (relTarget B₀ hQ hK B hS hU)

/-- The projection `U ⟶ X` is surjective, by **Stacks 02WW**. -/
theorem surjective_quotientProjection :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{0} : MorphismProperty Scheme.{0})
      (BigFppfOver.toScheme B cover.left hS))) (quotientProjection B₀ hQ hK B hS hU) := by
  have := isEtaleEquivalenceRelation_relation B₀ hQ hK B hS hU
  rw [quotientProjection_eq]
  exact Space.quotientMap_surjective_unconditional B cover.left hS
    (relSource B₀ hQ hK B hS hU) (relTarget B₀ hQ hK B hS hU)

/-- **Stacks 06MS.** `X` is not locally Noetherian: `U ⟶ X` is an étale atlas, and an
étale-local property of an algebraic space holds on every étale chart as soon as it holds at
all, while `U` is not locally Noetherian. -/
@[stacks 06MS "X is not locally Noetherian, the failure Definition 06MU excludes"]
theorem not_isLocallyNoetherian_galoisSelfProductQuotient :
    ¬ Space.HasEtaleLocalProperty B cover.left hS
      (galoisSelfProductQuotient B₀ hQ hK B hS hU)
      (fun T : Scheme.{0} ↦ IsLocallyNoetherian T) := by
  intro h
  exact not_isLocallyNoetherian_selfFiberProduct
    ((Space.exists_atlas_iff_forall_etale B cover.left hS _ _
      (isAlgebraicSpace_galoisSelfProductQuotient B₀ hQ hK B hS hU)).mp h
      (siteSelfFiberProduct B hS hU) (quotientProjection B₀ hQ hK B hS hU)
      (etale_quotientProjection B₀ hQ hK B hS hU))

/-- **Stacks 06MS.** The morphism `x : Spec(ℚ̄) ⟶ U ⟶ X` of the example: the diagonal followed
by the projection onto the quotient. -/
@[stacks 06MS "the morphism x : Spec(ℚ̄) ⟶ U ⟶ X"]
def canonicalPoint :
    yoneda.obj (Space.baseTerminal B cover.left hS) ⟶ galoisSelfProductQuotient B₀ hQ hK B hS hU :=
  yoneda.map (siteDiagonal B hS hU) ≫ quotientProjection B₀ hQ hK B hS hU

/-- **Stacks 06MS, the point of the example.** The morphism `x : Spec(ℚ̄) ⟶ X` is *not* an
isomorphism. If it were, `X` would be represented by `Spec(ℚ̄)`, hence locally Noetherian; but
`X` is not locally Noetherian. -/
@[stacks 06MS "x is not an isomorphism"]
theorem not_isIso_canonicalPoint : ¬ IsIso (canonicalPoint B₀ hQ hK B hS hU) := by
  intro h
  exact not_isLocallyNoetherian_galoisSelfProductQuotient B₀ hQ hK B hS hU <|
    (Space.exists_atlas_iff_of_representable B cover.left hS _
      (fun T : Scheme.{0} ↦ IsLocallyNoetherian T) (Space.baseTerminal B cover.left hS)
      (asIso (canonicalPoint B₀ hQ hK B hS hU)).symm).mpr
      (isLocallyNoetherian_Spec.mpr (inferInstance : IsNoetherianRing (AlgebraicClosure ℚ)))

/-- **Stacks 06MS.** `X` is reduced, witnessed by the reduced étale atlas `U ⟶ X`. -/
@[stacks 06MS "X is reduced"]
theorem isReduced_galoisSelfProductQuotient :
    Space.HasEtaleLocalProperty B cover.left hS
      (galoisSelfProductQuotient B₀ hQ hK B hS hU)
      (fun T : Scheme.{0} ↦ IsReduced T) :=
  ⟨siteSelfFiberProduct B hS hU, quotientProjection B₀ hQ hK B hS hU,
    surjective_quotientProjection B₀ hQ hK B hS hU,
    etale_quotientProjection B₀ hQ hK B hS hU, isReduced_selfFiberProduct⟩

/-- **Stacks 06MS.** `X` is not a Noetherian algebraic space in the sense of **Stacks 03EA**,
because it is not locally Noetherian. -/
@[stacks 06MS "X is non-noetherian"]
theorem not_isNoetherian_galoisSelfProductQuotient (hZ : B.Contains (⊤_ Scheme.{0})) :
    ¬ Space.IsNoetherian B cover.left hS hZ (galoisSelfProductQuotient B₀ hQ hK B hS hU) :=
  fun h ↦ not_isLocallyNoetherian_galoisSelfProductQuotient B₀ hQ hK B hS hU h.2.2

/-- **Stacks 06MS.** The morphism `x : Spec(ℚ̄) ⟶ X` is a monomorphism, because `Spec(ℚ̄)` is
the terminal object of the big fppf site over `Spec(ℚ̄)`: this is the source's remark that `x`
is a monomorphism since `X` is an algebraic space over `ℚ̄`. -/
@[stacks 06MS "x is a monomorphism"]
theorem mono_canonicalPoint : Mono (canonicalPoint B₀ hQ hK B hS hU) :=
  ⟨fun u v _ ↦ (Space.baseTerminal_yonedaIsTerminal B cover.left hS).hom_ext u v⟩

/-- The morphism `x : Spec(ℚ̄) ⟶ X` read as a field-valued point of `X`. -/
def canonicalFieldPoint :
    Space.FieldValuedPoint B cover.left hS (galoisSelfProductQuotient B₀ hQ hK B hS hU) where
  carrier := AlgebraicClosure ℚ
  contained := hS
  toBase := 𝟙 cover.left
  value := (canonicalPoint B₀ hQ hK B hS hU).app (op (Space.baseTerminal B cover.left hS))
    (𝟙 (Space.baseTerminal B cover.left hS))

/-- **Stacks 06MS.** `X` has a point, namely the class of `x`; with
`AlgebraicGeometry.RationalGaloisQuotient.subsingleton_points_galoisSelfProductQuotient` it is the
only one. -/
@[stacks 06MS "X has a point"]
theorem nonempty_points_galoisSelfProductQuotient :
    Nonempty (Space.points B cover.left hS (galoisSelfProductQuotient B₀ hQ hK B hS hU)) :=
  ⟨(canonicalFieldPoint B₀ hQ hK B hS hU).class B cover.left hS _⟩

/-- **Stacks 06MS.** The class of `x` is a finite type point of `X` in the sense of
**Stacks 06EG**: it is the image of the closed point of `U` cut out by the diagonal under the
étale chart `U ⟶ X`. -/
@[stacks 06MS "x is a (locally) finite type point of X"]
theorem isFiniteTypePoint_canonicalFieldPoint :
    Space.IsFiniteTypePoint B cover.left hS (galoisSelfProductQuotient B₀ hQ hK B hS hU)
      ((canonicalFieldPoint B₀ hQ hK B hS hU).class B cover.left hS _) := by
  let p : Space.FieldValuedPoint B cover.left hS
      (yoneda.obj (siteSelfFiberProduct B hS hU)) :=
    { carrier := AlgebraicClosure ℚ
      contained := hS
      toBase := 𝟙 cover.left
      value := siteDiagonal B hS hU }
  refine (Space.isFiniteTypePoint_iff_exists_isClosed_etaleChart B cover.left hS _
    (isAlgebraicSpace_galoisSelfProductQuotient B₀ hQ hK B hS hU) _).mpr
    ⟨siteSelfFiberProduct B hS hU, quotientProjection B₀ hQ hK B hS hU, p,
      Space.isEtale_of_presheaf_etale B cover.left hS
        (etale_quotientProjection B₀ hQ hK B hS hU),
      isClosed_singleton_selfFiberProduct _, ?_⟩
  simp only [Space.pointsMap_class, Space.FieldValuedPoint.map,
    canonicalFieldPoint, canonicalPoint, p, NatTrans.comp_app, yoneda_map_app,
    ConcreteCategory.comp_apply]
  rfl

/-- **Stacks 06MS.** The algebraic space `X = U/G` has at most one point.

Every point of `X` comes from a point of the atlas `U`, the atlas being surjective on points;
the Galois action is transitive on the points of `U`
(`AlgebraicGeometry.RationalGaloisQuotient.selfFiberProductAction_transitive`) and the
projection `U ⟶ X` is invariant under it. -/
theorem subsingleton_points_galoisSelfProductQuotient :
    Subsingleton
      (Space.points B cover.left hS (galoisSelfProductQuotient B₀ hQ hK B hS hU)) := by
  have hsurj : Function.Surjective (Space.pointsMap B cover.left hS
      (yoneda.obj (siteSelfFiberProduct B hS hU))
      (quotientProjection B₀ hQ hK B hS hU)) :=
    (Space.surjective_iff_surjective_pointsMap B cover.left hS _
      (isAlgebraicSpace_galoisSelfProductQuotient B₀ hQ hK B hS hU)
      (siteSelfFiberProduct B hS hU) (quotientProjection B₀ hQ hK B hS hU)).mp
      (surjective_quotientProjection B₀ hQ hK B hS hU)
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  obtain ⟨σ, hσ⟩ := selfFiberProductAction_transitive B₀ hQ hK
    (Space.pointsToScheme B cover.left hS (siteSelfFiberProduct B hS hU) x)
    (Space.pointsToScheme B cover.left hS (siteSelfFiberProduct B hS hU) y)
  have hleft : (BigFppfOver.toScheme B cover.left hS).map
      (Space.siteActionHom galoisGroup B hS (siteSelfFiberProduct B hS hU)
        (selfFiberProductAction B₀ hQ hK) σ) =
      (selfFiberProductAction B₀ hQ hK σ).hom.left :=
    congrArg Over.Hom.left (Space.post_map_siteActionHom galoisGroup B hS
      (siteSelfFiberProduct B hS hU) (selfFiberProductAction B₀ hQ hK) σ)
  have hmap : Space.pointsMap B cover.left hS
      (yoneda.obj (siteSelfFiberProduct B hS hU))
      (yoneda.map (Space.siteActionHom galoisGroup B hS (siteSelfFiberProduct B hS hU)
        (selfFiberProductAction B₀ hQ hK) σ)) x = y := by
    refine (Space.bijective_pointsToScheme B cover.left hS
      (siteSelfFiberProduct B hS hU)).1 ?_
    rw [Space.pointsToScheme_pointsMap_yoneda, hleft]
    exact hσ
  have key := congrArg
    (fun γ ↦ Space.pointsMap B cover.left hS
      (yoneda.obj (siteSelfFiberProduct B hS hU)) γ x)
    (Space.siteActionHom_comp_actionProjection galoisGroup B hS
      (siteSelfFiberProduct B hS hU) (selfFiberProductAction B₀ hQ hK) σ)
  simpa only [Space.pointsMap_comp, Function.comp_apply, hmap] using key.symm

/-- **Stacks 06MS.** The algebraic space `X = U/G` has exactly one point, and it is the class of
`x : Spec(ℚ̄) ⟶ X`. -/
@[stacks 06MS "X has exactly one point, namely the class of x"]
theorem eq_class_canonicalFieldPoint
    (p : Space.points B cover.left hS (galoisSelfProductQuotient B₀ hQ hK B hS hU)) :
    p = (canonicalFieldPoint B₀ hQ hK B hS hU).class B cover.left hS _ :=
  (subsingleton_points_galoisSelfProductQuotient B₀ hQ hK B hS hU).elim _ _

/-- **Stacks 06MS.** The space of points of `X = U/G` is a singleton. -/
@[stacks 06MS "X has exactly one point"]
theorem nonempty_unique_points_galoisSelfProductQuotient :
    Nonempty (Unique
      (Space.points B cover.left hS (galoisSelfProductQuotient B₀ hQ hK B hS hU))) :=
  ⟨{ default := (canonicalFieldPoint B₀ hQ hK B hS hU).class B cover.left hS _
     uniq := eq_class_canonicalFieldPoint B₀ hQ hK B hS hU }⟩

/-- `X` regarded as an algebraic stack over `Spec(ℚ̄)`, the object **Stacks 06MR** speaks
about. -/
abbrev quotientStack : Stack.AlgebraicStacks.{0, w} B cover.left hS :=
  Stack.algebraicSpaceStack B cover.left hS (galoisSelfProductQuotient B₀ hQ hK B hS hU)
    (isAlgebraicSpace_galoisSelfProductQuotient B₀ hQ hK B hS hU)

private instance isLocal_isLocallyNoetherian_smooth :
    ObjectProperty.IsLocal (fun X : Scheme.{0} ↦ IsLocallyNoetherian X)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{0})) :=
  ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage

/-- `X`, as an algebraic stack, is not locally Noetherian: a smooth scheme atlas with locally
Noetherian source would be an étale-local witness of local Noetherianity for the algebraic
space `X`, which has none. -/
theorem not_isLocallyNoetherianStack_quotientStack :
    ¬ Stack.IsLocallyNoetherianStack B cover.left hS
      (quotientStack.{w} B₀ hQ hK B hS hU) := by
  intro h
  exact not_isLocallyNoetherian_galoisSelfProductQuotient B₀ hQ hK B hS hU
    ((Stack.scheme_atlas_iff_etaleLocalProperty B cover.left hS
      (fun X : Scheme.{0} ↦ IsLocallyNoetherian X)
      (galoisSelfProductQuotient B₀ hQ hK B hS hU)
      (isAlgebraicSpace_galoisSelfProductQuotient B₀ hQ hK B hS hU)).mp h)

/-- **Stacks 06MS, the assertion about the morphism of Stacks 06MR.** Let `P` be any object
property of `X` of the kind **Stacks 06MR** produces, that is one which is closed under
isomorphism and cuts out an algebraic stack satisfying condition (2) of **Stacks 06MP**. Then
the inclusion `X_P ⟶ X` is *not* an equivalence over the big fppf site, which is this library's
notion of an isomorphism of algebraic stacks.

Stacks 06MR asserts that exactly one object property of `X` has that kind, so this says that
the morphism Stacks 06MR constructs for `X` is not an isomorphism. Quantifying over all
candidates rather than naming the one Stacks 06MR constructs avoids the two undischarged
hypotheses under which this library proves the existence half of Stacks 06MR, and makes the
statement stronger rather than weaker.

If the inclusion were an equivalence, condition (2) of Stacks 06MP would transport to `X`, and
condition (1) — in particular local Noetherianity — would follow; but `X` is not locally
Noetherian. -/
@[stacks 06MS "the morphism Stacks 06MR constructs for X is not an isomorphism: for every \
object property of X satisfying the conditions of Stacks 06MR, its substack inclusion is not \
an equivalence over the big fppf site"]
theorem not_isEquivalence_substackInclusion
    (P : ObjectProperty (quotientStack.{w} B₀ hQ hK B hS hU).val.val.obj)
    (hP : Stack.IsReducedLocallyNoetherianUniquePointSubstack.{0, w} B cover.left hS
      (quotientStack.{w} B₀ hQ hK B hS hU) P) :
    ¬ Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor
      (Stack.fullSubcategoryInclusion (quotientStack.{w} B₀ hQ hK B hS hU) P
        hP.2.choose).hom) := by
  intro he
  refine not_isLocallyNoetherianStack_quotientStack.{w} B₀ hQ hK B hS hU ?_
  exact (Stack.isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation
    B cover.left hS (quotientStack.{w} B₀ hQ hK B hS hU)
    (Stack.hasLocallyOfFinitePresentationFlatFieldSpectrumCover_of_isEquivalenceFunctor
      B cover.left hS _ he hP.2.choose_spec)).2

/-! ### `x` is the morphism of Stacks 06MR, and the residual gerbe of `X` at `x` -/

/-- **Stacks 06MS.** `X`, as an algebraic stack, satisfies the hypothesis of **Stacks 06MR**,
condition (1) of **Stacks 06MN**: it is reduced and its space of points is a singleton. -/
@[stacks 06MS "X, as an algebraic stack, is reduced with exactly one point: the hypothesis of \
Lemma 06MR"]
theorem isReducedWithUniquePoint_quotientStack :
    Stack.IsReducedWithUniquePoint B cover.left hS (quotientStack.{w} B₀ hQ hK B hS hU) := by
  let e := Stack.spacePointsEquiv B cover.left hS (galoisSelfProductQuotient B₀ hQ hK B hS hU)
  have hsub := subsingleton_points_galoisSelfProductQuotient B₀ hQ hK B hS hU
  obtain ⟨p⟩ := nonempty_points_galoisSelfProductQuotient B₀ hQ hK B hS hU
  exact ⟨(Stack.scheme_atlas_iff_etaleLocalProperty B cover.left hS
      (fun X : Scheme.{0} ↦ IsReduced X) (galoisSelfProductQuotient B₀ hQ hK B hS hU)
      (isAlgebraicSpace_galoisSelfProductQuotient B₀ hQ hK B hS hU)).mpr
      (isReduced_galoisSelfProductQuotient B₀ hQ hK B hS hU), ⟨e p⟩, e.symm.subsingleton⟩

/-- `Spec(ℚ̄)`, the terminal object of the big fppf site over `Spec(ℚ̄)`, as the spectrum of a
field. -/
def baseFieldSpectrum : Stack.FieldSpectrum B cover.left hS where
  carrier := AlgebraicClosure ℚ
  base := Space.baseTerminal B cover.left hS
  isSpec := Iso.refl _

/-- **Stacks 06MS.** The morphism `x : Spec(ℚ̄) ⟶ X`, as a 1-morphism of algebraic stacks over
`Spec(ℚ̄)`: the 1-morphism of categories of elements induced by
`AlgebraicGeometry.RationalGaloisQuotient.canonicalPoint`. -/
def canonicalPointStack :
    Stack.schemeStack.{0, w} B cover.left hS (baseFieldSpectrum B hS).base ⟶
      quotientStack.{w} B₀ hQ hK B hS hU :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (Stack.presentationBasedFunctor B cover.left hS (Space.baseTerminal B cover.left hS)
      (canonicalPoint B₀ hQ hK B hS hU)))

/-- The functor of categories of elements underlying `canonicalPointStack` is full. -/
theorem full_canonicalPointStack :
    (CatFiberedInGroupoids.homFunctor (canonicalPointStack.{w} B₀ hQ hK B hS hU).hom).Full := by
  have := mono_canonicalPoint B₀ hQ hK B hS hU
  exact Stack.full_presentationBasedFunctor_of_mono B cover.left hS
    (Space.baseTerminal B cover.left hS)
    (canonicalPoint B₀ hQ hK B hS hU)

/-- The functor of categories of elements underlying `canonicalPointStack` is faithful. -/
theorem faithful_canonicalPointStack :
    (CatFiberedInGroupoids.homFunctor (canonicalPointStack.{w} B₀ hQ hK B hS hU).hom).Faithful :=
  Stack.faithful_presentationBasedFunctor B cover.left hS (Space.baseTerminal B cover.left hS)
    (canonicalPoint B₀ hQ hK B hS hU)

/-- **Stacks 06MS.** `x : Spec(ℚ̄) ⟶ X` is a monomorphism of algebraic stacks in the sense of
**Stacks 04ZW**: it is fully faithful because `x` is a monomorphism of sheaves, and a fully
faithful 1-morphism of algebraic stacks is a monomorphism. -/
@[stacks 06MS "x is a monomorphism of algebraic stacks"]
theorem isMonomorphism_canonicalPointStack :
    Stack.AlgebraicStacks.IsMonomorphism B cover.left hS
      (canonicalPointStack.{w} B₀ hQ hK B hS hU) :=
  Stack.AlgebraicStacks.isMonomorphism_of_full_and_faithful B cover.left hS _
    (full_canonicalPointStack.{w} B₀ hQ hK B hS hU)
    (faithful_canonicalPointStack.{w} B₀ hQ hK B hS hU)

/-- The point `x ∈ |X|` of the algebraic stack `X`: the image of the point of `Spec(ℚ̄)` under
`x : Spec(ℚ̄) ⟶ X`. Since `|X|` is a singleton it is the unique point of `X`. -/
def canonicalStackPoint :
    Stack.AlgebraicStacks.points B cover.left hS (quotientStack.{w} B₀ hQ hK B hS hU) :=
  Stack.AlgebraicStacks.pointsMap B cover.left hS (canonicalPointStack.{w} B₀ hQ hK B hS hU)
    (Stack.pointClass B cover.left hS _ _
      (Stack.fieldSpectrumPoint.{0, w} B cover.left hS (baseFieldSpectrum B hS)))

/-- The strictly full subcategory of `X` cut out by `x : Spec(ℚ̄) ⟶ X`: the essential image of
the 1-morphism `x`. -/
abbrev canonicalPointSubstack : ObjectProperty (quotientStack.{w} B₀ hQ hK B hS hU).val.val.obj :=
  (CatFiberedInGroupoids.homFunctor (canonicalPointStack.{w} B₀ hQ hK B hS hU).hom).essImage

/-- **Stacks 06MS: `x` is the morphism constructed in Lemma 06MR.** The strictly full
subcategory of `X` cut out by `x : Spec(ℚ̄) ⟶ X` is a substack of the kind **Stacks 06MR**
produces for the reduced one-point algebraic stack `X`: it is closed under isomorphism, its full
subcategory is an algebraic stack, and that algebraic stack satisfies condition (2) of
**Stacks 06MP**. Moreover `x` factors through the inclusion of that substack by a 1-morphism whose
underlying functor is an equivalence of categories, so `x` *is* the inclusion morphism of
Lemma 06MR up to equivalence. And that inclusion morphism is *not* an isomorphism: it is not an
equivalence over the big fppf site, because `X` is not locally Noetherian. -/
@[stacks 06MS "x is the morphism constructed in Lemma 06MR, and it is not an isomorphism: the \
substack of X cut out by x is closed under isomorphism, algebraic and satisfies the conditions \
of 06MP, x factors through its inclusion by an equivalence, and that inclusion is not an \
equivalence"]
theorem isReducedLocallyNoetherianUniquePointSubstack_canonicalPointSubstack :
    Stack.IsReducedLocallyNoetherianUniquePointSubstack.{0, w} B cover.left hS
        (quotientStack.{w} B₀ hQ hK B hS hU) (canonicalPointSubstack.{w} B₀ hQ hK B hS hU) ∧
      ∃ hP : Stack.IsAlgebraicStack.{0, w} B cover.left hS
          (Stack.fullSubcategoryBased (quotientStack.{w} B₀ hQ hK B hS hU)
            (canonicalPointSubstack.{w} B₀ hQ hK B hS hU)),
        ∃ t : Stack.schemeStack.{0, w} B cover.left hS (baseFieldSpectrum B hS).base ⟶
            Stack.fullSubcategoryAlgebraicStack (quotientStack.{w} B₀ hQ hK B hS hU)
              (canonicalPointSubstack.{w} B₀ hQ hK B hS hU) hP,
          Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor t.hom) ∧
            Nonempty (t ≫ Stack.fullSubcategoryInclusion (quotientStack.{w} B₀ hQ hK B hS hU)
              (canonicalPointSubstack.{w} B₀ hQ hK B hS hU) hP ≅
                canonicalPointStack.{w} B₀ hQ hK B hS hU ≫ 𝟙 _) ∧
          ¬ Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor
            (Stack.fullSubcategoryInclusion (quotientStack.{w} B₀ hQ hK B hS hU)
              (canonicalPointSubstack.{w} B₀ hQ hK B hS hU) hP).hom) := by
  obtain ⟨hP, hcov, t, ht, hκ⟩ := Stack.exists_isEquivalence_essImage_of_full_of_faithful.{0, w}
    B cover.left hS (quotientStack.{w} B₀ hQ hK B hS hU) (baseFieldSpectrum B hS)
    (canonicalPointStack.{w} B₀ hQ hK B hS hU) (full_canonicalPointStack.{w} B₀ hQ hK B hS hU)
    (faithful_canonicalPointStack.{w} B₀ hQ hK B hS hU)
  have hsub : Stack.IsReducedLocallyNoetherianUniquePointSubstack.{0, w} B cover.left hS
      (quotientStack.{w} B₀ hQ hK B hS hU) (canonicalPointSubstack.{w} B₀ hQ hK B hS hU) :=
    ⟨inferInstance, hP, hcov⟩
  exact ⟨hsub, hP, t, ht, hκ, not_isEquivalence_substackInclusion.{w} B₀ hQ hK B hS hU _ hsub⟩

/-- **Stacks 06MS: `x` is the morphism constructed in Lemma 06MR.** The substack of `X` cut out
by `x : Spec(ℚ̄) ⟶ X` is *the* strictly full subcategory of `X` which Stacks 06MR produces: a
strictly full subcategory of `X` is an algebraic stack satisfying the conditions of
**Stacks 06MP** if and only if it is the substack cut out by `x`.

Uniqueness is the argument of Stacks 06MR. Its input, that the inclusion of a strictly full
algebraic substack is a monomorphism, holds because `X` is an algebraic space: such a substack is
a stack in setoids, hence an algebraic space by **Stacks 04SZ**, so its inclusion is
representable by algebraic spaces by **Stacks 02ZZ**. -/
@[stacks 06MS "x is the morphism constructed in Lemma 06MR: the substack cut out by x is the \
unique strictly full subcategory of X which is an algebraic stack satisfying the conditions of \
06MP"]
theorem isReducedLocallyNoetherianUniquePointSubstack_iff_eq_canonicalPointSubstack
    (Q : ObjectProperty (quotientStack.{w} B₀ hQ hK B hS hU).val.val.obj) :
    Stack.IsReducedLocallyNoetherianUniquePointSubstack.{0, w} B cover.left hS
        (quotientStack.{w} B₀ hQ hK B hS hU) Q ↔
      Q = canonicalPointSubstack.{w} B₀ hQ hK B hS hU := by
  have hP := (isReducedLocallyNoetherianUniquePointSubstack_canonicalPointSubstack.{w}
    B₀ hQ hK B hS hU).1
  refine ⟨fun hQ' ↦ ?_, fun h ↦ h ▸ hP⟩
  exact Stack.eq_of_isReducedLocallyNoetherianUniquePointSubstack_of_representable
    B cover.left hS _
    (Stack.isRepresentableByAlgebraicSpace_fibredCategory B cover.left hS _
      (isAlgebraicSpace_galoisSelfProductQuotient B₀ hQ hK B hS hU))
    (isReducedWithUniquePoint_quotientStack.{w} B₀ hQ hK B hS hU).2.2 hQ' hP

/-- **Stacks 06MS: `x` is the morphism constructed in Lemma 06MR, the uniqueness half.** Every
strictly full subcategory of `X` of the kind **Stacks 06MR** produces — closed under isomorphism,
algebraic, and satisfying condition (2) of **Stacks 06MP** — is contained in the substack cut out
by `x`.

This is one half of
`AlgebraicGeometry.RationalGaloisQuotient`
`.isReducedLocallyNoetherianUniquePointSubstack_iff_eq_canonicalPointSubstack`. -/
@[stacks 06MS "x is the morphism constructed in Lemma 06MR: every strictly full subcategory of \
X with the properties of Lemma 06MR is contained in the substack cut out by x"]
theorem le_canonicalPointSubstack
    (Q : ObjectProperty (quotientStack.{w} B₀ hQ hK B hS hU).val.val.obj)
    (hQ' : Stack.IsReducedLocallyNoetherianUniquePointSubstack.{0, w} B cover.left hS
      (quotientStack.{w} B₀ hQ hK B hS hU) Q) :
    Q ≤ canonicalPointSubstack.{w} B₀ hQ hK B hS hU :=
  ((isReducedLocallyNoetherianUniquePointSubstack_iff_eq_canonicalPointSubstack.{w}
    B₀ hQ hK B hS hU Q).mp hQ').le

/-- **Stacks 06MS: `Spec(ℚ̄) ⟶ X` is the residual gerbe of `X` at `x`.** The residual gerbe of
`X` at `x` exists in the sense of **Stacks 06MU (1)** — `x : Spec(ℚ̄) ⟶ X` is a monomorphism from
a reduced algebraic stack with a single point mapping to `x` — and the strictly full subcategory
cut out by `x` meets the specification `AlgebraicGeometry.Stack.IsResidualGerbeAt` of
**Stacks 06MT** that defines the residual gerbe of **Stacks 06MU (2)**: it is a reduced, locally
Noetherian algebraic stack with exactly one point, lying over `x`. -/
@[stacks 06MS "Spec(ℚ̄) ⟶ X is the residual gerbe of X at x"]
theorem isResidualGerbeAt_canonicalPointSubstack :
    Stack.HasReducedSingletonPointMonomorphism B cover.left hS
        (quotientStack.{w} B₀ hQ hK B hS hU) (canonicalStackPoint.{w} B₀ hQ hK B hS hU) ∧
      Stack.IsResidualGerbeAt B cover.left hS (quotientStack.{w} B₀ hQ hK B hS hU)
        (canonicalStackPoint.{w} B₀ hQ hK B hS hU)
        (canonicalPointSubstack.{w} B₀ hQ hK B hS hU) := by
  obtain ⟨⟨hred, -, hsub⟩, -⟩ :=
    Stack.isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation.{0, w}
      B cover.left hS _
      (Stack.hasLocallyOfFinitePresentationFlatFieldSpectrumCover_schemeStack.{0, w}
        B cover.left hS (baseFieldSpectrum B hS))
  refine ⟨⟨_, canonicalPointStack.{w} B₀ hQ hK B hS hU, hred,
    isMonomorphism_canonicalPointStack.{w} B₀ hQ hK B hS hU, _, fun z ↦ hsub.elim z _, rfl⟩, ?_⟩
  exact Stack.isResidualGerbeAt_essImage_of_full_of_faithful.{0, w} B cover.left hS _
    (baseFieldSpectrum B hS) (canonicalPointStack.{w} B₀ hQ hK B hS hU)
    (full_canonicalPointStack.{w} B₀ hQ hK B hS hU)
    (faithful_canonicalPointStack.{w} B₀ hQ hK B hS hU) _ _ rfl

/-- **Stacks 06MS.** `x : Spec(ℚ̄) ⟶ U ⟶ X` is locally of finite type: the diagonal
`Spec(ℚ̄) ⟶ U` is a closed immersion, `U` being separated over `Spec(ℚ̄)`, and `U ⟶ X` is étale. -/
@[stacks 06MS "x : Spec(ℚ̄) ⟶ U ⟶ X is locally of finite type"]
theorem isLocallyOfFiniteType_canonicalPoint :
    Space.IsLocallyOfFiniteType B cover.left hS (canonicalPoint B₀ hQ hK B hS hU) := by
  have hdiag : LocallyOfFiniteType
      ((BigFppfOver.toScheme B cover.left hS).map (siteDiagonal B hS hU)) := by
    change LocallyOfFiniteType (pullback.diagonal cover.hom)
    infer_instance
  exact Space.isLocallyOfFiniteType_comp' B cover.left hS _ _
    (isAlgebraicSpace_yoneda B cover.left hS _)
    (isAlgebraicSpace_galoisSelfProductQuotient B₀ hQ hK B hS hU)
    ((Space.isLocallyOfFiniteType_yoneda_map_iff B cover.left hS _).2 hdiag)
    (Space.isLocallyOfFiniteType_of_isEtale B cover.left hS
      (isAlgebraicSpace_galoisSelfProductQuotient B₀ hQ hK B hS hU)
      (Space.isEtale_of_presheaf_etale B cover.left hS (etale_quotientProjection B₀ hQ hK B hS hU)))

/-- All of `X`, as a strictly full subcategory, satisfies the specification of the residual
gerbe at `x` without its local Noetherianity clause, with a monomorphic inclusion, and its full
subcategory is not locally Noetherian. -/
private theorem top_isReducedUniquePointSubstackAt :
    Stack.IsReducedUniquePointSubstackAt B cover.left hS (quotientStack.{w} B₀ hQ hK B hS hU)
        (canonicalStackPoint.{w} B₀ hQ hK B hS hU) ⊤ ∧
      ∀ hT : Stack.IsAlgebraicStack.{0, w} B cover.left hS
          (Stack.fullSubcategoryBased (quotientStack.{w} B₀ hQ hK B hS hU) ⊤),
        ¬ Stack.IsLocallyNoetherianStack B cover.left hS
          (Stack.fullSubcategoryAlgebraicStack (quotientStack.{w} B₀ hQ hK B hS hU) ⊤ hT) := by
  classical
  set 𝒳 := quotientStack.{w} B₀ hQ hK B hS hU
  set i : 𝒳 ⟶ 𝒳 := 𝟙 𝒳
  have hid : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor i.hom) :=
    Stack.AlgebraicStacks.isEquivalence_basedFunctorId (𝒳 := 𝒳)
  have htop : (CatFiberedInGroupoids.homFunctor i.hom).essImage = ⊤ := by
    funext X
    exact propext ⟨fun _ ↦ trivial,
      fun _ ↦ (CatFiberedInGroupoids.homFunctor i.hom).obj_mem_essImage X⟩
  have hequiv : Functor.IsEquivalence (Stack.AlgebraicStacks.toEssImageBased i).toFunctor :=
    Stack.isEquivalence_toEssImageBased_of_full_of_faithful B cover.left hS i inferInstance
      inferInstance
  obtain ⟨e, -⟩ := Stack.exists_basedEquivalence_functor_eq B cover.left hS 𝒳.val
    (Stack.AlgebraicStacks.essImageFibered i) (Stack.AlgebraicStacks.toEssImageBased i) hequiv
  have hP : Stack.IsAlgebraicStack.{0, w} B cover.left hS
      (Stack.fullSubcategoryBased 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage) :=
    (Stack.isAlgebraicStack_iff_of_equivalence B cover.left hS e).mp 𝒳.property
  set t : 𝒳 ⟶ Stack.fullSubcategoryAlgebraicStack 𝒳
      (CatFiberedInGroupoids.homFunctor i.hom).essImage hP :=
    Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom (Stack.AlgebraicStacks.toEssImageBased i))
  have ht : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor t.hom) := hequiv
  have htsurj := Stack.isSurjective_of_isEquivalenceFunctor B cover.left hS t ht
  have hκ : t ≫ Stack.fullSubcategoryInclusion 𝒳
      (CatFiberedInGroupoids.homFunctor i.hom).essImage hP ≅ i ≫ 𝟙 𝒳 :=
    Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
      (Stack.AlgebraicStacks.toEssImageBasedSquareIso i))
  have h𝒳 := isReducedWithUniquePoint_quotientStack.{w} B₀ hQ hK B hS hU
  rw [← htop]
  refine ⟨⟨inferInstance, hP,
    Stack.isReducedStack_of_isEquivalence_stackMorphism t ht htsurj h𝒳.1,
    Stack.AlgebraicStacks.pointsMap B cover.left hS t (canonicalStackPoint.{w} B₀ hQ hK B hS hU),
    fun z ↦ ?_, ?_⟩, fun hT hln ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := htsurj z
    rw [h𝒳.2.2.elim y (canonicalStackPoint.{w} B₀ hQ hK B hS hU)]
  · calc Stack.AlgebraicStacks.pointsMap B cover.left hS
            (Stack.fullSubcategoryInclusion 𝒳
              (CatFiberedInGroupoids.homFunctor i.hom).essImage hP)
            (Stack.AlgebraicStacks.pointsMap B cover.left hS t
              (canonicalStackPoint.{w} B₀ hQ hK B hS hU))
        = Stack.AlgebraicStacks.pointsMap B cover.left hS
            (t ≫ Stack.fullSubcategoryInclusion 𝒳
              (CatFiberedInGroupoids.homFunctor i.hom).essImage hP)
            (canonicalStackPoint.{w} B₀ hQ hK B hS hU) := by
          simp only [Stack.AlgebraicStacks.pointsMap_comp, Function.comp_apply]
      _ = Stack.AlgebraicStacks.pointsMap B cover.left hS (i ≫ 𝟙 𝒳)
            (canonicalStackPoint.{w} B₀ hQ hK B hS hU) := by
          rw [Stack.AlgebraicStacks.pointsMap_eq_of_hom₂ B cover.left hS hκ.hom]
      _ = canonicalStackPoint.{w} B₀ hQ hK B hS hU := by
          simp only [Stack.AlgebraicStacks.pointsMap_comp, Function.comp_apply,
            Stack.AlgebraicStacks.pointsMap_id, id_eq, i]
  · obtain ⟨V, a, hasurj, hasmooth, hV⟩ := hln
    set j := Stack.fullSubcategoryInclusion 𝒳 (CatFiberedInGroupoids.homFunctor i.hom).essImage hT
    have hj : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor j.hom) :=
      ObjectProperty.isEquivalence_ι htop
    refine not_isLocallyNoetherianStack_quotientStack.{w} B₀ hQ hK B hS hU
      ⟨V, a ≫ j, ?_, Stack.AlgebraicStacks.isSmooth_comp B cover.left hS a j hasmooth
        (Stack.AlgebraicStacks.isSmooth_of_isEquivalence B cover.left hS j hj), hV⟩
    change Function.Surjective (Stack.AlgebraicStacks.pointsMap B cover.left hS (a ≫ j))
    rw [Stack.AlgebraicStacks.pointsMap_comp]
    exact (Stack.isSurjective_of_isEquivalenceFunctor B cover.left hS j hj).comp hasurj

/-- **Stacks 06MS: imposing that residual gerbes be locally Noetherian is necessary in
Definition 06MU.** Drop the local Noetherianity clause from the specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt` of the residual gerbe, leaving
`AlgebraicGeometry.Stack.IsReducedUniquePointSubstackAt`: a strictly full subcategory which is a
reduced algebraic stack with exactly one point, lying over `x`. Then two *distinct* strictly full
subcategories of `X` meet it at `x` — the substack cut out by `x` and all of `X` — and both
inclusions are monomorphisms of algebraic stacks; so the residual gerbe would not be unique. The
local Noetherianity clause is exactly what tells them apart: the substack cut out by `x` is the
residual gerbe of `X` at `x`, and all of `X` is not locally Noetherian. -/
@[stacks 06MS "imposing that residual gerbes are locally Noetherian is necessary in Definition \
06MU: without that clause the substack cut out by x and all of X are two distinct reduced \
one-point substacks over x with monomorphic inclusions, and only the first is locally \
Noetherian"]
theorem ne_and_isReducedUniquePointSubstackAt_canonicalPointSubstack_top :
    canonicalPointSubstack.{w} B₀ hQ hK B hS hU ≠ ⊤ ∧
      Stack.IsReducedUniquePointSubstackAt B cover.left hS (quotientStack.{w} B₀ hQ hK B hS hU)
        (canonicalStackPoint.{w} B₀ hQ hK B hS hU) (canonicalPointSubstack.{w} B₀ hQ hK B hS hU) ∧
      Stack.IsReducedUniquePointSubstackAt B cover.left hS (quotientStack.{w} B₀ hQ hK B hS hU)
        (canonicalStackPoint.{w} B₀ hQ hK B hS hU) ⊤ ∧
      (∀ (P : ObjectProperty (quotientStack.{w} B₀ hQ hK B hS hU).val.val.obj)
        (hP : Stack.IsAlgebraicStack.{0, w} B cover.left hS
          (Stack.fullSubcategoryBased (quotientStack.{w} B₀ hQ hK B hS hU) P)),
        Stack.AlgebraicStacks.IsMonomorphism B cover.left hS
          (Stack.fullSubcategoryInclusion (quotientStack.{w} B₀ hQ hK B hS hU) P hP)) ∧
      Stack.IsResidualGerbeAt B cover.left hS (quotientStack.{w} B₀ hQ hK B hS hU)
        (canonicalStackPoint.{w} B₀ hQ hK B hS hU) (canonicalPointSubstack.{w} B₀ hQ hK B hS hU) ∧
      ¬ Stack.IsResidualGerbeAt B cover.left hS (quotientStack.{w} B₀ hQ hK B hS hU)
        (canonicalStackPoint.{w} B₀ hQ hK B hS hU) ⊤ := by
  obtain ⟨-, hP, -, -, -, hnot⟩ :=
    isReducedLocallyNoetherianUniquePointSubstack_canonicalPointSubstack.{w} B₀ hQ hK B hS hU
  have hres := (isResidualGerbeAt_canonicalPointSubstack.{w} B₀ hQ hK B hS hU).2
  obtain ⟨htop, htopln⟩ := top_isReducedUniquePointSubstackAt.{w} B₀ hQ hK B hS hU
  refine ⟨fun h ↦ hnot (ObjectProperty.isEquivalence_ι h), hres.isReducedUniquePointSubstackAt
    B cover.left hS, htop, fun P hP' ↦
      Stack.AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion B cover.left hS _ P hP',
    hres, fun h ↦ htopln h.2.choose h.2.choose_spec.2.1⟩

end Quotient

end AlgebraicGeometry.RationalGaloisQuotient

end
