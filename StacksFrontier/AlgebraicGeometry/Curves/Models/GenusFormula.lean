module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.IntersectionForm
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Additivity
import StacksCore.Tactic.StacksAttribute

/-!
# A formula for the genus: adding a component of the special fibre to a divisor

In the situation of [Stacks, Tag 0C61] let `C₁, …, Cₙ` be the irreducible components of the
special fibre of a regular proper model `X ⟶ Spec(R)` and let `D ⊂ X` be an effective Cartier
divisor supported on the special fibre, `D = ∑ⱼ bⱼCⱼ`. Adding one more component `Cᵢ` to `D`
changes the Euler characteristic of the structure sheaf of the divisor by

`χ(Cᵢ, 𝒪_X(-D)|_{Cᵢ}) = -(Cᵢ · D) + χ(Cᵢ, 𝒪_{Cᵢ})`,

the second equality of [Stacks, Tag 0CA2]. Both sides are degrees of invertible modules on the
component: unfolding `AlgebraicGeometry.invertibleCurveDegree`, which is `χ(ℒ) - χ(𝒪)` by
definition, and the intersection product of [Stacks, Tag 0C65], which is the degree pairing of
[Stacks, Tag 0C64] against `𝒪_X(D)`, the identity becomes
`deg(𝒪_X(-D)|_{Cᵢ}) = -deg(𝒪_X(D)|_{Cᵢ})`: the degree of the inverse of an invertible module is
minus its degree. That is the invertible case of [Stacks, Tag 0AYX], and it is carried
unconditionally below.

## Main definitions

* `Stacks.Models.invertibleSheafTensorNegativeTwistIsoUnit` — the evaluation pairing
  `𝒪_X(D) ⊗ 𝒪_X(-D) ≅ 𝒪_X` of an effective Cartier divisor.
* `Stacks.Models.ComponentDegreeAdditive` — additivity of the degree on a component in the
  tensor product, the invertible case of [Stacks, Tag 0AYX].

## Main results

* `Stacks.Models.componentDegree_tensorSheaf_eq_add` — the invertible case of
  [Stacks, Tag 0AYX] on a closed subscheme, `deg((ℒ ⊗ ℳ)|_D) = deg(ℒ|_D) + deg(ℳ|_D)`, with no
  hypothesis.
* `Stacks.Models.componentDegree_negativeTwist_eq_neg` —
  `deg(𝒪_X(-D)|_{Cᵢ}) = -deg(𝒪_X(D)|_{Cᵢ})`, with no hypothesis.
* `Stacks.Models.componentDegree_eq_eulerCharacteristic_restrict_sub` — the component degree as
  a difference of Euler characteristics on the component.
* `Stacks.Models.intersectionProduct_single_eq_componentDegree` — the intersection product of a
  single component against `∑ⱼ bⱼCⱼ` is the degree of `𝒪_X(∑ⱼ bⱼCⱼ)` on that component.
* `Stacks.Models.eulerCharacteristic_negativeTwist_restrict_eq` — **the second equality of
  [Stacks, Tag 0CA2]**.

## Implementation notes

**`D` is a nonnegative combination of the components.** Tag 0CA2 takes `D ⊂ D' ⊂ X_k` effective
Cartier, which forces `D = ∑ⱼ bⱼCⱼ`; and the intersection product
`Stacks.Models.intersectionProduct` takes the second divisor as a coefficient family, so no other
form of `D` makes the right-hand side expressible. The hypothesis `hDsum` is therefore not a
restriction of the source but the source's hypothesis made explicit. The divisor `D'` itself does
not occur: the second equality does not mention it, so stating it without `D'` is the stronger
reading.

**The orientation of the intersection product.** The pairing of equation (55.9.6.1) is
`(∑ᵢ aᵢCᵢ · ∑ⱼ bⱼCⱼ) = ⟨a, 𝒪_X(∑ⱼ bⱼCⱼ)⟩ = ⟨b, 𝒪_X(∑ᵢ aᵢCᵢ)⟩`, the two readings agreeing by
[Stacks, Tag 0C64]. That symmetry is proved, at the irreducible components of the special fibre,
as `Stacks.Models.RegularProperModelSituation.specialFiberIntersectionProduct_comm` of
`StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean`;
`Stacks.Models.intersectionProduct` is the first reading, and `(D · Cᵢ)` of the source is
written here in the orientation `(Cᵢ · D) = ⟨eᵢ, 𝒪_X(D)⟩`. This is the reading the source's own
proof of the second equality uses, which is why it cites the definition of the pairing together
with Tag 0C64 rather than the symmetry alone.

**The Euler characteristics are taken on the component.** The source writes
`χ(X_k, 𝒪_X(-D)|_{Cᵢ})` and `χ(Cᵢ, 𝒪_{Cᵢ})` for the two sides of one equation; the two readings
agree by `AlgebraicGeometry.eulerCharacteristic_pushforward_of_isClosedImmersion`. Everything
below is taken on `Cᵢ`, which is the reading `AlgebraicGeometry.invertibleCurveDegree` consumes
and the one in which the right-hand side is already written. The structure morphism
`Cᵢ ⟶ Spec(k)` and its properness are explicit arguments, as they are for
`Stacks.Models.componentDegree`.

**The first equality is not proved here.** `χ(𝒪_{D'}) - χ(𝒪_D) = χ(𝒪_X(-D)|_{Cᵢ})` is proved, on
an ambient scheme that itself carries the morphism to `k`, as
`Stacks.Divisors.eulerCharacteristic_sub_eq_of_eq_mul`; in Tag 0CA2 the divisors are Cartier on
`X`, which lies over `R` and not over `k`, while the Euler characteristics are taken on the
special fibre. Transporting the short exact sequence of [Stacks, Tag 0C4T] from `X` to `X_k`
along [Stacks, Tag 01QY] is what is missing, and no module of this library carries it.

**The one mathematical input needs no hypothesis.** The invertible case of [Stacks, Tag 0AYX] on
a closed subscheme is `Stacks.Models.componentDegree_tensorSheaf_eq_add` below: the restriction
of a tensor product is the tensor product of the restrictions, [Stacks, Tag 01CD], and
`AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add` is unconditional on a proper scheme
of dimension at most one over a field. So neither
`Stacks.Models.componentDegree_negativeTwist_eq_neg` nor the tagged statement below carries it,
and the hypothesis bundle `Stacks.Models.ComponentDegreeAdditive` survives only for the
statements that quantify over one component of an abstract family. The coherence of the three
modules on the component is still an argument rather than an instance, since
`AlgebraicGeometry.eulerCharacteristic` requires it and [Stacks, Tag 02O6] is not available to
supply it.

## References

* [Stacks Project, Tag 0CA2](https://stacks.math.columbia.edu/tag/0CA2)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)
* [Stacks Project, Tag 0C65](https://stacks.math.columbia.edu/tag/0C65)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.Models

/-- **The evaluation pairing `𝒪_X(D) ⊗ 𝒪_X(-D) ≅ 𝒪_X`** of an effective Cartier divisor, which
is what makes `𝒪_X(D)` the inverse of the ideal sheaf `𝒪_X(-D) = ℐ_D`.

This is `Stacks.SheafOfModules.Scheme.evaluationIso` at `ℐ_D`, whose dual is `𝒪_X(D)` by
definition. `Stacks.Divisors.invertibleSheafPairing` is the same pairing at the other of the two
spellings of the sheaf of rings; this one is indexed over
`structureSheafRing`, which is the index
`Stacks.Models.componentDegree` consumes. -/
@[ega "IV 21.2.8" "special case"]
def invertibleSheafTensorNegativeTwistIsoUnit {X : Scheme.{u}} (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            ((Stacks.Divisors.invertibleSheaf' D))).obj
        ((Stacks.Divisors.negativeTwist' D))) ≅ SheafOfModules.unit X.ringCatSheaf :=
  haveI := hD
  haveI := Stacks.Divisors.isTensorInvertible_negativeTwist D
  Stacks.SheafOfModules.Scheme.evaluationIso X (Stacks.Divisors.negativeTwist' D)

/-- The tensor product `𝒪_X(D) ⊗ 𝒪_X(-D)` of an effective Cartier divisor is invertible, being
the tensor product of two invertible modules ([Stacks, Tag 01CT] (1)). -/
theorem isTensorInvertible_invertibleSheafTensorNegativeTwist {X : Scheme.{u}}
    (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              ((Stacks.Divisors.invertibleSheaf' D))).obj
          ((Stacks.Divisors.negativeTwist' D)))) :=
  have := hD
  have := Stacks.Divisors.isTensorInvertible_negativeTwist D
  have := Stacks.Divisors.isTensorInvertible_invertibleSheaf D
  Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _

/-- `deg(ℒ|_D) = χ(D, ℒ|_D) - χ(D, 𝒪_D)`: the degree of an invertible module on a closed
subscheme which is a proper curve over `k` is the difference of the Euler characteristic of its
restriction with that of the structure sheaf. This is the defining formula for
`AlgebraicGeometry.invertibleCurveDegree`, read at `Stacks.Models.componentDegree`. -/
theorem componentDegree_eq_eulerCharacteristic_restrict_sub (k : Type u) [Field k]
    {X : Scheme.{u}} (D : X.IdealSheafData) (g : D.subscheme ⟶ Spec (.of k)) (hg : IsProper g)
    (hdim : topologicalKrullDim D.subscheme ≤ 1) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L)
    (hcL : ((Scheme.Modules.pullback D.subschemeι).obj L).IsCoherent)
    (hcO : (SheafOfModules.unit D.subscheme.ringCatSheaf).IsCoherent) :
    componentDegree k D g hg hdim L hL =
      @eulerCharacteristic k _ _ g hg ((Scheme.Modules.pullback D.subschemeι).obj L) hcL -
        @eulerCharacteristic k _ _ g hg (SheafOfModules.unit D.subscheme.ringCatSheaf) hcO :=
  @AlgebraicGeometry.invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ g hg hdim _
    (isInvertible_restrict D L hL) hcL hcO

/-- **Additivity of the degree on a closed subscheme in the tensor product**,
`deg((ℒ ⊗ ℳ)|_D) = deg(ℒ|_D) + deg(ℳ|_D)`: the invertible case of [Stacks, Tag 0AYX] read at
`Stacks.Models.componentDegree`, carrying **no hypothesis**.

The restriction of a tensor product is the tensor product of the restrictions,
[Stacks, Tag 01CD], and the degree of an invertible module on a proper scheme of dimension at
most one over a field is additive in the tensor product, so
`AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add` applies on `D`. -/
theorem componentDegree_tensorSheaf_eq_add (k : Type u) [Field k] {X : Scheme.{u}}
    (D : X.IdealSheafData) (g : D.subscheme ⟶ Spec (.of k)) (hg : IsProper g)
    (hdim : topologicalKrullDim D.subscheme ≤ 1) (L M : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M)
    (hLM : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (L)).obj (M)))) :
    componentDegree k D g hg hdim
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (L)).obj (M))) hLM =
      componentDegree k D g hg hdim L hL + componentDegree k D g hg hdim M hM := by
  have := hL
  have := hM
  have e : (Scheme.Modules.pullback D.subschemeι).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (L)).obj (M))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨(D.subscheme.toRingedSpace).presheaf,
                  (D.subscheme.toRingedSpace).IsSheaf⟩).obj
            (((Scheme.Modules.pullback D.subschemeι).obj L))).obj
        (((Scheme.Modules.pullback D.subschemeι).obj M))) :=
    AlgebraicGeometry.pullbackTensorObjIso D.subschemeι L M
  have hsL : Stacks.SheafOfModules.IsInvertible D.subscheme.presheaf
      D.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback D.subschemeι).obj L) :=
    Stacks.Modules.isInvertible_pullback D.subschemeι L
  have hsM : Stacks.SheafOfModules.IsInvertible D.subscheme.presheaf
      D.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback D.subschemeι).obj M) :=
    Stacks.Modules.isInvertible_pullback D.subschemeι M
  have hsT : Stacks.SheafOfModules.IsInvertible D.subscheme.presheaf
      D.subscheme.ringCatSheaf.2
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨(D.subscheme.toRingedSpace).presheaf,
                    (D.subscheme.toRingedSpace).IsSheaf⟩).obj
              (((Scheme.Modules.pullback D.subschemeι).obj L))).obj
          (((Scheme.Modules.pullback D.subschemeι).obj M)))) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _
  have hT : AlgebraicGeometry.SheafOfModules.IsInvertible D.subscheme.presheaf
      D.subscheme.ringCatSheaf.2
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨(D.subscheme.toRingedSpace).presheaf,
                    (D.subscheme.toRingedSpace).IsSheaf⟩).obj
              (((Scheme.Modules.pullback D.subschemeι).obj L))).obj
          (((Scheme.Modules.pullback D.subschemeι).obj M)))) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 hsT
  have hpL : AlgebraicGeometry.SheafOfModules.IsInvertible D.subscheme.presheaf
      D.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback D.subschemeι).obj L) :=
    isInvertible_restrict D L hL
  have hpM : AlgebraicGeometry.SheafOfModules.IsInvertible D.subscheme.presheaf
      D.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback D.subschemeι).obj M) :=
    isInvertible_restrict D M hM
  change @invertibleCurveDegree k _ _ g hg hdim _ (isInvertible_restrict D _ hLM) = _
  rw [@invertibleCurveDegree_eq_of_iso k _ _ g hg hdim _ _
      (isInvertible_restrict D _ hLM) hT e,
    AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add k g hdim _ _]
  rfl

variable (S : RegularProperModelSituation.{u}) {ι : Type*} (s : Finset ι)
  (C : ι → S.X.IdealSheafData) (g : ∀ i, (C i).subscheme ⟶ Spec (.of S.k))
  (hg : ∀ i, IsProper (g i)) (hdim : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1)

/-- **Additivity of the degree on the component `Cᵢ` in the tensor product**,
`deg((ℒ ⊗ ℳ)|_{Cᵢ}) = deg(ℒ|_{Cᵢ}) + deg(ℳ|_{Cᵢ})`: the invertible case of
[Stacks, Tag 0AYX] for the components of the special fibre of a regular proper model.

It is named so that a statement needing it on one component can take it as a single hypothesis.
It is **not** a gap: `Stacks.Models.componentDegree_tensorSheaf_eq_add` proves it with no
hypothesis at any closed subscheme, and
`Stacks.Models.componentDegreeAdditive` of
`StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean` is that reading at a
component. -/
def ComponentDegreeAdditive (i : ι) : Prop :=
  ∀ (L M : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L)
    (hM : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property M)
    (hLM : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((S.X.toRingedSpace)).presheaf,
                ((S.X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M)))),
    componentDegree S.k (C i) (g i) (hg i) (hdim i)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((S.X.toRingedSpace)).presheaf,
                ((S.X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (M))) hLM =
      componentDegree S.k (C i) (g i) (hg i) (hdim i) L hL +
        componentDegree S.k (C i) (g i) (hg i) (hdim i) M hM

/-- **The degree of `𝒪_X(-D)` on a component is minus the degree of `𝒪_X(D)`**,
`deg(𝒪_X(-D)|_{Cᵢ}) = -deg(𝒪_X(D)|_{Cᵢ})`, for an effective Cartier divisor `D` on a regular
proper model and a component `Cᵢ` of its special fibre that is a proper curve over the residue
field.

The evaluation pairing trivializes `𝒪_X(D) ⊗ 𝒪_X(-D)`, so that module has degree zero on the
component; additivity of the degree in the tensor product,
`Stacks.Models.componentDegree_tensorSheaf_eq_add`, then splits that zero into the two degrees.
**No hypothesis** beyond `D` being an effective Cartier divisor: that additivity carries none. -/
theorem componentDegree_negativeTwist_eq_neg (i : ι) (D : S.X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    componentDegree S.k (C i) (g i) (hg i) (hdim i) (Stacks.Divisors.negativeTwist' D)
        (@Stacks.Divisors.isTensorInvertible_negativeTwist _ D hD) =
      -componentDegree S.k (C i) (g i) (hg i) (hdim i) (Stacks.Divisors.invertibleSheaf' D)
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ D hD) := by
  have hLM := isTensorInvertible_invertibleSheafTensorNegativeTwist D hD
  have h0 : componentDegree S.k (C i) (g i) (hg i) (hdim i)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
                  ⟨((S.X.toRingedSpace)).presheaf, ((S.X.toRingedSpace)).IsSheaf⟩).obj
              ((Stacks.Divisors.invertibleSheaf' D))).obj
          ((Stacks.Divisors.negativeTwist' D)))) hLM = 0 := by
    rw [componentDegree_eq_of_iso S.k (C i) (g i) (hg i) (hdim i) _
      (SheafOfModules.unit S.X.ringCatSheaf) hLM (isTensorInvertible_unit S.X)
      (invertibleSheafTensorNegativeTwistIsoUnit D hD)]
    exact componentDegree_unit_eq_zero S.k (C i) (g i) (hg i) (hdim i)
      (isTensorInvertible_unit S.X)
  have h1 := componentDegree_tensorSheaf_eq_add S.k (C i) (g i) (hg i) (hdim i)
    (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.negativeTwist' D)
    (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ D hD)
    (@Stacks.Divisors.isTensorInvertible_negativeTwist _ D hD) hLM
  rw [h0] at h1
  linarith

/-- **The intersection product of a single component against `∑ⱼ bⱼCⱼ`**,
`(Cᵢ · ∑ⱼ bⱼCⱼ) = deg(𝒪_X(∑ⱼ bⱼCⱼ)|_{Cᵢ})`: the degree pairing of [Stacks, Tag 0C64] against the
basis vector `eᵢ` keeps only the `i`-th term of its defining sum. -/
theorem intersectionProduct_single_eq_componentDegree [DecidableEq ι] (i : ι) (hi : i ∈ s)
    (b : ι → ℕ) (hC : ∀ j ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C j)) :
    intersectionProduct S s C g hg hdim (Pi.single i 1) b hC =
      componentDegree S.k (C i) (g i) (hg i) (hdim i) (divisorSheaf S s C b)
        (isInvertible_divisorSheaf S s C b hC) := by
  rw [intersectionProduct_eq_degreePairing_divisorSheaf, degreePairing,
    Finset.sum_eq_single_of_mem i hi
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_mul]), Pi.single_eq_same, one_mul]

/-- **The second equality of [Stacks, Tag 0CA2].** In the situation of [Stacks, Tag 0C61],
for an effective Cartier divisor `D = ∑ⱼ bⱼCⱼ` supported on the special fibre and a component
`Cᵢ` of that fibre which is a proper curve over the residue field,

`χ(Cᵢ, 𝒪_X(-D)|_{Cᵢ}) = -(Cᵢ · D) + χ(Cᵢ, 𝒪_{Cᵢ})`.

Both sides are Euler characteristics on `Cᵢ`, which is how the source writes the right-hand side;
the intersection product is `Stacks.Models.intersectionProduct`, the pairing of equation
(55.9.6.1) in the orientation `(Cᵢ · D) = ⟨eᵢ, 𝒪_X(D)⟩`.

Unfolding the degree of an invertible module on a proper curve, which is `χ(ℒ) - χ(𝒪)` by
definition, the identity is `deg(𝒪_X(-D)|_{Cᵢ}) = -deg(𝒪_X(D)|_{Cᵢ})`, the invertible case of
[Stacks, Tag 0AYX], which is `Stacks.Models.componentDegree_negativeTwist_eq_neg` and carries no
hypothesis. The whole of Tag 0CA2, at the canonical
components and with both equalities, is
`Stacks.Models.RegularProperModelSituation.eulerCharacteristic_addComponent` of
`StacksFrontier/AlgebraicGeometry/Curves/Models/ComponentStepEulerCharacteristic.lean`. -/
theorem eulerCharacteristic_negativeTwist_restrict_eq [DecidableEq ι] (i : ι) (hi : i ∈ s)
    (b : ι → ℕ) (hC : ∀ j ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C j))
    (D : S.X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hDsum : D = ∏ j ∈ s, C j ^ b j)
    (hcL : ((Scheme.Modules.pullback (C i).subschemeι).obj
      (Stacks.Divisors.negativeTwist' D)).IsCoherent)
    (hcM : ((Scheme.Modules.pullback (C i).subschemeι).obj
      (Stacks.Divisors.invertibleSheaf' D)).IsCoherent)
    (hcO : (SheafOfModules.unit (C i).subscheme.ringCatSheaf).IsCoherent) :
    @eulerCharacteristic S.k _ _ (g i) (hg i)
        ((Scheme.Modules.pullback (C i).subschemeι).obj
          (Stacks.Divisors.negativeTwist' D)) hcL =
      -intersectionProduct S s C g hg hdim (Pi.single i 1) b hC +
        @eulerCharacteristic S.k _ _ (g i) (hg i)
          (SheafOfModules.unit (C i).subscheme.ringCatSheaf) hcO := by
  have hneg := componentDegree_negativeTwist_eq_neg S C g hg hdim i D hD
  have h1 := componentDegree_eq_eulerCharacteristic_restrict_sub S.k (C i) (g i) (hg i) (hdim i)
    (Stacks.Divisors.negativeTwist' D)
    (@Stacks.Divisors.isTensorInvertible_negativeTwist _ D hD) hcL hcO
  have h2 := componentDegree_eq_eulerCharacteristic_restrict_sub S.k (C i) (g i) (hg i) (hdim i)
    (Stacks.Divisors.invertibleSheaf' D)
    (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ D hD) hcM hcO
  have h3 := intersectionProduct_single_eq_componentDegree S s C g hg hdim i hi b hC
  have h4 : componentDegree S.k (C i) (g i) (hg i) (hdim i) (divisorSheaf S s C b)
        (isInvertible_divisorSheaf S s C b hC) =
      componentDegree S.k (C i) (g i) (hg i) (hdim i) (Stacks.Divisors.invertibleSheaf' D)
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ D hD) := by
    subst hDsum
    exact componentDegree_eq_of_iso S.k (C i) (g i) (hg i) (hdim i) _ _ _ _ (Iso.refl _)
  rw [h3, h4]
  linarith

end Stacks.Models

end
