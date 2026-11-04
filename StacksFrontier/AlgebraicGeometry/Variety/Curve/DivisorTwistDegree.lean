module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Symmetry
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.IdealSheafSequence.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of an effective Cartier divisor and of a twist by it

Let `k` be a field, let `X` be a proper scheme of dimension at most one over `k` and let `D` be
an effective Cartier divisor on `X`. Then `D` is finite over `Spec(k)` of degree
`deg(D) = dim_k Γ(D, 𝒪_D)`, and for a finite locally free `ℰ` of rank `n`

`deg(ℰ(D)) = n · deg(D) + deg(ℰ)`,  where `ℰ(D) = ℰ ⊗_{𝒪_X} 𝒪_X(D)`.

Those are the three assertions of **[Stacks, Tag 0AYY]**, and this file proves the third and then
all three together.

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `curveDegree_invertibleSheaf_eq_finrank_globalSections`: `deg(𝒪_X(D)) = dim_k Γ(D, 𝒪_D)`, the
  degree formula at `ℰ = 𝒪_X` and `n = 1`, which is the whole arithmetic content of the tag.
* `isFiniteLocallyFreeOfRank_one_invertibleSheaf` and
  `isFiniteLocallyFreeOfRank_one_negativeTwist`: `𝒪_X(D)` and `𝒪_X(-D) = ℐ_D` are finite locally
  free of rank one.
* `isFiniteLocallyFreeOfRank_tensorSheaf_invertibleSheaf`: `ℰ(D)` is finite locally free of
  rank `n` when `ℰ` is, which is what makes `deg(ℰ(D))` meaningful at rank `n`.
* `isFinite_and_curveDegree_tensorSheaf_invertibleSheaf`: **the whole of [Stacks, Tag 0AYY]** in
  one statement — finiteness of `D` over the base field, its degree being `dim_k Γ(D, 𝒪_D)`, and
  the twist formula at that same number.

## Implementation notes

**The route is the ideal sequence, not the twisted one.** The source's proof tensors
`0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` with `ℰ(D)` and reads off the Euler characteristics. Doing that
needs `i^* ℰ(D)` to be identified on `D`, where the normal bundle `i^* 𝒪_X(D)` is not trivial as
written. The untwisted sequence avoids it entirely: additivity of the Euler characteristic
([Stacks, Tag 08AA], proved unconditionally as
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact`) along
`Stacks.IdealSheafSequence.divisorIdeal_shortExact` — which is [Stacks, Tag 0C6K] and needs no
effective-Cartier hypothesis — gives `χ(𝒪_X) = χ(ℐ_D) + χ(i_* 𝒪_D)`, so that

`deg(ℐ_D) = χ(ℐ_D) - χ(𝒪_X) = -χ(i_* 𝒪_D) = -dim_k Γ(D, 𝒪_D)`.

The last equality is `χ(X, i_* 𝒪_D) = χ(D, 𝒪_D)` for a closed immersion
(`AlgebraicGeometry.eulerCharacteristic_pushforward_of_isClosedImmersion`), then vanishing of the
higher cohomology on the affine `D`
(`AlgebraicGeometry.eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_isFinite`, whose
`IsFinite` hypothesis is the *first* assertion of this tag, proved as
`AlgebraicGeometry.isFinite_divisorSubscheme`), and finally `H⁰ = Γ` `k`-linearly
(`AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections`).

Passing from `deg(ℐ_D)` to `deg(𝒪_X(D))`, and from there to `deg(ℰ(D))`, is [Stacks, Tag 0AYX] in
its unconditional form
`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one`: applied to the
evaluation pairing `𝒪_X(D) ⊗ ℐ_D ≅ 𝒪_X` it gives `deg(𝒪_X(D)) = -deg(ℐ_D)`, since `deg(𝒪_X) = 0`;
applied to `ℰ ⊗ 𝒪_X(D)` it gives `deg(ℰ(D)) = deg(ℰ) + n · deg(𝒪_X(D))`.

**The pairing is `Stacks.SheafOfModules.Scheme.evaluationIso` at `ℐ_D`** and is used inline: the
sheaf `𝒪_X(D)` is *defined* as the dual of `ℐ_D`, so the pairing of [Stacks, Tag 01WX] is that
evaluation with no restatement. `Stacks.Models.invertibleSheafTensorNegativeTwistIsoUnit` is the
same isomorphism, named there for the component degrees of a regular proper model; it is not
imported here because that file lies downstream of this one.

**The rank index of `curveDegree` is `n`, not `n * 1`.** Tag 0AYX concludes at the rank
`n * m` of the tensor product, which at `m = 1` is `n * 1`, and `n * 1` is not syntactically `n`.
`AlgebraicGeometry.curveDegree` ignores its `IsFiniteLocallyFreeOfRank` argument — the rank
enters the body only through the coefficient `(rank : ℤ)` of `χ(𝒪_X)` — so the private
`curveDegree_rank_congr` moves the degree between two equal ranks with no transport, and the
statement is at the rank `n` the source gives `ℰ(D)`.

**The `k`-algebra structure on `Γ(D, 𝒪_D)`** is the one induced by the structure morphism
`D.subschemeι ≫ f` of the divisor, as in
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_divisorSubscheme`; it appears as a `letI` in the
statement, and it is the structure in which
`AlgebraicGeometry.finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections` compares `H⁰`
with `Γ`.

## References

* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

section

variable [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-! ### Ranks -/

/-- The degree of a finite locally free sheaf depends on its rank but not on the instance
witnessing it: `AlgebraicGeometry.curveDegree` uses that argument nowhere in its body. -/
private theorem curveDegree_rank_congr (E : X.Modules) {r r' : ℕ} (h : r = r')
    (i : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r)
    (i' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r') :
    @curveDegree k _ X f _ hdim E r i = @curveDegree k _ X f _ hdim E r' i' := by
  subst h; rfl

/-- **The sheaf `𝒪_X(D)` of an effective Cartier divisor is finite locally free of rank one**,
being invertible ([Stacks, Tag 01WX] (1)). -/
theorem isFiniteLocallyFreeOfRank_one_invertibleSheaf :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
      (Stacks.Divisors.invertibleSheaf' D) 1 :=
  have : Stacks.Ample.IsInvertibleModule X (Stacks.Divisors.invertibleSheaf' D) :=
    Stacks.Divisors.invertibleSheaf_isInvertible D
  Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X _

/-- **The ideal sheaf `𝒪_X(-D) = ℐ_D` of an effective Cartier divisor is finite locally free of
rank one**, that being what the effective-Cartier condition asserts. -/
theorem isFiniteLocallyFreeOfRank_one_negativeTwist :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
      (Stacks.Divisors.negativeTwist' D) 1 :=
  have : Stacks.Ample.IsInvertibleModule X (Stacks.Divisors.negativeTwist' D) :=
    Stacks.Divisors.isInvertible_negativeTwist D
  Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule X _

/-- **The twist `ℰ(D) = ℰ ⊗_{𝒪_X} 𝒪_X(D)` of a finite locally free sheaf of rank `n` is finite
locally free of rank `n`**: the tensor product of finite locally free sheaves of ranks `n` and
`1` has rank `n * 1`. -/
theorem isFiniteLocallyFreeOfRank_tensorSheaf_invertibleSheaf (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
        ((Stacks.Divisors.invertibleSheaf' D)))) n :=
  have := isFiniteLocallyFreeOfRank_one_invertibleSheaf D
  mul_one n ▸ SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E _ n 1

/-! ### The degree of `𝒪_X(D)` -/

/-- **The degree of `𝒪_X(D)` is the dimension of the ring of global sections of `D`**:

`deg(𝒪_X(D)) = dim_k Γ(D, 𝒪_D)`,

for `D` an effective Cartier divisor on a proper scheme of dimension at most one over a field.

This is [Stacks, Tag 0AYY]'s degree formula at `ℰ = 𝒪_X`, `n = 1`, and it carries the whole
computation: additivity of the Euler characteristic along `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0`
identifies `-deg(ℐ_D)` with `χ(D, 𝒪_D) = dim_k Γ(D, 𝒪_D)`, and the evaluation pairing
`𝒪_X(D) ⊗ ℐ_D ≅ 𝒪_X` with [Stacks, Tag 0AYX] identifies `deg(𝒪_X(D))` with `-deg(ℐ_D)`. -/
theorem curveDegree_invertibleSheaf_eq_finrank_globalSections :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    @curveDegree k _ X f _ hdim (Stacks.Divisors.invertibleSheaf' D) 1
        (isFiniteLocallyFreeOfRank_one_invertibleSheaf D) =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) := by
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  have hXLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hfin : IsFinite (D.subschemeι ≫ f) := isFinite_divisorSubscheme k f hdim D
  have hZLN : IsLocallyNoetherian D.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion D.subschemeι
  have hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hOZ : SheafOfModules.IsCoherent (SheafOfModules.unit D.subscheme.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent D.subscheme
  have hpush : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward D.subschemeι).obj
        (SheafOfModules.unit D.subscheme.ringCatSheaf)) :=
    isCoherent_pushforward_of_isClosedImmersion D.subschemeι _
  have hiI : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.Divisors.negativeTwist' D) := Stacks.Divisors.isTensorInvertible_negativeTwist D
  have hcI : SheafOfModules.IsCoherent (Stacks.Divisors.negativeTwist' D) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X _
  have h1I := isFiniteLocallyFreeOfRank_one_negativeTwist D
  have h1O := isFiniteLocallyFreeOfRank_one_invertibleSheaf D
  have hten : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := X.ringCatSheaf)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
        ((Stacks.Divisors.invertibleSheaf' D))).obj ((Stacks.Divisors.negativeTwist' D)))) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X _ _ 1 1
  -- additivity of `χ` along the ideal sequence `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0`
  obtain ⟨hz, hse⟩ := Stacks.IdealSheafSequence.divisorIdeal_shortExact D
  have hadd : @eulerCharacteristic k _ X f _ (SheafOfModules.unit X.ringCatSheaf) hOX =
      @eulerCharacteristic k _ X f _ (Stacks.Divisors.negativeTwist' D) hcI +
        @eulerCharacteristic k _ X f _
          ((Scheme.Modules.pushforward D.subschemeι).obj
            (SheafOfModules.unit D.subscheme.ringCatSheaf)) hpush :=
    @eulerCharacteristic_add_of_shortExact k _ X f _ _ hse hcI hOX hpush
  -- `χ(X, i_* 𝒪_D) = χ(D, 𝒪_D) = dim_k H⁰(D, 𝒪_D) = dim_k Γ(D, 𝒪_D)`
  have hchi : @eulerCharacteristic k _ X f _
      ((Scheme.Modules.pushforward D.subschemeι).obj
        (SheafOfModules.unit D.subscheme.ringCatSheaf)) hpush =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) := by
    rw [eulerCharacteristic_pushforward_of_isClosedImmersion k D.subschemeι f
      (SheafOfModules.unit D.subscheme.ringCatSheaf) hOZ hpush,
      eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_isFinite k
        (D.subschemeι ≫ f) (SheafOfModules.unit D.subscheme.ringCatSheaf) hOZ]
    exact congrArg _ (finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k
      (D.subschemeι ≫ f))
  -- `deg(ℐ_D) = χ(ℐ_D) - χ(𝒪_X)` by the definition of the degree
  have hdegI : @curveDegree k _ X f _ hdim (Stacks.Divisors.negativeTwist' D) 1 h1I =
      @eulerCharacteristic k _ X f _ (Stacks.Divisors.negativeTwist' D) hcI -
        (1 : ℤ) * @eulerCharacteristic k _ X f _ (SheafOfModules.unit X.ringCatSheaf) hOX :=
    @curveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim
      (Stacks.Divisors.negativeTwist' D) 1 h1I hcI hOX
  -- `deg(𝒪_X(D) ⊗ ℐ_D) = deg(𝒪_X) = 0` through the evaluation pairing
  have htensor0 : @curveDegree k _ X f _ hdim
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
        ((Stacks.Divisors.invertibleSheaf' D))).obj
        ((Stacks.Divisors.negativeTwist' D)))) 1 hten = 0 := by
    rw [@curveDegree_eq_of_iso k _ X f _ hdim _ (SheafOfModules.unit X.ringCatSheaf) 1 hten
      (SheafOfModules.isFiniteLocallyFreeOfRank_unit X)
      (Stacks.SheafOfModules.Scheme.evaluationIso X (Stacks.Divisors.negativeTwist' D))]
    exact @curveDegree_unit_eq_zero k _ X f _ hdim hOX
  -- [Stacks, Tag 0AYX] at `𝒪_X(D) ⊗ ℐ_D`
  have h0AYX : @curveDegree k _ X f _ hdim
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((Stacks.Divisors.invertibleSheaf' D))).obj
          ((Stacks.Divisors.negativeTwist' D)))) 1 hten =
      (1 : ℤ) * @curveDegree k _ X f _ hdim (Stacks.Divisors.invertibleSheaf' D) 1 h1O +
        (1 : ℤ) * @curveDegree k _ X f _ hdim (Stacks.Divisors.negativeTwist' D) 1 h1I :=
    curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k f hdim
      (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.negativeTwist' D) 1 1
  rw [htensor0] at h0AYX
  omega

/-! ### The tag -/

/-- **[Stacks, Tag 0AYY].** Let `k` be a field, let `X` be a proper scheme of dimension at most
one over `k` and let `D` be an effective Cartier divisor on `X`. Then `D` is finite over
`Spec(k)`, of degree

`deg(D) = dim_k Γ(D, 𝒪_D)`,

and for a finite locally free `ℰ` of rank `n`,

`deg(ℰ(D)) = n · deg(D) + deg(ℰ)`,  where `ℰ(D) = ℰ ⊗_{𝒪_X} 𝒪_X(D)`.

The three assertions are about one and the same number `dim_k Γ(D, 𝒪_D)`: it is the rank of the
finite locally free morphism `D ⟶ Spec(k)` — which is what "finite of degree `deg(D)`" asserts —
and it is the coefficient of `n` in the twist formula.

Finiteness and the degree are `AlgebraicGeometry.isFinite_divisorSubscheme` and
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_divisorSubscheme`. The twist formula is
[Stacks, Tag 0AYX], i.e.
`AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one`,
at `ℰ` and `𝒪_X(D)`, whose `deg(𝒪_X(D))` term is
`AlgebraicGeometry.curveDegree_invertibleSheaf_eq_finrank_globalSections`. -/
@[stacks 0AYY]
theorem isFinite_and_curveDegree_tensorSheaf_invertibleSheaf (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    IsFinite (D.subschemeι ≫ f) ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f)
          (Module.finrank k Γ(D.subscheme, ⊤)) ∧
        @curveDegree k _ X f _ hdim
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
              ((Stacks.Divisors.invertibleSheaf' D)))) n
            (isFiniteLocallyFreeOfRank_tensorSheaf_invertibleSheaf D E n) =
          (n : ℤ) * (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) + curveDegree k f hdim E n := by
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  refine ⟨isFinite_divisorSubscheme k f hdim D,
    isFiniteLocallyFreeOfRank_divisorSubscheme k f hdim D, ?_⟩
  have h1O := isFiniteLocallyFreeOfRank_one_invertibleSheaf D
  have hdeg : @curveDegree k _ X f _ hdim (Stacks.Divisors.invertibleSheaf' D) 1 h1O =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) :=
    curveDegree_invertibleSheaf_eq_finrank_globalSections k f hdim D
  have h0AYX : @curveDegree k _ X f _ hdim
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
          ((Stacks.Divisors.invertibleSheaf' D)))) (n * 1)
        (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E _ n 1) =
      (1 : ℤ) * curveDegree k f hdim E n +
        (n : ℤ) * @curveDegree k _ X f _ hdim (Stacks.Divisors.invertibleSheaf' D) 1 h1O :=
    curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one k f hdim E
      (Stacks.Divisors.invertibleSheaf' D) n 1
  rw [curveDegree_rank_congr k f hdim
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
        ((Stacks.Divisors.invertibleSheaf' D))))
      (mul_one n).symm (isFiniteLocallyFreeOfRank_tensorSheaf_invertibleSheaf D E n)
      (SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E _ n 1), h0AYX, hdeg]
  ring

end

end AlgebraicGeometry

end
