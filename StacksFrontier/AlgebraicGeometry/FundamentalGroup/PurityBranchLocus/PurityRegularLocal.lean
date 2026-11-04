module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.PurityRegularDimensionTwo
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularPurity

/-!
# Clause (2) of purity for a regular local ring of any dimension at least two

Let `A` be a regular local ring of dimension `d ≥ 2`. Clause (1) of [Stacks, Tag 0BMA] says that
purity holds for `A`: every finite étale cover of the punctured spectrum of `A` extends to a
finite étale cover of `Spec A`. That is `AlgebraicGeometry.purityAtRegularLocalRings`, the
predicate `AlgebraicGeometry.PurityAtRegularLocalRings`. This file derives clause (2) of the tag
from it, for the same `d`, by the source's own route through [Stacks, Tag 0BM9].

## Main results

* `Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_two_le_ringKrullDim` — clause (2) of the
  tag for every `d ≥ 2`, derived from clause (1) through [Stacks, Tag 0BM9] as the source does.

## What is and is not proved

Clause (2) is proved for every `d ≥ 2`. It is stated with one hypothesis the source omits,
`Module.IsTorsionFree A B`. That is a repair: clause (2) as literally stated in the source is
false, and the counterexample — the residue field `A ⧸ 𝔪` — is recorded in the module docstring
of `StacksFrontier/AlgebraicGeometry/FundamentalGroup/PurityBranchLocus/RegularDimensionTwo.lean`
and in the docstring of the theorem below, together with the reason the two weaker repairs do
not suffice.

## References

* [Stacks Project, Tag 0BMA](https://stacks.math.columbia.edu/tag/0BMA)
* [Stacks Project, Tag 0BM9](https://stacks.math.columbia.edu/tag/0BM9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.PurityDimensionTwo

/-! ### Clause (2) in every dimension -/

/-- **[Stacks, Tag 0BMA] clause (2) for every `d ≥ 2`.** Let `A` be a regular local ring of
dimension at least two and let `B` be a finite `A`-algebra which is a normal ring and
torsion-free over `A`, such that `Spec B ⟶ Spec A` is étale over the punctured spectrum. Then
`A → B` is étale.

This is the source's derivation of clause (2) from clause (1) through [Stacks, Tag 0BM9]: `A` is
normal, so `B` is an object of the category `NormalFiniteEtaleAwayAlgebra A` equivalent to
`(FÉt_U)ᵒᵖ`, hence `B ≅ Γ(V, 𝒪_V)` for some finite étale `V ⟶ U`; purity extends `V` over
`Spec A`, and the extension criterion of [Stacks, Tag 0BM9] then says that `Γ(V, 𝒪_V)` is finite
étale over `A`.

The hypothesis `Module.IsTorsionFree A B` is not in the source, and is necessary: it is exactly
the point at which the source's statement of clause (2) is wrong, and the counterexample is
recorded in the module docstring of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/PurityBranchLocus/RegularDimensionTwo.lean`. In
brief: `B = A ⧸ 𝔪` is finite over `A`, is a field and hence a normal ring, and has empty
punctured spectrum, so it is étale over `U` vacuously; but `A` is a domain with `𝔪 ≠ 0`, so
`A ⧸ 𝔪` is not even flat over `A`; this is proved as
`Stacks.PurityDimensionTwo.quotient_maximalIdeal_counterexample_clauseTwo`. Nor does it help to
ask only that `algebraMap A B` be injective, or that `Spec B ⟶ Spec A` be surjective:
`B = A × (A ⧸ 𝔪)` is a finite normal `A`-algebra satisfying both, is the identity over `U`, and
is not flat over `A`. -/
@[stacks 0BMA "clause (2) of the tag, at every `d ≥ 2`: `A` regular local with \
`2 ≤ ringKrullDim A`, `B` a finite `A`-algebra which is a normal ring in the sense of \
`IsNormalRing` (item (1) of tag 030C) and is torsion-free over `A`, and `Spec B ⟶ Spec A` \
étale over the punctured spectrum; the conclusion is `Algebra.Etale A B`. The source's \
derivation from clause (1) through tag 0BM9 is the proof, and clause (1) at every `d ≥ 2` is \
`AlgebraicGeometry.purityAtRegularLocalRings`. Torsion-freeness over `A` is an extra \
hypothesis, not present in the source and necessary for the statement to be true: the residue \
field `A ⧸ 𝔪` is a finite normal `A`-algebra whose spectrum misses the punctured spectrum, hence \
is étale there, and is not flat over `A`. Weakening it to injectivity of `algebraMap A B`, or to \
surjectivity of `Spec B ⟶ Spec A`, leaves the statement false as well: `B = A × (A ⧸ 𝔪)` is a \
finite normal `A`-algebra with both properties which is the identity over the punctured spectrum \
and is not flat over `A`. That clause (2) as literally stated is false is proved in \
`Stacks.PurityDimensionTwo.quotient_maximalIdeal_counterexample_clauseTwo` \
(`PurityBranchLocus.PurityClauseTwoCounterexample`); see also the module docstring of \
`PurityBranchLocus.RegularDimensionTwo`.",
  sga "1 X 3.2" "Case B finite over A",
  sga "4½ Arcata 5.2.4" "special case"]
public theorem etale_of_isNormalRing_of_two_le_ringKrullDim
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsRegularLocalRing A]
    [Module.Finite A B] [Module.IsTorsionFree A B] (hB : IsNormalRing B)
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (hetale : Etale (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_
      Stacks.puncturedSpectrum A)) :
    Algebra.Etale A B := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  have hA : IsNormalRing A := IsNormalRing.of_isIntegrallyClosed A
  have hiso : MorphismProperty.RespectsIso (@Etale.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hetB : Etale (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Stacks.puncturedSpectrum A).ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) (Stacks.puncturedSpectrum A)]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Etale) _ _).mpr hetale
  -- `B` as an object of the category of [Stacks, Tag 0BM9].
  let BB : NormalPurity.NormalFiniteEtaleAwayAlgebra A :=
    ⟨CommAlgCat.of A B, ⟨inferInstance, hB, inferInstance, hetB⟩⟩
  obtain ⟨F, hF, ⟨nat⟩⟩ :=
    NormalPurity.globalSections_isEquivalence_normalFiniteEtaleAwayAlgebra A hA hdim
  let : F.IsEquivalence := hF
  obtain ⟨V, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage F BB
  have : IsFinite V.unop.hom := V.unop.prop.1
  have : Etale V.unop.hom := V.unop.prop.2
  let : Algebra A Γ(V.unop.left, ⊤) := NormalPurity.globalSectionsAlgebra A V.unop
  obtain ⟨-, hetΓ⟩ :=
    (NormalPurity.exists_finiteEtale_extension_iff_globalSections_finiteEtale A hA hdim
      V.unop.left V.unop.hom).mp
      (exists_isPullback_of_mem_essImage _ V.unop
        ((purityAtRegularLocalRings A hdim).mem_essImage V.unop))
  have : Algebra.Etale A ↑((NormalPurity.globalSections A).obj V) := hetΓ
  exact Algebra.Etale.of_equiv (R := A)
    (CommAlgCat.algEquivOfIso ((nat.app V).symm ≪≫ (ObjectProperty.ι _).mapIso e))

end Stacks.PurityDimensionTwo

/-! ### Clause (1)

Clause (1) of Stacks 0BMA, purity at every regular local ring of dimension `d ≥ 2`, is the base
declaration `AlgebraicGeometry.purityAtRegularLocalRings`; it is registered here. -/

add_to_stacks 0BMA "clause (1) of the tag, at every `d ≥ 2`: for every regular local ring `A` with
  `2 ≤ ringKrullDim A`, `AlgebraicGeometry.HasPurity A`, i.e. essential surjectivity of
  `FÉt_{Spec A} ⟶ FÉt_U` for `U` the punctured spectrum, which is the source's definition of purity
  for `(A, 𝔪)`."
  AlgebraicGeometry.purityAtRegularLocalRings

end
