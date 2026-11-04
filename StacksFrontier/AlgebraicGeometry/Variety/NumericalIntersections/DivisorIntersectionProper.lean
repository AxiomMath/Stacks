module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionBound
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorFirstDifference
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 0BEU, unconditionally

`AlgebraicGeometry.intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor` proves
[Stacks, Tag 0BEU] with one hypothesis beyond the tag's own data: finite dimensionality over `k`
of the cohomology of every coherent module on `X`, which is [Stacks, Tag 02O6].  That hypothesis
is now a theorem — `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`,
which is [Stacks, Tag 02O6] as proved in
`StacksFrontier/AlgebraicGeometry/ProperCoherenceWitness/ChowStalk.lean`, read in the
`AlgebraicGeometry.cohomologyOverField` spelling.

A second hypothesis of that statement is `hdD`, the bound `dim D ≤ d` on the dimension of the
divisor.  Tag 0BEU does not assume it either: it is a consequence of `hd`, because an effective
Cartier divisor is nowhere dense and therefore loses a dimension.  Discharging both gives the
tag with nothing carried.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper`:
  an effective Cartier divisor on a closed subscheme of dimension at most `d + 1` of a proper
  `k`-scheme has dimension at most `d`.
* `AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor'`:
  **[Stacks, Tag 0BEU].**  For `X` proper over a field `k`, a closed subscheme `i : Z ⟶ X` of
  dimension at most `d + 1`, invertible `𝒪_X`-modules `𝓛_1, …, 𝓛_{d+1}` and an effective Cartier
  divisor `D ⊆ Z` with `𝓛_1|_Z ≅ 𝒪_Z(D)`,
  `(𝓛_1 ⋯ 𝓛_{d+1} · Z) = (𝓛_2 ⋯ 𝓛_{d+1} · D)`.  **No hypothesis.**
* `AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor`: the intermediate form,
  with `hfin` discharged but `hdD` still an argument.

## Implementation notes

The statement of the intermediate form is that of
`AlgebraicGeometry.intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor`
verbatim, with `hfin` removed.  The dimension bound `hd` is an argument of
`AlgebraicGeometry.intersectionNumber` itself, so it is part of the tag's data and not a
hypothesis carried past it, and the isomorphism `hL` is the tag's own assumption that `𝓛_1`
restricts to the divisor's invertible sheaf.  The bound `hdD` is an argument of
`AlgebraicGeometry.intersectionNumber` too, but not part of the tag's data, so the tagged
statement supplies it rather than asking for it.

The dimension drop is
`AlgebraicGeometry.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor`, which needs the
underlying space of `Z` to be Noetherian.  That is where properness is used a second time: a
proper morphism is locally of finite type and quasi-compact, so `X` is a Noetherian scheme, and
the closed immersion `i` induces the topology of `Z` from it.

## References

* [Stacks Project, Tag 0BEU](https://stacks.math.columbia.edu/tag/0BEU)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules.Invertible
open Stacks.Divisors

/-- **[Stacks, Tag 0BEU].**  Let `k` be a field, let `X` be a scheme proper over `k`, let
`i : Z ⟶ X` be a closed subscheme of dimension at most `d + 1` and let `𝓛_1, …, 𝓛_{d+1}` be
invertible `𝒪_X`-modules.  Let `D ⊆ Z` be an effective Cartier divisor of dimension at most `d`
with `𝓛_1|_Z ≅ 𝒪_Z(D)`.  Then

`(𝓛_1 ⋯ 𝓛_{d+1} · Z) = (𝓛_2 ⋯ 𝓛_{d+1} · D)`,

the intersection number of the divisor being taken along the composite closed immersion
`D ⟶ Z ⟶ X`.

This is
`AlgebraicGeometry.intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor` with
its hypothesis `hfin` discharged by
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`, which is
[Stacks, Tag 02O6].

The bound `hdD` on the dimension of the divisor is still an argument here; it is *not* part of
Tag 0BEU's data, being a consequence of `hd`, and it is discharged in
`AlgebraicGeometry.intersectionNumber_eq_of_isEffectiveCartierDivisor'`, which therefore carries
the tag with no bound to supply. This form keeps its own registration. -/
@[stacks 0BEU "taking the divisor's dimension bound as an argument"]
public theorem intersectionNumber_eq_of_isEffectiveCartierDivisor
    (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (L : Fin (d + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)]
    (Dv : Z.IdealSheafData) [hDv : IsEffectiveCartierDivisor Dv]
    (hdD : topologicalKrullDim Dv.subscheme ≤ d)
    (hL : (Scheme.Modules.pullback i).obj (L 0) ≅ (invertibleSheaf Dv : Z.Modules)) :
    intersectionNumber k f i (d + 1) hd L =
      intersectionNumber k f (Dv.subschemeι ≫ i) d hdD fun t : Fin d => L t.succ :=
  intersectionNumber_eq_intersectionNumber_of_isEffectiveCartierDivisor k f i d hd L Dv hdD hL
    (forall_finiteDimensional_cohomologyOverField_of_isProper k f)

/-- **An effective Cartier divisor on a closed subscheme of a proper `k`-scheme of dimension at
most `d + 1` has dimension at most `d`**, so its intersection number against `d` invertible
modules is defined.  A proper morphism is locally of finite type and quasi-compact, so `X` is a
Noetherian scheme and `Z`, carrying the topology induced by the closed immersion `i`, has a
Noetherian space; the bound is then
`AlgebraicGeometry.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor`. -/
@[ega "IV 4.1.2.1" "rare ⇒ dim(Z) < dim(Y)"]
public theorem topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper
    (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (Dv : Z.IdealSheafData)
    [hDv : IsEffectiveCartierDivisor Dv] :
    topologicalKrullDim Dv.subscheme ≤ (d : WithBot ℕ∞) := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hcpt : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hnoe : IsNoetherian X := ⟨⟩
  have hZ : TopologicalSpace.NoetherianSpace Z :=
    i.isEmbedding.toIsInducing.noetherianSpace
  exact topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor Dv hDv d hd

/-- **[Stacks, Tag 0BEU].**  Let `k` be a field, let `X` be a scheme proper over `k`, let
`i : Z ⟶ X` be a closed subscheme of dimension at most `d + 1` and let `𝓛_1, …, 𝓛_{d+1}` be
invertible `𝒪_X`-modules.  Let `D ⊆ Z` be an effective Cartier divisor with
`𝓛_1|_Z ≅ 𝒪_Z(D)`.  Then

`(𝓛_1 ⋯ 𝓛_{d+1} · Z) = (𝓛_2 ⋯ 𝓛_{d+1} · D)`,

the intersection number of the divisor being taken along the composite closed immersion
`D ⟶ Z ⟶ X`.

This is the tag with nothing assumed.  Beyond `hd`, `hL` and the effective Cartier divisor
instance — which are the tag's own data — it has no hypothesis: the dimension bound
`dim D ≤ d` that the right-hand intersection number needs is supplied by
`AlgebraicGeometry.topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper`,
since an effective Cartier divisor is nowhere dense and so loses a dimension. -/
@[stacks 0BEU "the intersection number of a closed subscheme against invertible modules equals
that of an effective Cartier divisor cutting out the first module's restriction"]
public theorem intersectionNumber_eq_of_isEffectiveCartierDivisor'
    (k : Type u) [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z ≤ (d + 1 : ℕ)) (L : Fin (d + 1) → X.Modules)
    [∀ t, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L t)]
    (Dv : Z.IdealSheafData) [hDv : IsEffectiveCartierDivisor Dv]
    (hL : (Scheme.Modules.pullback i).obj (L 0) ≅ (invertibleSheaf Dv : Z.Modules)) :
    intersectionNumber k f i (d + 1) hd L =
      intersectionNumber k f (Dv.subschemeι ≫ i) d
        (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k f i d hd Dv)
        fun t : Fin d => L t.succ :=
  intersectionNumber_eq_of_isEffectiveCartierDivisor k f i d hd L Dv _ hL

end AlgebraicGeometry

end
