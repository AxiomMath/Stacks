module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusSurjectivity
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology

/-!
# Étale cohomology with constant coefficients `𝐙/p𝐙` above the dimension

Let `X` be separated and of finite type over an algebraically closed field `k` of characteristic
`p > 0` and let `d = dim(X)`. Then the étale cohomology of the constant sheaf `𝐙/p𝐙` vanishes in
every degree at least `d + 1`.

The argument is the one of the source. In degrees at least `d + 2` this is the vanishing of
[Stacks, Tag 0A3K] (2), the underlying space of `X` being spectral of dimension `d`. The one
remaining degree `d + 1` is where the hypotheses on `k` enter: the long exact sequence of the
Artin–Schreier sequence `0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0` ends in
`H ^ d (𝐆_a) ⟶[F - 1] H ^ d (𝐆_a) ⟶ H ^ (d + 1) (𝐙/p𝐙) ⟶ 0`, the group `H ^ d (X, 𝒪_X)` is a
finite-dimensional `k`-vector space by [Stacks, Tag 0A3M], and `F - 1` is therefore surjective on
it by [Stacks, Tag 0A3L]; a surjection on the left of that sequence forces the right-hand term to
vanish.

## Main definitions

* `Stacks.ArtinSchreier.TopDegreeFrobeniusComparison`: the comparison, in the top degree, of the
  étale cohomology of `𝐆_a` with the cohomology of the structure sheaf, together with the
  Frobenius-semilinear description of the Artin–Schreier map on it, as a carried datum.

## Main results

* `Stacks.ArtinSchreier.subsingleton_sheafH_X₁_of_shortExact_of_surjective`: the vanishing step of
  the long exact sequence driven by a surjection, rather than by a vanishing, on the left.
* `Stacks.ArtinSchreier.surjective_sheafH_map_of_topDegreeFrobeniusComparison`:
  [Stacks, Tag 0A3L] applied to the top-degree cohomology of the structure sheaf.
* `Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_isAlgClosed`:
  [Stacks, Tag 0A3N] with the inputs below carried. The tag itself is formalized, with nothing
  carried, by `Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_isAlgClosed_unconditional`
  in `ArtinSchreierSequence/TopDegreeVanishingUnconditional.lean`.

## Implementation notes

Three inputs of the source argument are not available in the shape the argument needs and are
carried as explicit hypotheses; everything else is proved here.

The first two are the ones already carried by [Stacks, Tag 0A3K] in the neighbouring module
`ConstantCoefficientVanishing`:
exactness of the Artin–Schreier sequence ([Stacks, Tag 0A3J]), as
`Stacks.ArtinSchreier.ArtinSchreierSequence`, and the comparison of the étale cohomology of `𝐆_a`
with the cohomology of the structure sheaf ([Stacks, Tag 03P2]) in the vanishing-transfer shape,
as `hcomp`. The degree `d + 1` needs that comparison in a second, finer shape as well — an
additive bijection in degree `d` under which the Artin–Schreier map becomes `F - 1` for a
Frobenius-semilinear `F` — and that is `TopDegreeFrobeniusComparison`.

`hcomp` is carried rather than proved only because of the coefficient universe. Its content is a
theorem: `AlgebraicGeometry.subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup` of
`CechComparison/SmallEtaleGlobalCohomology.lean` proves exactly that implication at coefficient
universe `u`, for the associated small étale sheaf of a quasi-coherent module. It does not apply
here, where the Artin–Schreier sequence lives at coefficients `u + 1` with an abstract `𝐆_a`. The
finer shape `TopDegreeFrobeniusComparison` is out of its reach in any universe: the library has
no Frobenius endomorphism of the structure sheaf of the small étale site, that being part of
[Stacks, Tag 0A3J].

The third is [Stacks, Tag 0A3M], the finite dimensionality of `H ^ d (X, 𝒪_X)` over `k`, carried as
`hfin`. The library proves that tag, in
`StacksFrontier/AlgebraicGeometry/TopDegreeCoherentFiniteness/Basic.lean`, only for an affine `X`
and for `dim(X) = 0`, not for a general separated `X` of finite type, so it cannot be discharged
here in general. It is stated in the shape that file uses,
`FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d)`, so that
those two cases do discharge it.

Étale cohomology is Mathlib's `CategoryTheory.Sheaf.H` on `Scheme.smallEtaleTopology` at the
coefficient universe `u + 1`, and the constant sheaf `𝐙/p𝐙` is
`Stacks.ArtinSchreier.etaleConstantZMod`, both as in [Stacks, Tag 0A3K]. Vanishing of a cohomology
group is `Subsingleton`, and the dimension of `X` is `topologicalKrullDim` of its underlying space.

## References

* [Stacks Project, Tag 0A3N](https://stacks.math.columbia.edu/tag/0A3N)
* [Stacks Project, Tag 0A3K](https://stacks.math.columbia.edu/tag/0A3K)
* [Stacks Project, Tag 0A3L](https://stacks.math.columbia.edu/tag/0A3L)
* [Stacks Project, Tag 0A3M](https://stacks.math.columbia.edu/tag/0A3M)
* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the sequence.
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2): the comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w w₁ v₁ u₁ u

namespace Stacks.ArtinSchreier

/-- **The vanishing step of the long exact cohomology sequence, surjective form.** Let `T` be a
short exact sequence of abelian sheaves on a site. If the map `H ^ n₀ (T.X₂) ⟶ H ^ n₀ (T.X₃)` is
surjective and the cohomology of `T.X₂` vanishes in degree `n₁ = n₀ + 1`, then the cohomology of
`T.X₁` vanishes in degree `n₁`.

A class in `H ^ n₁ (T.X₁)` is killed by the map to `H ^ n₁ (T.X₂)` because the target vanishes,
hence is the image of a class in `H ^ n₀ (T.X₃)` under the connecting map; that class comes from
`H ^ n₀ (T.X₂)`, and the composite of `H ^ n₀ (T.X₂) ⟶ H ^ n₀ (T.X₃)` with the connecting map is
zero. -/
public theorem subsingleton_sheafH_X₁_of_shortExact_of_surjective {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w₁}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w₁})]
    {T : ShortComplex (Sheaf J AddCommGrpCat.{w₁})} (hT : T.ShortExact)
    (n₀ n₁ : ℕ) (hn : n₀ + 1 = n₁)
    (hsurj : ∀ y : Sheaf.H.{w, w₁} T.X₃ n₀,
      ∃ x : Sheaf.H.{w, w₁} T.X₂ n₀, Sheaf.H.map T.g n₀ x = y)
    (h₂ : Subsingleton (Sheaf.H.{w, w₁} T.X₂ n₁)) :
    Subsingleton (Sheaf.H.{w, w₁} T.X₁ n₁) := by
  have key : ∀ x : Sheaf.H.{w, w₁} T.X₁ n₁, x = 0 := by
    intro x
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ hT x (h₂.elim _ _) hn
    obtain ⟨x₂, rfl⟩ := hsurj x₃
    rw [← hx₃, Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass,
      Ext.comp_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

/-- **The top-degree Frobenius comparison for the Artin–Schreier sequence**, a carried datum. For
`X` a scheme over a field `k`, an abelian sheaf `Ga` on the small étale site of `X` with an
endomorphism `φ`, and a degree `d`, this records an additive bijection between `H ^ d (Ga)` and
`H ^ d (X, 𝒪_X)` under which `φ` becomes `F - 1` for a Frobenius-semilinear `F`.

This is the comparison of [Stacks, Tag 03P2] in the shape the top degree of the source's argument
uses: the library has neither the Frobenius endomorphism of the structure sheaf of the small étale
site nor the comparison of its étale cohomology with the cohomology of `𝒪_X`, so the identification
of the Artin–Schreier map with a Frobenius-semilinear `F - 1` cannot be constructed here. Carrying
it in this shape is what lets [Stacks, Tag 0A3L] and [Stacks, Tag 0A3M], which are statements about
a finite-dimensional `k`-vector space, apply to `H ^ d (Ga)`. -/
public structure TopDegreeFrobeniusComparison (p : ℕ) (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (Ga : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : Ga ⟶ Ga) (d : ℕ) where
  /-- The comparison of the degree-`d` étale cohomology of `Ga` with `H ^ d (X, 𝒪_X)`. -/
  equiv : Sheaf.H.{w, u + 1} Ga d ≃+
    cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d
  /-- The Frobenius `F` on `H ^ d (X, 𝒪_X)`. -/
  frobenius : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d →+
    cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d
  /-- `F` is Frobenius-semilinear: `F (a • v) = a ^ p • F v`. -/
  frobenius_smul : ∀ (a : k)
    (v : cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d),
    frobenius (a • v) = a ^ p • frobenius v
  /-- Under the comparison, the Artin–Schreier map `φ` becomes `F - 1`. -/
  equiv_map : ∀ x : Sheaf.H.{w, u + 1} Ga d,
    equiv (Sheaf.H.map φ d x) = frobenius (equiv x) - equiv x

/-- **[Stacks, Tag 0A3L] on the top-degree cohomology of the structure sheaf.** Let `X` be a scheme
over an algebraically closed field `k` of characteristic `p > 0`, and suppose that the degree-`d`
étale cohomology of `Ga` is comparable to `H ^ d (X, 𝒪_X)` with the Artin–Schreier map becoming
`F - 1`. If `H ^ d (X, 𝒪_X)` is a finite-dimensional `k`-vector space, then the map induced by `φ`
on `H ^ d (Ga)` is surjective.

The map `F - 1` of a Frobenius-semilinear endomorphism of a finite-dimensional vector space over an
algebraically closed field of positive characteristic is surjective
(`AlgebraicGeometry.frobeniusSemilinear_sub_id_surjective`); the comparison transports that
surjectivity back to `H ^ d (Ga)`. The finite dimensionality is [Stacks, Tag 0A3M]. -/
public theorem surjective_sheafH_map_of_topDegreeFrobeniusComparison {p : ℕ} (hp : 0 < p)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {Ga : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : Ga ⟶ Ga) {d : ℕ}
    (cmp : TopDegreeFrobeniusComparison p k f Ga φ d)
    (hfin : FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d))
    (y : Sheaf.H.{w, u + 1} Ga d) :
    ∃ x : Sheaf.H.{w, u + 1} Ga d, Sheaf.H.map φ d x = y := by
  have := hfin
  obtain ⟨v, hv⟩ := frobeniusSemilinear_sub_id_surjective k hp
    (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d) cmp.frobenius
    cmp.frobenius_smul (cmp.equiv y)
  refine ⟨cmp.equiv.symm v, cmp.equiv.injective ?_⟩
  rw [cmp.equiv_map, cmp.equiv.apply_symm_apply]
  exact hv

/-- **Vanishing above the dimension, with the Artin–Schreier inputs carried.** Let `X` be
separated and of finite type over an algebraically closed field `k` of characteristic `p > 0` and
let `d = dim(X)`, with an Artin–Schreier sequence `AS`, the comparisons `hcomp` and `cmp`, and the
finite dimensionality `hfin`. Then `H ^ q (X_étale, 𝐙/p𝐙) = 0` for every `q ≥ d + 1`.

This is the special case, with those inputs as hypotheses, of [Stacks, Tag 0A3N], which is
`subsingleton_etaleH_constantZMod_of_isAlgClosed_unconditional`.

This is the source's proof. Degrees at least `d + 2` are [Stacks, Tag 0A3K] (2), the underlying
space of `X` being quasi-compact and quasi-separated of dimension `d`. In the remaining degree
`d + 1` the long exact sequence of the Artin–Schreier sequence is used once more, but now the
vanishing of `H ^ d (𝐆_a)` is unavailable and is replaced by the surjectivity of `F - 1` on it,
which `surjective_sheafH_map_of_topDegreeFrobeniusComparison` deduces from [Stacks, Tag 0A3L] and
the finite dimensionality `hfin` of [Stacks, Tag 0A3M]. -/
public theorem subsingleton_etaleH_constantZMod_of_isAlgClosed {p : ℕ} (hp : 0 < p) (k : Type u)
    [Field k] [IsAlgClosed k] [CharP k p] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology (X : Type u)) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (AS : ArtinSchreierSequence p X)
    (hcomp : ∀ i : ℕ,
      IsZero (Hgroup X.ringCatSheaf ⊤ i (SheafOfModules.unit X.ringCatSheaf)) →
        Subsingleton (Sheaf.H.{w, u + 1} AS.Ga i))
    (d : ℕ) (hd : topologicalKrullDim (X : Type u) = (d : WithBot ℕ∞))
    (cmp : TopDegreeFrobeniusComparison p k f AS.Ga AS.φ d)
    (hfin : FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d))
    (q : ℕ) (hq : d + 1 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q) := by
  have : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : X.IsSeparated := by
    refine ⟨?_⟩
    have : IsSeparated (f ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa using this
  have : QuasiSeparatedSpace (X : Type u) := inferInstance
  rcases Nat.lt_or_ge q (d + 2) with hq₂ | hq₂
  · obtain rfl : q = d + 1 := by omega
    refine subsingleton_sheafH_X₁_of_shortExact_of_surjective AS.shortExact d (d + 1) rfl
      (surjective_sheafH_map_of_topDegreeFrobeniusComparison hp k f AS.φ cmp hfin)
      (hcomp (d + 1) ?_)
    exact Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology
      (SheafOfModules.unit X.ringCatSheaf) (d + 1) (by omega)
      (Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le d (X : Type u)
        inferInstance inferInstance
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf))
        (d + 1) hd.le (by omega))
  · exact subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le p X AS hcomp d hd.le q hq₂

end Stacks.ArtinSchreier

end
