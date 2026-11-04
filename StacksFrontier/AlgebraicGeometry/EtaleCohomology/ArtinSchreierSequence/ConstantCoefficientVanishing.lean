module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ZMod.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.HgroupOfSheafCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Étale cohomology with constant coefficients `𝐙/p𝐙` in characteristic `p`

Let `p` be a prime and let `S` be a scheme of characteristic `p`. The étale cohomology of the
constant sheaf `𝐙/p𝐙` vanishes in degrees at least two when `S` is affine, and in degrees at
least `d + 2` when `S` is quasi-compact, quasi-separated of dimension at most `d`.

The argument is the one of the source. The Artin–Schreier sequence
`0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0`, with second map `x ↦ x ^ p - x`, is short exact on the small
étale site; its long exact cohomology sequence squeezes `H ^ q` of `𝐙/p𝐙` between `H ^ (q - 1)`
and `H ^ q` of `𝐆_a`. So any degree above which the cohomology of the structure sheaf vanishes
bounds the cohomology of `𝐙/p𝐙` one degree later. On an affine scheme that degree is `0`, and
on a quasi-compact quasi-separated scheme of dimension `d` it is `d`, the underlying space
being spectral.

## Main definitions

* `Stacks.ArtinSchreier.etaleConstantZMod`: the constant sheaf `𝐙/p𝐙` on the small étale site.
* `Stacks.ArtinSchreier.ArtinSchreierSequence`: the Artin–Schreier short exact sequence on the
  small étale site of a scheme of characteristic `p`, as a carried datum.

## Main results

* `Stacks.ArtinSchreier.subsingleton_sheafH_X₁_of_shortExact`: the vanishing step of the long
  exact cohomology sequence of a short exact sequence of abelian sheaves on any site.
* `Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_hgroup_vanishing`: the
  Artin–Schreier degree shift.
* `Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le`: part (2)
  with the Artin–Schreier sequence and `hcomp` carried. [Stacks, Tag 0A3K] itself is
  formalized, with neither carried, in `ArtinSchreierSequence/ConstantSequenceDatum.lean`.

## Implementation notes

Two inputs of the source argument are not available in the shape the argument needs and are
carried as explicit hypotheses; everything else is proved here.

The first is exactness of the Artin–Schreier sequence itself, carried as
`ArtinSchreierSequence`. The source states the sequence without proving its exactness, which
holds in the étale topology and fails in the Zariski topology. The library has the surjectivity
half for a hypothesized Frobenius-semilinear endomorphism of a finite locally free module
(`AlgebraicGeometry.epi_frobeniusSemilinear_sub_id`), and the linear algebra over a field
behind it, but neither the Frobenius endomorphism of the structure sheaf of the small étale site
nor the identification of the kernel of `F - 1` with the constant sheaf `𝐙/p𝐙`. The
characteristic hypothesis of the source enters the argument only through this datum, and is
recorded as the field `natCast_eq_zero`.

The second is the comparison of the étale cohomology of `𝐆_a` with the cohomology of the
structure sheaf on the underlying topological space, carried as `hcomp` in the weakest shape the
argument uses, a transfer of vanishing from the one to the other, so that the Zariski-side
vanishing theorems still do the work of distinguishing the two parts.

That comparison is the source's cited theorem [Stacks, Tag 03P2], and it **is** in the library:
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`, in the `CechComparison`
directory of this chapter, carries `@[stacks 03P2]` for the case `𝒞 = S_étale`. It does not
discharge `hcomp`, for two reasons of shape rather than of content. It is stated for
`CategoryTheory.Sheaf.H'`, `Ext` out of the free abelian sheaf on the Yoneda presheaf of an
object, with the `Ext` universe at the morphism universe `u` on both sides, whereas `hcomp` speaks
of `CategoryTheory.Sheaf.H`, `Ext` out of the constant sheaf `𝐙`; and its étale coefficient
`AlgebraicGeometry.smallEtaleAssociatedSheaf` lives in `AddCommGrpCat.{u}`, whereas the
Artin–Schreier sequence here lives in `AddCommGrpCat.{u + 1}`. The first gap is closed, in
`AlgebraicGeometry.subsingleton_sheafH_smallEtaleAssociatedSheaf_of_isZero_hgroup` of
`CechComparison/SmallEtaleGlobalCohomology.lean`: that is exactly `hcomp`, proved, at coefficient
universe `u` and for the associated sheaf of a quasi-coherent module. What is left is the
coefficient universe, and `𝐆_a` being a carried datum here rather than the associated sheaf of
the structure sheaf, so a `hcomp` discharged in place would need the sequence of
[Stacks, Tag 0A3J] first.

Étale cohomology is Mathlib's `CategoryTheory.Sheaf.H` on `Scheme.smallEtaleTopology`, at the
coefficient universe `u + 1`. Sheafification is not what forces that choice: the small étale
site of `S : Scheme.{u}` has `HasSheafify` at `AddCommGrpCat.{u}` as well. What `u + 1` is is the
coefficient universe at which sections on this site are corepresented, the site having its
objects in `Type (u + 1)` and its homs in `Type u`; it is the universe the statements of this
file and of the vanishing theorems they feed use. The structure-sheaf side is
`Hgroup`, the derived global sections of a sheaf of modules, which is the form in which the two
vanishing theorems used here are stated. Vanishing of a cohomology group is `Subsingleton` on the
étale side and `Limits.IsZero` on the module side, following the two sources.

## References

* [Stacks Project, Tag 0A3K](https://stacks.math.columbia.edu/tag/0A3K)
* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the sequence.
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2): the comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w w₁ v₁ u₁ u

namespace Stacks.ArtinSchreier

/-- The constant sheaf `𝐙/p𝐙` on the small étale site of a scheme. -/
public noncomputable abbrev etaleConstantZMod (S : Scheme.{u}) (p : ℕ) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))

/-- **The vanishing step of the long exact cohomology sequence.** Let `T` be a short exact
sequence of abelian sheaves on a site. If the cohomology of `T.X₃` vanishes in degree `n₀` and
that of `T.X₂` in degree `n₁ = n₀ + 1`, then the cohomology of `T.X₁` vanishes in degree `n₁`.

The three groups sit in the exact sequence
`H ^ n₀ (T.X₃) ⟶ H ^ n₁ (T.X₁) ⟶ H ^ n₁ (T.X₂)` of the long exact sequence: a class in the
middle is killed by the right map because the target vanishes, hence comes from the left, which
vanishes too. -/
public theorem subsingleton_sheafH_X₁_of_shortExact {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{w₁}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w₁})]
    {T : ShortComplex (Sheaf J AddCommGrpCat.{w₁})} (hT : T.ShortExact)
    (n₀ n₁ : ℕ) (hn : n₀ + 1 = n₁)
    (h₃ : Subsingleton (Sheaf.H.{w, w₁} T.X₃ n₀))
    (h₂ : Subsingleton (Sheaf.H.{w, w₁} T.X₂ n₁)) :
    Subsingleton (Sheaf.H.{w, w₁} T.X₁ n₁) := by
  have key : ∀ x : Sheaf.H.{w, w₁} T.X₁ n₁, x = 0 := by
    intro x
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ hT x (h₂.elim _ _) hn
    rw [← hx₃, h₃.elim x₃ 0, Ext.zero_comp]
  exact ⟨fun a b => by rw [key a, key b]⟩

/-- **The Artin–Schreier sequence on the small étale site of a scheme of characteristic `p`**,
[Stacks, Tag 0A3J]: the short exact sequence `0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0` whose second map is
`x ↦ x ^ p - x`.

This is a carried datum, not a construction: the source states the sequence and does not prove
its exactness, and the library has neither the Frobenius endomorphism of the structure sheaf of
the small étale site nor the identification of the kernel of `F - 1` with `𝐙/p𝐙`. The middle and
right terms are left as one abelian sheaf `Ga` rather than built, so that a consumer supplies
the sequence it has; the characteristic hypothesis of the source, which the argument uses only
to produce this sequence, is the field `natCast_eq_zero`. -/
public structure ArtinSchreierSequence (p : ℕ) (S : Scheme.{u}) where
  /-- `p` vanishes on `S`, that is, `S` is a scheme of characteristic `p`. -/
  natCast_eq_zero : (p : Γ(S, ⊤)) = 0
  /-- The additive group `𝐆_{a, S}` of the structure sheaf, as an abelian sheaf. -/
  Ga : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  /-- The inclusion of the constant sheaf `𝐙/p𝐙`. -/
  ι : etaleConstantZMod S p ⟶ Ga
  /-- The map `F - 1`, that is, `x ↦ x ^ p - x`. -/
  φ : Ga ⟶ Ga
  /-- The composite of the two maps vanishes. -/
  comp_eq_zero : ι ≫ φ = 0
  /-- The sequence is short exact. -/
  shortExact : (ShortComplex.mk ι φ comp_eq_zero).ShortExact

/-- **The Artin–Schreier degree shift.** Let `S` be a scheme carrying an Artin–Schreier
sequence. If the cohomology of the structure sheaf of `S` vanishes in all degrees above `n`,
then the étale cohomology of the constant sheaf `𝐙/p𝐙` vanishes in all degrees at least
`n + 2`.

This is the source's argument. In degree `q = q' + 1 ≥ n + 2` the long exact sequence of the
Artin–Schreier sequence puts `H ^ q (𝐙/p𝐙)` between `H ^ q' (𝐆_a)` and `H ^ q (𝐆_a)`, and both
of those vanish because `q'` and `q` exceed `n`. The hypothesis `hcomp` is the comparison of
[Stacks, Tag 03P2] in the shape used, transferring vanishing from the structure sheaf to
`𝐆_a`. -/
public theorem subsingleton_etaleH_constantZMod_of_hgroup_vanishing (p : ℕ) (S : Scheme.{u})
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (AS : ArtinSchreierSequence p S)
    (hcomp : ∀ i : ℕ,
      IsZero (Hgroup S.ringCatSheaf ⊤ i (SheafOfModules.unit S.ringCatSheaf)) →
        Subsingleton (Sheaf.H.{w, u + 1} AS.Ga i))
    (n : ℕ)
    (hvan : ∀ i : ℕ, n < i →
      IsZero (Hgroup S.ringCatSheaf ⊤ i (SheafOfModules.unit S.ringCatSheaf)))
    (q : ℕ) (hq : n + 2 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (etaleConstantZMod S p) q) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  exact subsingleton_sheafH_X₁_of_shortExact AS.shortExact q' (q' + 1) rfl
    (hcomp q' (hvan q' (by omega))) (hcomp (q' + 1) (hvan (q' + 1) (by omega)))

/-- **Vanishing above the dimension plus one, with the Artin–Schreier sequence carried.** Let `p`
be a prime and let `S` be a quasi-compact and quasi-separated scheme of characteristic `p` and of
dimension at most `d`, with an Artin–Schreier sequence `AS` and the comparison `hcomp`. Then
`H ^ q (S_étale, 𝐙/p𝐙) = 0` for every `q ≥ d + 2`.

This is the special case, with `AS` and `hcomp` as hypotheses, of [Stacks, Tag 0A3K] (2), which is
`subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le_constantSequence` and
`subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le_unconditional`.

The underlying space of `S` is a spectral space by [Stacks, Tag 094L], so the cohomology of any
abelian sheaf on it vanishes above its dimension by [Stacks, Tag 0A3G]; applied to the structure
sheaf and transported to derived global sections of module sheaves, that makes the Artin–Schreier
degree shift apply with `n = d`. Note that `q = d + 1` is not covered, and in particular `q = 1`
is not covered for any `d`. -/
public theorem subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le (p : ℕ) [Fact p.Prime]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology (S : Type u)) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (AS : ArtinSchreierSequence p S)
    (hcomp : ∀ i : ℕ,
      IsZero (Hgroup S.ringCatSheaf ⊤ i (SheafOfModules.unit S.ringCatSheaf)) →
        Subsingleton (Sheaf.H.{w, u + 1} AS.Ga i))
    (d : ℕ) (hdim : topologicalKrullDim (S : Type u) ≤ (d : WithBot ℕ∞))
    (q : ℕ) (hq : d + 2 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (etaleConstantZMod S p) q) :=
  subsingleton_etaleH_constantZMod_of_hgroup_vanishing p S AS hcomp d
    (fun i hi => Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology
      (SheafOfModules.unit S.ringCatSheaf) i (by omega)
      (Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le d (S : Type u)
        inferInstance inferInstance
        ((SheafOfModules.toSheaf S.ringCatSheaf).obj (SheafOfModules.unit S.ringCatSheaf))
        i hdim hi))
    q hq

end Stacks.ArtinSchreier

end
