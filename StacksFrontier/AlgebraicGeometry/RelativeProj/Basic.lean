module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.MY

/-!
# Quasi-coherent graded algebras over a base scheme

Situation 01NN of the Stacks project fixes a scheme `S` together with a quasi-coherent graded
`𝒪_S`-algebra `𝒜`, and the relative homogeneous spectrum
`Proj_S(𝒜) ⟶ S` is built by glueing the absolute `Proj Γ(U, 𝒜)` over the affine opens `U` of `S`.
This file sets up the algebra side of that construction: the data of such an algebra, and the
consequence of quasi-coherence that makes the glueing possible, namely that the morphism of
projective spectra induced by a restriction map is defined *everywhere*.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra`: a quasi-coherent, nonnegatively graded
  commutative `𝒪_S`-algebra, recorded by its rings of sections over the affine opens of `S`.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.algebra`: the algebra structure that a
  restriction map puts on the sections over a smaller affine open.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProj.exists_mem_graded_mul_pow`: if `ψ : 𝒜 →+*ᵍ ℬ` exhibits
  `B` as a localization of `A` away from an element `g` of degree `0`, then every homogeneous
  element of `B` of degree `n` becomes, after multiplication by a power of `ψ g`, the image of a
  homogeneous element of `A` of the *same* degree `n`.
* `Stacks.AlgebraicGeometry.RelativeProj.mapDomain_eq_top_of_isLocalizationAway`: such a `ψ` is
  everywhere defined, i.e. `U(ψ) = Proj ℬ`. This is the algebraic heart of Tag 01NO.
* `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra.mapDomain_res_eq_top`: the restriction map
  of a quasi-coherent graded algebra along a basic open inclusion of affine opens is everywhere
  defined.

## Implementation notes

The index type is `Scheme.AffineZariskiSite`, i.e. the affine opens of `S`. Its *order* is not
used as the index of the restriction maps: `Scheme.AffineZariskiSite`'s `≤` relates `U` to `V`
only when `U` is a *basic* open of `V`, whereas Situation 01NN restricts along an arbitrary
inclusion of affine opens, and the dependent tags (01NO, 01NP) quantify over arbitrary nested
affine opens. The field `GradedAlgebra.res` is therefore indexed by an inclusion
`U.toOpens ≤ V.toOpens` of the underlying opens, which is strictly more general; the basic-open
inclusions are recovered through `Scheme.AffineZariskiSite.toOpens_mono`, which is what feeds
Mathlib's relative glueing machinery.

Quasi-coherence is recorded in the form it is used in, and in the form Mathlib states it for
algebras over a scheme (`AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData` and
`coequifibered_iff_forall_isLocalizationAway`): the sections over a basic open `D(f) ⊆ U` are
the localization of the sections over `U` away from the image of `f`. Only this inclusion-wise
form is assumed, never a sheaf axiom, because the glueing needs nothing else.

The rings of sections are objects of `CommRingCat.{u}` rather than bare types carrying a
`CommRing` instance. This is not cosmetic: it is what lets `grading U : ℕ → AddSubgroup (ring U)`
be written as a structure field at all, since `CommRingCat`'s coercion to types supplies the
`CommRing`, hence `AddGroup`, instance that `AddSubgroup` needs. Spelling the carrier as a type
plus a `commRing` field forces a `letI` into the type of every later field and of every
consumer.

The `Algebra` structure induced by a restriction map depends on the inclusion, which is an
explicit argument, so it cannot be an instance; `GradedAlgebra.algebra` is an `abbrev` so that
`letI := 𝒜.algebra h` unifies with the occurrence inside the `isLocalization` field.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)

## Not done here

The *geometric* content of Tag 01NO — that the square of projective spectra over a nested pair
of affine opens is cartesian, and that the comparison maps on the twists `𝒪(n)` are isomorphisms
— is not proved, so the charts are not glued. The charts themselves, their structure morphisms
and the commuting squares are in `StacksFrontier.AlgebraicGeometry.RelativeProj.Local`;
functoriality of the transitions is in
`StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjShared

namespace Stacks.AlgebraicGeometry.RelativeProj

universe u w w'

/-- A quasi-coherent, commutative, nonnegatively graded `𝒪_S`-algebra, recorded by its graded
rings of sections over the affine opens of `S`.

This is the data of Situation 01NN. The grading is by `ℕ`, matching the Stacks project's
convention that a graded ring has no negative part, and matching Mathlib's `Proj`. Quasi-coherence
is the field `isLocalization`: the sections over a basic open `D(f) ⊆ U` form the localization of
the sections over `U` away from the image of `f`. -/
public structure GradedAlgebra (S : Scheme.{u}) where
  /-- The ring of sections of the algebra over an affine open of the base. -/
  ring : S.AffineZariskiSite → CommRingCat.{u}
  /-- The grading of the ring of sections over an affine open. -/
  grading (U : S.AffineZariskiSite) : ℕ → AddSubgroup (ring U)
  /-- The grading makes the sections over an affine open a graded ring. -/
  gradedRing (U : S.AffineZariskiSite) : GradedRing (grading U)
  /-- The structure morphism from the sections of `𝒪_S` over an affine open. -/
  str (U : S.AffineZariskiSite) : Γ(S, U.toOpens) ⟶ ring U
  /-- The structure morphism lands in degree `0`. -/
  str_mem (U : S.AffineZariskiSite) (r : Γ(S, U.toOpens)) : str U r ∈ grading U 0
  /-- Restriction of sections along an inclusion of affine opens, as a graded ring map. -/
  res {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens) : grading V →+*ᵍ grading U
  /-- Restriction along the identity is the identity. -/
  res_id (U : S.AffineZariskiSite) : res (le_refl U.toOpens) = GradedRingHom.id (grading U)
  /-- Restriction is functorial. -/
  res_comp {U V W : S.AffineZariskiSite} (hUV : U.toOpens ≤ V.toOpens)
      (hVW : V.toOpens ≤ W.toOpens) :
    res (hUV.trans hVW) = (res hUV).comp (res hVW)
  /-- Restriction is compatible with the structure morphism. -/
  res_str {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens) (r : Γ(S, V.toOpens)) :
    res h (str V r) = str U (S.presheaf.map (homOfLE h).op r)
  /-- **Quasi-coherence.** The sections over a basic open `D(f) ⊆ U` are the localization of the
  sections over `U` away from the image of `f` under the structure morphism. -/
  isLocalization (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    letI : Algebra (ring U) (ring (U.basicOpen f)) :=
      (res (S.basicOpen_le f)).toRingHom.toAlgebra
    IsLocalization.Away (str U f) (ring (U.basicOpen f))

namespace GradedAlgebra

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S)

/-- The grading of the sections over an affine open, as an instance. -/
public instance instGradedRing (U : S.AffineZariskiSite) : GradedRing (𝒜.grading U) :=
  𝒜.gradedRing U

/-- The algebra structure that restriction along an inclusion of affine opens puts on the
sections over the smaller one. An `abbrev` so that it is interchangeable with the occurrence
inside the `isLocalization` field of `GradedAlgebra`. -/
public abbrev algebra {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens) :
    Algebra (𝒜.ring V) (𝒜.ring U) :=
  (𝒜.res h).toRingHom.toAlgebra

/-- The algebra map of `𝒜.algebra h` is the restriction map `𝒜.res h`. -/
public theorem algebraMap_eq {U V : S.AffineZariskiSite} (h : U.toOpens ≤ V.toOpens) :
    letI := 𝒜.algebra h
    (algebraMap (𝒜.ring V) (𝒜.ring U) : 𝒜.ring V →+* 𝒜.ring U) = (𝒜.res h).toRingHom :=
  rfl

end GradedAlgebra

section Away

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- If `ψ : 𝒜 →+*ᵍ ℬ` exhibits `B` as a localization of `A` away from `g`, then `ψ g` is a unit.
-/
public theorem isUnit_of_isLocalizationAway (ψ : 𝒜 →+*ᵍ ℬ) (g : A) [Algebra A B]
    (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B] :
    IsUnit (ψ g) := by
  have := IsLocalization.map_units (M := Submonoid.powers g) B ⟨g, Submonoid.mem_powers g⟩
  rwa [show (algebraMap A B) g = ψ g from RingHom.congr_fun halg g] at this

/-- **The key consequence of quasi-coherence.** If `ψ : 𝒜 →+*ᵍ ℬ` exhibits `B` as a localization
of `A` away from an element `g` of degree `0`, then every homogeneous element `b` of `B` of
degree `n` satisfies `ψ a = b * ψ g ^ k` for some `k` and some homogeneous `a` of `A` of the
*same* degree `n`.

Localization only provides `b * ψ g ^ k = ψ a'` for an *unspecified* `a' : A`. The degree is
recovered by projecting `a'` to its degree-`n` part: `ψ g ^ k` has degree `0`, so `b * ψ g ^ k`
has degree `n`, so the projection is lost on the right-hand side. This degree bookkeeping is
exactly what Tag 01NO needs and what makes `mapDomain_eq_top_of_isLocalizationAway` work. -/
public theorem exists_mem_graded_mul_pow (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0) [Algebra A B]
    (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B] {n : ℕ} {b : B}
    (hb : b ∈ ℬ n) : ∃ (a : A) (k : ℕ), a ∈ 𝒜 n ∧ ψ a = b * ψ g ^ k := by
  obtain ⟨⟨a', m⟩, hm⟩ := IsLocalization.surj (M := Submonoid.powers g) b
  obtain ⟨k, hk⟩ := m.2
  have hmap : ∀ x : A, (algebraMap A B) x = ψ x := RingHom.congr_fun halg
  have hgk : b * ψ g ^ k = ψ a' := by
    rw [← map_pow, ← hmap, ← hmap]
    simpa [hk] using hm
  have hdeg : b * ψ g ^ k ∈ ℬ n := by
    have h0 : ψ g ^ k ∈ ℬ (k • 0) := SetLike.pow_mem_graded k (ψ.map_mem hg)
    rw [smul_zero] at h0
    simpa using SetLike.mul_mem_graded hb h0
  refine ⟨GradedRing.proj 𝒜 n a', k, ?_, ?_⟩
  · rw [GradedRing.proj_apply]; exact SetLike.coe_mem _
  · rw [GradedRing.proj_apply, ψ.map_directSumDecompose, ← hgk,
      DirectSum.decompose_of_mem_same ℬ hdeg]

/-- **Tag 01NO, the algebraic half.** A graded ring map exhibiting `B` as a localization of `A`
away from an element of degree `0` induces a morphism `Proj ℬ ⟶ Proj 𝒜` defined on *all* of
`Proj ℬ`.

The statement is about `Stacks.AlgebraicGeometry.ProjShared.mapDomain`, the exact domain of
definition of the induced morphism. Mathlib's hypothesis for `AlgebraicGeometry.Proj.map`, namely
`ℬ₊ ≤ 𝒜₊.map ψ`, does hold here, but proving it directly means producing, for a homogeneous
`b : B` of positive degree, a representation of `b` in the ideal generated by the images of the
positive-degree homogeneous elements of `A`, which is `exists_mem_graded_mul_pow` plus an
inversion of `ψ g`; working with `mapDomain` instead keeps the argument pointwise. -/
public theorem mapDomain_eq_top_of_isLocalizationAway (ψ : 𝒜 →+*ᵍ ℬ) {g : A} (hg : g ∈ 𝒜 0)
    [Algebra A B] (halg : (algebraMap A B : A →+* B) = ψ.toRingHom) [IsLocalization.Away g B] :
    mapDomain 𝒜 ℬ ψ = ⊤ := by
  have hu : IsUnit (ψ g) := isUnit_of_isLocalizationAway 𝒜 ℬ ψ g halg
  refine top_le_iff.mp fun y _ => (mem_mapDomain_iff 𝒜 ℬ ψ y).mpr ?_
  obtain ⟨m, b, hm, hb, hby⟩ := exists_homogeneous_pos_notMem ℬ y
  obtain ⟨a, k, ha, hak⟩ := exists_mem_graded_mul_pow 𝒜 ℬ ψ hg halg hb
  refine ⟨m, a, hm, ha, ?_⟩
  rw [hak]
  intro hmem
  exact hby (((Ideal.unit_mul_mem_iff_mem _ (hu.pow k)).mp (by rwa [mul_comm] at hmem)))

end Away

namespace GradedAlgebra

variable {S : Scheme.{u}} (𝒜 : GradedAlgebra S)

/-- **Tag 01NO for a basic open inclusion.** The morphism of projective spectra induced by the
restriction map of a quasi-coherent graded algebra along a basic open inclusion `D(f) ⊆ U` of
affine opens is defined on all of `Proj (𝒜.grading (U.basicOpen f))`.

Basic open inclusions are exactly the morphisms of `Scheme.AffineZariskiSite`, so this is what
Mathlib's relative glueing machinery asks for. -/
public theorem mapDomain_res_eq_top (U : S.AffineZariskiSite) (f : Γ(S, U.toOpens)) :
    mapDomain (𝒜.grading U) (𝒜.grading (U.basicOpen f))
      (𝒜.res (S.basicOpen_le f)) = ⊤ := by
  let := 𝒜.algebra (U := U.basicOpen f) (V := U) (S.basicOpen_le f)
  have := 𝒜.isLocalization U f
  exact mapDomain_eq_top_of_isLocalizationAway _ _ _ (𝒜.str_mem U f)
    (𝒜.algebraMap_eq (U := U.basicOpen f) (V := U) (S.basicOpen_le f))

end GradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProj

end
