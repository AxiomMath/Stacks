module

public import StacksFrontier.Deformation.BaseCategory.AugmentedPowQuotient

/-!
# Lifting `R` through a morphism onto `R ⧸ 𝔭 ^ n` splits that morphism

Let `ε : R →ₐ[Λ] k` be a surjective augmentation of a Noetherian `Λ`-algebra, let `𝔭 = Ker ε`
and `n ≠ 0`, and let `f : C ⟶ R ⧸ 𝔭 ^ n` be a morphism of `𝒞_Λ` whose source satisfies
`𝔪_C ^ n = 0`. If the quotient map `R → R ⧸ 𝔭 ^ n` lifts through `f` to a `Λ`-algebra map
`σ : R →ₐ[Λ] C`, then `f` has a section in `𝒞_Λ`, and so is not an essential surjection.

This is the last step of the implication `(1) ⇒ (2)` of [Stacks, Tag 07YM] in degree `-1`. There
`f` is the small extension `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` of
`Deformation.ArtinianLocalAlgCat.isSmallExtension_powQuotientMap`, which
[Stacks, Tag 06H0] makes an essential surjection; versality of `x` at the closed point
supplies the lift `σ`, and the resulting section is the contradiction. The source phrases the
step as "since the maximal ideal of `B'` has `n`th power equal to zero, this `q` factors
through `B`, which contradicts the fact that `B' → B` is an essential surjection".

## Main results

* `Deformation.ArtinianLocalAlgCat.map_ker_augmentation_le_maximalIdeal` — a lift of the
  quotient map carries `𝔭` into `𝔪_C`.
* `Deformation.ArtinianLocalAlgCat.exists_section_of_lift_powQuotient` — the section of `f`
  in `𝒞_Λ`.
* `Deformation.ArtinianLocalAlgCat.not_isEssentialSurjection_of_lift_powQuotient` — hence `f`
  is not an essential surjection, provided it is a small extension.

## Implementation notes

The hypothesis on `σ` is that `f ∘ σ` is the quotient map, written out pointwise; this is what
the geometric input of [Stacks, Tag 07YM] delivers, and it is strictly weaker than asking `σ`
to be local — locality of `σ` is *derived*, in the form
`Deformation.ArtinianLocalAlgCat.map_ker_augmentation_le_maximalIdeal`, from the fact that a
ring homomorphism carries units to units: if `σ a` were a unit for some `a ∈ 𝔭` then `a` would
be a unit in `R ⧸ 𝔭 ^ n`, which it is not.

The factorization of `σ` through `R ⧸ 𝔭 ^ n` is `IsLocalRing.exists_isLocalHom_comp_mk_pow`,
which supplies the ring homomorphism and its locality. What remains is the two further pieces
of data that a morphism of `𝒞_Λ` carries: compatibility with the `Λ`-algebra structures, which
holds because `σ` is one and the quotient map is, and compatibility with the identifications of
the residue fields, which is read off the same compatibility for `f` — both are checked on
representatives, the quotient map being surjective.

## References

* [Stacks Project, Tag 06H0](https://stacks.math.columbia.edu/tag/06H0)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u v w

namespace Deformation.ArtinianLocalAlgCat

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {R : Type v} [CommRing R] [Algebra Λ R] [IsNoetherianRing R]
variable (ε : R →ₐ[Λ] k) (hε : Function.Surjective ε) (n : ℕ) [NeZero n]
  (C : ArtinianLocalAlgCat.{u, v, w} Λ k) (f : C ⟶ powQuotientObj ε hε n)
  (σ : R →ₐ[Λ] (C : Type v))
  (hσ : ∀ a : R, f.hom (σ a) =
    Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n) a)

include hσ in
/-- A lift of the quotient map `R → R ⧸ 𝔭 ^ n` through a morphism of `𝒞_Λ` carries `𝔭` into
the maximal ideal: were `σ a` a unit for some `a ∈ 𝔭`, its image `a mod 𝔭 ^ n` would be a unit
of `R ⧸ 𝔭 ^ n`, which it is not. -/
public theorem map_ker_augmentation_le_maximalIdeal :
    (RingHom.ker ε.toRingHom).map σ.toRingHom ≤ maximalIdeal (C : Type v) := by
  have := isMaximal_ker_augmentation ε hε
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap]
  by_contra hcon
  have hu : IsUnit (Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n) a) := by
    rw [← hσ a]
    exact (notMem_maximalIdeal.mp hcon).map f.hom
  refine notMem_maximalIdeal.mpr hu ?_
  rw [IsLocalRing.maximalIdeal_quotient_pow (RingHom.ker ε.toRingHom) n]
  exact Ideal.mem_map_of_mem _ ha

include hσ in
/-- **The section of [Stacks, Tag 07YM].** If the quotient map `R → R ⧸ 𝔭 ^ n` lifts through a
morphism `f : C ⟶ R ⧸ 𝔭 ^ n` of `𝒞_Λ` whose source has `𝔪_C ^ n = 0`, then `f` has a section
in `𝒞_Λ`.

The lift factors through `R ⧸ 𝔭 ^ n` by `IsLocalRing.exists_isLocalHom_comp_mk_pow`, and the
factorization is a morphism of `𝒞_Λ`: it is a `Λ`-algebra map because `σ` is, it is local by
that lemma, and it respects the identifications of the residue fields because `f` does. -/
@[stacks 07YM "the lift factors through A/𝔭 ^ n, giving a section of the small extension"]
public theorem exists_section_of_lift_powQuotient
    (hn : maximalIdeal (C : Type v) ^ n = ⊥) :
    ∃ s : powQuotientObj ε hε n ⟶ C, s ≫ f = 𝟙 (powQuotientObj ε hε n) := by
  have := isMaximal_ker_augmentation ε hε
  obtain ⟨F, hFloc, hFcomp⟩ := IsLocalRing.exists_isLocalHom_comp_mk_pow σ.toRingHom
    (RingHom.ker ε.toRingHom) (map_ker_augmentation_le_maximalIdeal ε hε n C f σ hσ) hn
  have hFmk : ∀ a : R, F (Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n) a) = σ a := fun a =>
    RingHom.congr_fun hFcomp a
  have hcomm : ∀ r : Λ,
      F (algebraMap Λ (R ⧸ RingHom.ker ε.toRingHom ^ n) r) = algebraMap Λ (C : Type v) r :=
    fun r => by
      rw [show algebraMap Λ (R ⧸ RingHom.ker ε.toRingHom ^ n) r =
        Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n) (algebraMap Λ R r) from rfl, hFmk,
        σ.commutes]
  refine ⟨{ hom := { F with commutes' := hcomm }, isLocal := hFloc, residue_comm := ?_ }, ?_⟩
  · refine Ideal.Quotient.mk_surjective.forall.mpr fun x => ?_
    change C.residueEquiv (residue (C : Type v) (F _)) = _
    rw [hFmk x, ← f.residue_comm (σ x), hσ x]
  · refine Hom.ext (AlgHom.ext (Ideal.Quotient.mk_surjective.forall.mpr fun x => ?_))
    change f.hom (F _) = _
    rw [hFmk x, hσ x]
    rfl

include hσ in
/-- **The contradiction of [Stacks, Tag 07YM].** A small extension `f : C ⟶ R ⧸ 𝔭 ^ n` of
`𝒞_Λ` whose source has `𝔪_C ^ n = 0` and through which the quotient map `R → R ⧸ 𝔭 ^ n` lifts
is not an essential surjection: the lift produces a section
(`Deformation.ArtinianLocalAlgCat.exists_section_of_lift_powQuotient`), and a small extension
with a section is not essential (`Deformation.not_isEssentialSurjection_iff_exists_section`). -/
@[stacks 07YM "a lift of A through A'/(𝔭') ^ n contradicts essential surjectivity"]
public theorem not_isEssentialSurjection_of_lift_powQuotient
    (hn : maximalIdeal (C : Type v) ^ n = ⊥)
    (hf : InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom)) :
    ¬ IsEssentialSurjection f :=
  (not_isEssentialSurjection_iff_exists_section f hf).mpr
    (exists_section_of_lift_powQuotient ε hε n C f σ hσ hn)

end Deformation.ArtinianLocalAlgCat
