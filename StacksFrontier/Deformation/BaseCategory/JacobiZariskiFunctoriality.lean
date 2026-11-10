module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.CotangentSequence

/-!
# Functoriality of the Jacobi–Zariski sequence in the base category

Let `Λ → B → A` be algebra maps and let `k` be a common residue field, so that both `B → k`
and `A → k` are surjective. Each of `B` and `A` then presents `k` over `Λ`, with conormal
module `𝔪/𝔪²` for `𝔪` the kernel of the residue map, and the two Jacobi–Zariski sequences

    H₁(L_{k/Λ}) → 𝔪_B/𝔪_B² --d_B--> k ⊗_B Ω_{B/Λ} → Ω_{k/Λ} → 0
    H₁(L_{k/Λ}) → 𝔪_A/𝔪_A² --d_A--> k ⊗_A Ω_{A/Λ} → Ω_{k/Λ} → 0

are related by vertical maps: the identity on `H₁(L_{k/Λ})`, the maps `𝔪_B/𝔪_B² → 𝔪_A/𝔪_A²`
and `k ⊗_B Ω_{B/Λ} → k ⊗_A Ω_{A/Λ}` induced by `B → A`, and the identity on `Ω_{k/Λ}`. The
three squares so formed commute.

## Main definitions

* `Deformation.residueExtension`: an algebra `A` over `Λ` with a surjection onto `k`, viewed
  as a presentation of `k` over `Λ`.
* `Deformation.residueExtensionHom`: the morphism of presentations induced by `B → A`.
* `Deformation.h1CotangentToConormal`: the arrow `H₁(L_{S/R}) → I/I²` that opens the
  Jacobi–Zariski sequence of a presentation of `S` over `R` with kernel `I`.

## Main results

* `Deformation.cotangentMap_comp_h1CotangentToConormal`: the left square, comparing the two
  arrows out of `H₁(L_{k/Λ})`.
* `Deformation.cotangentSpaceMap_comp_cotangentComplex`: the middle square, naturality of the
  differentials `d_B` and `d_A`.
* `Deformation.toKaehler_comp_cotangentSpaceMap`: the right square, comparing the two arrows
  into `Ω_{k/Λ}`.
* `Deformation.residueExtension_ker_eq_maximalIdeal`: for a local ring the kernel of the
  residue map is the maximal ideal, so the conormal module above really is `𝔪/𝔪²`.
* `Deformation.cotangentMap_residueExtensionHom_of`: the vertical map `𝔪_B/𝔪_B² → 𝔪_A/𝔪_A²`
  of the diagram is the map `Ideal.mapCotangent` induced by `𝔪_B → 𝔪_A`.
* `Deformation.mapCotangent_h1CotangentToCotangent`: the left square once more, this time for
  the arrow `H₁(L_{k/Λ}) → 𝔪/𝔪²` of the four-term sequence of [Stacks, Tag 06S7].
* `Deformation.h1Cotangent_map_comp_map`: for `Λ → B → A` with common residue field `k`, the
  functoriality maps of `H₁` compose, `H₁(L_{k/Λ}) → H₁(L_{k/B}) → H₁(L_{k/A})`.

## Implementation notes

The terms of the rows are read off a presentation `P` of `k` over `Λ` whose ring is `B`
respectively `A`: the conormal module is `Algebra.Extension.Cotangent P`, the differential
`d` is `Algebra.Extension.cotangentComplex P`, the cotangent space is
`Algebra.Extension.CotangentSpace P`, which is `k ⊗_{P.Ring} Ω_{P.Ring/Λ}` rather than the
`Ω_{P.Ring/Λ} ⊗_{P.Ring} k` of the source, and the last arrow of the row is
`Algebra.Extension.toKaehler P`. The first arrow is not part of that package and is built
here: it pushes a class of `H₁(L_{k/Λ})` forward along the canonical morphism from the
universal presentation `Λ[k] → k` and then includes `H₁` of the presentation into its
conormal module.

The source's first arrow has a second realization, `Deformation.h1CotangentToCotangent`, which
reads the connecting map of the Jacobi–Zariski sequence of `Λ → A → k` through the
identification `𝔪_A/𝔪_A² = H₁(L_{k/A})`; that is the arrow used in the four-term sequence of
[Stacks, Tag 06S7]. The left square is proved for both realizations, in
`cotangentMap_comp_h1CotangentToConormal` and in `mapCotangent_h1CotangentToCotangent`
respectively; the two realizations are not compared to each other.

The leftmost and rightmost columns of the diagram are equalities in the source. They are
equalities here too, in the strong sense that the two rows share the module `H₁(L_{k/Λ})` they
start from and the module `Ω_{k/Λ}` they end in; the two squares at those ends therefore
compare two maps with the same source, respectively the same target, and no comparison
isomorphism intervenes.

The hypotheses are on a tower of rings rather than on a morphism of an ambient category of
Artinian local algebras: every morphism of such a category supplies the data below, with the
kernel of the residue map equal to the maximal ideal.

## References

* [Stacks Project, Tag 06S8](https://stacks.math.columbia.edu/tag/06S8)
-/

@[expose] public section

universe u v v' w

namespace Deformation

/-- An algebra `A` over `Λ` together with a surjection onto `k`, viewed as a presentation of
`k` over `Λ`. Its kernel is the kernel of the residue map `A → k`, so its conormal module is
`𝔪_A/𝔪_A²` and its cotangent space is `k ⊗_A Ω_{A/Λ}`. -/
public noncomputable def residueExtension (Λ : Type u) {A : Type v} {k : Type w}
    [CommRing Λ] [CommRing A] [CommRing k] [Algebra Λ A] [Algebra A k] [Algebra Λ k]
    [IsScalarTower Λ A k] (h : Function.Surjective (algebraMap A k)) :
    Algebra.Extension.{v} Λ k where
  Ring := A
  σ := Function.surjInv h
  algebraMap_σ := Function.surjInv_eq h

/-- For a local ring `A` with a surjection onto a field `k`, the kernel of that surjection is
the maximal ideal of `A`; so the conormal module of `residueExtension` is `𝔪_A/𝔪_A²`. -/
public theorem residueExtension_ker_eq_maximalIdeal (Λ : Type u) {A : Type v} {k : Type w}
    [CommRing Λ] [CommRing A] [IsLocalRing A] [Field k] [Algebra Λ A] [Algebra A k]
    [Algebra Λ k] [IsScalarTower Λ A k] (h : Function.Surjective (algebraMap A k)) :
    (residueExtension Λ h).ker = IsLocalRing.maximalIdeal A := by
  change RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A
  exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (algebraMap A k) h)

/-- The arrow `H₁(L_{S/R}) → I/I²` that opens the Jacobi–Zariski sequence of a presentation
`P` of `S` over `R` with kernel `I`: push a class forward along the canonical morphism from
the universal presentation `R[S] → S` to `P`, then include `H₁` of `P` into `I/I²`. -/
public noncomputable def h1CotangentToConormal {R : Type u} {S : Type w} [CommRing R]
    [CommRing S] [Algebra R S] (P : Algebra.Extension.{v} R S) :
    Algebra.H1Cotangent R S →ₗ[S] P.Cotangent :=
  P.h1Cotangentι ∘ₗ Algebra.Extension.H1Cotangent.map (Algebra.Extension.defaultHom R S P)

section Ladder

variable {Λ : Type u} {B : Type v} {A : Type v'} {k : Type w}
  [CommRing Λ] [CommRing B] [CommRing A] [CommRing k]
  [Algebra Λ B] [Algebra Λ A] [Algebra Λ k] [Algebra B A] [Algebra B k] [Algebra A k]
  [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k]

variable (hB : Function.Surjective (algebraMap B k))
  (hA : Function.Surjective (algebraMap A k))

/-- The morphism of presentations of `k` over `Λ` induced by an algebra map `B → A` that is
compatible with the residue maps onto `k`. -/
public noncomputable def residueExtensionHom :
    (residueExtension Λ hB).Hom (residueExtension Λ hA) :=
  Algebra.Extension.Hom.ofAlgHom (IsScalarTower.toAlgHom Λ B A)
    (by ext b; exact (IsScalarTower.algebraMap_apply B A k b).symm)

/-- **Stacks 06S8**, left square. The two arrows out of `H₁(L_{k/Λ})` agree: pushing a class
into `𝔪_B/𝔪_B²` and then along `B → A` gives its image in `𝔪_A/𝔪_A²`.

The source leaves this horizontal arrow unlabelled. It is realized here as
`Deformation.h1CotangentToConormal`, the canonical map through the universal presentation of `k`
over `Λ`. The square for the other realization of that arrow, the one used in the four-term exact
sequence of [Stacks, Tag 06S7], is `Deformation.mapCotangent_h1CotangentToCotangent`; the two
realizations are not compared to each other, which is why the scope label names this one. -/
@[stacks 06S8 "left square, for the canonical map through the universal presentation"]
public theorem cotangentMap_comp_h1CotangentToConormal :
    Algebra.Extension.Cotangent.map (residueExtensionHom (Λ := Λ) hB hA) ∘ₗ
        h1CotangentToConormal (residueExtension Λ hB) =
      h1CotangentToConormal (residueExtension Λ hA) := by
  have key : ∀ y, Algebra.Extension.Cotangent.map (residueExtensionHom (Λ := Λ) hB hA)
      ((residueExtension Λ hB).h1Cotangentι y) =
      (residueExtension Λ hA).h1Cotangentι
        (Algebra.Extension.H1Cotangent.map (residueExtensionHom (Λ := Λ) hB hA) y) :=
    fun _ => rfl
  ext x
  rw [LinearMap.comp_apply, h1CotangentToConormal, h1CotangentToConormal,
    LinearMap.comp_apply, LinearMap.comp_apply, key,
    ← Algebra.Extension.H1Cotangent.map_comp_apply,
    Algebra.Extension.H1Cotangent.map_eq _
      (Algebra.Extension.defaultHom Λ k (residueExtension Λ hA))]

/-- **Stacks 06S8**, middle square. The differentials `d_B : 𝔪_B/𝔪_B² → k ⊗_B Ω_{B/Λ}` and
`d_A : 𝔪_A/𝔪_A² → k ⊗_A Ω_{A/Λ}` are compatible with the maps induced by `B → A`. -/
@[stacks 06S8 "middle square"]
public theorem cotangentSpaceMap_comp_cotangentComplex :
    Algebra.Extension.CotangentSpace.map (residueExtensionHom (Λ := Λ) hB hA) ∘ₗ
        (residueExtension Λ hB).cotangentComplex =
      (residueExtension Λ hA).cotangentComplex ∘ₗ
        Algebra.Extension.Cotangent.map (residueExtensionHom (Λ := Λ) hB hA) := by
  simpa using Algebra.Extension.CotangentSpace.map_comp_cotangentComplex
    (residueExtensionHom (Λ := Λ) hB hA)

/-- **Stacks 06S8**, right square. The two arrows into `Ω_{k/Λ}` agree: the projection of
`k ⊗_B Ω_{B/Λ}` onto `Ω_{k/Λ}` factors through `k ⊗_A Ω_{A/Λ}` along `B → A`. -/
@[stacks 06S8 "right square"]
public theorem toKaehler_comp_cotangentSpaceMap :
    (residueExtension Λ hA).toKaehler ∘ₗ
        Algebra.Extension.CotangentSpace.map (residueExtensionHom (Λ := Λ) hB hA) =
      (residueExtension Λ hB).toKaehler := by
  ext x
  simp

end Ladder

section ResidueField

variable {Λ : Type u} {B : Type v} {A : Type v'} {k : Type w}
  [CommRing Λ] [CommRing B] [CommRing A] [Field k]
  [Algebra Λ B] [Algebra Λ A] [Algebra Λ k] [Algebra B A] [Algebra B k] [Algebra A k]
  [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k]

/-- For a tower `Λ → B → A` of algebras with a common residue field `k`, the functoriality
maps of the first homology of the naive cotangent complex compose: the map
`H₁(L_{k/Λ}) → H₁(L_{k/A})` is the map `H₁(L_{k/Λ}) → H₁(L_{k/B})` followed by
`H₁(L_{k/B}) → H₁(L_{k/A})`. -/
public theorem h1Cotangent_map_comp_map :
    Algebra.H1Cotangent.map B A k k ∘ₗ Algebra.H1Cotangent.map Λ B k k =
      Algebra.H1Cotangent.map Λ A k k := by
  refine LinearMap.ext fun x => ?_
  have h := Algebra.Extension.H1Cotangent.map_eq
    (((Algebra.Generators.defaultHom (Algebra.Generators.self B k)
        (Algebra.Generators.self A k)).toExtensionHom).comp
      ((Algebra.Generators.defaultHom (Algebra.Generators.self Λ k)
        (Algebra.Generators.self B k)).toExtensionHom))
    ((Algebra.Generators.defaultHom (Algebra.Generators.self Λ k)
        (Algebra.Generators.self A k)).toExtensionHom)
  simpa only [LinearMap.comp_apply, Algebra.Extension.H1Cotangent.map_comp_apply,
    Algebra.H1Cotangent.map] using congrArg (fun F => F x) h

variable (hB : Function.Surjective (algebraMap B k))
  (hA : Function.Surjective (algebraMap A k))

/-- The middle vertical arrow `𝔪_B/𝔪_B² → 𝔪_A/𝔪_A²` of the diagram, read on the conormal
modules of the two presentations, is the map on conormal modules induced by the inclusion
`𝔪_B → 𝔪_A` of ideals along `B → A`. -/
public theorem cotangentMap_residueExtensionHom_of
    (z : (RingHom.ker (algebraMap B k)).Cotangent) :
    Algebra.Extension.Cotangent.map (residueExtensionHom (Λ := Λ) hB hA)
        (Algebra.Extension.Cotangent.of (P := residueExtension Λ hB) z) =
      Algebra.Extension.Cotangent.of (P := residueExtension Λ hA)
        (Ideal.mapCotangent (RingHom.ker (algebraMap B k)) (RingHom.ker (algebraMap A k))
          (Algebra.ofId B A)
          (ker_algebraMap_le_comap_ker (Λ := B) (S := k) (k := k) (A := A)) z) := by
  obtain ⟨y, rfl⟩ := (RingHom.ker (algebraMap B k)).toCotangent_surjective z
  apply Algebra.Extension.Cotangent.ext
  rfl

/-- Reading the arrow `H₁(L_{k/Λ}) → 𝔪/𝔪²` back through the identification `𝔪/𝔪² = H₁(L_{k/A})`
recovers the functoriality map `H₁(L_{k/Λ}) → H₁(L_{k/A})`. -/
private theorem conormalToH1Cotangent_h1CotangentToCotangent
    (h : Function.Surjective (algebraMap B k)) (x : Algebra.H1Cotangent Λ k) :
    conormalToH1Cotangent (Λ := B) (S := k) (k := k) h (h1CotangentToCotangent Λ h x) =
      Algebra.H1Cotangent.map Λ B k k x := by
  rw [h1CotangentToCotangent]
  exact (cotangentEquivH1Cotangent h).apply_symm_apply _

/-- **Stacks 06S8**, left square, for the arrow `H₁(L_{k/Λ}) → 𝔪/𝔪²` of the four-term exact
sequence of [Stacks, Tag 06S7]: pushing a class of `H₁(L_{k/Λ})` into `𝔪_B/𝔪_B²` and then
along `𝔪_B → 𝔪_A` gives its image in `𝔪_A/𝔪_A²`. -/
@[stacks 06S8 "left square, for the arrow of the four-term sequence of 06S7"]
public theorem mapCotangent_h1CotangentToCotangent (x : Algebra.H1Cotangent Λ k) :
    Ideal.mapCotangent (RingHom.ker (algebraMap B k)) (RingHom.ker (algebraMap A k))
        (Algebra.ofId B A)
        (ker_algebraMap_le_comap_ker (Λ := B) (S := k) (k := k) (A := A))
        (h1CotangentToCotangent Λ hB x) =
      h1CotangentToCotangent Λ hA x := by
  have key := conormalToH1Cotangent_comp (Λ := B) (S := k) (k := k) (A := A) hB hA
    (h1CotangentToCotangent Λ hB x)
  rw [conormalToH1Cotangent_h1CotangentToCotangent, ← LinearMap.comp_apply,
    h1Cotangent_map_comp_map] at key
  exact (cotangentEquivH1Cotangent hA).injective
    (key.symm.trans (conormalToH1Cotangent_h1CotangentToCotangent hA x).symm)

end ResidueField

end Deformation

end
