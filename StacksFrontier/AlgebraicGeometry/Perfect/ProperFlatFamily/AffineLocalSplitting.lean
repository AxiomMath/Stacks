module

public import StacksFrontier.Homology.Perfect.FibreCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# The affine-local splitting of a derived direct image off its degree-zero cohomology

Part (b) of [Stacks, Tag 0E62] asserts, for a proper flat morphism `f : X ⟶ S` of finite
presentation all of whose fibres satisfy `κ(s) = H⁰(X_s, 𝒪_{X_s})`, that locally on `S` there is a
decomposition `Rf_*𝒪_X = 𝒪_S ⊕ P` in `D(𝒪_S)` with `P` perfect of Tor amplitude in `[1, ∞)`.

This file proves the **affine-local algebraic form** of that decomposition. The source's proof has
four steps, of which the first is geometric and the rest are commutative algebra:

1. by cohomology and base change ([Stacks, Tag 0B91]) the object `E = Rf_*𝒪_X` of `D(𝒪_S)` is
   perfect and its formation commutes with arbitrary base change, whence `E` has Tor amplitude in
   `[0, ∞)`;
2. hence `H⁰(E) ⊗ κ(s) → H⁰(E ⊗^L κ(s))` is surjective, because `H⁰(E ⊗^L κ(s))` is
   `H⁰(X_s, 𝒪_{X_s}) = κ(s)` and the unit `𝒪_S → E` already hits it;
3. [Stacks, Tag 0A1U] then splits `E = H⁰(E) ⊕ τ_{≥1}E` after shrinking `S` to an affine open
   neighbourhood of `s`, with `τ_{≥1}E` perfect of Tor amplitude in `[1, ∞)`;
4. `H⁰(E)` is flat, being a summand of something of Tor amplitude in `[0, ∞)`, and perfect, hence
   finite locally free by [Stacks, Tag 0658] and [Stacks, Tag 00NX]; finally the unit
   `𝒪_S → H⁰(E)` is an isomorphism because it is one after tensoring with every residue field
   ([Stacks, Tag 00O0]).

Steps 3 and 4's first half are what is carried here, in the ring-theoretic vocabulary in which
this library has [Stacks, Tag 0A1U] and [Stacks, Tag 0A1V] — namely for an object `K` of `D(R)`,
`R` a commutative ring, standing for `E` restricted to an affine open of `S`. Step 1 is not
performed: nothing here identifies `K` with a derived direct image, and the inputs the source
reads off [Stacks, Tag 0B91] appear only through the hypotheses they give about `K`. Step 4's
second half — the identification of `H⁰(E)` with `𝒪_S`, which is part (a) of the tag and is what
turns the first summand into `𝒪_S` — is not performed either.

## Main results

* `StacksDraft.Perfect.UnitSplitting.cohomologyBaseChangeSurjective_of_fibreCohomologyVanishes`:
  if the derived fibre of `K` at `p` has no cohomology in degree `i`, then the degree-`i`
  base-change map is surjective, its target being zero.
* `StacksDraft.Perfect.UnitSplitting.exists_localization_iso_single_homology_biprod_truncGE`:
  **the affine-local algebraic form of part (b) of [Stacks, Tag 0E62]**. For `K` pseudo-coherent
  in `D(R)` with no cohomology below degree zero, with derived fibre at `p` having no cohomology
  in degree `-1`, and with surjective degree-zero base-change map at `p`, there is `g ∉ p` with
  `K ⊗_R R_g ≅ H⁰(K)_g[0] ⊕ τ_{≥1}(K ⊗_R R_g)` in `D(R_g)`, where `H⁰(K)_g` is finite free over
  `R_g` and `τ_{≥1}(K ⊗_R R_g)` is perfect of Tor amplitude in `[1, ∞)`.

## Implementation notes

**Where the hypotheses come from.** The source's standing assumptions enter only through the
conclusions of step 1 and step 2, and those are what is assumed of `K`:

* `hneg`, the vanishing of `Hⁱ(K)` for `i < 0`, and `hfib`, the vanishing of `H^{-1}` of the
  derived fibre of `K` at `p`, are the two consequences of "`E` has Tor amplitude in `[0, ∞)`"
  that the source's steps 3 and 4 use. They are stated as the two separate vanishing statements
  rather than as Tor amplitude itself, because `StacksDraft.TorAmplitude.HasTorAmplitude` carries
  the derived tensor product, its comparison and its universal property as explicit parameters,
  and nothing weaker than those two vanishings is needed below.
* `hbase` is the surjectivity of step 2, in the spelling
  `StacksDraft.Perfect.CohomologyBaseChangeSurjective` that [Stacks, Tag 0A1U] consumes.
* pseudo-coherence `hK` is the part of perfectness of `E` that [Stacks, Tag 0A1U] asks for.

**What the degree `-1` hypothesis buys.** [Stacks, Tag 0A1V], the form of the splitting criterion
that exhibits the degree-`i` cohomology module as a summand in its own right, needs surjectivity
of the base-change map in the two adjacent degrees `i` and `i - 1`. In degree `-1` the target is
zero, so surjectivity is free; that implication is
`cohomologyBaseChangeSurjective_of_fibreCohomologyVanishes`. Running the criterion at `i = 0`
then produces the three-term decomposition
`K_g ≅ τ_{≤-1}K_g ⊕ H⁰(K)_g[0] ⊕ τ_{≥1}K_g`, and `hneg` collapses the first summand: it places
`K_g` in degrees `≥ 0`, so `τ_{≤-1}K_g` vanishes.

**The first summand is `H⁰(K)_g`, not `R_g`.** Finite freeness of `H⁰(K)_g` comes from
[Stacks, Tag 0A1V] and is the conclusion of the source's step 4 that this file reaches. The
remaining half of step 4, that the unit `R → H⁰(K)` is an isomorphism, is not carried: it needs
the map `H⁰(ε) : R → H⁰(K)` induced by a unit `ε : R[0] ⟶ K` — which this file does not take as
data — and then the transport of the fibrewise bijectivity of that map from the primes of `R` to
the primes of `R_g`, so that the isomorphism locus of [Stacks, Tag 00O0] (3), carried here as
`Stacks.FiniteProjective.MapLocus.isOpen_isoLocus_and_localized`, can be read at the prime of
`R_g` above `p`. Neither is written.

**Why the statement is algebraic.** [Stacks, Tag 0A1U] and [Stacks, Tag 0A1V] are carried in this
library only over a commutative ring, as results about `D(R)`, and not for the derived category of
modules on a scheme. Passing from `D(𝒪_S)` on an affine open `U = Spec R ⊆ S` to `D(R)` would
need the affine-local comparison of the two derived categories, and the geometric statement would
in addition need the identification of `H⁰(E ⊗^L κ(s))` with `H⁰(X_s, 𝒪_{X_s})`.

## References

* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
* [Stacks Project, Tag 0A1U](https://stacks.math.columbia.edu/tag/0A1U)
* [Stacks Project, Tag 0A1V](https://stacks.math.columbia.edu/tag/0A1V)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [Stacks Project, Tag 00O0](https://stacks.math.columbia.edu/tag/00O0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect.UnitSplitting

universe u v

/-- A biproduct whose first summand is a zero object is its second summand, via the projection. -/
private def biprodIsoSndOfIsZeroFst {C : Type*} [Category C] [Preadditive C] {X Y : C}
    [HasBinaryBiproduct X Y] (hX : IsZero X) : X ⊞ Y ≅ Y where
  hom := biprod.snd
  inv := biprod.inr
  hom_inv_id := biprod.hom_ext' _ _ (hX.eq_of_src _ _) (by simp)
  inv_hom_id := biprod.inr_snd

/-- If the derived fibre of `K` at `p` has no cohomology in degree `i`, then the degree-`i`
base-change map `Hⁱ(K) ⊗_R κ(p) → Hⁱ(K ⊗_R^L κ(p))` is surjective: its target is zero.

This is how the hypothesis `H^{-1}(E ⊗^L κ(s)) = 0` of the proof of [Stacks, Tag 0E62] feeds the
degree `i - 1` input of [Stacks, Tag 0A1V]. -/
theorem cohomologyBaseChangeSurjective_of_fibreCohomologyVanishes
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (i : ℤ)
    (h : FibreCohomologyVanishes.{u, v} p K i) :
    CohomologyBaseChangeSurjective.{u, v} p K i := by
  obtain ⟨P, hP, hQ, hzero⟩ := h
  exact ⟨P, hP, hQ, fun _ =>
    ⟨0, map_zero _, @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.mp hzero) _ _⟩⟩

/-! ### The affine-local form of part (b) of Stacks 0E62 -/

/-- **The affine-local algebraic form of part (b) of [Stacks, Tag 0E62].**

Let `R` be a commutative ring, `p ⊂ R` a prime, and `K` a pseudo-coherent object of `D(R)` --
standing for `E = Rf_*𝒪_X` restricted to an affine open of `S`. Assume

* `Hⁱ(K) = 0` for `i < 0` and `H^{-1}(K ⊗_R^L κ(p)) = 0`, and
* `H⁰(K) ⊗_R κ(p) → H⁰(K ⊗_R^L κ(p))` is surjective.

Then there is `g ∈ R`, `g ∉ p`, such that over `R_g` the localization `K_g = K ⊗_R R_g` splits as

`K_g ≅ H⁰(K)_g[0] ⊕ τ_{≥1}K_g`,

where `H⁰(K)_g` is a finite free `R_g`-module and `τ_{≥1}K_g` is a perfect object of `D(R_g)` of
Tor amplitude in `[1, ∞)`, recorded by a bounded complex of finite projective `R_g`-modules
concentrated in degrees `≥ 1` representing it whose termwise tensor products have no cohomology
below degree `1`. -/
@[stacks 0E62 "PART (b) ONLY, and only in its AFFINE-LOCAL ALGEBRAIC FORM: the statement is \
about an abstract pseudo-coherent object K of D(R) for a commutative ring R, standing for E = \
Rf_*O_X restricted to an affine open of S, and NOTHING HERE IDENTIFIES K WITH A DERIVED DIRECT \
IMAGE. The source's proof has four steps and the first, geometric one is NOT performed: \
cohomology and base change (Tag 0B91), which gives that E is perfect and that its formation \
commutes with arbitrary base change, is not invoked at all. What is assumed of K instead is \
exactly what the source's remaining three steps use of E: pseudo-coherence (the part of \
perfectness Tag 0A1U asks for); the vanishing of H^i(K) for i < 0 and of H^{-1}(K tensor^L \
k(p)), which are the two consequences of `E has tor amplitude in [0, infinity)` that the source \
uses, taken as two separate vanishing statements because \
StacksDraft.TorAmplitude.HasTorAmplitude carries the derived tensor product, its comparison and \
its universal property as explicit parameters and nothing stronger is needed; and surjectivity \
of H^0(K) tensor k(p) --> H^0(K tensor^L k(p)) at p, which is the source's second step. \
WITHIN part (b), THE FIRST SUMMAND IS NOT IDENTIFIED WITH O_S. What is delivered is the \
splitting K_g = H^0(K)_g[0] (+) tau_{>=1}K_g after localizing away from a single element g \
outside p, with tau_{>=1}K_g perfect of tor amplitude in [1, infinity) -- the source's step 3, \
Tag 0A1U -- and with H^0(K)_g FINITE FREE over R_g, which is the half of the source's step 4 \
that Tags 0658 and 00NX supply. The remaining half of step 4, that the unit O_S --> H^0(E) is \
an isomorphism, is NOT carried, and that is also exactly PART (a) of this tag, `f_*O_X = O_S \
and this holds after any base change`, WHICH IS NOT DELIVERED ANYWHERE in this file: carrying \
it needs the map H^0(epsilon) : R --> H^0(K) induced by a unit epsilon : R[0] --> K, which this \
statement does not take as data, and then the transport of the fibrewise bijectivity of that \
map from the primes of R to the primes of R_g so that the isomorphism locus of Algebra Tag 00O0 \
(3) can be read at the prime of R_g above p; that locus result IS carried in this library, as \
Stacks.FiniteProjective.MapLocus.isOpen_isoLocus_and_localized, but neither the induced map nor \
the transport is written here. The statement is algebraic rather than geometric because Tags \
0A1U and 0A1V are carried in this library only over a commutative ring, as StacksDraft.Perfect \
results about D(R) in StacksFrontier/Homology/Perfect/FibreCriterion.lean -- no declaration \
anywhere in the library carries either tag for the derived category of modules on a scheme -- so \
the geometric statement would need in addition the affine-local comparison of D(O_S)|_U with \
D(R) for U = Spec R an affine open, and the identification of H^0(E tensor^L k(s)) with H^0(X_s, \
O_{X_s}), which the module documentation of \
StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatFibreEulerCharacteristic.lean records as absent \
from this library. What is PROVED here, assuming nothing beyond the stated hypotheses on K: \
that the degree -1 \
base-change map is surjective because its target vanishes, so that Tag 0A1V applies at degree \
0; that the vanishing of H^i(K) below degree 0 places the localization K_g in degrees >= 0 and \
so kills the summand tau_{<=-1}K_g of the three-term decomposition of Tag 0A1V; and the \
assembly of the remaining two summands into the two-term splitting the source states"]
theorem exists_localization_iso_single_homology_biprod_truncGE
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hneg : ∀ i : ℤ, i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K))
    (hfib : FibreCohomologyVanishes.{u, v} p K (-1))
    (hbase : CohomologyBaseChangeSurjective.{u, v} p K 0) :
    ∃ g : R, g ∉ p ∧
      let Rg := Localization.Away g
      let Kg := (PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K
      let upper := (DerivedCategory.TStructure.t.truncGE 1).obj Kg
      let H0g := (ModuleCat.extendScalars (algebraMap R Rg)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj K)
      Module.Finite Rg H0g ∧ Module.Free Rg H0g ∧ IsPerfect upper ∧
        (∃ (P : CochainComplex (ModuleCat.{max u v} Rg) ℤ) (b : ℤ),
          P.IsStrictlyGE 1 ∧ P.IsStrictlyLE b ∧
            (∀ j : ℤ, Module.Finite Rg (P.X j)) ∧
            (∀ j : ℤ, Module.Projective Rg (P.X j)) ∧
            Nonempty (upper ≅ DerivedCategory.Q.obj P) ∧
            ∀ (M : ModuleCat.{max u v} Rg) (j : ℤ), j < 1 →
              IsZero ((TorAmplitude.tensorComplex P M).homology j)) ∧
        Nonempty (Kg ≅
          (DerivedCategory.singleFunctor (ModuleCat.{max u v} Rg) 0).obj H0g ⊞ upper) := by
  have hprev : CohomologyBaseChangeSurjective.{u, v} p K ((0 : ℤ) - 1) := by
    rw [zero_sub]
    exact cohomologyBaseChangeSurjective_of_fibreCohomologyVanishes.{u, v} p K (-1) hfib
  obtain ⟨g, hg, hmain⟩ :=
    exists_localization_finite_free_homology_and_iso_biprod.{u, v} p K hK 0 hbase hprev
  refine ⟨g, hg, ?_⟩
  dsimp only at hmain ⊢
  simp only [zero_add] at hmain
  obtain ⟨hperf, hamp, hfin, hfree, e, -, -⟩ := hmain
  have hge : DerivedCategory.IsGE
      ((PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K) 0 := by
    rw [DerivedCategory.isGE_iff]
    exact fun i hi => PseudoCoherence.localizationAway_homology_isZero.{u, v} g K i (hneg i hi)
  have hlow : IsZero ((DerivedCategory.TStructure.t.truncLE (-1)).obj
      ((PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K)) :=
    DerivedCategory.TStructure.t.isZero_truncLE_obj_of_isGE (-1) 0 (by norm_num) _
  exact ⟨hfin, hfree, hperf, hamp,
    ⟨e ≪≫ biprod.mapIso (biprodIsoSndOfIsZeroFst hlow) (Iso.refl _)⟩⟩

end StacksDraft.Perfect.UnitSplitting

end
