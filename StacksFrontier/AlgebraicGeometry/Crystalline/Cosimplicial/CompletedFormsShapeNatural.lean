module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedFormsShapeLinear
public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap

/-!
# The comparison of the two shapes of the completed forms is natural in the base ring

`Crystalline.completedFormsShapeEquiv` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShape.lean` identifies the
two shapes of the completed forms in positive exterior degree,

`AdicCompletion_B (⋀ⁱ_B N) ≃ AdicCompletion_{B̂} (⋀ⁱ_{B̂} N̂)`,

and `Crystalline.completedFormsShapeEquiv_smul` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShapeLinear.lean` makes it
`B̂`-linear.  Those two modules record one thing still missing: **naturality in `B`**.  Without it
the comparison is not a morphism of cosimplicial modules over
`Crystalline.CosimplicialEnvelope.ring`, so the null homotopy of
[Stacks, Lemma 60.19.1, Tag 07LA] does not transport along it and the `hcolumns` hypothesis of
`...SmallSite.computes07LG_of_doubleComplex` cannot be discharged.  **This module proves it**, as
`Crystalline.completedFormsShapeEquiv_natural`.

## What naturality says

A ring map `σ : B → B'` carrying `I` into `I'`, together with a `σ`-semilinear map of the
differentials, induces a map on each of the two shapes — on the left the completion of the
exterior power of the uncompleted differentials, on the right the completion of the exterior
power of the completed ones — and the claim is that the square of those two maps and the two
comparisons commutes.  Both vertical maps are `Crystalline.adicCompletionMapₛₗ`, which is the
only shape in which the transition maps `D(m) → D(n)` of the cosimplicial envelope act on a
completion.

## How the maps are presented, and why

The two exterior-power maps are carried as **variables with defining equations** rather than as
constructions: `Φ` is any `σ`-semilinear map of the uncompleted exterior powers which sends
`ω₁ ∧ ⋯ ∧ ωᵢ` to `ψ ω₁ ∧ ⋯ ∧ ψ ωᵢ`, and `Φc` any `σc`-semilinear map of the completed ones which
sends the wedge of the images of the `ωⱼ` in `N̂` to the wedge of the images of the `ψ ωⱼ` in
`N̂'`.  Instantiated directly at the envelopes the nested `AdicCompletion`s unfold during
unification and nothing elaborates within the heartbeat limit; the same reason makes
`Crystalline.quotSmulTop_exteriorPower_squareₛₗ` below state the level step for an **abstract**
pair of level comparisons `e`, `e'` into abstract level modules, with
`Crystalline.completedFormsShapeLevelEquiv` substituted only once, in a single `exact`.

`ψ` is only a function `N → N'`, not a semilinear map: nothing below uses more than its values
on the `ωⱼ`.

The variables are not a restriction on what the result applies to.
`Crystalline.completedFormsShapeEquiv_natural_powMapₛₗ` substitutes for both of them, with
`ExteriorAlgebra.powMapₛₗ` — the semilinear exterior power of a semilinear map, whose
`ExteriorAlgebra.powMapₛₗ_ιMulti` is the wedge equation verbatim.  That is the shape the library
builds these maps in: `Crystalline.mapDifferentialFormsOfDPMorphism` is `powMapₛₗ` of the map
of the uncompleted differentials, and `Crystalline.envelopeFormsMap` is its completion.

## Why the hypotheses are the ones carried

Beyond the `I.FG` and `0 < i` the comparison itself carries, and `hmap : I.map σ ≤ I'`, which is
part of the data of either vertical map:

* `hσc`, that `σc` is the completion of `σ` — `σc (algebraMap B B̂ b) = algebraMap B' B̂' (σ b)`.
  This **delimits** the statement rather than restricting it: `σc` is a variable, and without
  `hσc` the square below is not the naturality square of `σ` at all, since nothing would relate
  the ring map the right-hand vertical map is semilinear over to `σ`.  It is also **not**
  implied by the other hypotheses, and it is where the proof's one real step happens.
  `hΦc` pins `Φc` down only on the wedges of elements of the image of `N` in `N̂`, and those span
  a proper `B̂`-submodule of `⋀ⁱ_{B̂} N̂` in general — a lemma
  pinning a map on a dense image does not determine it — so neither `Φc` nor the `σc` it is
  semilinear over is determined, and the two composites around the square are semilinear over
  `σc ∘ algebraMap` and `algebraMap ∘ σ` respectively.  `hσc` is exactly the identification of
  those two, and the `smul` step of the span induction is where it is used.
* No hypothesis is carried about `I B̂` mapping into `I' B̂'`:
  `Crystalline.map_map_adicCompletion_le` derives it from `hmap` and `hσc`.

## Why the levels, and not the completions

The comparison is assembled from its levels, and a level of the source is a quotient of the
exterior power of the **uncompleted** `N`, where the classes of wedges span.  So at a level the
square is determined by its value on those classes, which is the computation
`Crystalline.completedFormsShapeLevelEquiv_mk_ιMulti` already supplies on both sides.  Working
on the completions directly would not do: an additive map out of a completion is **not**
determined by its values on the image of the uncompleted module, which is why
`Crystalline.completedFormsShapeEquiv_of_ιMulti` alone cannot prove naturality.

## Main results

* `Crystalline.quotSmulTop_exteriorPower_squareₛₗ` — **a square of level maps commutes as soon
  as it commutes on the classes of wedges**, for abstract level comparisons.
* `Crystalline.map_map_adicCompletion_le` — the completion of `σ` carries `I B̂` into `I' B̂'`.
* `Crystalline.completedFormsShapeLevelEquiv_natural` — the level `k` square commutes.
* `Crystalline.completedFormsShapeEquiv_natural` — **the comparison of the two shapes of the
  completed forms is natural in the base ring.**
* `Crystalline.completedFormsShapeEquiv_natural_of_completedMap` — the same with `Φc` pinned on
  every wedge of `N̂` through a completed map `ψc` of the differentials, which is the form in
  which a caller has it.
* `Crystalline.completedFormsShapeLinearEquiv_natural` — naturality of the `B̂`-linear
  comparison.
* `Crystalline.algebraMap_adicCompletion_eq_of` — the structure map of a completion over its
  base is `AdicCompletion.of`, which is the one bridge between the spelling `Ideal.map` is
  written in and the spelling the library's lemmas on induced maps are written in.
* `Crystalline.completedFormsShapeEquiv_natural_powMapₛₗ` — **naturality for the two
  exterior-power maps the library builds**, `ExteriorAlgebra.powMapₛₗ` of a semilinear map of
  the differentials and of a completed one.  Nothing is a variable here but the data: a
  semilinear `ψ` of the differentials, its completion `ψc`, and the completion `σc` of the ring
  map, each with the defining equation the library already proves of it.

## What is and is not proved

Everything stated is proved, under no hypothesis beyond `I.FG`, `0 < i`, and the defining
equations of the maps appearing in the square.  **No tag attribute is placed**: this is one
identification inside the proof of [Stacks, Proposition 60.21.3, Tag 07LG] and is not a clause
of any tag's statement.

[Stacks, Tag 07LA] is **not** transported along the comparison here, and the `hcolumns`
hypothesis of `...SmallSite.computes07LG_of_doubleComplex` is **not** discharged.  That
hypothesis is stated about the double complex `K` which that theorem also carries as a variable,
so no instance of it is provable while `K` is free; discharging it needs the `K` of
`Crystalline.CosimplicialCompletedPair.doubleComplex`, hence the per-degree connection on `M(•)`
which the module documentation of `Crystalline/Computes07LGFromDoubleComplex.lean` records as
missing.  What this module removes is the *other* obstruction named there: the comparison is now
known to be natural.

## References

* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

namespace Crystalline

/-! ### Two values of the induced maps on levels -/

section Pieces

variable {R S : Type*} [CommRing R] [CommRing S] {P Q : Type*}
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module S Q]
  {σ : R →+* S} {I : Ideal R} {J : Ideal S}

/-- The map induced on the levels by a semilinear map sends the class of `x` to the class of
`g x`. -/
@[simp]
public theorem adicQuotientMap_mk (g : P →ₛₗ[σ] Q) (h : I.map σ ≤ J) (n : ℕ) (x : P) :
    adicQuotientMap g h n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x) := rfl

/-- The completion of a semilinear map, read at a level, is the map induced on that level. -/
@[simp]
public theorem adicCompletionMapₛₗ_val (g : P →ₛₗ[σ] Q) (h : I.map σ ≤ J)
    (x : AdicCompletion I P) (n : ℕ) :
    (adicCompletionMapₛₗ g h x).val n = adicQuotientMap g h n (x.val n) := rfl

end Pieces

/-! ### A square of level maps is determined on the classes of wedges -/

section Square

variable {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R' S']
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R' N']
  {Q : Type*} [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
  {Q' : Type*} [AddCommGroup Q'] [Module R' Q'] [Module S' Q'] [IsScalarTower R' S' Q']
  {σ : R →+* R'} {τ : S →+* S'}

/-- **A square of level maps commutes as soon as it commutes on the classes of wedges.**

The source is a reduction of an exterior power of `N`, and the classes of the wedges
`ω₁ ∧ ⋯ ∧ ωᵢ` span it (`exteriorPower.ιMulti_span`), so the two composites — `G` after the
comparison `e`, and the comparison `e'` after `F` — agree everywhere as soon as they agree
there, by induction over that span.  The `smul` step is the one with content: the two composites
carry the action of `r : R` to the action of `algebraMap R' S' (σ r)` and of `τ (algebraMap R S r)`
respectively, and `hτ` is exactly the identification of those two scalars.

The level comparisons `e` and `e'` and their targets are abstract on purpose.  Substituted for
by `Crystalline.completedFormsShapeLevelEquiv`, whose target is a reduction of an exterior power
of a completion over a completed ring, the induction above does not elaborate within the
heartbeat limit; stated here it costs nothing and is substituted into once. -/
public theorem quotSmulTop_exteriorPower_squareₛₗ {K : Ideal R} {K' : Ideal R'} {i : ℕ}
    (e : (↥(⋀[R]^i N) ⧸ (K • (⊤ : Submodule R ↥(⋀[R]^i N)))) ≃ₗ[R] Q)
    (e' : (↥(⋀[R']^i N') ⧸ (K' • (⊤ : Submodule R' ↥(⋀[R']^i N')))) ≃ₗ[R'] Q')
    (F : (↥(⋀[R]^i N) ⧸ (K • (⊤ : Submodule R ↥(⋀[R]^i N)))) →ₛₗ[σ]
      (↥(⋀[R']^i N') ⧸ (K' • (⊤ : Submodule R' ↥(⋀[R']^i N')))))
    (G : Q →ₛₗ[τ] Q')
    (hτ : ∀ r : R, τ (algebraMap R S r) = algebraMap R' S' (σ r))
    (hwedge : ∀ v : Fin i → N, G (e (Submodule.Quotient.mk (exteriorPower.ιMulti R i v))) =
      e' (F (Submodule.Quotient.mk (exteriorPower.ιMulti R i v))))
    (z : ↥(⋀[R]^i N) ⧸ (K • (⊤ : Submodule R ↥(⋀[R]^i N)))) : G (e z) = e' (F z) := by
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R i (M := N))) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨v, rfl⟩ := hy; exact hwedge v
    | zero => simp
    | add a b _ _ ha hb =>
      rw [Submodule.Quotient.mk_add, map_add, map_add, map_add, map_add, ha, hb]
    | smul r a _ ha =>
      rw [Submodule.Quotient.mk_smul, e.map_smul, ← IsScalarTower.algebraMap_smul S r,
        G.map_smulₛₗ, hτ, F.map_smulₛₗ, e'.map_smul, ha, IsScalarTower.algebraMap_smul]

end Square

/-! ### The comparison is natural in the base ring -/

section Naturality

variable {R R' : Type*} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R' N']
  {σ : R →+* R'} {σc : AdicCompletion I R →+* AdicCompletion I' R'}

/-- **The completion of a ring map carrying `I` into `I'` carries `I B̂` into `I' B̂'`.**  This is
why no hypothesis about the completed ideals is carried below: an ideal mapped twice is generated
by the images of the generators, and `hσc` computes each of those. -/
public theorem map_map_adicCompletion_le (hmap : I.map σ ≤ I')
    (hσc : ∀ r : R, σc (algebraMap R (AdicCompletion I R) r) =
      algebraMap R' (AdicCompletion I' R') (σ r)) :
    (I.map (algebraMap R (AdicCompletion I R))).map σc ≤
      I'.map (algebraMap R' (AdicCompletion I' R')) := by
  rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  intro r hr
  simp only [Ideal.mem_comap, hσc]
  exact Ideal.mem_map_of_mem _ (hmap (Ideal.mem_map_of_mem σ hr))

variable {i : ℕ} {ψ : N → N'}
  {Φ : ↥(⋀[R]^i N) →ₛₗ[σ] ↥(⋀[R']^i N')}
  {Φc : ↥(⋀[AdicCompletion I R]^i (AdicCompletion I N)) →ₛₗ[σc]
    ↥(⋀[AdicCompletion I' R']^i (AdicCompletion I' N'))}

/-- **The level `k` comparison of the two shapes is natural in the base ring.**

Both composites send the class of `ω₁ ∧ ⋯ ∧ ωᵢ` to the class, formed over `B̂'`, of the wedge of
the images of the `ψ ωⱼ` in `N̂'` — on one route `Φc` is applied to the wedge of the images of
the `ωⱼ`, on the other `Φ` is applied first and the comparison second — and those classes span
the source, so `Crystalline.quotSmulTop_exteriorPower_squareₛₗ` concludes. -/
public theorem completedFormsShapeLevelEquiv_natural (hI : I.FG) (hI' : I'.FG) (hi : 0 < i)
    (k : ℕ) (hmap : I.map σ ≤ I')
    (hσc : ∀ r : R, σc (algebraMap R (AdicCompletion I R) r) =
      algebraMap R' (AdicCompletion I' R') (σ r))
    (hΦ : ∀ v : Fin i → N, Φ (exteriorPower.ιMulti R i v) =
      exteriorPower.ιMulti R' i fun j => ψ (v j))
    (hΦc : ∀ v : Fin i → N, Φc (exteriorPower.ιMulti (AdicCompletion I R) i
          fun j => AdicCompletion.of I N (v j)) =
      exteriorPower.ιMulti (AdicCompletion I' R') i
        fun j => AdicCompletion.of I' N' (ψ (v j)))
    (z : ↥(⋀[R]^i N) ⧸ (I ^ k • (⊤ : Submodule R ↥(⋀[R]^i N)))) :
    adicQuotientMap Φc (map_map_adicCompletion_le hmap hσc) k
        (completedFormsShapeLevelEquiv hI i k hi z) =
      completedFormsShapeLevelEquiv hI' i k hi (adicQuotientMap Φ hmap k z) :=
  quotSmulTop_exteriorPower_squareₛₗ (completedFormsShapeLevelEquiv hI i k hi)
    (completedFormsShapeLevelEquiv hI' i k hi) (adicQuotientMap Φ hmap k)
    (adicQuotientMap Φc (map_map_adicCompletion_le hmap hσc) k) hσc
    (fun v => by
      rw [completedFormsShapeLevelEquiv_mk_ιMulti, adicQuotientMap_mk, hΦc,
        adicQuotientMap_mk, hΦ, completedFormsShapeLevelEquiv_mk_ιMulti]) z

/-- **The comparison of the two shapes of the completed forms is natural in the base ring**: for
a ring map `σ : B → B'` carrying `I` into `I'`, its completion `σc`, and semilinear maps `Φ`,
`Φc` of the two shapes of the forms induced by one map `ψ` of the differentials, the square

`AdicCompletion_B (⋀ⁱ_B N) → AdicCompletion_{B'} (⋀ⁱ_{B'} N')`,
`AdicCompletion_{B̂} (⋀ⁱ_{B̂} N̂) → AdicCompletion_{B̂'} (⋀ⁱ_{B̂'} N̂')`

commutes, both vertical maps being `Crystalline.adicCompletionMapₛₗ`.

This is `Crystalline.completedFormsShapeLevelEquiv_natural` read level by level: the comparison
is by construction the level comparisons assembled, and so is each vertical map. -/
public theorem completedFormsShapeEquiv_natural (hI : I.FG) (hI' : I'.FG) (hi : 0 < i)
    (hmap : I.map σ ≤ I')
    (hσc : ∀ r : R, σc (algebraMap R (AdicCompletion I R) r) =
      algebraMap R' (AdicCompletion I' R') (σ r))
    (hΦ : ∀ v : Fin i → N, Φ (exteriorPower.ιMulti R i v) =
      exteriorPower.ιMulti R' i fun j => ψ (v j))
    (hΦc : ∀ v : Fin i → N, Φc (exteriorPower.ιMulti (AdicCompletion I R) i
          fun j => AdicCompletion.of I N (v j)) =
      exteriorPower.ιMulti (AdicCompletion I' R') i
        fun j => AdicCompletion.of I' N' (ψ (v j)))
    (x : AdicCompletion I ↥(⋀[R]^i N)) :
    adicCompletionMapₛₗ Φc (map_map_adicCompletion_le hmap hσc)
        (completedFormsShapeEquiv hI i hi x) =
      completedFormsShapeEquiv hI' i hi (adicCompletionMapₛₗ Φ hmap x) := by
  refine AdicCompletion.ext fun k => ?_
  rw [adicCompletionMapₛₗ_val, completedFormsShapeEquiv_val, completedFormsShapeEquiv_val,
    adicCompletionMapₛₗ_val]
  exact completedFormsShapeLevelEquiv_natural hI hI' hi k hmap hσc hΦ hΦc (x.val k)

/-- **Naturality, with the completed forms map presented through a completed map of the
differentials.**  This is the form a caller has it in: `Φc` is pinned on every wedge of `N̂`
through a map `ψc : N̂ → N̂'`, and `ψc` is the completion of `ψ`.  Those two equations give the
one hypothesis of `Crystalline.completedFormsShapeEquiv_natural`, which asks only for the wedges
of the images of `N`. -/
public theorem completedFormsShapeEquiv_natural_of_completedMap (hI : I.FG) (hI' : I'.FG)
    (hi : 0 < i) (hmap : I.map σ ≤ I')
    (hσc : ∀ r : R, σc (algebraMap R (AdicCompletion I R) r) =
      algebraMap R' (AdicCompletion I' R') (σ r))
    (hΦ : ∀ v : Fin i → N, Φ (exteriorPower.ιMulti R i v) =
      exteriorPower.ιMulti R' i fun j => ψ (v j))
    (ψc : AdicCompletion I N → AdicCompletion I' N')
    (hψc : ∀ x : N, ψc (AdicCompletion.of I N x) = AdicCompletion.of I' N' (ψ x))
    (hΦc : ∀ w : Fin i → AdicCompletion I N,
      Φc (exteriorPower.ιMulti (AdicCompletion I R) i w) =
        exteriorPower.ιMulti (AdicCompletion I' R') i fun j => ψc (w j))
    (x : AdicCompletion I ↥(⋀[R]^i N)) :
    adicCompletionMapₛₗ Φc (map_map_adicCompletion_le hmap hσc)
        (completedFormsShapeEquiv hI i hi x) =
      completedFormsShapeEquiv hI' i hi (adicCompletionMapₛₗ Φ hmap x) :=
  completedFormsShapeEquiv_natural hI hI' hi hmap hσc hΦ
    (fun v => by rw [hΦc]; simp only [hψc]) x

/-- **The `B̂`-linear comparison of the two shapes is natural in the base ring.**  It has the
same underlying function as `Crystalline.completedFormsShapeEquiv`, so this is
`Crystalline.completedFormsShapeEquiv_natural`. -/
public theorem completedFormsShapeLinearEquiv_natural (hI : I.FG) (hI' : I'.FG) (hi : 0 < i)
    (hmap : I.map σ ≤ I')
    (hσc : ∀ r : R, σc (algebraMap R (AdicCompletion I R) r) =
      algebraMap R' (AdicCompletion I' R') (σ r))
    (hΦ : ∀ v : Fin i → N, Φ (exteriorPower.ιMulti R i v) =
      exteriorPower.ιMulti R' i fun j => ψ (v j))
    (hΦc : ∀ v : Fin i → N, Φc (exteriorPower.ιMulti (AdicCompletion I R) i
          fun j => AdicCompletion.of I N (v j)) =
      exteriorPower.ιMulti (AdicCompletion I' R') i
        fun j => AdicCompletion.of I' N' (ψ (v j)))
    (x : AdicCompletion I ↥(⋀[R]^i N)) :
    adicCompletionMapₛₗ Φc (map_map_adicCompletion_le hmap hσc)
        (completedFormsShapeLinearEquiv hI i hi x) =
      completedFormsShapeLinearEquiv hI' i hi (adicCompletionMapₛₗ Φ hmap x) :=
  completedFormsShapeEquiv_natural hI hI' hi hmap hσc hΦ hΦc x

end Naturality

/-! ### Naturality for the exterior-power maps the library actually builds -/

section PowMap

variable {R R' : Type*} [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R' N']
  {σ : R →+* R'} {σc : AdicCompletion I R →+* AdicCompletion I' R'}

/-- The structure map of a completion as an algebra over its base is the canonical map `of`.
This is the one bridge between the two spellings: `Ideal.map` of the adic ideal is written with
`algebraMap` throughout
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShape.lean`, while the
library's lemmas about induced maps of completions — `Crystalline.adicCompletionRingMap_of`,
`Crystalline.completedRingHom_of`, `Crystalline.completionDifferentialsMapₛₗ_of` — are written
with `AdicCompletion.of`. -/
public theorem algebraMap_adicCompletion_eq_of (r : R) :
    algebraMap R (AdicCompletion I R) r = AdicCompletion.of I R r := rfl

/-- **Naturality in the base ring, for the two exterior-power maps the library builds.**

`ExteriorAlgebra.powMapₛₗ` is the semilinear exterior power of a semilinear map, and
`ExteriorAlgebra.powMapₛₗ_ιMulti` is exactly the wedge equation
`Crystalline.completedFormsShapeEquiv_natural` asks of its `Φ` and `Φc`.  So the square commutes
for the maps a caller has: on the left `Crystalline.mapDifferentialFormsOfDPMorphism`, which is
`ExteriorAlgebra.powMapₛₗ` of the map of the uncompleted differentials and whose completion is
the transition map `Crystalline.envelopeFormsMap` of the uncompleted shape; and on the right
`ExteriorAlgebra.powMapₛₗ` of a completed map of the differentials, for instance
`Crystalline.completedEnvelopeDifferentialsMap` or the general
`Crystalline.completionDifferentialsMapₛₗ`.

The two scalar hypotheses are in the `AdicCompletion.of` spelling the library's own lemmas use:
`hσc` is `Crystalline.adicCompletionRingMap_of`, and `hψc` is
`Crystalline.completionDifferentialsMapₛₗ_of`. -/
public theorem completedFormsShapeEquiv_natural_powMapₛₗ (hI : I.FG) (hI' : I'.FG) {i : ℕ}
    (hi : 0 < i) (hmap : I.map σ ≤ I') (ψ : N →ₛₗ[σ] N')
    (ψc : AdicCompletion I N →ₛₗ[σc] AdicCompletion I' N')
    (hσc : ∀ r : R, σc (AdicCompletion.of I R r) = AdicCompletion.of I' R' (σ r))
    (hψc : ∀ y : N, ψc (AdicCompletion.of I N y) = AdicCompletion.of I' N' (ψ y))
    (x : AdicCompletion I ↥(⋀[R]^i N)) :
    adicCompletionMapₛₗ (ExteriorAlgebra.powMapₛₗ i σc ψc)
          (map_map_adicCompletion_le hmap hσc)
        (completedFormsShapeEquiv hI i hi x) =
      completedFormsShapeEquiv hI' i hi
        (adicCompletionMapₛₗ (ExteriorAlgebra.powMapₛₗ i σ ψ) hmap x) :=
  completedFormsShapeEquiv_natural_of_completedMap hI hI' hi hmap hσc
    (ExteriorAlgebra.powMapₛₗ_ιMulti i σ ψ) ψc hψc
    (ExteriorAlgebra.powMapₛₗ_ιMulti i σc ψc) x

end PowMap

end Crystalline

end
