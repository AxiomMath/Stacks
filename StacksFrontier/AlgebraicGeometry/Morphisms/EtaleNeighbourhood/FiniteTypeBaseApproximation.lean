module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.BaseChangeApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkHelpers
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.StalkHomAtHelpers
public import StacksCore.Tactic.StacksAttribute

/-!
# Approximating a map out of the local ring of a base that does not lie over `S`

Tag 0CAW approximates a local `𝒪_{S, s}`-algebra map `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` for a `T` given
over `S`. Tag 0GDX is the variant in which `T` carries no morphism to `S` at all and is instead
of finite type over `Spec ℤ`, while `σ` is merely a local homomorphism. Among the clauses of its
conclusion are an elementary étale neighbourhood `(V, v)` of `(S, s)` and a morphism `τ : V ⟶ T`
with `τ(v) = t` — clauses (1) and (3) of the source.

Clauses (1) and (3) are proved here. The device is that `σ` and the completion map
`𝒪_{S, s} → 𝒪^∧_{S, s}` together give a morphism `Spec 𝒪^∧_{S, s} ⟶ T ×_Z S` for any `Z`
receiving both `T` and `S` and over which the two are compatible, hence a point `t'` of
`T ×_Z S` and a local homomorphism `σ' : 𝒪_{T ×_Z S, t'} → 𝒪^∧_{S, s}` which *is* an
`𝒪_{S, s}`-algebra map for the second projection. So the first stage of Tag 0CAW applies to
`T ×_Z S ⟶ S`, which is locally of finite type because `T ⟶ Z` is, and `τ` is obtained by
composing with the first projection. For `Z` terminal — the case `Z = Spec ℤ` of Tag 0GDX — the
compatibility over `Z` is automatic.

What comes out is slightly stronger than clauses (1) and (3): it carries in addition the
congruence which Tag 0CAW records as its clause (3), i.e. that the square relating `σ` to
`τ^♯_v` commutes modulo `𝔪_v ^ N`. The source of Tag 0GDX does not state that, but this
construction delivers it.

## Main results

* `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_baseApproximation_over`: the
  statement for an arbitrary auxiliary base `Z` receiving both `T` and `S`, with the
  compatibility of `σ` over `Z` as a hypothesis.
* `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_absoluteApproximation`:
  clauses (1) and (3) of Tag 0GDX, with the congruence of Tag 0CAW clause (3). The whole of Tag
  0GDX is proved in two other files, independently of one another:
  `StacksDraft.ArtinApproximation.exists_common_elementaryEtaleNeighborhood_absoluteApproximation`
  in `StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/RelativeMapApproximation.lean`,
  and
  `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_absoluteApproximation_full_section` in
  `StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/AbsoluteApproximationFull.lean`.

## Implementation notes

*Which hypotheses are carried.* None: Theorem 07QZ is proved as
`StacksDraft.ArtinApproximation.localApproximationProperty`, so Tag 0CAU behind Tag
0CAW's first stage is unconditional and so is everything here. The source's "finite type over
`Spec ℤ`" is weakened to "locally of finite type over `Spec ℤ`", which is all the construction
uses.

*Where clauses (2) and (4) of Tag 0GDX are.* They are proved, twice over and independently, and
both statements carry a registration for the whole conclusion:
`StacksDraft.ArtinApproximation.exists_common_elementaryEtaleNeighborhood_absoluteApproximation`
in `StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/RelativeMapApproximation.lean`,
and
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_absoluteApproximation_full_section` in
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AbsoluteApproximationFull`. What
neither of them carries is the congruence recorded here, which belongs to Tag 0CAW and not to Tag
0GDX; that is why the theorem below keeps its own registration for clauses (1) and (3).

The source gets those two clauses from Tag 0CAV applied over `Spec 𝒪^∧_{S, s}`, followed by a
descent of the resulting étale neighbourhood along a presentation of `Spec 𝒪^∧_{S, s}` as a limit
of schemes smooth over `S` (Popescu's Theorem 07GC), using the descent lemmas 01ZM and 07RP and the
étale slice 057G; that composite is what the other files assemble, the slice excepted. Its
ingredients are Popescu's theorem `Stacks.Smoothing.indSmooth_of_isRegularRingMap` (Tag 07GC)
together with the regularity of the completion map
`Stacks.GRing.isRegularRingHom_algebraMap_adicCompletion` (Tag 0AH2) and the bridge
`Stacks.Smoothing.isRegularRingMap_of_regularRingHom` between the two regularity predicates, which
exhibit `𝒪^∧_{S, s}` as a filtered colimit of smooth algebras; the presentation of
`Spec 𝒪^∧_{S, s}` itself as a cofiltered inverse limit of affine schemes smooth over an affine open
of `S`, `AlgebraicGeometry.exists_limitPresentation_spec_completedStalk_of_isAffineOpen`; the
descent of a finitely presented scheme and of a morphism between two such to a finite stage,
`AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_finitePresentation` and
`AlgebraicGeometry.exists_morphism_after_baseChange` (Tag 01ZM); and the descent of étaleness,
`AlgebraicGeometry.exists_etale_pullback_of_isLimit` (Tag 07RP). What this file proves on its own
is clauses (1) and (3), in a form carrying the congruence of Tag 0CAW clause (3).

The étale slice 057G is *not* among them, and need not be. The source cuts the smooth stage `W`
down to a closed subscheme `V ⊆ W` étale over `S`; but `W = E ×_{W} V` is formed by base change
and étaleness is stable under base change, so all the construction needs of `V` is a morphism
`V ⟶ W` over `S` through the right point with trivial residue field extension. The first
stage of Tag 0CAW supplies one, by Artin approximation, and supplies in addition the congruence
modulo `𝔪_v ^ N` — which the slice does not. That substitution is
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_over_stage`; the coupling of
the resulting `(V, v)` to `Y` and `y_σ`, namely the source's identification
`(Y_σ)_s = (Y ×_T V)_v` and the point `y_τ` it produces, is
`StacksDraft.ArtinApproximation.exists_point_and_closedFiberIso_over_stage`. Dropping the slice
costs one lemma: the source identifies the point of the fibre product by injectivity of a base
change of an immersion, and with `V ⟶ W` no longer an immersion that step is instead
`AlgebraicGeometry.Scheme.Pullback.point_eq_of_isIso_residueFieldMap`, the uniqueness
counterpart of `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`.

What those ingredients must be assembled into is the descent half of [Stacks Project, Tag 0CAW]:
from `σ` and `φ` alone, produce the pair `(V, v)` together with `τ : V ⟶ T` **coupled to**
`Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}` — Artin approximation over `Spec 𝒪^∧_{S, s}`, then a
factorisation of `𝒪_{T, t} → 𝒪^∧_{S, s}` through a smooth stage of the ind-smooth presentation,
then descent of the approximating neighbourhood to that stage, then the first stage of
Tag 0CAW over it, then base change along the resulting `V ⟶` that stage. The coupling is the
content: the first stage alone constrains only `(V, τ)`, with no reference to `X`, `Y` or `φ`.

One might expect the coupling to identify `Y_σ` at
`y_σ` with `Y ×_{T, τ} V` at `y_τ`, carrying `φ` over to an isomorphism of **completed** local
rings. That is false, and it is worth recording why, because the shape invites it. Clause (5) of
Tag 0CAW identifies only the `𝔪 ^ N`-truncations, never the completions, and no isomorphism of
completions exists in general: with `k` algebraically closed of characteristic `≠ 2`,
`S = Spec k[u]`, `T = Spec k[u, a]`, `σ : a ↦ u ^ 7`, `Y = Spec k[u, b]` and
`g : (u, b) ↦ (u, b ^ 2)`, the ring `𝒪^∧_{Y_σ, y_σ} = k[[u, b]] / (b ^ 2 - u ^ 7)` is a domain,
while at `N = 2` with `τ : a ↦ u ^ 2` — legitimate, since `u ^ 7 - u ^ 2 ∈ 𝔪_v ^ 2` — the ring
`𝒪^∧_{Y ×_{T, τ} V, y_τ} = k[[u, b]] / ((b - u) * (b + u))` is not. A cusp is not a node, and
there is not even a `k[[u]]`-algebra map between them. So the congruence proved here is not a
weaker substitute for an available identification; the identification does not exist.

Nor does the route need the unproved remainder of [Stacks Project, Tag 0CAY]. In the descent the
approximating neighbourhood over the smooth stage is pulled back along `V ⟶` that stage, and
étaleness is stable under base change, so it is enough that the neighbourhood over the stage is
étale. Running the approximation step with [Stacks Project, Tag 0CAV], that is
`exists_common_elementaryEtaleNeighborhood_of_adicCompletion_ringEquiv` in the namespace
`StacksDraft.ArtinApproximation`, rather than Tag 0CAU delivers that directly when `φ` is an
isomorphism, and `AlgebraicGeometry.exists_etale_pullback_of_isLimit` (Tag 07RP) carries it from
the limit to a stage. No comparison of associated graded rings and no conormal-algebra isomorphism
is involved.

*The shape of the two stalk computations.* Both uses of `σ'` — that it is an `𝒪_{S, s}`-algebra
map for the second projection, and that it restricts to `σ` along the first — are instances of
one lemma, `stalkClosedPointTo_comp_stalkHomAt`: for a morphism `m` out of the spectrum of a
local ring and a further morphism `k`, the local homomorphism attached to `m` precomposed with
the map of stalks of `k` is read off from the composite `m ≫ k`.

*Why the proofs are in term form.* The type of `AlgebraicGeometry.Scheme.stalkClosedPointTo f` is
indexed by `f (closedPoint R)`, and `↥(Spec R)` is `PrimeSpectrum ↑R` only after unfolding
`Spec`. Goals mentioning such a point are therefore not type-correct at the transparency level
at which `rw` abstracts its pattern, and `rw` reports the pattern as missing even where it is
plainly present. Mathlib handles this with a `backward.isDefEq` option; here the same steps are
taken with `congrArg`, `Eq.trans` and `change`, which elaborate at default transparency.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
* [Stacks Project, Tag 0CAU](https://stacks.math.columbia.edu/tag/0CAU)
* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- If `m ≫ k` is the morphism attached to a local homomorphism `f` out of `𝒪_{X, x}`, then `m`
sends the closed point to a point over `x`, and the local homomorphism attached to `m`
precomposed with the stalk map of `k` is `f`. -/
private theorem point_and_stalkClosedPointTo_comp_stalkHomAt {W X : Scheme.{u}}
    {R : CommRingCat.{u}} [IsLocalRing R] (m : Spec R ⟶ W) (k : W ⟶ X) {x : X}
    (f : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom]
    (hmk : m ≫ k = Spec.map f ≫ X.fromSpecStalk x) :
    ∃ hk : k (m (closedPoint R)) = x,
      (Scheme.stalkClosedPointTo m).hom.comp (k.stalkHomAt hk) = f.hom :=
  have hk : k (m (closedPoint R)) = x :=
    (congrArg (fun φ : Spec R ⟶ X => φ (closedPoint R)) hmk).trans
      (specMap_fromSpecStalk_closedPoint f)
  ⟨hk, stalkClosedPointTo_comp_stalkHomAt m k f hmk hk⟩

/-- **Tag 0GDX, clauses (1) and (3), over an arbitrary auxiliary base.** Let `S` be locally
Noetherian, let `zT : T ⟶ Z` be locally of finite type, let `zS : S ⟶ Z` be arbitrary, let
`t ∈ T` and `s ∈ S` with `𝒪_{S, s}` a G-ring, and let `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local
homomorphism whose associated morphism `Spec 𝒪^∧_{S, s} ⟶ T` agrees over `Z` with the one coming
from the completion map `𝒪_{S, s} → 𝒪^∧_{S, s}`. Then for every `N ≥ 1` there are an elementary
étale neighbourhood `(V, v)` of `(S, s)` and a morphism `τ : V ⟶ T` with `τ v = t` such that the
square
```
𝒪^∧_{S, s} ⟶ 𝒪^∧_{V, v}
    ↑σ             ↑
𝒪_{T, t}  —τ^♯—→ 𝒪_{V, v}
```
commutes modulo `𝔪_v ^ N`. -/
theorem exists_elementaryEtaleNeighborhood_baseApproximation_over
    {S T Z : Scheme.{u}} (zT : T ⟶ Z) (zS : S ⟶ Z)
    [IsLocallyNoetherian S] [LocallyOfFiniteType zT]
    (t : T) (s : S) (hG : IsGRing (S.presheaf.stalk s))
    (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (hcompat : (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) ≫ zT =
      (Spec.map (CommRingCat.ofHom
          (algebraMap (S.presheaf.stalk s)
            (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
        S.fromSpecStalk s) ≫ zS) :
    ∃ V : EtaleNeighborhood S s, V.IsElementary ∧
      ∃ (τ : V.scheme ⟶ T) (hτ : τ V.point = t),
        ∀ a : T.presheaf.stalk t,
          V.completionMap (σ a) -
              algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)) (τ.stalkHomAt hτ a) ∈
            Ideal.map
              (algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)))
              (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N) := by
  have hσhom : IsLocalHom (CommRingCat.ofHom σ).hom := hσ
  have haS : IsLocalHom (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))
  obtain ⟨m, hmc, hmb⟩ :
      ∃ m : Spec (completedStalkObj S s) ⟶ pullback zT zS,
        m ≫ pullback.fst zT zS = Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t ∧
          m ≫ pullback.snd zT zS =
            Spec.map (CommRingCat.ofHom
                (algebraMap (S.presheaf.stalk s)
                  (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
              S.fromSpecStalk s :=
    ⟨pullback.lift _ _ hcompat, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨hfst, hres⟩ := point_and_stalkClosedPointTo_comp_stalkHomAt m (pullback.fst zT zS)
    (CommRingCat.ofHom σ) hmc
  obtain ⟨hsnd, hbase⟩ := point_and_stalkClosedPointTo_comp_stalkHomAt m (pullback.snd zT zS)
    (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) hmb
  obtain ⟨V, hVel, τ', hτ', -, hcong⟩ :=
    exists_elementaryEtaleNeighborhood_baseApproximation (pullback.snd zT zS)
      (m (closedPoint (completedStalkObj S s))) s hsnd hG N hN (Scheme.stalkClosedPointTo m).hom
      (Scheme.isLocalHom_stalkClosedPointTo m) hbase
  have hτ : (τ' ≫ pullback.fst zT zS) V.point = t :=
    (congrArg (fun z => pullback.fst zT zS z) hτ').trans hfst
  refine ⟨V, hVel, τ' ≫ pullback.fst zT zS, hτ, fun a => ?_⟩
  have hmem := hcong ((pullback.fst zT zS).stalkHomAt hfst a)
  have e1 : V.completionMap (σ a) =
      V.completionMap ((Scheme.stalkClosedPointTo m).hom
        ((pullback.fst zT zS).stalkHomAt hfst a)) :=
    congrArg V.completionMap (RingHom.congr_fun hres a).symm
  have e2 : (τ' ≫ pullback.fst zT zS).stalkHomAt hτ a =
      (τ'.stalkHomAt hτ') ((pullback.fst zT zS).stalkHomAt hfst a) :=
    RingHom.congr_fun
      (Scheme.Hom.stalkHomAt_comp τ' (pullback.fst zT zS) hτ' hfst) a
  have e3 : V.completionMap (σ a) -
        algebraMap (V.scheme.presheaf.stalk V.point)
          (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
            (V.scheme.presheaf.stalk V.point))
          ((τ' ≫ pullback.fst zT zS).stalkHomAt hτ a) =
      V.completionMap ((Scheme.stalkClosedPointTo m).hom
          ((pullback.fst zT zS).stalkHomAt hfst a)) -
        algebraMap (V.scheme.presheaf.stalk V.point)
          (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
            (V.scheme.presheaf.stalk V.point))
          ((τ'.stalkHomAt hτ') ((pullback.fst zT zS).stalkHomAt hfst a)) :=
    congrArg₂ (· - ·) e1 (congrArg _ e2)
  rw [e3]
  exact hmem

/-- **Stacks Project, Tag 0GDX, clauses (1) and (3).** Let `S` be a locally Noetherian scheme,
let `T` be locally of finite type over `Spec ℤ`, let `t ∈ T` and `s ∈ S`, assume `𝒪_{S, s}` is a
G-ring, and let `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local homomorphism. Then for every `N ≥ 1`
there are an elementary étale neighbourhood `(V, v)` of `(S, s)` and a morphism `τ : V ⟶ T` with
`τ v = t`; moreover the square relating `σ` to `τ^♯_v` commutes modulo `𝔪_v ^ N`, which is the
extra conclusion that Tag 0CAW records as its clause (3). -/
@[stacks 0GDX "clauses (1) and (3) of the conclusion: the elementary étale neighbourhood \
`(V, v)` of `(S, s)` and the morphism `τ : V ⟶ T` with `τ(v) = t`. What is proved is STRONGER \
than those two clauses: it carries in addition the congruence that Tag 0CAW records as its \
clause (3), namely that the square relating `σ` to `τ^♯_v` commutes modulo `𝔪_v ^ N`, which is \
why this registration is kept; and the source's `T` of finite type over `Spec ℤ` is weakened to \
LOCALLY of finite type. None of `X`, `Y`, `φ`, `y_σ` enters this statement, so it says nothing \
about clauses (2) and (4) — the elementary étale neighbourhood `(W, w)` of `(X, x)` which is \
simultaneously one of `(Y ×_{T, τ} V, y_τ)`. THOSE ARE PROVED ELSEWHERE, twice over and \
independently, and both of those statements carry a registration for the whole conclusion: all \
four clauses are \
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_absoluteApproximation_full_section` in \
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AbsoluteApproximationFull`, \
and also \
`StacksDraft.ArtinApproximation.exists_common_elementaryEtaleNeighborhood_absoluteApproximation` \
in `StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.RelativeMapApproximation`. NO \
hypothesis beyond the source's is carried: \
the library's Tag 0CAU behind this deduction is unconditional, Theorem 07QZ being proved as \
`StacksDraft.ArtinApproximation.localApproximationProperty`"]
theorem exists_elementaryEtaleNeighborhood_absoluteApproximation
    {S T : Scheme.{u}} [IsLocallyNoetherian S]
    (hT : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from T))
    (t : T) (s : S) (hG : IsGRing (S.presheaf.stalk s))
    (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hσ : IsLocalHom σ) :
    ∃ V : EtaleNeighborhood S s, V.IsElementary ∧
      ∃ (τ : V.scheme ⟶ T) (hτ : τ V.point = t),
        ∀ a : T.presheaf.stalk t,
          V.completionMap (σ a) -
              algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)) (τ.stalkHomAt hτ a) ∈
            Ideal.map
              (algebraMap (V.scheme.presheaf.stalk V.point)
                (AdicCompletion (maximalIdeal (V.scheme.presheaf.stalk V.point))
                  (V.scheme.presheaf.stalk V.point)))
              (maximalIdeal (V.scheme.presheaf.stalk V.point) ^ N) := by
  have hTi := hT
  exact exists_elementaryEtaleNeighborhood_baseApproximation_over
    (specULiftZIsTerminal.{u}.from T) (specULiftZIsTerminal.{u}.from S) t s hG N hN σ hσ
    (specULiftZIsTerminal.{u}.hom_ext _ _)

end StacksDraft.ArtinApproximation

end
