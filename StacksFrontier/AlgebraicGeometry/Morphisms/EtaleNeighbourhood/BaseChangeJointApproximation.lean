module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximationScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation
public import StacksFrontier.RingTheory.GRing.Criteria
public import StacksCore.Tactic.StacksAttribute

/-!
# Approximating a map whose source is of finite type over a scheme underneath the base

This file proves the two steps with which the source's proof of Stacks Tag 0CAW opens: the
*algebraization of `φ`*, and the *affine-chart reduction* which turns the étale neighbourhood
that step produces into the étale **ring** map the rest of the source's proof works with.

Tag 0CAW is handed a local `𝒪_{S, s}`-algebra map `φ : 𝒪_{X, x} → 𝒪^∧_{Y_σ, y_σ}`, where
`Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}`, and its proof begins by replacing `φ` with an *actual*
morphism of schemes into `X`, defined on an elementary étale neighbourhood of `(Y_σ, y_σ)` and
agreeing with `φ` modulo `𝔪^N`: "Thus we may replace `φ` by this composition because the only
way `φ` enters the conclusion is via the commutativity requirement in part (5)". Everything the
source does afterwards — the presentation of `𝒪^∧_{S, s}` as a filtered colimit of smooth
`𝒪_{S, s}`-algebras, the descent of that étale neighbourhood to a stage, and the final
application of Tag 0CAU producing `V` and `τ` — operates on the neighbourhood this step produces.
It is therefore the step that makes the *joint* production of `V`, `τ`, `W` and `f` from `σ` and
`φ` possible at all: a choice of `V` and `τ` made before `φ` has been algebraized can make
clause (5) unsatisfiable, so no amount of work after an independent first stage can close
clauses (4) and (5).

The step is not an instance of Tag 0CAU. Tag 0CAU asks both of its schemes to be
locally of finite type over the base, and `Y_σ` is locally of finite type over
`Spec 𝒪^∧_{S, s}`, not over `S`, while `X` is locally of finite type over `S` and not over
`Spec 𝒪^∧_{S, s}`. What is proved here is the variant of Tag 0CAU in which the *source of `φ`*
is locally of finite type over a scheme `S` sitting underneath the actual base `Ŝ` — read at
`Ŝ = Spec 𝒪^∧_{S, s}` this is exactly the step above. The deduction from Tag 0CAU is the
replacement of `X` by its base change `X ×_S Ŝ`, which *is* locally of finite type over `Ŝ`,
together with the observation that `φ`, being a map of `𝒪_{S, s}`-algebras, extends canonically
to the local ring of `X ×_S Ŝ` at a point over `(x, ŝ)`.

## Main results

* `StacksDraft.ArtinApproximation.exists_point_stalkHom_pullback`: **the universal property of a
  fibre product at local rings.** Two local homomorphisms `α : 𝒪_{A, p} → R` and
  `β : 𝒪_{B, q} → R` into one local ring `R`, agreeing on `𝒪_{S, t}` for morphisms `a : A ⟶ S`
  and `b : B ⟶ S` carrying `p` and `q` to `t`, determine a point `z` of `A ×_S B` over `p` and
  `q` and a local homomorphism `𝒪_{A ×_S B, z} → R` restricting to `α` and to `β`.
* `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_approximation_over_base`:
  **Tag 0CAU with the source of `φ` only of finite type over a scheme underneath the base**, the
  step above. Read at `Ŝ = Spec 𝒪^∧_{S, s}`, `G` the second projection of
  `Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}` and `c` the morphism the completion map determines, it is
  that step verbatim.
* `StacksDraft.ArtinApproximation.stalkHomAt_specMap_fromSpecStalk`: the map of local rings of
  the morphism `Spec R ⟶ X` attached to a local homomorphism `𝒪_{X, x} → R` is that
  homomorphism, followed by the inverse of Mathlib's
  `AlgebraicGeometry.stalkClosedPointIso`. This is the identification of `R` with
  `𝒪_{Spec R, closed point}` which the `𝒪_{S, s}`-algebra structure of `𝒪^∧_{Y_σ, y_σ}` is
  stated through, and which clause (5) of Tag 0CAW needs on its base side as well.
* `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_algebraization`: the
  previous two combined, i.e. **the algebraization of `φ` at Tag 0CAW's own data**, with the
  `𝒪_{S, s}`-algebra structure of `𝒪^∧_{Y_σ, y_σ}` spelled out through the completion map
  `𝒪_{S, s} → 𝒪^∧_{S, s}`. It carries no G-ring hypothesis at all.
* `StacksDraft.ArtinApproximation.exists_isAffineOpen_etale_appLE`: **the affine-chart
  reduction**, which reads an étale neighbourhood of a point of a scheme — together with a
  morphism out of it — as ring-level data: an affine chart on which the structure morphism
  becomes an étale ring map inducing an isomorphism of residue fields at the two primes, the
  restriction on sections of the morphism out of it, and the identification of the local ring at
  the point with the localization of the chart ring at its prime. This is the reduction with
  which the source's proof of Tag 0CAW opens, run in the direction in which the previous step
  leaves the data.

## Implementation notes

*What is proved and what is not.* Clauses (4) and (5) of Tag 0CAW are **not** proved here, and
nothing in this file is registered for them. What is registered for Tag 0CAW is nothing at all:
the statements below are steps of the source's proof, not clauses of its conclusion. The two
clause-wise registrations of Tag 0CAW are
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_baseApproximation` (clauses
(1) for `(v, τ)`, (2) and (3)) and
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_relativeApproximation`
(the rest of clause (1), clause (4) and clause (5), from a first stage and a map into
`𝒪^∧_{Y ×_{T, τ} V, (y, v)}` supplied as hypotheses); neither is superseded by anything here.

*Why the fibre-product step is stated separately.* The extension of `φ` to the base change is
the universal property of `A ×_S B` applied to the two morphisms `Spec R ⟶ A` and
`Spec R ⟶ B` that `α` and `β` determine, `R` being the completed local ring. Since
`AlgebraicGeometry.SpecToEquivOfLocalRing` makes such morphisms the same thing as local
homomorphisms out of local rings, that universal property can be stated with no `Spec` in it,
and that is the shape every consumer wants; so it is proved once, in that shape. The proof does
not go through the equivalence itself but through
`AlgebraicGeometry.Scheme.stalkClosedPointTo`, one direction of it, whose compatibility with
composition and with `X.fromSpecStalk` is what the three steps of the argument are.

*Which hypotheses are carried.* None beyond the source's. The form of Tag 0CAU used here is
unconditional, Theorem 07QZ being proved as
`StacksDraft.ArtinApproximation.localApproximationProperty`, and Tag 0CAR as
`StacksDraft.ArtinApproximation.artinApproximationGRing`. The G-ring hypothesis is the one Tag
0CAU needs, namely on the local ring of the *actual* base `Ŝ` at the image point; at
`Ŝ = Spec 𝒪^∧_{S, s}` that ring is `𝒪^∧_{S, s}`, which Tag 07PS makes a G-ring for free, so the
corollary carries no G-ring hypothesis at all — not even the source's own, which is about
`𝒪_{S, s}`.

*Why the affine-chart reduction is not a copy of Tag 0CAU's.* Tag 0CAU's own reduction, inside
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_approximation`, runs from
rings to schemes: it is handed an étale algebra over a chart ring and reads its spectrum back as
an elementary étale neighbourhood. Here the neighbourhood is what the previous step produces, so
the reduction has to run the other way, and the chart-level plumbing of that file — the germ
identity `StacksDraft.ArtinApproximation.appLE_germ` and the identification
`StacksDraft.ArtinApproximation.spec_residueFieldMap_eq_of_eq` of the residue field map of a
`Spec` with `Ideal.ResidueField.map` — is reused rather than restated.

*Why `Ŝ` is not required to be locally of finite type over `S`.* It is not, in the application:
`Spec 𝒪^∧_{S, s} ⟶ S` is not of finite type. Only `IsLocallyNoetherian Ŝ` and
`LocallyOfFiniteType G` are used, and the morphism `c : Ŝ ⟶ S` enters solely through the
compatibility of `φ` with it.

## References

* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
* [Stacks Project, Tag 0CAU](https://stacks.math.columbia.edu/tag/0CAU)
* [Stacks Project, Tag 07PS](https://stacks.math.columbia.edu/tag/07PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- The map of stalks induced at a point, with no transport, is the stalk map. -/
private theorem stalkHomAt_rfl_eq_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.stalkHomAt (rfl : f x = f x) = (f.stalkMap x).hom := by
  simp [Scheme.Hom.stalkHomAt]

/-- The local homomorphism attached to the morphism `Spec.map ρ ≫ fromSpecStalk x` is `ρ`. -/
private theorem stalkCongr_comp_stalkClosedPointTo_specMap {X : Scheme.{u}} {x : X}
    {R : CommRingCat.{u}} [IsLocalRing R] (ρ : X.presheaf.stalk x ⟶ R) (hρ : IsLocalHom ρ.hom)
    (hpt : (Spec.map ρ ≫ X.fromSpecStalk x) (closedPoint R) = x) :
    (X.presheaf.stalkCongr (.of_eq hpt.symm)).hom ≫
        Scheme.stalkClosedPointTo (Spec.map ρ ≫ X.fromSpecStalk x) = ρ := by
  let := hρ
  -- A germ followed by the transport of stalks along an equality of points is a germ.
  have hgerm : ∀ (u v : X) (huv : u = v) (U : X.Opens) (hu : u ∈ U),
      X.presheaf.germ U u hu ≫ (X.presheaf.stalkCongr (.of_eq huv)).hom =
        X.presheaf.germ U v (huv ▸ hu) := by
    intro u v huv U hu
    cases huv
    simp
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU => ?_
  have hU : (Spec.map ρ ≫ X.fromSpecStalk x) (closedPoint R) ∈ U :=
    (congrArg (fun zz : X => zz ∈ U) hpt.symm).mp hxU
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ Scheme.stalkClosedPointTo (Spec.map ρ ≫ X.fromSpecStalk x))
      (hgerm x _ hpt.symm U hxU))).trans
    (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk ρ U hU)

/-- **The universal property of a fibre product at local rings.** Let `a : A ⟶ S` and
`b : B ⟶ S` be morphisms of schemes, let `p ∈ A` and `q ∈ B` lie over the same point `t ∈ S`,
let `R` be a local ring and let `α : 𝒪_{A, p} → R` and `β : 𝒪_{B, q} → R` be local
homomorphisms which agree on `𝒪_{S, t}`. Then there are a point `z` of `A ×_S B` lying over `p`
and over `q` and a local homomorphism `γ : 𝒪_{A ×_S B, z} → R` whose restrictions along the two
projections are `α` and `β`.

This is `AlgebraicGeometry.SpecToEquivOfLocalRing` combined with the universal property of the
fibre product: `α` and `β` are the two morphisms `Spec R ⟶ A` and `Spec R ⟶ B`, the hypothesis
is that they agree over `S`, and `γ` is the local homomorphism attached to the induced morphism
`Spec R ⟶ A ×_S B` at the image of the closed point. -/
theorem exists_point_stalkHom_pullback {S A B : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
    {p : A} {q : B} {t : S} (hp : a p = t) (hq : b q = t)
    (R : Type u) [CommRing R] [IsLocalRing R]
    (α : A.presheaf.stalk p →+* R) (β : B.presheaf.stalk q →+* R)
    [IsLocalHom α] [IsLocalHom β]
    (hab : α.comp (a.stalkHomAt hp) = β.comp (b.stalkHomAt hq)) :
    ∃ (z : (pullback a b : Scheme.{u})) (hz₁ : pullback.fst a b z = p)
      (hz₂ : pullback.snd a b z = q)
      (γ : (pullback a b : Scheme.{u}).presheaf.stalk z →+* R),
      IsLocalHom γ ∧ γ.comp ((pullback.fst a b).stalkHomAt hz₁) = α ∧
        γ.comp ((pullback.snd a b).stalkHomAt hz₂) = β := by
  -- The canonical morphism out of the spectrum of a local ring, read through the map of local
  -- rings it induces.
  have hfsc : ∀ (A' B' : Scheme.{u}) (k : A' ⟶ B') (a' : A') (b' : B') (h : k a' = b'),
      A'.fromSpecStalk a' ≫ k =
        Spec.map (CommRingCat.ofHom (k.stalkHomAt h)) ≫ B'.fromSpecStalk b' := by
    intro A' B' k a' b' h
    subst h
    rw [stalkHomAt_rfl_eq_stalkMap, CommRingCat.ofHom_hom]
    exact (Scheme.SpecMap_stalkMap_fromSpecStalk k).symm
  -- The morphism attached to a local homomorphism carries the closed point to the base point.
  have hcp : ∀ (A' : Scheme.{u}) (p' : A') (ρ : A'.presheaf.stalk p' ⟶ CommRingCat.of R),
      IsLocalHom ρ.hom → (Spec.map ρ ≫ A'.fromSpecStalk p') (closedPoint R) = p' := by
    intro A' p' ρ hρ
    let := hρ
    show A'.fromSpecStalk p' ((Spec.map ρ) (closedPoint R)) = p'
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  -- Equal morphisms have the same attached local homomorphism.
  have hcongr : ∀ (W : Scheme.{u}) (w : W) (m₁ m₂ : Spec (CommRingCat.of R) ⟶ W), m₁ = m₂ →
      ∀ (h₁ : m₁ (closedPoint R) = w) (h₂ : m₂ (closedPoint R) = w),
        (W.presheaf.stalkCongr (.of_eq h₁.symm)).hom ≫ Scheme.stalkClosedPointTo m₁ =
          (W.presheaf.stalkCongr (.of_eq h₂.symm)).hom ≫ Scheme.stalkClosedPointTo m₂ := by
    intro W w m₁ m₂ hm h₁ h₂
    subst hm
    rfl
  have hαc : IsLocalHom (CommRingCat.ofHom α).hom := inferInstanceAs (IsLocalHom α)
  have hβc : IsLocalHom (CommRingCat.ofHom β).hom := inferInstanceAs (IsLocalHom β)
  -- The two morphisms out of `Spec R` agree over `S`.
  have hsq : (Spec.map (CommRingCat.ofHom α) ≫ A.fromSpecStalk p) ≫ a =
      (Spec.map (CommRingCat.ofHom β) ≫ B.fromSpecStalk q) ≫ b := by
    rw [Category.assoc, Category.assoc, hfsc A S a p t hp, hfsc B S b q t hq,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : Spec (CommRingCat.of R) ⟶ (pullback a b : Scheme.{u}),
      m ≫ pullback.fst a b = Spec.map (CommRingCat.ofHom α) ≫ A.fromSpecStalk p ∧
        m ≫ pullback.snd a b = Spec.map (CommRingCat.ofHom β) ≫ B.fromSpecStalk q :=
    ⟨pullback.lift _ _ hsq, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hz₁ : pullback.fst a b (m (closedPoint R)) = p :=
    (congrArg (fun k : Spec (CommRingCat.of R) ⟶ A => k (closedPoint R)) hm₁).trans
      (hcp A p (CommRingCat.ofHom α) hαc)
  have hz₂ : pullback.snd a b (m (closedPoint R)) = q :=
    (congrArg (fun k : Spec (CommRingCat.of R) ⟶ B => k (closedPoint R)) hm₂).trans
      (hcp B q (CommRingCat.ofHom β) hβc)
  -- The restriction of the attached local homomorphism along a leg of the fibre product.
  have key : ∀ (W : Scheme.{u}) (w : W) (k : (pullback a b : Scheme.{u}) ⟶ W)
      (ρ : W.presheaf.stalk w ⟶ CommRingCat.of R), IsLocalHom ρ.hom →
      m ≫ k = Spec.map ρ ≫ W.fromSpecStalk w →
      ∀ hk : k (m (closedPoint R)) = w,
        (Scheme.stalkClosedPointTo m).hom.comp (k.stalkHomAt hk) = ρ.hom := by
    intro W w k ρ hρ hmk hk
    let := hρ
    have hpt : (Spec.map ρ ≫ W.fromSpecStalk w) (closedPoint R) = w := hcp W w ρ hρ
    apply CommRingCat.hom_ext_iff.mp
    show (W.presheaf.stalkCongr (.of_eq hk.symm)).hom ≫
      k.stalkMap (m (closedPoint R)) ≫ Scheme.stalkClosedPointTo m = ρ
    exact (congrArg (fun zz => (W.presheaf.stalkCongr (.of_eq hk.symm)).hom ≫ zz)
        (Scheme.stalkClosedPointTo_comp m k).symm).trans
      ((hcongr W w (m ≫ k) (Spec.map ρ ≫ W.fromSpecStalk w) hmk hk hpt).trans
        (stalkCongr_comp_stalkClosedPointTo_specMap ρ hρ hpt))
  refine ⟨m (closedPoint R), hz₁, hz₂, (Scheme.stalkClosedPointTo m).hom,
    Scheme.isLocalHom_stalkClosedPointTo m, ?_, ?_⟩
  · exact key A p (pullback.fst a b) (CommRingCat.ofHom α) hαc hm₁ hz₁
  · exact key B q (pullback.snd a b) (CommRingCat.ofHom β) hβc hm₂ hz₂

/-- **Stacks Tag 0CAU with the source of `φ` only locally of finite type over a scheme
underneath the base.** Let `Ŝ` be a locally Noetherian scheme with a morphism `c : Ŝ ⟶ S` to an
arbitrary scheme `S`, let `fX : X ⟶ S` and `G : 𝒴 ⟶ Ŝ` be locally of finite type, let `x ∈ X`
and `y ∈ 𝒴` with `fX x = s`, `G y = ŝ` and `c ŝ = s`, assume `𝒪_{Ŝ, ŝ}` is a G-ring, and let
`φ : 𝒪_{X, x} → 𝒪^∧_{𝒴, y}` be a local homomorphism of `𝒪_{S, s}`-algebras, the algebra
structure on the target being the one through `𝒪_{S, s} → 𝒪_{Ŝ, ŝ} → 𝒪_{𝒴, y}`. Then for every
`N ≥ 1` there are an elementary étale neighbourhood `(W, w)` of `(𝒴, y)` and a morphism
`F : W ⟶ X` with `F w = x`, compatible with the two morphisms to `S`, such that `φ` agrees
modulo `𝔪_w ^ N` with the map of local rings induced by `F`.

This is the step with which the source's proof of Tag 0CAW opens, read at
`Ŝ = Spec 𝒪^∧_{S, s}`: the *algebraization of `φ`*. The deduction from Tag 0CAU replaces `X` by
`X ×_S Ŝ`, which is locally of finite type over `Ŝ`, and extends `φ` to the local ring of that
base change by `StacksDraft.ArtinApproximation.exists_point_stalkHom_pullback`. -/
theorem exists_elementaryEtaleNeighborhood_approximation_over_base
    {S Sb X Y : Scheme.{u}} (fX : X ⟶ S) (c : Sb ⟶ S) (G : Y ⟶ Sb)
    [IsLocallyNoetherian Sb] [LocallyOfFiniteType fX] [LocallyOfFiniteType G]
    (x : X) (s : S) (sb : Sb) (y : Y)
    (hx : fX x = s) (hy : G y = sb) (hc : c sb = s)
    (hG : IsGRing (Sb.presheaf.stalk sb))
    (N : ℕ) (hN : 1 ≤ N)
    (φ : X.presheaf.stalk x →+*
      AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
    (hφ : IsLocalHom φ)
    (hφbase : φ.comp (fX.stalkHomAt hx) =
      (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))).comp
        ((G.stalkHomAt hy).comp (c.stalkHomAt hc))) :
    ∃ W : EtaleNeighborhood Y y, W.IsElementary ∧
      ∃ (F : W.scheme ⟶ X) (hF : F W.point = x),
        F ≫ fX = W.toBase ≫ G ≫ c ∧
        ∀ a : X.presheaf.stalk x,
          W.completionMap (φ a) -
              algebraMap (W.scheme.presheaf.stalk W.point)
                (AdicCompletion (maximalIdeal (W.scheme.presheaf.stalk W.point))
                  (W.scheme.presheaf.stalk W.point)) (F.stalkHomAt hF a) ∈
            Ideal.map
              (algebraMap (W.scheme.presheaf.stalk W.point)
                (AdicCompletion (maximalIdeal (W.scheme.presheaf.stalk W.point))
                  (W.scheme.presheaf.stalk W.point)))
              (maximalIdeal (W.scheme.presheaf.stalk W.point) ^ N) := by
  subst hy
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian G
  have hφ' : IsLocalHom φ := hφ
  have hr := stalkHomAt_rfl_eq_stalkMap G y
  -- the structure map of the completed local ring of `𝒴` at `y` over `𝒪_{Ŝ, ŝ}`
  have hlocG : IsLocalHom (G.stalkHomAt (rfl : G y = G y)) := by
    rw [hr]
    infer_instance
  have hlocψ : IsLocalHom ((algebraMap (Y.presheaf.stalk y)
      (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))).comp
      (G.stalkHomAt (rfl : G y = G y))) := RingHom.isLocalHom_comp _ _
  -- the extension of `φ` to the base change of `X` along `c`
  obtain ⟨z, hz₁, hz₂, γ, hγloc, hγ₁, hγ₂⟩ :=
    exists_point_stalkHom_pullback fX c hx hc
      (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)) φ
      ((algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))).comp
        (G.stalkHomAt (rfl : G y = G y)))
      (hφbase.trans (RingHom.comp_assoc _ _ _).symm)
  have := hγloc
  -- Tag 0CAU for `G : 𝒴 ⟶ Ŝ` and the second projection of `X ×_S Ŝ`
  have hbase : γ.comp ((Sb.presheaf.stalkCongr (.of_eq hz₂.symm)).hom ≫
        (pullback.snd fX c).stalkMap z).hom =
      (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))).comp
        (G.stalkMap y).hom := by
    rw [← hr]
    exact hγ₂
  obtain ⟨W, hWel, F₀, hF₀, hover, hcong⟩ :=
    exists_elementaryEtaleNeighborhood_approximation G (pullback.snd fX c) y z hz₂.symm hG N hN
      γ hγloc hbase
  -- read back along the first projection
  have hFx : (F₀ ≫ pullback.fst fX c) W.point = x :=
    (congrArg (fun w => pullback.fst fX c w) hF₀).trans hz₁
  refine ⟨W, hWel, F₀ ≫ pullback.fst fX c, hFx, ?_, fun a => ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hover, Category.assoc]
  · rw [← RingHom.congr_fun hγ₁ a,
      RingHom.congr_fun (Scheme.Hom.stalkHomAt_comp F₀ (pullback.fst fX c) hF₀ hz₁) a]
    exact hcong _

/-- **The map of local rings of the morphism `Spec R ⟶ X` attached to a local homomorphism
`ρ : 𝒪_{X, x} → R`, read at the closed point, is `ρ` itself.** Precisely: it is `ρ` followed by
the inverse of Mathlib's `AlgebraicGeometry.stalkClosedPointIso`, which identifies `R` with the
local ring of `Spec R` at its closed point.

This is the identification that a consumer of
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_approximation_over_base` needs
in order to recognise the `𝒪_{S, s}`-algebra structure of the target: at
`Ŝ = Spec 𝒪^∧_{S, s}` the morphism `c : Ŝ ⟶ S` is the one the completion map
`𝒪_{S, s} → 𝒪^∧_{S, s}` determines, and this says that its map of local rings *is* the
completion map, up to that one identification. Tag 0CAW's clause (5) needs the same
identification on the base side, where the `V` it produces is a `Spec D`. -/
theorem stalkHomAt_specMap_fromSpecStalk {X : Scheme.{u}} {x : X} {R : CommRingCat.{u}}
    [IsLocalRing R] (ρ : X.presheaf.stalk x ⟶ R) (hρ : IsLocalHom ρ.hom)
    (hpt : (Spec.map ρ ≫ X.fromSpecStalk x) (closedPoint R) = x) :
    (Spec.map ρ ≫ X.fromSpecStalk x).stalkHomAt hpt =
      (stalkClosedPointIso R).inv.hom.comp ρ.hom := by
  let := hρ
  have h0 := stalkCongr_comp_stalkClosedPointTo_specMap ρ hρ hpt
  have h0' : ((stalkClosedPointIso R).hom.hom).comp
      ((Spec.map ρ ≫ X.fromSpecStalk x).stalkHomAt hpt) = ρ.hom := by
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom ((Category.assoc _ _ _).trans h0)
  rw [← h0', ← RingHom.comp_assoc, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
    RingHom.id_comp]

/-- **The algebraization of `φ`, at Stacks Tag 0CAW's own data.** Let `S` be locally Noetherian,
let `fX : X ⟶ S` and `g : Y ⟶ T` be locally of finite type, let `x ∈ X` lie over `s ∈ S`, let
`b : Spec 𝒪^∧_{S, s} ⟶ T` be a morphism — in Tag 0CAW the one `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}`
determines — and let `y_σ` be a point of `Y_σ = Y ×_{T, b} Spec 𝒪^∧_{S, s}` lying over the closed
point. Let `φ : 𝒪_{X, x} → 𝒪^∧_{Y_σ, y_σ}` be a local homomorphism of `𝒪_{S, s}`-algebras, the
algebra structure on the target being the one through the completion map
`𝒪_{S, s} → 𝒪^∧_{S, s} = 𝒪_{Spec 𝒪^∧_{S, s}, closed point} → 𝒪_{Y_σ, y_σ}`. Then for every
`N ≥ 1` there are an elementary étale neighbourhood `(W, w)` of `(Y_σ, y_σ)` and a morphism
`F : W ⟶ X` with `F w = x`, compatible over `S`, such that `φ` agrees modulo `𝔪_w ^ N` with the
map of local rings induced by `F`.

This is the first step of the source's proof: "there exists an étale ring map
`B ⊗_{C, σ} R^∧ → B'` inducing an isomorphism of residue fields and an `R`-algebra map `A → B'`
such that `A → B' → (B')^∧ = (B ⊗_{C, σ} R^∧)^∧` is the same as `φ` modulo `𝔪^N`. Thus we may
replace `φ` by this composition". No G-ring hypothesis is carried — not even the source's, which
is about `𝒪_{S, s}`: the G-ring that Tag 0CAU is applied with here is `𝒪^∧_{S, s}`, which is a
complete Noetherian local ring and hence a G-ring by Tag 07PS.

This step does **not** prove clause (4) or clause (5) of Tag 0CAW, and nothing here is
registered for them: the `W` produced is an étale neighbourhood of `(Y_σ, y_σ)`, not of
`(Y ×_{T, τ} V, (y, v))`, and no `V` or `τ` has been produced at all. What it does is make the
*joint* production of `V`, `τ`, `W` and `f` possible, by removing `φ` from the problem before
`V` and `τ` are chosen. -/
theorem exists_elementaryEtaleNeighborhood_algebraization
    {S T X Y : Scheme.{u}} (fX : X ⟶ S) (g : Y ⟶ T)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType g]
    (x : X) (s : S) (hx : fX x = s)
    (b : Spec (CommRingCat.of (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s))) ⟶ T)
    (yσ : (pullback g b : Scheme.{u}))
    (hvσ : pullback.snd g b yσ =
      closedPoint (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))
    (N : ℕ) (hN : 1 ≤ N)
    (φ : X.presheaf.stalk x →+*
      AdicCompletion (maximalIdeal ((pullback g b : Scheme.{u}).presheaf.stalk yσ))
        ((pullback g b : Scheme.{u}).presheaf.stalk yσ))
    (hφ : IsLocalHom φ)
    (hφbase : φ.comp (fX.stalkHomAt hx) =
      (algebraMap ((pullback g b : Scheme.{u}).presheaf.stalk yσ)
          (AdicCompletion (maximalIdeal ((pullback g b : Scheme.{u}).presheaf.stalk yσ))
            ((pullback g b : Scheme.{u}).presheaf.stalk yσ))).comp
        (((pullback.snd g b).stalkHomAt hvσ).comp
          ((stalkClosedPointIso (CommRingCat.of
                (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                  (S.presheaf.stalk s)))).inv.hom.comp
            (algebraMap (S.presheaf.stalk s)
              (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))))) :
    ∃ W : EtaleNeighborhood (pullback g b : Scheme.{u}) yσ, W.IsElementary ∧
      ∃ (F : W.scheme ⟶ X) (hF : F W.point = x),
        F ≫ fX = W.toBase ≫ pullback.snd g b ≫
            (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
                (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
              S.fromSpecStalk s) ∧
        ∀ a : X.presheaf.stalk x,
          W.completionMap (φ a) -
              algebraMap (W.scheme.presheaf.stalk W.point)
                (AdicCompletion (maximalIdeal (W.scheme.presheaf.stalk W.point))
                  (W.scheme.presheaf.stalk W.point)) (F.stalkHomAt hF a) ∈
            Ideal.map
              (algebraMap (W.scheme.presheaf.stalk W.point)
                (AdicCompletion (maximalIdeal (W.scheme.presheaf.stalk W.point))
                  (W.scheme.presheaf.stalk W.point)))
              (maximalIdeal (W.scheme.presheaf.stalk W.point) ^ N) := by
  have hlocc : IsLocalHom (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))))
  -- the morphism `Spec 𝒪^∧_{S, s} ⟶ S` and the image of its closed point
  have hc : (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s)
      (closedPoint (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s))) = s := by
    show S.fromSpecStalk s ((Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))))
        (closedPoint _)) = s
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  -- `𝒪^∧_{S, s}` is a G-ring (Tag 07PS), hence so is the local ring of its spectrum at the
  -- closed point
  have hG : IsGRing ((Spec (CommRingCat.of (AdicCompletion
      (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))).presheaf.stalk
      (closedPoint (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s)))) := by
    let e := (stalkClosedPointIso (CommRingCat.of (AdicCompletion
      (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))).symm.commRingCatIsoToRingEquiv
    let : Algebra (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
        ((Spec (CommRingCat.of (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s)))).presheaf.stalk
          (closedPoint (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
            (S.presheaf.stalk s)))) := e.toRingHom.toAlgebra
    let : Algebra.FiniteType
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
        ((Spec (CommRingCat.of (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s)))).presheaf.stalk
          (closedPoint (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
            (S.presheaf.stalk s)))) :=
      RingHom.finiteType_algebraMap.mp
        (RingHom.FiniteType.of_surjective e.toRingHom e.surjective)
    exact isGRing_of_essFiniteType (isGRing_of_isPrecomplete_maximalIdeal
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))
  -- the map of local rings of `Spec 𝒪^∧_{S, s} ⟶ S` is the completion map
  have hcstalk : (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s).stalkHomAt hc =
      (stalkClosedPointIso (CommRingCat.of (AdicCompletion
        (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))).inv.hom.comp
        (algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))) :=
    stalkHomAt_specMap_fromSpecStalk _ hlocc hc
  exact exists_elementaryEtaleNeighborhood_approximation_over_base fX
    (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s) (pullback.snd g b) x s _ yσ hx hvσ hc hG N hN φ hφ
    (by rw [hφbase, hcstalk])

/-! ### The affine-chart reduction -/

attribute [local instance] PrimeSpectrum.isPrime

/-- **The affine-chart reduction: an étale neighbourhood of a point of a scheme, together with a
morphism out of it, read as ring-level data.** Let `p : W ⟶ Z` be étale, let `w ∈ W` lie over
`z ∈ Z`, assume the residue field map of `p` at `w` is an isomorphism, and let `F : W ⟶ X` be a
further morphism carrying `w` to `x`. Choose an affine open `UZ ∋ z` of `Z` and any open
`UX ∋ x` of `X`. Then there is an affine open `UW ∋ w` of `W` contained in both preimages, such
that, writing `B' = Γ(W, UW)`, `R = Γ(Z, UZ)`, `A = Γ(X, UX)` and `ι = p^♯`, `κ = F^♯` for the
two restriction maps on sections:

* `ι : R → B'` is an **étale** ring map;
* the prime of `w` **contracts** along `ι` to the prime of `z`, and the induced extension of
  residue fields `κ(𝔭_z) → κ(𝔭_w)` is **bijective**;
* `𝒪_{W, w}` is the **localization** of `B'` at the prime of `w`, by an isomorphism carrying
  germs to the canonical maps, and carrying the two maps of local rings induced by `p` and by
  `F` to the localizations of `ι` and of `κ`.

This is the reduction with which the source's proof of Tag 0CAW opens — "after replacing `X`,
`S`, `T`, `Y` by affine open subschemes we may assume the diagram comes from applying `Spec`" —
run in the direction the formalized first step of that proof needs. Tag 0CAU's own reduction, inside
`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_approximation`, runs the
*other* way: it starts from an étale algebra `A'` over a chart ring and reads `Spec A'` back as
an elementary étale neighbourhood of the scheme. Here the étale neighbourhood is given — it is
what the algebraization of `φ`
(`StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_algebraization`) produces —
and the étale *ring* map is what is extracted, because the descent of that neighbourhood to a
stage of a filtered colimit (`Algebra.Etale.exists_etale_stage_of_isColimit_of_smallCategory`)
is a statement about rings and has nothing to grip on a scheme.

Nothing here is registered for Tag 0CAW: this is a step of its proof, not one of its clauses.

The hypothesis on the residue field is `IsIso (p.residueFieldMap w)`, which for the structure
morphism of an étale neighbourhood is exactly
`AlgebraicGeometry.EtaleNeighborhood.isElementary_iff`; the two point equalities are taken as
data, so that an étale neighbourhood is fed in as `p := U.toBase`, `hz := U.map_point` with no
transport of stalks. The open `UX` is *not* required to be affine: nothing below needs it, and a
consumer that wants `𝒪_{X, x}` as a localization of `Γ(X, UX)` can ask for it separately. -/
theorem exists_isAffineOpen_etale_appLE {Z X W : Scheme.{u}} (p : W ⟶ Z) [Etale p] (F : W ⟶ X)
    (w : W) {z : Z} (hz : p w = z) {x : X} (hx : F w = x)
    (hres : IsIso (p.residueFieldMap w))
    {UZ : Z.Opens} (hUZ : IsAffineOpen UZ) (hzU : z ∈ UZ)
    {UX : X.Opens} (hxU : x ∈ UX) :
    ∃ (UW : W.Opens) (hUW : IsAffineOpen UW) (hw : w ∈ UW)
      (hWZ : UW ≤ p ⁻¹ᵁ UZ) (hWX : UW ≤ F ⁻¹ᵁ UX),
      (p.appLE UZ UW hWZ).hom.Etale ∧
      ∃ _hcomap : (hUZ.primeIdealOf ⟨z, hzU⟩).asIdeal =
          (hUW.primeIdealOf ⟨w, hw⟩).asIdeal.comap (p.appLE UZ UW hWZ).hom,
        Function.Bijective
            (Ideal.ResidueField.map (hUZ.primeIdealOf ⟨z, hzU⟩).asIdeal
              (hUW.primeIdealOf ⟨w, hw⟩).asIdeal (p.appLE UZ UW hWZ).hom _hcomap) ∧
          ∃ e : W.presheaf.stalk w ≃+*
              Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal,
            (∀ b : Γ(W, UW), e ((W.presheaf.germ UW w hw).hom b) =
                algebraMap Γ(W, UW)
                  (Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal) b) ∧
            (∀ c : Γ(Z, UZ), e (p.stalkHomAt hz ((Z.presheaf.germ UZ z hzU).hom c)) =
                algebraMap Γ(W, UW)
                  (Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal)
                  ((p.appLE UZ UW hWZ).hom c)) ∧
            (∀ a : Γ(X, UX), e (F.stalkHomAt hx ((X.presheaf.germ UX x hxU).hom a)) =
                algebraMap Γ(W, UW)
                  (Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal)
                  ((F.appLE UX UW hWX).hom a)) := by
  subst hz
  subst hx
  -- An affine open around `w` inside both preimages.
  obtain ⟨UW, hUW, hw, hsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := W) (x := w)
      (U := p ⁻¹ᵁ UZ ⊓ F ⁻¹ᵁ UX) ⟨hzU, hxU⟩
  have hle : UW ≤ p ⁻¹ᵁ UZ ⊓ F ⁻¹ᵁ UX := SetLike.coe_subset_coe.mp hsub
  have hWZ : UW ≤ p ⁻¹ᵁ UZ := hle.trans inf_le_left
  have hWX : UW ≤ F ⁻¹ᵁ UX := hle.trans inf_le_right
  -- The prime of `w` contracts to the prime of `p w`.
  have hcomap : (hUZ.primeIdealOf ⟨p w, hzU⟩).asIdeal =
      (hUW.primeIdealOf ⟨w, hw⟩).asIdeal.comap (p.appLE UZ UW hWZ).hom :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE UZ hUZ UW hUW hWZ hw).1).symm
  refine ⟨UW, hUW, hw, hWZ, hWX, p.etale_appLE hUZ hUW hWZ, hcomap, ?_, ?_⟩
  · -- The residue field extension is bijective, because `p` is residually trivial at `w`.
    have hcompZ : (Spec.map (p.appLE UZ UW hWZ) ≫ hUZ.fromSpec).residueFieldMap
          (hUW.primeIdealOf ⟨w, hw⟩) =
        hUZ.fromSpec.residueFieldMap (Spec.map (p.appLE UZ UW hWZ) (hUW.primeIdealOf ⟨w, hw⟩)) ≫
          (Spec.map (p.appLE UZ UW hWZ)).residueFieldMap (hUW.primeIdealOf ⟨w, hw⟩) :=
      Scheme.residueFieldMap_comp _ _ _
    have hcompW : (hUW.fromSpec ≫ p).residueFieldMap (hUW.primeIdealOf ⟨w, hw⟩) =
        p.residueFieldMap (hUW.fromSpec (hUW.primeIdealOf ⟨w, hw⟩)) ≫
          hUW.fromSpec.residueFieldMap (hUW.primeIdealOf ⟨w, hw⟩) :=
      Scheme.residueFieldMap_comp _ _ _
    have hOpenW : ∀ v : ↥(Spec Γ(W, UW)), IsIso (hUW.fromSpec.residueFieldMap v) :=
      fun _ => inferInstance
    have hOpenZ : ∀ v : ↥(Spec Γ(Z, UZ)), IsIso (hUZ.fromSpec.residueFieldMap v) :=
      fun _ => inferInstance
    have hA : IsIso ((Spec.map (p.appLE UZ UW hWZ) ≫ hUZ.fromSpec).residueFieldMap
        (hUW.primeIdealOf ⟨w, hw⟩)) := by
      rw [IsAffineOpen.SpecMap_appLE_fromSpec p hUZ hUW hWZ, hcompW]
      exact IsIso.comp_isIso'
        ((p.isIso_residueFieldMap_congr (hUW.fromSpec_primeIdealOf ⟨w, hw⟩)).mpr hres)
        (hOpenW _)
    rw [hcompZ] at hA
    have : IsIso ((Spec.map (p.appLE UZ UW hWZ)).residueFieldMap
        (hUW.primeIdealOf ⟨w, hw⟩)) :=
      @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
        (hOpenZ (Spec.map (p.appLE UZ UW hWZ) (hUW.primeIdealOf ⟨w, hw⟩))) hA
    have hp : Spec.map (p.appLE UZ UW hWZ) (hUW.primeIdealOf ⟨w, hw⟩) =
        hUZ.primeIdealOf ⟨p w, hzU⟩ :=
      IsAffineOpen.comap_primeIdealOf_appLE UZ hUZ UW hUW hWZ hw
    have hring : ((Scheme.Spec.residueFieldIso Γ(Z, UZ) (hUZ.primeIdealOf ⟨p w, hzU⟩)).inv ≫
        (Scheme.residueFieldCongr hp).inv ≫
        (Spec.map (p.appLE UZ UW hWZ)).residueFieldMap (hUW.primeIdealOf ⟨w, hw⟩) ≫
        (Scheme.Spec.residueFieldIso Γ(W, UW) (hUW.primeIdealOf ⟨w, hw⟩)).hom) =
        CommRingCat.ofHom
          (Ideal.ResidueField.map (hUZ.primeIdealOf ⟨p w, hzU⟩).asIdeal
            (hUW.primeIdealOf ⟨w, hw⟩).asIdeal (p.appLE UZ UW hWZ).hom hcomap) :=
      CommRingCat.hom_ext (spec_residueFieldMap_eq_of_eq (p.appLE UZ UW hWZ)
        (hUW.primeIdealOf ⟨w, hw⟩) (hUZ.primeIdealOf ⟨p w, hzU⟩) hp hcomap.symm)
    have hiso : IsIso (CommRingCat.ofHom
        (Ideal.ResidueField.map (hUZ.primeIdealOf ⟨p w, hzU⟩).asIdeal
          (hUW.primeIdealOf ⟨w, hw⟩).asIdeal (p.appLE UZ UW hWZ).hom hcomap)) := by
      rw [← hring]
      infer_instance
    rwa [ConcreteCategory.isIso_iff_bijective] at hiso
  · -- The local ring of `W` at `w` is the localization of the chart at the prime of `w`.
    let : Algebra Γ(W, UW) (W.presheaf.stalk w) :=
      W.presheaf.algebra_section_stalk ⟨w, hw⟩
    have : IsLocalization.AtPrime (W.presheaf.stalk w)
        (hUW.primeIdealOf ⟨w, hw⟩).asIdeal := hUW.isLocalization_stalk ⟨w, hw⟩
    refine ⟨(IsLocalization.algEquiv (hUW.primeIdealOf ⟨w, hw⟩).asIdeal.primeCompl
      (W.presheaf.stalk w)
      (Localization.AtPrime (hUW.primeIdealOf ⟨w, hw⟩).asIdeal)).toRingEquiv,
      fun b => (IsLocalization.algEquiv _ _ _).commutes b, fun c => ?_, fun a => ?_⟩
    · have h := congrArg (fun k : Γ(Z, UZ) ⟶ _ => k.hom c)
        (appLE_germ p UZ UW hWZ w hw hzU)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
      rw [stalkHomAt_rfl_eq_stalkMap, ← h]
      exact (IsLocalization.algEquiv _ _ _).commutes _
    · have h := congrArg (fun k : Γ(X, UX) ⟶ _ => k.hom a)
        (appLE_germ F UX UW hWX w hw hxU)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
      rw [stalkHomAt_rfl_eq_stalkMap, ← h]
      exact (IsLocalization.algEquiv _ _ _).commutes _

end StacksDraft.ArtinApproximation

end
