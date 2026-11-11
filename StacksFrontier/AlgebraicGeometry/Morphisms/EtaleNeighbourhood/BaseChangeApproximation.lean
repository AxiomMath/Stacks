module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximationScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation

/-!
# Artin approximation over a second base

Tag 0CAU approximates a local homomorphism `𝒪_{Y, y} → 𝒪^∧_{X, x}` between the local rings of
two schemes locally of finite type over one and the same locally Noetherian base `S`. Tag 0CAW
is the version in which the target `Y` lives over a *second* base `T`, itself locally of finite
type over `S`, and in which the local homomorphism to be approximated lands in the completed
local ring of the base change `Y_σ = Y ×_{T, σ} Spec 𝒪^∧_{S, s}` along a local
`𝒪_{S, s}`-algebra map `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}`. Its conclusion is a diagram
```
X ← X ×_S V ←—f— W —→ Y ×_{T, τ} V → Y
↓               ↓                     ↓
S ←——————————— V ———τ——————————————→ T
```
together with points `w ∈ W` and `v ∈ V` satisfying the five clauses (1)–(5) of the source.

This file proves the two halves of that conclusion which Tag 0CAU gives:

* the *first stage* — clauses (1) for `(v, τ)`, (2) and (3) — is Tag 0CAU applied to the
  pointed diagram `(S, s) ← (S, s)`, `(T, t) → (S, s)` and the map `σ` itself. The neighbourhood
  `(V, v)` of `(S, s)` which 0CAU produces, the morphism `τ : V ⟶ T` over `S` carrying `v` to
  `t`, and the congruence modulo `𝔪_v ^ N` which 0CAU asserts are literally clauses (1), (2)
  and (3);

* the *second stage* — the remaining part of clause (1), clause (4), and clause (5) in the form
  of a congruence inside `𝒪^∧_{W, w}` — is Tag 0CAU applied to the pointed diagram
  `(Y ×_{T, τ} V, y_τ) → (S, s)`, `(X, x) → (S, s)`, both legs being read over `S` through
  `V ⟶ S`. Here the `W` of the source appears as an elementary étale neighbourhood of
  `(Y ×_{T, τ} V, y_τ)` and the morphism `f : W ⟶ X ×_S V` of the source is recovered from the
  morphism `W ⟶ X` which 0CAU returns together with `W ⟶ Y ×_{T, τ} V ⟶ V`.

Neither stage is registered for Tag 0CAW: the complete statement, under the source's own
hypotheses, is `StacksDraft.ArtinApproximation.exists_relativeMapApproximation` in
`CompletedBaseChangeMapApproximation.lean`.

## Main results

* `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_baseApproximation`: the
  first stage of Tag 0CAW, i.e. clauses (1) for `(v, τ)`, (2) and (3).
* `StacksDraft.ArtinApproximation.exists_elementaryEtaleNeighborhood_relativeApproximation`: the
  second stage of Tag 0CAW, i.e. the rest of clause (1), clause (4), and clause (5) read as a
  congruence in `𝒪^∧_{W, w}`.

## Implementation notes

*Which hypotheses are carried.* Neither theorem carries Theorem 07QZ: it is proved as
`StacksDraft.ArtinApproximation.localApproximationProperty`, so Tags 0CAU and 0CAV
used here are unconditional. The second stage carries one hypothesis beyond the source's, stated
there and discussed below: the local `𝒪_{S, s}`-algebra map
`φ : 𝒪_{X, x} → 𝒪^∧_{Y ×_{T, τ} V, y_τ}`.

*Why that hypothesis is carried.* Tag 0CAW is handed `φ : 𝒪_{X, x} → 𝒪^∧_{Y_σ, y_σ}`, a map
into the completed local ring of the base change along `σ`, whereas the second stage needs a map
into the completed local ring of the base change along `τ`. The source bridges the two with the
canonical isomorphism of `Y_σ` and `Y ×_{T, τ} V` over
`𝒪_{V, v}/𝔪_v ^ N = 𝒪_{S, s}/𝔪_s ^ N`, which is exactly what clauses (2) and (3) of the first
stage make available and which clause (5) of the source invokes as an equality of rings. That
identification *is* constructed, as
`StacksDraft.ArtinApproximation.exists_truncationEquiv_stalk_relativeBaseChange`, but only in the
shape the source's clause (5) uses it: an isomorphism of the two local rings *truncated* at
`𝔪 ^ N`. It therefore does not convert the source's `φ` into a map into
`𝒪^∧_{Y ×_{T, τ} V, (y, v)}`, which is what the hypothesis `φ` below is; no isomorphism of the
*completed* local rings exists to do that. Consequently clause (5) is proved in the equivalent
shape that does not mention it, namely the congruence modulo `𝔪_w ^ N` between `φ` followed by
the map of completions of the étale neighbourhood `W ⟶ Y ×_{T, τ} V` and the map
`𝒪_{X, x} → 𝒪_{W, w}` induced by the morphism `W ⟶ X`. Since `(W, w) → (Y ×_{T, τ} V, y_τ)` is
an *elementary* étale
neighbourhood, `𝒪_{Y ×_{T, τ} V, y_τ}/𝔪^N → 𝒪_{W, w}/𝔪_w ^ N` is an isomorphism, so this
congruence is the source's square with the one bridge removed from both of its sides.

*The point of the base change.* The point `(y, v)` of `Y ×_{T, τ} V` is taken as data, together
with the equation saying it lies over `v`; the source's `y_τ` is such a point. Nothing about `y`
itself enters the second stage, so the first projection of the point is not constrained.

*The identity morphism.* The first stage applies Tag 0CAU with `X := S` and `f := 𝟙 S`. The
coercion of `𝟙 S` to a function is the identity by definition — this is what makes
`AlgebraicGeometry.Scheme.Hom.stalkMap_id` typecheck — so the point hypothesis and the G-ring
hypothesis of 0CAU can be discharged with the hypotheses as given, and only the stalk map of the
identity has to be simplified away.

## References

* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
* [Stacks Project, Tag 0CAU](https://stacks.math.columbia.edu/tag/0CAU)
* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- The transports of stalks along an equality of points of a scheme and along its symmetric are
mutually inverse. This is what moves an identity of maps out of the stalk at one of two equal
points into an identity of maps out of the stalk at the other. -/
private theorem stalkCongr_hom_comp_symm {S : Scheme.{u}} {a b : S} (hab : a = b) :
    (S.presheaf.stalkCongr (.of_eq hab)).hom ≫ (S.presheaf.stalkCongr (.of_eq hab.symm)).hom =
      𝟙 (S.presheaf.stalk a) := by
  cases hab
  simp

/-- **Stacks Project, Tag 0CAW, first stage: clauses (1) for `(v, τ)`, (2) and (3).** Let `S` be
a locally Noetherian scheme, let `h : T ⟶ S` be locally of finite type, let `t ∈ T` lie over
`s ∈ S`, assume `𝒪_{S, s}` is a G-ring, and let `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local
homomorphism of `𝒪_{S, s}`-algebras. Then for every `N ≥ 1` there are an elementary étale
neighbourhood `(V, v)` of `(S, s)` and a morphism `τ : V ⟶ T` over `S` with `τ v = t` such that
the square
```
𝒪^∧_{S, s} ⟶ 𝒪^∧_{V, v}
    ↑σ             ↑
𝒪_{T, t}  —τ^♯—→ 𝒪_{V, v}
```
commutes modulo `𝔪_v ^ N`.

This is Tag 0CAU for the pointed diagram `(S, s) ← (S, s)`, `(T, t) → (S, s)` and the map `σ`:
the source's own proof of 0CAW ends by applying 0CAU "one more time to `Spec C` and `Spec R` over
`Spec R` and the map `C → R^∧`", and that application is this statement. -/
theorem exists_elementaryEtaleNeighborhood_baseApproximation
    {S T : Scheme.{u}} (h : T ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType h]
    (t : T) (s : S) (hts : h t = s)
    (hG : IsGRing (S.presheaf.stalk s))
    (N : ℕ) (hN : 1 ≤ N)
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (hσbase : σ.comp (h.stalkHomAt hts) =
      algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))) :
    ∃ V : EtaleNeighborhood S s, V.IsElementary ∧
      ∃ (τ : V.scheme ⟶ T) (hτ : τ V.point = t), τ ≫ h = V.toBase ∧
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
  have hid : LocallyOfFiniteType (𝟙 S) := inferInstance
  have hxy : (𝟙 S : S ⟶ S) s = h t := hts.symm
  have hbase : σ.comp ((S.presheaf.stalkCongr (.of_eq hxy)).hom ≫ h.stalkMap t).hom =
      (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))).comp
        ((𝟙 S : S ⟶ S).stalkMap s).hom := by
    simp only [Scheme.Hom.stalkMap_id]
    exact hσbase
  obtain ⟨V, hVel, τ, hτ, hover, hcong⟩ :=
    exists_elementaryEtaleNeighborhood_approximation (𝟙 S) h s t hxy hG N hN σ hσ hbase
  refine ⟨V, hVel, τ, hτ, ?_, hcong⟩
  simpa using hover

/-- **Stacks Project, Tag 0CAW, second stage: the rest of clause (1), clause (4), and clause (5)
in the form of a congruence in `𝒪^∧_{W, w}`.** Given the first stage — an elementary étale
neighbourhood `(V, v)` of `(S, s)` and a morphism `τ : V ⟶ T` — a point `y_τ` of
`Y ×_{T, τ} V` lying over `v`, and a local `𝒪_{S, s}`-algebra map
`φ : 𝒪_{X, x} → 𝒪^∧_{Y ×_{T, τ} V, y_τ}`, there are for every `N ≥ 1` an elementary étale
neighbourhood `(W, w)` of `(Y ×_{T, τ} V, y_τ)` and a morphism `F : W ⟶ X` over `S` with
`F w = x`, hence a morphism `W ⟶ X ×_S V` carrying `w` to `(x, v)`, such that `φ` followed by
the map `𝒪^∧_{Y ×_{T, τ} V, y_τ} → 𝒪^∧_{W, w}` agrees modulo `𝔪_w ^ N` with the map
`𝒪_{X, x} → 𝒪_{W, w}` induced by `F`.

This is Tag 0CAU for the pointed diagram `(Y ×_{T, τ} V, y_τ) → (S, s)`, `(X, x) → (S, s)`, the
first leg being read over `S` through `V ⟶ S`. -/
theorem exists_elementaryEtaleNeighborhood_relativeApproximation
    {S T X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ T)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : X) (hG : IsGRing (S.presheaf.stalk (f x)))
    (V : EtaleNeighborhood S (f x)) (τ : V.scheme ⟶ T)
    (yτ : ↥(pullback g τ)) (hyτ : pullback.snd g τ yτ = V.point)
    (N : ℕ) (hN : 1 ≤ N)
    (φ : X.presheaf.stalk x →+*
      AdicCompletion (maximalIdeal ((pullback g τ).presheaf.stalk yτ))
        ((pullback g τ).presheaf.stalk yτ))
    (hφ : IsLocalHom φ)
    (hφbase : φ.comp (f.stalkMap x).hom =
      (algebraMap ((pullback g τ).presheaf.stalk yτ)
          (AdicCompletion (maximalIdeal ((pullback g τ).presheaf.stalk yτ))
            ((pullback g τ).presheaf.stalk yτ))).comp
        (((pullback.snd g τ).stalkHomAt hyτ).comp V.stalkHom)) :
    ∃ W : EtaleNeighborhood (pullback g τ) yτ, W.IsElementary ∧
      ∃ (F : W.scheme ⟶ X) (hF : F W.point = x),
        F ≫ f = W.toBase ≫ pullback.snd g τ ≫ V.toBase ∧
        (∃ fW : W.scheme ⟶ pullback f V.toBase,
          fW ≫ pullback.fst f V.toBase = F ∧
            fW ≫ pullback.snd f V.toBase = W.toBase ≫ pullback.snd g τ) ∧
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
  have hxy : (pullback.snd g τ ≫ V.toBase) yτ = f x := by
    change V.toBase (pullback.snd g τ yτ) = f x
    rw [hyτ, V.map_point]
  have hGp : IsGRing (S.presheaf.stalk ((pullback.snd g τ ≫ V.toBase) yτ)) := by
    rw [hxy]; exact hG
  have hpcomp : (pullback.snd g τ ≫ V.toBase).stalkHomAt hxy =
      ((pullback.snd g τ).stalkHomAt hyτ).comp V.stalkHom :=
    Scheme.Hom.stalkHomAt_comp (pullback.snd g τ) V.toBase hyτ V.map_point
  have hdc : ((S.presheaf.stalkCongr (.of_eq hxy.symm)).hom).hom.comp
      ((S.presheaf.stalkCongr (.of_eq hxy)).hom).hom =
      RingHom.id (S.presheaf.stalk ((pullback.snd g τ ≫ V.toBase) yτ)) := by
    rw [← CommRingCat.hom_comp, stalkCongr_hom_comp_symm hxy, CommRingCat.hom_id]
  have hbase : φ.comp
        (((S.presheaf.stalkCongr (.of_eq hxy)).hom ≫ f.stalkMap x).hom) =
      (algebraMap ((pullback g τ).presheaf.stalk yτ)
          (AdicCompletion (maximalIdeal ((pullback g τ).presheaf.stalk yτ))
            ((pullback g τ).presheaf.stalk yτ))).comp
        ((pullback.snd g τ ≫ V.toBase).stalkMap yτ).hom := by
    rw [CommRingCat.hom_comp, ← RingHom.comp_assoc, hφbase, ← hpcomp,
      show (pullback.snd g τ ≫ V.toBase).stalkHomAt hxy =
          ((pullback.snd g τ ≫ V.toBase).stalkMap yτ).hom.comp
            ((S.presheaf.stalkCongr (.of_eq hxy.symm)).hom).hom from CommRingCat.hom_comp _ _,
      RingHom.comp_assoc, RingHom.comp_assoc, hdc, RingHom.comp_id]
  obtain ⟨W, hWel, F, hF, hover, hcong⟩ :=
    exists_elementaryEtaleNeighborhood_approximation (pullback.snd g τ ≫ V.toBase) f yτ x
      hxy hGp N hN φ hφ hbase
  have hcomm : F ≫ f = (W.toBase ≫ pullback.snd g τ) ≫ V.toBase := by
    rw [hover, Category.assoc]
  exact ⟨W, hWel, F, hF, hover,
    ⟨pullback.lift F (W.toBase ≫ pullback.snd g τ) hcomm, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩, hcong⟩

end StacksDraft.ArtinApproximation

end
