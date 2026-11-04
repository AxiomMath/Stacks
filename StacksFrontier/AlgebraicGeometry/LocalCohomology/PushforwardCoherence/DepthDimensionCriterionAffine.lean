module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.AffineOpens
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.CodimAffineOpen
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthDimensionCriterionPoints
public import StacksFrontier.RingTheory.LocalCohomology.CutoffCompletionSerreTransport

/-!
# The depth–dimension criterion along an open immersion into an affine scheme

Let `T` be an affine locally Noetherian universally catenary scheme, let `g : W ⟶ T` be an open
immersion and let `ℱ` be a coherent `𝒪_W`-module. Assume Serre's condition `(Sₙ)` on the formal
fibres of `𝒪_{T,z}` for every point `z` outside the image of `g`. This file proves that
`R^p g_* ℱ` is coherent for every `0 ≤ p < n` if and only if

  `depth_{𝒪_{W,x}}(ℱ_x) + codim(closure {z}, closure {g(x)}) > n`

for every `x ∈ Supp(ℱ)` and every `z ∉ g(W)` lying in the closure of `{g(x)}`.

This is `forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_opens` moved off the
spectrum: no ring, no ideal and no prime appears in the statement, and the base is an arbitrary
affine scheme rather than a `Spec`. It is the form in which the global case of [Stacks, Tag 0BJY]
applies the criterion at an affine open of a locally Noetherian scheme.

## Main results

* `forall_lt_depth_add_topCodim_transport_iff` — the depth–dimension condition is carried by a
  commuting square of isomorphisms of the source and the target.
* `forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_affine` — **the criterion
  along an open immersion into an affine scheme.**

## Implementation notes

The passage from an affine `T` to `Spec Γ(T, ⊤)` is `AlgebraicGeometry.Scheme.isoSpec` on the
target and `AlgebraicGeometry.Scheme.Hom.isoOpensRange` on the source, exactly as in
`Stacks.LocalCohomologySequence.isCoherent_rightDerived_of_isFiniteLocallyFree_affine` and in
`AlgebraicGeometry.exists_ideal_finiteModule_isCoherent_rightDerived_iff_affine`: the source open
is then the range of `g ≫ T.isoSpec.hom`, so no description of it is needed, and the square the
two isomorphisms form commutes by `AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι`. The
coherence of the higher direct images crosses that square by
`Stacks.AlgebraicGeometry.DerivedPushforward.isCoherent_rightDerived_transport_iff`; the
depth–dimension condition crosses it by `forall_lt_depth_add_topCodim_transport_iff`, whose four
terms move one by one:

* the **support**, by `AlgebraicGeometry.Scheme.Modules.mem_supp_pushforward_iso_iff`;
* the **depth**, by `AlgebraicGeometry.Scheme.Modules.depth_stalk_pushforward_eq`;
* the **codimension**, by
  `IrreducibleClosedsCodim.topCodim_closureSingleton_map_isOpenEmbedding`, an isomorphism of
  schemes being an open embedding on points;
* the two **memberships**, by injectivity of that embedding and by
  `Topology.IsInducing.specializes_iff` through `specializes_iff_mem_closure`.

The transport lemma asks nothing of `g` and `g'` beyond the commuting square — not even that they
be open immersions — because the condition reads only their underlying maps and the stalks of the
module.

**The formal-fibres hypothesis is not routed through an affine open.**
`AlgebraicGeometry.formalFibersHavePropertySk_stalk_iff_primeIdealOf` identifies the condition at
a point of an affine open `V` of a scheme with the condition at a prime of `Γ(X, V)`; at `V = ⊤`
of `Spec A` the ring it produces is `Γ(Spec A, ⊤)` and **not** `A`, so it does not answer the
question asked here. The stalk of `Spec A` at a prime `q` is instead identified with
`Localization.AtPrime q` by Mathlib's `AlgebraicGeometry.Spec.stalkIso` directly, and the stalk of
`T` at the corresponding point by `AlgebraicGeometry.Scheme.Hom.stalkMap` of `T.isoSpec.inv`,
which is an isomorphism because an isomorphism of schemes is an open immersion. The point of `T`
is taken to be `T.isoSpec.inv q` precisely so that no equality of points has to be rewritten
inside a stalk.

## References

* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace
open TopologicalSpace.IrreducibleCloseds (closureSingleton)
open IrreducibleClosedsCodim (topCodim topCodim_closureSingleton_map_isOpenEmbedding)
open Stacks.AlgebraicGeometry.DerivedPushforward (isCoherent_rightDerived_transport_iff)
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent (isCoherent_pushforward_of_isFinite)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

/-! ### The depth–dimension condition across a square of isomorphisms -/

/-- **The depth–dimension condition of [Stacks, Tag 0BJY] is carried by a commuting square of
isomorphisms.** Let `a : W ≅ W'` and `b : T ≅ T'` be isomorphisms of schemes with
`a.hom ≫ g' = g ≫ b.hom`, and let `ℱ` be an `𝒪_W`-module. Then the condition

  `depth_{𝒪_{W,x}}(ℱ_x) + codim(closure {z}, closure {g(x)}) > n`
  for every `x ∈ Supp(ℱ)` and every `z ∉ g(W)` with `z ∈ closure {g(x)}`

holds for `g` and `ℱ` exactly when it holds for `g'` and `a_*ℱ`.

Nothing is assumed of `g` and `g'`: the condition reads only their underlying maps and the stalks
of the module. The support moves by
`AlgebraicGeometry.Scheme.Modules.mem_supp_pushforward_iso_iff`, the depth by
`AlgebraicGeometry.Scheme.Modules.depth_stalk_pushforward_eq`, the codimension by
`IrreducibleClosedsCodim.topCodim_closureSingleton_map_isOpenEmbedding`, and the two memberships
by injectivity of `b` on points and by `Topology.IsInducing.specializes_iff`. -/
public theorem forall_lt_depth_add_topCodim_transport_iff {W T W' T' : Scheme.{u}}
    (g : W ⟶ T) (g' : W' ⟶ T') (a : W ≅ W') (b : T ≅ T') (h : a.hom ≫ g' = g ≫ b.hom)
    (F : W.Modules) (n : ℕ) :
    (∀ x : W, x ∈ SheafOfModules.supp F →
        ∀ z : T, z ∉ Set.range g.base → z ∈ closure ({g.base x} : Set T) →
          (n : ℕ∞) <
            Module.depth (W.presheaf.stalk x) (IsLocalRing.maximalIdeal (W.presheaf.stalk x))
                (F.presheaf.stalk x) +
              topCodim (closureSingleton z) (closureSingleton (g.base x))) ↔
      ∀ y : W', y ∈ SheafOfModules.supp ((Scheme.Modules.pushforward a.hom).obj F) →
        ∀ w : T', w ∉ Set.range g'.base → w ∈ closure ({g'.base y} : Set T') →
          (n : ℕ∞) <
            Module.depth (W'.presheaf.stalk y) (IsLocalRing.maximalIdeal (W'.presheaf.stalk y))
                (((Scheme.Modules.pushforward a.hom).obj F).presheaf.stalk y) +
              topCodim (closureSingleton w) (closureSingleton (g'.base y)) := by
  have hemb : IsOpenEmbedding b.hom.base := (Scheme.homeoOfIso b).isOpenEmbedding
  have hbase : ∀ x : W, g'.base (a.hom.base x) = b.hom.base (g.base x) := fun x => by
    have h1 : (a.hom ≫ g').base x = (g ≫ b.hom).base x := by rw [h]
    exact h1
  have hclos : ∀ y z : T, (b.hom.base z ∈ closure ({b.hom.base y} : Set T') ↔
      z ∈ closure ({y} : Set T)) := by
    intro y z
    rw [← specializes_iff_mem_closure, ← specializes_iff_mem_closure]
    exact hemb.isInducing.specializes_iff
  have hrange : ∀ z : T, (b.hom.base z ∈ Set.range g'.base ↔ z ∈ Set.range g.base) := by
    intro z
    refine ⟨fun hz => ?_, fun hz => ?_⟩
    · obtain ⟨y, hy⟩ := hz
      refine ⟨a.inv.base y, hemb.injective ?_⟩
      rw [← hbase (a.inv.base y), Scheme.inv_hom_apply a y, hy]
    · obtain ⟨x, hx⟩ := hz
      exact ⟨a.hom.base x, by rw [hbase x, hx]⟩
  refine ⟨fun hcond y hy w hw hwy => ?_, fun hcond x hx z hz hzx => ?_⟩
  · obtain ⟨x, rfl⟩ : ∃ x : W, a.hom.base x = y := ⟨a.inv.base y, Scheme.inv_hom_apply a y⟩
    obtain ⟨z, rfl⟩ : ∃ z : T, b.hom.base z = w := ⟨b.inv.base w, Scheme.inv_hom_apply b w⟩
    rw [hbase x] at hwy
    rw [Scheme.Modules.depth_stalk_pushforward_eq a F x, hbase x,
      topCodim_closureSingleton_map_isOpenEmbedding hemb z (g.base x)]
    exact hcond x ((Scheme.Modules.mem_supp_pushforward_iso_iff a F x).mp hy) z
      (fun hc => hw ((hrange z).mpr hc)) ((hclos (g.base x) z).mp hwy)
  · have key := hcond (a.hom.base x)
      ((Scheme.Modules.mem_supp_pushforward_iso_iff a F x).mpr hx) (b.hom.base z)
      (fun hc => hz ((hrange z).mp hc)) (by rw [hbase x]; exact (hclos (g.base x) z).mpr hzx)
    rw [Scheme.Modules.depth_stalk_pushforward_eq a F x, hbase x,
      topCodim_closureSingleton_map_isOpenEmbedding hemb z (g.base x)] at key
    exact key

/-! ### Along an open immersion into an affine scheme -/

/-- **[Stacks, Tag 0BJY] along an open immersion into an affine scheme.** Let `T` be an affine
locally Noetherian universally catenary scheme, let `g : W ⟶ T` be an open immersion, let `ℱ` be
a coherent `𝒪_W`-module and let `n` be a natural number. Assume the formal fibres of `𝒪_{T,z}`
satisfy Serre's condition `(Sₙ)` for every point `z` outside the image of `g`. Then `R^p g_* ℱ`
is coherent for every `0 ≤ p < n` if and only if

  `depth_{𝒪_{W,x}}(ℱ_x) + codim(closure {z}, closure {g(x)}) > n`

for every `x ∈ Supp(ℱ)` and every `z ∉ g(W)` lying in the closure of `{g(x)}`.

No ring, ideal or prime occurs in the statement. It is
`forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_opens` transported along
`AlgebraicGeometry.Scheme.isoSpec` and `AlgebraicGeometry.Scheme.Hom.isoOpensRange`: the
coherence side by
`Stacks.AlgebraicGeometry.DerivedPushforward.isCoherent_rightDerived_transport_iff` and the
depth–dimension side by `forall_lt_depth_add_topCodim_transport_iff`. The ring of sections is
universally catenary by `AlgebraicGeometry.isUniversallyCatenary_sections_of_affineOpen`, and the
formal fibres at a prime `q` outside the open are those of `𝒪_{T, T.isoSpec.inv q}` by
`AlgebraicGeometry.Spec.stalkIso` and the stalk map of `T.isoSpec.inv`. -/
public theorem forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_affine
    {W T : Scheme.{u}} [IsAffine T] [IsLocallyNoetherian T] (g : W ⟶ T) [IsOpenImmersion g]
    (F : W.Modules) [F.IsCoherent] (n : ℕ) (hT : Scheme.IsUniversallyCatenary T)
    (hformal : ∀ z : T, z ∉ Set.range g.base →
      Stacks.LocalCohomology.FormalFibersHavePropertySk (T.presheaf.stalk z) n) :
    (∀ x : W, x ∈ SheafOfModules.supp F →
        ∀ z : T, z ∉ Set.range g.base → z ∈ closure ({g.base x} : Set T) →
          (n : ℕ∞) <
            Module.depth (W.presheaf.stalk x) (IsLocalRing.maximalIdeal (W.presheaf.stalk x))
                (F.presheaf.stalk x) +
              topCodim (closureSingleton z) (closureSingleton (g.base x))) ↔
      ∀ p : ℕ, p < n →
        (((Scheme.Modules.pushforward g).rightDerived p).obj F).IsCoherent := by
  have hNoeth : IsNoetherianRing Γ(T, (⊤ : T.Opens)) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  have hA : Ring.IsUniversallyCatenary (ToType Γ(T, (⊤ : T.Opens))) :=
    isUniversallyCatenary_sections_of_affineOpen hT ⟨⊤, isAffineOpen_top T⟩
  have hGcoh : ((Scheme.Modules.pushforward
      (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)).hom).obj F).IsCoherent :=
    isCoherent_pushforward_of_isFinite (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)).hom F
  have := hGcoh
  -- Serre's condition at a point of `Spec Γ(T, ⊤)`, read at `T`
  have hstalkT : ∀ x : Spec Γ(T, (⊤ : T.Opens)),
      (Stacks.LocalCohomology.FormalFibersHavePropertySk
          (T.presheaf.stalk (T.isoSpec.inv.base x)) n ↔
        Stacks.LocalCohomology.FormalFibersHavePropertySk
          ((Spec Γ(T, (⊤ : T.Opens))).presheaf.stalk x) n) := fun x =>
    Stacks.LocalCohomology.formalFibersHavePropertySk_iff_of_ringEquiv
      (asIso (T.isoSpec.inv.stalkMap x)).commRingCatIsoToRingEquiv n
  -- and at a prime, the point and the prime being passed separately
  have hstalkSpec : ∀ (x : Spec Γ(T, (⊤ : T.Opens)))
      (p : PrimeSpectrum (ToType Γ(T, (⊤ : T.Opens)))),
      (p : Spec Γ(T, (⊤ : T.Opens))) = x →
      (Stacks.LocalCohomology.FormalFibersHavePropertySk
          ((Spec Γ(T, (⊤ : T.Opens))).presheaf.stalk x) n ↔
        Stacks.LocalCohomology.FormalFibersHavePropertySk
          (Localization.AtPrime p.asIdeal) n) := by
    intro x p hp
    let : IsLocalRing ((Spec Γ(T, (⊤ : T.Opens))).presheaf.stalk x) := inferInstance
    subst hp
    exact Stacks.LocalCohomology.formalFibersHavePropertySk_iff_of_ringEquiv
      (Spec.stalkIso Γ(T, (⊤ : T.Opens)) p).commRingCatIsoToRingEquiv n
  have hformal' : ∀ q : PrimeSpectrum (ToType Γ(T, (⊤ : T.Opens))),
      (q : Spec Γ(T, (⊤ : T.Opens))) ∉ Scheme.Hom.opensRange (g ≫ T.isoSpec.hom) →
      Stacks.LocalCohomology.FormalFibersHavePropertySk (Localization.AtPrime q.asIdeal) n := by
    intro q hq
    have hz : T.isoSpec.inv.base (q : Spec Γ(T, (⊤ : T.Opens))) ∉ Set.range g.base := by
      rintro ⟨w, hw⟩
      refine hq (Scheme.Hom.mem_opensRange.mpr ⟨w, ?_⟩)
      have h1 : T.isoSpec.hom.base (g.base w) = (q : Spec Γ(T, (⊤ : T.Opens))) := by
        rw [hw]
        exact Scheme.inv_hom_apply T.isoSpec _
      exact h1
    exact (hstalkSpec (q : Spec Γ(T, (⊤ : T.Opens))) q rfl).mp
      ((hstalkT (q : Spec Γ(T, (⊤ : T.Opens)))).mp (hformal _ hz))
  refine Iff.trans (forall_lt_depth_add_topCodim_transport_iff g
      (Scheme.Hom.opensRange (g ≫ T.isoSpec.hom)).ι
      (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)) T.isoSpec
      (Scheme.Hom.isoOpensRange_hom_ι (g ≫ T.isoSpec.hom)) F n) ?_
  refine Iff.trans ?_ (forall_congr' fun p => imp_congr_right fun _ =>
    (isCoherent_rightDerived_transport_iff g (Scheme.Hom.opensRange (g ≫ T.isoSpec.hom)).ι
      (Scheme.Hom.isoOpensRange (g ≫ T.isoSpec.hom)) T.isoSpec
      (Scheme.Hom.isoOpensRange_hom_ι (g ≫ T.isoSpec.hom)) p F).symm)
  refine Iff.trans ?_ (forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_opens
    (Scheme.Hom.opensRange (g ≫ T.isoSpec.hom)) _ hA n hformal')
  refine forall_congr' fun y => imp_congr_right fun _ => forall_congr' fun w => ?_
  rw [Scheme.Opens.range_ι]
  exact Iff.rfl

end Stacks.LocalCohomologySequence

end
