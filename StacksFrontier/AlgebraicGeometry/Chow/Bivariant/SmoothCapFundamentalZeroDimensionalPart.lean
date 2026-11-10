module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalThroughBase
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero

/-!
# Bivariant classes over the zero-dimensional part of a Dedekind base

Let `(S, δ)` be a base as in section 42.63 of the Stacks Project: locally the spectrum of a
Dedekind domain, with `δ = 0` at the closed points and `δ = 1` elsewhere. A field is a Dedekind
domain, so `S` may have points `s` which are closed and have no proper generalization; such a
point is the generic point of a zero-dimensional irreducible component, it has `δ(s) = 0`, and the
set of such points is open. Over an open `V ⊆ S` consisting of such points the identification
`A^p(X → S) = CH_{1-p}(X)` of Stacks 0FC5 fails (`[S]₁` restricts to zero on `V`), and the
correct statement is

  `A^p(X → S) = CH_{-p}(X)`,  `c ↦ c ∩ [V]₀`,

for `X` locally of finite type over `S` with image in `V`. This file proves it, by the source's
proof of Stacks 0FC5 specialised to `V`.

**Injectivity.** By Stacks 02UC a class `c` vanishes as soon as `c ∩ [T] = 0` for every integral
`T` locally of finite type over `S`. If the generic point of `T` lies over a point `s ∈ V`, then
all of `T` lies over the closed point `s`, so `T ⟶ S` factors through `V`; it is flat of relative
dimension `r = δ(T)` over `V` (Stacks 0AUW), so `[T]_r` is the flat pullback of `[V]₀` and the law
of Stacks 0B76 for flat pullback carries `c ∩ [V]₀ = 0` to `c ∩ [T]_r = 0`. Otherwise no point of
`T` lies over `V`, so `X ×_S T` is empty and so is its Chow group.

**Surjectivity.** The image is a subgroup. A class in `CH_{-p}(X)` is that of a locally finite
cycle; separating its positive and negative coefficients it is a difference of two cycles
`∑_j [y_j]`, the points repeated according to the coefficients. For each, the coproduct
`W = ∐_j closure{y_j}` is proper over `X` and flat over `S` of relative dimension `-p`, since all
its points lie over generic points of `S`; the flat pullback class `ξ` of Stacks 0B78 of
`W ⟶ S` caps `[V]₀` to `[W]_{-p}`, and `g_* ∘ ξ` (Stacks 0EPK) is sent to `g_*[W]_{-p}`, which is
`∑_j [y_j]`.

Finally, for `X ⟶ S` flat of relative dimension `e` with image in `V`, the map
`c ↦ c ∩ [X]_e` on `A^p(X)` factors as `c ↦ c ∘ g^*` followed by `c' ↦ c' ∩ [V]₀`, which gives
the isomorphism of Stacks 0FCB over the zero-dimensional part of the base once Stacks 0FBT is
known.

## Main definitions

* `Stacks.Chow.bivariantCapOpenFundamentalClass` — for an open `V` of the base containing the
  image of `X`, the map `A^p(X → S) → CH_{m-p}(X)`, `c ↦ c ∩ [V]_m`.

## Main results

* `IsDedekindChowBase.bivariantCapOpenFundamentalClass_bijective` — over an open `V`
  of zero-dimensional components of a base as in section 42.63, `c ↦ c ∩ [V]₀` is an
  identification `A^p(X → S) = CH_{-p}(X)`.
* `IsDedekindChowBase.chowCohomologyCapFundamentalClass_eq_bivariantCapOpenFundamentalClass`
  — the map `c ↦ c ∩ [X]_e` of Stacks 0FCB factors through `c ↦ c ∘ g^*`.
* `IsDedekindChowBase.chowCohomologyCapFundamentalClass_bijective_of_forall_mem_zeroDimensional`
  — Stacks 0FCB over the zero-dimensional part, from Stacks 0FBT.

## Implementation notes

The cap product is taken at the test scheme `V ⟶ S` itself, with the fundamental class
`[V]₀ ∈ CH₀(V)`, rather than at `S` with `[S]₀`: the base has delta-dimension one as soon as it
has a component of dimension one, and the flat pullback of a fundamental class is a fundamental
class only below the delta-dimension of the target. The cap product lands on `X ×_S V`, which is
carried to `X` by the first projection, an isomorphism because `X ⟶ S` factors through the
monomorphism `V ⟶ S`.

## References

* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FCB](https://stacks.math.columbia.edu/tag/0FCB)
* [Stacks Project, Tag 0FBT](https://stacks.math.columbia.edu/tag/0FBT)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-- If the image of `f : X ⟶ S` lies in an open `V` of `S`, the first projection
`X ×_S V ⟶ X` is an isomorphism: `f` factors through the monomorphism `V ⟶ S`. -/
theorem AlgebraicGeometry.Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem {X S : Scheme.{u}}
    (f : X ⟶ S) (V : S.Opens) (hf : ∀ x : X, f.base x ∈ V) : IsIso (pullback.fst f V.ι) := by
  set l : X ⟶ (V : Scheme.{u}) := IsOpenImmersion.lift V.ι f (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨_, hf x⟩, rfl⟩) with hldef
  have hl : l ≫ V.ι = f := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨pullback.lift (𝟙 X) l (by rw [Category.id_comp, hl]), ?_, pullback.lift_fst _ _ _⟩⟩
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, pullback.lift_snd_assoc, hl,
      Category.id_comp, pullback.condition]

namespace Stacks.Chow

/-! ### The canonical map `c ↦ c ∩ [V]_m` -/

section OpenFundamentalClass

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (V : C.S.Opens) (hX : ∀ x : X, sX.base x ∈ V)

/-- For an open `V` of the base containing the image of `X`, the map
`A^p(X → S) → CH_{m-p}(X)` sending a bivariant class `c` to `c ∩ [V]_m`.

The cap product is taken at the test scheme `V ⟶ S` and lands on `X ×_S V`; it is carried to
`X` by pushforward along the first projection, an isomorphism
(`AlgebraicGeometry.Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem`). For `V` an open of
zero-dimensional components of a base as in section 42.63 and `m = 0` it is bijective,
`Stacks.Chow.IsDedekindChowBase.bivariantCapOpenFundamentalClass_bijective`. -/
def bivariantCapOpenFundamentalClass (m p : ℤ) :
    BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p →+ chowGroup C sX (m - p) :=
  haveI := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem sX V hX
  AddMonoidHom.mk'
    (fun c ↦ chowPushforwardOfIso C (pullback.fst sX V.ι ≫ sX) sX (pullback.fst sX V.ι) rfl
      (m - p) (c.cap V.ι m (fundamentalChowClass C (V.ι ≫ 𝟙 C.S) m)))
    (fun c d ↦ by rw [BivariantClass.add_cap, map_add])

/-- The defining formula of `Stacks.Chow.bivariantCapOpenFundamentalClass`: the pushforward along
`X ×_S V ⟶ X` of the cap product of the class with `[V]_m`. -/
theorem bivariantCapOpenFundamentalClass_apply (m p : ℤ)
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    haveI := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem sX V hX
    bivariantCapOpenFundamentalClass C G sX V hX m p c =
      chowPushforwardOfIso C (pullback.fst sX V.ι ≫ sX) sX (pullback.fst sX V.ι) rfl (m - p)
        (c.cap V.ι m (fundamentalChowClass C (V.ι ≫ 𝟙 C.S) m)) :=
  rfl

/-- `c ↦ c ∩ [V]_m` commutes with proper pushforward: for `g : W ⟶ X` proper and
`ξ ∈ A^p(W → S)`, the class `g_* ∘ ξ ∈ A^p(X → S)` of Stacks 0EPK is sent to
`g_*(ξ ∩ [V]_m)`. -/
theorem bivariantCapOpenFundamentalClass_bivariantProperPushforward {W : Scheme.{u}}
    (g : W ⟶ X) [IsProper g] [LocallyOfFiniteType (g ≫ sX)] (m p : ℤ)
    (ξ : BivariantClass C (gysinSystemOfInvertible C) (g ≫ sX) (𝟙 C.S) (g ≫ sX)
      (Category.comp_id _) p) :
    bivariantCapOpenFundamentalClass C (gysinSystemOfInvertible C) sX V hX m p
        (bivariantProperPushforwardOfInvertible C (g ≫ sX) sX (𝟙 C.S) g sX rfl
          (Category.comp_id sX) p ξ) =
      properChowPushforward C (g ≫ sX) sX g rfl (m - p) (properPushforwardDescends C _ _ g rfl _)
        (bivariantCapOpenFundamentalClass C (gysinSystemOfInvertible C) (g ≫ sX) V
          (fun w ↦ hX (g.base w)) m p ξ) := by
  have := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem sX V hX
  have := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem (g ≫ sX) V (fun w ↦ hX (g.base w))
  exact properChowPushforward_comp_eq C _ _ _ _ (bivariantPushforwardBaseChange g sX V.ι)
    (pullback.fst sX V.ι) (pullback.fst (g ≫ sX) V.ι) g
    (bivariantPushforwardBaseChange_fst g sX V.ι) _ rfl rfl rfl (m - p)
    (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (properPushforwardDescends C _ _ g rfl _) _

/-- `c ↦ c ∩ [V]_m` sends a class characterized by the rule of Stacks 0B78
(`Stacks.Chow.IsBivariantFlatPullback`) for a structure morphism `X ⟶ S` flat of relative
dimension `r` to the fundamental class `[X]_{m+r}`, as soon as `V` has delta-dimension at most
`m`. -/
theorem bivariantCapOpenFundamentalClass_flatPullbackBivariantClass [Flat sX] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension sX r)
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) (-(r : ℤ)))
    (hc : IsBivariantFlatPullback C G sX (𝟙 C.S) sX (Category.comp_id sX) r hr
      (flatPullbackDescends C) c) (m : ℤ)
    (hdim : schemeDeltaDimension C (V.ι ≫ 𝟙 C.S) ≤ (m : EInt)) :
    bivariantCapOpenFundamentalClass C G sX V hX m (-(r : ℤ)) c =
      fundamentalChowClass C sX (m - -(r : ℤ)) := by
  have := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem sX V hX
  rw [bivariantCapOpenFundamentalClass_apply, hc.cap_fundamentalChowClass V.ι m hdim,
    chowPushforwardOfIso_fundamentalChowClass]

end OpenFundamentalClass

/-! ### Capping `[X]` through `[V]`: the composite with the smooth pullback class -/

section ThroughOpen

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (V : C.S.Opens) (hX : ∀ x : X, sX.base x ∈ V)

/-- **The computation behind Stacks 0FCB, at an open of the base.** For `c ∈ A^p(X)`,
`g : X ⟶ S` flat of relative dimension `e` with image in an open `V` of delta-dimension at most
`m`, capping the composite `c ∘ g^* ∈ A^{p-e}(X ⟶ S)` with `[V]_m` is capping `c` with
`[X]_{m+e}`:

  `(c ∘ g^*) ∩ [V]_m = c ∩ (g^* ∩ [V]_m) = c ∩ [X]_{m+e}`,

each side read on `X` through the canonical identifications of the fibre products. -/
theorem chowPushforwardOfIso_cap_opens_comp_structureFlatPullbackClass [Flat sX] (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension sX e) (m p : ℤ)
    (hdim : schemeDeltaDimension C (V.ι ≫ 𝟙 C.S) ≤ (m : EInt)) (n : ℤ) (hn : n = m + e)
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    haveI := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem (𝟙 X ≫ sX) V fun x ↦ hX x
    chowPushforwardOfIso C (pullback.fst (𝟙 X ≫ sX) V.ι ≫ sX) sX
        (pullback.fst (𝟙 X ≫ sX) V.ι) rfl (m - (p + -(e : ℤ)))
        ((bivariantCompositeOfInvertible C sX sX (𝟙 C.S) (𝟙 X) sX (Category.id_comp sX)
          (Category.comp_id sX) p (-(e : ℤ)) c
          (smoothShiftFlatPullbackClass C sX (𝟙 C.S) sX (Category.comp_id sX) e he)).cap
          V.ι m (fundamentalChowClass C (V.ι ≫ 𝟙 C.S) m)) ≍
      chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX n p c := by
  subst hn
  have := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem (𝟙 X ≫ sX) V fun x ↦ hX x
  set h : (pullback sX V.ι : Scheme.{u}) ⟶ X := pullback.fst sX V.ι with hh
  have : IsIso h := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem sX V hX
  set k : ℤ := m - -(e : ℤ) with hk
  -- `g^* ∩ [V]_m = [X ×_S V]_k`
  have hstar :
      (smoothShiftFlatPullbackClass C sX (𝟙 C.S) sX (Category.comp_id sX) e he).cap V.ι m
      (fundamentalChowClass C (V.ι ≫ 𝟙 C.S) m) = fundamentalChowClass C (h ≫ sX) k :=
    IsBivariantFlatPullback.cap_fundamentalChowClass
      (hdesc := flatPullbackDescends C)
        (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sX (𝟙 C.S) sX
        (Category.comp_id sX) e he) V.ι m hdim
  -- `h_*[X ×_S V]_k = [X]_k`, and the cap of `c` commutes with `h_*`
  have hpush : chowPushforwardOfIso C (h ≫ sX) (𝟙 X ≫ sX) h (by simp) k
      (fundamentalChowClass C (h ≫ sX) k) = fundamentalChowClass C (𝟙 X ≫ sX) k :=
    chowPushforwardOfIso_fundamentalChowClass C _ _ h _ k
  have hcap := BivariantClass.cap_chowPushforwardOfTestIso C (gysinSystemOfInvertible C) sX sX
    (𝟙 X) (Category.id_comp sX) p c (𝟙 X) h (Category.comp_id h) k
    (fundamentalChowClass C (h ≫ sX) k)
  rw [hpush] at hcap
  -- the left-hand side, unfolded
  have hL : (bivariantCompositeOfInvertible C sX sX (𝟙 C.S) (𝟙 X) sX (Category.id_comp sX)
          (Category.comp_id sX) p (-(e : ℤ)) c
          (smoothShiftFlatPullbackClass C sX (𝟙 C.S) sX (Category.comp_id sX) e he)).cap
          V.ι m (fundamentalChowClass C (V.ι ≫ 𝟙 C.S) m) ≍
      chowPushforwardOfIso C (pullback.fst (𝟙 X) h ≫ sX) (pullback.fst (𝟙 X ≫ sX) V.ι ≫ sX)
        (pullbackRightPullbackFstIso sX V.ι (𝟙 X)).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sX (𝟙 X) sX V.ι) (k - p)
        (c.cap h k (fundamentalChowClass C (h ≫ sX) k)) := by
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    rw [bivariantCompositeCap_apply, hstar]
    rfl
  refine (chowPushforwardOfIso_heq_congr C _ _ _ rfl (by ring) _ _ hL).trans ?_
  rw [chowPushforwardOfIso_comp_apply]
  -- the right-hand side, unfolded
  rw [chowCohomologyCapFundamentalClass_apply, chowGroupSelfUnitCollapse,
    chowGroupEquivOfIso_apply]
  have hR : chowPushforwardOfIso C (pullback.fst (𝟙 X) (𝟙 X) ≫ sX) sX
        (pullback.fst (𝟙 X) (𝟙 X)) rfl (k - p)
        (c.cap (𝟙 X) k (fundamentalChowClass C (𝟙 X ≫ sX) k)) ≍
      chowPushforwardOfIso C (pullback.fst (𝟙 X) (𝟙 X) ≫ sX) sX
        (pullback.fst (𝟙 X) (𝟙 X)) rfl ((m + e) - p)
        (c.cap (𝟙 X) (m + e) (selfFundamentalClass C sX (m + e))) :=
    chowPushforwardOfIso_heq_congr C _ _ _ rfl (by rw [hk]; ring) _ _
      (BivariantClass.cap_heq_congr c (𝟙 X) (by rw [hk]; ring) _ _
        (fundamentalChowClass_heq C _ (by rw [hk]; ring)))
  refine HEq.trans ?_ hR
  rw [hcap, chowPushforwardOfIso_comp_apply]
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ (k - p) _)
  simp only [hh, pullbackBaseChangeOfTestIso_hom_fst, pullbackRightPullbackFstIso_hom_fst]
  all_goals rfl

end ThroughOpen

/-! ### The zero-dimensional part of a base as in section 42.63 -/

namespace IsDedekindChowBase

section ZeroDimensional

variable {C : ChowSituation.{u}} (hS : IsDedekindChowBase C) (V : C.S.Opens)
  (hV : ∀ s ∈ V, IsClosed ({s} : Set C.S) ∧ s ∈ genericPoints C.S)
  {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (hX : ∀ x : X, sX.base x ∈ V)

/-- The dimension function at the image of a point is at most the relative dimension there. -/
private theorem dimensionFunction_apply_le_relativeDimension {X S : Scheme.{u}}
    (δ : DimensionFunction S) (f : X ⟶ S) (x : X) : δ (f.base x) ≤ relativeDimension δ f x :=
  le_add_of_nonneg_right (Int.natCast_nonneg _)

include hS hV in
/-- An open of a base as in section 42.63 consisting of closed points has delta-dimension zero:
the dimension function vanishes at closed points. -/
theorem schemeDeltaDimension_opensι_le_zero :
    schemeDeltaDimension C (V.ι ≫ 𝟙 C.S) ≤ ((0 : ℤ) : EInt) := by
  have h := schemeDeltaDimension_le_of_forall_relativeDimension_le C (V.ι ≫ 𝟙 C.S)
    (𝟙 (V : Scheme.{u})) (k := 0) fun w ↦ by
      rw [relativeDimension_opensι_comp, relativeDimension_id]
      exact (hS.2.1 _ (hV _ w.2).1).le
  simpa using h

include hS hV hX in
/-- **The final paragraph of the proof of Stacks 0FC5, over the zero-dimensional part.** Let `V`
be an open of a base as in section 42.63 consisting of closed points with no proper
generalization, and let `X` lie over `V`. A bivariant class `c ∈ A^p(X → S)` killing `[V]₀`
kills the fundamental class of every integral scheme `T` locally of finite type over the base.

If the generic point of `T` lies over a point `s ∈ V`, all of `T` lies over the closed point `s`,
so `T ⟶ S` factors through `V`, flatly of relative dimension `r = δ(T)`, and `[T]_r` is the flat
pullback of `[V]₀`. Otherwise no point of `T` lies over `V`, so `X ×_S T` is empty. -/
theorem cap_fundamentalChowClass_eq_zero_of_cap_opens {G : GysinSystem C} {p : ℤ}
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : c.cap V.ι 0 (fundamentalChowClass C (V.ι ≫ 𝟙 C.S) 0) = 0)
    {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] [IsIntegral T] (k : ℤ) :
    c.cap g k (fundamentalChowClass C (g ≫ 𝟙 C.S) k) = 0 := by
  set η := genericPoint T with hη
  by_cases hηV : g.base η ∈ V
  · -- `T` lies over a point of `V`, and is flat over `V`
    set s := g.base η with hs
    obtain ⟨hclosed, hgen⟩ := hV s hηV
    have hδs : C.dimensionFunction s = 0 := hS.2.1 s hclosed
    have hrange : ∀ w : T, g.base w = s := by
      intro w
      have h1 := ((genericPoint_spec T).specializes (Set.mem_univ w)).map g.continuous
      have h2 := specializes_iff_mem_closure.mp h1
      rwa [hclosed.closure_eq, Set.mem_singleton_iff] at h2
    have hsub : Set.range g.base ⊆ Set.range V.ι.base := by
      rintro _ ⟨w, rfl⟩
      exact ⟨⟨s, hηV⟩, (hrange w).symm⟩
    set g₀ : T ⟶ (V : Scheme.{u}) := IsOpenImmersion.lift V.ι g hsub with hg₀def
    have hg₀ : g₀ ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
    have hg₀pt : ∀ w, V.ι.base (g₀.base w) = s := fun w ↦ by
      rw [← Scheme.Hom.comp_apply, hg₀, hrange]
    have _ : Flat g := hS.flat_of_mem_genericPoints g hgen
    have _ : Flat (g₀ ≫ V.ι) := by rw [hg₀]; infer_instance
    have _ : Flat g₀ :=
      ((MorphismProperty.hasOfPostcompProperty_iff_le_diagonal (P := @Flat)
        (Q := @IsOpenImmersion)).mpr (fun _ _ f _ ↦ by
          change Flat (pullback.diagonal f); infer_instance)).of_postcomp g₀ V.ι
        inferInstance inferInstance
    have _ : LocallyOfFiniteType (g₀ ≫ V.ι) := by rw [hg₀]; infer_instance
    have _ : LocallyOfFiniteType g₀ := locallyOfFiniteType_of_comp g₀ V.ι
    have hnn : 0 ≤ relativeDimension C.dimensionFunction g η := by
      have := dimensionFunction_apply_le_relativeDimension C.dimensionFunction g η
      rwa [← hs, hδs] at this
    set r := (relativeDimension C.dimensionFunction g η).toNat with hrdef
    have hr : AlgebraicGeometry.RelativeDimension g₀ r := by
      refine relativeDimension_of_flat_of_coheight C g₀ V.ι r fun w ↦ ?_
      have hmax : Order.coheight (g₀.base w) = 0 := by
        refine Order.coheight_eq_zero.mpr fun b hb ↦ le_of_eq ?_
        have hb' : b ⤳ g₀.base w := hb
        have h1 := hb'.map V.ι.continuous
        rw [hg₀pt] at h1
        have h2 := (mem_genericPoints_iff_forall_specializes_eq s).1 hgen _ h1
        exact V.ι.isOpenEmbedding.injective (h2.trans (hg₀pt w).symm)
      rw [hmax, zero_add, hg₀, ← Category.comp_id V.ι, relativeDimension_opensι_comp,
        relativeDimension_id, hg₀pt, hδs, sub_zero]
    -- `c` kills `[T]_r = (T ⟶ V)^*[V]₀`
    have hB := BivariantClass.cap_flatPullbackChow_eq_zero c V.ι g₀ r hr 0 _ hc
    rw [flatPullbackChow_fundamentalChowClass _ _ _ _ _ r _ 0 _
      (schemeDeltaDimension_opensι_le_zero hS V hV)] at hB
    have hrd : relativeDimension C.dimensionFunction (g ≫ 𝟙 C.S) η = 0 + r := by
      rw [Category.comp_id, zero_add, hrdef, Int.toNat_of_nonneg hnn]
    by_cases hk : k = 0 + r
    · subst hk
      exact BivariantClass.cap_fundamentalChowClass_eq_zero_congr C G sX (𝟙 C.S) sX
        (Category.comp_id sX) p c hg₀.symm _ hB
    · rw [fundamentalChowClass_eq_zero_of_ne C (g ≫ 𝟙 C.S) (by rw [hrd]; exact Ne.symm hk),
        map_zero]
  · -- no point of `T` lies over `V`, so `X ×_S T` is empty
    have _ : IsEmpty ↥(pullback sX g) := by
      refine ⟨fun z ↦ hηV ?_⟩
      have hcond : sX.base ((pullback.fst sX g).base z) =
          g.base ((pullback.snd sX g).base z) := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      have hspec : g.base η ⤳ g.base ((pullback.snd sX g).base z) :=
        ((genericPoint_spec T).specializes (Set.mem_univ _)).map g.continuous
      exact hspec.mem_open V.isOpen (hcond ▸ hX _)
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty C _ _) _ 0

include hS hV in
/-- **Injectivity over the zero-dimensional part.** For `V` an open of a base as in section 42.63
consisting of closed points with no proper generalization and `X` lying over `V`, the map
`A^q(X → S) → CH_{-q}(X)`, `c ↦ c ∩ [V]₀`, is injective: by Stacks 02UC a class is zero once it
kills the fundamental class of every integral scheme over the base, and
`Stacks.Chow.IsDedekindChowBase.cap_fundamentalChowClass_eq_zero_of_cap_opens` derives that from
`c ∩ [V]₀ = 0`. -/
theorem bivariantCapOpenFundamentalClass_injective (q : ℤ) :
    Function.Injective
      (bivariantCapOpenFundamentalClass C (gysinSystemOfInvertible C) sX V hX 0 q) := by
  have := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem sX V hX
  intro c d h
  rw [← sub_eq_zero, BivariantClass.eq_zero_iff_capsIntegral_canonical]
  intro T g _ _ k
  refine cap_fundamentalChowClass_eq_zero_of_cap_opens hS V hV sX hX (c - d) ?_ g k
  rw [BivariantClass.sub_cap, sub_eq_zero]
  exact chowPushforwardOfIso_injective C _ _ (pullback.fst sX V.ι) rfl (0 - q) h

include hS hV in
/-- **The generators of `CH_{-q}(X)` reached by `c ↦ c ∩ [V]₀`.** For `V` an open of
zero-dimensional components of a base as in section 42.63 and `X` lying over `V`, the cycle
`∑_j [y_j]` attached to a locally finite family of points of delta-dimension `-q`, possibly with
repetitions, is in the image of `c ↦ c ∩ [V]₀`.

The closures of the `y_j` lie over generic points of the base, so they are flat over it of
relative dimension `-q` (Stacks 0AUW), and so is their coproduct `W`; the flat pullback class of
Stacks 0B78 of `W ⟶ S` caps `[V]₀` to `[W]_{-q}`, and its pushforward along the proper
`W ⟶ X` (Stacks 0EPK) to `∑_j [y_j]`. -/
theorem exists_cycle_mem_range_bivariantCapOpenFundamentalClass (q : ℤ) {J : Type u}
    (y : J → X) (hlf : LocallyFinite fun j ↦ Set.range (integralComponentAt (y j)).subschemeι)
    (hδ : ∀ j, relativeDimension C.dimensionFunction sX (y j) = 0 - q) :
    ∃ P : CycleGroup C sX (0 - q),
      QuotientAddGroup.mk' (rationalEquivalences C sX (0 - q)) P ∈
          (bivariantCapOpenFundamentalClass C (gysinSystemOfInvertible C) sX V hX 0 q).range ∧
        ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ) := by
  by_cases hJ : IsEmpty J
  · refine ⟨0, zero_mem _, fun x ↦ ?_⟩
    rw [Set.eq_empty_of_isEmpty (y ⁻¹' {x}), finsum_mem_empty]
    rfl
  obtain ⟨j₀⟩ := not_isEmpty_iff.mp hJ
  have hδ0 : ∀ j, C.dimensionFunction (sX.base (y j)) = 0 := fun j ↦
    hS.2.1 _ (hV _ (hX (y j))).1
  have hq : q ≤ 0 := by
    have h1 := hδ j₀
    have h2 := dimensionFunction_apply_le_relativeDimension C.dimensionFunction sX (y j₀)
    rw [hδ0] at h2
    omega
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, q = -(r : ℤ) := ⟨(-q).toNat, by omega⟩
  have _ : ∀ j, IsIntegral (integralComponentAt (y j)).subscheme := fun j ↦
    isIntegral_integralComponentAt _
  have hπ : ∀ j, (integralComponentAt (y j)).subschemeι.base
      (genericPoint (integralComponentAt (y j)).subscheme) = y j := fun j ↦
    genericPointOf_integralComponentAt _
  set Zs := fun j ↦ (integralComponentAt (y j)).subscheme with hZs
  set v : ∀ j, Zs j ⟶ X := fun j ↦ (integralComponentAt (y j)).subschemeι with hv
  have _ : IsProper (Sigma.desc v) := isProper_sigmaDesc_of_locallyFinite Zs v hlf
  have hflat : ∀ j, Flat (v j ≫ sX) := fun j ↦ by
    refine hS.flat_of_mem_genericPoints _ ?_
    rw [Scheme.Hom.comp_apply, subschemeι_genericPoint_integralComponentAt]
    exact (hV _ (hX (y j))).2
  have hdesc : Sigma.desc v ≫ sX = Sigma.desc fun j ↦ v j ≫ sX := by
    refine Sigma.hom_ext _ _ fun j ↦ ?_
    simp
  have _ : Flat (Sigma.desc v ≫ sX) := by
    have := hflat
    rw [hdesc]
    infer_instance
  have hr : AlgebraicGeometry.RelativeDimension (Sigma.desc v ≫ sX) r := by
    refine AlgebraicGeometry.RelativeDimension.of_sigmaι_comp Zs _ fun j ↦ ?_
    have _ := hflat j
    have h := hS.relativeDimension_integralComponentAt_comp sX (y j) (hV _ (hX (y j))).2
    have e : (relativeDimension C.dimensionFunction sX (y j) -
        C.dimensionFunction (sX.base (y j))).toNat = r := by
      rw [hδ j, hδ0]
      omega
    rw [e] at h
    exact AlgebraicGeometry.RelativeDimension.of_eq (Sigma.ι_comp_desc_assoc _ _ _).symm h
  set ξ := flatPullbackBivariantClassOfInvertible C (Sigma.desc v ≫ sX) (𝟙 C.S)
    (Sigma.desc v ≫ sX) (Category.comp_id _) r hr with hξdef
  have hξ : bivariantCapOpenFundamentalClass C (gysinSystemOfInvertible C) (Sigma.desc v ≫ sX) V
      (fun w ↦ hX ((Sigma.desc v).base w)) 0 (-(r : ℤ)) ξ =
        fundamentalChowClass C (Sigma.desc v ≫ sX) (0 - -(r : ℤ)) :=
    bivariantCapOpenFundamentalClass_flatPullbackBivariantClass C _ _ V _ r hr ξ
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C (Sigma.desc v ≫ sX)
        (𝟙 C.S) (Sigma.desc v ≫ sX) (Category.comp_id _) r hr) 0
      (schemeDeltaDimension_opensι_le_zero hS V hV)
  refine ⟨properPushforward C _ sX (Sigma.desc v) rfl (0 - -(r : ℤ))
    (fundamentalCycle C _ (0 - -(r : ℤ))), ⟨bivariantProperPushforwardOfInvertible C _ sX (𝟙 C.S)
      (Sigma.desc v) sX rfl (Category.comp_id sX) (-(r : ℤ)) ξ, ?_⟩,
    fun x ↦ properPushforward_fundamentalCycle_sigma_apply C sX Zs v y hπ (0 - -(r : ℤ)) hδ x⟩
  rw [bivariantCapOpenFundamentalClass_bivariantProperPushforward, hξ]
  rfl

include hS hV in
/-- **Surjectivity over the zero-dimensional part.** For `V` an open of zero-dimensional
components of a base as in section 42.63 and `X` lying over `V`, every class in `CH_{-q}(X)` is
`c ∩ [V]₀` for some `c ∈ A^q(X → S)`: the image is a subgroup containing the generators
of `Stacks.Chow.IsDedekindChowBase.exists_cycle_mem_range_bivariantCapOpenFundamentalClass`. -/
theorem bivariantCapOpenFundamentalClass_surjective (q : ℤ) :
    Function.Surjective
      (bivariantCapOpenFundamentalClass C (gysinSystemOfInvertible C) sX V hX 0 q) := by
  have key : ∀ (k : ℤ) (K : AddSubgroup (chowGroup C sX k)),
      (∀ {J : Type u} (y : J → X),
        LocallyFinite (fun j ↦ Set.range (integralComponentAt (y j)).subschemeι) →
        (∀ j, relativeDimension C.dimensionFunction sX (y j) = k) →
        ∃ P : CycleGroup C sX k,
          QuotientAddGroup.mk' (rationalEquivalences C sX k) P ∈ K ∧
            ∀ x, P.1 x = ∑ᶠ j ∈ y ⁻¹' {x}, (1 : ℤ)) →
      ∀ β : chowGroup C sX k, β ∈ K := by
    intro k K hK β
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = 1 - p := ⟨1 - k, by ring⟩
    exact mem_of_forall_cycle_generators_of_partition C sX p K (fun _ ↦ True) (fun _ ↦ False)
      (fun _ ↦ False) (fun _ ↦ by simp) (fun y hlf hδ _ ↦ hK y hlf hδ)
      (fun y hlf hδ _ ↦ hK y hlf hδ) (fun y hlf hδ _ ↦ hK y hlf hδ) β
  intro α
  obtain ⟨c, hc⟩ := key (0 - q) _
    (fun y hlf hδ ↦ exists_cycle_mem_range_bivariantCapOpenFundamentalClass hS V hV sX hX q y hlf
      hδ) α
  exact ⟨c, hc⟩

include hS hV in
/-- **Stacks 0FC5 over the zero-dimensional part of the base.** For `V` an open of a base as in
section 42.63 consisting of closed points with no proper generalization, and `X` locally of
finite type over the base with image in `V`, the map `c ↦ c ∩ [V]₀` is an identification

  `A^q(X → S) = CH_{-q}(X)`. -/
theorem bivariantCapOpenFundamentalClass_bijective (q : ℤ) :
    Function.Bijective
      (bivariantCapOpenFundamentalClass C (gysinSystemOfInvertible C) sX V hX 0 q) :=
  ⟨bivariantCapOpenFundamentalClass_injective hS V hV sX hX q,
    bivariantCapOpenFundamentalClass_surjective hS V hV sX hX q⟩

include hS hV in
/-- **The factorization of the map of Stacks 0FCB over the zero-dimensional part.** For `V` an
open of zero-dimensional components of a base as in section 42.63 and `g : X ⟶ S` flat of
relative dimension `e` with image in `V`, the map `c ↦ c ∩ [X]_e` is the composite of
`c ↦ c ∘ g^*` with `c' ↦ c' ∩ [V]₀`, up to the transport of degrees `0 - (p - e) = e - p`. -/
theorem chowCohomologyCapFundamentalClass_eq_bivariantCapOpenFundamentalClass [Flat sX]
    (e : ℕ) (he : AlgebraicGeometry.RelativeDimension sX e) (p : ℤ)
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p) :
    chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX e p c =
      chowGroupDegreeEquiv C sX (by ring)
        (bivariantCapOpenFundamentalClass C (gysinSystemOfInvertible C) sX V hX 0
          (p + -(e : ℤ)) (compStructureFlatPullbackClass C sX e he p c)) := by
  have := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem sX V hX
  have := Scheme.Opens.isIso_pullback_fst_ι_of_forall_mem (𝟙 X ≫ sX) V fun x ↦ hX x
  refine eq_of_heq (HEq.trans ?_ (chowGroupDegreeEquiv_heq C sX _ _).symm)
  refine HEq.symm (HEq.trans ?_
    (chowPushforwardOfIso_cap_opens_comp_structureFlatPullbackClass C sX V hX e he 0 p
      (schemeDeltaDimension_opensι_le_zero hS V hV) e (by ring) c))
  rw [bivariantCapOpenFundamentalClass_apply, compStructureFlatPullbackClass_apply,
    BivariantClass.congrHom_cap, chowPushforwardOfIso_comp_apply]
  refine heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ _)
  simp

include hS hV hX in
/-- **Stacks 0FCB over the zero-dimensional part, from Stacks 0FBT.** For `V` an open of
zero-dimensional components of a base as in section 42.63 and `g : X ⟶ S` flat of relative
dimension `e` with image in `V`, the map `c ↦ c ∩ [X]_e`, `A^p(X) ⟶ CH_{e-p}(X)`, is bijective as
soon as `c ↦ c ∘ g^*` is (Stacks 0FBT, for `g` smooth): it is the composite of that map with the
bijection `Stacks.Chow.IsDedekindChowBase.bivariantCapOpenFundamentalClass_bijective`. -/
theorem chowCohomologyCapFundamentalClass_bijective_of_forall_mem_zeroDimensional [Flat sX]
    (e : ℕ) (he : AlgebraicGeometry.RelativeDimension sX e) (p : ℤ)
    (hT : Function.Bijective (compStructureFlatPullbackClass C sX e he p)) :
    Function.Bijective
      (chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX e p) := by
  have hfun : ⇑(chowCohomologyCapFundamentalClass C (gysinSystemOfInvertible C) sX e p) =
      (chowGroupDegreeEquiv C sX (by ring)) ∘
        (bivariantCapOpenFundamentalClass C (gysinSystemOfInvertible C) sX V hX 0
          (p + -(e : ℤ))) ∘
          (compStructureFlatPullbackClass C sX e he p) :=
    funext (chowCohomologyCapFundamentalClass_eq_bivariantCapOpenFundamentalClass hS V hV sX hX
      e he p)
  rw [hfun]
  exact (chowGroupDegreeEquiv C sX _).bijective.comp
    ((bivariantCapOpenFundamentalClass_bijective hS V hV sX hX _).comp hT)

end ZeroDimensional

end IsDedekindChowBase

end Stacks.Chow

end
