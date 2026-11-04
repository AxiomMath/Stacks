module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsAffineSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsComparison

/-!
# The presheaf of divided power differentials already has the sheaf's sections on an affine open

Let `(T, J, δ)` be a divided power scheme and `f : T ⟶ Y` a morphism of schemes.  The sheaf
`Ω_{T/Y,δ}` of divided power differentials is by definition the sheafification of the presheaf
`Crystalline.dpDifferentialsPresheaf`, whose sections over an open `W` are the divided power
differentials of `Γ(W, 𝒪_T)` over the *global* sections of `Y` modulo the differentials of every
section pulled back from *some* open of `Y`.  This module shows that on an affine open `W` lying
over an affine open `V` of `Y` the comparison `Crystalline.dpDifferentialsToSheaf` between the
two is bijective: nothing is lost or gained by sheafifying there.

The proof does not touch sheafification.  By [Stacks, Tag 07IY] clause (2) —
`Crystalline.affineSectionsEquiv` — the sheaf's sections over such a `W` are the ring-theoretic
divided power differentials `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}`, and the comparison carries the universal
divided power derivation to the universal divided power differential.  The presheaf's sections
carry a derivation over `Γ(V, 𝒪_Y)` too — the sections pulled back from `V` are among the
sections pulled back from some open, so their differentials are already killed — and it obeys the
divided power chain rule, so the universal property of `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}` produces a map
back.  The two composites are the identity on the universal differentials, which generate.

## Main definitions

* `Crystalline.affineSheafComparison` — the comparison with the sheaf followed by
  `Crystalline.affineSectionsEquiv`, a map from the presheaf's sections over `W` to
  `Ω¹_{Γ(W,𝒪_T)/Γ(V,𝒪_Y),δ}`.

## Main results

* `Crystalline.dpDifferentials_span` — the module of divided power differentials of a ring map is
  spanned by the universal differentials.
* `Crystalline.affineSheafComparison_d` and `Crystalline.affineDpInv_dpd` — the two maps
  match the two universal differentials.
* `Crystalline.bijective_dpDifferentialsToSheaf_app` — **the comparison of the presheaf of
  divided power differentials with the sheaf it generates is bijective on an affine open lying
  over an affine open of the base.**

## Implementation notes

The two composites are shown to be the identity by induction over a spanning set rather than by
an extensionality lemma for morphisms of `ModuleCat`.  The reason is the one recorded in
`StacksFrontier/AlgebraicGeometry/Crystalline/DifferentialsAffineSections.lean`:
`Crystalline.affineSectionsEquiv` is a linear equivalence over `Γ(W, 𝒪_T)`, while the sections of
a presheaf of modules are indexed by the structure sheaf in its `RingCat`-valued form, so a
composite of the two does not elaborate as a morphism of `ModuleCat`.  As a map of types it
composes without trouble, and additivity and `Γ(W, 𝒪_T)`-linearity of each factor are available
separately.

## References

* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07IW](https://stacks.math.columbia.edu/tag/07IW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-! ### The divided power differentials of a ring map are spanned by the universal ones -/

section Span

variable {A B : CommRingCat.{u}} {J : Ideal B}

/-- **The module of divided power differentials of a morphism of commutative rings is spanned by
the universal divided power differentials.**  The quotient by the span receives the zero map, by
the extensionality lemma for maps out of the divided power differentials. -/
theorem dpDifferentials_span (f : A ⟶ B) (hJ : DividedPowers J) :
    Submodule.span B (Set.range (dpd (f := f) hJ)) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x ↦ ?_
  set N := Submodule.span B (Set.range (dpd (f := f) hJ)) with hN
  suffices h : N.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero N).mp h
  have hz : (ModuleCat.ofHom N.mkQ :
      dpDifferentials f hJ ⟶ ModuleCat.of B (↥(dpDifferentials f hJ) ⧸ N)) = 0 := by
    refine dpDifferentials_ext fun b ↦ ?_
    exact (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨b, rfl⟩)
  exact congrArg (fun φ : dpDifferentials f hJ ⟶
    ModuleCat.of B (↥(dpDifferentials f hJ) ⧸ N) ↦ φ x) hz

end Span

/-! ### The comparison on an affine open over an affine open -/

section Affine

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)
  {W : T.scheme.Opens} (hW : IsAffineOpen W) {V : Y.Opens} (h : W ≤ f ⁻¹ᵁ V)
  (hV : IsAffineOpen V)

include hW hV in
/-- **The comparison of the presheaf of divided power differentials with the sheaf it generates,
followed by the identification of [Stacks, Tag 07IY] of the sheaf's sections over an affine open
with the divided power differentials of the rings.** -/
def affineSheafComparison :
    ↥((dpDifferentialsPresheaf T Y f).obj (op W)) →
      ↥(dpDifferentials (f.appLE V W h) (T.dividedPowers.dividedPowers (op W))) :=
  fun x ↦ affineSectionsEquiv T Y f hW h hV ((dpDifferentialsToSheaf T Y f).app (op W) x)

include hW hV in
/-- The comparison carries the universal differential of the presheaf to the universal divided
power differential of the rings. -/
theorem affineSheafComparison_d (b : Γ(T.scheme, W)) :
    affineSheafComparison T Y f hW h hV ((presheafD T Y f W).d b) =
      dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)) b :=
  affineSectionsEquiv_apply T Y f hW h hV b

/-- The comparison preserves zero. -/
private theorem affineSheafComparison_zero :
    affineSheafComparison T Y f hW h hV 0 = 0 :=
  (congrArg (affineSectionsEquiv T Y f hW h hV)
    (map_zero ((dpDifferentialsToSheaf T Y f).app (op W)).hom)).trans
    (map_zero (affineSectionsEquiv T Y f hW h hV))

include hW hV in
/-- The comparison is additive. -/
theorem affineSheafComparison_add (x y : ↥((dpDifferentialsPresheaf T Y f).obj (op W))) :
    affineSheafComparison T Y f hW h hV (x + y) =
      affineSheafComparison T Y f hW h hV x + affineSheafComparison T Y f hW h hV y := by
  refine (congrArg (affineSectionsEquiv T Y f hW h hV)
    (map_add ((dpDifferentialsToSheaf T Y f).app (op W)).hom x y)).trans ?_
  exact map_add (affineSectionsEquiv T Y f hW h hV) _ _

include hW hV in
/-- The comparison is linear over the sections of `𝒪_T`. -/
theorem affineSheafComparison_smul (r : Γ(T.scheme, W))
    (x : ↥((dpDifferentialsPresheaf T Y f).obj (op W))) :
    affineSheafComparison T Y f hW h hV (r • x) =
      r • affineSheafComparison T Y f hW h hV x := by
  refine (congrArg (affineSectionsEquiv T Y f hW h hV)
    (map_smul ((dpDifferentialsToSheaf T Y f).app (op W)).hom r x)).trans ?_
  exact map_smul (affineSectionsEquiv T Y f hW h hV) r _

include hW hV in
/-- **The map back is a left inverse of the comparison.**  Both composites are the identity on the
universal differentials of the presheaf, which span its sections over `W`. -/
theorem affinePresheafOfSheaf_affineSheafComparison
    (x : ↥((dpDifferentialsPresheaf T Y f).obj (op W))) :
    (affineDpInv T Y f h).hom (affineSheafComparison T Y f hW h hV x) = x := by
  have hx : x ∈ Submodule.span Γ(T.scheme, W) (Set.range (presheafD T Y f W).d) :=
    (dpConstDifferentials_span (baseAppLE T Y f W) (T.dividedPowers.dividedPowers (op W))
      (baseSections T Y f W)).ge Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact (congrArg (affineDpInv T Y f h).hom
        (affineSheafComparison_d T Y f hW h hV b)).trans
        (affineDpInv_dpd T Y f h b)
  | zero =>
      rw [affineSheafComparison_zero T Y f hW h hV, map_zero]
  | add a b _ _ ha hb =>
      rw [affineSheafComparison_add T Y f hW h hV, map_add, ha, hb]
  | smul r a _ ha =>
      rw [affineSheafComparison_smul T Y f hW h hV, map_smul, ha]

include hW hV in
/-- **The map back is a right inverse of the comparison.**  Both composites are the identity on
the universal divided power differentials of the rings, which span. -/
theorem affineSheafComparison_affinePresheafOfSheaf
    (x : ↥(dpDifferentials (f.appLE V W h) (T.dividedPowers.dividedPowers (op W)))) :
    affineSheafComparison T Y f hW h hV ((affineDpInv T Y f h).hom x) = x := by
  have hx : x ∈ Submodule.span Γ(T.scheme, W)
      (Set.range (dpd (f := f.appLE V W h) (T.dividedPowers.dividedPowers (op W)))) :=
    (dpDifferentials_span (f.appLE V W h) (T.dividedPowers.dividedPowers (op W))).ge
      Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact (congrArg (affineSheafComparison T Y f hW h hV)
        (affineDpInv_dpd T Y f h b)).trans
        (affineSheafComparison_d T Y f hW h hV b)
  | zero =>
      rw [map_zero, affineSheafComparison_zero T Y f hW h hV]
  | add a b _ _ ha hb =>
      rw [map_add, affineSheafComparison_add T Y f hW h hV, ha, hb]
  | smul r a _ ha =>
      rw [map_smul, affineSheafComparison_smul T Y f hW h hV, ha]

include hW h hV in
/-- **The comparison of the presheaf of divided power differentials with the sheaf it generates is
bijective on an affine open lying over an affine open of the base.**  The composite of the
comparison with the identification of [Stacks, Tag 07IY] has a two-sided inverse, namely the map
out of the ring-level divided power differentials given by their universal property, and the
identification is itself bijective. -/
theorem bijective_dpDifferentialsToSheaf_app :
    Function.Bijective ((dpDifferentialsToSheaf T Y f).app (op W)).hom := by
  have hbij : Function.Bijective (affineSheafComparison T Y f hW h hV) :=
    ⟨Function.LeftInverse.injective (affinePresheafOfSheaf_affineSheafComparison T Y f hW h hV),
      Function.RightInverse.surjective (affineSheafComparison_affinePresheafOfSheaf T Y f hW h hV)⟩
  refine ⟨fun a b hab ↦ hbij.1 ?_, fun z ↦ ?_⟩
  · exact congrArg (affineSectionsEquiv T Y f hW h hV) hab
  · obtain ⟨x, hx⟩ := hbij.2 (affineSectionsEquiv T Y f hW h hV z)
    exact ⟨x, (affineSectionsEquiv T Y f hW h hV).injective hx⟩

include hW h hV in
/-- **The comparison of the presheaf of divided power differentials with the sheaf it generates is
injective on an affine open lying over an affine open of the base.** -/
theorem injective_dpDifferentialsToSheaf_app :
    Function.Injective ((dpDifferentialsToSheaf T Y f).app (op W)).hom :=
  (bijective_dpDifferentialsToSheaf_app T Y f hW h hV).1

include hW h hV in
/-- **The comparison of the presheaf of divided power differentials with the sheaf it generates is
surjective on an affine open lying over an affine open of the base.** -/
theorem surjective_dpDifferentialsToSheaf_app :
    Function.Surjective ((dpDifferentialsToSheaf T Y f).app (op W)).hom :=
  (bijective_dpDifferentialsToSheaf_app T Y f hW h hV).2

end Affine

end Crystalline

end
