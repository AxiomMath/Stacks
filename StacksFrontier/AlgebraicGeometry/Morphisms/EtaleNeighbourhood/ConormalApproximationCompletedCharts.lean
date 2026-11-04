module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximationChartFamily
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximationExtension

/-!
# The chart family of Stacks 0CAY at the two completed base changes

This file instantiates the sub-family of common charts of
`StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/ConormalApproximationChartFamily.lean`
at the two morphisms Stacks 0CAY compares, namely
`b = Spec(𝒪^∧_{S,s}) ⟶ Spec(𝒪_{T,t}) ⟶ T` determined by `σ` and the same for `σ'`, and reduces
`Stacks.ConormalApproximation.HasConormalIso` for them to the *affine* comparison of associated
graded algebras over the charts.

Everything geometric is discharged here. The chart of `W = Spec(𝒪^∧_{S,s})` is the whole of it:
the range of `T.fromSpecStalk t` is the set of generalisations of `t`, so `W` lies over any open
`T₀` containing `t`.

## Main results

* `Stacks.ConormalApproximation.preimage_eq_top_specMap_fromSpecStalk`: the base change along
  `Spec A ⟶ Spec 𝒪_{T,t} ⟶ T` lies over every open containing `t`.
* `Stacks.ConormalApproximation.ΓSpecIso_appLE_specMap_fromSpecStalk`: the structure map
  `Γ(T, T₀) ⟶ Γ(Spec A, ⊤) ≅ A` of that chart is the germ at `t` followed by `σ`.
* `Stacks.ConormalApproximation.hasConormalIso_of_chartGradedAlgEquiv`: **`HasConormalIso` for
  the two completed base changes, from the affine comparison over the charts.** Every geometric
  hypothesis of the chart family comparison is discharged: the chart of `W` is the whole of
  `Spec(𝒪^∧_{S,s})`, the ideal cutting out the fibre is its maximal ideal, the map to the residue
  field is surjective, and the two points of `Spec(𝒪^∧_{S,s})` that the predicate admits are the
  same morphism (`Stacks.ConormalApproximation.eq_of_sub_mem_maximalIdeal`).
* `Stacks.ConormalApproximation.hasConormalBoundAlongExtension_of_chartGradedAlgEquiv`: the same
  for `Stacks.ConormalApproximation.HasConormalBoundAlongExtension`, which is the hypothesis
  Stacks 0CAY is registered relative to. What remains of it is a statement about rings and one
  chart: a single finite type extension and a single bound must serve *every* affine open of `Y`
  above `T₀` with a presentation, whereas the affine core
  `Stacks.ConormalApproximation.exists_finiteType_coefficients_associatedGraded_equiv` produces an
  extension and an Artin-Rees bound depending on the chart, and
  `Stacks.ConormalApproximation.exists_pointed_extension_merge_family` merges only finitely many.

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.ConormalApproximation

section SpecStalkChart

variable {T : Scheme.{u}} (t : T)

/-- **The base change along `Spec A ⟶ Spec 𝒪_{T,t} ⟶ T` lies entirely over any open containing
`t`.** The range of `T.fromSpecStalk t` is the set of generalisations of `t`, by
`AlgebraicGeometry.Scheme.range_fromSpecStalk`, and an open neighbourhood of `t` contains every
generalisation of `t`.

So `W₀ = ⊤` is an affine open of `Spec A` above `T₀`, which is the chart of `W` that Stacks 0CAY
uses: the comparison of the two base changes happens over the *whole* of `Spec(𝒪^∧_{S,s})`, and
only the affine open of `Y` varies. -/
theorem preimage_eq_top_specMap_fromSpecStalk {T₀ : T.Opens} (ht : t ∈ T₀) {A : CommRingCat.{u}}
    (φ : T.presheaf.stalk t ⟶ A) :
    (Spec.map φ ≫ T.fromSpecStalk t) ⁻¹ᵁ T₀ = ⊤ := by
  refine top_le_iff.mp fun z _ => ?_
  show (T.fromSpecStalk t) ((Spec.map φ) z) ∈ T₀
  have hz : (T.fromSpecStalk t) ((Spec.map φ) z) ∈ {y | y ⤳ t} := by
    rw [← Scheme.range_fromSpecStalk]
    exact ⟨(Spec.map φ) z, rfl⟩
  exact hz.mem_open T₀.2 ht

/-- **The structure map of the chart `⊤` of `Spec A` is the germ at `t` followed by `φ`.** The map
`Γ(T, T₀) ⟶ Γ(Spec A, ⊤)` that `b = Spec φ ≫ T.fromSpecStalk t` induces is, read in `A` along
`AlgebraicGeometry.Scheme.ΓSpecIso`, the composite of the germ map `Γ(T, T₀) ⟶ 𝒪_{T,t}` with `φ`.

This is the hypothesis `hD` of the chart family comparison, and it is what turns a congruence of
`σ` with `σ'` as maps out of the stalk into a congruence of the two structure maps `Γ(T, T₀) ⟶ A`
that the affine comparison compares across. -/
theorem ΓSpecIso_appLE_specMap_fromSpecStalk {T₀ : T.Opens} (ht : t ∈ T₀) {A : CommRingCat.{u}}
    (φ : T.presheaf.stalk t ⟶ A) :
    (Spec.map φ ≫ T.fromSpecStalk t).appLE T₀ ⊤
          (preimage_eq_top_specMap_fromSpecStalk t ht φ).ge ≫ (Scheme.ΓSpecIso A).hom =
      T.presheaf.germ T₀ t ht ≫ φ := by
  have hle : (⊤ : (Spec A).Opens) ≤ Spec.map φ ⁻¹ᵁ (T.fromSpecStalk t ⁻¹ᵁ T₀) := by
    rw [← Scheme.Hom.comp_preimage]
    exact (preimage_eq_top_specMap_fromSpecStalk t ht φ).ge
  have hsplit := Scheme.Hom.appLE_comp_appLE (Spec.map φ) (T.fromSpecStalk t) T₀
    (T.fromSpecStalk t ⁻¹ᵁ T₀) ⊤ le_rfl hle
  rw [← hsplit, Scheme.Hom.appLE_eq_app, Scheme.fromSpecStalk_app ht]
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE_assoc,
    show Scheme.Hom.appLE (Spec.map φ) ⊤ ⊤ le_top =
      (Spec.map φ).appTop from Scheme.Hom.appLE_eq_app (Spec.map φ),
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- **The structure map of the chart of a base change along the spectrum of a ring receiving a map
out of the stalk**: the germ at `t` followed by that map. This is the ring map `C → D` across which
the affine comparison
`Stacks.ConormalApproximation.exists_finiteType_coefficients_associatedGraded_equiv` of Stacks
0CAY compares, by `Stacks.ConormalApproximation.ΓSpecIso_appLE_specMap_fromSpecStalk`. -/
def completedChartHom {T₀ : T.Opens} (ht : t ∈ T₀) {A : Type u} [CommRing A]
    (φ : T.presheaf.stalk t →+* A) : Γ(T, T₀) →+* A :=
  φ.comp (T.presheaf.germ T₀ t ht).hom

/-- The identification of the global sections of an affine scheme with its ring, as a ring
equivalence. -/
abbrev specTopEquiv (A : CommRingCat.{u}) : Γ(Spec A, ⊤) ≃+* A :=
  (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv

/-- For `φ : 𝒪_{T,t} ⟶ A` and an open `T₀` containing `t`, the map on sections
`Γ(T, T₀) → Γ(Spec A, ⊤)` induced by `Spec A → Spec 𝒪_{T,t} → T`, followed by `specTopEquiv A`,
is `completedChartHom t ht φ.hom`. -/
theorem specTopEquiv_appLE_specMap_fromSpecStalk {T₀ : T.Opens} (ht : t ∈ T₀)
    {A : CommRingCat.{u}} (φ : T.presheaf.stalk t ⟶ A) (x : Γ(T, T₀)) :
    specTopEquiv A (((Spec.map φ ≫ T.fromSpecStalk t).appLE T₀ ⊤
          (preimage_eq_top_specMap_fromSpecStalk t ht φ).ge).hom x) =
      completedChartHom t ht φ.hom x := by
  show (Scheme.ΓSpecIso A).hom.hom _ = _
  rw [← CommRingCat.comp_apply, ΓSpecIso_appLE_specMap_fromSpecStalk t ht φ,
    CommRingCat.comp_apply]
  rfl

end SpecStalkChart

section CompletedComparison

variable {S T Y : Scheme.{u}} (p : Y ⟶ T) [LocallyOfFiniteType p] [IsNoetherian T]
  [IsNoetherian S] (s : S) (t : T) {T₀ : T.Opens} (hT₀ : IsAffineOpen T₀) (ht : t ∈ T₀)
  (σ σ' : T.presheaf.stalk t →+* completedStalk S s)

include hT₀ ht in
/-- **The conormal algebras of the two completed base changes of Stacks 0CAY are isomorphic, as
soon as the associated graded algebras of the chart presentations are.** Let `t ∈ T₀` with `T₀`
an affine open of a Noetherian `T`, let `p : Y ⟶ T` be locally of finite type and let
`σ, σ' : 𝒪_{T,t} → 𝒪^∧_{S,s}` agree modulo the maximal ideal. Then
`Stacks.ConormalApproximation.HasConormalIso` holds for the two base changes as soon as, over
every affine open `U` of `Y` above `T₀` with a presentation of `Γ(Y, U)` over `Γ(T, T₀)`, the two
specialised relation matrices have isomorphic `𝔪`-adic associated graded cokernels by an
isomorphism induced by the identity of `𝒪^∧_{S,s}[x_1, …, x_n]`.

This is the whole geometric content of Stacks 0CAY's gluing step, discharged: the chart of
`W = Spec(𝒪^∧_{S,s})` is the whole of it
(`Stacks.ConormalApproximation.preimage_eq_top_specMap_fromSpecStalk`), its structure map is the
germ followed by `σ` (`Stacks.ConormalApproximation.ΓSpecIso_appLE_specMap_fromSpecStalk`), the
ideal cutting out the fibre is the maximal ideal
(`Stacks.ConormalApproximation.map_ker_appLE_top_eq_maximalIdeal`), the map to the residue field
is surjective (`Stacks.ConormalApproximation.surjective_appLE_of_comp_eq_fromSpecResidueField`)
and the two points of `Spec(𝒪^∧_{S,s})` admitted by the predicate are literally the same morphism
(`Stacks.ConormalApproximation.eq_of_sub_mem_maximalIdeal`). What is left is the hypothesis `e`
with its disclosure `hind`, which is ring theory over one chart. -/
theorem hasConormalIso_of_chartGradedAlgEquiv
    (hcong : ∀ x, σ x - σ' x ∈ IsLocalRing.maximalIdeal (completedStalk S s))
    (e : ∀ a : PresentedChart p T₀ Γ(T, T₀) (RingEquiv.refl Γ(T, T₀)),
      AssociatedGraded.GradedAlgEquiv
        ((IsLocalRing.maximalIdeal (completedStalk S s)).map
          (MvPolynomial.C : completedStalk S s →+*
            MvPolynomial (Fin a.n) (completedStalk S s)))
        (MvPolynomial (Fin a.n) (completedStalk S s) ⧸
          LinearMap.range (relationMapOfHom (completedChartHom t ht σ) a.relation))
        (MvPolynomial (Fin a.n) (completedStalk S s) ⧸
          LinearMap.range (relationMapOfHom (completedChartHom t ht σ') a.relation)))
    (hind : ∀ a, (e a).IsInducedByIdentity) :
    HasConormalIso p t (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t)
      (Spec.map (CommRingCat.ofHom σ') ≫ T.fromSpecStalk t) := by
  intro r r' j j' hr hr' hfst hfst' hsnd hsnd' hj hj'
  have := hj
  have := hj'
  have hrr : r = r' :=
    eq_of_sub_mem_maximalIdeal t (CommRingCat.ofHom σ) (CommRingCat.ofHom σ') hcong r r' hr hr'
  refine nonempty_conormalAlgebra_iso_of_presentedCharts_of_eq_on p t _ _ hr hr' hfst hsnd hfst'
    hsnd' hT₀ (isAffineOpen_top _) (isAffineOpen_top _)
    (preimage_eq_top_specMap_fromSpecStalk t ht (CommRingCat.ofHom σ)).ge
    (preimage_eq_top_specMap_fromSpecStalk t ht (CommRingCat.ofHom σ')).ge
    le_top le_top (RingEquiv.refl Γ(T, T₀))
    (completedChartHom t ht σ) (completedChartHom t ht σ')
    (specTopEquiv _) (specTopEquiv _)
    (fun x => specTopEquiv_appLE_specMap_fromSpecStalk t ht (CommRingCat.ofHom σ) x)
    (fun x => specTopEquiv_appLE_specMap_fromSpecStalk t ht (CommRingCat.ofHom σ') x)
    (IsLocalRing.maximalIdeal (completedStalk S s))
    (map_ker_appLE_top_eq_maximalIdeal t (CommRingCat.ofHom σ) r hr le_top)
    (surjective_appLE_of_comp_eq_fromSpecResidueField t (CommRingCat.ofHom σ) r hr ⊤
      le_top)
    (surjective_appLE_of_comp_eq_fromSpecResidueField t (CommRingCat.ofHom σ') r' hr' ⊤
      le_top)
    (fun d => ?_) ht e hind
  rw [hrr]

end CompletedComparison

section Bound

variable {S T Y : Scheme.{u}} (p : Y ⟶ T) [LocallyOfFiniteType p] [IsNoetherian T]
  [IsNoetherian S] (s : S) (t : T) {T₀ : T.Opens} (hT₀ : IsAffineOpen T₀) (ht : t ∈ T₀)
  (sigma : T.presheaf.stalk t →+* completedStalk S s)

/-- **The congruence of `Stacks.ConormalApproximation.HasConormalBoundAlongExtension` implies
congruence modulo the maximal ideal of the completed local ring**, as soon as the bound is at
least one: the ideal that `𝔪_s` generates in `𝒪^∧_{S,s}` is contained in the maximal ideal, the
structure map being local. -/
theorem sub_mem_maximalIdeal_of_mem_map_pow {N : ℕ} (hN : 1 ≤ N) {x : completedStalk S s}
    (hx : x ∈ Ideal.map (algebraMap (S.presheaf.stalk s) (completedStalk S s))
      (IsLocalRing.maximalIdeal (S.presheaf.stalk s) ^ N)) :
    x ∈ IsLocalRing.maximalIdeal (completedStalk S s) :=
  IsLocalRing.map_maximalIdeal_le _
    (Ideal.map_mono (Ideal.pow_le_self (Nat.one_le_iff_ne_zero.mp hN)) hx)

include hT₀ ht in
/-- **The comparison hypothesis of Stacks 0CAY, reduced to the affine comparison over the charts.**
Given a pointed finite type extension `(T₁, t₁) → (T, t)` through which `σ` factors by a local
homomorphism `τ`, a bound `N ≥ 1`, and — for every `τ'` congruent to `τ` modulo `𝔪_s^N` and
*every* affine open `U` of `Y` above `T₀` with a presentation of `Γ(Y, U)` over `Γ(T, T₀)` — an
isomorphism of the `𝔪`-adic associated graded cokernels of the two specialised relation matrices
induced by the identity of `𝒪^∧_{S,s}[x_1, …, x_n]`, the property
`Stacks.ConormalApproximation.HasConormalBoundAlongExtension` holds.

Everything other than that per-chart isomorphism is discharged here and in
`Stacks.ConormalApproximation.hasConormalIso_of_chartGradedAlgEquiv`: the hypothesis that remains
is a statement about rings and one chart, and it is what the affine core
`Stacks.ConormalApproximation.exists_finiteType_coefficients_associatedGraded_equiv` produces —
there, however, with a finite type extension and an Artin-Rees bound depending on the chart,
whereas here one extension and one bound must serve them all. -/
theorem hasConormalBoundAlongExtension_of_chartGradedAlgEquiv
    {T₁ : Scheme.{u}} (g : T₁ ⟶ T) (t₁ : T₁) (hgt : g t₁ = t) [IsNoetherian T₁]
    [LocallyOfFiniteType g] [QuasiCompact g]
    (tau : T₁.presheaf.stalk t₁ →+* completedStalk S s) (htau : IsLocalHom tau)
    (hfact : sigma = tau.comp (pointedStalkMap g hgt))
    (N : ℕ) (hN : 1 ≤ N)
    (hchart : ∀ tau' : T₁.presheaf.stalk t₁ →+* completedStalk S s,
      (∀ y, tau y - tau' y ∈
        Ideal.map (algebraMap (S.presheaf.stalk s) (completedStalk S s))
          (IsLocalRing.maximalIdeal (S.presheaf.stalk s) ^ N)) →
      ∀ a : PresentedChart p T₀ Γ(T, T₀) (RingEquiv.refl Γ(T, T₀)),
        ∃ eq : AssociatedGraded.GradedAlgEquiv
          ((IsLocalRing.maximalIdeal (completedStalk S s)).map
            (MvPolynomial.C : completedStalk S s →+*
              MvPolynomial (Fin a.n) (completedStalk S s)))
          (MvPolynomial (Fin a.n) (completedStalk S s) ⧸
            LinearMap.range (relationMapOfHom (completedChartHom t ht sigma) a.relation))
          (MvPolynomial (Fin a.n) (completedStalk S s) ⧸
            LinearMap.range (relationMapOfHom
              (completedChartHom t ht (tau'.comp (pointedStalkMap g hgt))) a.relation)),
          eq.IsInducedByIdentity) :
    HasConormalBoundAlongExtension p s t sigma := by
  refine ⟨T₁, g, t₁, hgt, inferInstance, inferInstance, inferInstance, tau, htau, hfact, N, hN,
    fun tau' hcongr => ?_⟩
  have hcong : ∀ x, sigma x - (tau'.comp (pointedStalkMap g hgt)) x ∈
      IsLocalRing.maximalIdeal (completedStalk S s) := by
    intro x
    refine sub_mem_maximalIdeal_of_mem_map_pow s hN ?_
    rw [hfact]
    exact hcongr (pointedStalkMap g hgt x)
  choose e hind using hchart tau' hcongr
  exact hasConormalIso_of_chartGradedAlgEquiv p s t hT₀ ht sigma
    (tau'.comp (pointedStalkMap g hgt)) hcong e hind

end Bound

end Stacks.ConormalApproximation

end
