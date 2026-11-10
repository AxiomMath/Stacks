module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximationSchemeDefs
public import StacksCore.Tactic.StacksAttribute

/-!
# The closed fibre of a base change along a completed local ring

Let `f : T ⟶ S` be a morphism of schemes with `S` Noetherian, let `t ∈ T` lie over `s ∈ S` and
let `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local homomorphism of `𝒪_{S, s}`-algebras. Writing `Y_σ` for
the base change of a morphism `p : Y ⟶ T` along the map `Spec(𝒪^∧_{S, s}) ⟶ T` that `σ`
determines, this file proves that the scheme-theoretic fibre `Y_t` of `p` at `t` is a closed
subscheme of `Y_σ`, compatibly with both projections.

Two facts combine. First, the residue field does not change: `σ` induces a homomorphism
`κ(t) → κ(𝒪^∧_{S, s})` which is bijective, because the composite with `κ(s) → κ(t)` is the
residue field map of `𝒪_{S, s} → 𝒪^∧_{S, s}`, which is bijective for a Noetherian local ring.
Second, inverting that bijection gives a surjection `𝒪^∧_{S, s} → κ(t)`, hence a closed point
`Spec κ(t) ⟶ Spec(𝒪^∧_{S, s})` over `t`, and `Y_t` is the base change of `Y_σ` along it.

## Main results

* `Stacks.ConormalApproximation.residueField_map_bijective_of_algebraMap`: the residue field map
  induced by `σ` is bijective, which is the observation `κ(s) = κ(t)` opening the proof of
  Stacks 0CAY.
* `Stacks.ConormalApproximation.hasFibreImmersion_of_isLocalHom`: the fibre `Y_t` is a closed
  subscheme of the base change `Y ×_{T, σ} Spec(𝒪^∧_{S, s})`, over `Spec κ(t)` and compatibly
  with both projections.
* `Stacks.ConormalApproximation.base_eq_closedPoint_completedStalk`: **the point of
  `Spec(𝒪^∧_{S, s})` that the predicates of Stacks 0CAY admit is the closed point**, and nothing
  else. The predicates `HasFibreImmersion` and `HasConormalIso` constrain `r : Spec κ(t) ⟶ W`
  only by `r ≫ b = T.fromSpecResidueField t`, but for the `b` that `σ` determines that one
  condition pins `r` down.
* `Stacks.ConormalApproximation.surjective_appLE_of_comp_eq_fromSpecResidueField`: **the
  surjectivity of `Γ(W, W₀) ⟶ κ(t)` that the chart comparison of Stacks 0CAY needs**, for every
  such `r` and every open `W₀` containing its image.
* `Stacks.ConormalApproximation.map_ker_appLE_top_eq_maximalIdeal`: **the ideal cutting out the
  fibre in the chart of the base change is the maximal ideal of `𝒪^∧_{S,s}`**, which is the
  hypothesis `hI` of the chart comparison at `W₀ = ⊤`.

## Implementation notes

The closed immersion is obtained from the universal property of the pullback rather than by
transporting the fibre along an isomorphism: the map `Y_t ⟶ Y ×_T Spec(𝒪^∧_{S, s})` is the one
induced by `Y_t ⟶ Y` and by `Y_t ⟶ Spec κ(t) ⟶ Spec(𝒪^∧_{S, s})`, and the square it makes with
the two second projections is a pullback square by the pasting law, since pasting it onto the
defining square of `Y ×_T Spec(𝒪^∧_{S, s})` gives the defining square of `Y_t`. Closed
immersions are stable under base change, so the induced map is one.

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.ConormalApproximation

variable {S T Y : Scheme.{u}}

/-- **The observation `κ(s) = κ(t)` opening the proof of Stacks 0CAY.** If `t ∈ T` lies over
`s ∈ S`, the scheme `S` is Noetherian and `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` is a local homomorphism of
`𝒪_{S, s}`-algebras, then the induced homomorphism of residue fields
`κ(t) → κ(𝒪^∧_{S, s})` is bijective.

Injectivity holds because both sides are fields. For surjectivity, the residue field map of
`𝒪_{S, s} → 𝒪^∧_{S, s}` is bijective, and it factors through `κ(t)` because `σ` is a map of
`𝒪_{S, s}`-algebras. -/
theorem residueField_map_bijective_of_algebraMap
    (f : T ⟶ S) [IsNoetherian S] (s : S) (t : T) (ht : f t = s)
    (σ : T.presheaf.stalk t →+* completedStalk S s) [IsLocalHom σ]
    (hbase : σ.comp ((f.stalkMap t).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) ht).symm).hom) =
      algebraMap (S.presheaf.stalk s) (completedStalk S s)) :
    Function.Bijective (ResidueField.map σ) := by
  subst ht
  refine ⟨RingHom.injective _, fun z => ?_⟩
  obtain ⟨w, hw⟩ := (AdicCompletion.residueField_map_bijective (S.presheaf.stalk (f t))).2 z
  obtain ⟨u, hu⟩ := residue_surjective (R := S.presheaf.stalk (f t)) w
  refine ⟨residue (T.presheaf.stalk t) ((f.stalkMap t).hom u), ?_⟩
  have h : σ ((f.stalkMap t).hom u) =
      algebraMap (S.presheaf.stalk (f t)) (completedStalk S (f t)) u := by
    simpa using RingHom.congr_fun hbase u
  rw [ResidueField.map_residue, h, ← ResidueField.map_residue, hu, hw]

/-- **Stacks Project, Tag 0CAY, the closed immersion of the common closed fibre.** Let
`p : Y ⟶ T` be a morphism of schemes, let `f : T ⟶ S` with `S` Noetherian, let `t ∈ T` lie over
`s ∈ S` and let `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local homomorphism of `𝒪_{S, s}`-algebras. Then
the scheme-theoretic fibre `Y_t` of `p` at `t` is a closed subscheme of the base change
`Y ×_{T, σ} Spec(𝒪^∧_{S, s})`, over a point of `Spec(𝒪^∧_{S, s})` above `t` cut out by the
residue field of `t`, and compatibly with both projections.

This is the step of Stacks 0CAY that makes its conclusion meaningful: the two base changes
`Y_σ` and `Y_{σ'}` both contain `Y_t` as a closed subscheme, so their conormal algebras along it
are defined and live on the same scheme.

This is the step of the proof of Tag 0CAY that makes its statement meaningful, for a local
`𝒪_{S, s}`-algebra map: the fibre `Y_t` is a closed subscheme of the completed base change
`Y ×_{T, σ} Spec(𝒪^∧_{S, s})`, over a point above `t` given by the residue field of `t` and
compatibly with both projections, which is `Stacks.ConormalApproximation.HasFibreImmersion`.
The source's opening observation `κ(s) = κ(t)` is `residueField_map_bijective_of_algebraMap`
above. It covers neither the existence of the pointed finite type extension nor the
isomorphism of conormal algebras; the full statement of the tag is
`exists_finiteType_pointed_extension_conormalAlgebra_iso_of_isLocalHom`. -/
theorem hasFibreImmersion_of_isLocalHom
    (f : T ⟶ S) (p : Y ⟶ T) [IsNoetherian S] (s : S) (t : T) (ht : f t = s)
    (σ : T.presheaf.stalk t →+* completedStalk S s) (hσ : IsLocalHom σ)
    (hbase : σ.comp ((f.stalkMap t).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) ht).symm).hom) =
      algebraMap (S.presheaf.stalk s) (completedStalk S s)) :
    HasFibreImmersion p t (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) := by
  have := hσ
  let e := RingEquiv.ofBijective (ResidueField.map σ)
    (residueField_map_bijective_of_algebraMap f s t ht σ hbase)
  let ρ0 : completedStalk S s →+* IsLocalRing.ResidueField (T.presheaf.stalk t) :=
    e.symm.toRingHom.comp (residue (completedStalk S s))
  have hρσ : ρ0.comp σ = IsLocalRing.residue (T.presheaf.stalk t) := by
    ext a
    change e.symm (residue (completedStalk S s) (σ a)) = residue _ a
    rw [← ResidueField.map_residue, show (ResidueField.map σ) (residue (T.presheaf.stalk t) a)
      = e (residue (T.presheaf.stalk t) a) from rfl, e.symm_apply_apply]
  let ρ : CommRingCat.of (completedStalk S s) ⟶ T.residueField t := CommRingCat.ofHom ρ0
  have hr : Spec.map ρ ≫ Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t =
      T.fromSpecResidueField t := by
    rw [← Spec.map_comp_assoc,
      show CommRingCat.ofHom σ ≫ ρ = T.residue t from CommRingCat.hom_ext hρσ]
    rfl
  have hcond : p.fiberι t ≫ p = (p.fiberToSpecResidueField t ≫ Spec.map ρ) ≫
      Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t := by
    rw [Category.assoc, hr]
    exact p.fiber_fac t
  exact ⟨Spec.map ρ,
    pullback.lift (p.fiberι t) (p.fiberToSpecResidueField t ≫ Spec.map ρ) hcond,
    hr, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (isPullback_fibre_of_immersionData p t _ (Spec.map ρ) _ hr
        (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _))
      (IsClosedImmersion.spec_of_surjective _
        (e.symm.surjective.comp (residue_surjective (R := completedStalk S s))))⟩

section FibrePoint

/-! ### The point of the base change that a fibre immersion can be taken over

`Stacks.ConormalApproximation.HasFibreImmersion` and
`Stacks.ConormalApproximation.HasConormalIso` quantify over a morphism
`r : Spec κ(t) ⟶ W` constrained only by `r ≫ b = T.fromSpecResidueField t`. For a general `b`
that leaves `r` genuinely free, and the map `Γ(W, W₀) ⟶ κ(t)` it induces need not be surjective:
for `W = T = Spec ℤ`, `b = 𝟙` and `t` the generic point, `r = T.fromSpecResidueField t` satisfies
the condition and induces `ℤ → ℚ`.

For the `b` that a ring map `σ : 𝒪_{T,t} ⟶ A` determines, namely
`Spec A ⟶ Spec 𝒪_{T,t} ⟶ T`, there is no freedom left. The morphism `Spec 𝒪_{T,t} ⟶ T` is a
preimmersion, hence a monomorphism, so `r` is determined by a ring map `ρ : A ⟶ κ(t)` with
`ρ ∘ σ` the residue map of `𝒪_{T,t}`; the residue map is surjective, so `ρ` is surjective, and
therefore so is every `Γ(Spec A, W₀) ⟶ κ(t)` it factors through. If `A` is moreover local — as
`completedStalk S s` is for `S` Noetherian — then `ρ` surjective onto a field forces its kernel
to be the maximal ideal, that is, `r` to be the closed point of `Spec A`.

Both conclusions use only the condition `r ≫ b = T.fromSpecResidueField t`. The closed immersion
`j` of `HasFibreImmersion`, the locality of `σ` and the `𝒪_{S,s}`-algebra condition on it play no
part.
-/

variable {A : CommRingCat.{u}}

/-- **The ring map underlying a point over `t` is a retraction of `σ` onto the residue field.**
Let `σ : 𝒪_{T,t} ⟶ A` and let `ρ : A ⟶ κ(t)` be ring maps such that the morphism
`Spec κ(t) ⟶ Spec A` induced by `ρ` lies over `t` for the morphism `Spec A ⟶ T` induced by `σ`.
Then `ρ ∘ σ` is the residue map of `𝒪_{T,t}`.

The morphism `T.fromSpecStalk t` is a preimmersion, hence a monomorphism, so the two
factorisations through it agree; and `Spec` is faithful. -/
theorem comp_eq_residue_of_comp_eq_fromSpecResidueField (t : T) (σ : T.presheaf.stalk t ⟶ A)
    (ρ : A ⟶ CommRingCat.of (T.residueField t))
    (hr : Spec.map ρ ≫ (Spec.map σ ≫ T.fromSpecStalk t) = T.fromSpecResidueField t) :
    σ ≫ ρ = T.residue t := by
  refine Spec.map_inj.mp ((cancel_mono (T.fromSpecStalk t)).mp ?_)
  rwa [Spec.map_comp, Category.assoc]

/-- **A point of `Spec A` over `t` has surjective ring map.** With `σ`, `ρ` and the condition of
`comp_eq_residue_of_comp_eq_fromSpecResidueField`, the map `ρ : A ⟶ κ(t)` is surjective, because
`ρ ∘ σ` is the residue map of `𝒪_{T,t}`, which is. -/
theorem surjective_of_comp_eq_fromSpecResidueField (t : T) (σ : T.presheaf.stalk t ⟶ A)
    (ρ : A ⟶ CommRingCat.of (T.residueField t))
    (hr : Spec.map ρ ≫ (Spec.map σ ≫ T.fromSpecStalk t) = T.fromSpecResidueField t) :
    Function.Surjective ρ.hom := by
  refine Function.Surjective.of_comp (g := σ.hom) ?_
  rw [← RingHom.coe_comp, ← CommRingCat.hom_comp,
    comp_eq_residue_of_comp_eq_fromSpecResidueField t σ ρ hr]
  exact T.residue_surjective t

/-- The kernel of the surjection `ρ : A ⟶ κ(t)` of a point over `t` is the maximal ideal. -/
private theorem ker_eq_maximalIdeal_of_comp_eq_fromSpecResidueField [IsLocalRing A] (t : T)
    (σ : T.presheaf.stalk t ⟶ A) (ρ : A ⟶ CommRingCat.of (T.residueField t))
    (hr : Spec.map ρ ≫ (Spec.map σ ≫ T.fromSpecStalk t) = T.fromSpecResidueField t) :
    RingHom.ker ρ.hom = IsLocalRing.maximalIdeal A :=
  IsLocalRing.ker_eq_maximalIdeal ρ.hom (surjective_of_comp_eq_fromSpecResidueField t σ ρ hr)

/-- The global sections map of `Spec.map ρ` is `ρ` up to the `ΓSpecIso` identifications. -/
private theorem appTop_spec_map_eq {B : CommRingCat.{u}} (ρ : A ⟶ B) :
    (Spec.map ρ).appTop = (Scheme.ΓSpecIso A).hom ≫ ρ ≫ (Scheme.ΓSpecIso B).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **The point of `Spec A` over `t` is its closed point, when `A` is local.** If `A` is a local
ring, the only morphism `r : Spec κ(t) ⟶ Spec A` with
`r ≫ (Spec σ ≫ T.fromSpecStalk t) = T.fromSpecResidueField t` sends the point of `Spec κ(t)` to
the closed point of `Spec A`: the ring map underlying `r` is a surjection onto a field by
`surjective_of_comp_eq_fromSpecResidueField`, so its kernel is a maximal ideal, hence the
maximal ideal.

For `A = 𝒪^∧_{S,s}` this is the answer to the question which points of `Spec(𝒪^∧_{S,s})` the
predicates of `ConormalApproximationSchemeDefs` admit: only the closed point. -/
theorem base_eq_closedPoint_of_comp_eq_fromSpecResidueField [IsLocalRing A] (t : T)
    (σ : T.presheaf.stalk t ⟶ A)
    (r : Spec (CommRingCat.of (T.residueField t)) ⟶ Spec A)
    (hr : r ≫ (Spec.map σ ≫ T.fromSpecStalk t) = T.fromSpecResidueField t)
    (x : Spec (CommRingCat.of (T.residueField t))) :
    r x = IsLocalRing.closedPoint A := by
  obtain ⟨ρ, rfl⟩ := Spec.map_surjective r
  have hx : x.asIdeal = ⊥ := by
    rw [Unique.eq_default x]
    exact Scheme.default_asIdeal
  refine PrimeSpectrum.ext ?_
  change Ideal.comap ρ.hom x.asIdeal = IsLocalRing.maximalIdeal A
  rw [hx, ← RingHom.ker_eq_comap_bot]
  exact ker_eq_maximalIdeal_of_comp_eq_fromSpecResidueField t σ ρ hr

/-- **The point of `Spec(𝒪^∧_{S,s})` admitted by the predicates of Stacks 0CAY is its closed
point.** For `b = Spec σ ≫ T.fromSpecStalk t` the morphism of
`Stacks.ConormalApproximation.hasFibreImmersion_of_isLocalHom` and of
`Stacks.ConormalApproximation.HasUniformConormalBound`, any `r` with
`r ≫ b = T.fromSpecResidueField t` — the sole condition that
`Stacks.ConormalApproximation.HasFibreImmersion` and
`Stacks.ConormalApproximation.HasConormalIso` put on `r` — sends the point of `Spec κ(t)` to the
closed point of `Spec(𝒪^∧_{S,s})`. Neither the closed immersion `j`, nor the locality of `σ`, nor
its being a map of `𝒪_{S,s}`-algebras is used; `S` Noetherian enters only to make `𝒪^∧_{S,s}` a
local ring. -/
theorem base_eq_closedPoint_completedStalk [IsNoetherian S] (s : S) (t : T)
    (σ : T.presheaf.stalk t →+* completedStalk S s)
    (r : Spec (CommRingCat.of (T.residueField t)) ⟶
      Spec (CommRingCat.of (completedStalk S s)))
    (hr : r ≫ (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) =
      T.fromSpecResidueField t)
    (x : Spec (CommRingCat.of (T.residueField t))) :
    r x = IsLocalRing.closedPoint (completedStalk S s) :=
  base_eq_closedPoint_of_comp_eq_fromSpecResidueField t (CommRingCat.ofHom σ) r hr x

/-- **The surjectivity of `Γ(W, W₀) ⟶ κ(t)` that the chart comparison of Stacks 0CAY needs.**
For `W = Spec A` and `b` the morphism a ring map `σ : 𝒪_{T,t} ⟶ A` determines, every point
`r : Spec κ(t) ⟶ W` over `t` — in particular every one that
`Stacks.ConormalApproximation.HasFibreImmersion` or
`Stacks.ConormalApproximation.HasConormalIso` admits — induces a surjection
`Γ(W, W₀) ⟶ Γ(Spec κ(t), ⊤)` on any open `W₀` of `W` containing the image of `r`.

The map on global sections is surjective by
`surjective_of_comp_eq_fromSpecResidueField` and the naturality of
`AlgebraicGeometry.Scheme.ΓSpecIso`, and it factors through the restriction to `W₀`.

This is the hypothesis `hsurj` of
`Stacks.ConormalApproximation.chartIdeal_eq_of_fibreImmersion` and of
`Stacks.ConormalApproximation.chartQuotientPresentationOfPullbackChart`. No locality of `A` is
needed, and no part of the data of the closed immersion `j`. -/
theorem surjective_appLE_of_comp_eq_fromSpecResidueField (t : T) (σ : T.presheaf.stalk t ⟶ A)
    (r : Spec (CommRingCat.of (T.residueField t)) ⟶ Spec A)
    (hr : r ≫ (Spec.map σ ≫ T.fromSpecStalk t) = T.fromSpecResidueField t)
    (W₀ : (Spec A).Opens)
    (hrW : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤ r ⁻¹ᵁ W₀) :
    Function.Surjective (r.appLE W₀ ⊤ hrW).hom := by
  have htop : Function.Surjective r.appTop.hom := by
    obtain ⟨ρ, rfl⟩ := Spec.map_surjective r
    have hsurj := surjective_of_comp_eq_fromSpecResidueField t σ ρ hr
    rw [appTop_spec_map_eq]
    exact ((CategoryTheory.ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (T.residueField t))).inv).2.comp hsurj).comp
      (CategoryTheory.ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).2
  have hfac : (Spec A).presheaf.map (homOfLE (le_top (a := W₀))).op ≫ r.appLE W₀ ⊤ hrW =
      r.appTop := by
    rw [Scheme.Hom.map_appLE]
    exact Scheme.Hom.appLE_eq_app r
  refine Function.Surjective.of_comp
    (g := ((Spec A).presheaf.map (homOfLE (le_top (a := W₀))).op).hom) ?_
  rw [← RingHom.coe_comp, ← CommRingCat.hom_comp, hfac]
  exact htop

/-- **The ideal cutting out the fibre in the chart of the base change is the maximal ideal.**
For `W = Spec A` with `A` a local ring and `b` the morphism a ring map `σ : 𝒪_{T,t} ⟶ A`
determines, the kernel of the map `Γ(Spec A, ⊤) ⟶ κ(t)` induced by a point `r` over `t` is, read
in `A` along `AlgebraicGeometry.Scheme.ΓSpecIso`, the maximal ideal of `A`: the map is surjective
by `surjective_of_comp_eq_fromSpecResidueField`, so its kernel is a maximal ideal, hence *the*
maximal ideal.

For `A = 𝒪^∧_{S,s}` this is the hypothesis `hI` of
`Stacks.ConormalApproximation.chartQuotientPresentationOfPullbackChart` and of the chart family
comparison, at `W₀ = ⊤`: it says that the ideal the comparison takes the associated graded for is
the maximal ideal of the completed local ring, which is what makes the `I`-adic filtration of the
chart the `𝔪_s`-adic one. -/
theorem map_ker_appLE_top_eq_maximalIdeal [IsLocalRing A] (t : T) (σ : T.presheaf.stalk t ⟶ A)
    (r : Spec (CommRingCat.of (T.residueField t)) ⟶ Spec A)
    (hr : r ≫ (Spec.map σ ≫ T.fromSpecStalk t) = T.fromSpecResidueField t)
    (hrW : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤
      r ⁻¹ᵁ (⊤ : (Spec A).Opens)) :
    (RingHom.ker (r.appLE ⊤ ⊤ hrW).hom).map (Scheme.ΓSpecIso A).hom.hom =
      IsLocalRing.maximalIdeal A := by
  obtain ⟨ρ, rfl⟩ := Spec.map_surjective r
  have happ : (Spec.map ρ).appLE ⊤ ⊤ hrW = (Scheme.ΓSpecIso A).hom ≫ ρ ≫
      (Scheme.ΓSpecIso (CommRingCat.of (T.residueField t))).inv := appTop_spec_map_eq ρ
  have hinj : Function.Injective
      (Scheme.ΓSpecIso (CommRingCat.of (T.residueField t))).inv.hom :=
    (CategoryTheory.ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (T.residueField t))).inv).1
  have hker : RingHom.ker ((Scheme.ΓSpecIso A).hom ≫ ρ ≫
        (Scheme.ΓSpecIso (CommRingCat.of (T.residueField t))).inv).hom =
      Ideal.comap (Scheme.ΓSpecIso A).hom.hom (RingHom.ker ρ.hom) := by
    refine Ideal.ext fun x => ?_
    simp only [Ideal.mem_comap, RingHom.mem_ker, CommRingCat.hom_comp, RingHom.comp_apply]
    exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
  rw [happ, hker, Ideal.map_comap_of_surjective _
      (CategoryTheory.ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).2,
    ker_eq_maximalIdeal_of_comp_eq_fromSpecResidueField t σ ρ hr]

/-- **Two points of `Spec A` over `t`, for two maps out of the stalk which agree modulo the
maximal ideal of a local ring `A`, are the same point of `Spec A` — the same morphism, not merely
the same element of the space.**

The two ring maps `ρ, ρ' : A ⟶ κ(t)` underlying the two points are surjective and satisfy
`ρ ∘ σ = ρ' ∘ σ' = ` the residue map of `𝒪_{T,t}`, by
`Stacks.ConormalApproximation.surjective_of_comp_eq_fromSpecResidueField` and
`Stacks.ConormalApproximation.comp_eq_residue_of_comp_eq_fromSpecResidueField`, and their kernels
are both the maximal ideal of `A`. Every `a : A` is therefore congruent modulo that kernel to some
`σ x`: pick `x` with residue `ρ a`. On `σ x` the two maps agree, because `σ x` and `σ' x` differ
by an element of the kernel of `ρ'`.

For `A = 𝒪^∧_{S,s}` this is the hypothesis `hsource` of the chart family comparison of Stacks
0CAY, and it is what makes the two base changes present the *same* functions on the fibre: the
chart of the base is entered only through the one map `A ⟶ κ(t)`. Note that no locality of `σ` or
`σ'`, and no `𝒪_{S,s}`-algebra condition, is used. -/
theorem eq_of_sub_mem_maximalIdeal [IsLocalRing A] (t : T) (σ σ' : T.presheaf.stalk t ⟶ A)
    (hcong : ∀ x, σ.hom x - σ'.hom x ∈ IsLocalRing.maximalIdeal A)
    (r r' : Spec (CommRingCat.of (T.residueField t)) ⟶ Spec A)
    (hr : r ≫ (Spec.map σ ≫ T.fromSpecStalk t) = T.fromSpecResidueField t)
    (hr' : r' ≫ (Spec.map σ' ≫ T.fromSpecStalk t) = T.fromSpecResidueField t) :
    r = r' := by
  obtain ⟨ρ, rfl⟩ := Spec.map_surjective r
  obtain ⟨ρ', rfl⟩ := Spec.map_surjective r'
  have hker := ker_eq_maximalIdeal_of_comp_eq_fromSpecResidueField t σ ρ hr
  have hker' := ker_eq_maximalIdeal_of_comp_eq_fromSpecResidueField t σ' ρ' hr'
  suffices h : ρ = ρ' by rw [h]
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  obtain ⟨x, hx⟩ := T.residue_surjective t (ρ.hom a)
  have h1 : ρ.hom (σ.hom x) = ρ.hom a := by
    rwa [← CommRingCat.comp_apply, comp_eq_residue_of_comp_eq_fromSpecResidueField t σ ρ hr]
  have h2 : ρ'.hom a = ρ'.hom (σ.hom x) := by
    have hmem : a - σ.hom x ∈ RingHom.ker ρ'.hom := by
      rw [hker', ← hker, RingHom.mem_ker, map_sub, h1, sub_self]
    rwa [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
  have h3 : ρ'.hom (σ.hom x) = ρ'.hom (σ'.hom x) := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker']
    exact hcong x
  have h4 : ρ'.hom (σ'.hom x) = (T.residue t).hom x := by
    rw [← CommRingCat.comp_apply, comp_eq_residue_of_comp_eq_fromSpecResidueField t σ' ρ' hr']
  rw [h2, h3, h4, hx]

end FibrePoint

end Stacks.ConormalApproximation

end
