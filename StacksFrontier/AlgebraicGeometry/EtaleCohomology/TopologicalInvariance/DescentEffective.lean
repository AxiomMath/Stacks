module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentGluing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.SectionSplitting
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentDataBridgeRelation
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentTransport
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine case of topological invariance of the small étale site

Let `f : X ⟶ Y` be a universal homeomorphism of affine schemes. Stacks Project, Tag 04E0 asserts
that `V ↦ X ×_Y V` is an equivalence from the affine schemes étale over `Y` to the affine schemes
étale over `X`; its essential surjectivity is the content the source proves, by induction on a
bound for the degrees of the fibres of an étale morphism of affine schemes. This file carries out
the one descent the induction needs, and thereby proves that essential surjectivity
unconditionally.

## What is still open coming into this file

`Stacks.Etale.exists_affine_etale_descent_of_surjective` reduces the inductive step to the
following. For a surjective étale `p : U ⟶ X` with `U` affine there are an affine scheme `W`
étale and surjective over `Y` and an affine scheme `T` étale over `W`, together with an
isomorphism `e : T ×_W W_X ≅ U ×_X W_X` over `W_X := X ×_Y W`. What remains is to descend `T`
along the surjective étale `w : W ⟶ Y` and to identify the base change along `f` of the result
with `U`.

## The mechanism

A generalized point of `T` lying over a point of `W_X` has, through `e`, a `U`-component
(`Stacks.Etale.descentUComp`). Two such points are related when, at every lift of the test object
to `X` compatible with the two of them, those `U`-components agree: this is
`Stacks.Etale.DescentRel`. It is an equivalence relation stable under precomposition, and the
`Y`-image of a point is one of its invariants — the `W`-image is *not*, and must not be added, for
the gluing action moves a point from one chart of `W ×_Y W` to the other.

`Stacks.Etale.eq_of_descentUComp_eq` is the extensionality the relation is built for: two points
of `T` with a *common* lift to `W_X` and equal `U`-components are equal, because `e` is an
isomorphism and a point of `U ×_X W_X` is determined by its two components. On a test object with
no lift to `X` this says nothing, and `Stacks.Etale.eq_of_descentRel` is what covers that case:
pass to `Z ×_Y X`, where the tautological lift exists, and descend the resulting equality along
the surjection `Z ×_Y X ⟶ Z` by
`AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_etale`. Those two statements discharge the
extensionality hypothesis of `AlgebraicGeometry.exists_transition_of_pullbackIso_of_rel`, whose
remaining inputs are the gluing isomorphism of
`Stacks.Etale.exists_gluing_of_descentIso` and its characterization; so the cocycle condition
holds, `T` carries a descent datum relative to `w`, and the datum is effective by
Stacks Project, Tag 02W8 in the form
`AlgebraicGeometry.DescentDatum.isEffective_of_isSeparated_of_locallyQuasiFinite`.

That produces a scheme `V` over `Y` with `T = W ×_Y V`, étale over `Y` by fppf descent of
étaleness, and a projection `r : T ⟶ V` which
`AlgebraicGeometry.DescentDatum.Descended.proj_act` says is invariant for the gluing action.
The invariance is exactly what makes `e.inv ≫ pr_T ≫ r : U ×_X W_X ⟶ V` compatible for the
étale covering `U ×_X W_X ⟶ U`, which is an effective epimorphism because it is surjective, flat
and locally of finite presentation; so that morphism descends to `ρ : U ⟶ V`. The resulting
comparison `c : U ⟶ V ×_Y X` becomes an isomorphism after base change along the surjection
`W_X ⟶ X`, where it is `e`, and
`AlgebraicGeometry.isIso_of_etale_of_isPullback_id` turns that into an isomorphism.

## Main definitions

* `Stacks.Etale.DescentRel` — two generalized points of `T` have the same `U`-component at every
  compatible lift of the test object to `X`, and the same image in `Y`.

## Main results

* `Stacks.Etale.eq_of_descentUComp_eq` — extensionality at a fixed lift.
* `Stacks.Etale.eq_of_descentRel` — extensionality for the relation, at an arbitrary test object.
* `Stacks.Etale.exists_affine_etale_pullback_iso_of_descentIso` — **the descent.** The data left
  over by `Stacks.Etale.exists_affine_etale_descent_of_surjective` descends `U` along `f`.
* `Stacks.Etale.essSurjAffineEtalePullback` — **the affine case**, unconditionally: the
  hypothesis `Stacks.Etale.EssSurjAffineEtalePullback` carried throughout
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance` is a theorem.
* `Stacks.Etale.exists_etale_pullback_iso` — essential surjectivity for a scheme étale over `X`
  which is not assumed affine.
* `Stacks.Etale.affineEtalePullback_isEquivalence` — **Stacks Project, Tag 04E0** in full.
* `Stacks.Etale.etalePullback_isEquivalence` — **Stacks Project, Tag 04DZ** in full.

## Implementation notes

The relation `Stacks.Etale.DescentRel` names the test object of the two points it relates and
quantifies over factorisations `(c₁, c₂) = (γ ≫ a₁, γ ≫ a₂)` instead of over `γ` alone. The two
formulations are equivalent, but this one is stable under precomposition without rewriting under
the dependent proof argument of `Stacks.Etale.descentUComp`.

`Stacks.Etale.exists_affine_etale_pullback_iso_of_descentIso` does not use
`AlgebraicGeometry.isPullback_descentUComp`: the extensionality it needs at a fixed lift is a
two-component `CategoryTheory.Limits.pullback.hom_ext` through `e`, which needs no hypothesis on
`f`, on `p` or on `w` at all.

The descended scheme is read off `AlgebraicGeometry.DescentDatum.Descended` rather than from
`AlgebraicGeometry.DescentData.exists_descent_of_isEffective_of_rel`, because the invariance of
the projection that the final identification needs is the implication opposite to the one that
statement delivers: it must be known that points with the same `U`-component have the same image
in `V`, and that is `AlgebraicGeometry.DescentDatum.Descended.proj_act` together with the
relation.

## References

* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Etale

variable {X Y : Scheme.{u}}

/-- **Extensionality of the `U`-component at a fixed lift.** Let `e` identify the base change of
`T` to `W_X := X ×_Y W` with the base change of `U` to `W_X`, over `W_X`. Two generalized points
of `T` which admit one and the same lift `ζ` of their image in `W` to `W_X`, and whose
`U`-components at `ζ` agree, are equal.

Through `e`, the pair of a point of `T` and a lift of it is a point of `U ×_X W_X`, which is
determined by its two components; the second component is `ζ` for both, by `he`, and the first is
the `U`-component. No hypothesis is needed on `f`, on `p` or on `w`. -/
theorem eq_of_descentUComp_eq (f : X ⟶ Y) {U W T : Scheme.{u}} (p : U ⟶ X) (w : W ⟶ Y)
    (t : T ⟶ W) (e : pullback t (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd t (pullback.snd f w))
    {Z : Scheme.{u}} (a₁ a₂ : Z ⟶ T) (ζ : Z ⟶ pullback f w)
    (h₁ : a₁ ≫ t = ζ ≫ pullback.snd f w) (h₂ : a₂ ≫ t = ζ ≫ pullback.snd f w)
    (hU : descentUComp f p w t e a₁ ζ h₁ = descentUComp f p w t e a₂ ζ h₂) : a₁ = a₂ := by
  have key : pullback.lift a₁ ζ h₁ = pullback.lift a₂ ζ h₂ := by
    rw [← cancel_mono e.hom]
    refine pullback.hom_ext ?_ ?_
    · simpa only [descentUComp, Category.assoc] using hU
    · rw [Category.assoc, Category.assoc, he, pullback.lift_snd, pullback.lift_snd]
  simpa only [pullback.lift_fst] using key =≫ pullback.fst t (pullback.snd f w)

/-- **The relation on generalized points of `T`.** Two generalized points `a₁ a₂ : Z ⟶ T` are
related when they have the same image in `Y` and, for every factorisation of a pair of points of
`T` through them and every pair of lifts to `W_X := X ×_Y W` with the same `X`-component, the two
`U`-components agree.

The relation is an equivalence relation stable under precomposition
(`Stacks.Etale.DescentRel.refl`, `Stacks.Etale.DescentRel.symm`,
`Stacks.Etale.DescentRel.trans`, `Stacks.Etale.DescentRel.comp`) and it is the relation for which
the gluing isomorphism of `Stacks.Etale.exists_gluing_of_descentIso` relates a point to its
translate. The equality of the images in `Y` is what makes the relation transitive: it is what
produces the intermediate lift. The equality of the images in `W` must *not* be added — the
gluing action moves a point from one chart to the other, and the third conclusion of
`Stacks.Etale.exists_gluing_of_descentIso` would become false. -/
def DescentRel (f : X ⟶ Y) {U W T : Scheme.{u}} (p : U ⟶ X) (w : W ⟶ Y) (t : T ⟶ W)
    (e : pullback t (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    {Z : Scheme.{u}} (a₁ a₂ : Z ⟶ T) : Prop :=
  a₁ ≫ t ≫ w = a₂ ≫ t ≫ w ∧
    ∀ {Z' : Scheme.{u}} (c₁ c₂ : Z' ⟶ T) (ζ₁ ζ₂ : Z' ⟶ pullback f w)
      (h₁ : c₁ ≫ t = ζ₁ ≫ pullback.snd f w) (h₂ : c₂ ≫ t = ζ₂ ≫ pullback.snd f w),
      (∃ γ : Z' ⟶ Z, c₁ = γ ≫ a₁ ∧ c₂ = γ ≫ a₂) →
      ζ₁ ≫ pullback.fst f w = ζ₂ ≫ pullback.fst f w →
      descentUComp f p w t e c₁ ζ₁ h₁ = descentUComp f p w t e c₂ ζ₂ h₂

variable {U W T : Scheme.{u}} {f : X ⟶ Y} {p : U ⟶ X} {w : W ⟶ Y} {t : T ⟶ W}
  {e : pullback t (pullback.snd f w) ≅ pullback p (pullback.fst f w)}

/-- A lift to `X ×_Y W` of a generalized point of `T` is determined by its `X`-component: its
`W`-component is the image of the point. -/
theorem lift_eq_of_fst_eq {Z : Scheme.{u}} {a : Z ⟶ T} {ζ₁ ζ₂ : Z ⟶ pullback f w}
    (h₁ : a ≫ t = ζ₁ ≫ pullback.snd f w) (h₂ : a ≫ t = ζ₂ ≫ pullback.snd f w)
    (hx : ζ₁ ≫ pullback.fst f w = ζ₂ ≫ pullback.fst f w) : ζ₁ = ζ₂ :=
  pullback.hom_ext hx (by rw [← h₁, ← h₂])

/-- The relation is reflexive: for a fixed point of `T`, two lifts with the same `X`-component
coincide. -/
theorem DescentRel.refl {Z : Scheme.{u}} (a : Z ⟶ T) : DescentRel f p w t e a a := by
  refine ⟨rfl, ?_⟩
  rintro Z' c₁ c₂ ζ₁ ζ₂ h₁ h₂ ⟨γ, rfl, rfl⟩ hx
  obtain rfl : ζ₁ = ζ₂ := lift_eq_of_fst_eq h₁ h₂ hx
  rfl

/-- The relation is symmetric. -/
theorem DescentRel.symm {Z : Scheme.{u}} {a₁ a₂ : Z ⟶ T}
    (h : DescentRel f p w t e a₁ a₂) : DescentRel f p w t e a₂ a₁ := by
  refine ⟨h.1.symm, ?_⟩
  rintro Z' c₁ c₂ ζ₁ ζ₂ h₁ h₂ ⟨γ, hc₁, hc₂⟩ hx
  exact (h.2 c₂ c₁ ζ₂ ζ₁ h₂ h₁ ⟨γ, hc₂, hc₁⟩ hx.symm).symm

/-- The relation is transitive. The lift of the middle point that chains the two instances is
built from the common `X`-component and the image of that point in `W`; it exists precisely
because the three points have the same image in `Y`. -/
theorem DescentRel.trans {Z : Scheme.{u}} {a₁ a₂ a₃ : Z ⟶ T}
    (h₁₂ : DescentRel f p w t e a₁ a₂) (h₂₃ : DescentRel f p w t e a₂ a₃) :
    DescentRel f p w t e a₁ a₃ := by
  refine ⟨h₁₂.1.trans h₂₃.1, ?_⟩
  rintro Z' c₁ c₃ ζ₁ ζ₃ h₁ h₃ ⟨γ, hc₁, hc₃⟩ hx
  have hcond : pullback.fst f w ≫ f = pullback.snd f w ≫ w := pullback.condition
  have hz : (ζ₁ ≫ pullback.fst f w) ≫ f = ((γ ≫ a₂) ≫ t) ≫ w := by
    rw [Category.assoc, hcond, ← Category.assoc, ← h₁, hc₁]
    simp only [Category.assoc, h₁₂.1]
  refine (h₁₂.2 c₁ (γ ≫ a₂) ζ₁ (pullback.lift (ζ₁ ≫ pullback.fst f w) ((γ ≫ a₂) ≫ t) hz)
    h₁ (pullback.lift_snd _ _ _).symm ⟨γ, hc₁, rfl⟩ (pullback.lift_fst _ _ _).symm).trans ?_
  exact h₂₃.2 (γ ≫ a₂) c₃ _ ζ₃ (pullback.lift_snd _ _ _).symm h₃ ⟨γ, rfl, hc₃⟩
    (by rwa [pullback.lift_fst])

/-- The relation is stable under precomposition. -/
theorem DescentRel.comp {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) {a₁ a₂ : Z ⟶ T}
    (h : DescentRel f p w t e a₁ a₂) : DescentRel f p w t e (k ≫ a₁) (k ≫ a₂) := by
  refine ⟨by simp only [Category.assoc, h.1], ?_⟩
  rintro Z'' c₁ c₂ ζ₁ ζ₂ h₁ h₂ ⟨γ, hc₁, hc₂⟩ hx
  exact h.2 c₁ c₂ ζ₁ ζ₂ h₁ h₂ ⟨γ ≫ k, by rw [hc₁, Category.assoc], by rw [hc₂, Category.assoc]⟩ hx

/-- **Extensionality for the relation, at an arbitrary test object.** Let `f` be a universal
homeomorphism and `t` étale. Two generalized points of `T` with the same image in `W` which are
related by `Stacks.Etale.DescentRel` are equal.

The test object need not admit a lift to `X`, so `Stacks.Etale.eq_of_descentUComp_eq` does not
apply to it directly. It does apply to `Z ×_Y X`, which carries the tautological lift, and
`Z ×_Y X ⟶ Z` is surjective, being a base change of `f`; so
`AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_etale` descends the equality. This is the
extensionality hypothesis of
`AlgebraicGeometry.exists_transition_of_pullbackIso_of_rel`. -/
theorem eq_of_descentRel [UniversalHomeomorphism f] [Etale t]
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd t (pullback.snd f w))
    {Z : Scheme.{u}} {a₁ a₂ : Z ⟶ T} (ht : a₁ ≫ t = a₂ ≫ t)
    (hR : DescentRel f p w t e a₁ a₂) : a₁ = a₂ := by
  obtain ⟨-, -, _⟩ :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).mp inferInstance
  have hcond : pullback.fst (a₁ ≫ t ≫ w) f ≫ (a₁ ≫ t ≫ w) =
      pullback.snd (a₁ ≫ t ≫ w) f ≫ f := pullback.condition
  have hζc : pullback.snd (a₁ ≫ t ≫ w) f ≫ f =
      (pullback.fst (a₁ ≫ t ≫ w) f ≫ a₁ ≫ t) ≫ w := by
    rw [← hcond]
    simp only [Category.assoc]
  set γ : pullback (a₁ ≫ t ≫ w) f ⟶ Z := pullback.fst (a₁ ≫ t ≫ w) f with hγ
  set ζ : pullback (a₁ ≫ t ≫ w) f ⟶ pullback f w :=
    pullback.lift (pullback.snd (a₁ ≫ t ≫ w) f) (γ ≫ a₁ ≫ t) hζc
  have hζ2 : ζ ≫ pullback.snd f w = γ ≫ a₁ ≫ t := pullback.lift_snd _ _ _
  have h₁ : (γ ≫ a₁) ≫ t = ζ ≫ pullback.snd f w := by rw [hζ2, Category.assoc]
  have h₂ : (γ ≫ a₂) ≫ t = ζ ≫ pullback.snd f w := by
    rw [hζ2, Category.assoc, ht]
  have _hsurjγ : Surjective γ := by
    rw [hγ]
    infer_instance
  exact eq_of_comp_eq_of_surjective_of_etale t γ a₁ a₂ ht
    (eq_of_descentUComp_eq f p w t e he _ _ ζ h₁ h₂ (hR.2 _ _ ζ ζ h₁ h₂ ⟨γ, rfl, rfl⟩ rfl))

/-- A surjective flat morphism locally of finite presentation is an effective epimorphism. -/
private theorem effectiveEpi_of_flat_of_surjective {A B : Scheme.{u}} (g : A ⟶ B) [Flat g]
    [Surjective g] [LocallyOfFinitePresentation g] : EffectiveEpi g := by
  apply (Sieve.effectiveEpimorphic_singleton g).mp
  apply (Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda _).mpr
  intro Z
  apply (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology) (P := yoneda.obj Z)).isSheafFor
  exact Precoverage.generate_mem_toGrothendieck g.singleton_mem_fppfPrecoverage

/-- **One descent along a surjective étale covering of the target closes the inductive step.**
Let `f : X ⟶ Y` be a universal homeomorphism of affine schemes, let `p : U ⟶ X` be étale with `U`
affine, let `w : W ⟶ Y` be étale and surjective with `W` affine and let `t : T ⟶ W` be étale with
`T` affine. If the base change of `T` to `W_X := X ×_Y W` is identified over `W_X` with the base
change of `U`, then `U` is, over `X`, the base change along `f` of an affine scheme étale over
`Y`.

This is the data `Stacks.Etale.exists_affine_etale_descent_of_surjective` leaves over, so it is
what remains of the inductive step of the second proof of Stacks Project, Tag 04DZ. The gluing
isomorphism is `Stacks.Etale.exists_gluing_of_descentIso`, the cocycle condition is
`AlgebraicGeometry.exists_transition_of_pullbackIso_of_rel` fed with
`Stacks.Etale.DescentRel` and `Stacks.Etale.eq_of_descentRel`, effectivity is Stacks Project,
Tag 02W8, and the identification of the base change of the descended scheme with `U` is the
descent of a morphism along the étale covering `U ×_X W_X ⟶ U`, which is an effective
epimorphism by Stacks Project, Tag 023Q. -/
theorem exists_affine_etale_pullback_iso_of_descentIso (f : X ⟶ Y) [UniversalHomeomorphism f]
    [IsAffine X] [IsAffine Y] {U W T : Scheme.{u}} (p : U ⟶ X) [Etale p] [IsAffine U]
    (w : W ⟶ Y) [Etale w] [IsAffine W] [Surjective w] (t : T ⟶ W) [Etale t] [IsAffine T]
    (e : pullback t (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd t (pullback.snd f w)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (_ : IsAffine V) (e' : pullback q f ≅ U),
      e'.hom ≫ p = pullback.snd q f := by
  have hfw : pullback.fst f w ≫ f = pullback.snd f w ≫ w := pullback.condition
  have hN : pullback.fst p (pullback.fst f w) ≫ p =
      pullback.snd p (pullback.fst f w) ≫ pullback.fst f w := pullback.condition
  have hM : pullback.fst t (pullback.snd f w) ≫ t =
      pullback.snd t (pullback.snd f w) ≫ pullback.snd f w := pullback.condition
  have hei : e.inv ≫ pullback.snd t (pullback.snd f w) = pullback.snd p (pullback.fst f w) := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  -- the gluing isomorphism and the cocycle condition it satisfies
  obtain ⟨Θ, hΘ1, hΘ2, hΘ3⟩ := exists_gluing_of_descentIso f p w t e he
  have hΘ3' : DescentRel f p w t e (Θ.hom ≫ pullback.snd w (t ≫ w))
      (pullback.fst (t ≫ w) w) := by
    refine ⟨?_, ?_⟩
    · have h2 : pullback.fst (t ≫ w) w ≫ t ≫ w = pullback.snd (t ≫ w) w ≫ w :=
        pullback.condition
      have h1 : (Θ.hom ≫ pullback.snd w (t ≫ w)) ≫ t ≫ w = pullback.snd (t ≫ w) w ≫ w := by
        rw [← Category.assoc (Θ.hom ≫ pullback.snd w (t ≫ w)), Category.assoc Θ.hom, hΘ2]
      rw [h1, h2]
    · rintro Z' c₁ c₂ ζ₁ ζ₂ h₁ h₂ ⟨γ, rfl, rfl⟩ hx
      exact hΘ3 γ ζ₂ ζ₁ h₂ h₁ hx.symm
  have hext : ∀ a₁ a₂ : ((Over.map w).obj (Over.mk t) ⨯ Over.mk w) ⨯ Over.mk w ⟶
      (Over.map w).obj (Over.mk t),
      DescentRel f p w t e a₁.left a₂.left → a₁.left ≫ t = a₂.left ≫ t → a₁ = a₂ :=
    fun _ _ hR hcomp ↦ Over.OverMorphism.ext (eq_of_descentRel he hcomp hR)
  obtain ⟨φ, hcoc, hact⟩ := exists_transition_of_pullbackIso_of_rel w t
    (fun {_} a₁ a₂ ↦ DescentRel f p w t e a₁ a₂) (fun k _ _ h ↦ DescentRel.comp k h)
    (fun _ _ h ↦ h.symm) (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) Θ hΘ1 hΘ2 hΘ3' hext
  -- the descent datum, its effectivity and the descended scheme
  set D : DescentDatum w := DescentDatum.mk' (Over.mk t) φ hcoc
  have hover : (structureMap w D.over).left = t := rfl
  have hactD : ∀ {Z : Over Y} (v : Z ⟶ (Over.map w).obj D.over) (x : Z ⟶ Over.mk w),
      DescentRel f p w t e (D.act v x).left v.left := hact
  obtain ⟨Q⟩ := DescentDatum.nonempty_descended_of_isEffective
    (DescentDatum.isEffective_of_isSeparated_of_locallyQuasiFinite D
      (show IsSeparated t from inferInstance) (show LocallyQuasiFinite t from inferInstance)
      (show LocallyOfFiniteType t from inferInstance))
  have hQ : IsPullback t Q.proj w Q.base.hom := Q.isPullback
  have _hw₀ : Etale Q.base.hom :=
    Space.etale_descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation.of_isPullback
      hQ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  set g₀ : pullback p (pullback.fst f w) ⟶ Q.base.left :=
    e.inv ≫ pullback.fst t (pullback.snd f w) ≫ Q.proj with hg₀
  -- the two chart-free identities the whole argument runs on, for a point of the covering
  have hpt : ∀ {Z : Scheme.{u}} (k : Z ⟶ pullback p (pullback.fst f w)),
      (k ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) ≫ t =
        (k ≫ pullback.snd p (pullback.fst f w)) ≫ pullback.snd f w := fun k ↦ by
    rw [Category.assoc, Category.assoc, hM, ← Category.assoc e.inv, hei, Category.assoc]
  have hxc : ∀ {Z : Scheme.{u}} (k : Z ⟶ pullback p (pullback.fst f w)),
      (k ≫ pullback.snd p (pullback.fst f w)) ≫ pullback.fst f w =
        (k ≫ pullback.fst p (pullback.fst f w)) ≫ p :=
    fun k ↦ by simpa only [Category.assoc] using (congrArg (k ≫ ·) hN).symm
  have hYk : ∀ {Z : Scheme.{u}} (k : Z ⟶ pullback p (pullback.fst f w)),
      (k ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) ≫ t ≫ w =
        (k ≫ pullback.fst p (pullback.fst f w)) ≫ p ≫ f := fun k ↦ by
    rw [← Category.assoc _ t, hpt, Category.assoc, ← hfw, ← Category.assoc, hxc, Category.assoc]
  have hUcomp : ∀ {Z : Scheme.{u}} (k : Z ⟶ pullback p (pullback.fst f w)),
      descentUComp f p w t e (k ≫ e.inv ≫ pullback.fst t (pullback.snd f w))
          (k ≫ pullback.snd p (pullback.fst f w)) (hpt k) =
        k ≫ pullback.fst p (pullback.fst f w) := by
    intro Z k
    have hl : pullback.lift (k ≫ e.inv ≫ pullback.fst t (pullback.snd f w))
        (k ≫ pullback.snd p (pullback.fst f w)) (hpt k) = k ≫ e.inv := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, Category.assoc]
      · rw [pullback.lift_snd, Category.assoc, hei]
    simp only [descentUComp, hl, Category.assoc, Iso.inv_hom_id_assoc]
  -- the `V`-valued morphism on the covering is compatible
  have hcompat : ∀ {Z : Scheme.{u}} (k₁ k₂ : Z ⟶ pullback p (pullback.fst f w)),
      k₁ ≫ pullback.fst p (pullback.fst f w) = k₂ ≫ pullback.fst p (pullback.fst f w) →
      k₁ ≫ g₀ = k₂ ≫ g₀ := by
    intro Z k₁ k₂ hk
    have hx : (k₁ ≫ pullback.snd p (pullback.fst f w)) ≫ pullback.fst f w =
        (k₂ ≫ pullback.snd p (pullback.fst f w)) ≫ pullback.fst f w := by
      rw [hxc, hxc, hk]
    have hY : ((k₂ ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) ≫ t) ≫ w =
        (k₁ ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) ≫ t ≫ w := by
      rw [Category.assoc, hYk, hYk, hk]
    -- the gluing action moves the first point onto the chart of the second
    set Z₀ : Over Y :=
      Over.mk ((k₁ ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) ≫ t ≫ w)
    set v : Z₀ ⟶ (Over.map w).obj D.over :=
      Over.homMk (k₁ ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) rfl
    set x : Z₀ ⟶ Over.mk w :=
      Over.homMk ((k₂ ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) ≫ t) hY with hx₀
    have hact1 : (D.act v x).left ≫ t =
        (k₂ ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) ≫ t := by
      simpa only [Over.comp_left, hover, hx₀, Over.homMk_left] using
        congrArg (fun m ↦ Over.Hom.left m) (D.act_comp_structureMap v x)
    have hact2 : (D.act v x).left ≫ Q.proj =
        (k₁ ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) ≫ Q.proj := Q.proj_act v x
    have hreleq := (hactD v x).2 ((D.act v x).left)
      (k₁ ≫ e.inv ≫ pullback.fst t (pullback.snd f w))
      (k₂ ≫ pullback.snd p (pullback.fst f w)) (k₁ ≫ pullback.snd p (pullback.fst f w))
      (hact1.trans (hpt k₂)) (hpt k₁)
      ⟨𝟙 Z₀.left, (Category.id_comp _).symm, (Category.id_comp _).symm⟩ hx.symm
    have hfinal : (D.act v x).left = k₂ ≫ e.inv ≫ pullback.fst t (pullback.snd f w) := by
      refine eq_of_descentUComp_eq f p w t e he _ _ (k₂ ≫ pullback.snd p (pullback.fst f w))
        (hact1.trans (hpt k₂)) (hpt k₂) ?_
      rw [hreleq, hUcomp, hUcomp, hk]
    have hres : (k₂ ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) ≫ Q.proj =
        (k₁ ≫ e.inv ≫ pullback.fst t (pullback.snd f w)) ≫ Q.proj := by
      rwa [← hfinal]
    rw [hg₀]
    simpa only [Category.assoc] using hres.symm
  -- the comparison morphism, descended from the covering
  have _hepi : EffectiveEpi (pullback.fst p (pullback.fst f w)) :=
    effectiveEpi_of_flat_of_surjective _
  obtain ⟨ρ, hρ⟩ : ∃ ρ : U ⟶ Q.base.left, pullback.fst p (pullback.fst f w) ≫ ρ = g₀ :=
    ⟨EffectiveEpi.desc _ g₀ hcompat, EffectiveEpi.fac _ g₀ hcompat⟩
  have hρw : ρ ≫ Q.base.hom = p ≫ f := by
    rw [← cancel_epi (pullback.fst p (pullback.fst f w)), ← Category.assoc, hρ, hg₀]
    simpa only [Category.assoc, ← hQ.w, Category.id_comp] using hYk (𝟙 _)
  set c : U ⟶ pullback Q.base.hom f := pullback.lift ρ p hρw
  have hcfst : c ≫ pullback.fst Q.base.hom f = ρ := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd Q.base.hom f = p := pullback.lift_snd _ _ _
  -- after base change along the covering, the comparison morphism is an isomorphism
  have hκc : (pullback.fst t (pullback.snd f w) ≫ Q.proj) ≫ Q.base.hom =
      (pullback.snd t (pullback.snd f w) ≫ pullback.fst f w) ≫ f := by
    rw [Category.assoc, ← hQ.w, ← Category.assoc, hM, Category.assoc, Category.assoc, ← hfw]
  set κ : pullback t (pullback.snd f w) ⟶ pullback Q.base.hom f :=
    pullback.lift (pullback.fst t (pullback.snd f w) ≫ Q.proj)
      (pullback.snd t (pullback.snd f w) ≫ pullback.fst f w) hκc
  have hκ1 : κ ≫ pullback.fst Q.base.hom f = pullback.fst t (pullback.snd f w) ≫ Q.proj :=
    pullback.lift_fst _ _ _
  have hκ2 : κ ≫ pullback.snd Q.base.hom f =
      pullback.snd t (pullback.snd f w) ≫ pullback.fst f w := pullback.lift_snd _ _ _
  have hbig : IsPullback (pullback.fst t (pullback.snd f w) ≫ Q.proj)
      (pullback.snd t (pullback.snd f w)) Q.base.hom (pullback.fst f w ≫ f) := by
    have h := (IsPullback.of_hasPullback t (pullback.snd f w)).paste_horiz hQ.flip
    rwa [← hfw] at h
  have hMsq : IsPullback κ (pullback.snd t (pullback.snd f w)) (pullback.snd Q.base.hom f)
      (pullback.fst f w) := by
    refine IsPullback.of_right ?_ hκ2 (IsPullback.of_hasPullback Q.base.hom f)
    rwa [hκ1]
  have _hκsurj : Surjective κ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) hMsq.flip
      inferInstance
  have hNsq : IsPullback (e.hom ≫ pullback.fst p (pullback.fst f w))
      (pullback.snd t (pullback.snd f w)) p (pullback.fst f w) := by
    have hiso : IsPullback e.hom (pullback.snd t (pullback.snd f w))
        (pullback.snd p (pullback.fst f w)) (𝟙 (pullback f w)) :=
      IsPullback.of_horiz_isIso ⟨by rwa [Category.comp_id]⟩
    have h := hiso.paste_horiz (IsPullback.of_hasPullback p (pullback.fst f w))
    rwa [Category.id_comp] at h
  have hidsq : IsPullback (e.hom ≫ pullback.fst p (pullback.fst f w))
      (𝟙 (pullback t (pullback.snd f w))) c κ := by
    refine IsPullback.of_bot ?_ ?_ hMsq
    · rwa [Category.id_comp, hcsnd]
    · rw [Category.id_comp]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hcfst, hκ1, Category.assoc, hρ, hg₀, Iso.hom_inv_id_assoc]
      · rw [Category.assoc, hcsnd, hκ2, Category.assoc, hN, ← Category.assoc, he]
  have _hec : Etale c := by
    have _ : Etale (c ≫ pullback.snd Q.base.hom f) := by
      rw [hcsnd]
      infer_instance
    exact Etale.of_comp c (pullback.snd Q.base.hom f)
  have _hisoc : IsIso c :=
    isIso_of_etale_of_isPullback_id c κ (e.hom ≫ pullback.fst p (pullback.fst f w)) hidsq
  have _haffpb : IsAffine (pullback Q.base.hom f) := IsAffine.of_isIso (inv c)
  refine ⟨Q.base.left, Q.base.hom, inferInstance,
    isAffine_of_isAffine_pullback f Q.base.hom inferInstance, (asIso c).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, ← hcsnd, IsIso.inv_hom_id_assoc]

/-! ### The affine case of topological invariance, unconditionally -/

/-- **The inductive step of the affine case, for a surjective étale morphism.** Granted the
affine case of Stacks Project, Tag 04E0 for a bound of `n` on the degrees of the fibres, a
surjective étale `p : U ⟶ X` with `U` affine and fibre degrees bounded by `n + 1` descends along
a universal homeomorphism `f : X ⟶ Y` of affine schemes.

`Stacks.Etale.exists_affine_etale_descent_of_surjective` produces the covering `W ⟶ Y` and the
étale `W`-scheme `T`, and
`Stacks.Etale.exists_affine_etale_pullback_iso_of_descentIso` descends it. This is the hypothesis
of `Stacks.Etale.essSurjAffineEtalePullback_of_inductiveStep_surjective`. -/
theorem exists_affine_etale_pullback_iso_of_surjective (n : ℕ)
    (ih : EssSurjAffineEtalePullbackBounded.{u} n) (f : X ⟶ Y) [UniversalHomeomorphism f]
    [IsAffine X] [IsAffine Y] {U : Scheme.{u}} (p : U ⟶ X) [Etale p] [IsAffine U]
    [Surjective p] (hdeg : BoundsFiberDegrees p ((n + 1 : ℕ) : ℤ)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (_ : IsAffine V) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f := by
  obtain ⟨W, w, _, _, _, T, t, _, _, e, he⟩ :=
    exists_affine_etale_descent_of_surjective n ih f p hdeg
  exact exists_affine_etale_pullback_iso_of_descentIso f p w t e he

/-- **The affine case of topological invariance of the small étale site.** For a universal
homeomorphism `f : X ⟶ Y` between affine schemes, every affine scheme étale over `X` is, over
`X`, the base change along `f` of an affine scheme étale over `Y`.

This is the essential surjectivity of the correspondence displayed as Stacks Project, Tag 04E0,
and the hypothesis `Stacks.Etale.EssSurjAffineEtalePullback` which
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.AffineCase` carries
throughout. The source's induction on a bound for the degrees of the fibres is
`Stacks.Etale.essSurjAffineEtalePullback_of_inductiveStep_surjective`, whose step is
`Stacks.Etale.exists_affine_etale_pullback_iso_of_surjective`. -/
@[sga "4 VIII 1.1" "partial", sga "4½ Th_finitude 2.7" "Affine object descent"]
theorem essSurjAffineEtalePullback : EssSurjAffineEtalePullback.{u} := by
  refine essSurjAffineEtalePullback_of_inductiveStep_surjective ?_
  intro n _ ih X Y f _ _ _ U p _ _ _ hdeg
  exact exists_affine_etale_pullback_iso_of_surjective n ih f p hdeg

/-- **Essential surjectivity of base change on small étale sites.** Let `f : X ⟶ Y` be a
universal homeomorphism. Every scheme étale over `X`, affine or not, is over `X` the base change
along `f` of a scheme étale over `Y`.

This is `Stacks.Etale.exists_etale_pullback_iso_of_essSurjAffine` with its hypothesis
discharged by `Stacks.Etale.essSurjAffineEtalePullback`. -/
@[sga "4½ Th_finitude 2.7" "partial"]
theorem exists_etale_pullback_iso (f : X ⟶ Y) [UniversalHomeomorphism f] (U : Scheme.{u})
    (p : U ⟶ X) (hp : Etale p) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f :=
  exists_etale_pullback_iso_of_essSurjAffine essSurjAffineEtalePullback f U p hp

/-- **The affine correspondence of Stacks Project, Tag 04E0.** Let `f : X ⟶ Y` be a universal
homeomorphism of affine schemes. Base change along `f` carries an affine scheme étale over `Y` to
an affine scheme étale over `X`, and the induced functor between the affine objects of the two
small étale sites is an equivalence.

This is `Stacks.Etale.affineEtalePullback_isEquivalence_of_essSurjAffine` with its hypothesis
discharged by `Stacks.Etale.essSurjAffineEtalePullback`. -/
@[stacks 04E0 "the displayed correspondence, in full and unconditionally. Its three clauses are
covered as follows. Preservation of affineness and full faithfulness are
`Stacks.Etale.affineEtalePullback_fullyFaithful`, which carries the tag too. Essential
surjectivity -- the content the source proves, by induction on a bound for the degree of the
fibres of an etale morphism of affine schemes, descending at each step by effectivity of
descent -- is `Stacks.Etale.essSurjAffineEtalePullback`. This declaration is the equivalence the
three together give, assembled by
`Stacks.Etale.affineEtalePullback_isEquivalence_of_essSurjAffine`. The source's induction runs
through `Stacks.Etale.essSurjAffineEtalePullback_of_inductiveStep_surjective`, whose step is
`Stacks.Etale.exists_affine_etale_pullback_iso_of_surjective`; its one descent along an etale
covering of the target is
`Stacks.Etale.exists_affine_etale_pullback_iso_of_descentIso`, where effectivity enters as
Tag 02W8 rather than as the source's Tag 0245."]
theorem affineEtalePullback_isEquivalence (f : X ⟶ Y) [UniversalHomeomorphism f]
    [IsAffine X] [IsAffine Y] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    let F : Y.Etale ⥤ X.Etale :=
      MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ f
    let PY : ObjectProperty Y.Etale := fun V ↦ IsAffine V.left
    let PX : ObjectProperty X.Etale := fun U ↦ IsAffine U.left
    ∃ h : ∀ V : PY.FullSubcategory, PX (F.obj V.obj),
      (PX.lift (PY.ι ⋙ F) h).IsEquivalence :=
  affineEtalePullback_isEquivalence_of_essSurjAffine essSurjAffineEtalePullback f

/-- **Topological invariance of the small étale site.** Let `f : X ⟶ Y` be integral, universally
injective and surjective. Then `V ↦ X ×_Y V` is an equivalence from the category of schemes étale
over `Y` to the category of schemes étale over `X`.

Essential surjectivity is `Stacks.Etale.exists_etale_pullback_iso_of_essSurjAffine` with its
hypothesis discharged by `Stacks.Etale.essSurjAffineEtalePullback`. -/
@[stacks 04DZ "the equivalence, unconditionally. Full faithfulness is Tag 0BTY; essential
surjectivity is the affine case `Stacks.Etale.essSurjAffineEtalePullback` glued over an affine
cover by `Stacks.Etale.exists_etale_pullback_iso_of_essSurjAffine`. The name
`Stacks.Etale.etalePullback_isEquivalence_of_integral_universallyInjective_surjective` is an
alias of this declaration and keeps the tag as well.",
  ega "IV 18.1.2" "more general",
  sga "1 IX 4.10",
  sga "4 VIII 1.1" "partial"]
theorem etalePullback_isEquivalence (f : X ⟶ Y) [IsIntegralHom f]
    [UniversallyInjective f] [Surjective f] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f).IsEquivalence :=
  have : UniversalHomeomorphism f :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective f).2
      ⟨inferInstance, inferInstance, inferInstance⟩
  etalePullback_isEquivalence_of_forall_exists_pullback_iso f
    (exists_etale_pullback_iso_of_essSurjAffine essSurjAffineEtalePullback f)

/-- **Topological invariance of the small étale site.** Let `f : X ⟶ Y` be integral, universally
injective and surjective. Then `V ↦ X ×_Y V` is an equivalence from the category of schemes
étale over `Y` to the category of schemes étale over `X`. -/
@[stacks 04DZ "Full faithfulness is unconditional, from Tag 0BTY. A scheme etale over `X` is
covered by affine opens lying over affine opens of `Y`, and the glueing of Schemes 01JA and
01JC -- in this library `exists_etale_pullback_iso_of_descendedOpens_cover` -- assembles the
local descents into a global one. Essential surjectivity is thereby reduced to the affine case,
the essential surjectivity of the correspondence displayed as Tag 04E0, which is proved
unconditionally as `Stacks.Etale.essSurjAffineEtalePullback` by the source's induction on a
bound for the degree of the fibres of an etale morphism of affine schemes. This name is an alias
of `Stacks.Etale.etalePullback_isEquivalence`. The source's hypotheses are stated in their own
form, as integrality, universal injectivity and surjectivity, and converted by Tag 04DF."]
alias etalePullback_isEquivalence_of_integral_universallyInjective_surjective :=
  etalePullback_isEquivalence

end Stacks.Etale

end

end
