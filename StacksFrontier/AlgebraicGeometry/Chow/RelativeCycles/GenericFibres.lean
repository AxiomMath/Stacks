module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Injective
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation
public import StacksCore.Tactic.StacksAttribute

/-!
# A relative cycle is determined by its generic members

Let `S` be a locally Noetherian scheme and let `f : X ⟶ S` be locally of finite type. Two
relative `r`-cycles on `X/S` are equal as soon as their members over the generic points of the
irreducible components of `S` agree.

The reason is the valuative condition itself. Given `s ∈ S`, pick a generic point `η` of an
irreducible component of `S` specializing to `s` and, by Stacks 054F, a morphism
`g : Spec R ⟶ S` from the spectrum of a discrete valuation ring carrying the generic point to
`η` and the closed point to `s`. The valuative condition expresses the member of `g^*α` over the
closed point as the specialization of its member over the generic point, and the latter depends
only on `α_η`. So `α_s` and `β_s` have the same image under the base-change map
`Z_r(X_s) ⟶ Z_r(X'_0)` attached to the residue field extension `κ(0)/κ(s)`, and that map is
injective.

## Main results

* `Stacks.Chow.injective_baseChangeFiberCycle` — the base-change map on fibrewise cycle groups
  induced by an arbitrary morphism of bases is injective.
* `Stacks.Chow.IsRelativeCycle.eq_iff_eq_of_mem_genericPoints` — two relative `r`-cycles are
  equal if and only if they agree over the generic points of the irreducible components of the
  base.

## Implementation notes

Injectivity of the base-change map on fibrewise cycle groups factors through the two halves of
`Stacks.Chow.baseChangeFiberCycle`: the base change of cycles along the residue field extension,
injective by `Stacks.Chow.injective_baseChangeCyclePullback_of_surjective` because the spectrum
of a field extension surjects onto the spectrum of the base field, and the transport of cycles
along the canonical isomorphism of fibres, injective because that isomorphism is surjective on
points.

Local Noetherianity of `S` enters only through Stacks 054F, which produces the discrete
valuation ring realizing a specialization. Local finiteness of type of `f` enters through the
cycle groups on the fibres and through the injectivity statement, whose proof uses that a fibre
of `f` is locally of finite type over the residue field of its base point.

The source states the result as an equivalence of two conditions; the implication from equality
to agreement over generic points is immediate, and the content is the converse.

## References

* [Stacks Project, Lemma 0H55](https://stacks.math.columbia.edu/tag/0H55)
* [Stacks Project, Lemma 054F](https://stacks.math.columbia.edu/tag/054F)
* [Stacks Project, Section 0H4E](https://stacks.math.columbia.edu/tag/0H4E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- Every point of a quasi-sober space is a specialization of the generic point of an
irreducible component. -/
private theorem exists_mem_genericPoints_specializes {A : Type*} [TopologicalSpace A]
    [QuasiSober A] (x : A) : ∃ η ∈ genericPoints A, η ⤳ x := by
  refine ⟨(genericPoints.ofComponent
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩).1,
    (genericPoints.ofComponent _).2, ?_⟩
  rw [specializes_iff_mem_closure, genericPoints.isGenericPoint_ofComponent]
  exact mem_irreducibleComponent

/-- Restriction of cycles along an open immersion which is surjective on points is injective:
every coefficient of the restricted cycle is a coefficient of the original one, and every point
of the ambient scheme is hit. -/
private theorem injective_cycleGroupRestrict_of_surjective (C : ChowSituation.{u})
    {Y U : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (j : U ⟶ Y) [IsOpenImmersion j] (hj : j ≫ sY = sU)
    (hsurj : Function.Surjective j.base) (k : ℤ) :
    Function.Injective (cycleGroupRestrict C sY sU j hj k) := by
  intro c d hcd
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  obtain ⟨z, rfl⟩ := hsurj y
  have h := congrArg (fun e : CycleGroup C sU k ↦ e.1 z) hcd
  simpa only [cycleGroupRestrict_apply] using h

/-- **Stacks Project, Section 0H4E.** The base-change homomorphism
`Z_r(X_{g t}) ⟶ Z_r((X ×_S S')_t)` on fibrewise cycle groups induced by an arbitrary morphism
`g : S' ⟶ S` is injective: the base change of cycles along the residue field extension
`κ(t)/κ(g t)` is injective because `Spec κ(t) ⟶ Spec κ(g t)` is surjective, and transport along
the canonical isomorphism of fibres is injective because that isomorphism is surjective. -/
theorem injective_baseChangeFiberCycle {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (t : S') (r : ℕ) : Function.Injective (baseChangeFiberCycle f g t r) := by
  have h₁ : Function.Injective (baseChangeCyclePullback (residueFieldBaseChangeSituation g t)
      (f.fiberToSpecResidueField (g t)) (r : ℤ)) :=
    injective_baseChangeCyclePullback_of_surjective (residueFieldBaseChangeSituation g t)
      (f.fiberToSpecResidueField (g t)) (r : ℤ)
  have h₂ := injective_cycleGroupRestrict_of_surjective (fieldChowSituation (S'.residueField t))
    (pullback.snd (f.fiberToSpecResidueField (g t)) (residueFieldBaseChangeSituation g t).g)
    ((pullback.snd f g).fiberToSpecResidueField t) (fibreBaseChangeIso f g t).hom
    (fibreBaseChangeIso_hom_snd f g t) (fibreBaseChangeIso f g t).hom.surjective (r : ℤ)
  exact fun a b hab ↦ h₁ (h₂ hab)

/-- **Stacks Project, Lemma 0H55.** Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be
locally of finite type and let `r ≥ 0`. Two relative `r`-cycles on `X/S` are equal if and only
if their members over the generic points of the irreducible components of `S` agree. -/
@[stacks 0H55]
theorem IsRelativeCycle.eq_iff_eq_of_mem_genericPoints {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (r : ℕ) {α β : FamilyOfCycles f r}
    (hα : IsRelativeCycle f r α) (hβ : IsRelativeCycle f r β) :
    α = β ↔ ∀ η ∈ genericPoints ↥S, α η = β η := by
  refine ⟨fun h η _ ↦ by rw [h], fun h ↦ funext fun s ↦ ?_⟩
  obtain ⟨η, hη, hspec⟩ := exists_mem_genericPoints_specializes s
  obtain ⟨R, _, _, _, g, hgη, hgs⟩ := exists_dvr_morphism_of_specializes S hspec
  subst hgs
  refine injective_baseChangeFiberCycle f g (IsLocalRing.closedPoint R) r ?_
  have e := baseChangeFamily_eq_baseChangeFiberCycle f g r
  refine (e α _).symm.trans (Eq.trans ?_ (e β _))
  have := h η hη
  rw [← hgη] at this
  rw [← hα R g, ← hβ R g, e, e, this]

end Stacks.Chow

end
