module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint

/-!
# The geometric fibre of an étale morphism is the set of lifts of the geometric point

Let `f : X ⟶ S` be étale and let `s` be a geometric point of `S`, with algebraically closed
residue field `Ω` and source `s̄ = Spec Ω`. The *geometric fibre* of `f` at `s` is the scheme
`X_s̄ = X ×_S s̄`, and its underlying set `|X_s̄|` is identified here with the set of lifts
`ū : s̄ ⟶ X` of `s`, that is, with the set of `ū` making `(X, ū)` an étale neighbourhood of `s`.

A lift `ū` is the same datum as a section of `X_s̄ ⟶ s̄`, and the identification sends such a
section to the point of `X_s̄` it hits. It is injective because a section of a morphism locally
of finite type over an algebraically closed field is determined by that point
(`AlgebraicGeometry.ext_of_apply_closedPoint_eq`), and surjective because `X_s̄ ⟶ s̄` is étale
and `Ω` is separably closed, so every point of `X_s̄` is hit by a section
(`AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`).

## Main definitions

* `AlgebraicGeometry.geometricFibreSection` — a lift of the geometric point, read as a section
  of the geometric fibre over the source of the geometric point.
* `AlgebraicGeometry.geometricFibrePoint` — the point of the geometric fibre that a lift hits.

## Main results

* `AlgebraicGeometry.geometricFibrePoint_bijective` — the lifts of the geometric point are in
  bijection with the points of the geometric fibre.
* `AlgebraicGeometry.geometricPointFiberObjEquivGeometricFibre` — the same bijection for an
  object of the small étale site, which is what identifies the two descriptions
  `U ↦ |U_s̄|` and `U ↦ {ū : (U, ū) is an étale neighbourhood of s̄}` of the fibre functor of
  Tag 04FM.

## Implementation notes

The bijection is pointwise in `X` (respectively in the object of the small étale site), which is
the form the source uses: it identifies the two readings of the set `u(U)` and then works with
the second. Making `U ↦ |U_s̄|` a functor on the small étale site would require the underlying
space of the geometric fibre to be functorial in `U`, which is not needed for Tag 04FM and is
not set up here.

## References

* [Stacks Project, Tag 04FM](https://stacks.math.columbia.edu/tag/04FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Fibre

variable {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (s : GeometricPoint S)

/-- A lift of a geometric point `s` along `f : X ⟶ S`, read as a section of the geometric fibre
`X ×_S s̄` over the source `s̄` of the geometric point. -/
def geometricFibreSection (p : {p : s.source ⟶ X // p ≫ f = s.hom}) :
    s.source ⟶ pullback f s.hom :=
  pullback.lift p.1 (𝟙 s.source) (by simpa using p.2)

omit [Etale f] in
/-- The section of the geometric fibre attached to a lift `p` composes with the first projection
`X ×_S s̄ ⟶ X` to `p`. -/
@[simp]
theorem geometricFibreSection_comp_fst (p : {p : s.source ⟶ X // p ≫ f = s.hom}) :
    geometricFibreSection f s p ≫ pullback.fst f s.hom = p.1 :=
  pullback.lift_fst _ _ _

omit [Etale f] in
/-- The section of the geometric fibre attached to a lift `p` is a section of the second
projection `X ×_S s̄ ⟶ s̄`. -/
@[simp]
theorem geometricFibreSection_comp_snd (p : {p : s.source ⟶ X // p ≫ f = s.hom}) :
    geometricFibreSection f s p ≫ pullback.snd f s.hom = 𝟙 s.source :=
  pullback.lift_snd _ _ _

/-- The point of the geometric fibre `X ×_S s̄` hit by a lift of the geometric point `s`. -/
def geometricFibrePoint (p : {p : s.source ⟶ X // p ≫ f = s.hom}) : ↥(pullback f s.hom) :=
  geometricFibreSection f s p default

/-- **The two descriptions of the fibre of a geometric point agree.** For `f : X ⟶ S` étale and
`s` a geometric point of `S`, the lifts `ū : s̄ ⟶ X` of `s` — equivalently, the `ū` making
`(X, ū)` an étale neighbourhood of `s` — are in bijection with the points of the underlying
space of the geometric fibre `X_s̄ = X ×_S s̄`.

Injectivity: a lift is recovered from its section of `X_s̄ ⟶ s̄`, and that section is determined
by the point of `X_s̄` it hits, because `X_s̄` is locally of finite type over the spectrum of the
algebraically closed field `Ω`. Surjectivity: `X_s̄ ⟶ s̄` is étale and `Ω` is separably closed,
so each point of `X_s̄` is hit by a section, whose composite with the first projection is the
required lift. -/
theorem geometricFibrePoint_bijective :
    Function.Bijective (geometricFibrePoint f s) := by
  refine ⟨fun a b hab ↦ Subtype.ext ?_, fun z ↦ ?_⟩
  · have hsec : geometricFibreSection f s a = geometricFibreSection f s b :=
      ext_of_apply_closedPoint_eq (pullback.snd f s.hom)
        (geometricFibreSection_comp_snd f s a) (geometricFibreSection_comp_snd f s b)
        (by
          rw [Subsingleton.elim (IsLocalRing.closedPoint s.residueField) (default : ↥s.source)]
          exact hab)
    rw [← geometricFibreSection_comp_fst f s a, ← geometricFibreSection_comp_fst f s b, hsec]
  · obtain ⟨σ, hσ, hz⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
      (pullback.snd f s.hom) (𝟙 s.source) z (Subsingleton.elim _ _)
    have hfac : (σ ≫ pullback.fst f s.hom) ≫ f = s.hom := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
    have hsec : geometricFibreSection f s ⟨_, hfac⟩ = σ :=
      pullback.hom_ext (by simp) (by simp [hσ])
    exact ⟨⟨_, hfac⟩, by rw [geometricFibrePoint, hsec]; exact hz⟩

end Fibre

section Site

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **Stacks Project, Tag 04FM**, the identification of the two descriptions of the value of the
fibre functor. For an object `U` of the small étale site of `S`, the set
`(geometricPointFiber B S hS s).obj U` of lifts of the geometric point `s` to `U` — the set
`{ū : (U, ū) is an étale neighbourhood of s̄}` of the source — is in bijection with the
underlying set `|U_s̄|` of the geometric fibre of `U` at `s`. -/
@[stacks 04FM "the two descriptions of `u(U)`: the geometric fibre and the étale neighbourhoods"]
def geometricPointFiberObjEquivGeometricFibre (U : SmallEtale B S hS) :
    (geometricPointFiber B S hS s).obj U ≃
      ↥(pullback (B.inclusion.map U.obj.hom) s.hom) :=
  Equiv.ofBijective _ (geometricFibrePoint_bijective (B.inclusion.map U.obj.hom) s)

end Site

end AlgebraicGeometry

end
