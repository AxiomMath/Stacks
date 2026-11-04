module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleDescentCompletion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The overlaps of an étale covering of the locally Noetherian site

Let `{V_i ⟶ V}` be an étale covering family of the locally Noetherian site over `S`. The overlaps
`V_i ×_V V_j` are objects of that site, with two projections, and they have the lifting property
of a fibre product inside the big fppf site over `S`.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_pullback_of_etale`: a fibre product of objects of
  the big fppf site over `S` along an étale morphism with locally Noetherian second factor is
  locally Noetherian.
* `AlgebraicGeometry.LocallyNoetherianOver.overlap`, together with
  `AlgebraicGeometry.LocallyNoetherianOver.overlapFst`,
  `AlgebraicGeometry.LocallyNoetherianOver.overlapSnd`,
  `AlgebraicGeometry.LocallyNoetherianOver.overlapFst_comp_f` and
  `AlgebraicGeometry.LocallyNoetherianOver.exists_lift_overlap`: the overlap of two morphisms
  of the locally Noetherian site, its projections, the commuting square, and the lifting
  property inside the big fppf site.

## References

* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 0GE1](https://stacks.math.columbia.edu/tag/0GE1)
* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A fibre product `V_i ×_V V_j` in the big fppf category over `S` is locally Noetherian as
soon as `V_i ⟶ V` is étale and `V_j` is locally Noetherian. -/
theorem isLocallyNoetherian_pullback_of_etale {V Vi Vj : BigFppfOver B S hS} (f : Vi ⟶ V)
    (g : Vj ⟶ V) (hf : Etale ((BigFppfOver.toScheme B S hS).map f))
    (hj : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Vj)) :
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (pullback f g)) := by
  have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst f g))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f g))
      ((BigFppfOver.toScheme B S hS).map f) ((BigFppfOver.toScheme B S hS).map g) :=
    (IsPullback.of_hasPullback f g).map _
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (pullback.snd f g)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian
    ((BigFppfOver.toScheme B S hS).map (pullback.snd f g))

namespace LocallyNoetherianOver

/-- The overlap `V_i ×_V V_j` of two morphisms of the locally Noetherian site over `S` with
étale first member, as an object of that site. -/
noncomputable def overlap {V Vi Vj : LocallyNoetherianOver B S hS} (f : Vi ⟶ V) (g : Vj ⟶ V)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f.hom)) :
    LocallyNoetherianOver B S hS :=
  ⟨pullback f.hom g.hom,
    isLocallyNoetherian_pullback_of_etale B S hS f.hom g.hom hf Vj.property⟩

/-- The first projection of the overlap. -/
noncomputable def overlapFst {V Vi Vj : LocallyNoetherianOver B S hS} (f : Vi ⟶ V) (g : Vj ⟶ V)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f.hom)) : overlap B S hS f g hf ⟶ Vi :=
  ObjectProperty.homMk (pullback.fst f.hom g.hom)

/-- The second projection of the overlap. -/
noncomputable def overlapSnd {V Vi Vj : LocallyNoetherianOver B S hS} (f : Vi ⟶ V) (g : Vj ⟶ V)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f.hom)) : overlap B S hS f g hf ⟶ Vj :=
  ObjectProperty.homMk (pullback.snd f.hom g.hom)

/-- The overlap square commutes. -/
theorem overlapFst_comp_f {V Vi Vj : LocallyNoetherianOver B S hS} (f : Vi ⟶ V) (g : Vj ⟶ V)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f.hom)) :
    overlapFst B S hS f g hf ≫ f = overlapSnd B S hS f g hf ≫ g :=
  ObjectProperty.hom_ext _ pullback.condition

/-- The overlap is the fibre product inside the *big* fppf site: every pair of morphisms out
of an arbitrary object of the big fppf site over `S` which agrees over `V` factors through
it. -/
theorem exists_lift_overlap {V Vi Vj : LocallyNoetherianOver B S hS} (f : Vi ⟶ V) (g : Vj ⟶ V)
    (hf : Etale ((BigFppfOver.toScheme B S hS).map f.hom)) (Y : BigFppfOver B S hS)
    (a : Y ⟶ Vi.obj) (b : Y ⟶ Vj.obj) (hab : a ≫ f.hom = b ≫ g.hom) :
    ∃ h : Y ⟶ (overlap B S hS f g hf).obj,
      h ≫ (overlapFst B S hS f g hf).hom = a ∧ h ≫ (overlapSnd B S hS f g hf).hom = b :=
  ⟨pullback.lift a b hab, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end LocallyNoetherianOver

end AlgebraicGeometry

end
