module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The generic fibre of an étale neighbourhood, and injectivity of `𝐆_m ⟶ j_* 𝐆_{m,K}`

Let `X` be an integral scheme with generic point `η` and function field `K = 𝒪_{X,η}`, and let
`j : Spec K ⟶ X` be the inclusion of the generic point. The divisor sequence of Stacks 03RM,
`0 → 𝐆_{m,X} → j_* 𝐆_{m,K} → ⨁_x i_{x,*} ℤ → 0`,
begins with the comparison morphism
`Stacks.EtaleCohomology.multiplicativeDirectImageComparison`, whose value on sections over an
étale `X`-scheme `U` restricts an invertible global function along the projection
`U ×_X Spec K ⟶ U` off the *generic fibre* of `U`. This file proves that morphism is a
monomorphism, which is the exactness of the sequence at its left end.

Two statements carry the geometry.

The first is where the generic fibre sits inside `U`. For a **flat** `f : U ⟶ X` over an
irreducible `X`, generalizations lift along `f`
(`AlgebraicGeometry.Flat.generalizingMap`), so every point of `U` is a specialization of a point
lying over `η`; at a point whose closure is a whole irreducible component of `U` there is nothing
to specialize from, so such a point lies over `η` *itself*. Thus the generic fibre of `U`
contains every generic point of `U` — it is not merely dense in `U`, it meets every irreducible
component in that component's generic point.

The second is the injectivity statement. `j` is quasi-compact (`Spec K` is a one-point space,
because `j` is a preimmersion whose image is `{η}`) and dominant (its image is `{η}`, which is
dense), hence *scheme-theoretically dominant* over the reduced scheme `X`. Scheme-theoretic
dominance is stable under flat base change, so `U ×_X Spec K ⟶ U` is scheme-theoretically
dominant for every étale — in particular flat — `U ⟶ X`, and
`AlgebraicGeometry.Scheme.Hom.app_injective` makes `Γ(U, 𝒪_U) → Γ(U ×_X Spec K, 𝒪)` injective.
Injectivity on invertible functions, hence on sections of `𝐆_m`, follows, and a morphism of
sheaves injective on all sections is a monomorphism.

## Main results

* `eq_of_specializes_of_closure_mem_irreducibleComponents`: a generalization of a generic point
  of an irreducible component is that point. This is the minimality that makes the key lemma
  work, and it is purely topological.
* `AlgebraicGeometry.exists_specializes_base_eq_genericPoint`: along a flat morphism to an
  irreducible scheme, every point of the source is a specialization of a point lying over the
  generic point.
* `AlgebraicGeometry.base_eq_genericPoint_of_closure_mem_irreducibleComponents`: **the key
  lemma** — along a flat morphism to an irreducible scheme, every generic point of an irreducible
  component of the source lies over the generic point of the target.
* `Stacks.EtaleCohomology.exists_pullback_genericPointInclusion_eq_of_mem_irreducibleComponents`:
  the generic fibre of an étale `X`-scheme `U` contains every generic point of `U`.
* `Stacks.EtaleCohomology.appTop_pullback_fst_injective`: `Γ(U, 𝒪_U) → Γ(U ×_X Y, 𝒪)` is
  injective for a quasi-compact scheme-theoretically dominant `Y ⟶ X` and a flat `U ⟶ X`.
* `Stacks.EtaleCohomology.mono_multiplicativeDirectImageComparison`: the comparison morphism
  `𝐆_{m,X} ⟶ i_* 𝐆_{m,Y}` is a monomorphism for a quasi-compact scheme-theoretically dominant
  `i : Y ⟶ X`.
* `Stacks.EtaleCohomology.mono_multiplicativeDirectImageComparison_genericPointInclusion`:
  **`0 → 𝐆_{m,X} → j_* 𝐆_{m,K}` is exact** on an integral scheme — the left end of the divisor
  sequence of Stacks 03RM.

## Implementation notes

The monomorphism is proved for an arbitrary quasi-compact scheme-theoretically dominant
`i : Y ⟶ X`, not only for the generic point, because that is the hypothesis the argument uses and
the same statement is wanted at other morphisms. The generic point supplies the instances
`Stacks.EtaleCohomology.isDominant_genericPointInclusion` and
`Stacks.EtaleCohomology.quasiCompact_genericPointInclusion`.

The key lemma is stated for `Flat` rather than `Etale` because lifting generalizations is all it
uses, and it is stated with `closure {u} ∈ irreducibleComponents U` rather than with
`IsGenericPoint`, which is the same hypothesis written out.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the divisor sequence.
* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7): the image of
  `Spec 𝒪_{X,x} ⟶ X` is the set of generalizations of `x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

/-- **A generalization of the generic point of an irreducible component is that point.** If
`closure {x}` is an irreducible component and `y ⤳ x`, then `closure {x} ⊆ closure {y}`, and
`closure {y}` is irreducible, so maximality forces the two closures to agree; a T0 space then
has `y = x`. -/
theorem eq_of_specializes_of_closure_mem_irreducibleComponents {α : Type*} [TopologicalSpace α]
    [T0Space α] {x y : α} (hx : closure {x} ∈ irreducibleComponents α) (h : y ⤳ x) : y = x :=
  (h.antisymm (specializes_iff_closure_subset.2
    (hx.eq_of_ge isIrreducible_singleton.closure h.closure_subset).le)).eq

namespace AlgebraicGeometry

variable {X U : Scheme.{u}} (f : U ⟶ X) [Flat f] [IrreducibleSpace X]

/-- **Along a flat morphism to an irreducible scheme, every point of the source is a
specialization of a point lying over the generic point.** The generic point of `X` is a
generalization of every point of `X`, and generalizations lift along a flat morphism. -/
theorem exists_specializes_base_eq_genericPoint (u : U) :
    ∃ u' : U, u' ⤳ u ∧ f.base u' = genericPoint X :=
  Flat.generalizingMap f (a := u) (b := genericPoint X) (genericPoint_specializes _)

/-- **The generic point of an irreducible component of the source of a flat morphism to an
irreducible scheme lies over the generic point of the target.**

This is the geometric input to the divisor sequence of Stacks 03RM: the fibre over the generic
point of `X` of an étale `X`-scheme `U` contains every generic point of `U`, so an invertible
function on `U` is determined by its restriction to that fibre.

Flatness is used only to lift the generalization `genericPoint X ⤳ f u` to a generalization
`u' ⤳ u` over it, and `u` admits no proper generalization because `closure {u}` is already a
maximal irreducible closed subset. -/
@[ega "IV 18.10.6" "(i), (ii)"]
theorem base_eq_genericPoint_of_closure_mem_irreducibleComponents {u : U}
    (hu : closure {u} ∈ irreducibleComponents U) :
    f.base u = genericPoint X := by
  obtain ⟨u', hu', hfu'⟩ := exists_specializes_base_eq_genericPoint f u
  rw [← hfu', eq_of_specializes_of_closure_mem_irreducibleComponents hu hu']

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

section GenericPoint

variable (X : Scheme.{u}) [IrreducibleSpace X]

/-- The only generalization of the generic point of an irreducible scheme is itself. -/
theorem eq_genericPoint_of_specializes {y : X} (h : y ⤳ genericPoint X) : y = genericPoint X :=
  eq_of_specializes_of_closure_mem_irreducibleComponents
    (by simp [irreducibleComponents_eq_singleton]) h

/-- **The image of the inclusion of the generic point is `{η}`.** By Stacks 01J7 the image of
`Spec 𝒪_{X,x} ⟶ X` is the set of generalizations of `x`, and the generic point has no proper
generalization. -/
theorem range_genericPointInclusion :
    Set.range (genericPointInclusion X).base = {genericPoint X} := by
  rw [genericPointInclusion, Scheme.range_fromSpecStalk]
  exact Set.eq_singleton_iff_unique_mem.2
    ⟨specializes_rfl, fun _ h => eq_genericPoint_of_specializes X h⟩

/-- Every point of `Spec K` is sent to the generic point of `X`. -/
theorem genericPointInclusion_base (z : Spec X.functionField) :
    (genericPointInclusion X).base z = genericPoint X := by
  have : (genericPointInclusion X).base z ∈ Set.range (genericPointInclusion X).base :=
    Set.mem_range_self z
  rwa [range_genericPointInclusion X, Set.mem_singleton_iff] at this

/-- The inclusion of the generic point is a preimmersion, being
`AlgebraicGeometry.Scheme.fromSpecStalk`. -/
instance isPreimmersion_genericPointInclusion : IsPreimmersion (genericPointInclusion X) :=
  inferInstanceAs (IsPreimmersion (X.fromSpecStalk (genericPoint X)))

/-- **`Spec K` is a one-point space.** The inclusion of the generic point is a preimmersion,
hence injective on points, and its image is the single point `η`. -/
instance subsingleton_spec_functionField : Subsingleton (Spec X.functionField) :=
  ⟨fun a b => (genericPointInclusion X).isEmbedding.injective
    (by rw [genericPointInclusion_base X a, genericPointInclusion_base X b])⟩

/-- **The inclusion of the generic point is quasi-compact**: every subset of the one-point space
`Spec K` is compact. -/
instance quasiCompact_genericPointInclusion : QuasiCompact (genericPointInclusion X) :=
  ⟨fun _ _ _ => Set.Subsingleton.isCompact Set.subsingleton_of_subsingleton⟩

/-- **The inclusion of the generic point is dominant**: its image `{η}` is dense. -/
instance isDominant_genericPointInclusion : IsDominant (genericPointInclusion X) := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq, range_genericPointInclusion X]
  exact genericPoint_spec X

/-- **The inclusion of the generic point of an integral scheme is scheme-theoretically
dominant.** A dominant morphism to a reduced scheme has trivial kernel. -/
instance isSchemeTheoreticallyDominant_genericPointInclusion [IsReduced X] :
    IsSchemeTheoreticallyDominant (genericPointInclusion X) :=
  .of_isDominant _

/-- **The generic fibre of an étale `X`-scheme contains every generic point of that scheme.**
For `u` a generic point of an irreducible component of `U`, the key lemma
`AlgebraicGeometry.base_eq_genericPoint_of_closure_mem_irreducibleComponents` puts `u` over the
generic point of `X`, which is the image of every point of `Spec K`; a fibre product carries a
point over any pair of points with a common image.

This refines `Stacks.EtaleCohomology.exists_mem_pullback_genericPointInclusion`, which only
produces *some* point of the generic fibre: here the generic fibre is shown to meet every
irreducible component of `U` in that component's generic point. -/
theorem exists_pullback_genericPointInclusion_eq_of_mem_irreducibleComponents (V : X.Etale)
    {u : V.left} (hu : closure {u} ∈ irreducibleComponents V.left) :
    ∃ z : ↥(pullback V.hom (genericPointInclusion X)),
      (pullback.fst V.hom (genericPointInclusion X)).base z = u := by
  have : IrreducibleSpace ↥((Functor.fromPUnit X).obj V.right) :=
    inferInstanceAs (IrreducibleSpace ↥X)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.hom)
    (g := genericPointInclusion X) u (IsLocalRing.closedPoint X.functionField)
    ((base_eq_genericPoint_of_closure_mem_irreducibleComponents V.hom hu).trans
      (genericPointInclusion_base X _).symm)
  exact ⟨z, hz⟩

end GenericPoint

section Mono

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [QuasiCompact i] [IsSchemeTheoreticallyDominant i]

/-- **Restriction of global functions to a base change along a quasi-compact
scheme-theoretically dominant morphism is injective.** Scheme-theoretic dominance is stable under
flat base change, so `U ×_X Y ⟶ U` is quasi-compact and scheme-theoretically dominant, and such a
morphism has injective maps on sections. -/
theorem appTop_pullback_fst_injective {V : Scheme.{u}} (g : V ⟶ X) [Flat g] :
    Function.Injective (pullback.fst g i).appTop :=
  Scheme.Hom.app_injective _ ⊤

/-- **The comparison morphism `𝐆_{m,X} ⟶ i_* 𝐆_{m,Y}` is a monomorphism** when `i` is
quasi-compact and scheme-theoretically dominant. On sections over an étale `X`-scheme `U` the
morphism is `Units.map` of the injective restriction
`Γ(U, 𝒪_U) → Γ(U ×_X Y, 𝒪)`, so it is injective; a morphism of sheaves injective on every
section is a monomorphism. -/
theorem mono_multiplicativeDirectImageComparison :
    Mono (multiplicativeDirectImageComparison.{u, v} i) := by
  have happ : ∀ W, Mono ((multiplicativeDirectImageComparison.{u, v} i).hom.app W) := by
    rintro ⟨V⟩
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    obtain ⟨x, rfl⟩ := Stacks.Kummer.ofUnit_surjective.{u, v} a
    obtain ⟨y, rfl⟩ := Stacks.Kummer.ofUnit_surjective.{u, v} b
    rw [multiplicativeDirectImageComparison_app_ofUnit,
      multiplicativeDirectImageComparison_app_ofUnit] at hab
    refine congrArg _ (Units.ext ?_)
    exact appTop_pullback_fst_injective i V.hom
      (congrArg Units.val (Stacks.Kummer.ofUnit_injective.{u, v} hab))
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _ (h := NatTrans.mono_of_mono_app _)

end Mono

section DivisorSequence

variable (X : Scheme.{u}) [IsIntegral X]

/-- **The first map of the divisor sequence is injective**: on an integral scheme the comparison
morphism `𝐆_{m,X} ⟶ j_* 𝐆_{m,K}` at the inclusion of the generic point is a monomorphism, so
`0 → 𝐆_{m,X} → j_* 𝐆_{m,K}` is exact.

This is the left end of the divisor sequence of Stacks 03RM. The remaining content of that tag —
the order-of-vanishing map to `⨁_x i_{x,*} ℤ` and exactness in the middle and on the right — is
not proved here. -/
theorem mono_multiplicativeDirectImageComparison_genericPointInclusion :
    Mono (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)) :=
  mono_multiplicativeDirectImageComparison _

end DivisorSequence

end Stacks.EtaleCohomology

end
