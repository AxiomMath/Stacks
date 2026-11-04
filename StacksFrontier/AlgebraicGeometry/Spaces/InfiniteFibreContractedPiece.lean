module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.Topology.Jacobson.InfiniteClosedSubset
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extracting a contracted piece from an infinite fibre

The proof of [Stacks, Tag 0AEM] contracts a morphism `f : (ℙ¹_k)^n ⟶ Z` by running, on a
*closed subvariety `C` which `f` maps to a point*, the application of [Stacks, Tag 0AEJ] to the
action of `(GL_{2,k})^n`.  This file produces that `C`, and the two distinct rational points of
it that the argument then needs, out of the only hypothesis available: that some fibre of `f`
over a point of `Z` is infinite.

The extraction is topological.  The fibre over a closed point of `|Z|` is a closed subset of
`|(ℙ¹_k)^n|`, which is a Noetherian Jacobson space; so if it is infinite it has an irreducible
closed piece with infinitely many closed points
(`Set.Infinite.exists_pair_ne_mem_closedPoints_of_isClosed`), and `Stacks 03IQ` puts the reduced
closed subspace structure on that piece.  Over an algebraically closed field the closed points
are the rational points, which is why 0AEM reduces to that case.

## Main results

* `AlgebraicGeometry.Space.noetherianSpace_points_yoneda`,
  `AlgebraicGeometry.Space.jacobsonSpace_points_yoneda`: the point space of a represented
  presheaf inherits both properties from the representing scheme, by clause (1) of
  Stacks 03BX.
* `AlgebraicGeometry.noetherianSpace_of_isProper_over_field` and
  `AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType_over_field`: a scheme proper over a
  field is a Noetherian space, and one locally of finite type over a field is a Jacobson space.
  These are what make the hypotheses of the extraction available at `(ℙ¹_k)^n`, whose
  representing object in the site is proper over `Spec k`.
* `AlgebraicGeometry.Space.exists_isIrreducible_mapsTo_of_infinite_fibre`: the extraction, for
  a morphism out of any presheaf with Noetherian Jacobson point space.
* `AlgebraicGeometry.Space.range_pointsMap_reducedClosedSubspace_comp_subset`: the reduced
  closed subspace on the extracted piece has a single point as its image in `|Z|`, which is the
  finiteness hypothesis the application of Stacks 0AEJ asks for.

## References

* [Stacks Project, Tag 005U](https://stacks.math.columbia.edu/tag/005U)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Noetherian and Jacobson point spaces -/

/-- **A scheme locally of finite type over a field is a Jacobson space.**  This is
`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace` over `Spec k`, whose Jacobson-ness is
that of a field as a ring. -/
@[ega "IV 10.4.6" "partial",
  ega "IV 10.4.9" "over a field",
  ega "IV 10.7.1" "1° over a field",
  sga "4 VIII 3.13" "partial"]
theorem jacobsonSpace_of_locallyOfFiniteType_over_field {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] : JacobsonSpace X :=
  LocallyOfFiniteType.jacobsonSpace f

/-- **A scheme proper over a field is a Noetherian space.**  Properness gives both halves of
`AlgebraicGeometry.IsNoetherian`: local finite type over a field makes the scheme locally
Noetherian, and quasi-compactness over the one-point space `Spec k` makes it compact. -/
theorem noetherianSpace_of_isProper_over_field {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] : NoetherianSpace X := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := ⟨⟩
  infer_instance

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transporting the point space along an isomorphism or a representation -/

/-- Being a Noetherian space transports along an isomorphism of presheaves. -/
theorem noetherianSpace_points_of_iso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ Y)
    (h : NoetherianSpace (points B S hS Y)) : NoetherianSpace (points B S hS X) :=
  (noetherianSpace_iff_of_homeomorph (pointsHomeomorphOfIso B S hS e)).2 h

/-- Being a Jacobson space transports along an isomorphism of presheaves. -/
theorem jacobsonSpace_points_of_iso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : X ≅ Y)
    (h : JacobsonSpace (points B S hS Y)) : JacobsonSpace (points B S hS X) :=
  have := h
  JacobsonSpace.of_isClosedEmbedding (pointsHomeomorphOfIso B S hS e).isClosedEmbedding

/-- The point space of a represented presheaf is a Noetherian space as soon as the representing
scheme is, the two being homeomorphic by clause (1) of Stacks 03BX. -/
theorem noetherianSpace_points_yoneda (U : BigFppfOver B S hS)
    (h : NoetherianSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    NoetherianSpace (points B S hS (yoneda.obj U)) :=
  (noetherianSpace_iff_of_homeomorph (schemePointsHomeomorph B S hS U)).2 h

/-- The point space of a represented presheaf is a Jacobson space as soon as the representing
scheme is, the two being homeomorphic by clause (1) of Stacks 03BX. -/
theorem jacobsonSpace_points_yoneda (U : BigFppfOver B S hS)
    (h : JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    JacobsonSpace (points B S hS (yoneda.obj U)) :=
  have := h
  JacobsonSpace.of_isClosedEmbedding (schemePointsHomeomorph B S hS U).isClosedEmbedding

/-! ### The extraction -/

variable {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A morphism with an infinite fibre over a closed point contracts an irreducible closed
piece of that fibre.**  Let `X` be a presheaf on the big fppf site over `S` whose point space is
a Noetherian Jacobson space, let `g : X ⟶ Z`, and let `y` be a closed point of `|Z|` whose
fibre is infinite.  Then there is an irreducible closed subset of `|X|` carried into `y` by `g`
and containing two distinct closed points of `|X|`.

The fibre is closed because it is the preimage of the closed set `{y}` under a continuous map,
and the rest is `Set.Infinite.exists_pair_ne_mem_closedPoints_of_isClosed`. -/
theorem exists_isIrreducible_mapsTo_of_infinite_fibre
    (hnoeth : NoetherianSpace (points B S hS X)) (hjac : JacobsonSpace (points B S hS X))
    (g : X ⟶ Z) (y : points B S hS Z) (hy : IsClosed {y})
    (hinf : {x : points B S hS X | pointsMap B S hS X g x = y}.Infinite) :
    ∃ (C : Set (points B S hS X)) (x₁ x₂ : points B S hS X),
      IsClosed C ∧ IsIrreducible C ∧ (∀ x ∈ C, pointsMap B S hS X g x = y) ∧
        x₁ ∈ C ∧ x₂ ∈ C ∧ IsClosed {x₁} ∧ IsClosed {x₂} ∧ x₁ ≠ x₂ := by
  let := hnoeth
  let := hjac
  have hfibre : {x : points B S hS X | pointsMap B S hS X g x = y} =
      pointsMap B S hS X g ⁻¹' {y} := rfl
  have hclosed : IsClosed {x : points B S hS X | pointsMap B S hS X g x = y} :=
    hfibre ▸ hy.preimage (continuous_pointsMap B S hS g)
  obtain ⟨C, x₁, x₂, hCS, hCclosed, hCirr, hx₁, hx₂, hx₁c, hx₂c, hne⟩ :=
    hinf.exists_pair_ne_mem_closedPoints_of_isClosed hclosed
  exact ⟨C, x₁, x₂, hCclosed, hCirr, fun x hx ↦ hCS hx, hx₁, hx₂, hx₁c, hx₂c, hne⟩

/-- The reduced closed subspace on a closed set of points carried by `g` into a single point of
`|Z|` has, as its image in `|Z|`, that one point: its set of points is the given closed set by
Stacks 03IQ. -/
theorem range_pointsMap_reducedClosedSubspace_comp_subset
    (hX : IsAlgebraicSpace B S hS X) (g : X ⟶ Z) (y : points B S hS Z)
    (C : Set (points B S hS X)) (hC : IsClosed C)
    (hCy : ∀ x ∈ C, pointsMap B S hS X g x = y) :
    Set.range (pointsMap B S hS (reducedClosedSubspace B S hS X hX C hC).toFunctor
      ((reducedClosedSubspace B S hS X hX C hC).ι ≫ g)) ⊆ {y} := by
  rintro w ⟨c, rfl⟩
  have hmem := (range_pointsMap_ι_reducedClosedSubspace B S hS X hX C hC).subset
    (Set.mem_range_self c)
  rw [Set.mem_singleton_iff, pointsMap_comp, Function.comp_apply]
  exact hCy _ hmem

end Space

end AlgebraicGeometry

end
