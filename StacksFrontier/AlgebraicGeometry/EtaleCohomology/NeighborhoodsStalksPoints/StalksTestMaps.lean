module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks at geometric points detect injectivity and surjectivity

A geometric point of a scheme `S` is a point of the small étale site of `S`, so it has a stalk
functor on sheaves of sets. This file shows that the geometric points of `S` form a
*conservative* family: a map of sheaves of sets on `S_étale` is injective, resp. surjective,
resp. an isomorphism, exactly when the induced map on the stalk at every geometric point is.

## Main definitions

* `AlgebraicGeometry.Scheme.algClosedPoint`: the geometric point above a point of `S` whose
  residue field is an algebraic closure of the residue field there.
* `AlgebraicGeometry.GeometricPoint.toPoint`: a geometric point, read as a point of the small
  étale site.
* `AlgebraicGeometry.GeometricPoint.stalkFunctor`: the stalk of a sheaf of sets at a geometric
  point.

## Main results

* `AlgebraicGeometry.GeometricPoint.isConservativeFamilyOfPoints`: the geometric points of a
  scheme are a conservative family of points of its small étale site.
* `AlgebraicGeometry.GeometricPoint.mono_iff_forall_injective_stalkFunctor` and
  `AlgebraicGeometry.GeometricPoint.epi_iff_forall_surjective_stalkFunctor`: injectivity and
  surjectivity of a map of sheaves of sets are tested at the stalks.
* `AlgebraicGeometry.GeometricPoint.isIso_iff_forall_bijective_stalkFunctor`: and so is being an
  isomorphism.

## Implementation notes

Mathlib's `AlgebraicGeometry.Scheme.pointSmallEtale` builds a point of the small étale site from
a morphism out of the spectrum of a *separably* closed field, and
`AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_pointSmallEtale'` exhibits one
conservative family, indexed by the points of `S` with the separable closures of their residue
fields. The source quantifies instead over geometric points, whose residue fields are
*algebraically* closed; so the family used here is the one indexed by the points of `S` with the
algebraic closures of their residue fields, which is conservative for the same reason — it is
jointly surjective on the underlying space — and consists of geometric points in the sense of the
source.

Injectivity and surjectivity of a map of sheaves of sets are taken in their categorical form,
as `Mono` and `Epi`; `CategoryTheory.Sheaf.isLocallyInjective_iff_injective` and
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi` relate these to the section-level statements.
The necessity of the stalk conditions is exactness of the stalk functor, which is a left adjoint
preserving finite limits; their sufficiency is conservativity.

The coefficient category is `Type u` for `S : Scheme.{u}`: this is the universe at which the
small étale site of `S` has enough points, since the conservative family is indexed by the
underlying space of `S`.

## References

* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 03PO](https://stacks.math.columbia.edu/tag/03PO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- The morphism underlying `AlgebraicGeometry.Scheme.algClosedPoint`: the spectrum of an
algebraic closure of the residue field at `s`, mapped to `S` through `s`. -/
noncomputable def algClosedPointHom (S : Scheme.{u}) (s : S) :
    Spec (.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
  (SpecToEquivOfField (AlgebraicClosure (S.residueField s)) S).symm
    ⟨s, CommRingCat.ofHom (algebraMap (S.residueField s) _)⟩

/-- The morphism `AlgebraicGeometry.Scheme.algClosedPointHom S s` sends every point of the
spectrum of the algebraic closure to `s`. -/
@[simp]
theorem algClosedPointHom_apply (S : Scheme.{u}) (s : S)
    (x : (Spec (.of (AlgebraicClosure (S.residueField s))) : Scheme.{u})) :
    S.algClosedPointHom s x = s := by
  simp [algClosedPointHom, SpecToEquivOfField]

/-- The geometric point of `S` above `s` whose residue field is an algebraic closure of the
residue field of `S` at `s`. Every point of `S` carries one, so these geometric points are
jointly surjective. -/
@[sga "3 XII 1.3", sga "3 XIX 1.4.0"]
noncomputable def algClosedPoint (S : Scheme.{u}) (s : S) : GeometricPoint S where
  residueField := AlgebraicClosure (S.residueField s)
  hom := S.algClosedPointHom s

/-- The morphism of the geometric point `AlgebraicGeometry.Scheme.algClosedPoint S s` is
`AlgebraicGeometry.Scheme.algClosedPointHom S s`. -/
@[simp]
theorem algClosedPoint_hom (S : Scheme.{u}) (s : S) :
    (S.algClosedPoint s).hom = S.algClosedPointHom s :=
  rfl

end Scheme

namespace GeometricPoint

variable {S : Scheme.{u}}

/-- A geometric point of a scheme is a point of its small étale site: the residue field of a
geometric point is algebraically closed, hence separably closed. -/
noncomputable abbrev toPoint (s : GeometricPoint S) :
    (Scheme.smallEtaleTopology S).Point.{u} :=
  Scheme.pointSmallEtale s.hom

/-- The stalk of a sheaf of sets on the small étale site of `S` at a geometric point of `S`. -/
noncomputable abbrev stalkFunctor (s : GeometricPoint S) :
    Sheaf (Scheme.smallEtaleTopology S) (Type u) ⥤ Type u :=
  s.toPoint.sheafFiber

/-- The geometric points of a scheme form a conservative family of points of its small étale
site: the family indexed by the points of `S`, taking at each the algebraic closure of the
residue field, is jointly surjective. -/
@[sga "4 VIII 3.13" "Case E = X"]
theorem isConservativeFamilyOfPoints (S : Scheme.{u}) :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun (s : S) ↦ (S.algClosedPoint s).toPoint)) :=
  Scheme.isConservative_pointSmallEtale _ (by
    ext s
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨s, default, S.algClosedPointHom_apply s _⟩)

variable {F G : Sheaf (Scheme.smallEtaleTopology S) (Type u)}

/-- A property of maps of types that holds for the stalk maps at all geometric points holds for the
stalk maps at all members of the conservative family of geometric points. -/
private theorem property_stalk_map_of_forall_geometricPoint (P : MorphismProperty (Type u))
    (φ : F ⟶ G) (h : ∀ s : GeometricPoint S, P (s.stalkFunctor.map φ))
    (Φ : (ObjectProperty.ofObj (fun (s : S) ↦ (S.algClosedPoint s).toPoint)).FullSubcategory) :
    P (Φ.obj.sheafFiber.map φ) := by
  obtain ⟨s, hs⟩ := (ObjectProperty.ofObj_iff _ _).1 Φ.property
  rw [← hs]
  exact h _

/-- **Stacks Project, Tag 03PU.** A map of sheaves of sets on the small étale site of a scheme
is injective if and only if it is injective on the stalk at every geometric point. -/
@[stacks 03PU "injectivity on stalks at geometric points", sga "4 VIII 3.6" "mono ⟺ inj on stalks"]
theorem mono_iff_forall_injective_stalkFunctor (φ : F ⟶ G) :
    Mono φ ↔ ∀ s : GeometricPoint S, Function.Injective (s.stalkFunctor.map φ) := by
  refine ⟨fun _ s ↦ ?_, fun h ↦ ?_⟩
  · rw [← mono_iff_injective]
    infer_instance
  · have key := (isConservativeFamilyOfPoints S).jointlyReflectIsomorphisms_type
    have := property_stalk_map_of_forall_geometricPoint (MorphismProperty.monomorphisms _) φ
      fun s ↦ (mono_iff_injective _).2 (h s)
    exact key.jointlyReflectMonomorphisms.mono φ

/-- **Stacks Project, Tag 03PU.** A map of sheaves of sets on the small étale site of a scheme
is surjective if and only if it is surjective on the stalk at every geometric point. -/
@[stacks 03PU "surjectivity on stalks at geometric points", sga "4 VIII 3.6" "epi ⟺ surj on stalks"]
theorem epi_iff_forall_surjective_stalkFunctor (φ : F ⟶ G) :
    Epi φ ↔ ∀ s : GeometricPoint S, Function.Surjective (s.stalkFunctor.map φ) := by
  refine ⟨fun _ s ↦ ?_, fun h ↦ ?_⟩
  · rw [← epi_iff_surjective]
    infer_instance
  · have key := (isConservativeFamilyOfPoints S).jointlyReflectIsomorphisms_type
    have := property_stalk_map_of_forall_geometricPoint (MorphismProperty.epimorphisms _) φ
      fun s ↦ (epi_iff_surjective _).2 (h s)
    exact key.jointlyReflectEpimorphisms.epi φ

/-- A map of sheaves of sets on the small étale site of a scheme is an isomorphism if and only
if it is bijective on the stalk at every geometric point. -/
theorem isIso_iff_forall_bijective_stalkFunctor (φ : F ⟶ G) :
    IsIso φ ↔ ∀ s : GeometricPoint S, Function.Bijective (s.stalkFunctor.map φ) := by
  refine ⟨fun _ s ↦ ?_, fun h ↦ ?_⟩
  · rw [← isIso_iff_bijective]
    infer_instance
  · rw [(isConservativeFamilyOfPoints S).jointlyReflectIsomorphisms_type.isIso_iff]
    refine property_stalk_map_of_forall_geometricPoint (MorphismProperty.isomorphisms _) φ
      fun s ↦ (isIso_iff_bijective _).2 (h s)

end GeometricPoint

end AlgebraicGeometry

end
