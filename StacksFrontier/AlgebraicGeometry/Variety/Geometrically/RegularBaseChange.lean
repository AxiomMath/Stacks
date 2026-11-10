module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularNoetherian
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom

/-!
# Geometric regularity after a finitely generated field extension

For a locally Noetherian scheme over a field, geometric regularity at a point can be
checked at any point lying above it after a finitely generated extension of the field.
Consequently, geometric regularity of the entire scheme is invariant under such base change.

## Main results

* `AlgebraicGeometry.geometricallyRegularAt_baseChange_iff` gives the pointwise equivalence.
* `AlgebraicGeometry.geometricallyRegular_baseChange_iff` gives the equivalence for schemes.

## Implementation notes

Base change is the categorical pullback of the structure morphism along the morphism of
spectra induced by the field extension. The base-changed scheme is viewed over the larger
field using the second pullback projection. The first projection identifies a point lying
above the original point. The comparison between base changing twice and base changing once
along a composite is `AlgebraicGeometry.iteratedBaseChangeIso`.

The two directions of the pointwise equivalence are carried by separate lemmas, so that neither
proof has to be elaborated as part of the other.

## References

* [Stacks Project, Tag 038W](https://stacks.math.columbia.edu/tag/038W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Two extensions of a field admit a common extension which is finitely generated over the
first one, when the second is finite. -/
private lemma exists_common_extension_essFiniteType
    (k k' E : Type u) [Field k] [Field k'] [Field E]
    [Algebra k k'] [Algebra k E] [Module.Finite k E] :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra k M) (_ : Algebra k' M)
      (_ : Algebra E M), Algebra.EssFiniteType k' M ∧
        IsScalarTower k k' M ∧ IsScalarTower k E M := by
  let T := k' ⊗[k] E
  have : Module.Finite k' T := Module.Finite.base_change k k' E
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  have : Module.Finite k' (T ⧸ m) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ k' m).toLinearMap Ideal.Quotient.mk_surjective
  exact ⟨T ⧸ m, Ideal.Quotient.field m, inferInstance, inferInstance, inferInstance,
    Algebra.EssFiniteType.of_finiteType k' _, inferInstance, inferInstance⟩

/-- Geometric regularity at a point passes to any point above it after a finitely generated
base change. -/
private lemma isGeometricallyRegularAt_baseChange_of_isGeometricallyRegularAt
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [Algebra.EssFiniteType k k']
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) (x : X)
    (x' : (pullback f (Spec.map (ofHom (algebraMap k k'))) : Scheme.{u}))
    (hx' : pullback.fst f (Spec.map (ofHom (algebraMap k k'))) x' = x)
    (h : IsGeometricallyRegularAt f x) :
    IsGeometricallyRegularAt
      (pullback.snd f (Spec.map (ofHom (algebraMap k k')))) x' := by
  let φ : Spec (.of k') ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k k'))
  intro L _ _ hL ψ z hz
  let : Algebra k L := RingHom.toAlgebra ((algebraMap k' L).comp (algebraMap k k'))
  have : IsScalarTower k k' L := .of_algebraMap_eq' rfl
  have : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k k' L
  let μ : Spec (.of L) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k L))
  have hcomp : ψ ≫ φ = μ := specMap_algebraMap_comp k k' L
  let e := iteratedBaseChangeIso f φ ψ μ hcomp
  have hz' : pullback.fst f μ (e.hom z) = x := by
    rw [← hx', ← hz]
    exact congrArg (fun g ↦ g.base.hom z) (iteratedBaseChangeIso_fst f φ ψ μ hcomp)
  have : IsRegularLocalRing ((pullback f μ).presheaf.stalk (e.hom z)) := h L (e.hom z) hz'
  exact IsRegularLocalRing.of_ringEquiv (asIso (e.hom.stalkMap z)).commRingCatIsoToRingEquiv

/-- Geometric regularity at a point of a base change descends to the point below it. -/
private lemma isGeometricallyRegularAt_of_baseChange
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [Algebra.EssFiniteType k k']
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) (x : X)
    (x' : (pullback f (Spec.map (ofHom (algebraMap k k'))) : Scheme.{u}))
    (hx' : pullback.fst f (Spec.map (ofHom (algebraMap k k'))) x' = x)
    (h : IsGeometricallyRegularAt
      (pullback.snd f (Spec.map (ofHom (algebraMap k k')))) x') :
    IsGeometricallyRegularAt f x := by
  let φ : Spec (.of k') ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k k'))
  apply ((geometricallyRegularAt_tfae k X f x).out 2 1).mp
  intro E _ _ _ _ xE hxE
  have : Algebra.EssFiniteType k E := Algebra.EssFiniteType.of_finiteType k E
  let ψ : Spec (.of E) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k E))
  have : UniversallyInjective ψ := universallyInjective_specMap_of_isPurelyInseparable k E
  have : UniversallyInjective (pullback.fst f ψ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f ψ).flip inferInstance
  obtain ⟨M, _, _, _, _, _, _, _⟩ := exists_common_extension_essFiniteType k k' E
  let χK : Spec (.of M) ⟶ Spec (.of k') := Spec.map (ofHom (algebraMap k' M))
  let χE : Spec (.of M) ⟶ Spec (.of E) := Spec.map (ofHom (algebraMap E M))
  let μ : Spec (.of M) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k M))
  have hcompK : χK ≫ φ = μ := specMap_algebraMap_comp k k' M
  have hcompE : χE ≫ ψ = μ := specMap_algebraMap_comp k E M
  let A : Scheme.{u} := pullback (pullback.snd f φ) χK
  obtain ⟨z, hz⟩ := (pullback.fst (pullback.snd f φ) χK).surjective x'
  have : IsRegularLocalRing (A.presheaf.stalk z) := h M z hz
  let r : A ⟶ pullback f ψ := iteratedBaseChangeComparison f φ ψ χK χE μ hcompK hcompE
  have : Flat r := by
    dsimp [r, iteratedBaseChangeComparison]
    infer_instance
  have hrx : (pullback.fst f ψ) (r z) = x := by
    calc
      (pullback.fst f ψ) (r z) = (r ≫ pullback.fst f ψ) z := rfl
      _ = ((pullback.fst (pullback.snd f φ) χK) ≫ pullback.fst f φ) z :=
        congrArg (fun g ↦ g.base.hom z)
          (iteratedBaseChangeComparison_fst f φ ψ χK χE μ hcompK hcompE)
      _ = x := by rw [Scheme.Hom.comp_apply, hz, hx']
  obtain rfl : r z = xE := (pullback.fst f ψ).injective (hrx.trans hxE.symm)
  have : IsLocallyNoetherian (pullback f ψ) :=
    (isLocallyNoetherian_baseChange_iff k E X f).mp inferInstance
  let R := (pullback f ψ).presheaf.stalk (r z)
  let S := A.presheaf.stalk z
  let : Algebra R S := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat R S := Flat.stalkMap r z
  have : IsLocalHom (algebraMap R S) := r.toLRSHom.prop z
  exact IsRegularLocalRing.of_flat_of_isLocalHom (R := R) S

/-- **Stacks Project, Tag 038W, pointwise assertion.** Geometric regularity at a point
is equivalent to geometric regularity at any point above it after a finitely generated
extension of the ground field. -/
@[stacks 038W "pointwise equivalence"]
public theorem geometricallyRegularAt_baseChange_iff
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [Algebra.EssFiniteType k k']
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) (x : X) :
    let g : Spec (.of k') ⟶ Spec (.of k) :=
      Spec.map (ofHom (algebraMap k k'))
    ∀ (x' : (pullback f g : Scheme.{u})),
      pullback.fst f g x' = x →
        (IsGeometricallyRegularAt f x ↔
          IsGeometricallyRegularAt (pullback.snd f g) x') := by
  intro g x' hx'
  exact ⟨isGeometricallyRegularAt_baseChange_of_isGeometricallyRegularAt k k' X f x x' hx',
    isGeometricallyRegularAt_of_baseChange k k' X f x x' hx'⟩

/-- **Stacks Project, Tag 038W, global assertion.** Geometric regularity is invariant
under finitely generated extension of the ground field. -/
@[stacks 038W "global equivalence"]
public theorem geometricallyRegular_baseChange_iff
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [Algebra.EssFiniteType k k']
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) :
    let g : Spec (.of k') ⟶ Spec (.of k) :=
      Spec.map (ofHom (algebraMap k k'))
    IsGeometricallyRegular f ↔
      IsGeometricallyRegular (pullback.snd f g) := by
  change (∀ x : X, IsGeometricallyRegularAt f x) ↔
    (∀ (x' : (pullback f (Spec.map (ofHom (algebraMap k k'))) : Scheme.{u})),
      IsGeometricallyRegularAt
        (pullback.snd f (Spec.map (ofHom (algebraMap k k')))) x')
  refine ⟨fun h x' ↦ (geometricallyRegularAt_baseChange_iff k k' X f _ x' rfl).mp (h _),
    fun h x ↦ ?_⟩
  obtain ⟨x', hx'⟩ := (pullback.fst f (Spec.map (ofHom (algebraMap k k')))).surjective x
  exact (geometricallyRegularAt_baseChange_iff k k' X f x x' hx').mpr (h x')

end AlgebraicGeometry
