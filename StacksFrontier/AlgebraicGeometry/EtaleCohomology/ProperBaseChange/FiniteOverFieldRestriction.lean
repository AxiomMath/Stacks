module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointsVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction for schemes finite over a separably closed field

Let `Z` be a scheme finite over a separably closed field `k` and let `k'/k` be a separably
closed extension. For every abelian sheaf `G` on the small étale site of `Z` and every degree
`q`, the restriction map `H^q(Z, G) → H^q(Z_{k'}, G|_{Z_{k'}})` is bijective.

In degree zero this is
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_zero_bijective_of_isSepClosed`. In positive
degrees both groups vanish by Stacks Project Tag 09AY: every point of a scheme finite over a field
is closed, and its residue field is a finite, hence separably closed, extension of the separably
closed base.

This is the zero-dimensional input of the dévissage of Stacks Project Tag 03SC part (7): the
sheaves `i_* i^{-1} F` supported on a finite set of closed points of a curve, as in Tag 0GJA.

## Main results

* `AlgebraicGeometry.isClosed_singleton_of_locallyQuasiFinite_spec`: every point of a scheme
  locally quasi-finite over a field is closed.
* `Stacks.EtaleCohomology.subsingleton_etaleCohomology_of_isFinite_of_isSepClosed`: positive
  degree vanishing for a scheme finite over a separably closed field.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_isFinite_of_isSepClosed`:
  the bijectivity of the restriction map, in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry

/-- Every point of a scheme locally quasi-finite over a field is closed: the fibre over the
unique point of the base is the whole scheme, and it is discrete. -/
public theorem isClosed_singleton_of_locallyQuasiFinite_spec {K : Type u} [Field K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K)) [LocallyQuasiFinite f] (z : Z) :
    IsClosed ({z} : Set Z) := by
  have hd := f.isDiscrete_preimage_singleton (f z)
  have huniv : f ⁻¹' {f z} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [huniv] at hd
  have : DiscreteTopology Z := isDiscrete_univ_iff.mp hd
  exact isClosed_discrete _

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- **Positive-degree vanishing on a scheme finite over a separably closed field.** -/
public theorem subsingleton_etaleCohomology_of_isFinite_of_isSepClosed {K : Type u} [Field K]
    [IsSepClosed K] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K)) [IsFinite f]
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w} G q) :=
  have : IsAffine Z := isAffine_of_isAffineHom f
  subsingleton_etaleCohomology_of_closed_points' Z
    (isClosed_singleton_of_locallyQuasiFinite_spec f)
    (fun z ↦ isSepClosed_residueField_of_isClosed f z
      (isClosed_singleton_of_locallyQuasiFinite_spec f z)) G q hq

/-- **Restriction is bijective on a scheme finite over a separably closed field.** For `Z`
finite over a separably closed field `k`, a separably closed extension `k'/k` and any abelian
sheaf `G` on `Z_étale`, restriction `H^q(Z, G) → H^q(Z_{k'}, G|_{Z_{k'}})` is bijective in every
degree. -/
@[sga "4 XII 5.4" "special case", sga "4 XVI 1.6" "Abelian clause"]
public theorem etaleCohomologyRestrictionMap_bijective_of_isFinite_of_isSepClosed
    (k k' : Type u) [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k'] [Algebra k k']
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsFinite f]
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (scalarExtension k k' f).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective
      (etaleCohomologyRestrictionMap.{u, 0, w} (scalarExtensionFst k k' f) G q) := by
  obtain _ | m := q
  · exact etaleCohomologyRestrictionMap_zero_bijective_of_isSepClosed k k' f G
  · have h₁ := subsingleton_etaleCohomology_of_isFinite_of_isSepClosed f G (m + 1) (by omega)
    have h₂ := subsingleton_etaleCohomology_of_isFinite_of_isSepClosed
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
      ((etaleAbelianInverseImage.{u, 0} (scalarExtensionFst k k' f)).obj G) (m + 1) (by omega)
    exact ⟨fun x y _ ↦ Subsingleton.elim x y, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end Stacks.EtaleCohomology

end
