module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.Variety.JacobsonClosedPoints
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Closed points of a scalar extension over a closed point

Let `X` be a scheme locally of finite type over an algebraically closed field `k`, `k'/k` a field
extension and `p : X_{k'} ⟶ X` the projection. Over a closed point `x` of `X` there is exactly
one point of `X_{k'}`, and it is closed: the residue field of `x` is `k`, so the fibre of `p`
over `x` is the fibre of `Spec k' ⟶ Spec k`, a single point.

## Main results

* `Stacks.EtaleCohomology.isIso_residueFieldMap_of_isClosed`: `κ(g x) ⟶ κ(x)` is an
  isomorphism at a closed point `x` of a scheme locally of finite type over an algebraically
  closed field.
* `Stacks.EtaleCohomology.subsingleton_preimage_scalarExtensionFst`: the fibre of
  `X_{k'} ⟶ X` over a closed point has at most one point.
* `Stacks.EtaleCohomology.surjective_scalarExtensionFst`: `X_{k'} ⟶ X` is surjective.
* `Stacks.EtaleCohomology.scalarExtensionClosedPoint`: the closed point of `X_{k'}` over a closed
  point of `X`, and `Stacks.EtaleCohomology.eq_scalarExtensionClosedPoint` its uniqueness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [LocallyOfFiniteType g]

/-- **At a closed point the residue field is the base field**: for `X` locally of finite type
over an algebraically closed field `k` and `x` a closed point, `κ(g x) ⟶ κ(x)` is an
isomorphism. -/
theorem isIso_residueFieldMap_of_isClosed {x : X} (hx : IsClosed ({x} : Set X)) :
    IsIso (g.residueFieldMap x) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have := isAlgebraic_residueField_of_isClosed g hx
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := X.residueField x)
  have hcomp : ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (g x)) ≫
      g.residueFieldMap x = (Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation x := by
    rw [Category.assoc, Scheme.Γevaluation_naturality]
  have hsurj : Function.Surjective (g.residueFieldMap x) := by
    intro y
    obtain ⟨a, ha⟩ := hbij.2 y
    refine ⟨((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (g x)) a, ?_⟩
    rw [← ConcreteCategory.comp_apply, hcomp]
    exact ha
  exact ConcreteCategory.isIso_iff_bijective _ |>.2
    ⟨(g.residueFieldMap x).hom.injective, hsurj⟩

variable (k' : Type u) [Field k'] [Algebra k k']

/-- **The fibre of `X_{k'} ⟶ X` over a closed point has at most one point.** -/
theorem subsingleton_preimage_scalarExtensionFst {x : X} (hx : IsClosed ({x} : Set X)) :
    ((scalarExtensionFst k k' g).base ⁻¹' {x}).Subsingleton := by
  have := isIso_residueFieldMap_of_isClosed g hx
  have hpb := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom (algebraMap k k')))).flip x
  have hiso := hpb.isIso_fst_of_isIso
  have : Subsingleton (Spec (.of k')) := inferInstanceAs (Subsingleton (PrimeSpectrum k'))
  have hsub : Subsingleton ((Spec.map (CommRingCat.ofHom (algebraMap k k'))).fiber (g x)) :=
    (Scheme.Hom.fiberι _ _).isEmbedding.injective.subsingleton
  have key : ∀ {A B : Scheme.{u}} (T : A ⟶ B) [IsIso T] [Subsingleton B], Subsingleton A :=
    fun T _ _ => T.isOpenEmbedding.injective.subsingleton
  have : Subsingleton ((scalarExtensionFst k k' g).fiber x) := @key _ _ _ hiso hsub
  intro a ha b hb
  have e := (scalarExtensionFst k k' g).fiberHomeo x
  exact congrArg Subtype.val (e.symm.injective (Subsingleton.elim (e.symm ⟨a, ha⟩)
    (e.symm ⟨b, hb⟩)))

/-- **The projection `X_{k'} ⟶ X` is surjective.** -/
theorem surjective_scalarExtensionFst : Surjective (scalarExtensionFst k k' g) := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint k', Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  infer_instance

/-- The fibre of `X_{k'} ⟶ X` over a closed point is a single point. -/
theorem existsUnique_scalarExtensionFst_eq {x : X} (hx : IsClosed ({x} : Set X)) :
    ∃! y : scalarExtension k k' g, (scalarExtensionFst k k' g).base y = x := by
  obtain ⟨y, hy⟩ := (surjective_scalarExtensionFst g k').surj x
  exact ⟨y, hy, fun z hz => subsingleton_preimage_scalarExtensionFst g k' hx hz hy⟩

/-- **The point of `X_{k'}` over a closed point of `X` is closed.** -/
theorem isClosed_singleton_of_scalarExtensionFst_eq {x : X} (hx : IsClosed ({x} : Set X))
    {y : scalarExtension k k' g} (hy : (scalarExtensionFst k k' g).base y = x) :
    IsClosed ({y} : Set (scalarExtension k k' g)) := by
  have heq : ({y} : Set (scalarExtension k k' g)) = (scalarExtensionFst k k' g).base ⁻¹' {x} :=
    Set.ext fun z => ⟨fun hz => by rw [Set.mem_singleton_iff.1 hz]; exact hy,
      fun hz => subsingleton_preimage_scalarExtensionFst g k' hx hz hy⟩
  rw [heq]
  exact hx.preimage (scalarExtensionFst k k' g).base.hom.continuous

/-- **The closed point of `X_{k'}` over a closed point of `X`.** -/
def scalarExtensionClosedPoint (x : closedPoints X) : closedPoints (scalarExtension k k' g) :=
  ⟨(existsUnique_scalarExtensionFst_eq g k' x.2).choose,
    isClosed_singleton_of_scalarExtensionFst_eq g k' x.2
      (existsUnique_scalarExtensionFst_eq g k' x.2).choose_spec.1⟩

/-- The closed point of `X_{k'}` over a closed point `x` of `X` lies over `x`. -/
@[simp]
theorem scalarExtensionFst_scalarExtensionClosedPoint (x : closedPoints X) :
    (scalarExtensionFst k k' g).base (scalarExtensionClosedPoint g k' x).1 = x.1 :=
  (existsUnique_scalarExtensionFst_eq g k' x.2).choose_spec.1

/-- A point of `X_{k'}` over a closed point `x` of `X` is the closed point over `x`. -/
theorem eq_scalarExtensionClosedPoint (x : closedPoints X) {y : scalarExtension k k' g}
    (hy : (scalarExtensionFst k k' g).base y = x.1) : y = (scalarExtensionClosedPoint g k' x).1 :=
  (existsUnique_scalarExtensionFst_eq g k' x.2).choose_spec.2 y hy

/-- Distinct closed points of `X` have distinct closed points of `X_{k'}` over them. -/
theorem injective_scalarExtensionClosedPoint :
    Function.Injective (scalarExtensionClosedPoint g k') := fun x y hxy =>
  Subtype.ext ((scalarExtensionFst_scalarExtensionClosedPoint g k' x).symm.trans
    ((congrArg (fun z : closedPoints (scalarExtension k k' g) =>
      (scalarExtensionFst k k' g).base z.1) hxy).trans
        (scalarExtensionFst_scalarExtensionClosedPoint g k' y)))

end Stacks.EtaleCohomology

end
