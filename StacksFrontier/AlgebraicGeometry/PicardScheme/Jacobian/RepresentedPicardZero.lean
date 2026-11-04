module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardLocallyTrivial
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# A group scheme representing the degree-zero rigidified Picard functor

Let `f : X ⟶ S` be a proper relative curve with a section `σ`, and let `A` be a group object in
`S`-schemes whose functor of points is identified, as a functor to groups, with
`Pic⁰_{X/S,σ}` (`Stacks.RigidifiedPicard.functorZero`). This file records what such an
identification gives on Picard classes, together with two facts about Picard groups used with it.

## Main definitions

* `Stacks.RigidifiedPicard.representedClass`: the class in `Pic(X_T)` classified by `T ⟶ A`.
* `Stacks.RigidifiedPicard.classifyingHom`: the morphism `T ⟶ A` classifying a rigidified class
  of degree zero.

## Main results

* `Stacks.RigidifiedPicard.eq_zero_of_subsingleton`: the Picard group of a one-point scheme is
  trivial.
* `Stacks.RigidifiedPicard.relativeInvertibleDegreeHomAt_eq_invertibleCurveDegreeHom`: over a
  field the degree on the fibre is the degree.
* `Stacks.RigidifiedPicard.representedClass_injective`, `representedClass_mul`,
  `representedClass_zpow`, `representedClass_comp`: the classified class is injective, a group
  homomorphism, and natural in `T`.

## References

* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.RigidifiedPicard

/-! ### Picard groups of one-point schemes -/

/-- **The Picard group of a scheme with a single point is trivial**: an invertible module is
trivial on a neighbourhood of the point, which is the whole scheme. -/
theorem eq_zero_of_subsingleton {Y : Scheme.{u}} [Subsingleton Y] [Nonempty Y]
    (N : Stacks.Picard.ofScheme Y) : N = 0 := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨U, hyU, hU⟩ := Stacks.Picard.exists_mem_schemePullbackClass_eq_zero N y
  obtain rfl : U = ⊤ := by
    ext z
    exact ⟨fun _ => trivial, fun _ => Subsingleton.elim y z ▸ hyU⟩
  have h := congrArg (Stacks.Picard.schemePullbackClass Y.topIso.inv) hU
  rw [Stacks.Picard.schemePullbackClass_comp, Scheme.toIso_inv_ι,
    Stacks.Picard.schemePullbackClass_id] at h
  exact h.trans (map_zero (Stacks.Picard.schemePullbackClassHom Y.topIso.inv))

/-! ### Degrees over a field -/

/-- **Over a field the degree on the fibre is the degree.** For a scheme `Y` proper of dimension
at most one over a field `k`, the degree of a Picard class on the fibre of `Y ⟶ Spec k` over the
point of `Spec k` is its degree on `Y`: the fibre is the base change of `Y` along the
residue-field point, a field extension of `k`, and the degree is invariant under field
extension (Tag 0B59). -/
theorem relativeInvertibleDegreeHomAt_eq_invertibleCurveDegreeHom {k : Type u} [Field k]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) [IsProper π]
    (hdim : ∀ t, topologicalKrullDim ↥(π.fiber t) ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (t : Spec (.of k)) (x : Stacks.Picard.ofScheme Y) :
    relativeInvertibleDegreeHomAt π hdim t x = invertibleCurveDegreeHom k π hdimY x := by
  let ψ : CommRingCat.of k ⟶ (Spec (.of k)).residueField t :=
    Spec.preimage ((Spec (.of k)).fromSpecResidueField t)
  let : Algebra k ((Spec (.of k)).residueField t) := ψ.hom.toAlgebra
  have hψ : Spec.map (CommRingCat.ofHom (algebraMap k ((Spec (.of k)).residueField t))) =
      (Spec (.of k)).fromSpecResidueField t := Spec.map_preimage _
  have h : IsPullback (π.fiberι t) (π.fiberToSpecResidueField t) π
      (Spec.map (CommRingCat.ofHom (algebraMap k ((Spec (.of k)).residueField t)))) :=
    hψ ▸ IsPullback.of_hasPullback π _
  rw [relativeInvertibleDegreeHomAt_apply]
  exact @invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k
    ((Spec (.of k)).residueField t) _ _ _ _ _ _ _ _ h _
    (isProper_fiberToSpecResidueField π t) hdimY (hdim t) x

/-! ### A group scheme representing `Pic⁰_{X/S,σ}` -/

section Represented

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [LocallyOfFiniteType f]
  (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
  {A : Grp (Over S)} (e : CategoryTheory.yonedaGrp.obj A ≅ functorZero f hdim σ hσ)

/-- The Picard class of `X_T` classified by a morphism `T ⟶ A`, through a representation of
`Pic⁰_{X/S,σ}` by `A`. -/
def representedClass {T : Over S} (a : T ⟶ A.X) : Stacks.Picard.ofScheme (bc f T) :=
  smallEquiv _ (Multiplicative.toAdd ((e.hom.app (op T)).hom a)).1.1

/-- The class classified by a morphism `T ⟶ A` determines the morphism. -/
theorem representedClass_injective (T : Over S) :
    Function.Injective (representedClass f hdim σ hσ e (T := T)) := by
  intro a b hab
  have h0 : (Multiplicative.toAdd ((e.hom.app (op T)).hom a)).1.1 =
      (Multiplicative.toAdd ((e.hom.app (op T)).hom b)).1.1 := (smallEquiv (bc f T)).injective hab
  have h1 : (Multiplicative.toAdd ((e.hom.app (op T)).hom a)) =
      (Multiplicative.toAdd ((e.hom.app (op T)).hom b)) :=
    Subtype.ext (Subtype.ext h0)
  have h2 : (e.hom.app (op T)).hom a = (e.hom.app (op T)).hom b := h1
  have h3 := congrArg (e.inv.app (op T)).hom h2
  have ha := congrArg (fun φ => φ.hom a) (e.hom_inv_id_app (op T))
  have hb := congrArg (fun φ => φ.hom b) (e.hom_inv_id_app (op T))
  simp only [GrpCat.hom_comp, MonoidHom.coe_comp] at ha hb
  exact ha.symm.trans (h3.trans hb)

/-- The class classified by a product `a * b` of morphisms `T ⟶ A` is the sum of the classes
classified by `a` and by `b`. -/
theorem representedClass_mul {T : Over S} (a b : T ⟶ A.X) :
    representedClass f hdim σ hσ e (a * b) =
      representedClass f hdim σ hσ e a + representedClass f hdim σ hσ e b := by
  have h := (e.hom.app (op T)).hom.map_mul a b
  simp only [representedClass]
  rw [← map_add]
  congr 1
  exact congrArg (fun z => (Multiplicative.toAdd z).1.1) h

/-- The class classified by `a ^ n` is `n` times the class classified by `a`. -/
theorem representedClass_zpow {T : Over S} (a : T ⟶ A.X) (n : ℤ) :
    representedClass f hdim σ hσ e (a ^ n) = n • representedClass f hdim σ hσ e a := by
  have h := (e.hom.app (op T)).hom.map_zpow a n
  simp only [representedClass]
  rw [← map_zsmul]
  congr 1
  exact congrArg (fun z => (Multiplicative.toAdd z).1.1) h

/-- **Naturality of the classified class**: the class classified by `g ≫ a` is the pullback of
the class classified by `a` along `X_{T'} ⟶ X_T`. -/
theorem representedClass_comp {T' T : Over S} (g : T' ⟶ T) (a : T ⟶ A.X) :
    representedClass f hdim σ hσ e (g ≫ a) =
      Stacks.Picard.schemePullbackClass (bcMap f g) (representedClass f hdim σ hσ e a) := by
  have h := congrArg (fun φ => φ.hom a) (e.hom.naturality g.op)
  simp only [GrpCat.hom_comp, MonoidHom.coe_comp] at h
  simp only [representedClass]
  rw [← smallEquiv_smallSchemePullbackClassHom]
  congr 1
  exact congrArg (fun z => (Multiplicative.toAdd z).1.1) h

/-- The class classified by a morphism `T ⟶ A` is the image of a rigidified class of degree zero.
-/
theorem representedClass_mem_groupZero {T : Over S} (a : T ⟶ A.X) :
    ∃ x ∈ groupZero f hdim σ hσ T, smallEquiv _ x.1 = representedClass f hdim σ hσ e a :=
  ⟨_, (Multiplicative.toAdd ((e.hom.app (op T)).hom a)).2, rfl⟩

/-- The morphism into `A` classifying a rigidified class of degree zero. -/
def classifyingHom {T : Over S} (x : group f σ hσ T) (hx : x ∈ groupZero f hdim σ hσ T) :
    T ⟶ A.X :=
  (e.inv.app (op T)).hom (Multiplicative.ofAdd ⟨x, hx⟩)

/-- The class classified by `classifyingHom x hx` is the class of `x`. -/
theorem representedClass_classifyingHom {T : Over S} (x : group f σ hσ T)
    (hx : x ∈ groupZero f hdim σ hσ T) :
    representedClass f hdim σ hσ e (classifyingHom f hdim σ hσ e x hx) = smallEquiv _ x.1 := by
  simp only [representedClass, classifyingHom]
  have : (e.hom.app (op T)).hom ((e.inv.app (op T)).hom (Multiplicative.ofAdd ⟨x, hx⟩)) =
      Multiplicative.ofAdd ⟨x, hx⟩ := by
    have h := congrArg (fun φ => φ.hom (Multiplicative.ofAdd ⟨x, hx⟩)) (e.inv_hom_id_app (op T))
    simp only [GrpCat.hom_comp, MonoidHom.coe_comp] at h
    exact h
  rw [this]
  rfl

/-- Every rigidified class of degree zero is classified by a morphism into `A`. -/
theorem exists_representedClass_eq {T : Over S} (x : group f σ hσ T)
    (hx : x ∈ groupZero f hdim σ hσ T) :
    ∃ a : T ⟶ A.X, representedClass f hdim σ hσ e a = smallEquiv _ x.1 :=
  ⟨_, representedClass_classifyingHom f hdim σ hσ e x hx⟩

end Represented

end Stacks.RigidifiedPicard
