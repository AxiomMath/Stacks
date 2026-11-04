module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Projectivization.Action
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.DualClosedPoints
public import StacksCore.Tactic.StacksAttribute

/-!
# Double transitivity of the projective linear group

The projective general linear group of a vector space `V` acts doubly transitively on the closed
points of `P(V) = Proj (Sym V)`: over an algebraically closed field those points are the classes
of nonzero linear functionals on `V`, and `GL(V)` already acts doubly transitively on pairs of
linearly independent vectors.

Along the way the quotient `PGL(V)` is identified with the invertible locus of the
projectivized endomorphism space, and the closed points of the projective space of the dual of
the endomorphism space — the parameter space of a linear projective transformation — are
identified with the classes of endomorphisms, which is the form in which `PGL(V)` enters a
moving-lemma argument.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.InvertibleEndomorphismClasses`: the classes of
  endomorphisms of `V` admitting an invertible representative.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.projGenLinGroupEquivInvertibleClasses`: `PGL(V)` as
  that locus.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.dualEndClosedPointsEquiv`: the closed points of
  `P((End V)ᵛ)` as the classes of endomorphisms.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.InvertibleParameterPoints` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.parameterPointToProjGenLinGroup`: the parameter
  points representing an invertible endomorphism, and the element of `PGL(V)` they name.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.projGenLinGroup_is_two_pretransitive`: the action of
  `PGL(V)` on the closed points of `P(V)` is doubly transitive.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.map_eq_map_iff`: two invertible linear maps induce
  the same morphism exactly when they differ by a unit scalar.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.parameterPoint_smul_eq_map`: on the invertible
  locus the parameter point acts by the morphism attached to its representative.

## Implementation notes

Double transitivity is transported along the identification of the closed points of `P(V)` with
the projectivization of the dual of `V`: a linear automorphism `e` of `V` acts on functionals by
`e.dualMap`, which corresponds to the action of `e` on `P(V)`, and every automorphism of the
dual is `e.dualMap` for a unique `e` when `V` is finite-dimensional. Mathlib's double
transitivity of the group of linear automorphisms on a projectivization then finishes the proof.

The inversion appearing in `parameterPoint_smul_eq_map` accounts for the contravariance of
`Proj`: the left action of a class is `Proj (Sym g⁻¹)`.

## References

* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
-/

@[expose] public section

open CategoryTheory

namespace LinearEquiv

/-- Over a finite-dimensional vector space every automorphism of the dual is the transpose of a
unique automorphism of the space. -/
public theorem exists_dualMap_eq {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (e : Module.Dual k V ≃ₗ[k] Module.Dual k V) :
    ∃ d : V ≃ₗ[k] V, d.dualMap = e := by
  refine ⟨(Module.evalEquiv k V).trans (e.dualMap.trans (Module.evalEquiv k V).symm), ?_⟩
  ext f v
  exact DFunLike.congr_fun
    ((Module.evalEquiv k V).apply_symm_apply (e.dualMap (Module.evalEquiv k V v))) f

end LinearEquiv

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u v

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

/-- The morphism attached to an invertible linear map carries the point cut out by a functional
to the point cut out by its transpose. -/
public theorem map_linearFunctionalPoint (g : LinearMap.GeneralLinearGroup k V)
    (f : Module.Dual k V) (hf : f ≠ 0) (hgf : (g : V →ₗ[k] V).dualMap f ≠ 0) :
    map k V g (linearFunctionalPoint k V f hf) =
      linearFunctionalPoint k V ((g : V →ₗ[k] V).dualMap f) hgf := by
  apply ProjectiveSpectrum.ext
  ext z
  show SymPow.symAlgMap (g : V →ₗ[k] V) z ∈
      (linearFunctionalPoint k V f hf).asHomogeneousIdeal ↔
    z ∈ (linearFunctionalPoint k V ((g : V →ₗ[k] V).dualMap f) hgf).asHomogeneousIdeal
  rw [linearFunctionalPoint_mem, linearFunctionalPoint_mem]
  show SymPow.symAlgMap f (SymPow.symAlgMap (g : V →ₗ[k] V) z) = 0 ↔
    SymPow.symAlgMap (f ∘ₗ (g : V →ₗ[k] V)) z = 0
  rw [SymPow.symAlgMap_comp_apply]

/-- An invertible linear map inducing the identity on `P(V)` is a unit scalar multiple of the
identity: it preserves every hyperplane, so it is a homothety. -/
public theorem exists_units_smul_id_of_map_eq_id [Nontrivial V]
    (g : LinearMap.GeneralLinearGroup k V) (hg : map k V g = 𝟙 _) :
    ∃ c : kˣ, (g : V →ₗ[k] V) = (c : k) • LinearMap.id := by
  have hdep : ∀ f : Module.Dual k V,
      ¬ LinearIndependent k ![f, (g : V →ₗ[k] V).dualMap f] := by
    intro f hli
    have hf : f ≠ 0 := by simpa using hli.ne_zero 0
    have hgf : (g : V →ₗ[k] V).dualMap f ≠ 0 := by
      intro hzero
      apply hf
      ext x
      obtain ⟨w, rfl⟩ := g.toLinearEquiv.surjective x
      exact DFunLike.congr_fun hzero w
    have hker : ∀ x, ((g : V →ₗ[k] V).dualMap f) x = 0 ↔ f x = 0 := by
      intro x
      have hp := congrArg (fun h : projectiveSpaceOfModule k V ⟶ projectiveSpaceOfModule k V =>
        h (linearFunctionalPoint k V f hf)) hg
      have he := congrArg (fun p : projectiveSpaceOfModule k V =>
        SymmetricAlgebra.ι k V x ∈ p.asHomogeneousIdeal) hp
      change (SymPow.symAlgMap (g : V →ₗ[k] V) (SymmetricAlgebra.ι k V x) ∈
        (linearFunctionalPoint k V f hf).asHomogeneousIdeal) =
          (SymmetricAlgebra.ι k V x ∈
            (linearFunctionalPoint k V f hf).asHomogeneousIdeal) at he
      simpa only [SymPow.symAlgMap_ι, linearFunctionalPoint_ι_mem,
        LinearMap.dualMap_apply] using Iff.of_eq he
    obtain ⟨c, hc⟩ := Module.Dual.exists_units_smul_eq_of_forall_eq_zero_iff hf hker
    have he : (c : k) • f = (1 : k) • ((g : V →ₗ[k] V).dualMap f) := by
      rw [hc, one_smul]
      rfl
    exact one_ne_zero (hli.eq_zero_of_pair' he).2
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
  have hga : (g : V →ₗ[k] V) = a • LinearMap.id := by
    ext x
    apply Module.eval_apply_injective k
    ext f
    simpa using DFunLike.congr_fun (DFunLike.congr_fun ha f) x
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_smul] at hga
    exact g.ne_zero hga
  exact ⟨Units.mk0 a ha0, hga⟩

/-- Two invertible linear maps induce the same morphism of projective spaces exactly when they
differ by a unit scalar. -/
public theorem map_eq_map_iff [Nontrivial V] (g h : LinearMap.GeneralLinearGroup k V) :
    map k V g = map k V h ↔ ∃ c : kˣ, (g : V →ₗ[k] V) = c • (h : V →ₗ[k] V) := by
  constructor
  · intro heq
    have hr : map k V (g * h⁻¹) = 𝟙 _ := by
      rw [map_mul, heq, ← map_mul, mul_inv_cancel, map_one]
    obtain ⟨c, hc⟩ := exists_units_smul_id_of_map_eq_id k V (g * h⁻¹) hr
    refine ⟨c, ?_⟩
    calc
      (g : V →ₗ[k] V) = ((g * h⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) * h := by
        simp
      _ = ((c : k) • (1 : V →ₗ[k] V)) * h := by rw [hc]; rfl
      _ = c • (h : V →ₗ[k] V) := by simp [Units.smul_def]
  · rintro ⟨c, hc⟩
    have hr : ((g * h⁻¹ : LinearMap.GeneralLinearGroup k V) : V →ₗ[k] V) =
        (c : k) • LinearMap.id := by
      show (g : V →ₗ[k] V) * (h⁻¹ : LinearMap.GeneralLinearGroup k V) = _
      rw [hc]
      simp [Units.smul_def]
      rfl
    calc
      map k V g = map k V ((g * h⁻¹) * h) := by simp
      _ = map k V (g * h⁻¹) ≫ map k V h := map_mul ..
      _ = map k V h := by rw [map_eq_id_of_eq_smul_id k V _ c hr, Category.id_comp]

/-- The classes of endomorphisms of `V` admitting an invertible representative: the invertible
locus of the projectivized endomorphism space. -/
public abbrev InvertibleEndomorphismClasses :=
  { p : Projectivization k (V →ₗ[k] V) //
    ∃ (g : LinearMap.GeneralLinearGroup k V) (hg : (g : V →ₗ[k] V) ≠ 0),
      p = Projectivization.mk k (g : V →ₗ[k] V) hg }

/-- Two invertible linear maps have the same class in `PGL(V)` exactly when they have the same
class in the projectivized endomorphism space. -/
public theorem mk_eq_mk_iff_projectivization [Nontrivial V]
    (g h : LinearMap.GeneralLinearGroup k V) :
    (g : ProjGenLinGroup k V) = (h : ProjGenLinGroup k V) ↔
      Projectivization.mk k (g : V →ₗ[k] V) g.ne_zero =
        Projectivization.mk k (h : V →ₗ[k] V) h.ne_zero := by
  rw [QuotientGroup.eq, MonoidHom.mem_ker, _root_.map_mul, _root_.map_inv, inv_mul_eq_one]
  have hAut : generalLinearToAut k V g = generalLinearToAut k V h ↔
      map k V g = map k V h :=
    ⟨fun he => congrArg Iso.inv he, fun he => inv_injective (Iso.ext he)⟩
  rw [hAut, map_eq_map_iff, Projectivization.mk_eq_mk_iff]
  exact exists_congr fun c => eq_comm

/-- The class in the projectivized endomorphism space of a projective linear transformation. -/
public noncomputable def toInvertibleClass [Nontrivial V] :
    ProjGenLinGroup k V → InvertibleEndomorphismClasses k V :=
  Quotient.lift
    (fun g => ⟨Projectivization.mk k (g : V →ₗ[k] V) g.ne_zero, ⟨g, g.ne_zero, rfl⟩⟩)
    (by
      intro g h hgh
      exact Subtype.ext ((mk_eq_mk_iff_projectivization k V g h).1 (Quotient.sound hgh)))

/-- Every class with an invertible representative comes from exactly one element of
`PGL(V)`. -/
public theorem toInvertibleClass_bijective [Nontrivial V] :
    Function.Bijective (toInvertibleClass k V) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with | h g =>
    induction y using Quotient.inductionOn with | h h =>
    intro he
    exact (mk_eq_mk_iff_projectivization k V g h).2 (congrArg Subtype.val he)
  · intro p
    obtain ⟨g, hg, he⟩ := p.property
    exact ⟨(g : ProjGenLinGroup k V), Subtype.ext he.symm⟩

/-- **`PGL(V)` is the invertible open locus of the projectivized endomorphism space.** The
quotient presentation of `PGL(V)` sends a projective linear transformation to the projective
class of any of its linear representatives. -/
@[stacks 0B2U "identification with the invertible open locus"]
public noncomputable def projGenLinGroupEquivInvertibleClasses [Nontrivial V] :
    ProjGenLinGroup k V ≃ InvertibleEndomorphismClasses k V :=
  Equiv.ofBijective (toInvertibleClass k V) (toInvertibleClass_bijective k V)

/-- The equivalence with the invertible locus sends a projective linear transformation to the
projective class of any of its linear representatives. -/
@[stacks 0B2U "representative formula for the invertible locus"]
public theorem projGenLinGroupEquivInvertibleClasses_apply [Nontrivial V]
    (g : LinearMap.GeneralLinearGroup k V) (hg : (g : V →ₗ[k] V) ≠ 0) :
    ((projGenLinGroupEquivInvertibleClasses k V) (g : ProjGenLinGroup k V)).val =
      Projectivization.mk k (g : V →ₗ[k] V) hg := rfl

/-- **The closed points of `P((End V)ᵛ)` are the projective classes of endomorphisms.** This is
the parameter space of a linear projective transformation. -/
@[stacks 0B2U "closed-point identification for the parameter space"]
public noncomputable def dualEndClosedPointsEquiv [IsAlgClosed k] [Module.Finite k V] :
    ClosedPoints k (Module.Dual k (V →ₗ[k] V)) ≃ Projectivization k (V →ₗ[k] V) :=
  (closedPointsEquivDual k (Module.Dual k (V →ₗ[k] V))).symm.trans
    (Projectivization.mapEquiv (Module.evalEquiv k (V →ₗ[k] V)).symm)

/-- The parameter point corresponding to a class of endomorphisms is cut out by the linear forms
annihilating that class. This fixes the identification. -/
@[stacks 0B2U "annihilator formula for the parameter-space identification"]
public theorem dualEndClosedPointsEquiv_apply [IsAlgClosed k] [Module.Finite k V]
    (p : ClosedPoints k (Module.Dual k (V →ₗ[k] V))) (φ : Module.Dual k (V →ₗ[k] V)) :
    SymmetricAlgebra.ι k (Module.Dual k (V →ₗ[k] V)) φ ∈ p.val.asHomogeneousIdeal ↔
      φ ((dualEndClosedPointsEquiv k V p).rep) = 0 := by
  set q := (closedPointsEquivDual k (Module.Dual k (V →ₗ[k] V))).symm p with hq
  have hp : closedPointOfDual k (Module.Dual k (V →ₗ[k] V)) q = p :=
    (closedPointsEquivDual k (Module.Dual k (V →ₗ[k] V))).apply_symm_apply p
  have hmem := closedPointOfDual_ι_mem k (Module.Dual k (V →ₗ[k] V)) q φ
  rw [hp] at hmem
  refine hmem.trans ?_
  show q.rep φ = 0 ↔
    φ ((Projectivization.mapEquiv (Module.evalEquiv k (V →ₗ[k] V)).symm q).rep) = 0
  rw [Projectivization.apply_mapEquiv_rep_eq_zero_iff]
  exact Iff.of_eq (congrArg (· = 0)
    (DFunLike.congr_fun ((Module.evalEquiv k (V →ₗ[k] V)).apply_symm_apply q.rep) φ).symm)

/-- The parameter points representing an invertible endomorphism: the open locus of the
parameter space on which a projective linear transformation is defined. -/
public abbrev InvertibleParameterPoints [IsAlgClosed k] [Module.Finite k V] :=
  { p : ClosedPoints k (Module.Dual k (V →ₗ[k] V)) //
    ∃ q : InvertibleEndomorphismClasses k V,
      (dualEndClosedPointsEquiv k V) p = q.val }

/-- The projective linear transformation named by an invertible parameter point. -/
public noncomputable def parameterPointToProjGenLinGroup
    [Nontrivial V] [IsAlgClosed k] [Module.Finite k V]
    (p : InvertibleParameterPoints k V) : ProjGenLinGroup k V :=
  (projGenLinGroupEquivInvertibleClasses k V).symm
    ⟨(dualEndClosedPointsEquiv k V) p.val,
      by obtain ⟨q, hq⟩ := p.property; rw [hq]; exact q.property⟩

/-- A parameter point represented by `g` names the class of `g` in `PGL(V)`. -/
@[stacks 0B2U "parameter point to projective linear transformation"]
public theorem parameterPointToProjGenLinGroup_of_rep
    [Nontrivial V] [IsAlgClosed k] [Module.Finite k V]
    (p : InvertibleParameterPoints k V) (g : LinearMap.GeneralLinearGroup k V)
    (hg : (g : V →ₗ[k] V) ≠ 0)
    (hpg : (dualEndClosedPointsEquiv k V) p.val = Projectivization.mk k (g : V →ₗ[k] V) hg) :
    parameterPointToProjGenLinGroup k V p = (g : ProjGenLinGroup k V) := by
  apply (projGenLinGroupEquivInvertibleClasses k V).injective
  apply Subtype.ext
  unfold parameterPointToProjGenLinGroup
  rwa [Equiv.apply_symm_apply,
    projGenLinGroupEquivInvertibleClasses_apply k V g hg]

/-- On a parameter point represented by `g`, the morphism in the moving family is the action of
the inverse element of `PGL(V)`; the inversion accounts for the contravariance of `Proj`. -/
@[stacks 0B2U "compatibility of the parameter-point action"]
public theorem parameterPoint_smul_eq_map
    [Nontrivial V] [IsAlgClosed k] [Module.Finite k V]
    (p : InvertibleParameterPoints k V) (g : LinearMap.GeneralLinearGroup k V)
    (hg : (g : V →ₗ[k] V) ≠ 0)
    (hpg : (dualEndClosedPointsEquiv k V) p.val = Projectivization.mk k (g : V →ₗ[k] V) hg)
    (x : projectiveSpaceOfModule k V) :
    (parameterPointToProjGenLinGroup k V p)⁻¹ • x = map k V g x := by
  rw [parameterPointToProjGenLinGroup_of_rep k V p g hg hpg]
  rfl

/-- The transpose action of a linear automorphism on the projectivized dual corresponds to its
action on the closed points of `P(V)`. -/
public theorem closedPointOfDual_dualMap_smul (e : V ≃ₗ[k] V)
    (p : Projectivization k (Module.Dual k V)) :
    (closedPointOfDual k V (e.dualMap • p)).val =
      map k V (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
        (closedPointOfDual k V p).val := by
  induction p using Projectivization.ind with | h f hf =>
  rw [Projectivization.smul_mk]
  exact (map_linearFunctionalPoint k V (LinearMap.GeneralLinearGroup.ofLinearEquiv e) f hf
    (e.dualMap.map_ne_zero_iff.mpr hf)).symm

/-- **Stacks Project, Tag 0B2U.** The projective general linear group of a finite-dimensional
vector space over an algebraically closed field acts doubly transitively on the closed points of
its projective space. -/
@[stacks 0B2U]
public lemma projGenLinGroup_is_two_pretransitive [IsAlgClosed k] [Module.Finite k V] :
    MulAction.IsMultiplyPretransitive (ProjGenLinGroup k V) (ClosedPoints k V) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  set E := closedPointsEquivDual k V with hE
  have hEapp (p : ClosedPoints k V) : closedPointOfDual k V (E.symm p) = p :=
    E.apply_symm_apply p
  have hab' : E.symm a ≠ E.symm b := fun h => hab (E.symm.injective h)
  have hcd' : E.symm c ≠ E.symm d := fun h => hcd (E.symm.injective h)
  obtain ⟨e, he₁, he₂⟩ :=
    (MulAction.is_two_pretransitive_iff
      (G := Module.Dual k V ≃ₗ[k] Module.Dual k V)
      (α := Projectivization k (Module.Dual k V))).mp inferInstance hab' hcd'
  obtain ⟨L, hL⟩ := LinearEquiv.exists_dualMap_eq e
  set g := LinearMap.GeneralLinearGroup.ofLinearEquiv L with hg
  have key : ∀ x y : ClosedPoints k V, e • E.symm x = E.symm y → map k V g x.val = y.val := by
    intro x y hxy
    have h := closedPointOfDual_dualMap_smul k V L (E.symm x)
    rw [hL, hxy, hEapp, hEapp] at h
    exact h.symm
  exact ⟨((g⁻¹ : LinearMap.GeneralLinearGroup k V) : ProjGenLinGroup k V),
    Subtype.ext (key a c he₁), Subtype.ext (key b d he₂)⟩

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
