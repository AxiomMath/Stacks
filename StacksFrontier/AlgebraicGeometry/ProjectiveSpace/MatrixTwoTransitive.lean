module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.ProjectiveLinearGroup
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.MatrixSubstitution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The matrix action on projective space is two-transitive on rational points

Over an algebraically closed field `K` the general linear group of `(n + 1) × (n + 1)` matrices
acts on `ℙⁿ_K` by `AlgebraicGeometry.projectiveSpaceMatrixToAut`, and this file records that the
action is *two-transitive on the `K`-rational points*: any ordered pair of distinct `K`-points of
`ℙⁿ_K` is carried to any other ordered pair of distinct `K`-points by one matrix.

This is the input the contraction step of [Stacks, Tag 0AEM] needs and which the source leaves as
an exercise. Nothing here is new mathematics: two-transitivity of `PGL(V)` on the closed points of
`𝐏(V) = Proj (Sym V)` is already
`AlgebraicGeometry.ProjectiveSpaceOfModule.projGenLinGroup_is_two_pretransitive`
(Stacks 0B2U). What this file does is transport that statement across the two translations the
contraction step needs: from `PGL(V)` to invertible matrices acting on the library's model of
projective space, and from closed points of the topological space to `K`-rational points, that is
sections of the structure morphism.

## Main results

* `AlgebraicGeometry.exists_matrixToAut_apply_eq_apply_eq`: two-transitivity on the closed points
  of `ℙⁿ_K`.
* `AlgebraicGeometry.exists_matrixToAut_apply_eq`: transitivity on the closed points, given a
  single pair of distinct closed points to start from.
* `AlgebraicGeometry.exists_comp_matrixToAut_hom_eq_and_eq`: **two-transitivity on the
  `K`-rational points.**
* `AlgebraicGeometry.exists_comp_matrixToAut_hom_eq`: **transitivity on the `K`-rational
  points.**

## Implementation notes

The passage from closed points to rational points is Mathlib's
`AlgebraicGeometry.pointEquivClosedPoint`: over an algebraically closed field the closed points of
a scheme locally of finite type are exactly the images of the sections of its structure morphism.
Two sections with the same image point are therefore equal
(`AlgebraicGeometry.ext_of_apply_closedPoint_eq`), which is what turns an equality of points into
an equality of morphisms.

Transitivity is *not* proved from scratch: a two-transitive action of a group on a set with at
least two elements is transitive, and the two distinct elements are available wherever this is
used — the contraction step of 0AEM has a pair of distinct rational points in hand. Carrying them
as hypotheses avoids having to count the closed points of `ℙⁿ_K`.

## References

* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### A two-transitive action is transitive -/

/-- **A two-transitive action of a group on a set with two distinct elements is transitive.**
Rather than counting the elements of the set, the two distinct elements are taken as an argument:
at the only place this is used, the contraction step of [Stacks, Tag 0AEM], a pair of distinct
points is exactly what is in hand. -/
theorem exists_smul_eq_of_isMultiplyPretransitive_two {G α : Type*} [Group G] [MulAction G α]
    [MulAction.IsMultiplyPretransitive G α 2] {u v : α} (huv : u ≠ v) (a b : α) :
    ∃ g : G, g • a = b := by
  have key : ∀ p : α, ∃ z : α, p ≠ z := fun p => by
    by_cases h : u = p
    · exact ⟨v, fun hv => huv (h.trans hv)⟩
    · exact ⟨u, fun hv => h hv.symm⟩
  obtain ⟨z, hz⟩ := key a
  obtain ⟨w, hw⟩ := key b
  obtain ⟨g, hg, -⟩ :=
    (MulAction.is_two_pretransitive_iff (G := G) (α := α)).1 inferInstance hz hw
  exact ⟨g, hg⟩

/-! ### Two-transitivity on the closed points of `𝐏(V)`, as a statement about linear maps -/

namespace ProjectiveSpaceOfModule

/-- A coset action on closed points, lifted to the general linear group. -/
private theorem map_inv_apply_eq_of_mk_smul_eq {k V : Type u} [Field k] [AddCommGroup V]
    [Module k V] (h : LinearMap.GeneralLinearGroup k V)
    {x y : ClosedPoints k V} (hg : (QuotientGroup.mk h : ProjGenLinGroup k V) • x = y) :
    map k V h⁻¹ x.val = y.val := by
  have h₁ := congrArg Subtype.val hg
  rwa [coe_smul_closedPoints, mk_smul_eq_map] at h₁

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [IsAlgClosed k]
  [Module.Finite k V]

/-- **The general linear group of a finite-dimensional vector space over an algebraically closed
field carries any ordered pair of distinct closed points of its projective space to any other.**

This is [Stacks, Tag 0B2U] —
`AlgebraicGeometry.ProjectiveSpaceOfModule.projGenLinGroup_is_two_pretransitive` — with the
element of `PGL(V)` it produces lifted to the general linear group and its action spelled out as
`AlgebraicGeometry.ProjectiveSpaceOfModule.map`. -/
theorem exists_map_apply_eq_apply_eq (a b c d : ClosedPoints k V) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : LinearMap.GeneralLinearGroup k V,
      map k V g a.val = c.val ∧ map k V g b.val = d.val := by
  obtain ⟨g, hg₁, hg₂⟩ := (MulAction.is_two_pretransitive_iff).1
    (projGenLinGroup_is_two_pretransitive k V) hab hcd
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨h⁻¹, map_inv_apply_eq_of_mk_smul_eq h hg₁, map_inv_apply_eq_of_mk_smul_eq h hg₂⟩

/-- **The same action is transitive on the closed points**, given a pair of distinct closed
points to start from. -/
theorem exists_map_apply_eq {u v : ClosedPoints k V} (huv : u ≠ v) (a b : ClosedPoints k V) :
    ∃ g : LinearMap.GeneralLinearGroup k V, map k V g a.val = b.val := by
  have := projGenLinGroup_is_two_pretransitive k V
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMultiplyPretransitive_two
    (G := ProjGenLinGroup k V) huv a b
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨h⁻¹, map_inv_apply_eq_of_mk_smul_eq h hg⟩

end ProjectiveSpaceOfModule

/-! ### Two-transitivity on the closed points of `ℙⁿ_K` -/

section Matrix

variable (K : Type u) [Field K] (n : ℕ)

/-- The action of a matrix on a point of `ℙⁿ_K`, read through the identification of `ℙⁿ_K` with
the projective space of `Fin (n + 1) → K` given by the standard basis. -/
theorem projectiveSpaceMatrixToAut_hom_apply (M : Matrix.GeneralLinearGroup (Fin (n + 1)) K)
    (p : projectiveSpaceOverRing n (.of K)) :
    (projectiveSpaceMatrixToAut K n M).hom p =
      (projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1)))).hom
        (ProjectiveSpaceOfModule.map K (Fin (n + 1) → K)
            (Matrix.GeneralLinearGroup.toLin M)⁻¹
          ((projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1)))).inv p)) := by
  rw [show (projectiveSpaceMatrixToAut K n M).hom = _ from
      projectiveSpaceLinearToAut_hom (Pi.basisFun K (Fin (n + 1)))
        (Matrix.GeneralLinearGroup.toLin M),
    Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]

/-- The standard-basis identification of `𝐏(Fin (n + 1) → K)` with `ℙⁿ_K` recovers a point of
`ℙⁿ_K` from its preimage. -/
theorem projectiveSpaceOfModuleIso_hom_inv_apply (p : projectiveSpaceOverRing n (.of K)) :
    (projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1)))).hom
        ((projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1)))).inv p) = p :=
  (Scheme.homeoOfIso (projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1))))).apply_symm_apply p

/-- That identification is injective on points in the direction used below. -/
theorem projectiveSpaceOfModuleIso_inv_injective {p q : projectiveSpaceOverRing n (.of K)}
    (h : (projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1)))).inv p =
      (projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1)))).inv q) : p = q := by
  rw [← projectiveSpaceOfModuleIso_hom_inv_apply K n p,
    ← projectiveSpaceOfModuleIso_hom_inv_apply K n q, h]

/-- A closed point of `ℙⁿ_K` has a closed preimage in `𝐏(Fin (n + 1) → K)`. -/
theorem isClosed_singleton_projectiveSpaceOfModuleIso_inv
    {p : projectiveSpaceOverRing n (.of K)} (hp : IsClosed ({p} : Set _)) :
    IsClosed ({(projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1)))).inv p} : Set _) := by
  have h :=
    (Scheme.homeoOfIso
      (projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1)))).symm).isClosedMap _ hp
  rwa [Set.image_singleton] at h

/-- The matrix attached to `g⁻¹` sends `p` to `q` once `g` sends the preimage of `p` to that
of `q`. -/
private theorem matrixToAut_symm_inv_hom_apply_eq
    (g : LinearMap.GeneralLinearGroup K (Fin (n + 1) → K)) {p q : projectiveSpaceOverRing n (.of K)}
    (h : ProjectiveSpaceOfModule.map K (Fin (n + 1) → K) g
      ((projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1)))).inv p) =
      (projectiveSpaceOfModuleIso (Pi.basisFun K (Fin (n + 1)))).inv q) :
    (projectiveSpaceMatrixToAut K n (Matrix.GeneralLinearGroup.toLin.symm g⁻¹)).hom p = q := by
  rw [projectiveSpaceMatrixToAut_hom_apply, MulEquiv.apply_symm_apply, inv_inv, h]
  exact projectiveSpaceOfModuleIso_hom_inv_apply K n q

variable [IsAlgClosed K]

/-- **The matrix action on `ℙⁿ_K` carries any ordered pair of distinct closed points to any
other**, for `K` algebraically closed. -/
theorem exists_matrixToAut_apply_eq_apply_eq
    (a b c d : projectiveSpaceOverRing n (.of K))
    (ha : IsClosed ({a} : Set _)) (hb : IsClosed ({b} : Set _))
    (hc : IsClosed ({c} : Set _)) (hd : IsClosed ({d} : Set _))
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ M : Matrix.GeneralLinearGroup (Fin (n + 1)) K,
      (projectiveSpaceMatrixToAut K n M).hom a = c ∧
        (projectiveSpaceMatrixToAut K n M).hom b = d := by
  obtain ⟨g, hg₁, hg₂⟩ := ProjectiveSpaceOfModule.exists_map_apply_eq_apply_eq K
    (Fin (n + 1) → K)
    ⟨_, isClosed_singleton_projectiveSpaceOfModuleIso_inv K n ha⟩
    ⟨_, isClosed_singleton_projectiveSpaceOfModuleIso_inv K n hb⟩
    ⟨_, isClosed_singleton_projectiveSpaceOfModuleIso_inv K n hc⟩
    ⟨_, isClosed_singleton_projectiveSpaceOfModuleIso_inv K n hd⟩
    (fun h => hab (projectiveSpaceOfModuleIso_inv_injective K n (congrArg Subtype.val h)))
    (fun h => hcd (projectiveSpaceOfModuleIso_inv_injective K n (congrArg Subtype.val h)))
  exact ⟨_, matrixToAut_symm_inv_hom_apply_eq K n g hg₁,
    matrixToAut_symm_inv_hom_apply_eq K n g hg₂⟩

/-- **The matrix action on `ℙⁿ_K` is transitive on the closed points**, given a pair of distinct
closed points to start from. -/
theorem exists_matrixToAut_apply_eq
    {u v : projectiveSpaceOverRing n (.of K)}
    (hu : IsClosed ({u} : Set _)) (hv : IsClosed ({v} : Set _)) (huv : u ≠ v)
    (a b : projectiveSpaceOverRing n (.of K))
    (ha : IsClosed ({a} : Set _)) (hb : IsClosed ({b} : Set _)) :
    ∃ M : Matrix.GeneralLinearGroup (Fin (n + 1)) K,
      (projectiveSpaceMatrixToAut K n M).hom a = b := by
  obtain ⟨g, hg⟩ := ProjectiveSpaceOfModule.exists_map_apply_eq K (Fin (n + 1) → K)
    (u := ⟨_, isClosed_singleton_projectiveSpaceOfModuleIso_inv K n hu⟩)
    (v := ⟨_, isClosed_singleton_projectiveSpaceOfModuleIso_inv K n hv⟩)
    (fun h => huv (projectiveSpaceOfModuleIso_inv_injective K n (congrArg Subtype.val h)))
    ⟨_, isClosed_singleton_projectiveSpaceOfModuleIso_inv K n ha⟩
    ⟨_, isClosed_singleton_projectiveSpaceOfModuleIso_inv K n hb⟩
  exact ⟨_, matrixToAut_symm_inv_hom_apply_eq K n g hg⟩

end Matrix

/-! ### Two-transitivity on the rational points of `ℙⁿ_K` -/

section RationalPoints

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- **A section of the structure morphism of a scheme locally of finite type over an
algebraically closed field has a closed image point.** This is one half of
`AlgebraicGeometry.pointEquivClosedPoint`. -/
theorem isClosed_singleton_apply_closedPoint {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    IsClosed ({p (IsLocalRing.closedPoint K)} : Set X) :=
  (pointEquivClosedPoint f ⟨p, hp⟩).2

/-- **Two rational points with the same image point are equal**, over an algebraically closed
field. This is `AlgebraicGeometry.ext_of_apply_closedPoint_eq`, restated as the contrapositive
used below. -/
@[ega "IV 10.10.3" "partial"]
theorem apply_closedPoint_ne_of_ne {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] {p q : Spec (.of K) ⟶ X} (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _)
    (hpq : p ≠ q) :
    p (IsLocalRing.closedPoint K) ≠ q (IsLocalRing.closedPoint K) := fun h =>
  hpq (ext_of_apply_closedPoint_eq f hp hq h)

variable (n : ℕ)

/-- Two `K`-rational points moved by a matrix agree once their image points do. -/
private theorem comp_matrixToAut_hom_eq_of_apply_eq (M : Matrix.GeneralLinearGroup (Fin (n + 1)) K)
    {a b : Spec (.of K) ⟶ projectiveSpaceOverRing n (.of K)}
    (ha : a ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) = 𝟙 _)
    (hb : b ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) = 𝟙 _)
    (h : (projectiveSpaceMatrixToAut K n M).hom (a (IsLocalRing.closedPoint K)) =
      b (IsLocalRing.closedPoint K)) :
    a ≫ (projectiveSpaceMatrixToAut K n M).hom = b :=
  ext_of_apply_closedPoint_eq _
    (by rw [Category.assoc, projectiveSpaceMatrixToAut_hom_comp_structureMorphism, ha]) hb
    ((Scheme.Hom.comp_apply a _ _).trans h)

/-- **The matrix action on `ℙⁿ_K` carries any ordered pair of distinct `K`-rational points to any
other**, for `K` algebraically closed.

This is the form the contraction step of [Stacks, Tag 0AEM] uses: the source argues with rational
points, and what it needs of the group `(GL_{2,k})^n` is exactly that its factors move a pair of
distinct rational points of `ℙ¹` to any other such pair. -/
theorem exists_comp_matrixToAut_hom_eq_and_eq
    (a b c d : Spec (.of K) ⟶ projectiveSpaceOverRing n (.of K))
    (ha : a ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) = 𝟙 _)
    (hb : b ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) = 𝟙 _)
    (hc : c ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) = 𝟙 _)
    (hd : d ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) = 𝟙 _)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ M : Matrix.GeneralLinearGroup (Fin (n + 1)) K,
      a ≫ (projectiveSpaceMatrixToAut K n M).hom = c ∧
        b ≫ (projectiveSpaceMatrixToAut K n M).hom = d := by
  obtain ⟨M, hM₁, hM₂⟩ := exists_matrixToAut_apply_eq_apply_eq K n
    (a (IsLocalRing.closedPoint K)) (b (IsLocalRing.closedPoint K))
    (c (IsLocalRing.closedPoint K)) (d (IsLocalRing.closedPoint K))
    (isClosed_singleton_apply_closedPoint K _ a ha)
    (isClosed_singleton_apply_closedPoint K _ b hb)
    (isClosed_singleton_apply_closedPoint K _ c hc)
    (isClosed_singleton_apply_closedPoint K _ d hd)
    (apply_closedPoint_ne_of_ne K _ ha hb hab) (apply_closedPoint_ne_of_ne K _ hc hd hcd)
  exact ⟨M, comp_matrixToAut_hom_eq_of_apply_eq K n M ha hc hM₁,
    comp_matrixToAut_hom_eq_of_apply_eq K n M hb hd hM₂⟩

/-- **The matrix action on `ℙⁿ_K` is transitive on the `K`-rational points**, given a pair of
distinct rational points to start from. -/
theorem exists_comp_matrixToAut_hom_eq
    {u v : Spec (.of K) ⟶ projectiveSpaceOverRing n (.of K)}
    (hu : u ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) = 𝟙 _)
    (hv : v ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) = 𝟙 _) (huv : u ≠ v)
    (a b : Spec (.of K) ⟶ projectiveSpaceOverRing n (.of K))
    (ha : a ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) = 𝟙 _)
    (hb : b ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) = 𝟙 _) :
    ∃ M : Matrix.GeneralLinearGroup (Fin (n + 1)) K,
      a ≫ (projectiveSpaceMatrixToAut K n M).hom = b := by
  obtain ⟨M, hM⟩ := exists_matrixToAut_apply_eq K n
    (isClosed_singleton_apply_closedPoint K _ u hu)
    (isClosed_singleton_apply_closedPoint K _ v hv)
    (apply_closedPoint_ne_of_ne K _ hu hv huv)
    (a (IsLocalRing.closedPoint K)) (b (IsLocalRing.closedPoint K))
    (isClosed_singleton_apply_closedPoint K _ a ha)
    (isClosed_singleton_apply_closedPoint K _ b hb)
  exact ⟨M, comp_matrixToAut_hom_eq_of_apply_eq K n M ha hb hM⟩

end RationalPoints

end AlgebraicGeometry

end
