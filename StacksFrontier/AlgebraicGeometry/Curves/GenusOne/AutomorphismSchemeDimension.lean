module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.AutomorphismScheme
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesFibreProductFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesJInvariant
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension

/-!
# The automorphism group scheme of a curve of genus one has dimension one

Let `X` be a proper scheme over a field `k`, smooth of relative dimension one, with
`dim_k H⁰(X, 𝒪_X) = 1`, genus one and a rational point `p`, and let `G` be the automorphism scheme
of `AlgebraicGeometry.GenusOne.autSchemeOver`, built from the fibre product
`Spec k ×_{𝓜₁,₁} X` of the elliptic curve `(X, p)` and of the diagonal family. The morphism
`G ⟶ X, ψ ↦ ψ(p)` is **finite**, because the isomorphisms between two elliptic curves form a
finite scheme; and when `k` is algebraically closed it is **surjective**, because every pointed
curve `(X, q)` is isomorphic to `(X, p)`. Hence `G` has the dimension of `X`, namely one.

The surjectivity is the transitivity of the automorphisms of `X` on its rational points, and it is
proved through the `j`-invariant: the `j`-invariant of `(X, q)` is the value at `q` of the
`j`-invariant of the diagonal family, a global function on `X`
(`AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.exists_jInvariant`), hence a constant;
and over an algebraically closed field two elliptic curves with the same `j`-invariant are
isomorphic (`WeierstrassCurve.exists_variableChange_of_j_eq`).

## Main results

* `AlgebraicGeometry.GenusOne.isFinite_autScheme_toCurve`: `G ⟶ X` is finite.
* `AlgebraicGeometry.GenusOne.exists_comparison_of_isAlgClosed`: over an algebraically closed
  field every pointed curve `(X, q)` is isomorphic to `(X, p)`.
* `AlgebraicGeometry.GenusOne.surjective_autScheme_toCurve`: `G ⟶ X` is surjective.
* `AlgebraicGeometry.GenusOne.topologicalKrullDim_autScheme`: **`G` has dimension one.**
* `AlgebraicGeometry.GenusOne.exists_weierstrassComparison`: near every rational point the
  diagonal family is a restriction of the Weierstrass family.
* `AlgebraicGeometry.GenusOne.autScheme_topologicalKrullDim_eq_one_of_genus_eq_one`:
  **[Stacks, Tag 0DSV], genus one**: for a smooth proper curve of genus one over an
  algebraically closed field the automorphism functor is representable, and every representing
  scheme has dimension one.

## Implementation notes

The automorphism group scheme is a representing object of
`AlgebraicGeometry.Scheme.autFunctor`; since representing objects are unique up to isomorphism,
the dimension statement is made for every representing object. The hypotheses are those of the
source: a smooth curve (`AlgebraicGeometry.IsCurve` with `Smooth`), proper as every object of the
stack of curves over `k` is, of genus one in the sense of `AlgebraicGeometry.genus`, over an
algebraically closed field. A rational point exists because `k` is algebraically closed, and
`H⁰(X, 𝒪_X) = k` because `X` is a proper variety over an algebraically closed field.

## References

* [Stacks Project, Tag 0DSV](https://stacks.math.columbia.edu/tag/0DSV)
* [Stacks Project, Tag 072M](https://stacks.math.columbia.edu/tag/072M)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

/-- **Elliptic curves with the same `j`-invariant are isomorphic over a ring isomorphic to a
separably closed field.** -/
theorem WeierstrassCurve.exists_variableChange_of_j_eq_of_ringEquiv {F K : Type*} [CommRing F]
    [Field K] [IsSepClosed K] (φ : F ≃+* K) (C₁ C₂ : WeierstrassCurve F) [C₁.IsElliptic]
    [C₂.IsElliptic] (h : C₁.j = C₂.j) : ∃ γ : WeierstrassCurve.VariableChange F, γ • C₂ = C₁ := by
  have hj : (C₂.map (φ : F →+* K)).j = (C₁.map (φ : F →+* K)).j := by
    rw [WeierstrassCurve.map_j, WeierstrassCurve.map_j, h]
  obtain ⟨γ, hγ⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj
  refine ⟨γ.map (φ.symm : K →+* F), ?_⟩
  have := congrArg (fun C : WeierstrassCurve K ↦ C.map (φ.symm : K →+* F)) hγ
  simp only [← WeierstrassCurve.map_variableChange, WeierstrassCurve.map_map] at this
  simpa [RingEquiv.symm_comp] using this

namespace AlgebraicGeometry.GenusOne

open ModuliEllipticCurves

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Weierstrass presentations at rational points -/

/-- **Near every rational point the diagonal family is a restriction of the Weierstrass family.**
For a rational point `q`, there is a triple comparing the Weierstrass family with the diagonal
family over `Spec k`, whose morphism to `X` is `q`. -/
theorem exists_weierstrassComparison (hE : (diagonalFamily f).IsElliptic)
    (q : Spec (.of k) ⟶ X) :
    ∃ y : Comparison Weierstrass.family.{u} (diagonalFamily f) (Spec (.of k)), y.snd = q := by
  obtain ⟨U, hU, x, hx⟩ := Weierstrass.localWeierstrassAt_of_noetherian
    Weierstrass.localWeierstrassNoetherian _ hE (q (IsLocalRing.closedPoint k))
  have hrange : Set.range q ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    rw [Subsingleton.elim t (IsLocalRing.closedPoint k)]
    exact hU
  refine ⟨x.baseChange (IsOpenImmersion.lift U.ι q hrange), ?_⟩
  show IsOpenImmersion.lift U.ι q hrange ≫ x.snd = q
  rw [hx, IsOpenImmersion.lift_fac]

variable {f} in
/-- The isomorphism of pointed families over `Spec k` from the restriction of the Weierstrass
family along the first morphism of a triple `y` with `y.snd = q` to `(X, q)`. -/
def weierstrassFamilyIso {q : Spec (.of k) ⟶ X} (hq : q ≫ f = 𝟙 _)
    (y : Comparison Weierstrass.family.{u} (diagonalFamily f) (Spec (.of k))) (hy : y.snd = q) :
    FamilyIso (Weierstrass.family.pullback y.fst) (pointedFamily f q hq) :=
  (y.familyIsoOfSnd hy).trans (diagonalFamilyPointIso f q hq)

/-! ### Finiteness -/

section Finite

variable [IsProper f] [SmoothOfRelativeDimension 1 f]
  (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) (hg : genus f = 1)
  (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
  {P : Scheme.{u}} (r : RepresentsComparisons (pointedFamily f p hp) (diagonalFamily f) P)
include h0 hg

/-- The projection `Spec k ×_{𝓜₁,₁} X ⟶ Spec k × X` is finite. -/
theorem isFinite_comparisonProjection : IsFinite (comparisonProjection f p hp r) := by
  have hE := isElliptic_diagonalFamily f h0 hg p hp
  obtain ⟨y, hy⟩ := exists_weierstrassComparison f hE p
  exact r.isFinite_prodLift (Comparison.ofFamilyIso y.fst (𝟙 _)
    ((weierstrassFamilyIso hp y hy).trans (pointedFamily f p hp).pullbackIdIso.symm)) rfl hE

/-- **The morphism `G ⟶ X, ψ ↦ ψ(p)` from the automorphism scheme is finite.** -/
theorem isFinite_autScheme_toCurve :
    IsFinite (pullback.snd (comparisonProjection f p hp r) (graphOf f)) := by
  have := isFinite_comparisonProjection f h0 hg p hp r
  infer_instance

end Finite

/-! ### Transitivity -/

section Transitive

variable [IsProper f] [SmoothOfRelativeDimension 1 f]
  (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) (hg : genus f = 1)
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] [IsAlgClosed k]
include h0 hg

/-- **Any two pointed curves `(X, p)` and `(X, q)` are isomorphic** over an algebraically closed
field: there is a triple comparing `(X, p)` over `Spec k` with the diagonal family whose
morphism to `X` is `q`. -/
theorem exists_comparison_of_isAlgClosed (p q : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (hq : q ≫ f = 𝟙 _) :
    ∃ w : Comparison (pointedFamily f p hp) (diagonalFamily f) (Spec (.of k)),
      w.fst = 𝟙 _ ∧ w.snd = q := by
  have hE := isElliptic_diagonalFamily f h0 hg p hp
  obtain ⟨J, hJ⟩ := (diagonalFamily f).exists_jInvariant hE
  obtain ⟨yp, hyp⟩ := exists_weierstrassComparison f hE p
  obtain ⟨yq, hyq⟩ := exists_weierstrassComparison f hE q
  -- the `j`-invariant of the diagonal family is a constant
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop
  obtain ⟨c, hc⟩ : ∃ c, f.appTop c = J :=
    ⟨inv f.appTop J, by
      rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id]
      rfl⟩
  have hj : ∀ (s : Spec (.of k) ⟶ X), s ≫ f = 𝟙 _ →
      ∀ y : Comparison Weierstrass.family.{u} (diagonalFamily f) (Spec (.of k)), y.snd = s →
        (Weierstrass.curveAt y.fst).j = c := by
    intro s hs y hy
    rw [hJ, hy, ← hc]
    show (s ≫ f).appTop c = c
    rw [hs]
    rfl
  -- so the two Weierstrass equations differ by a coordinate change
  obtain ⟨γ, hγ⟩ := WeierstrassCurve.exists_variableChange_of_j_eq_of_ringEquiv
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv _ _
    ((hj p hp yp hyp).trans (hj q hq yq hyq).symm)
  let g := Weierstrass.productLift (Weierstrass.toGroup γ) yq.fst
  have hg₁ : g ≫ Weierstrass.actionMap.{u} = yp.fst := by
    refine Weierstrass.eq_of_curveAt_eq ?_
    rw [Weierstrass.productLift_actionMap, Weierstrass.curveAt_act, Weierstrass.changeAt_toGroup,
      hγ]
  have hg₂ : g ≫ Weierstrass.productToBase.{u} = yq.fst := Weierstrass.productLift_snd _ _
  let z := Weierstrass.representsComparisons_coordinateChange.{u}.homEquiv _ g
  have hz₁ : z.fst = yp.fst := by
    rw [RepresentsComparisons.fst_homEquiv,
      Weierstrass.representsComparisons_coordinateChange_homEquiv_id_fst, hg₁]
  have hz₂ : z.snd = yq.fst := by
    rw [RepresentsComparisons.snd_homEquiv,
      Weierstrass.representsComparisons_coordinateChange_homEquiv_id_snd, hg₂]
  refine ⟨Comparison.ofFamilyIso (𝟙 _) q ((((((pointedFamily f p hp).pullbackIdIso.trans
    (weierstrassFamilyIso hp yp hyp).symm).trans
    (Weierstrass.family.pullbackFamilyIsoOfEq hz₁.symm)).trans z.familyIso).trans
    (Weierstrass.family.pullbackFamilyIsoOfEq hz₂)).trans (yq.familyIsoOfSnd hyq)), rfl, rfl⟩

variable (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
  {P : Scheme.{u}} (r : RepresentsComparisons (pointedFamily f p hp) (diagonalFamily f) P)

/-- **The morphism `G ⟶ X, ψ ↦ ψ(p)` from the automorphism scheme is surjective** over an
algebraically closed field. -/
theorem surjective_autScheme_toCurve :
    Surjective (pullback.snd (comparisonProjection f p hp r) (graphOf f)) := by
  have := isFinite_autScheme_toCurve f h0 hg p hp r
  set π := pullback.snd (comparisonProjection f p hp r) (graphOf f)
  have hpts : closedPoints X ⊆ Set.range π := by
    intro x hx
    let q := pointOfClosedPoint f x hx
    have hq : q ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hx
    obtain ⟨w, hw₁, hw₂⟩ := exists_comparison_of_isAlgClosed f h0 hg p q hp hq
    let u := (r.homEquiv _).symm w
    have hu : u ≫ comparisonProjection f p hp r = q ≫ graphOf f := by
      refine prod.hom_ext ?_ ?_
      · rw [Category.assoc, prod.lift_fst, ← r.fst_homEquiv, Equiv.apply_symm_apply, hw₁,
          Category.assoc, prod.lift_fst, hq]
      · rw [Category.assoc, prod.lift_snd, ← r.snd_homEquiv, Equiv.apply_symm_apply, hw₂,
          Category.assoc, prod.lift_snd, Category.comp_id]
    let t : Spec (.of k) := IsLocalRing.closedPoint k
    refine ⟨pullback.lift u q hu t, ?_⟩
    rw [← pointOfClosedPoint_apply f x hx t]
    show (pullback.lift u q hu ≫ pullback.snd _ _) t = q t
    rw [pullback.lift_snd]
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have h := π.isClosedMap.isClosed_range.closure_subset_iff.2 hpts
  rw [closure_closedPoints] at h
  exact ⟨fun x ↦ h (Set.mem_univ x)⟩

/-- **The automorphism scheme of `X` has the dimension of `X`.** -/
theorem topologicalKrullDim_autScheme :
    topologicalKrullDim (autSchemeOver f p hp r).left = topologicalKrullDim X := by
  have := isFinite_autScheme_toCurve f h0 hg p hp r
  have := surjective_autScheme_toCurve f h0 hg p hp r
  exact topologicalKrullDim_eq_of_isIntegralHom_of_surjective
    (pullback.snd (comparisonProjection f p hp r) (graphOf f))

end Transitive

/-! ### Smooth curves of genus one over an algebraically closed field -/

section Curve

/-- On a proper curve over an algebraically closed field the global functions are the constants. -/
theorem isIso_globalSections_of_isAlgClosed [IsAlgClosed k] [IsProper f] [IsCurve k f] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  have : IsProperVariety k f := (isProperVariety_iff k f).2 ⟨inferInstance, inferInstance⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Stacks.AlgebraicGeometry.UnitsNormalProper.bijective_structMap k f

variable [IsAlgClosed k] [IsProper f] [Smooth f] [IsCurve k f]

omit [Smooth f] in
/-- On a proper curve over an algebraically closed field `dim_k H⁰(X, 𝒪_X) = 1`. -/
theorem finrank_structureSheafCohomology_zero_of_isAlgClosed :
    Module.finrank k (structureSheafCohomology f 0) = 1 := by
  have := isIso_globalSections_of_isAlgClosed f
  rw [(structureSheafCohomologyIsoCohomologyOverField k f 0).toLinearEquiv.finrank_eq]
  exact finrank_cohomologyOverField_unit_zero_eq_one f

omit [IsProper f] in
/-- A curve over an algebraically closed field has a rational point. -/
theorem exists_section_of_isAlgClosed : ∃ p : Spec (.of k) ⟶ X, p ≫ f = 𝟙 _ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy⟩ : (closedPoints X).Nonempty := Set.nonempty_iff_ne_empty.2 fun h ↦
    Set.empty_ne_univ (by rw [← closure_empty (X := X), ← h, closure_closedPoints])
  exact ⟨pointOfClosedPoint f y hy, pointOfClosedPoint_comp f y hy⟩

/-- **Stacks Project, Tag 0DSV**, genus one. **The automorphism group scheme of a smooth proper
curve of genus one over an algebraically closed field has dimension one.** The automorphism
functor `T ↦ Aut_T(X ×_k T)` of `X` over `k` is representable by a scheme over `k`, and every
scheme representing it has dimension one. -/
@[stacks 0DSV "genus one: the automorphism group scheme of a smooth proper genus one curve over \
an algebraically closed field exists and has dimension one"]
theorem autScheme_topologicalKrullDim_eq_one_of_genus_eq_one
    (hg : genus f = 1) :
    (∃ G : Over (Spec (.of k)), Nonempty ((Scheme.autFunctor (Over.mk f)).RepresentableBy G)) ∧
      ∀ (G : Over (Spec (.of k))), (Scheme.autFunctor (Over.mk f)).RepresentableBy G →
        topologicalKrullDim G.left = 1 := by
  have := smoothOfRelativeDimension_one_of_isCurve k f
  have := isIso_globalSections_of_isAlgClosed f
  have h0 := finrank_structureSheafCohomology_zero_of_isAlgClosed f
  obtain ⟨p, hp⟩ := exists_section_of_isAlgClosed f
  obtain ⟨P, ⟨r⟩⟩ := exists_representsComparisons (pointedFamily f p hp) (diagonalFamily f)
    (isElliptic_pointedFamily f h0 hg p hp) (isElliptic_diagonalFamily f h0 hg p hp)
  refine ⟨⟨_, ⟨autFunctorRepresentableBy f p hp r⟩⟩, fun G R ↦ ?_⟩
  rw [Scheme.topologicalKrullDim_left_eq_of_representableBy R
    (autFunctorRepresentableBy f p hp r), topologicalKrullDim_autScheme f h0 hg p hp r,
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)]

end Curve

end AlgebraicGeometry.GenusOne
