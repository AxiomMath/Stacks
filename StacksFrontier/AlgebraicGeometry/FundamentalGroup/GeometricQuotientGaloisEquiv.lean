module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafPullback
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.FieldFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFundamentalExactSequence

/-!
# `π₁(X, η̄) ⧸ π₁(X_k̄, η̄) ≅ Aut(k̄/k)`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraically closed
algebraic extension of `k` and `η̄` a geometric point of `X_k̄`. The image `N` of
`π₁(X_k̄, η̄) ⟶ π₁(X, η̄)` is the kernel of the surjection `π₁(X, η̄) ⟶ π₁(Spec k, η̄)`
(Tag 0BTX), so it is normal and `π₁(X, η̄) ⧸ N ≅ π₁(Spec k, η̄)`. This file identifies the
latter with `Aut(k̄/k)`:

* the geometric point `η̄ ⟶ X ⟶ Spec k` factors as `Spec Ω ⟶ Spec k̄ ⟶ Spec k`, where `Ω` is the
  residue field of `η̄`; precomposition with `Spec Ω ⟶ Spec k̄` is a morphism of fibre functors
  `F_{k̄} ⟶ F_{η̄}` on finite étale `k`-schemes, hence an isomorphism (any morphism of fibre
  functors of a Galois category is one), and conjugating by it is
  `π₁(Spec k, k̄) ≅ π₁(Spec k, η̄)`;
* `π₁(Spec k, k̄) ≅ Gal(k^{sep}/k)` for the separable closure `k^{sep}` of `k` in `k̄`
  (Tag 0BNE, `AlgebraicGeometry.galoisEquivEtaleFundamentalGroup`);
* `Aut(k̄/k) ≅ Gal(k^{sep}/k)` by restriction, which is injective because `k̄` is purely
  inseparable over `k^{sep}`.

## Main definitions

* `AlgebraicGeometry.finiteEtaleFiberPrecompIso` — the isomorphism of geometric fibre functors
  of a connected scheme given by precomposition with a morphism of geometric points.
* `AlgebraicGeometry.separableClosureRestrictMulEquiv` — `Aut(k̄/k) ≃* Gal(k^{sep}/k)`, by
  restriction.
* `AlgebraicGeometry.geometricQuotientGaloisEquiv` — `π₁(X, η̄) ⧸ π₁(X_k̄, η̄) ≃* Aut(k̄/k)`.

## Main results

* `AlgebraicGeometry.normal_range_etaleFundamentalGroupMap_fieldBaseChangeObjProj` — the image
  of `π₁(X_k̄, η̄)` is normal (an instance).
* `AlgebraicGeometry.geometricQuotientGaloisEquiv_spec` — the defining property: the image in
  `π₁(Spec k, η̄)` of `γ` acts on the point `Spec Ω ⟶ Spec k̄ ⟶ Y` of a finite étale `k`-scheme
  `Y` by `e ↦ e ∘ Spec σ`, where `σ` is the image of `γ` in `Aut(k̄/k)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Change of geometric point along a morphism of geometric points -/

section Precomp

variable {S : Scheme.{u}} {x x' : GeometricPoint S} (h : x'.source ⟶ x.source)
  (hh : h ≫ x.hom = x'.hom)

/-- Precomposition with a morphism of geometric points `h : x' ⟶ x` over `S` maps the fibre of a
finite étale cover at `x` to its fibre at `x'`, naturally in the cover. -/
def finiteEtaleFiberPrecomp : finiteEtaleFiberFunctor x ⟶ finiteEtaleFiberFunctor x' where
  app Y := ↾ fun p ↦ ⟨h ≫ p.1, by rw [Category.assoc, p.2, hh]⟩
  naturality Y Z g := by
    ext p
    exact Subtype.ext (Category.assoc _ _ _).symm

/-- The image of a point `p` of the fibre at `x` under `finiteEtaleFiberPrecomp h hh` is
`h ≫ p`. -/
@[simp]
theorem finiteEtaleFiberPrecomp_app_apply (Y : FiniteEtaleOver S)
    (p : finiteEtaleFiber x Y) :
    ((finiteEtaleFiberPrecomp h hh).app Y p).1 = h ≫ p.1 :=
  rfl

/-- **Precomposition with a morphism of geometric points is an isomorphism of fibre functors**
on the finite étale covers of a connected scheme. -/
instance isIso_finiteEtaleFiberPrecomp [ConnectedSpace S] :
    IsIso (finiteEtaleFiberPrecomp h hh) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso_of_connectedSpace S x' x
  let L := (Functor.whiskeringRight (FiniteEtaleOver S) FintypeCat.{u} (Type u)).obj
    FintypeCat.incl
  let e : finiteEtaleFiberFintypeFunctor S x ⟶ finiteEtaleFiberFintypeFunctor S x :=
    (fullyFaithfulWhiskeringRightFintypeIncl S).preimage (finiteEtaleFiberPrecomp h hh ≫ t.hom)
  have : IsIso e := FibreFunctor.end_isIso _ (End.of e)
  have he : IsIso (L.map e) := inferInstance
  have he' : L.map e = finiteEtaleFiberPrecomp h hh ≫ t.hom :=
    (fullyFaithfulWhiskeringRightFintypeIncl S).map_preimage _
  rw [he'] at he
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ t.hom inferInstance he

/-- The isomorphism of geometric fibre functors of a connected scheme given by precomposition
with a morphism of geometric points. -/
def finiteEtaleFiberPrecompIso [ConnectedSpace S] :
    finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor x' :=
  asIso (finiteEtaleFiberPrecomp h hh)

/-- The image of a point `p` of the fibre at `x` under `finiteEtaleFiberPrecompIso h hh` is
`h ≫ p`. -/
@[simp]
theorem finiteEtaleFiberPrecompIso_hom_app_apply [ConnectedSpace S] (Y : FiniteEtaleOver S)
    (p : finiteEtaleFiber x Y) :
    ((finiteEtaleFiberPrecompIso h hh).hom.app Y p).1 = h ≫ p.1 :=
  rfl

end Precomp

/-! ### Restriction to the separable closure -/

section Restriction

variable (k kbar : Type u) [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosed kbar]
  [Algebra.IsAlgebraic k kbar]

/-- **`Aut(k̄/k) ≃* Gal(k^{sep}/k)`, by restriction**, for an algebraically closed algebraic
extension `k̄` of `k` with separable closure `k^{sep}` of `k` in `k̄`. -/
def separableClosureRestrictMulEquiv :
    (kbar ≃ₐ[k] kbar) ≃* Gal(separableClosure k kbar/k) :=
  haveI : IsAlgClosure k kbar := ⟨inferInstance, inferInstance⟩
  MulEquiv.ofBijective (AlgEquiv.restrictNormalHom (separableClosure k kbar))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro σ hσ
      have hfix : ∀ x ∈ separableClosure k kbar, σ x = x :=
        (AlgEquiv.restrictNormal_eq_one_iff (separableClosure k kbar) σ).mp hσ
      let : IsPurelyInseparable (separableClosure k kbar) kbar :=
        separableClosure.isPurelyInseparable k kbar
      have hcomp : σ.toRingHom.comp (algebraMap (separableClosure k kbar) kbar) =
          (RingHom.id kbar).comp (algebraMap (separableClosure k kbar) kbar) := by
        ext x
        exact hfix x x.2
      have hst : σ.toRingHom = RingHom.id kbar :=
        IsPurelyInseparable.injective_comp_algebraMap (separableClosure k kbar) kbar kbar hcomp
      ext x
      exact congrArg (fun g : kbar →+* kbar ↦ g x) hst,
    AlgEquiv.restrictNormalHom_surjective (E := kbar)⟩

/-- The restriction of `σ ∈ Aut(k̄/k)` to `k^{sep}` agrees with `σ` on every element of
`k^{sep}`. -/
@[simp]
theorem separableClosureRestrictMulEquiv_apply_coe (σ : kbar ≃ₐ[k] kbar)
    (x : separableClosure k kbar) :
    ((separableClosureRestrictMulEquiv k kbar σ x : separableClosure k kbar) : kbar) = σ x :=
  have : IsAlgClosure k kbar := ⟨inferInstance, inferInstance⟩
  AlgEquiv.restrictNormalHom_apply _ σ x

end Restriction

/-! ### The quotient of `π₁(X)` by the geometric fundamental group -/

section GeometricQuotient

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar))

omit [IsCurve k f] [Smooth f] [GeometricallyConnected f] [IsAlgClosed kbar]
  [Algebra.IsAlgebraic k kbar] in
/-- The morphism `Spec Ω ⟶ Spec k̄` underlying a geometric point `η̄` of `X_k̄`: the composite of
`η̄` with the structure morphism `X_k̄ ⟶ Spec k̄`. -/
abbrev geometricPointToSpec : y.source ⟶ Spec (.of kbar) :=
  y.hom ≫ pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)

omit [Smooth f] [GeometricallyConnected f] [IsAlgClosed kbar] in
/-- The image of `η̄` in `Spec k` is `Spec Ω ⟶ Spec k̄ ⟶ Spec k`. -/
theorem geometricPointToSpec_comp_specAlgebraMap :
    geometricPointToSpec B X f kbar y ≫ specAlgebraMap k kbar =
      ((y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom).map f).hom := by
  change (y.hom ≫ pullback.snd _ _) ≫ _ = (y.hom ≫ pullback.fst _ _) ≫ f
  rw [Category.assoc, Category.assoc, ← pullback.condition]
  rfl

/-- **The image of the geometric fundamental group is normal.** For a geometrically connected
smooth curve `X` over `k` and a geometric point `η̄` of `X_k̄`, the image of
`π₁(X_k̄, η̄) ⟶ π₁(X, η̄)` is a normal subgroup. -/
instance normal_range_etaleFundamentalGroupMap_fieldBaseChangeObjProj [ConnectedSpace X.1]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] :
    ((etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range).Normal :=
  haveI : CompactSpace X.1 := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X.1 := quasiSeparatedSpace_of_quasiSeparated f
  normal_range_etaleFundamentalGroupMap_of_isPullback_isAlgClosed k kbar f
    (pullback.fst (Over.mk f).hom (specAlgebraMap k kbar))
    (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
    (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) y

/-- **`π₁(X, η̄) ⧸ π₁(X_k̄, η̄) ≃* Aut(k̄/k)`.** For a geometrically connected smooth curve `X`
over `k`, an algebraically closed algebraic extension `k̄` of `k` and a geometric point `η̄` of
`X_k̄`: the quotient of `π₁(X, η̄)` by the image of `π₁(X_k̄, η̄)` is `π₁(Spec k, η̄)` (Tag 0BTX),
which is `π₁(Spec k, k̄)` by precomposition with `Spec Ω ⟶ Spec k̄`, which is
`Gal(k^{sep}/k)` (Tag 0BNE), which is `Aut(k̄/k)` by restriction. The defining property is
`AlgebraicGeometry.geometricQuotientGaloisEquiv_spec`. -/
def geometricQuotientGaloisEquiv :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) ⧸
      (etaleFundamentalGroupMap (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom y).toMonoidHom.range ≃*
      (kbar ≃ₐ[k] kbar) :=
  letI := connectedSpace_of_isCurve B X f
  letI := connectedSpace_fieldBaseChange f kbar
  haveI : CompactSpace X.1 := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X.1 := quasiSeparatedSpace_of_quasiSeparated f
  haveI : ConnectedSpace ↥(pullback f (specAlgebraMap k kbar)) :=
    connectedSpace_fieldBaseChange f kbar
  (QuotientGroup.quotientMulEquivOfEq
    (range_etaleFundamentalGroupMap_eq_ker_of_isPullback_isAlgClosed k kbar f
      (fieldBaseChangeObjProj B X f kbar (contains_fieldBaseChange_of_isCurve B X f kbar)).hom
      (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) y)).trans <|
  (QuotientGroup.quotientKerEquivOfSurjective _
    (surjective_etaleFundamentalGroupMap_isAlgClosed k kbar f
      (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))).trans <|
  (etaleFundamentalGroupMulEquiv (finiteEtaleFiberPrecompIso (geometricPointToSpec B X f kbar y)
    (x := algebraicClosureGeometricPoint k kbar)
    (geometricPointToSpec_comp_specAlgebraMap B X f kbar y))).symm.trans <|
  (galoisEquivEtaleFundamentalGroup k (separableClosure k kbar) kbar).toMulEquiv.symm.trans
    (separableClosureRestrictMulEquiv k kbar).symm

omit [Smooth f] in
/-- **The defining property of `AlgebraicGeometry.geometricQuotientGaloisEquiv`**, in terms of
the fibre functor of `Spec k` at `η̄`. Let `γ ∈ π₁(X, η̄)` with image `σ ∈ Aut(k̄/k)`, let `Y` be
a finite étale `k`-scheme and `e : Spec k̄ ⟶ Y` a `k̄`-point of `Y` over `k`. Then the image of `γ`
in `π₁(Spec k, η̄)` maps the point `Spec Ω ⟶ Spec k̄ ⟶ Y` of the fibre of `Y` at `η̄` to
`Spec Ω ⟶ Spec k̄ ⟶ Spec k̄ ⟶ Y`, the middle arrow being `Spec σ`; on `k̄`-points of `Y` this is
`e ↦ e ∘ Spec σ`. The point is given as any `p` equal to that composite. -/
theorem geometricQuotientGaloisEquiv_spec
    (γ : letI := connectedSpace_of_isCurve B X f
      EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))
    (Y : FiniteEtaleOver (Spec (.of k))) (e : Spec (.of kbar) ⟶ Y.left)
    (he : e ≫ Y.hom = specAlgebraMap k kbar)
    (p : finiteEtaleFiber ((y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom).map f) Y)
    (hp : p.1 = geometricPointToSpec B X f kbar y ≫ e) :
    letI := connectedSpace_of_isCurve B X f
    letI := connectedSpace_fieldBaseChange f kbar
    ((((etaleFundamentalGroupMap f (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)) γ).asIso.app Y).hom p).1 =
      geometricPointToSpec B X f kbar y ≫
        Spec.map (CommRingCat.ofHom
          (geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ)).toAlgHom.toRingHom) ≫
        e := by
  let := connectedSpace_of_isCurve B X f
  let := connectedSpace_fieldBaseChange f kbar
  let L := separableClosure k kbar
  let t := finiteEtaleFiberPrecompIso (geometricPointToSpec B X f kbar y)
    (x := algebraicClosureGeometricPoint k kbar)
    (x' := (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom).map f)
    (geometricPointToSpec_comp_specAlgebraMap B X f kbar y)
  let G := galoisEquivEtaleFundamentalGroup k L kbar
  let r := separableClosureRestrictMulEquiv k kbar
  let Q := etaleFundamentalGroupMap f (y.map (fieldBaseChangeObjProj B X f kbar
    (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) γ
  let τ : Gal(L/k) := G.symm ((etaleFundamentalGroupMulEquiv t).symm Q)
  have hσ : geometricQuotientGaloisEquiv B X f kbar y (QuotientGroup.mk γ) = r.symm τ := rfl
  have hQ : Q = etaleFundamentalGroupMulEquiv t (G τ) := by
    simp only [τ, ContinuousMulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  let p₀ : finiteEtaleFiber (algebraicClosureGeometricPoint k kbar) Y := ⟨e, he⟩
  have hp₀ : p = t.hom.app Y p₀ := Subtype.ext hp
  let y₀ := (finiteEtaleFiberIso k L kbar).inv.app Y p₀
  let g := (separableFiberEquiv k L kbar Y y₀).1
  have hy₀ : (finiteEtaleFiberIso k L kbar).hom.app Y y₀ = p₀ :=
    congrArg (fun η => η p₀) (congrArg (fun η => NatTrans.app η Y)
      (finiteEtaleFiberIso k L kbar).inv_hom_id)
  have hg : p₀.1 = Spec.map (CommRingCat.ofHom (algebraMap L kbar)) ≫ g := by
    rw [← finiteEtaleFiberIso_apply k L kbar Y y₀, hy₀]
  have hact := galoisEquivEtaleFundamentalGroup_apply k L kbar Y τ p₀ g hg
  have hsq : Spec.map (CommRingCat.ofHom (algebraMap L kbar)) ≫
      Spec.map (CommRingCat.ofHom τ.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom (r.symm τ).toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L kbar)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    have hx := separableClosureRestrictMulEquiv_apply_coe k kbar (r.symm τ) x
    rwa [MulEquiv.apply_symm_apply] at hx
  rw [hσ]
  refine (congrArg (fun q : Aut (finiteEtaleFiberFunctor _) ↦ ((q.asIso.app Y).hom p).1)
    hQ).trans ?_
  dsimp only
  rw [hp₀]
  refine (congrArg Subtype.val
    (Stacks.FundamentalGroup.conjAut_app_apply t (G τ) Y p₀)).trans ?_
  refine (finiteEtaleFiberPrecompIso_hom_app_apply _ _ Y _).trans ?_
  rw [hact, ← Category.assoc
    (Spec.map (CommRingCat.ofHom (algebraMap L kbar))), hsq, Category.assoc, ← hg]
  rfl

end GeometricQuotient

end AlgebraicGeometry

end
