module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomPairingDerived
public import StacksFrontier.Algebra.Homology.HomComplexCocycleInjectiveTarget
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# The top-degree map of a pairing into the trace target

Let `P : Aⁿ × E^p → T^{p+n}` be a pairing of complexes of discrete `Q`-modules
(`Stacks.ContinuousCohomology.ComplexPairing`) into the trace target `T`, the injective
resolution of `ℚ/ℤ[-d]` (`Stacks.ContinuousCohomology.traceTarget`). It induces
`Φ_P : A ⟶ Hom^•_ℤ(E, T)` (`Stacks.ContinuousCohomology.internalHomComplexOfPairing`). This file
reduces the bijectivity of `H^d(Φ_P)` to the perfectness of the pairing it induces on cohomology:
`H^d(A) × H^0(E) → H^d(T) = H^0(T[d])`, `([a], [β]) ↦ [P(a, β)]`.

* A degree-`n` cohomology class `[z]` of Mathlib's Hom complex `Hom^•(K, L)` is a morphism of
  complexes `z̃ : K ⟶ L[n]` up to homotopy, so it has a well-defined effect on `H^0`
  (`CochainComplex.HomComplex.CohomologyClass.homologyEval`). When `L` is a K-injective resolution
  of an injective object placed in degree `n`, this evaluation is injective
  (`CochainComplex.HomComplex.CohomologyClass.homologyEval_injective`).
* On underlying abelian groups `Φ_P` is a morphism into Mathlib's Hom complex
  (`Stacks.ContinuousCohomology.ComplexPairing.homComplexMap`). Following its effect on `H^d` by
  evaluation gives `ψ_P : H^d(A) → Hom(H^0(E), H^0(T[d]))`
  (`Stacks.ContinuousCohomology.ComplexPairing.topDegreePairing`), computed on cocycles by
  `Stacks.ContinuousCohomology.ComplexPairing.topDegreePairing_homologyπ`.
* If `ψ_P` is bijective then `H^d(Φ_P)` is an isomorphism
  (`Stacks.ContinuousCohomology.isIso_homologyMap_internalHomComplexOfPairing_of_bijective`).

This is the base case of the derived Poincaré duality of Tag 03VM: there `d = 2`, the pairing is
evaluation followed by the trace, and `ψ_P` is the degree-zero duality
`H²_c(X_k̄, ℱ_M) ≅ Hom_N(M, μ_n)^∨`.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v w

namespace CochainComplex.HomComplex.CohomologyClass

section Eval

variable {C : Type*} [Category* C] [Preadditive C] [CategoryWithHomology C]
  {K L : CochainComplex C ℤ}

/-- **The effect on `H^0` of a cohomology class of the Hom complex**: `[z] ↦ H^0(z̃)`, where
`z̃ : K ⟶ L[n]` is the morphism of complexes of the cocycle `z`. Well defined since coboundaries
give null-homotopic morphisms. -/
def homologyEval (n : ℤ) : CohomologyClass K L n →+ (K.homology 0 ⟶ (L⟦n⟧).homology 0) :=
  descAddMonoidHom
    { toFun z := HomologicalComplex.homologyMap (Cocycle.equivHomShift.symm z) 0
      map_zero' := by simp
      map_add' z z' := by rw [map_add, HomologicalComplex.homologyMap_add] }
    (fun z hz => by
      rw [← toHom_mk_eq_zero_iff, toHom_mk, HomotopyCategory.quotient_map_eq_zero_iff] at hz
      obtain ⟨h⟩ := hz
      exact (h.homologyMap_eq 0).trans (by simp))

/-- The evaluation on `H^0` of the class of a cocycle `z` is `H^0(z̃)`, where `z̃ : K ⟶ L[n]` is
the morphism of complexes of `z`. -/
lemma homologyEval_mk (n : ℤ) (z : Cocycle K L n) :
    homologyEval n (mk z) = HomologicalComplex.homologyMap (Cocycle.equivHomShift.symm z) 0 :=
  rfl

end Eval

/-- **The evaluation on `H^0` is injective** when `L` is a K-injective resolution of an injective
object `W` placed in degree `d`. -/
theorem homologyEval_injective {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} (W : C) [Injective W] (d : ℤ)
    (ι : (CochainComplex.singleFunctor C d).obj W ⟶ L) [QuasiIso ι] [(L⟦d⟧).IsKInjective] :
    Function.Injective (homologyEval (K := K) (L := L) d) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := x.mk_surjective
  exact (mk_eq_zero_iff z).2 (mem_coboundaries_of_homologyMap_eq_zero W d ι z hx)

section Homology

variable {C : Type*} [Category* C] [Preadditive C] (K L : CochainComplex C ℤ) (n : ℤ)

/-- The cocycle underlying a cycle of the Hom complex is its image in the cochains. -/
lemma coe_leftHomologyData_cyclesIso_hom (w : (HomComplex K L).cycles n) :
    Cocycle.toCochainAddMonoidHom K L n ((leftHomologyData K L n).cyclesIso.hom w) =
      (HomComplex K L).iCycles n w :=
  ConcreteCategory.congr_hom (leftHomologyData K L n).cyclesIso_hom_comp_i w

/-- The identification of the homology of the Hom complex with cohomology classes sends the class
of a cycle to the class of the corresponding cocycle. -/
lemma homologyAddEquiv_homologyπ (w : (HomComplex K L).cycles n) :
    homologyAddEquiv K L n ((HomComplex K L).homologyπ n w) =
      mk ((leftHomologyData K L n).cyclesIso.hom w : Cocycle K L n) :=
  ConcreteCategory.congr_hom (leftHomologyData K L n).homologyπ_comp_homologyIso_hom w

end Homology

end CochainComplex.HomComplex.CohomologyClass

namespace Stacks.ContinuousCohomology

open CochainComplex.HomComplex InternalHomCochain Stacks.GroupHomology

section HomComplexMap

variable {R : Type} [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] {S : Type} [Ring S] {φ : S →+* Rᵐᵒᵖ}
  {A : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} S Q) ℤ}
  {E : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} R Q) ℤ}
  {G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ}

/-- **The pairing as a morphism of complexes of abelian groups** from the underlying complex of
`A` to Mathlib's Hom complex of the underlying complexes of `E` and `G`: the underlying morphism
of `Stacks.ContinuousCohomology.internalHomComplexOfPairing`. -/
def ComplexPairing.homComplexMap (P : ComplexPairing R φ A E G) :
    underlyingAb S A ⟶ CochainComplex.HomComplex (underlyingAb R E) (underlyingAb ℤ G) where
  f n := AddCommGrpCat.ofHom
    { toFun a := Cochain.mk fun p q hpq => AddCommGrpCat.ofHom (P.pair n p q hpq a)
      map_zero' := Cochain.ext _ _ fun p q hpq => AddCommGrpCat.hom_ext <|
        AddMonoidHom.ext fun e => by
          change P.pair n p q hpq 0 e = 0
          rw [map_zero]
          rfl
      map_add' a b := Cochain.ext _ _ fun p q hpq => AddCommGrpCat.hom_ext <|
        AddMonoidHom.ext fun e => by
          change P.pair n p q hpq (a + b) e = P.pair n p q hpq a e + P.pair n p q hpq b e
          exact congrArg (fun f => f e) ((P.pair n p q hpq).map_add a b) }
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    refine AddCommGrpCat.ext fun a => ?_
    refine Cochain.ext _ _ fun p q' hpq' => ?_
    change (δ n (n + 1) (Cochain.mk fun p q hpq => AddCommGrpCat.ofHom (P.pair n p q hpq a) :
        Cochain (underlyingAb R E) (underlyingAb ℤ G) n)).v p q' hpq' =
      AddCommGrpCat.ofHom (P.pair (n + 1) p q' hpq' ((A.d n (n + 1)).hom.hom.hom.hom a))
    rw [δ_v n (n + 1) rfl _ p q' hpq' (q' - 1) (p + 1) (by omega) rfl]
    refine AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun e => ?_
    exact (P.leibniz n p (q' - 1) q' (by omega) (by omega) a e).symm

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- The degree-`n` component of `Stacks.ContinuousCohomology.ComplexPairing.homComplexMap` sends
`a` to the cochain whose `(p, q)` component is `P(a, -) : E^p → G^q`. -/
lemma ComplexPairing.homComplexMap_f_apply_v (P : ComplexPairing R φ A E G) (n : ℤ)
    (a : (A.X n).obj.obj.V) (p q : ℤ) (hpq : p + n = q) :
    (((P.homComplexMap).f n).hom a : Cochain (underlyingAb R E) (underlyingAb ℤ G) n).v p q hpq =
      (AddCommGrpCat.ofHom (P.pair n p q hpq a) :
        (underlyingAb R E).X p ⟶ (underlyingAb ℤ G).X q) :=
  rfl

/-- **`H^d` of the chain map of a pairing is invertible iff it is so on underlying abelian
groups**, where the chain map is `Stacks.ContinuousCohomology.ComplexPairing.homComplexMap`. -/
theorem ComplexPairing.isIso_homologyMap_iff (P : ComplexPairing R φ A E G) (d : ℤ) :
    IsIso (HomologicalComplex.homologyMap (internalHomComplexOfPairing P) d) ↔
      IsIso (HomologicalComplex.homologyMap P.homComplexMap d) := by
  let F := forget₂ (ModuleCat.{w} (CompletedGroupAlgebra S Q)) AddCommGrpCat.{w}
  let e₁ : (F.mapHomologicalComplex _).obj
      (((discreteToCompletedGroupAlgebra.{0, v, w} S Q).mapHomologicalComplex _).obj A) ≅
        underlyingAb S A :=
    HomologicalComplex.Hom.isoOfComponents (fun n => (AddEquiv.refl _).toAddCommGrpIso)
      (fun i j _ => rfl)
  let e₂ : (F.mapHomologicalComplex _).obj
      (((ModuleCat.restrictScalars
        (CompletedGroupAlgebra.mapCoeff (G := Q) φ)).mapHomologicalComplex _).obj
          (internalHomComplex R E G)) ≅
        CochainComplex.HomComplex (underlyingAb R E) (underlyingAb ℤ G) :=
    HomologicalComplex.Hom.isoOfComponents (fun n => (AddEquiv.refl _).toAddCommGrpIso)
      (fun i j _ => rfl)
  have h : (F.mapHomologicalComplex _).map (internalHomComplexOfPairing P) =
      e₁.hom ≫ P.homComplexMap ≫ e₂.inv :=
    HomologicalComplex.hom_ext _ _ fun n => AddCommGrpCat.ext fun a => rfl
  rw [← quasiIsoAt_iff_isIso_homologyMap, ← quasiIsoAt_iff_isIso_homologyMap,
    ← HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology _ F, h,
    quasiIsoAt_iff_comp_left, quasiIsoAt_iff_comp_right]

/-- **The pairing `H^d(A) × H^0(E) → H^0(G[d])` induced by a pairing of complexes**, curried:
`H^d` of the chain map `Stacks.ContinuousCohomology.ComplexPairing.homComplexMap`, followed by the
evaluation of cohomology classes of the Hom complex on `H^0`. On cocycles it is
`([a], [β]) ↦ [P(a, β)]` (`Stacks.ContinuousCohomology.ComplexPairing.topDegreePairing_homologyπ`).
-/
def ComplexPairing.topDegreePairing (P : ComplexPairing R φ A E G) (d : ℤ) :
    (underlyingAb S A).homology d →+
      ((underlyingAb R E).homology 0 ⟶ ((underlyingAb ℤ G)⟦d⟧).homology 0) :=
  (CohomologyClass.homologyEval d).comp
    ((CochainComplex.HomComplex.homologyAddEquiv _ _ d).toAddMonoidHom.comp
      (HomologicalComplex.homologyMap P.homComplexMap d).hom)

omit [Finite R] [IsTopologicalGroup Q] [CompactSpace Q] in
/-- **The pairing on cohomology, on cocycles**: `ψ_P([x])([y]) = [P(x, y)]`, for cycles `x` of `A`
in degree `d` and `y` of `E` in degree `0`, where `P(x, y) ∈ G^d = G[d]^0`. -/
lemma ComplexPairing.topDegreePairing_homologyπ (P : ComplexPairing R φ A E G) (d : ℤ)
    (x : (underlyingAb S A).cycles d) (y : (underlyingAb R E).cycles 0)
    (z : ((underlyingAb ℤ G)⟦d⟧).cycles 0)
    (h : ((underlyingAb ℤ G)⟦d⟧).iCycles 0 z =
      ((underlyingAb ℤ G).shiftFunctorObjXIso d 0 d (zero_add d).symm).inv
        (P.pair d 0 d (zero_add d) ((underlyingAb S A).iCycles d x)
          ((underlyingAb R E).iCycles 0 y))) :
    P.topDegreePairing d ((underlyingAb S A).homologyπ d x) ((underlyingAb R E).homologyπ 0 y) =
      ((underlyingAb ℤ G)⟦d⟧).homologyπ 0 z := by
  let w := HomologicalComplex.cyclesMap P.homComplexMap d x
  have h1 : HomologicalComplex.homologyMap P.homComplexMap d ((underlyingAb S A).homologyπ d x) =
      (CochainComplex.HomComplex _ _).homologyπ d w :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality P.homComplexMap d) x
  let c : Cocycle (underlyingAb R E) (underlyingAb ℤ G) d :=
    (leftHomologyData (underlyingAb R E) (underlyingAb ℤ G) d).cyclesIso.hom w
  have hc : (c : Cochain _ _ d) = P.homComplexMap.f d ((underlyingAb S A).iCycles d x) :=
    (CohomologyClass.coe_leftHomologyData_cyclesIso_hom _ _ d w).trans
      (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i P.homComplexMap d) x)
  show CohomologyClass.homologyEval d (CochainComplex.HomComplex.homologyAddEquiv _ _ d
      (HomologicalComplex.homologyMap P.homComplexMap d ((underlyingAb S A).homologyπ d x)))
        ((underlyingAb R E).homologyπ 0 y) = _
  rw [h1, CohomologyClass.homologyAddEquiv_homologyπ]
  show (HomologicalComplex.homologyMap (Cocycle.equivHomShift.symm c) 0)
      ((underlyingAb R E).homologyπ 0 y) = _
  refine (ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (Cocycle.equivHomShift.symm c) 0) y).trans ?_
  show ((underlyingAb ℤ G)⟦d⟧).homologyπ 0
    (HomologicalComplex.cyclesMap (Cocycle.equivHomShift.symm c) 0 y) = _
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (((underlyingAb ℤ G)⟦d⟧).iCycles 0)).1 inferInstance
  refine (ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (Cocycle.equivHomShift.symm c) 0) y).trans (h ▸ ?_)
  show ((Cochain.rightShift (c : Cochain (underlyingAb R E) (underlyingAb ℤ G) d) d 0
    (zero_add d)).v 0 0 (add_zero 0))
      ((underlyingAb R E).iCycles 0 y) = _
  rw [Cochain.rightShift_v _ d 0 (zero_add d) 0 0 (add_zero 0) d (zero_add d), hc]
  rfl

end HomComplexMap

section TopDegree

variable {R : Type} [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] {S : Type} [Ring S] {φ : S →+* Rᵐᵒᵖ}
  {A : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} S Q) ℤ}
  {E : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ}

/-- The augmentation `ℚ/ℤ[-d] ⟶ T` of the trace target on underlying abelian groups. -/
def underlyingTraceTargetι (d : ℤ) :
    (CochainComplex.singleFunctor AddCommGrpCat.{max v w} d).obj
        ((forgetAb ℤ Q).obj (ratCircle.{v, w} Q)) ⟶
      underlyingAb ℤ (traceTarget.{v, w} Q d) :=
  (HomologicalComplex.singleMapHomologicalComplex (forgetAb ℤ Q) (ComplexShape.up ℤ) d).inv.app
      (ratCircle.{v, w} Q) ≫
    ((forgetAb ℤ Q).mapHomologicalComplex _).map (traceTargetι.{v, w} Q d)

/-- The augmentation `ℚ/ℤ[-d] ⟶ T` on underlying abelian groups is a quasi-isomorphism. -/
instance (d : ℤ) : QuasiIso (underlyingTraceTargetι.{v, w} (Q := Q) d) := by
  unfold underlyingTraceTargetι
  infer_instance

/-- The abelian group underlying `ℚ/ℤ` is an injective object. -/
instance injective_forgetAb_ratCircle : Injective ((forgetAb ℤ Q).obj (ratCircle.{v, w} Q)) :=
  AddCommGrpCat.injective_of_divisible (ULift.{max v w} (AddCircle (1 : ℚ)))

/-- **Base case of the derived Poincaré duality, abstractly**: for a pairing `P` into the trace
target `T` of degree `d`, if the induced pairing `H^d(A) × H^0(E) → H^0(T[d]) = ℚ/ℤ` is perfect
(its curried form is bijective), then `H^d(Φ_P)` is an isomorphism. -/
theorem isIso_homologyMap_internalHomComplexOfPairing_of_bijective (d : ℤ)
    (P : ComplexPairing R φ A E (traceTarget.{v, w} Q d))
    (h : Function.Bijective (P.topDegreePairing d)) :
    IsIso (HomologicalComplex.homologyMap (internalHomComplexOfPairing P) d) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{max v w}
  have hev := CohomologyClass.homologyEval_injective (K := underlyingAb R E)
    ((forgetAb ℤ Q).obj (ratCircle.{v, w} Q)) d (underlyingTraceTargetι.{v, w} (Q := Q) d)
  rw [P.isIso_homologyMap_iff, ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy => h.1 (by simp [ComplexPairing.topDegreePairing, hxy]), fun c => ?_⟩
  obtain ⟨x, hx⟩ := h.2
    (CohomologyClass.homologyEval d (CochainComplex.HomComplex.homologyAddEquiv _ _ d c))
  exact ⟨x, (CochainComplex.HomComplex.homologyAddEquiv _ _ d).injective (hev hx)⟩

end TopDegree

/-! ### The trace on `H^d` of the trace target -/

section Trace

attribute [local instance] HasDerivedCategory.standard

variable (Q : Type v) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]

/-- **`H^d(T) ≅ ℚ/ℤ`** for the trace target `T` of degree `d`, in the derived category: through
the augmentation `ℚ/ℤ[-d] ⟶ T`. -/
def traceTargetDerivedHomologyIso (d : ℤ) :
    (DerivedCategory.homologyFunctor _ d).obj (DerivedCategory.Q.obj (traceTarget.{v, w} Q d)) ≅
      ratCircle.{v, w} Q :=
  (DerivedCategory.homologyFunctor _ d).mapIso
      (asIso (DerivedCategory.Q.map (traceTargetι.{v, w} Q d))).symm ≪≫
    (DerivedCategory.homologyFunctor _ d).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ d).app (ratCircle.{v, w} Q)).symm ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ d).app (ratCircle.{v, w} Q)

/-- **A lift `t : P ⟶ T` of the derived trace induces the trace on `H^d`**, in the derived
category: `H^d(t)` followed by `H^d(T) ≅ ℚ/ℤ` is `tr`. -/
theorem homologyFunctor_map_traceLift
    (P : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q) ℤ) (d : ℤ)
    [(DerivedCategory.Q.obj P).IsLE d]
    (tr : (DerivedCategory.homologyFunctor _ d).obj (DerivedCategory.Q.obj P) ⟶ ratCircle.{v, w} Q)
    (t : P ⟶ traceTarget.{v, w} Q d)
    (ht : DerivedCategory.Q.map t =
      derivedTraceOfIsLE.{v, w} Q P d tr ≫ DerivedCategory.Q.map (traceTargetι.{v, w} Q d)) :
    (DerivedCategory.homologyFunctor _ d).map (DerivedCategory.Q.map t) ≫
        (traceTargetDerivedHomologyIso.{v, w} Q d).hom = tr := by
  refine Eq.trans ?_ (homologyToSingle_derivedTraceOfIsLE.{v, w} Q P d tr)
  rw [DerivedCategory.homologyToSingle_apply, ht, traceTargetDerivedHomologyIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv, Functor.map_comp,
    Category.assoc, Iso.app_inv]
  rw [← Functor.map_comp_assoc (DerivedCategory.homologyFunctor _ d)
    (DerivedCategory.Q.map (traceTargetι.{v, w} Q d)), IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- **`H^d(T) ≅ ℚ/ℤ`** for the trace target `T` of degree `d`, on cohomology of complexes. -/
def traceTargetHomologyIso (d : ℤ) : (traceTarget.{v, w} Q d).homology d ≅ ratCircle.{v, w} Q :=
  ((DerivedCategory.homologyFunctorFactors _ d).app (traceTarget.{v, w} Q d)).symm ≪≫
    traceTargetDerivedHomologyIso.{v, w} Q d

/-- **A lift `t : P ⟶ T` of the derived trace induces the trace on `H^d`**, on cohomology of
complexes: `H^d(t)` followed by `H^d(T) ≅ ℚ/ℤ` is `tr`, read through `H^d(P) ≅ H^d(Q P)`. -/
theorem homologyMap_traceLift
    (P : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q) ℤ) (d : ℤ)
    [(DerivedCategory.Q.obj P).IsLE d]
    (tr : (DerivedCategory.homologyFunctor _ d).obj (DerivedCategory.Q.obj P) ⟶ ratCircle.{v, w} Q)
    (t : P ⟶ traceTarget.{v, w} Q d)
    (ht : DerivedCategory.Q.map t =
      derivedTraceOfIsLE.{v, w} Q P d tr ≫ DerivedCategory.Q.map (traceTargetι.{v, w} Q d)) :
    HomologicalComplex.homologyMap t d ≫ (traceTargetHomologyIso.{v, w} Q d).hom =
      (DerivedCategory.homologyFunctorFactors _ d).inv.app P ≫ tr := by
  rw [← homologyFunctor_map_traceLift.{v, w} Q P d tr t ht]
  have hn := DerivedCategory.homologyFunctorFactors_hom_naturality t d
  have h1 := (Iso.inv_comp_eq ((DerivedCategory.homologyFunctorFactors _ d).app P)).2 hn
  refine (congrArg (· ≫ (traceTargetHomologyIso.{v, w} Q d).hom) h1.symm).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ?_)))
  exact Iso.hom_inv_id_app_assoc _ _ _

end Trace

end Stacks.ContinuousCohomology

end
