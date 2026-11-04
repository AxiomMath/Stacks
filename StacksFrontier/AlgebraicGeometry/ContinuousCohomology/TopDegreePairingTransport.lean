module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomPairingTopDegree

/-!
# Transporting the top-degree pairing

Two tools for the base case of the derived Poincaré duality of [Stacks, Tag 03VM]:

* a pairing `ψ : X → Hom(Y, Z)` which, read through isomorphisms `X ≃ X'`, `Y ≃ Y'`, `Z ≃ Z'`, is a
  bijective pairing `ψ' : X' → Hom(Y', Z')` is itself bijective
  (`Stacks.ContinuousCohomology.bijective_of_pairing_transport`);
* the class of a degree-`0` cycle `z` of `K⟦n⟧` corresponds, under `H⁰(K⟦n⟧) ≅ Hⁿ(K)`, to the class
  of the degree-`n` cycle of `K` with the same underlying element
  (`CochainComplex.ShiftSequence.shiftIso_hom_app_homologyπ`).
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v w

namespace Stacks.ContinuousCohomology

/-- **A pairing conjugate to a bijective pairing is bijective**: if `e₃ (ψ x y) = ψ' (e₁ x) (e₂ y)`
for bijections `e₁` and additive isomorphisms `e₂`, `e₃`, and `ψ'` is bijective, so is `ψ`. -/
theorem bijective_of_pairing_transport {X X' Y' Z' : Type*} [AddCommGroup Y'] [AddCommGroup Z']
    {Y Z : AddCommGrpCat.{w}} (ψ : X → (Y ⟶ Z)) (ψ' : X' → (Y' →+ Z')) (e₁ : X ≃ X')
    (e₂ : Y ≃+ Y') (e₃ : Z ≃+ Z') (h : ∀ x y, e₃ ((ψ x).hom y) = ψ' (e₁ x) (e₂ y))
    (hψ' : Function.Bijective ψ') : Function.Bijective ψ := by
  let Φ : (Y' →+ Z') → (Y ⟶ Z) := fun g =>
    AddCommGrpCat.ofHom (e₃.symm.toAddMonoidHom.comp (g.comp e₂.toAddMonoidHom))
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun g g' hg => AddMonoidHom.ext fun y' => ?_, fun c =>
      ⟨e₃.toAddMonoidHom.comp (c.hom.comp e₂.symm.toAddMonoidHom), ?_⟩⟩
    · simpa [Φ] using congrArg (fun c : Y ⟶ Z => e₃ (c.hom (e₂.symm y'))) hg
    · ext y
      simp [Φ]
  have hψ : ψ = Φ ∘ ψ' ∘ e₁ := by
    funext x
    ext y
    show (ψ x).hom y = e₃.symm (ψ' (e₁ x) (e₂ y))
    rw [← h, AddEquiv.symm_apply_apply]
  rw [hψ]
  exact hΦ.comp (hψ'.comp e₁.bijective)

end Stacks.ContinuousCohomology

namespace CochainComplex.ShiftSequence

/-- **`H⁰(K⟦n⟧) ≅ Hⁿ(K)` on classes**: the class of a degree-`0` cycle `z` of `K⟦n⟧` goes to the
class of the degree-`n` cycle `c` of `K` with the same underlying element. -/
lemma shiftIso_hom_app_homologyπ (K : CochainComplex AddCommGrpCat.{w} ℤ) (n : ℤ)
    (z : (K⟦n⟧).cycles 0) (c : K.cycles n)
    (h : (K⟦n⟧).iCycles 0 z = (K.shiftFunctorObjXIso n 0 n (zero_add n).symm).inv (K.iCycles n c)) :
    ((shiftIso AddCommGrpCat.{w} n 0 n (add_zero n)).hom.app K) ((K⟦n⟧).homologyπ 0 z) =
      K.homologyπ n c := by
  rw [shiftIso_hom_app]
  refine (ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality
    ((shiftShortComplexFunctorIso AddCommGrpCat.{w} n 0 n (add_zero n)).hom.app K)) z).trans ?_
  show ((K.sc n).homologyπ) (ShortComplex.cyclesMap
    ((shiftShortComplexFunctorIso AddCommGrpCat.{w} n 0 n (add_zero n)).hom.app K) z) =
      (K.sc n).homologyπ c
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (K.iCycles n)).1 inferInstance
  refine (ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i
    ((shiftShortComplexFunctorIso AddCommGrpCat.{w} n 0 n (add_zero n)).hom.app K)) z).trans ?_
  show (K.shiftFunctorObjXIso n 0 n (zero_add n).symm).hom ((K⟦n⟧).iCycles 0 z) = _
  rw [h]
  exact ConcreteCategory.congr_hom (K.shiftFunctorObjXIso n 0 n (zero_add n).symm).inv_hom_id _

end CochainComplex.ShiftSequence

namespace Stacks.ContinuousCohomology

section TraceShift

attribute [local instance] HasDerivedCategory.standard

variable (Q : Type v) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]

/-- **`H⁰(T⟦d⟧) ≅ ℚ/ℤ` on underlying abelian groups**, for the trace target `T` of degree `d`:
`H⁰(T⟦d⟧) ≅ H^d(T)`, the underlying functor commutes with cohomology, and
`Stacks.ContinuousCohomology.traceTargetHomologyIso`. -/
def traceTargetShiftHomologyIso (d : ℤ) :
    ((underlyingAb ℤ (traceTarget.{v, w} Q d))⟦d⟧).homology 0 ≅
      (forgetAb ℤ Q).obj (ratCircle.{v, w} Q) :=
  (CochainComplex.ShiftSequence.shiftIso AddCommGrpCat d 0 d (add_zero d)).app _ ≪≫
    ((traceTarget.{v, w} Q d).sc d).mapHomologyIso (forgetAb ℤ Q) ≪≫
    (forgetAb ℤ Q).mapIso (traceTargetHomologyIso.{v, w} Q d)

omit [CompactSpace Q] in
/-- **`H⁰(T⟦d⟧) ≅ ℚ/ℤ` on the class of `t(w)`**: for a morphism `t : P ⟶ T` and a degree-`d` cycle
`w` of the underlying complex of `P`, the class in `H⁰(T⟦d⟧)` of the cycle with underlying element
`t(w)` goes to the image of the class of `w` under `H^d(t)` followed by `H^d(T) ≅ ℚ/ℤ`. -/
theorem traceTargetShiftHomologyIso_hom_homologyπ
    (P : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q) ℤ) (d : ℤ)
    (t : P ⟶ traceTarget.{v, w} Q d) (w : (underlyingAb ℤ P).cycles d)
    (z : ((underlyingAb ℤ (traceTarget.{v, w} Q d))⟦d⟧).cycles 0)
    (h : ((underlyingAb ℤ (traceTarget.{v, w} Q d))⟦d⟧).iCycles 0 z =
      ((underlyingAb ℤ (traceTarget.{v, w} Q d)).shiftFunctorObjXIso d 0 d (zero_add d).symm).inv
        ((forgetAb ℤ Q).map (t.f d) ((underlyingAb ℤ P).iCycles d w))) :
    (traceTargetShiftHomologyIso.{v, w} Q d).hom
        (((underlyingAb ℤ (traceTarget.{v, w} Q d))⟦d⟧).homologyπ 0 z) =
      (forgetAb ℤ Q).map (HomologicalComplex.homologyMap t d ≫
          (traceTargetHomologyIso.{v, w} Q d).hom)
        (((P.sc d).mapHomologyIso (forgetAb ℤ Q)).hom ((underlyingAb ℤ P).homologyπ d w)) := by
  let c := HomologicalComplex.cyclesMap (((forgetAb ℤ Q).mapHomologicalComplex _).map t) d w
  have hc : (underlyingAb ℤ (traceTarget.{v, w} Q d)).iCycles d c =
      (forgetAb ℤ Q).map (t.f d) ((underlyingAb ℤ P).iCycles d w) :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (((forgetAb ℤ Q).mapHomologicalComplex _).map t) d) w
  have h1 := CochainComplex.ShiftSequence.shiftIso_hom_app_homologyπ _ d z c (h.trans (by rw [hc]))
  have h2 : (underlyingAb ℤ (traceTarget.{v, w} Q d)).homologyπ d c =
      HomologicalComplex.homologyMap (((forgetAb ℤ Q).mapHomologicalComplex _).map t) d
        ((underlyingAb ℤ P).homologyπ d w) :=
    (ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality (((forgetAb ℤ Q).mapHomologicalComplex _).map t) d)
        w).symm
  have h3 := ConcreteCategory.congr_hom (ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) d).map t) (forgetAb ℤ Q))
      ((underlyingAb ℤ P).homologyπ d w)
  show (forgetAb ℤ Q).map (traceTargetHomologyIso.{v, w} Q d).hom
      ((((traceTarget.{v, w} Q d).sc d).mapHomologyIso (forgetAb ℤ Q)).hom
        ((CochainComplex.ShiftSequence.shiftIso AddCommGrpCat d 0 d (add_zero d)).hom.app _
          (((underlyingAb ℤ (traceTarget.{v, w} Q d))⟦d⟧).homologyπ 0 z))) = _
  rw [h1, h2, CategoryTheory.Functor.map_comp]
  exact congrArg _ h3

variable {R : Type} [Ring R] [Finite R] {S : Type} [Ring S] {φ : S →+* Rᵐᵒᵖ}
  {A : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} S Q) ℤ}
  {E : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ}
  {G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q) ℤ}

omit [CompactSpace Q] [Finite R] in
/-- **The top-degree pairing of a pairing followed by `t : G ⟶ T`, read in `ℚ/ℤ`**: on classes of
cycles `x` of `A` in degree `d` and `y` of `E` in degree `0` it is the image, under `H^d(t)`
followed by `H^d(T) ≅ ℚ/ℤ`, of the class of the cycle `P(x, y)` of `G`. -/
theorem postcomp_topDegreePairing_homologyπ (P : ComplexPairing R φ A E G) (d : ℤ)
    (t : G ⟶ traceTarget.{v, w} Q d) (x : (underlyingAb S A).cycles d)
    (y : (underlyingAb R E).cycles 0) (c : (underlyingAb ℤ G).cycles d)
    (hc : (underlyingAb ℤ G).iCycles d c =
      P.pair d 0 d (zero_add d) ((underlyingAb S A).iCycles d x) ((underlyingAb R E).iCycles 0 y)) :
    (traceTargetShiftHomologyIso.{v, w} Q d).hom ((P.postcomp t).topDegreePairing d
        ((underlyingAb S A).homologyπ d x) ((underlyingAb R E).homologyπ 0 y)) =
      (forgetAb ℤ Q).map (HomologicalComplex.homologyMap t d ≫
          (traceTargetHomologyIso.{v, w} Q d).hom)
        (((G.sc d).mapHomologyIso (forgetAb ℤ Q)).hom ((underlyingAb ℤ G).homologyπ d c)) := by
  let c' := HomologicalComplex.cyclesMap (((forgetAb ℤ Q).mapHomologicalComplex _).map t) d c
  have hc' : (underlyingAb ℤ (traceTarget.{v, w} Q d)).iCycles d c' =
      (forgetAb ℤ Q).map (t.f d) ((underlyingAb ℤ G).iCycles d c) :=
    ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (((forgetAb ℤ Q).mapHomologicalComplex _).map t) d) c
  let z : ((underlyingAb ℤ (traceTarget.{v, w} Q d))⟦d⟧).cycles 0 :=
    ShortComplex.cyclesMap ((CochainComplex.shiftShortComplexFunctorIso
      AddCommGrpCat d 0 d (add_zero d)).inv.app (underlyingAb ℤ (traceTarget.{v, w} Q d))) c'
  have hz : ((underlyingAb ℤ (traceTarget.{v, w} Q d))⟦d⟧).iCycles 0 z =
      ((underlyingAb ℤ (traceTarget.{v, w} Q d)).shiftFunctorObjXIso d 0 d (zero_add d).symm).inv
        ((forgetAb ℤ Q).map (t.f d) ((underlyingAb ℤ G).iCycles d c)) := by
    rw [← hc']
    exact ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i
      ((CochainComplex.shiftShortComplexFunctorIso
        AddCommGrpCat d 0 d (add_zero d)).inv.app (underlyingAb ℤ (traceTarget.{v, w} Q d)))) c'
  rw [(P.postcomp t).topDegreePairing_homologyπ d x y z (hz.trans (by rw [hc]; rfl))]
  exact traceTargetShiftHomologyIso_hom_homologyπ Q G d t c z hz

/-- **The top-degree pairing of a pairing followed by a trace lift, read in `ℚ/ℤ`, is the trace of
the pairing**: if `t : G ⟶ T` lifts the derived trace `tr : H^d(G) ⟶ ℚ/ℤ`, the pairing of the
classes of `x` and `y` is `tr` of the class of the cycle `P(x, y)`. -/
theorem postcomp_topDegreePairing_homologyπ_of_traceLift (P : ComplexPairing R φ A E G) (d : ℤ)
    [(DerivedCategory.Q.obj G).IsLE d]
    (tr : (DerivedCategory.homologyFunctor _ d).obj (DerivedCategory.Q.obj G) ⟶ ratCircle.{v, w} Q)
    (t : G ⟶ traceTarget.{v, w} Q d)
    (ht : DerivedCategory.Q.map t =
      derivedTraceOfIsLE.{v, w} Q G d tr ≫ DerivedCategory.Q.map (traceTargetι.{v, w} Q d))
    (x : (underlyingAb S A).cycles d) (y : (underlyingAb R E).cycles 0)
    (c : (underlyingAb ℤ G).cycles d)
    (hc : (underlyingAb ℤ G).iCycles d c =
      P.pair d 0 d (zero_add d) ((underlyingAb S A).iCycles d x) ((underlyingAb R E).iCycles 0 y)) :
    (traceTargetShiftHomologyIso.{v, w} Q d).hom ((P.postcomp t).topDegreePairing d
        ((underlyingAb S A).homologyπ d x) ((underlyingAb R E).homologyπ 0 y)) =
      (forgetAb ℤ Q).map ((DerivedCategory.homologyFunctorFactors _ d).inv.app G ≫ tr)
        (((G.sc d).mapHomologyIso (forgetAb ℤ Q)).hom ((underlyingAb ℤ G).homologyπ d c)) := by
  rw [postcomp_topDegreePairing_homologyπ Q P d t x y c hc,
    homologyMap_traceLift.{v, w} Q G d tr t ht]
  rfl

end TraceShift

end Stacks.ContinuousCohomology

end
