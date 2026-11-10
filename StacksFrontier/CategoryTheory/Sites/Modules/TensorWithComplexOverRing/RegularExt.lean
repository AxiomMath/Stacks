module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexRegularExt
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.SignTwist

/-!
# The endomorphism algebra of a K-injective complex computes its Ext groups, over the base ring

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O`, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded `R`-algebra. If `K` is
K-injective, then the map

`Hom_{D(E, d)}(E, E[n]) ⟶ Hom_{D(O)}(E ⊗_E^𝐋 K, E[n] ⊗_E^𝐋 K)`

induced by the derived tensor product of Tag 09LX formed over `R` is bijective for every `n`
(hypothesis (2) of Tag 09LZ).

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedHomWithComplexUnit_app_of_isKInjectiveOver`: the
  comparison of derived Hom out of `K` with the underived one is invertible at a K-injective
  complex.
* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerived_adj_unit_app_repRegularDerivedOver`:
  the unit of the adjunction of Tag 09LY is invertible at `E`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_map_bijective_of_isKInjectiveOver`: the
  bijectivity above.

## References

* [Stacks Project, Tag 09LZ](https://stacks.math.columbia.edu/tag/09LZ)
* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s o

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, o} X R]
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
/-- `RHom(K, -)` over `R` commutes with the translation, as the right adjoint of the derived
tensor product, which does. -/
instance derivedHomWithComplexOverCommShift :
    (derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).CommShift ℤ :=
  (tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, o} X R K
    ).rightAdjointCommShift ℤ

/-! ### The differential graded level -/

/-- The identity of `K`, as a closed element of degree zero of `Hom(K, K)`. -/
def repIdentityOver :
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading 0 :=
  ((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) 0).symm
    ((CompDG.{u, v, w, t, s, o} X R).id (liftComplex.{u, v, w, t, s} X K))

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- Under the identification of degree-zero elements of `Hom(K, K)` with morphisms `K ⟶ K`,
`repIdentityOver` corresponds to the identity of `K`. -/
theorem moduleHom_repIdentityOver :
    (Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) 0
        (repIdentityOver.{u, v, w, t, s, o} X R K) =
      (CompDG.{u, v, w, t, s, o} X R).id (liftComplex.{u, v, w, t, s} X K) :=
  LinearEquiv.apply_symm_apply _ _

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- The identity of `K` is a cocycle of `Hom(K, K)`. -/
theorem d_repIdentityOver :
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d
      (repIdentityOver.{u, v, w, t, s, o} X R K).1 = 0 := by
  have h := (Rep.{u, v, w, t, s, o} X R K).module_d (liftComplex.{u, v, w, t, s} X K) 0
    (repIdentityOver.{u, v, w, t, s, o} X R K)
  rw [moduleHom_repIdentityOver, (CompDG.{u, v, w, t, s, o} X R).d_id] at h
  exact congrArg Subtype.val
    (((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K)
      (0 + 1)).injective (h.trans (map_zero _).symm))

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- The value at the identity of `K` of a closed degree-zero homomorphism out of `Hom(K, K)` has
degree zero. -/
theorem repEval_memOver (Y : (CompDG.{u, v, w, t, s, o} X R).Obj)
    (f : (show (dgCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra).Comp from
          (Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)) ⟶
      (show (dgCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra).Comp from
          (Rep.{u, v, w, t, s, o} X R K).functor.obj Y)) :
    f.1.1 (repIdentityOver.{u, v, w, t, s, o} X R K).1 ∈
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj Y).grading 0 :=
  f.1.2.1 0 _ (repIdentityOver.{u, v, w, t, s, o} X R K).2

/-- Evaluation at the identity of `K`: a closed degree-zero homomorphism of differential graded
modules `Hom(K, K) ⟶ Hom(K, Y)` gives a closed degree-zero morphism `K ⟶ Y`. -/
def repEvalOver (Y : (CompDG.{u, v, w, t, s, o} X R).Obj)
    (f : (show (dgCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra).Comp from
          (Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)) ⟶
      (show (dgCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra).Comp from
          (Rep.{u, v, w, t, s, o} X R K).functor.obj Y)) :
    (show (CompDG.{u, v, w, t, s, o} X R).Comp from liftComplex.{u, v, w, t, s} X K) ⟶
      (show (CompDG.{u, v, w, t, s, o} X R).Comp from Y) :=
  ⟨(Rep.{u, v, w, t, s, o} X R K).moduleHom Y 0
      ⟨f.1.1 (repIdentityOver.{u, v, w, t, s, o} X R K).1,
        repEval_memOver.{u, v, w, t, s, o} X R K Y f⟩, by
    have hd : ((Rep.{u, v, w, t, s, o} X R K).functor.obj Y).d
        (f.1.1 (repIdentityOver.{u, v, w, t, s, o} X R K).1) = 0 := by
      have h := LinearMap.congr_fun (congrArg Subtype.val f.2)
        (repIdentityOver.{u, v, w, t, s, o} X R K).1
      change ((Rep.{u, v, w, t, s, o} X R K).functor.obj Y).d
          (f.1.1 (repIdentityOver.{u, v, w, t, s, o} X R K).1) -
        DifferentialGraded.gradedSign R 0 • f.1.1
          (((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d
            (repIdentityOver.{u, v, w, t, s, o} X R K).1) = 0 at h
      rwa [d_repIdentityOver, map_zero, smul_zero, sub_zero] at h
    rw [← (Rep.{u, v, w, t, s, o} X R K).module_d Y 0]
    refine (congrArg ((Rep.{u, v, w, t, s, o} X R K).moduleHom Y (0 + 1))
      (Subtype.ext hd : (_ : ((Rep.{u, v, w, t, s, o} X R K).functor.obj Y).grading (0 + 1)) =
        0)).trans (map_zero _)⟩

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- The underlying morphism of `repEvalOver Y f` is the morphism `K ⟶ Y` corresponding to the
value of `f` at the identity of `K`. -/
theorem repEval_valOver (Y : (CompDG.{u, v, w, t, s, o} X R).Obj)
    (f : (show (dgCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra).Comp from
          (Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)) ⟶
      (show (dgCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra).Comp from
          (Rep.{u, v, w, t, s, o} X R K).functor.obj Y)) :
    (repEvalOver.{u, v, w, t, s, o} X R K Y f).1 = (Rep.{u, v, w, t, s, o} X R K).moduleHom Y 0
      ⟨f.1.1 (repIdentityOver.{u, v, w, t, s, o} X R K).1,
        repEval_memOver.{u, v, w, t, s, o} X R K Y f⟩ :=
  rfl

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- Evaluation at the identity is natural in the target. -/
theorem repEval_compOver {Y Y' : (CompDG.{u, v, w, t, s, o} X R).Obj}
    (f : (show (dgCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra).Comp from
          (Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)) ⟶
      (show (dgCategory.{o, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, o} X R K).algebra).Comp from
          (Rep.{u, v, w, t, s, o} X R K).functor.obj Y))
    (g : (show (CompDG.{u, v, w, t, s, o} X R).Comp from Y) ⟶
      (show (CompDG.{u, v, w, t, s, o} X R).Comp from Y')) :
    repEvalOver.{u, v, w, t, s, o} X R K Y'
        (f ≫ (Rep.{u, v, w, t, s, o} X R K).functor.onComp.map g) =
      repEvalOver.{u, v, w, t, s, o} X R K Y f ≫ g := by
  obtain ⟨c, hc₁, hc₂⟩ := (Rep.{u, v, w, t, s, o} X R K).map_comp Y Y' 0 0 0 (by omega) g.1
    ⟨f.1.1 (repIdentityOver.{u, v, w, t, s, o} X R K).1,
      repEval_memOver.{u, v, w, t, s, o} X R K Y f⟩
  apply Subtype.ext
  rw [repEval_valOver]
  refine Eq.trans ?_ hc₂
  congr 1
  exact Subtype.ext hc₁.symm

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- A closed degree-zero homomorphism out of `Hom(K, K)` is determined by its value at the
identity of `K`. -/
theorem repEval_injectiveOver (Y : (CompDG.{u, v, w, t, s, o} X R).Obj) :
    Function.Injective (repEvalOver.{u, v, w, t, s, o} X R K Y) := by
  intro f f' h
  have h₀ : f.1.1 (repIdentityOver.{u, v, w, t, s, o} X R K).1 =
      f'.1.1 (repIdentityOver.{u, v, w, t, s, o} X R K).1 :=
    congrArg Subtype.val (((Rep.{u, v, w, t, s, o} X R K).moduleHom Y 0).injective
      (congrArg Subtype.val h))
  apply Subtype.ext
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  induction z using DirectSum.Decomposition.inductionOn
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | @homogeneous i z =>
    let b : (Rep.{u, v, w, t, s, o} X R K).algebra.grading i :=
      ((Rep.{u, v, w, t, s, o} X R K).algebraHom i).symm
        ((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) i z)
    obtain ⟨c, hc₁, hc₂⟩ := (Rep.{u, v, w, t, s, o} X R K).module_action
      (liftComplex.{u, v, w, t, s} X K) 0 i i (zero_add i)
      (repIdentityOver.{u, v, w, t, s, o} X R K) b
    rw [moduleHom_repIdentityOver, LinearEquiv.apply_symm_apply,
      (CompDG.{u, v, w, t, s, o} X R).id_comp] at hc₂
    have hcz : c = z :=
      ((Rep.{u, v, w, t, s, o} X R K).moduleHom (liftComplex.{u, v, w, t, s} X K) i).injective hc₂
    have hz : (z : ((Rep.{u, v, w, t, s, o} X R K).functor.obj
        (liftComplex.{u, v, w, t, s} X K)).M) =
        MulOpposite.op (b : (Rep.{u, v, w, t, s, o} X R K).algebra.A) •
          (repIdentityOver.{u, v, w, t, s, o} X R K).1 := by
      rw [← hcz, hc₁]
    rw [hz, f.1.2.2, f'.1.2.2, h₀]

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- The identity of `K` is sent to itself by evaluation at the identity. -/
theorem repEval_idOver :
    repEvalOver.{u, v, w, t, s, o} X R K (liftComplex.{u, v, w, t, s} X K) (𝟙 _) = 𝟙 _ :=
  Subtype.ext (moduleHom_repIdentityOver.{u, v, w, t, s, o} X R K)

/-- The unit of the differential graded tensor-Hom adjunction is invertible at `Hom(K, K)`. -/
theorem isIso_tensorWithComplexDG_adjunction_unit_app_repOver :
    IsIso ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.unit.app
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K))) :=
  (tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.isIso_unit_app_of_injective_natural
    (B := liftComplex.{u, v, w, t, s} X K)
    (repEvalOver.{u, v, w, t, s, o} X R K)
    (fun f g => repEval_compOver.{u, v, w, t, s, o} X R K f g)
    (repEval_injectiveOver.{u, v, w, t, s, o} X R K _) (Iso.refl _)
    (repEval_idOver.{u, v, w, t, s, o} X R K)

/-! ### Complexes and homotopy categories -/

/-- The unit of the tensor-Hom adjunction on complexes is invertible at `Hom(K, K)`. -/
theorem isIso_tensorWithComplexComplexes_adj_unit_app_repOver :
    IsIso ((tensorWithComplexComplexes_adj_homWithComplexOver.{u, v, w, t, s, o} X R K).unit.app
      ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K))) := by
  have h := isIso_tensorWithComplexDG_adjunction_unit_app_repOver.{u, v, w, t, s, o} X R K
  dsimp only [tensorWithComplexComplexes_adj_homWithComplexOver]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  have h₂ : IsIso ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).adjunction.unit.app
      ((compModulesEquivalence (Rep.{u, v, w, t, s, o} X R K).algebra).symm.functor.obj
        ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)))) := h
  simp only [Equivalence.toAdjunction_unit]
  refine IsIso.comp_isIso' (IsIso.comp_isIso' ?_ (Functor.map_isIso _ _))
    (Functor.map_isIso _ _)
  exact (inferInstance : IsIso ((compModulesEquivalence
      (Rep.{u, v, w, t, s, o} X R K).algebra).symm.unitIso.hom.app _))

/-- The unit of the tensor-Hom adjunction on homotopy categories is invertible at `Hom(K, K)`. -/
theorem isIso_tensorWithComplexHomotopy_adj_unit_app_repOver :
    IsIso ((tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, v, w, t, s, o}
        X R K).unit.app
      ((toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra).obj
        ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K)))) := by
  have := isIso_tensorWithComplexComplexes_adj_unit_app_repOver.{u, v, w, t, s, o} X R K
  exact CategoryTheory.Quotient.isIso_adjunctionOfSquares_unit_app _ _ _ _ _ _

/-! ### The derived categories -/

omit [ScalarSections.{u, v, w, t, s, o} X R] in
/-- The comparison of derived Hom out of `K` with the underived one is invertible at a
K-injective complex. -/
theorem isIso_derivedHomWithComplexUnit_app_of_isKInjectiveOver
    (L : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) [L.IsKInjective] :
    IsIso ((derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K).app
      ((HomotopyCategory.quotient _ _).obj L)) := by
  have := Functor.hasPointwiseRightDerivedFunctor_of_coresolutions
    (L := DerivedCategory.Qh)
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (homWithComplexToDerivedCategoryOver.{u, v, w, t, s, o} X R K)
    (exists_coresolution_map_bijective_sheaf.{u, v, w, t, s} X)
  exact (Functor.LeftExtension.mk _ (derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K)
    ).isIso_hom_app_of_bijective
    (Functor.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
      (derivedHomWithComplexOver.{u, v, w, t, s, o} X R K)
      (derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K)
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) _)
    (fun Z => CochainComplex.IsKInjective.Qh_map_bijective Z L)

/-- **The unit of the derived adjunction of Tag 09LY is invertible at the regular module** when
`K` is K-injective. -/
theorem isIso_tensorWithComplexDerived_adj_unit_app_repRegularDerivedOver
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] :
    IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, o}
        X R K).unit.app (repRegularDerivedOver.{u, v, w, t, s, o} X R K)) := by
  let P := (toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra).obj
    ((Rep.{u, v, w, t, s, o} X R K).functor.obj (liftComplex.{u, v, w, t, s} X K))
  let eReg : (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.obj P ≅
      repRegularDerivedOver.{u, v, w, t, s, o} X R K :=
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.mapIso
      ((toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra).mapIso
        DGCategory.representableSelfIsoRegular)
  suffices h : IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, o}
      X R K).unit.app ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.obj P)) from
    NatTrans.isIso_app_of_iso_of_isIso _ eReg.symm
  have hα : (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).IsLeftDerivedFunctor
      (show (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⋙
            tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⟶
          tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K ⋙ DerivedCategory.Qh from
        tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra) :=
    tensorWithComplexDerived_isLeftDerivedFunctor.{u, v, w, t, s, o} X R K
  have hβ' : (derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).IsRightDerivedFunctor
      (show homWithComplexHomotopyOver.{u, v, w, t, s, o} X R K ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⟶
          DerivedCategory.Qh ⋙ derivedHomWithComplexOver.{u, v, w, t, s, o} X R K from
        derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K)
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) :=
    derivedHomWithComplex_isRightDerivedFunctorOver.{u, v, w, t, s, o} X R K
  have hleft := Functor.isLeftDerivedFunctor_comp_of_resolutions
    (L := (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q)
    (W := quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
    (show (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⋙
          tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⟶
        tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K ⋙ DerivedCategory.Qh from
      tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
    (derivedHomWithComplexOver.{u, v, w, t, s, o} X R K)
    (exists_resolution_q_map_bijective_rep.{u, v, w, t, s, o} X R K)
  have hfac := Adjunction.derivedη_fac_app
    (tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, v, w, t, s, o} X R K)
    (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra)
    (show (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⋙
          tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⟶
        tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K ⋙ DerivedCategory.Qh from
      tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K)
    (show homWithComplexHomotopyOver.{u, v, w, t, s, o} X R K ⋙
          (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q ⟶
        DerivedCategory.Qh ⋙ derivedHomWithComplexOver.{u, v, w, t, s, o} X R K from
      derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K) P
  have hc : IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app P) :=
    isIso_tensorWithComplexDerivedCounit_appOver.{u, v, w, t, s, o} X R K _
      (leftOrthogonal_acyclic_rep_selfOver.{u, v, w, t, s, o} X R K)
  have hη : IsIso ((tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, v, w, t, s, o}
      X R K).unit.app P) :=
    isIso_tensorWithComplexHomotopy_adj_unit_app_repOver.{u, v, w, t, s, o} X R K
  have hβ : IsIso ((derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K).app
      ((tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K).obj P)) := by
    have := isIso_derivedHomWithComplexUnit_app_of_isKInjectiveOver.{u, v, w, t, s, o} X R K
      (liftComplex.{u, v, w, t, s} X K)
    exact NatTrans.isIso_app_of_iso_of_isIso _
      (tensorWithComplexHomotopyRegularIsoOver.{u, v, w, t, s, o} X R K)
  have hfac' : (tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, o}
      X R K).unit.app ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.obj P) ≫
      (derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).map
        ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app P) =
      (quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.map
        ((tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, v, w, t, s, o}
          X R K).unit.app P) ≫
      (derivedHomWithComplexUnitOver.{u, v, w, t, s, o} X R K).app
        ((tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K).obj P) := hfac
  have hcomp : IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, o}
      X R K).unit.app ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.obj P) ≫
      (derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).map
        ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app P)) := by
    rw [hfac']
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) hβ
  exact IsIso.of_isIso_comp_right _
    ((derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).map
      ((tensorWithComplexDerivedCounit.{u, v, w, t, s, o} X R K).app P))

/-- **`E` computes the ext groups of a K-injective `K`.** For every `n`, the derived tensor
product `- ⊗_E^𝐋 K` of Tag 09LX is bijective from `Hom_{D(E, d)}(E, E[n])` onto
`Hom_{D(O)}(E ⊗_E^𝐋 K, E[n] ⊗_E^𝐋 K)`. This is hypothesis (2) of Tag 09LZ for `K` K-injective. -/
theorem tensorWithComplexDerived_map_bijective_of_isKInjectiveOver
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] (n : ℤ) :
    Function.Bijective
      (fun f : repRegularDerivedOver.{u, v, w, t, s, o} X R K ⟶
          (repRegularDerivedOver.{u, v, w, t, s, o} X R K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).map f) := by
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, o} X R K
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have h₀ :=
    isIso_tensorWithComplexDerived_adj_unit_app_repRegularDerivedOver.{u, v, w, t, s, o} X R K
  have hshift : IsIso (adj.unit.app ((repRegularDerivedOver.{u, v, w, t, s, o} X R K)⟦n⟧)) := by
    have h := NatTrans.shift_app_comm adj.unit n (repRegularDerivedOver.{u, v, w, t, s, o} X R K)
    have : IsIso (adj.unit.app ((repRegularDerivedOver.{u, v, w, t, s, o} X R K)⟦n⟧) ≫
        (((tensorWithComplexDerived.{u, v, w, t, s, o} X R K) ⋙
          derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).commShiftIso n).hom.app
            (repRegularDerivedOver.{u, v, w, t, s, o} X R K)) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((((tensorWithComplexDerived.{u, v, w, t, s, o} X R K) ⋙
          derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).commShiftIso n).hom.app
            (repRegularDerivedOver.{u, v, w, t, s, o} X R K))
  exact adj.map_bijective_of_isIso_unit_app _

end AlgebraicGeometry.RingedSite

end
