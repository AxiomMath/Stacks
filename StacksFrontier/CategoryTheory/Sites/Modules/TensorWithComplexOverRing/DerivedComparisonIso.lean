module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoproducts
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.ComparisonRegular
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.DerivedComparison

/-!
# The comparison `θ : - ⊗_A^𝐋 Hom(L, K) ⋙ - ⊗_B^𝐋 L ⟶ - ⊗_A^𝐋 K` is an isomorphism

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O`, let `K`, `L` be complexes of `O`-modules with endomorphism
differential graded `R`-algebras `A`, `B`, with `K` K-injective, and let `𝒟` be a strictly full
subcategory of `D(O)` containing the images of `- ⊗_A^𝐋 K` and of `- ⊗_B^𝐋 L` and onto which
`- ⊗_B^𝐋 L` is an equivalence. Then the comparison `θ` of
`AlgebraicGeometry.RingedSite.tensorHomComparisonDerived` is an isomorphism: the composite
`D(A, d) → 𝒟 → D(B, d)` of `- ⊗_A^𝐋 K` with the quasi-inverse of `- ⊗_B^𝐋 L` is
`- ⊗_A^𝐋 Hom(L, K)`.

The argument: `θ` is invertible as soon as its conjugate `RHom(K, -) ⟶ RHom(Hom(L, K), RHom(L, -))`
under the adjunctions of Tags 09LY and 09LT is, and that is tested against the shifts of the
regular module, which generate `D(A, d)`. At a shift `E[k]` of `E = Hom(K, K)` the comparison is
computed by the ordinary tensor products, and its adjoint is the class of the isomorphism
`E[k] ⊗_A Hom(L, K) ≅ Hom(L, E[k] ⊗_A K)` of
`AlgebraicGeometry.RingedSite.isIso_tensorHomComparison_shift` followed by the comparison of
derived Hom with ordinary Hom at the K-injective complex `E[k] ⊗_A K ≅ K[k]`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_tensorHomComparisonDerived`

## References

* [Stacks Project, Tag 09SU](https://stacks.math.columbia.edu/tag/09SU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DifferentialGradedModule CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  (R : Type u) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  [ScalarSections.{u, u, u, u, u, u} X R]
  (K L : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-- The tensor-Hom adjunction on homotopy categories, on the class of a morphism of complexes, is
the class of the adjoint on complexes. -/
theorem tensorWithComplexHomotopy_adj_homEquiv_quotient
    (N : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra)
    (Y : CochainComplex (TensorModO.{u, u, u, u, u} X) ℤ)
    (g : (dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R L).functor).obj N ⟶ Y) :
    (tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, u, u, u, u, u} X R L).homEquiv
        ((toHomotopyCategory _).obj N) ((HomotopyCategory.quotient _ _).obj Y)
        ((HomotopyCategory.quotient _ _).map g) =
      (toHomotopyCategory _).map
        ((tensorWithComplexComplexes_adj_homWithComplexOver.{u, u, u, u, u, u} X R L).homEquiv
          N Y g) := by
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  refine congrArg₂ (· ≫ ·) ?_ rfl
  simp only [tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver,
    Quotient.adjunctionOfSquares, Quotient.adjunctionLift, Adjunction.ofNatIsoLeft,
    Adjunction.ofNatIsoRight, NatTrans.comp_app, Quotient.natIsoLift]
  rw [Category.assoc]
  refine (congrArg _ ?_).trans (Category.comp_id _)
  change (homWithComplexHomotopyOver.{u, u, u, u, u, u} X R L).map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
  exact (congrArg (· ≫ 𝟙 _) ((homWithComplexHomotopyOver.{u, u, u, u, u, u} X R L).map_id _)).trans
    (Category.comp_id _)

/-- **The counit of the adjunction of Tag 09LY is invertible on the essential image.** If
`- ⊗_B^𝐋 L` is an equivalence onto a strictly full subcategory `𝒟` of `D(O)`, then the counit
`RHom(L, Y) ⊗_B^𝐋 L ⟶ Y` is invertible at every `Y` of `𝒟`. -/
theorem isIso_tensorWithComplexDerived_adj_counit_app
    (P : ObjectProperty (stdDerivedSite X)) [P.IsClosedUnderIsomorphisms]
    (hPL : ∀ M, P ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).obj M))
    [(P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).IsEquivalence]
    (Y : stdDerivedSite X) (hY : P Y) :
    IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, u, u, u, u, u}
      X R L).counit.app Y) := by
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, u, u, u, u, u} X R L
  let hff : (tensorWithComplexDerived.{u, u, u, u, u, u} X R L).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful
      (P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL)).comp P.fullyFaithfulι
  have := hff.full
  have := hff.faithful
  let e : (tensorWithComplexDerived.{u, u, u, u, u, u} X R L).obj
      ((P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).objPreimage ⟨Y, hY⟩) ≅ Y :=
    P.ι.mapIso ((P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).objObjPreimageIso
      ⟨Y, hY⟩)
  have : IsIso (adj.counit.app ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).obj
      ((P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).objPreimage ⟨Y, hY⟩))) := by
    have h := adj.left_triangle_components
      ((P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).objPreimage ⟨Y, hY⟩)
    have : IsIso ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).map
        (adj.unit.app ((P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).objPreimage
          ⟨Y, hY⟩)) ≫ adj.counit.app ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).obj
          ((P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).objPreimage
            ⟨Y, hY⟩))) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).map
      (adj.unit.app _)) _
  exact NatTrans.isIso_app_of_iso_of_isIso adj.counit e.symm

/-- **`E[k] ⊗_A K` is K-injective** when `K` is: it is `(E ⊗_A K)[k] ≅ K[k]`. -/
theorem isKInjective_tensorWithComplexDG_repSelfShift
    [(liftComplex.{u, u, u, u, u} X K).IsKInjective] (k : ℤ) :
    ((dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).obj
      (repSelfShift X R K k)).IsKInjective := by
  let e₂ : (dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).obj
      (repSelf X R K) ≅ liftComplex.{u, u, u, u, u} X K :=
    (CochainComplex.complexesToCochainFunctorLinear (TensorModO.{u, u, u, u, u} X) R).mapIso
      (tensorWithComplexDG_regular.{u, u, u, u, u, u} X R K)
  exact CochainComplex.isKInjective_of_iso
    ((dgFunctorToComplexesShiftIso (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor
      (repSelf X R K) k) ≪≫ (CategoryTheory.shiftFunctor _ k).mapIso e₂).symm

/-- The unit of the derived adjunction of Tag 09LY followed by derived Hom of the counit is the
class of the unit on homotopy categories followed by the comparison of derived with ordinary
Hom. -/
theorem tensorWithComplexDerived_adj_unit_app_comp_map_counit
    (N : DifferentialGradedModule.HomotopyCategory.{u, u, u}
      (Rep.{u, u, u, u, u, u} X R L).algebra) :
    (tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, u, u, u, u, u} X R L).unit.app
        ((quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q.obj N) ≫
      (derivedHomWithComplexOver.{u, u, u, u, u, u} X R L).map
        ((tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L).app N) =
      (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q.map
        ((tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, u, u, u, u, u}
          X R L).unit.app N) ≫
      (derivedHomWithComplexUnitOver.{u, u, u, u, u, u} X R L).app
        ((tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L).obj N) := by
  have hα : (tensorWithComplexDerived.{u, u, u, u, u, u} X R L).IsLeftDerivedFunctor
      (show (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q ⋙
            tensorWithComplexDerived.{u, u, u, u, u, u} X R L ⟶
          tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L ⋙ stdQh X from
        tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L)
      (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra) :=
    tensorWithComplexDerived_isLeftDerivedFunctor.{u, u, u, u, u, u} X R L
  have hβ' : (derivedHomWithComplexOver.{u, u, u, u, u, u} X R L).IsRightDerivedFunctor
      (show homWithComplexHomotopyOver.{u, u, u, u, u, u} X R L ⋙
            (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q ⟶
          stdQh X ⋙ derivedHomWithComplexOver.{u, u, u, u, u, u} X R L from
        derivedHomWithComplexUnitOver.{u, u, u, u, u, u} X R L)
      (HomotopyCategory.quasiIso (TensorModO.{u, u, u, u, u} X) (ComplexShape.up ℤ)) :=
    derivedHomWithComplex_isRightDerivedFunctorOver.{u, u, u, u, u, u} X R L
  have hleft := Functor.isLeftDerivedFunctor_comp_of_resolutions
    (L := (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q)
    (W := quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra)
    (show (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q ⋙
          tensorWithComplexDerived.{u, u, u, u, u, u} X R L ⟶
        tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L ⋙ stdQh X from
      tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L)
    (derivedHomWithComplexOver.{u, u, u, u, u, u} X R L)
    (exists_resolution_q_map_bijective_rep.{u, u, u, u, u, u} X R L)
  exact Adjunction.derivedη_fac_app
    (tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, u, u, u, u, u} X R L)
    (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra)
    (show (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q ⋙
          tensorWithComplexDerived.{u, u, u, u, u, u} X R L ⟶
        tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L ⋙ stdQh X from
      tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L)
    (show homWithComplexHomotopyOver.{u, u, u, u, u, u} X R L ⋙
          (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q ⟶
        stdQh X ⋙ derivedHomWithComplexOver.{u, u, u, u, u, u} X R L from
      derivedHomWithComplexUnitOver.{u, u, u, u, u, u} X R L) N

/-- **The adjoint, under Tag 09LY, of a morphism out of a derived tensor product computed by the
plain one.** For `N` in `K(Mod_(B, d))` and a morphism `g : N ⊗_B L ⟶ Y` of `K(O)`, the adjoint of
`N ⊗_B^𝐋 L ⟶ N ⊗_B L ⟶ Y` is the class of the adjoint of `g` on homotopy categories followed by
the comparison of derived Hom with ordinary Hom out of `L`. -/
theorem tensorWithComplexDerived_adj_homEquiv_counit_comp
    (N : DifferentialGradedModule.HomotopyCategory.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra)
    (Y : _root_.HomotopyCategory (TensorModO.{u, u, u, u, u} X) (ComplexShape.up ℤ))
    (g : (tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L).obj N ⟶ Y) :
    (tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, u, u, u, u, u} X R L).homEquiv
        ((quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q.obj N)
        ((stdQh X).obj Y)
        ((tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L).app N ≫
          (show (tensorWithComplexToDerivedCategory.{u, u, u, u, u, u} X R L).obj N ⟶
            (stdQh X).obj Y from (stdQh X).map g)) =
      (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q.map
          ((tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, u, u, u, u, u}
            X R L).homEquiv N Y g) ≫
        (derivedHomWithComplexUnitOver.{u, u, u, u, u, u} X R L).app Y := by
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, u, u, u, u, u} X R L
  let Q := (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q
  let η := (tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, u, u, u, u, u}
    X R L).unit.app N
  let β := derivedHomWithComplexUnitOver.{u, u, u, u, u, u} X R L
  calc adj.homEquiv _ _ ((tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L).app N ≫
          (show (tensorWithComplexToDerivedCategory.{u, u, u, u, u, u} X R L).obj N ⟶
            (stdQh X).obj Y from (stdQh X).map g))
        = adj.homEquiv _ _ ((tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L).app N) ≫
          (derivedHomWithComplexOver.{u, u, u, u, u, u} X R L).map ((stdQh X).map g) :=
          adj.homEquiv_naturality_right _ _
      _ = (Q.map η ≫ β.app ((tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L).obj N)) ≫
          (derivedHomWithComplexOver.{u, u, u, u, u, u} X R L).map ((stdQh X).map g) :=
          congrArg (· ≫ _) ((adj.homEquiv_unit _ _ _).trans
            (tensorWithComplexDerived_adj_unit_app_comp_map_counit X R L N))
      _ = Q.map η ≫ (β.app ((tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L).obj N) ≫
          (derivedHomWithComplexOver.{u, u, u, u, u, u} X R L).map ((stdQh X).map g)) :=
          Category.assoc _ _ _
      _ = Q.map η ≫ (Q.map ((homWithComplexHomotopyOver.{u, u, u, u, u, u} X R L).map g) ≫
          β.app Y) := congrArg (Q.map η ≫ ·) (β.naturality g).symm
      _ = (Q.map η ≫ Q.map ((homWithComplexHomotopyOver.{u, u, u, u, u, u} X R L).map g)) ≫
          β.app Y := (Category.assoc _ _ _).symm
      _ = Q.map (η ≫ (homWithComplexHomotopyOver.{u, u, u, u, u, u} X R L).map g) ≫ β.app Y :=
          congrArg (· ≫ β.app Y) (Q.map_comp _ _).symm
      _ = _ := congrArg (fun f => Q.map f ≫ β.app Y)
          ((tensorWithComplexHomotopy_adj_homWithComplexHomotopyOver.{u, u, u, u, u, u}
            X R L).homEquiv_unit _ _ _).symm

/-- The comparison on homotopy categories at the class of a differential graded module. -/
theorem tensorHomComparisonHomotopy_app
    (M : DifferentialGradedModule.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra) :
    (tensorHomComparisonHomotopy X R K L).app ((toHomotopyCategory _).obj M) =
      (tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L).map
          ((DifferentialGraded.Bimodule.tensorCompFunctor_quotient (homBimodule X R K L)).inv.app
            M) ≫
        (HomotopyCategory.quotient _ _).map ((tensorHomComparisonComplexes X R K L).app M) := by
  simp only [tensorHomComparisonHomotopy, Quotient.natTransLift_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app]
  change _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

omit [ScalarSections.{u, u, u, u, u, u} X R] in
/-- `E[k]` is orthogonal on the left to the acyclic modules: it is a shift of the regular
module. -/
theorem leftOrthogonal_acyclic_repSelfShift (k : ℤ) :
    (acyclic' (Rep.{u, u, u, u, u, u} X R K).algebra).leftOrthogonal
      ((toHomotopyCategory _).obj (repSelfShift X R K k)) :=
  leftOrthogonal_acyclic_of_iso _
    ((CategoryTheory.shiftFunctor (DifferentialGradedModule _) k).mapIso
      (DGCategory.representableSelfIsoRegular (A := CompDG.{u, u, u, u, u, u} X R)
        (x := liftComplex.{u, u, u, u, u} X K))).symm
    (leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule _ k)

/-- The adjoint, under Tag 09LY, of the comparison at `E[k]` after the derived tensor product
with `Hom(L, K)` has been computed by the plain one, is an isomorphism. -/
theorem isIso_homEquiv_tensorWithComplexDerivedCounit_comp_comparison
    [(liftComplex.{u, u, u, u, u} X K).IsKInjective] (k : ℤ) :
    IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, u, u, u, u, u}
        X R L).homEquiv _ _
        ((tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L).app
          ((toHomotopyCategory _).obj
            ((DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L)).obj
              (repSelfShift X R K k))) ≫
        (show (tensorWithComplexToDerivedCategory.{u, u, u, u, u, u} X R L).obj
            ((toHomotopyCategory _).obj
              ((DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L)).obj
                (repSelfShift X R K k))) ⟶
          (stdQh X).obj ((HomotopyCategory.quotient _ _).obj
            ((dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).obj
              (repSelfShift X R K k)))
          from (stdQh X).map ((HomotopyCategory.quotient _ _).map
            ((tensorHomComparisonComplexes X R K L).app (repSelfShift X R K k)))))) := by
  have := isKInjective_tensorWithComplexDG_repSelfShift X R K k
  have hμ := isIso_tensorHomComparison_shift X R K L k
  have hu := isIso_derivedHomWithComplexUnit_app_of_isKInjectiveOver.{u, u, u, u, u, u} X R L
    ((dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).obj
      (repSelfShift X R K k))
  have e₁ := tensorWithComplexDerived_adj_homEquiv_counit_comp X R L
    ((toHomotopyCategory _).obj
      ((DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L)).obj
        (repSelfShift X R K k)))
    ((HomotopyCategory.quotient _ _).obj
      ((dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).obj
        (repSelfShift X R K k)))
    ((HomotopyCategory.quotient _ _).map
      ((tensorHomComparisonComplexes X R K L).app (repSelfShift X R K k)))
  rw [tensorWithComplexHomotopy_adj_homEquiv_quotient,
    tensorHomComparisonComplexes_homEquiv] at e₁
  have hr : IsIso ((quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q.map
      ((toHomotopyCategory _).map (tensorHomComparison X R K L (repSelfShift X R K k))) ≫
    (derivedHomWithComplexUnitOver.{u, u, u, u, u, u} X R L).app
      ((HomotopyCategory.quotient _ _).obj
        ((dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).obj
          (repSelfShift X R K k)))) := by
    have : IsIso ((toHomotopyCategory _).map
        (tensorHomComparison X R K L (repSelfShift X R K k))) := Functor.map_isIso _ _
    have : IsIso ((quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q.map
        ((toHomotopyCategory _).map (tensorHomComparison X R K L (repSelfShift X R K k)))) :=
      Functor.map_isIso _ _
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hu
  exact (congrArg IsIso e₁).mpr hr

/-- **The comparison at `E[k]`, after the derived tensor product with `Hom(L, K)` has been
computed by the plain one, is an isomorphism**: `(E[k] ⊗_A Ω') ⊗_B^𝐋 L ⟶ (E[k] ⊗_A Ω') ⊗_B L ⟶
E[k] ⊗_A K`. Its adjoint under Tag 09LY is the class of the isomorphism
`E[k] ⊗_A Ω' ≅ Hom(L, E[k] ⊗_A K)` followed by the comparison of derived Hom with ordinary Hom at
the K-injective `E[k] ⊗_A K`, and the counit is invertible there because `E[k] ⊗_A K` lies in the
essential image of `- ⊗_B^𝐋 L`. -/
theorem isIso_tensorWithComplexDerivedCounit_comp_comparison
    [(liftComplex.{u, u, u, u, u} X K).IsKInjective]
    (P : ObjectProperty (stdDerivedSite X)) [P.IsClosedUnderIsomorphisms]
    (hPK : ∀ M, P ((tensorWithComplexDerived.{u, u, u, u, u, u} X R K).obj M))
    (hPL : ∀ M, P ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).obj M))
    [(P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).IsEquivalence] (k : ℤ) :
    IsIso ((tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L).app
        ((toHomotopyCategory _).obj
          ((DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L)).obj
            (repSelfShift X R K k))) ≫
      (show (tensorWithComplexToDerivedCategory.{u, u, u, u, u, u} X R L).obj
          ((toHomotopyCategory _).obj
            ((DifferentialGraded.Bimodule.tensorCompFunctor (homBimodule X R K L)).obj
              (repSelfShift X R K k))) ⟶
        (stdQh X).obj ((HomotopyCategory.quotient _ _).obj
          ((dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).obj
            (repSelfShift X R K k)))
        from (stdQh X).map ((HomotopyCategory.quotient _ _).map
          ((tensorHomComparisonComplexes X R K L).app (repSelfShift X R K k))))) := by
  -- the adjoint is an isomorphism
  have hadj := isIso_homEquiv_tensorWithComplexDerivedCounit_comp_comparison X R K L k
  -- the counit is an isomorphism at `E[k] ⊗_A K`
  have hcK := isIso_tensorWithComplexDerivedCounit_appOver.{u, u, u, u, u, u} X R K _
    (leftOrthogonal_acyclic_repSelfShift X R K k)
  have hY : P ((stdQh X).obj ((HomotopyCategory.quotient _ _).obj
      ((dgFunctorToComplexes (tensorWithComplexDG.{u, u, u, u, u, u} X R K).functor).obj
        (repSelfShift X R K k)))) :=
    P.prop_of_iso (@asIso _ _ _ _ ((tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R K).app
      ((toHomotopyCategory _).obj (repSelfShift X R K k))) hcK) (hPK _)
  have hε := isIso_tensorWithComplexDerived_adj_counit_app X R L P hPL _ hY
  rw [← ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, u, u, u, u, u} X R L).homEquiv
    _ _).symm_apply_apply ((tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L).app _ ≫ _),
    Adjunction.homEquiv_counit]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) hε

/-- A composite `𝟙 ≫ a ≫ ((𝟙 ≫ b) ≫ (𝟙 ≫ c))` is invertible when `a` is, and when `b ≫ c` can be
rewritten, through a commutative square `b ≫ c₁ = d ≫ b'` with `d` invertible, as
`d ≫ b' ≫ c₂` with `b' ≫ c₂` invertible. -/
theorem isIso_comp_of_square {C : Type*} [Category C] {P₀ P₁ P₂ P₁' P₃ P₄ : C} (a : P₀ ⟶ P₁)
    (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₄) (c₁ : P₂ ⟶ P₃) (c₂ : P₃ ⟶ P₄) (d : P₁ ⟶ P₁') (b' : P₁' ⟶ P₃)
    (hc : c = c₁ ≫ c₂) (h : b ≫ c₁ = d ≫ b') (ha : IsIso a) (hd : IsIso d)
    (hbc : IsIso (b' ≫ c₂)) :
    IsIso (𝟙 P₀ ≫ a ≫ ((𝟙 P₁ ≫ b) ≫ (𝟙 P₂ ≫ c))) := by
  rw [Category.id_comp, Category.id_comp, Category.id_comp, hc, ← Category.assoc b, h,
    Category.assoc]
  infer_instance

/-- **The comparison `θ̃` is invertible at `E[k]`.** -/
theorem isIso_tensorHomComparisonDerivedAux_app_shift
    [(liftComplex.{u, u, u, u, u} X K).IsKInjective]
    (P : ObjectProperty (stdDerivedSite X)) [P.IsClosedUnderIsomorphisms]
    (hPK : ∀ M, P ((tensorWithComplexDerived.{u, u, u, u, u, u} X R K).obj M))
    (hPL : ∀ M, P ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).obj M))
    [(P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).IsEquivalence] (k : ℤ) :
    IsIso ((tensorHomComparisonDerivedAux X R K L).app
      ((toHomotopyCategory _).obj (repSelfShift X R K k))) := by
  have hnat := (tensorWithComplexDerivedCounit.{u, u, u, u, u, u} X R L).naturality
    ((DifferentialGraded.Bimodule.tensorCompFunctor_quotient (homBimodule X R K L)).inv.app
      (repSelfShift X R K k))
  have hτ : (stdQh X).map ((tensorHomComparisonHomotopy X R K L).app
      ((toHomotopyCategory _).obj (repSelfShift X R K k))) =
      (stdQh X).map ((tensorWithComplexHomotopy.{u, u, u, u, u, u} X R L).map
          ((DifferentialGraded.Bimodule.tensorCompFunctor_quotient (homBimodule X R K L)).inv.app
            (repSelfShift X R K k))) ≫
        (stdQh X).map ((HomotopyCategory.quotient _ _).map
          ((tensorHomComparisonComplexes X R K L).app (repSelfShift X R K k))) := by
    rw [tensorHomComparisonHomotopy_app]
    exact (stdQh X).map_comp _ _
  have hT : IsIso
      ((DifferentialGraded.Bimodule.derivedTensorFunctorCounit (homBimodule X R K L)).app
        ((toHomotopyCategory _).obj (repSelfShift X R K k))) :=
    DifferentialGraded.Bimodule.isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal _ _
      (leftOrthogonal_acyclic_repSelfShift X R K k)
  have hc := isIso_tensorWithComplexDerivedCounit_comp_comparison X R K L P hPK hPL k
  have hFT : IsIso ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).map
      ((DifferentialGraded.Bimodule.derivedTensorFunctorCounit (homBimodule X R K L)).app
        ((toHomotopyCategory _).obj (repSelfShift X R K k)))) :=
    ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).mapIso (@asIso _ _ _ _ _ hT)).isIso_hom
  have hd : IsIso ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).map
      ((quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R L).algebra).Q.map
        ((DifferentialGraded.Bimodule.tensorCompFunctor_quotient (homBimodule X R K L)).inv.app
          (repSelfShift X R K k)))) := Functor.map_isIso _ _
  exact isIso_comp_of_square _ _ _ _ _ _ _ hτ hnat.symm hFT hd hc

/-- **The mate of a transformation of left adjoints, on morphisms.** For adjunctions
`L₁ ⊣ R₁`, `L₂ ⊣ R₂` and `α : L₂ ⟶ L₁` with conjugate `β : R₁ ⟶ R₂`, postcomposition with `β` is
precomposition with `α` read through the two adjunctions. -/
theorem comp_conjugateEquiv_app {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D}
    {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {Z : C} {Y : D}
    (f : Z ⟶ R₁.obj Y) :
    f ≫ (conjugateEquiv adj₁ adj₂ α).app Y =
      adj₂.homEquiv Z Y (α.app Z ≫ (adj₁.homEquiv Z Y).symm f) := by
  apply (adj₂.homEquiv Z Y).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc, conjugateEquiv_counit, ← Category.assoc,
    α.naturality, Category.assoc]

section Detection

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-- **The comparison `θ` is invertible at `E[k]`.** -/
theorem isIso_tensorHomComparisonDerived_app_repSelfShift
    [(liftComplex.{u, u, u, u, u} X K).IsKInjective]
    (P : ObjectProperty (stdDerivedSite X)) [P.IsClosedUnderIsomorphisms]
    (hPK : ∀ M, P ((tensorWithComplexDerived.{u, u, u, u, u, u} X R K).obj M))
    (hPL : ∀ M, P ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).obj M))
    [(P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).IsEquivalence] (k : ℤ) :
    IsIso ((tensorHomComparisonDerived X R K L).app
      ((quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra).Q.obj
        ((toHomotopyCategory _).obj (repSelfShift X R K k)))) := by
  have hcK := isIso_tensorWithComplexDerivedCounit_appOver.{u, u, u, u, u, u} X R K _
    (leftOrthogonal_acyclic_repSelfShift X R K k)
  have hθ' := isIso_tensorHomComparisonDerivedAux_app_shift X R K L P hPK hPL k
  rw [← tensorHomComparisonDerived_app_comp_counit] at hθ'
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hcK hθ'

/-- **The comparison `θ : - ⊗_A^𝐋 Hom(L, K) ⋙ - ⊗_B^𝐋 L ⟶ - ⊗_A^𝐋 K` is an isomorphism**, when
`K` is K-injective and `- ⊗_B^𝐋 L` is an equivalence onto a strictly full subcategory `𝒟` of
`D(O)` containing the image of `- ⊗_A^𝐋 K`. -/
theorem isIso_tensorHomComparisonDerived
    [(liftComplex.{u, u, u, u, u} X K).IsKInjective]
    (P : ObjectProperty (stdDerivedSite X)) [P.IsClosedUnderIsomorphisms]
    (hPK : ∀ M, P ((tensorWithComplexDerived.{u, u, u, u, u, u} X R K).obj M))
    (hPL : ∀ M, P ((tensorWithComplexDerived.{u, u, u, u, u, u} X R L).obj M))
    [(P.lift (tensorWithComplexDerived.{u, u, u, u, u, u} X R L) hPL).IsEquivalence] :
    IsIso (tensorHomComparisonDerived X R K L) := by
  -- the three adjunctions
  let adjK := tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, u, u, u, u, u} X R K
  let adjL := tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, u, u, u, u, u} X R L
  let adjT : derivedTensorHom X R K L ⊣
      (show DifferentialGradedModule.derivedCategory.{u, u, u}
          (Rep.{u, u, u, u, u, u} X R L).algebra ⥤
        DifferentialGradedModule.derivedCategory.{u, u, u}
          (Rep.{u, u, u, u, u, u} X R K).algebra from
        (derivedHomData (Rep.{u, u, u, u, u, u} X R K).algebra
          (Rep.{u, u, u, u, u, u} X R L).algebra
          (homBimodule X R K L).rightModule (homBimodule X R K L).leftAction).functor) :=
    DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHomFunctor (homBimodule X R K L)
  let adjLT := adjT.comp adjL
  suffices h : IsIso (conjugateEquiv adjK adjLT (tensorHomComparisonDerived X R K L)) from
    conjugateEquiv_of_iso adjK adjLT (tensorHomComparisonDerived X R K L)
  have hY : ∀ Y,
      IsIso ((conjugateEquiv adjK adjLT (tensorHomComparisonDerived X R K L)).app Y) := by
    intro Y
    refine (DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule
      (Rep.{u, u, u, u, u, u} X R K).algebra).isIso_of_bijective_comp
      ((conjugateEquiv adjK adjLT (tensorHomComparisonDerived X R K L)).app Y) (fun {Z} hZ => ?_)
    obtain ⟨E', n, e, hE'⟩ := hZ
    obtain rfl := (ObjectProperty.singleton_iff _ _).1 hE'
    -- `θ` is invertible at `Z ≅ E[n]`
    let eZ : Z ≅ (quasiIsomorphisms.{u, u, u} (Rep.{u, u, u, u, u, u} X R K).algebra).Q.obj
        ((toHomotopyCategory _).obj (repSelfShift X R K n)) :=
      e ≪≫ (((toHomotopyCategory _ ⋙
        (quasiIsomorphisms' (Rep.{u, u, u, u, u, u} X R K).algebra).Q).commShiftIso n).app
          (regularModule _)).symm ≪≫
      (toHomotopyCategory _ ⋙ (quasiIsomorphisms' (Rep.{u, u, u, u, u, u} X R K).algebra).Q).mapIso
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule _) n).mapIso
          (DGCategory.representableSelfIsoRegular (A := CompDG.{u, u, u, u, u, u} X R)
            (x := liftComplex.{u, u, u, u, u} X K))).symm
    have hθZ : IsIso ((tensorHomComparisonDerived X R K L).app Z) :=
      @NatTrans.isIso_app_of_iso_of_isIso _ _ _ _ _ _ (tensorHomComparisonDerived X R K L) _ _ eZ
        (isIso_tensorHomComparisonDerived_app_repSelfShift X R K L P hPK hPL n)
    have hfun : (fun f : Z ⟶ (derivedHomWithComplexOver.{u, u, u, u, u, u} X R K).obj Y =>
        f ≫ (conjugateEquiv adjK adjLT (tensorHomComparisonDerived X R K L)).app Y) =
        (adjLT.homEquiv Z Y) ∘ (fun g => (tensorHomComparisonDerived X R K L).app Z ≫ g) ∘
          (adjK.homEquiv Z Y).symm :=
      funext fun f => comp_conjugateEquiv_app adjK adjLT (tensorHomComparisonDerived X R K L) f
    rw [hfun]
    refine (Equiv.bijective _).comp (Function.Bijective.comp ?_ (Equiv.bijective _))
    exact Function.bijective_iff_has_inverse.2
      ⟨fun g => inv ((tensorHomComparisonDerived X R K L).app Z) ≫ g, fun g => by simp,
        fun g => by simp⟩
  exact NatIso.isIso_of_isIso_app _

end Detection

end AlgebraicGeometry.RingedSite

end
