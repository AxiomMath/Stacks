module

public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedClasses

/-!
# The comparison `Lg^* ⟶ g^*` commutes with the shift

Let `g : (Sh(𝒟), 𝒪_𝒟) ⟶ (Sh(𝒞), 𝒪_𝒞)` be a morphism of ringed topoi. The comparison
`Lg^*K ⟶ g^*K` of the derived pullback with the degreewise pullback of a complex of
`𝒪_𝒞`-modules (Stacks 06YY) is compatible with the shift functors: the derived pullback commutes
with the shift as a total left derived functor, its counit is compatible with that commutation,
and degreewise pullback commutes with the shift on the nose. On a module `ℱ` placed in degree
`n`, the comparison `Lg^*(ℱ[-n]) ⟶ (g^*ℱ)[-n]` is therefore the shift of the comparison in
degree `0`; this is how `Lg^*` of an `Ext`-class of the proof of **Stacks 0GQ7**, written as a
chain map followed by the shift isomorphism of the single functors, is computed.

## Main definitions

* `Deformation.ToposThickening.LiftingMorphismDerived.derivedPullbackSingleObjAt`: the
  comparison `Lg^*(ℱ[-n]) ⟶ (g^*ℱ)[-n]` for a module `ℱ` placed in degree `n`.

## Main results

* `.derivedPullbackComparisonNat_commShift`: the comparison `Q ⋙ Lg^* ⟶ g^* ⋙ Q` commutes with
  the shift.
* `.derivedPullback_map_shiftIso_inv_comp`: the comparison in degree `-1` is the shift of the
  comparison in degree `0`, through the shift isomorphism of the single functors.

## References

* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Cohomology.DerivedPullbackOfToposHom

universe u v' u' w'

attribute [local instance 10000] HasDerivedCategory.standard

namespace Deformation.ToposThickening.LiftingMorphismDerived

/-! ### Degreewise functors commute with the shift and with the single functors -/

section Degreewise

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- A natural transformation of additive functors induces, on cochain complexes, a natural
transformation compatible with the shift. -/
instance natTrans_mapHomologicalComplex_commShift {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) : NatTrans.CommShift (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)) ℤ :=
  ⟨fun n => by
    ext K i
    simp [NatTrans.mapHomologicalComplex, CochainComplex.shiftFunctor_map_f']⟩

/-- A natural isomorphism of additive functors induces, on cochain complexes, a natural
isomorphism whose forward direction is compatible with the shift. -/
instance natIso_mapHomologicalComplex_commShift {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ≅ G) : NatTrans.CommShift (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).hom ℤ :=
  natTrans_mapHomologicalComplex_commShift α.hom

variable [HasZeroObject C] [HasZeroObject D]

/-- On cochain complexes, the identification of the degreewise image of a single complex with a
single complex is compatible with the shift isomorphisms of the single functors. -/
theorem map_singleFunctors_shiftIso_inv_app (F : C ⥤ D) [F.Additive] (n a a' : ℤ)
    (h : n + a = a') (M : C) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((CochainComplex.singleFunctors C).shiftIso n a a' h).inv.app M) ≫
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) a').obj M) ≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) a').hom.app M)⟦n⟧' =
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) a).hom.app M ≫
      ((CochainComplex.singleFunctors D).shiftIso n a a' h).inv.app (F.obj M) := by
  obtain rfl : a' = a + n := by lia
  ext i
  by_cases hi : i = a
  · subst hi
    simp [CochainComplex.singleFunctors, HomologicalComplex.singleMapHomologicalComplex,
      CochainComplex.shiftFunctor_map_f', eqToHom_map]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (a + n) (F.obj M) (i + n)
      (by lia)).eq_of_tgt _ _

/-- A natural transformation `τ : Q₁ ⋙ L ⟶ G ⋙ Q₂` compatible with the shift carries a square
relating a morphism `s : K' ⟶ K⟦n⟧` to a morphism `s' : M' ⟶ M⟦n⟧` through `G` to the
corresponding square after `Q₁ ⋙ L` and `Q₂`. -/
theorem shift_app_comm_of_comp {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂] [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
    (Q₁ : C₁ ⥤ D₁) (L : D₁ ⥤ D₂) (G : C₁ ⥤ C₂) (Q₂ : C₂ ⥤ D₂) [Q₁.CommShift ℤ] [L.CommShift ℤ]
    [G.CommShift ℤ] [Q₂.CommShift ℤ] (τ : Q₁ ⋙ L ⟶ G ⋙ Q₂) [NatTrans.CommShift τ ℤ] (n : ℤ)
    {K K' : C₁} {M M' : C₂} (s : K' ⟶ K⟦n⟧) (m : G.obj K ⟶ M) (m' : G.obj K' ⟶ M')
    (s' : M' ⟶ M⟦n⟧) (h : G.map s ≫ (G.commShiftIso n).hom.app K ≫ m⟦n⟧' = m' ≫ s') :
    L.map (Q₁.map s ≫ (Q₁.commShiftIso n).hom.app K) ≫ (L.commShiftIso n).hom.app (Q₁.obj K) ≫
        (τ.app K ≫ Q₂.map m)⟦n⟧' =
      (τ.app K' ≫ Q₂.map m') ≫ Q₂.map s' ≫ (Q₂.commShiftIso n).hom.app M := by
  have key := NatTrans.shift_app_comm τ n K
  have nat := τ.naturality s
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, Category.assoc] at key nat
  calc _ = L.map (Q₁.map s) ≫ (L.map ((Q₁.commShiftIso n).hom.app K) ≫
          (L.commShiftIso n).hom.app (Q₁.obj K) ≫ (τ.app K)⟦n⟧') ≫ (Q₂.map m)⟦n⟧' := by
        simp
    _ = (L.map (Q₁.map s) ≫ τ.app (K⟦n⟧)) ≫ Q₂.map ((G.commShiftIso n).hom.app K) ≫
          (Q₂.commShiftIso n).hom.app (G.obj K) ≫ (Q₂.map m)⟦n⟧' := by
        rw [key]
        simp
    _ = τ.app K' ≫ Q₂.map (G.map s ≫ (G.commShiftIso n).hom.app K ≫ m⟦n⟧') ≫
          (Q₂.commShiftIso n).hom.app M := by
        rw [nat]
        simp [Functor.commShiftIso_hom_naturality]
    _ = _ := by
        rw [h]
        simp

/-- The shift isomorphism of the single functors to the derived category, read through the
shift isomorphism of the single functors to cochain complexes. -/
theorem singleFunctors_shiftIso_inv_app {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (n a a' : ℤ) (h : n + a = a') (M : C) :
    ((DerivedCategory.singleFunctors C).shiftIso n a a' h).inv.app M =
      DerivedCategory.Q.map (((CochainComplex.singleFunctors C).shiftIso n a a' h).inv.app M) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app _ := by
  simp [DerivedCategory.singleFunctors]

end Degreewise

/-! ### The comparison on single complexes induced by a comparison on complexes -/

section SingleComparison

variable {C C' : Type*} [Category* C] [Category* C'] [Abelian C] [Abelian C']
  [HasDerivedCategory C] [HasDerivedCategory C']
  (L : DerivedCategory C ⥤ DerivedCategory C') (Φ : C ⥤ C') [Φ.Additive]
  (τ : DerivedCategory.Q ⋙ L ⟶ Φ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

/-- The comparison `singleObjComparison L Φ τ n M` is the component of `τ` at the single complex
on `M` in degree `n`, followed by the image under `Q` of the identification of the degreewise
image of that single complex with the single complex on `Φ.obj M`. -/
theorem singleObjComparison_eq (n : ℤ) (M : C) :
    singleObjComparison L Φ τ n M =
      τ.app ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) n).hom.app M) := by
  simp [singleObjComparison, DerivedCategory.singleFunctorIsoCompQ]

/-- **The comparison on single objects is compatible with the shift isomorphisms of the single
functors**, when `τ` commutes with the shift. -/
theorem map_singleFunctors_shiftIso_inv_app_comp_singleObjComparison [L.CommShift ℤ]
    [NatTrans.CommShift τ ℤ] (n a a' : ℤ) (h : n + a = a') (M : C) :
    L.map (((DerivedCategory.singleFunctors C).shiftIso n a a' h).inv.app M) ≫
        (L.commShiftIso n).hom.app ((DerivedCategory.singleFunctor C a').obj M) ≫
        (singleObjComparison L Φ τ a' M)⟦n⟧' =
      singleObjComparison L Φ τ a M ≫
        ((DerivedCategory.singleFunctors C').shiftIso n a a' h).inv.app (Φ.obj M) := by
  rw [singleFunctors_shiftIso_inv_app, singleFunctors_shiftIso_inv_app, singleObjComparison_eq,
    singleObjComparison_eq]
  exact shift_app_comm_of_comp DerivedCategory.Q L (Φ.mapHomologicalComplex (ComplexShape.up ℤ))
    DerivedCategory.Q τ n _ _ _ _ (map_singleFunctors_shiftIso_inv_app Φ n a a' h M)

end SingleComparison

variable {X Y : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The comparison commutes with the shift -/

section Shift

variable (g : RingedToposHom Y X)

/-- The counit `Lg^* ∘ Qh ⟶ Qh ∘ g^*` of the derived pullback is compatible with the
commutation of `Lg^*` with the shift (Stacks 06YY). -/
instance derivedPullbackComparison_commShift :
    NatTrans.CommShift (derivedPullbackComparison g) ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift_compatibility (derivedPullback g)
    (derivedPullbackComparison g) _ ℤ

/-- `derivedPullbackComparisonNat` with its associators spelled out between the functors they
relate: in the definition the elaborator reads `quotient ⋙ g^*` where `g^* ⋙ quotient` is meant
(the two agree up to `mapHomotopyCategoryFactors`), which hides the shift structures of the
intermediate functors. -/
theorem derivedPullbackComparisonNat_eq_comp :
    derivedPullbackComparisonNat g =
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv (derivedPullback g) ≫
        (Functor.associator (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) DerivedCategory.Qh
          (derivedPullback g)).hom ≫
        Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (derivedPullbackComparison g) ≫
        (Functor.associator (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (g.toModulesHom.pullbackModules.mapHomotopyCategory (ComplexShape.up ℤ))
          DerivedCategory.Qh).inv ≫
        Functor.whiskerRight
          (g.toModulesHom.pullbackModules.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
          DerivedCategory.Qh ≫
        (Functor.associator
          (g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ))
          (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) DerivedCategory.Qh).hom ≫
        Functor.whiskerLeft
          (g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso _).hom ≫
        Functor.whiskerRight (NatIso.mapHomologicalComplex (pullbackModulesIso g)
          (ComplexShape.up ℤ)).hom DerivedCategory.Q :=
  rfl

/-- The composite `derivedPullbackComparisonNat_eq_comp` commutes with the shift: each factor
does. -/
theorem derivedPullbackComparisonNat_commShift_aux :
    NatTrans.CommShift (Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
          (derivedPullback g) ≫
        (Functor.associator (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) DerivedCategory.Qh
          (derivedPullback g)).hom ≫
        Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (derivedPullbackComparison g) ≫
        (Functor.associator (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (g.toModulesHom.pullbackModules.mapHomotopyCategory (ComplexShape.up ℤ))
          DerivedCategory.Qh).inv ≫
        Functor.whiskerRight
          (g.toModulesHom.pullbackModules.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom
          DerivedCategory.Qh ≫
        (Functor.associator
          (g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ))
          (HomotopyCategory.quotient _ (ComplexShape.up ℤ)) DerivedCategory.Qh).hom ≫
        Functor.whiskerLeft
          (g.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso _).hom ≫
        Functor.whiskerRight (NatIso.mapHomologicalComplex (pullbackModulesIso g)
          (ComplexShape.up ℤ)).hom DerivedCategory.Q) ℤ := by
  iterate 7
    refine @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ ?_ ?_
    · infer_instance
  infer_instance

/-- **The comparison `Q ⋙ Lg^* ⟶ g^* ⋙ Q` commutes with the shift.** -/
instance derivedPullbackComparisonNat_commShift :
    NatTrans.CommShift (derivedPullbackComparisonNat g) ℤ := by
  rw [derivedPullbackComparisonNat_eq_comp]
  exact derivedPullbackComparisonNat_commShift_aux g

end Shift

/-! ### Modules placed in an arbitrary degree -/

section Single

variable (g : RingedToposHom Y X)

/-- **The comparison `Lg^*(ℱ[-n]) ⟶ (g^*ℱ)[-n]`** of the derived with the degreewise pullback on
a module placed in degree `n`: the recipe of `derivedPullbackSingleObj`, in degree `n`. -/
def derivedPullbackSingleObjAt (n : ℤ)
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (derivedPullback g).obj ((DerivedCategory.singleFunctor _ n).obj F) ⟶
      (DerivedCategory.singleFunctor _ n).obj (g.toRingedToposModulesHom.pullbackModules.obj F) :=
  singleObjComparison (derivedPullback g) g.toRingedToposModulesHom.pullbackModules
    (derivedPullbackComparisonNat g) n F

/-- **The comparison on a module placed in degree `a` is the shift of the comparison in degree
`a' = n + a`**, through the shift isomorphisms `(ℱ[-a'])[n] ≅ ℱ[-a]` of the single functors and
the commutation of `Lg^*` with the shift. -/
theorem derivedPullback_map_singleFunctors_shiftIso_inv_app (n a a' : ℤ) (h : n + a = a')
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (derivedPullback g).map (((DerivedCategory.singleFunctors _).shiftIso n a a' h).inv.app F) ≫
        ((derivedPullback g).commShiftIso n).hom.app ((DerivedCategory.singleFunctor _ a').obj F) ≫
        (derivedPullbackSingleObjAt g a' F)⟦n⟧' =
      derivedPullbackSingleObjAt g a F ≫
        ((DerivedCategory.singleFunctors _).shiftIso n a a' h).inv.app
          (g.toRingedToposModulesHom.pullbackModules.obj F) :=
  map_singleFunctors_shiftIso_inv_app_comp_singleObjComparison _ _ _ n a a' h F

/-- **The comparison in degree `-1` is the shift of the comparison in degree `0`**: through the
shift isomorphism `ℱ[1] ≅ (ℱ[0])[1]` of the single functors and the commutation of `Lg^*` with
the shift, the comparison `Lg^*(ℱ[1]) ⟶ (g^*ℱ)[1]` is `(Lg^*(ℱ[0]) ⟶ (g^*ℱ)[0])[1]`. -/
theorem derivedPullback_map_shiftIso_inv_comp
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (derivedPullback g).map
        (((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app F) ≫
      ((derivedPullback g).commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj F) ≫
      (derivedPullbackSingleObjAt g 0 F)⟦(1 : ℤ)⟧' =
    derivedPullbackSingleObjAt g (-1) F ≫
      ((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0 (by decide)).inv.app
        (g.toRingedToposModulesHom.pullbackModules.obj F) :=
  derivedPullback_map_singleFunctors_shiftIso_inv_app g 1 (-1) 0 (by decide) F

/-- The comparison in degree `0` is `derivedPullbackSingleObj`. -/
theorem derivedPullbackSingleObjAt_zero
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    derivedPullbackSingleObjAt g 0 F = derivedPullbackSingleObj g F :=
  rfl

end Single

end Deformation.ToposThickening.LiftingMorphismDerived

end
