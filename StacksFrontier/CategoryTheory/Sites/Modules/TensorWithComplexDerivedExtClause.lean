module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorHomotopyCommShift
public import StacksFrontier.CategoryTheory.CancelRetraction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomDegreeTransport
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedHom
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of Tag 0CS6 on cohomology is the map induced on `Ext`

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. The canonical
map of Tag 0CS6,

`RHom(M, N) ⟶ RHom_O(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K)`,

is `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived`, and the two cohomology
modules it compares are identified with the `Ext`-groups `Ext^n_{D(E, d)}(M, N)` and
`Ext^n_{D(O)}(M ⊗_E^𝐋 K, N ⊗_E^𝐋 K)`. The degree-`n` cohomology of the canonical map is the map on
`Ext` induced by `- ⊗_E^𝐋 K`, for every `M`, `N` in `D(E, d)` and every `n`, with no further
hypothesis. The identification is read in `D(ℤ) = D(Ab)`: the objects are formed over the base
ring `R`, but the canonical map has the scalars of its source and target forgotten.

## Main results

* `AlgebraicGeometry.RingedSite.localizationHomAddHom_comp_commShiftIso`: the localization
  functor on morphism groups, followed by the commutation of `K(O) ⥤ D(O)` with the translation,
  written through `CategoryTheory.DerivedCategory.Qh`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy_commShiftIso_hom_app` and
  `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_commShiftIso_hom_app`: the
  commutations with the translation of the functor of Tag 09LW and of the functor being derived
  in Tag 09LX, at the class of a differential graded module.
* `AlgebraicGeometry.RingedSite.localizationHomAddHom_tensorWithComplexHomotopy`: the sheaf-side
  localization `K(O) ⥤ D(O)` applied to the image of a homotopy class under the functor of
  Tag 09LW is the differential-graded-side map on `Ext` of
  `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategoryExtMap`, conjugated by
  `CategoryTheory.DerivedCategory.quotientCompQhIso`.
* `AlgebraicGeometry.RingedSite.repIso_hom_comp_quotientCompQhIso_inv` and
  `AlgebraicGeometry.RingedSite.counit_comp_quotientCompQhIso_hom_comp_repIso_inv`: the two legs
  of `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso` against that same comparison.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived_homology`: the degree-`n`
  cohomology of the canonical map of Tag 0CS6 is the map on `Ext` induced by `- ⊗_E^𝐋 K`.

## References

* [Stacks Project, Tag 0CS6](https://stacks.math.columbia.edu/tag/0CS6)
* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u o

attribute [local instance] HasDerivedCategory.standard

/-! ### Rearrangements of composites in a category -/

/-- Substituting a factorisation of the second factor of a composite of three. -/
private theorem comp_bridge {C : Type*} [Category C] {W₀ W₁ W₂ W₃ W₄ : C}
    (P : W₀ ⟶ W₁) (R : W₁ ⟶ W₂) (S : W₂ ⟶ W₃) (U : W₃ ⟶ W₄) {V : W₀ ⟶ W₂} (hV : P ≫ R = V)
    {Z : W₁ ⟶ W₄} (hZ : Z = R ≫ S ≫ U) :
    P ≫ Z = (V ≫ S) ≫ U := by
  subst hV hZ
  rw [Category.assoc, Category.assoc]

/-- The companion of `AlgebraicGeometry.RingedSite.comp_bridge` with a functor applied to the
first two factors. -/
private theorem map_comp_bridge {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {W₀ W₁ W₂ : C} (P : W₀ ⟶ W₁) (Y : W₁ ⟶ W₂) {V : W₀ ⟶ W₂} (hV : P ≫ Y = V)
    {E : D} {Z : G.obj W₁ ⟶ E} (W : G.obj W₂ ⟶ E) (hZ : Z = G.map Y ≫ W) :
    G.map P ≫ Z = G.map V ≫ W := by
  subst hV hZ
  rw [Functor.map_comp, Category.assoc]

/-- Reassociating against a factorisation of the middle factor of a composite of three. -/
private theorem comp_assoc_bridge {C : Type*} [Category C] {W₀ W₁ W₂ W₃ W₄ : C}
    (f : W₀ ⟶ W₁) {α : W₁ ⟶ W₃} (β : W₁ ⟶ W₂) (γ : W₂ ⟶ W₃) (δ : W₃ ⟶ W₄) (h : α = β ≫ γ) :
    f ≫ β ≫ γ ≫ δ = f ≫ α ≫ δ := by
  subst h
  rw [Category.assoc]

/-- Cancelling two inverses out of the middle of a composite. -/
private theorem comp_cancel_middle {C : Type*} [Category C] {W₀ W₁ W₂ W₃ : C}
    (g : W₀ ⟶ W₁) (h : W₁ ⟶ W₂) (k : W₂ ⟶ W₁) (g' : W₁ ⟶ W₀) (m : W₀ ⟶ W₃)
    (hhk : h ≫ k = 𝟙 W₁) (hgg : g ≫ g' = 𝟙 W₀) :
    g ≫ h ≫ (k ≫ g') ≫ m = m := by
  simp [reassoc_of% hhk, reassoc_of% hgg]

/-- Applying the image under an `AddCommGrpCat`-valued functor to an element, split along a
composite. -/
private theorem functor_map_comp_apply {C : Type*} [Category C] {W₀ W₁ W₂ : C}
    (G : C ⥤ AddCommGrpCat.{u}) (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂) (x : ↥(G.obj W₀)) :
    G.map (f ≫ g) x = G.map g (G.map f x) := by
  rw [G.map_comp]
  rfl

/-- Four factorisations `hlam`, `hrh`, `htau` and `hkap` of composites chain into the identity
`rh ≫ lam ≫ G.map rn = (a ≫ e) ≫ G.map d`. -/
private theorem assemble {C : Type*} [Category C] (G : C ⥤ C) {V₀ V₁ V₂ V₃ V₄ V₅ V₆ V₇ : C}
    (rh : V₀ ⟶ V₁) (lam : V₁ ⟶ G.obj V₂) (rn : V₂ ⟶ V₃)
    (iota : V₁ ⟶ V₄) (tau : V₄ ⟶ G.obj V₅) (kap : V₅ ⟶ V₂)
    (a : V₀ ⟶ V₆) (b : V₆ ⟶ V₄) (e : V₆ ⟶ G.obj V₇) (c : V₇ ⟶ V₅) (d : V₇ ⟶ V₃)
    (hlam : lam = iota ≫ tau ≫ G.map kap) (hrh : rh ≫ iota = a ≫ b)
    (htau : b ≫ tau = e ≫ G.map c) (hkap : c ≫ kap ≫ rn = d) :
    rh ≫ lam ≫ G.map rn = (a ≫ e) ≫ G.map d := by
  subst hlam hkap
  simp only [Category.assoc, Functor.map_comp, reassoc_of% hrh, reassoc_of% htau]

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})

/-! ### The localization map on morphism groups against the translation -/

/-- **The localization functor on morphism groups, followed by the commutation of `K(O) ⥤ D(O)`
with the translation.** For a homotopy class `γ : A ⟶ B[n]` of morphisms of complexes of
`O`-modules, the class of `γ` in `D(O)`, read into `Hom_{D(O)}(Q A, (Q B)[n])`, is the image of
`γ` under `CategoryTheory.DerivedCategory.Qh` conjugated by
`CategoryTheory.DerivedCategory.quotientCompQhIso`, with the translation moved across by the
commutations of the homotopy quotient functor and of `Qh`. -/
theorem localizationHomAddHom_comp_commShiftIso
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (γ : (HomotopyCategory.quotient
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)).obj A ⟶
      (HomotopyCategory.quotient
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).obj
        (B⟦n⟧)) :
    localizationHomAddHom X A (B⟦n⟧) γ ≫ (DerivedCategory.Q.commShiftIso n).hom.app B =
      (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inv.app A ≫
        DerivedCategory.Qh.map (γ ≫
            ((HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              (ComplexShape.up ℤ)).commShiftIso n).hom.app B) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app
              ((HomotopyCategory.quotient
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
                (ComplexShape.up ℤ)).obj B) ≫
            ((DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
                B)⟦n⟧' := by
  rw [localizationHomAddHom_apply]
  simp only [Iso.app_hom, Iso.app_inv, Category.assoc, Functor.map_comp]
  rw [← NatTrans.shift_app_comm
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom n B,
    Functor.commShiftIso_comp_hom_app]
  simp only [Category.assoc]

variable (R : Type o) [CommRing R] [Linear R (TensorModO.{u, u, u, u, u} X)]
  [ScalarSections.{u, u, u, u, u, o} X R]
  (K : CochainComplex (ModO.{u, u, u, u} X) ℤ)

/-! ### The comparison of the two localizations -/

/-- **The commutation of the functor of Tag 09LW with the translation**, at the class of a
differential graded module: it is the comparison `(N[n]) ⊗_E K ≅ (N ⊗_E K)[n]` of
`DifferentialGradedModule.dgFunctorToComplexesShiftIso`, conjugated by the commutations of the
two homotopy quotient functors with the translation. -/
theorem tensorWithComplexHomotopy_commShiftIso_hom_app
    (N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) (n : ℤ) :
    ((tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).commShiftIso n).hom.app
        ((DifferentialGradedModule.toHomotopyCategory
          (Rep.{u, u, u, u, u, o} X R K).algebra).obj N) =
      (tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).map
          (((DifferentialGradedModule.toHomotopyCategory
            (Rep.{u, u, u, u, u, o} X R K).algebra).commShiftIso n).inv.app N) ≫
        (HomotopyCategory.quotient (TensorModO.{u, u, u, u, u} X) (ComplexShape.up ℤ)).map
            (DifferentialGradedModule.dgFunctorToComplexesShiftIso
              (tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor N n).hom ≫
          ((HomotopyCategory.quotient (TensorModO.{u, u, u, u, u} X)
              (ComplexShape.up ℤ)).commShiftIso n).hom.app
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N) :=
  DifferentialGradedModule.dgFunctorToHomotopyCategory_commShiftIso_hom_app _ N n

/-- **The commutation with the translation of the functor being derived in Tag 09LX.** That
functor is tensoring with `K` on homotopy categories followed by
`CategoryTheory.DerivedCategory.Qh`, by definition, so its commutation with the translation
splits into the two factors. -/
theorem tensorWithComplexToDerivedCategory_commShiftIso_hom_app
    (Y : DifferentialGradedModule.HomotopyCategory.{o, u, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra) (n : ℤ) :
    ((tensorWithComplexToDerivedCategory.{u, u, u, u, u, o} X R K).commShiftIso n).hom.app Y =
      DerivedCategory.Qh.map
          (((tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).commShiftIso n).hom.app Y) ≫
        (DerivedCategory.Qh.commShiftIso n).hom.app
          ((tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).obj Y) :=
  Functor.commShiftIso_comp_hom_app _ _ n Y

/-- **The two localizations of Tag 0CS6 agree.** The sheaf side uses the localization
`K(O) ⥤ D(O)` of `AlgebraicGeometry.RingedSite.localizationHomAddHom`, applied to the image
under the functor of Tag 09LW of a morphism `c : [M] ⟶ [N[n]]` of `K(E, d)` composed with the
comparison `DifferentialGradedModule.dgFunctorToComplexesShiftIso`; the differential graded side
uses `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategoryExtMap`. The two agree,
after the transport of `c` along the equality of objects of Tag 09LC's identification, up to the
comparison `CategoryTheory.DerivedCategory.quotientCompQhIso` of the two localizations of the
category of complexes. -/
theorem localizationHomAddHom_tensorWithComplexHomotopy
    (M N : (DifferentialGradedModule.dgCategory.{_, _, u}
      (Rep.{u, u, u, u, u, o} X R K).algebra).Obj) (n : ℤ)
    (c : (DifferentialGradedModule.toHomotopyCategory
        (Rep.{u, u, u, u, u, o} X R K).algebra).obj M ⟶
      (DifferentialGradedModule.toHomotopyCategory (Rep.{u, u, u, u, u, o} X R K).algebra).obj
        (DifferentialGradedModule.shift N n)) :
    localizationHomAddHom X ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M)
          (((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N)⟦n⟧)
          ((tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).map c ≫
            (HomotopyCategory.quotient (TensorModO.{u, u, u, u, u} X)
              (ComplexShape.up ℤ)).map
              (DifferentialGradedModule.dgFunctorToComplexesShiftIso
                (tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor N n).hom) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N) =
      (DerivedCategory.quotientCompQhIso (TensorModO.{u, u, u, u, u} X)).inv.app
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj M) ≫
        tensorWithComplexToDerivedCategoryExtMap.{u, u, u, u, u, o} X R K n
            (DifferentialGradedModule.General.homAddEquivOfEq
              (DifferentialGradedModule.General.toHomotopyCategory_obj_shift
                (Rep.{u, u, u, u, u, o} X R K).algebra N n) c) ≫
          ((DerivedCategory.quotientCompQhIso (TensorModO.{u, u, u, u, u} X)).hom.app
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N))⟦n⟧' := by
  have hc : (tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).map
          (DifferentialGradedModule.General.homAddEquivOfEq
            (DifferentialGradedModule.General.toHomotopyCategory_obj_shift
              (Rep.{u, u, u, u, u, o} X R K).algebra N n) c) ≫
        ((tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).commShiftIso n).hom.app
          ((DifferentialGradedModule.toHomotopyCategory
            (Rep.{u, u, u, u, u, o} X R K).algebra).obj N) =
      ((tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).map c ≫
          (HomotopyCategory.quotient (TensorModO.{u, u, u, u, u} X) (ComplexShape.up ℤ)).map
            (DifferentialGradedModule.dgFunctorToComplexesShiftIso
              (tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor N n).hom) ≫
        ((HomotopyCategory.quotient (TensorModO.{u, u, u, u, u} X)
            (ComplexShape.up ℤ)).commShiftIso n).hom.app
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N) :=
    comp_bridge _ _ _ _
      ((((tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K)).map_comp _ _).symm.trans
        (congrArg (fun z => (tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).map z)
          (DifferentialGradedModule.General.homAddEquivOfEq_comp_commShiftIso_inv n c)))
      (tensorWithComplexHomotopy_commShiftIso_hom_app X R K N n)
  have hd : DerivedCategory.Qh.map ((tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).map
          (DifferentialGradedModule.General.homAddEquivOfEq
            (DifferentialGradedModule.General.toHomotopyCategory_obj_shift
              (Rep.{u, u, u, u, u, o} X R K).algebra N n) c)) ≫
        ((tensorWithComplexToDerivedCategory.{u, u, u, u, u, o} X R K).commShiftIso n).hom.app
          ((DifferentialGradedModule.toHomotopyCategory
            (Rep.{u, u, u, u, u, o} X R K).algebra).obj N) =
      DerivedCategory.Qh.map
          (((tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).map c ≫
              (HomotopyCategory.quotient (TensorModO.{u, u, u, u, u} X)
                (ComplexShape.up ℤ)).map
                (DifferentialGradedModule.dgFunctorToComplexesShiftIso
                  (tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor N n).hom) ≫
            ((HomotopyCategory.quotient (TensorModO.{u, u, u, u, u} X)
                (ComplexShape.up ℤ)).commShiftIso n).hom.app
              ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N)) ≫
        (DerivedCategory.Qh.commShiftIso n).hom.app
          ((HomotopyCategory.quotient (TensorModO.{u, u, u, u, u} X) (ComplexShape.up ℤ)).obj
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj N)) :=
    map_comp_bridge DerivedCategory.Qh _ _ hc _
      (tensorWithComplexToDerivedCategory_commShiftIso_hom_app X R K
        ((DifferentialGradedModule.toHomotopyCategory
          (Rep.{u, u, u, u, u, o} X R K).algebra).obj N) n)
  have hextmap : tensorWithComplexToDerivedCategoryExtMap.{u, u, u, u, u, o} X R K n
        (DifferentialGradedModule.General.homAddEquivOfEq
          (DifferentialGradedModule.General.toHomotopyCategory_obj_shift
            (Rep.{u, u, u, u, u, o} X R K).algebra N n) c) =
      DerivedCategory.Qh.map ((tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).map
          (DifferentialGradedModule.General.homAddEquivOfEq
            (DifferentialGradedModule.General.toHomotopyCategory_obj_shift
              (Rep.{u, u, u, u, u, o} X R K).algebra N n) c)) ≫
        ((tensorWithComplexToDerivedCategory.{u, u, u, u, u, o} X R K).commShiftIso n).hom.app
          ((DifferentialGradedModule.toHomotopyCategory
            (Rep.{u, u, u, u, u, o} X R K).algebra).obj N) := rfl
  rw [localizationHomAddHom_comp_commShiftIso, hextmap]
  exact comp_assoc_bridge _ _ _ _ hd

/-! ### The representative isomorphism against the comparison of the two localizations -/

/-- **The contravariant leg of the representative isomorphism.** The trailing comparison
`CategoryTheory.DerivedCategory.quotientCompQhIso` of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso` is cancelled by the inverse of the
same comparison that `AlgebraicGeometry.RingedSite.localizationHomAddHom` carries, leaving the
action of `- ⊗_E^𝐋 K` on `DifferentialGradedModule.propertyPModelIso` followed by the comparison
of Tag 09LX. -/
theorem repIso_hom_comp_quotientCompQhIso_inv
    (M : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra) :
    (tensorWithComplexDerivedRepIso.{u, o} X R K M).hom ≫
        (DerivedCategory.quotientCompQhIso (TensorModO.{u, u, u, u, u} X)).inv.app
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M)) =
      (tensorWithComplexDerived.{u, u, u, u, u, o} X R K).map
          (DifferentialGradedModule.propertyPModelIso.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M).inv ≫
        (tensorWithComplexDerivedCounit.{u, u, u, u, u, o} X R K).app
          ((DifferentialGradedModule.toHomotopyCategory
              (Rep.{u, u, u, u, u, o} X R K).algebra).obj
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M)) :=
  comp_comp_cancel_right _ _ _ _
    (Iso.hom_inv_id_app (DerivedCategory.quotientCompQhIso (TensorModO.{u, u, u, u, u} X))
      ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M)))

/-- **The covariant leg of the representative isomorphism.** Preceded by the comparison of
Tag 09LX, the inverse of `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedRepIso` read
after the comparison `CategoryTheory.DerivedCategory.quotientCompQhIso` is the action of
`- ⊗_E^𝐋 K` on `DifferentialGradedModule.propertyPModelIso`: both comparisons cancel forwards,
so no inverse of the comparison of Tag 09LX occurs. -/
theorem counit_comp_quotientCompQhIso_hom_comp_repIso_inv
    (M : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra) :
    (tensorWithComplexDerivedCounit.{u, u, u, u, u, o} X R K).app
          ((DifferentialGradedModule.toHomotopyCategory
              (Rep.{u, u, u, u, u, o} X R K).algebra).obj
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M)) ≫
        (DerivedCategory.quotientCompQhIso (TensorModO.{u, u, u, u, u} X)).hom.app
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M)) ≫
          (tensorWithComplexDerivedRepIso.{u, o} X R K M).inv =
      (tensorWithComplexDerived.{u, u, u, u, u, o} X R K).map
        (DifferentialGradedModule.propertyPModelIso.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M).hom := by
  have := isIso_tensorWithComplexDerivedCounit_app_of_propertyP.{u, u, u, u, u, o} X R K
    (DifferentialGradedModule.propertyPFiltration_propertyPModel.{o, u, 0}
      (Rep.{u, u, u, u, u, o} X R K).algebra M)
  exact comp_cancel_middle _ _ _ _ _
    (Iso.hom_inv_id_app (DerivedCategory.quotientCompQhIso (TensorModO.{u, u, u, u, u} X))
      ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M)))
    (IsIso.hom_inv_id ((tensorWithComplexDerivedCounit.{u, u, u, u, u, o} X R K).app
      ((DifferentialGradedModule.toHomotopyCategory
          (Rep.{u, u, u, u, u, o} X R K).algebra).obj
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M))))

/-! ### The central clause of Tag 0CS6 -/

/-- `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived_homology` at a
cohomology class `η` presented as the class of a closed degree-`n` homogeneous morphism `f`. -/
private theorem tensorWithComplexDerivedHomMapDerived_homology_aux
    (M N : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra) (n : ℤ)
    (η : ↥((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      (DerivedCategory.Q.obj ((DifferentialGradedModule.dgCategory.{_, _, u}
          (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M)
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra N)))))
    (f : ↥(AddCommGrpCat.Hom.hom (DifferentialGradedModule.General.homSc
      (Rep.{u, u, u, u, u, o} X R K).algebra
      (DifferentialGradedModule.propertyPModel.{o, u, 0} (Rep.{u, u, u, u, u, o} X R K).algebra M)
      (DifferentialGradedModule.propertyPModel.{o, u, 0}
        (Rep.{u, u, u, u, u, o} X R K).algebra N) n).g).ker)
    (hη : ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
          ((DifferentialGradedModule.dgCategory.{_, _, u}
              (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M)
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N))).hom η =
      (DifferentialGradedModule.General.homScHomologyEquiv
          (Rep.{u, u, u, u, u, o} X R K).algebra
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M)
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N) n).symm (QuotientAddGroup.mk f)) :
    tensorWithComplexDerivedHomTargetExtEquiv.{u, o} X R K M N n
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          (tensorWithComplexDerivedHomMapDerived.{u, o} X R K M N) η) =
      tensorWithComplexDerivedExtMap.{u, u, u, u, u, o} X R K n
        (tensorWithComplexDerivedHomSourceExtEquiv.{u, o} X R K M N n η) := by
  let := tensorModOHasBinaryBiproducts.{u, u, u, u, u} X
  have hmd : tensorWithComplexDerivedHomMapDerived.{u, o} X R K M N =
      (DerivedCategory.Q.map (tensorWithComplexHomComplexMap.{u, o} X R K
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M)
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N)) ≫
          homComplexToGlobalDerivedHom X
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M))
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra N))) ≫
        (derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map
              (tensorWithComplexDerivedRepIso.{u, o} X R K M).hom.op).app
              (DerivedCategory.Q.obj ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
                (DifferentialGradedModule.propertyPModel.{o, u, 0}
                  (Rep.{u, u, u, u, u, o} X R K).algebra N))) ≫
            ((derivedSheafHomBifunctor X).obj
                (op ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M))).map
              (tensorWithComplexDerivedRepIso.{u, o} X R K N).inv) := by
    rw [Functor.map_comp]
    rfl
  have hsplit : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        (tensorWithComplexDerivedHomMapDerived.{u, o} X R K M N) η =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map
              (tensorWithComplexDerivedRepIso.{u, o} X R K M).hom.op).app
              (DerivedCategory.Q.obj ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
                (DifferentialGradedModule.propertyPModel.{o, u, 0}
                  (Rep.{u, u, u, u, u, o} X R K).algebra N))) ≫
            ((derivedSheafHomBifunctor X).obj
                (op ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M))).map
              (tensorWithComplexDerivedRepIso.{u, o} X R K N).inv))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          (homComplexToGlobalDerivedHom X
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M))
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra N)))
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
            (DerivedCategory.Q.map (tensorWithComplexHomComplexMap.{u, o} X R K
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M)
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra N))) η)) := by
    rw [hmd]
    exact (functor_map_comp_apply (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n) _ _ η).trans
      (congrArg (fun z => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map _ z)
        (functor_map_comp_apply (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n) _ _ η))
  have htgt := globalDerivedHomDegreeEquiv_naturality X
    (tensorWithComplexDerivedRepIso.{u, o} X R K M).hom
    (tensorWithComplexDerivedRepIso.{u, o} X R K N).inv n
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
      (homComplexToGlobalDerivedHom X
        ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M))
        ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        (DerivedCategory.Q.map (tensorWithComplexHomComplexMap.{u, o} X R K
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M)
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N))) η))
  have hin1 : globalDerivedHomDegreeEquiv X
        (DerivedCategory.Q.obj ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M)))
        (DerivedCategory.Q.obj ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N))) n
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          (homComplexToGlobalDerivedHom X
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M))
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra N)))
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
            (DerivedCategory.Q.map (tensorWithComplexHomComplexMap.{u, o} X R K
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M)
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra N))) η)) =
      localizationHomAddHom X
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M))
          (((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N))⟦n⟧)
          (homComplexHomologyAddEquiv
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M))
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra N)) n
            (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
              (((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
                  (DifferentialGradedModule.propertyPModel.{o, u, 0}
                    (Rep.{u, u, u, u, u, o} X R K).algebra M)).HomComplex
                ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
                  (DifferentialGradedModule.propertyPModel.{o, u, 0}
                    (Rep.{u, u, u, u, u, o} X R K).algebra N)))).hom
              ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
                (DerivedCategory.Q.map (tensorWithComplexHomComplexMap.{u, o} X R K
                  (DifferentialGradedModule.propertyPModel.{o, u, 0}
                    (Rep.{u, u, u, u, u, o} X R K).algebra M)
                  (DifferentialGradedModule.propertyPModel.{o, u, 0}
                    (Rep.{u, u, u, u, u, o} X R K).algebra N))) η))) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N)) :=
    (Iso.comp_inv_eq ((DerivedCategory.Q.commShiftIso n).app
      ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra N)))).1
    (homComplexToGlobalDerivedHom_homology_degree X
      ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M))
      ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra N)) n
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
        (DerivedCategory.Q.map (tensorWithComplexHomComplexMap.{u, o} X R K
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M)
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N))) η))
  have hffnat : ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
          (((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M)).HomComplex
            ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra N)))).hom
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          (DerivedCategory.Q.map (tensorWithComplexHomComplexMap.{u, o} X R K
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M)
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N))) η) =
      HomologicalComplex.homologyMap (tensorWithComplexHomComplexMap.{u, o} X R K
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M)
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N)) n
        (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
          ((DifferentialGradedModule.dgCategory.{_, _, u}
              (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M)
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N))).hom η) :=
    ConcreteCategory.congr_hom
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).hom.naturality
        (tensorWithComplexHomComplexMap.{u, o} X R K
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M)
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N))) η
  have hin3 : homComplexHomologyAddEquiv
        ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M))
        ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N)) n
        (HomologicalComplex.homologyMap (tensorWithComplexHomComplexMap.{u, o} X R K
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M)
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N)) n
          (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
            ((DifferentialGradedModule.dgCategory.{_, _, u}
                (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M)
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra N))).hom η)) =
      (tensorWithComplexHomotopy.{u, u, u, u, u, o} X R K).map
          (DifferentialGradedModule.General.closedToHomotopy
            (Rep.{u, u, u, u, u, o} X R K).algebra
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M)
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N) n f) ≫
        (HomotopyCategory.quotient (TensorModO.{u, u, u, u, u} X) (ComplexShape.up ℤ)).map
          (DifferentialGradedModule.dgFunctorToComplexesShiftIso
            (tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N) n).hom := by
    rw [hη, show ∀ x, homComplexHomologyAddEquiv
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M))
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N)) n x =
        CohomologyClass.homAddEquiv (homologyAddEquiv
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra M))
          ((tensorWithComplexDG.{u, u, u, u, u, o} X R K).functor.obj
            (DifferentialGradedModule.propertyPModel.{o, u, 0}
              (Rep.{u, u, u, u, u, o} X R K).algebra N)) n x) from fun _ => rfl]
    exact tensorWithComplexHomComplexMap_homology X R K _ _ n f
  have hsrc : tensorWithComplexDerivedHomSourceExtEquiv.{u, o} X R K M N n η =
      ((DifferentialGradedModule.propertyPModelIso.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M).inv ≫
          ((DifferentialGradedModule.quasiIsomorphisms
                (Rep.{u, u, u, u, u, o} X R K).algebra).Q.map
              (DifferentialGradedModule.General.homAddEquivOfEq
                (DifferentialGradedModule.General.toHomotopyCategory_obj_shift
                  (Rep.{u, u, u, u, u, o} X R K).algebra
                  (DifferentialGradedModule.propertyPModel.{o, u, 0}
                    (Rep.{u, u, u, u, u, o} X R K).algebra N) n)
                (DifferentialGradedModule.General.closedToHomotopy
                  (Rep.{u, u, u, u, u, o} X R K).algebra
                  (DifferentialGradedModule.propertyPModel.{o, u, 0}
                    (Rep.{u, u, u, u, u, o} X R K).algebra M)
                  (DifferentialGradedModule.propertyPModel.{o, u, 0}
                    (Rep.{u, u, u, u, u, o} X R K).algebra N) n f)) ≫
            (((DifferentialGradedModule.quasiIsomorphisms
                (Rep.{u, u, u, u, u, o} X R K).algebra).Q).commShiftIso n).hom.app
              ((DifferentialGradedModule.toHomotopyCategory
                  (Rep.{u, u, u, u, u, o} X R K).algebra).obj
                (DifferentialGradedModule.propertyPModel.{o, u, 0}
                  (Rep.{u, u, u, u, u, o} X R K).algebra N)))) ≫
        (CategoryTheory.shiftFunctor (DifferentialGradedModule.derivedCategory
            (Rep.{u, u, u, u, u, o} X R K).algebra) n).map
          (DifferentialGradedModule.propertyPModelIso.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N).hom := by
    rw [show tensorWithComplexDerivedHomSourceExtEquiv.{u, o} X R K M N n η =
        DifferentialGradedModule.propertyPModelExtEquiv.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M N n
          (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
            ((DifferentialGradedModule.dgCategory.{_, _, u}
                (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M)
              (DifferentialGradedModule.propertyPModel.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra N))).hom η) from rfl, hη,
      show DifferentialGradedModule.propertyPModelExtEquiv.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M N n
            ((DifferentialGradedModule.General.homScHomologyEquiv
                (Rep.{u, u, u, u, u, o} X R K).algebra
                (DifferentialGradedModule.propertyPModel.{o, u, 0}
                  (Rep.{u, u, u, u, u, o} X R K).algebra M)
                (DifferentialGradedModule.propertyPModel.{o, u, 0}
                  (Rep.{u, u, u, u, u, o} X R K).algebra N) n).symm
              (QuotientAddGroup.mk f)) =
          ((DifferentialGradedModule.propertyPModelIso.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra M).inv ≫
              ((DifferentialGradedModule.quasiIsomorphisms
                    (Rep.{u, u, u, u, u, o} X R K).algebra).Q.map
                  (DifferentialGradedModule.General.homComplexHomologyEquiv
                    (Rep.{u, u, u, u, u, o} X R K).algebra
                    (DifferentialGradedModule.propertyPModel.{o, u, 0}
                      (Rep.{u, u, u, u, u, o} X R K).algebra M)
                    (DifferentialGradedModule.propertyPModel.{o, u, 0}
                      (Rep.{u, u, u, u, u, o} X R K).algebra N) n
                    ((DifferentialGradedModule.General.homScHomologyEquiv
                        (Rep.{u, u, u, u, u, o} X R K).algebra
                        (DifferentialGradedModule.propertyPModel.{o, u, 0}
                          (Rep.{u, u, u, u, u, o} X R K).algebra M)
                        (DifferentialGradedModule.propertyPModel.{o, u, 0}
                          (Rep.{u, u, u, u, u, o} X R K).algebra N) n).symm
                      (QuotientAddGroup.mk f))) ≫
                (((DifferentialGradedModule.quasiIsomorphisms
                    (Rep.{u, u, u, u, u, o} X R K).algebra).Q).commShiftIso n).hom.app
                  ((DifferentialGradedModule.toHomotopyCategory
                      (Rep.{u, u, u, u, u, o} X R K).algebra).obj
                    (DifferentialGradedModule.propertyPModel.{o, u, 0}
                      (Rep.{u, u, u, u, u, o} X R K).algebra N)))) ≫
            (CategoryTheory.shiftFunctor (DifferentialGradedModule.derivedCategory
                (Rep.{u, u, u, u, u, o} X R K).algebra) n).map
              (DifferentialGradedModule.propertyPModelIso.{o, u, 0}
                (Rep.{u, u, u, u, u, o} X R K).algebra N).hom from rfl,
      DifferentialGradedModule.General.homComplexHomologyEquiv_mk]
  have hM := repIso_hom_comp_quotientCompQhIso_inv X R K M
  have hN := counit_comp_quotientCompQhIso_hom_comp_repIso_inv X R K N
  have hq := tensorWithComplexDerivedExtMap_q.{u, u, u, u, u, o} X R K n
    (DifferentialGradedModule.General.homAddEquivOfEq
      (DifferentialGradedModule.General.toHomotopyCategory_obj_shift
        (Rep.{u, u, u, u, u, o} X R K).algebra
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra N) n)
      (DifferentialGradedModule.General.closedToHomotopy (Rep.{u, u, u, u, u, o} X R K).algebra
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M)
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra N) n f))
  have hiii := localizationHomAddHom_tensorWithComplexHomotopy X R K
    (DifferentialGradedModule.propertyPModel.{o, u, 0} (Rep.{u, u, u, u, u, o} X R K).algebra M)
    (DifferentialGradedModule.propertyPModel.{o, u, 0} (Rep.{u, u, u, u, u, o} X R K).algebra N) n
    (DifferentialGradedModule.General.closedToHomotopy (Rep.{u, u, u, u, u, o} X R K).algebra
      (DifferentialGradedModule.propertyPModel.{o, u, 0}
        (Rep.{u, u, u, u, u, o} X R K).algebra M)
      (DifferentialGradedModule.propertyPModel.{o, u, 0}
        (Rep.{u, u, u, u, u, o} X R K).algebra N) n f)
  rw [show tensorWithComplexDerivedHomTargetExtEquiv.{u, o} X R K M N n =
      globalDerivedHomDegreeEquiv X ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj M)
        ((tensorWithComplexDerived.{u, u, u, u, u, o} X R K).obj N) n from rfl, hsplit, htgt,
    hin1, hffnat, hin3, hsrc,
    tensorWithComplexDerivedExtMap_comp_right, tensorWithComplexDerivedExtMap_comp_left]
  exact assemble
    (CategoryTheory.shiftFunctor
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n)
    _ _ _ _ _ _ _ _ _ _ _ hiii hM hq hN

/-- *The map on cohomology is the map*
`Ext^n_{D(E, d)}(M, N) → Ext^n_{D(O)}(M ⊗_E^𝐋 K^•, N ⊗_E^𝐋 K^•)` *induced by the functor*
`- ⊗_E^𝐋 K^•`. The degree-`n` cohomology of the canonical map
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerived`, read on the source by
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomSourceExtEquiv` and on the target by
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomTargetExtEquiv` — which exhibit the two
cohomology modules as those two `Ext`-groups — is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedExtMap`, the map on `Ext` induced by the
derived tensor product with `K`.

There is no hypothesis on `M`, `N` or the site. The identification lives in `D(ℤ) = D(Ab)`: the
objects quantified over are formed over `R`, but the canonical map is read with the scalars of its
source and target forgotten. The same identification for the `D(R)`-valued map is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedHomMapDerivedModulesOver_homology`. -/
theorem tensorWithComplexDerivedHomMapDerived_homology
    (M N : DifferentialGradedModule.derivedCategory (Rep.{u, u, u, u, u, o} X R K).algebra) (n : ℤ)
    (η : ↥((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      (DerivedCategory.Q.obj ((DifferentialGradedModule.dgCategory.{_, _, u}
          (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M)
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra N))))) :
    tensorWithComplexDerivedHomTargetExtEquiv.{u, o} X R K M N n
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map
          (tensorWithComplexDerivedHomMapDerived.{u, o} X R K M N) η) =
      tensorWithComplexDerivedExtMap.{u, u, u, u, u, o} X R K n
        (tensorWithComplexDerivedHomSourceExtEquiv.{u, o} X R K M N n η) := by
  obtain ⟨f, hf⟩ := QuotientAddGroup.mk_surjective
    ((DifferentialGradedModule.General.homScHomologyEquiv
        (Rep.{u, u, u, u, u, o} X R K).algebra
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra M)
        (DifferentialGradedModule.propertyPModel.{o, u, 0}
          (Rep.{u, u, u, u, u, o} X R K).algebra N) n)
      (((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
        ((DifferentialGradedModule.dgCategory.{_, _, u}
            (Rep.{u, u, u, u, u, o} X R K).algebra).homComplex
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra M)
          (DifferentialGradedModule.propertyPModel.{o, u, 0}
            (Rep.{u, u, u, u, u, o} X R K).algebra N))).hom η))
  refine tensorWithComplexDerivedHomMapDerived_homology_aux X R K M N n η f ?_
  rw [hf]
  exact (AddEquiv.symm_apply_apply _ _).symm

end AlgebraicGeometry.RingedSite

end
