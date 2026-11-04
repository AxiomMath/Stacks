module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionShift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionWeaklyExact
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestrictionTriangulated
public import StacksFrontier.CategoryTheory.Triangulated.TransposeLocus

/-!
# Derived restriction of sections and the translation

Let `C` be a category with the chaotic topology, `O` a sheaf of commutative rings on it and
`(A, d)` a sheaf of differential graded `O`-algebras. For a morphism `a : V ⟶ U` of `Cᵒᵖ` the
derived restriction map `RΓ(V, -) ⟶ RΓ(U, -)_{A(V)}` at the translate `X[1]` of an object of
`D(A, d)` is the translate of the derived restriction map at `X`, up to the identifications
`RΓ(W, X[1]) ≅ RΓ(W, X)[1]` given by `M[1](W) ≅ M(W)[1]` on a module `M` computing `X`, and the
commutation of derived restriction of scalars with the translation. This is the shift hypothesis
of `CategoryTheory.Pretriangulated.transposeLocus_isTriangulated`.

## Main results

* `SheafOfModules.DifferentialGradedModule.derivedRestrictionMap_app_eq`: the derived restriction
  map at the class of a module, written through the identifications of derived sections with
  sections.
* `SheafOfModules.DifferentialGradedModule.shiftSquare_derivedRestrictionMap`: the shift square
  at the class of every module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective
attribute [local instance 10000]
  _root_.DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-! ### Two identities in an arbitrary category

The identities below are the bookkeeping of the computation of this file, stated over arbitrary
objects. Applied to the actual morphisms they are checked up to definitional unfolding of the
functors on homotopy categories, whose values on the classes of modules are only definitionally,
not syntactically, those classes. -/

section Bookkeeping

variable {E : Type*} [Category E]

private theorem eq_of_comp_eq {P P' T S S' : E} (d : P ⟶ P') (q : P' ⟶ T) (ψ : P ⟶ S)
    (g : S ⟶ S') (f : S' ⟶ T) (f' : T ⟶ S') (g' : S' ⟶ S) (h : d ≫ q = ψ ≫ g ≫ f)
    (e₁ : f ≫ f' = 𝟙 _) (e₂ : g ≫ g' = 𝟙 _) : ψ = d ≫ q ≫ f' ≫ g' := by
  rw [← Category.assoc d, h]
  simp [reassoc_of% e₁, e₂]

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂] (G : D₁ ⥤ D₂) (Sh₁ : D₁ ⥤ D₁)
  (Sh₂ : D₂ ⥤ D₂) (e : Sh₁ ⋙ G ≅ G ⋙ Sh₂)

/-- The computation of the shift square, over arbitrary objects. -/
private theorem shiftSquare_aux
    {SU₁ SUs cUs cUt cU SU : D₁} {SV₁ SVs cVs cVt cV SV cVr cVsr cVrs cVsr' : D₂}
    (ψ' : SV₁ ⟶ G.obj SU₁) (ψs : SVs ⟶ G.obj SUs) (ψX : SV ⟶ G.obj SU)
    (ιU : SU₁ ⟶ SUs) (ιV : SV₁ ⟶ SVs)
    (φUs : SUs ⟶ cUs) (φUs' : cUs ⟶ SUs) (φU' : cU ⟶ SU)
    (φVs : SVs ⟶ cVs) (φV : SV ⟶ cV) (φV' : cV ⟶ SV)
    (rs : cVs ⟶ cVsr') (fs : cVsr' ⟶ G.obj cUs) (σU : cUs ⟶ cUt) (σUr : cVsr' ⟶ cVrs)
    (f' : cVrs ⟶ G.obj cUt) (σV : cVs ⟶ cVt) (r1 : cVt ⟶ cVsr) (ρ : cVsr ⟶ cVrs)
    (r : cV ⟶ cVr) (f : cVr ⟶ G.obj cU) (finv : G.obj cU ⟶ cVr) (j₁ : cVr ⟶ cVr) (j₂ : cVrs ⟶ cVrs)
    (κU : cUt ⟶ Sh₁.obj cU) (κV : cVt ⟶ Sh₂.obj cV) (κVr : cVsr ⟶ Sh₂.obj cVr)
    (κVr' : Sh₂.obj cVr ⟶ cVsr)
    (hψι : ψ' ≫ G.map ιU = ιV ≫ ψs) (hψs : ψs = φVs ≫ rs ≫ fs ≫ G.map φUs')
    (hφUs : φUs' ≫ φUs = 𝟙 _) (hnat : fs ≫ G.map σU = σUr ≫ f')
    (hstar : rs ≫ σUr = σV ≫ r1 ≫ ρ) (hψX : ψX = φV ≫ r ≫ f ≫ G.map φU')
    (hφV : φV' ≫ φV = 𝟙 _) (hf : f ≫ finv = 𝟙 _) (hj₁ : j₁ = 𝟙 _) (hj₂ : j₂ = 𝟙 _)
    (hE : e.inv.app cU = Sh₂.map finv ≫ Sh₂.map j₁ ≫ κVr' ≫ ρ ≫ j₂ ≫ f' ≫ G.map κU)
    (hκV : r1 ≫ κVr = κV ≫ Sh₂.map r) (hκVr : κVr ≫ κVr' = 𝟙 _) :
    ψ' ≫ G.map (ιU ≫ φUs ≫ σU ≫ κU ≫ Sh₁.map φU') =
      (ιV ≫ φVs ≫ σV ≫ κV ≫ Sh₂.map φV') ≫ Sh₂.map ψX ≫ e.inv.app SU := by
  have hn := e.inv.naturality φU'
  simp only [Functor.comp_map] at hn
  rw [hψX]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, hE, hj₁, hj₂, Sh₂.map_id, Category.id_comp, Category.id_comp]
  simp only [Category.assoc]
  rw [← Sh₂.map_comp_assoc φV' φV, hφV, Sh₂.map_id, Category.id_comp,
    ← Sh₂.map_comp_assoc f finv, hf, Sh₂.map_id, Category.id_comp,
    ← reassoc_of% hκV, reassoc_of% hκVr, reassoc_of% hψι, hψs]
  simp only [Category.assoc]
  rw [← G.map_comp_assoc φUs' φUs, hφUs, G.map_id, Category.id_comp,
    reassoc_of% hnat, reassoc_of% hstar]

end Bookkeeping

variable {C : Type u} [Category.{u} C] {O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, v}
    (Stacks.SheafOfModules.Tensor.ringSheaf (chaoticRingedSite O).O)) {U V : Cᵒᵖ} (a : V ⟶ U)

/-- The derived restriction map at the class of a module `M`, written through the
identifications of the derived sections with the classes of the section modules: it is the class
of restriction of sections `M(V) ⟶ M(U)_{A(V)}`. -/
theorem derivedRestrictionMap_app_eq (M : DifferentialGradedModule.{u, v, v} A) :
    (derivedRestrictionMap A a).app
        ((toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj M)) =
      (derivedSectionsIso A V).hom.app M ≫
        (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q.map
          ((_root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra V)).map
            (M.sectionModuleRestriction a)) ≫
        (_root_.DifferentialGradedModule.derivedRestrictionFactorization
          (A.sectionRestriction a)).inv.app
          ((_root_.DifferentialGradedModule.toHomotopyCategory _).obj
            ((sectionModuleFunctor A U).obj M)) ≫
        (_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a)).map
          ((derivedSectionsIso A U).inv.app M) :=
  eq_of_comp_eq _ _ _ _ _ _ _ (derivedRestrictionMap_app_toDerivedCategory A a M)
    (Iso.hom_inv_id_app _ _)
    (((_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a)).map_comp
      _ _).symm.trans ((congrArg (_root_.DifferentialGradedModule.derivedRestriction
        (A.sectionRestriction a)).map (Iso.hom_inv_id_app _ _)).trans
          (CategoryTheory.Functor.map_id _ _)))

/-- The translate of the class of a module is the class of its shift. -/
def shiftClassIso (M : DifferentialGradedModule.{u, v, v} A) :
    ((toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj M))⟦(1 : ℤ)⟧ ≅
      (toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj (shift M)) :=
  (((toDerivedCategory A).commShiftIso (1 : ℤ)).app _).symm ≪≫
    eqToIso (congrArg (toDerivedCategory A).obj (HomotopyCategory.shiftFunctor_obj A M))

/-- **The shift square of the derived restriction map**: at the class of every module, the
derived restriction map at the translate is the translate of the derived restriction map, up to
the identifications `RΓ(W, X[1]) ≅ RΓ(W, X)[1]` coming from `M[1](W) ≅ M(W)[1]` and the
commutation `_root_.DifferentialGradedModule.derivedRestrictionShiftIso` of derived restriction
of scalars with the translation. -/
theorem shiftSquare_derivedRestrictionMap (M : DifferentialGradedModule.{u, v, v} A) :
    ShiftSquare (derivedRestrictionMap A a)
      (_root_.DifferentialGradedModule.derivedRestrictionShiftIso (A.sectionRestriction a) 1)
      ((toDerivedCategory A).obj ((HomotopyCategory.quotient A).obj M)) := by
  let cl' := _root_.DifferentialGradedModule.classFunctor (A.sectionAlgebra V)
  let fact := _root_.DifferentialGradedModule.derivedRestrictionFactorization
    (A.sectionRestriction a)
  let i := shiftClassIso A M
  let φU := derivedSectionsIso A U
  let φV := derivedSectionsIso A V
  let iso (W : Cᵒᵖ) := (derivedSections A W).mapIso i ≪≫ (derivedSectionsIso A W).app (shift M) ≪≫
    (_root_.DifferentialGradedModule.classFunctor (A.sectionAlgebra W)).mapIso
      (shiftSectionsIso M W) ≪≫
    ((_root_.DifferentialGradedModule.classFunctor (A.sectionAlgebra W)).commShiftIso
      (1 : ℤ)).app (M.sectionModule W) ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso ((derivedSectionsIso A W).app M).symm
  refine ⟨iso U, iso V, ?_⟩
  have hψι := (derivedRestrictionMap A a).naturality i.hom
  simp only [Functor.comp_map] at hψι
  have hnat := fact.inv.naturality ((_root_.DifferentialGradedModule.toHomotopyCategory _).map
    (shiftSectionsHom M U))
  simp only [Functor.comp_map] at hnat
  have hκV := (cl'.commShiftIso (1 : ℤ)).hom.naturality (M.sectionModuleRestriction a)
  simp only [Functor.comp_map] at hκV
  have hstar : cl'.map ((shift M).sectionModuleRestriction a) ≫
      cl'.map (_root_.DifferentialGradedModule.restrictScalarsHom (A.sectionRestriction a)
        (shiftSectionsHom M U)) =
      cl'.map (shiftSectionsHom M V) ≫
        cl'.map ((shiftFunctor _ (1 : ℤ)).map (M.sectionModuleRestriction a)) ≫
        cl'.map (_root_.DifferentialGradedModule.restrictScalarsShiftInv (A.sectionRestriction a)
          1 (M.sectionModule U)) :=
    (cl'.map_comp _ _).symm.trans ((congrArg cl'.map
      (sectionModuleRestriction_shiftSectionsHom M U a)).trans
        ((cl'.map_comp _ _).trans (congrArg (cl'.map _ ≫ ·) (cl'.map_comp _ _))))
  have hE := _root_.DifferentialGradedModule.derivedRestrictionShiftIso_inv_app
    (A.sectionRestriction a) 1 (M.sectionModule U)
  simp only [_root_.DifferentialGradedModule.derivedRestrictionShiftIsoOnModules,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom, Functor.comp_map] at hE
  let Qv := (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra V)).Q
  let rI := _root_.DifferentialGradedModule.restrictScalarsHomotopyFunctorIso
    (A.sectionRestriction a)
  have hj₁ : Qv.map (rI.hom.app (M.sectionModule U)) = 𝟙 _ :=
    (congrArg Qv.map (CategoryTheory.Quotient.lift.isLift_hom _ _ _ _)).trans (Qv.map_id _)
  have hj₂ : Qv.map (rI.inv.app ((shiftFunctor _ (1 : ℤ)).obj (M.sectionModule U))) = 𝟙 _ :=
    (congrArg Qv.map (CategoryTheory.Quotient.lift.isLift_inv _ _ _ _)).trans (Qv.map_id _)
  exact shiftSquare_aux
    (_root_.DifferentialGradedModule.derivedRestriction (A.sectionRestriction a))
    (shiftFunctor _ (1 : ℤ)) (shiftFunctor _ (1 : ℤ))
    (_root_.DifferentialGradedModule.derivedRestrictionShiftIso (A.sectionRestriction a) 1)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hψι.symm (derivedRestrictionMap_app_eq A a (shift M)) (Iso.inv_hom_id_app φU (shift M))
    hnat.symm hstar (derivedRestrictionMap_app_eq A a M) (Iso.inv_hom_id_app φV M)
    (Iso.inv_hom_id_app fact _) hj₁ hj₂ hE hκV (Iso.hom_inv_id_app (cl'.commShiftIso (1 : ℤ)) _)

end DifferentialGradedModule

end SheafOfModules

end
