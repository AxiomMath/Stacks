module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismCupProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedExtensionByZero
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
import StacksCore.Tactic.StacksAttribute

/-!
# The morphism `ξ' : Ω^• ⟶ Ω^•[n]` commutes with restriction to opens

Property (4) of Remark 0FU7: for an open `U ⊆ X` the restriction `ξ'|_U` is the morphism attached
by Differential Graded Sheaves, Section 0FU3 to the restriction `ξ|_U`.

Restriction to `U` is restriction to the slice site at `U`
(`AlgebraicGeometry.RingedSite.over`), for sheaves of modules
(`SheafOfModules.overFunctor`, exact, so it induces a functor of derived categories), for sheaves
of differential graded algebras (`SheafOfModules.DifferentialGradedAlgebra.over`) and for right
differential graded modules (`SheafOfModules.DifferentialGradedModule.over`). The argument is the
one of the source: `ξ'` is the image of a roof `𝒜 ⟶ I ⟵ 𝒜[n]` of maps of right differential
graded modules; restricting the roof gives a roof over `U`, so `ξ'|_U` lifts to `D(𝒜|_U, d)`;
restriction commutes with precomposition with the unit, so `ξ'|_U(1) = ξ|_U`; and the uniqueness
of Section 0FU3 over `U` concludes.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.restrictShiftedHom`: the restriction `F|_U` of a
  morphism `F : K ⟶ K[n]` of `D(𝒪)`.
* `SheafOfModules.DifferentialGradedModule.structureSheafComplexOverHom`: the comparison
  `𝒪_U[0] ⟶ (𝒪[0])|_U`, through which the unit of `𝒜|_U` factors.
* `AlgebraicGeometry.SheafOfModules.deRhamDerivedClass`: a de Rham class `ξ ∈ H^n_{dR}(X/S)` as a
  morphism `f^{-1}𝒪_S ⟶ Ω^•[n]` of `D(f^{-1}𝒪_S)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_derivedForgetShiftedHom_eq_restrictShiftedHom`:
  the restriction of the underlying morphism of `g : 𝒜 ⟶ 𝒜[n]` in `D(𝒜, d)` lifts to `D(𝒜|_U, d)`.
* `SheafOfModules.DifferentialGradedModule.lift_and_unit_iff_eq_restrictShiftedHom`: a morphism
  `𝒜|_U ⟶ 𝒜|_U[n]` of `D(𝒪_U)` lifts to `D(𝒜|_U, d)` and has value `ξ|_U` at the unit if and only
  if it is `ξ'|_U`.
* `AlgebraicGeometry.SheafOfModules.lift_and_unit_iff_eq_restrictShiftedHom_deRhamClassMorphism`:
  property (4) of Remark 0FU7 for the relative de Rham complex.

## References

* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Section 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}} (U : X.C)

/-! ### Restriction of morphisms of the derived category to a slice -/

section Restriction

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [HasDerivedCategory.{w'}
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- **The restriction `F|_U` of a morphism `F : K ⟶ K[n]` of `D(𝒪)` to the slice at `U`**: the
image of `F` under the exact restriction functor, through its commutation with the localization
functors and with the translations. -/
noncomputable def restrictShiftedHom
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (n : ℤ) (F : DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :
    DerivedCategory.Q.obj (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⟶
      (DerivedCategory.Q.obj (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L))⟦n⟧ :=
  (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors.inv.app K ≫
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map F ≫
    ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.commShiftIso n).hom.app
        (DerivedCategory.Q.obj L) ≫
    ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors.hom.app L)⟦n⟧'

/-- The restriction of a morphism `Q K ⟶ Q L` of `D(𝒪)`, through the commutation of the
restriction functor with the localization functors. -/
noncomputable abbrev restrictHom
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.obj (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) :=
  (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors.inv.app K ≫
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map f ≫
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors.hom.app L

/-- The restriction of the image of a chain map is the image of its restriction. -/
theorem restrictHom_Q_map
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : K ⟶ L) : restrictHom U (DerivedCategory.Q.map φ) =
      DerivedCategory.Q.map (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) := by
  rw [restrictHom, Functor.mapDerivedCategoryFactors_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- Restriction is compatible with composition. -/
theorem restrictHom_comp
    {K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L)
    (g : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj M) :
    restrictHom U (f ≫ g) = restrictHom U f ≫ restrictHom U g := by
  simp [restrictHom]

/-- **The restriction of a shifted morphism through the commutation of the localization with the
translation**: for `f : Q K ⟶ Q(K[n])`, the restriction of `f` followed by the commutation of `Q`
with `[n]` is the restriction of `f`, followed by the commutation of the restriction of complexes
with `[n]` (degreewise the identity) and that of `Q` over `U`. -/
theorem restrictShiftedHom_comp_commShiftIso
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (n : ℤ) (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (L⟦n⟧)) :
    restrictShiftedHom U n (f ≫ (DerivedCategory.Q.commShiftIso n).hom.app L) =
      restrictHom U f ≫ DerivedCategory.Q.map ((((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso n).hom.app L) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) := by
  have h := NatTrans.shift_app_comm ((SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors.hom) n L
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at h
  simp only [Functor.comp_obj, Category.assoc] at h
  rw [restrictShiftedHom, restrictHom, Functor.map_comp, Category.assoc, Category.assoc,
    Category.assoc, h]

/-- Restriction of a shifted morphism precomposed with the image of a chain map. -/
theorem restrictShiftedHom_Q_map_comp
    {K K' L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (n : ℤ) (φ : K' ⟶ K) (F : DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :
    restrictShiftedHom U n (DerivedCategory.Q.map φ ≫ F) =
      DerivedCategory.Q.map (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) ≫ restrictShiftedHom U n F := by
  rw [restrictShiftedHom, restrictShiftedHom, Functor.map_comp, ← restrictHom_Q_map]
  simp only [restrictHom, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Restriction of an identification `Q K = Q L` coming from an equality of complexes. -/
theorem restrictHom_eqToHom
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (h : K = L) :
    restrictHom U (eqToHom (congrArg DerivedCategory.Q.obj h)) =
      eqToHom (congrArg (fun K => DerivedCategory.Q.obj (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) h) := by
  subst h
  simp [restrictHom]

end Restriction

/-- An `eqToHom` between complexes of sheaves of modules does not move local sections, up to
transport. -/
theorem eqToHom_f_val_app_heq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {K L : CochainComplex (SheafOfModules.{u} R) ℤ} (h : K = L) (k : ℤ)
    (V : Cᵒᵖ) (x : (K.X k).val.obj V) : HEq (((eqToHom h).f k).val.app V x) x := by
  subst h
  rfl

/-- **A chain map which does not move local sections is a map of right differential graded
modules** as soon as the two actions agree with a common family of maps on local sections. -/
theorem map_mul_of_heq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {B : DifferentialGradedAlgebra.{u, u} R}
    {M N : DifferentialGradedModule.{u, u, u} B} (φ : M.complex ⟶ N.complex)
    (W : ℤ → Cᵒᵖ → Type u) (T : ℤ → ℤ → Cᵒᵖ → Type u)
    (G : ∀ p q V, W p V → (B.complex.X q).val.obj V → T p q V)
    (c : ∀ p V, (M.complex.X p).val.obj V → W p V) (hc : ∀ p V x, HEq x (c p V x))
    (hφ : ∀ k V (z : (M.complex.X k).val.obj V), HEq ((φ.f k).val.app V z) z)
    (hM : ∀ p q V (x : (M.complex.X p).val.obj V) (w : W p V) y, HEq x w →
      HEq ((M.mul p q).app V x y) (G p q V w y))
    (hN : ∀ p q V (x : (N.complex.X p).val.obj V) (w : W p V) y, HEq x w →
      HEq ((N.mul p q).app V x y) (G p q V w y))
    (p q : ℤ) (V : Cᵒᵖ) (x : (M.complex.X p).val.obj V) (y : (B.complex.X q).val.obj V) :
    (φ.f (p + q)).val.app V ((M.mul p q).app V x y) =
      (N.mul p q).app V ((φ.f p).val.app V x) y :=
  eq_of_heq ((hφ _ _ _).trans ((hM p q V x _ y (hc p V x)).trans
    (hN p q V _ _ y ((hφ p V x).trans (hc p V x))).symm))

variable (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The restriction `𝒜|_U` of a sheaf of differential graded algebras to the slice at `U`**,
`SheafOfModules.DifferentialGradedAlgebra.over`, read as a sheaf of differential graded algebras
over the structure sheaf of the localized ringed site `AlgebraicGeometry.RingedSite.over`. -/
noncomputable abbrev dgaOver :
    DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) :=
  A.over U

/-- The identification underlying `shiftedModuleOverHom`, degreewise the identity. -/
noncomputable abbrev shiftedModuleOverComplexHom (n : ℤ) :
    ((shiftedModule A (regularModule A) n).over U).complex ⟶
      (shiftedModule (dgaOver U A) (regularModule (dgaOver U A)) n).complex :=
  eqToHom (congrArg ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (HomotopyCategory.shiftFunctor_obj_complex A n (regularModule A))) ≫
    (((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso n).hom.app A.complex ≫
    eqToHom (HomotopyCategory.shiftFunctor_obj_complex (dgaOver U A) n
      (regularModule (dgaOver U A))).symm

/-- The components of `shiftedModuleOverComplexHom` do not move local sections, up to transport. -/
theorem shiftedModuleOverComplexHom_heq (n k : ℤ) (V : (Over U)ᵒᵖ)
    (z : (((shiftedModule A (regularModule A) n).over U).complex.X k).val.obj V) :
    HEq (((shiftedModuleOverComplexHom U A n).f k).val.app V z) z := by
  let e₁ := eqToHom (congrArg ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
    (HomotopyCategory.shiftFunctor_obj_complex A n (regularModule A)))
  let σ := (((SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).commShiftIso n).hom.app A.complex
  let e₂ := eqToHom (HomotopyCategory.shiftFunctor_obj_complex (dgaOver U A) n
      (regularModule (dgaOver U A))).symm
  have h1 : ((shiftedModuleOverComplexHom U A n).f k).val.app V z =
      (e₂.f k).val.app V ((σ.f k).val.app V ((e₁.f k).val.app V z)) := rfl
  exact (heq_of_eq h1).trans ((eqToHom_f_val_app_heq _ k V _).trans
    (eqToHom_f_val_app_heq _ k V z))

/-- **The restriction of the translate is the translate of the restriction**: the identification
of the restriction to `U` of the translate `𝒜[n]` of the regular module with the translate of the
regular module of `𝒜|_U`, as a map of right differential graded `𝒜|_U`-modules. In each degree it
is the identity of `𝒜^{p + n}|_U`. -/
noncomputable def shiftedModuleOverHom (n : ℤ) :
    (shiftedModule A (regularModule A) n).over U ⟶
      shiftedModule (dgaOver U A) (regularModule (dgaOver U A)) n where
  toHomologicalComplex := shiftedModuleOverComplexHom U A n
  map_mul := map_mul_of_heq (shiftedModuleOverComplexHom U A n)
    (fun p V => (A.complex.X (p + n)).val.obj (op V.unop.left))
    (fun p q V => (A.complex.X (p + n + q)).val.obj (op V.unop.left))
    (fun p q V w y => ((regularModule A).mul (p + n) q).app (op V.unop.left) w y)
    (fun p V x => cast (by
      change (((shiftedModule A (regularModule A) n).complex.X p).val.obj (op V.unop.left) :
        Type u) = _
      rw [HomotopyCategory.shiftFunctor_obj_complex A n (regularModule A)]
      rfl) x)
    (fun p V x => (cast_heq _ x).symm)
    (shiftedModuleOverComplexHom_heq U A n)
    (fun p q V x w y hx =>
      shiftedModule_mul_heq A (regularModule A) n p q (op V.unop.left) x w y hx)
    (fun p q V x w y hx => shiftedModule_mul_heq (dgaOver U A)
      (regularModule (dgaOver U A)) n p q V x w y hx)

/-- The forgetful computation behind `exists_derivedForgetShiftedHom_eq_restrictShiftedHom`, with
every object and morphism a variable. -/
theorem forget_roof_paste {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {P Q R S T : C}
    {T' T'' : D} (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S) (h : S ⟶ T) (i : T ⟶ S)
    (a' : F.obj P ⟶ F.obj Q)
    (c' : F.obj R ⟶ F.obj S) (k : F.obj S ⟶ T') (l : T' ⟶ T'') (hi : h ≫ i = 𝟙 _)
    (ha : F.map a = a') (hc : F.map c = c') :
    F.map ((a ≫ b ≫ c ≫ h) ≫ i) ≫ k ≫ l = a' ≫ F.map b ≫ c' ≫ k ≫ l := by
  rw [Category.assoc, Category.assoc, Category.assoc, hi, Category.comp_id, F.map_comp, F.map_comp,
    ha, hc]
  simp only [Category.assoc]

/-- The cancellations behind `exists_derivedForgetShiftedHom_eq_restrictShiftedHom`, with every
object and morphism a variable. -/
theorem restrict_roof_paste {C : Type*} [Category C] {P Q Q' R S₁ S₂ T : C}
    (r : P ⟶ Q) (h' : Q = Q') (eb : Q' ≅ R) (jx : P ⟶ R) (σ : Q ⟶ S₁)
    (h₃ : S₁ = S₂) (h₄ : S₂ = S₁) (cU : S₁ ⟶ T) (e' : Q ⟶ Q') (rb : Q' ⟶ R)
    (he' : e' = eqToHom h') (hrb : rb = eb.hom) (hr : r ≫ e' ≫ rb = jx) :
    jx ≫ eb.inv ≫ (eqToHom h'.symm ≫ σ ≫ eqToHom h₃) ≫ eqToHom h₄ ≫ cU = r ≫ σ ≫ cU := by
  subst h' h₃ he' hrb
  rw [← hr]
  simp

/-- The roof of `exists_derivedForgetShiftedHom_comp_eq` with the underlying morphism split off its
last commutation with the translation, with every object and morphism a variable. -/
theorem roof_split_paste {C : Type*} [Category C] {P Q R S : C} (F : P ⟶ S) (a : P ⟶ Q)
    (c : Q ⟶ S) (ci : S ⟶ Q) (rest : Q ⟶ R) (y : P ⟶ R) (hF : F = a ≫ c) (hcc : c ≫ ci = 𝟙 _)
    (h : F ≫ ci ≫ rest = y) : a ≫ rest = y := by
  rw [← h, hF, Category.assoc, reassoc_of% hcc]

/-- **The restriction of the structure sheaf placed in degree zero** is the structure sheaf of the
slice placed in degree zero: the comparison `𝒪_U[0] ⟶ (𝒪[0])|_U`. -/
noncomputable def structureSheafComplexOverHom :
    AlgebraicGeometry.RingedSite.structureSheafComplex (X.over U) ⟶
      ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (AlgebraicGeometry.RingedSite.structureSheafComplex X) :=
  HomologicalComplex.mkHomFromSingle
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inv) (by
    intro k _
    change _ ≫ (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
      ((AlgebraicGeometry.RingedSite.structureSheafComplex X).d 0 k) = 0
    rw [show (AlgebraicGeometry.RingedSite.structureSheafComplex X).d 0 k = 0 by simp,
      Functor.map_zero]
    exact Limits.comp_zero)

/-- **The restriction of the unit `𝒪 ⟶ 𝒜` is the unit `𝒪|_U ⟶ 𝒜|_U`.** -/
theorem structureSheafComplexOverHom_comp_unitComplexRingHom :
    structureSheafComplexOverHom U ≫ ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (unitComplexRingHom A) =
      unitComplexRingHom (dgaOver U A) := by
  refine HomologicalComplex.from_single_hom_ext ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  rfl

section Unit

variable [HasDerivedCategory.{w'}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))]

/-- The image in `D(𝒪_U)` of the unit `𝒪_U ⟶ 𝒜|_U` factors through the restriction of the unit
`𝒪 ⟶ 𝒜`. -/
theorem Q_map_unitComplexRingHom_dgaOver :
    Eq (DerivedCategory.Q.map (unitComplexRingHom (dgaOver U A)))
      (DerivedCategory.Q.map (structureSheafComplexOverHom U) ≫
        DerivedCategory.Q.map (((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (unitComplexRingHom A))) :=
  (congrArg DerivedCategory.Q.map
    (structureSheafComplexOverHom_comp_unitComplexRingHom U A).symm).trans
      (DerivedCategory.Q.map_comp _ _)

end Unit

/-! ### The restriction of `ξ'`

The derived category `D(𝒜, d)` of right differential graded modules, its forgetful functor
`derivedForget` and `derivedForgetShiftedHom` are built on `HasDerivedCategory.standard`, which is
therefore the model of `D(𝒪)` used below. -/

section Standard

attribute [local instance] HasDerivedCategory.standard

/-- The unit of `𝒜|_U` followed by a restricted shifted morphism is the comparison followed by the
restriction of the unit of `𝒜` composed with that morphism. -/
private theorem Q_map_unitComplexRingHom_dgaOver_comp_restrictShiftedHom (n : ℤ)
    (F : DerivedCategory.Q.obj A.complex ⟶ (DerivedCategory.Q.obj A.complex)⟦n⟧) :
    DerivedCategory.Q.map (unitComplexRingHom (dgaOver U A)) ≫ restrictShiftedHom U n F =
      DerivedCategory.Q.map (structureSheafComplexOverHom U) ≫
        restrictShiftedHom U n (DerivedCategory.Q.map (unitComplexRingHom A) ≫ F) :=
  (congrArg (· ≫ _) (Q_map_unitComplexRingHom_dgaOver U A)).trans
    ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (restrictShiftedHom_Q_map_comp U n _ _).symm))

/-- **The restriction of `ξ'` lifts to `D(𝒜|_U, d)`.** For a morphism `g : 𝒜 ⟶ 𝒜[n]` of
`D(𝒜, d)`, the restriction to `U` of its underlying morphism of `D(𝒪)` is the underlying morphism
of a morphism `𝒜|_U ⟶ 𝒜|_U[n]` of `D(𝒜|_U, d)`: restricting a roof `𝒜 ⟶ I ⟵ 𝒜[n]` of maps of
right differential graded modules gives one over `U`. -/
theorem exists_derivedForgetShiftedHom_eq_restrictShiftedHom (n : ℤ)
    (g : (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
      ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj
        (regularModule A)))⟦n⟧) :
    ∃ g' : (toDerivedCategory.{u, u, u} (dgaOver U A)).obj
        ((HomotopyCategory.quotient (dgaOver U A)).obj (regularModule (dgaOver U A))) ⟶
      ((toDerivedCategory.{u, u, u} (dgaOver U A)).obj
        ((HomotopyCategory.quotient (dgaOver U A)).obj
        (regularModule (dgaOver U A))))⟦n⟧,
      Eq (derivedForgetShiftedHom (dgaOver U A) (regularModule (dgaOver U A)) n g')
        (restrictShiftedHom U n (derivedForgetShiftedHom A (regularModule A) n g)) := by
  obtain ⟨I, x, b, hb, hroof⟩ := exists_derivedForgetShiftedHom_comp_eq A n g
  let := Stacks.SheafOfModules.preservesHomology_overFunctor
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  have hjb : QuasiIso (overMap b U).toHomologicalComplex :=
    inferInstanceAs (QuasiIso (((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map b.toHomologicalComplex))
  have hN := HomotopyCategory.shiftFunctor_obj_complex A n (regularModule A)
  refine ⟨(toDerivedCategory.{u, u, u} (dgaOver U A)).map
      ((HomotopyCategory.quotient (dgaOver U A)).map
      (overMap x U)) ≫ (toDerivedCategoryIso (overMap b U) hjb).inv ≫
      (toDerivedCategory.{u, u, u} (dgaOver U A)).map ((HomotopyCategory.quotient (dgaOver U A)).map
        (shiftedModuleOverHom U A n)) ≫
      ((toDerivedCategory.{u, u, u} (dgaOver U A)).commShiftIso n).hom.app
        ((HomotopyCategory.quotient (dgaOver U A)).obj (regularModule (dgaOver U A))), ?_⟩
  refine Eq.trans (b := DerivedCategory.Q.map (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map x.toHomologicalComplex) ≫
        ((derivedForget (dgaOver U A)).mapIso (toDerivedCategoryIso (overMap b U) hjb)).inv ≫
        DerivedCategory.Q.map (shiftedModuleOverComplexHom U A n) ≫
        eqToHom (congrArg DerivedCategory.Q.obj (HomotopyCategory.shiftFunctor_obj_complex
          (dgaOver U A) n (regularModule (dgaOver U A)))) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (dgaOver U A).complex) ?_ ?_
  · unfold derivedForgetShiftedHom
    exact forget_roof_paste (derivedForget (dgaOver U A)) _ _ _ _ _ _ _ _ _
      (Iso.hom_inv_id_app _ _) (derivedForget_map_toDerivedCategory_map (dgaOver U A) _)
      (derivedForget_map_toDerivedCategory_map (dgaOver U A) _)
  have hF : derivedForgetShiftedHom A (regularModule A) n g =
      ((derivedForget A).map (g ≫ ((toDerivedCategory.{u, u, u} A).commShiftIso n).inv.app
        ((HomotopyCategory.quotient A).obj (regularModule A))) ≫
        eqToHom (congrArg DerivedCategory.Q.obj hN)) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (regularModule A).complex :=
    (Category.assoc _ _ _).symm
  have hDE := roof_split_paste _ _ _ _ _ _ hF (Iso.hom_inv_id_app _ _) hroof
  have hr := ((restrictHom_comp U _ _).trans (congrArg (_ ≫ ·) (restrictHom_comp U _ _))).symm.trans
    ((congrArg (restrictHom U) hDE).trans (restrictHom_Q_map U x.toHomologicalComplex))
  have hb' : ((derivedForget (dgaOver U A)).mapIso (toDerivedCategoryIso (overMap b U) hjb)).hom =
      DerivedCategory.Q.map (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map b.toHomologicalComplex) :=
    derivedForget_map_toDerivedCategory_map (dgaOver U A) _
  have hι : DerivedCategory.Q.map (shiftedModuleOverComplexHom U A n) =
      eqToHom (congrArg (fun K => DerivedCategory.Q.obj (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) hN) ≫
        DerivedCategory.Q.map ((((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso n).hom.app A.complex) ≫
        eqToHom (congrArg DerivedCategory.Q.obj (HomotopyCategory.shiftFunctor_obj_complex
          (dgaOver U A) n (regularModule (dgaOver U A))).symm) :=
    (DerivedCategory.Q.map_comp _ _).trans (congrArg₂ (· ≫ ·) (eqToHom_map _ _)
      ((DerivedCategory.Q.map_comp _ _).trans (congrArg (_ ≫ ·) (eqToHom_map _ _))))
  refine Eq.trans ?_ (congrArg (restrictShiftedHom U n) hF).symm
  refine Eq.trans ?_ (restrictShiftedHom_comp_commShiftIso U n _).symm
  refine Eq.trans (congrArg (fun t => _ ≫ _ ≫ t ≫ _ ≫ _) hι) ?_
  exact restrict_roof_paste _ _ _ _ _ _ _ _ _ _ (restrictHom_eqToHom U hN.symm)
    ((restrictHom_Q_map U b.toHomologicalComplex).trans hb'.symm) hr

/-- **Remark 0FU7, property (4), for a sheaf of differential graded algebras.** Let
`g : 𝒜 ⟶ 𝒜[n]` be a morphism of `D(𝒜, d)` with underlying morphism `ξ'` of `D(𝒪)`, and let `g'` be
a morphism of `D(𝒜|_U, d)` whose value at the unit is the restriction of that of `g`. Then the
restriction `ξ'|_U` is the underlying morphism of `g'`. -/
theorem restrictShiftedHom_derivedForgetShiftedHom (n : ℤ)
    (g : (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
      ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj
        (regularModule A)))⟦n⟧)
    (g' : (toDerivedCategory.{u, u, u} (dgaOver U A)).obj
        ((HomotopyCategory.quotient (dgaOver U A)).obj (regularModule (dgaOver U A))) ⟶
      ((toDerivedCategory.{u, u, u} (dgaOver U A)).obj
        ((HomotopyCategory.quotient (dgaOver U A)).obj
        (regularModule (dgaOver U A))))⟦n⟧)
    (h : Eq (DerivedCategory.Q.map (unitComplexRingHom (dgaOver U A)) ≫
        derivedForgetShiftedHom (dgaOver U A) (regularModule (dgaOver U A)) n g')
      (DerivedCategory.Q.map (structureSheafComplexOverHom U) ≫
        restrictShiftedHom U n (DerivedCategory.Q.map (unitComplexRingHom A) ≫
          derivedForgetShiftedHom A (regularModule A) n g))) :
    Eq (restrictShiftedHom U n (derivedForgetShiftedHom A (regularModule A) n g))
      (derivedForgetShiftedHom (dgaOver U A) (regularModule (dgaOver U A)) n g') := by
  obtain ⟨g'', hg''⟩ := exists_derivedForgetShiftedHom_eq_restrictShiftedHom U A n g
  have h₁ : DerivedCategory.Q.map (unitComplexRingHom (dgaOver U A)) ≫
      derivedForgetShiftedHom (dgaOver U A) (regularModule (dgaOver U A)) n g'' =
      DerivedCategory.Q.map (unitComplexRingHom (dgaOver U A)) ≫
      derivedForgetShiftedHom (dgaOver U A) (regularModule (dgaOver U A)) n g' :=
    (congrArg (_ ≫ ·) hg'').trans
      ((Q_map_unitComplexRingHom_dgaOver_comp_restrictShiftedHom U A n _).trans h.symm)
  rw [unitComplexRingHom_derivedForgetShiftedHom, unitComplexRingHom_derivedForgetShiftedHom] at h₁
  exact hg''.symm.trans (congrArg _ ((forgetUnitHom_bijective (dgaOver U A)
    (regularModule (dgaOver U A)) n).1 ((cancel_mono _).1 h₁)))

/-- **Remark 0FU7, property (4), for a sheaf of differential graded algebras.** Let
`g : 𝒜 ⟶ 𝒜[n]` be a morphism of `D(𝒜, d)` with underlying morphism `ξ'` of `D(𝒪)`, and let
`ξ = ξ' ∘ 1 ∈ Hom_{D(𝒪)}(𝒪, 𝒜[n]) = H^n(𝒜)`. A morphism `f : 𝒜|_U ⟶ 𝒜|_U[n]` of `D(𝒪_U)` has
properties (1) and (2) over `U` for the restriction `ξ|_U` (it lifts to `D(𝒜|_U, d)`, and its
value `f ∘ 1` at the unit is `ξ|_U`) if and only if it is the restriction `ξ'|_U`. -/
theorem lift_and_unit_iff_eq_restrictShiftedHom (n : ℤ)
    (g : (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj (regularModule A)) ⟶
      ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj
        (regularModule A)))⟦n⟧)
    (f : DerivedCategory.Q.obj (regularModule (dgaOver U A)).complex ⟶
      (DerivedCategory.Q.obj (regularModule (dgaOver U A)).complex)⟦n⟧) :
    ((∃ g' : (toDerivedCategory.{u, u, u} (dgaOver U A)).obj
        ((HomotopyCategory.quotient (dgaOver U A)).obj (regularModule (dgaOver U A))) ⟶
      ((toDerivedCategory.{u, u, u} (dgaOver U A)).obj
        ((HomotopyCategory.quotient (dgaOver U A)).obj
        (regularModule (dgaOver U A))))⟦n⟧,
        Eq (derivedForgetShiftedHom (dgaOver U A) (regularModule (dgaOver U A)) n g') f) ∧
      Eq (DerivedCategory.Q.map (unitComplexRingHom (dgaOver U A)) ≫ f)
        (DerivedCategory.Q.map (structureSheafComplexOverHom U) ≫
          restrictShiftedHom U n (DerivedCategory.Q.map (unitComplexRingHom A) ≫
            derivedForgetShiftedHom A (regularModule A) n g))) ↔
      Eq f (restrictShiftedHom U n (derivedForgetShiftedHom A (regularModule A) n g)) := by
  constructor
  · rintro ⟨⟨g', rfl⟩, h⟩
    exact (restrictShiftedHom_derivedForgetShiftedHom U A n g g' h).symm
  · rintro rfl
    obtain ⟨g'', hg''⟩ := exists_derivedForgetShiftedHom_eq_restrictShiftedHom U A n g
    exact ⟨⟨g'', hg''⟩, Q_map_unitComplexRingHom_dgaOver_comp_restrictShiftedHom U A n _⟩

end Standard

end SheafOfModules.DifferentialGradedModule

/-! ### The relative de Rham complex -/

namespace AlgebraicGeometry.SheafOfModules

open TopologicalSpace

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

section Standard

attribute [local instance] HasDerivedCategory.standard

/-- **A de Rham class as a morphism of `D(f^{-1}𝒪_S)`**: the morphism
`f^{-1}𝒪_S ⟶ Ω^•_{X/S}[n]` corresponding to `ξ ∈ H^n_{dR}(X/S)` under
`H^n(X, Ω^•[n]) = Hom_{D(f^{-1}𝒪_S)}(f^{-1}𝒪_S, Ω^•[n])`, `φ ↦ φ(1)`
(`structureSheafEval_bijective`). -/
noncomputable def deRhamDerivedClass (n : ℤ) (ξ : deRhamCohomology B D n) :
    AlgebraicGeometry.RingedSite.derivedStructureSheaf (baseSite A) ⟶
      (deRhamDerivedObject B D)⟦n⟧ :=
  (Equiv.ofBijective _ (structureSheafEval_bijective A _)).symm
    ((deRhamShiftHomologyIso B D n 0 n (add_zero n)).inv ξ)

/-- `ξ'` precomposed with the unit `f^{-1}𝒪_S ⟶ Ω^•` is the class of `ξ`: this is property (2). -/
theorem deRhamUnitHom_comp_deRhamClassMorphism (n : ℤ) (ξ : deRhamCohomology B D n) :
    deRhamUnitHom B D ≫ deRhamClassMorphism B D n ξ = deRhamDerivedClass B D n ξ := by
  apply (structureSheafEval_bijective A _).1
  calc structureSheafEval A _ (deRhamUnitHom B D ≫ deRhamClassMorphism B D n ξ)
      = (deRhamShiftHomologyIso B D n 0 n (add_zero n)).inv
          ((deRhamShiftHomologyIso B D n 0 n (add_zero n)).hom
            (structureSheafEval A _ (deRhamUnitHom B D ≫ deRhamClassMorphism B D n ξ))) := by
        simp
    _ = (deRhamShiftHomologyIso B D n 0 n (add_zero n)).inv ξ :=
        congrArg _ ((deRhamEvalOne_eq B D n (deRhamClassMorphism B D n ξ)).symm.trans
          (deRhamEvalOne_deRhamClassMorphism B D n ξ))
    _ = _ := (Equiv.ofBijective_apply_symm_apply _ _ _).symm

/-- **Stacks Project, Tag 0FU7, property (4).** The construction of `ξ'` commutes with
restriction to opens: for an open `U ⊆ X`, write `Ω^•_{U/S} = Ω^•_{X/S}|_U` for the restriction
of the de Rham complex (a sheaf of differential graded algebras over the slice site at `U`) and
`ξ|_U ∈ Hom_{D(f^{-1}𝒪_S|_U)}(f^{-1}𝒪_S|_U, Ω^•_{U/S}[n]) = H^n_{dR}(U/S)` for the restriction of
`ξ`. A morphism `f : Ω^•_{U/S} ⟶ Ω^•_{U/S}[n]` of `D(f^{-1}𝒪_S|_U)` is the map corresponding to
`ξ|_U` (it lifts to the derived category of right differential graded `Ω^•_{U/S}`-modules, and
its value `f(1)` at the unit is `ξ|_U`) if and only if it is the restriction `ξ'|_U`. -/
@[stacks 0FU7 "property (4): the construction commutes with restriction to opens"]
theorem lift_and_unit_iff_eq_restrictShiftedHom_deRhamClassMorphism (n : ℤ)
    (ξ : deRhamCohomology B D n) (U : Opens X.carrier)
    (f : DerivedCategory.Q.obj (_root_.SheafOfModules.DifferentialGradedModule.regularModule
        (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
          (deRhamDifferentialGradedAlgebra B D))).complex ⟶
      (DerivedCategory.Q.obj (_root_.SheafOfModules.DifferentialGradedModule.regularModule
        (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
          (deRhamDifferentialGradedAlgebra B D))).complex)⟦n⟧) :
    ((∃ g' : (_root_.SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u}
        (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
          (deRhamDifferentialGradedAlgebra B D))).obj
        ((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient
          (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
            (deRhamDifferentialGradedAlgebra B D))).obj
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule
            (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
              (deRhamDifferentialGradedAlgebra B D)))) ⟶
      ((_root_.SheafOfModules.DifferentialGradedModule.toDerivedCategory.{u, u, u}
        (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
          (deRhamDifferentialGradedAlgebra B D))).obj
        ((_root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient
          (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
            (deRhamDifferentialGradedAlgebra B D))).obj
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule
            (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
              (deRhamDifferentialGradedAlgebra B D)))))⟦n⟧,
        Eq (_root_.SheafOfModules.DifferentialGradedModule.derivedForgetShiftedHom
          (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
            (deRhamDifferentialGradedAlgebra B D))
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule
            (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
              (deRhamDifferentialGradedAlgebra B D))) n g') f) ∧
      Eq (DerivedCategory.Q.map (_root_.SheafOfModules.DifferentialGradedModule.unitComplexRingHom
          (_root_.SheafOfModules.DifferentialGradedModule.dgaOver (X := baseSite A) U
            (deRhamDifferentialGradedAlgebra B D))) ≫ f)
        (DerivedCategory.Q.map
          (_root_.SheafOfModules.DifferentialGradedModule.structureSheafComplexOverHom
            (X := baseSite A) U) ≫
          _root_.SheafOfModules.DifferentialGradedModule.restrictShiftedHom (X := baseSite A) U n
            (deRhamDerivedClass B D n ξ))) ↔
      Eq f (_root_.SheafOfModules.DifferentialGradedModule.restrictShiftedHom (X := baseSite A) U n
        (deRhamClassMorphism B D n ξ)) := by
  rw [← deRhamUnitHom_comp_deRhamClassMorphism]
  exact _root_.SheafOfModules.DifferentialGradedModule.lift_and_unit_iff_eq_restrictShiftedHom
    (X := baseSite A) U (deRhamDifferentialGradedAlgebra B D) n
    (deRhamClassDerivedEquiv B D n ξ) f

end Standard

end AlgebraicGeometry.SheafOfModules
