module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpDerivedGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicResolutionIsoNaturality

/-!
# Naturality in `F` of `Γ^Gal(Ȳ, ℋom^•_ℤ((i_! F)[0], K)) ≅ RΓ^Gal(Y, ℋom_ℤ(F, ω))`

Let `i : Y ⟶ Ȳ` be an open immersion of quasi-compact and quasi-separated `k`-schemes and
`u : F₁ ⟶ F₂` a morphism of sheaves of `Λ`-modules on `Y_étale`, both as in
`Stacks.EtaleCohomology.galoisHomOpDerivedGlobalSectionsOverIso`. The isomorphisms
`Γ^Gal(Ȳ, ℋom^•_ℤ((i_! Fₐ)[0], K)) ≅ RΓ^Gal(Y, ℋom_ℤ(Fₐ, ω))` form a commutative square with
precomposition by `(i_! u)[0]` and `RΓ^Gal(Y, -)` of precomposition by `u`:

* termwise, `ℋom_ℤ(A[0], -)^p ≅ ℋom_ℤ(A, -^p)` and `ℋom_ℤ(i_! F, -) ≅ i_* ℋom_ℤ(F, i⁻¹ -)` are
  natural in `A` and `F`;
* precomposition by `u` is a morphism of `Γ^Gal`-acyclic resolutions
  `ℋom_ℤ(F₂, i⁻¹ K) ⟶ ℋom_ℤ(F₁, i⁻¹ K)` over `ℋom_ℤ(F₂, ω) ⟶ ℋom_ℤ(F₁, ω)`
  (`CategoryTheory.Functor.rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality`).

## Main results

* `Stacks.EtaleCohomology.galoisHomOpDerivedGlobalSectionsOverIso_hom_naturality`.

## Implementation notes

The local instances of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpDerivedGlobalSections` are
reactivated, so that the complexes below are spelled as there (see its implementation notes).
For the same reason
`CategoryTheory.Functor.rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality` is restated,
for abstract `C`, `D` and `G`, with the shape `ComplexShape.up ℤ` built from an arbitrary proof
of `IsRightCancelAdd ℤ`, as `Stacks.EtaleCohomology`'s
`rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality_of_isRightCancelAdd`: the kernel then
compares the two spellings once, on abstract data, instead of on the complexes of this file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.AbelianInternalHom
  Stacks.ConstantSheaf Stacks.Frobenius

universe w₁ w₂ w₃ w₄ w v u

namespace Stacks.AbelianInternalHom

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {Λ : Type w} [Ring Λ]

/-- **Precomposition with `φ : G₁ ⟶ G₂`, as a natural transformation
`ℋom_ℤ(G₂, -) ⟶ ℋom_ℤ(G₁, -)`.** -/
@[simps]
def homOpMapLeftNatTrans {G₁ G₂ : Sheaf K (ModuleCat.{max u v} Λ)} (φ : G₁ ⟶ G₂) :
    homOpFunctor K G₂ ⟶ homOpFunctor K G₁ where
  app F := homOpMapLeft K φ F
  naturality _ _ g := (homOpMapLeft_homOpMap K φ g).symm

variable [HasZeroObject (Sheaf K (ModuleCat.{max u v} Λ))]

/-- `ℋom^n_ℤ(A[0], M) ≅ ℋom_ℤ(A, M^n)` is natural in `A`. -/
lemma homOpComplexSingleXIso_hom_naturality_left {A A' : Sheaf K (ModuleCat.{max u v} Λ)}
    (a : A ⟶ A') (M : CochainComplex (Sheaf K AddCommGrpCat.{max u v}) ℤ) (n : ℤ) :
    homOpComplexPrecompX (M := M) ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map a) n ≫
        (homOpComplexSingleXIso K A M n).hom =
      (homOpComplexSingleXIso K A' M n).hom ≫ homOpMapLeft K a (M.X n) := by
  simp only [homOpComplexSingleXIso, homOpComplexPrecompX_π_assoc, Category.assoc,
    homOpMapLeft_comp]
  congr 2

end Stacks.AbelianInternalHom

namespace Stacks.EtaleCohomology

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance 10000] isRightCancelAdd_int_galoisHomOpDerived
  preservesZeroMorphisms_forgetAbOp_galoisHomOpDerived
  preservesZeroMorphisms_forgetAbZMod_galoisHomOpDerived
  preservesZeroMorphisms_forgetAbZModBar_galoisHomOpDerived
  preservesZeroMorphisms_homOp_galoisHomOpDerived preservesZeroMorphisms_homAb_galoisHomOpDerived
  preservesZeroMorphisms_restriction_galoisHomOpDerived
  preservesZeroMorphisms_etaleRestriction_galoisHomOpDerived
  preservesZeroMorphisms_galoisGlobalSections_galoisHomOpDerived
  additive_galoisGlobalSections_galoisHomOpDerived enoughInjectives_galoisHomOpDerived
  hasZeroObject_zmod_galoisHomOpDerived hasZeroObject_zmodBar_galoisHomOpDerived
  hasZeroObject_op_galoisHomOpDerived hasZeroObject_ab_galoisHomOpDerived etale_galoisHomOpDerived
  preservesZeroMorphisms_galoisGlobalSectionsBar_galoisHomOpDerived
  hasZeroObject_bar_galoisHomOpDerived hasZeroObject_abBar_galoisHomOpDerived
  hasZeroObject_opBar_galoisHomOpDerived


section ExtensionByZero

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (Λ : Type) [Ring Λ]

/-- `ℋom_ℤ(j_! F, B) ≅ j_* ℋom_ℤ(F, j⁻¹ B)` for the lifted extension by zero is natural in `F`. -/
lemma homOpLiftExtensionByZeroIso_hom_naturality_left {F₁ F₂ : EtaleModules.{u, 0} Λ U}
    (v : F₁ ⟶ F₂) (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    homOpMapLeft X.smallEtaleTopology
        ((Stacks.ModuleCatLift.moduleLift.{u + 1} Λ U.smallEtaleTopology X.smallEtaleTopology
          (extensionByZero.{u, 0} j)).map v) B ≫
        (homOpLiftExtensionByZeroIso j Λ F₁ B).hom =
      (homOpLiftExtensionByZeroIso j Λ F₂ B).hom ≫
        (Stacks.ModuleCatLift.moduleLift.{u + 1} Λᵐᵒᵖ U.smallEtaleTopology X.smallEtaleTopology
          (etaleAbelianDirectImage.{u, 0} j)).map
            (homOpMapLeft U.smallEtaleTopology v ((etaleRestriction.{u, 0} j).obj B)) :=
  (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    simp only [homOpLiftExtensionByZeroIso]
    exact internalHomExtensionByZeroIso_hom_naturality_left j B
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map v))

/-- **`ℋom_ℤ(j_! F, B) ≅ j_* ℋom_ℤ(F, j⁻¹ B)` is natural in `F`.** -/
lemma homOpExtensionByZeroIso_hom_naturality_left {F₁ F₂ : EtaleModules.{u, 0} Λ U}
    (v : F₁ ⟶ F₂) (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    homOpMapLeft X.smallEtaleTopology ((etaleModuleExtensionByZero.{u, 0} Λ j).map v) B ≫
        (homOpExtensionByZeroIso j Λ F₁ B).hom =
      (homOpExtensionByZeroIso j Λ F₂ B).hom ≫ (etaleModuleDirectImage.{u, 0} Λᵐᵒᵖ j).map
        (homOpMapLeft U.smallEtaleTopology v ((etaleRestriction.{u, 0} j).obj B)) := by
  simp only [homOpExtensionByZeroIso, Iso.trans_hom, Iso.symm_hom, homOpMapLeftIso, Iso.app_hom,
    Iso.app_inv]
  rw [← Category.assoc, homOpMapLeft_comp, ← (etaleModuleExtensionByZeroLiftIso j Λ).inv.naturality,
    ← homOpMapLeft_comp]
  simp only [Category.assoc]
  rw [reassoc_of% homOpLiftExtensionByZeroIso_hom_naturality_left j Λ v B,
    (moduleLiftEtaleDirectImageIso j Λᵐᵒᵖ).hom.naturality]

end ExtensionByZero

/-- `G(Z)[0] ≅ G(Z[0])` is natural in the functor `G`. -/
lemma singleObjMapIso_hom_naturality_functor {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroObject A] [HasZeroObject B] {G G' : A ⥤ B}
    [G.PreservesZeroMorphisms] [G'.PreservesZeroMorphisms] (τ : G ⟶ G') (Z : A) :
    (singleObjMapIso G Z).hom ≫ (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj Z) =
      (HomologicalComplex.single B (ComplexShape.up ℤ) 0).map (τ.app Z) ≫
        (singleObjMapIso G' Z).hom := by
  refine HomologicalComplex.from_single_hom_ext ?_
  simp [singleObjMapIso, HomologicalComplex.single_map_f_self]

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar] {Y Yb : Over (Spec (.of k))} (i : Y ⟶ Yb) [IsOpenImmersion i.left]
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom]

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom] in
/-- The resolutions `ℋom_ℤ(Fₐ, ω)[0] ⟶ ℋom_ℤ(Fₐ, i⁻¹ K)` commute with precomposition by
`v : F₁ ⟶ F₂`. -/
lemma homOpRestrictionResolutionMap_naturality {n : ℕ} {F₁ F₂ : EtaleModules.{u, 0} Λ Y.left}
    (v : F₁ ⟶ F₂) (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ)
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) :
    homOpRestrictionResolutionMap Λ i F₂ ω K₀ ι₀ ≫
        (NatTrans.mapHomologicalComplex (homOpMapLeftNatTrans Y.left.smallEtaleTopology v)
          (ComplexShape.up ℤ)).app
            (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              (((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
                i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)) =
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          ((homOpMapLeftNatTrans Y.left.smallEtaleTopology v).app
            ((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).obj ω)) ≫
        homOpRestrictionResolutionMap Λ i F₁ ω K₀ ι₀ := by
  simp only [homOpRestrictionResolutionMap, Category.assoc]
  rw [NatTrans.naturality, NatTrans.naturality_assoc,
    reassoc_of% singleObjMapIso_hom_naturality_functor]

omit [QuasiCompact Y.hom] [QuasiSeparated Y.hom] [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom] in
/-- The degree-`p` sheaf-level square of
`galoisHomOpSingleExtensionByZeroOverIso_hom_naturality`. -/
lemma homOpSingleExtensionByZeroOverXIso_hom_naturality {F₁ F₂ : EtaleModules.{u, 0} Λ Y.left}
    (v : F₁ ⟶ F₂) (M : CochainComplex (Sheaf Yb.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (p : ℤ) :
    homOpComplexPrecompX (M := M) ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        ((etaleModuleExtensionByZero.{u, 0} Λ i.left).map v)) p ≫
        (homOpSingleExtensionByZeroOverXIso Λ i F₁ M p).hom =
      (homOpSingleExtensionByZeroOverXIso Λ i F₂ M p).hom ≫
        (etaleModuleDirectImage.{u, 0} Λᵐᵒᵖ i.left).map
          (homOpMapLeft Y.left.smallEtaleTopology v
            ((etaleRestriction.{u, 0} i.left).obj (M.X p))) := by
  simp only [homOpSingleExtensionByZeroOverXIso, Iso.trans_hom]
  rw [← Category.assoc, homOpComplexSingleXIso_hom_naturality_left, Category.assoc,
    homOpExtensionByZeroIso_hom_naturality_left, Category.assoc]

/-- Two commutative squares compose. -/
private theorem comp_comp_square {𝒞 : Type*} [Category* 𝒞] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : 𝒞}
    {p : X₂ ⟶ X₁} {a₁ : X₁ ⟶ Y₁} {a₂ : X₂ ⟶ Y₂} {q : Y₂ ⟶ Y₁} {b₁ : Y₁ ⟶ Z₁} {b₂ : Y₂ ⟶ Z₂}
    {r : Z₂ ⟶ Z₁} (h₁ : p ≫ a₁ = a₂ ≫ q) (h₂ : q ≫ b₁ = b₂ ≫ r) :
    p ≫ a₁ ≫ b₁ = (a₂ ≫ b₂) ≫ r := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- The degree-`p` component of `galoisHomOpSingleExtensionByZeroOverIso_hom_naturality`. -/
lemma galoisHomOpSingleExtensionByZeroOverIso_hom_f_naturality
    {F₁ F₂ : EtaleModules.{u, 0} Λ Y.left} (v : F₁ ⟶ F₂)
    (M : CochainComplex (Sheaf Yb.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) (p : ℤ) :
    (galoisGlobalSections Λᵐᵒᵖ Yb kbar).map
        (homOpComplexPrecompX (M := M) ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          ((etaleModuleExtensionByZero.{u, 0} Λ i.left).map v)) p) ≫
        (galoisHomOpSingleExtensionByZeroOverIso Λ kbar i F₁ M).hom.f p =
      (galoisHomOpSingleExtensionByZeroOverIso Λ kbar i F₂ M).hom.f p ≫
        (galoisGlobalSections Λᵐᵒᵖ Y kbar).map
          (homOpMapLeft Y.left.smallEtaleTopology v
            ((etaleRestriction.{u, 0} i.left).obj (M.X p))) := by
  have h := (galoisGlobalSectionsMapDirectImageIso Λᵐᵒᵖ i kbar).hom.naturality
    (homOpMapLeft Y.left.smallEtaleTopology v ((etaleRestriction.{u, 0} i.left).obj (M.X p)))
  rw [Functor.comp_map] at h
  have hX := congrArg (galoisGlobalSections Λᵐᵒᵖ Yb kbar).map
    (homOpSingleExtensionByZeroOverXIso_hom_naturality Λ i v M p)
  rw [Functor.map_comp, Functor.map_comp] at hX
  rw [galoisHomOpSingleExtensionByZeroOverIso_hom_f, galoisHomOpSingleExtensionByZeroOverIso_hom_f]
  exact comp_comp_square hX h

/-- **`Γ^Gal(Ȳ, ℋom^•_ℤ((i_! F)[0], M)) ≅ Γ^Gal(Y, ℋom_ℤ(F, i⁻¹ M))` is natural in `F`.** -/
lemma galoisHomOpSingleExtensionByZeroOverIso_hom_naturality {F₁ F₂ : EtaleModules.{u, 0} Λ Y.left}
    (v : F₁ ⟶ F₂) (M : CochainComplex (Sheaf Yb.left.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    ((galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (homOpComplexPrecomp (M := M) ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          ((etaleModuleExtensionByZero.{u, 0} Λ i.left).map v))) ≫
        (galoisHomOpSingleExtensionByZeroOverIso Λ kbar i F₁ M).hom =
      (galoisHomOpSingleExtensionByZeroOverIso Λ kbar i F₂ M).hom ≫
        ((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (homOpMapLeftNatTrans Y.left.smallEtaleTopology v)
            (ComplexShape.up ℤ)).app
            (((etaleRestriction.{u, 0} i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              M)) := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  exact galoisHomOpSingleExtensionByZeroOverIso_hom_f_naturality Λ kbar i v M p

/-- Three commutative squares compose. -/
lemma comp_comp_comp_square {𝒞 : Type*} [Category* 𝒞] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ W₁ W₂ : 𝒞}
    {p : X₂ ⟶ X₁} {a₁ : X₁ ⟶ Y₁} {a₂ : X₂ ⟶ Y₂} {q : Y₂ ⟶ Y₁} {b₁ : Y₁ ⟶ Z₁} {b₂ : Y₂ ⟶ Z₂}
    {q' : Z₂ ⟶ Z₁} {c₁ : Z₁ ⟶ W₁} {c₂ : Z₂ ⟶ W₂} {r : W₂ ⟶ W₁} (h₁ : p ≫ a₁ = a₂ ≫ q)
    (h₂ : q ≫ b₁ = b₂ ≫ q') (h₃ : q' ≫ c₁ = c₂ ≫ r) :
    p ≫ a₁ ≫ b₁ ≫ c₁ = (a₂ ≫ b₂ ≫ c₂) ≫ r := by
  exact comp_comp_square h₁ (comp_comp_square h₂ h₃)

omit [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom] in
/-- `galoisHomOpRestrictionForgetIso` is natural in `F`. -/
lemma galoisHomOpRestrictionForgetIso_hom_naturality {n : ℕ} {F₁ F₂ : EtaleModules.{u, 0} Λ Y.left}
    (v : F₁ ⟶ F₂) (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) :
    ((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (homOpMapLeftNatTrans Y.left.smallEtaleTopology v)
          (ComplexShape.up ℤ)).app
          (((etaleRestriction.{u, 0} i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K₀))) ≫
        (galoisHomOpRestrictionForgetIso Λ kbar i F₁ K₀).hom =
      (galoisHomOpRestrictionForgetIso Λ kbar i F₂ K₀).hom ≫
        ((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (homOpMapLeftNatTrans Y.left.smallEtaleTopology v)
            (ComplexShape.up ℤ)).app
            (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              (((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
                i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀))) :=
  HomologicalComplex.hom_ext _ _ fun _ => (Category.comp_id _).trans (Category.id_comp _).symm

/-- `CategoryTheory.Functor.rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality`, with the
shapes of the single complexes and of `G.mapHomologicalComplex` built from an arbitrary proof `hc`
of `IsRightCancelAdd ℤ` (see the implementation notes). -/
theorem rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality_of_isRightCancelAdd
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] [HasDerivedCategory C]
    [HasDerivedCategory D] [EnoughInjectives C] (G : C ⥤ D) [G.Additive] (hc : IsRightCancelAdd ℤ)
    {A A' : C} (a : A ⟶ A') (R R' : CochainComplex C ℤ) (n₀ : ℤ) [R.IsStrictlyGE n₀]
    [R'.IsStrictlyGE n₀]
    (q : (HomologicalComplex.single C (@ComplexShape.up ℤ _ hc _) 0).obj A ⟶ R) [hq : QuasiIso q]
    (q' : (HomologicalComplex.single C (@ComplexShape.up ℤ _ hc _) 0).obj A' ⟶ R')
    [hq' : QuasiIso q'] (hR : ∀ n, G.rightAcyclic (R.X n)) (hR' : ∀ n, G.rightAcyclic (R'.X n))
    (g : R ⟶ R')
    (hg : q ≫ g = (HomologicalComplex.single C (@ComplexShape.up ℤ _ hc _) 0).map a ≫ q') :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (@ComplexShape.up ℤ _ hc _)).map g) ≫
        (G.rightDerivedFunctorPlusSingleIsoOfAcyclic A' R' n₀ q' hR').hom =
      (G.rightDerivedFunctorPlusSingleIsoOfAcyclic A R n₀ q hR).hom ≫
        DerivedCategory.Plus.ι.map
          (G.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map a)) :=
  Functor.rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality G a R R' n₀ q q' hR hR' g hg

section Derived

variable [HasDerivedCategory.{w₁} (EtaleModules.{u, 0} Λᵐᵒᵖ Y.left)]
  [HasDerivedCategory.{w₂} (GaloisModules Λᵐᵒᵖ k kbar)]
  [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange Y kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)]
  {n : ℕ} [NeZero n]

omit [QuasiCompact Yb.hom] [QuasiSeparated Yb.hom] in
/-- `RΓ^Gal(Y, ℋom_ℤ(F, ω)) ≅ Γ^Gal(Y, ℋom_ℤ(F, i⁻¹ K))` is natural in `F`. -/
lemma galoisHomOpDerivedLerayIso_hom_naturality {F₁ F₂ : EtaleModules.{u, 0} Λ Y.left}
    (v : F₁ ⟶ F₂)
    (G₁ : EtaleModules.{u, 0} (ZMod n) Y.left) (e₁ : toAb _ F₁ ≅ toAb _ G₁)
    (hG₁ : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G₁)
    (G₂ : EtaleModules.{u, 0} (ZMod n) Y.left) (e₂ : toAb _ F₂ ≅ toAb _ G₂)
    (hG₂ : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G₂)
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective Y.left.smallEtaleTopology (ZMod n) ω)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [K₀.IsStrictlyGE 0]
    [∀ q, Injective (K₀.X q)]
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) [QuasiIso ι₀] :
    DerivedCategory.Q.map (((galoisGlobalSections Λᵐᵒᵖ Y kbar).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (homOpMapLeftNatTrans Y.left.smallEtaleTopology v)
          (ComplexShape.up ℤ)).app
            (((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              (((etaleModuleRestriction.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left)
                i.left).mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)))) ≫
        (galoisHomOpDerivedLerayIso Λ kbar i F₁ G₁ e₁ hG₁ ω hω K₀ ι₀).hom =
      (galoisHomOpDerivedLerayIso Λ kbar i F₂ G₂ e₂ hG₂ ω hω K₀ ι₀).hom ≫
        DerivedCategory.Plus.ι.map ((galoisDerivedGlobalSections Λᵐᵒᵖ Y kbar).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((homOpMapLeftNatTrans Y.left.smallEtaleTopology v).app
              ((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).obj ω)))) :=
  rightDerivedFunctorPlusSingleIsoOfAcyclic_hom_naturality_of_isRightCancelAdd
    (galoisGlobalSections Λᵐᵒᵖ Y kbar) isRightCancelAdd_int_galoisHomOpDerived _ _ _ 0 _ _
    (hq := quasiIso_homOpRestrictionResolutionMap Λ i F₂ G₂ e₂ hG₂ ω hω K₀ ι₀)
    (hq' := quasiIso_homOpRestrictionResolutionMap Λ i F₁ G₁ e₁ hG₁ ω hω K₀ ι₀)
    (rightAcyclic_homOpRestriction Λ kbar i F₂ G₂ e₂ K₀)
    (rightAcyclic_homOpRestriction Λ kbar i F₁ G₁ e₁ K₀) _
    (homOpRestrictionResolutionMap_naturality Λ i v ω K₀ ι₀)

omit [HasDerivedCategory.{w₃} (EtaleModules.{u, 0} Λᵐᵒᵖ (fieldBaseChange Y kbar))]
  [HasDerivedCategory.{w₄} (ModuleCat.{u + 1} Λᵐᵒᵖ)] [NeZero n] in
/-- The respelling `galoisDerivedHomOpSingleRespellIso` is natural in `F`. -/
lemma galoisDerivedHomOpSingleRespellIso_hom_naturality {F₁ F₂ : EtaleModules.{u, 0} Λ Y.left}
    (v : F₁ ⟶ F₂) (ω : EtaleModules.{u, 0} (ZMod n) Y.left) :
    DerivedCategory.Plus.ι.map ((galoisDerivedGlobalSections Λᵐᵒᵖ Y kbar).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((homOpMapLeftNatTrans Y.left.smallEtaleTopology v).app
            ((etaleModuleForgetAb.{u, 0} (ZMod n) Y.left).obj ω)))) ≫
        (galoisDerivedHomOpSingleRespellIso Λ kbar F₁ ω).hom =
      (galoisDerivedHomOpSingleRespellIso Λ kbar F₂ ω).hom ≫
        DerivedCategory.Plus.ι.map ((galoisDerivedGlobalSections Λᵐᵒᵖ Y kbar).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            (homOpMapLeft Y.left.smallEtaleTopology v (toAb _ ω)))) :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- **`Γ^Gal(Ȳ, ℋom^•_ℤ((i_! F)[0], K)) ≅ RΓ^Gal(Y, ℋom_ℤ(F, ω))` is natural in `F`**: for
`v : F₁ ⟶ F₂`, the isomorphisms `galoisHomOpDerivedGlobalSectionsOverIso` commute with
precomposition by `(i_! v)[0]` and `RΓ^Gal(Y, -)` of precomposition by `v`. -/
theorem galoisHomOpDerivedGlobalSectionsOverIso_hom_naturality
    {F₁ F₂ : EtaleModules.{u, 0} Λ Y.left} (v : F₁ ⟶ F₂)
    (G₁ : EtaleModules.{u, 0} (ZMod n) Y.left) (e₁ : toAb _ F₁ ≅ toAb _ G₁)
    (hG₁ : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G₁)
    (G₂ : EtaleModules.{u, 0} (ZMod n) Y.left) (e₂ : toAb _ F₂ ≅ toAb _ G₂)
    (hG₂ : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} Y.left.smallEtaleTopology
      (ZMod n) G₂)
    (ω : EtaleModules.{u, 0} (ZMod n) Y.left)
    (hω : Stacks.ModuleInternalHom.IsLocallyConstantInjective Y.left.smallEtaleTopology (ZMod n) ω)
    (K₀ : CochainComplex (EtaleModules.{u, 0} (ZMod n) Yb.left) ℤ) [K₀.IsStrictlyGE 0]
    [∀ q, Injective (K₀.X q)]
    (ι₀ : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod n) (U := Y.left) (X := Yb.left) i.left).obj ω) ⟶
        K₀) [QuasiIso ι₀] :
    DerivedCategory.Q.map (((galoisGlobalSections Λᵐᵒᵖ Yb kbar).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        (homOpComplexPrecomp
          (M := ((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K₀)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            ((etaleModuleExtensionByZero.{u, 0} Λ i.left).map v)))) ≫
        (galoisHomOpDerivedGlobalSectionsOverIso Λ kbar i F₁ G₁ e₁ hG₁ ω hω K₀ ι₀).hom =
      (galoisHomOpDerivedGlobalSectionsOverIso Λ kbar i F₂ G₂ e₂ hG₂ ω hω K₀ ι₀).hom ≫
        DerivedCategory.Plus.ι.map ((galoisDerivedGlobalSections Λᵐᵒᵖ Y kbar).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            (homOpMapLeft Y.left.smallEtaleTopology v (toAb _ ω)))) := by
  have h₁ := galoisHomOpSingleExtensionByZeroOverIso_hom_naturality Λ kbar i v
    (((etaleModuleForgetAb.{u, 0} (ZMod n) Yb.left).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K₀)
  have h₂ := galoisHomOpRestrictionForgetIso_hom_naturality Λ kbar i v K₀
  have h₃ := galoisHomOpDerivedLerayIso_hom_naturality Λ kbar i v G₁ e₁ hG₁ G₂ e₂ hG₂ ω hω K₀ ι₀
  have hQ := (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
    (comp_comp_square h₁ h₂)).trans (DerivedCategory.Q.map_comp _ _))
  have h₄ := galoisDerivedHomOpSingleRespellIso_hom_naturality Λ kbar v ω
  exact comp_comp_comp_square hQ h₃ h₄

end Derived

end Stacks.EtaleCohomology

end
