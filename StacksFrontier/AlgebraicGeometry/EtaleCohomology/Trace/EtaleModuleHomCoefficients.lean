module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHomResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleHomAcyclic

/-!
# The sheaf `Hom_R(M, -)` with coefficients in an `A`-algebra `Λ`

Let `A` be a commutative ring, `R` and `Λ` two `A`-algebras and `M` an `(R, Λ)`-bimodule on
which `A` acts centrally: `ρ : Λ →+* (End_R M)ᵐᵒᵖ` with `ρ(a) = a` for `a ∈ A`. Then `Hom_R(M, -)`
with its `Λ`-module structure, read over `A`, is `Hom_R(M, -)` with its `A`-module structure.
Every property of the sheaf `Hom_R(M, G)` which may be read on underlying sheaves of `A`-modules
is therefore inherited from the case `Λ = A`: commutation with inverse image and extension by
zero for `M` finite, exactness of `Hom_R(M, -)` on a complex, and acyclicity of `Hom_R(M, I)` for
an injective sheaf `I`.

The comparison maps are mates (`Stacks.EtaleCohomology.coefficientMate`), and the mate for a
composite change of coefficients is the composite of the mates
(`Stacks.EtaleCohomology.coefficientMate_comp`).

## Main results

* `Stacks.EtaleCohomology.coefficientMate_comp`
* `Stacks.EtaleCohomology.isIso_coefficientMate_inverseImage_homFunctor`
* `Stacks.EtaleCohomology.isIso_coefficientMate_extensionByZero_homFunctor`
* `Stacks.EtaleCohomology.quasiIso_map_etaleModuleHom_of_central`
* `Stacks.EtaleCohomology.isAcyclicEverywhere_etaleModuleHom_of_injective_of_central`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Mates of composite squares -/

section Mate

variable {C₁ C₂ D₁ D₂ E₁ E₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Category* E₁] [Category* E₂]
  {L₁ : C₁ ⥤ C₂} {P₁ : C₂ ⥤ C₁} (adj₁ : L₁ ⊣ P₁) {L₂ : D₁ ⥤ D₂} {P₂ : D₂ ⥤ D₁} (adj₂ : L₂ ⊣ P₂)
  {L₃ : E₁ ⥤ E₂} {P₃ : E₂ ⥤ E₁} (adj₃ : L₃ ⊣ P₃)

/-- **The mate of a composite square is the composite of the mates.** -/
lemma strictMate_comp {Ψ₁ : C₁ ⥤ D₁} {Ψ₂ : C₂ ⥤ D₂} {Ψ₁' : D₁ ⥤ E₁} {Ψ₂' : D₂ ⥤ E₂}
    (β : P₁ ⋙ Ψ₁ ⟶ Ψ₂ ⋙ P₂) (β' : P₂ ⋙ Ψ₁' ⟶ Ψ₂' ⋙ P₃)
    (γ : P₁ ⋙ (Ψ₁ ⋙ Ψ₁') ⟶ (Ψ₂ ⋙ Ψ₂') ⋙ P₃)
    (hγ : ∀ Z, γ.app Z = Ψ₁'.map (β.app Z) ≫ β'.app (Ψ₂.obj Z)) (X : C₁) :
    (strictMate adj₁ adj₃ γ).app X =
      (strictMate adj₂ adj₃ β').app (Ψ₁.obj X) ≫ Ψ₂'.map ((strictMate adj₁ adj₂ β).app X) := by
  have hε := adj₃.counit.naturality
    (Ψ₂'.map (L₂.map (Ψ₁.map (adj₁.unit.app X)) ≫ L₂.map (β.app (L₁.obj X)) ≫
      adj₂.counit.app (Ψ₂.obj (L₁.obj X))))
  have hβ' := β'.naturality (L₂.map (Ψ₁.map (adj₁.unit.app X)) ≫ L₂.map (β.app (L₁.obj X)) ≫
      adj₂.counit.app (Ψ₂.obj (L₁.obj X)))
  have hη := adj₂.unit.naturality (Ψ₁.map (adj₁.unit.app X) ≫ β.app (L₁.obj X))
  have htri := adj₂.right_triangle_components (Ψ₂.obj (L₁.obj X))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hε hβ' hη htri
  have key : adj₂.unit.app (Ψ₁.obj X) ≫ P₂.map (L₂.map (Ψ₁.map (adj₁.unit.app X)) ≫
      L₂.map (β.app (L₁.obj X)) ≫ adj₂.counit.app (Ψ₂.obj (L₁.obj X))) =
        Ψ₁.map (adj₁.unit.app X) ≫ β.app (L₁.obj X) := by
    rw [← L₂.map_comp_assoc, P₂.map_comp, ← Category.assoc, ← hη, Category.assoc, htri,
      Category.comp_id]
  rw [strictMate_app, strictMate_app, strictMate_app, hγ]
  simp only [Category.assoc]
  rw [← hε, ← L₃.map_comp_assoc, ← L₃.map_comp_assoc, ← L₃.map_comp_assoc]
  refine congrArg (· ≫ _) (congrArg L₃.map ?_)
  rw [Category.assoc, ← hβ', ← Ψ₁'.map_comp_assoc, key, Ψ₁'.map_comp, Functor.comp_map,
    Category.assoc]

end Mate

section Coefficients

variable {R B C : Type} [Ring R] [Ring B] [Ring C] {S T : Scheme.{u}} (uf : S.Etale ⥤ T.Etale)
  [uf.IsContinuous S.smallEtaleTopology T.smallEtaleTopology]
  {L_R : EtaleModules.{u, 0} R S ⥤ EtaleModules.{u, 0} R T}
  (adj_R : L_R ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} R) S.smallEtaleTopology
    T.smallEtaleTopology)
  {L_B : EtaleModules.{u, 0} B S ⥤ EtaleModules.{u, 0} B T}
  (adj_B : L_B ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} B) S.smallEtaleTopology
    T.smallEtaleTopology)
  {L_C : EtaleModules.{u, 0} C S ⥤ EtaleModules.{u, 0} C T}
  (adj_C : L_C ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} C) S.smallEtaleTopology
    T.smallEtaleTopology)

/-- **The comparison for a composite change of coefficients** `Φ ⋙ Φ'` is the comparison for
`Φ'` followed by `Φ'` applied to the comparison for `Φ`. -/
lemma coefficientMate_comp (Φ : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} B)
    (Φ' : ModuleCat.{u + 1} B ⥤ ModuleCat.{u + 1} C)
    [S.smallEtaleTopology.HasSheafCompose Φ] [T.smallEtaleTopology.HasSheafCompose Φ]
    [S.smallEtaleTopology.HasSheafCompose Φ'] [T.smallEtaleTopology.HasSheafCompose Φ']
    [S.smallEtaleTopology.HasSheafCompose (Φ ⋙ Φ')] [T.smallEtaleTopology.HasSheafCompose (Φ ⋙ Φ')]
    (G : EtaleModules.{u, 0} R S) :
    (coefficientMate uf adj_R L_C adj_C (Φ ⋙ Φ')).app G =
      (coefficientMate uf adj_B L_C adj_C Φ').app ((sheafCompose S.smallEtaleTopology Φ).obj G) ≫
        (sheafCompose T.smallEtaleTopology Φ').map ((coefficientMate uf adj_R L_B adj_B Φ).app G) :=
  strictMate_comp adj_R adj_B adj_C (Ψ₁ := sheafCompose S.smallEtaleTopology Φ)
    (Ψ₂ := sheafCompose T.smallEtaleTopology Φ) (Ψ₁' := sheafCompose S.smallEtaleTopology Φ')
    (Ψ₂' := sheafCompose T.smallEtaleTopology Φ') (𝟙 _) (𝟙 _) (𝟙 _) (fun Z => by
      change 𝟙 _ = (sheafCompose S.smallEtaleTopology Φ').map (𝟙 _) ≫ 𝟙 _
      rw [Category.comp_id, CategoryTheory.Functor.map_id]) G

end Coefficients

/-- Restriction of scalars of sheaves of modules along a morphism of rings reflects
isomorphisms. -/
lemma isIso_of_isIso_etaleModuleRestrictScalars_map {Λ Λ' : Type} [Ring Λ] [Ring Λ']
    (φ : Λ →+* Λ') {Y : Scheme.{u}} {F G : EtaleModules.{u, 0} Λ' Y} (f : F ⟶ G)
    [IsIso ((etaleModuleRestrictScalars φ Y).map f)] : IsIso f := by
  have : ∀ U, IsIso (f.hom.app U) := fun U => by
    have : IsIso ((etaleModuleRestrictScalars φ Y).map f).hom :=
      (sheafToPresheaf _ _).map_isIso ((etaleModuleRestrictScalars φ Y).map f)
    have : IsIso ((ModuleCat.restrictScalars.{u + 1} φ).map (f.hom.app U)) :=
      NatIso.isIso_app_of_isIso ((etaleModuleRestrictScalars φ Y).map f).hom U
    exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars.{u + 1} φ)
  have : IsIso f.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')).map f) := this
  exact isIso_of_reflects_iso f (sheafToPresheaf _ _)

section Transfer

variable {A : Type} [CommRing A] {R : Type} [Ring R] [Algebra A R] {Λ : Type} [Ring Λ]
  [Algebra A Λ] (M : ModuleCat.{u + 1} R) (ρ : Λ →+* (End M)ᵐᵒᵖ)
  (hρ : ∀ a : A, ρ (algebraMap A Λ a) = centralScalars M a)

include hρ in
/-- **`Hom_R(M, -)` with coefficients in `Λ`, read over `A`**, is `Hom_R(M, -)` with
coefficients in `A`, when `A` acts on `M` through `Λ` by central scalars. -/
def homFunctorCentralIso :
    homFunctor M (centralScalars (A := A) M) ≅
      homFunctor M ρ ⋙ ModuleCat.restrictScalars.{u + 1} (algebraMap A Λ) :=
  Functor.isoWhiskerLeft (preadditiveCoyonedaObj M)
    (ModuleCat.restrictScalarsComp'.{u + 1} (algebraMap A Λ) ρ (centralScalars M)
      (RingHom.ext fun a => (hρ a).symm))

variable {S T : Scheme.{u}} (uf : S.Etale ⥤ T.Etale)
  [uf.IsContinuous S.smallEtaleTopology T.smallEtaleTopology]
  {L_R : EtaleModules.{u, 0} R S ⥤ EtaleModules.{u, 0} R T}
  (adj_R : L_R ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} R) S.smallEtaleTopology
    T.smallEtaleTopology)
  {L_Λ : EtaleModules.{u, 0} Λ S ⥤ EtaleModules.{u, 0} Λ T}
  (adj_Λ : L_Λ ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} Λ) S.smallEtaleTopology
    T.smallEtaleTopology)
  {L_A : EtaleModules.{u, 0} A S ⥤ EtaleModules.{u, 0} A T}
  (adj_A : L_A ⊣ uf.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.smallEtaleTopology
    T.smallEtaleTopology)

include hρ in
/-- **The comparison for `Hom_R(M, -)` with coefficients in `Λ` is invertible** as soon as the
one for coefficients in `A` and the one for restriction of scalars from `Λ` to `A` are. -/
lemma isIso_coefficientMate_homFunctor_of_central (G : EtaleModules.{u, 0} R S)
    (hres : IsIso ((coefficientMate uf adj_Λ L_A adj_A
      (ModuleCat.restrictScalars.{u + 1} (algebraMap A Λ))).app
        ((sheafCompose S.smallEtaleTopology (homFunctor M ρ)).obj G)))
    (hcen : IsIso ((coefficientMate uf adj_R L_A adj_A
      (homFunctor M (centralScalars (A := A) M))).app G)) :
    IsIso ((coefficientMate uf adj_R L_Λ adj_Λ (homFunctor M ρ)).app G) := by
  have hcomp := isIso_coefficientMate_of_iso uf adj_R L_A adj_A
    (homFunctorCentralIso M ρ hρ).symm G
  rw [coefficientMate_comp uf adj_R adj_Λ adj_A] at hcomp
  have : IsIso ((etaleModuleRestrictScalars (algebraMap A Λ) T).map _) :=
    (@isIso_comp_left_iff _ _ _ _ _ _ _ hres).1 hcomp
  exact isIso_of_isIso_etaleModuleRestrictScalars_map (algebraMap A Λ) _

variable [IsNoetherianRing R]

include hρ in
/-- **`Hom_R(M, -)` with coefficients in `Λ` commutes with inverse image**, for `M` finite. -/
theorem isIso_coefficientMate_inverseImage_homFunctor [Module.Finite R M] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (G : EtaleModules.{u, 0} R Y) :
    IsIso ((coefficientMate (smallEtaleBaseChange f) (etaleModuleInverseImageAdj.{u, 0} R f)
      (etaleModuleInverseImage.{u, 0} Λ f) (etaleModuleInverseImageAdj.{u, 0} Λ f)
      (homFunctor M ρ)).app G) :=
  isIso_coefficientMate_homFunctor_of_central M ρ hρ _ _ _ (etaleModuleInverseImageAdj.{u, 0} A f) G
    (inferInstance : IsIso ((etaleModuleInverseImageRestrictScalars (algebraMap A Λ) f).hom.app _))
    (isIso_coefficientMate_inverseImage f M G)

include hρ in
/-- **`Hom_R(M, -)` with coefficients in `Λ` commutes with extension by zero**, for `M`
finite. -/
theorem isIso_coefficientMate_extensionByZero_homFunctor [Module.Finite R M] {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] (G : EtaleModules.{u, 0} R U) :
    IsIso ((coefficientMate (Scheme.Etale.smallEtaleCompose j)
      (etaleModuleExtensionByZeroAdj.{u, 0} R j) (etaleModuleExtensionByZero.{u, 0} Λ j)
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) (homFunctor M ρ)).app G) :=
  isIso_coefficientMate_homFunctor_of_central M ρ hρ _ _ _
    (etaleModuleExtensionByZeroAdj.{u, 0} A j) G
    (inferInstance :
      IsIso ((etaleModuleExtensionByZeroRestrictScalars (algebraMap A Λ) j).hom.app _))
    (isIso_coefficientMate_extensionByZero j M G)

omit [IsNoetherianRing R] in
include hρ in
/-- **Quasi-isomorphisms for `Hom_R(M, -)` with coefficients in `Λ` are read over `A`.** -/
theorem quasiIso_map_etaleModuleHom_of_central {Y : Scheme.{u}}
    {K L : CochainComplex (EtaleModules.{u, 0} R Y) ℤ} (φ : K ⟶ L)
    (h : QuasiIso (((homSheaf A M Y).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) :
    QuasiIso (((etaleModuleHom M ρ Y).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have : (etaleModuleRestrictScalars (algebraMap A Λ) Y).ReflectsIsomorphisms :=
    ⟨fun f _ => isIso_of_isIso_etaleModuleRestrictScalars_map (algebraMap A Λ) f⟩
  have : Functor.PreservesZeroMorphisms (sheafCompose Y.smallEtaleTopology
      (homFunctor M ρ ⋙ ModuleCat.restrictScalars.{u + 1} (algebraMap A Λ))) :=
    inferInstanceAs (etaleModuleHom M ρ Y ⋙
      etaleModuleRestrictScalars (algebraMap A Λ) Y).PreservesZeroMorphisms
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (etaleModuleRestrictScalars (algebraMap A Λ) Y)]
  let e := NatIso.mapHomologicalComplex (sheafComposeIso Y (homFunctorCentralIso M ρ hρ))
    (ComplexShape.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality φ).symm)).1 h

end Transfer

/-! ### Acyclicity

`Stacks.EtaleCohomology.IsAcyclicEverywhere` is stated in the model `HasDerivedCategory.standard`
of the derived categories. -/

section Acyclic

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Acyclicity everywhere passes to the underlying sheaf of abelian groups**, read as a sheaf
of `ℤ`-modules: the converse of
`Stacks.EtaleCohomology.IsAcyclicEverywhere.of_restrictScalars_int`, by the same comparison of
cohomologies. -/
theorem IsAcyclicEverywhere.restrictScalars_int {Λ : Type} [Ring Λ] {X : Scheme.{u}}
    (B : EtaleModules.{u, 0} Λ X) (h : IsAcyclicEverywhere B) :
    IsAcyclicEverywhere ((etaleModuleRestrictScalars (Int.castRingHom Λ) X).obj B) := by
  intro U
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  have hU := h U
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived] at hU
  let G := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op U)
  let G₀ := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} ℤ)).obj (op U)
  let F := etaleModuleRestrictScalars (Int.castRingHom Λ) X
  let r := ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)
  let e : G ⋙ r ≅ F ⋙ G₀ := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact (r.map_isZero (hU p hp)).of_iso
    ((Stacks.Cohomology.DerivedForget.rightDerivedCompIso G r p).app B ≪≫
      (ModuleSheafCohomology.rightDerivedIso e p).app B ≪≫
      (Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic F G₀
        (fun I _ => rightAcyclic_sections_restrictScalars_int I U) p).app B).symm

variable {A : Type} [CommRing A] {R : Type} [Ring R] [Algebra A R] [IsNoetherianRing R]
  {Λ : Type} [Ring Λ] [Algebra A Λ] (M : ModuleCat.{u + 1} R) (ρ : Λ →+* (End M)ᵐᵒᵖ)
  (hρ : ∀ a : A, ρ (algebraMap A Λ a) = centralScalars M a)

include hρ in
/-- **`Hom_R(M, I)` with coefficients in `Λ` is acyclic everywhere** for an injective sheaf `I`
and a finite `R`-module `M`, `R` being Noetherian. -/
theorem isAcyclicEverywhere_etaleModuleHom_of_injective_of_central [Module.Finite R M]
    {Y : Scheme.{u}} (I : EtaleModules.{u, 0} R Y) [Injective I] :
    IsAcyclicEverywhere ((etaleModuleHom M ρ Y).obj I) := by
  apply IsAcyclicEverywhere.of_restrictScalars_int
  have h := IsAcyclicEverywhere.restrictScalars_int _
    (isAcyclicEverywhere_etaleModuleHom_of_injective (A := A) I M)
  intro U
  let e₁ := ModuleCat.restrictScalarsComp'.{u + 1} (Int.castRingHom A) (algebraMap A Λ)
    (Int.castRingHom Λ) (RingHom.ext_int _ _)
  let e : homFunctor M ρ ⋙ ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ) ≅
      homFunctor M (centralScalars (A := A) M) ⋙
        ModuleCat.restrictScalars.{u + 1} (Int.castRingHom A) :=
    Functor.isoWhiskerLeft _ e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (homFunctorCentralIso M ρ hρ).symm
        (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom A))
  exact (Functor.rightAcyclic _).prop_of_iso ((sheafComposeIso Y e).app I).symm (h U)

end Acyclic

end Stacks.EtaleCohomology
