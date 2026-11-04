module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechClasses

/-!
# The cup product on hypercohomology, computed by Čech cocycles

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings, `A = Γ(X, 𝒪_X)`, and let
`F`, `G`, `H` be bounded below complexes of `𝒪_X`-modules with a pairing
`γ : F^a ⊗ G^b ⟶ H^{a+b}` (a compatible family of `A`-bilinear maps on sections, satisfying the
Leibniz rule).  For an open covering `𝒰` the signed Alexander--Whitney formula of
[Stacks, Tag 07MB] gives a cup product `Tot(Č(𝒰, F)) ⊗ Tot(Č(𝒰, G)) ⟶ Tot(Č(𝒰, H))`, hence a
product of Čech cohomology classes, compatible with refinement.  Following [Stacks, Section 01FP],
the cup product `γ(a ∪ b) ∈ Hⁿ⁺ᵐ(X, H)` of classes `a ∈ Hⁿ(X, F)`, `b ∈ Hᵐ(X, G)` is defined by
representing `a` and `b` by Čech classes on a common covering and taking the class of their Čech
cup product.  When Čech cohomology computes the cohomology of `F` and of `G` this does not depend
on the representatives (`cup_eq`).

When `H = Tot(F ⊗ G)` and `γ` is the canonical pairing this is the cup product `a ∪ b`; in general
it is `γ(a ∪ b)`, the image of `a ∪ b` under the map induced by `γ`.

## Main definitions

* `Stacks.Cech.Hypercohomology.cechCupClass`: the cup product of two Čech classes.
* `Stacks.Cech.Hypercohomology.cup`: the cup product `γ(a ∪ b)` on hypercohomology.

## Main results

* `Stacks.Cech.Hypercohomology.cechCupClass_refinement`: the Čech cup product commutes with
  refinement.
* `Stacks.Cech.Hypercohomology.cup_eq`: the cup product is computed by any representing Čech
  classes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.RightDerivedBoundary
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing coverObject)
open Stacks.Cech.CupProduct (tensorModules tensorModulesMap)
open Stacks.Cech.LinearCupProduct (ComplexPairing)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- A pairing `F^a ⊗ G^b ⟶ H^{a+b}` of bounded below complexes of `𝒪_X`-modules: a compatible
family of `Γ(X, 𝒪_X)`-bilinear maps on sections satisfying the Leibniz rule. -/
abbrev Pairing (F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) :=
  ComplexPairing (SectionRing (ringSheaf O) ⊤)
    ((Stacks.Cech.Refinement.sectionsComplex O).obj F.obj)
    ((Stacks.Cech.Refinement.sectionsComplex O).obj G.obj)
    ((Stacks.Cech.Refinement.sectionsComplex O).obj H.obj)

variable {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)

/-- The total Čech complex of the sections presheaves. -/
noncomputable abbrev cechSections :=
  Stacks.Cech.Refinement.sectionsComplex O ⋙
    Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤)

/-- The Čech cup product of the sections presheaves, with its type inferred. -/
def cechCupRaw {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) :=
  Stacks.Cech.LinearCupProduct.cechCupProduct (coverObject U hU) (SectionRing (ringSheaf O) ⊤) γ

/-- The Čech cup product on the total Čech complexes of the sections presheaves. -/
def cechCupS {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) :
    HomologicalComplex.mapBifunctor ((cechSections O U hU).obj F.obj)
        ((cechSections O U hU).obj G.obj) (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ⟶
      (cechSections O U hU).obj H.obj :=
  cechCupRaw O U hU γ

/-- The identification of the total Čech complex. -/
theorem cech_obj_eq' (K : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) :
    (cech O U hU).obj K = (cechSections O U hU).obj K :=
  congrArg (fun T => T.obj K) (Stacks.Cech.Refinement.totalCechComplexFunctor_eq O U hU)

/-- The identification of the total Čech complex. -/
theorem cech_obj_eq (H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) :
    (cech O U hU).obj H.obj = (cechSections O U hU).obj H.obj :=
  cech_obj_eq' O U hU H.obj

/-- The total Čech complex of a morphism, through the identification `cech_obj_eq'`. -/
theorem cech_map_eq {K L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ} (f : K ⟶ L) :
    (cech O U hU).map f =
      eqToHom (cech_obj_eq' O U hU K) ≫ (cechSections O U hU).map f ≫
        eqToHom (cech_obj_eq' O U hU L).symm :=
  Functor.congr_hom (Stacks.Cech.Refinement.totalCechComplexFunctor_eq O U hU) f

/-- **The Čech cup product of [Stacks, Tag 07MB]** relative to a pairing `γ`, as a morphism of
complexes `Tot(Č(𝒰, F)) ⊗ Tot(Č(𝒰, G)) ⟶ Tot(Č(𝒰, H))`. -/
def cechCup {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) :
    HomologicalComplex.mapBifunctor ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ⟶ (cech O U hU).obj H.obj :=
  HomologicalComplex.mapBifunctorMap (eqToHom (cech_obj_eq O U hU F))
      (eqToHom (cech_obj_eq O U hU G)) (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫
    cechCupS O U hU γ ≫ eqToHom (cech_obj_eq O U hU H).symm

/-- The tensor bifunctor of complexes is functorial in both variables at once. -/
theorem mapBifunctorMap_comp {K₁ K₂ L₁ L₂ M₁ M₂ :
      CochainComplex (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) ℤ}
    (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    HomologicalComplex.mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) =
      HomologicalComplex.mapBifunctorMap f₁ f₂
          (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫
        HomologicalComplex.mapBifunctorMap g₁ g₂
          (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ fun n => HomologicalComplex.mapBifunctor.hom_ext
    fun i j h => ?_
  simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc, Category.assoc, Functor.map_comp,
    NatTrans.comp_app]
  congr 1
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Category.assoc, Category.assoc, ← Category.assoc _ (((tensorModules _).map (g₁.f i)).app _),
    NatTrans.naturality, Category.assoc]

/-- The tensor bifunctor of complexes carries `eqToHom` to `eqToHom`. -/
theorem mapBifunctorMap_eqToHom {K₁ K₂ L₁ L₂ :
      CochainComplex (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) ℤ}
    (h₁ : K₁ = L₁) (h₂ : K₂ = L₂) :
    HomologicalComplex.mapBifunctorMap (eqToHom h₁) (eqToHom h₂)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) = eqToHom (by subst h₁ h₂; rfl) := by
  subst h₁ h₂
  refine HomologicalComplex.hom_ext _ _ fun n => HomologicalComplex.mapBifunctor.hom_ext
    fun i j h => ?_
  simp

/-- The composite of the tensor products of two pairs of maps of complexes is the tensor product
of the composites. -/
@[reassoc]
theorem mapBifunctorMap_comp' {K₁ K₂ L₁ L₂ M₁ M₂ :
      CochainComplex (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) ℤ}
    (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    HomologicalComplex.mapBifunctorMap f₁ f₂ (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫
        HomologicalComplex.mapBifunctorMap g₁ g₂
          (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) =
      HomologicalComplex.mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) :=
  (mapBifunctorMap_comp O f₁ g₁ f₂ g₂).symm

/-- Conjugating a commutative square by identifications, stated with every object and morphism a
variable. -/
theorem conj_aux {C : Type*} [Category* C] {a b c d a' b' c' d' : C}
    (ea : a = a') (eb : b = b') (ec : c = c') (ed : d = d')
    (R : a' ⟶ b') (cupV : b' ⟶ d') (cupU : a' ⟶ c') (R' : c' ⟶ d') (h : R ≫ cupV = cupU ≫ R') :
    (eqToHom ea ≫ R ≫ eqToHom eb.symm) ≫ (eqToHom eb ≫ cupV ≫ eqToHom ed.symm) =
      (eqToHom ea ≫ cupU ≫ eqToHom ec.symm) ≫ (eqToHom ec ≫ R' ≫ eqToHom ed.symm) := by
  subst ea eb ec ed
  simpa using h

/-- The tensor bifunctor of complexes carries identities to identities. -/
@[simp]
theorem mapBifunctorMap_id (K L : CochainComplex (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 K) (𝟙 L)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) = 𝟙 _ := by
  have := mapBifunctorMap_eqToHom O (rfl : K = K) (rfl : L = L)
  simpa only [eqToHom_refl] using this

/-- Conjugating a commutative square of cup products by identifications, stated with every object
and morphism a variable. -/
theorem conj_cup_aux
    {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ x₆ y₆ :
      CochainComplex (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) ℤ}
    (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) (h₃ : x₃ = y₃) (h₄ : x₄ = y₄) (h₅ : x₅ = y₅) (h₆ : x₆ = y₆)
    (RF : y₁ ⟶ y₂) (RG : y₃ ⟶ y₄) (RH : y₅ ⟶ y₆)
    (cupU : HomologicalComplex.mapBifunctor y₁ y₃
      (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ⟶ y₅)
    (cupV : HomologicalComplex.mapBifunctor y₂ y₄
      (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ⟶ y₆)
    (h : HomologicalComplex.mapBifunctorMap RF RG
      (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cupV = cupU ≫ RH) :
    HomologicalComplex.mapBifunctorMap (eqToHom h₁ ≫ RF ≫ eqToHom h₂.symm)
        (eqToHom h₃ ≫ RG ≫ eqToHom h₄.symm) (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫
      (HomologicalComplex.mapBifunctorMap (eqToHom h₂) (eqToHom h₄)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cupV ≫ eqToHom h₆.symm) =
    (HomologicalComplex.mapBifunctorMap (eqToHom h₁) (eqToHom h₃)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cupU ≫ eqToHom h₅.symm) ≫
      (eqToHom h₅ ≫ RH ≫ eqToHom h₆.symm) := by
  subst h₁ h₂ h₃ h₄ h₅ h₆
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, mapBifunctorMap_id]
  exact h

section Refinement

variable {J : Type u} (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (c : J → I)
  (hc : ∀ j, V j ≤ U (c j))

/-- The refinement map of total Čech complexes of `𝒪_X`-modules, through `cech_obj_eq'`. -/
theorem cechRefinement_app_eq (K : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) :
    (Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app K =
      eqToHom (cech_obj_eq' O U hU K) ≫
        (Stacks.Cech.LinearCupProduct.totalCechRefinement (coverObject U hU) (coverObject V hV)
          (SectionRing (ringSheaf O) ⊤) c
          (Stacks.Cech.Refinement.coverRefinementHom U hU V hV c hc)).app
            ((Stacks.Cech.Refinement.sectionsComplex O).obj K) ≫
        eqToHom (cech_obj_eq' O V hV K).symm := by
  rw [Stacks.Cech.Refinement.cechRefinement_eq]
  simp only [NatTrans.comp_app, eqToHom_app, Functor.whiskerLeft_app]

/-- **The Čech cup product commutes with refinement.** -/
theorem cechCup_refinement {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) :
    HomologicalComplex.mapBifunctorMap
        ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app F.obj)
        ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app G.obj)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cechCup O V hV γ =
      cechCup O U hU γ ≫ (Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app H.obj := by
  rw [cechRefinement_app_eq, cechRefinement_app_eq, cechRefinement_app_eq]
  exact conj_cup_aux O (cech_obj_eq O U hU F) (cech_obj_eq O V hV F) (cech_obj_eq O U hU G)
    (cech_obj_eq O V hV G) (cech_obj_eq O U hU H) (cech_obj_eq O V hV H) _ _ _ _ _
    (Stacks.Cech.LinearCupProduct.cechCupProduct_refinement (coverObject U hU)
      (coverObject V hV) (SectionRing (ringSheaf O) ⊤) c
      (Stacks.Cech.Refinement.coverRefinementHom U hU V hV c hc) γ)

end Refinement

/-- Conjugating the naturality square of cup products by identifications, stated with every
object and morphism a variable. -/
theorem conj_cup_aux₂
    {x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ x₅ y₅ :
      CochainComplex (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) ℤ}
    (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) (h₃ : x₃ = y₃) (h₄ : x₄ = y₄) (h₅ : x₅ = y₅)
    (g : y₂ ⟶ y₃) (f : y₁ ⟶ y₄)
    (cup₁ : HomologicalComplex.mapBifunctor y₁ y₃
      (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ⟶ y₅)
    (cup₂ : HomologicalComplex.mapBifunctor y₄ y₂
      (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ⟶ y₅)
    (h : HomologicalComplex.mapBifunctorMap (𝟙 _) g
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cup₁ =
      HomologicalComplex.mapBifunctorMap f (𝟙 _)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cup₂) :
    HomologicalComplex.mapBifunctorMap (𝟙 x₁) (eqToHom h₂ ≫ g ≫ eqToHom h₃.symm)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫
      (HomologicalComplex.mapBifunctorMap (eqToHom h₁) (eqToHom h₃)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cup₁ ≫ eqToHom h₅.symm) =
    HomologicalComplex.mapBifunctorMap (eqToHom h₁ ≫ f ≫ eqToHom h₄.symm) (𝟙 x₂)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫
      (HomologicalComplex.mapBifunctorMap (eqToHom h₄) (eqToHom h₂)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cup₂ ≫ eqToHom h₅.symm) := by
  subst h₁ h₂ h₃ h₄ h₅
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, mapBifunctorMap_id]
  exact h

/-- **The Čech cup product is natural in the coefficients**: for morphisms `f : F₁ ⟶ F₂`,
`g : G₂ ⟶ G₁` and pairings `γ₁` of `(F₁, G₁)` and `γ₂` of `(F₂, G₂)` into `H` which agree on
`F₁ ⊗ G₂`, the two cup products agree on `Tot(Č(𝒰, F₁)) ⊗ Tot(Č(𝒰, G₂))`. -/
theorem cechCup_naturality {F₁ F₂ G₁ G₂ H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (f : F₁ ⟶ F₂) (g : G₂ ⟶ G₁) (γ₁ : Pairing O F₁ G₁ H) (γ₂ : Pairing O F₂ G₂ H)
    (h : ∀ a b n (hn : a + b = n),
      ((Stacks.Cech.LinearCupProduct.tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
          (((Stacks.Cech.Refinement.sectionsComplex O).obj F₁.obj).X a)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map g.hom).f b) ≫ γ₁.μ a b n hn =
        ((Stacks.Cech.LinearCupProduct.tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map f.hom).f a)).app
            (((Stacks.Cech.Refinement.sectionsComplex O).obj G₂.obj).X b) ≫ γ₂.μ a b n hn) :
    HomologicalComplex.mapBifunctorMap (𝟙 _) ((cech O U hU).map g.hom)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cechCup O U hU γ₁ =
      HomologicalComplex.mapBifunctorMap ((cech O U hU).map f.hom) (𝟙 _)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cechCup O U hU γ₂ := by
  rw [cech_map_eq, cech_map_eq]
  exact conj_cup_aux₂ O (cech_obj_eq O U hU F₁) (cech_obj_eq O U hU G₂) (cech_obj_eq O U hU G₁)
    (cech_obj_eq O U hU F₂) (cech_obj_eq O U hU H) _ _ _ _
    (Stacks.Cech.LinearCupProduct.cechCupProduct_naturality (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) ((Stacks.Cech.Refinement.sectionsComplex O).map f.hom)
      ((Stacks.Cech.Refinement.sectionsComplex O).map g.hom) γ₁ γ₂ h)

/-! ### The cup product of Čech classes -/

/-- The unit `1 ⊗ 1` of `A ⊗_A A`. -/
def unitTensor :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((tensorModules (SectionRing (ringSheaf O) ⊤)).obj (unitModule _)).obj (unitModule _) :=
  toMor ((1 : SectionRing (ringSheaf O) ⊤) ⊗ₜ[SectionRing (ringSheaf O) ⊤]
    (1 : SectionRing (ringSheaf O) ⊤))

/-- **The cup product of two Čech classes** relative to a pairing `γ`: the class of the Čech cup
product of cocycle representatives. -/
def cechCupClass {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) (p q t : ℤ) (ht : p + q = t)
    (x : unitModule _ ⟶ ((cech O U hU).obj F.obj).homology p)
    (y : unitModule _ ⟶ ((cech O U hU).obj G.obj).homology q) :
    unitModule _ ⟶ ((cech O U hU).obj H.obj).homology t :=
  unitTensor O ≫ Stacks.CupProduct.cupClass (tensorModules (SectionRing (ringSheaf O) ⊤))
    ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht x y ≫
      HomologicalComplex.homologyMap (cechCup O U hU γ) t

/-- The cup product of two Čech classes is computed by any cocycle representatives. -/
theorem cechCupClass_eq {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) (p q t : ℤ) (ht : p + q = t)
    (z : unitModule _ ⟶ ((cech O U hU).obj F.obj).X p)
    (hz : z ≫ ((cech O U hU).obj F.obj).d p (p + 1) = 0)
    (w : unitModule _ ⟶ ((cech O U hU).obj G.obj).X q)
    (hw : w ≫ ((cech O U hU).obj G.obj).d q (q + 1) = 0) :
    cechCupClass O U hU γ p q t ht (cocycleClass p z hz) (cocycleClass q w hw) =
      unitTensor O ≫ cocycleClass t (Stacks.CupProduct.cupPair
        (tensorModules (SectionRing (ringSheaf O) ⊤)) ((cech O U hU).obj F.obj)
          ((cech O U hU).obj G.obj) p q t ht z w ≫ (cechCup O U hU γ).f t)
        (Stacks.CupProduct.cupPair_comp_gamma_comp_d_eq_zero _ _ _ _ p q t ht z w hz hw) := by
  dsimp only [cechCupClass]
  congr 1
  exact (Stacks.CupProduct.liftCycles_cupPair_comp_gamma_homologyπ_eq_cupClass _ _ _ _ p q t ht
    _ _ z hz rfl w hw rfl).symm

/-- The cup product of cochains is natural in both complexes at once. -/
theorem cupPair_comp_mapBifunctorMap
    {K K' L L' : CochainComplex (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) ℤ}
    (φ : K ⟶ K') (ψ : L ⟶ L') {P Q : ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)}
    (p q t : ℤ) (ht : p + q = t) (z : P ⟶ K.X p) (w : Q ⟶ L.X q) :
    Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤)) K L p q t ht z w ≫
        (HomologicalComplex.mapBifunctorMap φ ψ
          (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ)).f t =
      Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤)) K' L' p q t ht
        (z ≫ φ.f p) (w ≫ ψ.f q) := by
  have e : HomologicalComplex.mapBifunctorMap φ ψ
      (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) =
      HomologicalComplex.mapBifunctorMap φ (𝟙 L) (tensorModules (SectionRing (ringSheaf O) ⊤))
        (up ℤ) ≫ HomologicalComplex.mapBifunctorMap (𝟙 K') ψ
          (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) := by
    rw [mapBifunctorMap_comp', Category.comp_id, Category.id_comp]
  rw [e, HomologicalComplex.comp_f, ← Category.assoc,
    Stacks.CupProduct.cupPair_comp_mapBifunctorMap_left,
    Stacks.CupProduct.cupPair_comp_mapBifunctorMap_right]

section Refinement

variable {J : Type u} (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (c : J → I)
  (hc : ∀ j, V j ≤ U (c j))

/-- **The cup product of Čech classes commutes with refinement.** -/
theorem cechCupClass_refinement
    {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) (p q t : ℤ) (ht : p + q = t)
    (x : unitModule _ ⟶ ((cech O U hU).obj F.obj).homology p)
    (y : unitModule _ ⟶ ((cech O U hU).obj G.obj).homology q) :
    cechCupClass O U hU γ p q t ht x y ≫ HomologicalComplex.homologyMap
        ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app H.obj) t =
      cechCupClass O V hV γ p q t ht
        (x ≫ HomologicalComplex.homologyMap
          ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app F.obj) p)
        (y ≫ HomologicalComplex.homologyMap
          ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app G.obj) q) := by
  obtain ⟨z, hz, hzx⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj F.obj) p (p + 1) (CochainComplex.next ℤ p) x
  obtain ⟨w, hw, hwy⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj G.obj) q (q + 1) (CochainComplex.next ℤ q) y
  obtain rfl : x = cocycleClass p z hz := hzx.symm
  obtain rfl : y = cocycleClass q w hw := hwy.symm
  rw [cocycleClass_comp_homologyMap, cocycleClass_comp_homologyMap, cechCupClass_eq,
    cechCupClass_eq, Category.assoc, cocycleClass_comp_homologyMap]
  congr 1
  refine cocycleClass_congr t ?_ _ _
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← cechCup_refinement,
    HomologicalComplex.comp_f, ← Category.assoc, cupPair_comp_mapBifunctorMap]

end Refinement

/-- The cup product of Čech classes followed by the class in hypercohomology does not change
under refinement. -/
theorem cechCupClass_cechClass_refinement {J : Type u} (V : J → Opens X) (hV : ⊤ = ⨆ j, V j)
    (c : J → I) (hc : ∀ j, V j ≤ U (c j))
    {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) (p q t : ℤ) (ht : p + q = t)
    (x : unitModule _ ⟶ ((cech O U hU).obj F.obj).homology p)
    (y : unitModule _ ⟶ ((cech O U hU).obj G.obj).homology q) :
    cechCupClass O U hU γ p q t ht x y ≫ cechClass O U hU H t =
      cechCupClass O V hV γ p q t ht
        (x ≫ HomologicalComplex.homologyMap
          ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app F.obj) p)
        (y ≫ HomologicalComplex.homologyMap
          ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app G.obj) q) ≫
        cechClass O V hV H t := by
  rw [← cechCupClass_refinement, Category.assoc, cechClass_refinement]

/-- A Čech representative of a class of `Hⁿ(X, K)`. -/
structure CechRep (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ)
    (a : hypercohomology O K n) where
  /-- The index type of the covering. -/
  I : Type u
  /-- The covering. -/
  U : I → Opens X
  hU : ⊤ = ⨆ i, U i
  /-- The Čech class. -/
  z : ((cech O U hU).obj K.obj).homology n
  hz : cechClass O U hU K n z = a

/-- A chosen Čech representative of a class, when Čech cohomology computes cohomology. -/
def CechComputes.rep {K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (h : CechComputes O K) (n : ℤ) (a : hypercohomology O K n) : CechRep O K n a :=
  Classical.choice (by
    obtain ⟨I, U, hU, z, hz⟩ := (h n).1 a
    exact ⟨⟨I, U, hU, z, hz⟩⟩)

/-- **The cup product `γ(a ∪ b) ∈ Hᵗ(X, H)`** of classes `a ∈ Hᵖ(X, F)` and `b ∈ Hᵠ(X, G)`, for a
pairing `γ` of `F` and `G` into `H` and `p + q = t`, when Čech cohomology computes the cohomology
of `F` and of `G` ([Stacks, Section 01FP]): represent `a` and `b` by Čech classes on a common
covering and take the class of their Čech cup product of [Stacks, Tag 07MB].  By `cup_eq` the
result does not depend on the representatives. -/
def cup {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) (a : hypercohomology O F p) (b : hypercohomology O G q) :
    hypercohomology O H t :=
  let ra := CechComputes.rep O hF p a
  let rb := CechComputes.rep O hG q b
  let hW := iSup_inf_eq_top ra.U ra.hU rb.U rb.hU
  (cechCupClass O _ hW γ p q t ht
    (toMor ra.z ≫ HomologicalComplex.homologyMap
      ((Stacks.Cech.Refinement.cechRefinement O ra.U ra.hU _ hW Prod.fst
        (fun _ => inf_le_left)).app F.obj) p)
    (toMor rb.z ≫ HomologicalComplex.homologyMap
      ((Stacks.Cech.Refinement.cechRefinement O rb.U rb.hU _ hW Prod.snd
        (fun _ => inf_le_right)).app G.obj) q) ≫
    cechClass O _ hW H t) (1 : SectionRing (ringSheaf O) ⊤)

/-- Two Čech classes with the same image in hypercohomology agree after refinement, when Čech
cohomology computes the cohomology of the complex. -/
theorem exists_refinement_eq {K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hK : CechComputes O K) (n : ℤ)
    (x x' : unitModule _ ⟶ ((cech O U hU).obj K.obj).homology n)
    (h : x ≫ cechClass O U hU K n = x' ≫ cechClass O U hU K n) :
    ∃ (J : Type u) (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (c : J → I) (hc : ∀ j, V j ≤ U (c j)),
      x ≫ HomologicalComplex.homologyMap
          ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app K.obj) n =
        x' ≫ HomologicalComplex.homologyMap
          ((Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc).app K.obj) n := by
  obtain ⟨J, V, hV, c, hc, h0⟩ := (hK n).2 I U hU ((x - x') (1 : SectionRing (ringSheaf O) ⊤))
    (by rw [← ConcreteCategory.comp_apply, Preadditive.sub_comp, h, sub_self]; rfl)
  refine ⟨J, V, hV, c, hc, ?_⟩
  rw [← sub_eq_zero, ← Preadditive.sub_comp, ← toMor_apply ((x - x') ≫ _),
    ConcreteCategory.comp_apply, h0]
  ext : 1
  exact LinearMap.ext_ring (by simp [toMor])

/-- **The cup product of Čech representatives does not depend on the representatives**, when
Čech cohomology computes the cohomology of `F` and of `G`. -/
theorem cechCupClass_cechClass_eq {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) {I' : Type u} (U' : I' → Opens X) (hU' : ⊤ = ⨆ i, U' i)
    (x : unitModule _ ⟶ ((cech O U hU).obj F.obj).homology p)
    (y : unitModule _ ⟶ ((cech O U hU).obj G.obj).homology q)
    (x' : unitModule _ ⟶ ((cech O U' hU').obj F.obj).homology p)
    (y' : unitModule _ ⟶ ((cech O U' hU').obj G.obj).homology q)
    (hx : x ≫ cechClass O U hU F p = x' ≫ cechClass O U' hU' F p)
    (hy : y ≫ cechClass O U hU G q = y' ≫ cechClass O U' hU' G q) :
    cechCupClass O U hU γ p q t ht x y ≫ cechClass O U hU H t =
      cechCupClass O U' hU' γ p q t ht x' y' ≫ cechClass O U' hU' H t := by
  have hW := iSup_inf_eq_top U hU U' hU'
  -- a common refinement on which the representatives of `a` agree
  obtain ⟨J₁, V₁, hV₁, c₁, hc₁, hx₁⟩ := exists_refinement_eq O _ hW hF p
    (x ≫ HomologicalComplex.homologyMap ((Stacks.Cech.Refinement.cechRefinement O U hU _ hW
      Prod.fst (fun _ => inf_le_left)).app F.obj) p)
    (x' ≫ HomologicalComplex.homologyMap ((Stacks.Cech.Refinement.cechRefinement O U' hU' _ hW
      Prod.snd (fun _ => inf_le_right)).app F.obj) p)
    (by rw [Category.assoc, Category.assoc, cechClass_refinement, cechClass_refinement, hx])
  -- a further refinement on which the representatives of `b` agree
  obtain ⟨J₂, V₂, hV₂, c₂, hc₂, hy₂⟩ := exists_refinement_eq O _ hV₁ hG q
    ((y ≫ HomologicalComplex.homologyMap ((Stacks.Cech.Refinement.cechRefinement O U hU _ hW
      Prod.fst (fun _ => inf_le_left)).app G.obj) q) ≫ HomologicalComplex.homologyMap
        ((Stacks.Cech.Refinement.cechRefinement O _ hW V₁ hV₁ c₁ hc₁).app G.obj) q)
    ((y' ≫ HomologicalComplex.homologyMap ((Stacks.Cech.Refinement.cechRefinement O U' hU' _ hW
      Prod.snd (fun _ => inf_le_right)).app G.obj) q) ≫ HomologicalComplex.homologyMap
        ((Stacks.Cech.Refinement.cechRefinement O _ hW V₁ hV₁ c₁ hc₁).app G.obj) q)
    (by simp only [Category.assoc, cechClass_refinement]; exact hy)
  rw [cechCupClass_cechClass_refinement O U hU _ hW Prod.fst (fun _ => inf_le_left),
    cechCupClass_cechClass_refinement O U' hU' _ hW Prod.snd (fun _ => inf_le_right)]
  simp only [cechCupClass_cechClass_refinement O _ hW V₁ hV₁ c₁ hc₁,
    cechCupClass_cechClass_refinement O _ hV₁ V₂ hV₂ c₂ hc₂, hx₁, hy₂]

/-- **The cup product is computed by any Čech representatives on a common covering.** -/
theorem cup_eq {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) (x : ((cech O U hU).obj F.obj).homology p)
    (y : ((cech O U hU).obj G.obj).homology q) :
    cup O hF hG γ p q t ht (cechClass O U hU F p x) (cechClass O U hU G q y) =
      (cechCupClass O U hU γ p q t ht (toMor x) (toMor y) ≫ cechClass O U hU H t)
        (1 : SectionRing (ringSheaf O) ⊤) := by
  dsimp only [cup]
  rw [cechCupClass_cechClass_eq O _ _ hF hG γ p q t ht U hU _ _ (toMor x) (toMor y)
    (by rw [Category.assoc, cechClass_refinement, toMor_comp, toMor_comp, CechRep.hz])
    (by rw [Category.assoc, cechClass_refinement, toMor_comp, toMor_comp, CechRep.hz])]

end Stacks.Cech.Hypercohomology
