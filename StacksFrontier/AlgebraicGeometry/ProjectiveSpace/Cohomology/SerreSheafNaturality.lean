module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreSheafMultiplication
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplexFunctor

/-!
# Naturality of the Čech computation of the cohomology of projective space

For an open covering `𝒰` of a ringed space `X` and a morphism `φ : ℱ → 𝒢` of `𝒪_X`-modules, the
identifications of Čech cohomology with the explicit Čech complex, with the alternating and the
ordered Čech complexes ([Stacks, Tag 01FG] and [Stacks, Tag 01FJ]), and the map from Čech
cohomology to sheaf cohomology for a covering by acyclic opens ([Stacks, Tag 01EV]) commute with
the maps induced by `φ`.

On `ℙⁿ_R = Proj R[T₀, …, Tₙ]` with the standard covering by the `D₊(Tᵢ)`, this gives the
naturality in morphisms `𝒪(d) → 𝒪(e)` of the identification of `Hᵖ(ℙⁿ_R, 𝒪(d))` with the homology
of the ordered Čech complex of `𝒪(d)`.

## Main results

* `Stacks.Cohomology.CechSheaf.orderedCechHomologyModuleIso_naturality`: the ordered Čech
  homology of `ℱ` is natural in `ℱ`.
* `Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived_naturality`: the identification of Čech
  homology with sheaf cohomology for an acyclic covering is natural in the sheaf.
* `Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoOrderedHomology_naturality`: the
  identification of `Hᵖ(ℙⁿ_R, 𝒪(d))` with ordered Čech homology is natural in `𝒪(d) → 𝒪(e)`.

-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.Basis (res res_app)

universe uX uR uM u

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] AddCommGrpCat.hasLimitsOfSize
attribute [local implicit_reducible] CechCochains.Cochain
attribute [local implicit_reducible] CechCochains.OrdCochain
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.cechComplex

/-! ### Two pasting lemmas -/

/-- A commuting square followed by a pair of isomorphisms, stated on variables. -/
theorem sq_comp_inv {C : Type*} [Category* C] {A A' B B' D D' : C} (f : A ⟶ A')
    (g : A ⟶ B) (g' : A' ⟶ B') (h : B ⟶ B') (e : D ≅ B) (e' : D' ≅ B') (k : D ⟶ D')
    (h₁ : f ≫ g' = g ≫ h) (h₂ : k ≫ e'.hom = e.hom ≫ h) :
    f ≫ g' ≫ e'.inv = (g ≫ e.inv) ≫ k := by
  rw [← cancel_mono e'.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, h₂, Category.assoc, Iso.inv_hom_id_assoc, h₁]

/-- Two commuting squares of complexes pasted, read on homology, stated on variables. -/
theorem homologyMap_sq {C : Type*} [Category* C] [HasZeroMorphisms C] {κ : Type*}
    {c : ComplexShape κ} {K₁ K₂ L₁ L₂ M₁ M₂ : HomologicalComplex C c} (a : K₁ ⟶ K₂)
    (b₁ : K₁ ⟶ L₁) (b₂ : K₂ ⟶ L₂) (c₁ : L₁ ⟶ M₁) (c₂ : L₂ ⟶ M₂) (m : M₁ ⟶ M₂)
    (h : a ≫ b₂ ≫ c₂ = b₁ ≫ c₁ ≫ m) (p : κ) [K₁.HasHomology p] [K₂.HasHomology p]
    [L₁.HasHomology p] [L₂.HasHomology p] [M₁.HasHomology p] [M₂.HasHomology p] :
    HomologicalComplex.homologyMap a p ≫
        (HomologicalComplex.homologyMap b₂ p ≫ HomologicalComplex.homologyMap c₂ p) =
      (HomologicalComplex.homologyMap b₁ p ≫ HomologicalComplex.homologyMap c₁ p) ≫
        HomologicalComplex.homologyMap m p := by
  simp only [← HomologicalComplex.homologyMap_comp, Category.assoc, h]

/-- Three commuting squares pasted side by side, stated on variables. -/
theorem paste_three {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : C}
    (a : A₀ ⟶ B₀) (b : A₁ ⟶ B₁) (c : A₂ ⟶ B₂) (d : A₃ ⟶ B₃)
    (f₁ : A₀ ⟶ A₁) (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃) (g₁ : B₀ ⟶ B₁) (g₂ : B₁ ⟶ B₂) (g₃ : B₂ ⟶ B₃)
    (h₁ : a ≫ g₁ = f₁ ≫ b) (h₂ : b ≫ g₂ = f₂ ≫ c) (h₃ : c ≫ g₃ = f₃ ≫ d) :
    a ≫ (g₁ ≫ g₂ ≫ g₃) = (f₁ ≫ f₂ ≫ f₃) ≫ d := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

/-- Two commuting squares pasted side by side, stated on variables. -/
theorem paste_two {C : Type*} [Category* C] {A₀ A₁ A₂ B₀ B₁ B₂ : C}
    (a : A₀ ⟶ B₀) (b : A₁ ⟶ B₁) (c : A₂ ⟶ B₂) (f₁ : A₀ ⟶ A₁) (f₂ : A₁ ⟶ A₂) (g₁ : B₀ ⟶ B₁)
    (g₂ : B₁ ⟶ B₂) (h₁ : a ≫ g₁ = f₁ ≫ b) (h₂ : b ≫ g₂ = f₂ ≫ c) :
    a ≫ (g₁ ≫ g₂) = (f₁ ≫ f₂) ≫ c := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- A commuting square of isomorphisms, inverted, stated on variables. -/
theorem sq_inv {C : Type*} [Category* C] {A A' B B' : C} (f : A ⟶ A') (h : B ⟶ B')
    (e : A ≅ B) (e' : A' ≅ B') (w : f ≫ e'.hom = e.hom ≫ h) : h ≫ e'.inv = e.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]

namespace Stacks.Cohomology.CechSheaf

variable {X : Type uX} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{uR}}
  {ι : Type uM}
  (V : Opens X) (U : ι → Opens X) (hU : V = ⨆ i, U i) {I J K : SheafOfModules.{uM} R}

/-- A morphism of sheaves of modules, acting on the abelian presheaves of sections. -/
abbrev abSectionsMap (φ : I ⟶ J) : abSections I ⟶ abSections J :=
  (PresheafOfModules.toPresheaf _).map φ.val

/-- A morphism of sheaves of modules is `R(V)`-linear on the sections over an open contained in
`V`. -/
theorem abSectionsMap_smul (φ : I ⟶ J) {W : Opens X} (h : W ≤ V) (a : SectionRing R V)
    (t : ToType ((abSections I).obj (op W))) :
    letI := sectionsModuleOfLE V I h
    letI := sectionsModuleOfLE V J h
    ConcreteCategory.hom ((abSectionsMap φ).app (op W)) (a • t) =
      a • ConcreteCategory.hom ((abSectionsMap φ).app (op W)) t :=
  let := sectionsModuleOfLE V I h
  let := sectionsModuleOfLE V J h
  map_smul (((sectionsPresheafFunctor V).map φ).app (op (Over.mk (homOfLE h)))).hom a t

/-! ### A morphism of sheaves of modules on the explicit Čech complexes -/

/-- A morphism of sheaves of modules acting on the degree-`p` Čech cochains, `R(V)`-linearly. -/
def cochainModuleMap (φ : I ⟶ J) (p : ℕ) :
    cechCochainModuleObj V U hU I p ⟶ cechCochainModuleObj V U hU J p :=
  letI := cochainModule V U hU I p
  letI := cochainModule V U hU J p
  ModuleCat.ofHom
    { toFun := Stacks.Cech.cochainMap (X := TopCat.of X) U (abSectionsMap φ) p
      map_add' := map_add _
      map_smul' := fun a s => funext fun i =>
        abSectionsMap_smul V φ (cechInter_le_covered V U hU i) a (s i) }

/-- The action of a morphism on Čech cochains, componentwise. -/
theorem cochainModuleMap_apply (φ : I ⟶ J) (p : ℕ)
    (s : CechCochains.Cochain (X := TopCat.of X) U (abSections I) p) (i : Fin (p + 1) → ι) :
    ConcreteCategory.hom (cochainModuleMap V U hU φ p) s i =
      ConcreteCategory.hom ((abSectionsMap φ).app (op (CechCochains.inter (X := TopCat.of X) U i)))
        (s i) :=
  rfl

/-- **A morphism of sheaves of modules induces a morphism of the explicit Čech complexes of
`R(V)`-modules.** -/
def cechModuleMap (φ : I ⟶ J) : cechModuleComplex V U hU I ⟶ cechModuleComplex V U hU J :=
  CochainComplex.ofHom (cochainModuleMap V U hU φ) fun p => by
    rw [cechModuleComplex_d, cechModuleComplex_d]
    ext s
    exact (Stacks.Cech.cochainMap_cechD (X := TopCat.of X) U (abSectionsMap φ) p s).symm

/-- The degree-`p` component of `cechModuleMap`. -/
@[simp]
theorem cechModuleMap_f (φ : I ⟶ J) (p : ℕ) :
    (cechModuleMap V U hU φ).f p = cochainModuleMap V U hU φ p := rfl

/-- A morphism of sheaves of modules acting on the degree-`p` alternating Čech cochains. -/
def alternatingCochainModuleMap (φ : I ⟶ J) (p : ℕ) :
    alternatingCochainModuleObj V U hU I p ⟶ alternatingCochainModuleObj V U hU J p :=
  letI := cochainModule V U hU I p
  letI := cochainModule V U hU J p
  ModuleCat.ofHom (LinearMap.restrict (cochainModuleMap V U hU φ p).hom fun _ hs =>
    Stacks.Cech.cochainMap_isAlternating (X := TopCat.of X) U (abSectionsMap φ) p hs)

/-- **A morphism of sheaves of modules induces a morphism of the alternating Čech complexes of
`R(V)`-modules.** -/
def alternatingModuleMap (φ : I ⟶ J) :
    alternatingModuleComplex V U hU I ⟶ alternatingModuleComplex V U hU J :=
  CochainComplex.ofHom (alternatingCochainModuleMap V U hU φ) fun p => by
    rw [alternatingModuleComplex_d, alternatingModuleComplex_d]
    ext s
    exact Subtype.ext
      (Stacks.Cech.cochainMap_cechD (X := TopCat.of X) U (abSectionsMap φ) p s.1).symm

/-- The inclusion of the alternating Čech complex is natural in the sheaf of modules. -/
theorem alternatingModuleInclusion_naturality (φ : I ⟶ J) :
    alternatingModuleMap V U hU φ ≫ alternatingModuleInclusion V U hU J =
      alternatingModuleInclusion V U hU I ≫ cechModuleMap V U hU φ := by
  ext p s
  rfl

/-- Taking the components of a cochain of the slice model is natural in the sheaf of modules. -/
theorem toCochainFun_map (φ : I ⟶ J) {n : ℕ}
    (s : ToType (((cechComplexFunctor (coverObject U hU)).obj (sectionsPresheaf V I)).X n))
    (x : Fin (n + 1) → ι) :
    toCochainFun V U hU J
        (ConcreteCategory.hom (((cechComplexFunctorOfCover V U hU).map φ).f n) s) x =
      ConcreteCategory.hom ((abSectionsMap φ).app (op (CechCochains.inter (X := TopCat.of X) U x)))
        (toCochainFun V U hU I s x) := by
  have hπ : rawcomp V U hU J
      (ConcreteCategory.hom (((cechComplexFunctorOfCover V U hU).map φ).f n) s) x =
      ConcreteCategory.hom ((abSectionsMap φ).app (op (inter (coverObject U hU) x).left))
        (rawcomp V U hU I s x) :=
    ConcreteCategory.congr_hom
      (cech_map_comp_π (coverObject U hU) ((sectionsPresheafFunctor V).map φ) n x) s
  exact (congrArg (fun z => res (abSections J)
      (Stacks.Cech.cechComplexInter_eq (X := TopCat.of X) U x).ge
      (res (abSections J) (inter_coverObject_left V U hU x).ge z)) hπ).trans
    (by rw [res_app, res_app]; rfl)

/-- **The identification of the slice model with the explicit Čech complex is natural in the
sheaf of modules.** -/
theorem cechComplexModuleIso_naturality (φ : I ⟶ J) :
    (cechComplexFunctorOfCover V U hU).map φ ≫ (cechComplexModuleIso V U hU J).hom =
      (cechComplexModuleIso V U hU I).hom ≫ cechModuleMap V U hU φ := by
  ext n s
  exact funext fun x => toCochainFun_map V U hU φ s x

section Ordered

variable [LinearOrder ι]

/-- The ordered Čech differential commutes with a morphism of abelian presheaves. -/
theorem ordD_app {F G : (Opens (TopCat.of X))ᵒᵖ ⥤ AddCommGrpCat.{uM}} (a : F ⟶ G) (p : ℕ)
    (s : CechCochains.OrdCochain (X := TopCat.of X) U F p)
    (i : CechCochains.OrdIndex (I := ι) (p + 1)) :
    ConcreteCategory.hom (a.app (op (CechCochains.inter (X := TopCat.of X) U i.1)))
        (CechCochains.ordD (X := TopCat.of X) U F p s i) =
      CechCochains.ordD (X := TopCat.of X) U G p
        (fun k => ConcreteCategory.hom
          (a.app (op (CechCochains.inter (X := TopCat.of X) U k.1))) (s k)) i := by
  show ConcreteCategory.hom (a.app (op (CechCochains.inter (X := TopCat.of X) U i.1)))
      (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr F (CechCochains.inter_le_omit U i.1 j)
          (s ⟨i.1 ∘ j.succAbove, CechCochains.strictMono_omit i.2 j⟩)) =
    ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      CechCochains.restr G (CechCochains.inter_le_omit U i.1 j)
        (ConcreteCategory.hom (a.app _)
          (s ⟨i.1 ∘ j.succAbove, CechCochains.strictMono_omit i.2 j⟩))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, Stacks.Cech.restr_app a (CechCochains.inter_le_omit U i.1 j)]

/-- A morphism of sheaves of modules acting on the degree-`p` ordered Čech cochains,
`R(V)`-linearly. -/
def ordCochainModuleMap (φ : I ⟶ J) (p : ℕ) :
    ordCochainModuleObj V U hU I p ⟶ ordCochainModuleObj V U hU J p :=
  letI := ordCochainModule V U hU I p
  letI := ordCochainModule V U hU J p
  ModuleCat.ofHom
    { toFun := fun s k => ConcreteCategory.hom
        ((abSectionsMap φ).app (op (CechCochains.inter (X := TopCat.of X) U k.1))) (s k)
      map_add' := fun s t => funext fun k => map_add _ (s k) (t k)
      map_smul' := fun a s => funext fun k =>
        abSectionsMap_smul V φ (cechInter_le_covered V U hU k.1) a (s k) }

/-- The action of a morphism on ordered Čech cochains, componentwise. -/
theorem ordCochainModuleMap_apply (φ : I ⟶ J) (p : ℕ)
    (s : CechCochains.OrdCochain (X := TopCat.of X) U (abSections I) p)
    (k : CechCochains.OrdIndex (I := ι) p) :
    ConcreteCategory.hom (ordCochainModuleMap V U hU φ p) s k =
      ConcreteCategory.hom
        ((abSectionsMap φ).app (op (CechCochains.inter (X := TopCat.of X) U k.1))) (s k) :=
  rfl

/-- **A morphism of sheaves of modules induces a morphism of the ordered Čech complexes of
`R(V)`-modules.** -/
def orderedModuleMap (φ : I ⟶ J) :
    orderedModuleComplex V U hU I ⟶ orderedModuleComplex V U hU J :=
  CochainComplex.ofHom (ordCochainModuleMap V U hU φ) fun p => by
    rw [orderedModuleComplex_d, orderedModuleComplex_d]
    ext s
    exact funext fun i => (ordD_app U (abSectionsMap φ) p s i).symm

/-- The degree-`p` component of `orderedModuleMap`. -/
@[simp]
theorem orderedModuleMap_f (φ : I ⟶ J) (p : ℕ) :
    (orderedModuleMap V U hU φ).f p = ordCochainModuleMap V U hU φ p := rfl

/-- The comparison of Tag 01FJ between the ordered and the alternating Čech complex of
`R(V)`-modules is natural in the sheaf of modules. -/
theorem orderedIsoAlternatingModuleComplex_naturality (φ : I ⟶ J) :
    orderedModuleMap V U hU φ ≫ (orderedIsoAlternatingModuleComplex V U hU J).hom =
      (orderedIsoAlternatingModuleComplex V U hU I).hom ≫ alternatingModuleMap V U hU φ := by
  refine sq_inv _ _ (alternatingIsoOrderedModuleComplex V U hU I)
    (alternatingIsoOrderedModuleComplex V U hU J) ?_
  ext p s
  rfl

omit [LinearOrder ι] in
/-- The `R(V)`-linear inclusion of the alternating Čech complex into the slice model is natural
in the sheaf of modules. -/
theorem alternatingInclusionToCechComplex_naturality (φ : I ⟶ J) :
    alternatingModuleMap V U hU φ ≫ alternatingInclusionToCechComplex V U hU J =
      alternatingInclusionToCechComplex V U hU I ≫ (cechComplexFunctorOfCover V U hU).map φ :=
  sq_comp_inv _ _ _ _ _ _ _ (alternatingModuleInclusion_naturality V U hU φ)
    (cechComplexModuleIso_naturality V U hU φ)

/-- **The module-valued Čech cohomology of the cover, computed by the ordered Čech complex, is
natural in the sheaf of modules.** -/
theorem orderedCechHomologyModuleIso_naturality (φ : I ⟶ J) (p : ℕ) :
    HomologicalComplex.homologyMap (orderedModuleMap V U hU φ) p ≫
        (orderedCechHomologyModuleIso V U hU J p).hom =
      (orderedCechHomologyModuleIso V U hU I p).hom ≫
        HomologicalComplex.homologyMap ((cechComplexFunctorOfCover V U hU).map φ) p :=
  homologyMap_sq _ _ _ _ _ _ (by
    rw [← Category.assoc, orderedIsoAlternatingModuleComplex_naturality, Category.assoc,
      alternatingInclusionToCechComplex_naturality]
    rfl) p

/-- The comparison of the ordered Čech complex with the slice model, the composite of
Tag 01FJ and of the inclusion of the alternating cochains. -/
abbrev orderedToCechComplex (M : SheafOfModules.{uM} R) :
    orderedModuleComplex V U hU M ⟶ cechComplex.{uX, uR, uM, uM} V U hU M :=
  (orderedIsoAlternatingModuleComplex V U hU M).hom ≫ alternatingInclusionToCechComplex V U hU M

/-- The value of the comparison of Tag 01FJ on an ordered cochain is its signed extension. -/
theorem coe_orderedIsoAlternating_hom_f (M : SheafOfModules.{uM} R) (p : ℕ)
    (t : CechCochains.OrdCochain (X := TopCat.of X) U (abSections M) p) :
    (show alternatingSubmodule V U hU M p from
        ConcreteCategory.hom ((orderedIsoAlternatingModuleComplex V U hU M).hom.f p) t).1 =
      CechCochains.c (X := TopCat.of X) U (abSections M) p t := by
  have h : (cLinearEquiv V U hU M p).symm t =
      ⟨CechCochains.c (X := TopCat.of X) U (abSections M) p t,
        CechCochains.c_isAlternating (X := TopCat.of X) U (abSections M) p t⟩ := by
    refine (cLinearEquiv V U hU M p).injective ?_
    rw [LinearEquiv.apply_symm_apply]
    exact (CechCochains.pi_c (X := TopCat.of X) U (abSections M) p t).symm
  exact congrArg Subtype.val h

/-- **The comparison of the ordered Čech complex with the slice model, on explicit cochains.**
The components of the image of an ordered cochain are those of its signed extension. -/
theorem toCochainFun_orderedToCechComplex (M : SheafOfModules.{uM} R) (p : ℕ)
    (t : CechCochains.OrdCochain (X := TopCat.of X) U (abSections M) p) :
    toCochainFun V U hU M (ConcreteCategory.hom ((orderedToCechComplex V U hU M).f p) t) =
      CechCochains.c (X := TopCat.of X) U (abSections M) p t := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun φ => HomologicalComplex.Hom.f φ p) (cechComplexModuleIso V U hU M).inv_hom_id)
    (ConcreteCategory.hom ((alternatingModuleInclusion V U hU M).f p)
      (ConcreteCategory.hom ((orderedIsoAlternatingModuleComplex V U hU M).hom.f p) t))
  exact h.trans (coe_orderedIsoAlternating_hom_f V U hU M p t)

/-- The comparison of the ordered Čech complex with the slice model is injective in every
degree. -/
theorem orderedToCechComplex_f_injective (M : SheafOfModules.{uM} R) (p : ℕ) :
    Function.Injective (ConcreteCategory.hom ((orderedToCechComplex V U hU M).f p)) := by
  intro t t' h
  have h' := congrArg (toCochainFun V U hU M) h
  rw [toCochainFun_orderedToCechComplex V U hU M, toCochainFun_orderedToCechComplex V U hU M] at h'
  rw [← CechCochains.pi_c (X := TopCat.of X) U (abSections M) p t,
    ← CechCochains.pi_c (X := TopCat.of X) U (abSections M) p t', h']

/-- The comparison of the ordered Čech complex with the slice model induces, on homology, the
module-valued comparison of Tags 01FJ and 01FM. -/
theorem orderedCechHomologyModuleIso_hom (M : SheafOfModules.{uM} R) (p : ℕ) :
    (orderedCechHomologyModuleIso V U hU M p).hom =
      HomologicalComplex.homologyMap (orderedToCechComplex V U hU M) p := by
  rw [HomologicalComplex.homologyMap_comp]
  rfl

end Ordered

end Stacks.Cohomology.CechSheaf

namespace Stacks.Cohomology.CechIso

open Stacks.Cohomology.CechSheaf Stacks.Cohomology.CechDerived

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u}) {ι : Type u} (U : X.Opens) (Ui : ι → X.Opens) (hU : U = ⨆ i, Ui i)
  (haffine : ∀ (r : ℕ) (s : Fin (r + 1) → ι), IsAffineOpen (⨅ k, Ui (s k)))
  {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]

omit [SheafOfModules.IsQuasicoherent F] [SheafOfModules.IsQuasicoherent F'] in
/-- The identification of Čech cohomology presented in the bounded-below derived category with
the homology of the explicit Čech complex is natural in the sheaf of modules. -/
theorem cechPlusHomologyIso_naturality (φ : F ⟶ F') (p : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} (SectionRing X.ringCatSheaf U))
          (p : ℤ)).map
        (DerivedCategory.Plus.Q.map ((cechComplexPlusFunctor X.ringCatSheaf U Ui hU).map φ)) ≫
      (Stacks.Cohomology.CechVanishing.cechPlusHomologyIso X.ringCatSheaf U Ui hU F' p).hom =
    (Stacks.Cohomology.CechVanishing.cechPlusHomologyIso X.ringCatSheaf U Ui hU F p).hom ≫
      HomologicalComplex.homologyMap ((cechComplexFunctorOfCover U Ui hU).map φ) p := by
  have h₁ := DerivedCategory.homologyFunctorFactors_hom_naturality
    ((cechComplexIntFunctor X.ringCatSheaf U Ui hU).map φ) (p : ℤ)
  have h₂ := HomologicalComplex.extendHomologyIso_hom_naturality
    ((cechComplexFunctorOfCover U Ui hU).map φ) ComplexShape.embeddingUpNat
    (j := p) (j' := (p : ℤ)) (by simp)
  exact paste_two _ _ _ _ _ _ _ h₁ h₂

/-- **The comparison of [Stacks, Tag 01XD] between sheaf cohomology and the homology of the
explicit Čech complex of a covering with affine finite intersections is natural in the
quasi-coherent module.** A morphism `φ : F ⟶ F'` induces on the cohomology the map that the
morphism of Čech complexes it induces induces on homology. -/
theorem cechHomologyIsoRightDerived_naturality (φ : F ⟶ F') (p : ℕ) :
    ((Stacks.Cohomology.sectionsFunctor X U).rightDerived p).map φ ≫
        (cechHomologyIsoRightDerived X U Ui hU haffine F' p).hom =
      (cechHomologyIsoRightDerived X U Ui hU haffine F p).hom ≫
        HomologicalComplex.homologyMap ((cechComplexFunctorOfCover U Ui hU).map φ) p := by
  have hiso : ∀ G : X.Modules, [G.IsQuasicoherent] →
      IsIso ((cechCohomologyToCohomology X.ringCatSheaf U Ui hU (p : ℤ)).app G) :=
    fun G _ => Stacks.Cohomology.Affine.isIso_cechCohomologyToCohomology_of_isAffineOpen X U Ui
      hU haffine G p
  have h₁ := (Stacks.DerivedIndexing.rightDerivedIso
    (Stacks.Cohomology.sectionsFunctor X U) p).hom.naturality φ
  have h₂ := sq_inv _ _
    (@asIso _ _ _ _ ((cechCohomologyToCohomology X.ringCatSheaf U Ui hU (p : ℤ)).app F)
      (hiso F))
    (@asIso _ _ _ _ ((cechCohomologyToCohomology X.ringCatSheaf U Ui hU (p : ℤ)).app F')
      (hiso F'))
    ((cechCohomologyToCohomology X.ringCatSheaf U Ui hU (p : ℤ)).naturality φ)
  exact paste_three _ _ _ _ _ _ _ _ _ _ h₁ h₂ (cechPlusHomologyIso_naturality X U Ui hU φ p)

end Stacks.Cohomology.CechIso


namespace Stacks.Homology.RestrictScalars

/-- **Restriction of scalars commutes with homology, naturally in the complex.** -/
theorem restrictScalarsHomologyIso_naturality {R S : Type u} [Ring R] [Ring S] (φ : R →+* S)
    {K L : CochainComplex (ModuleCat.{u} S) ℕ} (g : K ⟶ L) (q : ℕ) :
    HomologicalComplex.homologyMap
          (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (ComplexShape.up ℕ)).map g) q ≫
        (restrictScalarsHomologyIso φ L q).hom =
      (restrictScalarsHomologyIso φ K q).hom ≫
        (ModuleCat.restrictScalars.{u} φ).map (HomologicalComplex.homologyMap g q) :=
  have := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars.{u} φ
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) q).map g)
    (ModuleCat.restrictScalars.{u} φ)

end Stacks.Homology.RestrictScalars

namespace Stacks.ProjectiveSpace.Cohomology

open Stacks.Cohomology.CechSheaf Stacks.ProjectiveCohomology

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] laurentCechComplex

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The morphism of ordered Čech complexes of the standard cover induced by a morphism of
twists. -/
abbrev twistOrderedMap {d e : ℤ}
    (φ : ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d ⟶
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) e) :
    twistOrderedComplex R n d ⟶ twistOrderedComplex R n e :=
  orderedModuleMap (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm φ

/-- The comparison of [Stacks, Tag 01XD] for the standard cover of `ℙⁿ_R` is natural in the
twist. -/
theorem cechHomologyIsoRightDerivedTwistingSheaf_naturality {d e : ℤ}
    (φ : ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d ⟶
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) e) (q : ℕ) :
    ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n))
          ⊤).rightDerived q).map φ ≫ (cechHomologyIsoRightDerivedTwistingSheaf R n e q).hom =
      (cechHomologyIsoRightDerivedTwistingSheaf R n d q).hom ≫
        HomologicalComplex.homologyMap
          ((cechComplexFunctorOfCover (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
            (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm).map φ) q :=
  @Stacks.Cohomology.CechIso.cechHomologyIsoRightDerived_naturality
    (AlgebraicGeometry.Proj (polyGrading R n)) _ ⊤ (basicOpenXAtUniverse R n)
    (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (fun r s => isAffineOpen_iInf_basicOpenXAtUniverse R n r s) _ _
    (isQuasicoherent_twistingSheaf R n d) (isQuasicoherent_twistingSheaf R n e) φ q

/-- The comparison of the ordered Čech complex of the standard cover of `ℙⁿ_R` with the
module-valued Čech complex is natural in the twist. -/
theorem orderedCechHomologyTwist_naturality {d e : ℤ}
    (φ : ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d ⟶
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) e) (q : ℕ) :
    HomologicalComplex.homologyMap
          ((cechComplexFunctorOfCover (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
            (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm).map φ) q ≫
        (orderedCechHomologyModuleIso (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
          (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) e) q).inv =
      (orderedCechHomologyModuleIso (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
          (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) q).inv ≫
        HomologicalComplex.homologyMap (twistOrderedMap R n φ) q :=
  sq_inv _ _ _ _ (orderedCechHomologyModuleIso_naturality _ _ _ φ q)

/-- **The identification of the cohomology of a twist with the homology of the ordered Čech
complex of the standard cover is natural in the twist.** -/
theorem sheafCohomologyIsoOrderedHomology_naturality {d e : ℤ}
    (φ : ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d ⟶
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) e) (q : ℕ) :
    ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n))
          ⊤).rightDerived q).map φ ≫ (sheafCohomologyIsoOrderedHomology R n e q).hom =
      (sheafCohomologyIsoOrderedHomology R n d q).hom ≫
        HomologicalComplex.homologyMap (twistOrderedMap R n φ) q := by
  show _ ≫ ((cechHomologyIsoRightDerivedTwistingSheaf R n e q).hom ≫
      (orderedCechHomologyModuleIso (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
        (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) e) q).inv) =
    ((cechHomologyIsoRightDerivedTwistingSheaf R n d q).hom ≫
      (orderedCechHomologyModuleIso (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
        (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) q).inv) ≫ _
  exact paste_two _ _ _ _ _ _ _ (cechHomologyIsoRightDerivedTwistingSheaf_naturality R n φ q)
    (orderedCechHomologyTwist_naturality R n φ q)

/-- **The identification of the cohomology of a twist, as an `R`-module, with the homology of the
ordered Čech complex is natural in the twist.** -/
theorem twistCohomologyIsoOrderedHomology_naturality {d e : ℤ}
    (φ : ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d ⟶
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) e) (q : ℕ) :
    (ModuleCat.restrictScalars.{u} (coeffScalar R n)).map
          (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n))
            ⊤).rightDerived q).map φ) ≫ (twistCohomologyIsoOrderedHomology R n e q).hom =
      (twistCohomologyIsoOrderedHomology R n d q).hom ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.restrictScalars.{u} (coeffScalar R n)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (twistOrderedMap R n φ)) q :=
  paste_two _ _ _ _ _ _ _
    ((Functor.map_comp _ _ _).symm.trans
      ((congrArg (ModuleCat.restrictScalars.{u} (coeffScalar R n)).map
        (sheafCohomologyIsoOrderedHomology_naturality R n φ q)).trans
        (Functor.map_comp _ _ _)))
    (sq_inv _ _ _ _ (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso_naturality
      (coeffScalar R n) (twistOrderedMap R n φ) q))

end Stacks.ProjectiveSpace.Cohomology

end
