module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgetModuleHelpers
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the underlying abelian sheaf

Let `X` be a ringed space and `K` an object of the unbounded derived category `D(O_X)` of
sheaves of `O_X`-modules.  Writing `K_ab` for the image of `K` in the unbounded derived
category of abelian sheaves on `X`, the canonical comparison `RΓ(U, K) ⟶ RΓ(U, K_ab)` is an
isomorphism in `D(Ab)` for every open `U ⊆ X`: forgetting the module structure does not
change cohomology over an open.

The comparison `sectionsForgetComparison` is the map of right derived functors induced,
through the universal property of `RΓ(U, -)` on `D(O_X)`, by the identification of the two
underived sections functors.  It is invertible because it is invertible on K-injective
complexes of `O_X`-modules, and those suffice since sheaves of modules on a ringed space form
a Grothendieck abelian category.

## Main definitions

* `Stacks.Cohomology.UnderlyingAbelianSheaf.underlyingDerivedSheaf`: the functor
  `D(O_X) ⥤ D(Ab_X)` forgetting the module structure.
* `Stacks.Cohomology.UnderlyingAbelianSheaf.derivedAbelianSectionsOnOpen`: unbounded derived
  sections over an open for abelian sheaves.
* `Stacks.Cohomology.UnderlyingAbelianSheaf.sectionsForgetComparison`: the canonical
  comparison `RΓ(U, K) ⟶ RΓ(U, K_ab)`.

## Main results

* `Stacks.Cohomology.UnderlyingAbelianSheaf.sectionsForgetComparison_isIso` (Tag 0D5Y, part
  (1)): the comparison is an isomorphism.
* `Stacks.Cohomology.UnderlyingAbelianSheaf.hasRightDerivedFunctor_of_abelianSheafKInjectives`:
  every functor out of the homotopy category of abelian sheaves on `X` has a total right
  derived functor.

## Implementation notes

The K-injective criterion reduces the claim to the invertibility, on a K-injective complex `I`
of `O_X`-modules, of the derived unit for abelian sections.  That in turn needs the underlying
abelian complex of `I` to compute derived sections, which is where the arithmetic of the proof
sits: extension of scalars `- ⊗_ℤ O_X`, the left adjoint of `SheafOfModules.toSheaf` supplied
by `ModuleSheafCohomology.tensorSheafHomIso`, is exact on sectionwise torsion-free abelian
sheaves, so morphisms out of a bounded-above sectionwise torsion-free complex into the
underlying abelian complex of `I` are already computed in the homotopy category.  Sections over
an open are corepresented by such a complex, by
`ModuleSheafCohomology.evaluationRepresentation`, and the free abelian sheaf appearing there is
sectionwise torsion free.

That extension of scalars and the homotopy-category computation it yields —
`Stacks.Cohomology.ForgetModule.toSheaf_localization_map_bijective_of_isLE` — hold on an
arbitrary small site and are proved there, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgetModuleHelpers`; they are
used here at the site `Opens.grothendieckTopology X`.  What is special to a ringed space, and so
stays in this file, is the passage from that statement to the vanishing of all morphisms into
the mapping cone over the K-injective resolution of the underlying abelian complex, which is
what feeds the derived unit.

**The derived categories.** The derived categories of `O_X`-modules, of abelian sheaves on
`X` and of abelian groups are taken at `CategoryTheory.HasDerivedCategory.standard`, the
localization of the homotopy category at the quasi-isomorphisms, installed as a file-level local
instance. `X` is an arbitrary `TopCat.{u}` carrying an arbitrary sheaf of rings. Part (2) of the
tag is `Stacks.Cohomology.UnderlyingAbelianPushforward.pushforwardForgetComparison_isIso`, in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedCategory/UnderlyingAbelianSheafPushforward.lean`.

Both total right derived functors compared in `sectionsForgetComparison_isIso` exist by the
global instance `Stacks.Cohomology.Localization.hasRightDerivedFunctorOfGrothendieck`, sheaves
of modules and abelian sheaves on a space being Grothendieck abelian.

## References

* [Stacks Project, Tag 0D5Y](https://stacks.math.columbia.edu/tag/0D5Y)
* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject

namespace Stacks.Cohomology.UnderlyingAbelianSheaf

open Stacks.Cohomology.OpenSubspace
open Stacks.Cohomology.Localization (enoughKInjectives derivedUnit_isIsoOnKInjective
  rightDerived_of_kInjectives)

universe u v₁ v₂

attribute [local instance] HasDerivedCategory.standard

section PrivateSheafLemmas

open ModuleSheafCohomology

private lemma isIso_Qh_map_quotient_map_of_quasiIso
    {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ} (q : K ⟶ L) [QuasiIso q] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map q)) :=
  (DerivedCategory.isIso_Qh_map_iff _).mpr
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff q).mpr ‹_›)

private lemma postcomp_bijective_of_localization
    {A B : Type*} [Category A] [Category B] (L : A ⥤ B)
    {X Y Z : A} (s : X ⟶ Y) [IsIso (L.map s)]
    (hX : Function.Bijective (L.map : (Z ⟶ X) → _))
    (hY : Function.Bijective (L.map : (Z ⟶ Y) → _)) :
    Function.Bijective (fun a : Z ⟶ X => a ≫ s) := by
  constructor
  · intro a b hab
    apply hX.injective
    apply (cancel_mono (L.map s)).mp
    simpa only [← L.map_comp] using congrArg L.map hab
  · intro b
    obtain ⟨a, ha⟩ := hX.surjective (L.map b ≫ inv (L.map s))
    refine ⟨a, hY.injective ?_⟩
    simp only [L.map_comp, ha, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

private lemma acyclic_mapCoyoneda_of_zero_hom
    {A : Type*} [Category A] [Abelian A] (F : A) (K : CochainComplex A ℤ)
    (h : ∀ n, ∀ f : (HomotopyCategory.quotient A (.up ℤ)).obj
        ((CochainComplex.singleFunctor A n).obj F) ⟶
          (HomotopyCategory.quotient A (.up ℤ)).obj K, f = 0) :
    (((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro f hf
  change f ≫ K.d i (i + 1) = 0 at hf
  have hd : ∀ j, (ComplexShape.up ℤ).Rel i j → f ≫ K.d i j = 0 := by
    rintro j hj
    obtain rfl : j = i + 1 := by simpa using hj.symm
    exact hf
  let g := HomologicalComplex.mkHomFromSingle f hd
  obtain ⟨ht⟩ := (HomotopyCategory.quotient_map_eq_zero_iff g).mp (h i _)
  refine ⟨(HomologicalComplex.singleObjXSelf (.up ℤ) i F).inv ≫
    ht.hom i (i - 1), ?_⟩
  have he := ht.comm i
  simp only [g, dNext,
    prevD, HomologicalComplex.single_obj_d, zero_comp,
    HomologicalComplex.zero_f, add_zero] at he
  simp only [AddMonoidHom.mk'_apply, zero_add] at he
  rw [CochainComplex.prev ℤ i] at he
  have he' : (HomologicalComplex.singleObjXSelf (.up ℤ) i F).hom ≫ f =
      ht.hom i (i - 1) ≫ K.d (i - 1) i :=
    (HomologicalComplex.mkHomFromSingle_f (K := K) (j := i) f hd).symm.trans he
  change ((HomologicalComplex.singleObjXSelf (.up ℤ) i F).inv ≫
    ht.hom i (i - 1)) ≫ K.d (i - 1) i = f
  rw [Category.assoc, ← he']
  exact Iso.inv_hom_id_assoc _ _

open CategoryTheory.Pretriangulated in
private lemma hom_cone_eq_zero
    {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]
    [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    (T : Triangle A) (hT : T ∈ distTriang A) (F : A)
    (hs : Function.Surjective (fun a : F ⟶ T.obj₁ => a ≫ T.mor₁))
    (hi : Function.Injective (fun a : F ⟶ T.obj₁⟦(1 : ℤ)⟧ => a ≫ T.mor₁⟦1⟧'))
    (f : F ⟶ T.obj₃) : f = 0 := by
  have hf : f ≫ T.mor₃ = 0 := hi (by
    simp [Category.assoc, comp_distTriang_mor_zero₃₁ T hT])
  obtain ⟨g, rfl⟩ := T.coyoneda_exact₃ hT f hf
  obtain ⟨a, rfl⟩ := hs g
  simp [Category.assoc, comp_distTriang_mor_zero₁₂ T hT]

private lemma postcomp_bijective_source_iso
    {A : Type*} [Category A] {X X' I J : A} (e : X ≅ X') (q : I ⟶ J)
    (h : Function.Bijective (fun a : X ⟶ I => a ≫ q)) :
    Function.Bijective (fun a : X' ⟶ I => a ≫ q) := by
  constructor
  · intro a b hab
    apply (cancel_epi e.hom).mp
    apply h.injective
    simpa only [Category.assoc] using congrArg (fun f => e.hom ≫ f) hab
  · intro b
    obtain ⟨a, ha⟩ := h.surjective (e.hom ≫ b)
    exact ⟨e.inv ≫ a, by
      dsimp only at ha ⊢
      rw [Category.assoc, ha, Iso.inv_hom_id_assoc]⟩

private lemma adjunction_postcomp_bijective
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) (X : A) {I J : B} (q : I ⟶ J)
    (h : Function.Bijective (fun a : F.obj X ⟶ I => a ≫ q)) :
    Function.Bijective (fun a : X ⟶ G.obj I => a ≫ G.map q) := by
  constructor
  · intro a b hab
    apply (adj.homEquiv X I).symm.injective
    apply h.injective
    simpa only [← adj.homEquiv_naturality_right_symm] using
      congrArg (adj.homEquiv X J).symm hab
  · intro b
    obtain ⟨a, ha⟩ := h.surjective ((adj.homEquiv X J).symm b)
    refine ⟨adj.homEquiv X I a, ?_⟩
    simpa only [adj.homEquiv_naturality_right, Equiv.apply_symm_apply] using
      congrArg (adj.homEquiv X J) ha

private lemma toSheaf_hom_cone_eq_zero {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    (n : ℤ) [K.IsLE n]
    (hK : ∀ i U, Module.IsTorsionFree ℤ ((K.X i).obj.obj U))
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective]
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    [J.IsKInjective]
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso q]
    (f : (HomotopyCategory.quotient _ (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mappingCone q)) : f = 0 := by
  let A := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let H := HomotopyCategory A (.up ℤ)
  let Q := HomotopyCategory.quotient A (.up ℤ)
  have hpost (L : CochainComplex A ℤ) (m : ℤ) [L.IsLE m]
      (hL : ∀ i U, Module.IsTorsionFree ℤ ((L.X i).obj.obj U)) :
      Function.Bijective (fun a : Q.obj L ⟶ Q.obj _ => a ≫ Q.map q) := by
    have : IsIso (DerivedCategory.Qh.map (Q.map q)) := isIso_Qh_map_quotient_map_of_quasiIso q
    exact postcomp_bijective_of_localization DerivedCategory.Qh (Q.map q)
      (ForgetModule.toSheaf_localization_map_bijective_of_isLE _ O L m hL I)
      (CochainComplex.IsKInjective.Qh_map_bijective _ J)
  have hshift : (K⟦(-1 : ℤ)⟧).IsLE (n + 1) := K.isLE_shift n (-1) (n + 1) (by omega)
  have hshiftP : ∀ i U, Module.IsTorsionFree ℤ (((K⟦(-1 : ℤ)⟧).X i).obj.obj U) := fun i =>
    isTorsionFree_of_mono _ (K.shiftFunctorObjXIso (-1) i (i + -1) rfl).hom (hK (i + -1))
  have hs := postcomp_bijective_source_iso ((Q.commShiftIso (-1 : ℤ)).app K)
    (Q.map q) (hpost (K⟦(-1 : ℤ)⟧) (n + 1) hshiftP)
  have ht := adjunction_postcomp_bijective
    (shiftEquiv' H (-1 : ℤ) 1 (by omega)).toAdjunction (Q.obj K) (Q.map q) hs
  exact hom_cone_eq_zero (CochainComplex.mappingCone.triangleh q)
    (HomotopyCategory.mappingCone_triangleh_distinguished q) (Q.obj K)
    (hpost K n hK).surjective ht.injective f

/-- Forget the module structure on an object of the unbounded derived category. -/
public abbrev underlyingDerivedSheaf {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  (SheafOfModules.toSheaf O).mapDerivedCategory

/-- Sections over an open of an abelian sheaf. -/
public abbrev abelianSectionsOnOpen (X : TopCat.{u}) (U : Opens X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)

/-- Sections of abelian sheaves over an open are additive. -/
public instance abelianSectionsOnOpen_additive (X : TopCat.{u}) (U : Opens X) :
    (abelianSectionsOnOpen X U).Additive where
  map_add := rfl

/-- The homotopy-category functor whose right derived functor is sections of abelian
sheaves over an open. -/
public abbrev homotopyAbelianSectionsOnOpen (X : TopCat.{u}) (U : Opens X) :
    HomotopyCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (abelianSectionsOnOpen X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- **Every functor out of the homotopy category of abelian sheaves on a space has a total
right derived functor.** The site of opens of `X` is essentially small, so abelian sheaves on
`X` are Grothendieck abelian and every complex of them receives a quasi-isomorphism from a
K-injective one. -/
public theorem hasRightDerivedFunctor_of_abelianSheafKInjectives (X : TopCat.{u})
    {C : Type v₁} [Category.{v₂} C]
    (S : HomotopyCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ComplexShape.up ℤ) ⥤ C) :
    S.HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (ComplexShape.up ℤ)) := by
  have : IsGrothendieckAbelian.{u}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _
  have : S.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (ComplexShape.up ℤ)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, v₂, v₁, u + 1, v₁, u + 1} S
      (enoughKInjectives
        (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))).1
  exact Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor S _

/-- Unbounded derived sections over an open for abelian sheaves. -/
public abbrev derivedAbelianSectionsOnOpen (X : TopCat.{u}) (U : Opens X) :
    DerivedCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (homotopyAbelianSectionsOnOpen X U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (ComplexShape.up ℤ))

/-- Ordinary sections agree after forgetting module structure. -/
public noncomputable def ordinarySectionsForgetIso {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    sectionsOnOpen O U ≅ SheafOfModules.toSheaf O ⋙ abelianSectionsOnOpen X U :=
  Iso.refl _

/-- The canonical unit comparison for derived sections after forgetting module structure. -/
public noncomputable def sectionsForgetUnit {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    homotopySectionsOnOpen O U ⟶
      DerivedCategory.Qh ⋙ (underlyingDerivedSheaf O ⋙ derivedAbelianSectionsOnOpen X U) := by
  letI : (SheafOfModules.evaluation O (op U)).Additive := ⟨by intros; rfl⟩
  exact
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (sectionsOnOpen O U))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (ordinarySectionsForgetIso O U)
        (ComplexShape.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (SheafOfModules.toSheaf O ⋙ abelianSectionsOnOpen X U))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator
      ((SheafOfModules.toSheaf O).mapHomotopyCategory (ComplexShape.up ℤ))
      ((abelianSectionsOnOpen X U).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft ((SheafOfModules.toSheaf O).mapHomotopyCategory (ComplexShape.up ℤ))
      ((homotopyAbelianSectionsOnOpen X U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
          (ComplexShape.up ℤ))) ≫
    Functor.whiskerRight (SheafOfModules.toSheaf O).mapDerivedCategoryFactorsh.inv
      (derivedAbelianSectionsOnOpen X U)

/-- The canonical comparison induced by `sectionsForgetUnit` through the universal
property of the right derived functor. -/
public noncomputable def sectionsForgetComparison {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    derivedSectionsOnOpen O U ⟶
      underlyingDerivedSheaf O ⋙ derivedAbelianSectionsOnOpen X U :=
  (derivedSectionsOnOpen O U).rightDerivedDesc
    ((homotopySectionsOnOpen O U).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))
    _ (sectionsForgetUnit O U)

private lemma evaluationRepresentation_torsionFree {X : TopCat.{u}} (U : Opens X) :
    ∀ V : (Opens X)ᵒᵖ, Module.IsTorsionFree ℤ
      (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)).obj.obj V) := by
  apply ModuleSheafCohomology.isTorsionFree_sheafify
  intro V
  change Module.IsTorsionFree ℤ (FreeAbelianGroup (V.unop ⟶ U))
  exact Module.Flat.isTorsionFree

private lemma sections_quasiIso_of_moduleKInjective {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective]
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    [J.IsKInjective]
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso q] :
    QuasiIso (((abelianSectionsOnOpen X U).mapHomologicalComplex (.up ℤ)).map q) := by
  let P : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free)
  have hcone : (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mappingCone q)).Acyclic := by
    apply acyclic_mapCoyoneda_of_zero_hom
    intro n f
    exact toSheaf_hom_cone_eq_zero O ((CochainComplex.singleFunctor _ n).obj P) n
      (ForgetModule.torsionFree_single _ P (evaluationRepresentation_torsionFree U) n) I J q f
  let e := NatIso.mapHomologicalComplex
    (ModuleSheafCohomology.evaluationRepresentation
      (Opens.grothendieckTopology X) U) (.up ℤ)
  have hsections : (((abelianSectionsOnOpen X U).mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mappingCone q)).Acyclic := by
    intro i
    exact (exactAt_iff_of_quasiIsoAt (e.app (CochainComplex.mappingCone q)).hom i).mpr
      (hcone i)
  apply Functor.quasiIso_of_acyclic_mappingCone
  intro i
  exact (exactAt_iff_of_quasiIsoAt
    (CochainComplex.mappingCone.mapHomologicalComplexIso q
      (abelianSectionsOnOpen X U)).hom i).mp (hsections i)

private lemma abelianSections_unit_isIso_of_moduleKInjective {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    IsIso (((homotopyAbelianSectionsOnOpen X U).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (.up ℤ))).app
      (((SheafOfModules.toSheaf O).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
  let A := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let F := homotopyAbelianSectionsOnOpen X U
  let RF := derivedAbelianSectionsOnOpen X U
  let α := F.totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ))
  let K := ((SheafOfModules.toSheaf O).mapHomologicalComplex (.up ℤ)).obj I
  obtain ⟨J, q, hJ, hq⟩ := Stacks.Cohomology.Localization.enoughKInjectives K
  let Q := HomotopyCategory.quotient A (.up ℤ)
  have hαJ : IsIso (α.app (Q.obj J)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective F RF α J
  have hqD : IsIso (DerivedCategory.Qh.map (Q.map q)) := isIso_Qh_map_quotient_map_of_quasiIso q
  have hqF : IsIso (F.map (Q.map q)) := by
    have := sections_quasiIso_of_moduleKInjective O U I J q
    exact isIso_Qh_map_quotient_map_of_quasiIso
      (((abelianSectionsOnOpen X U).mapHomologicalComplex (.up ℤ)).map q)
  have hαK : IsIso (α.app (Q.obj K)) := by
    have : IsIso ((DerivedCategory.Qh ⋙ RF).map (Q.map q)) := by
      change IsIso (RF.map (DerivedCategory.Qh.map (Q.map q)))
      infer_instance
    have hcomp : IsIso (α.app (Q.obj K) ≫ (DerivedCategory.Qh ⋙ RF).map (Q.map q)) := by
      rw [← α.naturality (Q.map q)]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp hcomp
  exact hαK

/-- **Stacks 0D5Y, part (1).** Unbounded derived sections of modules agree canonically and
naturally with derived sections after forgetting to abelian sheaves: for every open `U ⊆ X` the
canonical map `RΓ(U, K) ⟶ RΓ(U, K_ab)` is an isomorphism in `D(Ab)`. -/
@[stacks 0D5Y "part (1)"]
public theorem sectionsForgetComparison_isIso {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    IsIso (sectionsForgetComparison O U) := by
  let Q := HomotopyCategory.quotient (SheafOfModules.{u} O) (.up ℤ)
  let β := (homotopySectionsOnOpen O U).totalRightDerivedUnit
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (.up ℤ))
  let γ := sectionsForgetUnit O U
  have hγ : ∀ (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective],
      IsIso (γ.app (Q.obj I)) := by
    intro I _
    have := abelianSections_unit_isIso_of_moduleKInjective O U I
    dsimp only [γ, sectionsForgetUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (derivedSectionsOnOpen O U) β
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (.up ℤ)) _ γ).mp
    (rightDerived_of_kInjectives (homotopySectionsOnOpen O U)
      (underlyingDerivedSheaf O ⋙ derivedAbelianSectionsOnOpen X U) γ hγ)

end PrivateSheafLemmas

end Stacks.Cohomology.UnderlyingAbelianSheaf

end
