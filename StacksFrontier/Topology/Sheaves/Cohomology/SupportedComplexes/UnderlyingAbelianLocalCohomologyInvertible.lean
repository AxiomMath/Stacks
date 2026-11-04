module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalSectionsDerived
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveFlasqueModules
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.FlasqueSupportedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Invertibility of the comparison of derived local cohomology sheaves

Let `Z` be a closed subset of a ringed space `X` and let `K` be an object of the unbounded
derived category `D(𝒪_X)` with image `K_ab` in `D(ℤ_X)`. The file
`UnderlyingAbelianLocalCohomologyComparison.lean` constructs the canonical comparison

`RH_Z(K)_ab ⟶ RH_Z(K_ab)`

of Stacks 0G74 part (2). This file proves that it is an **isomorphism**.

## Main results

* `isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor` (Stacks 0G74, part (2)):
  the comparison is invertible, in all degrees.
* `abelianSupportedUnit_isIso_at_underlying_kInjective`: the derivation unit of derived abelian
  supported sections is invertible at the underlying abelian complex of a K-injective complex of
  `𝒪_X`-modules with injective terms. This is the mathematical heart of the file.
* `abelianSupportedSectionsRealized_map_quasiIso_of_kInjectiveModule`,
  `supportedSections_map_quasiIso_of_kInjectiveModule` and
  `supportedSectionsEvaluation_map_quasiIso_of_kInjectiveModule`: the same statement in its three
  successive forms — realized on `Z`, as a sheaf on `X`, and over a single open subset of `X`.
* `abelianSections_map_quasiIso_of_kInjectiveModule`: the corresponding statement for sections
  over an open, which is Stacks 0D5Y part (1) read at a single complex.

## Implementation notes

Forgetting the module structure does not preserve injectives, so an injective resolution of a
complex of `𝒪_X`-modules is not an injective resolution of its underlying complex of abelian
sheaves and the comparison is not formal. The source's argument runs through **flasqueness**,
and so does this file:

1. the underlying abelian sheaf of an injective `𝒪_X`-module is flasque — Stacks 09SX, already
   available as `Stacks.Cohomology.isFlasque_of_injective_module`, and likewise an injective
   abelian sheaf is flasque by `Stacks.Cohomology.isFlasque_of_injective`;
2. for a flasque abelian sheaf, sections supported on `Z` over an open `W` are the kernel of a
   *surjection* `F(W) ⟶ F(W ∖ Z)` — this is
   `ClosedImmersionSheaves.supportedSections_restriction_shortExact`.

Step 2 turns a K-injective resolution `q : K_ab ⟶ J` of the underlying abelian complex into a
morphism of short exact sequences of complexes whose outer two terms are `q` followed by
sections over `W` and over `W ∖ Z`. Those two are quasi-isomorphisms by Stacks 0D5Y part (1),
which is exactly the statement that the underlying abelian complex of a K-injective complex of
modules computes derived sections over an open; two out of three in the associated
distinguished triangles then gives the remaining term. Quasi-isomorphy of a morphism of
complexes of sheaves is detected open by open, and pushforward along the inclusion of `Z` is
exact and fully faithful, so the statement descends to `H_Z : Ab(X) ⥤ Ab(Z)`. Finally, the
derivation unit of `RH_Z` on abelian sheaves is invertible at a K-injective complex, so
naturality carries invertibility back to `K_ab`, and the defining factorization of the
comparison map (`localCohomologySheafForgetComparison_fac`) transfers it to the comparison
itself.

Note that this is **not** the route of part (1) of the tag, where supported sections over `X`
were the kernel of `Γ(X,−) ⟶ Γ(X ∖ Z,−)` and both functors were directly comparable. At the
sheaf level `H_Z` is not the kernel of a pair of already-comparable functors; what makes the
argument work here is that it is such a kernel *after evaluation at each open*, and only on
flasque sheaves.

Several small lemmas (`isIso_comp_app`, `isIso_whiskerLeft_app` and friends) exist only to
decompose the long composite `supportedSheafForgetUnit` at one object. `simp` cannot do this:
the additivity instances occurring in the functors there are produced by separate tactic
blocks, so consecutive factors of the composite have middle functors that are definitionally
but not syntactically equal, and congruence closure fails. These helpers are applied by
`exact`, which checks equality up to unfolding.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.34.5 (Tag 0D5Y)](https://stacks.math.columbia.edu/tag/0D5Y)
* [Stacks Project, Lemma 20.11.1 (Tag 09SX)](https://stacks.math.columbia.edu/tag/09SX)
* [Stacks Project, Remark 17.5.4 (Tag 01AY)](https://stacks.math.columbia.edu/tag/01AY)
* [Stacks Project, Tag 01AX](https://stacks.math.columbia.edu/tag/01AX)
* [Stacks Project, Tag 00AG](https://stacks.math.columbia.edu/tag/00AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry.SheafOfModules (supportedSectionsSheafι supportedSectionsPresheafι)
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.OpenSubspace
open Stacks.Cohomology.Localization (derivedUnit_isIsoOnKInjective
  enoughKInjectives natTrans_isIso_of_kInjectives)
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

/-! ### Transport of quasi-isomorphisms -/

/-- Two out of three in a map of short exact sequences of cochain complexes: if a morphism of
short exact sequences is a quasi-isomorphism on the second and third terms, it is one on the
first. The three terms of a short exact sequence of complexes form a distinguished triangle in
the derived category, and in a triangulated category two out of three isomorphisms force the
third. -/
lemma quasiIso_τ₁_of_shortExact {C : Type*} [Category C] [Abelian C]
    {S T : ShortComplex (CochainComplex C ℤ)} (f : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) [QuasiIso f.τ₂] [QuasiIso f.τ₃] :
    QuasiIso f.τ₁ := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃
    (DerivedCategory.triangleOfSES.map hS hT f)
    (DerivedCategory.triangleOfSES_distinguished hS)
    (DerivedCategory.triangleOfSES_distinguished hT)
    (inferInstanceAs (IsIso (DerivedCategory.Q.map f.τ₂)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map f.τ₃)))

/-- A morphism of complexes of sheaves is a quasi-isomorphism as soon as it is one on the
underlying complexes of presheaves. Sheafification is exact and undoes the inclusion of sheaves
into presheaves, so the morphism is isomorphic, as an arrow, to the sheafification of its
presheaf-level counterpart. -/
lemma sheafQuasiIso_of_presheafQuasiIso
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ} (f : K ⟶ L)
    [HasSheafify J AddCommGrpCat.{u}]
    (hf : QuasiIso (((sheafToPresheaf J AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) : QuasiIso f := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  let G := presheafToSheaf J AddCommGrpCat.{u}
  let c := ComplexShape.up ℤ
  let _ : G.Additive := Functor.additive_of_preserves_binary_products G
  let e : F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
      𝟭 (CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c ≪≫
      NatIso.mapHomologicalComplex (sheafificationNatIso J AddCommGrpCat.{u}).symm c ≪≫
      Functor.mapHomologicalComplexIdIso _ c
  let sf := (G.mapHomologicalComplex c).map ((F.mapHomologicalComplex c).map f)
  have hsf : QuasiIso sf :=
    HomologicalComplex.quasiIso_map_of_preservesHomology
      ((F.mapHomologicalComplex c).map f) G
  let he : Arrow.mk sf ≅ Arrow.mk f :=
    Arrow.isoMk (e.app K) (e.app L) (by simpa [sf] using (e.hom.naturality f).symm)
  exact quasiIso_of_arrow_mk_iso sf f he

/-- Transport of quasi-isomorphy along an isomorphism of functors into cochain complexes. -/
lemma quasiIso_map_of_functor_iso
    {C D : Type*} [Category C] [Category D] [Abelian D]
    {F G : C ⥤ CochainComplex D ℤ} (e : F ≅ G)
    {K L : C} (f : K ⟶ L) (hf : QuasiIso (G.map f)) :
    QuasiIso (F.map f) :=
  (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality f).symm)).2 hf

/-- Invertibility of a composite of natural transformations at one object, factor by factor.
Stated so that it can be applied by `refine` to a long composite: the two middle functors are
implicit and are determined by the composite being matched, which `simp` cannot do here because
the additivity instances appearing in the functors are produced by separate tactic blocks and so
are only definitionally, not syntactically, equal. -/
lemma isIso_comp_app {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (a : F ⟶ G) (b : G ⟶ H) (x : C) (ha : IsIso (a.app x)) (hb : IsIso (b.app x)) :
    IsIso ((a ≫ b).app x) := by
  have := ha
  have := hb
  rw [NatTrans.comp_app]
  infer_instance

/-- Invertibility at one object of a transformation whiskered on the left. -/
lemma isIso_whiskerLeft_app {A B E : Type*} [Category A] [Category B] [Category E]
    (F : A ⥤ B) {G H : B ⥤ E} (α : G ⟶ H) (x : A) (h : IsIso (α.app (F.obj x))) :
    IsIso ((Functor.whiskerLeft F α).app x) := h

/-- Invertibility at one object of the forward direction of an isomorphism whiskered on the
left. -/
lemma isIso_whiskerLeft_isoHom_app {A B E : Type*} [Category A] [Category B] [Category E]
    (F : A ⥤ B) {G H : B ⥤ E} (e : G ≅ H) (x : A) :
    IsIso ((Functor.whiskerLeft F e.hom).app x) :=
  inferInstanceAs (IsIso (e.hom.app (F.obj x)))

/-- Invertibility at one object of the forward direction of an isomorphism whiskered on the
right. -/
lemma isIso_whiskerRight_isoHom_app {A B E : Type*} [Category A] [Category B] [Category E]
    {F G : A ⥤ B} (e : F ≅ G) (K : B ⥤ E) (x : A) :
    IsIso ((Functor.whiskerRight e.hom K).app x) :=
  inferInstanceAs (IsIso (K.map (e.hom.app x)))

/-- Invertibility at one object of the backward direction of an isomorphism whiskered on the
right. -/
lemma isIso_whiskerRight_isoInv_app {A B E : Type*} [Category A] [Category B] [Category E]
    {F G : A ⥤ B} (e : F ≅ G) (K : B ⥤ E) (x : A) :
    IsIso ((Functor.whiskerRight e.inv K).app x) :=
  inferInstanceAs (IsIso (K.map (e.inv.app x)))

/-- The associator is the identity on components. -/
lemma isIso_associator_hom_app {A B E T : Type*} [Category A] [Category B] [Category E]
    [Category T] (F : A ⥤ B) (G : B ⥤ E) (H : E ⥤ T) (x : A) :
    IsIso ((Functor.associator F G H).hom.app x) := by
  show IsIso (𝟙 _)
  infer_instance

/-- The inverse associator is the identity on components. -/
lemma isIso_associator_inv_app {A B E T : Type*} [Category A] [Category B] [Category E]
    [Category T] (F : A ⥤ B) (G : B ⥤ E) (H : E ⥤ T) (x : A) :
    IsIso ((Functor.associator F G H).inv.app x) := by
  show IsIso (𝟙 _)
  infer_instance

/-- A quasi-isomorphism of complexes becomes invertible in the derived category. -/
private theorem isIso_Qh_map_quotient_map {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (q : K ⟶ L) [QuasiIso q] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map q)) :=
  (DerivedCategory.isIso_Qh_map_iff _).mpr
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff q).mpr ‹QuasiIso q›)

/-! ### Existence of the derived functors of sections over an open -/

variable {X : TopCat.{u}}

/-- Sections of abelian sheaves over an open have a total right derived functor: abelian
sheaves on a space are Grothendieck abelian, so every complex admits a quasi-isomorphism into a
K-injective one. -/
instance hasRightDerivedFunctor_abelianSectionsOnOpen (W : Opens X) :
    (homotopyAbelianSectionsOnOpen X W).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) := by
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
    u + 1, u + 1, u + 1, u + 1, u + 1}
    (homotopyAbelianSectionsOnOpen X W) Stacks.Cohomology.Localization.enoughKInjectives).1
  infer_instance

/-- Sections of sheaves of modules over an open have a total right derived functor, sheaves of
modules on a space being Grothendieck abelian. -/
instance hasRightDerivedFunctor_sectionsOnOpen
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (W : Opens X) :
    (homotopySectionsOnOpen O W).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) := by
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
    u + 1, u + 1, u + 1, u + 1, u + 1}
    (homotopySectionsOnOpen O W) Stacks.Cohomology.Localization.enoughKInjectives).1
  infer_instance

/-! ### Sections over an open after forgetting the module structure -/

/-- The derivation unit of derived sections over an open, after forgetting the module structure,
is invertible at a K-injective complex of modules. This is Stacks 0D5Y part (1)
(`Stacks.Cohomology.UnderlyingAbelianSheaf.sectionsForgetComparison_isIso`) read at a single
K-injective complex. -/
lemma sectionsForgetUnit_isIso_at_kInjective
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (W : Opens X)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    IsIso ((sectionsForgetUnit O W).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  let F := homotopySectionsOnOpen O W
  let R := derivedSectionsOnOpen O W
  let α := F.totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))
  have hα : IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective F R α I
  have : IsIso (sectionsForgetComparison O W) := sectionsForgetComparison_isIso O W
  have hf := R.rightDerived_fac_app α
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))
    _ (sectionsForgetUnit O W)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
  rw [← hf]
  show IsIso (α.app _ ≫ (sectionsForgetComparison O W).app _)
  infer_instance

/-- The derivation unit of derived sections of *abelian* sheaves over an open is invertible at
the underlying abelian complex of a K-injective complex of modules — even though that underlying
complex need not itself be K-injective. This is the content of Stacks 0D5Y part (1), stripped of
the isomorphisms that
`Stacks.Cohomology.UnderlyingAbelianSheaf.sectionsForgetUnit` composes it with. -/
lemma abelianSectionsUnit_isIso_at_underlying_kInjective
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (W : Opens X)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    IsIso (((homotopyAbelianSectionsOnOpen X W).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (ComplexShape.up ℤ))).app
      (((SheafOfModules.toSheaf O).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have h := sectionsForgetUnit_isIso_at_kInjective O W I
  unfold sectionsForgetUnit at h
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using h

/-- **Sections over an open take a K-injective resolution of an underlying abelian complex to a
quasi-isomorphism.** Let `I` be a K-injective complex of `𝒪_X`-modules, let `J` be a K-injective
complex of abelian sheaves and let `q : I_ab ⟶ J` be a quasi-isomorphism. Then `q` stays a
quasi-isomorphism after taking sections over any open `W`.

This is the key consequence of Stacks 0D5Y part (1): the underlying abelian complex `I_ab` of a
K-injective complex of modules, while not K-injective, computes derived sections. -/
lemma abelianSections_map_quasiIso_of_kInjectiveModule
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (W : Opens X)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective]
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    [J.IsKInjective]
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso q] :
    QuasiIso (((abelianSectionsOnOpen X W).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  let A := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let HA := homotopyAbelianSectionsOnOpen X W
  let RA := derivedAbelianSectionsOnOpen X W
  let α := HA.totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  let M := ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hαM : IsIso (α.app (Q.obj M)) :=
    abelianSectionsUnit_isIso_at_underlying_kInjective O W I
  have hαJ : IsIso (α.app (Q.obj J)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective HA RA α J
  have hq : IsIso (DerivedCategory.Qh.map (Q.map q)) := isIso_Qh_map_quotient_map q
  have hr : IsIso (α.app (Q.obj M) ≫ RA.map (DerivedCategory.Qh.map (Q.map q))) :=
    inferInstance
  have hl : IsIso (HA.map (Q.map q) ≫ α.app (Q.obj J)) := by
    rw [α.naturality (Q.map q)]
    exact hr
  show HomologicalComplex.quasiIso _ _
    (((abelianSectionsOnOpen X W).mapHomologicalComplex (ComplexShape.up ℤ)).map q)
  rw [← HomotopyCategory.quotient_map_mem_quasiIso_iff, ← DerivedCategory.isIso_Qh_map_iff]
  show IsIso (HA.map (Q.map q))
  exact (isIso_comp_right_iff _ _).mp hl

/-! ### Supported sections over a single open -/

/-- The supported-sections endofunctor on abelian sheaves, with source and target spelled as
sheaves for the Grothendieck topology of opens. This is
`ClosedImmersionSheaves.supportedSectionsFunctor` verbatim; only the spelling of the two sheaf
categories differs, as for `abelianSupportedSectionsOnClosed`. -/
abbrev abelianSupportedSections (Z : Set X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ClosedImmersionSheaves.supportedSectionsFunctor Z

/-- The supported-sections endofunctor is additive: supported sections are a subgroup of the
ambient sections, on which addition is the ambient one. -/
instance abelianSupportedSections_additive (Z : Set X) :
    (abelianSupportedSections Z).Additive := by
  refine ⟨?_⟩
  intro F G f g
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  rfl

/-- Sections over the open `W` of the subsheaf of sections supported on `Z`. -/
abbrev supportedSectionsEvaluation (Z : Set X) (W : Opens X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  abelianSupportedSections Z ⋙ abelianSectionsOnOpen X W

/-- Supported sections over an open are additive: they are a subgroup of the ambient sections,
and addition is the ambient one. -/
instance supportedSectionsEvaluation_additive (Z : Set X) (W : Opens X) :
    (supportedSectionsEvaluation Z W).Additive := by
  refine ⟨?_⟩
  intro F G f g
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply Subtype.ext
  rfl

/-- The inclusion of the sections supported on `Z` into all sections over `W`. -/
def supportedSectionsEvaluationInclusion (Z : Set X) (W : Opens X) :
    supportedSectionsEvaluation Z W ⟶ abelianSectionsOnOpen X W where
  app F := (supportedSectionsSheafι Z F).hom.app (op W)
  naturality F G f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    rfl

/-- Restriction of sections over `W` to the part of `W` outside the closed set `Z`. -/
abbrev restrictionToSupportComplement (Z : Set X) (hZ : IsClosed Z) (W : Opens X) :
    abelianSectionsOnOpen X W ⟶ abelianSectionsOnOpen X (W ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩) :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (homOfLE (inf_le_left : W ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ ≤ W)).op

/-- A supported section restricts to zero outside `Z`, naturally in the sheaf. -/
lemma supportedSectionsEvaluation_comp_zero (Z : Set X) (hZ : IsClosed Z) (W : Opens X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (supportedSectionsEvaluationInclusion Z W).app F ≫
      (restrictionToSupportComplement Z hZ W).app F = 0 :=
  ClosedImmersionSheaves.supportedSections_restriction_zero Z hZ F W

/-! ### Supported sections of an underlying abelian complex, over one open -/

/-- **Supported sections over an open take a K-injective resolution of an underlying abelian
complex to a quasi-isomorphism.** This is the flasqueness step of the source's argument. Let `I`
be a K-injective complex of `𝒪_X`-modules with injective terms, let `J` be a K-injective complex
of abelian sheaves with injective terms and let `q : I_ab ⟶ J` be a quasi-isomorphism. For each
open `W`, the sections supported on `Z` over `W` form the kernel of restriction to `W ∖ Z`; the
terms of `I_ab` are flasque by Stacks 09SX and those of `J` are flasque because they are
injective, so in both cases that kernel sits in a short exact sequence of complexes. The outer
two terms of the resulting map of short exact sequences are quasi-isomorphisms by
`abelianSections_map_quasiIso_of_kInjectiveModule`, hence so is the first. -/
lemma supportedSectionsEvaluation_map_quasiIso_of_kInjectiveModule
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (Z : Set X) (hZ : IsClosed Z) (W : Opens X)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective]
    (hI : ∀ n, Injective (I.X n))
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    [J.IsKInjective] (hJ : ∀ n, Injective (J.X n))
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso q] :
    QuasiIso (((supportedSectionsEvaluation Z W).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  let V : Opens X := W ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  let A := supportedSectionsEvaluation Z W
  let B := abelianSectionsOnOpen X W
  let Cc := abelianSectionsOnOpen X V
  let f := supportedSectionsEvaluationInclusion Z W
  let g := restrictionToSupportComplement Z hZ W
  let fc := f.mapHomologicalComplex (ComplexShape.up ℤ)
  let gc := g.mapHomologicalComplex (ComplexShape.up ℤ)
  let M := ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have hz (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ) :
      fc.app K ≫ gc.app K = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    exact supportedSectionsEvaluation_comp_zero Z hZ W (K.X n)
  let S (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ) :=
    ShortComplex.mk (fc.app K) (gc.app K) (hz K)
  have hS (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
      (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj) : (S K).ShortExact := by
    rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
    exact fun n => ClosedImmersionSheaves.supportedSections_restriction_shortExact Z hZ (K.X n)
      (hK n) W
  let k : S M ⟶ S J :=
    { τ₁ := (A.mapHomologicalComplex (ComplexShape.up ℤ)).map q
      τ₂ := (B.mapHomologicalComplex (ComplexShape.up ℤ)).map q
      τ₃ := (Cc.mapHomologicalComplex (ComplexShape.up ℤ)).map q
      comm₁₂ := fc.naturality q
      comm₂₃ := gc.naturality q }
  have h₂ : QuasiIso k.τ₂ := abelianSections_map_quasiIso_of_kInjectiveModule O W I J q
  have h₃ : QuasiIso k.τ₃ := abelianSections_map_quasiIso_of_kInjectiveModule O V I J q
  exact quasiIso_τ₁_of_shortExact k
    (hS M fun n => @Stacks.Cohomology.isFlasque_of_injective_module X _ O (I.X n) (hI n))
    (hS J fun n => @Stacks.Cohomology.isFlasque_of_injective X (J.X n) (hJ n))

/-! ### Supported sections of an underlying abelian complex, as a sheaf -/

/-- **Supported sections take a K-injective resolution of an underlying abelian complex to a
quasi-isomorphism.** The sheaf-level form of
`supportedSectionsEvaluation_map_quasiIso_of_kInjectiveModule`: quasi-isomorphy of a morphism of
complexes of sheaves is detected on the underlying complexes of presheaves, hence open by
open. -/
lemma supportedSections_map_quasiIso_of_kInjectiveModule
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (Z : Set X) (hZ : IsClosed Z)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective]
    (hI : ∀ n, Injective (I.X n))
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    [J.IsKInjective] (hJ : ∀ n, Injective (J.X n))
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso q] :
    QuasiIso (((abelianSupportedSections Z).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  refine sheafQuasiIso_of_presheafQuasiIso _ _ ?_
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro W
  show QuasiIso (((supportedSectionsEvaluation Z (unop W)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map q)
  exact supportedSectionsEvaluation_map_quasiIso_of_kInjectiveModule O Z hZ (unop W) I hI J hJ q

/-! ### Supported sections realized on the closed subset -/

/-- Pushforward of abelian sheaves along the inclusion of the closed subset `Z`, with source and
target spelled as sheaves for the Grothendieck topology of opens. -/
abbrev abelianClosedPushforward (Z : Set X) :
    Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  closedInclusionPushforward (TopCat.of Z) X (ClosedImmersionSheaves.closedSubsetInclusion Z)

/-- `H_Z : Ab(X) ⥤ Ab(Z)`, with source and target spelled as sheaves for the Grothendieck
topology of opens. This is `abelianSupportedSectionsOnClosed` for a bare topological space. -/
abbrev abelianSupportedSectionsRealized (Z : Set X) (hZ : IsClosed Z) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u} :=
  ClosedImmersionSheaves.supportedSectionsOnClosedFunctor Z hZ

/-- `H_Z : Ab(X) ⥤ Ab(Z)` is additive, in the sheaf spelling. -/
instance abelianSupportedSectionsRealized_additive (Z : Set X) (hZ : IsClosed Z) :
    (abelianSupportedSectionsRealized Z hZ).Additive :=
  ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_additive Z hZ

/-- Pushforward along the inclusion of a closed subset is additive, in the sheaf spelling. -/
instance abelianClosedPushforward_additive (Z : Set X) :
    (abelianClosedPushforward Z).Additive where
  map_add := by intros; rfl

/-- Pushforward along the inclusion of a closed subset is fully faithful (Stacks 00AG), so it
reflects isomorphisms. -/
lemma abelianClosedPushforward_reflectsIsomorphisms (Z : Set X) (hZ : IsClosed Z) :
    (abelianClosedPushforward Z).ReflectsIsomorphisms :=
  Functor.FullyFaithful.reflectsIsomorphisms
    (closedInclusionPushforwardFullyFaithful (TopCat.of Z) X
      (ClosedImmersionSheaves.closedSubsetInclusion Z) hZ.isClosedEmbedding_subtypeVal)

/-- Pushing `H_Z : Ab(X) ⥤ Ab(Z)` forward to `X` recovers the supported-sections endofunctor,
in the sheaf spelling. -/
def abelianSupportedSectionsRealizedCompPushforwardIso (Z : Set X) (hZ : IsClosed Z) :
    abelianSupportedSectionsRealized Z hZ ⋙ abelianClosedPushforward Z ≅
      abelianSupportedSections Z :=
  ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_comp_pushforward_iso Z hZ

/-- **Supported sections realized on `Z` take a K-injective resolution of an underlying abelian
complex to a quasi-isomorphism.** This is
`supportedSections_map_quasiIso_of_kInjectiveModule` reflected along pushforward from `Z`, which
is exact and fully faithful, hence reflects quasi-isomorphy. -/
lemma abelianSupportedSectionsRealized_map_quasiIso_of_kInjectiveModule
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (Z : Set X) (hZ : IsClosed Z)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective]
    (hI : ∀ n, Injective (I.X n))
    (J : CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℤ)
    [J.IsKInjective] (hJ : ∀ n, Injective (J.X n))
    (q : ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso q] :
    QuasiIso (((abelianSupportedSectionsRealized Z hZ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
  let A := abelianSupportedSectionsRealized Z hZ
  let P := abelianClosedPushforward Z
  let c := ComplexShape.up ℤ
  have hP : exactFunctor (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u})
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) P :=
    Stacks.ClosedImmersion.exactFunctor_closedInclusionPushforward
      (ClosedImmersionSheaves.closedSubsetInclusion Z) hZ.isClosedEmbedding_subtypeVal
  have : PreservesFiniteLimits P := hP.1
  have : PreservesFiniteColimits P := hP.2
  have : (abelianClosedPushforward Z).ReflectsIsomorphisms :=
    abelianClosedPushforward_reflectsIsomorphisms Z hZ
  have hAP : QuasiIso (((A ⋙ P).mapHomologicalComplex c).map q) :=
    quasiIso_map_of_functor_iso
      (NatIso.mapHomologicalComplex (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ) c) q
      (supportedSections_map_quasiIso_of_kInjectiveModule O Z hZ I hI J hJ q)
  have hPA : QuasiIso ((P.mapHomologicalComplex c).map ((A.mapHomologicalComplex c).map q)) :=
    quasiIso_map_of_functor_iso
      (Functor.mapHomologicalComplexCompIso (Iso.refl (A ⋙ P)) c).symm q hAP
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((A.mapHomologicalComplex c).map q) P).mp hPA

/-! ### The derivation unit of abelian supported sections at an underlying complex -/

/-- **The derivation unit of `RH_Z` on abelian sheaves is invertible at the underlying abelian
complex of a K-injective complex of modules with injective terms.** This is the point of the
whole argument: `I_ab` is not a complex of injective abelian sheaves and is not K-injective, yet
it still computes `RH_Z`, because its terms are flasque and flasque abelian sheaves are acyclic
for supported sections. Formally: a K-injective resolution `q : I_ab ⟶ J` of `I_ab` stays a
quasi-isomorphism after applying `H_Z`
(`abelianSupportedSectionsRealized_map_quasiIso_of_kInjectiveModule`), and the unit is invertible
at the K-injective `J`, so naturality transports invertibility back to `I_ab`. -/
lemma abelianSupportedUnit_isIso_at_underlying_kInjective
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (Z : Set X) (hZ : IsClosed Z)
    (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}))
    (aHab : (abelianSupportedSectionsRealized Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective]
    (hI : ∀ n, Injective (I.X n)) :
    IsIso (aHab.app
      (((SheafOfModules.toSheaf O).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  let Ab := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let A := abelianSupportedSectionsRealized Z hZ
  let M : CochainComplex Ab ℤ :=
    ((SheafOfModules.toSheaf O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let J : CochainComplex Ab ℤ := (Stacks.Injectives.kInjectiveResolutionFunctor Ab).obj M
  let q : M ⟶ J := (Stacks.Injectives.kInjectiveResolutionInclusion Ab).app M
  have _ : J.IsKInjective :=
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective Ab M
  have _ : QuasiIso q := Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso Ab M
  let Q := HomotopyCategory.quotient Ab (ComplexShape.up ℤ)
  have hαJ : IsIso (aHab.app (Q.obj J)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
      (A.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) RHab aHab J
  have hqA : IsIso ((A.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).map (Q.map q)) := by
    have := abelianSupportedSectionsRealized_map_quasiIso_of_kInjectiveModule O Z hZ I hI J
      (fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective Ab M n) q
    exact isIso_Qh_map_quotient_map ((A.mapHomologicalComplex (ComplexShape.up ℤ)).map q)
  have hqD : IsIso (DerivedCategory.Qh.map (Q.map q)) := isIso_Qh_map_quotient_map q
  have hqR : IsIso ((DerivedCategory.Qh ⋙ RHab).map (Q.map q)) :=
    Functor.map_isIso RHab (DerivedCategory.Qh.map (Q.map q))
  have hcomp : IsIso (aHab.app (Q.obj M) ≫ (DerivedCategory.Qh ⋙ RHab).map (Q.map q)) := by
    rw [← aHab.naturality (Q.map q)]
    infer_instance
  show IsIso (aHab.app (Q.obj M))
  exact (isIso_comp_right_iff _ _).mp hcomp

/-! ### Invertibility of the comparison of Tag 0G74 (2) -/

/-- **Stacks 0G74, part (2).** Let `Z` be a closed subset of a ringed space `X`, let `RH` be a
right derived functor of the sections supported on `Z` of sheaves of `𝒪_X`-modules and let
`RHab` be one of the sections supported on `Z` of abelian sheaves. The canonical map

`RH_Z(K)_ab ⟶ RH_Z(K_ab)`

of `localCohomologySheafForgetComparison` is an **isomorphism** in `D(Ab(Z))`, in all degrees.

The proof is the source's. It is enough to check invertibility at the image of a K-injective
complex `K` of `𝒪_X`-modules, and a K-injective resolution of `K` with injective terms has the
same image in the derived category, so one may take the terms of `K` injective. There the
derivation unit of `RH` is invertible because `K` is K-injective, and the transported unit is
invertible by `abelianSupportedUnit_isIso_at_underlying_kInjective` — which is where flasqueness
enters: the underlying abelian sheaf of an injective `𝒪_X`-module is flasque (Stacks 09SX), and
supported sections of a flasque abelian sheaf are the kernel of a *surjection* between sections
over two opens, so `K_ab` computes the derived functor even though it is neither K-injective nor
a complex of injectives. The defining factorization
`localCohomologySheafForgetComparison_fac` then forces the comparison itself to be
invertible. -/
@[stacks 0G74 "part (2), invertibility of the canonical map"]
theorem isIso_localCohomologySheafForgetComparison_of_isRightDerivedFunctor
    (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
    (RHab : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}))
    (aHab : (abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RHab)
    [RHab.IsRightDerivedFunctor aHab
      (HomotopyCategory.quasiIso
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
    (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory
        (_root_.SheafOfModules.{u} (structureSheafRing (closedSubsetRingedSpace X Z))))
    (aH : (supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    IsIso (localCohomologySheafForgetComparison X Z hZ RHab aHab RH aH) := by
  let Md := _root_.SheafOfModules.{u} (structureSheafRing X)
  apply Stacks.Cohomology.Localization.natTrans_isIso_of_kInjectives
  intro K _
  let Q := HomotopyCategory.quotient Md (ComplexShape.up ℤ)
  let I : CochainComplex Md ℤ := (Stacks.Injectives.kInjectiveResolutionFunctor Md).obj K
  let q : K ⟶ I := (Stacks.Injectives.kInjectiveResolutionInclusion Md).app K
  have _ : I.IsKInjective :=
    Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective Md K
  have _ : QuasiIso q := Stacks.Injectives.kInjectiveResolutionInclusion_quasiIso Md K
  have hq : IsIso (DerivedCategory.Qh.map (Q.map q)) := isIso_Qh_map_quotient_map q
  rw [NatTrans.isIso_app_iff_of_iso _ (asIso (DerivedCategory.Qh.map (Q.map q)))]
  have hβI : IsIso ((supportedSheafForgetUnit X Z hZ RHab aHab).app (Q.obj I)) := by
    have hα := abelianSupportedUnit_isIso_at_underlying_kInjective (structureSheafRing X) Z hZ
      RHab aHab I (fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective Md K n)
    unfold supportedSheafForgetUnit
    refine isIso_comp_app _ _ _ ?_ (isIso_comp_app _ _ _ ?_ (isIso_comp_app _ _ _ ?_
      (isIso_comp_app _ _ _ ?_ (isIso_comp_app _ _ _ ?_ (isIso_comp_app _ _ _ ?_ ?_)))))
    · exact isIso_whiskerLeft_isoHom_app _ _ _
    · exact isIso_associator_inv_app _ _ _ _
    · exact isIso_whiskerRight_isoHom_app _ _ _
    · exact isIso_whiskerRight_isoInv_app _ _ _
    · exact isIso_associator_hom_app _ _ _ _
    · exact isIso_whiskerLeft_app _ aHab _ hα
    · exact isIso_whiskerRight_isoInv_app _ _ _
  have haI : IsIso ((forgetfulSupportedSheafUnit X Z hZ RH aH).app (Q.obj I)) := by
    have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
      ((supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) RH aH I
    dsimp only [forgetfulSupportedSheafUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.associator_hom_app]
    infer_instance
  have hfac : (forgetfulSupportedSheafUnit X Z hZ RH aH).app (Q.obj I) ≫
      (localCohomologySheafForgetComparison X Z hZ RHab aHab RH aH).app
        (DerivedCategory.Qh.obj (Q.obj I)) =
      (supportedSheafForgetUnit X Z hZ RHab aHab).app (Q.obj I) := by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using
      congrArg (fun t => t.app (Q.obj I))
        (localCohomologySheafForgetComparison_fac X Z hZ RHab aHab RH aH)
  rw [← hfac] at hβI
  exact (isIso_comp_left_iff _ _).mp hβI

end Stacks.Cohomology.SupportedComplexes

end
