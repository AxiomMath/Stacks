module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Global sections of a module on a scheme as morphisms from the structure sheaf

A global section of a module `M` on a scheme `X` is the same thing as a morphism from the
structure sheaf of `X`, viewed as a module over itself, into `M`.  Pulling a module back along a
morphism of schemes carries the structure sheaf to the structure sheaf, so a global section of
`M` on `Y` gives, after pullback along `f : X ⟶ Y`, a global section of `f⁺ M`.  This file
supplies these two identifications and their compatibility with composition.

## Main definitions

* `AlgebraicGeometry.Scheme.unitModule`: the structure sheaf of a scheme as a module over
  itself.
* `AlgebraicGeometry.Scheme.Modules.sectionsTopEquiv`: global sections over `⊤` are the sections
  of the underlying sheaf in the sense of `CategoryTheory.SheafOfModules.sections`.
* `AlgebraicGeometry.Scheme.Modules.unitHomEquivTop`: global sections over `⊤` are the morphisms
  from the structure sheaf.
* `AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit`: the canonical morphism
  `𝒪_Y ⟶ f_* 𝒪_X`.
* `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`: the pullback of the structure sheaf of the
  target of a morphism of schemes is the structure sheaf of the source.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp` and
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq`: `pullbackUnitIso` is compatible
  with composition of morphisms of schemes.
* `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_sections_naturality`: the morphism out of
  the structure sheaf attached to a global section is natural under pullback followed by a
  morphism of modules on the source.

## Implementation notes

`pullbackUnitIso` is Mathlib's comparison `CategoryTheory.SheafOfModules.pullbackObjUnitToUnit`,
which is an isomorphism as soon as the functor on opens induced by the continuous map is final;
for a morphism of schemes this holds because that functor is representably flat.

The compatibilities are proved after transposing along the pullback--pushforward adjunction,
where `pullbackUnitIso` becomes `unitToPushforwardUnit`.  The adjunction's `homEquiv` is
injective, so nothing is lost, and this replaces computations with the left adjoint — which is
an abstract adjoint with no formula — by computations with the right adjoint, which acts on
sections by restriction.

Three definitions here exist only to ascribe a type: `Scheme.unitModule`,
`Scheme.Modules.unitToPushforwardUnit` and `Scheme.Modules.unitHomEquivTop` name objects that
Mathlib already provides, but at the types `X.Modules`, `𝒪_Y ⟶ f_* 𝒪_X` and
`𝒪_X ⟶ M` rather than at the corresponding `CategoryTheory.SheafOfModules` types.  The two
descriptions are definitionally equal, but not at the transparency at which `rw` and `simp`
check that a goal is type-correct, so a goal written with the Mathlib spellings is rejected by
those tactics even when every rewrite applies.  Naming each identification once, at the type
its consumers use, keeps every intermediate goal type-correct.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The structure sheaf of a scheme, viewed as a module over itself. -/
noncomputable def Scheme.unitModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

instance (X : Scheme.{u}) : (Scheme.unitModule X).IsQuasicoherent :=
  inferInstanceAs (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent

/-- Restriction maps of a module on a scheme compose. -/
lemma Scheme.Modules.presheaf_map_comp_apply {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opensᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x : M.presheaf.obj U) :
    M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map (i ≫ j) x := by
  rw [M.presheaf.map_comp]; rfl

/-- A morphism of modules on a scheme commutes with the restriction maps. -/
lemma Scheme.Modules.Hom.app_presheaf_map {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {U V : X.Opens} (i : U ⟶ V) (x : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app V x) := by
  have h := φ.mapPresheaf.naturality i.op
  exact congr($h x)

/-- Global sections of a module on a scheme over `⊤` are the sections of its underlying sheaf,
because `⊤` is a terminal object of the lattice of opens. -/
noncomputable def Scheme.Modules.sectionsTopEquiv {X : Scheme.{u}} (M : X.Modules) :
    Γ(M, ⊤) ≃ M.sections :=
  (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M
    (isTerminalTop (α := X.Opens))).symm

/-- The section attached to a global section restricts to it on every open set. -/
lemma Scheme.Modules.sectionsTopEquiv_val {X : Scheme.{u}} (M : X.Modules) (x : Γ(M, ⊤))
    (U : X.Opensᵒᵖ) :
    (Scheme.Modules.sectionsTopEquiv M x).val U =
      M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op x := by
  have h : isTerminalTop.from U.unop = homOfLE (le_top : U.unop ≤ ⊤) := Subsingleton.elim _ _
  exact PresheafOfModules.congr_map_apply M.val (congrArg Quiver.Hom.op h) x

/-- Pushing a section forward along a morphism of schemes evaluates it on preimages. -/
lemma Scheme.Modules.pushforwardSections_val {X Y : Scheme.{u}} (f : X ⟶ Y) (N : X.Modules)
    (s : N.sections) (U : Y.Opensᵒᵖ) :
    (SheafOfModules.pushforwardSections f.toRingCatSheafHom s).val U =
      s.val (op (f ⁻¹ᵁ U.unop)) := rfl

/-- The action of a morphism of modules on sections is its action on sections over each open
set. -/
lemma Scheme.Modules.sectionsMap_val {X : Scheme.{u}} {M N : X.Modules} (α : M ⟶ N)
    (s : M.sections) (U : X.Opensᵒᵖ) :
    (SheafOfModules.sectionsMap α s).val U = α.app U.unop (s.val U) := rfl

/-- Global sections of a module on a scheme are the morphisms from the structure sheaf. -/
noncomputable def Scheme.Modules.unitHomEquivTop {X : Scheme.{u}} (M : X.Modules) :
    Γ(M, ⊤) ≃ (Scheme.unitModule X ⟶ M) :=
  (Scheme.Modules.sectionsTopEquiv M).trans (SheafOfModules.unitHomEquiv M).symm

/-- The section underlying the morphism attached to a global section is the section attached to
it by `AlgebraicGeometry.Scheme.Modules.sectionsTopEquiv`. -/
lemma Scheme.Modules.unitHomEquiv_unitHomEquivTop {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, ⊤)) :
    SheafOfModules.unitHomEquiv M (Scheme.Modules.unitHomEquivTop M x) =
      Scheme.Modules.sectionsTopEquiv M x :=
  (SheafOfModules.unitHomEquiv M).apply_symm_apply _

/-- The canonical morphism `𝒪_Y ⟶ f_* 𝒪_X` attached to a morphism of schemes `f : X ⟶ Y`. -/
noncomputable def Scheme.Modules.unitToPushforwardUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.unitModule Y ⟶ (Scheme.Modules.pushforward f).obj (Scheme.unitModule X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- The morphisms `𝒪 ⟶ f_* 𝒪` are compatible with composition of morphisms of schemes. -/
lemma Scheme.Modules.unitToPushforwardUnit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.Modules.unitToPushforwardUnit g ≫
        (Scheme.Modules.pushforward g).map (Scheme.Modules.unitToPushforwardUnit f) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (Scheme.unitModule X) =
      Scheme.Modules.unitToPushforwardUnit (f ≫ g) := by
  ext U
  rfl

/-- **The pullback of the structure sheaf is the structure sheaf.**  For a morphism of schemes
`f : X ⟶ Y`, pulling the structure sheaf of `Y` back along `f` gives the structure sheaf of
`X`. -/
noncomputable def Scheme.Modules.pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (Scheme.unitModule Y) ≅ Scheme.unitModule X :=
  have : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have hiso : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) hiso

/-- Under the pullback--pushforward adjunction, `pullbackUnitIso` transposes to
`unitToPushforwardUnit`. -/
lemma Scheme.Modules.pullbackUnitIso_homEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (Scheme.Modules.pullbackUnitIso f).hom =
      Scheme.Modules.unitToPushforwardUnit f := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- `pullbackUnitIso` is compatible with composition of morphisms of schemes. -/
lemma Scheme.Modules.pullbackUnitIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).inv.app (Scheme.unitModule Z) ≫
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
      (Scheme.Modules.pullbackUnitIso f).hom =
      (Scheme.Modules.pullbackUnitIso (f ≫ g)).hom := by
  have hu : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Scheme.unitModule Y) ≫
        (Scheme.Modules.pushforward f).map (Scheme.Modules.pullbackUnitIso f).hom =
      Scheme.Modules.unitToPushforwardUnit f := fun f ↦
    Scheme.Modules.pullbackUnitIso_homEquiv f
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [Scheme.Modules.pullbackUnitIso_homEquiv]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [pullbackComp_unit]
  simp only [Category.assoc]
  rw [← (Scheme.Modules.pushforwardComp f g).hom.naturality_assoc,
    ← (Scheme.Modules.pushforwardComp f g).hom.naturality]
  simp only [Functor.comp_map]
  simp only [← Functor.map_comp_assoc]
  erw [reassoc_of%
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality
      (Scheme.Modules.pullbackUnitIso g).hom).symm]
  rw [hu f]
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  rw [hu g]
  simp only [Category.assoc]
  exact Scheme.Modules.unitToPushforwardUnit_comp f g

/-- The composition compatibility of `pullbackUnitIso`, in the form needed for a factorisation
`f ≫ g = h` of morphisms of schemes. -/
lemma Scheme.Modules.pullbackUnitIso_comp_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    (Scheme.Modules.pullbackCongr w).inv.app (Scheme.unitModule Z) ≫
      (Scheme.Modules.pullbackComp f g).inv.app (Scheme.unitModule Z) ≫
      (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
      (Scheme.Modules.pullbackUnitIso f).hom =
      (Scheme.Modules.pullbackUnitIso h).hom := by
  subst h
  simpa [Scheme.Modules.pullbackCongr, NatTrans.id_app] using
    Scheme.Modules.pullbackUnitIso_comp f g

private lemma pushforwardSections_sectionsTopEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (N : X.Modules)
    (α : M ⟶ (Scheme.Modules.pushforward f).obj N) (x : Γ(M, ⊤)) :
    SheafOfModules.pushforwardSections f.toRingCatSheafHom
        (Scheme.Modules.sectionsTopEquiv N
          (N.presheaf.map (eqToHom (show ⊤ = f ⁻¹ᵁ ⊤ by simp)).op (α.app ⊤ x))) =
      SheafOfModules.sectionsMap α (Scheme.Modules.sectionsTopEquiv M x) := by
  ext Z
  rw [Scheme.Modules.pushforwardSections_val, Scheme.Modules.sectionsTopEquiv_val,
    Scheme.Modules.sectionsMap_val, Scheme.Modules.sectionsTopEquiv_val,
    Scheme.Modules.Hom.app_presheaf_map, Scheme.Modules.pushforward_obj_presheaf_map]
  exact (Scheme.Modules.presheaf_map_comp_apply N _ _ _).trans
    (congrArg (fun k ↦ N.presheaf.map k (α.app ⊤ x)) (Subsingleton.elim _ _))

/-- **Naturality of the morphism out of the structure sheaf attached to a global section.**  Let
`f : X ⟶ Y` and `k : f⁺ M ⟶ N`.  The morphism `𝒪_X ⟶ N` attached to the global section of `N`
obtained from a global section `x` of `M` by transposing `k` is the pullback of the morphism
`𝒪_Y ⟶ M` attached to `x`, followed by `k`. -/
lemma Scheme.Modules.pullbackUnitIso_sections_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (N : X.Modules)
    (k : (Scheme.Modules.pullback f).obj M ⟶ N) (x : Γ(M, ⊤)) :
    (Scheme.Modules.pullbackUnitIso f).hom ≫
        Scheme.Modules.unitHomEquivTop N
          (N.presheaf.map (eqToHom (show ⊤ = f ⁻¹ᵁ ⊤ by simp)).op
            (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N k).app ⊤ x)) =
      (Scheme.Modules.pullback f).map (Scheme.Modules.unitHomEquivTop M x) ≫ k := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Scheme.Modules.pullbackUnitIso_homEquiv,
    Adjunction.homEquiv_naturality_left]
  apply (SheafOfModules.unitHomEquiv _).injective
  exact (SheafOfModules.pushforwardSections_unitHomEquiv f.toRingCatSheafHom
      (Scheme.Modules.unitHomEquivTop N _)).symm.trans
    ((((congrArg (SheafOfModules.pushforwardSections f.toRingCatSheafHom)
            (Scheme.Modules.unitHomEquiv_unitHomEquivTop N _)).trans
          (pushforwardSections_sectionsTopEquiv f M N _ x)).trans
        (congrArg (SheafOfModules.sectionsMap _)
          (Scheme.Modules.unitHomEquiv_unitHomEquivTop M x)).symm).trans
      (SheafOfModules.unitHomEquiv_comp_apply _ _).symm)

end AlgebraicGeometry

end
