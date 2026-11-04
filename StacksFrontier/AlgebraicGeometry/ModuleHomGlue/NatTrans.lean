module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# Glueing natural transformations of module-valued functors over an open cover

Let `Y` be a scheme, let `C` be any category and let `G H : C ⥤ Y.Modules` be two functors into
the sheaves of `𝒪_Y`-modules. This file introduces the notion of a **natural transformation
`G ⟶ H` given only over an open `U` of `Y`**, assembles a family of such over an open cover of
`Y` into a single natural transformation `G ⟶ H`, and shows that the assembled transformation is
an isomorphism as soon as each member of the family is.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.LocalNatTrans`: a natural transformation from `G`
  to `H` defined over an open `U` of `Y`, recorded as maps on sections over the opens `V ≤ U`
  which are `Γ(Y, V)`-linear, compatible with restriction, and natural in the object of `C`.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.LocalNatTrans.ofNatTrans`: the restriction of a
  global natural transformation `G ⟶ H` to an open `U`.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.CompatibleFamily`: a **compatible family** of such
  local transformations over a family of opens `U : ι → Y.Opens`, the compatibility being
  agreement on every open contained in two members of the family.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.CompatibleFamily.glue`: the glued natural
  transformation `G ⟶ H`.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.CompatibleFamily.glueIso`: the glued natural
  isomorphism `G ≅ H`, when every member of the family is invertible on sections.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.glueFullSubcategory`: the same glueing for functors
  into a full subcategory of `Y.Modules`, along its fully faithful inclusion.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.quasicoherent`: quasi-coherence as a
  `CategoryTheory.ObjectProperty` on `Y.Modules`, whose full subcategory is `QCoh(𝒪_Y)`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.hom_ext_of_le_cover`: **equality of morphisms of
  sheaves of modules is local, in directed form.** Two morphisms which agree on every open
  contained in a member of an open cover are equal.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.isIso_of_isIso_app_of_le_cover`: **invertibility of
  a morphism of sheaves of modules is local, in directed form.**
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.CompatibleFamily.existsUnique_natTrans`:
  **natural transformations of module-valued functors glue over an open cover.** A compatible
  family of local natural transformations over an open cover of `Y` comes from exactly one
  natural transformation `G ⟶ H`.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.CompatibleFamily.natTrans_ext`,
  `Stacks.AlgebraicGeometry.ModuleNatTransGlue.natTrans_ext_of_fullSubcategory` and
  `Stacks.AlgebraicGeometry.ModuleNatTransGlue.natTrans_ext_quasicoherent`: **a natural
  transformation is determined by its restrictions to the members of an open cover of `Y`**, the
  separation half of the same statement.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.CompatibleFamily.isIso_glue`: the glued
  transformation is an isomorphism as soon as every member of the family is invertible on
  sections.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.existsUnique_natTrans_of_fullSubcategory` and
  `Stacks.AlgebraicGeometry.ModuleNatTransGlue.isIso_glueFullSubcategory`: the same two statements
  for functors into a full subcategory of `Y.Modules`.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.existsUnique_natTrans_quasicoherent` and
  `Stacks.AlgebraicGeometry.ModuleNatTransGlue.isIso_glueFullSubcategory_quasicoherent`:
  **natural transformations of `QCoh(𝒪_Y)`-valued functors glue over an open cover of `Y`**, and
  the glued transformation is an isomorphism when the family is.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ModuleNatTransGlue

universe u v w

variable {Y : Scheme.{u}} {C : Type v} [Category.{w} C]

/-! ### Locality of equality and of invertibility, in directed form -/

/-- **Equality of morphisms of sheaves of modules is local, in directed form.** Two morphisms
`M ⟶ N` of sheaves of `𝒪_Y`-modules which agree on sections over every open of `Y` contained in
some member of an open cover are equal. -/
theorem hom_ext_of_le_cover {M N : Y.Modules} {ι : Type u} {U : ι → Y.Opens}
    (hU : IsOpenCover U) {φ ψ : M ⟶ N}
    (h : ∀ (i : ι) (V : Y.Opens), V ≤ U i → φ.app V = ψ.app V) : φ = ψ := by
  obtain ⟨χ, -, huniq⟩ :=
    ModuleHomGlue.existsUnique_hom_of_cover_app hU.iSup_eq_top (fun _ V _ => φ.app V)
      (fun _ _ _ r s => Scheme.Modules.Hom.app_smul φ r s)
      (fun _ _ _ _ hWV s => (ModuleLimits.Hom_app_presheaf_map φ hWV s).symm)
      (fun _ _ _ _ _ => rfl)
  exact (huniq φ fun _ _ _ => rfl).trans (huniq ψ fun i V hV => (h i V hV).symm).symm

/-- A morphism of sheaves of modules on a scheme which is invertible on the sections over every
open is invertible. -/
theorem isIso_of_isIso_app {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N)
    (h : ∀ V : Z.Opens, IsIso (φ.app V)) : IsIso φ := by
  rw [← isIso_iff_of_reflects_iso φ (Scheme.Modules.toPresheaf Z)]
  have h' : ∀ V, IsIso (((Scheme.Modules.toPresheaf Z).map φ).app V) := fun V => h V.unop
  exact NatIso.isIso_of_isIso_app _

/-- **Invertibility of a morphism of sheaves of modules is local, in directed form.** A morphism
`M ⟶ N` which is invertible on the sections over every open contained in some member of an open
cover is invertible. -/
theorem isIso_of_isIso_app_of_le_cover {M N : Y.Modules} {ι : Type*} {U : ι → Y.Opens}
    (hU : IsOpenCover U) (φ : M ⟶ N)
    (h : ∀ (i : ι) (V : Y.Opens), V ≤ U i → IsIso (φ.app V)) : IsIso φ :=
  AffineBaseChange.isIso_of_isIso_restrict φ U hU fun i =>
    isIso_of_isIso_app _ fun W => h i _ ((U i).ι_image_le W)

/-! ### Natural transformations defined over an open -/

/-- **A natural transformation `G ⟶ H` defined only over an open `U` of `Y`.** The data is a map
on sections `Γ(G.obj A, V) ⟶ Γ(H.obj A, V)` for every object `A` of `C` and every open `V ≤ U`,
subject to three conditions: it is `Γ(Y, V)`-linear, it commutes with the restriction maps of the
two sheaves, and it is natural in `A`. -/
structure LocalNatTrans (G H : C ⥤ Y.Modules) (U : Y.Opens) where
  /-- The map on sections over an open `V ≤ U`, at an object `A` of `C`. -/
  app (A : C) (V : Y.Opens) (hV : V ≤ U) : Γ(G.obj A, V) ⟶ Γ(H.obj A, V)
  /-- The maps on sections are linear over the sections of the structure sheaf. -/
  app_smul (A : C) (V : Y.Opens) (hV : V ≤ U) (r : Γ(Y, V)) (s : Γ(G.obj A, V)) :
    app A V hV (r • s) = r • app A V hV s
  /-- The maps on sections commute with the restriction maps of the two sheaves. -/
  app_map (A : C) (V W : Y.Opens) (hV : V ≤ U) (hWV : W ≤ V) (s : Γ(G.obj A, V)) :
    app A W (hWV.trans hV) ((G.obj A).presheaf.map (homOfLE hWV).op s) =
      (H.obj A).presheaf.map (homOfLE hWV).op (app A V hV s)
  /-- The maps on sections are natural in the object of `C`. -/
  app_naturality {A B : C} (φ : A ⟶ B) (V : Y.Opens) (hV : V ≤ U) (s : Γ(G.obj A, V)) :
    app B V hV ((G.map φ).app V s) = (H.map φ).app V (app A V hV s)

namespace LocalNatTrans

variable {G H : C ⥤ Y.Modules}

/-- Two natural transformations over an open `U` with the same maps on sections are equal. -/
@[ext] theorem ext {U : Y.Opens} :
    ∀ {f g : LocalNatTrans G H U}, f.app = g.app → f = g
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

/-- **The restriction of a global natural transformation to an open.** -/
def ofNatTrans (α : G ⟶ H) (U : Y.Opens) : LocalNatTrans G H U where
  app A V _ := (α.app A).app V
  app_smul _ _ _ r s := Scheme.Modules.Hom.app_smul _ r s
  app_map A _ _ _ hWV s := (ModuleLimits.Hom_app_presheaf_map (α.app A) hWV s).symm
  app_naturality {A B} φ V _ s :=
    congrArg (fun χ : G.obj A ⟶ H.obj B => (ConcreteCategory.hom (Scheme.Modules.Hom.app χ V)) s)
      (α.naturality φ)

/-- The maps on sections of the restriction of `α` to `U` are the components of `α`. -/
@[simp]
theorem ofNatTrans_app (α : G ⟶ H) (U : Y.Opens) (A : C) (V : Y.Opens) (hV : V ≤ U) :
    (ofNatTrans α U).app A V hV = (α.app A).app V :=
  rfl

end LocalNatTrans

/-! ### Compatible families and their gluing -/

/-- **A compatible family of natural transformations over a family of opens.** For each index `i`
a natural transformation `G ⟶ H` over the open `U i`, any two of which agree on the sections over
every open of `Y` contained in both of their domains. -/
structure CompatibleFamily (G H : C ⥤ Y.Modules) {ι : Type u} (U : ι → Y.Opens) where
  /-- The member of the family over `U i`. -/
  trans (i : ι) : LocalNatTrans G H (U i)
  /-- Two members of the family agree over every open contained in both of their domains. -/
  agree (A : C) (i j : ι) (V : Y.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j) :
    (trans i).app A V hVi = (trans j).app A V hVj

namespace CompatibleFamily

variable {G H : C ⥤ Y.Modules} {ι : Type u} {U : ι → Y.Opens}

/-- At each object of `C` the family glues to exactly one morphism of sheaves of modules. -/
theorem existsUnique_app (f : CompatibleFamily G H U) (hU : IsOpenCover U) (A : C) :
    ∃! φ : G.obj A ⟶ H.obj A,
      ∀ (i : ι) (V : Y.Opens) (hV : V ≤ U i), φ.app V = (f.trans i).app A V hV :=
  ModuleHomGlue.existsUnique_hom_of_cover_app hU.iSup_eq_top (fun i => (f.trans i).app A)
    (fun i => (f.trans i).app_smul A) (fun i => (f.trans i).app_map A)
    (fun i j => f.agree A i j)

/-- The morphism `G.obj A ⟶ H.obj A` glued from the family at the object `A`. -/
def glueApp (f : CompatibleFamily G H U) (hU : IsOpenCover U) (A : C) :
    G.obj A ⟶ H.obj A :=
  (f.existsUnique_app hU A).choose

/-- Over an open contained in `U i`, the morphism glued at `A` is the `i`-th member of the
family. -/
@[simp]
theorem glueApp_app (f : CompatibleFamily G H U) (hU : IsOpenCover U) (A : C) (i : ι)
    (V : Y.Opens) (hV : V ≤ U i) :
    (f.glueApp hU A).app V = (f.trans i).app A V hV :=
  (f.existsUnique_app hU A).choose_spec.1 i V hV

/-- The glued morphism at an object is the only one restricting to the family. -/
theorem eq_glueApp (f : CompatibleFamily G H U) (hU : IsOpenCover U) {A : C}
    (φ : G.obj A ⟶ H.obj A)
    (hφ : ∀ (i : ι) (V : Y.Opens) (hV : V ≤ U i), φ.app V = (f.trans i).app A V hV) :
    φ = f.glueApp hU A :=
  (f.existsUnique_app hU A).choose_spec.2 φ hφ

/-- **The natural transformation glued from a compatible family over an open cover.** Its
component at an object `A` of `C` is the morphism glued from the family at `A`. -/
def glue (f : CompatibleFamily G H U) (hU : IsOpenCover U) : G ⟶ H where
  app A := f.glueApp hU A
  naturality A B φ := by
    refine hom_ext_of_le_cover hU fun i V hV => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
      f.glueApp_app hU B i V hV, f.glueApp_app hU A i V hV]
    ext s
    exact (f.trans i).app_naturality φ V hV s

/-- The component at `A` of the glued transformation is the morphism glued at `A`. -/
@[simp]
theorem glue_app (f : CompatibleFamily G H U) (hU : IsOpenCover U) (A : C) :
    (f.glue hU).app A = f.glueApp hU A := rfl

/-- The glued transformation restricts, over each member of the cover, to the corresponding
member of the family. -/
@[simp]
theorem ofNatTrans_glue (f : CompatibleFamily G H U) (hU : IsOpenCover U) (i : ι) :
    LocalNatTrans.ofNatTrans (f.glue hU) (U i) = f.trans i := by
  refine LocalNatTrans.ext (funext fun A => funext fun V => funext fun hV => ?_)
  exact f.glueApp_app hU A i V hV

/-- **Natural transformations of module-valued functors glue over an open cover.** Let `Y` be a
scheme, `C` any category and `G H : C ⥤ Y.Modules`. A compatible family of natural
transformations `G ⟶ H` over the members of an open cover of `Y` comes from exactly one natural
transformation `G ⟶ H`. -/
theorem existsUnique_natTrans (f : CompatibleFamily G H U) (hU : IsOpenCover U) :
    ∃! α : G ⟶ H, ∀ i : ι, LocalNatTrans.ofNatTrans α (U i) = f.trans i := by
  refine ⟨f.glue hU, f.ofNatTrans_glue hU, fun α hα => ?_⟩
  refine NatTrans.ext (funext fun A => ?_)
  refine f.eq_glueApp hU _ fun i V hV => ?_
  exact congrFun (congrFun (congrFun
    (congrArg (fun g : LocalNatTrans G H (U i) => g.app) (hα i)) A) V) hV

/-- **The glued transformation is an isomorphism when the family is.** If every member of the
family is invertible on the sections over every open contained in its domain, then the glued
natural transformation `G ⟶ H` is a natural isomorphism. -/
theorem isIso_glue (f : CompatibleFamily G H U) (hU : IsOpenCover U)
    (h : ∀ (A : C) (i : ι) (V : Y.Opens) (hV : V ≤ U i), IsIso ((f.trans i).app A V hV)) :
    IsIso (f.glue hU) := by
  have h' : ∀ A : C, IsIso ((f.glue hU).app A) := fun A =>
    isIso_of_isIso_app_of_le_cover hU _ fun i V hV => by
      rw [glue_app, f.glueApp_app hU A i V hV]; exact h A i V hV
  exact NatIso.isIso_of_isIso_app _

/-- **The natural isomorphism glued from a compatible family of invertible local
transformations.** -/
def glueIso (f : CompatibleFamily G H U) (hU : IsOpenCover U)
    (h : ∀ (A : C) (i : ι) (V : Y.Opens) (hV : V ≤ U i), IsIso ((f.trans i).app A V hV)) :
    G ≅ H :=
  haveI := f.isIso_glue hU h
  asIso (f.glue hU)

/-- The forward map of the glued isomorphism is the glued transformation. -/
@[simp]
theorem glueIso_hom (f : CompatibleFamily G H U) (hU : IsOpenCover U)
    (h : ∀ (A : C) (i : ι) (V : Y.Opens) (hV : V ≤ U i), IsIso ((f.trans i).app A V hV)) :
    (f.glueIso hU h).hom = f.glue hU :=
  rfl

/-- **Every natural transformation gives a compatible family:** restrict it to each member of
the family of opens. -/
def ofNatTrans (α : G ⟶ H) (U : ι → Y.Opens) : CompatibleFamily G H U where
  trans i := LocalNatTrans.ofNatTrans α (U i)
  agree _ _ _ _ _ _ := rfl

/-- The `i`-th member of the family cut out of `α` is the restriction of `α` to `U i`. -/
@[simp]
theorem ofNatTrans_trans (α : G ⟶ H) (U : ι → Y.Opens) (i : ι) :
    (ofNatTrans α U).trans i = LocalNatTrans.ofNatTrans α (U i) :=
  rfl

/-- Glueing the family cut out of a natural transformation returns that transformation. -/
@[simp]
theorem glue_ofNatTrans (α : G ⟶ H) (hU : IsOpenCover U) : (ofNatTrans α U).glue hU = α :=
  ((ofNatTrans α U).existsUnique_natTrans hU).unique
    ((ofNatTrans α U).ofNatTrans_glue hU) fun _ => rfl

/-- **A natural transformation of module-valued functors is determined by its restrictions to
the members of an open cover of the target.** -/
theorem natTrans_ext (hU : IsOpenCover U) {α γ : G ⟶ H}
    (h : ∀ i : ι, LocalNatTrans.ofNatTrans α (U i) = LocalNatTrans.ofNatTrans γ (U i)) :
    α = γ :=
  ((ofNatTrans α U).existsUnique_natTrans hU).unique (fun _ => rfl) fun i => (h i).symm

end CompatibleFamily

/-! ### Functors into a full subcategory, in particular into the quasi-coherent modules -/

section FullSubcategory

variable {P : ObjectProperty Y.Modules} {G H : C ⥤ P.FullSubcategory}
  {ι : Type u} {U : ι → Y.Opens}

/-- **The natural transformation `G ⟶ H` glued from a compatible family, for functors into a full
subcategory of `Y.Modules`.** Its component at `A` is the component of
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.CompatibleFamily.glue` for the composites with the
inclusion, read back in the subcategory. -/
def glueFullSubcategory (f : CompatibleFamily (G ⋙ P.ι) (H ⋙ P.ι) U) (hU : IsOpenCover U) :
    G ⟶ H where
  app A := ObjectProperty.homMk ((f.glue hU).app A)
  naturality A B φ := ObjectProperty.hom_ext _ (by simpa using (f.glue hU).naturality φ)

/-- Composing the glued transformation with the inclusion of the full subcategory gives the
transformation glued from the family. -/
@[simp]
theorem whiskerRight_glueFullSubcategory (f : CompatibleFamily (G ⋙ P.ι) (H ⋙ P.ι) U)
    (hU : IsOpenCover U) :
    Functor.whiskerRight (glueFullSubcategory f hU) P.ι = f.glue hU :=
  rfl

/-- The glued transformation restricts, over each member of the cover, to the corresponding
member of the family. -/
theorem ofNatTrans_glueFullSubcategory (f : CompatibleFamily (G ⋙ P.ι) (H ⋙ P.ι) U)
    (hU : IsOpenCover U) (i : ι) :
    LocalNatTrans.ofNatTrans (Functor.whiskerRight (glueFullSubcategory f hU) P.ι) (U i) =
      f.trans i :=
  f.ofNatTrans_glue hU i

/-- **Natural transformations of functors into a full subcategory of `Y.Modules` glue over an
open cover.** A compatible family of local natural transformations between `G ⋙ P.ι` and
`H ⋙ P.ι` comes from exactly one natural transformation `G ⟶ H`. -/
theorem existsUnique_natTrans_of_fullSubcategory
    (f : CompatibleFamily (G ⋙ P.ι) (H ⋙ P.ι) U) (hU : IsOpenCover U) :
    ∃! α : G ⟶ H, ∀ i : ι,
      LocalNatTrans.ofNatTrans (Functor.whiskerRight α P.ι) (U i) = f.trans i := by
  refine ⟨glueFullSubcategory f hU, ofNatTrans_glueFullSubcategory f hU, fun α hα => ?_⟩
  have hw : Functor.whiskerRight α P.ι = f.glue hU :=
    (f.existsUnique_natTrans hU).unique hα (f.ofNatTrans_glue hU)
  exact ((Functor.whiskeringRight C _ _).obj P.ι).map_injective hw

/-- **The glued transformation of functors into a full subcategory is an isomorphism when the
family is.** -/
theorem isIso_glueFullSubcategory (f : CompatibleFamily (G ⋙ P.ι) (H ⋙ P.ι) U)
    (hU : IsOpenCover U)
    (h : ∀ (A : C) (i : ι) (V : Y.Opens) (hV : V ≤ U i), IsIso ((f.trans i).app A V hV)) :
    IsIso (glueFullSubcategory f hU) := by
  have : IsIso (((Functor.whiskeringRight C _ _).obj P.ι).map (glueFullSubcategory f hU)) :=
    f.isIso_glue hU h
  exact isIso_of_reflects_iso _ ((Functor.whiskeringRight C _ _).obj P.ι)

/-- **A natural transformation of functors into a full subcategory of `Y.Modules` is determined
by its restrictions to the members of an open cover of `Y`.** -/
theorem natTrans_ext_of_fullSubcategory (hU : IsOpenCover U) {α γ : G ⟶ H}
    (h : ∀ i : ι, LocalNatTrans.ofNatTrans (Functor.whiskerRight α P.ι) (U i) =
      LocalNatTrans.ofNatTrans (Functor.whiskerRight γ P.ι) (U i)) :
    α = γ := by
  exact ((Functor.whiskeringRight C _ _).obj P.ι).map_injective (CompatibleFamily.natTrans_ext hU h)

end FullSubcategory

/-! ### The quasi-coherent case -/

section Quasicoherent

/-- **Quasi-coherence as a property of the objects of `Y.Modules`.** Its full subcategory is,
definitionally, `(SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory`. -/
def quasicoherent (Y : Scheme.{u}) : ObjectProperty Y.Modules :=
  fun M => M.IsQuasicoherent

variable {ι : Type u} {U : ι → Y.Opens}
  {G H : C ⥤ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory}

/-- **Natural transformations of functors into the quasi-coherent modules glue over an open
cover of the target scheme.** Let `Y` be a scheme, `C` any category and
`G H : C ⥤ QCoh(𝒪_Y)`. A compatible family of natural transformations `G ⟶ H` over the members of
an open cover of `Y` comes from exactly one natural transformation `G ⟶ H`. -/
theorem existsUnique_natTrans_quasicoherent
    (f : CompatibleFamily (G ⋙ (quasicoherent Y).ι) (H ⋙ (quasicoherent Y).ι) U)
    (hU : IsOpenCover U) :
    ∃! α : G ⟶ H, ∀ i : ι,
      LocalNatTrans.ofNatTrans (Functor.whiskerRight α (quasicoherent Y).ι) (U i) = f.trans i :=
  existsUnique_natTrans_of_fullSubcategory f hU

/-- **The transformation glued from a compatible family of natural transformations of
`QCoh(𝒪_Y)`-valued functors is an isomorphism when the family is.** -/
theorem isIso_glueFullSubcategory_quasicoherent
    (f : CompatibleFamily (G ⋙ (quasicoherent Y).ι) (H ⋙ (quasicoherent Y).ι) U)
    (hU : IsOpenCover U)
    (h : ∀ (A : C) (i : ι) (V : Y.Opens) (hV : V ≤ U i), IsIso ((f.trans i).app A V hV)) :
    IsIso (glueFullSubcategory f hU) :=
  isIso_glueFullSubcategory f hU h

/-- **A natural transformation of `QCoh(𝒪_Y)`-valued functors is determined by its restrictions
to the members of an open cover of `Y`.** -/
theorem natTrans_ext_quasicoherent (hU : IsOpenCover U) {α γ : G ⟶ H}
    (h : ∀ i : ι, LocalNatTrans.ofNatTrans (Functor.whiskerRight α (quasicoherent Y).ι) (U i) =
      LocalNatTrans.ofNatTrans (Functor.whiskerRight γ (quasicoherent Y).ι) (U i)) :
    α = γ :=
  natTrans_ext_of_fullSubcategory hU h

end Quasicoherent

end Stacks.AlgebraicGeometry.ModuleNatTransGlue

end
