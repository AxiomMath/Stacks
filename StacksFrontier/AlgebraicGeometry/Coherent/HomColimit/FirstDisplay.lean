module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimitSheafHom

/-!
# The canonical map `colim_n Hom(Iⁿ G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals on `X`, let `U` be the
complement of the closed subscheme it cuts out, and let `G` and `F` be `𝒪_X`-modules.  This file
constructs the map

`colim_n Hom_{𝒪_X}(Iⁿ G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`

that the first display of [Stacks, Tag 01YB] asserts to be bijective, and identifies it on
sections.

The subsheaf `Iⁿ G` of `G` is `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple`, which is
defined for an arbitrary sheaf of modules `G`; `idealPowSmul` names it as an object of
`X.Modules`, exactly as `idealPow` names the case `G = 𝒪_X`.  The inclusions `I^m G ⟶ Iⁿ G` for
`n ≤ m` assemble `n ↦ Hom_{𝒪_X}(Iⁿ G, F)` into a direct system `idealPowSmulHomSystem` over
`ℕ`, which for `G = 𝒪_X` is the system `idealPowHomSystem` of Tag 01PQ.

The map out of the colimit comes from the fact that `Iⁿ G` and `G` agree over any open disjoint
from the support of `I`, where the unit ideal already generates: the inclusion
`(Iⁿ G)|_U ⟶ G|_U` has `Subtype.val` on an affine open as its only component, and that is a
bijection because the submodule of sections is the whole module there.  So the inclusion is an
isomorphism, and a morphism `φ : Iⁿ G ⟶ F` restricts to a morphism `G|_U ⟶ F|_U`.

## Main definitions

* `idealPowSmul`: the subsheaf `Iⁿ G` of `G`, as an object of `X.Modules`.
* `idealPowSmulHomSystem`: the direct system `n ↦ Hom_{𝒪_X}(Iⁿ G, F)`, the transition maps
  being precomposition with the inclusions `I^m G ⟶ Iⁿ G`.
* `idealPowSmulOverIso`: the isomorphism `(Iⁿ G)|_U ≅ G|_U` over an open `U` disjoint from the
  support of `I`.
* `homRestrict`: the morphism `G|_U ⟶ F|_U` attached to a morphism `Iⁿ G ⟶ F`.
* `canonicalMapToHomRestrict`: the map `colim_n Hom_{𝒪_X}(Iⁿ G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`,
  which is the arrow of the first display of [Stacks, Tag 01YB].

## Main results

* `val_homRestrict_app`: `homRestrict` reads on sections as `g ↦ φ(g)`, the section `g` of `G`
  over an open contained in `U` being viewed as a section of `Iⁿ G` there.  This pins the
  canonical map down; without it the definition would not be identified.
* `smul_mem_idealPowerMultiple`: a section of `Iⁿ` times a section of `G` is a section of
  `Iⁿ G`.
* `bijective_sectionsSheafHomModulesEquiv_canonicalMapToSections`, in the namespace
  `Stacks.AlgebraicGeometry.InternalHomModules`:
  the global-sections clause of [Stacks, Tag 01YB] applied to `SheafHom_{𝒪_X}(G, F)`, with its
  target read as `Hom_{𝒪_U}(G|_U, F|_U)`.  For `G` of finite presentation and `F` quasi-coherent
  on a Noetherian scheme this is a bijection

  `colim_n Hom_{𝒪_X}(Iⁿ, SheafHom_{𝒪_X}(G, F)) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`

  onto the same target as `canonicalMapToHomRestrict`.

## Implementation notes

**Where bijectivity of the first display is proved.**  Not here: injectivity is
`Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToHomRestrict_injective` and
bijectivity is
`Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToHomRestrict_bijective`, which carries
the clause of the tag.  Surjectivity runs the source's argument: it takes the `ψ` produced by
`bijective_sectionsSheafHomModulesEquiv_canonicalMapToSections` below, turns it into a morphism
`Iⁿ ⊗_{𝒪_X} G ⟶ F` by `Stacks.AlgebraicGeometry.InternalHomModules.tensorHomToModule`, and
transports that across the surjection `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`, whose kernel `𝒦` satisfies
`Iⁿ 𝒦 = 0` and is therefore killed by a second application of Artin-Rees.  Those three steps are
`Stacks.AlgebraicGeometry.IdealPowerColimit.epi_idealPowTensorToSmul`,
`Stacks.AlgebraicGeometry.IdealPowerColimit.smul_eq_zero_of_idealPowTensorToSmul_eq_zero` — of
which `smul_mem_idealPowerMultiple` is the first step — and
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_isIso_idealPowSmulTensorToSmul`.

**Isomorphy of the restricted inclusion is checked componentwise.**
`SheafOfModules.forget ⋙ PresheafOfModules.toPresheaf` reflects isomorphisms, and the
restriction functor to the slice site over `U` is a pushforward, so the component of
`(Iⁿ G).ι.over U` at an object `V ⟶ U` of that site is the inclusion of
`(Iⁿ G)(V)` into `G(V)`, that is `Subtype.val`.

**`asIso` is applied with its witness positional.**  `Scheme.Modules` carries its own `Category`
instance whose `Hom` is only definitionally that of `SheafOfModules`, so instance resolution
does not find an `IsIso` hypothesis that is in scope; passing the witness by position forces
unification from its type.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower

noncomputable section

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### `Iⁿ G` and its filtration -/

/-- `Iⁿ G`, the subsheaf `I ^ n • G` of `G`, as a sheaf of modules on `X`.

The ascription to `X.Modules` matters: `Scheme.Modules` is a `def`, so without it the morphisms
out of this object are elaborated in `SheafOfModules` and the `X.Modules` API is unavailable.
For `G = 𝒪_X` this is `idealPow`. -/
public noncomputable abbrev idealPowSmul (I : X.IdealSheafData) (n : ℕ) (G : X.Modules) :
    X.Modules :=
  subMod (idealPowerMultiple I n G)

/-- The inclusion `I^m G ⟶ Iⁿ G` for `n ≤ m`. -/
public noncomputable abbrev idealPowSmulMap (I : X.IdealSheafData) (G : X.Modules) {n m : ℕ}
    (h : n ≤ m) : idealPowSmul I m G ⟶ idealPowSmul I n G :=
  idealPowerMultipleMap I G h

/-- The inclusion of `Iⁿ G` into itself is the identity. -/
public theorem idealPowSmulMap_refl (I : X.IdealSheafData) (G : X.Modules) (n : ℕ) :
    idealPowSmulMap I G (le_refl n) = 𝟙 (idealPowSmul I n G) :=
  subInclusion_refl _

/-- The inclusions of the filtration `n ↦ Iⁿ G` compose. -/
public theorem idealPowSmulMap_comp (I : X.IdealSheafData) (G : X.Modules) {n m k : ℕ}
    (h : n ≤ m) (h' : m ≤ k) :
    idealPowSmulMap I G h' ≫ idealPowSmulMap I G h = idealPowSmulMap I G (h.trans h') :=
  idealPowerMultipleMap_comp I G h h'

/-- **A section of `Iⁿ` times a section of `G` is a section of `Iⁿ G`.**

Membership in a subsheaf is local on the affine opens, and on an affine open `V'` the section of
`Iⁿ` restricts into `I(V')ⁿ` while `I(V')ⁿ • G(V')` is contained in `(Iⁿ G)(V')` by the defining
lower bound of `Iⁿ G`. -/
public theorem smul_mem_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    {V : X.Opens} (a : Γ(X, V))
    (ha : a ∈ (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op V))
    (g : Γ(G, V)) :
    a • g ∈ (idealPowerMultiple I n G).toSubmodule.obj (op V) := by
  refine mem_of_forall_affineOpens _ (a • g) fun V' hV' ↦ ?_
  rw [Scheme.Modules.map_smul]
  have ha' : X.presheaf.map (homOfLE hV').op a ∈ (I.ideal V' ^ n : Ideal Γ(X, V'.1)) := by
    rw [← obj_idealPow_affineOpen I n V']
    exact (idealPowerMultiple I n (structureModule X)).toSubmodule.map_mem (homOfLE hV').op ha
  exact le_idealPowerMultiple_obj I n G V' (Submodule.smul_mem_smul ha' Submodule.mem_top)

/-! ### The direct system `n ↦ Hom_{𝒪_X}(Iⁿ G, F)` -/

/-- The direct system `n ↦ Hom_{𝒪_X}(Iⁿ G, F)`, the transition maps being precomposition with
the inclusions `I^m G ⟶ Iⁿ G`.

For `G = 𝒪_X` this is the system `idealPowHomSystem` whose colimit Tag 01PQ compares with the
sections of `F` over the complement of the support of `I`. -/
public noncomputable def idealPowSmulHomSystem (I : X.IdealSheafData) (G F : X.Modules) :
    ℕ ⥤ AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (idealPowSmul I n G ⟶ F)
  map {m n} h := AddCommGrpCat.ofHom (Preadditive.leftComp F (idealPowSmulMap I G (leOfHom h)))
  map_id n := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦ by
    change idealPowSmulMap I G (le_refl n) ≫ φ = φ
    rw [idealPowSmulMap_refl, Category.id_comp])
  map_comp {k m n} h h' := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦ by
    change idealPowSmulMap I G (leOfHom (h ≫ h')) ≫ φ
      = idealPowSmulMap I G (leOfHom h') ≫ (idealPowSmulMap I G (leOfHom h) ≫ φ)
    rw [← Category.assoc, idealPowSmulMap_comp])

/-- A transition map of the system `n ↦ Hom_{𝒪_X}(Iⁿ G, F)` is precomposition with an inclusion
of the filtration. -/
@[simp] public theorem idealPowSmulHomSystem_map (I : X.IdealSheafData) (G F : X.Modules)
    {m n : ℕ} (h : m ⟶ n) (φ : idealPowSmul I m G ⟶ F) :
    (idealPowSmulHomSystem I G F).map h φ = idealPowSmulMap I G (leOfHom h) ≫ φ := rfl

/-! ### `Iⁿ G` and `G` agree away from the support of `I` -/

/-- Over an open disjoint from the support of `I` the inclusion of `Iⁿ G` into `G` is bijective
on sections, because the submodule of sections is the whole module there. -/
public theorem bijective_val_idealPowerMultiple_of_disjoint (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X))
    {V : X.Opens} (hV : V ≤ U) :
    Function.Bijective (Subtype.val :
      ((idealPowerMultiple I n G).toSubmodule.obj (op V)) → Γ(G, V)) := by
  have htop := idealPowerMultiple_obj_eq_top_of_disjoint_support I n G hU hV
  refine ⟨Subtype.val_injective, fun s ↦ ?_⟩
  exact ⟨⟨s, htop ▸ Submodule.mem_top⟩, rfl⟩

/-- Each component of the restriction to `U` of the inclusion `Iⁿ G ⟶ G` is an isomorphism.

The restriction functor to the slice site over `U` is a pushforward, so the component at an
object `V ⟶ U` of that site is the inclusion of `(Iⁿ G)(V)` into `G(V)`. -/
public theorem isIso_idealPowerMultiple_ι_over_app (I : X.IdealSheafData) (n : ℕ)
    (G : X.Modules) {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X))
    (V : (Over U)ᵒᵖ) :
    IsIso (((SheafOfModules.forget (Sheaf.over X.ringCatSheaf U) ⋙
      PresheafOfModules.toPresheaf _).map
        ((idealPowerMultiple I n G).ι.over U)).app V) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_val_idealPowerMultiple_of_disjoint I n G hU (leOfHom V.unop.hom)

/-- The restriction to `U` of the inclusion `Iⁿ G ⟶ G` is an isomorphism, for `U` disjoint from
the support of `I`.

`SheafOfModules.forget ⋙ PresheafOfModules.toPresheaf` reflects isomorphisms, so it is enough
that every component is one. -/
public theorem isIso_idealPowerMultiple_ι_over (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X)) :
    IsIso ((idealPowerMultiple I n G).ι.over U) := by
  have := isIso_idealPowerMultiple_ι_over_app I n G hU
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (SheafOfModules.forget (Sheaf.over X.ringCatSheaf U) ⋙
    PresheafOfModules.toPresheaf _) (NatIso.isIso_of_isIso_app _) _

/-- **`(Iⁿ G)|_U ≅ G|_U`** for `U` an open disjoint from the support of `I`: away from the
closed subscheme cut out by `I` the unit ideal already generates, so `Iⁿ G` is all of `G`
there. -/
public noncomputable def idealPowSmulOverIso (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X)) :
    (idealPowSmul I n G).over U ≅ G.over U :=
  @asIso _ _ _ _ ((idealPowerMultiple I n G).ι.over U)
    (isIso_idealPowerMultiple_ι_over I n G hU)

/-- The isomorphism `(Iⁿ G)|_U ≅ G|_U` is the restriction of the inclusion of `Iⁿ G` into `G`. -/
@[simp] public theorem idealPowSmulOverIso_hom (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X)) :
    (idealPowSmulOverIso I n G hU).hom = (idealPowerMultiple I n G).ι.over U := rfl

/-- The isomorphisms `(Iⁿ G)|_U ≅ G|_U` are compatible with the inclusions of the filtration. -/
public theorem idealPowSmulMap_over_comp_hom (I : X.IdealSheafData) (G : X.Modules) {n m : ℕ}
    (h : n ≤ m) {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X)) :
    (idealPowSmulMap I G h).over U ≫ (idealPowSmulOverIso I n G hU).hom =
      (idealPowSmulOverIso I m G hU).hom :=
  ((SheafOfModules.overFunctor _ U).map_comp _ _).symm.trans
    (congrArg ((SheafOfModules.overFunctor _ U).map) (idealPowerMultipleMap_comp_ι I G h))

/-- The inverses of the isomorphisms `(Iⁿ G)|_U ≅ G|_U` are compatible with the inclusions of
the filtration. -/
public theorem inv_comp_idealPowSmulMap_over (I : X.IdealSheafData) (G : X.Modules) {n m : ℕ}
    (h : n ≤ m) {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X)) :
    (idealPowSmulOverIso I m G hU).inv ≫ (idealPowSmulMap I G h).over U =
      (idealPowSmulOverIso I n G hU).inv := by
  have hf : (idealPowSmulMap I G h).over U
      = (idealPowSmulOverIso I m G hU).hom ≫ (idealPowSmulOverIso I n G hU).inv :=
    (Iso.eq_comp_inv _).mpr (idealPowSmulMap_over_comp_hom I G h hU)
  rw [hf, Iso.inv_hom_id_assoc]

/-! ### The canonical map of the first display -/

/-- The morphism `G|_U ⟶ F|_U` attached to a morphism `φ : Iⁿ G ⟶ F`: the inverse of
`(Iⁿ G)|_U ≅ G|_U` followed by the restriction of `φ`. -/
public noncomputable def homRestrict (I : X.IdealSheafData) {G F : X.Modules} {U : X.Opens}
    (hU : Disjoint (U : Set X) (I.support : Set X)) {n : ℕ} (φ : idealPowSmul I n G ⟶ F) :
    G.over U ⟶ F.over U :=
  (idealPowSmulOverIso I n G hU).inv ≫ φ.over U

/-- A section of `G` over an open contained in `U` is a section of `Iⁿ G` there. -/
public theorem mem_idealPowerMultiple_of_le (I : X.IdealSheafData) (n : ℕ) (G : X.Modules)
    {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X)) {V : X.Opens} (hV : V ≤ U)
    (g : Γ(G, V)) :
    g ∈ (idealPowerMultiple I n G).toSubmodule.obj (op V) :=
  (idealPowerMultiple_obj_eq_top_of_disjoint_support I n G hU hV).ge Submodule.mem_top

/-- The inverse of `(Iⁿ G)|_U ≅ G|_U` does not change the value of a section: it is the map
viewing a section of `G` over an open contained in `U` as a section of `Iⁿ G`. -/
public theorem coe_idealPowSmulOverIso_inv_val_app (I : X.IdealSheafData) {n : ℕ}
    {G : X.Modules} {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X))
    (V : (Over U)ᵒᵖ) (g : Γ(G, V.unop.left)) :
    ((((idealPowSmulOverIso I n G hU).inv.val.app V).hom g).val : Γ(G, V.unop.left)) = g :=
  congrArg (fun f : (G.over U) ⟶ (G.over U) => (f.val.app V).hom g)
    ((idealPowSmulOverIso I n G hU).inv_hom_id)

/-- **The canonical map of the first display, read on sections.**  For an open `V ⟶ U` of the
slice site over `U`, the morphism `homRestrict I hU φ : G|_U ⟶ F|_U` sends a section `g` of `G`
over `V` to `φ(g)`, the section `g` being viewed as a section of `Iⁿ G` over `V`.

This identifies `homRestrict`, and hence `canonicalMapToHomRestrict`.  Without it the
definition would be unpinned, since `homRestrict` is built from the inverse of an isomorphism
obtained from `asIso`. -/
public theorem val_homRestrict_app (I : X.IdealSheafData) {n : ℕ} {G F : X.Modules}
    {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X))
    (φ : idealPowSmul I n G ⟶ F) (V : (Over U)ᵒᵖ) (g : Γ(G, V.unop.left)) :
    ((homRestrict I hU φ).val.app V).hom g
      = φ.app V.unop.left ⟨g, mem_idealPowerMultiple_of_le I n G hU (leOfHom V.unop.hom) g⟩ := by
  change φ.app V.unop.left (((idealPowSmulOverIso I n G hU).inv.val.app V).hom g) = _
  exact congrArg (φ.app V.unop.left)
    (Subtype.ext (coe_idealPowSmulOverIso_inv_val_app I hU V g))

/-- Restricting a morphism out of `Iⁿ G` to `U` is additive. -/
public theorem homRestrict_add (I : X.IdealSheafData) {G F : X.Modules} {U : X.Opens}
    (hU : Disjoint (U : Set X) (I.support : Set X)) {n : ℕ}
    (φ ψ : idealPowSmul I n G ⟶ F) :
    homRestrict I hU (φ + ψ) = homRestrict I hU φ + homRestrict I hU ψ := by
  change (idealPowSmulOverIso I n G hU).inv ≫ (φ.over U + ψ.over U) = _
  rw [Preadditive.comp_add]
  rfl

/-- Precomposing with an inclusion `I^m G ⟶ Iⁿ G` does not change the restriction to `U`, so
`homRestrict` is a cocone on the system `n ↦ Hom_{𝒪_X}(Iⁿ G, F)`. -/
public theorem homRestrict_idealPowSmulMap (I : X.IdealSheafData) {G F : X.Modules}
    {U : X.Opens} (hU : Disjoint (U : Set X) (I.support : Set X)) {n m : ℕ} (h : n ≤ m)
    (φ : idealPowSmul I n G ⟶ F) :
    homRestrict I hU (idealPowSmulMap I G h ≫ φ) = homRestrict I hU φ := by
  have hmc : (idealPowSmulMap I G h ≫ φ).over U
      = (idealPowSmulMap I G h).over U ≫ φ.over U :=
    (SheafOfModules.overFunctor _ U).map_comp _ _
  rw [homRestrict, homRestrict, hmc, ← Category.assoc,
    inv_comp_idealPowSmulMap_over I G h hU]

/-- The complement of the support of `I` is disjoint from that support. -/
public theorem disjoint_supportCompl_support (I : X.IdealSheafData) :
    Disjoint ((I.support.compl : X.Opens) : Set X) (I.support : Set X) :=
  disjoint_compl_left

/-- The cocone on `n ↦ Hom_{𝒪_X}(Iⁿ G, F)` whose leg at `n` restricts a morphism
`Iⁿ G ⟶ F` to a morphism `G|_U ⟶ F|_U`, where `U = X \ V(I)`. -/
public noncomputable def homRestrictCocone (I : X.IdealSheafData) (G F : X.Modules) :
    Limits.Cocone (idealPowSmulHomSystem I G F) where
  pt := AddCommGrpCat.of
    (G.over (I.support.compl : X.Opens) ⟶ F.over (I.support.compl : X.Opens))
  ι :=
    { app := fun n ↦ AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun φ : idealPowSmul I n G ⟶ F ↦
            homRestrict I (disjoint_supportCompl_support I) φ)
          (homRestrict_add I (disjoint_supportCompl_support I)))
      naturality := fun {m n} h ↦ by
        simp only [Functor.const_obj_map]
        exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦
          homRestrict_idealPowSmulMap I (disjoint_supportCompl_support I) (leOfHom h) φ) }

/-- **The arrow of the first display of [Stacks, Tag 01YB].**  For a scheme `X`, a
quasi-coherent sheaf of ideals `I` with complement `U = X \ V(I)` and `𝒪_X`-modules `G` and `F`,
the canonical map

`colim_n Hom_{𝒪_X}(Iⁿ G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`.

It is the map `val_homRestrict_app` identifies: a morphism `φ : Iⁿ G ⟶ F` goes to the morphism
sending a section `g` of `G` over an open contained in `U` to `φ(g)`.  The tag asserts that it
is bijective when `X` is Noetherian, `G` is coherent and `F` is quasi-coherent; that is
`Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToHomRestrict_bijective`. -/
public noncomputable def canonicalMapToHomRestrict (I : X.IdealSheafData) (G F : X.Modules) :
    Limits.colimit (idealPowSmulHomSystem I G F) ⟶
      AddCommGrpCat.of
        (G.over (I.support.compl : X.Opens) ⟶ F.over (I.support.compl : X.Opens)) :=
  Limits.colimit.desc _ (homRestrictCocone I G F)

/-- The canonical map of the first display, on the image of the `n`-th leg of the colimit. -/
public theorem canonicalMapToHomRestrict_ι (I : X.IdealSheafData) (G F : X.Modules) (n : ℕ)
    (φ : idealPowSmul I n G ⟶ F) :
    canonicalMapToHomRestrict I G F
        (Limits.colimit.ι (idealPowSmulHomSystem I G F) n φ)
      = homRestrict I (disjoint_supportCompl_support I) φ :=
  congr($(Limits.colimit.ι_desc (homRestrictCocone I G F) n) φ)

end Stacks.AlgebraicGeometry.IdealPowerColimit

namespace Stacks.AlgebraicGeometry.InternalHomModules

open Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-- **The global-sections clause of [Stacks, Tag 01YB] applied to a sheaf Hom, with its target
read as a module of morphisms.**  For `G` of finite presentation and `F` quasi-coherent on a
Noetherian scheme, the canonical map

`colim_n Hom_{𝒪_X}(Iⁿ, SheafHom_{𝒪_X}(G, F)) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`

is a bijection: `SheafHom_{𝒪_X}(G, F)` is quasi-coherent, so the global-sections clause applies
to it, and its sections over `U` are by definition the morphisms `G|_U ⟶ F|_U`.

This is the opening step of the source's proof of the first display of Tag 01YB: its target is
that of `canonicalMapToHomRestrict`, so surjectivity of the first display follows once the `ψ`
it produces is transported across the surjection `Iⁿ ⊗_{𝒪_X} G ⟶ Iⁿ G`. -/
public theorem bijective_sectionsSheafHomModulesEquiv_canonicalMapToSections
    [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData) (G F : X.Modules)
    (hG : G.IsFinitePresentation) [F.IsQuasicoherent] :
    Function.Bijective
      (sectionsSheafHomModulesEquiv G F (I.support.compl : X.Opens) ∘
        canonicalMapToSections I (sheafHomModules G F)) :=
  (sectionsSheafHomModulesEquiv G F (I.support.compl : X.Opens)).bijective.comp
    (canonicalMapToSections_sheafHomModules_bijective I G F hG)

end Stacks.AlgebraicGeometry.InternalHomModules

end

end
