module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Order.CompletePartialOrder
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Building an `f`-map of sheaves of modules from data on bases (Stacks 009Y)

Let `(f, f^♯) : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, `F` a sheaf of
`𝒪_X`-modules and `G` a sheaf of `𝒪_Y`-modules. An `f`-map `G → F` is a family of additive
maps `ψ_V : G(V) → F(f⁻¹ V)`, one for each open `V ⊆ Y`, that is semilinear over `f^♯` and
commutes with restriction; this is `FMapAddGroupHom`.

Such a family is determined by, and can be reconstructed from, its values on *bases*. Given
bases `B_X` of `X` and `B_Y` of `Y` together with additive maps `φ_V^U : G(V) → F(U)` for
every `V ∈ B_Y` and every `U ∈ B_X` with `U ≤ f⁻¹ V`, semilinear over `f^♯` composed with
restriction and compatible with shrinking `U` and `V` simultaneously — the bundle of that
data is `BasisCompat` — there is a unique `f`-map `ψ` recovering each `φ_V^U` as the composite
`G(V) → F(f⁻¹ V) → F(U)`. That is `existsUnique_fMap_of_bases`.

The construction is by gluing. For an arbitrary open `V ⊆ Y`, the opens `U ∈ B_X` that fit
inside `f⁻¹ V'` for some `V' ∈ B_Y` with `V' ≤ V` cover `f⁻¹ V` (`cover_iSup_eq`), the
sections `φ_{V'}^U(g|_{V'})` agree on overlaps (`cover_sections_compatible`, which reduces
to `basisApp_agreement` after refining an intersection twice), and the sheaf condition on
`F` glues them to a single section `ψ_V(g)` (`constructApp`). Additivity, semilinearity and
naturality of `ψ` all follow from uniqueness of the gluing, and uniqueness of `ψ` itself
from the separation lemma `SheafOfModulesOnRingedSpace.section_ext_cover`.

A sheaf of modules on a ringed space is modelled here by `SheafOfModulesOnRingedSpace`: a
`PresheafOfModules` over the `RingCat`-valued structure sheaf (`structureSheafRingCat`,
the `CommRingCat`-valued one postcomposed with `forget₂ CommRingCat RingCat`, as the
`PresheafOfModules` API requires) together with the topological sheaf condition on its
underlying presheaf of abelian groups. Mathlib's `CategoryTheory.SheafOfModules` is stated
over a site; the argument here is run entirely through `TopCat.Presheaf.IsSheafUniqueGluing`,
so the sheaf condition is kept in that topological form.

Everything is stated for `RingedSpace.{v, u}`: the structure sheaf may take values in
`CommRingCat.{v}` for an arbitrary `v`, but the underlying space must live in `Type u` with
the modules in `PresheafOfModules.{u}`, that is, in the same universe. Tying those two is
forced rather than chosen: the gluing argument goes through
`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`, whose hypothesis
`HasLimitsOfSize.{u, u} AddCommGrpCat.{w}` for a space in `Type u` holds only for `w = u`
among the instances available, so an independent module universe `w` cannot be used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.RingedSpace

universe v u

/- The sheaf condition below is stated for the underlying presheaf of abelian groups
`PresheafOfModules.presheaf`, while sections are handled as modules, so the two spellings of a
section type have to be interchangeable for `rw`, `change` and `congr`. Since Lean 4.34 the
`implicit` transparency level used by `isDefEq` unfolds only `@[reducible]`,
`@[instance_reducible]` and `@[implicit_reducible]` definitions, so the semireducible
`PresheafOfModules.presheaf` is marked reducible at that level throughout this file. -/
attribute [local implicit_reducible] PresheafOfModules.presheaf

/-- The structure sheaf of a ringed space as a presheaf of (not necessarily commutative)
rings, obtained by postcomposing with `forget₂ CommRingCat RingCat`. This is the form the
`PresheafOfModules` API takes as its base ring object. -/
noncomputable abbrev structureSheafRingCat (X : RingedSpace.{v, u}) :
    (Opens X.carrier)ᵒᵖ ⥤ RingCat.{v} :=
  X.presheaf ⋙ forget₂ CommRingCat RingCat

/-- A sheaf of `𝒪_X`-modules on a ringed space `X`: a presheaf of modules over the structure
sheaf whose underlying presheaf of abelian groups satisfies the sheaf condition. -/
structure SheafOfModulesOnRingedSpace (X : RingedSpace.{v, u}) where
  /-- The underlying presheaf of `𝒪_X`-modules. -/
  toPresheaf : PresheafOfModules.{u} (structureSheafRingCat X)
  /-- The sheaf condition on the underlying presheaf of abelian groups. -/
  isSheaf : TopCat.Presheaf.IsSheaf toPresheaf.presheaf

namespace SheafOfModulesOnRingedSpace
variable {X : RingedSpace.{v, u}}

/-- The `𝒪_X(U)`-module of sections of `M` over an open `U`. -/
noncomputable abbrev sections (M : SheafOfModulesOnRingedSpace X) (U : Opens X.carrier) :
    ModuleCat (X.presheaf.obj (op U)) := M.toPresheaf.obj (op U)

/-- Restriction of sections of `M` along an inclusion `V ≤ U` of opens, as a map of additive
groups. -/
noncomputable abbrev restrict (M : SheafOfModulesOnRingedSpace X)
    {U V : Opens X.carrier} (h : V ≤ U) : M.sections U →+ M.sections V :=
  ((M.toPresheaf.map (homOfLE h).op).hom).toAddMonoidHom

/-- The restriction map `M.restrict h` agrees with the restriction map of the underlying
presheaf of abelian groups. -/
lemma restrict_apply (M : SheafOfModulesOnRingedSpace X) {U V : Opens X.carrier} (h : V ≤ U)
    (x : M.sections U) : M.restrict h x = M.toPresheaf.presheaf.map (homOfLE h).op x :=
  rfl

/-- Restriction along the identity inclusion `U ≤ U` is the identity. -/
@[simp]
lemma restrict_self (M : SheafOfModulesOnRingedSpace X) {U : Opens X.carrier} (h : U ≤ U)
    (x : M.sections U) : M.restrict h x = x := by
  rw [restrict_apply, show homOfLE h = 𝟙 U from Subsingleton.elim _ _, op_id,
    M.toPresheaf.presheaf.map_id, CategoryTheory.id_apply]

/-- Restricting from `U` to `V` and then from `V` to `W` is restriction from `U` to `W`. -/
@[simp]
lemma restrict_restrict (M : SheafOfModulesOnRingedSpace X) {U V W : Opens X.carrier}
    (h₁ : V ≤ U) (h₂ : W ≤ V) (x : M.sections U) :
    M.restrict h₂ (M.restrict h₁ x) = M.restrict (h₂.trans h₁) x := by
  rw [restrict_apply, restrict_apply, restrict_apply, ← CategoryTheory.comp_apply,
    ← M.toPresheaf.presheaf.map_comp]
  rfl

/-- Two sections of a sheaf of modules over `W` agree if they agree on a family covering `W`. -/
private lemma section_ext_of_cover (M : SheafOfModulesOnRingedSpace X)
    {W : Opens X.carrier} {ι : Type u} (U_cover : ι → Opens X.carrier)
    (hle : ∀ i, U_cover i ≤ W) (hcover : W ≤ iSup U_cover)
    (s t : M.sections W)
    (h : ∀ i, M.restrict (hle i) s = M.restrict (hle i) t) : s = t := by
  have hSheaf := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    M.toPresheaf.presheaf).mp M.isSheaf
  have hW_eq : iSup U_cover = W := le_antisymm (iSup_le hle) hcover
  let sf : (i : ι) → M.toPresheaf.presheaf.obj (op (U_cover i)) :=
    fun i => M.toPresheaf.presheaf.map (homOfLE (hle i)).op s
  have hcompat : TopCat.Presheaf.IsCompatible M.toPresheaf.presheaf U_cover sf := by
    intro i j
    simp only [sf]
    rw [← CategoryTheory.comp_apply
          (M.toPresheaf.presheaf.map (homOfLE (hle i)).op)
          (M.toPresheaf.presheaf.map (Opens.infLELeft _ _).op),
        ← CategoryTheory.comp_apply
          (M.toPresheaf.presheaf.map (homOfLE (hle j)).op)
          (M.toPresheaf.presheaf.map (Opens.infLERight _ _).op),
        ← M.toPresheaf.presheaf.map_comp, ← M.toPresheaf.presheaf.map_comp]
    congr 1
  obtain ⟨_, _, hglued_unique⟩ := hSheaf U_cover sf hcompat
  let s' : M.toPresheaf.presheaf.obj (op (iSup U_cover)) :=
    M.toPresheaf.presheaf.map (eqToHom (by rw [hW_eq] : op W = op (iSup U_cover))) s
  let t' : M.toPresheaf.presheaf.obj (op (iSup U_cover)) :=
    M.toPresheaf.presheaf.map (eqToHom (by rw [hW_eq] : op W = op (iSup U_cover))) t
  have hs'_gluing : TopCat.Presheaf.IsGluing M.toPresheaf.presheaf U_cover sf s' := by
    intro i
    simp only [s', sf]
    rw [← CategoryTheory.comp_apply
          (M.toPresheaf.presheaf.map (eqToHom _))
          (M.toPresheaf.presheaf.map (Opens.leSupr U_cover i).op),
        ← M.toPresheaf.presheaf.map_comp]
    congr 1
  have ht'_gluing : TopCat.Presheaf.IsGluing M.toPresheaf.presheaf U_cover sf t' := by
    intro i
    simp only [t', sf]
    rw [← CategoryTheory.comp_apply
          (M.toPresheaf.presheaf.map (eqToHom _))
          (M.toPresheaf.presheaf.map (Opens.leSupr U_cover i).op),
        ← M.toPresheaf.presheaf.map_comp,
        show eqToHom _ ≫ (Opens.leSupr U_cover i).op = (homOfLE (hle i)).op
          from Subsingleton.elim _ _]
    exact (h i).symm
  have hs't' : s' = t' := (hglued_unique s' hs'_gluing).trans (hglued_unique t' ht'_gluing).symm
  have hinj :
      Function.Injective (ConcreteCategory.hom (M.toPresheaf.presheaf.map
        (eqToHom (by rw [hW_eq] : op W = op (iSup U_cover))))) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  exact hinj hs't'

/-- Two sections of a sheaf of modules over an open `W` agree as soon as they agree after
restriction to every basis open contained in `W`. -/
lemma section_ext (M : SheafOfModulesOnRingedSpace X)
    {W : Opens X.carrier} (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B)
    (s t : M.sections W)
    (h : ∀ (U : Opens X.carrier) (_ : U ∈ B) (hUW : U ≤ W),
      M.restrict hUW s = M.restrict hUW t) : s = t := by
  have hSheaf := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    M.toPresheaf.presheaf).mp M.isSheaf
  refine section_ext_of_cover M (ι := { U : Opens X.carrier // U ∈ B ∧ U ≤ W }) (fun i => i.val)
    (fun i => i.prop.2) ?_ s t fun i => h i.val i.prop.1 i.prop.2
  intro x hx
  rw [Opens.mem_iSup]
  obtain ⟨_, ⟨U, hU_B, rfl⟩, hx_U, hU_W⟩ := hB.mem_nhds_iff.mp (W.2.mem_nhds hx)
  exact ⟨⟨U, hU_B, hU_W⟩, hx_U⟩

/-- Two sections of a sheaf of modules over an open `W` agree as soon as they agree after
restriction to every member of a family of opens covering `W`. Unlike `section_ext` the
family need not consist of basis opens. -/
lemma section_ext_cover (M : SheafOfModulesOnRingedSpace X)
    {W : Opens X.carrier} {ι : Type u} (U_cover : ι → Opens X.carrier)
    (hle : ∀ i, U_cover i ≤ W) (hcover : W ≤ iSup U_cover)
    (s t : M.sections W)
    (h : ∀ i, M.restrict (hle i) s = M.restrict (hle i) t) : s = t :=
  section_ext_of_cover M U_cover hle hcover s t h

end SheafOfModulesOnRingedSpace

section FMapAddGroupHom
variable {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
variable (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)

/-- The component `f^♯_V : 𝒪_Y(V) ⟶ 𝒪_X(f⁻¹ V)` of the structure-sheaf map of `f`. -/
noncomputable abbrev fSharp (V : Opens Y.carrier) :
    Y.presheaf.obj (op V) ⟶ X.presheaf.obj (op ((Opens.map f.hom.base).obj V)) :=
  f.hom.c.app (op V)

/-- The component `f^♯_V` followed by restriction to an open `U ≤ f⁻¹ V`; this is the ring
map over which a map `G(V) → F(U)` is required to be semilinear. -/
noncomputable abbrev fSharpRestrict (V : Opens Y.carrier) {U : Opens X.carrier}
    (hU : U ≤ (Opens.map f.hom.base).obj V) :
    Y.presheaf.obj (op V) ⟶ X.presheaf.obj (op U) :=
  fSharp f V ≫ X.presheaf.map (homOfLE hU).op

/-- An `f`-map from `G` to `F`: additive maps `G(V) → F(f⁻¹ V)` for every open `V ⊆ Y`,
semilinear over `f^♯` and compatible with restriction. This is the notion the Stacks
Project writes as a map `G → f_* F` of sheaves of `𝒪_Y`-modules. -/
structure FMapAddGroupHom where
  /-- The additive map on sections over each open of `Y`. -/
  app : ∀ V : Opens Y.carrier, G.sections V →+ F.sections ((Opens.map f.hom.base).obj V)
  /-- Semilinearity: scalars are transported along `f^♯_V`. -/
  smul_compat : ∀ (V : Opens Y.carrier) (r : Y.presheaf.obj (op V)) (g : G.sections V),
    app V (r • g) = (fSharp f V r) • app V g
  /-- Compatibility with restriction along `V' ≤ V`. -/
  naturality : ∀ {V V' : Opens Y.carrier} (h : V' ≤ V) (g : G.sections V),
    app V' (G.restrict h g) = F.restrict ((Opens.map f.hom.base).map (homOfLE h)).le (app V g)

/-- The data an `f`-map is to be built from: additive maps `φ_V^U : G(V) → F(U)` for basis
opens `V ∈ BY` and `U ∈ BX` with `U ≤ f⁻¹ V`, semilinear over `f^♯` composed with
restriction and compatible with shrinking `U` and `V` at once. -/
structure BasisCompat (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier)) where
  /-- The map on sections attached to a pair of basis opens `U ≤ f⁻¹ V`. -/
  basisApp : ∀ {V : Opens Y.carrier} (_ : V ∈ BY)
    {U : Opens X.carrier} (_ : U ∈ BX) (_ : U ≤ (Opens.map f.hom.base).obj V),
    G.sections V →+ F.sections U
  /-- Semilinearity of `φ_V^U` over `f^♯_V` followed by restriction to `U`. -/
  basisApp_smul : ∀ {V : Opens Y.carrier} (hV : V ∈ BY)
      {U : Opens X.carrier} (hU : U ∈ BX) (hUV : U ≤ (Opens.map f.hom.base).obj V)
      (r : Y.presheaf.obj (op V)) (g : G.sections V),
    basisApp hV hU hUV (r • g) = (fSharpRestrict f V hUV r) • basisApp hV hU hUV g
  /-- Compatibility of the `φ_V^U` with shrinking both basis opens. -/
  basisApp_restrict :
    ∀ {V V' : Opens Y.carrier} (hV : V ∈ BY) (hV' : V' ∈ BY) (hVV' : V' ≤ V)
      {U U' : Opens X.carrier} (hU : U ∈ BX) (hU' : U' ∈ BX) (hUU' : U' ≤ U)
      (hUV : U ≤ (Opens.map f.hom.base).obj V) (hUV' : U' ≤ (Opens.map f.hom.base).obj V')
      (g : G.sections V),
    F.restrict hUU' (basisApp hV hU hUV g) = basisApp hV' hU' hUV' (G.restrict hVV' g)
end FMapAddGroupHom

/-! ## Gluing the maps `φ_V^U` into a single `f`-map -/

/-- Index type for the basis cover of `f⁻¹ W`: pairs `(V, U)` with `V ∈ BY`, `V ≤ W`,
`U ∈ BX` and `U ≤ f⁻¹ V`. -/
abbrev CoverIdx {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (W : Opens Y.carrier) : Type u :=
  { p : Opens Y.carrier × Opens X.carrier //
    p.1 ∈ BY ∧ p.1 ≤ W ∧ p.2 ∈ BX ∧ p.2 ≤ (Opens.map f.hom.base).obj p.1 }

/-- The covering family of `f⁻¹ W` indexed by `CoverIdx`, sending `(V, U)` to `U`. -/
abbrev coverFamily {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (W : Opens Y.carrier) : CoverIdx f BX BY W → Opens X.carrier :=
  fun i => i.val.2

/-- The basis opens indexed by `CoverIdx f BX BY W` cover `f⁻¹ W` exactly. -/
lemma cover_iSup_eq {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (W : Opens Y.carrier) :
    iSup (coverFamily f BX BY W) = (Opens.map f.hom.base).obj W := by
  refine le_antisymm (iSup_le fun i =>
    le_trans i.prop.2.2.2 ((Opens.map f.hom.base).monotone (homOfLE i.prop.2.1).le)) ?_
  intro x hx
  rw [Opens.mem_iSup]
  rw [Opens.mem_map] at hx
  obtain ⟨_, ⟨V, hV_BY, rfl⟩, hfx_V, hV_W⟩ := hBY.mem_nhds_iff.mp (W.2.mem_nhds hx)
  have hx_fV : x ∈ ((Opens.map f.hom.base).obj V : Set X.carrier) := hfx_V
  obtain ⟨_, ⟨U, hU_BX, rfl⟩, hx_U, hU_fV⟩ :=
    hBX.mem_nhds_iff.mp (((Opens.map f.hom.base).obj V).2.mem_nhds hx_fV)
  exact ⟨⟨(V, U), hV_BY, hV_W, hU_BX, hU_fV⟩, hx_U⟩

/-- Each member of the basis cover of `f⁻¹ W` lies in `f⁻¹ W`. -/
private lemma coverFamily_le {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier)) (W : Opens Y.carrier)
    (i : CoverIdx f BX BY W) : coverFamily f BX BY W i ≤ (Opens.map f.hom.base).obj W :=
  le_trans i.prop.2.2.2 ((Opens.map f.hom.base).monotone (homOfLE i.prop.2.1).le)

/-- The maps `φ_V^U` do not depend on the choice of `V`: if `V₁, V₂ ∈ BY` both contain a
common `V' ∈ BY` over which `U' ∈ BX` still lies, then `φ_{V₁}^{U'}` and `φ_{V₂}^{U'}` send
the restrictions of a section `g` over `W` to the same section over `U'`. -/
lemma basisApp_agreement {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (φ : BasisCompat f F G BX BY)
    {V₁ V₂ : Opens Y.carrier} (hV₁ : V₁ ∈ BY) (hV₂ : V₂ ∈ BY)
    {W : Opens Y.carrier} (hV₁W : V₁ ≤ W) (hV₂W : V₂ ≤ W)
    {U' : Opens X.carrier} (hU' : U' ∈ BX)
    (hU'V₁ : U' ≤ (Opens.map f.hom.base).obj V₁)
    (hU'V₂ : U' ≤ (Opens.map f.hom.base).obj V₂)
    {V' : Opens Y.carrier} (hV' : V' ∈ BY) (hV'V₁ : V' ≤ V₁) (hV'V₂ : V' ≤ V₂)
    (hU'V' : U' ≤ (Opens.map f.hom.base).obj V')
    (g : G.sections W) :
    φ.basisApp hV₁ hU' hU'V₁ (G.restrict hV₁W g) =
    φ.basisApp hV₂ hU' hU'V₂ (G.restrict hV₂W g) := by
  have h1 := φ.basisApp_restrict hV₁ hV' hV'V₁ hU' hU' (le_refl U') hU'V₁ hU'V' (G.restrict hV₁W g)
  have h2 := φ.basisApp_restrict hV₂ hV' hV'V₂ hU' hU' (le_refl U') hU'V₂ hU'V' (G.restrict hV₂W g)
  rw [F.restrict_self] at h1 h2
  rw [h1, h2, G.restrict_restrict, G.restrict_restrict]

/-- The sections `φ_V^U(g|_V)` attached to the members of the basis cover of `f⁻¹ W` agree on
overlaps, so they are a candidate gluing datum for the sheaf `F`. -/
lemma cover_sections_compatible {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (hBX : Opens.IsBasis BX) (hBY : Opens.IsBasis BY)
    (φ : BasisCompat f F G BX BY)
    (W : Opens Y.carrier) (g : G.sections W) :
    TopCat.Presheaf.IsCompatible F.toPresheaf.presheaf (coverFamily f BX BY W)
      (fun i => φ.basisApp i.prop.1 i.prop.2.2.1 i.prop.2.2.2
        (G.restrict i.prop.2.1 g)) := by
  intro i j
  let V₁ := i.val.1; let U₁ := i.val.2
  let V₂ := j.val.1; let U₂ := j.val.2
  -- Use section_ext_cover with a cover of U₁ ⊓ U₂ by opens that lie in f⁻¹(V')
  -- for some V' ∈ BY with V' ≤ V₁ ⊓ V₂
  let ι := { q : Opens Y.carrier × Opens X.carrier //
    q.1 ∈ BY ∧ q.1 ≤ V₁ ∧ q.1 ≤ V₂ ∧ q.2 ∈ BX ∧ q.2 ≤ U₁ ⊓ U₂ ∧
    q.2 ≤ (Opens.map f.hom.base).obj q.1 }
  let U_cover : ι → Opens X.carrier := fun k => k.val.2
  have hle : ∀ k : ι, U_cover k ≤ U₁ ⊓ U₂ := fun k => k.prop.2.2.2.2.1
  have hcover : U₁ ⊓ U₂ ≤ iSup U_cover := by
    intro x hx
    rw [Opens.mem_iSup]
    have hxU₁ : x ∈ (U₁ : Set X.carrier) := hx.1
    have hxU₂ : x ∈ (U₂ : Set X.carrier) := hx.2
    have hfx_inf : f.hom.base x ∈ (V₁ ⊓ V₂ : Opens Y.carrier) :=
      ⟨i.prop.2.2.2 hxU₁, j.prop.2.2.2 hxU₂⟩
    obtain ⟨_, ⟨V', hV'BY, rfl⟩, hfxV', hV'le⟩ :=
      hBY.mem_nhds_iff.mp ((V₁ ⊓ V₂).2.mem_nhds hfx_inf)
    have hx_fV' : x ∈ ((Opens.map f.hom.base).obj V' : Set X.carrier) := hfxV'
    have hx_inter : x ∈ ((Opens.map f.hom.base).obj V' ⊓ (U₁ ⊓ U₂) : Opens X.carrier) :=
      ⟨hx_fV', hx⟩
    obtain ⟨_, ⟨U', hU'BX, rfl⟩, hxU', hU'le2⟩ :=
      hBX.mem_nhds_iff.mp (((Opens.map f.hom.base).obj V' ⊓ (U₁ ⊓ U₂)).2.mem_nhds hx_inter)
    exact ⟨⟨(V', U'), hV'BY, le_trans hV'le inf_le_left, le_trans hV'le inf_le_right,
      hU'BX, le_trans hU'le2 inf_le_right, le_trans hU'le2 inf_le_left⟩, hxU'⟩
  apply F.section_ext_cover U_cover hle hcover
  intro k
  have hU'_le_U₁ : k.val.2 ≤ U₁ := le_trans k.prop.2.2.2.2.1 inf_le_left
  have hU'_le_U₂ : k.val.2 ≤ U₂ := le_trans k.prop.2.2.2.2.1 inf_le_right
  rw [F.restrict_apply, F.restrict_apply,
      ← CategoryTheory.comp_apply (F.toPresheaf.presheaf.map (Opens.infLELeft U₁ U₂).op)
        (F.toPresheaf.presheaf.map (homOfLE (hle k)).op),
      ← CategoryTheory.comp_apply (F.toPresheaf.presheaf.map (Opens.infLERight U₁ U₂).op)
        (F.toPresheaf.presheaf.map (homOfLE (hle k)).op),
      ← F.toPresheaf.presheaf.map_comp, ← F.toPresheaf.presheaf.map_comp,
      show (Opens.infLELeft U₁ U₂).op ≫ (homOfLE (hle k)).op = (homOfLE hU'_le_U₁).op
        from Subsingleton.elim _ _,
      show (Opens.infLERight U₁ U₂).op ≫ (homOfLE (hle k)).op = (homOfLE hU'_le_U₂).op
        from Subsingleton.elim _ _,
      ← F.restrict_apply, ← F.restrict_apply,
      φ.basisApp_restrict i.prop.1 k.prop.1 k.prop.2.1 i.prop.2.2.1 k.prop.2.2.2.1 hU'_le_U₁
        i.prop.2.2.2 k.prop.2.2.2.2.2 (G.restrict i.prop.2.1 g),
      φ.basisApp_restrict j.prop.1 k.prop.1 k.prop.2.2.1 j.prop.2.2.1 k.prop.2.2.2.1 hU'_le_U₂
        j.prop.2.2.2 k.prop.2.2.2.2.2 (G.restrict j.prop.2.1 g),
      G.restrict_restrict, G.restrict_restrict]

/-- The section `ψ_W(g) ∈ F(f⁻¹ W)` obtained by gluing the sections `φ_{V}^{U}(g|_V)` over the
basis cover of `f⁻¹ W`. This is the value at `W` of the `f`-map built from `φ`. -/
noncomputable def constructApp
    {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (hBY : Opens.IsBasis BY) (hBX : Opens.IsBasis BX)
    (φ : BasisCompat f F G BX BY)
    (W : Opens Y.carrier) (g : G.sections W) :
    F.sections ((Opens.map f.hom.base).obj W) := by
  -- Get the unique gluing property from F being a sheaf
  have hSheaf := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    F.toPresheaf.presheaf).mp F.isSheaf
  -- Define the sections on the covering family
  let sf : (i : CoverIdx f BX BY W) →
      F.toPresheaf.presheaf.obj (op (coverFamily f BX BY W i)) :=
    fun i => φ.basisApp i.prop.1 i.prop.2.2.1 i.prop.2.2.2
      (G.restrict i.prop.2.1 g)
  -- Get compatibility
  have hcompat := cover_sections_compatible f F G BX BY hBX hBY φ W g
  -- Apply sheaf gluing to get unique section on iSup
  have hglue := hSheaf (coverFamily f BX BY W) sf hcompat
  -- Transport via the covering equality iSup coverFamily = f⁻¹(W)
  have heq := cover_iSup_eq f BX BY hBX hBY W
  exact heq ▸ hglue.choose

/-- Restricting `ψ_W(g)` to a member `U` of the basis cover of `f⁻¹ W` gives `φ_V^U(g|_V)`. -/
private lemma restrict_constructApp_cover
    {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (hBY : Opens.IsBasis BY) (hBX : Opens.IsBasis BX)
    (φ : BasisCompat f F G BX BY)
    {W : Opens Y.carrier} (i : CoverIdx f BX BY W)
    (hi : coverFamily f BX BY W i ≤ (Opens.map f.hom.base).obj W) (g : G.sections W) :
    F.restrict hi (constructApp f F G BX BY hBY hBX φ W g) =
      φ.basisApp i.prop.1 i.prop.2.2.1 i.prop.2.2.2 (G.restrict i.prop.2.1 g) := by
  unfold constructApp
  set hSheaf := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    F.toPresheaf.presheaf).mp F.isSheaf
  set sf : (j : CoverIdx f BX BY W) →
      F.toPresheaf.presheaf.obj (op (coverFamily f BX BY W j)) :=
    fun j => φ.basisApp j.prop.1 j.prop.2.2.1 j.prop.2.2.2 (G.restrict j.prop.2.1 g)
  set hcompat := cover_sections_compatible f F G BX BY hBX hBY φ W g
  set hglue := hSheaf (coverFamily f BX BY W) sf hcompat
  set heq := cover_iSup_eq f BX BY hBX hBY W
  suffices h : ∀ (T : Opens X.carrier) (heqT : iSup (coverFamily f BX BY W) = T)
      (hleT : coverFamily f BX BY W i ≤ T),
      F.restrict hleT (heqT ▸ hglue.choose) = sf i from h _ heq hi
  intro T heqT hleT
  subst heqT
  rw [F.restrict_apply, show (homOfLE hleT).op = (Opens.leSupr (coverFamily f BX BY W) i).op
    from Subsingleton.elim _ _]
  exact hglue.choose_spec.1 i

/-- The recovery property: restricting `ψ_V(g)` to a basis open `U ≤ f⁻¹ V` returns
`φ_V^U(g)`. -/
lemma constructApp_restrict_basis
    {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (hBY : Opens.IsBasis BY) (hBX : Opens.IsBasis BX)
    (φ : BasisCompat f F G BX BY)
    {V : Opens Y.carrier} (hV : V ∈ BY)
    {U : Opens X.carrier} (hU : U ∈ BX) (hUV : U ≤ (Opens.map f.hom.base).obj V)
    (g : G.sections V) :
    F.restrict hUV (constructApp f F G BX BY hBY hBX φ V g) =
      φ.basisApp hV hU hUV g := by
  simpa using restrict_constructApp_cover f F G BX BY hBY hBX φ
    (⟨(V, U), hV, le_refl V, hU, hUV⟩ : CoverIdx f BX BY V) hUV g

/-- `ψ_W` is additive. -/
lemma constructApp_add
    {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (hBY : Opens.IsBasis BY) (hBX : Opens.IsBasis BX)
    (φ : BasisCompat f F G BX BY)
    (W : Opens Y.carrier) (g₁ g₂ : G.sections W) :
    constructApp f F G BX BY hBY hBX φ W (g₁ + g₂) =
      constructApp f F G BX BY hBY hBX φ W g₁ +
        constructApp f F G BX BY hBY hBX φ W g₂ := by
  refine F.section_ext_cover _ (coverFamily_le f BX BY W) (cover_iSup_eq f BX BY hBX hBY W).ge
    _ _ fun i => ?_
  simp only [map_add, restrict_constructApp_cover f F G BX BY hBY hBX φ i]

/-- `ψ_W` sends the zero section to the zero section. -/
lemma constructApp_zero
    {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (hBY : Opens.IsBasis BY) (hBX : Opens.IsBasis BX)
    (φ : BasisCompat f F G BX BY)
    (W : Opens Y.carrier) :
    constructApp f F G BX BY hBY hBX φ W 0 = 0 := by
  refine F.section_ext_cover _ (coverFamily_le f BX BY W) (cover_iSup_eq f BX BY hBX hBY W).ge
    _ _ fun i => ?_
  simp only [map_zero, restrict_constructApp_cover f F G BX BY hBY hBX φ i]

/-- `ψ_W` is semilinear over `f^♯_W`. -/
lemma constructApp_smul
    {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (hBY : Opens.IsBasis BY) (hBX : Opens.IsBasis BX)
    (φ : BasisCompat f F G BX BY)
    (W : Opens Y.carrier) (r : Y.presheaf.obj (op W)) (g : G.sections W) :
    constructApp f F G BX BY hBY hBX φ W (r • g) =
      (fSharp f W r) • constructApp f F G BX BY hBY hBX φ W g := by
  have hle := coverFamily_le f BX BY W
  refine F.section_ext_cover _ hle (cover_iSup_eq f BX BY hBX hBY W).ge _ _ fun i => ?_
  have hrestrict := restrict_constructApp_cover f F G BX BY hBY hBX φ i (hle i)
  rw [hrestrict (r • g)]
  -- Semilinearity of `F.restrict`
  rw [show F.restrict (hle i) ((fSharp f W r) • constructApp f F G BX BY hBY hBX φ W g) =
      (X.presheaf.map (homOfLE (hle i)).op (fSharp f W r)) •
        F.restrict (hle i) (constructApp f F G BX BY hBY hBX φ W g)
    from PresheafOfModules.map_smul F.toPresheaf (homOfLE (hle i)).op (fSharp f W r)
      (constructApp f F G BX BY hBY hBX φ W g)]
  rw [hrestrict g]
  -- Use G.restrict smul compatibility
  rw [show G.restrict i.prop.2.1 (r • g) =
      (Y.presheaf.map (homOfLE i.prop.2.1).op r) • G.restrict i.prop.2.1 g
    from PresheafOfModules.map_smul G.toPresheaf (homOfLE i.prop.2.1).op r g]
  -- Apply basisApp_smul
  rw [φ.basisApp_smul i.prop.1 i.prop.2.2.1 i.prop.2.2.2
    (Y.presheaf.map (homOfLE i.prop.2.1).op r) (G.restrict i.prop.2.1 g)]
  -- Reduce to scalar equality
  congr 1
  -- Express both sides as single composed morphism applied to r, use naturality
  unfold fSharpRestrict
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply]
  congr 2
  rw [fSharp, fSharp, ← Category.assoc, f.hom.c.naturality, Category.assoc,
    TopCat.Presheaf.pushforward_obj_map, ← X.presheaf.map_comp]
  congr 1

/-- `ψ` commutes with restriction: `ψ_{W'}(g|_{W'})` is the restriction of `ψ_W(g)` to
`f⁻¹ W'`. -/
lemma constructApp_naturality
    {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (hBY : Opens.IsBasis BY) (hBX : Opens.IsBasis BX)
    (φ : BasisCompat f F G BX BY)
    {W W' : Opens Y.carrier} (h : W' ≤ W) (g : G.sections W) :
    constructApp f F G BX BY hBY hBX φ W' (G.restrict h g) =
      F.restrict ((Opens.map f.hom.base).map (homOfLE h)).le
        (constructApp f F G BX BY hBY hBX φ W g) := by
  refine F.section_ext_cover _ (coverFamily_le f BX BY W') (cover_iSup_eq f BX BY hBX hBY W').ge
    _ _ fun i => ?_
  -- View the cover index `i` of `W'` as a cover index of `W` via `W' ≤ W`
  let i_W : CoverIdx f BX BY W :=
    ⟨i.val, i.prop.1, le_trans i.prop.2.1 h, i.prop.2.2.1, i.prop.2.2.2⟩
  rw [restrict_constructApp_cover f F G BX BY hBY hBX φ i (coverFamily_le f BX BY W' i),
    F.restrict_restrict,
    restrict_constructApp_cover f F G BX BY hBY hBX φ i_W _ g, G.restrict_restrict]

/-- Two `f`-maps that both recover the same basis data `φ` are equal. -/
lemma fmap_unique
    {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BX : Set (Opens X.carrier)) (BY : Set (Opens Y.carrier))
    (hBY : Opens.IsBasis BY) (hBX : Opens.IsBasis BX)
    (φ : BasisCompat f F G BX BY)
    (ψ₁ ψ₂ : FMapAddGroupHom f F G)
    (h₁ : ∀ {V : Opens Y.carrier} (hV : V ∈ BY)
      {U : Opens X.carrier} (hU : U ∈ BX) (hUV : U ≤ (Opens.map f.hom.base).obj V)
      (g : G.sections V), φ.basisApp hV hU hUV g = F.restrict hUV (ψ₁.app V g))
    (h₂ : ∀ {V : Opens Y.carrier} (hV : V ∈ BY)
      {U : Opens X.carrier} (hU : U ∈ BX) (hUV : U ≤ (Opens.map f.hom.base).obj V)
      (g : G.sections V), φ.basisApp hV hU hUV g = F.restrict hUV (ψ₂.app V g)) :
    ψ₁ = ψ₂ := by
  -- Suffices to show ψ₁.app = ψ₂.app (other fields are Prop)
  have happ : ψ₁.app = ψ₂.app := by
    funext W
    ext g
    have hle := coverFamily_le f BX BY W
    refine F.section_ext_cover _ hle (cover_iSup_eq f BX BY hBX hBY W).ge _ _ fun i => ?_
    -- Split the restriction to a cover piece through `f⁻¹ V` and use naturality of `ψ₁`, `ψ₂`
    have hdecomp : ∀ s : F.sections ((Opens.map f.hom.base).obj W),
        F.restrict (hle i) s = F.restrict i.prop.2.2.2
          (F.restrict ((Opens.map f.hom.base).map (homOfLE i.prop.2.1)).le s) :=
      fun s => (F.restrict_restrict _ _ s).symm
    rw [hdecomp, ← ψ₁.naturality i.prop.2.1, hdecomp, ← ψ₂.naturality i.prop.2.1]
    exact (h₁ i.prop.1 i.prop.2.2.1 i.prop.2.2.2 _).symm.trans (h₂ i.prop.1 i.prop.2.2.1 _ _)
  cases ψ₁
  cases ψ₂
  congr

/-! ## Main theorem -/

/-- **Stacks 009Y.** Let `f : X ⟶ Y` be a morphism of ringed spaces, `F` a sheaf of
`𝒪_X`-modules, `G` a sheaf of `𝒪_Y`-modules, and `BX`, `BY` bases of the topologies of `X`
and `Y`. Then a compatible system `φ` of maps `G(V) → F(U)`, indexed by the pairs of basis
opens with `U ≤ f⁻¹ V`, extends to a unique `f`-map `ψ : G → F`, and each `φ_V^U` is
recovered from `ψ` as the composite `G(V) → F(f⁻¹ V) → F(U)`. -/
@[stacks 009Y, ega "0 4.4.1" "basis data suffices"]
theorem existsUnique_fMap_of_bases
    {X Y : RingedSpace.{v, u}} (f : X ⟶ Y)
    (F : SheafOfModulesOnRingedSpace X) (G : SheafOfModulesOnRingedSpace Y)
    (BY : Set (Opens Y.carrier)) (BX : Set (Opens X.carrier))
    (hBY : Opens.IsBasis BY) (hBX : Opens.IsBasis BX)
    (φ : BasisCompat f F G BX BY) :
    ∃! ψ : FMapAddGroupHom f F G,
      ∀ {V : Opens Y.carrier} (hV : V ∈ BY)
        {U : Opens X.carrier} (hU : U ∈ BX) (hUV : U ≤ (Opens.map f.hom.base).obj V)
        (g : G.sections V),
        φ.basisApp hV hU hUV g = F.restrict hUV (ψ.app V g) := by
  refine ⟨⟨fun V => ⟨⟨constructApp f F G BX BY hBY hBX φ V,
    constructApp_zero f F G BX BY hBY hBX φ V⟩,
    constructApp_add f F G BX BY hBY hBX φ V⟩,
    constructApp_smul f F G BX BY hBY hBX φ,
    constructApp_naturality f F G BX BY hBY hBX φ⟩,
    fun {V} hV {U} hU hUV g =>
      (constructApp_restrict_basis f F G BX BY hBY hBX φ hV hU hUV g).symm,
    fun ψ hψ => fmap_unique f F G BX BY hBY hBX φ ψ _
      (fun {V} hV {U} hU hUV g => hψ hV hU hUV g)
      (fun {V} hV {U} hU hUV g =>
        (constructApp_restrict_basis f F G BX BY hBY hBX φ hV hU hUV g).symm)⟩

end Stacks.RingedSpace
