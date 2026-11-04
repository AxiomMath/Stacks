module

public import StacksFrontier.AlgebraicGeometry.Modules.AffineChartSheaf
public import StacksFrontier.AlgebraicGeometry.Modules.ChartSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Modules.GlueDataOfBasis
public import StacksFrontier.AlgebraicGeometry.Modules.GluedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherent sheaves from affine-local systems of modules

Let `Y` be a scheme. An *affine-local quasi-coherent system* `T` on `Y` assigns to every affine
open `U` a `Γ(Y, U)`-module `T(U)`, and to every inclusion `V ≤ U` of affine opens a restriction
map `ρ : T(U) → T(V)` which is `Γ(Y, U)`-linear (with `T(V)` a `Γ(Y, U)`-module by restriction of
scalars), functorial, and *quasi-coherent*: the induced `Γ(Y, V)`-linear map
`Γ(Y, V) ⊗_{Γ(Y, U)} T(U) → T(V)` is bijective. No separation hypothesis is made on `Y`.

This file shows that such a system is the same as a quasi-coherent `𝒪_Y`-module. From `T` we
construct a quasi-coherent `𝒪_Y`-module `T̃` together with `Γ(Y, U)`-linear identifications
`Γ(T̃, U) ≃ T(U)` for every affine open `U`, compatible with the restriction maps. The
construction is functorial and exact, preserves finiteness (on a locally Noetherian scheme `T̃` is
coherent as soon as every `T(U)` is finite) and support, and the system of sections of a
quasi-coherent module `F` over the affine opens gives back `F`.

## Main definitions

* `Stacks.Modules.IsBaseChangeAlong`: a semilinear map `f : M →ₛₗ[φ] N` exhibits `N` as the base
  change of `M` along the ring homomorphism `φ`.
* `Stacks.Modules.AffineSystem`: an affine-local quasi-coherent system on a scheme.
* `Stacks.Modules.AffineSystem.Hom`: morphisms of systems, making `AffineSystem Y` a category.
* `Stacks.Modules.AffineSystem.sheaf`: the quasi-coherent `𝒪_Y`-module `T̃`.
* `Stacks.Modules.AffineSystem.sectionsEquiv`: the identification `Γ(T̃, U) ≃ₗ[Γ(Y, U)] T(U)`.
* `Stacks.Modules.AffineSystem.sheafMap` and `Stacks.Modules.AffineSystem.sheafFunctor`: the
  morphism `T̃ ⟶ T̃'` induced by a morphism of systems, and the functor `T ↦ T̃`.
* `Stacks.Modules.AffineSystem.ofQuasicoherent` and
  `Stacks.Modules.AffineSystem.ofQuasicoherentIso`: the system of affine sections of a
  quasi-coherent module `F`, and the isomorphism of its sheaf with `F`.

## Main results

* `Stacks.Modules.AffineSystem.sectionsEquiv_res`: the identifications `Γ(T̃, U) ≃ T(U)` commute
  with restriction along any inclusion `V ≤ U` of affine opens.
* `Stacks.Modules.AffineSystem.isQuasicoherent_sheaf`: `T̃` is quasi-coherent.
* `Stacks.Modules.AffineSystem.sectionsEquiv_sheafMap_app`: on an affine open `U`, the induced
  morphism `T̃ ⟶ T̃'` is the given map `T(U) → T'(U)`; `sheafMap_id` and `sheafMap_comp`.
* `Stacks.Modules.AffineSystem.exact_sheafMap` and
  `Stacks.Modules.AffineSystem.shortExact_sheafMap`: a sequence of systems which is exact on
  every affine open gives an exact sequence of `𝒪_Y`-modules; likewise for short exact
  sequences, so a long exact sequence of systems gives a long exact sequence of quasi-coherent
  modules.
* `Stacks.Modules.AffineSystem.isCoherent_sheaf`: on a locally Noetherian scheme, `T̃` is coherent
  if every `T(U)` is a finite `Γ(Y, U)`-module.
* `Stacks.Modules.AffineSystem.supp_sheaf_subset`: the support of `T̃` lies in `Z` as soon as,
  for every affine open `U`, the support of `T(U)` lies over `Z ∩ U` under `Spec Γ(Y, U) ≅ U`.
* `Stacks.Modules.exact_of_exact_sections`: a short complex of `𝒪_Y`-modules is exact as soon as
  it is exact on the sections over every affine open.

## Implementation notes

`T̃` is glued (Stacks 00AM) from the *chart sheaves* `chartSheaf U T(U)`, the direct images of the
modules `T(U)^~` along `Spec Γ(Y, U) ≅ U ⊆ Y`. The direct image of a quasi-coherent module along
the inclusion of an affine open need not be quasi-coherent on `Y` when `Y` is not quasi-separated,
but only its restriction to `U` matters for the glueing. Two charts are compared over the affine
opens which are *basic* (of the form `D(g)`) in both: over such an open `V ⊆ U` the sections of
the chart at `U` are the localization of `T(U)`, hence its base change to `Γ(Y, V)`, and so are
canonically `T(V)` by the quasi-coherence of `T`. The cocycle condition is then automatic, since
all comparisons factor through `T(V)`. Such opens form a basis of every pairwise and every triple
intersection of affine opens, which is what
`Stacks.Modules.exists_transData_of_basis` needs to extend the comparisons to all opens of the
overlaps.

The identification `Γ(T̃, V) ≃ T(V)` is first shown to commute with restriction along an
inclusion `V ≤ U` with `V` basic in `U`; for a general inclusion of affine opens one compares
both sides after restriction to the opens basic in both `V` and `U`, which cover `V`, and uses
that `T(V)` is separated for these restrictions (being `Γ(T̃, V)`). Morphisms of systems are
assembled into morphisms of sheaves on the basis of affine opens (Stacks 009U).

The quasi-coherence condition on a system is stated with `IsBaseChange` for the
`Γ(Y, U)`-linear map underlying the semilinear restriction map, the algebra and module structures
over `Γ(Y, U)` being those obtained from the restriction map of rings. Only its instance for basic
opens is used in the construction; for the system of sections of a quasi-coherent module the
general instance is `Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_restrictₗ`.

## References

* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR) and
  [Tag 01I8](https://stacks.math.columbia.edu/tag/01I8), for quasi-coherent modules on affine
  schemes and affine opens.
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9), for the base change
  property of the sections of a quasi-coherent module over nested affine opens.
* [Stacks Project, Tag 009J](https://stacks.math.columbia.edu/tag/009J) and
  [Tag 009U](https://stacks.math.columbia.edu/tag/009U), for sheaves on a basis.
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM), for glueing sheaves of
  modules.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Modules

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {M N : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- The `R`-linear map underlying a `φ`-semilinear map `f : M →ₛₗ[φ] N`, the target being an
`R`-module by restriction of scalars along `φ`. -/
@[ega "II 1.7.2" "partial"]
def semilinearToLinear (f : M →ₛₗ[φ] N) :
    letI := Module.compHom N φ
    M →ₗ[R] N :=
  letI := Module.compHom N φ
  { toFun := f
    map_add' := f.map_add
    map_smul' := f.map_smulₛₗ }

/-- A `φ`-semilinear map `f : M →ₛₗ[φ] N` *exhibits `N` as the base change of `M` along `φ`*:
regarding `S` as an `R`-algebra and `N` as an `R`-module through `φ`, the induced `S`-linear map
`S ⊗[R] M → N` is bijective. -/
def IsBaseChangeAlong (f : M →ₛₗ[φ] N) : Prop :=
  letI := φ.toAlgebra
  letI := Module.compHom N φ
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  IsBaseChange S (semilinearToLinear φ f)

end BaseChange

section Sections

variable {Y : Scheme.{u}}

/-- The affine opens of a scheme, as the range of the inclusion of `Y.affineOpens`, form a basis
of its topology. -/
lemma isBasis_range_affineOpens :
    Opens.IsBasis (Set.range fun U : Y.affineOpens => (U : Y.Opens)) := by
  rw [Subtype.range_coe]
  exact Y.isBasis_affineOpens

/-- **Exactness of a short complex of `𝒪_Y`-modules can be tested on affine opens.** If on the
sections over every affine open, every section killed by `g` is in the image of `f`, the short
complex `E ⟶ F ⟶ G` is exact. -/
theorem exact_of_exact_sections {E F G : Y.Modules} (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0)
    (h : ∀ (U : Y.affineOpens) (s : Γ(F, U)), g.app U s = 0 → ∃ t : Γ(E, U), f.app U t = s) :
    (ShortComplex.mk f g w).Exact := by
  have hS : (ShortComplex.mk (C := _root_.SheafOfModules.{u} Y.ringCatSheaf) f g w).Exact := by
    rw [AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact]
    intro x
    rw [ShortComplex.moduleCat_exact_iff]
    intro m hm
    obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
    have hm' : (TopCat.Presheaf.germ G.val.presheaf W x hxW).hom (g.val.app (op W) s) =
        (TopCat.Presheaf.germ G.val.presheaf W x hxW).hom 0 := by
      rw [map_zero]
      exact (AlgebraicGeometry.SheafOfModules.stalkMap_germ _ x g W hxW s).symm.trans hm
    obtain ⟨W', hxW', i₁, i₂, hW'⟩ := TopCat.Presheaf.germ_eq _ x hxW hxW _ _ hm'
    obtain ⟨V, hV, hxV, hVW'⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hxW'
    have hgs : g.app V (F.presheaf.map (homOfLE (hVW'.trans i₁.le)).op s) = 0 := by
      have e := congr($(g.mapPresheaf.naturality (homOfLE (hVW'.trans i₁.le)).op) s)
      have hW'' : G.presheaf.map i₁.op (g.app W s) = G.presheaf.map i₂.op 0 := hW'
      refine e.trans ?_
      show G.presheaf.map (homOfLE (hVW'.trans i₁.le)).op (g.app W s) = 0
      rw [← res_comp G (homOfLE hVW') i₁ (homOfLE (hVW'.trans i₁.le)), hW'', map_zero, map_zero]
    obtain ⟨t, ht⟩ := h ⟨V, hV⟩ _ hgs
    refine ⟨(TopCat.Presheaf.germ E.val.presheaf V x hxV).hom t, ?_⟩
    refine (AlgebraicGeometry.SheafOfModules.stalkMap_germ _ x f V hxV t).trans ?_
    show (TopCat.Presheaf.germ F.val.presheaf V x hxV).hom (f.app V t) = _
    rw [ht]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  exact hS

end Sections

/-- An **affine-local quasi-coherent system** on a scheme `Y`: a `Γ(Y, U)`-module `obj U` for
every affine open `U`, and for affine opens `V ≤ U` a restriction map `obj U → obj V`, semilinear
along the restriction `Γ(Y, U) → Γ(Y, V)`, which is functorial and exhibits `obj V` as the base
change `Γ(Y, V) ⊗_{Γ(Y, U)} obj U`. -/
structure AffineSystem (Y : Scheme.{u}) where
  /-- The module over an affine open. -/
  obj (U : Y.affineOpens) : ModuleCat.{u} Γ(Y, U)
  /-- The restriction map to a smaller affine open. -/
  map {U V : Y.affineOpens} (h : (V : Y.Opens) ≤ U) :
    obj U →ₛₗ[(Y.presheaf.map (homOfLE h).op).hom] obj V
  /-- Restriction to the same affine open is the identity. -/
  map_id (U : Y.affineOpens) (x : obj U) : map (le_refl (U : Y.Opens)) x = x
  /-- Restriction is transitive. -/
  map_comp {U V W : Y.affineOpens} (h₁ : (V : Y.Opens) ≤ U) (h₂ : (W : Y.Opens) ≤ V)
    (x : obj U) : map h₂ (map h₁ x) = map (h₂.trans h₁) x
  /-- Quasi-coherence: `obj V` is the base change of `obj U` to `Γ(Y, V)`. -/
  isBaseChange {U V : Y.affineOpens} (h : (V : Y.Opens) ≤ U) :
    IsBaseChangeAlong (Y.presheaf.map (homOfLE h).op).hom (map h)

namespace AffineSystem

variable {Y : Scheme.{u}}

/-! ### Opens which are basic in an affine open -/

/-- `k` is a basic open `D(g)` of the open `U`. -/
def IsBasicIn (U k : Y.Opens) : Prop := ∃ g : Γ(Y, U), Y.basicOpen g = k

/-- A basic open of `U` is contained in `U`. -/
lemma IsBasicIn.le {U k : Y.Opens} (h : IsBasicIn U k) : k ≤ U := by
  obtain ⟨g, rfl⟩ := h
  exact Y.basicOpen_le g

/-- A basic open of an affine open is affine. -/
lemma IsBasicIn.isAffineOpen {U k : Y.Opens} (hU : IsAffineOpen U) (h : IsBasicIn U k) :
    IsAffineOpen k := by
  obtain ⟨g, rfl⟩ := h
  exact hU.basicOpen g

/-- Every open is basic in itself, as `D(1)`. -/
lemma isBasicIn_self (U : Y.Opens) : IsBasicIn U U := ⟨1, Y.basicOpen_one⟩

/-- A basic open of a basic open of an affine open `U` is basic in `U`. -/
lemma IsBasicIn.trans {U k l : Y.Opens} (hU : IsAffineOpen U) (hk : IsBasicIn U k)
    (hl : IsBasicIn k l) : IsBasicIn U l := by
  obtain ⟨g, rfl⟩ := hk
  obtain ⟨h, rfl⟩ := hl
  exact hU.basicOpen_basicOpen_is_basicOpen g h

/-- Around every point of an open contained in two affine opens there is an open which is basic
in both of them and lies in the given open. -/
lemma exists_isBasicIn_pair {U U' : Y.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    {V : Y.Opens} (hV : V ≤ U ⊓ U') {x : Y} (hx : x ∈ V) :
    ∃ k : Y.Opens, IsBasicIn U k ∧ IsBasicIn U' k ∧ x ∈ k ∧ k ≤ V := by
  obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le (V := V) ⟨x, hx⟩ (hV hx).1
  obtain ⟨a, b, hab, hxa⟩ :=
    exists_basicOpen_le_affine_inter (hU.basicOpen f) hU' x ⟨hxf, (hV hx).2⟩
  refine ⟨Y.basicOpen a, IsBasicIn.trans hU ⟨f, rfl⟩ ⟨a, rfl⟩, ⟨b, hab.symm⟩, hxa,
    (Y.basicOpen_le a).trans hfV⟩

/-- Around every point of an open contained in three affine opens there is an open which is
basic in all three of them and lies in the given open. -/
lemma exists_isBasicIn_triple {U U' U'' : Y.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hU'' : IsAffineOpen U'') {V : Y.Opens} (hV : V ≤ U ⊓ U' ⊓ U'') {x : Y} (hx : x ∈ V) :
    ∃ k : Y.Opens, IsBasicIn U k ∧ IsBasicIn U' k ∧ IsBasicIn U'' k ∧ x ∈ k ∧ k ≤ V := by
  obtain ⟨k, hk, hk', hxk, hkV⟩ := exists_isBasicIn_pair hU hU'
    (V := V) (fun y hy => (hV hy).1) hx
  obtain ⟨l, hl, hl'', hxl, hlk⟩ := exists_isBasicIn_pair (hk.isAffineOpen hU) hU''
    (V := k) (fun y hy => ⟨hy, (hV (hkV hy)).2⟩) hxk
  exact ⟨l, hk.trans hU hl, hk'.trans hU' hl, hl'', hxl, hlk.trans hkV⟩

/-! ### The chart sheaves and their comparison with the system -/

variable (T : AffineSystem Y)

/-- The chart of `T` at an affine open `U`: the sheaf `chartSheaf U (T.obj U)`, whose sections
over `U` are `T.obj U`. -/
abbrev chart (U : Y.affineOpens) : Y.Modules := chartSheaf U (T.obj U)

/-- `chartSection` as a semilinear map along the restriction `Γ(Y, U) → Γ(Y, W)`. -/
def chartSectionₛₗ (U : Y.affineOpens) (M : ModuleCat.{u} Γ(Y, U)) {W : Y.Opens}
    (h : W ≤ U) : M →ₛₗ[(Y.presheaf.map (homOfLE h).op).hom] Γ(chartSheaf U M, W) where
  toFun := chartSection U M W
  map_add' := chartSection_add U M W
  map_smul' := chartSection_smul U M h

/-- Over a basic open `D(g)` of `U`, the sections of `chartSheaf U M` are the base change of
`M` along `Γ(Y, U) → Γ(Y, D(g))`. -/
lemma isBaseChangeAlong_chartSectionₛₗ (U : Y.affineOpens) (M : ModuleCat.{u} Γ(Y, U))
    (g : Γ(Y, U)) :
    IsBaseChangeAlong _ (chartSectionₛₗ U M (Y.basicOpen_le g)) := by
  let := (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  let := Module.compHom Γ(chartSheaf U M, Y.basicOpen g)
    (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom
  let : IsScalarTower Γ(Y, U) Γ(Y, Y.basicOpen g) Γ(chartSheaf U M, Y.basicOpen g) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsLocalization.Away g Γ(Y, Y.basicOpen g) := U.2.isLocalization_basicOpen g
  have : IsLocalizedModule (Submonoid.powers g)
      (semilinearToLinear _ (chartSectionₛₗ U M (Y.basicOpen_le g))) :=
    isLocalizedModule_chartSectionBasicOpen U M g
  exact IsLocalizedModule.isBaseChange (Submonoid.powers g) Γ(Y, Y.basicOpen g)
    (semilinearToLinear _ (chartSectionₛₗ U M (Y.basicOpen_le g)))

/-- `isBaseChangeAlong_chartSectionₛₗ`, for an open which is basic in `U`. -/
lemma isBaseChangeAlong_chartSectionₛₗ_of_isBasicIn (U : Y.affineOpens)
    (M : ModuleCat.{u} Γ(Y, U)) {k : Y.Opens} (hk : IsBasicIn U k) :
    IsBaseChangeAlong _ (chartSectionₛₗ U M hk.le) := by
  obtain ⟨g, rfl⟩ := hk
  exact isBaseChangeAlong_chartSectionₛₗ U M g

/-- **The comparison of a chart with the system.** For an affine open `V` basic in the affine
open `U`, the sections of the chart of `T` at `U` over `V` are `T.obj V`, `Γ(Y, V)`-linearly:
both are the base change of `T.obj U` along `Γ(Y, U) → Γ(Y, V)`. -/
def chartEquiv (U V : Y.affineOpens) (hV : IsBasicIn (U : Y.Opens) V) :
    Γ(T.chart U, V) ≃ₗ[Γ(Y, V)] T.obj V :=
  letI := (Y.presheaf.map (homOfLE hV.le).op).hom.toAlgebra
  letI := Module.compHom Γ(T.chart U, V) (Y.presheaf.map (homOfLE hV.le).op).hom
  letI := Module.compHom (T.obj V) (Y.presheaf.map (homOfLE hV.le).op).hom
  letI : IsScalarTower Γ(Y, U) Γ(Y, V) Γ(T.chart U, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower Γ(Y, U) Γ(Y, V) (T.obj V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  (show IsBaseChange Γ(Y, V) (semilinearToLinear _ (chartSectionₛₗ U (T.obj U) hV.le)) from
      isBaseChangeAlong_chartSectionₛₗ_of_isBasicIn U (T.obj U) hV).equiv.symm.trans
    (show IsBaseChange Γ(Y, V) (semilinearToLinear _ (T.map hV.le)) from
      T.isBaseChange hV.le).equiv

/-- `chartEquiv` sends the section of the chart determined by `m : T(U)` to the restriction of
`m`. -/
lemma chartEquiv_chartSection (U V : Y.affineOpens) (hV : IsBasicIn (U : Y.Opens) V)
    (m : T.obj U) :
    T.chartEquiv U V hV (chartSection U (T.obj U) V m) = T.map hV.le m := by
  let := (Y.presheaf.map (homOfLE hV.le).op).hom.toAlgebra
  let := Module.compHom Γ(T.chart U, V) (Y.presheaf.map (homOfLE hV.le).op).hom
  let := Module.compHom (T.obj V) (Y.presheaf.map (homOfLE hV.le).op).hom
  let : IsScalarTower Γ(Y, U) Γ(Y, V) Γ(T.chart U, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower Γ(Y, U) Γ(Y, V) (T.obj V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hα : IsBaseChange Γ(Y, V) (semilinearToLinear _ (chartSectionₛₗ U (T.obj U) hV.le)) :=
    isBaseChangeAlong_chartSectionₛₗ_of_isBasicIn U (T.obj U) hV
  have hβ : IsBaseChange Γ(Y, V) (semilinearToLinear _ (T.map hV.le)) := T.isBaseChange hV.le
  show hβ.equiv (hα.equiv.symm (semilinearToLinear _ (chartSectionₛₗ U (T.obj U) hV.le) m)) = _
  rw [hα.equiv_symm_apply, hβ.equiv_tmul, one_smul]
  rfl

/-- The comparison of a chart with the system commutes with restriction between affine opens
basic in the chart's open. -/
lemma chartEquiv_res (U V W : Y.affineOpens) (hV : IsBasicIn (U : Y.Opens) V)
    (hW : IsBasicIn (U : Y.Opens) W) (hWV : (W : Y.Opens) ≤ V) (s : Γ(T.chart U, V)) :
    T.chartEquiv U W hW ((T.chart U).presheaf.map (homOfLE hWV).op s) =
      T.map hWV (T.chartEquiv U V hV s) := by
  let := (Y.presheaf.map (homOfLE hV.le).op).hom.toAlgebra
  let := Module.compHom Γ(T.chart U, V) (Y.presheaf.map (homOfLE hV.le).op).hom
  let : IsScalarTower Γ(Y, U) Γ(Y, V) Γ(T.chart U, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hα : IsBaseChange Γ(Y, V) (semilinearToLinear _ (chartSectionₛₗ U (T.obj U) hV.le)) :=
    isBaseChangeAlong_chartSectionₛₗ_of_isBasicIn U (T.obj U) hV
  induction s using hα.inductionOn with
  | zero => simp only [map_zero]
  | tmul m =>
    show T.chartEquiv U W hW (chartSection U (T.obj U) W m) =
      T.map hWV (T.chartEquiv U V hV (chartSection U (T.obj U) V m))
    rw [chartEquiv_chartSection, chartEquiv_chartSection, T.map_comp]
  | smul a n ih =>
    rw [Scheme.Modules.map_smul, map_smul, map_smul, ih, LinearMap.map_smulₛₗ]
  | add n₁ n₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]

/-- The comparison of the charts at `U` and `U'` over an affine open basic in both. -/
def chartTrans (V U U' : Y.affineOpens) (h : IsBasicIn (U : Y.Opens) V)
    (h' : IsBasicIn (U' : Y.Opens) V) : Γ(T.chart U, V) ≃ₗ[Γ(Y, V)] Γ(T.chart U', V) :=
  (T.chartEquiv U V h).trans (T.chartEquiv U' V h').symm

/-- `chartTrans` commutes with restriction. -/
lemma chartTrans_res (V V' U U' : Y.affineOpens) (h : IsBasicIn (U : Y.Opens) V)
    (h' : IsBasicIn (U' : Y.Opens) V) (k : IsBasicIn (U : Y.Opens) V')
    (k' : IsBasicIn (U' : Y.Opens) V') (hle : (V' : Y.Opens) ≤ V) (s : Γ(T.chart U, V)) :
    T.chartTrans V' U U' k k' ((T.chart U).presheaf.map (homOfLE hle).op s) =
      (T.chart U').presheaf.map (homOfLE hle).op (T.chartTrans V U U' h h' s) := by
  apply (T.chartEquiv U' V' k').injective
  simp only [chartTrans, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [T.chartEquiv_res U' V V' h' k' hle, LinearEquiv.apply_symm_apply,
    T.chartEquiv_res U V V' h k hle]

/-- The cocycle identity for `chartTrans`. -/
lemma chartTrans_trans (V U U' U'' : Y.affineOpens) (h : IsBasicIn (U : Y.Opens) V)
    (h' : IsBasicIn (U' : Y.Opens) V) (h'' : IsBasicIn (U'' : Y.Opens) V)
    (s : Γ(T.chart U, V)) :
    T.chartTrans V U' U'' h' h'' (T.chartTrans V U U' h h' s) = T.chartTrans V U U'' h h'' s := by
  simp only [chartTrans, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- The comparison data on every open of every overlap of two affine opens, extending
`chartTrans`. -/
theorem exists_transData :
    ∃ (t : ∀ (i j : Y.affineOpens) {V : Y.Opens} (_hi : V ≤ i) (_hj : V ≤ j),
        (T.chart i).val.obj (op V) ≃ₗ[ToType (Y.ringCatSheaf.obj.obj (op V))]
          (T.chart j).val.obj (op V))
      (_tm : ∀ (i j : Y.affineOpens) {V V' : Y.Opens} (hi : V ≤ i) (hj : V ≤ j) (h : V' ≤ V)
        (s : ToType ((T.chart i).val.obj (op V))),
        t i j (h.trans hi) (h.trans hj) ((T.chart i).val.map (homOfLE h).op s)
          = (T.chart j).val.map (homOfLE h).op (t i j hi hj s))
      (_tt : ∀ (i j m : Y.affineOpens) {V : Y.Opens} (hi : V ≤ i) (hj : V ≤ j) (hm : V ≤ m)
        (s : ToType ((T.chart i).val.obj (op V))),
        t j m hj hm (t i j hi hj s) = t i m hi hm s),
      ∀ (k i j : Y.affineOpens) (hki : IsBasicIn (i : Y.Opens) k)
        (hkj : IsBasicIn (j : Y.Opens) k) (s : Γ(T.chart i, k)),
        t i j hki.le hkj.le s = T.chartTrans k i j hki hkj s :=
  exists_transData_of_basis (fun i : Y.affineOpens => (i : Y.Opens)) T.chart
    (fun k : Y.affineOpens => (k : Y.Opens)) (fun k i => IsBasicIn (i : Y.Opens) k)
    (fun _ _ h => h.le)
    (fun i j V hV x hx => by
      obtain ⟨k, hk, hk', hxk, hkV⟩ := exists_isBasicIn_pair i.2 j.2 hV hx
      exact ⟨⟨k, hk.isAffineOpen i.2⟩, hk, hk', hxk, hkV⟩)
    (fun i j m V hV x hx => by
      obtain ⟨k, hk, hk', hk'', hxk, hkV⟩ := exists_isBasicIn_triple i.2 j.2 m.2 hV hx
      exact ⟨⟨k, hk.isAffineOpen i.2⟩, hk, hk', hk'', hxk, hkV⟩)
    (fun k i j hi hj => T.chartTrans k i j hi hj)
    (fun k l i j hki hkj hli hlj h s => T.chartTrans_res k l i j hki hkj hli hlj h s)
    (fun k i j m hi hj hm s => T.chartTrans_trans k i j m hi hj hm s)

/-- The glueing datum of the charts of `T` along the affine opens of `Y`. -/
def glueData :
    Stacks.SheafOfModules.OModuleGlueData Y.ringCatSheaf (fun i : Y.affineOpens => (i : Y.Opens)) :=
  Stacks.SheafOfModules.OModuleGlueData.ofModules T.chart T.exists_transData.choose
    T.exists_transData.choose_spec.choose T.exists_transData.choose_spec.choose_spec.choose

/-- Over an affine open basic in both charts, the comparison of the glueing datum is
`chartTrans`. -/
lemma glueData_trans (k i j : Y.affineOpens) (hki : IsBasicIn (i : Y.Opens) k)
    (hkj : IsBasicIn (j : Y.Opens) k) (s : Γ(T.chart i, k)) :
    T.glueData.trans i j hki.le hkj.le s = T.chartTrans k i j hki hkj s :=
  T.exists_transData.choose_spec.choose_spec.choose_spec k i j hki hkj s

/-- **The quasi-coherent sheaf `T̃` attached to an affine-local system `T`**, glued from the
charts of `T` at the affine opens of `Y`. Its sections over an affine open `U` are `T.obj U`
(`sectionsEquiv`), compatibly with restriction (`sectionsEquiv_res`). -/
def sheaf : Y.Modules := T.glueData.gluedModules

/-- The sections of `T̃` over an open `V` contained in an affine open `U` are those of the chart
of `T` at `U`. -/
def sheafChartEquiv (U : Y.affineOpens) {V : Y.Opens} (hV : V ≤ U) :
    Γ(T.sheaf, V) ≃ₗ[Γ(Y, V)] Γ(T.chart U, V) :=
  T.glueData.chartLinearEquiv U hV

/-- `sheafChartEquiv` commutes with restriction. -/
lemma sheafChartEquiv_res (U : Y.affineOpens) {V V' : Y.Opens} (hV : V ≤ U) (h : V' ≤ V)
    (s : Γ(T.sheaf, V)) :
    T.sheafChartEquiv U (h.trans hV) (T.sheaf.presheaf.map (homOfLE h).op s) =
      (T.chart U).presheaf.map (homOfLE h).op (T.sheafChartEquiv U hV s) :=
  T.glueData.chartLinearEquiv_restrict U hV h s

/-- Over an affine open basic in two charts, the two identifications of the sections of `T̃` with
those of the charts differ by `chartTrans`. -/
lemma sheafChartEquiv_basic (k i j : Y.affineOpens) (hki : IsBasicIn (i : Y.Opens) k)
    (hkj : IsBasicIn (j : Y.Opens) k) (s : Γ(T.sheaf, k)) :
    T.sheafChartEquiv j hkj.le s = T.chartTrans k i j hki hkj (T.sheafChartEquiv i hki.le s) :=
  (T.glueData.trans_chartLinearEquiv i j hki.le hkj.le s).symm.trans
    (T.glueData_trans k i j hki hkj _)

/-- **The sections of `T̃` over an affine open `U` are `T.obj U`**, `Γ(Y, U)`-linearly. -/
def sectionsEquiv (U : Y.affineOpens) : Γ(T.sheaf, U) ≃ₗ[Γ(Y, U)] T.obj U :=
  (T.sheafChartEquiv U le_rfl).trans (T.chartEquiv U U (isBasicIn_self _))

/-- Compatibility of `sectionsEquiv` with restriction to an affine open basic in a larger one. -/
lemma sectionsEquiv_res_of_isBasicIn {U V : Y.affineOpens} (hV : IsBasicIn (U : Y.Opens) V)
    (s : Γ(T.sheaf, U)) :
    T.sectionsEquiv V (T.sheaf.presheaf.map (homOfLE hV.le).op s) =
      T.map hV.le (T.sectionsEquiv U s) := by
  have h1 := T.sheafChartEquiv_basic V U V hV (isBasicIn_self _)
    (T.sheaf.presheaf.map (homOfLE hV.le).op s)
  have h2 : T.chartEquiv V V (isBasicIn_self _)
      (T.sheafChartEquiv V le_rfl (T.sheaf.presheaf.map (homOfLE hV.le).op s)) =
      T.chartEquiv U V hV
        (T.sheafChartEquiv U hV.le (T.sheaf.presheaf.map (homOfLE hV.le).op s)) := by
    rw [show (le_rfl : (V : Y.Opens) ≤ V) = (isBasicIn_self (V : Y.Opens)).le from rfl, h1]
    simp only [chartTrans, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  show T.chartEquiv V V (isBasicIn_self _)
      (T.sheafChartEquiv V le_rfl (T.sheaf.presheaf.map (homOfLE hV.le).op s)) = _
  rw [h2, show hV.le = hV.le.trans (le_rfl : (U : Y.Opens) ≤ U) from rfl,
    T.sheafChartEquiv_res U le_rfl hV.le s, T.chartEquiv_res U U V (isBasicIn_self _) hV hV.le]
  rfl

/-- An element of `T.obj V` is determined by its restrictions to the affine opens which are basic
both in `V` and in a larger affine open `U`. -/
lemma ext_of_map_eq {U V : Y.affineOpens} (hVU : (V : Y.Opens) ≤ U) {a b : T.obj V}
    (h : ∀ (W : Y.affineOpens) (hW : IsBasicIn (V : Y.Opens) W), IsBasicIn (U : Y.Opens) W →
      T.map hW.le a = T.map hW.le b) : a = b := by
  obtain ⟨x, rfl⟩ := (T.sectionsEquiv V).surjective a
  obtain ⟨y, rfl⟩ := (T.sectionsEquiv V).surjective b
  suffices x = y by rw [this]
  refine sections_eq_of_basis
    (κ := {W : Y.affineOpens // IsBasicIn (V : Y.Opens) W ∧ IsBasicIn (U : Y.Opens) W})
    (W := fun k => (k.1 : Y.Opens)) T.sheaf (T := (V : Y.Opens)) (fun V' hV' z hz => ?_)
    le_rfl x y (fun k hk => ?_)
  · obtain ⟨k, hk, hk', hzk, hkV⟩ := exists_isBasicIn_pair V.2 U.2 (V := V')
      (fun w hw => ⟨hV' hw, hVU (hV' hw)⟩) hz
    exact ⟨⟨⟨k, hk.isAffineOpen V.2⟩, hk, hk'⟩, hzk, hkV⟩
  · exact (T.sectionsEquiv k.1).injective <| (T.sectionsEquiv_res_of_isBasicIn k.2.1 x).trans
      ((h k.1 k.2.1 k.2.2).trans (T.sectionsEquiv_res_of_isBasicIn k.2.1 y).symm)

/-- **`sectionsEquiv` is compatible with the restriction maps** of `T̃` and of `T`, between any
two affine opens `V ≤ U`. -/
theorem sectionsEquiv_res {U V : Y.affineOpens} (h : (V : Y.Opens) ≤ U) (s : Γ(T.sheaf, U)) :
    T.sectionsEquiv V (T.sheaf.presheaf.map (homOfLE h).op s) =
      T.map h (T.sectionsEquiv U s) := by
  refine T.ext_of_map_eq h fun W hW hW' => ?_
  rw [← T.sectionsEquiv_res_of_isBasicIn hW, T.map_comp,
    res_comp T.sheaf (homOfLE hW.le) (homOfLE h) (homOfLE hW'.le)]
  exact T.sectionsEquiv_res_of_isBasicIn hW' s

/-- **`T̃` is quasi-coherent.** -/
instance isQuasicoherent_sheaf : T.sheaf.IsQuasicoherent :=
  Stacks.SheafOfModules.isQuasicoherent_gluedModules_ofModules
    (U := fun i : Y.affineOpens => (i : Y.Opens)) (iSup_affineOpens_eq_top Y) T.chart _ _ _
    fun i => isQuasicoherent_restrict_chartSheaf i (T.obj i)

/-- **`T̃` is coherent** when `Y` is locally Noetherian and every `T.obj U` is a finite
`Γ(Y, U)`-module. -/
theorem isCoherent_sheaf [IsLocallyNoetherian Y]
    (hT : ∀ U : Y.affineOpens, Module.Finite Γ(Y, U) (T.obj U)) :
    _root_.SheafOfModules.IsCoherent T.sheaf :=
  Stacks.SheafOfModules.isCoherent_gluedModules_ofModules
    (U := fun i : Y.affineOpens => (i : Y.Opens)) (iSup_affineOpens_eq_top Y) T.chart _ _ _
    (fun i => isQuasicoherent_restrict_chartSheaf i (T.obj i))
    (fun i => isFiniteType_restrict_chartSheaf i (T.obj i) (hT i))

/-! ### Morphisms of systems -/

/-- A morphism of affine-local systems: a `Γ(Y, U)`-linear map on every affine open `U`,
commuting with the restriction maps. -/
@[ext]
structure Hom (T T' : AffineSystem Y) where
  /-- The component on an affine open. -/
  app (U : Y.affineOpens) : T.obj U →ₗ[Γ(Y, U)] T'.obj U
  naturality {U V : Y.affineOpens} (h : (V : Y.Opens) ≤ U) (x : T.obj U) :
    app V (T.map h x) = T'.map h (app U x)

/-- The category of affine-local systems on `Y`, with morphisms the families of linear maps
commuting with restriction. -/
instance : Category (AffineSystem Y) where
  Hom := Hom
  id T := ⟨fun _ => LinearMap.id, fun _ _ => rfl⟩
  comp f g := ⟨fun U => g.app U ∘ₗ f.app U, fun h x => by
    simp only [LinearMap.comp_apply, f.naturality, g.naturality]⟩

/-- Morphisms of systems are determined by their components. -/
@[ext]
lemma hom_ext {T T' : AffineSystem Y} {f g : T ⟶ T'} (h : ∀ U, f.app U = g.app U) : f = g :=
  Hom.ext (funext h)

/-- The components of the identity. -/
@[simp]
lemma id_app (U : Y.affineOpens) (x : T.obj U) : Hom.app (𝟙 T) U x = x := rfl

/-- The components of a composite. -/
@[simp]
lemma comp_app {T₁ T₂ T₃ : AffineSystem Y} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) (U : Y.affineOpens)
    (x : T₁.obj U) : Hom.app (f ≫ g) U x = g.app U (f.app U x) := rfl

/-- Two morphisms out of `T̃` agreeing on the sections over every affine open are equal. -/
lemma sheaf_hom_ext {M : Y.Modules} {φ ψ : T.sheaf ⟶ M}
    (h : ∀ (U : Y.affineOpens) (s : Γ(T.sheaf, U)), φ.app U s = ψ.app U s) : φ = ψ :=
  Stacks.BasisRestriction.moduleSheafHom_ext_onBasis (𝒪 := Y.ringCatSheaf) T.sheaf M
    (fun U : Y.affineOpens => (U : Y.Opens)) isBasis_range_affineOpens φ ψ fun U =>
      ModuleCat.hom_ext (LinearMap.ext (h U))

variable {T} {T' T'' : AffineSystem Y}

/-- The components on affine opens of the morphism `T̃ ⟶ T̃'` induced by `f`. -/
def sheafMapApp (f : T ⟶ T') (U : Y.affineOpens) :
    T.sheaf.val.obj (op (U : Y.Opens)) ⟶ T'.sheaf.val.obj (op (U : Y.Opens)) :=
  ModuleCat.ofHom ((T'.sectionsEquiv U).symm.toLinearMap ∘ₗ f.app U ∘ₗ
    (T.sectionsEquiv U).toLinearMap)

/-- The components `sheafMapApp f` commute with restriction between affine opens. -/
lemma sheafMapApp_compatible (f : T ⟶ T') :
    Stacks.BasisRestriction.IsCompatibleOnBasis T.sheaf T'.sheaf
      (fun U : Y.affineOpens => (U : Y.Opens)) (sheafMapApp f) := by
  intro U V (h : (V : Y.Opens) ≤ U) (s : Γ(T.sheaf, (U : Y.Opens)))
  apply (T'.sectionsEquiv V).injective
  show T'.sectionsEquiv V ((T'.sectionsEquiv V).symm (f.app V (T.sectionsEquiv V
      (T.sheaf.presheaf.map (homOfLE h).op s)))) =
    T'.sectionsEquiv V (T'.sheaf.presheaf.map (homOfLE h).op
      ((T'.sectionsEquiv U).symm (f.app U (T.sectionsEquiv U s))))
  rw [LinearEquiv.apply_symm_apply, T.sectionsEquiv_res, T'.sectionsEquiv_res,
    LinearEquiv.apply_symm_apply, f.naturality]

/-- **The morphism `T̃ ⟶ T̃'` induced by a morphism of systems.** -/
def sheafMap (f : T ⟶ T') : T.sheaf ⟶ T'.sheaf :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis T.sheaf T'.sheaf
    (fun U : Y.affineOpens => (U : Y.Opens)) (sheafMapApp f) isBasis_range_affineOpens
    (sheafMapApp_compatible f)

/-- `sheafMap f` is compatible with `sectionsEquiv`: on an affine open `U` it is `f.app U`. -/
@[simp]
theorem sectionsEquiv_sheafMap_app (f : T ⟶ T') (U : Y.affineOpens) (s : Γ(T.sheaf, U)) :
    T'.sectionsEquiv U ((sheafMap f).app U s) = f.app U (T.sectionsEquiv U s) := by
  have h := Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app T.sheaf T'.sheaf
    (fun U : Y.affineOpens => (U : Y.Opens)) (sheafMapApp f) isBasis_range_affineOpens
    (sheafMapApp_compatible f) U
  show T'.sectionsEquiv U ((sheafMap f).val.app (op (U : Y.Opens)) s) = _
  rw [show (sheafMap f).val.app (op (U : Y.Opens)) = sheafMapApp f U from h]
  show T'.sectionsEquiv U ((T'.sectionsEquiv U).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The components of `sheafMap f` on affine opens. -/
lemma sheafMap_app (f : T ⟶ T') (U : Y.affineOpens) (s : Γ(T.sheaf, U)) :
    (sheafMap f).app U s = (T'.sectionsEquiv U).symm (f.app U (T.sectionsEquiv U s)) := by
  rw [← sectionsEquiv_sheafMap_app, LinearEquiv.symm_apply_apply]

/-- `sheafMap` preserves identities. -/
@[simp]
lemma sheafMap_id : sheafMap (𝟙 T) = 𝟙 T.sheaf :=
  T.sheaf_hom_ext fun U s => by
    rw [sheafMap_app, id_app, LinearEquiv.symm_apply_apply]
    rfl

/-- `sheafMap` preserves composites. -/
@[simp]
lemma sheafMap_comp (f : T ⟶ T') (g : T' ⟶ T'') :
    sheafMap (f ≫ g) = sheafMap f ≫ sheafMap g :=
  T.sheaf_hom_ext fun U s => by
    show _ = (sheafMap g).app U ((sheafMap f).app U s)
    rw [sheafMap_app, sheafMap_app, sheafMap_app, comp_app, LinearEquiv.apply_symm_apply]

variable (Y) in
/-- **The functor `T ↦ T̃`** from affine-local systems on `Y` to `𝒪_Y`-modules. -/
def sheafFunctor : AffineSystem Y ⥤ Y.Modules where
  obj T := T.sheaf
  map f := sheafMap f
  map_id _ := sheafMap_id
  map_comp f g := sheafMap_comp f g

/-- The functor `T ↦ T̃` on objects. -/
@[simp]
lemma sheafFunctor_obj (T : AffineSystem Y) : (sheafFunctor Y).obj T = T.sheaf := rfl

/-- The functor `T ↦ T̃` on morphisms. -/
@[simp]
lemma sheafFunctor_map (f : T ⟶ T') : (sheafFunctor Y).map f = sheafMap f := rfl

/-! ### Exactness -/

variable {T₁ T₂ T₃ : AffineSystem Y}

/-- If `g ∘ f` vanishes on every affine open, then `sheafMap f ≫ sheafMap g = 0`. -/
lemma sheafMap_comp_eq_zero (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
    (hfg : ∀ (U : Y.affineOpens) (x : T₁.obj U), g.app U (f.app U x) = 0) :
    sheafMap f ≫ sheafMap g = 0 :=
  T₁.sheaf_hom_ext fun U s => by
    apply (T₃.sectionsEquiv U).injective
    show T₃.sectionsEquiv U ((sheafMap g).app U ((sheafMap f).app U s)) =
      T₃.sectionsEquiv U 0
    rw [sectionsEquiv_sheafMap_app, sectionsEquiv_sheafMap_app, hfg, map_zero]

/-- If `sheafMap f` kills a section over an affine open `U`, `f` kills its image in `T₁.obj U`. -/
private lemma app_sectionsEquiv_eq_zero (f : T₁ ⟶ T₂) {U : Y.affineOpens} {s : Γ(T₁.sheaf, U)}
    (hs : (sheafMap f).app U s = 0) : f.app U (T₁.sectionsEquiv U s) = 0 := by
  rw [← sectionsEquiv_sheafMap_app, hs, map_zero]

/-- A section of `T̃₂` over an affine open `U` which is the image of `x` under `f.app U` is in the
image of `sheafMap f`. -/
private lemma exists_sheafMap_app_eq (f : T₁ ⟶ T₂) {U : Y.affineOpens} {s : Γ(T₂.sheaf, U)}
    {x : T₁.obj U} (hx : f.app U x = T₂.sectionsEquiv U s) : ∃ t, (sheafMap f).app U t = s :=
  ⟨(T₁.sectionsEquiv U).symm x, (T₂.sectionsEquiv U).injective <| by
    rw [sectionsEquiv_sheafMap_app, LinearEquiv.apply_symm_apply, hx]⟩

/-- **Exactness.** If `T₁ ⟶ T₂ ⟶ T₃` is exact on every affine open, then
`T̃₁ ⟶ T̃₂ ⟶ T̃₃` is an exact sequence of `𝒪_Y`-modules. -/
theorem exact_sheafMap (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
    (hfg : ∀ U : Y.affineOpens, Function.Exact (f.app U) (g.app U)) :
    (ShortComplex.mk (sheafMap f) (sheafMap g)
      (sheafMap_comp_eq_zero f g fun U => (hfg U).apply_apply_eq_zero)).Exact := by
  refine exact_of_exact_sections _ _ _ fun U s hs => ?_
  obtain ⟨x, hx⟩ := ((hfg U) _).mp (app_sectionsEquiv_eq_zero g hs)
  exact exists_sheafMap_app_eq f hx

/-- If `f` is injective on every affine open, `T̃₁ ⟶ T̃₂` is a monomorphism. -/
theorem mono_sheafMap (f : T₁ ⟶ T₂) (hf : ∀ U : Y.affineOpens, Function.Injective (f.app U)) :
    Mono (sheafMap f) := by
  refine (ShortComplex.exact_iff_mono (S := ShortComplex.mk (0 : T₁.sheaf ⟶ T₁.sheaf)
    (sheafMap f) Limits.zero_comp) rfl).mp (exact_of_exact_sections _ _ _ fun U s hs => ⟨0, ?_⟩)
  rw [(T₁.sectionsEquiv U).map_eq_zero_iff.mp
    ((hf U).eq_iff' (map_zero _) |>.mp (app_sectionsEquiv_eq_zero f hs))]
  rfl

/-- If `g` is surjective on every affine open, `T̃₂ ⟶ T̃₃` is an epimorphism. -/
theorem epi_sheafMap (g : T₂ ⟶ T₃) (hg : ∀ U : Y.affineOpens, Function.Surjective (g.app U)) :
    Epi (sheafMap g) := by
  refine (ShortComplex.exact_iff_epi (S := ShortComplex.mk (sheafMap g)
    (0 : T₃.sheaf ⟶ T₃.sheaf) Limits.comp_zero) rfl).mp
    (exact_of_exact_sections _ _ _ fun U s _ => ?_)
  obtain ⟨x, hx⟩ := hg U (T₃.sectionsEquiv U s)
  exact exists_sheafMap_app_eq g hx

/-- **Short exact sequences.** A sequence of systems `0 → T₁ → T₂ → T₃ → 0` which is short exact
on every affine open gives a short exact sequence `0 → T̃₁ → T̃₂ → T̃₃ → 0` of `𝒪_Y`-modules. -/
theorem shortExact_sheafMap (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
    (hf : ∀ U : Y.affineOpens, Function.Injective (f.app U))
    (hfg : ∀ U : Y.affineOpens, Function.Exact (f.app U) (g.app U))
    (hg : ∀ U : Y.affineOpens, Function.Surjective (g.app U)) :
    (ShortComplex.mk (sheafMap f) (sheafMap g)
      (sheafMap_comp_eq_zero f g fun U => (hfg U).apply_apply_eq_zero)).ShortExact :=
  ShortComplex.ShortExact.mk' (exact_sheafMap f g hfg) (mono_sheafMap f hf) (epi_sheafMap g hg)

/-! ### Support -/

/-- **Support.** If for every affine open `U` the support of `T.obj U` in `Spec Γ(Y, U)` lies over
`Z ∩ U` under `Spec Γ(Y, U) ≅ U`, then the support of `T̃` is contained in `Z`. -/
theorem supp_sheaf_subset (T : AffineSystem Y) {Z : Set Y}
    (hZ : ∀ U : Y.affineOpens, Module.support Γ(Y, U) (T.obj U) ⊆ U.2.fromSpec ⁻¹' Z) :
    SheafOfModules.supp T.sheaf ⊆ Z := by
  rintro y ⟨m, hm⟩
  by_contra hyZ
  apply hm
  obtain ⟨W, hyW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq T.sheaf.presheaf m
  obtain ⟨U, hU, hyU, hUW⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hyW
  let U' : Y.affineOpens := ⟨U, hU⟩
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hUW) y hyU s]
  set s' := T.sheaf.presheaf.map (homOfLE hUW).op s
  have hfrom : hU.fromSpec (hU.primeIdealOf ⟨y, hyU⟩) = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have hp : hU.primeIdealOf ⟨y, hyU⟩ ∉ Module.support Γ(Y, U) (T.obj U') := fun hp =>
    hyZ (hfrom ▸ hZ U' hp)
  obtain ⟨a, ha, hax⟩ := Module.notMem_support_iff'.mp hp (T.sectionsEquiv U' s')
  have hya : y ∈ Y.basicOpen a := by
    have : hU.primeIdealOf ⟨y, hyU⟩ ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen a := by
      rwa [hU.fromSpec_preimage_basicOpen]
    rwa [← hfrom]
  let V : Y.affineOpens := ⟨Y.basicOpen a, hU.basicOpen a⟩
  have hres : T.sheaf.presheaf.map (homOfLE (Y.basicOpen_le a)).op s' = 0 := by
    apply (T.sectionsEquiv V).injective
    rw [map_zero, T.sectionsEquiv_res (U := U') (V := V) (Y.basicOpen_le a)]
    have h1 := congrArg (T.map (U := U') (V := V) (Y.basicOpen_le a)) hax
    rw [LinearMap.map_smulₛₗ, map_zero] at h1
    have hu : IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le a)).op).hom a) :=
      Y.toRingedSpace.isUnit_res_basicOpen a
    exact hu.smul_eq_zero.mp h1
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (Y.basicOpen_le a)) y hya s', hres, map_zero]
  rfl

/-! ### Recovering a quasi-coherent module from its affine sections -/

/-- **The affine-local system of a quasi-coherent module.** The sections of a quasi-coherent
`𝒪_Y`-module over the affine opens, with its restriction maps, form an affine-local system: the
base change condition is `Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_restrictₗ`
(Stacks 01I9). -/
def ofQuasicoherent (F : Y.Modules) [F.IsQuasicoherent] : AffineSystem Y where
  obj U := ModuleCat.of Γ(Y, U) Γ(F, U)
  map h :=
    { toFun := F.presheaf.map (homOfLE h).op
      map_add' := map_add _
      map_smul' := F.map_smul (homOfLE h) }
  map_id U x := by
    change F.presheaf.map (𝟙 (op (U : Y.Opens))) x = x
    rw [F.presheaf.map_id]
    rfl
  map_comp h₁ h₂ x := res_comp F (homOfLE h₂) (homOfLE h₁) (homOfLE (h₂.trans h₁)) x
  isBaseChange {U V} h := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isBaseChange_restrictₗ
    F V.2 U.2 h

/-- The modules of `ofQuasicoherent F` are the sections of `F`. -/
@[simp]
lemma ofQuasicoherent_obj (F : Y.Modules) [F.IsQuasicoherent] (U : Y.affineOpens) :
    (ofQuasicoherent F).obj U = ModuleCat.of Γ(Y, U) Γ(F, U) := rfl

/-- The restriction maps of `ofQuasicoherent F` are those of `F`. -/
lemma ofQuasicoherent_map (F : Y.Modules) [F.IsQuasicoherent] {U V : Y.affineOpens}
    (h : (V : Y.Opens) ≤ U) (x : Γ(F, U)) :
    (ofQuasicoherent F).map h x = F.presheaf.map (homOfLE h).op x := rfl

/-- **Recovery.** The sheaf attached to the affine-local system of a quasi-coherent module `F`
is isomorphic to `F`. -/
def ofQuasicoherentIso (F : Y.Modules) [F.IsQuasicoherent] : (ofQuasicoherent F).sheaf ≅ F :=
  Stacks.BasisRestriction.moduleSheafIsoOfSectionIsoOnBasis (𝒪 := Y.ringCatSheaf)
    (ofQuasicoherent F).sheaf F (fun U : Y.affineOpens => (U : Y.Opens))
    (fun U => ((ofQuasicoherent F).sectionsEquiv U).toModuleIso) isBasis_range_affineOpens
    (by
      intro U V (h : (V : Y.Opens) ≤ U) (s : Γ((ofQuasicoherent F).sheaf, (U : Y.Opens)))
      exact (ofQuasicoherent F).sectionsEquiv_res h s)

/-- On an affine open `U`, the recovery isomorphism is `sectionsEquiv`. -/
lemma ofQuasicoherentIso_hom_app (F : Y.Modules) [F.IsQuasicoherent] (U : Y.affineOpens)
    (s : Γ((ofQuasicoherent F).sheaf, U)) :
    (ofQuasicoherentIso F).hom.app U s = (ofQuasicoherent F).sectionsEquiv U s := by
  show (ofQuasicoherentIso F).hom.val.app (op (U : Y.Opens)) s = _
  rw [show (ofQuasicoherentIso F).hom.val.app (op (U : Y.Opens)) = _ from
    Stacks.BasisRestriction.moduleSheafIsoOfSectionIsoOnBasis_hom_app (𝒪 := Y.ringCatSheaf)
      (ofQuasicoherent F).sheaf F (fun U : Y.affineOpens => (U : Y.Opens))
      (fun U => ((ofQuasicoherent F).sectionsEquiv U).toModuleIso) isBasis_range_affineOpens _ U]
  rfl

end AffineSystem

end Stacks.Modules
