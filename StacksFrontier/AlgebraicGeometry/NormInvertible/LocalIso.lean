module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Cocycle

/-!
# Invertibility of a morphism of sheaves of modules is local on a ringed space

A morphism `φ : M ⟶ N` of sheaves of `𝒪_X`-modules on a ringed space is an isomorphism as soon
as it is bijective on sections over every open contained in some member of a covering family.
This is the gluing criterion behind every "it is enough to check this locally" step of the
invertible-module calculus: a construction carried out in local charts produces a morphism whose
bijectivity is visible only on the charts, and this file turns that into a global isomorphism.

## Main definitions

* `Stacks.SheafOfModules.isoOfBijective`: a morphism of sheaves of modules which is bijective on
  sections over every open is an isomorphism, with the inverse given sectionwise.

## Main results

* `Stacks.SheafOfModules.section_eq_of_locally_eq` and
  `Stacks.SheafOfModules.existsUnique_glue`: the sheaf condition of a sheaf of modules in the
  unique-gluing form, for a covering family of an arbitrary open.
* `Stacks.SheafOfModules.bijective_app_of_le_cover`: **bijectivity on sections is local** — if
  `φ` is bijective on sections over every open inside a member of a covering family, then it is
  bijective on sections over every open.
* `Stacks.SheafOfModules.isIso_of_bijective_le_cover` and
  `Stacks.SheafOfModules.isoOfBijectiveLeCover`: the resulting local criterion for invertibility.

## Implementation notes

**Why this is not `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`.** That
theorem is the same mathematics in a spelling that cannot be reached from here: it is stated for
`M N : X.Modules` with `X : Scheme`, and it is proved by comparing stalks through
`Scheme.Modules.restrictStalkNatIso`. The invertible-module calculus lives on a bare
`RingedSpace.{u, u}`, where there is no `Scheme` structure to restrict along and the category
`X.Modules` does not exist, so there is nothing to bridge; the sheaf condition is applied directly
instead. The present statement is also sharper in the direction that matters for a chart
construction — it asks for bijectivity on *sections*, not for invertibility of a restricted
morphism — so no restriction functor is needed either.

The underlying sheaf of abelian groups is written out inline as
`(⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X))` rather than named.
`Stacks.Cohomology.CechSheaf.abSheaf` is already exactly this construction at full generality, so
naming it again here would fork the identifier; and importing it would drag the Čech-complex
development into the invertible-module calculus for a one-line coercion.

`existsUnique_glue` restates compatibility with `homOfLE inf_le_left`/`homOfLE inf_le_right`
rather than with `Opens.infLELeft`/`Opens.infLERight`, which is the spelling the surrounding
files produce; the two are definitionally equal but not syntactically, so Mathlib's
`TopCat.Presheaf.IsCompatible` does not match a hypothesis stated in the local idiom without the
intervening `intro`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}}

/-! ### The sheaf condition in unique-gluing form -/

section

variable (M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))

/-- Restriction of sections of a sheaf of modules is transitive, in applied form. -/
theorem map_map_apply {V W Z : Opens X.carrier} (h : W ≤ V) (k : Z ≤ W)
    (x : M.val.obj (op V)) :
    M.val.map (homOfLE k).op (M.val.map (homOfLE h).op x) =
      M.val.map (homOfLE (k.trans h)).op x := by
  rw [← PresheafOfModules.map_comp_apply]
  exact PresheafOfModules.congr_map_apply M.val (Subsingleton.elim _ _) x

/-- Two sections of a sheaf of modules over an open `W` which agree on a family of opens
covering `W` are equal. -/
theorem section_eq_of_locally_eq {ι : Type u} (V : ι → Opens X.carrier) (W : Opens X.carrier)
    (hle : ∀ i, V i ≤ W) (hcover : W ≤ ⨆ i, V i) (s t : M.val.obj (op W))
    (h : ∀ i, M.val.map (homOfLE (hle i)).op s = M.val.map (homOfLE (hle i)).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq'
    (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X))
    V W (fun i => homOfLE (hle i)) hcover s t h

/-- A family of sections of a sheaf of modules on a covering family of an open `W`, agreeing on
the pairwise intersections, glues uniquely to a section over `W`. -/
theorem existsUnique_glue {ι : Type u} (V : ι → Opens X.carrier) (W : Opens X.carrier)
    (hle : ∀ i, V i ≤ W) (hcover : W ≤ ⨆ i, V i) (sf : ∀ i, M.val.obj (op (V i)))
    (hcompat : ∀ i j, M.val.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (sf i) =
      M.val.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (sf j)) :
    ∃! s : M.val.obj (op W), ∀ i, M.val.map (homOfLE (hle i)).op s = sf i := by
  refine TopCat.Sheaf.existsUnique_gluing'
    (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X))
    V W (fun i => homOfLE (hle i)) hcover sf ?_
  intro i j
  exact hcompat i j

end

/-! ### Bijectivity on sections is local -/

section

variable {M N : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)}

/-- **Bijectivity on sections of a morphism of sheaves of modules is local.** If `φ` is
bijective on sections over every open contained in a member of a covering family, then it is
bijective on sections over every open. -/
theorem bijective_app_of_le_cover (φ : M ⟶ N) {ι : Type u} (U : ι → Opens X.carrier)
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i)
    (h : ∀ (i : ι) (V : Opens X.carrier), V ≤ U i → Function.Bijective (φ.val.app (op V)))
    (W : Opens X.carrier) : Function.Bijective (φ.val.app (op W)) := by
  have hcov : W ≤ ⨆ i, W ⊓ U i := by
    rw [← inf_iSup_eq]
    exact le_inf le_rfl (le_top.trans hU)
  have nat : ∀ {V V' : Opens X.carrier} (k : V' ≤ V) (x : M.val.obj (op V)),
      φ.val.app (op V') (M.val.map (homOfLE k).op x) =
        N.val.map (homOfLE k).op (φ.val.app (op V) x) := fun k x =>
    PresheafOfModules.naturality_apply φ.val (homOfLE k).op x
  constructor
  · intro s t hst
    refine section_eq_of_locally_eq M (fun i => W ⊓ U i) W (fun _ => inf_le_left) hcov s t
      fun i => ?_
    refine (h i (W ⊓ U i) inf_le_right).injective ?_
    rw [nat, nat, hst]
  · intro τ
    choose σ hσ using fun i => (h i (W ⊓ U i) inf_le_right).surjective
      (N.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op τ)
    have hcompat : ∀ i j, M.val.map
          (homOfLE (inf_le_left : (W ⊓ U i) ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op (σ i) =
        M.val.map (homOfLE (inf_le_right : (W ⊓ U i) ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op (σ j) := by
      intro i j
      refine (h i ((W ⊓ U i) ⊓ (W ⊓ U j)) (inf_le_left.trans inf_le_right)).injective ?_
      rw [nat, nat, hσ i, hσ j, map_map_apply N, map_map_apply N]
    obtain ⟨s, hs, -⟩ :=
      existsUnique_glue M (fun i => W ⊓ U i) W (fun _ => inf_le_left) hcov σ hcompat
    refine ⟨s, section_eq_of_locally_eq N (fun i => W ⊓ U i) W (fun _ => inf_le_left) hcov _ _
      fun i => ?_⟩
    rw [← nat, hs i, hσ i]

/-- A morphism of sheaves of modules which is bijective on sections over every open is an
isomorphism, the inverse being the sectionwise inverse. -/
noncomputable def isoOfBijective (φ : M ⟶ N)
    (h : ∀ W : Opens X.carrier, Function.Bijective (φ.val.app (op W))) : M ≅ N :=
  (_root_.SheafOfModules.fullyFaithfulForget (structureSheaf X.sheaf)).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (LinearEquiv.ofBijective (φ.val.app V).hom (h V.unop)).toModuleIso)
      (fun {_ _} f => φ.val.naturality f))

/-- The sections of the forward morphism of `isoOfBijective φ h` are those of `φ`. -/
@[simp]
theorem isoOfBijective_hom_val_app (φ : M ⟶ N)
    (h : ∀ W : Opens X.carrier, Function.Bijective (φ.val.app (op W)))
    (V : (Opens X.carrier)ᵒᵖ) :
    (isoOfBijective φ h).hom.val.app V = φ.val.app V :=
  rfl

/-- A morphism of sheaves of modules which is bijective on sections over every open is an
isomorphism. -/
theorem isIso_of_bijective (φ : M ⟶ N)
    (h : ∀ W : Opens X.carrier, Function.Bijective (φ.val.app (op W))) : IsIso φ := by
  have hhom : (isoOfBijective φ h).hom = φ :=
    _root_.SheafOfModules.Hom.ext (PresheafOfModules.hom_ext (isoOfBijective_hom_val_app φ h))
  rw [← hhom]
  infer_instance

/-- **A morphism of sheaves of modules which is bijective on the sections of a covering family
and all its subopens is an isomorphism.** -/
noncomputable def isoOfBijectiveLeCover (φ : M ⟶ N) {ι : Type u} (U : ι → Opens X.carrier)
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i)
    (h : ∀ (i : ι) (V : Opens X.carrier), V ≤ U i → Function.Bijective (φ.val.app (op V))) :
    M ≅ N :=
  isoOfBijective φ (bijective_app_of_le_cover φ U hU h)

/-- A morphism of sheaves of modules which is bijective on sections over every open contained in a
member of a covering family is an isomorphism. -/
theorem isIso_of_bijective_le_cover (φ : M ⟶ N) {ι : Type u} (U : ι → Opens X.carrier)
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i)
    (h : ∀ (i : ι) (V : Opens X.carrier), V ≤ U i → Function.Bijective (φ.val.app (op V))) :
    IsIso φ :=
  isIso_of_bijective φ (bijective_app_of_le_cover φ U hU h)

end

end Stacks.SheafOfModules
