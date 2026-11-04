module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackCanonical

/-!
# Restricting a morphism of pullbacks to a smaller open

Let `M` and `N` be sheaves of modules on a scheme `X` and let `Z ≤ W` be opens of `X`.  A
morphism of the restrictions of `M` and `N` to `W` restricts to a morphism of the restrictions
to `Z`.  This file constructs that restriction, computes its action on sections, and records the
composition law for the corresponding operation on morphisms of pullbacks,
`Stacks.AlgebraicGeometry.ModuleLimits.canStep`.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomLE`: the restriction to `Z` of a morphism of
  the restrictions of `M` and `N` to `W`, for `Z ≤ W`.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomLEComp`: the same operation written through
  the composition and congruence isomorphisms of
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor` rather than through the action on sections.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp_canStep` and
  `Stacks.AlgebraicGeometry.ModuleLimits.eq_canStep_of_canHom_comp`: the canonical comparison
  carries the pullback of a morphism to the morphism `canStep` produces, and that property
  determines it.
* `Stacks.AlgebraicGeometry.ModuleLimits.canStep_canStep`: **the composition law.**  Carrying a
  morphism between pullbacks along two successive morphisms is carrying it along the composite.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomSection_restrictHomLE`: `restrictHomLE` acts
  on the sections over an open contained in `Z` exactly as the given morphism does.  This is the
  characterising property, and it is what makes `restrictHomLE` usable as the agreement
  condition of a glueing.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomLE_eq_restrictHomLEComp`: **the
  sections-versus-composition bridge.**  The operation defined by its action on sections is the
  conjugate, by the composition and congruence isomorphisms of `restrictFunctor`, of the
  restriction of the morphism along `AlgebraicGeometry.Scheme.homOfLE`.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomSection_eq_app`: the action on sections,
  computed at an arbitrary open of `W` whose image is the given open, rather than only at
  `W.ι ⁻¹ᵁ U`.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_restrictHomLE`: glueing
  of a morphism of sheaves of modules out of morphisms of its restrictions, with the agreement
  condition stated as an equality of restrictions to the overlaps rather than sectionwise, and
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_restrictFunctor_map_eq_of_restrictHomLEComp`:
  the same with the agreement condition in the composition spelling.

## Implementation notes

`restrictHomLE` is built from `Stacks.AlgebraicGeometry.ModuleLimits.homOfSections`, that is,
from its action on sections, which is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomSection`; the three hypotheses of
`homOfSections` are the three basic properties of `restrictHomSection`.  Building it this way
rather than from the pseudofunctoriality of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is what makes
`restrictHomSection_restrictHomLE` a one-line consequence of `restrictHomSection_res`: the
action on sections is the definition.

The sections of `AlgebraicGeometry.Scheme.Modules.restrict M Z.ι` over an open `U` of `Z` are
the sections of `M` over `Z.ι ''ᵁ U`, and that identification is never left implicit: it goes
through `AlgebraicGeometry.Scheme.Modules.restrictAppIso`, as elsewhere in this directory.

Comparing the two presentations of the restriction operation is the one place where that
identification has to be crossed, and the order of the steps is what makes it go through.  The
composite is split into its factors *first* — `AlgebraicGeometry.Scheme.Modules.Hom.comp_app`
and then `CategoryTheory.ConcreteCategory.comp_apply` — and the factors are rewritten only
afterwards; rewriting a factor first retypes it, after which the split no longer applies because
`Γ(M.restrict Z.ι, V)` and `Γ(M, Z.ι ''ᵁ V)` are equal only by `rfl` and not syntactically, so
the composite is no longer type-correct at the transparency `simp` and `rw` work at.  For the
same reason the comparison of the two spellings is run at the level of morphisms
(`restrictHomLEComp_app`) and only then read on a section
(`restrictHomLEComp_app_apply`), and the two congruence factors are collapsed against the two
composition factors by `presheaf_map_eq_presheaf_map`, which is available because a morphism of
`TopologicalSpace.Opens X` between fixed opens is unique.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### The composition law for `canStep` -/

/-- **The characterising property of `Stacks.AlgebraicGeometry.ModuleLimits.canStep`.**  The
canonical comparison carries the pullback of a morphism along `m` to the morphism obtained from
it by `canStep`. -/
theorem canHom_comp_canStep {Zk Zj Zi : Scheme.{u}} (m : Zk ⟶ Zj) (g : Zj ⟶ Zi) (mg : Zk ⟶ Zi)
    (hmg : m ≫ g = mg) {F G : Zi.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G) :
    canHom m g mg hmg F ≫ canStep m g mg hmg ψ
      = (Scheme.Modules.pullback m).map ψ ≫ canHom m g mg hmg G := by
  rw [canStep, ← canIso_hom m g mg hmg F, Iso.hom_inv_id_assoc, canIso_hom]

/-- A morphism between pullbacks along `mg` that the canonical comparison carries the pullback
of `ψ` along `m` to is `canStep m g mg hmg ψ`. -/
theorem eq_canStep_of_canHom_comp {Zk Zj Zi : Scheme.{u}} (m : Zk ⟶ Zj) (g : Zj ⟶ Zi)
    (mg : Zk ⟶ Zi) (hmg : m ≫ g = mg) {F G : Zi.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (θ : (Scheme.Modules.pullback mg).obj F ⟶ (Scheme.Modules.pullback mg).obj G)
    (h : canHom m g mg hmg F ≫ θ = (Scheme.Modules.pullback m).map ψ ≫ canHom m g mg hmg G) :
    θ = canStep m g mg hmg ψ := by
  rw [← cancel_epi (canHom m g mg hmg F), h, canHom_comp_canStep]

/-- **The composition law for `Stacks.AlgebraicGeometry.ModuleLimits.canStep`.**  Carrying a
morphism between pullbacks along `g` first along `u` and then along `v` is carrying it along the
composite `v ≫ u`.  The three composites are taken as variables together with their equations so
that both sides can be stated with named morphisms. -/
theorem canStep_canStep {T₃ T₂ T₁ Y : Scheme.{u}} (v : T₃ ⟶ T₂) (u : T₂ ⟶ T₁) (g : T₁ ⟶ Y)
    (vu : T₃ ⟶ T₁) (ug : T₂ ⟶ Y) (vug : T₃ ⟶ Y) (hvu : v ≫ u = vu) (hug : u ≫ g = ug)
    (hvug : v ≫ ug = vug) (hvu' : vu ≫ g = vug) {F G : Y.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G) :
    canStep v ug vug hvug (canStep u g ug hug ψ) = canStep vu g vug hvu' ψ := by
  refine eq_canStep_of_canHom_comp vu g vug hvu' ψ _ ?_
  rw [← cancel_epi (canHom v u vu hvu ((Scheme.Modules.pullback g).obj F)),
    ← reassoc_of% (canHom_comp v u g vu ug vug hvu hug hvu' hvug F),
    canHom_comp_canStep v ug vug hvug, ← Functor.map_comp_assoc,
    canHom_comp_canStep u g ug hug ψ, Functor.map_comp, Category.assoc,
    canHom_comp v u g vu ug vug hvu hug hvu' hvug G,
    canHom_naturality_assoc v u vu hvu ψ]

section

variable {X : Scheme.{u}} {M N : X.Modules}

/-! ### Restriction of a morphism of restrictions to a smaller open -/

/-- The restriction to `Z` of a morphism between the restrictions of `M` and `N` to `W`, for
`Z ≤ W`.  It is the morphism acting on the sections over an open contained in `Z` as the given
morphism does. -/
noncomputable def restrictHomLE {W Z : X.Opens} (h : Z ≤ W)
    (η : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι) :
    Scheme.Modules.restrict M Z.ι ⟶ Scheme.Modules.restrict N Z.ι :=
  homOfSections
    (fun U m => (N.restrictAppIso Z.ι U).inv
      (restrictHomSection η ((image_ι_le U).trans h) ((M.restrictAppIso Z.ι U).hom m)))
    (fun U m m' => by
      simp only [map_add, restrictHomSection_add])
    (fun U r m => by
      simp only [Scheme.Modules.smul_restrictAppIso_hom_apply, restrictHomSection_smul,
        Scheme.Modules.smul_restrictAppIso_inv_apply, Iso.inv_hom_id_apply])
    (fun U V hUV m => by
      simp only [Scheme.Modules.map_restrictAppIso_hom_apply,
        restrictHomSection_res η (Scheme.Hom.image_mono Z.ι hUV) ((image_ι_le V).trans h),
        Scheme.Modules.restrictAppIso_inv_map_apply])

/-- **The characterising property of `restrictHomLE`.**  The restriction to `Z` of a morphism of
the restrictions to `W` acts on the sections over an open contained in `Z` exactly as the given
morphism does. -/
theorem restrictHomSection_restrictHomLE {W Z : X.Opens} (h : Z ≤ W)
    (η : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι) {U : X.Opens}
    (hU : U ≤ Z) (m : Γ(M, U)) :
    restrictHomSection (restrictHomLE h η) hU m = restrictHomSection η (hU.trans h) m := by
  rw [restrictHomSection, restrictHomLE, homOfSections_app]
  simp only [Iso.inv_hom_id_apply]
  rw [restrictHomSection_res η (image_preimage_of_le hU).le (hU.trans h),
    presheaf_map_homOfLE_comp]
  simp

/-! ### The restriction of a morphism of restrictions, in the composition spelling -/

/-- Restricting a section along the inclusion of an open into itself does nothing. -/
theorem presheaf_map_homOfLE_self {Y : TopCat.{u}} (P : TopCat.Presheaf Ab.{u} Y)
    {U : Opens Y} (h : U ≤ U) (s : P.obj (op U)) : P.map (homOfLE h).op s = s := by
  simp

/-- Any two restriction maps of a sheaf of modules between the same pair of opens agree: a
morphism of `TopologicalSpace.Opens X` between fixed opens is unique. -/
theorem presheaf_map_eq_presheaf_map (M : X.Modules) {U V : X.Opensᵒᵖ} (f g : U ⟶ V) :
    M.presheaf.map f = M.presheaf.map g := by
  congr 1
  exact Subsingleton.elim f g

/-- `AlgebraicGeometry.Scheme.Modules.restrictAppIso` is the identity: a section of the
restriction of `M` along an open immersion `f` over `V` *is* a section of `M` over `f ''ᵁ V`.
The isomorphism is `Iso.refl`, but that is not visible to `rw` or `simp`, and this is the form
in which the identification is removed. -/
theorem restrictAppIso_hom_apply {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : Y.Opens) (y : Γ(Scheme.Modules.restrict M f, V)) :
    (M.restrictAppIso f V).hom y = y := rfl

/-- `restrictAppIso_hom_apply` for the inverse. -/
theorem restrictAppIso_inv_apply {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : Y.Opens) (x : Γ(M, f ''ᵁ V)) :
    (M.restrictAppIso f V).inv x = x := rfl

/-- **The restriction of a morphism along an open immersion, on sections.**  The restriction of
`φ` along `f` acts on the sections over an open `V` of the source as `φ` acts on the sections
over `f ''ᵁ V`.  This is the morphism-level form of
`Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctor_map_app_apply`, and holds for an arbitrary
open immersion rather than only for the inclusion of an open. -/
theorem restrictFunctor_map_app {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    {A B : Z.Modules} (φ : A ⟶ B) (V : Y.Opens) :
    ((Scheme.Modules.restrictFunctor f).map φ).app V = φ.app (f ''ᵁ V) := rfl

/-- **The action on sections of a morphism of restrictions, computed at an arbitrary open of `W`
lying over `U`.**  For `U ≤ W`, the open `W.ι ⁻¹ᵁ U` used in the definition of
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomSection` may be replaced by any open `B` of `W`
whose image is `U`; the two restriction maps are then the ones belonging to the equality of
opens.  `restrictHomSection_image` is the case `U = W.ι ''ᵁ B`. -/
theorem restrictHomSection_eq_app {W : X.Opens}
    (η : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (B : W.toScheme.Opens) {U : X.Opens} (hU : U ≤ W) (hB : W.ι ''ᵁ B = U) (m : Γ(M, U)) :
    restrictHomSection η hU m
      = N.presheaf.map (homOfLE hB.ge).op (η.app B (M.presheaf.map (homOfLE hB.le).op m)) := by
  have key := presheaf_map_restrictHomSection η hU B hB.le m
  rw [restrictAppIso_inv_apply, restrictAppIso_hom_apply] at key
  rw [← key, presheaf_map_homOfLE_comp, presheaf_map_homOfLE_self]

/-- The image in `X` of an open of `Z` does not change when it is read through an intermediate
open subscheme `W` containing `Z`. -/
theorem image_homOfLE_image {W Z : X.Opens} (h : Z ≤ W) (V : Z.toScheme.Opens) :
    W.ι ''ᵁ (X.homOfLE h ''ᵁ V) = Z.ι ''ᵁ V := by
  simp only [← Scheme.Hom.comp_image, Scheme.homOfLE_ι]

/-- The restriction to `Z` of a morphism of the restrictions of `M` and `N` to `W`, for `Z ≤ W`,
written through the composition and congruence isomorphisms of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` instead of through its action on sections.
`restrictHomLE_eq_restrictHomLEComp` identifies it with
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomLE`. -/
noncomputable def restrictHomLEComp {W Z : X.Opens} (h : Z ≤ W)
    (η : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι) :
    Scheme.Modules.restrict M Z.ι ⟶ Scheme.Modules.restrict N Z.ι :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).inv.app M ≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) W.ι).hom.app M ≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).map η ≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) W.ι).inv.app N ≫
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).hom.app N

/-- **`restrictHomLEComp` on the sections over an open of `Z`.**  The two congruence factors and
the two composition factors collapse to the restriction maps of the equality of opens
`image_homOfLE_image`, leaving the action of `η` over the image of the open in `W`. -/
theorem restrictHomLEComp_app {W Z : X.Opens} (h : Z ≤ W)
    (η : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (V : Z.toScheme.Opens) :
    (restrictHomLEComp h η).app V
      = M.presheaf.map (homOfLE (image_homOfLE_image h V).le).op ≫
          η.app (X.homOfLE h ''ᵁ V) ≫
          N.presheaf.map (homOfLE (image_homOfLE_image h V).ge).op := by
  have e₁ : W.ι ''ᵁ (X.homOfLE h ''ᵁ V) = (X.homOfLE h ≫ W.ι) ''ᵁ V :=
    (Scheme.Hom.comp_image (X.homOfLE h) W.ι V).symm
  have e₂ : (X.homOfLE h ≫ W.ι) ''ᵁ V = Z.ι ''ᵁ V := by
    simp only [Scheme.homOfLE_ι]
  have hsplit : (restrictHomLEComp h η).app V
      = M.presheaf.map (eqToHom e₂).op ≫ M.presheaf.map (eqToHom e₁).op ≫
          η.app (X.homOfLE h ''ᵁ V) ≫ N.presheaf.map (eqToHom e₁.symm).op ≫
          N.presheaf.map (eqToHom e₂.symm).op := by
    rw [restrictHomLEComp]
    simp only [Scheme.Modules.Hom.comp_app]
    simp only [Scheme.Modules.restrictFunctorCongr_inv_app_app,
      Scheme.Modules.restrictFunctorCongr_hom_app_app,
      Scheme.Modules.restrictFunctorComp_hom_app_app,
      Scheme.Modules.restrictFunctorComp_inv_app_app, restrictFunctor_map_app]
    rfl
  rw [hsplit, ← Functor.map_comp_assoc]
  erw [← Functor.map_comp]
  rfl

/-- `restrictHomLEComp_app` on a section. -/
theorem restrictHomLEComp_app_apply {W Z : X.Opens} (h : Z ≤ W)
    (η : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    (V : Z.toScheme.Opens) (x : Γ(M, Z.ι ''ᵁ V)) :
    (restrictHomLEComp h η).app V x
      = N.presheaf.map (homOfLE (image_homOfLE_image h V).ge).op
          (η.app (X.homOfLE h ''ᵁ V)
            (M.presheaf.map (homOfLE (image_homOfLE_image h V).le).op x)) :=
  ConcreteCategory.congr_hom (restrictHomLEComp_app h η V) x

/-- **The sections-versus-composition bridge.**  The restriction to `Z` of a morphism of the
restrictions to `W`, defined by its action on sections, is the conjugate of the restriction of
that morphism along `X.homOfLE h` by the composition and congruence isomorphisms of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`.

This is what lets the agreement condition of
`exists_restrictFunctor_map_eq_of_restrictHomLE` be supplied by data presented through those
isomorphisms rather than sectionwise. -/
theorem restrictHomLE_eq_restrictHomLEComp {W Z : X.Opens} (h : Z ≤ W)
    (η : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι) :
    restrictHomLE h η = restrictHomLEComp h η := by
  refine restrictFunctor_map_eq_of_restrictHomSection fun U hU m => ?_
  have hZU : Z.ι ''ᵁ (Z.ι ⁻¹ᵁ U) = U := image_preimage_of_le hU
  have hB : W.ι ''ᵁ (X.homOfLE h ''ᵁ (Z.ι ⁻¹ᵁ U)) = U :=
    (image_homOfLE_image h (Z.ι ⁻¹ᵁ U)).trans hZU
  rw [restrictHomSection_restrictHomLE h η hU,
    restrictHomSection_eq_app η (X.homOfLE h ''ᵁ (Z.ι ⁻¹ᵁ U)) (hU.trans h) hB m,
    restrictHomSection_eq_app _ (Z.ι ⁻¹ᵁ U) hU hZU m,
    restrictHomLEComp_app_apply h η (Z.ι ⁻¹ᵁ U), presheaf_map_homOfLE_comp]
  exact (presheaf_map_homOfLE_comp N.presheaf _ _ _).symm

/-- Two morphisms of the restrictions of `M` and `N` to opens `W₁` and `W₂` act in the same way
on the sections over an open contained in both as soon as their restrictions to a common open
containing the intersection do. -/
theorem restrictHomSection_eq_of_restrictHomLE_eq {W₁ W₂ Z : X.Opens} (h₁ : Z ≤ W₁)
    (h₂ : Z ≤ W₂) {η₁ : Scheme.Modules.restrict M W₁.ι ⟶ Scheme.Modules.restrict N W₁.ι}
    {η₂ : Scheme.Modules.restrict M W₂.ι ⟶ Scheme.Modules.restrict N W₂.ι}
    (h : restrictHomLE h₁ η₁ = restrictHomLE h₂ η₂) {U : X.Opens} (hU₁ : U ≤ W₁) (hU₂ : U ≤ W₂)
    (hUZ : U ≤ Z) (m : Γ(M, U)) :
    restrictHomSection η₁ hU₁ m = restrictHomSection η₂ hU₂ m := by
  rw [← restrictHomSection_restrictHomLE h₁ η₁ hUZ, h,
    restrictHomSection_restrictHomLE h₂ η₂ hUZ]

/-- **Glueing of a morphism of sheaves of modules out of morphisms of its restrictions**, with
the agreement condition stated as an equality of the restrictions to the overlaps.  The overlap
of two members of the covering is allowed to be enlarged to any open containing it and contained
in both members, which is what lets a consumer use an open presented in whatever form the rest
of its argument produced. -/
theorem exists_restrictFunctor_map_eq_of_restrictHomLE {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ x : X, ∃ a, x ∈ W a)
    (η : ∀ a, Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι)
    (Z : ι → ι → X.Opens) (hZ₁ : ∀ a b, Z a b ≤ W a) (hZ₂ : ∀ a b, Z a b ≤ W b)
    (hZ : ∀ a b, W a ⊓ W b ≤ Z a b)
    (hagree : ∀ a b, restrictHomLE (hZ₁ a b) (η a) = restrictHomLE (hZ₂ a b) (η b)) :
    ∃ φ : M ⟶ N, ∀ a, (Scheme.Modules.restrictFunctor (W a).ι).map φ = η a :=
  exists_restrictFunctor_map_eq_of_cover W hW η fun a b _U ha hb m =>
    restrictHomSection_eq_of_restrictHomLE_eq (hZ₁ a b) (hZ₂ a b) (hagree a b) ha hb
      ((le_inf ha hb).trans (hZ a b)) m

/-- `exists_restrictFunctor_map_eq_of_restrictHomLE` with the agreement condition stated through
the composition and congruence isomorphisms of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, which is the presentation a consumer working
with pullbacks along the inclusions of the opens produces.  The two forms of the hypothesis are
interchangeable by `restrictHomLE_eq_restrictHomLEComp`. -/
theorem exists_restrictFunctor_map_eq_of_restrictHomLEComp {ι : Type u} (W : ι → X.Opens)
    (hW : ∀ x : X, ∃ a, x ∈ W a)
    (η : ∀ a, Scheme.Modules.restrict M (W a).ι ⟶ Scheme.Modules.restrict N (W a).ι)
    (Z : ι → ι → X.Opens) (hZ₁ : ∀ a b, Z a b ≤ W a) (hZ₂ : ∀ a b, Z a b ≤ W b)
    (hZ : ∀ a b, W a ⊓ W b ≤ Z a b)
    (hagree : ∀ a b, restrictHomLEComp (hZ₁ a b) (η a) = restrictHomLEComp (hZ₂ a b) (η b)) :
    ∃ φ : M ⟶ N, ∀ a, (Scheme.Modules.restrictFunctor (W a).ι).map φ = η a :=
  exists_restrictFunctor_map_eq_of_restrictHomLE W hW η Z hZ₁ hZ₂ hZ fun a b =>
    (restrictHomLE_eq_restrictHomLEComp (hZ₁ a b) (η a)).trans
      ((hagree a b).trans (restrictHomLE_eq_restrictHomLEComp (hZ₂ a b) (η b)).symm)

end

end Stacks.AlgebraicGeometry.ModuleLimits

end
