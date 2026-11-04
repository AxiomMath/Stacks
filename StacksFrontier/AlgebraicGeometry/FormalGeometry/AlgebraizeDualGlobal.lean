module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeDualGlue

/-!
# Algebraizing a map out of a completion, globally

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals on `X`, `G` a
coherent `𝒪_X`-module, `(F_n)` a coherent `ℐ`-adic system and `α : G^∧ ⟶ (F_n)` the datum of
Stacks 0889 part (2). `StacksFrontier/AlgebraicGeometry/FormalGeometry/AlgebraizeDualGlue.lean`
produces the coherent `𝒪_X`-module `M` glued from the local algebraizations over the affine opens
of `X`, together with the overlap comparisons and their two defining identities. This file
produces the morphism-free half of the global statement: the isomorphism `β : M^∧ ≅ (F_n)`,
together with the chart identifications and the overlap comparisons from which the morphism
`a : G ⟶ M` is glued.

## The asymmetry the two pieces are built from

The two defining identities of the overlap comparisons `d` sit at different levels.

* The first, `restrictedAlgebraizationMapOfLE hki (b i) ≫ (d k i j hki hkj).hom =
  restrictedAlgebraizationMapOfLE hkj (b j)`, is an equation between morphisms of **coherent
  modules**. It therefore reads on the sections over an open, and
  `Stacks.Algebraization.localAppOpen_pushforwardChartMap_overlap` is that reading: it is exactly
  the overlap hypothesis of `Stacks.Coherent.existsUnique_hom_of_cover_affineApp`, so `a` glues.
* The second, `((completionFunctor _ _).map (d k i j hki hkj).hom).hom ≫
  (restrictedAlgebraizationIsoOfLE I Fsys hkj (β j)).hom =
  (restrictedAlgebraizationIsoOfLE I Fsys hki (β i)).hom`, is an equation between morphisms of
  **completions**, and cannot be read on sections: `Stacks.Algebraization.epi_completionProjection`
  is an epimorphism of sheaves of modules, not a surjection on the sections over a fixed open.

So the comparison of the two charts over an affine `k ⊆ U i ∩ U j` is made at the sheaf level and
only then carried to sections, by `Stacks.Algebraization.localAppOpen_eq_of_restrictDown_eq`. At
the sheaf level the canonical projection out of the completion of `M|_k` *is* an epimorphism, so
`Stacks.Algebraization.completionSystemHom_ext` applies, and the second identity enters through
`Stacks.Algebraization.completionProjection_comp_restrictedAlgebraizationIsoOfLE` with no
reading of sections anywhere.

The cross-chart compatibility of the glued module is section-level — it is
`Stacks.Modules.OModuleGlueData.trans_chartLinearEquiv` at bottom — and it is lifted to the sheaf
level over `k` by `Stacks.Algebraization.chartIso_comp_overlapComparison`, using the fact that it
holds over *every* affine open inside `k` together with
`Stacks.Algebraization.localAppOpen_overlapRestrictIso_restrict`, which identifies the comparison
over a smaller affine open with the restriction of the one over `k`.

## Main definitions

* `Stacks.Algebraization.pushforwardChartMap` — the morphism of a local algebraization read into
  the direct image of the chart's module, which is the shape in which two charts are compared over
  an open of `X`.

## Main results

* `Stacks.Algebraization.restrictHom_ext_of_localAppOpen` — **a morphism of the restrictions to an
  open is determined by its action on the sections over the opens inside it.** This is the
  uniqueness half of `Stacks.Coherent.exists_restrictHom_of_app`.
* `Stacks.Algebraization.restrictDownIso_hom_naturality` — the comparison of the two routes down
  to a smaller open is natural in the module.
* `Stacks.Algebraization.restrictedAlgebraizationMapOfLE_hom_eq_restrictDown` and
  `Stacks.Algebraization.restrictedAlgebraizationMapOfLE_hom_eq_pushforward` — **the transported
  algebraization morphism is the restriction down of the morphism itself**, in the two shapes the
  two glueings need.
* `Stacks.Algebraization.localAppOpen_pushforwardChartMap_overlap` — **the first defining identity
  of the overlap comparisons, read on the sections over the overlap.**
* `Stacks.Algebraization.exists_gluedHom_of_sectionChart` — **the morphism `G ⟶ M` glued from the
  local algebraizations.**
* `Stacks.Algebraization.chartIso_comp_overlapComparison` — **the cross-chart compatibility of the
  glued module at the sheaf level**, in the shape of the first defining identity of an overlap
  comparison.
* `Stacks.Algebraization.completionProjection_comp_completionRestrictChartIso` and
  `Stacks.Algebraization.restrictDown_completionRestrictChartIso` — **the local comparison of the
  completion of the glued module with the given system, read through the canonical projections**,
  the second of them carried down to an open of the chart.
* `Stacks.Algebraization.completionMapOfLE_comp_restrictedAlgebraizationIsoOfLE_eq` — **the second
  defining identity of the overlap comparisons with the first substituted into it**, at the level
  of systems over the overlap.
* `Stacks.Algebraization.localAppOpen_completionRestrictChartIso_overlap` — **the overlap
  hypothesis of `Stacks.Coherent.existsUnique_coherentSystemIso_of_affineComparison` for the local
  comparisons of the completion of the glued module with the given system.**
* `Stacks.Algebraization.exists_glued_completionIso_of_localAlgebraizations` — **the glued module
  together with an isomorphism of its completion with the given system**, its chart
  identifications and the overlap comparisons intertwining them.
* `Stacks.Algebraization.essImage_of_map_from_completion` — **a coherent adic system receiving a
  map out of a completion with power-annihilated kernel and cokernel is itself a completion.**

## Where the statement is completed

The morphism `a : G ⟶ M`, the factorization `α = β ∘ a^∧`, the annihilation of the kernel and the
cokernel of `a` and the uniqueness clause are proved in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AlgebraizeDualTheorem.lean`, which states Stacks
0889 (2) as `Stacks.Algebraization.exists_unique_algebraization_dual_of_isNoetherian`. The chart
identifications and the overlap comparisons returned by
`Stacks.Algebraization.exists_glued_completionIso_of_localAlgebraizations` are what `a` is glued
from.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and
`AlgebraicGeometry.Scheme.ringCatSheaf` is typed at `TopCat.Sheaf`, itself a `def` for a
`CategoryTheory.Sheaf`. A goal naming a coherent module on `X` is therefore *not* type correct at
the transparency `rw` builds a motive at, and no rewrite fires in it — the error reported is a
mismatch between `TopCat.Sheaf RingCat X` and `Sheaf (Opens.grothendieckTopology X) RingCat`. Two
devices get around this, both used throughout the file: the computation is carried out in a lemma
stated purely in `AlgebraicGeometry.Scheme.Modules` with no coherent module in sight — that is
what `Stacks.Algebraization.restrictedAlgebraizationMapOfLE_hom_eq_pushforwardAux` is for — and
the passage between the two levels is made by `exact` and `congrArg`, which check up to
definitional equality. The same is the reason for the `rfl` lemmas `appComp₂`, `appComp₃` and
`appComp₄` below, and for `Stacks.Algebraization.restrictFunctor_map_app`:
`AlgebraicGeometry.Scheme.Modules.Hom.comp_app` does not match goals of exactly its own shape.

The consolidated list of the frictions of this development is in the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/AlgebraizeDualOverlap.lean`.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.AlgebraicGeometry.ModuleHomGlue

/-! ### Abstract reassociation and action-on-sections helpers -/

section Helpers

variable {C : Type*} [Category C]

/-- The underlying morphism of a composite in a full subcategory. -/
private theorem fullSubcategoryComp_hom {P : ObjectProperty C} {A B D : P.FullSubcategory}
    (f : A ⟶ B) (g : B ⟶ D) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Equal morphisms of a full subcategory have equal underlying morphisms. -/
private theorem fullSubcategoryHom_congr {P : ObjectProperty C} {A B : P.FullSubcategory}
    {f g : A ⟶ B} (h : f = g) : f.hom = g.hom := by rw [h]

/-- Reassociating a composite of four morphisms whose head is a threefold composite. -/
private theorem assocHead₃ {A B D E Z : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ Z) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

/-- An overlap comparison, conjugated by two isomorphisms, against the two factorizations of its
ends. -/
private theorem overlapChain {A B₁ B₂ D₁ D₂ : C} {u : A ⟶ B₁} {e₁ : B₁ ≅ D₁} {w : D₁ ⟶ D₂}
    {e₂ : B₂ ≅ D₂} {v : A ⟶ B₂} {x₁ : A ⟶ D₁} {x₂ : A ⟶ D₂}
    (h₁ : u ≫ e₁.hom = x₁) (h₂ : x₁ ≫ w = x₂) (h₃ : v ≫ e₂.hom = x₂) :
    u ≫ e₁.hom ≫ w ≫ e₂.inv = v := by
  rw [← Category.assoc, ← Category.assoc, h₁, h₂, ← h₃, Category.assoc, e₂.hom_inv_id,
    Category.comp_id]

end Helpers

/-- The action on sections of a composite of two morphisms of sheaves of modules. Stated as a
`rfl` lemma at exactly this shape because
`AlgebraicGeometry.Scheme.Modules.Hom.comp_app` does not match; see the implementation notes. -/
private theorem appComp₂ {Z : Scheme.{u}} {M N P : Z.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (A : Z.Opens) :
    Scheme.Modules.Hom.app (a ≫ b) A =
      Scheme.Modules.Hom.app a A ≫ Scheme.Modules.Hom.app b A := rfl

/-- The action on sections of a threefold composite. -/
private theorem appComp₃ {Z : Scheme.{u}} {M N P Q : Z.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (c : P ⟶ Q) (A : Z.Opens) :
    Scheme.Modules.Hom.app (a ≫ b ≫ c) A =
      Scheme.Modules.Hom.app a A ≫ Scheme.Modules.Hom.app b A ≫
        Scheme.Modules.Hom.app c A := rfl

/-- The action on sections of a fourfold composite. -/
private theorem appComp₄ {Z : Scheme.{u}} {M N P Q R : Z.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (c : P ⟶ Q) (d : Q ⟶ R) (A : Z.Opens) :
    Scheme.Modules.Hom.app (a ≫ b ≫ c ≫ d) A =
      Scheme.Modules.Hom.app a A ≫ Scheme.Modules.Hom.app b A ≫
        Scheme.Modules.Hom.app c A ≫ Scheme.Modules.Hom.app d A := rfl

/-- The inverse of the counit of Mathlib's restriction adjunction acts on the sections over an
open as a restriction map of the presheaf. -/
private theorem restrictCounitInv_app {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsOpenImmersion g]
    (F : Z.Modules) (A : Z.Opens) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorAdjCounitIso g).app F).inv A =
      F.presheaf.map (eqToHom (g.preimage_image_eq A)).op := rfl

/-- A map between the sections of two presheaves, sandwiched between restriction maps on the left
and a round trip of restriction maps on the right, is that map between a single restriction map and
nothing: the category of opens is thin, so the round trip is the identity and the two maps on the
left compose to one. -/
private theorem presheafSandwich_collapse {Z Y : Scheme.{u}} (M : Z.Modules) (N : Y.Modules)
    {P T Q : (Z.Opens)ᵒᵖ} {P' Q' R' : (Y.Opens)ᵒᵖ}
    (a : P ⟶ Q) (a₁ : P ⟶ T) (a₂ : T ⟶ Q) (f₁ : P' ⟶ Q') (f₂ : Q' ⟶ R') (f₃ : R' ⟶ P')
    (D : M.presheaf.obj Q ⟶ N.presheaf.obj P') :
    M.presheaf.map a ≫ (D ≫ N.presheaf.map f₁) ≫ N.presheaf.map f₂ ≫ N.presheaf.map f₃ =
      M.presheaf.map a₁ ≫ M.presheaf.map a₂ ≫ D := by
  have hN : N.presheaf.map f₁ ≫ N.presheaf.map f₂ ≫ N.presheaf.map f₃ = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Subsingleton.elim (f₁ ≫ f₂ ≫ f₃) (𝟙 P')]
    exact N.presheaf.map_id P'
  have hM : M.presheaf.map a₁ ≫ M.presheaf.map a₂ = M.presheaf.map a := by
    rw [← Functor.map_comp, Subsingleton.elim (a₁ ≫ a₂) a]
  simp only [Category.assoc]
  rw [hN, Category.comp_id, ← hM]
  simp only [Category.assoc]

/-! ### A morphism of restrictions is determined by its action on sections -/

/-- **A morphism of the restrictions of two sheaves of modules to an open is determined by its
action on the sections over the opens inside that open.** This is the uniqueness half of
`Stacks.Coherent.exists_restrictHom_of_app`, read for the family that one of the two morphisms
produces: the linearity and the restriction compatibility that the glueing asks of a family are
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_smul` and
`Stacks.Coherent.localAppOpen_map_of_le`, so both morphisms are *the* morphism that family comes
from. -/
public theorem restrictHom_ext_of_localAppOpen {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (ψ ψ' : Scheme.Modules.restrict M U.ι ⟶ Scheme.Modules.restrict N U.ι)
    (h : ∀ (V : X.Opens) (hV : V ≤ U),
      Stacks.Coherent.localAppOpen U ψ hV = Stacks.Coherent.localAppOpen U ψ' hV) :
    ψ = ψ' := by
  obtain ⟨_χ, -, huniq⟩ := Stacks.Coherent.exists_restrictHom_of_app U
    (fun V hV => Stacks.Coherent.localAppOpen U ψ hV)
    (fun _ hV r s => localApp_smul U.ι ψ _ r s)
    (fun _ _ hV hWV s => Stacks.Coherent.localAppOpen_map_of_le U ψ hV hWV s)
  exact (huniq ψ fun _ _ => rfl).trans (huniq ψ' fun V hV => (h V hV).symm).symm

/-- The action on the sections over an open of a morphism of restrictions is linear. This is
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_smul` in the
`Stacks.Coherent.localAppOpen` spelling. -/
public theorem localAppOpen_smul {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules}
    (ψ : Scheme.Modules.restrict M U.ι ⟶ Scheme.Modules.restrict N U.ι) {V : X.Opens}
    (hV : V ≤ U) (r : Γ(X, V)) (s : Γ(M, V)) :
    Stacks.Coherent.localAppOpen U ψ hV (r • s) =
      r • Stacks.Coherent.localAppOpen U ψ hV s :=
  localApp_smul U.ι ψ _ r s

/-! ### The comparison of the two routes down to a smaller open -/

/-- `Stacks.Algebraization.restrictDownIso` is the composite of the two transports of Mathlib.
Definitional; the spelling is what the naturality and the identification with
`Stacks.Algebraization.restrictedAlgebraizationMapOfLE` are stated against. -/
public theorem restrictDownIso_hom_eq {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    (M : X.Modules) :
    (restrictDownIso hWU M).hom =
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).inv.app M ≫
        (Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).hom.app M := rfl

/-- The inverse of `Stacks.Algebraization.restrictDownIso` as the composite of the two transports
of Mathlib, in the order in which
`Stacks.Algebraization.completionProjection_comp_restrictedAlgebraizationIsoOfLE` produces
them. -/
public theorem restrictDownIso_inv_eq {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    (M : X.Modules) :
    (restrictDownIso hWU M).inv =
      (Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).inv.app M ≫
        (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).hom.app M := rfl

/-- **`Stacks.Algebraization.restrictDownIso` is natural in the module.** Both of its factors are
components of natural isomorphisms of Mathlib, so this is their two naturality squares in
series. -/
public theorem restrictDownIso_hom_naturality {X : Scheme.{u}} {U W : X.Opens} (hWU : W ≤ U)
    {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.restrictFunctor W.ι).map φ ≫ (restrictDownIso hWU N).hom =
      (restrictDownIso hWU M).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          ((Scheme.Modules.restrictFunctor U.ι).map φ) := by
  rw [restrictDownIso_hom_eq, restrictDownIso_hom_eq, ← Category.assoc,
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).inv.naturality φ, Category.assoc,
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).hom.naturality φ]
  exact (Category.assoc _ _ _).symm

/-! ### The transported algebraization morphism is a restriction down -/

/-- **The morphism of a local algebraization carried to a smaller open is its restriction down
along `W ⟶ U`.** Both sides are the two transports of the source followed by the restriction of
`b`, the first by definition of `Stacks.Algebraization.restrictDownIso` and the second by
definition of `Stacks.Algebraization.restrictedAlgebraizationMapOfLE` read through
`Stacks.Algebraization.restrictCoherentModulesCongrIso_inv_hom`. -/
public theorem restrictedAlgebraizationMapOfLE_hom_eq_restrictDown {X : Scheme.{u}}
    [IsLocallyNoetherian X] {U W : X.Opens} (hWU : W ≤ U)
    {N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (b : restrictCoherentModules U.ι N ⟶ F) :
    (restrictDownIso hWU N.obj).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map b.hom =
      (restrictedAlgebraizationMapOfLE hWU b).hom := by
  refine Eq.trans (congrArg (fun z => z ≫
      (Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).hom.app N.obj ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map b.hom)
    (restrictCoherentModulesCongrIso_inv_hom (X.homOfLE_ι hWU) N).symm) ?_
  rfl

/-- `Stacks.Algebraization.restrictedAlgebraizationMapOfLE_hom_eq_pushforward` with every coherent
module replaced by its underlying sheaf of modules.

That is what makes it provable: a goal naming
`AlgebraicGeometry.SheafOfModules.CoherentModules` is not type correct at the transparency `rw`
builds a motive at, so no rewrite fires in it — see the implementation notes. Here every factor
acts on the sections over an open as a restriction map of one of the two presheaves, by
`Stacks.Algebraization.restrictDownIso_hom_app`,
`Stacks.Algebraization.restrictDownIso_inv_app`,
`Stacks.Algebraization.restrictCoherentPushforwardCompIso_hom_app` and the `app`-lemmas of
Mathlib's two transports, and what is left is thinness. -/
private theorem restrictedAlgebraizationMapOfLE_hom_eq_pushforwardAux {X : Scheme.{u}}
    {U W : X.Opens} (hWU : W ≤ U) (Nm : X.Modules) (Fm : U.toScheme.Modules)
    (bh : Scheme.Modules.restrict Nm U.ι ⟶ Fm) :
    (restrictDownIso hWU Nm).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          (bh ≫ ((Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app Fm).inv) ≫
          (restrictDownIso hWU ((Scheme.Modules.pushforward U.ι).obj Fm)).inv ≫
            (restrictCoherentPushforwardCompIso (X.homOfLE hWU) U.ι W.ι
              (X.homOfLE_ι hWU) Fm).hom =
      (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hWU)).inv.app Nm ≫
        (Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).hom.app Nm ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map bh := by
  refine Scheme.Modules.hom_ext _ _ fun A => ?_
  rw [appComp₄, appComp₃, restrictDownIso_hom_app hWU Nm A
      (eqToHom (image_comp_eq_of_eq (X.homOfLE hWU) U.ι W.ι (X.homOfLE_ι hWU) A)),
    restrictDownIso_inv_app hWU ((Scheme.Modules.pushforward U.ι).obj Fm) A
      (eqToHom (image_comp_eq_of_eq (X.homOfLE hWU) U.ι W.ι (X.homOfLE_ι hWU) A).symm),
    restrictCoherentPushforwardCompIso_hom_app (X.homOfLE hWU) U.ι W.ι (X.homOfLE_ι hWU) Fm A
      (eqToHom (homOfLE_image_eq_ι_preimage_image hWU A)),
    restrictFunctor_map_app, appComp₂, restrictCounitInv_app,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.pushforward_obj_presheaf_map, restrictFunctor_map_app]
  exact presheafSandwich_collapse Nm Fm _ _ _ _ _ _ _

/-- **The morphism of a local algebraization carried to a smaller open, read into the direct image
of the chart's module.** This is
`Stacks.Algebraization.restrictedAlgebraizationMapOfLE_hom_eq_restrictDown` with the target moved
across the counit of Mathlib's restriction adjunction and the identification
`Stacks.Algebraization.coherentModulesPushforwardRestrictIso` of the sections of a direct image
over a smaller open.

It is in this shape that the first defining identity of an overlap comparison becomes the overlap
hypothesis of a glueing: the two sides of that hypothesis are maps on the sections of the two
*direct images*, which are sheaves of modules on `X`, and only such maps can be compared over one
and the same open of `X`. -/
public theorem restrictedAlgebraizationMapOfLE_hom_eq_pushforward {X : Scheme.{u}}
    [IsLocallyNoetherian X] {U W : X.Opens} (hWU : W ≤ U)
    (N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (b : restrictCoherentModules U.ι N ⟶ F) :
    (restrictDownIso hWU N.obj).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          (b.hom ≫ ((Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app F.obj).inv) ≫
          (restrictDownIso hWU (coherentModulesPushforward U.ι F)).inv ≫
            (coherentModulesPushforwardRestrictIso hWU F).hom =
      (restrictedAlgebraizationMapOfLE hWU b).hom := by
  refine (restrictedAlgebraizationMapOfLE_hom_eq_pushforwardAux hWU N.obj F.obj b.hom).trans ?_
  exact congrArg (fun z => z ≫
      ((Scheme.Modules.restrictFunctorComp (X.homOfLE hWU) U.ι).hom.app N.obj ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map b.hom))
    (restrictCoherentModulesCongrIso_inv_hom (X.homOfLE_ι hWU) N).symm

/-! ### The first defining identity read on the sections over the overlap -/

/-- **The morphism of a local algebraization read into the direct image of the chart's module.**
This is the local datum from which the morphism `G ⟶ M` of Stacks 0889 (2) is glued: its action on
the sections over an open `V ≤ U` is a map between the sections of two sheaves of modules on `X`,
so two charts can be compared over `V` with no transport along an isomorphism of opens. -/
public def pushforwardChartMap {X : Scheme.{u}} [IsLocallyNoetherian X] {U : X.Opens}
    {N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (b : restrictCoherentModules U.ι N ⟶ F) :
    Scheme.Modules.restrict N.obj U.ι ⟶
      Scheme.Modules.restrict (coherentModulesPushforward U.ι F) U.ι :=
  b.hom ≫ ((Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app F.obj).inv

/-- The chart datum read into the direct image, carried down to a smaller open and followed by the
identification of the sections of a direct image, is the transported algebraization morphism. -/
private theorem restrictDown_pushforwardChartMap_comp_hom_eq {X : Scheme.{u}}
    [IsLocallyNoetherian X] {U W : X.Opens} (hWU : W ≤ U)
    (N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (b : restrictCoherentModules U.ι N ⟶ F) :
    ((restrictDownIso hWU N.obj).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map (pushforwardChartMap b) ≫
          (restrictDownIso hWU (coherentModulesPushforward U.ι F)).inv) ≫
        (coherentModulesPushforwardRestrictIso hWU F).hom =
      (restrictedAlgebraizationMapOfLE hWU b).hom :=
  (assocHead₃ _ _ _ _).trans (restrictedAlgebraizationMapOfLE_hom_eq_pushforward hWU N F b)

/-- The overlap comparison of two direct images unfolded into its three factors. -/
private theorem overlapRestrictIso_hom_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U U' W : X.Opens} (hWU : W ≤ U) (hWU' : W ≤ U')
    {M : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    {M' : AlgebraicGeometry.SheafOfModules.CoherentModules U'.toScheme.ringCatSheaf}
    (e : restrictCoherentModules (X.homOfLE hWU) M ≅
      restrictCoherentModules (X.homOfLE hWU') M') :
    (overlapRestrictIso hWU hWU' e).hom =
      (coherentModulesPushforwardRestrictIso hWU M).hom ≫ e.hom.hom ≫
        (coherentModulesPushforwardRestrictIso hWU' M').inv := rfl

/-- **The first defining identity of an overlap comparison, read on the sections over the
overlap.** If the comparison `dk` intertwines the two local algebraization morphisms carried down
to `Wk`, then the two local data `Stacks.Algebraization.pushforwardChartMap` act on the sections
over `Wk` in the same way once one of them is followed by the overlap comparison of the two direct
images.

This is the overlap hypothesis of `Stacks.Coherent.existsUnique_hom_of_cover_affineApp`, and it is
available because the identity being used is an equation between morphisms of *coherent modules*:
`Stacks.Algebraization.localAppOpen_eq_restrictDown` rewrites each side as the action of a
morphism living over `Wk` itself, and
`Stacks.Algebraization.restrictedAlgebraizationMapOfLE_hom_eq_pushforward` identifies that
morphism with the transported algebraization morphism, after which the identity closes the goal at
the sheaf level. -/
public theorem localAppOpen_pushforwardChartMap_overlap {X : Scheme.{u}} [IsLocallyNoetherian X]
    {Ui Uj Wk : X.Opens} (hki : Wk ≤ Ui) (hkj : Wk ≤ Uj)
    {N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {Fi : AlgebraicGeometry.SheafOfModules.CoherentModules Ui.toScheme.ringCatSheaf}
    {Fj : AlgebraicGeometry.SheafOfModules.CoherentModules Uj.toScheme.ringCatSheaf}
    (bi : restrictCoherentModules Ui.ι N ⟶ Fi) (bj : restrictCoherentModules Uj.ι N ⟶ Fj)
    (dk : restrictCoherentModules (X.homOfLE hki) Fi ≅
      restrictCoherentModules (X.homOfLE hkj) Fj)
    (hdk : restrictedAlgebraizationMapOfLE hki bi ≫ dk.hom =
      restrictedAlgebraizationMapOfLE hkj bj) :
    Stacks.Coherent.localAppOpen Ui (pushforwardChartMap bi) hki ≫
        Stacks.Coherent.localAppOpen Wk (overlapRestrictIso hki hkj dk).hom le_rfl =
      Stacks.Coherent.localAppOpen Uj (pushforwardChartMap bj) hkj := by
  refine Eq.trans (congrArg
      (fun z => z ≫
        Stacks.Coherent.localAppOpen Wk (overlapRestrictIso hki hkj dk).hom le_rfl)
      (localAppOpen_eq_restrictDown hki (pushforwardChartMap bi))) ?_
  refine Eq.trans (localAppOpen_comp Wk _ _ le_rfl).symm ?_
  refine Eq.trans (congrArg (fun z => Stacks.Coherent.localAppOpen Wk z le_rfl) ?_)
    (localAppOpen_eq_restrictDown hkj (pushforwardChartMap bj)).symm
  exact overlapChain (e₁ := coherentModulesPushforwardRestrictIso hki Fi) (w := dk.hom.hom)
    (e₂ := coherentModulesPushforwardRestrictIso hkj Fj)
    (restrictDown_pushforwardChartMap_comp_hom_eq hki N Fi bi)
    ((fullSubcategoryComp_hom _ _).symm.trans (fullSubcategoryHom_congr hdk))
    (restrictDown_pushforwardChartMap_comp_hom_eq hkj N Fj bj)

/-! ### Glueing the morphism out of `G` -/

/-- **The morphism `G ⟶ M` of Stacks 0889 (2), glued from the local algebraizations.** Let `M` be
a sheaf of modules whose sections over an open of a chart are identified with those of the direct
image of that chart's module, compatibly with restriction and intertwined by the overlap
comparisons — which is what
`Stacks.Algebraization.exists_glued_of_localAlgebraizations` returns — and let the overlap
comparisons satisfy the first of their two defining identities. Then there is a morphism
`G ⟶ M` acting on the sections over an open of a chart as that chart's algebraization morphism,
read through the identification.

This is `Stacks.Coherent.existsUnique_hom_of_cover_affineApp` for the cover of `X` by all of its
affine opens. Its overlap hypothesis, which is required only over the affine opens contained in
two charts, is `Stacks.Algebraization.localAppOpen_pushforwardChartMap_overlap` composed with the
cross-chart compatibility of the glued module; the linearity and the restriction compatibility are
`Stacks.Algebraization.localAppOpen_smul` and `Stacks.Coherent.localAppOpen_map_of_le` together
with the restriction compatibility of the identifications. -/
public theorem exists_gluedHom_of_sectionChart {X : Scheme.{u}} [IsLocallyNoetherian X]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (M : X.Modules)
    (F : ∀ i : X.affineOpens,
      AlgebraicGeometry.SheafOfModules.CoherentModules i.1.toScheme.ringCatSheaf)
    (b : ∀ i : X.affineOpens, restrictCoherentModules i.1.ι G ⟶ F i)
    (d : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
      restrictCoherentModules (X.homOfLE hki) (F i) ≅
        restrictCoherentModules (X.homOfLE hkj) (F j))
    (c : ∀ (i : X.affineOpens) (V : X.Opens), V ≤ i.1 →
      (Γ(M, V) ≃ₗ[Γ(X, V)] Γ(coherentModulesPushforward i.1.ι (F i), V)))
    (hd₁ : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
      restrictedAlgebraizationMapOfLE hki (b i) ≫ (d k i j hki hkj).hom =
        restrictedAlgebraizationMapOfLE hkj (b j))
    (hcres : ∀ (i : X.affineOpens) (V V' : X.Opens) (hV : V ≤ i.1) (h : V' ≤ V) (s : Γ(M, V)),
      c i V' (h.trans hV) ((Scheme.Modules.presheaf M).map (homOfLE h).op s) =
        (Scheme.Modules.presheaf (coherentModulesPushforward i.1.ι (F i))).map (homOfLE h).op
          (c i V hV s))
    (hchart : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1) (s : Γ(M, k.1)),
      c j k.1 hkj s = Stacks.Coherent.localAppOpen k.1
        (overlapRestrictIso hki hkj (d k i j hki hkj)).hom le_rfl (c i k.1 hki s)) :
    ∃ φ : G.obj ⟶ M, ∀ (i : X.affineOpens) (V : X.Opens) (hV : V ≤ i.1) (s : Γ(G.obj, V)),
      Scheme.Modules.Hom.app φ V s = (c i V hV).symm
        (Stacks.Coherent.localAppOpen i.1 (pushforwardChartMap (b i)) hV s) := by
  classical
  set g : ∀ (i : X.affineOpens) (V : X.Opens), V ≤ i.1 → (Γ(G.obj, V) ⟶ Γ(M, V)) :=
    fun i V hV => Stacks.Coherent.localAppOpen i.1 (pushforwardChartMap (b i)) hV ≫
      AddCommGrpCat.ofHom (c i V hV).symm.toLinearMap.toAddMonoidHom with hgdef
  have hgapp : ∀ (i : X.affineOpens) (V : X.Opens) (hV : V ≤ i.1) (s : Γ(G.obj, V)),
      g i V hV s = (c i V hV).symm
        (Stacks.Coherent.localAppOpen i.1 (pushforwardChartMap (b i)) hV s) :=
    fun _ _ _ _ => rfl
  obtain ⟨φ, hφ, -⟩ := Stacks.Coherent.existsUnique_hom_of_cover_affineApp
    (X := X) (M := G.obj) (N := M) (ι := X.affineOpens) (U := fun i : X.affineOpens => i.1)
    (iSup_affineOpens_eq_top X) g
    (fun i V hV r s => by
      rw [hgapp, hgapp, localAppOpen_smul i.1 (pushforwardChartMap (b i)) hV r s]
      exact (c i V hV).symm.map_smul r _)
    (fun i V W hV hWV s => by
      rw [hgapp, hgapp,
        Stacks.Coherent.localAppOpen_map_of_le i.1 (pushforwardChartMap (b i)) hV hWV s]
      refine (c i W (hWV.trans hV)).injective ?_
      rw [LinearEquiv.apply_symm_apply, hcres i V W hV hWV _, LinearEquiv.apply_symm_apply])
    (fun i j k hki hkj => by
      have hov := localAppOpen_pushforwardChartMap_overlap hki hkj (b i) (b j)
        (d k i j hki hkj) (hd₁ k i j hki hkj)
      ext s
      rw [hgapp, hgapp]
      refine ((c j k.1 hkj).injective ?_).symm
      rw [LinearEquiv.apply_symm_apply,
        hchart k i j hki hkj ((c i k.1 hki).symm (Stacks.Coherent.localAppOpen i.1
          (pushforwardChartMap (b i)) hki s)), LinearEquiv.apply_symm_apply]
      exact congrArg (fun z => z s) hov.symm)
  exact ⟨φ, fun i V hV s => (congrArg (fun z => z s) (hφ i V hV)).trans (hgapp i V hV s)⟩

/-! ### Abstract reassociation helpers for the two glueings -/

section Helpers₂

variable {C : Type*} [Category C]

/-- An overlap comparison read backwards: from the identity satisfied by the two conjugated
morphisms, the identity satisfied by the two morphisms themselves. This is
`Stacks.Algebraization.overlapChain` in the other direction, and it is what turns the sheaf-level
comparison of two charts into the first defining identity of an overlap comparison. -/
private theorem overlapChainRev {A B₁ B₂ D₁ D₂ : C} {u : A ⟶ B₁} {e₁ : B₁ ≅ D₁} {w : D₁ ⟶ D₂}
    {e₂ : B₂ ≅ D₂} {v : A ⟶ B₂} {x₁ : A ⟶ D₁} {x₂ : A ⟶ D₂}
    (h : u ≫ e₁.hom ≫ w ≫ e₂.inv = v) (h₁ : u ≫ e₁.hom = x₁) (h₂ : v ≫ e₂.hom = x₂) :
    x₁ ≫ w = x₂ := by
  subst h₁
  subst h₂
  rw [← h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Reassociating a composite of four morphisms whose first two and whose middle step are
known. -/
private theorem compChain₃ {A B D E Z S : C} {p : A ⟶ B} {a : B ⟶ D} {b : D ⟶ E} {c : E ⟶ Z}
    {u : A ⟶ D} {v : A ⟶ S} {w : S ⟶ E}
    (h₁ : p ≫ a = u) (h₂ : u ≫ b = v ≫ w) : p ≫ a ≫ b ≫ c = v ≫ w ≫ c := by
  rw [← Category.assoc, ← Category.assoc, h₁, h₂, Category.assoc]

/-- Associativity read right to left. -/
private theorem assocRev {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) :
    a ≫ b ≫ c = (a ≫ b) ≫ c := (Category.assoc a b c).symm

/-- The component at an object of a composite of three isomorphisms of functors. Taking the
component of the composite rather than composing the components is what keeps the definitional
check small; see the implementation notes. -/
private theorem isoTrans₃_app {J : Type*} [Category J] {A B D E : J ⥤ C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (n : J) :
    (a ≪≫ b ≪≫ c).hom.app n = a.hom.app n ≫ b.hom.app n ≫ c.hom.app n := rfl

/-- **A composite of four morphisms rewritten by five local identities.** The chain is carried out
in an abstract category on purpose: `CategoryTheory.Category.assoc` does not rewrite in a goal
naming `AlgebraicGeometry.Scheme.Modules` morphisms, so every reassociation of the composites of
this file is performed here and transported by `exact`.

The eight objects are all distinct. That matters: identifying the target of `c₂` with the target
of `pw'` — they are the restriction of a term of the given system and a term of the completion of
a restriction, which the comparison of Stacks 0880 identifies but which are not the same object —
makes the elaborator unfold `Stacks.Algebraization.completionFunctor` and time out. -/
private theorem assembleChain {A B D E Z S T V K : C}
    {p : A ⟶ B} {q : B ⟶ D} {r : D ⟶ E} {s : E ⟶ Z}
    {g : A ⟶ S} {h : S ⟶ D} {c₁ : S ⟶ T} {c₂ : T ⟶ E}
    {a : A ⟶ T} {pw : A ⟶ V} {mf : V ⟶ K} {pw' : T ⟶ K} {w : K ⟶ Z}
    (e1 : p ≫ q = g ≫ h) (e2 : h ≫ r = c₁ ≫ c₂) (e3 : g ≫ c₁ = a)
    (e4 : c₂ ≫ s = pw' ≫ w) (e5 : pw ≫ mf = a ≫ pw') :
    p ≫ q ≫ r ≫ s = pw ≫ mf ≫ w := by
  rw [← Category.assoc, e1, Category.assoc, ← Category.assoc h r, e2, Category.assoc, e4,
    ← Category.assoc, e3, ← Category.assoc, ← e5, Category.assoc]

/-- Cancelling a known middle factor out of a composite of three morphisms. -/
private theorem threeChain {A B D Z : C} {u : A ⟶ B} {m : B ⟶ D} {ij : D ⟶ Z} {ii : B ⟶ Z}
    {v : A ⟶ D} (h : m ≫ ij = ii) (h₁ : u ≫ m = v) : u ≫ ii = v ≫ ij := by
  rw [← h, ← Category.assoc, h₁]

/-- Contracting the first two factors of a composite of three. -/
private theorem reassocLeft {A B D Z : C} {p : A ⟶ B} {q : B ⟶ D} {e : A ⟶ D} (h : p ≫ q = e)
    (Λ : D ⟶ Z) : p ≫ q ≫ Λ = e ≫ Λ := by rw [← Category.assoc, h]

end Helpers₂

/-! ### The cross-chart compatibility of the glued module at the sheaf level -/

/-- **The cross-chart compatibility of a glued module, at the sheaf level, in the shape of the
first defining identity of an overlap comparison.** Let `M` be a sheaf of modules identified over
every affine open `i` with the direct image of a coherent module `F i` on `i`, let `d` be a family
of comparisons of those modules over the affine opens contained in two charts, and suppose the two
identifications over an affine open `k` differ by the comparison *on sections* — which is what
`Stacks.Algebraization.exists_glued_of_localAlgebraizations` returns — and that the comparisons
are compatible with shrinking the overlap. Then the identifications themselves, carried to `k`,
differ by the comparison as an equation of morphisms of coherent modules.

This is the statement the glueing of the isomorphism `M^∧ ≅ (F_n)` needs, and it cannot be had by
reading the hypothesis over `k` alone: a morphism of the restrictions to `k` is pinned down by its
action on the sections over *every* open inside `k`, not over `k` itself. The hypothesis is
available over every affine open inside `k`, and
`Stacks.Coherent.localAppOpen_eq_of_affineOpens` upgrades agreement there to agreement over every
open inside `k`, after which the uniqueness half of
`Stacks.Coherent.exists_restrictHom_of_app` — in the form
`Stacks.Algebraization.restrictHom_ext_of_localAppOpen` — identifies the two morphisms. Moving
between the comparison over `k` and the comparison over a smaller affine open is
`Stacks.Algebraization.localAppOpen_eq_restrictDown_of_le` on the chart data and the hypothesis
`hdres` on the comparisons; the latter is
`Stacks.Algebraization.localAppOpen_overlapRestrictIso_restrict`.

The passage between the two presentations of a chart datum — as a morphism of the restrictions to
a chart and as the transported algebraization morphism — is
`Stacks.Algebraization.restrictedAlgebraizationMapOfLE_hom_eq_pushforward` at both ends. -/
public theorem chartIso_comp_overlapComparison {X : Scheme.{u}} [IsLocallyNoetherian X]
    {N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    {F : ∀ i : X.affineOpens,
      AlgebraicGeometry.SheafOfModules.CoherentModules i.1.toScheme.ringCatSheaf}
    (chart : ∀ i : X.affineOpens, restrictCoherentModules i.1.ι N ⟶ F i)
    (d : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
      restrictCoherentModules (X.homOfLE hki) (F i) ≅
        restrictCoherentModules (X.homOfLE hkj) (F j))
    (hsec : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
      Stacks.Coherent.localAppOpen i.1 (pushforwardChartMap (chart i)) hki ≫
          Stacks.Coherent.localAppOpen k.1
            (overlapRestrictIso hki hkj (d k i j hki hkj)).hom le_rfl =
        Stacks.Coherent.localAppOpen j.1 (pushforwardChartMap (chart j)) hkj)
    (hdres : ∀ (k l i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1) (hlk : l.1 ≤ k.1),
      Stacks.Coherent.localAppOpen l.1
          (overlapRestrictIso (hlk.trans hki) (hlk.trans hkj)
            (d l i j (hlk.trans hki) (hlk.trans hkj))).hom le_rfl =
        Stacks.Coherent.localAppOpen k.1
          (overlapRestrictIso hki hkj (d k i j hki hkj)).hom hlk)
    (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1) :
    restrictedAlgebraizationMapOfLE hki (chart i) ≫ (d k i j hki hkj).hom =
      restrictedAlgebraizationMapOfLE hkj (chart j) := by
  have hΨ : ((restrictDownIso hki N.obj).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hki)).map (pushforwardChartMap (chart i)) ≫
          (restrictDownIso hki (coherentModulesPushforward i.1.ι (F i))).inv) ≫
        (overlapRestrictIso hki hkj (d k i j hki hkj)).hom =
      (restrictDownIso hkj N.obj).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hkj)).map (pushforwardChartMap (chart j)) ≫
          (restrictDownIso hkj (coherentModulesPushforward j.1.ι (F j))).inv := by
    refine restrictHom_ext_of_localAppOpen k.1 _ _ fun V hV => ?_
    refine Stacks.Coherent.localAppOpen_eq_of_affineOpens _ _ (fun l hlk hlk' => ?_) hV hV
    refine Eq.trans (localAppOpen_comp k.1 _ _ hlk) ?_
    refine Eq.trans (congrArg (fun z => z ≫ Stacks.Coherent.localAppOpen k.1
        (overlapRestrictIso hki hkj (d k i j hki hkj)).hom hlk)
      (localAppOpen_eq_restrictDown_of_le hki hlk (pushforwardChartMap (chart i))).symm) ?_
    refine Eq.trans (congrArg (fun z =>
        Stacks.Coherent.localAppOpen i.1 (pushforwardChartMap (chart i)) (hlk.trans hki) ≫ z)
      (hdres k l i j hki hkj hlk).symm) ?_
    exact (hsec l i j (hlk.trans hki) (hlk.trans hkj)).trans
      (localAppOpen_eq_restrictDown_of_le hkj hlk' (pushforwardChartMap (chart j)))
  have hfinal := overlapChainRev (e₁ := coherentModulesPushforwardRestrictIso hki (F i))
      (w := (d k i j hki hkj).hom.hom) (e₂ := coherentModulesPushforwardRestrictIso hkj (F j)) hΨ
    (restrictDown_pushforwardChartMap_comp_hom_eq hki N (F i) (chart i))
    (restrictDown_pushforwardChartMap_comp_hom_eq hkj N (F j) (chart j))
  exact ObjectProperty.hom_ext _ ((fullSubcategoryComp_hom _ _).trans hfinal)

/-! ### The chart comparison of the completion read through the projections -/

/-- The underlying morphism of a completed composite. -/
private theorem completionMapComp_hom {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (J : Y.IdealSheafData)
    {A B E : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf} (a : A ⟶ B)
    (b : B ⟶ E) :
    ((completionFunctor Y J).map (a ≫ b)).hom =
      ((completionFunctor Y J).map a).hom ≫ ((completionFunctor Y J).map b).hom := by
  rw [Functor.map_comp]
  exact fullSubcategoryComp_hom _ _

/-- `Stacks.Algebraization.completionRestrictChartIso` unfolded, at the level of isomorphisms of
systems. Unfolding before taking a component is what keeps the definitional check small: the
component's type names the terms of a completion, which are cokernels. -/
private theorem completionRestrictChartIso_hom_hom {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.Opens)
    (Fg : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (Fi : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (chart : restrictCoherentModules U.ι Fg ≅ Fi)
    (βi : ((completionFunctor U.toScheme (I.comap U.ι)).obj Fi).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj) :
    (completionRestrictChartIso I U Fg Fsys Fi chart βi).hom.hom =
      (completionRestrictOpenIso U.ι I Fg ≪≫
        underlyingObjIso ((completionFunctor U.toScheme (I.comap U.ι)).mapIso chart) ≪≫
          βi).hom := rfl

/-- **The local comparison of the completion of a glued module with the given system, read through
the projections.** Restricting the projection of the glued module onto the `n`-th term of its
completion and then comparing over the chart `U` gives the chart identification followed by the
projection of the chart's module and the chart's own comparison.

The three factors of `Stacks.Algebraization.completionRestrictChartIso` are annihilated one at a
time: the comparison of Stacks 0880 by
`Stacks.Algebraization.completionProjection_comp_completionRestrictOpenIso`, the completion of the
chart identification by `Stacks.Algebraization.completionFunctor_map_quotient`, and `β` is left
standing. -/
public theorem completionProjection_comp_completionRestrictChartIso {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
    (Fg : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (Fi : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf)
    (chart : restrictCoherentModules U.ι Fg ≅ Fi)
    (βi : ((completionFunctor U.toScheme (I.comap U.ι)).obj Fi).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map (completionProjection X I Fg n) ≫
        (completionRestrictChartIso I U Fg Fsys Fi chart βi).hom.hom.app (op n) =
      chart.hom.hom ≫
        completionProjection U.toScheme (I.comap U.ι) Fi n ≫ βi.hom.app (op n) := by
  rw [completionRestrictChartIso_hom_hom, isoTrans₃_app]
  exact compChain₃ (completionProjection_comp_completionRestrictOpenIso U.ι I Fg n)
    (completionFunctor_map_quotient U.toScheme (I.comap U.ι) chart.hom n)

/-! ### The local comparison of the completion, restricted down to an overlap -/

/-- Two restrictions of a morphism agree as soon as the morphism does, at a factorization chosen
on each side. This is `CategoryTheory.Functor.map_comp` read backwards on both sides; the rewrite
has to happen in a standalone lemma, because `← Functor.map_comp` does not fire inside
`simp only` in the goals of this development. -/
private theorem restrictFunctorMapChain {Z V : Scheme.{u}} (f : V ⟶ Z) [IsOpenImmersion f]
    {M N P S : Z.Modules} (a : M ⟶ N) (b : N ⟶ P) (c : M ⟶ S) (e : S ⟶ P) (h : a ≫ b = c ≫ e) :
    (Scheme.Modules.restrictFunctor f).map a ≫ (Scheme.Modules.restrictFunctor f).map b =
      (Scheme.Modules.restrictFunctor f).map c ≫ (Scheme.Modules.restrictFunctor f).map e := by
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- **The local comparison of the completion of a glued module with the given system, carried down
to an open `W` of the chart and read through the projections.**

This is the computation the overlap hypothesis of
`Stacks.Coherent.existsUnique_coherentSystemIso_of_affineComparison` is checked by. The left-hand
side is the restriction down to `W` of the chart comparison, precomposed with the restriction of
the projection of the glued module; the right-hand side names only the *transported* chart datum —
`Stacks.Algebraization.restrictedAlgebraizationMapOfLE` and
`Stacks.Algebraization.restrictedAlgebraizationIsoOfLE` — and so depends on the chart `U` through
nothing but those two. Two charts therefore give the same right-hand side as soon as their
transported data agree, which is what
`Stacks.Algebraization.completionMapOfLE_comp_restrictedAlgebraizationIsoOfLE_eq` says.

Nothing is read on sections: the chain is
`Stacks.Algebraization.restrictDownIso_hom_naturality`,
`Stacks.Algebraization.completionProjection_comp_completionRestrictChartIso`,
`Stacks.Algebraization.restrictedAlgebraizationMapOfLE_hom_eq_restrictDown`,
`Stacks.Algebraization.completionProjection_comp_restrictedAlgebraizationIsoOfLE` and
`Stacks.Algebraization.completionFunctor_map_quotient`, assembled by
`Stacks.Algebraization.assembleChain`. -/
public theorem restrictDown_completionRestrictChartIso {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    {N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (Fsys : Stacks.Coherent.CoherentAdicSystems I) {U W : X.Opens} (hWU : W ≤ U)
    {F : AlgebraicGeometry.SheafOfModules.CoherentModules U.toScheme.ringCatSheaf}
    (chart : restrictCoherentModules U.ι N ≅ F)
    (β : ((completionFunctor U.toScheme (I.comap U.ι)).obj F).obj ≅
      ((Stacks.Coherent.restrictFunctor I U.ι).obj Fsys).obj) (n : ℕ) :
    (Scheme.Modules.restrictFunctor W.ι).map (completionProjection X I N n) ≫
        (restrictDownIso hWU (((completionFunctor X I).obj N).obj.obj (op n))).hom ≫
          (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
              ((completionRestrictChartIso I U N Fsys F chart β).hom.hom.app (op n)) ≫
            (restrictDownIso hWU (Fsys.obj.obj (op n))).inv =
      completionProjection W.toScheme (I.comap W.ι) (restrictCoherentModules W.ι N) n ≫
        ((completionFunctor W.toScheme (I.comap W.ι)).map
            (restrictedAlgebraizationMapOfLE hWU chart.hom)).hom.app (op n) ≫
          (restrictedAlgebraizationIsoOfLE I Fsys hWU β).hom.app (op n) := by
  have e1 : (Scheme.Modules.restrictFunctor W.ι).map (completionProjection X I N n) ≫
        (restrictDownIso hWU (((completionFunctor X I).obj N).obj.obj (op n))).hom =
      (restrictDownIso hWU N.obj).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          ((Scheme.Modules.restrictFunctor U.ι).map (completionProjection X I N n)) :=
    restrictDownIso_hom_naturality hWU (completionProjection X I N n)
  have e2 : (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          ((Scheme.Modules.restrictFunctor U.ι).map (completionProjection X I N n)) ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          ((completionRestrictChartIso I U N Fsys F chart β).hom.hom.app (op n)) =
      (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map chart.hom.hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          (completionProjection U.toScheme (I.comap U.ι) F n ≫ β.hom.app (op n)) :=
    restrictFunctorMapChain (X.homOfLE hWU) _ _ _ _
      (completionProjection_comp_completionRestrictChartIso I U N Fsys F chart β n)
  have e3 : (restrictDownIso hWU N.obj).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map chart.hom.hom =
      (restrictedAlgebraizationMapOfLE hWU chart.hom).hom :=
    restrictedAlgebraizationMapOfLE_hom_eq_restrictDown hWU chart.hom
  have e4 : (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
          (completionProjection U.toScheme (I.comap U.ι) F n ≫ β.hom.app (op n)) ≫
        (restrictDownIso hWU (Fsys.obj.obj (op n))).inv =
      completionProjection W.toScheme (I.comap W.ι)
          (restrictCoherentModules (X.homOfLE hWU) F) n ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hWU β).hom.app (op n) :=
    (congrArg (fun z => (Scheme.Modules.restrictFunctor (X.homOfLE hWU)).map
        (completionProjection U.toScheme (I.comap U.ι) F n ≫ β.hom.app (op n)) ≫ z)
      (restrictDownIso_inv_eq hWU (Fsys.obj.obj (op n)))).trans
      (completionProjection_comp_restrictedAlgebraizationIsoOfLE I Fsys hWU β n).symm
  have e5 : completionProjection W.toScheme (I.comap W.ι)
          (restrictCoherentModules W.ι N) n ≫
        ((completionFunctor W.toScheme (I.comap W.ι)).map
          (restrictedAlgebraizationMapOfLE hWU chart.hom)).hom.app (op n) =
      (restrictedAlgebraizationMapOfLE hWU chart.hom).hom ≫
        completionProjection W.toScheme (I.comap W.ι)
          (restrictCoherentModules (X.homOfLE hWU) F) n :=
    completionFunctor_map_quotient W.toScheme (I.comap W.ι)
      (restrictedAlgebraizationMapOfLE hWU chart.hom) n
  exact assembleChain e1 e2 e3 e4 e5

/-! ### The overlap hypothesis of the glueing of the isomorphism -/

/-- **Two charts whose transported algebraization data are comparable have the same transported
comparison.** This is the second defining identity of an overlap comparison with the first one
substituted into it: completing the first identity and composing with the comparison of the second
chart turns the comparison of the two transported `β`'s into an equality of the two transported
composites.

It is an equation between morphisms of *systems* over the overlap, and it is never read on
sections — which is why the cokernel obstruction does not arise: the projection out of the
completion over the overlap is an epimorphism of sheaves of modules
(`Stacks.Algebraization.epi_completionProjection`), not a surjection on the sections over a fixed
open, and that is all that is used. -/
public theorem completionMapOfLE_comp_restrictedAlgebraizationIsoOfLE_eq {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    {N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (Fsys : Stacks.Coherent.CoherentAdicSystems I) {Ui Uj Wk : X.Opens}
    (hki : Wk ≤ Ui) (hkj : Wk ≤ Uj)
    {Fi : AlgebraicGeometry.SheafOfModules.CoherentModules Ui.toScheme.ringCatSheaf}
    {Fj : AlgebraicGeometry.SheafOfModules.CoherentModules Uj.toScheme.ringCatSheaf}
    (bi : restrictCoherentModules Ui.ι N ⟶ Fi) (bj : restrictCoherentModules Uj.ι N ⟶ Fj)
    (βi : ((completionFunctor Ui.toScheme (I.comap Ui.ι)).obj Fi).obj ≅
      ((Stacks.Coherent.restrictFunctor I Ui.ι).obj Fsys).obj)
    (βj : ((completionFunctor Uj.toScheme (I.comap Uj.ι)).obj Fj).obj ≅
      ((Stacks.Coherent.restrictFunctor I Uj.ι).obj Fsys).obj)
    (dk : restrictCoherentModules (X.homOfLE hki) Fi ≅
      restrictCoherentModules (X.homOfLE hkj) Fj)
    (hd₁ : restrictedAlgebraizationMapOfLE hki bi ≫ dk.hom =
      restrictedAlgebraizationMapOfLE hkj bj)
    (hd₂ : ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map dk.hom).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hkj βj).hom =
      (restrictedAlgebraizationIsoOfLE I Fsys hki βi).hom) :
    ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map
          (restrictedAlgebraizationMapOfLE hki bi)).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hki βi).hom =
      ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map
          (restrictedAlgebraizationMapOfLE hkj bj)).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hkj βj).hom := by
  have h₁ : ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map
          (restrictedAlgebraizationMapOfLE hki bi)).hom ≫
        ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map dk.hom).hom =
      ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map
        (restrictedAlgebraizationMapOfLE hkj bj)).hom :=
    (completionMapComp_hom (I.comap Wk.ι) _ _).symm.trans
      (congrArg (fun z => ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map z).hom) hd₁)
  exact threeChain hd₂ h₁

/-- **The overlap hypothesis of
`Stacks.Coherent.existsUnique_coherentSystemIso_of_affineComparison` for the local comparisons of
the completion of a glued module with the given system.** Over an affine open `W` contained in two
charts, the two local comparisons act on the sections over `W` in the same way, provided the two
transported chart data are related by a comparison satisfying the two defining identities.

This is the last hypothesis of the globalization of Stacks 0889 part (2), and the point of its
proof is *where* each of the two identities is used.

* The first identity is used only through
  `Stacks.Algebraization.chartIso_comp_overlapComparison`, which is where the section-level
  cross-chart compatibility of the glued module is lifted to the sheaf level — through the affine
  opens inside `W`, not generically. Lifting it generically would be circular: reading both sides
  on the sections over every open inside `W` returns this very statement at those opens.
* The second identity is used only at the level of *systems*, by
  `Stacks.Algebraization.completionMapOfLE_comp_restrictedAlgebraizationIsoOfLE_eq`. It is never
  read on sections, and it cannot be: a morphism out of a completion is pinned down by the
  canonical projections, and `Stacks.Algebraization.epi_completionProjection` is an epimorphism of
  sheaves of modules, whose cokernel on the sections over a fixed open is only power-annihilated.

Accordingly the proof reduces the claim to a sheaf-level equation over `W` by
`Stacks.Algebraization.localAppOpen_eq_of_restrictDown_eq`, cancels the projection of the glued
module restricted to `W` — an epimorphism, as the composite of
`Stacks.Algebraization.epi_completionProjection` over `W` with the comparison of Stacks 0880 — and
computes both sides with `Stacks.Algebraization.restrictDown_completionRestrictChartIso`, whose
right-hand side mentions the chart only through its transported datum. -/
public theorem localAppOpen_completionRestrictChartIso_overlap {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    {N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (Fsys : Stacks.Coherent.CoherentAdicSystems I) {Ui Uj Wk : X.Opens}
    (hki : Wk ≤ Ui) (hkj : Wk ≤ Uj)
    {Fi : AlgebraicGeometry.SheafOfModules.CoherentModules Ui.toScheme.ringCatSheaf}
    {Fj : AlgebraicGeometry.SheafOfModules.CoherentModules Uj.toScheme.ringCatSheaf}
    (charti : restrictCoherentModules Ui.ι N ≅ Fi)
    (chartj : restrictCoherentModules Uj.ι N ≅ Fj)
    (βi : ((completionFunctor Ui.toScheme (I.comap Ui.ι)).obj Fi).obj ≅
      ((Stacks.Coherent.restrictFunctor I Ui.ι).obj Fsys).obj)
    (βj : ((completionFunctor Uj.toScheme (I.comap Uj.ι)).obj Fj).obj ≅
      ((Stacks.Coherent.restrictFunctor I Uj.ι).obj Fsys).obj)
    (dk : restrictCoherentModules (X.homOfLE hki) Fi ≅
      restrictCoherentModules (X.homOfLE hkj) Fj)
    (hd₁ : restrictedAlgebraizationMapOfLE hki charti.hom ≫ dk.hom =
      restrictedAlgebraizationMapOfLE hkj chartj.hom)
    (hd₂ : ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map dk.hom).hom ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hkj βj).hom =
      (restrictedAlgebraizationIsoOfLE I Fsys hki βi).hom) (n : ℕ) :
    Stacks.Coherent.localAppOpen Ui
        ((completionRestrictChartIso I Ui N Fsys Fi charti βi).hom.hom.app (op n)) hki =
      Stacks.Coherent.localAppOpen Uj
        ((completionRestrictChartIso I Uj N Fsys Fj chartj βj).hom.hom.app (op n)) hkj := by
  have hP : Epi (C := Wk.toScheme.Modules)
      (completionProjection Wk.toScheme (I.comap Wk.ι) (restrictCoherentModules Wk.ι N) n) :=
    epi_completionProjection Wk.toScheme (I.comap Wk.ι) (restrictCoherentModules Wk.ι N) n
  have hQiso : IsIso ((completionRestrictOpenIso Wk.ι I N).inv.app (op n)) :=
    NatIso.isIso_app_of_isIso _ _
  have hPQ : completionProjection Wk.toScheme (I.comap Wk.ι)
          (restrictCoherentModules Wk.ι N) n ≫
        (completionRestrictOpenIso Wk.ι I N).inv.app (op n) =
      (Scheme.Modules.restrictFunctor Wk.ι).map (completionProjection X I N n) :=
    completionProjection_comp_completionRestrictOpenIso_inv Wk.ι I N n
  have hstar : ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map
          (restrictedAlgebraizationMapOfLE hki charti.hom)).hom.app (op n) ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hki βi).hom.app (op n) =
      ((completionFunctor Wk.toScheme (I.comap Wk.ι)).map
          (restrictedAlgebraizationMapOfLE hkj chartj.hom)).hom.app (op n) ≫
        (restrictedAlgebraizationIsoOfLE I Fsys hkj βj).hom.app (op n) :=
    congrArg (fun t => NatTrans.app t (op n))
      (completionMapOfLE_comp_restrictedAlgebraizationIsoOfLE_eq I Fsys hki hkj charti.hom
        chartj.hom βi βj dk hd₁ hd₂)
  refine localAppOpen_eq_of_restrictDown_eq hki hkj _ _ ?_
  refine (cancel_epi ((completionRestrictOpenIso Wk.ι I N).inv.app (op n))).mp ?_
  refine (@cancel_epi _ _ _ _ _ (completionProjection Wk.toScheme (I.comap Wk.ι)
    (restrictCoherentModules Wk.ι N) n) hP _ _).mp ?_
  refine ((reassocLeft hPQ _).trans
    (restrictDown_completionRestrictChartIso I Fsys hki charti βi n)).trans ?_
  refine Eq.trans ?_ ((reassocLeft hPQ _).trans
    (restrictDown_completionRestrictChartIso I Fsys hkj chartj βj n)).symm
  exact congrArg (fun z => completionProjection Wk.toScheme (I.comap Wk.ι)
    (restrictCoherentModules Wk.ι N) n ≫ z) hstar

/-! ### The glued isomorphism of the completion with the given system -/

/-- **The coherent module glued from a family of local algebraizations, with an isomorphism of its
completion with the given system.** Let `α : G^∧ ⟶ (F_n)` be the datum of Stacks 0889 (2) and
suppose given a local algebraization `b i : G|_i ⟶ F i` with `β i : (F i)^∧ ≅ (F_n)|_i` over every
affine open `i` of `X`, with kernel and cokernel of `b i` annihilated by a power of `ℐ|_i`. Then
there is a coherent `𝒪_X`-module `M` with chart identifications `M|_i ≅ F i` and an isomorphism
`e : M^∧ ≅ (F_n)` restricting over each chart to the composite of the comparison of Stacks 0880,
the completed chart identification and `β i`; over an affine `k` inside two charts `i` and `j` one
comparison intertwines both the transported `b`'s and the transported chart identifications.

`Stacks.Algebraization.exists_glued_of_localAlgebraizations` builds `M` and the overlap
comparisons; `Stacks.Algebraization.exists_chartIso_of_appEquiv` upgrades its chart
identifications from linear equivalences of sections to isomorphisms of coherent modules;
`Stacks.Algebraization.completionRestrictChartIso` turns each of those into a comparison of the
completion of `M` restricted to the chart with the restricted system; and
`Stacks.Coherent.existsUnique_coherentSystemIso_of_affineComparison` glues those comparisons, its
overlap hypothesis being
`Stacks.Algebraization.localAppOpen_completionRestrictChartIso_overlap`.

The first defining identity of the overlap comparisons is consumed once, through
`Stacks.Algebraization.chartIso_comp_overlapComparison`, which converts the section-level
cross-chart compatibility of `M` into the identity for the *chart isomorphisms*; the second is
consumed at the level of systems and is never read on sections. -/
public theorem exists_glued_completionIso_of_localAlgebraizations {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (F : ∀ i : X.affineOpens,
      AlgebraicGeometry.SheafOfModules.CoherentModules i.1.toScheme.ringCatSheaf)
    (b : ∀ i : X.affineOpens, restrictCoherentModules i.1.ι G ⟶ F i)
    (β : ∀ i : X.affineOpens,
      ((completionFunctor i.1.toScheme (I.comap i.1.ι)).obj (F i)).obj ≅
        ((Stacks.Coherent.restrictFunctor I i.1.ι).obj Fsys).obj)
    (hβ : ∀ i : X.affineOpens, restrictedSystemMapDual i.1.ι I G Fsys α =
      ((completionFunctor i.1.toScheme (I.comap i.1.ι)).map (b i)).hom ≫ (β i).hom)
    (hK : ∀ i : X.affineOpens, IsPowerAnnihilated (I.comap i.1.ι)
      (kernel (C := i.1.toScheme.Modules) (b i).hom))
    (hC : ∀ i : X.affineOpens, IsPowerAnnihilated (I.comap i.1.ι)
      (cokernel (C := i.1.toScheme.Modules) (b i).hom)) :
    ∃ (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
      (chart : ∀ i : X.affineOpens, restrictCoherentModules i.1.ι M ≅ F i)
      (e : (completionFunctor X I).obj M ≅ Fsys),
      (∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
        ∃ dk : restrictCoherentModules (X.homOfLE hki) (F i) ≅
            restrictCoherentModules (X.homOfLE hkj) (F j),
          restrictedAlgebraizationMapOfLE hki (b i) ≫ dk.hom =
              restrictedAlgebraizationMapOfLE hkj (b j) ∧
            restrictedAlgebraizationMapOfLE hki (chart i).hom ≫ dk.hom =
              restrictedAlgebraizationMapOfLE hkj (chart j).hom) ∧
      ∀ i : X.affineOpens, (Stacks.Coherent.restrictFunctor I i.1.ι).map e.hom =
        (completionRestrictChartIso I i.1 M Fsys (F i) (chart i) (β i)).hom := by
  obtain ⟨M, d, c, ⟨-, hcoh⟩, hd₁, hd₂, hcres, hchart⟩ :=
    exists_glued_of_localAlgebraizations I G Fsys α F b β hβ hK hC
  choose chart hchartApp using fun i : X.affineOpens =>
    exists_chartIso_of_appEquiv i.1 hcoh (F i) (fun V hV => c i V hV)
      (fun V W hV hWV s => hcres i V W hV hWV s)
  have hA : ∀ (i : X.affineOpens) (V : X.Opens) (hV : V ≤ i.1) (s : Γ(M, V)),
      Stacks.Coherent.localAppOpen i.1 (pushforwardChartMap (chart i).hom) hV s =
        c i V hV s := hchartApp
  have hsec : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
      Stacks.Coherent.localAppOpen i.1 (pushforwardChartMap (chart i).hom) hki ≫
          Stacks.Coherent.localAppOpen k.1
            (overlapRestrictIso hki hkj (d k i j hki hkj)).hom le_rfl =
        Stacks.Coherent.localAppOpen j.1 (pushforwardChartMap (chart j).hom) hkj := by
    intro k i j hki hkj
    ext s
    refine Eq.trans (congrArg (fun z => Stacks.Coherent.localAppOpen k.1
        (overlapRestrictIso hki hkj (d k i j hki hkj)).hom le_rfl z) (hA i k.1 hki s)) ?_
    exact (hchart k i j hki hkj s).symm.trans (hA j k.1 hkj s).symm
  have hdres : ∀ (k l i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1)
      (hlk : l.1 ≤ k.1),
      Stacks.Coherent.localAppOpen l.1
          (overlapRestrictIso (hlk.trans hki) (hlk.trans hkj)
            (d l i j (hlk.trans hki) (hlk.trans hkj))).hom le_rfl =
        Stacks.Coherent.localAppOpen k.1
          (overlapRestrictIso hki hkj (d k i j hki hkj)).hom hlk :=
    fun k l i j hki hkj hlk =>
      localAppOpen_overlapRestrictIso_restrict I G Fsys α l hki hkj hlk (b i) (b j) (β i)
        (β j) (hβ i) (hβ j) (hK i) (hC i) (hK j) (hC j) (d k i j hki hkj)
        (hd₁ k i j hki hkj) (hd₂ k i j hki hkj)
        (d l i j (hlk.trans hki) (hlk.trans hkj))
        (hd₁ l i j (hlk.trans hki) (hlk.trans hkj))
        (hd₂ l i j (hlk.trans hki) (hlk.trans hkj))
  have hd₁' : ∀ (k i j : X.affineOpens) (hki : k.1 ≤ i.1) (hkj : k.1 ≤ j.1),
      restrictedAlgebraizationMapOfLE hki (chart i).hom ≫ (d k i j hki hkj).hom =
        restrictedAlgebraizationMapOfLE hkj (chart j).hom :=
    fun k i j hki hkj =>
      chartIso_comp_overlapComparison (fun i => (chart i).hom) d hsec hdres k i j hki hkj
  obtain ⟨e, he, -⟩ := Stacks.Coherent.existsUnique_coherentSystemIso_of_affineComparison I
    (fun i : X.affineOpens => i.1) (iSup_affineOpens_eq_top X)
    (S := (completionFunctor X I).obj ⟨M, hcoh⟩) (T := Fsys)
    (fun i => completionRestrictChartIso I i.1 ⟨M, hcoh⟩ Fsys (F i) (chart i) (β i))
    (fun i j n k hki hkj => localAppOpen_completionRestrictChartIso_overlap I Fsys hki hkj
      (chart i) (chart j) (β i) (β j) (d k i j hki hkj) (hd₁' k i j hki hkj)
      (hd₂ k i j hki hkj) n.unop)
  exact ⟨⟨M, hcoh⟩, chart, e,
    fun k i j hki hkj => ⟨d k i j hki hkj, hd₁ k i j hki hkj, hd₁' k i j hki hkj⟩, he⟩

/-- **A coherent adic system that receives a map out of a completion with power-annihilated kernel
and cokernel is itself a completion.** On a locally Noetherian scheme, if `α : G^∧ ⟶ (F_n)` has
levelwise kernels and cokernels annihilated by a power of `ℐ`, then `(F_n)` lies in the essential
image of the completion functor of Stacks 0880.

This is the essential-image consequence of Stacks 0889 part (2):
`Stacks.Algebraization.exists_local_algebraization_dual` provides a local algebraization over
every affine open — that is the affine theorem, available because `X` is locally Noetherian — and
`Stacks.Algebraization.exists_glued_completionIso_of_localAlgebraizations` glues them. It is the
form of part (2) that Tag 0EIU consumes.

Note that no quasi-compactness is used: the exponent of the annihilation of the kernel and the
cokernel of the local algebraizations is allowed to vary with the affine open, because the
conclusion does not mention it. That is why this holds on a locally Noetherian rather than a
Noetherian scheme. -/
public theorem essImage_of_map_from_completion {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (Fsys : Stacks.Coherent.CoherentAdicSystems I)
    (α : ((completionFunctor X I).obj G).obj ⟶ Fsys.obj)
    (hα : IsKernelCokernelAnnihilatedByPower I α) :
    (completionFunctor X I).essImage Fsys := by
  choose F b β h using fun i : X.affineOpens =>
    exists_local_algebraization_dual I G Fsys α hα i
  obtain ⟨M, -, e, -, -⟩ := exists_glued_completionIso_of_localAlgebraizations I G Fsys α F b β
    (fun i => (h i).1) (fun i => (h i).2.1) fun i => (h i).2.2
  exact ⟨M, ⟨e⟩⟩

end Stacks.Algebraization

end
