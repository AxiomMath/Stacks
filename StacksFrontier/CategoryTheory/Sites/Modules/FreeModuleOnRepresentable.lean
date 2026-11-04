module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelianSmall
public import StacksFrontier.CategoryTheory.Sites.Sheafification.LocalRepresentatives
import StacksCore.Tactic.StacksAttribute

/-! # The free sheaf of modules on a representable

Let `R` be a sheaf of rings on a site `(C, J)` whose objects, morphisms and rings all fit in
the universe `v` of the sections of the modules. The file
`StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelianSmall` builds, for each object `X`
of the site, the free presheaf of `R`-modules `generator R.obj X` on the representable at `X`,
with the index set and the coefficients shrunk into `v`, and the morphism `generatorDesc`
determined by a section over `X`. This file makes that construction *functorial* in `X`,
sheafifies it, and shows that restriction of sections of an injective sheaf of modules is
surjective along a morphism of the site whose representables are locally injective.

## Main definitions

* `Stacks.SheafOfModules.Small.generatorMap`: the morphism `generator R.obj X₁ ⟶
  generator R.obj X₂` of free presheaves of modules induced by `g : X₁ ⟶ X₂`.
* `Stacks.SheafOfModules.Small.freeSheaf` and `freeSheafMap`: their sheafifications.
* `Stacks.SheafOfModules.Small.freeSheafEval`: the section over `X` of a sheaf of modules `M`
  determined by a morphism `freeSheaf R X ⟶ M`.

## Main results

* `Stacks.SheafOfModules.Small.freeMap_eq_of_pairs`: a reindexing of finitely supported
  functions is determined, on the kernel of a coarser reindexing, by the coarser one, provided
  the finer map identifies every relevant pair the coarser one identifies.
* `Stacks.SheafOfModules.Small.isLocallyInjective_generatorMap`: the free module on a
  representable preserves local injectivity.
* `Stacks.SheafOfModules.Small.mono_freeSheafMap`: hence the induced morphism of free sheaves
  of modules is a monomorphism.
* `Stacks.SheafOfModules.Small.freeSheafEval_surjective` and
  `freeSheafEval_freeSheafMap_comp`: `freeSheafEval` is surjective and turns precomposition
  with `freeSheafMap` into restriction of sections.
* `Stacks.SheafOfModules.Small.exists_val_map_eq_of_injective`: restriction of sections of an
  injective sheaf of modules is surjective.

## Implementation notes

`freeMap_eq_of_pairs` is the combinatorial heart. A section of the free module over `Y` is a
finitely supported function on the shrunken set of morphisms `Y ⟶ X₁`; two sections with the
same image under `g` differ by an element of the kernel of reindexing along `g`, and only the
finitely many indices in its support matter, so the finitely many covering sieves produced by
local injectivity of the representables can be intersected. The factorisation of the
restriction map through the coarser reindexing is obtained with `Function.extend` on the
subtype of the support, where `Function.FactorsThrough` holds; the case of a zero difference is
separated out because `Function.extend` needs a default value.

The sheafification used is `PresheafOfModules.sheafification` at the identity of the underlying
presheaf of rings, which is locally bijective because it is an isomorphism. `freeSheaf`,
`freeSheafMap` and the sheafification functor itself are `abbrev`s so that the universal
property of the sheafification adjunction applies to them without unfolding; declaring
`freeSheaf` a `def` makes the adjunction's naturality fail to typecheck at instance
transparency.

## References

* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
* [Stacks Project, Tag 0EVY](https://stacks.math.columbia.edu/tag/0EVY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.Small

universe u v w r

section FreeMapAux

/-- `freeMap` with the identity on coefficients is reindexing. -/
lemma freeMap_id {I K M : Type*} [AddCommMonoid M] (g : I → K) (x : I →₀ M) :
    freeMap g (AddMonoidHom.id M) x = Finsupp.mapDomain g x := by
  simp [freeMap]

/-- `freeMap` reindexes first and then changes coefficients. -/
lemma freeMap_eq_mapRange_mapDomain {I K M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (g : I → K) (ψ : M →+ N) (x : I →₀ M) :
    freeMap g ψ x = Finsupp.mapRange ψ (map_zero ψ) (Finsupp.mapDomain g x) := by
  rw [freeMap, Finsupp.mapDomain.addMonoidHom_comp_mapRange]
  rfl

/-- **Reindexing along a finer map agrees on the kernel of a coarser one.** If two finitely
supported functions have the same image under reindexing along `p`, and if `q` identifies
every pair of relevant indices that `p` identifies, then they also have the same image under
reindexing along `q`, whatever the change of coefficients. -/
lemma freeMap_eq_of_pairs {I K L M N : Type*} [DecidableEq I] [AddCommGroup M] [AddCommGroup N]
    (p : I → K) (q : I → L) (ψ : M →+ N) (x y : I →₀ M)
    (hxy : freeMap p (AddMonoidHom.id M) x = freeMap p (AddMonoidHom.id M) y)
    (hq : ∀ i ∈ x.support ∪ y.support, ∀ j ∈ x.support ∪ y.support,
      p i = p j → q i = q j) :
    freeMap q ψ x = freeMap q ψ y := by
  classical
  have hzero : Finsupp.mapDomain p (x - y) = 0 := by
    rw [← freeMap_id, map_sub]
    exact sub_eq_zero_of_eq hxy
  have key : Finsupp.mapDomain q (x - y) = 0 := by
    rcases eq_or_ne (x - y) 0 with h0 | h0
    · rw [h0, Finsupp.mapDomain_zero]
    obtain ⟨i₀, hi₀⟩ := Finsupp.support_nonempty_iff.2 h0
    have hfac : (fun i : {i // i ∈ (x - y).support} ↦ q i.1).FactorsThrough
        (fun i : {i // i ∈ (x - y).support} ↦ p i.1) :=
      fun i j hij ↦ hq i.1 (Finsupp.support_sub i.2) j.1 (Finsupp.support_sub j.2) hij
    rw [Finsupp.mapDomain_congr (g := Function.extend
        (fun i : {i // i ∈ (x - y).support} ↦ p i.1)
        (fun i : {i // i ∈ (x - y).support} ↦ q i.1) (fun _ ↦ q i₀) ∘ p)
        (fun i hi ↦ (hfac.extend_apply _ ⟨i, hi⟩).symm),
      Finsupp.mapDomain_comp, hzero, Finsupp.mapDomain_zero]
  rw [← sub_eq_zero, ← map_sub, freeMap_eq_mapRange_mapDomain, key, Finsupp.mapRange_zero]

end FreeMapAux

section BasisPost

variable {C : Type u} [Category.{w} C] [UnivLE.{w, v}]

/-- Postcomposition with `g` on the index set of the free module on a representable. -/
def basisPost {X₁ X₂ : C} (g : X₁ ⟶ X₂) {Y : Cᵒᵖ} (i : Shrink.{v} (Y.unop ⟶ X₁)) :
    Shrink.{v} (Y.unop ⟶ X₂) :=
  basisUp.{u, v, w} (basisDown.{u, v, w} i ≫ g)

/-- The morphism named by `basisPost g i` is `basisDown i` followed by `g`. -/
@[simp]
lemma basisDown_basisPost {X₁ X₂ : C} (g : X₁ ⟶ X₂) {Y : Cᵒᵖ}
    (i : Shrink.{v} (Y.unop ⟶ X₁)) :
    basisDown.{u, v, w} (basisPost.{u, v, w} g i) = basisDown.{u, v, w} i ≫ g :=
  basisDown_basisUp.{u, v, w} _

/-- Postcomposition with `g` on indices commutes with restriction of indices. -/
lemma basisPost_basisMap {X₁ X₂ : C} (g : X₁ ⟶ X₂) {Y Z : Cᵒᵖ} (f : Y ⟶ Z)
    (i : Shrink.{v} (Y.unop ⟶ X₁)) :
    basisPost.{u, v, w} g (basisMap.{u, v, w} f i) =
      basisMap.{u, v, w} f (basisPost.{u, v, w} g i) :=
  basisDown_injective.{u, v, w} (by
    simp only [basisDown_basisPost.{u, v, w}, basisDown_basisMap.{u, v, w}, Category.assoc])

end BasisPost

section GeneratorMap

variable {C : Type u} [Category.{w} C] (Rp : Cᵒᵖ ⥤ RingCat.{r})
  [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- Restriction in the free module on a representable, on a basis element. -/
@[simp]
lemma generator_map_single {X : C} {Y Z : Cᵒᵖ} (f : Y ⟶ Z)
    (i : Shrink.{v} (Y.unop ⟶ X)) (a : Shrink.{v} (Rp.obj Y)) :
    (generator.{u, v, w, r} Rp X).map f (Finsupp.single i a) =
      Finsupp.single (basisMap.{u, v, w} f i) (coeffMap.{u, v, w, r} Rp f a) :=
  freeMap_single _ _ i a

/-- The morphism of free modules on representables induced by a morphism of the site. -/
def generatorMap {X₁ X₂ : C} (g : X₁ ⟶ X₂) :
    generator.{u, v, w, r} Rp X₁ ⟶ generator.{u, v, w, r} Rp X₂ :=
  PresheafOfModules.homMk
    { app Y := AddCommGrpCat.ofHom
        (freeMap (basisPost.{u, v, w} g (Y := Y)) (AddMonoidHom.id (Shrink.{v} (Rp.obj Y))))
      naturality := by
        intro Y Z f
        apply AddCommGrpCat.hom_ext
        apply Finsupp.addHom_ext
        intro i a
        change freeMap (basisPost.{u, v, w} g) (AddMonoidHom.id _)
            (freeMap (basisMap.{u, v, w} (X := X₁) f) (coeffMap.{u, v, w, r} Rp f)
              (Finsupp.single i a)) =
          freeMap (basisMap.{u, v, w} (X := X₂) f) (coeffMap.{u, v, w, r} Rp f)
            (freeMap (basisPost.{u, v, w} g) (AddMonoidHom.id _) (Finsupp.single i a))
        rw [freeMap_single, freeMap_single, freeMap_single, freeMap_single,
          basisPost_basisMap.{u, v, w}]
        rfl }
    (fun Y a x ↦ freeMap_smul (RingHom.id (Rp.obj Y)) _ _ (fun _ _ ↦ rfl) a x)

/-- `generatorMap g` sends the basis element at `i` to the basis element at `basisPost g i`,
leaving the coefficient alone. -/
@[simp]
lemma generatorMap_app_single {X₁ X₂ : C} (g : X₁ ⟶ X₂) (Y : Cᵒᵖ)
    (i : Shrink.{v} (Y.unop ⟶ X₁)) (a : Shrink.{v} (Rp.obj Y)) :
    (generatorMap.{u, v, w, r} Rp g).app Y (Finsupp.single i a) =
      Finsupp.single (basisPost.{u, v, w} g i) a :=
  freeMap_single _ _ i a

/-- The canonical section of the free module on the representable at `X₁`, pushed forward
along `g`, is the restriction along `g` of the canonical section at `X₂`. -/
lemma generatorMap_app_generatorUnit {X₁ X₂ : C} (g : X₁ ⟶ X₂) :
    (generatorMap.{u, v, w, r} Rp g).app (op X₁) (generatorUnit.{u, v, w, r} Rp X₁) =
      (generator.{u, v, w, r} Rp X₂).map g.op (generatorUnit.{u, v, w, r} Rp X₂) := by
  have hidx : basisPost.{u, v, w} g (basisUp.{u, v, w} (𝟙 X₁)) =
      basisMap.{u, v, w} (X := X₂) g.op (basisUp.{u, v, w} (𝟙 X₂)) :=
    basisDown_injective.{u, v, w} (by
      simp only [basisDown_basisPost.{u, v, w}, basisDown_basisMap.{u, v, w},
        basisDown_basisUp.{u, v, w}, Category.id_comp, Category.comp_id, Quiver.Hom.unop_op])
  have hcoeff : coeffUp.{u, v, w, r} Rp 1 =
      coeffMap.{u, v, w, r} Rp g.op (coeffUp.{u, v, w, r} Rp 1) :=
    coeffDown_injective.{u, v, w, r} Rp (by
      simp only [coeffDown_coeffUp.{u, v, w, r}, coeffDown_coeffMap.{u, v, w, r}, map_one])
  have h1 : (generatorMap.{u, v, w, r} Rp g).app (op X₁)
        (generatorUnit.{u, v, w, r} Rp X₁) =
      Finsupp.single (basisPost.{u, v, w} g (basisUp.{u, v, w} (𝟙 X₁)))
        (coeffUp.{u, v, w, r} Rp 1) :=
    generatorMap_app_single.{u, v, w, r} Rp g (op X₁) _ _
  have h2 : (generator.{u, v, w, r} Rp X₂).map g.op (generatorUnit.{u, v, w, r} Rp X₂) =
      Finsupp.single (basisMap.{u, v, w} (X := X₂) g.op (basisUp.{u, v, w} (𝟙 X₂)))
        (coeffMap.{u, v, w, r} Rp g.op (coeffUp.{u, v, w, r} Rp 1)) :=
    generator_map_single.{u, v, w, r} Rp g.op _ _
  rw [h1, h2, hidx, hcoeff]

end GeneratorMap

section LocalInjectivity

variable {C : Type u} [Category.{w} C] (J : GrothendieckTopology C) (Rp : Cᵒᵖ ⥤ RingCat.{r})
  [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- **The free module on a representable preserves local injectivity.** If postcomposition
with `g : X₁ ⟶ X₂` is locally injective on the representables, then so is the induced map of
the free modules on those representables. -/
theorem isLocallyInjective_generatorMap {X₁ X₂ : C} (g : X₁ ⟶ X₂)
    (hg : Presheaf.IsLocallyInjective J (yoneda.map g)) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf Rp).map (generatorMap.{u, v, w, r} Rp g)) := by
  classical
  refine ⟨fun {Y} x y hxy ↦ ?_⟩
  set F : Shrink.{v} (Y.unop ⟶ X₁) × Shrink.{v} (Y.unop ⟶ X₁) → Sieve Y.unop :=
    fun pr ↦ if basisDown.{u, v, w} pr.1 ≫ g = basisDown.{u, v, w} pr.2 ≫ g then
      Presheaf.equalizerSieve (F := yoneda.obj X₁) (X := Y)
        (basisDown.{u, v, w} pr.1) (basisDown.{u, v, w} pr.2) else ⊤ with hF
  have hFmem : ∀ pr, F pr ∈ J Y.unop := by
    intro pr
    rw [hF]
    dsimp only
    split
    · exact hg.equalizerSieve_mem _ _ (by assumption)
    · exact J.top_mem _
  refine J.superset_covering ?_
    (Stacks.Sheafification.finsetInf_covering J
      ((Finsupp.support x ∪ Finsupp.support y) ×ˢ (Finsupp.support x ∪ Finsupp.support y))
      F hFmem)
  intro Z h hh
  refine freeMap_eq_of_pairs (basisPost.{u, v, w} g (X₂ := X₂) (Y := Y))
    (basisMap.{u, v, w} (X := X₁) h.op) (coeffMap.{u, v, w, r} Rp h.op) x y hxy
    (fun i hi j hj hij ↦ ?_)
  have hgij : basisDown.{u, v, w} i ≫ g = basisDown.{u, v, w} j ≫ g := by
    simpa only [basisDown_basisPost.{u, v, w}] using
      congrArg (basisDown.{u, v, w} (X := X₂) (Y := Y)) hij
  have hFij : F (i, j) h :=
    Finset.inf_le (f := F) (Finset.mk_mem_product hi hj) h hh
  rw [hF] at hFij
  simp only [ite_eq_left hgij] at hFij
  have heq : h ≫ basisDown.{u, v, w} i = h ≫ basisDown.{u, v, w} j := hFij
  exact basisDown_injective.{u, v, w}
    (by simpa only [basisDown_basisMap.{u, v, w}, Quiver.Hom.unop_op] using heq)

end LocalInjectivity

section FreeSheaf

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [UnivLE.{w, v}] [UnivLE.{r, v}]
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Sheafification of presheaves of `R`-modules, taken at the identity of the underlying
presheaf of rings. -/
noncomputable abbrev shf : PresheafOfModules.{v} R.obj ⥤ SheafOfModules.{v} R :=
  PresheafOfModules.sheafification (R := R) (𝟙 R.obj)

/-- The free sheaf of modules on the representable at `X`: the sheafification of the free
presheaf of modules on the shrunken representable. -/
noncomputable abbrev freeSheaf (X : C) : SheafOfModules.{v} R :=
  (shf.{u, v, w, r} R).obj (generator.{u, v, w, r} R.obj X)

/-- The canonical section over `X` of the free sheaf of modules on the representable at `X`,
the image of `generatorUnit` under the sheafification map. -/
def freeSheafUnit (X : C) : (freeSheaf.{u, v, w, r} R X).val.obj (op X) :=
  (CategoryTheory.toSheafify J (generator.{u, v, w, r} R.obj X).presheaf).app (op X)
    (generatorUnit.{u, v, w, r} R.obj X)

/-- The section over `X` of a sheaf of modules `M` determined by a morphism out of the free
sheaf of modules on the representable at `X`: the image of the canonical section. -/
def freeSheafEval {X : C} {M : SheafOfModules.{v} R} (φ : freeSheaf.{u, v, w, r} R X ⟶ M) :
    M.val.obj (op X) :=
  φ.val.app (op X) (freeSheafUnit.{u, v, w, r} R X)

/-- `freeSheafEval` is evaluation of the morphism of presheaves of modules which corresponds
to `φ` under the sheafification adjunction. -/
lemma freeSheafEval_eq {X : C} {M : SheafOfModules.{v} R}
    (φ : freeSheaf.{u, v, w, r} R X ⟶ M) :
    freeSheafEval.{u, v, w, r} R φ =
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) φ).app (op X)
        (generatorUnit.{u, v, w, r} R.obj X) := rfl

/-- Every section over `X` comes from a morphism out of the free sheaf of modules on the
representable at `X`, namely from `generatorDesc`. -/
lemma freeSheafEval_surjective {X : C} {M : SheafOfModules.{v} R} (m : M.val.obj (op X)) :
    ∃ φ : freeSheaf.{u, v, w, r} R X ⟶ M, freeSheafEval.{u, v, w, r} R φ = m := by
  refine ⟨(PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    (generatorDesc.{u, v, w, r} R.obj _ m), ?_⟩
  refine (freeSheafEval_eq.{u, v, w, r} R _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact generatorDesc_app_generatorUnit.{u, v, w, r} R.obj _ m

/-- The morphism of free sheaves of modules induced by a morphism of the site. -/
noncomputable abbrev freeSheafMap {X₁ X₂ : C} (g : X₁ ⟶ X₂) :
    freeSheaf.{u, v, w, r} R X₁ ⟶ freeSheaf.{u, v, w, r} R X₂ :=
  (shf.{u, v, w, r} R).map (generatorMap.{u, v, w, r} R.obj g)

/-- Precomposing with `freeSheafMap R g` restricts the corresponding section along `g`. -/
lemma freeSheafEval_freeSheafMap_comp {X₁ X₂ : C} (g : X₁ ⟶ X₂) {M : SheafOfModules.{v} R}
    (φ : freeSheaf.{u, v, w, r} R X₂ ⟶ M) :
    freeSheafEval.{u, v, w, r} R (freeSheafMap.{u, v, w, r} R g ≫ φ) =
      M.val.map g.op (freeSheafEval.{u, v, w, r} R φ) := by
  have h1 : PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)
        (freeSheafMap.{u, v, w, r} R g ≫ φ) =
      generatorMap.{u, v, w, r} R.obj g ≫
        PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) φ := by
    rw [← PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
      ← PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
    exact (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left _ _
  rw [freeSheafEval_eq.{u, v, w, r}, freeSheafEval_eq.{u, v, w, r}, h1,
    PresheafOfModules.comp_app]
  rw [show ((generatorMap.{u, v, w, r} R.obj g).app (op X₁) ≫
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) φ).app (op X₁))
        (generatorUnit.{u, v, w, r} R.obj X₁) =
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) φ).app (op X₁)
        ((generatorMap.{u, v, w, r} R.obj g).app (op X₁)
          (generatorUnit.{u, v, w, r} R.obj X₁)) from rfl,
    generatorMap_app_generatorUnit.{u, v, w, r}]
  exact PresheafOfModules.naturality_apply _ _ _

/-- **The free sheaf of modules on a representable preserves monomorphy.** If precomposition
with `g` is locally injective on the representables, the induced morphism of free sheaves of
modules is a monomorphism. -/
lemma mono_freeSheafMap {X₁ X₂ : C} (g : X₁ ⟶ X₂)
    [J.HasSheafCompose (forget AddCommGrpCat.{v})]
    (hg : Presheaf.IsLocallyInjective J (yoneda.map g)) :
    Mono (freeSheafMap.{u, v, w, r} R g) := by
  have h2 : Sheaf.IsLocallyInjective ((presheafToSheaf J AddCommGrpCat.{v}).map
      ((PresheafOfModules.toPresheaf R.obj).map
        (generatorMap.{u, v, w, r} R.obj g))) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ _).2
      (isLocallyInjective_generatorMap.{u, v, w, r} J R.obj g hg)
  have h3 : Sheaf.IsLocallyInjective
      ((SheafOfModules.toSheaf R).map (freeSheafMap.{u, v, w, r} R g)) := h2
  exact (SheafOfModules.toSheaf R).mono_of_mono_map (Sheaf.mono_of_isLocallyInjective _)

/-- **Restriction of sections of an injective sheaf of modules is surjective along a locally
injective map of representables.** -/
theorem exists_val_map_eq_of_injective {X₁ X₂ : C} (g : X₁ ⟶ X₂)
    [J.HasSheafCompose (forget AddCommGrpCat.{v})]
    (hg : Presheaf.IsLocallyInjective J (yoneda.map g))
    (M : SheafOfModules.{v} R) [Injective M] (m : M.val.obj (op X₁)) :
    ∃ n : M.val.obj (op X₂), M.val.map g.op n = m := by
  obtain ⟨φ, hφ⟩ := freeSheafEval_surjective.{u, v, w, r} R m
  have hmono := mono_freeSheafMap.{u, v, w, r} R g hg
  refine ⟨freeSheafEval.{u, v, w, r} R
    (Injective.factorThru φ (freeSheafMap.{u, v, w, r} R g)), ?_⟩
  rw [← freeSheafEval_freeSheafMap_comp.{u, v, w, r}, Injective.comp_factorThru, hφ]

end FreeSheaf

end Stacks.SheafOfModules.Small

end
