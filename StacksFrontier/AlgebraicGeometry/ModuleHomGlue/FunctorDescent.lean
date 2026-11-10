module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.NatTrans
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic

/-!
# Descending a functor valued in sheaves of modules along an open cover of the target

Let `S` be a scheme, let `C` be any category, and let `f i : Y i ⟶ S` be a family of open
immersions whose images cover `S`. This file glues a family of functors
`F i : C ⥤ (Y i).Modules`, together with comparison isomorphisms over the overlaps satisfying the
cocycle condition, into a **single** functor `C ⥤ S.Modules` restricting to the `F i`.

This is object-level 2-descent for the pseudofunctor `U ↦ Fun(C, QCoh(𝒪_U))`, which is what step
3 of the Gabriel–Rosenberg reconstruction theorem (Tag 0GPJ) needs: there a functor
`QCoh(𝒪_X) ⥤ QCoh(𝒪_{V i})` is built on each member of an affine open cover of `Y`, and a single
functor `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` has to be produced. The companion file
`StacksFrontier/AlgebraicGeometry/ModuleHomGlue/NatTrans.lean` does the 1-morphism layer: it glues a
family of natural transformations defined over the members of the cover. Here the *objects* are
glued, and the 1-morphism layer is what makes the glued assignment a functor and what pins it
down up to isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.sectionsOfHom`: a map between the modules of
  sections over an open `V` of `S`, read as a map of the underlying abelian groups `Γ(M, V)`.
  This is the one piece of plumbing the file needs: the comparison isomorphisms of Tag 00AM are
  isomorphisms of bundled `Γ(S, V)`-modules, while the gluing statement for morphisms is phrased
  with `AlgebraicGeometry.Scheme.Modules.Hom.app`.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData`: **descent data for a functor
  valued in sheaves of modules.** A functor `C ⥤ (Y i).Modules` for each chart, plus comparison
  isomorphisms on the sections over the opens of `S` contained in two chart images, natural in
  the object of `C`, compatible with restriction, and satisfying the cocycle condition.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.toModulesGlueData`: the descent
  datum of sheaves of modules obtained by evaluating at one object of `C`.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.gluedObj`: the sheaf of modules
  on `S` glued from the datum at an object of `C`, i.e. the glued functor on objects.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.chartHom` and `.chartInv`: the
  comparison isomorphism between the sections of `gluedObj A` over an open `V` contained in the
  `i`-th chart image and the sections of `(functor i).obj A` over its preimage.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.localSectionsMap`: the map on
  sections over an open contained in the `i`-th chart image induced by a morphism of `C`, namely
  `(functor i).map φ` conjugated by the comparison isomorphisms.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.gluedMap`: the morphism
  `gluedObj A ⟶ gluedObj B` glued from those local maps.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.glued`: **the glued functor**
  `C ⥤ S.Modules`.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.ChartComparison`: comparison data identifying a
  functor `C ⥤ S.Modules` with the glued one.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.gluedFullSubcategory` and
  `.gluedQuasicoherent`: the glued functor read in a full subcategory of `S.Modules`, in
  particular in `QCoh(𝒪_S)`.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.gluedQuasicoherentOfAffineOpen`:
  the same for charts which are the inclusions of *affine* opens, where the quasi-coherence
  hypothesis of `.gluedQuasicoherent` is discharged.

## Main results

* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.existsUnique_gluedMap`: the
  local maps on sections glue to exactly one morphism `gluedObj A ⟶ gluedObj B`.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.chartHom_gluedMap_app`:
  **the glued functor restricts to the given ones, on sections.** Over an open `V` contained in
  the `i`-th chart image the comparison isomorphism carries the glued map of `φ` to the map
  induced by `(functor i).map φ`. This is the comparison `F ⋙ restrict_i ≅ F i` read on
  sections, and it needs no identification of opens.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.FunctorGlueData.restrictIso`:
  **the comparison isomorphism `glued ⋙ restrictFunctor (f i) ≅ functor i`**, in the category of
  functors `C ⥤ (Y i).Modules`.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.ChartComparison.existsUnique_natTrans` and
  `Stacks.AlgebraicGeometry.ModuleFunctorDescent.ChartComparison.isoGlued`: **uniqueness of the
  glued functor.** A functor `G : C ⥤ S.Modules` equipped with comparison isomorphisms on
  sections which are compatible with the descent datum is isomorphic to `glued`, by exactly one
  natural transformation inducing those comparisons. This is where the 1-morphism layer is used.
* `Stacks.AlgebraicGeometry.ModuleFunctorDescent.isQuasicoherent_gluedObj_of_isAffineOpen`:
  **when the charts are the inclusions of affine opens, the glued object is quasi-coherent as
  soon as the given functors take quasi-coherent values.** Quasi-coherence is local, and on an
  affine scheme a quasi-coherent module has a global presentation, so `restrictIso` transports
  the global presentations of the `(functor i).obj A` to presentations of the restrictions of
  the glued object. This is what makes `.gluedQuasicoherentOfAffineOpen` ask nothing beyond
  quasi-coherence of the given functors, which is the situation of Tag 0GPJ.

## Implementation notes

**Why this reduces to Tag 00AM rather than redoing it.** Stacks 00AM for sheaves of `𝒪`-modules
is formalized in `StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/Basic.lean`, and crucially
it is formalized in the *directed, section-level* form: `Stacks.SheafOfModules.OModuleGlueData`
indexes its local data by the opens `V` of the ambient space together with a proof `V ≤ U i`, and
its comparison isomorphisms `trans i j` are indexed by an open `V` of the ambient space with
`V ≤ U i` and `V ≤ U j`. Both sides of such a comparison are modules over the *same* ring
`𝒪_S(V)`, so the datum carries no transport. This file inherits that: a `FunctorGlueData` is
exactly an `𝒪`-module descent datum in each object of `C`, plus naturality of the comparisons in
that object.

**Where the only transport lives.** The comparison in the form a category theorist wants it,
`glued ⋙ Scheme.Modules.restrictFunctor (f i) ≅ functor i`, cannot avoid the identification
`f i ⁻¹ᵁ (f i ''ᵁ W) = W` for an open `W` of `Y i`: the sections of the left-hand side over `W`
are the sections of `gluedObj A` over `f i ''ᵁ W`, hence — after the section-level comparison —
the sections of `(functor i).obj A` over `f i ⁻¹ᵁ (f i ''ᵁ W)`. That transport is already paid,
once, inside `Stacks.SheafOfModules.ModulesGlueData.chartIso`, which composes with the
counit isomorphism `Scheme.Modules.restrictFunctorAdjCounitIso`. The present file reuses that
isomorphism as the component of `restrictIso`, and its naturality in the object of `C` then costs
exactly one application of `pushHom_app_comp_counitApp`, the naturality of that counit; see the
proof of `chartIso_naturality`. Everything else — the glued
functor itself, its functoriality, and the uniqueness statement — is stated and proved on
sections over opens of `S`, with no transport anywhere.

**One spelling of the module category.** As in the 1-morphism layer, everything is stated for
`AlgebraicGeometry.Scheme.Modules` and its `Γ`-and-`Hom.app` interface. The only point where the
bundled `ModuleCat` picture is needed is the comparison isomorphism of Tag 00AM, and
`sectionsOfHom` is the single bridge.

**No tag is claimed.** This is substrate that the Stacks project never states as a lemma.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.SheafOfModules

namespace Stacks.AlgebraicGeometry.ModuleFunctorDescent

universe u v w

variable {S : Scheme.{u}}

/-! ### Maps on sections -/

/-- **A map of the modules of sections over an open, read on the underlying abelian groups.**
The sections `Γ(M, V)` of a sheaf of modules on a scheme are an object of `AddCommGrpCat`
carrying a `Γ(S, V)`-module structure, while the module of sections `M.val.obj (op V)` is a
bundled `ModuleCat Γ(S, V)`; this is the forgetful functor applied to a morphism of the latter.

It is the only bridge the file needs between the two pictures: the comparison isomorphisms of
Tag 00AM are isomorphisms of bundled modules, and the gluing statement for morphisms of sheaves
of modules is phrased with `AlgebraicGeometry.Scheme.Modules.Hom.app`. -/
def sectionsOfHom {M N : S.Modules} {V : S.Opens}
    (h : M.val.obj (op V) ⟶ N.val.obj (op V)) : Γ(M, V) ⟶ Γ(N, V) :=
  (forget₂ (ModuleCat Γ(S, V)) Ab).map h

/-- The components of a morphism of sheaves of modules, read through `sectionsOfHom`, are its
maps on sections. -/
@[simp] theorem sectionsOfHom_val_app {M N : S.Modules} (φ : M ⟶ N) (V : S.Opens) :
    sectionsOfHom (φ.val.app (op V)) = φ.app V := rfl

/-- `sectionsOfHom` sends the identity to the identity. -/
@[simp] theorem sectionsOfHom_id (M : S.Modules) (V : S.Opens) :
    sectionsOfHom (𝟙 (M.val.obj (op V))) = 𝟙 Γ(M, V) :=
  CategoryTheory.Functor.map_id _ _

/-- `sectionsOfHom` is compatible with composition. -/
@[simp] theorem sectionsOfHom_comp {M N P : S.Modules} {V : S.Opens}
    (h : M.val.obj (op V) ⟶ N.val.obj (op V)) (k : N.val.obj (op V) ⟶ P.val.obj (op V)) :
    sectionsOfHom (h ≫ k) = sectionsOfHom h ≫ sectionsOfHom k :=
  CategoryTheory.Functor.map_comp _ _ _

/-- A map of modules of sections is linear over the functions on the open. -/
theorem sectionsOfHom_smul {M N : S.Modules} {V : S.Opens}
    (h : M.val.obj (op V) ⟶ N.val.obj (op V)) (r : Γ(S, V)) (s : Γ(M, V)) :
    sectionsOfHom h (r • s) = r • sectionsOfHom h s :=
  h.hom.map_smul r s

/-- The two composites of an isomorphism of modules of sections, read on sections, are the
identity: first the `hom`-then-`inv` direction. -/
theorem sectionsOfHom_hom_inv_apply {M N : S.Modules} {V : S.Opens}
    (e : M.val.obj (op V) ≅ N.val.obj (op V)) (s : Γ(M, V)) :
    sectionsOfHom e.inv (sectionsOfHom e.hom s) = s := by
  have h : sectionsOfHom e.hom ≫ sectionsOfHom e.inv = 𝟙 Γ(M, V) := by
    rw [← sectionsOfHom_comp, e.hom_inv_id, sectionsOfHom_id]
  exact congr($(h) s)

/-- The two composites of an isomorphism of modules of sections, read on sections, are the
identity: now the `inv`-then-`hom` direction. -/
theorem sectionsOfHom_inv_hom_apply {M N : S.Modules} {V : S.Opens}
    (e : M.val.obj (op V) ≅ N.val.obj (op V)) (t : Γ(N, V)) :
    sectionsOfHom e.hom (sectionsOfHom e.inv t) = t := by
  have h : sectionsOfHom e.inv ≫ sectionsOfHom e.hom = 𝟙 Γ(N, V) := by
    rw [← sectionsOfHom_comp, e.inv_hom_id, sectionsOfHom_id]
  exact congr($(h) t)

/-! ### Pushing a sheaf of modules on a chart forward to the base -/

variable {Z : Scheme.{u}}

/-- A sheaf of modules on a scheme over `S`, pushed forward to `S`. Its sections over an open `V`
of `S` are the sections of `M` over the preimage of `V`, as a module over `Γ(S, V)`; this is the
spelling `Stacks.SheafOfModules.openSections` uses, and it is what makes every open of `S` carry
its sections over one ring, with no transport. -/
abbrev push (g : Z ⟶ S) (M : Z.Modules) : S.Modules :=
  (Scheme.Modules.pushforward g).obj M

/-- A morphism of sheaves of modules on a scheme over `S`, pushed forward to `S`. -/
abbrev pushHom (g : Z ⟶ S) {M N : Z.Modules} (ψ : M ⟶ N) : push g M ⟶ push g N :=
  (Scheme.Modules.pushforward g).map ψ

/-- The sections of `push g M` over `V` are `Stacks.SheafOfModules.openSections g M V`, the
module of sections the descent data of Tag 00AM is phrased with. -/
theorem push_val_obj (g : Z ⟶ S) (M : Z.Modules) (V : S.Opens) :
    (push g M).val.obj (op V) = openSections g M V := rfl

/-- **The counit of the restriction–pushforward adjunction, on sections.** For an open immersion
`g` and an open `W` of its source, the sections of `push g M` over the image `g ''ᵁ W` are the
sections of `M` over `g ⁻ᵁᵁ (g ''ᵁ W)`; this is the comparison with the sections of `M` over `W`
itself, i.e. the component of `AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso`.

It is spelled with `Γ(push g M, g ''ᵁ W)` as its source rather than with
`Γ((pushforward g ⋙ restrictFunctor g).obj M, W)`. The two are equal by `rfl`, but
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is not reducible, so a composite written with
the second spelling is not type-correct at `implicit` transparency and `rw [Category.assoc]` on
it fails; see the implementation notes. -/
def counitApp (g : Z ⟶ S) [IsOpenImmersion g] (M : Z.Modules) (W : Z.Opens) :
    Γ(push g M, g ''ᵁ W) ⟶ Γ(M, W) :=
  ((Scheme.Modules.restrictFunctorAdjCounitIso g).hom.app M).app W

/-- **The counit is natural, read on sections.** This is
`CategoryTheory.NatTrans.naturality` of `restrictFunctorAdjCounitIso`, evaluated on the sections
over `W`. -/
theorem pushHom_app_comp_counitApp (g : Z ⟶ S) [IsOpenImmersion g] {M N : Z.Modules} (ψ : M ⟶ N)
    (W : Z.Opens) :
    (pushHom g ψ).app (g ''ᵁ W) ≫ counitApp g N W = counitApp g M W ≫ ψ.app W :=
  congrArg (fun χ => Scheme.Modules.Hom.app χ W)
    ((Scheme.Modules.restrictFunctorAdjCounitIso g).hom.naturality ψ)

/-! ### The comparison isomorphism of Tag 00AM, on sections -/

variable {ι : Type u} {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ S} [∀ i, IsOpenImmersion (f i)]

/-- **The comparison isomorphism of Tag 00AM commutes with restriction.** This is
`Stacks.SheafOfModules.OModuleGlueData.chartLinearEquiv_restrict` read through `sectionsOfHom`;
the two statements are the same up to `rfl`. -/
theorem chartSectionsIso_restrict (D : ModulesGlueData S f) (i : ι) {V W : S.Opens}
    (hV : V ≤ (f i).opensRange) (hWV : W ≤ V) (s : Γ(D.glued, V)) :
    sectionsOfHom (D.chartSectionsIso i (hWV.trans hV)).hom
        (D.glued.presheaf.map (homOfLE hWV).op s)
      = (push (f i) (D.mod i)).presheaf.map (homOfLE hWV).op
          (sectionsOfHom (D.chartSectionsIso i hV).hom s) :=
  D.toOModuleGlueData.chartLinearEquiv_restrict i hV hWV s

/-- **The comparison isomorphisms of Tag 00AM are compatible with the descent datum.** Over an
open contained in two chart images, the comparison with the `j`-th member is the comparison with
the `i`-th member followed by `trans i j`. -/
theorem trans_chartSectionsIso (D : ModulesGlueData S f) (i j : ι) {V : S.Opens}
    (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange) (s : Γ(D.glued, V)) :
    D.trans i j hi hj (sectionsOfHom (D.chartSectionsIso i hi).hom s)
      = sectionsOfHom (D.chartSectionsIso j hj).hom s :=
  D.toOModuleGlueData.trans_chartLinearEquiv i j hi hj s

/-! ### Descent data for a functor -/

/-- **Descent data for a functor valued in sheaves of modules.** For a family of open immersions
`f i : Y i ⟶ S`: a functor `C ⥤ (Y i).Modules` for each `i`, together with comparison
isomorphisms between the sections of the `i`-th and the `j`-th member over an open `V` of `S`
contained in both chart images, compatible with restriction, natural in the object of `C`, and
satisfying the cocycle condition.

Both sides of a comparison isomorphism are modules over `𝒪_S(V)` for the *same* open `V` of `S`,
so the datum carries no transport; this is the directed, section-level formulation inherited from
`Stacks.SheafOfModules.ModulesGlueData`. Evaluating at one object of `C` gives exactly such a
datum of sheaves of modules, which is `FunctorGlueData.toModulesGlueData`. -/
structure FunctorGlueData (S : Scheme.{u}) (C : Type v) [Category.{w} C] {ι : Type u}
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ S) [∀ i, IsOpenImmersion (f i)] where
  /-- The functor into the sheaves of modules on the `i`-th chart. -/
  functor : ∀ i, C ⥤ (Y i).Modules
  /-- The comparison isomorphism on the sections over an open `V` of `S` contained in both the
  `i`-th and the `j`-th chart image, linear over the functions on `V`. -/
  trans : ∀ (i j : ι) {V : S.Opens} (_hi : V ≤ (f i).opensRange) (_hj : V ≤ (f j).opensRange)
      (A : C),
    openSections (f i) ((functor i).obj A) V ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))]
      openSections (f j) ((functor j).obj A) V
  /-- The comparison isomorphisms commute with the restriction maps. -/
  trans_map : ∀ (i j : ι) {V W : S.Opens} (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) (hWV : W ≤ V) (A : C)
      (s : Γ(push (f i) ((functor i).obj A), V)),
    trans i j (hWV.trans hi) (hWV.trans hj) A
        ((push (f i) ((functor i).obj A)).presheaf.map (homOfLE hWV).op s)
      = (push (f j) ((functor j).obj A)).presheaf.map (homOfLE hWV).op (trans i j hi hj A s)
  /-- The comparison isomorphisms are natural in the object of `C`. -/
  trans_naturality : ∀ (i j : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) {A B : C} (φ : A ⟶ B)
      (s : Γ(push (f i) ((functor i).obj A), V)),
    trans i j hi hj B ((pushHom (f i) ((functor i).map φ)).app V s)
      = (pushHom (f j) ((functor j).map φ)).app V (trans i j hi hj A s)
  /-- The cocycle condition on the triple overlaps. -/
  trans_trans : ∀ (i j k : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
      (hj : V ≤ (f j).opensRange) (hk : V ≤ (f k).opensRange) (A : C)
      (s : Γ(push (f i) ((functor i).obj A), V)),
    trans j k hj hk A (trans i j hi hj A s) = trans i k hi hk A s

namespace FunctorGlueData

variable {C : Type v} [Category.{w} C]

/-- **Descent data for a functor, evaluated at one object of `C`.** This is descent data of
sheaves of modules in the sense of Tag 00AM, so Tag 00AM glues it. -/
abbrev toModulesGlueData (D : FunctorGlueData S C f) (A : C) : ModulesGlueData S f where
  mod i := (D.functor i).obj A
  trans := fun i j {_V} hi hj => D.trans i j hi hj A
  trans_map := fun i j {_V _W} hi hj hWV s => D.trans_map i j hi hj hWV A s
  trans_trans := fun i j k {_V} hi hj hk s => D.trans_trans i j k hi hj hk A s

/-- The `i`-th sheaf of modules of the descent datum at `A` is `(functor i).obj A`. -/
@[simp] theorem toModulesGlueData_mod (D : FunctorGlueData S C f) (A : C) (i : ι) :
    (D.toModulesGlueData A).mod i = (D.functor i).obj A := rfl

/-- **The glued functor on objects:** the sheaf of modules on `S` glued from the descent datum at
the object `A`, by Tag 00AM. -/
abbrev gluedObj (D : FunctorGlueData S C f) (A : C) : S.Modules :=
  (D.toModulesGlueData A).glued

/-- **The comparison isomorphism on sections, forwards.** Over an open `V` of `S` contained in
the `i`-th chart image it carries the sections of `gluedObj A` to the sections of
`(functor i).obj A` over the preimage of `V`. -/
def chartHom (D : FunctorGlueData S C f) (A : C) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) : Γ(D.gluedObj A, V) ⟶ Γ(push (f i) ((D.functor i).obj A), V) :=
  sectionsOfHom ((D.toModulesGlueData A).chartSectionsIso i hV).hom

/-- **The comparison isomorphism on sections, backwards.** -/
def chartInv (D : FunctorGlueData S C f) (A : C) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) : Γ(push (f i) ((D.functor i).obj A), V) ⟶ Γ(D.gluedObj A, V) :=
  sectionsOfHom ((D.toModulesGlueData A).chartSectionsIso i hV).inv

/-- The inverse comparison on sections undoes the comparison. -/
@[simp] theorem chartInv_chartHom (D : FunctorGlueData S C f) (A : C) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) (s : Γ(D.gluedObj A, V)) :
    D.chartInv A i hV (D.chartHom A i hV s) = s :=
  sectionsOfHom_hom_inv_apply _ s

/-- The comparison on sections undoes the inverse comparison. -/
@[simp] theorem chartHom_chartInv (D : FunctorGlueData S C f) (A : C) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) (t : Γ(push (f i) ((D.functor i).obj A), V)) :
    D.chartHom A i hV (D.chartInv A i hV t) = t :=
  sectionsOfHom_inv_hom_apply _ t

/-- The inverse comparison on sections sends `t` to `s` as soon as the comparison sends `s` to
`t`. -/
private theorem chartInv_eq_of_chartHom_eq (D : FunctorGlueData S C f) (A : C) (i : ι)
    {V : S.Opens} (hV : V ≤ (f i).opensRange) {s : Γ(D.gluedObj A, V)}
    {t : Γ(push (f i) ((D.functor i).obj A), V)} (h : D.chartHom A i hV s = t) :
    D.chartInv A i hV t = s := by
  rw [← h, chartInv_chartHom]

/-- The comparison isomorphism on sections, composed with its inverse. -/
theorem chartHom_comp_chartInv (D : FunctorGlueData S C f) (A : C) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) :
    D.chartHom A i hV ≫ D.chartInv A i hV = 𝟙 Γ(D.gluedObj A, V) := by
  change sectionsOfHom ((D.toModulesGlueData A).chartSectionsIso i hV).hom ≫
      sectionsOfHom ((D.toModulesGlueData A).chartSectionsIso i hV).inv = _
  rw [← sectionsOfHom_comp, Iso.hom_inv_id, sectionsOfHom_id]

/-- The inverse comparison isomorphism on sections, composed with the comparison. -/
theorem chartInv_comp_chartHom (D : FunctorGlueData S C f) (A : C) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) :
    D.chartInv A i hV ≫ D.chartHom A i hV
      = 𝟙 Γ(push (f i) ((D.functor i).obj A), V) := by
  change sectionsOfHom ((D.toModulesGlueData A).chartSectionsIso i hV).inv ≫
      sectionsOfHom ((D.toModulesGlueData A).chartSectionsIso i hV).hom = _
  rw [← sectionsOfHom_comp, Iso.inv_hom_id, sectionsOfHom_id]

/-- The comparison isomorphism on sections is invertible. -/
instance isIso_chartHom (D : FunctorGlueData S C f) (A : C) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) : IsIso (D.chartHom A i hV) :=
  ⟨⟨D.chartInv A i hV, D.chartHom_comp_chartInv A i hV, D.chartInv_comp_chartHom A i hV⟩⟩

/-- The inverse comparison isomorphism on sections is invertible. -/
instance isIso_chartInv (D : FunctorGlueData S C f) (A : C) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) : IsIso (D.chartInv A i hV) :=
  ⟨⟨D.chartHom A i hV, D.chartInv_comp_chartHom A i hV, D.chartHom_comp_chartInv A i hV⟩⟩

/-- The comparison isomorphism on sections is linear over the functions on the open. -/
theorem chartHom_smul (D : FunctorGlueData S C f) (A : C) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) (r : Γ(S, V)) (s : Γ(D.gluedObj A, V)) :
    D.chartHom A i hV (r • s) = r • D.chartHom A i hV s :=
  sectionsOfHom_smul _ r s

/-- The inverse comparison isomorphism on sections is linear over the functions on the open. -/
theorem chartInv_smul (D : FunctorGlueData S C f) (A : C) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) (r : Γ(S, V))
    (t : Γ(push (f i) ((D.functor i).obj A), V)) :
    D.chartInv A i hV (r • t) = r • D.chartInv A i hV t :=
  sectionsOfHom_smul _ r t

/-- The comparison isomorphism commutes with restriction. -/
theorem chartHom_res (D : FunctorGlueData S C f) (A : C) (i : ι) {V W : S.Opens}
    (hV : V ≤ (f i).opensRange) (hWV : W ≤ V) (s : Γ(D.gluedObj A, V)) :
    D.chartHom A i (hWV.trans hV) ((D.gluedObj A).presheaf.map (homOfLE hWV).op s)
      = (push (f i) ((D.functor i).obj A)).presheaf.map (homOfLE hWV).op (D.chartHom A i hV s) :=
  chartSectionsIso_restrict (D.toModulesGlueData A) i hV hWV s

/-- The inverse comparison isomorphism commutes with restriction. -/
theorem chartInv_res (D : FunctorGlueData S C f) (A : C) (i : ι) {V W : S.Opens}
    (hV : V ≤ (f i).opensRange) (hWV : W ≤ V)
    (t : Γ(push (f i) ((D.functor i).obj A), V)) :
    D.chartInv A i (hWV.trans hV)
        ((push (f i) ((D.functor i).obj A)).presheaf.map (homOfLE hWV).op t)
      = (D.gluedObj A).presheaf.map (homOfLE hWV).op (D.chartInv A i hV t) :=
  D.chartInv_eq_of_chartHom_eq A i (hWV.trans hV)
    (by rw [D.chartHom_res A i hV hWV, chartHom_chartInv])

/-- The comparison isomorphism is compatible with the descent datum: the comparison with the
`j`-th member is the comparison with the `i`-th member followed by `trans i j`. -/
theorem trans_chartHom (D : FunctorGlueData S C f) (A : C) (i j : ι) {V : S.Opens}
    (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange) (s : Γ(D.gluedObj A, V)) :
    D.trans i j hi hj A (D.chartHom A i hi s) = D.chartHom A j hj s :=
  trans_chartSectionsIso (D.toModulesGlueData A) i j hi hj s

/-- The inverse comparison isomorphism absorbs `trans i j`. -/
theorem chartInv_trans (D : FunctorGlueData S C f) (A : C) (i j : ι) {V : S.Opens}
    (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange)
    (t : Γ(push (f i) ((D.functor i).obj A), V)) :
    D.chartInv A j hj (D.trans i j hi hj A t) = D.chartInv A i hi t :=
  D.chartInv_eq_of_chartHom_eq A j hj (by rw [← trans_chartHom _ _ i, chartHom_chartInv])

/-! ### The glued functor -/

/-- **The map on sections induced by a morphism of `C`, over an open contained in the `i`-th
chart image:** the map `(functor i).map φ` induces on sections, conjugated by the comparison
isomorphisms. -/
def localSectionsMap (D : FunctorGlueData S C f) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) {A B : C} (φ : A ⟶ B) :
    Γ(D.gluedObj A, V) ⟶ Γ(D.gluedObj B, V) :=
  D.chartHom A i hV ≫ (pushHom (f i) ((D.functor i).map φ)).app V ≫ D.chartInv B i hV

/-- The local map on sections is the comparison, then the map induced by `(functor i).map φ`,
then the inverse comparison. -/
@[simp] theorem localSectionsMap_apply (D : FunctorGlueData S C f) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) {A B : C} (φ : A ⟶ B) (s : Γ(D.gluedObj A, V)) :
    D.localSectionsMap i hV φ s
      = D.chartInv B i hV ((pushHom (f i) ((D.functor i).map φ)).app V (D.chartHom A i hV s)) :=
  rfl

/-- The local maps on sections are linear over the functions on the open. -/
theorem localSectionsMap_smul (D : FunctorGlueData S C f) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) {A B : C} (φ : A ⟶ B) (r : Γ(S, V)) (s : Γ(D.gluedObj A, V)) :
    D.localSectionsMap i hV φ (r • s) = r • D.localSectionsMap i hV φ s := by
  rw [localSectionsMap_apply, localSectionsMap_apply, D.chartHom_smul,
    Scheme.Modules.Hom.app_smul, D.chartInv_smul]

/-- The local map on sections of an identity is the identity. -/
theorem localSectionsMap_id (D : FunctorGlueData S C f) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) (A : C) :
    D.localSectionsMap i hV (𝟙 A) = 𝟙 Γ(D.gluedObj A, V) := by
  ext s
  rw [localSectionsMap_apply, CategoryTheory.Functor.map_id,
    show pushHom (f i) (𝟙 ((D.functor i).obj A)) = 𝟙 _ from CategoryTheory.Functor.map_id _ _,
    Scheme.Modules.Hom.id_app]
  exact D.chartInv_chartHom A i hV s

/-- The local maps on sections are compatible with composition. -/
theorem localSectionsMap_comp (D : FunctorGlueData S C f) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) {A B E : C} (φ : A ⟶ B) (ψ : B ⟶ E) :
    D.localSectionsMap i hV (φ ≫ ψ)
      = D.localSectionsMap i hV φ ≫ D.localSectionsMap i hV ψ := by
  ext s
  simp only [localSectionsMap_apply, ConcreteCategory.comp_apply, chartHom_chartInv,
    CategoryTheory.Functor.map_comp, Scheme.Modules.Hom.comp_app]

/-- The local maps on sections commute with the restriction maps. -/
theorem localSectionsMap_res (D : FunctorGlueData S C f) (i : ι) {V W : S.Opens}
    (hV : V ≤ (f i).opensRange) (hWV : W ≤ V) {A B : C} (φ : A ⟶ B)
    (s : Γ(D.gluedObj A, V)) :
    D.localSectionsMap i (hWV.trans hV) φ ((D.gluedObj A).presheaf.map (homOfLE hWV).op s)
      = (D.gluedObj B).presheaf.map (homOfLE hWV).op (D.localSectionsMap i hV φ s) := by
  rw [localSectionsMap_apply, localSectionsMap_apply, D.chartHom_res A i hV hWV,
    ← ModuleLimits.Hom_app_presheaf_map (pushHom (f i) ((D.functor i).map φ)) hWV,
    D.chartInv_res B i hV hWV]

/-- **The local maps on sections agree on the overlaps.** Over an open contained in two chart
images the two descriptions of the map induced by `φ` coincide; this is where the naturality of
the comparison isomorphisms in the object of `C` is used. -/
theorem localSectionsMap_agree (D : FunctorGlueData S C f) (i j : ι) {V : S.Opens}
    (hi : V ≤ (f i).opensRange) (hj : V ≤ (f j).opensRange) {A B : C} (φ : A ⟶ B) :
    D.localSectionsMap i hi φ = D.localSectionsMap j hj φ := by
  ext s
  rw [localSectionsMap_apply, localSectionsMap_apply, ← D.trans_chartHom A i j hi hj s,
    ← D.trans_naturality i j hi hj φ (D.chartHom A i hi s), D.chartInv_trans B i j hi hj]

/-- **The local maps on sections glue to exactly one morphism of sheaves of modules.** This is
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover_app` for the family
`localSectionsMap`. -/
theorem existsUnique_gluedMap (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) {A B : C} (φ : A ⟶ B) :
    ∃! χ : D.gluedObj A ⟶ D.gluedObj B, ∀ (i : ι) (V : S.Opens) (hV : V ≤ (f i).opensRange),
      χ.app V = D.localSectionsMap i hV φ :=
  ModuleHomGlue.existsUnique_hom_of_cover_app hU (fun i _ hV => D.localSectionsMap i hV φ)
    (fun i _ hV => D.localSectionsMap_smul i hV φ)
    (fun i _ _ hV hWV => D.localSectionsMap_res i hV hWV φ)
    (fun i j _ hi hj => D.localSectionsMap_agree i j hi hj φ)

/-- **The glued functor on morphisms:** the morphism `gluedObj A ⟶ gluedObj B` glued from the
local maps on sections. -/
def gluedMap (D : FunctorGlueData S C f) (hU : IsOpenCover fun i => (f i).opensRange)
    {A B : C} (φ : A ⟶ B) : D.gluedObj A ⟶ D.gluedObj B :=
  (D.existsUnique_gluedMap hU φ).choose

/-- On sections over an open contained in the `i`-th chart image, the glued morphism is the local
map on sections. -/
@[simp] theorem gluedMap_app (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) {A B : C} (φ : A ⟶ B) (i : ι) (V : S.Opens)
    (hV : V ≤ (f i).opensRange) :
    (D.gluedMap hU φ).app V = D.localSectionsMap i hV φ :=
  (D.existsUnique_gluedMap hU φ).choose_spec.1 i V hV

/-- The glued morphism is the only one restricting to the local maps on sections. -/
theorem eq_gluedMap (D : FunctorGlueData S C f) (hU : IsOpenCover fun i => (f i).opensRange)
    {A B : C} (φ : A ⟶ B) (χ : D.gluedObj A ⟶ D.gluedObj B)
    (hχ : ∀ (i : ι) (V : S.Opens) (hV : V ≤ (f i).opensRange),
      χ.app V = D.localSectionsMap i hV φ) :
    χ = D.gluedMap hU φ :=
  (D.existsUnique_gluedMap hU φ).choose_spec.2 χ hχ

/-- **The functor `C ⥤ S.Modules` glued from the descent datum.** Its value at `A` is the sheaf
of modules glued from the datum at `A`, and its value at `φ` is the morphism glued from the local
maps on sections.

Functoriality is not proved by hand: both `gluedMap hU (𝟙 A) = 𝟙` and
`gluedMap hU (φ ≫ ψ) = gluedMap hU φ ≫ gluedMap hU ψ` hold because the two sides agree on
sections over every open contained in a chart image, hence by the uniqueness half of
`existsUnique_gluedMap`. -/
def glued (D : FunctorGlueData S C f) (hU : IsOpenCover fun i => (f i).opensRange) :
    C ⥤ S.Modules where
  obj A := D.gluedObj A
  map φ := D.gluedMap hU φ
  map_id A := by
    refine (D.eq_gluedMap hU (𝟙 A) (𝟙 (D.gluedObj A)) fun i V hV => ?_).symm
    rw [Scheme.Modules.Hom.id_app, D.localSectionsMap_id i hV A]
  map_comp {A B E} φ ψ := by
    refine (D.eq_gluedMap hU (φ ≫ ψ) (D.gluedMap hU φ ≫ D.gluedMap hU ψ) fun i V hV => ?_).symm
    rw [Scheme.Modules.Hom.comp_app, D.gluedMap_app hU φ i V hV, D.gluedMap_app hU ψ i V hV,
      D.localSectionsMap_comp i hV φ ψ]

/-- The glued functor sends `A` to `gluedObj A`. -/
@[simp] theorem glued_obj (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) (A : C) :
    (D.glued hU).obj A = D.gluedObj A := rfl

/-- The glued functor sends `φ` to `gluedMap hU φ`. -/
@[simp] theorem glued_map (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) {A B : C} (φ : A ⟶ B) :
    (D.glued hU).map φ = D.gluedMap hU φ := rfl

/-! ### The comparison with the given functors -/

/-- **The glued functor restricts to the given ones, on sections.** Over an open `V` of `S`
contained in the `i`-th chart image, the comparison isomorphism carries the glued map of `φ` to
the map induced by `(functor i).map φ`.

This is the comparison isomorphism `glued ⋙ restrict_i ≅ functor i`, naturality included, in the
form that needs no identification of opens: both sides are maps of `Γ(S, V)`-modules for the same
open `V` of `S`. -/
theorem chartHom_gluedMap_app (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) {A B : C} (φ : A ⟶ B) (s : Γ(D.gluedObj A, V)) :
    D.chartHom B i hV ((D.gluedMap hU φ).app V s)
      = (pushHom (f i) ((D.functor i).map φ)).app V (D.chartHom A i hV s) := by
  rw [D.gluedMap_app hU φ i V hV, localSectionsMap_apply, chartHom_chartInv]

/-- The same statement as a commuting square of maps on sections. -/
theorem chartHom_comp_gluedMap (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) {A B : C} (φ : A ⟶ B) :
    (D.gluedMap hU φ).app V ≫ D.chartHom B i hV
      = D.chartHom A i hV ≫ (pushHom (f i) ((D.functor i).map φ)).app V := by
  ext s
  simpa only [ConcreteCategory.comp_apply] using D.chartHom_gluedMap_app hU i hV φ s

/-- The component of the comparison isomorphism of Tag 00AM on the sections over an open of the
`i`-th chart: the comparison on sections over its image, followed by the counit. -/
theorem chartIso_hom_app (D : FunctorGlueData S C f) (A : C) (i : ι) (W : (Y i).Opens) :
    ((D.toModulesGlueData A).chartIso i).hom.app W
      = D.chartHom A i ((f i).image_le_opensRange W) ≫ counitApp (f i) ((D.functor i).obj A) W :=
  rfl

/-- **The comparison isomorphism of Tag 00AM is natural in the object of `C`.** On the sections
over an open `W` of the `i`-th chart this is the section-level comparison
`chartHom_comp_gluedMap` over the image of `W`, followed by the naturality of the counit. -/
theorem chartIso_naturality (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) (i : ι) {A B : C} (φ : A ⟶ B) :
    (Scheme.Modules.restrictFunctor (f i)).map (D.gluedMap hU φ) ≫
        ((D.toModulesGlueData B).chartIso i).hom
      = ((D.toModulesGlueData A).chartIso i).hom ≫ (D.functor i).map φ := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  change (D.gluedMap hU φ).app ((f i) ''ᵁ W) ≫
        (D.chartHom B i ((f i).image_le_opensRange W) ≫ counitApp (f i) ((D.functor i).obj B) W)
      = (D.chartHom A i ((f i).image_le_opensRange W) ≫ counitApp (f i) ((D.functor i).obj A) W)
        ≫ ((D.functor i).map φ).app W
  rw [← Category.assoc, D.chartHom_comp_gluedMap hU i ((f i).image_le_opensRange W) φ,
    Category.assoc, Category.assoc,
    pushHom_app_comp_counitApp (f i) ((D.functor i).map φ) W]

/-- **The glued functor restricts along each chart to the functor it was glued from.** This is
the comparison isomorphism `glued ⋙ restrictFunctor (f i) ≅ functor i` in the category of
functors `C ⥤ (Y i).Modules`.

Its component at `A` is the comparison isomorphism of Tag 00AM,
`Stacks.SheafOfModules.ModulesGlueData.chartIso`, which is where the identification
`f i ⁻¹ᵁ (f i ''ᵁ W) = W` is paid for. Naturality in `A` then costs one application of
`pushHom_app_comp_counitApp` on top of the section-level comparison
`chartHom_gluedMap_app`; see the implementation notes. -/
def restrictIso (D : FunctorGlueData S C f) (hU : IsOpenCover fun i => (f i).opensRange) (i : ι) :
    D.glued hU ⋙ Scheme.Modules.restrictFunctor (f i) ≅ D.functor i :=
  NatIso.ofComponents (fun A => (D.toModulesGlueData A).chartIso i)
    fun {_A _B} φ => D.chartIso_naturality hU i φ

/-- The component at `A` of `restrictIso` is the comparison isomorphism `chartIso i` of the
descent datum at `A`. -/
@[simp] theorem restrictIso_hom_app (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) (i : ι) (A : C) :
    (D.restrictIso hU i).hom.app A = ((D.toModulesGlueData A).chartIso i).hom :=
  rfl

/-- The glued morphism transported through the inverse comparison isomorphism: the inverse
comparison intertwines the glued map with the map induced by `(functor i).map φ`. -/
theorem gluedMap_app_chartInv (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) (i : ι) {V : S.Opens}
    (hV : V ≤ (f i).opensRange) {A B : C} (φ : A ⟶ B)
    (t : Γ(push (f i) ((D.functor i).obj A), V)) :
    (D.gluedMap hU φ).app V (D.chartInv A i hV t)
      = D.chartInv B i hV ((pushHom (f i) ((D.functor i).map φ)).app V t) :=
  (D.chartInv_eq_of_chartHom_eq B i _
    (by rw [chartHom_gluedMap_app, chartHom_chartInv])).symm

end FunctorGlueData

/-! ### Uniqueness of the glued functor -/

/-- **Comparison data identifying a functor with the glued one.** For a functor
`G : C ⥤ S.Modules`: an invertible comparison between the sections of `G.obj A` over an open `V`
of `S` contained in the `i`-th chart image and the sections of `(functor i).obj A` over the
preimage of `V`, linear over the functions on `V`, compatible with restriction, natural in the
object of `C`, and compatible with the descent datum.

This is exactly the data `FunctorGlueData.chartHom` carries for the glued functor itself, and
`ChartComparison.isoGlued` says that any functor carrying it is isomorphic to the glued one. As
everywhere else in this file the data is indexed by the opens of `S`, so it needs no
identification of opens. -/
structure ChartComparison {C : Type v} [Category.{w} C] (D : FunctorGlueData S C f)
    (G : C ⥤ S.Modules) where
  /-- The comparison on the sections over an open contained in the `i`-th chart image. -/
  hom : ∀ (A : C) (i : ι) {V : S.Opens}, V ≤ (f i).opensRange →
    (Γ(G.obj A, V) ⟶ Γ(push (f i) ((D.functor i).obj A), V))
  /-- Each comparison is invertible. -/
  isIso_hom : ∀ (A : C) (i : ι) {V : S.Opens} (hV : V ≤ (f i).opensRange), IsIso (hom A i hV)
  /-- Each comparison is linear over the functions on the open. -/
  hom_smul : ∀ (A : C) (i : ι) {V : S.Opens} (hV : V ≤ (f i).opensRange) (r : Γ(S, V))
    (s : Γ(G.obj A, V)), hom A i hV (r • s) = r • hom A i hV s
  /-- Each comparison commutes with the restriction maps. -/
  hom_res : ∀ (A : C) (i : ι) {V W : S.Opens} (hV : V ≤ (f i).opensRange) (hWV : W ≤ V)
    (s : Γ(G.obj A, V)),
    hom A i (hWV.trans hV) ((G.obj A).presheaf.map (homOfLE hWV).op s)
      = (push (f i) ((D.functor i).obj A)).presheaf.map (homOfLE hWV).op (hom A i hV s)
  /-- The comparisons are natural in the object of `C`. -/
  hom_naturality : ∀ {A B : C} (φ : A ⟶ B) (i : ι) {V : S.Opens} (hV : V ≤ (f i).opensRange)
    (s : Γ(G.obj A, V)),
    hom B i hV ((G.map φ).app V s) = (pushHom (f i) ((D.functor i).map φ)).app V (hom A i hV s)
  /-- The comparisons are compatible with the descent datum. -/
  trans_hom : ∀ (A : C) (i j : ι) {V : S.Opens} (hi : V ≤ (f i).opensRange)
    (hj : V ≤ (f j).opensRange) (s : Γ(G.obj A, V)),
    D.trans i j hi hj A (hom A i hi s) = hom A j hj s

namespace ChartComparison

variable {C : Type v} [Category.{w} C] {D : FunctorGlueData S C f} {G : C ⥤ S.Modules}

/-- **The comparison transformation `G ⟶ glued` over the `i`-th chart image**, as local data for
the 1-morphism layer: the comparison of `e` followed by the inverse comparison of the glued
functor. -/
def localNatTrans (e : ChartComparison D G) (hU : IsOpenCover fun i => (f i).opensRange)
    (i : ι) :
    ModuleNatTransGlue.LocalNatTrans G (D.glued hU) ((f i).opensRange) where
  app A V hV := e.hom A i hV ≫ D.chartInv A i hV
  app_smul A V hV r s := by
    change D.chartInv A i hV (e.hom A i hV (r • s)) = r • D.chartInv A i hV (e.hom A i hV s)
    rw [e.hom_smul, D.chartInv_smul]
  app_map A V W hV hWV s := by
    change D.chartInv A i (hWV.trans hV)
          (e.hom A i (hWV.trans hV) ((G.obj A).presheaf.map (homOfLE hWV).op s))
        = (D.gluedObj A).presheaf.map (homOfLE hWV).op (D.chartInv A i hV (e.hom A i hV s))
    rw [e.hom_res, D.chartInv_res]
  app_naturality := fun {A B} φ V hV s => by
    change D.chartInv B i hV (e.hom B i hV ((G.map φ).app V s))
        = (D.gluedMap hU φ).app V (D.chartInv A i hV (e.hom A i hV s))
    rw [e.hom_naturality, D.gluedMap_app_chartInv hU i hV φ]

/-- On sections over an open contained in the `i`-th chart image, `localNatTrans` is the
comparison of `e` followed by the inverse comparison of the glued functor. -/
@[simp] theorem localNatTrans_app (e : ChartComparison D G)
    (hU : IsOpenCover fun i => (f i).opensRange) (i : ι) (A : C) (V : S.Opens)
    (hV : V ≤ (f i).opensRange) :
    (e.localNatTrans hU i).app A V hV = e.hom A i hV ≫ D.chartInv A i hV :=
  rfl

/-- **The comparison transformations form a compatible family over the cover**, because `e` and
the glued functor's own comparisons are compatible with the same descent datum. -/
def compatibleFamily (e : ChartComparison D G)
    (hU : IsOpenCover fun i => (f i).opensRange) :
    ModuleNatTransGlue.CompatibleFamily G (D.glued hU) (fun i => (f i).opensRange) where
  trans i := e.localNatTrans hU i
  agree A i j V hVi hVj := by
    ext s
    change D.chartInv A i hVi (e.hom A i hVi s) = D.chartInv A j hVj (e.hom A j hVj s)
    rw [← e.trans_hom A i j hVi hVj, D.chartInv_trans]

/-- **A functor carrying comparison data comes with exactly one natural transformation to the
glued functor inducing it.** This is the 1-morphism layer,
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.CompatibleFamily.existsUnique_natTrans`, applied to
the compatible family of comparisons. -/
theorem existsUnique_natTrans (e : ChartComparison D G)
    (hU : IsOpenCover fun i => (f i).opensRange) :
    ∃! α : G ⟶ D.glued hU, ∀ i : ι,
      ModuleNatTransGlue.LocalNatTrans.ofNatTrans α ((f i).opensRange) = e.localNatTrans hU i :=
  (e.compatibleFamily hU).existsUnique_natTrans hU

/-- The natural transformation `G ⟶ glued` glued from the comparison data. -/
def natTrans (e : ChartComparison D G) (hU : IsOpenCover fun i => (f i).opensRange) :
    G ⟶ D.glued hU :=
  (e.compatibleFamily hU).glue hU

/-- On sections over an open contained in the `i`-th chart image, the component of `natTrans` at
`A` is the comparison of `e` followed by the inverse comparison of the glued functor. -/
@[simp] theorem natTrans_app_app (e : ChartComparison D G)
    (hU : IsOpenCover fun i => (f i).opensRange) (A : C) (i : ι) (V : S.Opens)
    (hV : V ≤ (f i).opensRange) :
    ((e.natTrans hU).app A).app V = e.hom A i hV ≫ D.chartInv A i hV :=
  (e.compatibleFamily hU).glueApp_app hU A i V hV

/-- **The glued transformation is an isomorphism**, since each comparison is. -/
theorem isIso_natTrans (e : ChartComparison D G)
    (hU : IsOpenCover fun i => (f i).opensRange) : IsIso (e.natTrans hU) :=
  (e.compatibleFamily hU).isIso_glue hU fun A i V hV => by
    have := e.isIso_hom A i hV
    change IsIso (e.hom A i hV ≫ D.chartInv A i hV)
    infer_instance

/-- **Uniqueness of the glued functor.** A functor `G : C ⥤ S.Modules` carrying comparison data
for the descent datum is isomorphic to the glued functor; the isomorphism is the unique natural
transformation inducing the comparisons. -/
def isoGlued (e : ChartComparison D G) (hU : IsOpenCover fun i => (f i).opensRange) :
    G ≅ D.glued hU :=
  haveI := e.isIso_natTrans hU
  asIso (e.natTrans hU)

/-- The forward morphism of `isoGlued` is `natTrans`. -/
@[simp] theorem isoGlued_hom (e : ChartComparison D G)
    (hU : IsOpenCover fun i => (f i).opensRange) : (e.isoGlued hU).hom = e.natTrans hU :=
  rfl

end ChartComparison

/-- **The glued functor carries its own comparison data**, namely
`FunctorGlueData.chartHom`. Together with `ChartComparison.isoGlued` this says that the glued
functor is the unique one, up to isomorphism, restricting to the given ones. -/
def FunctorGlueData.chartComparison {C : Type v} [Category.{w} C] (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) : ChartComparison D (D.glued hU) where
  hom := fun A i {_V} hV => D.chartHom A i hV
  isIso_hom := fun A i {_V} hV => D.isIso_chartHom A i hV
  hom_smul := fun A i {_V} hV r s => D.chartHom_smul A i hV r s
  hom_res := fun A i {_V _W} hV hWV s => D.chartHom_res A i hV hWV s
  hom_naturality := fun {_A _B} φ i {_V} hV s => D.chartHom_gluedMap_app hU i hV φ s
  trans_hom := fun A i j {_V} hi hj s => D.trans_chartHom A i j hi hj s

/-! ### The glued functor into a full subcategory, and the quasi-coherent case -/

section FullSubcategory

variable {C : Type v} [Category.{w} C]

/-- **The glued functor, read in a full subcategory of `S.Modules`.** Given a property of the
objects of `S.Modules` which the glued sheaf of modules has at every object of `C`, the glued
functor factors through the corresponding full subcategory. Composing with the inclusion returns
`FunctorGlueData.glued` on the nose, so every statement above transfers. -/
def FunctorGlueData.gluedFullSubcategory (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) (P : ObjectProperty S.Modules)
    (hP : ∀ A : C, P (D.gluedObj A)) : C ⥤ P.FullSubcategory :=
  P.lift (D.glued hU) hP

/-- Composing the full-subcategory form of the glued functor with the inclusion returns the
glued functor. -/
@[simp] theorem FunctorGlueData.gluedFullSubcategory_comp_ι (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange) (P : ObjectProperty S.Modules)
    (hP : ∀ A : C, P (D.gluedObj A)) :
    D.gluedFullSubcategory hU P hP ⋙ P.ι = D.glued hU :=
  rfl

/-- **The glued functor into the quasi-coherent modules.** If the glued sheaf of modules is
quasi-coherent at every object of `C` — quasi-coherence being a local condition, this is what the
quasi-coherence of the given functors buys — then the glued functor lands in `QCoh(𝒪_S)`.

This is the shape step 3 of the Gabriel–Rosenberg reconstruction theorem (Tag 0GPJ) consumes: a
functor `QCoh(𝒪_X) ⥤ QCoh(𝒪_{V i})` on each member of an affine open cover of `Y`, assembled
into a single `QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`. The target is spelled
`(SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory`, the `QCoh(𝒪_S)` of the rest of
the library, with no coercion. -/
def FunctorGlueData.gluedQuasicoherent (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange)
    (hQ : ∀ A : C, (D.gluedObj A).IsQuasicoherent) :
    C ⥤ (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
  D.gluedFullSubcategory hU (ModuleNatTransGlue.quasicoherent S) hQ

/-- Composing the quasi-coherent form of the glued functor with the inclusion returns the glued
functor; in particular `FunctorGlueData.restrictIso` is the comparison for it too. -/
@[simp] theorem FunctorGlueData.gluedQuasicoherent_comp_ι (D : FunctorGlueData S C f)
    (hU : IsOpenCover fun i => (f i).opensRange)
    (hQ : ∀ A : C, (D.gluedObj A).IsQuasicoherent) :
    D.gluedQuasicoherent hU hQ ⋙ (ModuleNatTransGlue.quasicoherent S).ι = D.glued hU :=
  rfl

end FullSubcategory

/-! ### Affine charts: quasi-coherence of the glued object is automatic -/

section AffineCharts

variable {C : Type v} [Category.{w} C] {ι : Type u}

/-- The family of images of the inclusions of a family of opens is the family itself. -/
theorem opensRange_ι_eq (U : ι → S.Opens) : (fun i ↦ (U i).ι.opensRange) = U :=
  funext fun i ↦ (U i).opensRange_ι

/-- Covering by a family of opens is covering by the images of their inclusions. -/
theorem isOpenCover_opensRange_ι_iff (U : ι → S.Opens) :
    IsOpenCover (fun i ↦ (U i).ι.opensRange) ↔ IsOpenCover U := by
  rw [opensRange_ι_eq]

/-- **The glued object is quasi-coherent when the charts are affine opens.** This discharges the
hypothesis `hQ` of `FunctorGlueData.gluedQuasicoherent` in the situation of the Gabriel–Rosenberg
reconstruction theorem (Tag 0GPJ), where the charts are the inclusions of the members of an
affine open cover.

Quasi-coherence is local
(`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations`), so it is enough
to present the restriction of the glued object to each chart.  That restriction is
`(functor i).obj A` by `FunctorGlueData.restrictIso`, and on an affine scheme a quasi-coherent
module has a global presentation
(`Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec`). -/
theorem isQuasicoherent_gluedObj_of_isAffineOpen {U : ι → S.Opens}
    (D : FunctorGlueData S C fun i ↦ (U i).ι)
    (hU : IsOpenCover fun i ↦ ((U i).ι).opensRange) (hUaff : ∀ i, IsAffineOpen (U i))
    (hQ : ∀ (i : ι) (A : C), ((D.functor i).obj A).IsQuasicoherent) (A : C) :
    (D.gluedObj A).IsQuasicoherent := by
  refine Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_of_presentations
    (D.gluedObj A) U ((isOpenCover_opensRange_ι_iff U).mp hU) fun i ↦ ?_
  have : IsAffine (U i).toScheme := hUaff i
  have : ((D.functor i).obj A).IsQuasicoherent := hQ i A
  exact Stacks.AlgebraicGeometry.AffinePushforward.presentationOfIso
    ((D.restrictIso hU i).app A).symm
    (Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec
      (U i).toScheme.isoSpec ((D.functor i).obj A)).some

/-- **The glued functor into the quasi-coherent modules, for affine charts.** This is
`FunctorGlueData.gluedQuasicoherent` with its quasi-coherence hypothesis discharged by
`isQuasicoherent_gluedObj_of_isAffineOpen`: all that is asked of the data is that each of the
given functors take quasi-coherent values. -/
def FunctorGlueData.gluedQuasicoherentOfAffineOpen {U : ι → S.Opens}
    (D : FunctorGlueData S C fun i ↦ (U i).ι)
    (hU : IsOpenCover fun i ↦ ((U i).ι).opensRange) (hUaff : ∀ i, IsAffineOpen (U i))
    (hQ : ∀ (i : ι) (A : C), ((D.functor i).obj A).IsQuasicoherent) :
    C ⥤ (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory :=
  D.gluedQuasicoherent hU (isQuasicoherent_gluedObj_of_isAffineOpen D hU hUaff hQ)

/-- Composing the affine-chart form of the glued quasi-coherent functor with the inclusion
returns the glued functor, so `FunctorGlueData.restrictIso` is the comparison for it too. -/
@[simp] theorem FunctorGlueData.gluedQuasicoherentOfAffineOpen_comp_ι {U : ι → S.Opens}
    (D : FunctorGlueData S C fun i ↦ (U i).ι)
    (hU : IsOpenCover fun i ↦ ((U i).ι).opensRange) (hUaff : ∀ i, IsAffineOpen (U i))
    (hQ : ∀ (i : ι) (A : C), ((D.functor i).obj A).IsQuasicoherent) :
    D.gluedQuasicoherentOfAffineOpen hU hUaff hQ ⋙ (ModuleNatTransGlue.quasicoherent S).ι =
      D.glued hU :=
  rfl

end AffineCharts

end Stacks.AlgebraicGeometry.ModuleFunctorDescent

end
