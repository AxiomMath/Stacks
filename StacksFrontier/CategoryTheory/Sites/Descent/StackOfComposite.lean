module

public import Mathlib.CategoryTheory.Sites.Descent.Precoverage
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiModuleChartComparison

/-!
# The stack condition for a composite covering family

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor, let `g i : V i ⟶ S` be a family of
morphisms, and for each `i` let `h i k : U i k ⟶ V i` be a family over `V i`. The *composite*
family is the family indexed by pairs whose member at `⟨i, k⟩` is `h i k ≫ g i`
(`CategoryTheory.Pseudofunctor.DescentData.bindFamily`); it generates the sieve that Mathlib's
`CategoryTheory.Presieve.bindOfArrows` describes, by
`CategoryTheory.Presieve.bindOfArrows_ofArrows`.

This file proves that effective descent holds along the composite family as soon as it holds
along `g` and along each `h i` — equivalently, that the stack condition is **local on the
base**. That statement is *not* in Mathlib and not elsewhere in this
library: Mathlib's refinement results (`CategoryTheory.Pseudofunctor.IsStackFor.of_le`, `.of_le'`
and `CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le`), and this
library's Stacks 0GEA (`CategoryTheory.Functor.isEquivalence_toFamilyDescentDatum_of_homOver`),
all carry effective descent from a *finer* family to a *coarser* one at a **fixed base**, which
is the opposite direction. The morphism-descent half is already local on the base
(`CategoryTheory.Pseudofunctor.isPrestackFor_of_cover`); the object half is what is missing.

## Main definitions and results

* `CategoryTheory.Pseudofunctor.DescentData.restrictBase`: a descent datum relative to the
  composite family restricts, over each `V i`, to a descent datum relative to `h i`. This is
  where the stack condition for `h i` is applied, producing an object `N i` over `V i`.
* `CategoryTheory.Pseudofunctor.DescentData.BindGlue.locIso`: the local comparison between the
  inverse image of `N i` and the component of the given datum, along a factorization through the
  fine family, with its compatibility with further pullback (`pullHom_locIso_hom`,
  `pullHom_locIso_inv`).
* `CategoryTheory.Pseudofunctor.DescentData.BindGlue.mor`: the local section of the presheaf of
  morphisms that the gluing amalgamates, with `pullHom_mor` its compatibility with pullback and
  `mor_unique` its independence of the chosen factorizations.
* `CategoryTheory.Pseudofunctor.DescentData.BindGlue.bindSieve` and `bindSieve_mem`: the covering
  sieve of morphisms along which both structure morphisms factor through the fine families.
* `CategoryTheory.Pseudofunctor.DescentData.BindGlue.isSheafFor_presheafHom`: the descent of
  morphisms in the form the amalgamation consumes.

* `CategoryTheory.Pseudofunctor.DescentData.BindGlue.glued`: the descent datum for the coarse
  family `g` obtained by gluing, with its three laws.
* `CategoryTheory.Pseudofunctor.DescentData.BindGlue.gluedPullIso`: the comparison
  `pullFunctorObj (bindFamily_w g h) (glued γ hh) ≅ D`, which says that nothing was lost in the
  gluing. Its components are `componentIso`; its compatibility condition reduces, by
  `glueHom_eq_mor` and `CategoryTheory.Pseudofunctor.DescentData.pullFunctorObjHom_eq`, to a
  single cancellation of the inverse images of the two components of `γ i`.
* `CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_bindFamily` and
  `CategoryTheory.Pseudofunctor.DescentData.isStackFor_bindFamily`: **effective descent is local
  on the base.** Essential surjectivity is the comparison above; fully faithfulness is
  `CategoryTheory.Pseudofunctor.fullyFaithfulToDescentData` at the composite family, which is
  covering by `CategoryTheory.GrothendieckTopology.bindOfArrows`.
* `CategoryTheory.Pseudofunctor.IsStackFor.transitive`: the same statement for sieves — the
  **local-character axiom for effective descent**, which is the form a reduction of the stack
  condition to a generating family of coverings consumes.

The hypothesis `γ` of the `BindGlue` section is *data* rather than a claim, so no declaration
there asserts a descent statement whose premise could be unsatisfiable. What makes `γ` available
is the stack condition for each `h i`, via `CategoryTheory.Functor.objObjPreimageIso`; that is
where `isEquivalence_toDescentData_bindFamily` obtains it.

No Stacks tag is claimed: this is category-theoretic substrate, and the source states none of it.
Its intended consumers are Stacks 0EXE and Stacks 023T; the gap it fills for the latter is
described in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcStandardReduction.lean`.

## Implementation notes

Every application of a field of the given descent datum supplies the pair index explicitly, as in
`D.hom q (i₁ := ⟨i, k₁⟩) (i₂ := ⟨i, k₂⟩) f₁ f₂`. Leaving it to unification fails: `bindFamily` is
an `abbrev`, so `bindFamily g h ?p` unfolds to `h ?p.1 ?p.2 ≫ g ?p.1`, and `?p.1 ≟ i` is a
projection of a metavariable, which unification cannot solve.

The general `pullHom`/`mapCompIso` API this file consumes
(`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_mapCompIso_hom_comp_map`,
`pullHom_inv_eq`, `pullHom_comp₃_eq`) currently lives in
`StacksFrontier/AlgebraicGeometry/Descent/ZariskiModuleChartComparison.lean`, which is why this
module imports an `AlgebraicGeometry` file. That API is not specific to schemes and belongs
beside `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`; relocating it would remove
the import and is the reason `pullHom_comp` has been reproved independently several times across
the library.
-/

@[expose] public section

universe t t' v' v u' u

namespace CategoryTheory

open Opposite Limits Pseudofunctor Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]

namespace Pseudofunctor.DescentData

variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {S : C} {ι : Type t} {V : ι → C} {g : ∀ i, V i ⟶ S}
  {κ : ι → Type t'} {U : ∀ i, κ i → C} {h : ∀ i (k : κ i), U i k ⟶ V i}

variable (g h) in
/-- The composite of a family `g i : V i ⟶ S` with families `h i k : U i k ⟶ V i`: the family
indexed by pairs whose member at `⟨i, k⟩` is `h i k ≫ g i`. -/
abbrev bindFamily : ∀ p : Σ i, κ i, U p.1 p.2 ⟶ S := fun p ↦ h p.1 p.2 ≫ g p.1

variable (g) in
/-- A factorization through a member of `h i` is, after composing with `g i`, a factorization
through the corresponding member of the composite family.

This is given a name, with `g` explicit, rather than left to a tactic block inside the
definitions below: a tactic block in the value of a structure field is postponed, and so is the
unification that an implicit `g` here would require, which leaves the field unassigned and the
types of the later fields full of metavariables. -/
lemma bindFamily_fac {i : ι} {k : κ i} {Y : C} {f : Y ⟶ U i k} {q : Y ⟶ V i}
    (hf : f ≫ h i k = q) : f ≫ bindFamily g h ⟨i, k⟩ = q ≫ g i := by
  rw [← hf, Category.assoc]

variable (g h) in
/-- The composite family refines the coarse family, in the form
`CategoryTheory.Pseudofunctor.DescentData.pullFunctor` asks for when the morphism of targets is
the identity of `S`. -/
lemma bindFamily_w (p : Σ i, κ i) :
    h p.1 p.2 ≫ g p.1 = bindFamily g h p ≫ 𝟙 S := by
  rw [Category.comp_id]

variable (g) in
/-- The gluing morphisms of `CategoryTheory.Pseudofunctor.DescentData.restrictBase`: the gluing
morphism of the composite datum taken at the composed morphism to `S`.

This is a separate declaration, rather than a field given in place, because the statements of the
three laws of a descent datum mention the `hom` field: were it given by a postponed field value,
those statements would still contain a metavariable in place of `hom` when they are elaborated,
and a tactic block cannot run on such a goal. It is an `abbrev` so that the laws below remain
literally the corresponding laws of `D`. -/
abbrev restrictBaseHom (D : F.DescentData (bindFamily g h)) (i : ι) ⦃Y : C⦄ (q : Y ⟶ V i)
    ⦃k₁ k₂ : κ i⦄ (f₁ : Y ⟶ U i k₁) (f₂ : Y ⟶ U i k₂)
    (hf₁ : f₁ ≫ h i k₁ = q) (hf₂ : f₂ ≫ h i k₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.obj (D.obj ⟨i, k₁⟩) ⟶
      (F.map f₂.op.toLoc).toFunctor.obj (D.obj ⟨i, k₂⟩) :=
  D.hom (q ≫ g i) (i₁ := ⟨i, k₁⟩) (i₂ := ⟨i, k₂⟩) f₁ f₂
    (bindFamily_fac g hf₁) (bindFamily_fac g hf₂)

/-- A descent datum relative to the composite family restricts, over each `V i`, to a descent
datum relative to the family `h i`. -/
def restrictBase (D : F.DescentData (bindFamily g h)) (i : ι) : F.DescentData (h i) where
  obj k := D.obj ⟨i, k⟩
  hom := restrictBaseHom g D i
  pullHom_hom _ _ s q q' hq k₁ k₂ f₁ f₂ hf₁ hf₂ sf₁ sf₂ hsf₁ hsf₂ := by
    unfold restrictBaseHom
    exact D.pullHom_hom s (q ≫ g i) (q' ≫ g i) (by rw [← hq, Category.assoc])
      (i₁ := ⟨i, k₁⟩) (i₂ := ⟨i, k₂⟩) f₁ f₂
      (bindFamily_fac g hf₁) (bindFamily_fac g hf₂) sf₁ sf₂ hsf₁ hsf₂
  hom_self _ q k e he := by
    unfold restrictBaseHom
    exact D.hom_self (q ≫ g i) (i := ⟨i, k⟩) e (bindFamily_fac g he)
  hom_comp _ q k₁ k₂ k₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    unfold restrictBaseHom
    exact D.hom_comp (q ≫ g i) (i₁ := ⟨i, k₁⟩) (i₂ := ⟨i, k₂⟩) (i₃ := ⟨i, k₃⟩) f₁ f₂ f₃
      (bindFamily_fac g hf₁) (bindFamily_fac g hf₂) (bindFamily_fac g hf₃)

variable (g) in
/-- A factorization of a morphism to `V i` through a member of `h i`, composed with the
structure morphism of `V i`, is a factorization through the composite family. -/
lemma bindFamily_fac' {i : ι} {k : κ i} {Y : C} {c : Y ⟶ U i k} {a : Y ⟶ V i} {q : Y ⟶ S}
    (hc : c ≫ h i k = a) (ha : a ≫ g i = q) : c ≫ bindFamily g h ⟨i, k⟩ = q := by
  rw [← ha, ← hc, Category.assoc]

namespace BindGlue

variable {D : F.DescentData (bindFamily g h)} {N : ∀ i, F.obj (.mk (op (V i)))}
  (γ : ∀ i, (ofObj (f := h i) (N i)) ≅ restrictBase D i)

/-- The components of the isomorphisms `γ i`, as isomorphisms of objects: the inverse image of
`N i` along `h i k` is isomorphic to the component of `D` at `⟨i, k⟩`. -/
@[simps]
def componentIso (i : ι) (k : κ i) :
    (F.map (h i k).op.toLoc).toFunctor.obj (N i) ≅ D.obj ⟨i, k⟩ where
  hom := (γ i).hom.hom k
  inv := (γ i).inv.hom k
  hom_inv_id := congrArg (fun φ ↦ Hom.hom φ k) (γ i).hom_inv_id
  inv_hom_id := congrArg (fun φ ↦ Hom.hom φ k) (γ i).inv_hom_id

/-- The local comparison. Over an object `Y` whose morphism `a` to `V i` factors as `c ≫ h i k`,
the inverse image of `N i` along `a` is isomorphic to the inverse image of the component of `D`
at `⟨i, k⟩` along `c`. -/
noncomputable def locIso (i : ι) (k : κ i) ⦃Y : C⦄ {c : Y ⟶ U i k} {a : Y ⟶ V i}
    (hc : c ≫ h i k = a) :
    (F.map a.op.toLoc).toFunctor.obj (N i) ≅
      (F.map c.op.toLoc).toFunctor.obj (D.obj ⟨i, k⟩) :=
  mapCompIso hc (N i) ≪≫ (F.map c.op.toLoc).toFunctor.mapIso (componentIso γ i k)

/-- The forward morphism of `locIso` is the composite of `mapCompIso` with the inverse image
along `c` of the component of `γ i` at `k`. -/
lemma locIso_hom (i : ι) (k : κ i) ⦃Y : C⦄ {c : Y ⟶ U i k} {a : Y ⟶ V i}
    (hc : c ≫ h i k = a) :
    (locIso γ i k hc).hom = (mapCompIso hc (N i)).hom ≫
      (F.map c.op.toLoc).toFunctor.map (componentIso γ i k).hom := rfl

/-- The compatibility of the components of `γ i` with the gluing morphisms, restated so that the
inverse image of `N i` along `h i k` is spelled as it is in `locIso` rather than as a component
of `ofObj (N i)`.  The two spellings are definitionally equal but not syntactically so, and a
`rw` with the raw compatibility fails its motive check; stating it once as a term, which is
checked at default transparency, keeps every later rewrite inside one spelling. -/
lemma componentIso_comm (i : ι) {k k' : κ i} ⦃Y : C⦄ {a : Y ⟶ V i} {c : Y ⟶ U i k}
    {c' : Y ⟶ U i k'} (hc : c ≫ h i k = a) (hc' : c' ≫ h i k' = a) :
    (F.map c.op.toLoc).toFunctor.map (componentIso γ i k).hom ≫
        restrictBaseHom g D i a c c' hc hc' =
      ((mapCompIso hc (N i)).inv ≫ (mapCompIso hc' (N i)).hom) ≫
        (F.map c'.op.toLoc).toFunctor.map (componentIso γ i k').hom :=
  (γ i).hom.comm a c c' hc hc'

/-- The local comparison is compatible with further pullback. -/
lemma pullHom_locIso_hom (i : ι) (k : κ i) ⦃Y : C⦄ {c : Y ⟶ U i k} {a : Y ⟶ V i}
    (hc : c ≫ h i k = a) ⦃Y' : C⦄ (s : Y' ⟶ Y) {sc : Y' ⟶ U i k} {sa : Y' ⟶ V i}
    (hsc : s ≫ c = sc) (hsa : s ≫ a = sa) (hsc' : sc ≫ h i k = sa) :
    pullHom (locIso γ i k hc).hom s sa sc hsa hsc = (locIso γ i k hsc').hom :=
  pullHom_mapCompIso_hom_comp_map hc (N i) _ s hsc hsa

/-- The inverse local comparison is compatible with further pullback. -/
lemma pullHom_locIso_inv (i : ι) (k : κ i) ⦃Y : C⦄ {c : Y ⟶ U i k} {a : Y ⟶ V i}
    (hc : c ≫ h i k = a) ⦃Y' : C⦄ (s : Y' ⟶ Y) {sc : Y' ⟶ U i k} {sa : Y' ⟶ V i}
    (hsc : s ≫ c = sc) (hsa : s ≫ a = sa) (hsc' : sc ≫ h i k = sa) :
    pullHom (locIso γ i k hc).inv s sc sa hsc hsa = (locIso γ i k hsc').inv :=
  pullHom_inv_eq _ s hsa hsc (pullHom_locIso_hom γ i k hc s hsc hsa hsc')

/-- The local section of the presheaf of morphisms that the gluing amalgamates: over an object
`Y` at which both structure morphisms factor through the fine family, the comparison of the
inverse images of `N i₁` and `N i₂` read off the gluing morphism of `D`. -/
noncomputable def mor {i₁ i₂ : ι} (k₁ : κ i₁) (k₂ : κ i₂) ⦃Y : C⦄ {q : Y ⟶ S}
    {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂} {c₁ : Y ⟶ U i₁ k₁} {c₂ : Y ⟶ U i₂ k₂}
    (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q)
    (hc₁ : c₁ ≫ h i₁ k₁ = a₁) (hc₂ : c₂ ≫ h i₂ k₂ = a₂) :
    (F.map a₁.op.toLoc).toFunctor.obj (N i₁) ⟶ (F.map a₂.op.toLoc).toFunctor.obj (N i₂) :=
  (locIso γ i₁ k₁ hc₁).hom ≫
    D.hom q (i₁ := ⟨i₁, k₁⟩) (i₂ := ⟨i₂, k₂⟩) c₁ c₂
      (bindFamily_fac' g hc₁ ha₁) (bindFamily_fac' g hc₂ ha₂) ≫
    (locIso γ i₂ k₂ hc₂).inv

/-- The local section is compatible with further pullback. -/
lemma pullHom_mor {i₁ i₂ : ι} (k₁ : κ i₁) (k₂ : κ i₂) ⦃Y : C⦄ {q : Y ⟶ S}
    {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂} {c₁ : Y ⟶ U i₁ k₁} {c₂ : Y ⟶ U i₂ k₂}
    (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q)
    (hc₁ : c₁ ≫ h i₁ k₁ = a₁) (hc₂ : c₂ ≫ h i₂ k₂ = a₂)
    ⦃Y' : C⦄ (s : Y' ⟶ Y) {q' : Y' ⟶ S} {sa₁ : Y' ⟶ V i₁} {sa₂ : Y' ⟶ V i₂}
    {sc₁ : Y' ⟶ U i₁ k₁} {sc₂ : Y' ⟶ U i₂ k₂}
    (hq' : s ≫ q = q') (hsa₁ : s ≫ a₁ = sa₁) (hsa₂ : s ≫ a₂ = sa₂)
    (hsc₁ : s ≫ c₁ = sc₁) (hsc₂ : s ≫ c₂ = sc₂)
    (hsa₁' : sa₁ ≫ g i₁ = q') (hsa₂' : sa₂ ≫ g i₂ = q')
    (hsc₁' : sc₁ ≫ h i₁ k₁ = sa₁) (hsc₂' : sc₂ ≫ h i₂ k₂ = sa₂) :
    pullHom (mor γ k₁ k₂ ha₁ ha₂ hc₁ hc₂) s sa₁ sa₂ hsa₁ hsa₂ =
      mor γ k₁ k₂ hsa₁' hsa₂' hsc₁' hsc₂' := by
  unfold mor
  apply pullHom_comp₃_eq _ _ _ s hsa₁ hsc₁ hsc₂ hsa₂
    (pullHom_locIso_hom γ i₁ k₁ hc₁ s hsc₁ hsa₁ hsc₁')
    (D.pullHom_hom s q q' hq' (i₁ := ⟨i₁, k₁⟩) (i₂ := ⟨i₂, k₂⟩) c₁ c₂
      (bindFamily_fac' g hc₁ ha₁) (bindFamily_fac' g hc₂ ha₂) sc₁ sc₂ hsc₁ hsc₂)
    (pullHom_locIso_inv γ i₂ k₂ hc₂ s hsc₂ hsa₂ hsc₂')

/-- Changing the chosen factorization on one side changes the local comparison by the gluing
morphism of `D`: this is what makes the local sections independent of the choices. -/
lemma locIso_hom_comp_hom (i : ι) {k k' : κ i} ⦃Y : C⦄ {a : Y ⟶ V i} {c : Y ⟶ U i k}
    {c' : Y ⟶ U i k'} (hc : c ≫ h i k = a) (hc' : c' ≫ h i k' = a) :
    (locIso γ i k hc).hom ≫ restrictBaseHom g D i a c c' hc hc' = (locIso γ i k' hc').hom := by
  rw [locIso_hom, locIso_hom, Category.assoc, componentIso_comm γ i hc hc']
  simp

/-- `locIso_hom_comp_hom` with the morphism to `S` given rather than computed. -/
lemma locIso_hom_comp_hom' (i : ι) {k k' : κ i} ⦃Y : C⦄ {q : Y ⟶ S} {a : Y ⟶ V i}
    {c : Y ⟶ U i k} {c' : Y ⟶ U i k'} (ha : a ≫ g i = q)
    (hc : c ≫ h i k = a) (hc' : c' ≫ h i k' = a) :
    (locIso γ i k hc).hom ≫ D.hom q (i₁ := ⟨i, k⟩) (i₂ := ⟨i, k'⟩) c c'
        (bindFamily_fac' g hc ha) (bindFamily_fac' g hc' ha) =
      (locIso γ i k' hc').hom := by
  subst ha
  exact locIso_hom_comp_hom γ i hc hc'

/-- The inverse local comparison changes by the gluing morphism of `D` the other way round. -/
lemma hom_comp_locIso_inv (i : ι) {k k' : κ i} ⦃Y : C⦄ {q : Y ⟶ S} {a : Y ⟶ V i}
    {c : Y ⟶ U i k} {c' : Y ⟶ U i k'} (ha : a ≫ g i = q)
    (hc : c ≫ h i k = a) (hc' : c' ≫ h i k' = a) :
    D.hom q (i₁ := ⟨i, k'⟩) (i₂ := ⟨i, k⟩) c' c
        (bindFamily_fac' g hc' ha) (bindFamily_fac' g hc ha) ≫
        (locIso γ i k hc).inv = (locIso γ i k' hc').inv := by
  rw [← cancel_epi (locIso γ i k' hc').hom, Iso.hom_inv_id, ← Category.assoc,
    locIso_hom_comp_hom' γ i ha hc' hc, Iso.hom_inv_id]

/-- **The local section does not depend on the chosen factorizations.**  This is what makes the
family of local sections well defined, and it is the only place the cocycle condition of `D` is
used. -/
lemma mor_unique {i₁ i₂ : ι} {k₁ k₁' : κ i₁} {k₂ k₂' : κ i₂} ⦃Y : C⦄ {q : Y ⟶ S}
    {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂}
    {c₁ : Y ⟶ U i₁ k₁} {c₂ : Y ⟶ U i₂ k₂} {c₁' : Y ⟶ U i₁ k₁'} {c₂' : Y ⟶ U i₂ k₂'}
    (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q)
    (hc₁ : c₁ ≫ h i₁ k₁ = a₁) (hc₂ : c₂ ≫ h i₂ k₂ = a₂)
    (hc₁' : c₁' ≫ h i₁ k₁' = a₁) (hc₂' : c₂' ≫ h i₂ k₂' = a₂) :
    mor γ k₁ k₂ ha₁ ha₂ hc₁ hc₂ = mor γ k₁' k₂' ha₁ ha₂ hc₁' hc₂' := by
  unfold mor
  rw [← locIso_hom_comp_hom' γ i₁ ha₁ hc₁ hc₁', ← hom_comp_locIso_inv γ i₂ ha₂ hc₂ hc₂']
  simp only [Category.assoc, hom_comp_assoc]

section Sieve

variable (h) in
/-- The sieve of morphisms to `Y` along which both structure morphisms factor through the fine
families. This is the covering sieve on which the local sections of the gluing are defined. -/
abbrev bindSieve {i₁ i₂ : ι} {Y : C} (a₁ : Y ⟶ V i₁) (a₂ : Y ⟶ V i₂) : Sieve Y :=
  (Sieve.ofArrows (U i₁) (h i₁)).pullback a₁ ⊓ (Sieve.ofArrows (U i₂) (h i₂)).pullback a₂

/-- Membership of `bindSieve` yields the two factorizations the local section needs. -/
lemma exists_fac_of_mem_bindSieve {i₁ i₂ : ι} {Y : C} {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂}
    {Z : C} {t : Z ⟶ Y} (ht : bindSieve h a₁ a₂ t) :
    ∃ (k₁ : κ i₁) (k₂ : κ i₂) (c₁ : Z ⟶ U i₁ k₁) (c₂ : Z ⟶ U i₂ k₂),
      c₁ ≫ h i₁ k₁ = t ≫ a₁ ∧ c₂ ≫ h i₂ k₂ = t ≫ a₂ := by
  obtain ⟨⟨_, b₁, _, ⟨k₁⟩, fac₁⟩, ⟨_, b₂, _, ⟨k₂⟩, fac₂⟩⟩ := ht
  exact ⟨k₁, k₂, b₁, b₂, fac₁, fac₂⟩

variable {J : GrothendieckTopology C}

/-- `bindSieve` is covering as soon as both fine families are. -/
lemma bindSieve_mem (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) {i₁ i₂ : ι} {Y : C}
    (a₁ : Y ⟶ V i₁) (a₂ : Y ⟶ V i₂) : bindSieve h a₁ a₂ ∈ J Y :=
  J.intersection_covering (J.pullback_stable _ (hh i₁)) (J.pullback_stable _ (hh i₂))

/-- **The descent of morphisms, in the form the gluing amalgamates.** For two objects over `Y`
and a covering sieve of `Y`, the presheaf of morphisms between them is a sheaf for the
corresponding sieve on the slice category over `Y`. -/
lemma isSheafFor_presheafHom [F.IsPrestack J] {Y : C} (T : Sieve Y) (hT : T ∈ J Y)
    (A B : F.obj (.mk (op Y))) :
    Presieve.IsSheafFor (F.presheafHom A B)
      ((Sieve.overEquiv (Over.mk (𝟙 Y))).symm T).arrows :=
  IsPrestackFor.isSheafFor' (Over.mk (𝟙 Y)) (by simpa using F.isPrestackFor' T hT) A B

end Sieve

section Amalgamation

/-- A factorization through the fine family, extracted from membership of the pullback of the
sieve that family generates. -/
lemma exists_fac_of_mem_pullback {i : ι} {Y : C} {a : Y ⟶ V i} {Z : C} {t : Z ⟶ Y}
    (ht : ((Sieve.ofArrows (U i) (h i)).pullback a).arrows t) :
    ∃ (k : κ i) (c : Z ⟶ U i k), c ≫ h i k = t ≫ a := by
  obtain ⟨_, b, _, ⟨k⟩, fac⟩ := ht
  exact ⟨k, b, fac⟩

/-- A chosen index of the fine family through which `t ≫ a` factors. -/
noncomputable def facIdx {i : ι} {Y : C} {a : Y ⟶ V i} {Z : C} {t : Z ⟶ Y}
    (ht : ((Sieve.ofArrows (U i) (h i)).pullback a).arrows t) : κ i :=
  (exists_fac_of_mem_pullback ht).choose

/-- A chosen factorization of `t ≫ a` through the fine family. -/
noncomputable def facHom {i : ι} {Y : C} {a : Y ⟶ V i} {Z : C} {t : Z ⟶ Y}
    (ht : ((Sieve.ofArrows (U i) (h i)).pullback a).arrows t) : Z ⟶ U i (facIdx ht) :=
  (exists_fac_of_mem_pullback ht).choose_spec.choose

/-- The chosen morphism `facHom ht` composed with `h i (facIdx ht)` is `t ≫ a`. -/
@[reassoc]
lemma facHom_fac {i : ι} {Y : C} {a : Y ⟶ V i} {Z : C} {t : Z ⟶ Y}
    (ht : ((Sieve.ofArrows (U i) (h i)).pullback a).arrows t) :
    facHom ht ≫ h i (facIdx ht) = t ≫ a :=
  (exists_fac_of_mem_pullback ht).choose_spec.choose_spec

variable (g) in
/-- Composing a morphism to `S` with a further morphism. Named, with `g` explicit, for the same
reason as `bindFamily_fac`: a tactic block in the *statement* of a declaration is postponed and
leaves metavariables in the goals of the proof. -/
lemma comp_fac {i : ι} {Y Z : C} {q : Y ⟶ S} {a : Y ⟶ V i} (t : Z ⟶ Y) (ha : a ≫ g i = q) :
    (t ≫ a) ≫ g i = t ≫ q := by rw [Category.assoc, ha]

/-- The local section at the chosen factorizations. -/
noncomputable def morOfMem {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S} {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂}
    (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) {Z : C} {t : Z ⟶ Y}
    (ht : (bindSieve h a₁ a₂).arrows t) :
    (F.map (t ≫ a₁).op.toLoc).toFunctor.obj (N i₁) ⟶
      (F.map (t ≫ a₂).op.toLoc).toFunctor.obj (N i₂) :=
  mor γ (facIdx ht.1) (facIdx ht.2) (comp_fac g t ha₁) (comp_fac g t ha₂)
    (facHom_fac ht.1) (facHom_fac ht.2)

/-- The local section at the chosen factorizations agrees with the one at any other pair of
factorizations. -/
lemma morOfMem_eq {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S} {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂}
    (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) {Z : C} {t : Z ⟶ Y}
    (ht : (bindSieve h a₁ a₂).arrows t) {k₁ : κ i₁} {k₂ : κ i₂}
    {c₁ : Z ⟶ U i₁ k₁} {c₂ : Z ⟶ U i₂ k₂}
    (hc₁ : c₁ ≫ h i₁ k₁ = t ≫ a₁) (hc₂ : c₂ ≫ h i₂ k₂ = t ≫ a₂) :
    morOfMem γ ha₁ ha₂ ht =
      mor γ k₁ k₂ (comp_fac g t ha₁) (comp_fac g t ha₂) hc₁ hc₂ :=
  mor_unique γ _ _ (facHom_fac ht.1) (facHom_fac ht.2) hc₁ hc₂

/-- The local section, as an element of the presheaf of morphisms over `Y`. -/
noncomputable def sect {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S} {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂}
    (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) {Z : C} {t : Z ⟶ Y}
    (ht : (bindSieve h a₁ a₂).arrows t) :
    (F.map t.op.toLoc).toFunctor.obj ((F.map a₁.op.toLoc).toFunctor.obj (N i₁)) ⟶
      (F.map t.op.toLoc).toFunctor.obj ((F.map a₂.op.toLoc).toFunctor.obj (N i₂)) :=
  (mapCompIso (rfl : t ≫ a₁ = t ≫ a₁) (N i₁)).inv ≫ morOfMem γ ha₁ ha₂ ht ≫
    (mapCompIso (rfl : t ≫ a₂ = t ≫ a₂) (N i₂)).hom

/-- The local sections are compatible with further pullback: this is the whole content of the
compatibility of the family that the gluing amalgamates. -/
lemma pullHom_sect {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S} {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂}
    (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) {Z : C} {t : Z ⟶ Y}
    (ht : (bindSieve h a₁ a₂).arrows t) {Z' : C} (s : Z' ⟶ Z) {t' : Z' ⟶ Y}
    (hst' : s ≫ t = t') (ht' : (bindSieve h a₁ a₂).arrows t') :
    pullHom (sect γ ha₁ ha₂ ht) s t' t' hst' hst' = sect γ ha₁ ha₂ ht' := by
  have e₀ := (reassoc_of% hst') q
  have e₁ := (reassoc_of% hst') a₁
  have e₂ := (reassoc_of% hst') a₂
  have f : ∀ {i} {a : Y ⟶ V i} {k : κ i} {c : Z ⟶ U i k}, c ≫ h i k = t ≫ a →
      (s ≫ c) ≫ h i k = t' ≫ a := fun hc ↦ by
    rw [Category.assoc, hc, ← Category.assoc, hst']
  have f₁ := f (facHom_fac ht.1)
  have f₂ := f (facHom_fac ht.2)
  have hβ : pullHom (morOfMem γ ha₁ ha₂ ht) s (t' ≫ a₁) (t' ≫ a₂) e₁ e₂ =
      morOfMem γ ha₁ ha₂ ht' := by
    rw [morOfMem_eq γ ha₁ ha₂ ht' f₁ f₂]
    unfold morOfMem
    exact pullHom_mor γ (facIdx ht.1) (facIdx ht.2) (comp_fac g t ha₁) (comp_fac g t ha₂)
      (facHom_fac ht.1) (facHom_fac ht.2) s e₀ e₁ e₂ rfl rfl
      (comp_fac g t' ha₁) (comp_fac g t' ha₂) f₁ f₂
  unfold sect
  exact pullHom_comp₃_eq _ _ _ s hst' e₁ e₂ hst'
    (pullHom_inv_eq _ s e₁ hst' (pullHom_mapCompIso_hom _ (N i₁) s hst' e₁)) hβ
    (pullHom_mapCompIso_hom _ (N i₂) s hst' e₂)

variable {J : GrothendieckTopology C}

/-- A morphism of the slice lies in the transported sieve as soon as its structure morphism lies
in the original one. -/
lemma mem_slice {i₁ i₂ : ι} {Y : C} {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂} {Z : C} {t : Z ⟶ Y}
    (ht : (bindSieve h a₁ a₂).arrows t) :
    ((Sieve.overEquiv (Over.mk (𝟙 Y))).symm (bindSieve h a₁ a₂)).arrows
      (Over.homMk t : Over.mk t ⟶ Over.mk (𝟙 Y)) := by
  rw [Sieve.overEquiv_symm_iff]
  exact ht

/-- Conversely, membership of the transported sieve gives membership for the structure
morphism. -/
lemma mem_of_mem_slice {i₁ i₂ : ι} {Y : C} {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂} {T : Over Y}
    {p : T ⟶ Over.mk (𝟙 Y)}
    (hp : ((Sieve.overEquiv (Over.mk (𝟙 Y))).symm (bindSieve h a₁ a₂)).arrows p) :
    (bindSieve h a₁ a₂).arrows T.hom := by
  rw [Sieve.overEquiv_symm_iff] at hp
  have hl : p.left = T.hom := (Category.comp_id p.left).symm.trans (Over.w p)
  rwa [hl] at hp

/-- The family of local sections that the gluing amalgamates. -/
noncomputable def familyOfElements {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S} {a₁ : Y ⟶ V i₁}
    {a₂ : Y ⟶ V i₂} (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) :
    Presieve.FamilyOfElements
      (F.presheafHom ((F.map a₁.op.toLoc).toFunctor.obj (N i₁))
        ((F.map a₂.op.toLoc).toFunctor.obj (N i₂)))
      ((Sieve.overEquiv (Over.mk (𝟙 Y))).symm (bindSieve h a₁ a₂)).arrows :=
  fun _ _ hp ↦ sect γ ha₁ ha₂ (mem_of_mem_slice hp)

/-- Restricting a local section of `familyOfElements γ ha₁ ha₂` along a morphism `u` in
`Over Y` gives the local section at the source of `u`. -/
lemma map_sect {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S} {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂}
    (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) {T W : Over Y} (u : W ⟶ T)
    (ht : (bindSieve h a₁ a₂).arrows T.hom) (hw : (bindSieve h a₁ a₂).arrows W.hom) :
    (F.presheafHom ((F.map a₁.op.toLoc).toFunctor.obj (N i₁))
        ((F.map a₂.op.toLoc).toFunctor.obj (N i₂))).map u.op (sect γ ha₁ ha₂ ht) =
      sect γ ha₁ ha₂ hw :=
  pullHom_sect γ ha₁ ha₂ ht u.left (Over.w u) hw

/-- The family of local sections `familyOfElements γ ha₁ ha₂` is compatible. -/
lemma compatible_familyOfElements {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S} {a₁ : Y ⟶ V i₁}
    {a₂ : Y ⟶ V i₂} (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) :
    (familyOfElements γ ha₁ ha₂).Compatible := by
  intro T₁ T₂ W u₁ u₂ p₁ p₂ hp₁ _ _
  have hW : (bindSieve h a₁ a₂).arrows W.hom :=
    mem_of_mem_slice
      (((Sieve.overEquiv (Over.mk (𝟙 Y))).symm (bindSieve h a₁ a₂)).downward_closed hp₁ u₁)
  exact (map_sect γ ha₁ ha₂ u₁ _ hW).trans (map_sect γ ha₁ ha₂ u₂ _ hW).symm

/-- The section `F.presheafHomObjHomEquiv f` of the presheaf of morphisms corresponding to a
morphism `f` is the inverse image of `f` along `𝟙 Y`. -/
lemma presheafHomObjHomEquiv_eq {Y : C} {A B : F.obj (.mk (op Y))} (f : A ⟶ B) :
    F.presheafHomObjHomEquiv f = (F.map (𝟙 Y).op.toLoc).toFunctor.map f := by
  rw [presheafHomObjHomEquiv_apply, ← Category.assoc,
    show (F.mapId (.mk (op Y))).hom.toNatTrans.app A ≫ f =
        (F.map (𝟙 (.mk (op Y)))).toFunctor.map f ≫
          (F.mapId (.mk (op Y))).hom.toNatTrans.app B from
      ((F.mapId (.mk (op Y))).hom.toNatTrans.naturality f).symm,
    Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]
  rfl

/-- Restricting the section `F.presheafHomObjHomEquiv f` along `Over.homMk t` gives the inverse
image of `f` along `t`. -/
lemma presheafHom_map_homMk_objHomEquiv {Y : C} (A B : F.obj (.mk (op Y))) (f : A ⟶ B)
    {Z : C} (t : Z ⟶ Y) :
    (F.presheafHom A B).map (Over.homMk t : Over.mk t ⟶ Over.mk (𝟙 Y)).op
        (F.presheafHomObjHomEquiv f) =
      (F.map t.op.toLoc).toFunctor.map f := by
  rw [presheafHomObjHomEquiv_eq]
  exact pullHom_map f t t (Category.comp_id t)

/-- **The glued morphism.** The amalgamation of the family of local sections. -/
noncomputable def glueHom [F.IsPrestack J]
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S}
    {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂} (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) :
    (F.map a₁.op.toLoc).toFunctor.obj (N i₁) ⟶ (F.map a₂.op.toLoc).toFunctor.obj (N i₂) :=
  F.presheafHomObjHomEquiv.symm
    ((isSheafFor_presheafHom (bindSieve h a₁ a₂) (bindSieve_mem hh a₁ a₂) _ _).amalgamate _
      (compatible_familyOfElements γ ha₁ ha₂))

/-- The defining property of the glued morphism: its restriction along a member of the sieve is
the local section there. -/
lemma map_glueHom [F.IsPrestack J]
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S}
    {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂} (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q)
    {Z : C} {t : Z ⟶ Y} (ht : (bindSieve h a₁ a₂).arrows t) :
    (F.map t.op.toLoc).toFunctor.map (glueHom γ hh ha₁ ha₂) = sect γ ha₁ ha₂ ht := by
  have hs := (isSheafFor_presheafHom (bindSieve h a₁ a₂) (bindSieve_mem hh a₁ a₂)
    ((F.map a₁.op.toLoc).toFunctor.obj (N i₁))
    ((F.map a₂.op.toLoc).toFunctor.obj (N i₂))).isAmalgamation
      (compatible_familyOfElements γ ha₁ ha₂)
  rw [← presheafHom_map_homMk_objHomEquiv, glueHom, Equiv.apply_symm_apply]
  exact hs (Over.homMk t : Over.mk t ⟶ Over.mk (𝟙 Y)) (mem_slice ht)

/-- The defining property of the glued morphism, in `pullHom` form. -/
lemma pullHom_glueHom [F.IsPrestack J]
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S}
    {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂} (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q)
    {Z : C} {t : Z ⟶ Y} (ht : (bindSieve h a₁ a₂).arrows t) :
    pullHom (glueHom γ hh ha₁ ha₂) t (t ≫ a₁) (t ≫ a₂) rfl rfl = morOfMem γ ha₁ ha₂ ht := by
  have h₁ := map_glueHom γ hh ha₁ ha₂ ht
  rw [map_eq_pullHom (glueHom γ hh ha₁ ha₂) t (t ≫ a₁) (t ≫ a₂) rfl rfl] at h₁
  unfold sect at h₁
  rw [← cancel_epi ((mapCompIso (rfl : t ≫ a₁ = t ≫ a₁) (N i₁)).inv),
    ← cancel_mono ((mapCompIso (rfl : t ≫ a₂ = t ≫ a₂) (N i₂)).hom)]
  simp only [Category.assoc]
  exact h₁

/-- **Morphisms between inverse images are determined by their pullbacks along a covering
sieve.** This is the separatedness half of the descent of morphisms, in the form the three laws
of the glued descent datum consume. -/
lemma hom_ext_of_covering [F.IsPrestack J] {Y : C} {A B : F.obj (.mk (op Y))} {T : Sieve Y}
    (hT : T ∈ J Y) {φ ψ : A ⟶ B}
    (hres : ∀ ⦃Z : C⦄ (t : Z ⟶ Y), T.arrows t →
      (F.map t.op.toLoc).toFunctor.map φ = (F.map t.op.toLoc).toFunctor.map ψ) :
    φ = ψ := by
  apply F.presheafHomObjHomEquiv.injective
  refine (isSheafFor_presheafHom T hT A B).isSeparatedFor.ext ?_
  intro T' p hp
  obtain ⟨Z, t, rfl⟩ := T'.mk_surjective
  obtain rfl : p = Over.homMk t := by ext; simpa using Over.w p
  rw [presheafHom_map_homMk_objHomEquiv, presheafHom_map_homMk_objHomEquiv]
  exact hres t (by rwa [Sieve.overEquiv_symm_iff] at hp)

/-- Extensionality in the form the three laws of the glued descent datum consume. -/
lemma hom_ext_of_covering' [F.IsPrestack J] {X₁ X₂ : C} {M₁ : F.obj (.mk (op X₁))}
    {M₂ : F.obj (.mk (op X₂))} {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {T : Sieve Y} (hT : T ∈ J Y)
    {φ ψ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    (hres : ∀ ⦃Z : C⦄ (t : Z ⟶ Y), T.arrows t →
      pullHom φ t (t ≫ f₁) (t ≫ f₂) rfl rfl = pullHom ψ t (t ≫ f₁) (t ≫ f₂) rfl rfl) :
    φ = ψ := by
  refine hom_ext_of_covering hT (fun Z t ht ↦ ?_)
  rw [map_eq_pullHom φ t (t ≫ f₁) (t ≫ f₂) rfl rfl,
    map_eq_pullHom ψ t (t ≫ f₁) (t ≫ f₂) rfl rfl, hres t ht]

/-- The defining property of the glued morphism, with the pulled-back morphisms given by
equations rather than computed, which is the form the laws below need. -/
lemma pullHom_glueHom_eq_mor [F.IsPrestack J]
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S}
    {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂} (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q)
    {Z : C} {t : Z ⟶ Y} (ht : (bindSieve h a₁ a₂).arrows t)
    {ta₁ : Z ⟶ V i₁} {ta₂ : Z ⟶ V i₂} {tq : Z ⟶ S}
    (hta₁ : t ≫ a₁ = ta₁) (hta₂ : t ≫ a₂ = ta₂) (htq : t ≫ q = tq)
    {k₁ : κ i₁} {k₂ : κ i₂} {c₁ : Z ⟶ U i₁ k₁} {c₂ : Z ⟶ U i₂ k₂}
    (hc₁ : c₁ ≫ h i₁ k₁ = ta₁) (hc₂ : c₂ ≫ h i₂ k₂ = ta₂)
    (hta₁' : ta₁ ≫ g i₁ = tq) (hta₂' : ta₂ ≫ g i₂ = tq) :
    pullHom (glueHom γ hh ha₁ ha₂) t ta₁ ta₂ hta₁ hta₂ = mor γ k₁ k₂ hta₁' hta₂' hc₁ hc₂ := by
  subst hta₁ hta₂ htq
  rw [pullHom_glueHom γ hh ha₁ ha₂ ht]
  exact morOfMem_eq γ ha₁ ha₂ ht hc₁ hc₂

/-- The local section at a single factorization taken twice is the identity. -/
lemma mor_self {i : ι} (k : κ i) ⦃Y : C⦄ {q : Y ⟶ S} {a : Y ⟶ V i} {c : Y ⟶ U i k}
    (ha : a ≫ g i = q) (hc : c ≫ h i k = a) : mor γ k k ha ha hc hc = 𝟙 _ := by
  unfold mor
  rw [D.hom_self q (i := ⟨i, k⟩) c (bindFamily_fac' g hc ha), Category.id_comp, Iso.hom_inv_id]

/-- The local sections compose. -/
lemma mor_comp {i₁ i₂ i₃ : ι} (k₁ : κ i₁) (k₂ : κ i₂) (k₃ : κ i₃) ⦃Y : C⦄ {q : Y ⟶ S}
    {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂} {a₃ : Y ⟶ V i₃}
    {c₁ : Y ⟶ U i₁ k₁} {c₂ : Y ⟶ U i₂ k₂} {c₃ : Y ⟶ U i₃ k₃}
    (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) (ha₃ : a₃ ≫ g i₃ = q)
    (hc₁ : c₁ ≫ h i₁ k₁ = a₁) (hc₂ : c₂ ≫ h i₂ k₂ = a₂) (hc₃ : c₃ ≫ h i₃ k₃ = a₃) :
    mor γ k₁ k₂ ha₁ ha₂ hc₁ hc₂ ≫ mor γ k₂ k₃ ha₂ ha₃ hc₂ hc₃ =
      mor γ k₁ k₃ ha₁ ha₃ hc₁ hc₃ := by
  unfold mor
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hom_comp_assoc]

/-- The gluing morphisms of the glued descent datum. Named rather than given in place, because
the statements of the three laws of a descent datum mention the `hom` field, and a field given in
place leaves them with a metavariable there that no tactic can grip. -/
noncomputable abbrev gluedHom [F.IsPrestack J]
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (a₁ : Y ⟶ V i₁) (a₂ : Y ⟶ V i₂) (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) :
    (F.map a₁.op.toLoc).toFunctor.obj (N i₁) ⟶ (F.map a₂.op.toLoc).toFunctor.obj (N i₂) :=
  glueHom γ hh ha₁ ha₂

/-- **The descent datum for the coarse family obtained by gluing.** Its components are the
objects the stack condition for each fine family produced, and its gluing morphisms are glued
from the gluing morphisms of the given datum. Each of the three laws is checked after pullback
along a covering sieve, where it reduces to the corresponding law for the local sections. -/
noncomputable def glued [F.IsPrestack J]
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) : F.DescentData g where
  obj := N
  hom := gluedHom γ hh
  pullHom_hom _ _ s q q' hq i₁ i₂ a₁ a₂ ha₁ ha₂ sa₁ sa₂ hsa₁ hsa₂ := by
    have hsa₁' : sa₁ ≫ g i₁ = q' := by rw [← hsa₁, Category.assoc, ha₁, hq]
    have hsa₂' : sa₂ ≫ g i₂ = q' := by rw [← hsa₂, Category.assoc, ha₂, hq]
    refine hom_ext_of_covering' (bindSieve_mem hh sa₁ sa₂) (fun W u hu ↦ ?_)
    have hus : (bindSieve h a₁ a₂).arrows (u ≫ s) :=
      ⟨⟨_, facHom hu.1, _, ⟨facIdx hu.1⟩, by rw [facHom_fac, Category.assoc, hsa₁]⟩,
        ⟨_, facHom hu.2, _, ⟨facIdx hu.2⟩, by rw [facHom_fac, Category.assoc, hsa₂]⟩⟩
    rw [pullHom_pullHom,
      pullHom_glueHom_eq_mor γ hh ha₁ ha₂ hus (by rw [Category.assoc, hsa₁])
        (by rw [Category.assoc, hsa₂]) (by rw [Category.assoc, hq]) (facHom_fac hu.1)
        (facHom_fac hu.2) (comp_fac g u hsa₁') (comp_fac g u hsa₂'),
      pullHom_glueHom_eq_mor γ hh hsa₁' hsa₂' hu rfl rfl rfl (facHom_fac hu.1)
        (facHom_fac hu.2) (comp_fac g u hsa₁') (comp_fac g u hsa₂')]
  hom_self _ q i e he := by
    refine hom_ext_of_covering' (bindSieve_mem hh e e) (fun W u hu ↦ ?_)
    rw [pullHom_glueHom_eq_mor γ hh he he hu rfl rfl rfl (facHom_fac hu.1) (facHom_fac hu.1)
      (comp_fac g u he) (comp_fac g u he), mor_self, pullHom_id']
  hom_comp _ q i₁ i₂ i₃ a₁ a₂ a₃ ha₁ ha₂ ha₃ := by
    have hT : (bindSieve h a₁ a₂ ⊓ (Sieve.ofArrows (U i₃) (h i₃)).pullback a₃) ∈ J _ :=
      J.intersection_covering (bindSieve_mem hh a₁ a₂) (J.pullback_stable a₃ (hh i₃))
    refine hom_ext_of_covering' hT (fun W u hu ↦ ?_)
    rw [pullHom_comp _ _ u (u ≫ a₁) (u ≫ a₂) (u ≫ a₃) rfl rfl rfl,
      pullHom_glueHom_eq_mor γ hh ha₁ ha₂ hu.1 rfl rfl rfl (facHom_fac hu.1.1)
        (facHom_fac hu.1.2) (comp_fac g u ha₁) (comp_fac g u ha₂),
      pullHom_glueHom_eq_mor γ hh ha₂ ha₃ ⟨hu.1.2, hu.2⟩ rfl rfl rfl (facHom_fac hu.1.2)
        (facHom_fac hu.2) (comp_fac g u ha₂) (comp_fac g u ha₃),
      pullHom_glueHom_eq_mor γ hh ha₁ ha₃ ⟨hu.1.1, hu.2⟩ rfl rfl rfl (facHom_fac hu.1.1)
        (facHom_fac hu.2) (comp_fac g u ha₁) (comp_fac g u ha₃), mor_comp]

/-- **At a point where both legs already factor through the fine families, the glued morphism
is the local section itself.** The identity lies in the sieve there, so this is the defining
property of the amalgamation and not a further computation. -/
lemma glueHom_eq_mor [F.IsPrestack J]
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) {i₁ i₂ : ι} {Y : C} {q : Y ⟶ S}
    {a₁ : Y ⟶ V i₁} {a₂ : Y ⟶ V i₂} (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q)
    {k₁ : κ i₁} {k₂ : κ i₂} {c₁ : Y ⟶ U i₁ k₁} {c₂ : Y ⟶ U i₂ k₂}
    (hc₁ : c₁ ≫ h i₁ k₁ = a₁) (hc₂ : c₂ ≫ h i₂ k₂ = a₂) :
    glueHom γ hh ha₁ ha₂ = mor γ k₁ k₂ ha₁ ha₂ hc₁ hc₂ := by
  have hid : (bindSieve h a₁ a₂).arrows (𝟙 Y) :=
    ⟨⟨_, c₁, _, ⟨k₁⟩, by rw [hc₁, Category.id_comp]⟩,
      ⟨_, c₂, _, ⟨k₂⟩, by rw [hc₂, Category.id_comp]⟩⟩
  rw [← pullHom_id (glueHom γ hh ha₁ ha₂)]
  exact pullHom_glueHom_eq_mor γ hh ha₁ ha₂ hid (Category.id_comp a₁) (Category.id_comp a₂)
    (Category.id_comp q) hc₁ hc₂ ha₁ ha₂

/-- The object of `glued γ hh` over `V i` is `N i`. -/
@[simp]
lemma glued_obj [F.IsPrestack J] (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) (i : ι) :
    (glued γ hh).obj i = N i := rfl

/-- The gluing morphisms of `glued γ hh` are the morphisms `glueHom γ hh ha₁ ha₂`. -/
@[simp]
lemma glued_hom [F.IsPrestack J] (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i))
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (a₁ : Y ⟶ V i₁) (a₂ : Y ⟶ V i₂)
    (ha₁ : a₁ ≫ g i₁ = q) (ha₂ : a₂ ≫ g i₂ = q) :
    (glued γ hh).hom q a₁ a₂ ha₁ ha₂ = glueHom γ hh ha₁ ha₂ := rfl

end Amalgamation

section Comparison

/-- The inverse of the local comparison, with the two factors in the order they occur. -/
lemma locIso_inv (i : ι) (k : κ i) ⦃Y : C⦄ {c : Y ⟶ U i k} {a : Y ⟶ V i}
    (hc : c ≫ h i k = a) :
    (locIso γ i k hc).inv = (F.map c.op.toLoc).toFunctor.map (componentIso γ i k).inv ≫
      (mapCompIso hc (N i)).inv := rfl

variable {J : GrothendieckTopology C}

/-- The gluing morphism of the glued datum, read at a point where both legs already factor
through the fine families, in the shape the comparison below consumes: the local comparisons
conjugating the gluing morphism of `D`. -/
lemma pullFunctorObjHom_glued [F.IsPrestack J]
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) (i₁ i₂ : ι) (k₁ : κ i₁) (k₂ : κ i₂)
    {Y : C} (q : Y ⟶ S) (f₁ : Y ⟶ U i₁ k₁) (f₂ : Y ⟶ U i₂ k₂)
    (hf₁ : f₁ ≫ bindFamily g h ⟨i₁, k₁⟩ = q) (hf₂ : f₂ ≫ bindFamily g h ⟨i₂, k₂⟩ = q)
    (ha₁ : (f₁ ≫ h i₁ k₁) ≫ g i₁ = q) (ha₂ : (f₂ ≫ h i₂ k₂) ≫ g i₂ = q) :
    pullFunctorObjHom (bindFamily_w g h) (glued γ hh) q (j₁ := ⟨i₁, k₁⟩) (j₂ := ⟨i₂, k₂⟩)
        f₁ f₂ hf₁ hf₂ =
      (mapCompIso (rfl : f₁ ≫ h i₁ k₁ = f₁ ≫ h i₁ k₁) (N i₁)).inv ≫
        mor γ k₁ k₂ ha₁ ha₂ rfl rfl ≫
          (mapCompIso (rfl : f₂ ≫ h i₂ k₂ = f₂ ≫ h i₂ k₂) (N i₂)).hom := by
  rw [pullFunctorObjHom_eq (bindFamily_w g h) (glued γ hh) q (j₁ := ⟨i₁, k₁⟩) (j₂ := ⟨i₂, k₂⟩)
    f₁ f₂ q (f₁ ≫ h i₁ k₁) (f₂ ≫ h i₂ k₂) hf₁ hf₂ (Category.comp_id q) rfl rfl, glued_hom,
    glueHom_eq_mor γ hh ha₁ ha₂ rfl rfl]
  rfl

/-- **The compatibility condition of the comparison.** Stated as a standalone lemma, in the
spelling `componentIso` and `N` carry, rather than inside the definition below: inside, the
objects are spelled as components of `pullFunctorObj`, and a `rw` whose motive mentions them is
not type-correct at the transparency the motive check uses.

The morphism to `S` is taken to be the composite `f₁ ≫ bindFamily g h ⟨i₁, k₁⟩` rather than an
arbitrary `q` together with an equation, because that is the spelling
`CategoryTheory.Pseudofunctor.DescentData.pullFunctorObj_hom` produces: the `q` of
`pullFunctorObjHom` occurs in that definition only inside the two factorization proofs, so when
the field is given it is unification, not the surrounding binder, that fixes it, and it is fixed
to the composite. -/
lemma componentIso_comm_glued [F.IsPrestack J]
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) (i₁ i₂ : ι) (k₁ : κ i₁) (k₂ : κ i₂)
    {Y : C} (f₁ : Y ⟶ U i₁ k₁) (f₂ : Y ⟶ U i₂ k₂)
    (hf₂ : f₂ ≫ bindFamily g h ⟨i₂, k₂⟩ = f₁ ≫ bindFamily g h ⟨i₁, k₁⟩) :
    (F.map f₁.op.toLoc).toFunctor.map (componentIso γ i₁ k₁).hom ≫
        D.hom (f₁ ≫ bindFamily g h ⟨i₁, k₁⟩) (i₁ := ⟨i₁, k₁⟩) (i₂ := ⟨i₂, k₂⟩) f₁ f₂ rfl hf₂ =
      pullFunctorObjHom (bindFamily_w g h) (glued γ hh) (f₁ ≫ bindFamily g h ⟨i₁, k₁⟩)
          (j₁ := ⟨i₁, k₁⟩) (j₂ := ⟨i₂, k₂⟩) f₁ f₂ rfl hf₂ ≫
        (F.map f₂.op.toLoc).toFunctor.map (componentIso γ i₂ k₂).hom := by
  have ha₁ : (f₁ ≫ h i₁ k₁) ≫ g i₁ = f₁ ≫ bindFamily g h ⟨i₁, k₁⟩ := Category.assoc _ _ _
  have ha₂ : (f₂ ≫ h i₂ k₂) ≫ g i₂ = f₁ ≫ bindFamily g h ⟨i₁, k₁⟩ := by
    rw [Category.assoc]; exact hf₂
  dsimp only [glued_obj]
  rw [pullFunctorObjHom_glued γ hh i₁ i₂ k₁ k₂ _ f₁ f₂ rfl hf₂ ha₁ ha₂]
  unfold mor
  rw [locIso_hom, locIso_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Iso.map_inv_hom_id, Category.comp_id]

/-- **The pullback of the glued datum along the composite family is the datum it was glued
from.** Its components are the comparisons `componentIso`, and the compatibility condition is the
defining property of the glued morphisms at a point where both legs already factor through the
fine families. -/
noncomputable def gluedPullIso [F.IsPrestack J]
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) :
    pullFunctorObj (bindFamily_w g h) (glued γ hh) ≅ D :=
  isoMk (fun p ↦ componentIso γ p.1 p.2) (by
    rintro Y q ⟨i₁, k₁⟩ ⟨i₂, k₂⟩ f₁ f₂ hf₁ hf₂
    subst hf₁
    exact componentIso_comm_glued γ hh i₁ i₂ k₁ k₂ f₁ f₂ hf₂)

end Comparison

end BindGlue

section Composite

variable {J : GrothendieckTopology C}

/-- The natural isomorphism identifying the descent data along the composite family that come
from an object over `S` with the pullbacks along the composite family of the descent data along
the coarse family that come from that object. -/
noncomputable def toDescentDataCompPullFunctorBindIso :
    F.toDescentData g ⋙ pullFunctor F (bindFamily_w g h) ≅ F.toDescentData (bindFamily g h) :=
  toDescentDataCompPullFunctorIso F (bindFamily_w g h) ≪≫
    Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫ Functor.leftUnitor _

/-- The composite family is covering as soon as the coarse family and each fine family is. -/
lemma ofArrows_bindFamily_mem (hg : Sieve.ofArrows V g ∈ J S)
    (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i)) :
    Sieve.ofArrows _ (bindFamily g h) ∈ J S := by
  have := J.bindOfArrows (Z := V) (f := g) (R := fun i ↦ Presieve.ofArrows (U i) (h i)) hg
    (fun i ↦ hh i)
  rwa [Presieve.bindOfArrows_ofArrows] at this

/-- **Effective descent is local on the base.** If `F` is a prestack for `J`, if effective
descent holds along a family `g i : V i ⟶ S`, and if it holds along a family
`h i k : U i k ⟶ V i` over each `V i`, then it holds along the composite family. -/
theorem isEquivalence_toDescentData_bindFamily [F.IsPrestack J]
    (hg : Sieve.ofArrows V g ∈ J S) (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i))
    (hgeq : (F.toDescentData g).IsEquivalence)
    (hheq : ∀ i, (F.toDescentData (h i)).IsEquivalence) :
    (F.toDescentData (bindFamily g h)).IsEquivalence := by
  have hcov : Sieve.ofArrows _ (bindFamily g h) ∈ J S := ofArrows_bindFamily_mem hg hh
  have ff := F.fullyFaithfulToDescentData (bindFamily g h) hcov
  have := ff.full
  have := ff.faithful
  have : (F.toDescentData (bindFamily g h)).EssSurj := by
    refine ⟨fun D ↦ ?_⟩
    have := hgeq
    have (i : ι) := hheq i
    let N (i : ι) : F.obj (.mk (op (V i))) :=
      (F.toDescentData (h i)).objPreimage (restrictBase D i)
    let γ (i : ι) : (ofObj (f := h i) (N i)) ≅ restrictBase D i :=
      (F.toDescentData (h i)).objObjPreimageIso (restrictBase D i)
    exact ⟨(F.toDescentData g).objPreimage (BindGlue.glued γ hh),
      ⟨(toDescentDataCompPullFunctorBindIso.app _).symm ≪≫
        (pullFunctor F (bindFamily_w g h)).mapIso
          ((F.toDescentData g).objObjPreimageIso (BindGlue.glued γ hh)) ≪≫
        BindGlue.gluedPullIso γ hh⟩⟩
  exact { }

/-- **The stack condition for a composite covering family.** Effective descent along the
composite of a covering family with covering families over each of its members. -/
theorem isStackFor_bindFamily [F.IsPrestack J]
    (hg : Sieve.ofArrows V g ∈ J S) (hh : ∀ i, Sieve.ofArrows (U i) (h i) ∈ J (V i))
    (hgeq : (F.toDescentData g).IsEquivalence)
    (hheq : ∀ i, (F.toDescentData (h i)).IsEquivalence) :
    F.IsStackFor (Presieve.ofArrows _ (bindFamily g h)) :=
  (F.isStackFor_ofArrows_iff (bindFamily g h)).2
    (isEquivalence_toDescentData_bindFamily hg hh hgeq hheq)

end Composite

end Pseudofunctor.DescentData

namespace Pseudofunctor

variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}} {J : GrothendieckTopology C}

/-- **The local-character axiom for effective descent.** If effective descent holds along a
covering sieve `S`, and along the restriction of a sieve `R` to each member of `S`, then it holds
along `R`.

This is the stack analogue of the transitivity axiom of a Grothendieck topology, and it is the
form in which the composite statement
`CategoryTheory.Pseudofunctor.DescentData.isStackFor_bindFamily` is consumed: a sieve covered by
sieves along a covering is itself one for which descent is effective.

This is the step Mathlib's `CategoryTheory.Pseudofunctor.IsStack.of_precoverage` does not need,
because its precoverage is assumed closed under composition and base change, so a covering sieve
of the generated topology already contains a single covering family. For a precoverage that only
*generates* the coverings — which is the situation of Stacks 0EX9 — the saturation has to be run,
and this is its local-character case; the remaining case is pullback stability of
`CategoryTheory.Pseudofunctor.IsStackFor` along a morphism, which is not formal. -/
theorem IsStackFor.transitive [F.IsPrestack J] {X : C} {S R : Sieve X} (hS : S ∈ J X)
    (hSst : F.IsStackFor S.arrows)
    (hRmem : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ J Y)
    (hRst : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → F.IsStackFor (R.pullback f).arrows) :
    F.IsStackFor R.arrows := by
  have hg : Sieve.ofArrows (fun i : S.arrows.category ↦ i.obj.left)
      (fun i ↦ i.obj.hom) ∈ J X := by rw [Sieve.ofArrows_category]; exact hS
  have hh (i : S.arrows.category) :
      Sieve.ofArrows (fun k : (R.pullback i.obj.hom).arrows.category ↦ k.obj.left)
        (fun k ↦ k.obj.hom) ∈ J i.obj.left := by
    rw [Sieve.ofArrows_category]; exact hRmem i.property
  have hbind := DescentData.isStackFor_bindFamily hg hh hSst.isEquivalence
    (fun i ↦ (hRst i.property).isEquivalence)
  refine hbind.of_le _ (DescentData.ofArrows_bindFamily_mem hg hh) ?_
  rintro Y u ⟨⟨i, k⟩⟩
  exact k.property

end Pseudofunctor

end CategoryTheory

end
