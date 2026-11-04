module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingInSite

/-!
# Gluing data from a family of open subfunctors

Mathlib proves Stacks 01JJ for the category of all schemes: a `Type u`-valued Zariski sheaf
on `Sch` admitting a jointly surjective family of relatively representable open immersions
from representable presheaves is representable
(`AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable`). The consumers in the
algebraic-spaces chapter need the same statement one level down, for a presheaf on the big
fppf site over a scheme `S`, where the representing object must itself be an object of that
site — an `S`-scheme satisfying the site's size cutoff. Mathlib's statement does not give
that, because the scheme it glues is produced in `Sch` with no size control.

This file supplies the part of that transfer which is independent of schemes. The gluing
data underlying Mathlib's proof is built from
`CategoryTheory.Functor.relativelyRepresentable` alone, so it exists in **any** category
with pullbacks whose chosen morphism property consists of monomorphisms. That construction
is carried out here once, for an abstract category, and then instantiated at the big fppf
site over `S`, where the glued object is the candidate representing object.

## Main definitions

* `Stacks.SubfunctorGlue.transition` is the transition morphism between the triple
  pullbacks which underlies the cocycle condition, together with its three projection
  formulas `Stacks.SubfunctorGlue.transition_p₁`, `_p₂` and `_p₃`.
* `Stacks.SubfunctorGlue.glueData` is the gluing data attached to a family of relatively
  representable monomorphisms into a presheaf on an abstract category with pullbacks.
* `AlgebraicGeometry.Space.openImmersionOver` is the property of a morphism of the big fppf
  site over `S` that its underlying morphism of schemes is an open immersion.
* `AlgebraicGeometry.Space.glueData` is `Stacks.SubfunctorGlue.glueData` instantiated at
  the big fppf site over `S`, and `AlgebraicGeometry.Space.schemeGlueData` is the gluing
  data of schemes it induces.
* `AlgebraicGeometry.Space.gluedStructureHom` is the structure morphism of the glued scheme
  over `S`, and `AlgebraicGeometry.Space.gluedObj` is the glued scheme together with it, as
  an object of the big fppf site over `S`.
* `AlgebraicGeometry.Space.toGlued` is the `i`-th chart as a morphism of the site into the
  glued object.

## Main results

* `AlgebraicGeometry.Space.openImmersionOver_le_monomorphisms`: an open immersion of the site
  is a monomorphism, which is what makes the gluing data's self-intersections isomorphisms
  and is the only hypothesis the abstract construction needs beyond pullbacks.
* `AlgebraicGeometry.Space.glueData_f_openImmersion`: every structure map of the gluing
  data is an open immersion of the site, so the gluing data is one that schemes can be
  glued along.
* `AlgebraicGeometry.BigFppfSite.contains_glueData_glued`: a big fppf site is closed under
  gluing along an index type below the cofinality of its size cutoff. This is the
  set-theoretic content of the transfer, and
  `AlgebraicGeometry.Space.contains_schemeGlueData_glued` is its application here.
* `AlgebraicGeometry.Space.ι_gluedStructureHom`, `_toScheme_map_toGlued`,
  `AlgebraicGeometry.Space.toGlued_openImmersion` and
  `AlgebraicGeometry.Space.toGlued_jointly_surjective` describe the charts of the glued
  object: they are open immersions of the site, they are jointly surjective, and they
  commute with the structure morphisms.

What is **not** proved here is the comparison `yoneda.obj (gluedObj …) ≅ F` itself, so
nothing in this file carries an unqualified `@[stacks 01JJ]`; the tag already sits on
Mathlib's `AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable` for the case of
all schemes. See the implementation notes for what the comparison still needs.

## Implementation notes

The overlaps are the representable pullbacks `V i j = X i ×_F X j`, the transition maps are
the symmetry isomorphisms of those pullbacks, and the cocycle condition is read off the
triple pullback `CategoryTheory.Functor.relativelyRepresentable.pullback₃`. This is
Mathlib's `AlgebraicGeometry.Scheme.LocalRepresentability.glueData`, with two changes.

First, the ambient category is a variable. That is not generality for its own sake: it is
what makes the instance searches in the three pullback fields resolve, and it is the cure
recorded for this family of failures elsewhere in the project.

Second, and this is the delicate point, none of the rewriting tactics can be used inside
these fields. `CategoryTheory.Functor.relativelyRepresentable.pullback₃` is a `def` for a
`CategoryTheory.Limits.pullback`, so the two spellings of the overlap object are only
*reducibly* equal; the goals produced by `hom_ext'` and `pullback₃.hom_ext` are therefore
not type-correct at `implicit` transparency, which is the transparency at which `rw` and
`simp only` do their matching. Compounding this, Mathlib proves `lift₃_p₁`, `lift₃_p₂`,
`lift₃_p₃` and the three `pullback₃.map_pᵢ_comp` lemmas under
`backward.isDefEq.respectTransparency false`, so those lemmas do not fire under `rw` or
`simp` here even where the goal is well behaved. Both problems are avoided the same way:
every one of these fields is discharged by a *term*, since a term is checked at `default`
transparency. The projection formulas are packaged as
`Stacks.SubfunctorGlue.transition_p₁`, `_p₂`, `_p₃` precisely so that the cocycle
identity is a composition of named equations rather than a rewrite. Mathlib needs the flag
for this construction; stated this way, no flag is needed.

The same discipline is forced again lower down, for a second reason. Through
`CategoryTheory.GlueData.mapGlueData` the index type of the gluing data of schemes is
`(schemeGlueData f hf).J` rather than `ι`, and the glued object is a `colimit` whose
`getColimitCocone` is not exposed; both are reducible rather than syntactic identities, so
`rw` reports "did not find an occurrence" against goals that print identically to the
pattern. Hence `AlgebraicGeometry.Space.toGlued_openImmersion` is an `Eq.mpr` and not a
`rwa`. Relatedly, `CategoryTheory.Functor.map_preimage` cannot be applied to a bare
morphism here, because recovering its implicit endpoints would mean inverting
`B.inclusion.obj`; `AlgebraicGeometry.Space.toGluedLeft` exists to pin those endpoints in a
signature, and with it the lemma is immediate.

To finish Stacks 01JJ for the site, three further steps are needed, in this order: that the
charts of `AlgebraicGeometry.Space.gluedObj` generate a covering sieve for
`AlgebraicGeometry.BigFppfOver.topology` (they are jointly surjective open immersions, so
this is Stacks 021S plus `AlgebraicGeometry.BigFppfSite.generate_mem_topology`); that the
overlaps are the fibre products of the charts over the glued object, which is
`CategoryTheory.GlueData.vPullbackConeIsLimit` transported through
`CategoryTheory.Over.forget`; and then the comparison morphism
`yoneda.obj (gluedObj …) ⟶ F` obtained from the sheaf condition by
`CategoryTheory.GlueData.sheafValGluedMk`, which is an isomorphism by
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`.

The identities relating the glued object to the glued scheme are deliberately *not* `simp`
lemmas. Their left-hand sides are not in simp-normal form: `simp` rewrites
`B.inclusion.map g` and `(toScheme B S hS).map g` into the projection spellings
`g.hom` and `(Over.Hom.left g).hom`, so marking them `@[simp]` fails the `simpNF` linter.
They are used as terms throughout, which is also what the transparency discussion above
requires.

## References

* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 01JB](https://stacks.math.columbia.edu/tag/01JB)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.SubfunctorGlue

open Functor.relativelyRepresentable

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {P : MorphismProperty C}
  (hP : P ≤ MorphismProperty.monomorphisms C) {G : Cᵒᵖ ⥤ Type v} {ι : Type v} {X : ι → C}
  (f : (i : ι) → yoneda.obj (X i) ⟶ G) (hf : ∀ i, P.presheaf (f i))

omit [HasPullbacks C] in
/-- The first projection of the representable pullback `X i ×_G X j` has the chosen property:
it is a base change of the morphism `f j`, which has it. -/
theorem fst'_prop (i j : ι) : P ((hf i).rep.fst' (f j)) :=
  (hf j).property (f i) (yoneda.map ((hf i).rep.snd (f j))) ((hf i).rep.fst' (f j))
    ((hf i).1.isPullback' (f j)).flip

/-- The transition morphism between triple pullbacks, `(X i ×_G X j) ×_{X i} (X i ×_G X k) ⟶
(X j ×_G X k) ×_{X j} (X j ×_G X i)`, obtained from the universal property of the target by
the three projections of the source taken in cyclic order. -/
noncomputable def transition (i j k : ι) :
    (hf i).rep.pullback₃ (f j) (f k) ⟶ (hf j).rep.pullback₃ (f k) (f i) :=
  lift₃ _ _ _ (pullback₃.p₂ _ _ _) (pullback₃.p₃ _ _ _) (pullback₃.p₁ _ _ _)
    ((pullback₃.map_p₂_comp (hf i).rep (f j) (f k)).trans
      (pullback₃.map_p₃_comp (hf i).rep (f j) (f k)).symm)
    ((pullback₃.map_p₂_comp (hf i).rep (f j) (f k)).trans
      (pullback₃.map_p₁_comp (hf i).rep (f j) (f k)).symm)

/-- The transition morphism carries the first projection of its target to the second
projection of its source. -/
theorem transition_p₁ (i j k : ι) :
    transition f hf i j k ≫ pullback₃.p₁ (hf j).rep (f k) (f i) =
      pullback₃.p₂ (hf i).rep (f j) (f k) :=
  lift₃_p₁ _ _ _ _ _ _ _ _

/-- The transition morphism carries the second projection of its target to the third
projection of its source. -/
theorem transition_p₂ (i j k : ι) :
    transition f hf i j k ≫ pullback₃.p₂ (hf j).rep (f k) (f i) =
      pullback₃.p₃ (hf i).rep (f j) (f k) :=
  lift₃_p₂ _ _ _ _ _ _ _ _

/-- The transition morphism carries the third projection of its target to the first
projection of its source. -/
theorem transition_p₃ (i j k : ι) :
    transition f hf i j k ≫ pullback₃.p₃ (hf j).rep (f k) (f i) =
      pullback₃.p₁ (hf i).rep (f j) (f k) :=
  lift₃_p₃ _ _ _ _ _ _ _ _

/-- **Stacks 01JJ**, the gluing data. A family of relatively representable monomorphisms
into a presheaf on a category with pullbacks determines gluing data in that category, with
`X i` as the charts and the representable pullback `X i ×_G X j` as the overlap of the
`i`-th and `j`-th chart.

This is the construction of `AlgebraicGeometry.Scheme.LocalRepresentability.glueData` with
the ambient category left as a variable. -/
noncomputable def glueData : CategoryTheory.GlueData C where
  J := ι
  U := X
  V := fun (i, j) ↦ (hf i).rep.pullback (f j)
  f := fun i j ↦ (hf i).rep.fst' (f j)
  f_mono := fun i j ↦ hP _ (fst'_prop f hf i j)
  f_id := fun i ↦ MorphismProperty.isIso_fst'_self hP (hf i)
  t := fun i j ↦ (hf i).rep.symmetry (hf j).rep
  t_id := fun i ↦ by
    apply (hf i).rep.hom_ext' <;> simp [MorphismProperty.fst'_self_eq_snd hP (hf i)]
  t' := transition f hf
  t_fac := fun i j k ↦ (hf j).rep.hom_ext'
    (((Category.assoc _ _ _).trans
        ((congrArg (transition f hf i j k ≫ ·)
            (pullback₃.snd_fst'_eq_p₁ (hf j).rep (f k) (f i))).trans
          (transition_p₁ f hf i j k))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (pullback.fst ((hf i).rep.fst' (f j)) ((hf i).rep.fst' (f k)) ≫ ·)
            (symmetry_fst (hf i).rep (hf j).rep)).trans
          (pullback₃.fst_snd_eq_p₂ (hf i).rep (f j) (f k)))).symm)
    (((Category.assoc _ _ _).trans
        ((congrArg (transition f hf i j k ≫ ·)
            (pullback₃.snd_snd_eq_p₃ (hf j).rep (f k) (f i))).trans
          (transition_p₃ f hf i j k))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (pullback.fst ((hf i).rep.fst' (f j)) ((hf i).rep.fst' (f k)) ≫ ·)
            (symmetry_snd (hf i).rep (hf j).rep)).trans
          (pullback₃.fst_fst'_eq_p₁ (hf i).rep (f j) (f k)))).symm)
  cocycle := fun i j k ↦ pullback₃.hom_ext
    ((Category.assoc _ _ _).trans
      (((congrArg (transition f hf i j k ≫ ·)
            ((Category.assoc _ _ _).trans
              (congrArg (transition f hf j k i ≫ ·) (transition_p₁ f hf k i j)))).trans
          ((congrArg (transition f hf i j k ≫ ·) (transition_p₂ f hf j k i)).trans
            (transition_p₃ f hf i j k))).trans
        (Category.id_comp _).symm))
    ((Category.assoc _ _ _).trans
      (((congrArg (transition f hf i j k ≫ ·)
            ((Category.assoc _ _ _).trans
              (congrArg (transition f hf j k i ≫ ·) (transition_p₂ f hf k i j)))).trans
          ((congrArg (transition f hf i j k ≫ ·) (transition_p₃ f hf j k i)).trans
            (transition_p₁ f hf i j k))).trans
        (Category.id_comp _).symm))
    ((Category.assoc _ _ _).trans
      (((congrArg (transition f hf i j k ≫ ·)
            ((Category.assoc _ _ _).trans
              (congrArg (transition f hf j k i ≫ ·) (transition_p₃ f hf k i j)))).trans
          ((congrArg (transition f hf i j k ≫ ·) (transition_p₁ f hf j k i)).trans
            (transition_p₂ f hf i j k))).trans
        (Category.id_comp _).symm))

/-- The chart attached to a subfunctor of `G` which is represented by an object `Y`: the
representing isomorphism followed by the inclusion of the subfunctor. This is the form in
which a covering family of representable subfunctors is handed to
`Stacks.SubfunctorGlue.glueData`. -/
noncomputable def chartMap {H : Subfunctor G} {Y : C} (e : H.toFunctor.RepresentableBy Y) :
    yoneda.obj Y ⟶ G :=
  e.toIso.hom ≫ H.ι

omit hP [HasPullbacks C] in
/-- A chart inherits the relative property of the subfunctor's inclusion, the two differing
only by an isomorphism of the source. -/
theorem presheaf_chartMap {H : Subfunctor G} {Y : C} (e : H.toFunctor.RepresentableBy Y)
    (hH : P.presheaf H.ι) : P.presheaf (chartMap e) :=
  have ea : Arrow.mk H.ι ≅ Arrow.mk (chartMap e) :=
    Arrow.isoMk e.toIso.symm (Iso.refl _)
      (by exact (Iso.inv_hom_id_assoc e.toIso H.ι).trans (Category.comp_id _).symm)
  (P.presheaf.arrow_mk_iso_iff ea).mp hH

/-- The `i`-th chart of the gluing data is `X i`. -/
@[simp]
theorem glueData_U (i : ι) : (glueData hP f hf).U i = X i := rfl

/-- The structure map from the overlap `X i ×_G X j` to `X i` is the first projection of the
representable pullback. -/
@[simp]
theorem glueData_f (i j : ι) : (glueData hP f hf).f i j = (hf i).rep.fst' (f j) := rfl

/-- The transition map `X i ×_G X j ⟶ X j ×_G X i` is the symmetry isomorphism of the
representable pullbacks. -/
@[simp]
theorem glueData_t (i j : ι) :
    (glueData hP f hf).t i j = (hf i).rep.symmetry (hf j).rep := rfl

end Stacks.SubfunctorGlue

namespace AlgebraicGeometry

/-! ### The size of a glued scheme -/

namespace BigFppfSite

/-- A big fppf site is closed under gluing: if every chart of a gluing datum of schemes lies
in the site and the index type is smaller than the cofinality of the size cutoff, then the
glued scheme lies in the site as well.

The hypothesis on the index type is not an artefact. The glued scheme is covered by the
images of its charts, so the open-cover bound of Stacks 000Q bounds its size by
`max #J (⨆ i, size (U i))`, and the supremum is below the cutoff exactly when the index type
is below the cutoff's cofinality. Uncountable cofinality is a field of
`AlgebraicGeometry.BigFppfSite`, so an at most countable index type qualifies
automatically. -/
theorem contains_glueData_glued (B : BigFppfSite.{u}) (D : Scheme.GlueData.{u})
    (hJ : #D.J < B.cutoff.ord.cof) (hU : ∀ i, B.Contains (D.U i)) :
    B.Contains D.glued := by
  rcases isEmpty_or_nonempty D.J with hJe | hJn
  · have : IsEmpty D.glued := ⟨fun x ↦ (D.ι_jointly_surjective x).elim fun i _ ↦ hJe.elim i⟩
    have e : D.glued ≅ (∅ : Scheme.{u}) :=
      (isInitialOfIsEmpty (X := D.glued)).uniqueUpToIso emptyIsInitial
    exact lt_of_le_of_lt ((Scheme.size_congr e).trans_le Scheme.size_empty_le_aleph0)
      B.aleph0_lt_cutoff
  · have hcov : ⨆ i, (D.ι i).opensRange = ⊤ := by
      refine top_le_iff.mp fun x _ ↦ ?_
      obtain ⟨i, y, hy⟩ := D.ι_jointly_surjective x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, hy⟩
    refine lt_of_le_of_lt
      (Scheme.size_le_of_iSup_eq_top (fun i ↦ (D.ι i).opensRange) hcov) (max_lt ?_ ?_)
    · exact hJ.trans_le (Ordinal.cof_ord_le B.cutoff)
    · refine Cardinal.iSup_lt_of_lt_cof_ord hJ fun i ↦ ?_
      exact ((Scheme.size_congr (D.ι i).isoOpensRange).symm.trans_lt (hU i))

end BigFppfSite

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Underlying a morphism of the big fppf site over `S` is a morphism of schemes commuting
with the two structure morphisms to `S`. This is `CategoryTheory.Over.w` read through the
functor to schemes, and it is what makes the structure morphisms of a gluing datum
compatible. -/
theorem toScheme_map_comp_structureHom {A C : BigFppfOver B S hS} (g : A ⟶ C) :
    (toScheme B S hS).map g ≫ B.inclusion.map C.hom = B.inclusion.map A.hom :=
  (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w g))

end BigFppfOver

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open immersions of the site -/

/-- An open immersion of algebraic spaces in the sense of
`AlgebraicGeometry.Space.IsOpenImmersion` is exactly a relatively representable morphism for
`AlgebraicGeometry.Space.openImmersionOver`. This is the identification through which a Zariski
covering by open subspaces becomes an input to `Stacks.SubfunctorGlue.glueData`. -/
theorem isOpenImmersion_iff_presheaf_openImmersions
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    IsOpenImmersion B S hS f ↔ (openImmersionOver B S hS).presheaf f :=
  Iff.rfl

/-! ### The gluing data attached to a family of open subfunctors -/

section GlueData

variable {B S hS}
variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {ι : Type u} {X : ι → BigFppfOver B S hS}
  (f : (i : ι) → yoneda.obj (X i) ⟶ F)
  (hf : ∀ i, (openImmersionOver B S hS).presheaf (f i))

/-- The first projection of the representable pullback `X i ×_F X j` is an open immersion of
the site: it is a base change of the open immersion `f j`. -/
theorem fst'_openImmersion (i j : ι) :
    openImmersionOver B S hS ((hf i).rep.fst' (f j)) :=
  Stacks.SubfunctorGlue.fst'_prop f hf i j

/-- **Stacks 01JJ**, the gluing data in the big fppf site over `S`. A family of relatively
representable open immersions into a presheaf on the site determines gluing data in the
site, with `X i` as the charts and `X i ×_F X j` as the overlaps. -/
noncomputable def glueData : CategoryTheory.GlueData (BigFppfOver B S hS) :=
  letI := B.hasPullbacks_schemes
  Stacks.SubfunctorGlue.glueData openImmersionOver_le_monomorphisms f hf

/-- Every structure map of the gluing data is an open immersion of the site, so the
underlying family of schemes may be glued. -/
theorem glueData_f_openImmersion (i j : ι) :
    openImmersionOver B S hS ((glueData f hf).f i j) :=
  fst'_openImmersion f hf i j

/-- The gluing data of schemes underlying `AlgebraicGeometry.Space.glueData`. Its charts are
the schemes underlying the `X i` and its overlaps are the schemes underlying the
representable pullbacks; the functor to schemes preserves the pullbacks involved because the
size cutoff is closed under fibre products. -/
noncomputable def schemeGlueData : Scheme.GlueData.{u} :=
  letI := B.hasPullbacks_schemes
  { toGlueData := (glueData f hf).mapGlueData (BigFppfOver.toScheme B S hS)
    f_open := fun i j ↦ glueData_f_openImmersion f hf i j }

/-- The `i`-th chart of the gluing data of schemes is the scheme underlying `X i`. -/
@[simp]
theorem schemeGlueData_U (i : ι) :
    (schemeGlueData f hf).U i = (BigFppfOver.toScheme B S hS).obj (X i) := rfl

/-- **The glued scheme lies in the site.** If the index type of the covering family is
smaller than the cofinality of the site's size cutoff, the scheme glued from the charts is
again an object of the site, and so carries a structure morphism making it a candidate
representing object.

Every chart lies in the site by construction, since it is an object of the site; the content
is the open-cover size bound of `AlgebraicGeometry.BigFppfSite.contains_glueData_glued`. -/
theorem contains_schemeGlueData_glued (hι : #ι < B.cutoff.ord.cof) :
    B.Contains (schemeGlueData f hf).glued :=
  B.contains_glueData_glued (schemeGlueData f hf) hι fun i ↦ (X i).left.property

/-! ### The glued object of the site -/

/-- The structure morphism of the glued scheme to `S`, glued from the structure morphisms of
the charts. The charts' structure morphisms are compatible for the purely formal reason that
every morphism of the slice commutes with them
(`AlgebraicGeometry.BigFppfOver.toScheme_map_comp_structureHom`), so no identification of the
overlaps with fibre products is needed. -/
noncomputable def gluedStructureHom :
    (schemeGlueData f hf).glued ⟶ B.inclusion.obj (B.obj hS) :=
  Multicoequalizer.desc _ _ (fun i ↦ B.inclusion.map (X i).hom) fun a ↦
    (BigFppfOver.toScheme_map_comp_structureHom B S hS
        ((glueData f hf).f a.1 a.2)).trans
      ((BigFppfOver.toScheme_map_comp_structureHom B S hS
          ((glueData f hf).t a.1 a.2)).symm.trans
        ((congrArg ((BigFppfOver.toScheme B S hS).map ((glueData f hf).t a.1 a.2) ≫ ·)
            (BigFppfOver.toScheme_map_comp_structureHom B S hS
              ((glueData f hf).f a.2 a.1))).symm.trans
          (Category.assoc _ _ _).symm))

/-- The chart `X i` maps into the glued scheme compatibly with the structure morphisms. -/
@[reassoc (attr := simp)]
theorem ι_gluedStructureHom (i : ι) :
    (schemeGlueData f hf).ι i ≫ gluedStructureHom f hf = B.inclusion.map (X i).hom :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- **Stacks 01JJ**, the glued object. The glued scheme, with its glued structure morphism,
as an object of the big fppf site over `S`. This is the candidate representing object for a
presheaf covered by the family `f`. -/
noncomputable def gluedObj (hι : #ι < B.cutoff.ord.cof) : BigFppfOver B S hS :=
  Over.mk (Y := B.obj (contains_schemeGlueData_glued f hf hι))
    (B.inclusion.preimage (gluedStructureHom f hf))

/-- The scheme underlying the glued object of the site is the glued scheme. -/
theorem gluedObj_left (hι : #ι < B.cutoff.ord.cof) :
    B.inclusion.obj (gluedObj f hf hι).left = (schemeGlueData f hf).glued := rfl

/-- The scheme underlying the glued object of the site is the glued scheme, with the glued
structure morphism. -/
theorem toScheme_map_gluedObj_hom (hι : #ι < B.cutoff.ord.cof) :
    B.inclusion.map (gluedObj f hf hι).hom = gluedStructureHom f hf :=
  B.inclusion.map_preimage _

/-- The `i`-th chart into the glued scheme, as a morphism of the underlying category of the
site. Pinning the source and target in the signature is what lets
`AlgebraicGeometry.Space.inclusion_map_toGluedLeft` be proved at all: the implicit
endpoints of `CategoryTheory.Functor.map_preimage` cannot be recovered from the type of the
morphism being lifted, since that would mean inverting `B.inclusion.obj`. -/
noncomputable def toGluedLeft (hι : #ι < B.cutoff.ord.cof) (i : ι) :
    (X i).left ⟶ B.obj (contains_schemeGlueData_glued f hf hι) :=
  B.inclusion.preimage ((schemeGlueData f hf).ι i)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.toGluedLeft` is the `i`-th
structure map of the glued scheme. -/
theorem inclusion_map_toGluedLeft (hι : #ι < B.cutoff.ord.cof) (i : ι) :
    B.inclusion.map (toGluedLeft f hf hι i) = (schemeGlueData f hf).ι i :=
  B.inclusion.map_preimage _

/-- The `i`-th chart as a morphism of the big fppf site over `S` into the glued object. Its
underlying morphism of schemes is the `i`-th structure map of the glued scheme, and it
commutes with the structure morphisms by `AlgebraicGeometry.Space.ι_gluedStructureHom`. -/
noncomputable def toGlued (hι : #ι < B.cutoff.ord.cof) (i : ι) : X i ⟶ gluedObj f hf hι :=
  Over.homMk (toGluedLeft f hf hι i)
    (B.inclusion.map_injective
      ((B.inclusion.map_comp _ _).trans
        ((congrArg (· ≫ B.inclusion.map (gluedObj f hf hι).hom)
            (inclusion_map_toGluedLeft f hf hι i)).trans
          ((congrArg ((schemeGlueData f hf).ι i ≫ ·)
              (toScheme_map_gluedObj_hom f hf hι)).trans
            (ι_gluedStructureHom f hf i)))))

/-- The morphism of schemes underlying the `i`-th chart into the glued object is the `i`-th
structure map of the glued scheme. -/
theorem toScheme_map_toGlued (hι : #ι < B.cutoff.ord.cof) (i : ι) :
    (BigFppfOver.toScheme B S hS).map (toGlued f hf hι i) = (schemeGlueData f hf).ι i :=
  inclusion_map_toGluedLeft f hf hι i

/-- Each chart is an open immersion into the glued object, in the site. -/
theorem toGlued_openImmersion (hι : #ι < B.cutoff.ord.cof) (i : ι) :
    openImmersionOver B S hS (toGlued f hf hι i) :=
  Eq.mpr (congrArg (fun m ↦ _root_.AlgebraicGeometry.IsOpenImmersion m)
      (toScheme_map_toGlued f hf hι i))
    ((schemeGlueData f hf).ι_isOpenImmersion i)

/-- The charts are jointly surjective onto the glued object: every point of the glued scheme
comes from a chart. -/
theorem toGlued_jointly_surjective (hι : #ι < B.cutoff.ord.cof)
    (x : (schemeGlueData f hf).glued) :
    ∃ (i : ι) (y : (BigFppfOver.toScheme B S hS).obj (X i)),
      ((BigFppfOver.toScheme B S hS).map (toGlued f hf hι i)).base y = x := by
  obtain ⟨i, y, hy⟩ := (schemeGlueData f hf).ι_jointly_surjective x
  rw [← toScheme_map_toGlued f hf hι i] at hy
  exact ⟨i, y, hy⟩

end GlueData

end Space

end AlgebraicGeometry

end
