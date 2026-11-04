module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleSeparated

/-!
# Two global sections of an étale sheaf agree over an open subscheme

Two global sections of a sheaf of sets on the small étale site of `X` — that is, two sections over
the final object — agree over some objects of the site and not over others. The objects over which
they agree have open images in `X`, so their union is an open subscheme `U₀`, and the content of
this file is that this open *decides* the question: the two sections agree over an object of the
site exactly when the image of that object is contained in `U₀`.

One direction is the definition. The other is the sheaf condition: if the image of `W` lies in
`U₀`, cover `W` by the fibre products `W ×_X V` taken over all objects `V` on which the sections
agree. Those fibre products are again étale over `X`, their images in `W` are the preimages of the
images of the `V`, so they do cover `W`, and the sections agree over each of them because they
agree over `V` and the second projection is a morphism of the site. Separatedness of the sheaf
for that covering gives the conclusion.

It is essential that the sections are *global* — sections over the final object. For sections over
a general object `A` the same family of fibre products still covers, but the two projections give
two different morphisms to `A`, and the argument breaks down; over the final object all morphisms
to the base agree, so the ambiguity disappears.

This is the open equality locus of
[Stacks, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM) for Mathlib's small étale site
`AlgebraicGeometry.Scheme.Etale`, and it is the step of
[Stacks, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF) which turns local agreement of two
global sections near a closed subscheme into agreement over an open subscheme containing it.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleImage` — the open image in `X` of an object of the small
  étale site.
* `Stacks.EtaleCohomology.smallEtalePair` — the fibre product of two objects of the small étale
  site, as an object of that site, with its two projections
  `Stacks.EtaleCohomology.smallEtalePairFst` and `Stacks.EtaleCohomology.smallEtalePairSnd`.
* `Stacks.EtaleCohomology.globalSectionEqOpen` — the open subscheme over which two global
  sections of a sheaf on the small étale site agree.

## Main results

* `Stacks.EtaleCohomology.range_smallEtalePairFst` — the image of the first projection of a fibre
  product is the preimage of the image of the second factor.
* `Stacks.EtaleCohomology.smallEtaleImage_le_globalSectionEqOpen` — the image of an object over
  which the sections agree is contained in the equality locus.
* `Stacks.EtaleCohomology.eq_restrict_of_range_subset_globalSectionEqOpen` — conversely, the
  sections agree over any object of the site whose image lies in the equality locus.
* `Stacks.EtaleCohomology.eq_of_globalSectionEqOpen_eq_top` — two global sections whose equality
  locus is all of `X` are equal.

## Implementation notes

The fibre product is built by hand from `CategoryTheory.Limits.pullback` in `Scheme` and promoted
to the small étale site, rather than taken as a limit inside `X.Etale`. Both exist, but the image
of the projection is wanted as a set of points, and that is a statement about the underlying
scheme-theoretic fibre product, available as `AlgebraicGeometry.Scheme.Pullback.range_fst`.

Images are open because an étale morphism is flat and locally of finite presentation, hence an
open map; this is the same route `Stacks.EtaleCohomology.exists_opensToEtale_hom_surjective`
takes.

## References

* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

universe w u

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}}

/-- The image in `X` of an object of the small étale site of `X`, as an open subscheme: an étale
morphism is flat and locally of finite presentation, hence an open map. -/
public def smallEtaleImage (W : X.Etale) : X.Opens :=
  letI : Etale (W.hom : W.left ⟶ X) := W.prop
  ⟨Set.range (W.hom : W.left ⟶ X).base, (Scheme.Hom.isOpenMap _).isOpen_range⟩

/-- A point of `X` lies in `smallEtaleImage W` if and only if it is in the image of the structure
morphism of `W`. -/
@[simp]
public theorem mem_smallEtaleImage_iff (W : X.Etale) (x : X) :
    x ∈ smallEtaleImage W ↔ x ∈ Set.range (W.hom : W.left ⟶ X).base :=
  Iff.rfl

/-- The fibre product over `X` of two objects of the small étale site of `X`, as an object of that
site. -/
public def smallEtalePair (W V : X.Etale) : X.Etale :=
  letI : Etale (W.hom : W.left ⟶ X) := W.prop
  letI : Etale (V.hom : V.left ⟶ X) := V.prop
  MorphismProperty.Over.mk ⊤
    (pullback.fst (W.hom : W.left ⟶ X) (V.hom : V.left ⟶ X) ≫ (W.hom : W.left ⟶ X))
    inferInstance

/-- The first projection of the fibre product of two objects of the small étale site. -/
public def smallEtalePairFst (W V : X.Etale) : smallEtalePair W V ⟶ W :=
  MorphismProperty.Over.homMk (pullback.fst _ _) rfl trivial

/-- The second projection of the fibre product of two objects of the small étale site. -/
public def smallEtalePairSnd (W V : X.Etale) : smallEtalePair W V ⟶ V :=
  MorphismProperty.Over.homMk (pullback.snd _ _) pullback.condition.symm trivial

/-- The image in `W` of the first projection of the fibre product `W ×_X V` is the preimage of the
image of `V` in `X`. -/
public theorem range_smallEtalePairFst (W V : X.Etale) :
    Set.range (smallEtalePairFst W V).left.base
      = (W.hom : W.left ⟶ X).base ⁻¹' (smallEtaleImage V : Set X) := by
  show Set.range (pullback.fst (W.hom : W.left ⟶ X) (V.hom : V.left ⟶ X)).base = _
  exact Scheme.Pullback.range_fst _ _

variable (F : Sheaf (Scheme.smallEtaleTopology X) (Type w))

/-- Two global sections of a sheaf on the small étale site of `X` agree over an object `W` of the
site when their restrictions along the unique morphism `W ⟶ X` of the site are equal. -/
public abbrev GlobalSectionEqAt (a b : F.obj.obj (op (terminal X.Etale))) (W : X.Etale) : Prop :=
  F.obj.map (terminal.from W).op a = F.obj.map (terminal.from W).op b

/-- Restricting a global section to `V` and then along `g : W ⟶ V` is restricting it to `W`. -/
private theorem map_map_terminal_from (a : F.obj.obj (op (terminal X.Etale))) {W V : X.Etale}
    (g : W ⟶ V) :
    F.obj.map g.op (F.obj.map (terminal.from V).op a) = F.obj.map (terminal.from W).op a := by
  rw [← types_comp_apply (F.obj.map _) (F.obj.map g.op), ← F.obj.map_comp, ← op_comp,
    Subsingleton.elim (g ≫ terminal.from V) (terminal.from W)]

/-- Agreement of two global sections is inherited along any morphism of the small étale site. -/
public theorem GlobalSectionEqAt.of_hom {a b : F.obj.obj (op (terminal X.Etale))} {W V : X.Etale}
    (h : GlobalSectionEqAt F a b V) (g : W ⟶ V) : GlobalSectionEqAt F a b W :=
  (map_map_terminal_from F a g).symm.trans <|
    (congrArg (F.obj.map g.op) h).trans (map_map_terminal_from F b g)

/-- The open subscheme of `X` over which two global sections of a sheaf on the small étale site
agree: the union of the images of the objects of the site over which they agree. -/
public def globalSectionEqOpen (a b : F.obj.obj (op (terminal X.Etale))) : X.Opens :=
  ⨆ W : {W : X.Etale // GlobalSectionEqAt F a b W}, smallEtaleImage W.1

/-- The image of an object over which two global sections agree is contained in their equality
locus. -/
public theorem smallEtaleImage_le_globalSectionEqOpen
    {a b : F.obj.obj (op (terminal X.Etale))} {W : X.Etale} (h : GlobalSectionEqAt F a b W) :
    smallEtaleImage W ≤ globalSectionEqOpen F a b :=
  le_iSup (fun W : {W : X.Etale // GlobalSectionEqAt F a b W} ↦ smallEtaleImage W.1) ⟨W, h⟩

/-- A point lies in the equality locus of two global sections exactly when it is in the image of
some object of the site over which they agree. -/
public theorem mem_globalSectionEqOpen_iff (a b : F.obj.obj (op (terminal X.Etale))) (x : X) :
    x ∈ globalSectionEqOpen F a b ↔
      ∃ W : X.Etale, GlobalSectionEqAt F a b W ∧ x ∈ smallEtaleImage W := by
  refine ⟨fun hx ↦ ?_, fun ⟨W, hW, hx⟩ ↦ smallEtaleImage_le_globalSectionEqOpen F hW hx⟩
  obtain ⟨W, hW⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ W : {W : X.Etale // GlobalSectionEqAt F a b W}, smallEtaleImage W.1 from hx)
  exact ⟨W.1, W.2, hW⟩

/-- **The equality locus decides agreement.** Two global sections of a sheaf on the small étale
site of `X` agree over any object of the site whose image in `X` is contained in their equality
locus.

The object is covered by its fibre products with the objects over which the sections agree, and
the sections agree over each of those by functoriality; separatedness of the sheaf for that
covering finishes. -/
public theorem eq_restrict_of_range_subset_globalSectionEqOpen
    {a b : F.obj.obj (op (terminal X.Etale))} (A : X.Etale)
    (hA : Set.range (A.hom : A.left ⟶ X).base ⊆ (globalSectionEqOpen F a b : Set X)) :
    GlobalSectionEqAt F a b A := by
  have hcov : Sieve.ofArrows (fun W : {W : X.Etale // GlobalSectionEqAt F a b W} ↦
      smallEtalePair A W.1) (fun W ↦ smallEtalePairFst A W.1) ∈
        Scheme.smallEtaleTopology X A := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨W, hW, hy⟩ := (mem_globalSectionEqOpen_iff F a b _).mp (hA ⟨y, rfl⟩)
    exact ⟨⟨W, hW⟩, by rw [range_smallEtalePairFst]; exact hy⟩
  refine (F.property.isSheafFor _ hcov).isSeparatedFor.ext fun {Y} {g} hg ↦ ?_
  obtain ⟨W, t, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  have hY : GlobalSectionEqAt F a b Y :=
    (W.2.of_hom F (smallEtalePairSnd A W.1)).of_hom F t
  rwa [map_map_terminal_from, map_map_terminal_from]

/-- Two global sections of a sheaf on the small étale site whose equality locus is all of `X` are
equal. -/
public theorem eq_of_globalSectionEqOpen_eq_top {a b : F.obj.obj (op (terminal X.Etale))}
    (h : globalSectionEqOpen F a b = ⊤) : a = b := by
  have hA : F.obj.map (terminal.from (terminal X.Etale)).op a =
      F.obj.map (terminal.from (terminal X.Etale)).op b :=
    eq_restrict_of_range_subset_globalSectionEqOpen F (terminal X.Etale)
      (by rw [h]; exact fun _ _ ↦ trivial)
  rwa [Subsingleton.elim (terminal.from (terminal X.Etale)) (𝟙 _), op_id,
    F.obj.map_id, types_id_apply, types_id_apply] at hA

end Stacks.EtaleCohomology

end
