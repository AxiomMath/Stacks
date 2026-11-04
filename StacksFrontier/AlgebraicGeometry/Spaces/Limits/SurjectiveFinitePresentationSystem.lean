module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.CategoryTheory.Presentable.Directed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian

/-!
# Approximation on a quasi-compact quasi-separated algebraic space

Two approximation statements of Stacks, Section 70.9 are treated here.

**Stacks 086Y.** A finite type quasi-coherent `𝒪_X`-module on a quasi-compact and
quasi-separated algebraic space is a *directed colimit* of `𝒪_X`-modules of finite presentation
whose transition maps are all surjective.

**Stacks 082A.** A quasi-coherent `𝒪_X`-algebra on such a space is a *directed colimit* of
finitely presented quasi-coherent `𝒪_X`-algebras.

## The direction of the limit

Stacks 086Y is stated in the source with the symbol `lim`, but its own proof ends with
"`ℱ = colim 𝒢_i/𝒦_a` is a solution to the problem posed by the lemma": the system is a
*filtered colimit* whose transition maps are surjective, and the scheme-level counterpart
Stacks 086M — formalized in this tree as
`AlgebraicGeometry.exists_directed_colimit_finitePresentation_with_epi_maps` — is stated as a
colimit over a directed poset.  That is the reading taken here.  Stacks 082A says
"directed colimit" outright.  Both conclusions below are therefore colimits over a directed
poset, and for Stacks 086Y the surjectivity of every transition map is part of the
conclusion.

## Main results

* `Stacks.DirectedCokernelSystem.exists_directed_of_filtered_colimit`: a filtered colimit
  presentation whose stages satisfy a property is reindexed by a directed poset, and
  `Stacks.DirectedCokernelSystem.exists_directed_epi_of_filtered_colimit` is the same keeping
  track of the surjectivity of the transition maps.  Pure category theory, used for both tags.
* `Stacks.DirectedCokernelSystem.exists_directed_colimit_of_cokernel`: in an abelian category,
  if `p : G ⟶ M` is an epimorphism and the kernel of `p` is a filtered colimit of a diagram
  `A`, then `M` is the colimit of the quotients `G/A_j` over a directed poset, and every
  transition map of that system is an epimorphism.  This is the construction of the source's
  proof, carried out once in the abstract.

## Implementation notes

### Why the quotients are one cokernel

The system `j ↦ G/𝒦_j` is not built stage by stage.  The inclusions `𝒦_j ⟶ 𝒦 ⟶ G` assemble
into a single natural transformation `β : A ⟶ (Functor.const J).obj G` in the functor category,
and the system is `cokernel β`.  Two things then come for free, and they are the two
conclusions that are easy to get wrong.  Surjectivity of the transition maps is
`Stacks.DirectedCokernelSystem.epi_cokernel_map`: the transition map is preceded by the
epimorphism `(cokernel.π β).app j` and the composite is the epimorphism
`(cokernel.π β).app j'`.  And the colimit is `M` itself, because a cocone on `cokernel β`
restricts to a map out of `G` killing `kernel p`, which factors through the epimorphism `p`
uniquely.

### The carried inputs of Stacks 086Y, and why each is general

Three hypotheses are carried.  Each is quantified over its own modules, none has the
conclusion of this theorem as its consequent, and none mentions the module `M` of the
statement.

* `h07V9` is **Stacks 07V9**, that a quasi-coherent module on a quasi-compact and
  quasi-separated algebraic space is a filtered colimit of modules of finite presentation.  It
  is spelled exactly as the hypothesis `h07V9` of
  `AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone_of_07V9`, which is
  the form in which this tree already carries that tag, so one discharge serves both.  Stacks
  07V9 *is* proved in this tree, as
  `AlgebraicGeometry.Space.isFilteredColimit_isFinitePresentation_of_isQuasiCompactSpace`, over
  its own seven cited inputs; that theorem concludes Mathlib's
  `SheafOfModules.IsFinitePresentation` over an index category in `Type (u + 1)`, whereas the
  spelling here asks for `SheafOfModules.IsFinitePresentationOnSite` over a small index
  category.  The two renderings of Stacks 03DL(7) are compared in
  `AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite`, but
  that bridge needs the structure sheaf to take values in `RingCat.{max u v}`, which on the
  small étale site of an algebraic space is `RingCat.{u + 1}` and not the `RingCat.{u}` the
  structure sheaf actually has.  So the spelling carried here is not deduced from that
  theorem, and is disclosed in the tag's clause as the small-index on-site form.
* `hstage` is the step of the source's proof that uses finite type: some stage of a filtered
  colimit presentation of a finite type quasi-coherent module already surjects onto it.  The
  source proves it by choosing an étale surjection `U ⟶ X` with `U` affine and finitely many
  sections of `ℱ` over `U` generating `ℱ|_U`, which lift to a stage because `U` is affine.
  Over a topological space this is Stacks 01BB, proved as
  `Stacks.SheafOfModules.exists_epi_to_colimit_of_isFiniteType`; that result is about a
  quasi-compact *space*, not a site, and the étale-chart form is not in this tree.
* `hcoker` is **Stacks 0H98**, that the cokernel of a map from a finite type module to a module
  of finite presentation is of finite presentation.  Stacks 0H98 is proved for an arbitrary
  ringed site, as `Stacks.SheafOfModules.LocalCokernel.isFinitePresentation_cokernel`, but in
  Mathlib's `SheafOfModules.IsFinitePresentation`; by the universe obstruction of the previous
  paragraph that does not transfer to the on-site rendering used here, so the on-site form is
  carried.  Its source module is asked to be of finite type in Mathlib's sense, which is what
  `AlgebraicGeometry.Space.finiteTypeQuasicoherentSubobjectProperty` supplies.

Everything else the source's proof uses is discharged from the tree: quasi-coherence of the
kernel of a map of quasi-coherent modules, by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_kernel_of_isCartesian` together with
Descent, Proposition 03DX(2); the directedness and the colimit property of the diagram of
finite type quasi-coherent submodules of that kernel, which is Stacks 0829, by
`AlgebraicGeometry.Space.isFiltered_finiteTypeQuasicoherentSubobject` and
`AlgebraicGeometry.Space.isColimit_finiteTypeQuasicoherentSubobjectCocone_of_07V9`; and the
invariance of finite presentation under isomorphism, by
`SheafOfModules.IsFinitePresentationOnSite.of_iso`.  The abelian structure of the category of
`𝒪_X`-modules is Mathlib's `SheafOfModules.instAbelian`, available at the universes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean`, which is where the kernels and
cokernels used throughout come from.

### What Stacks 082A rests on

The source's proof of Stacks 082A writes the algebra's underlying module as a directed colimit
of finitely presented modules, forms the symmetric algebra `ℬ_i = Sym(ℱ_i)`, takes the kernel
ideal `ℐ_i` of `ℬ_i ⟶ 𝒜`, writes `ℐ_i` as the colimit of its finite type quasi-coherent
submodules and divides.  Of that route this tree has the symmetric algebra of a module on an
algebraic space, `AlgebraicGeometry.Space.symmetricAlgebraSheaf`, but neither its
quasi-coherence, nor the quotient of an algebra sheaf by an ideal, nor any image factorization
in `AlgebraicGeometry.Space.AlgebraSheaf` — the category has a kernel pair and nothing more,
and the universe gap between the structure sheaf and the algebra's sections is what blocks the
missing pieces, as the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeSubalgebras.lean` records for Stacks 082B.
So for Stacks 082A only the final step of the source's argument is proved here: the passage
from a *filtered* system of finitely presented quasi-coherent algebras with colimit `𝒜` to a
*directed* one, which is the word "directed" in the statement.  The filtered system itself is
the hypothesis `hfiltered`, and the tag's clause says so.

## References

* [Stacks Project, Tag 086Y](https://stacks.math.columbia.edu/tag/086Y)
* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 086M](https://stacks.math.columbia.edu/tag/086M)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
* [Stacks Project, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t u v v' w w' c wC

namespace Stacks.DirectedCokernelSystem

/-! ### Reindexing a filtered colimit by a directed poset -/

section Reindex

variable {C : Type c} [Category.{wC, c} C]

/-- Whiskering a colimit cocone with a final functor leaves it a colimit cocone, in the shape
in which the reindexing below consumes it.

This is `CategoryTheory.Functor.Final.isColimitWhiskerEquiv`, stated as a named lemma over
abstract data so that the reindexing theorem instantiates it instead of re-elaborating it. -/
noncomputable def isColimit_whiskerLeft {I : Type v'} [Category.{w', v'} I] {J : Type v}
    [Category.{w, v} J] (r : I ⥤ J) [r.Final] (Q : J ⥤ C) (M : C)
    (q : Q ⟶ (Functor.const J).obj M)
    (hq : IsColimit (Cocone.mk M q)) :
    IsColimit (Cocone.mk M (Functor.whiskerLeft r q)) :=
  (Functor.Final.isColimitWhiskerEquiv r (Cocone.mk M q)).symm hq

/-- A small-enough filtered category admits a final functor from a directed poset in `Type t`. -/
private theorem exists_directed_final (J : Type v) [Category.{w, v} J] [IsFiltered J]
    [LocallySmall.{t} J] [FinallySmall.{t} J] :
    ∃ (I : Type t) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ J), F.Final := by
  obtain ⟨S, instS, hS, e, he⟩ := FinallySmall.exists_of_isFiltered.{t} J
  let _ := instS
  let _ : IsFiltered S := hS
  let _ : e.Final := he
  obtain ⟨I, instI, hIdir, hIne, r, hr⟩ := CategoryTheory.IsFiltered.exists_directed S
  let _ := instI
  let _ : r.Final := hr
  exact ⟨I, instI, hIne, hIdir, r ⋙ e, Functor.final_comp r e⟩

/-- A filtered colimit presentation is reindexed by a directed poset: if `Q` is a
filtered diagram, locally small and finally small at the universe `t`, with colimit `M`, and if
every `Q.obj j` satisfies `P`, then `M` is the colimit of a diagram indexed by a directed
poset in `Type t` whose objects satisfy `P`.

A small filtered category maps finally into `Q`'s index category, and a directed poset
maps finally into that; the composite is final, so whiskering along it preserves the colimit,
and `P` is inherited because every object of the new diagram is one of the old. -/
@[sga "4 I 8.2.2" "more general"]
theorem exists_directed_of_filtered_colimit {J : Type v} [Category.{w, v} J] [IsFiltered J]
    [LocallySmall.{t} J] [FinallySmall.{t} J]
    (P : C → Prop) (Q : J ⥤ C) (M : C) (q : Q ⟶ (Functor.const J).obj M)
    (hq : IsColimit (Cocone.mk M q)) (hP : ∀ j, P (Q.obj j)) :
    ∃ (I : Type t) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ C) (φ : D ⟶ (Functor.const I).obj M) (_ : IsColimit (Cocone.mk M φ)),
      ∀ i, P (D.obj i) := by
  obtain ⟨I, instI, hIne, hIdir, F, _⟩ := exists_directed_final.{t} J
  exact ⟨I, instI, hIne, hIdir, F ⋙ Q, Functor.whiskerLeft F q,
    isColimit_whiskerLeft F Q M q hq, fun i => hP _⟩

/-- `Stacks.DirectedCokernelSystem.exists_directed_of_filtered_colimit` keeping track, in
addition, of the surjectivity of the transition maps: every transition map of the reindexed
diagram is one of the original, so if all of those are epimorphisms then so are all of
these. -/
theorem exists_directed_epi_of_filtered_colimit {J : Type v} [Category.{w, v} J] [IsFiltered J]
    [LocallySmall.{t} J] [FinallySmall.{t} J]
    (P : C → Prop) (Q : J ⥤ C) (M : C) (q : Q ⟶ (Functor.const J).obj M)
    (hq : IsColimit (Cocone.mk M q)) (hP : ∀ j, P (Q.obj j))
    (hepi : ∀ (i j : J) (f : i ⟶ j), Epi (Q.map f)) :
    ∃ (I : Type t) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ C) (φ : D ⟶ (Functor.const I).obj M) (_ : IsColimit (Cocone.mk M φ)),
      (∀ i, P (D.obj i)) ∧ ∀ (i j : I) (h : i ≤ j), Epi (D.map (homOfLE h)) := by
  obtain ⟨I, instI, hIne, hIdir, F, _⟩ := exists_directed_final.{t} J
  exact ⟨I, instI, hIne, hIdir, F ⋙ Q, Functor.whiskerLeft F q,
    isColimit_whiskerLeft F Q M q hq, fun i => hP _, fun i j h => hepi _ _ _⟩

end Reindex

/-! ### The quotient system of an epimorphism -/

section Quotients

attribute [local instance] hasCokernel_of_hasCokernel_app
  evaluation_preservesColimit_of_hasCokernel_app

variable {J : Type v} [Category.{w, v} J] {C : Type c} [Category.{wC, c} C] [Abelian C]

/-- The projection to a cokernel in a functor category is an epimorphism at every index:
evaluation preserves the cokernel, and the projection becomes `cokernel.π` of the evaluated
map after composition with that isomorphism. -/
theorem epi_app_cokernel_π {A B : J ⥤ C} (α : A ⟶ B) (j : J) :
    Epi ((cokernel.π α).app j) := by
  have h : (cokernel.π α).app j ≫ (PreservesCokernel.iso ((evaluation J C).obj j) α).hom =
      cokernel.π (((evaluation J C).obj j).map α) :=
    PreservesCokernel.π_iso_hom ((evaluation J C).obj j) α
  have hepi : Epi ((cokernel.π α).app j ≫
      (PreservesCokernel.iso ((evaluation J C).obj j) α).hom) := by
    rw [h]
    infer_instance
  exact (epi_comp_iff_of_isIso _ _).mp hepi

/-- For a natural transformation into a constant functor, the cokernel projection at one index
followed by a transition map of the cokernel is the cokernel projection at the other index. -/
theorem cokernel_π_app_comp_map (G : C) {A : J ⥤ C} (α : A ⟶ (Functor.const J).obj G)
    {j j' : J} (f : j ⟶ j') :
    (cokernel.π α).app j ≫ (cokernel α).map f = (cokernel.π α).app j' := by
  have h := (cokernel.π α).naturality f
  change ((Functor.const J).obj G).map f ≫ (cokernel.π α).app j' =
    (cokernel.π α).app j ≫ (cokernel α).map f at h
  simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] using h.symm

/-- **Every transition map of the quotient system is surjective.** In the cokernel of a natural
transformation into a constant functor every transition map is an epimorphism, because it is
preceded by the epimorphism `cokernel.π` at the source index and that composite is the
epimorphism `cokernel.π` at the target index. -/
theorem epi_cokernel_map (G : C) {A : J ⥤ C} (α : A ⟶ (Functor.const J).obj G)
    {j j' : J} (f : j ⟶ j') : Epi ((cokernel α).map f) := by
  have hπ₁ : Epi ((cokernel.π α).app j') := epi_app_cokernel_π α j'
  have hc : Epi ((cokernel.π α).app j ≫ (cokernel α).map f) := by
    rw [cokernel_π_app_comp_map G α f]
    exact hπ₁
  exact (epi_comp_iff_of_epi ((cokernel.π α).app j) _).mp hc

variable {G M : C} (p : G ⟶ M)

/-- The composite `A ⟶ (Functor.const J).obj (kernel p) ⟶ (Functor.const J).obj G`, whose
cokernel is the system of quotients of `G`. -/
noncomputable def kernelDiagramInclusion {A : J ⥤ C} (a : A ⟶ (Functor.const J).obj (kernel p)) :
    A ⟶ (Functor.const J).obj G :=
  a ≫ (Functor.const J).map (kernel.ι p)

theorem kernelDiagramInclusion_app {A : J ⥤ C} (a : A ⟶ (Functor.const J).obj (kernel p))
    (j : J) : (kernelDiagramInclusion p a).app j = a.app j ≫ kernel.ι p :=
  rfl

theorem kernelDiagramInclusion_comp {A : J ⥤ C} (a : A ⟶ (Functor.const J).obj (kernel p)) :
    kernelDiagramInclusion p a ≫ (Functor.const J).map p = 0 := by
  refine NatTrans.ext (funext fun j => ?_)
  show (a.app j ≫ kernel.ι p) ≫ p = 0
  rw [Category.assoc, kernel.condition, comp_zero]

/-- The cocone on the quotient system with vertex `M`, whose leg at `j` is induced by `p`. -/
noncomputable def quotientCocone {A : J ⥤ C} (a : A ⟶ (Functor.const J).obj (kernel p)) :
    cokernel (kernelDiagramInclusion p a) ⟶ (Functor.const J).obj M :=
  cokernel.desc _ ((Functor.const J).map p) (kernelDiagramInclusion_comp p a)

theorem π_comp_quotientCocone {A : J ⥤ C} (a : A ⟶ (Functor.const J).obj (kernel p)) (j : J) :
    (cokernel.π (kernelDiagramInclusion p a)).app j ≫ (quotientCocone p a).app j = p := by
  have h := congrArg (fun η : (Functor.const J).obj G ⟶ (Functor.const J).obj M => η.app j)
    (cokernel.π_desc (kernelDiagramInclusion p a) ((Functor.const J).map p)
      (kernelDiagramInclusion_comp p a))
  change (cokernel.π (kernelDiagramInclusion p a)).app j ≫ (quotientCocone p a).app j =
    ((Functor.const J).map p).app j at h
  exact h

variable [IsFiltered J] [Epi p]

/-- **`M` is the colimit of the quotient system.** If `p : G ⟶ M` is an epimorphism and the
kernel of `p` is the colimit of a filtered diagram `A`, then `M`, with the legs induced by `p`,
is the colimit of the system of quotients of `G` by the stages of `A`.

A cocone `s` on the quotient system gives a map `G ⟶ s.pt`, namely `cokernel.π` at any index
followed by the leg of `s` there; filteredness of the index category makes that map independent
of the index.  It kills `kernel p`, because `kernel p` is the colimit of the `A.obj j` and each
`A.obj j ⟶ G ⟶ cokernel` vanishes, so it factors through the epimorphism `p`, uniquely. -/
noncomputable def isColimitQuotientCocone {A : J ⥤ C}
    (a : A ⟶ (Functor.const J).obj (kernel p)) (ha : IsColimit (Cocone.mk (kernel p) a)) :
    IsColimit (Cocone.mk M (quotientCocone p a)) := by
  classical
  let β := kernelDiagramInclusion p a
  let _ : Nonempty J := IsFiltered.nonempty
  let j₀ : J := Classical.choice (inferInstance : Nonempty J)
  let g₀ (s : Cocone (cokernel β)) : G ⟶ s.pt := (cokernel.π β).app j₀ ≫ s.ι.app j₀
  have hg₀ (s : Cocone (cokernel β)) (j : J) :
      g₀ s = (cokernel.π β).app j ≫ s.ι.app j := by
    obtain ⟨k, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs j₀ j
    calc
      g₀ s = (cokernel.π β).app j₀ ≫ ((cokernel β).map f ≫ s.ι.app k) := by
        dsimp only [g₀]
        rw [← s.w f]
      _ = ((cokernel.π β).app j₀ ≫ (cokernel β).map f) ≫ s.ι.app k := (Category.assoc _ _ _).symm
      _ = (cokernel.π β).app k ≫ s.ι.app k := by rw [cokernel_π_app_comp_map G β f]
      _ = ((cokernel.π β).app j ≫ (cokernel β).map g) ≫ s.ι.app k := by
        rw [cokernel_π_app_comp_map G β g]
      _ = (cokernel.π β).app j ≫ s.ι.app j := by rw [Category.assoc, s.w g]
  have hker (s : Cocone (cokernel β)) : kernel.ι p ≫ g₀ s = 0 := by
    refine ha.hom_ext fun j => ?_
    have hβ : β.app j ≫ (cokernel.π β).app j = 0 :=
      congrArg (fun η : A ⟶ cokernel β => η.app j) (cokernel.condition β)
    rw [hg₀ s j]
    calc
      a.app j ≫ kernel.ι p ≫ (cokernel.π β).app j ≫ s.ι.app j =
          (β.app j ≫ (cokernel.π β).app j) ≫ s.ι.app j := by
            rw [kernelDiagramInclusion_app]
            simp only [Category.assoc]
      _ = 0 := by rw [hβ, zero_comp]
      _ = a.app j ≫ 0 := by simp
  refine
    { desc := fun s => Abelian.epiDesc p (g₀ s) (hker s)
      fac := ?_
      uniq := ?_ }
  · intro s j
    refine (cancel_epi ((cokernel.π β).app j)).1 ?_
    calc
      (cokernel.π β).app j ≫ (quotientCocone p a).app j ≫ Abelian.epiDesc p (g₀ s) (hker s) =
          p ≫ Abelian.epiDesc p (g₀ s) (hker s) := by
            rw [← Category.assoc, π_comp_quotientCocone p a j]
      _ = g₀ s := Abelian.comp_epiDesc p (g₀ s) (hker s)
      _ = (cokernel.π β).app j ≫ s.ι.app j := hg₀ s j
  · intro s m hm
    refine (cancel_epi p).1 ?_
    have hpm : p ≫ m = g₀ s := by
      calc
        p ≫ m = ((cokernel.π β).app j₀ ≫ (quotientCocone p a).app j₀) ≫ m := by
          rw [π_comp_quotientCocone p a j₀]
        _ = (cokernel.π β).app j₀ ≫ s.ι.app j₀ := by
          rw [Category.assoc, hm j₀]
        _ = g₀ s := rfl
    rw [hpm, Abelian.comp_epiDesc]

/-- **The construction of the source's proof, in the abstract.** Let `p : G ⟶ M` be an
epimorphism in an abelian category and let the kernel of `p` be the colimit of a filtered
diagram `A` which is locally small and finally small at the universe `t`.  If every quotient
`G/A_j` satisfies a property `P` invariant under isomorphism, then `M` is the colimit of a
diagram indexed by a directed poset in `Type t`, all of whose objects satisfy `P` and
all of whose transition maps are epimorphisms. -/
theorem exists_directed_colimit_of_cokernel [LocallySmall.{t} J] [FinallySmall.{t} J]
    (P : C → Prop) (hiso : ∀ {Y Z : C}, (Y ≅ Z) → P Y → P Z)
    {A : J ⥤ C} (a : A ⟶ (Functor.const J).obj (kernel p))
    (ha : IsColimit (Cocone.mk (kernel p) a))
    (hP : ∀ j, P (cokernel (a.app j ≫ kernel.ι p))) :
    ∃ (I : Type t) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ C) (φ : D ⟶ (Functor.const I).obj M) (_ : IsColimit (Cocone.mk M φ)),
      (∀ i, P (D.obj i)) ∧ ∀ (i j : I) (h : i ≤ j), Epi (D.map (homOfLE h)) := by
  refine exists_directed_epi_of_filtered_colimit P (cokernel (kernelDiagramInclusion p a)) M
    (quotientCocone p a) (isColimitQuotientCocone p a ha) (fun j => ?_)
    (fun i j f => epi_cokernel_map G _ f)
  exact hiso (PreservesCokernel.iso ((evaluation J C).obj j)
    (kernelDiagramInclusion p a)).symm (hP j)

end Quotients

end Stacks.DirectedCokernelSystem

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- The category of `𝒪_X`-modules with sections in the universe of the schemes is abelian.

This is Mathlib's `SheafOfModules.instAbelian` at the universes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean`.  It is named once, as a local
instance, so that the kernels and cokernels of the statements below are found without instance
search having to rediscover the sheafification instances each time. -/
noncomputable local instance abelian_modules_of_algebraicSpace :
    Abelian (Modules.{u, u} B S hS X hX) :=
  SheafOfModules.instAbelian
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))

end AlgebraicGeometry.Space

end
