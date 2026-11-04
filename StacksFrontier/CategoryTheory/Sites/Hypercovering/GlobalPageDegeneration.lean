module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.GlobalEdgeNaturality
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PageDegeneration

/-!
# Degeneration ingredients for the spectral sequence of a hypercovering of the final presheaf

This file collects the ingredients of [Stacks, Tag 09VZ] in degrees above zero which are
available in the setting of hypercoverings of the **final presheaf**, that is for
`Stacks.CategoryTheory.Hypercovering.HypercoveringOfTerminal` and Čech cohomology taken in
`FormalCoproduct C`.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.evalBaseπ`: the component of a section of a presheaf on a
  formal coproduct of objects of the site at a summand.
* `Stacks.CategoryTheory.Hypercovering.HypercoveringOf.Hom.comp`: composition of morphisms of
  hypercoverings of a presheaf.

## Main results

* `CategoryTheory.SpectralSequence.exists_rel_page_apply_eq_zero`: **page-by-page propagation of
  degeneration.**  For an arbitrary family of spectral sequences of abelian groups and an
  arbitrary family of morphisms between its members, if every element of the initial page at a
  fixed bidegree is killed by some one of those morphisms, then so is every element of every
  later page.
* `CategoryTheory.SpectralSequence.exists_rel_pageInfinity_apply_eq_zero`: the same conclusion on
  the **infinity page** of a first-quadrant cohomological spectral sequence, which is the form in
  which a degeneration statement meets the graded pieces of an abutment.
* `Stacks.CategoryTheory.Hypercovering.exists_isCovering_of_presieves`: a covering presieve of
  each summand of a formal coproduct of objects of the site assembles into a covering morphism
  onto it ([Stacks, Tag 01G3]), the analogue for `FormalCoproduct C` of
  `exists_isCoveringOver_of_presieves`.
* `Stacks.CategoryTheory.Hypercovering.homologyπ_cochainComplexFunctorMap_eq_zero`: **a Čech
  cohomology class dies along a refinement whose component in its own degree factors through a
  morphism killing a representing cocycle.**
* `Stacks.CategoryTheory.Hypercovering.HypercoveringOf.Hom.cechCohomologyMap_comp`: the Čech
  pullback along a composite of morphisms of hypercoverings is the composite of the pullbacks.

## Implementation notes

The propagation lemmas are stated for a bare family `E : D → SpectralSequence …` together with a
family `Rel` of "refinements" and a morphism of spectral sequences for each refinement.  No
functoriality, no composition and no category structure on `D` is required, because the induction
on the page applies the inductive hypothesis at the *same* object and keeps the bidegree fixed.
That is what makes them usable for hypercoverings of the final presheaf, which carry
`Stacks.CategoryTheory.Hypercovering.HypercoveringOf.Hom` but are not known to form a category
with the smallness a colimit would need.

## References

* [Stacks Project, Tag 09VZ](https://stacks.math.columbia.edu/tag/09VZ)
* [Stacks Project, Tag 09VY](https://stacks.math.columbia.edu/tag/09VY)
* [Stacks Project, Tag 01GJ](https://stacks.math.columbia.edu/tag/01GJ)
* [Stacks Project, Tag 01G3](https://stacks.math.columbia.edu/tag/01G3)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public noncomputable section

universe t q w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

/-! ### Degeneration propagates from the initial page to every page -/

namespace CategoryTheory.SpectralSequence

variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- **Degeneration at a fixed bidegree propagates from the initial page to every page.**

Let `E` be a family of spectral sequences of abelian groups indexed by a type `D`, let `Rel K L`
be a type of "refinements" of `K` by `L` and let every refinement induce a morphism of spectral
sequences `E K ⟶ E L`.  If at the bidegree `pq` every element of the initial page of every `E K`
is killed by the morphism of some refinement, then the same holds on every page `r ≥ r₀`.

The passage from `E_r` to `E_{r+1}` is not a formal consequence of the statement on `E_{r₀}`:
`E_{r+1}` is a *subquotient* of `E_r`, so there is no morphism `E_{r₀} ⟶ E_r` along which the
initial statement could be pushed.  It is an induction on the page carried by
`page_apply_eq_zero_of_cycles_apply_eq_zero`: an element of `E_{r+1}^{pq}` is the class of a
cycle of `E_r^{pq}` by `exists_cycles_homologyπ_eq`, and the inductive hypothesis applied to the
underlying element of that cycle produces the refinement.

Neither composition of refinements nor functoriality of `E` is used: the induction applies the
inductive hypothesis at the same object and at the same bidegree. -/
theorem exists_rel_page_apply_eq_zero {D : Type*} {Rel : D → D → Type*}
    (E : D → SpectralSequence AddCommGrpCat.{t} c r₀)
    (Φ : ∀ {K L : D}, Rel K L → (E K ⟶ E L)) (pq : κ)
    (hbase : ∀ (K : D) (x : ToType (((E K).page r₀ le_rfl).X pq)),
      ∃ (L : D) (g : Rel K L),
        ConcreteCategory.hom (((Φ g).hom r₀ le_rfl).f pq) x = 0)
    (r : ℤ) (hr : r₀ ≤ r) (K : D) (x : ToType (((E K).page r hr).X pq)) :
    ∃ (L : D) (g : Rel K L),
      ConcreteCategory.hom (((Φ g).hom r hr).f pq) x = 0 := by
  induction r, hr using Int.leInduction with
  | base => exact hbase K x
  | succ r hrr ih =>
    obtain ⟨z, hz⟩ :=
      exists_cycles_homologyπ_eq (E K) r (r + 1) pq rfl hrr (Int.le_add_one hrr) x
    obtain ⟨L, g, hw⟩ := ih (ConcreteCategory.hom (((E K).page r hrr).iCycles pq) z)
    exact ⟨L, g, page_apply_eq_zero_of_cycles_apply_eq_zero (Φ g) r (r + 1) pq rfl hrr
      (Int.le_add_one hrr) x z hz hw⟩

/-- **Degeneration at a bidegree passes from the initial page to the infinity page**, for a
first-quadrant cohomological spectral sequence.

In the first quadrant the differentials into and out of `pq` vanish from the page
`max r₀ (max (pq.1 + 1) (pq.2 + 2))` on, for *every* spectral sequence at once
(`CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom` and `hasEdgeEpiAtFrom`), so one page can be
chosen before the refinement is produced; on it `Hom.mapPageInfinity` is the map on that page
conjugated by `pageInfinityIso` (`Hom.mapPageInfinity_eq`), and
`exists_rel_page_apply_eq_zero` applies.

This is the form in which a degeneration statement meets the abutment of a first-quadrant
spectral sequence: the field `gradedIso` of
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo` identifies `E_∞^{p,q}` with the graded
piece `gr^p H^{p+q}`. -/
theorem exists_rel_pageInfinity_apply_eq_zero {D : Type*} {Rel : D → D → Type*}
    (E : D → CohomologicalSpectralSequenceNat AddCommGrpCat.{t} r₀) (pq : ℕ × ℕ)
    (Φ : ∀ {K L : D}, Rel K L → (E K ⟶ E L))
    (hbase : ∀ (K : D) (x : ToType (((E K).page r₀ le_rfl).X pq)),
      ∃ (L : D) (g : Rel K L),
        ConcreteCategory.hom (((Φ g).hom r₀ le_rfl).f pq) x = 0)
    (K : D) (x : ToType ((E K).pageInfinity pq)) :
    ∃ (L : D) (g : Rel K L),
      ConcreteCategory.hom (Hom.mapPageInfinity (Φ g) pq) x = 0 := by
  set r : ℤ := max r₀ (max ((pq.1 : ℤ) + 1) ((pq.2 : ℤ) + 2)) with hrdef
  have hr₀ : r₀ ≤ r := le_max_left _ _
  have hA : (pq.1 : ℤ) + 1 ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hB : (pq.2 : ℤ) + 2 ≤ r := (le_max_right _ _).trans (le_max_right _ _)
  have edge : ∀ K' : D, (E K').HasEdgeMonoAtFrom pq r ∧ (E K').HasEdgeEpiAtFrom pq r := fun K' =>
    ⟨CohomologicalSpectralSequenceNat.hasEdgeMonoAtFrom (E K') pq r hA hr₀,
      CohomologicalSpectralSequenceNat.hasEdgeEpiAtFrom (E K') pq r hB hr₀⟩
  obtain ⟨_, _⟩ := edge K
  obtain ⟨L, g, hg⟩ := exists_rel_page_apply_eq_zero E Φ pq hbase r hr₀ K
    (ConcreteCategory.hom ((E K).pageInfinityIso pq r).hom x)
  obtain ⟨_, _⟩ := edge L
  refine ⟨L, g, ?_⟩
  rw [Hom.mapPageInfinity_eq (Φ g) pq r hr₀, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, hg, map_zero]

end CategoryTheory.SpectralSequence

/-! ### Sections of a presheaf on a formal coproduct of objects of the site -/

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

section EvalOpBase

variable (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w})

/-- **The component at a summand of a section of a presheaf on a formal coproduct.**  This is
`CategoryTheory.Limits.Pi.π`, restated with its source written as the value of
`FormalCoproduct.evalOp`, which is the form the Čech complex of a simplicial semi-representable
object presents it in.

It is the analogue for `FormalCoproduct C` of
`Stacks.CategoryTheory.Hypercovering.evalOpπ`, which is stated for `FormalCoproduct (Over X)`;
hypercoverings of the final presheaf live in the former. -/
def evalBaseπ (V : FormalCoproduct.{max u v w} C) (i : V.I) :
    ((evalOp.{max u v w} C AddCommGrpCat.{max u v w}).obj P).obj (op V) ⟶
      P.obj (op (V.obj i)) :=
  Pi.π _ i

/-- **Restriction along a morphism of formal coproducts, componentwise**: the component at `i` of
the restriction along `u` is the restriction along the component `u.φ i` of the component at
`u.f i`. -/
@[reassoc]
lemma map_comp_evalBaseπ {Z V : FormalCoproduct.{max u v w} C} (u : Z ⟶ V) (i : Z.I) :
    ((evalOp.{max u v w} C AddCommGrpCat.{max u v w}).obj P).map u.op ≫ evalBaseπ P Z i =
      evalBaseπ P V (u.f i) ≫ P.map (u.φ i).op := by
  simp [evalBaseπ, evalOp]

/-- **A section of a presheaf on a formal coproduct is determined by its components.** -/
lemma evalBase_ext (V : FormalCoproduct.{max u v w} C)
    {x y : ToType (((evalOp.{max u v w} C AddCommGrpCat.{max u v w}).obj P).obj (op V))}
    (h : ∀ i : V.I, (ConcreteCategory.hom (evalBaseπ P V i)) x =
      (ConcreteCategory.hom (evalBaseπ P V i)) y) : x = y := by
  refine Concrete.limit_ext (Discrete.functor (fun j : V.I => P.obj (op (V.obj j)))) x y ?_
  rintro ⟨j⟩
  exact h j

end EvalOpBase

/-! ### Assembling a covering morphism of formal coproducts -/

variable [HasPullbacks C]

/-- **A covering presieve of each summand assembles into a covering morphism**, which is
[Stacks, Tag 01G3] read as a construction: the summands of the source are the pairs of a summand
`j` of `V` and a member of the presieve `R j`, and the fibre of the resulting morphism over `j`
is exactly `R j`.

This is the analogue for `FormalCoproduct C` of
`Stacks.CategoryTheory.Hypercovering.exists_isCoveringOver_of_presieves`, which is stated for
`FormalCoproduct (Over X)`; hypercoverings of the final presheaf live in the former. -/
lemma exists_isCovering_of_presieves (J : Pretopology C) (V : FormalCoproduct.{max u v w} C)
    (R : ∀ j : V.I, Presieve (V.obj j)) (hR : ∀ j, R j ∈ J (V.obj j)) :
    ∃ (Z : FormalCoproduct.{max u v w} C) (u : Z ⟶ V), IsCovering J u ∧
      ∀ i : Z.I, R (u.f i) (u.φ i) := by
  classical
  refine ⟨⟨(Σ j : V.I, (R j).uncurry), fun p => p.2.val.1⟩,
    { f := fun p => p.1, φ := fun p => p.2.val.2 }, ?_, fun i => i.2.property⟩
  intro i
  have hEq : Presieve.ofArrows
      (fun j : {p : (Σ j : V.I, (R j).uncurry) // p.1 = i} => j.1.2.val.1)
      (fun j => j.1.2.val.2 ≫ eqToHom (congrArg V.obj j.2)) = R i := by
    apply le_antisymm
    · intro Y f hf
      rcases hf with ⟨j⟩
      rcases j with ⟨⟨i', a⟩, hi⟩
      dsimp at hi
      subst i'
      simp only [eqToHom_refl, Category.comp_id]
      exact a.property
    · intro Y f hf
      exact Presieve.ofArrows.mk' (⟨⟨i, ⟨⟨Y, f⟩, hf⟩⟩, rfl⟩ :
        {p : (Σ j : V.I, (R j).uncurry) // p.1 = i}) rfl (by simp)
  exact hEq ▸ hR i

/-! ### A cocycle killed by a covering dies on a refinement factoring through it -/

omit [HasPullbacks C] in
/-- **A Čech cohomology class dies along a refinement whose component in its own degree factors
through a morphism killing a representing cocycle.**

Let `f : L ⟶ K` be a morphism of simplicial semi-representable objects whose component in degree
`p` factors as `g ≫ u` through a morphism `u : Z ⟶ K_p`, and let `z` be a degree-`p` cocycle of
the complex of sections of `K` each of whose components restricts to zero along the corresponding
component of `u`.  Then the class of `z` restricts to zero on `L`.

This is the content of the second-page vanishing of [Stacks, Tag 01H0] for hypercoverings of the
final presheaf *other than* the production of the refinement: the components of a cocycle with
locally zero coefficients are killed on coverings of the summands of `K_p`, those coverings
assemble into a covering morphism `u : Z ⟶ K_p` by `exists_isCovering_of_presieves`, and what
remains is a morphism of hypercoverings whose degree-`p` component factors through `u`, that is
[Stacks, Tag 01GJ] for hypercoverings of the final presheaf.  Nothing here assumes the existence
of such a morphism: `f`, `g` and the factorisation are data. -/
theorem homologyπ_cochainComplexFunctorMap_eq_zero
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w})
    {K L : SimplicialObject (FormalCoproduct.{max u v w} C)} (f : L ⟶ K) (p : ℕ)
    {Z : FormalCoproduct.{max u v w} C} (u : Z ⟶ K.obj (op ⦋p⦌))
    (g : L.obj (op ⦋p⦌) ⟶ Z) (hfg : g ≫ u = f.app (op ⦋p⦌))
    (z : ToType (((FormalCoproduct.cochainComplexFunctor K).obj P).cycles p))
    (hz : ∀ i : Z.I, ConcreteCategory.hom (P.map (u.φ i).op)
        (ConcreteCategory.hom (evalBaseπ P (K.obj (op ⦋p⦌)) (u.f i))
          (ConcreteCategory.hom
            (((FormalCoproduct.cochainComplexFunctor K).obj P).iCycles p) z)) = 0) :
    ConcreteCategory.hom (HomologicalComplex.homologyMap
          ((cochainComplexFunctorMap.{max u v w} f).app P) p)
        (ConcreteCategory.hom
          (((FormalCoproduct.cochainComplexFunctor K).obj P).homologyπ p) z) = 0 := by
  set ξ : ToType (((evalOp.{max u v w} C AddCommGrpCat.{max u v w}).obj P).obj
      (op (K.obj (op ⦋p⦌)))) :=
    ConcreteCategory.hom
      (((FormalCoproduct.cochainComplexFunctor K).obj P).iCycles p) z with hξ
  set φ : (FormalCoproduct.cochainComplexFunctor K).obj P ⟶
      (FormalCoproduct.cochainComplexFunctor L).obj P :=
    (cochainComplexFunctorMap.{max u v w} f).app P with hφ
  have hZero : ConcreteCategory.hom
      (((evalOp.{max u v w} C AddCommGrpCat.{max u v w}).obj P).map u.op) ξ = 0 := by
    refine evalBase_ext P Z (fun i => ?_)
    rw [← ConcreteCategory.comp_apply, map_comp_evalBaseπ, ConcreteCategory.comp_apply]
    exact (hz i).trans (map_zero (ConcreteCategory.hom (evalBaseπ P Z i))).symm
  have hξZero : ConcreteCategory.hom (φ.f p) ξ = 0 := by
    have hφp : ((evalOp.{max u v w} C AddCommGrpCat.{max u v w}).obj P).map u.op ≫
        ((evalOp.{max u v w} C AddCommGrpCat.{max u v w}).obj P).map g.op = φ.f p := by
      rw [← Functor.map_comp, ← op_comp, hfg]
      rfl
    have h1 := ConcreteCategory.congr_hom hφp ξ
    rw [ConcreteCategory.comp_apply, hZero, map_zero] at h1
    exact h1.symm
  have hcyc : ConcreteCategory.hom (HomologicalComplex.cyclesMap φ p) z = 0 := by
    refine (AddCommGrpCat.mono_iff_injective
      (((FormalCoproduct.cochainComplexFunctor L).obj P).iCycles p)).1 inferInstance ?_
    have h2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ p) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← hξ, hξZero] at h2
    rw [map_zero]
    exact h2
  have h3 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ p) z
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hcyc, map_zero] at h3
  exact h3

/-! ### Refinements of a hypercovering of a presheaf compose -/

section Composition

variable [HasEqualizers C] {J : Pretopology C} {G : Cᵒᵖ ⥤ Type q}

/-- **Morphisms of hypercoverings of a presheaf compose.**  The underlying morphisms of
simplicial semi-representable objects compose, and the compatibility with the augmentations is
the two compatibilities pasted. -/
def HypercoveringOf.Hom.comp {K L M : HypercoveringOf.{q, w} J G}
    (ψ : HypercoveringOf.Hom K L) (χ : HypercoveringOf.Hom L M) :
    HypercoveringOf.Hom K M where
  simplicialHom := ψ.simplicialHom ≫ χ.simplicialHom
  whiskerRight_comp_augmentation := by
    rw [Functor.whiskerRight_comp, Category.assoc, χ.whiskerRight_comp_augmentation,
      ψ.whiskerRight_comp_augmentation]

/-- **The Čech pullback along a composite of morphisms of hypercoverings is the composite of the
Čech pullbacks**, Čech cohomology being contravariant in the simplicial semi-representable
object. -/
lemma HypercoveringOf.Hom.cechCohomologyMap_comp {K L M : HypercoveringOf.{q, w} J G}
    (ψ : HypercoveringOf.Hom K L) (χ : HypercoveringOf.Hom L M)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p : ℕ) :
    (ψ.comp χ).cechCohomologyMap F p =
      χ.cechCohomologyMap F p ≫ ψ.cechCohomologyMap F p := by
  change HomologicalComplex.homologyMap
      ((cochainComplexFunctorMap.{w} (ψ.simplicialHom ≫ χ.simplicialHom)).app F.obj) p =
    HomologicalComplex.homologyMap
        ((cochainComplexFunctorMap.{w} χ.simplicialHom).app F.obj) p ≫
      HomologicalComplex.homologyMap
        ((cochainComplexFunctorMap.{w} ψ.simplicialHom).app F.obj) p
  rw [cochainComplexFunctorMap_comp, NatTrans.comp_app, HomologicalComplex.homologyMap_comp]

end Composition

end Stacks.CategoryTheory.Hypercovering

end
