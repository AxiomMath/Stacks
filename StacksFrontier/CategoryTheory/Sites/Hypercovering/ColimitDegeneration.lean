module

public import Mathlib.Algebra.Category.Grp.AB
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Refinement
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequenceSecondPage

/-!
# Čech cohomology with locally zero coefficients dies in the colimit over hypercoverings

The proof of [Stacks, Tag 01H0] rests on the following vanishing: for `q > 0` the colimit over
all hypercoverings `K` of `X` of `Ȟ^p(K, H^q(𝓕))` is zero, so that in the colimit the
hypercovering spectral sequence of [Stacks, Tag 01GY] has only its bottom row left. This file
proves that vanishing.

The mechanism is not special to the cohomology presheaves: what is used about `H^q(𝓕)` for
`q > 0` is only that it is **locally zero** -- every section over every object of the site is
killed by restricting along some covering, which for the cohomology presheaves is
[Stacks, Tag 01FW]. So the argument is carried out for an arbitrary locally zero presheaf of
abelian groups and specialised at the end.

## The argument

Let `P` be a locally zero presheaf of abelian groups, `K` a hypercovering of `X` and
`ξ ∈ Ȟ^p(K, P)`. Lift `ξ` to a cocycle in degree `p` of the Čech complex, that is to a section
of `P` on the semi-representable object `K_p = {U_i → X}`; its components are sections
`ξ_i ∈ P(U_i)`.  Local vanishing gives for each `i` a covering `{U_{i,j} → U_i}` of the site
with `ξ_i|_{U_{i,j}} = 0`.  Assembling those coverings gives a semi-representable object
`Z = {U_{i,j} → X}` together with a morphism `u : Z ⟶ K_p` which is covering in the sense of
[Stacks, Tag 01G3], and the restriction of the cocycle along `u` is zero because each of its
components is. By [Stacks, Tag 01GJ] there is a morphism of hypercoverings `f : L ⟶ K` whose
component in degree `p` factors through `u`; hence the cocycle restricts to zero on `L_p`, and so
the class of `ξ` in `Ȟ^p(L, P)` is zero.

Every element therefore dies after *some* refinement, and that is already enough for the colimit
to vanish: each leg of each cocone on the diagram of Čech cohomology groups kills every element
of its source, hence is zero, hence the cocone with the zero object as vertex is a colimit
cocone. No cofilteredness of the index category is needed for this.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.IsLocallyZero`: a presheaf of abelian groups all of whose
  sections are killed by restriction along a covering.
* `Stacks.CategoryTheory.Hypercovering.evalOpπ`: the component of a section of a presheaf on a
  formal coproduct at a summand.
* `Stacks.CategoryTheory.Hypercovering.Functorial.cechHypercoveringDiagram`: the diagram
  `K ↦ Ȟ^p(K, P)` on the hypercoverings of `X`, for a presheaf of coefficients.
* `Stacks.CategoryTheory.Hypercovering.Functorial.zeroCocone`: the cocone on that diagram with
  the zero object as vertex.

## Main results

* `Stacks.CategoryTheory.Hypercovering.exists_isCoveringOver_of_presieves`: a covering presieve
  of each summand of a semi-representable object assembles into a covering morphism onto it
  ([Stacks, Tag 01G3]).
* `Stacks.CategoryTheory.Hypercovering.exists_hypercovering_map_cechCohomology_eq_zero`: every
  Čech cohomology class with locally zero coefficients dies after a refinement of the
  hypercovering.
* `Stacks.CategoryTheory.Hypercovering.isLocallyZero_cohomologyPresheaf`: for `q > 0` the
  degree-`q` cohomology presheaf of an abelian sheaf is locally zero, which is
  [Stacks, Tag 01FW].
* `Stacks.CategoryTheory.Hypercovering.Functorial.isColimit_zeroCocone`: for locally zero
  coefficients the colimit of `K ↦ Ȟ^p(K, P)` over the hypercoverings of `X` is zero.
* `Stacks.CategoryTheory.Hypercovering.Functorial.isColimit_zeroCocone_cohomologyPresheaf`:
  `colim_K Ȟ^p(K, H^q(𝓕)) = 0` for `q > 0`.

## Implementation notes

The colimit statement is phrased as "the cocone with vertex `0` is a colimit cocone" rather than
as `IsZero (colimit …)`: the hypercoverings of `X` are indexed by a category whose objects live
one universe above the coefficients, so the colimit is not known to exist. The content is
`cocone_ι_app_eq_zero_of_isLocallyZero`, that every leg of every cocone vanishes.

The index category is the category of hypercoverings with *all* maps, not with maps up to
homotopy. Nothing in the argument needs the homotopy quotient, and a cocone on the diagram over
`HC(C, X)ᵒᵖ` restricts to one over `HypercoveringCat`, so the vanishing transports to the
homotopy category for any diagram restricting to this one along the quotient functor.

Sections of a presheaf on a formal coproduct are a product over the summands, and
`Limits.Pi.π` is stated with the product written as `∏ᶜ`, whereas the Čech complex has it
written as a value of `FormalCoproduct.evalOp`. The two spellings are definitionally equal but
not syntactically so, which blocks `rw` and `simp`; `evalOpπ` is the projection restated in the
second spelling, and `map_comp_evalOpπ` and `evalOp_ext` are the two facts about it the argument
uses.

The diagram is identified with the bottom row of the second page of [Stacks, Tag 01GY] on
objects, by `cechHypercoveringDiagram_obj_eq_pageTwo`.

## References

* [Stacks Project, Tag 01H0](https://stacks.math.columbia.edu/tag/01H0)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
* [Stacks Project, Tag 01GJ](https://stacks.math.columbia.edu/tag/01GJ)
* [Stacks Project, Tag 01G3](https://stacks.math.columbia.edu/tag/01G3)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.Limits.FormalCoproduct
open scoped ZeroObject

universe v

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type v} [SmallCategory C] [HasPullbacks C] {X : C}

/-! ### Sections of a presheaf on a formal coproduct -/

section EvalOp

variable (Q : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{v})

/-- The component at a summand of a section of a presheaf on a formal coproduct:
`CategoryTheory.Limits.Pi.π`, with its source written as the value of `FormalCoproduct.evalOp`. -/
def evalOpπ (V : FormalCoproduct.{v} (Over X)) (i : V.I) :
    ((evalOp.{v} (Over X) AddCommGrpCat.{v}).obj Q).obj (op V) ⟶ Q.obj (op (V.obj i)) :=
  Pi.π _ i

omit [HasPullbacks C] in
/-- Restriction along a morphism of formal coproducts, componentwise: the component at `i` of
the restriction along `u` is the restriction along the component `u.φ i` of the component at
`u.f i`. -/
@[reassoc]
lemma map_comp_evalOpπ {Z V : FormalCoproduct.{v} (Over X)} (u : Z ⟶ V) (i : Z.I) :
    ((evalOp.{v} (Over X) AddCommGrpCat.{v}).obj Q).map u.op ≫ evalOpπ Q Z i =
      evalOpπ Q V (u.f i) ≫ Q.map (u.φ i).op := by
  simp [evalOpπ, evalOp]

omit [HasPullbacks C] in
/-- A section of a presheaf on a formal coproduct is determined by its components. -/
lemma evalOp_ext (V : FormalCoproduct.{v} (Over X))
    {x y : ToType (((evalOp.{v} (Over X) AddCommGrpCat.{v}).obj Q).obj (op V))}
    (h : ∀ i : V.I, (ConcreteCategory.hom (evalOpπ Q V i)) x =
      (ConcreteCategory.hom (evalOpπ Q V i)) y) : x = y := by
  refine Concrete.limit_ext (Discrete.functor (fun j : V.I => Q.obj (op (V.obj j)))) x y ?_
  rintro ⟨j⟩
  exact h j

end EvalOp

/-! ### Locally zero presheaves -/

variable (J : Pretopology C)

/-- A presheaf of abelian groups is locally zero when every one of its sections, over every object
of the site, is killed by restriction along every member of some covering family of that object.
-/
def IsLocallyZero (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) : Prop :=
  ∀ (U : C) (ξ : ToType (P.obj (op U))), ∃ R ∈ J U,
    ∀ ⦃Y : C⦄ (g : Y ⟶ U), R g → (ConcreteCategory.hom (P.map g.op)) ξ = 0

variable {J}

/-- A covering presieve of each summand assembles into a covering morphism, which is
[Stacks, Tag 01G3] read as a construction: the summands of the source are the pairs of a summand
`j` of `V` and a member of the presieve `R j`, and the fibre of the resulting morphism over `j`
is exactly `R j`. -/
lemma exists_isCoveringOver_of_presieves (V : FormalCoproduct.{v} (Over X))
    (R : ∀ j : V.I, Presieve (V.obj j).left) (hR : ∀ j, R j ∈ J (V.obj j).left) :
    ∃ (Z : FormalCoproduct.{v} (Over X)) (u : Z ⟶ V), IsCoveringOver J u ∧
      ∀ i : Z.I, R (u.f i) (u.φ i).left := by
  classical
  refine ⟨⟨(Σ j : V.I, (R j).uncurry), fun p => Over.mk (p.2.val.2 ≫ (V.obj p.1).hom)⟩,
    { f := fun p => p.1, φ := fun p => Over.homMk p.2.val.2 }, ?_, fun i => i.2.property⟩
  intro i
  have hEq : Presieve.ofArrows
      (fun j : {p : (Σ j : V.I, (R j).uncurry) // p.1 = i} =>
        (Over.mk (j.1.2.val.2 ≫ (V.obj j.1.1).hom) : Over X).left)
      (fun j => (Over.homMk j.1.2.val.2 :
          (Over.mk (j.1.2.val.2 ≫ (V.obj j.1.1).hom) : Over X) ⟶ V.obj j.1.1).left ≫
        eqToHom (congrArg (fun k => (V.obj k).left) j.2)) = R i := by
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

/-- Every Čech cohomology class with locally zero coefficients dies after a refinement of the
hypercovering. -/
theorem exists_hypercovering_map_cechCohomology_eq_zero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (hP : IsLocallyZero J P)
    (K : SimplicialObject (FormalCoproduct.{v} (Over X))) (hK : IsHypercovering J K) (p : ℕ)
    (x : ToType (((cechCohomologyOverBifunctor.{v} X p).obj (op K)).obj P)) :
    ∃ (L : SimplicialObject (FormalCoproduct.{v} (Over X))), IsHypercovering J L ∧
      ∃ f : L ⟶ K, (ConcreteCategory.hom
        ((((cechCohomologyOverBifunctor.{v} X p).map f.op).app P))) x = 0 := by
  classical
  set Q : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{v} := (Over.forget X).op ⋙ P
  set D : CochainComplex AddCommGrpCat.{v} ℕ := (cochainComplexFunctor K).obj Q
  set Kp : FormalCoproduct.{v} (Over X) := K.obj (op ⦋p⦌)
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective (D.homologyπ p)).1 inferInstance x
  set ξ : ToType (((evalOp.{v} (Over X) AddCommGrpCat.{v}).obj Q).obj (op Kp)) :=
    (ConcreteCategory.hom (D.iCycles p)) z with hξ
  choose R hR hR0 using fun i : Kp.I =>
    hP (Kp.obj i).left ((ConcreteCategory.hom (evalOpπ Q Kp i)) ξ)
  obtain ⟨Z, u, hu, hmem⟩ := exists_isCoveringOver_of_presieves Kp R hR
  obtain ⟨L, hL, f, g, hfg⟩ :=
    exists_hypercovering_map_factoring_through_covering J K hK p u hu
  refine ⟨L, hL, f, ?_⟩
  set φ : D ⟶ (cochainComplexFunctor L).obj Q :=
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).map
      (Functor.whiskerRight (NatTrans.rightOp f)
        ((evalOp.{v} (Over X) AddCommGrpCat.{v}).obj Q))
  have hZero : (ConcreteCategory.hom
      (((evalOp.{v} (Over X) AddCommGrpCat.{v}).obj Q).map u.op)) ξ = 0 := by
    refine evalOp_ext Q Z (fun i => ?_)
    rw [← ConcreteCategory.comp_apply, map_comp_evalOpπ, ConcreteCategory.comp_apply]
    exact (hR0 (u.f i) (u.φ i).left (hmem i)).trans (map_zero _).symm
  have hξZero : (ConcreteCategory.hom (φ.f p)) ξ = 0 := by
    have hφp : ((evalOp.{v} (Over X) AddCommGrpCat.{v}).obj Q).map u.op ≫
        ((evalOp.{v} (Over X) AddCommGrpCat.{v}).obj Q).map g.op = φ.f p := by
      rw [← Functor.map_comp, ← op_comp, hfg]
      rfl
    have h1 := ConcreteCategory.congr_hom hφp ξ
    rw [ConcreteCategory.comp_apply, hZero, map_zero] at h1
    exact h1.symm
  have hcyc : (ConcreteCategory.hom (HomologicalComplex.cyclesMap φ p)) z = 0 := by
    refine (AddCommGrpCat.mono_iff_injective
      (((cochainComplexFunctor L).obj Q).iCycles p)).1 inferInstance ?_
    rw [map_zero, ← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, ← hξ, hξZero]
  rw [cechCohomologyOverBifunctor_map_app, ← hz]
  have h3 := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ p) z
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hcyc, map_zero] at h3

/-- `CategoryTheory.Sheaf.hasExt_of_smallSite` as a local instance. -/
local instance hasExtSmallSiteDegeneration (J : GrothendieckTopology C) :
    HasExt.{v} (Sheaf J AddCommGrpCat.{v}) :=
  Sheaf.hasExt_of_smallSite J

/-- [Stacks, Tag 01FW] as local vanishing of the cohomology presheaf: for `q > 0` the degree-`q`
cohomology presheaf of an abelian sheaf on a small site is locally zero. -/
lemma isLocallyZero_cohomologyPresheaf (J : Pretopology C)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (q : ℕ) (hq : 0 < q) :
    IsLocallyZero J ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck q).obj F) := by
  intro U ξ
  obtain ⟨S, hS⟩ := Stacks.Cohomology.Locality.cohomologyPresheaf_locally_zero F q hq U ξ
  obtain ⟨R, hRmem, hRle⟩ := (Pretopology.mem_toGrothendieck J U S.1).1 S.2
  exact ⟨R, hRmem, fun {Y} g hg => hS ⟨Y, g, hRle _ _ hg⟩⟩

/-! ### The colimit over the hypercoverings -/

namespace Functorial

variable (X) (J : Pretopology C)

/-- The diagram `K ↦ Ȟ^p(K, P)` on the hypercoverings of `X`, for a presheaf of abelian
groups `P` of coefficients: the Čech cohomology bifunctor restricted along the inclusion of the
full subcategory of hypercoverings and evaluated at `P`. -/
abbrev cechHypercoveringDiagram (p : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (HypercoveringCat X J)ᵒᵖ ⥤ AddCommGrpCat.{v} :=
  (ObjectProperty.ι (fun K : SimplicialObject (FormalCoproduct.{v} (Over X)) =>
      IsHypercovering J K)).op ⋙
    cechCohomologyOverBifunctor.{v} X p ⋙ (evaluation _ _).obj P

/-- The value of the diagram is `Ȟ^p(K, P)`, on the nose. -/
lemma cechHypercoveringDiagram_obj (p : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (K : HypercoveringCat X J) :
    (cechHypercoveringDiagram X J p P).obj (op K) =
      ((cechCohomologyOverBifunctor.{v} X p).obj (op K.obj)).obj P :=
  rfl

/-- On a morphism of hypercoverings the diagram is the canonical pullback map on Čech
cohomology. -/
lemma cechHypercoveringDiagram_map (p : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    {K L : HypercoveringCat X J} (f : L ⟶ K) :
    (cechHypercoveringDiagram X J p P).map f.op =
      ((cechCohomologyOverBifunctor.{v} X p).map f.hom.op).app P :=
  rfl

/-- The diagram with coefficients in the degree-`q` cohomology presheaf is the bottom-row
coefficient of the second page of clause (3) of [Stacks, Tag 01GY], on objects: at a
hypercovering `K` and a sheaf `𝓕` it is the group `E₂^{p,q} = Ȟ^p(K, H^q(𝓕))`. -/
lemma cechHypercoveringDiagram_obj_eq_pageTwo (p q : ℕ) (K : HypercoveringCat X J)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) :
    (cechHypercoveringDiagram X J p
        ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck q).obj F)).obj (op K) =
      (pageTwoHypercovering.{v} X J p q).obj (op K, F) :=
  rfl

/-- The cocone on the diagram of Čech cohomology groups with the zero object as vertex. -/
def zeroCocone (p : ℕ) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    Cocone (cechHypercoveringDiagram X J p P) :=
  Cocone.mk 0 { app := fun _ => 0, naturality := fun _ _ _ => by simp }

/-- Every leg of every cocone on the diagram of Čech cohomology groups with locally zero
coefficients vanishes. -/
theorem cocone_ι_app_eq_zero_of_isLocallyZero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (hP : IsLocallyZero J P) (p : ℕ)
    (s : Cocone (cechHypercoveringDiagram X J p P)) (K : (HypercoveringCat X J)ᵒᵖ) :
    s.ι.app K = 0 := by
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  obtain ⟨L, hL, f, hf⟩ := exists_hypercovering_map_cechCohomology_eq_zero hP
    K.unop.obj K.unop.property p x
  have hw := s.w (Quiver.Hom.op
    (ObjectProperty.homMk f : (⟨L, hL⟩ : HypercoveringCat X J) ⟶ K.unop))
  rw [← ConcreteCategory.congr_hom hw x, ConcreteCategory.comp_apply,
    cechHypercoveringDiagram_map,
    show (ObjectProperty.homMk f : (⟨L, hL⟩ : HypercoveringCat X J) ⟶ K.unop).hom = f from rfl,
    hf, map_zero]
  simp

/-- The colimit over the hypercoverings of `X` of `Ȟ^p(K, P)` is zero for locally zero
coefficients `P`: the cocone with the zero object as vertex is a colimit cocone, every leg of
every cocone being zero. -/
def isColimit_zeroCocone [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (hP : IsLocallyZero J P) (p : ℕ) :
    IsColimit (zeroCocone X J p P) where
  desc _ := 0
  fac s K := zero_comp.trans (cocone_ι_app_eq_zero_of_isLocallyZero X J hP p s K).symm
  uniq _ m _ := (isZero_zero AddCommGrpCat.{v}).eq_of_src m 0

/-- `colim_K Ȟ^p(K, H^q(𝓕)) = 0` for `q > 0`, the colimit being over all hypercoverings of `X`:
the cocone with the zero object as vertex is a colimit cocone. -/
def isColimit_zeroCocone_cohomologyPresheaf
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{v}) (p q : ℕ) (hq : 0 < q) :
    IsColimit (zeroCocone X J p
      ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck q).obj F)) :=
  isColimit_zeroCocone X J (isLocallyZero_cohomologyPresheaf J F q hq) p

end Functorial

end Stacks.CategoryTheory.Hypercovering

end
