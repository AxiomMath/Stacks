module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Point.Presheaf
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksCore.Algebra.Homology.ShortComplex.Products
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Point.Topos
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianPresheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a category by the cochain replacement

Let `C` be a small category, carrying the chaotic topology. Stacks 08RZ computes the functors
`Hⁿ(C, -)` on abelian presheaves by the *cochain replacement* `K^•(F)`: the cosimplicial abelian
group whose group in degree `n` is `∏_{U₀ → ⋯ → Uₙ} F(U₀)`, the product over strings of `n`
composable arrows of `C`, with coface zero given by restriction along the first arrow and the
other cofaces by reindexing the string. Its alternating-coface complex is `K^•(F)`.

The argument has four parts. The replacement is exact degreewise, since a product of
exact sequences of abelian groups is exact, so its homology is a cohomological δ-functor. Its
degree-zero cohomology is the limit of the presheaf, which on the chaotic site is global
sections. For `F = p_{U,*}A` the pushforward of an abelian group along the point of the chaotic
site at `U`, the degree-`n` term of the replacement is the group of maps from the `n`-simplices
of the nerve of `U/C` to `A`, compatibly with every coface; that nerve is contractible, so those
`F` are acyclic, and every abelian presheaf embeds in a product of them. A δ-functor which is
effaceable by such objects is universal, hence agrees with the right-derived functors of global
sections.

## Main definitions

* `Stacks.CategoryCohomology.IsCochainReplacement`: the specification of the replacement — the
  identification of its terms with products of values of `F`, compatibly with every coface and
  with morphisms of presheaves.
* `Stacks.CategoryCohomology.cochainReplacement`: the cosimplicial replacement functor,
  together with a proof that it meets that specification, and
  `cochainReplacementComplex`: its alternating-coface cochain complex.
* `Stacks.CategoryCohomology.cochainReplacementDeltaFunctor`: its homology as a cohomological
  δ-functor.

## Main results

* `Stacks.CategoryCohomology.cochainReplacementComplex_preservesFiniteLimits` and
  `cochainReplacementComplex_preservesFiniteColimits`: degreewise exactness.
* `Stacks.CategoryCohomology.cochainReplacementZeroHomologyIsoLimit`: degree-zero cohomology is
  naturally the limit of the presheaf.
* `Stacks.CategoryCohomology.pointSimplicialReplacement_contractible` and
  `cochainReplacementPointIsoNerve`: the simplicial set of strings ending in an arrow to `U` is
  the nerve of `Under U` and is homotopy equivalent to a point; the point-pushforward terms of
  the replacement are maps out of it, compatibly with every coface.
* `Stacks.CategoryCohomology.cochainReplacementPointAcyclic` and
  `cochainReplacementPointProductAcyclic`: those presheaves, and products of them, are acyclic
  in positive degrees.
* `Stacks.CategoryCohomology.presheafEmbedsInPointProduct`: every abelian presheaf embeds in
  such a product.
* `Stacks.CategoryCohomology.cochainReplacementHomologyIsoSiteCohomology`: the cohomology of the
  replacement is the right-derived global sections of the chaotic site, in every degree.

## Implementation notes

The chaotic topology is the bottom Grothendieck topology; `CategoryTheory.sheafBotEquivalence`
identifies abelian sheaves for it with abelian-group-valued presheaves, and the comparison with
the site-cohomology functor `Stacks.Cohomology.CompositeRightDerived.siteCohomology` is made
after that equivalence. The value universe is `max u v`, large enough for products indexed by
strings in `C`; the degree-zero limit comparison stays polymorphic, while the comparison with the
site-cohomology functor specializes to its universe.

**Transparency.** The reindexing maps of the replacement are built from
`SimplexCategory.toCat`, whose objects have to be read as `Fin (n + 1)` with
`Preorder.smallCategory` — true definitionally but not at the transparency a rewrite motive is
built at. Rather than relax that globally, the definitions of this file are marked
`@[implicit_reducible]`, `CategoryTheory.SimplicialObject.augmentOfIsTerminal` is made locally
so, and the remaining computations are done in term mode: each step is a `have` with an
explicit type, chained with `Eq.trans` and `congrArg`. Where a rewrite is genuinely wanted, the
equation it needs is stated as its own named lemma — `comp_map_homOfLE`,
`under_eqToHom_right`, `under_conj_eqToHom_of_heq_right`, `underChain_recover_obj`,
`pointBot_fiber_map_shrinkYonedaObjObjEquiv_symm`, `comp_sum_zsmul_eq_sum_zsmul_comp` and
`piComparison_comp_pi_map_eq` — and the rewrite uses that. The last two are stated for a
general preadditive, respectively product-preserving, situation.

`comp_map_homOfLE` and `piComparison_comp_pi_map_eq` cannot be `private`: they are used inside
the bodies of `@[expose]`d definitions, which the module system requires to reference only
public declarations.

## References

* [Stacks Project, Tag 08RZ](https://stacks.math.columbia.edu/tag/08RZ)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryCohomology

attribute [local implicit_reducible]
  CategoryTheory.SimplicialObject.augmentOfIsTerminal

universe u v

universe uA vA

/-- The natural identification of the replacement's terms with products of values
respects every coface. In particular the alternating differential has the
restriction term in coface zero. -/
@[implicit_reducible]
def IsCochainReplacement
    (C : Type u) [SmallCategory C]
    (K : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ CosimplicialObject AddCommGrpCat.{max u v}) : Prop :=
  ∃ e : ∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ),
      (K.obj F).obj (.mk n) ≅
        AddCommGrpCat.of (∀ x : ComposableArrows C n, F.obj (Opposite.op x.left)),
      (∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) (x : ComposableArrows C (n + 1))
          (s : (K.obj F).obj (.mk n)),
        ((e F (n + 1)).hom ((K.obj F).δ 0 s)) x =
          (F.map (x.map' 0 1).op).hom (((e F n).hom s) x.δ₀)) ∧
      ((∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ)
          (i : Fin (n + 2)) (hi : i ≠ 0)
          (x : ComposableArrows C (n + 1))
          (s : (K.obj F).obj (.mk n)),
        ∃ h : ((nerve C).δ i x).left = x.left,
          ((e F (n + 1)).hom ((K.obj F).δ i s)) x =
            h ▸ (((e F n).hom s) ((nerve C).δ i x))) ∧
      (∀ (F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (f : F ⟶ G)
          (n : ℕ) (x : ComposableArrows C n)
          (s : (K.obj F).obj (.mk n)),
        ((e G n).hom (((K.map f).app (.mk n)) s)) x =
          (f.app (Opposite.op x.left)).hom (((e F n).hom s) x)))

/-- The map of the cochain replacement along a morphism `f : a ⟶ b` of `SimplexCategory`: its
value at a string `x` of `b.len` composable arrows is the value of `s` at the string
`(nerve C).map f.op x`, restricted along the arrow `x 0 ⟶ x (f 0)`. -/
@[implicit_reducible]
def replacementMap {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) {a b : SimplexCategory} (f : a ⟶ b) :
    AddCommGrpCat.of (∀ x : ComposableArrows C a.len, F.obj (Opposite.op x.left)) ⟶
      AddCommGrpCat.of (∀ x : ComposableArrows C b.len, F.obj (Opposite.op x.left)) :=
  AddCommGrpCat.ofHom
    { toFun := fun s x ↦ F.map (x.map (homOfLE (Fin.zero_le (f.toOrderHom 0)))).op
        (s ((nerve C).map f.op x))
      map_zero' := by funext x; exact map_zero _
      map_add' := by intro s t; funext x; exact map_add _ _ _ }

/-- Functoriality of a chain of composable arrows, phrased for the canonical arrows
`homOfLE` of the indexing linear order. -/
lemma comp_map_homOfLE {C : Type u} [SmallCategory C] {n : ℕ}
    (x : ComposableArrows C n) {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    x.map (homOfLE (hij.trans hjk)) = x.map (homOfLE hij) ≫ x.map (homOfLE hjk) := by
  rw [← x.map_comp]
  rfl

/-- The cosimplicial abelian group of the cochain replacement of `F`: in degree `[n]` it is the
product of the groups `F(x 0)` over the strings `x` of `n` composable arrows of `C`, with the
maps `replacementMap F`. -/
@[implicit_reducible]
def replacementObj {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) : CosimplicialObject AddCommGrpCat.{max u v} where
  obj a := AddCommGrpCat.of (∀ x : ComposableArrows C a.len, F.obj (Opposite.op x.left))
  map f := replacementMap F f
  map_id a := by
    apply ConcreteCategory.hom_ext; intro s; funext x
    change F.map (x.map (𝟙 (0 : Fin (a.len + 1)))).op (s x) = s x
    rw [x.map_id, op_id, F.map_id]
    rfl
  map_comp {a b c} f g := by
    apply ConcreteCategory.hom_ext; intro s; funext x
    change F.map (x.map (homOfLE (Fin.zero_le ((f ≫ g).toOrderHom 0)))).op _ =
      F.map (x.map (homOfLE (Fin.zero_le (g.toOrderHom 0)))).op
        (F.map (((nerve C).map g.op x).map
          (homOfLE (Fin.zero_le (f.toOrderHom 0)))).op _)
    have h : x.map (homOfLE (Fin.zero_le ((f ≫ g).toOrderHom 0))) =
        x.map (homOfLE (Fin.zero_le (g.toOrderHom 0))) ≫
          ((nerve C).map g.op x).map (homOfLE (Fin.zero_le (f.toOrderHom 0))) :=
      comp_map_homOfLE x (Fin.zero_le (g.toOrderHom 0))
        (g.toOrderHom.monotone (Fin.zero_le (f.toOrderHom 0)))
    exact (congrArg
        (fun m ↦ (F.map (Quiver.Hom.op m)) (s ((nerve C).map (f ≫ g).op x))) h).trans
      (ConcreteCategory.congr_hom
        (F.map_comp
          (((nerve C).map g.op x).map (homOfLE (Fin.zero_le (f.toOrderHom 0)))).op
          (x.map (homOfLE (Fin.zero_le (g.toOrderHom 0)))).op)
        (s ((nerve C).map (f ≫ g).op x)))

/-- The cochain replacement `F ↦ replacementObj F` as a functor from abelian presheaves on `C` to
cosimplicial abelian groups; a morphism of presheaves acts componentwise. -/
@[implicit_reducible]
def replacementFunctor (C : Type u) [SmallCategory C] :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ CosimplicialObject AddCommGrpCat.{max u v} where
  obj F := replacementObj F
  map {F G} f :=
    { app := fun a ↦ AddCommGrpCat.ofHom
        { toFun := fun s x ↦ f.app (Opposite.op x.left) (s x)
          map_zero' := funext fun _ ↦ map_zero _
          map_add' := fun _ _ ↦ funext fun _ ↦ map_add _ _ _ }
      naturality := by
        intro a b g
        apply ConcreteCategory.hom_ext
        intro s
        funext x
        exact ConcreteCategory.congr_hom (f.naturality
          (x.map (homOfLE (Fin.zero_le (g.toOrderHom 0)))).op) _ }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functorial cosimplicial cochain replacement of an abelian presheaf. -/
@[implicit_reducible, stacks 08RZ "the cochain replacement"]
noncomputable def cochainReplacement
    (C : Type u) [SmallCategory C] :
    {K : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ CosimplicialObject AddCommGrpCat.{max u v} //
      IsCochainReplacement C K} := by
  refine ⟨replacementFunctor C, fun F n ↦ Iso.refl _, ?_, ?_, ?_⟩
  · intro F n x s
    rfl
  · intro F n i hi x s
    have h : i.succAbove (0 : Fin (n + 1)) = 0 := Fin.succAbove_ne_zero_zero hi
    have hr (j : Fin (n + 2)) (hj : j = 0)
        (t : F.obj (Opposite.op (x.obj j))) :
        F.map (x.map (homOfLE (Fin.zero_le j))).op t =
          (congrArg x.obj hj) ▸ t := by
      subst j
      change F.map (x.map (𝟙 (0 : Fin (n + 2)))).op t = t
      rw [x.map_id, op_id, F.map_id]
      rfl
    exact ⟨congrArg x.obj h, hr _ h _⟩
  · intro F G f n x s
    rfl

/-- The alternating-coface cochain complex functor of the replacement. -/
noncomputable abbrev cochainReplacementComplex
    (C : Type u) [SmallCategory C] :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ :=
  (cochainReplacement C).1 ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

/-- The functor sending an abelian presheaf `F` to the family `x ↦ F(x 0)` indexed by the strings
`x` of `n` composable arrows of `C`, as a functor on the discrete category. -/
@[implicit_reducible]
def replacementFamily (C : Type u) [SmallCategory C] (n : ℕ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤
      (Discrete (ComposableArrows C n) ⥤ AddCommGrpCat.{max u v}) where
  obj F := Discrete.functor fun x ↦ F.obj (Opposite.op x.left)
  map f := Discrete.natTrans fun x ↦ f.app (Opposite.op x.as.left)

/-- The degree-`n` term of the cochain replacement is naturally the limit of
`replacementFamily C n`, that is, the product of the groups `F(x 0)`. -/
@[implicit_reducible]
def replacementDegreeIso (C : Type u) [SmallCategory C] (n : ℕ) :
    replacementFunctor.{u, v} C ⋙ (evaluation _ _).obj (.mk n) ≅
      replacementFamily.{u, v} C n ⋙ lim := by
  refine NatIso.ofComponents (fun F ↦
    (AddCommGrpCat.HasLimit.productLimitCone
      (fun x : ComposableArrows C n ↦ F.obj (Opposite.op x.left))).isLimit.conePointUniqueUpToIso
        (limit.isLimit _)) ?_
  intro F G f
  apply limit.hom_ext
  intro x
  have hG : ((AddCommGrpCat.HasLimit.productLimitCone
        fun y : ComposableArrows C n ↦ G.obj (Opposite.op y.left)).isLimit.conePointUniqueUpToIso
          (limit.isLimit (Discrete.functor
            fun y : ComposableArrows C n ↦ G.obj (Opposite.op y.left)))).hom ≫
        limit.π ((replacementFamily.{u, v} C n).obj G) x =
      (AddCommGrpCat.HasLimit.productLimitCone
        fun y : ComposableArrows C n ↦ G.obj (Opposite.op y.left)).cone.π.app x :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ x
  have hF : ((AddCommGrpCat.HasLimit.productLimitCone
        fun y : ComposableArrows C n ↦ F.obj (Opposite.op y.left)).isLimit.conePointUniqueUpToIso
          (limit.isLimit (Discrete.functor
            fun y : ComposableArrows C n ↦ F.obj (Opposite.op y.left)))).hom ≫
        limit.π ((replacementFamily.{u, v} C n).obj F) x =
      (AddCommGrpCat.HasLimit.productLimitCone
        fun y : ComposableArrows C n ↦ F.obj (Opposite.op y.left)).cone.π.app x :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ x
  have hp : (replacementFamily.{u, v} C n ⋙ lim).map f ≫ limit.π ((replacementFamily.{u, v} C n).obj G) x =
      limit.π ((replacementFamily.{u, v} C n).obj F) x ≫ ((replacementFamily.{u, v} C n).map f).app x :=
    limMap_π _ x
  rw [Category.assoc, Category.assoc]
  refine (congrArg (fun t ↦ _ ≫ t) hG).trans (Eq.trans ?_
    ((congrArg (fun t ↦ _ ≫ t) hp).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t ↦ t ≫ ((replacementFamily.{u, v} C n).map f).app x) hF))).symm)
  rfl

/-- Each degree of the cochain replacement preserves limits of shape `J`, when abelian groups
have them. -/
lemma replacementDegree_preservesLimitsOfShape
    (C : Type u) [SmallCategory C] (n : ℕ) (J : Type uA) [Category.{vA} J]
    [HasLimitsOfShape J AddCommGrpCat.{max u v}] :
    PreservesLimitsOfShape J
      (replacementFunctor.{u, v} C ⋙ (evaluation _ _).obj (.mk n)) := by
  have : PreservesLimitsOfShape J (replacementFamily.{u, v} C n) := by
    apply preservesLimitsOfShape_of_evaluation
    intro x
    change PreservesLimitsOfShape J
      ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (Opposite.op x.as.left))
    infer_instance
  exact preservesLimitsOfShape_of_natIso (replacementDegreeIso C n).symm

/-- Each degree of the cochain replacement preserves finite colimits. -/
lemma replacementDegree_preservesFiniteColimits
    (C : Type u) [SmallCategory C] (n : ℕ) :
    PreservesFiniteColimits
      (replacementFunctor.{u, v} C ⋙ (evaluation _ _).obj (.mk n)) := by
  have : PreservesFiniteColimits (replacementFamily.{u, v} C n) := by
    apply preservesFiniteColimits_of_evaluation
    intro x
    change PreservesFiniteColimits
      ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (Opposite.op x.as.left))
    infer_instance
  have : AB4StarOfSize.{u} AddCommGrpCat.{max u v} := AB4StarOfSize_shrink _
  exact preservesFiniteColimits_of_natIso (replacementDegreeIso C n).symm

/-- The cochain replacement preserves finite limits, degree by degree. -/
@[stacks 08RZ "left exactness of the replacement"]
theorem cochainReplacementComplex_preservesFiniteLimits
    (C : Type u) [SmallCategory C] :
    PreservesFiniteLimits (cochainReplacementComplex C) :=
  ⟨fun J _ _ ↦ HomologicalComplex.preservesLimitsOfShape_of_eval _ fun n ↦
    replacementDegree_preservesLimitsOfShape C n J⟩

/-- The cochain replacement preserves finite colimits, degree by degree. -/
@[stacks 08RZ "right exactness of the replacement"]
theorem cochainReplacementComplex_preservesFiniteColimits
    (C : Type u) [SmallCategory C] :
    PreservesFiniteColimits (cochainReplacementComplex C) :=
  ⟨fun J _ _ ↦ HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦
    (replacementDegree_preservesFiniteColimits C n).preservesFiniteColimits J⟩

/-- The cohomological δ-functor of an exact functor `G` to cochain complexes: its `n`-th functor
is `G` followed by `n`-th homology, and its connecting morphisms are those of the homology
sequence. -/
@[implicit_reducible]
noncomputable def deltaFunctorOfExactCochainComplex
    {A : Type*} [Category A] [Abelian A]
    {B : Type*} [Category B] [Abelian B]
    (G : A ⥤ CochainComplex B ℕ)
    (hG : exactFunctor A (CochainComplex B ℕ) G) :
    { F : DeltaFunctor A B //
      ∀ n : ℕ, F.functor n = G ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n } := by
  let hG' := (exactFunctor_iff G).mp hG
  have : PreservesFiniteLimits G := hG'.1
  have : PreservesFiniteColimits G := hG'.2
  letI : G.Additive := exactFunctor_le_additiveFunctor _ _ G hG
  let F : DeltaFunctor A B :=
    { functor := fun n => G ⋙ HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n
      additive := fun n => inferInstance
      δ := fun {S} hS n =>
        (hS.map_of_exact G).δ n (n + 1)
          (ComplexShape.up_mk n (n + 1) (by omega))
      map_g_δ := by
        intro S hS n
        exact (hS.map_of_exact G).comp_δ n (n + 1)
          (ComplexShape.up_mk n (n + 1) (by omega))
      δ_map_f := by
        intro S hS n
        exact (hS.map_of_exact G).δ_comp n (n + 1)
          (ComplexShape.up_mk n (n + 1) (by omega))
      mono_map_f := by
        intro S hS
        let hS' : (S.map G).ShortExact := hS.map_of_exact G
        have : Mono ((S.map G).f) := hS'.mono_f
        apply HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (S.map G).f 0
        intro i; simp only [ComplexShape.up_Rel]; omega
      exact_map := by intro S hS n; exact (hS.map_of_exact G).homology_exact₂ n
      exact_δ₁ := by
        intro S hS n
        exact (hS.map_of_exact G).homology_exact₃ n (n + 1)
          (ComplexShape.up_mk n (n + 1) (by omega))
      exact_δ₂ := by
        intro S hS n
        exact (hS.map_of_exact G).homology_exact₁ n (n + 1)
          (ComplexShape.up_mk n (n + 1) (by omega))
      δ_naturality := by
        intro S T hS hT φ n
        let hS' : (S.map G).ShortExact := hS.map_of_exact G
        let hT' : (T.map G).ShortExact := hT.map_of_exact G
        let ψ : S.map G ⟶ T.map G :=
          { τ₁ := G.map φ.τ₁
            τ₂ := G.map φ.τ₂
            τ₃ := G.map φ.τ₃
            comm₁₂ := by simpa using congrArg G.map φ.comm₁₂
            comm₂₃ := by simpa using congrArg G.map φ.comm₂₃ }
        change HomologicalComplex.homologyMap (G.map φ.τ₃) n ≫ _ =
          _ ≫ HomologicalComplex.homologyMap (G.map φ.τ₁) (n + 1)
        exact (HomologicalComplex.HomologySequence.δ_naturality ψ hS' hT' n (n + 1)
          (ComplexShape.up_mk n (n + 1) (by omega))).symm }
  exact ⟨F, fun _ => rfl⟩

/-- The homology functors of the replacement, with their natural connecting
morphisms, form a cohomological delta functor. -/
@[implicit_reducible, stacks 08RZ "cohomological delta functor"]
noncomputable def cochainReplacementDeltaFunctor
    (C : Type u) [SmallCategory C] :
    {D : DeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) AddCommGrpCat.{max u v} //
      ∀ n, D.functor n = cochainReplacementComplex C ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) n} :=
  deltaFunctorOfExactCochainComplex (cochainReplacementComplex C)
    ((exactFunctor_iff _).mpr ⟨cochainReplacementComplex_preservesFiniteLimits C,
      cochainReplacementComplex_preservesFiniteColimits C⟩)

/-- The differential of the cochain replacement from degree `0` to degree `1`: at a string
`x : x 0 ⟶ x 1` it is the restriction of `s` at `x 1` along `x`, minus `s` at `x 0`. -/
lemma replacement_d_zero {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (s : ((cochainReplacementComplex C).obj F).X 0) (x : ComposableArrows C 1) :
    ((cochainReplacementComplex C).obj F).d 0 1 s x =
      (show F.obj (Opposite.op x.left) from
        F.map (x.map' 0 1).op (s (ComposableArrows.mk₀ x.right))) -
      (show F.obj (Opposite.op x.left) from s (ComposableArrows.mk₀ x.left)) := by
  change (AlgebraicTopology.AlternatingCofaceMapComplex.objD (replacementObj F) 0) s x = _
  have hd : AlgebraicTopology.AlternatingCofaceMapComplex.objD (replacementObj F) 0 =
      (replacementObj F).δ 0 - (replacementObj F).δ 1 := by
    simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg]
  rw [hd]
  change (show F.obj (Opposite.op x.left) from F.map (x.map' 0 1).op (s x.δ₀)) -
    (show F.obj (Opposite.op x.left) from
      F.map (x.map (𝟙 (0 : Fin 2))).op (s ((nerve C).δ 1 x))) = _
  rw [x.map_id, op_id, F.map_id]
  have h₀ : x.δ₀ = ComposableArrows.mk₀ x.right := ComposableArrows.ext₀ rfl
  have h₁ : (nerve C).δ (1 : Fin 2) x = ComposableArrows.mk₀ x.left :=
    ComposableArrows.ext₀ rfl
  have hs (y z : ComposableArrows C 0) (h : y = z) : HEq (s y) (s z) := by
    subst z
    rfl
  have hs₀ : (show F.obj (Opposite.op x.right) from s x.δ₀) =
      (show F.obj (Opposite.op x.right) from s (ComposableArrows.mk₀ x.right)) :=
    eq_of_heq (hs x.δ₀ (ComposableArrows.mk₀ x.right) h₀)
  have hs₁ : (show F.obj (Opposite.op x.left) from s ((nerve C).δ 1 x)) =
      (show F.obj (Opposite.op x.left) from s (ComposableArrows.mk₀ x.left)) :=
    eq_of_heq (hs ((nerve C).δ 1 x) (ComposableArrows.mk₀ x.left) h₁)
  exact congrArg₂ (· - ·) (congrArg
    (fun t : F.obj (Opposite.op x.right) ↦ F.map (x.map' 0 1).op t) hs₀) hs₁

/-- The projection from degree zero of the cochain replacement of `F` onto `F(U)`, the component
at the string of length zero at `U`. -/
@[implicit_reducible]
def replacementEvalZero {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (U : C) :
    ((cochainReplacementComplex C).obj F).X 0 ⟶ F.obj (Opposite.op U) :=
  AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ (ComposableArrows.mk₀ U))

/-- On the degree-zero cycles of the cochain replacement of `F`, the projections onto `F(V)` and
`F(U)` are compatible with the restriction along `f : U ⟶ V`. -/
lemma replacement_cycle_naturality {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) {U V : C} (f : U ⟶ V) :
    ((cochainReplacementComplex C).obj F).iCycles 0 ≫ replacementEvalZero F V ≫ F.map f.op =
      ((cochainReplacementComplex C).obj F).iCycles 0 ≫ replacementEvalZero F U := by
  apply ConcreteCategory.hom_ext
  intro s
  have h := ConcreteCategory.congr_hom
    (((cochainReplacementComplex C).obj F).iCycles_d 0 1) s
  have h' := congrFun h (ComposableArrows.mk₁ f)
  change (((cochainReplacementComplex C).obj F).d 0 1
    (((cochainReplacementComplex C).obj F).iCycles 0 s)) (ComposableArrows.mk₁ f) = 0 at h'
  rw [replacement_d_zero, sub_eq_zero] at h'
  exact h'

/-- The cone over `F` whose vertex is the degree-zero cycles of its cochain replacement and whose
legs are the projections `replacementEvalZero`. -/
@[implicit_reducible]
def replacementCyclesCone {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) : Cone F where
  pt := ((cochainReplacementComplex C).obj F).cycles 0
  π :=
    { app := fun U ↦ ((cochainReplacementComplex C).obj F).iCycles 0 ≫
        replacementEvalZero F U.unop
      naturality := fun _ _ f ↦
        (Category.id_comp _).trans
          ((replacement_cycle_naturality F f.unop).symm.trans
            (Category.assoc _ _ _).symm) }

/-- The map from the vertex of a cone `s` over `F` to degree zero of the cochain replacement of
`F` whose component at the string of length zero at `U` is the leg of `s` at `U`. -/
@[implicit_reducible]
def replacementConeMap {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (s : Cone F) :
    s.pt ⟶ ((cochainReplacementComplex C).obj F).X 0 :=
  AddCommGrpCat.ofHom
    { toFun := fun a x ↦ s.π.app (Opposite.op x.left) a
      map_zero' := funext fun _ ↦ map_zero _
      map_add' := fun _ _ ↦ funext fun _ ↦ map_add _ _ _ }

/-- The map `replacementConeMap F s` composed with the differential out of degree zero is zero. -/
lemma replacementConeMap_d {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (s : Cone F) :
    replacementConeMap F s ≫ ((cochainReplacementComplex C).obj F).d 0 1 = 0 := by
  refine ConcreteCategory.hom_ext _ _ fun a ↦ funext fun x ↦ ?_
  change ((cochainReplacementComplex C).obj F).d 0 1 (replacementConeMap F s a) x = 0
  rw [replacement_d_zero, sub_eq_zero]
  exact ConcreteCategory.congr_hom (s.w (x.map' 0 1).op) a

/-- The degree-zero cycles of the cochain replacement of `F`, with the projections onto the
`F(U)`, are a limit cone over `F`. -/
@[implicit_reducible]
def replacementCyclesConeIsLimit {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) : IsLimit (replacementCyclesCone F) where
  lift s := ((cochainReplacementComplex C).obj F).liftCycles
    (replacementConeMap F s) 1 (by simp) (replacementConeMap_d F s)
  fac s U := by
    dsimp [replacementCyclesCone]
    rw [← Category.assoc, HomologicalComplex.liftCycles_i]
    rfl
  uniq s m hm := by
    apply (cancel_mono (((cochainReplacementComplex C).obj F).iCycles 0)).mp
    rw [HomologicalComplex.liftCycles_i]
    apply ConcreteCategory.hom_ext
    intro a
    funext x
    have hx : x = ComposableArrows.mk₀ x.left := ComposableArrows.ext₀ rfl
    have h := ConcreteCategory.congr_hom (hm (Opposite.op x.left)) a
    change (((cochainReplacementComplex C).obj F).iCycles 0 (m a))
      (ComposableArrows.mk₀ x.left) = _ at h
    change (((cochainReplacementComplex C).obj F).iCycles 0 (m a)) x =
      s.π.app (Opposite.op x.left) a
    rw [hx]
    exact h

/-- The degree-zero cohomology of the cochain replacement of `F` is isomorphic to the limit of
`F`. -/
@[implicit_reducible]
def replacementZeroIsoLimit {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    ((cochainReplacementComplex C).obj F).homology 0 ≅ limit F :=
  ((cochainReplacementComplex C).obj F).isoHomologyπ₀.symm ≪≫
    (replacementCyclesConeIsLimit F).conePointUniqueUpToIso (limit.isLimit F)

/-- The isomorphism `replacementZeroIsoLimit F` followed by the projection onto `F(U)` is the
inverse of `homologyπ 0` followed by the projection of the degree-zero cycles onto `F(U)`. -/
lemma replacementZeroIsoLimit_hom_π {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (U : Cᵒᵖ) :
    (replacementZeroIsoLimit F).hom ≫ limit.π F U =
      inv (((cochainReplacementComplex C).obj F).homologyπ 0) ≫
        ((cochainReplacementComplex C).obj F).iCycles 0 ≫ replacementEvalZero F U.unop := by
  dsimp only [replacementZeroIsoLimit, Iso.trans_hom]
  rw [Category.assoc]
  change _ ≫ ((replacementCyclesConeIsLimit F).conePointUniqueUpToIso
    (limit.isLimit F)).hom ≫ (limit.cone F).π.app U = _
  rw [IsLimit.conePointUniqueUpToIso_hom_comp]
  rfl

/-- The zeroth cohomology of the replacement is naturally the limit of the
presheaf. -/
@[stacks 08RZ "degree-zero cohomology"]
theorem cochainReplacementZeroHomologyIsoLimit
    (C : Type u) [SmallCategory C] :
    Nonempty
      (cochainReplacementComplex C ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) 0 ≅
        (lim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v})) := by
  refine ⟨NatIso.ofComponents (fun F ↦ replacementZeroIsoLimit F) ?_⟩
  intro F G f
  apply limit.hom_ext
  intro U
  change (HomologicalComplex.homologyMap ((cochainReplacementComplex C).map f) 0 ≫
    (replacementZeroIsoLimit G).hom) ≫ limit.π G U =
    ((replacementZeroIsoLimit F).hom ≫ lim.map f) ≫ limit.π G U
  simp only [Category.assoc]
  rw [replacementZeroIsoLimit_hom_π, lim_map, limMap_π]
  conv_rhs => rw [← Category.assoc, replacementZeroIsoLimit_hom_π]
  apply (cancel_epi (((cochainReplacementComplex C).obj F).homologyπ 0)).mp
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, HomologicalComplex.cyclesMap_i]
  rfl

/-- Prepending an arrow `f` to a chain `x` does not change the arrows of `x`: the arrow `a ⟶ b`
of `x.precomp f`, for `a = j.succ` and `b = k.succ`, is heterogeneously equal to the arrow
`j ⟶ k` of `x`. -/
lemma precomp_map_heq {C : Type u} [SmallCategory C] {n : ℕ}
    (x : ComposableArrows C n) {O : C} (f : O ⟶ x.left)
    {a b : Fin (n + 2)} {j k : Fin (n + 1)}
    (ha : a = j.succ) (hb : b = k.succ) (g : a ⟶ b) (g' : j ⟶ k) :
    HEq ((x.precomp f).map g) (x.map g') := by
  subst a; subst b
  rfl

/-- Precomposing a chain with a monotone reindexing that fixes the first index commutes with
prepending the arrow out of an initial object. -/
private lemma precomp_comp_reindex {C : Type u} [SmallCategory C]
    {O : C} (hO : IsInitial O) {n k : ℕ} (x : ComposableArrows C n)
    (φ : Fin (k + 1) ⥤ Fin (n + 1)) (ψ : Fin (k + 2) ⥤ Fin (n + 2))
    (h₀ : ψ.obj 0 = 0) (h : ∀ j, ψ.obj j.succ = (φ.obj j).succ) :
    ψ ⋙ x.precomp (hO.to x.left) =
      ComposableArrows.precomp (φ ⋙ x : ComposableArrows C k) (hO.to _) := by
  refine ComposableArrows.ext_succ ?_ ?_ ?_
  · change ComposableArrows.Precomp.obj x O (ψ.obj 0) = O
    rw [h₀]
    rfl
  · refine CategoryTheory.Functor.ext (h_obj := fun j ↦ ?_) (h_map := fun j k f ↦ ?_)
    · exact (congrArg (ComposableArrows.Precomp.obj x O) (h j)).trans rfl
    · exact (conj_eqToHom_iff_heq' _ _ _ _).mpr <| precomp_map_heq x (hO.to x.left)
        (h j) (h k) (ψ.map ((Fin.succFunctor _).map f)) (φ.map f)
  · have hO' : IsInitial (ComposableArrows.Precomp.obj x O (ψ.obj 0)) := by
      rw [h₀]
      exact hO
    exact hO'.hom_ext _ _

/-- Prepending the arrow out of an initial object `O` commutes with the faces of the nerve: the
`i.succ`-th face of the prepended chain is the prepended `i`-th face. -/
lemma nerve_prepend_face {C : Type u} [SmallCategory C]
    {O : C} (hO : IsInitial O) {n : ℕ} (x : ComposableArrows C (n + 1))
    (i : Fin (n + 2)) :
    (nerve C).δ i.succ (x.precomp (hO.to x.left)) =
      ((nerve C).δ i x).precomp (hO.to _) :=
  precomp_comp_reindex hO x _ _ (Fin.succ_succAbove_zero i) (Fin.succ_succAbove_succ i)

/-- Prepending the arrow out of an initial object `O` commutes with the degeneracies of the
nerve: the `i.succ`-th degeneracy of the prepended chain is the prepended `i`-th degeneracy. -/
lemma nerve_prepend_degeneracy {C : Type u} [SmallCategory C]
    {O : C} (hO : IsInitial O) {n : ℕ} (x : ComposableArrows C n)
    (i : Fin (n + 1)) :
    (nerve C).σ i.succ (x.precomp (hO.to x.left)) =
      ((nerve C).σ i x).precomp (hO.to _) :=
  precomp_comp_reindex hO x _ _ (by change i.succ.predAbove 0 = 0; simp) (Fin.succ_predAbove_succ i)

/-- For a category with an initial object `O`, prepending the arrow out of `O` is an extra
degeneracy of the nerve, augmented over the point. -/
@[implicit_reducible]
def nerveExtraDegeneracy {C : Type u} [SmallCategory C]
    {O : C} (hO : IsInitial O) :
    ((nerve C).augmentOfIsTerminal (Types.isTerminalPUnit)).ExtraDegeneracy where
  s' := ↾fun _ ↦ ComposableArrows.mk₀ O
  s n := ↾fun x ↦ x.precomp (hO.to x.left)
  s'_comp_ε := by ext x; rfl
  s₀_comp_δ₁ := by ext x; apply ComposableArrows.ext₀; rfl
  s_comp_δ₀ n := by ext x; rfl
  s_comp_δ n i := by ext x; exact nerve_prepend_face hO x i
  s_comp_σ n i := by ext x; exact nerve_prepend_degeneracy hO x i

/-- The simplicial set of chains `U₀ ⟶ ⋯ ⟶ Uₙ` equipped with a map
`U ⟶ U₀` is the nerve of the under-category of `U`, and is simplicially
homotopy equivalent to a point. -/
@[stacks 08RZ "contractibility of the point simplicial replacement"]
theorem pointSimplicialReplacement_contractible
    (C : Type u) [SmallCategory C] (U : C) :
    ∃ f : nerve (Under U) ⟶ ⊤_ SSet.{u},
      SimplicialObject.homotopyEquivalences (Type u) f := by
  let X := (nerve (Under U)).augmentOfIsTerminal Types.isTerminalPUnit
  let ed := nerveExtraDegeneracy (Under.mkIdInitial (X := U))
  let e := (CategoryTheory.Functor.isTerminalConst SimplexCategoryᵒᵖ
    Types.isTerminalPUnit).uniqueUpToIso (terminalIsTerminal (C := SSet.{u}))
  refine ⟨X.hom ≫ e.hom, e.inv ≫ ed.section_, ?_, ?_⟩
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      (Relation.EqvGen.rel _ _ ⟨ed.homotopy⟩)
  · rw [(terminalIsTerminal (C := SSet.{u})).hom_ext
      ((e.inv ≫ ed.section_) ≫ X.hom ≫ e.hom) (𝟙 _)]
    exact Relation.EqvGen.refl _

/-- A chain `x` of composable arrows of `C` together with an arrow `f : U ⟶ x 0`, as a chain of
composable arrows of `Under U`: its object at `i` is `x i` with structure map `f` followed by
`x 0 ⟶ x i`. -/
@[implicit_reducible]
def underChain {C : Type u} [SmallCategory C] {U : C} {n : ℕ}
    (x : ComposableArrows C n) (f : U ⟶ x.left) : ComposableArrows (Under U) n :=
  x.toUnder U (fun i ↦ f ≫ x.map (homOfLE (Fin.zero_le i))) (by
    intro i j g
    rw [Category.assoc, ← x.map_comp]
    rfl)

/-- The underlying chain of `underChain x f` is `x`. -/
lemma underChain_forget {C : Type u} [SmallCategory C] {U : C} {n : ℕ}
    (x : ComposableArrows C n) (f : U ⟶ x.left) :
    underChain x f ⋙ Under.forget U = x := rfl

/-- The structure map of the first object of `underChain x f` is `f`. -/
lemma underChain_left_hom {C : Type u} [SmallCategory C] {U : C} {n : ℕ}
    (x : ComposableArrows C n) (f : U ⟶ x.left) :
    (underChain x f).left.hom = f := by
  change f ≫ x.map (𝟙 _) = f
  rw [x.map_id, Category.comp_id]

/-- The underlying morphism of `C` of an `eqToHom` of `Under U`. -/
private lemma under_eqToHom_right {C : Type u} [SmallCategory C] {U : C}
    {a b : Under U} (h : a = b) :
    Under.Hom.right (eqToHom h) = eqToHom (congrArg Under.right h) := by
  subst h; rfl

/-- Two morphisms of `Under U` are conjugate by `eqToHom`s as soon as their underlying
morphisms of `C` are heterogeneously equal. -/
private lemma under_conj_eqToHom_of_heq_right {C : Type u} [SmallCategory C] {U : C}
    {a b c d : Under U} (φ : a ⟶ b) (ψ : c ⟶ d) (h : a = c) (h' : d = b)
    (H : Under.Hom.right φ ≍ Under.Hom.right ψ) :
    φ = eqToHom h ≫ ψ ≫ eqToHom h' := by
  refine Under.UnderMorphism.ext ?_
  change Under.Hom.right φ = Under.Hom.right (eqToHom h) ≫
    Under.Hom.right ψ ≫ Under.Hom.right (eqToHom h')
  rw [under_eqToHom_right, under_eqToHom_right]
  exact (conj_eqToHom_iff_heq' _ _ _ _).mpr H

private lemma underChain_recover_obj {C : Type u} [SmallCategory C] {U : C} {n : ℕ}
    (x : ComposableArrows (Under U) n) (i : Fin (n + 1)) :
    (underChain (x ⋙ Under.forget U) x.left.hom).obj i = x.obj i :=
  StructuredArrow.obj_ext _ _ rfl
    ((Category.comp_id _).trans (Under.w (x.map (homOfLE (Fin.zero_le i)))))

/-- Every chain of composable arrows of `Under U` is the `underChain` of its underlying chain and
of the structure map of its first object. -/
lemma underChain_recover {C : Type u} [SmallCategory C] {U : C} {n : ℕ}
    (x : ComposableArrows (Under U) n) :
    underChain (x ⋙ Under.forget U) x.left.hom = x :=
  CategoryTheory.Functor.ext (underChain_recover_obj x) fun _ _ _ ↦
    under_conj_eqToHom_of_heq_right _ _ _ _ HEq.rfl

/-- Chains of `n` composable arrows of `Under U` are equivalent to chains `x` of `n` composable
arrows of `C` together with an arrow `U ⟶ x 0`. -/
@[implicit_reducible]
def underChainEquiv {C : Type u} [SmallCategory C] (U : C) (n : ℕ) :
    ComposableArrows (Under U) n ≃ Σ x : ComposableArrows C n, (U ⟶ x.left) where
  toFun x := ⟨x ⋙ Under.forget U, x.left.hom⟩
  invFun x := underChain x.1 x.2
  left_inv := underChain_recover
  right_inv x := by
    rcases x with ⟨x, f⟩
    simp only [underChain_forget, underChain_left_hom]

/-- The categorical product of a family of abelian groups is isomorphic to the group of
dependent functions. -/
@[implicit_reducible]
def productFunctionIso {I : Type u} (A : I → AddCommGrpCat.{max u v}) :
    (∏ᶜ A) ≅ AddCommGrpCat.of (∀ i, A i) :=
  (limit.isLimit _).conePointUniqueUpToIso (AddCommGrpCat.HasLimit.productLimitCone A).isLimit

/-- The components of `productFunctionIso A` are the product projections. -/
lemma productFunctionIso_apply {I : Type u} (A : I → AddCommGrpCat.{max u v})
    (s : (∏ᶜ A : AddCommGrpCat.{max u v})) (i : I) :
    (productFunctionIso A).hom s i = Pi.π A i s := by
  have h := (limit.isLimit _).conePointUniqueUpToIso_hom_comp
    (AddCommGrpCat.HasLimit.productLimitCone A).isLimit (Discrete.mk i)
  exact ConcreteCategory.congr_hom h s

/-- Chains of `n` composable arrows of `Under U` are equivalent to chains `x` of `n` composable
arrows of `C` together with an element of the fiber at `x 0` of the point `pointBot U`. -/
@[implicit_reducible]
def pointChainEquiv {C : Type u} [SmallCategory C] (U : C) (n : ℕ) :
    ComposableArrows (Under U) n ≃
      Σ x : ComposableArrows C n, (GrothendieckTopology.pointBot U).fiber.obj x.left :=
  (underChainEquiv U n).trans (Equiv.sigmaCongrRight fun _ ↦ shrinkYonedaObjObjEquiv.symm)

/-- The degree-`n` term of the cochain replacement of the skyscraper presheaf of `A` at the point
`pointBot U` is isomorphic, as an abelian group, to the group of functions from chains of `n`
composable arrows of `Under U` to `A`. -/
@[implicit_reducible]
def replacementPointEquiv {C : Type u} [SmallCategory C]
    (U : C) (A : AddCommGrpCat.{max u v}) (n : ℕ) :
    (∀ x : ComposableArrows C n,
      ((GrothendieckTopology.pointBot U).skyscraperPresheaf A).obj (Opposite.op x.left)) ≃+
      (ComposableArrows (Under U) n → A) := by
  let e := AddEquiv.piCongrRight (fun x : ComposableArrows C n ↦
    (productFunctionIso
      (fun _ : (GrothendieckTopology.pointBot U).fiber.obj x.left ↦ A)).addCommGroupIsoToAddEquiv)
  let d : (∀ x : ComposableArrows C n,
      (GrothendieckTopology.pointBot U).fiber.obj x.left → A) ≃+
        (ComposableArrows (Under U) n → A) :=
    { toFun := fun s x ↦ s ((pointChainEquiv U n) x).1 ((pointChainEquiv U n) x).2
      invFun := fun s x f ↦ s ((pointChainEquiv U n).symm ⟨x, f⟩)
      left_inv := by
        intro s; funext x f
        exact congrArg (fun t ↦ s t.1 t.2) ((pointChainEquiv U n).apply_symm_apply ⟨x, f⟩)
      right_inv := by intro s; funext x; simp
      map_add' := by intros; rfl }
  exact e.trans d

/-- The value of `replacementPointEquiv U A n s` at a chain `x` of `Under U` is the component of
`s` at the underlying chain of `x`, projected to the factor indexed by the structure map of the
first object of `x`. -/
lemma replacementPointEquiv_apply {C : Type u} [SmallCategory C]
    (U : C) (A : AddCommGrpCat.{max u v}) (n : ℕ)
    (s : ∀ x : ComposableArrows C n,
      ((GrothendieckTopology.pointBot U).skyscraperPresheaf A).obj (Opposite.op x.left))
    (x : ComposableArrows (Under U) n) :
    replacementPointEquiv U A n s x =
      Pi.π (fun _ : (GrothendieckTopology.pointBot U).fiber.obj x.left.right ↦ A)
        (shrinkYonedaObjObjEquiv.symm x.left.hom) (s (x ⋙ Under.forget U)) :=
  productFunctionIso_apply _ _ _

/-- The fiber functor of the point `pointBot U` sends a morphism to precomposition
of the corresponding `shrinkYoneda` section. -/
private lemma pointBot_fiber_map_shrinkYonedaObjObjEquiv_symm {C : Type u} [SmallCategory C]
    (U : C) {X Y : C} (a : U ⟶ X) (g : X ⟶ Y) :
    (GrothendieckTopology.pointBot U).fiber.map g (shrinkYonedaObjObjEquiv.symm a) =
      shrinkYonedaObjObjEquiv.symm (a ≫ g) := by
  change (shrinkYoneda.map g).app (Opposite.op U) (shrinkYonedaObjObjEquiv.symm a) = _
  rw [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm]

/-- The degree-`n` replacement of the point-pushforward of `A` is the group
of maps from the `n`-simplices of the nerve of `Under U` to `A`. These
identifications intertwine every coface with precomposition by the
corresponding simplicial face, hence identify the cochain complexes. -/
@[stacks 08RZ "point-pushforward replacement as maps from the nerve"]
theorem cochainReplacementPointIsoNerve
    (C : Type u) [SmallCategory C] (U : C) (A : AddCommGrpCat.{max u v}) :
    ∃ e : ∀ n : ℕ,
        (((cochainReplacement C).1.obj
          ((sheafBotEquivalence (C := C) AddCommGrpCat.{max u v}).functor.obj
            ((GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A))).obj (.mk n)) ≅
          AddCommGrpCat.of (ComposableArrows (Under U) n → A),
      ∀ (n : ℕ) (i : Fin (n + 2)) (x : ComposableArrows (Under U) (n + 1))
          (s : ((cochainReplacement C).1.obj
            ((sheafBotEquivalence (C := C) AddCommGrpCat.{max u v}).functor.obj
              ((GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A))).obj (.mk n)),
        ((e (n + 1)).hom
          (((cochainReplacement C).1.obj
            ((sheafBotEquivalence (C := C) AddCommGrpCat.{max u v}).functor.obj
              ((GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A))).δ i s)) x =
          ((e n).hom s) ((nerve (Under U)).δ i x) := by
  refine ⟨fun n ↦ (replacementPointEquiv U A n).toAddCommGrpIso, fun n i x s ↦ ?_⟩
  change replacementPointEquiv U A (n + 1) ((replacementObj _).δ i s) x =
    replacementPointEquiv U A n s ((nerve (Under U)).δ i x)
  refine (replacementPointEquiv_apply U A (n + 1) _ x).trans
    (Eq.trans ?_
      (replacementPointEquiv_apply U A n s ((nerve (Under U)).δ i x)).symm)
  let f := (x.map (homOfLE (Fin.zero_le (i.succAbove 0)))).right
  let P := (GrothendieckTopology.pointBot U).fiber
  have h := ConcreteCategory.congr_hom
    (Pi.map'_comp_π (C := AddCommGrpCat.{max u v}) (fun a ↦ P.map f a)
      (fun _ ↦ 𝟙 A) (shrinkYonedaObjObjEquiv.symm x.left.hom))
    (s (((nerve (Under U)).δ i x) ⋙ Under.forget U))
  simp only [Category.comp_id] at h
  have hidx : P.map f (shrinkYonedaObjObjEquiv.symm x.left.hom) =
      shrinkYonedaObjObjEquiv.symm (((nerve (Under U)).δ i x).left.hom) :=
    (pointBot_fiber_map_shrinkYonedaObjObjEquiv_symm U x.left.hom f).trans
      (congrArg shrinkYonedaObjObjEquiv.symm
        (Under.w (x.map (homOfLE (Fin.zero_le (i.succAbove 0))))))
  exact h.trans (congrArg (fun t ↦ (Pi.π (fun _ ↦ A) t)
    (s (((nerve (Under U)).δ i x) ⋙ Under.forget U))) hidx)

/-- The contravariant functor `X ↦ (X → A)` from types to abelian groups, acting on morphisms by
precomposition. -/
@[implicit_reducible]
def functionsFunctor (A : AddCommGrpCat.{max u v}) :
    Type u ⥤ AddCommGrpCat.{max u v}ᵒᵖ where
  obj X := Opposite.op (AddCommGrpCat.of (X → A))
  map f := (AddCommGrpCat.ofHom
    { toFun := fun s x ↦ s (f x)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A square of alternating sums commutes as soon as it commutes term by term. -/
private lemma comp_sum_zsmul_eq_sum_zsmul_comp {D : Type uA} [Category.{vA} D] [Preadditive D]
    {ι : Type*} [Fintype ι] {P P' Q Q' : D} (f : P ⟶ P') (f' : Q ⟶ Q')
    (g : ι → (P' ⟶ Q')) (g' : ι → (P ⟶ Q)) (c : ι → ℤ)
    (h : ∀ k, f ≫ g k = g' k ≫ f') :
    f ≫ (∑ k, c k • g k) = (∑ k, c k • g' k) ≫ f' := by
  rw [Preadditive.comp_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, h k]

/-- Pushforward from a point of the chaotic site is acyclic for the cochain
replacement in every positive degree. -/
@[stacks 08RZ "point-pushforward acyclicity"]
theorem cochainReplacementPointAcyclic
    (C : Type u) [SmallCategory C] (U : C) (A : AddCommGrpCat.{max u v})
    (n : ℕ) (hn : 0 < n) :
    IsZero ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) n).obj
      ((cochainReplacementComplex C).obj
        ((sheafBotEquivalence (C := C) AddCommGrpCat.{max u v}).functor.obj
          ((GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A)))) := by
  let X := (nerve (Under U)).augmentOfIsTerminal Types.isTerminalPUnit
  let ed := (nerveExtraDegeneracy (Under.mkIdInitial (X := U))).map (functionsFunctor A)
  let L := AlgebraicTopology.AlternatingFaceMapComplex.obj
    ((nerve (Under U)) ⋙ functionsFunctor A)
  obtain ⟨e, he⟩ := cochainReplacementPointIsoNerve C U A
  let K := (cochainReplacementComplex C).obj
    ((sheafBotEquivalence (C := C) AddCommGrpCat.{max u v}).functor.obj
      ((GrothendieckTopology.pointBot U).skyscraperSheafFunctor.obj A))
  let eK : K ≅ L.unop := HomologicalComplex.Hom.isoOfComponents e (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    have hL : L.d (i + 1) i = AlgebraicTopology.AlternatingFaceMapComplex.objD
        ((nerve (Under U)) ⋙ functionsFunctor A) i := by
      simp [L, AlgebraicTopology.AlternatingFaceMapComplex.obj]
    have hK : K.d i (i + 1) = AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (replacementObj.{u, v} ((GrothendieckTopology.pointBot U).skyscraperPresheaf A)) i := by
      change (AlgebraicTopology.AlternatingCofaceMapComplex.obj
        (replacementObj.{u, v} ((GrothendieckTopology.pointBot U).skyscraperPresheaf A))).d i (i + 1) = _
      simp [AlgebraicTopology.AlternatingCofaceMapComplex.obj]
    have key : ∀ k : Fin (i + 2),
        (e i).hom ≫ (SimplicialObject.δ ((nerve (Under U)) ⋙ functionsFunctor A) k).unop =
          (replacementObj.{u, v} ((GrothendieckTopology.pointBot U).skyscraperPresheaf A)).δ k ≫
            (e (i + 1)).hom := by
      intro k
      apply ConcreteCategory.hom_ext
      intro s
      funext x
      exact (he i k x s).symm
    change (e i).hom ≫ (L.d (i + 1) i).unop = K.d i (i + 1) ≫ (e (i + 1)).hom
    rw [hL, hK]
    simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD, unop_sum, unop_zsmul]
    exact comp_sum_zsmul_eq_sum_zsmul_comp (e i).hom (e (i + 1)).hom
      (fun k ↦ (SimplicialObject.δ ((nerve (Under U)) ⋙ functionsFunctor A) k).unop)
      (fun k ↦ (replacementObj.{u, v}
        ((GrothendieckTopology.pointBot U).skyscraperPresheaf A)).δ k)
      (fun k ↦ (-1 : ℤ) ^ (k : ℕ)) key)
  have hL : IsZero (L.homology n) :=
    (HomologicalComplex.isZero_single_obj_homology _ 0 _ n (by omega)).of_iso
      (ed.homotopyEquiv.toHomologyIso n)
  exact IsZero.of_iso (IsZero.of_iso hL.unop (L.homologyUnop n))
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso eK)

/-- A square built from the product comparison morphisms commutes as soon as it commutes
after projecting to each factor. -/
lemma piComparison_comp_pi_map_eq {J : Type*} {D : Type uA} [Category.{vA} D]
    {E : Type*} [Category E] (G G' : D ⥤ E) (L : J → D)
    [HasProduct L] [HasProduct fun j ↦ G.obj (L j)] [HasProduct fun j ↦ G'.obj (L j)]
    (q : ∀ j, G.obj (L j) ⟶ G'.obj (L j)) (d : G.obj (∏ᶜ L) ⟶ G'.obj (∏ᶜ L))
    (h : ∀ j, G.map (Pi.π L j) ≫ q j = d ≫ G'.map (Pi.π L j)) :
    piComparison G L ≫ Limits.Pi.map q = d ≫ piComparison G' L := by
  refine Pi.hom_ext _ _ fun j ↦ ?_
  rw [Category.assoc, Category.assoc, Pi.map_π, piComparison_comp_π_assoc,
    piComparison_comp_π]
  exact h j

/-- In an abelian category with exact products of shape `I`, the homology of a product of
cochain complexes is the product of their homologies. -/
@[implicit_reducible]
def productHomologyIso {B : Type*} [Category B] [Abelian B]
    {I : Type*} [HasProductsOfShape I B] [HasExactLimitsOfShape (Discrete I) B]
    (L : I → CochainComplex B ℕ) (n : ℕ) :
    (∏ᶜ L).homology n ≅ ∏ᶜ fun i ↦ (L i).homology n := by
  let e (k : ℕ) := PreservesProduct.iso (HomologicalComplex.eval B (ComplexShape.up ℕ) k) L
  let eS : (∏ᶜ L).sc n ≅ ShortComplex.pi (fun i ↦ (L i).sc n) :=
    ShortComplex.isoMk (e _) (e _) (e _)
      (by
        simp only [e, PreservesProduct.iso_hom, ShortComplex.pi_f]
        exact piComparison_comp_pi_map_eq
          (HomologicalComplex.eval B (ComplexShape.up ℕ) ((ComplexShape.up ℕ).prev n))
          (HomologicalComplex.eval B (ComplexShape.up ℕ) n) L
          (fun i ↦ (L i).d ((ComplexShape.up ℕ).prev n) n)
          ((∏ᶜ L).d ((ComplexShape.up ℕ).prev n) n)
          (fun i ↦ (Pi.π L i).comm _ _))
      (by
        simp only [e, PreservesProduct.iso_hom, ShortComplex.pi_g]
        exact piComparison_comp_pi_map_eq
          (HomologicalComplex.eval B (ComplexShape.up ℕ) n)
          (HomologicalComplex.eval B (ComplexShape.up ℕ) ((ComplexShape.up ℕ).next n)) L
          (fun i ↦ (L i).d n ((ComplexShape.up ℕ).next n))
          ((∏ᶜ L).d n ((ComplexShape.up ℕ).next n))
          (fun i ↦ (Pi.π L i).comm _ _))
  exact (ShortComplex.homologyFunctor B).mapIso eS ≪≫
    ShortComplex.piHomologyIso (fun i ↦ (L i).sc n)

/-- A product of pushforwards from points is acyclic in positive degrees. -/
@[stacks 08RZ "product acyclicity"]
theorem cochainReplacementPointProductAcyclic
    (C : Type u) [SmallCategory C] (I : Type u)
    (U : I → C) (A : I → AddCommGrpCat.{max u v})
    (n : ℕ) (hn : 0 < n) :
    IsZero ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℕ) n).obj
      ((cochainReplacementComplex C).obj
        (∏ᶜ fun i : I ↦
          (sheafBotEquivalence (C := C) AddCommGrpCat.{max u v}).functor.obj
            ((GrothendieckTopology.pointBot (U i)).skyscraperSheafFunctor.obj (A i))))) := by
  let P : I → Cᵒᵖ ⥤ AddCommGrpCat.{max u v} := fun i ↦
    (sheafBotEquivalence (C := C) AddCommGrpCat.{max u v}).functor.obj
      ((GrothendieckTopology.pointBot (U i)).skyscraperSheafFunctor.obj (A i))
  have : PreservesLimitsOfShape (Discrete I) (cochainReplacementComplex.{u, v} C) :=
    HomologicalComplex.preservesLimitsOfShape_of_eval _ fun k ↦
      replacementDegree_preservesLimitsOfShape.{u, v} C k (Discrete I)
  have : AB4StarOfSize.{u} AddCommGrpCat.{max u v} := AB4StarOfSize_shrink _
  let e := (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
    (PreservesProduct.iso (cochainReplacementComplex C) P) ≪≫
      productHomologyIso (B := AddCommGrpCat.{max u v})
        (fun i ↦ (cochainReplacementComplex C).obj (P i)) n
  exact IsZero.of_iso ((limit.isLimit _).isZero_pt (Functor.isZero _ fun i ↦
    cochainReplacementPointAcyclic C (U i.as) (A i.as) n hn)) e

/-- Every abelian presheaf embeds in a product of point-pushforwards. -/
@[stacks 08RZ "embedding into a product of point pushforwards"]
theorem presheafEmbedsInPointProduct
    (C : Type u) [SmallCategory C] (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    ∃ (I : Type u) (U : I → C) (A : I → AddCommGrpCat.{max u v}),
      ∃ f : F ⟶
        (∏ᶜ fun i : I ↦
          (sheafBotEquivalence (C := C) AddCommGrpCat.{max u v}).functor.obj
            ((GrothendieckTopology.pointBot (U i)).skyscraperSheafFunctor.obj (A i))),
        Mono f := by
  let P : C → Cᵒᵖ ⥤ AddCommGrpCat.{max u v} := fun U ↦
    (GrothendieckTopology.pointBot U).skyscraperPresheaf (F.obj (Opposite.op U))
  let ι : ∀ U, F ⟶ P U := fun U ↦
    (GrothendieckTopology.pointBot U).skyscraperPresheafHomEquiv
      ((GrothendieckTopology.pointBotPresheafFiberIso U AddCommGrpCat.{max u v}).hom.app F)
  refine ⟨C, id, fun U ↦ F.obj (Opposite.op U), Pi.lift ι, ?_⟩
  rw [NatTrans.mono_iff_mono_app]
  intro V
  let r : (∏ᶜ P).obj V ⟶ F.obj V :=
    (Pi.π P V.unop).app V ≫
      Pi.π (fun _ : (GrothendieckTopology.pointBot V.unop).fiber.obj V.unop ↦ F.obj V)
        (shrinkYonedaObjObjEquiv.symm (𝟙 V.unop))
  have h1 : (Pi.lift ι).app V ≫ (Pi.π P V.unop).app V = (ι V.unop).app V :=
    (NatTrans.comp_app (Pi.lift ι) (Pi.π P V.unop) V).symm.trans
      (congrArg (fun α : F ⟶ P V.unop ↦ α.app V) (Pi.lift_comp_π ι V.unop))
  have hr : (Pi.lift ι).app V ≫ r = 𝟙 _ := by
    dsimp [r]
    refine (Category.assoc _ _ _).symm.trans ((congrArg (fun t ↦ t ≫ _) h1).trans ?_)
    dsimp [ι]
    refine ((GrothendieckTopology.pointBot V.unop).skyscraperPresheafHomEquiv_app_π
      ((GrothendieckTopology.pointBotPresheafFiberIso V.unop
        AddCommGrpCat.{max u v}).hom.app F)
      V.unop (shrinkYonedaObjObjEquiv.symm (𝟙 V.unop))).trans ?_
    change ((GrothendieckTopology.pointBot V.unop).toPresheafFiberNatTrans V.unop
      (shrinkYonedaObjObjEquiv.symm (𝟙 V.unop))).app F ≫
        (inv ((GrothendieckTopology.pointBot V.unop).toPresheafFiberNatTrans V.unop
          (shrinkYonedaObjObjEquiv.symm (𝟙 V.unop)))).app F = 𝟙 _
    rw [← NatTrans.comp_app, IsIso.hom_inv_id]
    rfl
  exact mono_of_mono_fac hr

attribute [-instance] CompletePartialOrder.toOrderBot in
/-- The cohomology of the cochain replacement computes the right-derived
functors of global sections on the chaotic site. -/
@[stacks 08RZ "right-derived global sections"]
theorem cochainReplacementHomologyIsoSiteCohomology
    {C : Type u} [SmallCategory C]
    (n : ℕ) :
    Nonempty
      (cochainReplacementComplex.{u, u} C ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n ≅
        (sheafBotEquivalence (C := C) AddCommGrpCat.{u}).inverse ⋙
          Stacks.Cohomology.CompositeRightDerived.siteCohomology
            (⊥ : GrothendieckTopology C) n) := by
  let E := (sheafBotEquivalence (C := C) AddCommGrpCat.{u}).inverse
  have : PreservesFiniteLimits E := by
    dsimp [E]
    infer_instance
  have : PreservesFiniteColimits E := by
    dsimp [E]
    infer_instance
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  have : EnoughInjectives (Cᵒᵖ ⥤ AddCommGrpCat.{u}) := EnoughInjectives.of_equivalence E
  let Z := (constantSheaf (⊥ : GrothendieckTopology C) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let G := Stacks.Cohomology.CompositeRightDerived.siteSections (⊥ : GrothendieckTopology C)
  have : PreservesFiniteLimits G := by
    dsimp [G, Stacks.Cohomology.CompositeRightDerived.siteSections]
    infer_instance
  let r : G ≅ preadditiveCoyoneda.obj (Opposite.op Z) :=
    (Sheaf.ΓNatIsoLim (⊥ : GrothendieckTopology C) AddCommGrpCat.{u}).symm ≪≫
      ModuleSheafCohomology.globalSectionsRepresentation _
  let D := (cochainReplacementDeltaFunctor.{u, u} C).1
  let R := ModuleSheafCohomology.extDeltaFunctor E Z
  have hD : D.IsUniversal := by
    apply DeltaFunctor.isUniversal_of_forall_exists_mono
    intro k F
    obtain ⟨I, U, A, f, hf⟩ := presheafEmbedsInPointProduct C F
    exact ⟨_, f, hf,
      (cochainReplacementPointProductAcyclic C I U A (k + 1) (by omega)).eq_of_tgt _ _⟩
  have hR : R.IsUniversal := ModuleSheafCohomology.extDeltaFunctor_isUniversal E Z
    fun _ _ _ a ↦ CategoryTheory.Abelian.Ext.eq_zero_of_injective a
  let eL := (cochainReplacementZeroHomologyIsoLimit C).some ≪≫
    eqToIso (show (lim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) = E ⋙ G from rfl)
  let e0 : D.functor 0 ≅ R.functor 0 :=
    eL ≪≫ CategoryTheory.Functor.isoWhiskerLeft E
        (r ≪≫ (ModuleSheafCohomology.extZeroIsoCoyoneda Z).symm)
  let e := DeltaFunctor.IsUniversal.isoOfIso e0
  let en : D.functor n ≅ R.functor n :=
    { hom := e.hom.app n
      inv := e.inv.app n
      hom_inv_id := congrArg (fun f ↦ f.app n) e.hom_inv_id
      inv_hom_id := congrArg (fun f ↦ f.app n) e.inv_hom_id }
  cases n with
  | zero =>
    exact ⟨eL ≪≫ CategoryTheory.Functor.isoWhiskerLeft E G.rightDerivedZeroIsoSelf.symm⟩
  | succ k =>
    exact ⟨en ≪≫ CategoryTheory.Functor.isoWhiskerLeft E
      ((ModuleSheafCohomology.rightDerivedCoyonedaSuccIso Z k).symm ≪≫
        (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso r (k + 1)).symm)⟩

end Stacks.CategoryCohomology

end
