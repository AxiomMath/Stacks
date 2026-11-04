module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.ExtensionByZeroRelativeCompactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Recovery21.FilteredColimitsAndCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Compactness of extension by zero under a cofinal collection of finite coverings

Let `(C, O)` be a ringed site, let `B` be a collection of objects of `C`, and let a collection of
covering families be given which is cofinal among the coverings of every object of `B`, is finite,
and whose nonempty iterated fibre products again lie in `B`. Then for `U` in `B` the module
`j_{U!} O_U` is compact relative to the bounded-below part of the derived category of module
sheaves: the canonical map from the direct sum of the groups `Hom(j_{U!} O_U, M i)` to
`Hom(j_{U!} O_U, ∐ M i)` is bijective whenever the coproduct is bounded below.

## Main results

* `Stacks.Cohomology.extensionByZero_unit_hom_coproduct_bijective_of_hasIntersectionsIn`:
  the statement above, Tag 0G22.
* `Stacks.Cohomology.preservesCoproducts_rightDerived_evaluation_of_hasIntersectionsIn`: the
  input Tag 0739 supplies to it, that the cohomology of module sheaves over `U` commutes with
  direct sums.

## Implementation notes

Tag 0G21 (`Stacks.Cohomology.extensionByZero_unit_hom_coproduct_bijective`) reduces the
conclusion to the hypothesis that the right derived functors of evaluation at `U` on module
sheaves commute with arbitrary direct sums, and this file supplies that hypothesis from the
covering families. The chain is: Tag 0739
(`Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections`) makes cohomology of abelian
sheaves over `U` commute with filtered colimits; a coproduct is the filtered colimit of its
finite subcoproducts, so an additive functor commuting with those filtered colimits commutes
with arbitrary coproducts
(`preservesColimitsOfShape_discrete_of_finite_and_filtered`); Tag 03FD
(`ModuleSheafCohomology.sectionsComparisonIso`) and
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` transport that from abelian sheaves to
module sheaves, where the forgetful functor to abelian groups reflects colimits; and finally the
index type is cut down to the universe of the category by discarding the zero summands
(`preservesCoproducts_of_small`), which is what lets the family in the main statement be indexed
by an arbitrary type.

All four universes of the ringed site and of the module sheaves are the single universe `u`.
This is forced by main's vocabulary, not a choice: Tag 0739 is stated for a small site with
coefficients in `Ab.{u}`, and the comparison of Tag 03FD exists only for a small site with
`RingCat.{u}`-valued structure sheaf and `SheafOfModules.{u}`. The index universes of the
covering families and of the direct sum stay arbitrary.

## References

* [Stacks Project, Tag 0G22](https://stacks.math.columbia.edu/tag/0G22)
* [Stacks Project, Tag 0G21](https://stacks.math.columbia.edu/tag/0G21)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Sites.OverModules

universe u i c

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard
/- The two standing facts that let the cohomology of abelian sheaves over an object be written
down. Neither is a global instance, so both have to be installed here for the statement of
Tag 0739 to be applied. -/
attribute [local instance] ColimitsOfCohomology.enoughInjectives_sheaf_ab sections_additive

/-- The right derived functors of an additive functor are additive: a sum of morphisms is
descended to the sum of the descents of the summands. -/
private theorem rightDerived_additive
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasInjectiveResolutions A] (F : A ⥤ B) [F.Additive] (n : ℕ) :
    (F.rightDerived n).Additive where
  map_add {X Y} f g := by
    have h (f : X ⟶ Y) := InjectiveResolution.desc_commutes f (injectiveResolution Y)
      (injectiveResolution X)
    have hsum : (injectiveResolution X).ι ≫ (InjectiveResolution.desc f
        (injectiveResolution Y) (injectiveResolution X) + InjectiveResolution.desc g
          (injectiveResolution Y) (injectiveResolution X)) =
          (CochainComplex.single₀ A).map (f + g) ≫ (injectiveResolution Y).ι := by
      simp only [Preadditive.comp_add, Functor.map_add, Preadditive.add_comp, h]
    rw [F.rightDerived_map_eq n (f + g) _ hsum, F.rightDerived_map_eq n f _ (h f),
      F.rightDerived_map_eq n g _ (h g)]
    simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

attribute [local instance] rightDerived_additive

/-! ### Cohomology over an object of `B` commutes with filtered colimits -/

private lemma preservesFilteredColimits_rightDerived_sections
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Set C) (Cov : ∀ U : C, Set (PreZeroHypercover.{c} U))
    (hCov : ∀ (U : C) (E : PreZeroHypercover.{c} U), Cov U E → E.sieve₀ ∈ J U)
    (hfinite : ∀ (U : C) (E : PreZeroHypercover.{c} U), Cov U E → HasIntersectionsIn B E)
    (hcofinal : ∀ (U : C), B U → ∀ S ∈ J U,
      ∃ E : PreZeroHypercover.{c} U, Cov U E ∧ E.sieve₀ ≤ S)
    (U : C) (hU : B U) (p : ℕ) :
    PreservesFilteredColimitsOfSize.{u, u}
      (((sheafSections J Ab.{u}).obj (op U)).rightDerived p) := by
  refine ⟨fun T _ _ => ⟨fun {F} => ?_⟩⟩
  have := isIso_colimit_post_rightDerived_sheafSections J B Cov hCov hfinite hcofinal p U hU F
  exact preservesColimit_of_isIso_post _ _

/-! ### Finite coproducts and filtered colimits give all coproducts -/

section Coproducts

variable {A : Type*} [Category* A] {D : Type*} [Category* D] [HasFiniteCoproducts A]
  (G : A ⥤ D) [PreservesFiniteCoproducts G] {I : Type*}

/-- The inclusion of one summand into a finite subcoproduct, written at the spelling the
`Finset`-indexed diagram of finite subcoproducts uses for its values. Naming it is what makes
the identification `(liftToFinsetObj F).obj S = ∐ fun x : S => F.obj x` happen once. -/
private noncomputable abbrev finStageι (M : I → A) (S : Finset (Discrete I)) (x : S) :
    (Discrete.functor M).obj x.1 ⟶
      (CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor M)).obj S :=
  Sigma.ι (fun y : S => (Discrete.functor M).obj y.1) x

private lemma finStageι_comp_map (M : I → A) {S T : Finset (Discrete I)} (h : S ⟶ T) (x : S) :
    finStageι M S x ≫
        (CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor M)).map h =
      finStageι M T ⟨x.1, h.down.down x.2⟩ :=
  Sigma.ι_desc _ _

private lemma finStageι_comp_ι_app (M : I → A) [HasCoproduct M] (S : Finset (Discrete I))
    (x : S) :
    finStageι M S x ≫
        (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone M).ι.app S =
      Sigma.ι M x.1.as :=
  Sigma.ι_desc _ _

/-- A finite stage of the diagram of finite subcoproducts stays a coproduct after applying `G`,
because `G` preserves finite coproducts. -/
private noncomputable def finStageIsColimit (M : I → A) (S : Finset (Discrete I)) :
    IsColimit (Cofan.mk
      (G.obj ((CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor M)).obj S))
      (fun x : S => G.map (finStageι M S x))) :=
  isColimitCofanMkObjOfIsColimit G _ _ (coproductIsCoproduct _)

/-- A cofan on the images of the summands induces a cocone on the image of the diagram of
finite subcoproducts. -/
private noncomputable def finStageCocone (M : I → A)
    (t : Cofan fun j => G.obj (M j)) :
    Cocone (CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor M) ⋙ G) where
  pt := t.pt
  ι :=
    { app := fun S => Cofan.IsColimit.desc (finStageIsColimit G M S)
        (fun x : S => t.inj x.1.as)
      naturality := by
        intro S T h
        refine Cofan.IsColimit.hom_ext (finStageIsColimit G M S) _ _ (fun x => ?_)
        have h₁ : G.map (finStageι M S x) ≫
            ((CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor M) ⋙ G).map h ≫
              Cofan.IsColimit.desc (finStageIsColimit G M T)
                (fun y : T => t.inj y.1.as)) = t.inj x.1.as := by
          rw [← Category.assoc, Functor.comp_map, ← G.map_comp, finStageι_comp_map]
          exact Cofan.IsColimit.fac (finStageIsColimit G M T) _ _
        have h₂ : G.map (finStageι M S x) ≫
            (Cofan.IsColimit.desc (finStageIsColimit G M S) (fun y : S => t.inj y.1.as) ≫
              ((Functor.const (Finset (Discrete I))).obj t.pt).map h) = t.inj x.1.as := by
          rw [Functor.const_obj_map, Category.comp_id]
          exact Cofan.IsColimit.fac (finStageIsColimit G M S) _ _
        exact h₁.trans h₂.symm }

private lemma finStageCocone_ι_app (M : I → A) (t : Cofan fun j => G.obj (M j))
    (S : Finset (Discrete I)) :
    (finStageCocone G M t).ι.app S =
      Cofan.IsColimit.desc (finStageIsColimit G M S) (fun x : S => t.inj x.1.as) :=
  rfl

/-- A functor preserving finite coproducts and the filtered colimits indexed by the finite
subsets of `I` preserves `I`-indexed coproducts, because an `I`-indexed coproduct is the
filtered colimit of its finite subcoproducts. -/
private lemma preservesColimitsOfShape_discrete_of_finite_and_filtered
    [HasColimitsOfShape (Finset (Discrete I)) A]
    [PreservesColimitsOfShape (Finset (Discrete I)) G] :
    PreservesColimitsOfShape (Discrete I) G := by
  have hM (M : I → A) : PreservesColimit (Discrete.functor M) G := by
    have : HasCoproduct M :=
      ⟨⟨CoproductsFromFiniteFiltered.liftToFinsetColimitCocone (Discrete.functor M)⟩⟩
    have hc : IsColimit (G.mapCocone
        (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone M)) :=
      isColimitOfPreserves G (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone M)
    have hι (S : Finset (Discrete I)) (x : S) : G.map (finStageι M S x) ≫
        (G.mapCocone (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone M)).ι.app S =
          G.map (Sigma.ι M x.1.as) :=
      (G.map_comp _ _).symm.trans (congrArg G.map (finStageι_comp_ι_app M S x))
    refine preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct M) ?_
    refine (isColimitMapCoconeCofanMkEquiv G M (Sigma.ι M)).symm ?_
    refine Cofan.IsColimit.mk _ (fun t => hc.desc (finStageCocone G M t)) ?_ ?_
    · intro t j
      have hmem : (⟨j⟩ : Discrete I) ∈ ({⟨j⟩} : Finset (Discrete I)) :=
        Finset.mem_singleton_self _
      have key := congrArg (· ≫ hc.desc (finStageCocone G M t))
        (hι ({⟨j⟩} : Finset (Discrete I)) ⟨⟨j⟩, hmem⟩)
      simp only [Category.assoc] at key
      refine key.symm.trans ?_
      rw [hc.fac, finStageCocone_ι_app]
      exact Cofan.IsColimit.fac (finStageIsColimit G M _) _ ⟨⟨j⟩, hmem⟩
    · intro t m hm
      refine hc.hom_ext (fun S => ?_)
      have hr : (G.mapCocone
          (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone M)).ι.app S ≫
            hc.desc (finStageCocone G M t) =
          Cofan.IsColimit.desc (finStageIsColimit G M S) (fun x : S => t.inj x.1.as) :=
        (hc.fac (finStageCocone G M t) S).trans (finStageCocone_ι_app G M t S)
      refine Eq.trans ?_ hr.symm
      refine Cofan.IsColimit.hom_ext (finStageIsColimit G M S) _ _ (fun x => ?_)
      have key : G.map (finStageι M S x) ≫
          ((G.mapCocone (CoproductsFromFiniteFiltered.finiteSubcoproductsCocone M)).ι.app S ≫
            m) = G.map (Sigma.ι M x.1.as) ≫ m :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ m) (hι S x))
      exact key.trans ((hm x.1.as).trans
        (Cofan.IsColimit.fac (finStageIsColimit G M S)
          (fun y : S => t.inj y.1.as) x).symm)
  exact preservesColimitsOfShape_of_discrete G

end Coproducts

/-! ### Coproducts indexed by an arbitrary type -/

private lemma small_nonzero_coproduct
    {A : Type*} [Category.{u} A] [HasZeroMorphisms A]
    {I : Type i} (M : I → A) [HasCoproduct M] : Small.{u} {j : I // ¬ IsZero (M j)} := by
  classical
  apply small_of_injective.{u, u, i} (f := fun j : {j : I // ¬ IsZero (M j)} =>
    Sigma.π M j.1 ≫ Sigma.ι M j.1)
  intro j k h
  by_contra hne
  have hjk : j.1 ≠ k.1 := fun h => hne (Subtype.ext h)
  have hh := congrArg (fun f => Sigma.ι M j.1 ≫ f ≫ Sigma.π M j.1) h
  have hid : 𝟙 (M j.1) = 0 := by
    simpa [Category.assoc, Sigma.ι_π_of_ne_assoc _ hjk] using hh
  exact j.2 ((IsZero.iff_id_eq_zero _).mpr hid)

/-- **A colimit cofan restricted to the indices satisfying a property which fails only at zero
objects is still colimiting.** A cofan on the subfamily is extended by zero on the discarded
indices. -/
noncomputable def restrictCofanIsColimit
    {A : Type*} [Category* A] [HasZeroMorphisms A]
    {I : Type*} {M : I → A} (c : Cofan M) (hc : IsColimit c)
    (P : I → Prop) (hP : ∀ j, ¬ P j → IsZero (M j)) :
    IsColimit (Cofan.mk c.pt (fun j : {j // P j} => c.inj j.1)) := by
  classical
  refine Cofan.IsColimit.mk _ (fun s => Cofan.IsColimit.desc hc
    (fun j => if h : P j then s.inj ⟨j, h⟩ else 0)) ?_ ?_
  · intro s j
    simpa only [cofan_mk_inj, dite_eq_left j.2] using
      Cofan.IsColimit.fac hc (fun k => if h : P k then s.inj ⟨k, h⟩ else 0) j.1
  · intro s f hf
    refine Cofan.IsColimit.hom_ext hc _ _ (fun j => ?_)
    rw [Cofan.IsColimit.fac]
    by_cases hj : P j
    · simpa only [cofan_mk_inj, dite_eq_left hj] using hf ⟨j, hj⟩
    · exact (hP j hj).eq_of_src _ _

/-- **The converse of `restrictCofanIsColimit`**: a cofan whose restriction to the indices
satisfying a property failing only at zero objects is colimiting is itself colimiting. -/
noncomputable def cofanIsColimitOfRestriction
    {A : Type*} [Category* A] [HasZeroMorphisms A]
    {I : Type*} {M : I → A} (c : Cofan M)
    (P : I → Prop) (hP : ∀ j, ¬ P j → IsZero (M j))
    (hc : IsColimit (Cofan.mk c.pt (fun j : {j // P j} => c.inj j.1))) :
    IsColimit c := by
  refine Cofan.IsColimit.mk _ (fun s => Cofan.IsColimit.desc hc
    (fun j : {j // P j} => s.inj j.1)) ?_ ?_
  · intro s j
    by_cases hj : P j
    · simpa only [cofan_mk_inj] using Cofan.IsColimit.fac hc _ ⟨j, hj⟩
    · exact (hP j hj).eq_of_src _ _
  · intro s f hf
    refine Cofan.IsColimit.hom_ext hc _ _ (fun j => ?_)
    rw [Cofan.IsColimit.fac, cofan_mk_inj]
    exact hf j.1

/-- A functor between categories with zero morphisms that preserves coproducts indexed by the
types in the universe of its source's morphisms preserves coproducts indexed by any type: all
but a small set of summands of a coproduct are zero. -/
private lemma preservesCoproducts_of_small
    {A : Type*} [Category.{u} A] [HasZeroMorphisms A]
    {D : Type*} [Category* D] [HasZeroMorphisms D]
    (G : A ⥤ D) [G.PreservesZeroMorphisms]
    (hG : ∀ T : Type u, PreservesColimitsOfShape (Discrete T) G)
    (I : Type i) : PreservesColimitsOfShape (Discrete I) G := by
  classical
  have hM (M : I → A) : PreservesColimit (Discrete.functor M) G := by
    refine ⟨fun {c} hc => ⟨?_⟩⟩
    have : HasCoproduct M := ⟨⟨⟨c, hc⟩⟩⟩
    have hsmall : Small.{u} {j // ¬ IsZero (M j)} := small_nonzero_coproduct M
    have := hG (Shrink.{u} {j // ¬ IsZero (M j)})
    have : PreservesColimitsOfShape (Discrete {j // ¬ IsZero (M j)}) G :=
      preservesColimitsOfShape_of_equiv
        (Discrete.equivalence (equivShrink.{u} {j // ¬ IsZero (M j)}).symm) G
    have hc' : IsColimit (Cofan.mk c.pt
        (fun j : {j // ¬ IsZero (M j)} => Cofan.inj c j.1)) :=
      restrictCofanIsColimit c hc _ (fun j hj => not_not.mp hj)
    have hd := isColimitCofanMkObjOfIsColimit G (fun j : {j // ¬ IsZero (M j)} => M j.1)
      (fun j => Cofan.inj c j.1) hc'
    have hfull : IsColimit (Cofan.mk (G.obj c.pt) (fun j => G.map (Cofan.inj c j))) :=
      cofanIsColimitOfRestriction _ _ (fun j hj => G.map_isZero (not_not.mp hj)) hd
    exact (Cofan.isColimitMapCoconeEquiv G M c).symm hfull
  exact preservesColimitsOfShape_of_discrete G

/-! ### Deriving module sections commutes with coproducts -/

private lemma preservesCoproducts_rightDerived_evaluation
    (X : RingedSite.{u, u, u})
    (B : Set X.C) (Cov : ∀ U : X.C, Set (PreZeroHypercover.{c} U))
    (hCov : ∀ (U : X.C) (E : PreZeroHypercover.{c} U), Cov U E → E.sieve₀ ∈ X.J U)
    (hfinite : ∀ (U : X.C) (E : PreZeroHypercover.{c} U), Cov U E → HasIntersectionsIn B E)
    (hcofinal : ∀ (U : X.C), B U → ∀ S ∈ X.J U,
      ∃ E : PreZeroHypercover.{c} U, Cov U E ∧ E.sieve₀ ≤ S)
    (U : X.C) (hU : B U) (p : ℕ) (I : Type u) :
    let : EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      enoughInjectives_of_ringedSite.{u, u, u, u} X
    let : (SheafOfModules.evaluation.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
      evaluation_additive_of_ringedSite.{u, u, u, u} X U
    PreservesColimitsOfShape (Discrete I)
      ((SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).rightDerived p) := by
  let : EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    enoughInjectives_of_ringedSite.{u, u, u, u} X
  let : (SheafOfModules.evaluation.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
    evaluation_additive_of_ringedSite.{u, u, u, u} X U
  set F := SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
  set G :=
    forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) Ab.{u}
  set T := SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  set S := (sheafSections X.J Ab.{u}).obj (op U)
  have : PreservesFilteredColimitsOfSize.{u, u} (S.rightDerived p) :=
    preservesFilteredColimits_rightDerived_sections X.J B Cov hCov hfinite hcofinal U hU p
  have : PreservesColimitsOfShape (Discrete I) (S.rightDerived p) :=
    preservesColimitsOfShape_discrete_of_finite_and_filtered (S.rightDerived p)
  have e :=
    ModuleSheafCohomology.sectionsComparisonIso X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U p
  have : PreservesColimitsOfShape (Discrete I) ((T ⋙ S).rightDerived p) :=
    preservesColimitsOfShape_of_natIso e.symm
  have : PreservesColimitsOfShape (Discrete I) (F.rightDerived p ⋙ G) :=
    preservesColimitsOfShape_of_natIso
      (ModuleComparison.rightDerivedCompIso F G (T ⋙ S) (Iso.refl _) p).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (F.rightDerived p) G

/-- **The cohomology of module sheaves over `U` commutes with direct sums**, for `U` in a
collection `B` of objects having a cofinal system of covering families whose nonempty iterated
fibre products again lie in `B`. This is the hypothesis Tag 0G21 consumes, and it is what
hypotheses (2) and (3) of Tag 09JC supply through Tag 0739; the chain is described in the
implementation notes of this module.

The index type is the universe of the site; `preservesCoproducts_of_small` widens it. -/
public alias preservesCoproducts_rightDerived_evaluation_of_hasIntersectionsIn :=
  preservesCoproducts_rightDerived_evaluation

/-! ### The tag -/

/-- On a ringed site with a cofinal collection of finite coverings closed under finite
intersections, extension by zero of the unit module over `U` is compact with respect to
bounded-below coproducts. -/
@[stacks 0G22]
public theorem extensionByZero_unit_hom_coproduct_bijective_of_hasIntersectionsIn
    (X : RingedSite.{u, u, u})
    (B : Set X.C) (Cov : ∀ U : X.C, Set (PreZeroHypercover.{c} U))
    (hCov : ∀ (U : X.C) (E : PreZeroHypercover.{c} U), Cov U E → E.sieve₀ ∈ X.J U)
    (hfinite : ∀ (U : X.C) (E : PreZeroHypercover.{c} U), Cov U E →
      HasIntersectionsIn B E)
    (hcofinal : ∀ (U : X.C), B U → ∀ S ∈ X.J U,
      ∃ E : PreZeroHypercover.{c} U, Cov U E ∧ E.sieve₀ ≤ S)
    (U : X.C) (hU : B U)
    (I : Type i) [DecidableEq I]
    (M : I → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct M]
    (hM : (DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).plus (∐ M)) :
    let K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (extensionByZeroUnit.{u, u, u, u} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U))
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun j : I => K ⟶ M j) (γ := K ⟶ ∐ M)
        fun j => Preadditive.rightComp K (Limits.Sigma.ι M j)) := by
  refine extensionByZero_unit_hom_coproduct_bijective.{u, u, u, i, u} X U ?_ I M hM
  let : EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    enoughInjectives_of_ringedSite.{u, u, u, u} X
  let : (SheafOfModules.evaluation.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
    evaluation_additive_of_ringedSite.{u, u, u, u} X U
  intro p T
  exact preservesCoproducts_of_small _
    (preservesCoproducts_rightDerived_evaluation X B Cov hCov hfinite hcofinal U hU p) T

end Stacks.Cohomology

end
