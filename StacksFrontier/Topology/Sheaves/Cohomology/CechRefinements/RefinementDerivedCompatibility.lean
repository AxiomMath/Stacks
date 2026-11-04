module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.DerivedGlobalSectionsCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.TotalComplexComparison
public import StacksFrontier.Algebra.Homology.MapTotalComplex

/-!
# The Čech refinement map on the total complex of a Čech bicomplex

Let `f : X ⟶ Y` be a morphism of ringed spaces, let `U` be an open covering of `X`, let `V` be
an open covering of `Y` and let `c` be a refinement function.  For a complex `K` of sheaves of
modules on `X` the counit of the adjunction `f^* ⊣ f_*` is an `f`-map from the pushforward of
each term of `K` to that term, so the Čech refinement map of [Stacks, Tag 01FD] assembles into
a morphism of Čech bicomplexes

`Č(V, f_* K) ⟶ Č(U, K)`,

the target read with scalars restricted to `Γ(Y, 𝒪_Y)`, and hence into a morphism of the total
complexes, compatible with the two augmentations `α` and `β` of the proof of [Stacks, Tag 01FD].

## Main definitions

* `Stacks.Cohomology.CechRefinement.cechBicomplexRefinementMap`: the refinement map of Čech
  bicomplexes.
* `Stacks.Cohomology.CechRefinement.cechTotalRefinementMap`: the induced map of total
  complexes.

## Main results

* `Stacks.Cohomology.CechRefinement.ιTotal_comp_cechTotalRefinementMap`: the degreewise
  formula, against the inclusions of the summands of the total complex.
* `Stacks.Cohomology.CechRefinement.cechTotalAugmentation_cechTotalRefinementMap`: the
  refinement map is compatible with the total Čech augmentation `α`.
* `Stacks.Cohomology.CechRefinement.cechBeta_cechTotalRefinementMap`: the refinement map is
  compatible with the augmentation `β`.

## References

* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open TopologicalSpace
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheaf)
open Stacks.Cohomology.CechDerived (cechComplexNatFunctor cechComplexIntFunctor
  cechAugmentationInt cechBicomplex cechBeta cechBeta_f cechTotalAugmentation
  cechTotalAugmentation_f)
open RingedSpaceModuleAdjunction (modulePushforward modulePullback homEquiv)

attribute [local implicit_reducible] TopCat.Sheaf
attribute [local implicit_reducible] structureSheafRing
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.sectionsPresheaf
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.cechComplexFunctorOfCover
attribute [local implicit_reducible] Stacks.Cohomology.CechDerived.cechComplexNatFunctor
attribute [local implicit_reducible] Stacks.Cohomology.CechDerived.cechComplexIntFunctor
attribute [local implicit_reducible] Stacks.Cohomology.CechSheaf.sectionsTerminalFunctor
attribute [local implicit_reducible] ComplexShape.Embedding.extendFunctor
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

universe u

namespace Stacks.Cohomology.CechRefinement

noncomputable section

attribute [local instance] ModuleCat.hasLimitsOfSize

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {I J : Type u} (U : I → Opens X.carrier) (V : J → Opens Y.carrier)
  (hU : (⊤ : Opens X.carrier) = ⨆ i, U i) (hV : (⊤ : Opens Y.carrier) = ⨆ j, V j)
  (c : I → J) (hc : ∀ i, U i ≤ (Opens.map f.hom.base).obj (V (c i)))

/-- The Čech refinement map of a complex of sheaves of modules, as a map of Čech bicomplexes: in
resolution degree `q` it is the Čech refinement map attached to the counit `f^* f_* K^q ⟶ K^q`,
which is an `f`-map. -/
def cechBicomplexRefinementMap (K : CochainComplex (Modules X) ℤ) :
    cechBicomplex (ringCatSheaf Y) ⊤ V hV
        (((modulePushforward f).mapHomologicalComplex (up ℤ)).obj K) ⟶
      HomologicalComplex₂.TotalMap.mapBicomplex (restrictGlobalScalars f)
        (cechBicomplex (ringCatSheaf X) ⊤ U hU K) where
  f q := cechComplexRefinementMapInt f (K.X q) ((modulePushforward f).obj (K.X q))
    (pushforwardCounit f (K.X q)) U V hU hV c hc
  comm' p q _ :=
    (cechComplexRefinementMapInt_naturality f (K.X p)
      ((modulePushforward f).obj (K.X p)) (pushforwardCounit f (K.X p)) U V hU hV c hc
      (pushforwardCounit f (K.X q)) ((modulePushforward f).map (K.d p q)) (K.d p q) (by
        dsimp only [pushforwardCounit]
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.comp_id,
          Category.id_comp])).symm

/-- The Čech refinement map on the total complexes: the map of total complexes induced by
`Stacks.Cohomology.CechRefinement.cechBicomplexRefinementMap`, followed by the comparison of the
total complex with restriction of scalars. -/
def cechTotalRefinementMap (K : CochainComplex (Modules X) ℤ) :
    (cechBicomplex (ringCatSheaf Y) ⊤ V hV
        (((modulePushforward f).mapHomologicalComplex (up ℤ)).obj K)).total (up ℤ) ⟶
      ((restrictGlobalScalars f).mapHomologicalComplex (up ℤ)).obj
        ((cechBicomplex (ringCatSheaf X) ⊤ U hU K).total (up ℤ)) :=
  HomologicalComplex₂.total.map (cechBicomplexRefinementMap f U V hU hV c hc K) (up ℤ) ≫
    HomologicalComplex₂.TotalMap.totalMap (restrictGlobalScalars f)
      (cechBicomplex (ringCatSheaf X) ⊤ U hU K)

/-- The degreewise formula for the refinement map of total complexes, against the inclusion of
the summand of bidegree `(p, q)`: it is the degree-`q` component of the Čech refinement map of
`K^p`, followed by the image of the corresponding inclusion. -/
theorem ιTotal_comp_cechTotalRefinementMap (K : CochainComplex (Modules X) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    (cechBicomplex (ringCatSheaf Y) ⊤ V hV
          (((modulePushforward f).mapHomologicalComplex (up ℤ)).obj K)).ιTotal
          (up ℤ) p q n h ≫
        (cechTotalRefinementMap f U V hU hV c hc K).f n =
      (cechComplexRefinementMapInt f (K.X p) ((modulePushforward f).obj (K.X p))
          (pushforwardCounit f (K.X p)) U V hU hV c hc).f q ≫
        (restrictGlobalScalars f).map
          ((cechBicomplex (ringCatSheaf X) ⊤ U hU K).ιTotal (up ℤ) p q n h) := by
  have hmap : (HomologicalComplex₂.TotalMap.mapBicomplex (restrictGlobalScalars f)
          (cechBicomplex (ringCatSheaf X) ⊤ U hU K)).ιTotal (up ℤ) p q n h ≫
        (HomologicalComplex₂.TotalMap.totalMap (restrictGlobalScalars f)
          (cechBicomplex (ringCatSheaf X) ⊤ U hU K)).f n =
      (restrictGlobalScalars f).map
        ((cechBicomplex (ringCatSheaf X) ⊤ U hU K).ιTotal (up ℤ) p q n h) :=
    HomologicalComplex₂.TotalMap.ι_totalMapf (restrictGlobalScalars f)
      (cechBicomplex (ringCatSheaf X) ⊤ U hU K) n p q h
  dsimp only [cechTotalRefinementMap]
  rw [HomologicalComplex.comp_f, ← Category.assoc,
    HomologicalComplex₂.ιTotal_map _ _ (cechBicomplexRefinementMap f U V hU hV c hc K)
      (up ℤ) p q n h, Category.assoc, hmap]
  rfl

/-- The Čech refinement map is compatible with the total Čech augmentation `α`: both routes from
the sections of the pushforward complex over `Y` to the total complex of the Čech bicomplex of `K`
on `X` agree. -/
theorem cechTotalAugmentation_cechTotalRefinementMap (K : CochainComplex (Modules X) ℤ)
    [K.IsStrictlyGE 0]
    [CochainComplex.IsStrictlyGE
      (((modulePushforward f).mapHomologicalComplex (up ℤ)).obj K) 0]
    (hK : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj (K.X q)).homology n))
    (hKP : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((cechComplexNatFunctor (ringCatSheaf Y) ⊤ V hV).obj
        ((((modulePushforward f).mapHomologicalComplex (up ℤ)).obj K).X q)).homology n)) :
    cechTotalAugmentation (ringCatSheaf Y) ⊤ V hV
          (((modulePushforward f).mapHomologicalComplex (up ℤ)).obj K) hKP ≫
        cechTotalRefinementMap f U V hU hV c hc K =
      ((restrictGlobalScalars f).mapHomologicalComplex (up ℤ)).map
        (cechTotalAugmentation (ringCatSheaf X) ⊤ U hU K hK) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  have hsq : cechAugmentationInt (ringCatSheaf Y) ⊤ V hV
          ((modulePushforward f).obj (K.X n)) ≫
        (cechComplexRefinementMapInt f (K.X n) ((modulePushforward f).obj (K.X n))
          (pushforwardCounit f (K.X n)) U V hU hV c hc).f 0 =
      (restrictGlobalScalars f).map
        (cechAugmentationInt (ringCatSheaf X) ⊤ U hU (K.X n)) :=
    cechAugmentationInt_pushforwardCounit f (K.X n) U V hU hV c hc
  refine Eq.trans (congrArg (fun z ↦ z ≫ (cechTotalRefinementMap f U V hU hV c hc K).f n)
    (cechTotalAugmentation_f (ringCatSheaf Y) ⊤ V hV _ hKP n)) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (fun z ↦ cechAugmentationInt (ringCatSheaf Y) ⊤ V hV
      ((modulePushforward f).obj (K.X n)) ≫ z)
    (ιTotal_comp_cechTotalRefinementMap f U V hU hV c hc K n 0 n (add_zero n))) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫ (restrictGlobalScalars f).map
      ((cechBicomplex (ringCatSheaf X) ⊤ U hU K).ιTotal (up ℤ) n 0 n (add_zero n))) hsq) ?_
  refine ((restrictGlobalScalars f).map_comp _ _).symm.trans ?_
  exact congrArg (restrictGlobalScalars f).map
    (cechTotalAugmentation_f (ringCatSheaf X) ⊤ U hU K hK n).symm

/-- The Čech refinement map is compatible with the augmentation `β`: a section of a sheaf `G` on
`Y` killed by the first differential of the pushforward complex, included in the total complex of
the Čech bicomplex on `Y`, is carried by the refinement map to the corresponding inclusion on `X`,
composed with the Čech refinement map of the `f`-map `φ`. -/
theorem cechBeta_cechTotalRefinementMap {F : Modules X} {G : Modules Y}
    (φ : (modulePullback f).obj G ⟶ F) (K : CochainComplex (Modules X) ℤ)
    [K.IsStrictlyGE 0]
    [CochainComplex.IsStrictlyGE
      (((modulePushforward f).mapHomologicalComplex (up ℤ)).obj K) 0]
    (ξ : F ⟶ K.X 0) (hξ : ξ ≫ K.d 0 1 = 0)
    (ξP : G ⟶ (((modulePushforward f).mapHomologicalComplex (up ℤ)).obj K).X 0)
    (hξP : ξP ≫ (((modulePushforward f).mapHomologicalComplex (up ℤ)).obj K).d 0 1 = 0)
    (hcompat : ξP = homEquiv f F G φ ≫ (modulePushforward f).map ξ) :
    cechBeta (ringCatSheaf Y) ⊤ V hV
          (((modulePushforward f).mapHomologicalComplex (up ℤ)).obj K) ξP hξP ≫
        cechTotalRefinementMap f U V hU hV c hc K =
      cechComplexRefinementMapInt f F G φ U V hU hV c hc ≫
        ((restrictGlobalScalars f).mapHomologicalComplex (up ℤ)).map
          (cechBeta (ringCatSheaf X) ⊤ U hU K ξ hξ) := by
  have hnat := cechComplexRefinementMapInt_naturality f F G φ U V hU hV c hc
    (pushforwardCounit f (K.X 0)) ξP ξ (by
      dsimp only [pushforwardCounit]
      rw [Equiv.apply_symm_apply, Category.comp_id, hcompat])
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  have hn := congrArg (fun k ↦ HomologicalComplex.Hom.f k n) hnat
  simp only [HomologicalComplex.comp_f] at hn
  refine Eq.trans (congrArg (fun z ↦ z ≫ (cechTotalRefinementMap f U V hU hV c hc K).f n)
    (cechBeta_f (ringCatSheaf Y) ⊤ V hV _ ξP hξP n)) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg
    (fun z ↦ ((cechComplexIntFunctor (ringCatSheaf Y) ⊤ V hV).map ξP).f n ≫ z)
    (ιTotal_comp_cechTotalRefinementMap f U V hU hV c hc K 0 n n (zero_add n))) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫ (restrictGlobalScalars f).map
      ((cechBicomplex (ringCatSheaf X) ⊤ U hU K).ιTotal (up ℤ) 0 n n (zero_add n))) hn) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg
    (fun z ↦ (cechComplexRefinementMapInt f F G φ U V hU hV c hc).f n ≫ z)
    ((restrictGlobalScalars f).map_comp
      (((cechComplexIntFunctor (ringCatSheaf X) ⊤ U hU).map ξ).f n)
      ((cechBicomplex (ringCatSheaf X) ⊤ U hU K).ιTotal (up ℤ) 0 n n (zero_add n))).symm) ?_
  exact congrArg
    (fun z ↦ (cechComplexRefinementMapInt f F G φ U V hU hV c hc).f n ≫
      (restrictGlobalScalars f).map z)
    (cechBeta_f (ringCatSheaf X) ⊤ U hU K ξ hξ n).symm

end

end Stacks.Cohomology.CechRefinement

end
