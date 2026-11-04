module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors

/-! # `R(G ∘ F) ≅ RG ∘ RF` on `D⁺`, for `F` preserving injective objects

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors between abelian categories, with `𝒜` and
`ℬ` having enough injectives, so that the three right derived functors
`RF : D⁺(𝒜) ⥤ D⁺(ℬ)`, `RG : D⁺(ℬ) ⥤ D⁺(𝒞)` and `R(G ∘ F) : D⁺(𝒜) ⥤ D⁺(𝒞)` are everywhere
defined.  Because `R(G ∘ F)` is the right derived functor of `K⁺(𝒜) ⥤ D⁺(𝒞)` along the
localization `Qh : K⁺(𝒜) ⥤ D⁺(𝒜)` at the quasi-isomorphisms, there is exactly one
transformation

`t : R(G ∘ F) ⟶ RG ∘ RF`

whose composite with the unit of `R(G ∘ F)` is the transformation
`G(F(K)) ⟶ RG(F(K)) ⟶ RG(RF(K))` assembled from the units of `RG` and of `RF`
(`CategoryTheory.Functor.rightComparisonUnit`).  This file *constructs* that `t`
(`rightDerivedFunctorPlusComp`), records the factorization characterising it
(`rightDerivedFunctorPlusComp_fac`), and shows that `t` is invertible as soon as `F` carries
injective objects to injective objects, producing the natural isomorphism

`rightDerivedFunctorPlusCompIso : R(G ∘ F) ≅ RF ⋙ RG`

of functors `D⁺(𝒜) ⥤ D⁺(𝒞)`.  This is the comparison the Grothendieck spectral sequence needs
in order to identify its abutment: the spectral object of the canonical truncation tower of
`RF K` pushed along `RG` abuts to `Hⁿ(RG(RF K))`, and the isomorphism above rewrites that as
`Hⁿ(R(G ∘ F) K)`.

## The argument

`K⁺(𝒜)` carries the injective derivability structure for the quasi-isomorphisms
(`HomotopyCategory.Plus.localizerMorphism`), so a transformation out of a functor on `K⁺(𝒜)`
exhibits its target as *the* right derived functor exactly when it is invertible on the bounded
below complexes of injective objects of `𝒜`
(`CategoryTheory.LocalizerMorphism.Derives.isRightDerivedFunctor_of_isIso`).  For `K` such a
complex, `rightComparisonUnit F G` at `K` is a composite of three maps, each invertible:

* the coherence isomorphism identifying the functor induced by `G ∘ F` on `K⁺` with the
  composite of the functors induced by `F` and by `G`;
* the unit of `RG` at `F(K)`, invertible because `F` preserves injective objects, so `F(K)` is
  again a bounded below complex of injectives;
* the image under `RG` of the unit of `RF` at `K`, invertible because `K` is a bounded below
  complex of injectives.

Hence `RF ⋙ RG`, with `rightComparisonUnit F G`, is a right derived functor of
`K⁺(𝒜) ⥤ D⁺(𝒞)`; `t`, being the descent of `rightComparisonUnit F G` along the unit of
`R(G ∘ F)`, is therefore invertible.

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusComp`: the canonical transformation
  `t : R(G ∘ F) ⟶ RF ⋙ RG` of [Stacks, Tag 05T2], in the bounded below derived categories.
* `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`: for `F` preserving injective
  objects, the natural isomorphism `R(G ∘ F) ≅ RF ⋙ RG`, with `t` as its `hom`.

## Main results

* `CategoryTheory.Functor.rightDerivedFunctorPlusComp_fac` and
  `rightDerivedFunctorPlusComp_fac_app`: the factorization through the unit of `R(G ∘ F)` that
  characterises `t`; it is exactly the hypothesis `ht` of
  `CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective` ([Stacks, Tag 015M]).
* `CategoryTheory.Functor.rightDerivedFunctorPlusComp_naturality`: the naturality square of
  `t`, named so that a downstream identification can cite it.
* `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusComp`: `t` is invertible when `F`
  preserves injective objects.
* `CategoryTheory.Functor.rightAcyclic_obj_of_preservesInjectiveObjects`: a functor preserving
  injective objects carries injective objects to objects right acyclic for `G`; read off
  [Stacks, Tag 015M] and recorded because it is the hypothesis every other form of the
  criterion is phrased with.

## Implementation notes

* The comparison is **data**, not a `Nonempty`: `rightDerivedFunctorPlusComp` is a named
  natural transformation and `rightDerivedFunctorPlusCompIso` is a named isomorphism of
  functors, so its naturality square is available (and named) and a downstream statement can
  be identified through it.  This is the difference from
  `CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`
  ([Stacks, Tag 015N]) and from
  `CochainComplex.CartanEilenbergResolution.exists_homologyIso_rightDerivedPlus`, both of which
  deliver their comparisons as `Nonempty (… ≅ …)`, from which no square can be deduced.
* No left exactness is assumed.  The source's hypothesis that `F` be left exact is not used:
  the only inputs are the injective derivability structure of `K⁺(𝒜)` and the invertibility of
  the units of `RF` and `RG` on complexes of injectives, both of which hold for additive `F`
  and `G`.  The statement for left exact `F` is the special case.
* No hypothesis is idle. `EnoughInjectives 𝒜` makes `RF` and `R(G ∘ F)` everywhere defined,
  `EnoughInjectives ℬ` makes `RG` everywhere defined, additivity of `F` and of `G` induces the
  functors on bounded below homotopy categories, and `HasDerivedCategory` on each of the three
  categories provides the derived categories in which `t` lives.
  `F.PreservesInjectiveObjects` is used only for the invertibility statements.
* `CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective` ([Stacks, Tag 015M]) takes the
  canonical map `t` and its characterising factorization as hypotheses, so it could not be
  applied before this file: nothing in the development constructed such a `t`.  Nothing here
  carries a Stacks tag — 015M is already tagged at that theorem, and 05T2 is tagged at
  `DerivedFunctorComposition.exists_rightDerived_comparison`, whose abstract triangulated
  setting is where the source states the comparison.

## References

* [Stacks, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2), the comparison transformation
* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M), when it is an isomorphism
* [Stacks, Tag 015E](https://stacks.math.columbia.edu/tag/015E), Leray's acyclicity lemma
-/

@[expose] public section

universe w w' w'' v v' v'' u u' u''

open CategoryTheory Limits

namespace CategoryTheory.Functor

-- As in `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors`:
-- `HomotopyCategory.Plus.hasPointwiseRightDerivedFunctorAt_of_injective` applies to an
-- arbitrary functor out of `K⁺(𝒜)` at an arbitrary object, so instance search reaches for it
-- before the instance that gets the same conclusion from `EnoughInjectives 𝒜`, and then embarks
-- on proving termwise injectivity of an unknown complex.  Everything below mentions
-- `Functor.rightDerivedFunctorPlus`, which needs that conclusion at every object, so the cheap
-- instance is given precedence here.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w''} E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [EnoughInjectives C] [EnoughInjectives D]

/-- **The canonical comparison transformation `t : R(G ∘ F) ⟶ RG ∘ RF`** of
[Stacks, Tag 05T2], in the bounded below derived categories.  It is the descent of
`CategoryTheory.Functor.rightComparisonUnit` along the unit of `R(G ∘ F)`, which exists and is
unique because that unit exhibits `R(G ∘ F)` as a left Kan extension along
`Qh : K⁺(𝒜) ⥤ D⁺(𝒜)`. -/
noncomputable def rightDerivedFunctorPlusComp :
    (F ⋙ G).rightDerivedFunctorPlus ⟶
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  (F ⋙ G).rightDerivedFunctorPlus.rightDerivedDesc (F ⋙ G).rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C) _ (rightComparisonUnit F G)

/-- The factorization that characterises `CategoryTheory.Functor.rightDerivedFunctorPlusComp`:
its composite with the unit of `R(G ∘ F)` is the comparison transformation
`G(F(K)) ⟶ RG(F(K)) ⟶ RG(RF(K))`.  This is the hypothesis `ht` of
`CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective`. -/
lemma rightDerivedFunctorPlusComp_fac :
    (F ⋙ G).rightDerivedFunctorPlusUnit ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedFunctorPlusComp F G) =
      rightComparisonUnit F G :=
  (F ⋙ G).rightDerivedFunctorPlus.rightDerived_fac (F ⋙ G).rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C) _ (rightComparisonUnit F G)

/-- The factorization of `CategoryTheory.Functor.rightDerivedFunctorPlusComp` read at a bounded
below complex `K`: the canonical map at `Qh(K)`, precomposed with the unit of `R(G ∘ F)` at `K`,
is the unit of `RG` at `F(K)` followed by `RG` applied to the unit of `RF` at `K`, up to the
coherence isomorphism identifying the functor induced by `G ∘ F` on `K⁺(𝒜)` with the composite
of the functors induced by `F` and by `G`. -/
lemma rightDerivedFunctorPlusComp_fac_app (K : HomotopyCategory.Plus C) :
    (F ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
        (rightDerivedFunctorPlusComp F G).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K) ≫
        G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) := by
  rw [← rightComparisonUnit_app F G K, ← rightDerivedFunctorPlusComp_fac F G]
  rfl

/-- **The naturality square of the canonical comparison transformation.**  Named so that an
identification of a construction built from `RG ∘ RF` with one built from `R(G ∘ F)` can cite
it; this is what a comparison available only as `Nonempty (… ≅ …)` cannot provide. -/
lemma rightDerivedFunctorPlusComp_naturality {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    (F ⋙ G).rightDerivedFunctorPlus.map f ≫ (rightDerivedFunctorPlusComp F G).app L =
      (rightDerivedFunctorPlusComp F G).app K ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlus.map f) :=
  (rightDerivedFunctorPlusComp F G).naturality f

section PreservesInjectiveObjects

variable [F.PreservesInjectiveObjects]

/-- Every term of `F(K)`, for `K` a bounded below complex of injective objects of `𝒜`, is an
injective object of `ℬ`. -/
private instance injective_mapHomotopyCategoryPlus_obj_as_X
    (K : HomotopyCategory.Plus (InjectiveObject C)) (n : ℤ) :
    Injective ((F.mapHomotopyCategoryPlus.obj
      ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj K)).obj.as.X n) :=
  inferInstanceAs (Injective (F.obj ((InjectiveObject.ι C).obj (K.obj.as.X n))))

/-- **`RF ⋙ RG` is a right derived functor of `K⁺(𝒜) ⥤ D⁺(𝒞)`** when `F` preserves injective
objects, with `CategoryTheory.Functor.rightComparisonUnit` as its unit.  On a bounded below
complex `K` of injective objects of `𝒜` that unit is a composite of three invertible maps: the
coherence isomorphism, the unit of `RG` at `F(K)` — invertible because `F(K)` is again a
bounded below complex of injectives — and the image under `RG` of the unit of `RF` at `K`.
The injective derivability structure of `K⁺(𝒜)` upgrades that to the universal property. -/
instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightComparisonUnit F G) (HomotopyCategory.Plus.quasiIso C) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso _ fun K ↦ by
    dsimp only [rightComparisonUnit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance

/-- **The canonical comparison `t : R(G ∘ F) ⟶ RG ∘ RF` is an isomorphism** when `F` preserves
injective objects: both `R(G ∘ F)` and `RF ⋙ RG` are right derived functors of
`K⁺(𝒜) ⥤ D⁺(𝒞)`, and `t` is the descent of the unit of the second along the unit of the
first. -/
instance isIso_rightDerivedFunctorPlusComp : IsIso (rightDerivedFunctorPlusComp F G) :=
  ((F ⋙ G).rightDerivedFunctorPlus.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    (F ⋙ G).rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) _
    (rightComparisonUnit F G)).1 inferInstance

/-- **Composition of right derived functors on `D⁺`, as an isomorphism of functors.**  For `F`
additive and preserving injective objects and `G` additive, the canonical comparison
transformation of [Stacks, Tag 05T2] is an isomorphism

`R(G ∘ F) ≅ RF ⋙ RG`

of functors `D⁺(𝒜) ⥤ D⁺(𝒞)`.  Its `hom` is
`CategoryTheory.Functor.rightDerivedFunctorPlusComp`, so it is pinned by the factorization
`rightDerivedFunctorPlusComp_fac` through the unit of `R(G ∘ F)` and its naturality square is
`rightDerivedFunctorPlusComp_naturality`. -/
noncomputable def rightDerivedFunctorPlusCompIso :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  asIso (rightDerivedFunctorPlusComp F G)

/-- The forward map of `rightDerivedFunctorPlusCompIso F G` is the canonical comparison
`rightDerivedFunctorPlusComp F G`. -/
@[simp]
lemma rightDerivedFunctorPlusCompIso_hom :
    (rightDerivedFunctorPlusCompIso F G).hom = rightDerivedFunctorPlusComp F G :=
  rfl

/-- The object-level comparison: for `K` in `D⁺(𝒜)`, `R(G ∘ F)(K) ≅ RG(RF(K))`. -/
noncomputable def rightDerivedFunctorPlusCompObjIso (K : DerivedCategory.Plus C) :
    (F ⋙ G).rightDerivedFunctorPlus.obj K ≅
      G.rightDerivedFunctorPlus.obj (F.rightDerivedFunctorPlus.obj K) :=
  (rightDerivedFunctorPlusCompIso F G).app K

/-- A functor preserving injective objects carries every injective object to an object right
acyclic for `G` ([Stacks, Tag 0157]).  This is the forward direction of
`CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective` ([Stacks, Tag 015M]) applied to
the canonical comparison, which this file has just shown to be invertible. -/
lemma rightAcyclic_obj_of_preservesInjectiveObjects (I : C) (hI : Injective I) :
    G.rightAcyclic (F.obj I) :=
  (isIso_iff_rightAcyclic_obj_injective F G (rightDerivedFunctorPlusComp F G)
    (rightDerivedFunctorPlusComp_fac F G)).1 inferInstance I hI

end PreservesInjectiveObjects

end CategoryTheory.Functor

end
