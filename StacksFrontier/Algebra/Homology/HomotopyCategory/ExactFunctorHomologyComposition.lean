module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor

/-!
# The homology comparison of an exact functor is compatible with composition

An exact additive functor `F : 𝒜 ⥤ ℬ` between abelian categories commutes with homology, and the
comparison is recorded in the development twice: on a short complex as Mathlib's
`CategoryTheory.ShortComplex.mapHomologyIso`, and on cochain complexes as
`Stacks.Homology.exactHomologyIso` and `Stacks.DerivedFunctor.complexHomologyIso`. This file
proves that all three comparisons are compatible with *composition* of exact functors: for
`F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` the comparison for `F ⋙ G` is the comparison for `G`, followed by
`G` applied to the comparison for `F`.

This is the base case of the corresponding statement one and two levels up — for the comparison
on the derived category, and for the comparison between the right derived functor of an exact
functor and homology — since both of those comparisons are obtained from the comparison on
complexes by the universal property of a localization, and a natural transformation out of a
localization is determined by its restriction along the localization functor.

## Main results

* `Stacks.Homology.mapHomologyIso_comp_hom`: **the composition law on a short complex.**
* `Stacks.Homology.exactHomologyIso_comp_hom_app` and
  `Stacks.DerivedFunctor.complexHomologyIso_comp_hom_app`: **the composition law on cochain
  complexes**, for the two comparisons the development carries.
* `Stacks.DerivedFunctor.complexHomologyIso_hom_app`: the component of
  `Stacks.DerivedFunctor.complexHomologyIso` is the short-complex comparison in the degree
  concerned, the chain of associators it is assembled from contributing only identities.

## Implementation notes

*Why the proofs are in term mode.* The two sides of each statement are stated at the two
spellings `S.map (F ⋙ G)` and `(S.map F).map G` of one short complex, and at the two spellings
`(F ⋙ G).mapHomologicalComplex c` and `F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c`
of one functor. These are definitionally equal but not syntactically equal, so `rw` and `simp`
cannot rewrite across them: the motive of such a rewrite is type-correct only at default
transparency, and both tactics match at `instances` transparency and silently find nothing.
Every step is therefore an explicit `CategoryTheory.Category.assoc`,
`CategoryTheory.Category.id_comp` or `congrArg`, composed with `Eq.trans`, which are checked up
to definitional equality.

For the same reason the identity morphisms in the auxiliary left homology map data below are
written with their object given explicitly: elaborating `𝟙 _` against the expected type
`(h.map (F ⋙ G)).K ⟶ ((h.map F).map G).K` postpones a definitional equality that then runs out
of heartbeats, whereas the equality itself is immediate once the object is known.

*Why a left homology map data appears at all.* The comparison
`CategoryTheory.ShortComplex.mapHomologyIso` is the canonical isomorphism attached to the image
of the chosen left homology data of `S`, and the composition law is the statement that the two
images of that data — under `F ⋙ G`, and under `G` of its image under `F` — induce the same
isomorphism. They are left homology data of the same short complex with the same underlying
objects and morphisms, so the identity is a map data between them, and the uniqueness of the
induced map on homology does the rest.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Homology

section ShortComplex

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Abelian A] [Abelian B] [Abelian C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The homology comparison of an exact functor is compatible with composition, on a short
complex.** The comparison `(S.map (F ⋙ G)).homology ≅ (F ⋙ G).obj S.homology` is the comparison
for `G` at `S.map F`, followed by `G` applied to the comparison for `F` at `S`. -/
theorem mapHomologyIso_comp_hom (S : ShortComplex A) :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ G)).hom := by
  let ψ : ShortComplex.LeftHomologyMapData (𝟙 (S.map (F ⋙ G)))
      (S.homologyData.left.map (F ⋙ G)) ((S.homologyData.left.map F).map G) :=
    { φK := 𝟙 (S.homologyData.left.map (F ⋙ G)).K
      φH := 𝟙 (S.homologyData.left.map (F ⋙ G)).H
      commi := (Category.id_comp _).trans (Category.comp_id _).symm
      commf' := by
        simp only [ShortComplex.LeftHomologyData.map_f', ShortComplex.id_τ₁]
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      commπ := (Category.comp_id _).trans (Category.id_comp _).symm }
  have hψ : ψ.φH = 𝟙 (S.homologyData.left.map (F ⋙ G)).H := rfl
  have hmap := ψ.leftHomologyMap'_eq
  rw [hψ] at hmap
  have hnat := ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality
    (𝟙 (S.map (F ⋙ G))) (S.homologyData.left.map (F ⋙ G))
    ((S.homologyData.left.map F).map G)
  rw [hmap, ShortComplex.homologyMap_id] at hnat
  have hiso : (S.homologyData.left.map (F ⋙ G)).homologyIso.hom =
      ((S.homologyData.left.map F).map G).homologyIso.hom :=
    ((Category.comp_id _).symm.trans hnat).trans (Category.id_comp _)
  have hmid : ((S.map F).mapHomologyIso G).hom =
      ((S.homologyData.left.map F).map G).homologyIso.hom ≫
        G.map (S.homologyData.left.map F).homologyIso.inv := by
    rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq
      (hl := S.homologyData.left.map F) (F := G)]
    rfl
  have hcancel : G.map (S.homologyData.left.map F).homologyIso.inv ≫
      G.map (S.homologyData.left.map F).homologyIso.hom =
      𝟙 (G.obj (S.homologyData.left.map F).H) :=
    Iso.inv_hom_id (G.mapIso (S.homologyData.left.map F).homologyIso)
  refine (congrArg (fun t => t ≫ G.map (S.mapHomologyIso F).hom) hmid).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg
    (fun t => ((S.homologyData.left.map F).map G).homologyIso.hom ≫ t) hcancel).trans ?_
  exact (Category.comp_id _).trans hiso.symm

/-- **The homology comparison of an exact functor on cochain complexes is compatible with
composition**, for `Stacks.Homology.exactHomologyIso`. -/
theorem exactHomologyIso_comp_hom_app (n : ℤ) (K : CochainComplex A ℤ) :
    (exactHomologyIso G n).hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        G.map ((exactHomologyIso F n).hom.app K) =
      (exactHomologyIso (F ⋙ G) n).hom.app K :=
  mapHomologyIso_comp_hom F G (K.sc n)

end ShortComplex

end Stacks.Homology

namespace Stacks.DerivedFunctor

section Complexes

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- **The component of `Stacks.DerivedFunctor.complexHomologyIso` is the comparison on the short
complex in the degree concerned.** The chain of associators and reflexive isomorphisms the
comparison is assembled from contributes only identity morphisms. -/
theorem complexHomologyIso_hom_app (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (K : HomologicalComplex A c) :
    (complexHomologyIso F c i).hom.app K = ((K.sc i).mapHomologyIso F).hom := by
  have expand : (complexHomologyIso F c i).hom.app K =
      𝟙 _ ≫ 𝟙 _ ≫ (ShortComplex.homologyFunctor B).map (𝟙 _) ≫ 𝟙 _ ≫
        ((K.sc i).mapHomologyIso F).hom ≫ 𝟙 _ ≫ F.map (𝟙 _) := rfl
  rw [expand]
  simp only [CategoryTheory.Functor.map_id]
  refine (Category.id_comp _).trans ((Category.id_comp _).trans
    ((Category.id_comp _).trans ((Category.id_comp _).trans ?_)))
  refine (congrArg (fun t => ((K.sc i).mapHomologyIso F).hom ≫ t)
    (Category.id_comp (𝟙 (F.obj (K.sc i).homology)))).trans ?_
  exact Category.comp_id _

variable {C : Type u₃} [Category.{v₃} C] [Abelian C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The homology comparison of an exact functor on complexes is compatible with
composition**, for `Stacks.DerivedFunctor.complexHomologyIso`. -/
theorem complexHomologyIso_comp_hom_app (K : HomologicalComplex A c) :
    (complexHomologyIso G c i).hom.app ((F.mapHomologicalComplex c).obj K) ≫
        G.map ((complexHomologyIso F c i).hom.app K) =
      (complexHomologyIso (F ⋙ G) c i).hom.app K := by
  rw [complexHomologyIso_hom_app, complexHomologyIso_hom_app, complexHomologyIso_hom_app]
  exact Stacks.Homology.mapHomologyIso_comp_hom F G (K.sc i)

end Complexes

end Stacks.DerivedFunctor

end
