module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.CategoryTheory.Sites.Over

/-!
# The site associated to a semi-representable object

A *semi-representable object* of a category `C` is a formal coproduct `K = ⨿ i, K.obj i` of
objects of `C`, so that the category `SR(C)` of semi-representable objects is
`CategoryTheory.FormalCoproduct C`. If `C` carries a Grothendieck topology `J`, the site
localized at `K` is the disjoint union `∐ i, C / K.obj i` of the slice categories over the
components of `K`, equipped with the topology whose restriction to each component is the
localized topology `J.over (K.obj i)`.

A morphism `f : K ⟶ L` of semi-representable objects consists of a map `f.f` of index types and,
for each `i`, an arrow `f.φ i : K.obj i ⟶ L.obj (f.f i)`. It induces a functor between the two
localized sites which on the `i`-th component is the relocalization functor
`Over.map (f.φ i)` followed by the inclusion of the component indexed by `f.f i`. The data of a
site, two semi-representable objects and a morphism between them is packaged as
`LocalizationSites`, which also records the localization functor to `C` itself.

## Main definitions

* `CategoryTheory.SemiRepresentable.ComponentOver`: the disjoint union of the slice categories
  over the components of a formal coproduct.
* `CategoryTheory.SemiRepresentable.componentwiseTopology`: the topology on that disjoint union
  whose restriction to every component is the localized topology.
* `CategoryTheory.SemiRepresentable.LocalizationSites`: a site, two semi-representable objects
  and a morphism between them.
* `CategoryTheory.SemiRepresentable.LocalizationSites.localizationFunctor`: the componentwise
  localization functor `C / K ⥤ C`.
* `CategoryTheory.SemiRepresentable.LocalizationSites.relocalizationFunctor`: the componentwise
  relocalization functor `C / K ⥤ C / L` induced by the morphism.

## Main results

* `CategoryTheory.SemiRepresentable.mem_componentwiseTopology_iff`: the characterization of the
  covering sieves of the componentwise topology.
* `CategoryTheory.SemiRepresentable.LocalizationSites.localizationFunctorCompIso` and
  `CategoryTheory.SemiRepresentable.LocalizationSites.relocalizationFunctorCompIso`: the
  canonical identifications of the restrictions of the two functors to a single component.

## References

* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SemiRepresentable

/-- The disjoint union `∐ i, C / Kᵢ` of the slice categories over the components of a formal
coproduct `K`. -/
abbrev ComponentOver {C : Type u} [Category.{v} C]
    (K : FormalCoproduct.{w} C) :=
  Σ i : K.I, Over (K.obj i)

/-- The componentwise topology on `∐ i, C / Kᵢ`, obtained by putting the localized topology
`J.over (K.obj i)` on its `i`-th component. -/
def componentwiseTopology {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) :
    GrothendieckTopology (Σ i : K.I, Over (K.obj i)) where
  sieves := fun X => match X with
    | ⟨i, X⟩ => {S | S.functorPullback
        (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i) ∈
          J.over (K.obj i) X}
  top_mem' := by
    rintro ⟨i, X⟩
    have h : (⊤ : Sieve (⟨i, X⟩ : Σ i : K.I, Over (K.obj i))).functorPullback
        (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i) = ⊤ := by
      ext Y f
      rfl
    change (⊤ : Sieve (⟨i, X⟩ : Σ i : K.I, Over (K.obj i))).functorPullback
      (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i) ∈
        J.over (K.obj i) X
    rw [h]
    exact (J.over (K.obj i)).top_mem X
  pullback_stable' := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ S ⟨f⟩ hS
    exact (J.over (K.obj i)).pullback_stable f hS
  transitive' := by
    rintro ⟨i, X⟩ S hS R hR
    exact (J.over (K.obj i)).transitive hS _ fun Y f hf =>
      hR (f := CategoryTheory.Sigma.SigmaHom.mk (C := fun i : K.I => Over (K.obj i)) f) hf

/-- A sieve on an object in the `i`-th component is covering for the componentwise topology
exactly when its restriction to that component is covering for the localized topology. -/
@[simp]
lemma mem_componentwiseTopology_iff {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C) (i : K.I)
    (X : Over (K.obj i)) (S : Sieve (⟨i, X⟩ : Σ i : K.I, Over (K.obj i))) :
    S ∈ componentwiseTopology J K (⟨i, X⟩ : Σ i : K.I, Over (K.obj i)) ↔
      S.functorPullback
        (CategoryTheory.Sigma.incl (C := fun i : K.I => Over (K.obj i)) i) ∈
          J.over (K.obj i) X :=
  Iff.rfl

/-- The data of a site `(C, J)`, two semi-representable objects of `C` and a morphism between
them. -/
structure LocalizationSites (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  /-- The source semi-representable object. -/
  K : FormalCoproduct.{w} C
  /-- The target semi-representable object. -/
  L : FormalCoproduct.{w} C
  /-- The morphism of semi-representable objects. -/
  f : K ⟶ L

namespace LocalizationSites

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (S : LocalizationSites.{w} C J)

/-- The site category denoted `C / K`. -/
abbrev source := ComponentOver S.K

/-- The site category denoted `C / L`. -/
abbrev target := ComponentOver S.L

/-- The componentwise topology on `C / K`. -/
def sourceTopology : GrothendieckTopology S.source :=
  componentwiseTopology J S.K

/-- The componentwise topology on `C / L`. -/
def targetTopology : GrothendieckTopology S.target :=
  componentwiseTopology J S.L

/-- The functor `j : C / K ⥤ C`, equal to the localization functor on each component. -/
def localizationFunctor : S.source ⥤ C :=
  CategoryTheory.Sigma.desc fun i => Over.forget (S.K.obj i)

/-- The canonical identification of the restriction of `localizationFunctor` to a component with
the localization functor of that component. -/
def localizationFunctorCompIso (i : S.K.I) :
    CategoryTheory.Sigma.incl (C := fun i : S.K.I => Over (S.K.obj i)) i ⋙
      S.localizationFunctor ≅ Over.forget (S.K.obj i) :=
  CategoryTheory.Sigma.inclDesc _ i

/-- The functor `v : C / K ⥤ C / L`; on the component over `K.obj i` it is the relocalization
functor associated to `S.f.φ i : K.obj i ⟶ L.obj (S.f.f i)`. -/
def relocalizationFunctor : S.source ⥤ S.target :=
  CategoryTheory.Sigma.desc fun i =>
    Over.map (S.f.φ i) ⋙
      CategoryTheory.Sigma.incl (C := fun j : S.L.I => Over (S.L.obj j)) (S.f.f i)

/-- The canonical identification of the restriction of `relocalizationFunctor` to a component
with the corresponding relocalization functor followed by inclusion of the target component. -/
def relocalizationFunctorCompIso (i : S.K.I) :
    CategoryTheory.Sigma.incl (C := fun i : S.K.I => Over (S.K.obj i)) i ⋙
      S.relocalizationFunctor ≅
      Over.map (S.f.φ i) ⋙
        CategoryTheory.Sigma.incl (C := fun j : S.L.I => Over (S.L.obj j)) (S.f.f i) :=
  CategoryTheory.Sigma.inclDesc _ i

end LocalizationSites

end CategoryTheory.SemiRepresentable

end
