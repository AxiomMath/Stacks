module

public import StacksFrontier.Topology.Simplicial.DiagramSlice
public import StacksFrontier.Topology.Simplicial.Site

/-!
# The slice of the total site of a simplicial space

For a simplicial topological space `Y` the total site of Stacks 09VL is
`Stacks.Topology.Simplicial.SimplicialOpen Y`. Its slice at an object `(n, W)` is *not* the site
of opens of `W`: an object of the slice is a simplex map `φ : m ⟶ n` together with an open of
`(Y φ)⁻¹W`, so the slice is the total site of the diagram of spaces over `(n, W)`, indexed by the
category of simplicial degrees over `n`.

This file transports the comparison of
`Stacks.Topology.Simplicial.DiagramOpen.sliceEquivalence` to that site. The transport is along
the identification of the total site of a simplicial space with the total site of the diagram it
is — the same objects and the same arrows, under different names — which is an equivalence of
sites, and along the induced equivalence of slices.

## Main definitions

* `Stacks.Topology.Simplicial.SimplicialOpen.levelHom`: the levelwise arrow into an object of
  the total site from a smaller open in the same degree.
* `Stacks.Topology.Simplicial.toDiagramOpen` and `Stacks.Topology.Simplicial.simplicialOpenEquiv`:
  the total site of a simplicial space as the total site of a diagram of spaces.
* `Stacks.Topology.Simplicial.SimplicialOpen.sliceEquivalence`: the slice of the total site at
  `(n, W)` as the total site of the over-diagram.
* `Stacks.Topology.Simplicial.SimplicialOpen.sheafSliceEquivalence`: the induced equivalence of
  sheaf categories.

## Main results

* `Stacks.Topology.Simplicial.SimplicialOpen.mem_grothendieckTopology_iff`: the covering sieves
  of the total site of a simplicial space, pointwise.
* `Stacks.Topology.Simplicial.toDiagramOpen_isDenseSubsite`: the identification of the two total
  sites is an equivalence of sites.
* `CategoryTheory.Functor.overPost_isDenseSubsite`: an equivalence of sites induces one on the
  slices at corresponding objects.
* `Stacks.Topology.Simplicial.SimplicialOpen.sliceEquivalence_functor_isDenseSubsite`: the slice
  comparison is an equivalence of sites.

## Implementation notes

`SimplicialOpen` and `DiagramOpen` are two structures with the same fields, so the comparison
functors are the identity on data and the unit and counit are `Iso.refl`; the content of
`toDiagramOpen_isDenseSubsite` is that the two covering notions agree, which both pointwise
characterizations reduce to a statement with no content. The reason the comparison is needed at
all is that `SimplicialOpen` is the structure the development's simplicial sites are built on and
`DiagramOpen` is the one that admits the over-diagram, whose index category is a slice of the
simplex category rather than the simplex category itself.

The slice comparison is the composite of the equivalence of slices induced by that
identification with the generic slice comparison. Its `IsDenseSubsite` instance is assembled
from cocontinuity of the two factors in both directions rather than from
`functorPushforward_mem_iff` of the two: the sieve pushed forward along a composite is only
*propositionally* equal to the iterated pushforward, and rewriting by that equality is not
type-correct, the covering sieves of the two readings living over objects that are equal only
definitionally. Cocontinuity composes with no such obstruction, and
`CategoryTheory.Equivalence.isDenseSubsite_functor_of_isCocontinuous` turns cocontinuity in both
directions back into an equivalence of sites.

## References

* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
* [Stacks Project, Tag 00XZ](https://stacks.math.columbia.edu/tag/00XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- **An equivalence of sites induces an equivalence of slices.** For a functor `F` that is an
equivalence of sites, the induced functor on slices at `Z` and `F.obj Z` is an equivalence of the
slice sites. -/
instance overPost_isDenseSubsite (F : C ⥤ D) [F.IsDenseSubsite J K] [F.IsEquivalence]
    (Z : C) : (Over.post (X := Z) F).IsDenseSubsite (J.over Z) (K.over (F.obj Z)) where
  functorPushforward_mem_iff {V S} := by
    rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_functorPushforward_post]
    exact F.functorPushforward_mem_iff J K

/-- For an equivalence `e` whose functor is an equivalence of sites, the functor of the induced
equivalence of slices at `Z` and `e.functor.obj Z` is an equivalence of the slice sites. -/
instance overPostEquiv_functor_isDenseSubsite (e : C ≌ D) [e.functor.IsDenseSubsite J K]
    (Z : C) :
    (Over.postEquiv (X := Z) e).functor.IsDenseSubsite (J.over Z)
      (K.over (e.functor.obj Z)) :=
  overPost_isDenseSubsite J K e.functor Z

/-- The inverse of `(Over.postEquiv e).symm`, which is the functor of `Over.postEquiv e`, is an
equivalence of the slice sites. -/
instance (e : C ≌ D) [e.functor.IsDenseSubsite J K] (Z : C) :
    (Over.postEquiv (X := Z) e).symm.inverse.IsDenseSubsite (J.over Z)
      (K.over (e.functor.obj Z)) :=
  inferInstanceAs ((Over.postEquiv (X := Z) e).functor.IsDenseSubsite ..)

/-- **An equivalence of sites induces an equivalence of slices, inverse direction.** -/
instance overPostEquiv_inverse_isDenseSubsite (e : C ≌ D) [e.functor.IsDenseSubsite J K]
    (Z : C) :
    (Over.postEquiv (X := Z) e).inverse.IsDenseSubsite (K.over (e.functor.obj Z)) (J.over Z) :=
  inferInstanceAs ((Over.postEquiv (X := Z) e).symm.functor.IsDenseSubsite ..)

end CategoryTheory.Functor

namespace Stacks.Topology.Simplicial

variable {Y : SimplicialObject TopCat.{u}}

namespace SimplicialOpen

/-- The levelwise arrow into `U` from an open subset of the space in the degree of `U` that is
contained in the open of `U`. -/
def levelHom (U : SimplicialOpen Y) {V : Opens (Y.obj U.degree)} (h : V ≤ U.toOpens) :
    (⟨U.degree, V⟩ : SimplicialOpen Y) ⟶ U where
  base := 𝟙 _
  le := by simpa using h

/-- The simplex map underlying `levelHom U h` is the identity of the degree of `U`. -/
@[simp]
theorem levelHom_base (U : SimplicialOpen Y) {V : Opens (Y.obj U.degree)} (h : V ≤ U.toOpens) :
    (levelHom U h).base = 𝟙 _ := rfl

/-- **The covering sieves of the total site of a simplicial space, pointwise.** A sieve on
`(n, W)` is covering exactly when every point of `W` lies in some open of `X_n` contained in `W`
whose levelwise arrow into `(n, W)` belongs to the sieve. -/
theorem mem_grothendieckTopology_iff {U : SimplicialOpen Y} (S : Sieve U) :
    S ∈ grothendieckTopology Y U ↔
      ∀ x ∈ U.toOpens, ∃ (V : Opens (Y.obj U.degree)) (h : V ≤ U.toOpens),
        S.arrows (levelHom U h) ∧ x ∈ V := by
  rw [mem_grothendieckTopology]
  constructor
  · rintro ⟨R, hR, hRS⟩ x hx
    obtain ⟨V', f, hRf, y, hy, hyx⟩ := hR.2 x hx
    obtain ⟨e, he⟩ := hR.1 V' f hRf
    rcases V' with ⟨d, V₀⟩
    change d = U.degree at e
    cases e
    simp only [eqToHom_refl] at he
    have hle : V₀ ≤ U.toOpens := by simpa [he] using Hom.le f
    have hfe : f = levelHom U hle := Hom.ext _ _ (by simp [he])
    refine ⟨V₀, hle, ?_, ?_⟩
    · rw [← hfe]
      exact hRS _ _ hRf
    · have hid : Y.map f.base y = y := by
        rw [he]
        exact ConcreteCategory.congr_hom (Y.map_id _) y
      rwa [← hyx, hid]
  · intro H
    refine ⟨fun {_} g ↦ S.arrows g ∧ IsLevelwise g, ⟨fun _ _ hg ↦ hg.2, fun x hx ↦ ?_⟩,
      fun _ _ hg ↦ hg.1⟩
    obtain ⟨V, h, hS, hxV⟩ := H x hx
    exact ⟨⟨U.degree, V⟩, levelHom U h, ⟨hS, ⟨rfl, rfl⟩⟩, x, hxV,
      ConcreteCategory.congr_hom (Y.map_id _) x⟩

end SimplicialOpen

/-- The total site of a simplicial space, read as the total site of the diagram of spaces it
is. -/
def toDiagramOpen (Y : SimplicialObject TopCat.{u}) :
    SimplicialOpen Y ⥤ DiagramOpen Y where
  obj U := ⟨U.degree, U.toOpens⟩
  map f := ⟨SimplicialOpen.Hom.base f, SimplicialOpen.Hom.le f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inverse reading: the total site of a diagram of spaces indexed by the simplex category is
the total site of that simplicial space. -/
def ofDiagramOpen (Y : SimplicialObject TopCat.{u}) :
    DiagramOpen Y ⥤ SimplicialOpen Y where
  obj P := ⟨P.index, P.toOpens⟩
  map f := ⟨DiagramOpen.Hom.base f, DiagramOpen.Hom.le f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The total site of a simplicial space and the total site of the diagram it is are the same
category. -/
def simplicialOpenEquiv (Y : SimplicialObject TopCat.{u}) :
    SimplicialOpen Y ≌ DiagramOpen Y where
  functor := toDiagramOpen Y
  inverse := ofDiagramOpen Y
  unitIso := Iso.refl (𝟭 (SimplicialOpen Y))
  counitIso := Iso.refl (𝟭 (DiagramOpen Y))
  functor_unitIso_comp _ := Category.id_comp _

/-- The functor `toDiagramOpen Y` is an equivalence of categories. -/
instance toDiagramOpen_isEquivalence (Y : SimplicialObject TopCat.{u}) :
    (toDiagramOpen Y).IsEquivalence :=
  Equivalence.isEquivalence_functor (simplicialOpenEquiv Y)

/-- The functor `ofDiagramOpen Y` is an equivalence of categories. -/
instance ofDiagramOpen_isEquivalence (Y : SimplicialObject TopCat.{u}) :
    (ofDiagramOpen Y).IsEquivalence :=
  Equivalence.isEquivalence_inverse (simplicialOpenEquiv Y)

/-- **The two readings of the total site of a simplicial space agree as sites.** -/
instance toDiagramOpen_isDenseSubsite :
    (toDiagramOpen Y).IsDenseSubsite (SimplicialOpen.grothendieckTopology Y)
      (DiagramOpen.grothendieckTopology Y) where
  functorPushforward_mem_iff {U S} := by
    rw [DiagramOpen.mem_grothendieckTopology_iff, SimplicialOpen.mem_grothendieckTopology_iff]
    dsimp only [toDiagramOpen]
    constructor
    · intro H x hx
      obtain ⟨V, hV, ⟨T, a, b, hSa, hcomp⟩, hxV⟩ := H x hx
      refine ⟨V, hV, ?_, hxV⟩
      have hfac : SimplicialOpen.levelHom U hV = (ofDiagramOpen Y).map b ≫ a :=
        SimplicialOpen.Hom.ext _ _ (congrArg DiagramOpen.Hom.base hcomp)
      rw [hfac]
      exact S.downward_closed hSa _
    · intro H x hx
      obtain ⟨V, hV, hS, hxV⟩ := H x hx
      exact ⟨V, hV, ⟨⟨U.degree, V⟩, SimplicialOpen.levelHom U hV, 𝟙 _, hS,
        DiagramOpen.Hom.ext _ _ (Category.id_comp _).symm⟩, hxV⟩

/-- The functor of `simplicialOpenEquiv Y` is an equivalence of sites. -/
instance simplicialOpenEquiv_functor_isDenseSubsite :
    (simplicialOpenEquiv Y).functor.IsDenseSubsite (SimplicialOpen.grothendieckTopology Y)
      (DiagramOpen.grothendieckTopology Y) :=
  toDiagramOpen_isDenseSubsite

/-- The inverse of `(simplicialOpenEquiv Y).symm`, which is the functor of
`simplicialOpenEquiv Y`, is an equivalence of sites. -/
instance : (simplicialOpenEquiv Y).symm.inverse.IsDenseSubsite
    (SimplicialOpen.grothendieckTopology Y) (DiagramOpen.grothendieckTopology Y) :=
  inferInstanceAs ((simplicialOpenEquiv Y).functor.IsDenseSubsite ..)

/-- The inverse of `simplicialOpenEquiv Y` is an equivalence of sites. -/
instance ofDiagramOpen_isDenseSubsite :
    (simplicialOpenEquiv Y).inverse.IsDenseSubsite (DiagramOpen.grothendieckTopology Y)
      (SimplicialOpen.grothendieckTopology Y) :=
  inferInstanceAs ((simplicialOpenEquiv Y).symm.functor.IsDenseSubsite ..)

namespace SimplicialOpen

variable (Y) (U : SimplicialOpen Y)

/-- **The slice of the total site of a simplicial space is the total site of the
over-diagram.** The slice at `(n, W)` has as objects a simplex map `φ : m ⟶ n` together with an
open of the space `(Y φ)⁻¹W`, which is the degree-`φ` space of the diagram over `(n, W)`. -/
def sliceEquivalence : Over U ≌ DiagramOpen (overSpace Y ((simplicialOpenEquiv Y).functor.obj U)) :=
  (Over.postEquiv (X := U) (simplicialOpenEquiv Y)).trans
    (DiagramOpen.sliceEquivalence Y ((simplicialOpenEquiv Y).functor.obj U))

/-- **The slice comparison is an equivalence of sites.** The slice topology on the slice of the
total site at `(n, W)` corresponds to the topology of levelwise open coverings on the total site
of the over-diagram. -/
instance sliceEquivalence_functor_isDenseSubsite :
    (sliceEquivalence Y U).functor.IsDenseSubsite ((grothendieckTopology Y).over U)
      (DiagramOpen.grothendieckTopology (overSpace Y ((simplicialOpenEquiv Y).functor.obj U))) := by
  have h1 : (sliceEquivalence Y U).functor.IsCocontinuous ((grothendieckTopology Y).over U)
      (DiagramOpen.grothendieckTopology (overSpace Y ((simplicialOpenEquiv Y).functor.obj U))) :=
    CategoryTheory.isCocontinuous_comp
      (G := Over.post (X := U) (simplicialOpenEquiv Y).functor)
      (G' := (DiagramOpen.sliceEquivalence Y ((simplicialOpenEquiv Y).functor.obj U)).functor)
      (J := (grothendieckTopology Y).over U)
      (K := (DiagramOpen.grothendieckTopology Y).over ((simplicialOpenEquiv Y).functor.obj U))
      (L := DiagramOpen.grothendieckTopology (overSpace Y ((simplicialOpenEquiv Y).functor.obj U)))
  have h2 : (sliceEquivalence Y U).inverse.IsCocontinuous
      (DiagramOpen.grothendieckTopology (overSpace Y ((simplicialOpenEquiv Y).functor.obj U)))
      ((grothendieckTopology Y).over U) :=
    CategoryTheory.isCocontinuous_comp
      (G := (DiagramOpen.sliceEquivalence Y ((simplicialOpenEquiv Y).functor.obj U)).inverse)
      (G' := (Over.postEquiv (X := U) (simplicialOpenEquiv Y)).inverse)
      (J := DiagramOpen.grothendieckTopology (overSpace Y ((simplicialOpenEquiv Y).functor.obj U)))
      (K := (DiagramOpen.grothendieckTopology Y).over ((simplicialOpenEquiv Y).functor.obj U))
      (L := (grothendieckTopology Y).over U)
  exact Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ (sliceEquivalence Y U)

/-- The inverse of `(sliceEquivalence Y U).symm`, which is the functor of
`sliceEquivalence Y U`, is an equivalence of sites. -/
instance : (sliceEquivalence Y U).symm.inverse.IsDenseSubsite
    ((grothendieckTopology Y).over U)
    (DiagramOpen.grothendieckTopology (overSpace Y ((simplicialOpenEquiv Y).functor.obj U))) :=
  inferInstanceAs ((sliceEquivalence Y U).functor.IsDenseSubsite ..)

/-- The inverse of `sliceEquivalence Y U` is an equivalence of sites from the total site of the
over-diagram to the slice of the total site at `U`. -/
instance sliceInverse_isDenseSubsite :
    (sliceEquivalence Y U).inverse.IsDenseSubsite
      (DiagramOpen.grothendieckTopology (overSpace Y ((simplicialOpenEquiv Y).functor.obj U)))
      ((grothendieckTopology Y).over U) :=
  inferInstanceAs ((sliceEquivalence Y U).symm.functor.IsDenseSubsite ..)

/-- **Sheaves on the slice of the total site of a simplicial space are sheaves on the total site
of the over-diagram.** -/
def sheafSliceEquivalence (B : Type w) [Category.{v} B] :
    Sheaf ((grothendieckTopology Y).over U) B ≌
      Sheaf (DiagramOpen.grothendieckTopology
        (overSpace Y ((simplicialOpenEquiv Y).functor.obj U))) B :=
  (sliceEquivalence Y U).sheafCongr _ _ B

end SimplicialOpen

end Stacks.Topology.Simplicial

end
