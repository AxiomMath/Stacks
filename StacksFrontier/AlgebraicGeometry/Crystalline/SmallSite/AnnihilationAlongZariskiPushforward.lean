module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCoverTowerAnnihilation

/-!
# Transporting the annihilation of [Stacks, Tag 07Q9] along a derived direct image

`...SmallSite.Annihilation07Q9 S q α` says that the cone of a morphism `α` of `D⁺(Ab(X_Zar))` has
all its cohomology sheaves annihilated by `q`.  This file transports such statements along a
triangulated functor `G`, in particular along `Rf_{Zar, *}`
(`...SmallSite.derivedZariskiPushforwardFunctor`), in two ways.

1. `ObjectAnnihilation07Q9 S q α` asks that `q • 𝟙` vanish on the cone *as an object* of
   `D⁺(Ab(X_Zar))`.  It transports along any additive triangulated functor
   (`objectAnnihilation07Q9_map`) and implies the cohomology-sheaf form
   (`annihilation07Q9_of_objectAnnihilation07Q9`).
2. If `ℋ^j(G K)` is identified with `R(ℋ^j K)` for an additive functor `R` in every degree `j`
   and at every object `K`, the cohomology-sheaf form transports along `G`
   (`annihilation07Q9_map_of_homologyIso`).

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `ObjectAnnihilation07Q9` — the object-level reading of [Stacks, Tag 07Q9]'s conclusion: every
  cone of `α` is killed by `q` as an object of `D⁺(Ab(X_Zar))`.

## Main results

* `annihilation07Q9_of_objectAnnihilation07Q9` — it implies the cohomology-sheaf reading
  `...SmallSite.Annihilation07Q9`.
* `objectAnnihilation07Q9_map` and `annihilation07Q9_map_of_objectAnnihilation07Q9` — the
  object-level form transports along any additive triangulated functor, and gives
  `Annihilation07Q9` for the image.
* `annihilation07Q9_map_of_homologyIso` — the cohomology-sheaf form transports along a
  triangulated functor that is identified degreewise with an additive functor on cohomology.
* `annihilation07Q9_derivedZariskiPushforward_map_of_object` and
  `annihilation07Q9_derivedZariskiPushforward_map_of_homologyIso` — the two transports at
  `G = Rf_{Zar, *}`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159), that a right derived
  functor is an exact functor of triangulated categories
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  TopologicalSpace Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  Functor.isTriangulated_rightDerivedFunctorPlus

/-- An additive functor preserves the vanishing of `q • 𝟙`. -/
private theorem smul_id_map_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {X : C} {q : ℤ} (h : q • 𝟙 X = 0) :
    q • 𝟙 (F.obj X) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, h, Functor.map_zero]

/-! ### The object-level reading of the conclusion -/

section Object

variable (S : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- **The object-level reading of [Stacks, Tag 07Q9]'s conclusion for a morphism `α` of
`D⁺(Ab(X_Zar))`**: in every distinguished triangle `A ⟶ B ⟶ E ⟶ A⟦1⟧` on `α`, the scalar `q`
annihilates the identity of `E` itself, not merely the identities of its cohomology sheaves. -/
def ObjectAnnihilation07Q9 (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})}
    (α : A ⟶ B) : Prop :=
  ∀ (E : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}))
    (v : B ⟶ E) (wE : E ⟶ A⟦(1 : ℤ)⟧),
    Triangle.mk α v wE ∈
        distTriang (DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})) →
      (q : ℤ) • 𝟙 E = 0

/-- **The object-level reading implies the cohomology-sheaf reading.** -/
theorem annihilation07Q9_of_objectAnnihilation07Q9 (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} {α : A ⟶ B}
    (h : ObjectAnnihilation07Q9 S q α) :
    Annihilation07Q9 S q α := by
  intro E v wE hT j
  exact smul_id_map_eq_zero _ (h E v wE hT)

end Object

/-! ### Transporting the annihilation along a functor -/

section Transport

variable (S S' : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

/-- Every distinguished triangle on `G.map α` has third vertex isomorphic to `G` of the third
vertex of a distinguished triangle on `α`. -/
private theorem exists_cone_iso_map {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] {A B : C} (α : A ⟶ B) (G : C ⥤ D) [G.Additive]
    [G.CommShift ℤ] [G.IsTriangulated] {E' : D} {v' : G.obj B ⟶ E'}
    {w' : E' ⟶ (G.obj A)⟦(1 : ℤ)⟧} (hT' : Triangle.mk (G.map α) v' w' ∈ distTriang D) :
    ∃ (E₀ : C) (v₀ : B ⟶ E₀) (w₀ : E₀ ⟶ A⟦(1 : ℤ)⟧), Triangle.mk α v₀ w₀ ∈ distTriang C ∧
      Nonempty (E' ≅ G.obj E₀) := by
  obtain ⟨E₀, v₀, w₀, hT₀⟩ := distinguished_cocone_triangle α
  have hdist : Triangle.mk (G.map α) (G.map v₀)
        (G.map w₀ ≫ (G.commShiftIso (1 : ℤ)).hom.app A) ∈
      distTriang D :=
    G.map_distinguished (Triangle.mk α v₀ w₀) hT₀
  exact ⟨E₀, v₀, w₀, hT₀, ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ (Triangle.mk (G.map α) v' w') _
    hT' hdist (Iso.refl _) (Iso.refl _) (by simp))⟩⟩

/-- **The object-level annihilation transports along any additive triangulated functor.** -/
theorem objectAnnihilation07Q9_map (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} {α : A ⟶ B}
    (G : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))
    [G.Additive] [G.CommShift ℤ] [G.IsTriangulated]
    (h : ObjectAnnihilation07Q9 S q α) :
    ObjectAnnihilation07Q9 S' q (G.map α) := by
  intro E' v' w' hT'
  obtain ⟨E₀, v₀, w₀, hT₀, ⟨i⟩⟩ := exists_cone_iso_map α G hT'
  exact Stacks.Algebraization.smul_id_eq_zero_of_iso (q : ℤ) i
    (smul_id_map_eq_zero G (h E₀ v₀ w₀ hT₀))

/-- **The object-level annihilation of `α` gives the cohomology-sheaf annihilation of `G.map α`**
for any additive triangulated functor `G`. -/
theorem annihilation07Q9_map_of_objectAnnihilation07Q9 (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} {α : A ⟶ B}
    (G : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))
    [G.Additive] [G.CommShift ℤ] [G.IsTriangulated]
    (h : ObjectAnnihilation07Q9 S q α) :
    Annihilation07Q9 S' q (G.map α) :=
  annihilation07Q9_of_objectAnnihilation07Q9 S' q (objectAnnihilation07Q9_map S S' q G h)

/-- **The cohomology-sheaf annihilation transports along a functor identified degreewise on
cohomology.**  Suppose for every degree `j` and every object `K` the cohomology sheaf `ℋ^j(G K)`
is isomorphic to `R(ℋ^j K)` for an additive `R : Ab(X_Zar) ⥤ Ab(X'_Zar)`.  Then
`Annihilation07Q9` for `α` gives `Annihilation07Q9` for `G.map α`, with the same `q`. -/
theorem annihilation07Q9_map_of_homologyIso (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} {α : A ⟶ B}
    (G : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}))
    [G.CommShift ℤ] [G.IsTriangulated]
    (R : Sheaf (opensTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) [R.Additive]
    (e : ∀ (j : ℤ) (K : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})),
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj (G.obj K) ≅
        R.obj ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) j).obj K))
    (h : Annihilation07Q9 S q α) :
    Annihilation07Q9 S' q (G.map α) := by
  intro E' v' w' hT' j
  obtain ⟨E₀, v₀, w₀, hT₀, ⟨i⟩⟩ := exists_cone_iso_map α G hT'
  exact Stacks.Algebraization.smul_id_eq_zero_of_iso (q : ℤ)
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).mapIso i)
    (Stacks.Algebraization.smul_id_eq_zero_of_iso (q : ℤ) (e j E₀)
      (smul_id_map_eq_zero R (h E₀ v₀ w₀ hT₀ j)))

end Transport

/-! ### Transport along `Rf_{Zar, *}` -/

section ZariskiPushforward

variable (S S' : GlobalCrystallineSituation.{u}) (fX : S.X ⟶ S'.X)
  [HasDerivedCategory.{w} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S') AddCommGrpCat.{u + 1})]

/-- `Rf_{Zar, *}` is additive. -/
instance additive_derivedZariskiPushforwardFunctor :
    (derivedZariskiPushforwardFunctor S S' fX).Additive :=
  inferInstanceAs (zariskiPushforward S S' fX).rightDerivedFunctorPlus.Additive

/-- `Rf_{Zar, *}` commutes with the shift. -/
instance commShift_derivedZariskiPushforwardFunctor :
    (derivedZariskiPushforwardFunctor S S' fX).CommShift ℤ :=
  inferInstanceAs ((zariskiPushforward S S' fX).rightDerivedFunctorPlus.CommShift ℤ)

/-- **`Rf_{Zar, *}` is an exact functor of triangulated categories**, [Stacks, Tag 0159]. -/
instance isTriangulated_derivedZariskiPushforwardFunctor :
    (derivedZariskiPushforwardFunctor S S' fX).IsTriangulated :=
  inferInstanceAs (zariskiPushforward S S' fX).rightDerivedFunctorPlus.IsTriangulated

/-- **The object-level annihilation pushed along `Rf_{Zar, *}`.**  If every cone of `α` is killed
by `q` as an object, then `Rf_{Zar, *}α` satisfies `Annihilation07Q9` for `q`. -/
theorem annihilation07Q9_derivedZariskiPushforward_map_of_object (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} {α : A ⟶ B}
    (h : ObjectAnnihilation07Q9 S q α) :
    Annihilation07Q9 S' q ((derivedZariskiPushforwardFunctor S S' fX).map α) :=
  annihilation07Q9_map_of_objectAnnihilation07Q9 S S' q
    (derivedZariskiPushforwardFunctor S S' fX) h

/-- **The cohomology-sheaf annihilation pushed along `Rf_{Zar, *}`.**  If
`ℋ^j(Rf_{Zar, *}K) ≅ f_{Zar, *}(ℋ^j K)` for every degree `j` and every object `K`, then
`Annihilation07Q9` for `α` gives `Annihilation07Q9` for `Rf_{Zar, *}α`, with the same `q`. -/
theorem annihilation07Q9_derivedZariskiPushforward_map_of_homologyIso (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} {α : A ⟶ B}
    (e : ∀ (j : ℤ) (K : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})),
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S') AddCommGrpCat.{u + 1}) j).obj
            ((derivedZariskiPushforwardFunctor S S' fX).obj K) ≅
        (zariskiPushforward S S' fX).obj ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) j).obj K))
    (h : Annihilation07Q9 S q α) :
    Annihilation07Q9 S' q ((derivedZariskiPushforwardFunctor S S' fX).map α) :=
  annihilation07Q9_map_of_homologyIso S S' q (derivedZariskiPushforwardFunctor S S' fX)
    (zariskiPushforward S S' fX) e h

end ZariskiPushforward

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
