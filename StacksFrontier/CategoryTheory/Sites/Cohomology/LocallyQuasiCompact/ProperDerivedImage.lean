module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiDerivedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDirectImage

/-!
# Derived direct image and the Zariski comparison morphism

Let `f : X ⟶ Y` be a morphism of the Zariski site `LC_Zar` of Hausdorff, locally quasi-compact
spaces, `g : X → Y` its underlying continuous map, and
`π_X : Sh(LC_Zar/X) → Sh(X_Zar)`, `π_Y : Sh(LC_Zar/Y) → Sh(Y_Zar)` the comparison morphisms of
topoi. On abelian sheaves `LocallyQuasiCompact.ProperDirectImage` constructs the ordinary
base-change map `π_Y^{-1} g_* ⟶ f_{Zar,*} π_X^{-1}`. This file derives it: it builds the
canonical map

`R g_* ⋙ R π_Y^{-1} ⟶ R π_X^{-1} ⋙ R f_{Zar,*}`

of functors between bounded-below derived categories, and reduces its invertibility to two
inputs, of which the second is the only mathematics the derived statement adds to the underived
one.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.topologicalPushforward`: the direct image
  `g_*` of abelian sheaves, *with its source and target written as `CategoryTheory.Sheaf`
  categories*. See the implementation note below: this spelling is what makes the whole file
  elaborate.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiBaseChange`: the ordinary abelian
  base-change map in that spelling. It is `abelianProperDirectImageComparison`, and the
  ascription in its body is the single place where the two spellings of `g_*` meet.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.baseChangeOnHomotopy`: the base-change map
  on bounded-below homotopy categories, with the derived unit of `π_Y^{-1}` undone.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.properDirectImageComparisonOnHomotopy`:
  the transformation out of the homotopy category that the derived map descends.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.properDerivedImageComparison`: the derived
  base-change map, obtained by the universal property of bounded-below right derivation.
* `Stacks.DerivedPlus.mapHomotopyCategoryPlusNatTrans`: a natural transformation of additive
  functors, mapped to the bounded-below homotopy categories.

## Main results

Two general facts this file used to restate are declared once in
`StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow`, which this module
imports and therefore re-exports: `CategoryTheory.Functor.isRightDerivedFunctor_postcomp`
(post-composing a right derived functor on `D⁺` with an arbitrary functor again gives one) and
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology` (a functor
preserving homology is its own right derived functor on `D⁺`).
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.properDerivedImageComparison_fac`: the
  defining equation of the derived map.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isIso_properDerivedImageComparison`: the
  derived base-change map is invertible, given the invertibility of the ordinary base-change map
  and the `f_{Zar,*}`-acyclicity of `π_X^{-1}` on complexes of injectives.
* `isIso_properDerivedImageComparison_of_preservesInjectiveObjects`, in the same namespace: the
  same conclusion when `π_X^{-1}` preserves injective objects.

## Implementation notes

**The two spellings of a category of sheaves on a space.** `TopCat.Sheaf C Z` and
`Sheaf (Opens.grothendieckTopology Z) C` are definitionally the same type, but they carry
*different* `Category` instances — `TopCat.instCategorySheaf` and
`ObjectProperty.FullSubcategory.category`. A composite
`TopCat.Sheaf.pushforward C g ⋙ S.abelianComparisonInverseImage Y` is therefore type-correct only
at default transparency, and every `Preadditive`, `Additive`, `mapHomotopyCategoryPlus` and
`rightDerivedFunctorPlus` built over it has to re-check that identification. Naming the middle
whiskerings as separate declarations does not help, because the cost is in a sub-term each piece
re-elaborates. The cure used here is to carry the identification in the *result type* of
`topologicalPushforward` and to state every whiskering, and all the derived machinery, against
that; the conversion to the `TopCat.Sheaf.pushforward` spelling then happens exactly once, in the
body of `zariskiBaseChange`. With that, nothing in this file needs a raised heartbeat budget.

**What is still open.** `isIso_properDerivedImageComparison` takes two hypotheses.

The first, `IsIso (zariskiBaseChange S f)`, is the *underived* clause of Stacks 0DCU for abelian
coefficients; `isIso_zariskiBaseChange_iff` identifies it with
`IsIso (abelianProperDirectImageComparison S f)`, which
`isIso_abelianProperDirectImageComparison_iff` turns into the invertibility of the `Y`-side
counit at every `f_{Zar,*} π_X^{-1} F`.

The second is the acyclicity input, and it is irreducible: the derived unit of `f_{Zar,*}` is not
invertible at a general `π_X^{-1} F`, since `R^i f_{Zar,*}(π_X^{-1} F) = π_Y^{-1}(R^i g_* F)` is
nonzero for `i > 0`. It is invertible on complexes of *injectives*, and that is exactly what is
hypothesized; the proof then runs the uniqueness of right derived functors, the criterion being
checkable at complexes of injectives because of the injective derivability structure on `D⁺`.

These declarations carry no tag: they do not state Stacks 0DCU in full, and its several assertions
are registered at their own statements.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.DerivedPlus

universe u₁ u₂ w

variable {ι : Type w} {A : Type u₁} {B : Type u₂} [Category* A] [Category* B]
  [Preadditive A] [Preadditive B] {F G : A ⥤ B} [F.Additive] [G.Additive]

/-- A natural isomorphism of additive functors stays an isomorphism after mapping to the homotopy
categories of complexes. -/
instance isIso_natTransMapHomotopyCategory (α : F ⟶ G) [IsIso α] (c : ComplexShape ι) :
    IsIso (NatTrans.mapHomotopyCategory α c) :=
  ⟨NatTrans.mapHomotopyCategory (inv α) c, by
    rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id, NatTrans.mapHomotopyCategory_id],
    by
    rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id, NatTrans.mapHomotopyCategory_id]⟩

/-- A natural transformation of additive functors, mapped to the bounded-below homotopy
categories. -/
def mapHomotopyCategoryPlusNatTrans (α : F ⟶ G) :
    F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus where
  app K := ObjectProperty.homMk ((NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app K.obj)
  naturality K L f := by
    ext
    exact (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).naturality f.hom

/-- Mapping a natural isomorphism to the bounded-below homotopy categories gives a natural
isomorphism. -/
instance isIso_mapHomotopyCategoryPlusNatTrans (α : F ⟶ G) [IsIso α] :
    IsIso (mapHomotopyCategoryPlusNatTrans α) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  rw [← ObjectProperty.isIso_hom_iff]
  exact NatIso.isIso_app_of_isIso (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)) K.obj

end Stacks.DerivedPlus

namespace CategoryTheory.Functor

universe u₁ u₂ u₃

variable {A : Type u₁} {B : Type u₂} {E : Type u₃} [Category* A] [Category* B] [Category* E]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive]

/-! `CategoryTheory.Functor.isRightDerivedFunctor_postcomp` — that post-composing a right derived
functor on `D⁺` with an arbitrary functor again gives a right derived functor — is declared once,
in `StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow`, which this module
imports and therefore re-exports. -/

/-! `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology` — that a
homology-preserving additive functor has an invertible derived unit on `D⁺` — is likewise
declared once, in `StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow`, and
re-exported here. -/

end CategoryTheory.Functor

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- The direct image `g_*` of abelian sheaves along the continuous map underlying `f`, with its
source and target written as `CategoryTheory.Sheaf` categories.

Writing the result type this way is what makes the derived constructions below elaborate. The two
spellings `TopCat.Sheaf C Z` and `Sheaf (Opens.grothendieckTopology Z) C` are definitionally the
same type but carry *different* `Category` instances (`TopCat.instCategorySheaf` versus
`ObjectProperty.FullSubcategory.category`), so a composite `TopCat.Sheaf.pushforward … ⋙
S.abelianComparisonInverseImage Y` is type-correct only at default transparency, and each
`Preadditive`, `Additive`, `mapHomotopyCategoryPlus` and `rightDerivedFunctorPlus` built over it
has to re-check that identification. Carrying it in this declaration's result type discharges it
once and for all. -/
abbrev topologicalPushforward
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{max (u + 1) v}
    ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)

/-- `g_*` is additive: on underlying presheaves it is restriction along `Opens.map g`, which only
reindexes the components of a natural transformation. -/
instance topologicalPushforward_additive
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y) :
    (topologicalPushforward.{u, w, v} S f).Additive where
  map_add := rfl

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)

/-- The ordinary base-change map `π_Y^{-1} g_* ⟶ f_{Zar,*} π_X^{-1}` on abelian sheaves, with
`g_*` in the `CategoryTheory.Sheaf` spelling. This *is*
`abelianProperDirectImageComparison`; the ascription is the single place where the two spellings
of `g_*` are identified. -/
def zariskiBaseChange :
    topologicalPushforward.{u, w, v} S f ⋙
        S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y ⟶
      S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (S.zariskiTopology.over Y) (S.zariskiTopology.over X) :=
  abelianProperDirectImageComparison.{u, w, v} S f

/-- The base-change map in the `Sheaf` spelling is invertible exactly when the one in the
`TopCat.Sheaf` spelling is: they are the same morphism. -/
theorem isIso_zariskiBaseChange_iff :
    IsIso (zariskiBaseChange.{u, w, v} S f) ↔
      IsIso (abelianProperDirectImageComparison.{u, w, v} S f) := Iff.rfl

section Derived

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- The comparison inverse image is exact, hence is its own right derived functor on `D⁺`: the
unit of its right derived functor is invertible. -/
instance abelianComparisonInverseImage_rightDerivedFunctorPlusUnit_isIso
    (T : S.category)
    [HasSheafify (Opens.grothendieckTopology T.obj) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (S.zariskiTopology.over T) AddCommGrpCat.{max (u + 1) v}]
    [EnoughInjectives (Sheaf (Opens.grothendieckTopology T.obj) AddCommGrpCat.{max (u + 1) v})] :
    IsIso (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} T).rightDerivedFunctorPlusUnit :=
  Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology _

/-- The first four factors of `properDirectImageComparisonOnHomotopy`: undo the derived unit of
`π_Y^{-1}` (invertible, because `π_Y^{-1}` is exact), merge the two homotopy-category functors,
apply the ordinary base-change map degreewise, and split them again. -/
def baseChangeOnHomotopy :
    (topologicalPushforward.{u, w, v} S f).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ⟶
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapHomotopyCategoryPlus ⋙
        ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
            (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh :=
  Functor.whiskerLeft (topologicalPushforward.{u, w, v} S f).mapHomotopyCategoryPlus
      (inv (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlusUnit) ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (topologicalPushforward.{u, w, v} S f ⋙
        S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y))).hom
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Stacks.DerivedPlus.mapHomotopyCategoryPlusNatTrans (zariskiBaseChange.{u, w, v} S f))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (S.zariskiTopology.over Y) (S.zariskiTopology.over X)))).inv
      DerivedCategory.Plus.Qh

/-- `baseChangeOnHomotopy` is an isomorphism as soon as the ordinary base-change map is: its other
three factors are isomorphisms unconditionally. -/
instance isIso_baseChangeOnHomotopy [IsIso (zariskiBaseChange.{u, w, v} S f)] :
    IsIso (baseChangeOnHomotopy.{u, w, v} S f) := by
  dsimp only [baseChangeOnHomotopy]
  infer_instance

/-- The ordinary base-change map applied degreewise to bounded-below complexes, followed by the
canonical derived units. This is the transformation that `properDerivedImageComparison` descends
through the universal property of right derivation. -/
def properDirectImageComparisonOnHomotopy :
    (topologicalPushforward.{u, w, v} S f).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ⟶
      DerivedCategory.Plus.Qh ⋙
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).rightDerivedFunctorPlus ⋙
        ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).rightDerivedFunctorPlus :=
  baseChangeOnHomotopy.{u, w, v} S f ≫
    Functor.whiskerLeft
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapHomotopyCategoryPlus
      ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (S.zariskiTopology.over Y)
        (S.zariskiTopology.over X)).rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).rightDerivedFunctorPlusUnit
      ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).rightDerivedFunctorPlus

/-- The components of `properDirectImageComparisonOnHomotopy`. -/
theorem properDirectImageComparisonOnHomotopy_app
    (K : HomotopyCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})) :
    (properDirectImageComparisonOnHomotopy.{u, w, v} S f).app K =
      (baseChangeOnHomotopy.{u, w, v} S f).app K ≫
        ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
            (S.zariskiTopology.over Y)
            (S.zariskiTopology.over X)).rightDerivedFunctorPlusUnit.app
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapHomotopyCategoryPlus.obj
            K) ≫
        ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
            (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).rightDerivedFunctorPlus.map
          ((S.abelianComparisonInverseImage.{u, w,
            max (u + 1) v} X).rightDerivedFunctorPlusUnit.app K) := rfl

/-- The canonical derived Zariski base-change map, extending `zariskiBaseChange` through the
universal property of bounded-below right derivation. -/
def properDerivedImageComparison :
    (topologicalPushforward.{u, w, v} S f).rightDerivedFunctorPlus ⋙
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ⟶
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).rightDerivedFunctorPlus ⋙
        ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc
    ((topologicalPushforward.{u, w, v} S f).rightDerivedFunctorPlus ⋙
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus)
    (L := DerivedCategory.Plus.Qh)
    (Functor.whiskerRight (topologicalPushforward.{u, w, v} S f).rightDerivedFunctorPlusUnit
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}))
    _ (properDirectImageComparisonOnHomotopy.{u, w, v} S f)

/-- The defining equation identifying the derived map with the ordinary base-change
transformation. -/
theorem properDerivedImageComparison_fac :
    Functor.whiskerRight (topologicalPushforward.{u, w, v} S f).rightDerivedFunctorPlusUnit
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        (properDerivedImageComparison.{u, w, v} S f) =
        properDirectImageComparisonOnHomotopy.{u, w, v} S f :=
  Functor.rightDerived_fac
    ((topologicalPushforward.{u, w, v} S f).rightDerivedFunctorPlus ⋙
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus)
    (L := DerivedCategory.Plus.Qh)
    (Functor.whiskerRight (topologicalPushforward.{u, w, v} S f).rightDerivedFunctorPlusUnit
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}))
    _ (properDirectImageComparisonOnHomotopy.{u, w, v} S f)

/-- **The derived base-change map is invertible, given the two inputs it needs.**

The first hypothesis is the *underived* clause of Stacks 0DCU for abelian coefficients: the
ordinary base-change map `π_Y^{-1} g_* ⟶ f_{Zar,*} π_X^{-1}` is invertible. By
`isIso_zariskiBaseChange_iff` it is the same statement as
`IsIso (abelianProperDirectImageComparison S f)`, which by
`isIso_abelianProperDirectImageComparison_iff` is the invertibility of the `Y`-side counit at
every `f_{Zar,*} π_X^{-1} F`.

The second hypothesis is the acyclicity input, and it is what the derived clause genuinely adds
to the underived one: a bounded-below complex of *injective* abelian sheaves on the small Zariski
site of `X` is carried by `π_X^{-1}` to a complex that already computes `R f_{Zar,*}`. It cannot
be dropped and it does not follow from the first hypothesis, because the derived unit of
`f_{Zar,*}` is not invertible at a general `π_X^{-1} F`:
`R^i f_{Zar,*}(π_X^{-1} F) = π_Y^{-1}(R^i g_* F)` is nonzero for `i > 0`.

The proof is the uniqueness of right derived functors. The source of the comparison is a right
derived functor by `Functor.isRightDerivedFunctor_postcomp`; the target is one as well, because
the injective derivability structure on `D⁺` reduces the criterion to complexes of injectives,
where `properDirectImageComparisonOnHomotopy` factors as `baseChangeOnHomotopy` (invertible by
the first hypothesis), the derived unit of `f_{Zar,*}` (invertible by the second) and the derived
unit of `π_X^{-1}` (invertible because `π_X^{-1}` is exact). -/
theorem isIso_properDerivedImageComparison
    (hbc : IsIso (zariskiBaseChange.{u, w, v} S f))
    (hac : ∀ K : HomotopyCategory.Plus (InjectiveObject
        (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})),
      IsIso (((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (S.zariskiTopology.over Y)
          (S.zariskiTopology.over X)).rightDerivedFunctorPlusUnit.app
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapHomotopyCategoryPlus.obj
          ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj K)))) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) := by
  have := hbc
  refine (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
    ((topologicalPushforward.{u, w, v} S f).rightDerivedFunctorPlus ⋙
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus)
    (Functor.whiskerRight (topologicalPushforward.{u, w, v} S f).rightDerivedFunctorPlusUnit
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}))
    _ (properDirectImageComparisonOnHomotopy.{u, w, v} S f)).1 ?_
  refine (HomotopyCategory.Plus.localizerMorphism_derives
    ((topologicalPushforward.{u, w, v} S f).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh ⋙
      (S.abelianComparisonInverseImage.{u, w,
        max (u + 1) v} Y).rightDerivedFunctorPlus)).isRightDerivedFunctor_of_isIso _ ?_
  intro K
  have h := hac K
  rw [properDirectImageComparisonOnHomotopy_app]
  infer_instance

/-- The acyclicity hypothesis of `isIso_properDerivedImageComparison` holds as soon as `π_X^{-1}`
preserves injective objects: a complex of injectives is then carried to a complex of injectives,
at which the unit of any right derived functor on `D⁺` is invertible. -/
theorem isIso_properDerivedImageComparison_of_preservesInjectiveObjects
    [(S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).PreservesInjectiveObjects]
    (hbc : IsIso (zariskiBaseChange.{u, w, v} S f)) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) := by
  refine isIso_properDerivedImageComparison.{u, w, v} S f hbc fun K => ?_
  have h : ∀ n : ℤ, Injective
      (((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapHomotopyCategoryPlus.obj
        ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj K)).obj.as.X n) := fun n =>
    (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).injective_obj_of_injective
      (K.obj.as.X n).property
  infer_instance

end Derived

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
