module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.DerivedSectionsOfAPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
import StacksCore.Tactic.StacksAttribute
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Relative cohomology across the Zariski comparison morphism

Let `f : X ⟶ Y` be a morphism of the locally quasi-compact Zariski site, and let
`π_Y : Sh(LC_Zar/Y) → Sh(Y_Zar)` be the comparison morphism of topoi. Part of Stacks 0DCU is
the assertion that for `L ∈ D⁺(Y)` the cohomology of `π_Y^{-1}L` *over the object `X/Y`* of the
localized Zariski site agrees with the cohomology of the space `X` with coefficients in
`f^{-1}L`:

`H^n_{Zar}(X, π_Y^{-1}L) = H^n(X, f^{-1}L)`.

This is `relativeZariskiCohomologyIso`.

The route is the source's. Four identifications chain up, each of them an isomorphism of
bounded below right derived functors:

* the commutative square of topoi of Stacks 0DCU, read on abelian sheaves:
  `f^{-1} ⋙ π_X^{-1} ≅ π_Y^{-1} ⋙ f_{Zar}^{-1}` (`abelianComparisonSquareIso`);
* sections of `f_{Zar}^{-1}` over `X` as an object over itself are sections over `X/Y`
  (`sliceInverseImageSectionsIso`), which is the relocalization step;
* sections of `π_{X,*}` over the whole space are sections over `X` as an object over itself
  (`comparisonDirectImageSectionsIso`);
* the unit `id ≅ π_{X,*} ∘ π_X^{-1}` of the comparison adjunction, which is the clause of
  Stacks 0DCU proved in `ZariskiComparisonEmbedding.lean`
  (`abelianComparisonAdjunction_unit_isIso`).

Passing each of these to bounded below right derived functors needs an acyclicity input, and
the whole point of this arrangement is that each stage has one: `π_X^{-1}`, `π_Y^{-1}`,
`f^{-1}` and `f_{Zar}^{-1}` are exact, so no object obstructs them; `π_{X,*}` preserves
injectives, because its left adjoint `π_X^{-1}` is exact; and `f_{Zar}^{-1}` preserves
injectives, because *its* left adjoint is lower shriek along `Over.map f`, which is exact by
Stacks 04BH.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensToSliceTopIso`: the top open subset
  of the space of `X`, as an object over `X`, is `X` over itself.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonDirectImageSectionsIso`: global
  sections of the comparison direct image.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.sliceInverseImageSectionsIso`: sections
  of the slice inverse image.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.abelianComparisonSquareIso`: the
  commutative square of Stacks 0DCU on abelian sheaves.

## Main results

* `sliceInverseImage_preservesInjectiveObjects`: the inverse image along a morphism of the
  Zariski slice sites preserves injective abelian sheaves.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.relativeZariskiCohomologyIso`: the
  relative cohomology comparison.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.relativeZariskiCohomologyIso_unconditional`:
  the same with the four sheafifications and the four enough-injectives inputs discharged
  rather than assumed. It is registered for the tag beside the form above.

## Implementation notes

Cohomology over an object `U` of a site is modelled as the bounded below right derived functor
of sections over `U`, and the degree-`n` group is read off with the homology functor of the
bounded below derived category. That is the model that makes sense of the source's `L ∈ D⁺(Y)`;
the clause of Stacks 0DCU about a single abelian sheaf on the space of `X` is recorded in
`ZariskiCohomologyComparison.lean` in Mathlib's `Ext`-model `Sheaf.H` instead, which is the
natural one for a single sheaf. The two models agree, in the shape of
`Stacks.Cohomology.ColimitsOfCohomology.globalSectionsRightDerivedIsoFunctorH`; that statement
itself does not apply here, being for global sections over a small site with coefficients in
`AddCommGrpCat` at the universe of the site.

`HasSheafify` and `EnoughInjectives` for the four sheaf categories are instance arguments of
`relativeZariskiCohomologyIso`, as they are in `ZariskiCohomologyComparison.lean`, and are *not*
assumptions of `relativeZariskiCohomologyIso_unconditional`. They are no restriction on either:
the sites of opens of the two spaces and the two Zariski slice sites are all essentially small at
this coefficient universe, so `hasSheafify_opensSite` and `hasSheafify_zariskiSlice` give the
four `HasSheafify` instances, and `enoughInjectives_spaceSheaf` and
`enoughInjectives_zariskiSliceSheaf` give the four `EnoughInjectives` instances. Neither class
can be found by instance search from those theorems — `HasSheafify` carries data, so a global
instance alongside the instance binders the abelian layer over this site threads through its
files would give two sheafification functors for one site — so the unconditional statement
supplies all eight with `letI` instead.

Of the seven clauses of Stacks 0DCU, the last of which the source splits into (7a) and (7b),
`relativeZariskiCohomologyIso` below is clause (6) and carries the tag for it. The others are
the cohomology comparison `zariskiCohomologyComparisonIso` (1), the exactness of the direct
image `abelianComparisonDirectImage_exact` (2), the invertibility of the unit
`abelianComparisonAdjunction_unit_isIso` (3), its derived counterpart
`abelianDerivedComparisonAdjunction_unit_isIso` (4), the commutative square
`zariskiComparisonSquareIso` (5), and the compatibility of the comparison with pushforward
along a *proper* morphism, `properDirectImageComparisonIsoOfProperMap` (7a) and
`properDerivedImageComparison_isIso` (7b).

The declarations of the first section are statements of homological algebra with no Zariski
content: the comparison `R(G ∘ F) ≅ RG ∘ RF` of Stacks 015M under the two acyclicity hypotheses
that occur here, the triviality of right derivation on an identity functor, and the two forms
in which a sections functor is transported across an adjunction. They specialize
`Stacks.Cohomology.DerivedPushforwardSections.compIso` and so are placed in its namespace.

`CategoryTheory.sheafSections_obj_additive` and `CategoryTheory.sheafPullback_additive` are two
additivity instances about an arbitrary site which right derivation needs and which Mathlib does
not have: sections over an object, and the pullback along a continuous functor, are additive. The
first holds because addition of morphisms of sheaves is computed componentwise; the second
because a left adjoint preserves zero morphisms and binary coproducts, hence biproducts.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w v a b t

namespace CategoryTheory

/-- Sections of a sheaf with values in a preadditive category, over a fixed object of the site,
is an additive functor: addition of morphisms of sheaves is computed componentwise. -/
instance sheafSections_obj_additive {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {A : Type*} [Category* A] [Preadditive A] (U : C) :
    ((sheafSections J A).obj (Opposite.op U)).Additive where
  map_add := by intro _ _ _ _; rfl

/-- The pullback of abelian sheaves along a continuous functor of sites is additive: being a
left adjoint it preserves zero morphisms and binary coproducts, hence binary biproducts. -/
instance sheafPullback_additive {C : Type*} [Category* C] {D : Type*} [Category* D]
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous AddCommGrpCat.{t} J K).IsRightAdjoint]
    [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}] :
    (u.sheafPullback AddCommGrpCat.{t} J K).Additive := by
  have _ : (u.sheafPullback AddCommGrpCat.{t} J K).IsLeftAdjoint :=
    (u.sheafAdjunctionContinuous AddCommGrpCat.{t} J K).isLeftAdjoint
  have _ : (u.sheafPullback AddCommGrpCat.{t} J K).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have _ : Limits.PreservesColimitsOfShape (Discrete Limits.WalkingPair)
      (u.sheafPullback AddCommGrpCat.{t} J K) := inferInstance
  have _ : Limits.PreservesBinaryBiproducts (u.sheafPullback AddCommGrpCat.{t} J K) :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

end CategoryTheory

/-! ### Right derivation of a composite -/

namespace Stacks.Cohomology.DerivedPushforwardSections

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Derived

variable {A : Type*} [Category* A] {B : Type*} [Category* B] {E : Type*} [Category* E]
  [Abelian A] [Abelian B] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]

/-- An injective object is right acyclic for a left exact additive functor: its higher right
derived functors vanish on an injective object, and that is the criterion of Stacks 015C (2). -/
theorem rightAcyclic_of_injective [EnoughInjectives A]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] (I : A) [Injective I] :
    G.rightAcyclic I :=
  ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus G I).2 inferInstance).2
    fun _ hn => Functor.isZero_rightDerivedPlus_obj_injective G _ (by omega) I

/-- **Stacks 015M** when the first functor preserves injectives and the second is left exact:
`R(G ∘ F) ≅ RG ∘ RF`. -/
def compIsoOfPreservesInjectives [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive] [F.PreservesInjectiveObjects]
    [PreservesFiniteLimits G] :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  Stacks.Cohomology.DerivedPushforwardSections.compIso F G (by
    intro I hI
    have _ : Injective I := hI
    have _ : Injective (F.obj I) := F.injective_obj I
    exact rightAcyclic_of_injective G (F.obj I))

/-- **Stacks 015M** when the second functor is exact: `R(G ∘ F) ≅ RG ∘ RF`, because an exact
functor is its own right derived functor, so every object is right acyclic for it. -/
def compIsoOfExact [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  have _ : IsIso G.rightDerivedFunctorPlusUnith :=
    Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology G
  Stacks.Cohomology.DerivedPushforwardSections.compIso F G (by
    intro I _
    change IsIso (G.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor B 0).obj (F.obj I)))
    exact NatIso.isIso_app_of_isIso G.rightDerivedFunctorPlusUnith _)

/-- Right derivation does nothing to an identity functor. -/
def rightDerivedFunctorPlusIdIso (A : Type*) [Category* A] [Abelian A]
    [HasDerivedCategory A] [EnoughInjectives A] :
    (𝟭 A).rightDerivedFunctorPlus ≅ 𝟭 (DerivedCategory.Plus A) := by
  have _ : IsIso (𝟭 A).rightDerivedFunctorPlusUnith :=
    Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology (𝟭 A)
  let eCx : (𝟭 A).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      𝟭 (HomotopyCategory A (ComplexShape.up ℤ)) :=
    CategoryTheory.Quotient.natIsoLift _
      (Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ))
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)))
  let eh : (𝟭 A).mapHomotopyCategoryPlus ≅ 𝟭 (HomotopyCategory.Plus A) :=
    NatIso.ofComponents (fun K => ObjectProperty.isoMk _ (eCx.app K.obj))
      (by intro K K' g; ext; exact eCx.hom.naturality g.hom)
  exact (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso A) _).preimageIso
    ((asIso (𝟭 A).rightDerivedFunctorPlusUnith).symm ≪≫ Functor.isoWhiskerRight eh _)

/-- Transport of a sections functor across a right adjoint which preserves injectives: if
`R ⋙ Γ ≅ Δ` then `RR ⋙ RΓ ≅ RΔ`. -/
def rightDerivedSectionsIso [EnoughInjectives A] [EnoughInjectives B]
    (R : A ⥤ B) (Γ : B ⥤ E) (Δ : A ⥤ E) [R.Additive] [Γ.Additive] [Δ.Additive]
    [R.PreservesInjectiveObjects] [PreservesFiniteLimits Γ] (e : R ⋙ Γ ≅ Δ) :
    R.rightDerivedFunctorPlus ⋙ Γ.rightDerivedFunctorPlus ≅ Δ.rightDerivedFunctorPlus :=
  (compIsoOfPreservesInjectives R Γ).symm ≪≫
    Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso e

/-- Transport of a sections functor across an exact adjoint pair whose unit is invertible: if
`L ⋙ R ≅ 𝟭` and `R ⋙ Γ ≅ Δ` then `RL ⋙ RΔ ≅ RΓ`. -/
def rightDerivedUnitSectionsIso [EnoughInjectives A] [EnoughInjectives B]
    (L : A ⥤ B) (R : B ⥤ A) (Γ : A ⥤ E) (Δ : B ⥤ E)
    [L.Additive] [R.Additive] [Γ.Additive] [Δ.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [R.PreservesInjectiveObjects] [PreservesFiniteLimits Γ]
    (η : L ⋙ R ≅ 𝟭 A) (e : R ⋙ Γ ≅ Δ) :
    L.rightDerivedFunctorPlus ⋙ Δ.rightDerivedFunctorPlus ≅ Γ.rightDerivedFunctorPlus :=
  let eR := rightDerivedSectionsIso R Γ Δ e
  let eUnit := (compIsoOfExact L R).symm ≪≫
    Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso η ≪≫
      rightDerivedFunctorPlusIdIso A
  Functor.isoWhiskerLeft L.rightDerivedFunctorPlus eR.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eUnit _ ≪≫
      Functor.leftUnitor _

end Derived

end Stacks.Cohomology.DerivedPushforwardSections

/-! ### The three underived identifications -/

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

open Stacks.Cohomology.DerivedPushforwardSections

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- The top open subset of the space of `X`, viewed as an object over `X`, is `X` over itself:
both structure morphisms are open embeddings with image everything. -/
def opensToSliceTopIso (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) :
    (S.opensToSlice X).1.obj (⊤ : Opens X.obj) ≅ Over.mk (𝟙 X) := by
  have ha := (S.opensToSlice X).2 (⊤ : Opens X.obj)
  have hb : Topology.IsOpenEmbedding ((Over.mk (𝟙 X)).hom : X.obj → X.obj) := by
    change Topology.IsOpenEmbedding (𝟙 X : X ⟶ X)
    exact Topology.IsOpenEmbedding.id
  have hrange : Set.range (((S.opensToSlice X).1.obj (⊤ : Opens X.obj)).hom :
        _ → X.obj) =
      Set.range ((Over.mk (𝟙 X)).hom : X.obj → X.obj) := by
    rw [ha.2]
    change Set.univ = Set.range (fun x : X.obj => x)
    simp
  exact overOpenEmbeddingIso S _ _ ha.1 hb hrange

/-- Sections of the comparison direct image over the whole space are sections over `X` as an
object over itself: the underlying presheaf of `π_{X,*}G` is `G` restricted along
`opensToSlice`, and `opensToSlice ⊤` is `X` over itself. -/
def comparisonDirectImageSectionsIso (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    (X : S.category) (A : Type a) [Category.{b} A] :
    S.comparisonDirectImage X A ⋙
        (sheafSections (Opens.grothendieckTopology X.obj) A).obj (op (⊤ : Opens X.obj)) ≅
      (sheafSections (S.zariskiTopology.over X) A).obj (op (Over.mk (𝟙 X))) :=
  eqToIso (comparisonDirectImage_comp_sheafSections S X A) ≪≫
    ((sheafSections (S.zariskiTopology.over X) A).mapIso (opensToSliceTopIso S X).op).symm

/-- Sections of the inverse image along `f_{Zar}` over `X` as an object over itself are sections
over `X/Y`: restriction along `Over.map f` carries `X` over itself to `X` over `Y`. -/
def sliceInverseImageSectionsIso (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    {X Y : S.category} (f : X ⟶ Y) (A : Type a) [Category.{b} A] :
    (Over.map f).sheafPushforwardContinuous A (S.zariskiTopology.over X)
          (S.zariskiTopology.over Y) ⋙
        (sheafSections (S.zariskiTopology.over X) A).obj (op (Over.mk (𝟙 X))) ≅
      (sheafSections (S.zariskiTopology.over Y) A).obj (op (Over.mk f)) :=
  (sheafSections (S.zariskiTopology.over Y) A).mapIso
    (Over.isoMk (Iso.refl X) (by simp) : Over.mk (𝟙 X ≫ f) ≅ Over.mk f).op

/-! ### The commutative square on abelian sheaves -/

/-- **The commutative square of Stacks 0DCU on abelian sheaves.** The comparison morphisms to
the Zariski topoi of the underlying spaces commute with the morphism of slice topoi induced by
`f`, read on inverse images of abelian sheaves.

It is obtained from the site-level square `zariskiComparisonDirectImageSquareIso` by uniqueness
of left adjoints, exactly as the topos-level statement `zariskiComparisonSquareIso` is.

The coefficients are `AddCommGrpCat.{max u t}` for an arbitrary `t`, not the
`AddCommGrpCat.{max (u + 1) v}` of the rest of the directory: nothing in the construction needs
the coefficients to contain the universe `u + 1` of the *objects* of the site. The site-level
square is stated for an arbitrary value category, and the comparison adjunction is available at
`AddCommGrpCat.{max u t}` by `abelianComparisonDirectImage_isRightAdjoint_ofSize`. Taking `t = u`
is what makes the restriction condition of Stacks 0EZI available at `AddCommGrpCat.{u}`, the
coefficient universe of a small model of the site in `Type u`.

What reaching the lower universes costs is the fourth adjunction. Taking it to be
`Functor.sheafAdjunctionContinuous` for `Over.pullback f` asks for the sheaf pullback along
`(Over.pullback f).op`, hence for colimits in the coefficients indexed by a comma category whose
objects live in `Type (u + 1)`; that needs `u + 1 ≤ max u t` and so fails at `t = u`. It is taken
instead to be `CategoryTheory.Adjunction.sheafPushforwardAdjunction` of
`CategoryTheory.Over.mapPullbackAdj`, which asks only that both members of the adjoint pair be
continuous and is therefore available at every coefficient universe. Its left adjoint is already
the direct image the statement is about, so the identification of the sheaf pullback with it
is not needed either. -/
def abelianComparisonSquareIsoOfSize (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    {X Y : S.category} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max u t}]
    [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max u t}]
    [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max u t}]
    [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max u t}] :
    (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).sheafPullback
          AddCommGrpCat.{max u t} (Opens.grothendieckTopology Y.obj)
          (Opens.grothendieckTopology X.obj) ⋙
        S.abelianComparisonInverseImageOfSize.{u, w, t} X ≅
      S.abelianComparisonInverseImageOfSize.{u, w, t} Y ⋙
        (Over.map f).sheafPushforwardContinuous AddCommGrpCat.{max u t}
          (S.zariskiTopology.over X) (S.zariskiTopology.over Y) := by
  let I : S.category ⥤ TopCat := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let A := AddCommGrpCat.{max u t}
  let JX := Opens.grothendieckTopology X.obj
  let JY := Opens.grothendieckTopology Y.obj
  let KX := S.zariskiTopology.over X
  let KY := S.zariskiTopology.over Y
  let uX := (S.opensToSlice X).1
  let uY := (S.opensToSlice Y).1
  let vOpen := Opens.map (I.map f)
  let pOver := Over.pullback f
  let _ : uX.IsContinuous JX KX := S.opensToSlice_isContinuous X
  let _ : uY.IsContinuous JY KY := S.opensToSlice_isContinuous Y
  let _ : vOpen.IsContinuous JY JX := inferInstance
  let _ : pOver.IsContinuous KY KX := inferInstance
  let adjOpen := vOpen.sheafAdjunctionContinuous A JY JX
  let adjX := uX.sheafAdjunctionContinuous A JX KX
  let adjY := uY.sheafAdjunctionContinuous A JY KY
  let adjP : (Over.map f).sheafPushforwardContinuous A KX KY ⊣
      pOver.sheafPushforwardContinuous A KY KX :=
    (Over.mapPullbackAdj f).sheafPushforwardAdjunction A
  let adjL := adjOpen.comp adjX
  let adjR := adjY.comp adjP
  let eRight := zariskiComparisonDirectImageSquareIso S f A
  let eSquarePullback := adjL.leftAdjointUniq (adjR.ofNatIsoRight eRight.symm)
  let eX : S.abelianComparisonInverseImageOfSize.{u, w, t} X ≅ uX.sheafPullback A JX KX :=
    Adjunction.leftAdjointUniq (S.abelianComparisonAdjunctionOfSize.{u, w, t} X) adjX
  let eY : S.abelianComparisonInverseImageOfSize.{u, w, t} Y ≅ uY.sheafPullback A JY KY :=
    Adjunction.leftAdjointUniq (S.abelianComparisonAdjunctionOfSize.{u, w, t} Y) adjY
  exact Functor.isoWhiskerLeft (vOpen.sheafPullback A JY JX) eX ≪≫
    eSquarePullback ≪≫
      Functor.isoWhiskerRight eY.symm ((Over.map f).sheafPushforwardContinuous A KX KY)

/-- **The commutative square of Stacks 0DCU on abelian sheaves.** The comparison morphisms to
the Zariski topoi of the underlying spaces commute with the morphism of slice topoi induced by
`f`, read on inverse images of abelian sheaves.

It is obtained from the site-level square `zariskiComparisonDirectImageSquareIso` by uniqueness
of left adjoints, exactly as the topos-level statement `zariskiComparisonSquareIso` is. -/
def abelianComparisonSquareIso (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    {X Y : S.category} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}] :
    (Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).sheafPullback
          AddCommGrpCat.{max (u + 1) v} (Opens.grothendieckTopology Y.obj)
          (Opens.grothendieckTopology X.obj) ⋙
        S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ≅
      S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y ⋙
        (Over.map f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
          (S.zariskiTopology.over X) (S.zariskiTopology.over Y) :=
  abelianComparisonSquareIsoOfSize.{u, w, max (u + 1) v} S f

/-! ### Preservation of injectives by the slice inverse image -/

/-- The inverse image along a morphism of the Zariski slice sites preserves injective abelian
sheaves: its left adjoint is lower shriek along `Over.map f`, and that is exact by Stacks
04BH, the slices having fibre products and equalizers which `Over.map f` preserves. -/
theorem sliceInverseImage_preservesInjectiveObjects
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}] :
    ((Over.map f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
      (S.zariskiTopology.over X) (S.zariskiTopology.over Y)).PreservesInjectiveObjects := by
  let A := AddCommGrpCat.{max (u + 1) v}
  let KX := S.zariskiTopology.over X
  let KY := S.zariskiTopology.over Y
  let _ : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
  let _ : HasEqualizers (Over X) := hasEqualizers_of_hasPullbacks_and_binary_products
  let _ : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (Over.map f) A KX KY) :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits (Over.map f) KX KY
  let _ : (Functor.sheafPullbackConstruction.sheafPullback (Over.map f) A KX
      KY).PreservesMonomorphisms := inferInstance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Over.map f) A KX KY)

/-! ### The relative cohomology comparison -/

/-- **Stacks 0DCU, clause (6): the relative-cohomology clause.** For a morphism `f : X ⟶ Y` of
the locally quasi-compact Zariski site and `L ∈ D⁺(Y)`, the cohomology of `π_Y^{-1}L` over the
object `X/Y` of the localized Zariski site is the cohomology of the space `X` with coefficients
in `f^{-1}L`:

`H^n_{Zar}(X, π_Y^{-1}L) ≅ H^n(X, f^{-1}L)`,

naturally in `L`. -/
@[stacks 0DCU "relative_cohomology"]
def relativeZariskiCohomologyIso
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    (n : ℤ)
    [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
    [EnoughInjectives
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
    [EnoughInjectives
      (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
    [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
    [EnoughInjectives (Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v})] :
    (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ⋙
        ((sheafSections (S.zariskiTopology.over Y)
            AddCommGrpCat.{max (u + 1) v}).obj (op (Over.mk f))).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max (u + 1) v} n ≅
      ((Opens.map
              ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).sheafPullback
            AddCommGrpCat.{max (u + 1) v} (Opens.grothendieckTopology Y.obj)
            (Opens.grothendieckTopology X.obj)).rightDerivedFunctorPlus ⋙
        ((sheafSections (Opens.grothendieckTopology X.obj)
            AddCommGrpCat.{max (u + 1) v}).obj
          (op (⊤ : Opens X.obj))).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max (u + 1) v} n := by
  let E := AddCommGrpCat.{max (u + 1) v}
  let I : S.category ⥤ TopCat := S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop
  let JX := Opens.grothendieckTopology X.obj
  let JY := Opens.grothendieckTopology Y.obj
  let KX := S.zariskiTopology.over X
  let KY := S.zariskiTopology.over Y
  let P := (Opens.map (I.map f)).sheafPullback E JY JX
  let L := S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X
  let Q := S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y
  let R := S.comparisonDirectImage X E
  let H := (Over.map f).sheafPushforwardContinuous E KX KY
  let ΓX := (sheafSections JX E).obj (op (⊤ : Opens X.obj))
  let ΓD := (sheafSections KX E).obj (op (Over.mk (𝟙 X)))
  let ΓY := (sheafSections KY E).obj (op (Over.mk f))
  -- exactness of the four inverse images
  let _ : PreservesFiniteLimits L := inferInstance
  let _ : PreservesFiniteColimits L :=
    ((exactFunctor_iff L).1 (S.abelianComparisonInverseImage_exact X)).2
  let _ : L.Additive := Functor.additive_of_preserves_binary_products L
  let _ : PreservesFiniteLimits Q := inferInstance
  let _ : PreservesFiniteColimits Q :=
    ((exactFunctor_iff Q).1 (S.abelianComparisonInverseImage_exact Y)).2
  let _ : Q.Additive := Functor.additive_of_preserves_binary_products Q
  let _ : P.Additive := inferInstance
  -- the comparison direct image
  let _ : PreservesFiniteLimits R :=
    ((exactFunctor_iff R).1 (abelianComparisonDirectImage_exact S X)).1
  let _ : PreservesFiniteColimits R :=
    ((exactFunctor_iff R).1 (abelianComparisonDirectImage_exact S X)).2
  let _ : R.Additive := Functor.additive_of_preserves_binary_products R
  let _ : R.PreservesInjectiveObjects := inferInstance
  -- the slice inverse image
  let _ : H.IsLeftAdjoint := ((Over.mapPullbackAdj f).sheafPushforwardAdjunction E).isLeftAdjoint
  let _ : PreservesFiniteColimits H := inferInstance
  let _ : PreservesFiniteLimits H := by
    let _ : PreservesFiniteLimits (H ⋙ sheafToPresheaf KX E) := by
      change PreservesFiniteLimits
        (sheafToPresheaf KY E ⋙ (Functor.whiskeringLeft _ _ E).obj (Over.map f).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves H (sheafToPresheaf KX E)
  let _ : H.Additive := Functor.additive_of_preserves_binary_products H
  let _ : H.PreservesInjectiveObjects := sliceInverseImage_preservesInjectiveObjects S f
  -- the three sections functors
  let _ : PreservesFiniteLimits ΓX := by
    change PreservesFiniteLimits
      (sheafToPresheaf JX E ⋙ (evaluation _ E).obj (op (⊤ : Opens X.obj)))
    infer_instance
  let _ : ΓX.Additive := Functor.additive_of_preserves_binary_products ΓX
  let _ : PreservesFiniteLimits ΓD := by
    change PreservesFiniteLimits
      (sheafToPresheaf KX E ⋙ (evaluation _ E).obj (op (Over.mk (𝟙 X))))
    infer_instance
  let _ : ΓD.Additive := Functor.additive_of_preserves_binary_products ΓD
  let _ : PreservesFiniteLimits ΓY := by
    change PreservesFiniteLimits
      (sheafToPresheaf KY E ⋙ (evaluation _ E).obj (op (Over.mk f)))
    infer_instance
  let _ : ΓY.Additive := Functor.additive_of_preserves_binary_products ΓY
  -- the four identifications
  let ηL : L ⋙ R ≅ 𝟭 _ :=
    have _ : IsIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit :=
      abelianComparisonAdjunction_unit_isIso.{u, w, v} S X
    (asIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit).symm
  let eL := rightDerivedUnitSectionsIso L R ΓX ΓD ηL (comparisonDirectImageSectionsIso S X E)
  let eH := rightDerivedSectionsIso H ΓD ΓY (sliceInverseImageSectionsIso S f E)
  let eStages : P.rightDerivedFunctorPlus ⋙ L.rightDerivedFunctorPlus ≅
      Q.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus :=
    (compIsoOfExact P L).symm ≪≫
      Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso
        (abelianComparisonSquareIso.{u, w, v} S f) ≪≫ compIsoOfExact Q H
  let eAll : P.rightDerivedFunctorPlus ⋙ ΓX.rightDerivedFunctorPlus ≅
      Q.rightDerivedFunctorPlus ⋙ ΓY.rightDerivedFunctorPlus :=
    Functor.isoWhiskerLeft P.rightDerivedFunctorPlus eL.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eStages ΓD.rightDerivedFunctorPlus ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Q.rightDerivedFunctorPlus eH
  exact Functor.isoWhiskerRight eAll.symm (DerivedCategory.Plus.homologyFunctor E n)

/-- **Stacks 0DCU, clause (6): the relative-cohomology clause, with no hypothesis.** For a
morphism `f : X ⟶ Y` of the locally quasi-compact Zariski site and `L ∈ D⁺(Y)`,

`H^n_{Zar}(X, π_Y^{-1}L) ≅ H^n(X, f^{-1}L)`,

naturally in `L`.

Nothing is assumed of the two sites. The four sheafifications and the four enough-injectives
inputs the bounded below right derived functors are built from are supplied by
`hasSheafify_opensSite`, `hasSheafify_zariskiSlice`, `enoughInjectives_spaceSheaf` and
`enoughInjectives_zariskiSliceSheaf`, each of which holds because the site in question is
essentially small at this coefficient universe. -/
@[stacks 0DCU "relative_cohomology, with the four sheafifications and the four \
enough-injectives inputs discharged rather than assumed"]
def relativeZariskiCohomologyIso_unconditional
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    (n : ℤ) :
    letI := hasSheafify_opensSite.{u, w, v} S X
    letI := hasSheafify_opensSite.{u, w, v} S Y
    letI := hasSheafify_zariskiSlice.{u, w, v} S X
    letI := hasSheafify_zariskiSlice.{u, w, v} S Y
    letI := enoughInjectives_spaceSheaf.{u, w, v} S X
    letI := enoughInjectives_spaceSheaf.{u, w, v} S Y
    letI := enoughInjectives_zariskiSliceSheaf.{u, w, v} S X
    letI := enoughInjectives_zariskiSliceSheaf.{u, w, v} S Y
    (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ⋙
        ((sheafSections (S.zariskiTopology.over Y)
            AddCommGrpCat.{max (u + 1) v}).obj (op (Over.mk f))).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max (u + 1) v} n ≅
      ((Opens.map
              ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f)).sheafPullback
            AddCommGrpCat.{max (u + 1) v} (Opens.grothendieckTopology Y.obj)
            (Opens.grothendieckTopology X.obj)).rightDerivedFunctorPlus ⋙
        ((sheafSections (Opens.grothendieckTopology X.obj)
            AddCommGrpCat.{max (u + 1) v}).obj
          (op (⊤ : Opens X.obj))).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max (u + 1) v} n :=
  letI := hasSheafify_opensSite.{u, w, v} S X
  letI := hasSheafify_opensSite.{u, w, v} S Y
  letI := hasSheafify_zariskiSlice.{u, w, v} S X
  letI := hasSheafify_zariskiSlice.{u, w, v} S Y
  letI := enoughInjectives_spaceSheaf.{u, w, v} S X
  letI := enoughInjectives_spaceSheaf.{u, w, v} S Y
  letI := enoughInjectives_zariskiSliceSheaf.{u, w, v} S X
  letI := enoughInjectives_zariskiSliceSheaf.{u, w, v} S Y
  relativeZariskiCohomologyIso.{u, w, v} S f n

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
