module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDifferentialSquare
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcisionComp
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionCocycle
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModulePushforwardComparison

/-!
# The derived excision of `i_*ℋ ⁿ_T`, read through the forgetful functor to abelian sheaves

`Stacks.Gysin.supportCohomologyRestrictIso` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcision.lean` is the derived excision of
[Stacks, Tag 0G78] on degree-`n` cohomology sheaves, an isomorphism of sheaves of
`𝒪_W`-**modules**.  The square of [Stacks, Tag 0G87] needs it read through the forgetful functor
to sheaves of abelian groups, where the action of `i_*ℋ ⁿ_T` on a merely additive morphism — the
de Rham differential — lives: that action is
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap`, [Stacks, Tag 0G74] part (2).

This file supplies the vocabulary in which that reading is a statement, and proves its
`𝒪`-linear half.

## Main definitions

* `Stacks.Gysin.abelianRestrict`: **restriction of sheaves of abelian groups to an open
  subscheme**, and `Stacks.Gysin.restrictFunctorCompAbelianSheafIso`: forgetting the module
  structure and restricting is restricting and forgetting.  Since
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor` **is** `SheafOfModules.pushforward` along the
  functor `W.ι.opensFunctor` on opens,
  `Stacks.Cohomology.SiteModulePushforward.AnySite.pushforwardCompToSheafIso` applies and is the
  identity.
* `Stacks.Gysin.restrictAbHom`: a morphism of the underlying abelian sheaves, restricted to an
  open subscheme.
* `Stacks.Gysin.supportCohomologyRestrictAbHom`: **the abelian reading of the derived excision**,
  `(abelianSheaf W).map` of `Stacks.Gysin.supportCohomologyRestrictIso`, with its source written
  as the abelian restriction of the forgetful image of `i_*ℋ ⁿ_T(ℱ)`.
* `Stacks.Gysin.excisionAbComparison`: that reading **conjugated into the spelling of
  [Stacks, Tag 0G74] part (2)** — an isomorphism between the abelian restriction of
  `i_*ℋ ⁿ_T(ℱ_ab)` and `i_*ℋ ⁿ_{W ∩ T}(ℱ_ab|_W)` for every `ℱ` in `X.Modules`, where both sides
  are the *abelian* local cohomology sheaves
  `Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward`.
* `Stacks.Gysin.SupportCohomologyRestrictAbNatural`: **the compatibility the square of
  [Stacks, Tag 0G87] needs** — the abelian reading of the excision commutes with the action of
  [Stacks, Tag 0G74] part (2) on a morphism `ψ` of the underlying abelian sheaves.

## Main results

* `Stacks.Gysin.supportCohomologyRestrictIso_naturality`: **the derived excision is natural in
  the coefficient module**, in the `AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling:
  the transport of `Stacks.Gysin.supportCohomologyPullbackIso_naturality`, stated in the
  `RingedSpaceModuleAdjunction.modulePullback` spelling.
* `Stacks.Gysin.supportCohomologyRestrictAbNatural_abelianSheaf_map`: **the compatibility holds
  on the underlying morphism of a morphism of modules.**
* `Stacks.Gysin.supportCohomologySheafAbelianMap_eq` and
  `Stacks.Gysin.restrictAbHom_supportCohomologySheafAbelianMap`: the action of
  [Stacks, Tag 0G74] part (2) and its restriction, written as conjugations, which is the form in
  which `SupportCohomologyRestrictAbNatural` is a naturality statement.

## Implementation notes

By `supportCohomologySheafAbelianMap_eq` and `restrictAbHom_supportCohomologySheafAbelianMap` the
compatibility for a given `ψ` is, after cancelling the four copies of [Stacks, Tag 0G74] part (2),
the single square

`(ℋ ⁿ_T(ψ_ab))|_W ≫ excisionAbComparison 𝒢 = excisionAbComparison ℱ ≫ ℋ ⁿ_{W ∩ T}(ψ_ab|_W)`,

that is, naturality of `excisionAbComparison` in `ψ`.  For `ψ` not `𝒪_X`-linear this is not a
consequence of naturality in the module; it follows from the identification of
`excisionAbComparison` with excision for the abelian local cohomology sheaves
(`Stacks.Gysin.supportCohomologyRestrictAbNatural` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean`).

`rw` on `CategoryTheory.Category.assoc` and on `CategoryTheory.Functor.map_comp` is not
type-correct at `implicit` transparency across the two spellings `AlgebraicGeometry.Scheme.Modules`
and `SheafOfModules (structureSheafRing _)` of the category of modules, so every chase is a helper
at a variable category (`paste3`, `map_square`, `CategoryTheory.Functor.map_comp₃`), applied with
`exact`.

`(abelianRestrict W).obj ((abelianSheaf X).obj ℱ)` and `(abelianSheaf W).obj (ℱ|_W)` are
definitionally but not syntactically equal, and identifying them while the elaborator also solves
for the surrounding objects is expensive; so `excisionAbComparison` is stated with the abelian
restriction on both sides and `SupportCohomologyRestrictAbNatural` with `restrictAbHom` on both
sides.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.28.6 (Tag 08FE)](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.GysinAbelianSquare
  (abelianLocalCohomologyPushforward supportCohomologySheafAbelianMap
    supportCohomologySheafForgetIso)
open Stacks.Perfect.SupportedFraction

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.SupportedComplexes.preservesFiniteLimits_modulePullback_of_isOpenImmersion

variable {Y : Scheme.{u}} (W : Y.Opens)

/-! ### Restriction of sheaves of abelian groups to an open subscheme -/

/-- **Restriction of sheaves of abelian groups to an open subscheme.**  It is the direct image
along the functor `W.ι.opensFunctor` on opens, which is the same functor on opens that
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is the direct image along. -/
def abelianRestrict :
    Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology W.toScheme.carrier) AddCommGrpCat.{u} :=
  W.ι.opensFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology W.toScheme.carrier) (Opens.grothendieckTopology Y.carrier)

/-- **Forgetting the module structure and restricting is restricting and forgetting.**
`AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι` is `SheafOfModules.pushforward` along
`W.ι.opensFunctor`, so this is
`Stacks.Cohomology.SiteModulePushforward.AnySite.pushforwardCompToSheafIso` — the two functors are
definitionally equal, the underlying abelian sheaf of `ℱ|_W` being literally `U ↦ ℱ(W.ι ''ᵁ U)`. -/
def restrictFunctorCompAbelianSheafIso :
    Scheme.Modules.restrictFunctor W.ι ⋙ abelianSheaf W.toScheme ≅
      abelianSheaf Y ⋙ abelianRestrict W :=
  Iso.refl _

/-- **A morphism of the underlying abelian sheaves, restricted to an open subscheme.**  The
de Rham differential of `X/S` is such a morphism and is `𝒪_X`-linear for no `X`, so this is the
only sense in which it restricts to a chart. -/
def restrictAbHom {F G : Y.Modules} (ψ : (abelianSheaf Y).obj F ⟶ (abelianSheaf Y).obj G) :
    (abelianSheaf W.toScheme).obj ((Scheme.Modules.restrictFunctor W.ι).obj F) ⟶
      (abelianSheaf W.toScheme).obj ((Scheme.Modules.restrictFunctor W.ι).obj G) :=
  (abelianRestrict W).map ψ

/-- **Restriction of the underlying morphism of a morphism of modules is the underlying morphism
of its restriction.**  True by definition, both being `φ` over the opens `W.ι ''ᵁ U`. -/
theorem restrictAbHom_abelianSheaf_map {F G : Y.Modules} (φ : F ⟶ G) :
    restrictAbHom W ((abelianSheaf Y).map φ) =
      (abelianSheaf W.toScheme).map ((Scheme.Modules.restrictFunctor W.ι).map φ) := rfl

/-! ### The derived excision is natural in the coefficient module -/

section Naturality

variable {T : Set Y} (hT : IsClosed T) (hTW : IsClosed (W.ι ⁻¹' T))

/-- Three naturality squares pasted along a three-factor composite.  Stated at an arbitrary
category. -/
private theorem paste3 {D : Type*} [Category* D] {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : D}
    (x : a₀ ⟶ b₀) (A : a₀ ⟶ a₁) (B : a₁ ⟶ a₂) (C : a₂ ⟶ a₃)
    (A' : b₀ ⟶ b₁) (B' : b₁ ⟶ b₂) (C' : b₂ ⟶ b₃)
    (y : a₁ ⟶ b₁) (z : a₂ ⟶ b₂) (t : a₃ ⟶ b₃)
    (h1 : x ≫ A' = A ≫ y) (h2 : y ≫ B' = B ≫ z) (h3 : z ≫ C' = C ≫ t) :
    x ≫ A' ≫ B' ≫ C' = (A ≫ B ≫ C) ≫ t := by
  rw [reassoc_of% h1, reassoc_of% h2, h3]
  simp

/-- **The derived excision of [Stacks, Tag 0G78] on degree-`n` cohomology sheaves is natural in
the coefficient module**, in the `AlgebraicGeometry.Scheme.Modules.restrictFunctor` spelling the
equation charts of [Stacks, Tag 0G86] use.

`Stacks.Gysin.supportCohomologyRestrictIso` is three factors: the identification of the pullback
of modules along the ringed-space inclusion with `restrictFunctor`, inverted; the excision
`Stacks.Gysin.supportCohomologyPullbackIso` in the pullback spelling, whose naturality is
`Stacks.Gysin.supportCohomologyPullbackIso_naturality`; and that identification again, under
`Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor`.  Each is natural, and the
three squares paste. -/
theorem supportCohomologyRestrictIso_naturality (n : ℤ) {M N : Y.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.restrictFunctor W.ι).map (supportCohomologySheafMap hT φ n) ≫
        (supportCohomologyRestrictIso W hT hTW n N).hom =
      (supportCohomologyRestrictIso W hT hTW n M).hom ≫
        supportCohomologySheafMap hTW ((Scheme.Modules.restrictFunctor W.ι).map φ) n := by
  have h1 := (modulePullbackRestrictFunctorIso W).inv.naturality
    (supportCohomologySheafMap hT φ n)
  have h2 := supportCohomologyPullbackIso_naturality
    (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) T hT n φ
  have h3 := map_square (supportCohomologySheafFunctor hTW n) _ _ _ _
    ((modulePullbackRestrictFunctorIso W).hom.naturality φ)
  exact paste3 _ _ _ _ _ _ _ _ _ _ h1 h2 h3

/-! ### The abelian reading of the excision -/

/-- **The abelian reading of the derived excision**: the underlying morphism of abelian sheaves of
`Stacks.Gysin.supportCohomologyRestrictIso`.  Its source is the abelian restriction to `W` of the
underlying abelian sheaf of `i_*ℋ ⁿ_T(ℱ)`, by
`Stacks.Gysin.restrictFunctorCompAbelianSheafIso`. -/
def supportCohomologyRestrictAbHom (n : ℤ) (F : Y.Modules) :
    (abelianRestrict W).obj ((abelianSheaf Y).obj (supportCohomologySheaf hT F n)) ⟶
      (abelianSheaf W.toScheme).obj
        (supportCohomologySheaf hTW ((Scheme.Modules.restrictFunctor W.ι).obj F) n) :=
  (abelianSheaf W.toScheme).map (supportCohomologyRestrictIso W hT hTW n F).hom

/-- **The abelian reading of the excision, conjugated into the spelling of [Stacks, Tag 0G74]
part (2).**  Both ends are the *abelian* local cohomology sheaves
`Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward`, which is the functor the
action `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap` is a conjugation of.
It is defined only at the underlying abelian sheaf of a module, the excision it comes from being
an isomorphism of modules. -/
def excisionAbComparison (n : ℕ) (F : Y.Modules) :
    (abelianRestrict W).obj
        ((abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).obj
          ((abelianSheaf Y).obj F)) ⟶
      (abelianLocalCohomologyPushforward W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW n).obj
        ((abelianRestrict W).obj ((abelianSheaf Y).obj F)) :=
  (abelianRestrict W).map ((supportCohomologySheafForgetIso hT n).inv.app F) ≫
    supportCohomologyRestrictAbHom W hT hTW (n : ℤ) F ≫
      (supportCohomologySheafForgetIso hTW n).hom.app
        ((Scheme.Modules.restrictFunctor W.ι).obj F)

/-- **The compatibility the square of [Stacks, Tag 0G87] needs**: the abelian reading of the
derived excision commutes with the action of [Stacks, Tag 0G74] part (2) on a morphism `ψ` of the
underlying abelian sheaves.

For `ψ` the underlying morphism of a morphism of modules this holds, by
`Stacks.Gysin.supportCohomologyRestrictAbNatural_abelianSheaf_map`; the case the chart transport
of [Stacks, Tag 0G87] needs is `ψ` the de Rham differential of `X/S`, which is `𝒪_X`-linear for
no `X`. -/
def SupportCohomologyRestrictAbNatural (n : ℕ) {F G : Y.Modules}
    (ψ : (abelianSheaf Y).obj F ⟶ (abelianSheaf Y).obj G) : Prop :=
  restrictAbHom W (supportCohomologySheafAbelianMap hT n ψ) ≫
      supportCohomologyRestrictAbHom W hT hTW (n : ℤ) G =
    supportCohomologyRestrictAbHom W hT hTW (n : ℤ) F ≫
      supportCohomologySheafAbelianMap hTW n (restrictAbHom W ψ)

/-- **The compatibility holds on the underlying morphism of a morphism of modules.**  Both abelian
actions are then the actions of `Stacks.Perfect.SupportedFraction.supportCohomologySheafMap`, by
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap_map`, so the square is
`Stacks.Gysin.supportCohomologyRestrictIso_naturality` pushed through the forgetful functor. -/
theorem supportCohomologyRestrictAbNatural_abelianSheaf_map (n : ℕ) {F G : Y.Modules}
    (φ : F ⟶ G) :
    SupportCohomologyRestrictAbNatural W hT hTW n ((abelianSheaf Y).map φ) := by
  change restrictAbHom W (supportCohomologySheafAbelianMap hT n ((abelianSheaf Y).map φ)) ≫ _ = _
  rw [Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap_map,
    restrictAbHom_abelianSheaf_map, restrictAbHom_abelianSheaf_map,
    Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafAbelianMap_map]
  exact map_square (abelianSheaf W.toScheme) _ _ _ _
    (supportCohomologyRestrictIso_naturality W hT hTW (n : ℤ) φ)

/-! ### What remains -/

/-- The action of [Stacks, Tag 0G74] part (2) is a conjugation of the abelian local cohomology
functor by `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso`, spelled out.  True
by definition, and recorded because it is what reduces
`Stacks.Gysin.SupportCohomologyRestrictAbNatural` to a naturality statement. -/
theorem supportCohomologySheafAbelianMap_eq (n : ℕ) {F G : Y.Modules}
    (ψ : (abelianSheaf Y).obj F ⟶ (abelianSheaf Y).obj G) :
    supportCohomologySheafAbelianMap hT n ψ =
      (supportCohomologySheafForgetIso hT n).hom.app F ≫
        (abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).map ψ ≫
          (supportCohomologySheafForgetIso hT n).inv.app G := rfl

/-- The restriction of that conjugation is the composite of the three restrictions. -/
theorem restrictAbHom_supportCohomologySheafAbelianMap (n : ℕ) {F G : Y.Modules}
    (ψ : (abelianSheaf Y).obj F ⟶ (abelianSheaf Y).obj G) :
    restrictAbHom W (supportCohomologySheafAbelianMap hT n ψ) =
      (abelianRestrict W).map ((supportCohomologySheafForgetIso hT n).hom.app F) ≫
        (abelianRestrict W).map
            ((abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).map ψ) ≫
          (abelianRestrict W).map ((supportCohomologySheafForgetIso hT n).inv.app G) :=
  (abelianRestrict W).map_comp₃ _ _ _

end Naturality

end Stacks.Gysin

end
