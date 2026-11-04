module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictionCalculus
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorSheafGlobalSections

/-!
# The sections of `F ⊗ Ω^i_{X/S}` over an object of `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)`, a sheaf of `𝒪_{X/S}`-modules `F` on the
small crystalline site and an `i : ℕ`.  The coefficient sheaf
`...SmallSite.tensorDifferentialFormsSheaf F i` of [Stacks, Tag 07LF] is the *crystalline
sheafification* of the sectionwise tensor product `W ↦ F(W) ⊗_{Γ(W, 𝒪)} Ω^i_{X/S}(W)`, so its
sections over an object `A = (U, T, δ)` are a priori only *locally* sums of pure tensors.  The
first equality of the source's computation of `Γ((X, T(n)_e, δ(n)), 𝓗)` asserts that over the
objects it uses they are honest tensors — that the sheafification unit

`F(A) ⊗_{Γ(T, 𝒪_T)} Ω^i_{X/S}(A) ⟶ Γ(A, F ⊗_{𝒪_{X/S}} Ω^i_{X/S})`

is bijective.  **This module carries that question from the crystalline site to the Zariski site
of the ambient scheme**, where it becomes a statement about one presheaf of modules on one scheme
and no longer mentions `Cris(X/S)` at all:

the crystalline sheafification unit of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` is bijective on the sections
over `A` **if and only if** the Zariski sheafification unit of `...SmallSite.tensorRestriction A F
i`, the restriction of that tensor product to the opens of `T`, is bijective on the sections over
`⊤`.

Both directions are proved and **no hypothesis on `F`, on `i` or on `A` is carried** — in
particular no affineness.  Affineness is what makes the Zariski side *true*; it is not needed to
make the two sides equivalent.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bijective_toSheafify_app_restrictOpenTop_iff` — **the reduction**, as an iff, read over the
  restriction `A|_T` of the object to the whole of its ambient scheme.
* `bijective_toSheafify_app_tensorDifferentialFormsPresheaf` — its useful direction, read over `A`
  itself: the crystalline unit is bijective over `A` as soon as the Zariski unit is bijective over
  `⊤`.
* `bijective_toSheafify_tensorRestriction_app_top` — the converse, also over `A` itself.
* `bijective_app_of_iso`, `bijective_uliftFunctor_map`, `bijective_uliftFunctor_map_iff`,
  `bijective_of_comp_right`, `bijective_comp` and `hom_comp_eq` — the transfers the proof runs on,
  stated for abelian presheaves on an arbitrary category, for an arbitrary morphism of abelian
  groups and for an arbitrary composite.

## What is and is not proved

**The bijectivity itself is not proved here, and no tag attribute is placed.**  What is proved is
that it is equivalent to the Zariski statement, which is the following, with `T` the ambient
divided power scheme of `A`:

> for `T` affine, the Zariski sheafification unit of the presheaf of `𝒪_T`-modules
> `W ↦ F(A|_W) ⊗_{Γ(W, 𝒪_T)} Ω^i_{X/S}(A|_W)` is bijective on the sections over `T`.

That presheaf is `...SmallSite.tensorRestriction A F i` and its associated sheaf
`...SmallSite.tensorRestrictionSheaf A F i` is quasi-coherent for a locally quasi-coherent `F`
(`...SmallSite.isQuasicoherentOnSite_tensorRestrictionSheaf`).  The Zariski statement itself is
**not proved here**, but it is no longer open in the library: the generic affine-chart argument
is `Stacks.AlgebraicGeometry.AffineChartLocalization.bijective_toSheafify_app_of_isAffineOpen`,
which proves it for any presheaf of modules that **localizes on the basic opens** of the affine
open, and `SmallSite/TensorRestrictionAffineChart.lean` runs that argument at
`...SmallSite.tensorRestriction`: `...SmallSite.tensorRestrictionLocalizes_of_forms` and
`...SmallSite.bijective_toSheafify_tensorRestriction_app_top_of_localizes` give the bijectivity
from the localization of the two factors, of which the `F` factor is discharged from
hypothesis (1) of [Stacks, Tag 07JN] by
`...SmallSite.restrictedLocalizes_coefficientRestriction` and the tensor step by
`...SmallSite.restrictedLocalizes_tensorObj`.

So exactly one statement is owed — **the restriction of `Ω^i_{X/S} = ⋀^i Ω_{X/S}` to `T`
localizes on the basic opens of `T`**, in the shape
`...SmallSite.RestrictedLocalizes A (restrictedModule A (crysDifferentialForms S i))` — and the
library has both of its ingredients.  The degree-one case for the presheaf of divided power
differentials is `Crystalline.isLocalizedModule_presheafRestrictₗ` of
`StacksFrontier/AlgebraicGeometry/Crystalline/DpDifferentialsAffineUnit.lean`, which is to be
transported to `Ω_{X/S}` along `Crystalline.GlobalCrystallineSituation.comparisonIso`, the
presheaf-level form of [Stacks, Tag 07IZ]; and the passage from degree one to degree `i` is
`IsLocalization.isLocalizedModule_of_exteriorPower` of
`StacksFrontier/LinearAlgebra/ExteriorPower/Localization.lean`, the sections of `Ω^i_{X/S}` being
the exterior power of those of `Ω_{X/S}` by `PresheafOfModules.extPowSections`.  Assembling those
two is not done anywhere.

The caveat recorded in the module documentation of `SmallSite/SheafifySections.lean` is respected
and is the reason the Zariski side is stated as a *sheafification unit* and not as a tensor
product of sections of sheaves: `F_T` is a Zariski sheaf but the restricted `Ω^i_{X/S}` is only a
presheaf, so `Γ(F_T ⊗ Ω^i|_T) ≅ Γ(F_T) ⊗ Γ(Ω^i|_T)` with the presheaf's sections on the right is
false in general, while the statement above — whose left-hand side is the *presheaf's* sections
over `T` and whose right-hand side is the *sheafification's* — is exactly the one the source's
first equality makes, and is the one that needs `T` affine.

Nothing here bears on inputs (1) and (2) of [Stacks, Tag 07LF]; both are already closed, by
`...SmallSite.vanishing07JJ_tensorDifferentialFormsSheaf` of
`SmallSite/TensorRestrictionVanishing.lean` and
`...SmallSite.hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf` of
`SmallSite/TensorSheafGlobalSections.lean`.  The remaining input is the level-`e` identification
of `...SmallSite.vanishing07LF_of_levelCosimplicialSectionsIso`, whose first equality is the
bijectivity reduced here.

## Implementation notes

The crystalline unit is read over `A.restrictOpen ⊤` first and transported to `A` afterwards,
along `...CrystallineThickening.isoRestrictOpenTop`.  Reading it over `A` directly is not
possible: the restriction functor `...CrystallineThickening.restrictOpenFunctor` lands on
`A.restrictOpen ⊤` at the top open, and the two objects are isomorphic but not equal.

`...SmallSite.restrictOpenTensorSheafIso` is spelled, as there, with
`sheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)` rather than with
`(tensorDifferentialFormsSheaf F i).obj`; the two are equal by `rfl`
(`...SmallSite.tensorDifferentialFormsSheaf_obj`), and the reason for the spelling is recorded in
the implementation notes of `SmallSite/TensorSheafGlobalSections.lean`.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe w v u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Three transfers of bijectivity -/

/-- The underlying function of a composite of morphisms of abelian groups is the composite of the
underlying functions. -/
theorem hom_comp_eq {M N P : AddCommGrpCat.{u}} (f : M ⟶ N) (g : N ⟶ P) :
    ConcreteCategory.hom (f ≫ g) =
      ConcreteCategory.hom g ∘ ConcreteCategory.hom f :=
  funext fun x ↦ ConcreteCategory.comp_apply f g x

/-- **The first factor of a bijective composite whose second factor is bijective is
bijective.** -/
theorem bijective_of_comp_right {M N P : AddCommGrpCat.{u}} (f : M ⟶ N) (g : N ⟶ P)
    (hg : Function.Bijective (ConcreteCategory.hom g))
    (hfg : Function.Bijective (ConcreteCategory.hom (f ≫ g))) :
    Function.Bijective (ConcreteCategory.hom f) :=
  (hg.of_comp_iff' _).1 (hom_comp_eq f g ▸ hfg)

/-- **A composite of bijective morphisms of abelian groups is bijective.** -/
theorem bijective_comp {M N P : AddCommGrpCat.{u}} (f : M ⟶ N) (g : N ⟶ P)
    (hf : Function.Bijective (ConcreteCategory.hom f))
    (hg : Function.Bijective (ConcreteCategory.hom g)) :
    Function.Bijective (ConcreteCategory.hom (f ≫ g)) :=
  (hom_comp_eq f g).symm ▸ hg.comp hf

/-- **A natural transformation of abelian presheaves is bijective over an object exactly when it
is bijective over an isomorphic one.**  Both legs of the naturality square are isomorphisms. -/
theorem bijective_app_of_iso {C : Type u} [Category.{v} C] {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (η : P ⟶ Q) {A B : C} (e : A ≅ B)
    (h : Function.Bijective (ConcreteCategory.hom (η.app (op A)))) :
    Function.Bijective (ConcreteCategory.hom (η.app (op B))) := by
  refine bijective_of_comp_right _ (Q.map e.hom.op) (ConcreteCategory.bijective_of_isIso _) ?_
  rw [← η.naturality e.hom.op]
  exact bijective_comp _ _ (ConcreteCategory.bijective_of_isIso _) h

/-- **Raising the universe of the sections preserves bijectivity** of a morphism of abelian
groups. -/
theorem bijective_uliftFunctor_map {M N : AddCommGrpCat.{u}} (f : M ⟶ N)
    (hf : Function.Bijective (ConcreteCategory.hom f)) :
    Function.Bijective (ConcreteCategory.hom (AddCommGrpCat.uliftFunctor.{u + 1, u}.map f)) :=
  ULift.map_bijective.2 hf

/-- **Raising the universe of the sections reflects bijectivity** of a morphism of abelian
groups, so the two bijectivity statements are the same statement. -/
theorem bijective_uliftFunctor_map_iff {M N : AddCommGrpCat.{u}} (f : M ⟶ N) :
    Function.Bijective (ConcreteCategory.hom (AddCommGrpCat.uliftFunctor.{u + 1, u}.map f)) ↔
      Function.Bijective (ConcreteCategory.hom f) :=
  ⟨ULift.map_bijective.1, bijective_uliftFunctor_map f⟩

/-! ### The reduction to the Zariski site of the ambient scheme -/

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
  (A : CrystallineThickening S)

/-- **The crystalline sheafification unit of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` is bijective on the
sections over the restriction `A|_T` of an object to the whole of its ambient scheme exactly when
the Zariski sheafification unit of the restricted presheaf tensor product is bijective on the
sections over `T`.**

The two units differ by the isomorphism `...SmallSite.restrictOpenTensorSheafIso`, which is what
`...SmallSite.whiskerLeft_toSheafify_comp_restrictOpenTensorSheafIso_hom` says, and by the
universe lift of the sections, which neither creates nor destroys bijectivity.  No hypothesis on
`F`, on `i` or on `A` is carried. -/
theorem bijective_toSheafify_app_restrictOpenTop_iff :
    Function.Bijective (ConcreteCategory.hom
        ((toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app
          (op (A.restrictOpen (⊤ : A.obj.thickening.target.scheme.Opens))))) ↔
      Function.Bijective (ConcreteCategory.hom
        ((toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
            (tensorRestriction A F i).presheaf).app
          (op (⊤ : A.obj.thickening.target.scheme.Opens)))) := by
  have hiso : Function.Bijective (ConcreteCategory.hom
      ((restrictOpenTensorSheafIso A F i).hom.app
        (op (⊤ : A.obj.thickening.target.scheme.Opens)))) :=
    ConcreteCategory.bijective_of_isIso _
  have key : (toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app
          (op (A.restrictOpen (⊤ : A.obj.thickening.target.scheme.Opens))) ≫
        (restrictOpenTensorSheafIso A F i).hom.app
          (op (⊤ : A.obj.thickening.target.scheme.Opens)) =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        ((toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
            (tensorRestriction A F i).presheaf).app
          (op (⊤ : A.obj.thickening.target.scheme.Opens))) := by
    have := NatTrans.congr_app
      (whiskerLeft_toSheafify_comp_restrictOpenTensorSheafIso_hom A F i)
      (op (⊤ : A.obj.thickening.target.scheme.Opens))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, tensorRestrictionSheafULiftUnit,
      Functor.whiskerRight_app] at this
    exact this
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hc := bijective_comp _ _ h hiso
    rw [key] at hc
    exact (bijective_uliftFunctor_map_iff _).1 hc
  · refine bijective_of_comp_right _ _ hiso ?_
    rw [key]
    exact bijective_uliftFunctor_map _ h

/-- **The sections over an object of the crystalline sheafification of
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` are the tensor product of the sections, as soon as that holds on the
Zariski site of the ambient scheme.**

Concretely: if the Zariski sheafification unit of the presheaf of `𝒪_T`-modules
`W ↦ F(A|_W) ⊗_{Γ(W, 𝒪_T)} Ω^i_{X/S}(A|_W)` is bijective on the sections over `T`, then

`F(A) ⊗_{Γ(T, 𝒪_T)} Ω^i_{X/S}(A) ⟶ Γ(A, F ⊗_{𝒪_{X/S}} Ω^i_{X/S})`

is bijective.  This is the first equality of the source's proof of [Stacks, Tag 07LF], carried
from the crystalline site to the ambient scheme; the hypothesis is where the affineness of `T`
is used, and it is not proved anywhere in the library.  **No tag attribute is placed.** -/
theorem bijective_toSheafify_app_tensorDifferentialFormsPresheaf
    (h : Function.Bijective (ConcreteCategory.hom
      ((toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          (tensorRestriction A F i).presheaf).app
        (op (⊤ : A.obj.thickening.target.scheme.Opens))))) :
    Function.Bijective (ConcreteCategory.hom
      ((toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app (op A))) :=
  bijective_app_of_iso _ (CrystallineThickening.isoRestrictOpenTop A)
    ((bijective_toSheafify_app_restrictOpenTop_iff F i A).2 h)

/-- **Conversely**, the Zariski statement follows from the crystalline one: the two are
equivalent over every object, with no hypothesis. -/
theorem bijective_toSheafify_tensorRestriction_app_top
    (h : Function.Bijective (ConcreteCategory.hom
      ((toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app (op A)))) :
    Function.Bijective (ConcreteCategory.hom
      ((toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          (tensorRestriction A F i).presheaf).app
        (op (⊤ : A.obj.thickening.target.scheme.Opens)))) :=
  (bijective_toSheafify_app_restrictOpenTop_iff F i A).1
    (bijective_app_of_iso _ (CrystallineThickening.isoRestrictOpenTop A).symm h)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
