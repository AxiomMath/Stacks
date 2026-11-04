module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionMulShape
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# Multiplication by a global section of `𝒪(1)`, pulled back along a morphism

`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape.mulSection` multiplies an `𝒪`-module on
`ℙⁿ_S` by a global section `s` of `𝒪(1)`: it is the arrow `ℳ ⟶ ℳ ⊗ 𝒪(1)` built from the right
unitor and from `s` read as a morphism `𝒪 ⟶ 𝒪(1)` out of the monoidal unit. This file proves that
**it is carried to multiplication by the restricted section by any pullback**: for a morphism of
schemes `g : ℙᵐ_S ⟶ ℙⁿ_S` and an identification `θ : g^*(𝒪_{ℙⁿ}(1)) ≅ 𝒪_{ℙᵐ}(1)`,

`g^*(s · -) ≫ (01CD) ≫ (- ⊗ θ) = (σ · -)`,

where `σ` is the restriction of `s` along `(g, θ)`. No hypothesis is needed beyond `θ`: the
comparison of [Stacks, Tag 01CD] and its compatibility with the right unitor are all that enter.

This is one of the two halves that the square of sheaves of [Stacks, Tag 08A7] is missing — see
the "What remains" section of
`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneRestrictionPackageConstruction.lean`,
where it is recorded as `j^*(mulSection ℳ σ') = mulSection (j^*ℳ) σ ≫ (monoidal comparison)`.

## Main results

* `Stacks.AlgebraicGeometry.PullbackSectionMul.pullbackTensorComparison_mulSection`: **the square
  on a morphism of ringed spaces**, for multiplication by an arbitrary morphism `τ : 𝟙_ ⟶ ℒ` out
  of the monoidal unit. The pulled-back multiplier is `ε⁻¹ ≫ f^*τ`, with `ε` the structure-sheaf
  comparison of `f^*`.
* `…pullbackTensorComparison_mulSection_comp`: the same with an identification of `f^*ℒ` composed
  on.
* `…pullback_mulSection`: **the square for
  `Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape.mulSection` on `ℙⁿ_S`**, for a section
  `t` of `𝒪_{ℙᵐ}(1)` that is the restriction of `s` along `(g, θ)`.
* `…exists_pullback_mulSection`: every global section of `𝒪(1)` upstairs **has** such a
  restriction, so the square holds for it, uniformly in the module.

## The mathematics

There is none beyond the coherence of [Stacks, Tag 01CD]: `mulSection ℳ s` is
`(ρ_ ℳ)⁻¹ ≫ ℳ ◁ (s : 𝟙_ ⟶ 𝒪(1))`, and `f^*` carries the right unitor and a left whiskering to
the right unitor and a left whiskering of the pullbacks, through the comparison
`f^*(𝒜 ⊗ ℬ) ⟶ f^*𝒜 ⊗ f^*ℬ`. Both compatibilities are available —
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_rightUnitor` and
`…_naturality_right` — so the proof is the two of them composed, the structure-sheaf comparison
being invertible.

## Implementation notes

**Which monoidal structure, and the bridge this file owes to it.** The repository carries three
monoidal structures on the `𝒪_X`-modules of a scheme, listed in the implementation notes of
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPowerPullbackMul.lean`. The coherences of
[Stacks, Tag 01CD] live in the third, `Stacks.PullbackGradedAlgebra.monoidalCategory`, whose
tensor product is the tensor product sheaf and whose structural morphisms are the localized ones
conjugated by `Stacks.SheafOfModules.tensorObjIso`;
`…ProjectiveSpaceSectionMulShape.mulSection` is written in
`Stacks.SheafOfModules.sheafTensorMonoidal`, whose tensor product is **the same sheaf** but whose
unitors are the fixed constraints `Stacks.SheafOfModules.Invertible.tensorProduct…` and whose
whiskerings are `Stacks.SheafOfModules.sheafifyWhiskerLeft`. The two are *not* definitionally
equal, but every structural morphism of the one equals the corresponding morphism of
the other, by `Stacks.SheafOfModules.tensorObjIso_rightUnitor` against the right unitor of
`Stacks.SheafOfModules.Strict.monoidalCategoryStruct` and by
`Stacks.SheafOfModules.sheafifyWhiskerLeft_eq_comparison` against `…Strict.whiskerLeft_eq`. That
bridge is `tensorProductRightUnitor_eq` and `sheafifyWhiskerLeft_eq_whiskerLeft` below, and
`mulSection_eq` is what it buys: `mulSection` written in the structure the coherences are
available in. This is the bridge recorded as missing at
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/TwistSquare.lean` ("the whiskerings are not
bridged to this one"), for the whiskering and the right unitor — which is all the statement
proved here uses.

**Why `rw` is not used to cross the two spellings.** `A ⊗ B` of the third structure and
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` are equal by `rfl` but not
syntactically, so a goal mixing them is not type-correct at `implicit` transparency and `rw`
refuses it, reporting a pattern rather than the cause — the failure mode this directory records.
Each crossing is therefore made once, inside a proof given by `:=` or `exact`, which are
defeq-tolerant: `mulSection_eq` is two `congrArg`s, and `pullback_mulSection` finishes with
`exact` on the ringed-space statement.

**`schemeTensorStrict`.** The structure of [Stacks, Tag 01CA] has to be named at the `X.Modules`
spelling for `ρ_` and `◁` to elaborate there at all: instance search does not unify
`Stacks.RingedSpace.structureRingSheaf ?Z` with `X.ringCatSheaf`. It is the same structure as
`Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace`, by `rfl`, and like it is not a
global instance — `Stacks.SheafInternalHom.schemeMonoidalCategory` is a *different* structure on
the same category.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)

## What is not done here

**The restricted section is not identified with `AlgebraicGeometry.pullbackGlobalSections`.**
`exists_pullback_mulSection` produces the restriction of `s` as the global section corresponding
to `ε⁻¹ ≫ g^*(s) ≫ θ` under `SheafOfModules.unitHomEquiv`, which is what the square is about and
is all it needs. That it is also the image of `s` under
`AlgebraicGeometry.pullbackGlobalSections` followed by `θ` — i.e. the *geometric* restriction, the
form in which a surjectivity statement for degree-one forms supplies it — is not proved here. The
same bridge for the *other* unit comparison is proved:
`Stacks.PullbackUnitSection.pullbackSectionHom_globalSection`
(`StacksFrontier/AlgebraicGeometry/SectionProduct/PullbackUnitSection.lean`) identifies the two for
`Stacks.PullbackUnitSection.unitPullbackHom`, the structure-sheaf comparison read in
`Stacks.SheafInternalHom.schemeMonoidalCategory`. That is a *different* monoidal structure from
the one used here, so what is owed is the transport of that bridge to
`Stacks.PullbackTensorCoherence.pullbackUnitComparison` — the same kind of spelling bridge as the
two proved above, not a new piece of mathematics.

**Nothing is proved about
`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul`**, which is
`mulSection` followed by the associator and by the regrouping `𝒪(d) ⊗ 𝒪(1) ≅ 𝒪(d + 1)`. Pulling
*that* back needs, besides the associator coherence (which is proved, as
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_associator`), a family
`θ_d : g^*(𝒪(d)) ≅ 𝒪(d)` over all of `ℤ` compatible with the regrouping isomorphisms; the
multiplicativity of the comparison is available only for the nonnegative powers of
`Stacks.TensorPowerPullbackMul.powModules`
(`Stacks.TensorPowerPullbackMul.pullbackPowModulesIso_powModulesAdd`), and its own file records
that the same square for `Stacks.Ample.tensorPowModuleAddIso` — the addition law the twists are
built from — is not proved anywhere.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules (sheafifyWhiskerLeft)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication (sectionHom)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape (mulSection)
open Stacks.RelativeVeryAmple (tensorModulesMapIso pullbackTensorModulesIso)

universe v u w

namespace Stacks.AlgebraicGeometry.PullbackSectionMul

/-! ### The fixed constraints of [Stacks, Tag 01CA] are those of the strict structure -/

section Bridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The fixed right unit constraint of the tensor product sheaf is the right unitor of
`Stacks.SheafOfModules.Strict.monoidalCategory`.** Both are the localized right unitor
precomposed with `Stacks.SheafOfModules.tensorObjIso`, which is what
`Stacks.SheafOfModules.tensorObjIso_rightUnitor` says; the strict right unitor *is* that
composite, so moving the comparison across it is the whole proof. -/
theorem tensorProductRightUnitor_hom_eq
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor O hO M).hom =
      (MonoidalCategoryStruct.rightUnitor
        (self := Stacks.SheafOfModules.Strict.monoidalCategoryStruct O hO) M).hom :=
  (Iso.eq_inv_comp (Stacks.SheafOfModules.tensorObjIso O hO M
    (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))).mpr
      (Stacks.SheafOfModules.tensorObjIso_rightUnitor O hO M)

/-- **Whiskering the sheaf tensor product on the left is left whiskering in
`Stacks.SheafOfModules.Strict.monoidalCategory`.** Both are the localized whiskering conjugated
by `Stacks.SheafOfModules.tensorObjIso`. -/
theorem sheafifyWhiskerLeft_eq_whiskerLeft
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    {N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (g : N ⟶ N') :
    sheafifyWhiskerLeft O hO M g =
      MonoidalCategoryStruct.whiskerLeft
        (self := Stacks.SheafOfModules.Strict.monoidalCategoryStruct O hO) M g := by
  rw [Stacks.SheafOfModules.Strict.whiskerLeft_eq,
    Stacks.SheafOfModules.sheafifyWhiskerLeft_eq_comparison]

end Bridge

/-- **The monoidal structure of [Stacks, Tag 01CA] on the `𝒪_X`-modules of a scheme**, named at
the `X.Modules` spelling. This is `Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace`
by `rfl`; it has to be named here because instance search does not unify
`Stacks.RingedSpace.structureRingSheaf ?Z` with `X.ringCatSheaf`. Deliberately not a global
instance: `Stacks.SheafInternalHom.schemeMonoidalCategory` is a different monoidal structure on
the same category. -/
abbrev schemeTensorStrict (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace

attribute [local instance] schemeTensorStrict

/-- `Stacks.SheafOfModules.Invertible.tensorProductRightUnitor` on a scheme **is** the right
unitor of [Stacks, Tag 01CA]. -/
theorem tensorProductRightUnitor_eq (X : Scheme.{u}) (M : X.Modules) :
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M = ρ_ M :=
  Iso.ext (tensorProductRightUnitor_hom_eq _ _ M)

private theorem rightUnitor_inv_eq (X : Scheme.{u}) (M : X.Modules) :
    (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M).inv = (ρ_ M).inv :=
  congrArg Iso.inv (tensorProductRightUnitor_eq X M)

/-- `Stacks.RelativeVeryAmple.tensorModulesMapIso` with the identity on the left **is** left
whiskering for [Stacks, Tag 01CA].

`Stacks.RelativeVeryAmple.tensorModulesMapIso` is the composite of the two legs of the curried
bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`, so at the identity in the first variable
its left leg is the functor applied to `𝟙`: it is the identity by
`CategoryTheory.Functor.map_id`, read at `B`, and what is left is the right leg, which is the
whiskering. -/
theorem tensorModulesMapIso_refl_hom (X : Scheme.{u}) (A : X.Modules) {B B' : X.Modules}
    (e : B ≅ B') : (tensorModulesMapIso X (Iso.refl A) e).hom = A ◁ e.hom := by
  have identityLeg := congrArg (fun naturality ↦ NatTrans.app naturality B)
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)⟩).map_id A)
  exact (congrArg (fun leftLeg ↦ leftLeg ≫ _) identityLeg).trans
    ((Category.id_comp _).trans (sheafifyWhiskerLeft_eq_whiskerLeft _ _ A e.hom))

/-- **`…ProjectiveSpaceSectionMulShape.mulSection` written in the monoidal structure of
[Stacks, Tag 01CA]**: multiplication by `s` is the inverse right unitor followed by whiskering
with `s` read as a morphism out of the monoidal unit. -/
theorem mulSection_eq (n : ℕ) (S : Scheme.{u}) (M : (projectiveSpaceOver n S).Modules)
    (s : (twistOver n S 1).sections) :
    mulSection n S M s = (ρ_ M).inv ≫ M ◁ sectionHom (twistOver n S 1) s :=
  (congrArg (fun φ => φ ≫ sheafifyWhiskerLeft (projectiveSpaceOver n S).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver n S)) M
        (sectionHom (twistOver n S 1) s))
      (rightUnitor_inv_eq (projectiveSpaceOver n S) M)).trans
    (congrArg (fun ψ => (ρ_ M).inv ≫ ψ)
      (sheafifyWhiskerLeft_eq_whiskerLeft _ _ M (sectionHom (twistOver n S 1) s)))

/-! ### The square on a morphism of ringed spaces -/

section Pullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (M L : SheafOfModules.{u} (structureRingSheaf Y))

/-- The comparison of [Stacks, Tag 01CD] at the monoidal unit, solved out of its compatibility
with the right unitor. -/
private theorem pullbackTensorComparison_unit_eq :
    pullbackTensorComparison f M (𝟙_ (SheafOfModules.{u} (structureRingSheaf Y))) =
      (pullbackFunctor f).map (ρ_ M).hom ≫ (ρ_ ((pullbackFunctor f).obj M)).inv ≫
        ((pullbackFunctor f).obj M ◁ inv (pullbackUnitComparison f)) := by
  rw [pullbackTensorComparison_rightUnitor, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, ← MonoidalCategory.whiskerLeft_comp, IsIso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.comp_id]

/-- The inverse right unitor, pulled back and compared: the shape in which the unitor enters
multiplication by a section. -/
private theorem map_rightUnitor_inv_comp_comparison :
    (pullbackFunctor f).map (ρ_ M).inv ≫
        pullbackTensorComparison f M (𝟙_ (SheafOfModules.{u} (structureRingSheaf Y))) =
      (ρ_ ((pullbackFunctor f).obj M)).inv ≫
        ((pullbackFunctor f).obj M ◁ inv (pullbackUnitComparison f)) := by
  rw [pullbackTensorComparison_unit_eq, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- **Multiplication by a morphism out of the monoidal unit is carried by `f^*` to
multiplication by its pullback**, the comparison of [Stacks, Tag 01CD] mediating. The pulled-back
multiplier is `f^*τ` preceded by the inverse of the structure-sheaf comparison, which is the only
thing that can repair the source: `f^*` does not send the monoidal unit to the monoidal unit on
the nose. -/
theorem pullbackTensorComparison_mulSection
    (τ : 𝟙_ (SheafOfModules.{u} (structureRingSheaf Y)) ⟶ L) :
    (pullbackFunctor f).map ((ρ_ M).inv ≫ M ◁ τ) ≫ pullbackTensorComparison f M L =
      (ρ_ ((pullbackFunctor f).obj M)).inv ≫
        ((pullbackFunctor f).obj M ◁ (inv (pullbackUnitComparison f) ≫
          (pullbackFunctor f).map τ)) := by
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    pullbackTensorComparison_naturality_right, MonoidalCategory.whiskerLeft_comp,
    ← Category.assoc, map_rightUnitor_inv_comp_comparison, Category.assoc]

/-- `Stacks.AlgebraicGeometry.PullbackSectionMul.pullbackTensorComparison_mulSection` with an
identification `θ` of `f^*ℒ` composed on, which is the shape a comparison of twists leaves the
square in. -/
theorem pullbackTensorComparison_mulSection_comp
    {L' : SheafOfModules.{u} (structureRingSheaf X)}
    (τ : 𝟙_ (SheafOfModules.{u} (structureRingSheaf Y)) ⟶ L)
    (θ : (pullbackFunctor f).obj L ⟶ L') :
    (pullbackFunctor f).map ((ρ_ M).inv ≫ M ◁ τ) ≫ pullbackTensorComparison f M L ≫
        ((pullbackFunctor f).obj M ◁ θ) =
      (ρ_ ((pullbackFunctor f).obj M)).inv ≫
        ((pullbackFunctor f).obj M ◁ (inv (pullbackUnitComparison f) ≫
          (pullbackFunctor f).map τ ≫ θ)) := by
  rw [← Category.assoc, pullbackTensorComparison_mulSection, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Category.assoc]

end Pullback

/-! ### The square on projective space -/

section Projective

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- The restriction of a global section of `𝒪(1)` along `(g, θ)`, as the section whose morphism
out of the monoidal unit is `ε⁻¹ ≫ g^*(s) ≫ θ`. -/
private theorem exists_restriction_section (n m : ℕ) (S : Scheme.{u})
    (g : projectiveSpaceOver m S ⟶ projectiveSpaceOver n S)
    (θ : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1)
    (s : (twistOver n S 1).sections) :
    ∃ t : (twistOver m S 1).sections, sectionHom (twistOver m S 1) t =
      inv (pullbackUnitComparison g.toLRSHom.toShHom) ≫
        (Scheme.Modules.pullback g).map (sectionHom (twistOver n S 1) s) ≫ θ.hom :=
  ⟨_, Equiv.symm_apply_apply (twistOver m S 1).unitHomEquiv _⟩

/-- **Restriction along `g` carries multiplication by a global section `s` of `𝒪_{ℙⁿ}(1)` to
multiplication by its restriction `t`.** The two sides are compared by the comparison of
[Stacks, Tag 01CD] and the identification `θ : g^*(𝒪_{ℙⁿ}(1)) ≅ 𝒪_{ℙᵐ}(1)`, and `t` is a
restriction of `s` in the sense that `t`, read as a morphism out of the monoidal unit, is `s`
pulled back and transported by `θ`.

The hypothesis is exactly what `…exists_pullback_mulSection` discharges; nothing is assumed about
`g` beyond its being a morphism of schemes. -/
theorem pullback_mulSection (n m : ℕ) (S : Scheme.{u})
    (g : projectiveSpaceOver m S ⟶ projectiveSpaceOver n S)
    (M : (projectiveSpaceOver n S).Modules)
    (θ : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1)
    (s : (twistOver n S 1).sections) (t : (twistOver m S 1).sections)
    (hst : sectionHom (twistOver m S 1) t =
      inv (pullbackUnitComparison g.toLRSHom.toShHom) ≫
        (Scheme.Modules.pullback g).map (sectionHom (twistOver n S 1) s) ≫ θ.hom) :
    (Scheme.Modules.pullback g).map (mulSection n S M s) ≫
        (pullbackTensorModulesIso g M (twistOver n S 1)).hom ≫
        (tensorModulesMapIso (projectiveSpaceOver m S)
          (Iso.refl ((Scheme.Modules.pullback g).obj M)) θ).hom =
      mulSection m S ((Scheme.Modules.pullback g).obj M) t := by
  rw [tensorModulesMapIso_refl_hom, mulSection_eq, mulSection_eq, hst]
  exact pullbackTensorComparison_mulSection_comp g.toLRSHom.toShHom M (twistOver n S 1)
    (sectionHom (twistOver n S 1) s) θ.hom

/-- **Every global section of `𝒪_{ℙⁿ}(1)` has a restriction along `(g, θ)`, and restriction
intertwines the two multiplications uniformly in the module.** This is the half of the sheaf
square of [Stacks, Tag 08A7] that concerns multiplication by a degree-one form: the restriction
`t` depends only on `g`, `θ` and `s`, so one `t` serves every `ℳ` — which is what a statement
quantified over all twists `ℱ(d)` needs. -/
theorem exists_pullback_mulSection (n m : ℕ) (S : Scheme.{u})
    (g : projectiveSpaceOver m S ⟶ projectiveSpaceOver n S)
    (θ : (Scheme.Modules.pullback g).obj (twistOver n S 1) ≅ twistOver m S 1)
    (s : (twistOver n S 1).sections) :
    ∃ t : (twistOver m S 1).sections, ∀ M : (projectiveSpaceOver n S).Modules,
      (Scheme.Modules.pullback g).map (mulSection n S M s) ≫
          (pullbackTensorModulesIso g M (twistOver n S 1)).hom ≫
          (tensorModulesMapIso (projectiveSpaceOver m S)
            (Iso.refl ((Scheme.Modules.pullback g).obj M)) θ).hom =
        mulSection m S ((Scheme.Modules.pullback g).obj M) t := by
  obtain ⟨t, ht⟩ := exists_restriction_section n m S g θ s
  exact ⟨t, fun M => pullback_mulSection n m S g M θ s t ht⟩

end Projective

end Stacks.AlgebraicGeometry.PullbackSectionMul

end
