module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `f^{-1}ℐ · 𝒪_X` of a composite, at morphisms of ringed topoi

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed topoi and let `ℐ ⊂ 𝒪_Z` be a sheaf of
ideals. `InverseImageIdealSheafTopos.lean` builds `f^{-1}ℐ · 𝒪_X` as the image of `f^*ℐ ⟶ 𝒪'`.
This file proves that the construction is **functorial**:

`f^{-1}(g^{-1}ℐ · 𝒪_Y) · 𝒪_X = (g ∘ f)^{-1}ℐ · 𝒪_X`.

That is what the reduction of [Stacks, Tag 0A0G] to a morphism of ringed sites needs in order to
match the sheaves of ideals along the square of [Stacks, Tag 03CR]: the square expresses `f` as a
composite of a dense-subsite replacement, a site-presented morphism and a dense-subsite
restriction, and the ideal the ringed-sites case of the tag constructs at each arrow has to be the
one the previous arrow produced.

## Main results

* `Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_locallySurjective_comp`: **precomposing
  with a locally surjective morphism does not change the image subsheaf.** No hypothesis on the
  site and no abelian structure.
* `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso_hom_app_comp_pullbackUnitStructureMap`:
  **the comparison `f^*𝒪 ⟶ 𝒪'` of a composite**, read through the comparison
  `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` of pullbacks, is the comparison of `g`
  pulled back along `f` followed by that of `f`. This is the inverse-image counterpart of
  `AlgebraicGeometry.RingedToposHom.unitStructureMap_comp`, which is the direct-image form.
* `AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_comp`: **the composition law for
  `f^{-1}ℐ · 𝒪_X`**, with no hypothesis on `ℐ` and none on either morphism.

## Implementation notes

*The comparison of a composite.* `pullbackUnitStructureMap` is defined as the transpose of
`unitStructureMap` under [Stacks, Tag 03D7], and `pullbackModulesCompIso` is built by
`CategoryTheory.Adjunction.leftAdjointUniq` from the adjunction of the composite, transported
along `AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso`, and the composite of the two
adjunctions. So the coherence is proved by transposing: `Equiv.injective` reduces it to an
equation between adjuncts, `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` turns the
comparison of pullbacks into the unit of the composite adjunction, and what is left is
`unitStructureMap_comp` — whose statement carries exactly the `pushforwardModulesCompIso` factor
that `CategoryTheory.Adjunction.ofNatIsoRight` contributes, so the two cancel against one another
rather than having to be reconciled.

*Why one inclusion is not enough, and how the other is obtained.* Both sides of the composition
law are least ideals, so `inverseImageIdealSheaf_le_iff` gives one inclusion directly: the ideal
of the composite is received by the iterated one. The reverse needs that `f^*` of the image of
`g^*ℐ ⟶ 𝒪_Y` is no larger than the image of `f^*g^*ℐ ⟶ 𝒪_X`, which is not a universal property
but a statement about images. It comes from three facts: the factorisation of a map through its
image is locally surjective, hence an epimorphism
(`Stacks.SheafOfModules.ImageSubsheaf.epi_toImage`, hypothesis-free); `f^*` is a left adjoint and
so preserves epimorphisms (`CategoryTheory.Functor.preservesEpimorphisms_of_adjunction` at
`pullbackAdjPushforwardModules`); and an epimorphism of sheaves of modules over a site carrying
an abelian structure is locally surjective
(`Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi`). Then
`imageSubmodule_locallySurjective_comp` discards the epimorphism and the two images coincide.
The proof is therefore a single computation rather than a double inclusion.

`imageSubmodule_locallySurjective_comp` is stated for a locally surjective morphism rather than
for an epimorphism on purpose: in that form it needs no abelian structure, and the abelian
structure is introduced only where it is actually used, in the composition law, where instance
search finds it from the standing sheafification hypotheses.

## Deliberately untagged

Functoriality of the construction of `f^{-1}ℐ · 𝒪_X` is not a numbered statement of the Stacks
Project; Section 52.7 introduces the ideal sheaf in passing. The pseudo-functoriality of the
pullback itself is [Stacks, Tag 03D6] part (2) and is registered on
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`, which this file consumes.

## References

* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u' t v₁ u₁ w₁ v₂ u₂ w₂ v₃ u₃ w₃ u

namespace Stacks.SheafOfModules.ImageSubsheaf

section LocallySurjective

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N M' : SheafOfModules.{t} R}

/-- **Precomposing with a locally surjective morphism does not change the image subsheaf.**
If `e : M' ⟶ M` is locally surjective then `e ≫ φ` and `φ` have the same image in the target.

Only the subobject of the target matters, and a section of the target which locally lies in the
range of `φ` lies locally in the range of `e ≫ φ` as well: refine the covering witnessing
membership by the covering on which a given section of `M` is hit by `e`. No hypothesis on the
site, and in particular no abelian structure: the epimorphism form of the statement is obtained
where it is needed by composing this with
`Stacks.SheafOfModules.ImageSubsheaf.isLocallySurjective_of_epi`. -/
theorem imageSubmodule_locallySurjective_comp (e : M' ⟶ M)
    (he : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map e.val))
    (f : M ⟶ N) :
    imageSubmodule (e ≫ f) = imageSubmodule f := by
  refine le_antisymm (imageSubmodule_le _ fun X m ↦
      apply_mem_imageSubmodule f (PresheafOfModules.Hom.app e.val X m))
    (imageSubmodule_le f fun X m ↦ ?_)
  change (rangeSubmodule (e ≫ f)).toSubfunctor.sieveOfSection
      (PresheafOfModules.Hom.app f.val X m) ∈ J X.unop
  refine J.superset_covering ?_ (he.imageSieve_mem m)
  intro V g hg
  obtain ⟨m', hm'⟩ := hg
  exact ⟨m', (congrArg (PresheafOfModules.Hom.app f.val (op V)) hm').trans
    (PresheafOfModules.naturality_apply f.val g.op m)⟩
end LocallySurjective

end Stacks.SheafOfModules.ImageSubsheaf

namespace AlgebraicGeometry.RingedToposHom

section UnitComparison

variable {X : RingedTopos.{v₁, u₁, w₁}} {Y : RingedTopos.{v₂, u₂, w₂}}
  {Z : RingedTopos.{v₃, u₃, w₃}}
  [X.J.HasSheafCompose (forget RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget RingCat.{w₂})]
  [Z.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w₃})]
  [HasWeakSheafify X.J AddCommGrpCat.{w₁}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w₂}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w₂}]

/-- **The comparison `f^*𝒪 ⟶ 𝒪'` of a composite of morphisms of ringed topoi.** Read through the
comparison `AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` of the pullback of a
composite with the composite of the pullbacks, the comparison attached to `g ∘ f` is the
comparison of `g` pulled back along `f`, followed by the comparison of `f`.

This is the inverse-image counterpart of
`AlgebraicGeometry.RingedToposHom.unitStructureMap_comp`, and it is proved from it by
transposing under [Stacks, Tag 03D7]; see the module documentation for why the
`pushforwardModulesCompIso` factor that statement carries is exactly what the transposition
needs. -/
theorem pullbackModulesCompIso_hom_app_comp_pullbackUnitStructureMap
    (g : RingedToposHom Y Z) (f : RingedToposHom X Y) :
    (pullbackModulesCompIso f g).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ≫
        (f.toModulesHom.pullbackModules).map (pullbackUnitStructureMap g) ≫
          pullbackUnitStructureMap f =
      pullbackUnitStructureMap (g.comp f) := by
  set psi := (f.toModulesHom.pullbackModules).map (pullbackUnitStructureMap g) ≫
    pullbackUnitStructureMap f with hpsidef
  have hpsi : ((pullbackAdjPushforwardModules g).comp
        (pullbackAdjPushforwardModules f)).homEquiv _ _ psi =
      unitStructureMap g ≫ (pushforwardModules g).map (unitStructureMap f) := by
    rw [hpsidef, Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left, homEquiv_pullbackUnitStructureMap,
      Adjunction.homEquiv_naturality_right, homEquiv_pullbackUnitStructureMap]
  have hAB : ((pullbackAdjPushforwardModules (g.comp f)).ofNatIsoRight
          (pushforwardModulesCompIso f g)).homEquiv _ _
        ((pullbackModulesCompIso f g).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ≫ psi) =
      ((pullbackAdjPushforwardModules g).comp
        (pullbackAdjPushforwardModules f)).homEquiv _ _ psi := by
    rw [Adjunction.homEquiv_naturality_right,
      show (pullbackModulesCompIso f g).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) =
        (Adjunction.leftAdjointUniq
          ((pullbackAdjPushforwardModules (g.comp f)).ofNatIsoRight
            (pushforwardModulesCompIso f g))
          ((pullbackAdjPushforwardModules g).comp
            (pullbackAdjPushforwardModules f))).hom.app _ from rfl,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]
  apply ((pullbackAdjPushforwardModules (g.comp f)).homEquiv _ _).injective
  refine Eq.trans ?_ (homEquiv_pullbackUnitStructureMap (g.comp f)).symm
  rw [← cancel_mono ((pushforwardModulesCompIso f g).hom.app
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))]
  refine Eq.trans ?_ (unitStructureMap_comp g f).symm
  rw [← Adjunction.homEquiv_ofNatIsoRight_apply, hAB, hpsi]
end UnitComparison

section Composition

open Stacks.SheafOfModules.ImageSubsheaf

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The canonical map `f^*ℐ ⟶ 𝒪'` written out, for rewriting. -/
theorem inverseImageIdealMap_eq (f : RingedToposHom X Y)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    inverseImageIdealMap.{u} f I =
      (f.toModulesHom.pullbackModules).map I.ι ≫ pullbackUnitStructureMap f := rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `f^{-1}ℐ · 𝒪_X` is the image subsheaf of the canonical map, written out, for rewriting. -/
theorem inverseImageIdealSheaf_eq (f : RingedToposHom X Y)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    inverseImageIdealSheaf.{u} f I = imageSubmodule (inverseImageIdealMap.{u} f I) := rfl

omit [HasWeakSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The factorisation of the canonical map through `f^{-1}ℐ · 𝒪_X` is the factorisation of a map
through its image, written out, for transporting the epimorphism instance. -/
theorem idealMapFactorThru_eq (f : RingedToposHom X Y)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    idealMapFactorThru.{u} f I = toImage (inverseImageIdealMap.{u} f I) := rfl

/-- **The construction `ℐ ↦ f^{-1}ℐ · 𝒪_X` is functorial**, for arbitrary morphisms of ringed
topoi `f : X ⟶ Y` and `g : Y ⟶ Z`: forming the ideal sheaf of `g` and then that of `f` gives the
ideal sheaf of `g ∘ f`. No hypothesis on `ℐ`, none on `f` and none on `g`.

This is what matches the sheaves of ideals along the square of [Stacks, Tag 03CR] in the
reduction of [Stacks, Tag 0A0G] to a morphism of ringed sites. The proof is one computation, not
a double inclusion: the canonical map of the composite is the canonical map of `f` at the ideal
of `g`, precomposed with `f^*` of the factorisation of `g`'s canonical map through its image and
with the comparison of pullbacks. The first of those is locally surjective and the second is an
isomorphism, and the image subsheaf is insensitive to both, by
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_locallySurjective_comp` and
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp`. -/
@[sga "3 III 0.1.4" "more general"]
theorem inverseImageIdealSheaf_comp (g : RingedToposHom Y Z) (f : RingedToposHom X Y)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    inverseImageIdealSheaf.{u} f (inverseImageIdealSheaf.{u} g I) =
      inverseImageIdealSheaf.{u} (g.comp f) I := by
  have : (f.toModulesHom.pullbackModules).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (pullbackAdjPushforwardModules f)
  have hepi : Epi (idealMapFactorThru.{u} g I) :=
    Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
      (isLocallySurjective_toImage (inverseImageIdealMap.{u} g I))
  set e := (f.toModulesHom.pullbackModules).map (idealMapFactorThru.{u} g I) with hedef
  have hkey : (pullbackModulesCompIso f g).hom.app I.toSheafOfModules ≫
      e ≫ (f.toModulesHom.pullbackModules).map (inverseImageIdealSheaf.{u} g I).ι ≫
        pullbackUnitStructureMap f =
      ((g.comp f).toModulesHom.pullbackModules).map I.ι ≫ pullbackUnitStructureMap (g.comp f) := by
    rw [← pullbackModulesCompIso_hom_app_comp_pullbackUnitStructureMap g f]
    simp only [← Category.assoc]
    congr 1
    rw [hedef, Category.assoc, ← CategoryTheory.Functor.map_comp, idealMapFactorThru_ι,
      inverseImageIdealMap_eq, CategoryTheory.Functor.map_comp, ← Category.assoc]
    congr 1
    exact ((pullbackModulesCompIso f g).hom.naturality I.ι).symm
  have hiso : (pullbackModulesCompIso f g).hom.app I.toSheafOfModules =
      ((pullbackModulesCompIso f g).app I.toSheafOfModules).hom := rfl
  rw [inverseImageIdealSheaf_eq (g.comp f) I, inverseImageIdealMap_eq (g.comp f) I, ← hkey,
    hiso, imageSubmodule_iso_hom_comp ((pullbackModulesCompIso f g).app I.toSheafOfModules),
    imageSubmodule_locallySurjective_comp e (isLocallySurjective_of_epi e),
    inverseImageIdealSheaf_eq f (inverseImageIdealSheaf.{u} g I),
    inverseImageIdealMap_eq f (inverseImageIdealSheaf.{u} g I)]

end Composition

end AlgebraicGeometry.RingedToposHom

end
