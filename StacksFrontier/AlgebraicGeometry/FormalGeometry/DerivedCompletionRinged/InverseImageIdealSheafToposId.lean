module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposId

/-!
# `f^{-1}ℐ · 𝒪_X` at the identity morphism

The construction `ℐ ↦ f^{-1}ℐ · 𝒪_X` of Section 52.7 of the Stacks project is the identity at the
identity morphism of a ringed topos: `id^{-1}ℐ · 𝒪 = ℐ`. With the composition law
`AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_comp` and the 2-isomorphism invariance
`AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIdealSheaf_eq`, this is what lets a sheaf of
ideals be carried around a round trip of inverse equivalences of ringed topoi and come back
unchanged — which is how the square of [Stacks, Tag 03CR] is turned from a statement about the
dense-subsite *replacements* into one about the *restrictions*.

## The two ingredients

* `Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_ι`: the image subsheaf of the inclusion of a
  submodule is that submodule. One inclusion is the universal property, the other is that every
  section of a submodule is a value of its own inclusion. This is a general fact about image
  subsheaves that the development did not yet record.
* `AlgebraicGeometry.RingedToposHom.pullbackModulesIdIso`: the pullback of sheaves of modules
  along the identity morphism is the identity functor. This is
  `AlgebraicGeometry.RingedToposHom.pullbackModulesIsoId` at the identity morphism, whose two
  inputs are both `rfl` there: the direct image along the identity morphism of a ringed topos *is*
  the identity functor (`AlgebraicGeometry.RingedToposHom.id_toToposHom_pushforward`) and its
  structure map *is* the identity on underlying sheaves of sets
  (`AlgebraicGeometry.RingedToposHom.forgetRing_map_id_fSharp`).

As in the comparison of the site-level and topos-level constructions, the comparison
`id^*𝒪 ⟶ 𝒪` is not identified with anything: it is invertible, so it differs from the identity by
an automorphism of `𝒪`, and the image subsheaf does not see an automorphism of the unit object.

## Main results

* `AlgebraicGeometry.RingedToposHom.inverseImageIdealSheaf_id`: **`id^{-1}ℐ · 𝒪 = ℐ`**, with no
  hypothesis on `ℐ`.

## Deliberately untagged

Section 52.7 introduces `f^{-1}ℐ · 𝒪_X` in passing rather than as a numbered statement, and
nothing in this development of it carries an attribute.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w t v₁ u₁

namespace Stacks.SheafOfModules.ImageSubsheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{t} R}

/-- **The image subsheaf of the inclusion of a submodule is that submodule.** One inclusion is the
universal property `Stacks.SheafOfModules.ImageSubsheaf.exists_factorThru_iff_imageSubmodule_le`
applied to the identity factorisation; the other is that a section of a submodule is the value of
its own inclusion at itself, so it lies in the image by
`Stacks.SheafOfModules.ImageSubsheaf.apply_mem_imageSubmodule`. -/
theorem imageSubmodule_ι (N : M.Submodule) : imageSubmodule N.ι = N :=
  le_antisymm
    ((exists_factorThru_iff_imageSubmodule_le N.ι).1 ⟨𝟙 _, Category.id_comp _⟩)
    fun X x hx ↦ apply_mem_imageSubmodule N.ι (⟨x, hx⟩ : N.toSheafOfModules.val.obj X)

end Stacks.SheafOfModules.ImageSubsheaf

namespace AlgebraicGeometry.RingedToposHom

section Pullback

variable (X : RingedTopos.{v, u, w})
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The pullback of sheaves of modules along the identity morphism of a ringed topos is the
identity functor.** The direct image along it is the identity functor, by
`Stacks.Sheaves.RingedToposModules.pushforwardModulesIdIso`, so both the pullback and the identity
functor are left adjoint to the identity functor, and this is uniqueness of left adjoints. -/
def pullbackModulesIdIso :
    (RingedToposHom.id X).toModulesHom.pullbackModules ≅
      𝟭 (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  pullbackModulesIsoId (RingedToposHom.id X) (Iso.refl _) (forgetRing_map_id_fSharp X)

end Pullback

section Ideal

open Stacks.SheafOfModules.ImageSubsheaf

variable (X : RingedTopos.{u, u, u})
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The sections of the structure sheaf of a ringed topos commute, read at the `Stacks.ringSheaf`
spelling in which the sheaves of ideals below are stated. It is the same sheaf of rings as
`(Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)`, whose commutativity is
`AlgebraicGeometry.RingedSite.instIsMulCommutativeRingSheafObj`, but
`AlgebraicGeometry.RingedTopos.toRingedSite` is a reducible abbreviation for a structure literal
and instance search does not see through it; this is the usual gap, keyed around.
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_comp_unitIso` needs it. -/
local instance isMulCommutative_ringSheaf_obj (U : X.Cᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) :=
  ⟨⟨fun a b ↦ mul_comm (G := X.O.obj.obj U) a b⟩⟩

/-- The automorphism of `𝒪` by which the comparison `id^*𝒪 ⟶ 𝒪` of the identity morphism differs
from `AlgebraicGeometry.RingedToposHom.pullbackModulesIdIso` at the unit object. Both are
invertible, so they differ by an automorphism, and
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_comp_unitIso` does not see it. -/
def idUnitDiscrepancy :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  ((pullbackModulesIdIso X).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm ≪≫
    @asIso _ _ _ _ _ (isIso_pullbackUnitStructureMap (RingedToposHom.id X))

/-- **The comparison `id^*𝒪 ⟶ 𝒪` of the identity morphism is
`AlgebraicGeometry.RingedToposHom.pullbackModulesIdIso` at the unit object**, up to the
automorphism `AlgebraicGeometry.RingedToposHom.idUnitDiscrepancy` of `𝒪`. This is the definition
of that automorphism, rearranged. -/
theorem pullbackUnitStructureMap_id :
    pullbackUnitStructureMap (RingedToposHom.id X) =
      (pullbackModulesIdIso X).hom.app
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≫
        (idUnitDiscrepancy X).hom :=
  (((pullbackModulesIdIso X).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom_inv_id_assoc
    (pullbackUnitStructureMap (RingedToposHom.id X))).symm

/-- **The canonical map `id^*ℐ ⟶ 𝒪` of the identity morphism is the inclusion `ℐ ↪ 𝒪`**, up to
`AlgebraicGeometry.RingedToposHom.pullbackModulesIdIso` on the source and an automorphism of `𝒪`
on the target.

The comparison of pullbacks is used through its naturality at the inclusion `ℐ ↪ 𝒪`; what remains
is `AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap_id`. -/
theorem inverseImageIdealMap_id :
    inverseImageIdealMap.{u} (RingedToposHom.id X) I =
      (pullbackModulesIdIso X).hom.app I.toSheafOfModules ≫ I.ι ≫ (idUnitDiscrepancy X).hom := by
  change ((RingedToposHom.id X).toModulesHom.pullbackModules).map I.ι ≫
      pullbackUnitStructureMap (RingedToposHom.id X) =
    (pullbackModulesIdIso X).hom.app I.toSheafOfModules ≫
      ((𝟭 (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map I.ι ≫
        (idUnitDiscrepancy X).hom)
  rw [pullbackUnitStructureMap_id X]
  simp only [← Category.assoc]
  rw [(pullbackModulesIdIso X).hom.naturality I.ι]

/-- **`id^{-1}ℐ · 𝒪 = ℐ`**: the construction of Section 52.7 is the identity at the identity
morphism of a ringed topos, with no hypothesis on `ℐ`.

The canonical map `id^*ℐ ⟶ 𝒪` is the inclusion `ℐ ↪ 𝒪` precomposed with an isomorphism and
postcomposed with an automorphism of `𝒪`, by
`AlgebraicGeometry.RingedToposHom.inverseImageIdealMap_id`; the image subsheaf sees neither, by
`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_iso_hom_comp` and
`.imageSubmodule_comp_unitIso`; and the image subsheaf of the inclusion of a submodule is that
submodule, by `Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_ι`. -/
theorem inverseImageIdealSheaf_id :
    inverseImageIdealSheaf.{u} (RingedToposHom.id X) I = I := by
  refine Eq.trans (congrArg (fun m ↦ imageSubmodule m) (inverseImageIdealMap_id X I)) ?_
  refine Eq.trans (imageSubmodule_iso_hom_comp
    ((pullbackModulesIdIso X).app I.toSheafOfModules) _) ?_
  exact (imageSubmodule_comp_unitIso I.ι (idUnitDiscrepancy X)).trans (imageSubmodule_ι I)

end Ideal

end AlgebraicGeometry.RingedToposHom

end
