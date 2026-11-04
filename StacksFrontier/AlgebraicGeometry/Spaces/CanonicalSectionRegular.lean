module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor

/-!
# The canonical section of an effective Cartier divisor is regular

Let `X` be an algebraic space over a scheme `S` and let `D ⊆ X` be an effective Cartier divisor,
so that its defining ideal sheaf `𝓘_D ⊆ 𝒪_X` is an invertible `𝒪_X`-module and
`𝒪_X(D) = 𝓘_D^{⊗ -1}` carries the canonical global section `1_D` of Stacks 0841.  Following
Stacks 0843 a global section of an `𝒪_X`-module is *regular* when multiplication by it is a
monomorphism from the structure sheaf; this file proves that `1_D` is regular, which is part (1)
of Stacks 0847.

## Main definitions

* `AlgebraicGeometry.Space.canonicalSectionHom` is multiplication by `1_D`, the morphism
  `𝒪_X ⟶ 𝒪_X(D)` whose monicity is the assertion that `1_D` is regular.
* `AlgebraicGeometry.Space.unitTensorPresheafIso` is the left unit constraint
  `𝒪_X ⊗ 𝓘_D ≅ 𝓘_D` of the tensor product of presheaves of `𝒪_X`-modules, and
* `AlgebraicGeometry.Space.unitTensorHom` is its sheafified companion
  `(𝒪_X ⊗ 𝓘_D)^# ⟶ 𝓘_D`, the morphism adjoint to it under sheafification.

## Main results

* `AlgebraicGeometry.Space.canonicalSection_isRegular` is **Stacks 0847, part (1)**: the
  canonical section `1_D` of `𝒪_X(D)` is a regular section.
* `AlgebraicGeometry.Space.map_canonicalSectionHom_comp_evaluation`: tensoring multiplication by
  `1_D` with `𝓘_D` and following it by the evaluation pairing `𝒪_X(D) ⊗ 𝓘_D ≅ 𝒪_X` recovers the
  inclusion `𝓘_D ⟶ 𝒪_X`, up to the unit constraint `𝒪_X ⊗ 𝓘_D ≅ 𝓘_D`.
* `AlgebraicGeometry.Space.isIso_unitTensorHom`: that unit constraint is an isomorphism of
  sheaves of modules.

## Implementation notes

Multiplication by `1_D` is monic because tensoring by the invertible sheaf `𝓘_D` is an
autoequivalence of `𝒪_X`-modules, hence reflects monomorphisms, and the tensored morphism is —
after the evaluation pairing `𝒪_X(D) ⊗ 𝓘_D ≅ 𝒪_X` of Stacks 0841 and the unit constraint
`𝒪_X ⊗ 𝓘_D ≅ 𝓘_D` — the inclusion `𝓘_D ⟶ 𝒪_X` of a sheaf submodule, which is monic for free.
So no local trivialization of `𝓘_D` is needed, and in particular the étale-local description of
a locally free module of rank one does not enter.

Both tensor products are taken at the level of presheaves of modules and then sheafified, as the
tensor product of sheaves of modules is in this library.  The comparison between the two levels is
`AlgebraicGeometry.Space.hom_ext_of_toSheafify`: a morphism out of a sheafification into a sheaf
is determined by its restriction along the unit of sheafification.  The relevant value of the
evaluation pairing on sections, `1_D ⊗ t ↦ t`, is read off from
`AlgebraicGeometry.Space.associatedInvertibleSheafHomEquiv_apply` and
`AlgebraicGeometry.Space.canonicalSection_apply`, which pin down `𝒪_X(D)` and `1_D` by that
pairing.

## References

* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 0843](https://stacks.math.columbia.edu/tag/0843)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite
open Stacks.PresheafOfModules.TensorInternalHom
open Stacks.SheafOfModules.Invertible
open Stacks.SheafOfModules.TensorSheafification (sheafify toSheafify sheafifyAdjunction)

namespace AlgebraicGeometry.Space

universe u

/-! ### Two cancellation lemmas in an arbitrary category -/

/-- A morphism which becomes, after composition with an isomorphism, an isomorphism followed by a
monomorphism, is itself a monomorphism. -/
private theorem mono_of_fac_of_isIso_of_mono {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) {e : X ⟶ Y} (he : IsIso e) {u : W ⟶ Z} (hu : IsIso u) {m : Z ⟶ Y}
    (hm : Mono m) (h : f ≫ e = u ≫ m) : Mono f := by
  have := he
  have := hu
  have := hm
  have hmc : Mono (u ≫ m) := mono_comp _ _
  rw [← h] at hmc
  exact mono_of_mono f e

/-- A faithful functor reflects monomorphisms. -/
private theorem mono_of_mono_map_of_faithful {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (hF : F.Faithful) {X Y : C} (f : X ⟶ Y) (h : Mono (F.map f)) : Mono f := by
  have := hF
  exact F.mono_of_mono_map h

/-! ### Multiplication by the canonical section -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (D : ClosedSubspaces B S hS X.1)
    (hD : IsEffectiveCartierDivisor B S hS X D)

/-- Multiplication by the canonical section `1_D`, as a morphism `𝒪_X ⟶ 𝒪_X(D)` of
`𝒪_X`-modules.  Stacks 0843 calls `1_D` regular exactly when this morphism is a
monomorphism. -/
noncomputable abbrev canonicalSectionHom :
    SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ associatedInvertibleSheaf B S hS X D hD :=
  (associatedInvertibleSheaf B S hS X D hD).unitHomEquiv.symm (canonicalSection B S hS X D hD)

/-- The evaluation pairing `𝒪_X(D) ⊗_{𝒪_X} 𝓘_D ⟶ 𝒪_X` sends `1_D ⊗ t` to `t`: the canonical
section corresponds, under the identification of `𝒪_X(D)` with `SheafHom_{𝒪_X}(𝓘_D, 𝒪_X)`, to
the inclusion `𝓘_D ⟶ 𝒪_X`. -/
theorem tensorPairing_canonicalSection_tmul (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (modulePresheaf B S hS X (idealSheafOfModules B S hS X D)).obj W) :
    tensorHomAt (structureCommRings B S hS X)
        (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD))
        (modulePresheaf B S hS X (idealSheafOfModules B S hS X D))
        (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)))
        (tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (idealSheafOfModules B S hS X D) (associatedInvertibleSheaf B S hS X D hD)
          (SheafOfModules.unit (structureRingSheaf B S hS X))
          (associatedInvertibleSheafEvaluation B S hS X D hD)) W
        ((canonicalSection B S hS X D hD).eval W ⊗ₜ t) =
      ((valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (definingIdealSheaf B S hS X D).ι).app W).hom t := by
  have hid : (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD)).restrictₛₗ
      (𝟙 W.unop).op ((canonicalSection B S hS X D hD).eval W) =
      (canonicalSection B S hS X D hD).eval W :=
    PresheafOfModules.sections_property
      (M := modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD))
      (canonicalSection B S hS X D hD) (𝟙 W.unop).op
  have h := associatedInvertibleSheafHomEquiv_apply B S hS X D hD W.unop
    ((canonicalSection B S hS X D hD).eval W) W (𝟙 W.unop) t
  rw [canonicalSection_apply, hid] at h
  exact h.symm

/-- The canonical section is the value of multiplication by it on the unit section. -/
theorem canonicalSectionHom_app_one (W : (SmallEtale B S hS X.1)ᵒᵖ) :
    (canonicalSection B S hS X D hD).eval W =
      (valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (canonicalSectionHom B S hS X D hD)).app W
          (1 : (structureRingSheaf B S hS X).obj.obj W) := by
  conv_lhs =>
    rw [← (associatedInvertibleSheaf B S hS X D hD).unitHomEquiv.apply_symm_apply
      (canonicalSection B S hS X D hD)]
  exact SheafOfModules.unitHomEquiv_apply_coe (associatedInvertibleSheaf B S hS X D hD)
    (canonicalSectionHom B S hS X D hD) W

/-- The left unit constraint `𝒪_X ⊗ 𝓘_D ≅ 𝓘_D` of the tensor product of presheaves of
`𝒪_X`-modules. -/
noncomputable def unitTensorPresheafIso :
    modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) ⊗
        modulePresheaf B S hS X (idealSheafOfModules B S hS X D) ≅
      modulePresheaf B S hS X (idealSheafOfModules B S hS X D) :=
  λ_ (modulePresheaf B S hS X (idealSheafOfModules B S hS X D))

/-- Tensoring multiplication by `1_D` with `𝓘_D` and following it by the evaluation pairing of
`𝒪_X(D)` is the inclusion `𝓘_D ⟶ 𝒪_X`, read through the unit constraint `𝒪_X ⊗ 𝓘_D ≅ 𝓘_D`. -/
theorem whiskerRight_canonicalSectionHom_tensorPairing :
    ((valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (canonicalSectionHom B S hS X D hD)) ▷
        modulePresheaf B S hS X (idealSheafOfModules B S hS X D)) ≫
      tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (idealSheafOfModules B S hS X D) (associatedInvertibleSheaf B S hS X D hD)
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (associatedInvertibleSheafEvaluation B S hS X D hD) =
      (unitTensorPresheafIso B S hS X D).hom ≫
        valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (definingIdealSheaf B S hS X D).ι := by
  refine (Iso.inv_comp_eq _).mp ?_
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have h := tensorPairing_canonicalSection_tmul B S hS X D hD W t
  rwa [canonicalSectionHom_app_one] at h

/-! ### Passing from presheaves to sheaves -/

/-- A morphism of `𝒪_X`-modules out of a sheafification is determined by its restriction along
the unit of sheafification. -/
theorem hom_ext_of_toSheafify {P : PresheafOfModules.{u} (Oforget (structureCommRings B S hS X))}
    {N : SheafOfModules.{u} (structureRingSheaf B S hS X)}
    {p q : (sheafify (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property).obj P ⟶ N}
    (h : toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property P ≫ p.val =
      toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property P ≫ q.val) :
    p = q :=
  ((sheafifyAdjunction (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property).homEquiv P N).injective h

/-- Restricting the sheafified multiplication by `1_D`, followed by the evaluation pairing, along
the unit of sheafification gives back the presheaf-level composite. -/
theorem toSheafify_comp_map_canonicalSectionHom :
    toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) ⊗
          modulePresheaf B S hS X (idealSheafOfModules B S hS X D)) ≫
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
          (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
          (structureRingSheaf B S hS X).property⟩).flip.obj
        (idealSheafOfModules B S hS X D)).map (canonicalSectionHom B S hS X D hD) ≫
        (associatedInvertibleSheafEvaluation B S hS X D hD).hom).val =
      ((valPresheafMap (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
            (canonicalSectionHom B S hS X D hD)) ▷
          modulePresheaf B S hS X (idealSheafOfModules B S hS X D)) ≫
        tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
          (idealSheafOfModules B S hS X D) (associatedInvertibleSheaf B S hS X D hD)
          (SheafOfModules.unit (structureRingSheaf B S hS X))
          (associatedInvertibleSheafEvaluation B S hS X D hD) := by
  rw [show (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
          (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
          (structureRingSheaf B S hS X).property⟩).flip.obj
        (idealSheafOfModules B S hS X D)).map (canonicalSectionHom B S hS X D hD) ≫
          (associatedInvertibleSheafEvaluation B S hS X D hD).hom).val =
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
          (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
          (structureRingSheaf B S hS X).property⟩).flip.obj
        (idealSheafOfModules B S hS X D)).map (canonicalSectionHom B S hS X D hD)).val ≫
          (associatedInvertibleSheafEvaluation B S hS X D hD).hom.val from rfl,
    show tensorPairing (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (idealSheafOfModules B S hS X D) (associatedInvertibleSheaf B S hS X D hD)
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (associatedInvertibleSheafEvaluation B S hS X D hD) =
      toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (associatedInvertibleSheaf B S hS X D hD) ⊗
          modulePresheaf B S hS X (idealSheafOfModules B S hS X D)) ≫
        (associatedInvertibleSheafEvaluation B S hS X D hD).hom.val from rfl]
  refine Eq.trans (Eq.trans (Category.assoc _ _ _).symm
    (congrArg (fun z => z ≫ (associatedInvertibleSheafEvaluation B S hS X D hD).hom.val)
      (((sheafifyAdjunction (structureCommRings B S hS X)
        (structureRingSheaf B S hS X).property).unit.naturality _).symm))) ?_
  exact Category.assoc _ _ _

/-- The sheafified left unit constraint `(𝒪_X ⊗ 𝓘_D)^# ⟶ 𝓘_D`: the morphism of `𝒪_X`-modules
adjoint to `AlgebraicGeometry.Space.unitTensorPresheafIso` under sheafification. -/
noncomputable def unitTensorHom :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
          (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
          (structureRingSheaf B S hS X).property⟩).flip.obj
        (idealSheafOfModules B S hS X D)).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)) ⟶ idealSheafOfModules B S hS X D :=
  ((sheafifyAdjunction (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property).homEquiv _ _).symm
      (unitTensorPresheafIso B S hS X D).hom

/-- Restricting the sheafified unit constraint along the unit of sheafification gives back the
presheaf-level unit constraint. -/
theorem toSheafify_comp_unitTensorHom :
    toSheafify (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
        (modulePresheaf B S hS X (SheafOfModules.unit (structureRingSheaf B S hS X)) ⊗
          modulePresheaf B S hS X (idealSheafOfModules B S hS X D)) ≫
      (unitTensorHom B S hS X D).val = (unitTensorPresheafIso B S hS X D).hom := by
  show ((sheafifyAdjunction (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property).homEquiv _ _) (unitTensorHom B S hS X D) = _
  exact ((sheafifyAdjunction (structureCommRings B S hS X)
    (structureRingSheaf B S hS X).property).homEquiv _ _).apply_symm_apply _

/-- The sheafified left unit constraint `(𝒪_X ⊗ 𝓘_D)^# ⟶ 𝓘_D` is an isomorphism: it is the
sheafification of an isomorphism of presheaves of modules followed by the counit of
sheafification. -/
theorem isIso_unitTensorHom : IsIso (unitTensorHom B S hS X D) := by
  have h : unitTensorHom B S hS X D =
      (sheafify (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property).map
            (unitTensorPresheafIso B S hS X D).hom ≫
        (sheafifyAdjunction (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property).counit.app
            (idealSheafOfModules B S hS X D) :=
    Adjunction.homEquiv_symm_apply (sheafifyAdjunction (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property) _ (idealSheafOfModules B S hS X D)
        (unitTensorPresheafIso B S hS X D).hom
  have h1 : IsIso ((sheafify (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property).map
        (unitTensorPresheafIso B S hS X D).hom) :=
    Iso.isIso_hom ((sheafify (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property).mapIso (unitTensorPresheafIso B S hS X D))
  have h2 : IsIso ((sheafifyAdjunction (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property).counit.app (idealSheafOfModules B S hS X D)) :=
    NatIso.isIso_app_of_isIso _ _
  rw [h]
  exact IsIso.comp_isIso' h1 h2

/-- Tensoring multiplication by `1_D` with `𝓘_D` and following it by the evaluation pairing
`𝒪_X(D) ⊗ 𝓘_D ≅ 𝒪_X` is the inclusion `𝓘_D ⟶ 𝒪_X`, read through the unit constraint
`(𝒪_X ⊗ 𝓘_D)^# ≅ 𝓘_D`. -/
theorem map_canonicalSectionHom_comp_evaluation :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
          (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
          (structureRingSheaf B S hS X).property⟩).flip.obj
        (idealSheafOfModules B S hS X D)).map (canonicalSectionHom B S hS X D hD) ≫
        (associatedInvertibleSheafEvaluation B S hS X D hD).hom =
      unitTensorHom B S hS X D ≫ (definingIdealSheaf B S hS X D).ι := by
  apply hom_ext_of_toSheafify
  refine (toSheafify_comp_map_canonicalSectionHom B S hS X D hD).trans
    ((whiskerRight_canonicalSectionHom_tensorPairing B S hS X D hD).trans ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact (congrArg (fun z => z ≫ (definingIdealSheaf B S hS X D).ι.val)
    (toSheafify_comp_unitTensorHom B S hS X D)).symm

/-- **Stacks 0847, part (1).** The canonical section `1_D` of the invertible sheaf `𝒪_X(D)`
attached to an effective Cartier divisor `D ⊆ X` is a regular section: multiplication by it is a
monomorphism `𝒪_X ⟶ 𝒪_X(D)`.  Tensoring by the invertible sheaf `𝓘_D` reflects monomorphisms,
and it turns multiplication by `1_D` into the inclusion `𝓘_D ⟶ 𝒪_X`. -/
@[stacks 0847 "part (1)"]
theorem canonicalSection_isRegular :
    IsRegularSection (structureCommRings B S hS X) (structureRingSheaf B S hS X).property
      (canonicalSection B S hS X D hD) := by
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (idealSheafOfModules B S hS X D) := hD
  have heq : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
          (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
          (structureRingSheaf B S hS X).property⟩).flip.obj
        (idealSheafOfModules B S hS X D)).IsEquivalence :=
    tensorRightFunctor_isEquivalence (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property (idealSheafOfModules B S hS X D)
  have hmono : Mono (definingIdealSheaf B S hS X D).ι := inferInstance
  have hmap : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨structureCommRings B S hS X, Presheaf.isSheaf_of_isSheaf_comp _
          (structureCommRings B S hS X) (forget₂ CommRingCat RingCat)
          (structureRingSheaf B S hS X).property⟩).flip.obj
        (idealSheafOfModules B S hS X D)).map (canonicalSectionHom B S hS X D hD)) :=
    mono_of_fac_of_isIso_of_mono _
      (Iso.isIso_hom (associatedInvertibleSheafEvaluation B S hS X D hD))
      (isIso_unitTensorHom B S hS X D) hmono
      (map_canonicalSectionHom_comp_evaluation B S hS X D hD)
  exact mono_of_mono_map_of_faithful _ heq.faithful _ hmap

end AlgebraicGeometry.Space

end
