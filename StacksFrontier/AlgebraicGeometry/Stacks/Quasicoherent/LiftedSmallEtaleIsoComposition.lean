module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilySheafCondition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonRestrictionComposition

/-!
# Factors 2, 3 and 4 of the identification of Stacks 076T, read backwards

`AlgebraicGeometry.Stack.liftedSmallEtaleIso` identifies the restriction `F|_{W_ét}` of
**Stacks 06WJ** with `(g^*𝓕)^a`, for an arrow `φ : z ⟶ x` of `𝒳` lying over a morphism of
schemes `g : W ⟶ U` along which the comparison map `c_φ` of **Stacks 06WC** is an isomorphism.
It is factors 2, 3 and 4 of the five-factor identification of sections of
`AlgebraicGeometry.Stack.liftedSectionsIso`, and it is built as a composite of a sheafification
unit, a sheafified comparison and the base change of **Stacks 03LC (1)** — a shape in which it
has no component formula and no composition law.

This file gives it one. The *inverse* identification is a morphism of **sheaves** of modules,
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`: the identification of Stacks 06WC read
backwards, the sheafified Stacks 06WC pullback of the identification `𝓕^a ≅ F|_{U_ét}` of
hypothesis (a), and the adjunct of `c_φ` under the sheafification adjunction. That the two are
inverse — `AlgebraicGeometry.Stack.liftedSmallEtaleIso_hom_comp_sheafInv` — is the triangle
identity of the sheafification adjunction, and it is what moves the composition law for
factors 2, 3 and 4 out of the presheaf world, where the sheafification unit obstructs it, and
into the category of sheaves of modules, where **Stacks 075D (1)** for the sheafified comparison
and the pentagon of `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso_comp`
both live.

## The proof

The identification is `η ≫ sheafify(ζ_φ)⁻¹ ≫ bc_φ` read on presheaves, where `ζ_φ` is the
Stacks 06WC pullback of hypothesis (a) followed by `c_φ`. Composing it with the sheaf-level
inverse and transposing, the whole composite becomes the adjunct of `ζ_φ⁻¹ ≫ ζ_φ`, which is the
identity; so the equation is
`CategoryTheory.PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm` applied to
the identity, after `CategoryTheory.Adjunction.homEquiv_naturality_left_symm` has collected the
two factors of `ζ_φ` into one.

## Implementation notes

Six definitions are locally irreducible. Four are the ones the imported module
`Quasicoherent.SheafifiedPullbackComparisonRestrictionComposition` already needs; the other two,
`AlgebraicGeometry.Stack.ringStructureSheafCore` and
`AlgebraicGeometry.Stack.restrictModuleToSmallEtale`, stop the restriction of Stacks 06WJ from
unfolding into the structure sheaf of **Stacks 06TV** that indexes it, which is what the one
defeq check between `F|_{W_ét}` and its restriction of scalars along the identity would
otherwise do. Without them the statement of the inverse identity exceeds two hundred
thousand heartbeats; with them the file checks in seven seconds.

## Main definitions

* `AlgebraicGeometry.Stack.sheafifiedRestrictComparison`: the adjunct of the comparison map
  `c_φ` of Stacks 06WC under the sheafification adjunction.
* `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`: **the inverse of
  `AlgebraicGeometry.Stack.liftedSmallEtaleIso`, as a morphism of sheaves of modules.**

## Main results

* `AlgebraicGeometry.Stack.liftedSmallEtaleIso_hom_comp_sheafInv`: **the two are inverse.**

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf

/-- **The adjunct of the comparison map `c_φ` of Stacks 06WC** under the sheafification
adjunction: the morphism of sheaves of modules out of the sheafification of the Stacks 06WC
pullback of `F|_{U_ét}` which `c_φ` corresponds to, the restriction `F|_{W_ét}` being a sheaf.

This is the third factor of `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`, and the form in
which `AlgebraicGeometry.Stack.sheafifiedRestrictModulePullbackComparison_comp` states
**Stacks 075D (1)** for it. -/
noncomputable def sheafifiedRestrictComparison {x z : 𝒳} (φ : z ⟶ x)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf) :
    (PresheafOfModules.sheafification
        (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
          (contains_base B E h S hS p z)).obj)).obj
        ((PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
              (etaleTopology_le_topology B))).obj
          (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
            (etaleTopology_le_topology B) F)) ⟶
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F z hMz :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
        (contains_base B E h S hS p z)).obj)).homEquiv _
      (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F z hMz)).symm
    (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F)

/-- **The inverse of `AlgebraicGeometry.Stack.liftedSmallEtaleIso`, as a morphism of sheaves of
modules.** For an arrow `φ : z ⟶ x` of `𝒳` lying over `g : W ⟶ U`, a quasi-coherent
`𝒪_U`-module `𝓕` and a morphism `e : 𝓕^a ⟶ F|_{U_ét}` of sheaves of modules, the composite of

* the identification `(g^*𝓕)^a ≅ ε_g^*(𝓕^a)` of **Stacks 03LC (1)**, read backwards;
* the sheafified Stacks 06WC pullback of `e`;
* `AlgebraicGeometry.Stack.sheafifiedRestrictComparison`, the adjunct of `c_φ`.

Taking `e` to be the identification of hypothesis (a) of **Stacks 076T** and `c_φ` invertible,
`AlgebraicGeometry.Stack.liftedSmallEtaleIso_hom_comp_sheafInv` shows that the underlying
morphism of presheaves is inverse to `AlgebraicGeometry.Stack.liftedSmallEtaleIso`.  No
invertibility is needed to *state* it, and none is assumed here. -/
noncomputable def liftedSmallEtaleSheafInv {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (e : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ⟶
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx) :
    (SmallEtale.associatedModule E (p.obj z).left.1 (contains_base B E h S hS p z)).obj
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕) ⟶
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F z hMz :=
  (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ 𝓕).inv ≫
    (sheafifiedPullbackComparison B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).map e ≫
    sheafifiedRestrictComparison B E h S hS p hp F φ hMz

/-- `AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv` with its middle factor spelled out as
the sheafification of the Stacks 06WC pullback of presheaves of modules, rather than as the
functor `AlgebraicGeometry.Stack.sheafifiedPullbackComparison` those compose into.

The two are definitionally equal; the spelling is recorded because the adjunction calculus
rewrites against the sheafification functor and not against the composite. -/
theorem liftedSmallEtaleSheafInv_eq {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (e : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ⟶
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx) :
    liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz e =
      (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ 𝓕).inv ≫
        (PresheafOfModules.sheafification (𝟙 _)).map
            ((PresheafOfModules.pullback.{u}
              (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
                (etaleTopology_le_topology B))).map ((SheafOfModules.forget _).map e)) ≫
          sheafifiedRestrictComparison B E h S hS p hp F φ hMz :=
  rfl

variable (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint SheafOfModules.pullback
  AlgebraicGeometry.SmallEtale.associatedModule PresheafOfModules.pullback
  AlgebraicGeometry.Stack.ringStructureSheafCore
  AlgebraicGeometry.Stack.restrictModuleToSmallEtale

/-- **`AlgebraicGeometry.Stack.liftedSmallEtaleIso` is inverse to
`AlgebraicGeometry.Stack.liftedSmallEtaleSheafInv`**, so factors 2, 3 and 4 of the
identification of sections of **Stacks 076T** are the underlying morphism of presheaves of a
morphism of sheaves of modules, read backwards.

Both sides are morphisms out of a sheafification, so the equation is proved by transposing it:
the composite of the two is the adjunct of `ζ_φ⁻¹ ≫ ζ_φ = 𝟙`, where `ζ_φ` is the Stacks 06WC
pullback of the identification of hypothesis (a) followed by the comparison map `c_φ`. -/
theorem liftedSmallEtaleIso_hom_comp_sheafInv {x z : 𝒳} (φ : z ⟶ x)
    (𝓕 : (p.obj x).left.1.Modules) (h𝓕 : 𝓕.IsQuasicoherent)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (hMz : Presheaf.IsSheaf (SmallEtale.topology E (p.obj z).left.1
        (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf)
    (eU : (SmallEtale.associatedModule E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj 𝓕 ≅
      restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F x hMx)
    (hiso : IsIso (restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
      (etaleTopology_le_topology B) F)) :
    (liftedSmallEtaleIso B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom ≫
        (PresheafOfModules.toPresheaf _).map
          ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
            (liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom)) =
      𝟙 _ := by
  let := h𝓕
  set ζ : (PresheafOfModules.pullback.{u}
        (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B))).obj
        ((SmallEtale.associatedModule E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj 𝓕).val ≅
      restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F :=
    (PresheafOfModules.pullback.{u} _).mapIso ((SheafOfModules.forget _).mapIso eU) ≪≫
      @asIso _ _ _ _ _ hiso with hζ
  have key : (liftedSmallEtaleIso B E h S hS p hp F hlqc φ 𝓕 h𝓕 hMx eU hiso).hom =
      (PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
              (contains_base B E h S hS p z)).obj)).unit.app
            (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
              (etaleTopology_le_topology B) F) ≫
          (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
            (((PresheafOfModules.sheafification (𝟙 _)).mapIso ζ).inv ≫
              (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
                (etaleTopology_le_topology B) φ 𝓕).hom)) := rfl
  have hpull : ζ.inv ≫ (PresheafOfModules.pullback.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B))).map
        ((SheafOfModules.forget _).map eU.hom) ≫
      restrictModulePullbackComparison B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F =
      𝟙 _ := ζ.inv_hom_id
  have halg : (((PresheafOfModules.sheafification (𝟙 _)).mapIso ζ).inv ≫
        (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ 𝓕).hom) ≫
      liftedSmallEtaleSheafInv B E h S hS p hp F φ 𝓕 hMx hMz eU.hom =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj z).left.1
            (contains_base B E h S hS p z)).obj)).homEquiv _
          (restrictModuleToSmallEtaleSheaf B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) F z hMz)).symm
        (𝟙 (restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
          (etaleTopology_le_topology B) F)) := by
    rw [liftedSmallEtaleSheafInv_eq]
    unfold sheafifiedRestrictComparison
    rw [Functor.mapIso_inv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← hpull]
    exact Eq.trans (congrArg (CategoryStruct.comp _) (Adjunction.homEquiv_naturality_left_symm
      _ _ _)).symm (Adjunction.homEquiv_naturality_left_symm _ _ _).symm
  have hmerge := congrArg (SheafOfModules.forget (SmallEtale.structureSheaf E (p.obj z).left.1
    (contains_base B E h S hS p z)) ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map halg
  rw [Functor.map_comp] at hmerge
  have main := (Category.assoc _ _ _).trans
    ((congrArg (CategoryStruct.comp _) hmerge).trans
      (PresheafOfModules.sheafificationAdjunction_unit_comp_homEquiv_symm _ _))
  rw [key]
  exact Eq.trans ((PresheafOfModules.toPresheaf _).map_comp _ _).symm
    (Eq.trans (congrArg ((PresheafOfModules.toPresheaf _).map) main)
      ((PresheafOfModules.toPresheaf _).map_id _))


end AlgebraicGeometry.Stack

end
