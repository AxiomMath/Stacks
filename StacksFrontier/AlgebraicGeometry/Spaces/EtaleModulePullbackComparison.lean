module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleStructureSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of modules along an étale morphism is the inverse image, and is exact

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  The pullback `f^*` of `𝒪_Y`-modules of Stacks 03LU is, by definition,
`𝒪_X ⊗_{f⁻¹𝒪_Y} f⁻¹(-)`: the inverse image of modules of Stacks 03D2 followed by extension of
scalars along the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`.  Stacks 03LV asserts that for an étale `f` the
structure map is an isomorphism, so that no tensor product is taken: `f^*𝒢` *is* the inverse
image `f⁻¹𝒢`, with its scalars transported along the canonical isomorphism of structure sheaves,
and `f^*` is therefore exact.

This file carries that out.  The invertibility of the structure map is
`AlgebraicGeometry.Space.isIso_fSharpInverseImage_of_isEtale`; what is added here is that
extension of scalars along an invertible structure map is restriction of scalars along its
inverse, which identifies `f^*` with the inverse image and makes both halves of exactness
properties of the inverse image of Stacks 03D2.

## Main definitions

* `AlgebraicGeometry.Space.etaleStructureRingSheafIso` is the canonical isomorphism
  `f⁻¹𝒪_Y ≅ 𝒪_X` of sheaves of (not necessarily commutative) rings, over which the sheaves of
  modules are indexed.
* `AlgebraicGeometry.Space.etaleModuleInverseImage` is the inverse image of `𝒪_Y`-modules of
  Stacks 03D2, read as `𝒪_X`-modules through that isomorphism.
* `AlgebraicGeometry.Space.extendScalarsFSharpAdjunction` is the extension/restriction of
  scalars adjunction along the structure map, whose unit is what specifies the comparison.

## Main results

* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModuleInverseImage`: **Stacks 03LV** — pullback
  of modules along an étale morphism is naturally isomorphic to the inverse image.
* `AlgebraicGeometry.Space.modulePullbackIsoEtaleModuleInverseImage_unit_app`: the comparison
  sends the canonical image of every inverse-image section to that same section, so it is the
  canonical comparison and not merely some natural isomorphism of the two functors.
* `AlgebraicGeometry.Space.modulePullback_exact`: **Stacks 03LV** — pullback of modules along an
  étale morphism of algebraic spaces is exact.

## Implementation notes

The comparison is `CategoryTheory.Adjunction.leftAdjointUniq` for the two adjunctions over the
same right adjoint `restrictScalars (f⁻¹𝒪_Y ⟶ 𝒪_X)`: extension of scalars along the structure
map, and restriction of scalars along its inverse, the latter being half of the equivalence
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`.  Uniqueness of left adjoints is
what makes the comparison canonical, and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` is what turns that into the sectionwise
statement: the unit of the second adjunction is the identity on sections, because restriction of
scalars does not change the sheaf of sections.

Exactness is `CategoryTheory.Limits.exactFunctor`, which packages preservation of finite limits
and of finite colimits.  Both are already available for the inverse image of modules
(`Stacks.Sheaves.RingedToposModules.inverseImageModules_preservesFiniteLimits_inst` and its
colimit companion, which are Stacks 04JC for modules), and restriction of scalars along an
isomorphism is an equivalence, so the composite has both and they transport along the
comparison.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The extension/restriction of scalars adjunction of Stacks 03CZ along the inverse-image form
`f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map of the morphism of small étale ringed topoi of
Stacks 03G8.  Its left adjoint is the second factor of the pullback of modules
`AlgebraicGeometry.Space.modulePullback`. -/
noncomputable def extendScalarsFSharpAdjunction :
    extendScalarsFSharp (smallEtaleRingedToposModulesHom B S hS f) ⊣
      SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage :=
  extendRestrictScalarsAdjunction.{u, u, u + 1} _
    (fSharpCommRing (smallEtaleRingedToposModulesHom B S hS f)) _ _

variable (hf : IsEtale B S hS f.hom)

include hf

/-- **Stacks 03LV** at the level of sheaves of rings: for an étale morphism the inverse-image
form of the structure map is an isomorphism after forgetting commutativity, which is the form in
which the sheaves of modules are indexed over it. -/
theorem isIso_ringFsharpInverseImage_of_isEtale :
    IsIso (smallEtaleRingedToposHom B S hS f).ringFsharpInverseImage := by
  have := isIso_fSharpInverseImage_of_isEtale B S hS f hf
  show IsIso ((sheafCompose (SmallEtale.topology B S hS X.1)
    (forget₂ CommRingCat.{u} RingCat.{u})).map
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage)
  infer_instance

/-- **Stacks 03LV.** The canonical isomorphism `f⁻¹𝒪_Y ≅ 𝒪_X` of sheaves of rings along an étale
morphism of algebraic spaces.  This is
`AlgebraicGeometry.Space.etaleStructureSheafIso` with commutativity forgotten; it is the form
over which the sheaves of modules of Stacks 03LU are indexed. -/
noncomputable def etaleStructureRingSheafIso :
    inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y) ≅
      structureRingSheaf B S hS X :=
  (sheafCompose (SmallEtale.topology B S hS X.1)
    (forget₂ CommRingCat.{u} RingCat.{u})).mapIso (etaleStructureSheafIso B S hS f hf)

/-- The forward map of the canonical isomorphism of structure sheaves of rings is the
inverse-image form of the structure map. -/
theorem etaleStructureRingSheafIso_hom :
    (etaleStructureRingSheafIso B S hS f hf).hom =
      (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage :=
  rfl

/-- **Stacks 03LV.** The inverse image of `𝒪_Y`-modules along an étale morphism of algebraic
spaces: the inverse image of modules of Stacks 03D2, with its scalar action read over `𝒪_X`
through the canonical isomorphism `f⁻¹𝒪_Y ≅ 𝒪_X`.  No extension of scalars occurs, which is
what distinguishes it from the pullback of Stacks 03D6. -/
noncomputable def etaleModuleInverseImage :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y) ⋙
    SheafOfModules.restrictScalars (etaleStructureRingSheafIso B S hS f hf).inv

/-- Restriction of scalars along the inverse of the canonical isomorphism of structure sheaves
is left adjoint to restriction of scalars along the structure map: it is half of the equivalence
`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`. -/
noncomputable def restrictScalarsInvAdjunction :
    SheafOfModules.restrictScalars (etaleStructureRingSheafIso B S hS f hf).inv ⊣
      SheafOfModules.restrictScalars
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (etaleStructureRingSheafIso B S hS f hf)).toAdjunction

/-- **Stacks 03LV.** For an étale morphism, extension of scalars along the structure map is
restriction of scalars along the inverse of the canonical isomorphism of structure sheaves: the
two are left adjoints of one and the same functor, so uniqueness of left adjoints identifies
them. -/
noncomputable def extendScalarsFSharpIsoRestrictScalarsInv :
    extendScalarsFSharp (smallEtaleRingedToposModulesHom B S hS f) ≅
      SheafOfModules.restrictScalars (etaleStructureRingSheafIso B S hS f hf).inv :=
  (extendScalarsFSharpAdjunction B S hS f).leftAdjointUniq
    (restrictScalarsInvAdjunction B S hS f hf)

/-- **Stacks 03LV.** Along an étale morphism of algebraic spaces, the pullback of `𝒪_Y`-modules
of Stacks 03LU is naturally isomorphic to the inverse image of modules with its scalars
transported along the canonical isomorphism of structure sheaves. -/
@[stacks 03LV "pullback of modules is inverse image",
  stacks 03LW "the identification f^*G = f_small^{-1}G along an étale morphism"]
noncomputable def modulePullbackIsoEtaleModuleInverseImage :
    modulePullback B S hS f ≅ etaleModuleInverseImage B S hS f hf :=
  Functor.isoWhiskerLeft
    (inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y))
    (extendScalarsFSharpIsoRestrictScalarsInv B S hS f hf)

/-- **Stacks 03LV.** The comparison of the pullback of modules with the inverse image sends the
canonical image of every section of the inverse image to that same section.  This specifies the
comparison, rather than merely asserting that the two functors are isomorphic: a scalar-unit
twist of the natural isomorphism is excluded. -/
@[stacks 03LV "canonical module comparison"]
theorem modulePullbackIsoEtaleModuleInverseImage_unit_app
    (G : Modules.{u, u} B S hS Y.1 Y.2) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (m : ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).obj G).val.obj U) :
    ((extendScalarsFSharpAdjunction B S hS f).unit.app
          ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
            (structureRingSheaf B S hS Y)).obj G) ≫
        (SheafOfModules.restrictScalars
          (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map
            ((modulePullbackIsoEtaleModuleInverseImage B S hS f hf).hom.app G)).val.app U m =
      m := by
  have hunit := Adjunction.unit_leftAdjointUniq_hom_app
    (extendScalarsFSharpAdjunction B S hS f) (restrictScalarsInvAdjunction B S hS f hf)
    ((inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS Y)).obj G)
  exact congrArg (fun q ↦ q.val.app U m) hunit

/-- **Stacks 03LV.** Pullback of sheaves of modules along an étale morphism of algebraic spaces
is exact.  Through the comparison with the inverse image both halves are the exactness of the
inverse image of modules of Stacks 04JC, restriction of scalars along an isomorphism being an
equivalence. -/
@[stacks 03LV "exactness"]
theorem modulePullback_exact :
    exactFunctor (Modules.{u, u} B S hS Y.1 Y.2) (Modules.{u, u} B S hS X.1 X.2)
      (modulePullback B S hS f) := by
  have : (SheafOfModules.restrictScalars
      (etaleStructureRingSheafIso B S hS f hf).inv).IsEquivalence :=
    (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
      (etaleStructureRingSheafIso B S hS f hf)).isEquivalence_functor
  have : PreservesFiniteLimits (etaleModuleInverseImage B S hS f hf) :=
    inferInstanceAs (PreservesFiniteLimits
      (inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y) ⋙
      SheafOfModules.restrictScalars (etaleStructureRingSheafIso B S hS f hf).inv))
  have : PreservesFiniteColimits (etaleModuleInverseImage B S hS f hf) :=
    inferInstanceAs (PreservesFiniteColimits
      (inverseImageModules (smallEtaleRingedToposHom B S hS f).toToposHom
        (structureRingSheaf B S hS Y) ⋙
      SheafOfModules.restrictScalars (etaleStructureRingSheafIso B S hS f hf).inv))
  rw [exactFunctor_iff]
  exact ⟨preservesFiniteLimits_of_natIso
      (modulePullbackIsoEtaleModuleInverseImage B S hS f hf).symm,
    preservesFiniteColimits_of_natIso
      (modulePullbackIsoEtaleModuleInverseImage B S hS f hf).symm⟩

end AlgebraicGeometry.Space

end
