module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionDirectImageDerivationKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalDirectImageUnitSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceCokernelDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDerivationBothEnds
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSplitDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageDerivationTransport

/-!
# Stacks 05ZB: the conormal sequence of an immersion with a left inverse is split exact

Let `Z ⊆ X` be a closed subspace of an algebraic space with inclusion `i`, and let `g : X ⟶ Z` be
a left inverse of `i`.  Stacks 05ZB asserts that the conormal sequence of Stacks 05ZA is *split
exact*; its remaining clause — the `0 ⟶` at the left end, that is, that
`AlgebraicGeometry.Space.conormalSequenceFirstMap` is a monomorphism — is what this file is for.

The route is Stacks 02HP inside the small étale topos: a retraction of the first arrow is, across
the adjunction of Stacks 03LU, the same thing as a `Z`-derivation `D : 𝒪_X ⟶ i_*𝒞_{Z/X}` whose
restriction to the defining ideal sheaf is the unit of that adjunction, and such a `D` is the
difference `a ↦ a - g^♯(i^♯a)` — which can be written on `i_*i⁻¹𝒪_X`, where
`i_*(i♯) : i_*i⁻¹𝒪_X ⟶ i_*𝒪_Z` is a split surjection that a left inverse of `i` splits.  Every
datum of that derivation is available; this file instantiates
`PresheafOfModules.splitIdealDerivation` at them.

## Main definitions

* `AlgebraicGeometry.Space.conormalSplitTarget`: the coefficients, the direct image `i_*𝒞_{Z/X}`
  over `i_*𝒪_Z`.
* `AlgebraicGeometry.Space.conormalSplitIdealDerivation`: **the derivation of Stacks 02HP for a
  closed subspace with a left inverse**, a derivation of `i_*i⁻¹𝒪_X` relative to
  `AlgebraicGeometry.Space.conormalSplitBase`.

## Main results

* `Stacks.Sheaves.RingedToposModules.smul_pullbackModuleObj_restrictScalars` and
  `…_commRing`, and `…smul_pushforwardModuleFunctor_restrictScalars`: the action of a section of
  `f_*S'` on the direct image of a restriction of scalars, in terms of the action of its image
  under `f_*α` on the direct image.  This is the one ingredient of the derivation that is not
  already in the library.
* `AlgebraicGeometry.Space.conormalDirectImageNu_smul_structureSharp`: the semilinearity the
  derivation consumes, at the restricted coefficients.

## Implementation notes

**The semilinearity is proved generically and instantiated.**  The coefficient map
`AlgebraicGeometry.Space.conormalDirectImageNu` is semilinear over `i_*i⁻¹𝒪_X` for the action on
`i_*(i^♯)^*𝒞_{Z/X}`, while the derivation's coefficients are `i_*𝒞_{Z/X}` with the scalars
restricted along the split surjection.  The two actions agree, and at the geometric instantiation
they are definitionally but not syntactically equal; the identification is therefore made with
the two sites, the functor and the two sheaves of rings all variables, where it is a `map_smul`
for `Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsInv` — whose underlying
morphism of sheaves of sets is the identity.

**The direct-image spellings are a separate wrapper, and that is not cosmetic.**
`Stacks.Sheaves.ToposPushforward.pushforwardRingSheaf` and `pushforwardModuleFunctor` are plain
definitions, so a conclusion stated at the `pullback…` spellings is not *found by instance
resolution* at a geometric instantiation: the scalar action is registered over the `pushforward…`
sheaf of rings and nothing unfolds the definition to see it.
`Stacks.Sheaves.RingedToposModules.smul_pushforwardModuleFunctor_restrictScalars` is the same
statement one delta later, so that the geometric instantiation applies it verbatim.

**The semilinearity is a declaration of its own.**  Inlined into the instantiation of
`PresheafOfModules.splitIdealDerivation` the two together exhaust the heartbeat budget, and
separately each takes seconds: the budget is per declaration.

## References

* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), the tag.
* [Stacks Project, Tag 02HP](https://stacks.math.columbia.edu/tag/02HP), the derivation.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction the
  retraction is transposed across.
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] CategoryTheory.Sheaf.hasSheafifyAddCommGrpCat
attribute [-instance] CategoryTheory.Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

namespace Stacks.Sheaves.RingedToposModules

universe ww ww' vv uu vv' uu'

section Generic

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {K : GrothendieckTopology D}
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{ww'})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww'})]
  [K.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{ww'} RingCat.{ww'})]

omit [K.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{ww'} RingCat.{ww'})] in
/-- **The action of a section of `f_*S'` on a direct image of a restriction of scalars.**  For a
morphism `α : S' ⟶ S` of sheaves of rings and an `S`-module `G`, the action of a section of
`f_*S'` on the direct image of `G` with its scalars restricted along `α` is the action, on the
direct image of `G`, of that section's image under `f_*α`.

This is the sections form of
`Stacks.Sheaves.RingedToposModules.pullbackModuleObjRestrictScalarsIso`, whose inverse is the
identity on underlying sheaves of sets and whose semilinearity is
`Stacks.Sheaves.RingedToposModules.moduleSMulObj_restrictScalars`.  It is stated with the two
sites, the functor and the two sheaves of rings all variables: at a geometric instantiation the
two module structures are definitionally but not syntactically equal, and deciding that is not
affordable, while generically the statement is a `map_smul`. -/
theorem smul_pullbackModuleObj_restrictScalars (J : GrothendieckTopology C)
    [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})]
    (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [Limits.PreservesFiniteProducts Φ]
    {S S' : Sheaf K RingCat.{ww'}} (α : S' ⟶ S) (G : SheafOfModules.{ww'} S) (U : Cᵒᵖ)
    (a : ToType ((pullbackRingSheaf J Φ S').obj.obj U))
    (m : ToType ((pullbackModuleObj J Φ S G).val.obj U)) :
    a • (show ToType ((pullbackModuleObj J Φ S'
          ((SheafOfModules.restrictScalars α).obj G)).val.obj U) from m) =
      ((pullbackRingSheafMap J Φ α).hom.app U) a • m := by
  have hid : ∀ z, (pullbackModuleObjRestrictScalarsInv J Φ α G).val.app U z = z := fun z ↦
    (moduleSheafFunctor_map_hom_app
        (pullbackModuleObjRestrictScalarsInv J Φ α G) U z).symm.trans
      ((congrArg (fun k : Sheaf.moduleSheaf (pullbackRingSheaf J Φ S')
            (pullbackModuleObj J Φ S' ((SheafOfModules.restrictScalars α).obj G)) ⟶
              Sheaf.moduleSheaf (pullbackRingSheaf J Φ S')
                ((SheafOfModules.restrictScalars (pullbackRingSheafMap J Φ α)).obj
                  (pullbackModuleObj J Φ S G)) ↦ k.hom.app U z)
        (moduleSheafFunctor_map_pullbackModuleObjRestrictScalarsInv J Φ α G)).trans
          (id_hom_app_apply _ U z))
  have h := map_smul ((pullbackModuleObjRestrictScalarsInv J Φ α G).val.app U).hom a
    (show ToType ((pullbackModuleObj J Φ S'
      ((SheafOfModules.restrictScalars α).obj G)).val.obj U) from m)
  rw [hid, hid] at h
  exact h

/-- **The same for a morphism of sheaves of commutative rings**, which is the form a geometric
consumer has: the comparison of scalars it restricts along is the forgetful image of a morphism
of sheaves of commutative rings, and the scalar it acts by is that morphism's direct image. -/
theorem smul_pullbackModuleObj_restrictScalars_commRing (J : GrothendieckTopology C)
    [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
    [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})]
    [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{ww} RingCat.{ww})]
    (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [Limits.PreservesFiniteProducts Φ]
    {O O' : Sheaf K CommRingCat.{ww'}} (θ : O' ⟶ O)
    (G : SheafOfModules.{ww'} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Cᵒᵖ)
    (a : ToType ((pullbackCommRingSheaf J Φ O').obj.obj U))
    (m : ToType ((pullbackModuleObj J Φ (Stacks.SheafOfModules.Tensor.ringSheaf O) G).val.obj U)) :
    (show ToType ((pullbackRingSheaf J Φ
          (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj.obj U) from a) •
        (show ToType ((pullbackModuleObj J Φ
            (Stacks.SheafOfModules.Tensor.ringSheaf O')
            ((SheafOfModules.restrictScalars
              ((Stacks.forgetCommRingSheaf.{vv', uu', ww'} K).map θ)).obj G)).val.obj U) from m) =
      (show ToType ((pullbackRingSheaf J Φ
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.obj U) from
        ((pullbackCommRingSheafMap J Φ θ).hom.app U) a) • m :=
  Eq.trans
    (smul_pullbackModuleObj_restrictScalars J Φ
      ((Stacks.forgetCommRingSheaf.{vv', uu', ww'} K).map θ) G U a m)
    (congrArg
      (fun t : ToType ((pullbackRingSheaf J Φ
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.obj U) ↦ t • m)
      (congrArg
        (fun k : pullbackRingSheaf J Φ (Stacks.SheafOfModules.Tensor.ringSheaf O') ⟶
            pullbackRingSheaf J Φ (Stacks.SheafOfModules.Tensor.ringSheaf O) ↦ k.hom.app U a)
        (forgetCommRingSheaf_map_pullbackCommRingSheafMap J Φ θ).symm))

end Generic

section DirectImage

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww})]
  [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (CategoryTheory.forget RingCat.{ww'})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{ww'})]
  [K.HasSheafCompose (CategoryTheory.forget₂ CommRingCat.{ww'} RingCat.{ww'})]

/-- **The action of a section of `f_*𝒪'` on the direct image of a restriction of scalars**, in
the spellings of a morphism of topoi: for `θ : 𝒪' ⟶ 𝒪` of sheaves of commutative rings on the
source and an `𝒪`-module `G`, a section of `f_*𝒪'` acts on `f_*((restrictScalars θ).obj G)` the
way its image under `f_*θ` acts on `f_*G`.

This is `Stacks.Sheaves.RingedToposModules.smul_pullbackModuleObj_restrictScalars_commRing` with
the finite-product-preserving functor taken to be `f.pushforward`.  It exists so that a geometric
consumer meets the statement already written with `pushforwardRingSheaf`,
`pushforwardModuleFunctor` and `pushforwardCommRingFunctor`: those are plain definitions, so a
conclusion stated at the `pullback…` spellings is not found by instance resolution at a geometric
instantiation, and the reconciliation would have to be paid for there. -/
theorem smul_pushforwardModuleFunctor_restrictScalars
    (f : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
    {O O' : Sheaf J CommRingCat.{ww}} (θ : O' ⟶ O)
    (G : SheafOfModules.{ww} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (U : Dᵒᵖ)
    (a : ToType (((pushforwardCommRingFunctor f).obj O').obj.obj U))
    (m : ToType (((pushforwardModuleFunctor f
      (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj G).val.obj U)) :
    (show ToType ((pushforwardRingSheaf f
          (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj.obj U) from a) •
        (show ToType (((pushforwardModuleFunctor f
            (Stacks.SheafOfModules.Tensor.ringSheaf O')).obj
            ((SheafOfModules.restrictScalars
              ((Stacks.forgetCommRingSheaf.{vv, uu, ww} J).map θ)).obj G)).val.obj U) from m) =
      (show ToType ((pushforwardRingSheaf f
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj.obj U) from
        (((pushforwardCommRingFunctor f).map θ).hom.app U) a) • m :=
  smul_pullbackModuleObj_restrictScalars_commRing K f.pushforward θ G U a m

end DirectImage

end Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
  (g : X ⟶ subspaceSpace B S hS Z)
  (hg : subspaceInclusion B S hS X Z ≫ g = 𝟙 (subspaceSpace B S hS Z))

/-- **The coefficients of the derivation of Stacks 02HP for a closed subspace**: the direct image
`i_*𝒞_{Z/X}` along the inclusion of the conormal module, taken over `i_*𝒪_Z`.

This is the spelling for which the sheaf of commutative rings the split surjection of
Stacks 02HP lives on is, on the nose, the sheaf of rings this is a module over. -/
noncomputable abbrev conormalSplitTarget :=
  (pushforwardModuleFunctor (subspaceToposHom B S hS X Z)
      (structureRingSheaf B S hS (subspaceSpace B S hS Z))).obj (conormalModule B S hS X Z)

/-- **The coefficient map is semilinear for the restricted coefficients.**  This is `hnuSmul`,
the one new ingredient the derivation of Stacks 02HP needs here: the coefficient map
`AlgebraicGeometry.Space.conormalDirectImageNu` is `i_*i⁻¹𝒪_X`-semilinear
(`AlgebraicGeometry.Space.conormalDirectImageNu_smul`), and the coefficients the derivation is
stated over are the direct image `i_*𝒞_{Z/X}` with its scalars restricted along the split
surjection, so the action has to be moved across
`Stacks.Sheaves.RingedToposModules.smul_pullbackModuleObj_restrictScalars_commRing`.

It is a declaration of its own because the budget is per declaration: inlined into
`AlgebraicGeometry.Space.conormalSplitIdealDerivation` the two together exhaust the heartbeat
budget, and separately each is seconds. -/
theorem conormalDirectImageNu_smul_structureSharp (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((directImageInverseImageStructureSheaf B S hS
      (subspaceInclusion B S hS X Z)).obj.obj U))
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    conormalDirectImageNu B S hS X Z U
        (directImageInverseImageIdealSmul B S hS X Z U a y) =
      (show ToType ((pushforwardRingSheaf (subspaceToposHom B S hS X Z)
          (structureRingSheaf B S hS (subspaceSpace B S hS Z))).obj.obj U) from
        ((directImageStructureSharpInverseImage B S hS
          (subspaceInclusion B S hS X Z)).hom.app U) a) •
        (show ToType ((conormalSplitTarget B S hS X Z).val.obj U) from
          conormalDirectImageNu B S hS X Z U y) :=
  Eq.trans (conormalDirectImageNu_smul B S hS X Z U a y)
    (smul_pushforwardModuleFunctor_restrictScalars (subspaceToposHom B S hS X Z)
      (structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z))
      (conormalModule B S hS X Z) U a (conormalDirectImageNu B S hS X Z U y))

/-- The derivation `a ↦ ν(a - g^♯(i^♯a))` of `i_*i⁻¹𝒪_X` relative to
`AlgebraicGeometry.Space.conormalSplitBase`, with values in the direct image `i_*𝒞_{Z/X}` with
its scalars restricted along the split surjection `i_*(i^♯) : i_*i⁻¹𝒪_X ⟶ i_*𝒪_Z`, where `ν` is
`AlgebraicGeometry.Space.conormalDirectImageNu`. -/
noncomputable def conormalSplitIdealDerivation :
    (PresheafOfModules.splitCoefficients
        (directImageStructureSharpInverseImage B S hS
          (subspaceInclusion B S hS X Z)).hom
        (conormalSplitTarget B S hS X Z).val).Derivation'
      (conormalSplitBase B S hS X Z g).hom := by
  refine PresheafOfModules.splitIdealDerivation
    (directImageStructureSharpInverseImage B S hS (subspaceInclusion B S hS X Z)).hom
    (directImageInverseImageStructureSharpSection B S hS
      (subspaceInclusion B S hS X Z) g hg).hom
    (conormalSplitTarget B S hS X Z).val
    (fun U ↦ ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U))
    (directImageInverseImageIdealIota B S hS X Z)
    (directImageInverseImageStructureSharpSection_comp_hom B S hS X Z g hg)
    (exists_directImageInverseImageIdealIota B S hS X Z)
    (conormalDirectImageNu B S hS X Z)
    (fun _ y z ↦ y + z)
    (directImageInverseImageIdealSmul B S hS X Z)
    (fun {_ _} f y ↦ (directImageInverseImageIdeal B S hS X Z).val.map f y)
    (injective_directImageInverseImageIdealIota B S hS X Z)
    (directImageInverseImageIdealIota_add B S hS X Z)
    (directImageInverseImageIdealIota_smul B S hS X Z)
    (fun {_ _} f y ↦ directImageInverseImageIdealIota_map B S hS X Z f y)
    (conormalDirectImageNu_add B S hS X Z)
    ?_
    (fun {_ _} f y ↦ conormalDirectImageNu_map B S hS X Z f y)
    (conormalSplitBase B S hS X Z g).hom
    (conormalSplitBase_comp_apply B S hS X Z g hg)
  exact conormalDirectImageNu_smul_structureSharp B S hS X Z

/-! ### Step 2: the derivation of `𝒪_X` -/

section Transport

universe t₀ w₀ v₀ u₀

variable {E : Type u₀} [Category.{v₀} E] {S₀ R₀ : Eᵒᵖ ⥤ CommRingCat.{w₀}} {φ : S₀ ⟶ R₀}

/-- **Transport of a relative derivation along an equality of its coefficients.**  This is
`h ▸ D`, named rather than written inline so that
`AlgebraicGeometry.Space.derivationTransport_d` can describe its values; it is the plain
counterpart of `AlgebraicGeometry.Space.derivationSubtypeTransport`. -/
noncomputable def derivationTransport
    {M N : PresheafOfModules.{w₀} (R₀ ⋙ forget₂ CommRingCat.{w₀} RingCat.{w₀})} (h : M = N)
    (D : M.Derivation' φ) : N.Derivation' φ :=
  h ▸ D

/-- **The transport acts on the value of a derivation on a local section by a cast**, the cast
being the one the equality of the coefficients induces on sections.  At a concrete transport
between two restrictions of scalars of one presheaf of modules the two section types are the same
and the cast disappears. -/
theorem derivationTransport_d
    {M N : PresheafOfModules.{w₀} (R₀ ⋙ forget₂ CommRingCat.{w₀} RingCat.{w₀})} (h : M = N)
    (D : M.Derivation' φ) (Y : Eᵒᵖ) (y : ToType (R₀.obj Y)) :
    (derivationTransport h D).d y =
      cast (congrArg (fun K : PresheafOfModules.{w₀}
          (R₀ ⋙ forget₂ CommRingCat.{w₀} RingCat.{w₀}) ↦ ToType (K.obj Y)) h) (D.d y) := by
  cases h
  rfl

end Transport

/-- **The `Z`-derivation of `𝒪_X` of Stacks 02HP for a closed subspace with a left inverse.**
`AlgebraicGeometry.Space.conormalSplitIdealDerivation` is a derivation of `i_*i⁻¹𝒪_X`; this is it
precomposed with the unit `η : 𝒪_X ⟶ i_*i⁻¹𝒪_X` of Stacks 00YV, so a `Z`-derivation of `𝒪_X` with
values in the direct image `i_*𝒞_{Z/X}` of Stacks 03LU.

The two hypotheses `Stacks.Sheaves.RingedToposModules.derivationPrecompRing` asks of `η` are
exactly the two known compatibilities: that it is compatible with the base is `rfl`, the base
`AlgebraicGeometry.Space.conormalSplitBase` being `g^♯` followed by `η` by definition, and that
it is compatible with the augmentation is
`AlgebraicGeometry.Space.unit_comp_map_structureSharpInverseImage`.

The coefficients `derivationPrecompRing` produces are `i_*𝒞_{Z/X}` with the scalars restricted
along the forgetful image of `AlgebraicGeometry.Space.structureSharpCommRing`, which is
`AlgebraicGeometry.Space.modulePushforward` only after
`AlgebraicGeometry.Space.map_structureSharpCommRing` — that map is a `Classical.choose` and is
irreducible, so the identification is not definitional.  It is
`AlgebraicGeometry.Space.restrictModuleAlong_moduleDirectImage`, transported along by
`AlgebraicGeometry.Space.derivationTransport`. -/
noncomputable def conormalSplitDerivation :
    ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        (conormalModule B S hS X Z)).val.Derivation'
      (structureSharpInverseImage B S hS g).hom :=
  derivationTransport
    (restrictModuleAlong_moduleDirectImage B S hS (subspaceInclusion B S hS X Z)
      (conormalModule B S hS X Z))
    (derivationPrecompRing
      (directImageModuleOver B S hS (subspaceInclusion B S hS X Z)
        (conormalModule B S hS X Z))
      (directImageInverseImageStructureUnit B S hS X Z) rfl
      (unit_comp_map_structureSharpInverseImage B S hS (subspaceInclusion B S hS X Z))
      (conormalSplitIdealDerivation B S hS X Z g hg))

/-- **The value of the derivation of `𝒪_X`**: it is the derivation of `i_*i⁻¹𝒪_X` evaluated at
the image of the section under the unit `η`.  The transport of the coefficients contributes a
cast between two restrictions of scalars of one presheaf of modules, which have the same
sections. -/
theorem conormalSplitDerivation_d (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (a : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj U)) :
    (conormalSplitDerivation B S hS X Z g hg).d a =
      (conormalSplitIdealDerivation B S hS X Z g hg).d
        (((directImageInverseImageStructureUnit B S hS X Z).hom.app U) a) :=
  derivationTransport_d _ _ U a

/-- **The derivation restricted to the defining ideal sheaf is the coefficient map.**  This is
`PresheafOfModules.splitIdealDerivation_d_iota` at the data above. -/
theorem conormalSplitIdealDerivation_d_iota (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageIdeal B S hS X Z).val.obj U)) :
    (conormalSplitIdealDerivation B S hS X Z g hg).d
        (directImageInverseImageIdealIota B S hS X Z U y) =
      conormalDirectImageNu B S hS X Z U y :=
  PresheafOfModules.splitIdealDerivation_d_iota _ _ _ _ _ _ _ _ _ _ _ _
    (directImageInverseImageIdealIota_eq_zero B S hS X Z) _ _ _ _ _ _ _ _ U y

/-- **The derivation of Stacks 02HP on a section of the defining ideal sheaf is the coefficient
map at the unit of Stacks 03D3.**  The unit `η : 𝒪_X ⟶ i_*i⁻¹𝒪_X` carries a section of `𝓘` into
`i_*i⁻¹𝓘` (`AlgebraicGeometry.Space.directImageInverseImageIdealIota_unit`), and the derivation
restricted to `i_*i⁻¹𝓘` is the coefficient map
(`AlgebraicGeometry.Space.conormalSplitIdealDerivation_d_iota`). -/
theorem conormalSplitDerivation_d_definingIdeal (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    (conormalSplitDerivation B S hS X Z g hg).d x.1 =
      conormalDirectImageNu B S hS X Z U
        (directImageInverseImageIdealUnit B S hS X Z U x) :=
  Eq.trans (conormalSplitDerivation_d B S hS X Z g hg U x.1)
    (Eq.trans
      (congrArg (conormalSplitIdealDerivation B S hS X Z g hg).d
        (directImageInverseImageIdealIota_unit B S hS X Z U x).symm)
      (conormalSplitIdealDerivation_d_iota B S hS X Z g hg U
        (directImageInverseImageIdealUnit B S hS X Z U x)))

/-- **The derivation of Stacks 02HP restricted to the defining ideal sheaf is the unit of
Stacks 03LU.**  This is the hypothesis Equation (0619) turns into a retraction of the first arrow:
`AlgebraicGeometry.Space.conormalSplitDerivation_d_definingIdeal` together with
`AlgebraicGeometry.Space.modulePullbackAdjunction_unit_definingIdealSheaf_val_app`. -/
theorem conormalSplitDerivation_d_unit (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj U) :
    (conormalSplitDerivation B S hS X Z g hg).d x.1 =
      ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules).val.app U x :=
  Eq.trans (conormalSplitDerivation_d_definingIdeal B S hS X Z g hg U x)
    (modulePullbackAdjunction_unit_definingIdealSheaf_val_app B S hS X Z U x).symm

/-! ### Step 4: monomorphy of the first arrow -/

section Transposition

variable {X' Y' Bb' : AlgebraicSpaces B S hS}

/-- **Equation (0619) at the morphism it attaches to a derivation, read on sections.**  The
direct image of `(0619)⁻¹ D` carries the value of
`AlgebraicGeometry.Space.pullbackUnitDerivation` on a local section to the value of `D` there.

Stated with the morphism, the structure morphism, the coefficients and the derivation all
variables: the transposition is then applied to a variable, so
`Equiv.apply_symm_apply` is available on the nose, while at a concrete inclusion identifying the
transpose of a *named* retraction with the derivation it came from exhausts the heartbeat
budget. -/
theorem map_derivationDirectImageEquiv_symm_pullbackUnitDerivation (f : X' ⟶ Y')
    (b : Y' ⟶ Bb') (C : Modules.{u, u} B S hS X'.1 X'.2)
    (D : ((modulePushforward B S hS f).obj C).val.Derivation'
      (structureSharpInverseImage B S hS b).hom)
    (U : (SmallEtale B S hS Y'.1)ᵒᵖ)
    (t : ToType ((structureRingSheaf B S hS Y').obj.obj U)) :
    (((modulePushforward B S hS f).map
          ((derivationDirectImageEquiv B S hS f b C).symm D)).val.app U).hom
        ((pullbackUnitDerivation B S hS f b).d t) = D.d t :=
  Eq.trans
    (derivationDirectImageEquiv_d B S hS f b C
      ((derivationDirectImageEquiv B S hS f b C).symm D) U t).symm
    (PresheafOfModules.Derivation.congr_d
      ((derivationDirectImageEquiv B S hS f b C).apply_symm_apply D) t)

/-- The transpose across `f^* ⊣ f_*` of the composite of a transposed map with `r` is the map
followed by `f_*r`. -/
private theorem homEquiv_submoduleTranspose_comp (f : X' ⟶ Y')
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y')).Submodule)
    (M N : Modules.{u, u} B S hS X'.1 X'.2)
    (u : I.toSheafOfModules ⟶ (modulePushforward B S hS f).obj M) (r : M ⟶ N) :
    ((modulePullbackAdjunction B S hS f).homEquiv I.toSheafOfModules N)
        (submoduleTranspose B S hS f I M u ≫ r) =
      u ≫ (modulePushforward B S hS f).map r :=
  Eq.trans (Adjunction.homEquiv_naturality_right _ _ _)
    (congrArg (fun t ↦ t ≫ (modulePushforward B S hS f).map r)
      (homEquiv_submoduleTranspose B S hS f I M u))

/-- **A derivation restricting on a sheaf of ideals to the unit of Stacks 03LU transposes to a
retraction of the transpose of that restriction.**  Let `f : X' ⟶ Y'` be a morphism of algebraic
spaces, `b : Y' ⟶ Bb'` a structure morphism and `𝓘 ⊆ 𝒪_{Y'}` a subsheaf of the structure sheaf.
Let

* `u : 𝓘 ⟶ f_*f^*Ω_{Y'/Bb'}` carry a local section `a` of `𝓘` to `E(a)`, where `E` is
  `d_{Y'/Bb'}` followed by the unit of `f^* ⊣ f_*` (`hu`, `hE`);
* `D` be a `Bb'`-derivation of `𝒪_{Y'}` with values in `f_*f^*𝓘` carrying a local section `a` of
  `𝓘` to the unit of `f^* ⊣ f_*` at `a` (`hD`);
* `α` be the transpose of `u`, and `r` the morphism Equation (0619) attaches to `D` (`hα`, `hr`).

Then `α ≫ r = 𝟙`, so `α` is a split monomorphism.

Both arrows and both derivations are supplied as data with their defining equations rather than
written out.  **That is what makes the statement instantiable at a concrete inclusion**: a
consumer discharges each equation by `rfl` at one and the same type, whereas a statement phrased
with the transposes written out would make the elaborator identify them underneath
`PresheafOfModules.Derivation.d` at a concrete small étale ringed topos, which does not fit the
heartbeat budget.  This is the device of
`AlgebraicGeometry.Space.submoduleTranspose_comp_pullbackDifferentialsMap_eq_zero'`, for the same
reason. -/
theorem submoduleTranspose_comp_derivationDirectImageEquiv_symm_eq_id (f : X' ⟶ Y')
    (b : Y' ⟶ Bb')
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y')).Submodule)
    (u : I.toSheafOfModules ⟶ (modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS b)))
    (E : ((modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj
        (sheafOfDifferentials B S hS b))).val.Derivation'
      (structureSharpInverseImage B S hS b).hom)
    (hE : E = pullbackUnitDerivation B S hS f b)
    (hu : ∀ (U : (SmallEtale B S hS Y'.1)ᵒᵖ) (x : I.toSheafOfModules.val.obj U),
      (ModuleCat.Hom.hom (u.val.app U)) x = E.d x.1)
    (D : ((modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj I.toSheafOfModules)).val.Derivation'
      (structureSharpInverseImage B S hS b).hom)
    (hD : ∀ (U : (SmallEtale B S hS Y'.1)ᵒᵖ) (x : I.toSheafOfModules.val.obj U),
      D.d x.1 = ((modulePullbackAdjunction B S hS f).unit.app
        I.toSheafOfModules).val.app U x)
    {α : (modulePullback B S hS f).obj I.toSheafOfModules ⟶
      (modulePullback B S hS f).obj (sheafOfDifferentials B S hS b)}
    (hα : α = submoduleTranspose B S hS f I
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS b)) u)
    {r : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS b) ⟶
      (modulePullback B S hS f).obj I.toSheafOfModules}
    (hr : r = (derivationDirectImageEquiv B S hS f b
      ((modulePullback B S hS f).obj I.toSheafOfModules)).symm D) :
    α ≫ r = 𝟙 ((modulePullback B S hS f).obj I.toSheafOfModules) := by
  subst hE
  subst hα
  subst hr
  refine ((modulePullbackAdjunction B S hS f).homEquiv I.toSheafOfModules
    ((modulePullback B S hS f).obj I.toSheafOfModules)).injective ?_
  refine Eq.trans (homEquiv_submoduleTranspose_comp B S hS f I _ _ u _) ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_id (modulePullbackAdjunction B S hS f)
    I.toSheafOfModules).symm
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  exact Eq.trans
    (congrArg (fun y ↦ ModuleCat.Hom.hom
        (((modulePushforward B S hS f).map ((derivationDirectImageEquiv B S hS f b
          ((modulePullback B S hS f).obj I.toSheafOfModules)).symm D)).val.app U) y)
      (hu U x))
    (Eq.trans
      (map_derivationDirectImageEquiv_symm_pullbackUnitDerivation B S hS f b
        ((modulePullback B S hS f).obj I.toSheafOfModules) D U x.1)
      (hD U x))

end Transposition

section AnyBase

variable {Bb : AlgebraicSpaces B S hS}

/-- The first arrow of Stacks 05ZA, at the reading whose source is `i^*𝓘`, is by definition the
transpose of `AlgebraicGeometry.Space.conormalSequenceIdealDifferential`.  It is stated so that
the instantiations below supply it as a proved equation instead of re-deciding it there; the
heartbeat budget is per declaration. -/
theorem conormalSequenceIdealPullbackMap_eq (b : X ⟶ Bb) :
    conormalSequenceIdealPullbackMap B S hS Z b =
      submoduleTranspose B S hS (subspaceInclusion B S hS X Z) (definingIdealSheaf B S hS X Z)
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          (sheafOfDifferentials B S hS b))
        (conormalSequenceIdealDifferential B S hS Z b) :=
  rfl

/-- The derivation that induces the first arrow of Stacks 05ZA is by definition `d_{X/Bb}`
followed by the unit of `i^* ⊣ i_*`, that is,
`AlgebraicGeometry.Space.pullbackUnitDerivation`. -/
theorem conormalSequenceUnitDerivation_eq (b : X ⟶ Bb) :
    conormalSequenceUnitDerivation B S hS Z b =
      pullbackUnitDerivation B S hS (subspaceInclusion B S hS X Z) b :=
  rfl

end AnyBase

/-- **The first arrow of Stacks 05ZA over the base `Z` has a retraction**, at the reading
`AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap` of the arrow whose source is `i^*𝓘`.
The retraction is the morphism `i^*Ω_{X/Z} ⟶ i^*𝓘 = 𝒞_{Z/X}` that Equation (0619) attaches to the
derivation `AlgebraicGeometry.Space.conormalSplitDerivation` of Stacks 02HP.

This is `AlgebraicGeometry.Space.submoduleTranspose_comp_derivationDirectImageEquiv_symm_eq_id`
at the data of Stacks 02HP: `hu` is the clause
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_val_app_apply` of Stacks 05ZA and `hD`
is `AlgebraicGeometry.Space.conormalSplitDerivation_d_unit`, while `hE` and `hα` are the two
`rfl` equations above.

**The retraction is written out rather than named**, and that is why `hr` is `rfl` on one and the
same term: behind a name — whether a semireducible definition or a reducible abbreviation — `hr`
becomes an equation whose two sides have to be identified underneath the transposition of
Stacks 03LU, which does not fit the heartbeat budget.
`AlgebraicGeometry.Space.conormalSplitRetraction` names it below, for consumers. -/
theorem conormalSequenceIdealPullbackMap_comp_derivationDirectImageEquiv_symm :
    conormalSequenceIdealPullbackMap B S hS Z g ≫
        (derivationDirectImageEquiv B S hS (subspaceInclusion B S hS X Z) g
            ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
              (definingIdealSheaf B S hS X Z).toSheafOfModules)).symm
          (conormalSplitDerivation B S hS X Z g hg) =
      𝟙 ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules) :=
  submoduleTranspose_comp_derivationDirectImageEquiv_symm_eq_id B S hS
    (subspaceInclusion B S hS X Z) g (definingIdealSheaf B S hS X Z)
    (conormalSequenceIdealDifferential B S hS Z g)
    (conormalSequenceUnitDerivation B S hS Z g)
    (conormalSequenceUnitDerivation_eq B S hS X Z g)
    (conormalSequenceIdealDifferential_val_app_apply B S hS Z g)
    (conormalSplitDerivation B S hS X Z g hg)
    (conormalSplitDerivation_d_unit B S hS X Z g hg)
    (conormalSequenceIdealPullbackMap_eq B S hS X Z g) rfl

/-- **The retraction of the first arrow of Stacks 05ZA over the base `Z`**, named: the morphism
`i^*Ω_{X/Z} ⟶ 𝒞_{Z/X}` that Equation (0619) attaches to the derivation of Stacks 02HP.  Its
target is written as `i^*𝓘`, which is the conormal module of Stacks 04CN by
`AlgebraicGeometry.Space.conormalModule_eq`. -/
noncomputable abbrev conormalSplitRetraction :
    (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (sheafOfDifferentials B S hS g) ⟶
      (modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules :=
  (derivationDirectImageEquiv B S hS (subspaceInclusion B S hS X Z) g
      ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules)).symm
    (conormalSplitDerivation B S hS X Z g hg)

include hg in
/-- **The first arrow of Stacks 05ZA over the base `Z` is a split monomorphism**, at the reading
whose source is `i^*𝓘`. -/
theorem isSplitMono_conormalSequenceIdealPullbackMap :
    IsSplitMono (conormalSequenceIdealPullbackMap B S hS Z g) :=
  IsSplitMono.mk' ⟨_,
    conormalSequenceIdealPullbackMap_comp_derivationDirectImageEquiv_symm B S hS X Z g hg⟩

include hg in
/-- **Stacks 05ZB's injectivity clause over the base `Z`.**  At a bundled closed subspace
`Z ⊆ X` of an algebraic space, with a left inverse `g : X ⟶ Z` of its inclusion, the first arrow
`𝒞_{Z/X} ⟶ i^*Ω_{X/Z}` of the conormal sequence of Stacks 05ZA over the base `Z` — the base being
`Z` itself through `g` — is a monomorphism.

No compatibility of `g` with an ambient base is used: over `Z` the left inverse *is* the structure
morphism.  This is
`AlgebraicGeometry.Space.isSplitMono_conormalSequenceIdealPullbackMap` read at
`AlgebraicGeometry.Space.conormalSequenceFirstMap`, which is that arrow with its source written as
the conormal module of Stacks 04CN. -/
theorem mono_conormalSequenceFirstMap_of_retraction :
    Mono (conormalSequenceFirstMap B S hS Z g) :=
  IsSplitMono.mono (conormalSequenceFirstMap B S hS Z g)
    (hf := isSplitMono_conormalSequenceIdealPullbackMap B S hS X Z g hg)

/-! ### The arbitrary base -/

section BaseGeneric

variable {X' Y' Bb₁ Bb₂ : AlgebraicSpaces B S hS}

/-- **The first arrows of Stacks 05ZA over two bases are carried to one another by the inverse
image of a compatible comparison of the sheaves of differentials.**  Let `f : X' ⟶ Y'` be a
morphism of algebraic spaces, `b₁ : Y' ⟶ Bb₁` and `b₂ : Y' ⟶ Bb₂` two structure morphisms, and
`𝓘 ⊆ 𝒪_{Y'}` a subsheaf of the structure sheaf.  Let `Φ : Ω_{Y'/Bb₁} ⟶ Ω_{Y'/Bb₂}` carry
`d_{Y'/Bb₁}` to a derivation `E` whose values are those of `d_{Y'/Bb₂}` (`hΦ`, `hE`), and let
`α₁`, `α₂` be the transposes of morphisms `u₁`, `u₂` out of `𝓘` whose values are those of
`d_{Y'/Bb₁}`, `d_{Y'/Bb₂}` followed by the unit of `f^* ⊣ f_*`.  Then `α₁ ≫ f^*Φ = α₂`.

Everything is a datum with its defining equation, for the reason recorded at
`AlgebraicGeometry.Space.submoduleTranspose_comp_derivationDirectImageEquiv_symm_eq_id`. -/
theorem submoduleTranspose_comp_map_eq_submoduleTranspose (f : X' ⟶ Y')
    (b₁ : Y' ⟶ Bb₁) (b₂ : Y' ⟶ Bb₂)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS Y')).Submodule)
    (Φ : sheafOfDifferentials B S hS b₁ ⟶ sheafOfDifferentials B S hS b₂)
    (E : (sheafOfDifferentials B S hS b₂).val.Derivation'
      (structureSharpInverseImage B S hS b₁).hom)
    (hΦ : (universalDerivation B S hS b₁).postcomp Φ.val = E)
    (hE : ∀ (U : (SmallEtale B S hS Y'.1)ᵒᵖ)
        (t : ToType ((structureRingSheaf B S hS Y').obj.obj U)),
      E.d t = (universalDerivation B S hS b₂).d t)
    (u₁ : I.toSheafOfModules ⟶ (modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS b₁)))
    (D₁ : ((modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj
        (sheafOfDifferentials B S hS b₁))).val.Derivation'
      (structureSharpInverseImage B S hS b₁).hom)
    (hD₁ : D₁ = pullbackUnitDerivation B S hS f b₁)
    (hu₁ : ∀ (U : (SmallEtale B S hS Y'.1)ᵒᵖ) (x : I.toSheafOfModules.val.obj U),
      (ModuleCat.Hom.hom (u₁.val.app U)) x = D₁.d x.1)
    (u₂ : I.toSheafOfModules ⟶ (modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS b₂)))
    (D₂ : ((modulePushforward B S hS f).obj
      ((modulePullback B S hS f).obj
        (sheafOfDifferentials B S hS b₂))).val.Derivation'
      (structureSharpInverseImage B S hS b₂).hom)
    (hD₂ : D₂ = pullbackUnitDerivation B S hS f b₂)
    (hu₂ : ∀ (U : (SmallEtale B S hS Y'.1)ᵒᵖ) (x : I.toSheafOfModules.val.obj U),
      (ModuleCat.Hom.hom (u₂.val.app U)) x = D₂.d x.1)
    {α₁ : (modulePullback B S hS f).obj I.toSheafOfModules ⟶
      (modulePullback B S hS f).obj (sheafOfDifferentials B S hS b₁)}
    (hα₁ : α₁ = submoduleTranspose B S hS f I
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS b₁)) u₁)
    {α₂ : (modulePullback B S hS f).obj I.toSheafOfModules ⟶
      (modulePullback B S hS f).obj (sheafOfDifferentials B S hS b₂)}
    (hα₂ : α₂ = submoduleTranspose B S hS f I
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS b₂)) u₂) :
    α₁ ≫ (modulePullback B S hS f).map Φ = α₂ := by
  subst hD₁
  subst hD₂
  subst hα₁
  subst hα₂
  refine ((modulePullbackAdjunction B S hS f).homEquiv I.toSheafOfModules
    ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS b₂))).injective ?_
  refine Eq.trans (homEquiv_submoduleTranspose_comp B S hS f I _ _ u₁ _) ?_
  refine Eq.trans ?_ (homEquiv_submoduleTranspose B S hS f I
    ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS b₂)) u₂).symm
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  refine Eq.trans (congrArg (fun y ↦ ModuleCat.Hom.hom
      (((modulePushforward B S hS f).map
        ((modulePullback B S hS f).map Φ)).val.app U) y) (hu₁ U x)) ?_
  refine Eq.trans ?_ (hu₂ U x).symm
  refine Eq.trans (PresheafOfModules.Derivation.postcomp_d_apply
    (pullbackUnitDerivation B S hS f b₁)
    ((modulePushforward B S hS f).map
      ((modulePullback B S hS f).map Φ)).val x.1).symm ?_
  refine Eq.trans (PresheafOfModules.Derivation.congr_d
    (pullbackUnitDerivation_postcomp_map_map B S hS f b₁
      (sheafOfDifferentials B S hS b₂) Φ E hΦ) x.1) ?_
  refine Eq.trans (PresheafOfModules.Derivation.postcomp_d_apply E
    ((modulePullbackAdjunction B S hS f).unit.app
      (sheafOfDifferentials B S hS b₂)).val x.1) ?_
  refine Eq.trans (congrArg (fun m ↦ ModuleCat.Hom.hom
      (((modulePullbackAdjunction B S hS f).unit.app
        (sheafOfDifferentials B S hS b₂)).val.app U) m) (hE U x.1)) ?_
  exact (PresheafOfModules.Derivation.postcomp_d_apply (universalDerivation B S hS b₂)
    ((modulePullbackAdjunction B S hS f).unit.app
      (sheafOfDifferentials B S hS b₂)).val x.1).symm

end BaseGeneric

section Base

variable {Bb : AlgebraicSpaces B S hS}

/-- The canonical map `Ω_{X/Bb} ⟶ Ω_{X/Z}` of Stacks 05Z8, for the factorization of the structure
morphism of `X` through the left inverse `g`. -/
noncomputable abbrev conormalSplitToRelativeDifferentials (b : X ⟶ Bb) :
    sheafOfDifferentials B S hS (g ≫ subspaceInclusion B S hS X Z ≫ b) ⟶
      sheafOfDifferentials B S hS g :=
  toRelativeDifferentials B S hS g (subspaceInclusion B S hS X Z ≫ b)

/-- The map of Stacks 05Z8 carries `d_{X/Bb}` to `d_{X/Z}`, in the shape
`AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_map_map` consumes.  It is the defining
property of `AlgebraicGeometry.Space.toRelativeDifferentials`, read back through the bijection of
Stacks 04CT it was built by. -/
theorem postcomp_conormalSplitToRelativeDifferentials (b : X ⟶ Bb) :
    (universalDerivation B S hS (g ≫ subspaceInclusion B S hS X Z ≫ b)).postcomp
        (conormalSplitToRelativeDifferentials B S hS X Z g b).val =
      relativeUniversalDerivation B S hS g (subspaceInclusion B S hS X Z ≫ b) :=
  Eq.trans
    (differentialsHomEquiv_apply B S hS (g ≫ subspaceInclusion B S hS X Z ≫ b)
      (sheafOfDifferentials B S hS g)
      (conormalSplitToRelativeDifferentials B S hS X Z g b)).symm
    ((differentialsHomEquiv B S hS (g ≫ subspaceInclusion B S hS X Z ≫ b)
      (sheafOfDifferentials B S hS g)).apply_symm_apply
        (relativeUniversalDerivation B S hS g (subspaceInclusion B S hS X Z ≫ b)))

/-- **The first arrow over an ambient base, followed by the inverse image along `i` of the map of
Stacks 05Z8, is the first arrow over `Z`**, at the reading of both arrows whose source is `i^*𝓘`.

This is `AlgebraicGeometry.Space.submoduleTranspose_comp_map_eq_submoduleTranspose` at the two
structure morphisms `g ≫ i ≫ b` and `g`; `hE` holds because the `d` of
`AlgebraicGeometry.Space.relativeUniversalDerivation` *is* that of
`AlgebraicGeometry.Space.universalDerivation`. -/
theorem conormalSequenceIdealPullbackMap_comp_map_conormalSplitToRelativeDifferentials
    (b : X ⟶ Bb) :
    conormalSequenceIdealPullbackMap B S hS Z (g ≫ subspaceInclusion B S hS X Z ≫ b) ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          (conormalSplitToRelativeDifferentials B S hS X Z g b) =
      conormalSequenceIdealPullbackMap B S hS Z g :=
  submoduleTranspose_comp_map_eq_submoduleTranspose B S hS
    (subspaceInclusion B S hS X Z) (g ≫ subspaceInclusion B S hS X Z ≫ b) g
    (definingIdealSheaf B S hS X Z)
    (conormalSplitToRelativeDifferentials B S hS X Z g b)
    (relativeUniversalDerivation B S hS g (subspaceInclusion B S hS X Z ≫ b))
    (postcomp_conormalSplitToRelativeDifferentials B S hS X Z g b)
    (fun _ _ ↦ rfl)
    (conormalSequenceIdealDifferential B S hS Z (g ≫ subspaceInclusion B S hS X Z ≫ b))
    (conormalSequenceUnitDerivation B S hS Z (g ≫ subspaceInclusion B S hS X Z ≫ b))
    (conormalSequenceUnitDerivation_eq B S hS X Z (g ≫ subspaceInclusion B S hS X Z ≫ b))
    (conormalSequenceIdealDifferential_val_app_apply B S hS Z
      (g ≫ subspaceInclusion B S hS X Z ≫ b))
    (conormalSequenceIdealDifferential B S hS Z g)
    (conormalSequenceUnitDerivation B S hS Z g)
    (conormalSequenceUnitDerivation_eq B S hS X Z g)
    (conormalSequenceIdealDifferential_val_app_apply B S hS Z g)
    (conormalSequenceIdealPullbackMap_eq B S hS X Z
      (g ≫ subspaceInclusion B S hS X Z ≫ b))
    (conormalSequenceIdealPullbackMap_eq B S hS X Z g)

include hg in
/-- **Stacks 05ZB's injectivity clause, at an arbitrary base.**  At a bundled closed subspace
`Z ⊆ X` of an algebraic space over `Bb` with structure morphism `b : X ⟶ Bb`, whose inclusion has
a left inverse `g` over `Bb`, the first arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/Bb}` of the conormal sequence of
Stacks 05ZA is a monomorphism.

The first arrow over `Bb`, followed by the inverse image along `i` of the canonical map
`Ω_{X/Bb} ⟶ Ω_{X/Z}` of Stacks 05Z8, is the first arrow over `Z`, which is a split monomorphism
by `AlgebraicGeometry.Space.isSplitMono_conormalSequenceIdealPullbackMap`; so the first arrow over
`Bb` is a monomorphism by `CategoryTheory.mono_of_mono_fac`.  The hypothesis that `g` is a
morphism over `Bb` enters only to identify `Ω_{X/Bb}` with `Ω_{X/(g ≫ i ≫ b)}`. -/
theorem mono_conormalSequenceFirstMap (b : X ⟶ Bb)
    (hgb : g ≫ subspaceInclusion B S hS X Z ≫ b = b) :
    Mono (conormalSequenceFirstMap B S hS Z b) :=
  have : Mono (conormalSequenceIdealPullbackMap B S hS Z g) :=
    IsSplitMono.mono (conormalSequenceIdealPullbackMap B S hS Z g)
      (hf := isSplitMono_conormalSequenceIdealPullbackMap B S hS X Z g hg)
  have : Mono (conormalSequenceIdealPullbackMap B S hS Z
      (g ≫ subspaceInclusion B S hS X Z ≫ b)) :=
    mono_of_mono_fac
      (conormalSequenceIdealPullbackMap_comp_map_conormalSplitToRelativeDifferentials
        B S hS X Z g b)
  hgb ▸ this

end Base

/-! ### Stacks 05ZB in full -/

section Full

variable {X' Bb : AlgebraicSpaces B S hS}

include hg in
/-- **Stacks 05ZB, the global clause in full.**  Let `Z ⊆ X` be a closed subspace of an algebraic
space over `Bb` with structure morphism `b : X ⟶ Bb`, and let `g : X ⟶ Z` be a left inverse over
`Bb` of its inclusion.  Then the conormal sequence of Stacks 05ZA
```
  0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
is **split exact**: it admits a `CategoryTheory.ShortComplex.Splitting`, that is a retraction of
the first arrow and a section of the second summing to the identity — so in particular the first
arrow is a monomorphism, the sequence is exact at its middle term and the second arrow is a split
epimorphism.

The exactness and the splitness of the second arrow are
`AlgebraicGeometry.Space.conormalSequence_splitExact`; what completes the tag is the injectivity
of the first arrow, `AlgebraicGeometry.Space.mono_conormalSequenceFirstMap`, which
`AlgebraicGeometry.Space.nonempty_conormalSequence_splitting_iff_mono` turns into the full
splitting. -/
@[stacks 05ZB "the global clause in full at the inclusion of a bundled subspace `Z ⊆ X` of an \
algebraic space over `B`, that inclusion having a left inverse over `B`: the conormal sequence \
of 05ZA is split exact, that is, it admits a `CategoryTheory.ShortComplex.Splitting`: the first \
arrow `conormalSequenceFirstMap` is a monomorphism, the sequence is exact at the middle term \
`i^*Ω_{X/B}`, and the second arrow is a split epimorphism.  Stated at the canonical inclusion \
and at the registered first arrow, with no hypothesis beyond the tag's own left inverse over \
`B`.  The same clause at an arbitrary closed immersion, with no bundled subspace anywhere, is \
`nonempty_conormalSequenceKernel_splitting`, and at the generality the tag is stated at, an \
arbitrary immersion with a left inverse over `B`, it is \
`nonempty_conormalSequenceOfImmersion_splitting`"]
theorem nonempty_conormalSequence_splitting (b : X ⟶ Bb)
    (hgb : g ≫ subspaceInclusion B S hS X Z ≫ b = b) :
    Nonempty (ShortComplex.mk _ _
      (conormalSequenceFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS Z b)).Splitting :=
  (nonempty_conormalSequence_splitting_iff_mono B S hS Z b g hg hgb).2
    (mono_conormalSequenceFirstMap B S hS X Z g hg b hgb)

/-- **Stacks 05ZB, the étale-local clause in full.**  Let `Z ⊆ X` and `Z' ⊆ X'` be closed
subspaces, let `φ : X' ⟶ X` be étale, let `a : Z' ⟶ Z` be étale with `i' ≫ φ = a ≫ i` for the two
inclusions, and let `g' : X' ⟶ Z'` be a left inverse over `Bb` of the inclusion of `Z'`.  Then

* the restricted conormal sequence, the sequence of Stacks 05ZA at `Z' ⊆ X'` over `φ ≫ b`, is
  split exact;
* the inverse image along `a` of the second arrow of the unrestricted sequence is a split
  epimorphism.

As in `AlgebraicGeometry.Space.conormalSequence_splitExact_of_etale`, étaleness is assumed of `φ`
and of `a` separately rather than `Z'` being assumed to be the preimage of `Z`, which is weaker:
in the situation of the source `a` is a base change of `φ`. -/
@[stacks 05ZB "the étale-local clause in full: for closed subspaces `Z ⊆ X` and `Z' ⊆ X'` joined \
by an étale `φ : X' ⟶ X` and an étale `a : Z' ⟶ Z` over it, with the inclusion of `Z'` admitting \
a left inverse over `B`, the restricted conormal sequence of 05ZA is split exact — it admits a \
`CategoryTheory.ShortComplex.Splitting`, so its first arrow is a monomorphism, it is exact at the \
middle term and its second arrow is a split epimorphism — and the inverse image along `a` of the \
second arrow of the unrestricted sequence is a split epimorphism too, which is where the \
étale-localization clause of 04CU is consumed.  Stated at the two canonical inclusions and at the \
registered first arrow, with no hypothesis beyond the étale-local data of the tag"]
theorem nonempty_conormalSequence_splitting_of_etale
    (Z' : ClosedSubspaces B S hS X'.1) (b : X ⟶ Bb) (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (a : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
    (ha : IsEtale B S hS a.hom)
    (hsq : subspaceInclusion B S hS X' Z' ≫ φ = a ≫ subspaceInclusion B S hS X Z)
    (g' : X' ⟶ (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hg' : subspaceInclusion B S hS X' Z' ≫ g' =
      𝟙 (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hg'b : g' ≫ subspaceInclusion B S hS X' Z' ≫ φ ≫ b = φ ≫ b) :
    Nonempty (ShortComplex.mk _ _
          (conormalSequenceFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS Z'
            (φ ≫ b))).Splitting ∧
      IsSplitEpi ((modulePullback B S hS a).map
        (pullbackDifferentialsMap B S hS (subspaceInclusion B S hS X Z) b)) :=
  ⟨(nonempty_conormalSequence_splitting_iff_mono B S hS Z' (φ ≫ b) g' hg' hg'b).2
      (mono_conormalSequenceFirstMap B S hS X' Z' g' hg' (φ ≫ b) hg'b),
    isSplitEpi_map_pullbackDifferentialsMap_of_etale B S hS
      (subspaceInclusion B S hS X Z) b φ hφ (subspaceInclusion B S hS X' Z') a ha hsq g' hg'
      hg'b⟩

end Full

end AlgebraicGeometry.Space

end
