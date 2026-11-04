module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceClosedImmersionSplitExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceSplitMono
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdealSplitBase
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdealSplitKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdealUnitSections

/-!
# The conormal sequence of a closed immersion with a left inverse

Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over `B` and let `g : Y ⟶ X` be a left
inverse of `f`.  This file constructs the derivation of Stacks 02HP at `f` and shows that the
first arrow `𝓘_f ⟶ f^*Ω_{Y/B}` of the conormal sequence of Stacks 05ZA, in the kernel-ideal form
`AlgebraicGeometry.Space.kernelConormalFirstMap`, is a monomorphism.  Consequently the conormal
sequence is split exact, and so is its restriction along an étale morphism.

## Main definitions

* `AlgebraicGeometry.Space.kernelSplitTarget`: the coefficients, the direct image `f_*f^*𝓘_f`
  over `f_*𝒪_X`.
* `AlgebraicGeometry.Space.kernelSplitIdealDerivation`: the derivation of Stacks 02HP at a
  closed immersion with a left inverse, a derivation of `f_*f⁻¹𝒪_Y` relative to
  `AlgebraicGeometry.Space.kernelSplitBase`.
* `AlgebraicGeometry.Space.kernelSplitDerivation`: it precomposed with the unit
  `η : 𝒪_Y ⟶ f_*f⁻¹𝒪_Y`, an `X`-derivation of `𝒪_Y` with values in `f_*f^*𝓘_f`.
* `AlgebraicGeometry.Space.kernelSplitRetraction`: the retraction of the first arrow.

## Main results

* `AlgebraicGeometry.Space.isSplitMono_kernelConormalFirstMap`: the first arrow of the conormal
  sequence over the base `X` is a split monomorphism.
* `AlgebraicGeometry.Space.mono_kernelConormalFirstMap`: the first arrow of the conormal
  sequence over an arbitrary base is a monomorphism.
* `AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting`: the conormal sequence is
  split exact.
* `AlgebraicGeometry.Space.nonempty_conormalSequenceKernel_splitting_of_etale`: the étale-local
  form of the splitting.

## References

* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the sequence.
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

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom)
  (g : Y ⟶ X) (hg : f ≫ g = 𝟙 X)

/-- The first arrow of Stacks 05ZA at the kernel ideal sheaf is the transpose of
`AlgebraicGeometry.Space.kernelIdealUnitDifferential`. -/
theorem kernelConormalFirstMap_eq {Bb₀ : AlgebraicSpaces B S hS} (b : Y ⟶ Bb₀) :
    kernelConormalFirstMap B S hS f b =
      submoduleTranspose B S hS f (kernelIdealSheaf B S hS f)
        ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS b))
        (kernelIdealUnitDifferential B S hS f b) :=
  rfl

/-- The coefficients of the derivation of Stacks 02HP: the direct image `f_*f^*𝓘_f` along `f`
of the conormal module, as a module over `f_*𝒪_X`. -/
noncomputable abbrev kernelSplitTarget :=
  (pushforwardModuleFunctor (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureRingSheaf B S hS X)).obj (kernelConormalModule B S hS f)

/-- The coefficient map `AlgebraicGeometry.Space.kernelConormalDirectImageNu` is semilinear:
the action of a section of `f_*f⁻¹𝒪_Y` on `f_*f⁻¹𝓘_f` is carried to the action of its image in
`f_*𝒪_X` on the coefficients `AlgebraicGeometry.Space.kernelSplitTarget`. -/
theorem kernelConormalDirectImageNu_smul_structureSharp (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : ToType ((directImageInverseImageStructureSheaf B S hS f).obj.obj U))
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    kernelConormalDirectImageNu B S hS f U
        (directImageInverseImageKernelIdealSmul B S hS f U a y) =
      (show ToType ((pushforwardRingSheaf (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS X)).obj.obj U) from
        ((directImageStructureSharpInverseImage B S hS f).hom.app U) a) •
        (show ToType ((kernelSplitTarget B S hS f).val.obj U) from
          kernelConormalDirectImageNu B S hS f U y) :=
  Eq.trans (kernelConormalDirectImageNu_smul B S hS f U a y)
    (smul_pushforwardModuleFunctor_restrictScalars
      (smallEtaleRingedToposHom B S hS f).toToposHom
      (structureSharpInverseImage B S hS f)
      (kernelConormalModule B S hS f) U a
      (show ToType ((kernelSplitTarget B S hS f).val.obj U) from
        kernelConormalDirectImageNu B S hS f U y))

include hf hg in
/-- The derivation of Stacks 02HP at a closed immersion with a left inverse: a derivation of
`f_*f⁻¹𝒪_Y` relative to `AlgebraicGeometry.Space.kernelSplitBase`, with values in the
coefficients `AlgebraicGeometry.Space.kernelSplitTarget`. -/
noncomputable def kernelSplitIdealDerivation :
    (PresheafOfModules.splitCoefficients
        (directImageStructureSharpInverseImage B S hS f).hom
        (kernelSplitTarget B S hS f).val).Derivation'
      (kernelSplitBase B S hS f g).hom := by
  refine PresheafOfModules.splitIdealDerivation
    (directImageStructureSharpInverseImage B S hS f).hom
    (directImageInverseImageStructureSharpSection B S hS f g hg).hom
    (kernelSplitTarget B S hS f).val
    (fun U ↦ ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U))
    (directImageInverseImageKernelIdealIota B S hS f)
    (directImageInverseImageStructureSharpSection_comp_hom_of_hom B S hS f g hg)
    (exists_directImageInverseImageKernelIdealIota B S hS f hf)
    (kernelConormalDirectImageNu B S hS f)
    (fun _ y z ↦ y + z)
    (directImageInverseImageKernelIdealSmul B S hS f)
    (fun {_ _} h y ↦ (directImageInverseImageKernelIdeal B S hS f).val.map h y)
    (injective_directImageInverseImageKernelIdealIota B S hS f)
    (directImageInverseImageKernelIdealIota_add B S hS f)
    (directImageInverseImageKernelIdealIota_smul B S hS f)
    (fun {_ _} h y ↦ directImageInverseImageKernelIdealIota_map B S hS f h y)
    (kernelConormalDirectImageNu_add B S hS f)
    ?_
    (fun {_ _} h y ↦ kernelConormalDirectImageNu_map B S hS f h y)
    (kernelSplitBase B S hS f g).hom
    (kernelSplitBase_comp_apply B S hS f g hg)
  exact kernelConormalDirectImageNu_smul_structureSharp B S hS f

include hf hg in
/-- The `X`-derivation of `𝒪_Y` of Stacks 02HP at a closed immersion with a left inverse:
`AlgebraicGeometry.Space.kernelSplitIdealDerivation` precomposed with the unit
`η : 𝒪_Y ⟶ f_*f⁻¹𝒪_Y`, with values in the direct image `f_*f^*𝓘_f`. -/
noncomputable def kernelSplitDerivation :
    ((modulePushforward B S hS f).obj (kernelConormalModule B S hS f)).val.Derivation'
      (structureSharpInverseImage B S hS g).hom :=
  derivationTransport
    (restrictModuleAlong_moduleDirectImage B S hS f (kernelConormalModule B S hS f))
    (derivationPrecompRing
      (directImageModuleOver B S hS f (kernelConormalModule B S hS f))
      (directImageInverseImageStructureUnitOfHom B S hS f) rfl
      (unit_comp_map_structureSharpInverseImage B S hS f)
      (kernelSplitIdealDerivation B S hS f hf g hg))

include hf hg in
/-- The derivation `AlgebraicGeometry.Space.kernelSplitDerivation` of a section is the
derivation of `f_*f⁻¹𝒪_Y` evaluated at the image of the section under the unit `η`. -/
theorem kernelSplitDerivation_d (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (a : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj U)) :
    (kernelSplitDerivation B S hS f hf g hg).d a =
      (kernelSplitIdealDerivation B S hS f hf g hg).d
        (((directImageInverseImageStructureUnitOfHom B S hS f).hom.app U) a) :=
  derivationTransport_d _ _ U a

include hf hg in
/-- The derivation `AlgebraicGeometry.Space.kernelSplitIdealDerivation` restricted to
`f_*f⁻¹𝓘_f` is the coefficient map `AlgebraicGeometry.Space.kernelConormalDirectImageNu`. -/
theorem kernelSplitIdealDerivation_d_iota (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : ToType ((directImageInverseImageKernelIdeal B S hS f).val.obj U)) :
    (kernelSplitIdealDerivation B S hS f hf g hg).d
        (directImageInverseImageKernelIdealIota B S hS f U y) =
      kernelConormalDirectImageNu B S hS f U y :=
  PresheafOfModules.splitIdealDerivation_d_iota _ _ _ _ _ _ _ _ _ _ _ _
    (directImageInverseImageKernelIdealIota_eq_zero B S hS f) _ _ _ _ _ _ _ _ U y

include hf hg in
/-- The derivation `AlgebraicGeometry.Space.kernelSplitDerivation` of a section of `𝓘_f` is the
coefficient map at the image of the section in `f_*f⁻¹𝓘_f` under the unit. -/
theorem kernelSplitDerivation_d_kernelIdeal (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : (kernelIdealSheaf B S hS f).toSheafOfModules.val.obj U) :
    (kernelSplitDerivation B S hS f hf g hg).d x.1 =
      kernelConormalDirectImageNu B S hS f U
        (directImageInverseImageKernelIdealUnit B S hS f U x) :=
  Eq.trans (kernelSplitDerivation_d B S hS f hf g hg U x.1)
    (Eq.trans
      (congrArg (kernelSplitIdealDerivation B S hS f hf g hg).d
        (directImageInverseImageKernelIdealIota_unit B S hS f U x).symm)
      (kernelSplitIdealDerivation_d_iota B S hS f hf g hg U
        (directImageInverseImageKernelIdealUnit B S hS f U x)))

include hf hg in
/-- The derivation `AlgebraicGeometry.Space.kernelSplitDerivation` restricted to the kernel ideal
sheaf is the unit of the adjunction of Stacks 03LU. -/
theorem kernelSplitDerivation_d_unit (U : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : (kernelIdealSheaf B S hS f).toSheafOfModules.val.obj U) :
    (kernelSplitDerivation B S hS f hf g hg).d x.1 =
      ((modulePullbackAdjunction B S hS f).unit.app
        (kernelIdealSheaf B S hS f).toSheafOfModules).val.app U x :=
  Eq.trans (kernelSplitDerivation_d_kernelIdeal B S hS f hf g hg U x)
    (modulePullbackAdjunction_unit_kernelIdealSheaf_val_app B S hS f U x).symm

/-! ### The retraction, and monomorphy over the base `X` -/

include hf hg in
/-- The first arrow of Stacks 05ZA over the base `X`, in the kernel-ideal form
`AlgebraicGeometry.Space.kernelConormalFirstMap`, has a retraction: the morphism
`f^*Ω_{Y/X} ⟶ f^*𝓘_f` that Equation (0619) attaches to the derivation
`AlgebraicGeometry.Space.kernelSplitDerivation`. -/
theorem kernelConormalFirstMap_comp_derivationDirectImageEquiv_symm :
    kernelConormalFirstMap B S hS f g ≫
        (derivationDirectImageEquiv B S hS f g
            ((modulePullback B S hS f).obj
              (kernelIdealSheaf B S hS f).toSheafOfModules)).symm
          (kernelSplitDerivation B S hS f hf g hg) =
      𝟙 ((modulePullback B S hS f).obj (kernelIdealSheaf B S hS f).toSheafOfModules) :=
  submoduleTranspose_comp_derivationDirectImageEquiv_symm_eq_id B S hS f g
    (kernelIdealSheaf B S hS f)
    (kernelIdealUnitDifferential B S hS f g)
    (pullbackUnitDerivation B S hS f g)
    rfl
    (kernelIdealUnitDifferential_val_app_apply B S hS f g)
    (kernelSplitDerivation B S hS f hf g hg)
    (kernelSplitDerivation_d_unit B S hS f hf g hg)
    (kernelConormalFirstMap_eq B S hS f g) rfl

/-- The retraction of the first arrow of Stacks 05ZA over the base `X`: the morphism
`f^*Ω_{Y/X} ⟶ f^*𝓘_f` that Equation (0619) attaches to the derivation of Stacks 02HP. -/
noncomputable abbrev kernelSplitRetraction :
    (modulePullback B S hS f).obj (sheafOfDifferentials B S hS g) ⟶
      (modulePullback B S hS f).obj (kernelIdealSheaf B S hS f).toSheafOfModules :=
  (derivationDirectImageEquiv B S hS f g
      ((modulePullback B S hS f).obj (kernelIdealSheaf B S hS f).toSheafOfModules)).symm
    (kernelSplitDerivation B S hS f hf g hg)

include hf hg in
/-- The first arrow of Stacks 05ZA over the base `X` is a split monomorphism, for a closed
immersion with a left inverse. -/
theorem isSplitMono_kernelConormalFirstMap :
    IsSplitMono (kernelConormalFirstMap B S hS f g) :=
  IsSplitMono.mk' ⟨_,
    kernelConormalFirstMap_comp_derivationDirectImageEquiv_symm B S hS f hf g hg⟩

/-! ### The arbitrary base -/

section Base

variable {Bb : AlgebraicSpaces B S hS}

/-- The canonical map `Ω_{Y/Bb} ⟶ Ω_{Y/X}` of Stacks 05Z8, for the factorization of the
structure morphism of `Y` through the left inverse `g`. -/
noncomputable abbrev kernelSplitToRelativeDifferentials (b : Y ⟶ Bb) :
    sheafOfDifferentials B S hS (g ≫ f ≫ b) ⟶ sheafOfDifferentials B S hS g :=
  toRelativeDifferentials B S hS g (f ≫ b)

/-- The map of Stacks 05Z8 carries the universal derivation `d_{Y/Bb}` to the relative
universal derivation `d_{Y/X}`. -/
theorem postcomp_kernelSplitToRelativeDifferentials (b : Y ⟶ Bb) :
    (universalDerivation B S hS (g ≫ f ≫ b)).postcomp
        (kernelSplitToRelativeDifferentials B S hS f g b).val =
      relativeUniversalDerivation B S hS g (f ≫ b) :=
  Eq.trans
    (differentialsHomEquiv_apply B S hS (g ≫ f ≫ b)
      (sheafOfDifferentials B S hS g)
      (kernelSplitToRelativeDifferentials B S hS f g b)).symm
    ((differentialsHomEquiv B S hS (g ≫ f ≫ b)
      (sheafOfDifferentials B S hS g)).apply_symm_apply
        (relativeUniversalDerivation B S hS g (f ≫ b)))

/-- The first arrow of the conormal sequence over an ambient base, followed by the inverse image
along `f` of the map of Stacks 05Z8, is the first arrow over `X`. -/
theorem kernelConormalFirstMap_comp_map_kernelSplitToRelativeDifferentials (b : Y ⟶ Bb) :
    kernelConormalFirstMap B S hS f (g ≫ f ≫ b) ≫
        (modulePullback B S hS f).map
          (kernelSplitToRelativeDifferentials B S hS f g b) =
      kernelConormalFirstMap B S hS f g :=
  submoduleTranspose_comp_map_eq_submoduleTranspose B S hS f (g ≫ f ≫ b) g
    (kernelIdealSheaf B S hS f)
    (kernelSplitToRelativeDifferentials B S hS f g b)
    (relativeUniversalDerivation B S hS g (f ≫ b))
    (postcomp_kernelSplitToRelativeDifferentials B S hS f g b)
    (fun _ _ ↦ rfl)
    (kernelIdealUnitDifferential B S hS f (g ≫ f ≫ b))
    (pullbackUnitDerivation B S hS f (g ≫ f ≫ b))
    rfl
    (kernelIdealUnitDifferential_val_app_apply B S hS f (g ≫ f ≫ b))
    (kernelIdealUnitDifferential B S hS f g)
    (pullbackUnitDerivation B S hS f g)
    rfl
    (kernelIdealUnitDifferential_val_app_apply B S hS f g)
    (kernelConormalFirstMap_eq B S hS f (g ≫ f ≫ b))
    (kernelConormalFirstMap_eq B S hS f g)

include hf hg in
/-- Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over `Bb` with structure morphism
`b : Y ⟶ Bb`, whose left inverse `g : Y ⟶ X` is a morphism over `Bb`.  Then the first arrow
`𝓘_f ⟶ f^*Ω_{Y/Bb}` of the conormal sequence of Stacks 05ZA is a monomorphism. -/
theorem mono_kernelConormalFirstMap (b : Y ⟶ Bb) (hgb : g ≫ f ≫ b = b) :
    Mono (kernelConormalFirstMap B S hS f b) :=
  have : Mono (kernelConormalFirstMap B S hS f g) :=
    IsSplitMono.mono (kernelConormalFirstMap B S hS f g)
      (hf := isSplitMono_kernelConormalFirstMap B S hS f hf g hg)
  have : Mono (kernelConormalFirstMap B S hS f (g ≫ f ≫ b)) :=
    mono_of_mono_fac
      (kernelConormalFirstMap_comp_map_kernelSplitToRelativeDifferentials B S hS f g b)
  hgb ▸ this

include hf hg in
/-- Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over `Bb` with structure morphism
`b : Y ⟶ Bb`, and let `g : Y ⟶ X` be a left inverse of `f` over `Bb`.  Then the conormal
sequence of Stacks 05ZA read off the kernel ideal sheaf
```
  0 ⟶ f^*𝓘_f ⟶ f^*Ω_{Y/Bb} ⟶ Ω_{X/Bb} ⟶ 0
```
is split exact: it admits a `CategoryTheory.ShortComplex.Splitting`. -/
theorem nonempty_conormalSequenceKernel_splitting (b : Y ⟶ Bb) (hgb : g ≫ f ≫ b = b) :
    Nonempty (ShortComplex.mk _ _
      (kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS f b)).Splitting :=
  (nonempty_conormalSequenceKernel_splitting_iff_mono_of_isClosedImmersion
      B S hS f hf b g hg hgb).2
    (mono_kernelConormalFirstMap B S hS f hf g hg b hgb)

end Base

/-! ### The étale-local clause -/

section EtaleLocal

variable {W W' Zs Zs' Bb : AlgebraicSpaces B S hS}

/-- Let `i : Zs ⟶ W` be a morphism of algebraic spaces over `Bb` with structure morphism
`b : W ⟶ Bb`, let `φ : W' ⟶ W` be étale, let `i' : Zs' ⟶ W'` be a closed immersion and
`a : Zs' ⟶ Zs` étale with `i' ≫ φ = a ≫ i`, and let `g' : W' ⟶ Zs'` be a left inverse of `i'`
over `Bb`.  Then

* the restricted conormal sequence, the sequence of Stacks 05ZA at `i'` over `φ ≫ b`, is split
  exact;
* the inverse image along `a` of the second arrow of the unrestricted sequence is a split
  epimorphism. -/
theorem nonempty_conormalSequenceKernel_splitting_of_etale (i : Zs ⟶ W) (b : W ⟶ Bb)
    (φ : W' ⟶ W) (hφ : IsEtale B S hS φ.hom) (i' : Zs' ⟶ W')
    (hi' : IsClosedImmersion B S hS i'.hom) (a : Zs' ⟶ Zs) (ha : IsEtale B S hS a.hom)
    (hsq : i' ≫ φ = a ≫ i) (g' : W' ⟶ Zs') (hg' : i' ≫ g' = 𝟙 Zs')
    (hg'b : g' ≫ i' ≫ φ ≫ b = φ ≫ b) :
    Nonempty (ShortComplex.mk _ _
          (kernelConormalFirstMap_comp_pullbackDifferentialsMap_eq_zero B S hS i'
            (φ ≫ b))).Splitting ∧
      IsSplitEpi ((modulePullback B S hS a).map (pullbackDifferentialsMap B S hS i b)) :=
  ⟨nonempty_conormalSequenceKernel_splitting B S hS i' hi' g' hg' (φ ≫ b) hg'b,
    isSplitEpi_map_pullbackDifferentialsMap_of_etale B S hS i b φ hφ i' a ha hsq g' hg' hg'b⟩

end EtaleLocal

end AlgebraicGeometry.Space

end
