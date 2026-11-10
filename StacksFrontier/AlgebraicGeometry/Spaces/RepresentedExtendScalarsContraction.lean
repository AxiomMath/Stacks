module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentPullbackIsoComp
public import StacksFrontier.CategoryTheory.Functor.Derived.ComparisonSquareChase
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCongr

/-!
# The contraction of the extensions of scalars along a composite of represented morphisms

Let `U'' --h--> U' --g--> U` be morphisms of the big fppf site over `S`, with `R`, `R'`, `R''` the
rings of global functions of their underlying schemes.  Extension of scalars along the induced ring
maps contracts: `R'' ⊗_{R'} (R' ⊗_R −) ≅ R'' ⊗_R −`, on modules, on complexes, and derived.  The
contraction on modules is `AlgebraicGeometry.Space.representedAffineExtendScalarsCompIso`; this
file builds the other two and proves that the derived one is compatible with the comparison to the
degreewise one — the composition law of [Stacks, Tag 06Y5] in the shape a chase of base change
squares consumes.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineExtendScalarsComplexCompIso` and
  `AlgebraicGeometry.Space.representedAffineDerivedExtensionCompIso`: the contraction on
  complexes, and derived.

## Main results

* `AlgebraicGeometry.Space.representedAffineDerivedExtensionCompIso_comparison`: the contraction
  of the derived extensions of scalars is compatible with the comparison to the degreewise one.

## Implementation notes

`Γ(U, 𝒪)` of a composite is the composite of the `Γ(U, 𝒪)`'s, but not syntactically so, which is
why every contraction here carries a renaming of extension of scalars along
`AlgebraicGeometry.Space.representedAffineCommRingCatHom_comp_hom`.  The transport of the
comparison across that renaming is
`CochainComplex.DerivedExtensionScalars.extendScalarsComparison_congr`.

## References

* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.DerivedExtensionScalars

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Extension of scalars is additive, being a left adjoint.  Re-attached as a local instance by
every file downstream of this one. -/
local instance additive_extendScalars_ofRingHom {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]
    (ψ : R₁ →+* R₂) : (ModuleCat.extendScalars.{u, u, u} ψ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj ψ).left_adjoint_additive

/-- Inverse image of modules along a represented morphism is additive, at the spelling used
downstream. -/
local instance additive_pullbackModules_ofRepresentedSpaceMap {V V' : BigFppfOver B S hS}
    (k : V' ⟶ V) :
    ((smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS k)).toModulesHom.pullbackModules).Additive :=
  pullbackModules_smallEtale_additive _

/-- The associated-module functor of an affine representable is additive, at the spelling used
downstream. -/
local instance additive_associated_ofAffineRepresentable (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    (representedAffineAssociated B S hS V).Additive :=
  additive_representedAffineAssociated B S hS V

variable {U'' U' U : BigFppfOver B S hS} (h : U'' ⟶ U') (g : U' ⟶ U)

/-! ### The two contractions -/

/-- **The contraction `R'' ⊗_{R'} (R' ⊗_R −) ≅ R'' ⊗_R −` on complexes**: the degreewise image of
`AlgebraicGeometry.Space.representedAffineExtendScalarsCompIso`. -/
def representedAffineExtendScalarsComplexCompIso :
    (ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS h).hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS (h ≫ g)).hom).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
    (representedAffineExtendScalarsCompIso B S hS h g) (ComplexShape.up ℤ)

/-- **The contraction `(- ⊗^L_R R') ⋙ (- ⊗^L_{R'} R'') ≅ - ⊗^L_R R''`** of the derived extensions
of scalars along the maps of rings of global functions: the composition isomorphism of
[Stacks, Tag 06Y5], read through
`AlgebraicGeometry.Space.representedAffineCommRingCatHom_comp_hom`. -/
def representedAffineDerivedExtensionCompIso :
    (representedAffineDerivedExtension B S hS g).functor ⋙
        (representedAffineDerivedExtension B S hS h).functor ≅
      (representedAffineDerivedExtension B S hS (h ≫ g)).functor :=
  totalDerivedExtensionScalarsComp.{u, u} (representedAffineCommRingCatHom B S hS g).hom
      (representedAffineCommRingCatHom B S hS h).hom ≪≫
    eqToIso (congrArg (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
      (representedAffineCommRingCatHom_comp_hom B S hS h g).symm)

/-! ### The comparison law -/

/-- The degreewise contraction, split into the scalar-tower isomorphism and the renaming along
`AlgebraicGeometry.Space.representedAffineCommRingCatHom_comp_hom`, after localization. -/
theorem representedAffineExtendScalarsComplexCompIso_hom_app
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    DerivedCategory.Q.map ((representedAffineExtendScalarsComplexCompIso B S hS h g).hom.app M) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u}
            (representedAffineCommRingCatHom B S hS g).hom
            (representedAffineCommRingCatHom B S hS h).hom).inv
          (ComplexShape.up ℤ)).app M) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (eqToHom (congrArg ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom_comp_hom B S hS h g).symm))
          (ComplexShape.up ℤ)).app M) := by
  rw [← CategoryTheory.Functor.map_comp]
  refine congrArg DerivedCategory.Q.map ?_
  change (NatTrans.mapHomologicalComplex
    (representedAffineExtendScalarsCompIso B S hS h g).hom
    (ComplexShape.up ℤ)).app M = _
  rw [representedAffineExtendScalarsCompIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

/-- **The contraction of the derived extensions of scalars is compatible with the comparison to
the degreewise one.**  This is
`CochainComplex.DerivedExtensionScalars.extendScalarsComparison_comp` followed by the transport
`CochainComplex.DerivedExtensionScalars.extendScalarsComparison_congr` along
`AlgebraicGeometry.Space.representedAffineCommRingCatHom_comp_hom`. -/
theorem representedAffineDerivedExtensionCompIso_comparison
    (M : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineDerivedExtension B S hS h).functor.map
          ((extendScalarsComparison (representedAffineCommRingCatHom B S hS g).hom).app M) ≫
        (extendScalarsComparison (representedAffineCommRingCatHom B S hS h).hom).app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Q.map
          ((representedAffineExtendScalarsComplexCompIso B S hS h g).hom.app M) =
      (representedAffineDerivedExtensionCompIso B S hS h g).hom.app (DerivedCategory.Q.obj M) ≫
        (extendScalarsComparison (representedAffineCommRingCatHom B S hS (h ≫ g)).hom).app M :=
  (congrArg (fun y => (representedAffineDerivedExtension B S hS h).functor.map
        ((extendScalarsComparison (representedAffineCommRingCatHom B S hS g).hom).app M) ≫
      (extendScalarsComparison (representedAffineCommRingCatHom B S hS h).hom).app
        (((ModuleCat.extendScalars.{u, u, u}
          (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫ y)
      (representedAffineExtendScalarsComplexCompIso_hom_app B S hS h g M)).trans
    (StacksDraft.ComparisonSquare.comp_split_right _ _ _ _ _ _ _ _
      (extendScalarsComparison_comp (representedAffineCommRingCatHom B S hS g).hom
        (representedAffineCommRingCatHom B S hS h).hom M)
      (extendScalarsComparison_congr
        (representedAffineCommRingCatHom_comp_hom B S hS h g).symm M))

end AlgebraicGeometry.Space

end
