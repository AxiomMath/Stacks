module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.TensorFunctorAffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineQuasicoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidalComparison

/-!
# The two direct images along an affine 1-morphism agree

Two constructions of the direct image `g_*` of modules along an affine 1-morphism
`g : 𝒰 ⟶ 𝒳` of algebraic stacks are in the library.

* `AlgebraicGeometry.Stack.affinePushforward` (used by Stacks 0GRK,
  `AlgebraicGeometry.Stack.exists_ringHom_tensorFunctor_comp_quasicoherentPushforward`):
  restriction along the right adjoint `r` of the functor underlying `g`, right adjoint to the
  inverse image `AlgebraicGeometry.Stack.stackModulePullback`;
* `AlgebraicGeometry.Stack.fppfModulesPushforward` (used by `f_{QCoh,*}` of Stacks 077A,
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImage`): the right Kan extension
  construction, right adjoint to the inverse image `AlgebraicGeometry.Stack.fppfModulesPullback`.

Both inverse images are objectwise restriction along the functor underlying `g`, with the same
identification of scalars, so they are *equal*
(`AlgebraicGeometry.Stack.AlgebraicStacks.stackModulePullback_eq_fppfModulesPullback`), and the
two direct images are isomorphic by uniqueness of right adjoints. On quasi-coherent modules this
identifies `AlgebraicGeometry.Stack.affineQuasicoherentPushforward` with both
`AlgebraicGeometry.Stack.AlgebraicStacks.affineQuasicoherentDirectImage` and `g_{QCoh,*}`.

The base states Stacks 0GRK for functors which are tensor functors for the localized monoidal
structure (I) of `QCoh(𝒪_𝒳)` (see
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidalComparison`). With the
comparison of the two monoidal structures, it is transferred here to a functor which is braided
monoidal for the strict structure (II), and to `g_{QCoh,*}` of Stacks 077A.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.affinePushforwardIsoFppfModulesPushforward`: the two
  direct images of modules agree.
* `AlgebraicGeometry.Stack.AlgebraicStacks.affineQuasicoherentPushforwardIsoDirectImage` and
  `quasicoherentDirectImageIsoAffineQuasicoherentPushforward` (same namespace): the same on
  quasi-coherent modules.
* `AlgebraicGeometry.Stack.AlgebraicStacks.localizedBraided`: a functor braided monoidal for (II)
  is braided monoidal for (I), with the braiding Stacks 0GRK and 0GRL use.
* `AlgebraicGeometry.Stack.AlgebraicStacks.comparisonTensorAlgebra` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.comparisonTensorRingHom`: the `R`-algebra
  `C = F(g_{QCoh,*}𝒪_U)` and the ring map `A ⟶ C` of Stacks 0GRK for a functor `F` braided
  monoidal for (II).
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImageTensorFunctorIso`:
  `F ∘ g_{QCoh,*} ≅ Γ(U, -) ⊗_A C`.

## Main results

* `exists_ringHom_tensorFunctor_comp_quasicoherentDirectImage`
  (namespace `AlgebraicGeometry.Stack.AlgebraicStacks`): Stacks 0GRK for `g_{QCoh,*}` of
  Stacks 077A and a functor braided monoidal for (II).

## References

* [Stacks Project, Tag 0GRK](https://stacks.math.columbia.edu/tag/0GRK)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Modules

variable {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒰 ⟶ 𝒳)

/-- **The two inverse images of modules along a 1-morphism of algebraic stacks are equal**: both
are objectwise restriction along the functor underlying `g`, with scalars identified by an
`eqToHom`. -/
theorem stackModulePullback_eq_fppfModulesPullback :
    stackModulePullback.{u, w, u} g = fppfModulesPullback B S hS g :=
  rfl

variable (hg : IsAffineHom B S hS g)

/-- **The two direct images of modules along an affine 1-morphism agree**: both are right adjoint
to the same inverse image. -/
def affinePushforwardIsoFppfModulesPushforward :
    affinePushforward.{u, w, u} g hg ≅ fppfModulesPushforward B S hS g :=
  (affinePullbackPushforwardAdjunction.{u, w, u} g hg).rightAdjointUniq
    (fppfModulesPullbackPushforwardAdjunction B S hS g)

end Modules

section Quasicoherent

variable {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : IsAffineHom B S hS g)

/-- **The two direct images of quasi-coherent modules along an affine 1-morphism out of a scheme
agree**: `AlgebraicGeometry.Stack.affineQuasicoherentPushforward` (used by Stacks 0GRK) and
`AlgebraicGeometry.Stack.AlgebraicStacks.affineQuasicoherentDirectImage`. -/
def affineQuasicoherentPushforwardIsoDirectImage :
    affineQuasicoherentPushforward g hg ≅ affineQuasicoherentDirectImage B S hS g hg :=
  NatIso.ofComponents
    (fun M => (ObjectProperty.fullyFaithfulι _).preimageIso
      ((affinePushforwardIsoFppfModulesPushforward g hg).app M.obj))
    (fun φ => (ObjectProperty.fullyFaithfulι _).map_injective
      ((affinePushforwardIsoFppfModulesPushforward g hg).hom.naturality φ.hom))

/-- `g_{QCoh,*}` of Stacks 077A is `AlgebraicGeometry.Stack.affineQuasicoherentPushforward` for an
affine `g` out of a scheme. -/
def quasicoherentDirectImageIsoAffineQuasicoherentPushforward :
    quasicoherentDirectImage B S hS g ≅ affineQuasicoherentPushforward g hg :=
  affineQuasicoherentDirectImageIso B S hS g hg ≪≫
    (affineQuasicoherentPushforwardIsoDirectImage g hg).symm

end Quasicoherent

section TensorFunctor

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory

variable {U : BigFppfOver B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : IsAffineHom B S hS g)
  {R : Type u} [CommRing R] (F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R)

/-- `F` is braided monoidal for the strict structure (II) of `QCoh(𝒪_𝒳)`. -/
local notation "BraidedII" F => @Functor.Braided _ _ (quasicoherentModulesMonoidal _ _ _ _)
  (quasicoherentModulesBraided _ _ _ _) _ _ _ _ F

/-- `F` composed with the inverse of the comparison of the two monoidal structures is additive. -/
theorem additive_comparisonInverse_comp [F.Additive] :
    ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F).Additive :=
  (additive_comparisonInverse_comp_iff B S hS 𝒳 F).2 inferInstance

/-- A functor braided monoidal for the strict structure (II) of `QCoh(𝒪_𝒳)` is braided monoidal for
the localized structure (I), after composing with the inverse of the comparison (the identity).
The braiding of (I) is the one of
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentSymmetricCategory`, which Stacks 0GRK and
0GRL use. -/
@[instance_reducible]
def localizedBraided (hF : BraidedII F) :
    ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F).Braided :=
  { comparisonInverseCompMonoidal B S hS 𝒳 F hF.toMonoidal with
    braided := (comparisonInverseCompBraided B S hS 𝒳 F hF).braided }

/-- The lax braided structure underlying
`AlgebraicGeometry.Stack.AlgebraicStacks.localizedBraided`. -/
@[instance_reducible]
def localizedLaxBraided (hF : BraidedII F) :
    ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F).LaxBraided :=
  (localizedBraided F hF).toLaxBraided

/-- **`C = F(g_{QCoh,*}𝒪_U)`** of Stacks 0GRK for a functor `F` braided monoidal for (II):
`AlgebraicGeometry.Stack.affineTensorAlgebra` of `F` seen as a functor out of (I), with its
`CommRing` and `R`-algebra structures. -/
def comparisonTensorAlgebra (hF : BraidedII F) [F.Additive] : Type u :=
  letI := localizedLaxBraided F hF
  letI := additive_comparisonInverse_comp F
  affineTensorAlgebra g hg ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F)

/-- `C` is a commutative ring. -/
instance (hF : BraidedII F) [F.Additive] : CommRing (comparisonTensorAlgebra g hg F hF) :=
  letI := localizedLaxBraided F hF
  letI := additive_comparisonInverse_comp F
  instCommRingAffineTensorAlgebra g hg ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F)

/-- `C` is an `R`-algebra. -/
instance (hF : BraidedII F) [F.Additive] : Algebra R (comparisonTensorAlgebra g hg F hF) :=
  letI := localizedLaxBraided F hF
  letI := additive_comparisonInverse_comp F
  instAlgebraAffineTensorAlgebra g hg ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F)

/-- **The ring map `A ⟶ C`** of Stacks 0GRK: `AlgebraicGeometry.Stack.affineTensorRingHom` of `F`
seen as a functor out of (I). -/
def comparisonTensorRingHom (hF : BraidedII F) [F.Additive] :
    schemeGlobalRing U →+* comparisonTensorAlgebra g hg F hF :=
  letI := localizedLaxBraided F hF
  letI := additive_comparisonInverse_comp F
  affineTensorRingHom g hg ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F)

variable (hF : BraidedII F) [F.Additive] [PreservesFiniteColimits F]
  [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]

/-- **Stacks 0GRK for `AlgebraicGeometry.Stack.AlgebraicStacks.affineQuasicoherentDirectImage`**:
`F ∘ g_*` is `N ↦ Γ(U, N) ⊗_A C` seen as an `R`-module, for `F` braided monoidal for (II). -/
def affineQuasicoherentDirectImageTensorFunctorIso (hU : IsAffineOver B S hS U) :
    affineQuasicoherentDirectImage B S hS g hg ⋙ F ≅
      quasicoherentGlobalSections.{u, w} U ⋙
        ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF) ⋙
          ModuleCat.restrictScalars (algebraMap R (comparisonTensorAlgebra g hg F hF)) :=
  letI := localizedLaxBraided F hF
  letI := additive_comparisonInverse_comp F
  letI : PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) :=
    inferInstanceAs (PreservesFiniteColimits F)
  letI : ∀ J : Type u, PreservesColimitsOfShape (Discrete J)
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) :=
    fun J => inferInstanceAs (PreservesColimitsOfShape (Discrete J) F)
  Functor.isoWhiskerRight (affineQuasicoherentPushforwardIsoDirectImage g hg).symm F ≪≫
    affineTensorFunctorGlobalSectionsIso g hg
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ F) hU

/-- **Stacks 0GRK for `g_{QCoh,*}` of Stacks 077A**: `F ∘ g_{QCoh,*}` is `N ↦ Γ(U, N) ⊗_A C` seen
as an `R`-module, for `F` braided monoidal for (II). -/
def quasicoherentDirectImageTensorFunctorIso (hU : IsAffineOver B S hS U) :
    quasicoherentDirectImage B S hS g ⋙ F ≅
      quasicoherentGlobalSections.{u, w} U ⋙
        ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF) ⋙
          ModuleCat.restrictScalars (algebraMap R (comparisonTensorAlgebra g hg F hF)) :=
  Functor.isoWhiskerRight (affineQuasicoherentDirectImageIso B S hS g hg) F ≪≫
    affineQuasicoherentDirectImageTensorFunctorIso g hg F hF hU

omit hg in
/-- **Stacks 0GRK for `g_{QCoh,*}` of Stacks 077A and a functor braided monoidal for the strict
structure (II).** Let `𝒳` be an algebraic stack with affine (absolute) diagonal, `R` a ring and
`F : QCoh(𝒪_𝒳) ⥤ Mod_R` an additive, right exact functor commuting with direct sums which is
braided monoidal for (II). For `g : U ⟶ 𝒳` with `U` affine, `g` is affine and
`F ∘ g_{QCoh,*}` is `N ↦ Γ(U, N) ⊗_A C` seen as an `R`-module, with `C = F(g_{QCoh,*}𝒪_U)` and
the ring map `A ⟶ C` of `AlgebraicGeometry.Stack.AlgebraicStacks.comparisonTensorRingHom`.
This is the base's
`AlgebraicGeometry.Stack.exists_ringHom_tensorFunctor_comp_quasicoherentPushforward` read through
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImageIsoAffineQuasicoherentPushforward`
and the comparison of the two monoidal structures. -/
theorem exists_ringHom_tensorFunctor_comp_quasicoherentDirectImage
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    (hU : IsAffineOver B S hS U) :
    ∃ hg : IsAffineHom B S hS g,
      Nonempty (quasicoherentDirectImage B S hS g ⋙ F ≅
        quasicoherentGlobalSections.{u, w} U ⋙
          ModuleCat.extendScalars (comparisonTensorRingHom g hg F hF) ⋙
            ModuleCat.restrictScalars (algebraMap R (comparisonTensorAlgebra g hg F hF))) :=
  have hg : IsAffineHom B S hS g :=
    isAffineHom_of_isAffineHom_diagonal_viewOverIntegers B S hS (contains_terminalScheme B) hU hΔ g
  ⟨hg, ⟨quasicoherentDirectImageTensorFunctorIso g hg F hF hU⟩⟩

end TensorFunctor

end AlgebraicGeometry.Stack.AlgebraicStacks
