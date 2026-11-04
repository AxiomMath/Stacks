module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMonomorphismModuleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotientExtension

/-!
# Extending a quotient of the Quot functor from the generic fibre

Let `D` be the standing data of the Quot functor of Stacks 09TR: a morphism `f : X ⟶ B` of
finite presentation and a quasi-coherent `𝒪_X`-module `F`.  Let `h : T' ⟶ T` be a morphism of
test schemes over `B`, and write `j : X_{T'} ⟶ X_T` for the induced morphism of base changes.
For the existence part of the valuative criterion for `Quot_{F/X/B} ⟶ B` (Stacks 0DM4), `T` is
the spectrum of a valuation ring and `T'` that of its fraction field, and a quotient
`F_{T'} ⟶ Q'` must be extended to a quotient of `F_T`.

The extension is canonical.  The projection `F_{T'} ⟶ Q'`, read on `j^*F_T ≅ F_{T'}`, has an
adjoint transpose `φ : F_T ⟶ j_*Q'`, and the extension is the image of `φ`, that is, the quotient
of `F_T` by the kernel of `φ`.  When `j^*` preserves monomorphisms — `j` is flat — and the counit
`j^*j_*Q' ⟶ Q'` is invertible — `j` is an affine monomorphism and `Q'` is quasi-coherent — this
quotient pulls back to `Q'` along `h`.  On an affine chart `Spec A` of `X_T`, with `F_T` given
by a finite `A`-module `M` and `Q'` by a quotient of `M_K`, the image of `φ` is the quotient of
`M` by `{x ∈ M | x ⊗ 1 ↦ 0 in Q'}`.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.extensionKernel`: the kernel of the adjoint transpose
  `F_T ⟶ j_*(F_{T'}/K')` of the projection onto a quotient over `T'`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.quotientPullback_extensionKernel`: the extended quotient
  pulls back to the given one along `h`.
* `AlgebraicGeometry.Space.QuotSituation.isQuasicoherentOnSite_quotientModule_extensionKernel`:
  the extended quotient is quasi-coherent.
* `AlgebraicGeometry.Space.QuotSituation.isFiniteTypeOnSite_quotientModule_extensionKernel`:
  the extended quotient is of finite type when `F` is.

## References

* [Stacks Project, Tag 0DM4](https://stacks.math.columbia.edu/tag/0DM4)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The cohomological abelian structure on modules at the ambient universe would be selected
-- ahead of `SheafOfModules.instAbelian` and leave the module universe of the subobjects
-- unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS) {T' T : SchemesOver D.Y} (h : T' ⟶ T)

/-- The base change `F_T` of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherentOnSite_baseChangeModule (T : SchemesOver D.Y) :
    (D.baseChangeModule T).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (D.sourceProjection T)
    D.F D.quasicoherent

/-- The base change `F_T` of a module of finite type is of finite type. -/
theorem isFiniteTypeOnSite_baseChangeModule (hF : SheafOfModules.IsFiniteTypeOnSite D.F)
    (T : SchemesOver D.Y) : SheafOfModules.IsFiniteTypeOnSite (D.baseChangeModule T) :=
  isFiniteTypeOnSite_modulePullback B S hS (D.sourceProjection T) D.F hF

/-- The identification `j^*F_T ≅ F_{T'}` of the inverse image of `F_T` along
`j : X_{T'} ⟶ X_T` with `F_{T'}`. -/
abbrev baseChangeModuleComparison :
    (modulePullback B S hS (D.relativeMap h)).obj (D.baseChangeModule T) ≅
      D.baseChangeModule T' :=
  ((D.baseChangeComparison h).app D.F).symm

/-- **The extension of a quotient over `T'` to a quotient over `T`**, recorded by its kernel:
the kernel of the adjoint transpose `F_T ⟶ j_*(F_{T'}/K')` of the projection
`j^*F_T ≅ F_{T'} ⟶ F_{T'}/K'`. -/
def extensionKernel (K : Subobject (D.baseChangeModule T')) : Subobject (D.baseChangeModule T) :=
  (modulePullbackAdjunction B S hS (D.relativeMap h)).extensionKernel
    (D.baseChangeModuleComparison h) K

/-- The adjoint transpose `F_T ⟶ j_*(F_{T'}/K')` whose image is the extended quotient. -/
abbrev extensionMap (K : Subobject (D.baseChangeModule T')) :
    D.baseChangeModule T ⟶
      (modulePushforward B S hS (D.relativeMap h)).obj (D.quotientModule T' K) :=
  (modulePullbackAdjunction B S hS (D.relativeMap h)).extensionMap
    (D.baseChangeModuleComparison h) K

/-- The extended quotient is the image of the adjoint transpose. -/
def extensionQuotientIso (K : Subobject (D.baseChangeModule T')) :
    D.quotientModule T (D.extensionKernel h K) ≅ image (D.extensionMap h K) :=
  (modulePullbackAdjunction B S hS (D.relativeMap h)).extensionQuotientIso
    (D.baseChangeModuleComparison h) K

/-- The embedding of the extended quotient into `j_*(F_{T'}/K')`. -/
abbrev extensionQuotientι (K : Subobject (D.baseChangeModule T')) :
    D.quotientModule T (D.extensionKernel h K) ⟶
      (modulePushforward B S hS (D.relativeMap h)).obj (D.quotientModule T' K) :=
  (modulePullbackAdjunction B S hS (D.relativeMap h)).extensionQuotientι
    (D.baseChangeModuleComparison h) K

/-- The embedding of the extended quotient into `j_*(F_{T'}/K')` is a monomorphism. -/
instance mono_extensionQuotientι (K : Subobject (D.baseChangeModule T')) :
    Mono (D.extensionQuotientι h K) :=
  Adjunction.mono_extensionQuotientι _ _ _

/-- **The extended quotient pulls back to the given one.**  If the inverse image along
`j : X_{T'} ⟶ X_T` preserves monomorphisms and the counit `j^*j_*Q' ⟶ Q'` is invertible at the
quotient `Q' = F_{T'}/K'`, then the pullback along `h` of the extension of `K'` is `K'`. -/
theorem quotientPullback_extensionKernel
    [(modulePullback B S hS (D.relativeMap h)).PreservesMonomorphisms]
    (K : Subobject (D.baseChangeModule T'))
    [IsIso ((modulePullbackAdjunction B S hS (D.relativeMap h)).counit.app
      (D.quotientModule T' K))] :
    D.quotientPullback h (D.extensionKernel h K) = K :=
  (modulePullbackAdjunction B S hS (D.relativeMap h)).kernelSubobject_extensionKernel
    (D.baseChangeModuleComparison h) K

/-- **The extended quotient is quasi-coherent** as soon as the direct image of the given
quotient is: it is the image of a morphism between quasi-coherent modules. -/
theorem isQuasicoherentOnSite_quotientModule_extensionKernel
    (K : Subobject (D.baseChangeModule T'))
    (hK : ((modulePushforward B S hS (D.relativeMap h)).obj
      (D.quotientModule T' K)).IsQuasicoherentOnSite) :
    (D.quotientModule T (D.extensionKernel h K)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (D.extensionQuotientIso h K).symm
    (isQuasicoherentOnSite_image_unconditional B S hS _ _ (D.extensionMap h K)
      (D.isQuasicoherentOnSite_baseChangeModule T) hK)

/-- **The extended quotient is of finite type** when `F` is: it is a quotient of `F_T`. -/
theorem isFiniteTypeOnSite_quotientModule_extensionKernel
    (hF : SheafOfModules.IsFiniteTypeOnSite D.F) (K : Subobject (D.baseChangeModule T')) :
    SheafOfModules.IsFiniteTypeOnSite (D.quotientModule T (D.extensionKernel h K)) :=
  isFiniteTypeOnSite_of_epi B S hS _ _ (D.quotientProjection T (D.extensionKernel h K))
    (D.isFiniteTypeOnSite_baseChangeModule hF T)

end QuotSituation

end AlgebraicGeometry.Space

end
