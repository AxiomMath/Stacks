module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree

/-!
# Direct image of a pseudo-coherent complex twisted by an invertible module

Let `p : T ⟶ X` be a flat and proper morphism of finite presentation of algebraic spaces, let
`q : T ⟶ P` be a morphism and `ℒ` a flat invertible `𝒪_P`-module. For `E` pseudo-coherent on `T`,
`Rp_*(E ⊗^𝐋 Lq^*ℒ)` is pseudo-coherent on `X`, by the perfectness part of Stacks 0A1P: the
module `q^*ℒ` is invertible, hence of finite presentation, flat over `X` and of support proper
over `X`, and `Lq^*ℒ = q^*ℒ` as `ℒ` is flat. This is how the proof of Stacks 0CTT applies
Stacks 0CTN to `E ⊗^𝐋 Lq^*𝒪(d)`.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_derivedModulePushforward_tensor_single_of_isInvertible`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  isGrothendieckAbelian_ringedToposStructureRingSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T X P : AlgebraicSpaces B S hS}

/-- The pullback of an invertible module along a morphism of algebraic spaces is invertible
(Stacks 0B8P). -/
theorem isInvertibleModule_pullbackModules (q : T ⟶ P) (L : Modules.{u, u} B S hS P.1 P.2)
    (hL : IsInvertibleModule P L) :
    IsInvertibleModule T
      (((smallEtaleRingedToposHom B S hS q).toModulesHom.pullbackModules).obj L) :=
  have := hL
  Stacks.SheafOfModules.isInvertible_pullbackModules_obj
    (smallEtaleRingedToposHom B S hS q).toModulesHom _

/-- An invertible module on an algebraic space is of finite presentation. -/
theorem isFinitePresentation_of_isInvertibleModule (L : Modules.{u, u} B S hS T.1 T.2)
    (hL : IsInvertibleModule T L) : L.IsFinitePresentation :=
  Stacks.SheafOfModules.isFinitePresentation_of_isInvertible _ L hL

/-- **`Rp_*(E ⊗^𝐋 Lq^*ℒ)` is pseudo-coherent** for `p` flat, proper and of finite presentation, `E`
pseudo-coherent and `ℒ` a flat invertible module, by the perfectness part of Stacks 0A1P. -/
theorem isPseudoCoherent_derivedModulePushforward_tensor_single_of_isInvertible
    (p : T ⟶ X) (hpfl : IsFlat B S hS p.hom) (hppr : IsProper B S hS p.hom)
    (hpfp : IsFinitePresentation B S hS p.hom) (q : T ⟶ P)
    (L : Modules.{u, u} B S hS P.1 P.2) (hL : IsInvertibleModule P L)
    (hLf : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS P).O) L)
    (E : DerivedCategory (Modules.{u, u} B S hS T.1 T.2))
    (hE : (smallEtaleRingedSite B S hS T.1 T.2).IsPseudoCoherent E) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
      ((derivedModulePushforward B S hS p).obj
        (((smallEtaleDerivedTensor B S hS T).obj E).obj
          ((smallEtaleDerivedModulePullback B S hS q).obj
            ((DerivedCategory.singleFunctor _ 0).obj L)))) := by
  let L' := ((smallEtaleRingedToposHom B S hS q).toModulesHom.pullbackModules).obj L
  have hL' : IsInvertibleModule T L' := isInvertibleModule_pullbackModules q L hL
  let G := (HomologicalComplex.single (Modules.{u, u} B S hS T.1 T.2)
    (ComplexShape.up ℤ) 0).obj L'
  have hG : ∀ n, n ≠ 0 → IsZero (G.X n) := fun n hn =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
  have hGfp : ∀ n, (G.X n).IsFinitePresentation := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · exact (SheafOfModules.isFinitePresentation _).prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L').symm
        (isFinitePresentation_of_isInvertibleModule L' hL')
    · exact isFinitePresentation_of_isZero B S hS (hG n hn)
  have h := isPseudoCoherent_derivedModulePushforward_derivedTensor_of_perfectness
    (fun f' hf' E' hE' G' h₁ h₂ h₃ h₄ =>
      (isPerfect_derivedModulePushforward_derivedTensor_and_isIso_baseChange f' hf' E' hE' G'
        h₁ h₂ h₃ h₄).1) p hpfp
    E hE G ⟨0, fun i hi => hG i (by omega)⟩ hGfp
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · exact IsFlatOver.of_iso B S hS _
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 L').symm
          (isFlatOver_of_isInvertibleModule p L' hpfl hL')
      · exact isFlatOver_of_isZero B S hS p (hG n hn))
    (fun n => have := hGfp n
      hasProperSupport_of_isFinitePresentation B S hS p hppr
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hpfp.1) (G.X n))
  exact (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m =>
    RingedSite.isPseudoCoherentFrom_of_iso _ m
      ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 h m)
      ((derivedModulePushforward B S hS p).mapIso
        (((smallEtaleDerivedTensor B S hS T).obj E).mapIso
          (smallEtaleDerivedModulePullbackSingleIsoOfFlat q L 0 hLf ≪≫
            (DerivedCategory.singleFunctorIsoCompQ _ 0).app L')))

end AlgebraicGeometry.Space

end
