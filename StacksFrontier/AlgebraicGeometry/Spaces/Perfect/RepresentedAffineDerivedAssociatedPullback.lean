module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePerfectSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummandsGeneral
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Derived pullback of the derived associated module between affine represented spaces

Let `g : U' ⟶ U` be a morphism of the big fppf site over `S` between objects whose underlying
schemes are affine, with rings of global functions `R = Γ(U)` and `R' = Γ(U')` and
`φ : R → R'` the induced ring map, and let `Φ_U : D(R) ⥤ D(𝒪_{h_U})` be the derived
associated-module functor (`AlgebraicGeometry.Space.representedAffineDerivedAssociated`). Then,
for a perfect `M ∈ D(R)`,

`Lg^*Φ_U(M) ≅ Φ_{U'}(M ⊗^L_R R')`.

In particular, at the spectrum `U'` of a field this is the statement "the derived fibre of the
associated complex is the derived fibre of the complex" of the proof of Stacks 0DKY: derived
pullback to `Spec κ` agrees with `M ⊗^L_R κ`.

A bounded complex `N` of finite projective `R`-modules representing `M` is carried by the
associated-module functor to a bounded complex of direct summands of finite free modules, which
are flat, so `Lg^*` is computed by termwise pullback
(`AlgebraicGeometry.Space.nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback`);
termwise, `g^*(N^i)^~ ≅ (R' ⊗_R N^i)^~`
(`AlgebraicGeometry.Space.representedAffineAssociatedModulePullbackIso`); and `R' ⊗_R N`
computes `M ⊗^L_R R'` because `N` is a bounded complex of projectives.

## Main results

* `nonempty_smallEtaleDerivedModulePullback_Q_representedAffineAssociated_iso`:
  the complex-level statement, `Lg^*Q(Φ₀ N) ≅ Q(Φ₀'(R' ⊗_R N))`.
* `nonempty_smallEtaleDerivedModulePullback_representedAffineDerivedAssociated_iso`:
  `Lg^*Φ_U(M) ≅ Φ_{U'}(M ⊗^L_R R')` for `M` perfect.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]

/-- **Derived pullback of an associated complex between affine represented spaces, at the
complex level.** For `g : U' ⟶ U` with affine underlying schemes and a bounded above complex
`N` of finite projective `Γ(U)`-modules, `Lg^*Q(Φ₀ N) ≅ Q(Φ₀'(Γ(U') ⊗_{Γ(U)} N))`. -/
theorem nonempty_smallEtaleDerivedModulePullback_Q_representedAffineAssociated_iso
    (g : U' ⟶ U) (N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ)
    (b : ℤ) [N.IsStrictlyLE b]
    (hfin : ∀ i, Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (N.X i))
    (hproj : ∀ i, Module.Projective Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) (N.X i)) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS (schemeSpaceMap g)).obj
        (DerivedCategory.Q.obj (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)) ≅
      DerivedCategory.Q.obj (((representedAffineAssociated B S hS U').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, u}
          (Scheme.Hom.appTop (B.inclusion.map g.left)).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N))) := by
  let Φ₀ := representedAffineAssociated B S hS U
  let K := (Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj N
  have hK : CochainComplex.IsStrictlyLE K b := (CochainComplex.isStrictlyLE_iff K b).2 fun i hi =>
    Φ₀.map_isZero (N.isZero_of_isStrictlyLE b i hi)
  have hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)
      (K.X i) := fun i => by
    have := hfin i
    have := hproj i
    exact Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree_general
      (Y := smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) _
      (isDirectSummandOfFiniteFree_representedAffineAssociated_obj B S hS U (N.X i))
  obtain ⟨e⟩ := @nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback _ _ _ _ _
    (representedSpaceMap B S hS g) K b hK hflat
  let c := representedAffineAssociatedModulePullbackIso B S hS g
  exact ⟨e ≪≫ DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
    (fun i => c.app (N.X i)) (fun i j _ => (c.hom.naturality (N.d i j)).symm))⟩

/-- **Derived pullback of the derived associated module between affine represented spaces.** For
`g : U' ⟶ U` with affine underlying schemes, `φ : Γ(U) → Γ(U')` the induced ring map, any total
derived extension of scalars `D` along `φ` and a perfect `M ∈ D(Γ(U))`,
`Lg^*Φ_U(M) ≅ Φ_{U'}(M ⊗^L_{Γ(U)} Γ(U'))`. At the spectrum of a field this is the derived fibre
of `Φ_U(M)`. -/
theorem nonempty_smallEtaleDerivedModulePullback_representedAffineDerivedAssociated_iso
    (g : U' ⟶ U)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{u, u, u}
      (Scheme.Hom.appTop (B.inclusion.map g.left)).hom)
    (M : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (hM : StacksDraft.Perfect.IsPerfect M) :
    Nonempty ((smallEtaleDerivedModulePullback B S hS (schemeSpaceMap g)).obj
        ((representedAffineDerivedAssociated B S hS U).obj M) ≅
      (representedAffineDerivedAssociated B S hS U').obj (D.functor.obj M)) := by
  obtain ⟨N, a, b, -, hLE, hfin, hproj, ⟨eM⟩⟩ := hM
  have : ∀ i, Projective (N.X i) := fun i => by
    have := hproj i
    infer_instance
  have := D.comparison_isIso_of_projective N b
  obtain ⟨e⟩ := nonempty_smallEtaleDerivedModulePullback_Q_representedAffineAssociated_iso g N b
    hfin hproj
  exact ⟨(smallEtaleDerivedModulePullback B S hS (schemeSpaceMap g)).mapIso
      ((representedAffineDerivedAssociated B S hS U).mapIso eM ≪≫
        ((representedAffineAssociated B S hS U).mapDerivedCategoryFactors.app N)) ≪≫ e ≪≫
    ((representedAffineAssociated B S hS U').mapDerivedCategoryFactors.app _).symm ≪≫
    (representedAffineDerivedAssociated B S hS U').mapIso
      ((asIso (D.comparison.app N)).symm ≪≫ D.functor.mapIso eM.symm)⟩

end AlgebraicGeometry.Space

end
