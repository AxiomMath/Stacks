module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfectReduction

/-!
# Vanishing of `RΓ_c(X_k̄, F)` above `b` for a flat sheaf, from its reduction modulo `p`

Let `F` be a flat sheaf of `ℤ/pᵐℤ`-modules on `X_étale`. `RΓ_c(X_k̄, F)` is computed by a bounded
below complex `J` of flat `ℤ/pᵐℤ`-modules whose `p`-torsion `J[p]` computes the cohomology of the
reduction of `(j_! F)|_{X̄_k̄}` modulo `p`. If the latter vanishes above `b`, the short exact
sequences `0 → J[pᶜ] → J[pᶜ⁺¹] → J[p] → 0` propagate the vanishing to `J[pᵐ] = J`: the
cohomology `Hⁱ_c(X_k̄, F)` vanishes for `i > b`.

This is how the vanishing of the cohomology of torsion sheaves above twice the dimension
(Tag 095U, applied to the constructible sheaf `j_! F / p` on the proper scheme `X̄_k̄`) gives the
vanishing of `Hⁱ_c(X_k̄, F)` for `i > 2 dim X` in
[Tag 03V2](https://stacks.math.columbia.edu/tag/03V2).

## Main results

* `Stacks.EtaleCohomology.isZero_homology_fieldBaseChangeCohomology_of_reduction`.
* `Stacks.EtaleCohomology.isZero_homology_compactSupportFrobeniusCohomology_single_of_reduction`.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius Stacks.ZModPrimePower

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section FieldBaseChange

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]

/-- **Vanishing of `Hⁱ(Y_k̄, F)` above `b` for a flat sheaf `F` of `ℤ/pᵐℤ`-modules** whose
`p`-torsion `F[p] ≅ F / pF` has cohomology vanishing above `b` on `Y_k̄`. -/
theorem isZero_homology_fieldBaseChangeCohomology_of_reduction
    {F₀ : EtaleModules.{u, 0} (ZMod (p ^ m)) Y.left} (hF : PowExact p m F₀) (b : ℤ)
    (hb : ∀ i, b < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
      (derivedDirectImageSections (pullback.snd Y.hom (specAlgebraMap k kbar)) (ZMod p)
        ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj Y kbar)).obj F₀)))))
    (i : ℤ) (hi : b < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (p ^ m))) i).obj
      (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} _
        (Spec (.of kbar))).obj ((etaleModuleDerivedDirectImage.{u, 0} _
          (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} _ Y kbar ⟨(CochainComplex.singleFunctor _ 0).obj F₀,
            CochainComplex.plus_singleFunctor_obj F₀⟩))))) := by
  obtain ⟨J, -, hJ, ⟨e⟩, hh⟩ := fieldBaseChangeCohomology_reduction Y kbar p m hF
  have h₁ : (torsionComplex p J 1).ExactAt i := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    obtain ⟨e'⟩ := hh i
    exact ((ModuleCat.restrictScalars (torsionCoeff p m)).map_isZero (hb i hi)).of_iso e'
  have hJi : IsZero (J.homology i) :=
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (exactAt_torsionComplex J hJ i h₁ le_rfl)).of_iso
      ((HomologicalComplex.homologyFunctor _ _ i).mapIso (torsionComplexTopIso J)).symm
  exact hJi.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app J)

end FieldBaseChange

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p : ℕ) [Fact p.Prime] (m : ℕ) [NeZero m]

omit [Fintype k] in
/-- **Vanishing of `Hⁱ_c(X_k̄, F)` above `b` for a flat sheaf `F` of `ℤ/pᵐℤ`-modules** whose
extension by zero to the compactification has, modulo `p`, cohomology on `X̄_k̄` vanishing above
`b`. -/
theorem isZero_homology_compactSupportFrobeniusCohomology_single_of_reduction
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) X) (hF : PowExact p m F) (b : ℤ)
    (hb : ∀ i, b < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod p)) i).obj
      (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
        (ZMod p) ((etaleModuleCoextendScalars (torsionCoeff p m) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F))))))
    (i : ℤ) (hi : b < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod (p ^ m))) i).obj
      (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} (ZMod (p ^ m)) f j kbar
          ⟨(CochainComplex.singleFunctor _ 0).obj F,
            CochainComplex.plus_singleFunctor_obj F⟩))) := by
  have hF' : PowExact p m ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj F) :=
    hF.map _ (etaleModules_pow_nsmul_id F)
  refine (isZero_homology_fieldBaseChangeCohomology_of_reduction (Over.mk j.toBase) kbar p m hF'
    b hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso ?_)
  refine DerivedCategory.Plus.ι.mapIso ((etaleModuleDerivedGlobalSections.{u, 0} _
    (Spec (.of kbar))).mapIso ((etaleModuleDerivedDirectImage.{u, 0} _
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapIso
      (DerivedCategory.Plus.Q.mapIso
        ((etaleModuleInverseImage.{u, 0} _
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.mapIso ?_))))
  exact ObjectProperty.isoMk _
    ((HomologicalComplex.singleMapHomologicalComplex
      (etaleModuleExtensionByZero.{u, 0} _ j.immersion) (ComplexShape.up ℤ) 0).app F)

end Stacks.EtaleCohomology
