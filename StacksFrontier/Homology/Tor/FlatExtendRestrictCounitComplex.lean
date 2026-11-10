module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import StacksFrontier.Homology.Tor.FlatDerivedExtensionScalars
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion

/-!
# Flat derived extension of scalars, computed termwise, and power torsion cohomology

Let `f : R → S` be a flat homomorphism of commutative rings. Extension of scalars along `f` is
exact, so derived extension of scalars is computed termwise and commutes with cohomology. If
moreover `R/I → S/IS` is bijective, the action map `S ⊗_R J → J` of a complex `J` of `S`-modules
with `IS`-power torsion cohomology is a quasi-isomorphism.

## Main results

All declarations are in the namespace `CochainComplex.DerivedExtensionScalars`.

* `TotalDerivedExtensionScalars.isIso_comparison_app_of_flat`: for `f` flat, the comparison of
  any total derived extension of scalars with degreewise extension of scalars is invertible at
  every complex.
* `quasiIso_extendRestrictScalarsAdj_counit_of_isIPowerTorsion`: for `f` flat and
  `R/I ⟶ S/IS` bijective, the degreewise action map `S ⊗_R J ⟶ J` of a complex `J` of
  `S`-modules whose cohomology modules are `IS`-power torsion is a quasi-isomorphism.

## References

* [Stacks Project, Tag 0AEU](https://stacks.math.columbia.edu/tag/0AEU)
* [Stacks Project, Tag 05E9](https://stacks.math.columbia.edu/tag/05E9)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace CochainComplex.DerivedExtensionScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **Derived extension of scalars along a flat ring map is computed termwise**: the comparison
`P ⊗ᴸ_R S ⟶ P ⊗_R S` of a total derived extension of scalars with degreewise extension of scalars
is invertible at every complex `P`. -/
theorem TotalDerivedExtensionScalars.isIso_comparison_app_of_flat {f : R →+* S}
    {_ : HasDerivedCategory.{w} (ModuleCat.{u} R)} {_ : HasDerivedCategory.{w'} (ModuleCat.{u} S)}
    (D : TotalDerivedExtensionScalars.{u, u, u, w, w'} f) (hf : f.Flat)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) : IsIso (D.comparison.app P) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let : (ModuleCat.extendScalars.{u, u, u} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isLeftAdjoint
  have hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
      (extensionOfScalarsComplexGeneral.{u, u, u, w'} f) := by
    intro K L φ hφ
    have : QuasiIso φ := hφ
    change IsIso (DerivedCategory.Q.map
      ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ) |>.map φ))
    infer_instance
  have := Functor.isIso_of_isLeftDerivedFunctor_of_inverts D.functor D.comparison hF
  infer_instance

/-- Let `f : R ⟶ S` be flat and `R/I ⟶ S/IS` bijective. For a
complex `J` of `S`-modules whose cohomology modules are `IS`-power torsion, the degreewise action
map `S ⊗_R J ⟶ J` is a quasi-isomorphism. -/
theorem quasiIso_extendRestrictScalarsAdj_counit_of_isIPowerTorsion (f : R →+* S) (hf : f.Flat)
    (I : Ideal R) (hq : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (J : CochainComplex (ModuleCat.{u} S) ℤ)
    (hJ : ∀ n, IsIPowerTorsion S (J.homology n) (I.map f)) :
    QuasiIso ((NatTrans.mapHomologicalComplex
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).counit (ComplexShape.up ℤ)).app J) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
  have hε : IsIso ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).counit.app
      (J.sc n).homology) := by
    algebraize [f]
    exact (ConcreteCategory.isIso_iff_bijective _).2
      (IPowerTorsion.extendRestrictScalarsAdj_counit_app_bijective.{u, u, u} I hf hq _ (hJ n))
  have h := NatTrans.app_homology (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).counit (J.sc n)
  change IsIso (ShortComplex.homologyMap ((J.sc n).mapNatTrans
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).counit))
  have : IsIso (((J.sc n).mapHomologyIso _).inv ≫ ShortComplex.homologyMap ((J.sc n).mapNatTrans
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).counit) ≫
        ((J.sc n).mapHomologyIso _).hom) := by
    rwa [← h]
  simpa using this

end CochainComplex.DerivedExtensionScalars

end
