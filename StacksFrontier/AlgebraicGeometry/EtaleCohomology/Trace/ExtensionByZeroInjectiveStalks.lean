module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RegularDescentSheaf
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenClosedPointReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientChangeTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.Algebra.Module.Injective.GroupAlgebraSelfInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DescentSheafCtf
public import StacksFrontier.Algebra.Module.Injective.ZModSelfInjective
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SectionwiseFunctorEtaleQuasiIso

/-!
# Injective stalks of `j_! D(A[H])`

Let `R = (ℤ/n)[H]` for a finite group `H`. The descent sheaf `D(A[H])` of a Galois covering
(`AlgebraicGeometry.EtaleGaloisCovering.regularDescentSheaf`) is locally constant with value the
self-injective ring `R`, so its stalks at all points are injective `R`-modules. The stalk of an
extension by zero `j_! F` along an open immersion `j : U ⟶ X` at a geometric point `s` of `X` is
the stalk of `F` at the lift of `s` if `s` lies in `U`, and zero otherwise. Hence the restriction
of `j_! D(A[H])` to `X_k̄` has injective stalks.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.isLocallyConstantWith_descentSheaf`: the descent sheaf
  `D(N)` is locally constant with value `N`.
* `Stacks.EtaleCohomology.moduleInjective_sheafFiber_regularDescentSheaf`: the stalks of
  `D((ℤ/n)[H])` are injective `(ℤ/n)[H]`-modules.
* `Stacks.EtaleCohomology.moduleInjective_sheafFiber_extensionByZero`: the stalks of an extension
  by zero are injective as soon as those of the sheaf are.
* `Stacks.EtaleCohomology.moduleInjective_sheafFiber_extensionByZeroComplex`: the restriction to
  `Y_k̄` of `j_! D`, for `D` with injective stalks, has injective stalks.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 7.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u v w r

namespace Stacks.EtaleCohomology

/-- Injectivity of a module transports along isomorphisms in `ModuleCat`. -/
theorem moduleInjective_of_iso {R : Type r} [Ring R] {A B : ModuleCat.{v} R} (e : A ≅ B)
    (h : Module.Injective R A) : Module.Injective R B :=
  have : CategoryTheory.Injective A := Module.injective_object_of_injective_module R A
  Module.injective_module_of_injective_object (inj := Injective.of_iso e inferInstance) R B

/-- A zero module is injective. -/
theorem moduleInjective_of_isZero {R : Type r} [Ring R] {A : ModuleCat.{v} R} (h : IsZero A) :
    Module.Injective R A :=
  have : Subsingleton A := (ModuleCat.isZero_iff_subsingleton).1 h
  Module.Baer.injective fun _ _ ↦ ⟨0, fun _ _ ↦ Subsingleton.elim _ _⟩

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type w} [Group H] (G : EtaleGaloisCovering X H)
  (Λ : Type r) [Ring Λ] (N : Type (max (u + 1) v)) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

/-- **The descent sheaf `D(N)` is locally constant with value `N`**: it is constant on the
covering, which pulls back to a covering of every étale `X`-scheme. -/
theorem isLocallyConstantWith_descentSheaf (Q : ModuleCat.{max (u + 1) v} Λ → Prop)
    (hQ : Q (ModuleCat.of Λ N)) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q
      (G.descentSheaf Λ N ρ) := by
  intro W
  exact ⟨PUnit.{u + 2}, fun _ ↦ G.fiberObj W, fun _ ↦ G.fiberObjFst W,
    G.ofArrows_fiberObjFst_mem W, fun _ ↦ ⟨ModuleCat.of Λ N, hQ,
      ⟨Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap X.smallEtaleTopology
        (ModuleCat.{max (u + 1) v} Λ) (G.fiberObjSnd W) (G.descentSheaf Λ N ρ) _
        (G.trivialization Λ N ρ)⟩⟩⟩

/-- **The stalks of a descent sheaf with injective value are injective.** -/
theorem moduleInjective_sheafFiber_descentSheaf (hN : Module.Injective Λ N)
    (p : GrothendieckTopology.Point.{max (u + 1) v} X.smallEtaleTopology) :
    Module.Injective Λ ((p.sheafFiber (A := ModuleCat.{max (u + 1) v} Λ)).obj
      (G.descentSheaf Λ N ρ)) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := AlgebraicGeometry.exists_constantValue_iso_sheafFiber p Λ
    (fun E : ModuleCat.{max (u + 1) v} Λ ↦ Module.Injective Λ E) (G.descentSheaf Λ N ρ)
    (G.isLocallyConstantWith_descentSheaf Λ N ρ _ hN)
  exact Stacks.EtaleCohomology.moduleInjective_of_iso e hE

/-- **The stalks of the descent sheaf `D(N)` are `N`.** -/
theorem nonempty_sheafFiber_descentSheaf_iso
    (p : GrothendieckTopology.Point.{max (u + 1) v} X.smallEtaleTopology) :
    Nonempty ((p.sheafFiber (A := ModuleCat.{max (u + 1) v} Λ)).obj (G.descentSheaf Λ N ρ) ≅
      ModuleCat.of Λ N) := by
  obtain ⟨E, ⟨hE⟩, ⟨e⟩⟩ := AlgebraicGeometry.exists_constantValue_iso_sheafFiber p Λ
    (fun E : ModuleCat.{max (u + 1) v} Λ ↦ Nonempty (E ≅ ModuleCat.of Λ N))
    (G.descentSheaf Λ N ρ) (G.isLocallyConstantWith_descentSheaf Λ N ρ _ ⟨Iso.refl _⟩)
  exact ⟨e.symm ≪≫ hE⟩

/-- **The value of a descent sheaf isomorphic to a sheaf locally constant with projective values
is projective**: it is a stalk of that sheaf. -/
theorem moduleProjective_of_iso_descentSheaf [Nonempty X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} Λ))
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.smallEtaleTopology F)
    (eF : F ≅ G.descentSheaf Λ N ρ) : Module.Projective Λ N := by
  let pt := Scheme.residueEtalePoint.{u, v} X (Classical.arbitrary X)
  obtain ⟨E, hE, ⟨eE⟩⟩ := AlgebraicGeometry.exists_constantValue_iso_sheafFiber pt Λ
    (fun E : ModuleCat.{max (u + 1) v} Λ ↦ Module.Projective Λ E) F
    (Stacks.ConstantSheaf.isLocallyConstantWith_projective_of_isFiniteProjectiveLocallyConstant
      (F := F) Λ X.smallEtaleTopology hF)
  obtain ⟨eM⟩ := G.nonempty_sheafFiber_descentSheaf_iso Λ N ρ pt
  exact Module.Projective.of_equiv
    ((eE ≪≫ (pt.sheafFiber (A := ModuleCat.{max (u + 1) v} Λ)).mapIso eF ≪≫ eM).toLinearEquiv)

end AlgebraicGeometry.EtaleGaloisCovering

namespace Stacks.EtaleCohomology

section Descent

variable {X : Scheme.{u}} {H : Type} [Group H] [Finite H] (G : EtaleGaloisCovering X H)
  (n : ℕ) [NeZero n]

/-- The group ring `(ℤ/n)[H]` is self-injective. -/
theorem baer_monoidAlgebra_zmod :
    Module.Baer (MonoidAlgebra (ZMod n) H) (MonoidAlgebra (ZMod n) H) :=
  have := Fintype.ofFinite H
  MonoidAlgebra.baer_self (ZMod.baer_self n)

/-- **The stalks of `D((ℤ/n)[H])` are injective `(ℤ/n)[H]`-modules**, at every point of `X_étale`
with fibres in `Type (u + 1)`. -/
theorem moduleInjective_sheafFiber_regularDescentSheaf
    (p : GrothendieckTopology.Point.{max (u + 1) 0} X.smallEtaleTopology) :
    Module.Injective (MonoidAlgebra (ZMod n) H)
      ((p.sheafFiber (A := ModuleCat.{max (u + 1) 0} (MonoidAlgebra (ZMod n) H))).obj
        (G.regularDescentSheaf (A := ZMod n))) :=
  have : Module.Injective (MonoidAlgebra (ZMod n) H) (MonoidAlgebra (ZMod n) H) :=
    (baer_monoidAlgebra_zmod n).injective
  G.moduleInjective_sheafFiber_descentSheaf _ _ _
    (Module.ulift_injective_of_injective (MonoidAlgebra (ZMod n) H) inferInstance) p

end Descent

section ExtensionByZero

variable {R : Type} [Ring R] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The stalk of `j_! F` at a geometric point `s ≫ j` is the stalk of `F` at `s`. -/
def extensionByZeroSheafFiberIso {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U)
    (F : EtaleModules.{u, 0} R U) :
    (((pointSmallEtale (s ≫ j)).ulift.{max (u + 1) 0}).sheafFiber
      (A := ModuleCat.{max (u + 1) 0} R)).obj
        ((etaleModuleExtensionByZero.{u, 0} R j).obj F) ≅
      (((pointSmallEtale s).ulift.{max (u + 1) 0}).sheafFiber
        (A := ModuleCat.{max (u + 1) 0} R)).obj F :=
  ((etaleModuleInverseImageSheafFiberIso.{u, 0} R j s).app _).symm ≪≫
    (((pointSmallEtale s).ulift.{max (u + 1) 0}).sheafFiber
      (A := ModuleCat.{max (u + 1) 0} R)).mapIso
      (((etaleModuleInverseImageRestrictionIso.{u, 0} R j).app _) ≪≫
        (asIso ((etaleModuleExtensionByZeroAdj.{u, 0} R j).unit.app F)).symm)

/-- **The stalks of an extension by zero are injective** as soon as the stalks of the sheaf are:
at a geometric point of `U` the stalk of `j_! F` is that of `F`, at a point of the complement it
vanishes. -/
theorem moduleInjective_sheafFiber_extensionByZero (F : EtaleModules.{u, 0} R U)
    (hF : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
      Module.Injective R ((((pointSmallEtale s).ulift.{max (u + 1) 0}).sheafFiber
        (A := ModuleCat.{max (u + 1) 0} R)).obj F))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Module.Injective R ((((pointSmallEtale s).ulift.{max (u + 1) 0}).sheafFiber
      (A := ModuleCat.{max (u + 1) 0} R)).obj ((etaleModuleExtensionByZero.{u, 0} R j).obj F)) := by
  by_cases hs : s.base default ∈ Set.range j.base
  · obtain ⟨w, hw⟩ := hs
    obtain ⟨s', rfl⟩ := exists_lift_of_isPreimmersion j s w hw
    exact moduleInjective_of_iso (extensionByZeroSheafFiberIso j s' F).symm (hF Ω s')
  · let C : TopologicalSpace.Closeds X :=
      ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
    let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
    have hrange : Set.range i.base = (Set.range j.base)ᶜ :=
      Scheme.IdealSheafData.range_subschemeι_vanishingIdeal C
    have hij : Set.range j.base = (Set.range i.base)ᶜ := by rw [hrange, compl_compl]
    obtain ⟨z, hz⟩ : s.base default ∈ Set.range i.base := by rwa [hrange]
    obtain ⟨s'', rfl⟩ := exists_lift_of_isPreimmersion i s z hz
    exact moduleInjective_of_isZero (IsZero.of_iso (Functor.map_isZero
      (((pointSmallEtale s'').ulift.{max (u + 1) 0}).sheafFiber (A := ModuleCat.{max (u + 1) 0} R))
      (isZero_etaleModuleInverseImage_extensionByZero R i j hij F))
      ((etaleModuleInverseImageSheafFiberIso.{u, 0} R i s'').app _).symm)

end ExtensionByZero

section Complex

variable {R : Type} [Ring R] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] {U : Scheme.{u}} (jU : U ⟶ Y.left)
  [IsOpenImmersion jU]

/-- **The restriction to `Y_k̄` of `j_! D`, for `D` with injective stalks, has injective stalks**:
each term of the complex `(j_! D)[0]` pulled back to `Y_k̄` has injective stalks. -/
theorem moduleInjective_sheafFiber_extensionByZeroComplex (D : EtaleModules.{u, 0} R U)
    (hD : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
      Module.Injective R ((((pointSmallEtale s).ulift.{max (u + 1) 0}).sheafFiber
        (A := ModuleCat.{max (u + 1) 0} R)).obj D))
    (x : fieldBaseChange Y kbar) (m : ℤ) :
    Module.Injective R
      (((residueEtalePoint.{u, 0} (fieldBaseChange Y kbar) x).sheafFiber
        (A := ModuleCat.{max (u + 1) 0} R)).obj
          (((etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            ((etaleModuleExtensionByZero.{u, 0} R jU).mapCochainComplexPlus.obj
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D))).obj.X m)) := by
  refine moduleInjective_of_iso ((etaleModuleInverseImageSheafFiberIso.{u, 0} R
    (fieldBaseChangeProj Y kbar) _).app _).symm ?_
  by_cases hm : m = 0
  · subst hm
    exact moduleInjective_of_iso (((pointSmallEtale _).ulift.{max (u + 1) 0}).sheafFiber.mapIso
      ((etaleModuleExtensionByZero.{u, 0} R jU).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 D))).symm
      (moduleInjective_sheafFiber_extensionByZero jU D hD _)
  · exact moduleInjective_of_isZero (Functor.map_isZero
      (((pointSmallEtale _).ulift.{max (u + 1) 0}).sheafFiber (A := ModuleCat.{max (u + 1) 0} R))
      (Functor.map_isZero (etaleModuleExtensionByZero.{u, 0} R jU)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 D m hm)))

end Complex

end Stacks.EtaleCohomology

end
