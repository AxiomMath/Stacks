module

public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.LerayScalars
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.DerivedSectionsOpenRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.RestrictionPreservesInjectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishingAffine

/-!
# Top-degree cohomology of an open subscheme is a quotient of that of the scheme

Let `Y` be a Noetherian scheme over a field `k` of dimension at most `d`, `G` an `𝒪_Y`-module
and `U ⊆ Y` an open. Restriction `H^d(Y, G) ⟶ H^d(U, G|_U)` is surjective ([Stacks, Tag 0A3G]
clause (2)) and `k`-linear, so if `H^d(Y, G)` is finite-dimensional so is `H^d(U, G|_U)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.HypercoveringModules

universe u

namespace AlgebraicGeometry.CohomologyScalars

/-- A scheme as a sheafed space of rings. -/
def asRingSheafedSpace (Y : Scheme.{u}) : SheafedSpace RingCat.{u} :=
  SheafedSpace.mk (PresheafedSpace.mk Y.carrier Y.ringCatSheaf.obj) Y.ringCatSheaf.property

/-- Restriction of `𝒪_Y`-modules to an open `U` agrees with `restMod` on the ringed space
`asRingSheafedSpace Y`. -/
theorem restrictFunctor_eq_restMod (Y : Scheme.{u}) (U : Y.Opens) :
    Scheme.Modules.restrictFunctor U.ι = restMod (asRingSheafedSpace Y) U := by
  unfold Scheme.Modules.restrictFunctor restMod
  congr 1
  ext V
  simp [phiSh, Scheme.Opens.ι_appIso]
  rfl

/-- Restriction of `𝒪_Y`-modules to an open subscheme preserves injective objects. -/
theorem restrictFunctor_preservesInjectiveObjects (Y : Scheme.{u}) (U : Y.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).PreservesInjectiveObjects := by
  constructor
  intro I hI
  rw [restrictFunctor_eq_restMod]
  exact @Stacks.Cohomology.HigherDirectImage.restMod_preservesInjective
    (asRingSheafedSpace Y) U I hI

/-- Restriction of `𝒪_Y`-modules to an open subscheme preserves finite limits. -/
theorem restrictFunctor_preservesFiniteLimits (Y : Scheme.{u}) (U : Y.Opens) :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) := by
  have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.restrictFunctor U.ι) := by
    rw [restrictFunctor_eq_restMod]
    exact (jShriekAdjunction (asRingSheafedSpace Y) U).rightAdjoint_preservesLimits
  infer_instance

/-- Restriction of modules along an open immersion `j` is isomorphic to restriction to the open
`j.opensRange` followed by restriction along `j.isoOpensRange.hom`. -/
def restrictFunctorIsoRange {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Scheme.Modules.restrictFunctor j.opensRange.ι ⋙
        Scheme.Modules.restrictFunctor j.isoOpensRange.hom ≅
      Scheme.Modules.restrictFunctor j :=
  (Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).symm ≪≫
    Scheme.Modules.restrictFunctorCongr j.isoOpensRange_hom_ι

/-- Restriction of modules along an open immersion preserves finite limits. -/
instance restrictFunctor_preservesFiniteLimits_ofIsOpenImmersion {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor j) :=
  have := Stacks.RegularSequence.restrictFunctor_isEquivalence j.isoOpensRange
  have := restrictFunctor_preservesFiniteLimits Y j.opensRange
  preservesFiniteLimits_of_natIso (restrictFunctorIsoRange j)

/-- Restriction of modules along an open immersion preserves injective objects. -/
theorem restrictFunctor_preservesInjectiveObjects' {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : (Scheme.Modules.restrictFunctor j).PreservesInjectiveObjects := by
  have := Stacks.RegularSequence.restrictFunctor_isEquivalence j.isoOpensRange
  have := restrictFunctor_preservesInjectiveObjects Y j.opensRange
  constructor
  intro I hI
  have : Injective I := hI
  exact Injective.of_iso ((restrictFunctorIsoRange j).app I) inferInstance

/-- Restriction of modules along an open immersion preserves finite colimits. -/
theorem restrictFunctor_preservesFiniteColimits' {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] : PreservesFiniteColimits (Scheme.Modules.restrictFunctor j) :=
  preservesFiniteColimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback j).symm

/-- Restriction of modules along an open immersion is an additive functor. -/
instance restrictFunctor_additive' {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (Scheme.Modules.restrictFunctor j).Additive :=
  have := restrictFunctor_preservesFiniteLimits_ofIsOpenImmersion j
  Functor.additive_of_preserves_binary_products _

/-- Sections of the restriction along an open immersion over the whole source are sections over
its image. -/
def secFRestrictIso' {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    secF Y.ringCatSheaf (j ''ᵁ ⊤) ≅ Scheme.Modules.restrictFunctor j ⋙ secF X.ringCatSheaf ⊤ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- **Cohomology over the image of an open immersion is cohomology of its source**, naturally in
the module. -/
def hfunctorOpenImmersionIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    Hfunctor Y.ringCatSheaf (j ''ᵁ ⊤) n ≅
      Scheme.Modules.restrictFunctor j ⋙ Hfunctor X.ringCatSheaf ⊤ n :=
  have := restrictFunctor_preservesFiniteLimits_ofIsOpenImmersion j
  have := restrictFunctor_preservesFiniteColimits' j
  have := restrictFunctor_preservesInjectiveObjects' j
  @Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso _ _ _ _ _ _ _ _ _
      (secFAdditive _ _) (Functor.additive_of_iso (secFRestrictIso' j)) (secFRestrictIso' j) n ≪≫
    @Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      _ _ _ _ _ _ _ _ _ _ _ (Scheme.Modules.restrictFunctor j) (secF X.ringCatSheaf ⊤)
      _ (secFAdditive _ _) _ _ _ n

/-- **The restriction of a scalar endomorphism along an open immersion is a scalar
endomorphism.** -/
theorem restrictFunctor_map_scalarEndo' {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (G : Y.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.restrictFunctor j).map (scalarEndo G r) =
      scalarEndo ((Scheme.Modules.restrictFunctor j).obj G) (j.appTop r) := by
  ext W x
  change (scalarEndo G r).app (j ''ᵁ W) x = _
  have hL := Stacks.SheafOfModules.smul_val_app Y.ringCatSheaf _ ⊤ isTerminalTop (RingHom.id _)
    r (𝟙 (show SheafOfModules.{u} Y.ringCatSheaf from G)) (op (j ''ᵁ W)) x
  have hR := Stacks.SheafOfModules.smul_val_app X.ringCatSheaf _ ⊤ isTerminalTop
    (RingHom.id _) (j.appTop r)
    (𝟙 (show SheafOfModules.{u} X.ringCatSheaf from
      (Scheme.Modules.restrictFunctor j).obj G)) (op W) x
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hn : Y.presheaf.map (isTerminalTop.from (j ''ᵁ W)).op r =
      (j.appIso W).inv (X.presheaf.map (isTerminalTop.from W).op (j.appTop r)) := by
    apply (ConcreteCategory.bijective_of_isIso (j.appIso W).hom).1
    rw [Iso.inv_hom_id_apply, Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply,
      ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rw [Scheme.Hom.appLE]
    rfl
  exact congrArg (fun t => (show Y.ringCatSheaf.obj.obj (op (j ''ᵁ W)) from t) •
    (show G.val.obj (op (j ''ᵁ W)) from x)) hn

/-- Restriction of `𝒪_Y`-modules to an open subscheme preserves finite colimits. -/
theorem restrictFunctor_preservesFiniteColimits (Y : Scheme.{u}) (U : Y.Opens) :
    PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι) :=
  restrictFunctor_preservesFiniteColimits' U.ι

/-- Restriction of `𝒪_Y`-modules to an open subscheme is an additive functor. -/
instance restrictFunctor_additive (Y : Scheme.{u}) (U : Y.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).Additive :=
  have := restrictFunctor_preservesFiniteLimits Y U
  Functor.additive_of_preserves_binary_products _

/-- Sections of the restriction to an open over the whole open subscheme are sections over the
open. -/
def secFRestrictIso (Y : Scheme.{u}) (U : Y.Opens) :
    secF Y.ringCatSheaf (U.ι ''ᵁ ⊤) ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ secF U.toScheme.ringCatSheaf ⊤ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- **Cohomology over an open is cohomology of the open subscheme**, naturally in the module. -/
def hfunctorOpenIso (Y : Scheme.{u}) (U : Y.Opens) (n : ℕ) :
    Hfunctor Y.ringCatSheaf (U.ι ''ᵁ ⊤) n ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Hfunctor U.toScheme.ringCatSheaf ⊤ n :=
  have := restrictFunctor_preservesFiniteLimits Y U
  have := restrictFunctor_preservesFiniteColimits Y U
  have := restrictFunctor_preservesInjectiveObjects Y U
  @Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso _ _ _ _ _ _ _ _ _
      (secFAdditive _ _) (Functor.additive_of_iso (secFRestrictIso Y U)) (secFRestrictIso Y U) n ≪≫
    @Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      _ _ _ _ _ _ _ _ _ _ _ (Scheme.Modules.restrictFunctor U.ι) (secF U.toScheme.ringCatSheaf ⊤)
      _ (secFAdditive _ _) _ _ _ n

/-- **The restriction of a scalar endomorphism is a scalar endomorphism.** -/
theorem restrictFunctor_map_scalarEndo (Y : Scheme.{u}) (U : Y.Opens) (G : Y.Modules)
    (r : Γ(Y, ⊤)) :
    (Scheme.Modules.restrictFunctor U.ι).map (scalarEndo G r) =
      scalarEndo ((Scheme.Modules.restrictFunctor U.ι).obj G) (U.ι.appTop r) :=
  restrictFunctor_map_scalarEndo' U.ι G r

attribute [local instance] Stacks.Topology.hasExt_sheafOpens

/-- Top-degree finiteness passes along an open immersion, given a natural isomorphism
identifying cohomology over the image with that of the source. -/
private theorem finiteDimensional_cohomologyOverField_restrict_aux (k : Type u) [Field k]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (g : Y ⟶ Spec (.of k))
    [IsNoetherian Y] (d : ℕ) (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (G : Y.Modules)
    [FiniteDimensional k (cohomologyOverField k g G d)]
    (Φ : Hfunctor Y.ringCatSheaf (j ''ᵁ ⊤) d ≅
      Scheme.Modules.restrictFunctor j ⋙ Hfunctor X.ringCatSheaf ⊤ d) :
    FiniteDimensional k
      (cohomologyOverField k (j ≫ g) ((Scheme.Modules.restrictFunctor j).obj G) d) := by
  have : SpectralSpace Y := ⟨⟩
  have hcpt : IsCompact ((j ''ᵁ ⊤ : Y.Opens) : Set Y) :=
    (NoetherianSpace.isCompact _)
  let ρ := Hrestrict Y.ringCatSheaf (show j ''ᵁ ⊤ ≤ ⊤ from le_top) d G
  let Ψ := Φ.app G
  have hρ : Function.Surjective ρ :=
    Stacks.TopDegreeRestriction.surjective_hrestrict_of_topologicalKrullDim_le
      Y.ringCatSheaf G d hdim (j ''ᵁ ⊤) hcpt
  let e := (ρ ≫ Ψ.hom)
  refine finiteDimensional_of_surjective (f := g) (f' := j ≫ g) e.hom ?_
    ((ConcreteCategory.bijective_of_isIso Ψ.hom).2.comp hρ)
  intro a x
  have h1 := ConcreteCategory.congr_hom ((HrestrictNT Y.ringCatSheaf
    (show j ''ᵁ ⊤ ≤ ⊤ from le_top) d).naturality (scalarEndo G (fieldScalar k g a))) x
  have h2 := ConcreteCategory.congr_hom (Φ.hom.naturality
    (scalarEndo G (fieldScalar k g a))) (ρ x)
  have hφ : (Scheme.Modules.restrictFunctor j ⋙ Hfunctor X.ringCatSheaf ⊤ d).map
      (scalarEndo G (fieldScalar k g a)) = (Hfunctor X.ringCatSheaf ⊤ d).map
        (scalarEndo ((Scheme.Modules.restrictFunctor j).obj G) (fieldScalar k (j ≫ g) a)) := by
    change (Hfunctor X.ringCatSheaf ⊤ d).map
      ((Scheme.Modules.restrictFunctor j).map _) = _
    rw [restrictFunctor_map_scalarEndo', fieldScalar_comp]
  change Ψ.hom (ρ ((Hfunctor Y.ringCatSheaf ⊤ d).map (scalarEndo G (fieldScalar k g a)) x)) = _
  refine (congrArg Ψ.hom h1).trans (h2.trans ?_)
  exact ConcreteCategory.congr_hom hφ (Ψ.hom (ρ x))

/-- **Top-degree finiteness passes to an open subscheme** ([Stacks, Tag 0A3G] clause (2)). Let
`Y` be a Noetherian scheme over `k` of dimension at most `d`, `G` an `𝒪_Y`-module with
`H^d(Y, G)` finite-dimensional and `U ⊆ Y` open. Then `H^d(U, G|_U)` is finite-dimensional. -/
theorem finiteDimensional_cohomologyOverField_restrict (k : Type u) [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsNoetherian Y] (d : ℕ)
    (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (U : Y.Opens) (G : Y.Modules)
    [FiniteDimensional k (cohomologyOverField k g G d)] :
    FiniteDimensional k
      (cohomologyOverField k (U.ι ≫ g) ((Scheme.Modules.restrictFunctor U.ι).obj G) d) :=
  finiteDimensional_cohomologyOverField_restrict_aux k U.ι g d hdim G (hfunctorOpenIso Y U d)

/-- **Top-degree finiteness passes along an open immersion** ([Stacks, Tag 0A3G] clause (2)). -/
theorem finiteDimensional_cohomologyOverField_restrict' (k : Type u) [Field k] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (g : Y ⟶ Spec (.of k)) [IsNoetherian Y] (d : ℕ)
    (hdim : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) (G : Y.Modules)
    [FiniteDimensional k (cohomologyOverField k g G d)] :
    FiniteDimensional k
      (cohomologyOverField k (j ≫ g) ((Scheme.Modules.restrictFunctor j).obj G) d) :=
  finiteDimensional_cohomologyOverField_restrict_aux k j g d hdim G
    (hfunctorOpenImmersionIso j d)

end AlgebraicGeometry.CohomologyScalars

end
