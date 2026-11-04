module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineChaoticCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedPushforwardVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.InjectiveSheafSections

/-!
# The level sections of an injective abelian sheaf are acyclic for the inverse limit

Let `(A, I, γ) → C` be an affine crystalline situation and `𝒞 = (Cris(C/A))ᵒᵖ`. For a completed
thickening with finite levels `B_e`, the level transitions `B_{e+1} ↠ B_e` are surjections of
divided power rings, hence epimorphisms of `Cris(C/A)` and monomorphisms of `𝒞`. An injective
abelian sheaf `I` on `𝒞` therefore has surjective transition maps on the inverse system
`e ↦ I(B_e)` of its level sections, so this system is Mittag-Leffler and all of its derived limits
vanish in positive degrees ([Stacks, Tag 07KW]).

## Main results

* `Crystalline.epi_of_surjective_hom`: a morphism of `Cris(C/A)` whose underlying map of divided
  power rings is surjective is an epimorphism.
* `Crystalline.FiniteLevelSystem.surjective_transition_hom`: the level transitions of a
  finite-level system are surjective on divided power rings.
* `Crystalline.FiniteLevelSystem.epi_transition`: the level transitions are epimorphisms of
  `Cris(C/A)`.
* `Crystalline.FiniteLevelSystem.mono_transition_op`: the level transitions are monomorphisms of
  `𝒞`.
* `Crystalline.surjective_map_of_injective`: an injective abelian sheaf on `𝒞` sends an
  epimorphism of `Cris(C/A)` to a surjection on sections.
* `Crystalline.surjective_finiteLevelSections_transition_of_injective`: the level sections of an
  injective abelian sheaf have surjective transition maps.
* `Crystalline.isZero_firstDerivedLimit_finiteLevelSections_of_injective`: the first derived limit
  of the level sections of an injective abelian sheaf vanishes.
* `Crystalline.isZero_homology_rightDerivedLimit_finiteLevelSections_of_injective`: every derived
  limit of the level sections of an injective abelian sheaf vanishes in positive degrees.

## References

* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
* [Stacks Project, Tag 07KW](https://stacks.math.columbia.edu/tag/07KW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe uAb

/-- The inverse limit functor on inverse systems of abelian groups is additive. -/
noncomputable local instance limAdditiveInjectiveLevelAcyclicity :
    (lim : Rlim.InvSystemAb.{uAb} ⥤ Ab.{uAb}).Additive :=
  Functor.additive_of_preserves_binary_products _

namespace Crystalline

universe u v w

variable {s : AffineCrystallineSituation.{u, v}}

/-! ### The level transitions are epimorphisms of the little crystalline category -/

/-- A morphism of `Cris(C/A)` with surjective underlying map of divided power rings is an
epimorphism. -/
theorem epi_of_surjective_hom {X Y : CrystallineThickening.{u, v, w} s} (f : X ⟶ Y)
    (hf : Function.Surjective f.hom.hom) : Epi f := by
  refine ⟨fun {Z} g₁ g₂ hg => ObjectProperty.hom_ext _ <| DividedPowerThickening.Hom.ext <|
    DividedPowers.DPMorphism.ext <| funext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hf y
  exact congrArg (fun k : X ⟶ Z => k.hom.hom x) hg

namespace FiniteLevelSystem

variable {X : CompletedCrystallineThickening.{u, v, w} s}

/-- The level transitions of a finite-level system are surjective on divided power rings. -/
theorem surjective_transition_hom (T : FiniteLevelSystem X) {e e' : ℕ} (h : e ≤ e') :
    Function.Surjective (T.transition h).hom.hom := fun y => by
  obtain ⟨x, rfl⟩ := T.projection_surjective e y
  exact ⟨T.projection e' x, congrArg (fun k => k x) (T.transition_projection h)⟩

/-- The level transitions of a finite-level system are epimorphisms of `Cris(C/A)`. -/
theorem epi_transition (T : FiniteLevelSystem X) {e e' : ℕ} (h : e ≤ e') :
    Epi (T.transition h) :=
  epi_of_surjective_hom _ (T.surjective_transition_hom h)

/-- The level transitions of a finite-level system are monomorphisms of `𝒞 = (Cris(C/A))ᵒᵖ`. -/
theorem mono_transition_op (T : FiniteLevelSystem X) {e e' : ℕ} (h : e ≤ e') :
    Mono (T.transition h).op :=
  have := T.epi_transition h
  inferInstance

end FiniteLevelSystem

/-! ### Sections of an injective abelian sheaf along an epimorphism of `Cris(C/A)` -/

/-- An injective abelian sheaf on `𝒞 = (Cris(C/A))ᵒᵖ` sends an epimorphism of `Cris(C/A)` to a
surjection on sections of the associated abelian presheaf on `Cris(C/A)`. -/
theorem surjective_map_of_injective
    (I : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) [Injective I]
    {X Y : CrystallineThickening.{u, v, w} s} (f : X ⟶ Y) [Epi f] :
    Function.Surjective
      (ConcreteCategory.hom (((abelianSheafEquivalence s).functor.obj I).map f)) :=
  Stacks.EtaleCohomology.RelativeMayerVietoris.injective_sections_map_surjective
    (littleChaoticTopology.{u, v, w} s) I f.op

/-! ### Acyclicity of the level sections of an injective abelian sheaf -/

variable {X : CompletedCrystallineThickening.{u, v, w} s}

/-- The inverse system `e ↦ I(B_e)` of level sections of an injective abelian sheaf `I` has
surjective transition maps. -/
theorem surjective_finiteLevelSections_transition_of_injective (T : FiniteLevelSystem X)
    (I : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) [Injective I] (e : ℕ) :
    Function.Surjective (ConcreteCategory.hom
      (((abelianSheafEquivalence s).functor.obj I).map (T.transition (Nat.le_succ e)))) :=
  have := T.epi_transition (Nat.le_succ e)
  surjective_map_of_injective I _

/-- The first derived limit of the level sections of an injective abelian sheaf vanishes. -/
theorem isZero_firstDerivedLimit_finiteLevelSections_of_injective (T : FiniteLevelSystem X)
    (I : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) [Injective I] :
    IsZero (Rlim.firstDerivedLimit
      (finiteLevelSections T ((abelianSheafEquivalence s).functor.obj I))) :=
  isZero_firstDerivedLimit_finiteLevelSections T _
    (surjective_finiteLevelSections_transition_of_injective T I)

/-- The level sections of an injective abelian sheaf are acyclic for the inverse limit: for an
arbitrary right derived functor `RF` of the inverse limit functor, every derived limit of the
inverse system `e ↦ I(B_e)` vanishes in every positive degree. -/
theorem isZero_homology_rightDerivedLimit_finiteLevelSections_of_injective
    (T : FiniteLevelSystem X)
    (I : Sheaf (littleChaoticTopology.{u, v, w} s) Ab.{max u v (w + 1)}) [Injective I]
    (RF : DerivedCategory Rlim.InvSystemAb.{max u v (w + 1)} ⥤
      DerivedCategory Ab.{max u v (w + 1)})
    (α : (lim : Rlim.InvSystemAb.{max u v (w + 1)} ⥤ Ab.{max u v (w + 1)}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{max u v (w + 1)} (ComplexShape.up ℤ)))
    (p : ℤ) (hp : 1 ≤ p) :
    IsZero ((DerivedCategory.homologyFunctor Ab.{max u v (w + 1)} p).obj
      (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{max u v (w + 1)} 0).obj
        (finiteLevelSections T ((abelianSheafEquivalence s).functor.obj I))))) :=
  isZero_homology_rightDerivedLimit_finiteLevelSections T _
    (surjective_finiteLevelSections_transition_of_injective T I) RF α hRF p hp

end Crystalline

end
