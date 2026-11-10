module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLevelPairingRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionByZeroOplaxMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationLevelPairingPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralDirectImage

/-!
# The coefficient pairing of Poincaré duality for the sheaf of a representation on an open curve

Let `ρ₀ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous on a connected noetherian scheme `X`, `F = ℱ_{ρ₀}`,
`F' = ℱ_{ρ₀^∨}`, `j : X ⟶ X̄` a compactification over a field `k`, `k̄` an extension of `k` and
`N = ℓⁿ⁺¹`. The pairing of the levels `μ_X : Fₙ ⊗ F'ₙ ⟶ ℤ/N` on `X`
(`Stacks.EtaleCohomology.levelTensorHom`, the dot product of `ρ₀` and its contragredient) is the
evaluation of an exact pairing on `X`
(`Stacks.EtaleCohomology.representationLevelOpenExactPairing`; no properness of `X` is needed).
Extended by zero it gives the pairing `μₙ : j_! Fₙ ⊗ j_! F'ₙ ≅ j_!(Fₙ ⊗ F'ₙ) ⟶ j_! ℤ/N ⟶ ℤ/N` on
`X̄` (`Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing`), and its pullback to
`X_k̄ ⊂ X̄_k̄` is perfect on the fibres at all points with separably closed residue field
(`Stacks.EtaleCohomology.LAdicSheaf.bijective_sheafFiber_representationCurveLevelPairing`). This is
the hypothesis `hμ` of the finite-level Poincaré duality on a curve
(`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_bounds`) for `F = ℱ_{ρ₀}`, `F' = ℱ_{ρ₀^∨}`,
in the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); the other two
coefficient hypotheses are, in the namespace `Stacks.EtaleCohomology`,
`isFiniteTypeLocallyConstant_inverseImage_etaleLevel_representationLAdicSheaf` and
`flat_sheafFiber_inverseImage_extensionByZero_representationLAdicSheaf`.

## Main definitions

* `Stacks.EtaleCohomology.representationLevelOpenExactPairing`.
* `Stacks.EtaleCohomology.LAdicSheaf.representationCurveLevelPairing`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.bijective_sheafFiber_representationCurveLevelPairing`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize Sheaf.monoidalCategory
  etaleModules_AB5OfSize etaleModules_preservesFilteredColimits_forget
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

attribute [local instance] isMonoidal_W_etaleModules

/-- Sheafification on the slices of the small étale site, at the coefficient universe `u + 1`. -/
local instance hasWeakSheafify_smallEtale_over_representationExtension (Y : Scheme.{u}) (N : ℕ)
    (V : Y.Etale) :
    HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} (ZMod N)) :=
  haveI := Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1}
    (Y.smallEtaleTopology.over V) (ZMod N)
  inferInstance

attribute [local instance] AlgebraicGeometry.moduleCat_preservesColimits_tensorLeft
  AlgebraicGeometry.moduleCat_preservesColimits_tensorRight
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1] (n : ℕ)

/-- A power `ℓ ^ n` of a prime `ℓ` is nonzero. -/
local instance neZero_prime_pow_curveLevelPairingExtension (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

set_option synthInstance.maxHeartbeats 200000 in
-- instance synthesis on the étale sheaf categories of `ZMod (ℓ ^ (n + 1))`-modules used here
/-- **The pairing of the levels is the evaluation of an exact pairing on `X`**: the lisse sheaves
of the level modules of `ρ₀^∨` and `ρ₀` form an exact pairing whose evaluation is
`Stacks.EtaleCohomology.levelTensorHom` (`Stacks.SheafDuality.exactPairingOfPerfect` at the
geometric points: the levels of `ℱ_{ρ₀^∨}` are lisse with flat fibres and the pairing is perfect
on the fibres at the geometric points). -/
@[instance_reducible]
def representationLevelOpenExactPairing :
    ExactPairing ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
        (levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀) (n + 1)))
      ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
        (levelModule.{u + 1, u + 1} ρ₀ hρ₀ (n + 1))) := by
  haveI : ∀ V : X.1.Etale,
      (X.1.smallEtaleTopology.over V).WEqualsLocallyBijective
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :=
    fun V => Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, u + 1, 0} _ _
  refine Stacks.SheafDuality.exactPairingOfPerfect
    (isConservativeFamilyOfPoints_geometricPointsAt B X)
    (levelTensorHom B X x ρ₀ hρ₀ (n + 1)) ?_ ?_ ?_
  · exact isFiniteTypeLocallyConstant_etaleLevel_representationLAdicSheaf B X x _ _ n
  · rintro ⟨_, ⟨y⟩⟩
    exact flat_sheafFiber_ulift_of_flat _ _ _ (flat_sheafFiber_of_powExact _
      (powExact_etaleLevel_representationLAdicSheaf B X x (contragredient ρ₀)
        (continuous_contragredient hρ₀) n) _)
  · rintro ⟨_, ⟨y⟩⟩
    have h := Function.Bijective.comp (LinearEquiv.congrRight (Stacks.SheafDuality.unitEquiv
      ((Scheme.pointSmallEtale (geometricPointAt X.1 y).hom).ulift.{u + 1}).sheafFiber)).bijective
        (bijective_levelTensorHom_ulift B X x ρ₀ hρ₀ (n + 1) (geometricPointAt X.1 y))
    convert h using 1
    funext b
    ext g
    rfl

/-- The evaluation of `Stacks.EtaleCohomology.representationLevelOpenExactPairing` is the dot
product pairing `Stacks.EtaleCohomology.levelTensorHom`. -/
theorem representationLevelOpenExactPairing_evaluation :
    letI := representationLevelOpenExactPairing B X x ρ₀ hρ₀ n
    ε_ ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
        (levelModule.{u + 1, u + 1} (contragredient ρ₀) (continuous_contragredient hρ₀) (n + 1)))
      ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
        (levelModule.{u + 1, u + 1} ρ₀ hρ₀ (n + 1))) = levelTensorHom B X x ρ₀ hρ₀ (n + 1) :=
  rfl

/-- **The levels of `ℱ_{ρ₀}` are the lisse sheaves of the level modules**, as an isomorphism of
étale sheaves on Mathlib's small étale site (an equality, `lisseSheaf_obj_levelModule`). -/
def representationLevelEtaleIso :
    LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n ≅
      (lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
        (levelModule.{u + 1, u + 1} ρ₀ hρ₀ (n + 1)) :=
  (SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).functor.mapIso
    (eqToIso (lisseSheaf_obj_levelModule B X x ρ₀ hρ₀ (n + 1)).symm)

/-- **The pairing of the levels of `ℱ_{ρ₀}` and `ℱ_{ρ₀^∨}`** `Fₙ ⊗ F'ₙ ⟶ ℤ/N` on `X`: the dot
product pairing `Stacks.EtaleCohomology.levelTensorHom`, through the identifications of the levels
with the lisse sheaves of the level modules. -/
def representationLevelEtalePairing :
    LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n ⊗
      LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ₀)
          (continuous_contragredient hρ₀)) n ⟶
      𝟙_ (EtaleModules.{u, 0} (ZMod (ℓ ^ (n + 1))) X.1) :=
  _ ◁ (representationLevelEtaleIso B X x (contragredient ρ₀)
      (continuous_contragredient hρ₀) n).hom ≫
    (representationLevelEtaleIso B X x ρ₀ hρ₀ n).hom ▷ _ ≫ levelTensorHom B X x ρ₀ hρ₀ (n + 1)

/-- **The pairing of the levels of `ℱ_{ρ₀}` and `ℱ_{ρ₀^∨}` is the evaluation of an exact pairing
on `X`**: transport of `Stacks.EtaleCohomology.representationLevelOpenExactPairing` along
`Stacks.EtaleCohomology.representationLevelEtaleIso`. -/
@[instance_reducible]
def representationLevelEtaleExactPairing :
    ExactPairing (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ₀)
          (continuous_contragredient hρ₀)) n)
      (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n) :=
  letI := representationLevelOpenExactPairing B X x ρ₀ hρ₀ n
  exactPairingCongr
    (representationLevelEtaleIso B X x (contragredient ρ₀) (continuous_contragredient hρ₀) n)
    (representationLevelEtaleIso B X x ρ₀ hρ₀ n)

/-- The evaluation of `Stacks.EtaleCohomology.representationLevelEtaleExactPairing` is the pairing
of the levels `Stacks.EtaleCohomology.representationLevelEtalePairing`. -/
theorem representationLevelEtaleExactPairing_evaluation :
    letI := representationLevelEtaleExactPairing B X x ρ₀ hρ₀ n
    ε_ (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ₀)
          (continuous_contragredient hρ₀)) n)
      (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n) =
      representationLevelEtalePairing B X x ρ₀ hρ₀ n :=
  rfl

variable {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The coefficient pairing of Poincaré duality on `X ⊂ X̄` for `ℱ_{ρ₀}`**:
`j_! Fₙ ⊗ j_! F'ₙ ≅ j_!(Fₙ ⊗ F'ₙ) ⟶ j_! ℤ/N ⟶ ℤ/N` for `F = ℱ_{ρ₀}`, `F' = ℱ_{ρ₀^∨}`, the pairing
of the levels (`Stacks.EtaleCohomology.representationLevelEtalePairing`) extended by zero
(`Stacks.EtaleCohomology.extensionByZeroPairing`). -/
def LAdicSheaf.representationCurveLevelPairing :
    (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
        (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ₀)
            (continuous_contragredient hρ₀)) n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        j.space.smallEtaleTopology :=
  haveI : IsOpenImmersion j.immersion := j.property.1
  extensionByZeroPairing (ℓ ^ (n + 1)) j.immersion (representationLevelEtalePairing B X x ρ₀ hρ₀ n)

/-- **The coefficient pairing for `ℱ_{ρ₀}` is perfect over `X_k̄`**: its pullback to `X̄_k̄` and
then to `X_k̄` is perfect on the fibres at all points with separably closed residue field. The
pairing of the levels is the evaluation of an exact pairing on `X`
(`Stacks.EtaleCohomology.representationLevelEtaleExactPairing`) and `X_k̄ ⟶ X̄_k̄ ⟶ X̄` factors
through `j` (in the namespace `Stacks.EtaleCohomology`,
`bijective_sheafFiber_inverseImageConstantPairing_extensionByZeroPairing`). -/
theorem LAdicSheaf.bijective_sheafFiber_representationCurveLevelPairing
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar) :
    Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
      (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeMap j.obj.hom kbar)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
            (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n))))
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeMap j.obj.hom kbar)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
            (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (contragredient ρ₀)
                (continuous_contragredient hρ₀)) n)))) ≫
      (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
        (inverseImageConstantPairing (fieldBaseChangeMap j.obj.hom kbar) (ℓ ^ (n + 1))
          (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk j.toBase) kbar)
            (ℓ ^ (n + 1))
            (LAdicSheaf.representationCurveLevelPairing B X x ρ₀ hρ₀ n f j)))).hom) := by
  have : IsOpenImmersion j.immersion := j.property.1
  let := representationLevelEtaleExactPairing B X x ρ₀ hρ₀ n
  exact bijective_sheafFiber_inverseImageConstantPairing_extensionByZeroPairing (ℓ ^ (n + 1))
    j.immersion (fieldBaseChangeProj (Over.mk j.toBase) kbar) (fieldBaseChangeMap j.obj.hom kbar)
    (fieldBaseChangeProj (Over.mk f) kbar) (fieldBaseChangeMap_comp_fst j.obj.hom kbar).symm _ _
    Ω s

end Stacks.EtaleCohomology

end
