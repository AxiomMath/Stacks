module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelModuleIntertwiner
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TwistNegOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekEnd
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientExactness

/-!
# The levels of `ℱ_ρ` are the lisse sheaves of the level modules

Let `X` be a connected Noetherian scheme of a big étale site with a geometric point `x̄`, and let
`ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous. The `n`-th level of the tower of the ℓ-adic sheaf `ℱ_ρ`
(`Stacks.EtaleCohomology.representationLAdicSheaf` for the canonical equivalence of Tag 0DV5 (2)),
read as a sheaf of `ℤ_ℓ`-modules on Mathlib's small étale site, is the restriction of scalars along
`ℤ_ℓ → ℤ/ℓ^{n+1}` of the lisse sheaf of the level module `(ℤ/ℓ^{n+1})^r`
(`Stacks.EtaleCohomology.padicTowerRepresentationLAdicSheafIso`), naturally in intertwiners: the
map of towers induced by an intertwiner `A` (`A ρ(g) = ρ'(g) A`) is the lisse sheaf of
multiplication by `A` modulo `ℓ^{n+1}`
(`Stacks.EtaleCohomology.padicTowerRepresentationLAdicSheafIso_naturality`).
These identifications are used for the sheaves of representations in piece L6 of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.padicTowerRepresentationLAdicSheafIso`.

## Main results

* `Stacks.EtaleCohomology.lisseSheaf_map_levelModuleHom`: the lisse sheaf of the map of level
  modules of an intertwiner is the map of level sheaves.
* `Stacks.EtaleCohomology.padicTowerRepresentationLAdicSheafIso_naturality`.
* `Stacks.EtaleCohomology.LAdicSheaf.representationSheaf_eq_representationLAdicSheaf`: the sheaf
  `ℱ_ρ` of a continuous `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` is the sheaf of its integral model.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] neZero_pow_of_fact_prime discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r r' : ℕ}

/-- **The lisse sheaf of the map of level modules of an intertwiner is the map of level sheaves**
of `Stacks.EtaleCohomology.representationLevelMap`, for the canonical equivalence of Tag 0DV5 (2).
-/
theorem lisseSheaf_map_levelModuleHom {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]}
    (hρ : Continuous ρ) {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]}
    (hρ' : Continuous ρ') (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (k : ℕ) :
    (lisseSheaf B X x (ZMod (ℓ ^ k))).map (levelModuleHom hρ hρ' A hA k) =
      representationLevelMap B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        hρ hρ' A hA k := by
  have h : (finiteTypeContinuousModuleForgetAbelian (ZMod (ℓ ^ k)) _).map
      (levelModuleHom hρ hρ' A hA k) = levelAbelianMap hρ hρ' A hA k :=
    finiteContinuousAbelianHom_ext _ rfl
  apply ObjectProperty.hom_ext
  ext U y
  exact congrArg (fun t => (t.hom.hom.app U).hom y)
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.congr_map h)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]

/-- **The `n`-th level of the tower of `ℱ_ρ` is the lisse sheaf of the level module**
`(ℤ/ℓ^{n+1})^r`, read as a sheaf of `ℤ_ℓ`-modules: both are the restriction of scalars of the
`(n + 1)`-st level sheaf, before and after reading it on Mathlib's small étale site. -/
def padicTowerRepresentationLAdicSheafIso (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ])
    (hρ : Continuous ρ) (n : ℕ) :
    (LAdicSheaf.padicTower B X ℓ (representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ)).obj (op n) ≅
      (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1).obj
        ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} ρ hρ (n + 1))) :=
  ((sheafEquivRestrictScalarsIso B X.1 X.2 (PadicInt.toZModPow (p := ℓ) (n + 1))).app
    ((lisseSheaf B X x (ZMod (ℓ ^ (n + 1)))).obj (levelModule.{u + 1, u + 1} ρ hρ (n + 1)))).symm

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **Naturality of `Stacks.EtaleCohomology.padicTowerRepresentationLAdicSheafIso` in
intertwiners**: on the `n`-th level, the map of towers induced by an intertwiner `A` of `ρ` and
`ρ'` is the restriction of scalars of the lisse sheaf of multiplication by `A` modulo `ℓ^{n+1}`. -/
theorem padicTowerRepresentationLAdicSheafIso_naturality
    {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
    {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')
    (A : Matrix (Fin r') (Fin r) ℤ_[ℓ]) (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (n : ℕ) :
    (LAdicSheaf.padicTowerMap (representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ' A hA)).app (op n) ≫
        (padicTowerRepresentationLAdicSheafIso B X x ρ' hρ' n).hom =
      (padicTowerRepresentationLAdicSheafIso B X x ρ hρ n).hom ≫
        (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1).map
          ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).map
            (levelModuleHom hρ hρ' A hA (n + 1))) := by
  have h :=
    (sheafEquivRestrictScalarsIso B X.1 X.2 (PadicInt.toZModPow (p := ℓ) (n + 1))).inv.naturality
      ((lisseSheaf B X x (ZMod (ℓ ^ (n + 1)))).map (levelModuleHom hρ hρ' A hA (n + 1)))
  rwa [lisseSheaf_map_levelModuleHom] at h

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **`ℱ_ρ` is the ℓ-adic sheaf of the integral model of `ρ`**, for the canonical equivalence of
Tag 0DV5 (2), so that its levels are described by
`Stacks.EtaleCohomology.padicTowerRepresentationLAdicSheafIso`. -/
theorem LAdicSheaf.representationSheaf_eq_representationLAdicSheaf
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    LAdicSheaf.representationSheaf B X x ρ hρ =
      representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (integralModel ρ hρ) (continuous_integralModel ρ hρ) :=
  rfl

end Stacks.EtaleCohomology

end
