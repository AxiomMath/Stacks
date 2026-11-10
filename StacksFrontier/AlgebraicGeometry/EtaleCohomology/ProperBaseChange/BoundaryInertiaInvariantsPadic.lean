module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryStalkFrobeniusSpecialization
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryInertiaInvariantsLevels
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalkFunctoriality

/-!
# The stalks of the `ℤ_ℓ`-module levels of `ℱ_ρ`, and `H⁰_loc` with `ℤ_ℓ` coefficients

The levels of an ℓ-adic sheaf, read as sheaves of `ℤ_ℓ`-modules
(`Stacks.EtaleCohomology.LAdicSheaf.padicLevel`), all live in one category, so that the transition
maps and the morphisms induced by intertwiners are morphisms there. For the ℓ-adic sheaf `ℱ_ρ` of
a continuous `ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` this file identifies the stalk at a geometric point `s̄`
of the `n`-th `ℤ_ℓ`-level with `(ℤ/ℓⁿ⁺¹)^r` along a path from `s̄` to `x̄`, compatibly with the
maps of Tag 04FN (which become `ρ mod ℓⁿ⁺¹`), with the transitions (reduction) and with the maps
induced by intertwiners (multiplication by the reduced matrix).

Combined with the specialization map of `j_*` at a boundary point
(`Stacks.EtaleCohomology.directImageStalkToStalkHom`, for the coefficient ring `ℤ_ℓ`), this gives
`H⁰_loc` of the `ℤ_ℓ`-levels of `ℱ_ρ` as the inertia invariants of `(ℤ/ℓⁿ⁺¹)^r`.

## Main definitions

* `Stacks.EtaleCohomology.padicLevelStalkIso` — the stalk of the `n`-th `ℤ_ℓ`-level is
  `(ℤ/ℓⁿ⁺¹)^r`.
* `Stacks.EtaleCohomology.sheafEquivPointStalkIso` — the stalk at `g(t̄)` of a sheaf moved to
  Mathlib's site, read back on the bounded site.
* `Stacks.EtaleCohomology.padicLevelDirectImageStalkHom` — `(j_* ℱₙ)_s → (ℤ/ℓⁿ⁺¹)^r`.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.8, `H⁰_loc`)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.SmallEtale
open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] GeometricPoint.residueFieldAlgebra

section PadicStalk

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)

/-- **The stalk at `s̄` of the `n`-th `ℤ_ℓ`-level of `ℱ_ρ` is `(ℤ/ℓⁿ⁺¹ℤ)^r`**, for a path `p`
from `s̄` to `x̄`: the stalk of the underlying abelian sheaf is the finite `π₁(X, x̄)`-module
attached to it by the canonical equivalence of Tag 0DV5 (2), which is the level module. -/
def padicLevelStalkIso {s : GeometricPoint X.1}
    (p : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (n : ℕ) :
    (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) n).obj) ≅
      AddCommGrpCat.of (ULift.{u + 1} (Fin r → ZMod (ℓ ^ (n + 1)))) :=
  etaleStalkForget₂Iso B X.1 X.2 s ℤ_[ℓ] _ ≪≫
    (finiteLocallyConstantAbelianStalkIso B X p).app
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj
        (levelAbelian ρ hρ (n + 1))) ≪≫
    (ObjectProperty.ι _ ⋙ ContinuousGAddCommGrp.forget (EtaleFundamentalGroup X.1 x)).mapIso
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.app
        (levelAbelian ρ hρ (n + 1)))

/-- The identification of the stalk of a `ℤ_ℓ`-level, as the composite of its three steps. -/
theorem padicLevelStalkIso_hom_apply {s : GeometricPoint X.1}
    (p : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (n : ℕ)
    (z : (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) n).obj)) :
    (padicLevelStalkIso B X x ρ hρ p n).hom z =
      ConcreteCategory.hom
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.hom.app
          (levelAbelian ρ hρ (n + 1))).hom.hom.hom.hom
        (ConcreteCategory.hom ((finiteLocallyConstantAbelianStalkIso B X p).hom.app
          ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj
            (levelAbelian ρ hρ (n + 1))))
          (ConcreteCategory.hom (etaleStalkForget₂Iso B X.1 X.2 s ℤ_[ℓ]
            (LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) n)).hom z)) :=
  rfl

/-- **The maps of Tag 04FN on the stalks of the `ℤ_ℓ`-levels of `ℱ_ρ` are `ρ mod ℓⁿ⁺¹`.** -/
theorem padicLevelStalkIso_geometricPointStalkMap {s : GeometricPoint X.1}
    (p : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.asIso.hom = finiteEtaleFiberMap a) (n : ℕ)
    (y : (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) n).obj)) :
    ((padicLevelStalkIso B X x ρ hρ p n).hom
        ((forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).map
          ((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} ℤ_[ℓ])).app
            (LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) n).obj) y)).down =
      levelRepresentation ρ (n + 1) (etaleFundamentalGroupMulEquiv p σ)
        ((padicLevelStalkIso B X x ρ hρ p n).hom y).down := by
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  set L := levelAbelian ρ hρ (n + 1)
  set g := etaleFundamentalGroupMulEquiv p σ
  let G := LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x e ρ hρ) n
  let I1 := ConcreteCategory.hom (etaleStalkForget₂Iso B X.1 X.2 s ℤ_[ℓ] G).hom
  let m := ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).map
    ((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} ℤ_[ℓ])).app G.obj))
  let abM := ConcreteCategory.hom ((geometricPointStalkMap B X.1 X.2 a AddCommGrpCat.{u + 1}).app
    (e.inverse.obj L).obj.obj)
  let I2 := ConcreteCategory.hom ((finiteLocallyConstantAbelianStalkIso B X p).hom.app
    (e.inverse.obj L))
  let C := ConcreteCategory.hom (e.counitIso.hom.app L).hom.hom.hom.hom
  let ρ1 := ConcreteCategory.hom ((e.functor.obj (e.inverse.obj L)).obj.obj.obj.ρ g).asHom
  let ρL := ConcreteCategory.hom (L.obj.obj.obj.ρ g).asHom
  have s1 : I1 (m y) = abM (I1 y) := ConcreteCategory.congr_hom
    (geometricPointStalkMap_preservesColimitIso B X.1 X.2
      (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}) a G.obj) y
  have s2 : ∀ z, I2 (abM z) = ρ1 (I2 z) := ConcreteCategory.congr_hom
    (geometricPointStalkMap_finiteLocallyConstantAbelianStalkIso B X p a σ hσ (e.inverse.obj L))
  have s3 : ∀ w, C (ρ1 w) = ρL (C w) := ConcreteCategory.congr_hom
    ((e.counitIso.hom.app L).hom.hom.hom.comm g)
  change (C (I2 (I1 (m y)))).down = levelRepresentation ρ (n + 1) g (C (I2 (I1 y))).down
  rw [s1]
  exact (congrArg (fun z => (C z).down) (s2 (I1 y))).trans (congrArg ULift.down (s3 _))

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- On underlying abelian sheaves, the transition of the `ℤ_ℓ`-levels of `ℱ_ρ` is the image
under the canonical equivalence of reduction of level modules. -/
theorem sheafCompose_forget₂_map_padicTransition (n : ℕ) :
    (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1})).map
        (LAdicSheaf.padicTransition B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) n) =
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
        (levelAbelianReduction ρ hρ (n + 1))).hom := by
  ext U z
  rfl

set_option maxHeartbeats 1000000 in
-- the final `change` unfolds composites of stalk isomorphisms of the `ℤ_ℓ`-level sheaves
/-- **The transitions of the `ℤ_ℓ`-levels of `ℱ_ρ` are reduction on stalks.** -/
theorem padicLevelStalkIso_padicTransition {s : GeometricPoint X.1}
    (p : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (n : ℕ)
    (y : (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) (n + 1)).obj)) :
    ((padicLevelStalkIso B X x ρ hρ p n).hom
        ((forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).map
          ((etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} ℤ_[ℓ])).map
            ((sheafToPresheaf _ _).map (LAdicSheaf.padicTransition B X ℓ
              (representationLAdicSheaf B X x
                (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) n))) y)).down =
      levelReduction (n + 1) ((padicLevelStalkIso B X x ρ hρ p (n + 1)).hom y).down := by
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  let red := levelAbelianReduction ρ hρ (n + 1)
  let G : ℕ → Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} ℤ_[ℓ]) := fun k =>
    LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x e ρ hρ) k
  let I1 : ∀ k, _ := fun k =>
    ConcreteCategory.hom (etaleStalkForget₂Iso B X.1 X.2 s ℤ_[ℓ] (G k)).hom
  let I2 : ∀ k, _ := fun k => ConcreteCategory.hom
    ((finiteLocallyConstantAbelianStalkIso B X p).hom.app (e.inverse.obj (levelAbelian ρ hρ k)))
  let C : ∀ k, _ := fun k => ConcreteCategory.hom
    (e.counitIso.hom.app (levelAbelian ρ hρ k)).hom.hom.hom.hom
  let m := ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).map
    ((etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} ℤ_[ℓ])).map
      ((sheafToPresheaf _ _).map (LAdicSheaf.padicTransition B X ℓ
        (representationLAdicSheaf B X x e ρ hρ) n))))
  let ab := ConcreteCategory.hom ((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
    (e.inverse.map red).hom)
  have s1 : I1 n (m y) = ab (I1 (n + 1) y) := by
    have h := ConcreteCategory.congr_hom (etaleStalkForget₂Iso_hom_naturality B X.1 X.2 s ℤ_[ℓ]
      (LAdicSheaf.padicTransition B X ℓ (representationLAdicSheaf B X x e ρ hρ) n)) y
    rwa [sheafCompose_forget₂_map_padicTransition B X x ρ hρ n] at h
  have s2 := ConcreteCategory.congr_hom
    ((finiteLocallyConstantAbelianStalkIso B X p).hom.naturality (e.inverse.map red))
  have s3 := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.hom.hom.hom) (e.counitIso.hom.naturality red))
  change (C (n + 1) (I2 (n + 1) (I1 n (m y)))).down =
    levelReduction (n + 1) (C (n + 1 + 1) (I2 (n + 1 + 1) (I1 (n + 1) y))).down
  rw [s1]
  exact (congrArg (fun z => (C (n + 1) z).down) (s2 _)).trans (congrArg ULift.down (s3 _))

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- On underlying abelian sheaves, the morphism of `ℤ_ℓ`-levels of `ℱ_ρ` induced by an
intertwiner is the image under the canonical equivalence of the map of level modules. -/
theorem sheafCompose_forget₂_map_padicLevelMap (M : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hM : ∀ g, M * (ρ g).val = (ρ g).val * M) (n : ℕ) :
    (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1})).map
        (LAdicSheaf.padicLevelMap (representationLAdicSheafMap B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ M hM) n) =
      ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
        (levelAbelianMap hρ hρ M hM (n + 1))).hom := by
  ext U z
  rfl

/-- **The morphisms induced by an intertwiner are multiplication by the reduced matrix on the
stalks of the `ℤ_ℓ`-levels of `ℱ_ρ`.** -/
theorem padicLevelStalkIso_padicLevelMap {s : GeometricPoint X.1}
    (p : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (M : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (hM : ∀ g, M * (ρ g).val = (ρ g).val * M) (n : ℕ)
    (y : (forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B X.1 X.2 s (LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) n).obj)) :
    ((padicLevelStalkIso B X x ρ hρ p n).hom
        ((forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).map
          ((etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} ℤ_[ℓ])).map
            ((sheafToPresheaf _ _).map (LAdicSheaf.padicLevelMap
              (representationLAdicSheafMap B X x
                (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ M hM) n)))
          y)).down =
      (M.map (PadicInt.toZModPow (n + 1))) *ᵥ ((padicLevelStalkIso B X x ρ hρ p n).hom y).down := by
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  let φ := levelAbelianMap hρ hρ M hM (n + 1)
  let G := LAdicSheaf.padicLevel B X ℓ (representationLAdicSheaf B X x e ρ hρ) n
  let I1 := ConcreteCategory.hom (etaleStalkForget₂Iso B X.1 X.2 s ℤ_[ℓ] G).hom
  let I2 := ConcreteCategory.hom
    ((finiteLocallyConstantAbelianStalkIso B X p).hom.app
      (e.inverse.obj (levelAbelian ρ hρ (n + 1))))
  let C := ConcreteCategory.hom
    (e.counitIso.hom.app (levelAbelian ρ hρ (n + 1))).hom.hom.hom.hom
  let m := ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).map
    ((etaleStalkPresheafFunctor B X.1 X.2 s (ModuleCat.{u + 1} ℤ_[ℓ])).map
      ((sheafToPresheaf _ _).map (LAdicSheaf.padicLevelMap
        (representationLAdicSheafMap B X x e hρ hρ M hM) n))))
  let ab := ConcreteCategory.hom ((abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
    (e.inverse.map φ).hom)
  have s1 : I1 (m y) = ab (I1 y) := by
    have h := ConcreteCategory.congr_hom (etaleStalkForget₂Iso_hom_naturality B X.1 X.2 s ℤ_[ℓ]
      (LAdicSheaf.padicLevelMap (representationLAdicSheafMap B X x e hρ hρ M hM) n)) y
    rwa [sheafCompose_forget₂_map_padicLevelMap B X x ρ hρ M hM n] at h
  have s2 := ConcreteCategory.congr_hom
    ((finiteLocallyConstantAbelianStalkIso B X p).hom.naturality (e.inverse.map φ))
  have s3 := ConcreteCategory.congr_hom
    (congrArg (fun f => f.hom.hom.hom.hom) (e.counitIso.hom.naturality φ))
  rw [padicLevelStalkIso_hom_apply]
  refine (congrArg ULift.down (padicLevelStalkIso_hom_apply B X x ρ hρ p n _)).trans ?_
  refine (congrArg (fun z => (C (I2 z)).down) s1).trans ?_
  exact ((congrArg (fun z => (C z).down) (s2 _)).trans (congrArg ULift.down (s3 _))).trans
    (levelAbelianMap_apply hρ hρ M hM (n + 1) _)

end PadicStalk

section PointStalk

variable (B' : BigEtaleSite.{u}) (U : B'.Scheme) (K : Type u) [Field K]
  (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
  (t : GeometricPoint (Spec (.of K))) (R : Type) [Ring R]

/-- The stalk at `g(t̄)` of a sheaf of modules on the bounded site moved to Mathlib's site, read
back on the bounded site, is its stalk there (through the unit of the equivalence of sites). -/
def sheafEquivPointStalkIso (G : Sheaf (SmallEtale.topology B' U.1 U.2) (ModuleCat.{u + 1} R)) :
    (pointStalkAb B' U K hK g t R).obj
        ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).functor.obj G) ≅
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B' U.1 U.2 (t.map (B'.inclusion.map g)) G.obj) :=
  (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).mapIso
    ((etaleStalkPresheafFunctor B' U.1 U.2 (t.map (B'.inclusion.map g))
      (ModuleCat.{u + 1} R)).mapIso
      ((sheafToPresheaf _ _).mapIso
        ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).unitIso.app G).symm))

/-- `Stacks.EtaleCohomology.sheafEquivPointStalkIso` is natural in the sheaf. -/
theorem sheafEquivPointStalkIso_hom_naturality
    {G G' : Sheaf (SmallEtale.topology B' U.1 U.2) (ModuleCat.{u + 1} R)} (φ : G ⟶ G')
    (w : (pointStalkAb B' U K hK g t R).obj
      ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).functor.obj G)) :
    ConcreteCategory.hom (sheafEquivPointStalkIso B' U K hK g t R G').hom
        (ConcreteCategory.hom ((pointStalkAb B' U K hK g t R).map
          ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).functor.map φ)) w) =
      ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((etaleStalkPresheafFunctor B' U.1 U.2 (t.map (B'.inclusion.map g))
            (ModuleCat.{u + 1} R)).map ((sheafToPresheaf _ _).map φ)))
        (ConcreteCategory.hom (sheafEquivPointStalkIso B' U K hK g t R G).hom w) := by
  have h := (SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).unitIso.inv.naturality φ
  have h' := congrArg (fun f => (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
    ((etaleStalkPresheafFunctor B' U.1 U.2 (t.map (B'.inclusion.map g))
      (ModuleCat.{u + 1} R)).map ((sheafToPresheaf _ _).map f))) h
  simp only [Functor.map_comp] at h'
  exact ConcreteCategory.congr_hom h' w

/-- `Stacks.EtaleCohomology.sheafEquivPointStalkIso` intertwines the maps of Tag 04FN. -/
theorem sheafEquivPointStalkIso_hom_geometricPointStalkMap
    (a : GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g)))
    (G : Sheaf (SmallEtale.topology B' U.1 U.2) (ModuleCat.{u + 1} R))
    (w : (pointStalkAb B' U K hK g t R).obj
      ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).functor.obj G)) :
    ConcreteCategory.hom (sheafEquivPointStalkIso B' U K hK g t R G).hom
        (ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((geometricPointStalkMap B' U.1 U.2 a (ModuleCat.{u + 1} R)).app
            ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).inverse.obj
              ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).functor.obj G)).obj)) w) =
      ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((geometricPointStalkMap B' U.1 U.2 a (ModuleCat.{u + 1} R)).app G.obj))
        (ConcreteCategory.hom (sheafEquivPointStalkIso B' U K hK g t R G).hom w) :=
  forget₂_etaleStalkPresheafFunctor_map_geometricPointStalkMap B' U.1 U.2 a R
    ((sheafToPresheaf _ _).map
      ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).unitIso.app G).inv) w

end PointStalk

section Generic

/-- The additive map `Stacks.EtaleCohomology.natTransAddHom` attached to a natural map of
underlying sets is natural. -/
theorem natTransAddHom_naturality {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] (F G : C ⥤ AddCommGrpCat.{u + 1}) [F.Additive] [G.Additive]
    (a : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) {X Y : C} (φ : X ⟶ Y)
    (z : F.obj X) :
    ConcreteCategory.hom (natTransAddHom F G a Y) (ConcreteCategory.hom (F.map φ) z) =
      ConcreteCategory.hom (G.map φ) (ConcreteCategory.hom (natTransAddHom F G a X) z) :=
  ConcreteCategory.congr_hom (a.naturality φ) z

end Generic

section Boundary

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (B' : BigEtaleSite.{u}) (U : B'.Scheme) (j : U.1 ⟶ S)
  (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
  (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
  (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
  (t : GeometricPoint (Spec (.of K))) (R : Type) [Ring R] [QuasiCompact j] [QuasiSeparated j]

/-- The specialization map of `j_*` at a boundary point is natural in the sheaf. -/
theorem directImageStalkToStalkHom_naturality
    {M M' : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R)} (φ : M ⟶ M')
    (z : (directImageStalkAb S s B' U j R).obj M) :
    ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t R M')
        (ConcreteCategory.hom ((directImageStalkAb S s B' U j R).map φ) z) =
      ConcreteCategory.hom ((pointStalkAb B' U K hK g t R).map φ)
        (ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t R M)
          z) :=
  natTransAddHom_naturality _ _ _ φ z

omit [QuasiCompact j] [QuasiSeparated j] in
/-- The map of stalks of `j_*` induced by a morphism of sheaves of modules, on the module-valued
stalk, is the map of `Stacks.EtaleCohomology.directImageStalkAb`. -/
theorem sheafFiber_map_etaleModuleDirectImage_hom_apply
    {M M' : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R)} (φ : M ⟶ M')
    (w : ((pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} R)).obj
      ((etaleModuleDirectImage.{u, 0} R j).obj M)) :
    (((pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} R)).map
        ((etaleModuleDirectImage.{u, 0} R j).map φ)).hom w =
      ConcreteCategory.hom ((directImageStalkAb S s B' U j R).map φ) w :=
  rfl

omit [QuasiCompact j] [QuasiSeparated j] in
/-- The map of stalks of `j_*` induced by an endomorphism of the geometric point, on the
module-valued stalk, is its image under the forgetful functor. -/
theorem sheafFiber_app_etaleModuleDirectImage_hom_apply
    (a : GeometricPoint.Hom s s) (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R))
    (w : ((pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} R)).obj
      ((etaleModuleDirectImage.{u, 0} R j).obj M)) :
    ((pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
        ((etaleModuleDirectImage.{u, 0} R j).obj M)).hom w =
      ConcreteCategory.hom (X := (directImageStalkAb S s B' U j R).obj M)
        (Y := (directImageStalkAb S s B' U j R).obj M)
        ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
            (((smallEtaleBaseChange j).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
              (smallEtaleTopology S) (smallEtaleTopology U.1)).obj M))) w :=
  rfl

end Boundary

section PadicBoundary

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (B' : BigEtaleSite.{u}) (U : B'.Scheme) [ConnectedSpace U.1] (x : GeometricPoint U.1)
  (j : U.1 ⟶ S) [QuasiCompact j] [QuasiSeparated j]
  (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
  (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
  (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
  (t : GeometricPoint (Spec (.of K)))
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B'.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B' g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B' S.1 S.property)
      (SmallEtale.topology B' T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B'.Scheme) (V : SmallEtale B' T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B' T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B' U.1 U.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian U.1]
  (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
  (p : finiteEtaleFiberFunctor (X := U.1) (t.map (B'.inclusion.map g)) ≅
    finiteEtaleFiberFunctor x)

/-- The `n`-th `ℤ_ℓ`-level of `ℱ_ρ`, read on Mathlib's small étale site. -/
abbrev padicLevelMathlib (n : ℕ) : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} ℤ_[ℓ]) :=
  (SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.obj
    (LAdicSheaf.padicLevel B' U ℓ (representationLAdicSheaf B' U x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B' U x) ρ hρ) n)

/-- The transition of the `ℤ_ℓ`-levels of `ℱ_ρ`, read on Mathlib's small étale site. -/
abbrev padicLevelMathlibTransition (n : ℕ) :
    padicLevelMathlib B' U x ρ hρ (n + 1) ⟶ padicLevelMathlib B' U x ρ hρ n :=
  (SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
    (LAdicSheaf.padicTransition B' U ℓ (representationLAdicSheaf B' U x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B' U x) ρ hρ) n)

/-- The morphism of `ℤ_ℓ`-levels of `ℱ_ρ` induced by an intertwiner, read on Mathlib's small étale
site. -/
abbrev padicLevelMathlibMap (M : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hM : ∀ g, M * (ρ g).val = (ρ g).val * M) (n : ℕ) :
    padicLevelMathlib B' U x ρ hρ n ⟶ padicLevelMathlib B' U x ρ hρ n :=
  (SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
    (LAdicSheaf.padicLevelMap (representationLAdicSheafMap B' U x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B' U x) hρ hρ M hM) n)

/-- The identification of the stalk at `g(t̄)` of the `n`-th `ℤ_ℓ`-level of `ℱ_ρ` with
`(ℤ/ℓⁿ⁺¹)^r` along the path `p`. -/
def padicLevelPointStalkTrivialization (n : ℕ) :
    (pointStalkAb B' U K hK g t ℤ_[ℓ]).obj (padicLevelMathlib B' U x ρ hρ n) ≅
      AddCommGrpCat.of (ULift.{u + 1} (Fin r → ZMod (ℓ ^ (n + 1)))) :=
  sheafEquivPointStalkIso B' U K hK g t ℤ_[ℓ] _ ≪≫ padicLevelStalkIso B' U x ρ hρ p n

/-- **`H⁰_loc` of the `n`-th `ℤ_ℓ`-level of `ℱ_ρ` at a boundary point**: the specialization map
`(j_* ℱₙ)_s → (ℱₙ)_{g(t̄)}` followed by the trivialization `(ℱₙ)_{g(t̄)} ≅ (ℤ/ℓⁿ⁺¹)^r` along
`p`. -/
def padicLevelDirectImageStalkHom (n : ℕ) :
    (directImageStalkAb S s B' U j ℤ_[ℓ]).obj (padicLevelMathlib B' U x ρ hρ n) ⟶
      AddCommGrpCat.of (ULift.{u + 1} (Fin r → ZMod (ℓ ^ (n + 1)))) :=
  directImageStalkToStalkHom B S hS s B' U j K e hK g hg t ℤ_[ℓ] _ ≫
    (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n).hom

/-- The map `padicLevelDirectImageStalkHom` from `(j_* ℱₙ)_s` to `(ℤ/ℓⁿ⁺¹)^r` is injective. -/
theorem padicLevelDirectImageStalkHom_injective (n : ℕ) :
    Function.Injective (ConcreteCategory.hom
      (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n)) := by
  intro y y' h
  refine directImageStalkToStalkHom_injective B S hS s B' U j K e hK g hg t ℤ_[ℓ] _ ?_
  simpa only [padicLevelDirectImageStalkHom, ConcreteCategory.comp_apply,
    Iso.hom_inv_id_apply] using congrArg (ConcreteCategory.hom
      (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n).inv) h

/-- The trivialization of the stalk at `g(t̄)` intertwines the maps of Tag 04FN with `ρ`. -/
theorem padicLevelPointStalkTrivialization_geometricPointStalkMap
    (a : GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g)))
    (σ : EtaleFundamentalGroup U.1 (t.map (B'.inclusion.map g)))
    (hσ : σ.asIso.hom = finiteEtaleFiberMap a) (n : ℕ)
    (w : (pointStalkAb B' U K hK g t ℤ_[ℓ]).obj (padicLevelMathlib B' U x ρ hρ n)) :
    (ConcreteCategory.hom (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n).hom
        (ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).map
          ((geometricPointStalkMap B' U.1 U.2 a (ModuleCat.{u + 1} ℤ_[ℓ])).app
            ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.obj
              (padicLevelMathlib B' U x ρ hρ n)).obj)) w)).down =
      levelRepresentation ρ (n + 1) (etaleFundamentalGroupMulEquiv p σ)
        (ConcreteCategory.hom (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n).hom
          w).down := by
  have h1 := sheafEquivPointStalkIso_hom_geometricPointStalkMap B' U K hK g t ℤ_[ℓ] a
    (LAdicSheaf.padicLevel B' U ℓ (representationLAdicSheaf B' U x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B' U x) ρ hρ) n) w
  have h2 := padicLevelStalkIso_geometricPointStalkMap B' U x ρ hρ p a σ hσ n
    (ConcreteCategory.hom (sheafEquivPointStalkIso B' U K hK g t ℤ_[ℓ] _).hom w)
  refine Eq.trans ?_ h2
  exact congrArg (fun y => (ConcreteCategory.hom (padicLevelStalkIso B' U x ρ hρ p n).hom y).down)
    h1

/-- The trivialization of the stalk at `g(t̄)` turns the transitions into reduction. -/
theorem padicLevelPointStalkTrivialization_padicTransition (n : ℕ)
    (z : (pointStalkAb B' U K hK g t ℤ_[ℓ]).obj (padicLevelMathlib B' U x ρ hρ (n + 1))) :
    (ConcreteCategory.hom (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n).hom
        (ConcreteCategory.hom ((pointStalkAb B' U K hK g t ℤ_[ℓ]).map
          (padicLevelMathlibTransition B' U x ρ hρ n)) z)).down =
      levelReduction (n + 1) (ConcreteCategory.hom
        (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p (n + 1)).hom z).down := by
  have h1 := sheafEquivPointStalkIso_hom_naturality B' U K hK g t ℤ_[ℓ]
    (LAdicSheaf.padicTransition B' U ℓ (representationLAdicSheaf B' U x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B' U x) ρ hρ) n) z
  have h2 := padicLevelStalkIso_padicTransition B' U x ρ hρ p n
    (ConcreteCategory.hom (sheafEquivPointStalkIso B' U K hK g t ℤ_[ℓ] _).hom z)
  refine Eq.trans ?_ h2
  exact congrArg (fun y => (ConcreteCategory.hom (padicLevelStalkIso B' U x ρ hρ p n).hom y).down)
    h1

/-- The trivialization of the stalk at `g(t̄)` turns the maps induced by an intertwiner into
multiplication by the reduced matrix. -/
theorem padicLevelPointStalkTrivialization_padicLevelMap (M : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hM : ∀ g, M * (ρ g).val = (ρ g).val * M) (n : ℕ)
    (z : (pointStalkAb B' U K hK g t ℤ_[ℓ]).obj (padicLevelMathlib B' U x ρ hρ n)) :
    (ConcreteCategory.hom (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n).hom
        (ConcreteCategory.hom ((pointStalkAb B' U K hK g t ℤ_[ℓ]).map
          (padicLevelMathlibMap B' U x ρ hρ M hM n)) z)).down =
      (M.map (PadicInt.toZModPow (n + 1))) *ᵥ (ConcreteCategory.hom
        (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n).hom z).down := by
  have h1 := sheafEquivPointStalkIso_hom_naturality B' U K hK g t ℤ_[ℓ]
    (LAdicSheaf.padicLevelMap (representationLAdicSheafMap B' U x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B' U x) hρ hρ M hM) n) z
  have h2 := padicLevelStalkIso_padicLevelMap B' U x ρ hρ p M hM n
    (ConcreteCategory.hom (sheafEquivPointStalkIso B' U K hK g t ℤ_[ℓ] _).hom z)
  refine Eq.trans ?_ h2
  exact congrArg (fun y => (ConcreteCategory.hom (padicLevelStalkIso B' U x ρ hρ p n).hom y).down)
    h1

/-- **Frobenius on `H⁰_loc` of the `ℤ_ℓ`-levels of `ℱ_ρ`**: the map of stalks of `j_* ℱₙ` induced
by an endomorphism `a` of `s` is `ρ mod ℓⁿ⁺¹` of the transport along `p` of any `σ` acting on the
fibre functor as the lift `ã` to `t̄` of the endomorphism `id ×_S β_a` of
`U ×_S Spec 𝒪^{sh} ≅ Spec K`. -/
theorem padicLevelDirectImageStalkHom_pointSmallEtaleHom (a : GeometricPoint.Hom s s)
    (ã : t.source ⟶ t.source)
    (hã : ã ≫ t.hom = t.hom ≫ e.inv ≫ baseChangeStrictHenselizationEndomorphism B S hS s B' U j a ≫
      e.hom)
    (hãg : ã ≫ t.hom ≫ B'.inclusion.map g = t.hom ≫ B'.inclusion.map g)
    (σ : EtaleFundamentalGroup U.1 (t.map (B'.inclusion.map g)))
    (hσ : σ.asIso.hom = finiteEtaleFiberMap
      (⟨ã, hãg⟩ : GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g))))
    (n : ℕ) (w : (directImageStalkAb S s B' U j ℤ_[ℓ]).obj (padicLevelMathlib B' U x ρ hρ n)) :
    (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n)
        (ConcreteCategory.hom (X := (directImageStalkAb S s B' U j ℤ_[ℓ]).obj
            (padicLevelMathlib B' U x ρ hρ n))
          (Y := (directImageStalkAb S s B' U j ℤ_[ℓ]).obj (padicLevelMathlib B' U x ρ hρ n))
          ((forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).map
            ((pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
              (((smallEtaleBaseChange j).sheafPushforwardContinuous (ModuleCat.{u + 1} ℤ_[ℓ])
                (smallEtaleTopology S) (smallEtaleTopology U.1)).obj
                (padicLevelMathlib B' U x ρ hρ n)))) w)).down =
      levelRepresentation ρ (n + 1) (etaleFundamentalGroupMulEquiv p σ)
        (ConcreteCategory.hom
          (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n) w).down := by
  have h1 := directImageStalkToStalkHom_pointSmallEtaleHom_geometricPointStalkMap B S hS s B' U j K
    e hK g hg t ℤ_[ℓ] a ã hã hãg (padicLevelMathlib B' U x ρ hρ n) w
  have h2 := padicLevelPointStalkTrivialization_geometricPointStalkMap B' U x K hK g t ρ hρ p
    ⟨ã, hãg⟩ σ hσ n
    (ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t ℤ_[ℓ]
      (padicLevelMathlib B' U x ρ hρ n)) w)
  refine Eq.trans ?_ h2
  exact congrArg (fun y => (ConcreteCategory.hom
    (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n).hom y).down) h1

/-- **The transitions on `H⁰_loc` of the `ℤ_ℓ`-levels of `ℱ_ρ` are reduction.** -/
theorem padicLevelDirectImageStalkHom_padicTransition (n : ℕ)
    (w : (directImageStalkAb S s B' U j ℤ_[ℓ]).obj (padicLevelMathlib B' U x ρ hρ (n + 1))) :
    (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n)
        (ConcreteCategory.hom ((directImageStalkAb S s B' U j ℤ_[ℓ]).map
          (padicLevelMathlibTransition B' U x ρ hρ n)) w)).down =
      levelReduction (n + 1) (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p (n + 1)) w).down := by
  have h1 := directImageStalkToStalkHom_naturality B S hS s B' U j K e hK g hg t ℤ_[ℓ]
    (padicLevelMathlibTransition B' U x ρ hρ n) w
  have h2 := padicLevelPointStalkTrivialization_padicTransition B' U x K hK g t ρ hρ p n
    (ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t ℤ_[ℓ]
      (padicLevelMathlib B' U x ρ hρ (n + 1))) w)
  refine Eq.trans ?_ h2
  exact congrArg (fun y => (ConcreteCategory.hom
    (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n).hom y).down) h1

/-- **The morphisms induced by an intertwiner on `H⁰_loc` of the `ℤ_ℓ`-levels of `ℱ_ρ` are
multiplication by the reduced matrix.** -/
theorem padicLevelDirectImageStalkHom_padicLevelMap (M : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hM : ∀ g, M * (ρ g).val = (ρ g).val * M) (n : ℕ)
    (w : (directImageStalkAb S s B' U j ℤ_[ℓ]).obj (padicLevelMathlib B' U x ρ hρ n)) :
    (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n)
        (ConcreteCategory.hom ((directImageStalkAb S s B' U j ℤ_[ℓ]).map
          (padicLevelMathlibMap B' U x ρ hρ M hM n)) w)).down =
      (M.map (PadicInt.toZModPow (n + 1))) *ᵥ (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n) w).down := by
  have h1 := directImageStalkToStalkHom_naturality B S hS s B' U j K e hK g hg t ℤ_[ℓ]
    (padicLevelMathlibMap B' U x ρ hρ M hM n) w
  have h2 := padicLevelPointStalkTrivialization_padicLevelMap B' U x K hK g t ρ hρ p M hM n
    (ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t ℤ_[ℓ]
      (padicLevelMathlib B' U x ρ hρ n)) w)
  refine Eq.trans ?_ h2
  exact congrArg (fun y => (ConcreteCategory.hom
    (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n).hom y).down) h1

/-- **`H⁰_loc` of the `n`-th `ℤ_ℓ`-level of `ℱ_ρ` at a boundary point is the module of inertia
invariants**: for an algebraic geometric point `t̄` of `Spec K`, a vector of `(ℤ/ℓⁿ⁺¹)^r` comes
from `(j_* ℱₙ)_s` exactly when it is fixed by `ρ mod ℓⁿ⁺¹` of the image in `π₁(U, x̄)`, along
`p`, of every automorphism of `t̄` over `K`. -/
theorem mem_range_padicLevelDirectImageStalkHom_iff (ht : t.IsAlgebraic) (n : ℕ)
    (v : ULift.{u + 1} (Fin r → ZMod (ℓ ^ (n + 1)))) :
    v ∈ Set.range (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n)) ↔
      ∀ (σ : GeometricPoint.absoluteGaloisGroup t)
        (τ : Gal(t.residueField / (Spec (.of K)).residueField (t.hom default)))
        (_ : ∀ a : GeometricPoint.separableClosure t,
          (σ a : t.residueField) = τ (a : t.residueField))
        (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
        (hαt : α.hom ≫ t.hom = t.hom),
        levelRepresentation ρ (n + 1)
          (etaleFundamentalGroupMulEquiv p
            (GeometricPoint.sourceAutElement (S := U.1) (t.map (B'.inclusion.map g)) α (by
              change α.hom ≫ t.hom ≫ _ = t.hom ≫ _
              rw [← Category.assoc, hαt]))) v.down = v.down := by
  rw [padicLevelDirectImageStalkHom, mem_range_comp_iso_hom_iff,
    mem_range_directImageStalkToStalkHom_iff B S hS s B' U j K e hK g hg t ℤ_[ℓ] ht]
  refine forall_congr' fun σ => forall_congr' fun τ => forall_congr' fun hτ =>
    forall_congr' fun α => forall_congr' fun hα => forall_congr' fun hαt => ?_
  refine (iso_inv_apply_fixed_iff
    (padicLevelPointStalkTrivialization B' U x K hK g t ρ hρ p n)
    (ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} ℤ_[ℓ]) AddCommGrpCat.{u + 1}).map
      ((geometricPointStalkMap B' U.1 U.2
        ((⟨α.hom, hαt⟩ : GeometricPoint.Hom t t).mapHom (B'.inclusion.map g))
          (ModuleCat.{u + 1} ℤ_[ℓ])).app
      ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} ℤ_[ℓ])).inverse.obj
        (padicLevelMathlib B' U x ρ hρ n)).obj)))
    (fun w => ULift.up (levelRepresentation ρ (n + 1) (etaleFundamentalGroupMulEquiv p
      (GeometricPoint.sourceAutElement (S := U.1) (t.map (B'.inclusion.map g)) α (by
        change α.hom ≫ t.hom ≫ _ = t.hom ≫ _
        rw [← Category.assoc, hαt]))) w.down))
    (fun w => ULift.ext
      (padicLevelPointStalkTrivialization_geometricPointStalkMap B' U x K hK g t ρ hρ p
        _ _ (GeometricPoint.sourceAutElement_hom_eq_finiteEtaleFiberMap (S := U.1)
          (t.map (B'.inclusion.map g)) α _
          ((⟨α.hom, hαt⟩ : GeometricPoint.Hom t t).mapHom (B'.inclusion.map g)) rfl) n w)) v).trans
    ⟨fun h => congrArg ULift.down h, fun h => ULift.ext h⟩

/-! ### The same statements on the module-valued stalk of `j_*` -/

/-- `Stacks.EtaleCohomology.padicLevelDirectImageStalkHom_padicTransition` on the stalk of
`j_* ℱₙ` as a `ℤ_ℓ`-module. -/
theorem padicLevelDirectImageStalkHom_sheafFiber_padicTransition (n : ℕ)
    (w : ((pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).obj
      ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).obj (padicLevelMathlib B' U x ρ hρ (n + 1)))) :
    (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n)
        (((pointSmallEtale s.hom).sheafFiber.map ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).map
          (padicLevelMathlibTransition B' U x ρ hρ n))).hom w)).down =
      levelReduction (n + 1) (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p (n + 1)) w).down := by
  rw [sheafFiber_map_etaleModuleDirectImage_hom_apply]
  exact padicLevelDirectImageStalkHom_padicTransition B S hS s B' U x j K e hK g hg t ρ hρ p n w

/-- `Stacks.EtaleCohomology.padicLevelDirectImageStalkHom_padicLevelMap` on the stalk of
`j_* ℱₙ` as a `ℤ_ℓ`-module. -/
theorem padicLevelDirectImageStalkHom_sheafFiber_padicLevelMap (M : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hM : ∀ g, M * (ρ g).val = (ρ g).val * M) (n : ℕ)
    (w : ((pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).obj
      ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).obj (padicLevelMathlib B' U x ρ hρ n))) :
    (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n)
        (((pointSmallEtale s.hom).sheafFiber.map ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).map
          (padicLevelMathlibMap B' U x ρ hρ M hM n))).hom w)).down =
      (M.map (PadicInt.toZModPow (n + 1))) *ᵥ (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n) w).down := by
  rw [sheafFiber_map_etaleModuleDirectImage_hom_apply]
  exact padicLevelDirectImageStalkHom_padicLevelMap B S hS s B' U x j K e hK g hg t ρ hρ p M hM n w

/-- `Stacks.EtaleCohomology.padicLevelDirectImageStalkHom_pointSmallEtaleHom` on the stalk of
`j_* ℱₙ` as a `ℤ_ℓ`-module. -/
theorem padicLevelDirectImageStalkHom_sheafFiber_pointSmallEtaleHom (a : GeometricPoint.Hom s s)
    (ã : t.source ⟶ t.source)
    (hã : ã ≫ t.hom = t.hom ≫ e.inv ≫ baseChangeStrictHenselizationEndomorphism B S hS s B' U j a ≫
      e.hom)
    (hãg : ã ≫ t.hom ≫ B'.inclusion.map g = t.hom ≫ B'.inclusion.map g)
    (σ : EtaleFundamentalGroup U.1 (t.map (B'.inclusion.map g)))
    (hσ : σ.asIso.hom = finiteEtaleFiberMap
      (⟨ã, hãg⟩ : GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g))))
    (n : ℕ) (w : ((pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).obj
      ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).obj (padicLevelMathlib B' U x ρ hρ n))) :
    (ConcreteCategory.hom
        (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n)
        (((pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
          ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).obj (padicLevelMathlib B' U x ρ hρ n))).hom
          w)).down =
      levelRepresentation ρ (n + 1) (etaleFundamentalGroupMulEquiv p σ)
        (ConcreteCategory.hom
          (padicLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p n) w).down := by
  rw [sheafFiber_app_etaleModuleDirectImage_hom_apply]
  exact padicLevelDirectImageStalkHom_pointSmallEtaleHom B S hS s B' U x j K e hK g hg t ρ hρ p a
    ã hã hãg σ hσ n w

end PadicBoundary

end Stacks.EtaleCohomology

end
