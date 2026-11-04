module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdStalk
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Exactness

/-!
# The Euler sequence of projective space splits on every stalk

Let `R` be a commutative ring, grade `R[T₀, …, Tₙ]` by total degree and write `X = P^n_R`. The
Euler sequence

`0 ⟶ Ω_{X/R} ⟶ 𝒪_X(-1)^{⊕ (n+1)} ⟶ 𝒪_X ⟶ 0`

is short exact but does not split globally. It splits at every point `x`: the stalk of the third
term is the stalk of the structure sheaf, free of rank one over itself, so the stalk of the
second arrow has a section. More generally, a short exact sequence of sheaves of modules whose
third term is the unit sheaf of modules has split stalk complexes.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.unitPresheafStalkCommEquiv` and
  `Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv`: the stalk of the unit sheaf of
  modules is the stalk of the sheaf of rings, linearly over that stalk.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkUnitLift`: a germ of the middle term carried
  by the stalk of the second arrow to the generator of the stalk of the unit sheaf.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkSplittingOfShortExactUnit`: the splitting of
  the stalk complex of a short exact sequence whose third term is the unit sheaf of modules.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.prodEquivOfStalkSplitting`: a splitting of the
  stalk complex identifies the stalk of the middle term with the product of the stalks of the
  outer terms.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkSplitting`: the Euler sequence of
  projective space splits on the stalk at every point.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.eulerStalkProdEquiv`: the stalk of
  `𝒪_X(-1)^{⊕ (n+1)}` is the product of the stalks of `Ω_{X/R}` and of `𝒪_X`.

## Main results

* `Stacks.AlgebraicGeometry.ProjEulerSequence.shortExact_map_stalkFunctor`: the complex of stalks
  of a short exact sequence of sheaves of modules is short exact.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.stalkMapL_stalkUnitLift`: the stalk of the second
  arrow carries the chosen lift to the generator.

## Implementation notes

Two stalks of the sheaf of rings are in play: the `RingCat`-valued one, over which the stalk
functor on sheaves of modules is linear, and the `CommRingCat`-valued one, over which the stalk
of a presheaf of modules carries Mathlib's module structure. `stalkCommLinearOfRingLinear` and
`stalkRingLinearOfCommLinear` change the ring a linear map of stalks is recorded over.

The sheaf of rings underlying a sheaf of commutative rings is spelled `ringSheafOfComm`, as
`sheafCompose` of the forgetful functor: at the `CategoryTheory.Sheaf.toRingCat` spelling, instance
search for `Functor.PreservesZeroMorphisms` of the stalk functor fails.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Changing the ring the linearity of a stalk map is recorded over -/

section Transfer

variable {X : TopCat.{u}} {Oc : TopCat.Presheaf CommRingCat.{u} X} (y : X)
  {M N : PresheafOfModules.{u} (Oc ⋙ forget₂ CommRingCat.{u} RingCat.{u})}

/-- A map of stalks which is linear over the `RingCat`-valued stalk of the sheaf of rings is
linear over the `CommRingCat`-valued one: the two actions agree through
`SemilinearStalk.commStalkRingEquiv`. -/
def stalkCommLinearOfRingLinear
    (φ : ToType (TopCat.Presheaf.stalk M.presheaf y)
      →ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Oc ⋙ forget₂ CommRingCat.{u} RingCat.{u}) y)]
      ToType (TopCat.Presheaf.stalk N.presheaf y)) :
    ToType (TopCat.Presheaf.stalk M.presheaf y)
      →ₗ[ToType (TopCat.Presheaf.stalk Oc y)]
      ToType (TopCat.Presheaf.stalk N.presheaf y) where
  toFun := φ
  map_add' := φ.map_add
  map_smul' c m := by
    have hM : c • m = (SemilinearStalk.commStalkRingEquiv Oc y).symm c • m := by
      rw [← SemilinearStalk.comm_smul_eq Oc y M
        ((SemilinearStalk.commStalkRingEquiv Oc y).symm c) m, RingEquiv.apply_symm_apply]
    have hN : (SemilinearStalk.commStalkRingEquiv Oc y).symm c • φ m = c • φ m := by
      rw [← SemilinearStalk.comm_smul_eq Oc y N
        ((SemilinearStalk.commStalkRingEquiv Oc y).symm c) (φ m), RingEquiv.apply_symm_apply]
    change φ (c • m) = c • φ m
    rw [hM, φ.map_smul, hN]

/-- A map of stalks which is linear over the `CommRingCat`-valued stalk of the sheaf of rings is
linear over the `RingCat`-valued one. -/
def stalkRingLinearOfCommLinear
    (φ : ToType (TopCat.Presheaf.stalk M.presheaf y)
      →ₗ[ToType (TopCat.Presheaf.stalk Oc y)]
      ToType (TopCat.Presheaf.stalk N.presheaf y)) :
    ToType (TopCat.Presheaf.stalk M.presheaf y)
      →ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Oc ⋙ forget₂ CommRingCat.{u} RingCat.{u}) y)]
      ToType (TopCat.Presheaf.stalk N.presheaf y) where
  toFun := φ
  map_add' := φ.map_add
  map_smul' t m := by
    change φ (t • m) = t • φ m
    rw [← SemilinearStalk.comm_smul_eq Oc y M t m, φ.map_smul,
      SemilinearStalk.comm_smul_eq Oc y N t (φ m)]

end Transfer

/-! ### The stalk of the unit sheaf of modules -/

section UnitStalk

variable {X : TopCat.{u}} (Ou : TopCat.Presheaf CommRingCat.{u} X) (z : X)

/-- The stalk of the unit presheaf of modules is the stalk of the presheaf of rings, linearly over
the `CommRingCat`-valued stalk. -/
def unitPresheafStalkCommEquiv :
    ToType (TopCat.Presheaf.stalk
        (PresheafOfModules.unit (Ou ⋙ forget₂ CommRingCat.{u} RingCat.{u})).presheaf z)
      ≃ₗ[ToType (TopCat.Presheaf.stalk Ou z)] ToType (TopCat.Presheaf.stalk Ou z) where
  toFun m := SemilinearStalk.commStalkRingEquiv Ou z
    (LocallyFreeRank.unitStalkLEquiv (Ou ⋙ forget₂ CommRingCat.{u} RingCat.{u}) z m)
  invFun c := (LocallyFreeRank.unitStalkLEquiv (Ou ⋙ forget₂ CommRingCat.{u} RingCat.{u}) z).symm
    ((SemilinearStalk.commStalkRingEquiv Ou z).symm c)
  map_add' a b := by rw [map_add, map_add]
  map_smul' c m := by
    have hM : c • m = (SemilinearStalk.commStalkRingEquiv Ou z).symm c • m := by
      rw [← SemilinearStalk.comm_smul_eq Ou z
        (PresheafOfModules.unit (Ou ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
        ((SemilinearStalk.commStalkRingEquiv Ou z).symm c) m, RingEquiv.apply_symm_apply]
    change SemilinearStalk.commStalkRingEquiv Ou z
        (LocallyFreeRank.unitStalkLEquiv (Ou ⋙ forget₂ CommRingCat.{u} RingCat.{u}) z (c • m)) =
      c • SemilinearStalk.commStalkRingEquiv Ou z
        (LocallyFreeRank.unitStalkLEquiv (Ou ⋙ forget₂ CommRingCat.{u} RingCat.{u}) z m)
    rw [hM, map_smul, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, smul_eq_mul]
  left_inv m := by
    change (LocallyFreeRank.unitStalkLEquiv (Ou ⋙ forget₂ CommRingCat.{u} RingCat.{u}) z).symm
        ((SemilinearStalk.commStalkRingEquiv Ou z).symm
          (SemilinearStalk.commStalkRingEquiv Ou z
            (LocallyFreeRank.unitStalkLEquiv
              (Ou ⋙ forget₂ CommRingCat.{u} RingCat.{u}) z m))) = m
    rw [RingEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  right_inv c := by
    change SemilinearStalk.commStalkRingEquiv Ou z
        (LocallyFreeRank.unitStalkLEquiv (Ou ⋙ forget₂ CommRingCat.{u} RingCat.{u}) z
          ((LocallyFreeRank.unitStalkLEquiv (Ou ⋙ forget₂ CommRingCat.{u} RingCat.{u}) z).symm
            ((SemilinearStalk.commStalkRingEquiv Ou z).symm c))) = c
    rw [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end UnitStalk

/-! ### Splitting the stalk complex of a short exact sequence onto the unit sheaf -/

section Split

variable {X : TopCat.{u}}

/-- The sheaf of rings underlying a sheaf of commutative rings, in the spelling
`Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf` uses: `sheafCompose` of the forgetful
functor. -/
abbrev ringSheafOfComm (Oc : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}) :
    Sheaf (Opens.grothendieckTopology ↥X) RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology ↥X) (forget₂ CommRingCat.{u} RingCat.{u})).obj Oc

variable (Oc : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u})

/-- The stalk of the unit sheaf of modules is the stalk of the sheaf of rings. -/
def unitStalkCommEquiv (y : ↥X) :
    ToType (TopCat.Presheaf.stalk (SheafOfModules.unit (ringSheafOfComm Oc)).val.presheaf y)
      ≃ₗ[ToType (TopCat.Presheaf.stalk Oc.obj y)]
      ToType (TopCat.Presheaf.stalk Oc.obj y) :=
  unitPresheafStalkCommEquiv Oc.obj y

variable {F H G : SheafOfModules.{u} (ringSheafOfComm Oc)}

/-- The complex of stalks of a short exact sequence of sheaves of modules is short exact. -/
theorem shortExact_map_stalkFunctor {f : F ⟶ H} {g : H ⟶ G} (hfg : f ≫ g = 0)
    (hSE : (ShortComplex.mk f g hfg).ShortExact) (y : ↥X) :
    ((ShortComplex.mk f g hfg).map
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (ringSheafOfComm Oc) y)).ShortExact :=
  (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact
    (ShortComplex.mk f g hfg)).mp hSE y

/-- A germ of `H` at `y` carried by the stalk of `g` to the generator of the stalk of the unit
sheaf of modules. -/
def stalkUnitLift {f : F ⟶ H} {g : H ⟶ SheafOfModules.unit (ringSheafOfComm Oc)}
    (hfg : f ≫ g = 0) (hSE : (ShortComplex.mk f g hfg).ShortExact) (y : ↥X) :
    ToType (TopCat.Presheaf.stalk H.val.presheaf y) :=
  ((ModuleCat.epi_iff_surjective _).mp (shortExact_map_stalkFunctor Oc hfg hSE y).epi_g
    ((unitStalkCommEquiv Oc y).symm 1)).choose

/-- The stalk of `g` carries `stalkUnitLift` to the generator of the stalk of the unit sheaf. -/
theorem stalkMapL_stalkUnitLift {f : F ⟶ H}
    {g : H ⟶ SheafOfModules.unit (ringSheafOfComm Oc)}
    (hfg : f ≫ g = 0) (hSE : (ShortComplex.mk f g hfg).ShortExact) (y : ↥X) :
    PresheafOfModules.stalkMapL y g.val (stalkUnitLift Oc hfg hSE y)
      = (unitStalkCommEquiv Oc y).symm 1 :=
  ((ModuleCat.epi_iff_surjective _).mp (shortExact_map_stalkFunctor Oc hfg hSE y).epi_g
    ((unitStalkCommEquiv Oc y).symm 1)).choose_spec

/-- A short exact sequence of sheaves of modules whose third term is the unit sheaf splits on
every stalk, with section `c ↦ c • stalkUnitLift` of the stalk of `g`. -/
def stalkSplittingOfShortExactUnit {f : F ⟶ H}
    {g : H ⟶ SheafOfModules.unit (ringSheafOfComm Oc)}
    (hfg : f ≫ g = 0) (hSE : (ShortComplex.mk f g hfg).ShortExact) (y : ↥X) :
    ((ShortComplex.mk f g hfg).map
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (ringSheafOfComm Oc) y)).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _ (shortExact_map_stalkFunctor Oc hfg hSE y).exact
    (ModuleCat.ofHom (stalkRingLinearOfCommLinear y
      ((LinearMap.toSpanSingleton _ _ (stalkUnitLift Oc hfg hSE y)).comp
        (unitStalkCommEquiv Oc y).toLinearMap)))
    (ModuleCat.hom_ext (LinearMap.ext fun m => by
      have hstep : PresheafOfModules.stalkMapL y g.val
          (unitStalkCommEquiv Oc y m • stalkUnitLift Oc hfg hSE y) = m := by
        rw [map_smul, stalkMapL_stalkUnitLift]
        refine (unitStalkCommEquiv Oc y).injective ?_
        rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
      exact hstep))
    (shortExact_map_stalkFunctor Oc hfg hSE y).mono_f

/-- For a short complex `F ⟶ H ⟶ G` of sheaves of modules together with a splitting of its
complex of stalks at `y`, the stalk of `H` at `y` is the product of the stalks of `F` and of `G`,
linearly over the stalk of the sheaf of rings; the forward map is the pair of the retraction and
of the stalk of the second arrow. -/
def prodEquivOfStalkSplitting {f : F ⟶ H} {g : H ⟶ G} (hfg : f ≫ g = 0) (y : ↥X)
    (sp : ((ShortComplex.mk f g hfg).map
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (ringSheafOfComm Oc) y)).Splitting) :
    ToType (TopCat.Presheaf.stalk H.val.presheaf y)
      ≃ₗ[ToType (TopCat.Presheaf.stalk Oc.obj y)]
      (ToType (TopCat.Presheaf.stalk F.val.presheaf y) ×
        ToType (TopCat.Presheaf.stalk G.val.presheaf y)) := by
  set ι := PresheafOfModules.stalkMapL y f.val with hι
  set π := PresheafOfModules.stalkMapL y g.val with hπ
  set ρ := stalkCommLinearOfRingLinear y (M := H.val) (N := F.val) sp.r.hom with hρ
  set σ := stalkCommLinearOfRingLinear y (M := G.val) (N := H.val) sp.s.hom with hσ
  have hfr : ∀ p, ρ (ι p) = p := fun p =>
    congrArg (fun φ : _ ⟶ _ => ModuleCat.Hom.hom φ p) sp.f_r
  have hsg : ∀ c, π (σ c) = c := fun c =>
    congrArg (fun φ : _ ⟶ _ => ModuleCat.Hom.hom φ c) sp.s_g
  have hsr : ∀ c, ρ (σ c) = 0 := fun c =>
    congrArg (fun φ : _ ⟶ _ => ModuleCat.Hom.hom φ c) sp.s_r
  have hpi : ∀ p, π (ι p) = 0 := fun p =>
    congrArg (fun φ : _ ⟶ _ => ModuleCat.Hom.hom φ p)
      ((ShortComplex.mk f g hfg).map
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (ringSheafOfComm Oc) y)).zero
  refine LinearEquiv.ofLinearMap (ρ.prod π)
    (ι.comp (LinearMap.fst _ _ _) + σ.comp (LinearMap.snd _ _ _)) ?_ ?_
  · refine LinearMap.ext fun ab => Prod.ext ?_ ?_
    · change ρ (ι ab.1 + σ ab.2) = ab.1
      rw [map_add, hfr, hsr, add_zero]
    · change π (ι ab.1 + σ ab.2) = ab.2
      rw [map_add, hpi, hsg, zero_add]
  · exact LinearMap.ext fun m => congrArg (fun φ : _ ⟶ _ => ModuleCat.Hom.hom φ m) sp.id

end Split

/-! ### The Euler sequence of projective space -/

section Euler

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The Euler sequence of projective space splits on the stalk at every point. -/
def eulerStalkSplitting (x : ProjectiveSpectrum.top (polyGrading R n)) :
    ((ShortComplex.mk (eulerFirstArrow R n) (eulerSurjection R n)
          (eulerFirstArrow_comp_eulerSurjection R n)).map
        (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (projRingSheaf (polyGrading R n)) x)).Splitting :=
  stalkSplittingOfShortExactUnit (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (eulerFirstArrow_comp_eulerSurjection R n) (shortExact_eulerSequence R n) x

/-- The stalk of `𝒪_X(-1)^{⊕ (n+1)}` is the product of the stalks of `Ω_{X/R}` and of `𝒪_X`,
linearly over the stalk of the structure sheaf, by the splitting of the Euler sequence at `x`. -/
def eulerStalkProdEquiv (x : ProjectiveSpectrum.top (polyGrading R n)) :
    ToType (TopCat.Presheaf.stalk (twistMinusOneSum R n).val.presheaf x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk
          (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n)).obj x)]
      (ToType (TopCat.Presheaf.stalk (projDifferentials R n).val.presheaf x) ×
        ToType (TopCat.Presheaf.stalk
          (SheafOfModules.unit (projRingSheaf (polyGrading R n))).val.presheaf x)) :=
  prodEquivOfStalkSplitting (ProjectiveSpectrum.Proj.structureSheaf (polyGrading R n))
    (eulerFirstArrow_comp_eulerSurjection R n) x (eulerStalkSplitting R n x)

end Euler

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
