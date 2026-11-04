module

public import StacksFrontier.RingTheory.Flat.DevissageBaseChange

/-!
# Localizing a complete dévissage at the base prime

Given a complete dévissage `D` of `N/S/R` over a prime `r` of `R` (`Module.CompleteDevissage`),
localizing every ring and every module of `D` at the image of `r.primeCompl` gives a complete
dévissage over the local ring `R_r = Localization r.primeCompl` and the ideal `rR_r`. Its
stage algebras are `Localization (Algebra.algebraMapSubmonoid (D.A i) r.primeCompl)` and its stage
modules are `LocalizedModule (Algebra.algebraMapSubmonoid (D.A i) r.primeCompl) (D.M i)`.

## Main definitions

* `Module.CompleteDevissage.localize`: the base change of a complete dévissage to the local ring
  at its prime, for any localization `S'` of the algebra and `N'` of the module.
* `Module.CompleteDevissage.localizeAtPrime`: the same with the canonical models
  `Localization (Algebra.algebraMapSubmonoid S r.primeCompl)` and
  `LocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) N`, for a base ring, an algebra
  and a module in one universe.
* `Module.CompleteDevissage.locA`, `locB`, `locM`, `locToLeft`, `locToRight`, `locToA₀`, `locMk`,
  `locAlpha`, `locCokerMap`, `locCokerEquiv`: the localized stage data.

## Main results

* `Stacks.Flatness.isPrime_map_algebraMap_primeCompl`: the prime `r` stays prime in `R_r`.
* `Stacks.Flatness.finiteType_of_isLocalization` and
  `Stacks.Flatness.finiteType_localization_algebraMapSubmonoid`: `S_r` is of finite type over
  `R_r` when `S` is of finite type over `R`.
* `Module.CompleteDevissage.locAlpha_mapRange`: the localized stage map is the localization of
  the stage map.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
-/

@[expose] public section

open AlgebraicGeometry

universe u v w

namespace Stacks.Flatness

/-- A prime `r` of `R` generates a prime ideal in a localization `R'` of `R` at `r.primeCompl`. -/
public instance isPrime_map_algebraMap_primeCompl {R : Type*} [CommRing R] {r : Ideal R}
    [r.IsPrime] (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization r.primeCompl R'] :
    (Ideal.map (algebraMap R R') r).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint r.primeCompl R' r ‹_›
    (Set.disjoint_left.mpr fun _ hx hx' => hx hx')

/-- If `S` is of finite type over `R`, `Rₚ` is a localization of `R` at `P` and `Sₚ` is a
localization of `S` at the image of `P`, compatibly with the algebra maps, then `Sₚ` is of finite
type over `Rₚ`. The four rings lie in one universe. -/
public theorem finiteType_of_isLocalization {R S Rₚ Sₚ : Type u} [CommRing R] [CommRing S]
    [CommRing Rₚ] [CommRing Sₚ] [Algebra R S] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (P : Submonoid R)
    [IsLocalization P Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid S P) Sₚ]
    [Algebra.FiniteType R S] : Algebra.FiniteType Rₚ Sₚ :=
  RingHom.finiteType_algebraMap.mp
    (RingHom.finiteType_isStableUnderBaseChange.of_isLocalization P
      (RingHom.finiteType_algebraMap.mpr ‹_›))

/-- The canonical localization of an algebra of finite type is of finite type over the
localization of the base. -/
public instance finiteType_localization_algebraMapSubmonoid {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (P : Submonoid R) :
    Algebra.FiniteType (Localization P) (Localization (Algebra.algebraMapSubmonoid S P)) :=
  finiteType_of_isLocalization (S := S) P

end Stacks.Flatness

namespace Module.CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R}
  [r.IsPrime] (D : CompleteDevissage R S N r)

/-! ### Restriction of scalars along the maps of a dévissage -/

/-- The lower algebra at a stage acts on the stage module through `toLeft`. -/
public instance moduleBM (i : Fin (D.stepCount + 1)) : Module (D.B i) (D.M i) :=
  Module.compHom (D.M i) (D.toLeft i).toRingHom

/-- The upper algebra at a stage is an algebra over the lower one through `toLeft`. -/
public instance algebraBA (i : Fin (D.stepCount + 1)) : Algebra (D.B i) (D.A i) :=
  (D.toLeft i).toRingHom.toAlgebra

/-- The scalar tower `R → D.B i → D.A i`. -/
public instance isScalarTowerRBA (i : Fin (D.stepCount + 1)) :
    IsScalarTower R (D.B i) (D.A i) :=
  IsScalarTower.of_algebraMap_eq fun x => ((D.toLeft i).commutes x).symm

/-- The scalar tower `D.B i → D.A i → D.M i`. -/
public instance isScalarTowerBAM (i : Fin (D.stepCount + 1)) :
    IsScalarTower (D.B i) (D.A i) (D.M i) :=
  ⟨fun b a m => by change (D.toLeft i b * a) • m = D.toLeft i b • (a • m); rw [mul_smul]⟩

/-- The upper algebra at a stage is finite over the lower one. -/
public instance finiteBA (i : Fin (D.stepCount + 1)) : Module.Finite (D.B i) (D.A i) :=
  RingHom.finite_algebraMap.mp (D.left_finite i)

/-- The module at a stage is finite over the lower algebra. -/
public instance finiteBM (i : Fin (D.stepCount + 1)) : Module.Finite (D.B i) (D.M i) :=
  Module.Finite.trans (D.A i) (D.M i)

/-- The original algebra acts on the first stage module through `toA₀`. -/
public instance moduleSM₀ : Module S (D.M 0) := Module.compHom (D.M 0) D.toA₀.toRingHom

/-- The first upper algebra is an algebra over the original algebra through `toA₀`. -/
public instance algebraSA₀ : Algebra S (D.A 0) := D.toA₀.toRingHom.toAlgebra

/-- The scalar tower `R → S → D.A 0`. -/
public instance isScalarTowerRSA₀ : IsScalarTower R S (D.A 0) :=
  IsScalarTower.of_algebraMap_eq fun x => (D.toA₀.commutes x).symm

/-- The scalar tower `S → D.A 0 → D.M 0`. -/
public instance isScalarTowerSA₀M₀ : IsScalarTower S (D.A 0) (D.M 0) :=
  ⟨fun b a m => by change (D.toA₀ b * a) • m = D.toA₀ b • (a • m); rw [mul_smul]⟩

/-- A lower algebra acts on the next stage's module through `toRight`. -/
public instance moduleBMsucc (i : Fin D.stepCount) : Module (D.B i.castSucc) (D.M i.succ) :=
  Module.compHom (D.M i.succ) (D.toRight i).toRingHom

/-- The next stage's upper algebra is an algebra over a lower algebra through `toRight`. -/
public instance algebraBAsucc (i : Fin D.stepCount) :
    Algebra (D.B i.castSucc) (D.A i.succ) := (D.toRight i).toRingHom.toAlgebra

/-- The scalar tower `R → D.B i.castSucc → D.A i.succ`. -/
public instance isScalarTowerRBAsucc (i : Fin D.stepCount) :
    IsScalarTower R (D.B i.castSucc) (D.A i.succ) :=
  IsScalarTower.of_algebraMap_eq fun x => ((D.toRight i).commutes x).symm

/-- The scalar tower `D.B i.castSucc → D.A i.succ → D.M i.succ`. -/
public instance isScalarTowerBAMsucc (i : Fin D.stepCount) :
    IsScalarTower (D.B i.castSucc) (D.A i.succ) (D.M i.succ) :=
  ⟨fun b a m => by
    change (D.toRight i b * a) • m = D.toRight i b • (a • m); rw [mul_smul]⟩

/-! ### The localized stage data -/

/-- The localization of the upper algebra at stage `i` of a dévissage over `r`, at the image of
the complement of `r`. -/
public abbrev locA (i : Fin (D.stepCount + 1)) : Type u :=
  Localization (Algebra.algebraMapSubmonoid (D.A i) r.primeCompl)

/-- The localization of the lower algebra at stage `i` of a dévissage over `r`, at the image of
the complement of `r`. -/
public abbrev locB (i : Fin (D.stepCount + 1)) : Type u :=
  Localization (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl)

/-- The localization of the module at stage `i` of a dévissage over `r`, at the image of the
complement of `r`. -/
public abbrev locM (i : Fin (D.stepCount + 1)) : Type max u w :=
  LocalizedModule (Algebra.algebraMapSubmonoid (D.A i) r.primeCompl) (D.M i)

/-- The localization of the map from the lower to the upper algebra at stage `i`. -/
public noncomputable def locToLeft (i : Fin (D.stepCount + 1)) :
    D.locB i →ₐ[Localization r.primeCompl] D.locA i :=
  IsLocalization.mapₐ r.primeCompl (Localization r.primeCompl) (D.locB i) (D.locA i) (D.toLeft i)

/-- The localization of the map from a lower algebra to the next upper algebra. -/
public noncomputable def locToRight (i : Fin D.stepCount) :
    D.locB i.castSucc →ₐ[Localization r.primeCompl] D.locA i.succ :=
  IsLocalization.mapₐ r.primeCompl (Localization r.primeCompl) (D.locB i.castSucc)
    (D.locA i.succ) (D.toRight i)

/-- The localized `toLeft` sends the image of `b` to the image of `D.toLeft i b`. -/
@[simp]
public theorem locToLeft_algebraMap (i : Fin (D.stepCount + 1)) (b : D.B i) :
    D.locToLeft i (algebraMap (D.B i) (D.locB i) b)
      = algebraMap (D.A i) (D.locA i) (D.toLeft i b) :=
  IsLocalization.map_eq (Algebra.algebraMapSubmonoid_le_comap r.primeCompl (D.toLeft i)) b

/-- The localized `toRight` sends the image of `b` to the image of `D.toRight i b`. -/
@[simp]
public theorem locToRight_algebraMap (i : Fin D.stepCount) (b : D.B i.castSucc) :
    D.locToRight i (algebraMap (D.B i.castSucc) (D.locB i.castSucc) b)
      = algebraMap (D.A i.succ) (D.locA i.succ) (D.toRight i b) :=
  IsLocalization.map_eq (Algebra.algebraMapSubmonoid_le_comap r.primeCompl (D.toRight i)) b

/-- The localized lower algebra at a stage acts on the localized module through the localized
`toLeft`. -/
public noncomputable instance moduleLocBLocM (i : Fin (D.stepCount + 1)) :
    Module (D.locB i) (D.locM i) :=
  Module.compHom (D.locM i) (D.locToLeft i).toRingHom

/-- The localized upper algebra at a stage is an algebra over the localized lower one. -/
public noncomputable instance algebraLocBLocA (i : Fin (D.stepCount + 1)) :
    Algebra (D.locB i) (D.locA i) := (D.locToLeft i).toRingHom.toAlgebra

/-- The scalar tower `D.locB i → D.locA i → D.locM i`. -/
public instance isScalarTowerLocBLocALocM (i : Fin (D.stepCount + 1)) :
    IsScalarTower (D.locB i) (D.locA i) (D.locM i) :=
  ⟨fun b a m => by
    change (D.locToLeft i b * a) • m = D.locToLeft i b • (a • m); rw [mul_smul]⟩

/-- The scalar tower `D.B i → D.locB i → D.locA i`. -/
public instance isScalarTowerBLocBLocA (i : Fin (D.stepCount + 1)) :
    IsScalarTower (D.B i) (D.locB i) (D.locA i) :=
  IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply (D.B i) (D.A i) (D.locA i)]
    exact (D.locToLeft_algebraMap i b).symm

/-- The scalar tower `D.B i → D.locB i → D.locM i`. -/
public instance isScalarTowerBLocBLocM (i : Fin (D.stepCount + 1)) :
    IsScalarTower (D.B i) (D.locB i) (D.locM i) :=
  IsScalarTower.of_algebraMap_smul fun b x => by
    rw [← IsScalarTower.algebraMap_smul (D.locA i) (algebraMap (D.B i) (D.locB i) b) x,
      ← IsScalarTower.algebraMap_apply (D.B i) (D.locB i) (D.locA i),
      IsScalarTower.algebraMap_apply (D.B i) (D.A i) (D.locA i),
      IsScalarTower.algebraMap_smul (D.locA i) (algebraMap (D.B i) (D.A i) b) x,
      IsScalarTower.algebraMap_smul (D.A i) b x]

/-- The localization map of the module at stage `i`, as a map of modules over the lower
algebra. -/
public noncomputable def locMk (i : Fin (D.stepCount + 1)) : D.M i →ₗ[D.B i] D.locM i :=
  (LocalizedModule.mkLinearMap
    (Algebra.algebraMapSubmonoid (D.A i) r.primeCompl) (D.M i)).restrictScalars (D.B i)

/-- `D.locMk i` sends `m` to the fraction `m / 1`. -/
@[simp]
public theorem locMk_apply (i : Fin (D.stepCount + 1)) (m : D.M i) :
    D.locMk i m = LocalizedModule.mk m 1 := rfl

/-- `D.locMk i` is a localization of the stage module at the image of `r.primeCompl` in the
lower algebra. -/
public instance isLocalizedModule_locMk (i : Fin (D.stepCount + 1)) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl) (D.locMk i) := by
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid (D.A i)
      (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl))
      (LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid (D.A i) r.primeCompl) (D.M i)) := by
    rw [Algebra.algebraMapSubmonoid_map_map (A := D.B i)]; infer_instance
  exact IsLocalizedModule.restrictScalars _ _

/-- The localization of the map of a dévissage stage. -/
public noncomputable def locAlpha (i : Fin (D.stepCount + 1)) :
    (Fin (D.multiplicity i) →₀ D.locB i) →ₗ[D.locB i] D.locM i :=
  IsLocalizedModule.mapExtendScalars (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl)
    (Finsupp.mapRange.linearMap (Algebra.linearMap (D.B i) (D.locB i))) (D.locMk i)
    (D.locB i) (D.alpha i)

/-- The localized map of a stage is the localization of the map of that stage. -/
public theorem locAlpha_mapRange (i : Fin (D.stepCount + 1))
    (x : Fin (D.multiplicity i) →₀ D.B i) :
    D.locAlpha i (Finsupp.mapRange.linearMap (Algebra.linearMap (D.B i) (D.locB i)) x)
      = D.locMk i (D.alpha i x) := by
  rw [locAlpha, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]

/-! ### The localized transition data -/

/-- The localized lower algebra at a stage acts on the next stage's localized module through the
localized `toRight`. -/
public noncomputable instance moduleLocBLocMsucc (i : Fin D.stepCount) :
    Module (D.locB i.castSucc) (D.locM i.succ) :=
  Module.compHom (D.locM i.succ) (D.locToRight i).toRingHom

/-- The next stage's localized upper algebra is an algebra over the localized lower one. -/
public noncomputable instance algebraLocBLocAsucc (i : Fin D.stepCount) :
    Algebra (D.locB i.castSucc) (D.locA i.succ) := (D.locToRight i).toRingHom.toAlgebra

/-- The scalar tower `D.locB i.castSucc → D.locA i.succ → D.locM i.succ`. -/
public instance isScalarTowerLocBLocALocMsucc (i : Fin D.stepCount) :
    IsScalarTower (D.locB i.castSucc) (D.locA i.succ) (D.locM i.succ) :=
  ⟨fun b a m => by
    change (D.locToRight i b * a) • m = D.locToRight i b • (a • m); rw [mul_smul]⟩

/-- The scalar tower `D.B i.castSucc → D.locB i.castSucc → D.locA i.succ`. -/
public instance isScalarTowerBLocBLocAsucc (i : Fin D.stepCount) :
    IsScalarTower (D.B i.castSucc) (D.locB i.castSucc) (D.locA i.succ) :=
  IsScalarTower.of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply (D.B i.castSucc) (D.A i.succ) (D.locA i.succ)]
    exact (D.locToRight_algebraMap i b).symm

/-- The scalar tower `D.B i.castSucc → D.locB i.castSucc → D.locM i.succ`. -/
public instance isScalarTowerBLocBLocMsucc (i : Fin D.stepCount) :
    IsScalarTower (D.B i.castSucc) (D.locB i.castSucc) (D.locM i.succ) :=
  IsScalarTower.of_algebraMap_smul fun b x => by
    rw [← IsScalarTower.algebraMap_smul (D.locA i.succ)
        (algebraMap (D.B i.castSucc) (D.locB i.castSucc) b) x,
      ← IsScalarTower.algebraMap_apply (D.B i.castSucc) (D.locB i.castSucc) (D.locA i.succ),
      IsScalarTower.algebraMap_apply (D.B i.castSucc) (D.A i.succ) (D.locA i.succ),
      IsScalarTower.algebraMap_smul (D.locA i.succ)
        (algebraMap (D.B i.castSucc) (D.A i.succ) b) x,
      IsScalarTower.algebraMap_smul (D.A i.succ) b x]

/-- The localization map of the next stage's module, as a map of modules over the lower algebra
of the current stage. -/
public noncomputable def locMkSucc (i : Fin D.stepCount) :
    D.M i.succ →ₗ[D.B i.castSucc] D.locM i.succ :=
  (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid (D.A i.succ) r.primeCompl)
    (D.M i.succ)).restrictScalars (D.B i.castSucc)

/-- `D.locMkSucc i` is a localization of the next stage's module at the image of
`r.primeCompl` in the lower algebra of the current stage. -/
public instance isLocalizedModule_locMkSucc (i : Fin D.stepCount) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid (D.B i.castSucc) r.primeCompl)
      (D.locMkSucc i) := by
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid (D.A i.succ)
      (Algebra.algebraMapSubmonoid (D.B i.castSucc) r.primeCompl))
      (LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid (D.A i.succ) r.primeCompl) (D.M i.succ)) := by
    rw [Algebra.algebraMapSubmonoid_map_map (A := D.B i.castSucc)]; infer_instance
  exact IsLocalizedModule.restrictScalars _ _

/-- The image of the map of a stage lands in the kernel of the localized quotient map. -/
public theorem range_alpha_le_ker (i : Fin (D.stepCount + 1)) :
    LinearMap.range (D.alpha i) ≤ LinearMap.ker
      (((LinearMap.range (D.locAlpha i)).mkQ).restrictScalars (D.B i) ∘ₗ D.locMk i) := by
  rintro y ⟨x, rfl⟩
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨Finsupp.mapRange.linearMap (Algebra.linearMap (D.B i) (D.locB i)) x,
    D.locAlpha_mapRange i x⟩

/-- The map on cokernels induced by the localization map of a stage. -/
public noncomputable def locCokerMap (i : Fin (D.stepCount + 1)) :
    (D.M i ⧸ LinearMap.range (D.alpha i)) →ₗ[D.B i]
      (D.locM i ⧸ LinearMap.range (D.locAlpha i)) :=
  Submodule.liftQ _ _ (D.range_alpha_le_ker i)

/-- `D.locCokerMap i` is a localization of the cokernel of a stage map at the image of
`r.primeCompl` in the lower algebra. -/
public instance isLocalizedModule_locCokerMap (i : Fin (D.stepCount + 1)) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl)
      (D.locCokerMap i) :=
  Stacks.Flatness.isLocalizedModule_of_quotient_range
    (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl)
    (Finsupp.mapRange.linearMap (Algebra.linearMap (D.B i) (D.locB i))) (D.locMk i)
    (D.alpha i) (D.locAlpha i) (D.locAlpha_mapRange i) (D.locCokerMap i) fun _ => rfl

/-- The cokernel identification of a stage, localized. -/
public noncomputable def locCokerEquiv (i : Fin D.stepCount) :
    (D.locM i.castSucc ⧸ LinearMap.range (D.locAlpha i.castSucc)) ≃ₗ[D.locB i.castSucc]
      D.locM i.succ :=
  IsLocalizedModule.mapEquiv (Algebra.algebraMapSubmonoid (D.B i.castSucc) r.primeCompl)
    (D.locCokerMap i.castSucc) (D.locMkSucc i) (D.locB i.castSucc) (D.cokerEquiv i)

/-- The ideal generated by `r` in the localized lower algebra of a stage is prime. -/
public instance isPrime_map_locB (i : Fin (D.stepCount + 1)) :
    (Ideal.map (algebraMap (Localization r.primeCompl) (D.locB i))
      (Ideal.map (algebraMap R (Localization r.primeCompl)) r)).IsPrime :=
  Stacks.Flatness.isPrime_map_algebraMap_of_disjoint r.primeCompl r
    (Localization r.primeCompl) (D.locB i) (D.disjoint_map i)

/-! ### The localized initial data -/

/-- The localization map of the first stage's module, as a map of modules over the original
algebra. -/
public noncomputable def locMk₀ : D.M 0 →ₗ[S] D.locM 0 :=
  (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid (D.A 0) r.primeCompl)
    (D.M 0)).restrictScalars S

/-- `D.locMk₀` is a localization of the first stage module at the image of `r.primeCompl` in
`S`. -/
public instance isLocalizedModule_locMk₀ :
    IsLocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) D.locMk₀ := by
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid (D.A 0)
      (Algebra.algebraMapSubmonoid S r.primeCompl))
      (LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid (D.A 0) r.primeCompl) (D.M 0)) := by
    rw [Algebra.algebraMapSubmonoid_map_map (A := S)]; infer_instance
  exact IsLocalizedModule.restrictScalars _ _

section Initial

variable (S' : Type v) [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
  [IsLocalization (Algebra.algebraMapSubmonoid S r.primeCompl) S']
  [Algebra (Localization r.primeCompl) S'] [IsScalarTower R (Localization r.primeCompl) S']

/-- The localization of the map from the original algebra to the first upper algebra. -/
public noncomputable def locToA₀ : S' →ₐ[Localization r.primeCompl] D.locA 0 :=
  IsLocalization.mapₐ r.primeCompl (Localization r.primeCompl) S' (D.locA 0) D.toA₀

/-- The localized `toA₀` sends the image of `s` to the image of `D.toA₀ s`. -/
@[simp]
public theorem locToA₀_algebraMap (s : S) :
    D.locToA₀ S' (algebraMap S S' s) = algebraMap (D.A 0) (D.locA 0) (D.toA₀ s) :=
  IsLocalization.map_eq (Algebra.algebraMapSubmonoid_le_comap r.primeCompl D.toA₀) s

/-- The localized original algebra acts on the first localized module through the localized
initial map. -/
public noncomputable instance moduleS'LocM₀ : Module S' (D.locM 0) :=
  Module.compHom (D.locM 0) (D.locToA₀ S').toRingHom

/-- The first localized upper algebra is an algebra over the localized original algebra. -/
public noncomputable instance algebraS'LocA₀ : Algebra S' (D.locA 0) :=
  (D.locToA₀ S').toRingHom.toAlgebra

/-- The scalar tower `S' → D.locA 0 → D.locM 0`. -/
public instance isScalarTowerS'LocA₀LocM₀ : IsScalarTower S' (D.locA 0) (D.locM 0) :=
  ⟨fun b a m => by
    change (D.locToA₀ S' b * a) • m = D.locToA₀ S' b • (a • m); rw [mul_smul]⟩

/-- The scalar tower `S → S' → D.locA 0`. -/
public instance isScalarTowerSS'LocA₀ : IsScalarTower S S' (D.locA 0) :=
  IsScalarTower.of_algebraMap_eq fun s => by
    rw [IsScalarTower.algebraMap_apply S (D.A 0) (D.locA 0)]
    exact (D.locToA₀_algebraMap S' s).symm

/-- The scalar tower `S → S' → D.locM 0`. -/
public instance isScalarTowerSS'LocM₀ : IsScalarTower S S' (D.locM 0) :=
  IsScalarTower.of_algebraMap_smul fun s x => by
    rw [← IsScalarTower.algebraMap_smul (D.locA 0) (algebraMap S S' s) x,
      ← IsScalarTower.algebraMap_apply S S' (D.locA 0),
      IsScalarTower.algebraMap_apply S (D.A 0) (D.locA 0),
      IsScalarTower.algebraMap_smul (D.locA 0) (algebraMap S (D.A 0) s) x,
      IsScalarTower.algebraMap_smul (D.A 0) s x]

variable (N' : Type max u w) [AddCommGroup N'] [Module S N'] [Module S' N']
  [IsScalarTower S S' N'] [Module.Finite S' N'] (gN : N →ₗ[S] N')
  [IsLocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) gN]
  [Algebra.FiniteType (Localization r.primeCompl) S']

/-- The base change of a complete dévissage of `N/S/R` over a prime `r` of `R` to the local
ring `R_r = Localization r.primeCompl`: a complete dévissage of `N'/S'/R_r` over `rR_r`.

It takes as hypotheses that `S'` is a localization of `S` at the image of `r.primeCompl`, of
finite type over `R_r`, and that `gN : N →ₗ[S] N'` is a localization of `N` at the same
submonoid, with `N'` finite over `S'`. Its stage algebras and stage modules are `D.locA`,
`D.locB` and `D.locM`. -/
public noncomputable def localize :
    CompleteDevissage (Localization r.primeCompl) S' N'
      (Ideal.map (algebraMap R (Localization r.primeCompl)) r) where
  stepCount := D.stepCount
  A := D.locA
  B := D.locB
  M := D.locM
  toA₀ := D.locToA₀ S'
  toLeft := D.locToLeft
  toRight := D.locToRight
  multiplicity := D.multiplicity
  alpha := D.locAlpha
  finiteM i := Module.Finite.of_isLocalizedModule
    (Algebra.algebraMapSubmonoid (D.A i) r.primeCompl)
    (LocalizedModule.mkLinearMap _ (D.M i))
  initial_surjective := IsLocalization.mapₐ_surjective_of_surjective r.primeCompl
    (Localization r.primeCompl) S' (D.locA 0) D.toA₀ D.initial_surjective
  initial_finitePresentation := Stacks.Flatness.finitePresentation_mapₐ_of_isLocalization
    r.primeCompl D.toA₀ D.initial_surjective D.initial_finitePresentation
    (Localization r.primeCompl) S' (D.locA 0)
  transition_surjective i := IsLocalization.mapₐ_surjective_of_surjective r.primeCompl
    (Localization r.primeCompl) (D.locB i.castSucc) (D.locA i.succ) (D.toRight i)
    (D.transition_surjective i)
  transition_finitePresentation i := Stacks.Flatness.finitePresentation_mapₐ_of_isLocalization
    r.primeCompl (D.toRight i) (D.transition_surjective i) (D.transition_finitePresentation i)
    (Localization r.primeCompl) (D.locB i.castSucc) (D.locA i.succ)
  left_finite i := RingHom.finite_algebraMap.mpr
    (Stacks.Flatness.finite_of_isLocalization r.primeCompl (A := D.A i) (B := D.B i)
      (D.locB i) (D.locA i))
  smooth i := Stacks.Flatness.smooth_of_isLocalization (D.B i) r.primeCompl
    (Localization r.primeCompl) (D.locB i)
  geometricallyIrreducibleFibers i :=
    Stacks.Flatness.geometricallyIrreducible_of_isLocalization (D.B i) r.primeCompl
      (Localization r.primeCompl) (D.locB i)
  initialEquiv := IsLocalizedModule.mapEquiv (Algebra.algebraMapSubmonoid S r.primeCompl)
    gN D.locMk₀ S' D.initialEquiv
  cokerEquiv := D.locCokerEquiv
  map_isPrime i := Stacks.Flatness.isPrime_map_algebraMap_of_disjoint r.primeCompl r
    (Localization r.primeCompl) (D.locB i) (D.disjoint_map i)
  fiber_bijective i := Stacks.Flatness.fiber_bijective_of_isLocalization (D.alpha i)
    (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl) (D.locMk i) (D.locAlpha i)
    (D.locAlpha_mapRange i) (Ideal.map (algebraMap R (D.B i)) r)
    (Ideal.map (algebraMap (Localization r.primeCompl) (D.locB i))
      (Ideal.map (algebraMap R (Localization r.primeCompl)) r))
    (Stacks.Flatness.map_algebraMap_eq_comap_of_disjoint r.primeCompl r
      (Localization r.primeCompl) (D.locB i) (D.disjoint_map i))
    (D.fiber_bijective i)
  final_surjective := Stacks.Flatness.surjective_of_isLocalization
    (Algebra.algebraMapSubmonoid (D.B (Fin.last D.stepCount)) r.primeCompl)
    (Finsupp.mapRange.linearMap (Algebra.linearMap (D.B (Fin.last D.stepCount))
      (D.locB (Fin.last D.stepCount))))
    (D.locMk (Fin.last D.stepCount)) (D.alpha (Fin.last D.stepCount))
    (D.locAlpha (Fin.last D.stepCount)) (D.locAlpha_mapRange (Fin.last D.stepCount))
    D.final_surjective

/-- The localized dévissage has as many stages as the original one. -/
@[simp]
public theorem stepCount_localize :
    (D.localize S' N' gN).stepCount = D.stepCount := rfl

end Initial

/-- The base change of a complete dévissage of `N/S/R` over a prime `r` of `R` to the local
ring `R_r = Localization r.primeCompl`, with the canonical localizations of `S` and `N` at the
image of `r.primeCompl`. The rings `R`, `S` and the module `N` lie in one universe. -/
public noncomputable def localizeAtPrime {R S N : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    {r : Ideal R} [r.IsPrime] (D : CompleteDevissage R S N r) :
    CompleteDevissage (Localization r.primeCompl)
      (Localization (Algebra.algebraMapSubmonoid S r.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid S r.primeCompl) N)
      (Ideal.map (algebraMap R (Localization r.primeCompl)) r) :=
  D.localize _ _ (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid S r.primeCompl) N)

/-- The canonically localized dévissage has as many stages as the original one. -/
@[simp]
public theorem stepCount_localizeAtPrime {R S N : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    {r : Ideal R} [r.IsPrime] (D : CompleteDevissage R S N r) :
    D.localizeAtPrime.stepCount = D.stepCount := rfl

end Module.CompleteDevissage

end
