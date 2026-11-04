module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Abelian.Transfer
public import StacksFrontier.Examples.Completion.CompleteModuleCategory
public import StacksFrontier.Examples.Completion.CompleteModulesNotAbelian
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit

/-!
# Adic towers and adically complete modules

Let `I` be a finitely generated ideal of a commutative ring `R`.  An *adic tower* over `(R, I)`
is a family of `R`-modules `Mₙ` together with surjections `πₙ : M (n + 1) → Mₙ` whose kernel is
exactly `Iⁿ M (n + 1)`, so that `Mₙ = M (n + 1) / Iⁿ M (n + 1)`.  These towers form a category,
a morphism being a family of linear maps commuting with the transitions.

This file proves that passing to the limit `M = lim Mₙ` is an **equivalence** from the category
of adic towers to the category of `I`-adically complete `R`-modules.

## Main definitions

* `Stacks.Examples.AdicTower`: an adic tower over `(R, I)`.
* `Stacks.Examples.AdicTower.limitFunctor`: the functor `(Mₙ) ↦ lim Mₙ` into the category of
  `I`-adically complete modules.
* `Stacks.Examples.AdicTower.quotientTower`: the tower `n ↦ M ⧸ Iⁿ M` of a module.
* `Stacks.Examples.AdicTower.limitEquivalence`: the equivalence of categories.

## Main results

* `Stacks.Examples.AdicTower.limitFunctor_faithful` and
  `Stacks.Examples.AdicTower.limitFunctor_full`: the limit functor is fully faithful.
* `Stacks.Examples.AdicTower.limitFunctor_essSurj`: every `I`-adically complete module is the
  limit of an adic tower, namely of its own tower of adic quotients.
* `Stacks.Examples.AdicTower.exists_not_abelian_adicTower`: the category of adic towers is not
  abelian in general, the counterexample of Stacks 07JR carried back along the equivalence.

## Implementation notes

The two halves of the inverse are the only inputs beyond formal nonsense.  One way, the limit of
an adic tower is `I`-adically complete and its quotients by the `Iⁿ` recover the tower; that is
Stacks 09B8, stated as `Stacks.AdicCompletion.InverseLimit.InverseSystem.isAdicComplete` and
`.quotientEquiv`, both under the finite generation of `I`, which is the hypothesis of that tag.
The other way, an `I`-adically complete module is the limit of its own tower of adic quotients;
that is `AdicCompletion.ofLinearEquiv`, together with the observation that a family of adic
quotients compatible for the successor transitions is already compatible for all of them.

The equivalence is obtained from full faithfulness and essential surjectivity rather than by
writing down the inverse functor.  Fullness is the only nonformal step, and it is exactly the
statement that a linear map `lim Mₙ → lim Nₙ` is induced by its own reductions modulo the `Iⁿ`,
which is `quotientEquiv` read in both directions.

Adic towers are indexed by all of `ℕ`.  At `n = 0` the condition reads `M 0 = M 1 / I⁰ M 1 = 0`,
so the bottom module of a tower is always zero; this matches the tower of adic quotients, whose
level `0` is `M ⧸ I⁰ M = 0`, and discards no information.

## References

* [Stacks Project, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
* [Stacks Project, Tag 0317](https://stacks.math.columbia.edu/tag/0317)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.AdicCompletion.InverseLimit

universe u v

namespace Stacks.Examples

variable {R : Type u} [CommRing R]

/-- An **adic tower** over `(R, I)`: a family of `R`-modules `Mₙ` with surjective transition
maps `πₙ : M (n + 1) → Mₙ` whose kernel is `Iⁿ M (n + 1)`, that is, with
`Mₙ = M (n + 1) / Iⁿ M (n + 1)`.  This is the system of hypotheses of Stacks 09B8. -/
structure AdicTower (R : Type u) [CommRing R] (I : Ideal R) where
  /-- The family of modules. -/
  M : ℕ → ModuleCat.{v} R
  /-- The transition maps. -/
  π : ∀ n, M (n + 1) ⟶ M n
  /-- The transition maps are surjective. -/
  surjective : ∀ n, Function.Surjective (π n).hom
  /-- The kernel of `πₙ` is `Iⁿ M (n + 1)`. -/
  ker_π : ∀ n, LinearMap.ker (π n).hom = I ^ n • (⊤ : Submodule R (M (n + 1)))

namespace AdicTower

variable {I : Ideal R}

/-- A morphism of adic towers: a family of linear maps commuting with the transitions. -/
@[ext]
structure Hom (S T : AdicTower.{u, v} R I) where
  /-- The components of the morphism. -/
  f : ∀ n, S.M n ⟶ T.M n
  /-- The components commute with the transition maps. -/
  comm : ∀ n, S.π n ≫ f n = f (n + 1) ≫ T.π n

/-- The identity morphism of an adic tower. -/
def Hom.id (S : AdicTower.{u, v} R I) : Hom S S where
  f _ := CategoryTheory.CategoryStruct.id _
  comm _ := by simp

/-- The composite of two morphisms of adic towers. -/
def Hom.comp {S T U : AdicTower.{u, v} R I} (φ : Hom S T) (ψ : Hom T U) : Hom S U where
  f n := φ.f n ≫ ψ.f n
  comm n := by
    rw [← Category.assoc, φ.comm n, Category.assoc, ψ.comm n, Category.assoc]

/-- Adic towers over `(R, I)` form a category, with morphisms `AdicTower.Hom`. -/
instance : Category (AdicTower.{u, v} R I) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- The components of the identity morphism of an adic tower are identities. -/
@[simp]
theorem id_f (S : AdicTower.{u, v} R I) (n : ℕ) :
    Hom.f (CategoryTheory.CategoryStruct.id S) n = CategoryTheory.CategoryStruct.id (S.M n) :=
  rfl

/-- The components of a composite of morphisms of adic towers are the composites of the
components. -/
@[simp]
theorem comp_f {S T U : AdicTower.{u, v} R I} (φ : S ⟶ T) (ψ : T ⟶ U) (n : ℕ) :
    Hom.f (φ ≫ ψ) n = φ.f n ≫ ψ.f n :=
  rfl

/-- A morphism of adic towers, read at a single level as an identity of linear maps. -/
theorem Hom.comm_apply {S T : AdicTower.{u, v} R I} (φ : S ⟶ T) (n : ℕ) (y : S.M (n + 1)) :
    (φ.f n).hom ((S.π n).hom y) = (T.π n).hom ((φ.f (n + 1)).hom y) := by
  simpa using congrArg (fun g : S.M (n + 1) ⟶ T.M n => g.hom y) (φ.comm n)

/-! ### The limit of an adic tower -/

/-- The adic tower read as a bundled inverse system in the sense of Stacks 09B8. -/
def toInverseSystem (S : AdicTower.{u, v} R I) : InverseSystem.{u, v} I where
  M n := S.M n
  π n := (S.π n).hom
  surjective := S.surjective
  ker_π := S.ker_π

/-- The limit `lim Mₙ` of an adic tower, as a submodule of the product. -/
abbrev limitSubmodule (S : AdicTower.{u, v} R I) : Submodule R (∀ n, S.M n) :=
  S.toInverseSystem.limit

/-- The limit `lim Mₙ` of an adic tower, as an object of `ModuleCat R`. -/
abbrev limitModule (S : AdicTower.{u, v} R I) : ModuleCat.{v} R :=
  ModuleCat.of R S.limitSubmodule

/-- The projection from the limit of an adic tower to its `n`-th module. -/
abbrev limitProj (S : AdicTower.{u, v} R I) (n : ℕ) : S.limitSubmodule →ₗ[R] S.M n :=
  S.toInverseSystem.proj n

/-- Each projection from the limit of an adic tower to its `n`-th module is surjective. -/
theorem limitProj_surjective (S : AdicTower.{u, v} R I) (n : ℕ) :
    Function.Surjective (S.limitProj n) :=
  S.toInverseSystem.proj_surjective n

/-- The projections from the limit of an adic tower commute with the transition maps. -/
theorem π_limitProj (S : AdicTower.{u, v} R I) (n : ℕ) (x : S.limitSubmodule) :
    (S.π n).hom (S.limitProj (n + 1) x) = S.limitProj n x :=
  x.property n

/-- An element of the limit of an adic tower is determined by its projections. -/
theorem limit_ext {S : AdicTower.{u, v} R I} {x y : S.limitSubmodule}
    (h : ∀ n, S.limitProj n x = S.limitProj n y) : x = y :=
  Subtype.ext (funext h)

/-- The map on limits induced by a morphism of adic towers. -/
def limitMap {S T : AdicTower.{u, v} R I} (φ : S ⟶ T) :
    S.limitSubmodule →ₗ[R] T.limitSubmodule :=
  LinearMap.codRestrict T.limitSubmodule
    (LinearMap.pi fun n => (φ.f n).hom ∘ₗ S.limitProj n)
    fun x n => by
      change (T.π n).hom ((φ.f (n + 1)).hom (S.limitProj (n + 1) x))
        = (φ.f n).hom (S.limitProj n x)
      rw [← φ.comm_apply n, S.π_limitProj n x]

/-- The `n`-th projection of the map on limits induced by `φ` is the `n`-th component of `φ`
applied to the `n`-th projection. -/
@[simp]
theorem limitProj_limitMap {S T : AdicTower.{u, v} R I} (φ : S ⟶ T) (n : ℕ)
    (x : S.limitSubmodule) :
    T.limitProj n (limitMap φ x) = (φ.f n).hom (S.limitProj n x) :=
  rfl

/-! ### The limit functor -/

/-- **The limit of an adic tower, as a functor into the `I`-adically complete modules.**  That
the limit is `I`-adically complete is Stacks 09B8, which is where the finite generation of `I`
is used. -/
def limitFunctor (hI : I.FG) :
    AdicTower.{u, v} R I ⥤ IAdicallyCompleteModuleCat.{v} R I where
  obj S := ⟨S.limitModule, S.toInverseSystem.isAdicComplete hI⟩
  map φ := ObjectProperty.homMk (ModuleCat.ofHom (limitMap φ))
  map_id _ := ObjectProperty.hom_ext _
    (ModuleCat.hom_ext (LinearMap.ext fun _ => limit_ext fun _ => rfl))
  map_comp _ _ := ObjectProperty.hom_ext _
    (ModuleCat.hom_ext (LinearMap.ext fun _ => limit_ext fun _ => rfl))

/-- The limit functor sends a morphism of adic towers to the induced map on limits. -/
@[simp]
theorem limitFunctor_map_hom (hI : I.FG) {S T : AdicTower.{u, v} R I} (φ : S ⟶ T) :
    ((limitFunctor hI).map φ).hom.hom = limitMap φ :=
  rfl

/-! ### Full faithfulness -/

/-- The limit functor from adic towers to `I`-adically complete modules is faithful. -/
instance limitFunctor_faithful (hI : I.FG) : (limitFunctor.{u, v} hI).Faithful where
  map_injective {S T} φ ψ h := by
    have h' : limitMap φ = limitMap ψ :=
      congrArg (fun k : (limitFunctor hI).obj S ⟶ (limitFunctor hI).obj T => k.hom.hom) h
    refine Hom.ext (funext fun n => ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
    obtain ⟨x, rfl⟩ := S.limitProj_surjective n y
    simpa using congrArg (T.limitProj n) (LinearMap.congr_fun h' x)

/-- A linear map carries `Iⁿ` into the preimage of `Iⁿ`. -/
theorem pow_smul_top_le_comap {M N : ModuleCat.{v} R} (g : M ⟶ N) (n : ℕ) :
    I ^ n • (⊤ : Submodule R M) ≤ Submodule.comap g.hom (I ^ n • (⊤ : Submodule R N)) :=
  Submodule.map_le_iff_le_comap.1 (map_pow_smul_top_le (I := I) g.hom n)

/-- The `n`-th component of the morphism of towers induced by a linear map of the limits: the
reduction of the map modulo `Iⁿ`, read through the identifications `Mₙ = (lim Mₙ) / Iⁿ` of
Stacks 09B8. -/
def preimageComponent (hI : I.FG) {S T : AdicTower.{u, v} R I}
    (g : S.limitModule ⟶ T.limitModule) (n : ℕ) : S.M n ⟶ T.M n :=
  ModuleCat.ofHom ((T.toInverseSystem.quotientEquiv hI n).toLinearMap ∘ₗ
    Submodule.mapQ _ _ g.hom (pow_smul_top_le_comap g n) ∘ₗ
    (S.toInverseSystem.quotientEquiv hI n).symm.toLinearMap)

/-- The `n`-th component of the morphism induced by a linear map `g` of the limits sends the
`n`-th projection of `x` to the `n`-th projection of `g x`. -/
theorem preimageComponent_limitProj (hI : I.FG) {S T : AdicTower.{u, v} R I}
    (g : S.limitModule ⟶ T.limitModule) (n : ℕ) (x : S.limitSubmodule) :
    (preimageComponent hI g n).hom (S.limitProj n x) = T.limitProj n (g.hom x) := by
  have hsymm : (S.toInverseSystem.quotientEquiv hI n).symm (S.limitProj n x)
      = (Submodule.Quotient.mk x :
          S.limitSubmodule ⧸ (I ^ n • (⊤ : Submodule R S.limitSubmodule))) :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  change (T.toInverseSystem.quotientEquiv hI n)
      (Submodule.mapQ _ _ g.hom (pow_smul_top_le_comap g n)
        ((S.toInverseSystem.quotientEquiv hI n).symm (S.limitProj n x))) = _
  rw [hsymm, Submodule.mapQ_apply]
  rfl

/-- A morphism of adic towers whose limit is a prescribed linear map of the limits. -/
def preimage (hI : I.FG) {S T : AdicTower.{u, v} R I} (g : S.limitModule ⟶ T.limitModule) :
    S ⟶ T where
  f := preimageComponent hI g
  comm n := ModuleCat.hom_ext (LinearMap.ext fun y => by
    obtain ⟨x, rfl⟩ := S.limitProj_surjective (n + 1) y
    change (preimageComponent hI g n).hom ((S.π n).hom (S.limitProj (n + 1) x))
      = (T.π n).hom ((preimageComponent hI g (n + 1)).hom (S.limitProj (n + 1) x))
    rw [S.π_limitProj n x, preimageComponent_limitProj, preimageComponent_limitProj,
      T.π_limitProj n])

/-- The limit functor from adic towers to `I`-adically complete modules is full. -/
instance limitFunctor_full (hI : I.FG) : (limitFunctor.{u, v} hI).Full where
  map_surjective {_ _} g :=
    ⟨preimage hI g.hom, ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x =>
      limit_ext fun n => preimageComponent_limitProj hI g.hom n x))⟩

/-! ### The tower of adic quotients -/

/-- Transition maps between adic quotients compose to transition maps. -/
theorem transitionMap_transitionMap (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    {m n k : ℕ} (h₁ : m ≤ n) (h₂ : n ≤ k) (z : M ⧸ (I ^ k • (⊤ : Submodule R M))) :
    AdicCompletion.transitionMap I M h₁ (AdicCompletion.transitionMap I M h₂ z)
      = AdicCompletion.transitionMap I M (h₁.trans h₂) z := by
  exact Submodule.factor_comp_apply _ _ z

/-- The kernel of the successor transition map `M ⧸ Iⁿ⁺¹M → M ⧸ IⁿM` is `Iⁿ (M ⧸ Iⁿ⁺¹M)`: it is
the image of `Iⁿ M`, and the quotient map is surjective. -/
theorem ker_transitionMap_succ (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    LinearMap.ker (AdicCompletion.transitionMap I M (Nat.le_succ n))
      = I ^ n • (⊤ : Submodule R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))) := by
  have hker : LinearMap.ker (AdicCompletion.transitionMap I M (Nat.le_succ n))
      = Submodule.map (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ
          (I ^ n • (⊤ : Submodule R M)) := by
    rw [AdicCompletion.transitionMap, Submodule.factorPow, Submodule.factor, Submodule.ker_mapQ]
    simp
  rw [hker, Submodule.map_smul'']
  congr 1
  rw [Submodule.map_top, Submodule.range_mkQ]

/-- A family of adic quotients compatible for the successor transitions is compatible for every
pair of levels. -/
theorem transitionMap_of_succ (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (x : ∀ n, M ⧸ (I ^ n • (⊤ : Submodule R M)))
    (hx : ∀ n, AdicCompletion.transitionMap I M (Nat.le_succ n) (x (n + 1)) = x n)
    {m n : ℕ} (h : m ≤ n) : AdicCompletion.transitionMap I M h (x n) = x m := by
  exact (Submodule.eq_factor_of_eq_factor_succ (p := fun n => I ^ n • (⊤ : Submodule R M))
    (fun _ _ le => Submodule.smul_mono_left (Ideal.pow_le_pow_right le)) x
    (fun m => (hx m).symm) h).symm

/-- **The tower of adic quotients** `n ↦ M ⧸ Iⁿ M` of a module, read as an adic tower. -/
def quotientTower (I : Ideal R) (M : ModuleCat.{v} R) : AdicTower.{u, v} R I where
  M n := ModuleCat.of R (M ⧸ (I ^ n • (⊤ : Submodule R M)))
  π n := ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ n))
  surjective n z := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  ker_π n := ker_transitionMap_succ I M n

/-- The limit of the tower of adic quotients of `M` is the `I`-adic completion of `M`.  The two
differ only in whether compatibility of a family is imposed for the successor transitions alone
or for all of them, and the first condition implies the second. -/
def quotientTowerLimitEquiv (I : Ideal R) (M : ModuleCat.{v} R) :
    (quotientTower I M).limitSubmodule ≃ₗ[R] AdicCompletion I M where
  toFun x := ⟨fun n => x.val n,
    fun h => transitionMap_of_succ I M (fun n => x.val n) (fun n => x.property n) h⟩
  invFun y := ⟨fun n => y.val n, fun n => y.property (Nat.le_succ n)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- For an `I`-adically complete module, the limit of its own tower of adic quotients is itself:
that is `AdicCompletion.ofLinearEquiv`, read through `quotientTowerLimitEquiv`. -/
def equivQuotientTowerLimit (I : Ideal R) (M : ModuleCat.{v} R) [IsAdicComplete I M] :
    (M : Type v) ≃ₗ[R] (quotientTower I M).limitSubmodule :=
  (AdicCompletion.ofLinearEquiv I M).trans (quotientTowerLimitEquiv I M).symm

/-! ### Essential surjectivity, and the equivalence -/

/-- The limit functor from adic towers to `I`-adically complete modules is essentially
surjective: every `I`-adically complete module is the limit of its tower of adic quotients. -/
instance limitFunctor_essSurj (hI : I.FG) : (limitFunctor.{u, v} hI).EssSurj where
  mem_essImage N := by
    have := N.property
    exact ⟨quotientTower I N.obj,
      ⟨ObjectProperty.isoMk _ (LinearEquiv.toModuleIso (equivQuotientTowerLimit I N.obj)).symm⟩⟩

/-- The limit functor from adic towers to `I`-adically complete modules is an equivalence. -/
instance limitFunctor_isEquivalence (hI : I.FG) : (limitFunctor.{u, v} hI).IsEquivalence where

/-- **The limit of an adic tower is an equivalence** from the category of adic towers over
`(R, I)`, for `I` finitely generated, to the category of `I`-adically complete `R`-modules.

This is the module-theoretic half of the identification of quasi-coherent modules on a formal
spectrum `Spf(A)` with complete `A`-modules: an adic tower is what such a module restricts to on
the thickenings, and the equivalence says that remembering only the limit loses nothing. -/
def limitEquivalence (hI : I.FG) :
    AdicTower.{u, v} R I ≌ IAdicallyCompleteModuleCat.{v} R I :=
  (limitFunctor hI).asEquivalence

/-! ### Adic towers are not abelian in general -/

/-- An abelian structure on the adic towers over `(R, I)` transports to the `I`-adically
complete `R`-modules along the inverse of `limitEquivalence`.  Finite products are transported
along the same equivalence; preadditivity is inherited from `ModuleCat R`. -/
@[instance_reducible]
def abelianIAdicallyCompleteOfAbelianAdicTower (hI : I.FG)
    (hab : Abelian (AdicTower.{u, v} R I)) : Abelian (IAdicallyCompleteModuleCat.{v} R I) := by
  letI := hab
  letI : Limits.HasFiniteProducts (IAdicallyCompleteModuleCat.{v} R I) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence (limitEquivalence.{u, v} hI).inverse⟩
  exact abelianOfEquivalence (limitEquivalence.{u, v} hI).inverse

/-- **The category of adic towers is not abelian in general.**  Over `ℤ₂` with `I = (2)` the
complete modules are not abelian — that is Stacks 07JR,
`Stacks.Examples.exists_not_abelian_iAdicallyCompleteModuleCat` — and `limitEquivalence`
carries that back to the towers. -/
theorem exists_not_abelian_adicTower :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R),
      I.FG ∧ ¬ Nonempty (Abelian (AdicTower.{u, v} R I)) := by
  obtain ⟨R, hR, I, hI, hna⟩ := exists_not_abelian_iAdicallyCompleteModuleCat.{u, v}
  exact ⟨R, hR, I, hI, fun ⟨hab⟩ =>
    hna ⟨abelianIAdicallyCompleteOfAbelianAdicTower hI hab⟩⟩

end AdicTower

end Stacks.Examples

end
