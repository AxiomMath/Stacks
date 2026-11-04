module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ModuleTower
public import StacksFrontier.Examples.Completion.CompleteModuleCategory
public import StacksFrontier.RingTheory.AdicCompletion.CategoricalLimit

/-!
# Complete modules are the same thing as inverse systems of adic quotients

Let `R` be a commutative ring and `I ⊆ R` a finitely generated ideal.  This file proves that the
category of `I`-adically complete `R`-modules is equivalent to the category of inverse systems
`(M_n)_{n ∈ ℕ}` of `R`-modules whose transition maps exhibit `M_n = M_{n+1} / I^{n+1} M_{n+1}`,
the equivalence being `M ↦ (M / I^{n+1} M)` with quasi-inverse `(M_n) ↦ lim M_n`.

Both directions are already available as statements about modules: `lim M_n` is `I`-adically
complete with `lim M_n / I^{n+1} lim M_n = M_n` by Stacks 09B8, and a complete module is the
limit of its own adic quotients, which is Mathlib's `IsAdicComplete.lift` together with its
uniqueness clause `IsAdicComplete.eq_lift`.  What is done here is the categorical re-gluing: the
assignment `M ↦ (M / I^{n+1} M)` is made into a functor, the universal property of completeness
is read as full faithfulness of that functor, and Stacks 09B8 is read as its essential
surjectivity.

## Main definitions

* `Stacks.Examples.IsAdicModuleSystem`: the condition on a functor `S : ℕᵒᵖ ⥤ ModuleCat R` that
  each transition `S_{n+1} → S_n` be surjective with kernel `I^{n+1} S_{n+1}`.
* `Stacks.Examples.AdicModuleSystems`: the category these systems form, as a full subcategory of
  the category of functors `ℕᵒᵖ ⥤ ModuleCat R`.
* `Stacks.Examples.adicQuotientTower`: the system `n ↦ M / I^{n+1} M` of adic quotients of a
  module, and `Stacks.Examples.adicQuotientTowerFunctor` its functoriality in `M`.
* `Stacks.Examples.completeModuleToAdicSystem`: the comparison functor from complete modules to
  adic systems.
* `Stacks.Examples.iAdicallyCompleteModuleCatEquivAdicModuleSystems`: the equivalence of
  categories.
* `Stacks.Examples.adicQuotientTowerLimitIso`: the identification of a system with the adic
  quotients of its limit, which is the quasi-inverse computed as `lim`.

## Main results

* `Stacks.Examples.completeModuleToAdicSystem_faithful`,
  `Stacks.Examples.completeModuleToAdicSystem_full` and
  `Stacks.Examples.completeModuleToAdicSystem_essSurj`: the three halves of the equivalence.
* `Stacks.Examples.isAdicComplete_limit`: the limit of an adic system is `I`-adically complete.

## Implementation notes

The indexing is the zero-indexed one of `Stacks.Coherent.CoherentAdicSystems` and of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CoherentAdicSystem/ModuleTower.lean`: the term of a
system at `n` plays the role of the Stacks source's `M_{n+1}`, so that it is the quotient of the
next term by the `(n+1)`-st power of `I`, and the degenerate zero term of the source is not
carried.  The bundled `Stacks.AdicCompletion.InverseLimit.InverseSystem` of Stacks 09B8 uses the
other convention, with `ker (π n) = I^n`; the shift between the two is
`Stacks.Coherent.shiftModuleTower`, and the consequences of 09B8 in the present convention are
the `Stacks.Coherent.moduleLimit_*` lemmas, which is why those are what is used below.

Only one universe is in play: `R : Type u` and the modules in `Type u`.  That is forced by the
`Stacks.Coherent.moduleLimit_*` lemmas, which are stated for `ℕᵒᵖ ⥤ ModuleCat.{u} R` with
`R : Type u`, the instantiation in which `ModuleCat` has the `ℕᵒᵖ`-indexed limits that compute
the quasi-inverse.  Nothing in the mathematics needs it.

Finite generation of `I` is used only for essential surjectivity, through Stacks 09B8; the
comparison functor is fully faithful for an arbitrary ideal.  Neither Noetherianness of `R` nor
completeness of `R` itself is needed, and the modules are not assumed finite: the finite case
over a scheme is Stacks 087W, proved in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CoherentAdicSystem/Equivalence.lean`, and does not
cover the present statement.

Finite generation cannot be dropped.  The tower `n ↦ M ⧸ Iⁿ⁺¹ M` of any module whatsoever is an
adic system — that is `Stacks.Examples.isAdicModuleSystem_adicQuotientTower`, which assumes
nothing — and its limit is the completion `M^∧`.  Were the comparison functor essentially
surjective for a non-finitely-generated `I`, every such `M^∧` would be isomorphic to a complete
module, whereas Stacks 05JA exhibits an `M` whose completion is not `I`-adically complete.  The
two clauses of the condition on a system are also not independent of the Stacks source's third
clause that `S_n` be an `R ⧸ Iⁿ⁺¹`-module: that is implied, and recorded as
`Stacks.Examples.IsAdicModuleSystem.pow_smul_top_eq_bot`.

Nothing here carries a `stacks` attribute.  The equivalence is the content of the paragraph
preceding Stacks 0ALG, where it appears as unlabelled prose ("We conclude that the category of
quasi-coherent modules on `X` is equivalent to the category of `p`-adically complete abelian
groups") deduced from Algebra, Lemma 09B8.  Tag 09B8 itself is the statement about one module,
already tagged in `StacksFrontier/RingTheory/AdicCompletion/InverseLimit.lean`, and tag 0ALG is the
non-abelianness of the category of quasi-coherent modules on a formal algebraic space, to which
the present equivalence is only an input.

## References

* [Stacks Project, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
* [Stacks Project, Tag 0ALG](https://stacks.math.columbia.edu/tag/0ALG)
* [Stacks Project, Tag 07JR](https://stacks.math.columbia.edu/tag/07JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Examples

variable {R : Type u} [CommRing R]

/-! ### The tower of adic quotients of a module -/

/-- The kernel of the transition `M ⧸ Iⁿ M → M ⧸ Iᵐ M` is `Iᵐ (M ⧸ Iⁿ M)`, so the tower of adic
quotients of a module satisfies the reduction condition of Stacks 09B8 on the nose. -/
public theorem ker_factorPow_eq_pow_smul_top (I : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] {m n : ℕ} (h : m ≤ n) :
    LinearMap.ker (Submodule.factorPow I M h) =
      I ^ m • (⊤ : Submodule R (M ⧸ (I ^ n • ⊤ : Submodule R M))) := by
  rw [Submodule.factorPow, Submodule.factor, Submodule.mapQ, Submodule.ker_liftQ,
    LinearMap.comp_id, Submodule.ker_mkQ, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)]

/-- The inverse system `n ↦ M ⧸ Iⁿ⁺¹ M` of adic quotients of an `R`-module, with the
exponent-lowering maps as transitions. -/
public def adicQuotientTower (I : Ideal R) (M : ModuleCat.{u} R) : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (M ⧸ (I ^ (n.unop + 1) • ⊤ : Submodule R M))
  map {_ _} a := ModuleCat.ofHom
    (Submodule.factorPow I M (Nat.add_le_add_right (leOfHom a.unop) 1))
  map_id _ := by
    rw [← ModuleCat.ofHom_id]
    exact congrArg ModuleCat.ofHom (Submodule.linearMap_qext _
      (by rw [Submodule.factor_comp_mk, LinearMap.id_comp]))
  map_comp _ _ := by
    rw [← ModuleCat.ofHom_comp]
    exact congrArg ModuleCat.ofHom (Submodule.factor_comp _ _).symm

/-- The transitions of the tower of adic quotients are the exponent-lowering maps. -/
public theorem adicQuotientTower_map (I : Ideal R) (M : ModuleCat.{u} R) {m n : ℕ} (h : n ≤ m) :
    ((adicQuotientTower I M).map (homOfLE h).op).hom =
      Submodule.factorPow I M (Nat.add_le_add_right h 1) :=
  rfl

/-- A linear map of modules induces a morphism of the towers of adic quotients. -/
public def adicQuotientTowerMap (I : Ideal R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    adicQuotientTower I M ⟶ adicQuotientTower I N where
  app n := ModuleCat.ofHom (Submodule.mapQ _ _ f.hom
    (Submodule.map_le_iff_le_comap.mp (map_pow_smul_top_le f.hom (n.unop + 1))))
  naturality _ _ _ := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ ?_)
    exact LinearMap.ext fun _ => rfl

/-- The components of `Stacks.Examples.adicQuotientTowerMap` on a class. -/
public theorem adicQuotientTowerMap_app_mk (I : Ideal R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (n : ℕᵒᵖ) (x : M) :
    ((adicQuotientTowerMap I f).app n).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.hom x) :=
  rfl

/-- The tower of adic quotients, as a functor of the module. -/
public def adicQuotientTowerFunctor (I : Ideal R) :
    ModuleCat.{u} R ⥤ (ℕᵒᵖ ⥤ ModuleCat.{u} R) where
  obj M := adicQuotientTower I M
  map f := adicQuotientTowerMap I f
  map_id _ := by
    refine NatTrans.ext (funext fun _ => ?_)
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ ?_)
    exact LinearMap.ext fun _ => rfl
  map_comp _ _ := by
    refine NatTrans.ext (funext fun _ => ?_)
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ ?_)
    exact LinearMap.ext fun _ => rfl

/-! ### The category of adic systems of modules -/

/-- The defining condition of an adic inverse system of modules along `I`: each transition
`S_{n+1} → S_n` is surjective with kernel exactly `Iⁿ⁺¹ S_{n+1}`, that is,
`S_n = S_{n+1} / Iⁿ⁺¹ S_{n+1}`. -/
public def IsAdicModuleSystem (I : Ideal R) (S : ℕᵒᵖ ⥤ ModuleCat.{u} R) : Prop :=
  (∀ n : ℕ, Function.Surjective ((S.map (homOfLE (Nat.le_succ n)).op).hom)) ∧
    (∀ n : ℕ, LinearMap.ker ((S.map (homOfLE (Nat.le_succ n)).op).hom) =
      I ^ (n + 1) • (⊤ : Submodule R (S.obj (op (n + 1)))))

/-- The terms of an adic system are annihilated by the corresponding power of `I`, so that `S_n`
is a module over `R ⧸ Iⁿ⁺¹`.  This is a consequence of the defining condition and not a further
hypothesis: `Iⁿ⁺¹ S_n` is the image of `Iⁿ⁺¹ S_{n+1} = ker (S_{n+1} → S_n)`. -/
public theorem IsAdicModuleSystem.pow_smul_top_eq_bot {I : Ideal R} {S : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    (hS : IsAdicModuleSystem I S) (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule R (S.obj (op n))) = ⊥ := by
  have hmap : Submodule.map ((S.map (homOfLE (Nat.le_succ n)).op).hom)
      (I ^ (n + 1) • ⊤) = (I ^ (n + 1) • ⊤ : Submodule R (S.obj (op n))) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (hS.1 n)]
  rw [← hmap, ← hS.2 n, eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  simpa using hy

/-- The category of adic inverse systems of `R`-modules along `I`, as a full subcategory of the
category of functors `ℕᵒᵖ ⥤ ModuleCat R`: a morphism of systems is a natural transformation of
the underlying functors. -/
public abbrev AdicModuleSystems (I : Ideal R) :=
  ObjectProperty.FullSubcategory (C := ℕᵒᵖ ⥤ ModuleCat.{u} R) (IsAdicModuleSystem I)

/-- The tower of adic quotients of any module is an adic system: the exponent-lowering maps are
surjective and their kernels are the ideal-power multiples. -/
public theorem isAdicModuleSystem_adicQuotientTower (I : Ideal R) (M : ModuleCat.{u} R) :
    IsAdicModuleSystem I (adicQuotientTower I M) := by
  refine ⟨fun n => ?_, fun n => ?_⟩ <;> rw [adicQuotientTower_map]
  exacts [Submodule.factor_surjective _, ker_factorPow_eq_pow_smul_top I M _]

/-- The comparison functor: an `I`-adically complete module goes to its tower of adic
quotients. -/
public def completeModuleToAdicSystem (I : Ideal R) :
    IAdicallyCompleteModuleCat.{u} R I ⥤ AdicModuleSystems.{u} I :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ adicQuotientTowerFunctor I)
    fun X => isAdicModuleSystem_adicQuotientTower I X.obj

/-- The components of the comparison functor on a morphism. -/
public theorem completeModuleToAdicSystem_map_app_mk (I : Ideal R)
    {X Y : IAdicallyCompleteModuleCat.{u} R I} (f : X ⟶ Y) (n : ℕᵒᵖ) (x : X.obj) :
    (((completeModuleToAdicSystem I).map f).hom.app n).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f.hom.hom x) :=
  rfl

/-! ### Full faithfulness

Both halves are the universal property of `I`-adic completeness: a map into a complete module is
determined by, and can be prescribed through, its reductions modulo the powers of `I`.  This is
`IsAdicComplete.eq_lift` and `IsAdicComplete.lift` in Mathlib.  The only bookkeeping is the
missing level `0`, where the quotient `N ⧸ I⁰ N` is a subsingleton and the component of the
family is forced to be the zero map. -/

/-- Two elements of a Hausdorff module with the same class modulo every `Iⁿ⁺¹` are equal. -/
public theorem eq_of_mk_eq_of_isHausdorff {M : Type u} [AddCommGroup M] [Module R M]
    (I : Ideal R) (hM : IsHausdorff I M) {x y : M}
    (h : ∀ n : ℕ, (Submodule.Quotient.mk x : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) =
      Submodule.Quotient.mk y) : x = y := by
  refine sub_eq_zero.mp (hM.haus (x - y) fun n => SModEq.zero.mpr ?_)
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))
    ((Submodule.Quotient.eq _).mp (h n))

/-- The comparison functor is faithful: a map into a complete module is determined by its
reductions modulo the powers of `I`. -/
public theorem completeModuleToAdicSystem_faithful (I : Ideal R) :
    (completeModuleToAdicSystem I).Faithful := by
  constructor
  intro X Y f g h
  refine ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  refine eq_of_mk_eq_of_isHausdorff I Y.property.toIsHausdorff fun n => ?_
  rw [← completeModuleToAdicSystem_map_app_mk I f (op n) x,
    ← completeModuleToAdicSystem_map_app_mk I g (op n) x, h]

/-- The level-`0` adic quotient of a module is a subsingleton. -/
private theorem subsingleton_quotient_zero (I : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] : Subsingleton (M ⧸ (I ^ 0 • ⊤ : Submodule R M)) :=
  AdicCompletion.subsingleton_quotient_pow_zero_smul_top I M

/-- The family of reductions `M → N ⧸ Iⁿ N` attached to a morphism of adic quotient towers.  The
component at level `0` is the zero map, that quotient being a subsingleton; the component at
level `n + 1` is the component of the morphism at `n`, precomposed with the projection. -/
private def towerHomFamily (I : Ideal R) {M N : ModuleCat.{u} R}
    (τ : adicQuotientTower I M ⟶ adicQuotientTower I N) :
    ∀ n : ℕ, M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)
  | 0 => 0
  | k + 1 => (τ.app (op k)).hom ∘ₗ Submodule.mkQ _

private theorem towerHomFamily_succ (I : Ideal R) {M N : ModuleCat.{u} R}
    (τ : adicQuotientTower I M ⟶ adicQuotientTower I N) (k : ℕ) (x : M) :
    towerHomFamily I τ (k + 1) x = (τ.app (op k)).hom (Submodule.Quotient.mk x) :=
  rfl

/-- The family `Stacks.Examples.towerHomFamily` is compatible with the exponent-lowering maps:
this is the naturality of the morphism of towers. -/
private theorem towerHomFamily_compat (I : Ideal R) {M N : ModuleCat.{u} R}
    (τ : adicQuotientTower I M ⟶ adicQuotientTower I N) {m n : ℕ} (hle : m ≤ n) :
    Submodule.factorPow I N hle ∘ₗ towerHomFamily I τ n = towerHomFamily I τ m := by
  obtain _ | k := m
  · have := subsingleton_quotient_zero I N
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  obtain _ | l := n
  · omega
  exact LinearMap.ext fun x => (congrArg
    (fun φ : (adicQuotientTower I M).obj (op l) ⟶ (adicQuotientTower I N).obj (op k) =>
      φ.hom (Submodule.Quotient.mk x))
    (τ.naturality (homOfLE (Nat.le_of_succ_le_succ hle)).op)).symm

/-- A morphism between the towers of adic quotients of two modules, the target being complete, is
induced by a linear map: this is the universal property `IsAdicComplete.lift`. -/
private theorem exists_hom_of_towerHom (I : Ideal R) {M N : ModuleCat.{u} R}
    (hN : IsAdicComplete I N) (τ : adicQuotientTower I M ⟶ adicQuotientTower I N) :
    ∃ F : M ⟶ N, ∀ (n : ℕ) (x : M),
      (Submodule.Quotient.mk (F.hom x) : N ⧸ (I ^ (n + 1) • ⊤ : Submodule R N)) =
        (τ.app (op n)).hom (Submodule.Quotient.mk x) :=
  ⟨ModuleCat.ofHom (IsAdicComplete.lift I (towerHomFamily I τ) (towerHomFamily_compat I τ)),
    fun n x => (IsAdicComplete.mk_lift I (towerHomFamily_compat I τ) (n + 1) x).trans
      (towerHomFamily_succ I τ n x)⟩

/-- The comparison functor is full: a morphism between the towers of adic quotients of two
complete modules comes from a linear map, by the universal property of completeness. -/
public theorem completeModuleToAdicSystem_full (I : Ideal R) :
    (completeModuleToAdicSystem I).Full := by
  constructor
  intro X Y τ
  obtain ⟨F, hF⟩ := exists_hom_of_towerHom I (N := Y.obj) Y.property τ.hom
  refine ⟨ObjectProperty.homMk F, ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))⟩
  refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
  exact hF n.unop x

/-! ### Essential surjectivity

This is Stacks 09B8, in the form of the `Stacks.Coherent.moduleLimit_*` lemmas: the limit of an
adic system is complete, and its projections identify the system with the system of adic
quotients of the limit. -/

variable {I : Ideal R}

/-- The limit of an adic system of modules is `I`-adically complete; this is Stacks 09B8 (2). -/
public theorem isAdicComplete_limit (hI : I.FG) (S : AdicModuleSystems.{u} I) :
    IsAdicComplete I (limit S.obj : ModuleCat.{u} R) :=
  Stacks.Coherent.moduleLimit_isAdicComplete S.obj S.property.1 S.property.2 hI

/-- The level-`n` adic quotient of the limit of an adic system, identified with the `n`-th term of
the system by the limit projection; this is Stacks 09B8 (1). -/
public def limitQuotientEquiv (hI : I.FG) (S : AdicModuleSystems.{u} I) (n : ℕ) :
    ((limit S.obj : ModuleCat.{u} R) ⧸
        (I ^ (n + 1) • ⊤ : Submodule R (limit S.obj : ModuleCat.{u} R))) ≃ₗ[R]
      S.obj.obj (op n) :=
  (Submodule.quotEquivOfEq _ _
      (Stacks.Coherent.moduleLimit_projection_ker S.obj S.property.1 S.property.2 hI n).symm).trans
    ((limit.π S.obj (op n)).hom.quotKerEquivOfSurjective
      (Stacks.Coherent.moduleLimit_projection_surjective S.obj S.property.1 n))

/-- `limitQuotientEquiv` sends the class of `x` in the level-`n` adic quotient of the limit to the
image of `x` under the `n`-th limit projection. -/
@[simp]
public theorem limitQuotientEquiv_mk (hI : I.FG) (S : AdicModuleSystems.{u} I) (n : ℕ)
    (x : (limit S.obj : ModuleCat.{u} R)) :
    limitQuotientEquiv hI S n (Submodule.Quotient.mk x) = (limit.π S.obj (op n)).hom x :=
  rfl

/-- An adic system is the system of adic quotients of its own limit: the object half of
Stacks 09B8, read as an isomorphism of systems. -/
public def adicQuotientTowerLimitIso (hI : I.FG) (S : AdicModuleSystems.{u} I) :
    adicQuotientTower I (limit S.obj) ≅ S.obj :=
  NatIso.ofComponents (fun n => (limitQuotientEquiv hI S n.unop).toModuleIso) fun {m n} a => by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change limitQuotientEquiv hI S n.unop
        (((adicQuotientTower I (limit S.obj)).map a).hom (Submodule.Quotient.mk x)) =
      (S.obj.map a).hom ((limit.π S.obj (op m.unop)).hom x)
    rw [show ((adicQuotientTower I (limit S.obj)).map a).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x from rfl, limitQuotientEquiv_mk]
    exact congrArg (fun φ : (limit S.obj : ModuleCat.{u} R) ⟶ S.obj.obj n => φ.hom x)
      (limit.w S.obj a).symm

/-- The comparison functor is essentially surjective: every adic system is, up to isomorphism,
the tower of adic quotients of the complete module `lim S_n`. -/
public theorem completeModuleToAdicSystem_essSurj (hI : I.FG) :
    (completeModuleToAdicSystem I).EssSurj :=
  ⟨fun S => ⟨⟨limit S.obj, isAdicComplete_limit hI S⟩,
    ⟨ObjectProperty.isoMk _ (adicQuotientTowerLimitIso hI S)⟩⟩⟩

/-! ### The equivalence -/

/-- The comparison functor is an equivalence. -/
public theorem completeModuleToAdicSystem_isEquivalence (hI : I.FG) :
    (completeModuleToAdicSystem I).IsEquivalence where
  faithful := completeModuleToAdicSystem_faithful I
  full := completeModuleToAdicSystem_full I
  essSurj := completeModuleToAdicSystem_essSurj hI

/-- For a finitely generated ideal `I` of a commutative ring `R`, the category of `I`-adically
complete `R`-modules is equivalent to the category of inverse systems `(M_n)` of `R`-modules with
`M_n = M_{n+1} / Iⁿ⁺¹ M_{n+1}`.  The functor is `M ↦ (M / Iⁿ⁺¹ M)`; its quasi-inverse is
`(M_n) ↦ lim M_n`, as `Stacks.Examples.adicQuotientTowerLimitIso` records.

This is the categorical form of Stacks 09B8, and the input to the discussion preceding Stacks
0ALG.  No finiteness of the modules is assumed, and `R` is neither Noetherian nor complete. -/
public def iAdicallyCompleteModuleCatEquivAdicModuleSystems (hI : I.FG) :
    IAdicallyCompleteModuleCat.{u} R I ≌ AdicModuleSystems.{u} I :=
  have : (completeModuleToAdicSystem I).IsEquivalence :=
    completeModuleToAdicSystem_isEquivalence hI
  (completeModuleToAdicSystem I).asEquivalence

end Stacks.Examples

end
