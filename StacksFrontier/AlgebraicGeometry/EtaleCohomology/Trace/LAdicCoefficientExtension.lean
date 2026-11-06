module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# ℓ-adic sheaves with coefficients in a finite extension of `ℤ_ℓ`

For `O_λ` the ring of integers of a finite extension of `ℚ_ℓ` (e.g. `O_λ ⊇ ℤ_ℓ[ζ_p]`, the
coefficients of the Artin–Schreier sheaves `L_ψ`), `O_λ` is finite over `ℤ_ℓ`, its `λ`-adic and
`ℓ`-adic topologies coincide, and an `O_λ`-sheaf is the same as an ℓ-adic sheaf with an action of
`O_λ` by endomorphisms [Weil II, 1.1.1], [SGA 5, VI 1.5].  In terms of the `ℤ_ℓ`-sheaves
`AlgebraicGeometry.SmallEtale.LAdicSheaf`:

* every ℓ-adic sheaf carries the canonical `ℤ_ℓ`-action `LAdicSheaf.scalarRingHom`, and it is the
  only ring homomorphism `ℤ_ℓ → End F` (`LAdicSheaf.eq_scalarRingHom`), so an action of a
  `ℤ_ℓ`-algebra is automatically `ℤ_ℓ`-linear;
* `LAdicSheaf.CoefficientSheaf B X ℓ O`: an ℓ-adic sheaf with an action of `O`; its field
  `toLAdicSheaf` is restriction of scalars to `ℤ_ℓ`;
* `LAdicSheaf.extendScalars F b`: extension of scalars `F ⊗_{ℤ_ℓ} O = ⨁_ι F` along a finite free
  `ℤ_ℓ`-algebra `O` with basis `b`, `O` acting by the matrices of multiplication;
* stalks and `Hⁱ_c(X_k̄, -)` of an `O`-sheaf are `O`-modules, compatibly with their `ℤ_ℓ`-module
  structure (`IsScalarTower`), and the geometric Frobenius on stalks and `π_X^*` on `Hⁱ_c` are
  `O`-linear (`LAdicSheaf.CoefficientSheaf.stalkEnd`,
  `LAdicSheaf.CoefficientSheaf.geometricCompactlySupportedFrobenius`), restricting to the
  `ℤ_ℓ`-linear ones.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {B X ℓ}

/-- Multiples of a morphism of sheaves of `R`-modules, on sections. -/
public theorem sheaf_nsmul_hom_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Type} [Ring R] {P Q : Sheaf J (ModuleCat.{u + 1} R)} (k : ℕ) (g : P ⟶ Q) (U : Cᵒᵖ)
    (x : P.obj.obj U) : ((k • g).hom.app U).hom x = k • (g.hom.app U).hom x :=
  rfl

/-- Two morphisms of ℓ-adic sheaves agreeing on all sections at all levels are equal. -/
public theorem LAdicSheaf.hom_ext_apply {F G : LAdicSheaf B X ℓ} {φ ψ : F ⟶ G}
    (h : ∀ n U x, ((φ.app n).hom.app U).hom x = ((ψ.app n).hom.app U).hom x) : φ = ψ :=
  AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext B X ℓ fun n => by
    ext U x
    exact h n U x

/-! ### The canonical `ℤ_ℓ`-action -/

/-- In a `ℤ/Nℤ`-module, multiples by natural numbers with the same residue agree. -/
public theorem nsmul_eq_of_natCast_eq {N : ℕ} (M : Type*) [AddCommGroup M] [Module (ZMod N) M]
    {k k' : ℕ} (h : (k : ZMod N) = k') (y : M) : k • y = k' • y := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod N), h, Nat.cast_smul_eq_nsmul]

/-- In a `ℤ/Nℤ`-module, the natural number `a.val` acts as `a`. -/
private theorem val_nsmul_eq_smul {N : ℕ} [NeZero N] {M : Type*} [AddCommGroup M]
    [Module (ZMod N) M] (a : ZMod N) (y : M) : a.val • y = a • y := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_val, ZMod.cast_id', id]

/-- Multiplication by `c ∈ ℤ_ℓ` on an ℓ-adic sheaf: on level `n` it is multiplication by the
reduction of `c` modulo `ℓⁿ⁺¹`. -/
public def LAdicSheaf.scalarEnd (F : LAdicSheaf B X ℓ) (c : ℤ_[ℓ]) : F ⟶ F where
  app n := (PadicInt.toZModPow (n + 1) c).val • 𝟙 (F.level n)
  naturality n := by
    rw [Preadditive.nsmul_comp, Category.id_comp, Functor.map_nsmul, Preadditive.comp_nsmul,
      CategoryTheory.Functor.map_id, Category.comp_id]
    ext U x
    exact nsmul_eq_of_natCast_eq (N := ℓ ^ (n + 1)) ((F.level n).obj.obj U)
      (by rw [ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id', id,
        ← PadicInt.cast_toZModPow (n + 1) (n + 2) (by omega) c, ZMod.cast_eq_val,
        ZMod.natCast_val]) (((F.transition n).hom.app U).hom x)

/-- On sections, multiplication by `c` is the scalar action of its reduction. -/
public theorem LAdicSheaf.scalarEnd_app_apply (F : LAdicSheaf B X ℓ) (c : ℤ_[ℓ]) (n : ℕ) (U)
    (x : (F.level n).obj.obj U) :
    (((LAdicSheaf.scalarEnd F c).app n).hom.app U).hom x = PadicInt.toZModPow (n + 1) c • x := by
  exact val_nsmul_eq_smul _ x

/-- On sections, the identity of an ℓ-adic sheaf is the identity. -/
public theorem LAdicSheaf.id_app_apply (F : LAdicSheaf B X ℓ) (n : ℕ) (U)
    (x : (F.level n).obj.obj U) : (((𝟙 F : F ⟶ F).app n).hom.app U).hom x = x :=
  rfl

/-- On sections, a composite of morphisms of ℓ-adic sheaves is the composite of the components. -/
public theorem LAdicSheaf.comp_app_apply {F G H : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ H)
    (n : ℕ) (U) (x : (F.level n).obj.obj U) :
    (((φ ≫ ψ).app n).hom.app U).hom x =
      ((ψ.app n).hom.app U).hom (((φ.app n).hom.app U).hom x) :=
  rfl

/-- On sections, a sum of morphisms of ℓ-adic sheaves is the sum of the components. -/
public theorem LAdicSheaf.add_app_apply {F G : LAdicSheaf B X ℓ} (φ ψ : F ⟶ G) (n : ℕ) (U)
    (x : (F.level n).obj.obj U) :
    (((φ + ψ).app n).hom.app U).hom x =
      ((φ.app n).hom.app U).hom x + ((ψ.app n).hom.app U).hom x :=
  rfl

/-- On sections, the zero morphism of ℓ-adic sheaves is zero. -/
public theorem LAdicSheaf.zero_app_apply (F G : LAdicSheaf B X ℓ) (n : ℕ) (U)
    (x : (F.level n).obj.obj U) : (((0 : F ⟶ G).app n).hom.app U).hom x = 0 :=
  rfl

/-- **The canonical `ℤ_ℓ`-algebra structure on `End F`**: `c ↦` multiplication by `c`. -/
public def LAdicSheaf.scalarRingHom (F : LAdicSheaf B X ℓ) : ℤ_[ℓ] →+* End F where
  toFun c := End.of (LAdicSheaf.scalarEnd F c)
  map_one' := by
    refine End.ext (LAdicSheaf.hom_ext_apply (fun n U x => ?_))
    change (((LAdicSheaf.scalarEnd F 1).app n).hom.app U).hom x = x
    rw [LAdicSheaf.scalarEnd_app_apply, map_one, one_smul]
  map_mul' c d := by
    refine End.ext (LAdicSheaf.hom_ext_apply (fun n U x => ?_))
    change (((LAdicSheaf.scalarEnd F (c * d)).app n).hom.app U).hom x = _
    rw [LAdicSheaf.scalarEnd_app_apply, map_mul, mul_smul]
    change _ = (((LAdicSheaf.scalarEnd F c).app n).hom.app U).hom
      ((((LAdicSheaf.scalarEnd F d).app n).hom.app U).hom x)
    rw [LAdicSheaf.scalarEnd_app_apply, LAdicSheaf.scalarEnd_app_apply]
  map_zero' := by
    refine End.ext (LAdicSheaf.hom_ext_apply (fun n U x => ?_))
    change (((LAdicSheaf.scalarEnd F 0).app n).hom.app U).hom x = 0
    rw [LAdicSheaf.scalarEnd_app_apply, map_zero, zero_smul]
  map_add' c d := by
    refine End.ext (LAdicSheaf.hom_ext_apply (fun n U x => ?_))
    change (((LAdicSheaf.scalarEnd F (c + d)).app n).hom.app U).hom x =
      (((LAdicSheaf.scalarEnd F c + LAdicSheaf.scalarEnd F d).app n).hom.app U).hom x
    rw [LAdicSheaf.scalarEnd_app_apply, map_add, add_smul, LAdicSheaf.add_app_apply,
      LAdicSheaf.scalarEnd_app_apply, LAdicSheaf.scalarEnd_app_apply]

/-- The canonical `ℤ_ℓ`-action sends `c` to multiplication by `c`. -/
@[simp]
public theorem LAdicSheaf.scalarRingHom_apply (F : LAdicSheaf B X ℓ) (c : ℤ_[ℓ]) :
    (LAdicSheaf.scalarRingHom F c).asHom = LAdicSheaf.scalarEnd F c :=
  rfl

/-- A `ℓ`-adic integer is its residue modulo `ℓⁿ⁺¹` plus a multiple of `ℓⁿ⁺¹`. -/
public theorem exists_eq_toZModPow_val_add (c : ℤ_[ℓ]) (n : ℕ) :
    ∃ d : ℤ_[ℓ], c = ((PadicInt.toZModPow (n + 1) c).val : ℤ_[ℓ]) + (ℓ : ℤ_[ℓ]) ^ (n + 1) * d := by
  have hmem : c - ((PadicInt.toZModPow (n + 1) c).val : ℤ_[ℓ]) ∈
      RingHom.ker (PadicInt.toZModPow (p := ℓ) (n + 1)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_val, ZMod.cast_id', id, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, by rw [mul_comm, hd]; ring⟩

/-- In a `ℤ_ℓ`-module killed by `ℓⁿ⁺¹`, a scalar acts as its residue modulo `ℓⁿ⁺¹`. -/
public theorem smul_eq_toZModPow_val_nsmul {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] (n : ℕ)
    (y : M) (hy : (ℓ ^ (n + 1)) • y = 0) (c : ℤ_[ℓ]) :
    c • y = (PadicInt.toZModPow (n + 1) c).val • y := by
  obtain ⟨d, hd⟩ := exists_eq_toZModPow_val_add (ℓ := ℓ) c n
  conv_lhs => rw [hd]
  rw [add_smul, Nat.cast_smul_eq_nsmul, mul_comm, mul_smul, ← Nat.cast_pow,
    Nat.cast_smul_eq_nsmul, hy, smul_zero, add_zero]

/-- A morphism of sheaves of `ℤ/Nℤ`-modules is killed by `N`. -/
public theorem sheaf_natCast_nsmul_eq_zero {C : Type*} [Category C] {J : GrothendieckTopology C}
    {N : ℕ} {P Q : Sheaf J (ModuleCat.{u + 1} (ZMod N))} (g : P ⟶ Q) : N • g = 0 := by
  ext U x
  show N • (g.hom.app U).hom x = 0
  rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul]

/-- **Every ring homomorphism `ℤ_ℓ → End F` is the canonical one.**  In particular an action of a
`ℤ_ℓ`-algebra `O` on `F` by endomorphisms is automatically `ℤ_ℓ`-linear. -/
public theorem LAdicSheaf.eq_scalarRingHom (F : LAdicSheaf B X ℓ) (φ : ℤ_[ℓ] →+* End F) :
    φ = LAdicSheaf.scalarRingHom F := by
  ext c : 1
  refine End.ext (AlgebraicGeometry.SmallEtale.LAdicSheaf.Hom.ext B X ℓ fun n => ?_)
  obtain ⟨d, hd⟩ := exists_eq_toZModPow_val_add (ℓ := ℓ) c n
  have e1 : (((PadicInt.toZModPow (n + 1) c).val : End F)).asHom.app n =
      (PadicInt.toZModPow (n + 1) c).val • 𝟙 (F.level n) := by
    rw [← nsmul_one]
    rfl
  have e2 : (((ℓ : End F) ^ (n + 1) * φ d : End F)).asHom.app n = 0 := by
    rw [← Nat.cast_pow, ← nsmul_one, smul_mul_assoc, one_mul]
    exact sheaf_natCast_nsmul_eq_zero (N := ℓ ^ (n + 1)) ((φ d).asHom.app n)
  calc (φ c).asHom.app n
      = (((PadicInt.toZModPow (n + 1) c).val : End F) + (ℓ : End F) ^ (n + 1) * φ d).asHom.app n := by
        refine congrArg (fun e : End F => e.asHom.app n) ?_
        conv_lhs => rw [hd]
        rw [map_add, map_mul, map_pow, map_natCast, map_natCast]
    _ = (((PadicInt.toZModPow (n + 1) c).val : End F)).asHom.app n +
          (((ℓ : End F) ^ (n + 1) * φ d : End F)).asHom.app n := rfl
    _ = (LAdicSheaf.scalarRingHom F c).asHom.app n := by
        rw [e1, e2, add_zero]
        rfl

/-! ### Multiplication by `c` on stalks -/

/-- The map of level-`n` stalks induced by a morphism depends only on its level-`n` component. -/
public theorem finiteLevelStalkMap_congr {F G : LAdicSheaf B X ℓ} {φ ψ : F ⟶ G}
    (s : GeometricPoint X.1) (n : ℕ) (h : φ.app n = ψ.app n) :
    finiteLevelStalkMap φ s n = finiteLevelStalkMap ψ s n := by
  unfold finiteLevelStalkMap
  rw [h]

/-- The map of finite-level stalks as an additive map of morphism groups. -/
public def finiteLevelStalkMapAddHom (F G : LAdicSheaf B X ℓ) (s : GeometricPoint X.1) (n : ℕ) :
    (F ⟶ G) →+ (finiteLevelStalk B X ℓ F s n ⟶ finiteLevelStalk B X ℓ G s n) where
  toFun φ := finiteLevelStalkMap φ s n
  map_zero' := finiteLevelStalkMap_zero F G s n
  map_add' φ ψ := finiteLevelStalkMap_add φ ψ s n

/-- **Multiplication by `c ∈ ℤ_ℓ` acts on the ℓ-adic stalk as the scalar `c`.** -/
public theorem LAdicSheaf.stalkMap_scalarEnd (F : LAdicSheaf B X ℓ) (s : GeometricPoint X.1)
    (c : ℤ_[ℓ]) (v : LAdicSheaf.stalk B X ℓ F s) :
    LAdicSheaf.stalkMap (LAdicSheaf.scalarEnd F c) s v = c • v := by
  apply Subtype.ext
  funext n
  have h : finiteLevelStalkMap (LAdicSheaf.scalarEnd F c) s n =
      (PadicInt.toZModPow (n + 1) c).val • 𝟙 _ := by
    rw [finiteLevelStalkMap_congr s n (φ := LAdicSheaf.scalarEnd F c)
      (ψ := (PadicInt.toZModPow (n + 1) c).val • 𝟙 F) rfl]
    show finiteLevelStalkMapAddHom F F s n _ = _
    rw [map_nsmul]
    show _ • finiteLevelStalkMap (𝟙 F) s n = _
    rw [finiteLevelStalkMap_id]
  show (finiteLevelStalkMap (LAdicSheaf.scalarEnd F c) s n).hom (v.1 n) =
    PadicInt.toZModPow (n + 1) c • v.1 n
  rw [h]
  exact val_nsmul_eq_smul _ (v.1 n)

/-! ### Multiplication by `c` on `Hⁱ_c(X_k̄, F)` -/

section CompactSupport

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- On the level-`n` sheaf, multiplication by `c` is multiplication by the residue of `c` modulo
`ℓⁿ⁺¹`. -/
public theorem LAdicSheaf.padicLevelMap_scalarEnd (F : LAdicSheaf B X ℓ) (c : ℤ_[ℓ]) (n : ℕ) :
    LAdicSheaf.padicLevelMap (LAdicSheaf.scalarEnd F c) n =
      (PadicInt.toZModPow (n + 1) c).val • 𝟙 (LAdicSheaf.padicLevel B X ℓ F n) := by
  ext U x
  rfl

/-- `ℓⁿ⁺¹` times the identity of the level-`n` sheaf `Fₙ` is zero. -/
public theorem LAdicSheaf.pow_nsmul_id_padicLevel (F : LAdicSheaf B X ℓ) (n : ℕ) :
    (ℓ ^ (n + 1)) • 𝟙 (LAdicSheaf.padicLevel B X ℓ F n) = 0 := by
  ext U x
  exact (nsmul_eq_of_natCast_eq (N := ℓ ^ (n + 1)) ((F.level n).obj.obj U)
    (k := ℓ ^ (n + 1)) (k' := 0) (by rw [ZMod.natCast_self, Nat.cast_zero]) x).trans (zero_smul _ _)

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- `ℓⁿ⁺¹` kills `Hⁱ_c(X_k̄, Fₙ)`. -/
public theorem LAdicSheaf.pow_nsmul_geometricCompactSupportPadicCohomology (F : LAdicSheaf B X ℓ)
    (i : ℤ) (n : ℕ)
    (y : (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ F n)) :
    (ℓ ^ (n + 1)) • y = 0 := by
  have h : (ℓ ^ (n + 1)) • 𝟙 ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ F n)) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul,
      LAdicSheaf.pow_nsmul_id_padicLevel, Functor.map_zero]
  exact (ConcreteCategory.congr_hom h y : _)

/-- **Multiplication by `c ∈ ℤ_ℓ` acts on `Hⁱ_c(X_k̄, F)` as the scalar `c`.** -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologyMap_scalarEnd
    (F : LAdicSheaf B X ℓ) (i : ℤ) (c : ℤ_[ℓ])
    (v : LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F i) :
    (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar
      (LAdicSheaf.scalarEnd F c) i).hom v = c • v := by
  refine Concrete.limit_ext _ _ _ fun n => ?_
  induction n using Opposite.rec with | op n => ?_
  show (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar
      (LAdicSheaf.scalarEnd F c) i ≫
    LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n).hom v =
    (LAdicSheaf.geometricCompactlySupportedCohomologyπ B X ℓ f j kbar F i n).hom (c • v)
  rw [LAdicSheaf.geometricCompactlySupportedCohomologyMap_π, LAdicSheaf.padicLevelMap_scalarEnd,
    Functor.map_nsmul, CategoryTheory.Functor.map_id, map_smul,
    smul_eq_toZModPow_val_nsmul n _
      (LAdicSheaf.pow_nsmul_geometricCompactSupportPadicCohomology f j kbar F i n _)]
  rfl

end CompactSupport

/-! ### ℓ-adic sheaves with coefficients in a finite `ℤ_ℓ`-algebra -/

variable (B X ℓ) in
/-- **An ℓ-adic sheaf with coefficients in a `ℤ_ℓ`-algebra `O`** (an `O_λ`-sheaf when `O` is the
ring of integers of a finite extension `E_λ` of `ℚ_ℓ`): an ℓ-adic sheaf together with an action of
`O` by endomorphisms.  As `O` is finite over `ℤ_ℓ`, its `λ`-adic and `ℓ`-adic topologies agree,
so this is the notion of [Weil II, 1.1.1] and [SGA 5, VI 1.5]; the action is automatically
`ℤ_ℓ`-linear (`LAdicSheaf.CoefficientSheaf.act_algebraMap`).  Forgetting the action is
restriction of scalars to `ℤ_ℓ`. -/
public structure LAdicSheaf.CoefficientSheaf (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O] where
  /-- The underlying ℓ-adic sheaf: the restriction of scalars to `ℤ_ℓ`. -/
  toLAdicSheaf : LAdicSheaf B X ℓ
  /-- The action of `O` by endomorphisms. -/
  act : O →+* End toLAdicSheaf

namespace LAdicSheaf.CoefficientSheaf

variable {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O)

/-- The action of `O` extends the canonical action of `ℤ_ℓ`. -/
public theorem act_algebraMap (c : ℤ_[ℓ]) :
    (F.act (algebraMap ℤ_[ℓ] O c)).asHom = LAdicSheaf.scalarEnd F.toLAdicSheaf c :=
  congrArg End.asHom
    (RingHom.congr_fun (LAdicSheaf.eq_scalarRingHom F.toLAdicSheaf (F.act.comp (algebraMap _ _))) c)

/-- The `O`-module structure on the ℓ-adic stalk, through the action of `O` on the sheaf. -/
public instance stalkModule (s : GeometricPoint X.1) :
    Module O (LAdicSheaf.stalk B X ℓ F.toLAdicSheaf s) :=
  Module.compHom _ ((LAdicSheaf.stalkEndRingHom F.toLAdicSheaf s).comp F.act)

/-- `o ∈ O` acts on the stalk of an `O`-sheaf as the stalk map of its action on the sheaf. -/
public theorem smul_stalk_def (s : GeometricPoint X.1) (o : O)
    (v : LAdicSheaf.stalk B X ℓ F.toLAdicSheaf s) :
    o • v = LAdicSheaf.stalkMap (F.act o).asHom s v :=
  rfl

/-- The `O`-module structure on the stalk of an `O`-sheaf extends its `ℤ_ℓ`-module structure. -/
public instance stalk_isScalarTower (s : GeometricPoint X.1) :
    IsScalarTower ℤ_[ℓ] O (LAdicSheaf.stalk B X ℓ F.toLAdicSheaf s) where
  smul_assoc c o v := by
    rw [smul_stalk_def, smul_stalk_def, Algebra.smul_def, map_mul, End.mul_asHom, act_algebraMap]
    change LAdicSheaf.stalkMap ((F.act o).asHom ≫ LAdicSheaf.scalarEnd F.toLAdicSheaf c) s v = _
    rw [LAdicSheaf.stalkMap_comp, LinearMap.comp_apply, LAdicSheaf.stalkMap_scalarEnd]

/-- **The action of an endomorphism of the geometric point (e.g. the geometric Frobenius) on the
stalk of an `O`-sheaf is `O`-linear.** -/
public def stalkEnd {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) :
    LAdicSheaf.stalk B X ℓ F.toLAdicSheaf s →ₗ[O] LAdicSheaf.stalk B X ℓ F.toLAdicSheaf s where
  toFun := LAdicSheaf.stalkEnd B X ℓ F.toLAdicSheaf a
  map_add' := map_add _
  map_smul' o v := by
    rw [smul_stalk_def, smul_stalk_def, RingHom.id_apply]
    exact LinearMap.congr_fun (LAdicSheaf.stalkEnd_comp_stalkMap (F.act o).asHom a) v

/-- Restricted to `ℤ_ℓ`, the `O`-linear action of an endomorphism of the geometric point on the
stalk is its `ℤ_ℓ`-linear action. -/
public theorem stalkEnd_restrictScalars {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) :
    (F.stalkEnd a).restrictScalars ℤ_[ℓ] = LAdicSheaf.stalkEnd B X ℓ F.toLAdicSheaf a :=
  rfl

section CompactSupport

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The `O`-module structure on `Hⁱ_c(X_k̄, F)`, through the action of `O` on the sheaf. -/
public instance compactlySupportedCohomologyModule (i : ℤ) :
    Module O (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :=
  Module.compHom _
    ((LAdicSheaf.geometricCompactlySupportedCohomologyEndRingHom f j kbar F.toLAdicSheaf i).comp
      F.act)

/-- `o ∈ O` acts on `Hⁱ_c(X_k̄, F)` as the map induced by its action on the sheaf. -/
public theorem smul_compactlySupportedCohomology_def (i : ℤ) (o : O)
    (v : LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :
    o • v = (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar (F.act o).asHom i).hom v :=
  rfl

/-- The `O`-module structure on `Hⁱ_c(X_k̄, F)` extends its `ℤ_ℓ`-module structure. -/
public instance compactlySupportedCohomology_isScalarTower (i : ℤ) :
    IsScalarTower ℤ_[ℓ] O
      (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) where
  smul_assoc c o v := by
    rw [smul_compactlySupportedCohomology_def, smul_compactlySupportedCohomology_def,
      Algebra.smul_def, map_mul, End.mul_asHom, act_algebraMap]
    change (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar
      ((F.act o).asHom ≫ LAdicSheaf.scalarEnd F.toLAdicSheaf c) i).hom v = _
    rw [LAdicSheaf.geometricCompactlySupportedCohomologyMap_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, LAdicSheaf.geometricCompactlySupportedCohomologyMap_scalarEnd]

/-- **`π_X^*` on `Hⁱ_c(X_k̄, F)` of an `O`-sheaf is `O`-linear.** -/
public def geometricCompactlySupportedFrobenius (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i →ₗ[O]
      LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i where
  toFun := (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
    F.toLAdicSheaf i).hom
  map_add' := map_add _
  map_smul' o v := by
    rw [smul_compactlySupportedCohomology_def, smul_compactlySupportedCohomology_def,
      RingHom.id_apply]
    exact ConcreteCategory.congr_hom
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap_frobenius f j kbar p q hcard
        (F.act o).asHom i) v

/-- Restricted to `ℤ_ℓ`, the `O`-linear `π_X^*` on `Hⁱ_c(X_k̄, F)` is the `ℤ_ℓ`-linear one. -/
public theorem geometricCompactlySupportedFrobenius_restrictScalars (p q : ℕ) [Fact p.Prime]
    [CharP k p] (hcard : Fintype.card k = p ^ q) (i : ℤ) :
    (F.geometricCompactlySupportedFrobenius f j kbar p q hcard i).restrictScalars ℤ_[ℓ] =
      (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        F.toLAdicSheaf i).hom :=
  rfl

end CompactSupport

end LAdicSheaf.CoefficientSheaf

/-! ### Matrices of endomorphisms and finite biproducts -/

section Matrix

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] (A : C)
  (ι : Type) [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The components of `biproduct.matrix` on a power of one object. -/
public theorem ι_matrix_π [Finite ι] (m : ι → ι → End A) (i k : ι) :
    biproduct.ι (fun _ : ι => A) i ≫ biproduct.matrix (f := fun _ : ι => A) (g := fun _ : ι => A)
      (fun i j => (m i j).asHom) ≫ biproduct.π (fun _ : ι => A) k = (m i k).asHom := by
  rw [biproduct.matrix_π, biproduct.ι_desc]

omit [Fintype ι] [DecidableEq ι] in
/-- Endomorphisms of a power of one object agreeing on all components are equal. -/
public theorem pow_hom_ext [Finite ι] {F G : (⨁ fun _ : ι => A) ⟶ ⨁ fun _ : ι => A}
    (h : ∀ i k, biproduct.ι (fun _ : ι => A) i ≫ F ≫ biproduct.π (fun _ : ι => A) k =
      biproduct.ι (fun _ : ι => A) i ≫ G ≫ biproduct.π (fun _ : ι => A) k) : F = G :=
  biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun k => by
    simpa only [Category.assoc] using h i k

/-- **`n × n` matrices of endomorphisms of `A` act on `Aⁿ = ⨁_ι A`**, as a ring homomorphism
`M_ι(End A) → End(⨁_ι A)`.  `End A` multiplies by composition in the reverse order, so the matrix
`M` acts through its transpose. -/
public def matrixEndRingHom : Matrix ι ι (End A) →+* End (⨁ fun _ : ι => A) where
  toFun M := End.of
    (biproduct.matrix (f := fun _ : ι => A) (g := fun _ : ι => A) fun i j => (M j i).asHom)
  map_one' := End.ext <| pow_hom_ext A ι fun i k => by
    dsimp only
    rw [ι_matrix_π A ι (fun i j => (1 : Matrix ι ι (End A)) j i)]
    change ((1 : Matrix ι ι (End A)) k i).asHom =
      biproduct.ι _ i ≫ 𝟙 (⨁ fun _ : ι => A) ≫ biproduct.π _ k
    rw [Category.id_comp, biproduct.ι_π, Matrix.one_apply]
    by_cases h : i = k
    · subst h
      rw [if_pos rfl, dif_pos rfl, eqToHom_refl]
      rfl
    · rw [if_neg (Ne.symm h), dif_neg h] <;> rfl
  map_mul' M N := End.ext <| pow_hom_ext A ι fun i k => by
    dsimp only
    rw [ι_matrix_π A ι (fun i j => (M * N) j i)]
    change _ = biproduct.ι _ i ≫ (biproduct.matrix (f := fun _ : ι => A) (g := fun _ : ι => A)
      (fun i j => (N j i).asHom) ≫ biproduct.matrix (f := fun _ : ι => A) (g := fun _ : ι => A)
        (fun i j => (M j i).asHom)) ≫ biproduct.π _ k
    rw [Category.assoc, biproduct.matrix_π, biproduct.matrix_desc, biproduct.ι_desc,
      Matrix.mul_apply, End.sum_asHom] <;> rfl
  map_zero' := End.ext <| pow_hom_ext A ι fun i k => by
    dsimp only
    rw [ι_matrix_π A ι (fun i j => (0 : Matrix ι ι (End A)) j i)]
    change ((0 : Matrix ι ι (End A)) k i).asHom = biproduct.ι (fun _ : ι => A) i ≫
      (0 : (⨁ fun _ : ι => A) ⟶ ⨁ fun _ : ι => A) ≫ biproduct.π (fun _ : ι => A) k
    simp only [Limits.zero_comp, Limits.comp_zero]
    rfl
  map_add' M N := End.ext <| pow_hom_ext A ι fun i k => by
    dsimp only
    rw [ι_matrix_π A ι (fun i j => (M + N) j i)]
    change _ = biproduct.ι _ i ≫ (biproduct.matrix (f := fun _ : ι => A) (g := fun _ : ι => A)
      (fun i j => (M j i).asHom) + biproduct.matrix (f := fun _ : ι => A) (g := fun _ : ι => A)
        (fun i j => (N j i).asHom)) ≫ biproduct.π _ k
    rw [Preadditive.add_comp, Preadditive.comp_add, ι_matrix_π A ι (fun i j => M j i),
      ι_matrix_π A ι (fun i j => N j i), Matrix.add_apply] <;> rfl

/-- The components of the action of a matrix. -/
public theorem ι_matrixEndRingHom_π (M : Matrix ι ι (End A)) (i k : ι) :
    biproduct.ι (fun _ : ι => A) i ≫ (matrixEndRingHom A ι M).asHom ≫
      biproduct.π (fun _ : ι => A) k = (M k i).asHom :=
  ι_matrix_π A ι (fun i j => M j i) i k

end Matrix

namespace LAdicSheaf

variable {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Extension of scalars `F ↦ F ⊗_{ℤ_ℓ} O`** along a finite free `ℤ_ℓ`-algebra `O` with basis
`b`: the ℓ-adic sheaf `F ⊗ O = ⨁_ι F`, on which `o ∈ O` acts by the matrix of multiplication by
`o` in the basis `b`, with entries acting through the canonical `ℤ_ℓ`-action. -/
public def extendScalars (F : LAdicSheaf B X ℓ) (b : Module.Basis ι ℤ_[ℓ] O) :
    LAdicSheaf.CoefficientSheaf B X ℓ O where
  toLAdicSheaf := ⨁ fun _ : ι => F
  act := (matrixEndRingHom F ι).comp
    ((LAdicSheaf.scalarRingHom F).mapMatrix.comp (Algebra.leftMulMatrix b).toRingHom)

/-- **Restriction of scalars of `F ⊗ O` is `F^{rank O}`.** -/
public theorem extendScalars_toLAdicSheaf (F : LAdicSheaf B X ℓ) (b : Module.Basis ι ℤ_[ℓ] O) :
    (extendScalars F b).toLAdicSheaf = ⨁ fun _ : ι => F :=
  rfl

/-- The action of `o ∈ O` on `F ⊗ O`, in components: the `(k, i)` component is multiplication by
the `(k, i)` entry of the matrix of `o`. -/
public theorem ι_extendScalars_act_π (F : LAdicSheaf B X ℓ) (b : Module.Basis ι ℤ_[ℓ] O) (o : O)
    (i k : ι) :
    biproduct.ι (fun _ : ι => F) i ≫ ((extendScalars F b).act o).asHom ≫ biproduct.π _ k =
      LAdicSheaf.scalarEnd F (Algebra.leftMulMatrix b o k i) :=
  ι_matrixEndRingHom_π F ι _ i k

end LAdicSheaf

end Stacks.EtaleCohomology
