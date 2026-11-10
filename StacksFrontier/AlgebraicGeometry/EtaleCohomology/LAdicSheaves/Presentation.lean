module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LAdicEventuallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Stabilisation

/-!
# A quotient presentation of the tower of levelwise kernels

For an epimorphism `f` of ℓ-adic sheaves the levelwise kernels form an inverse system whose
levels are not killed by the right power of `ℓ`, so that system is not the underlying tower of
an ℓ-adic sheaf. There is an ℓ-adic sheaf `H` whose underlying tower presents it, as a
`CategoryTheory.QuotientPresentation` of the kernel tower.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.underlyingRawKernelTower`: the inverse system of underlying
  levelwise kernels, with `underlyingRawKernelInclusion` into the underlying tower of the
  source.
* `Stacks.EtaleCohomology.LAdicSheaf.sheafOfPresentation`: the ℓ-adic sheaf whose underlying
  tower is the presented tower.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.epiKernel_eventually_constant_quotients` and
  `_reductions`: the quotients, respectively the reductions, of the levelwise kernels are
  eventually constant.
* `Stacks.EtaleCohomology.LAdicSheaf.epiKernel_has_presentation`: the kernel tower of an
  epimorphism admits a quotient presentation by an ℓ-adic sheaf.
* `Stacks.EtaleCohomology.LAdicSheaf.sheafOfPresentationIso`: its underlying tower is the
  presented tower.

## References

* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
* [Stacks Project, Tag 03UN](https://stacks.math.columbia.edu/tag/03UN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u u₁ u₂ v₁

namespace Stacks.EtaleCohomology

section ScalarChangeUnit

/-- An additive functor carries a morphism killed by `r` on its source to one killed by `r` on
its source. -/
public theorem map_nsmul_comp_eq_zero {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] {P Q : C}
    (r : ℕ) (g : P ⟶ Q) (h : (r • (𝟙 P)) ≫ g = 0) :
    (r • (𝟙 (F.obj P))) ≫ F.map g = 0 := by
  rw [← F.map_id, ← F.map_nsmul, ← F.map_comp, h, F.map_zero]

/-- The adjunction between extension and restriction of scalars along a map of cyclic
coefficient rings, on sheaves. -/
public abbrev zmodSheafAdjunction
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {m n : ℕ}
    [HasWeakSheafify J (ModuleCat.{max u₁ v₁ u₂} (ZMod n))] (f : ZMod m →+* ZMod n) :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{max u₁ v₁ u₂, 0, 0} f)

/-- The unit of that adjunction kills `n`. -/
public theorem zmodSheafUnit_condition
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {m n : ℕ}
    [HasWeakSheafify J (ModuleCat.{max u₁ v₁ u₂} (ZMod n))] (f : ZMod m →+* ZMod n)
    (M : Sheaf J (ModuleCat.{max u₁ v₁ u₂} (ZMod m))) :
    (n • (𝟙 M)) ≫ (zmodSheafAdjunction.{u₁, u₂, v₁} J f).unit.app M = 0 := by
  rw [Preadditive.nsmul_comp, Category.id_comp]
  ext U x
  rw [sheaf_nsmul_app]
  exact ZModModule.char_nsmul_eq_zero n
    (show (((Sheaf.composeAndSheafify J (ModuleCat.extendScalars f)).obj M).obj.obj U) from
      (((zmodSheafAdjunction.{u₁, u₂, v₁} J f).unit.app M).hom.app U x))

/-- The unit of that adjunction exhibits the restriction of the extension as the quotient
`M/nM`. -/
public def zmodSheafUnit_isCokernel
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {m n : ℕ}
    [HasWeakSheafify J (ModuleCat.{max u₁ v₁ u₂} (ZMod n))]
    [HasCokernels (Sheaf J (ModuleCat.{max u₁ v₁ u₂} (ZMod m)))]
    (f : ZMod m →+* ZMod n) (M : Sheaf J (ModuleCat.{max u₁ v₁ u₂} (ZMod m))) :
    IsColimit (CokernelCofork.ofπ ((zmodSheafAdjunction.{u₁, u₂, v₁} J f).unit.app M)
      (zmodSheafUnit_condition.{u₁, u₂, v₁} J f M)) := by
  let adj := zmodSheafAdjunction.{u₁, u₂, v₁} J f
  let L := Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{0, 0, max u₁ v₁ u₂} f)
  let R := sheafCompose J (ModuleCat.restrictScalars.{max u₁ v₁ u₂, 0, 0} f)
  haveI : (ModuleCat.restrictScalars.{max u₁ v₁ u₂} f).Full :=
    restrictScalars_full_of_surjective f (ZMod.ringHom_surjective f)
  haveI : R.Full := inferInstance
  let Q := cokernel (n • (𝟙 M))
  have hQ : ∀ U (x : Q.obj.obj U), n • x = 0 := by
    intro U x
    have h := congrArg (fun g : Q ⟶ Q => (g.hom.app U).hom x) (cokernel_nsmul_id M n)
    rwa [sheaf_nsmul_app] at h
  let Q₀ := annihilatedModuleSheaf.{u₁, u₂, v₁} J n m Q hQ
  let e : R.obj Q₀ ≅ Q := annihilatedModuleSheafIso.{u₁, u₂, v₁} J n m Q hQ f
  let q : M ⟶ R.obj Q₀ := cokernel.π (n • (𝟙 M)) ≫ e.inv
  let d : R.obj (L.obj M) ⟶ Q := R.map ((adj.homEquiv M Q₀).symm q) ≫ e.hom
  have hd : adj.unit.app M ≫ d = cokernel.π (n • (𝟙 M)) := by
    have hq : adj.unit.app M ≫ R.map ((adj.homEquiv M Q₀).symm q) = q :=
      (adj.homEquiv_unit M Q₀ _).symm.trans ((adj.homEquiv M Q₀).apply_symm_apply q)
    change adj.unit.app M ≫ (_ ≫ e.hom) = _
    rw [← Category.assoc, hq]
    simp [q]
  let β : Q ⟶ R.obj (L.obj M) := cokernel.desc (n • (𝟙 M))
    (adj.unit.app M) (zmodSheafUnit_condition.{u₁, u₂, v₁} J f M)
  have hβ : cokernel.π (n • (𝟙 M)) ≫ β = adj.unit.app M := cokernel.π_desc _ _ _
  have hdb : d ≫ β = 𝟙 _ := by
    apply adjunction_unit_hom_ext adj M (L.obj M)
    rw [← Category.assoc, hd, hβ]
    exact (Category.comp_id _).symm
  haveI : Epi β := epi_of_epi_fac hdb
  haveI : Epi (adj.unit.app M) := by rw [← hβ]; infer_instance
  apply CokernelCofork.IsColimit.ofπ' _ (zmodSheafUnit_condition.{u₁, u₂, v₁} J f M)
  intro H h wh
  refine ⟨d ≫ cokernel.desc (n • (𝟙 M)) h wh, ?_⟩
  rw [← Category.assoc, hd, cokernel.π_desc]

end ScalarChangeUnit

section CofinalIndex

/-- A cofinal index dominating a given sequence of bounds, monotone and above the identity. -/
public def cofinalIndex (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => N 0
  | n + 1 => cofinalIndex N n + N (n + 1) + 1

/-- The cofinal index dominates the bound at its own level. -/
public theorem cofinalIndex_bound (N : ℕ → ℕ) (n : ℕ) : N n ≤ cofinalIndex N n := by
  cases n with
  | zero => exact le_rfl
  | succ n => dsimp [cofinalIndex]; omega

/-- The cofinal index is above the identity. -/
public theorem cofinalIndex_le (N : ℕ → ℕ) (n : ℕ) : n ≤ cofinalIndex N n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => dsimp [cofinalIndex]; omega

/-- The cofinal index is monotone. -/
public theorem cofinalIndex_monotone (N : ℕ → ℕ) : Monotone (cofinalIndex N) := by
  refine monotone_nat_of_le_succ fun n => ?_
  dsimp [cofinalIndex]
  omega

end CofinalIndex

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

attribute [local instance] underlyingLevelFunctor_additive
  underlyingLevelFunctor_preservesMonomorphisms underlyingLevelFunctor_isLeftAdjoint
  underlyingLevelFunctor_preservesKernels underlyingLevelFunctor_full

/-- Extension of scalars from the coefficients of level `n` to those of level `k`, on
sheaves. -/
public abbrev levelScalarChange (n k : ℕ) (r : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1))) :=
  Sheaf.composeAndSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.extendScalars.{0, 0, u + 1} r)

/-- The unit of the scalar-change adjunction, read on underlying abelian sheaves. -/
public def levelScalarChangeUnit (n k : ℕ) (r : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1)))
    (P : FiniteLevelSheaf.{u, u + 1} B X ℓ n) :
    (underlyingLevelFunctor B X ℓ n).obj P ⟶
      (underlyingLevelFunctor B X ℓ k).obj ((levelScalarChange B X ℓ n k r).obj P) :=
  (underlyingLevelFunctor B X ℓ n).map
    ((zmodSheafAdjunction.{u + 1, u + 1, u} (SmallEtale.topology B X.1 X.property) r).unit.app P)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- That unit kills `ℓᵏ⁺¹`. -/
public theorem levelScalarChangeUnit_condition (n k : ℕ)
    (r : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1))) (P : FiniteLevelSheaf.{u, u + 1} B X ℓ n) :
    ((ℓ ^ (k + 1)) • (𝟙 ((underlyingLevelFunctor B X ℓ n).obj P))) ≫
      levelScalarChangeUnit B X ℓ n k r P = 0 :=
  map_nsmul_comp_eq_zero (underlyingLevelFunctor B X ℓ n) (ℓ ^ (k + 1)) _
    (zmodSheafUnit_condition.{u + 1, u + 1, u} (SmallEtale.topology B X.1 X.property) r P)

/-- That unit exhibits the scalar change as the quotient by `ℓᵏ⁺¹`. -/
public def levelScalarChangeUnit_isCokernel (n k : ℕ)
    (r : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1))) (P : FiniteLevelSheaf.{u, u + 1} B X ℓ n) :
    IsColimit (CokernelCofork.ofπ (levelScalarChangeUnit B X ℓ n k r P)
      (levelScalarChangeUnit_condition B X ℓ n k r P)) :=
  mapNsmulCokernel (underlyingLevelFunctor B X ℓ n) (ℓ ^ (k + 1)) _
    (zmodSheafUnit_condition.{u + 1, u + 1, u} (SmallEtale.topology B X.1 X.property) r P)
    (zmodSheafUnit_isCokernel.{u + 1, u + 1, u} (SmallEtale.topology B X.1 X.property) r P)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The unit of the scalar-change adjunction is natural. -/
public theorem levelScalarChangeUnit_naturality (n k : ℕ)
    (r : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1)))
    {P Q : FiniteLevelSheaf.{u, u + 1} B X ℓ n} (a : P ⟶ Q) :
    levelScalarChangeUnit B X ℓ n k r P ≫
        (underlyingLevelFunctor B X ℓ k).map ((levelScalarChange B X ℓ n k r).map a) =
      (underlyingLevelFunctor B X ℓ n).map a ≫ levelScalarChangeUnit B X ℓ n k r Q := by
  let adj := zmodSheafAdjunction.{u + 1, u + 1, u} (SmallEtale.topology B X.1 X.property) r
  change (underlyingLevelFunctor B X ℓ n).map (adj.unit.app P) ≫
      (underlyingLevelFunctor B X ℓ n).map (((levelScalarChange B X ℓ n k r) ⋙
        sheafCompose (SmallEtale.topology B X.1 X.property)
          (ModuleCat.restrictScalars.{u + 1, 0, 0} r)).map a) =
    (underlyingLevelFunctor B X ℓ n).map a ≫ (underlyingLevelFunctor B X ℓ n).map (adj.unit.app Q)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact (underlyingLevelFunctor B X ℓ n).congr_map (adj.unit.naturality a).symm

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- A morphism which is an isomorphism on the quotients by `ℓᵏ⁺¹` becomes an isomorphism after
scalar change to level `k`. -/
public theorem levelScalarChange_map_isIso (n k : ℕ)
    (r : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ (k + 1)))
    {P Q : FiniteLevelSheaf.{u, u + 1} B X ℓ n} (a : P ⟶ Q)
    [IsIso (scalarCokernelMap (ℓ ^ (k + 1)) ((underlyingLevelFunctor B X ℓ n).map a))] :
    IsIso ((levelScalarChange B X ℓ n k r).map a) := by
  have : IsIso ((underlyingLevelFunctor B X ℓ k).map ((levelScalarChange B X ℓ n k r).map a)) :=
    scalarQuotientMap_isIso (ℓ ^ (k + 1)) ((underlyingLevelFunctor B X ℓ n).map a)
      (levelScalarChangeUnit B X ℓ n k r P) (levelScalarChangeUnit B X ℓ n k r Q)
      (levelScalarChangeUnit_condition B X ℓ n k r P)
      (levelScalarChangeUnit_condition B X ℓ n k r Q)
      (levelScalarChangeUnit_isCokernel B X ℓ n k r P)
      (levelScalarChangeUnit_isCokernel B X ℓ n k r Q)
      _ (levelScalarChangeUnit_naturality B X ℓ n k r a)
  exact isIso_of_reflects_iso _ (underlyingLevelFunctor B X ℓ k)

variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

attribute [local instance] underlyingLAdicLevel_noetherian underlyingTransitionLE_epi
  underlyingRawKernelι_mono

/-- The quotients of the levelwise kernels are eventually constant: for each `k`, past some
level the transition map of the levelwise kernels is an isomorphism on the quotients by
`ℓᵏ⁺¹`. -/
public theorem epiKernel_eventually_constant_quotients {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (f : F ⟶ G) [Epi f] :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      IsIso (scalarCokernelMap (ℓ ^ (k + 1)) (underlyingRawKernelTransition B X ℓ f n)) := by
  obtain ⟨c, hc⟩ := underlyingLAdic_torsion_divisibility B X ℓ G
  intro k
  refine ⟨c + k, fun n hn => ?_⟩
  have ha : ℓ ^ (n + 1) = ℓ ^ (k + 1) * ℓ ^ (n - k) := by
    rw [← pow_add]
    congr 1
    omega
  have hrs : ℓ ^ (k + 1) * ℓ ^ (n - k + 1) = ℓ ^ (n + 2) := by
    rw [← pow_add]
    congr 1
    omega
  have := (epi_iff_app_epi f).1 inferInstance (n + 1)
  have := underlyingRawKernelTransition_epi B X ℓ f n
  apply scalarCokernelMap_isIso
  apply kernelTransition_scalar_quotient_zero
    ((underlyingLevelFunctor B X ℓ (n + 1)).map (f.app (n + 1)))
    (underlyingLAdicTransition B X ℓ F n)
    (ℓ ^ (n + 1)) (ℓ ^ (k + 1)) (ℓ ^ (n - k)) (ℓ ^ (n - k + 1)) ha
    (underlyingTransition_condition B X ℓ F n)
    (underlyingTransition_isCokernel B X ℓ F n)
    (underlyingRawKernelι B X ℓ f (n + 1))
    (underlyingRawKernelι_condition B X ℓ f (n + 1))
    (underlyingRawKernel_isKernel B X ℓ f (n + 1))
    (underlyingRawKernelTransition B X ℓ f n)
    (underlyingRawKernelι B X ℓ f n) (underlyingRawKernelTransition_fac B X ℓ f n)
  · rw [hrs]
    exact underlyingLAdicLevel_annihilated B X ℓ F (n + 1)
  · intro A g hg
    exact hc (n - k) (n + 1) (by omega) (by omega) A g hg

/-- The reductions of the levelwise kernels are eventually constant. -/
public theorem epiKernel_eventually_constant_reductions {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (f : F ⟶ G) [Epi f] :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (h : k ≤ n) →
      IsIso ((Sheaf.composeAndSheafify (SmallEtale.topology B X.1 X.property)
        (ModuleCat.extendScalars.{0, 0, u + 1}
          (ZMod.castHom (pow_dvd_pow ℓ (by omega : k + 1 ≤ n + 2)) _ :
            ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (k + 1))))).map (rawKernelTransition f n)) := by
  intro k
  obtain ⟨N, hN⟩ := epiKernel_eventually_constant_quotients B X ℓ f k
  refine ⟨N, fun n hn _ => ?_⟩
  have : IsIso (scalarCokernelMap (ℓ ^ (k + 1))
      ((underlyingLevelFunctor B X ℓ (n + 1)).map (rawKernelTransition f n))) := hN n hn
  exact levelScalarChange_map_isIso B X ℓ (n + 1) k _ (rawKernelTransition f n)

/-- There is an ℓ-adic sheaf whose levels are the stable values of the reductions of the
levelwise kernels. -/
public theorem epiKernel_stable_level_representatives {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (f : F ⟶ G) [Epi f] :
    ∃ H : LAdicSheaf.{u, u + 1} B X ℓ, ∃ N : ℕ → ℕ,
      Nonempty (∀ (k n : ℕ), N k ≤ n → (h : k ≤ n) →
        H.level k ≅ FiniteLevelSheaf.reduceTo B X ℓ n k h (kernel (f.app n))) := by
  obtain ⟨H, N, e, _⟩ := exists_lAdicSheaf_of_eventuallyConstant_reductions B X ℓ
    (fun n => kernel (f.app n)) (fun n => rawKernelTransition f n)
    (fun n => isConstructible_kernel_app f n)
    (epiKernel_eventually_constant_reductions B X ℓ f)
  exact ⟨H, N, ⟨e⟩⟩

/-- The inverse system of underlying levelwise kernels. -/
public def underlyingRawKernelTower {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) :=
  Functor.ofOpSequence (underlyingRawKernelTransition B X ℓ f)

/-- The inclusion of the tower of underlying levelwise kernels into the underlying tower of the
source. -/
public def underlyingRawKernelInclusion {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) :
    underlyingRawKernelTower B X ℓ f ⟶ underlyingLAdicTower B X ℓ F :=
  NatTrans.ofOpSequence (underlyingRawKernelι B X ℓ f) (fun n => by
    rw [show (underlyingRawKernelTower B X ℓ f).map (homOfLE (Nat.le_add_right n 1)).op =
        underlyingRawKernelTransition B X ℓ f n from
          Functor.ofOpSequence_map_homOfLE_succ _ _,
      show (underlyingLAdicTower B X ℓ F).map (homOfLE (Nat.le_add_right n 1)).op =
        underlyingLAdicTransition B X ℓ F n from Functor.ofOpSequence_map_homOfLE_succ _ _]
    exact underlyingRawKernelTransition_fac B X ℓ f n)

/-- The transition map of the tower of underlying levelwise kernels at `n + 1 → n`. -/
private theorem underlyingRawKernelTower_map_succ {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (f : F ⟶ G) (n : ℕ) :
    (underlyingRawKernelTower B X ℓ f).map (homOfLE (Nat.le_add_right n 1)).op =
      underlyingRawKernelTransition B X ℓ f n :=
  Functor.ofOpSequence_map_homOfLE_succ _ _

/-- For an epimorphism, every transition map of the tower of underlying levelwise kernels is an
epimorphism. -/
public theorem underlyingRawKernelTower_epi {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    [Epi f] {n m : ℕ} (h : n ≤ m) : Epi (towerMap (underlyingRawKernelTower B X ℓ f) h) := by
  apply inverseSystem_map_epi_of_succ
  intro k
  rw [underlyingRawKernelTower_map_succ]
  exact underlyingRawKernelTransition_epi B X ℓ f k

/-- The tower of levelwise kernels of an epimorphism admits a quotient presentation whose
presented objects are the levels of an ℓ-adic sheaf. -/
public theorem epiKernel_has_presentation {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    [Epi f] :
    ∃ H : LAdicSheaf.{u, u + 1} B X ℓ,
      Nonempty {P : QuotientPresentation (underlyingRawKernelTower B X ℓ f) ℓ //
        P.obj = fun n => underlyingLAdicLevel B X ℓ H n} := by
  classical
  obtain ⟨H, N, ⟨e⟩⟩ := epiKernel_stable_level_representatives B X ℓ f
  choose J hJ using epiKernel_eventually_constant_quotients B X ℓ f
  let M := cofinalIndex (fun n => N n + J n)
  have hN : ∀ n, N n ≤ M n := fun n =>
    (Nat.le_add_right (N n) (J n)).trans (cofinalIndex_bound (fun k => N k + J k) n)
  have hJ' : ∀ n, J n ≤ M n := fun n =>
    (Nat.le_add_left (J n) (N n)).trans (cofinalIndex_bound (fun k => N k + J k) n)
  have hM : ∀ n, n ≤ M n := cofinalIndex_le _
  let r (n : ℕ) : ZMod (ℓ ^ (M n + 1)) →+* ZMod (ℓ ^ (n + 1)) :=
    ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ (hM n))) _
  let q n := levelScalarChangeUnit B X ℓ (M n) n (r n) (kernel (f.app (M n)))
  let E n := (underlyingLevelFunctor B X ℓ n).mapIso (e n (M n) (hN n) (hM n))
  have hq n : ((ℓ ^ (n + 1)) • (𝟙 (underlyingRawKernelLevel B X ℓ f (M n)))) ≫
      (q n ≫ (E n).inv) = 0 := by
    rw [← Category.assoc, levelScalarChangeUnit_condition, zero_comp]
  refine ⟨H, ⟨⟨{
    obj := fun n => underlyingLAdicLevel B X ℓ H n
    index := M
    le_index := hM
    monotone_index := cofinalIndex_monotone _
    π := fun n => q n ≫ (E n).inv
    condition := hq
    isColimit := ?_
    stable := ?_ }, rfl⟩⟩⟩
  · intro n
    apply IsColimit.ofIsoColimit
      (levelScalarChangeUnit_isCokernel B X ℓ (M n) n (r n) (kernel (f.app (M n))))
    exact Cofork.ext (E n).symm (by rfl)
  · intro n m h
    apply inverseSystem_map_isIso_of_succ
      (underlyingRawKernelTower B X ℓ f ⋙ scalarCokernelFunctor _ (ℓ ^ (n + 1))) h
    intro k hk
    change IsIso (scalarCokernelMap (ℓ ^ (n + 1))
      ((underlyingRawKernelTower B X ℓ f).map (homOfLE (Nat.le_succ k)).op))
    rw [underlyingRawKernelTower_map_succ]
    exact hJ n k ((hJ' n).trans hk)

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime] [AlgebraicGeometry.IsNoetherian X.1] in
/-- A candidate transition map whose underlying map exhibits the lower level as the quotient by
`ℓⁿ⁺¹` satisfies the compatibility condition of Tag 03UM. -/
public theorem reduction_isIso_of_underlying_cokernel (n : ℕ)
    (A : FiniteLevelSheaf.{u, u + 1} B X ℓ (n + 1)) (D : FiniteLevelSheaf.{u, u + 1} B X ℓ n)
    (t : A ⟶ (restrictScalarsFunctor B X ℓ n).obj D)
    (ht : ((ℓ ^ (n + 1)) • (𝟙 ((underlyingLevelFunctor B X ℓ (n + 1)).obj A))) ≫
      (underlyingLevelFunctor B X ℓ (n + 1)).map t = 0)
    (htc : IsColimit (CokernelCofork.ofπ ((underlyingLevelFunctor B X ℓ (n + 1)).map t) ht)) :
    IsIso (FiniteLevelSheaf.scalarReductionMap B X ℓ n A D t) := by
  let a := FiniteLevelSheaf.scalarReductionMap B X ℓ n A D t
  let U := underlyingLevelFunctor B X ℓ (n + 1)
  let q := U.map ((scalarAdjunction B X ℓ n).unit.app A)
  have hq : ((ℓ ^ (n + 1)) • (𝟙 (U.obj A))) ≫ q = 0 := by
    simpa only [Functor.map_comp, Functor.map_nsmul, U.map_id, Functor.map_zero]
      using U.congr_map (scalarAdjunction_unit_condition B X ℓ n A)
  have hqc : IsColimit (CokernelCofork.ofπ q hq) :=
    mapNsmulCokernel U _ _ (scalarAdjunction_unit_condition B X ℓ n A)
      (scalarAdjunction_unit_isCokernel B X ℓ n A)
  have ha : q ≫ (underlyingLevelFunctor B X ℓ n).map a = 𝟙 (U.obj A) ≫ U.map t := by
    rw [Category.id_comp]
    change U.map ((scalarAdjunction B X ℓ n).unit.app A) ≫
      U.map ((restrictScalarsFunctor B X ℓ n).map a) = U.map t
    rw [← U.map_comp]
    apply U.congr_map
    exact ((scalarAdjunction B X ℓ n).homEquiv_unit A D a).symm.trans
      (FiniteLevelSheaf.scalarReductionMap_comp B X ℓ n A D t)
  have : IsIso (scalarCokernelMap (ℓ ^ (n + 1)) (𝟙 (U.obj A))) := by
    change IsIso ((scalarCokernelFunctor _ (ℓ ^ (n + 1))).map (𝟙 (U.obj A)))
    infer_instance
  have : IsIso ((underlyingLevelFunctor B X ℓ n).map a) :=
    scalarQuotientMap_isIso (ℓ ^ (n + 1)) (𝟙 (U.obj A)) q (U.map t) hq ht hqc htc _ ha
  exact isIso_of_reflects_iso a (underlyingLevelFunctor B X ℓ n)

/-- The ℓ-adic sheaf whose levels are those of `H` and whose transition maps are those of the
presented tower, pulled back through the full and faithful forgetful functor. -/
public abbrev sheafOfPresentation
    {S : ℕᵒᵖ ⥤ Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}}
    (H : LAdicSheaf.{u, u + 1} B X ℓ) (P : QuotientPresentation S ℓ)
    (hP : P.obj = fun n => underlyingLAdicLevel B X ℓ H n) : LAdicSheaf.{u, u + 1} B X ℓ := by
  let e n : P.obj n ≅ underlyingLAdicLevel B X ℓ H n := eqToIso (congrFun hP n)
  let t n : (underlyingLevelFunctor B X ℓ (n + 1)).obj (H.level (n + 1)) ⟶
      (underlyingLevelFunctor B X ℓ (n + 1)).obj
        ((restrictScalarsFunctor B X ℓ n).obj (H.level n)) :=
    (e (n + 1)).inv ≫ presentationTransition P n ≫
      ((e n).hom : P.obj n ⟶ (underlyingLevelFunctor B X ℓ (n + 1)).obj
        ((restrictScalarsFunctor B X ℓ n).obj (H.level n)))
  let T n : H.level (n + 1) ⟶ (restrictScalarsFunctor B X ℓ n).obj (H.level n) :=
    (underlyingLevelFunctor B X ℓ (n + 1)).preimage (t n)
  refine {
    level := H.level
    constructible := H.constructible
    transition := T
    reduction_isIso := ?_ }
  intro n
  have ht : ((ℓ ^ (n + 1)) • (𝟙 (underlyingLAdicLevel B X ℓ H (n + 1)))) ≫ t n = 0 :=
    nsmul_hom_eq_zero _ _ (underlyingLAdicLevel_annihilated B X ℓ H n)
  have ht' : ((ℓ ^ (n + 1)) • (𝟙 (underlyingLAdicLevel B X ℓ H (n + 1)))) ≫
      (underlyingLevelFunctor B X ℓ (n + 1)).map (T n) = 0 := by
    simpa only [T, Functor.map_preimage] using ht
  apply reduction_isIso_of_underlying_cokernel B X ℓ n _ _ (T n) ht'
  haveI : IsIso (scalarCokernelMap (ℓ ^ (n + 1)) (e (n + 1)).inv) := by
    change IsIso ((scalarCokernelFunctor _ (ℓ ^ (n + 1))).map (e (n + 1)).inv)
    infer_instance
  let h := scalarQuotient_comp_isCokernel _ (e (n + 1)).inv
    (presentationTransition P n) _ (presentationTransition_isCokernel P n)
  apply IsColimit.ofIsoColimit h
  refine Cofork.ext (e n) ?_
  change ((e (n + 1)).inv ≫ presentationTransition P n) ≫ (e n).hom = _
  rw [Category.assoc]
  exact ((underlyingLevelFunctor B X ℓ (n + 1)).map_preimage
    (X := H.level (n + 1)) (Y := (restrictScalarsFunctor B X ℓ n).obj (H.level n)) (t n)).symm

/-- The underlying tower of `Stacks.EtaleCohomology.LAdicSheaf.sheafOfPresentation` is the
presented tower. -/
public def sheafOfPresentationIso
    {S : ℕᵒᵖ ⥤ Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}}
    (H : LAdicSheaf.{u, u + 1} B X ℓ) (P : QuotientPresentation S ℓ)
    (hP : P.obj = fun n => underlyingLAdicLevel B X ℓ H n) :
    underlyingLAdicTower B X ℓ (sheafOfPresentation B X ℓ H P hP) ≅ presentationTower P := by
  let e n : P.obj n ≅ underlyingLAdicLevel B X ℓ H n := eqToIso (congrFun hP n)
  let a : underlyingLAdicTower B X ℓ (sheafOfPresentation B X ℓ H P hP) ⟶ presentationTower P :=
    NatTrans.ofOpSequence (fun n => (e n).inv) (fun n => by
      have key : underlyingLAdicTransition B X ℓ (sheafOfPresentation B X ℓ H P hP) n =
          (e (n + 1)).inv ≫ presentationTransition P n ≫ (e n).hom :=
        (underlyingLevelFunctor B X ℓ (n + 1)).map_preimage _
      have hcancel : ((e (n + 1)).inv ≫ presentationTransition P n ≫ (e n).hom) ≫ (e n).inv =
          (e (n + 1)).inv ≫ presentationTransition P n := by
        rw [Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      simp only [underlyingLAdicTower, Functor.ofOpSequence_map_homOfLE_succ]
      exact (congrArg (fun z => z ≫ (e n).inv) key).trans hcancel)
  exact NatIso.ofComponents (fun n => (e n.unop).symm) (fun f => a.naturality f)

/-- Passing to the underlying tower is additive. -/
public theorem underlyingLAdicFunctor_additive : (underlyingLAdicFunctor B X ℓ).Additive where
  map_add {F G} {f g} := by
    apply NatTrans.ext
    funext n
    exact (underlyingLevelFunctor B X ℓ n.unop).map_add

attribute [local instance] underlyingLAdicFunctor_additive
  underlyingLAdicFunctor_full underlyingLAdicFunctor_faithful

/-- The component at a level of the map of underlying towers induced by a morphism. -/
public theorem underlyingLAdicTowerMap_app {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) :
    (underlyingLAdicTowerMap B X ℓ f).app (Opposite.op n) =
      (underlyingLevelFunctor B X ℓ n).map (f.app n) := rfl

/-- The component at a level of the lift of a morphism killed by `f` into the tower of
underlying levelwise kernels. -/
public def underlyingRawKernelLiftApp {F G A : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (a : A ⟶ F) (ha : a ≫ f = 0) (n : ℕ) :
    underlyingLAdicLevel B X ℓ A n ⟶ underlyingRawKernelLevel B X ℓ f n :=
  (KernelFork.IsLimit.lift' (underlyingRawKernel_isKernel B X ℓ f n)
    ((underlyingLevelFunctor B X ℓ n).map (a.app n))
    (by rw [← Functor.map_comp, comp_eq_zero_app a f ha n, Functor.map_zero])).1

/-- The defining property of that component. -/
public theorem underlyingRawKernelLiftApp_ι {F G A : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (a : A ⟶ F) (ha : a ≫ f = 0) (n : ℕ) :
    underlyingRawKernelLiftApp B X ℓ f a ha n ≫ underlyingRawKernelι B X ℓ f n =
      (underlyingLevelFunctor B X ℓ n).map (a.app n) :=
  (KernelFork.IsLimit.lift' (underlyingRawKernel_isKernel B X ℓ f n)
    ((underlyingLevelFunctor B X ℓ n).map (a.app n))
    (by rw [← Functor.map_comp, comp_eq_zero_app a f ha n, Functor.map_zero])).2

/-- A morphism killed by `f` lifts to the tower of underlying levelwise kernels. -/
public def underlyingRawKernelLift {F G A : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (a : A ⟶ F) (ha : a ≫ f = 0) :
    underlyingLAdicTower B X ℓ A ⟶ underlyingRawKernelTower B X ℓ f :=
  NatTrans.ofOpSequence (underlyingRawKernelLiftApp B X ℓ f a ha) (fun n => by
    rw [show (underlyingLAdicTower B X ℓ A).map (homOfLE (Nat.le_add_right n 1)).op =
        underlyingLAdicTransition B X ℓ A n from Functor.ofOpSequence_map_homOfLE_succ _ _,
      show (underlyingRawKernelTower B X ℓ f).map (homOfLE (Nat.le_add_right n 1)).op =
        underlyingRawKernelTransition B X ℓ f n from Functor.ofOpSequence_map_homOfLE_succ _ _]
    refine (cancel_mono (underlyingRawKernelι B X ℓ f n)).1 ?_
    calc (underlyingLAdicTransition B X ℓ A n ≫ underlyingRawKernelLiftApp B X ℓ f a ha n) ≫
          underlyingRawKernelι B X ℓ f n
        = underlyingLAdicTransition B X ℓ A n ≫ (underlyingRawKernelLiftApp B X ℓ f a ha n ≫
            underlyingRawKernelι B X ℓ f n) := Category.assoc _ _ _
      _ = underlyingLAdicTransition B X ℓ A n ≫
            (underlyingLevelFunctor B X ℓ n).map (a.app n) := by
          rw [underlyingRawKernelLiftApp_ι]
      _ = (underlyingLevelFunctor B X ℓ (n + 1)).map (a.app (n + 1)) ≫
            underlyingLAdicTransition B X ℓ F n := by
          have hnat := (underlyingLAdicTowerMap B X ℓ a).naturality
            (homOfLE (Nat.le_add_right n 1)).op
          rw [underlyingLAdicTowerMap_app, underlyingLAdicTowerMap_app,
            show (underlyingLAdicTower B X ℓ A).map (homOfLE (Nat.le_add_right n 1)).op =
              underlyingLAdicTransition B X ℓ A n from
                Functor.ofOpSequence_map_homOfLE_succ _ _,
            show (underlyingLAdicTower B X ℓ F).map (homOfLE (Nat.le_add_right n 1)).op =
              underlyingLAdicTransition B X ℓ F n from
                Functor.ofOpSequence_map_homOfLE_succ _ _] at hnat
          exact hnat
      _ = (underlyingRawKernelLiftApp B X ℓ f a ha (n + 1) ≫
            underlyingRawKernelι B X ℓ f (n + 1)) ≫
            underlyingLAdicTransition B X ℓ F n := by rw [underlyingRawKernelLiftApp_ι]
      _ = underlyingRawKernelLiftApp B X ℓ f a ha (n + 1) ≫
            (underlyingRawKernelι B X ℓ f (n + 1) ≫
              underlyingLAdicTransition B X ℓ F n) := Category.assoc _ _ _
      _ = underlyingRawKernelLiftApp B X ℓ f a ha (n + 1) ≫
            (underlyingRawKernelTransition B X ℓ f n ≫
              underlyingRawKernelι B X ℓ f n) := by
          rw [underlyingRawKernelTransition_fac]
      _ = (underlyingRawKernelLiftApp B X ℓ f a ha (n + 1) ≫
            underlyingRawKernelTransition B X ℓ f n) ≫
            underlyingRawKernelι B X ℓ f n := (Category.assoc _ _ _).symm)

/-- The lift into the tower of underlying levelwise kernels recovers the morphism. -/
public theorem underlyingRawKernelLift_fac {F G A : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (a : A ⟶ F) (ha : a ≫ f = 0) :
    underlyingRawKernelLift B X ℓ f a ha ≫ underlyingRawKernelInclusion B X ℓ f =
      (underlyingLAdicFunctor B X ℓ).map a := by
  apply NatTrans.ext
  funext n
  exact underlyingRawKernelLiftApp_ι B X ℓ f a ha n.unop

/-- The inclusion of the tower of underlying levelwise kernels is killed by the morphism. -/
public theorem underlyingRawKernelInclusion_condition {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (f : F ⟶ G) :
    underlyingRawKernelInclusion B X ℓ f ≫ (underlyingLAdicFunctor B X ℓ).map f = 0 :=
  NatTrans.ext (funext fun n => underlyingRawKernelι_condition B X ℓ f n.unop)

end LAdicSheaf

end Stacks.EtaleCohomology

end
