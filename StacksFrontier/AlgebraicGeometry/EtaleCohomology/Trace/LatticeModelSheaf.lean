module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LatticeLevelModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GroupRingSheafPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LatticeConstituentsULift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFlatModelLevelZero

/-!
# The sheaves of the simple constituents of a lattice, and the closure they generate

Let `ρₘ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous. For each simple subquotient `W / W'` of the
reduction `L / ℓ L` of its lattice, and for one zero subquotient `⊥ / ⊥`
(`Stacks.EtaleCohomology.latticeModelModule`), let `Q_o` be the restriction of scalars to `ℤ_ℓ`
of the lisse sheaf of `ℤ/ℓ`-modules of `W / W'` (`Stacks.EtaleCohomology.latticeModelSheaf`). These
are finitely many, constructible and killed by `ℓ`.

For `f : Y ⟶ X`, a geometric point `ȳ`, a change of base point `t : F_x̄ ≅ F_{f(ȳ)}` and
`φ = φ_t ∘ f_*`, if `ℤ_ℓ^r / ℓ` with `π₁(Y, ȳ)` acting through a continuous `ρ_f` has its
constituents in the restrictions along `φ` of the simple subquotients of `L / ℓ L`, then the level
zero of the flat model of `ℱ_{ρ_f}` lies in the closure under extensions and summands of the
inverse images `f⁻¹ Q_o`
(`Stacks.EtaleCohomology.isExtensionSummandClosure_representationLAdicSheaf_levelZero`): the level
zero is `res ℱ_{ℤ_ℓ^r / ℓ}`
(`Stacks.EtaleCohomology.representationLAdicSheafFlatModelLevelZeroIso`,
`Stacks.EtaleCohomology.levelModuleLatticeIso`), the closure statement holds for the lisse sheaves
of group-ring modules (`Stacks.EtaleCohomology.isExtensionSummandClosure_groupRingSheaf`) and is
carried by the exact functor `res`, and `f⁻¹ Q_o` is `res ℱ_{(W/W')|φ}`
(`Stacks.EtaleCohomology.nonempty_inverseImage_restrictScalars_lisseEtaleSheaf_iso`).

## Main definitions

* `Stacks.EtaleCohomology.latticeModelModule`, `Stacks.EtaleCohomology.latticeModelSheaf`.

## Main results

* `Stacks.EtaleCohomology.isBigSiteConstructibleEtaleModule_latticeModelSheaf`,
  `Stacks.EtaleCohomology.nsmul_id_latticeModelSheaf_eq_zero`.
* `Stacks.EtaleCohomology.isExtensionSummandClosure_representationLAdicSheaf_levelZero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.LAdicTower MonoidAlgebra
  Stacks.GroupCohomology AlgebraicGeometry

universe u v w

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize groupRingSheaf_hasSheafify

section Algebra

variable {A : Type*} [Ring A] {ι ι' : Type*} {𝓜 : ι → Type v} {𝓜' : ι' → Type v}
  [∀ i, AddCommGroup (𝓜 i)] [∀ i, Module A (𝓜 i)] [∀ i, AddCommGroup (𝓜' i)]
  [∀ i, Module A (𝓜' i)] {M : Type v} [AddCommGroup M] [Module A M]

/-- **Constituents along a reindexing of the family by isomorphic members.** -/
theorem HasConstituentsIn.reindex (f : ι → ι') (e : ∀ i, 𝓜 i ≃ₗ[A] 𝓜' (f i))
    (h : HasConstituentsIn A 𝓜 M) : HasConstituentsIn A 𝓜' M := by
  intro W S _ _ q hq hS
  obtain ⟨i, a, b, hab⟩ := h W S q hq hS
  refine ⟨f i, (e i).toLinearMap ∘ₗ a, b ∘ₗ (e i).symm.toLinearMap, LinearMap.ext fun s => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun hab s

end Algebra

section Model

variable {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ} {G : Type v} [Group G]

/-- The simple subquotients of the reduction of the lattice of `ρ`, and one zero one. -/
abbrev LatticeModelIndex (ρ : G →* GL (Fin r) ℤ_[ℓ]) : Type :=
  Option (SimpleSubquotientIndex (MonoidAlgebra ℤ G) (latticeReduction ρ))

/-- The pair `W' ⊆ W` of the subquotient indexed by `o` (`⊥ ⊆ ⊥` for `none`). -/
def latticeModelPair (ρ : G →* GL (Fin r) ℤ_[ℓ]) :
    LatticeModelIndex ρ →
      Σ W : Submodule (MonoidAlgebra ℤ G) (latticeReduction ρ), Submodule (MonoidAlgebra ℤ G) W
  | none => ⟨⊥, ⊥⟩
  | some j => ⟨j.1, j.2.1⟩

/-- **The subquotient `W / W'` of `L / ℓ L` indexed by `o`.** -/
abbrev latticeModelModule (ρ : G →* GL (Fin r) ℤ_[ℓ]) (o : LatticeModelIndex ρ) : Type :=
  (latticeModelPair ρ o).1 ⧸ (latticeModelPair ρ o).2

/-- The subquotient `W / W'` is killed by `ℓ`. -/
theorem latticeModelModule_nsmul_eq_zero (ρ : G →* GL (Fin r) ℤ_[ℓ]) (o : LatticeModelIndex ρ)
    (x : ULift.{w} (latticeModelModule ρ o)) : ℓ ^ (0 + 1) • x = 0 := by
  refine ULift.ext _ _ ?_
  show ℓ ^ (0 + 1) • x.down = 0
  induction x.down using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, zero_add, pow_one]
    exact (Submodule.Quotient.mk_eq_zero _).2 (by
      rw [show ℓ • y = 0 from Subtype.ext (latticeReduction_nsmul_eq_zero ρ y.1)]
      exact zero_mem _)

/-- The `ℤ/ℓ`-module structure of `W / W'`. -/
abbrev latticeModelZModModule (ρ : G →* GL (Fin r) ℤ_[ℓ]) (o : LatticeModelIndex ρ) :
    Module (ZMod (ℓ ^ (0 + 1))) (ULift.{w} (latticeModelModule ρ o)) :=
  AddCommGroup.zmodModule (latticeModelModule_nsmul_eq_zero ρ o)

/-- The stabilizer of `m` in a module is that of `ULift.up m` in its universe lift. -/
private theorem setOf_smul_ulift_eq {M : Type*} [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M]
    (m : ULift.{w} M) :
    {g : G | of ℤ G g • m = m} = {g : G | of ℤ G g • m.down = m.down} := by
  ext g
  exact ⟨congrArg ULift.down, fun hg => ULift.ext _ _ hg⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- A module has open stabilizers if its universe lift does. -/
theorem groupRingIsContinuous_of_ulift {M : Type*} [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M]
    (h : GroupRingIsContinuous G (ULift.{w} M)) : GroupRingIsContinuous G M := fun m => by
  have := h (ULift.up m)
  rwa [setOf_smul_ulift_eq] at this

omit [IsTopologicalGroup G] in
/-- The universe lift of a module with open stabilizers has open stabilizers. -/
theorem groupRingIsContinuous_ulift {M : Type*} [AddCommGroup M] [Module (MonoidAlgebra ℤ G) M]
    (h : GroupRingIsContinuous G M) : GroupRingIsContinuous G (ULift.{w} M) := fun m => by
  rw [setOf_smul_ulift_eq]
  exact h _

/-- **`W / W'` has open stabilizers**, for `ρ` continuous. -/
theorem groupRingIsContinuous_latticeModelModule (ρ : G →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
    (o : LatticeModelIndex ρ) : GroupRingIsContinuous G (ULift.{w} (latticeModelModule ρ o)) := by
  have h₀ : GroupRingIsContinuous G (latticeReduction ρ) :=
    groupRingIsContinuous_of_ulift.{v, 0} (groupRingIsContinuous_latticeLevel.{v, 0} ρ hρ 1)
  exact groupRingIsContinuous_ulift (groupRingIsContinuous_quotient
    (groupRingIsContinuous_submodule h₀))

end Model

section Sheaf

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-- `ℓ ^ (0 + 1)` is nonzero. -/
instance instNeZeroPowLatticeModelSheaf : NeZero (ℓ ^ (0 + 1)) :=
  ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩

/-- **The sheaf `Q_o`**: the restriction of scalars to `ℤ_ℓ` of the lisse sheaf of `ℤ/ℓ`-modules
of the subquotient `W / W'` of the reduction of the lattice of `ρ`. -/
def latticeModelSheaf (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
    (o : LatticeModelIndex ρ) : EtaleModules.{u, 0} ℤ_[ℓ] X.1 :=
  letI := latticeModelZModModule.{u + 1, u + 1} ρ o
  (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (0 + 1)) X.1).obj
    ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (0 + 1)))).obj
      (groupRingContinuousModule (ℓ ^ (0 + 1)) (ULift.{u + 1} (latticeModelModule ρ o))
        (groupRingIsContinuous_latticeModelModule ρ hρ o)))

/-- **`Q_o` is constructible.** -/
theorem isBigSiteConstructibleEtaleModule_latticeModelSheaf
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
    (o : LatticeModelIndex ρ) :
    IsBigSiteConstructibleEtaleModule B X ℤ_[ℓ] (latticeModelSheaf B X x ρ hρ o) :=
  isBigSiteConstructibleEtaleModule_restrictScalars_lisseEtaleSheaf B X x (ℓ ^ (0 + 1))
    (PadicInt.toZModPow (0 + 1)) (ZMod.ringHom_surjective _) _

/-- **`Q_o` is killed by `ℓ`.** -/
theorem nsmul_id_latticeModelSheaf_eq_zero (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ])
    (hρ : Continuous ρ) (o : LatticeModelIndex ρ) : ℓ • 𝟙 (latticeModelSheaf B X x ρ hρ o) = 0 := by
  have h : ℓ ^ (0 + 1) • 𝟙 (latticeModelSheaf B X x ρ hρ o) = 0 :=
    nsmul_id_restrictScalars_lisseEtaleSheaf_eq_zero B X x _ _ _
  rwa [zero_add, pow_one] at h

end Sheaf

section Closure

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} [ConnectedSpace X.1] [ConnectedSpace Y.1]
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian Y.1]

/-- **The level zero of the flat model of `ℱ_{ρ_f}` lies in the closure of the `f⁻¹ Q_o`**, when
`ℤ_ℓ^r / ℓ` with `π₁(Y, ȳ)` acting through `ρ_f` has its constituents in the restrictions along
`φ = φ_t ∘ f_*` of the simple subquotients of the reduction of the lattice of `ρₘ`. -/
theorem isExtensionSummandClosure_representationLAdicSheaf_levelZero (f : Y ⟶ X)
    (y : GeometricPoint Y.1) {x : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor (y.map f.hom))
    (ρm : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρm : Continuous ρm)
    (ρf : EtaleFundamentalGroup Y.1 y →* GL (Fin r) ℤ_[ℓ]) (hρf : Continuous ρf)
    (hcon : HasConstituentsIn (MonoidAlgebra ℤ (EtaleFundamentalGroup Y.1 y))
      (fun j : SimpleSubquotientIndex (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x))
          (latticeReduction ρm) =>
        GroupRingRestrict ((etaleFundamentalGroupBasePointHom t).comp
          (etaleFundamentalGroupMap f.hom y)).toMonoidHom (simpleSubquotient _ _ j))
      (LatticeModule ρf ⧸ powSMulRange (MonoidAlgebra ℤ (EtaleFundamentalGroup Y.1 y)) ℓ
        (LatticeModule ρf) (0 + 1))) :
    IsExtensionSummandClosure (fun A => ∃ o, Nonempty (A ≅
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] f.hom).obj (latticeModelSheaf B X x ρm hρm o)))
      (towerObj (LAdicSheaf.padicTower B Y ℓ (LAdicSheaf.flatModel B ℓ
        (representationLAdicSheaf B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y) ρf hρf))) 0) := by
  let φ := (etaleFundamentalGroupBasePointHom t).comp (etaleFundamentalGroupMap f.hom y)
  let := latticeLevelZModModule.{u + 1, u + 1} ρf (0 + 1)
  have := finite_latticeLevel.{u + 1, u + 1} ρf (0 + 1)
  let : ∀ o, Module (ZMod (ℓ ^ (0 + 1))) (ULift.{u + 1} (latticeModelModule ρm o)) :=
    fun o => latticeModelZModModule ρm o
  let 𝓜 : LatticeModelIndex ρm → Type (u + 1) := fun o =>
    GroupRingRestrict φ.toMonoidHom (ULift.{u + 1} (latticeModelModule ρm o))
  have h𝓜 : ∀ o, GroupRingIsContinuous (EtaleFundamentalGroup Y.1 y) (𝓜 o) := fun o =>
    groupRingIsContinuous_groupRingRestrict φ (groupRingIsContinuous_latticeModelModule ρm hρm o)
  let Fm := (SmallEtale.sheafEquiv B Y.1 Y.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (0 + 1))))).functor ⋙
    etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (0 + 1)) Y.1
  let S : ObjectProperty
      (Sheaf (SmallEtale.topology B Y.1 Y.2) (ModuleCat.{u + 1} (ZMod (ℓ ^ (0 + 1))))) :=
    fun A => ∃ o, Nonempty (Fm.obj A ≅
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] f.hom).obj (latticeModelSheaf B X x ρm hρm o))
  have hS : ∀ o, S (groupRingSheaf B Y y (ℓ ^ (0 + 1)) (𝓜 o) (h𝓜 o)) := fun o =>
    ⟨o, ⟨(nonempty_inverseImage_restrictScalars_lisseEtaleSheaf_iso B f y t (ℓ ^ (0 + 1))
      (PadicInt.toZModPow (0 + 1)) _
      (groupRingIsContinuous_latticeModelModule ρm hρm o)).some.symm⟩⟩
  have hcon₁ : HasConstituentsIn (MonoidAlgebra ℤ (EtaleFundamentalGroup Y.1 y))
      (fun j : SimpleSubquotientIndex (MonoidAlgebra ℤ (EtaleFundamentalGroup X.1 x))
          (latticeReduction ρm) =>
        ULift.{u + 1} (GroupRingRestrict φ.toMonoidHom (simpleSubquotient _ _ j)))
      (ULift.{u + 1} (LatticeModule ρf ⧸ latticeLevelSubmodule ρf (0 + 1))) :=
    hcon.ulift
  have hcon' : HasConstituentsIn (MonoidAlgebra ℤ (EtaleFundamentalGroup Y.1 y)) 𝓜
      (ULift.{u + 1} (LatticeModule ρf ⧸ latticeLevelSubmodule ρf (0 + 1))) :=
    hcon₁.reindex some fun _ =>
      ULift.moduleEquiv.trans (groupRingRestrictEquiv φ.toMonoidHom ULift.moduleEquiv.symm)
  let S' : ObjectProperty (EtaleModules.{u, 0} ℤ_[ℓ] Y.1) := fun A => ∃ o, Nonempty (A ≅
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] f.hom).obj (latticeModelSheaf B X x ρm hρm o))
  have hcl := IsExtensionSummandClosure.map Fm (S := S) (S' := S') (fun A hA => by
      obtain ⟨o, ⟨e⟩⟩ := hA
      exact IsExtensionSummandClosure.of_mem ⟨o, ⟨e⟩⟩)
    (isExtensionSummandClosure_groupRingSheaf B Y y (ℓ ^ (0 + 1))
      (groupRingIsContinuous_latticeLevel ρf hρf (0 + 1)) 𝓜 h𝓜 S hS none hcon')
  exact IsExtensionSummandClosure.of_iso
    (representationLAdicSheafFlatModelLevelZeroIso B Y y ρf hρf ≪≫
      (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (0 + 1)) Y.1).mapIso
        ((lisseEtaleSheaf B Y y (ZMod (ℓ ^ (0 + 1)))).mapIso
          (levelModuleLatticeIso.{u + 1, u + 1} ρf hρf (0 + 1)))).symm hcl

end Closure

end Stacks.EtaleCohomology

end
