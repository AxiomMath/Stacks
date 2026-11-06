module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryInertiaInvariantsModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree

/-!
# `H⁰_loc` of the levels of `ℱ_ρ` at a boundary point

Let `j : U ⟶ S` be quasi-compact and quasi-separated, `s` a geometric point of `S` such that
`U ×_S Spec 𝒪^{sh}_{S,s}` is the spectrum of a field `K`, `g : Spec K ⟶ U` the projection,
`t̄` an algebraic geometric point of `Spec K` and `p` a path from `g(t̄)` to a base point `x̄` of
the connected scheme `U`. For a continuous representation `ρ : π₁(U, x̄) → GL_r(ℤ_ℓ)` with
`k`-th level sheaf `ℱ_k` (the finite locally constant sheaf of `ℤ/ℓ^k`-modules attached to
`ρ mod ℓ^k`), this file identifies the stalk `(j_* ℱ_k)_s` with the inertia invariants of
`(ℤ/ℓ^k)^r`: the specialization map of `BoundaryInertiaInvariantsModules`, followed by the
identification of the stalk of `ℱ_k` at `g(t̄)` with `(ℤ/ℓ^k)^r` along `p`, is injective and
additive, with image the set of vectors fixed by `ρ mod ℓ^k` of the image in `π₁(U, x̄)` of every
automorphism of `t̄` over `K`. This is `H⁰_loc` of Weil II 1.8 for the levels of `ℱ_ρ`.

## Main definitions

* `Stacks.EtaleCohomology.representationLevelSheafMathlib` — the level sheaf on Mathlib's small
  étale site.
* `Stacks.EtaleCohomology.representationLevelPointStalkIso` — its stalk at `g(t̄)` read back on
  the bounded site is the stalk of the level sheaf.
* `Stacks.EtaleCohomology.representationLevelDirectImageStalkHom` — the map
  `(j_* ℱ_k)_s → (ℤ/ℓ^k)^r`.

## Main results

* `Stacks.EtaleCohomology.representationLevelDirectImageStalkHom_injective`.
* `forall_mulVec_eq_self_iff_forall_mem_range_representationLevelDirectImageStalkHom`
  — the `ℓ`-adic form: a vector of `ℤ_ℓ^r` is inertia invariant exactly when all its reductions
  come from the levels of `(j_* ℱ_ρ)_s`.
* `Stacks.EtaleCohomology.mem_range_representationLevelDirectImageStalkHom_iff` — the image is the
  module of inertia invariants.

## Implementation notes

The transport facts are proved as lemmas over arbitrary objects and isomorphisms and then
instantiated, so that the kernel never compares the carriers of the concrete functors involved.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.8, `H⁰_loc`)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] GeometricPoint.residueFieldAlgebra

section Generic

/-- An element lies in the image of a map followed by an isomorphism of abelian groups exactly
when its preimage under the isomorphism lies in the image of the map. -/
theorem mem_range_comp_iso_hom_iff {A P V : AddCommGrpCat.{v}} (f : A ⟶ P) (e : P ≅ V) (w : V) :
    w ∈ Set.range (ConcreteCategory.hom (f ≫ e.hom)) ↔
      ConcreteCategory.hom e.inv w ∈ Set.range (ConcreteCategory.hom f) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, by simp⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by simp [hz]⟩

/-- If an isomorphism of abelian groups intertwines `f` and `g`, the preimage of `w` is fixed
by `f` exactly when `w` is fixed by `g`. -/
theorem iso_inv_apply_fixed_iff {P V : AddCommGrpCat.{v}} (e : P ≅ V) (f : P → P) (g : V → V)
    (h : ∀ w, ConcreteCategory.hom e.hom (f w) = g (ConcreteCategory.hom e.hom w)) (w : V) :
    f (ConcreteCategory.hom e.inv w) = ConcreteCategory.hom e.inv w ↔ g w = w := by
  constructor
  · intro hf
    simpa [hf] using (h (ConcreteCategory.hom e.inv w)).symm
  · intro hg
    calc f (ConcreteCategory.hom e.inv w)
        = ConcreteCategory.hom e.inv (ConcreteCategory.hom e.hom
            (f (ConcreteCategory.hom e.inv w))) := (Iso.hom_inv_id_apply e _).symm
      _ = ConcreteCategory.hom e.inv w := by rw [h, Iso.inv_hom_id_apply, hg]

/-- The maps of Tag 04FN on underlying abelian groups of stalks of presheaves of modules are
natural in the presheaf. -/
theorem forget₂_etaleStalkPresheafFunctor_map_geometricPointStalkMap (B : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X) {s : GeometricPoint X} (a : GeometricPoint.Hom s s)
    (R : Type) [Ring R] {P P' : (SmallEtale B X hX)ᵒᵖ ⥤ ModuleCat.{u + 1} R} (φ : P ⟶ P')
    (w : (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj
      ((etaleStalkPresheafFunctor B X hX s (ModuleCat.{u + 1} R)).obj P)) :
    ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
        ((etaleStalkPresheafFunctor B X hX s (ModuleCat.{u + 1} R)).map φ))
        (ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((geometricPointStalkMap B X hX a (ModuleCat.{u + 1} R)).app P)) w) =
      ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((geometricPointStalkMap B X hX a (ModuleCat.{u + 1} R)).app P'))
        (ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((etaleStalkPresheafFunctor B X hX s (ModuleCat.{u + 1} R)).map φ)) w) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, (geometricPointStalkMap B X hX a (ModuleCat.{u + 1} R)).naturality φ]

/-- The element of `π₁` given by an automorphism `α` of the source of a geometric point acts on
the fibre functor as precomposition with any endomorphism of the geometric point with
underlying morphism `α`. -/
theorem GeometricPoint.sourceAutElement_hom_eq_finiteEtaleFiberMap {S : Scheme.{u}}
    [ConnectedSpace S] (z : GeometricPoint S) (α : z.source ≅ z.source)
    (hα : α.hom ≫ z.hom = z.hom) (a : GeometricPoint.Hom z z) (ha : a.hom = α.hom) :
    (z.sourceAutElement α hα).asIso.hom = finiteEtaleFiberMap a := by
  ext V q
  apply Subtype.ext
  show α.hom ≫ q.1 = a.hom ≫ q.1
  rw [ha]

/-- An automorphism of the source of a geometric point that fixes the geometric point also fixes
its image under any morphism. -/
private theorem GeometricPoint.comp_map_hom_of_comp_hom {X Y : Scheme.{u}} (t : GeometricPoint X)
    (f : X ⟶ Y) (α : t.source ≅ t.source) (hαt : α.hom ≫ t.hom = t.hom) :
    α.hom ≫ (t.map f).hom = (t.map f).hom := by
  show α.hom ≫ t.hom ≫ f = t.hom ≫ f
  rw [← Category.assoc, hαt]

end Generic

section Level

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (B' : BigEtaleSite.{u}) (U : B'.Scheme) [ConnectedSpace U.1] (x : GeometricPoint U.1)
  (j : U.1 ⟶ S)
  (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
  (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
  (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
  (t : GeometricPoint (Spec (.of K)))
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
  (p : finiteEtaleFiberFunctor (X := U.1) (t.map (B'.inclusion.map g)) ≅
    finiteEtaleFiberFunctor x) (k : ℕ)

/-- The `k`-th level of `ℱ_ρ`, read on Mathlib's small étale site of `U`. -/
abbrev representationLevelSheafMathlib :
    Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) :=
  (SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).functor.obj
    (representationLevelSheaf B' U x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B' U x) ρ hρ k)

/-- The stalk at `g(t̄)` of the level sheaf on Mathlib's site, read back on the bounded site, is
the stalk of the level sheaf there (through the unit of the equivalence of sites). -/
def representationLevelPointStalkIso :
    (pointStalkAb B' U K hK g t (ZMod (ℓ ^ k))).obj
        (representationLevelSheafMathlib B' U x ρ hρ k) ≅
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).obj
        (etaleStalk B' U.1 U.2 (t.map (B'.inclusion.map g)) (representationLevelSheaf B' U x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B' U x) ρ hρ k).obj) :=
  (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).mapIso
    ((etaleStalkPresheafFunctor B' U.1 U.2 (t.map (B'.inclusion.map g))
      (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).mapIso
      ((sheafToPresheaf _ _).mapIso
        ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).unitIso.app
          (representationLevelSheaf B' U x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B' U x) ρ hρ k)).symm))

/-- The stalk at `g(t̄)` of the level sheaf on Mathlib's site is `(ℤ/ℓ^kℤ)^r`, along the path
`p`. -/
def representationLevelPointStalkTrivialization :
    (pointStalkAb B' U K hK g t (ZMod (ℓ ^ k))).obj
        (representationLevelSheafMathlib B' U x ρ hρ k) ≅
      AddCommGrpCat.of (ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))) :=
  representationLevelPointStalkIso B' U x K hK g t ρ hρ k ≪≫
    representationLevelStalkIso B' U x ρ hρ p k

/-- **The trivialization of the stalk at `g(t̄)` intertwines the maps of Tag 04FN with `ρ`**: the
map along an endomorphism `a` of `g(t̄)` whose action on the fibre functor is `σ` becomes
`ρ mod ℓ^k` of the element of `π₁(U, x̄)` that `p` transports `σ` to. -/
theorem representationLevelPointStalkTrivialization_geometricPointStalkMap
    (a : GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g)))
    (σ : EtaleFundamentalGroup U.1 (t.map (B'.inclusion.map g)))
    (hσ : σ.asIso.hom = finiteEtaleFiberMap a)
    (w : (pointStalkAb B' U K hK g t (ZMod (ℓ ^ k))).obj
      (representationLevelSheafMathlib B' U x ρ hρ k)) :
    (ConcreteCategory.hom (representationLevelPointStalkTrivialization B' U x K hK g t ρ hρ p k).hom
        (ConcreteCategory.hom ((geometricPointStalkMap B' U.1 U.2 a
          (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).inverse.obj
            (representationLevelSheafMathlib B' U x ρ hρ k)).obj) w)).down =
      levelRepresentation ρ k (etaleFundamentalGroupMulEquiv p σ)
        (ConcreteCategory.hom
          (representationLevelPointStalkTrivialization B' U x K hK g t ρ hρ p k).hom w).down := by
  have h1 := forget₂_etaleStalkPresheafFunctor_map_geometricPointStalkMap B' U.1 U.2 a
    (ZMod (ℓ ^ k))
    ((sheafToPresheaf _ _).map
      ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).unitIso.app
        (representationLevelSheaf B' U x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B' U x) ρ hρ k)).inv) w
  have h2 := representationLevelStalkIso_geometricPointStalkMap B' U x ρ hρ p a σ hσ k
    (ConcreteCategory.hom (representationLevelPointStalkIso B' U x K hK g t ρ hρ k).hom w)
  exact (congrArg (fun y => (ConcreteCategory.hom
    (representationLevelStalkIso B' U x ρ hρ p k).hom y).down) h1).trans h2

variable [QuasiCompact j] [QuasiSeparated j]

/-- **`H⁰_loc` of the `k`-th level of `ℱ_ρ` at a boundary point**: the specialization map
`(j_* ℱ_k)_s → (ℱ_k)_{g(t̄)}` followed by the trivialization `(ℱ_k)_{g(t̄)} ≅ (ℤ/ℓ^kℤ)^r` along
the path `p`. -/
def representationLevelDirectImageStalkHom :
    (directImageStalkAb S s B' U j (ZMod (ℓ ^ k))).obj
        (representationLevelSheafMathlib B' U x ρ hρ k) ⟶
      AddCommGrpCat.of (ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))) :=
  directImageStalkToStalkHom B S hS s B' U j K e hK g hg t (ZMod (ℓ ^ k))
      (representationLevelSheafMathlib B' U x ρ hρ k) ≫
    (representationLevelPointStalkTrivialization B' U x K hK g t ρ hρ p k).hom

/-- The map `representationLevelDirectImageStalkHom` from `(j_* ℱ_k)_s` to `(ℤ/ℓ^k)^r` is
injective. -/
theorem representationLevelDirectImageStalkHom_injective :
    Function.Injective (ConcreteCategory.hom
      (representationLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p k)) := by
  intro y y' h
  refine directImageStalkToStalkHom_injective B S hS s B' U j K e hK g hg t (ZMod (ℓ ^ k)) _ ?_
  simpa only [representationLevelDirectImageStalkHom, ConcreteCategory.comp_apply,
    Iso.hom_inv_id_apply] using congrArg (ConcreteCategory.hom
      (representationLevelPointStalkTrivialization B' U x K hK g t ρ hρ p k).inv) h

/-- **`H⁰_loc` of the `k`-th level of `ℱ_ρ` at a boundary point is the module of inertia
invariants** (Weil II 1.8, module form). For an algebraic geometric point `t̄` of `Spec K`, a
vector `v ∈ (ℤ/ℓ^kℤ)^r` comes from `(j_* ℱ_k)_s` exactly when it is fixed by `ρ mod ℓ^k` of the
image in `π₁(U, x̄)`, along the path `p`, of every automorphism of `t̄` over `K`. -/
theorem mem_range_representationLevelDirectImageStalkHom_iff (ht : t.IsAlgebraic)
    (v : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))) :
    v ∈ Set.range (ConcreteCategory.hom
        (representationLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p k)) ↔
      ∀ (σ : GeometricPoint.absoluteGaloisGroup t)
        (τ : Gal(t.residueField / (Spec (.of K)).residueField (t.hom default)))
        (_ : ∀ a : GeometricPoint.separableClosure t,
          (σ a : t.residueField) = τ (a : t.residueField))
        (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
        (hαt : α.hom ≫ t.hom = t.hom),
        levelRepresentation ρ k
          (etaleFundamentalGroupMulEquiv p
            (GeometricPoint.sourceAutElement (S := U.1) (t.map (B'.inclusion.map g)) α (by
              change α.hom ≫ t.hom ≫ _ = t.hom ≫ _
              rw [← Category.assoc, hαt]))) v.down = v.down := by
  rw [representationLevelDirectImageStalkHom, mem_range_comp_iso_hom_iff,
    mem_range_directImageStalkToStalkHom_iff B S hS s B' U j K e hK g hg t (ZMod (ℓ ^ k)) ht]
  refine forall_congr' fun σ => forall_congr' fun τ => forall_congr' fun hτ =>
    forall_congr' fun α => forall_congr' fun hα => forall_congr' fun hαt => ?_
  refine (iso_inv_apply_fixed_iff
    (representationLevelPointStalkTrivialization B' U x K hK g t ρ hρ p k)
    (ConcreteCategory.hom ((geometricPointStalkMap B' U.1 U.2
      ((⟨α.hom, hαt⟩ : GeometricPoint.Hom t t).mapHom (B'.inclusion.map g))
        (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).app
      ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).inverse.obj
        (representationLevelSheafMathlib B' U x ρ hρ k)).obj))
    (fun w => ULift.up (levelRepresentation ρ k (etaleFundamentalGroupMulEquiv p
      (GeometricPoint.sourceAutElement (S := U.1) (t.map (B'.inclusion.map g)) α
        (GeometricPoint.comp_map_hom_of_comp_hom t _ α hαt))) w.down))
    (fun w => ULift.ext
      (representationLevelPointStalkTrivialization_geometricPointStalkMap B' U x K hK g t ρ hρ p k
        _ _ (GeometricPoint.sourceAutElement_hom_eq_finiteEtaleFiberMap (S := U.1)
          (t.map (B'.inclusion.map g)) α _
          ((⟨α.hom, hαt⟩ : GeometricPoint.Hom t t).mapHom (B'.inclusion.map g)) rfl) w)) v).trans
    ⟨congrArg ULift.down, ULift.ext⟩

end Level

section LAdic

open Matrix

variable {G : Type*} [Group G] {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}

/-- The reduction modulo `ℓ ^ k` of `ρ(g) v` is the level representation applied to the reduction
of `v`. -/
theorem levelRepresentation_map_toZModPow (ρ : G →* GL (Fin r) ℤ_[ℓ]) (k : ℕ) (g : G)
    (v : Fin r → ℤ_[ℓ]) :
    levelRepresentation ρ k g (fun i => PadicInt.toZModPow k (v i)) =
      fun i => PadicInt.toZModPow k
        ((((ρ g : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v) i) := by
  ext i
  simp only [levelRepresentation_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Matrix.map_apply]

/-- **An `ℓ`-adic vector is fixed by `ρ(g)` exactly when all its reductions are fixed by the level
representations.** -/
theorem mulVec_eq_self_iff_forall_levelRepresentation (ρ : G →* GL (Fin r) ℤ_[ℓ]) (g : G)
    (v : Fin r → ℤ_[ℓ]) :
    ((ρ g : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v ↔
      ∀ k, levelRepresentation ρ k g (fun i => PadicInt.toZModPow k (v i)) =
        fun i => PadicInt.toZModPow k (v i) := by
  simp only [levelRepresentation_map_toZModPow]
  exact ⟨fun h k => by rw [h],
    fun h => funext fun i => PadicInt.ext_of_toZModPow.1 fun k => congrFun (h k) i⟩

end LAdic

section LAdicBoundary

open AlgebraicGeometry.SmallEtale Matrix

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (B' : BigEtaleSite.{u}) (U : B'.Scheme) [ConnectedSpace U.1] (x : GeometricPoint U.1)
  (j : U.1 ⟶ S) [QuasiCompact j] [QuasiSeparated j]
  (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
  (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
  (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
  (t : GeometricPoint (Spec (.of K)))
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
  (p : finiteEtaleFiberFunctor (X := U.1) (t.map (B'.inclusion.map g)) ≅
    finiteEtaleFiberFunctor x)

/-- **`H⁰_loc` of `ℱ_ρ` at a boundary point is the module of inertia invariants of `ℤ_ℓ^r`**
(Weil II 1.8, `ℓ`-adic form). For an algebraic geometric point `t̄` of `Spec K`, a vector
`v ∈ ℤ_ℓ^r` is fixed by `ρ` of the image in `π₁(U, x̄)`, along the path `p`, of every automorphism
of `t̄` over `K` exactly when, for every `k`, its reduction modulo `ℓ ^ k` comes from
`(j_* ℱ_k)_s` under the injective map `representationLevelDirectImageStalkHom`. -/
theorem forall_mulVec_eq_self_iff_forall_mem_range_representationLevelDirectImageStalkHom
    (ht : t.IsAlgebraic) (v : Fin r → ℤ_[ℓ]) :
    (∀ (σ : GeometricPoint.absoluteGaloisGroup t)
        (τ : Gal(t.residueField / (Spec (.of K)).residueField (t.hom default)))
        (_ : ∀ a : GeometricPoint.separableClosure t,
          (σ a : t.residueField) = τ (a : t.residueField))
        (α : t.source ≅ t.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
        (hαt : α.hom ≫ t.hom = t.hom),
        ((ρ (etaleFundamentalGroupMulEquiv p
            (GeometricPoint.sourceAutElement (S := U.1) (t.map (B'.inclusion.map g)) α (by
              change α.hom ≫ t.hom ≫ _ = t.hom ≫ _
              rw [← Category.assoc, hαt]))) : GL (Fin r) ℤ_[ℓ]) :
          Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v) ↔
      ∀ k, ULift.up (fun i => PadicInt.toZModPow k (v i)) ∈ Set.range (ConcreteCategory.hom
        (representationLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p k)) := by
  simp only [mem_range_representationLevelDirectImageStalkHom_iff B S hS s B' U x j K e hK g hg t
    ρ hρ p _ ht, mulVec_eq_self_iff_forall_levelRepresentation]
  exact ⟨fun h k σ τ hτ α hα hαt => h σ τ hτ α hα hαt k,
    fun h σ τ hτ α hα hαt k => h k σ τ hτ α hα hαt⟩

end LAdicBoundary

end Stacks.EtaleCohomology

end
