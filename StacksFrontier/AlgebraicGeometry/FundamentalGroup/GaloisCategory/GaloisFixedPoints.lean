module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.FieldFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.OpenSubgroups
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.InducedHomInnerConjugate

/-!
# Galois elements acting trivially on a geometric fibre

Let `L` be a separable closure of a field `K` inside an algebraically closed `Ω`. An element `σ`
of `Gal(L/K)` acts trivially on the geometric fibre of a finite étale `K`-scheme `Y` if and only if
it fixes every `L`-point of `Y`: `Spec σ ≫ f = f` for every `f : Spec L ⟶ Y` over `K`
(`AlgebraicGeometry.galoisEquivEtaleFundamentalGroup_apply_eq_self_iff`). Through a morphism
`J : Spec K ⟶ X` and a homomorphism `Φ : π₁(Spec K) → π₁(X, x̄)` induced by base change along `J`,
an element fixing every `L`-point of a finite étale `X`-scheme `Y` over `J` acts trivially on
`F_x̄(Y)` (`AlgebraicGeometry.forall_apply_eq_of_forall_spec_comp_eq`), and conversely
(`AlgebraicGeometry.forall_spec_comp_eq_of_forall_apply_eq`). The elements acting trivially on a
geometric fibre form an open subset of `Gal(L/K)`
(`AlgebraicGeometry.isOpen_setOf_forall_galoisEquivEtaleFundamentalGroup_apply_eq`).

These describe, in terms of fields, the open subgroups controlling a continuous representation of
`π₁`, used to make the inertia argument of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
uniform in the constant field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An element of `Gal(L/K)` commutes with the structure morphism `Spec L ⟶ Spec K`. -/
theorem spec_map_algEquiv_comp_spec_map_algebraMap {K L : Type u} [Field K] [Field L]
    [Algebra K L] (σ : Gal(L/K)) :
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← Spec.map_comp]
  congr 1
  ext z
  exact σ.commutes z

section Field

variable (K L Ω : Type u) [Field K] [Field L] [Field Ω] [Algebra K L] [IsSepClosure K L]
  [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]

/-- **An element of `Gal(L/K)` acts trivially on a geometric fibre iff it fixes every `L`-point.**
The fibre at `Spec Ω` is identified with the `L`-points (`finiteEtaleFiberIso`,
`separableFiberEquiv`), on which `σ` acts by `f ↦ Spec σ ≫ f`
(`galoisEquivEtaleFundamentalGroup_apply`). -/
theorem galoisEquivEtaleFundamentalGroup_apply_eq_self_iff (Y : FiniteEtaleOver (Spec (.of K)))
    (σ : Gal(L/K)) :
    (∀ p : (finiteEtaleFiberFunctor (algebraicClosureGeometricPoint K Ω)).obj Y,
      (((galoisEquivEtaleFundamentalGroup K L Ω) σ).asIso.app Y).hom p = p) ↔
    ∀ f : Spec (.of L) ⟶ Y.left, f ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) →
      Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ f = f := by
  let e := separableFiberEquiv K L Ω Y
  refine ⟨fun h f hf => ?_, fun h p => ?_⟩
  · have hσf : (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ f) ≫ Y.hom =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      rw [Category.assoc, hf, spec_map_algEquiv_comp_spec_map_algebraMap]
    have hp : ∀ g (hg : g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L))),
        ((finiteEtaleFiberIso K L Ω).hom.app Y (e.symm ⟨g, hg⟩)).1 =
          Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ g := fun g hg => by
      rw [finiteEtaleFiberIso_apply]
      show _ ≫ (e (e.symm ⟨g, hg⟩)).1 = _
      rw [Equiv.apply_symm_apply]
    have h1 := galoisEquivEtaleFundamentalGroup_apply K L Ω Y σ _ f (hp f hf)
    rw [h] at h1
    have h3 : e.symm ⟨_, hσf⟩ = e.symm ⟨f, hf⟩ :=
      ((isIso_iff_bijective ((finiteEtaleFiberIso K L Ω).hom.app Y)).1 inferInstance).1
        (Subtype.ext ((hp _ hσf).trans h1.symm))
    simpa only [Equiv.apply_symm_apply] using congrArg (fun y => (e y).1) h3
  · let y := (finiteEtaleFiberIso K L Ω).inv.app Y p
    have hy : (finiteEtaleFiberIso K L Ω).hom.app Y y = p :=
      congrArg (fun φ => φ p) (congrArg (fun η => η.app Y) (finiteEtaleFiberIso K L Ω).inv_hom_id)
    have hp : p.1 = Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ (e y).1 := by
      rw [← hy]
      exact finiteEtaleFiberIso_apply K L Ω Y y
    apply Subtype.ext
    rw [galoisEquivEtaleFundamentalGroup_apply K L Ω Y σ p (e y).1 hp, h _ (e y).2, hp]

/-- **The elements of `Gal(L/K)` acting trivially on a geometric fibre form an open set**: a
finite intersection of preimages of stabilizers, which are open (Tag 03VE). -/
theorem isOpen_setOf_forall_galoisEquivEtaleFundamentalGroup_apply_eq
    (W : FiniteEtaleOver (Spec (.of K))) :
    IsOpen {σ : Gal(L/K) |
      ∀ p : (finiteEtaleFiberFunctor (algebraicClosureGeometricPoint K Ω)).obj W,
        (((galoisEquivEtaleFundamentalGroup K L Ω) σ).asIso.app W).hom p = p} := by
  have := forall_finite_finiteEtaleFiberFunctor_obj (algebraicClosureGeometricPoint K Ω) W
  have heq : {σ : Gal(L/K) | ∀ p : (finiteEtaleFiberFunctor
      (algebraicClosureGeometricPoint K Ω)).obj W,
        (((galoisEquivEtaleFundamentalGroup K L Ω) σ).asIso.app W).hom p = p} =
      ⋂ p : (finiteEtaleFiberFunctor (algebraicClosureGeometricPoint K Ω)).obj W,
        (galoisEquivEtaleFundamentalGroup K L Ω) ⁻¹'
          (MulAction.stabilizer (EtaleFundamentalGroup (Spec (.of K))
            (algebraicClosureGeometricPoint K Ω)) p : Set _) := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
      MulAction.mem_stabilizer_iff]
    rfl
  rw [heq]
  exact isOpen_iInter_of_finite fun p =>
    (EtaleFundamentalGroup.isOpen_coe_of_isOpenSubgroup ⟨W, p, rfl⟩).preimage
      (galoisEquivEtaleFundamentalGroup K L Ω).continuous

end Field

section Induced

variable {X : Scheme.{u}} [ConnectedSpace X] (K L Ω : Type u) [Field K] [Field L] [Field Ω]
  [Algebra K L] [IsSepClosure K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]

/-- **An element fixing every `L`-point of `Y` over `J` acts trivially on `F_x̄(Y)`**, through any
homomorphism `Φ : π₁(Spec K) → π₁(X, x̄)` induced by base change along `J : Spec K ⟶ X`: an
`L`-point of `J*Y` over `K` is determined by its `L`-point of `Y` and its structure map. -/
theorem forall_apply_eq_of_forall_spec_comp_eq {x : GeometricPoint X} (J : Spec (.of K) ⟶ X)
    {Φ : EtaleFundamentalGroup (Spec (.of K)) (algebraicClosureGeometricPoint K Ω) →*
      EtaleFundamentalGroup X x}
    (hΦ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange J) Φ) (Y : FiniteEtaleOver X)
    (σ : Gal(L/K))
    (hσ : ∀ g : Spec (.of L) ⟶ Y.left,
      g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ J →
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g = g) :
    ∀ w : (finiteEtaleFiberFunctor x).obj Y,
      ((Φ (galoisEquivEtaleFundamentalGroup K L Ω σ)).asIso.app Y).hom w = w := by
  obtain ⟨T, hT⟩ := hΦ
  intro w
  rw [hT]
  have htriv := (galoisEquivEtaleFundamentalGroup_apply_eq_self_iff K L Ω
    ((finiteEtaleBaseChange J).obj Y) σ).2 (fun f hf => by
      let f' : Spec (.of L) ⟶ pullback Y.hom J := f
      have hf' : f' ≫ pullback.snd Y.hom J = Spec.map (CommRingCat.ofHom (algebraMap K L)) := hf
      show Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ f' = f'
      apply pullback.hom_ext
      · rw [Category.assoc]
        exact hσ _ (by rw [Category.assoc, pullback.condition, ← Category.assoc, hf'])
      · rw [Category.assoc, hf', spec_map_algEquiv_comp_spec_map_algebraMap]) (T.inv.app Y w)
  rw [htriv]
  exact congrArg (fun φ => φ w) (congrArg (fun η => η.app Y) T.inv_hom_id)

omit [ConnectedSpace X] in
/-- **Conversely, an element acting trivially on the geometric fibre of `J*Y` fixes every
`L`-point of `Y` over `J`.** -/
theorem forall_spec_comp_eq_of_forall_apply_eq (J : Spec (.of K) ⟶ X) (Y : FiniteEtaleOver X)
    (σ : Gal(L/K))
    (h : ∀ p : (finiteEtaleFiberFunctor (algebraicClosureGeometricPoint K Ω)).obj
      ((finiteEtaleBaseChange J).obj Y),
        (((galoisEquivEtaleFundamentalGroup K L Ω) σ).asIso.app _).hom p = p)
    (g : Spec (.of L) ⟶ Y.left)
    (hg : g ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ J) :
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ g = g := by
  have h1 := (galoisEquivEtaleFundamentalGroup_apply_eq_self_iff K L Ω _ σ).1 h
    (pullback.lift g (Spec.map (CommRingCat.ofHom (algebraMap K L))) hg) (pullback.lift_snd _ _ _)
  have h2 : (Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
      (pullback.lift g (Spec.map (CommRingCat.ofHom (algebraMap K L))) hg :
        Spec (.of L) ⟶ pullback Y.hom J)) ≫ pullback.fst Y.hom J =
      pullback.lift g (Spec.map (CommRingCat.ofHom (algebraMap K L))) hg ≫ pullback.fst Y.hom J :=
    congrArg (· ≫ pullback.fst Y.hom J) h1
  rwa [Category.assoc, pullback.lift_fst] at h2

end Induced

end AlgebraicGeometry

end
