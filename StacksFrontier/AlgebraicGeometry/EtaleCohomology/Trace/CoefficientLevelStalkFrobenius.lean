module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientLevelTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicPointTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTraceFormula
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local terms of the twisted trace formula for the `O`-sheaf of a representation

Let `σ : π₁(X, x̄) → GL_m(O)` be a representation with coefficients in a finite free
`ℤ_ℓ`-algebra `O`, and `G` the `n`-th level of its `O`-sheaf as a sheaf of
`Λ' = ℤ/ℓⁿ⁺¹ ⊗ O`-modules. Along a path from a geometric point `s̄` to `x̄`, the stalk of `G` at
`s̄` is `(Λ')^m`, an endomorphism `a` of `s̄` acting by the reduction of `σ(g)`, `g` the element
of `π₁(X, x̄)` that the path transports the action of `a` to. Hence the `Λ'`-trace of the
geometric Frobenius at a rational point `y` lying over the closed point `x` is the image of
`tr σ(F_x)`, and the local term of the twisted trace formula
(`Stacks.EtaleCohomology.coeffLevel_twistedTraceFormula`) at `y` is the reduction of
`Tr_{O/ℤ_ℓ}(c · tr σ(F_x))`.

## Main results

* `Stacks.EtaleCohomology.coeffLevelStalkIso_geometricPointStalkMap`
* `Stacks.EtaleCohomology.trace_geometricPointStalkMap_coeffLevelStacksSheaf`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived AlgebraicGeometry
  AlgebraicGeometry.SmallEtale Stacks.ConstantSheaf Stacks.Frobenius

open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable {ℓ : ℕ} [Fact ℓ.Prime] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {d : ℕ}
  (b : Module.Basis (Fin d) ℤ_[ℓ] O) {m : ℕ}

/-- **`coeffLevelVecEquiv` carries `Res_b M` modulo `ℓᵏ` to `M` with entries in `Λ'_k`.** -/
public theorem coeffLevelVecEquiv_coefficientMatrix_mulVec (k : ℕ)
    (M : Matrix (Fin m) (Fin m) O) (w : Fin (m * d) → ZMod (ℓ ^ k)) :
    coeffLevelVecEquiv ℓ b m k
        (((coefficientMatrixRingHom b m M).map (PadicInt.toZModPow k)) *ᵥ w) =
      (M.map (coeffLevelRing.of ℓ O k)) *ᵥ coeffLevelVecEquiv ℓ b m k w := by
  obtain ⟨w', rfl⟩ : ∃ w' : Fin (m * d) → ℤ_[ℓ], (fun p => PadicInt.toZModPow k (w' p)) = w :=
    ⟨fun p => (ZMod.ringHom_surjective (PadicInt.toZModPow k) (w p)).choose,
      funext fun p => (ZMod.ringHom_surjective (PadicInt.toZModPow k) (w p)).choose_spec⟩
  have hmv : ((coefficientMatrixRingHom b m M).map (PadicInt.toZModPow k)) *ᵥ
      (fun p => PadicInt.toZModPow k (w' p)) =
      fun p => PadicInt.toZModPow k ((coefficientMatrixRingHom b m M *ᵥ w') p) := by
    funext p
    exact (RingHom.map_mulVec (PadicInt.toZModPow k) _ w' p).symm
  rw [hmv, coeffLevelVecEquiv_reduce, coeffLevelVecEquiv_reduce, coefficientVecEquiv_mulVec]
  funext i
  exact (RingHom.map_mulVec (coeffLevelRing.of ℓ O k) M _ i)

/-- A bijective additive map commuting with the scalars, as a linear equivalence. -/
public def linearEquivOfBijectiveSMul {R V W : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W] (f : V → W) (hadd : ∀ v w, f (v + w) = f v + f w)
    (hsmul : ∀ (c : R) v, f (c • v) = c • f v) (hf : Function.Bijective f) : V ≃ₗ[R] W :=
  LinearEquiv.ofBijective { toFun := f, map_add' := hadd, map_smul' := hsmul } hf

/-- `linearEquivOfBijectiveSMul f hadd hsmul hf` sends `v` to `f v`. -/
public theorem linearEquivOfBijectiveSMul_apply {R V W : Type*} [Semiring R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid W] [Module R W] (f : V → W) (hadd : ∀ v w, f (v + w) = f v + f w)
    (hsmul : ∀ (c : R) v, f (c • v) = c • f v) (hf : Function.Bijective f) (v : V) :
    linearEquivOfBijectiveSMul f hadd hsmul hf v = f v :=
  rfl

section Stalks

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hρ : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ))

local notation "e₀" => canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x

/-- **An endomorphism `a` of the geometric point acts on the stalk of the `Λ'_k`-sheaf by the
reduction of `Res_b σ(g)`**, `g` the transport along `t` of the automorphism of the fibre
functor given by `a`. -/
public theorem coeffLevelStalkIso_geometricPointStalkMap {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (g : EtaleFundamentalGroup X.1 s) (hg : g.asIso.hom = finiteEtaleFiberMap a) (k : ℕ)
    (v : (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
      ModuleCat.{u + 1} (coeffLevelRing ℓ O k))) :
    ((coeffLevelStalkIso b B X x σ hρ t k).hom
        (((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} (coeffLevelRing ℓ O k))).app
          (coeffLevelStacksSheaf b B X x σ hρ k).obj).hom v)).down =
      levelRepresentation ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) k
        (etaleFundamentalGroupMulEquiv t g)
        ((coeffLevelStalkIso b B X x σ hρ t k).hom v).down := by
  have h1 := geometricPointStalkMap_preservesColimitIso B X.1 X.2
    (forget₂ (ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) AddCommGrpCat.{u + 1}) a
    (coeffLevelStacksSheaf b B X x σ hρ k).obj
  have h2 := geometricPointStalkMap_preservesColimitIso B X.1 X.2
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}) a
    (representationLevelSheaf B X x e₀
      ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k).obj
  set Φ₁ := etaleStalkForget₂Iso B X.1 X.2 s (coeffLevelRing ℓ O k)
    (coeffLevelStacksSheaf b B X x σ hρ k) with hΦ₁
  set ΦZ := etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k))
    (representationLevelSheaf B X x e₀
      ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k) with hΦZ
  set z := ΦZ.inv (Φ₁.hom v) with hz
  have e1 := ConcreteCategory.congr_hom h1 v
  have e2 := ConcreteCategory.congr_hom h2 z
  have e3 : ΦZ.hom z = Φ₁.hom v := Iso.inv_hom_id_apply ΦZ (Φ₁.hom v)
  have e4 : ΦZ.inv (Φ₁.hom (((geometricPointStalkMap B X.1 X.2 a
      (ModuleCat.{u + 1} (coeffLevelRing ℓ O k))).app
        (coeffLevelStacksSheaf b B X x σ hρ k).obj).hom v)) =
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).map
        ((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))).app
          (representationLevelSheaf B X x e₀
            ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ k).obj) z := by
    refine (congrArg ΦZ.inv (e1.trans ?_)).trans (Iso.hom_inv_id_apply ΦZ _)
    exact (congrArg _ e3.symm).trans e2.symm
  change ((representationLevelStalkIso B X x _ hρ t k).hom (ΦZ.inv (Φ₁.hom
    (((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} (coeffLevelRing ℓ O k))).app
      (coeffLevelStacksSheaf b B X x σ hρ k).obj).hom v)))).down = _
  rw [e4]
  exact representationLevelStalkIso_geometricPointStalkMap B X x _ hρ t a g hg k z

/-- **The stalk of the `Λ'_k`-sheaf is `(Λ'_k)^m`, linearly over `Λ'_k`**, along a path `t`. -/
public theorem exists_coeffLevelStalkLinearEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (k : ℕ) :
    ∃ L : (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
        ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) ≃ₗ[coeffLevelRing ℓ O k]
          (Fin m → coeffLevelRing ℓ O k),
      ∀ v, L v = coeffLevelVecEquiv ℓ b m k ((coeffLevelStalkIso b B X x σ hρ t k).hom v).down := by
  have hb := ConcreteCategory.bijective_of_isIso (coeffLevelStalkIso b B X x σ hρ t k).hom
  let Ψ : (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
      ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) →+ (Fin (m * d) → ZMod (ℓ ^ k)) :=
    { toFun := fun v => ((coeffLevelStalkIso b B X x σ hρ t k).hom v).down
      map_zero' := congrArg ULift.down ((coeffLevelStalkIso b B X x σ hρ t k).hom.hom.map_zero)
      map_add' := fun v w =>
        congrArg ULift.down ((coeffLevelStalkIso b B X x σ hρ t k).hom.hom.map_add v w) }
  refine ⟨linearEquivOfBijectiveSMul (fun v => coeffLevelVecEquiv ℓ b m k (Ψ v))
    (fun v w => by rw [map_add, map_add]) (fun c v => ?_) ⟨fun v w h => ?_, fun w => ?_⟩,
    fun v => rfl⟩
  · rw [show Ψ (c • v) = ((coeffLevelStalkIso b B X x σ hρ t k).hom (c • v)).down from rfl,
      coeffLevelStalkIso_smul b B X x σ hρ t k c v]
    exact coeffLevelVecEquiv_mulVec ℓ b m k c ((coeffLevelStalkIso b B X x σ hρ t k).hom v).down
  · exact hb.1 (ULift.ext ((coeffLevelVecEquiv ℓ b m k).injective h))
  · obtain ⟨v, hv⟩ := hb.2 (ULift.up ((coeffLevelVecEquiv ℓ b m k).symm w))
    refine ⟨v, ?_⟩
    change coeffLevelVecEquiv ℓ b m k ((coeffLevelStalkIso b B X x σ hρ t k).hom v).down = w
    rw [hv, LinearEquiv.apply_symm_apply]

/-- **The `Λ'_k`-trace of an endomorphism `a` of the geometric point on the stalk of the
`Λ'_k`-sheaf is the image of `tr σ(g)`.** -/
public theorem trace_geometricPointStalkMap_coeffLevelStacksSheaf {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (g : EtaleFundamentalGroup X.1 s) (hg : g.asIso.hom = finiteEtaleFiberMap a) (k : ℕ) :
    LinearMap.trace (coeffLevelRing ℓ O k)
        (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
          ModuleCat.{u + 1} (coeffLevelRing ℓ O k))
        ((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} (coeffLevelRing ℓ O k))).app
          (coeffLevelStacksSheaf b B X x σ hρ k).obj).hom =
      coeffLevelRing.of ℓ O k (σ (etaleFundamentalGroupMulEquiv t g)).val.trace := by
  obtain ⟨L, hL⟩ := exists_coeffLevelStalkLinearEquiv b B X x σ hρ t k
  let φ : (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
      ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) →ₗ[coeffLevelRing ℓ O k]
        (etaleStalk B X.1 X.2 s (coeffLevelStacksSheaf b B X x σ hρ k).obj :
          ModuleCat.{u + 1} (coeffLevelRing ℓ O k)) :=
    ((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} (coeffLevelRing ℓ O k))).app
      (coeffLevelStacksSheaf b B X x σ hρ k).obj).hom
  have hφ : ∀ v, (coeffLevelStalkIso b B X x σ hρ t k).hom (φ v) =
      (coeffLevelStalkIso b B X x σ hρ t k).hom
        (((geometricPointStalkMap B X.1 X.2 a (ModuleCat.{u + 1} (coeffLevelRing ℓ O k))).app
          (coeffLevelStacksSheaf b B X x σ hρ k).obj).hom v) := fun v => rfl
  have hconj : L.conj φ =
      Matrix.toLin'
        ((σ (etaleFundamentalGroupMulEquiv t g)).val.map (coeffLevelRing.of ℓ O k)) := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := L.surjective w
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, hL, hL,
      hφ, coeffLevelStalkIso_geometricPointStalkMap b B X x σ hρ t a g hg k v,
      levelRepresentation_apply]
    exact coeffLevelVecEquiv_coefficientMatrix_mulVec b k _ _
  change LinearMap.trace (coeffLevelRing ℓ O k) _ φ = _
  rw [← LinearMap.trace_conj' φ L, hconj, Matrix.trace_toLin'_eq]
  exact (AddMonoidHom.map_trace (coeffLevelRing.of ℓ O k).toAddMonoidHom _).symm

end Stalks

section Comparison

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type) [CommRing R]
  (G : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} R))
  (xc : X.1) [Finite (X.1.residueField xc)] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP kbar p]

/-- **The geometric Frobenius at a closed point and at a rational point over it**, for an
arbitrary sheaf of `R`-modules on the small étale site of Stacks 021B: its stalk at the geometric
point at `x` is isomorphic to the stalk of its transport to Mathlib's small étale site at the
geometric point over `y`, intertwining `frobeniusPointHom X x` with the geometric Frobenius of
`y`. -/
@[sga "4½ Rapport 1.5"]
public theorem exists_etaleStalk_iso_frobenius_comm (hcard : Fintype.card k = p ^ q)
    (y : Spec (.of k) ⟶ X.1)
    (θ : GeometricPoint.Hom (rationalGeometricPoint kbar y) (geometricPointAt X.1 xc))
    (hres : Nat.card (X.1.residueField xc) = Fintype.card k) :
    ∃ e : etaleStalk B X.1 X.2 (geometricPointAt X.1 xc) G.obj ≅
        (rationalPointStalkFunctor R kbar y).obj
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} R)).functor.obj G),
      (geometricPointStalkMap B X.1 X.2 (frobeniusPointHom X.1 xc) (ModuleCat.{u + 1} R)).app
          G.obj ≫ e.hom =
        e.hom ≫ (geometricFrobeniusStalkFunctor (ModuleCat.{u + 1} R) kbar p q hcard y).app
          ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} R)).functor.obj G) := by
  have := smallEtalePointHom_isIso X.1 θ
  let e₁ := ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B X R (geometricPointAt X.1 xc)).app G).symm
  let e₂ := (GrothendieckTopology.Point.sheafFiberIsoOfIso (A := ModuleCat.{u + 1} R)
      (asIso (smallEtalePointHom X.1 θ))).app
        ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} R)).functor.obj G)
  have h₁ := congrArg (fun α => α.app G)
    (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B X R (frobeniusPointHom X.1 xc))
  have h₂ := congrArg (fun α => α.app
      ((SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} R)).functor.obj G))
    (frobeniusStalkFunctor_comm_of_hom_to (ModuleCat.{u + 1} R) X.1 xc kbar p q hcard y θ hres)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁ h₂
  exact ⟨e₁ ≪≫ e₂, (CommSq.vert_comp ⟨h₁.symm⟩ ⟨h₂.symm⟩).w⟩

end Comparison

section LocalTerm

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hρ : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ))
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP kbar p] (hcard : Fintype.card k = p ^ q)

local notation "e₀" => canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x

attribute [local instance] sheafEquiv_functor_additive

omit [QuasiCompact f] [IsSeparated f] in
/-- **The local term at a rational point `y` of the twisted trace formula is the image of
`tr σ(F_x)`**, `x` the closed point of degree one hit by `y` and `F_x` its geometric Frobenius
element. -/
public theorem eval_localTerm_coeffLevelComplex [Module.Finite ℤ_[ℓ] O] (n : ℕ)
    (y : rationalPoints f)
    (hM : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (rationalPointStalkComplex.{u, 0} (coeffLevelRing ℓ O (n + 1)) kbar y.1
        (coeffLevelComplex b B X x σ hρ n)))) :
    Stacks.Trace.commutativeAdditiveCommutatorQuotientEval (coeffLevelRing ℓ O (n + 1))
        (perfectDerivedTrace (coeffLevelRing ℓ O (n + 1)) ⟨_, hM⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} (coeffLevelRing ℓ O (n + 1))
            kbar p q hcard y.1 (coeffLevelComplex b B X x σ hρ n)))) =
      coeffLevelRing.of ℓ O (n + 1)
        (σ (geometricFrobeniusFamily f x (rationalPointsEquivDegreeOne f y).1)).val.trace := by
  have := finite_residueField_rationalPoint B X f y
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  set xc := (rationalPointsEquivDegreeOne f y).1 with hxc
  have hres : Nat.card (X.1.residueField xc.1) = Fintype.card k :=
    natCard_residueField_of_residueDegree_eq_one f _ (rationalPointsEquivDegreeOne f y).2
  obtain ⟨e, he⟩ := exists_etaleStalk_iso_frobenius_comm B X (coeffLevelRing ℓ O (n + 1))
    (coeffLevelStacksSheaf b B X x σ hρ (n + 1)) xc.1 kbar p q hcard y.1
    (rationalGeometricPointHom kbar y.1) hres
  have := isIso_coeffLevelStacksSheafHom b B X x σ hρ n
  let ι : (SmallEtale.sheafEquiv B X.1 X.2
        (ModuleCat.{u + 1} (coeffLevelRing ℓ O (n + 1)))).functor.obj
      (coeffLevelStacksSheaf b B X x σ hρ (n + 1)) ≅ coeffLevelEtaleSheaf b B X x e₀ σ hρ n :=
    (SmallEtale.sheafEquiv B X.1 X.2
        (ModuleCat.{u + 1} (coeffLevelRing ℓ O (n + 1)))).functor.mapIso
      (asIso (coeffLevelStacksSheafHom b B X x σ hρ n)) ≪≫
    (SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (coeffLevelRing ℓ O (n + 1)))).counitIso.app
      (coeffLevelEtaleSheaf b B X x e₀ σ hρ n)
  let e' := e ≪≫ (rationalPointStalkFunctor (coeffLevelRing ℓ O (n + 1)) kbar y.1).mapIso ι
  have he' : (geometricPointStalkMap B X.1 X.2 (frobeniusPointHom X.1 xc.1)
      (ModuleCat.{u + 1} (coeffLevelRing ℓ O (n + 1)))).app
        (coeffLevelStacksSheaf b B X x σ hρ (n + 1)).obj ≫ e'.hom =
      e'.hom ≫ (geometricFrobeniusStalkFunctor (ModuleCat.{u + 1} (coeffLevelRing ℓ O (n + 1)))
        kbar p q hcard y.1).app (coeffLevelEtaleSheaf b B X x e₀ σ hρ n) := by
    exact (CommSq.vert_comp ⟨he⟩ ⟨((geometricFrobeniusStalkFunctor
      (ModuleCat.{u + 1} (coeffLevelRing ℓ O (n + 1))) kbar p q hcard y.1).naturality
        ι.hom).symm⟩).w
  let t := (nonempty_finiteEtaleFiberFunctorIso X.1 (geometricPointAt X.1 xc.1) x).some
  obtain ⟨L, -⟩ := exists_coeffLevelStalkLinearEquiv b B X x σ hρ t (n + 1)
  let eL := (e'.toLinearEquiv.symm.trans L).symm
  have : Module.Free (coeffLevelRing ℓ O (n + 1))
      ((rationalPointStalkFunctor (coeffLevelRing ℓ O (n + 1)) kbar y.1).obj
        (coeffLevelEtaleSheaf b B X x e₀ σ hρ n)) :=
    Module.Free.of_equiv eL
  have : Module.Finite (coeffLevelRing ℓ O (n + 1))
      ((rationalPointStalkFunctor (coeffLevelRing ℓ O (n + 1)) kbar y.1).obj
        (coeffLevelEtaleSheaf b B X x e₀ σ hρ n)) :=
    Module.Finite.equiv eL
  rw [eval_perfectDerivedTrace_rationalPointStalkFrobenius_single kbar p q _ hcard y.1 _ hM,
    ← trace_hom_eq_of_comm e' _ _ he']
  have hg := inv_localElement_hom x xc t
  refine (trace_geometricPointStalkMap_coeffLevelStacksSheaf b B X x σ hρ t
    (frobeniusPointHom X.1 xc.1) _ hg (n + 1)).trans ?_
  have hel : etaleFundamentalGroupMulEquiv t (frobeniusDataOfPath x xc t).localElement⁻¹ =
      (frobeniusDataOfPath x xc t).element⁻¹ := MulEquiv.map_inv (etaleFundamentalGroupMulEquiv t) _
  exact congrArg (fun g => coeffLevelRing.of ℓ O (n + 1) (σ g).val.trace) hel

variable (J : CompactificationOf (Over.mk f)) [Algebra.IsAlgebraic k kbar] [CharP k p]

/-- **The trace formula at the `n`-th level of `ℱ_ρ`, twisted by `c ∈ O`, with explicit local
terms**: for `X` of dimension at most one over `k` and `ℓ ≠ p`, `RΓ_c(X_k̄, ℱ_{ρ,n})` is perfect
and `Tr(π_X^* ≫ c_* | RΓ_c(X_k̄, ℱ_{ρ,n}))` is the reduction modulo `ℓⁿ⁺¹` of
`∑_{x ∈ X(k)} Tr_{O/ℤ_ℓ}(c · tr σ(F_x))`. -/
public theorem coeffLevel_twistedTraceFormula_explicit [Module.Free ℤ_[ℓ] O]
    [Module.Finite ℤ_[ℓ] O] (hℓp : ℓ ≠ p) (hdim : topologicalKrullDim X.1 ≤ 1)
    [Fintype (rationalPoints f)] (n : ℕ) (c : O) :
    ∃ hP : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar
          (LAdicSheaf.levelComplex B X ℓ (representationLAdicSheaf B X x e₀
            ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) n))),
      Stacks.Trace.commutativeAdditiveCommutatorQuotientEval (ZMod (ℓ ^ (n + 1)))
          (perfectDerivedTrace (ZMod (ℓ ^ (n + 1))) ⟨_, hP⟩ (DerivedCategory.Plus.ι.map
            (canonicalCompactSupportFrobenius.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar p q hcard
                (LAdicSheaf.levelComplex B X ℓ (representationLAdicSheaf B X x e₀
                  ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) n) ≫
              (compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ (n + 1))) f J kbar).map
                (LAdicSheaf.levelComplexMap (representationLAdicSheafMap B X x e₀ hρ hρ
                  (coefficientScalarRingHom b m c)
                  (fun g => coefficientScalarRingHom_commute b m c (σ g).val)) n)))) =
        ∑ y : rationalPoints f, PadicInt.toZModPow (n + 1) (Algebra.trace ℤ_[ℓ] O
          (c * (σ (geometricFrobeniusFamily f x
            (rationalPointsEquivDegreeOne f y).1)).val.trace)) := by
  obtain ⟨hP, hKs, h⟩ := coeffLevel_twistedTraceFormula b B X x σ hρ f J kbar p q hcard hℓp hdim n c
  refine ⟨hP, h.trans (Finset.sum_congr rfl fun y _ => ?_)⟩
  refine (congrArg (fun t => Algebra.trace (ZMod (ℓ ^ (n + 1))) (coeffLevelRing ℓ O (n + 1))
    (coeffLevelRing.of ℓ O (n + 1) c * t))
    (eval_localTerm_coeffLevelComplex b B X x σ hρ f kbar p q hcard n y
      (hKs (rationalGeometricPoint kbar y.1)))).trans ?_
  rw [← map_mul, algebraTrace_coeffLevelRing_of ℓ b]

end LocalTerm

end Stacks.EtaleCohomology

end
