module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalkFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicCoefficientExtension

/-!
# The `O`-sheaf of an `O^×`-valued character

For a finite free `ℤ_ℓ`-algebra `O` with basis `b` and a continuous character
`χ : π₁(X, x̄) → O^×`, the sheaf `ℱ_ρ` of `ρ = (multiplication by χ)` on `O ≅ ℤ_ℓ^d` is an
`O`-sheaf (`O` acting through the intertwiners `leftMulMatrix b o`), its stalks are free of rank
one over `O`, and an endomorphism of a geometric point acts on the stalk as the scalar `χ(g)`.

## Main definitions

* `Stacks.EtaleCohomology.representationCoefficientSheaf`: the `O`-sheaf of a representation
  commuting with an action of `O` on `ℤ_ℓ^r`.
* `Stacks.EtaleCohomology.characterSheaf`: the `O`-sheaf `ℱ_χ` of a continuous character
  `χ : π₁(X, x̄) → O^×`.
* `Stacks.EtaleCohomology.characterSheafStalkLinearEquiv`: the stalk of `ℱ_χ` is isomorphic to
  `O` as an `O`-module.

## Main results

* `Stacks.EtaleCohomology.characterSheaf_stalkEnd_eq_smul`: an endomorphism of a geometric point
  acts on the stalk of `ℱ_χ` as multiplication by `χ(g)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The morphism of an intertwiner depends only on the matrix. -/
public theorem representationLAdicSheafMap_congr
    {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
    {A A' : Matrix (Fin r) (Fin r) ℤ_[ℓ]} (h : A = A')
    (hA : ∀ g, A * (ρ g).val = (ρ g).val * A) (hA' : ∀ g, A' * (ρ g).val = (ρ g).val * A') :
    representationLAdicSheafMap B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        hρ hρ A hA =
      representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ A' hA' := by
  subst h
  rfl

/-- **The `O`-sheaf `ℱ_ρ` of a representation commuting with an action `μ` of `O` on `ℤ_ℓ^r`**
(a representation with coefficients in `O`): `O` acts on `ℱ_ρ` through the morphisms of the
intertwiners `μ(o)`. -/
public def representationCoefficientSheaf {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O]
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
    (μ : O →+* Matrix (Fin r) (Fin r) ℤ_[ℓ]) (hμ : ∀ o g, μ o * (ρ g).val = (ρ g).val * μ o) :
    LAdicSheaf.CoefficientSheaf B X ℓ O where
  toLAdicSheaf := representationLAdicSheaf B X x
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ
  act := RingHom.mk'
    { toFun := fun o => End.of (representationLAdicSheafMap B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ (μ o) (hμ o))
      map_one' := End.ext <| (representationLAdicSheafMap_congr B X x hρ (map_one μ) _ _).trans
        (representationLAdicSheafMap_one B X x _ hρ)
      map_mul' := fun o o' => End.ext <|
        (representationLAdicSheafMap_congr B X x hρ (map_mul μ o o') _
          (fun g => by
            rw [Matrix.mul_assoc, hμ o', ← Matrix.mul_assoc, hμ o, Matrix.mul_assoc])).trans
        (representationLAdicSheafMap_mul B X x _ hρ hρ hρ (μ o') (hμ o') (μ o) (hμ o)) }
    fun o o' => End.ext <| (representationLAdicSheafMap_congr B X x hρ (map_add μ o o') _
        (fun g => by rw [Matrix.add_mul, Matrix.mul_add, hμ o, hμ o'])).trans
      (representationLAdicSheafMap_add B X x _ hρ hρ (μ o) (μ o') (hμ o) (hμ o'))

/-- The action of `o : O` on `representationCoefficientSheaf` is the morphism of the intertwiner
`μ o`. -/
public theorem representationCoefficientSheaf_act {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O]
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
    (μ : O →+* Matrix (Fin r) (Fin r) ℤ_[ℓ]) (hμ : ∀ o g, μ o * (ρ g).val = (ρ g).val * μ o)
    (o : O) :
    ((representationCoefficientSheaf B X x ρ hρ μ hμ).act o).asHom =
      representationLAdicSheafMap B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ (μ o) (hμ o) :=
  rfl

/-! ### The `O`-sheaf of an `O^×`-valued character -/

section Character

variable {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[ℓ] O)
  (χ : EtaleFundamentalGroup X.1 x →* Oˣ)

/-- The `ℤ_ℓ`-representation `π₁ → GL_d(ℤ_ℓ)` of an `O^×`-valued character: multiplication by
`χ(g)` on `O ≅ ℤ_ℓ^d`. -/
public def characterRepresentation : EtaleFundamentalGroup X.1 x →* GL (Fin d) ℤ_[ℓ] :=
  (Units.map (Algebra.leftMulMatrix b).toMonoidHom).comp χ

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- The matrix of `characterRepresentation b χ g` is the matrix of multiplication by `χ g` in the
basis `b`. -/
public theorem characterRepresentation_val (g : EtaleFundamentalGroup X.1 x) :
    (characterRepresentation B X x b χ g).val = Algebra.leftMulMatrix b (χ g : O) :=
  rfl

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [AlgebraicGeometry.IsNoetherian X.1] in
/-- The matrix of multiplication by `o : O` in the basis `b` commutes with
`characterRepresentation b χ g`. -/
public theorem leftMulMatrix_commute (o : O) (g : EtaleFundamentalGroup X.1 x) :
    (Algebra.leftMulMatrix b).toRingHom o * (characterRepresentation B X x b χ g).val =
      (characterRepresentation B X x b χ g).val * (Algebra.leftMulMatrix b).toRingHom o := by
  rw [characterRepresentation_val]
  change Algebra.leftMulMatrix b o * _ = _ * Algebra.leftMulMatrix b o
  rw [← map_mul, ← map_mul, mul_comm]

/-- **The rank-one `O`-sheaf `ℱ_χ` of a continuous character `χ : π₁(X, x̄) → O^×`.** -/
public def characterSheaf (hχ : Continuous (characterRepresentation B X x b χ)) :
    LAdicSheaf.CoefficientSheaf B X ℓ O :=
  representationCoefficientSheaf B X x (characterRepresentation B X x b χ) hχ
    (Algebra.leftMulMatrix b).toRingHom (leftMulMatrix_commute B X x b χ)

variable (hχ : Continuous (characterRepresentation B X x b χ))

/-- The stalk of `ℱ_χ` at `s̄` is `O`, along a path `t` from `s̄` to `x̄`, as `ℤ_ℓ`-modules. -/
public def characterSheafStalkEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) :
    LAdicSheaf.stalk B X ℓ (characterSheaf B X x b χ hχ).toLAdicSheaf s ≃ₗ[ℤ_[ℓ]] O :=
  (representationLevelTrivialization B X x (characterRepresentation B X x b χ) hχ
    t).stalkEquiv.trans b.equivFun.symm

/-- Under `b.equivFun.symm`, multiplication by `leftMulMatrix b o` is multiplication by `o`. -/
private theorem equivFun_symm_leftMulMatrix_mulVec (o : O) (w : Fin d → ℤ_[ℓ]) :
    b.equivFun.symm (Algebra.leftMulMatrix b o *ᵥ w) = o * b.equivFun.symm w := by
  have hw : (b.repr (b.equivFun.symm w) : Fin d → ℤ_[ℓ]) = w := b.equivFun.apply_symm_apply w
  rw [← hw, Algebra.leftMulMatrix_mulVec_repr]
  change b.equivFun.symm (b.equivFun _) = _
  rw [LinearEquiv.symm_apply_apply, hw]

/-- `characterSheafStalkEquiv` is `O`-linear: it sends `o • v` to
`o * characterSheafStalkEquiv t v`. -/
public theorem characterSheafStalkEquiv_smul {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (o : O)
    (v : LAdicSheaf.stalk B X ℓ (characterSheaf B X x b χ hχ).toLAdicSheaf s) :
    characterSheafStalkEquiv B X x b χ hχ t (o • v) =
      o * characterSheafStalkEquiv B X x b χ hχ t v := by
  have h := representationLevelTrivialization_stalkEquiv_stalkMap B X x hχ hχ t
    ((Algebra.leftMulMatrix b).toRingHom o) (leftMulMatrix_commute B X x b χ o) v
  refine (congrArg b.equivFun.symm h).trans ?_
  exact equivFun_symm_leftMulMatrix_mulVec b o _

/-- **The stalk of `ℱ_χ` is free of rank one over `O`**, along a path `t` from `s̄` to `x̄`. -/
public def characterSheafStalkLinearEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) :
    LAdicSheaf.stalk B X ℓ (characterSheaf B X x b χ hχ).toLAdicSheaf s ≃ₗ[O] O :=
  { characterSheafStalkEquiv B X x b χ hχ t with
    map_smul' := fun o v => characterSheafStalkEquiv_smul B X x b χ hχ t o v }

/-- **An endomorphism `a` of the geometric point `s̄` acts on the stalk of `ℱ_χ` by multiplication
by `χ(g)`**, where `g ∈ π₁(X, x̄)` is the transport along `t` of the automorphism `σ` of the fibre
functor at `s̄` given by precomposition with `a`. -/
public theorem characterSheafStalkLinearEquiv_stalkEnd {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.asIso.hom = finiteEtaleFiberMap a)
    (v : LAdicSheaf.stalk B X ℓ (characterSheaf B X x b χ hχ).toLAdicSheaf s) :
    characterSheafStalkLinearEquiv B X x b χ hχ t ((characterSheaf B X x b χ hχ).stalkEnd a v) =
      (χ (etaleFundamentalGroupMulEquiv t σ) : O) *
        characterSheafStalkLinearEquiv B X x b χ hχ t v := by
  set T := representationLevelTrivialization B X x (characterRepresentation B X x b χ) hχ t
  have hT : T.stalkEquiv (LAdicSheaf.stalkEnd B X ℓ _ a v) =
      (characterRepresentation B X x b χ (etaleFundamentalGroupMulEquiv t σ)).val *ᵥ
        T.stalkEquiv v := by
    funext i
    apply eq_of_toZModPow_succ_eq
    intro n
    rw [LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv]
    change T.equiv n ((finiteLevelStalkEnd B X ℓ _ a n).hom (v.1 n)) i = _
    have hl := congrArg ULift.down (ULift.ext
      (representationLevelStalkIso_geometricPointStalkMap B X x _ hχ t a σ hσ (n + 1) (v.1 n)))
    change T.equiv n ((finiteLevelStalkEnd B X ℓ _ a n).hom (v.1 n)) =
      levelRepresentation _ (n + 1) _ (T.equiv n (v.1 n)) at hl
    rw [hl, levelRepresentation_apply, RingHom.map_mulVec]
    congr 2
    funext j
    exact (LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv T v n j).symm
  change b.equivFun.symm (T.stalkEquiv (LAdicSheaf.stalkEnd B X ℓ _ a v)) =
    _ * b.equivFun.symm (T.stalkEquiv v)
  rw [hT, characterRepresentation_val]
  exact equivFun_symm_leftMulMatrix_mulVec b _ _

/-- **The geometric point action on the stalk of `ℱ_χ` is the scalar `χ(g)`.** -/
public theorem characterSheaf_stalkEnd_eq_smul {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (a : GeometricPoint.Hom s s)
    (σ : EtaleFundamentalGroup X.1 s) (hσ : σ.asIso.hom = finiteEtaleFiberMap a) :
    (characterSheaf B X x b χ hχ).stalkEnd a =
      (χ (etaleFundamentalGroupMulEquiv t σ) : O) • LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  apply (characterSheafStalkLinearEquiv B X x b χ hχ t).injective
  rw [characterSheafStalkLinearEquiv_stalkEnd B X x b χ hχ t a σ hσ, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul, smul_eq_mul]

end Character

end Stacks.EtaleCohomology
