module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationMorphismIntertwiner

/-!
# The matrix of a morphism `ℱ_ρ → ℱ_{ρ'}`, independent of the point and the path

Let `ρ`, `ρ'` be continuous representations of `π₁(X, x̄)` on `ℤ_ℓ^r`, `ℤ_ℓ^{r'}`. A morphism
`θ : ℱ_ρ → ℱ_{ρ'}` acts on every level by the equivariant map of level modules
`Stacks.EtaleCohomology.representationLevelHomVec` attached to it by the canonical equivalence of
Tag 0DV5 (2), at every geometric point and along every path
(`Stacks.EtaleCohomology.representationLevelTrivialization_finiteLevelStalkMap_of_hom`). Hence one
matrix `M θ`, read on the stalk at `x̄` along the trivial path
(`Stacks.EtaleCohomology.representationLAdicSheafHomMatrix`), is the matrix of `θ` on **every**
trivialised stalk
(`Stacks.EtaleCohomology.representationLevelTrivialization_stalkEquiv_stalkMap_of_hom`;
`Stacks.EtaleCohomology.exists_intertwiner_stalkEquiv_stalkMap` gives a matrix for each point and
path separately). `M θ` is an intertwiner
(`Stacks.EtaleCohomology.representationLAdicSheafHomMatrix_mul`)
and `θ ↦ M θ` is a ring homomorphism `End ℱ_ρ →+* M_r(ℤ_ℓ)`
(`Stacks.EtaleCohomology.representationLAdicSheafEndMatrix`). This turns an action of coefficients
on `ℱ_ρ` into matrices commuting with `ρ`, compatibly with the Frobenius at every closed point, as
used in [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.representationLAdicSheafHomMatrix`,
  `Stacks.EtaleCohomology.representationLAdicSheafEndMatrix`.

## Main results

* `Stacks.EtaleCohomology.representationLevelTrivialization_stalkEquiv_stalkMap_of_hom`.
* `Stacks.EtaleCohomology.representationLAdicSheafHomMatrix_mul`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology Matrix

namespace Stacks.EtaleCohomology

section LAdic

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r r' r'' : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ')
  {ρ'' : EtaleFundamentalGroup X.1 x →* GL (Fin r'') ℤ_[ℓ]} (hρ'' : Continuous ρ'')

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The reductions of the ℓ-adic trivialisation of `θ` on a stalk are the morphisms of level
modules of `θ`. -/
public theorem toZModPow_stalkEquiv_stalkMap_of_hom
    {s : GeometricPoint X.1} (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (θ : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ')
    (v : LAdicSheaf.stalk B X ℓ (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) s) (n : ℕ) (i : Fin r') :
    PadicInt.toZModPow (n + 1)
        ((representationLevelTrivialization B X x ρ' hρ' t).stalkEquiv
          (LAdicSheaf.stalkMap θ s v) i) =
      representationLevelHomVec B X x hρ hρ'
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (n + 1) (θ.app n)
        (fun j => PadicInt.toZModPow (n + 1)
          ((representationLevelTrivialization B X x ρ hρ t).stalkEquiv v j)) i := by
  rw [LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv]
  change (representationLevelTrivialization B X x ρ' hρ' t).equiv n
    ((finiteLevelStalkMap θ s n).hom (v.1 n)) i = _
  rw [representationLevelTrivialization_finiteLevelStalkMap_of_hom]
  have hv : (representationLevelTrivialization B X x ρ hρ t).equiv n (v.1 n) = fun j =>
      PadicInt.toZModPow (n + 1)
        ((representationLevelTrivialization B X x ρ hρ t).stalkEquiv v j) := by
    funext j
    rw [LAdicSheaf.LevelTrivialization.toZModPow_stalkEquiv]
  rw [hv]

/-- **The matrix of a morphism `θ : ℱ_ρ → ℱ_{ρ'}`**: the matrix of the map of ℓ-adic stalks at `x̄`
in the trivialisations along the trivial path. -/
public def representationLAdicSheafHomMatrix
    (θ : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ') :
    Matrix (Fin r') (Fin r) ℤ_[ℓ] :=
  LinearMap.toMatrix'
    ((representationLevelTrivialization B X x ρ' hρ' (Iso.refl _)).stalkEquiv.toLinearMap ∘ₗ
      LAdicSheaf.stalkMap θ x ∘ₗ
        (representationLevelTrivialization B X x ρ hρ (Iso.refl _)).stalkEquiv.symm.toLinearMap)

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The reductions of `M θ ·` are the morphisms of level modules of `θ`. -/
public theorem toZModPow_mulVec_representationLAdicSheafHomMatrix
    (θ : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ')
    (w : Fin r → ℤ_[ℓ]) (n : ℕ) (i : Fin r') :
    PadicInt.toZModPow (n + 1) ((representationLAdicSheafHomMatrix B X x hρ hρ' θ *ᵥ w) i) =
      representationLevelHomVec B X x hρ hρ'
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (n + 1) (θ.app n)
        (fun j => PadicInt.toZModPow (n + 1) (w j)) i := by
  rw [representationLAdicSheafHomMatrix, LinearMap.toMatrix'_mulVec]
  change PadicInt.toZModPow (n + 1)
    ((representationLevelTrivialization B X x ρ' hρ' (Iso.refl _)).stalkEquiv
      (LAdicSheaf.stalkMap θ x
        ((representationLevelTrivialization B X x ρ hρ (Iso.refl _)).stalkEquiv.symm w)) i) = _
  rw [toZModPow_stalkEquiv_stalkMap_of_hom, LinearEquiv.apply_symm_apply]

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **A morphism `θ : ℱ_ρ → ℱ_{ρ'}` is multiplication by its matrix `M θ` on every stalk**,
trivialised along any path: the trivialisations of the stalks are natural in the sheaf, so
`θ` acts at every geometric point by the one equivariant map of level modules it induces. -/
public theorem representationLevelTrivialization_stalkEquiv_stalkMap_of_hom
    {s : GeometricPoint X.1} (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (θ : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ')
    (v : LAdicSheaf.stalk B X ℓ (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) s) :
    (representationLevelTrivialization B X x ρ' hρ' t).stalkEquiv (LAdicSheaf.stalkMap θ s v) =
      representationLAdicSheafHomMatrix B X x hρ hρ' θ *ᵥ
        (representationLevelTrivialization B X x ρ hρ t).stalkEquiv v := by
  funext i
  apply eq_of_toZModPow_succ_eq
  intro n
  rw [toZModPow_stalkEquiv_stalkMap_of_hom, toZModPow_mulVec_representationLAdicSheafHomMatrix]

/-- The matrix of `e' ∘ f ∘ e⁻¹` is `A` as soon as `e' (f v) = A *ᵥ e v` for all `v`. -/
private theorem toMatrix'_comp_symm_eq {R S S' : Type*} [CommRing R] [AddCommGroup S] [Module R S]
    [AddCommGroup S'] [Module R S'] (e : S ≃ₗ[R] (Fin r → R)) (e' : S' ≃ₗ[R] (Fin r' → R))
    (f : S →ₗ[R] S') (A : Matrix (Fin r') (Fin r) R) (h : ∀ v, e' (f v) = A *ᵥ e v) :
    LinearMap.toMatrix' (e'.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap) = A := by
  refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
  rw [Matrix.toLin'_toMatrix', Matrix.toLin'_apply]
  simpa using h (e.symm w)

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The matrix of a morphism `ℱ_ρ → ℱ_{ρ'}` is an intertwiner**: `M θ · ρ(g) = ρ'(g) · M θ`. -/
public theorem representationLAdicSheafHomMatrix_mul
    (θ : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ')
    (g : EtaleFundamentalGroup X.1 x) :
    representationLAdicSheafHomMatrix B X x hρ hρ' θ * (ρ g).val =
      (ρ' g).val * representationLAdicSheafHomMatrix B X x hρ hρ' θ := by
  refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  funext i
  apply eq_of_toZModPow_succ_eq
  intro n
  rw [toZModPow_mulVec_representationLAdicSheafHomMatrix, RingHom.map_mulVec]
  have hw : (fun j => PadicInt.toZModPow (n + 1) (((ρ g).val *ᵥ w) j)) =
      levelRepresentation ρ (n + 1) g (fun j => PadicInt.toZModPow (n + 1) (w j)) := by
    funext j
    rw [levelRepresentation_apply, RingHom.map_mulVec]
    rfl
  rw [hw]
  refine (congrFun (representationLevelHomVec_levelRepresentation B X x hρ hρ'
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) (n + 1) (θ.app n) g _) i).trans ?_
  rw [levelRepresentation_apply]
  congr 1
  funext j
  rw [Function.comp_apply, toZModPow_mulVec_representationLAdicSheafHomMatrix]

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The matrix of a composite is the product of the matrices. -/
public theorem representationLAdicSheafHomMatrix_comp
    (θ : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ')
    (θ' : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ' ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ'' hρ'') :
    representationLAdicSheafHomMatrix B X x hρ hρ'' (θ ≫ θ') =
      representationLAdicSheafHomMatrix B X x hρ' hρ'' θ' *
        representationLAdicSheafHomMatrix B X x hρ hρ' θ := by
  refine toMatrix'_comp_symm_eq _ _ _ _ fun v => ?_
  rw [LAdicSheaf.stalkMap_comp, ← Matrix.mulVec_mulVec]
  change (representationLevelTrivialization B X x ρ'' hρ'' (Iso.refl _)).stalkEquiv
    (LAdicSheaf.stalkMap θ' x (LAdicSheaf.stalkMap θ x v)) = _
  rw [representationLevelTrivialization_stalkEquiv_stalkMap_of_hom,
    representationLevelTrivialization_stalkEquiv_stalkMap_of_hom]

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The matrix of the identity is the identity. -/
public theorem representationLAdicSheafHomMatrix_id :
    representationLAdicSheafHomMatrix B X x hρ hρ (𝟙 _) = 1 := by
  refine toMatrix'_comp_symm_eq _ _ _ _ fun v => ?_
  rw [LAdicSheaf.stalkMap_id, Matrix.one_mulVec]
  rfl

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The matrix of a sum is the sum of the matrices. -/
public theorem representationLAdicSheafHomMatrix_add
    (θ θ' : representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ ⟶
      representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ' hρ') :
    representationLAdicSheafHomMatrix B X x hρ hρ' (θ + θ') =
      representationLAdicSheafHomMatrix B X x hρ hρ' θ +
        representationLAdicSheafHomMatrix B X x hρ hρ' θ' := by
  refine toMatrix'_comp_symm_eq _ _ _ _ fun v => ?_
  rw [LAdicSheaf.stalkMap_add, LinearMap.add_apply, map_add, Matrix.add_mulVec,
    representationLevelTrivialization_stalkEquiv_stalkMap_of_hom,
    representationLevelTrivialization_stalkEquiv_stalkMap_of_hom]

/-- **The matrix of an endomorphism of `ℱ_ρ`, as a ring homomorphism** `End ℱ_ρ →+* M_r(ℤ_ℓ)`. -/
public def representationLAdicSheafEndMatrix :
    End (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) →+*
      Matrix (Fin r) (Fin r) ℤ_[ℓ] where
  toFun θ := representationLAdicSheafHomMatrix B X x hρ hρ θ.asHom
  map_one' := representationLAdicSheafHomMatrix_id B X x hρ
  map_mul' θ θ' := representationLAdicSheafHomMatrix_comp B X x hρ hρ hρ θ'.asHom θ.asHom
  map_zero' := by
    have h := representationLAdicSheafHomMatrix_add B X x hρ hρ 0 0
    rw [add_zero] at h
    have h' := congrArg (· - representationLAdicSheafHomMatrix B X x hρ hρ 0) h
    simpa using h'.symm
  map_add' θ θ' := representationLAdicSheafHomMatrix_add B X x hρ hρ θ.asHom θ'.asHom

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The ring homomorphism `representationLAdicSheafEndMatrix` sends an endomorphism `θ` to its
matrix `representationLAdicSheafHomMatrix θ`. -/
public theorem representationLAdicSheafEndMatrix_apply
    (θ : End (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ)) :
    representationLAdicSheafEndMatrix B X x hρ θ =
      representationLAdicSheafHomMatrix B X x hρ hρ θ.asHom :=
  rfl

end LAdic

end Stacks.EtaleCohomology
