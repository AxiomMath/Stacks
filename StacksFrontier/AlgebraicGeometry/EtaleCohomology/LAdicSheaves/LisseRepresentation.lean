module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FlatStalkTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseFiniteLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationOfTrivializations
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk

/-!
# A lisse ℓ-adic sheaf comes from a continuous representation of `π₁`

Let `X` be a connected scheme with a geometric point `x̄`. Stated before
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) ("Fundamental groups and lisse sheaves"):
lisse ℓ-adic sheaves on `X` are the finitely generated `ℤ_ℓ`-modules with continuous
`π₁(X, x̄)`-action, and lisse `ℚ_ℓ`-sheaves correspond to continuous
`ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)`. This file proves the direction needed to pass from a lisse sheaf
to a representation: **every lisse ℓ-adic sheaf `F` is isogenous to the sheaf `ℱ_ρ` of a
continuous `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)`**, i.e. there are morphisms `F → ℱ_ρ → F` whose composites
in both orders are multiplication by a power of `ℓ` (so `F ⊗ ℚ_ℓ ≅ ℱ_ρ` as `ℚ_ℓ`-sheaves).

The proof: pass to the torsion-free model `F' = ℓᴺ F` (isogenous to `F`, with flat levels). Its
finite-level stalks at `x̄` are free over `ℤ/ℓⁿ⁺¹ℤ` of one rank `r` with compatible bases
(`Stacks.EtaleCohomology.LAdicSheaf.flatLevelTrivialization`); the levels are finite locally
constant, so by Tag 0DV5 they are the finite `π₁`-modules given by the stalks at `x̄`, and the
bases turn the actions into a continuous `ρ' : π₁ → GL_r(ℤ_ℓ)` with `F' ≅ ℱ_{ρ'}` levelwise
(`Stacks.EtaleCohomology.trivializationRepresentation`). Finally `ℱ_ρ` for `ρ = ρ' ⊗ ℚ_ℓ` is
built from an integral conjugate of `ρ`, which differs from `ρ'` by a matrix `P ∈ GL_r(ℚ_ℓ)`;
`ℓᵃ P` and `ℓᵇ P⁻¹` are integral intertwiners whose products are `ℓᵃ⁺ᵇ`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.forget₂_finiteLevelStalkTransition`: the stalk transition of
  an ℓ-adic sheaf is the map of abelian stalks induced by the transition.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_torsionFreeModel_iso_representationLAdicSheaf`: the
  torsion-free model of a lisse ℓ-adic sheaf is `ℱ_{ρ'}` for a continuous
  `ρ' : π₁ → GL_r(ℤ_ℓ)`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse`: a lisse
  ℓ-adic sheaf is isogenous to `ℱ_ρ` for a continuous `ρ : π₁ → GL_r(ℚ_ℓ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.ConstantSheaf Stacks.GroupCohomology Stacks.ZModPrimePower

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### Scalar intertwiners and integral rescaling -/

section Scalars

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (e : (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory ≌
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory)
  [e.functor.Additive] {r : ℕ}
  {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]} (hρ' : Continuous ρ')
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- The morphism induced by an intertwiner depends only on the underlying matrix. -/
private theorem representationLAdicSheafMap_congr {A A' : Matrix (Fin r) (Fin r) ℤ_[ℓ]}
    (h : A = A') (hA : ∀ g, A * (ρ g).val = (ρ g).val * A)
    (hA' : ∀ g, A' * (ρ g).val = (ρ g).val * A') :
    representationLAdicSheafMap B X x e hρ hρ A hA =
      representationLAdicSheafMap B X x e hρ hρ A' hA' := by
  subst h
  rfl

/-- **The scalar matrix `k` induces multiplication by `k`** on `ℱ_ρ`. -/
public theorem representationLAdicSheafMap_nsmul_one (k : ℕ)
    (hk : ∀ g, (k • 1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * (ρ g).val = (ρ g).val * (k • 1)) :
    representationLAdicSheafMap B X x e hρ hρ (k • 1) hk =
      k • 𝟙 (representationLAdicSheaf B X x e ρ hρ) := by
  have hc : ∀ (A : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (c : ℕ) g,
      (c • A) * (ρ g).val = (ρ g).val * (c • A) ↔ c • (A * (ρ g).val) = c • ((ρ g).val * A) := by
    intro A c g
    rw [Matrix.smul_mul, Matrix.mul_smul]
  have hscal : ∀ (c : ℕ) g, (c • 1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * (ρ g).val =
      (ρ g).val * (c • 1) := fun c g => (hc 1 c g).2 (by rw [one_mul, mul_one])
  have h1 : ∀ g, (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * (ρ g).val = (ρ g).val * 1 := fun g => by
    rw [one_mul, mul_one]
  induction k with
  | zero =>
    have h0 : ∀ g, (0 : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * (ρ g).val = (ρ g).val * 0 := fun g => by
      rw [zero_mul, mul_zero]
    have hadd := representationLAdicSheafMap_add B X x e hρ hρ 0 0 h0 h0
    rw [representationLAdicSheafMap_congr B X x e hρ (add_zero 0) _ h0] at hadd
    rw [representationLAdicSheafMap_congr B X x e hρ (zero_smul ℕ 1) hk h0, zero_smul]
    exact add_eq_left.1 hadd.symm
  | succ k ih =>
    rw [representationLAdicSheafMap_congr B X x e hρ (succ_nsmul 1 k) hk
      (fun g => by rw [Matrix.add_mul, Matrix.mul_add, hscal k g, h1 g]),
      representationLAdicSheafMap_add B X x e hρ hρ _ _ (hscal k) h1, ih (hscal k),
      representationLAdicSheafMap_one, succ_nsmul]

/-- Intertwiners whose product is the scalar matrix `k` compose to multiplication by `k`. -/
private theorem representationLAdicSheafMap_comp_eq_nsmul (A A' : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (hA' : ∀ g, A' * (ρ' g).val = (ρ g).val * A')
    (k : ℕ) (h : A' * A = k • 1) :
    representationLAdicSheafMap B X x e hρ hρ' A hA ≫
      representationLAdicSheafMap B X x e hρ' hρ A' hA' = k • 𝟙 _ := by
  rw [← representationLAdicSheafMap_mul,
    representationLAdicSheafMap_congr B X x e hρ h _ (fun g => by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]),
    representationLAdicSheafMap_nsmul_one]

end Scalars

/-- **Every matrix over `ℚ_ℓ` becomes integral after multiplication by a power of `ℓ`.** -/
public theorem exists_isIntegralMatrix_pow_smul {r : ℕ} (A : Matrix (Fin r) (Fin r) ℚ_[ℓ]) :
    ∃ a : ℕ, IsIntegralMatrix (((ℓ : ℚ_[ℓ]) ^ a) • A) := by
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt (∑ i, ∑ j, ‖A i j‖) hℓ
  refine ⟨a, fun i j => ?_⟩
  have hij : ‖A i j‖ ≤ ∑ i, ∑ j, ‖A i j‖ :=
    (Finset.single_le_sum (f := fun j => ‖A i j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow, Padic.norm_p, inv_pow]
  have hpos : (0 : ℝ) < (ℓ : ℝ) ^ a := pow_pos (by linarith) a
  rw [inv_mul_le_iff₀ hpos, mul_one]
  exact hij.trans ha.le

/-! ### Stalk transitions on underlying abelian groups -/

section Stalk

variable {B : BigEtaleSite.{u}} {X : B.Scheme}

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
variable [IsNoetherian X.1]

namespace LAdicSheaf

/-- **The stalk transition of an ℓ-adic sheaf, on underlying abelian groups, is the map of
abelian stalks induced by the transition of underlying abelian sheaves.** -/
public theorem forget₂_finiteLevelStalkTransition (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (s : GeometricPoint X.1) (n : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) AddCommGrpCat.{u + 1}).map
        (finiteLevelStalkTransition B X ℓ F s n) ≫
        (etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ (n + 1))) (F.level n)).hom =
      (etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ (n + 1 + 1))) (F.level (n + 1))).hom ≫
        (abelianEtaleStalkFunctor.{u, u + 1} B X.1 X.2 s).map
          (underlyingLAdicTransition B X ℓ F n) := by
  let π := (Functor.Elements.π (geometricPointFiber B X.1 X.property s)).op
  let f₁ := forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) AddCommGrpCat.{u + 1}
  let f₀ := forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}
  let res := ModuleCat.restrictScalars.{u + 1} (finiteLevelRingHom ℓ n)
  let D₁ := π ⋙ (F.level (n + 1)).obj
  let D₀ := π ⋙ (F.level n).obj
  refine (isColimitOfPreserves f₁ (colimit.isColimit D₁)).hom_ext fun j => ?_
  change f₁.map (colimit.ι D₁ j) ≫ _ = f₁.map (colimit.ι D₁ j) ≫ _
  have hT : colimit.ι D₁ j ≫ colim.map (Functor.whiskerLeft π (F.transition n).hom) ≫
        (preservesColimitIso res D₀).inv =
      (F.transition n).hom.app (π.obj j) ≫ res.map (colimit.ι D₀ j) := by
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (colimit.ι_map _ j))).trans ?_
    exact (Category.assoc _ _ _).trans
      (congrArg ((F.transition n).hom.app (π.obj j) ≫ ·) (ι_preservesColimitIso_inv res D₀ j))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ((f₁.map_comp _ _).symm.trans ((congrArg f₁.map hT).trans
    (f₁.map_comp _ _)))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (_ ≫ ·) (ι_preservesColimitIso_hom f₀ D₀ j)) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (· ≫ _) (ι_preservesColimitIso_hom f₁ D₁ j)).symm
  exact (colimit.ι_map (Functor.whiskerLeft π (underlyingLAdicTransition B X ℓ F n).hom) j).symm

end LAdicSheaf

end Stalk

/-! ### The torsion-free model of a lisse sheaf is the sheaf of a `ℤ_ℓ`-representation -/

section TorsionFree

variable {B : BigEtaleSite.{u}} {X : B.Scheme} [ConnectedSpace X.1] (x : GeometricPoint X.1)

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
variable [IsNoetherian X.1]

namespace LAdicSheaf

attribute [local instance] underlyingLevelFunctor_full

variable (F : LAdicSheaf.{u, u + 1} B X ℓ) (hF : F.IsLisse)

/-- The level `n` of the torsion-free model `ℓᴺ F` of a lisse `F` (`N` the torsion bound), as a
finite locally constant abelian sheaf. -/
public def lisseTorsionFreeLevel (n : ℕ) :
    (isFiniteLocallyConstantAbelianSheaf.{u, u + 1, u + 1}
      (SmallEtale.topology B X.1 X.2)).FullSubcategory :=
  ⟨underlyingLAdicLevel B X ℓ (torsionFreeModel F (torsionBound F)) n,
    isFiniteLocallyConstant_underlyingLAdicLevel_torsionFreeModel F hF _ n⟩

/-- The transition of the torsion-free model, between finite locally constant abelian sheaves. -/
public def lisseTorsionFreeTransition (n : ℕ) :
    lisseTorsionFreeLevel F hF (n + 1) ⟶ lisseTorsionFreeLevel F hF n :=
  ObjectProperty.homMk (underlyingLAdicTransition B X ℓ (torsionFreeModel F (torsionBound F)) n)

/-- The finite `π₁(X, x̄)`-module attached by Tag 0DV5 to the level `n` of the torsion-free
model. -/
public abbrev lisseTorsionFreeFibre (n : ℕ) :
    (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} (EtaleFundamentalGroup X.1 x)).FullSubcategory :=
  (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor.obj
    (lisseTorsionFreeLevel F hF n)

/-- The transitions of these `π₁(X, x̄)`-modules. -/
public abbrev lisseTorsionFreeFibreTransition (n : ℕ) :
    lisseTorsionFreeFibre x F hF (n + 1) ⟶ lisseTorsionFreeFibre x F hF n :=
  (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor.map
    (lisseTorsionFreeTransition F hF n)

/-- The finite-level stalk at `x̄` of the torsion-free model is the `π₁(X, x̄)`-module attached to
the level, as abelian groups. -/
public def lisseTorsionFreeStalkIso (n : ℕ) :
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}).obj
        (finiteLevelStalk B X ℓ (torsionFreeModel F (torsionBound F)) x n) ≅
      (ContinuousGAddCommGrp.forget _).obj (lisseTorsionFreeFibre x F hF n).obj :=
  etaleStalkForget₂Iso B X.1 X.2 x (ZMod (ℓ ^ (n + 1)))
      ((torsionFreeModel F (torsionBound F)).level n) ≪≫
    (finiteLocallyConstantAbelianStalkIso B X (Iso.refl (finiteEtaleFiberFunctor x))).app
      (lisseTorsionFreeLevel F hF n)

/-- The stalk transition is the transition of the `π₁(X, x̄)`-modules. -/
public theorem lisseTorsionFreeStalkIso_transition (n : ℕ)
    (y : finiteLevelStalk B X ℓ (torsionFreeModel F (torsionBound F)) x (n + 1)) :
    (lisseTorsionFreeStalkIso x F hF n).hom
        (LAdicSheaf.stalkTransition B X ℓ (torsionFreeModel F (torsionBound F)) x n y) =
      (lisseTorsionFreeFibreTransition x F hF n).hom.hom.hom.hom.hom
        ((lisseTorsionFreeStalkIso x F hF (n + 1)).hom y) := by
  have h1 := ConcreteCategory.congr_hom
    (forget₂_finiteLevelStalkTransition (torsionFreeModel F (torsionBound F)) x n) y
  have h2 := ConcreteCategory.congr_hom
    ((finiteLocallyConstantAbelianStalkIso B X
      (Iso.refl (finiteEtaleFiberFunctor x))).hom.naturality (lisseTorsionFreeTransition F hF n))
    ((etaleStalkForget₂Iso B X.1 X.2 x (ZMod (ℓ ^ (n + 1 + 1)))
      ((torsionFreeModel F (torsionBound F)).level (n + 1))).hom y)
  change (finiteLocallyConstantAbelianStalkIso B X (Iso.refl (finiteEtaleFiberFunctor x))).hom.app
      (lisseTorsionFreeLevel F hF n) ((etaleStalkForget₂Iso B X.1 X.2 x (ZMod (ℓ ^ (n + 1)))
        ((torsionFreeModel F (torsionBound F)).level n)).hom
          ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) AddCommGrpCat.{u + 1}).map
            (finiteLevelStalkTransition B X ℓ (torsionFreeModel F (torsionBound F)) x n) y)) = _
  exact (congrArg (ConcreteCategory.hom ((finiteLocallyConstantAbelianStalkIso B X
    (Iso.refl (finiteEtaleFiberFunctor x))).hom.app (lisseTorsionFreeLevel F hF n))) h1).trans h2

omit [ConnectedSpace X.1] in
/-- The finite-level stalks of the torsion-free model are flat. -/
public theorem isPowExact_finiteLevelStalk_torsionFreeModel (n : ℕ) :
    IsPowExact ℓ (n + 1) (finiteLevelStalk B X ℓ (torsionFreeModel F (torsionBound F)) x n) :=
  LAdicSheaf.isPowExact_finiteLevelStalk _ x n (powExact_torsionFreeModel_level F le_rfl n)

/-- The rank of the torsion-free model at `x̄`. -/
public abbrev lisseRank : ℕ :=
  LAdicSheaf.flatStalkRank (torsionFreeModel F (torsionBound F)) x

/-- Coordinates on the `π₁(X, x̄)`-modules of the levels: compatible bases of the flat
finite-level stalks, transported along
`Stacks.EtaleCohomology.LAdicSheaf.lisseTorsionFreeStalkIso`. -/
public def lisseTorsionFreeCoordinates (n : ℕ) :
    (lisseTorsionFreeFibre x F hF n).obj.obj.obj.V ≃+ (Fin (lisseRank x F) → ZMod (ℓ ^ (n + 1))) :=
  (lisseTorsionFreeStalkIso x F hF n).symm.addCommGroupIsoToAddEquiv.trans
    ((LAdicSheaf.flatLevelTrivialization _ x
      (isPowExact_finiteLevelStalk_torsionFreeModel x F)).equiv n)

/-- The coordinates carry the transitions to reduction. -/
public theorem lisseTorsionFreeCoordinates_transition (n : ℕ)
    (y : (lisseTorsionFreeFibre x F hF (n + 1)).obj.obj.obj.V) :
    lisseTorsionFreeCoordinates x F hF n
        ((lisseTorsionFreeFibreTransition x F hF n).hom.hom.hom.hom.hom y) =
      levelReduction (n + 1) (lisseTorsionFreeCoordinates x F hF (n + 1) y) := by
  have h := lisseTorsionFreeStalkIso_transition x F hF n
    ((lisseTorsionFreeStalkIso x F hF (n + 1)).inv y)
  have hy : (lisseTorsionFreeStalkIso x F hF (n + 1)).hom
      ((lisseTorsionFreeStalkIso x F hF (n + 1)).inv y) = y :=
    ConcreteCategory.congr_hom (lisseTorsionFreeStalkIso x F hF (n + 1)).inv_hom_id y
  rw [hy] at h
  change ((LAdicSheaf.flatLevelTrivialization _ x
      (isPowExact_finiteLevelStalk_torsionFreeModel x F)).equiv n)
      ((lisseTorsionFreeStalkIso x F hF n).inv
        ((lisseTorsionFreeFibreTransition x F hF n).hom.hom.hom.hom.hom y)) = _
  have hz : (lisseTorsionFreeStalkIso x F hF n).inv ((lisseTorsionFreeStalkIso x F hF n).hom
      (LAdicSheaf.stalkTransition B X ℓ (torsionFreeModel F (torsionBound F)) x n
        ((lisseTorsionFreeStalkIso x F hF (n + 1)).inv y))) =
      LAdicSheaf.stalkTransition B X ℓ (torsionFreeModel F (torsionBound F)) x n
        ((lisseTorsionFreeStalkIso x F hF (n + 1)).inv y) :=
    ConcreteCategory.congr_hom (lisseTorsionFreeStalkIso x F hF n).hom_inv_id _
  rw [← h, hz]
  exact (LAdicSheaf.flatLevelTrivialization _ x
    (isPowExact_finiteLevelStalk_torsionFreeModel x F)).transition n _

/-- **The `ℤ_ℓ`-representation `ρ' : π₁(X, x̄) →* GL_r(ℤ_ℓ)` of a lisse ℓ-adic sheaf**: the action
of `π₁(X, x̄)` on the inverse limit of the finite-level stalks at `x̄` of its torsion-free model,
in compatible bases. -/
public abbrev lisseRepresentation :
    EtaleFundamentalGroup X.1 x →* GL (Fin (lisseRank x F)) ℤ_[ℓ] :=
  trivializationRepresentation (lisseTorsionFreeFibre x F hF)
    (lisseTorsionFreeFibreTransition x F hF) (lisseTorsionFreeCoordinates x F hF)
    (lisseTorsionFreeCoordinates_transition x F hF)

/-- `ρ'` is continuous. -/
public theorem continuous_lisseRepresentation : Continuous (lisseRepresentation x F hF) :=
  continuous_trivializationRepresentation _ _ _ _

/-- The level `n` of the torsion-free model is the level `n` of `ℱ_{ρ'}`, as finite locally
constant abelian sheaves. -/
public def lisseTorsionFreeLevelIso (n : ℕ) :
    lisseTorsionFreeLevel F hF n ≅
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj
        (levelAbelian (lisseRepresentation x F hF) (continuous_lisseRepresentation x F hF)
          (n + 1)) :=
  (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).unitIso.app _ ≪≫
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.mapIso
      (trivializationLevelIso _ _ _ (lisseTorsionFreeCoordinates_transition x F hF) n)

/-- The forward map of `lisseTorsionFreeLevelIso` is the unit of the equivalence followed by the
image under its inverse of the forward map of the trivialization level isomorphism. -/
public theorem lisseTorsionFreeLevelIso_hom (n : ℕ) :
    (lisseTorsionFreeLevelIso x F hF n).hom =
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).unit.app _ ≫
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
          (trivializationLevelIso _ _ _ (lisseTorsionFreeCoordinates_transition x F hF) n).hom :=
  rfl

/-- The level isomorphisms carry the transition of the torsion-free model to the image under the
inverse of the equivalence of the reduction map between the levels of `ℱ_{ρ'}`. -/
public theorem lisseTorsionFreeLevelIso_transition (n : ℕ) :
    lisseTorsionFreeTransition F hF n ≫ (lisseTorsionFreeLevelIso x F hF n).hom =
      (lisseTorsionFreeLevelIso x F hF (n + 1)).hom ≫
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
          (levelAbelianReduction (lisseRepresentation x F hF)
            (continuous_lisseRepresentation x F hF) (n + 1)) := by
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  rw [lisseTorsionFreeLevelIso_hom, lisseTorsionFreeLevelIso_hom, Category.assoc,
    ← e.inverse.map_comp, trivializationLevelIso_hom_comp_levelAbelianReduction
      (lisseTorsionFreeFibre x F hF) (lisseTorsionFreeFibreTransition x F hF)
      (lisseTorsionFreeCoordinates x F hF) (lisseTorsionFreeCoordinates_transition x F hF) n,
    e.inverse.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  exact e.unit.naturality (lisseTorsionFreeTransition F hF n)

/-- The inverses of the level isomorphisms carry the image under the inverse of the equivalence
of the reduction map between the levels of `ℱ_{ρ'}` to the transition of the torsion-free model. -/
public theorem lisseTorsionFreeLevelIso_inv_transition (n : ℕ) :
    (lisseTorsionFreeLevelIso x F hF (n + 1)).inv ≫ lisseTorsionFreeTransition F hF n =
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
          (levelAbelianReduction (lisseRepresentation x F hF)
            (continuous_lisseRepresentation x F hF) (n + 1)) ≫
        (lisseTorsionFreeLevelIso x F hF n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, lisseTorsionFreeLevelIso_transition]

/-- The identification of the underlying abelian sheaves of the levels of `ℓᴺ F` and `ℱ_{ρ'}`. -/
public def lisseUnderlyingLevelIso (n : ℕ) :
    (underlyingLevelFunctor B X ℓ n).obj ((torsionFreeModel F (torsionBound F)).level n) ≅
      (underlyingLevelFunctor B X ℓ n).obj ((representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (lisseRepresentation x F hF) (continuous_lisseRepresentation x F hF)).level n) :=
  (ObjectProperty.ι _).mapIso (lisseTorsionFreeLevelIso x F hF n)

/-- The identifications of underlying abelian sheaves commute with the transitions of `ℓᴺ F` and
of `ℱ_{ρ'}`. -/
public theorem lisseUnderlyingLevelIso_hom_transition (n : ℕ) :
    (underlyingLevelFunctor B X ℓ (n + 1)).map
          ((torsionFreeModel F (torsionBound F)).transition n) ≫
        (lisseUnderlyingLevelIso x F hF n).hom =
      (lisseUnderlyingLevelIso x F hF (n + 1)).hom ≫
        (underlyingLevelFunctor B X ℓ (n + 1)).map ((representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (lisseRepresentation x F hF) (continuous_lisseRepresentation x F hF)).transition n) :=
  congrArg (fun φ => φ.hom) (lisseTorsionFreeLevelIso_transition x F hF n)

/-- The inverse identifications of underlying abelian sheaves commute with the transitions of
`ℱ_{ρ'}` and of `ℓᴺ F`. -/
public theorem lisseUnderlyingLevelIso_inv_transition (n : ℕ) :
    (lisseUnderlyingLevelIso x F hF (n + 1)).inv ≫
        (underlyingLevelFunctor B X ℓ (n + 1)).map
          ((torsionFreeModel F (torsionBound F)).transition n) =
      (underlyingLevelFunctor B X ℓ (n + 1)).map ((representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (lisseRepresentation x F hF) (continuous_lisseRepresentation x F hF)).transition n) ≫
        (lisseUnderlyingLevelIso x F hF n).inv :=
  congrArg (fun φ => φ.hom) (lisseTorsionFreeLevelIso_inv_transition x F hF n)

/-- The morphism `ℓᴺ F ⟶ ℱ_{ρ'}`: on each level, the preimage of the identification of
underlying abelian sheaves. -/
public def toLisseRepresentationLAdicSheaf :
    torsionFreeModel F (torsionBound F) ⟶ (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      (lisseRepresentation x F hF) (continuous_lisseRepresentation x F hF)) where
  app n := (underlyingLevelFunctor B X ℓ n).preimage (lisseUnderlyingLevelIso x F hF n).hom
  naturality n := by
    apply (underlyingLevelFunctor B X ℓ (n + 1)).map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage,
      underlyingLevelFunctor_restrict_map, Functor.map_preimage]
    exact (lisseUnderlyingLevelIso_hom_transition x F hF n).symm

/-- The morphism `ℱ_{ρ'} ⟶ ℓᴺ F`. -/
public def fromLisseRepresentationLAdicSheaf :
    (representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (lisseRepresentation x F hF) (continuous_lisseRepresentation x F hF)) ⟶
      torsionFreeModel F (torsionBound F) where
  app n := (underlyingLevelFunctor B X ℓ n).preimage (lisseUnderlyingLevelIso x F hF n).inv
  naturality n := by
    apply (underlyingLevelFunctor B X ℓ (n + 1)).map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage,
      underlyingLevelFunctor_restrict_map, Functor.map_preimage]
    exact lisseUnderlyingLevelIso_inv_transition x F hF n

/-- **The torsion-free model of a lisse ℓ-adic sheaf is `ℱ_{ρ'}`.** -/
public def lisseTorsionFreeIso :
    torsionFreeModel F (torsionBound F) ≅
      representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (lisseRepresentation x F hF) (continuous_lisseRepresentation x F hF) where
  hom := toLisseRepresentationLAdicSheaf x F hF
  inv := fromLisseRepresentationLAdicSheaf x F hF
  hom_inv_id := by
    refine LAdicSheaf.Hom.ext B X ℓ fun n => ?_
    apply (underlyingLevelFunctor B X ℓ n).map_injective
    change (underlyingLevelFunctor B X ℓ n).map
        ((underlyingLevelFunctor B X ℓ n).preimage (lisseUnderlyingLevelIso x F hF n).hom ≫
          (underlyingLevelFunctor B X ℓ n).preimage (lisseUnderlyingLevelIso x F hF n).inv) =
      (underlyingLevelFunctor B X ℓ n).map (𝟙 _)
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage, CategoryTheory.Functor.map_id]
    exact (lisseUnderlyingLevelIso x F hF n).hom_inv_id
  inv_hom_id := by
    refine LAdicSheaf.Hom.ext B X ℓ fun n => ?_
    apply (underlyingLevelFunctor B X ℓ n).map_injective
    change (underlyingLevelFunctor B X ℓ n).map
        ((underlyingLevelFunctor B X ℓ n).preimage (lisseUnderlyingLevelIso x F hF n).inv ≫
          (underlyingLevelFunctor B X ℓ n).preimage (lisseUnderlyingLevelIso x F hF n).hom) =
      (underlyingLevelFunctor B X ℓ n).map (𝟙 _)
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage, CategoryTheory.Functor.map_id]
    exact (lisseUnderlyingLevelIso x F hF n).inv_hom_id

include hF in
/-- **The torsion-free model of a lisse ℓ-adic sheaf on a connected scheme comes from a continuous
`ℤ_ℓ`-representation of `π₁`**: `ℓᴺ F ≅ ℱ_{ρ'}` for a continuous `ρ' : π₁(X, x̄) → GL_r(ℤ_ℓ)`. -/
public theorem exists_torsionFreeModel_iso_representationLAdicSheaf :
    ∃ (r : ℕ) (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ),
      Nonempty (torsionFreeModel F (torsionBound F) ≅ representationLAdicSheaf B X x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) :=
  ⟨_, _, _, ⟨lisseTorsionFreeIso x F hF⟩⟩

variable (B X ℓ) in
include hF in
/-- **A lisse ℓ-adic sheaf on a connected scheme comes from a continuous representation of
`π₁`, up to isogeny.** For `X` connected with geometric point `x̄` and `F` a lisse ℓ-adic sheaf
on `X`, there are a continuous `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` and morphisms `φ : F → ℱ_ρ`,
`ψ : ℱ_ρ → F` whose composites in both orders are multiplication by `ℓᴺ`; so `F` and `ℱ_ρ` define
the same `ℚ_ℓ`-sheaf. This is the passage from lisse `ℚ_ℓ`-sheaves to continuous representations
stated before [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) ("Fundamental groups and lisse
sheaves").

`ℓᴺ F ≅ ℱ_{ρ'}` for a continuous `ρ' : π₁ → GL_r(ℤ_ℓ)`
(`Stacks.EtaleCohomology.LAdicSheaf.lisseTorsionFreeIso`); `ρ = ρ' ⊗ ℚ_ℓ`, whose sheaf `ℱ_ρ` is
built from the integral conjugate `σ = P⁻¹ ρ P`; then `ℓᵇ P⁻¹ : ℱ_{ρ'} → ℱ_σ` and
`ℓᵃ P : ℱ_σ → ℱ_{ρ'}` are integral intertwiners with products `ℓᵃ⁺ᵇ`. -/
public theorem exists_representationSheaf_isogeny_of_isLisse :
    ∃ (r : ℕ) (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
      (φ : F ⟶ LAdicSheaf.representationSheaf B X x ρ hρ)
      (ψ : LAdicSheaf.representationSheaf B X x ρ hρ ⟶ F) (N : ℕ),
      φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  set N := torsionBound F
  set ρZ := lisseRepresentation x F hF
  have hρZ : Continuous ρZ := continuous_lisseRepresentation x F hF
  set I := lisseTorsionFreeIso x F hF
  let ρQ : EtaleFundamentalGroup X.1 x →* GL (Fin (lisseRank x F)) ℚ_[ℓ] :=
    (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))).comp ρZ
  have hcoe : Continuous ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) := PadicInt.isOpenEmbedding_coe.continuous
  have hρQ : Continuous ρQ := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val.comp hρZ).matrix_map hcoe
    · have : (fun g => ((ρQ g)⁻¹ : GL (Fin (lisseRank x F)) ℚ_[ℓ]).val) =
          fun g => ((ρZ g)⁻¹ : GL (Fin (lisseRank x F)) ℤ_[ℓ]).val.map (↑) := by
        funext g
        rw [← map_inv]
        rfl
      rw [this]
      exact (Units.continuous_coe_inv.comp hρZ).matrix_map hcoe
  set σ := integralModel ρQ hρQ
  have hσ : Continuous σ := continuous_integralModel ρQ hρQ
  set P := (exists_conj_integral ρQ hρQ).choose
  obtain ⟨a, ha⟩ := exists_isIntegralMatrix_pow_smul P.val
  obtain ⟨b, hb⟩ := exists_isIntegralMatrix_pow_smul P⁻¹.val
  have hPP : P.val * P⁻¹.val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPP' : P⁻¹.val * P.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hσv : ∀ g, (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (σ g).val =
      P⁻¹.val * (ρQ g).val * P.val := fun g => by
    have h := congrArg Units.val (map_integralModel ρQ hρQ g)
    rw [Units.val_mul, Units.val_mul] at h
    exact h
  have hρv : ∀ g, (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (ρZ g).val = (ρQ g).val :=
    fun g => rfl
  let A := ha.lift
  let A' := hb.lift
  have hA : ∀ g, A * (σ g).val = (ρZ g).val * A := fun g => by
    apply mapMatrix_padicInt_injective
    rw [map_mul, map_mul, IsIntegralMatrix.mapMatrix_lift, hσv, hρv, Matrix.smul_mul,
      Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP,
      Matrix.one_mul]
  have hA' : ∀ g, A' * (ρZ g).val = (σ g).val * A' := fun g => by
    apply mapMatrix_padicInt_injective
    rw [map_mul, map_mul, IsIntegralMatrix.mapMatrix_lift, hσv, hρv, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hscal : ∀ (c : ℕ) (Q : Matrix (Fin (lisseRank x F)) (Fin (lisseRank x F)) ℚ_[ℓ]),
      (c : ℚ_[ℓ]) • Q = c • Q := fun c Q => Nat.cast_smul_eq_nsmul ℚ_[ℓ] c Q
  have hAA' : A * A' =
      (ℓ ^ (a + b)) • (1 : Matrix (Fin (lisseRank x F)) (Fin (lisseRank x F)) ℤ_[ℓ]) := by
    apply mapMatrix_padicInt_injective
    rw [map_mul, IsIntegralMatrix.mapMatrix_lift, IsIntegralMatrix.mapMatrix_lift, map_nsmul,
      map_one, Matrix.smul_mul, Matrix.mul_smul, hPP, smul_smul, ← pow_add, ← hscal, Nat.cast_pow]
  have hA'A : A' * A =
      (ℓ ^ (a + b)) • (1 : Matrix (Fin (lisseRank x F)) (Fin (lisseRank x F)) ℤ_[ℓ]) := by
    apply mapMatrix_padicInt_injective
    rw [map_mul, IsIntegralMatrix.mapMatrix_lift, IsIntegralMatrix.mapMatrix_lift, map_nsmul,
      map_one, Matrix.smul_mul, Matrix.mul_smul, hPP', smul_smul, ← pow_add, add_comm b a,
      ← hscal, Nat.cast_pow]
  have key := representationLAdicSheafMap_comp_eq_nsmul B X x e hρZ hσ A' A hA' hA
    (ℓ ^ (a + b)) hAA'
  have key' := representationLAdicSheafMap_comp_eq_nsmul B X x e hσ hρZ A A' hA hA'
    (ℓ ^ (a + b)) hA'A
  refine ⟨lisseRank x F, ρQ, hρQ,
    toTorsionFreeModel F N ≫ I.hom ≫ representationLAdicSheafMap B X x e hρZ hσ A' hA',
    representationLAdicSheafMap B X x e hσ hρZ A hA ≫ I.inv ≫ fromTorsionFreeModel F N,
    N + (a + b), ?_, ?_⟩
  · calc (toTorsionFreeModel F N ≫ I.hom ≫ representationLAdicSheafMap B X x e hρZ hσ A' hA') ≫
          representationLAdicSheafMap B X x e hσ hρZ A hA ≫ I.inv ≫ fromTorsionFreeModel F N
        = toTorsionFreeModel F N ≫ I.hom ≫ (representationLAdicSheafMap B X x e hρZ hσ A' hA' ≫
          representationLAdicSheafMap B X x e hσ hρZ A hA) ≫ I.inv ≫ fromTorsionFreeModel F N := by
          simp only [Category.assoc]
      _ = (ℓ ^ (a + b)) • (toTorsionFreeModel F N ≫ fromTorsionFreeModel F N) := by
          rw [key, Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
            Preadditive.comp_nsmul, Iso.hom_inv_id_assoc]
      _ = (ℓ ^ (N + (a + b))) • 𝟙 F := by
          rw [toTorsionFreeModel_comp_fromTorsionFreeModel, smul_smul, ← pow_add, add_comm]
  · calc (representationLAdicSheafMap B X x e hσ hρZ A hA ≫ I.inv ≫ fromTorsionFreeModel F N) ≫
          toTorsionFreeModel F N ≫ I.hom ≫ representationLAdicSheafMap B X x e hρZ hσ A' hA'
        = representationLAdicSheafMap B X x e hσ hρZ A hA ≫ I.inv ≫
          (fromTorsionFreeModel F N ≫ toTorsionFreeModel F N) ≫ I.hom ≫
            representationLAdicSheafMap B X x e hρZ hσ A' hA' := by
          simp only [Category.assoc]
      _ = (ℓ ^ N) • (representationLAdicSheafMap B X x e hσ hρZ A hA ≫
            representationLAdicSheafMap B X x e hρZ hσ A' hA') := by
          rw [fromTorsionFreeModel_comp_toTorsionFreeModel, Preadditive.nsmul_comp,
            Category.id_comp, Preadditive.comp_nsmul, Preadditive.comp_nsmul,
            Iso.inv_hom_id_assoc]
      _ = (ℓ ^ (N + (a + b))) • 𝟙 _ := by
          rw [key', smul_smul, ← pow_add]

end LAdicSheaf

end TorsionFree

end Stacks.EtaleCohomology

end
