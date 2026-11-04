module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseSheafRestrictScalarsIntegers
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RepresentationLAdicSheafLevels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PermutationModuleCount
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PadicIntegerRingIntertwiner

/-!
# Levels of an `O`-model against the levels of an ℓ-adic sheaf of representations

Let `X` be a connected Noetherian scheme of a big étale site with a geometric point `x̄`, `O` a
finite free `ℤ_ℓ`-algebra with basis `β`, `τ_O : π₁(X, x̄) → GL_m(O)` a representation whose
reductions modulo every `ℓᵏ` have open kernel, and `ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` continuous. Integral
intertwiners `A`, `A'` between `Res_β τ_O` and `ρ` with `A A' = A' A = ℓᵃ` give, at every level
`n`, an `ℓᵃ`-isogeny of sheaves of `ℤ_ℓ`-modules between the lisse sheaf of `(O/ℓ^{n+1})^m`
(`π₁` acting through `τ_O mod ℓ^{n+1}`), with scalars restricted along `ℤ_ℓ → O/ℓ^{n+1}`, and the
`n`-th level of `ℱ_ρ` (`Stacks.EtaleCohomology.exists_levelIsogeny_lisseEtaleSheaf_padicTower`).
It carries multiplication by `o ∈ O` to the map of levels of any intertwiner `M` of `ρ` with
`A Res_β(o) = M A` and `A' M = Res_β(o) A'`. This compares the Fourier side of Laumon's argument
with the Fourier family sheaf in piece L6 of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.levelModuleHom_comp`, `Stacks.EtaleCohomology.levelModuleHom_congr`,
  `Stacks.EtaleCohomology.levelModuleHom_nsmul_one`.
* `Stacks.EtaleCohomology.exists_levelIsogeny_lisseEtaleSheaf_padicTower`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Stacks.GroupCohomology Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] neZero_pow_of_fact_prime discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

section LevelModule

variable {ℓ : ℕ} [Fact ℓ.Prime] {r r' r'' : ℕ} {G : Type (u + 1)} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ρ : G →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ)
  {ρ' : G →* GL (Fin r') ℤ_[ℓ]} (hρ' : Continuous ρ') {ρ'' : G →* GL (Fin r'') ℤ_[ℓ]}
  (hρ'' : Continuous ρ'')

/-- The maps of level modules of intertwiners compose as the intertwiners do. -/
theorem levelModuleHom_comp (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (A' : Matrix (Fin r'') (Fin r') ℤ_[ℓ])
    (hA' : ∀ g, A' * (ρ' g).val = (ρ'' g).val * A') (k : ℕ) :
    levelModuleHom hρ hρ' A hA k ≫ levelModuleHom hρ' hρ'' A' hA' k =
      levelModuleHom hρ hρ'' (A' * A) (fun g => by
        rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc, hA', Matrix.mul_assoc]) k := by
  apply finiteTypeContinuousModule_hom_ext
  intro y
  apply ULift.ext
  show A'.map (PadicInt.toZModPow k) *ᵥ (A.map (PadicInt.toZModPow k) *ᵥ y.down) =
    (A' * A).map (PadicInt.toZModPow k) *ᵥ y.down
  rw [Matrix.mulVec_mulVec, Matrix.map_mul]

/-- The map of level modules of an intertwiner depends only on the matrix. -/
theorem levelModuleHom_congr {A A' : Matrix (Fin r') (Fin r) ℤ_[ℓ]} (h : A = A')
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (hA' : ∀ g, A' * (ρ g).val = (ρ' g).val * A')
    (k : ℕ) : levelModuleHom hρ hρ' A hA k = levelModuleHom hρ hρ' A' hA' k := by
  subst h
  rfl

/-- **The map of level modules of `N · 1` is multiplication by `N`.** -/
theorem levelModuleHom_nsmul_one (N : ℕ)
    (h : ∀ g, (N • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ])) * (ρ g).val =
      (ρ g).val * (N • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]))) (k : ℕ) :
    levelModuleHom hρ hρ (N • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ])) h k =
      finiteTypeContinuousModuleSMul (ZMod (ℓ ^ k)) _ (N : ZMod (ℓ ^ k)) := by
  apply finiteTypeContinuousModule_hom_ext
  intro y
  apply ULift.ext
  show (N • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ])).map (PadicInt.toZModPow k) *ᵥ y.down =
    (N : ZMod (ℓ ^ k)) • y.down
  rw [nsmul_one, ← RingHom.mapMatrix_apply, map_natCast, Matrix.natCast_mulVec,
    Nat.cast_smul_eq_nsmul]

/-- The maps of level modules of intertwiners respect a commuting square of matrices. -/
private theorem levelModuleHom_comm (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (S : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    (hS : ∀ g, S * (ρ g).val = (ρ g).val * S) (T : Matrix (Fin r') (Fin r') ℤ_[ℓ])
    (hT : ∀ g, T * (ρ' g).val = (ρ' g).val * T) (h : A * S = T * A) (k : ℕ) :
    levelModuleHom hρ hρ S hS k ≫ levelModuleHom hρ hρ' A hA k =
      levelModuleHom hρ hρ' A hA k ≫ levelModuleHom hρ' hρ' T hT k :=
  (levelModuleHom_comp hρ hρ hρ' S hS A hA k).trans
    ((levelModuleHom_congr hρ hρ' h _ _ k).trans
      (levelModuleHom_comp hρ hρ' hρ' A hA T hT k).symm)

end LevelModule

section Chain

variable {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D] (R : C ⥤ D)
  {P Q : C} {S W : D} (i : S ≅ R.obj P) (g : P ⟶ Q) (g' : Q ⟶ P) (j : W ≅ R.obj Q)

omit [Preadditive C] in
/-- **An isogeny `g, g'` transported along an additive functor and two isomorphisms** is an
isogeny of the same degree. -/
theorem isogeny_conj_map (k : ℕ) (hg : R.map g ≫ R.map g' = k • 𝟙 (R.obj P))
    (hg' : R.map g' ≫ R.map g = k • 𝟙 (R.obj Q)) :
    (i.hom ≫ R.map g ≫ j.inv) ≫ (j.hom ≫ R.map g' ≫ i.inv) = k • 𝟙 S ∧
      (j.hom ≫ R.map g' ≫ i.inv) ≫ (i.hom ≫ R.map g ≫ j.inv) = k • 𝟙 W := by
  constructor <;> simp [reassoc_of% hg, reassoc_of% hg']

omit [Preadditive C] [Preadditive D] in
/-- **Equivariance of a transported morphism**: if the endomorphisms commute with each piece,
they commute with the composite. -/
theorem comm_conj_map {sS : S ⟶ S} {sP : P ⟶ P} {sQ : Q ⟶ Q} {sW : W ⟶ W}
    (hi : sS ≫ i.hom = i.hom ≫ R.map sP) (hg : sP ≫ g = g ≫ sQ)
    (hj : R.map sQ ≫ j.inv = j.inv ≫ sW) :
    sS ≫ (i.hom ≫ R.map g ≫ j.inv) = (i.hom ≫ R.map g ≫ j.inv) ≫ sW := by
  rw [reassoc_of% hi, ← R.map_comp_assoc, hg, R.map_comp_assoc, hj, Category.assoc,
    Category.assoc]

omit [Preadditive C] [Preadditive D] in
/-- **Equivariance of a transported morphism, backwards.** -/
theorem comm_conj_map' {sS : S ⟶ S} {sP : P ⟶ P} {sQ : Q ⟶ Q} {sW : W ⟶ W}
    (hi : sS ≫ i.hom = i.hom ≫ R.map sP) (hg' : sQ ≫ g' = g' ≫ sP)
    (hj : R.map sQ ≫ j.inv = j.inv ≫ sW) :
    sW ≫ (j.hom ≫ R.map g' ≫ i.inv) = (j.hom ≫ R.map g' ≫ i.inv) ≫ sS := by
  have hj' : sW ≫ j.hom = j.hom ≫ R.map sQ := by
    rw [← cancel_mono j.inv, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.assoc,
      hj, Iso.hom_inv_id_assoc]
  have hi' : R.map sP ≫ i.inv = i.inv ≫ sS := by
    rw [← cancel_epi i.hom, Iso.hom_inv_id_assoc, ← reassoc_of% hi, Iso.hom_inv_id,
      Category.comp_id]
  rw [reassoc_of% hj', ← R.map_comp_assoc, hg', R.map_comp_assoc, hi']
  simp only [Category.assoc]

omit [Preadditive C] [Preadditive D] in
/-- **A morphism commuting with an isomorphism commutes with its composite with a natural
isomorphism of functors.** -/
theorem comm_symm_app_trans_mapIso {C₀ : Type*} [Category C₀] {F : C₀ ⥤ C} {S' : C₀ ⥤ D}
    (c : F ⋙ R ≅ S') {Y : C₀} (e : F.obj Y ≅ P) {φ : Y ⟶ Y} {ψ : P ⟶ P}
    (h : F.map φ ≫ e.hom = e.hom ≫ ψ) :
    S'.map φ ≫ ((c.app Y).symm ≪≫ R.mapIso e).hom =
      ((c.app Y).symm ≪≫ R.mapIso e).hom ≫ R.map ψ := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
  rw [reassoc_of% (c.inv.naturality φ), ← R.map_comp, h, R.map_comp, Category.assoc]

end Chain

section Sheaves

attribute [local instance] padicIntAlgebraOfRat

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {m r : ℕ}
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
  {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {D : ℕ}
  (β : Module.Basis (Fin D) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))

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
/-- **The lisse sheaf of `N · 1` on a level module is multiplication by `N`.** -/
theorem lisseEtaleSheaf_map_levelModuleHom_nsmul_one
    {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]}
    (hρ : Continuous ρ) (N : ℕ)
    (h : ∀ g, (N • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ])) * (ρ g).val =
      (ρ g).val * (N • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]))) (k : ℕ) :
    (lisseEtaleSheaf B X x (ZMod (ℓ ^ k))).map
        (levelModuleHom hρ hρ (N • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ])) h k) = N • 𝟙 _ := by
  rw [levelModuleHom_nsmul_one, ← etaleModuleSMul_app_lisseEtaleSheaf,
    etaleModuleSMul_app_eq_smul_id, Nat.cast_smul_eq_nsmul]

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
/-- **The lisse sheaves of intertwiners `A`, `A'` with `A' A = N · 1` compose to `N`.** -/
private theorem lisseEtaleSheaf_map_levelModuleHom_comp_of_mul {r' : ℕ}
    {ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]}
    {ρ' : EtaleFundamentalGroup X.1 x →* GL (Fin r') ℤ_[ℓ]} (hρ : Continuous ρ)
    (hρ' : Continuous ρ') (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A) (A' : Matrix (Fin r) (Fin r') ℤ_[ℓ])
    (hA' : ∀ g, A' * (ρ' g).val = (ρ g).val * A') (N : ℕ)
    (h : A' * A = N • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ])) (k : ℕ) :
    (lisseEtaleSheaf B X x (ZMod (ℓ ^ k))).map (levelModuleHom hρ hρ' A hA k) ≫
      (lisseEtaleSheaf B X x (ZMod (ℓ ^ k))).map (levelModuleHom hρ' hρ A' hA' k) = N • 𝟙 _ := by
  rw [← Functor.map_comp, levelModuleHom_comp, levelModuleHom_congr hρ hρ h _ (fun g => by
    rw [← h, Matrix.mul_assoc, hA, ← Matrix.mul_assoc, hA', Matrix.mul_assoc])]
  exact lisseEtaleSheaf_map_levelModuleHom_nsmul_one B X x hρ _ _ _

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **Levels of an `O_E`-model against the levels of `ℱ_ρ`**: integral intertwiners `A`, `A'`
between `Res_β τ_O` and `ρ` with `A A' = A' A = ℓᵃ` give, at every level `n`, an `ℓᵃ`-isogeny of
sheaves of `ℤ_ℓ`-modules between `ℱ_{τ_O mod ℓ^{n+1}}` (scalars restricted along
`ℤ_ℓ → O_E/ℓ^{n+1}`) and the `n`-th level of `ℱ_ρ`, carrying multiplication by `o ∈ O_E` to the
map of levels of every intertwiner `M` of `ρ` with `A Res_β(o) = M A` and `A' M = Res_β(o) A'`. -/
theorem exists_levelIsogeny_lisseEtaleSheaf_padicTower
    (τO : EtaleFundamentalGroup X.1 x →* GL (Fin m) (integralClosure ℤ_[ℓ] E))
    (hτO : ∀ k : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ k}))).comp τO).ker :
        Set (EtaleFundamentalGroup X.1 x)))
    (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
    (A : Matrix (Fin r) (Fin (m * D)) ℤ_[ℓ])
    (hA : ∀ g, A * (restrictScalarsRepresentation B X x β τO g).val = (ρ g).val * A)
    (A' : Matrix (Fin (m * D)) (Fin r) ℤ_[ℓ])
    (hA' : ∀ g, A' * (ρ g).val = (restrictScalarsRepresentation B X x β τO g).val * A')
    (a : ℕ) (hAA' : A * A' = ℓ ^ a • (1 : Matrix (Fin r) (Fin r) ℤ_[ℓ]))
    (hA'A : A' * A = ℓ ^ a • (1 : Matrix (Fin (m * D)) (Fin (m * D)) ℤ_[ℓ])) (n : ℕ) :
    ∃ (u : (etaleModuleRestrictScalars ((Ideal.Quotient.mk (Ideal.span
          {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})).comp
          (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).obj
        ((lisseEtaleSheaf B X x (integralClosure ℤ_[ℓ] E ⧸
          Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})).obj
          (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E ⧸
            Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})
            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span
              {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)}))).comp τO) (hτO (n + 1)))) ⟶
        (LAdicSheaf.padicTower B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ)).obj (op n))
      (u' : (LAdicSheaf.padicTower B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ)).obj (op n) ⟶
        (etaleModuleRestrictScalars ((Ideal.Quotient.mk (Ideal.span
          {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})).comp
          (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).obj
        ((lisseEtaleSheaf B X x (integralClosure ℤ_[ℓ] E ⧸
          Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})).obj
          (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E ⧸
            Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})
            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span
              {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)}))).comp τO) (hτO (n + 1))))),
      u ≫ u' = ℓ ^ a • 𝟙 _ ∧ u' ≫ u = ℓ ^ a • 𝟙 _ ∧
      ∀ (o : integralClosure ℤ_[ℓ] E) (M : Matrix (Fin r) (Fin r) ℤ_[ℓ])
        (hM : ∀ g, M * (ρ g).val = (ρ g).val * M),
        A * coefficientScalarRingHom β m o = M * A →
        A' * M = coefficientScalarRingHom β m o * A' →
        (etaleModuleRestrictScalars ((Ideal.Quotient.mk (Ideal.span
          {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})).comp
          (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
            ((etaleModuleSMul X.1 (Ideal.Quotient.mk (Ideal.span
              {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)}) o)).app _) ≫ u =
          u ≫ (LAdicSheaf.padicTowerMap (representationLAdicSheafMap B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ M hM)).app
              (op n) ∧
        (LAdicSheaf.padicTowerMap (representationLAdicSheafMap B X x
            (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ M hM)).app
              (op n) ≫ u' =
          u' ≫ (etaleModuleRestrictScalars ((Ideal.Quotient.mk (Ideal.span
            {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})).comp
            (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E))) X.1).map
              ((etaleModuleSMul X.1 (Ideal.Quotient.mk (Ideal.span
                {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)}) o)).app _) := by
  have hRes := continuous_restrictScalarsRepresentation_of_isOpen B X x β τO hτO
  have hw : (Ideal.Quotient.mk (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})).comp
      (algebraMap ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)) =
      (ZMod.castHom dvd_rfl (integralClosure ℤ_[ℓ] E ⧸
        Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})).comp
        (PadicInt.toZModPow (p := ℓ) (n + 1)) :=
    RingHom.ext fun c => mk_algebraMap_eq_castHom_toZModPow (n + 1) c
  have h₁ :=
    lisseEtaleSheaf_map_levelModuleHom_comp_of_mul B X x hRes hρ A hA A' hA' _ hA'A (n + 1)
  have h₂ :=
    lisseEtaleSheaf_map_levelModuleHom_comp_of_mul B X x hρ hRes A' hA' A hA _ hAA' (n + 1)
  let i := ((etaleModuleRestrictScalarsComp (PadicInt.toZModPow (p := ℓ) (n + 1))
    (ZMod.castHom dvd_rfl (integralClosure ℤ_[ℓ] E ⧸
      Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})) _ hw X.1).app _).symm ≪≫
    (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1).mapIso
      (lisseEtaleSheafRestrictScalarsIntegersIso B X x β τO hRes (n + 1) (hτO (n + 1)))
  have hiso :=
    isogeny_conj_map (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1)
      i _ _ (padicTowerRepresentationLAdicSheafIso B X x ρ hρ n) (ℓ ^ a)
      (by rw [← Functor.map_comp, h₁]; simp)
      (by rw [← Functor.map_comp, h₂]; simp)
  refine ⟨_, _, hiso.1, hiso.2, fun o M hM hAM hMA => ?_⟩
  have h₃ := lisseEtaleSheafRestrictScalarsIntegersIso_smul B X x β τO hRes (n + 1) (hτO (n + 1)) o
  rw [← etaleModuleSMul_app_eq_smul_id] at h₃
  have hi := comm_symm_app_trans_mapIso _ (etaleModuleRestrictScalarsComp
    (PadicInt.toZModPow (p := ℓ) (n + 1)) (ZMod.castHom dvd_rfl (integralClosure ℤ_[ℓ] E ⧸
      Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E) ^ (n + 1)})) _ hw X.1) _ h₃
  have hj : (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (n + 1)) X.1).map
        ((lisseEtaleSheaf B X x (ZMod (ℓ ^ (n + 1)))).map (levelModuleHom hρ hρ M hM (n + 1))) ≫
        (padicTowerRepresentationLAdicSheafIso B X x ρ hρ n).inv =
      (padicTowerRepresentationLAdicSheafIso B X x ρ hρ n).inv ≫
        (LAdicSheaf.padicTowerMap (representationLAdicSheafMap B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) hρ hρ M hM)).app
            (op n) := by
    rw [Iso.eq_inv_comp, ← Category.assoc,
      ← padicTowerRepresentationLAdicSheafIso_naturality B X x hρ hρ M hM n, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  exact ⟨comm_conj_map _ i _ _ hi (by
      simpa only [← Functor.map_comp] using
        congrArg _ (levelModuleHom_comm hRes hρ A hA _ _ M hM hAM (n + 1))) hj,
    comm_conj_map' _ i _ _ hi (by
      simpa only [← Functor.map_comp] using
        congrArg _ (levelModuleHom_comm hρ hRes A' hA' M hM _ _ hMA (n + 1))) hj⟩

end Sheaves

end Stacks.EtaleCohomology

end
