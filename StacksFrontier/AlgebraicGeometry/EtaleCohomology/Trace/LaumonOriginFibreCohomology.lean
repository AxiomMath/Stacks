module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonOriginFibreCharacter
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FibreFieldExtensionCohomologyLinear
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCoefficientInverseImageIsogeny
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCoefficientBasePointIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicLFunction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageCoefficientIsogeny
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.InducedHomInnerConjugate

/-!
# The fibre of Laumon's family over the origin

This proves `Stacks.EtaleCohomology.LaumonOriginFibreCohomologyInput`, a step of the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): for a fibre `Y` of
`pr₂ : 𝔸² = Spec k'[x][t] → W = Spec k'[t]` over the origin `y` (`t = 0`) and the family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t (xⁿ⁰ + c x))`, there is an `E`-linear isomorphism
`H¹_c(Y_k̄, K|_Y ⊗ ℚ_ℓ) ≃ H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ)` carrying the Frobenius of `κ(y)` to
`(π_U^*) ^ {d_y}` (`Stacks.EtaleCohomology.laumonOriginFibreCohomologyInput`).

Choose a geometric point `ȳ` of `Y` and identify `Y` with `U ×_k κ(y)` by `α`
(`Stacks.EtaleCohomology.isPullback_laumonFibre_curve`). The isomorphism is a chain of `E`-linear
isomorphisms commuting with the Frobenius of `κ(y)`, each induced by an isogeny compatible with
the actions of the integral parts of `E`
(`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv`); isogenies
between sheaves with three different coefficient rings are not composed directly.

1. `i⁻¹ℱ_{Res K}` at `z` ~ `i⁻¹ℱ_{Res (K ∘ φ_{t₁})}` at `i(ȳ)`: a change of base point on `𝔸²`,
   pulled back along `i`.
2. ~ `ℱ_{Res (K ∘ φ_{t₁} ∘ i_*)}` at `ȳ`: the inverse image of a representation sheaf.
3. ~ `ℱ_{Res (σ ∘ φ_{t₂} ∘ pr_* ∘ α_*)}` at `ȳ`: the two representations of `π₁(Y, ȳ)` are
   conjugate, since the Artin–Schreier factor is trivial on `Y`
   (`Stacks.EtaleCohomology.artinSchreierCharacter_laumonFibre_eq_one`) and the two maps
   `π₁(Y, ȳ) → π₁(U, x̄)` come from the same morphism `Y → U`, hence are inner conjugate
   (`AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.isInnerConjugate_of_eq`).
4. ~ `α⁻¹ ℱ_{Res (σ ∘ φ_{t₂} ∘ pr_*)}` and ~ `α⁻¹ pr⁻¹ ℱ_{Res (σ ∘ φ_{t₂})}`: inverse images.
5. `H¹_c(Y_k̄, α⁻¹ pr⁻¹ ℱ_{σ ∘ φ_{t₂}} ⊗ ℚ_ℓ) ≃ H¹_c(U_k̄, ℱ_{σ ∘ φ_{t₂}} ⊗ ℚ_ℓ)`, carrying the
   Frobenius of `κ(y)` to `(π_U^*) ^ {d_y}`
   (`LAdicSheaf.CoefficientSheaf.exists_rationalLinearEquiv_of_fieldExtensionIso`).
6. `ℱ_{Res (σ ∘ φ_{t₂})}` at `x̄''` ~ `ℱ_{Res σ}` at `x̄`: a change of base point on `U`.

## Main results

* `Stacks.EtaleCohomology.exists_linearEquiv_intertwining_trans`,
  `Stacks.EtaleCohomology.exists_linearEquiv_intertwining_symm`.
* `Stacks.EtaleCohomology.laumonOriginFibreCohomologyInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Intertwining

variable {E : Type*} [Semiring E] {M₁ M₂ M₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [Module E M₁] [Module E M₂] [Module E M₃]

/-- Linear equivalences intertwining endomorphisms compose. -/
public theorem exists_linearEquiv_intertwining_trans {A₁ : M₁ → M₁} {A₂ : M₂ → M₂}
    {A₃ : M₃ → M₃} (h₁ : ∃ e : M₁ ≃ₗ[E] M₂, ∀ v, e (A₁ v) = A₂ (e v))
    (h₂ : ∃ e : M₂ ≃ₗ[E] M₃, ∀ v, e (A₂ v) = A₃ (e v)) :
    ∃ e : M₁ ≃ₗ[E] M₃, ∀ v, e (A₁ v) = A₃ (e v) := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  exact ⟨e₁.trans e₂, fun v => by rw [LinearEquiv.trans_apply, he₁, he₂, LinearEquiv.trans_apply]⟩

/-- The inverse of a linear equivalence intertwining endomorphisms intertwines them backwards. -/
public theorem exists_linearEquiv_intertwining_symm {A₁ : M₁ → M₁} {A₂ : M₂ → M₂}
    (h : ∃ e : M₁ ≃ₗ[E] M₂, ∀ v, e (A₁ v) = A₂ (e v)) :
    ∃ e : M₂ ≃ₗ[E] M₁, ∀ v, e (A₂ v) = A₁ (e v) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun w => e.injective ?_⟩
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

/-- A linear equivalence intertwining two endomorphisms intertwines their powers. -/
public theorem linearEquiv_intertwining_pow (e : M₁ ≃ₗ[E] M₂) {A₁ : Module.End E M₁}
    {A₂ : Module.End E M₂} (h : ∀ v, e (A₁ v) = A₂ (e v)) (r : ℕ) (v : M₁) :
    e ((A₁ ^ r) v) = (A₂ ^ r) (e v) := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

end Intertwining

section Chains

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}

/-- **The inverse image of `ℱ_{Res_b σ}` along `g : Y ⟶ X` is `ℱ_{Res_b (σ ∘ φ_t ∘ g_*)}`,
`E`-linearly on `Hⁱ_c` and compatibly with the Frobenius**, for a change of base point
`t : F_x̄ ≅ F_{g(ȳ)}` on `X`: the change of base point pulled back along `g`, then the inverse
image of a representation sheaf. -/
public theorem exists_inverseImage_restrictScalarsRepCoefficientSheaf_linearEquiv {X Y : B.Scheme}
    (g : Y ⟶ X) [ConnectedSpace X.1] [ConnectedSpace Y.1] [IsNoetherian X.1] [IsNoetherian Y.1]
    {x : GeometricPoint X.1} (y : GeometricPoint Y.1)
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor (y.map g.hom))
    (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))
    (hσ' : Continuous (restrictScalarsRep b
      ((σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom).comp
        (etaleFundamentalGroupMap g.hom y).toMonoidHom)))
    {κ : Type u} [Field κ] [Fintype κ] (fY : Y.1 ⟶ Spec (.of κ)) [LocallyOfFiniteType fY]
    [QuasiCompact fY] [IsSeparated fY] (jY : CompactificationOf (Over.mk fY)) (kbar : Type u)
    [Field kbar] [Algebra κ kbar] (i : ℤ) (p q : ℕ) [Fact p.Prime] [CharP κ p]
    (hcard : Fintype.card κ = p ^ q) :
    letI := (LAdicSheaf.CoefficientSheaf.inverseImage g
      (restrictScalarsRepCoefficientSheaf B X x b σ hσ)).rationalCohomologyModule fY jY kbar i E
    letI := (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').rationalCohomologyModule fY jY kbar
      i E
    ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
        (LAdicSheaf.CoefficientSheaf.inverseImage g
          (restrictScalarsRepCoefficientSheaf B X x b σ hσ)).toLAdicSheaf i ≃ₗ[E]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
          (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').toLAdicSheaf i,
      ∀ v, e ((LAdicSheaf.CoefficientSheaf.inverseImage g
          (restrictScalarsRepCoefficientSheaf B X x b σ
            hσ)).rationalGeometricCompactlySupportedFrobenius
              fY jY kbar i E p q hcard v) =
        (restrictScalarsRepCoefficientSheaf B Y y b _
          hσ').rationalGeometricCompactlySupportedFrobenius fY jY kbar i E p q hcard (e v) := by
  have hσt : Continuous (restrictScalarsRep b
      (σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom)) :=
    hσ.comp (etaleFundamentalGroupBasePointHom t).continuous
  let F := restrictScalarsRepCoefficientSheaf B X x b σ hσ
  let F' := restrictScalarsRepCoefficientSheaf B X (y.map g.hom) b _ hσt
  let G := LAdicSheaf.CoefficientSheaf.inverseImage g F
  let G' := LAdicSheaf.CoefficientSheaf.inverseImage g F'
  let G'' := restrictScalarsRepCoefficientSheaf B Y y b _ hσ'
  let := G.rationalCohomologyModule fY jY kbar i E
  let := G'.rationalCohomologyModule fY jY kbar i E
  let := G''.rationalCohomologyModule fY jY kbar i E
  obtain ⟨φa, ψa, Na, ha₁, ha₂, hac⟩ :=
    exists_basePoint_restrictScalarsRepCoefficientSheaf_isogeny B X t b σ hσ hσt
  obtain ⟨φa', ψa', ha₁', ha₂', hac'⟩ := LAdicSheaf.CoefficientSheaf.exists_inverseImage_isogeny g F
    F' (fun o o' => algebraMap _ E o = algebraMap _ E o') φa ψa Na ha₁ ha₂ hac
  obtain ⟨φb, ψb, Nb, hb₁, hb₂, hbc⟩ :=
    exists_inverseImage_restrictScalarsRepCoefficientSheaf_isogeny B g y b _ hσt hσ'
  exact exists_linearEquiv_intertwining_trans
    ⟨LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv G G' fY jY kbar i E φa' ψa' Na ha₁'
      ha₂' hac', LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius G G' fY jY kbar i
      E φa' ψa' Na ha₁' ha₂' hac' p q hcard⟩
    ⟨LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv G' G'' fY jY kbar i E φb ψb Nb hb₁
      hb₂ hbc, LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius G' G'' fY jY kbar i
      E φb ψb Nb hb₁ hb₂ hbc p q hcard⟩

/-- **`Hⁱ_c(Y_k̄, ℱ_{Res_b (σ ∘ φ_t ∘ pr_* ∘ α_*)} ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)`,
`E`-linearly, carrying the Frobenius of `Y` over `κ` to `(π_X^*) ^ (m + 1)`**, for
`α : Y ≅ X ×_k κ` over `κ`, `#κ = q ^ (m + 1)`, and a change of base point `t` on `X`: two inverse
images (along `α` and along the projection `pr`), the base change of the field and the change of
base point. -/
public theorem exists_fieldExtension_restrictScalarsRepCoefficientSheaf_linearEquiv
    {X : B.Scheme} [ConnectedSpace X.1] [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (κ : Type u) [Field κ] [Fintype κ] [Algebra k κ]
    [Module.Finite k κ] (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra κ kbar]
    [IsScalarTower k κ kbar] [IsNoetherian (fieldExtensionScheme B X f κ).1]
    [ConnectedSpace (fieldExtensionScheme B X f κ).1]
    {Y : B.Scheme} [IsNoetherian Y.1] [ConnectedSpace Y.1] (fY : Y.1 ⟶ Spec (.of κ))
    [LocallyOfFiniteType fY] [QuasiCompact fY] [IsSeparated fY]
    (jY : CompactificationOf (Over.mk fY))
    (α : Y ⟶ fieldExtensionScheme B X f κ) [IsIso (B.inclusion.map α)]
    (hα : B.inclusion.map α ≫ pullback.snd f (specAlgebraMap k κ) = fY)
    {x : GeometricPoint X.1} (y : GeometricPoint Y.1)
    (t : finiteEtaleFiberFunctor x ≅
      finiteEtaleFiberFunctor ((y.map α.hom).map (fieldExtensionProj B X f κ).hom))
    (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))
    (hσ' : Continuous (restrictScalarsRep b
      (((σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom).comp
        (etaleFundamentalGroupMap (fieldExtensionProj B X f κ).hom (y.map α.hom)).toMonoidHom).comp
          (etaleFundamentalGroupMap α.hom y).toMonoidHom)))
    (i : ℤ) (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP κ p] (hcard : Fintype.card k = p ^ q)
    (m' : ℕ) (hcard' : Fintype.card κ = p ^ (q * (m' + 1))) :
    letI := (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').rationalCohomologyModule fY jY kbar
      i E
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar i E
    ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
        (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').toLAdicSheaf i ≃ₗ[E]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
          (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i,
      ∀ v, e ((restrictScalarsRepCoefficientSheaf B Y y b _
          hσ').rationalGeometricCompactlySupportedFrobenius
            fY jY kbar i E p (q * (m' + 1)) hcard' v) =
        (((restrictScalarsRepCoefficientSheaf B X x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius
            f j kbar i E p q hcard) ^ (m' + 1)) (e v) := by
  let pr := fieldExtensionProj B X f κ
  let σ₂ := σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom
  have hσ₂ : Continuous (restrictScalarsRep b σ₂) :=
    hσ.comp (etaleFundamentalGroupBasePointHom t).continuous
  let σ₃ := σ₂.comp (etaleFundamentalGroupMap pr.hom (y.map α.hom)).toMonoidHom
  have hσ₃ : Continuous (restrictScalarsRep b σ₃) :=
    hσ₂.comp (etaleFundamentalGroupMap pr.hom (y.map α.hom)).continuous
  let G3 := restrictScalarsRepCoefficientSheaf B Y y b _ hσ'
  let F4 := restrictScalarsRepCoefficientSheaf B (fieldExtensionScheme B X f κ) (y.map α.hom) b σ₃
    hσ₃
  let G4 := LAdicSheaf.CoefficientSheaf.inverseImage α F4
  let Fσ₂ := restrictScalarsRepCoefficientSheaf B X ((y.map α.hom).map pr.hom) b σ₂ hσ₂
  let G5 := LAdicSheaf.CoefficientSheaf.inverseImage α
    (LAdicSheaf.CoefficientSheaf.inverseImage pr Fσ₂)
  let Fσ := restrictScalarsRepCoefficientSheaf B X x b σ hσ
  let := G3.rationalCohomologyModule fY jY kbar i E
  let := G4.rationalCohomologyModule fY jY kbar i E
  let := G5.rationalCohomologyModule fY jY kbar i E
  let := Fσ₂.rationalCohomologyModule f j kbar i E
  let := Fσ.rationalCohomologyModule f j kbar i E
  -- the inverse image along `α`
  obtain ⟨φd, ψd, Nd, hd₁, hd₂, hdc⟩ :=
    exists_inverseImage_restrictScalarsRepCoefficientSheaf_isogeny B α y b σ₃ hσ₃ hσ'
  refine exists_linearEquiv_intertwining_trans (exists_linearEquiv_intertwining_symm
    ⟨LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv G4 G3 fY jY kbar i E φd ψd Nd hd₁
      hd₂ hdc, LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius G4 G3 fY jY kbar i
      E φd ψd Nd hd₁ hd₂ hdc p (q * (m' + 1)) hcard'⟩) ?_
  -- the inverse image along the projection, pulled back along `α`
  obtain ⟨φe, ψe, Ne, he₁, he₂, hec⟩ :=
    exists_inverseImage_restrictScalarsRepCoefficientSheaf_isogeny B pr (y.map α.hom) b σ₂ hσ₂ hσ₃
  obtain ⟨φe', ψe', he₁', he₂', hec'⟩ := LAdicSheaf.CoefficientSheaf.exists_inverseImage_isogeny α
    (LAdicSheaf.CoefficientSheaf.inverseImage pr Fσ₂) F4
    (fun o o' => algebraMap _ E o = algebraMap _ E o') φe ψe Ne he₁ he₂ hec
  refine exists_linearEquiv_intertwining_trans (exists_linearEquiv_intertwining_symm
    ⟨LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv G5 G4 fY jY kbar i E φe' ψe' Ne he₁'
      he₂' hec', LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius G5 G4 fY jY kbar i
      E φe' ψe' Ne he₁' he₂' hec' p (q * (m' + 1)) hcard'⟩) ?_
  -- the base change of the field `k → κ`
  refine exists_linearEquiv_intertwining_trans
    (LAdicSheaf.CoefficientSheaf.exists_rationalLinearEquiv_of_fieldExtensionIso B ℓ f j κ kbar fY
      jY α hα G5 Fσ₂ i E (𝟙 _) (𝟙 _) 0 (by rw [pow_zero, one_smul, Category.comp_id])
      (by rw [pow_zero, one_smul, Category.comp_id])
      (fun o o' ho => by rw [Category.id_comp, Category.comp_id, (Subtype.ext ho : o = o')])
      p q hcard m' hcard') ?_
  -- the change of base point on `X`
  obtain ⟨φg, ψg, Ng, hg₁, hg₂, hgc⟩ :=
    exists_basePoint_restrictScalarsRepCoefficientSheaf_isogeny B X t b σ hσ hσ₂
  exact exists_linearEquiv_intertwining_symm
    ⟨LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv Fσ Fσ₂ f j kbar i E φg ψg Ng hg₁ hg₂
      hgc, linearEquiv_intertwining_pow _
      (LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius Fσ Fσ₂ f j kbar i E φg ψg
        Ng hg₁ hg₂ hgc p q hcard) (m' + 1)⟩

end Chains

/-- **The fibre of Laumon's family over the origin**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): `H¹_c(Y_k̄, K|_Y ⊗ ℚ_ℓ) ≃
H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ)`, `E`-linearly, carrying the Frobenius of `κ(y)` to `(π_U^*) ^ {d_y}`. -/
public theorem laumonOriginFibreCohomologyInput : LaumonOriginFibreCohomologyInput.{u} := by
  intro B ℓ _ _ _ _ k _ _ U _ _ f _ _ _ e _ he j kbar _ _ _ p n _ _ hcard x E _ _ _ d b m σ hσ ψ
    n₀ k' _ _ _ c hS hL z hz p₀ hσ₁ y hy _ _ dy hcardy _ hkbar Y _ i fY _ _ _ hY jY
  obtain ⟨m', rfl⟩ : ∃ m', dy = m' + 1 :=
    Nat.exists_eq_succ_of_ne_zero (right_ne_zero_of_mul (ne_zero_of_card_eq_pow hcardy))
  let : Algebra k ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) :=
    laumonPointAlgebra (𝟙 _) y k
  have : IsScalarTower k ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)
      kbar := IsScalarTower.of_algebraMap_eq fun a => (hkbar a).symm
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  have hP1 := isPullback_laumonFibre_curve k k' f e he y i fY hY
  have hYc : ConnectedSpace Y.1 := connectedSpace_laumonFibre k k' f e he y i fY hY
  let α : Y ⟶ fieldExtensionScheme B U f
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) :=
    ObjectProperty.homMk hP1.isoPullback.hom
  have : IsIso (B.inclusion.map α) := inferInstanceAs (IsIso hP1.isoPullback.hom)
  have hα : B.inclusion.map α ≫ pullback.snd f (specAlgebraMap k
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)) = fY :=
    hP1.isoPullback_hom_snd
  have : IsNoetherian (fieldExtensionScheme B U f
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)).1 :=
    isNoetherian_fieldExtensionScheme B U f _
  have : ConnectedSpace (fieldExtensionScheme B U f
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)).1 :=
    @Function.Surjective.connectedSpace _ _ _ hYc _ _ (Scheme.homeoOfIso hP1.isoPullback).surjective
      (Scheme.homeoOfIso hP1.isoPullback).continuous
  let pr := fieldExtensionProj B U f
    ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)
  let yb : GeometricPoint Y.1 := GeometricPoint.ofPoint Y.1 (@Classical.arbitrary _ hYc.toNonempty)
  obtain ⟨t₁⟩ := nonempty_finiteEtaleFiberFunctorIso
    (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 z (yb.map i.hom)
  obtain ⟨t₂⟩ := nonempty_finiteEtaleFiberFunctorIso U.1 x ((yb.map α.hom).map pr.hom)
  subst hz
  -- the representations
  let gU := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e
  let M := (etaleFundamentalGroupMap gU (z.map (laumonFamilyPr₁ k'))).toMonoidHom
  let ψ' := ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom
  let A2 := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS
  have hσ₁' : Continuous (restrictScalarsRep b (σ.comp M)) := hσ₁
  let Lrep := laumonFamilyRep k' ψ' n₀ c z p₀ (σ.comp M)
  have hLrep : Continuous (restrictScalarsRep b Lrep) :=
    continuous_restrictScalarsRep_laumonFamilyRep k' b ψ' n₀ c z p₀ (σ.comp M) hσ₁'
  let φ₁ := (etaleFundamentalGroupBasePointHom t₁).toMonoidHom
  have hLφ : Continuous (restrictScalarsRep b (Lrep.comp φ₁)) :=
    hLrep.comp (etaleFundamentalGroupBasePointHom t₁).continuous
  let ρK := (Lrep.comp φ₁).comp (etaleFundamentalGroupMap i.hom yb).toMonoidHom
  have hρK : Continuous (restrictScalarsRep b ρK) :=
    hLφ.comp (etaleFundamentalGroupMap i.hom yb).continuous
  let σ₂ := σ.comp (etaleFundamentalGroupBasePointHom t₂).toMonoidHom
  have hσ₂ : Continuous (restrictScalarsRep b σ₂) :=
    hσ.comp (etaleFundamentalGroupBasePointHom t₂).continuous
  let σ₃ := σ₂.comp (etaleFundamentalGroupMap pr.hom (yb.map α.hom)).toMonoidHom
  have hσ₃ : Continuous (restrictScalarsRep b σ₃) :=
    hσ₂.comp (etaleFundamentalGroupMap pr.hom (yb.map α.hom)).continuous
  let σ₄ := σ₃.comp (etaleFundamentalGroupMap α.hom yb).toMonoidHom
  have hσ₄ : Continuous (restrictScalarsRep b σ₄) :=
    hσ₃.comp (etaleFundamentalGroupMap α.hom yb).continuous
  -- the two maps `π₁(Y, ȳ) → π₁(U, x̄)` are inner conjugate
  let Φ₁ := M.comp ((etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom.comp
    (φ₁.comp (etaleFundamentalGroupMap i.hom yb).toMonoidHom))
  let Φ₂ := (etaleFundamentalGroupBasePointHom t₂).toMonoidHom.comp
    ((etaleFundamentalGroupMap pr.hom (yb.map α.hom)).toMonoidHom.comp
      (etaleFundamentalGroupMap α.hom yb).toMonoidHom)
  have hΦ₁ : IsEtaleFundamentalGroupHomInducedBy
      (finiteEtaleBaseChange (((i.hom ≫ 𝟙 _) ≫ laumonFamilyPr₁ k') ≫ gU)) Φ₁ :=
    (((isEtaleFundamentalGroupHomInducedBy_map i.hom yb).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t₁)).comp_baseChange
        (isEtaleFundamentalGroupHomInducedBy_map (laumonFamilyPr₁ k') z)).comp_baseChange
          (isEtaleFundamentalGroupHomInducedBy_map gU _)
  have hΦ₂ : IsEtaleFundamentalGroupHomInducedBy
      (finiteEtaleBaseChange ((α.hom ≫ pr.hom) ≫ 𝟙 _)) Φ₂ :=
    ((isEtaleFundamentalGroupHomInducedBy_map α.hom yb).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_map pr.hom (yb.map α.hom))).comp_baseChange
        (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t₂)
  have hf : ((i.hom ≫ 𝟙 _) ≫ laumonFamilyPr₁ k') ≫ gU = (α.hom ≫ pr.hom) ≫ 𝟙 _ := by
    have h := hP1.isoPullback_hom_fst
    change α.hom ≫ pr.hom = _ at h
    rw [Category.comp_id, h, Category.comp_id]
    simp only [gU, Category.assoc]
    rfl
  obtain ⟨cc, hcc⟩ := hΦ₁.isInnerConjugate_of_eq hΦ₂ hf
  have hg : ∀ γ, σ₄ γ = (σ cc)⁻¹⁻¹ * ρK γ * (σ cc)⁻¹ := by
    intro γ
    have hχ := artinSchreierCharacter_laumonFibre_eq_one k' ψ' n₀ c z p₀ y hy i fY hY yb t₁ γ
    have h1 : ρK γ = σ (Φ₁ γ) := by
      show (σ.comp M).comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom
          (φ₁ (etaleFundamentalGroupMap i.hom yb γ)) *
        Units.map (Matrix.scalar (Fin m) : E →+* Matrix (Fin m) (Fin m) E).toMonoidHom
          (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
            (laumonKernel k' n₀ c) ψ' z p₀ (φ₁ (etaleFundamentalGroupMap i.hom yb γ))) = _
      rw [show φ₁ (etaleFundamentalGroupMap i.hom yb γ) = etaleFundamentalGroupBasePointHom t₁
        (etaleFundamentalGroupMap i.hom yb γ) from rfl, hχ, map_one, mul_one]
      rfl
    have h2 : σ₄ γ = σ (Φ₂ γ) := rfl
    rw [h2, hcc γ, map_mul, map_mul, map_inv, h1, inv_inv]
  -- the chain of `E`-linear isomorphisms
  let G0 := LAdicSheaf.CoefficientSheaf.inverseImage i
    (restrictScalarsRepCoefficientSheaf B A2 z b Lrep hLrep)
  let Fσ := restrictScalarsRepCoefficientSheaf B U ((z.map (laumonFamilyPr₁ k')).map gU) b σ hσ
  let := G0.rationalCohomologyModule fY jY kbar 1 E
  let := Fσ.rationalCohomologyModule f j kbar 1 E
  let := (restrictScalarsRepCoefficientSheaf B Y yb b
    ((Lrep.comp (etaleFundamentalGroupBasePointHom t₁).toMonoidHom).comp
      (etaleFundamentalGroupMap i.hom yb).toMonoidHom) hρK).rationalCohomologyModule fY jY kbar 1 E
  let := (restrictScalarsRepCoefficientSheaf B Y yb b
    (((σ.comp (etaleFundamentalGroupBasePointHom t₂).toMonoidHom).comp
      (etaleFundamentalGroupMap (fieldExtensionProj B U f
        ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)).hom
          (yb.map α.hom)).toMonoidHom).comp (etaleFundamentalGroupMap α.hom yb).toMonoidHom)
      hσ₄).rationalCohomologyModule fY jY kbar 1 E
  show ∃ eY : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
      G0.toLAdicSheaf 1 ≃ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar Fσ.toLAdicSheaf 1,
    ∀ v, eY (G0.rationalGeometricCompactlySupportedFrobenius fY jY kbar 1 E p (n * (m' + 1))
      hcardy v) =
      ((Fσ.rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard) ^ (m' + 1)) (eY v)
  refine exists_linearEquiv_intertwining_trans
    (exists_inverseImage_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b i yb t₁ Lrep hLrep
      hρK fY jY kbar 1 p (n * (m' + 1)) hcardy) ?_
  refine exists_linearEquiv_intertwining_trans
    (exists_restrictScalarsRepCoefficientSheaf_conjLinearEquiv B Y yb b hρK hσ₄ (σ cc)⁻¹ hg fY jY
      kbar 1 p (n * (m' + 1)) hcardy) ?_
  exact exists_fieldExtension_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b f j
    ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) kbar fY jY α hα yb t₂
    σ hσ hσ₄ 1 p n hcard m' hcardy

end Stacks.EtaleCohomology

end
