module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierFamilyFibreScheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierEquinormInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AlgebraicClosureIndependenceLAdic

/-!
# The fibres of Laumon's Fourier family over the `t`-line

This proves `Stacks.EtaleCohomology.LaumonFourierFamilyFibreInput`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): for the Fourier family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t)` on `𝔸² = Spec k'[x][t]`, its restriction to `U' = pr₂⁻¹(V')`
and the fibre `Y` of `U' → V'` over a point `v` with `κ(v) = k'` lying over `t = c`, the
`E`-linear Frobenius of `κ(v)` on `H¹_c(Y_κ̄, K|_Y ⊗ ℚ_ℓ)` has the characteristic polynomial of the
Frobenius of `k'` on `H¹_c(𝔸¹_k̄', ℱ_τ ⊗ ℚ_ℓ)`, `τ = σ ⊗ L_ψ'(a xⁿ + c x)`, for every choice of the
data of the latter (geometric point, point of the Artin–Schreier cover, compactification,
algebraic closure) (`Stacks.EtaleCohomology.laumonFourierFamilyFibreInput`).

The fibre is `Y = X' ×_{k'} κ(v)`, `X' = 𝔸¹_{k'}`
(`Stacks.EtaleCohomology.exists_laumonFourierFibre_fieldExtension`), and the isomorphism of
cohomologies is a chain of `E`-linear isomorphisms commuting with the Frobenius:

1. `i⁻¹ jU⁻¹ ℱ_{Res K}` ~ `ℱ_{Res (K ∘ t₁ ∘ jU_* ∘ i_*)}` at `ȳ`
   (`exists_inverseImage_inverseImage_restrictScalarsRepCoefficientSheaf_linearEquiv`);
2. ~ `ℱ_{Res (τ ∘ t ∘ pr_* ∘ α_*)}` at `ȳ`: the two representations of `π₁(Y, ȳ)` are conjugate,
   since `Y → U' → 𝔸² → 𝔸¹_x → U` and `Y → X' → U` agree, and the Artin–Schreier characters agree
   along the section `t = c` (`Stacks.EtaleCohomology.artinSchreierCharacter_trace_baseChange_eq`
   for the trivial extension of constants);
3. ~ `H¹_c(X'_{κ̄}, ℱ_τ ⊗ ℚ_ℓ)` over `k'`, with `κ̄` an algebraic closure of `κ(v) = k'`
   (`Stacks.EtaleCohomology.exists_fieldExtension_restrictScalarsRepCoefficientSheaf_linearEquiv`,
   `κ(v)/k'` of degree one);
4. ~ `H¹_c(X'_{k̄'}, ℱ_τ ⊗ ℚ_ℓ)`: independence of the algebraic closure
   (`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalAlgEquivLinearEquiv`).

## Main results

* `Stacks.EtaleCohomology.laumonFourierFamilyFibreInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

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

/-- **`Hⁱ_c(Y_κ̄, ℱ_{Res (σ ∘ t ∘ pr_* ∘ α_*)} ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄', ℱ_{Res σ} ⊗ ℚ_ℓ)` for
`Y ≅ X ×_k κ` with `#κ = #k`**, `E`-linearly and compatibly with the Frobenius of `κ` and of `k`,
for any algebraic closure `k̄'` of `k` isomorphic over `k` to the algebraic closure `κ̄` of `κ`:
the field extension isomorphism of degree one, then the independence of the algebraic closure. -/
public theorem exists_fieldExtension_algEquiv_restrictScalarsRepCoefficientSheaf_linearEquiv
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
    (kbar' : Type u) [Field kbar'] [Algebra k kbar'] (σ' : kbar' ≃ₐ[k] kbar)
    (i : ℤ) (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP κ p] (hcard : Fintype.card k = p ^ q)
    (hcardκ : Fintype.card κ = p ^ q) :
    letI := (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').rationalCohomologyModule fY jY kbar
      i E
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar' i E
    ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
        (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').toLAdicSheaf i ≃ₗ[E]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar'
          (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i,
      ∀ v, e ((restrictScalarsRepCoefficientSheaf B Y y b _
          hσ').rationalGeometricCompactlySupportedFrobenius fY jY kbar i E p q hcardκ v) =
        (restrictScalarsRepCoefficientSheaf B X x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar' i E p q hcard (e v) := by
  let Fα := restrictScalarsRepCoefficientSheaf B Y y b _ hσ'
  let Fσ := restrictScalarsRepCoefficientSheaf B X x b σ hσ
  let := Fα.rationalCohomologyModule fY jY kbar i E
  let := Fσ.rationalCohomologyModule f j kbar i E
  let := Fσ.rationalCohomologyModule f j kbar' i E
  have hcardκ' : Fintype.card κ = p ^ (q * (0 + 1)) := by
    rw [Nat.zero_add, Nat.mul_one]; exact hcardκ
  have hFα : ∀ (q' : ℕ) (hq : q' = q) (hc : Fintype.card κ = p ^ q'),
      Fα.rationalGeometricCompactlySupportedFrobenius fY jY kbar i E p q' hc =
        Fα.rationalGeometricCompactlySupportedFrobenius fY jY kbar i E p q hcardκ := by
    intro q' hq hc
    subst hq
    rfl
  obtain ⟨e₃, he₃⟩ := exists_fieldExtension_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b
    f j κ kbar fY jY α hα y t σ hσ hσ' i p q hcard 0 hcardκ'
  refine exists_linearEquiv_intertwining_trans
    (A₂ := Fσ.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard)
    ⟨e₃, fun w => ?_⟩
    ⟨(Fσ.rationalAlgEquivLinearEquiv B ℓ f j σ' i E),
      Fσ.rationalAlgEquivLinearEquiv_frobenius B ℓ f j σ' i p q hcard E⟩
  rw [← hFα _ (by rw [Nat.zero_add, Nat.mul_one]) hcardκ', he₃, Nat.zero_add, pow_one]

/-- **The chain of `E`-linear isomorphisms for a fibre of the Fourier family**: for a fibre
`i : Y → U'` of an open `jU : U' → A₂`, `Y ≅ X ×_k κ` with `#κ = #k`, and representations
`ρ_K = L ∘ t₁ ∘ jU_* ∘ i_*`, `τ_α = σ ∘ t ∘ pr_* ∘ α_*` of `π₁(Y, ȳ)` conjugate by `g`,
`Hⁱ_c(Y_κ̄, i⁻¹ jU⁻¹ ℱ_{Res L} ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄', ℱ_{Res σ} ⊗ ℚ_ℓ)`, `E`-linearly and compatibly
with the Frobenius of `κ` and of `k`. -/
public theorem
    exists_inverseImage_conj_fieldExtension_restrictScalarsRepCoefficientSheaf_linearEquiv
    {A₂ U' : B.Scheme} (jU : U' ⟶ A₂) [ConnectedSpace A₂.1] [ConnectedSpace U'.1]
    [IsNoetherian A₂.1] [IsNoetherian U'.1] {z : GeometricPoint A₂.1}
    (L : EtaleFundamentalGroup A₂.1 z →* GL (Fin m) E) (hL : Continuous (restrictScalarsRep b L))
    {X : B.Scheme} [ConnectedSpace X.1] [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (κ : Type u) [Field κ] [Fintype κ] [Algebra k κ]
    [Module.Finite k κ] (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra κ kbar]
    [IsScalarTower k κ kbar] [IsNoetherian (fieldExtensionScheme B X f κ).1]
    [ConnectedSpace (fieldExtensionScheme B X f κ).1]
    {Y : B.Scheme} [IsNoetherian Y.1] [ConnectedSpace Y.1] (i : Y ⟶ U') (fY : Y.1 ⟶ Spec (.of κ))
    [LocallyOfFiniteType fY] [QuasiCompact fY] [IsSeparated fY]
    (jY : CompactificationOf (Over.mk fY))
    (α : Y ⟶ fieldExtensionScheme B X f κ) [IsIso (B.inclusion.map α)]
    (hα : B.inclusion.map α ≫ pullback.snd f (specAlgebraMap k κ) = fY)
    {x : GeometricPoint X.1} (y : GeometricPoint Y.1)
    (t₁ : finiteEtaleFiberFunctor z ≅ finiteEtaleFiberFunctor ((y.map i.hom).map jU.hom))
    (hρ : Continuous (restrictScalarsRep b
      (((L.comp (etaleFundamentalGroupBasePointHom t₁).toMonoidHom).comp
        (etaleFundamentalGroupMap jU.hom (y.map i.hom)).toMonoidHom).comp
          (etaleFundamentalGroupMap i.hom y).toMonoidHom)))
    (t : finiteEtaleFiberFunctor x ≅
      finiteEtaleFiberFunctor ((y.map α.hom).map (fieldExtensionProj B X f κ).hom))
    (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))
    (hσ' : Continuous (restrictScalarsRep b
      (((σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom).comp
        (etaleFundamentalGroupMap (fieldExtensionProj B X f κ).hom (y.map α.hom)).toMonoidHom).comp
          (etaleFundamentalGroupMap α.hom y).toMonoidHom)))
    (g : GL (Fin m) E)
    (hconj : ∀ γ, σ (etaleFundamentalGroupBasePointHom t
        (etaleFundamentalGroupMap (fieldExtensionProj B X f κ).hom (y.map α.hom)
          (etaleFundamentalGroupMap α.hom y γ))) =
      g⁻¹ * L (etaleFundamentalGroupBasePointHom t₁ (etaleFundamentalGroupMap jU.hom (y.map i.hom)
        (etaleFundamentalGroupMap i.hom y γ))) * g)
    (kbar' : Type u) [Field kbar'] [Algebra k kbar'] (σ' : kbar' ≃ₐ[k] kbar)
    (n : ℤ) (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP κ p] (hcard : Fintype.card k = p ^ q)
    (hcardκ : Fintype.card κ = p ^ q) :
    letI := (LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
      (restrictScalarsRepCoefficientSheaf B A₂ z b L hL))).rationalCohomologyModule fY jY kbar n E
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar' n E
    ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
        (LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
          (restrictScalarsRepCoefficientSheaf B A₂ z b L hL))).toLAdicSheaf n ≃ₗ[E]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar'
          (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf n,
      ∀ v, e ((LAdicSheaf.CoefficientSheaf.inverseImage i
          (LAdicSheaf.CoefficientSheaf.inverseImage jU
            (restrictScalarsRepCoefficientSheaf B A₂ z b L
              hL))).rationalGeometricCompactlySupportedFrobenius fY jY kbar n E p q hcardκ v) =
        (restrictScalarsRepCoefficientSheaf B X x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar' n E p q hcard (e v) := by
  let := (LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (restrictScalarsRepCoefficientSheaf B A₂ z b L hL))).rationalCohomologyModule fY jY kbar n E
  let := (restrictScalarsRepCoefficientSheaf B Y y b _ hρ).rationalCohomologyModule fY jY kbar n E
  let := (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').rationalCohomologyModule fY jY kbar n
    E
  let := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar' n E
  refine exists_linearEquiv_intertwining_trans
    (exists_inverseImage_inverseImage_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b jU i y
      t₁ L hL hρ fY jY kbar n p q hcardκ) ?_
  refine exists_linearEquiv_intertwining_trans
    (exists_restrictScalarsRepCoefficientSheaf_conjLinearEquiv B Y y b hρ hσ' g (fun γ => hconj γ)
      fY jY kbar n p q hcardκ) ?_
  exact exists_fieldExtension_algEquiv_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b f j κ
    kbar fY jY α hα y t σ hσ hσ' kbar' σ' n p q hcard hcardκ

/-- **The characteristic polynomials of the Frobenius agree** along the chain of
`exists_inverseImage_conj_fieldExtension_restrictScalarsRepCoefficientSheaf_linearEquiv`. -/
public theorem
    charpoly_inverseImage_conj_fieldExtension_rationalGeometricCompactlySupportedFrobenius_eq
    {A₂ U' : B.Scheme} (jU : U' ⟶ A₂) [ConnectedSpace A₂.1] [ConnectedSpace U'.1]
    [IsNoetherian A₂.1] [IsNoetherian U'.1] {z : GeometricPoint A₂.1}
    (L : EtaleFundamentalGroup A₂.1 z →* GL (Fin m) E) (hL : Continuous (restrictScalarsRep b L))
    {F₀ : _} (hF₀ : F₀ = restrictScalarsRepCoefficientSheaf B A₂ z b L hL)
    {X : B.Scheme} [ConnectedSpace X.1] [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (κ : Type u) [Field κ] [Fintype κ] [Algebra k κ]
    [Module.Finite k κ] (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra κ kbar]
    [IsScalarTower k κ kbar] [IsNoetherian (fieldExtensionScheme B X f κ).1]
    [ConnectedSpace (fieldExtensionScheme B X f κ).1]
    {Y : B.Scheme} [IsNoetherian Y.1] [ConnectedSpace Y.1] (i : Y ⟶ U') (fY : Y.1 ⟶ Spec (.of κ))
    [LocallyOfFiniteType fY] [QuasiCompact fY] [IsSeparated fY]
    (jY : CompactificationOf (Over.mk fY))
    (α : Y ⟶ fieldExtensionScheme B X f κ) [IsIso (B.inclusion.map α)]
    (hα : B.inclusion.map α ≫ pullback.snd f (specAlgebraMap k κ) = fY)
    {x : GeometricPoint X.1} (y : GeometricPoint Y.1)
    (t₁ : finiteEtaleFiberFunctor z ≅ finiteEtaleFiberFunctor ((y.map i.hom).map jU.hom))
    (hρ : Continuous (restrictScalarsRep b
      (((L.comp (etaleFundamentalGroupBasePointHom t₁).toMonoidHom).comp
        (etaleFundamentalGroupMap jU.hom (y.map i.hom)).toMonoidHom).comp
          (etaleFundamentalGroupMap i.hom y).toMonoidHom)))
    (t : finiteEtaleFiberFunctor x ≅
      finiteEtaleFiberFunctor ((y.map α.hom).map (fieldExtensionProj B X f κ).hom))
    (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))
    (hσ' : Continuous (restrictScalarsRep b
      (((σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom).comp
        (etaleFundamentalGroupMap (fieldExtensionProj B X f κ).hom (y.map α.hom)).toMonoidHom).comp
          (etaleFundamentalGroupMap α.hom y).toMonoidHom)))
    (g : GL (Fin m) E)
    (hconj : ∀ γ, σ (etaleFundamentalGroupBasePointHom t
        (etaleFundamentalGroupMap (fieldExtensionProj B X f κ).hom (y.map α.hom)
          (etaleFundamentalGroupMap α.hom y γ))) =
      g⁻¹ * L (etaleFundamentalGroupBasePointHom t₁ (etaleFundamentalGroupMap jU.hom (y.map i.hom)
        (etaleFundamentalGroupMap i.hom y γ))) * g)
    (kbar' : Type u) [Field kbar'] [Algebra k kbar'] (σ' : kbar' ≃ₐ[k] kbar)
    (n : ℤ) (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP κ p] (hcard : Fintype.card k = p ^ q)
    (hcardκ : Fintype.card κ = p ^ q) :
    letI := (LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
      F₀)).rationalCohomologyModule fY jY kbar n E
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar' n E
    ∀ (_ : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY
        kbar (LAdicSheaf.CoefficientSheaf.inverseImage i
          (LAdicSheaf.CoefficientSheaf.inverseImage jU F₀)).toLAdicSheaf n))
      (_ : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar'
        (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf n)),
    ((LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
        F₀)).rationalGeometricCompactlySupportedFrobenius
          fY jY kbar n E p q hcardκ).charpoly =
      ((restrictScalarsRepCoefficientSheaf B X x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar' n E p q hcard).charpoly := by
  subst hF₀
  let := (LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (restrictScalarsRepCoefficientSheaf B A₂ z b L hL))).rationalCohomologyModule fY jY kbar n E
  let := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar' n E
  intro _ _
  obtain ⟨e, he⟩ :=
    exists_inverseImage_conj_fieldExtension_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b jU
      L hL f j κ kbar i fY jY α hα y t₁ hρ t σ hσ hσ' g hconj kbar' σ' n p q hcard hcardκ
  rw [← e.charpoly_conj]
  congr 1
  refine LinearMap.ext fun w => ?_
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, he, LinearEquiv.apply_symm_apply]

end Chains


section Conj

variable {U : Scheme.{u}} [ConnectedSpace U] {E : Type} [Field E] {m : ℕ} {k' : Type u} [Field k']
  [Fintype k'] (ψ' : AddChar k' E) (n : ℕ) (a c : k') (gU : Spec (.of (Polynomial k')) ⟶ U)

/-- **The representations of `π₁(Y, ȳ)` of the Fourier family and of the fibre over `t = c` are
conjugate**: for `f₁ : Y → 𝔸²` factoring as `Spec(φ_c) ∘ f₂` through `f₂ : Y → 𝔸¹_x`, the
pullbacks along `f₁` of `σ ∘ g_U* ∘ pr₁* ⊗ L_ψ'(a xⁿ + x t)` and along `f₂` of
`σ ∘ g_U* ⊗ L_ψ'(a xⁿ + c x)` are conjugate: the maps to `π₁(U)` come from the same morphism
`Y → U` and the Artin–Schreier characters agree along the section `t = c`. -/
public theorem exists_conj_laumonFourierFamilyRep {Y : Scheme.{u}} [ConnectedSpace Y]
    {yb : GeometricPoint Y} (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (σ : EtaleFundamentalGroup U ((z.map (laumonFamilyPr₁ k')).map gU) →* GL (Fin m) E)
    (pz : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    (x' : GeometricPoint (Spec (.of (Polynomial k'))))
    (hx' : x'.map gU = (z.map (laumonFamilyPr₁ k')).map gU)
    (p₀ : (finiteEtaleFiberFunctor x').obj
      (Stacks.ArtinSchreier.cover k' (Polynomial k')
        (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)))
    (f₁ : Y ⟶ Spec (.of (Polynomial (Polynomial k')))) (f₂ : Y ⟶ Spec (.of (Polynomial k')))
    (hfc : f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom (laumonFourierEvalAlgHom c).toRingHom))
    {Φ₁ : EtaleFundamentalGroup Y yb →*
      EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z}
    {Φ₂ : EtaleFundamentalGroup Y yb →* EtaleFundamentalGroup (Spec (.of (Polynomial k'))) x'}
    (hΦ₁ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f₁) Φ₁)
    (hΦ₂ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f₂) Φ₂) :
    ∃ g : GL (Fin m) E, ∀ γ,
      characterTwist (σ.comp (hx' ▸ (etaleFundamentalGroupMap gU x').toMonoidHom))
          (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
            (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X) ψ' x' p₀)
          (Φ₂ γ) =
        g⁻¹ * laumonFourierFamilyRep k' ψ' n a z pz
          (σ.comp (etaleFundamentalGroupMap gU (z.map (laumonFamilyPr₁ k'))).toMonoidHom)
            (Φ₁ γ) * g := by
  have hCφ : Spec.map (CommRingCat.ofHom (laumonFourierEvalAlgHom c).toRingHom) ≫
      laumonFamilyPr₁ k' = 𝟙 _ := by
    have h1 : CommRingCat.ofHom ((laumonFourierEvalAlgHom c).toRingHom.comp
        (Polynomial.C : Polynomial k' →+* Polynomial (Polynomial k'))) =
        𝟙 (CommRingCat.of (Polynomial k')) :=
      CommRingCat.hom_ext (RingHom.ext fun q => laumonFourierEvalAlgHom_C c q)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h1, Spec.map_id]
  have hf : f₁ ≫ (laumonFamilyPr₁ k' ≫ gU) = f₂ ≫ gU := by
    rw [hfc, Category.assoc, reassoc_of% hCφ]
  have hχ := artinSchreierCharacter_trace_baseChange_eq k' k' ψ' ψ'
    (fun w => by rw [Algebra.trace_self_apply]) (laumonFourierKernel k' n a)
    (laumonFourierEvalAlgHom c) _ (laumonFourierEvalAlgHom_laumonFourierKernel n a c) z pz x' p₀
    f₁ f₂ hfc hΦ₁ hΦ₂
  obtain ⟨g, hg⟩ := exists_conj_of_isEtaleFundamentalGroupHomInducedBy σ hf hΦ₁
    ((isEtaleFundamentalGroupHomInducedBy_map (laumonFamilyPr₁ k') z).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_map gU (z.map (laumonFamilyPr₁ k')))) hΦ₂
    (isEtaleFundamentalGroupHomInducedBy_map_cast gU x' hx') _ _ hχ
    ((laumonFourierFamilyRep k' ψ' n a z pz
      (σ.comp (etaleFundamentalGroupMap gU (z.map (laumonFamilyPr₁ k'))).toMonoidHom)).comp Φ₁)
    ((characterTwist (σ.comp (hx' ▸ (etaleFundamentalGroupMap gU x').toMonoidHom))
      (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
        (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X) ψ' x' p₀)).comp Φ₂)
    (fun _ => rfl) (fun _ => rfl)
  exact ⟨g, fun γ => hg γ⟩

end Conj

/-- An open of `𝔸² = Spec k'[x][t]` with a point is connected: `𝔸²` is irreducible. -/
public theorem connectedSpace_of_isOpenImmersion_laumonPlane {k' : Type u} [Field k']
    {B : BigEtaleSite.{u}} {hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k'))))}
    {U' : B.Scheme} (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
    [IsOpenImmersion (B.inclusion.map jU)] [Nonempty U'.1] : ConnectedSpace U'.1 := by
  have hA2i : IrreducibleSpace
      (B.inclusion.obj (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)) :=
    PrimeSpectrum.irreducibleSpace (R := Polynomial (Polynomial k'))
  have hU'ne : Nonempty (B.inclusion.obj U') := ‹Nonempty U'.1›
  have hU'i : IrreducibleSpace (B.inclusion.obj U') :=
    (B.inclusion.map jU).isOpenEmbedding.irreducibleSpace
  exact connectedSpace_iff_univ.mpr
    (@IrreducibleSpace.isIrreducible_univ (B.inclusion.obj U') _ hU'i).isConnected

/-- Continuity of `Res_b` of a representation precomposed with three continuous homomorphisms. -/
private theorem continuous_restrictScalarsRep_comp_comp_comp {F E : Type*} [Field F] [Field E]
    [Algebra F E] [TopologicalSpace F] {d m : ℕ} (b : Module.Basis (Fin d) F E)
    {G₀ G₁ G₂ G₃ : Type*} [Monoid G₀] [Monoid G₁] [Monoid G₂] [Monoid G₃]
    [TopologicalSpace G₀] [TopologicalSpace G₁] [TopologicalSpace G₂] [TopologicalSpace G₃]
    {ρ : G₀ →* GL (Fin m) E} (hρ : Continuous (restrictScalarsRep b ρ)) (f₁ : G₁ →ₜ* G₀)
    (f₂ : G₂ →ₜ* G₁) (f₃ : G₃ →ₜ* G₂) :
    Continuous (restrictScalarsRep b
      (((ρ.comp f₁.toMonoidHom).comp f₂.toMonoidHom).comp f₃.toMonoidHom)) :=
  ((hρ.comp f₁.continuous).comp f₂.continuous).comp f₃.continuous

/-- The composite `π₁(Y, ȳ) → π₁(U) → π₁(A, z̄)` of `i_*`, `j_*` and a change of base point is
induced by the base change along `(i ≫ j) ≫ 𝟙`. -/
private theorem isEtaleFundamentalGroupHomInducedBy_basePointHom_comp_map_comp_map
    {Y U A : Scheme.{u}} [ConnectedSpace Y] [ConnectedSpace U] [ConnectedSpace A]
    (i : Y ⟶ U) (j : U ⟶ A) (yb : GeometricPoint Y) {z : GeometricPoint A}
    (t : finiteEtaleFiberFunctor z ≅ finiteEtaleFiberFunctor ((yb.map i).map j)) :
    IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange ((i ≫ j) ≫ 𝟙 _))
      (((etaleFundamentalGroupBasePointHom t).toMonoidHom.comp
        (etaleFundamentalGroupMap j (yb.map i)).toMonoidHom).comp
          (etaleFundamentalGroupMap i yb).toMonoidHom) :=
  ((isEtaleFundamentalGroupHomInducedBy_map i yb).comp_baseChange
    (isEtaleFundamentalGroupHomInducedBy_map j (yb.map i))).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t)

/-- **The fibres of the Fourier family at fixed `a`, for all choices**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the `E`-linear Frobenius of `κ(v) = k'`
on `H¹_c(Y_κ̄, K|_Y ⊗ ℚ_ℓ)` has the characteristic polynomial of the Frobenius of `k'` on
`H¹_c(𝔸¹_k̄', ℱ_σ ⊗ L_ψ'(a xⁿ + c x) ⊗ ℚ_ℓ)`. -/
public theorem laumonFourierFamilyFibreInput : LaumonFourierFamilyFibreInput.{u} := by
  intro B U ℓ _ _ _ _ k _ _ e _ x E _ _ d b m σ ψ n k' _ _ _ a hS hL z hz pz hσ₁ V' U' _ _
    jV' jU g' hjV' hU v _ Y _ i fY _ _ _ hY jY kbarv _ _ _ pv nv _ _ hcardv hfin c hι hXc hX' _ _
    x' hx' p₀ hτ _ _ _ j' kbar' _ _ _ p n' _ _ hcard' hV
  have hW : ∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) := fun n T =>
    AlgebraicGeometry.hasWeakSheafify_smallEtale_of_scheme B _ T
  subst hz
  -- the fields: `κ(v) = k'`, `p = pv`, `n' = nv`
  let iκ' : Algebra k' (V'.1.residueField v) :=
    ((laumonPointRingHom jV' v).comp Polynomial.C).toAlgebra
  have : Module.Finite k' (V'.1.residueField v) := Module.Finite.of_finite
  have hcp : CharP (V'.1.residueField v) p :=
    charP_of_injective_ringHom (algebraMap k' (V'.1.residueField v)).injective p
  obtain rfl : p = pv := CharP.eq (V'.1.residueField v) hcp ‹_›
  have hκcard : Fintype.card (V'.1.residueField v) = Fintype.card k' :=
    (Fintype.card_of_bijective hι).symm
  obtain rfl : n' = nv := Nat.pow_right_injective (Fact.out : p.Prime).two_le
    ((hκcard.trans hcard').symm.trans hcardv)
  let ikv : Algebra k' kbarv := ((algebraMap (V'.1.residueField v) kbarv).comp
    (algebraMap k' (V'.1.residueField v))).toAlgebra
  have : IsScalarTower k' (V'.1.residueField v) kbarv :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsAlgebraic k' (V'.1.residueField v) := Algebra.IsAlgebraic.of_finite k' _
  have : Algebra.IsAlgebraic k' kbarv := Algebra.IsAlgebraic.trans k' (V'.1.residueField v) kbarv
  have : IsAlgClosure k' kbarv := ⟨IsAlgClosure.isAlgClosed (V'.1.residueField v), inferInstance⟩
  -- the fibre `Y = X' ×_{k'} κ(v)`
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  let X' := Stacks.ArtinSchreier.specObject (Polynomial k') B hX'
  let f' := Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))
  have hX'n : IsNoetherian X'.1 := inferInstanceAs (IsNoetherian (Spec (.of (Polynomial k'))))
  have hX'c : ConnectedSpace X'.1 := inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial k'))))
  have hf'1 : LocallyOfFiniteType f' := ‹LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap k' (Polynomial k'))))›
  have hf'2 : QuasiCompact f' := ‹QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap k' (Polynomial k'))))›
  have hf'3 : IsSeparated f' := ‹IsSeparated (Spec.map (CommRingCat.ofHom
    (algebraMap k' (Polynomial k'))))›
  obtain ⟨α, hαi, hYc, hα, hiα⟩ :=
    exists_laumonFourierFibre_fieldExtension jV' v jU g' c hXc hX' hU i fY hY
  have := hαi
  have := hYc
  have hα' : B.inclusion.map α ≫ pullback.snd f' (specAlgebraMap k' (V'.1.residueField v)) = fY :=
    hα
  have : IsNoetherian (fieldExtensionScheme B X' f' (V'.1.residueField v)).1 :=
    isNoetherian_fieldExtensionScheme B X' f' (V'.1.residueField v)
  have : ConnectedSpace (fieldExtensionScheme B X' f' (V'.1.residueField v)).1 :=
    @Function.Surjective.connectedSpace _ _ _ hYc _ _
      (Scheme.homeoOfIso (asIso (B.inclusion.map α))).surjective
      (Scheme.homeoOfIso (asIso (B.inclusion.map α))).continuous
  have : Nonempty Y.1 := hYc.toNonempty
  have : IsOpenImmersion (B.inclusion.map jU) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hU.flip hjV'
  have : Nonempty U'.1 := ⟨B.inclusion.map i (Classical.arbitrary Y.1)⟩
  have hU'c : ConnectedSpace U'.1 := connectedSpace_of_isOpenImmersion_laumonPlane jU
  let yb : GeometricPoint Y.1 := GeometricPoint.ofPoint Y.1 (Classical.arbitrary Y.1)
  -- the family representation
  let gU := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e
  let M := (etaleFundamentalGroupMap gU (z.map (laumonFamilyPr₁ k'))).toMonoidHom
  let ψ' := ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom
  let A2 := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS
  have hA2n : IsNoetherian A2.1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  have hA2c : ConnectedSpace A2.1 :=
    inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial (Polynomial k')))))
  have hσ₁' : Continuous (restrictScalarsRep b (σ.comp M)) := hσ₁
  let Lrep := laumonFourierFamilyRep k' ψ' n a z pz (σ.comp M)
  have hLrep : Continuous (restrictScalarsRep b Lrep) :=
    continuous_restrictScalarsRep_laumonFourierFamilyRep k' b ψ' n a z pz (σ.comp M) hσ₁'
  obtain ⟨t₁⟩ := nonempty_finiteEtaleFiberFunctorIso A2.1 z ((yb.map i.hom).map jU.hom)
  let ρK := ((Lrep.comp (etaleFundamentalGroupBasePointHom t₁).toMonoidHom).comp
    (etaleFundamentalGroupMap jU.hom (yb.map i.hom)).toMonoidHom).comp
      (etaleFundamentalGroupMap i.hom yb).toMonoidHom
  have hρK : Continuous (restrictScalarsRep b ρK) :=
    continuous_restrictScalarsRep_comp_comp_comp b hLrep _ _ _
  -- the reference representation `τ` on `X'`, read on `Y` through `α` and `pr`
  let g' : Polynomial k' := Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X
  let τ := characterTwist (σ.comp (hx' ▸ (etaleFundamentalGroupMap gU x').toMonoidHom))
    (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k') g' ψ' x' p₀)
  let pr := fieldExtensionProj B X' f' (V'.1.residueField v)
  obtain ⟨t₃⟩ := nonempty_finiteEtaleFiberFunctorIso X'.1 x' ((yb.map α.hom).map pr.hom)
  let τα := ((τ.comp (etaleFundamentalGroupBasePointHom t₃).toMonoidHom).comp
    (etaleFundamentalGroupMap pr.hom (yb.map α.hom)).toMonoidHom).comp
      (etaleFundamentalGroupMap α.hom yb).toMonoidHom
  have hτα : Continuous (restrictScalarsRep b τα) :=
    continuous_restrictScalarsRep_comp_comp_comp b hτ _ _ _
  -- the two representations of `π₁(Y, ȳ)` are conjugate
  let Φ₁' := ((etaleFundamentalGroupBasePointHom t₁).toMonoidHom.comp
    (etaleFundamentalGroupMap jU.hom (yb.map i.hom)).toMonoidHom).comp
      (etaleFundamentalGroupMap i.hom yb).toMonoidHom
  have hΦ₁' := isEtaleFundamentalGroupHomInducedBy_basePointHom_comp_map_comp_map i.hom jU.hom yb t₁
  let Φ₂ := ((etaleFundamentalGroupBasePointHom t₃).toMonoidHom.comp
    (etaleFundamentalGroupMap pr.hom (yb.map α.hom)).toMonoidHom).comp
      (etaleFundamentalGroupMap α.hom yb).toMonoidHom
  have hΦ₂ := isEtaleFundamentalGroupHomInducedBy_basePointHom_comp_map_comp_map α.hom pr.hom yb t₃
  obtain ⟨gc, hconj⟩ := exists_conj_laumonFourierFamilyRep ψ' n a c gU z σ pz x' hx' p₀
    ((i.hom ≫ jU.hom) ≫ 𝟙 _) ((α.hom ≫ pr.hom) ≫ 𝟙 _)
    (by rw [Category.comp_id, Category.comp_id]; exact hiα) hΦ₁' hΦ₂
  -- the chain of `E`-linear isomorphisms
  have hK : laumonFourierFamilySheaf k' B hS b ψ' n a z pz _ hσ₁ =
      restrictScalarsRepCoefficientSheaf B A2 z b Lrep hLrep := rfl
  let G0 := LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (restrictScalarsRepCoefficientSheaf B A2 z b Lrep hLrep))
  let Fτ := restrictScalarsRepCoefficientSheaf B X' x' b τ hτ
  let := G0.rationalCohomologyModule fY jY kbarv 1 E
  let := Fτ.rationalCohomologyModule f' j' kbar' 1 E
  have hfin' : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      B Y ℓ fY jY kbarv G0.toLAdicSheaf 1) := hfin
  have := G0.rationalCohomologyModule_isScalarTower fY jY kbarv 1 E
    (algebraMap_conjIntegralSubring_algebraMap _ _)
  have hYfin : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY
      kbarv G0.toLAdicSheaf 1) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  have := Fτ.rationalCohomologyModule_isScalarTower f' j' kbar' 1 E
    (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ
      f' j' kbar' Fτ.toLAdicSheaf 1) := hV
  have hXfin : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ f'
      j' kbar' Fτ.toLAdicSheaf 1) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  exact charpoly_inverseImage_conj_fieldExtension_rationalGeometricCompactlySupportedFrobenius_eq
    (X := X') (k := k') (Y := Y) B ℓ b jU Lrep hLrep hK f' j' (V'.1.residueField v) kbarv i fY jY
    α hα' yb t₁ hρK t₃ τ hτ hτα gc hconj kbar' (IsAlgClosure.equiv k' kbar' kbarv) 1 p n' hcard'
    hcardv hYfin hXfin

end Stacks.EtaleCohomology

end
