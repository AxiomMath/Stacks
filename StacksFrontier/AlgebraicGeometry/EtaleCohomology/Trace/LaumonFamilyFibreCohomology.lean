module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyFibreScheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyFibreCharacter
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonOriginFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSchemeIsoTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineLineProjectiveCompactification

/-!
# The fibres of Laumon's family over the `t`-line

This proves `Stacks.EtaleCohomology.LaumonFamilyFibreLinearInput` (input (c) of
`Stacks.EtaleCohomology.laumonFamily_isPure_restrictScalarsRep`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): for the family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t (xⁿ⁰ + c x))` on `𝔸² = Spec k'[x][t]`, its restriction to
`U' = pr₂⁻¹(V')` and a fibre `Y` of `U' → V'` over a point `v`, the `E`-linear Frobenius of
`κ(v)` on `H¹_c(Y_κ̄, K|_Y ⊗ ℚ_ℓ)` has the characteristic polynomial of the one on
`H¹_c(𝔸¹_κ̄, ℱ_τ ⊗ ℚ_ℓ)`, `τ = σ ⊗ L_{ψ ∘ Tr_{κ(v)/k}}(s xⁿ⁰ + (c s) x)`, `s = t(v)`
(`Stacks.EtaleCohomology.laumonFamilyFibreLinearInput`).

Identify `Y` with `𝔸¹_{κ(v)}` by `β` (`Stacks.EtaleCohomology.exists_laumonFamilyFibre_iso`). The
isomorphism of cohomologies is a chain of `E`-linear isomorphisms commuting with the Frobenius of
`κ(v)`:

1. `i⁻¹ jU⁻¹ ℱ_{Res K}` ~ `ℱ_{Res (K ∘ t₁ ∘ jU_* ∘ i_*)}` at `ȳ`: changes of base point and
   inverse images
   (`exists_inverseImage_inverseImage_restrictScalarsRepCoefficientSheaf_linearEquiv`);
2. ~ `ℱ_{Res (τ ∘ t₃ ∘ β_*)}` at `ȳ`: the two representations of `π₁(Y, ȳ)` are conjugate, since
   the maps to `π₁(U)` come from the same morphism `Y → U`
   (`AlgebraicGeometry.IsEtaleFundamentalGroupHomInducedBy.isInnerConjugate_of_eq`) and the
   Artin–Schreier characters agree by the trace compatibility
   (`Stacks.EtaleCohomology.artinSchreierCharacter_trace_baseChange_eq`);
3. ~ `H¹_c(𝔸¹_κ̄, ℱ_τ ⊗ ℚ_ℓ)`: inverse image along `β`, and the transport of `H_c` along the
   isomorphism `β`
   (`Stacks.EtaleCohomology.exists_isIso_restrictScalarsRepCoefficientSheaf_linearEquiv`).

## Main results

* `exists_inverseImage_inverseImage_restrictScalarsRepCoefficientSheaf_linearEquiv`.
* `Stacks.EtaleCohomology.exists_isIso_restrictScalarsRepCoefficientSheaf_linearEquiv`.
* `Stacks.EtaleCohomology.laumonFamilyFibreLinearInput`.
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

/-- **The inverse image of `ℱ_{Res_b σ}` along `Y → X₁ → X` is `ℱ_{Res_b (σ ∘ φ_t ∘ g₂_* ∘ g₁_*)}`,
`E`-linearly on `Hⁱ_c` and compatibly with the Frobenius**, for a change of base point
`t : F_x̄ ≅ F_{g₂(g₁(ȳ))}` on `X`: the change of base point and the inverse image along `g₂`, both
pulled back along `g₁`, then the inverse image along `g₁`. -/
public theorem exists_inverseImage_inverseImage_restrictScalarsRepCoefficientSheaf_linearEquiv
    {X X₁ Y : B.Scheme} (g₂ : X₁ ⟶ X) (g₁ : Y ⟶ X₁) [ConnectedSpace X.1] [ConnectedSpace X₁.1]
    [ConnectedSpace Y.1] [IsNoetherian X.1] [IsNoetherian X₁.1] [IsNoetherian Y.1]
    {x : GeometricPoint X.1} (y : GeometricPoint Y.1)
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor ((y.map g₁.hom).map g₂.hom))
    (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))
    (hσ' : Continuous (restrictScalarsRep b
      (((σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom).comp
        (etaleFundamentalGroupMap g₂.hom (y.map g₁.hom)).toMonoidHom).comp
          (etaleFundamentalGroupMap g₁.hom y).toMonoidHom)))
    {κ : Type u} [Field κ] [Fintype κ] (fY : Y.1 ⟶ Spec (.of κ)) [LocallyOfFiniteType fY]
    [QuasiCompact fY] [IsSeparated fY] (jY : CompactificationOf (Over.mk fY)) (kbar : Type u)
    [Field kbar] [Algebra κ kbar] (i : ℤ) (p q : ℕ) [Fact p.Prime] [CharP κ p]
    (hcard : Fintype.card κ = p ^ q) :
    letI := (LAdicSheaf.CoefficientSheaf.inverseImage g₁
      (LAdicSheaf.CoefficientSheaf.inverseImage g₂
        (restrictScalarsRepCoefficientSheaf B X x b σ hσ))).rationalCohomologyModule fY jY kbar
      i E
    letI := (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').rationalCohomologyModule fY jY kbar
      i E
    ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
        (LAdicSheaf.CoefficientSheaf.inverseImage g₁ (LAdicSheaf.CoefficientSheaf.inverseImage g₂
          (restrictScalarsRepCoefficientSheaf B X x b σ hσ))).toLAdicSheaf i ≃ₗ[E]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
          (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').toLAdicSheaf i,
      ∀ v, e ((LAdicSheaf.CoefficientSheaf.inverseImage g₁
          (LAdicSheaf.CoefficientSheaf.inverseImage g₂
          (restrictScalarsRepCoefficientSheaf B X x b σ
            hσ))).rationalGeometricCompactlySupportedFrobenius fY jY kbar i E p q hcard v) =
        (restrictScalarsRepCoefficientSheaf B Y y b _
          hσ').rationalGeometricCompactlySupportedFrobenius fY jY kbar i E p q hcard (e v) := by
  let σ₂ := σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom
  have hσ₂ : Continuous (restrictScalarsRep b σ₂) :=
    hσ.comp (etaleFundamentalGroupBasePointHom t).continuous
  let σ₃ := σ₂.comp (etaleFundamentalGroupMap g₂.hom (y.map g₁.hom)).toMonoidHom
  have hσ₃ : Continuous (restrictScalarsRep b σ₃) :=
    hσ₂.comp (etaleFundamentalGroupMap g₂.hom (y.map g₁.hom)).continuous
  let F := restrictScalarsRepCoefficientSheaf B X x b σ hσ
  let F' := restrictScalarsRepCoefficientSheaf B X ((y.map g₁.hom).map g₂.hom) b σ₂ hσ₂
  let F₃ := restrictScalarsRepCoefficientSheaf B X₁ (y.map g₁.hom) b σ₃ hσ₃
  let G0 := LAdicSheaf.CoefficientSheaf.inverseImage g₁
    (LAdicSheaf.CoefficientSheaf.inverseImage g₂ F)
  let G1 := LAdicSheaf.CoefficientSheaf.inverseImage g₁
    (LAdicSheaf.CoefficientSheaf.inverseImage g₂ F')
  let G2 := LAdicSheaf.CoefficientSheaf.inverseImage g₁ F₃
  let G3 := restrictScalarsRepCoefficientSheaf B Y y b _ hσ'
  let := G0.rationalCohomologyModule fY jY kbar i E
  let := G1.rationalCohomologyModule fY jY kbar i E
  let := G2.rationalCohomologyModule fY jY kbar i E
  let := G3.rationalCohomologyModule fY jY kbar i E
  -- the change of base point on `X`, pulled back along `g₂` and `g₁`
  obtain ⟨φa, ψa, Na, ha₁, ha₂, hac⟩ :=
    exists_basePoint_restrictScalarsRepCoefficientSheaf_isogeny B X t b σ hσ hσ₂
  obtain ⟨φa', ψa', ha₁', ha₂', hac'⟩ := LAdicSheaf.CoefficientSheaf.exists_inverseImage_isogeny
    g₂ F F' (fun o o' => algebraMap _ E o = algebraMap _ E o') φa ψa Na ha₁ ha₂ hac
  obtain ⟨φa'', ψa'', ha₁'', ha₂'', hac''⟩ :=
    LAdicSheaf.CoefficientSheaf.exists_inverseImage_isogeny
      g₁ (LAdicSheaf.CoefficientSheaf.inverseImage g₂ F)
      (LAdicSheaf.CoefficientSheaf.inverseImage g₂ F')
      (fun o o' => algebraMap _ E o = algebraMap _ E o') φa' ψa' Na ha₁' ha₂' hac'
  refine exists_linearEquiv_intertwining_trans
    ⟨LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv G0 G1 fY jY kbar i E φa'' ψa'' Na
      ha₁'' ha₂'' hac'', LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius G0 G1 fY
      jY kbar i E φa'' ψa'' Na ha₁'' ha₂'' hac'' p q hcard⟩ ?_
  -- the inverse image along `g₂`, pulled back along `g₁`
  obtain ⟨φb, ψb, Nb, hb₁, hb₂, hbc⟩ :=
    exists_inverseImage_restrictScalarsRepCoefficientSheaf_isogeny B g₂ (y.map g₁.hom) b σ₂ hσ₂
      hσ₃
  obtain ⟨φb', ψb', hb₁', hb₂', hbc'⟩ := LAdicSheaf.CoefficientSheaf.exists_inverseImage_isogeny g₁
    (LAdicSheaf.CoefficientSheaf.inverseImage g₂ F') F₃
    (fun o o' => algebraMap _ E o = algebraMap _ E o') φb ψb Nb hb₁ hb₂ hbc
  refine exists_linearEquiv_intertwining_trans
    ⟨LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv G1 G2 fY jY kbar i E φb' ψb' Nb hb₁'
      hb₂' hbc', LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius G1 G2 fY jY kbar
      i E φb' ψb' Nb hb₁' hb₂' hbc' p q hcard⟩ ?_
  -- the inverse image along `g₁`
  obtain ⟨φc, ψc, Nc, hc₁, hc₂, hcc⟩ :=
    exists_inverseImage_restrictScalarsRepCoefficientSheaf_isogeny B g₁ y b σ₃ hσ₃ hσ'
  exact ⟨LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv G2 G3 fY jY kbar i E φc ψc Nc hc₁
    hc₂ hcc, LAdicSheaf.CoefficientSheaf.rationalIsogenyLinearEquiv_frobenius G2 G3 fY jY kbar i E
    φc ψc Nc hc₁ hc₂ hcc p q hcard⟩

/-- **`Hⁱ_c(Y_k̄, ℱ_{Res_b (σ ∘ φ_t ∘ g_*)} ⊗ ℚ_ℓ) ≃ Hⁱ_c(X_k̄, ℱ_{Res_b σ} ⊗ ℚ_ℓ)`, `E`-linearly
and compatibly with the Frobenius, for an isomorphism `g : Y ⟶ X` with `f_Y = f ∘ g`**, any
compactifications: the inverse image along `g`, then the transport of `H_c` along `g`. -/
public theorem exists_isIso_restrictScalarsRepCoefficientSheaf_linearEquiv {X Y : B.Scheme}
    (g : Y ⟶ X) [IsIso (B.inclusion.map g)] [ConnectedSpace X.1] [ConnectedSpace Y.1]
    [IsNoetherian X.1] [IsNoetherian Y.1] {x : GeometricPoint X.1} (y : GeometricPoint Y.1)
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor (y.map g.hom))
    (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))
    (hσ' : Continuous (restrictScalarsRep b
      ((σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom).comp
        (etaleFundamentalGroupMap g.hom y).toMonoidHom)))
    {κ : Type u} [Field κ] [Fintype κ] (f : X.1 ⟶ Spec (.of κ)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (fY : Y.1 ⟶ Spec (.of κ)) [LocallyOfFiniteType fY] [QuasiCompact fY] [IsSeparated fY]
    (jY : CompactificationOf (Over.mk fY)) (hfY : fY = B.inclusion.map g ≫ f) (kbar : Type u)
    [Field kbar] [Algebra κ kbar] (i : ℤ) (p q : ℕ) [Fact p.Prime] [CharP κ p]
    (hcard : Fintype.card κ = p ^ q) :
    letI := (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').rationalCohomologyModule fY jY kbar
      i E
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar i E
    ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
        (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').toLAdicSheaf i ≃ₗ[E]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
          (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf i,
      ∀ v, e ((restrictScalarsRepCoefficientSheaf B Y y b _
          hσ').rationalGeometricCompactlySupportedFrobenius fY jY kbar i E p q hcard v) =
        (restrictScalarsRepCoefficientSheaf B X x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard (e v) := by
  let F := restrictScalarsRepCoefficientSheaf B X x b σ hσ
  let G := LAdicSheaf.CoefficientSheaf.inverseImage g F
  let := (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').rationalCohomologyModule fY jY kbar
    i E
  let := G.rationalCohomologyModule fY jY kbar i E
  let := G.rationalCohomologyModule (B.inclusion.map g ≫ f) (j.restrictOpen (B.inclusion.map g))
    kbar i E
  let := F.rationalCohomologyModule f j kbar i E
  refine exists_linearEquiv_intertwining_trans (exists_linearEquiv_intertwining_symm
    (exists_inverseImage_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b g y t σ hσ hσ' fY jY
      kbar i p q hcard)) ?_
  refine exists_linearEquiv_intertwining_trans
    (LAdicSheaf.CoefficientSheaf.exists_rationalLinearEquiv_of_structureMap_eq B ℓ fY
      (B.inclusion.map g ≫ f) hfY jY (j.restrictOpen (B.inclusion.map g)) kbar G i E p q hcard) ?_
  exact ⟨F.rationalIsoOfIsIsoLinearEquiv B ℓ g f j kbar i E,
    F.rationalIsoOfIsIsoLinearEquiv_frobenius B ℓ g f j kbar i p q hcard E⟩

end Chains

/-- `φ_v` as a homomorphism of `k'`-algebras, for the `k'`-algebra structure of `κ(v)` through
`k' → k'[t] → κ(v)`. -/
public def laumonFibreAlgHom {k' : Type u} [Field k'] {B : BigEtaleSite.{u}}
    {hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))} {V' : B.Scheme}
    (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL) (v : V'.1) :
    letI := ((laumonPointRingHom jV' v).comp Polynomial.C).toAlgebra
    Polynomial (Polynomial k') →ₐ[k'] Polynomial (V'.1.residueField v) :=
  let := ((laumonPointRingHom jV' v).comp Polynomial.C).toAlgebra
  { laumonFibreRingHom jV' v with
    commutes' := fun a => by
      change laumonFibreRingHom jV' v (Polynomial.C (Polynomial.C a)) = Polynomial.C _
      simp [laumonFibreRingHom]
      rfl }

section Twist

variable {Y X₁ X₂ U : Scheme.{u}} [ConnectedSpace Y] [ConnectedSpace X₁] [ConnectedSpace X₂]
  [ConnectedSpace U] {yb : GeometricPoint Y} {x₁ : GeometricPoint X₁} {x₂ : GeometricPoint X₂}
  {x : GeometricPoint U} {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

/-- **Twists of representations pulled back along one morphism, by equal characters, are
conjugate**: if `ρᵢ = (σ ∘ Aᵢ ∘ Φᵢ) ⊗ (χᵢ ∘ Φᵢ)` with `Φᵢ`, `Aᵢ` induced by base changes along
`fᵢ : Y → Xᵢ`, `aᵢ : Xᵢ → U` with `f₁ ≫ a₁ = f₂ ≫ a₂`, and `χ₂ ∘ Φ₂ = χ₁ ∘ Φ₁`, then `ρ₂` is
conjugate to `ρ₁`: the two maps `π₁(Y) → π₁(U)` are inner conjugate and the scalar characters are
central. -/
public theorem exists_conj_of_isEtaleFundamentalGroupHomInducedBy
    (σ : EtaleFundamentalGroup U x →* GL n O) {f₁ : Y ⟶ X₁} {a₁ : X₁ ⟶ U} {f₂ : Y ⟶ X₂}
    {a₂ : X₂ ⟶ U} (h : f₁ ≫ a₁ = f₂ ≫ a₂)
    {Φ₁ : EtaleFundamentalGroup Y yb →* EtaleFundamentalGroup X₁ x₁}
    {A₁ : EtaleFundamentalGroup X₁ x₁ →* EtaleFundamentalGroup U x}
    {Φ₂ : EtaleFundamentalGroup Y yb →* EtaleFundamentalGroup X₂ x₂}
    {A₂ : EtaleFundamentalGroup X₂ x₂ →* EtaleFundamentalGroup U x}
    (hΦ₁ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f₁) Φ₁)
    (hA₁ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange a₁) A₁)
    (hΦ₂ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f₂) Φ₂)
    (hA₂ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange a₂) A₂)
    (χ₁ : EtaleFundamentalGroup X₁ x₁ →* Oˣ) (χ₂ : EtaleFundamentalGroup X₂ x₂ →* Oˣ)
    (hχ : ∀ γ, χ₂ (Φ₂ γ) = χ₁ (Φ₁ γ)) (ρ₁ ρ₂ : EtaleFundamentalGroup Y yb →* GL n O)
    (hρ₁ : ∀ γ, ρ₁ γ = σ (A₁ (Φ₁ γ)) *
      Units.map (Matrix.scalar n : O →+* Matrix n n O).toMonoidHom (χ₁ (Φ₁ γ)))
    (hρ₂ : ∀ γ, ρ₂ γ = σ (A₂ (Φ₂ γ)) *
      Units.map (Matrix.scalar n : O →+* Matrix n n O).toMonoidHom (χ₂ (Φ₂ γ))) :
    ∃ g : GL n O, ∀ γ, ρ₂ γ = g⁻¹ * ρ₁ γ * g := by
  obtain ⟨c, hc⟩ := (hΦ₁.comp_baseChange hA₁).isInnerConjugate_of_eq
    (hΦ₂.comp_baseChange hA₂) h
  refine ⟨(σ c)⁻¹, fun γ => ?_⟩
  have hs : Commute (Units.map (Matrix.scalar n : O →+* Matrix n n O).toMonoidHom
      (χ₁ (Φ₁ γ))) (σ c)⁻¹ :=
    Units.ext (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
  have hc' : A₂ (Φ₂ γ) = c * A₁ (Φ₁ γ) * c⁻¹ := hc γ
  rw [hρ₂, hρ₁, hχ, inv_inv, hc', map_mul, map_mul, map_inv]
  simp only [mul_assoc, hs.eq]

end Twist

/-- **(c) The fibres of Laumon's family over the `t`-line**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the `E`-linear Frobenius of `κ(v)` on
`H¹_c(Y_κ̄, K|_Y ⊗ ℚ_ℓ)` has the characteristic polynomial of the one on
`H¹_c(𝔸¹_κ̄, ℱ_σ ⊗ L_ψ''(s xⁿ⁰ + (c s) x) ⊗ ℚ_ℓ)`, `s = t(v)`, `ψ'' = ψ ∘ Tr_{κ(v)/k}`. -/
public theorem laumonFamilyFibreLinearInput : LaumonFamilyFibreLinearInput.{u} := by
  intro B ℓ _ _ _ _ k _ _ U _ _ e _ x E _ _ _ d b m σ ψ n₀ k' _ _ _ c hS hL z hz p₀ hσ₁ V' U' _ _
    jV' jU g' hjV' hU v _ Y _ i fY _ _ _ hY jY kbar _ _ _ p n _ _ hcard hfin C hC
  subst hz
  -- the fields
  let iκk : Algebra k (V'.1.residueField v) := laumonPointAlgebra jV' v k
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  let iκ' : Algebra k' (V'.1.residueField v) :=
    ((laumonPointRingHom jV' v).comp Polynomial.C).toAlgebra
  have hκt : IsScalarTower k k' (V'.1.residueField v) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite k k' := Module.Finite.of_finite
  have : Module.Finite k' (V'.1.residueField v) := Module.Finite.of_finite
  have : Module.Finite k (V'.1.residueField v) := Module.Finite.of_finite
  have : Algebra.IsAlgebraic k (V'.1.residueField v) := Algebra.IsAlgebraic.of_finite k _
  -- the fibre `Y ≅ 𝔸¹_{κ(v)}`
  obtain ⟨β, hβC, hβφ⟩ := exists_laumonFamilyFibre_iso jV' v jU g' hU i fY hY
  have hX' : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (V'.1.residueField v)))) := by
    show Scheme.size _ < B.cutoff
    rw [← Scheme.size_congr β]
    exact Y.2
  let X' := Stacks.ArtinSchreier.specObject (Polynomial (V'.1.residueField v)) B hX'
  let βB : Y ⟶ X' := ObjectProperty.homMk β.hom
  have : IsIso (B.inclusion.map βB) := inferInstanceAs (IsIso β.hom)
  have hX'n : IsNoetherian X'.1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (V'.1.residueField v)))))
  have hX'c : ConnectedSpace X'.1 :=
    inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial (V'.1.residueField v)))))
  have hYc : ConnectedSpace Y.1 :=
    @Function.Surjective.connectedSpace _ _ _ hX'c _ _ (Scheme.homeoOfIso β.symm).surjective
      (Scheme.homeoOfIso β.symm).continuous
  have : Nonempty Y.1 := hYc.toNonempty
  have : IsOpenImmersion (B.inclusion.map jU) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hU.flip hjV'
  have : Nonempty U'.1 := ⟨B.inclusion.map i (Classical.arbitrary Y.1)⟩
  have hU'c : ConnectedSpace U'.1 := by
    have hA2i : IrreducibleSpace
        (B.inclusion.obj (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)) :=
      PrimeSpectrum.irreducibleSpace (R := Polynomial (Polynomial k'))
    have hU'ne : Nonempty (B.inclusion.obj U') := ‹Nonempty U'.1›
    have hU'i : IrreducibleSpace (B.inclusion.obj U') :=
      (B.inclusion.map jU).isOpenEmbedding.irreducibleSpace
    exact connectedSpace_iff_univ.mpr
      (@IrreducibleSpace.isIrreducible_univ (B.inclusion.obj U') _ hU'i).isConnected
  let yb : GeometricPoint Y.1 := GeometricPoint.ofPoint Y.1 (Classical.arbitrary Y.1)
  -- the family representation
  let gU := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e
  let M := (etaleFundamentalGroupMap gU (z.map (laumonFamilyPr₁ k'))).toMonoidHom
  let ψ' := ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom
  let A2 := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS
  have hσ₁' : Continuous (restrictScalarsRep b (σ.comp M)) := hσ₁
  let Lrep := laumonFamilyRep k' ψ' n₀ c z p₀ (σ.comp M)
  have hLrep : Continuous (restrictScalarsRep b Lrep) :=
    continuous_restrictScalarsRep_laumonFamilyRep k' b ψ' n₀ c z p₀ (σ.comp M) hσ₁'
  obtain ⟨t₁⟩ := nonempty_finiteEtaleFiberFunctorIso A2.1 z ((yb.map i.hom).map jU.hom)
  let ρK := ((Lrep.comp (etaleFundamentalGroupBasePointHom t₁).toMonoidHom).comp
    (etaleFundamentalGroupMap jU.hom (yb.map i.hom)).toMonoidHom).comp
      (etaleFundamentalGroupMap i.hom yb).toMonoidHom
  have hρK : Continuous (restrictScalarsRep b ρK) :=
    ((hLrep.comp (etaleFundamentalGroupBasePointHom t₁).continuous).comp
      (etaleFundamentalGroupMap jU.hom (yb.map i.hom)).continuous).comp
        (etaleFundamentalGroupMap i.hom yb).continuous
  -- the fibre data
  obtain ⟨x', hx'⟩ := exists_geometricPoint_polynomial_map_eq e (V'.1.residueField v)
    ((z.map (laumonFamilyPr₁ k')).map gU)
  let gv : Polynomial (V'.1.residueField v) :=
    Polynomial.C (laumonPointRingHom jV' v Polynomial.X) * Polynomial.X ^ n₀ +
      Polynomial.C (laumonPointRingHom jV' v (Polynomial.C c) *
        laumonPointRingHom jV' v Polynomial.X) * Polynomial.X
  obtain ⟨p₀'⟩ := Stacks.ArtinSchreier.nonempty_finiteEtaleFiberFunctor_cover
    (V'.1.residueField v) gv x'
  let ψ'' := ψ.compAddMonoidHom (Algebra.trace k (V'.1.residueField v)).toAddMonoidHom
  let gκ := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    (algebraMap k (V'.1.residueField v)))) ≫ inv e
  let hκ := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    ((laumonPointRingHom jV' v).comp Polynomial.C)))
  have hg : hκ ≫ gU = gκ := by
    simp only [hκ, gU, gκ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Polynomial.mapRingHom_comp]
  have hτ₀ : Continuous (restrictScalarsRep b (σ.comp (hx' ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k (V'.1.residueField v)))) ≫
        inv e) x').toMonoidHom))) :=
    continuous_restrictScalarsRep_comp_of_factor hκ gU gκ hg x'
      (isEtaleFundamentalGroupHomInducedBy_map gU (z.map (laumonFamilyPr₁ k')))
      (isEtaleFundamentalGroupHomInducedBy_map_cast gκ x' hx') b σ hσ₁'
  let τ := characterTwist (σ.comp (hx' ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k (V'.1.residueField v)))) ≫
        inv e) x').toMonoidHom))
    (Stacks.ArtinSchreier.artinSchreierCharacter (V'.1.residueField v)
      (Polynomial (V'.1.residueField v)) gv ψ'' x' p₀')
  have hτ : Continuous (restrictScalarsRep b τ) :=
    continuous_restrictScalarsRep_characterTwist_artinSchreierCharacter (V'.1.residueField v)
      (Polynomial (V'.1.residueField v)) gv b ψ'' x' p₀' _ hτ₀
  obtain ⟨t₃⟩ := nonempty_finiteEtaleFiberFunctorIso X'.1 x' (yb.map βB.hom)
  let τβ := (τ.comp (etaleFundamentalGroupBasePointHom t₃).toMonoidHom).comp
    (etaleFundamentalGroupMap βB.hom yb).toMonoidHom
  have hτβ : Continuous (restrictScalarsRep b τβ) :=
    (hτ.comp (etaleFundamentalGroupBasePointHom t₃).continuous).comp
      (etaleFundamentalGroupMap βB.hom yb).continuous
  -- the two representations of `π₁(Y, ȳ)` are conjugate
  have hiφ : i.hom ≫ jU.hom = βB.hom ≫ Spec.map (CommRingCat.ofHom (laumonFibreRingHom jV' v)) :=
    hβφ
  let Φ₁' := ((etaleFundamentalGroupBasePointHom t₁).toMonoidHom.comp
    (etaleFundamentalGroupMap jU.hom (yb.map i.hom)).toMonoidHom).comp
      (etaleFundamentalGroupMap i.hom yb).toMonoidHom
  have hΦ₁' : IsEtaleFundamentalGroupHomInducedBy
      (finiteEtaleBaseChange ((i.hom ≫ jU.hom) ≫ 𝟙 _)) Φ₁' :=
    ((isEtaleFundamentalGroupHomInducedBy_map i.hom yb).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_map jU.hom (yb.map i.hom))).comp_baseChange
        (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t₁)
  let Φβ := (etaleFundamentalGroupBasePointHom t₃).toMonoidHom.comp
    (etaleFundamentalGroupMap βB.hom yb).toMonoidHom
  have hΦβ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange (βB.hom ≫ 𝟙 _)) Φβ :=
    (isEtaleFundamentalGroupHomInducedBy_map βB.hom yb).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t₃)
  have hpr : Spec.map (CommRingCat.ofHom (laumonFibreRingHom jV' v)) ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.C : Polynomial k' →+* Polynomial (Polynomial k'))) = hκ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, laumonFibreRingHom_comp_C]
  have hf : ((i.hom ≫ jU.hom) ≫ 𝟙 _) ≫ (laumonFamilyPr₁ k' ≫ gU) = (βB.hom ≫ 𝟙 _) ≫ gκ := by
    rw [Category.comp_id, Category.comp_id, hiφ, ← hg, ← hpr]
    simp only [Category.assoc]
  have hψ : ∀ a, ψ'' a = ψ' (Algebra.trace k' (V'.1.residueField v) a) := fun a => by
    show ψ (Algebra.trace k (V'.1.residueField v) a) =
      ψ (Algebra.trace k k' (Algebra.trace k' (V'.1.residueField v) a))
    rw [Algebra.trace_trace]
  have hχ := artinSchreierCharacter_trace_baseChange_eq k' (V'.1.residueField v) ψ' ψ'' hψ
    (laumonKernel k' n₀ c) (laumonFibreAlgHom jV' v) gv
    (laumonFibreRingHom_laumonKernel jV' v n₀ c) z p₀ x' p₀' ((i.hom ≫ jU.hom) ≫ 𝟙 _)
    (βB.hom ≫ 𝟙 _) (by rw [Category.comp_id, Category.comp_id, hiφ]; rfl) hΦ₁' hΦβ
  obtain ⟨gc, hconj⟩ := exists_conj_of_isEtaleFundamentalGroupHomInducedBy σ hf hΦ₁'
    ((isEtaleFundamentalGroupHomInducedBy_map (laumonFamilyPr₁ k') z).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_map gU (z.map (laumonFamilyPr₁ k')))) hΦβ
    (isEtaleFundamentalGroupHomInducedBy_map_cast gκ x' hx')
    (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
      (laumonKernel k' n₀ c) ψ' z p₀)
    (Stacks.ArtinSchreier.artinSchreierCharacter (V'.1.residueField v)
      (Polynomial (V'.1.residueField v)) gv ψ'' x' p₀') hχ ρK τβ (fun _ => rfl) (fun _ => rfl)
  -- the chain of `E`-linear isomorphisms
  let f' := Spec.map (CommRingCat.ofHom
    (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v))))
  have : LocallyOfFiniteType f' := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let j' := affineLineProjectiveCompactification (V'.1.residueField v)
  let G0 := LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (restrictScalarsRepCoefficientSheaf B A2 z b Lrep hLrep))
  let Fτ := restrictScalarsRepCoefficientSheaf B X' x' b τ hτ
  let := G0.rationalCohomologyModule fY jY kbar 1 E
  let := Fτ.rationalCohomologyModule f' j' kbar 1 E
  let := (restrictScalarsRepCoefficientSheaf B Y yb b ρK hρK).rationalCohomologyModule fY jY kbar
    1 E
  let := (restrictScalarsRepCoefficientSheaf B Y yb b τβ hτβ).rationalCohomologyModule fY jY kbar
    1 E
  have hfY : fY = B.inclusion.map βB ≫ f' := hβC.symm
  have hchain : ∃ eY : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
      G0.toLAdicSheaf 1 ≃ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ f' j' kbar Fτ.toLAdicSheaf 1,
      ∀ w, eY (G0.rationalGeometricCompactlySupportedFrobenius fY jY kbar 1 E p n hcard w) =
        Fτ.rationalGeometricCompactlySupportedFrobenius f' j' kbar 1 E p n hcard (eY w) := by
    refine exists_linearEquiv_intertwining_trans
      (exists_inverseImage_inverseImage_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b jU i yb
        t₁ Lrep hLrep hρK fY jY kbar 1 p n hcard) ?_
    refine exists_linearEquiv_intertwining_trans
      (exists_restrictScalarsRepCoefficientSheaf_conjLinearEquiv B Y yb b hρK hτβ gc hconj fY
        jY kbar 1 p n hcard) ?_
    exact exists_isIso_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b βB yb t₃ τ hτ hτβ f' j'
      fY jY hfY kbar 1 p n hcard
  obtain ⟨eY, heY⟩ := hchain
  -- finite dimensionality and the characteristic polynomials
  have := G0.rationalCohomologyModule_isScalarTower fY jY kbar 1 E
    (algebraMap_conjIntegralSubring_algebraMap _ _)
  have := Fτ.rationalCohomologyModule_isScalarTower f' j' kbar 1 E
    (algebraMap_conjIntegralSubring_algebraMap _ _)
  have hfin' : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      B Y ℓ fY jY kbar G0.toLAdicSheaf 1) := hfin
  have hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
      X' ℓ f' j' kbar Fτ.toLAdicSheaf 1) :=
    LinearEquiv.finiteDimensional (eY.restrictScalars ℚ_[ℓ])
  refine hC hX' x' hx' p₀' hτ j' hV ?_
  have : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY
      kbar G0.toLAdicSheaf 1) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  have : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ f' j'
      kbar Fτ.toLAdicSheaf 1) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  show (G0.rationalGeometricCompactlySupportedFrobenius fY jY kbar 1 E p n hcard).charpoly =
    (Fτ.rationalGeometricCompactlySupportedFrobenius f' j' kbar 1 E p n hcard).charpoly
  rw [← eY.charpoly_conj]
  congr 1
  refine LinearMap.ext fun w => ?_
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, heY, LinearEquiv.apply_symm_apply]

end Stacks.EtaleCohomology

end
