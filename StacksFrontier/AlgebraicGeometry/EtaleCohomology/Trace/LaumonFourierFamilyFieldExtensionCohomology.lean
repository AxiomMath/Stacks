module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierFamilyFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierFamilyConjugateWild

/-!
# The fibres of Laumon's Fourier family over every point of the `t`-line

This proves `Stacks.EtaleCohomology.LaumonFourierFamilyFieldExtensionInput`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): for the Fourier family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(a xⁿ + x t)` on `𝔸² = Spec k'[x][t]`, its restriction to `U' = pr₂⁻¹(V')`
and the fibre `Y` of `U' → V'` over ANY point `v` with finite residue field, the `E`-linear
Frobenius of `κ(v)` on `H¹_c(Y_κ̄, K|_Y ⊗ ℚ_ℓ)` has the characteristic polynomial of the Frobenius
of `κ(v)` on `H¹_c(𝔸¹_k̄', ℱ_τ ⊗ ℚ_ℓ)`, `τ = σ ⊗ L_{ψ ∘ Tr_{κ(v)/k}}(a(v) xⁿ + t(v) x)`, for every
choice of the data of the latter (geometric point, point of the Artin–Schreier cover,
compactification, algebraic closure `k̄'` of `κ(v)`)
(`Stacks.EtaleCohomology.laumonFourierFamilyFieldExtensionInput`).

The fibre is `Y ≅ 𝔸¹_{κ(v)}` (`Stacks.EtaleCohomology.exists_laumonFamilyFibre_iso`) and the
isomorphism of cohomologies is the chain of
`Stacks.EtaleCohomology.laumonFamilyFibreLinearInput` for the kernel `a xⁿ + x t`: inverse images
and changes of base point, conjugacy of the two representations of `π₁(Y, ȳ)` (the
Artin–Schreier characters agree by the trace compatibility over the extension of constants
`κ(v) / k'`), the transport along `Y ≅ 𝔸¹_{κ(v)}`, followed by the independence of the algebraic
closure (`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalAlgEquivLinearEquiv`).

## Main results

In the namespace `Stacks.EtaleCohomology`:

* `exists_conj_laumonFourierFamilyRep_of_extension`.
* `charpoly_inverseImage_conj_isIso_rationalGeometricCompactlySupportedFrobenius_eq`.
* `laumonFourierFamilyFieldExtensionInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Conj

variable {U : Scheme.{u}} [ConnectedSpace U] {E : Type} [Field E] {m : ℕ} {k : Type u} [Field k]
  [Fintype k] {k' : Type u} [Field k'] [Fintype k'] [Algebra k k'] (ψ : AddChar k E) (n : ℕ)
  (a : k') {κ : Type u} [Field κ] [Fintype κ] [Algebra k' κ] [Algebra k κ] [IsScalarTower k k' κ]
  (gU : Spec (.of (Polynomial k')) ⟶ U) (gκ : Spec (.of (Polynomial κ)) ⟶ U)

omit [Fintype k] in
/-- **The representations of `π₁(Y, ȳ)` of the Fourier family and of its fibre over an extension
of constants are conjugate**: for `f₁ : Y → 𝔸²` factoring as `Spec(φ) ∘ f₂` through
`f₂ : Y → 𝔸¹_κ` for a `k'`-algebra map `φ : k'[x][t] → κ[x]` with `φ(a xⁿ + x t) = g`, and
`Spec(φ) ∘ pr₁ ∘ g_U = g_κ`, the pullbacks along `f₁` of
`σ ∘ g_U* ∘ pr₁* ⊗ L_{ψ∘Tr_{k'/k}}(a xⁿ + x t)` and along `f₂` of `σ ∘ g_κ* ⊗ L_{ψ∘Tr_{κ/k}}(g)`
are conjugate. -/
public theorem exists_conj_laumonFourierFamilyRep_of_extension
    [Finite k] [Module.Finite k' κ] [Module.Finite k k'] {Y : Scheme.{u}} [ConnectedSpace Y]
    {yb : GeometricPoint Y} (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (σ : EtaleFundamentalGroup U ((z.map (laumonFamilyPr₁ k')).map gU) →* GL (Fin m) E)
    (pz : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    (x' : GeometricPoint (Spec (.of (Polynomial κ))))
    (hx' : x'.map gκ = (z.map (laumonFamilyPr₁ k')).map gU) (g : Polynomial κ)
    (φ : Polynomial (Polynomial k') →ₐ[k'] Polynomial κ) (hφ : φ (laumonFourierKernel k' n a) = g)
    (p₀ : (finiteEtaleFiberFunctor x').obj (Stacks.ArtinSchreier.cover κ (Polynomial κ) g))
    (f₁ : Y ⟶ Spec (.of (Polynomial (Polynomial k')))) (f₂ : Y ⟶ Spec (.of (Polynomial κ)))
    (hfc : f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hg : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ laumonFamilyPr₁ k' ≫ gU = gκ)
    {Φ₁ : EtaleFundamentalGroup Y yb →*
      EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z}
    {Φ₂ : EtaleFundamentalGroup Y yb →* EtaleFundamentalGroup (Spec (.of (Polynomial κ))) x'}
    (hΦ₁ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f₁) Φ₁)
    (hΦ₂ : IsEtaleFundamentalGroupHomInducedBy (finiteEtaleBaseChange f₂) Φ₂) :
    ∃ c : GL (Fin m) E, ∀ γ,
      characterTwist (σ.comp (hx' ▸ (etaleFundamentalGroupMap gκ x').toMonoidHom))
          (Stacks.ArtinSchreier.artinSchreierCharacter κ (Polynomial κ) g
            (ψ.compAddMonoidHom (Algebra.trace k κ).toAddMonoidHom) x' p₀) (Φ₂ γ) =
        c⁻¹ * laumonFourierFamilyRep k' (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a
          z pz (σ.comp (etaleFundamentalGroupMap gU (z.map (laumonFamilyPr₁ k'))).toMonoidHom)
            (Φ₁ γ) * c := by
  have hf : f₁ ≫ (laumonFamilyPr₁ k' ≫ gU) = f₂ ≫ gκ := by
    rw [hfc, Category.assoc, hg]
  have hψ : ∀ w, ψ.compAddMonoidHom (Algebra.trace k κ).toAddMonoidHom w =
      ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom (Algebra.trace k' κ w) := fun w => by
    show ψ (Algebra.trace k κ w) = ψ (Algebra.trace k k' (Algebra.trace k' κ w))
    rw [Algebra.trace_trace]
  have hχ := artinSchreierCharacter_trace_baseChange_eq k' κ _ _ hψ (laumonFourierKernel k' n a) φ g
    hφ z pz x' p₀ f₁ f₂ hfc hΦ₁ hΦ₂
  obtain ⟨c, hc⟩ := exists_conj_of_isEtaleFundamentalGroupHomInducedBy σ hf hΦ₁
    ((isEtaleFundamentalGroupHomInducedBy_map (laumonFamilyPr₁ k') z).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_map gU (z.map (laumonFamilyPr₁ k')))) hΦ₂
    (isEtaleFundamentalGroupHomInducedBy_map_cast gκ x' hx') _ _ hχ
    ((laumonFourierFamilyRep k' (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz
      (σ.comp (etaleFundamentalGroupMap gU (z.map (laumonFamilyPr₁ k'))).toMonoidHom)).comp Φ₁)
    ((characterTwist (σ.comp (hx' ▸ (etaleFundamentalGroupMap gκ x').toMonoidHom))
      (Stacks.ArtinSchreier.artinSchreierCharacter κ (Polynomial κ) g
        (ψ.compAddMonoidHom (Algebra.trace k κ).toAddMonoidHom) x' p₀)).comp Φ₂)
    (fun _ => rfl) (fun _ => rfl)
  exact ⟨c, fun γ => hc γ⟩

end Conj

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

/-- **The characteristic polynomials of the Frobenius agree along the chain for a fibre `Y ≅ X`**:
for a fibre `i : Y → U'` of an open `jU : U' → A₂`, an isomorphism `β : Y ≅ X` over `κ`, and
representations `ρ_K = L ∘ t₁ ∘ jU_* ∘ i_*`, `τ_β = σ ∘ t ∘ β_*` of `π₁(Y, ȳ)` conjugate by `g`,
the Frobenius of `κ` on `Hⁱ_c(Y_κ̄, i⁻¹ jU⁻¹ ℱ_{Res L} ⊗ ℚ_ℓ)` and on
`Hⁱ_c(X_κ̄', ℱ_{Res σ} ⊗ ℚ_ℓ)` have the same characteristic polynomial, for any algebraic closures
`κ̄ ≅ κ̄'` over `κ`. -/
public theorem charpoly_inverseImage_conj_isIso_rationalGeometricCompactlySupportedFrobenius_eq
    {A₂ U' : B.Scheme} (jU : U' ⟶ A₂) [ConnectedSpace A₂.1] [ConnectedSpace U'.1]
    [IsNoetherian A₂.1] [IsNoetherian U'.1] {z : GeometricPoint A₂.1}
    (L : EtaleFundamentalGroup A₂.1 z →* GL (Fin m) E) (hL : Continuous (restrictScalarsRep b L))
    {F₀ : _} (hF₀ : F₀ = restrictScalarsRepCoefficientSheaf B A₂ z b L hL)
    {X : B.Scheme} [ConnectedSpace X.1] [IsNoetherian X.1] {κ : Type u} [Field κ] [Fintype κ]
    (f : X.1 ⟶ Spec (.of κ)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra κ kbar]
    {Y : B.Scheme} [IsNoetherian Y.1] [ConnectedSpace Y.1] (i : Y ⟶ U') (fY : Y.1 ⟶ Spec (.of κ))
    [LocallyOfFiniteType fY] [QuasiCompact fY] [IsSeparated fY]
    (jY : CompactificationOf (Over.mk fY)) (β : Y ⟶ X) [IsIso (B.inclusion.map β)]
    (hfY : fY = B.inclusion.map β ≫ f)
    {x : GeometricPoint X.1} (y : GeometricPoint Y.1)
    (t₁ : finiteEtaleFiberFunctor z ≅ finiteEtaleFiberFunctor ((y.map i.hom).map jU.hom))
    (hρ : Continuous (restrictScalarsRep b
      (((L.comp (etaleFundamentalGroupBasePointHom t₁).toMonoidHom).comp
        (etaleFundamentalGroupMap jU.hom (y.map i.hom)).toMonoidHom).comp
          (etaleFundamentalGroupMap i.hom y).toMonoidHom)))
    (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor (y.map β.hom))
    (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (hσ : Continuous (restrictScalarsRep b σ))
    (hσ' : Continuous (restrictScalarsRep b
      ((σ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom).comp
        (etaleFundamentalGroupMap β.hom y).toMonoidHom)))
    (g : GL (Fin m) E)
    (hconj : ∀ γ, σ (etaleFundamentalGroupBasePointHom t (etaleFundamentalGroupMap β.hom y γ)) =
      g⁻¹ * L (etaleFundamentalGroupBasePointHom t₁ (etaleFundamentalGroupMap jU.hom (y.map i.hom)
        (etaleFundamentalGroupMap i.hom y γ))) * g)
    (kbar' : Type u) [Field kbar'] [Algebra κ kbar'] (σ' : kbar' ≃ₐ[κ] kbar)
    (n : ℤ) (p q : ℕ) [Fact p.Prime] [CharP κ p] (hcard : Fintype.card κ = p ^ q) :
    letI := (LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
      F₀)).rationalCohomologyModule fY jY kbar n E
    letI := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar' n E
    ∀ (_ : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY
        kbar (LAdicSheaf.CoefficientSheaf.inverseImage i
          (LAdicSheaf.CoefficientSheaf.inverseImage jU F₀)).toLAdicSheaf n))
      (_ : Module.Finite E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar'
        (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf n)),
    ((LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
        F₀)).rationalGeometricCompactlySupportedFrobenius fY jY kbar n E p q hcard).charpoly =
      ((restrictScalarsRepCoefficientSheaf B X x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar' n E p q hcard).charpoly := by
  subst hF₀
  let := (LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (restrictScalarsRepCoefficientSheaf B A₂ z b L hL))).rationalCohomologyModule fY jY kbar n E
  let := (restrictScalarsRepCoefficientSheaf B Y y b _ hρ).rationalCohomologyModule fY jY kbar n E
  let := (restrictScalarsRepCoefficientSheaf B Y y b _ hσ').rationalCohomologyModule fY jY kbar n
    E
  let := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar n E
  let := (restrictScalarsRepCoefficientSheaf B X x b σ hσ).rationalCohomologyModule f j kbar' n E
  intro _ _
  have hchain : ∃ e : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar
      (LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
        (restrictScalarsRepCoefficientSheaf B A₂ z b L hL))).toLAdicSheaf n ≃ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar'
        (restrictScalarsRepCoefficientSheaf B X x b σ hσ).toLAdicSheaf n,
      ∀ v, e ((LAdicSheaf.CoefficientSheaf.inverseImage i
          (LAdicSheaf.CoefficientSheaf.inverseImage jU
            (restrictScalarsRepCoefficientSheaf B A₂ z b L
              hL))).rationalGeometricCompactlySupportedFrobenius fY jY kbar n E p q hcard v) =
        (restrictScalarsRepCoefficientSheaf B X x b σ
          hσ).rationalGeometricCompactlySupportedFrobenius f j kbar' n E p q hcard (e v) := by
    refine exists_linearEquiv_intertwining_trans
      (exists_inverseImage_inverseImage_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b jU i y
        t₁ L hL hρ fY jY kbar n p q hcard) ?_
    refine exists_linearEquiv_intertwining_trans
      (exists_restrictScalarsRepCoefficientSheaf_conjLinearEquiv B Y y b hρ hσ' g (fun γ => hconj γ)
        fY jY kbar n p q hcard) ?_
    refine exists_linearEquiv_intertwining_trans
      (exists_isIso_restrictScalarsRepCoefficientSheaf_linearEquiv B ℓ b β y t σ hσ hσ' f j fY jY
        hfY kbar n p q hcard) ?_
    exact ⟨(restrictScalarsRepCoefficientSheaf B X x b σ
        hσ).rationalAlgEquivLinearEquiv B ℓ f j σ' n E,
      (restrictScalarsRepCoefficientSheaf B X x b σ
        hσ).rationalAlgEquivLinearEquiv_frobenius B ℓ f j σ' n p q hcard E⟩
  obtain ⟨e, he⟩ := hchain
  rw [← e.charpoly_conj]
  congr 1
  refine LinearMap.ext fun w => ?_
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, he, LinearEquiv.apply_symm_apply]

/-- A finite-dimensional `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is finite over `E` for its `E`-module structure. -/
private theorem finite_rationalCohomologyModule {X : B.Scheme} [IsNoetherian X.1] {O : Type}
    [CommRing O] [Algebra ℤ_[ℓ] O] [Algebra O E] [IsLocalization (Submonoid.powers (ℓ : O)) E]
    (F : LAdicSheaf.CoefficientSheaf B X ℓ O) {k : Type u} [Field k] [Fintype k]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)
    (hfin : FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf 1)) :
    letI := F.rationalCohomologyModule f j kbar 1 E
    Module.Finite E
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf 1) :=
  letI := F.rationalCohomologyModule f j kbar 1 E
  haveI := F.rationalCohomologyModule_isScalarTower f j kbar 1 E hOE
  Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _

end Chains

/-- **The fibres of the Fourier family over every point of `V'`, for all choices**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the `E`-linear Frobenius of `κ(v)` on
`H¹_c(Y_κ̄, K|_Y ⊗ ℚ_ℓ)` has the characteristic polynomial of the Frobenius of `κ(v)` on
`H¹_c(𝔸¹_k̄', ℱ_σ ⊗ L_{ψ∘Tr_{κ(v)/k}}(a(v) xⁿ + t(v) x) ⊗ ℚ_ℓ)`, for every choice of the data. -/
public theorem laumonFourierFamilyFieldExtensionInput :
    LaumonFourierFamilyFieldExtensionInput.{u} := by
  intro B U ℓ _ _ _ _ k _ _ e _ x E _ _ d b m σ ψ n k' _ _ _ a hS hL z hz pz hσ₁ V' U' _ _
    jV' jU g' hjV' hU v _ Y _ i fY _ _ _ hY jY kbarv _ _ _ pv nv _ _ hcardv hfin hX' _ _
    x' hx' p₀ hτ _ _ _ j' kbar' _ _ _ hV
  have hW : ∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) := fun n T =>
    AlgebraicGeometry.hasWeakSheafify_smallEtale_of_scheme B _ T
  subst hz
  let iκk : Algebra k (V'.1.residueField v) := laumonPointAlgebra jV' v k
  let iκ' : Algebra k' (V'.1.residueField v) :=
    ((laumonPointRingHom jV' v).comp Polynomial.C).toAlgebra
  have : IsScalarTower k k' (V'.1.residueField v) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite k k' := Module.Finite.of_finite
  have : Module.Finite k' (V'.1.residueField v) := Module.Finite.of_finite
  obtain ⟨β, hβC, hβφ⟩ := exists_laumonFamilyFibre_iso jV' v jU g' hU i fY hY
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
  have hU'c : ConnectedSpace U'.1 := connectedSpace_of_isOpenImmersion_laumonPlane jU
  let yb : GeometricPoint Y.1 := GeometricPoint.ofPoint Y.1 (Classical.arbitrary Y.1)
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
    ((hLrep.comp (etaleFundamentalGroupBasePointHom t₁).continuous).comp
      (etaleFundamentalGroupMap jU.hom (yb.map i.hom)).continuous).comp
        (etaleFundamentalGroupMap i.hom yb).continuous
  let gκ := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    (algebraMap k (V'.1.residueField v)))) ≫ inv e
  let hκ := Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom
    ((laumonPointRingHom jV' v).comp Polynomial.C)))
  have hg0 : hκ ≫ gU = gκ := by
    simp only [hκ, gU, gκ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Polynomial.mapRingHom_comp]
  have hpr : Spec.map (CommRingCat.ofHom (laumonFibreAlgHom jV' v).toRingHom) ≫
      laumonFamilyPr₁ k' = hκ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) (laumonFibreRingHom_comp_C jV' v)
  let g'' : Polynomial (V'.1.residueField v) :=
    Polynomial.C (laumonPointRingHom jV' v (Polynomial.C a)) * Polynomial.X ^ n +
      Polynomial.C (laumonPointRingHom jV' v Polynomial.X) * Polynomial.X
  let ψ'' := ψ.compAddMonoidHom (Algebra.trace k (V'.1.residueField v)).toAddMonoidHom
  let τ := characterTwist (σ.comp (hx' ▸ (etaleFundamentalGroupMap gκ x').toMonoidHom))
    (Stacks.ArtinSchreier.artinSchreierCharacter (V'.1.residueField v)
      (Polynomial (V'.1.residueField v)) g'' ψ'' x' p₀)
  obtain ⟨t₃⟩ := nonempty_finiteEtaleFiberFunctorIso X'.1 x' (yb.map βB.hom)
  let τβ := (τ.comp (etaleFundamentalGroupBasePointHom t₃).toMonoidHom).comp
    (etaleFundamentalGroupMap βB.hom yb).toMonoidHom
  have hτβ : Continuous (restrictScalarsRep b τβ) :=
    (hτ.comp (etaleFundamentalGroupBasePointHom t₃).continuous).comp
      (etaleFundamentalGroupMap βB.hom yb).continuous
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
  have hiφ : i.hom ≫ jU.hom = βB.hom ≫ Spec.map (CommRingCat.ofHom (laumonFibreRingHom jV' v)) :=
    hβφ
  obtain ⟨gc, hconj⟩ := exists_conj_laumonFourierFamilyRep_of_extension ψ n a gU gκ z σ pz x' hx'
    g'' (laumonFibreAlgHom jV' v)
    (laumonFourierKernel_eval k' ((laumonPointRingHom jV' v).comp Polynomial.C) n a _) p₀
    ((i.hom ≫ jU.hom) ≫ 𝟙 _) (βB.hom ≫ 𝟙 _)
    (by rw [Category.comp_id, Category.comp_id, hiφ]; rfl)
    (by rw [← Category.assoc, hpr, hg0]) hΦ₁' hΦβ
  let f' := Spec.map (CommRingCat.ofHom
    (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v))))
  have hf'1 : LocallyOfFiniteType f' := ‹LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v)))))›
  have hf'2 : QuasiCompact f' := ‹QuasiCompact (Spec.map (CommRingCat.ofHom
    (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v)))))›
  have hf'3 : IsSeparated f' := ‹IsSeparated (Spec.map (CommRingCat.ofHom
    (algebraMap (V'.1.residueField v) (Polynomial (V'.1.residueField v)))))›
  have hfY : fY = B.inclusion.map βB ≫ f' := hβC.symm
  have hK : laumonFourierFamilySheaf k' B hS b ψ' n a z pz _ hσ₁ =
      restrictScalarsRepCoefficientSheaf B A2 z b Lrep hLrep := rfl
  let G0 := LAdicSheaf.CoefficientSheaf.inverseImage i (LAdicSheaf.CoefficientSheaf.inverseImage jU
    (restrictScalarsRepCoefficientSheaf B A2 z b Lrep hLrep))
  let Fτ := restrictScalarsRepCoefficientSheaf B X' x' b τ hτ
  let := G0.rationalCohomologyModule fY jY kbarv 1 E
  let := Fτ.rationalCohomologyModule f' j' kbar' 1 E
  have hYfin := finite_rationalCohomologyModule B ℓ G0 fY jY kbarv
    (algebraMap_conjIntegralSubring_algebraMap _ _) hfin
  have hXfin := finite_rationalCohomologyModule B ℓ Fτ f' j' kbar'
    (algebraMap_conjIntegralSubring_algebraMap _ _) hV
  exact charpoly_inverseImage_conj_isIso_rationalGeometricCompactlySupportedFrobenius_eq
    (X := X') (Y := Y) B ℓ b jU Lrep hLrep hK f' j' kbarv i fY jY βB hfY yb t₁ hρK t₃ τ hτ hτβ
    gc hconj kbar' (IsAlgClosure.equiv (V'.1.residueField v) kbar' kbarv) 1 pv nv hcardv hYfin
    hXfin

end Stacks.EtaleCohomology

end
