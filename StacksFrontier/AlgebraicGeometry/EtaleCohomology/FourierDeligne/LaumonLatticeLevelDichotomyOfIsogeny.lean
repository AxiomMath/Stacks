module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LaumonFourierLineAbsIrrOfLatticeDichotomy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomySheafIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierMonodromyLevelDichotomy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseEtaleSheafMonodromy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomyIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ConstructibleKernelCokernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingValuation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PadicIntegerRingExtensionModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilySheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic

/-!
# The lattice level dichotomy of `τ ⊗ E'` from the level isogeny with `H¹Φ`

`Stacks.EtaleCohomology.LaumonLatticeLevelDichotomyInput` (the input of piece L6 of Laumon's proof
of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), see
`Stacks.EtaleCohomology.laumonFourierLineAbsIrrInput'_of_latticeLevelDichotomy`) asks, for every
finite extension `E''` of `E` inside `Ē`, for an integral model `τ_O` of `τ ⊗ E''` whose reduction
modulo some `ℓ^{N+1}` satisfies the level dichotomy at `(N, b)` with `b ≤ N`. We take
`O'' = integralClosure ℤ_ℓ E''` (a discrete valuation ring), the models `σ_O` of
`σ' = σ₁ ⊗ L_{ψ'}(a xⁿ)` and `τ_O` of `τ` (`Stacks.EtaleCohomology.exists_padicIntegerRing_model`),
and:

* `c₀` from the absolute irreducibility of `σ'` (the hypothesis of the target, transported to
  `σ_O`) through `Stacks.EtaleCohomology.exists_shifted_levelDichotomy_of_absIrr`: the levels of
  `σ_O` satisfy the dichotomy at `(N' - c, c₀ + c)` for all `c ≤ N'`;
* `c` from `Stacks.EtaleCohomology.LaumonFourierLevelIsogenyInput`: an `ℓᶜ`-isogeny between
  `H¹(Φ(ℱ_{σ_O mod ℓ^{N'+1}}))|_{V'}` and `ℱ_{τ_O mod ℓ^{N'+1}}`, with `c` INDEPENDENT of `N'`;
* the dichotomy for the Fourier transform on the lisse locus (S6), carried through the isogeny
  (`Stacks.EtaleCohomology.continuousModuleLevelDichotomy_of_isogeny_fourierTransform`), gives the
  dichotomy of `τ_O mod ℓ^{N'+1}` at `(N', c₀ + 2c)`; take `N' = b = c₀ + 2c`.

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLevelIsogenyInput`: the level isogeny (the sheaf chain).

## Main results

* `Stacks.EtaleCohomology.continuousModuleLevelDichotomy_of_isogeny_fourierTransform`.
* `Stacks.EtaleCohomology.laumonLatticeLevelDichotomyInput_of_levelIsogeny`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
  Polynomial Stacks.GroupCohomology

universe u v w

namespace Stacks.EtaleCohomology

section Matrix

variable {O : Type} [CommRing O] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {m : ℕ}

/-- **The level dichotomy of a matrix module from that of the stable submodules of `(O/I)^m`**,
`I = (ℓ^{N'+1})`: the form of `Stacks.EtaleCohomology.continuousModuleLevelDichotomy_of_matrix`
for `Stacks.EtaleCohomology.matrixContinuousModule` of the reduction of `σ : G → GL_m(O)`. -/
theorem continuousModuleLevelDichotomy_matrixContinuousModule (σ : G →* GL (Fin m) O) (ℓ : ℕ)
    {N' : ℕ} (hσ : IsOpen (((Matrix.GeneralLinearGroup.map
      (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (N' + 1)}))).comp σ).ker : Set G))
    [Finite (O ⧸ Ideal.span {(ℓ : O) ^ (N' + 1)})] (N c₀ : ℕ)
    (hD : ∀ S : Submodule (O ⧸ Ideal.span {(ℓ : O) ^ (N' + 1)})
        (Fin m → O ⧸ Ideal.span {(ℓ : O) ^ (N' + 1)}),
      (∀ A ∈ Set.range fun g => (σ g).val, ∀ v ∈ S,
        A.map (algebraMap O (O ⧸ Ideal.span {(ℓ : O) ^ (N' + 1)})) *ᵥ v ∈ S) →
      (∃ x ∈ S, (ℓ : O) ^ N • x ≠ 0) →
        ∀ w : Fin m → O ⧸ Ideal.span {(ℓ : O) ^ (N' + 1)}, (ℓ : O) ^ c₀ • w ∈ S) :
    ContinuousModuleLevelDichotomy (matrixContinuousModule.{v, w}
      (O ⧸ Ideal.span {(ℓ : O) ^ (N' + 1)}) ((Matrix.GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.span {(ℓ : O) ^ (N' + 1)}))).comp σ) hσ) ℓ N c₀ :=
  continuousModuleLevelDichotomy_of_matrix (Set.range fun g => (σ g).val) ULift.moduleEquiv
    (by
      rintro _ ⟨g, rfl⟩
      exact ⟨g, 1, fun v => by rw [one_smul]; rfl⟩)
    (ℓ : O) ℓ (map_natCast _ _) N c₀ hD

/-- **A matrix module is free.** -/
theorem free_matrixContinuousModule (Λ : Type) [CommRing Λ] (σ : G →* GL (Fin m) Λ)
    (hσ : IsOpen (σ.ker : Set G)) :
    Module.Free Λ (matrixContinuousModule.{v, w} Λ σ hσ).obj.obj.obj.V :=
  Module.Free.of_equiv (ULift.moduleEquiv (R := Λ) (M := Fin m → Λ)).symm

end Matrix

section Generic

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj
    (Stacks.ArtinSchreier.cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => Stacks.ArtinSchreier.affineLineStructureMap k

/-- **The level dichotomy of a lisse sheaf `ℒ` isogenous to `H¹(Φ(ℱ_P))`** (steps M1, M2, M6, M7
of the comparison in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).
Let `P` be a free finite continuous `Λ`-`π₁(𝔸¹_k, x̄₁)`-module satisfying the level dichotomy at
`N, c₀`, `V'` a connected Noetherian open of `𝔸¹_k` and `ℒ = ℱ_{P'}` lisse on `V'`. If the
restriction to `V'` of `H¹(Φ(ℱ_P[0]))` is `ℓᶜ`-isogenous to `ℒ`, then `P'` satisfies the level
dichotomy at `N + c, c₀ + c`: on a nonempty open `V'' ⊆ V'` on which `H¹(Φ(ℱ_P[0]))` is locally
constant (it is constructible), the monodromy of `H¹(Φ(ℱ_P[0]))` satisfies the dichotomy at
`N, c₀` (`Stacks.EtaleCohomology.fourier_monodromy_level_dichotomy`), hence so does that of
`ℒ|_{V''}` at `N + c, c₀ + c`, hence that of `ℒ`, and the monodromy of `ℱ_{P'}` is `P'`. -/
theorem continuousModuleLevelDichotomy_of_isogeny_fourierTransform (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k))))
    (x₁ : GeometricPoint (Spec (.of (Polynomial k))))
    (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup (Spec (.of (Polynomial k))) x₁))
    (hPf : Module.Free Λ P.obj.obj.obj.V) (V' : B.Scheme) [IsNoetherian V'.1]
    [ConnectedSpace V'.1] (jV' : V'.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV']
    (xV : GeometricPoint V'.1)
    (P' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup V'.1 xV))
    (f : (etaleModuleInverseImage.{u, 0} Λ jV').obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k) B hL) x₁ Λ).obj
              P)))) ⟶ (lisseEtaleSheaf B V' xV Λ).obj P')
    (g : (lisseEtaleSheaf B V' xV Λ).obj P' ⟶ (etaleModuleInverseImage.{u, 0} Λ jV').obj
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k) B hL) x₁ Λ).obj
              P)))))
    {ℓ c : ℕ} (hfg : f ≫ g = ℓ ^ c • 𝟙 _) (hgf : g ≫ f = ℓ ^ c • 𝟙 _) {N c₀ : ℕ}
    (hP : ContinuousModuleLevelDichotomy P ℓ N c₀) :
    ContinuousModuleLevelDichotomy P' ℓ (N + c) (c₀ + c) := by
  have : IsNoetherianRing Λ := inferInstance
  let X₁ := Stacks.ArtinSchreier.specObject (Polynomial k) B hL
  have : ConnectedSpace X₁.1 := inferInstanceAs (ConnectedSpace (Spec (.of (Polynomial k))))
  let F := (lisseEtaleSheaf B X₁ x₁ Λ).obj P
  have hF : IsLocallyFreeEtaleModule Λ F := isLocallyFreeEtaleModule_lisseEtaleSheaf Λ B X₁ x₁ P hPf
  let H := (DerivedCategory.Plus.homologyFunctor _ 1).obj ((fourierTransform k Λ ψ B p₀ j).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have hHc : IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, 0} Λ jV').obj H) :=
    isConstructibleEtaleModule_etaleModuleInverseImage Λ jV' H
      (isConstructibleEtaleModule_homology_fourierTransform k Λ ψ B p₀ j F
        (isConstructibleEtaleModule_of_isFiniteTypeLocallyConstant Λ
          (isFiniteTypeLocallyConstant_lisseEtaleSheaf B X₁ x₁ P)) 1)
  have : IsReduced V'.1 := isReduced_of_isOpenImmersion jV'
  have : Nonempty V'.1 := ⟨xV.hom.base (IsLocalRing.closedPoint xV.residueField)⟩
  -- the lisse locus `V''`
  obtain ⟨U, hUne, hU, -⟩ :=
    exists_opens_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule Λ hHc hHc
  let VB : B.Scheme := B.obj U ((Scheme.size_coe_opens_le _ U).trans_lt V'.property)
  let ι : VB ⟶ V' := ObjectProperty.homMk U.ι
  have : IrreducibleSpace V'.1 := jV'.isOpenEmbedding.irreducibleSpace
  have : Nonempty U := hUne.to_subtype
  have : IrreducibleSpace VB.1 := U.ι.isOpenEmbedding.irreducibleSpace
  have : ConnectedSpace VB.1 := inferInstance
  let jV : VB.1 ⟶ Spec (.of (Polynomial k)) := U.ι ≫ jV'
  have : IsOpenImmersion jV := inferInstanceAs (IsOpenImmersion (U.ι ≫ jV'))
  let e := etaleModuleInverseImageCompObjIso Λ U.ι jV' H
  have hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ VB.1.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ jV).obj H) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ e.symm hU
  let v : GeometricPoint VB.1 := GeometricPoint.ofPoint VB.1 ⟨_, hUne.some_mem⟩
  obtain ⟨jQ, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace
    (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)
  have hdich := continuousModuleLevelDichotomy_lisseEtaleSheaf B X₁ x₁ P hP x₁
    (isFiniteTypeLocallyConstant_of_isLocallyConstantWith F hF)
  -- the dichotomy for the Fourier transform on `V''` (S6)
  have hS6 : ContinuousModuleLevelDichotomy
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B VB v Λ).functor.obj ⟨_, hG⟩)
      ℓ N c₀ := fun W hW hne =>
    (fourier_monodromy_level_dichotomy k Λ ψ B p₀ hψ hq j jQ F hF VB jV v hG ℓ N c₀ x₁ hdich W
      hW).resolve_left fun h0 => by
        obtain ⟨x, hx, hx0⟩ := hne
        exact hx0 (h0 x hx)
  -- through the isogeny, restricted to `V''`
  let Fι := etaleModuleInverseImage.{u, 0} Λ U.ι
  have hℒ := isFiniteTypeLocallyConstant_lisseEtaleSheaf B V' xV P'
  have hℒU := isFiniteTypeLocallyConstant_etaleModuleInverseImage_of_hom U.ι Λ _ hℒ
  have h1 := continuousModuleLevelDichotomy_of_isogeny B VB v hℒU hG (Fι.map g ≫ e.inv)
    (e.hom ≫ Fι.map f) (by
      rw [Category.assoc, e.inv_hom_id_assoc, ← Fι.map_comp, hgf, Functor.map_nsmul,
        CategoryTheory.Functor.map_id]) (by
      rw [Category.assoc, ← Fι.map_comp_assoc, hfg, Functor.map_nsmul,
        CategoryTheory.Functor.map_id, Preadditive.nsmul_comp, Category.id_comp,
        Preadditive.comp_nsmul, e.hom_inv_id]) hS6
  have h2 := continuousModuleLevelDichotomy_of_inverseImage B ι hℒ hℒU v h1 xV
  obtain ⟨e'⟩ := nonempty_monodromy_lisseEtaleSheaf_iso B V' xV P' hℒ
  exact h2.of_iso e'

end Generic

section Isogeny

attribute [local instance] padicIntAlgebraOfRat HasDerivedCategory.standard

/-- **The level isogeny between `H¹Φ` of the levels of an `O''`-model of `σ'` and the levels of an
`O''`-model of `τ`** (the sheaf chain of the comparison in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). In the situation of
`Stacks.EtaleCohomology.LaumonLatticeLevelDichotomyInput`, for every finite extension `E''` of `E`
inside `Ē` with ring of integers `O''`, every `O''`-model `σ_O` of
`σ' = σ₁ ⊗ L_{ψ'}(a xⁿ)` and every `O''`-model `τ_O` of `τ`, there is an exponent `c`,
INDEPENDENT of the level `N'`, such that at every level `N'`, for `Λ = O''/ℓ^{N'+1}`, a nontrivial
additive character `ψ_N : k' → Λ`, and the Fourier transform `Φ` attached to it, the restriction to
`V'` of `H¹(Φ(ℱ_{σ_O mod ℓ^{N'+1}}))` and the lisse sheaf of `τ_O mod ℓ^{N'+1}` on `V'` are
`ℓᶜ`-isogenous as sheaves of `Λ`-modules. The Fourier transform lives in the standard model of the
derived category. -/
def LaumonFourierLevelIsogenyInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k' : Type u) [Field k'] [Fintype k'] (p : ℕ) [Fact p.Prime] [CharP k' p], ℓ ≠ p →
    ∀ (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E), ψ' ≠ 1 →
    (∃ ζ : E, IsPrimitiveRoot ζ p) → ∀ (n : ℕ) (a : k')
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    {m : ℕ}
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (p₁ : (finiteEtaleFiberFunctor (z.map (laumonFamilyPr₁ k'))).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial k') (Polynomial.C a * Polynomial.X ^ n))),
    ∀ (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1] [ConnectedSpace V'.1]
      (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
      (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
      [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
      [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
    IsOpenImmersion (B.inclusion.map jV') →
    IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
    ∀ (xV : GeometricPoint V'.1) {r : ℕ}
      (ρ : EtaleFundamentalGroup V'.1 xV →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
      (φ : (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b ψ' n a z p₀ σ₁ hσ₁ jU g'
          jg').toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B V' xV ρ hρ)
      (ψ₀ : LAdicSheaf.representationSheaf B V' xV ρ hρ ⟶
        (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b ψ' n a z p₀ σ₁ hσ₁ jU g'
          jg').toLAdicSheaf) (N : ℕ)
      (hφψ : φ ≫ ψ₀ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ₀ ≫ φ = (ℓ ^ N) • 𝟙 _) {mτ : ℕ}
      (τ : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) E)
      (P : Matrix (Fin r) (Fin (mτ * d)) ℚ_[ℓ]) (Q : Matrix (Fin (mτ * d)) (Fin r) ℚ_[ℓ]),
      P * Q = 1 →
      (∀ e' : E, Q * isogenyCoefficientAlgHom B V' xV
        (laumonFourierRestrictedHigherDirectImage k' B hS ℓ b ψ' n a z p₀ σ₁ hσ₁ jU g' jg')
        ρ hρ φ ψ₀ N E hφψ hψφ (algebraMap_conjIntegralSubring_algebraMap _ _) e' * P =
          restrictScalarsMatrix b (Matrix.scalar (Fin mτ) e')) →
      (∀ g : EtaleFundamentalGroup V'.1 xV,
        haveI := compactSpace_etaleFundamentalGroup V'.1 xV
        Q * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ hρ g)).val * P = (restrictScalarsRep b τ g).val) →
      Q * P = 1 →
      ∀ (E'' : IntermediateField E (AlgebraicClosure E)) [FiniteDimensional E E'']
        (σO : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
          GL (Fin m) (integralClosure ℤ_[ℓ] E'')) (T₁ : GL (Fin m) E''),
        (∀ g, (σO g).val.map (algebraMap (integralClosure ℤ_[ℓ] E'') E'') =
          (T₁⁻¹ : GL (Fin m) E'').val * (characterTwist σ₁
              (Stacks.ArtinSchreier.artinSchreierCharacter
            k' (Polynomial k') (Polynomial.C a * Polynomial.X ^ n) ψ' (z.map (laumonFamilyPr₁ k'))
              p₁) g).val.map (algebraMap E E'') * T₁.val) →
        ∀ (hσO : ∀ k : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
            (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (k)}))).comp σO).ker :
            Set (EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')))))
          (τO : EtaleFundamentalGroup V'.1 xV →* GL (Fin mτ) (integralClosure ℤ_[ℓ] E''))
              (T : GL (Fin mτ) E''),
        (∀ g, (τO g).val.map (algebraMap (integralClosure ℤ_[ℓ] E'') E'') =
          (T⁻¹ : GL (Fin mτ) E'').val * (τ g).val.map (algebraMap E E'') * T.val) →
        ∀ (hτO : ∀ k : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
            (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (k)}))).comp τO).ker : Set
            (EtaleFundamentalGroup V'.1 xV))),
        ∃ c : ℕ, ∀ N' : ℕ,
          ∃ (ψN : AddChar k' (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
              {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)})) (_ : ∑ x, ψN x = 0)
            (p₀' : (finiteEtaleFiberFunctor (affineLineOrigin k')).obj
              (Stacks.ArtinSchreier.cover k' (Polynomial k') Polynomial.X))
            (j : CompactificationOf (Over.mk (Stacks.ArtinSchreier.affineLineStructureMap k')))
            (f : (etaleModuleInverseImage.{u, 0} (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
                {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)}) (B.inclusion.map jV')).obj
                ((DerivedCategory.Plus.homologyFunctor _ 1).obj
                  ((fourierTransform k' (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
                      {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)}) ψN B p₀' j).obj
                    ((DerivedCategory.Plus.singleFunctor _ 0).obj
                      ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                        (z.map (laumonFamilyPr₁ k')) (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
                            {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)})).obj
                          (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E'' ⧸
                              Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)})
                            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
                                (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)}))).comp σO)
                                (hσO (N' + 1))))))) ⟶
              (lisseEtaleSheaf B V' xV (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
                  {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)})).obj
                (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
                    {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)})
                  ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
                      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)}))).comp τO)
                      (hτO (N' + 1))))
            (g : (lisseEtaleSheaf B V' xV (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
                {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)})).obj
                (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
                    {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)})
                  ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
                      (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)}))).comp τO)
                      (hτO (N' + 1))) ⟶
              (etaleModuleInverseImage.{u, 0} (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
                  {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)}) (B.inclusion.map jV')).obj
                ((DerivedCategory.Plus.homologyFunctor _ 1).obj
                  ((fourierTransform k' (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
                      {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)}) ψN B p₀' j).obj
                    ((DerivedCategory.Plus.singleFunctor _ 0).obj
                      ((lisseEtaleSheaf B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
                        (z.map (laumonFamilyPr₁ k')) (integralClosure ℤ_[ℓ] E'' ⧸ Ideal.span
                            {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)})).obj
                          (matrixContinuousModule.{u + 1, u + 1} (integralClosure ℤ_[ℓ] E'' ⧸
                              Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)})
                            ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk
                                (Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (N' + 1)}))).comp σO)
                                (hσO (N' + 1)))))))),
            f ≫ g = ℓ ^ c • 𝟙 _ ∧ g ≫ f = ℓ ^ c • 𝟙 _

end Isogeny

section Reduction

attribute [local instance] padicIntAlgebraOfRat HasDerivedCategory.standard
    moduleCat_hasLimitsOfSize

/-- **The lattice level dichotomy of `τ ⊗ E''` from the level isogeny with `H¹Φ`**: for every
finite `E''`, the level `N' = c₀ + 2c` works, where `c₀` is the dichotomy exponent of the model of
`σ'` and `c` the (level-independent) isogeny exponent. -/
theorem laumonLatticeLevelDichotomyInput_of_levelIsogeny
    (hI : LaumonFourierLevelIsogenyInput.{u}) : LaumonLatticeLevelDichotomyInput.{u} := by
  intro B ℓ _ _ _ _ k' _ _ p _ _ hℓp E _ _ _ d b ψ' hψ' hζ n a hS hL z p₀ m σ₁ hσ₁ p₁ hirr V' U'
    _ _ _ jV' jU g' _ _ _ jg' hjV hpb xV r ρ hρ φ ψ₀ N hφψ hψφ mτ τ P Q hPQ hα hτ hQP E'' hE''
  have : FiniteDimensional E E'' := hE''
  have := compactSpace_etaleFundamentalGroup V'.1 xV
  have := compactSpace_etaleFundamentalGroup (Spec (.of (Polynomial k')))
    (z.map (laumonFamilyPr₁ k'))
  -- the integral models of `σ' = σ₁ ⊗ L_{ψ'}(a xⁿ)` and of `τ`
  -- over `O'' = integralClosure ℤ_ℓ E''`
  have hσ' := continuous_restrictScalarsRep_characterTwist_artinSchreierCharacter k'
    (Polynomial k') (Polynomial.C a * Polynomial.X ^ n) b ψ' (z.map (laumonFamilyPr₁ k')) p₁ σ₁ hσ₁
  have hτc : Continuous (restrictScalarsRep b τ) := by
    refine continuous_restrictScalarsRep b τ ?_
    have : (fun g => restrictScalarsMatrix b (τ g).val) = fun g => Q *
        (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ hρ g)).val * P := funext fun g => by
      rw [hτ g, restrictScalarsRep_val]
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.comp
      (continuous_integralModel ρ hρ)).matrix_map continuous_subtype_val)).matrix_mul
        continuous_const
  obtain ⟨σO, T₁, hT₁, hσO⟩ := exists_padicIntegerRing_model b E'' _ hσ'
  obtain ⟨τO, T, hT, hτO⟩ := exists_padicIntegerRing_model b E'' τ hτc
  -- the exponent `c₀` of the level dichotomy of `σ_O` (absolutely irreducible)
  let : Algebra E (AlgebraicClosure E'') :=
    ((algebraMap E'' (AlgebraicClosure E'')).comp (algebraMap E E'')).toAlgebra
  have hirr' : ∀ W : Submodule (AlgebraicClosure E'') (Fin m → AlgebraicClosure E''),
      (∀ A ∈ Set.range fun g => (σO g).val, ∀ v ∈ W,
        (A.map (algebraMap (integralClosure ℤ_[ℓ] E'') E'')).map
          (algebraMap E'' (AlgebraicClosure E'')) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let A : Matrix (Fin m) (Fin m) (AlgebraicClosure E'') :=
      T₁.val.map (algebraMap E'' (AlgebraicClosure E''))
    let A' : Matrix (Fin m) (Fin m) (AlgebraicClosure E'') :=
      (T₁⁻¹ : GL (Fin m) E'').val.map (algebraMap E'' (AlgebraicClosure E''))
    have hA'A : A' * A = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hAA' : A * A' = 1 := mul_eq_one_comm.1 hA'A
    have hrt : ∀ w, A' *ᵥ (A *ᵥ w) = w := fun w => by
      rw [Matrix.mulVec_mulVec, hA'A, Matrix.one_mulVec]
    let W' := W.comap (Matrix.toLin' A')
    have hW' : ∀ g, ∀ v ∈ W', (characterTwist σ₁ (Stacks.ArtinSchreier.artinSchreierCharacter k'
        (Polynomial k') (Polynomial.C a * Polynomial.X ^ n) ψ' (z.map (laumonFamilyPr₁ k'))
          p₁) g).val.map (algebraMap E (AlgebraicClosure E'')) *ᵥ v ∈ W' := by
      intro g v hv
      have hσK : ((σO g).val.map (algebraMap (integralClosure ℤ_[ℓ] E'') E'')).map
          (algebraMap E'' (AlgebraicClosure E'')) = A' * (characterTwist σ₁
            (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
              (Polynomial.C a * Polynomial.X ^ n) ψ' (z.map (laumonFamilyPr₁ k')) p₁) g).val.map
                (algebraMap E (AlgebraicClosure E'')) * A := by
        rw [hT₁ g, Matrix.map_mul, Matrix.map_mul, Matrix.map_map]
        rfl
      show A' *ᵥ (_ *ᵥ v) ∈ W
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_one (A' * _), ← hAA', ← Matrix.mul_assoc,
        ← hσK, ← Matrix.mulVec_mulVec]
      exact hW _ ⟨g, rfl⟩ _ hv
    have hmem : ∀ w, w ∈ W ↔ A *ᵥ w ∈ W' := fun w => by
      change _ ↔ A' *ᵥ (A *ᵥ w) ∈ W
      rw [hrt]
    rcases hirr (AlgebraicClosure E'') W' hW' with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      have hAw := (hmem w).1 hw
      rw [h, Submodule.mem_bot] at hAw
      rw [← hrt w, hAw, Matrix.mulVec_zero]
      exact (Submodule.mem_bot _).2 rfl
    · right
      rw [eq_top_iff]
      intro w _
      exact (hmem w).2 (h ▸ Submodule.mem_top)
  obtain ⟨c₀, hc₀⟩ := exists_shifted_levelDichotomy_of_absIrr (O := integralClosure ℤ_[ℓ] E'')
    E'' (AlgebraicClosure E'') (ℓ := (ℓ : integralClosure ℤ_[ℓ] E''))
    (fun o ho => exists_dvd_natCast_pow_padicIntegerRing ℓ ho) (Set.range fun g => (σO g).val)
    (by rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩; exact ⟨g * h, by simp⟩) ⟨1, by simp⟩ hirr'
  obtain ⟨c, hc⟩ := hI B ℓ k' p hℓp E b ψ' hψ' hζ n a hS hL z p₀ σ₁ hσ₁ p₁ V' U' jV' jU g' jg' hjV
    hpb xV ρ hρ φ ψ₀ N hφψ hψφ τ P Q hPQ hα hτ hQP E'' σO T₁ hT₁ hσO τO T hT hτO
  -- the level `N' = c₀ + 2c`; `c` does not depend on `N'`
  obtain ⟨ψN, hψN, p₀', j, f₀, g₀, hfg₀, hgf₀⟩ := hc (c₀ + c + c)
  have hq : IsUnit (Fintype.card k' : integralClosure ℤ_[ℓ] E'' ⧸
      Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (c₀ + c + c + 1)}) := by
    obtain ⟨f', hp', hcard⟩ := FiniteField.card k' p
    have hcop : (Fintype.card k').Coprime ℓ := by
      rw [hcard]
      exact Nat.Coprime.pow_left _ ((Nat.coprime_primes hp' Fact.out).2 hℓp.symm)
    rw [← map_natCast (Ideal.Quotient.mk _)]
    exact (isUnit_natCast_padicIntegerRing_of_coprime ℓ hcop).map _
  have hPdich : ContinuousModuleLevelDichotomy (matrixContinuousModule.{u + 1, u + 1} _
      ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span
        {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (c₀ + c + c + 1)}))).comp σO) (hσO _)) ℓ
      (c₀ + c + c - c) (c₀ + c) :=
    continuousModuleLevelDichotomy_matrixContinuousModule σO ℓ (hσO _) _ _
      (hc₀ (c₀ + c + c) c (by omega))
  have := hjV
  have key := continuousModuleLevelDichotomy_of_isogeny_fourierTransform k' _ ψN B p₀' hψN hq j
    hL (z.map (laumonFamilyPr₁ k')) _ (free_matrixContinuousModule _ _ _) V'
    (B.inclusion.map jV') xV _ f₀ g₀ hfg₀ hgf₀ hPdich
  rw [Nat.sub_add_cancel (by omega : c ≤ c₀ + c + c)] at key
  exact ⟨(integralClosure ℤ_[ℓ] E'').toSubring,
    inferInstanceAs (ValuationRing (integralClosure ℤ_[ℓ] E'')),
    inferInstanceAs (IsFractionRing (integralClosure ℤ_[ℓ] E'') E''),
    natCast_ne_zero_padicIntegerRing ℓ, not_isUnit_natCast_padicIntegerRing ℓ,
    fun o ho => exists_dvd_natCast_pow_padicIntegerRing ℓ ho, τO, T, hT, c₀ + c + c, c₀ + c + c,
    inferInstanceAs (Finite (integralClosure ℤ_[ℓ] E'' ⧸
      Ideal.span {(ℓ : integralClosure ℤ_[ℓ] E'') ^ (c₀ + c + c + 1)})), le_rfl, hτO _, key⟩

end Reduction

end Stacks.EtaleCohomology

end
