module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLisseLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilySheaf

/-!
# A basic open of the lisse locus of `Rʳ g_!`, avoiding a given divisor

Let `g : U → Spec R` be separated of finite type, `R` a Noetherian domain, and `G` a lisse ℓ-adic
sheaf on `U`. The lisse locus of the higher direct images with compact support
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageLisseLocusInput_higherDirectImageShriek`,
with Tag 0GL0 now a theorem, `Stacks.EtaleCohomology.lowerShriekConstructibilityInput`) is a
nonempty open of `Spec R`, so it contains a basic open `D(f₁)`, `f₁ ≠ 0`. Given `h₀ ≠ 0`,
`f = f₁ h₀` is nonzero, divisible by `h₀`, and over every open `V'` of `Spec R` inside `D(f)`
(so off the zeros of `h₀`), with `g' : U' → V'` the base change of `g` and any compactification,
every `Rʳ g'_!(G|_{U'})` is lisse
(`Stacks.EtaleCohomology.exists_ne_zero_dvd_forall_isLisse_higherDirectImageShriek`).

For Laumon's degeneration ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), piece P2 of
`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`), `R = k'[t]`, `g = pr₂` and `G` the family
sheaf (`Stacks.EtaleCohomology.laumonFamilySheaf`), and `h₀ = t · D(t, c t)`: the open `V` avoids
the origin and the zeros of `D` on the line.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

section LisseLocus

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
  {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (hR : schemeSizeBelow B.cutoff (Spec (.of R)))

/-- **A basic open of the lisse locus of the `Rʳ g_!`, off a given divisor**: for
`g : U → Spec R` separated of finite type (`R` a Noetherian domain), `G` lisse on `U` and
`h₀ ≠ 0` in `R`, there is `f ≠ 0` divisible by `h₀` such that over every open `V' ⊆ D(f)`, with
`g' : U' → V'` the base change of `g` and any compactification `jg'` of `g'`, every
`Rʳ g'_!(G|_{U'})` is lisse. -/
public theorem exists_ne_zero_dvd_forall_isLisse_higherDirectImageShriek {U : B.Scheme}
    [IsNoetherian U.1] (g : U ⟶ Stacks.ArtinSchreier.specObject R B hR)
    [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map g)] (G : LAdicSheaf.{u, u + 1} B U ℓ) (hG : G.IsLisse)
    (h₀ : R) (hh₀ : h₀ ≠ 0) :
    ∃ f : R, f ≠ 0 ∧ h₀ ∣ f ∧ ∀ (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1]
      (jV' : V' ⟶ Stacks.ArtinSchreier.specObject R B hR) (jU : U' ⟶ U) (g' : U' ⟶ V')
      [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
      [IsSeparated (B.inclusion.map g')]
      (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
      IsOpenImmersion (B.inclusion.map jV') →
      Set.range (B.inclusion.map jV') ⊆ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) →
      IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
        (B.inclusion.map jV') →
      ∀ r : ℕ, (LAdicSheaf.higherDirectImageShriek B ℓ g' jg'
        (LAdicSheaf.inverseImage jU G) r).IsLisse := by
  have : IsReduced (Stacks.ArtinSchreier.specObject R B hR).1 :=
    inferInstanceAs (IsReduced (Spec (.of R)))
  have : IsNoetherian (Stacks.ArtinSchreier.specObject R B hR).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of R)))
  have : Nonempty (Stacks.ArtinSchreier.specObject R B hR).1 :=
    inferInstanceAs (Nonempty (PrimeSpectrum R))
  obtain ⟨V₀, jV₀, hjV₀, ⟨v⟩, hV₀⟩ :=
    LAdicSheaf.higherDirectImageLisseLocusInput_higherDirectImageShriek B ℓ
      (lowerShriekConstructibilityInput B) U _ g G hG inferInstance
  -- a basic open `D(f₁)` inside the image of `V₀`
  have hopen : IsOpen (Set.range (B.inclusion.map jV₀)) :=
    (B.inclusion.map jV₀).isOpenEmbedding.isOpen_range
  have hmem : ((B.inclusion.map jV₀) v : PrimeSpectrum R) ∈ Set.range (B.inclusion.map jV₀) :=
    ⟨v, rfl⟩
  obtain ⟨_, ⟨_, ⟨f₁, rfl⟩, rfl⟩, hvf₁, hf₁⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hmem hopen
  have hf₁0 : f₁ ≠ 0 := by
    rintro rfl
    exact hvf₁ (Ideal.zero_mem _)
  refine ⟨f₁ * h₀, mul_ne_zero hf₁0 hh₀, dvd_mul_left _ _, ?_⟩
  intro V' U' _ _ jV' jU g' _ _ _ jg' hjV' hrange hpb r
  have hrange₀ : Set.range (B.inclusion.map jV') ⊆ Set.range (B.inclusion.map jV₀) := by
    refine hrange.trans (fun p hp => hf₁ ?_)
    rw [PrimeSpectrum.basicOpen_mul] at hp
    exact hp.1
  let jV'' : V' ⟶ V₀ := ObjectProperty.homMk
    (IsOpenImmersion.lift (B.inclusion.map jV₀) (B.inclusion.map jV') hrange₀)
  have hfac : jV'' ≫ jV₀ = jV' := by
    ext : 1
    exact IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (B.inclusion.map jV'') := by
    have : IsOpenImmersion (B.inclusion.map jV'' ≫ B.inclusion.map jV₀) := by
      rw [← Functor.map_comp, hfac]
      exact hjV'
    exact IsOpenImmersion.of_comp _ (B.inclusion.map jV₀)
  exact hV₀ V' U' jV'' jU g' jg' inferInstance (by rw [hfac]; exact hpb) r

end LisseLocus

section Family

open Polynomial

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
  (ℓ : ℕ) [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (n₀ : ℕ) (c : k')
  (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
  (p₀ : (finiteEtaleFiberFunctor z).obj
    (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c))) {m : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The open `V` of Laumon's degeneration** (piece P2 of
`Stacks.EtaleCohomology.LaumonDegenerationFamilyInput`): for the family sheaf
`pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t (xⁿ⁰ + c x))` on `Spec k'[x][t]` and a nonzero `Dline ∈ k'[t]` (the
restriction `D(t, c t)` of the curve of `Stacks.EtaleCohomology.LaumonFibrePure`,
`Stacks.EtaleCohomology.exists_aeval_line_ne_zero`), there is `f ≠ 0` in `k'[t]` divisible by
`t · Dline` such that over every open `V' ⊆ D(f)` of the `t`-line (so `V'` misses the origin and
the zeros of `Dline`), with `g' : U' → V'` the base change of `pr₂` and any compactification,
every `Rʳ g'_!` of the restriction of the family sheaf is lisse. -/
public theorem exists_laumonFamily_lisseLocus
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁)) (Dline : Polynomial k')
    (hD : Dline ≠ 0) :
    ∃ f : Polynomial k', f ≠ 0 ∧ Polynomial.X * Dline ∣ f ∧ ∀ (V' U' : B.Scheme) [IsNoetherian V'.1]
      [IsNoetherian U'.1] (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
      (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
      [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
      [IsSeparated (B.inclusion.map g')]
      (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
      IsOpenImmersion (B.inclusion.map jV') →
      Set.range (B.inclusion.map jV') ⊆
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial k'))) →
      IsPullback (B.inclusion.map jU) (B.inclusion.map g')
        (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
      ∀ r : ℕ, (LAdicSheaf.higherDirectImageShriek B ℓ g' jg'
        (LAdicSheaf.inverseImage jU
          (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf) r).IsLisse := by
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  exact exists_ne_zero_dvd_forall_isLisse_higherDirectImageShriek B ℓ hL
    (laumonFamilyProjection k' B hS hL) _
    (LAdicSheaf.representationSheaf_isLisse _ _ _ _ _) (Polynomial.X * Dline)
    (mul_ne_zero Polynomial.X_ne_zero hD)

end Family

end Stacks.EtaleCohomology
