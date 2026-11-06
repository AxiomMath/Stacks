module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ProperDirectImageConstructibleTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityOfIsUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaFibration

/-!
# Proper direct images along curve fibrations preserve `D_ctf`

Let `k` be a finite field, `Λ` a finite ring (not necessarily commutative) of order prime to
`#k`, `h : X ⟶ Y` a proper morphism of schemes proper over `k`, and `j_U : U ⟶ X` an open
immersion such that the fibres of `j_U ≫ h` have dimension at most one. For `K₀ ∈ D_ctf(U, Λ)`
bounded below and a resolution `J` of `j_{U!} K₀` by injectives, `h_* J ∈ D_ctf(Y, Λ)`. This is the
statement `Stacks.EtaleCohomology.DirectImagePreservesCtf` consumed by the fibration step of the
trace formula in any dimension, [Stacks, Tag 03UI] (1).

The proof follows the source: `Rh_*(j_{U!} K₀) = Rf_! K₀` for `f = j_U ≫ h` has perfect stalks
(proper base change, and the perfectness of `RΓ` of `D_ctf` on proper curves over an algebraically
closed field), bounded cohomology (Tag 0A53), and constructible cohomology sheaves (Tag 0GL0 over
`ℤ/n`, `n` the characteristic of `Λ`, which is invertible on `Y`, read for `Λ` through restriction
of scalars), so it lies in `D_ctf` by Tag 03TT, (1) ⟹ (2), for a noncommutative Noetherian ring.

## Main results

* `Stacks.EtaleCohomology.isUnit_ringChar_cast_appTop_of_coprime`
* `Stacks.EtaleCohomology.directImagePreservesCtf`

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (1), the proof.
* [Stacks Project, Tag 0GL0](https://stacks.math.columbia.edu/tag/0GL0)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModules_ab5OfSize
attribute [local instance high] smallEtale_hasSheafify_moduleCat_of_type
  hasWeakSheafify_over_moduleCat_type isRightAdjoint_smallEtalePushforward_moduleCat_type

/-- **The characteristic of a finite coefficient ring of order prime to `q` is invertible on a
scheme over `𝔽_q`**: for a finite ring `Λ` with `#Λ` prime to `#k`, `k` a finite field, the
characteristic `n` of `Λ` is a unit in `Γ(Y, 𝒪_Y)` for every scheme `Y` over `k`. -/
theorem isUnit_ringChar_cast_appTop_of_coprime (Λ : Type) [Ring Λ] [Finite Λ] (k : Type u)
    [Field k] [Fintype k] (hcop : Nat.Coprime (Nat.card Λ) (Fintype.card k)) {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k)) : IsUnit ((ringChar Λ : ℕ) : Γ(Y, ⊤)) := by
  have hΛ : ringChar Λ ∣ Nat.card Λ := ringChar.dvd (by
    rw [← nsmul_one]
    exact card_nsmul_eq_zero')
  have hk : ((ringChar Λ : ℕ) : k) ≠ 0 := by
    intro h0
    have h1 : ringChar k ∣ Nat.gcd (Nat.card Λ) (Fintype.card k) :=
      Nat.dvd_gcd ((ringChar.dvd h0).trans hΛ) (ringChar.dvd (FiniteField.cast_card_eq_zero k))
    rw [hcop] at h1
    exact CharP.ringChar_ne_one (Nat.dvd_one.1 h1)
  have := (isUnit_iff_ne_zero.2 hk).map ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop).hom
  simpa using this

/-- **Proper direct images of extensions by zero along curve fibrations lie in `D_ctf`**, for a
finite coefficient ring `Λ` of order prime to `#k`: the statement
`Stacks.EtaleCohomology.DirectImagePreservesCtf` holds. -/
theorem directImagePreservesCtf
    (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] [Finite Λ] (k : Type u) [Field k] [Fintype k]
    (hcop : Nat.Coprime (Nat.card Λ) (Fintype.card k)) :
    DirectImagePreservesCtf B Λ k := by
  intro X Y U fY hfYp h _ hhfY jU _ hfib K₀ hK₀ J ψ hψ hJ
  have := hψ
  have : CompactSpace Y.obj := QuasiCompact.compactSpace_of_compactSpace fY
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace (h ≫ fY)
  have : LocallyOfFiniteType (h ≫ fY) := hhfY.toLocallyOfFiniteType
  have : LocallyOfFiniteType fY := hfYp.toLocallyOfFiniteType
  have hXl : IsLocallyNoetherian X.obj := LocallyOfFiniteType.isLocallyNoetherian (h ≫ fY)
  have hYl : IsLocallyNoetherian Y.obj := LocallyOfFiniteType.isLocallyNoetherian fY
  have : IsNoetherian X.obj := { }
  have : TopologicalSpace.NoetherianSpace U.obj := jU.isOpenEmbedding.isEmbedding.noetherianSpace
  have : QuasiCompact jU := quasiCompact_of_noetherianSpace_source jU
  have : QuasiSeparatedSpace Y.obj := IsLocallyNoetherian.quasiSeparatedSpace
  have : LocallyOfFiniteType (jU ≫ h) := inferInstance
  have : IsLocallyNoetherian U.obj := LocallyOfFiniteType.isLocallyNoetherian (jU ≫ h)
  have : QuasiSeparatedSpace U.obj := IsLocallyNoetherian.quasiSeparatedSpace
  have : LocallyOfFinitePresentation (jU ≫ h) :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  -- the coefficient ring `ℤ/n`, `n` the characteristic of `Λ`
  let n := ringChar Λ
  have : CharP Λ n := ringChar.charP Λ
  have : NeZero n := ⟨CharP.char_ne_zero_of_finite Λ n⟩
  let ρ : ZMod n →+* Λ := ZMod.castHom dvd_rfl Λ
  -- a bounded representative `C` of `K₀` and a resolution `I` of `j_{U!} C` by injectives
  obtain ⟨C, a, b, ha, hb, hflat, ⟨e₀⟩⟩ := (isCtf_iff_of_qcqs B Λ _).1 hK₀
  have := ha
  have := hb
  have hC : IsCtf B U Λ (DerivedCategory.Q.obj C) := hK₀.of_iso B U Λ e₀.symm
  have : EnoughInjectives (EtaleModules.{u, 0} Λ X.obj) :=
    etaleModules_enoughInjectives.{u, 0} Λ X.obj
  let Cb : CochainComplex.Plus (EtaleModules.{u, 0} Λ U.obj) := ⟨C, ⟨a, inferInstance⟩⟩
  let L := (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj Cb
  obtain ⟨c, _⟩ := L.property
  obtain ⟨R, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE c L.obj
  let I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj) := ⟨R.cocomplex, R.boundedBelow⟩
  let φ : L ⟶ I := ObjectProperty.homMk R.ι
  have : QuasiIso φ.hom := inferInstanceAs (QuasiIso R.ι)
  have hI : ∀ n, Injective (I.obj.X n) := fun n => inferInstanceAs (Injective (R.cocomplex.X n))
  -- constructibility, by Tag 0GL0 over `ℤ/n`
  have hR : IsConstructibleEtaleComplex (ZMod n) ((derivedLowerShriekUnbounded.{u, 0} (jU ≫ h)
      (compactificationOfOpenImmersionProper jU h) (ZMod n)).obj
        (DerivedCategory.Q.obj (((etaleModuleRestrictScalars ρ U.obj).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C))) := fun i =>
    ((isTorsionConstructibleEtaleComplexPlus_derivedLowerShriekUnbounded_of_isUnit_natCast
      (ZMod n) (Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite Λ n)) (ZMod.natCast_self n)
      (jU ≫ h) (isUnit_ringChar_cast_appTop_of_coprime Λ k hcop fY) _ _
      (isTorsionConstructibleEtaleComplexPlus_restrictScalars B ρ U C a hflat)).2 i).2
  have hc := isConstructibleModuleSheaf_homology_directImage_of_isConstructibleEtaleComplex B ρ X Y
    U h jU C a I φ hI hR
  obtain ⟨eJI⟩ := nonempty_directImage_iso_of_extensionByZero_iso Λ h jU K₀ Cb e₀.symm J ψ hJ I φ hI
  exact (isCtf_directImage_extensionByZero_of_isConstructible_of_bounded Λ B X Y U h jU hfib C a b
    hC I φ hI hc).of_iso B Y Λ eJI.symm

end Stacks.EtaleCohomology

end
