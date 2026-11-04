module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.CohomologySequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupSmoothCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.PicardGroup.OpenUFD
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Descent
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularSchemes
public import StacksFrontier.RingTheory.Localization.AwayPrimeUnits

/-!
# The étale cohomology of `μ_ℓ` on the affine line and on the punctured affine line

Let `k` be an algebraically closed field and `ℓ` an integer invertible in `k`. On the affine
line `𝐀¹_k` and on the punctured affine line `𝐆_m = D(t) ⊆ 𝐀¹_k` the Kummer sequence gives

* `H¹(𝐀¹, μ_ℓ) = 0` and `H²(𝐀¹, μ_ℓ) = 0`, because `Pic(𝐀¹) = 0`, every unit of `k[t]` is an
  `ℓ`-th power and `H²(𝐀¹, 𝐆_m) = 0` (Stacks 03RM);
* `H¹(𝐆_m, μ_ℓ) ≅ k[t, t⁻¹]^× / ℓ ≅ ℤ/ℓ`, because `Pic(𝐆_m) = 0`; in particular this group has
  exactly `ℓ` elements.

These are the global inputs of the computation of the higher direct images of `Λ = ℤ/ℓ` along
`j : 𝐆_m ⟶ 𝐀¹`, which is the local model of cohomological purity in codimension one.

## Main definitions

* `Stacks.EtaleCohomology.Purity.affineLine`, `coordinate`, `punctured`: `𝐀¹_k`, the coordinate
  `t` and the basic open `D(t) = 𝐆_m`.

## Main results

* `Stacks.EtaleCohomology.Purity.subsingleton_sheafH_one_rootsOfUnity_affineLine`.
* `Stacks.EtaleCohomology.Purity.subsingleton_sheafH_two_rootsOfUnity_affineLine`.
* `Stacks.EtaleCohomology.Purity.natCard_sheafH_one_rootsOfUnity_punctured`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.Purity

variable (k : Type u) [Field k]

/-- The affine line `𝐀¹_k`. -/
abbrev affineLine : Scheme.{u} := 𝔸(ULift.{u} (Fin 1); Spec (.of k))

/-- The coordinate `t` on the affine line. -/
def coordinate : Γ(affineLine k, ⊤) := AffineSpace.coord (Spec (.of k)) ⟨0⟩

/-- The punctured affine line `𝐆_m = D(t)`, as an open of `𝐀¹_k`. -/
abbrev punctured : (affineLine k).Opens := (affineLine k).basicOpen (coordinate k)

/-- The global functions of the affine line are the polynomials in one variable. -/
def globalSectionsEquiv : Γ(affineLine k, ⊤) ≃+* MvPolynomial (ULift.{u} (Fin 1)) k :=
  ((Scheme.Γ.mapIso (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).symm.op) ≪≫
    Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin 1)) k))).commRingCatIsoToRingEquiv

/-- The identification of the global functions of `𝐀¹_k` with `k[t]` sends the coordinate to the
variable. -/
theorem globalSectionsEquiv_coordinate :
    globalSectionsEquiv k (coordinate k) = MvPolynomial.X ⟨0⟩ := by
  show (Scheme.ΓSpecIso _).hom ((AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).inv.appTop
    (AffineSpace.coord _ ⟨0⟩)) = _
  rw [AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply, Iso.inv_hom_id,
    CommRingCat.id_apply]

/-- The global functions of the affine line form a domain. -/
instance isDomain_globalSections : IsDomain Γ(affineLine k, ⊤) :=
  (globalSectionsEquiv k).toMulEquiv.isDomain _

/-- The coordinate `t` is a prime element of `k[t] = Γ(𝐀¹_k, 𝒪)`. -/
theorem prime_coordinate : Prime (coordinate k) := by
  rw [← MulEquiv.prime_iff (globalSectionsEquiv k).toMulEquiv]
  show Prime (globalSectionsEquiv k (coordinate k))
  rw [globalSectionsEquiv_coordinate]
  exact MvPolynomial.X_prime

/-- Every unit of `k[t]` is an `n`-th power, `k` being algebraically closed. -/
theorem exists_pow_eq_units_globalSections [IsAlgClosed k] {n : ℕ} (hn : 0 < n)
    (a : (Γ(affineLine k, ⊤))ˣ) : ∃ b : (Γ(affineLine k, ⊤))ˣ, b ^ n = a := by
  have ha := (Units.map (globalSectionsEquiv k).toMonoidHom a).isUnit
  obtain ⟨c, hc⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 ha
  have hc0 : c ≠ 0 := hc.1.ne_zero
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hd, zero_pow hn.ne'])
  let b : (Γ(affineLine k, ⊤))ˣ :=
    (Units.mk0 d hd0).map ((globalSectionsEquiv k).symm.toMonoidHom.comp
      (MvPolynomial.C : k →+* MvPolynomial _ k).toMonoidHom)
  refine ⟨b, Units.ext ?_⟩
  apply (globalSectionsEquiv k).injective
  show globalSectionsEquiv k ((globalSectionsEquiv k).symm (MvPolynomial.C d) ^ n) =
    globalSectionsEquiv k a
  rw [map_pow, RingEquiv.apply_symm_apply, ← map_pow, hd]
  exact hc.2.symm

/-- The Picard group of the affine line vanishes (Stacks 0BDA). -/
theorem subsingleton_picard_affineLine : Subsingleton (Stacks.Picard.ofScheme (affineLine k)) :=
  Stacks.PicardGroup.subsingleton_of_iso (Scheme.topIso (affineLine k))
    (Stacks.PicardUFD.subsingleton_picardGroup_open_affineSpace k (ULift.{u} (Fin 1)) ⊤)

/-- The Picard group of the punctured affine line vanishes (Stacks 0BDA). -/
theorem subsingleton_picard_punctured :
    Subsingleton (Stacks.Picard.ofScheme (punctured k).toScheme) :=
  Stacks.PicardUFD.subsingleton_picardGroup_open_affineSpace k (ULift.{u} (Fin 1)) (punctured k)

variable {k} {ℓ : ℕ}

/-- `ℓ` is invertible on every scheme over `k` on which it is invertible in `k`. -/
theorem isUnit_natCast_globalSections_of_over {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hℓ : IsUnit (ℓ : k)) : IsUnit ((ℓ : ℕ) : Γ(X, ⊤)) := by
  have := hℓ.map (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
  simpa using this

variable (k)

/-- `H¹(𝐀¹, 𝐆_m) = Pic(𝐀¹) = 0`. -/
theorem subsingleton_sheafH_one_multiplicative_affineLine :
    Subsingleton (Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, 0} (affineLine k)) 1) :=
  have := subsingleton_picard_affineLine k
  (Stacks.Kummer.etaleH1MultiplicativeAddEquivPicard.{u + 1, 0, u}
    (affineLine k)).toEquiv.subsingleton

/-- `H¹(𝐆_m, 𝐆_m) = Pic(𝐆_m) = 0`. -/
theorem subsingleton_sheafH_one_multiplicative_punctured :
    Subsingleton (Sheaf.H.{u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} (punctured k).toScheme) 1) :=
  have := subsingleton_picard_punctured k
  (Stacks.Kummer.etaleH1MultiplicativeAddEquivPicard.{u + 1, 0, u}
    (punctured k).toScheme).toEquiv.subsingleton

/-- `H²(𝐀¹, 𝐆_m) = 0` (Stacks 03RM). -/
theorem subsingleton_sheafH_two_multiplicative_affineLine [IsAlgClosed k] :
    Subsingleton (Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, 0} (affineLine k)) 2) :=
  have := isCurve_affineSpace k (ULift.{u} (Fin 1))
  have := AffineSpace.smooth_over (ULift.{u} (Fin 1)) (Spec (.of k))
  subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve (affineLine k ↘ Spec (.of k)) 2 le_rfl

/-- **`H¹(𝐀¹, μ_ℓ) = 0`** for `ℓ` invertible in the algebraically closed field `k`. -/
theorem subsingleton_sheafH_one_rootsOfUnity_affineLine [IsAlgClosed k] (hℓ0 : 0 < ℓ)
    (hℓ : IsUnit (ℓ : k)) :
    Subsingleton (Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ) 1) := by
  have hX := isUnit_natCast_globalSections_of_over (affineLine k ↘ Spec (.of k)) hℓ
  have hinj := Stacks.Kummer.injective_sheafH_map_rootsOfUnityι_one.{u + 1, u, 0}
    (affineLine k) hℓ0.ne' hX
    (Stacks.Kummer.surjective_sheafH_map_powMap_zero.{u + 1, u, 0} (affineLine k) ℓ
      (exists_pow_eq_units_globalSections k hℓ0))
  have := subsingleton_sheafH_one_multiplicative_affineLine k
  exact hinj.subsingleton

/-- **`H²(𝐀¹, μ_ℓ) = 0`** for `ℓ` invertible in the algebraically closed field `k`. -/
theorem subsingleton_sheafH_two_rootsOfUnity_affineLine [IsAlgClosed k] (hℓ0 : 0 < ℓ)
    (hℓ : IsUnit (ℓ : k)) :
    Subsingleton (Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ) 2) :=
  Stacks.Kummer.subsingleton_sheafH_rootsOfUnitySheaf.{u + 1, u, 0} (affineLine k) hℓ0.ne'
    (isUnit_natCast_globalSections_of_over (affineLine k ↘ Spec (.of k)) hℓ) 1
    (subsingleton_sheafH_one_multiplicative_affineLine k)
    (subsingleton_sheafH_two_multiplicative_affineLine k)

/-- A counting lemma: if `δ : A → B` is onto with kernel the image of `pw : A → A`, and `A` is
identified with `Additive Sˣ` carrying `pw` to multiplication by `n`, then `#B = #(Sˣ / n)`. -/
theorem natCard_eq_of_surjective_of_ker_eq_range {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (δ : A →+ B) (hδ : Function.Surjective δ) (pw : A →+ A) (hker : δ.ker = pw.range)
    {S : Type*} [CommRing S] {n : ℕ} (E : A ≃+ Additive Sˣ) (hE : ∀ y, E (pw y) = n • E y) :
    Nat.card B = Nat.card (Additive Sˣ ⧸
      (nsmulAddMonoidHom n : Additive Sˣ →+ Additive Sˣ).range) := by
  have hmap : pw.range.map E.toAddMonoidHom =
      (nsmulAddMonoidHom n : Additive Sˣ →+ Additive Sˣ).range := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨E y, (hE y).symm⟩
    · rintro ⟨w, rfl⟩
      refine ⟨pw (E.symm w), ⟨E.symm w, rfl⟩, ?_⟩
      show E (pw (E.symm w)) = n • w
      rw [hE, AddEquiv.apply_symm_apply]
  let e : B ≃+ Additive Sˣ ⧸ (nsmulAddMonoidHom n : Additive Sˣ →+ Additive Sˣ).range :=
    ((QuotientAddGroup.quotientKerEquivOfSurjective δ hδ).symm.trans
      (QuotientAddGroup.quotientAddEquivOfEq hker)).trans
      (QuotientAddGroup.congr _ _ E hmap)
  exact Nat.card_congr e.toEquiv

/-- The identification behind `natCard_eq_of_surjective_of_ker_eq_range`: if `δ : A → B` is onto
with kernel the image of `pw : A → A`, and `A ≃ Additive Sˣ` carries `pw` to multiplication by
`n`, then `B ≃ Sˣ / n`. -/
def addEquivQuotientOfSurjectiveOfKerEqRange {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (δ : A →+ B) (hδ : Function.Surjective δ) (pw : A →+ A) (hker : δ.ker = pw.range)
    {S : Type*} [CommRing S] {n : ℕ} (E : A ≃+ Additive Sˣ) (hE : ∀ y, E (pw y) = n • E y) :
    B ≃+ Additive Sˣ ⧸ (nsmulAddMonoidHom n : Additive Sˣ →+ Additive Sˣ).range :=
  ((QuotientAddGroup.quotientKerEquivOfSurjective δ hδ).symm.trans
      (QuotientAddGroup.quotientAddEquivOfEq hker)).trans
      (QuotientAddGroup.congr _ _ E (by
        ext z
        constructor
        · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
          exact ⟨E y, (hE y).symm⟩
        · rintro ⟨w, rfl⟩
          refine ⟨pw (E.symm w), ⟨E.symm w, rfl⟩, ?_⟩
          change E (pw (E.symm w)) = n • w
          rw [hE, AddEquiv.apply_symm_apply]))

/-- **`H¹(𝐆_m, μ_ℓ) ≅ ℤ/ℓ`** for `ℓ` invertible in the algebraically closed field `k`, the
Kummer class of the coordinate going to `1`: by the Kummer sequence and `Pic(𝐆_m) = 0` it is
`k[t, t⁻¹]^× / ℓ`, generated by `t`. -/
def sheafHOneRootsOfUnityPuncturedEquiv [IsAlgClosed k] (hℓ0 : 0 < ℓ) (hℓ : IsUnit (ℓ : k)) :
    Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured k).toScheme ℓ) 1 ≃+
      ZMod ℓ := by
  set P := (punctured k).toScheme
  have hX : IsUnit ((ℓ : ℕ) : Γ(P, ⊤)) :=
    isUnit_natCast_globalSections_of_over ((punctured k).ι ≫ (affineLine k ↘ Spec (.of k))) hℓ
  let δ := Stacks.Kummer.kummerδ.{u + 1, u, 0} P hℓ0.ne' hX 0
  haveI := subsingleton_sheafH_one_multiplicative_punctured k
  have hδsurj : Function.Surjective δ := fun x =>
    (Stacks.Kummer.mem_range_kummerδ_iff.{u + 1, u, 0} P hℓ0.ne' hX 0 x).2
      (Subsingleton.elim _ _)
  let pw := Sheaf.H.map.{u + 1} (Stacks.Kummer.powMap.{u, 0} P ℓ) 0
  have hker : δ.ker = pw.range := by
    ext x
    exact (Stacks.Kummer.mem_range_sheafH_map_powMap_iff.{u + 1, u, 0} P hℓ0.ne' hX 0 x).symm
  letI : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 P)) := MorphismProperty.Over.mkIdTerminal _ _
  let E : Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, 0} P) 0 ≃+
      Additive (Γ(P, ⊤))ˣ :=
    (Sheaf.H.equiv₀ (Stacks.Kummer.multiplicativeSheaf.{u, 0} P) hT).trans AddEquiv.ulift
  have hE : ∀ y, E (pw y) = ℓ • E y := by
    intro y
    obtain ⟨a, ha⟩ := Stacks.Kummer.ofUnit_surjective
      (Sheaf.H.equiv₀ (Stacks.Kummer.multiplicativeSheaf.{u, 0} P) hT y)
    change (Sheaf.H.equiv₀ _ hT (pw y)).down = ℓ • (Sheaf.H.equiv₀ _ hT y).down
    rw [← Sheaf.H.equiv₀_naturality, ← ha, Stacks.Kummer.powMap_app_ofUnit]
    change Additive.ofMul (a ^ ℓ) = ℓ • Additive.ofMul a
    rw [ofMul_pow]
  let : Algebra Γ(affineLine k, ⊤) Γ(P, ⊤) := (punctured k).ι.appTop.hom.toAlgebra
  have : IsLocalization.Away (coordinate k) Γ(P, ⊤) :=
    Γ_restrict_isLocalization (affineLine k) (coordinate k)
  exact (addEquivQuotientOfSurjectiveOfKerEqRange δ hδsurj pw hker E hE).trans
    (Stacks.LocalizationAway.quotientRangeNsmulUnitsAwayEquiv (prime_coordinate k) Γ(P, ⊤) ℓ
      (exists_pow_eq_units_globalSections k hℓ0))

/-- **`H¹(𝐆_m, μ_ℓ)` has exactly `ℓ` elements** for `ℓ` invertible in the algebraically closed
field `k`: by the Kummer sequence and `Pic(𝐆_m) = 0` it is `k[t, t⁻¹]^× / ℓ ≅ ℤ/ℓ`. -/
theorem natCard_sheafH_one_rootsOfUnity_punctured [IsAlgClosed k] (hℓ0 : 0 < ℓ)
    (hℓ : IsUnit (ℓ : k)) :
    Nat.card (Sheaf.H.{u + 1}
      (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured k).toScheme ℓ) 1) = ℓ :=
  (Nat.card_congr (sheafHOneRootsOfUnityPuncturedEquiv k hℓ0 hℓ).toEquiv).trans (Nat.card_zmod ℓ)

end Stacks.EtaleCohomology.Purity

end
