module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineSkyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections

/-!
# Higher direct images of `ℤ/ℓ` along the complement of a principal smooth divisor

Let `k` be an algebraically closed field, `ℓ ≥ 1` an integer invertible in `k`, `φ : X ⟶ 𝐀¹_k` a
smooth morphism, `T ⟶ X` its fibre over the origin and `h : V = φ⁻¹(𝐆_m) ⟶ X` the open
complement. By smooth base change (Stacks 0EYU) along `φ` the higher direct images of `ℤ/ℓ` along
`h` are the inverse images along `φ` of those along `𝐆_m ⟶ 𝐀¹`, which are `ℤ/ℓ`, the skyscraper
`ℤ/ℓ` at the origin, and zero. Hence

* `h_* (ℤ/ℓ)_V ≅ (ℤ/ℓ)_X`,
* `R¹h_* (ℤ/ℓ)_V ≅ i_* (ℤ/ℓ)_T`,
* `R^q h_* (ℤ/ℓ)_V = 0` for `q ≥ 2`,

as abelian sheaves on `X_étale`. This is cohomological purity for the principal smooth divisor
`T = φ⁻¹(0)` (SGA 4 XVI 3.7, Milne, *Lectures on étale cohomology* §16), in its local form.

## Main results

* `Stacks.EtaleCohomology.Purity.isZero_rightDerived_complement_constant`:
  `R^q h_* (ℤ/ℓ)_V = 0` for `q ≥ 2`.
* `Stacks.EtaleCohomology.Purity.nonempty_directImage_complement_constant_iso`:
  `h_* (ℤ/ℓ)_V ≅ (ℤ/ℓ)_X`.
* `Stacks.EtaleCohomology.Purity.nonempty_rightDerived_one_complement_constant_iso`:
  `R¹h_* (ℤ/ℓ)_V ≅ i_* (ℤ/ℓ)_T`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.Purity

variable {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} (hℓ : IsUnit (ℓ : k))
  {X T : Scheme.{u}} (φ : X ⟶ affineLine k) [Smooth φ] (i : T ⟶ X) [IsClosedImmersion i]
  (ψ : T ⟶ Spec (.of k)) (hT : IsPullback i ψ φ (origin k))

/-- The open complement `φ⁻¹(𝐆_m)` of the principal divisor `φ⁻¹(0)`. -/
abbrev complementOpen : X.Opens := φ ⁻¹ᵁ punctured k

omit [IsAlgClosed k] [Smooth φ] [IsClosedImmersion i] in
include hT in
/-- The open `φ⁻¹(𝐆_m)` is the complement of the divisor `φ⁻¹(0)`. -/
theorem range_complementOpen_ι :
    Set.range (complementOpen φ).ι.base = (Set.range i.base)ᶜ := by
  have hi : Set.range i.base = φ.base ⁻¹' Set.range (origin k).base := by
    rw [← hT.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      ← Scheme.Pullback.range_fst]
    exact Function.Surjective.range_comp (Scheme.homeoOfIso hT.isoPullback).surjective _
  rw [hi, range_origin, Scheme.Opens.range_ι, Set.preimage_compl, compl_compl]
  rfl

omit [IsAlgClosed k] [Smooth φ] in
/-- The base change square of `𝐆_m ⟶ 𝐀¹` along `φ`. -/
theorem isPullback_complementOpen :
    IsPullback (complementOpen φ).ι (φ ∣_ punctured k) φ (punctured k).ι :=
  (isPullback_morphismRestrict φ (punctured k)).flip

/-- The open immersion `φ⁻¹(𝐆_m) ⟶ X` is quasi-compact. -/
instance quasiCompact_complementOpen_ι : QuasiCompact (complementOpen φ).ι :=
  MorphismProperty.of_isPullback (isPullback_complementOpen φ).flip inferInstance

/-- A natural number that is a unit in a field is positive. -/
private theorem pos_of_isUnit_natCast {k : Type*} [Field k] {ℓ : ℕ} (hℓ : IsUnit (ℓ : k)) :
    0 < ℓ :=
  Nat.pos_of_ne_zero fun h => hℓ.ne_zero (by rw [h, Nat.cast_zero])

omit [IsAlgClosed k] in
/-- `j⁻¹ μ_ℓ` is killed by `ℓ`. -/
theorem nsmul_id_rootsOfUnityPunctured (k : Type u) [Field k] :
    ℓ • 𝟙 (rootsOfUnityPunctured k (ℓ := ℓ)) = 0 := by
  have hμ : ℓ • 𝟙 (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ) = 0 := by
    rw [← cancel_mono (Stacks.Kummer.rootsOfUnityι.{u, 0} (affineLine k) ℓ), Preadditive.nsmul_comp,
      Category.id_comp, zero_comp]
    have := Stacks.Kummer.rootsOfUnityι_comp_powMap.{u, 0} (affineLine k) ℓ
    simpa [Stacks.Kummer.powMap, Preadditive.comp_nsmul] using this
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hμ, Functor.map_zero]

omit [IsAlgClosed k] in
include hℓ in
/-- The torsion hypothesis of smooth base change for `j⁻¹ μ_ℓ`. -/
theorem torsion_rootsOfUnityPunctured (t : GeometricPoint (punctured k).toScheme)
    (a : (smallEtaleStalkAb t.hom).obj (rootsOfUnityPunctured k (ℓ := ℓ))) :
    ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(affineLine k, ⊤)) ∧ n • a = 0 :=
  ⟨ℓ, pos_of_isUnit_natCast hℓ, by
    exact_mod_cast isUnit_natCast_globalSections_of_over (affineLine k ↘ Spec (.of k)) hℓ,
    nsmul_eq_zero_stalk_rootsOfUnityPunctured k t a⟩

include hℓ in
/-- **Smooth base change** along `φ` for `j⁻¹ μ_ℓ`. -/
def complementBaseChangeIso (q : ℕ) :
    (smallEtalePullbackAb φ).obj (((smallEtalePushforwardAb (punctured k).ι).rightDerived q).obj
        (rootsOfUnityPunctured k (ℓ := ℓ))) ≅
      ((smallEtalePushforwardAb (complementOpen φ).ι).rightDerived q).obj
        ((smallEtalePullbackAb (φ ∣_ punctured k)).obj (rootsOfUnityPunctured k (ℓ := ℓ))) :=
  haveI : IsSeparated (punctured k).ι := IsSeparated.isSeparated_of_mono _
  haveI : QuasiSeparated (punctured k).ι := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  haveI := SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth φ (complementOpen φ).ι
    (φ ∣_ punctured k) (punctured k).ι (isPullback_complementOpen φ)
    (rootsOfUnityPunctured k (ℓ := ℓ)) (torsion_rootsOfUnityPunctured hℓ) q
  asIso ((higherBaseChangeMapAb φ (punctured k).ι (complementOpen φ).ι (φ ∣_ punctured k)
    (isPullback_complementOpen φ).w q).app _)

omit [IsAlgClosed k] [Smooth φ] in
include hℓ in
/-- `μ_ℓ ≅ ℤ/ℓ` on a scheme over `k`, through a choice of a primitive root of unity. -/
theorem nonempty_rootsOfUnity_iso_constant' [IsSepClosed k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (hℓ0 : ℓ ≠ 0) :
    Nonempty (etaleConstantSheaf Y (ZMod ℓ) ≅ Stacks.Kummer.rootsOfUnitySheaf.{u, 0} Y ℓ) := by
  classical
  exact Stacks.Kummer.nonempty_rootsOfUnity_iso_constant f hℓ0 hℓ.ne_zero

/-- The inverse image of a constant sheaf is constant. -/
def pullbackConstantIso {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Type) [AddCommGroup M] :
    (smallEtalePullbackAb f).obj (etaleConstantSheaf Z M) ≅ etaleConstantSheaf Y M :=
  (smallEtalePullbackAbConstantIso f).app _

omit [Smooth φ] in
include hℓ in
/-- `j⁻¹ μ_ℓ` pulled back to `φ⁻¹(𝐆_m)` is the constant sheaf `ℤ/ℓ`. -/
theorem nonempty_pullback_rootsOfUnityPunctured_iso :
    Nonempty ((smallEtalePullbackAb (φ ∣_ punctured k)).obj (rootsOfUnityPunctured k (ℓ := ℓ)) ≅
      etaleConstantSheaf (complementOpen φ).toScheme (ZMod ℓ)) := by
  obtain ⟨e⟩ := nonempty_rootsOfUnity_iso_constant' hℓ (affineLine k ↘ Spec (.of k))
    (pos_of_isUnit_natCast hℓ).ne'
  exact ⟨(smallEtalePullbackAb (φ ∣_ punctured k)).mapIso
    ((etaleRestriction.{u, 0} (punctured k).ι).mapIso e.symm ≪≫
      ((smallEtalePullbackAbIsoEtaleRestriction (punctured k).ι).app _).symm ≪≫
      pullbackConstantIso _ _) ≪≫ pullbackConstantIso _ _⟩

include hℓ in
/-- **`R^q h_* (ℤ/ℓ) = 0` for `q ≥ 2`** along the complement `h : φ⁻¹(𝐆_m) ⟶ X`. -/
theorem isZero_rightDerived_complement_constant (q : ℕ) (hq : 2 ≤ q) :
    IsZero (((smallEtalePushforwardAb (complementOpen φ).ι).rightDerived q).obj
      (etaleConstantSheaf (complementOpen φ).toScheme (ZMod ℓ))) := by
  obtain ⟨e⟩ := nonempty_pullback_rootsOfUnityPunctured_iso hℓ φ
  have hdim : topologicalKrullDim (punctured k).toScheme ≤ 1 :=
    (SmoothBaseChange.topologicalKrullDim_le_of_etale (punctured k).ι).trans
      (SmoothBaseChange.topologicalKrullDim_affineLine_spec k)
  have : IsAffineHom (punctured k).ι := isAffineHom_of_isAffine _
  have hz := isZero_rightDerived_pushforward_of_isAffineHom_of_dim_le_one k (punctured k).ι
    ((punctured k).ι ≫ (affineLine k ↘ Spec (.of k))) hdim (rootsOfUnityPunctured k (ℓ := ℓ))
    (fun V x => ⟨⊤, (punctured k).toScheme.smallEtaleTopology.top_mem _, fun W f _ => ⟨ℓ,
      pos_of_isUnit_natCast hℓ, by
        have h1 := (sheafToPresheaf _ _).map_nsmul (f := 𝟙 (rootsOfUnityPunctured k (ℓ := ℓ)))
          (n := ℓ)
        rw [nsmul_id_rootsOfUnityPunctured (ℓ := ℓ) k, Functor.map_zero,
          CategoryTheory.Functor.map_id] at h1
        have := congrArg (fun g => (g.app (op W)).hom
          ((rootsOfUnityPunctured k (ℓ := ℓ)).obj.map f.op x)) h1
        simpa [NatTrans.app_nsmul, AddCommGrpCat.hom_nsmul] using this.symm⟩⟩) q hq
  exact ((Functor.map_isZero (smallEtalePullbackAb φ) hz).of_iso
    (complementBaseChangeIso hℓ φ q).symm).of_iso
      (((smallEtalePushforwardAb (complementOpen φ).ι).rightDerived q).mapIso e.symm)

include hℓ in
/-- **`h_* (ℤ/ℓ) ≅ ℤ/ℓ`** along the complement `h : φ⁻¹(𝐆_m) ⟶ X`. -/
theorem nonempty_directImage_complement_constant_iso :
    Nonempty ((smallEtalePushforwardAb (complementOpen φ).ι).obj
      (etaleConstantSheaf (complementOpen φ).toScheme (ZMod ℓ)) ≅
        etaleConstantSheaf X (ZMod ℓ)) := by
  obtain ⟨e⟩ := nonempty_pullback_rootsOfUnityPunctured_iso hℓ φ
  obtain ⟨c⟩ := nonempty_rootsOfUnity_iso_constant' hℓ (affineLine k ↘ Spec (.of k))
    (pos_of_isUnit_natCast hℓ).ne'
  have hθ := isIso_rootsOfUnityUnit k
    (pos_of_isUnit_natCast hℓ) hℓ
  have : PreservesLimitsOfSize.{0, 0} (smallEtalePushforwardAb (complementOpen φ).ι) :=
    (smallEtaleAdjunctionAb (complementOpen φ).ι).rightAdjoint_preservesLimits
  have : PreservesLimitsOfSize.{0, 0} (smallEtalePushforwardAb (punctured k).ι) :=
    (smallEtaleAdjunctionAb (punctured k).ι).rightAdjoint_preservesLimits
  exact ⟨(smallEtalePushforwardAb (complementOpen φ).ι).mapIso e.symm ≪≫
    (Functor.rightDerivedZeroIsoSelf _).symm.app _ ≪≫ (complementBaseChangeIso hℓ φ 0).symm ≪≫
    (smallEtalePullbackAb φ).mapIso ((Functor.rightDerivedZeroIsoSelf _).app _ ≪≫
      (asIso (rootsOfUnityUnit k (ℓ := ℓ))).symm ≪≫ c.symm) ≪≫ pullbackConstantIso φ _⟩

omit [IsAlgClosed k] [Smooth φ] in
/-- The constant sheaf `ℤ/ℓ` is killed by `ℓ`, on every stalk. -/
theorem nsmul_eq_zero_stalk_constant {Y : Scheme.{u}} (t : GeometricPoint Y)
    (a : (smallEtaleStalkAb t.hom).obj (etaleConstantSheaf Y (ZMod ℓ))) : ℓ • a = 0 := by
  have h0 : ℓ • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) = 0 := by
    ext x
    simp [nsmul_eq_mul]
  have hF : ℓ • 𝟙 (etaleConstantSheaf Y (ZMod ℓ)) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, h0, Functor.map_zero]
  have := congrArg (fun f => ((smallEtaleStalkAb t.hom).map f) a) hF
  simpa [Functor.map_nsmul] using this

include hℓ hT in
/-- **`R¹h_* (ℤ/ℓ) ≅ i_* (ℤ/ℓ)`** along the complement `h : φ⁻¹(𝐆_m) ⟶ X` of the principal divisor
`i : T = φ⁻¹(0) ⟶ X`. -/
theorem nonempty_rightDerived_one_complement_constant_iso :
    Nonempty (((smallEtalePushforwardAb (complementOpen φ).ι).rightDerived 1).obj
        (etaleConstantSheaf (complementOpen φ).toScheme (ZMod ℓ)) ≅
      (etaleAbelianDirectImage.{u, 0} i).obj (etaleConstantSheaf T (ZMod ℓ))) := by
  obtain ⟨e⟩ := nonempty_pullback_rootsOfUnityPunctured_iso hℓ φ
  obtain ⟨s⟩ := nonempty_rightDerived_one_iso_origin k hℓ
  set R := ((smallEtalePushforwardAb (complementOpen φ).ι).rightDerived 1).obj
    (etaleConstantSheaf (complementOpen φ).toScheme (ZMod ℓ))
  let C := etaleConstantSheaf (Spec (.of k)) (ZMod ℓ)
  let eR : R ≅ (etaleAbelianInverseImage.{u, 0} φ).obj
      ((etaleAbelianDirectImage.{u, 0} (origin k)).obj C) :=
    ((smallEtalePushforwardAb (complementOpen φ).ι).rightDerived 1).mapIso e.symm ≪≫
      (complementBaseChangeIso hℓ φ 1).symm ≪≫ (smallEtalePullbackAb φ).mapIso s ≪≫
      (smallEtalePullbackAbIsoEtaleAbelianInverseImage φ).app _
  have hres : IsZero ((etaleRestriction.{u, 0} (complementOpen φ).ι).obj R) :=
    isZero_restriction_rightDerived_of_isOpenImmersion (complementOpen φ).ι _
      (fun t a => ⟨ℓ, pos_of_isUnit_natCast hℓ, by
        exact_mod_cast isUnit_natCast_globalSections_of_over (φ ≫ (affineLine k ↘ Spec (.of k))) hℓ,
        nsmul_eq_zero_stalk_constant t a⟩) 1 one_pos
  obtain ⟨hz, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} i
    (complementOpen φ).ι (range_complementOpen_ι φ i ψ hT) R
  have : Mono ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app R) :=
    hS.exact.mono_g
      ((Functor.map_isZero (extensionByZero.{u, 0} (complementOpen φ).ι) hres).eq_of_src _ _)
  have : Epi ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app R) := hS.epi_g
  have : IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app R) :=
    isIso_of_mono_of_epi _
  have hfo := (etaleAbelianDirectImageFullyFaithful.{u, 0} (origin k)).full
  have hfo' := (etaleAbelianDirectImageFullyFaithful.{u, 0} (origin k)).faithful
  let eT : (etaleAbelianInverseImage.{u, 0} i).obj R ≅ etaleConstantSheaf T (ZMod ℓ) :=
    (etaleAbelianInverseImage.{u, 0} i).mapIso eR ≪≫
      ((etaleAbelianInverseImageCompIso.{u, 0} i φ).app _).symm ≪≫
      eqToIso (by rw [hT.w]) ≪≫
      (etaleAbelianInverseImageCompIso.{u, 0} ψ (origin k)).app _ ≪≫
      (etaleAbelianInverseImage.{u, 0} ψ).mapIso
        (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (origin k)).counit.app C)) ≪≫
      ((smallEtalePullbackAbIsoEtaleAbelianInverseImage ψ).app _).symm ≪≫ pullbackConstantIso ψ _
  exact ⟨asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} i).unit.app R) ≪≫
    (etaleAbelianDirectImage.{u, 0} i).mapIso eT⟩

end Stacks.EtaleCohomology.Purity

end
