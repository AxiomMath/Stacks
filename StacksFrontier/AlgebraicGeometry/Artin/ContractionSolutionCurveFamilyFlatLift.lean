module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyFlatCompletion
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyFlatStalk
public import StacksFrontier.Deformation.Artin.Predeformation.FormallyEtale

/-!
# Truncations of the local rings of a chart at a point of the contracted locus

Let `s` be a solution of Artin's contraction problem of Stacks 0GH8 with target `X` over an
affine base `S`, with `W` identified with the completion of `Spec A` at its closed point for a
local `Γ(S)`-algebra `A`. For an étale chart `a : V ⟶ X` and a point `v ∈ V` over the contracted
locus `T`, this file builds, for every `n`, the map of `Γ(S)`-algebras
`θₙ : A ⧸ 𝔪_Aⁿ⁺¹ → 𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹` read off from `a : X_{/T} ≅ W` on the truncation
`Spec (𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹) ⟶ V ⟶ X`, together with the section `βₙ` of `X` over `Spec (A ⧸ 𝔪_Aⁿ⁺¹)`
corresponding to `Spec (A ⧸ 𝔪_Aⁿ⁺¹) ⟶ Spec A`, and proves that `βₙ` restricts along `Spec θₙ` to
the truncation of the chart.

## Main definitions

* `AlgebraicGeometry.Space.truncSpec`, `AlgebraicGeometry.Space.truncRes`: the spectra of the
  truncations `L ⧸ Iⁿ⁺¹` of a `Γ(S)`-algebra as objects of the site, and their restrictions.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.betaSection`: the section `βₙ`.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.truncTheta`: the map `θₙ`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_lift_truncSpec`: a formally étale morphism has unique
  lifts along `Spec (L ⧸ I) ⟶ Spec (L ⧸ Iⁿ⁺¹)`.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.map_truncTau_betaSection`: `βₙ`
  restricted along `Spec θₙ` is the truncation of the chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsAffine S]

/-- The spectrum of the truncation `L ⧸ Iⁿ⁺¹` of a `Γ(S)`-algebra `L`, as an object of the big
fppf site of `S`. -/
abbrev truncSpec {L : Type u} [CommRing L] [Algebra Γ(S, ⊤) L] (hL : B.Contains (Spec (.of L)))
    (I : Ideal L) (n : ℕ) : BigFppfOver B S hS :=
  specOver B S hS S.isoSpec.inv (L ⧸ I ^ (n + 1)) (contains_spec_quotient hL _)

omit [IsAffine S] in
/-- The spectrum of the local ring of an object of the site at a point lies in the site. -/
theorem contains_spec_stalk_toScheme (V : BigFppfOver B S hS)
    (v : (BigFppfOver.toScheme B S hS).obj V) :
    B.Contains (Spec (.of (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v))) :=
  B.contains_spec_stalk_of_contains V.left.property v

/-- The restriction `Spec (L ⧸ Iᵐ⁺¹) ⟶ Spec (L ⧸ Iⁿ⁺¹)` for `m ≤ n`. -/
def truncRes {L : Type u} [CommRing L] [Algebra Γ(S, ⊤) L] (hL : B.Contains (Spec (.of L)))
    (I : Ideal L) {m n : ℕ} (h : m ≤ n) :
    truncSpec (S := S) (hS := hS) hL I m ⟶ truncSpec hL I n :=
  specOverHom B S hS S.isoSpec.inv _ _
    (Ideal.Quotient.factorₐ Γ(S, ⊤) (Ideal.pow_le_pow_right (Nat.succ_le_succ h)))

/-- The restrictions between truncations compose. -/
theorem truncRes_comp {L : Type u} [CommRing L] [Algebra Γ(S, ⊤) L]
    (hL : B.Contains (Spec (.of L))) (I : Ideal L) {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) :
    truncRes (S := S) (hS := hS) hL I h₁ ≫ truncRes hL I h₂ = truncRes hL I (h₁.trans h₂) := by
  rw [truncRes, truncRes, specOverHom_comp]
  apply specOverHom_congr
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The restriction from a truncation to itself is the identity. -/
@[simp]
theorem truncRes_self {L : Type u} [CommRing L] [Algebra Γ(S, ⊤) L]
    (hL : B.Contains (Spec (.of L))) (I : Ideal L) (n : ℕ) :
    truncRes (S := S) (hS := hS) hL I (le_refl n) = 𝟙 _ := by
  rw [truncRes, ← specOverHom_id]
  apply specOverHom_congr
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- **Unique lifts along the truncations.** A formally étale morphism `a : F ⟶ G` has exactly one
lift in every square over the restriction `Spec (L ⧸ I) ⟶ Spec (L ⧸ Iⁿ⁺¹)`: its kernel
`I / Iⁿ⁺¹` is nilpotent. -/
theorem existsUnique_lift_truncSpec {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : FormallyEtale a) {L : Type u} [CommRing L] [Algebra Γ(S, ⊤) L]
    (hL : B.Contains (Spec (.of L))) (I : Ideal L) (n : ℕ)
    (x₀ : F.obj (op (truncSpec hL I 0))) (y : G.obj (op (truncSpec hL I n)))
    (hy : G.map (truncRes hL I (Nat.zero_le n)).op y = a.app _ x₀) :
    ∃! x : F.obj (op (truncSpec hL I n)),
      F.map (truncRes hL I (Nat.zero_le n)).op x = x₀ ∧ a.app _ x = y := by
  let : Algebra (L ⧸ I ^ (n + 1)) (L ⧸ I ^ (0 + 1)) :=
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)))).toAlgebra
  have : IsScalarTower Γ(S, ⊤) (L ⧸ I ^ (n + 1)) (L ⧸ I ^ (0 + 1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hres : truncRes (S := S) (hS := hS) hL I (Nat.zero_le n) =
      specOverHom B S hS S.isoSpec.inv _ _
        (IsScalarTower.toAlgHom Γ(S, ⊤) (L ⧸ I ^ (n + 1)) (L ⧸ I ^ (0 + 1))) :=
    specOverHom_congr (AlgHom.ext fun _ => rfl)
  have hker : RingHom.ker (algebraMap (L ⧸ I ^ (n + 1)) (L ⧸ I ^ (0 + 1))) ^ (n + 1) = ⊥ := by
    change RingHom.ker (Ideal.Quotient.factor _) ^ (n + 1) = ⊥
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
    change Ideal.map _ ((I ^ 1) ^ (n + 1)) = ⊥
    rw [pow_one, Ideal.map_quotient_self]
  rw [hres] at hy ⊢
  exact existsUnique_lift_specOverHom_of_isNilpotent a ha S.isoSpec.inv (n + 1)
    (Ideal.Quotient.factor_surjective _) hker _ _ x₀ y hy

end Space

namespace Artin.ContractionSituation.Solution

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsAffine S]
    {c : ContractionSituation B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (s : Solution c X) {A : Type u} [CommRing A] [IsLocalRing A] [Algebra Γ(S, ⊤) A]
    {hA : B.Contains (Spec (.of A))}
    (eW : c.W ≅ Space.completionSheaf B S hS
      (yoneda.obj (Space.specOver B S hS S.isoSpec.inv A hA))
      {(Space.schemePointsHomeomorph B S hS (Space.specOver B S hS S.isoSpec.inv A hA)).symm
        (IsLocalRing.closedPoint A)})

/-! ### The sections `βₙ` over the truncations of `A` -/

/-- The morphism `Spec (A ⧸ 𝔪_Aⁿ⁺¹) ⟶ Spec A` of the site. -/
def truncToP (hA : B.Contains (Spec (.of A))) (n : ℕ) :
    Space.truncSpec (S := S) (hS := hS) hA (maximalIdeal A) n ⟶
      Space.specOver B S hS S.isoSpec.inv A hA :=
  Space.specOverHom B S hS S.isoSpec.inv hA _ (Ideal.Quotient.mkₐ Γ(S, ⊤) _)

/-- `Spec (A ⧸ 𝔪_Aⁿ⁺¹) ⟶ Spec A` has point-set image the closed point. -/
theorem hasImageIn_truncToP (hA : B.Contains (Spec (.of A))) (n : ℕ) :
    Space.HasImageIn B S hS (yoneda.obj (Space.specOver B S hS S.isoSpec.inv A hA))
      {(Space.schemePointsHomeomorph B S hS (Space.specOver B S hS S.isoSpec.inv A hA)).symm
        (IsLocalRing.closedPoint A)} _
      (truncToP hA n) :=
  (Space.hasImageIn_yoneda_iff_range_eq _ _).2 fun y => SpecMap_quotient_mk_apply n y

/-- The restrictions of `Spec (A ⧸ 𝔪_Aⁿ⁺¹) ⟶ Spec A` are the morphisms of the smaller
truncations. -/
theorem truncRes_comp_truncToP (hA : B.Contains (Spec (.of A))) {m n : ℕ} (h : m ≤ n) :
    Space.truncRes hA (maximalIdeal A) h ≫ truncToP (S := S) (hS := hS) hA n =
      truncToP hA m := by
  rw [truncToP, truncToP, Space.truncRes, Space.specOverHom_comp]
  rfl

/-- The section `βₙ` of `X` over `Spec (A ⧸ 𝔪_Aⁿ⁺¹)` corresponding, under `X_{/T} ≅ W`, to the
morphism `Spec (A ⧸ 𝔪_Aⁿ⁺¹) ⟶ Spec A`. -/
def betaSection (n : ℕ) : X.obj (op (Space.truncSpec hA (maximalIdeal A) n)) :=
  ((s.completionEquiv eW _).symm ⟨truncToP hA n, hasImageIn_truncToP hA n⟩).1

/-- The sections `βₙ` are compatible with the restrictions. -/
theorem map_truncRes_betaSection {m n : ℕ} (h : m ≤ n) :
    X.map (Space.truncRes hA (maximalIdeal A) h).op (s.betaSection eW n) =
      s.betaSection eW m := by
  rw [betaSection, ← s.completionEquiv_symm_map eW (Space.truncRes hA (maximalIdeal A) h)
    ⟨truncToP hA n, hasImageIn_truncToP hA n⟩
    (by rw [truncRes_comp_truncToP]; exact hasImageIn_truncToP hA m)]
  exact congrArg (fun z => ((s.completionEquiv eW _).symm z).1)
    (Subtype.ext (truncRes_comp_truncToP hA h))

/-! ### The maps `θₙ` read off on the truncations of a chart -/

section Chart

variable {V : BigFppfOver B S hS} (a : yoneda.obj V ⟶ X)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    [Algebra Γ(S, ⊤) (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)]
    (hR : algebraMap Γ(S, ⊤) (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) =
      (Space.chartStalkStructureMap V v).hom)

/-- The spectrum of the truncation `𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹`, as an object of the site. -/
abbrev truncY (n : ℕ) : BigFppfOver B S hS :=
  Space.truncSpec (Space.contains_spec_stalk_toScheme V v)
    (maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)) n

include hR in
/-- The truncation `Spec (𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹) ⟶ V`, as a morphism of the site. -/
def truncCan (n : ℕ) : truncY v n ⟶ V :=
  Space.homOfSpec
    (L := ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v ⧸
      maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (n + 1)) V
    (Space.contains_spec_quotient (Space.contains_spec_stalk_toScheme V v) _)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (n + 1)))) ≫
      ((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v) (by
    rw [Category.assoc, Space.fromSpecStalk_comp_str, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    change _ = Ideal.Quotient.mk _ (algebraMap _ _ x)
    rw [hR]
    rfl)

/-- The truncation `Spec (𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹) ⟶ V` is constant with value `v`. -/
theorem toScheme_map_truncCan_apply (n : ℕ)
    (y : (BigFppfOver.toScheme B S hS).obj (truncY v n)) :
    (BigFppfOver.toScheme B S hS).map (truncCan v hR n) y = v := by
  rw [truncCan, Space.toScheme_map_homOfSpec, Scheme.Hom.comp_apply, SpecMap_quotient_mk_apply,
    Scheme.fromSpecStalk_closedPoint]

variable {v}
variable (hv : Space.pointsMap B S hS (yoneda.obj V) a
  ((Space.schemePointsHomeomorph B S hS V).symm v) ∈ s.T)

include hv in
/-- The truncation of a chart at a point over `T` has point-set image in `T`. -/
theorem hasImageIn_truncCan (n : ℕ) :
    Space.HasImageIn B S hS X s.T _ (a.app _ (truncCan v hR n)) :=
  Space.hasImageIn_app_of_forall_eq a _ v (toScheme_map_truncCan_apply v hR n) hv

/-- The map of `Γ(S)`-algebras `A → 𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹` corresponding, under `X_{/T} ≅ W`, to the
truncation of the chart. -/
def thetaHom (n : ℕ) :
    A →ₐ[Γ(S, ⊤)] ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v ⧸
      maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (n + 1) :=
  (Space.exists_specOverHom_eq
    (s.completionEquiv eW _ ⟨a.app _ (truncCan v hR n), s.hasImageIn_truncCan a hR hv n⟩).1).choose

/-- `Spec` of `thetaHom` is the morphism to `Spec A` read off from the truncation. -/
theorem specOverHom_thetaHom (n : ℕ) :
    Space.specOverHom B S hS S.isoSpec.inv hA _ (s.thetaHom eW a hR hv n) =
      (s.completionEquiv eW _ ⟨a.app _ (truncCan v hR n), s.hasImageIn_truncCan a hR hv n⟩).1 :=
  (Space.exists_specOverHom_eq _).choose_spec

/-- `thetaHom` is a local map. -/
theorem isLocalHom_thetaHom (n : ℕ) : IsLocalHom (s.thetaHom eW a hR hv n).toRingHom := by
  have h := (s.completionEquiv eW _ ⟨a.app _ (truncCan v hR n), s.hasImageIn_truncCan a hR hv n⟩).2
  rw [← s.specOverHom_thetaHom eW a hR hv n] at h
  rw [isLocalHom_iff_comap_closedPoint]
  exact (Space.hasImageIn_yoneda_iff_range_eq _ _).1 h (closedPoint _)

/-- The map of `Γ(S)`-algebras `θₙ : A ⧸ 𝔪_Aⁿ⁺¹ → 𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹`. -/
def truncTheta (n : ℕ) :
    A ⧸ maximalIdeal A ^ (n + 1) →ₐ[Γ(S, ⊤)]
      ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v ⧸
        maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (n + 1) :=
  haveI := s.isLocalHom_thetaHom eW a hR hv n
  Ideal.Quotient.liftₐ _ (s.thetaHom eW a hR hv n)
    fun _ hx => map_eq_zero_of_mem_maximalIdeal_pow n (s.thetaHom eW a hR hv n).toRingHom hx

/-- `Spec θₙ : Spec (𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹) ⟶ Spec (A ⧸ 𝔪_Aⁿ⁺¹)`, as a morphism of the site. -/
def truncTau (n : ℕ) : truncY v n ⟶ Space.truncSpec hA (maximalIdeal A) n :=
  Space.specOverHom B S hS S.isoSpec.inv _ _ (s.truncTheta eW a hR hv n)

/-- `Spec θₙ` followed by `Spec (A ⧸ 𝔪_Aⁿ⁺¹) ⟶ Spec A` is the morphism read off from the
truncation of the chart. -/
theorem truncTau_comp_truncToP (n : ℕ) :
    s.truncTau eW a hR hv n ≫ truncToP hA n =
      (s.completionEquiv eW _ ⟨a.app _ (truncCan v hR n), s.hasImageIn_truncCan a hR hv n⟩).1 := by
  rw [truncTau, truncToP, Space.specOverHom_comp, ← s.specOverHom_thetaHom eW a hR hv n]
  exact Space.specOverHom_congr (Ideal.Quotient.liftₐ_comp _ _ _)

/-- **`βₙ` restricts along `Spec θₙ` to the truncation of the chart.** Both have the same image
`Spec (𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹) ⟶ Spec A` under `X_{/T} ≅ W`. -/
theorem map_truncTau_betaSection (n : ℕ) :
    X.map (s.truncTau eW a hR hv n).op (s.betaSection eW n) = a.app _ (truncCan v hR n) := by
  have hβ : Space.HasImageIn B S hS X s.T _ (s.betaSection eW n) :=
    ((s.completionEquiv eW _).symm ⟨truncToP hA n, hasImageIn_truncToP hA n⟩).2
  have hβ' : Space.HasImageIn B S hS X s.T _
      (X.map (s.truncTau eW a hR hv n).op (s.betaSection eW n)) :=
    (Space.completionSubfunctor B S hS X s.T).map (s.truncTau eW a hR hv n).op hβ
  have h1 := s.completionEquiv_map eW (s.truncTau eW a hR hv n) ⟨_, hβ⟩ hβ'
  have h2 : s.completionEquiv eW _ ⟨s.betaSection eW n, hβ⟩ =
      ⟨truncToP hA n, hasImageIn_truncToP hA n⟩ :=
    (s.completionEquiv eW _).apply_symm_apply _
  rw [h2] at h1
  change _ = s.truncTau eW a hR hv n ≫ truncToP hA n at h1
  rw [s.truncTau_comp_truncToP eW a hR hv n] at h1
  exact congrArg Subtype.val ((s.completionEquiv eW _).injective (Subtype.ext h1))

end Chart

end Artin.ContractionSituation.Solution

end AlgebraicGeometry

end
