module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreCurve
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreCurveCounterexample.Algebra

/-!
# Bounded ramification in the normalization of a curve in a finite extension

Let `S` be an integral scheme, `U` a nonempty affine open of `S` whose ring of sections `A` is a
Nagata Dedekind domain, `τ ∈ A` a nonzero generator of a maximal ideal, and `T` the
normalization of `S` in a finite extension `L` of its function field `K`. At every point `b` of
`T` over `U` where `τ` vanishes, the germ of `τ` does not lie in the `([L : K] + 1)`-st power of
the maximal ideal of `𝒪_{T,b}`: the local ring is a localization of the integral closure of `A`
in `L`, where the ramification index is at most `[L : K]`.

## Main results

* `AlgebraicGeometry.ReducedFibreCurveCounterexample.germ_notMem_maximalIdeal_pow`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.ReducedFibreCurveCounterexample

variable {S : Scheme.{u}} [IsIntegral S] {L : Type u} [Field L] [Algebra S.functionField L]

/-- The germ at a point of the normalization `T` of `S` in `Spec L` lying over the image of a
prime `q` of the integral closure `B` of `Γ(S, U)` in `L`, read in `B_q`: the germ of a section
`τ` of `S` over `U` is the image of `τ` in `B_q`. -/
theorem exists_ringEquiv_stalk_genericExtensionHom_normalization (U : S.Opens)
    (hU : IsAffineOpen U) [Nonempty U] (b : (S.genericExtensionHom L).normalization)
    (hb : b ∈ (S.genericExtensionHom L).fromNormalization ⁻¹ᵁ U) :
    letI : Algebra Γ(S, U) L :=
      ((algebraMap S.functionField L).comp (algebraMap Γ(S, U) S.functionField)).toAlgebra
    ∃ (q : Ideal (integralClosure Γ(S, U) L)) (_ : q.IsPrime)
      (e : (S.genericExtensionHom L).normalization.presheaf.stalk b ≃+* Localization.AtPrime q),
      ∀ τ : Γ(S, U), e ((S.genericExtensionHom L).normalization.presheaf.germ
        ((S.genericExtensionHom L).fromNormalization ⁻¹ᵁ U) b hb
          ((S.genericExtensionHom L).fromNormalization.app U τ)) =
        algebraMap Γ(S, U) (Localization.AtPrime q) τ := by
  let : Algebra Γ(S, U) L :=
    ((algebraMap S.functionField L).comp (algebraMap Γ(S, U) S.functionField)).toAlgebra
  obtain ⟨ψ, hψ⟩ := Scheme.exists_isPullback_genericExtensionHom_fromNormalization (L := L) U hU
  have : IsOpenImmersion ψ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hψ.flip inferInstance
  set π := (S.genericExtensionHom L).fromNormalization
  set φ := CommRingCat.ofHom (algebraMap Γ(S, U) ↥(integralClosure Γ(S, U) L))
  -- `b` comes from a prime `q` of the integral closure
  have hb' : π b ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hb
  obtain ⟨a, ha⟩ := hb'
  obtain ⟨q, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hψ b a ha.symm
  refine ⟨q.asIdeal, q.isPrime,
    ((asIso (ψ.stalkMap q)).commRingCatIsoToRingEquiv).trans
      (Spec.stalkIso _ q).commRingCatIsoToRingEquiv, fun τ ↦ ?_⟩
  have := q.isPrime
  have hb' : ψ q ∈ π ⁻¹ᵁ U := hb
  have hb'' : q ∈ (ψ ≫ π) ⁻¹ᵁ U := hb
  -- germs of sections pulled back along two equal morphisms agree
  have key : ∀ (F G : Spec (.of ↥(integralClosure Γ(S, U) L)) ⟶ S) (_ : F = G)
      (hF : q ∈ F ⁻¹ᵁ U) (hG : q ∈ G ⁻¹ᵁ U), F.app U ≫ (Spec _).presheaf.germ (F ⁻¹ᵁ U) q hF =
        G.app U ≫ (Spec _).presheaf.germ (G ⁻¹ᵁ U) q hG := by
    rintro F G rfl hF hG
    rfl
  have hq : q ∈ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
    change (Spec.map φ ≫ hU.fromSpec) q ∈ U
    rw [← hψ.w]
    exact hb
  have hF : π.app U ≫ (S.genericExtensionHom L).normalization.presheaf.germ (π ⁻¹ᵁ U) (ψ q) hb' ≫
      ψ.stalkMap q = φ ≫ (Scheme.ΓSpecIso _).inv ≫
        (Spec _).presheaf.germ ⊤ q (show q ∈ (⊤ : (Spec _).Opens) from trivial) := by
    rw [Scheme.Hom.germ_stalkMap, ← Category.assoc (π.app U) (ψ.app _)]
    change (ψ ≫ π).app U ≫ (Spec _).presheaf.germ ((ψ ≫ π) ⁻¹ᵁ U) q hb'' = _
    rw [key (ψ ≫ π) (Spec.map φ ≫ hU.fromSpec) hψ.w hb'' hq]
    have hq' : q ∈ Spec.map φ ⁻¹ᵁ hU.fromSpec ⁻¹ᵁ U := hq
    change hU.fromSpec.app U ≫ (Spec.map φ).app _ ≫
      (Spec _).presheaf.germ (Spec.map φ ⁻¹ᵁ hU.fromSpec ⁻¹ᵁ U) q hq' = _
    rw [hU.fromSpec_app_self, Category.assoc, Scheme.Hom.naturality_assoc,
      TopCat.Presheaf.germ_res', ← Category.assoc]
    change ((Scheme.ΓSpecIso _).inv ≫ (Spec.map φ).appTop) ≫
      (Spec _).presheaf.germ ⊤ q (show q ∈ (⊤ : (Spec _).Opens) from trivial) = _
    rw [← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have hG := Spec.germ_stalkMapIso_hom (R := .of ↥(integralClosure Γ(S, U) L)) (x := q)
  have h1 := ConcreteCategory.congr_hom hF τ
  have h2 := ConcreteCategory.congr_hom hG ((Scheme.ΓSpecIso _).inv (φ τ))
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at h1 h2
  change (Spec.stalkIso _ q).hom (ψ.stalkMap q
    ((S.genericExtensionHom L).normalization.presheaf.germ (π ⁻¹ᵁ U) (ψ q) hb' (π.app U τ))) = _
  rw [h1, h2]
  rfl

/-- **Bounded ramification in the normalization of a curve.** Let `U` be a nonempty affine open of
`S` whose ring of sections is a Nagata Dedekind domain, and let `τ` be a nonzero section over `U`
generating a maximal ideal. At a point `b` of the normalization of `S` in `Spec L` over `U`
where `τ` vanishes, the germ of `τ` does not lie in the `([L : K] + 1)`-st power of the maximal
ideal of the local ring. -/
theorem germ_notMem_maximalIdeal_pow [FiniteDimensional S.functionField L] (U : S.Opens)
    (hU : IsAffineOpen U) [Nonempty U] (hded : IsDedekindDomain Γ(S, U))
    (hA : IsNagataRing Γ(S, U)) {τ : Γ(S, U)} (hτ0 : τ ≠ 0) (hτ : (Ideal.span {τ}).IsMaximal)
    (b : (S.genericExtensionHom L).normalization)
    (hb : b ∈ (S.genericExtensionHom L).fromNormalization ⁻¹ᵁ U)
    (hτb : (S.genericExtensionHom L).normalization.presheaf.germ
        ((S.genericExtensionHom L).fromNormalization ⁻¹ᵁ U) b hb
          ((S.genericExtensionHom L).fromNormalization.app U τ) ∈
      maximalIdeal ((S.genericExtensionHom L).normalization.presheaf.stalk b)) :
    (S.genericExtensionHom L).normalization.presheaf.germ
        ((S.genericExtensionHom L).fromNormalization ⁻¹ᵁ U) b hb
          ((S.genericExtensionHom L).fromNormalization.app U τ) ∉
      maximalIdeal ((S.genericExtensionHom L).normalization.presheaf.stalk b) ^
        (Module.finrank S.functionField L + 1) := by
  let : Algebra Γ(S, U) L :=
    ((algebraMap S.functionField L).comp (algebraMap Γ(S, U) S.functionField)).toAlgebra
  have := functionField_isFractionRing_of_isAffineOpen S U hU
  have : IsScalarTower Γ(S, U) S.functionField L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨q, hq, e, he⟩ := exists_ringEquiv_stalk_genericExtensionHom_normalization U hU b hb
  have hmax : (maximalIdeal ((S.genericExtensionHom L).normalization.presheaf.stalk b)).map
      (e : _ →+* Localization.AtPrime q) = maximalIdeal (Localization.AtPrime q) :=
    map_ringEquiv_maximalIdeal e
  intro hmem
  have h1 := Ideal.mem_map_of_mem (e : _ →+* Localization.AtPrime q) hmem
  have h2 := Ideal.mem_map_of_mem (e : _ →+* Localization.AtPrime q) hτb
  rw [Ideal.map_pow, hmax] at h1
  rw [hmax] at h2
  rw [RingEquiv.coe_toRingHom, he] at h1 h2
  exact algebraMap_notMem_maximalIdeal_pow S.functionField L hA hτ0 hτ q h2 h1

end AlgebraicGeometry.ReducedFibreCurveCounterexample
