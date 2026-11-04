module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartIdealFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartNerveAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartNerveSpace
public import StacksFrontier.RingTheory.Descent.CechNerveNilClimb

/-!
# An algebraic space with an affine closed thickening is affine

Let `j : P ⟶ W` be a closed immersion of algebraic spaces over `S` which is surjective, with `P`
affine. Then `W` is affine. This is the closed-immersion case of Stacks 07VS, and the affine case
of Stacks 05ZR (`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_affineCase`).

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_range_eq_ker`: on a chart `f : h_U → W`, the defining
  ideal of the image of a closed immersion `j` is the kernel of `Γ(U) → Γ(U ×_W P)`, for any
  representation of the base change.
* `AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace`:
  the statement above.

## Implementation notes

The proof is the deformation argument of the second proof of Stacks 05ZR, made to work for a
thickening of arbitrary order. An affine surjective étale chart `U → W` with kernel pair `R` and
triple product `W₃` gives rings `Γ(U) ⇉ Γ(R) ⇉ Γ(W₃)` which form a Čech nerve modulo the ideal
`K` of `U ×_W P ⊆ U`, because `P` is affine
(`AlgebraicGeometry.Space.exists_affineChart_isNerveReduction`). The ideal `K` is nil, and it is a
directed union of finitely generated ideals invariant under the two projections (Stacks 0829 on
charts, `AlgebraicGeometry.Space.exists_directed_fg_invariant_ideals`), so the nerve modulo `K`
climbs to a nerve modulo `0` (`Module.Descent.isNerveReduction_bot_of_iSup_fg`), and a nerve
modulo `0` presents `W` as an affine scheme
(`AlgebraicGeometry.Space.isAffineSpace_of_isNerveReduction_bot`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The defining ideal of the image of a closed immersion on a chart.** For a closed immersion
`j : P ⟶ W` from an algebraic space and a chart `T` of `W` with structure map `f`, if
`h_{U₀} → P, i : U₀ → U` is a pullback of `j` along `f`, the defining ideal of the image of `j`
at `T` is the kernel of `i^* : Γ(U) → Γ(U₀)`. -/
theorem definingIdealAt_range_eq_ker {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : AlgebraicSpaces B S hS) (j : P ⟶ W.1) (hP : IsAlgebraicSpace B S hS P)
    (hj : IsClosedImmersion B S hS j) (T : SmallEtale B S hS W.1) {U₀ : BigFppfOver B S hS}
    (i : U₀ ⟶ T.1.left) (k : yoneda.obj U₀ ⟶ P) (hk : IsPullback k (yoneda.map i) j T.1.hom) :
    definingIdealAt B S hS W ⟨Subfunctor.range j,
        isClosedSubspace_range_of_isClosedImmersion B S hS j hP hj⟩ (Opposite.op T) =
      RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom := by
  let Z : ClosedSubspaces B S hS W.1 :=
    ⟨Subfunctor.range j, isClosedSubspace_range_of_isClosedImmersion B S hS j hP hj⟩
  rw [definingIdealAt_eq_ker B S hS W Z T]
  have hmono : Mono j := mono_of_isClosedImmersion B S hS j hj
  have : IsIso (Subfunctor.toRange j) := inferInstance
  have hk' : IsPullback (k ≫ Subfunctor.toRange j) (yoneda.map i) Z.1.ι T.1.hom :=
    IsPullback.of_iso hk (Iso.refl _) (asIso (Subfunctor.toRange j)) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp [Z]) (by simp)
  let e := hk'.isoIsPullback _ _ (Z.2.2.rep.isPullback T.1.hom)
  let e' := yoneda.preimageIso e
  have he : e'.hom ≫ Z.2.2.rep.snd T.1.hom = i := yoneda.map_injective (by
    rw [yoneda.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
    exact hk'.isoIsPullback_hom_snd _ _ (Z.2.2.rep.isPullback T.1.hom))
  have hiso : IsIso ((BigFppfOver.toScheme B S hS).map e'.hom).appTop := by
    have : IsIso ((BigFppfOver.toScheme B S hS).map e'.hom) :=
      ((BigFppfOver.toScheme B S hS).mapIso e').isIso_hom
    rw [← Scheme.Γ_map_op]
    exact Functor.map_isIso Scheme.Γ _
  have hinj := (ConcreteCategory.bijective_of_isIso
    ((BigFppfOver.toScheme B S hS).map e'.hom).appTop).injective
  ext a
  simp only [RingHom.mem_ker]
  rw [← he, Functor.map_comp, Scheme.Hom.comp_appTop]
  show _ ↔ ((BigFppfOver.toScheme B S hS).map e'.hom).appTop.hom
    (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd T.1.hom)).appTop.hom a) = 0
  rw [← map_zero ((BigFppfOver.toScheme B S hS).map e'.hom).appTop.hom, hinj.eq_iff]
  rfl

/-- **An algebraic space receiving a surjective closed immersion from an affine algebraic space
is affine** (the closed-immersion case of Stacks 07VS; the affine case of Stacks 05ZR). -/
theorem isAffineSpace_of_isClosedImmersion_of_isSurjective_of_isAffineSpace
    {P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : P ⟶ W) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W) (hj : IsClosedImmersion B S hS j)
    (hsurj : IsSurjective B S hS j) (haff : IsAffineSpace B S hS P) :
    IsAffineSpace B S hS W := by
  obtain ⟨hqc, hqs⟩ := isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isClosedImmersion
    B S hS j hP hW hj hsurj haff
  obtain ⟨X₀, hX₀, ⟨eQ⟩⟩ := haff
  obtain ⟨U, R, W₃, U₀, f, t, s, δ, e₁₂, e₁₃, e₂₃, i, k, hfs, hfe, hR, hU, hRa, hW₃, hδt, hδs,
    h₁₂₁₃, h₁₂₂₃, h₁₃₂₃, ht, hs, he₁₂, he₂₃, -, -, hk, -, hKnil, hnerve⟩ :=
    exists_affineChart_isNerveReduction B S hS hW j hj
      (presheafSurjective_of_isSurjective B S hS j hj.1 hsurj) hX₀ eQ
  let G := BigFppfOver.toScheme B S hS
  have := hU
  have := hRa
  have := hW₃
  have := ht
  have := hs
  have := he₁₂
  have := he₂₃
  -- the chart `U` and the chart `R` over it, with the two maps `t, s`
  let T : SmallEtale B S hS W := ⟨CostructuredArrow.mk f, hfe⟩
  let T₂ : SmallEtale B S hS W :=
    ⟨CostructuredArrow.mk (yoneda.map t ≫ f), isEtaleChart_comp_of_isPullback hfe hR⟩
  let g₁ : T₂ ⟶ T := ObjectProperty.homMk (CostructuredArrow.homMk t rfl)
  let g₂ : T₂ ⟶ T := ObjectProperty.homMk (CostructuredArrow.homMk s hR.w.symm)
  let Z : ClosedSubspaces B S hS W :=
    ⟨Subfunctor.range j, isClosedSubspace_range_of_isClosedImmersion B S hS j hP hj⟩
  obtain ⟨ι, _, _, _, K, hKm, hKinv, hKfg, hKI⟩ :=
    exists_directed_fg_invariant_ideals B S hS ⟨W, hW⟩ Z hqc hqs (T := T) (T₂ := T₂) hU hRa g₁ g₂
  have hdef := definingIdealAt_range_eq_ker B S hS ⟨W, hW⟩ j hP hj T i k hk
  -- the rings of functions, as algebras over `ℤ` (lifted to the universe `u`)
  let : ∀ X : Scheme.{u}, Algebra (ULift.{u} ℤ) Γ(X, ⊤) := fun _ =>
    ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom).toAlgebra
  let mk : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), Γ(Y, ⊤) →ₐ[ULift.{u} ℤ] Γ(X, ⊤) := fun g =>
    { toRingHom := g.appTop.hom, commutes' := fun r => map_intCast g.appTop.hom r.down }
  let p₁ := mk (G.map t)
  let p₂ := mk (G.map s)
  let δ' := mk (G.map δ)
  let q₁₂ := mk (G.map e₁₂)
  let q₁₃ := mk (G.map e₁₃)
  let q₂₃ := mk (G.map e₂₃)
  obtain ⟨hδ₁, hδ₂, h₁, h₂, h₃, hp₁, hp₂, hq₁₂, hq₂₃⟩ := nerve_identities_of_schemes (G.map t)
    (G.map s) (G.map δ) (G.map e₁₂) (G.map e₁₃) (G.map e₂₃) hδt hδs h₁₂₁₃ h₁₂₂₃ h₁₃₂₃
    p₁ p₂ δ' q₁₂ q₁₃ q₂₃ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
  have hN := hnerve p₁ p₂ q₁₂ q₁₃ q₂₃ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)
  have hbot := Module.Descent.isNerveReduction_bot_of_iSup_fg p₁ p₂ δ' q₁₂ q₁₃ q₂₃ hδ₁ hδ₂
    h₁ h₂ h₃ hp₁ hp₂ hq₁₂ hq₂₃ K hKm hKinv hKfg _ hKnil (hKI.trans hdef) hN
  exact isAffineSpace_of_isNerveReduction_bot B S hS hW f t s hR hfs hfe hU hRa p₁ p₂
    (fun _ => rfl) (fun _ => rfl) hbot

end AlgebraicGeometry.Space
