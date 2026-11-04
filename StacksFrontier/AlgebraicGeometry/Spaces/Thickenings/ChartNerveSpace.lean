module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartNerveClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.NilpotentUnits

/-!
# An affine Čech nerve of an algebraic space with an affine closed thickening

Let `F` be an algebraic space over `S` and `j : Q → F` a surjective closed immersion from an
affine scheme `X₀` (`Q ≅ h_{X₀}`). Then `F` is quasi-compact, so it has a surjective étale chart
`f : U → F` with `U` affine; its kernel pair `R = U ×_F U` and triple product `W = R ×_U R` are
affine too, being thickenings of the affine schemes `R ×_F Q` and `W ×_F Q` (Stacks 06AD). The
rings of functions `Γ(U) ⇉ Γ(R) ⇉ Γ(W)` form a Čech nerve modulo the ideal of the closed subscheme
`U₀ = U ×_F Q` of `U` (`Module.Descent.IsNerveReduction`), over any compatible base ring:
`AlgebraicGeometry.Space.exists_affineChart_isNerveReduction`.

The proof restricts the chart to `U₀ → X₀` and computes, by pasting pullback squares, that
`R ×_U U₀` is the kernel pair of `U₀ → X₀` and `W ×_R (R ×_U U₀)` its triple product; then
`AlgebraicGeometry.isNerveReduction_of_isClosedImmersion` applies.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.IsPullback

variable {D : Type*} [Category D]

/-- **The restriction of a kernel pair to a pullback of the base.** Let `t, s : R ⇉ U` be the
kernel pair of `f : U → F`, let `i : U₀ → U` be the base change of `j : Q → F` along `f` (with
`k : U₀ → Q`), let `R₀ = R ×_{t, U} U₀` (projections `r`, `tQ`), and let `sQ : R₀ → U₀` lift
`r ≫ s` with `sQ ≫ k = tQ ≫ k`. Then `tQ, sQ` is the kernel pair of `k`. -/
theorem kernelPair_restrict {U R F Q U₀ R₀ : D} {t s : R ⟶ U} {f : U ⟶ F} {j : Q ⟶ F}
    {k : U₀ ⟶ Q} {i : U₀ ⟶ U} {r : R₀ ⟶ R} {tQ sQ : R₀ ⟶ U₀}
    (hR : IsPullback t s f f) (hk : IsPullback k i j f) (hr : IsPullback r tQ t i)
    (hsQi : sQ ≫ i = r ≫ s) (hsQk : sQ ≫ k = tQ ≫ k) : IsPullback tQ sQ k k := by
  have hA : IsPullback (sQ ≫ i) tQ f (k ≫ j) := by
    rw [hsQi, hk.w]
    exact hr.paste_horiz hR.flip
  exact (hA.of_right hsQk hk.flip).flip

/-- **The second projection of a restricted kernel pair is a base change.** In the situation of
`CategoryTheory.IsPullback.kernelPair_restrict`, `R₀ = R ×_{s, U} U₀` with projections `r`,
`sQ`. -/
theorem kernelPair_restrict_snd {U R F Q U₀ R₀ : D} {t s : R ⟶ U} {f : U ⟶ F} {j : Q ⟶ F}
    {k : U₀ ⟶ Q} {i : U₀ ⟶ U} {r : R₀ ⟶ R} {tQ sQ : R₀ ⟶ U₀}
    (hR : IsPullback t s f f) (hk : IsPullback k i j f) (hRQ : IsPullback tQ sQ k k)
    (hrt : r ≫ t = tQ ≫ i) (hsQi : sQ ≫ i = r ≫ s) : IsPullback r sQ s i := by
  have hA : IsPullback (r ≫ t) sQ f (i ≫ f) := by
    rw [hrt, ← hk.w]
    exact hRQ.paste_horiz hk.flip
  exact hA.of_right hsQi.symm hR

/-- **The restriction of a triple product to a pullback.** Let `W = R ×_{s, U, t} R` (with
`e₁₂, e₂₃`), `R₀ = R ×_{t, U} U₀` (with `r`, `tQ`), `W₀ = W ×_{e₁₂, R} R₀` (with `w`, `e₁₂Q`),
`sQ : R₀ → U₀` lifting `r ≫ s` and `e₂₃Q : W₀ → R₀` lifting `w ≫ e₂₃` with
`e₂₃Q ≫ tQ = e₁₂Q ≫ sQ`. Then `W₀ = R₀ ×_{sQ, U₀, tQ} R₀`. -/
theorem triple_restrict {U R W U₀ R₀ W₀ : D} {t s : R ⟶ U} {e₁₂ e₂₃ : W ⟶ R} {i : U₀ ⟶ U}
    {r : R₀ ⟶ R} {tQ sQ : R₀ ⟶ U₀} {w : W₀ ⟶ W} {e₁₂Q e₂₃Q : W₀ ⟶ R₀}
    (hW : IsPullback e₁₂ e₂₃ s t) (hr : IsPullback r tQ t i) (hw : IsPullback w e₁₂Q e₁₂ r)
    (hsQ : sQ ≫ i = r ≫ s) (h₂₃ : e₂₃Q ≫ r = w ≫ e₂₃) (hc : e₂₃Q ≫ tQ = e₁₂Q ≫ sQ) :
    IsPullback e₁₂Q e₂₃Q sQ tQ := by
  have hA : IsPullback (e₂₃Q ≫ r) e₁₂Q t (sQ ≫ i) := by
    rw [h₂₃, hsQ]
    exact hw.paste_horiz hW.flip
  exact (hA.of_right hc hr).flip

end CategoryTheory.IsPullback

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine Čech nerve of an algebraic space with an affine closed thickening (G1, G2).**
Let `F` be an algebraic space over `S` and `j : Q → F` a closed immersion which is surjective
after every representable base change, with `Q ≅ h_{X₀}` for an affine `X₀`. Then there are a
surjective étale chart `f : h_U → F` with kernel pair `t, s : R ⇉ U`, a diagonal `δ`, morphisms
`e₁₂, e₁₃, e₂₃ : W → R` of the site, with `U`, `R`, `W` affine and the identities and étaleness
of a Čech nerve, and the base change `i : U₀ → U` of `j` (a surjective closed immersion, with
`k : h_{U₀} → Q`), such that the kernel `K` of `Γ(U) → Γ(U₀)` is invariant (`t^* K` and `s^* K`
generate the same ideal) and nil, and for every compatible base ring `R'` the rings of functions
`Γ(U) ⇉ Γ(R) ⇉ Γ(W)` form a nerve modulo `K`. -/
theorem exists_affineChart_isNerveReduction {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (j : Q ⟶ F)
    (hj : IsClosedImmersion B S hS j)
    (hjs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j)
    {X₀ : BigFppfOver B S hS} (hX₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj X₀))
    (eQ : Q ≅ yoneda.obj X₀) :
    ∃ (U R W U₀ : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F) (t s : R ⟶ U) (δ : U ⟶ R)
      (e₁₂ e₁₃ e₂₃ : W ⟶ R) (i : U₀ ⟶ U) (k : yoneda.obj U₀ ⟶ Q),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) f ∧
      IsPullback (yoneda.map t) (yoneda.map s) f f ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj R) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
      (BigFppfOver.toScheme B S hS).map δ ≫ (BigFppfOver.toScheme B S hS).map t = 𝟙 _ ∧
      (BigFppfOver.toScheme B S hS).map δ ≫ (BigFppfOver.toScheme B S hS).map s = 𝟙 _ ∧
      (BigFppfOver.toScheme B S hS).map e₁₂ ≫ (BigFppfOver.toScheme B S hS).map t =
        (BigFppfOver.toScheme B S hS).map e₁₃ ≫ (BigFppfOver.toScheme B S hS).map t ∧
      (BigFppfOver.toScheme B S hS).map e₁₂ ≫ (BigFppfOver.toScheme B S hS).map s =
        (BigFppfOver.toScheme B S hS).map e₂₃ ≫ (BigFppfOver.toScheme B S hS).map t ∧
      (BigFppfOver.toScheme B S hS).map e₁₃ ≫ (BigFppfOver.toScheme B S hS).map s =
        (BigFppfOver.toScheme B S hS).map e₂₃ ≫ (BigFppfOver.toScheme B S hS).map s ∧
      Etale ((BigFppfOver.toScheme B S hS).map t) ∧ Etale ((BigFppfOver.toScheme B S hS).map s) ∧
      Etale ((BigFppfOver.toScheme B S hS).map e₁₂) ∧
      Etale ((BigFppfOver.toScheme B S hS).map e₂₃) ∧
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map i) ∧ IsPullback k (yoneda.map i) j f ∧
      (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom).map
          ((BigFppfOver.toScheme B S hS).map t).appTop.hom =
        (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom).map
          ((BigFppfOver.toScheme B S hS).map s).appTop.hom ∧
      RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom ≤
        nilradical Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ∧
      ∀ {R' : Type u} [CommRing R'] [Algebra R' Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)]
        [Algebra R' Γ((BigFppfOver.toScheme B S hS).obj R, ⊤)]
        [Algebra R' Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)]
        (p₁ p₂ : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →ₐ[R']
          Γ((BigFppfOver.toScheme B S hS).obj R, ⊤))
        (e₁₂' e₁₃' e₂₃' : Γ((BigFppfOver.toScheme B S hS).obj R, ⊤) →ₐ[R']
          Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)),
        (∀ b, p₁ b = ((BigFppfOver.toScheme B S hS).map t).appTop.hom b) →
        (∀ b, p₂ b = ((BigFppfOver.toScheme B S hS).map s).appTop.hom b) →
        (∀ c, e₁₂' c = ((BigFppfOver.toScheme B S hS).map e₁₂).appTop.hom c) →
        (∀ c, e₁₃' c = ((BigFppfOver.toScheme B S hS).map e₁₃).appTop.hom c) →
        (∀ c, e₂₃' c = ((BigFppfOver.toScheme B S hS).map e₂₃).appTop.hom c) →
        Module.Descent.IsNerveReduction p₁ p₂ e₁₂' e₁₃' e₂₃'
          (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom) := by
  have : HasPullbacks (BigFppfOver B S hS) := by
    let := B.hasPullbacks_schemes
    infer_instance
  let G := BigFppfOver.toScheme B S hS
  have : PreservesLimitsOfShape WalkingCospan G :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have mc : ∀ {X Y Z X' : BigFppfOver B S hS} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ X')
      (d : X' ⟶ Z), a ≫ b = c ≫ d → G.map a ≫ G.map b = G.map c ≫ G.map d := by
    intro X Y Z X' a b c d h
    rw [← G.map_comp, ← G.map_comp, h]
  have yc : ∀ {X Y Z X' : BigFppfOver B S hS} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ X')
      (d : X' ⟶ Z), yoneda.map a ≫ yoneda.map b = yoneda.map c ≫ yoneda.map d →
      a ≫ b = c ≫ d := by
    intro X Y Z X' a b c d h
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, h]
  -- the chart
  have hQaff : IsAffineSpace B S hS Q := ⟨X₀, hX₀, ⟨eQ⟩⟩
  have hFqc : IsQuasiCompactSpace B S hS F :=
    isQuasiCompactSpace_of_isSurjective B S hS hQaff.isAlgebraicSpace hF j
      (isSurjective_of_presheafSurjective B S hS j hjs) hQaff.isQuasiCompactSpace
  obtain ⟨U, f, hU, hsurj, hetU⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).1 hFqc
  have hetale := (isEtale_iff_presheaf_of_yoneda B S hS f).1 hetU
  let hrep : yoneda.relativelyRepresentable f := hetale.1
  let R := hrep.pullback f
  let t : R ⟶ U := hrep.fst' f
  let s : R ⟶ U := hrep.snd f
  have hR : IsPullback (yoneda.map t) (yoneda.map s) f f := hrep.isPullback' f
  have ht : Etale (G.map t) := hetale.2 f (yoneda.map s) t hR.flip
  have hs : Etale (G.map s) := hetale.2 f (hrep.fst f) s (hrep.isPullback f)
  -- diagonal and triple product
  let δ : U ⟶ R := yoneda.preimage (hR.lift (𝟙 _) (𝟙 _) rfl)
  have hδt : δ ≫ t = 𝟙 U := yoneda.map_injective (by
    rw [yoneda.map_comp, Functor.map_preimage, IsPullback.lift_fst, yoneda.map_id])
  have hδs : δ ≫ s = 𝟙 U := yoneda.map_injective (by
    rw [yoneda.map_comp, Functor.map_preimage, IsPullback.lift_snd, yoneda.map_id])
  let W := pullback s t
  let e₁₂ : W ⟶ R := pullback.fst s t
  let e₂₃ : W ⟶ R := pullback.snd s t
  have hW : IsPullback e₁₂ e₂₃ s t := IsPullback.of_hasPullback s t
  have hW' : yoneda.map e₁₂ ≫ yoneda.map s = yoneda.map e₂₃ ≫ yoneda.map t := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, hW.w]
  let e₁₃ : W ⟶ R := yoneda.preimage (hR.lift (yoneda.map e₁₂ ≫ yoneda.map t)
    (yoneda.map e₂₃ ≫ yoneda.map s) (by
      simp only [Category.assoc, hR.w]
      rw [← Category.assoc, hW', Category.assoc, hR.w]))
  have h₁₃t : e₁₃ ≫ t = e₁₂ ≫ t := yoneda.map_injective (by
    rw [yoneda.map_comp, Functor.map_preimage, IsPullback.lift_fst, yoneda.map_comp])
  have h₁₃s : e₁₃ ≫ s = e₂₃ ≫ s := yoneda.map_injective (by
    rw [yoneda.map_comp, Functor.map_preimage, IsPullback.lift_snd, yoneda.map_comp])
  have hWG : IsPullback (G.map e₁₂) (G.map e₂₃) (G.map s) (G.map t) := hW.map G
  have he₁₂ : Etale (G.map e₁₂) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hWG.flip ht
  have he₂₃ : Etale (G.map e₂₃) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hWG hs
  -- the restriction to `Q`
  let hrepj : yoneda.relativelyRepresentable j := hj.1
  let U₀ := hrepj.pullback f
  let i : U₀ ⟶ U := hrepj.snd f
  let k : yoneda.obj U₀ ⟶ Q := hrepj.fst f
  have hk : IsPullback k (yoneda.map i) j f := hrepj.isPullback f
  have hi : AlgebraicGeometry.IsClosedImmersion (G.map i) := hj.2 f k i hk
  have := hi
  have his : Surjective (G.map i) := hjs.2 f k i hk
  let g : U₀ ⟶ X₀ := yoneda.preimage (k ≫ eQ.hom)
  have hgk : yoneda.map g = k ≫ eQ.hom := Functor.map_preimage _ _
  have hk' : IsPullback (yoneda.map g) (yoneda.map i) (eQ.inv ≫ j) f := by
    refine hk.of_iso (Iso.refl _) eQ (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hgk]
    · simp
    · simp
    · simp
  have hge : Etale (G.map g) := hetale.2 (eQ.inv ≫ j) (yoneda.map i) g hk'.flip
  have hgs : Surjective (G.map g) := hsurj.2 (eQ.inv ≫ j) (yoneda.map i) g hk'.flip
  -- the kernel pair of `U₀ → X₀`
  let R₀ := pullback t i
  let r : R₀ ⟶ R := pullback.fst t i
  let tQ : R₀ ⟶ U₀ := pullback.snd t i
  have hr : IsPullback r tQ t i := IsPullback.of_hasPullback t i
  have hyr : IsPullback (yoneda.map r) (yoneda.map tQ) (yoneda.map t) (yoneda.map i) :=
    hr.map yoneda
  let sQ : R₀ ⟶ U₀ := yoneda.preimage (hk'.lift (yoneda.map tQ ≫ yoneda.map g)
    (yoneda.map r ≫ yoneda.map s) (by
      rw [Category.assoc, hk'.w, ← Category.assoc, ← hyr.w]
      simp only [Category.assoc, hR.w]))
  have hsQi : sQ ≫ i = r ≫ s := yoneda.map_injective (by
    rw [yoneda.map_comp, Functor.map_preimage, IsPullback.lift_snd, yoneda.map_comp])
  have hsQg : sQ ≫ g = tQ ≫ g := yoneda.map_injective (by
    rw [yoneda.map_comp, Functor.map_preimage, IsPullback.lift_fst, yoneda.map_comp])
  have hRQy : IsPullback (yoneda.map tQ) (yoneda.map sQ) (yoneda.map g) (yoneda.map g) :=
    IsPullback.kernelPair_restrict hR hk' hyr (by rw [← yoneda.map_comp, hsQi, yoneda.map_comp])
      (by rw [← yoneda.map_comp, hsQg, yoneda.map_comp])
  have hRQ : IsPullback tQ sQ g g := IsPullback.of_map yoneda (by rw [hsQg]) hRQy
  have hrs' : IsPullback r sQ s i := IsPullback.of_map yoneda (by rw [hsQi])
    (IsPullback.kernelPair_restrict_snd hR hk' hRQy (by rw [← yoneda.map_comp, hr.w,
      yoneda.map_comp]) (by rw [← yoneda.map_comp, hsQi, yoneda.map_comp]))
  -- the triple product of `U₀ → X₀`
  let W₀ := pullback e₁₂ r
  let w : W₀ ⟶ W := pullback.fst e₁₂ r
  let e₁₂Q : W₀ ⟶ R₀ := pullback.snd e₁₂ r
  have hw : IsPullback w e₁₂Q e₁₂ r := IsPullback.of_hasPullback e₁₂ r
  let e₁₃Q : W₀ ⟶ R₀ := pullback.lift (w ≫ e₁₃) (e₁₂Q ≫ tQ) (by
    rw [Category.assoc, h₁₃t, ← Category.assoc, hw.w, Category.assoc, hr.w, Category.assoc])
  let e₂₃Q : W₀ ⟶ R₀ := pullback.lift (w ≫ e₂₃) (e₁₂Q ≫ sQ) (by
    rw [Category.assoc, ← hW.w, ← Category.assoc, hw.w, Category.assoc, Category.assoc, hsQi])
  have h₁₃ : e₁₃Q ≫ r = w ≫ e₁₃ := pullback.lift_fst _ _ _
  have h₂₃ : e₂₃Q ≫ r = w ≫ e₂₃ := pullback.lift_fst _ _ _
  have h₁₂₁₃Q : e₁₂Q ≫ tQ = e₁₃Q ≫ tQ := (pullback.lift_snd _ _ _).symm
  have h₂₃t : e₂₃Q ≫ tQ = e₁₂Q ≫ sQ := pullback.lift_snd _ _ _
  have hc₁ : (e₁₃Q ≫ sQ) ≫ g = (e₂₃Q ≫ sQ) ≫ g :=
    calc (e₁₃Q ≫ sQ) ≫ g = e₁₃Q ≫ tQ ≫ g := by rw [Category.assoc, hsQg]
    _ = e₁₂Q ≫ tQ ≫ g := by rw [← Category.assoc, ← h₁₂₁₃Q, Category.assoc]
    _ = e₁₂Q ≫ sQ ≫ g := by rw [hsQg]
    _ = e₂₃Q ≫ tQ ≫ g := by rw [← Category.assoc, ← h₂₃t, Category.assoc]
    _ = (e₂₃Q ≫ sQ) ≫ g := by rw [Category.assoc, hsQg]
  have hc₂ : (e₁₃Q ≫ sQ) ≫ i = (e₂₃Q ≫ sQ) ≫ i :=
    calc (e₁₃Q ≫ sQ) ≫ i = e₁₃Q ≫ r ≫ s := by rw [Category.assoc, hsQi]
    _ = w ≫ e₁₃ ≫ s := by rw [← Category.assoc, h₁₃, Category.assoc]
    _ = w ≫ e₂₃ ≫ s := by rw [h₁₃s]
    _ = e₂₃Q ≫ r ≫ s := by rw [← Category.assoc e₂₃Q, h₂₃, Category.assoc]
    _ = (e₂₃Q ≫ sQ) ≫ i := by rw [Category.assoc, hsQi]
  have h₁₃₂₃Q : e₁₃Q ≫ sQ = e₂₃Q ≫ sQ := by
    refine yoneda.map_injective (hk'.hom_ext ?_ ?_)
    · rw [← yoneda.map_comp, ← yoneda.map_comp, hc₁]
    · rw [← yoneda.map_comp, ← yoneda.map_comp, hc₂]
  have hWQ : IsPullback e₁₂Q e₂₃Q sQ tQ :=
    IsPullback.triple_restrict hW hr hw hsQi h₂₃ h₂₃t
  have : IsAffine (G.obj U) := hU
  have : IsAffine (G.obj X₀) := hX₀
  have : IsAffine (G.obj U₀) := isAffine_of_isAffineHom (G.map i)
  -- affineness
  have hrG : IsPullback (G.map r) (G.map tQ) (G.map t) (G.map i) := hr.map G
  have hwG : IsPullback (G.map w) (G.map e₁₂Q) (G.map e₁₂) (G.map r) := hw.map G
  have hRQG : IsPullback (G.map tQ) (G.map sQ) (G.map g) (G.map g) := hRQ.map G
  have hWQG : IsPullback (G.map e₁₂Q) (G.map e₂₃Q) (G.map sQ) (G.map tQ) := hWQ.map G
  have : IsAffine (G.obj R₀) := IsAffine.of_isPullback hRQG
  have : IsAffine (G.obj W₀) := IsAffine.of_isPullback hWQG
  have hrc : AlgebraicGeometry.IsClosedImmersion (G.map r) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsClosedImmersion) hrG.flip hi
  have hrs : Surjective (G.map r) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) hrG.flip his
  have : IsAffine (G.obj R) :=
    Stacks.Thickenings.isAffine_of_isThickening (i := G.map r) ⟨hrc, hrs.surj⟩
  have hwc : AlgebraicGeometry.IsClosedImmersion (G.map w) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsClosedImmersion) hwG.flip hrc
  have hws : Surjective (G.map w) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) hwG.flip hrs
  have : IsAffine (G.obj W) :=
    Stacks.Thickenings.isAffine_of_isThickening (i := G.map w) ⟨hwc, hws.surj⟩
  refine ⟨U, R, W, U₀, f, t, s, δ, e₁₂, e₁₃, e₂₃, i, k, hsurj, hetale, hR, hU, inferInstance,
    inferInstance, by rw [← G.map_comp, hδt, G.map_id], by rw [← G.map_comp, hδs, G.map_id],
    mc _ _ _ _ h₁₃t.symm, mc _ _ _ _ hW.w, mc _ _ _ _ h₁₃s, ht, hs, he₁₂, he₂₃, hi, his, hk,
    ((surjective_and_ker_appTop_of_isPullback hrG).2.symm.trans
      (surjective_and_ker_appTop_of_isPullback (hrs'.map G)).2),
    Stacks.LiftInvertible.ker_app_le_nilradical (G.map i)
      (Stacks.LiftInvertible.ker_le_nilradical_of_surjective (G.map i) his.surj)
      ⟨⊤, isAffineOpen_top _⟩, ?_⟩
  intro R' _ _ _ _ p₁ p₂ e₁₂' e₁₃' e₂₃' hp₁ hp₂ hf₁₂ hf₁₃ hf₂₃
  have := hge
  have := hgs
  exact isNerveReduction_of_isClosedImmersion (G.map i) (G.map g) hrG (mc _ _ _ _ hsQi) hRQG hwG
    hWQG (mc _ _ _ _ h₁₃) (mc _ _ _ _ h₂₃) (mc _ _ _ _ h₁₂₁₃Q) (mc _ _ _ _ h₁₃₂₃Q) p₁ p₂ e₁₂' e₁₃'
    e₂₃' hp₁ hp₂ hf₁₂ hf₁₃ hf₂₃

end AlgebraicGeometry.Space
