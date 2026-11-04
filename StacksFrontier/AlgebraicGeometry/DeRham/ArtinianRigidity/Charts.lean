module

public import StacksFrontier.AlgebraicGeometry.DeRham.ArtinianRigidity.Setup
public import StacksFrontier.AlgebraicGeometry.DeRham.ArtinianRigidity.ClosedFibreSections
public import StacksFrontier.AlgebraicGeometry.DeRham.ArtinianRigidity.ChartAlgebra
public import StacksFrontier.AlgebraicGeometry.Size.Pullback

/-!
# Affine charts of the graph neighbourhood

For affine opens `U ⊆ X` and `V ⊆ X'` whose special fibres are nested, the box
`U ×_A V ⊆ W = X ×_A X'` is affine with ring `Γ(X, U) ⊗_A Γ(X', V)`, it contains the part of the
graph over `U` (resp. `V`), and the sections of the graph neighbourhood `W_N` over `q⁻¹ U`
(resp. `q'⁻¹ V`) are the quotient of that ring by the `N`-th power of the ideal of the graph.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.DeRhamRigidity

/-- Restriction to an open equal to the inverse image: same kernel. -/
theorem ker_appLE_of_eq {Y Y' : Scheme.{u}} (φ : Y ⟶ Y') (O : Y'.Opens) {P : Y.Opens}
    (hP : φ ⁻¹ᵁ O = P) :
    RingHom.ker (φ.appLE O P hP.ge).hom = RingHom.ker (φ.app O).hom := by
  subst hP
  rw [Scheme.Hom.app_eq_appLE]

/-- Restriction to an open equal to the inverse image: same surjectivity. -/
theorem surjective_appLE_of_eq {Y Y' : Scheme.{u}} (φ : Y ⟶ Y') (O : Y'.Opens) {P : Y.Opens}
    (hP : φ ⁻¹ᵁ O = P) (h : Function.Surjective (φ.app O)) :
    Function.Surjective (φ.appLE O P hP.ge) := by
  subst hP
  rwa [← Scheme.Hom.app_eq_appLE]

variable {A : CommRingCat.{u}} [IsLocalRing A] {σ : A ⧸ maximalIdeal A →+* A}
  (hσ : (Ideal.Quotient.mk (maximalIdeal A)).comp σ = RingHom.id _)
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f] (N : ℕ)

/-- The box `U ×_A V = pr₁⁻¹ U ∩ pr₂⁻¹ V` of `W`. -/
abbrev box (U : X.Opens) (V : (trivialDef σ f).Opens) : (graphSpace σ f).Opens :=
  pullback.fst f (trivialMap σ f) ⁻¹ᵁ U ⊓ pullback.snd f (trivialMap σ f) ⁻¹ᵁ V

/-- If `specialIncl f ⁻¹ᵁ U ≤ trivialIncl hσ f ⁻¹ᵁ V`, the inverse image of the box `box f U V`
under the graph is `specialIncl f ⁻¹ᵁ U`. -/
theorem graph_preimage_box_of_le {U : X.Opens} {V : (trivialDef σ f).Opens}
    (hUV : specialIncl f ⁻¹ᵁ U ≤ trivialIncl hσ f ⁻¹ᵁ V) :
    graph hσ f ⁻¹ᵁ box f U V = specialIncl f ⁻¹ᵁ U := by
  ext z
  simp only [box, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, graph_fst, graph_snd]
  exact ⟨fun h => h.1, fun h => ⟨h, hUV h⟩⟩

/-- If `trivialIncl hσ f ⁻¹ᵁ V ≤ specialIncl f ⁻¹ᵁ U`, the inverse image of the box `box f U V`
under the graph is `trivialIncl hσ f ⁻¹ᵁ V`. -/
theorem graph_preimage_box_of_ge {U : X.Opens} {V : (trivialDef σ f).Opens}
    (hVU : trivialIncl hσ f ⁻¹ᵁ V ≤ specialIncl f ⁻¹ᵁ U) :
    graph hσ f ⁻¹ᵁ box f U V = trivialIncl hσ f ⁻¹ᵁ V := by
  ext z
  simp only [box, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, graph_fst, graph_snd]
  exact ⟨fun h => h.2, fun h => ⟨hVU h, h⟩⟩

/-- A point in the range of `φ` whose image under `p` lies in `U` has image under `q` in `V`, if
`(φ ≫ p) ⁻¹ᵁ U ≤ (φ ≫ q) ⁻¹ᵁ V`. -/
private theorem apply_mem_of_range_of_le {Z W S T : Scheme.{u}} (φ : Z ⟶ W) (p : W ⟶ S)
    (q : W ⟶ T) {U : S.Opens} {V : T.Opens} (h : (φ ≫ p) ⁻¹ᵁ U ≤ (φ ≫ q) ⁻¹ᵁ V) {w : W}
    (hw : w ∈ Set.range φ) (hwU : p w ∈ U) : q w ∈ V := by
  obtain ⟨z, rfl⟩ := hw
  exact h hwU

/-- If `specialIncl f ⁻¹ᵁ U ≤ trivialIncl hσ f ⁻¹ᵁ V` and `N ≠ 0`, the inverse image of the box
`box f U V` in the graph neighbourhood `W_N` is `graphNbhdFst hσ f N ⁻¹ᵁ U`. -/
theorem graphNbhdFst_preimage {U : X.Opens} {V : (trivialDef σ f).Opens}
    (hUV : specialIncl f ⁻¹ᵁ U ≤ trivialIncl hσ f ⁻¹ᵁ V) (hN : N ≠ 0) :
    graphNbhdι hσ f N ⁻¹ᵁ box f U V = graphNbhdFst hσ f N ⁻¹ᵁ U := by
  refine le_antisymm (fun w hw => hw.1) fun w hw => ⟨hw, ?_⟩
  exact apply_mem_of_range_of_le (graph hσ f) _ _ (by rwa [graph_fst, graph_snd])
    (range_graphNbhdι_subset hσ f N hN ⟨w, rfl⟩) hw

/-- If `trivialIncl hσ f ⁻¹ᵁ V ≤ specialIncl f ⁻¹ᵁ U` and `N ≠ 0`, the inverse image of the box
`box f U V` in the graph neighbourhood `W_N` is `graphNbhdSnd hσ f N ⁻¹ᵁ V`. -/
theorem graphNbhdSnd_preimage {U : X.Opens} {V : (trivialDef σ f).Opens}
    (hVU : trivialIncl hσ f ⁻¹ᵁ V ≤ specialIncl f ⁻¹ᵁ U) (hN : N ≠ 0) :
    graphNbhdι hσ f N ⁻¹ᵁ box f U V = graphNbhdSnd hσ f N ⁻¹ᵁ V := by
  refine le_antisymm (fun w hw => hw.2) fun w hw => ⟨?_, hw⟩
  exact apply_mem_of_range_of_le (graph hσ f) _ _ (by rwa [graph_fst, graph_snd])
    (range_graphNbhdι_subset hσ f N hN ⟨w, rfl⟩) hw

/-- **The box of two affine opens is a pushout of rings**:
`Γ(W, U ×_A V) = Γ(X, U) ⊗_A Γ(X', V)`. -/
theorem isPushout_box {U : X.Opens} (hU : IsAffineOpen U) {V : (trivialDef σ f).Opens}
    (hV : IsAffineOpen V) :
    IsPushout (f.appLE ⊤ U le_top) ((trivialMap σ f).appLE ⊤ V le_top)
      ((pullback.fst f (trivialMap σ f)).appLE U (box f U V) inf_le_left)
      ((pullback.snd f (trivialMap σ f)).appLE V (box f U V) inf_le_right) :=
  (isIso_pushoutSection_iff (IsPullback.of_hasPullback f (trivialMap σ f)) (US := ⊤) (UT := V)
    (UX := U) le_top le_top (UY := box f U V) rfl).1
    (isIso_pushoutSection_of_isAffineOpen _ le_top le_top rfl (isAffineOpen_top _) hV hU)

/-- The box `box f U V` of two affine opens is an affine open of `W`. -/
theorem isAffineOpen_box {U : X.Opens} (hU : IsAffineOpen U) {V : (trivialDef σ f).Opens}
    (hV : IsAffineOpen V) : IsAffineOpen (box f U V) :=
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine (⊤ : (Spec A).Opens).toScheme := isAffineOpen_top _
  isAffineOpen_inf_preimage f (trivialMap σ f) (S₀ := ⊤) le_top le_top

/-- The sections of the graph neighbourhood over a box: the restriction from the box is
surjective with kernel `I_Γ^N`. -/
theorem graphNbhd_appLE_surjective_and_ker {U : X.Opens} (hU : IsAffineOpen U)
    {V : (trivialDef σ f).Opens} (hV : IsAffineOpen V) {P : (graphNbhd hσ f N).Opens}
    (hP : graphNbhdι hσ f N ⁻¹ᵁ box f U V = P) :
    Function.Surjective ((graphNbhdι hσ f N).appLE (box f U V) P hP.ge) ∧
      RingHom.ker ((graphNbhdι hσ f N).appLE (box f U V) P hP.ge).hom =
        RingHom.ker ((graph hσ f).app (box f U V)).hom ^ N := by
  let O : (graphSpace σ f).affineOpens := ⟨box f U V, isAffineOpen_box f hU hV⟩
  refine ⟨surjective_appLE_of_eq _ _ hP
    (Scheme.IdealSheafData.subschemeι_app_surjective (graphIdealSheaf hσ f ^ N) O), ?_⟩
  rw [ker_appLE_of_eq _ _ hP]
  have h := Scheme.IdealSheafData.ker_subschemeι_app (graphIdealSheaf hσ f ^ N) O
  rwa [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply] at h

/-- The ideal `𝔪 Γ(Spec A, ⊤)` of the global sections of `Spec A`. -/
abbrev baseIdeal (A : CommRingCat.{u}) [IsLocalRing A] : Ideal Γ(Spec A, ⊤) :=
  (maximalIdeal A).map (Scheme.ΓSpecIso A).inv.hom

/-- If `𝔪^N = 0` then `baseIdeal A ^ N = 0`. -/
theorem baseIdeal_pow (A : CommRingCat.{u}) [IsLocalRing A] {N : ℕ}
    (hN : maximalIdeal A ^ N = ⊥) : baseIdeal A ^ N = ⊥ := by
  rw [baseIdeal, ← Ideal.map_pow, hN, Ideal.map_bot]

/-- `Γ(Spec A, ⊤)` is a `ℚ`-algebra when `A` is. -/
@[instance_reducible]
def baseRatAlgebra (A : CommRingCat.{u}) [Algebra ℚ A] : Algebra ℚ Γ(Spec A, ⊤) :=
  ((Scheme.ΓSpecIso A).inv.hom.comp (algebraMap ℚ A)).toAlgebra

/-- Composing restrictions along `f ≫ g = h` gives the restriction of `h` to `U`. -/
private theorem appLE_comp_appLE_eq_app {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (f : X ⟶ Y) {h : X ⟶ Z}
    (hfg : f ≫ g = h) (U : Z.Opens) (V : Y.Opens) (e₁ e₂) :
    g.appLE U V e₁ ≫ f.appLE V (h ⁻¹ᵁ U) e₂ = h.app U := by
  subst hfg
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]

/-- **The chart computation on the `X` side.** For affine opens `U ⊆ X`, `V ⊆ X'` with
`U₀ ⊆ V₀` and `V` with étale coordinates over `A`, restriction of forms
`Ω^•_{Γ(X, U)/A} → Ω^•_{Γ(W_N, q⁻¹ U)/A}` is a quasi-isomorphism, when `A ⊇ ℚ` and `𝔪^N = 0`. -/
theorem quasiIso_chartFst [Algebra ℚ A] (hN0 : N ≠ 0) (hN : maximalIdeal A ^ N = ⊥)
    {U : X.Opens} (hU : IsAffineOpen U) {V : (trivialDef σ f).Opens} (hV : IsAffineOpen V)
    (hUV : specialIncl f ⁻¹ᵁ U ≤ trivialIncl hσ f ⁻¹ᵁ V) {d : ℕ}
    (e : MvPolynomial (Fin d) Γ(Spec A, ⊤) →+* Γ(trivialDef σ f, V))
    (he : e.comp MvPolynomial.C = ((trivialMap σ f).appLE ⊤ V le_top).hom) (het : e.Etale) :
    letI : Algebra Γ(Spec A, ⊤) Γ(X, U) := (f.appLE ⊤ U le_top).hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(graphNbhd hσ f N, graphNbhdFst hσ f N ⁻¹ᵁ U) :=
      ((graphNbhdFst hσ f N).app U).hom.toAlgebra
    letI : Algebra Γ(Spec A, ⊤) Γ(graphNbhd hσ f N, graphNbhdFst hσ f N ⁻¹ᵁ U) :=
      ((graphNbhdFst hσ f N ≫ f).appLE ⊤ (graphNbhdFst hσ f N ⁻¹ᵁ U) le_top).hom.toAlgebra
    haveI : IsScalarTower Γ(Spec A, ⊤) Γ(X, U)
        Γ(graphNbhd hσ f N, graphNbhdFst hσ f N ⁻¹ᵁ U) :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change _ = (f.appLE ⊤ U le_top ≫ (graphNbhdFst hσ f N).app U) r
        rw [Scheme.Hom.app_eq_appLE]
        exact congrArg (fun φ : Γ(Spec A, ⊤) ⟶ Γ(graphNbhd hσ f N, graphNbhdFst hσ f N ⁻¹ᵁ U) =>
          φ r) (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    QuasiIso (KaehlerDifferential.deRhamComplexMap Γ(Spec A, ⊤) Γ(X, U)
      Γ(graphNbhd hσ f N, graphNbhdFst hσ f N ⁻¹ᵁ U)) := by
  let := baseRatAlgebra A
  have hgr := graph_preimage_box_of_le hσ f hUV
  have hq := graphNbhdFst_preimage hσ f N hUV hN0
  obtain ⟨hρ, hρker⟩ := graphNbhd_appLE_surjective_and_ker hσ f N hU hV hq
  obtain ⟨hπ, hπker⟩ := app_surjective_and_ker_of_isPullback (maximalIdeal A)
    (isPullback_specialIncl f) hU
  have hcγ : (pullback.fst f (trivialMap σ f)).appLE U (box f U V) inf_le_left ≫
      (graph hσ f).appLE (box f U V) (specialIncl f ⁻¹ᵁ U) hgr.ge = (specialIncl f).app U :=
    appLE_comp_appLE_eq_app _ _ (graph_fst hσ f) _ _ _ _
  refine quasiIso_deRhamComplexMap_of_isPushout (f.appLE ⊤ U le_top)
    ((trivialMap σ f).appLE ⊤ V le_top) _ _
    ((graph hσ f).appLE (box f U V) (specialIncl f ⁻¹ᵁ U) hgr.ge)
    ((graphNbhdι hσ f N).appLE (box f U V) _ hq.ge) (isPushout_box f hU hV) hρ ?_
    (baseIdeal A) hN0 (baseIdeal_pow A hN) ?_ ?_ e he het _ ?_ _ ?_
  · rw [hρker, ker_appLE_of_eq _ _ hgr]
  · rwa [hcγ]
  · rw [hcγ, hπker, baseIdeal, Ideal.map_map]
    rfl
  · exact appLE_comp_appLE_eq_app _ _ rfl _ _ _ _
  · rw [Scheme.Hom.app_eq_appLE]
    exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _

/-- **The chart computation on the `X'` side.** The mirror image of `quasiIso_chartFst`: for
affine opens `U ⊆ X`, `V ⊆ X'` with `V₀ ⊆ U₀` and `U` with étale coordinates over `A`,
restriction of forms `Ω^•_{Γ(X', V)/A} → Ω^•_{Γ(W_N, q'⁻¹ V)/A}` is a quasi-isomorphism. -/
theorem quasiIso_chartSnd [Algebra ℚ A] (hN0 : N ≠ 0) (hN : maximalIdeal A ^ N = ⊥)
    {U : X.Opens} (hU : IsAffineOpen U) {V : (trivialDef σ f).Opens} (hV : IsAffineOpen V)
    (hVU : trivialIncl hσ f ⁻¹ᵁ V ≤ specialIncl f ⁻¹ᵁ U) {d : ℕ}
    (e : MvPolynomial (Fin d) Γ(Spec A, ⊤) →+* Γ(X, U))
    (he : e.comp MvPolynomial.C = (f.appLE ⊤ U le_top).hom) (het : e.Etale) :
    letI : Algebra Γ(Spec A, ⊤) Γ(trivialDef σ f, V) :=
      ((trivialMap σ f).appLE ⊤ V le_top).hom.toAlgebra
    letI : Algebra Γ(trivialDef σ f, V) Γ(graphNbhd hσ f N, graphNbhdSnd hσ f N ⁻¹ᵁ V) :=
      ((graphNbhdSnd hσ f N).app V).hom.toAlgebra
    letI : Algebra Γ(Spec A, ⊤) Γ(graphNbhd hσ f N, graphNbhdSnd hσ f N ⁻¹ᵁ V) :=
      ((graphNbhdSnd hσ f N ≫ trivialMap σ f).appLE ⊤ (graphNbhdSnd hσ f N ⁻¹ᵁ V)
        le_top).hom.toAlgebra
    haveI : IsScalarTower Γ(Spec A, ⊤) Γ(trivialDef σ f, V)
        Γ(graphNbhd hσ f N, graphNbhdSnd hσ f N ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun r => by
        change _ = ((trivialMap σ f).appLE ⊤ V le_top ≫ (graphNbhdSnd hσ f N).app V) r
        rw [Scheme.Hom.app_eq_appLE]
        exact congrArg (fun φ : Γ(Spec A, ⊤) ⟶ Γ(graphNbhd hσ f N, graphNbhdSnd hσ f N ⁻¹ᵁ V) =>
          φ r) (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    QuasiIso (KaehlerDifferential.deRhamComplexMap Γ(Spec A, ⊤) Γ(trivialDef σ f, V)
      Γ(graphNbhd hσ f N, graphNbhdSnd hσ f N ⁻¹ᵁ V)) := by
  let := baseRatAlgebra A
  have hgr := graph_preimage_box_of_ge hσ f hVU
  have hq := graphNbhdSnd_preimage hσ f N hVU hN0
  obtain ⟨hρ, hρker⟩ := graphNbhd_appLE_surjective_and_ker hσ f N hU hV hq
  obtain ⟨hπ, hπker⟩ := app_surjective_and_ker_of_isPullback (maximalIdeal A)
    (isPullback_trivialIncl hσ f) hV
  have hcγ : (pullback.snd f (trivialMap σ f)).appLE V (box f U V) inf_le_right ≫
      (graph hσ f).appLE (box f U V) (trivialIncl hσ f ⁻¹ᵁ V) hgr.ge =
        (trivialIncl hσ f).app V :=
    appLE_comp_appLE_eq_app _ _ (graph_snd hσ f) _ _ _ _
  refine quasiIso_deRhamComplexMap_of_isPushout ((trivialMap σ f).appLE ⊤ V le_top)
    (f.appLE ⊤ U le_top) _ _
    ((graph hσ f).appLE (box f U V) (trivialIncl hσ f ⁻¹ᵁ V) hgr.ge)
    ((graphNbhdι hσ f N).appLE (box f U V) _ hq.ge) (isPushout_box f hU hV).flip hρ ?_
    (baseIdeal A) hN0 (baseIdeal_pow A hN) ?_ ?_ e he het _ ?_ _ ?_
  · rw [hρker, ker_appLE_of_eq _ _ hgr]
  · rwa [hcγ]
  · rw [hcγ, hπker, baseIdeal, Ideal.map_map]
    rfl
  · exact appLE_comp_appLE_eq_app _ _ rfl _ _ _ _
  · rw [Scheme.Hom.app_eq_appLE]
    exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _

end Stacks.DeRhamRigidity
