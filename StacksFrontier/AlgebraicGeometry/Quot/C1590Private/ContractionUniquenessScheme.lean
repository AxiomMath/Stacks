module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ContractionUniquenessAffine

/-!
# Uniqueness of contractions near a point, for schemes

Let `S` be a scheme and `t : Spec K ⟶ S` a field-valued point over `s ∈ S`, let `X`, `Y₁`, `Y₂` be
proper flat schemes of finite presentation over `S` and let `cᵢ : X ⟶ Yᵢ` be morphisms over `S`.
Let the fibres over `t` be presented by cartesian squares `V ⟶ X`, `Wᵢ ⟶ Yᵢ` over `t`, with the
induced morphisms `mᵢ : V ⟶ Wᵢ`. Suppose there is an isomorphism `ε : W₁ ≅ W₂` over `Spec K` with
`m₁ ≫ ε = m₂`, that `V` has dimension at most one, and that `𝒪_{W₁} ≅ m₁,*𝒪_V` and `R¹m₁,*𝒪_V = 0`.
Then there is an open immersion `e : U ⟶ S` whose image contains `s` such that over `U` the base
changes of `Y₁` and `Y₂` are isomorphic compatibly with `c₁` and `c₂`.

This is [Stacks, Tag 0E89] for schemes. The case of an affine base is
`AlgebraicGeometry.C1590Private.exists_open_iso_of_fieldFibre_of_isAffine`; here the fibres are
read on arbitrary cartesian presentations, the base is arbitrary (one restricts to an affine
neighbourhood of `s`), and the conclusion is stated for arbitrary cartesian presentations of the
base changes, so that it can be consumed through any identification of the fibre products, for
instance by the algebraic spaces they represent.

## Main results

* `AlgebraicGeometry.C1590Private.fibreData_of_isPullback`: fibre data on cartesian presentations
  give fibre data on the chosen fibre products.
* `AlgebraicGeometry.C1590Private.exists_openImmersion_iso_of_fibre_of_isPullback`: the statement
  above.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

/-- **Fibre data on cartesian presentations give fibre data on the chosen fibre products.** -/
theorem fibreData_of_isPullback {S T : Scheme.{u}} (t : T ⟶ S) {X Y₁ Y₂ : Scheme.{u}}
    (fX : X ⟶ S) (fY₁ : Y₁ ⟶ S) (fY₂ : Y₂ ⟶ S) [IsProper fX] [IsProper fY₁]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    {V W₁ W₂ : Scheme.{u}} (v : V ⟶ T) (w₁ : W₁ ⟶ T) (w₂ : W₂ ⟶ T) (qV : V ⟶ X)
    (r₁ : W₁ ⟶ Y₁) (r₂ : W₂ ⟶ Y₂) (hV : IsPullback qV v fX t) (hW₁ : IsPullback r₁ w₁ fY₁ t)
    (hW₂ : IsPullback r₂ w₂ fY₂ t) (m₁ : V ⟶ W₁) (m₂ : V ⟶ W₂) (hm₁ : m₁ ≫ w₁ = v)
    (hm₁r : m₁ ≫ r₁ = qV ≫ c₁) (hm₂ : m₂ ≫ w₂ = v) (hm₂r : m₂ ≫ r₂ = qV ≫ c₂) (ε : W₁ ≅ W₂)
    (hε : ε.hom ≫ w₂ = w₁) (hεm : m₁ ≫ ε.hom = m₂)
    (hdim : topologicalKrullDim V ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit m₁))
    (hR : IsZero (((Scheme.Modules.pushforward m₁).rightDerived 1).obj
      (SheafOfModules.unit V.ringCatSheaf))) :
    ∃ φ : pullback fY₁ t ≅ pullback fY₂ t, φ.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      fibreHom t fX fY₁ c₁ hc₁ ≫ φ.hom = fibreHom t fX fY₂ c₂ hc₂ ∧
      (∀ y, topologicalKrullDim ((fibreHom t fX fY₁ c₁ hc₁).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsIso (Scheme.Modules.unitToPushforwardUnit (fibreHom t fX fY₁ c₁ hc₁)) ∧
      IsZero (((Scheme.Modules.pushforward (fibreHom t fX fY₁ c₁ hc₁)).rightDerived 1).obj
        (SheafOfModules.unit (pullback fX t).ringCatSheaf)) := by
  have : IsProper c₁ := by subst hc₁; exact IsProper.of_comp c₁ fY₁
  set eV := hV.isoPullback
  set e₁ := hW₁.isoPullback
  set e₂ := hW₂.isoPullback
  have hk : ∀ (m : V ⟶ W₁) (hm : m ≫ w₁ = v) (hmr : m ≫ r₁ = qV ≫ c₁),
      eV.hom ≫ fibreHom t fX fY₁ c₁ hc₁ = m ≫ e₁.hom := fun m hm hmr => by
    apply pullback.hom_ext
    · rw [Category.assoc, fibreHom_fst, IsPullback.isoPullback_hom_fst_assoc, Category.assoc,
        IsPullback.isoPullback_hom_fst, hmr]
    · rw [Category.assoc, fibreHom_snd, IsPullback.isoPullback_hom_snd, Category.assoc,
        IsPullback.isoPullback_hom_snd, hm]
  have hk₁ := hk m₁ hm₁ hm₁r
  have hk₂ : eV.hom ≫ fibreHom t fX fY₂ c₂ hc₂ = m₂ ≫ e₂.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, fibreHom_fst, IsPullback.isoPullback_hom_fst_assoc, Category.assoc,
        IsPullback.isoPullback_hom_fst, hm₂r]
    · rw [Category.assoc, fibreHom_snd, IsPullback.isoPullback_hom_snd, Category.assoc,
        IsPullback.isoPullback_hom_snd, hm₂]
  refine ⟨e₁.symm ≪≫ ε ≪≫ e₂, ?_, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [IsPullback.isoPullback_hom_snd, hε, Iso.inv_comp_eq,
      IsPullback.isoPullback_hom_snd]
  · rw [← cancel_epi eV.hom, reassoc_of% hk₁]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hεm, hk₂]
  -- the conditions, along the isomorphism of presentations
  have hdimX : topologicalKrullDim ↥(pullback fX t) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    (Topology.IsInducing.topologicalKrullDim_le (Scheme.Hom.homeomorph eV.inv).isInducing).trans
      hdim
  have hdimF : ∀ y, topologicalKrullDim ((fibreHom t fX fY₁ c₁ hc₁).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞) := fun y =>
    (Topology.IsInducing.topologicalKrullDim_le
      ((fibreHom t fX fY₁ c₁ hc₁).fiberι y).isEmbedding.isInducing).trans hdimX
  have : IsProper (fibreHom t fX fY₁ c₁ hc₁) :=
    MorphismProperty.of_isPullback (isPullback_fibreHom_fst t fX fY₁ c₁ hc₁) inferInstance
  have H : IsPullback eV.hom m₁ (fibreHom t fX fY₁ c₁ hc₁) e₁.hom :=
    IsPullback.of_horiz_isIso ⟨hk₁⟩
  have : Flat e₁.hom := inferInstance
  have : Surjective e₁.hom := inferInstance
  obtain ⟨h0', hR'⟩ := fibreConditions_of_isPullback_of_surjective H hdimF h0 hR
  exact ⟨hdimF, h0', hR'⟩

/-! ### Reading the conclusion on arbitrary cartesian presentations -/

/-- The conclusion of [Stacks, Tag 0E89] over an open immersion `e : U ⟶ S`, read on arbitrary
cartesian presentations of the base changes: there is an isomorphism `A₁ ≅ A₂` over `U` of any two
presentations of `Y₁ ×_S U` and `Y₂ ×_S U`, compatible with `c₁` and `c₂` on any presentation of
`X ×_S U`. -/
def IsoOverOfIsPullback {S U X Y₁ Y₂ : Scheme.{u}} (e : U ⟶ S) (fX : X ⟶ S) (fY₁ : Y₁ ⟶ S)
    (fY₂ : Y₂ ⟶ S) (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) : Prop :=
  ∀ ⦃A₁ A₂ AX : Scheme.{u}⦄ (j₁ : A₁ ⟶ Y₁) (p₁ : A₁ ⟶ U) (j₂ : A₂ ⟶ Y₂) (p₂ : A₂ ⟶ U)
    (jX : AX ⟶ X) (pX : AX ⟶ U), IsPullback j₁ p₁ fY₁ e → IsPullback j₂ p₂ fY₂ e →
    IsPullback jX pX fX e →
    ∃ θ : A₁ ≅ A₂, θ.hom ≫ p₂ = p₁ ∧ ∀ (a₁ : AX ⟶ A₁) (a₂ : AX ⟶ A₂),
      a₁ ≫ j₁ = jX ≫ c₁ → a₂ ≫ j₂ = jX ≫ c₂ → a₁ ≫ θ.hom = a₂

/-- An isomorphism of the preimages of an open `U ⊆ S` compatible with `c₁` and `c₂` gives the
conclusion on arbitrary cartesian presentations over `U.ι`. -/
theorem isoOverOfIsPullback_of_preimage {S X Y₁ Y₂ : Scheme.{u}} (fX : X ⟶ S) (fY₁ : Y₁ ⟶ S)
    (fY₂ : Y₂ ⟶ S) (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (U : S.Opens)
    (ψ : (fY₁ ⁻¹ᵁ U).toScheme ≅ (fY₂ ⁻¹ᵁ U).toScheme)
    (hψ : ψ.hom ≫ (fY₂ ⁻¹ᵁ U).ι ≫ fY₂ = (fY₁ ⁻¹ᵁ U).ι ≫ fY₁)
    (hcψ : ∀ a : (fX ⁻¹ᵁ U).toScheme ⟶ (fY₁ ⁻¹ᵁ U).toScheme,
      a ≫ (fY₁ ⁻¹ᵁ U).ι = (fX ⁻¹ᵁ U).ι ≫ c₁ → a ≫ ψ.hom ≫ (fY₂ ⁻¹ᵁ U).ι = (fX ⁻¹ᵁ U).ι ≫ c₂) :
    IsoOverOfIsPullback U.ι fX fY₁ fY₂ c₁ c₂ := by
  intro A₁ A₂ AX j₁ p₁ j₂ p₂ jX pX h₁ h₂ hX
  let κ₁ := h₁.isoIsPullback _ _ (isPullback_morphismRestrict fY₁ U).flip
  let κ₂ := h₂.isoIsPullback _ _ (isPullback_morphismRestrict fY₂ U).flip
  let κX := hX.isoIsPullback _ _ (isPullback_morphismRestrict fX U).flip
  have hκ₁f : κ₁.hom ≫ (fY₁ ⁻¹ᵁ U).ι = j₁ := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hκ₁s : κ₁.hom ≫ fY₁ ∣_ U = p₁ := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hκ₂f : κ₂.hom ≫ (fY₂ ⁻¹ᵁ U).ι = j₂ := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hκ₂s : κ₂.inv ≫ p₂ = fY₂ ∣_ U := IsPullback.isoIsPullback_inv_snd _ _ _ _
  have hκXf : κX.inv ≫ jX = (fX ⁻¹ᵁ U).ι := IsPullback.isoIsPullback_inv_fst _ _ _ _
  have hψ' : ψ.hom ≫ fY₂ ∣_ U = fY₁ ∣_ U := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, hψ, morphismRestrict_ι]
  refine ⟨κ₁ ≪≫ ψ ≪≫ κ₂.symm, ?_, fun a₁ a₂ ha₁ ha₂ => ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [hκ₂s, hψ', hκ₁s]
  · have hcomp := hcψ (κX.inv ≫ a₁ ≫ κ₁.hom) (by
      rw [Category.assoc, Category.assoc, hκ₁f, ha₁, reassoc_of% hκXf])
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, ← Category.assoc, Iso.comp_inv_eq, ← cancel_mono (fY₂ ⁻¹ᵁ U).ι,
      Category.assoc, Category.assoc, Category.assoc, hκ₂f, ha₂]
    have := congrArg (κX.hom ≫ ·) hcomp
    simp only [Category.assoc, Iso.hom_inv_id_assoc] at this
    rw [this, ← hκXf, Category.assoc, Iso.hom_inv_id_assoc]

/-! ### An arbitrary base -/

/-- **Uniqueness of contractions near a point, for schemes** ([Stacks, Tag 0E89] for schemes). Let
`t : Spec K ⟶ S` be a field-valued point over `s`, let `X`, `Y₁`, `Y₂` be proper flat schemes of
finite presentation over `S` and `cᵢ : X ⟶ Yᵢ` morphisms over `S`. Let the fibres over `t` be
presented by cartesian squares `V ⟶ X`, `Wᵢ ⟶ Yᵢ` over `t` with induced `mᵢ : V ⟶ Wᵢ`. Suppose
there is `ε : W₁ ≅ W₂` over `Spec K` with `m₁ ≫ ε = m₂`, that `dim V ≤ 1`, and that
`𝒪_{W₁} ≅ m₁,*𝒪_V` and `R¹m₁,*𝒪_V = 0`. Then there is an open immersion `e : U ⟶ S` whose image
contains `s`, over which the base changes of `Y₁` and `Y₂` are isomorphic compatibly with `c₁` and
`c₂` (`AlgebraicGeometry.C1590Private.IsoOverOfIsPullback`). -/
theorem exists_openImmersion_iso_of_fibre_of_isPullback {S : Scheme.{u}} {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ S) (s : S) (hs : t (IsLocalRing.closedPoint K) = s)
    {X Y₁ Y₂ : Scheme.{u}} (fX : X ⟶ S) (fY₁ : Y₁ ⟶ S) (fY₂ : Y₂ ⟶ S)
    [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX] [IsProper fY₁] [Flat fY₁]
    [LocallyOfFinitePresentation fY₁] [IsProper fY₂] [Flat fY₂] [LocallyOfFinitePresentation fY₂]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    {V W₁ W₂ : Scheme.{u}} (v : V ⟶ Spec (.of K)) (w₁ : W₁ ⟶ Spec (.of K))
    (w₂ : W₂ ⟶ Spec (.of K)) (qV : V ⟶ X) (r₁ : W₁ ⟶ Y₁) (r₂ : W₂ ⟶ Y₂)
    (hV : IsPullback qV v fX t) (hW₁ : IsPullback r₁ w₁ fY₁ t) (hW₂ : IsPullback r₂ w₂ fY₂ t)
    (m₁ : V ⟶ W₁) (m₂ : V ⟶ W₂) (hm₁ : m₁ ≫ w₁ = v) (hm₁r : m₁ ≫ r₁ = qV ≫ c₁)
    (hm₂ : m₂ ≫ w₂ = v) (hm₂r : m₂ ≫ r₂ = qV ≫ c₂) (ε : W₁ ≅ W₂) (hε : ε.hom ≫ w₂ = w₁)
    (hεm : m₁ ≫ ε.hom = m₂) (hdim : topologicalKrullDim V ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit m₁))
    (hR : IsZero (((Scheme.Modules.pushforward m₁).rightDerived 1).obj
      (SheafOfModules.unit V.ringCatSheaf))) :
    ∃ (U : Scheme.{u}) (e : U ⟶ S), IsOpenImmersion e ∧ s ∈ Set.range e ∧
      IsoOverOfIsPullback e fX fY₁ fY₂ c₁ c₂ := by
  obtain ⟨φ, hφ, hφc, hdim', h0', hR'⟩ := fibreData_of_isPullback t fX fY₁ fY₂ c₁ hc₁ c₂ hc₂
    v w₁ w₂ qV r₁ r₂ hV hW₁ hW₂ m₁ m₂ hm₁ hm₁r hm₂ hm₂r ε hε hεm hdim h0 hR
  have : IsProper c₁ := by subst hc₁; exact IsProper.of_comp c₁ fY₁
  -- an affine neighbourhood of `s`
  obtain ⟨V₀, hV₀, hsV₀, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  have : IsAffine V₀.toScheme := hV₀
  have ht : Set.range t ⊆ Set.range V₀.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim x (IsLocalRing.closedPoint K), hs]
    exact hsV₀
  set t' := IsOpenImmersion.lift V₀.ι t ht
  have ht' : t' ≫ V₀.ι = t := IsOpenImmersion.lift_fac _ _ _
  -- the restricted configuration
  set fX' := fX ∣_ V₀
  set fY₁' := fY₁ ∣_ V₀
  set fY₂' := fY₂ ∣_ V₀
  have sqX := (isPullback_morphismRestrict fX V₀).flip
  have sqY₁ := (isPullback_morphismRestrict fY₁ V₀).flip
  have sqY₂ := (isPullback_morphismRestrict fY₂ V₀).flip
  have : IsProper fX' := MorphismProperty.of_isPullback sqX inferInstance
  have : Flat fX' := MorphismProperty.of_isPullback sqX inferInstance
  have : LocallyOfFinitePresentation fX' := MorphismProperty.of_isPullback sqX inferInstance
  have : IsProper fY₁' := MorphismProperty.of_isPullback sqY₁ inferInstance
  have : Flat fY₁' := MorphismProperty.of_isPullback sqY₁ inferInstance
  have : LocallyOfFinitePresentation fY₁' := MorphismProperty.of_isPullback sqY₁ inferInstance
  have : IsProper fY₂' := MorphismProperty.of_isPullback sqY₂ inferInstance
  have : Flat fY₂' := MorphismProperty.of_isPullback sqY₂ inferInstance
  have : LocallyOfFinitePresentation fY₂' := MorphismProperty.of_isPullback sqY₂ inferInstance
  have hle : ∀ {Y : Scheme.{u}} (fY : Y ⟶ S) (c : X ⟶ Y), c ≫ fY = fX →
      fX ⁻¹ᵁ V₀ ≤ c ⁻¹ᵁ fY ⁻¹ᵁ V₀ := fun fY c hc => by
    rw [← Scheme.Hom.comp_preimage, hc]
  set c₁' := c₁.resLE (fY₁ ⁻¹ᵁ V₀) (fX ⁻¹ᵁ V₀) (hle fY₁ c₁ hc₁)
  set c₂' := c₂.resLE (fY₂ ⁻¹ᵁ V₀) (fX ⁻¹ᵁ V₀) (hle fY₂ c₂ hc₂)
  have hcc₁ : c₁' ≫ (fY₁ ⁻¹ᵁ V₀).ι = (fX ⁻¹ᵁ V₀).ι ≫ c₁ := Scheme.Hom.resLE_comp_ι _ _
  have hcc₂ : c₂' ≫ (fY₂ ⁻¹ᵁ V₀).ι = (fX ⁻¹ᵁ V₀).ι ≫ c₂ := Scheme.Hom.resLE_comp_ι _ _
  have hc₁' : c₁' ≫ fY₁' = fX' := by
    rw [← cancel_mono V₀.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hcc₁, hc₁,
      morphismRestrict_ι]
  have hc₂' : c₂' ≫ fY₂' = fX' := by
    rw [← cancel_mono V₀.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hcc₂, hc₂,
      morphismRestrict_ι]
  have hsq₁ : IsPullback (fX ⁻¹ᵁ V₀).ι c₁' c₁ (fY₁ ⁻¹ᵁ V₀).ι :=
    IsPullback.of_bot (by rw [hc₁', hc₁]; exact sqX) hcc₁.symm sqY₁
  have hsq₂ : IsPullback (fX ⁻¹ᵁ V₀).ι c₂' c₂ (fY₂ ⁻¹ᵁ V₀).ι :=
    IsPullback.of_bot (by rw [hc₂', hc₂]; exact sqX) hcc₂.symm sqY₂
  -- the fibre data, restricted
  have hst : t' ≫ V₀.ι = 𝟙 _ ≫ t := by rw [ht', Category.id_comp]
  have PY₁ := isPullback_fibreMap hst fY₁ fY₁' (fY₁ ⁻¹ᵁ V₀).ι sqY₁.w.symm sqY₁
  have PY₂ := isPullback_fibreMap hst fY₂ fY₂' (fY₂ ⁻¹ᵁ V₀).ι sqY₂.w.symm sqY₂
  have H₁ := isPullback_fibreHom hst fX fY₁ fX' fY₁' (fX ⁻¹ᵁ V₀).ι (fY₁ ⁻¹ᵁ V₀).ι sqX.w.symm
    sqY₁.w.symm c₁ hc₁ c₁' hc₁' hcc₁ hsq₁
  have H₂ := isPullback_fibreHom hst fX fY₂ fX' fY₂' (fX ⁻¹ᵁ V₀).ι (fY₂ ⁻¹ᵁ V₀).ι sqX.w.symm
    sqY₂.w.symm c₂ hc₂ c₂' hc₂' hcc₂ hsq₂
  set n₁ := fibreMap hst fY₁ fY₁' (fY₁ ⁻¹ᵁ V₀).ι sqY₁.w.symm
  set n₂ := fibreMap hst fY₂ fY₂' (fY₂ ⁻¹ᵁ V₀).ι sqY₂.w.symm
  have : IsIso n₁ := PY₁.isIso_fst_of_isIso
  have : IsIso n₂ := PY₂.isIso_fst_of_isIso
  have : Flat n₁ := inferInstance
  have : IsProper (fibreHom t fX fY₁ c₁ hc₁) :=
    MorphismProperty.of_isPullback (isPullback_fibreHom_fst t fX fY₁ c₁ hc₁) inferInstance
  obtain ⟨h0'', hR''⟩ := fibreConditions_of_isPullback H₁ hdim' h0' hR'
  have hdim'' : ∀ y, topologicalKrullDim ((fibreHom t' fX' fY₁' c₁' hc₁').fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞) := fun y =>
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.topologicalKrullDim_fiber_le_of_isPullback H₁ 1
      y (hdim' _)
  let φ' : pullback fY₁' t' ≅ pullback fY₂' t' := asIso n₁ ≪≫ φ ≪≫ (asIso n₂).symm
  have hn₁ : n₁ ≫ pullback.snd fY₁ t = pullback.snd fY₁' t' := by
    rw [fibreMap_snd, Category.comp_id]
  have hn₂ : n₂ ≫ pullback.snd fY₂ t = pullback.snd fY₂' t' := by
    rw [fibreMap_snd, Category.comp_id]
  have hφ' : φ'.hom ≫ pullback.snd fY₂' t' = pullback.snd fY₁' t' := by
    simp only [φ', Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc]
    rw [← hn₂, IsIso.inv_hom_id_assoc, hφ, hn₁]
  have hφc' : fibreHom t' fX' fY₁' c₁' hc₁' ≫ φ'.hom = fibreHom t' fX' fY₂' c₂' hc₂' := by
    simp only [φ', Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom]
    rw [← cancel_mono n₂]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← H₂.w, ← reassoc_of% H₁.w, hφc]
  -- the affine case over `V₀`, and the conclusion
  obtain ⟨U', hsU', ψ', hψ', hcψ'⟩ := exists_open_iso_of_fieldFibre_of_isAffine t' ⟨s, hsV₀⟩
    (Subtype.ext ((congrArg (fun g => g.base (IsLocalRing.closedPoint K)) ht').trans hs))
    fX' fY₁' fY₂' c₁' hc₁' c₂' hc₂' φ' hφ' hφc' hdim'' h0'' hR''
  have hconv := isoOverOfIsPullback_of_preimage fX' fY₁' fY₂' c₁' c₂' U' ψ' hψ' hcψ'
  refine ⟨U', U'.ι ≫ V₀.ι, inferInstance, ⟨⟨⟨s, hsV₀⟩, hsU'⟩, rfl⟩, ?_⟩
  intro A₁ A₂ AX j₁ p₁ j₂ p₂ jX pX h₁ h₂ hX
  -- the presentations over `V₀`
  have hres : ∀ {Y : Scheme.{u}} (fY : Y ⟶ S) {A : Scheme.{u}} (j : A ⟶ Y) (p : A ⟶ U'),
      IsPullback j p fY (U'.ι ≫ V₀.ι) → ∀ a, fY (j a) ∈ V₀ := fun fY A j p h a => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact ((p ≫ U'.ι) a).2
  have hlift : ∀ {Y : Scheme.{u}} (fY : Y ⟶ S) {A : Scheme.{u}} (j : A ⟶ Y) (p : A ⟶ U')
      (h : IsPullback j p fY (U'.ι ≫ V₀.ι)),
      IsPullback (toPreimage fY V₀ j (hres fY j p h)) p (fY ∣_ V₀) U'.ι := fun fY A j p h => by
    refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict fY V₀).flip
    · rw [toPreimage_ι]
      exact h
    · rw [← cancel_mono V₀.ι, Category.assoc, morphismRestrict_ι, toPreimage_ι_assoc, h.w,
        Category.assoc]
  obtain ⟨θ, hθ, hθc⟩ := hconv _ _ _ _ _ _ (hlift fY₁ j₁ p₁ h₁) (hlift fY₂ j₂ p₂ h₂)
    (hlift fX jX pX hX)
  refine ⟨θ, hθ, fun a₁ a₂ ha₁ ha₂ => hθc a₁ a₂ ?_ ?_⟩
  · rw [← cancel_mono (fY₁ ⁻¹ᵁ V₀).ι, Category.assoc, toPreimage_ι, ha₁, Category.assoc, hcc₁,
      toPreimage_ι_assoc]
  · rw [← cancel_mono (fY₂ ⁻¹ᵁ V₀).ι, Category.assoc, toPreimage_ι, ha₂, Category.assoc, hcc₂,
      toPreimage_ι_assoc]

end AlgebraicGeometry.C1590Private

end
