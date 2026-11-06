module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFaithfulGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism

/-!
# Fullness of base change along a thickening of arbitrary order

Let `G ⊂ Y` be a thickening of algebraic spaces over a scheme `S`, of arbitrary order. Base change
along the inclusion of `G` is full, hence fully faithful, from the spaces-étale site of `Y` to that
of `G`; this is the full faithfulness part of Stacks 05ZH. Two statements proved here do not
mention a thickening: the graph of a morphism into a space unramified over the base is an open
immersion, and an étale morphism whose base change along a morphism surjective on points is an
isomorphism is itself an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsThickening`: base change along the
  inclusion of a thickening of arbitrary order is fully faithful on spaces-étale sites.

## Main results

* `AlgebraicGeometry.Space.isPullback_fst_pullback_fst`: a fibre product `T ×_Z M` is the base
  change along `c : T ⟶ M` of the first projection of `M ×_Z M`.
* `AlgebraicGeometry.Space.isOpenImmersion_graph_of_isUnramified`: the graph of a morphism
  `c : T ⟶ M` over a base `Z`, as a morphism from `T` into a fibre product `T ×_Z M`, is an
  open immersion as soon as `M ⟶ Z` is unramified.
* `AlgebraicGeometry.Space.mono_of_isPullback_of_isIso_of_isSurjective`: an unramified morphism
  whose base change along a morphism surjective on points is an isomorphism is a monomorphism.
* `AlgebraicGeometry.Space.isIso_of_isEtale_of_isPullback_of_isIso`: an étale morphism whose
  base change along a morphism surjective on points is an isomorphism is itself an
  isomorphism.
* `AlgebraicGeometry.Space.full_spacesBaseChange_of_isThickening`: base change along the
  inclusion of a thickening of arbitrary order is full on spaces-étale sites.

## References

* [Stacks Project, Tag 02X3](https://stacks.math.columbia.edu/tag/02X3)
* [Stacks Project, Tag 02X8](https://stacks.math.columbia.edu/tag/02X8)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S`, supplied directly: instance search
for them now times out. -/
local instance (priority := high) hasLimit_cospan_presheaf_spacesEtaleFullGeneral
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/-! ### The graph of a morphism into a space unramified over the base -/

section Graph

variable {T M Z P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A fibre product `T ×_Z M` is the base change along `c : T ⟶ M` of the first projection of
`M ×_Z M`, for any `c` over `Z`. -/
theorem isPullback_fst_pullback_fst (u : M ⟶ Z) {t : T ⟶ Z} {q₁ : P ⟶ T} {q₂ : P ⟶ M}
    (pb : IsPullback q₁ q₂ t u) (c : T ⟶ M) (hc : c ≫ u = t) :
    IsPullback q₁ (pullback.lift (q₁ ≫ c) q₂ (by rw [Category.assoc, hc, pb.w])) c
      (pullback.fst u u) :=
  IsPullback.of_bot (by rwa [pullback.lift_snd, hc]) (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback u u)

/-- Let `u : M ⟶ Z` be an unramified morphism of algebraic spaces over `S`, let `t : T ⟶ Z` be a
morphism with a fibre product `(P, q₁, q₂)` of `t` and `u`, and let `c : T ⟶ M` be a morphism over
`Z`. A morphism `γ : T ⟶ P` whose two components are the identity of `T` and `c` — the graph of `c`
— is an open immersion. -/
@[sga "1 I 3.4" "more general"]
theorem isOpenImmersion_graph_of_isUnramified (hM : IsAlgebraicSpace B S hS M)
    (hZ : IsAlgebraicSpace B S hS Z) (u : M ⟶ Z) (hu : IsUnramified B S hS u)
    {t : T ⟶ Z} {q₁ : P ⟶ T} {q₂ : P ⟶ M} (pb : IsPullback q₁ q₂ t u)
    (c : T ⟶ M) (hc : c ≫ u = t) (γ : T ⟶ P) (hγ₁ : γ ≫ q₁ = 𝟙 T) (hγ₂ : γ ≫ q₂ = c) :
    IsOpenImmersion B S hS γ := by
  have hright := isPullback_fst_pullback_fst B S hS u pb c hc
  have hcomm : γ ≫ pullback.lift (q₁ ≫ c) q₂ (by rw [Category.assoc, hc, pb.w]) =
      c ≫ pullback.diagonal u := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hγ₁, Category.id_comp,
        Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, hγ₂, Category.assoc, pullback.diagonal_snd,
        Category.comp_id]
  have houter : IsPullback (γ ≫ q₁) c c (pullback.diagonal u ≫ pullback.fst u u) := by
    rw [hγ₁, pullback.diagonal_fst]
    exact IsPullback.of_id_fst
  exact (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback
    (IsPullback.of_right houter hcomm hright).flip
    (isOpenImmersion_diagonal_of_isUnramified B S hS hM hZ u hu)

end Graph

/-! ### Descending the property of being an isomorphism along a point-surjective base change -/

section IsoDescent

variable {Γ T Γ' T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An unramified morphism `h : Γ ⟶ T` of algebraic spaces over `S` whose base change along a
morphism `g : T' ⟶ T` surjective on points is an isomorphism is a monomorphism. -/
theorem mono_of_isPullback_of_isIso_of_isSurjective (hΓ : IsAlgebraicSpace B S hS Γ)
    (hT : IsAlgebraicSpace B S hS T) (hT' : IsAlgebraicSpace B S hS T')
    {h : Γ ⟶ T} (hh : IsUnramified B S hS h) {h' : Γ' ⟶ T'} {q : Γ' ⟶ Γ} {g : T' ⟶ T}
    (sq : IsPullback h' q g h) (hiso : IsIso h') (hg : IsSurjective B S hS g) :
    Mono h := by
  have key : ∀ {U : BigFppfOver B S hS} (α β : yoneda.obj U ⟶ Γ),
      α ≫ h = β ≫ h → α = β := by
    intro U α β hαβ
    have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
    have hZsq : IsPullback (pullback.fst (α ≫ h) g) (pullback.snd (α ≫ h) g) (α ≫ h) g :=
      IsPullback.of_hasPullback (α ≫ h) g
    have hZalg : IsAlgebraicSpace B S hS (pullback (α ≫ h) g) :=
      isAlgebraicSpace_of_isPullback hUalg hT' hT.isSheaf hT.diagonal_representable hZsq
    let Usp : AlgebraicSpaces B S hS := ⟨yoneda.obj U, hUalg⟩
    let Tsp : AlgebraicSpaces B S hS := ⟨T, hT⟩
    let T'sp : AlgebraicSpaces B S hS := ⟨T', hT'⟩
    let Zsp : AlgebraicSpaces B S hS := ⟨pullback (α ≫ h) g, hZalg⟩
    let zf : Zsp ⟶ Usp := ObjectProperty.homMk (pullback.fst (α ≫ h) g)
    let zs : Zsp ⟶ T'sp := ObjectProperty.homMk (pullback.snd (α ≫ h) g)
    let ah : Usp ⟶ Tsp := ObjectProperty.homMk (α ≫ h)
    let gs : T'sp ⟶ Tsp := ObjectProperty.homMk g
    have hZsp : IsPullback zs zf gs ah :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _) hZsq.flip
    have hp : IsSurjective B S hS (pullback.fst (α ≫ h) g) :=
      isSurjective_of_isPullback B S hS hZsp hg
    have hl₁ : pullback.snd (α ≫ h) g ≫ g = (pullback.fst (α ≫ h) g ≫ α) ≫ h := by
      rw [Category.assoc, hZsq.w]
    have hl₂ : pullback.snd (α ≫ h) g ≫ g = (pullback.fst (α ≫ h) g ≫ β) ≫ h := by
      rw [Category.assoc, ← hαβ, hZsq.w]
    have hpe : pullback.fst (α ≫ h) g ≫ α = pullback.fst (α ≫ h) g ≫ β := by
      have e₁ : sq.lift _ _ hl₁ ≫ q = pullback.fst (α ≫ h) g ≫ α :=
        IsPullback.lift_snd sq _ _ hl₁
      have e₂ : sq.lift _ _ hl₂ ≫ q = pullback.fst (α ≫ h) g ≫ β :=
        IsPullback.lift_snd sq _ _ hl₂
      have : Mono h' := IsIso.mono_of_iso h'
      have e₃ : sq.lift _ _ hl₁ = sq.lift _ _ hl₂ :=
        (cancel_mono h').mp ((sq.lift_fst _ _ hl₁).trans (sq.lift_fst _ _ hl₂).symm)
      rw [← e₁, ← e₂, e₃]
    exact eq_of_comp_eq_of_isSurjective B S hS hΓ hT h hh α β hαβ _ hp hpe
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  intro x y hxy
  have hαβ : (yonedaEquiv.symm x : yoneda.obj U.unop ⟶ Γ) ≫ h =
      (yonedaEquiv.symm y : yoneda.obj U.unop ⟶ Γ) ≫ h :=
    yonedaEquiv.injective (by
      rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  simpa using congrArg (fun k ↦ (yonedaEquiv k : Γ.obj (Opposite.op U.unop))) (key _ _ hαβ)

/-- An étale morphism `h : Γ ⟶ T` of algebraic spaces over `S` whose base change along a morphism
`g : T' ⟶ T` surjective on points is an isomorphism is an isomorphism. -/
theorem isIso_of_isEtale_of_isPullback_of_isIso (hΓ : IsAlgebraicSpace B S hS Γ)
    (hT : IsAlgebraicSpace B S hS T) (hT' : IsAlgebraicSpace B S hS T')
    {h : Γ ⟶ T} (hh : IsEtale B S hS h) {h' : Γ' ⟶ T'} {q : Γ' ⟶ Γ} {g : T' ⟶ T}
    (sq : IsPullback h' q g h) (hiso : IsIso h') (hg : IsSurjective B S hS g) :
    IsIso h := by
  have hsurj : IsSurjective B S hS h := by
    intro x
    obtain ⟨y, rfl⟩ := hg x
    refine ⟨pointsMap B S hS Γ' q (pointsMap B S hS T' (inv h') y), ?_⟩
    simp only [← pointsMap_comp_apply]
    rw [Category.assoc, ← sq.w, IsIso.inv_hom_id_assoc]
  exact isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS hΓ hT h hh
    (universallyInjective_of_mono B S hS h (mono_of_isPullback_of_isIso_of_isSurjective B S hS hΓ
      hT hT' (isUnramified_of_isEtale B S hS hh) sq hiso hg)) hsurj

end IsoDescent

/-! ### Descending a morphism of base changes along a thickening of arbitrary order -/

section Descent

variable {Yp A M A' M' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Let `G ⊂ Yp` be a thickening of algebraic spaces over `S`, of arbitrary order, let
`v' : A ⟶ Yp` and `v : M ⟶ Yp` be objects over `Yp` with a fibre product `(W, p₁, p₂)` whose first
projection is étale, and let `(A', πA, xA)` and `(M', πM, xM)` be base changes of `A` and `M` along
the inclusion of the thickening, with `xM` unramified. Then every morphism `c₀ : A' ⟶ M'` over the
thickening is the base change of a morphism `a : A ⟶ M` over `Yp`. -/
private theorem exists_hom_baseChange_eq_of_isThickening
    (hY : IsAlgebraicSpace B S hS Yp) (hA : IsAlgebraicSpace B S hS A)
    (hA' : IsAlgebraicSpace B S hS A') (hM' : IsAlgebraicSpace B S hS M')
    (hW : IsAlgebraicSpace B S hS W)
    {G : Subfunctor Yp} (hG : IsThickening B S hS ⟨Yp, hY⟩ G)
    {v' : A ⟶ Yp} {v : M ⟶ Yp} {p₁ : W ⟶ A} {p₂ : W ⟶ M}
    (hWsq : IsPullback p₁ p₂ v' v) (hp₁ : IsEtale B S hS p₁)
    {wmap : W ⟶ Yp} (hw : p₁ ≫ v' = wmap)
    {πA : A' ⟶ A} {xA : A' ⟶ G.toFunctor} (sqA : IsPullback πA xA v' G.ι)
    {πM : M' ⟶ M} {xM : M' ⟶ G.toFunctor} (sqM : IsPullback πM xM v G.ι)
    (hxM : IsUnramified B S hS xM) (c₀ : A' ⟶ M') (hc₀ : c₀ ≫ xM = xA) :
    ∃ a : A ⟶ M, a ≫ v = v' ∧ πA ≫ a = c₀ ≫ πM := by
  have hXp : IsAlgebraicSpace B S hS G.toFunctor := hG.1.1
  have hGW : IsThickening B S hS (⟨W, hW⟩ : AlgebraicSpaces B S hS) (G.preimage wmap) :=
    isThickening_preimage B S hS G
      (ObjectProperty.homMk wmap : (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Yp, hY⟩) hG
  have sqW : IsPullback (G.preimage wmap).ι (G.fromPreimage wmap) wmap G.ι :=
    (Subfunctor.isPullback_preimage wmap G).flip
  obtain ⟨r₁, hr₁A, hr₁X⟩ : ∃ r₁ : (G.preimage wmap).toFunctor ⟶ A',
      r₁ ≫ πA = (G.preimage wmap).ι ≫ p₁ ∧ r₁ ≫ xA = G.fromPreimage wmap :=
    ⟨sqA.lift ((G.preimage wmap).ι ≫ p₁) (G.fromPreimage wmap)
      (by rw [Category.assoc, hw]; exact sqW.w),
      sqA.lift_fst _ _ _, sqA.lift_snd _ _ _⟩
  obtain ⟨r₂, hr₂A, hr₂X⟩ : ∃ r₂ : (G.preimage wmap).toFunctor ⟶ M',
      r₂ ≫ πM = (G.preimage wmap).ι ≫ p₂ ∧ r₂ ≫ xM = G.fromPreimage wmap :=
    ⟨sqM.lift ((G.preimage wmap).ι ≫ p₂) (G.fromPreimage wmap)
      (by rw [Category.assoc, ← hWsq.w, hw]; exact sqW.w),
      sqM.lift_fst _ _ _, sqM.lift_snd _ _ _⟩
  have s₁ : IsPullback (G.preimage wmap).ι r₁ p₁ πA :=
    IsPullback.of_bot (by rw [hr₁X, hw]; exact sqW) hr₁A.symm sqA
  have sqProd : IsPullback r₁ r₂ xA xM :=
    (IsPullback.of_right (by rw [hr₂A, ← sqA.w]; exact s₁.paste_horiz hWsq.flip)
      (by rw [hr₂X, hr₁X]) sqM).flip
  obtain ⟨γ, hγ₁, hγ₂⟩ : ∃ γ : A' ⟶ (G.preimage wmap).toFunctor,
      γ ≫ r₁ = 𝟙 A' ∧ γ ≫ r₂ = c₀ :=
    ⟨sqProd.lift (𝟙 A') c₀ (by rw [Category.id_comp, hc₀]),
      sqProd.lift_fst _ _ _, sqProd.lift_snd _ _ _⟩
  have hγopen : IsOpenImmersion B S hS γ :=
    isOpenImmersion_graph_of_isUnramified B S hS hM' hXp xM hxM sqProd c₀ hc₀ γ hγ₁ hγ₂
  have _ : Mono γ := mono_of_presheaf_isOpenImmersion hγopen
  have hinv : inv (Subfunctor.toRange γ) = (Subfunctor.range γ).ι ≫ r₁ :=
    IsIso.inv_eq_of_hom_inv_id (by rw [← Category.assoc, Subfunctor.toRange_ι, hγ₁])
  obtain ⟨U', hU', k, sqQ⟩ := exists_isOpenSubspace_isPullback_ι_of_isThickening B S hS hGW
    (Subfunctor.range γ) (isOpenSubspace_subfunctorRange B S hS hA' hγopen)
  have hkiso : IsIso ((Subfunctor.range γ).ι ≫ r₁) := by rw [← hinv]; infer_instance
  have hπAsurj : IsSurjective B S hS πA :=
    isSurjective_of_isPullback B S hS
      (p := (ObjectProperty.homMk xA :
        (⟨A', hA'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G.toFunctor, hXp⟩))
      (q := (ObjectProperty.homMk πA : (⟨A', hA'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨A, hA⟩))
      (g := (ObjectProperty.homMk G.ι :
        (⟨G.toFunctor, hXp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Yp, hY⟩))
      (f := (ObjectProperty.homMk v' : (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Yp, hY⟩))
      (IsPullback.of_map_of_faithful (ObjectProperty.ι _) sqA.flip) hG.2
  have hIso : IsIso (U'.ι ≫ p₁) :=
    isIso_of_isEtale_of_isPullback_of_isIso B S hS hU'.1 hA hA'
      (isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS hU'.2) hp₁)
      (sqQ.paste_vert s₁).flip hkiso hπAsurj
  have hπA : πA = Subfunctor.toRange γ ≫ k ≫ U'.ι ≫ p₁ := by
    have h₁ : inv (Subfunctor.toRange γ) ≫ πA = k ≫ U'.ι ≫ p₁ := by
      rw [hinv]; exact (sqQ.paste_vert s₁).flip.w
    rw [← h₁, IsIso.hom_inv_id_assoc]
  have hinvfac : πA ≫ inv (U'.ι ≫ p₁) = Subfunctor.toRange γ ≫ k := by
    rw [hπA, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hk : k ≫ U'.ι ≫ p₂ = (Subfunctor.range γ).ι ≫ r₂ ≫ πM := by
    rw [← Category.assoc, sqQ.w, Category.assoc, ← hr₂A]
  refine ⟨inv (U'.ι ≫ p₁) ≫ U'.ι ≫ p₂, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← hWsq.w, ← Category.assoc U'.ι p₁ v',
      IsIso.inv_hom_id_assoc]
  · rw [← Category.assoc, hinvfac, Category.assoc, hk, ← Category.assoc,
      Subfunctor.toRange_ι, ← Category.assoc, hγ₂]

end Descent

/-! ### Fullness of base change at a thickening of arbitrary order -/

section Full

variable {Y : AlgebraicSpaces B S hS}

/-- Every morphism between two base changes along the inclusion of a thickening of arbitrary order
is the base change of a morphism of the spaces-étale site of the ambient space. -/
private theorem exists_map_eq_spacesBaseChange_of_isThickening {G : Subfunctor Y.1}
    (hG : IsThickening B S hS Y G)
    (D : SpacesBaseChange B S hS (IsThickening.inclusion B S hS hG))
    (V' V : SpacesEtale B S hS Y) (c : D.functor.obj V' ⟶ D.functor.obj V) :
    ∃ a : V' ⟶ V, D.functor.map a = c := by
  have hWsq : IsPullback (pullback.fst V'.1.hom.hom V.1.hom.hom)
      (pullback.snd V'.1.hom.hom V.1.hom.hom) V'.1.hom.hom V.1.hom.hom :=
    IsPullback.of_hasPullback _ _
  have hW : IsAlgebraicSpace B S hS (pullback V'.1.hom.hom V.1.hom.hom) :=
    isAlgebraicSpace_of_isPullback V'.1.left.property V.1.left.property Y.property.isSheaf
      Y.property.diagonal_representable hWsq
  have hp₁ : IsEtale B S hS (pullback.fst V'.1.hom.hom V.1.hom.hom) :=
    isEtale_of_isPullback B S hS
      (ObjectProperty.homMk (pullback.snd V'.1.hom.hom V.1.hom.hom) :
        (⟨pullback V'.1.hom.hom V.1.hom.hom, hW⟩ : AlgebraicSpaces B S hS) ⟶ V.1.left)
      (ObjectProperty.homMk (pullback.fst V'.1.hom.hom V.1.hom.hom)) V.1.hom V'.1.hom
      (IsPullback.of_map_of_faithful (ObjectProperty.ι _) hWsq.flip) V.property
  obtain ⟨a, haV, haπ⟩ := exists_hom_baseChange_eq_of_isThickening B S hS Y.property
    V'.1.left.property (D.functor.obj V').1.left.property (D.functor.obj V).1.left.property
    hW hG hWsq hp₁ rfl (AlgebraicSpaces.isPullback_hom B S hS (D.isPullback V'))
    (AlgebraicSpaces.isPullback_hom B S hS (D.isPullback V))
    (isUnramified_of_isEtale B S hS (D.functor.obj V).property) c.hom.left.hom
    (congrArg (fun k ↦ k.hom) (Over.w c.hom))
  have hα : (ObjectProperty.homMk a : V'.1.left ⟶ V.1.left) ≫ V.1.hom = V'.1.hom :=
    ObjectProperty.hom_ext _ haV
  refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) hα), ?_⟩
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ((D.isPullback V).hom_ext ?_ ?_))
  · exact (D.projection.naturality
      (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) hα) : V' ⟶ V)).trans
      (ObjectProperty.hom_ext _ haπ)
  · exact (Over.w (D.functor.map
      (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) hα))).hom).trans
      (Over.w c.hom).symm

/-- Let `G ⊂ Y` be a thickening of algebraic spaces over `S`, of arbitrary order. Base change along
the inclusion, `V ↦ G ×_Y V`, is full from the spaces-étale site of `Y` to that of `G`. -/
@[stacks 05ZH "FULLNESS ONLY, at a thickening of ARBITRARY order. Together with \
`AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isThickening` this gives FULL \
FAITHFULNESS at arbitrary order, bundled as \
`AlgebraicGeometry.Space.fullyFaithfulSpacesBaseChangeOfIsThickening`; ESSENTIAL \
SURJECTIVITY is not covered here; it is proved at arbitrary order in \
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening`, and the equivalence in \
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening`. The \
library's other fullness statement, \
`AlgebraicGeometry.Space.full_spacesBaseChange_of_isFirstOrderThickening`, is restricted to \
first order because it goes through the square-zero lifting property of Stacks 0611; this one \
reproduces the source's graph argument instead, and the source's integrality and universal \
injectivity hypotheses are not needed beyond what a thickening already gives"]
theorem full_spacesBaseChange_of_isThickening {G : Subfunctor Y.1}
    (hG : IsThickening B S hS Y G) :
    (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.Full where
  map_surjective {V' V} c :=
    exists_map_eq_spacesBaseChange_of_isThickening B S hS hG
      (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)) V' V c

/-- Let `G ⊂ Y` be a thickening of algebraic spaces over `S`, of arbitrary order. Base change along
the inclusion, `V ↦ G ×_Y V`, is fully faithful from the spaces-étale site of `Y` to that of
`G`. -/
@[stacks 05ZH "FULL FAITHFULNESS ONLY, at a thickening of ARBITRARY order; ESSENTIAL \
SURJECTIVITY is not covered here, and is proved at arbitrary order in \
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening`"]
noncomputable def fullyFaithfulSpacesBaseChangeOfIsThickening {G : Subfunctor Y.1}
    (hG : IsThickening B S hS Y G) :
    (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.FullyFaithful :=
  letI := full_spacesBaseChange_of_isThickening B S hS hG
  letI := faithful_spacesBaseChange_of_isThickening B S hS hG
  Functor.FullyFaithful.ofFullyFaithful _

end Full

end AlgebraicGeometry.Space

end
