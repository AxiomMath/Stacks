module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.EtaleSquareGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.GluedCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.DenseOpenProperExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianOfFiniteTypeOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformOverAdmissibleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation

/-!
# Compactifications glue across an elementary distinguished square

This file proves Stacks 0F4B, in the repaired form described in
`StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.EtaleSquareGluing`: over a
quasi-compact and quasi-separated algebraic space `Y` of finite type over `Spec ℤ`, let `U` be
separated and of finite type over `Y` and `(U₂ ⊆ U, f : U₁ ⟶ U)` an elementary distinguished
square such that `U₁` and `U₂` have compactifications over `Y`. Then `U` has a compactification
over `Y`.

The proof follows the source. Compactify `U₂` by `X₂`, which may be taken with `U₂`
scheme-theoretically dense; by Stacks 0F4A, after `Uᵢ`-admissible blowups of the
compactifications `Xᵢ` there are opens `Vᵢ ⊇ Uᵢ` with proper `ψᵢ : Vᵢ ⟶ U` extending `Uᵢ ⟶ U`.
On the side of `U₁` the chart `N ⊆ X₁` of the repair gives the separated `W₁ = U ⊔_{U₁} N`; on the
side of `U₂`, after the blowup of Stacks 0F48 applied to the closure of `V₁ ×_U V₂` in
`X₁ ×_Y X₂`, the separated `W₂ = U ⊔_{U₂} (X₂ ∖ closure (V₂ ∖ U₂))`. Valuation rings extend to
`W₁` or to `W₂`, and Stacks 088Q and 089G conclude.

## Main results

* `AlgebraicGeometry.Space.HasCompactification.exists_isSchemeTheoreticallyDense`: a
  compactification may be taken with dense image.
* `AlgebraicGeometry.Space.denseRange_of_isAdmissibleBlowup`: density survives an admissible
  blowup and restriction to an open subspace.

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
* [B. Conrad, M. Lieblich, M. Olsson, *Nagata compactification for algebraic spaces*][CLO]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- **A compactification may be taken with scheme-theoretically dense image.** If `f : U ⟶ Y`
has a compactification `U ⟶ X ⟶ Y`, then the scheme-theoretic image of `U` in `X` is a
compactification in which `U` is scheme-theoretically dense (Stacks 088G). -/
theorem HasCompactification.exists_isSchemeTheoreticallyDense
    {U Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hY : IsAlgebraicSpace B S hS Y) {f : U ⟶ Y}
    (hf : HasCompactification B S hS f) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j : U ⟶ X) (p : X ⟶ Y),
      IsAlgebraicSpace B S hS X ∧ IsOpenImmersion B S hS j ∧ IsQuasiCompact B S hS j ∧
        IsProper B S hS p ∧ j ≫ p = f ∧
        IsSchemeTheoreticallyDense B S hS (Subfunctor.range j) := by
  obtain ⟨X, j, p, hX, hj, hjqc, hp, rfl⟩ := hf
  obtain ⟨hopen, -, -, hdense, -⟩ :=
    isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced B S hS hU hX j
      (isImmersion_of_isOpenImmersion B S hS hj) (Or.inl hjqc)
  have hIc := isClosedSubspace_schemeTheoreticImageSubfunctor B S hS j hX
  have : Mono (schemeTheoreticImageSubfunctor B S hS j).ι :=
    mono_of_isClosedImmersion B S hS _ hIc.2
  refine ⟨_, toSchemeTheoreticImage B S hS j, (schemeTheoreticImageSubfunctor B S hS j).ι ≫ p,
    hIc.1, hopen, isQuasiCompact_of_comp_mono B S hS _ _ (by rwa [toSchemeTheoreticImage_ι]),
    isProper_comp B S hS hIc.1 hX hY _ _
      (isProper_of_isClosedImmersion B S hS hIc.1 hX _ hIc.2) hp,
    by rw [← Category.assoc, toSchemeTheoreticImage_ι], hdense⟩

/-- **Density survives an admissible blowup and restriction to an open subspace.** Let
`j : U ⟶ X` be an open immersion with scheme-theoretically dense image and `b : X' ⟶ X` a
`U`-admissible blowup, and let `e : U ⟶ V'` into an open subspace `V'` of `X'` have image
`b⁻¹(U)` in `X'`. Then `e` has dense image. -/
theorem denseRange_of_isAdmissibleBlowup {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) {X X' : AlgebraicSpaces B S hS} {j : U ⟶ X.1}
    (hj : IsOpenImmersion B S hS j)
    (hd : IsSchemeTheoreticallyDense B S hS (Subfunctor.range j)) {b : X' ⟶ X}
    (hb : IsAdmissibleBlowup B S hS
      ⟨Subfunctor.range j, isOpenSubspace_subfunctorRange B S hS hU hj⟩ b)
    (V' : OpenSubspaces B S hS X'.1) (e : U ⟶ V'.1.toFunctor)
    (he : Subfunctor.range (e ≫ V'.1.ι) = (Subfunctor.range j).preimage b.hom)
    (heb : e ≫ V'.1.ι ≫ b.hom = j) :
    DenseRange (pointsMap B S hS U e) := by
  obtain ⟨Zc, -, -, hbl⟩ := hb
  have hd' := dense_subspacePointSet_of_isSchemeTheoreticallyDense B S hS _
    (isSchemeTheoreticallyDense_preimage_of_isBlowupAlong_of_isSchemeTheoreticallyDense b Zc hbl _
      hd)
  have : Mono j := mono_of_presheaf_isOpenImmersion hj
  have : Mono (e ≫ V'.1.ι) :=
    mono_of_mono_fac (show (e ≫ V'.1.ι) ≫ b.hom = j by rw [Category.assoc, heb])
  rw [← he, subspacePointSet_range, pointsMap_comp, Set.range_comp] at hd'
  have hemb : IsOpenEmbedding (pointsMap B S hS _ V'.1.ι) :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS V'.1.ι)
      (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ V'.2.2)
  have := hd'.preimage hemb.isOpenMap
  rwa [Set.preimage_image_eq _ hemb.injective] at this

/-- **An open subspace of a Noetherian algebraic space is of finite type over it.** -/
theorem isFiniteType_ι_of_isNoetherian (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hN : IsNoetherian B S hS hZ X) {O : Subfunctor X} (hO : IsOpenSubspace B S hS O) :
    IsFiniteType B S hS O.ι :=
  ⟨isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
    (isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_ι_of_isOpenSubspace hO)),
    isQuasiCompact_ι_of_isNoetherian B S hS hZ hX hN hO⟩

/-- **The glued space is of finite type.** In an elementary distinguished square `U ⊆ W`,
`h : N ⟶ W` over `Y`, if `U ⟶ Y` is of finite type and `N` is an open subspace of a Noetherian `X`
of finite type over `Y`, then `W ⟶ Y` is of finite type. -/
theorem isFiniteType_of_isElementaryDistinguishedSquare_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) {Y W X : AlgebraicSpaces B S hS}
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    {Uw : Subfunctor W.1} (ε : U ≅ Uw.toFunctor) {O : Subfunctor X.1} (hO : IsOpenSubspace B S hS O)
    (hXN : IsNoetherian B S hS hZ X.1) {h : O.toFunctor ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uw h) {g : W.1 ⟶ Y.1} {π : X.1 ⟶ Y.1}
    (hπ : IsFiniteType B S hS π) {p : U ⟶ Y.1} (hp : IsFiniteType B S hS p)
    (hgU : ε.hom ≫ Uw.ι ≫ g = p) (hgN : h ≫ g = O.ι ≫ π) :
    IsFiniteType B S hS g := by
  refine isFiniteType_of_isElementaryDistinguishedSquare hZ (V := ⟨O.toFunctor, hO.1⟩)
    (f := ObjectProperty.homMk h) hsq (ObjectProperty.homMk g) hYqc hYqs ?_ ?_
  · have : Uw.ι ≫ g = inv ε.hom ≫ p := by rw [← hgU, IsIso.inv_hom_id_assoc]
    show IsFiniteType B S hS (Uw.ι ≫ g)
    rw [this]
    exact isFiniteType_comp' B S hS _ _ hU Y.2 (isProper_of_isIso B S hS _).2.1 hp
  · show IsFiniteType B S hS (h ≫ g)
    rw [hgN]
    exact isFiniteType_comp' B S hS _ _ X.2 Y.2 (isFiniteType_ι_of_isNoetherian hZ X.2 hXN hO) hπ

/-- **The proof of Stacks 0F4B from the two proper extensions.**
Over a quasi-compact, quasi-separated and Noetherian `Y`, let `p : U ⟶ Y` be separated and of
finite type, `U₂ ⊆ U` open with closed complement `Z`, and:

* on the side of `U₁`: a proper `π₁ : X₁ ⟶ Y`, an open immersion `ι₁ : V₁ ⟶ X₁`, a proper
  `ψ₁ : V₁ ⟶ U` over `Y`, and an open immersion `j : U₁ ⟶ V₁` with `f = j ≫ ψ₁` étale and an
  isomorphism over `Z`; an open `N ⊆ |X₁|` meeting `V₁` only in `U₁` and containing the closure of
  `f⁻¹ Z`, and the separated `W₁ = U ⊔_{U₁} N` of Stacks 0DVJ;
* on the side of `U₂`: a proper `π₂ : X₂ ⟶ Y`, an open immersion `ι₂ : V₂ ⟶ X₂` and a proper
  `ψ₂ : V₂ ⟶ U` over `Y` extending the inclusion of `U₂` through a dense open immersion
  `e₂ : U₂ ⟶ V₂`.

Then `U` has a compactification over `Y`. -/
theorem hasCompactification_of_isProper_extensions (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : AlgebraicSpaces B S hS} (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hYN : IsNoetherian B S hS hZ Y.1)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U) {p : U ⟶ Y.1}
    (hpsep : IsSeparated B S hS p) (hpft : IsFiniteType B S hS p) (U₂ : Subfunctor U)
    (hU₂ : IsOpenSubspace B S hS U₂) (hZs : IsClosed (Set.range (pointsMap B S hS _ U₂.ι))ᶜ)
    {X₁ : AlgebraicSpaces B S hS} {π₁ : X₁.1 ⟶ Y.1} (hπ₁ : IsProper B S hS π₁)
    {V₁ U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV₁ : IsAlgebraicSpace B S hS V₁)
    (hU₁ : IsAlgebraicSpace B S hS U₁) {ψ₁ : V₁ ⟶ U} (hψ₁ : IsProper B S hS ψ₁)
    {ι₁ : V₁ ⟶ X₁.1} (hι₁ : IsOpenImmersion B S hS ι₁) (h₁ : ψ₁ ≫ p = ι₁ ≫ π₁)
    {j : U₁ ⟶ V₁} (hj : IsOpenImmersion B S hS j) (hf : IsEtale B S hS (j ≫ ψ₁))
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU _ hZs).fromPreimage (j ≫ ψ₁)))
    (Nset : Set (points B S hS X₁.1)) (hNo : IsOpen Nset)
    (hN₂ : Nset ∩ Set.range (pointsMap B S hS V₁ ι₁) ⊆ Set.range (pointsMap B S hS U₁ (j ≫ ι₁)))
    (hN₃ : closure (pointsMap B S hS U₁ (j ≫ ι₁) ''
      (pointsMap B S hS U₁ (j ≫ ψ₁) ⁻¹' (Set.range (pointsMap B S hS _ U₂.ι))ᶜ)) ⊆ Nset)
    {jN : U₁ ⟶ (openSubspaceOfPoints B S hS X₁.1 Nset).toFunctor}
    (hjN : jN ≫ (openSubspaceOfPoints B S hS X₁.1 Nset).ι = j ≫ ι₁)
    {W₁ : AlgebraicSpaces B S hS} {Uw₁ : Subfunctor W₁.1} {ε₁ : U ≅ Uw₁.toFunctor}
    {fW₁ : (openSubspaceOfPoints B S hS X₁.1 Nset).toFunctor ⟶ W₁.1} {g₁ : W₁.1 ⟶ Y.1}
    (hsq₁ : IsElementaryDistinguishedSquare B S hS W₁.2 Uw₁ fW₁)
    (hpb₁ : IsPullback jN (j ≫ ψ₁) fW₁ (ε₁.hom ≫ Uw₁.ι)) (hgU₁ : ε₁.hom ≫ Uw₁.ι ≫ g₁ = p)
    (hgN₁ : fW₁ ≫ g₁ = (openSubspaceOfPoints B S hS X₁.1 Nset).ι ≫ π₁)
    (hg₁ : IsSeparated B S hS g₁)
    {X₂ : AlgebraicSpaces B S hS} {π₂ : X₂.1 ⟶ Y.1} (hπ₂ : IsProper B S hS π₂)
    {V₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV₂ : IsAlgebraicSpace B S hS V₂) {ψ₂ : V₂ ⟶ U}
    (hψ₂ : IsProper B S hS ψ₂) {ι₂ : V₂ ⟶ X₂.1} (hι₂ : IsOpenImmersion B S hS ι₂)
    (h₂ : ψ₂ ≫ p = ι₂ ≫ π₂) {e₂ : U₂.toFunctor ⟶ V₂} (he₂ : IsOpenImmersion B S hS e₂)
    (he₂ψ : e₂ ≫ ψ₂ = U₂.ι) (hd : DenseRange (pointsMap B S hS _ e₂)) :
    HasCompactification B S hS p := by
  have hUqc : IsQuasiCompactSpace B S hS U :=
    (hpft.2 Y.1 Y.2 hYqc (𝟙 Y.1)).of_iso B S hS (asIso (pullback.snd (𝟙 Y.1) p))
  have hV₂qc : IsQuasiCompactSpace B S hS V₂ :=
    (hψ₂.isFiniteType.2 U hU hUqc (𝟙 U)).of_iso B S hS (asIso (pullback.snd (𝟙 U) ψ₂))
  have hV₂Z : (Set.range (pointsMap B S hS _ e₂))ᶜ ⊆
      pointsMap B S hS V₂ ψ₂ ⁻¹' (Set.range (pointsMap B S hS _ U₂.ι))ᶜ := by
    intro x hx hψx
    refine hx (preimage_range_comp_subset_range_of_denseRange hU hV₂ hU₂.1 hψ₂.1
      (by rw [he₂ψ]; exact hU₂.2) hd ?_)
    rw [Set.mem_preimage, he₂ψ]
    exact hψx
  -- the flat cover and the blowup of `X₂` (Stacks 0F48)
  obtain ⟨X₂', b, ι₂', E, t, r, hE, hb, hι₂'b, hι₂'o, ht, hr, hrN, hcl, hfac⟩ :=
    exists_isFlat_cover_closure_of_isEtale hZ hYqc hYqs hU hV₁ hV₂ hU₁ hψ₁ hψ₂ hpsep hpft.2 hπ₁
      hπ₂ hι₁ hι₂ h₁ h₂ hV₂qc hj hf _ hZs hiso Nset hNo hN₃
  set π₂' : X₂' ⟶ Y := b ≫ ObjectProperty.homMk π₂ with hπ₂'def
  have hπ₂'P : IsProper B S hS π₂'.hom := isProper_comp B S hS X₂'.2 X₂.2 Y.2 _ _ hb hπ₂
  have h₂' : ψ₂ ≫ p = ι₂' ≫ π₂'.hom := by
    rw [h₂, ← hι₂'b]
    simp only [Category.assoc, hπ₂'def, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom]
  -- the space `W₂`
  obtain ⟨jN₂, W₂, Uw₂, ε₂, fW₂, g₂, hjN₂, hsq₂, hpb₂, hgU₂, hgN₂, hg₂⟩ :=
    exists_isSeparated_pushout_of_isOpenImmersion (π := π₂') hπ₂'P.1 hV₂ hU hU₂.1 hψ₂ hpsep
      hι₂'o he₂ h₂' (by rw [he₂ψ]; exact hU₂.2)
  -- finite type of `W₁` and `W₂`
  have hX₁N : IsNoetherian B S hS hZ X₁.1 := isNoetherian_of_isProper hZ X₁.2 Y.2 hYN _ hπ₁
  have hX₂'N : IsNoetherian B S hS hZ X₂'.1 := isNoetherian_of_isProper hZ X₂'.2 Y.2 hYN _ hπ₂'P
  have hg₁ft : IsFiniteType B S hS g₁ :=
    isFiniteType_of_isElementaryDistinguishedSquare_of_isNoetherian hZ hU hYqc hYqs ε₁
      (isOpenSubspace_openSubspaceOfPoints B S hS X₁.2 Nset hNo) hX₁N hsq₁ hπ₁.isFiniteType hpft
      hgU₁ hgN₁
  have hg₂ft : IsFiniteType B S hS g₂ :=
    isFiniteType_of_isElementaryDistinguishedSquare_of_isNoetherian hZ hU hYqc hYqs ε₂
      (isOpenSubspace_openSubspaceOfPoints B S hS X₂'.2 _ isClosed_closure.isOpen_compl) hX₂'N
      hsq₂ hπ₂'P.isFiniteType hpft hgU₂ hgN₂
  -- the open immersions `U ⟶ Wᵢ`
  have ha₁ : IsOpenImmersion B S hS (ε₁.hom ≫ Uw₁.ι) :=
    isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) hsq₁.isOpenSubspace.2
  have ha₂ : IsOpenImmersion B S hS (ε₂.hom ≫ Uw₂.ι) :=
    isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) hsq₂.isOpenSubspace.2
  -- existence for the compactifications
  have hπ₁E : ValuativeCriterion.Existence π₁ :=
    valuativeCriterion_existence_of_isQuasiSeparated_of_universallyClosed X₁.2 Y.2 π₁
      (isQuasiSeparated_of_isSeparated B S hS hπ₁.1) hπ₁.2.2
  have hπ₂E : ValuativeCriterion.Existence π₂'.hom :=
    valuativeCriterion_existence_of_isQuasiSeparated_of_universallyClosed X₂'.2 Y.2 π₂'.hom
      (isQuasiSeparated_of_isSeparated B S hS hπ₂'P.1) hπ₂'P.2.2
  have hr' : r ≫ π₁ = t ≫ π₂'.hom := by
    rw [hr]
    simp only [hπ₂'def, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
  refine hasCompactification_of_forall_exists_lift hZ (U := ⟨U, hU⟩) hYqc hYqs hpsep hpft
    (ObjectProperty.homMk (ε₁.hom ≫ Uw₁.ι)) (ObjectProperty.homMk (ε₂.hom ≫ Uw₂.ι)) ha₁ ha₂
    (ObjectProperty.homMk g₁) (ObjectProperty.homMk g₂) hg₁ hg₁ft hg₂ hg₂ft
    (by simpa only [ObjectProperty.homMk_hom, Category.assoc] using hgU₁)
    (by simpa only [ObjectProperty.homMk_hom, Category.assoc] using hgU₂)
    (fun q γ σ hγσ => ValuativeSquare.exists_lift_of_isElementaryDistinguishedSquare hU hU₂ X₁.2
      X₂'.2 hV₁ hV₂ hU₁ hE hπ₁E hπ₂E hι₁ h₁ hj hι₂'o h₂' he₂ψ hZs hiso hV₂Z Nset hNo hN₂ hN₃ hjN
      hpb₁.w hgN₁ hjN₂ hpb₂.w hgN₂ (by simpa only [Category.assoc] using hgU₂) ht hr' hrN hcl hfac
      q γ σ hγσ)

/-- **The lift of an open immersion through a modification is an open immersion.** If
`e : V ⟶ V'` into an open subspace `V'` of `X'` lies over an open immersion `j : V ⟶ X` through
`b : X' ⟶ X`, and the image of `V` in `X'` is `b⁻¹(j(V))`, then `e` is an open immersion. -/
theorem isOpenImmersion_of_range_eq_preimage {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) {X X' : AlgebraicSpaces B S hS} {j : V ⟶ X.1}
    (hj : IsOpenImmersion B S hS j) {b : X' ⟶ X} (V' : OpenSubspaces B S hS X'.1)
    (e : V ⟶ V'.1.toFunctor)
    (he : Subfunctor.range (e ≫ V'.1.ι) = (Subfunctor.range j).preimage b.hom)
    (heb : e ≫ V'.1.ι ≫ b.hom = j) :
    IsOpenImmersion B S hS e := by
  have : Mono j := mono_of_presheaf_isOpenImmersion hj
  have : Mono (e ≫ V'.1.ι) :=
    mono_of_mono_fac (show (e ≫ V'.1.ι) ≫ b.hom = j by rw [Category.assoc, heb])
  have : Mono V'.1.ι := mono_of_presheaf_isOpenImmersion V'.2.2
  have hro : IsOpenSubspace B S hS (Subfunctor.range (e ≫ V'.1.ι)) := by
    rw [he]
    exact isOpenSubspace_preimage B S hS b.hom _ X.2 X'.2
      (isOpenSubspace_subfunctorRange B S hS hV hj)
  refine isOpenImmersion_of_comp_mono B S hS e V'.1.ι ?_
  rw [← Subfunctor.toRange_ι (e ≫ V'.1.ι)]
  exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) hro.2

/-- **Compactifications glue across an elementary distinguished square** (Stacks 0F4B). Over a
quasi-compact, quasi-separated algebraic space `Y` of finite type over `Spec ℤ`, let `U` be
separated and of finite type over `Y` and `(U₂ ⊆ U, f : U₁ ⟶ U)` an elementary distinguished
square such that `U₁` and `U₂` have compactifications over `Y` and `U₁ ×_U U₂ ⟶ U` has dense
image. Then `U` has a compactification over `Y`.

The proof is the repaired one of
`StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.EtaleSquareGluing`; the density of
`U₁ ×_U U₂` in `U` is not needed. -/
@[stacks 0F4B "proof corrected: the source's W₁ = U ⊔_{U₁} (X₁ ∖ (Z̄₁₂ ∪ T̄)) need not be \
separated; X₁ is modified by three more admissible blowups (0F46 twice, and a blowup in I + J^M \
from the Nullstellensatz on the closure of the off-diagonal of U₁ ×_U U₁), and W₁ is glued from \
the chart N = X₁ ∖ (closure (V₁ ∖ U₁) ∪ closure (∂ ∖ Q))"]
theorem hasCompactification_of_isElementaryDistinguishedSquare (hZ : B.Contains (⊤_ Scheme.{u})) :
    Stmt0F4B (B := B) (S := S) (hS := hS) hZ := by
  intro U Y hU hY hYqc hYqs hYft p hpsep hpft U₂ U₁ f₁ hsq hc₁ hc₂ _
  have hYN : IsNoetherian B S hS hZ Y :=
    isNoetherian_of_isFiniteType_viewOverIntegers B S hS hZ _ hY hYqs hYft
  have hU₁ := hsq.isAlgebraicSpace
  have hU₂ := hsq.isOpenSubspace
  have hZs := hsq.isClosedComplement
  -- the side of `U₁`: Stacks 0F4A and the chart `N`
  have hf₁sep : IsSeparated B S hS f₁ := isSeparated_of_comp B S hS f₁ p hc₁.isSeparated
  obtain ⟨X₁₀, j₁, p₁, hX₁₀, hj₁, hj₁qc, hp₁, hjp₁⟩ := hc₁
  obtain ⟨X₁', b₁, hb₁, V₁, e₁, ψ₁, hV₁r, he₁b, hψ₁, he₁ψ, hψ₁p⟩ :=
    exists_isAdmissibleBlowup_isProper_extension_of_isEtale hZ (T := ⟨Y, hY⟩) (U := ⟨U, hU⟩)
      (V := ⟨U₁, hU₁⟩) (Y := ⟨X₁₀, hX₁₀⟩) hYqc hYqs p hpft hpsep f₁ hsq.isEtale j₁ p₁ hj₁ hj₁qc
      hp₁ hjp₁
  have he₁o : IsOpenImmersion B S hS e₁ :=
    isOpenImmersion_of_range_eq_preimage hU₁ hj₁ V₁ e₁ hV₁r he₁b
  have hπ₁ : IsProper B S hS (b₁ ≫ (ObjectProperty.homMk p₁ : (⟨X₁₀, hX₁₀⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).hom :=
    isProper_comp B S hS X₁'.2 hX₁₀ hY _ _ hb₁.isProper hp₁
  have hf : IsEtale B S hS (e₁ ≫ ψ₁) := he₁ψ ▸ hsq.isEtale
  have hfsep : IsSeparated B S hS (e₁ ≫ ψ₁) := he₁ψ ▸ hf₁sep
  have hiso' : IsIso ((reducedClosedSubspace B S hS U hU _ hZs).fromPreimage (e₁ ≫ ψ₁)) :=
    he₁ψ ▸ hsq.isIsoOverComplement
  obtain ⟨X₁'', b', ι₁, Nset, hNo, jN, W₁, Uw₁, ε₁, fW₁, g₁, hb', hι₁b, hι₁o, -, hjN, hN₂, hN₃,
    hsq₁, hpb₁, hgU₁, hgN₁, hg₁⟩ :=
    exists_isSeparated_pushout_offDiagonal_chart hZ hπ₁ hYN V₁.2.1 hU hU₁ hψ₁ hpsep V₁.2.2 he₁o
      hψ₁p hf hfsep _ hZs hiso'
  -- the side of `U₂`: a dense compactification and Stacks 0F4A
  obtain ⟨X₂₀, j₂, p₂, hX₂₀, hj₂, hj₂qc, hp₂, hjp₂, hd₂⟩ :=
    hc₂.exists_isSchemeTheoreticallyDense hU₂.1 hY
  obtain ⟨X₂', b₂, hb₂, V₂, e₂, ψ₂, hV₂r, he₂b, hψ₂, he₂ψ, hψ₂p⟩ :=
    exists_isAdmissibleBlowup_isProper_extension_of_isEtale hZ (T := ⟨Y, hY⟩) (U := ⟨U, hU⟩)
      (V := ⟨U₂.toFunctor, hU₂.1⟩) (Y := ⟨X₂₀, hX₂₀⟩) hYqc hYqs p hpft hpsep U₂.ι
      (isEtale_ι_of_isOpenSubspace hU₂) j₂ p₂ hj₂ hj₂qc hp₂ hjp₂
  have he₂o : IsOpenImmersion B S hS e₂ :=
    isOpenImmersion_of_range_eq_preimage hU₂.1 hj₂ V₂ e₂ hV₂r he₂b
  have hd : DenseRange (pointsMap B S hS _ e₂) :=
    denseRange_of_isAdmissibleBlowup hU₂.1 hj₂ hd₂ hb₂ V₂ e₂ hV₂r he₂b
  exact hasCompactification_of_isProper_extensions hZ (Y := ⟨Y, hY⟩) hYqc hYqs hYN hU hpsep hpft
    U₂ hU₂ hZs (isProper_comp B S hS X₁''.2 X₁'.2 hY _ _ hb' hπ₁) V₁.2.1 hU₁ hψ₁ hι₁o
    (by rw [hψ₁p, ← hι₁b]; simp only [Category.assoc, ObjectProperty.FullSubcategory.comp_hom]; rfl)
    he₁o hf hiso' Nset hNo hN₂ hN₃ hjN hsq₁ hpb₁ hgU₁ hgN₁ hg₁
    (isProper_comp B S hS X₂'.2 hX₂₀ hY _ _ hb₂.isProper hp₂) V₂.2.1 hψ₂ V₂.2.2 hψ₂p he₂o he₂ψ hd

end AlgebraicGeometry.Space

end
