module

public import StacksFrontier.AlgebraicGeometry.ChowQcqs.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Chow's lemma for a separated morphism of finite type to a quasi-compact quasi-separated space

Let `Y` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let
`f : X ⟶ Y` be separated and of finite type. Chow's lemma in the form of [Stacks, Tag 089L]
produces a proper surjective `X' ⟶ X` and an open immersion of `X'` into an algebraic space
`X̄'` which is proper and representable over `Y`, compatibly with the maps to `Y`.

This file proves that conclusion once `Y`, and then the fibre product `X ×_Y Z`, are covered
properly and surjectively by schemes. Given a proper surjection `π : Z ⟶ Y` from a
quasi-compact quasi-separated scheme and a proper surjection `p : X₂ ⟶ X ×_Y Z` from a
quasi-compact scheme, the composite `X₂ ⟶ X ×_Y Z ⟶ Z` is a separated morphism of finite type
of schemes over a quasi-compact quasi-separated base, so Chow's lemma for schemes,
[Stacks, Tag 0202], gives a proper surjective `X₃ ⟶ X₂` and an immersion `X₃ ⟶ ℙⁿ_Z` over `Z`.
The immersion is quasi-compact, so `X₃` is open in its scheme-theoretic image `X̄'`, which is a
closed subscheme of `ℙⁿ_Z` and hence proper over `Z`. Then `X' = X₃` maps properly and
surjectively to `X` through `X₂` and `X ×_Y Z`, and `X̄' ⟶ Z ⟶ Y` is proper; it is
representable because its source is a scheme.

## Main results

* `AlgebraicGeometry.Space.exists_chowDiagram`: **Chow's lemma, [Stacks, Tag 089L].**
* `AlgebraicGeometry.Space.exists_chowDiagram_of_proper_scheme_covers`: the diagram of
  [Stacks, Tag 089L], from a proper surjective scheme cover of `Y` and one of `X ×_Y Z`.
* `AlgebraicGeometry.Space.exists_chowDiagram_of_forall_properSchemeCover`: the diagram of
  [Stacks, Tag 089L] for every separated morphism of finite type to a quasi-compact
  quasi-separated algebraic space, as soon as every quasi-compact quasi-separated algebraic space
  is the target of a proper surjective morphism from a scheme.
* `AlgebraicGeometry.Space.exists_chowDiagram_of_forall_finiteSchemeCover`: the same, from
  finite surjective scheme covers, the form of [Stacks, Tag 09YC], part (1).
* `AlgebraicGeometry.Space.quasiSeparatedSpace_of_isAbsolutelyQuasiSeparated_yoneda`: an object
  of the site whose represented presheaf is quasi-separated has quasi-separated underlying
  scheme.

## Implementation notes

The source deduces [Stacks, Tag 089L] from its Noetherian case, [Stacks, Tag 088S], by
Noetherian approximation of `Y`. Here the reduction is instead to Chow's lemma for schemes, by
base change along a proper surjective scheme cover of `Y`; such covers are supplied by the
finite scheme covers of [Stacks, Tag 09YC] in the form
`AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace`. The
algebraic space `X̄'` produced is in fact a
scheme, projective over the cover `Z`.

## References

* [Stacks Project, Tag 089L](https://stacks.math.columbia.edu/tag/089L)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 04NZ](https://stacks.math.columbia.edu/tag/04NZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The diagram of [Stacks, Tag 089L], from proper surjective scheme covers.** Let
`f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S`. Suppose given a
proper surjective `π : Z ⟶ Y` whose source is a quasi-compact quasi-separated scheme, and a
proper surjective `p : X₂ ⟶ X ×_Y Z` whose source is a quasi-compact scheme. Then there are a
proper surjective `q : X' ⟶ X`, an open immersion `j : X' ⟶ X̄'` and a proper representable
`g : X̄' ⟶ Y` with `q ≫ f = j ≫ g`.

The composite `X₂ ⟶ Z` is separated and of finite type, so Chow's lemma for schemes,
[Stacks, Tag 0202], applies to it; `X'` is the modification it returns and `X̄'` the
scheme-theoretic image of its quasi-compact immersion into `ℙⁿ_Z`, which contains `X'` as an open
subscheme by [Stacks, Tag 01RG]. -/
theorem exists_chowDiagram_of_proper_scheme_covers
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hfsep : IsSeparated B S hS f) (hfft : IsFiniteType B S hS f)
    (Z : BigFppfOver B S hS) (π : yoneda.obj Z ⟶ Y) (hπ : IsProper B S hS π)
    (hπs : IsSurjective B S hS π)
    (hZqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj Z))
    (hZqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Z))
    (X₂ : BigFppfOver B S hS) (p : yoneda.obj X₂ ⟶ pullback f π) (hp : IsProper B S hS p)
    (hps : IsSurjective B S hS p)
    (hX₂qc : CompactSpace ((BigFppfOver.toScheme B S hS).obj X₂)) :
    ∃ (X' Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hX' : IsAlgebraicSpace B S hS X')
      (_hXbar : IsAlgebraicSpace B S hS Xbar) (q : X' ⟶ X) (j : X' ⟶ Xbar) (g : Xbar ⟶ Y),
      IsProper B S hS q ∧ IsSurjective B S hS q ∧ IsOpenImmersion B S hS j ∧
        IsProper B S hS g ∧ yoneda.relativelyRepresentable g ∧ q ≫ f = j ≫ g := by
  classical
  have hZalg : IsAlgebraicSpace B S hS (yoneda.obj Z) := isAlgebraicSpace_yoneda B S hS Z
  have hX₂alg : IsAlgebraicSpace B S hS (yoneda.obj X₂) := isAlgebraicSpace_yoneda B S hS X₂
  have hPalg : IsAlgebraicSpace B S hS (pullback f π) :=
    isAlgebraicSpace_pullback B S hS f π hX hZalg hY
  -- the morphism of schemes `X₂ ⟶ Z`
  let h : X₂ ⟶ Z := yoneda.preimage (p ≫ pullback.snd f π)
  have hh : yoneda.map h = p ≫ pullback.snd f π := yoneda.map_preimage _
  have hsq : IsPullback (pullback.fst f π) (pullback.snd f π) f π :=
    IsPullback.of_hasPullback f π
  have hhsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map h) := by
    rw [← isSeparated_yoneda_map_iff, hh]
    exact isSeparated_comp B S hS p _ hp.1 (isSeparated_pullback B S hS f π hfsep)
  have hhlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) := by
    rw [← isLocallyOfFiniteType_yoneda_map_iff, hh]
    exact (isFiniteType_comp B S hS hX₂alg hPalg hZalg p _ hp.2.1
      ⟨IsLocallyOfFiniteType.of_isPullback B S hS hsq.flip hX hY hfft.1,
        isQuasiCompact_of_isPullback B S hS hsq hfft.2⟩).1
  -- Chow's lemma for the morphism of schemes `X₂ ⟶ Z`, Stacks 0202
  obtain ⟨n, X₃, ρ, i, hρ, hρs, hi, hcomm⟩ :=
    hasChowModification_of_compactSpace_quasiSeparatedSpace ((BigFppfOver.toScheme B S hS).map h)
  have := hρ
  have := hi
  -- the projective space over `Z` and the modification as objects of the site
  let Zs := (BigFppfOver.toScheme B S hS).obj Z
  let pr : ProjectiveSpace n Zs ⟶ Zs := ProjectiveSpace n Zs ↘ Zs
  have hPn : B.Contains (ProjectiveSpace n Zs) :=
    contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := Z) pr
  let Pn : BigFppfOver B S hS := BigFppfOver.mk B S hS hPn (pr ≫ B.inclusion.map Z.hom)
  have hX₃ : B.Contains X₃ := contains_of_locallyOfFiniteType_of_quasiCompact B S hS (Y₀ := X₂) ρ
  let X₃' : BigFppfOver B S hS := BigFppfOver.mk B S hS hX₃ (ρ ≫ B.inclusion.map X₂.hom)
  let ρ' : X₃' ⟶ X₂ :=
    Over.homMk (ObjectProperty.homMk ρ) (by apply ObjectProperty.hom_ext; rfl)
  let pn : Pn ⟶ Z :=
    Over.homMk (ObjectProperty.homMk pr) (by apply ObjectProperty.hom_ext; rfl)
  have hhw : (BigFppfOver.toScheme B S hS).map h ≫ B.inclusion.map Z.hom =
      B.inclusion.map X₂.hom := by
    change B.inclusion.map h.left ≫ B.inclusion.map Z.hom = _
    rw [← Functor.map_comp, Over.w]
  let i' : X₃' ⟶ Pn :=
    Over.homMk (ObjectProperty.homMk i) (by
      apply ObjectProperty.hom_ext
      change i ≫ pr ≫ B.inclusion.map Z.hom = ρ ≫ B.inclusion.map X₂.hom
      rw [← Category.assoc, ← hcomm, Category.assoc, hhw])
  have hi'pn : i' ≫ pn = ρ' ≫ h := BigFppfOver.map_toScheme_injective B S hS hcomm.symm
  have hX₃c : CompactSpace X₃ := QuasiCompact.compactSpace_of_compactSpace ρ
  have hPnqs : QuasiSeparatedSpace (ProjectiveSpace n Zs) :=
    quasiSeparatedSpace_of_quasiSeparated pr
  have hi'qc : QuasiCompact ((BigFppfOver.toScheme B S hS).map i') :=
    inferInstanceAs (QuasiCompact i)
  have hj : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (toSchemeImageObj B S hS i')) :=
    isOpenImmersion_toSchemeImageObj B S hS i' hi (Or.inl hi'qc)
  let gs : schemeImageObj B S hS i' ⟶ Z := schemeImageObjι B S hS i' ≫ pn
  have hgs : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map gs) := by
    have := isClosedImmersion_schemeImageObjι B S hS i'
    have h₂ : _root_.AlgebraicGeometry.IsProper pr := inferInstance
    rw [Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ inferInstance h₂
  have hfstp : IsProper B S hS (pullback.fst f π) :=
    isProper_of_isPullback B S hS hPalg hZalg hX hY hsq.flip hπ
  have hρ'p : IsProper B S hS (yoneda.map ρ') := isProper_yoneda_map B S hS ρ' hρ
  refine ⟨yoneda.obj X₃', yoneda.obj (schemeImageObj B S hS i'),
    isAlgebraicSpace_yoneda B S hS _, isAlgebraicSpace_yoneda B S hS _,
    yoneda.map ρ' ≫ p ≫ pullback.fst f π, yoneda.map (toSchemeImageObj B S hS i'),
    yoneda.map gs ≫ π, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS _) hX₂alg hX _ _ hρ'p
      (isProper_comp B S hS hX₂alg hPalg hX _ _ hp hfstp)
  · exact isSurjective_comp B S hS (isSurjective_yoneda_map B S hS ρ' hρs)
      (isSurjective_comp B S hS hps
        (isSurjective_pullback_fst B S hS hX hY hZalg f π hπs))
  · exact isOpenImmersion_yoneda_map B S hS _ hj
  · exact isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS _) hZalg hY _ _
      (isProper_yoneda_map B S hS gs hgs) hπ
  · exact relativelyRepresentable_of_isAlgebraicSpace B S hS hY _
  · have hgs' : toSchemeImageObj B S hS i' ≫ gs = ρ' ≫ h := by
      rw [← hi'pn]
      change toSchemeImageObj B S hS i' ≫ schemeImageObjι B S hS i' ≫ pn = i' ≫ pn
      rw [← Category.assoc, toSchemeImageObj_comp_schemeImageObjι]
    rw [Category.assoc, Category.assoc, hsq.w, ← Category.assoc p, ← hh, ← Category.assoc,
      ← Functor.map_comp, ← hgs', Functor.map_comp, Category.assoc]

/-! ### Quasi-separatedness of the underlying scheme of a represented presheaf -/

/-- **An object of the site whose represented presheaf is absolutely quasi-separated has
quasi-separated underlying scheme.** The point space of the represented presheaf is
quasi-separated by
`AlgebraicGeometry.Space.quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated` and
homeomorphic to the underlying scheme by Stacks 03BX. -/
theorem quasiSeparatedSpace_of_isAbsolutelyQuasiSeparated_yoneda (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : BigFppfOver B S hS) (hT : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T)) :
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T) := by
  let := pointTopology B S hS (yoneda.obj T)
  exact (quasiSeparatedSpace_congr (schemePointsHomeomorph B S hS T)).mp
    (quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T) hT)

/-! ### Chow's lemma from proper surjective scheme covers of quasi-compact quasi-separated
spaces -/

/-- **The diagram of [Stacks, Tag 089L], from proper surjective scheme covers of quasi-compact
quasi-separated algebraic spaces.** If every quasi-compact quasi-separated algebraic space over `S`
is the target of a proper surjective morphism from a scheme, then every separated morphism of
finite type `f : X ⟶ Y` to a quasi-compact quasi-separated algebraic space fits in a diagram
`X ⟵ X' ⟶ X̄' ⟶ Y` with `X' ⟶ X` proper surjective, `X' ⟶ X̄'` an open immersion and
`X̄' ⟶ Y` proper and representable.

The covers are applied to `Y` and to the fibre product `X ×_Y Z` with the cover `Z` of `Y`, both
of which are quasi-compact and quasi-separated, and
`AlgebraicGeometry.Space.exists_chowDiagram_of_proper_scheme_covers` assembles the diagram. -/
theorem exists_chowDiagram_of_forall_properSchemeCover (hZ : B.Contains (⊤_ Scheme.{u}))
    (hcov : ∀ W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS W →
      IsQuasiCompactSpace B S hS W → IsAbsolutelyQuasiSeparated B S hS hZ W →
        ∃ (W' : BigFppfOver B S hS) (c : yoneda.obj W' ⟶ W),
          IsProper B S hS c ∧ IsSurjective B S hS c)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hfsep : IsSeparated B S hS f) (hfft : IsFiniteType B S hS f) :
    ∃ (X' Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hX' : IsAlgebraicSpace B S hS X')
      (_hXbar : IsAlgebraicSpace B S hS Xbar) (q : X' ⟶ X) (j : X' ⟶ Xbar) (g : Xbar ⟶ Y),
      IsProper B S hS q ∧ IsSurjective B S hS q ∧ IsOpenImmersion B S hS j ∧
        IsProper B S hS g ∧ yoneda.relativelyRepresentable g ∧ q ≫ f = j ≫ g := by
  obtain ⟨Z, π, hπ, hπs⟩ := hcov Y hY hYqc hYqs
  have hZalg : IsAlgebraicSpace B S hS (yoneda.obj Z) := isAlgebraicSpace_yoneda B S hS Z
  have hZqc : IsQuasiCompactSpace B S hS (yoneda.obj Z) :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS hY hYqc π hπ.2.1.2
  have hZqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj Z) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hZalg hYqs
      (isQuasiSeparated_of_isSeparated B S hS hπ.1)
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS hY hYqc f hfft.2
  have hPalg : IsAlgebraicSpace B S hS (pullback f π) :=
    isAlgebraicSpace_pullback B S hS f π hX hZalg hY
  have hPqc : IsQuasiCompactSpace B S hS (pullback f π) :=
    isQuasiCompactSpace_pullback B S hS hZ f π hX hY hXqc hZqc hYqs
  have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ (pullback f π) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hPalg hZqs
      (isQuasiSeparated_of_isSeparated B S hS (isSeparated_pullback B S hS f π hfsep))
  obtain ⟨X₂, p, hp, hps⟩ := hcov (pullback f π) hPalg hPqc hPqs
  have hX₂qc : IsQuasiCompactSpace B S hS (yoneda.obj X₂) :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS hPalg hPqc p hp.2.1.2
  exact exists_chowDiagram_of_proper_scheme_covers B S hS hX hY f hfsep hfft Z π hπ hπs
    (compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hZqc)
    (quasiSeparatedSpace_of_isAbsolutelyQuasiSeparated_yoneda B S hS hZ Z hZqs) X₂ p hp hps
    (compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hX₂qc)

/-- **The diagram of [Stacks, Tag 089L], from finite surjective scheme covers of quasi-compact
quasi-separated algebraic spaces.** This is
`AlgebraicGeometry.Space.exists_chowDiagram_of_forall_properSchemeCover` with the covers taken
finite, which is the form in which [Stacks, Tag 09YC], part (1), provides them: a finite morphism
of algebraic spaces is proper by [Stacks, Tag 04NZ]. -/
theorem exists_chowDiagram_of_forall_finiteSchemeCover (hZ : B.Contains (⊤_ Scheme.{u}))
    (hcov : ∀ W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS W →
      IsQuasiCompactSpace B S hS W → IsAbsolutelyQuasiSeparated B S hS hZ W →
        ∃ (W' : BigFppfOver B S hS) (c : yoneda.obj W' ⟶ W),
          IsSurjective B S hS c ∧ IsFinite B S hS c)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hfsep : IsSeparated B S hS f) (hfft : IsFiniteType B S hS f) :
    ∃ (X' Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hX' : IsAlgebraicSpace B S hS X')
      (_hXbar : IsAlgebraicSpace B S hS Xbar) (q : X' ⟶ X) (j : X' ⟶ Xbar) (g : Xbar ⟶ Y),
      IsProper B S hS q ∧ IsSurjective B S hS q ∧ IsOpenImmersion B S hS j ∧
        IsProper B S hS g ∧ yoneda.relativelyRepresentable g ∧ q ≫ f = j ≫ g := by
  refine exists_chowDiagram_of_forall_properSchemeCover B S hS hZ (fun W hW hWqc hWqs => ?_)
    hX hY f hYqc hYqs hfsep hfft
  obtain ⟨W', c, hcs, hcf⟩ := hcov W hW hWqc hWqs
  exact ⟨W', c, ((isFinite_iff_isAffineHom_and_isProper B S hS
    (isAlgebraicSpace_yoneda B S hS W') hW c).mp hcf).2, hcs⟩

/-- **Chow's lemma for algebraic spaces, [Stacks, Tag 089L].** Let `Y` be a quasi-compact and
quasi-separated algebraic space over `S` and let `f : X ⟶ Y` be a separated morphism of finite
type. Then there are algebraic spaces `X'` and `X̄'` and a commutative diagram
`X ⟵ X' ⟶ X̄' ⟶ Y` over `Y` in which `X' ⟶ X` is proper and surjective, `X' ⟶ X̄'` is an open
immersion and `X̄' ⟶ Y` is proper and representable.

Every quasi-compact quasi-separated algebraic space has a finite surjective scheme cover
(`AlgebraicGeometry.Space.existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace`), so
`AlgebraicGeometry.Space.exists_chowDiagram_of_forall_finiteSchemeCover` applies. -/
@[stacks 089L]
theorem exists_chowDiagram (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (hfsep : IsSeparated B S hS f) (hfft : IsFiniteType B S hS f) :
    ∃ (X' Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hX' : IsAlgebraicSpace B S hS X')
      (_hXbar : IsAlgebraicSpace B S hS Xbar) (q : X' ⟶ X) (j : X' ⟶ Xbar) (g : Xbar ⟶ Y),
      IsProper B S hS q ∧ IsSurjective B S hS q ∧ IsOpenImmersion B S hS j ∧
        IsProper B S hS g ∧ yoneda.relativelyRepresentable g ∧ q ≫ f = j ≫ g :=
  exists_chowDiagram_of_forall_finiteSchemeCover B S hS hZ
    (existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace B S hS hZ)
    hX hY f hYqc hYqs hfsep hfft

end AlgebraicGeometry.Space

end
