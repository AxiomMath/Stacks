module

import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.AffineCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionLocusOnBase
import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableClosedSubspaceIdeal

/-! # A divisor on an étale chart of a family of curves descends near a closed fibre

This is the back half of step P2a of the proof of Stacks 0E6F (families of curves are
étale locally schemes). The statement `ChartDivisorDescends B hZ` is proved as
`chartDivisorDescends`; it is unregistered.

Setting: `Y` a family of curves, `P` the residue point of a closed point of `Y.base` (`P.value` a
closed immersion), `V` the fibre with `q`. `c : O ⟶ Y.total` an étale chart over `b : O ⟶ Y.base`,
`D` a relative effective Cartier divisor on `O` over `Y.base`, finite over `Y.base`. `G = O ×_Y V`
(a scheme of the site, `gO`, `gV`). On the fibre, `D` is the pullback of `E` and
`E ×_V G ⟶ V` is the closed immersion of `E` itself.

Conclusion: over an affine open `U' ∋ s` of `Y.base`, the image of `D ⟶ Y.total` is a relative
effective Cartier divisor `D'` of the base change `Y'` whose preimage in the fibre is `E`.

Route: `i := yoneda(D.subschemeι) ≫ c` is finite over the base and its base change to
`Spec κ(s)` is `E ×_V G ⟶ V`, a closed immersion; Stacks 05XA
(`Space.exists_isOpenSubspace_iff_isClosedImmersion_baseChange`) gives an open `W ∋ s` of the base
over which the base change of `i` is a closed immersion; take an affine open `U' ⊆ W` through
which `P` factors and `Y' = Y ×_{Y.base} U'`; `D'` is the range of the base-changed `i`, that is
of `D ∩ O' ⟶ O' ⟶ Y'` for `O' = O ×_{Y.base} U'`. Flat: `D' ≅ D ∩ O'`, a base change of
`D ⟶ Y.base`. Effective Cartier: Stacks 083C (4)
(`Space.isEffectiveCartierDivisor_of_hasAffinePrincipalEtaleNeighborhoods`). In
`H = D' ×_{Y'} O' ⟶ O'`, a closed immersion, the diagonal section of the étale projection
`H ⟶ D ∩ O'` is an open immersion (a section of an étale morphism), so the other sheets of `H` have
closed image in `O'` missing `D`; off it the inverse image of `D'` is `D`, which on small affine
opens is `V(f)` with `f` a nonzerodivisor.

## Main results

* `AlgebraicGeometry.C1590Private.exists_affine_isClosedImmersion_baseChange`: the 05XA step.
* `AlgebraicGeometry.C1590Private.isEffectiveCartierDivisor_range_yoneda_map_comp`: the image
  of an effective Cartier divisor of an étale chart, embedded by a closed immersion, is an
  effective Cartier divisor of the algebraic space.
* `AlgebraicGeometry.C1590Private.chartDivisorDescends`: `ChartDivisorDescends B hZ`. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **P2a, back half.** A finite relative effective Cartier divisor on an étale chart of a family
of curves, which on the closed fibre is the pullback of `E` and maps isomorphically onto `E`,
descends over an affine open neighbourhood of the closed point. -/
def ChartDivisorDescends : Prop :=
  ∀ (Y : CurveFamily B hZ)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj)
    (_ : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ Y.total.obj)
    (_ : IsPullback q (yoneda.map v) Y.toBase.hom (yonedaEquiv.symm P.value))
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData)
    (O : BigFppfOver B integerBase hZ) (c : yoneda.obj O ⟶ Y.total.obj)
    (_ : Space.IsEtale B integerBase hZ c) (b : O ⟶ Y.base) (_ : yoneda.map b = c ≫ Y.toBase.hom)
    (D : ((BigFppfOver.toScheme B integerBase hZ).obj O).IdealSheafData)
    (_ : Stacks.Divisors.IsRelativeEffectiveCartierDivisor
      ((BigFppfOver.toScheme B integerBase hZ).map b) D)
    (_ : IsFinite (D.subschemeι ≫ (BigFppfOver.toScheme B integerBase hZ).map b))
    (G : BigFppfOver B integerBase hZ) (gO : G ⟶ O) (gV : G ⟶ V)
    (_ : IsPullback (yoneda.map gO) (yoneda.map gV) c q)
    (_ : D.comap ((BigFppfOver.toScheme B integerBase hZ).map gO) =
      E.comap ((BigFppfOver.toScheme B integerBase hZ).map gV))
    (_ : IsClosedImmersion ((E.comap ((BigFppfOver.toScheme B integerBase hZ).map gV)).subschemeι ≫
      (BigFppfOver.toScheme B integerBase hZ).map gV))
    (_ : ((E.comap ((BigFppfOver.toScheme B integerBase hZ).map gV)).subschemeι ≫
      (BigFppfOver.toScheme B integerBase hZ).map gV).ker = E),
    ∃ (Y' : CurveFamily B hZ) (φ : Y' ⟶ Y) (t : P.siteObject ⟶ Y'.base)
      (q' : yoneda.obj V ⟶ Y'.total.obj) (D' : Space.ClosedSubspaces B integerBase hZ Y'.total.obj),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ∧
      t ≫ φ.baseMap = P.value ∧
      IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map t) ∧
      IsPullback q' (yoneda.map v) Y'.toBase.hom (yoneda.map t) ∧ q' ≫ φ.totalMap.hom = q ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Y'.base) ∧
      Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y'.toBase D' ∧
      D'.1.preimage q' = (Space.closedSubspaceOfIdeal V E).1

/-- A morphism whose underlying scheme map has range inside an open of the source of the
structure morphism of `T` factors through `openSubObj`. -/
private theorem exists_comp_openSubHom_eq {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (T : BigFppfOver B S hS) (V : T.left.obj.Opens) {X : BigFppfOver B S hS} (f : X ⟶ T)
    (hf : Set.range ((BigFppfOver.toScheme B S hS).map f) ⊆ Set.range V.ι) :
    ∃ t : X ⟶ BigFppfOver.openSubObj B S hS T V, t ≫ BigFppfOver.openSubHom B S hS T V = f := by
  have h := IsOpenImmersion.lift_fac V.ι ((BigFppfOver.toScheme B S hS).map f) hf
  refine ⟨Over.homMk (ObjectProperty.homMk (IsOpenImmersion.lift V.ι _ hf))
    (ObjectProperty.hom_ext _ ?_), Over.OverMorphism.ext (ObjectProperty.hom_ext _ h)⟩
  change IsOpenImmersion.lift V.ι _ hf ≫ (V.ι ≫ T.hom.hom) = X.hom.hom
  rw [← Category.assoc, h]
  exact congrArg (fun z => z.hom) (Over.w f)

/-- The closed subscheme of an object cut out by an ideal sheaf is a closed immersion with that
kernel. -/
private theorem isClosedImmersion_and_ker_map_closedSubschemeOverι
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (O : BigFppfOver B S hS)
    (I : ((BigFppfOver.toScheme B S hS).obj O).IdealSheafData) :
    IsClosedImmersion ((BigFppfOver.toScheme B S hS).map (Space.closedSubschemeOverι B S hS O I)) ∧
      ((BigFppfOver.toScheme B S hS).map (Space.closedSubschemeOverι B S hS O I)).ker = I := by
  rw [Space.toScheme_map_closedSubschemeOverι]
  exact ⟨inferInstanceAs (IsClosedImmersion I.subschemeι), Scheme.IdealSheafData.ker_subschemeι I⟩

/-! ### Open subspaces of a scheme and the closed immersion locus -/

section Locus

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- An open subspace of the algebraic space represented by an object `U` of the site is
represented by an open subscheme of `U`. -/
theorem exists_isOpenImmersion_of_isOpenSubspace (U : BigFppfOver B integerBase hZ)
    (W : Subfunctor (yoneda.obj U)) (hW : Space.IsOpenSubspace B integerBase hZ W) :
    ∃ (V : BigFppfOver B integerBase hZ) (j : V ⟶ U),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
      ∃ e : yoneda.obj V ≅ W.toFunctor, e.hom ≫ W.ι = yoneda.map j := by
  have h := hW.2.rep.isPullback (𝟙 (yoneda.obj U))
  have : IsIso (hW.2.rep.fst (𝟙 (yoneda.obj U))) := h.isIso_fst_of_isIso
  exact ⟨_, hW.2.rep.snd (𝟙 (yoneda.obj U)), hW.2.property_snd (𝟙 (yoneda.obj U)),
    asIso (hW.2.rep.fst (𝟙 (yoneda.obj U))), by simpa only [asIso_hom, Category.comp_id] using h.w⟩

/-- **Spreading out a closed immersion from a closed point of the base (Stacks 05XA).** Let
`π : X ⟶ Bs` be a separated morphism from an algebraic space to a scheme and `i : R ⟶ X` a
morphism from a scheme, finite over `Bs`. If the base change of `i` along a closed immersion
`s : Pt ⟶ Bs` of a one-point scheme is a closed immersion, then so is its base change along an
affine open neighbourhood `U' ⊆ Bs` of the image of `s`, through which `s` factors by a closed
immersion. -/
theorem exists_affine_isClosedImmersion_baseChange
    {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B integerBase hZ X)
    {Bs : BigFppfOver B integerBase hZ} (π : X ⟶ yoneda.obj Bs)
    (hπ : Space.IsSeparated B integerBase hZ π)
    {R : BigFppfOver B integerBase hZ} (i : yoneda.obj R ⟶ X) (pR : R ⟶ Bs)
    (hi : i ≫ π = yoneda.map pR)
    (hpR : IsFinite ((BigFppfOver.toScheme B integerBase hZ).map pR))
    {Pt : BigFppfOver B integerBase hZ} (s : Pt ⟶ Bs)
    (hsub : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj Pt))
    (pt : (BigFppfOver.toScheme B integerBase hZ).obj Pt)
    (hs : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map s))
    (hbc : Space.IsClosedImmersion B integerBase hZ
      (Space.baseChangeOverBase B integerBase hZ i (yoneda.map pR) π hi
        (yoneda.map s))) :
    ∃ (U' : BigFppfOver B integerBase hZ) (j : U' ⟶ Bs) (t : Pt ⟶ U'),
      IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U') ∧ t ≫ j = s ∧
      IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map t) ∧
      Space.IsClosedImmersion B integerBase hZ
        (Space.baseChangeOverBase B integerBase hZ i (yoneda.map pR) π hi
          (yoneda.map j)) := by
  classical
  have hprop : Space.IsProper B integerBase hZ (yoneda.map pR) :=
    (Space.isProper_yoneda_map_iff B integerBase hZ pR).2 inferInstance
  obtain ⟨W, hWopen, hW⟩ := Space.exists_isOpenSubspace_iff_isClosedImmersion_baseChange
    B integerBase hZ (isAlgebraicSpace_yoneda B integerBase hZ R) hX
    (isAlgebraicSpace_yoneda B integerBase hZ Bs) i (yoneda.map pR) π hi
    hprop.2.1.1 hprop.2.2 hπ
  obtain ⟨Wo, jW, hjW, e, he⟩ := exists_isOpenImmersion_of_isOpenSubspace Bs W hWopen
  obtain ⟨r, hr⟩ := (hW (yoneda.obj Pt) (isAlgebraicSpace_yoneda B integerBase hZ Pt)
    (yoneda.map s)).2 hbc
  set sW : Pt ⟶ Wo := yoneda.preimage (r ≫ e.inv) with hsWdef
  have hsW : sW ≫ jW = s := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hsWdef, Functor.map_preimage, Category.assoc, ← he,
      Iso.inv_hom_id_assoc, hr]
  obtain ⟨⟨V, hV⟩, hpV⟩ := Stacks.Divisors.exists_affineOpens_mem ((𝒯).map sW pt)
  set U' := BigFppfOver.openSubObj B integerBase hZ Wo V with hU'
  set kU : U' ⟶ Wo := BigFppfOver.openSubHom B integerBase hZ Wo V with hkU
  have hkUm : (𝒯).map kU = V.ι := rfl
  have hrange : Set.range ((𝒯).map sW) ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim z pt]
    exact hpV
  obtain ⟨t, htk⟩ := exists_comp_openSubHom_eq Wo V sW hrange
  have hts : t ≫ (kU ≫ jW) = s := by rw [← Category.assoc, htk, hsW]
  have : IsOpenImmersion ((𝒯).map (kU ≫ jW)) := by
    rw [Functor.map_comp, hkUm]; infer_instance
  refine ⟨U', kU ≫ jW, t, inferInstance, hV, hts, ?_, ?_⟩
  · have : IsClosedImmersion ((𝒯).map t ≫ (𝒯).map (kU ≫ jW)) := by
      rw [← Functor.map_comp, hts]; exact hs
    exact IsClosedImmersion.of_comp ((𝒯).map t) ((𝒯).map (kU ≫ jW))
  · exact (hW (yoneda.obj U') (isAlgebraicSpace_yoneda B integerBase hZ U')
      (yoneda.map (kU ≫ jW))).1 ⟨yoneda.map kU ≫ e.hom, by
        rw [Category.assoc, he, ← Functor.map_comp]⟩

end Locus

/-! ### The image of a closed subscheme of an étale chart -/

section EffectiveCartier

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- **The image of an effective Cartier divisor of an étale chart, embedded by a closed
immersion, is an effective Cartier divisor.** Let `c : O ⟶ X` be an étale chart of an algebraic
space and `d : R ⟶ O` a closed immersion of schemes whose ideal sheaf is effective Cartier. If
the composite `R ⟶ X` is a closed immersion, its image is an effective Cartier divisor of `X`.

In `H = R ×_X O ⟶ O`, a closed immersion, the diagonal section `R ⟶ H` of the étale projection
`H ⟶ R` is an open immersion; so the image in `O` of the rest of `H` is closed and misses `R`.
Off that closed set the inverse image of the image of `R` is `R` itself, and Stacks 083C (4)
applies with the affine opens on which `R` is cut out by a nonzerodivisor. -/
theorem isEffectiveCartierDivisor_range_yoneda_map_comp (X : AlgebraicSpaces B S hS)
    {O R : BigFppfOver B S hS} (c : yoneda.obj O ⟶ X.1) (hc : Space.IsEtale B S hS c)
    (d : R ⟶ O) [IsClosedImmersion ((BigFppfOver.toScheme B S hS).map d)]
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor
      ((BigFppfOver.toScheme B S hS).map d).ker)
    (hi : Space.IsClosedImmersion B S hS (yoneda.map d ≫ c)) :
    Space.IsEffectiveCartierDivisor B S hS X
      ⟨Subfunctor.range (yoneda.map d ≫ c),
        Space.isClosedSubspace_range_of_isClosedImmersion B S hS _
          (isAlgebraicSpace_yoneda B S hS R) hi⟩ := by
  classical
  set i := yoneda.map d ≫ c with hidef
  have hcp := Space.presheaf_etale_of_isEtale B S hS hc
  -- `H = R ×_X O`
  set H := hi.rep.pullback c with hH
  set h2 : H ⟶ O := hi.rep.snd c with hh2def
  set φ : H ⟶ R := yoneda.preimage (hi.rep.fst c) with hφdef
  have hpb : IsPullback (yoneda.map φ) (yoneda.map h2) i c := by
    rw [hφdef, Functor.map_preimage]
    exact hi.rep.isPullback c
  have hh2 : IsClosedImmersion ((𝒯).map h2) := hi.property_snd c
  have hφ : Etale ((𝒯).map φ) := hcp.2 i (yoneda.map h2) φ hpb.flip
  -- the diagonal section of `H ⟶ R`
  set σ : R ⟶ H := yoneda.preimage (hpb.lift (𝟙 _) (yoneda.map d) (by simp [i])) with hσdef
  have hσφ : σ ≫ φ = 𝟙 R := by
    apply yoneda.map_injective
    simp [hσdef]
  have hσh2 : σ ≫ h2 = d := by
    apply yoneda.map_injective
    simp [hσdef]
  have hσ : IsOpenImmersion ((𝒯).map σ) :=
    isOpenImmersion_of_section_of_etale ((𝒯).map φ) ((𝒯).map σ)
      (by rw [← Functor.map_comp, hσφ, CategoryTheory.Functor.map_id])
  -- the closed set swept out by the other sheets, and its open complement
  set Bad : Set ((𝒯).obj O) := (𝒯).map h2 '' (Set.range ((𝒯).map σ))ᶜ with hBad
  have hBadc : IsClosed Bad :=
    ((𝒯).map h2).isClosedEmbedding.isClosedMap _
      ((𝒯).map σ).isOpenEmbedding.isOpen_range.isClosed_compl
  set O'' : ((𝒯).obj O).Opens := ⟨Badᶜ, hBadc.isOpen_compl⟩ with hO''
  have hinj : Function.Injective ((𝒯).map h2) := ((𝒯).map h2).isClosedEmbedding.injective
  have hgood : ∀ z, (𝒯).map d z ∈ O'' := by
    rintro z ⟨h, hh, he⟩
    apply hh
    refine ⟨z, hinj ?_⟩
    rw [he, ← Scheme.Hom.comp_apply, ← Functor.map_comp, hσh2]
  have hsep : ∀ {T' : BigFppfOver B S hS} (ρ : T' ⟶ H),
      Set.range ((𝒯).map (ρ ≫ h2)) ⊆ (O'' : Set ((𝒯).obj O)) →
        ∃ z : T' ⟶ R, z ≫ d = ρ ≫ h2 := by
    intro T' ρ hρ
    have hsub : Set.range ((𝒯).map ρ) ⊆ Set.range ((𝒯).map σ) := by
      rintro _ ⟨τ, rfl⟩
      by_contra hn
      exact hρ ⟨τ, rfl⟩ ⟨(𝒯).map ρ τ, hn, by rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]⟩
    have hfac := IsOpenImmersion.lift_fac ((𝒯).map σ) ((𝒯).map ρ) hsub
    have hle : ((𝒯).map d).ker ≤ ((𝒯).map (ρ ≫ h2)).ker := by
      rw [Functor.map_comp, ← hfac, Category.assoc, ← Functor.map_comp, hσh2]
      exact Scheme.Hom.le_ker_comp _ _
    obtain ⟨z, hz⟩ :=
      (Space.mem_range_yoneda_map_iff B S hS d inferInstance (T := Opposite.op T')
        (ρ ≫ h2)).2 hle
    exact ⟨z, hz⟩
  refine Space.isEffectiveCartierDivisor_of_hasAffinePrincipalEtaleNeighborhoods B S hS X _ ?_
  rw [Space.hasAffinePrincipalEtaleNeighborhoods_iff]
  intro x
  have : Mono i := Space.mono_of_isClosedImmersion B S hS i hi
  -- a field-valued point of `R` over `x`
  obtain ⟨p, hp⟩ : ∃ p : Space.FieldValuedPoint B S hS (yoneda.obj R),
      Space.pointsMap B S hS _ i (p.class B S hS _) =
        Space.pointsMap B S hS _ (Subfunctor.range i).ι x := by
    obtain ⟨p, hpc : p.class B S hS _ = _⟩ :=
      Quot.exists_rep (Space.pointsMap B S hS _ (inv (Subfunctor.toRange i)) x)
    refine ⟨p, ?_⟩
    calc Space.pointsMap B S hS _ i (p.class B S hS _)
        = Space.pointsMap B S hS _ (Subfunctor.toRange i ≫ (Subfunctor.range i).ι)
            (p.class B S hS _) := by rw [Subfunctor.toRange_ι]
      _ = _ := by
        rw [hpc, ← Space.pointsMap_comp_apply, IsIso.inv_hom_id_assoc]
  set w := (𝒯).map (p.value ≫ d) (IsLocalRing.closedPoint p.carrier) with hw
  have hwO : w ∈ O'' := hgood ((𝒯).map p.value (IsLocalRing.closedPoint p.carrier))
  obtain ⟨A, hA, hwA, hAO, f, hf, hgen⟩ :=
    Stacks.Divisors.exists_basicOpen_isRegular_span_of_isEffectiveCartierDivisor _ hD w O'' hwO
  -- the affine chart
  set Uv := BigFppfOver.openSubObj B S hS O A with hUv
  set kV : Uv ⟶ O := BigFppfOver.openSubHom B S hS O A with hkV
  have hkVm : (𝒯).map kV = A.ι := rfl
  set g := yoneda.map kV ≫ c with hgdef
  have hg : Space.IsEtale B S hS g :=
    Space.isEtale_yoneda_map_comp B S hS c kV (by rw [hkVm]; infer_instance) hc
  -- the point of the chart
  have hrange : Set.range ((𝒯).map (p.value ≫ d)) ⊆ Set.range A.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim (α := PrimeSpectrum p.carrier) z
      (IsLocalRing.closedPoint p.carrier)]
    exact hwA
  obtain ⟨qv, hqv⟩ := exists_comp_openSubHom_eq O A (p.value ≫ d) hrange
  set p' : Space.FieldValuedPoint B S hS (yoneda.obj Uv) :=
    { carrier := p.carrier
      contained := p.contained
      toBase := p.toBase
      value := qv } with hp'd
  -- the inverse image of the image of `R` on the chart is `R ∩ A`
  have hAaff : IsAffine ((𝒯).obj Uv) := hA
  set I := (((𝒯).map d).ker).comap A.ι with hIdef
  have hI : I = Scheme.IdealSheafData.ofIdealTop (Ideal.span {A.topIso.inv.hom f}) :=
    Stacks.Divisors.comap_ι_eq_ofIdealTop_of_ideal_eq_span _ A hA f hgen
  set jR := Space.closedSubschemeOverι B S hS Uv I with hjR
  obtain ⟨hjRci, hkerjR⟩ := isClosedImmersion_and_ker_map_closedSubschemeOverι Uv I
  have hpre : (Subfunctor.range i).preimage g = Subfunctor.range (yoneda.map jR) := by
    have hr : (Subfunctor.range i).preimage c = Subfunctor.range (yoneda.map h2) :=
      (Subfunctor.range_snd_eq_preimage_range_of_isPullback hpb).symm
    rw [hgdef, Subfunctor.preimage_comp, hr]
    ext ⟨T'⟩ y
    change y ≫ kV ∈ (Subfunctor.range (yoneda.map h2)).obj _ ↔
      y ∈ (Subfunctor.range (yoneda.map jR)).obj _
    rw [Space.mem_range_yoneda_map_iff B S hS jR inferInstance, hkerjR]
    refine ⟨?_, fun hle => ?_⟩
    · rintro ⟨ρ, hρ⟩
      have hρ' : ρ ≫ h2 = y ≫ kV := hρ
      obtain ⟨z, hz⟩ := hsep ρ (by
        rw [hρ', Functor.map_comp, hkVm]
        rintro _ ⟨τ, rfl⟩
        have hmem : A.ι ((𝒯).map y τ) ∈ Set.range A.ι := ⟨_, rfl⟩
        rw [Scheme.Opens.range_ι] at hmem
        exact hAO hmem)
      have hle : ((𝒯).map d).ker ≤ ((𝒯).map (y ≫ kV)).ker := by
        rw [← hρ', ← hz, Functor.map_comp]
        exact Scheme.Hom.le_ker_comp _ _
      rw [Functor.map_comp, hkVm, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.le_map_iff_comap_le] at hle
      exact hle
    · have hle' : ((𝒯).map d).ker ≤ ((𝒯).map (y ≫ kV)).ker := by
        rw [Functor.map_comp, hkVm, Scheme.Hom.ker_comp,
          Scheme.IdealSheafData.le_map_iff_comap_le]
        exact hle
      obtain ⟨z, hz⟩ := (Space.mem_range_yoneda_map_iff B S hS d inferInstance
        (T := Opposite.op T') (y ≫ kV)).2 hle'
      refine ⟨z ≫ σ, ?_⟩
      change (z ≫ σ) ≫ h2 = y ≫ kV
      rw [Category.assoc, hσh2]
      exact hz
  refine ⟨Uv, g, p'.class B S hS _, hAaff, hg, ?_, A.topIso.inv.hom f,
    Stacks.Divisors.isRegular_ringEquiv A.topIso.symm.commRingCatIsoToRingEquiv hf, ?_⟩
  · rw [← hp]
    change (Space.FieldValuedPoint.map B S hS _ g p').class B S hS _ =
      (Space.FieldValuedPoint.map B S hS _ i p).class B S hS _
    apply congrArg (Space.FieldValuedPoint.class B S hS X.1)
    change (⟨p.carrier, p.contained, p.toBase, c.app _ (qv ≫ kV)⟩ :
      Space.FieldValuedPoint B S hS X.1) = ⟨p.carrier, p.contained, p.toBase, c.app _ (p.value ≫ d)⟩
    rw [hqv]
  · rw [Space.ker_rep_snd_eq_ker_of_range_eq B S hS X _ Uv _ g jR hpre, hkerjR, hI]
    rfl

end EffectiveCartier

/-! ### The proof -/

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **P2a, back half, proved.** A finite relative effective Cartier divisor `D` on an étale chart
`c : O ⟶ Y.total` of a family of curves, which on the closed fibre is the pullback of `E` and
maps isomorphically onto `E`, descends over an affine open neighbourhood `U'` of the closed
point: its image in `Y' = Y ×_{Y.base} U'` is a relative effective Cartier divisor whose
preimage in the fibre is `E`. -/
theorem chartDivisorDescends : ChartDivisorDescends B hZ := by
  intro Y P hP V v q hq E O c hc b hb D hD hDfin G gO gV hG hDE hEci hEker
  classical
  -- cleanly typed names for the structure morphism and the closed point
  obtain ⟨π, hπ⟩ : ∃ π : Y.total.obj ⟶ yoneda.obj Y.base, π = Y.toBase.hom := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : P.siteObject ⟶ Y.base, s = P.value := ⟨_, rfl⟩
  have hπsep : Space.IsSeparated B integerBase hZ π := by rw [hπ]; exact Y.proper.1
  have hb' : yoneda.map b = c ≫ π := by rw [hπ]; exact hb
  have hq' : IsPullback q (yoneda.map v) π (yoneda.map s) := by
    have hPv : yonedaEquiv.symm P.value = yoneda.map s :=
      yonedaEquiv.symm_apply_eq.2 (by rw [hs]; exact (yonedaEquiv_yoneda_map _).symm)
    rw [hπ, ← hPv]
    exact hq
  have hsci : IsClosedImmersion ((𝒯).map s) := by rw [hs]; exact hP
  -- the divisor as an object of the site
  set Dobj := Space.closedSubschemeOverObj B integerBase hZ O D with hDobj
  set dι : Dobj ⟶ O := Space.closedSubschemeOverι B integerBase hZ O D with hdιdef
  have hdι : (𝒯).map dι = D.subschemeι :=
    Space.toScheme_map_closedSubschemeOverι B integerBase hZ O D
  obtain ⟨hdιci, hkerdι⟩ := isClosedImmersion_and_ker_map_closedSubschemeOverι O D
  set pD : Dobj ⟶ Y.base := dι ≫ b with hpDdef
  have hpDfin : IsFinite ((𝒯).map pD) := by rw [hpDdef, Functor.map_comp, hdι]; exact hDfin
  have hpDflat : Flat ((𝒯).map pD) := by rw [hpDdef, Functor.map_comp, hdι]; exact hD.2
  set i : yoneda.obj Dobj ⟶ Y.total.obj := yoneda.map dι ≫ c with hidef
  have hi : i ≫ π = yoneda.map pD := by
    rw [hidef, hpDdef, Functor.map_comp, hb', Category.assoc]
  -- the fibre of the divisor over the closed point
  have hQ2 : IsPullback (yoneda.map (pullback.fst dι gO))
      (yoneda.map (pullback.snd dι gO ≫ gV)) i q := by
    have h1 := (IsPullback.of_hasPullback dι gO).map yoneda
    rw [Functor.map_comp, hidef]
    exact h1.paste_vert hG
  have hsnd : ∀ {Z : BigFppfOver B integerBase hZ} (g : Z ⟶ O),
      IsClosedImmersion ((𝒯).map (pullback.snd dι g)) ∧
        ((𝒯).map (pullback.snd dι g)).ker = D.comap ((𝒯).map g) := fun g => by
    have hsq := (𝒯).map_isPullback (IsPullback.of_hasPullback dι g)
    exact ⟨MorphismProperty.of_isPullback hsq inferInstance,
      by rw [Stacks.Divisors.ker_eq_comap_of_isPullback hsq.flip, hkerdι]⟩
  have := (hsnd gO).1
  have hker1 : ((𝒯).map (pullback.snd dι gO)).ker = E.comap ((𝒯).map gV) := by
    rw [(hsnd gO).2, hDE]
  have hε : IsClosedImmersion ((𝒯).map (pullback.snd dι gO ≫ gV)) ∧
      ((𝒯).map (pullback.snd dι gO ≫ gV)).ker = E := by
    set K := ((𝒯).map (pullback.snd dι gO)).ker with hK
    have hfac : (𝒯).map (pullback.snd dι gO) =
        (Stacks.Divisors.closedImmersionKerIso _).hom ≫ K.subschemeι :=
      Stacks.Divisors.closedImmersion_eq_kerIso_comp _
    have h1 : IsClosedImmersion (K.subschemeι ≫ (𝒯).map gV) := by rw [hker1]; exact hEci
    have h2 : (K.subschemeι ≫ (𝒯).map gV).ker = E := by rw [hker1]; exact hEker
    rw [Functor.map_comp, hfac, Category.assoc]
    exact ⟨inferInstance, by rw [Scheme.Hom.ker_comp_of_isIso, h2]⟩
  have := hε.1
  have hrangeE : Subfunctor.range (yoneda.map (pullback.snd dι gO ≫ gV)) =
      (Space.closedSubspaceOfIdeal V E).1 := by
    obtain ⟨hEι, hEk⟩ := isClosedImmersion_and_ker_map_closedSubschemeOverι V E
    ext ⟨T'⟩ y
    change y ∈ (Subfunctor.range (yoneda.map (pullback.snd dι gO ≫ gV))).obj _ ↔
      y ∈ (Subfunctor.range (yoneda.map (Space.closedSubschemeOverι B integerBase hZ V E))).obj _
    rw [Space.mem_range_yoneda_map_iff B integerBase hZ _ hε.1,
      Space.mem_range_yoneda_map_iff B integerBase hZ _ hEι, hEk, hε.2]
  -- the base change of `D ⟶ Y.total` to the closed point is a closed immersion
  have hbcP : Space.IsClosedImmersion B integerBase hZ
      (Space.baseChangeOverBase B integerBase hZ i (yoneda.map pD) π hi (yoneda.map s)) := by
    have hbc := Space.isPullback_baseChangeOverBase B integerBase hZ i (yoneda.map pD) π hi
      (yoneda.map s)
    have hQ2' : IsPullback (yoneda.map (pullback.fst dι gO))
        (yoneda.map (pullback.snd dι gO ≫ gV) ≫ hq'.isoPullback.hom) i
        (pullback.fst π (yoneda.map s)) :=
      IsPullback.of_iso hQ2 (Iso.refl _) (Iso.refl _) hq'.isoPullback (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)
    have he := hQ2'.isoIsPullback_hom_snd _ _ hbc
    have hcl : Space.IsClosedImmersion B integerBase hZ
        (yoneda.map (pullback.snd dι gO ≫ gV) ≫ hq'.isoPullback.hom) :=
      (MorphismProperty.cancel_right_of_respectsIso
        (Space.closedImmersionPresheafProperty B integerBase hZ) _ _).2
        ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B integerBase hZ _ _).2 hε.1)
    rw [← he] at hcl
    exact (MorphismProperty.cancel_left_of_respectsIso
      (Space.closedImmersionPresheafProperty B integerBase hZ) _ _).1 hcl
  -- an affine open neighbourhood of the closed point over which it is a closed immersion
  obtain ⟨U', j, t, hjopen, hU'aff, hts, htci, hbcj⟩ :=
    exists_affine_isClosedImmersion_baseChange Y.total.property π hπsep i pD hi hpDfin s
      (inferInstanceAs (Subsingleton (PrimeSpectrum P.carrier)))
      (IsLocalRing.closedPoint P.carrier) hsci hbcP
  -- the base change of the total space
  set Yfst := pullback.fst π (yoneda.map j) with hYfst
  set Ysnd := pullback.snd π (yoneda.map j) with hYsnd
  have hYpb : IsPullback Yfst Ysnd π (yoneda.map j) := IsPullback.of_hasPullback _ _
  have hts' : yoneda.map t ≫ yoneda.map j = yoneda.map s := by rw [← Functor.map_comp, hts]
  set q'' : yoneda.obj V ⟶ pullback π (yoneda.map j) :=
    pullback.lift q (yoneda.map (v ≫ t)) (by rw [hq'.w, Functor.map_comp, Category.assoc, hts'])
    with hq''def
  have hq''fst : q'' ≫ Yfst = q := pullback.lift_fst _ _ _
  have hq''snd : q'' ≫ Ysnd = yoneda.map (v ≫ t) := pullback.lift_snd _ _ _
  have hq''pb : IsPullback q'' (yoneda.map v) Ysnd (yoneda.map t) := by
    have hout : IsPullback (q'' ≫ Yfst) (yoneda.map v) π (yoneda.map t ≫ yoneda.map j) := by
      rw [hq''fst, hts']; exact hq'
    exact IsPullback.of_right hout (by rw [hq''snd, Functor.map_comp]) hYpb
  -- the open of the chart over `U'`
  have hOsq := IsPullback.of_hasPullback b j
  have : IsOpenImmersion ((𝒯).map (pullback.fst b j)) :=
    MorphismProperty.of_isPullback ((𝒯).map_isPullback hOsq).flip hjopen
  have hbj : yoneda.map (pullback.fst b j) ≫ yoneda.map b =
      yoneda.map (pullback.snd b j) ≫ yoneda.map j := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  set c' : yoneda.obj (pullback b j) ⟶ pullback π (yoneda.map j) :=
    pullback.lift (yoneda.map (pullback.fst b j) ≫ c) (yoneda.map (pullback.snd b j)) (by
      rw [Category.assoc, ← hb']; exact hbj) with hc'def
  have hc'fst : c' ≫ Yfst = yoneda.map (pullback.fst b j) ≫ c := pullback.lift_fst _ _ _
  have hc'snd : c' ≫ Ysnd = yoneda.map (pullback.snd b j) := pullback.lift_snd _ _ _
  have hQ4 : IsPullback c' (yoneda.map (pullback.fst b j)) Yfst c := by
    have hout : IsPullback (c' ≫ Ysnd) (yoneda.map (pullback.fst b j)) (yoneda.map j)
        (c ≫ π) := by
      rw [hc'snd, ← hb']; exact (hOsq.map yoneda).flip
    exact IsPullback.of_right hout hc'fst hYpb.flip
  have hcp := Space.presheaf_etale_of_isEtale B integerBase hZ hc
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Etale) 𝒯)
  have hc' : Space.IsEtale B integerBase hZ c' :=
    Space.isEtale_of_presheaf_etale B integerBase hZ (MorphismProperty.of_isPullback hQ4.flip hcp)
  -- the divisor over `U'`
  have hDsq := IsPullback.of_hasPullback dι (pullback.fst b j)
  have := (hsnd (pullback.fst b j)).1
  have hkerdO := (hsnd (pullback.fst b j)).2
  set i' := yoneda.map (pullback.snd dι (pullback.fst b j)) ≫ c' with hi'def
  have hQ1 : IsPullback (yoneda.map (pullback.fst dι (pullback.fst b j))) i' i Yfst :=
    ((hDsq.map yoneda).flip.paste_horiz hQ4).flip
  have hi' : Space.IsClosedImmersion B integerBase hZ i' := by
    have hbc := Space.isPullback_baseChangeOverBase B integerBase hZ i (yoneda.map pD) π hi
      (yoneda.map j)
    have he := hQ1.isoIsPullback_hom_snd _ _ hbc
    rw [← he]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (Space.closedImmersionPresheafProperty B integerBase hZ) _ _).2 hbcj
  have : Mono i' := Space.mono_of_isClosedImmersion B integerBase hZ i' hi'
  have hi'snd : i' ≫ Ysnd =
      yoneda.map (pullback.snd dι (pullback.fst b j) ≫ pullback.snd b j) := by
    rw [hi'def, Category.assoc, hc'snd, Functor.map_comp]
  -- the image of the divisor in the base change
  set Xt : AlgebraicSpaces B integerBase hZ := ⟨pullback π (yoneda.map j),
    isAlgebraicSpace_pullback B integerBase hZ π (yoneda.map j) Y.total.property
      (isAlgebraicSpace_yoneda B integerBase hZ U')
      (isAlgebraicSpace_yoneda B integerBase hZ Y.base)⟩ with hXt
  have hEC := isEffectiveCartierDivisor_range_yoneda_map_comp Xt c' hc'
    (pullback.snd dι (pullback.fst b j))
    (by rw [hkerdO]; exact Stacks.Divisors.isPullbackDefined_of_flat _ _ hD.1) hi'
  have hFlat : Space.IsFlat B integerBase hZ ((Subfunctor.range i').ι ≫ Ysnd) := by
    have hflat : Flat ((𝒯).map (pullback.snd dι (pullback.fst b j) ≫ pullback.snd b j)) :=
      MorphismProperty.of_isPullback ((𝒯).map_isPullback (hDsq.paste_vert hOsq)) hpDflat
    have hι : (Subfunctor.range i').ι = inv (Subfunctor.toRange i') ≫ i' := by
      rw [IsIso.eq_inv_comp, Subfunctor.toRange_ι]
    rw [hι, Category.assoc, hi'snd]
    have := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B integerBase hZ (@Flat)
    exact (MorphismProperty.cancel_left_of_respectsIso
      (fun _ _ f => Space.IsFlat B integerBase hZ f) _ _).2
      (Space.isFlat_yoneda_map B integerBase hZ _ hflat)
  -- the preimage in the fibre
  have hgob : gO ≫ b = gV ≫ v ≫ s := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hb', ← Category.assoc, hG.w, Category.assoc, hq'.w,
      Functor.map_comp, Functor.map_comp]
  have hζ : (pullback.snd dι gO ≫ gO) ≫ b = ((pullback.snd dι gO ≫ gV) ≫ v ≫ t) ≫ j := by
    rw [Category.assoc, hgob, Category.assoc, Category.assoc, Category.assoc, hts]
  set ζ : pullback dι gO ⟶ pullback b j := pullback.lift _ _ hζ with hζdef
  set ξ : pullback dι gO ⟶ pullback dι (pullback.fst b j) :=
    pullback.lift (pullback.fst dι gO) ζ (by rw [hζdef, pullback.lift_fst, pullback.condition])
    with hξdef
  have hξfst : ξ ≫ pullback.fst dι (pullback.fst b j) = pullback.fst dι gO :=
    pullback.lift_fst _ _ _
  have hξsnd : ξ ≫ pullback.snd dι (pullback.fst b j) = ζ := pullback.lift_snd _ _ _
  have hζfst : ζ ≫ pullback.fst b j = pullback.snd dι gO ≫ gO := pullback.lift_fst _ _ _
  have hζsnd : ζ ≫ pullback.snd b j = (pullback.snd dι gO ≫ gV) ≫ v ≫ t :=
    pullback.lift_snd _ _ _
  have hQ3 : IsPullback (yoneda.map ξ) (yoneda.map (pullback.snd dι gO ≫ gV)) i' q'' := by
    have hout : IsPullback (yoneda.map ξ ≫ yoneda.map (pullback.fst dι (pullback.fst b j)))
        (yoneda.map (pullback.snd dι gO ≫ gV)) i (q'' ≫ Yfst) := by
      rw [← Functor.map_comp, hξfst, hq''fst]
      exact hQ2
    refine IsPullback.of_right hout ?_ hQ1
    apply pullback.hom_ext
    · rw [← hYfst, Category.assoc (yoneda.map _) q'' Yfst, hq''fst, hi'def, Category.assoc,
        Category.assoc, hc'fst, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, hξsnd, hζfst, Functor.map_comp, Functor.map_comp, Category.assoc,
        Category.assoc, hG.w]
    · rw [← hYsnd, Category.assoc (yoneda.map _) q'' Ysnd, hq''snd, hi'def, Category.assoc,
        Category.assoc, hc'snd, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
        ← Category.assoc, hξsnd, hζsnd]
  have hpre : (Subfunctor.range i').preimage q'' = (Space.closedSubspaceOfIdeal V E).1 := by
    rw [← Subfunctor.range_snd_eq_preimage_range_of_isPullback hQ3, hrangeE]
  -- assembly
  subst hπ hs
  exact ⟨Y.ofIsPullback B hZ j _ _
      (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ Y.toBase (schemeSpaceMap j)),
    Y.homOfIsPullback B hZ j _ _
      (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ Y.toBase (schemeSpaceMap j)),
    t, q'', ⟨Subfunctor.range i', Space.isClosedSubspace_range_of_isClosedImmersion B integerBase hZ
      i' (isAlgebraicSpace_yoneda B integerBase hZ _) hi'⟩,
    hjopen, hts, htci, hq''pb, hq''fst, hU'aff, ⟨hEC, hFlat⟩, hpre⟩

end AlgebraicGeometry.C1590Private

end
