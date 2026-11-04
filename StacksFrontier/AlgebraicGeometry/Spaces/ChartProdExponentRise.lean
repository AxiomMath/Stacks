module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartProdHomRestrictAgreement

/-!
# Raising the exponent of the ideal until the kernel-pair relocalizations agree

Let `X` be an algebraic space over a scheme `S` of a big fppf site `B`, let `ℐ ⊆ 𝒪_X` be a sheaf
of ideals which is cartesian on affine charts, let `U = X ∖ V(ℐ)`, let `𝒢` be coherent and `ℱ`
quasi-coherent, let `θ : 𝒢|_U ⟶ ℱ|_U` and let `A` be an étale scheme chart of `X`.  A morphism
`φ : Iᵏ · 𝒢|_A ⟶ ℱ|_A` on the chart's scheme restricting to the transport of `θ` gives, through
`AlgebraicGeometry.Space.chartAlpha`, a morphism `α : (ℐᵏ𝒢)|_A ⟶ ℱ|_A` of the restrictions to the
slice of the small étale site at `A`, and the one-chart gluing
`AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod` asks for the two relocalizations
of `α` to the kernel pair `A ⨯ A` to agree.

They need not: all that
`StacksFrontier/AlgebraicGeometry/Spaces/ChartProdHomRestrictAgreement.lean` gives is that the two
morphisms on the scheme of `A ⨯ A` whose chart transports they are have the same restriction to
the complement of the support of the chartwise sheaf of ideals.  **This file closes the gap by
raising the exponent.**  The injectivity clause of the first display of [Stacks, Tag 01YB] on the
scheme of `A ⨯ A` turns that agreement after restriction into an agreement in the colimit, and a
filtered colimit of concrete objects identifies two representatives which agree in it after a
finite number of transition maps; the transition maps of the two direct systems are identified by
`AlgebraicGeometry.Space.chartAlpha_idealPowSmulMap_comp`, so the agreement obtained at the higher
exponent on the chart's scheme is read back as the agreement of the two relocalizations there.

**Raising the exponent is not optional.**  The transition maps of both systems are precomposition
with a monomorphism, hence not injective, so an agreement which holds in the colimit does not hold
at the exponent one started from.

## Main results

* `AlgebraicGeometry.Space.exists_val_eq_homRestr`: a relocalization of a morphism of the slice
  restrictions is the underlying morphism of a morphism of *sheaves* of modules on the slice at
  the smaller chart.  This is what `AlgebraicGeometry.Space.bijective_chartAlpha` has to be
  applied to; see the implementation notes for why no such morphism is *defined*.
* `AlgebraicGeometry.Space.overFunctor_map_comp_val`: the underlying morphism of a composite whose
  first factor is the restriction to the slice of a morphism of `𝒪_X`-modules, by `rfl`.
* `AlgebraicGeometry.Space.homRestr_chartAlphaSheaf_idealPowSmulMap_comp_val`: **relocalizing the
  chart transport at the raised exponent is precomposing the relocalization at the original
  exponent with the restriction of the inclusion `ℐⁿ𝒢 ⟶ ℐᵏ𝒢`.**  This is
  `AlgebraicGeometry.Space.chartAlpha_idealPowSmulMap_comp` read through
  `Stacks.PresheafOfModules.homRestr_restrFun_map_comp`.
* `AlgebraicGeometry.Space.exists_homRestr_prod_eq`: **the exponent rise.**  There are an exponent
  `n` and a morphism `φ'` on the chart's scheme at that exponent, still restricting to the
  transport of `θ`, whose chart transport has **equal** relocalizations to the kernel pair.
  This is the compatibility condition of
  `AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod`.

## Implementation notes

**No sheaf-level relocalization is defined.**  Wrapping `AlgebraicGeometry.Space.homRestr` as a
morphism of sheaves of modules typechecks, but the `rfl` which says that the `val`
field of the wrapper is the relocalization again does not fit in the heartbeat budget, because it
has to unfold the wrapping definition at the chart data.  The *existence* statement
`AlgebraicGeometry.Space.exists_val_eq_homRestr`, whose witness is the anonymous constructor and
whose equation is immediate, costs nothing; so the wrapper is obtained where it is needed and
never named.

**The hypotheses at the kernel pair are the Noetherian hypothesis there and nothing else.**  The
scheme of `A ⨯ A` is Noetherian but it is not an affine chart, so coherence of the chart
restriction of `𝒢` there is `AlgebraicGeometry.Space.isCoherent_chartPush` and not
`AlgebraicGeometry.Space.isCoherent_chartSchemeModule`; quasi-coherence of the chart restriction
of `ℱ` is unconditional.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Two `rfl`s about the slice restriction -/

/-- **A relocalization of a morphism of the slice restrictions is the underlying morphism of a
morphism of sheaves of modules on the slice at the smaller chart.**

A morphism of the slice restrictions of two sheaves of modules has an underlying morphism of the
`restrFun` restrictions with no transport (`AlgebraicGeometry.Space.val_app_homRestr_apply`), so
the anonymous constructor of `CategoryTheory.SheafOfModules.Hom` applies; stating the equation for
*that* witness costs nothing, whereas naming the wrapper as a definition makes the same equation
unaffordable.  See the implementation notes. -/
theorem exists_val_eq_homRestr (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    {A A' : SmallEtale B S hS X.1} (p : A' ⟶ A) (α : M.over A ⟶ N.over A) :
    ∃ β : M.over A' ⟶ N.over A',
      β.val = homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) M.val N.val p α.val :=
  ⟨⟨homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) M.val N.val p α.val⟩, rfl⟩

/-- **The underlying morphism of a composite whose first factor is the restriction to the slice at
a chart of a morphism of `𝒪_X`-modules**, by `rfl`: the restriction to a slice is a direct image
with the identity change of scalars, so it agrees with `restrFun` on morphisms. -/
theorem overFunctor_map_comp_val (M M' N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (u : M ⟶ M') (Y : SmallEtale B S hS X.1) (γ : M'.over Y ⟶ N.over Y) :
    ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) Y).map u ≫ γ).val =
      (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) Y).map u.val ≫ γ.val := rfl

/-! ### The chart transport at a raised exponent -/

variable (I : IdealSheaves B S hS X.1 X.2)
    (hIc : IsCartesianOnAffineCharts I.toSheafOfModules)
    (G F : Modules.{u, u} B S hS X.1 X.2)
    (hZt : B.Contains (⊤_ Scheme.{u})) (hNo : IsNoetherian B S hS hZt X.1)
    (hIq : I.toSheafOfModules.IsQuasicoherentOnSite) (hFq : F.IsQuasicoherentOnSite)
    (hG : IsCoherent B S hS X.1 X.2 G) (A : SmallEtale B S hS X.1)

/-- **The chart transport at a raised exponent is the chart transport at the original exponent
precomposed with the restriction to the slice of the inclusion `ℐⁿ𝒢 ⟶ ℐᵏ𝒢`**, read on underlying
morphisms of presheaves of modules.  This is
`AlgebraicGeometry.Space.chartAlpha_idealPowSmulMap_comp`. -/
theorem chartAlphaSheaf_idealPowSmulMap_comp_val (k n : ℕ) (h : k ≤ n)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A) :
    (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A n
          (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
            (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h ≫ φ)).val =
      (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) A).map
          (idealPowModuleHomOfLE I G h).val ≫
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val :=
  (congrArg
        (fun m : (asStructureSheafModule B S hS X (idealPowModule I n G)).over A ⟶
            (asStructureSheafModule B S hS X F).over A => m.val)
        (chartAlpha_idealPowSmulMap_comp B S hS X I hIc G F hZt hNo hIq hFq hG A h φ)).trans
    (overFunctor_map_comp_val B S hS X
      (asStructureSheafModule B S hS X (idealPowModule I n G))
      (asStructureSheafModule B S hS X (idealPowModule I k G))
      (asStructureSheafModule B S hS X F) (idealPowModuleHomOfLE I G h) A
      (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ))

/-- **Relocalizing the chart transport at a raised exponent to the kernel pair is precomposing the
relocalization at the original exponent with the restriction of the inclusion `ℐⁿ𝒢 ⟶ ℐᵏ𝒢`.**

The relocalization is given as the underlying morphism of a morphism `β` of sheaves of modules on
the slice at the kernel pair, with the equation as a hypothesis — consumed at the level of
morphisms, where no component is projected. -/
theorem homRestr_chartAlphaSheaf_idealPowSmulMap_comp_val (k n : ℕ) (h : k ≤ n)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (p : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
    (β : (asStructureSheafModule B S hS X (idealPowModule I k G)).over
        (A ⨯ A : SmallEtale B S hS X.1) ⟶
      (asStructureSheafModule B S hS X F).over (A ⨯ A : SmallEtale B S hS X.1))
    (hβ : β.val =
      homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I k G).val F.val p
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val) :
    homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I n G).val F.val p
        (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A n
          (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
            (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) h ≫ φ)).val =
      ((SheafOfModules.overFunctor (structureRingSheaf B S hS X)
          (A ⨯ A : SmallEtale B S hS X.1)).map (idealPowModuleHomOfLE I G h) ≫ β).val :=
  (congrArg
        (fun z : (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) A).obj
              (idealPowModule I n G).val ⟶
            (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2) A).obj F.val =>
          homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I n G).val F.val
            p z)
        (chartAlphaSheaf_idealPowSmulMap_comp_val B S hS X I hIc G F hZt hNo hIq hFq hG A k n h
          φ)).trans
    ((Stacks.PresheafOfModules.homRestr_restrFun_map_comp
          (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I n G).val
          (idealPowModule I k G).val F.val (idealPowModuleHomOfLE I G h).val p
          (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ).val).trans
      ((congrArg
          (fun z : (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2)
                (A ⨯ A : SmallEtale B S hS X.1)).obj (idealPowModule I k G).val ⟶
              (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2)
                (A ⨯ A : SmallEtale B S hS X.1)).obj F.val =>
            (restrFun (smallEtaleStructurePresheaf B S hS X.1 X.2)
                (A ⨯ A : SmallEtale B S hS X.1)).map (idealPowModuleHomOfLE I G h).val ≫ z)
          hβ).symm.trans
        (overFunctor_map_comp_val B S hS X
          (asStructureSheafModule B S hS X (idealPowModule I n G))
          (asStructureSheafModule B S hS X (idealPowModule I k G))
          (asStructureSheafModule B S hS X F) (idealPowModuleHomOfLE I G h)
          (A ⨯ A : SmallEtale B S hS X.1) β).symm))

/-! ### The exponent rise -/

variable (θ : (restrictToIdealComplement B S hS X I).obj G ⟶
    (restrictToIdealComplement B S hS X I).obj F)

/-- **The exponent rise.**  On a chart whose kernel pair has Noetherian scheme, a morphism on the
chart's scheme restricting to the transport of `θ` can be replaced by one at a possibly larger
exponent, still restricting to the transport of `θ`, whose chart transport has **equal**
relocalizations along the two projections of the kernel pair.

The two relocalizations are the chart transports of two morphisms `ψ₁`, `ψ₂` on the scheme of the
kernel pair (`AlgebraicGeometry.Space.bijective_chartAlpha`), and
`AlgebraicGeometry.Space.homRestrict_eq_of_chartAlphaSheaf_val_eq_homRestr_prod` says that those
two restrict equally to the complement of the support.  The injectivity clause of the first
display of [Stacks, Tag 01YB] on the scheme of the kernel pair therefore identifies them in the
colimit, and a filtered colimit of concrete objects identifies two representatives agreeing in it
after finitely many transition maps.  Raising the exponent by that many steps makes them equal,
and `AlgebraicGeometry.Space.chartAlpha_idealPowSmulMap_comp` reads the resulting equality back as
the equality of the two relocalizations.

This is the compatibility condition of
`AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod`. -/
theorem exists_homRestr_prod_eq
    (hNoP : _root_.AlgebraicGeometry.IsNoetherian
      (chartScheme (A ⨯ A : SmallEtale B S hS X.1)))
    (k : ℕ)
    (φ : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) k (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A)
    (hφ : Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
        (idealSheafDataOfChart B S hS X I hIc A)
        (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
          (idealSheafDataOfChart B S hS X I hIc A)) φ =
      chartThetaOver B S hS X I hIc G F θ A) :
    ∃ (n : ℕ) (φ' : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmul
        (idealSheafDataOfChart B S hS X I hIc A) n (chartPush B S hS X G A) ⟶
      chartPush B S hS X F A),
      Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict
            (idealSheafDataOfChart B S hS X I hIc A)
            (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
              (idealSheafDataOfChart B S hS X I hIc A)) φ' =
          chartThetaOver B S hS X I hIc G F θ A ∧
        homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I n G).val F.val
            (Limits.prod.fst : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
            (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A n φ').val =
          homRestr (smallEtaleStructurePresheaf B S hS X.1 X.2) (idealPowModule I n G).val F.val
            (Limits.prod.snd : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
            (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A n φ').val := by
  obtain ⟨β₁, hβ₁⟩ := exists_val_eq_homRestr B S hS X
    (asStructureSheafModule B S hS X (idealPowModule I k G))
    (asStructureSheafModule B S hS X F)
    (Limits.prod.fst : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
    (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ)
  obtain ⟨β₂, hβ₂⟩ := exists_val_eq_homRestr B S hS X
    (asStructureSheafModule B S hS X (idealPowModule I k G))
    (asStructureSheafModule B S hS X F)
    (Limits.prod.snd : (A ⨯ A : SmallEtale B S hS X.1) ⟶ A)
    (chartAlphaSheaf B S hS X I hIc G F hZt hNo hIq hFq hG A k φ)
  obtain ⟨ψ₁, hψ₁⟩ :=
    (bijective_chartAlpha B S hS X I hIc G F hZt hNo hIq hFq hG (A ⨯ A) k).2 β₁
  obtain ⟨ψ₂, hψ₂⟩ :=
    (bijective_chartAlpha B S hS X I hIc G F hZt hNo hIq hFq hG (A ⨯ A) k).2 β₂
  have hA := homRestrict_eq_of_chartAlphaSheaf_val_eq_homRestr_prod B S hS X I hIc G F θ hZt
    hNo hIq hFq hG A k φ hφ ψ₁ ψ₂
    (by rw [← hβ₁, ← hψ₁]) (by rw [← hβ₂, ← hψ₂])
  have _hno : _root_.AlgebraicGeometry.IsNoetherian
      (chartScheme (A ⨯ A : SmallEtale B S hS X.1)) := hNoP
  have _hcoh := isCoherent_chartPush B S hS X G hG (A ⨯ A) hNoP.toIsLocallyNoetherian
  have _hqc := isQuasicoherent_chartPush B S hS X F hFq (A ⨯ A)
  have _hforget : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  have hι : Limits.colimit.ι (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulHomSystem
          (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) (chartPush B S hS X G (A ⨯ A))
          (chartPush B S hS X F (A ⨯ A))) k ψ₁ =
      Limits.colimit.ι (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulHomSystem
        (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) (chartPush B S hS X G (A ⨯ A))
        (chartPush B S hS X F (A ⨯ A))) k ψ₂ :=
    Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToHomRestrict_injective
      (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) (chartPush B S hS X G (A ⨯ A))
      (chartPush B S hS X F (A ⨯ A))
      ((Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToHomRestrict_ι
            (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) (chartPush B S hS X G (A ⨯ A))
            (chartPush B S hS X F (A ⨯ A)) k ψ₁).trans
        (hA.trans (Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToHomRestrict_ι
          (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) (chartPush B S hS X G (A ⨯ A))
          (chartPush B S hS X F (A ⨯ A)) k ψ₂).symm))
  obtain ⟨n, f, g, hfg⟩ := Limits.Concrete.colimit_exists_of_rep_eq
    (Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulHomSystem
      (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) (chartPush B S hS X G (A ⨯ A))
      (chartPush B S hS X F (A ⨯ A))) ψ₁ ψ₂ hι
  obtain rfl : f = g := Subsingleton.elim f g
  have hstep : Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
          (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) (chartPush B S hS X G (A ⨯ A))
          (leOfHom f) ≫ ψ₁ =
      Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
        (idealSheafDataOfChart B S hS X I hIc (A ⨯ A)) (chartPush B S hS X G (A ⨯ A))
        (leOfHom f) ≫ ψ₂ := hfg
  have hsheaf : (SheafOfModules.overFunctor (structureRingSheaf B S hS X)
          (A ⨯ A : SmallEtale B S hS X.1)).map (idealPowModuleHomOfLE I G (leOfHom f)) ≫ β₁ =
      (SheafOfModules.overFunctor (structureRingSheaf B S hS X)
        (A ⨯ A : SmallEtale B S hS X.1)).map (idealPowModuleHomOfLE I G (leOfHom f)) ≫ β₂ := by
    rw [← hψ₁, ← hψ₂]
    exact (chartAlpha_idealPowSmulMap_comp B S hS X I hIc G F hZt hNo hIq hFq hG (A ⨯ A)
      (leOfHom f) ψ₁).symm.trans ((congrArg (chartAlpha B S hS X I hIc G F hZt hNo hIq hFq hG
      (A ⨯ A) n) hstep).trans (chartAlpha_idealPowSmulMap_comp B S hS X I hIc G F hZt hNo hIq hFq
      hG (A ⨯ A) (leOfHom f) ψ₂))
  refine ⟨n, Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulMap
    (idealSheafDataOfChart B S hS X I hIc A) (chartPush B S hS X G A) (leOfHom f) ≫ φ,
    (Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict_idealPowSmulMap
      (idealSheafDataOfChart B S hS X I hIc A)
      (Stacks.AlgebraicGeometry.IdealPowerColimit.disjoint_supportCompl_support
        (idealSheafDataOfChart B S hS X I hIc A)) (leOfHom f) φ).trans hφ, ?_⟩
  refine Eq.trans (homRestr_chartAlphaSheaf_idealPowSmulMap_comp_val B S hS X I hIc G F hZt hNo
    hIq hFq hG A k n (leOfHom f) φ Limits.prod.fst β₁ hβ₁) ?_
  refine Eq.trans ?_ (homRestr_chartAlphaSheaf_idealPowSmulMap_comp_val B S hS X I hIc G F hZt
    hNo hIq hFq hG A k n (leOfHom f) φ Limits.prod.snd β₂ hβ₂).symm
  exact congrArg SheafOfModules.Hom.val hsheaf

end AlgebraicGeometry.Space

end
