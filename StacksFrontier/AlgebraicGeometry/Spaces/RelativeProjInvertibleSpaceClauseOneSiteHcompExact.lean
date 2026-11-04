module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneTargetOverSite

/-!
# The slot `hcomp` of the target square of clause (1) of Stacks 0D2Z, spelled as the hypothesis

The target square of clause (1) of [Stacks, Tag 0D2Z] over the site of `s`
(`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`) takes as its
hypothesis `hcomp` the composition law of the identifications `ρ` of Stacks 03DX (2) along the
section `c_w` of the fibre `q : W ×_Y P ⟶ W`, with `r = c_w ≫ q = 𝟙`.  At variables this is
`AlgebraicGeometry.Space.compIso_hom_app_comp_pullbackTransport_comp_idIso_app_hom_eq_canHom`,
but its instance at the chart data spells the same factors differently from the hypothesis: the
transport along `c ≫ q = 𝟙` is `pullbackTransport` rather than `eqToHom (congrArg …)`, the
structure morphism of the fibre is `(toScheme).map (fibreHom W v)` rather than
`…RelativeProjSituation.fibreToBase`, the point `R` is `⟨yoneda.obj W, _⟩` rather than
`yonedaSpace W`, and the sheafification instances differ.  Each is a definitional unfolding, but
checking the whole equation across the two spellings at once exhausts the heartbeat budget.

This file states the slot at variables in the spelling of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`: an arbitrary family `Φ` of inverse
images with comparisons `κ`, heterogeneously equal to `modulePullback` and
`modulePullbackCompIso`, with leaves `R`, `Fs`, `c`, `q`, `r`, `Zr`, `Zq`, `Qc`, `Zcq`, `ρq`,
`ρc`, `ρr`, `Fq` heterogeneously equal to the factors of the composition law at a section
`c₀ ≫ q₀ = 𝟙` of the site, and the structure morphism `g` of the scheme-level identification any
morphism equal to `(toScheme).map q₀`
(`AlgebraicGeometry.Space.compIso_hom_app_comp_eqToHom_comp_hom_eq_canHom_of_heq`).  It is proved
by `subst`, the identity `pullbackTransport = eqToHom` at variables and the composition law at
variables, so no factor is converted between two spellings.  At the chart data the leaves are
passed exactly as the target square passes them and `g` is `fibreToBase`, related to
`(toScheme).map fibreHom` by its equation lemma, so the statement is the hypothesis `hcomp`
itself, and only the leaf identities are checked, each on its own.

## Main results

* `AlgebraicGeometry.Space.compIso_hom_app_comp_eqToHom_comp_hom_eq_canHom_of_heq`: the
  hypothesis `hcomp` of the target square at `r = 𝟙`, for a family heterogeneously equal to
  `modulePullback`.
* `…InvertibleTwistingRestriction.targetSquare_hcomp_exact`: **the hypothesis `hcomp` of
  `…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`, in its own
  spelling.**

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

namespace AlgebraicGeometry.Space

section HcompHEq

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (Φ : ∀ {X Y : AlgebraicSpaces B S hS}, (X ⟶ Y) →
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2)
  (κ : ∀ {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z), Φ g ⋙ Φ f ≅ Φ (f ≫ g))

/-- **The hypothesis `hcomp` of the target square at `r = 𝟙`, for a family heterogeneously equal
to `modulePullback`**: for `Φ = modulePullback` and `κ = modulePullbackCompIso` (as heterogeneous
equalities), a section `c₀ ≫ q₀ = 𝟙` of the site, `c`, `q`, `r` the represented maps of `c₀`, `q₀`
and `𝟙`, `ρq`, `ρc` the identifications `g^*(M^a) ≅ (g^*M)^a` of Stacks 03DX (2) along `q₀` and
`c₀`, `ρr` the unit law `(𝟙)^* ≅ 𝟭` of Stacks 03LU, and `Fq` the module attached to the canonical
identification `c₀^*q₀^*Z ≅ (𝟙)^*Z ≅ Z` formed with any `g = (toScheme).map q₀`, the composition
law `(κ c q).hom ≫ τZ ≫ ρr = (Φ c).map ρq ≫ ρc ≫ Fq` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` holds, with `τZ` the transport along
`c ≫ q = r` written as `eqToHom`; it is
`AlgebraicGeometry.Space.compIso_hom_app_comp_pullbackTransport_comp_idIso_app_hom_eq_canHom`.
The binders `R`, …, `τZ` are those of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`, in its order, so that an instance
names its leaves as the target square does; `c`, `q` and `hcq : c ≫ q = r` fix `r` as the target
square does. -/
theorem compIso_hom_app_comp_eqToHom_comp_hom_eq_canHom_of_heq
    (hΦ : HEq (@Φ) (@modulePullback B S hS)) (hκ : HEq (@κ) (@modulePullbackCompIso B S hS))
    {R Fs : AlgebraicSpaces B S hS} {c : R ⟶ Fs} {q : Fs ⟶ R}
    {r : R ⟶ R} (hcq : c ≫ q = r)
    {Zr Qc Zcq : Modules.{u, u} B S hS R.1 R.2} {Zq : Modules.{u, u} B S hS Fs.1 Fs.2}
    {ρq : (Φ q).obj Zr ≅ Zq} {ρc : (Φ c).obj Zq ≅ Qc} {ρr : (Φ r).obj Zr ≅ Zcq}
    {Fq : Qc ⟶ Zcq}
    {τZ : (Φ (c ≫ q)).obj Zr ⟶ (Φ r).obj Zr}
    (hτZ : τZ = eqToHom (congrArg (fun k => (Φ k).obj Zr) hcq))
    {W F : BigFppfOver B S hS} (c₀ : W ⟶ F) (q₀ : F ⟶ W) (hcq₀ : c₀ ≫ q₀ = 𝟙 W)
    (hcq₀' : (BigFppfOver.toScheme B S hS).map c₀ ≫ (BigFppfOver.toScheme B S hS).map q₀ =
      𝟙 ((BigFppfOver.toScheme B S hS).obj W))
    (Z₀ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory)
    (hR : R = (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS))
    (hFs : Fs = (⟨yoneda.obj F, isAlgebraicSpace_yoneda B S hS F⟩ : AlgebraicSpaces B S hS))
    (hc : HEq c (representedSpaceMap B S hS c₀)) (hq : HEq q (representedSpaceMap B S hS q₀))
    (hr : HEq r (𝟙 (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS)))
    (hZr : HEq Zr ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj Z₀).obj)
    (hZq : HEq Zq ((representedQuasicoherentSchemeEquivalence B S hS F).functor.obj
      (quasicoherentPullbackObj B S hS q₀ Z₀)).obj)
    (hQc : HEq Qc ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj
      (quasicoherentPullbackObj B S hS c₀ (quasicoherentPullbackObj B S hS q₀ Z₀))).obj)
    (hZcq : Zcq = Zr)
    (hρq : HEq ρq (modulePullbackRepresentedQuasicoherentIso B S hS q₀ Z₀))
    (hρc : HEq ρc (modulePullbackRepresentedQuasicoherentIso B S hS c₀
      (quasicoherentPullbackObj B S hS q₀ Z₀)))
    (hρr : HEq ρr ((modulePullbackIdIso B S hS
      (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS)).app
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj Z₀).obj))
    (hFq : HEq Fq ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
      (ObjectProperty.homMk (Stacks.AlgebraicGeometry.ModuleLimits.canHom
          ((BigFppfOver.toScheme B S hS).map c₀) ((BigFppfOver.toScheme B S hS).map q₀) (𝟙 _)
          hcq₀' Z₀.obj ≫
        (Scheme.Modules.pullbackId _).hom.app Z₀.obj) :
        quasicoherentPullbackObj B S hS c₀ (quasicoherentPullbackObj B S hS q₀ Z₀) ⟶ Z₀)).hom) :
    (κ c q).hom.app Zr ≫ τZ ≫ ρr.hom = (Φ c).map ρq.hom ≫ ρc.hom ≫ Fq := by
  obtain rfl : @Φ = @modulePullback B S hS := eq_of_heq hΦ
  obtain rfl : @κ = @modulePullbackCompIso B S hS := eq_of_heq hκ
  subst hτZ hZcq hR hFs
  have ec := eq_of_heq hc
  subst ec
  have eq := eq_of_heq hq
  subst eq
  have er := eq_of_heq hr
  subst er
  have eZr := eq_of_heq hZr
  subst eZr
  have eZq := eq_of_heq hZq
  subst eZq
  have eQc := eq_of_heq hQc
  subst eQc
  have eρq := eq_of_heq hρq
  subst eρq
  have eρc := eq_of_heq hρc
  subst eρc
  have eρr := eq_of_heq hρr
  subst eρr
  have eFq := eq_of_heq hFq
  subst eFq
  refine Eq.trans ?_
    (compIso_hom_app_comp_pullbackTransport_comp_idIso_app_hom_eq_canHom c₀ q₀ hcq₀ hcq₀' hcq Z₀)
  exact congrArg (fun t => _ ≫ t ≫ _) (pullbackTransport_eq_eqToHom _ hcq).symm

end HcompHEq

end AlgebraicGeometry.Space

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  {W : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)

/-- **The hypothesis `hcomp` of the target square of clause (1) at a scheme point `w` of `U(ψ)`,
over the site of `s`, in the spelling of
`…InvertibleTwistingRestriction.clauseOneTarget_square_overSite_of_slots`**, at
`r = c_w ≫ q = 𝟙`: the comparison `c_w^*q^* ≅ (c_w ≫ q)^*` of Stacks 03LU at the module attached
to the piece of the point algebra, the transport along `c_w ≫ q = 𝟙` and the unit law
`(𝟙)^* ≅ 𝟭` are the inverse image along `c_w` of the identification of Stacks 03DX (2) along `q`,
the identification along `c_w`, and the module attached to the canonical identification
`c_w^*q^*Z ≅ Z` formed with the structure morphism `…RelativeProjSituation.fibreToBase` of the
fibre.  This is
`AlgebraicGeometry.Space.compIso_hom_app_comp_pullbackTransport_comp_idIso_app_hom_eq_canHom`
restated through `AlgebraicGeometry.Space.compIso_hom_app_comp_eqToHom_comp_hom_eq_canHom_of_heq`,
with the leaves passed exactly as the target square passes them, so that its type is the
hypothesis `hcomp`. -/
theorem targetSquare_hcomp_exact :
    type_of% (compIso_hom_app_comp_eqToHom_comp_hom_eq_canHom_of_heq
      (@modulePullback s.site s.base s.containsBase)
      (@modulePullbackCompIso s.site s.base s.containsBase) HEq.rfl HEq.rfl
      (R := yonedaSpace s.site s.base s.containsBase W)
      (c := representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
      (q := representedSpaceMap s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom)))
      (hcq := representedSpaceMap_chartSection_comp_fibreHom_overSite w)
      (Zr := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (ρq := modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))
      (ρc := modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))))
      (ρr := (modulePullbackIdIso s.site s.base s.containsBase
        (⟨yoneda.obj W, isAlgebraicSpace_yoneda s.site s.base s.containsBase W⟩ :
          AlgebraicSpaces s.site s.base s.containsBase)).app
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (Fq := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          W).functor.map
        (ObjectProperty.homMk (Stacks.AlgebraicGeometry.ModuleLimits.canHom
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
            (s.fibreToBase W (locusPoint w ≫ f.hom))
            (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W))
            (toScheme_map_chartSection_comp_fibreToBase s f L ψ (locusPoint w)
              (locusOpen_locusPoint w))
            (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)).obj ≫
          (Scheme.Modules.pullbackId _).hom.app
            (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)).obj) :
        quasicoherentPullbackObj s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
              (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))) ⟶
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).hom)
      (hτZ := rfl)
      (c₀ := (ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
      (q₀ := s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
      (hcq₀ := (ofUnitalHom s f L ψ).chartSection_fibreHom (locusPoint w) (locusOpen_locusPoint w))
      (hcq₀' := toScheme_map_chartSection_comp_fibreToBase s f L ψ (locusPoint w)
        (locusOpen_locusPoint w))
      (Z₀ := s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))
      (hR := rfl) (hFs := rfl) (hc := HEq.rfl) (hq := HEq.rfl) (hr := HEq.rfl) (hZr := HEq.rfl)
      (hZq := HEq.rfl) (hQc := HEq.rfl) (hZcq := rfl) (hρq := HEq.rfl) (hρc := HEq.rfl)
      (hρr := HEq.rfl) (hFq := HEq.rfl)) :=
  compIso_hom_app_comp_eqToHom_comp_hom_eq_canHom_of_heq
      (@modulePullback s.site s.base s.containsBase)
      (@modulePullbackCompIso s.site s.base s.containsBase) HEq.rfl HEq.rfl
      (R := yonedaSpace s.site s.base s.containsBase W)
      (c := representedSpaceMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
      (q := representedSpaceMap s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom)))
      (hcq := representedSpaceMap_chartSection_comp_fibreHom_overSite w)
      (Zr := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (ρq := modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))
      (ρc := modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (quasicoherentPullbackObj s.site s.base s.containsBase
          (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))))
      (ρr := (modulePullbackIdIso s.site s.base s.containsBase
        (⟨yoneda.obj W, isAlgebraicSpace_yoneda s.site s.base s.containsBase W⟩ :
          AlgebraicSpaces s.site s.base s.containsBase)).app
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase W).functor.obj
          (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).obj)
      (Fq := ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          W).functor.map
        (ObjectProperty.homMk (Stacks.AlgebraicGeometry.ModuleLimits.canHom
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map
              ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
            (s.fibreToBase W (locusPoint w ≫ f.hom))
            (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W))
            (toScheme_map_chartSection_comp_fibreToBase s f L ψ (locusPoint w)
              (locusOpen_locusPoint w))
            (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)).obj ≫
          (Scheme.Modules.pullbackId _).hom.app
            (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)).obj) :
        quasicoherentPullbackObj s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
              (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))) ⟶
          s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))).hom)
      (hτZ := rfl)
      (c₀ := (ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
      (q₀ := s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
      (hcq₀ := (ofUnitalHom s f L ψ).chartSection_fibreHom (locusPoint w) (locusOpen_locusPoint w))
      (hcq₀' := toScheme_map_chartSection_comp_fibreToBase s f L ψ (locusPoint w)
        (locusOpen_locusPoint w))
      (Z₀ := s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ))
      (hR := rfl) (hFs := rfl) (hc := HEq.rfl) (hq := HEq.rfl) (hr := HEq.rfl) (hZr := HEq.rfl)
      (hZq := HEq.rfl) (hQc := HEq.rfl) (hZcq := rfl) (hρq := HEq.rfl) (hρc := HEq.rfl)
      (hρr := HEq.rfl) (hFq := HEq.rfl)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
