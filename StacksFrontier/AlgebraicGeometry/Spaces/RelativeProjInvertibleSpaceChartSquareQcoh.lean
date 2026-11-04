module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMapNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartMiddleSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceSchemeHomBridge

/-!
# The square of `θ` on the schemes of the chart maps of Stacks 0D2Z, as quasi-coherent modules

`…InvertibleTwistingRestriction.chartTheta_square` states the square of `θ` of [Stacks, Tag 01O9]
on the schemes of the site along `τ : T' ⟶ T`, for any restriction datum, in the vocabulary of
`Scheme.Modules.pullbackComp` / `Scheme.Modules.pullbackCongr`.  The chart maps of Stacks 0D2Z
(`…InvertibleTwistingRestriction.pointFamilyNatural_chartMap_of_square`) ask for the same square in
the vocabulary of quasi-coherent modules of the site (`quasicoherentPullbackMap`,
`quasicoherentPullbackCompIso`, `quasicoherentPullbackEqToHom`), with `θ` packaged as
`…InvertibleTwistingRestriction.chartSchemeTheta` and the target comparison as
`AlgebraicGeometry.Space.pointLaurentPiecePullbackHom`.

## Main results

* `…InvertibleTwistingRestriction.chartSchemeTheta_square`: **the square in the quasi-coherent
  vocabulary**, in the binder shape of the hypothesis `hm` of
  `…InvertibleTwistingRestriction.pointFamilyNatural_chartMap_of_square`.

## Implementation notes

The two statements are the same up to definitional unfolding, but they spell the graded algebra
of the twists (`s.shrink.pointAlgebra` / `Tag07ZGTwist.twistAlgebra` against
`s.relativeProjPoints.algebra` / `GradedPowerMap.twD`), the chart morphism (`chartMorphism` against
`chartLift ≫ globalMorphism`), the targets (`pointLaurentPieceQcoh` against `tensorPowerModule`)
and the composite `x ≫ f` (in the presheaves on `s.shrink.site` against `s.site`) differently, and
comparing the two composites at once exceeds the per-declaration budget.  The comparison is done at
the leaves instead: generic lemmas with the factors of each side as variables, equal or
heterogeneously equal leaf by leaf, proved by `subst` (`…pullback_map_comp_eq_comp_of_heq`,
`…pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_heq`,
`…twistPieceComparison_hom_hom_heq_of_eq`), each leaf then closed by `rfl` or `HEq.rfl`.  The site
of the test objects is fixed as `s.site` in `…chartSchemeTheta_square_of_eq` and passed explicitly
(`(s := s)`) at its one use: left implicit, it is unified as `s.shrink` from the type of `τ`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A square `τ^*Θ₀ ≫ ρ = σ ≫ Θ₁` of quasi-coherent modules on the schemes of the site, with the
comparison `σ` of the sources given by its value `hσ`, from the square of the underlying
morphisms of modules, every morphism of schemes spelled `(BigFppfOver.toScheme …).map _`. -/
theorem quasicoherentPullbackMap_comp_eq_comp_of_hom_eq {W V V' U : BigFppfOver B S hS}
    (τ : W ⟶ V) (c : V ⟶ U) (c' : W ⟶ V') (y : V' ⟶ U) (e : τ ≫ c = c' ≫ y)
    (N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    {N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V').ringCatSheaf).FullSubcategory}
    (t : quasicoherentPullbackObj B S hS y N ⟶ N')
    {Q₀ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    {Q₁ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (Θ₀ : quasicoherentPullbackObj B S hS c N ⟶ Q₀)
    (ρ : quasicoherentPullbackObj B S hS τ Q₀ ⟶ Q₁)
    (Θ₁ : quasicoherentPullbackObj B S hS c' N' ⟶ Q₁)
    (σ : quasicoherentPullbackObj B S hS τ (quasicoherentPullbackObj B S hS c N) ⟶
      quasicoherentPullbackObj B S hS c' N')
    (hσ : σ = (quasicoherentPullbackCompIso B S hS τ c N).hom ≫
      quasicoherentPullbackEqToHom B S hS e N ≫
        (quasicoherentPullbackCompIso B S hS c' y N).inv ≫
          quasicoherentPullbackMap B S hS c' t)
    (H : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ)).map Θ₀.hom ≫ ρ.hom =
      ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map c)).hom.app N.obj ≫
        eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj N.obj)
          (toScheme_map_comp_eq_of_comp_eq e)) ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map c')
          ((BigFppfOver.toScheme B S hS).map y)).inv.app N.obj ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map c')).map t.hom) ≫
        Θ₁.hom) :
    quasicoherentPullbackMap B S hS τ Θ₀ ≫ ρ = σ ≫ Θ₁ := by
  refine ObjectProperty.hom_ext _ ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    hom_eq_of_eq_quasicoherentPullbackCompIso τ c c' y e N t σ hσ]
  exact H

/-- The underlying morphism of a morphism of a full subcategory built from a morphism `φ` of the
ambient category is `φ`. -/
theorem fullSubcategory_homMk_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {A B : P.FullSubcategory} (φ : A.obj ⟶ B.obj) : (ObjectProperty.homMk φ).hom = φ :=
  rfl

/-- **The contraction, the transport and a map out of the pullback along the composite, read in
two spellings**: `c^*(t^*M) ≅ (c ≫ t)^*M = g^*M ⟶ N` is heterogeneously equal to the same
composite for heterogeneously equal leaves `t`, `g`, `M`, `θ` over equal schemes `P₁ = P₂`. -/
theorem pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_heq {A F P₁ P₂ : Scheme.{u}}
    (c : A ⟶ F) {t₁ : F ⟶ P₁} {t₂ : F ⟶ P₂} {g₁ : A ⟶ P₁} {g₂ : A ⟶ P₂} (h₁ : c ≫ t₁ = g₁)
    (h₂ : c ≫ t₂ = g₂) {M₁ : P₁.Modules} {M₂ : P₂.Modules} {N₁ N₂ : A.Modules}
    (θ₁ : (Scheme.Modules.pullback g₁).obj M₁ ⟶ N₁) (θ₂ : (Scheme.Modules.pullback g₂).obj M₂ ⟶ N₂)
    (hP : P₁ = P₂) (ht : HEq t₁ t₂) (hg : HEq g₁ g₂) (hM : HEq M₁ M₂) (hN : N₁ = N₂)
    (hθ : HEq θ₁ θ₂) :
    HEq ((Scheme.Modules.pullbackComp c t₁).hom.app M₁ ≫
        (Scheme.Modules.pullbackCongr h₁).hom.app M₁ ≫ θ₁)
      ((Scheme.Modules.pullbackComp c t₂).hom.app M₂ ≫
        (Scheme.Modules.pullbackCongr h₂).hom.app M₂ ≫ θ₂) := by
  subst hP hN
  cases ht
  cases hg
  cases hM
  cases hθ
  rfl

/-- **The comparison of the pullbacks of a module along a square, read in two spellings**:
`y^*(ι^*G) ≅ (y ≫ ι)^*G = (ι' ≫ p)^*G ≅ ι'^*(p^*G) ⟶ ι'^*K` is heterogeneously equal to the same
composite for heterogeneously equal leaves over equal schemes. -/
theorem pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_inv_app_comp_map_heq
    {F' F P₁ P₂ P₁' P₂' : Scheme.{u}} (y : F' ⟶ F) {ι₁ : F ⟶ P₁} {ι₂ : F ⟶ P₂}
    {ι₁' : F' ⟶ P₁'} {ι₂' : F' ⟶ P₂'} {p₁ : P₁' ⟶ P₁} {p₂ : P₂' ⟶ P₂}
    (h₁ : y ≫ ι₁ = ι₁' ≫ p₁) (h₂ : y ≫ ι₂ = ι₂' ≫ p₂) {G₁ : P₁.Modules} {G₂ : P₂.Modules}
    {K₁ : P₁'.Modules} {K₂ : P₂'.Modules}
    (e₁ : (Scheme.Modules.pullback p₁).obj G₁ ⟶ K₁) (e₂ : (Scheme.Modules.pullback p₂).obj G₂ ⟶ K₂)
    (hP : P₁ = P₂) (hP' : P₁' = P₂') (hι : HEq ι₁ ι₂) (hι' : HEq ι₁' ι₂') (hp : HEq p₁ p₂)
    (hG : HEq G₁ G₂) (hK : HEq K₁ K₂) (he : HEq e₁ e₂) :
    HEq ((Scheme.Modules.pullbackComp y ι₁).hom.app G₁ ≫
        (Scheme.Modules.pullbackCongr h₁).hom.app G₁ ≫
        (Scheme.Modules.pullbackComp ι₁' p₁).inv.app G₁ ≫ (Scheme.Modules.pullback ι₁').map e₁)
      ((Scheme.Modules.pullbackComp y ι₂).hom.app G₂ ≫
        (Scheme.Modules.pullbackCongr h₂).hom.app G₂ ≫
        (Scheme.Modules.pullbackComp ι₂' p₂).inv.app G₂ ≫
          (Scheme.Modules.pullback ι₂').map e₂) := by
  subst hP hP'
  cases hι
  cases hι'
  cases hp
  cases hG
  cases hK
  cases he
  rfl

/-- **The square `τ^*Θ ≫ ρ = σ ≫ Θ'` of modules on schemes, read in two spellings**: from the
square for one spelling of its factors, the square for heterogeneously equal factors over equal
modules. -/
theorem pullback_map_comp_eq_comp_of_heq {A A' F F' : Scheme.{u}} (τ : A' ⟶ A) (c : A ⟶ F)
    (c' : A' ⟶ F') (y : F' ⟶ F) (e : τ ≫ c = c' ≫ y) {Na Nb : F.Modules} {Ka Kb : F'.Modules}
    {Qa Qb : A.Modules} {Qa' Qb' : A'.Modules}
    {Θa : (Scheme.Modules.pullback c).obj Na ⟶ Qa} {Θb : (Scheme.Modules.pullback c).obj Nb ⟶ Qb}
    {ρa : (Scheme.Modules.pullback τ).obj Qa ⟶ Qa'}
    {ρb : (Scheme.Modules.pullback τ).obj Qb ⟶ Qb'}
    {ta : (Scheme.Modules.pullback y).obj Na ⟶ Ka} {tb : (Scheme.Modules.pullback y).obj Nb ⟶ Kb}
    {Θa' : (Scheme.Modules.pullback c').obj Ka ⟶ Qa'}
    {Θb' : (Scheme.Modules.pullback c').obj Kb ⟶ Qb'}
    (H : (Scheme.Modules.pullback τ).map Θb ≫ ρb =
      ((Scheme.Modules.pullbackComp τ c).hom.app Nb ≫
        eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj Nb) e) ≫
        (Scheme.Modules.pullbackComp c' y).inv.app Nb ≫ (Scheme.Modules.pullback c').map tb) ≫ Θb')
    (hN : Na = Nb) (hK : Ka = Kb) (hQ : Qa = Qb) (hQ' : Qa' = Qb') (hΘ : HEq Θa Θb)
    (hρ : HEq ρa ρb) (ht : HEq ta tb) (hΘ' : HEq Θa' Θb') :
    (Scheme.Modules.pullback τ).map Θa ≫ ρa =
      ((Scheme.Modules.pullbackComp τ c).hom.app Na ≫
        eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj Na) e) ≫
        (Scheme.Modules.pullbackComp c' y).inv.app Na ≫ (Scheme.Modules.pullback c').map ta) ≫
        Θa' := by
  subst hN hK hQ hQ'
  cases hΘ
  cases hρ
  cases ht
  cases hΘ'
  exact H

/-- A morphism of a full subcategory followed by the identification of its target with itself
has the same underlying morphism. -/
theorem fullSubcategory_comp_eqToHom_refl_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {A B : P.FullSubcategory} (φ : A ⟶ B) (h : B = B) : (φ ≫ eqToHom h).hom = φ.hom := by
  rw [eqToHom_refl, Category.comp_id]

end AlgebraicGeometry.Space

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

/-- The comparison `τ^*((x^*ℒ)^{⊗ d}) ≅ ((x ∘ τ)^*ℒ)^{⊗ d}` of quasi-coherent modules, followed by
the identity transport, is on the underlying modules the comparison `ρ` of the targets of
`…InvertibleTwistingRestriction.chartTheta_square` at the datum `…ofUnitalHom s f L ψ`. -/
theorem pointLaurentPiecePullbackHom_comp_eqToHom_hom (d : ℤ)
    {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1) :
    (pointLaurentPiecePullbackHom L τ x d ≫
        eqToHom (congrArg (fun k => pointLaurentPieceQcoh L T' k d)
          (rfl : yoneda.map τ ≫ x = yoneda.map τ ≫ x))).hom =
      (Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ)
          ((ofUnitalHom s f L ψ).line T x) d).hom ≫
        (LaurentCongr.congrIso ((ofUnitalHom s f L ψ).lineIso τ x) d).hom :=
  (fullSubcategory_comp_eqToHom_refl_hom _ _).trans
    (pointLaurentPiecePullbackHom_hom_eq s f L ψ τ x d)

/-- **`…InvertibleTwistingRestriction.chartSchemeTheta` on the underlying modules, in the
spelling of `…InvertibleTwistingRestriction.chartTheta_square`**: the contraction
`c_x^*(t^*𝒪(d)) ≅ (c_x ≫ t)^*𝒪(d)`, the transport along `c_x ≫ t = r_x` and `θ`, with the graded
algebra of the twist and the relative homogeneous spectrum read through
`s.relativeProjPoints.algebra` and `r_x` as the chart lift followed by the global morphism. -/
theorem chartSchemeTheta_hom_heq (d : ℤ) {T : BigFppfOver s.site s.base s.containsBase}
    (x : yoneda.obj T ⟶ X.1) (hx : (ofUnitalHom s f L ψ).locusOpen T x = ⊤) :
    HEq (chartSchemeTheta s f L ψ x hx d).hom
      ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          ((ofUnitalHom s f L ψ).chartSection x hx)) (s.toRelativeProj T (x ≫ f.hom) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre T (x ≫
            f.hom)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f.hom))).scheme)).hom.app
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f.hom))).algebra.piece d) ≫
              (Scheme.Modules.pullbackCongr ((ofUnitalHom s f L
              ψ).toScheme_map_chartSection_comp_toRelativeProj x hx :
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map ((ofUnitalHom s f L ψ).chartSection
            x hx)) ≫ (s.toRelativeProj T (x ≫ f.hom) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre T (x ≫
            f.hom)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f.hom))).scheme) = ((ofUnitalHom s f L
              ψ).chartLift x hx) ≫ ((toGradedPowerMap ((ofUnitalHom s f L ψ).twisting T
              x)).globalMorphism (relativeProj (s.relativeProjPoints.algebra T (x ≫
              f.hom)))))).hom.app ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫
              f.hom))).algebra.piece d) ≫
        (ofUnitalHom s f L ψ).chartTheta x hx d) := by
  unfold chartSchemeTheta
  rw [fullSubcategory_homMk_hom]
  refine pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_heq _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · rfl
  · exact HEq.rfl

/-- **The comparison of the twists `𝒪(n)` along `y` on the underlying modules, in the spelling of
`…InvertibleTwistingRestriction.chartTheta_square`**: the contraction, the transport along the
square of `…RelativeProjSituation.toRelativeProj`, the inverse contraction and the degree-`n`
piece of `…RelativeProjSituation.pointTwistComparison`, with the graded algebras read through
`s.relativeProjPoints.algebra`. -/
theorem twistPieceComparison_hom_hom_heq {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : s.relativeProjPoints.LiesOver y k) (n : ℤ) :
    HEq (s.twistPieceComparison k hv y hy n).hom.hom
      ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (s.toRelativeProj U u :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre U u) ⟶
            (relativeProj (s.relativeProjPoints.algebra U u)).scheme)).hom.app ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra U u)).algebra.piece n) ≫
        (Scheme.Modules.pullbackCongr (s.map_comp_toRelativeProj y :
          (BigFppfOver.toScheme s.site s.base s.containsBase).map y ≫ (s.toRelativeProj U u :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre U u) ⟶
            (relativeProj (s.relativeProjPoints.algebra U u)).scheme) = (s.toRelativeProj V v :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v) ⟶
            (relativeProj (s.relativeProjPoints.algebra V v)).scheme) ≫ ((BigFppfOver.toScheme
                s.site s.base s.containsBase).map y :
          (relativeProj (s.relativeProjPoints.algebra V v)).scheme ⟶
            (relativeProj (s.relativeProjPoints.algebra U u)).scheme))).hom.app ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra U u)).algebra.piece n) ≫
        (Scheme.Modules.pullbackComp (s.toRelativeProj V v :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v) ⟶
            (relativeProj (s.relativeProjPoints.algebra V v)).scheme) ((BigFppfOver.toScheme s.site
                s.base s.containsBase).map y :
          (relativeProj (s.relativeProjPoints.algebra V v)).scheme ⟶
            (relativeProj (s.relativeProjPoints.algebra U u)).scheme)).inv.app ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra U u)).algebra.piece n) ≫
        (Scheme.Modules.pullback (s.toRelativeProj V v :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v) ⟶
            (relativeProj (s.relativeProjPoints.algebra V v)).scheme)).map
          ((@Iso.hom _ _ (pullbackGradedAlgebra ((BigFppfOver.toScheme s.site s.base
              s.containsBase).map y :
          (relativeProj (s.relativeProjPoints.algebra V v)).scheme ⟶
            (relativeProj (s.relativeProjPoints.algebra U u)).scheme).toLRSHom.toShHom
            (GradedPowerMap.twD (s.shrink.pointAlgebra U u)).algebra)
            (GradedPowerMap.twD (s.shrink.pointAlgebra V v)).algebra
            (s.pointTwistComparison k u v hv ((BigFppfOver.toScheme s.site s.base
                s.containsBase).map y :
          (relativeProj (s.relativeProjPoints.algebra V v)).scheme ⟶
            (relativeProj (s.relativeProjPoints.algebra U u)).scheme)
              (s.toScheme_map_eq_of_liesOver hv hy))).app n :
            (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y :
          (relativeProj (s.relativeProjPoints.algebra V v)).scheme ⟶
            (relativeProj (s.relativeProjPoints.algebra U u)).scheme)).obj ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra U u)).algebra.piece n) ⟶ ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra V v)).algebra.piece n))) := by
  rw [twistPieceComparison_hom_hom]
  refine HEq.trans (heq_of_eq (pullbackSheafIsoOfSquare_gradedPieceIso_hom _ _ _ _ _ _ _)) ?_
  refine pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_inv_app_comp_map_heq _ _ _ _ _
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl

/-- `…InvertibleTwistingRestriction.twistPieceComparison_hom_hom_heq` with the points `u`,
`v` and the morphism `y` of base changes on the two sides as separate variables, equal (`u`, `v`)
or heterogeneously equal (`y`): the two sides may then spell them differently. -/
theorem twistPieceComparison_hom_hom_heq_of_eq {U V : BigFppfOver s.site s.base s.containsBase}
    {u₁ u₂ : yoneda.obj U ⟶ s.space.1} {v₁ v₂ : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
    {hv₁ : yoneda.map k ≫ u₁ = v₁} {hv₂ : yoneda.map k ≫ u₂ = v₂}
    {y₁ : s.relativeProjPoints.fibre V v₁ ⟶ s.relativeProjPoints.fibre U u₁}
    {y₂ : s.relativeProjPoints.fibre V v₂ ⟶ s.relativeProjPoints.fibre U u₂}
    {hy₁ : s.relativeProjPoints.LiesOver y₁ k} {hy₂ : s.relativeProjPoints.LiesOver y₂ k} (n : ℤ)
    (hu : u₁ = u₂) (hv : v₁ = v₂) (hy : HEq y₁ y₂) :
    @HEq ((Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y₁)).obj
        (s.twistPieceQcoh U u₁ n).obj ⟶
        (s.twistPieceQcoh V v₁ n).obj) (s.twistPieceComparison k hv₁ y₁ hy₁ n).hom.hom
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y₂)).obj
          ((Scheme.Modules.pullback (s.toRelativeProj U u₂ :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre U u₂)
              ⟶
            (relativeProj (s.relativeProjPoints.algebra U u₂)).scheme)).obj ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra U u₂)).algebra.piece n)) ⟶
        (Scheme.Modules.pullback (s.toRelativeProj V v₂ :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v₂)
              ⟶
            (relativeProj (s.relativeProjPoints.algebra V v₂)).scheme)).obj ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra V v₂)).algebra.piece n))
      ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map y₂)
          (s.toRelativeProj U u₂ :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre U u₂)
              ⟶
            (relativeProj (s.relativeProjPoints.algebra U u₂)).scheme)).hom.app ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra U u₂)).algebra.piece n) ≫
        (Scheme.Modules.pullbackCongr (s.map_comp_toRelativeProj y₂ :
          (BigFppfOver.toScheme s.site s.base s.containsBase).map y₂ ≫ (s.toRelativeProj U u₂ :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre U u₂)
              ⟶
            (relativeProj (s.relativeProjPoints.algebra U u₂)).scheme) = (s.toRelativeProj V v₂ :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v₂)
              ⟶
            (relativeProj (s.relativeProjPoints.algebra V v₂)).scheme) ≫ ((BigFppfOver.toScheme
                s.site s.base s.containsBase).map y₂ :
          (relativeProj (s.relativeProjPoints.algebra V v₂)).scheme ⟶
            (relativeProj (s.relativeProjPoints.algebra U u₂)).scheme))).hom.app
                ((GradedPowerMap.twD (s.relativeProjPoints.algebra U u₂)).algebra.piece n) ≫
        (Scheme.Modules.pullbackComp (s.toRelativeProj V v₂ :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v₂)
              ⟶
            (relativeProj (s.relativeProjPoints.algebra V v₂)).scheme) ((BigFppfOver.toScheme s.site
                s.base s.containsBase).map y₂ :
          (relativeProj (s.relativeProjPoints.algebra V v₂)).scheme ⟶
            (relativeProj (s.relativeProjPoints.algebra U u₂)).scheme)).inv.app ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra U u₂)).algebra.piece n) ≫
        (Scheme.Modules.pullback (s.toRelativeProj V v₂ :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj (s.relativeProjPoints.fibre V v₂)
              ⟶
            (relativeProj (s.relativeProjPoints.algebra V v₂)).scheme)).map
          ((@Iso.hom _ _ (pullbackGradedAlgebra ((BigFppfOver.toScheme s.site s.base
              s.containsBase).map y₂ :
          (relativeProj (s.relativeProjPoints.algebra V v₂)).scheme ⟶
            (relativeProj (s.relativeProjPoints.algebra U u₂)).scheme).toLRSHom.toShHom
            (GradedPowerMap.twD (s.shrink.pointAlgebra U u₂)).algebra)
            (GradedPowerMap.twD (s.shrink.pointAlgebra V v₂)).algebra
            (s.pointTwistComparison k u₂ v₂ hv₂ ((BigFppfOver.toScheme s.site s.base
                s.containsBase).map y₂ :
          (relativeProj (s.relativeProjPoints.algebra V v₂)).scheme ⟶
            (relativeProj (s.relativeProjPoints.algebra U u₂)).scheme)
              (s.toScheme_map_eq_of_liesOver hv₂ hy₂))).app n :
            (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y₂ :
          (relativeProj (s.relativeProjPoints.algebra V v₂)).scheme ⟶
            (relativeProj (s.relativeProjPoints.algebra U u₂)).scheme)).obj ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra U u₂)).algebra.piece n) ⟶ ((GradedPowerMap.twD
                (s.relativeProjPoints.algebra V v₂)).algebra.piece n))) := by
  subst hu hv
  cases hy
  exact twistPieceComparison_hom_hom_heq k hv₂ y₁ hy₂ n

/-- `…InvertibleTwistingRestriction.chartTheta_square` at the datum `…ofUnitalHom s f L ψ`, with
the comparison `ρ` of the targets the underlying morphism of
`AlgebraicGeometry.Space.pointLaurentPiecePullbackHom`. -/
theorem chartTheta_square_ofUnitalHom (d : ℤ)
    {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (x : yoneda.obj T ⟶ X.1) (hx : (ofUnitalHom s f L ψ).locusOpen T x = ⊤)
    (hx' : (ofUnitalHom s f L ψ).locusOpen T' (yoneda.map τ ≫ x) = ⊤)
    (y : s.relativeProjPoints.fibre T' ((yoneda.map τ ≫ x) ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (x ≫ f.hom))
    (hy : s.relativeProjPoints.LiesOver y τ) :
    type_of% ((ofUnitalHom s f L ψ).chartTheta_square τ x hx d hx' y hy _
      (pointLaurentPiecePullbackHom_comp_eqToHom_hom d τ x)) :=
  (ofUnitalHom s f L ψ).chartTheta_square τ x hx d hx' y hy _
    (pointLaurentPiecePullbackHom_comp_eqToHom_hom d τ x)

/-- `…InvertibleTwistingRestriction.chartSchemeTheta_square` at scheme points `x` of `X` at `T`
and `x'` at `T'` with `x ∘ τ = x'`, the two sections and the two points of `Y` related by
hypotheses `hc`, `hv`. -/
theorem chartSchemeTheta_square_of_eq (d : ℤ)
    {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (x : yoneda.obj T ⟶ X.1) (hx : (ofUnitalHom s f L ψ).locusOpen T x = ⊤)
    (x' : yoneda.obj T' ⟶ X.1) (hx' : (ofUnitalHom s f L ψ).locusOpen T' x' = ⊤)
    (e : yoneda.map τ ≫ x = x')
    (y : s.relativeProjPoints.fibre T' (x' ≫ f.hom) ⟶ s.relativeProjPoints.fibre T (x ≫ f.hom))
    (hy : s.relativeProjPoints.LiesOver y τ)
    (hc : τ ≫ (ofUnitalHom s f L ψ).chartSection x hx =
      (ofUnitalHom s f L ψ).chartSection x' hx' ≫ y)
    (hv : yoneda.map τ ≫ x ≫ f.hom = x' ≫ f.hom)
    (σ : quasicoherentPullbackObj s.site s.base s.containsBase τ
        (quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection x hx) (s.twistPieceQcoh T (x ≫ f.hom) d)) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x' hx') (s.twistPieceQcoh T' (x' ≫ f.hom) d))
    (hσ : σ = (quasicoherentPullbackCompIso s.site s.base s.containsBase τ
        ((ofUnitalHom s f L ψ).chartSection x hx) (s.twistPieceQcoh T (x ≫ f.hom) d)).hom ≫
      quasicoherentPullbackEqToHom s.site s.base s.containsBase hc
        (s.twistPieceQcoh T (x ≫ f.hom) d) ≫
      (quasicoherentPullbackCompIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x' hx') y (s.twistPieceQcoh T (x ≫ f.hom) d)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x' hx') (s.twistPieceComparison τ hv y hy d).hom) :
    quasicoherentPullbackMap s.site s.base s.containsBase τ (chartSchemeTheta s f L ψ x hx d) ≫
          (pointLaurentPiecePullbackHom L τ x d ≫
            eqToHom (congrArg (fun k => pointLaurentPieceQcoh L T' k d) e)) =
      σ ≫ chartSchemeTheta s f L ψ x' hx' d := by
  subst e
  refine quasicoherentPullbackMap_comp_eq_comp_of_hom_eq (B := s.site) (S := s.base)
    (hS := s.containsBase) τ _ _ y hc _ _ _ _ _ σ hσ ?_
  refine pullback_map_comp_eq_comp_of_heq _ _ _ _ (toScheme_map_comp_eq_of_comp_eq hc)
    (chartTheta_square_ofUnitalHom d τ x hx hx' y hy) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · exact chartSchemeTheta_hom_heq d x hx
  · exact HEq.rfl
  · refine twistPieceComparison_hom_hom_heq_of_eq τ (hy₂ := hy) d ?_ ?_ ?_
    · rfl
    · rfl
    · exact HEq.rfl
  · exact chartSchemeTheta_hom_heq d (yoneda.map τ ≫ x) hx'

/-- **The square of `θ` on the schemes of the chart maps of Stacks 0D2Z along `τ : T' ⟶ T`, as
quasi-coherent modules**: for scheme points `w` of `U(ψ)` at `T` and `w' = w ∘ τ` at `T'`, a
morphism `y : T' ×_Y Proj_Y(𝒜) ⟶ T ×_Y Proj_Y(𝒜)` lying over `τ` and the comparison `σ` of the
sources of `θ_w` and `θ_{w'}` along `y` (given by its value `hσ`), `τ^*θ_w` followed by the
comparison `τ^*((w^*ℒ)^{⊗ d}) ⟶ ((w ∘ τ)^*ℒ)^{⊗ d}` of the targets is `σ` followed by `θ_{w'}`.

This is the hypothesis `hm` of
`…InvertibleTwistingRestriction.pointFamilyNatural_chartMap_of_square`, in its binder shape:
`…InvertibleTwistingRestriction.chartTheta_square` at the datum `…ofUnitalHom s f L ψ`, read
through `…InvertibleTwistingRestriction.chartSchemeTheta_square_of_eq`. -/
theorem chartSchemeTheta_square (d : ℤ)
    ⦃T T' : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase⦄ (τ : T' ⟶ T)
    {w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj}
    {w' : yoneda.obj T' ⟶ (locusSpaceOfUnitalHom s f L ψ).obj} (hw : yoneda.map τ ≫ w = w')
    (y : s.relativeProjPoints.fibre T' (locusPoint w' ≫ f.hom) ⟶
      s.relativeProjPoints.fibre T (locusPoint w ≫ f.hom))
    (hy : s.relativeProjPoints.LiesOver y τ)
    (σ : quasicoherentPullbackObj s.site s.base s.containsBase τ
        (quasicoherentPullbackObj s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
          (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
        (s.twistPieceQcoh T' (locusPoint w' ≫ f.hom) d))
    (hσ : σ = (quasicoherentPullbackCompIso s.site s.base s.containsBase τ
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).hom ≫
      quasicoherentPullbackEqToHom s.site s.base s.containsBase
        (comp_chartSection_locusPoint τ hw y hy) (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d) ≫
      (quasicoherentPullbackCompIso s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w')) y
        (s.twistPieceQcoh T (locusPoint w ≫ f.hom) d)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (locusPoint w') (locusOpen_locusPoint w'))
        (s.twistPieceComparison τ (map_comp_locusPoint_comp τ hw) y hy d).hom) :
    quasicoherentPullbackMap s.site s.base s.containsBase τ
        (chartSchemeTheta s f L ψ (locusPoint w) (locusOpen_locusPoint w) d) ≫
          (pointLaurentPiecePullbackHom L τ (locusPoint w) d ≫
            eqToHom (congrArg (fun k => pointLaurentPieceQcoh L T' k d)
              (map_comp_locusPoint τ hw))) =
      σ ≫ chartSchemeTheta s f L ψ (locusPoint w') (locusOpen_locusPoint w') d :=
  chartSchemeTheta_square_of_eq (s := s) d τ (locusPoint w) (locusOpen_locusPoint w)
    (locusPoint w') (locusOpen_locusPoint w') (map_comp_locusPoint τ hw) y hy _ _ σ hσ

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
