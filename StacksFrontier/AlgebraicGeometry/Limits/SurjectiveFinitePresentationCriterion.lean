module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Surjectivity alone suffices for local finite presentation

A morphism of schemes `f : X ⟶ S` is locally of finite presentation as soon as every morphism
to `X` over `S` out of a cofiltered limit of affine schemes over `S` factors through some stage
of the system. Injectivity of the comparison map `colim Mor_S(T_i, X) ⟶ Mor_S(T, X)` is not
needed: in the limit characterisation of Stacks 01ZC, parts (2) and (3), surjectivity is enough.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_of_affineLimit_surjective` — Stacks 0CM0.

## Implementation notes

Surjectivity is phrased elementwise in the category of schemes over the base: each morphism out
of the limit cone's vertex factors through one projection. That is exactly surjectivity of the
canonical map out of the filtered colimit of relative morphism sets, without naming the colimit.
The index categories are cofiltered categories in the universe of the schemes, as in the
affine-limit characterisation of local finite presentation.

The proof reduces to the ring-theoretic criterion. Given affine opens `V ⊆ S` and `U ⊆ X` with
`f U ⊆ V`, local finite presentation asks that `Γ(S, V) ⟶ Γ(X, U)` be of finite presentation,
and Stacks 00QO gives that from surjectivity of `colim Hom(Γ(X,U), A_i) ⟶ Hom(Γ(X,U), colim A_i)`
for directed systems of `Γ(S, V)`-algebras. A directed system of algebras is turned into a
cofiltered system of affine schemes over `S` by `Spec`, its colimit into the limit, and the
hypothesis applied there produces the required factorisation.

## References

* [The Stacks Project, Lemma 32.6.4 (0CM0)](https://stacks.math.columbia.edu/tag/0CM0)
* [The Stacks Project, Proposition 32.6.1 (01ZC)](https://stacks.math.columbia.edu/tag/01ZC)
* [The Stacks Project, Lemma 10.127.3 (00QO)](https://stacks.math.columbia.edu/tag/00QO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FinitePresentationLimit

variable {R : CommRingCat.{u}}
variable {Λ : Type u} [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
variable (A : Λ ⥤ Under R) (c : Cocone A)

private noncomputable def algDiagram {R : CommRingCat.{u}} (A : Λ ⥤ Under R) :
    Λᵒᵖ ⥤ Over (Spec R) :=
  A.op ⋙ (commAlgCatEquivUnder R).inverse.op ⋙ algSpec R

private noncomputable def specCone {R : CommRingCat.{u}} (A : Λ ⥤ Under R) (c : Cocone A) :
    Cone (algDiagram A) :=
  ((commAlgCatEquivUnder R).inverse.op ⋙ algSpec R).mapCone c.op

private noncomputable def isLimitMapSpecCone {S : Scheme.{u}} (φ : Spec R ⟶ S) (hc : IsColimit c) :
    IsLimit ((Over.map φ).mapCone (specCone A c)) := by
  haveI : IsConnected Λᵒᵖ := IsCofiltered.isConnected _
  have : PreservesLimitsOfShape Λᵒᵖ (Over.map φ) := by
    have : PreservesLimitsOfShape Λᵒᵖ (Over.map φ ⋙ Over.forget S) :=
      preservesLimitsOfShape_of_natIso (Over.mapForget φ).symm
    exact preservesLimitsOfShape_of_reflects_of_preserves (Over.map φ) (Over.forget S)
  exact isLimitOfPreserves (Over.map φ) (isLimitOfPreserves _ hc.op)

omit [Nonempty Λ] [IsDirectedOrder Λ] in
private theorem exists_fac_of_specCone_comp {B : Under R} (g : B ⟶ c.pt) (j : Λᵒᵖ)
    (q : (algDiagram A).obj j ⟶
      (algSpec R).obj (Opposite.op ((commAlgCatEquivUnder R).inverse.obj B)))
    (hq : (specCone A c).π.app j ≫ q =
      (algSpec R).map ((commAlgCatEquivUnder R).inverse.map g).op) :
    ∃ g' : B ⟶ A.obj j.unop, g' ≫ c.ι.app j.unop = g := by
  let eR := commAlgCatEquivUnder R
  let qAlgOp := (algSpec.fullyFaithful (R := R)).preimage q
  refine ⟨eR.functor.map qAlgOp.unop, ?_⟩
  have hπspec : (specCone A c).π.app j =
      (algSpec R).map ((eR.inverse.map (c.ι.app j.unop)).op) := by
    dsimp [specCone, algDiagram, eR]
  have hAlg : (algSpec R).map ((eR.inverse.map (c.ι.app j.unop)).op ≫ qAlgOp) =
      (algSpec R).map (eR.inverse.map g).op := by
    rw [Functor.map_comp, ← hπspec, (algSpec.fullyFaithful (R := R)).map_preimage q]
    exact hq
  apply eR.inverse.map_injective
  simp only
  show eR.inverse.map (eR.functor.map qAlgOp.unop) ≫
      eR.inverse.map (c.ι.app j.unop) = eR.inverse.map g
  rw [show eR.inverse.map (eR.functor.map qAlgOp.unop) = qAlgOp.unop by rfl]
  exact congrArg Opposite.unop ((algSpec R).map_injective hAlg)

/-- If a morphism out of a stage of a directed affine system over `S` pulls `U` back to the whole
limit, then it does so already at some later stage. -/
theorem exists_comp_preimage_eq_top_of_isLimit {X S : Scheme.{u}} (D : Λᵒᵖ ⥤ Over S)
    (hD : ∀ i, IsAffine (D.obj i).left) {cL : Cone D} (hL : IsLimit cL) {i : Λᵒᵖ}
    (h : (D.obj i).left ⟶ X) (U : X.Opens) (hpre : (cL.π.app i).left ⁻¹ᵁ (h ⁻¹ᵁ U) = ⊤) :
    ∃ (j : Λᵒᵖ) (kji : j ⟶ i), ((D.map kji).left ≫ h) ⁻¹ᵁ U = ⊤ := by
  let D₀ := D ⋙ Over.forget S
  have (i : Λᵒᵖ) : IsAffine (D₀.obj i) := hD i
  have {i j : Λᵒᵖ} (k : i ⟶ j) : IsAffineHom (D₀.map k) := isAffineHom_of_isAffine _
  obtain ⟨j, kji, hji⟩ := exists_map_eq_top D₀ ((Over.forget S).mapCone cL)
    (isLimitOfPreserves (Over.forget S) hL) (h ⁻¹ᵁ U) hpre
  exact ⟨j, kji, by simpa [D₀, Scheme.Hom.comp_preimage] using hji⟩

/-- A morphism `h : T ⟶ X` over `Spec Γ(S, V)` landing in an affine open `U ⊆ f⁻¹ V` lifts to a
morphism to `Spec Γ(X, U)` over `Spec Γ(S, V)`. -/
theorem exists_overHom_comp_fromSpec_eq {X S : Scheme.{u}} (f : X ⟶ S) {V : S.Opens}
    (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U) (hVU : U ≤ f ⁻¹ᵁ V)
    (T : Over (Spec (CommRingCat.of Γ(S, V)))) (h : T.left ⟶ X) (hU' : h ⁻¹ᵁ U = ⊤)
    (hh : h ≫ f = T.hom ≫ hV.fromSpec) :
    ∃ q : T ⟶ Over.mk (Spec.map (f.appLE V U hVU)), q.left ≫ hU.fromSpec = h := by
  let qU : T.left ⟶ U.toScheme := T.left.topIso.inv ≫ h.resLE U ⊤ hU'.ge
  have hqU : qU ≫ U.ι = h := by
    simp [qU, Scheme.Hom.resLE_comp_ι]
  refine ⟨Over.homMk (qU ≫ hU.isoSpec.hom) ?_, ?_⟩
  · apply (cancel_mono hV.fromSpec).1
    calc
      (qU ≫ hU.isoSpec.hom) ≫ Spec.map (f.appLE V U hVU) ≫ hV.fromSpec = qU ≫ U.ι ≫ f := by
        simp [Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hVU]
      _ = T.hom ≫ hV.fromSpec := by rw [← Category.assoc, hqU, hh]
  · show (qU ≫ hU.isoSpec.hom) ≫ hU.fromSpec = h
    rw [Category.assoc, hU.isoSpec_hom_fromSpec, hqU]

private theorem factorChart
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsurj : ∀ (Λ' : Type u) [PartialOrder Λ'] [Nonempty Λ'] [IsDirectedOrder Λ']
      (D : Λ'ᵒᵖ ⥤ Over S) (c : Cone D), IsLimit c →
      (∀ i, IsAffine (D.obj i).left) →
      ∀ g : c.pt ⟶ Over.mk f,
        ∃ (i : Λ'ᵒᵖ) (gᵢ : D.obj i ⟶ Over.mk f), c.π.app i ≫ gᵢ = g)
    {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U)
    (hVU : U ≤ f ⁻¹ᵁ V)
    {Λ : Type u} [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (A : Λ ⥤ Under (CommRingCat.of Γ(S, V))) (c : Cocone A) (hc : IsColimit c)
    (g : Under.mk (f.appLE V U hVU) ⟶ c.pt) :
    ∃ (l : Λ) (g' : Under.mk (f.appLE V U hVU) ⟶ A.obj l),
      g' ≫ c.ι.app l = g := by
  let R : CommRingCat := CommRingCat.of Γ(S, V)
  let eR := commAlgCatEquivUnder R
  let D : Λᵒᵖ ⥤ Over S := algDiagram A ⋙ Over.map hV.fromSpec
  let cL := (Over.map hV.fromSpec).mapCone (specCone A c)
  have hAffine (i : Λᵒᵖ) : IsAffine (D.obj i).left := by
    show IsAffine (Spec (A.obj i.unop).right)
    infer_instance
  let gSpec := (algSpec R).map (eR.inverse.map g).op
  let chartSpec := (algSpec R).obj
    (Opposite.op (eR.inverse.obj (Under.mk (f.appLE V U hVU))))
  let chartOver : (Over.map hV.fromSpec).obj chartSpec ⟶ Over.mk f :=
    Over.homMk hU.fromSpec (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hVU).symm
  let gOver : cL.pt ⟶ Over.mk f := (Over.map hV.fromSpec).map gSpec ≫ chartOver
  have hL : IsLimit cL := isLimitMapSpecCone A c hV.fromSpec hc
  obtain ⟨i, gᵢ, hgi⟩ := hsurj Λ D cL hL hAffine gOver
  have hpre : (cL.π.app i).left ⁻¹ᵁ (gᵢ.left ⁻¹ᵁ U) = ⊤ := by
    have hgiL : (cL.π.app i).left ≫ gᵢ.left = gOver.left := by
      simpa using congrArg Over.Hom.left hgi
    have hchart : chartOver.left ⁻¹ᵁ U = ⊤ := hU.fromSpec_preimage_self
    rw [← Scheme.Hom.comp_preimage, hgiL]
    show (((Over.map hV.fromSpec).map gSpec).left ≫ chartOver.left) ⁻¹ᵁ U = ⊤
    rw [Scheme.Hom.comp_preimage, hchart]
    simp
  obtain ⟨j, kji, hlateTop⟩ :=
    exists_comp_preimage_eq_top_of_isLimit D hAffine hL gᵢ.left U hpre
  let lateX : (D.obj j).left ⟶ X := (D.map kji).left ≫ gᵢ.left
  have hlateBase : lateX ≫ f = ((algDiagram A).obj j).hom ≫ hV.fromSpec := by
    calc
      lateX ≫ f = (D.map kji).left ≫ (D.obj i).hom := by
        simpa [lateX, Category.assoc] using congrArg (fun k ↦ (D.map kji).left ≫ k) gᵢ.w
      _ = (D.obj j).hom := (D.map kji).w
      _ = ((algDiagram A).obj j).hom ≫ hV.fromSpec := by simp [D, algDiagram]
  obtain ⟨q, hq⟩ := exists_overHom_comp_fromSpec_eq f hV hU hVU ((algDiagram A).obj j) lateX
    hlateTop hlateBase
  have hproj : (cL.π.app j).left ≫ (D.map kji).left = (cL.π.app i).left := by
    simpa [D] using congrArg Over.Hom.left (cL.w kji)
  have hpiLate : ((specCone A c).π.app j).left ≫ lateX = gOver.left := by
    show (cL.π.app j).left ≫ ((D.map kji).left ≫ gᵢ.left) = gOver.left
    rw [← Category.assoc, hproj]
    exact congrArg Over.Hom.left hgi
  have hgo : gOver.left = gSpec.left ≫ hU.fromSpec := by
    show ((Over.map hV.fromSpec).map gSpec).left ≫ hU.fromSpec =
      gSpec.left ≫ hU.fromSpec
    rw [Over.map_map_left]
  have hfactorLeft : ((specCone A c).π.app j).left ≫ q.left = gSpec.left := by
    apply (cancel_mono hU.fromSpec).1
    rw [Category.assoc, hq, hpiLate, hgo]
    rfl
  obtain ⟨g', hg'⟩ := exists_fac_of_specCone_comp A c g j q (Over.OverMorphism.ext hfactorLeft)
  exact ⟨j.unop, g', hg'⟩

end AlgebraicGeometry.FinitePresentationLimit

namespace AlgebraicGeometry

/-- If every map to `X` out of the limit of a **directed** inverse system of affine schemes over
`S` descends to a finite stage, then `X ⟶ S` is locally of finite presentation.

This is the sharp form of the criterion: the index categories are the opposites of directed
posets in the universe of the schemes, rather than arbitrary cofiltered categories, which is all
the ring-theoretic criterion of Stacks 00QO ever needs. Limit preservation in the sense of
`AlgebraicGeometry.ExtendingFunctors.PreservesAffineLimits` is tested on exactly these index
categories, so it is this form and not
`AlgebraicGeometry.locallyOfFinitePresentation_of_affineLimit_surjective` that applies to a
functor known to be limit preserving in that sense. -/
@[ega "IV 17.3.2" "partial", ega "IV 8.14.2" "partial", sga "3 XI 3.2" "partial"]
public theorem locallyOfFinitePresentation_of_directedAffineLimit_surjective
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsurj : ∀ (Λ : Type u) [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
      (D : Λᵒᵖ ⥤ Over S) (c : Cone D), IsLimit c →
      (∀ i, IsAffine (D.obj i).left) →
      ∀ g : c.pt ⟶ Over.mk f,
        ∃ (i : Λᵒᵖ) (gᵢ : D.obj i ⟶ Over.mk f), c.π.app i ≫ gᵢ = g) :
    LocallyOfFinitePresentation f := by
  refine LocallyOfFinitePresentation.mk ?_
  intro V hV U hU hVU
  let R : CommRingCat := CommRingCat.of Γ(S, V)
  let A₀ : Under R := Under.mk (f.appLE V U hVU)
  simpa [A₀] using ((CommRingCat.isFinitelyPresentable_under_tfae A₀).out 3 1).mp (by
    intro Λ hPO hNE hDir D c hc g
    exact FinitePresentationLimit.factorChart f hsurj hV hU hVU D c hc g)

/-- If every map from a cofiltered limit of affine schemes over `S` to `X`
descends to a finite stage, then `X ⟶ S` is locally of finite presentation. -/
@[stacks 0CM0, sga "3 XI 3.2" "partial"]
public theorem locallyOfFinitePresentation_of_affineLimit_surjective
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hsurj : ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ Over S) (c : Cone D), IsLimit c →
      (∀ i, IsAffine (D.obj i).left) →
      ∀ g : c.pt ⟶ Over.mk f,
        ∃ (i : I) (gᵢ : D.obj i ⟶ Over.mk f), c.π.app i ≫ gᵢ = g) :
    LocallyOfFinitePresentation f :=
  locallyOfFinitePresentation_of_directedAffineLimit_surjective f
    fun Λ _ _ _ D c hc hD g => hsurj Λᵒᵖ D c hc hD g

end AlgebraicGeometry

end
