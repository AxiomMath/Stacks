module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceIsSpecGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.IsomorphismOfChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationGlobalFunctionsDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentSituationGlobalFunctionsDescentSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback

/-!
# Cartesianness at the limit of the square of Stacks 084U

In the situation of Stacks 084R, let the limit `X = lim X_i` be affine, let `A_i` be a model of
the global functions of a stage, let `A_i[x₁, …, xₙ] ⧸ (g₁, …, gₙ)` be a presentation over it and
let `U_i ⟶ X_i` be an affine étale chart carrying functions `h₁, …, hₙ` killing the `g_λ`. The
square of Stacks 084U,

```
  X_i   ⟵ U_i
   ↓       ↓
Spec A_i ⟵ Spec B_i
```

is then available at the stage, and base changing it to the limit gives the morphism `f₀` of
display 70.5.10.1 of the proof of Stacks 07SQ. This file proves that *the base change of `f₀` to
the limit is an isomorphism*, which is the hypothesis `hf` of Stacks 084S,
`AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded.exists_isIso_mapAt`.

## Main results

* `AlgebraicGeometry.Space.isIso_specMapOfGlobalHom_yonedaSpace`: over a terminal base an affine
  object of the site is the spectrum of any model of its regular functions.
* `AlgebraicGeometry.Space.comp_coordinateHom_eq_coordinateHom_comp_presentationBaseChangeHom`
  and `AlgebraicGeometry.Space.yoneda_map_comp_specMapOfGlobalHom_presentation`: the two
  morphisms `U ⟶ Spec B_i` of the proof of Stacks 07SQ — the limit chart followed by the right
  vertical at the stage, and the right vertical at the limit followed by the base change of the
  presentation — agree.
* `AlgebraicGeometry.Space.DescentSituation.isPullback_paste_of_isIso_horiz`: the horizontal
  pasting which makes the outer rectangle `U ⟶ Spec B_i`, `X ⟶ Spec A_i` Cartesian.
* `AlgebraicGeometry.Space.MorphismDescentSystemOfChartsBounded.isIso_mapLimit_of_isPullback`: a
  base change to the limit whose outer rectangle is Cartesian is an isomorphism.
* `AlgebraicGeometry.Space.DescentSituation.isIso_mapLimit_morphismDescentSystemOfPresentation`:
  the two combined, which is the hypothesis `hf` of Stacks 084S in the situation of the proof of
  Stacks 07SQ.

## Implementation notes

*Why the pasting works.* The outer rectangle is the horizontal pasting of the square of Stacks
084U at the limit chart with the square of the base change of the presentation along
`A_i ⟶ A`. The second is Cartesian because the square of rings is a pushout, which is
`AlgebraicGeometry.Space.isPullback_schemePointsMap_presentationBaseChange`; the first is
Cartesian because *both of its horizontal edges are invertible*: `X ⟶ Spec A` is invertible
because `X` is affine and the base is terminal
(`AlgebraicGeometry.Space.isIso_specMapOfGlobalHom_of_isAffineSpace`), and `U ⟶ Spec B` is
invertible by the same statement read at the limit chart, the model of its regular functions
being the presentation.

*Why the model of the limit chart is not `Γ(U, 𝒪_U)`.* The right vertical of the square of
Stacks 084U at the limit lands in the spectrum of the base-changed presentation
`A[x] ⧸ (g)`, not in the spectrum of the regular functions of the limit chart; the two are
identified by a ring isomorphism, and that is exactly why
`AlgebraicGeometry.Space.isIso_specMapOfGlobalHom_of_isAffineSpace` is stated for an arbitrary
`u`-model rather than for the regular functions of the representing scheme.

*The two identifications the pasting runs on.* The morphism `X ⟶ Spec A_i` of the descent system
is `lim π ≫ p_i`, whereas the pasting produces `X ⟶ Spec A ⟶ Spec A_i`. The two agree, and the
proof is that they agree after composing with the limit chart — which cancels, the limit chart
being a surjective étale chart
(`AlgebraicGeometry.Space.hom_ext_of_etale_atlas`) — where both become the composite
`U ⟶ Spec B_i ⟶ Spec A_i`. The agreement of the two morphisms `U ⟶ Spec B_i` needed for that is
the ring identity of
`AlgebraicGeometry.Space.comp_coordinateHom_eq_coordinateHom_comp_presentationBaseChangeHom`,
whose two clauses are that the chosen functions at the limit are the restrictions of those at the
stage and that the structure homomorphism at the limit restricts to the one at the stage.

*The limit of the system against the limit of the situation.* Stacks 084W is stated at the
categorical limit `CategoryTheory.Limits.limit` of the inverse system, whereas a descent
situation carries its own limiting cone; `AlgebraicGeometry.Space.DescentSituation.limitObjSpace`
is the former read as an algebraic space, the algebraicity being transported along the canonical
comparison of two limiting cones. Everything below is stated at the categorical limit, so no
further transport intervenes.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 084S](https://stacks.math.columbia.edu/tag/084S)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_AffineLimitChartCartesian :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site, as a high-priority shortcut. -/
local instance (priority := high) hasPullback_presheaf_AffineLimitChartCartesian
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Postcomposing the morphism to a spectrum attached to a homomorphism into global functions
with the spectrum of a ring homomorphism restricts the homomorphism along it. -/
theorem specMapOfGlobalHom_comp_SpecMap {Y : Scheme.{u}} (A A' : Type u) [CommRing A]
    [CommRing A'] (ψ : A →+* Γ(Y, ⊤)) (χ : A' →+* A) :
    specMapOfGlobalHom A ψ ≫ Spec.map (CommRingCat.ofHom χ) =
      specMapOfGlobalHom A' (ψ.comp χ) := by
  rw [specMapOfGlobalHom, specMapOfGlobalHom, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]

/-- **The chart formula for the canonical morphism out of a representable presheaf.** For a
homomorphism `ψ : A →+* Γ(W, 𝒪_W)` the morphism of presheaves `yoneda W ⟶ Spec A` attached to it
satisfies, at every étale chart of `yoneda W`, the formula which characterises the canonical
morphism to the spectrum of a ring of global functions. -/
theorem yonedaEquiv_comp_specMapOfGlobalHom_yonedaSpace (W : BigFppfOver B S hS)
    (A : Type u) [CommRing A] (ψ : A →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (V : SmallEtale B S hS (yoneda.obj W)) :
    yonedaEquiv (V.1.hom ≫ (yonedaEquiv.symm (specMapOfGlobalHom A ψ) :
        yoneda.obj W ⟶ schemePoints B S hS (Spec (CommRingCat.of A)))) =
      specMapOfGlobalHom A ((globalFunctionsChartRestriction B S hS
          (yonedaSpace B S hS W) V).comp
        ((globalFunctionsAffineEquiv B S hS (yonedaSpace B S hS W) W
          (Iso.refl _)).symm.toRingHom.comp ψ)) := by
  obtain ⟨v, hv⟩ : ∃ v, yoneda.map v = V.1.hom :=
    ⟨yoneda.preimage V.1.hom, Functor.map_preimage _ _⟩
  have hpre : yoneda.preimage V.1.hom = v := by rw [← hv]; exact Functor.preimage_map _
  have hcomp : ((globalFunctionsChartRestriction B S hS (yonedaSpace B S hS W) V).comp
        ((globalFunctionsAffineEquiv B S hS (yonedaSpace B S hS W) W
          (Iso.refl _)).symm.toRingHom.comp ψ))
      = (((BigFppfOver.toScheme B S hS).map v).appTop.hom).comp ψ := by
    refine RingHom.ext fun x => ?_
    have h := globalFunctionsChartRestriction_globalFunctionsAffineEquiv_symm B S hS
      (yonedaSpace B S hS W) W (Iso.refl _) V (ψ x)
    rw [Iso.refl_hom, Category.comp_id, hpre] at h
    simpa using h
  rw [hcomp, ← comp_specMapOfGlobalHom, ← hv, ← yonedaEquiv_naturality,
    Equiv.apply_symm_apply]
  rfl

/-- **An affine object of the site is the spectrum of any model of its regular functions.**
Over a terminal base, the morphism `yoneda W ⟶ Spec A` attached to a ring *isomorphism*
`A ≃+* Γ(W, 𝒪_W)` is an isomorphism of presheaves, provided the scheme underlying `W` is
affine. -/
theorem isIso_specMapOfGlobalHom_yonedaSpace (hterminal : IsTerminal S)
    (W : BigFppfOver B S hS) (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (A : Type u) [CommRing A] (ψ : A →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (hψ : Function.Bijective ψ) :
    IsIso (yonedaEquiv.symm (specMapOfGlobalHom A ψ) :
      yoneda.obj W ⟶ schemePoints B S hS (Spec (CommRingCat.of A))) := by
  refine isIso_specMapOfGlobalHom_of_isAffineSpace B S hS hterminal
    (yonedaSpace B S hS W) W hW (Iso.refl _) A
    ((RingEquiv.ofBijective ψ hψ).trans
      (globalFunctionsAffineEquiv B S hS (yonedaSpace B S hS W) W (Iso.refl _)).symm)
    fun V => ?_
  rw [yonedaEquiv_comp_specMapOfGlobalHom_yonedaSpace B S hS W A ψ V]
  rfl


variable {B S hS}

/-- **The formal step of the last part of the proof of Stacks 07SQ.** Let `D` be the situation of
Stacks 084W, let the target `Y₀` of the morphism to be descended sit in a Cartesian square over
the chosen stage, and suppose the outer rectangle at the limit is Cartesian with the same apex as
the base change of the source. Then the base change `f` of `f₀` to the limit is an isomorphism.

Both base changes compare two cones over the one cospan `q`, `lim π ≫ p`, so the comparison is
the canonical isomorphism of two limits. -/
theorem MorphismDescentSystemOfChartsBounded.isIso_mapLimit_of_isPullback
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : MorphismDescentSystemOfChartsBounded B S hS hZ I)
    {Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {r₀ : D.target₀ ⟶ Z'}
    {p : D.base.obj (op D.initial) ⟶ Z} {q : Z' ⟶ Z}
    (htgt : IsPullback D.targetToBase r₀ p q)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : P ⟶ limit D.base} {b : P ⟶ D.source₀}
    (hstage : IsPullback c b (limit.π D.base (op D.initial)) D.sourceToBase)
    (hsrc : IsPullback (b ≫ D.map₀ ≫ r₀) c q (limit.π D.base (op D.initial) ≫ p)) :
    IsIso D.mapLimit := by
  have htgtlim : IsPullback
      (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase ≫ r₀)
      (pullback.fst (limit.π D.base (op D.initial)) D.targetToBase) q
      (limit.π D.base (op D.initial) ≫ p) :=
    (D.targetLimit_isPullback.paste_vert htgt).flip
  set ε : P ≅ D.sourceLimit := hstage.isoIsPullback _ _ D.sourceLimit_isPullback with hε
  set δ : P ≅ D.targetLimit := hsrc.isoIsPullback _ _ htgtlim with hδ
  have hεfst : ε.hom ≫ pullback.fst (limit.π D.base (op D.initial)) D.sourceToBase = c :=
    hstage.isoIsPullback_hom_fst _ _ D.sourceLimit_isPullback
  have hεsnd : ε.hom ≫ pullback.snd (limit.π D.base (op D.initial)) D.sourceToBase = b :=
    hstage.isoIsPullback_hom_snd _ _ D.sourceLimit_isPullback
  have hδfst : δ.hom ≫ (pullback.snd (limit.π D.base (op D.initial)) D.targetToBase ≫ r₀)
      = b ≫ D.map₀ ≫ r₀ := hsrc.isoIsPullback_hom_fst _ _ htgtlim
  have hδsnd : δ.hom ≫ pullback.fst (limit.π D.base (op D.initial)) D.targetToBase = c :=
    hsrc.isoIsPullback_hom_snd _ _ htgtlim
  have hmap : D.mapLimit = ε.inv ≫ δ.hom := by
    refine ε.eq_inv_comp.2 (htgtlim.hom_ext ?_ ?_)
    · erw [hδfst, Category.assoc, ← Category.assoc D.mapLimit, D.mapLimit_snd,
        Category.assoc, ← Category.assoc, hεsnd]
    · erw [Category.assoc, D.mapLimit_fst, hδsnd, hεfst]
  rw [hmap]
  infer_instance



/-- The homomorphism out of a presentation, evaluated at the class of a polynomial, is the
evaluation of that polynomial. -/
theorem coordinateHom_mk {A R : Type u} [CommRing A] [CommRing R] {m : ℕ}
    (g : Fin m → MvPolynomial (Fin m) A) (ψ : A →+* R) (h : Fin m → R)
    (hrel : ∀ l, MvPolynomial.eval₂ ψ h (g l) = 0) (r : MvPolynomial (Fin m) A) :
    coordinateHom g ψ h hrel (Ideal.Quotient.mk (Ideal.span (Set.range g)) r)
      = MvPolynomial.eval₂ ψ h r := rfl


/-! ### The two morphisms to the spectrum of the presentation at the stage -/

section Presentation

variable {Ai Al R R' : Type u} [CommRing Ai] [CommRing Al] [CommRing R] [CommRing R']
  {n : ℕ} (gi : Fin n → MvPolynomial (Fin n) Ai) (mp : Ai →+* Al)
  {ψi : Ai →+* R} {hi : Fin n → R} (hreli : ∀ l, MvPolynomial.eval₂ ψi hi (gi l) = 0)
  {ψl : Al →+* R'} {hl : Fin n → R'}
  (hrell : ∀ l, MvPolynomial.eval₂ ψl hl (MvPolynomial.map mp (gi l)) = 0)
  {χ : R →+* R'} (hmp : ψl.comp mp = χ.comp ψi) (hhl : ∀ k, hl k = χ (hi k))

include hmp hhl

/-- **The base change of a presentation, read through the two coordinate homomorphisms.**
Restricting the coordinate homomorphism of the base-changed presentation along the base-change
homomorphism is the coordinate homomorphism of the original presentation followed by `χ`, as
soon as `χ` carries the chosen elements and the structure homomorphism to theirs.

This is the ring identity behind the identification of the two morphisms `U ⟶ Spec B_i` in the
proof of Stacks 07SQ: one of them is the limit chart followed by the right vertical of the square
of Stacks 084U at the stage, the other the right vertical at the limit followed by the base
change of the presentation. -/
theorem comp_coordinateHom_eq_coordinateHom_comp_presentationBaseChangeHom :
    χ.comp (coordinateHom gi ψi hi hreli)
      = (coordinateHom (fun k => MvPolynomial.map mp (gi k)) ψl hl hrell).comp
        (presentationBaseChangeHom mp gi) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_))
  · simp only [RingHom.comp_apply, coordinateHom_mk, presentationBaseChangeHom_mk,
      MvPolynomial.eval₂_C, MvPolynomial.map_C]
    exact (RingHom.congr_fun hmp r).symm
  · simp only [RingHom.comp_apply, coordinateHom_mk, presentationBaseChangeHom_mk,
      MvPolynomial.eval₂_X, MvPolynomial.map_X]
    exact (hhl k).symm

end Presentation

/-- **The two morphisms `U ⟶ Spec B_i` of the proof of Stacks 07SQ agree.** The morphism of the
site underlying the limit chart followed by the right vertical of the square of Stacks 084U at
the stage is the right vertical at the limit followed by the base change of the presentation. -/
theorem yoneda_map_comp_specMapOfGlobalHom_presentation
    {U W : BigFppfOver B S hS} (b : W ⟶ U)
    {Ai : Type u} [CommRing Ai] {n : ℕ} (gi : Fin n → MvPolynomial (Fin n) Ai)
    {Al : Type u} [CommRing Al] (mp : Ai →+* Al)
    {ψi : Ai →+* Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    {hi : Fin n → Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    (hreli : ∀ l, MvPolynomial.eval₂ ψi hi (gi l) = 0)
    {ψl : Al →+* Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)}
    {hl : Fin n → Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)}
    (hrell : ∀ l, MvPolynomial.eval₂ ψl hl (MvPolynomial.map mp (gi l)) = 0)
    (hmp : ψl.comp mp = (((BigFppfOver.toScheme B S hS).map b).appTop.hom).comp ψi)
    (hhl : ∀ k, hl k = ((BigFppfOver.toScheme B S hS).map b).appTop.hom (hi k)) :
    yoneda.map b ≫ (yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra gi)
          (coordinateHom gi ψi hi hreli)) :
        yoneda.obj U ⟶ schemePoints B S hS (Spec (CommRingCat.of (presentationAlgebra gi))))
      = (yonedaEquiv.symm (specMapOfGlobalHom
            (presentationAlgebra (fun k => MvPolynomial.map mp (gi k)))
            (coordinateHom (fun k => MvPolynomial.map mp (gi k)) ψl hl hrell)) :
          yoneda.obj W ⟶ schemePoints B S hS (Spec (CommRingCat.of
            (presentationAlgebra (fun k => MvPolynomial.map mp (gi k)))))) ≫
        schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (presentationBaseChangeHom mp gi))) := by
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_comp_schemePointsMap, Equiv.apply_symm_apply,
    specMapOfGlobalHom_comp_SpecMap,
    ← comp_coordinateHom_eq_coordinateHom_comp_presentationBaseChangeHom gi mp hreli hrell
      hmp hhl,
    ← comp_specMapOfGlobalHom, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  rfl

/-! ### The pasting at the limit -/

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- The categorical limit of the inverse system of a descent situation, as an algebraic space
over `S`: the vertex of the chosen limiting cone is one, and the two limits are canonically
isomorphic. -/
abbrev DescentSituation.limitObjSpace (D : DescentSituation B S hS hZ I) :
    AlgebraicSpaces B S hS :=
  ⟨limit D.system, IsAlgebraicSpace.of_iso D.limitAlgebraicSpace
    (D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system))⟩

namespace DescentSituation

variable (D : DescentSituation B S hS hZ I)

/-- **The horizontal pasting at the limit, in the abstract.** Let `D` be a descent situation, let
`a : yoneda U ⟶ X₀` be a scheme-valued point of the chosen stage, let `p : X₀ ⟶ Z` and
`q : Z' ⟶ Z` be morphisms and let `f₀` be a morphism over `X₀` from `a` to the base change of `q`
along `p`. Suppose the limit chart `c : yoneda W ⟶ lim X_i` exhibits `yoneda W` as the base change
of `a` along the limit projection, and suppose given a commuting square

```
  yoneda W --qW--> Z'l
     |              |
     c             vlim
     v              v
  lim X_i --plim--> Zl
```

whose two horizontals are invertible, together with a Cartesian square `hmid`, `vlim`, `q`,
`hbot` identifying `Z'l` as the base change of `Z'` and an identification of the two morphisms
`yoneda W ⟶ Z'`. Then the outer rectangle is Cartesian.

The two horizontals being invertible makes the left-hand square Cartesian
(`CategoryTheory.IsPullback.of_horiz_isIso`), so the conclusion is the horizontal pasting of two
Cartesian squares; what the hypotheses additionally buy is the identification of the composite
`lim X_i ⟶ Zl ⟶ Z` with `lim X_i ⟶ X₀ ⟶ Z`, which holds because the limit chart is a surjective
étale chart and so cancels. -/
theorem isPullback_paste_of_isIso_horiz
    {Z Z' Zl Z'l : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : D.system.obj (op D.base) ⟶ Z} {q : Z' ⟶ Z}
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ D.system.obj (op D.base)}
    (f₀ : Over.mk a ⟶ Over.mk (pullback.fst p q))
    {W : BigFppfOver B S hS} {c : yoneda.obj W ⟶ limit D.system} {b : W ⟶ U}
    (hstage : IsPullback c (yoneda.map b) (limit.π D.system (op D.base)) a)
    (hcchart : IsEtaleChart B S hS (limit D.system) (CostructuredArrow.mk c))
    (hcsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    {plim : limit D.system ⟶ Zl} [IsIso plim] {qW : yoneda.obj W ⟶ Z'l} [IsIso qW]
    {vlim : Z'l ⟶ Zl} {hbot : Zl ⟶ Z} {hmid : Z'l ⟶ Z'}
    (hsq : c ≫ plim = qW ≫ vlim) (hbc : IsPullback hmid vlim q hbot)
    (halpha : yoneda.map b ≫ f₀.left ≫ pullback.snd p q = qW ≫ hmid)
    (hZ' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z) :
    IsPullback (yoneda.map b ≫ f₀.left ≫ pullback.snd p q) c q
      (limit.π D.system (op D.base) ≫ p) := by
  have hfw : f₀.left ≫ pullback.fst p q = a := Over.w f₀
  have hbeta : plim ≫ hbot = limit.π D.system (op D.base) ≫ p := by
    refine hom_ext_of_etale_atlas B S hS D.limitObjSpace.property.isSheaf hZ' c hcsurj
      hcchart ?_
    rw [reassoc_of% hsq, ← hbc.w, ← reassoc_of% halpha, ← pullback.condition,
      reassoc_of% hfw, ← reassoc_of% hstage.w]
  rw [halpha, ← hbeta]
  exact (IsPullback.of_horiz_isIso ⟨hsq.symm⟩).paste_horiz hbc

/-- **The hypothesis `hf` of Stacks 084S, in the situation of the proof of Stacks 07SQ.** In a
descent situation whose limit `X` is affine, with the square of Stacks 084U formed at a stage out
of a descended presentation, the base change to the limit of the morphism `f₀` of display
70.5.10.1 is an isomorphism.

The hypotheses say that the data at the limit is the base change of the data at the stage: the
polynomials are the images of those at the stage under `A_i ⟶ A`, the chosen functions are the
restrictions along the limit chart, and `ψ` at the limit restricts to `ψ` at the stage. -/
theorem isIso_mapLimit_morphismDescentSystemOfPresentation (hterminal : IsTerminal S)
    (hI : ChartsBounded B S hS D.system)
    {Ai : Type u} [CommRing Ai] {n : ℕ} (gi : Fin n → MvPolynomial (Fin n) Ai)
    {p : D.system.obj (op D.base) ⟶ schemePoints B S hS (Spec (CommRingCat.of Ai))}
    {U : BigFppfOver B S hS}
    (hUqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    {a : yoneda.obj U ⟶ D.system.obj (op D.base)} (ha : IsEtale B S hS a)
    (f₀ : Over.mk a ⟶ Over.mk (pullback.fst p (schemePointsMap B S hS
      (Spec.map (CommRingCat.ofHom (presentationStructureHom gi))))))
    {ψi : Ai →+* Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    {hi : Fin n → Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)}
    {hreli : ∀ l, MvPolynomial.eval₂ ψi hi (gi l) = 0}
    (hf₀snd : f₀.left ≫ pullback.snd p (schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (presentationStructureHom gi))))
        = yonedaEquiv.symm (specMapOfGlobalHom (presentationAlgebra gi)
            (coordinateHom gi ψi hi hreli)))
    {W : BigFppfOver B S hS} (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    {c : yoneda.obj W ⟶ limit D.system} {b : W ⟶ U}
    (hstage : IsPullback c (yoneda.map b) (limit.π D.system (op D.base)) a)
    (hcchart : IsEtaleChart B S hS (limit D.system) (CostructuredArrow.mk c))
    (hcsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    {T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (eT : limit D.system ≅ yoneda.obj T)
    (mp : Ai →+* Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    {ψlim : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+*
      Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)}
    (hψlim : ψlim = (globalFunctionsChartRestriction B S hS D.limitObjSpace
          ⟨CostructuredArrow.mk c, hcchart⟩).comp
        (globalFunctionsAffineEquiv B S hS D.limitObjSpace T eT).symm.toRingHom)
    {hlim : Fin n → Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)}
    (hhlim : ∀ k, hlim k = ((BigFppfOver.toScheme B S hS).map b).appTop.hom (hi k))
    (hmp : ψlim.comp mp = (((BigFppfOver.toScheme B S hS).map b).appTop.hom).comp ψi)
    {hrellim : ∀ l, MvPolynomial.eval₂ ψlim hlim (MvPolynomial.map mp (gi l)) = 0}
    (hbij : Function.Bijective
      (coordinateHom (fun k => MvPolynomial.map mp (gi k)) ψlim hlim hrellim)) :
    IsIso
      (D.morphismDescentSystemOfPresentationOfChartsBounded hI gi p hUqc hUqs ha f₀).mapLimit := by
  obtain ⟨plim, hplimiso, hplimchart⟩ :=
    exists_isIso_specMap_of_isAffineSpace B S hS hterminal D.limitObjSpace T hT eT
  have := hplimiso
  have := isIso_specMapOfGlobalHom_yonedaSpace B S hS hterminal W hWaff
    (presentationAlgebra (fun k => MvPolynomial.map mp (gi k)))
    (coordinateHom (fun k => MvPolynomial.map mp (gi k)) ψlim hlim hrellim) hbij
  have hsq : c ≫ plim
      = (yonedaEquiv.symm (specMapOfGlobalHom
            (presentationAlgebra (fun k => MvPolynomial.map mp (gi k)))
            (coordinateHom (fun k => MvPolynomial.map mp (gi k)) ψlim hlim hrellim)) :
          yoneda.obj W ⟶ schemePoints B S hS (Spec (CommRingCat.of
            (presentationAlgebra (fun k => MvPolynomial.map mp (gi k)))))) ≫
        schemePointsMap B S hS (Spec.map (CommRingCat.ofHom
          (presentationStructureHom (fun k => MvPolynomial.map mp (gi k))))) := by
    subst hψlim
    exact commSq_chart_specOfGlobalFunctions B S hS D.limitObjSpace
      ⟨CostructuredArrow.mk c, hcchart⟩ (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
      (globalFunctionsAffineEquiv B S hS D.limitObjSpace T eT).symm
      (fun k => MvPolynomial.map mp (gi k)) hlim hrellim plim
      (hplimchart ⟨CostructuredArrow.mk c, hcchart⟩)
  have halpha : yoneda.map b ≫ f₀.left ≫ pullback.snd p (schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (presentationStructureHom gi))))
      = (yonedaEquiv.symm (specMapOfGlobalHom
            (presentationAlgebra (fun k => MvPolynomial.map mp (gi k)))
            (coordinateHom (fun k => MvPolynomial.map mp (gi k)) ψlim hlim hrellim)) :
          yoneda.obj W ⟶ schemePoints B S hS (Spec (CommRingCat.of
            (presentationAlgebra (fun k => MvPolynomial.map mp (gi k)))))) ≫
        schemePointsMap B S hS
          (Spec.map (CommRingCat.ofHom (presentationBaseChangeHom mp gi))) := by
    rw [hf₀snd]
    exact yoneda_map_comp_specMapOfGlobalHom_presentation b gi mp hreli hrellim hmp hhlim
  exact MorphismDescentSystemOfChartsBounded.isIso_mapLimit_of_isPullback _
    (IsPullback.of_hasPullback _ _)
    hstage (D.isPullback_paste_of_isIso_horiz f₀ hstage hcchart hcsurj hsq
      (isPullback_schemePointsMap_presentationBaseChange B S hS mp gi).flip halpha
      (isSheaf_schemePoints B S hS _))

end DescentSituation

end AlgebraicGeometry.Space

end
