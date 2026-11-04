module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The reduction of the source of a smooth representable morphism

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` which is representable by algebraic spaces and smooth. Stacks
0GB7 identifies the reduction of `X` with the base change `X ×_Y Y_red` of the reduction of
`Y`. The identification is proved in the two halves it naturally has: the fibre product
`X ×_Y Y_red`, with its projection to `X`, satisfies the defining properties of a reduction of
`X` (`AlgebraicGeometry.FormalSpace.IsReduction`), and any two reductions of one sheaf are
isomorphic over it, so every comparison morphism `X_red ⟶ X ×_Y Y_red` over `X` is an
isomorphism.

The argument is the one of the source. The fibre product is an algebraic space by Stacks 03XY,
since `f` is representable by algebraic spaces and `Y_red` is an algebraic space. Its second
projection to `Y_red` is a base change of `f`, hence smooth, so the fibre product is reduced by
Stacks 0GB3. Its first projection to `X` is a base change of the inclusion `Y_red ⟶ Y`, hence a
representable thickening. Finally a morphism to `X` from a reduced algebraic space factors
uniquely through the fibre product, because its composite with `f` factors uniquely through
`Y_red` by the universal property of the reduction of `Y`; this half uses neither smoothness
nor representability.

## Main definitions

* `AlgebraicGeometry.Space.IsSmoothULift`: **Stacks 03ZC**, part (1), for a morphism of
  presheaves with values in a universe independent of the universe of the schemes.
* `AlgebraicGeometry.Space.smoothPropertyULift`: the same condition as a property of morphisms
  of algebraic spaces over `S` in that value universe.

## Main results

* `AlgebraicGeometry.Space.hasEtaleLocalPropertyULift_isReduced_of_isSmoothULift`:
  **Stacks 0GB3**, reducedness of the source, in a larger value universe.
* `AlgebraicGeometry.FormalSpace.isReduction_pullback_reduction_of_smooth`: **Stacks 0GB7**,
  the fibre product `X ×_Y Y_red` is a reduction of `X`.
* `AlgebraicGeometry.FormalSpace.isIso_of_isReduction_of_isPullback_of_smooth`:
  **Stacks 0GB7**, every comparison morphism `X_red ⟶ X ×_Y Y_red` over `X` is an isomorphism.

## Implementation notes

Exactly as for Stacks 0GB8 in `StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction`, the
reductions and their inclusions are givens rather than constructed, and the fibre product is
quantified over as a cartesian square rather than chosen. Reductions exist, by Stacks 0AIN,
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`, so this is more
general than the statement about chosen reductions and a chosen fibre product, which it
implies, and it needs no choice. For the same reason the conclusion is stated in the two
halves described above rather than as an equality of chosen objects: without a choice of
reduction there are no subobjects of `X` to equate, and the pair of halves is what such an
equality would amount to.

Smoothness of `f` is the condition of Stacks 03XZ at smoothness of morphisms of algebraic
spaces, that is `AlgebraicGeometry.Space.HasPropertyULift` at
`AlgebraicGeometry.Space.smoothPropertyULift`, exactly as étaleness of an atlas arrow is
recorded in `AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace`. Smoothness of a morphism of
algebraic spaces in the value universe of the formal algebraic spaces is the every-étale-chart
condition `AlgebraicGeometry.Space.HoldsOnEveryEtaleChartULift` at smoothness of morphisms of
schemes, which is the definition of Stacks 03ZC in the value universe of the site; nothing is
weakened by the move, as the condition is the same one tested against the morphisms out of a
universe-lifted Yoneda presheaf.

Stacks 0GB3 is carried by this library only in the value universe of the site, as
`AlgebraicGeometry.Space.isReduced_source_of_isSmooth`, whose proof uses the equivalence of the
every-chart and some-surjective-chart forms of smoothness. It is reproved here in the larger
value universe directly from a chart square, which is the form
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartULift_of_forall_pullback_fst` already assembles:
a reduced surjective étale atlas `V` of the target and an atlas `W` of the base change of the
morphism along it give a commuting square of étale charts, the scheme morphism `W ⟶ V` of which
is smooth, so `W` is reduced by Stacks 033B for schemes and is a reduced surjective étale atlas
of the source.

The hypotheses that `X` and `Y` be formal algebraic spaces are, as for Stacks 0GB8, not needed
once the reduction of `Y` is given: everything the argument uses about `Y` is contained in the
reduction datum. They are nevertheless part of the statement, as they are part of the source
statement, and are marked as unused.

## References

* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03ZC](https://stacks.math.columbia.edu/tag/03ZC)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0APZ](https://stacks.math.columbia.edu/tag/0APZ)
* [Stacks Project, Tag 0GB3](https://stacks.math.columbia.edu/tag/0GB3)
* [Stacks Project, Tag 0GB7](https://stacks.math.columbia.edu/tag/0GB7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Smoothness in a larger value universe -/

/-- **Stacks 03ZC, part (1)** for presheaves with values in a universe `max w u` independent of
the universe `u` of the schemes: a morphism is *smooth* when the scheme morphism underlying
every commuting square of étale scheme charts of it is smooth. -/
abbrev IsSmoothULift {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G) : Prop :=
  HoldsOnEveryEtaleChartULift.{w} B S hS
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u}) f

/-- Being smooth (**Stacks 03ZC**, part (1)), as a property of morphisms in the category of
algebraic spaces over `S` with values in `Type (max w u)`. -/
abbrev smoothPropertyULift : MorphismProperty (AlgebraicSpacesULift.{w} B S hS) :=
  fun _ _ f => IsSmoothULift.{w} B S hS f.hom

/-- Smoothness is invariant under isomorphisms of algebraic spaces over `S` with values in
`Type (max w u)`. -/
instance smoothPropertyULift_respectsIso :
    (smoothPropertyULift.{w} B S hS).RespectsIso := by
  refine MorphismProperty.RespectsIso.mk _ (fun e f hf => ?_) (fun e f hf => ?_)
  · have := AlgebraicGeometry.Space.isIso_hom_of_iso B S hS e
    exact holdsOnEveryEtaleChartULift_precomp B S hS _ e.hom.hom f.hom hf
  · have := AlgebraicGeometry.Space.isIso_hom_of_iso B S hS e
    exact holdsOnEveryEtaleChartULift_postcomp B S hS _ e.hom.hom f.hom hf

/-! ### Relative properties along the universe-lifted Yoneda embedding -/

/-! ### Stacks 0GB3 in a larger value universe -/

/-- **Stacks 0GB3, reducedness of the source**, for presheaves with values in a universe
`max w u` independent of the universe `u` of the schemes: a smooth morphism of algebraic spaces
over `S` whose target is reduced has reduced source.

A reduced surjective étale atlas `V` of the target and an atlas `W` of the base change of the
morphism along it form a commuting square of étale charts, so the scheme morphism `W ⟶ V` is
smooth and `W` is reduced by Stacks 033B; it is a reduced surjective étale atlas of the
source. -/
@[stacks 0GB3 "reducedness of the source, in an arbitrary value universe"]
theorem hasEtaleLocalPropertyULift_isReduced_of_isSmoothULift
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    (hF : IsAlgebraicSpaceULift.{w} B S hS F) (hG : IsAlgebraicSpaceULift.{w} B S hS G)
    (f : F ⟶ G) (hf : IsSmoothULift.{w} B S hS f)
    (hred : HasEtaleLocalPropertyULift.{w} B S hS G (fun T : Scheme.{u} ↦ IsReduced T)) :
    HasEtaleLocalPropertyULift.{w} B S hS F (fun T : Scheme.{u} ↦ IsReduced T) := by
  obtain ⟨V, b, hbSurj, hbEtale, hVred⟩ := hred
  have hT : IsAlgebraicSpaceULift.{w} B S hS (pullback b f) :=
    isAlgebraicSpaceULift_pullback B S hS b f
      (isAlgebraicSpaceULift_uliftYoneda.{w} B S hS V) hF hG
  obtain ⟨W, β, hβSurj, hβEtale⟩ := hT.exists_atlas
  obtain ⟨h, hh⟩ : ∃ h : W ⟶ V, (uliftYoneda.{w}).map h = β ≫ pullback.fst b f :=
    ⟨(uliftYoneda.{w}).preimage (β ≫ pullback.fst b f), by simp⟩
  have hsq : IsPullback (pullback.fst b f) (pullback.snd b f) b f :=
    IsPullback.of_hasPullback b f
  have haEtale := Space.relative_comp B S hS hβEtale
    (AlgebraicGeometry.Space.relative_of_isPullback B S hS hsq.flip hbEtale)
  have haSurj := Space.relative_comp B S hS hβSurj
    (AlgebraicGeometry.Space.relative_of_isPullback B S hS hsq.flip hbSurj)
  have _ : AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map h) :=
    hf W V (β ≫ pullback.snd b f) b h haEtale hbEtale
      (by rw [hh, Category.assoc, Category.assoc, hsq.w])
  have _ : IsReduced ((BigFppfOver.toScheme B S hS).obj V) := hVred
  exact ⟨W, β ≫ pullback.snd b f, haSurj, haEtale,
    isReduced_of_smooth ((BigFppfOver.toScheme B S hS).map h)⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A cartesian square of fppf sheaves on the big fppf site of `S` is cartesian on the
underlying presheaves, the forgetful functor to presheaves preserving limits. -/
private theorem isPullback_sheafHom {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f) :
    IsPullback p.hom q.hom g.hom f.hom :=
  sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-! ### Two reductions of one sheaf -/

/-- Any two reductions of an fppf sheaf on the big fppf site of `S` are isomorphic over it:
a morphism between them commuting with the inclusions is an isomorphism, because the
composites both ways are the unique factorizations of the inclusions through themselves. -/
theorem IsReduction.isIso_of_comp_eq {X X₁ X₂ : FppfSheaf B S hS} {i₁ : X₁ ⟶ X} {i₂ : X₂ ⟶ X}
    (h₁ : IsReduction B S hS X X₁ i₁) (h₂ : IsReduction B S hS X X₂ i₂)
    {g : X₁ ⟶ X₂} (hg : g ≫ i₂ = i₁) : IsIso g := by
  obtain ⟨k, hk, -⟩ := h₁.universal X₂ h₂.algebraic h₂.reduced i₂
  have key : ∀ {Z j} (_ : IsReduction B S hS X Z j) (e : Z ⟶ Z), e ≫ j = j → e = 𝟙 Z :=
    fun hZ e he => by
      obtain ⟨_, -, hu⟩ := hZ.universal _ hZ.algebraic hZ.reduced _
      exact (hu e he).trans (hu _ (Category.id_comp _)).symm
  exact ⟨k, key h₁ _ (by rw [Category.assoc, hk, hg]), key h₂ _ (by rw [Category.assoc, hg, hk])⟩

/-! ### Stacks 0GB7 -/

/-- **Stacks 0GB7.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S` which is
representable by algebraic spaces and smooth, let `iY : Yred ⟶ Y` be a reduction of `Y` and let
`P` with projections `fst : P ⟶ X` and `snd : P ⟶ Yred` be a fibre product `X ×_Y Yred`. Then
`P`, with the projection `fst`, is a reduction of `X`: this is the assertion
`X_red = X ×_Y Y_red`.

`P` is an algebraic space by Stacks 03XY, reduced by Stacks 0GB3 applied to the base change
`snd` of `f`, and `fst` is a representable thickening because `iY` is; a morphism to `X` from a
reduced algebraic space factors uniquely through `P` because its composite with `f` factors
uniquely through `Yred`. -/
@[stacks 0GB7 "the fibre product X ×_Y Y_red is a reduction of X; read against given \
reductions and a given fibre product rather than chosen ones, exactly as for Stacks 0GB8. \
Stacks 0AIN supplies the reductions"]
theorem isReduction_pullback_reduction_of_smooth {X Y Yred P : FppfSheaf B S hS}
    (_hX : IsFormalAlgebraicSpace B S hS X) (_hY : IsFormalAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsmooth : Space.HasPropertyULift.{u + 1} B S hS
      (Space.smoothPropertyULift.{u + 1} B S hS) f.hom hf)
    {iY : Yred ⟶ Y} (hiY : IsReduction B S hS Y Yred iY)
    {fst : P ⟶ X} {snd : P ⟶ Yred} (sq : IsPullback fst snd f iY) :
    IsReduction B S hS X P fst := by
  have sqh : IsPullback fst.hom snd.hom f.hom iY.hom := isPullback_sheafHom B S hS sq
  have hPalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS P.obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS sqh.flip.isoPullback.symm
      (Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS f.hom iY.hom hf
        hiY.algebraic)
  have hthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS fst.hom :=
    AlgebraicGeometry.Space.relative_of_isPullback B S hS sqh hiY.isRepresentableThickening
  have hsndProp := Space.hasPropertyULift_of_isPullback B S hS sqh hf hsmooth
  have hsndSmooth : Space.IsSmoothULift.{u + 1} B S hS snd.hom :=
    Space.holdsOnEveryEtaleChartULift_of_forall_pullback_fst B S hS
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
      AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget hPalg hiY.algebraic snd.hom
      (fun U ξ => hsndProp U ξ)
  refine { algebraic := hPalg
           reduced := Space.hasEtaleLocalPropertyULift_isReduced_of_isSmoothULift B S hS
             hPalg hiY.algebraic snd.hom hsndSmooth hiY.reduced
           representable := hthick.rep
           thickening := hthick.property
           universal := ?_ }
  intro U hUalg hUred g
  obtain ⟨m, hm, hmuniq⟩ := hiY.universal U hUalg hUred (g ≫ f)
  refine ⟨sq.lift g m hm.symm, sq.lift_fst _ _ _, fun l hl => ?_⟩
  have hlsnd : l ≫ snd = m :=
    hmuniq _ (by beta_reduce at hl ⊢; rw [Category.assoc, ← sq.w, ← Category.assoc, hl])
  exact sq.hom_ext (by rw [hl, sq.lift_fst]) (by rw [hlsnd, sq.lift_snd])

/-- **Stacks 0GB7.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over `S` which is
representable by algebraic spaces and smooth, let `iX : Xred ⟶ X` and `iY : Yred ⟶ Y` be
reductions and let `P` with projections `fst` and `snd` be a fibre product `X ×_Y Yred`. Then
every morphism `Xred ⟶ P` over `X` is an isomorphism: the canonical comparison morphism
`X_red ⟶ X ×_Y Y_red` identifies the two.

`P` is a reduction of `X` by
`AlgebraicGeometry.FormalSpace.isReduction_pullback_reduction_of_smooth`, and two reductions of
`X` are isomorphic over `X`. -/
@[stacks 0GB7 "the comparison morphism X_red ⟶ X ×_Y Y_red over X is an isomorphism; read \
against given reductions and a given fibre product rather than chosen ones, exactly as for \
Stacks 0GB8. Stacks 0AIN supplies the reductions"]
theorem isIso_of_isReduction_of_isPullback_of_smooth {X Y Xred Yred P : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hsmooth : Space.HasPropertyULift.{u + 1} B S hS
      (Space.smoothPropertyULift.{u + 1} B S hS) f.hom hf)
    {iX : Xred ⟶ X} (hiX : IsReduction B S hS X Xred iX)
    {iY : Yred ⟶ Y} (hiY : IsReduction B S hS Y Yred iY)
    {fst : P ⟶ X} {snd : P ⟶ Yred} (sq : IsPullback fst snd f iY)
    {g : Xred ⟶ P} (hg : g ≫ fst = iX) : IsIso g :=
  IsReduction.isIso_of_comp_eq B S hS hiX
    (isReduction_pullback_reduction_of_smooth B S hS hX hY hf hsmooth hiY sq) hg

end AlgebraicGeometry.FormalSpace

end
