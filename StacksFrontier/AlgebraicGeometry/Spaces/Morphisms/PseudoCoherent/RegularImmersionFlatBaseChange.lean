module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RegularImmersion

/-!
# Flat base change of a regular immersion of algebraic spaces

Let `i : Z ⟶ X` be a Koszul-regular, `H₁`-regular or quasi-regular immersion of algebraic
spaces over `S` in the sense of Stacks 06BN, and let `g : X' ⟶ X` be a flat morphism of
algebraic spaces over `S` in the sense of Stacks 03ML. Then the base change
`i' : Z ×_X X' ⟶ X'` of `i` along `g` is again a Koszul-regular, `H₁`-regular or
quasi-regular immersion. This is **Stacks 09RX**, all three of its clauses.

## Main results

* `AlgebraicGeometry.Space.forall_etale_chart_of_isPullback_of_isFlat`: the chart condition of
  Stacks 06BM is stable under flat base change, for any property of scheme morphisms which is
  étale local on the target and transfers along flat base change of schemes.
* `AlgebraicGeometry.Space.isKoszulRegularImmersion_pullback_snd_of_isFlat`: **Stacks 09RX**,
  the Koszul-regular clause.
* `AlgebraicGeometry.Space.isH1RegularImmersion_pullback_snd_of_isFlat`: **Stacks 09RX**, the
  `H₁`-regular clause.
* `AlgebraicGeometry.Space.isQuasiRegularImmersion_pullback_snd_of_isFlat`: **Stacks 09RX**,
  the quasi-regular clause.

Each clause is proved first for an arbitrary cartesian square
(`AlgebraicGeometry.Space.isKoszulRegularImmersion_of_isPullback_of_isFlat` and its two
companions) and then specialised to the fibre product taken in the presheaf category, exactly
as the scheme-level statements of Stacks 067P are arranged in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/RegularIdealSheaf/FlatBaseChange.lean`.

## Implementation notes

The three predicates of Stacks 06BN read the corresponding scheme condition on the represented
base change of `i` to every étale *scheme* chart of the target, so the whole content of the
tag is the transport of that condition from the charts of `X` to the charts of `X'`. The
obstruction is that a chart `q' : V' ⟶ X'` of the target of `i'` composes with `g` to a
morphism `V' ⟶ X` which is flat but not étale, so it is not itself a chart of `X` and the
hypothesis cannot be read at it. The repair is to cover it: pulling a surjective étale atlas
`q : V ⟶ X` back along `q' ≫ g` produces a scheme `W` with

* `π : W ⟶ V'` surjective and étale, being a base change of the atlas, so that `W` is again an
  étale chart of `X'` and the regularity condition on the base change to `V'` may be read on
  `W` instead, the three conditions being étale local on the target by Stacks 0694;
* `r : W ⟶ V` flat, because `W ⟶ X'` is an étale chart and `q` is an étale chart, so the
  square they form with `r` and `g` is one of the commuting squares of étale charts that the
  definition of flatness in Stacks 03ML quantifies over.

The base change of `i'` to `W` is then simultaneously a base change of `i` along `q' ≫ g` and
a base change along the flat `r` of the base change of `i` to the étale chart `V`, where the
hypothesis applies; the scheme-level flat base change of Stacks 067P closes it. The two
descriptions of that base change are compared by the usual isomorphism between any two
cartesian squares over a common cospan, which is where
`CategoryTheory.IsPullback.isoPullback` is used; nothing in the argument depends on the
particular choice of represented fibre product made by
`CategoryTheory.Functor.relativelyRepresentable`.

Only the target `X` is required to be an algebraic space, since the atlas of `X` is the only
one taken; the source statement has all four of `Z`, `X`, `Z'`, `X'` algebraic spaces, so this
is weaker in hypothesis and therefore stronger. Representability of `i'` is not a hypothesis
either: it follows from representability of `i`, which is part of each predicate of Stacks
06BN, because relative representability is stable under base change.

The geometric work is done once, for an arbitrary property `P` of scheme morphisms which is
étale local on the target and transfers along a flat base change of schemes, in
`AlgebraicGeometry.Space.forall_etale_chart_of_isPullback_of_isFlat`; the three clauses then
differ only in which of the three theorems of Stacks 067P and which of the three theorems of
Stacks 0694 is supplied to it.

## References

* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
* [Stacks Project, Tag 063J](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Tag 067P](https://stacks.math.columbia.edu/tag/067P)
* [Stacks Project, Tag 0694](https://stacks.math.columbia.edu/tag/0694)
* [Stacks Project, Tag 06BM](https://stacks.math.columbia.edu/tag/06BM)
* [Stacks Project, Tag 06BN](https://stacks.math.columbia.edu/tag/06BN)
* [Stacks Project, Tag 09RX](https://stacks.math.columbia.edu/tag/09RX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

/-- Pullbacks of presheaves on the big fppf site of `S`, supplied directly: since Lean v4.35.0
instance search times out finding them through the functor-category limit instances. -/
local instance (priority := high) hasLimit_cospan_presheaf_RegularImmersionFlatBaseChange (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/-- **The chart condition of Stacks 06BM is stable under flat base change.** Let `P` be a
property of morphisms of schemes which is étale local on the target and transfers along a flat
base change of schemes. Let `i : Z ⟶ X` be a relatively representable morphism of presheaves
on the big fppf site of `S` with `X` an algebraic space over `S`, and suppose the represented
base change of `i` to every étale scheme chart of `X` has `P`. Then for every flat
`g : X' ⟶ X` and every cartesian square exhibiting `i' : Z' ⟶ X'` as a base change of `i`
along `g`, the represented base change of `i'` to every étale scheme chart of `X'` has `P`.

The conclusion is stated for the canonical represented base change `hi'.snd q'`; since `P`
respects isomorphisms, the same holds for any other choice. -/
theorem forall_etale_chart_of_isPullback_of_isFlat (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (P : MorphismProperty Scheme.{u})
    (hPloc : P.IsLocalAtTarget Scheme.etalePrecoverage)
    (hPflat : ∀ {Z₀ X₀ Z₁ X₁ : Scheme.{u}} {i₀ : Z₀ ⟶ X₀} {i₁ : Z₁ ⟶ X₁} {c₀ : Z₁ ⟶ Z₀}
      {b : X₁ ⟶ X₀}, _root_.AlgebraicGeometry.Flat b → IsPullback i₁ c₀ b i₀ → P i₀ → P i₁)
    {Z X X' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {i : Z ⟶ X} {g : X' ⟶ X} {i' : Z' ⟶ X'} {c : Z' ⟶ Z}
    (H : IsPullback i' c g i) (hg : IsFlat B S hS g)
    (hi : yoneda.relativelyRepresentable i)
    (hall : ∀ (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ X),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q →
      P ((BigFppfOver.toScheme B S hS).map (hi.snd q)))
    (hi' : yoneda.relativelyRepresentable i') (V' : BigFppfOver B S hS)
    (q' : yoneda.obj V' ⟶ X')
    (hq' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q') :
    P ((BigFppfOver.toScheme B S hS).map (hi'.snd q')) := by
  have := hPloc
  have : HasLimitsOfShape WalkingCospan B.Schemes := inferInstance
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  let T := BigFppfOver.toScheme B S hS
  -- a surjective étale atlas of the target of `i`
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hX.exists_atlas
  -- pulled back along `q' ≫ g` it gives a chart `W` of `X'` lying over the chart `V` of `X`
  obtain ⟨W, π, fstW, hWpb⟩ := hqEtale.1 (q' ≫ g)
  obtain ⟨r, rfl⟩ := yoneda.map_surjective fstW
  have hπEtale : Etale (T.map π) := hqEtale.2 (q' ≫ g) (yoneda.map r) π hWpb
  have hπSurj : Surjective (T.map π) := hqSurj.2 (q' ≫ g) (yoneda.map r) π hWpb
  have haEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf (yoneda.map π ≫ q') :=
    etale_comp_of_scheme B S hS π q' hπEtale hq'
  have hcomm : yoneda.map r ≫ q = (yoneda.map π ≫ q') ≫ g :=
    hWpb.w.trans (Category.assoc _ _ _).symm
  -- `r` is the morphism of schemes underlying a commuting square of étale charts of `g`
  have hrFlat : Flat (T.map r) :=
    hg W V (yoneda.map π ≫ q') q r haEtale hqEtale hcomm
  -- the two descriptions of the base change of `i` to `W`
  have hLeft : IsPullback (yoneda.map (pullback.fst (hi.snd q) r) ≫ hi.fst q)
      (yoneda.map (pullback.snd (hi.snd q) r)) i (yoneda.map r ≫ q) :=
    (Functor.map_isPullback yoneda (IsPullback.of_hasPullback (hi.snd q) r)).paste_horiz
      (hi.isPullback q)
  have hRight : IsPullback
      ((yoneda.map (pullback.fst (hi'.snd q') π) ≫ hi'.fst q') ≫ c)
      (yoneda.map (pullback.snd (hi'.snd q') π)) i (yoneda.map r ≫ q) := by
    rw [hcomm]
    exact ((Functor.map_isPullback yoneda
      (IsPullback.of_hasPullback (hi'.snd q') π)).paste_horiz (hi'.isPullback q')).paste_horiz
      H.flip
  -- the hypothesis at the chart `V`, pulled back along the flat `r`
  have hβ : P (T.map (pullback.snd (hi.snd q) r)) :=
    hPflat hrFlat
      (Functor.map_isPullback T (IsPullback.of_hasPullback (hi.snd q) r)).flip
      (hall V q hqEtale)
  -- the comparison isomorphism between the two descriptions
  let eW := hLeft.isoPullback.trans hRight.isoPullback.symm
  have heW : eW.hom ≫ yoneda.map (pullback.snd (hi'.snd q') π) =
      yoneda.map (pullback.snd (hi.snd q) r) := by
    simp only [eW, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      hRight.isoPullback_inv_snd, hLeft.isoPullback_hom_snd]
  let e := yoneda.preimageIso eW
  have he : e.hom ≫ pullback.snd (hi'.snd q') π = pullback.snd (hi.snd q) r := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
    exact heW
  let eSch := Functor.mapIso T e
  have heSch : eSch.hom ≫ T.map (pullback.snd (hi'.snd q') π) =
      T.map (pullback.snd (hi.snd q) r) := by
    simpa [eSch, Functor.map_comp] using congrArg T.map he
  have hβ' : P (T.map (pullback.snd (hi'.snd q') π)) := by
    apply (P.cancel_left_of_respectsIso eSch.hom _).mp
    rw [heSch]
    exact hβ
  -- and étale locality on the target along the surjective étale `π`
  have hA'Sch : IsPullback (T.map (pullback.fst (hi'.snd q') π))
      (T.map (pullback.snd (hi'.snd q') π)) (T.map (hi'.snd q')) (T.map π) :=
    Functor.map_isPullback T (IsPullback.of_hasPullback (hi'.snd q') π)
  have hCanon : P (pullback.snd (T.map (hi'.snd q')) (T.map π)) := by
    apply (P.cancel_left_of_respectsIso hA'Sch.isoPullback.hom _).mp
    simpa only [hA'Sch.isoPullback_hom_snd] using hβ'
  have hCover : Presieve.singleton (T.map π) ∈ Scheme.etalePrecoverage.coverings _ := by
    rw [Scheme.etalePrecoverage]
    exact (Scheme.singleton_mem_precoverage_iff (@Etale) (T.map π)).2 ⟨hπSurj.surj, hπEtale⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hCover
  intro U₀ g₀ _ hg₀
  cases hg₀
  exact hCanon

/-! ### The Koszul-regular clause -/

/-- **Stacks 09RX, the Koszul-regular clause, for an arbitrary cartesian square.** Let
`i : Z ⟶ X` be a Koszul-regular immersion of algebraic spaces over `S`, let `g : X' ⟶ X` be
flat and let `i' : Z' ⟶ X'` be a base change of `i` along `g`. Then `i'` is a Koszul-regular
immersion. -/
theorem isKoszulRegularImmersion_of_isPullback_of_isFlat (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {Z X X' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {i : Z ⟶ X} {g : X' ⟶ X} {i' : Z' ⟶ X'} {c : Z' ⟶ Z}
    (H : IsPullback i' c g i) (hg : IsFlat B S hS g)
    (hi : IsKoszulRegularImmersion B S hS i) :
    IsKoszulRegularImmersion B S hS i' := by
  obtain ⟨hiRep, hall⟩ := hi
  have hi'Rep : yoneda.relativelyRepresentable i' :=
    MorphismProperty.of_isPullback (P := yoneda.relativelyRepresentable) H.flip hiRep
  refine ⟨hi'Rep, fun V' q' hq' ↦ ?_⟩
  refine forall_etale_chart_of_isPullback_of_isFlat B S hS
    (fun _ _ f ↦ ∃ hf : _root_.AlgebraicGeometry.IsImmersion f,
      @_root_.Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion _ _ f hf)
    _root_.AlgebraicGeometry.isLocalAtTarget_koszulRegularImmersion_etale.{u}
    (fun hb Hsq hP ↦ ?_) hX H hg hiRep hall hi'Rep V' q' hq'
  obtain ⟨hii, hK⟩ := hP
  have hij := MorphismProperty.of_isPullback
    (P := (@_root_.AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u})) Hsq.flip hii
  exact ⟨hij, _root_.Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_isPullback_of_flat
    Hsq hK⟩

/-- **Stacks 09RX, the Koszul-regular clause.** The base change `Z ×_X X' ⟶ X'` of a
Koszul-regular immersion `i : Z ⟶ X` of algebraic spaces over `S` along a flat morphism
`g : X' ⟶ X` is a Koszul-regular immersion. -/
@[stacks 09RX "koszul"]
theorem isKoszulRegularImmersion_pullback_snd_of_isFlat (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Z X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X) (g : X' ⟶ X) (hg : IsFlat B S hS g)
    (hi : IsKoszulRegularImmersion B S hS i) :
    IsKoszulRegularImmersion B S hS (pullback.snd i g) :=
  isKoszulRegularImmersion_of_isPullback_of_isFlat B S hS hX
    (IsPullback.of_hasPullback i g).flip hg hi

/-! ### The `H₁`-regular clause -/

/-- **Stacks 09RX, the `H₁`-regular clause, for an arbitrary cartesian square.** Let
`i : Z ⟶ X` be an `H₁`-regular immersion of algebraic spaces over `S`, let `g : X' ⟶ X` be
flat and let `i' : Z' ⟶ X'` be a base change of `i` along `g`. Then `i'` is an `H₁`-regular
immersion. -/
theorem isH1RegularImmersion_of_isPullback_of_isFlat (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    {Z X X' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {i : Z ⟶ X} {g : X' ⟶ X} {i' : Z' ⟶ X'} {c : Z' ⟶ Z}
    (H : IsPullback i' c g i) (hg : IsFlat B S hS g)
    (hi : IsH1RegularImmersion B S hS i) :
    IsH1RegularImmersion B S hS i' := by
  obtain ⟨hiRep, hall⟩ := hi
  have hi'Rep : yoneda.relativelyRepresentable i' :=
    MorphismProperty.of_isPullback (P := yoneda.relativelyRepresentable) H.flip hiRep
  refine ⟨hi'Rep, fun V' q' hq' ↦ ?_⟩
  refine forall_etale_chart_of_isPullback_of_isFlat B S hS
    (fun _ _ f ↦ ∃ hf : _root_.AlgebraicGeometry.IsImmersion f,
      @_root_.Stacks.AlgebraicGeometry.RegularIdealSheaf.IsH1RegularImmersion _ _ f hf)
    _root_.AlgebraicGeometry.isLocalAtTarget_h1RegularImmersion_etale.{u}
    (fun hb Hsq hP ↦ ?_) hX H hg hiRep hall hi'Rep V' q' hq'
  obtain ⟨hii, hK⟩ := hP
  have hij := MorphismProperty.of_isPullback
    (P := (@_root_.AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u})) Hsq.flip hii
  exact ⟨hij, _root_.Stacks.AlgebraicGeometry.isH1RegularImmersion_of_isPullback_of_flat
    Hsq hK⟩

/-- **Stacks 09RX, the `H₁`-regular clause.** The base change `Z ×_X X' ⟶ X'` of an
`H₁`-regular immersion `i : Z ⟶ X` of algebraic spaces over `S` along a flat morphism
`g : X' ⟶ X` is an `H₁`-regular immersion. -/
@[stacks 09RX "h1"]
theorem isH1RegularImmersion_pullback_snd_of_isFlat (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Z X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X) (g : X' ⟶ X) (hg : IsFlat B S hS g)
    (hi : IsH1RegularImmersion B S hS i) :
    IsH1RegularImmersion B S hS (pullback.snd i g) :=
  isH1RegularImmersion_of_isPullback_of_isFlat B S hS hX
    (IsPullback.of_hasPullback i g).flip hg hi

/-! ### The quasi-regular clause -/

/-- **Stacks 09RX, the quasi-regular clause, for an arbitrary cartesian square.** Let
`i : Z ⟶ X` be a quasi-regular immersion of algebraic spaces over `S`, let `g : X' ⟶ X` be
flat and let `i' : Z' ⟶ X'` be a base change of `i` along `g`. Then `i'` is a quasi-regular
immersion. -/
@[ega "IV 19.1.5" "more general"]
theorem isQuasiRegularImmersion_of_isPullback_of_isFlat (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    {Z X X' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {i : Z ⟶ X} {g : X' ⟶ X} {i' : Z' ⟶ X'} {c : Z' ⟶ Z}
    (H : IsPullback i' c g i) (hg : IsFlat B S hS g)
    (hi : IsQuasiRegularImmersion B S hS i) :
    IsQuasiRegularImmersion B S hS i' := by
  obtain ⟨hiRep, hall⟩ := hi
  have hi'Rep : yoneda.relativelyRepresentable i' :=
    MorphismProperty.of_isPullback (P := yoneda.relativelyRepresentable) H.flip hiRep
  refine ⟨hi'Rep, fun V' q' hq' ↦ ?_⟩
  refine forall_etale_chart_of_isPullback_of_isFlat B S hS
    (fun _ _ f ↦ ∃ hf : _root_.AlgebraicGeometry.IsImmersion f,
      @_root_.Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion _ _ f hf)
    _root_.AlgebraicGeometry.isLocalAtTarget_quasiRegularImmersion_etale.{u}
    (fun hb Hsq hP ↦ ?_) hX H hg hiRep hall hi'Rep V' q' hq'
  obtain ⟨hii, hK⟩ := hP
  have hij := MorphismProperty.of_isPullback
    (P := (@_root_.AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u})) Hsq.flip hii
  exact ⟨hij, _root_.Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_isPullback_of_flat
    Hsq hK⟩

/-- **Stacks 09RX, the quasi-regular clause.** The base change `Z ×_X X' ⟶ X'` of a
quasi-regular immersion `i : Z ⟶ X` of algebraic spaces over `S` along a flat morphism
`g : X' ⟶ X` is a quasi-regular immersion. -/
@[stacks 09RX "quasi"]
theorem isQuasiRegularImmersion_pullback_snd_of_isFlat (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Z X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X) (g : X' ⟶ X) (hg : IsFlat B S hS g)
    (hi : IsQuasiRegularImmersion B S hS i) :
    IsQuasiRegularImmersion B S hS (pullback.snd i g) :=
  isQuasiRegularImmersion_of_isPullback_of_isFlat B S hS hX
    (IsPullback.of_hasPullback i g).flip hg hi

end AlgebraicGeometry.Space

end
