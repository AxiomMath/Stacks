module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FlatBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionUniqueness
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper

/-!
# Essential surjectivity of finite étale restriction descends along flat covers

Let `X` be a locally Noetherian scheme and `j : U ⟶ X` an open immersion such that the local
rings of `X` at the points outside `U` have depth at least two. A finite étale cover `V ⟶ U`
then has a canonical candidate extension, the relative spectrum `Y` of `(π ≫ j)_* 𝒪_V`, which is
finite over `X` and restricts to `V` over `U` ([Stacks, Tag 0EY6]). The cover extends to a
finite étale cover of `X` exactly when `Y ⟶ X` is étale, since any finite étale extension is
isomorphic to `Y`.

Formation of `Y` commutes with flat base change. Hence if `g : X' ⟶ X` is flat, surjective and
quasi-compact, with `U' = g⁻¹(U)`, and every finite étale cover of `U'` extends to `X'`, then
`Y ×_X X' ⟶ X'` is étale, so `Y ⟶ X` is étale by fpqc descent of étaleness. This is the
descent step of the proof of [Stacks, Tag 0EYC].

## Main results

* `Stacks.FundamentalGroup.essSurj_finiteEtaleBaseChange_iff_exists_isPullback` — base change
  of finite étale covers along `j` is essentially surjective iff every finite étale cover of `U`
  is the pullback of a finite étale cover of `X`.
* `Stacks.FundamentalGroup.essSurj_finiteEtaleBaseChange_of_flat_of_surjective` — essential
  surjectivity of restriction along `j` descends along flat, surjective, quasi-compact base
  change, when the complement of `U` has depth at least two.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0EYC](https://stacks.math.columbia.edu/tag/0EYC)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MorphismProperty

namespace Stacks.FundamentalGroup

open Stacks.RelativeSpec ExtendedEtaleFold

/-- Base change of finite étale covers along `j` is essentially surjective if and only if every
finite étale cover of `U` is the pullback along `j` of a finite étale cover of `X`. -/
public theorem essSurj_finiteEtaleBaseChange_iff_exists_isPullback {U X : Scheme.{u}}
    (j : U ⟶ X) :
    (finiteEtaleBaseChange j).EssSurj ↔
      ∀ (V : Scheme.{u}) (π : V ⟶ U) [IsFinite π] [Etale π],
        ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (g : V ⟶ Y),
          IsFinite f ∧ Etale f ∧ IsPullback π g j f := by
  constructor
  · intro h V π hfinite hetale
    let cover : FiniteEtaleOver U := MorphismProperty.Over.mk ⊤ π ⟨hfinite, hetale⟩
    obtain ⟨extension, ⟨iso⟩⟩ := Functor.EssSurj.mem_essImage (finiteEtaleBaseChange j) cover
    let underlyingIso : Limits.pullback extension.hom j ≅ V :=
      (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso iso
    have hcomm : underlyingIso.hom ≫ π = Limits.pullback.snd extension.hom j :=
      MorphismProperty.Over.w iso.hom
    refine ⟨extension.left, extension.hom,
      underlyingIso.inv ≫ Limits.pullback.fst extension.hom j,
      extension.prop.1, extension.prop.2, ?_⟩
    refine IsPullback.flip (IsPullback.of_iso_pullback ⟨?_⟩ underlyingIso.symm rfl ?_)
    · rw [Category.assoc, Limits.pullback.condition, ← hcomm]
      simp
    · rw [← hcomm]
      simp
  · refine fun h => ⟨fun cover => ?_⟩
    have : IsFinite cover.hom := cover.prop.1
    have : Etale cover.hom := cover.prop.2
    obtain ⟨Y, f, g, hfinite, hetale, hcover⟩ := h cover.left cover.hom
    exact ⟨MorphismProperty.Over.mk ⊤ f ⟨hfinite, hetale⟩,
      ⟨MorphismProperty.Over.isoMk hcover.flip.isoPullback.symm
        hcover.flip.isoPullback_inv_snd⟩⟩

/-- If a finite étale cover `π` of `U` is the pullback of some finite étale cover of `X`, then
the structure morphism of its canonical extension is étale: the two extensions are isomorphic
over `X` by the uniqueness clause of [Stacks, Tag 0EY6]. -/
private theorem etale_extendedEtale_of_isPullback {U X V Y : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (π : V ⟶ U) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (f : Y ⟶ X) [IsFinite f] [Etale f] (g : V ⟶ Y) (hcover : IsPullback π g j f) :
    Etale (gluedSpectrum (extendedEtaleSituation j π hdepth)).toBase := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have hdepthY : ∀ y : Y, f y ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y) :=
    fun y hy => (hdepth (f y) hy).trans (depth_stalk_le_depth_stalk_of_flat f y)
  obtain ⟨e, he, -⟩ := extendedEtale_unique j π hdepth f g hcover hdepthY
  refine (MorphismProperty.cancel_left_of_respectsIso @Etale e.hom _).mp ?_
  rw [he.1]
  exact ‹Etale f›

/-- **Essential surjectivity of finite étale restriction descends along flat surjective
quasi-compact base change** when the complement of the open has depth at least two. -/
public theorem essSurj_finiteEtaleBaseChange_of_flat_of_surjective
    {U X U' X' : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian X']
    (j : U ⟶ X) [IsOpenImmersion j]
    (g : X' ⟶ X) [Flat g] [Surjective g] [QuasiCompact g]
    (j' : U' ⟶ X') [IsOpenImmersion j'] (gU : U' ⟶ U)
    (hj : IsPullback j' gU g j)
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hess : (finiteEtaleBaseChange j').EssSurj) :
    (finiteEtaleBaseChange j).EssSurj := by
  refine (essSurj_finiteEtaleBaseChange_iff_exists_isPullback j).mpr fun V π _ _ => ?_
  refine ⟨_, (gluedSpectrum (extendedEtaleSituation j π hdepth)).toBase,
    extendedEtaleCoverMap j π hdepth,
    isFinite_relativeSpectrum_extendedEtaleSituation j π hdepth, ?_,
    extendedEtaleCoverMap_isPullback j π hdepth⟩
  let π' := Limits.pullback.snd π gU
  let gV := Limits.pullback.fst π gU
  obtain ⟨Y', f', c', _, _, hcover⟩ :=
    (essSurj_finiteEtaleBaseChange_iff_exists_isPullback j').mp hess _ π'
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective.{u} ⊓ @Flat ⊓ @QuasiCompact)
    (extendedEtaleSpectrum_flatBaseChange j π g j' gU π' gV hj
      (IsPullback.of_hasPullback π gU).flip hdepth)
    ⟨⟨‹Surjective g›, ‹Flat g›⟩, ‹QuasiCompact g›⟩
    (etale_extendedEtale_of_isPullback j' π'
      (extendedEtaleDepth_flatBaseChange j g j' gU hj hdepth) f' c' hcover)

end Stacks.FundamentalGroup

end
