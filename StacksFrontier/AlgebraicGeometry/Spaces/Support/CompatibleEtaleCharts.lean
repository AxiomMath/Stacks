module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# Compatible étale charts for a fibre product of algebraic spaces

For a pair of morphisms `f : X ⟶ Y` and `g : Y' ⟶ Y` of algebraic spaces over `S` one can
choose surjective étale scheme charts of `Y`, of `X` and of `Y'` in such a way that the
induced chart of the presheaf fibre product `X ×_Y Y'` is itself a fibre product of schemes.
Concretely: a chart `V ⟶ Y` of the target, a chart `U ⟶ X ×_Y V` of the first base change
and a chart `V' ⟶ Y' ×_Y V` of the second produce a cartesian square of schemes
`U ×_V V' ⟶ U`, `U ×_V V' ⟶ V'` over `U ⟶ V`, `V' ⟶ V`, whose top corner is a surjective
étale chart of `X ×_Y Y'`.

## Main results

* `AlgebraicGeometry.Space.exists_compatible_etale_charts` produces the four objects of the
  site, their cartesian square of underlying schemes, and the surjective étale charts of the
  four corners of the original square, together with the equations identifying the chart of
  the fibre product with the one induced by the other three.

## Implementation notes

An object of the big fppf site over `S` is a scheme over the base, and the fourth algebraic
space is the presheaf fibre product `CategoryTheory.Limits.pullback`, which is algebraic by
`AlgebraicGeometry.isAlgebraicSpace_pullback`. The equations on the chart maps identify the
maps to the two factors with the maps induced by the other charts, so the chart of the fibre
product is not an unrelated étale presentation. Cartesianity of the square of charts is
asserted after passing to schemes along `AlgebraicGeometry.BigFppfOver.toScheme`, which
preserves fibre products.

Surjectivity and étaleness of a chart are the relatively representable properties
`CategoryTheory.MorphismProperty.presheaf` of the inverse images of
`AlgebraicGeometry.Surjective` and `AlgebraicGeometry.Etale` along that functor, as in
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts`, whose stability lemmas for those inverse
images are what the proof runs on.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Compatible surjective étale scheme charts for a fibre product of algebraic spaces. -/
theorem exists_compatible_etale_charts
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    ∃ (U V U' V' : BigFppfOver B S hS)
      (p : U ⟶ V) (q : V' ⟶ V)
      (pU : U' ⟶ U) (pV' : U' ⟶ V')
      (v : yoneda.obj V ⟶ Y.1)
      (a : yoneda.obj U ⟶ pullback v f.hom)
      (b : yoneda.obj V' ⟶ pullback v g.hom)
      (c : yoneda.obj U' ⟶ pullback f.hom g.hom),
      IsPullback
        ((BigFppfOver.toScheme B S hS).map pU)
        ((BigFppfOver.toScheme B S hS).map pV')
        ((BigFppfOver.toScheme B S hS).map p)
        ((BigFppfOver.toScheme B S hS).map q) ∧
      a ≫ pullback.fst v f.hom = yoneda.map p ∧
      b ≫ pullback.fst v g.hom = yoneda.map q ∧
      c ≫ pullback.fst f.hom g.hom =
        yoneda.map pU ≫ a ≫ pullback.snd v f.hom ∧
      c ≫ pullback.snd f.hom g.hom =
        yoneda.map pV' ≫ b ≫ pullback.snd v g.hom ∧
      (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf v ∧
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf v ∧
      (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c ∧
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c := by
  let C := BigFppfOver.toScheme B S hS
  let PS := MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) C
  let PE := MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) C
  let : PS.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  let : PE.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  let : PS.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition
  let : PE.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  obtain ⟨V, v, hvS, hvE⟩ := Y.property.exists_atlas
  have hV := isAlgebraicSpace_yoneda B S hS V
  have hA := isAlgebraicSpace_pullback B S hS v f.hom hV X.property Y.property
  obtain ⟨U, a, haS, haE⟩ := hA.exists_atlas
  have hD := isAlgebraicSpace_pullback B S hS v g.hom hV Y'.property Y.property
  obtain ⟨V', b, hbS, hbE⟩ := hD.exists_atlas
  let p : U ⟶ V := yoneda.preimage (a ≫ pullback.fst v f.hom)
  let q : V' ⟶ V := yoneda.preimage (b ≫ pullback.fst v g.hom)
  have hap : a ≫ pullback.fst v f.hom = yoneda.map p := by simp [p]
  have hbq : b ≫ pullback.fst v g.hom = yoneda.map q := by simp [q]
  let U' := pullback q p
  let pU : U' ⟶ U := pullback.snd q p
  let pV' : U' ⟶ V' := pullback.fst q p
  have hChart : pU ≫ p = pV' ≫ q := by
    simpa [pU, pV', U'] using (pullback.condition (f := q) (g := p)).symm
  have hMapChart : yoneda.map pU ≫ yoneda.map p = yoneda.map pV' ≫ yoneda.map q := by
    simpa only [← Functor.map_comp] using congrArg yoneda.map hChart
  have hAY : a ≫ pullback.snd v f.hom ≫ f.hom = a ≫ pullback.fst v f.hom ≫ v := by
    rw [← pullback.condition]
  have hBY : b ≫ pullback.snd v g.hom ≫ g.hom = b ≫ pullback.fst v g.hom ≫ v := by
    rw [← pullback.condition]
  have hAMap : yoneda.map pU ≫ a ≫ pullback.fst v f.hom =
      yoneda.map pU ≫ yoneda.map p := by
    simpa [Category.assoc] using congrArg (fun z => yoneda.map pU ≫ z) hap
  have hBMap : yoneda.map pV' ≫ b ≫ pullback.fst v g.hom =
      yoneda.map pV' ≫ yoneda.map q := by
    simpa [Category.assoc] using congrArg (fun z => yoneda.map pV' ≫ z) hbq
  let x : yoneda.obj U' ⟶ X.1 := yoneda.map pU ≫ a ≫ pullback.snd v f.hom
  let y' : yoneda.obj U' ⟶ Y'.1 := yoneda.map pV' ≫ b ≫ pullback.snd v g.hom
  have hxy : x ≫ f.hom = y' ≫ g.hom := by
    calc
      x ≫ f.hom = yoneda.map pU ≫ a ≫ pullback.snd v f.hom ≫ f.hom := rfl
      _ = yoneda.map pU ≫ a ≫ pullback.fst v f.hom ≫ v := by
        simpa [Category.assoc] using congrArg (fun z => yoneda.map pU ≫ z) hAY
      _ = yoneda.map pU ≫ yoneda.map p ≫ v := by
        simpa [Category.assoc] using congrArg (fun z => z ≫ v) hAMap
      _ = yoneda.map pV' ≫ yoneda.map q ≫ v := by
        simpa [Category.assoc] using congrArg (fun z => z ≫ v) hMapChart
      _ = yoneda.map pV' ≫ b ≫ pullback.fst v g.hom ≫ v := by
        simpa [Category.assoc] using (congrArg (fun z => z ≫ v) hBMap).symm
      _ = yoneda.map pV' ≫ b ≫ pullback.snd v g.hom ≫ g.hom := by
        simpa [Category.assoc] using (congrArg (fun z => yoneda.map pV' ≫ z) hBY).symm
      _ = y' ≫ g.hom := rfl
  let c := pullback.lift x y' hxy
  have hCeqX : c ≫ pullback.fst f.hom g.hom = x := by
    simpa [c] using pullback.lift_fst x y' hxy
  have hCeqY : c ≫ pullback.snd f.hom g.hom = y' := by
    simpa [c] using pullback.lift_snd x y' hxy
  let d := b ≫ pullback.snd v g.hom
  let W := pullback (pullback.snd f.hom g.hom) d
  have hYonPB : IsPullback (yoneda.map pV') (yoneda.map pU) (yoneda.map q) (yoneda.map p) :=
    (IsPullback.of_hasPullback q p).map yoneda
  have hW : IsPullback (pullback.fst (pullback.snd f.hom g.hom) d)
      (pullback.snd (pullback.snd f.hom g.hom) d)
      (pullback.snd f.hom g.hom) d := IsPullback.of_hasPullback _ _
  let r : yoneda.obj U' ⟶ W := pullback.lift c (yoneda.map pV') (by rw [hCeqY])
  let k : W ⟶ pullback v f.hom :=
    pullback.lift
      (pullback.snd (pullback.snd f.hom g.hom) d ≫ yoneda.map q)
      (pullback.fst (pullback.snd f.hom g.hom) d ≫ pullback.fst f.hom g.hom) (by
        calc
          _ = pullback.snd (pullback.snd f.hom g.hom) d ≫
              b ≫ pullback.fst v g.hom ≫ v := by
            simpa [Category.assoc] using congrArg
              (fun z => pullback.snd (pullback.snd f.hom g.hom) d ≫ z ≫ v) hbq.symm
          _ = pullback.snd (pullback.snd f.hom g.hom) d ≫
              b ≫ pullback.snd v g.hom ≫ g.hom := by
            simpa [Category.assoc] using congrArg
              (fun z => pullback.snd (pullback.snd f.hom g.hom) d ≫ z) hBY.symm
          _ = pullback.fst (pullback.snd f.hom g.hom) d ≫
              pullback.snd f.hom g.hom ≫ g.hom := by
            simpa [d, Category.assoc] using congrArg (fun z => z ≫ g.hom) hW.w.symm
          _ = pullback.fst (pullback.snd f.hom g.hom) d ≫
              pullback.fst f.hom g.hom ≫ f.hom := by
            simpa [Category.assoc] using congrArg
              (fun z => pullback.fst (pullback.snd f.hom g.hom) d ≫ z)
                (pullback.condition (f := f.hom) (g := g.hom)).symm)
  have hrFst : r ≫ pullback.fst (pullback.snd f.hom g.hom) d = c :=
    pullback.lift_fst c (yoneda.map pV') _
  have hrSnd : r ≫ pullback.snd (pullback.snd f.hom g.hom) d = yoneda.map pV' :=
    pullback.lift_snd c (yoneda.map pV') _
  have hkFst : k ≫ pullback.fst v f.hom =
      pullback.snd (pullback.snd f.hom g.hom) d ≫ yoneda.map q :=
    pullback.lift_fst _ _ _
  have hkSnd : k ≫ pullback.snd v f.hom =
      pullback.fst (pullback.snd f.hom g.hom) d ≫ pullback.fst f.hom g.hom :=
    pullback.lift_snd _ _ _
  have hkw : yoneda.map pU ≫ a = r ≫ k := by
    apply pullback.hom_ext
    · calc
        yoneda.map pU ≫ a ≫ pullback.fst v f.hom = yoneda.map pU ≫ yoneda.map p := hAMap
        _ = yoneda.map pV' ≫ yoneda.map q := hMapChart
        _ = r ≫ k ≫ pullback.fst v f.hom := by
          simpa [Category.assoc, hkFst] using
            (congrArg (fun z => z ≫ yoneda.map q) hrSnd).symm
    · calc
        yoneda.map pU ≫ a ≫ pullback.snd v f.hom = x := rfl
        _ = c ≫ pullback.fst f.hom g.hom := hCeqX.symm
        _ = r ≫ k ≫ pullback.snd v f.hom := by
          simpa [Category.assoc, hkSnd] using
            (congrArg (fun z => z ≫ pullback.fst f.hom g.hom) hrFst).symm
  have hBaseA : IsPullback (yoneda.map pU) r a k := by
    let liftCond : ∀ s : PullbackCone a k,
        (s.snd ≫ pullback.snd (pullback.snd f.hom g.hom) d) ≫ yoneda.map q =
          s.fst ≫ yoneda.map p := fun s => by
      have h := congrArg (fun z => z ≫ pullback.fst v f.hom) s.condition
      simpa [Category.assoc, hap, hkFst] using h.symm
    let lift : ∀ s : PullbackCone a k, s.pt ⟶ yoneda.obj U' := fun s =>
      hYonPB.lift (s.snd ≫ pullback.snd (pullback.snd f.hom g.hom) d) s.fst (liftCond s)
    have liftP (s : PullbackCone a k) :
        lift s ≫ yoneda.map pV' = s.snd ≫ pullback.snd (pullback.snd f.hom g.hom) d := by
      simp [lift]
    have liftU (s : PullbackCone a k) : lift s ≫ yoneda.map pU = s.fst := by
      simp [lift]
    apply IsPullback.of_isLimit' ⟨hkw⟩
    refine PullbackCone.IsLimit.mk hkw lift (fun s => liftU s) (fun s => ?_) (fun s m h₁ h₂ => ?_)
    · apply hW.hom_ext
      · apply pullback.hom_ext
        · calc
            (lift s ≫ r) ≫ pullback.fst (pullback.snd f.hom g.hom) d ≫
                pullback.fst f.hom g.hom = lift s ≫ c ≫ pullback.fst f.hom g.hom := by
                  simpa [Category.assoc] using congrArg
                    (fun z => lift s ≫ z ≫ pullback.fst f.hom g.hom) hrFst
            _ = lift s ≫ x := by rw [hCeqX]
            _ = lift s ≫ yoneda.map pU ≫ a ≫ pullback.snd v f.hom := by
                  simp [x]
            _ = s.fst ≫ a ≫ pullback.snd v f.hom := by
                  simpa [Category.assoc] using congrArg
                    (fun z => z ≫ a ≫ pullback.snd v f.hom) (liftU s)
            _ = s.snd ≫ k ≫ pullback.snd v f.hom := by
                  simpa [Category.assoc] using congrArg
                    (fun z => z ≫ pullback.snd v f.hom) s.condition
            _ = s.snd ≫ pullback.fst (pullback.snd f.hom g.hom) d ≫
                  pullback.fst f.hom g.hom := by
                  simpa [Category.assoc] using congrArg (fun z => s.snd ≫ z) hkSnd
        · calc
            (lift s ≫ r) ≫ pullback.fst (pullback.snd f.hom g.hom) d ≫
                pullback.snd f.hom g.hom = lift s ≫ c ≫ pullback.snd f.hom g.hom := by
                  simpa [Category.assoc] using congrArg
                    (fun z => lift s ≫ z ≫ pullback.snd f.hom g.hom) hrFst
            _ = (lift s ≫ yoneda.map pV') ≫ d := by
                  rw [hCeqY]
                  simp [y', d, Category.assoc]
            _ = s.snd ≫ pullback.snd (pullback.snd f.hom g.hom) d ≫ d := by
                  simpa [Category.assoc] using congrArg (fun z => z ≫ d) (liftP s)
            _ = s.snd ≫ pullback.fst (pullback.snd f.hom g.hom) d ≫
                  pullback.snd f.hom g.hom := by
                  simpa [Category.assoc, d] using congrArg (fun z => s.snd ≫ z) hW.w.symm
      · calc
          (lift s ≫ r) ≫ pullback.snd (pullback.snd f.hom g.hom) d =
              lift s ≫ yoneda.map pV' := by
                simpa [Category.assoc] using congrArg (fun z => lift s ≫ z) hrSnd
          _ = s.snd ≫ pullback.snd (pullback.snd f.hom g.hom) d := liftP s
    · apply hYonPB.hom_ext
      · calc
          m ≫ yoneda.map pV' =
              m ≫ r ≫ pullback.snd (pullback.snd f.hom g.hom) d := by
                simpa [Category.assoc] using congrArg (fun z => m ≫ z) hrSnd.symm
          _ = s.snd ≫ pullback.snd (pullback.snd f.hom g.hom) d := by
                simpa [Category.assoc] using congrArg
                  (fun z => z ≫ pullback.snd (pullback.snd f.hom g.hom) d) h₂
          _ = lift s ≫ yoneda.map pV' := (liftP s).symm
      · calc
          m ≫ yoneda.map pU = s.fst := h₁
          _ = lift s ≫ yoneda.map pU := (liftU s).symm
  have key : ∀ P : MorphismProperty (BigFppfOver B S hS), P.IsStableUnderBaseChange →
      P.IsStableUnderComposition → P.presheaf v → P.presheaf a → P.presheaf b → P.presheaf c := by
    intro P _ _ hv ha hb
    have hbc : P.presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange P
    have : P.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition P
    have hd : P.presheaf d :=
      MorphismProperty.comp_mem P.presheaf _ _ hb
        (hbc.of_isPullback (IsPullback.of_hasPullback v g.hom) hv)
    rw [← hrFst]
    exact MorphismProperty.comp_mem P.presheaf _ _ (hbc.of_isPullback hBaseA ha)
      (hbc.of_isPullback hW.flip hd)
  exact ⟨U, V, U', V', p, q, pU, pV', v, a, b, c,
    ((IsPullback.of_hasPullback q p).flip).map C,
    hap, hbq, hCeqX, hCeqY, hvS, hvE, haS, haE, hbS, hbE,
    key PS inferInstance inferInstance hvS haS hbS,
    key PE inferInstance inferInstance hvE haE hbE⟩

end AlgebraicGeometry.Space

end
