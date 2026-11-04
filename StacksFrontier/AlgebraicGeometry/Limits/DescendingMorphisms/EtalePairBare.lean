module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtalePair
public import StacksFrontier.AlgebraicGeometry.Limits.StageFactorizationOfLimitMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The descent of an étale pair over a cofiltered limit, in terms of bare pullbacks

`AlgebraicGeometry.exists_stage_etale_pair` states the descent step of tag 0GDX in the over
categories of the stages, so that base change is `CategoryTheory.Over.pullback` and the two
schemes `X₀` and `Y₀` over the stage are objects of an over category. This file restates it for
two morphisms `fX : X ⟶ S` and `gY : Y ⟶ T` of schemes and the *bare* fibre products
`pullback fX m` and `pullback gY n` over the vertex of the limit cone, which is the form in which
the step is consumed.

## Main results

* `AlgebraicGeometry.exists_stage_etale_pair_bare`: a pair of étale morphisms from a scheme `Usch`
  of finite presentation over the limit into `pullback fX m` and `pullback gY n` is, after moving
  to a later stage `j'`, the base change of a pair of étale morphisms into
  `pullback fX (p.app j')` and `pullback gY (D.map e ≫ tj)`.

## Implementation notes

The translation instantiates `AlgebraicGeometry.exists_stage_etale_pair` at the stage `j` with
`X₀ := Over.mk (pullback.snd fX (p.app j))` and `Y₀ := Over.mk (pullback.snd gY tj)` and with
`U := Over.mk pU`, so that the base change of `X₀` along a morphism `g'` of bases has underlying
scheme `pullback (pullback.snd fX (p.app j)) g'`. Every comparison that is then needed is an
instance of `CategoryTheory.Limits.pullbackLeftPullbackSndIso` followed by
`CategoryTheory.Limits.pullback.congrHom`, which transports the pullback along an equality of the
two legs; `AlgebraicGeometry.pullbackSndPullbackIso` packages that composite together with its
four characterising identities, and nothing in the proof has to rewrite inside a type.

The three equalities of legs used are `hm j` at the limit, the naturality
`AlgebraicGeometry.map_comp_natTrans_app` of the structure morphisms at the later stage, and `hn`
for the `T`-side at the limit; on the `T`-side at the later stage the leg is already
`D.map e ≫ tj`, so there the comparison is `pullbackLeftPullbackSndIso` itself.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The base change of `pullback f g` along `g' : W ⟶ Y`, identified with the fibre product of `f`
and a morphism `h : W ⟶ Z` presented as the composite `g' ≫ g`. -/
def pullbackSndPullbackIso {W X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    (h : W ⟶ Z) (hh : g' ≫ g = h) :
    pullback (pullback.snd f g) g' ≅ pullback f h :=
  pullbackLeftPullbackSndIso f g g' ≪≫ pullback.congrHom rfl hh

/-- The comparison isomorphism of `AlgebraicGeometry.pullbackSndPullbackIso` read through the
first projections. -/
@[reassoc]
lemma pullbackSndPullbackIso_hom_fst {W X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    (h : W ⟶ Z) (hh : g' ≫ g = h) :
    (pullbackSndPullbackIso f g g' h hh).hom ≫ pullback.fst f h =
      pullback.fst (pullback.snd f g) g' ≫ pullback.fst f g := by
  simp [pullbackSndPullbackIso, pullback.map, pullback.lift_fst]

/-- The comparison isomorphism of `AlgebraicGeometry.pullbackSndPullbackIso` read through the
second projections. -/
@[reassoc]
lemma pullbackSndPullbackIso_hom_snd {W X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    (h : W ⟶ Z) (hh : g' ≫ g = h) :
    (pullbackSndPullbackIso f g g' h hh).hom ≫ pullback.snd f h =
      pullback.snd (pullback.snd f g) g' := by
  simp [pullbackSndPullbackIso, pullback.map, pullback.lift_snd]

/-- The inverse of the comparison isomorphism of `AlgebraicGeometry.pullbackSndPullbackIso` read
through the first projections. -/
@[reassoc]
lemma pullbackSndPullbackIso_inv_fst {W X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    (h : W ⟶ Z) (hh : g' ≫ g = h) :
    (pullbackSndPullbackIso f g g' h hh).inv ≫
        pullback.fst (pullback.snd f g) g' ≫ pullback.fst f g = pullback.fst f h := by
  rw [← pullbackSndPullbackIso_hom_fst f g g' h hh, Iso.inv_hom_id_assoc]

/-- The inverse of the comparison isomorphism of `AlgebraicGeometry.pullbackSndPullbackIso` read
through the second projections. -/
@[reassoc]
lemma pullbackSndPullbackIso_inv_snd {W X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    (h : W ⟶ Z) (hh : g' ≫ g = h) :
    (pullbackSndPullbackIso f g g' h hh).inv ≫ pullback.snd (pullback.snd f g) g' =
      pullback.snd f h := by
  rw [← pullbackSndPullbackIso_hom_snd f g g' h hh, Iso.inv_hom_id_assoc]

/-- The base change of a morphism of finite presentation is of finite presentation, read on the
second projection of the fibre product. -/
@[ega "IV 1.6.2"]
lemma finitePresentation_pullback_snd {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : FinitePresentation f) : FinitePresentation (pullback.snd f g) := by
  have : LocallyOfFinitePresentation f := hf.1
  have : QuasiCompact f := hf.2.1
  have : QuasiSeparated f := hf.2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- A morphism into the bare fibre product `pullback f h`, compatible with the structure morphism
to `W`, read as a morphism of `Over W` into the base change of `Over.mk (pullback.snd f g)`
along `g'`. -/
def overHomMkPullbackSnd {A W X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    (h : W ⟶ Z) (hh : g' ≫ g = h) (pA : A ⟶ W) (al : A ⟶ pullback f h)
    (hal : al ≫ pullback.snd f h = pA) :
    (Over.mk pA : Over W) ⟶ (Over.pullback g').obj (Over.mk (pullback.snd f g)) :=
  Over.homMk (al ≫ (pullbackSndPullbackIso f g g' h hh).inv) (by
    simp only [Over.pullback_obj_hom, Over.mk_hom, Category.assoc,
      pullbackSndPullbackIso_inv_snd]
    exact hal)

/-- The underlying morphism of schemes of `AlgebraicGeometry.overHomMkPullbackSnd`. -/
@[simp]
lemma overHomMkPullbackSnd_left {A W X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    (h : W ⟶ Z) (hh : g' ≫ g = h) (pA : A ⟶ W) (al : A ⟶ pullback f h)
    (hal : al ≫ pullback.snd f h = pA) :
    (overHomMkPullbackSnd f g g' h hh pA al hal).left =
      al ≫ (pullbackSndPullbackIso f g g' h hh).inv := rfl

/-- Composing an étale morphism with an isomorphism gives an étale morphism. -/
private theorem etale_comp_of_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g]
    (hf : Etale f) : Etale (f ≫ g) := by
  have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @Etale) _ _).mpr hf

/-- **A pair of étale morphisms into two bare fibre products over a cofiltered limit of affine
schemes descends to a finite stage.**

Let `S` receive a compatible family of morphisms `p` from a cofiltered diagram `D` of affine
schemes with limit cone `c`, inducing `m : c.pt ⟶ S`, and let `n : c.pt ⟶ T` factor as
`c.π.app j ≫ tj` through the stage `j`. Given `fX : X ⟶ S` and `gY : Y ⟶ T` of finite
presentation and a scheme `Usch` of finite presentation over `c.pt` with two étale morphisms into
`pullback fX m` and `pullback gY n` compatible with the structure morphism to `c.pt`, the whole
configuration is the base change of one over a stage `j'` lying over `j`.

This is `AlgebraicGeometry.exists_stage_etale_pair` restated with bare pullbacks in place of
iterated base changes in over categories. -/
theorem exists_stage_etale_pair_bare
    {S T X Y : Scheme.{u}} (fX : X ⟶ S) (gY : Y ⟶ T)
    (hfp : FinitePresentation fX) (hgp : FinitePresentation gY)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]
    (m : c.pt ⟶ S) (hm : ∀ i, c.π.app i ≫ p.app i = m)
    (j : I) (tj : D.obj j ⟶ T) (n : c.pt ⟶ T) (hn : c.π.app j ≫ tj = n)
    (Usch : Scheme.{u}) (pU : Usch ⟶ c.pt) (hUfp : FinitePresentation pU)
    (al : Usch ⟶ pullback fX m) (be : Usch ⟶ pullback gY n)
    (hal : al ≫ pullback.snd fX m = pU) (hbe : be ≫ pullback.snd gY n = pU)
    (hale : Etale al) (hbee : Etale be) :
    ∃ (j' : I) (e : j' ⟶ j) (U' : Scheme.{u}) (pU' : U' ⟶ D.obj j')
      (a' : U' ⟶ pullback fX (p.app j')) (b' : U' ⟶ pullback gY (D.map e ≫ tj)),
      Etale a' ∧ Etale b' ∧
      a' ≫ pullback.snd fX (p.app j') = pU' ∧
      b' ≫ pullback.snd gY (D.map e ≫ tj) = pU' ∧
      ∃ psi : Usch ⟶ U',
        psi ≫ a' ≫ pullback.fst fX (p.app j') = al ≫ pullback.fst fX m ∧
        psi ≫ b' ≫ pullback.fst gY (D.map e ≫ tj) = be ≫ pullback.fst gY n ∧
        psi ≫ pU' = pU ≫ c.π.app j' := by
  have hX₀ : FinitePresentation (Over.mk (pullback.snd fX (p.app j))).hom :=
    finitePresentation_pullback_snd fX (p.app j) hfp
  have hY₀ : FinitePresentation (Over.mk (pullback.snd gY tj)).hom :=
    finitePresentation_pullback_snd gY tj hgp
  obtain ⟨j', e, U', a', b', ha'E, hb'E, psi, hpsia, hpsib, hpsiU⟩ :=
    exists_stage_etale_pair D c hc j (Over.mk (pullback.snd fX (p.app j)))
      (Over.mk (pullback.snd gY tj)) hX₀ hY₀ (Over.mk pU) hUfp
      (overHomMkPullbackSnd fX (p.app j) (c.π.app j) m (hm j) pU al hal)
      (overHomMkPullbackSnd gY tj (c.π.app j) n hn pU be hbe)
      (etale_comp_of_isIso _ _ hale) (etale_comp_of_isIso _ _ hbee)
  simp only [Over.mk_hom] at hpsia hpsib hpsiU
  refine ⟨j', e, U'.left, U'.hom,
    a'.left ≫ (pullbackSndPullbackIso fX (p.app j) (D.map e) (p.app j')
      (map_comp_natTrans_app D p e)).hom,
    b'.left ≫ (pullbackSndPullbackIso gY tj (D.map e) (D.map e ≫ tj) rfl).hom,
    etale_comp_of_isIso _ _ ha'E, etale_comp_of_isIso _ _ hb'E, ?_, ?_,
    psi, ?_, ?_, hpsiU⟩
  · rw [Category.assoc, pullbackSndPullbackIso_hom_snd]
    simpa using Over.w a'
  · rw [Category.assoc, pullbackSndPullbackIso_hom_snd]
    simpa using Over.w b'
  · rw [Category.assoc, pullbackSndPullbackIso_hom_fst, reassoc_of% hpsia,
      overHomMkPullbackSnd_left, Category.assoc, pullbackSndPullbackIso_inv_fst]
  · rw [Category.assoc, pullbackSndPullbackIso_hom_fst, reassoc_of% hpsib,
      overHomMkPullbackSnd_left, Category.assoc, pullbackSndPullbackIso_inv_fst]

end AlgebraicGeometry

end
