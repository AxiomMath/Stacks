module

public import StacksFrontier.AlgebraicGeometry.Spaces.ArtinAxiomsAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSitePresheafCanonicalModel
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorFpqcSheaf
public import StacksFrontier.CategoryTheory.MorphismProperty.RelativeDiagonalEqualizerLocus
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonSituation
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.RimSchlessingerOfThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPushoutBijective
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushout
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditionalSupplement
public import StacksFrontier.Deformation.Artin.FunctorAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts

/-!
# Quot via Artin's axioms (Stacks 0CZW)

Let `S` be a Noetherian scheme all of whose local rings are G-rings, `X` an algebraic space over
`S` with structure morphism `f : X ⟶ S` of finite presentation and separated, and `F` a finitely
presented quasi-coherent `𝒪_X`-module flat over `S`. Remark 0CZW sketches how Artin's axioms,
checked one by one through the conditions of Stacks 07Y1, show that `Quot_{F/X/S}` is an
algebraic space locally of finite presentation over `S`. This file sets up the situation with
base `B = S`, through the canonical model in the universe of the site of the Quot presheaf, and
proves the conditions which do not involve deformation theory.

## Main definitions

* `AlgebraicGeometry.Space.quotOverBase`: the situation of the remark, as the situation of
  Stacks 09TR with base `S`.
* `AlgebraicGeometry.Space.quotOverBasePresheaf`: `Quot_{F/X/S}`, the canonical model of the
  Quot presheaf in the universe of the site.

## Main results

* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_diag_quotOverBase`: the diagonal is
  representable (by closed immersions).
* `AlgebraicGeometry.Space.isSheaf_quotOverBase`: axiom [0].
* `AlgebraicGeometry.Space.satisfiesRS_quotOverBase`: axiom [2], condition (RS).
* `AlgebraicGeometry.Space.QuotSitePresheafModel.exists_stage_eq`: the injectivity half of the
  limit preservation axiom [1].

## References

* [Stacks Project, Tag 0CZW](https://stacks.math.columbia.edu/tag/0CZW)
* [Stacks Project, Tag 07Y1](https://stacks.math.columbia.edu/tag/07Y1)
* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 08IW](https://stacks.math.columbia.edu/tag/08IW)
* [Stacks Project, Tag 0DM2](https://stacks.math.columbia.edu/tag/0DM2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The comparison functor of a category fibred in sets -/

section FibredSets

open Deformation.Artin Functor

/-- **The comparison functor of `𝒮_F` at a square is an equivalence as soon as `F` glues
uniquely across it**: the fibres of `𝒮_F` are discrete, so the comparison functor
`𝒮_{F, Y'} ⥤ 𝒮_{F, Y} ×_{𝒮_{F, X}} 𝒮_{F, X'}` is the map `F(Y') ⟶ F(Y) ×_{F(X)} F(X')` up to
the identification of objects of fibres with elements. This is the argument of
`Deformation.Artin.satisfiesRS_fibredCategory_of_satisfiesRSFunctor`, at a single square. -/
theorem isEquivalence_fiberSquareComparison_fibredCategory
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y') (j' : Y ⟶ Y') (w : i ≫ i' = j ≫ j')
    (hRS : ∀ (a : F.obj (op Y)) (b : F.obj (op X')), F.map j.op a = F.map i.op b →
      ∃! t : F.obj (op Y'), F.map j'.op t = a ∧ F.map i'.op t = b) :
    letI : (Stack.fibredCategory B S hS F).val.p.IsFibered :=
      (Stack.fibredCategory B S hS F).isFiberedInGroupoids.isFibered
    (fiberSquareComparison (Stack.fibredCategory B S hS F).val.p
      (Stack.fibredCategory B S hS F).val.p.chosenPullbacks j i j' i' w.symm).IsEquivalence := by
  let : (Stack.fibredCategory B S hS F).val.p.IsFibered :=
    (Stack.fibredCategory B S hS F).isFiberedInGroupoids.isFibered
  let p := (Stack.fibredCategory B S hS F).val.p
  let c := p.chosenPullbacks
  let G := fiberSquareComparison p c j i j' i' w.symm
  have hcomp : ∀ t : F.obj (op Y'), F.map j.op (F.map j'.op t) = F.map i.op (F.map i'.op t) := by
    intro t
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
      w]
  have : G.Faithful := ⟨fun {_ _} _ _ _ => Subsingleton.elim _ _⟩
  have : G.Full := by
    refine ⟨fun {z₁ z₂} φ => ?_⟩
    obtain ⟨t₁, rfl⟩ := exists_eq_fibredCategoryFiberMk z₁
    obtain ⟨t₂, rfl⟩ := exists_eq_fibredCategoryFiberMk z₂
    have h₁ : F.map j'.op t₁ = F.map j'.op t₂ := by
      have φ₁ := φ.fst
      change (c.pullbackFunctor j').obj _ ⟶ (c.pullbackFunctor j').obj _ at φ₁
      rw [pullbackFunctor_obj_eq, pullbackFunctor_obj_eq] at φ₁
      exact eq_of_fiber_hom φ₁
    have h₂ : F.map i'.op t₁ = F.map i'.op t₂ := by
      have φ₂ := φ.snd
      change (c.pullbackFunctor i').obj _ ⟶ (c.pullbackFunctor i').obj _ at φ₂
      rw [pullbackFunctor_obj_eq, pullbackFunctor_obj_eq] at φ₂
      exact eq_of_fiber_hom φ₂
    obtain ⟨t, -, ht⟩ := hRS (F.map j'.op t₁) (F.map i'.op t₁) (hcomp t₁)
    have e : t₁ = t₂ := (ht t₁ ⟨rfl, rfl⟩).trans (ht t₂ ⟨h₁.symm, h₂.symm⟩).symm
    subst e
    refine ⟨𝟙 _, ?_⟩
    apply CategoricalPullback.hom_ext <;> exact Subsingleton.elim _ _
  have : G.EssSurj := by
    refine ⟨fun P => ?_⟩
    obtain ⟨x, y, e⟩ := P
    obtain ⟨a, rfl⟩ := exists_eq_fibredCategoryFiberMk x
    obtain ⟨b, rfl⟩ := exists_eq_fibredCategoryFiberMk y
    have hab : F.map j.op a = F.map i.op b := by
      have e' := e.hom
      rw [pullbackFunctor_obj_eq, pullbackFunctor_obj_eq] at e'
      exact eq_of_fiber_hom e'
    obtain ⟨t, ⟨ht₁, ht₂⟩, -⟩ := hRS a b hab
    refine ⟨fibredCategoryFiberMk t, ⟨CategoricalPullback.mkIso
      (eqToIso (by
        show (c.pullbackFunctor j').obj _ = _
        rw [pullbackFunctor_obj_eq, ht₁]))
      (eqToIso (by
        show (c.pullbackFunctor i').obj _ = _
        rw [pullbackFunctor_obj_eq, ht₂]))
      (Subsingleton.elim _ _)⟩⟩
  exact { }

end FibredSets

/-! ### Quotients over a base with a unique point over every scheme -/

namespace QuotSituation

variable (D : QuotSituation B S hS) (ι : ∀ T : BigFppfOver B S hS,
    (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
  [hY : ∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]

/-- A scheme of the site as a test scheme over the base, through the unique morphism to it. -/
abbrev testOver (T : BigFppfOver B S hS) : SchemesOver D.Y := CostructuredArrow.mk (ι T)

/-- A morphism of schemes of the site as a morphism of test schemes over the base. -/
def testHom {T T' : BigFppfOver B S hS} (g : T ⟶ T') : D.testOver ι T ⟶ D.testOver ι T' :=
  CostructuredArrow.homMk g (Subsingleton.elim _ _)

/-- The underlying morphism of `testHom g` is `g`. -/
@[simp]
theorem testHom_left {T T' : BigFppfOver B S hS} (g : T ⟶ T') : (D.testHom ι g).left = g := rfl

/-- A quotient over the test scheme of a scheme of the site, as a section of the Quot
presheaf. -/
def ofQuot (T : BigFppfOver B S hS) (K : D.properlySupportedQuotients (D.testOver ι T)) :
    QuotFamilyOver D T :=
  ⟨ι T, K.1, K.2⟩

omit hY in
/-- The map `ofQuot` is injective. -/
theorem ofQuot_injective (T : BigFppfOver B S hS) : Function.Injective (D.ofQuot ι T) := by
  intro K K' h
  simp only [ofQuot, QuotFamilyOver.mk.injEq, heq_eq_eq, true_and] at h
  exact Subtype.ext h

/-- When every scheme of the site has a unique morphism to the base, the map `ofQuot` is
surjective. -/
theorem ofQuot_surjective (T : BigFppfOver B S hS) : Function.Surjective (D.ofQuot ι T) := by
  rintro ⟨b, K, hK⟩
  obtain rfl : b = ι T := Subsingleton.elim _ _
  exact ⟨⟨K, hK⟩, rfl⟩

omit hY in
private theorem quotientPullback_homMk_heq {T : SchemesOver D.Y} {V : BigFppfOver B S hS}
    (g : V ⟶ T.left) {b b' : (schemeSpaceFunctor B S hS).obj V ⟶ D.Y}
    (hb : (schemeSpaceFunctor B S hS).map g ≫ T.hom = b)
    (hb' : (schemeSpaceFunctor B S hS).map g ≫ T.hom = b')
    (K : Subobject (D.baseChangeModule T)) :
    D.quotientPullback (CostructuredArrow.homMk g hb : CostructuredArrow.mk b ⟶ T) K ≍
      D.quotientPullback (CostructuredArrow.homMk g hb' : CostructuredArrow.mk b' ⟶ T) K := by
  subst hb hb'
  rfl

/-- Base change of a quotient over a scheme of the site is pullback along the induced morphism of
test schemes. -/
theorem baseChange_ofQuot {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    (K : D.properlySupportedQuotients (D.testOver ι T)) :
    (D.ofQuot ι T K).baseChange g = D.ofQuot ι T'
      ⟨D.quotientPullback (D.testHom ι g) K.1,
        D.quotientPullback_mem_properlySupportedQuotients _ K.1 K.2⟩ := by
  refine QuotFamilyOver.ext (Subsingleton.elim _ _) ?_
  show D.quotientPullback (QuotFamilyOver.restrict g (ι T)) K.1 ≍
    D.quotientPullback (D.testHom ι g) K.1
  exact D.quotientPullback_homMk_heq (T := D.testOver ι T) g rfl (Subsingleton.elim _ _) K.1

include ι in
/-- **Quotients glue uniquely over a pushout along a thickening**, for the Quot presheaf over a
base with a unique point over every scheme of the site. For a pushout `Y' = Y ⨿_X X'` of schemes
of the site along a thickening `X ⟶ X'` and an affine morphism `X ⟶ Y`, two quotients over `Y`
and `X'` with the same restriction to `X` are the restrictions of exactly one quotient over `Y'`.
This is Stacks 08IW for the finitely presented quotients, together with the descent of the
properness of the support across the thickening `Y ⟶ Y'` (the "extra work" of Remark 0CZW). -/
theorem existsUnique_quotSitePresheaf_of_isPushout {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y') (j' : Y ⟶ Y')
    (hthick : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    (haff : AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map j))
    (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map i) ((BigFppfOver.toScheme B S hS).map j)
      ((BigFppfOver.toScheme B S hS).map i') ((BigFppfOver.toScheme B S hS).map j'))
    (a : D.quotSitePresheaf.obj (op Y)) (b : D.quotSitePresheaf.obj (op X'))
    (hab : D.quotSitePresheaf.map j.op a = D.quotSitePresheaf.map i.op b) :
    ∃! t : D.quotSitePresheaf.obj (op Y'),
      D.quotSitePresheaf.map j'.op t = a ∧ D.quotSitePresheaf.map i'.op t = b := by
  obtain ⟨Ka, rfl⟩ := D.ofQuot_surjective ι Y a
  obtain ⟨Kb, rfl⟩ := D.ofQuot_surjective ι X' b
  change (D.ofQuot ι Y Ka).baseChange j = (D.ofQuot ι X' Kb).baseChange i at hab
  rw [D.baseChange_ofQuot, D.baseChange_ofQuot] at hab
  have hab' := congrArg Subtype.val (D.ofQuot_injective ι X hab)
  have hbij := D.toQuotientSituation.finitePresentationQuotientsPushoutMap_bijective
    (D.testHom ι i) (D.testHom ι j) (D.testHom ι i') (D.testHom ι j') hpo hthick haff
    D.finitePresentation.1
  have hthick' : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map j') :=
    Stacks.Pushout.isThickening_of_isPushout_of_isThickening hpo hthick
  let e : Types.PullbackObj
      (D.toQuotientSituation.finitePresentationQuotientsFunctor.map (D.testHom ι j).op)
      (D.toQuotientSituation.finitePresentationQuotientsFunctor.map (D.testHom ι i).op) :=
    ⟨(⟨Ka.1, Ka.2.1⟩, ⟨Kb.1, Kb.2.1⟩), Subtype.ext hab'⟩
  obtain ⟨K', hK'⟩ := hbij.2 e
  have h₁ : D.quotientPullback (D.testHom ι j') K'.1 = Ka.1 :=
    congrArg (fun q => q.1.1.1) hK'
  have h₂ : D.quotientPullback (D.testHom ι i') K'.1 = Kb.1 :=
    congrArg (fun q => q.1.2.1) hK'
  have hprop : K'.1 ∈ D.properlySupportedQuotients (D.testOver ι Y') := by
    refine ⟨K'.2, ?_⟩
    have := K'.2.2
    have hpb : D.IsProperlySupportedOver (D.testOver ι Y)
        ((modulePullback B S hS (D.relativeMap (D.testHom ι j'))).obj
          (D.quotientModule _ K'.1)) := by
      have h := Ka.2.2
      rw [← h₁] at h
      exact D.isProperlySupportedOver_of_iso (D.quotientPullbackCokernelIso _ _) h
    obtain ⟨hU, hpr⟩ := hpb
    obtain ⟨_, hU', hpr'⟩ :=
      (CoherentSituation.mk D.X D.Y D.f D.finitePresentation).properSupport_of_thickening
        (D.testHom ι j') hthick' (D.quotientModule _ K'.1) K'.2.1.1 inferInstance
        ⟨D.isLocallyOfFiniteType_projection _, hU, hpr⟩
    exact ⟨hU', hpr'⟩
  refine ⟨D.ofQuot ι Y' ⟨K'.1, hprop⟩, ⟨?_, ?_⟩, ?_⟩
  · show (D.ofQuot ι Y' _).baseChange j' = _
    rw [D.baseChange_ofQuot]
    exact congrArg (D.ofQuot ι Y) (Subtype.ext h₁)
  · show (D.ofQuot ι Y' _).baseChange i' = _
    rw [D.baseChange_ofQuot]
    exact congrArg (D.ofQuot ι X') (Subtype.ext h₂)
  · rintro t ⟨ht₁, ht₂⟩
    obtain ⟨Kt, rfl⟩ := D.ofQuot_surjective ι Y' t
    change (D.ofQuot ι Y' Kt).baseChange j' = _ at ht₁
    change (D.ofQuot ι Y' Kt).baseChange i' = _ at ht₂
    rw [D.baseChange_ofQuot] at ht₁ ht₂
    have e₁ := congrArg Subtype.val (D.ofQuot_injective ι Y ht₁)
    have e₂ := congrArg Subtype.val (D.ofQuot_injective ι X' ht₂)
    have key := hbij.1 (a₁ := ⟨Kt.1, Kt.2.1⟩) (a₂ := K') (by
      refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
      · exact e₁.trans h₁.symm
      · exact e₂.trans h₂.symm)
    exact congrArg (D.ofQuot ι Y') (Subtype.ext (congrArg Subtype.val key :))

include ι in
/-- **Condition (RS) for the Quot presheaf over a base with a unique point over every scheme**
(Stacks 0CZW, axiom [2]). For a pushout `Y' = Y ⨿_X X'` of spectra of Artinian local rings of
finite type over `S` along a closed immersion `X ⟶ X'`, two quotients over `Y` and `X'` with the
same restriction to `X` are the restrictions of exactly one quotient over `Y'`: the closed
immersion `X ⟶ X'` is a thickening and `X ⟶ Y` is affine, so this is
`AlgebraicGeometry.Space.QuotSituation.existsUnique_quotSitePresheaf_of_isPushout`. -/
theorem satisfiesRSFunctor_quotSitePresheaf :
    Deformation.Artin.SatisfiesRSFunctor B S hS D.quotSitePresheaf := by
  intro X X' Y Y' i j i' j' _ hX hX' hYa _ _ _ _ _ hi hpo a b hab
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj X) := hX.1
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Y) := hYa.1
  exact D.existsUnique_quotSitePresheaf_of_isPushout ι i j i' j'
    (Deformation.Artin.isThickening_of_isArtinianLocal hX hX' i hi) (isAffineHom_of_isAffine _)
    hpo a b hab

end QuotSituation

namespace QuotSitePresheafModel

variable {D : QuotSituation B S hS} (M : QuotSitePresheafModel D)

/-- Restriction in a model of the Quot presheaf is read off the Quot presheaf. -/
theorem iso_hom_app_map {a c : BigFppfOver B S hS} (t : c ⟶ a) (x : M.presheaf.obj (op a)) :
    M.iso.hom.app (op c) (ULift.up (M.presheaf.map t.op x)) =
      D.quotSitePresheaf.map t.op (M.iso.hom.app (op a) (ULift.up x)) :=
  types_congr_hom (M.iso.hom.naturality t.op) (ULift.up x)

/-- Two sections of a model of the Quot presheaf are equal exactly when the quotients they
stand for are. -/
theorem iso_hom_app_injective (a : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Injective fun x : M.presheaf.obj a => M.iso.hom.app a (ULift.up x) := by
  intro x y h
  exact congrArg ULift.down ((M.iso.app a).toEquiv.injective h)

/-- **The equalizer loci of a model of the Quot presheaf**, for a property `Q` of morphisms of the
site as in `AlgebraicGeometry.Space.QuotSituation.exists_equalizerLocus_quotSitePresheaf`, when
the base `B` of the situation has at most one point with values in every scheme of the site:
two sections of a model over `a` agree after restriction along `t : c ⟶ a` exactly when `t`
factors through a fixed monomorphism `b ⟶ a` with property `Q`. -/
theorem exists_equalizerLocus_of (Q : MorphismProperty (BigFppfOver B S hS))
    [Q.IsStableUnderComposition]
    (hQmono : ∀ {V T : BigFppfOver B S hS} (s : V ⟶ T), Q s → Mono s)
    (hQ : ∀ (T : BigFppfOver B S hS) (Z : Subfunctor (yoneda.obj T)), IsClosedSubspace B S hS Z →
      (SheafOfModules.IsFiniteTypeOnSite D.F → IsFinitePresentation B S hS Z.ι) → Q.presheaf Z.ι)
    (hY : ∀ a : BigFppfOver B S hS, Subsingleton (D.Y.1.obj (op a)))
    (a : BigFppfOver B S hS) (x y : M.presheaf.obj (op a)) :
    ∃ (b : BigFppfOver B S hS) (s : b ⟶ a), Mono s ∧ Q s ∧ ∀ (c : BigFppfOver B S hS) (t : c ⟶ a),
        M.presheaf.map t.op x = M.presheaf.map t.op y ↔ ∃ r : c ⟶ b, r ≫ s = t := by
  obtain ⟨b, s, hmono, hs, hloc⟩ := D.exists_equalizerLocus_quotSitePresheaf Q hQmono hQ a
    (M.iso.hom.app (op a) (ULift.up x)) (M.iso.hom.app (op a) (ULift.up y))
    (congrArg ULift.up (Subsingleton.elim (α := D.Y.1.obj (op a)) _ _))
  refine ⟨b, s, hmono, hs, fun c t => ?_⟩
  rw [← hloc c t, ← M.iso_hom_app_map, ← M.iso_hom_app_map]
  exact (M.iso_hom_app_injective (op c)).eq_iff.symm

/-- **The equalizer loci of a model of the Quot presheaf are closed subschemes**, when the
base `B` of the situation has at most one point with values in every scheme of the site
(for instance when it is `S` itself): two sections of a model over `a` agree after restriction
along `t : c ⟶ a` exactly when `t` factors through a fixed closed immersion `b ⟶ a`. This is
Stacks 0DM2 read on the model. -/
theorem exists_equalizerLocus (hY : ∀ a : BigFppfOver B S hS, Subsingleton (D.Y.1.obj (op a)))
    (a : BigFppfOver B S hS) (x y : M.presheaf.obj (op a)) :
    ∃ (b : BigFppfOver B S hS) (s : b ⟶ a), Mono s ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
        (BigFppfOver.toScheme B S hS)) s ∧ ∀ (c : BigFppfOver B S hS) (t : c ⟶ a),
        M.presheaf.map t.op x = M.presheaf.map t.op y ↔ ∃ r : c ⟶ b, r ≫ s = t :=
  M.exists_equalizerLocus_of
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B S hS)) (fun s hs => mono_of_isClosedImmersion_toScheme_map s hs)
    (fun _ Z hZ _ => presheaf_isClosedImmersion_of_isClosedSubspace Z hZ) hY a x y

/-- A morphism of presheaves on the site relatively representable by schemes is representable by
algebraic spaces. -/
private theorem isRepresentableByAlgebraicSpaces_of_relRep
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f) :
    IsRepresentableByAlgebraicSpaces B S hS f := by
  intro U ξ
  let e := (hf.isPullback ξ).flip.isoPullback
  exact AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable B S hS e.inv
    (Functor.relativelyRepresentable.of_isIso yoneda e.inv)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS (hf.pullback ξ))

/-- **The diagonal of a model of the Quot presheaf is representable**, by closed immersions of
schemes, when the base `B` has at most one point with values in every scheme of the site: the
pullback of `Δ : M ⟶ M × M` along a pair of sections over a scheme `a` of the site is the
equalizer locus of the pair, a closed subscheme of `a`. -/
theorem isRepresentableByAlgebraicSpaces_diag
    (hY : ∀ a : BigFppfOver B S hS, Subsingleton (D.Y.1.obj (op a))) :
    IsRepresentableByAlgebraicSpaces B S hS (diag M.presheaf) := by
  have _ : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have h := MorphismProperty.presheaf_pullbackDiagonal_of_equalizerLoci
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
      (BigFppfOver.toScheme B S hS)) (terminal.from M.presheaf)
    (fun a x y _ => M.exists_equalizerLocus hY a x y)
  have heq : diag M.presheaf =
      pullback.diagonal (terminal.from M.presheaf) ≫ (prodIsoPullback _ _).inv := by
    apply prod.hom_ext <;> simp
  apply isRepresentableByAlgebraicSpaces_of_relRep
  rw [heq]
  exact MorphismProperty.RespectsIso.postcomp _ _ _ h.rep

/-- **A model of the Quot presheaf is an fppf sheaf**: its universe lift is the Quot presheaf,
which is an fppf sheaf by Stacks 09TT, and the sheaf condition is insensitive to the lift. -/
theorem isSheaf_fppf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) M.presheaf := by
  have h := (Presheaf.isSheaf_of_iso_iff M.iso).2 D.quotSitePresheaf_isSheaf_fppf
  rw [isSheaf_iff_isSheaf_of_type] at h ⊢
  exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 h

/-- **A model of the Quot presheaf is an étale sheaf**, the étale topology being coarser than
the fppf topology. -/
theorem isSheaf_etale :
    Presheaf.IsSheaf ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)) M.presheaf :=
  M.isSheaf_fppf.of_le
    (Stacks.ComparingTopologies.over_le_over (Stack.etaleTopology_le_topology B) _)

/-- Unique gluing of quotients across a square passes from the Quot presheaf to any of its
models: the sections of a model are in bijection with the quotients, compatibly with
restriction. -/
theorem existsUnique_of_quotSitePresheaf {X X' Y Y' : BigFppfOver B S hS}
    (i : X ⟶ X') (j : X ⟶ Y) (i' : X' ⟶ Y') (j' : Y ⟶ Y')
    (h : ∀ (a : D.quotSitePresheaf.obj (op Y)) (b : D.quotSitePresheaf.obj (op X')),
      D.quotSitePresheaf.map j.op a = D.quotSitePresheaf.map i.op b →
        ∃! t : D.quotSitePresheaf.obj (op Y'),
          D.quotSitePresheaf.map j'.op t = a ∧ D.quotSitePresheaf.map i'.op t = b)
    (a : M.presheaf.obj (op Y)) (b : M.presheaf.obj (op X'))
    (hab : M.presheaf.map j.op a = M.presheaf.map i.op b) :
    ∃! t : M.presheaf.obj (op Y'), M.presheaf.map j'.op t = a ∧ M.presheaf.map i'.op t = b := by
  have hab' : D.quotSitePresheaf.map j.op (M.iso.hom.app (op Y) (ULift.up a)) =
      D.quotSitePresheaf.map i.op (M.iso.hom.app (op X') (ULift.up b)) := by
    rw [← M.iso_hom_app_map, ← M.iso_hom_app_map, hab]
  obtain ⟨t, ⟨ht₁, ht₂⟩, hu⟩ := h _ _ hab'
  obtain ⟨t₀, rfl⟩ : ∃ t₀, M.iso.hom.app (op Y') (ULift.up t₀) = t :=
    ⟨(M.iso.inv.app (op Y') t).down, by
      show (M.iso.inv ≫ M.iso.hom).app (op Y') t = t
      rw [Iso.inv_hom_id]
      rfl⟩
  refine ⟨t₀, ⟨?_, ?_⟩, fun t' ⟨h₁, h₂⟩ => ?_⟩
  · apply M.iso_hom_app_injective (op Y)
    simpa only [M.iso_hom_app_map] using ht₁
  · apply M.iso_hom_app_injective (op X')
    simpa only [M.iso_hom_app_map] using ht₂
  · apply M.iso_hom_app_injective (op Y')
    refine hu _ ⟨?_, ?_⟩
    · rw [← M.iso_hom_app_map, h₁]
    · rw [← M.iso_hom_app_map, h₂]

/-- **Condition (RS) passes from the Quot presheaf to any of its models**: the sections of a
model are in bijection with the quotients, compatibly with restriction. -/
theorem satisfiesRSFunctor (h : Deformation.Artin.SatisfiesRSFunctor B S hS D.quotSitePresheaf) :
    Deformation.Artin.SatisfiesRSFunctor B S hS M.presheaf := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hi hpo a b hab
  exact M.existsUnique_of_quotSitePresheaf i j i' j'
    (h i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hi hpo) a b hab

/-- **Two sections of a model of the Quot presheaf which agree over a limit agree at a stage**
(the injectivity half of axiom [1]), when `F` is of finite type and the base has at most one
point over every scheme of the site. For a cofiltered system of affine schemes `E_j` of the site
with limit `T` in schemes, two sections over a stage `E_i` which agree over `T` agree over some
`E_j ⟶ E_i`: their equalizer locus is a closed immersion of finite presentation `Z ⟶ E_i`
(Stacks 0DM2), through which `T ⟶ E_i` factors, so that some `E_j ⟶ E_i` factors through it
(Stacks 01ZC). -/
theorem exists_stage_eq (hY : ∀ a : BigFppfOver B S hS, Subsingleton (D.Y.1.obj (op a)))
    (hFt : SheafOfModules.IsFiniteTypeOnSite D.F)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (E : I ⥤ BigFppfOver B S hS) (c : Cone E)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (haff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (E.obj i)))
    (i : I) (x y : M.presheaf.obj (op (E.obj i)))
    (h : M.presheaf.map (c.π.app i).op x = M.presheaf.map (c.π.app i).op y) :
    ∃ (j : I) (g : j ⟶ i), M.presheaf.map (E.map g).op x = M.presheaf.map (E.map g).op y := by
  obtain ⟨b, s, -, hs, hloc⟩ := M.exists_equalizerLocus_of
    (closedImmersionFinitePresentation (B := B) (S := S) (hS := hS))
    (fun s hs => mono_of_isClosedImmersion_toScheme_map s hs.1)
    (fun _ Z hZ hfp => presheaf_closedImmersionFinitePresentation_of_isClosedSubspace Z hZ
      (hfp hFt)) hY (E.obj i) x y
  obtain ⟨r, hr⟩ := (hloc c.pt (c.π.app i)).1 h
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map s) := hs.2
  let V := BigFppfOver.toScheme B S hS
  let D' : Over i ⥤ Scheme.{u} := Over.forget i ⋙ E ⋙ V
  let t : D' ⟶ (Functor.const _).obj (V.obj (E.obj i)) :=
    { app := fun j => V.map (E.map j.hom)
      naturality := fun j k f => by
        show V.map (E.map f.left) ≫ V.map (E.map k.hom) = V.map (E.map j.hom) ≫ 𝟙 _
        rw [Category.comp_id, ← V.map_comp, ← E.map_comp, Over.w f] }
  let c' : Cone D' := (V.mapCone c).whisker (Over.forget i)
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) _).symm hc
  have : ∀ j, IsAffine (D'.obj j) := fun j => haff j.left
  have : ∀ {j k : Over i} (f : j ⟶ k), AlgebraicGeometry.IsAffineHom (D'.map f) :=
    fun _ => isAffineHom_of_isAffine _
  obtain ⟨j, g, -, hg⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D' t
    (V.map s) c' hc' (V.map r) (by
      ext j
      show V.map (c.π.app j.left) ≫ V.map (E.map j.hom) = V.map r ≫ V.map s
      rw [← V.map_comp, ← V.map_comp, c.w, hr])
  refine ⟨j.left, j.hom, (hloc (E.obj j.left) (E.map j.hom)).2 ⟨Over.homMk
    (B.inclusion.preimage g) ?_, ?_⟩⟩
  · apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_preimage, ← Over.w s, Functor.map_comp, ← Category.assoc]
    show (g ≫ V.map s) ≫ _ = _
    rw [hg]
    show B.inclusion.map (E.map j.hom).left ≫ _ = _
    rw [← Functor.map_comp, Over.w]
  · apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show B.inclusion.map (B.inclusion.preimage g ≫ s.left) = B.inclusion.map (E.map j.hom).left
    rw [Functor.map_comp, Functor.map_preimage]
    exact hg

end QuotSitePresheafModel

/-! ### The setting of Remark 0CZW -/

section OverBase

variable (B S hS)

/-- The base `S`, as an object of its big fppf site, has exactly one point over every scheme of
the site. -/
instance subsingleton_hom_terminalObj (T : BigFppfOver B S hS) :
    Subsingleton (T ⟶ BigFppfOver.terminalObj B S hS) :=
  ⟨fun f g => Over.OverMorphism.ext (by
    have hf := Over.w f
    have hg := Over.w g
    exact (Category.comp_id _).symm.trans (hf.trans (hg.symm.trans (Category.comp_id _))))⟩

/-- `S`, as an algebraic space over itself, has exactly one point over every scheme of the
site. -/
instance subsingleton_schemeSpace_terminalObj (T : BigFppfOver B S hS) :
    Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶
      schemeSpace (BigFppfOver.terminalObj B S hS)) :=
  ⟨fun f g => ObjectProperty.hom_ext _ (by
    rw [← yoneda.map_preimage f.hom, ← yoneda.map_preimage g.hom,
      Subsingleton.elim (yoneda.preimage f.hom) (yoneda.preimage g.hom)])⟩

variable {B S hS}

/-- **The situation of Remark 0CZW**: an algebraic space `X` over `S` with structure morphism
`f : X ⟶ S` of finite presentation and a quasi-coherent `𝒪_X`-module `F`, as the situation of
Stacks 09TR with base `B = S`. -/
def quotOverBase (X : AlgebraicSpaces B S hS)
    (f : X ⟶ schemeSpace (BigFppfOver.terminalObj B S hS))
    (hf : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) : QuotSituation B S hS where
  X := X
  Y := schemeSpace (BigFppfOver.terminalObj B S hS)
  f := f
  F := F
  quasicoherent := hF
  finitePresentation := hf

variable (X : AlgebraicSpaces B S hS) (f : X ⟶ schemeSpace (BigFppfOver.terminalObj B S hS))
  (hf : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
  (hF : F.IsQuasicoherentOnSite)

/-- **`Quot_{F/X/S}`**, the canonical model in the universe of the site of the Quot functor of
`F/X/S`: its sections over a scheme `T` of the site are the quotients of `F_T` which are of
finite presentation, flat over `T` and have support proper over `T`. -/
abbrev quotOverBasePresheaf : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (quotOverBase X f hf F hF).quotSitePresheafModel.presheaf

/-- Every scheme of the site has at most one morphism to the base `S` of `quotOverBase`. -/
instance (T : BigFppfOver B S hS) :
    Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ (quotOverBase X f hf F hF).Y) :=
  subsingleton_schemeSpace_terminalObj B S hS T

/-- **Stacks 0CZW, the diagonal.** In the situation of the remark, the diagonal
`Quot_{F/X/S} ⟶ Quot_{F/X/S} × Quot_{F/X/S}` is representable (by closed immersions of
schemes, hence by algebraic spaces): for two quotients `F_T ⟶ 𝒬ᵢ`, the locus of `T` over which
they agree is a closed subscheme of `T`, by Stacks 083M (the remark's own argument, through the
vanishing of `𝒦₁ ⟶ 𝒬₂` and of `𝒦₂ ⟶ 𝒬₁`). -/
@[stacks 0CZW "the diagonal of Quot_{F/X/S} is representable by algebraic spaces"]
theorem isRepresentableByAlgebraicSpaces_diag_quotOverBase :
    IsRepresentableByAlgebraicSpaces B S hS (diag (quotOverBasePresheaf X f hf F hF)) :=
  (quotOverBase X f hf F hF).quotSitePresheafModel.isRepresentableByAlgebraicSpaces_diag
    fun a => inferInstanceAs (Subsingleton (a ⟶ BigFppfOver.terminalObj B S hS))

/-- **Stacks 0CZW, axiom [0].** In the situation of the remark, `Quot_{F/X/S}` is a sheaf for
the étale topology (indeed for the fppf topology), by Stacks 09TT. -/
@[stacks 0CZW "axiom [0]: Quot_{F/X/S} is a sheaf, for the fppf and hence for the étale topology"]
theorem isSheaf_quotOverBase :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (quotOverBasePresheaf X f hf F hF) ∧
      Presheaf.IsSheaf ((AlgebraicGeometry.etaleTopology B).over (B.obj hS))
        (quotOverBasePresheaf X f hf F hF) :=
  ⟨QuotSitePresheafModel.isSheaf_fppf _, QuotSitePresheafModel.isSheaf_etale _⟩

/-- **Stacks 0CZW, axiom [2].** In the situation of the remark, `Quot_{F/X/S}` satisfies the
Rim–Schlessinger condition: for a pushout `Y' = Y ⨿_X X'` of spectra of Artinian local rings of
finite type over `S` along a closed immersion `X ⟶ X'`, the map
`Quot(Y') ⟶ Quot(Y) ×_{Quot(X)} Quot(X')` is bijective; equivalently the category fibred in sets
`𝒮_{Quot}` satisfies (RS) of Stacks 07WP. This is Stacks 08IW together with the descent of the
properness of the support across the thickening `Y ⟶ Y'`. -/
@[stacks 0CZW "axiom [2]: Quot_{F/X/S} satisfies the Rim-Schlessinger condition (RS)"]
theorem satisfiesRS_quotOverBase :
    Deformation.Artin.SatisfiesRSFunctor B S hS (quotOverBasePresheaf X f hf F hF) ∧
      Deformation.Artin.SatisfiesRS B S hS
        (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).val.p
        (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).isFiberedInGroupoids := by
  have hq : Deformation.Artin.SatisfiesRSFunctor B S hS
      (quotOverBase X f hf F hF).quotSitePresheaf :=
    (quotOverBase X f hf F hF).satisfiesRSFunctor_quotSitePresheaf
      (fun T => ObjectProperty.homMk (yoneda.map (Over.homMk T.hom (by simp))))
  have h : Deformation.Artin.SatisfiesRSFunctor B S hS (quotOverBasePresheaf X f hf F hF) :=
    (quotOverBase X f hf F hF).quotSitePresheafModel.satisfiesRSFunctor hq
  exact ⟨h, Deformation.Artin.satisfiesRS_fibredCategory_of_satisfiesRSFunctor h⟩

/-- **Condition (RS*) for `Quot_{F/X/S}`** (Stacks 07Y8), the strong form of axiom [2] which the
openness criteria of Artin's Axioms consume: for a pushout of affine schemes along a first order
thickening the comparison functor of `𝒮_{Quot}` is an equivalence. This is Stacks 08IW with the
descent of properness of the support, as for (RS). -/
theorem satisfiesRSStar_quotOverBase :
    Deformation.Artin.SatisfiesRSStar B S hS
      (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).val.p
      (Stack.fibredCategory B S hS (quotOverBasePresheaf X f hf F hF)).isFiberedInGroupoids := by
  refine Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence B S hS _ _
    fun {X₀ X₀' Y₀ Y₀'} i f₀ a b w hi hf₀ hpo => ?_
  exact isEquivalence_fiberSquareComparison_fibredCategory i f₀ a b w
    ((quotOverBase X f hf F hF).quotSitePresheafModel.existsUnique_of_quotSitePresheaf i f₀ a b
      ((quotOverBase X f hf F hF).existsUnique_quotSitePresheaf_of_isPushout
        (fun T => ObjectProperty.homMk (yoneda.map (Over.homMk T.hom (by simp)))) i f₀ a b hi
        hf₀ hpo))

end OverBase

end AlgebraicGeometry.Space
