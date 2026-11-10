module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms

/-!
# Relative normalization of algebraic spaces

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`. The *normalization of
`X` in `Y`* is the relative spectrum over `X` of the integral closure of `𝒪_X` in `f_* 𝒪_Y`,
and it comes with a factorization `f = ν ∘ f'` in which `ν : X' ⟶ X` is integral. Tag 0823
shows that this factorization is characterized by integrality of `ν` together with a universal
property: every factorization of `f` through an integral morphism to `X` receives a unique
compatible morphism from `X'`. That characterization is the predicate
`AlgebraicGeometry.Space.IsRelativeNormalization` used throughout this file.

Two properties of the normalization are proved. It is reduced as soon as `Y` is, and it turns
a disjoint union of sources into a disjoint union of normalizations.

## Main definitions

* `AlgebraicGeometry.Space.IsRelativeNormalization` says that a factorization of a morphism of
  algebraic spaces through an integral morphism is the normalization of the target in the
  source, in the sense of the characterization of Tag 0823.

## Main results

* `AlgebraicGeometry.Space.IsRelativeNormalization.hasEtaleLocalProperty_isReduced` is
  Tag 0AYF: the normalization of `X` in a reduced algebraic space `Y` is reduced. The
  companion `…_of_reducedClosedSubspace` in the same namespace runs the argument against a
  presented reduction instead of the constructed one.
* `AlgebraicGeometry.Space.isRelativeNormalization_coproduct` is Tag 0824: a coproduct of the
  normalizations of `X` in the summands of a disjoint union `Y` is the normalization of `X`
  in `Y`.

## Implementation notes

**Why the characterization and not the construction.** The relative spectrum of a
quasi-coherent algebra on an algebraic space is not available in this library, and neither is
quasi-coherence of the integral closure of `𝒪_X` in `f_* 𝒪_Y`: the latter is the missing half
of Tag 0820, and the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf` record what discharging it needs.
So the normalization of `X` in `Y` cannot be constructed here. What Tag 0823 supplies instead
is a characterization of the factorization `f = ν ∘ f'` by two properties of it, and
`IsRelativeNormalization` is exactly the conjunction of those two properties. Both results
below are therefore stated for every factorization satisfying the characterization rather than
for a chosen one, which is both the only available form and the stronger statement; this is the
idiom of `AlgebraicGeometry.Space.NormalizationData` in
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization` for the absolute normalization.

**The quasi-compactness and quasi-separatedness hypotheses are absent.** The source imposes
them on `f` because they are what makes the normalization exist. Neither result below uses
them: each is an argument with the characterization, so dropping them generalises rather than
weakens. The test objects `Z` of the universal property are, as in the source, algebraic
spaces over `S`.

**Tag 0AYF and the reduction of `X'`.** The source argues that a subring of a reduced ring is
reduced. Read through the characterization the argument is instead that the inclusion of the
reduction of `X'` is an isomorphism: a morphism from a reduced algebraic space into `X'`
factors through that reduction by Tag 03JJ, so the reduction is an integral factorization of
`f` and receives the unique comparison morphism from `X'`, which is a section of the inclusion;
uniqueness in the characterization makes it a retraction as well, and the inclusion of a
subfunctor is a monomorphism, so it is an isomorphism.

The reduction `X'_red` is not hypothesised: it is `AlgebraicGeometry.Space.reduction`, the
reduced induced structure of Tag 03IQ on the whole point set of `X'`, which
`StacksFrontier.AlgebraicGeometry.Spaces.Reduction` supplies unconditionally — its closed-subspace
clause rests on effective descent for closed immersions along the surjective étale morphisms
of the site, and that descent is discharged in
`StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent`. The argument itself is
carried out for an arbitrary reduced closed subspace of `X'` whose inclusion is surjective on
points, in `…_of_reducedClosedSubspace`; Tag 0AYF is that lemma at the reduction, where all
four of its subspace hypotheses are theorems. The two forms agree because such a subspace is
unique, by `AlgebraicGeometry.Space.eq_reduction`.

**Tag 0824 at a finite index type.** The source splits `Y` into two summands. The statement
below is for a finite family, which contains the two-summand case and costs nothing: the
coproduct of the normalizations is formed by a colimit cofan of sheaves of sets, exactly as in
`AlgebraicGeometry.Space.isFinite_coproduct`, so no choice of coproduct is involved and the
empty family is included. Integrality of the induced morphism out of the coproduct is proved
by the argument of that lemma, with the finite coproduct of integral morphisms of schemes in
place of the finite coproduct of finite ones; the universal property is transported summand by
summand. The coproduct is again an algebraic space over `S` by Tag 040T,
`AlgebraicGeometry.Space.isAlgebraicSpace_finiteCoproduct`, so the conclusion is a statement
about a morphism of algebraic spaces; neither half of the proof uses that, and it is therefore
not assumed.

## References

* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0824](https://stacks.math.columbia.edu/tag/0824)
* [Stacks Project, Tag 0AYF](https://stacks.math.columbia.edu/tag/0AYF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A factorization `f = f' ≫ ν` of a morphism of algebraic spaces over `S` through an
integral morphism `ν : X' ⟶ X` exhibits `X'` as the **normalization of `X` in `Y`** when every
factorization of `f` through an integral morphism `π : Z ⟶ X` of algebraic spaces receives a
unique morphism from `X'` compatible with both factorizations. -/
def IsRelativeNormalization {Y X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ X)
    (ν : X' ⟶ X) (f' : Y ⟶ X') : Prop :=
  f' ≫ ν = f ∧ IsIntegralHom B S hS ν ∧
    ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z → ∀ π : Z ⟶ X,
      IsIntegralHom B S hS π → ∀ g : Y ⟶ Z, g ≫ π = f →
        ∃! h : X' ⟶ Z, f' ≫ h = g ∧ h ≫ π = ν

namespace IsRelativeNormalization

variable {B S hS} {Y X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : Y ⟶ X} {ν : X' ⟶ X}
    {f' : Y ⟶ X'}

/-- The normalization of `X` in `Y` factors `f`. -/
theorem fac (h : IsRelativeNormalization B S hS f ν f') : f' ≫ ν = f := h.1

/-- The normalization morphism is integral. -/
theorem isIntegralHom (h : IsRelativeNormalization B S hS f ν f') :
    IsIntegralHom B S hS ν := h.2.1

/-- Every factorization of `f` through an integral morphism of algebraic spaces to `X`
receives a unique compatible morphism from the normalization of `X` in `Y`. -/
theorem existsUnique_lift (h : IsRelativeNormalization B S hS f ν f')
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z) (π : Z ⟶ X)
    (hπ : IsIntegralHom B S hS π) (g : Y ⟶ Z) (hg : g ≫ π = f) :
    ∃! h' : X' ⟶ Z, f' ≫ h' = g ∧ h' ≫ π = ν := h.2.2 Z hZ π hπ g hg

/-- The normalization of an algebraic space `X` in a reduced algebraic space `Y` is reduced,
with the reduction of the normalization presented as a reduced closed subspace `R` of `X'`
whose inclusion is surjective on points.

This is the argument of Tag 0AYF; the tag itself is
`AlgebraicGeometry.Space.IsRelativeNormalization.hasEtaleLocalProperty_isReduced`, which is
this lemma at `AlgebraicGeometry.Space.reduction`, where every hypothesis on `R` is a theorem.
Such an `R` is in any case the reduction, by `AlgebraicGeometry.Space.eq_reduction`. -/
theorem hasEtaleLocalProperty_isReduced_of_reducedClosedSubspace
    (hnorm : IsRelativeNormalization B S hS f ν f')
    (hX' : IsAlgebraicSpace B S hS X') (hY : IsAlgebraicSpace B S hS Y)
    (hYred : HasEtaleLocalProperty B S hS Y fun T : Scheme.{u} => IsReduced T)
    (R : Subfunctor X') (hR : IsClosedSubspace B S hS R)
    (hRred : HasEtaleLocalProperty B S hS R.toFunctor fun T : Scheme.{u} => IsReduced T)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ) :
    HasEtaleLocalProperty B S hS X' fun T : Scheme.{u} => IsReduced T := by
  -- the morphism from the reduced space `Y` factors through the reduction of `X'`
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX' hY R hR
    hYred f').mpr (by rw [hfull]; exact Set.subset_univ _)
  -- so the reduction is an integral factorization of `f`, and receives a comparison morphism
  have hRint : IsIntegralHom B S hS (R.ι ≫ ν) :=
    isIntegralHom_comp B S hS
      (isIntegralHom_of_isClosedImmersion B S hS R.ι hR.2) hnorm.isIntegralHom
  obtain ⟨h, ⟨hhg, hhν⟩, -⟩ := hnorm.existsUnique_lift hR.1 (R.ι ≫ ν) hRint g
    (by rw [← Category.assoc, hg, hnorm.fac])
  -- the comparison morphism is a section of the inclusion, by uniqueness at `X'` itself
  have hsection : h ≫ R.ι = 𝟙 X' := by
    refine (hnorm.existsUnique_lift hX' ν hnorm.isIntegralHom f' hnorm.fac).unique
      ⟨?_, ?_⟩ ⟨Category.comp_id f', Category.id_comp ν⟩
    · rw [← Category.assoc, hhg, hg]
    · rw [Category.assoc]; exact hhν
  -- hence the inclusion of the reduction is an isomorphism
  have hretract : R.ι ≫ h = 𝟙 R.toFunctor := by
    refine (cancel_mono R.ι).1 ?_
    rw [Category.assoc, hsection, Category.comp_id, Category.id_comp]
  have : IsIso R.ι := ⟨h, hretract, hsection⟩
  -- a chart of the reduction is a chart of `X'`
  obtain ⟨U, a, haSurj, haEtale, haRed⟩ := hRred
  refine ⟨U, a ≫ R.ι, ?_, ?_, haRed⟩
  · refine (surjective_iff_surjective_pointsMap B S hS X' hX' U (a ≫ R.ι)).mpr ?_
    rw [pointsMap_comp]
    exact (pointsMap_surjective_of_isIso B S hS R.ι).comp
      ((surjective_iff_surjective_pointsMap B S hS R.toFunctor hR.1 U a).mp haSurj)
  · exact (isEtale_iff_presheaf_of_yoneda B S hS (a ≫ R.ι)).mp
      (isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS a).mpr haEtale)
        (isEtale_of_isIso B S hS R.ι))

/-- **Stacks 0AYF.** The normalization of an algebraic space `X` in a reduced algebraic space
`Y` is reduced.

Reducedness is asked of an algebraic space as the étale-local property of schemes of Tag 03E6.
The reduction of the normalization is constructed here rather than taken as an input: it is
`AlgebraicGeometry.Space.reduction`, the reduced induced structure of Tag 03IQ on the whole
point set of `X'`. -/
@[stacks 0AYF]
theorem hasEtaleLocalProperty_isReduced (hnorm : IsRelativeNormalization B S hS f ν f')
    (hX' : IsAlgebraicSpace B S hS X') (hY : IsAlgebraicSpace B S hS Y)
    (hYred : HasEtaleLocalProperty B S hS Y fun T : Scheme.{u} => IsReduced T) :
    HasEtaleLocalProperty B S hS X' fun T : Scheme.{u} => IsReduced T :=
  hnorm.hasEtaleLocalProperty_isReduced_of_reducedClosedSubspace hX' hY hYred
    (reduction B S hS X' hX') (isAlgebraicSpaceStructure_reduction B S hS X' hX').1
    (hasEtaleLocalProperty_isReduced_reduction B S hS X' hX')
    (range_pointsMap_ι_reduction B S hS X' hX')

end IsRelativeNormalization

/-! ### Integral morphisms out of a finite coproduct of schemes -/

/-- The coproduct over `Option ι` splits off the component at `none`. -/
private noncomputable def sigmaOptionIso {ι : Type v} [Finite ι] (Y : Option ι → Scheme.{u}) :
    (∐ Y) ≅ Y none ⨿ (∐ fun i => Y (some i)) where
  hom := Sigma.desc (Option.rec coprod.inl fun i => Sigma.ι (fun i => Y (some i)) i ≫ coprod.inr)
  inv := coprod.desc (Sigma.ι Y none) (Sigma.desc fun i => Sigma.ι Y (some i))
  hom_inv_id := by
    ext i
    cases i with
    | none => simp only [← Category.assoc, Sigma.ι_comp_desc, coprod.inl_desc, Category.comp_id]
    | some i =>
      rw [Sigma.ι_comp_desc_assoc, Category.assoc, coprod.inr_desc, Sigma.ι_comp_desc,
        Category.comp_id]
  inv_hom_id := by
    apply coprod.hom_ext
    · simp only [← Category.assoc, coprod.inl_desc, Sigma.ι_comp_desc, Category.comp_id]
    · simp only [← Category.assoc, coprod.inr_desc]
      ext i
      simp only [← Category.assoc, Sigma.ι_comp_desc, Category.comp_id]

/-- A morphism from a finite coproduct of schemes is integral when its restriction to every
component is integral.

This is the integral counterpart of `AlgebraicGeometry.isFinite_sigmaDesc`, proved by the same
induction on the index type; the binary case is Mathlib's instance for the codiagonal of two
integral morphisms. -/
private instance isIntegralHom_sigmaDesc {ι : Type v} [Finite ι] {X : Scheme.{u}}
    {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
    [∀ i, _root_.AlgebraicGeometry.IsIntegralHom (f i)] :
    _root_.AlgebraicGeometry.IsIntegralHom (Sigma.desc f) := by
  revert X Y f
  let P : Type v → Prop := fun ι => ∀ (hι : Finite ι),
    letI : Finite ι := hι
    (∀ {X : Scheme.{u}} {Y : ι → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
      [∀ i, _root_.AlgebraicGeometry.IsIntegralHom (f i)],
      _root_.AlgebraicGeometry.IsIntegralHom (Sigma.desc f))
  have hp : P ι := by
    apply Finite.induction_empty_option (P := P)
    · intro ι κ e ih hκ X Y f h
      let hι : Finite ι := @Finite.of_injective ι κ hκ e e.injective
      let E := Sigma.reindex e Y
      have hf' := ih hι (Y := Y ∘ e) (f := fun i => f (e i))
      have heq : E.inv ≫ Sigma.desc (fun i => f (e i)) = Sigma.desc f := by
        ext i
        rw [← e.apply_symm_apply i, Sigma.ι_reindex_inv_assoc, Sigma.ι_comp_desc]
        simp
      rw [← heq]
      infer_instance
    · intro hι X Y f h
      have : IsEmpty (∐ Y : Scheme.{u}) :=
        ⟨fun x => isEmptyElim ((Sigma.desc fun i => i.elim :
          (∐ Y) ⟶ (∅ : Scheme.{u})).base x)⟩
      infer_instance
    · intro ι hι ih hOption X Y f h
      have hf' := ih (Finite.of_fintype ι) (Y := fun i => Y (some i)) (f := fun i => f (some i))
      have heq : (sigmaOptionIso Y).hom ≫
          coprod.desc (f none) (Sigma.desc fun i => f (some i)) = Sigma.desc f := by
        ext i
        cases i with
        | none => simp only [← Category.assoc, sigmaOptionIso, Sigma.ι_comp_desc, coprod.inl_desc]
        | some i =>
          dsimp only [sigmaOptionIso]
          rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, coprod.inr_desc,
            Sigma.ι_comp_desc, Sigma.ι_comp_desc]
      rw [← heq]
      infer_instance
  intro X Y f h
  exact hp (inferInstance : Finite ι)

/-- Two morphisms out of the underlying presheaf of a coproduct of sheaves are equal when they
agree on every summand. -/
private theorem presheaf_hom_ext_of_isColimit_cofan {C : Type*} [Category C]
    {J : GrothendieckTopology C} {I : Type v} {F : I → Sheaf J (Type u)} {Y W : Sheaf J (Type u)}
    {ι : ∀ i, F i ⟶ Y} (hY : IsColimit (Cofan.mk Y ι)) (a b : Y.obj ⟶ W.obj)
    (h : ∀ i, (ι i).hom ≫ a = (ι i).hom ≫ b) : a = b :=
  Sheaf.hom_ext_iff.mp (Cofan.IsColimit.hom_ext hY (⟨a⟩ : Y ⟶ W) ⟨b⟩ fun i => Sheaf.hom_ext (h i))

/-! ### Disjoint unions of the source -/

/-- **Stacks 0824.** Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` whose source
is a disjoint union of finitely many algebraic spaces `Y i`, and let `X' i` be the
normalization of `X` in `Y i`. Then a disjoint union of the `X' i` is the normalization of `X`
in `Y`.

The normalization morphism is integral because its base change along a morphism from an affine
object of the site is the induced morphism out of the coproduct of the base changes of the
summands, which is a finite coproduct of integral morphisms of schemes; the universal property
is checked summand by summand, each factorization of `f` through an integral morphism
restricting to one of `f i`. -/
@[stacks 0824]
theorem isRelativeNormalization_coproduct {I : Type v} [Finite I]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : ∀ i, IsAlgebraicSpace B S hS (F i))
    (Y : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, (⟨F i, (hF i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ Y)
    (hY : IsColimit (Cofan.mk Y ι)) (f : Y.obj ⟶ X)
    (N : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hN : ∀ i, IsAlgebraicSpace B S hS (N i))
    (νs : ∀ i, N i ⟶ X) (fs : ∀ i, F i ⟶ N i)
    (hnorm : ∀ i, IsRelativeNormalization B S hS ((ι i).hom ≫ f) (νs i) (fs i))
    (P : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (κ : ∀ i, (⟨N i, (hN i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ P)
    (hP : IsColimit (Cofan.mk P κ))
    (ν : P.obj ⟶ X) (hν : ∀ i, (κ i).hom ≫ ν = νs i)
    (f' : Y.obj ⟶ P.obj) (hf' : ∀ i, (ι i).hom ≫ f' = fs i ≫ (κ i).hom) :
    IsRelativeNormalization B S hS f ν f' := by
  classical
  have := AlgebraicGeometry.BigFppfOver.hasSheafify_type B S hS
  let T := BigFppfOver.toScheme B S hS
  let J := BigFppfOver.topology B S hS
  let Xs : Sheaf J (Type u) := ⟨X, hX.isSheaf⟩
  let Ns : ∀ i, Sheaf J (Type u) := fun i => ⟨N i, (hN i).isSheaf⟩
  refine ⟨?_, ?_, ?_⟩
  · -- the coproduct morphism factors `f`
    refine presheaf_hom_ext_of_isColimit_cofan (W := Xs) hY _ _ fun i => ?_
    rw [← Category.assoc, hf' i, Category.assoc, hν i, (hnorm i).fac]
  · -- the coproduct morphism is integral
    intro U hU ξ
    choose V p a hpb hVaff hp using fun i => (hnorm i).isIntegralHom U hU ξ
    let W := BigFppfOver.sigmaObj B S hS V
    let d : W ⟶ U := Cofan.IsColimit.desc (BigFppfOver.isColimit_sigmaCofan B S hS V) p
    have hdfac : ∀ i, BigFppfOver.sigmaIncl B S hS V i ≫ d = p i := fun i =>
      Cofan.IsColimit.fac (BigFppfOver.isColimit_sigmaCofan B S hS V) p i
    have hdfacS : ∀ i, Sigma.ι (fun j => T.obj (V j)) i ≫ T.map d = T.map (p i) := by
      intro i
      have h : T.map (BigFppfOver.sigmaIncl B S hS V i) ≫ T.map d = T.map (p i) := by
        rw [← Functor.map_comp, hdfac]
      exact (congrArg (· ≫ T.map d) (BigFppfOver.toScheme_map_sigmaIncl B S hS V i)).symm.trans h
    have hd : T.map d = Sigma.desc fun i => T.map (p i) :=
      Sigma.hom_ext _ _ fun i => (hdfacS i).trans (Sigma.ι_comp_desc (fun j => T.map (p j)) i).symm
    have : ∀ i, _root_.AlgebraicGeometry.IsIntegralHom (T.map (p i)) := hp
    have hdint : _root_.AlgebraicGeometry.IsIntegralHom (T.map d) := by
      rw [hd]; exact isIntegralHom_sigmaDesc
    have hWaff : IsAffine (T.obj W) := isAffine_of_isIntegralHom (T.map d) hdint hU
    have hcolim := BigFppfOver.isColimit_yoneda_sigmaCofan B S hS V
    let as : ∀ i, J.yoneda.obj (V i) ⟶ Ns i := fun i => ⟨a i⟩
    let νsh : ∀ i, Ns i ⟶ Xs := fun i => ⟨νs i⟩
    have hsq : ∀ i, IsPullback (as i) (J.yoneda.map (p i)) (νsh i)
        (⟨ξ⟩ : J.yoneda.obj U ⟶ Xs) := fun i => isPullback_sheaf_of_hom (hpb i)
    have hwhole := (FinitaryPreExtensive.isUniversal_finiteCoproducts
      hP).isPullback_of_isColimit_right νsh (⟨ν⟩ : P ⟶ Xs) (⟨ξ⟩ : J.yoneda.obj U ⟶ Xs) as
      (fun i => J.yoneda.map (p i)) hsq hcolim (fun i => Sheaf.hom_ext (hν i))
    have hdesc : Cofan.IsColimit.desc hcolim (fun i => J.yoneda.map (p i)) = J.yoneda.map d := by
      refine Cofan.IsColimit.hom_ext hcolim _ _ fun i => ?_
      rw [Cofan.IsColimit.fac]
      simp only [Cofan.inj, Cofan.mk_ι_app]
      rw [← Functor.map_comp, hdfac]
    rw [hdesc] at hwhole
    exact ⟨W, d, (Cofan.IsColimit.desc hcolim fun i => as i ≫ κ i).hom,
      hwhole.map (sheafToPresheaf J (Type u)), hWaff, hdint⟩
  · -- the universal property, checked on each summand
    intro Z hZ π hπ g hg
    let Zs : Sheaf J (Type u) := ⟨Z, hZ.isSheaf⟩
    have hgi : ∀ i, ((ι i).hom ≫ g) ≫ π = (ι i).hom ≫ f := by
      intro i
      rw [Category.assoc, hg]
    choose h hspec huniq using fun i =>
      (hnorm i).existsUnique_lift hZ π hπ ((ι i).hom ≫ g) (hgi i)
    let hsh : P ⟶ Zs := Cofan.IsColimit.desc hP fun i => (⟨h i⟩ : Ns i ⟶ Zs)
    have hshfac : ∀ i, (κ i).hom ≫ hsh.hom = h i := by
      intro i
      exact Sheaf.hom_ext_iff.mp (Cofan.IsColimit.fac hP (fun i => (⟨h i⟩ : Ns i ⟶ Zs)) i)
    refine ⟨hsh.hom, ⟨?_, ?_⟩, ?_⟩
    · refine presheaf_hom_ext_of_isColimit_cofan (W := Zs) hY _ _ fun i => ?_
      rw [← Category.assoc, hf' i, Category.assoc, hshfac i]
      exact (hspec i).1
    · refine presheaf_hom_ext_of_isColimit_cofan (W := Xs) hP _ _ fun i => ?_
      rw [← Category.assoc, hshfac i, (hspec i).2, hν i]
    · intro k hk
      refine presheaf_hom_ext_of_isColimit_cofan (W := Zs) hP _ _ fun i => ?_
      rw [hshfac i]
      refine huniq i ((κ i).hom ≫ k) ⟨?_, ?_⟩
      · rw [← Category.assoc, ← hf' i, Category.assoc, hk.1]
      · rw [Category.assoc, hk.2, hν i]

end AlgebraicGeometry.Space

end
