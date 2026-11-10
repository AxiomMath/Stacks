module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.GenericFibreContraction
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DenseOpenEmbeddingIntoAffineSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EmbeddingIntoAffineSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenGaloisDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Extending effective Cartier divisors from the generic fibre

Let `R` be a valuation ring with fraction field `K` and let `X` be an algebraic space smooth over
`Spec R`. Every effective Cartier divisor `D` on the generic fibre `X_K` is the base change of an
effective Cartier divisor `D'` on `X` (Stacks 0DMC).

## Main definitions

* `AlgebraicGeometry.Space.specAlgebraMapHom`: the morphism `Spec K ⟶ Spec R` of the big fppf
  site attached to an `R`-algebra `K`.

## Main results

* `AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_genericFibre_eq`: Stacks 0DMC.
* `AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_preimage_eq_of_isPullback`:
  Stacks 0DMC over an arbitrary base `S`, for a cartesian square `Y_K = Y ×_{T_R} T_K` of
  algebraic spaces over `S` whose base is the image of `Spec K ⟶ Spec R` in the big fppf site.

## Implementation notes

The base change `X_K` is the restriction of `X` along `Spec K ⟶ Spec R`,
`CategoryTheory.OverShriek.relocalizeRestrict`, as in `AlgebraicGeometry.Space.fieldBaseChange`,
and the base change of a closed subspace `D' ⊆ X` is
`CategoryTheory.OverShriek.relocalizeRestrictSubfunctor`. As in the source, `D'` is the
scheme-theoretic image of `D → X_K → X`. The morphism `X_K → X` is flat and `D → X` is
quasi-compact, so the image commutes with flat base change (Stacks 089E): restricted to `X_K` it
gives back `D`, and on each étale chart `U → X` it is the scheme-theoretic image of the
quasi-compact morphism `D ×_X U → U`, which factors through `U_K`. Effective Cartier-ness is
checked on étale charts (Stacks 083C), where it is
`Stacks.Divisors.isEffectiveCartierDivisor_of_generic_kernel`.

## References

* [Stacks Project, Tag 0DMC](https://stacks.math.columbia.edu/tag/0DMC)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct nonZeroDivisors

universe u v w

namespace AlgebraicGeometry

/-- Pullbacks of presheaves of types (instance search times out without this shortcut). -/
abbrev hasLimit_cospan_presheaf_EffectiveCartierGenericFibreExtension
    {C : Type v} [Category.{u} C] {X Y Z : Cᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  @HasLimitsOfShape.has_limit _ _ _ _
    (@functorCategoryHasLimitsOfShape _ _ _ _ _ _ inferInstance) _

/-- Small products of presheaves of types (instance search times out without this shortcut). -/
abbrev hasLimitsOfShape_discrete_presheaf_EffectiveCartierGenericFibreExtension
    {C : Type v} [Category.{u} C] (J : Type) :
    HasLimitsOfShape (Discrete J) (Cᵒᵖ ⥤ Type u) :=
  @functorCategoryHasLimitsOfShape _ _ _ _ _ _ inferInstance

end AlgebraicGeometry

namespace AlgebraicGeometry.GenericFibreExtension

attribute [local instance high] hasLimit_cospan_presheaf_EffectiveCartierGenericFibreExtension
  hasLimitsOfShape_discrete_presheaf_EffectiveCartierGenericFibreExtension

attribute [local instance] MorphismProperty.IsStableUnderBaseChange.respectsIso
  MorphismProperty.relative_isStableUnderBaseChange
  MorphismProperty.RespectsIso.inverseImage
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

/-- Extension by lower shriek of a map on the generic fibre factors through the counit. -/
private theorem relocalize_map_comp_counit
    {C : Type v} [Category.{w, v} C] {U V : C} (g : V ⟶ U)
    {G : (Over V)ᵒᵖ ⥤ Type w} {F : (Over U)ᵒᵖ ⥤ Type w}
    (φ : G ⟶ (OverShriek.relocalizeRestrict g).obj F) :
    (OverShriek.relocalizePresheafFunctor g).map φ ≫
      OverShriek.relocalizeOfRestricted g (𝟙 _) = OverShriek.relocalizeOfRestricted g φ := by
  ext W ⟨⟨ψ, s⟩, hψ⟩
  rfl

section Relocalization

open Opposite

variable {C : Type u} [Category.{v} C] {U V : C} (c : V ⟶ U)

private theorem relocalize_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor c) := by
  let : (OverShriek.presheafFunctorToOver (U := V)).IsEquivalence :=
    (OverShriek.presheafEquivalence (U := V)).isEquivalence_functor
  let : (OverShriek.fiberFunctor (𝟙 (yoneda.obj U))).IsEquivalence :=
    (OverShriek.presheafEquivalence (U := U)).isEquivalence_inverse
  have : PreservesLimitsOfShape WalkingCospan (Over.map (yoneda.map c)) := by
    have : PreservesLimitsOfShape WalkingCospan
        (Over.map (yoneda.map c) ⋙ Over.forget (yoneda.obj U)) :=
      show PreservesLimitsOfShape WalkingCospan (Over.forget (yoneda.obj V)) from inferInstance
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (Over.map (yoneda.map c)) (Over.forget (yoneda.obj U))
  dsimp [OverShriek.relocalizePresheafFunctor]
  infer_instance

private theorem sigma_yoneda_ext {T : Over V} {W : C}
    {a b : Σ ψ : W ⟶ V, Over.mk ψ ⟶ T} (h : a.2.left = b.2.left) : a = b := by
  rcases a with ⟨ψ, a⟩
  rcases b with ⟨φ, b⟩
  have hh := OverShriek.sigmaMk_eq (yoneda.obj T) (𝟙 T) a b h
  change (⟨ψ, a ≫ 𝟙 T⟩ : Σ ψ : W ⟶ V, Over.mk ψ ⟶ T) = ⟨φ, b ≫ 𝟙 T⟩ at hh
  simpa only [Category.comp_id] using hh

private def relocalizedYonedaRepresentableBy (T : Over V) :
    ((OverShriek.relocalizePresheafFunctor c).obj (yoneda.obj T)).RepresentableBy
      ((Over.map c).obj T) := by
  refine ⟨?_, ?_⟩
  · intro W
    refine
      { toFun := fun g => ⟨⟨g.left ≫ T.hom, Over.homMk g.left rfl⟩, by
          change (g.left ≫ T.hom) ≫ c = W.hom
          simpa [Category.assoc] using g.w⟩
        invFun := fun x => Over.homMk x.1.2.left (by
          change x.1.2.left ≫ (T.hom ≫ c) = W.hom
          rw [← Category.assoc]
          exact (congrArg (fun t => t ≫ c) x.1.2.w).trans x.2)
        left_inv := fun g => by ext; rfl
        right_inv := by
          intro x
          apply Subtype.ext
          apply sigma_yoneda_ext
          rfl }
  · intro W W' g a
    apply Subtype.ext
    apply sigma_yoneda_ext
    rfl

private def relocalizedYonedaIso (T : Over V) :
    yoneda.obj ((Over.map c).obj T) ≅
      (OverShriek.relocalizePresheafFunctor c).obj (yoneda.obj T) :=
  Functor.representableByEquiv (relocalizedYonedaRepresentableBy c T)

private theorem relocalizedYonedaIso_naturality {T T' : Over V} (f : T ⟶ T') :
    yoneda.map ((Over.map c).map f) ≫ (relocalizedYonedaIso c T').hom =
      (relocalizedYonedaIso c T).hom ≫
        (OverShriek.relocalizePresheafFunctor c).map (yoneda.map f) := by
  ext W g
  apply Subtype.ext
  apply sigma_yoneda_ext
  rfl

private theorem relocalize_factors {F : (Over V)ᵒᵖ ⥤ Type v}
    {T : Over U} (a : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor c).obj F) :
    ∃ (T' : Over V) (e : T ≅ (Over.map c).obj T') (b : yoneda.obj T' ⟶ F),
      a = yoneda.map e.hom ≫ (relocalizedYonedaIso c T').hom ≫
        (OverShriek.relocalizePresheafFunctor c).map b := by
  let x := yonedaEquiv a
  let T' : Over V := Over.mk x.1.1
  let e : T ≅ (Over.map c).obj T' := Over.isoMk (Iso.refl _) (by
    have hx := x.2
    change x.1.1 ≫ c = T.hom at hx
    simpa [T'] using hx)
  refine ⟨T', e, yonedaEquiv.symm x.1.2, ?_⟩
  apply yonedaEquiv.injective
  change x = _
  apply Subtype.ext
  dsimp [yonedaEquiv, e, relocalizedYonedaIso, Functor.representableByEquiv,
    relocalizedYonedaRepresentableBy]
  exact (OverShriek.sigmaMk_eq_self F x.1.2 _ (by change 𝟙 T.left ≫ 𝟙 T.left = 𝟙 T.left; simp)).symm

private theorem relocalize_source_factors {F : (Over V)ᵒᵖ ⥤ Type v}
    {T : Over U}
    (a : yoneda.obj T ⟶ (OverShriek.relocalizePresheafFunctor c).obj F) :
    ∃ ψ : T.left ⟶ V, ψ ≫ c = T.hom := by
  obtain ⟨T', e, _, _⟩ := relocalize_factors c a
  refine ⟨e.hom.left ≫ T'.hom, ?_⟩
  simpa [Over.map, Category.assoc] using e.hom.w

private theorem presheaf_relocalize (P : MorphismProperty (Over U)) [P.RespectsIso]
    {F G : (Over V)ᵒᵖ ⥤ Type v} (f : F ⟶ G)
    (hf : (P.inverseImage (Over.map c)).presheaf f) :
    P.presheaf ((OverShriek.relocalizePresheafFunctor c).map f) := by
  let L := OverShriek.relocalizePresheafFunctor c
  let J := Over.map c
  have : PreservesLimitsOfShape WalkingCospan L := relocalize_preservesPullbacks c
  apply MorphismProperty.relative.of_exists
  intro T a
  obtain ⟨T', e, b, rfl⟩ := relocalize_factors c a
  let R := hf.rep.pullback b
  let t := hf.rep.fst b
  let s := hf.rep.snd b
  let iR := relocalizedYonedaIso c R
  let iT := yoneda.mapIso e ≪≫ relocalizedYonedaIso c T'
  refine ⟨J.obj R, iR.hom ≫ L.map t, J.map s ≫ e.inv, ?_, ?_⟩
  · apply (hf.rep.isPullback b |>.map L).of_iso
      iR.symm (Iso.refl _) iT.symm (Iso.refl _)
    · simp [iR, t]
    · simp only [Iso.symm_hom, Functor.map_comp]
      change L.map (yoneda.map s) ≫ iT.inv =
        iR.inv ≫ yoneda.map (J.map s) ≫ yoneda.map e.inv
      apply (cancel_epi iR.hom).mp
      simp only [iT, Iso.trans_inv, Functor.mapIso_inv,
        Iso.hom_inv_id_assoc]
      change (relocalizedYonedaIso c R).hom ≫
        (OverShriek.relocalizePresheafFunctor c).map (yoneda.map s) ≫
        (relocalizedYonedaIso c T').inv ≫ yoneda.map e.inv = _
      rw [← reassoc_of% (relocalizedYonedaIso_naturality c s)]
      simp [J]
    · simp [L]
    · simp [iT, L, Category.assoc]
  · exact (P.cancel_right_of_respectsIso _ e.inv).mpr (hf.property_snd b)

private theorem isEtale_of_presheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    Space.IsEtale B S hS f := by
  let Q := MorphismProperty.inverseImage (@Etale.{u})
    (BigFppfOver.toScheme B S hS)
  let : MorphismProperty.IsStableUnderComposition (@Etale.{u}) := ⟨by
    intro X Y Z f g hf hg
    let := hf
    let := hg
    exact Etale.etale_comp f g⟩
  let : Q.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let : Q.presheaf.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition Q
  intro T a ha
  exact MorphismProperty.comp_mem Q.presheaf a f ha hf

private def relocalizeToBase (F : (Over V)ᵒᵖ ⥤ Type v) :
    (OverShriek.relocalizePresheafFunctor c).obj F ⟶ yoneda.obj (Over.mk c) where
  app W := ↾fun s => Over.homMk s.1.1 s.2
  naturality W W' f := by ext s; rfl

private theorem relocalizeRestriction_isPullback (F : (Over U)ᵒᵖ ⥤ Type v)
    (p : F ⟶ yoneda.obj (Over.mk (𝟙 U))) :
    IsPullback (OverShriek.relocalizeOfRestricted c (𝟙 _))
      (relocalizeToBase c ((OverShriek.relocalizeRestrict c).obj F))
      p (yoneda.map (Over.homMk c : Over.mk c ⟶ Over.mk (𝟙 U))) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext s
    apply Over.OverMorphism.ext
    have hleft (z : W.unop ⟶ Over.mk (𝟙 U)) : z.left = W.unop.hom := by
      simpa using z.w
    exact (hleft _).trans (hleft _).symm
  · rintro ⟨⟨ψ, x⟩, hx⟩ ⟨⟨φ, y⟩, hy⟩ ⟨h₁, h₂⟩
    have hψ : ψ = φ := congrArg Over.Hom.left h₂
    subst φ
    apply Subtype.ext
    apply congrArg (Sigma.mk ψ)
    have hψc : ψ ≫ c = W.unop.hom := hx
    let e : W.unop ≅ Over.mk (ψ ≫ c) :=
      Over.isoMk (Iso.refl _) (by simpa using hψc)
    exact (ConcreteCategory.bijective_of_isIso (F.map e.hom.op)).1 h₁
  · intro x y hxy
    let e : W.unop ≅ Over.mk (y.left ≫ c) :=
      Over.isoMk (Iso.refl _) (by simpa using y.w)
    refine ⟨⟨⟨y.left, F.map e.inv.op x⟩, y.w⟩, ?_, ?_⟩
    · change F.map e.hom.op (F.map e.inv.op x) = x
      simp [← Functor.map_comp_apply, ← op_comp]
    · apply Over.OverMorphism.ext
      rfl

private theorem relocalizeCounit_mono [Mono c] (F : (Over U)ᵒᵖ ⥤ Type v) :
    Mono (OverShriek.relocalizeOfRestricted c
      (𝟙 ((OverShriek.relocalizeRestrict c).obj F))) := by
  rw [NatTrans.mono_iff_mono_app]
  intro W
  apply (mono_iff_injective _).2
  rintro ⟨⟨ψ, x⟩, hx⟩ ⟨⟨φ, y⟩, hy⟩ h
  have hψ : ψ = φ := (cancel_mono c).1 (hx.trans hy.symm)
  subst φ
  apply Subtype.ext
  apply congrArg (Sigma.mk ψ)
  have hx' : ψ ≫ c = W.unop.hom := hx
  let e : W.unop ≅ Over.mk (ψ ≫ c) :=
    Over.isoMk (Iso.refl _) (by simpa using hx')
  exact (ConcreteCategory.bijective_of_isIso (F.map e.hom.op)).1 h

private theorem relocalizeRestrict_range_ofRestricted [Mono c]
    {F : (Over U)ᵒᵖ ⥤ Type v}
    (D : Subfunctor ((OverShriek.relocalizeRestrict c).obj F)) :
    Subfunctor.range ((OverShriek.relocalizeRestrict c).map
      (OverShriek.relocalizeOfRestricted c D.ι)) = D := by
  ext W x
  constructor
  · rintro ⟨⟨⟨ψ, y⟩, hψ⟩, hy⟩
    have he : ψ = W.unop.hom := (cancel_mono c).1 hψ
    subst ψ
    have hval : (y.1 : F.obj ((Over.map c).op.obj W)) = x := by
      change OverShriek.relocalizeDescend c D.ι rfl y = x at hy
      exact (OverShriek.relocalizeDescend_self c D.ι W.unop.hom y).symm.trans hy
    exact hval ▸ y.property
  · intro hx
    refine ⟨⟨⟨W.unop.hom, ⟨x, hx⟩⟩, rfl⟩, ?_⟩
    exact OverShriek.relocalizeDescend_self c D.ι W.unop.hom ⟨x, hx⟩

end Relocalization

/-- In a cartesian square over the inclusion of a subfunctor, the preimage of the subfunctor
is the range of the parallel morphism. -/
private theorem preimage_eq_range_of_isPullback
    {C : Type*} [Category C] {F G H : C ⥤ Type u}
    (D : Subfunctor H) (f : G ⟶ H) (t : F ⟶ D.toFunctor) (s : F ⟶ G)
    (h : IsPullback t s D.ι f) : D.preimage f = Subfunctor.range s := by
  ext W x
  constructor
  · intro hx
    obtain ⟨y, hy, hy'⟩ := (Types.isPullback_iff _ _ _ _).mp (h.app W) |>.2.2
      ⟨f.app W x, hx⟩ x rfl
    exact ⟨y, hy'⟩
  · rintro ⟨y, rfl⟩
    have hw := congrArg (fun α => α.app W y) h.w
    change (t.app W y).val = f.app W (s.app W y) at hw
    change f.app W (s.app W y) ∈ D.obj W
    exact hw ▸ (t.app W y).property

private theorem exists_scheme_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (D : Space.ClosedSubspaces B S hS X.1)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) :
    ∃ (I : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData)
      (V : BigFppfOver B S hS) (j : V ⟶ U)
      (e : (BigFppfOver.toScheme B S hS).obj V ≅ I.subscheme),
      (BigFppfOver.toScheme B S hS).map j = e.hom ≫ I.subschemeι ∧
      D.1.preimage a = Subfunctor.range (yoneda.map j) := by
  let T := BigFppfOver.toScheme B S hS
  let V := D.2.2.rep.pullback a
  let j := D.2.2.rep.snd a
  have : IsClosedImmersion (T.map j) := D.2.2.property_snd a
  refine ⟨(T.map j).ker, V, j, asIso (T.map j).toImage, ?_, ?_⟩
  · exact (Scheme.Hom.toImage_imageι _).symm
  · exact preimage_eq_range_of_isPullback D.1 a _ _ (D.2.2.rep.isPullback a)

/-- A factorization of maps of schemes in the chosen big site lifts uniquely
to the over category. -/
private theorem site_factors_of_scheme_factors
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T R V : BigFppfOver B S hS} (j : R ⟶ V) (g : T ⟶ V)
    (k : (BigFppfOver.toScheme B S hS).obj T ⟶
      (BigFppfOver.toScheme B S hS).obj R)
    (hk : k ≫ (BigFppfOver.toScheme B S hS).map j =
      (BigFppfOver.toScheme B S hS).map g) :
    ∃ l : T ⟶ R, l ≫ j = g := by
  let k₀ : T.left ⟶ R.left := B.inclusion.preimage k
  have hk₀ : k₀ ≫ j.left = g.left := by
    apply B.inclusion.map_injective
    rwa [B.inclusion.map_comp, show B.inclusion.map k₀ = k from
      B.inclusion.map_preimage k]
  let l : T ⟶ R := Over.homMk k₀ (by rw [← j.w, ← Category.assoc, hk₀, g.w])
  exact ⟨l, Over.OverMorphism.ext hk₀⟩

/-- Inclusion of ranges of represented maps gives the reverse inclusion of scheme kernels. -/
private theorem ker_le_of_range_yoneda_le
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T R V : BigFppfOver B S hS} (j : R ⟶ V) (g : T ⟶ V)
    (h : Subfunctor.range (yoneda.map g) ≤ Subfunctor.range (yoneda.map j)) :
    ((BigFppfOver.toScheme B S hS).map j).ker ≤ ((BigFppfOver.toScheme B S hS).map g).ker := by
  obtain ⟨l, hl⟩ := h (Opposite.op T) (show g ∈
    (Subfunctor.range (yoneda.map g)).obj (Opposite.op T) from ⟨𝟙 T, by simp⟩)
  change l ≫ j = g at hl
  rw [← hl, Functor.map_comp]
  exact Scheme.Hom.le_ker_comp _ _

/-- Inclusion of ranges into a represented closed subscheme is equivalent to
the reverse inclusion of defining ideals. -/
private theorem range_yoneda_le_iff_ker_le
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T R V : BigFppfOver B S hS} (j : R ⟶ V) (g : T ⟶ V)
    [IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] :
    Subfunctor.range (yoneda.map g) ≤ Subfunctor.range (yoneda.map j) ↔
      ((BigFppfOver.toScheme B S hS).map j).ker ≤
        ((BigFppfOver.toScheme B S hS).map g).ker := by
  refine ⟨ker_le_of_range_yoneda_le B S hS j g, fun h => ?_⟩
  let F := BigFppfOver.toScheme B S hS
  obtain ⟨l, hl⟩ := site_factors_of_scheme_factors B S hS j g
    (IsClosedImmersion.lift (F.map j) (F.map g) h)
    (IsClosedImmersion.lift_fac _ _ h)
  rw [← hl, yoneda.map_comp]
  exact Subfunctor.range_comp_le _ _

/-- Representable maps with the same functorial range have the same scheme
kernel ideal. -/
private theorem ker_eq_of_yoneda_range_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T R V : BigFppfOver B S hS} (j : R ⟶ V) (g : T ⟶ V)
    (h : Subfunctor.range (yoneda.map j) = Subfunctor.range (yoneda.map g)) :
    ((BigFppfOver.toScheme B S hS).map j).ker =
      ((BigFppfOver.toScheme B S hS).map g).ker :=
  le_antisymm (ker_le_of_range_yoneda_le B S hS j g h.symm.le)
    (ker_le_of_range_yoneda_le B S hS g j h.le)

/-- Restricting a represented space to a new base is represented by the
ordinary pullback scheme. -/
private noncomputable def relocalizeRestrictYonedaIso
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (U : BigFppfOver B S' hS') :
    (OverShriek.relocalizeRestrict g).obj (yoneda.obj U) ≅
      yoneda.obj ((Over.pullback g).obj U) := by
  let adj := Over.mapPullbackAdj g
  exact NatIso.ofComponents (fun X => Equiv.toIso (adj.homEquiv _ _))
    (fun f => by
      ext x
      exact adj.homEquiv_naturality_left _ _)

private theorem relocalizeRestrictYonedaIso_naturality
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {U V : BigFppfOver B S' hS'} (j : U ⟶ V) :
    (OverShriek.relocalizeRestrict g).map (yoneda.map j) ≫
        (relocalizeRestrictYonedaIso B S S' hS hS' g V).hom =
      (relocalizeRestrictYonedaIso B S S' hS hS' g U).hom ≫
        yoneda.map ((Over.pullback g).map j) := by
  ext X x
  exact (Over.mapPullbackAdj g).homEquiv_naturality_right _ _

private theorem mem_range_relocalizeRestrict_subfunctor
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (Z : Subfunctor F) (W : (BigFppfOver B S hS)ᵒᵖ)
    (x : ((OverShriek.relocalizeRestrict g).obj F).obj W) :
    x ∈ (Subfunctor.range ((OverShriek.relocalizeRestrict g).map Z.ι)).obj W ↔
      x ∈ Z.obj ((Over.map g).op.obj W) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem preimage_relocalizeRestrict_eq_range_pullback
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u}
    (Z : Subfunctor F) (U V : BigFppfOver B S' hS')
    (a : yoneda.obj U ⟶ F) (j : V ⟶ U)
    (hpre : Z.preimage a = Subfunctor.range (yoneda.map j)) :
    let eU := relocalizeRestrictYonedaIso B S S' hS hS' g U
    let jK := (Over.pullback g).map j
    (Subfunctor.range ((OverShriek.relocalizeRestrict g).map Z.ι)).preimage
        (eU.inv ≫ (OverShriek.relocalizeRestrict g).map a) =
      Subfunctor.range (yoneda.map jK) := by
  let R := OverShriek.relocalizeRestrict g
  let eU := relocalizeRestrictYonedaIso B S S' hS hS' g U
  let eV := relocalizeRestrictYonedaIso B S S' hS hS' g V
  let jK := (Over.pullback g).map j
  ext W x
  let t := eU.inv.app W x
  have hbase : a.app ((Over.map g).op.obj W) t ∈ Z.obj ((Over.map g).op.obj W) ↔
      t ∈ (Subfunctor.range (yoneda.map j)).obj ((Over.map g).op.obj W) := by
    change t ∈ (Z.preimage a).obj ((Over.map g).op.obj W) ↔ _
    rw [hpre]
  have hnat := congrArg (fun φ => φ.app W)
    (relocalizeRestrictYonedaIso_naturality B S S' hS hS' g j)
  constructor
  · intro hx
    change (eU.inv ≫ R.map a).app W x ∈
      (Subfunctor.range (R.map Z.ι)).obj W at hx
    rw [mem_range_relocalizeRestrict_subfunctor B S S' hS hS' g Z W] at hx
    change a.app ((Over.map g).op.obj W) t ∈ Z.obj ((Over.map g).op.obj W) at hx
    obtain ⟨y, hy⟩ := hbase.mp hx
    refine ⟨eV.hom.app W y, ?_⟩
    have hn := congrArg (fun φ => φ y) hnat
    calc
      (yoneda.map jK).app W (eV.hom.app W y) =
          eU.hom.app W ((R.map (yoneda.map j)).app W y) := hn.symm
      _ = eU.hom.app W t := congrArg (eU.hom.app W) hy
      _ = x := by simp [t]
  · rintro ⟨y, hy⟩
    let y' := eV.inv.app W y
    have hn := congrArg (fun φ => φ y') hnat
    have ht : (R.map (yoneda.map j)).app W y' = t := by
      calc
        (R.map (yoneda.map j)).app W y' =
            eU.inv.app W (eU.hom.app W ((R.map (yoneda.map j)).app W y')) := by simp
        _ = eU.inv.app W ((yoneda.map jK).app W (eV.hom.app W y')) :=
          congrArg (eU.inv.app W) hn
        _ = eU.inv.app W ((yoneda.map jK).app W y) := by simp [y']
        _ = t := congrArg (eU.inv.app W) hy
    have hx : a.app ((Over.map g).op.obj W) t ∈ Z.obj ((Over.map g).op.obj W) :=
      hbase.mpr ⟨y', ht⟩
    change (eU.inv ≫ R.map a).app W x ∈
      (Subfunctor.range (R.map Z.ι)).obj W
    rw [mem_range_relocalizeRestrict_subfunctor B S S' hS hS' g Z W]
    exact hx

/-- Pulling back a morphism in an over category gives a cartesian square
with the projections to its original source and target. -/
private theorem over_pullback_map_isPullback
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {X Y : C} (f : X ⟶ Y) {U V : Over Y} (j : V ⟶ U) :
    IsPullback (pullback.fst V.hom f) ((Over.pullback f).map j).left
      j.left (pullback.fst U.hom f) := by
  have houter : IsPullback (pullback.fst V.hom f)
      (pullback.snd V.hom f) (j.left ≫ U.hom) f := by
    rw [j.w]
    exact IsPullback.of_hasPullback V.hom f
  have hright : IsPullback (pullback.fst U.hom f)
      (pullback.snd U.hom f) U.hom f :=
    IsPullback.of_hasPullback U.hom f
  refine IsPullback.of_bot ?_ ?_ hright
  · simpa only [Over.pullback_map_left, pullback.lift_snd] using houter
  · simp only [Over.pullback_map_left, pullback.lift_fst]

/-- The ideal of a closed immersion in a cartesian square is the pulled-back
ideal of the immersion on the base. -/
private theorem ker_of_isPullback_of_isClosedImmersion
    {P X Z Y : Scheme.{u}} (iX : P ⟶ X) (p : P ⟶ Z)
    (f : X ⟶ Y) (iY : Z ⟶ Y) [IsClosedImmersion iY]
    (h : IsPullback iX p f iY) :
    iX.ker = iY.ker.comap f := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

private theorem isClosedSubspace_range
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (f : F ⟶ G) [Mono f] (hf : Space.IsClosedImmersion B S hS f) :
    Space.IsClosedSubspace B S hS (Subfunctor.range f) := by
  let e := asIso (Subfunctor.toRange f)
  refine ⟨Space.isAlgebraicSpace_of_presheafIso B S hS e hF, ?_⟩
  let P := (MorphismProperty.inverseImage (@IsClosedImmersion.{u})
    (BigFppfOver.toScheme B S hS)).presheaf
  have : P.RespectsIso := inferInstance
  have h := MorphismProperty.RespectsIso.precomp P e.inv f hf
  have he : e.inv ≫ f = (Subfunctor.range f).ι := by
    calc
      e.inv ≫ f = e.inv ≫ (Subfunctor.toRange f ≫ (Subfunctor.range f).ι) :=
        congrArg (fun k => e.inv ≫ k) (Subfunctor.toRange_ι f).symm
      _ = _ := by simp [e]
  exact he ▸ h

/-- Closure along a flat monomorphism recovers the given closed subspace on
restriction, provided its composite with the inclusion is quasi-compact. -/
private theorem schemeTheoreticImage_restrict_eq
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') [Mono g]
    (X : AlgebraicSpaces B S' hS')
    (D : Space.ClosedSubspaces B S hS
      ((OverShriek.relocalizeRestrict g).obj X.1))
    (hj : Space.IsFlat B S' hS'
      (OverShriek.relocalizeOfRestricted g
        (𝟙 ((OverShriek.relocalizeRestrict g).obj X.1))))
    (hi : Space.IsQuasiCompact B S' hS'
      (OverShriek.relocalizeOfRestricted g D.1.ι)) :
    Subfunctor.range ((OverShriek.relocalizeRestrict g).map
      (Space.schemeTheoreticImageSubfunctor B S' hS'
        (OverShriek.relocalizeOfRestricted g D.1.ι)).ι) = D.1 := by
  let L := OverShriek.relocalizePresheafFunctor g
  let R := OverShriek.relocalizeRestrict g
  let XK := R.obj X.1
  let j := OverShriek.relocalizeOfRestricted g (𝟙 XK)
  let i := OverShriek.relocalizeOfRestricted g D.1.ι
  have hjmono : Mono j := relocalizeCounit_mono g X.1
  let d := L.map D.1.ι
  have hdmono : Mono d := by
    have : PreservesLimitsOfShape WalkingCospan L := relocalize_preservesPullbacks g
    exact Functor.map_mono L D.1.ι
  have hfac : d ≫ j = i := relocalize_map_comp_counit g D.1.ι
  let hD := isAlgebraicSpace_viewOver B S S' hS hS' g
    D.1.toFunctor D.2.1
  let hXK := isAlgebraicSpace_viewOver B S S' hS hS' g XK
    (isAlgebraicSpace_relocalizeRestrict B S S' hS hS' g X.1 X.2)
  let Z := Space.schemeTheoreticImageSubfunctor B S' hS' i
  have hdclosed : Space.IsClosedImmersion B S' hS' d := by
    let : (MorphismProperty.inverseImage (@IsClosedImmersion.{u})
        (BigFppfOver.toScheme B S' hS')).RespectsIso :=
      MorphismProperty.RespectsIso.inverseImage (@IsClosedImmersion.{u}) _
    exact presheaf_relocalize g
      (MorphismProperty.inverseImage (@IsClosedImmersion.{u})
        (BigFppfOver.toScheme B S' hS')) D.1.ι D.2.2
  have hd : Space.IsClosedSubspace B S' hS' (Subfunctor.range d) :=
    isClosedSubspace_range B S' hS' hD d hdclosed
  have hpb : pullback.snd i j = pullback.fst i j ≫ d := by
    apply (cancel_mono j).1
    rw [Category.assoc, hfac, pullback.condition]
  have hpre : Z.preimage j ≤ Subfunctor.range d := by
    rw [← Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact'
      B S' hS' j i
      hXK X.2 hD hj hi]
    apply Space.schemeTheoreticImageSubfunctor_le B S' hS' _ hd
    rw [hpb]
    exact Subfunctor.range_comp_le _ _
  change Subfunctor.range (R.map Z.ι) = D.1
  ext W x
  constructor
  · rintro ⟨z, rfl⟩
    let a : (L.obj XK).obj ((Over.map g).op.obj W) :=
      ⟨⟨W.unop.hom, z.1⟩, rfl⟩
    have haeval : j.app ((Over.map g).op.obj W) a = z.1 :=
      OverShriek.relocalizeDescend_self g (F := X.1) (𝟙 XK) W.unop.hom z.1
    have ha : a ∈ (Z.preimage j).obj ((Over.map g).op.obj W) := by
      change j.app ((Over.map g).op.obj W) a ∈ Z.obj ((Over.map g).op.obj W)
      rw [haeval]
      exact z.2
    obtain ⟨y, hy⟩ := hpre _ ha
    have hiy : (R.map i).app W y = z.1 := by
      have h := congrArg (fun t => j.app ((Over.map g).op.obj W) t) hy
      change (d ≫ j).app ((Over.map g).op.obj W) y = _ at h
      rw [hfac] at h
      exact h.trans haeval
    have hz : z.1 ∈ (Subfunctor.range (R.map i)).obj W := ⟨y, hiy⟩
    rwa [relocalizeRestrict_range_ofRestricted g] at hz
  · intro hx
    have hdi : x ∈ (Subfunctor.range (R.map i)).obj W := by
      rw [relocalizeRestrict_range_ofRestricted g]
      exact hx
    obtain ⟨y, hy⟩ := hdi
    refine ⟨⟨x, ?_⟩, rfl⟩
    exact Space.range_le_schemeTheoreticImageSubfunctor B S' hS' i _ ⟨y, hy⟩

private theorem presheaf_relocalizeCounit
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (F : (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)
    (f : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS'))))
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hg : P (B.inclusion.map g)) :
    (P.inverseImage (BigFppfOver.toScheme B S' hS')).presheaf
      (OverShriek.relocalizeOfRestricted g
        (𝟙 ((OverShriek.relocalizeRestrict g).obj F))) := by
  let h : Over.mk g ⟶ Over.mk (𝟙 (B.obj hS')) := Over.homMk g
  let Q := P.inverseImage (BigFppfOver.toScheme B S' hS')
  let : Q.IsStableUnderBaseChange :=
    Space.inverseImage_isStableUnderBaseChange B S' hS' inferInstance
  have hh : Q.presheaf (yoneda.map h) := MorphismProperty.relative_map (P := Q) hg
  exact Q.presheaf.of_isPullback (relocalizeRestriction_isPullback g F f).flip hh

private theorem isQuasiCompact_of_iso
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {F G : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) (hF : Space.IsQuasiCompactSpace C S hS F) :
    Space.IsQuasiCompactSpace C S hS G := by
  obtain ⟨U, f, hc, hs, he⟩ := hF
  refine ⟨U, f ≫ e.hom, hc, MorphismProperty.RespectsIso.postcomp _ e.hom f hs, ?_⟩
  intro V g hg
  exact MorphismProperty.RespectsIso.postcomp _ e.hom (g ≫ f) (he V g hg)

private theorem isQuasiCompact_yoneda_of_compact
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS)
    (hT : CompactSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    Space.IsQuasiCompactSpace B S hS (yoneda.obj T) := by
  refine ⟨T, 𝟙 _, hT, ?_, ?_⟩
  · refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
    intro A D g fst snd hpb
    have hmap : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
    let : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
    let : IsIso ((BigFppfOver.toScheme B S hS).map snd) :=
      Functor.map_isIso _ snd
    exact (inferInstance : Surjective ((BigFppfOver.toScheme B S hS).map snd))
  · intro U φ hφ
    exact hφ

private theorem isQuasiCompact_of_presheaf
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {F G : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace C S hS F)
    (hG : IsAlgebraicSpace C S hS G)
    (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage (@QuasiCompact : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf f) :
    Space.IsQuasiCompact C S hS f := by
  apply ((Space.isQuasiCompact_tfae C S hS hF hG f).out 1 3).mpr
  intro U g hU
  let T := BigFppfOver.toScheme C S hS
  have : IsAffine (T.obj U) := hU
  have : QuasiCompact (T.map (hf.rep.snd g)) := hf.property_snd g
  have : CompactSpace (T.obj (hf.rep.pullback g)) :=
    QuasiCompact.compactSpace_of_compactSpace (T.map (hf.rep.snd g))
  exact isQuasiCompact_of_iso C S hS (hf.rep.isPullback g).flip.isoPullback
    (isQuasiCompact_yoneda_of_compact C S hS _ inferInstance)

/-- The morphism `Spec K ⟶ Spec R` of the big fppf site induced by the structure map of an
`R`-algebra `K`. -/
abbrev _root_.AlgebraicGeometry.Space.specAlgebraMapHom (B : BigFppfSite.{u}) (R K : Type u)
    [CommRing R] [CommRing K]
    [Algebra R K] (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K))) :
    B.obj hK ⟶ B.obj hR :=
  ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K)))

/-- The inclusion of the generic point of the spectrum of a domain is a monomorphism of schemes. -/
private theorem mono_spec_map_algebraMap {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    Mono (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : Epi (CommRingCat.ofHom (algebraMap R K)) :=
    IsLocalization.epi (nonZeroDivisors R) K
  change Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op)
  exact Functor.map_mono Scheme.Spec _

/-- The inclusion of the generic point of the spectrum of a domain is a monomorphism of the
big fppf site. -/
private theorem specAlgebraMapHom_mono {R K : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (B : BigFppfSite.{u})
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K))) :
    Mono (Space.specAlgebraMapHom B R K hR hK) :=
  Functor.mono_of_mono_map B.inclusion mono_spec_map_algebraMap

/-- The inclusion of the generic point of the spectrum of a domain is flat. -/
private theorem flat_spec_map_algebraMap {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  apply Flat.SpecMap_iff.mpr
  change (algebraMap R K).Flat
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R))

private theorem isFlat_relocalizeCounit
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (X : AlgebraicSpaces B S' hS')
    (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS'))))
    (hg : Flat (B.inclusion.map g)) :
    Space.IsFlat B S' hS'
      (OverShriek.relocalizeOfRestricted g
        (𝟙 ((OverShriek.relocalizeRestrict g).obj X.1))) := by
  have hj := presheaf_relocalizeCounit B S S' hS hS' g X.1 f (@Flat.{u}) hg
  exact (Space.isFlat_iff_presheaf B S' hS'
    (isAlgebraicSpace_viewOver B S S' hS hS' g _
      (isAlgebraicSpace_relocalizeRestrict B S S' hS hS' g X.1 X.2))
    X.2 hj.rep).2 hj

private theorem presheaf_relocalize_closedSubspace
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (X : AlgebraicSpaces B S' hS')
    (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS'))))
    (hg : QuasiCompact (B.inclusion.map g))
    (D : Space.ClosedSubspaces B S hS
      ((OverShriek.relocalizeRestrict g).obj X.1)) :
    (MorphismProperty.inverseImage (@QuasiCompact.{u})
      (BigFppfOver.toScheme B S' hS')).presheaf
      (OverShriek.relocalizeOfRestricted g D.1.ι) := by
  let L := OverShriek.relocalizePresheafFunctor g
  let j := OverShriek.relocalizeOfRestricted g
    (𝟙 ((OverShriek.relocalizeRestrict g).obj X.1))
  let Q := MorphismProperty.inverseImage (@QuasiCompact.{u})
    (BigFppfOver.toScheme B S' hS')
  have hj : Q.presheaf j := presheaf_relocalizeCounit B S S' hS hS' g X.1 f _ hg
  have hd : Q.presheaf (L.map D.1.ι) := by
    let : MorphismProperty.RespectsIso (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
      @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        quasiCompact_isStableUnderBaseChange
    let : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage (@QuasiCompact.{u}) _
    have hmono : (MorphismProperty.inverseImage (@IsClosedImmersion.{u})
        (BigFppfOver.toScheme B S hS)) ≤ Q.inverseImage (Over.map g) := by
      intro A C h hh
      have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map h) := hh
      exact (inferInstance : QuasiCompact ((BigFppfOver.toScheme B S hS).map h))
    exact presheaf_relocalize g Q D.1.ι
      (MorphismProperty.relative_monotone hmono _ D.2.2)
  have : Q.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have : Q.presheaf.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition Q
  have hi := Q.presheaf.comp_mem _ _ hd hj
  exact relocalize_map_comp_counit g D.1.ι ▸ hi

private theorem isQuasiCompact_relocalize_closedSubspace
    (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (X : AlgebraicSpaces B S' hS')
    (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS'))))
    (hg : QuasiCompact (B.inclusion.map g))
    (D : Space.ClosedSubspaces B S hS
      ((OverShriek.relocalizeRestrict g).obj X.1)) :
    Space.IsQuasiCompact B S' hS'
      (OverShriek.relocalizeOfRestricted g D.1.ι) :=
  isQuasiCompact_of_presheaf B S' hS'
    (isAlgebraicSpace_viewOver B S S' hS hS' g _ D.2.1) X.2 _
    (presheaf_relocalize_closedSubspace B S S' hS hS' g X f hg D)

private theorem etale_presheaf_id
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj U)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
  intro A C g fst snd hpb
  have hmap : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  exact (inferInstance : Etale ((BigFppfOver.toScheme B S hS).map snd))

private theorem smooth_chart_structureMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (f : X.1 ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))))
    (hf : Space.IsSmooth B S hS f)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1)
    (ha : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Smooth (B.inclusion.map U.hom) := by
  let T := BigFppfOver.toScheme B S hS
  let V : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let h : U ⟶ V := Over.homMk U.hom
  have hi := etale_presheaf_id B S hS V
  apply hf U V a (𝟙 _) h ha hi
  ext W x
  apply Over.OverMorphism.ext
  have hx := ((a ≫ f).app W x).w
  exact x.w.trans (by simpa using hx.symm)

private theorem isFlat_of_presheafEtale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G)
    (a : F ⟶ G)
    (ha : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Space.IsFlat B S hS a := by
  have hle : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)) ≤
      (MorphismProperty.inverseImage (@Flat.{u})
        (BigFppfOver.toScheme B S hS)) := by
    intro U V b hb
    have : Etale ((BigFppfOver.toScheme B S hS).map b) := hb
    exact (inferInstance : Flat ((BigFppfOver.toScheme B S hS).map b))
  have hFlat : (MorphismProperty.inverseImage (@Flat.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a :=
    MorphismProperty.relative_monotone hle a ha
  exact (Space.isFlat_iff_presheaf B S hS hF hG hFlat.rep).2 hFlat

private theorem schemeTheoreticImage_ker_of_representable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T U V : BigFppfOver B S hS} (g : T ⟶ U) (j : V ⟶ U)
    [IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hZ : Space.schemeTheoreticImageSubfunctor B S hS (yoneda.map g) =
      Subfunctor.range (yoneda.map j)) :
    ((BigFppfOver.toScheme B S hS).map j).ker =
      ((BigFppfOver.toScheme B S hS).map g).ker := by
  let F := BigFppfOver.toScheme B S hS
  let K := (F.map g).ker
  let hK : B.Contains K.subscheme :=
    Scheme.size_lt_of_isClosedImmersion K.subschemeι U.left.property
  let k₀ : B.obj hK ⟶ U.left := B.inclusion.preimage K.subschemeι
  let W : BigFppfOver B S hS := Over.mk (k₀ ≫ U.hom)
  let k : W ⟶ U := Over.homMk k₀
  have hk : F.map k = K.subschemeι :=
    B.inclusion.map_preimage (X := B.obj hK) (Y := U.left) K.subschemeι
  have : IsClosedImmersion (F.map k) := hk ▸ inferInstance
  have : Mono k := by
    apply Functor.mono_of_mono_map F
    infer_instance
  have : Mono (yoneda.map k) := Functor.map_mono yoneda k
  let := Space.inverseImage_isStableUnderBaseChange B S hS
    (IsClosedImmersion.isStableUnderBaseChange.{u})
  have hkclosed : Space.IsClosedImmersion B S hS (yoneda.map k) := by
    apply MorphismProperty.relative_map
    exact (inferInstance : IsClosedImmersion (F.map k))
  have hclosed : Space.IsClosedSubspace B S hS
      (Subfunctor.range (yoneda.map k)) :=
    isClosedSubspace_range B S hS
      (isAlgebraicSpace_yoneda B S hS W) (yoneda.map k) hkclosed
  obtain ⟨l, hl⟩ := site_factors_of_scheme_factors B S hS k g
    (F.map g).toImage (by rw [hk]; exact (F.map g).toImage_imageι)
  have hrange : Subfunctor.range (yoneda.map g) ≤
      Subfunctor.range (yoneda.map k) := by
    rw [← hl, yoneda.map_comp]
    exact Subfunctor.range_comp_le _ _
  have hmin : Subfunctor.range (yoneda.map j) ≤
      Subfunctor.range (yoneda.map k) := by
    rw [← hZ]
    exact Space.schemeTheoreticImageSubfunctor_le B S hS _ hclosed hrange
  apply le_antisymm
  · apply (range_yoneda_le_iff_ker_le B S hS j g).mp
    rw [← hZ]
    exact Space.range_le_schemeTheoreticImageSubfunctor B S hS _
  · have h := (range_yoneda_le_iff_ker_le B S hS k j).mp hmin
    change (F.map k).ker ≤ (F.map j).ker at h
    rw [hk, K.ker_subschemeι] at h
    exact h

/-- The schematic image is determined by the range of the source map. -/
private theorem schemeTheoreticImage_eq_of_range_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (h : Subfunctor.range f = Subfunctor.range g) :
    Space.schemeTheoreticImageSubfunctor B S hS f =
      Space.schemeTheoreticImageSubfunctor B S hS g := by
  simp only [Space.schemeTheoreticImageSubfunctor, h]

/-- If the schematic image of the pullback projection to a chart is the closed subscheme cut out
by `I`, then `I` is the kernel of the quasi-compact pullback projection. -/
private theorem ideal_eq_ker_snd_of_schemeTheoreticImage_eq
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i : F ⟶ H} {U V : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ H) (jV : V ⟶ U)
    [IsClosedImmersion ((BigFppfOver.toScheme B S hS).map jV)]
    (hi : (MorphismProperty.inverseImage (@QuasiCompact.{u})
      (BigFppfOver.toScheme B S hS)).presheaf i)
    (I : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData)
    (eV : (BigFppfOver.toScheme B S hS).obj V ≅ I.subscheme)
    (hjV : (BigFppfOver.toScheme B S hS).map jV = eV.hom ≫ I.subschemeι)
    (hchart : Space.schemeTheoreticImageSubfunctor B S hS (pullback.snd i a) =
      Subfunctor.range (yoneda.map jV)) :
    I = ((BigFppfOver.toScheme B S hS).map (hi.rep.snd a)).ker := by
  let e : yoneda.obj (hi.rep.pullback a) ≅ pullback i a := (hi.rep.isPullback a).isoPullback
  have hrange : Subfunctor.range (yoneda.map (hi.rep.snd a)) =
      Subfunctor.range (pullback.snd i a) := by
    have he : yoneda.map (hi.rep.snd a) = e.hom ≫ pullback.snd i a :=
      (hi.rep.isPullback a).isoPullback_hom_snd.symm
    rw [he]
    ext W x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.hom.app W y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e.inv.app W y, by simp⟩
  have hker := schemeTheoreticImage_ker_of_representable B S hS (hi.rep.snd a) jV
    ((schemeTheoreticImage_eq_of_range_eq B S hS _ _ hrange).trans hchart)
  simpa only [hjV, Scheme.Hom.ker_comp_of_isIso, I.ker_subschemeι] using hker

/-- Let `R` be a valuation ring with fraction field `K`, and let `X` be an algebraic space over
`R` whose structure morphism `X → Spec R` is smooth. For every effective Cartier divisor
`D ⊆ X_K` there is an effective Cartier divisor `D' ⊆ X` with `D'_K = D`.

Here `X_K` is the base change of `X` along `Spec K → Spec R`, that is the restriction of `X`
along `CategoryTheory.OverShriek.relocalizeRestrict`, and `D'_K` is the base change of the
closed subspace `D'`, `CategoryTheory.OverShriek.relocalizeRestrictSubfunctor`, a closed subspace
of `X_K`. The divisor `D'` is the scheme-theoretic image of `D → X_K → X`. -/
@[stacks 0DMC]
theorem _root_.AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_genericFibre_eq
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (B : BigFppfSite.{u}) (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (X : AlgebraicSpaces B (Spec (.of R)) hR)
    (hX : Space.IsSmooth B (Spec (.of R)) hR (Space.toBaseSiteMap B (Spec (.of R)) hR X.1))
    (D : Space.ClosedSubspaces B (Spec (.of K)) hK
      ((OverShriek.relocalizeRestrict (Space.specAlgebraMapHom B R K hR hK)).obj X.1))
    (hD : Space.IsEffectiveCartierDivisor B (Spec (.of K)) hK
      ⟨(OverShriek.relocalizeRestrict (Space.specAlgebraMapHom B R K hR hK)).obj X.1,
        isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of R)) hK hR
          (Space.specAlgebraMapHom B R K hR hK) X.1 X.2⟩ D) :
    ∃ D' : Space.ClosedSubspaces B (Spec (.of R)) hR X.1,
      Space.IsEffectiveCartierDivisor B (Spec (.of R)) hR X D' ∧
        OverShriek.relocalizeRestrictSubfunctor (Space.specAlgebraMapHom B R K hR hK) D'.1 =
          D.1 := by
  let f := Space.toBaseSiteMap B (Spec (.of R)) hR X.1
  let hf := hX
  let g := Space.specAlgebraMapHom B R K hR hK
  have hDalg : IsAlgebraicSpace B (Spec (.of K)) hK
      D.1.toFunctor := D.2.1
  let hDalgR := isAlgebraicSpace_viewOver B
    (Spec (.of K)) (Spec (.of R)) hK hR g
    D.1.toFunctor hDalg
  let i : (OverShriek.relocalizePresheafFunctor g).obj D.1.toFunctor ⟶ X.1 :=
    OverShriek.relocalizeOfRestricted g D.1.ι
  let XK := (OverShriek.relocalizeRestrict g).obj X.1
  let j : (OverShriek.relocalizePresheafFunctor g).obj XK ⟶ X.1 :=
    OverShriek.relocalizeOfRestricted g (𝟙 XK)
  have hi : (OverShriek.relocalizePresheafFunctor g).map D.1.ι ≫ j = i :=
    relocalize_map_comp_counit g D.1.ι
  let Z := Space.schemeTheoreticImage B (Spec (.of R)) hR i X.2
  have hgQC : QuasiCompact (B.inclusion.map g) := by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    infer_instance
  have hDglobal :
      Subfunctor.range ((OverShriek.relocalizeRestrict g).map Z.1.ι) = D.1 := by
    have : Mono g := specAlgebraMapHom_mono B hR hK
    apply schemeTheoreticImage_restrict_eq B (Spec (.of K))
      (Spec (.of R)) hK hR g X D
    · apply isFlat_relocalizeCounit B _ _ hK hR g X f
      exact flat_spec_map_algebraMap (R := R) (K := K)
    · exact isQuasiCompact_relocalize_closedSubspace B _ _ hK hR g X f hgQC D
  refine ⟨Z, ?_, ?_⟩
  · apply Space.isEffectiveCartierDivisor_of_hasEffectiveCartierEtalePullbacks
    intro U a ha
    have haEtale := ha U (𝟙 _) (etale_presheaf_id B (Spec (.of R)) hR U)
    have hU : Smooth (B.inclusion.map U.hom) :=
      smooth_chart_structureMap B (Spec (.of R)) hR X f hf U a (by simpa using haEtale)
    obtain ⟨I, V, jV, eV, hjV, hpre⟩ :=
      exists_scheme_pullback B (Spec (.of R)) hR X Z U a
    refine ⟨I, V, jV, eV, ?_, hjV, hpre⟩
    have haFlat : Space.IsFlat B (Spec (.of R)) hR a :=
      isFlat_of_presheafEtale B (Spec (.of R)) hR
        (isAlgebraicSpace_yoneda B (Spec (.of R)) hR U)
        X.2 a (by simpa using haEtale)
    have hiQC : Space.IsQuasiCompact B (Spec (.of R)) hR i :=
      isQuasiCompact_relocalize_closedSubspace B
        (Spec (.of K)) (Spec (.of R)) hK hR g X f hgQC D
    have hchartImageRange : Space.schemeTheoreticImageSubfunctor B (Spec (.of R)) hR
        (pullback.snd i a) = Subfunctor.range (yoneda.map jV) := by
      calc
        _ = Z.1.preimage a :=
          Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact'
            B (Spec (.of R)) hR a i
            (isAlgebraicSpace_yoneda B (Spec (.of R)) hR U)
            X.2 hDalgR haFlat hiQC
        _ = Subfunctor.range (yoneda.map jV) := hpre
    let hiPres := presheaf_relocalize_closedSubspace B
      (Spec (.of K)) (Spec (.of R)) hK hR g X f hgQC D
    let T := hiPres.rep.pullback a
    let b : T ⟶ U := hiPres.rep.snd a
    have hTgeneric : ∃ ψ : T.left ⟶ B.obj hK, ψ ≫ g = T.hom :=
      relocalize_source_factors g (hiPres.rep.fst a)
    have : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B (Spec (.of R)) hR).map jV) := by
      rw [hjV]
      infer_instance
    have hIker := ideal_eq_ker_snd_of_schemeTheoreticImage_eq B (Spec (.of R)) hR a jV hiPres I eV
      hjV hchartImageRange
    let W : BigFppfOver B (Spec (.of K)) hK :=
      (Over.pullback g).obj U
    let eW : (OverShriek.relocalizeRestrict g).obj (yoneda.obj U) ≅
        yoneda.obj W :=
      relocalizeRestrictYonedaIso B (Spec (.of K))
        (Spec (.of R)) hK hR g U
    let aK : yoneda.obj W ⟶ XK :=
      eW.inv ≫ (OverShriek.relocalizeRestrict g).map a
    let QE := MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B (Spec (.of K)) hK)
    let : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        Etale.etale_isStableUnderBaseChange
    have hRae : QE.presheaf ((OverShriek.relocalizeRestrict g).map a) :=
      Space.presheaf_restrict B (Spec (.of R))
        (Spec (.of K)) hR hK g (@Etale.{u}) a
        (by simpa using haEtale)
    have haKpre : QE.presheaf aK := by
      let : QE.presheaf.RespectsIso := inferInstance
      exact MorphismProperty.RespectsIso.precomp QE.presheaf eW.inv _ hRae
    have haK : Space.IsEtale B (Spec (.of K)) hK aK :=
      isEtale_of_presheaf B (Spec (.of K)) hK aK haKpre
    have hDlocal := Space.hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B
      (Spec (.of K)) hK
      ⟨XK, isAlgebraicSpace_relocalizeRestrict B
        (Spec (.of K)) (Spec (.of R)) hK hR g X.1 X.2⟩ D hD
    obtain ⟨J, E, jE, eE, hJCartier, hjE, hpreE⟩ := hDlocal W aK haK
    let VK : BigFppfOver B (Spec (.of K)) hK :=
      (Over.pullback g).obj V
    let jVK : VK ⟶ W := (Over.pullback g).map jV
    have hpreK : D.1.preimage aK = Subfunctor.range (yoneda.map jVK) := by
      rw [← hDglobal]
      exact preimage_relocalizeRestrict_eq_range_pullback B
        (Spec (.of K)) (Spec (.of R)) hK hR g
        Z.1 U V a jV hpre
    have hKrange : Subfunctor.range (yoneda.map jVK) =
        Subfunctor.range (yoneda.map jE) := hpreK.symm.trans hpreE
    have hKker :
        ((BigFppfOver.toScheme B (Spec (.of K)) hK).map jVK).ker =
          ((BigFppfOver.toScheme B (Spec (.of K)) hK).map jE).ker :=
      ker_eq_of_yoneda_range_eq B (Spec (.of K)) hK jVK jE hKrange
    have hJker : J =
        ((BigFppfOver.toScheme B (Spec (.of K)) hK).map jVK).ker := by
      rw [hKker, hjE, Scheme.Hom.ker_comp_of_isIso, J.ker_subschemeι]
    let p : (BigFppfOver.toScheme B
        (Spec (.of K)) hK).obj W ⟶
        (BigFppfOver.toScheme B (Spec (.of R)) hR).obj U :=
      B.inclusion.map (pullback.fst U.hom g)
    have hpb : IsPullback
        ((BigFppfOver.toScheme B
          (Spec (.of K)) hK).map jVK)
        (B.inclusion.map (pullback.fst V.hom g)) p
        ((BigFppfOver.toScheme B (Spec (.of R)) hR).map jV) :=
      (over_pullback_map_isPullback g jV).flip.map B.inclusion
    have hJcomap : J = I.comap p := by
      rw [hJker, ker_of_isPullback_of_isClosedImmersion _ _ _ _ hpb,
        hjV, Scheme.Hom.ker_comp_of_isIso, I.ker_subschemeι]
    let q := B.inclusion.map (pullback.snd U.hom g)
    have H : IsPullback p q (B.inclusion.map U.hom)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
      (IsPullback.of_hasPullback U.hom g).map B.inclusion
    obtain ⟨ψ, hψ⟩ := hTgeneric
    let bS := (BigFppfOver.toScheme B (Spec (.of R)) hR).map b
    have hb : bS ≫ B.inclusion.map U.hom =
        B.inclusion.map ψ ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      change B.inclusion.map b.left ≫ B.inclusion.map U.hom =
        B.inclusion.map ψ ≫ B.inclusion.map g
      rw [← Functor.map_comp, ← Functor.map_comp, b.w, hψ]
    let t := H.lift bS (B.inclusion.map ψ) hb
    have : Smooth (B.inclusion.map U.hom) := hU
    have : QuasiCompact bS := hiPres.property_snd a
    apply Stacks.Divisors.isEffectiveCartierDivisor_of_generic_kernel (B.inclusion.map U.hom)
      p q H bS t (H.lift_fst _ _ _) I hIker
    rwa [← hJcomap]
  · rw [← Subfunctor.range_ι (OverShriek.relocalizeRestrictSubfunctor g Z.1),
      OverShriek.ι_relocalizeRestrictSubfunctor]
    exact hDglobal

end AlgebraicGeometry.GenericFibreExtension

/-! ### Over an arbitrary base

The same argument runs over an arbitrary base scheme `S`, for a cartesian square of algebraic
spaces over `S` whose bottom edge is the image of `Spec K ⟶ Spec R` in the big fppf site of
`S`. The base change `j : Y_K ⟶ Y` of `Spec K ⟶ Spec R` is then a flat, quasi-compact
monomorphism of algebraic spaces over `S`, and no change of base is needed. -/

namespace AlgebraicGeometry.Space

attribute [local instance high] hasLimit_cospan_presheaf_EffectiveCartierGenericFibreExtension
  hasLimitsOfShape_discrete_presheaf_EffectiveCartierGenericFibreExtension

attribute [local instance] MorphismProperty.IsStableUnderBaseChange.respectsIso
  MorphismProperty.relative_isStableUnderBaseChange
  MorphismProperty.RespectsIso.inverseImage
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- In a cartesian square of representables, the preimage of the range of one leg along the
other is the range of the parallel projection. -/
private theorem preimage_range_yoneda_map_of_isPullback {C : Type v} [Category.{w} C]
    {P V W U : C} {fst : P ⟶ V} {snd : P ⟶ W} {f : V ⟶ U} {g : W ⟶ U}
    (h : IsPullback fst snd f g) :
    (Subfunctor.range (yoneda.map f)).preimage (yoneda.map g) =
      Subfunctor.range (yoneda.map snd) := by
  ext Z x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨h.lift y x hy, h.lift_snd _ _ _⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y ≫ fst, by simp [h.w]⟩

/-- A presheaf morphism that is a base change of the Yoneda image of a morphism of the site
inherits every base-change-stable property of the underlying morphism of schemes. -/
private theorem presheaf_of_isPullback_yoneda_map
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V : BigFppfOver B S hS}
    {f : F ⟶ G} {a : F ⟶ yoneda.obj U} {b : G ⟶ yoneda.obj V} {h : U ⟶ V}
    (sq : IsPullback f a b (yoneda.map h)) (hh : P ((BigFppfOver.toScheme B S hS).map h)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f := by
  let : (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    Space.inverseImage_isStableUnderBaseChange B S hS inferInstance
  exact MorphismProperty.of_isPullback sq.flip (MorphismProperty.relative_map hh)

/-- **Stacks 0DMC over an arbitrary base.** Let `R` be a valuation ring with fraction field `K`,
let `T_R ⟶ S` and `T_K ⟶ S` be objects of the big fppf site of `S` with underlying schemes
`Spec R` and `Spec K`, and `g : T_K ⟶ T_R` a morphism lying over `Spec K ⟶ Spec R`. Let
`π : Y ⟶ T_R` be a smooth morphism of algebraic spaces over `S` and `Y_K = Y ×_{T_R} T_K`.
Every effective Cartier divisor `D ⊆ Y_K` is the inverse image of an effective Cartier divisor
`D' ⊆ Y`. -/
theorem exists_isEffectiveCartierDivisor_preimage_eq_of_isPullback
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {TK TR : BigFppfOver B S hS} (g : TK ⟶ TR)
    (hTK : (BigFppfOver.toScheme B S hS).obj TK = Spec (.of K))
    (hTR : (BigFppfOver.toScheme B S hS).obj TR = Spec (.of R))
    (hg : (BigFppfOver.toScheme B S hS).map g =
      eqToHom hTK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ eqToHom hTR.symm)
    {Y YK : AlgebraicSpaces B S hS} (π : Y ⟶ (schemeSpaceFunctor B S hS).obj TR)
    (πK : YK ⟶ (schemeSpaceFunctor B S hS).obj TK) (j : YK ⟶ Y)
    (sq : IsPullback j πK π ((schemeSpaceFunctor B S hS).map g))
    (hπ : IsSmooth B S hS π.hom)
    (D : ClosedSubspaces B S hS YK.1) (hD : IsEffectiveCartierDivisor B S hS YK D) :
    ∃ D' : ClosedSubspaces B S hS Y.1,
      IsEffectiveCartierDivisor B S hS Y D' ∧ D'.1.preimage j.hom = D.1 := by
  obtain ⟨πR, hπR⟩ : ∃ πR : Y.1 ⟶ yoneda.obj TR, π.hom = πR := ⟨π.hom, rfl⟩
  obtain ⟨πKR, hπKR⟩ : ∃ πKR : YK.1 ⟶ yoneda.obj TK, πK.hom = πKR := ⟨πK.hom, rfl⟩
  have hsq : IsPullback j.hom πKR πR (yoneda.map g) := by
    subst hπR hπKR
    exact AlgebraicSpaces.isPullback_hom B S hS sq
  have hπR' : IsSmooth B S hS πR := by
    subst hπR
    exact hπ
  have hφFlat : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    GenericFibreExtension.flat_spec_map_algebraMap
  have hgFlat : Flat ((BigFppfOver.toScheme B S hS).map g) := by
    rw [hg]
    infer_instance
  have hgQC : QuasiCompact ((BigFppfOver.toScheme B S hS).map g) := by
    rw [hg]
    infer_instance
  have hgMono : Mono g := by
    have : Mono (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
      GenericFibreExtension.mono_spec_map_algebraMap
    have : Mono ((BigFppfOver.toScheme B S hS).map g) := by
      rw [hg]
      infer_instance
    exact Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS) this
  have : Mono (yoneda.map g) := Functor.map_mono yoneda g
  have hjMono : Mono j.hom := hsq.mono_fst_of_mono
  let QC := MorphismProperty.inverseImage (@QuasiCompact.{u}) (BigFppfOver.toScheme B S hS)
  have hjF : (MorphismProperty.inverseImage (@Flat.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j.hom :=
    presheaf_of_isPullback_yoneda_map B S hS _ hsq hgFlat
  have hjFlat : Space.IsFlat B S hS j.hom :=
    (Space.isFlat_iff_presheaf B S hS YK.2 Y.2 hjF.rep).2 hjF
  let i : D.1.toFunctor ⟶ Y.1 := D.1.ι ≫ j.hom
  have hiPres : QC.presheaf i := by
    have hjQC : QC.presheaf j.hom := presheaf_of_isPullback_yoneda_map B S hS _ hsq hgQC
    have hd : QC.presheaf D.1.ι := by
      have hmono : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
          (BigFppfOver.toScheme B S hS)) ≤ QC := by
        intro A C h hh
        have : _root_.AlgebraicGeometry.IsClosedImmersion
            ((BigFppfOver.toScheme B S hS).map h) := hh
        exact (inferInstance : QuasiCompact ((BigFppfOver.toScheme B S hS).map h))
      exact MorphismProperty.relative_monotone hmono _ D.2.2
    have : QC.IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    have : QC.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition QC
    exact QC.presheaf.comp_mem _ _ hd hjQC
  have hiQC : Space.IsQuasiCompact B S hS i :=
    GenericFibreExtension.isQuasiCompact_of_presheaf B S hS D.2.1 Y.2 i hiPres
  let Z := Space.schemeTheoreticImage B S hS i Y.2
  have hDglobal : Z.1.preimage j.hom = D.1 := by
    apply le_antisymm
    · change (Space.schemeTheoreticImageSubfunctor B S hS i).preimage j.hom ≤ D.1
      rw [← Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact'
        B S hS j.hom i YK.2 Y.2 D.2.1 hjFlat hiQC]
      apply Space.schemeTheoreticImageSubfunctor_le B S hS _ D.2
      have hpb : pullback.snd i j.hom = pullback.fst i j.hom ≫ D.1.ι := by
        apply (cancel_mono j.hom).1
        rw [Category.assoc, ← pullback.condition]
      rw [hpb]
      exact (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι D.1).le
    · intro W x hx
      exact Space.range_le_schemeTheoreticImageSubfunctor B S hS i W ⟨⟨x, hx⟩, rfl⟩
  refine ⟨Z, ?_, hDglobal⟩
  apply Space.isEffectiveCartierDivisor_of_hasEffectiveCartierEtalePullbacks
  intro U a ha
  have haEtale := ha U (𝟙 _) (GenericFibreExtension.etale_presheaf_id B S hS U)
  rw [Category.id_comp] at haEtale
  obtain ⟨I, V, jV, eV, hjV, hpre⟩ := GenericFibreExtension.exists_scheme_pullback B S hS Y Z U a
  refine ⟨I, V, jV, eV, ?_, hjV, hpre⟩
  let u : U ⟶ TR := Yoneda.fullyFaithful.preimage (a ≫ πR)
  have hu : yoneda.map u = a ≫ πR := Yoneda.fullyFaithful.map_preimage _
  have hUsmooth : Smooth ((BigFppfOver.toScheme B S hS).map u) :=
    hπR' U TR a (𝟙 _) u haEtale (GenericFibreExtension.etale_presheaf_id B S hS TR)
      (by rw [Category.comp_id, hu])
  have haFlat : Space.IsFlat B S hS a :=
    GenericFibreExtension.isFlat_of_presheafEtale B S hS (isAlgebraicSpace_yoneda B S hS U) Y.2 a
      haEtale
  have hchartImageRange : Space.schemeTheoreticImageSubfunctor B S hS
      (pullback.snd i a) = Subfunctor.range (yoneda.map jV) := by
    calc
      _ = Z.1.preimage a :=
        Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact'
          B S hS a i (isAlgebraicSpace_yoneda B S hS U) Y.2 D.2.1 haFlat hiQC
      _ = Subfunctor.range (yoneda.map jV) := hpre
  let T := hiPres.rep.pullback a
  let b : T ⟶ U := hiPres.rep.snd a
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map jV) := by
    rw [hjV]
    infer_instance
  have hIker := GenericFibreExtension.ideal_eq_ker_snd_of_schemeTheoreticImage_eq B S hS a jV
    hiPres I eV hjV hchartImageRange
  let pr₁ : pullback u g ⟶ U := pullback.fst u g
  let pr₂ : pullback u g ⟶ TK := pullback.snd u g
  let tK : T ⟶ TK := Yoneda.fullyFaithful.preimage
    (hiPres.rep.fst a ≫ D.1.ι ≫ πKR)
  have htK : b ≫ u = tK ≫ g := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_comp, hu, Yoneda.fullyFaithful.map_preimage,
      ← Category.assoc, ← (hiPres.rep.isPullback a).w, Category.assoc, Category.assoc,
      Category.assoc]
    exact congrArg (fun φ => hiPres.rep.fst a ≫ D.1.ι ≫ φ) hsq.w
  let t' : T ⟶ pullback u g := pullback.lift b tK htK
  have hW : IsPullback (yoneda.map pr₁) (yoneda.map pr₂) (yoneda.map u) (yoneda.map g) :=
    (IsPullback.of_hasPullback u g).map yoneda
  have hcomm : (yoneda.map pr₁ ≫ a) ≫ πR = yoneda.map pr₂ ≫ yoneda.map g := by
    rw [Category.assoc, ← hu, ← yoneda.map_comp, ← yoneda.map_comp, pullback.condition]
  let aK : yoneda.obj (pullback u g) ⟶ YK.1 :=
    hsq.lift (yoneda.map pr₁ ≫ a) (yoneda.map pr₂) hcomm
  have haKj : aK ≫ j.hom = yoneda.map pr₁ ≫ a := hsq.lift_fst _ _ _
  have haKπ : aK ≫ πKR = yoneda.map pr₂ := hsq.lift_snd _ _ _
  have hleft : IsPullback aK (yoneda.map pr₁) j.hom a := by
    refine IsPullback.of_right ?_ haKj hsq.flip
    rw [haKπ, ← hu]
    exact hW.flip
  have haKpre : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf aK := by
    let : (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
      Space.inverseImage_isStableUnderBaseChange B S hS inferInstance
    exact MorphismProperty.of_isPullback hleft.flip haEtale
  have haK : Space.IsEtale B S hS aK := GenericFibreExtension.isEtale_of_presheaf B S hS aK haKpre
  obtain ⟨J, E, jE, eE, hJCartier, hjE, hpreE⟩ :=
    Space.hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS YK D hD _ aK haK
  let jVK : pullback jV pr₁ ⟶ pullback u g := pullback.snd jV pr₁
  have hpreK : D.1.preimage aK = Subfunctor.range (yoneda.map jVK) := by
    rw [← preimage_range_yoneda_map_of_isPullback (IsPullback.of_hasPullback jV pr₁), ← hpre,
      ← hDglobal]
    ext W x
    change j.hom.app W (aK.app W x) ∈ Z.1.obj W ↔ a.app W ((yoneda.map pr₁).app W x) ∈ Z.1.obj W
    rw [show j.hom.app W (aK.app W x) = a.app W ((yoneda.map pr₁).app W x) from
      congrArg (fun φ => φ.app W x) haKj]
  have hKker : ((BigFppfOver.toScheme B S hS).map jVK).ker =
      ((BigFppfOver.toScheme B S hS).map jE).ker :=
    GenericFibreExtension.ker_eq_of_yoneda_range_eq B S hS jVK jE (hpreK.symm.trans hpreE)
  let p := (BigFppfOver.toScheme B S hS).map pr₁
  have hJcomap : J = I.comap p := by
    have hpbK : IsPullback ((BigFppfOver.toScheme B S hS).map jVK)
        ((BigFppfOver.toScheme B S hS).map (pullback.fst jV pr₁)) p
        ((BigFppfOver.toScheme B S hS).map jV) :=
      ((IsPullback.of_hasPullback jV pr₁).map (BigFppfOver.toScheme B S hS)).flip
    rw [← J.ker_subschemeι, ← Scheme.Hom.ker_comp_of_isIso eE.hom, ← hjE, ← hKker,
      GenericFibreExtension.ker_of_isPullback_of_isClosedImmersion _ _ _ _ hpbK, hjV,
      Scheme.Hom.ker_comp_of_isIso, I.ker_subschemeι]
  let q := (BigFppfOver.toScheme B S hS).map pr₂ ≫ eqToHom hTK
  let fR := (BigFppfOver.toScheme B S hS).map u ≫ eqToHom hTR
  have H : IsPullback p q fR (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    refine ((IsPullback.of_hasPullback u g).map (BigFppfOver.toScheme B S hS)).of_iso
      (Iso.refl _) (Iso.refl _) (eqToIso hTK) (eqToIso hTR) ?_ ?_ ?_ ?_
    · simp [p, pr₁]
    · simp [q, pr₂]
    · simp [fR]
    · rw [hg]
      simp
  have : Smooth ((BigFppfOver.toScheme B S hS).map u) := hUsmooth
  have : Smooth fR := by
    dsimp only [fR]
    infer_instance
  have : QuasiCompact ((BigFppfOver.toScheme B S hS).map b) := hiPres.property_snd a
  apply Stacks.Divisors.isEffectiveCartierDivisor_of_generic_kernel fR p q H
    ((BigFppfOver.toScheme B S hS).map b) ((BigFppfOver.toScheme B S hS).map t')
    (by rw [← Functor.map_comp]; exact congrArg _ (pullback.lift_fst _ _ _)) I hIker
  rwa [← hJcomap]

end AlgebraicGeometry.Space

end
