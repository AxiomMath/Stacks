module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Nagata
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# Finiteness of the relative normalization over a Nagata algebraic space

Let `f : Y ⟶ X` be a quasi-separated morphism of finite type of algebraic spaces over a scheme
`S`, with `X` Nagata and `Y` reduced. Tag 0BB0 asserts that the normalization `ν : X' ⟶ X` of
`X` in `Y` is then a finite morphism. That is proved here for every factorization satisfying the
characterization `AlgebraicGeometry.Space.IsRelativeNormalization` of Tag 0823, in the idiom of
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalization`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.finite_integralClosure_of_isNagataScheme`: for a morphism of schemes of
  finite type with reduced source and Nagata target, the integral closure of the functions on an
  affine open of the target in the functions on its preimage is a finite module. This is Tag 03GR
  read through the sections of the relative normalization.
* `AlgebraicGeometry.isFinite_of_isIntegralHom_of_injective_appTop`: an integral morphism of
  affine schemes over a Nagata affine base is finite as soon as its sections embed into those of
  a reduced affine scheme of finite type over the base.
* `AlgebraicGeometry.Space.IsRelativeNormalization.isFinite_of_isNagata` is **Tag 0BB0**.

## Implementation notes

**The shape of the argument.** Finiteness of a morphism of algebraic spaces is étale local on the
target, which is condition (3) of Tag 03ZQ and is the source's first step; here it is
`AlgebraicGeometry.Space.isFinite_iff_etaleLocal`, and since finiteness of a morphism of schemes
is Zariski local on the target the question reduces to the affine étale charts of `X`. Over such
a chart `V` the morphism `ν` is representable with affine integral base change `n : N ⟶ V`,
because `ν` is integral by the characterization; quasi-compactness of `f` makes the part of `Y`
over `V` quasi-compact, so Tag 03H6 supplies an affine surjective étale cover `W` of it, and `W`
is reduced and of finite type over `V`. Tag 03GR then makes the integral closure of the functions
on `V` in the functions on `W` a finite module over the Noetherian ring of functions on `V`, and
the functions on `N` are an integral subalgebra of it; a submodule of a finite module over a
Noetherian ring is finite, which is the source's last step.

**The hypothesis `hdom`, and why it is carried.** What makes the functions on `N` a *subalgebra*
of the functions on `W` is the construction of Tag 0822: the normalization is the relative
spectrum of a subalgebra `𝒪' ⊂ f_* 𝒪_Y`, so over an affine chart its functions are the integral
closure of the chart ring inside the functions on the part of `Y` over the chart, and those inject
into the functions on a surjective étale cover of it. The characterization of Tag 0823 does not
see this: it determines the factorization up to unique isomorphism among integral factorizations,
and nothing in a universal property distinguishes a subalgebra of `f_* 𝒪_Y` from a quotient of
one. The construction itself rests on the relative spectrum of a quasi-coherent algebra on an
algebraic space, Tag 081V, whose input
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` has no inhabitant in this library — the
same gap that confines `AlgebraicGeometry.Space.normalizationIn` of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationIn` to a conditional statement. So the
injectivity of the comparison on sections is carried as the named hypothesis `hdom`, and recorded
in the attribute: it is the only input of the proof that the source gets from the construction
rather than from the characterization. The sections assertion of Tag 0820, which the construction
also uses, *is* available, as
`AlgebraicGeometry.Space.AlgebraSheaf.range_integralClosureInclusion_app_eq_integralClosure'`.

**The quasi-separatedness hypothesis is not used.** The source imposes it on `f`, together with
quasi-compactness, so that `f_* 𝒪_Y` is quasi-coherent and the normalization exists. Here the
normalization is given, and the argument uses only quasi-compactness of `f` — to cover the part
of `Y` over a chart by an affine scheme — and local finite type — to apply Tag 03GR. The
hypothesis is kept in the shape the tag states it and discarded by the proof.

## References

* [Stacks Project, Tag 0BB0](https://stacks.math.columbia.edu/tag/0BB0)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03GR](https://stacks.math.columbia.edu/tag/03GR)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### The scheme-level input -/

/-- Over an affine open of the base the integral closure of the functions on that open in the
functions on its preimage is a finite module, for a finite type morphism with reduced source and
Nagata target. -/
theorem finite_integralClosure_of_isNagataScheme
    {W V : Scheme.{u}} (g : W ⟶ V) [LocallyOfFiniteType g] [QuasiCompact g] [QuasiSeparated g]
    [IsReduced W] (hV : IsNagataScheme V) (U : V.affineOpens) :
    letI := (g.app U.1).hom.toAlgebra
    Module.Finite Γ(V, U.1) (integralClosure Γ(V, U.1) Γ(W, g ⁻¹ᵁ U.1)) := by
  have : IsFinite g.fromNormalization :=
    AlgebraicGeometry.isFinite_fromNormalization_of_locallyOfFiniteType g hV
  let := (g.app U.1).hom.toAlgebra
  let : Algebra Γ(V, U.1) Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U.1) :=
    (g.fromNormalization.app U.1).hom.toAlgebra
  have h := IsFinite.finite_app g.fromNormalization U.1 U.2
  let : Module.Finite Γ(V, U.1)
      Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U.1) := RingHom.finite_algebraMap.mp h
  let e := Scheme.Hom.normalizationObjIso g U.2
  let er : Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U.1) ≃+*
      integralClosure Γ(V, U.1) Γ(W, g ⁻¹ᵁ U.1) := e.commRingCatIsoToRingEquiv
  have e2 : g ⁻¹ᵁ U.1 ≤ g.toNormalization ⁻¹ᵁ (g.fromNormalization ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage g.toNormalization g.fromNormalization U.1,
      g.toNormalization_fromNormalization]
  have hcomp : g.fromNormalization.app U.1 ≫
      g.toNormalization.appLE (g.fromNormalization ⁻¹ᵁ U.1) (g ⁻¹ᵁ U.1) e2 = g.app U.1 := by
    calc
      _ = Scheme.Hom.appLE g.fromNormalization U.1 (g.fromNormalization ⁻¹ᵁ U.1)
          le_rfl ≫ g.toNormalization.appLE (g.fromNormalization ⁻¹ᵁ U.1)
            (g ⁻¹ᵁ U.1) e2 := by rw [← Scheme.Hom.app_eq_appLE]
      _ = Scheme.Hom.appLE (g.toNormalization ≫ g.fromNormalization) U.1
          (g ⁻¹ᵁ U.1) _ := Scheme.Hom.appLE_comp_appLE g.toNormalization
            g.fromNormalization U.1 (g.fromNormalization ⁻¹ᵁ U.1) (g ⁻¹ᵁ U.1) le_rfl e2
      _ = g.app U.1 := by
        simp only [g.toNormalization_fromNormalization, Scheme.Hom.app_eq_appLE]
  have her (r : Γ(V, U.1)) : er (algebraMap Γ(V, U.1)
      Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U.1) r) =
      algebraMap Γ(V, U.1) (integralClosure Γ(V, U.1) Γ(W, g ⁻¹ᵁ U.1)) r := by
    apply Subtype.ext
    have hval := ConcreteCategory.congr_hom
      (Scheme.Hom.normalizationObjIso_hom_val g U.2)
      ((g.fromNormalization.app U.1).hom r)
    calc
      _ = (g.toNormalization.appLE (g.fromNormalization ⁻¹ᵁ U.1)
          (g ⁻¹ᵁ U.1) e2).hom ((g.fromNormalization.app U.1).hom r) := hval
      _ = (g.app U.1).hom r := ConcreteCategory.congr_hom hcomp r
      _ = _ := rfl
  let ea : Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U.1) ≃ₐ[Γ(V, U.1)]
      integralClosure Γ(V, U.1) Γ(W, g ⁻¹ᵁ U.1) := AlgEquiv.ofRingEquiv her
  exact Module.Finite.equiv ea.toLinearEquiv

/-- An integral morphism of affine schemes over a Nagata affine base is finite as soon as its
sections embed into those of a reduced affine scheme of finite type over the base. -/
theorem isFinite_of_isIntegralHom_of_injective_appTop
    {V N W : Scheme.{u}} (n : N ⟶ V) (c : W ⟶ N)
    [IsAffine V] [IsAffine N] [IsAffine W] [IsIntegralHom n]
    [LocallyOfFiniteType (c ≫ n)] [IsReduced W] (hV : IsNagataScheme V)
    (hinj : Function.Injective c.appTop.hom) :
    IsFinite n := by
  have hVnoeth : IsLocallyNoetherian V :=
    ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme V).mp hV).1
  have _ : IsNoetherianRing Γ(V, (⊤ : V.Opens)) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V⟩
  let instA : Algebra Γ(V, (⊤ : V.Opens)) Γ(N, (⊤ : N.Opens)) := n.appTop.hom.toAlgebra
  let instC : Algebra Γ(V, (⊤ : V.Opens)) Γ(W, (⊤ : W.Opens)) := (c ≫ n).appTop.hom.toAlgebra
  have hfin : Module.Finite Γ(V, (⊤ : V.Opens))
      (integralClosure Γ(V, (⊤ : V.Opens)) Γ(W, (⊤ : W.Opens))) :=
    finite_integralClosure_of_isNagataScheme (c ≫ n) hV ⟨⊤, isAffineOpen_top V⟩
  have hint : Algebra.IsIntegral Γ(V, (⊤ : V.Opens)) Γ(N, (⊤ : N.Opens)) :=
    ⟨fun x => n.isIntegral_app ⊤ (isAffineOpen_top V) x⟩
  let φ : Γ(N, (⊤ : N.Opens)) →ₐ[Γ(V, (⊤ : V.Opens))] Γ(W, (⊤ : W.Opens)) :=
    { c.appTop.hom with
      commutes' := fun r => congrArg (fun k : Γ(V, (⊤ : V.Opens)) ⟶ Γ(W, (⊤ : W.Opens)) => k.hom r)
        (Scheme.Hom.comp_appTop c n).symm }
  let ψ : Γ(N, (⊤ : N.Opens)) →ₐ[Γ(V, (⊤ : V.Opens))]
      integralClosure Γ(V, (⊤ : V.Opens)) Γ(W, (⊤ : W.Opens)) :=
    AlgHom.codRestrict φ _ fun x => (hint.isIntegral x).map φ
  have hψ : Function.Injective ψ := fun x y h => hinj (congrArg Subtype.val h)
  have hmod : Module.Finite Γ(V, (⊤ : V.Opens)) Γ(N, (⊤ : N.Opens)) :=
    Module.Finite.of_injective ψ.toLinearMap hψ
  have _ : IsFinite (Spec.map n.appTop) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hmod)
  have hfac : n = N.isoSpec.hom ≫ Spec.map n.appTop ≫ V.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality n, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [hfac]
  infer_instance

namespace Space

/-! ### Reduction to affine étale charts of the target -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A representable morphism of algebraic spaces over `S` is finite as soon as, over every
affine étale chart of its target, the morphism of schemes representing its base change is
finite. -/
private theorem isFinite_of_affine_etale_tests
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hf : ∀ (V : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∀ (q : yoneda.obj V ⟶ Y),
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf q →
        _root_.AlgebraicGeometry.IsFinite
          ((BigFppfOver.toScheme B S hS).map (hrep.snd q))) :
    IsFinite B S hS f := by
  let T := BigFppfOver.toScheme B S hS
  have key (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
      (P.inverseImage T).IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS P
  have _ := key (@_root_.AlgebraicGeometry.IsFinite.{u})
  have _ := key (@AlgebraicGeometry.Etale.{u})
  obtain ⟨V, q, hsurj, hetale⟩ := hY.exists_atlas
  refine (isFinite_iff_etaleLocal B S hS f hX hY).mpr ⟨V, q, hsurj, hetale, ?_⟩
  have hpb := hrep.isPullback q
  have hfin : _root_.AlgebraicGeometry.IsFinite (T.map (hrep.snd q)) := by
    have _ := isZariskiLocalAtTarget_isFinite.{u}
    let cover := (T.obj V).affineCover
    refine IsZariskiLocalAtTarget.of_openCover
      (P := @_root_.AlgebraicGeometry.IsFinite.{u}) cover fun j => ?_
    let T₀ : B.Schemes := B.obj (Scheme.size_lt_of_isOpenImmersion (cover.f j) V.left.property)
    let a₀ : T₀ ⟶ V.left :=
      B.inclusion.preimage (show B.inclusion.obj T₀ ⟶ B.inclusion.obj V.left from cover.f j)
    let Tj : BigFppfOver B S hS := Over.mk (a₀ ≫ V.hom)
    let a : Tj ⟶ V := Over.homMk a₀
    have ha : T.map a = cover.f j := B.inclusion.map_preimage _
    have hTaff : IsAffine (T.obj Tj) := by
      show IsAffine (cover.X j); infer_instance
    have haEtale : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T) a := by
      show AlgebraicGeometry.Etale (T.map a)
      rw [ha]; infer_instance
    have hqa : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
        (yoneda.map a ≫ q) :=
      (isEtale_of_presheaf_etale B S hS hetale) Tj (yoneda.map a)
        (MorphismProperty.relative_map haEtale)
    have hfinite := hf Tj hTaff (yoneda.map a ≫ q) hqa
    let q' := yoneda.map a ≫ q
    let t : hrep.pullback q' ⟶ hrep.pullback q :=
      hrep.lift (hrep.fst q') (hrep.snd q' ≫ a) (by
        simpa only [Functor.map_comp, Category.assoc] using (hrep.isPullback q').w)
    have ht : yoneda.map t ≫ hrep.fst q = hrep.fst q' := hrep.lift_fst _ _ _
    have hs : yoneda.map t ≫ yoneda.map (hrep.snd q) =
        yoneda.map (hrep.snd q') ≫ yoneda.map a := by
      rw [← yoneda.map_comp, hrep.lift_snd, yoneda.map_comp]
    have hsq : IsPullback (yoneda.map t) (yoneda.map (hrep.snd q'))
        (yoneda.map (hrep.snd q)) (yoneda.map a) :=
      (ht.symm ▸ hrep.isPullback q').of_right hs (hrep.isPullback q)
    have hscheme := (hsq.of_map_of_faithful yoneda).map T
    rw [ha] at hscheme
    have _ : _root_.AlgebraicGeometry.IsFinite (T.map (hrep.snd q')) := hfinite
    show _root_.AlgebraicGeometry.IsFinite (Limits.pullback.snd (T.map (hrep.snd q)) (cover.f j))
    rw [← hscheme.isoPullback_inv_snd]
    infer_instance
  have hVspace : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hPull : IsAlgebraicSpace B S hS (Limits.pullback f q) :=
    isAlgebraicSpace_pullback B S hS f q hX hVspace hY
  have hrelq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      T).relative yoneda (Limits.pullback.snd f q) := by
    refine (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      T).relative yoneda).cancel_left_of_respectsIso
      hpb.isoPullback.hom (Limits.pullback.snd f q)).mp ?_
    rw [hpb.isoPullback_hom_snd]
    exact MorphismProperty.relative_map hfin
  exact (isFinite_iff_representable B S hS (Limits.pullback.snd f q) hPull hVspace).2
    ⟨hrelq.1, hrelq⟩

/-! ### Finiteness of the normalization -/

variable {X Y X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : Y ⟶ X} {ν : X' ⟶ X} {f' : Y ⟶ X'}

/-- **Stacks 0BB0.** Let `f : Y ⟶ X` be a quasi-separated morphism of finite type of algebraic
spaces over `S` with `X` Nagata and `Y` reduced. Then the normalization `ν : X' ⟶ X` of `X`
in `Y` is finite.

Nagata-ness and reducedness are the étale-local properties of schemes of Tag 03E6. The
hypothesis `hdom` is the affine-chart description of the normalization of Tag 0822: over an
affine étale chart of `X` the functions on the base change of `X'` embed into the functions on
an affine surjective étale cover of the part of `Y` over the chart. -/
@[stacks 0BB0 "granted Tag 081V, the relative spectrum of a quasi-coherent algebra on an \
algebraic space, in the shape of the hypothesis hdom: over an affine étale chart of the base \
the functions on the chart base change of the normalization embed into the functions on an \
affine surjective étale cover of the corresponding part of the source"]
theorem IsRelativeNormalization.isFinite_of_isNagata
    (hnorm : IsRelativeNormalization B S hS f ν f')
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hX' : IsAlgebraicSpace B S hS X')
    (hXnagata : HasEtaleLocalProperty B S hS X fun Z : Scheme.{u} => IsNagataScheme Z)
    (hYred : HasEtaleLocalProperty B S hS Y fun Z : Scheme.{u} => IsReduced Z)
    (hft : IsFiniteType B S hS f) (_hqs : IsQuasiSeparated B S hS f)
    (hdom : ∀ (V N W : BigFppfOver B S hS) (q : yoneda.obj V ⟶ X) (n : N ⟶ V)
      (i : yoneda.obj N ⟶ X') (w : yoneda.obj W ⟶ Limits.pullback q f) (c : W ⟶ N),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q →
      IsPullback i (yoneda.map n) ν q →
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf w →
      IsEtale B S hS w →
      yoneda.map c ≫ i = w ≫ Limits.pullback.snd q f ≫ f' →
      Function.Injective ((BigFppfOver.toScheme B S hS).map c).appTop.hom) :
    IsFinite B S hS ν := by
  let T := BigFppfOver.toScheme B S hS
  have hrepν := (isIntegralHom_iff_representable B S hS ν hX' hX).mp hnorm.isIntegralHom
  refine isFinite_of_affine_etale_tests B S hS ν hX' hX hrepν.1 fun V hV q hq => ?_
  -- the chart is Nagata, hence Noetherian
  have hVnag : IsNagataScheme (T.obj V) :=
    (exists_atlas_iff_forall_etale B S hS X (fun Z : Scheme.{u} => IsNagataScheme Z) hX).mp
      hXnagata V q hq
  -- the base change of `ν` along the chart is represented by an affine scheme, integral over it
  have hpb := hrepν.1.isPullback q
  have hnInt : _root_.AlgebraicGeometry.IsIntegralHom (T.map (hrepν.1.snd q)) :=
    hrepν.2.property q (hrepν.1.fst q) (hrepν.1.snd q) hpb
  have hNaff : IsAffine (T.obj (hrepν.1.pullback q)) :=
    isAffine_of_isIntegralHom (T.map (hrepν.1.snd q)) hnInt hV
  -- an affine surjective étale cover of the part of `Y` lying over the chart
  have hVspace : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hPspace : IsAlgebraicSpace B S hS (Limits.pullback q f) :=
    isAlgebraicSpace_pullback B S hS q f hVspace hY hX
  obtain ⟨W, w, hWaff, hwSurj, hwEt⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (Limits.pullback q f) hPspace).mp
      (hft.2 (yoneda.obj V) hVspace (isQuasiCompactSpace_yoneda_of_isAffine B S hS V hV) q)
  -- the cover is an étale chart of `Y`
  have hsnd : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
      (Limits.pullback.snd q f) :=
    presheaf_of_isPullback B S hS (IsPullback.of_hasPullback q f) hq
  have hchart : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
      (w ≫ Limits.pullback.snd q f) := by
    have := isMultiplicative_presheaf_etale B S hS
    exact MorphismProperty.comp_mem _ _ _ (presheaf_etale_of_isEtale B S hS hwEt) hsnd
  have hWred : IsReduced (T.obj W) :=
    (exists_atlas_iff_forall_etale B S hS Y (fun Z : Scheme.{u} => IsReduced Z) hY).mp
      hYred W (w ≫ Limits.pullback.snd q f) hchart
  -- the cover maps to the chart, and that morphism of schemes is of finite type
  let m : W ⟶ V := yoneda.preimage (w ≫ Limits.pullback.fst q f)
  have hm : yoneda.map m = w ≫ Limits.pullback.fst q f := yoneda.map_preimage _
  have hmft : LocallyOfFiniteType (T.map m) := by
    refine hft.1 W V (w ≫ Limits.pullback.snd q f) q m hchart hq ?_
    rw [hm, Category.assoc, Category.assoc, Limits.pullback.condition]
  -- the comparison of the cover with the base change of the normalization
  have hwfac : (w ≫ Limits.pullback.snd q f ≫ f') ≫ ν = (w ≫ Limits.pullback.fst q f) ≫ q := by
    rw [Category.assoc, Category.assoc, hnorm.fac, Category.assoc, Limits.pullback.condition]
  let c : W ⟶ hrepν.1.pullback q :=
    yoneda.preimage (hpb.lift (w ≫ Limits.pullback.snd q f ≫ f')
      (w ≫ Limits.pullback.fst q f) hwfac)
  have hc : yoneda.map c =
      hpb.lift (w ≫ Limits.pullback.snd q f ≫ f') (w ≫ Limits.pullback.fst q f) hwfac :=
    yoneda.map_preimage _
  have hcfst : yoneda.map c ≫ hrepν.1.fst q = w ≫ Limits.pullback.snd q f ≫ f' := by
    rw [hc]; exact hpb.lift_fst _ _ _
  have hcsnd : c ≫ hrepν.1.snd q = m := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hc, hpb.lift_snd, hm]
  -- the sections of the base change embed in those of the cover
  have hinj := hdom V (hrepν.1.pullback q) W q (hrepν.1.snd q) (hrepν.1.fst q) w c hV hWaff hq
    hpb hwSurj hwEt hcfst
  have hcomp : LocallyOfFiniteType (T.map c ≫ T.map (hrepν.1.snd q)) := by
    rw [← Functor.map_comp, hcsnd]; exact hmft
  exact isFinite_of_isIntegralHom_of_injective_appTop
    (T.map (hrepν.1.snd q)) (T.map c) hVnag hinj

end Space

end AlgebraicGeometry

end
