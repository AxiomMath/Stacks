module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local finite type through an integral, injective map of affines

This file proves the commutative-algebra and étale-local step of Stacks 0DUX. Let `A ⟶ M` be an
integral morphism of affine schemes which is injective on global sections, and let `M ⟶ Y` be a
morphism to a locally Noetherian algebraic space such that `A ⟶ M ⟶ Y` is locally of finite type.
Then `M ⟶ Y` is locally of finite type.

On an affine étale chart `U ⟶ M` over an affine étale chart `V ⟶ Y` the base change
`A ×_M U ⟶ U` is again integral, affine, and injective on global sections (`U ⟶ M` being flat),
and `A ×_M U ⟶ V` is locally of finite type. The ring `Γ(V)` is Noetherian, so the Artin–Tate
lemma (Stacks 00IS, Mathlib's `fg_of_fg_of_fg`) applies to `Γ(V) ⟶ Γ(U) ⟶ Γ(A ×_M U)`: the
second map is injective and finite (integral and of finite type), so the first is of finite type.

## Main results

* `RingHom.FiniteType.of_comp_of_isIntegral_of_injective`: the Artin–Tate step for ring maps.
* `AlgebraicGeometry.locallyOfFiniteType_of_isIntegralHom_of_injective_appTop`: the affine
  scheme statement over a Noetherian affine base.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isIntegralHom_of_injective_appTop`: the
  statement over a locally Noetherian algebraic space.

## References

* [Stacks Project, Tag 0DUX](https://stacks.math.columbia.edu/tag/0DUX)
* [Stacks Project, Tag 00IS](https://stacks.math.columbia.edu/tag/00IS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **Artin–Tate for ring maps (Stacks 00IS).** Let `R` be Noetherian, `f : R →+* C` and
`g : C →+* A` with `g` injective and integral. If `g ∘ f` is of finite type, so is `f`. -/
@[sga "3 V 6.1"]
theorem RingHom.FiniteType.of_comp_of_isIntegral_of_injective
    {R C A : Type*} [CommRing R] [CommRing C] [CommRing A] [IsNoetherianRing R]
    (f : R →+* C) (g : C →+* A) (hg : Function.Injective g) (hint : g.IsIntegral)
    (hfg : (g.comp f).FiniteType) : f.FiniteType := by
  let : Algebra R C := f.toAlgebra
  let : Algebra C A := g.toAlgebra
  let : Algebra R A := (g.comp f).toAlgebra
  have : IsScalarTower R C A := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FiniteType R A := hfg
  have : Algebra.IsIntegral C A := ⟨hint⟩
  have : Algebra.FiniteType C A := Algebra.FiniteType.of_restrictScalars_finiteType R C A
  have : Module.Finite C A :=
    (Algebra.finite_iff_isIntegral_and_finiteType (R := C) (A := A)).2
      ⟨inferInstance, inferInstance⟩
  exact ⟨fg_of_fg_of_fg R C A Algebra.FiniteType.out (Module.Finite.fg_top (R := C) (M := A)) hg⟩

namespace AlgebraicGeometry

/-- **The affine statement.** Let `a : A ⟶ M` be an integral morphism of affine schemes which is
injective on global sections, and `q : M ⟶ Y` a morphism to a Noetherian affine scheme with
`a ≫ q` locally of finite type. Then `q` is locally of finite type. -/
theorem locallyOfFiniteType_of_isIntegralHom_of_injective_appTop
    {A M Y : Scheme.{u}} [IsAffine A] [IsAffine M] [IsAffine Y] [IsLocallyNoetherian Y]
    (a : A ⟶ M) [IsIntegralHom a] (hinj : Function.Injective a.appTop.hom)
    (q : M ⟶ Y) [LocallyOfFiniteType (a ≫ q)] : LocallyOfFiniteType q := by
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have hint : RingHom.IsIntegral a.appTop.hom :=
    ((@HasAffineProperty.iff_of_isAffine _ _ IsIntegralHom.hasAffineProperty.{u} _ _ a _).1
      inferInstance).2
  apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).2
  refine RingHom.FiniteType.of_comp_of_isIntegral_of_injective q.appTop.hom a.appTop.hom hinj
    hint ?_
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
    HasRingHomProperty.appTop (@LocallyOfFiniteType) (a ≫ q) inferInstance

/-- **Injectivity on global sections survives flat base change of affine schemes.** -/
theorem injective_appTop_of_isPullback_of_flat
    {A M U P : Scheme.{u}} [IsAffine A] [IsAffine M] [IsAffine U]
    {a : A ⟶ M} {b : U ⟶ M} {fst : P ⟶ A} {snd : P ⟶ U}
    (h : IsPullback fst snd a b) [Flat b] (hinj : Function.Injective a.appTop.hom) :
    Function.Injective snd.appTop.hom := by
  have hpush := isPushout_appTop_of_isPullback h
  rw [← hpush.inr_isoPushout_inv]
  exact (ConcreteCategory.bijective_of_isIso hpush.isoPushout.inv).injective.comp
    (CommRingCat.inr_injective_of_flat a.appTop b.appTop hinj
      (HasRingHomProperty.appTop (@Flat) b inferInstance))

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Local finite type may be tested on squares of affine étale charts.** -/
theorem isLocallyOfFiniteType_of_affine_etale_charts
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : ∀ (U V : BigFppfOver B S hS)
      (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
      (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
      (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (g : U ⟶ V),
      (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a →
      (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b →
      yoneda.map g ≫ b = a ≫ f → LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g)) :
    IsLocallyOfFiniteType B S hS f := by
  intro U V a b g ha hb hcomm
  let : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun sq h => MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
      (sq.map (BigFppfOver.toScheme B S hS)) h⟩
  let : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  let : IsZariskiLocalAtTarget @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFiniteType
  let : MorphismProperty.RespectsRight (@LocallyOfFiniteType)
      (@AlgebraicGeometry.IsOpenImmersion) :=
    ⟨fun _ _ _ _ => inferInstance⟩
  apply (IsZariskiLocalAtSource.iff_exists_resLE (P := @LocallyOfFiniteType)).2
  intro x
  obtain ⟨V₀, hV₀, hxV₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := V.left.obj) (x := g.left.hom x) (U := ⊤) trivial
  obtain ⟨U₀, hU₀, hxU₀, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (X := U.left.obj) (x := x) (U := g.left.hom ⁻¹ᵁ V₀) hxV₀
  refine ⟨V₀, U₀, hxU₀, hUV, ?_⟩
  have : IsAffine U₀.toScheme := hU₀
  have : IsAffine V₀.toScheme := hV₀
  have hUm : B.Contains U₀.toScheme :=
    (Scheme.size_le_of_locallyOfFiniteType U₀.ι).trans_lt U.left.property
  have hVm : B.Contains V₀.toScheme :=
    (Scheme.size_le_of_locallyOfFiniteType V₀.ι).trans_lt V.left.property
  let U' : BigFppfOver B S hS := Over.mk (⟨U₀.ι ≫ U.hom.hom⟩ : B.obj hUm ⟶ B.obj hS)
  let V' : BigFppfOver B S hS := Over.mk (⟨V₀.ι ≫ V.hom.hom⟩ : B.obj hVm ⟶ B.obj hS)
  let iU : U' ⟶ U := Over.homMk (ObjectProperty.homMk U₀.ι) rfl
  let iV : V' ⟶ V := Over.homMk (ObjectProperty.homMk V₀.ι) rfl
  let g' : U' ⟶ V' := Over.homMk (ObjectProperty.homMk (g.left.hom.resLE V₀ U₀ hUV)) (by
    apply ObjectProperty.hom_ext
    show (g.left.hom.resLE V₀ U₀ hUV) ≫ V₀.ι ≫ V.hom.hom = U₀.ι ≫ U.hom.hom
    rw [reassoc_of% (Scheme.Hom.resLE_comp_ι g.left.hom hUV)]
    exact congrArg (fun k => U₀.ι ≫ k.hom) g.w)
  apply hf U' V' hU₀ hV₀ (yoneda.map iU ≫ a) (yoneda.map iV ≫ b) g'
  · apply MorphismProperty.comp_mem _ _ _ _ ha
    apply MorphismProperty.relative_map
    exact inferInstanceAs (Etale U₀.ι)
  · apply MorphismProperty.comp_mem _ _ _ _ hb
    apply MorphismProperty.relative_map
    exact inferInstanceAs (Etale V₀.ι)
  · have hg' : g' ≫ iV = iU ≫ g := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact Scheme.Hom.resLE_comp_ι _ _
    rw [← Category.assoc, ← yoneda.map_comp, hg', yoneda.map_comp, Category.assoc, hcomm,
      Category.assoc]

/-- **The space statement (the core of Stacks 0DUX).** Let `a : A ⟶ M` be a morphism of the big
fppf site between objects with affine underlying schemes which is integral and injective on global
sections, and let `q : h_M ⟶ Y` be a morphism to a locally Noetherian algebraic space such that
`h_A ⟶ h_M ⟶ Y` is locally of finite type. Then `q` is locally of finite type. -/
theorem isLocallyOfFiniteType_of_isIntegralHom_of_injective_appTop
    (A M : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj A)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj M)] (a : A ⟶ M)
    [AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map a)]
    (hinj : Function.Injective ((BigFppfOver.toScheme B S hS).map a).appTop.hom)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hYa : IsAlgebraicSpace B S hS Y)
    (hY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (q : yoneda.obj M ⟶ Y) (hcomp : IsLocallyOfFiniteType B S hS (yoneda.map a ≫ q)) :
    IsLocallyOfFiniteType B S hS q := by
  apply isLocallyOfFiniteType_of_affine_etale_charts B S hS q
  intro U V hU hV c b g hc hb hcomm
  let T := BigFppfOver.toScheme B S hS
  let j : U ⟶ M := yoneda.preimage c
  have hj : Etale (T.map j) := by
    apply MorphismProperty.of_relative_map (F := yoneda)
      (P := MorphismProperty.inverseImage (@Etale) T)
    simpa only [j, Functor.map_preimage] using hc
  have hsq := (IsPullback.of_hasPullback a j).map T
  have : Etale (T.map (pullback.fst a j)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip hj
  have : AlgebraicGeometry.IsIntegralHom (T.map (pullback.snd a j)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq
      (inferInstanceAs (AlgebraicGeometry.IsIntegralHom (T.map a)))
  have : IsAffine (T.obj (pullback a j)) := isAffine_of_isAffineHom (T.map (pullback.snd a j))
  have : IsLocallyNoetherian (T.obj V) :=
    (exists_atlas_iff_forall_etale B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T)
      hYa).1 hY V b hb
  have hft := isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS A) hYa (yoneda.map (pullback.fst a j)) (yoneda.map a ≫ q)
    ((isLocallyOfFiniteType_yoneda_map_iff B S hS _).2 inferInstance) hcomp
  have heq : yoneda.map (pullback.fst a j) ≫ (yoneda.map a ≫ q) =
      yoneda.map (pullback.snd a j ≫ g) ≫ b := by
    rw [← Category.assoc, ← yoneda.map_comp, pullback.condition, yoneda.map_comp,
      Category.assoc, show yoneda.map j = c from yoneda.map_preimage c, ← hcomm,
      ← Category.assoc, ← yoneda.map_comp]
  rw [heq] at hft
  have hg := isLocallyOfFiniteType_of_comp B S hS (isAlgebraicSpace_yoneda B S hS _)
    (isAlgebraicSpace_yoneda B S hS V) hYa (yoneda.map (pullback.snd a j ≫ g)) b hft
  have : LocallyOfFiniteType (T.map (pullback.snd a j) ≫ T.map g) := by
    rw [← T.map_comp]
    exact (isLocallyOfFiniteType_yoneda_map_iff B S hS _).1 hg
  exact locallyOfFiniteType_of_isIntegralHom_of_injective_appTop (T.map (pullback.snd a j))
    (injective_appTop_of_isPullback_of_flat hsq hinj) (T.map g)

end Space

end AlgebraicGeometry

end
