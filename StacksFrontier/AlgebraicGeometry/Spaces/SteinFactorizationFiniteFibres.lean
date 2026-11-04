module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.GoingUp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedAffineBase
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.FiniteFibres

/-!
# Finite fibres of the Stein projection over an affine base

Let `f : X ⟶ Y` be a universally closed morphism of algebraic spaces over a scheme `S` and let
`X ⟶ Y' ⟶ Y` be its Stein factorization (Stacks 0A19).  Assume in addition that `f` is locally
of finite type and that `Y` is affine.  Then `Y'` is an affine scheme over `Y`, every fibre of
`π : Y' ⟶ Y` is a finite set, and every residue field extension `κ(y')/κ(π y')` is finite.
This file proves the scheme-level core of that statement and the reduction to it; Stacks 0E1C
itself is `AlgebraicGeometry.Space.exists_isAffine_finite_fibres_normalizationInQcqs` in
`StacksFrontier/AlgebraicGeometry/Spaces/SteinFactorizationQcqsFiniteFibres.lean`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.finite_preimage_singleton_of_surjective_of_locallyOfFiniteType` and
  `AlgebraicGeometry.finite_residueFieldMap_of_surjective_of_locallyOfFiniteType` are the
  scheme-level core: an integral morphism `π : W ⟶ V` which is surjectively dominated by a
  scheme locally of finite type over `V` has finite residue field extensions, and finite
  fibres as soon as that dominating scheme is compact.

## Implementation notes

Residue fields are read in the scheme `Y'`, as they must be: the quotient model of the points
of an algebraic space carries no residue fields.

Since `f` is quasi-compact and `Y` is affine, `X` is a quasi-compact algebraic space and so
has a surjective étale chart `a : h_U ⟶ X` whose scheme `U` is compact.  The composite
`U ⟶ Y'` is then a surjective morphism of schemes and `U ⟶ Y` is locally of finite type, which
is all the scheme-level core needs.  That core follows the source's argument: the fibre `U_y`
is a Noetherian topological space and maps onto `π⁻¹({y})`, which is T1 because `π` is integral
(Stacks 00GT), and a Noetherian sober space whose points are closed is finite; for the residue
fields, `U_y` is a Jacobson space, so a point of `π⁻¹({y})` is the image of a point of `U`
closed in its `U ⟶ Y`-fibre, whose residue field is finite over `κ(y)` by Stacks 01TA, and
`κ(y')` embeds into it over `κ(y)`.

## References

* [Stacks Project, Tag 0E1C](https://stacks.math.columbia.edu/tag/0E1C)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Topological and ring-theoretic preliminaries -/

/-- **Stacks 00GT**, geometrically. The fibre of an integral morphism of schemes over a point
is a T1 space: it is affine and its ring of global sections is integral over the residue field
of the point, so all of its primes are maximal. -/
private theorem t1Space_fiber_of_integral {Y Z : Scheme.{u}} (g : Z ⟶ Y) [IsIntegralHom g]
    (y : Y) : T1Space (g.fiber y) := by
  have : IsIntegralHom (g.fiberToSpecResidueField y) :=
    inferInstanceAs (IsIntegralHom (Limits.pullback.snd g (Y.fromSpecResidueField y)))
  have : IsAffine (g.fiber y) := inferInstance
  have : AlgebraicGeometry.IsIntegral (Spec (Y.residueField y)) :=
    (affine_isIntegral_iff _).mpr inferInstance
  have hR : IsField Γ(Spec (Y.residueField y), ⊤) :=
    isField_of_isIntegral_of_subsingleton _
  have hint := (g.fiberToSpecResidueField y).isIntegral_app ⊤ (isAffineOpen_top _)
  have : Ring.KrullDimLE 0 Γ(g.fiber y, ⊤) :=
    Stacks.SteinFactorization.krullDimLE_zero_of_isIntegral _ hint hR
  have : T1Space (Spec Γ(g.fiber y, ⊤)) :=
    ⟨fun p ↦ (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2 p.2.isMaximal'⟩
  exact (g.fiber y).isoSpec.inv.homeomorph.t1Space

/-! ### The scheme-level core -/

section SchemeCore

variable {U W V : Scheme.{u}} (g : U ⟶ W) (π : W ⟶ V)

/-- A point of the source mapping to `v` comes from the fibre over `v`. -/
private theorem exists_fiberι_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {v : Y} {x : X} (h : f x = v) :
    ∃ z : f.fiber v, f.fiberι v z = x := by
  have : x ∈ Set.range (f.fiberι v) := by rw [f.range_fiberι v]; exact h
  exact this

private theorem mem_preimage_apply_fiberι (v : V) (u : (g ≫ π).fiber v) :
    g ((g ≫ π).fiberι v u) ∈ π ⁻¹' {v} := by
  simp only [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply]
  exact (g ≫ π).apply_fiberι v u

/-- The map from the fibre of `g ≫ π` over `v` to the fibre of `π` over `v` induced by `g`. -/
private noncomputable def compFiberMap (v : V) (u : (g ≫ π).fiber v) : π.fiber v :=
  (π.fiberHomeo v).symm ⟨_, mem_preimage_apply_fiberι g π v u⟩

private theorem fiberι_compFiberMap (v : V) (u : (g ≫ π).fiber v) :
    π.fiberι v (compFiberMap g π v u) = g ((g ≫ π).fiberι v u) := by
  simp [compFiberMap]

private theorem continuous_compFiberMap (v : V) : Continuous (compFiberMap g π v) :=
  (π.fiberHomeo v).symm.continuous.comp
    (Continuous.subtype_mk (g.continuous.comp ((g ≫ π).fiberι v).continuous)
      (mem_preimage_apply_fiberι g π v))

private theorem surjective_compFiberMap (hg : Function.Surjective g) (v : V) :
    Function.Surjective (compFiberMap g π v) := by
  intro x
  obtain ⟨u₀, hu₀⟩ := hg (π.fiberι v x)
  have hcomp : (g ≫ π) u₀ = v := by
    rw [Scheme.Hom.comp_apply, hu₀]
    exact π.apply_fiberι v x
  obtain ⟨u, hu⟩ := exists_fiberι_eq (g ≫ π) hcomp
  refine ⟨u, ?_⟩
  apply (π.fiberHomeo v).injective
  exact Subtype.ext (by simp [compFiberMap, hu, hu₀])

private theorem noetherianSpace_fiber_comp [CompactSpace U] [LocallyOfFiniteType (g ≫ π)]
    (v : V) : NoetherianSpace ((g ≫ π).fiber v) := by
  have : IsLocallyNoetherian ((g ≫ π).fiber v) :=
    inferInstanceAs (IsLocallyNoetherian (Limits.pullback (g ≫ π) (V.fromSpecResidueField v)))
  have : CompactSpace ((g ≫ π).fiber v) :=
    inferInstanceAs (CompactSpace ↑(Limits.pullback (g ≫ π) (V.fromSpecResidueField v)))
  have : IsNoetherian ((g ≫ π).fiber v) := ⟨⟩
  infer_instance

/-- An integral morphism of schemes `π : W ⟶ V` which is surjectively dominated by a compact
scheme locally of finite type over `V` has finite fibres.

This is the scheme-level core of **Stacks 0E1C**: the fibre of `g ≫ π` over `v` is a Noetherian
topological space and maps onto `π ⁻¹' {v}`, which is sober and, `π` being integral, T1. -/
theorem finite_preimage_singleton_of_surjective_of_locallyOfFiniteType [CompactSpace U]
    [IsIntegralHom π] [LocallyOfFiniteType (g ≫ π)]
    (hg : Function.Surjective g) (v : V) : (π ⁻¹' {v}).Finite := by
  have : NoetherianSpace ((g ≫ π).fiber v) := noetherianSpace_fiber_comp g π v
  have : NoetherianSpace (π.fiber v) :=
    noetherianSpace_of_surjective _ (continuous_compFiberMap g π v)
      (surjective_compFiberMap g π hg v)
  have : T1Space (π.fiber v) := Stacks.SteinFactorization.t1Space_fiber_of_isIntegralHom π v
  have : Finite (π.fiber v) := Stacks.SteinFactorization.finite_of_noetherianSpace_of_t1Space _
  have : Finite ↥(π ⁻¹' {v}) := Finite.of_equiv _ (π.fiberHomeo v).toEquiv
  exact Set.finite_coe_iff.mp this

/-- Every point of `W` is the image under `g` of a point of `U` which is closed in its
`g ≫ π`-fibre. -/
private theorem exists_isClosed_inter_eq_singleton [IsIntegralHom π]
    [LocallyOfFiniteType (g ≫ π)] (hg : Function.Surjective g) (w : W) :
    ∃ u : U, g u = w ∧ ∃ D : Set U, IsClosed D ∧ D ∩ (g ≫ π) ⁻¹' {(g ≫ π) u} = {u} := by
  set v := π w with hv
  obtain ⟨x, hx⟩ := exists_fiberι_eq π hv.symm
  have : T1Space (π.fiber v) := Stacks.SteinFactorization.t1Space_fiber_of_isIntegralHom π v
  have hpre : IsClosed (compFiberMap g π v ⁻¹' {x}) :=
    (isClosed_singleton (x := x)).preimage (continuous_compFiberMap g π v)
  obtain ⟨u₀, hu₀⟩ := surjective_compFiberMap g π hg v x
  have : JacobsonSpace ((g ≫ π).fiber v) := inferInstance
  obtain ⟨u', hu'Z, hu'cl⟩ :=
    nonempty_inter_closedPoints (X := (g ≫ π).fiber v) ⟨u₀, hu₀⟩ hpre.isLocallyClosed
  have hu'x : compFiberMap g π v u' = x := hu'Z
  refine ⟨(g ≫ π).fiberι v u', ?_, ?_⟩
  · rw [← hx, ← hu'x, fiberι_compFiberMap]
  · have hfx : (g ≫ π) ((g ≫ π).fiberι v u') = v := (g ≫ π).apply_fiberι v u'
    set e := (g ≫ π).fiberHomeo v with he
    have himg : IsClosed ({e u'} : Set ↥((g ≫ π) ⁻¹' {v})) := by
      have h := e.isClosedMap {u'} hu'cl
      rwa [Set.image_singleton] at h
    obtain ⟨D, hD, hDeq⟩ := isClosed_induced_iff.mp himg
    refine ⟨D, hD, ?_⟩
    rw [hfx]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hyD, hyv⟩
      have hy : (⟨y, hyv⟩ : ↥((g ≫ π) ⁻¹' {v})) ∈ Subtype.val ⁻¹' D := hyD
      rw [hDeq] at hy
      exact congrArg Subtype.val hy
    · rintro rfl
      refine ⟨?_, hfx⟩
      have hy : (e u') ∈ Subtype.val ⁻¹' D := by rw [hDeq]; rfl
      exact hy

/-- An integral morphism of schemes `π : W ⟶ V` which is surjectively dominated by a scheme
locally of finite type over `V` has finite residue field extensions.

This is the scheme-level core of **Stacks 0E1C**: a point `w` of `W` is the image of a point
`u` of `U` closed in its `g ≫ π`-fibre, so `κ(u)` is finite over `κ(π w)` by Stacks 01TA, and
`κ(w)` embeds into `κ(u)` over `κ(π w)`. -/
@[ega "I 6.4.2" "special case"]
theorem finite_residueFieldMap_of_surjective_of_locallyOfFiniteType [IsIntegralHom π]
    [LocallyOfFiniteType (g ≫ π)] (hg : Function.Surjective g) (w : W) :
    (π.residueFieldMap w).hom.Finite := by
  obtain ⟨u, hu, D, hD, hDu⟩ := exists_isClosed_inter_eq_singleton g π hg w
  have key : ((g ≫ π).residueFieldMap u).hom.Finite :=
    Stacks.SteinFactorization.finite_residueFieldMap_of_isClosed_inter (g ≫ π) u hD hDu
  rw [Scheme.residueFieldMap_comp] at key
  rw [← hu]
  exact Stacks.SteinFactorization.hom_finite_of_comp _ _ (g.residueFieldMap u).hom.injective key

end SchemeCore

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reduction of the Stein projection to a morphism of schemes -/

/-- Let `φ = f' ≫ π : X ⟶ G` be a factorization of presheaves with `f'` surjective on points,
`φ` quasi-compact and locally of finite type, and let `b` and `e` present `G` and the
intermediate presheaf by objects `T` and `T'` of the site with `T` affine, compatibly with a
morphism `p : T' ⟶ T` of the site.  Then `X` has a surjective étale chart whose scheme `U` is
compact, and the induced `U ⟶ T'` is surjective with `U ⟶ T` locally of finite type. -/
private theorem exists_compact_chart_scheme_data
    {X G Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    {π : Z ⟶ G} {f' : X ⟶ Z} {φ : X ⟶ G} (hfac : f' ≫ π = φ)
    {T T' : BigFppfOver B S hS} (b : yoneda.obj T ⟶ G) [IsIso b]
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (e : yoneda.obj T' ⟶ Z) [IsIso e] (p : T' ⟶ T)
    (hsq : yoneda.map p ≫ b = e ≫ π)
    (hsurj : IsSurjective B S hS f')
    (hqcφ : IsQuasiCompact B S hS φ)
    (hlftφ : IsLocallyOfFiniteType B S hS φ) :
    ∃ (U : BigFppfOver B S hS) (g : U ⟶ T'),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
      Function.Surjective ((BigFppfOver.toScheme B S hS).map g) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g ≫
        (BigFppfOver.toScheme B S hS).map p) := by
  have hGqc : IsQuasiCompactSpace B S hS G :=
    isQuasiCompactSpace_of_iso B S hS (asIso b)
      (isAffineSpace_yoneda B S hS T hT).isQuasiCompactSpace
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hG hGqc hqcφ
  obtain ⟨U, a, hUcpt, hasurj, haetale⟩ := hXqc
  obtain ⟨g, hgmap⟩ := Yoneda.fullyFaithful.map_surjective (a ≫ f' ≫ inv e)
  refine ⟨U, g, hUcpt, ?_, ?_⟩
  · have hpts : Function.Surjective (pointsMap B S hS (yoneda.obj U) (yoneda.map g)) := by
      rw [hgmap, pointsMap_comp, pointsMap_comp]
      exact (((bijective_pointsMap_of_isIso B S hS (inv e)).2).comp hsurj).comp
        (isSurjective_of_presheafSurjective B S hS a hasurj)
    have hsurj' : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map g) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).mp
        ((surjective_yonedaMap_iff_surjective_pointsMap B S hS _).mpr hpts)
    exact (AlgebraicGeometry.surjective_iff _).mp hsurj'
  · have h0 : MorphismProperty.ContainsIdentities
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    have h0' : MorphismProperty.RespectsIso
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have h1 : MorphismProperty.ContainsIdentities
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
    have h2 : MorphismProperty.RespectsIso
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
    have hbet : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b :=
      MorphismProperty.presheaf_of_isIso _ b
    have hsq2 : yoneda.map (g ≫ p) ≫ b = a ≫ φ := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc, hsq, hgmap, ← hfac]
      simp [Category.assoc]
    have := hlftφ U T a b (g ≫ p) (presheaf_etale_of_isEtale B S hS haetale) hbet hsq2
    rwa [CategoryTheory.Functor.map_comp] at this

variable (E : AffineAlgebraAntiEquivalence B S hS) (C : BaseChangeCompatibility B S hS E)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hqcoh : (pushforwardAlgebra B S hS (Over.mk f)).IsQuasicoherent)
    (hqcoh' : (AlgebraSheaf.integralClosureSheaf
      (pushforwardAlgebra B S hS (Over.mk f))).IsQuasicoherent)
    (hid : pushforwardAlgebra B S hS (idAffineOver B S hS X).obj ≅ unitAlgebra B S hS X)

end AlgebraicGeometry.Space

end
