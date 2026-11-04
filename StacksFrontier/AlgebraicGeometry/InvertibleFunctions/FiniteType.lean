module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProjectiveSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.AffineSpaceImmersion.Projective
public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.NormalModel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced

/-!
# Invertible functions on an integral scheme locally of finite type over a field

Let `k` be an algebraically closed field and let `X` be an integral scheme locally of finite type
over `k`.  Then the group `𝒪^*(X)/k^*` of invertible global functions modulo the constants is a
finitely generated abelian group.  This is Stacks Tag 04L5.

The argument reduces to Tag 04L4, the case of a normal open subscheme of a proper variety.  A
morphism of schemes over `k` which is injective on global sections induces an injection of the
two quotient groups, and a commutative group embedding in a finitely generated one is finitely
generated; so the problem for `X` may be replaced by the problem for the normalization of `X`,
and then by the problem for an affine open of that normalization.  An affine integral scheme
locally of finite type over `k` immerses into a projective space over `k`, and the
scheme-theoretic image of that immersion is a proper variety in which it is a dense open
subscheme.

## Main results

* `AlgebraicGeometry.fg_units_quotient_of_injective_appTop`: finite generation passes from a
  scheme to any scheme over it on which it is injective on global sections.
* `AlgebraicGeometry.exists_properVariety_model_of_isAffine`: an affine integral scheme locally
  of finite type over a field is an open subscheme of a proper variety over that field.
* `AlgebraicGeometry.fg_units_quotient_of_isAffine_isNormal` and
  `AlgebraicGeometry.fg_units_quotient_of_isNormal`: Tag 04L5 for a normal scheme, first affine
  and then in general.
* `AlgebraicGeometry.fg_units_quotient_of_locallyOfFiniteType`: Tag 04L5.

## References

* [Stacks Project, Tag 04L5](https://stacks.math.columbia.edu/tag/04L5)
* [Stacks Project, Tag 04L4](https://stacks.math.columbia.edu/tag/04L4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Let `g : W ⟶ Spec k` be a scheme over a field and let `h : V ⟶ W` be a morphism which is
injective on global sections.  If the invertible functions on `V` modulo the constants form a
finitely generated group, then so do the invertible functions on `W`.

The induced map of quotients is injective, and a commutative group embedding in a finitely
generated commutative group is finitely generated. -/
theorem fg_units_quotient_of_injective_appTop (k : Type u) [Field k] {V W : Scheme.{u}}
    (g : W ⟶ Spec (.of k)) (h : V ⟶ W) (hinj : Function.Injective h.appTop.hom)
    (hFG : Group.FG (Γ(V, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (h ≫ g).appTop).hom).toMonoidHom).range)) :
    Group.FG (Γ(W, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toMonoidHom).range) := by
  have := hFG
  set φW : k →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom with hφW
  set φV : k →+* Γ(V, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (h ≫ g).appTop).hom with hφV
  set m : Γ(W, ⊤)ˣ →* Γ(V, ⊤)ˣ := Units.map h.appTop.hom.toMonoidHom with hm
  have hminj : Function.Injective m := Units.map_injective hinj
  have h1 (c : kˣ) : m (Units.map φW.toMonoidHom c) = Units.map φV.toMonoidHom c := by
    refine Units.ext ?_
    rw [hφV, hφW, Scheme.Hom.comp_appTop, ← Category.assoc]
    rfl
  have hle : (Units.map φW.toMonoidHom).range ≤
      ((Units.map φV.toMonoidHom).range).comap m := by
    rintro u ⟨c, rfl⟩
    exact ⟨c, h1 c⟩
  refine Group.fg_of_injective (ψ := QuotientGroup.map _ _ m hle) ?_
  intro q₁ q₂ hq
  obtain ⟨u₁, rfl⟩ := QuotientGroup.mk_surjective q₁
  obtain ⟨u₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  rw [QuotientGroup.map_mk, QuotientGroup.map_mk, QuotientGroup.eq] at hq
  obtain ⟨c, hc⟩ := hq
  rw [QuotientGroup.eq]
  refine ⟨c, hminj ?_⟩
  rw [h1, hc, map_mul, map_inv]

/-- An affine integral scheme locally of finite type over a field is an open subscheme of a
proper variety over that field, compatibly with the structure morphisms.

Being affine and locally of finite type it admits an immersion into a projective space over the
field; the scheme-theoretic image of that immersion is a closed subscheme of the projective
space, hence proper over the field, and it is integral because its source is integral and maps
onto a dense subset.  A reduced immersion is an open immersion onto its scheme-theoretic
image. -/
theorem exists_properVariety_model_of_isAffine (k : Type u) [Field k] {Y : Scheme.{u}}
    [IsAffine Y] [IsIntegral Y] (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType g] :
    ∃ (Ybar : Scheme.{u}) (p : Ybar ⟶ Spec (.of k)) (_ : IsProperVariety k p) (j : Y ⟶ Ybar)
      (_ : IsOpenImmersion j), j ≫ p = g := by
  obtain ⟨n, i, hi, hig⟩ := AlgebraicGeometry.exists_immersion_projectiveSpace g
  have := hi
  have : QuasiSeparatedSpace (ProjectiveSpace n (Spec (.of k))) :=
    quasiSeparatedSpace_of_quasiSeparated (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k))
  have : IsOpenImmersion i.toImage := isOpenImmersion_toImage i (.inr inferInstance)
  have : IrreducibleSpace i.image := by
    refine (irreducibleSpace_def _).mpr ?_
    rw [Set.top_eq_univ, ← i.toImage.denseRange.closure_range]
    have himg := ((IrreducibleSpace.isIrreducible_univ Y).image _
      i.toImage.continuous.continuousOn).closure
    rwa [Set.image_univ] at himg
  have : IsIntegral i.image := isIntegral_of_irreducibleSpace_of_isReduced _
  set q : i.image ⟶ Spec (.of k) :=
    i.imageι ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) with hq
  have : IsProper q := by rw [hq]; infer_instance
  have : IsVariety k q := IsVariety.mk
  refine ⟨i.image, q, IsProperVariety.mk, i.toImage, inferInstance, ?_⟩
  rw [hq, ← Category.assoc, Scheme.Hom.toImage_imageι]
  exact hig

/-- **Stacks Tag 04L5 for an affine normal scheme.** Let `k` be an algebraically closed field and
let `Y` be an affine normal integral scheme locally of finite type over `k`.  Then the invertible
global functions on `Y` modulo the constants form a finitely generated group.

The scheme `Y` is an open subscheme of a proper variety over `k` and is normal, so this is
Tag 04L4. -/
theorem fg_units_quotient_of_isAffine_isNormal (k : Type u) [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} [IsAffine Y] [IsIntegral Y] [IsNormal Y] (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType g] :
    Group.FG (Γ(Y, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toMonoidHom).range) := by
  obtain ⟨Ybar, p, hp, j, hj, hjp⟩ := exists_properVariety_model_of_isAffine k g
  have := hp
  have := hj
  have hFG : Group.FG (Γ(Y, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ p).appTop).hom).toMonoidHom).range) :=
    fg_units_quotient_of_isOpenImmersion_into_properVariety k p j
  rw [hjp] at hFG
  exact hFG

/-- **Stacks Tag 04L5 for a normal scheme.** Let `k` be an algebraically closed field and let `X`
be a normal integral scheme locally of finite type over `k`.  Then the invertible global functions
on `X` modulo the constants form a finitely generated group.

Restriction to a nonempty affine open is injective on global sections, because a nonempty open of
an integral scheme is scheme-theoretically dense, and such an open is again normal, integral and
locally of finite type over `k`. -/
theorem fg_units_quotient_of_isNormal (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    [IsIntegral X] [IsNormal X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toMonoidHom).range) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨y, -⟩ := X.affineCover.covers x
  have : Nonempty (X.affineCover.X (X.affineCover.idx x)) := ⟨y⟩
  have : IsIntegral (X.affineCover.X (X.affineCover.idx x)) :=
    isIntegral_of_isOpenImmersion (X.affineCover.f (X.affineCover.idx x))
  have : IsNormal (X.affineCover.X (X.affineCover.idx x)) :=
    isNormal_of_iso (X.affineCover.f (X.affineCover.idx x)).isoOpensRange
  have : IsDominant (X.affineCover.f (X.affineCover.idx x)) :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
      (X.affineCover.f (X.affineCover.idx x)).isOpenEmbedding.isOpenMap⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant
    (X.affineCover.f (X.affineCover.idx x))
  refine fg_units_quotient_of_injective_appTop k f (X.affineCover.f (X.affineCover.idx x))
    (fun a b hab => (X.affineCover.f (X.affineCover.idx x)).app_injective ⊤ hab) ?_
  exact fg_units_quotient_of_isAffine_isNormal k
    (X.affineCover.f (X.affineCover.idx x) ≫ f)

/-- **Stacks Project, Tag 04L5.** Let `k` be an algebraically closed field and let `X` be an
integral scheme locally of finite type over `k`.  Then the group of invertible global functions on
`X` modulo the constants coming from `k` is a finitely generated abelian group.

The normalization `ν : X^ν ⟶ X` is finite, `X^ν` is a normal integral scheme locally of finite
type over `k`, and `ν` is dominant, hence injective on global sections; so the statement follows
from the normal case. -/
@[stacks 04L5]
theorem fg_units_quotient_of_locallyOfFiniteType (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    let φ : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
    Group.FG (Γ(X, ⊤)ˣ ⧸ (Units.map φ.toMonoidHom).range) := by
  intro φ
  have hfin := finite_irreducibleComponents_of_isIntegral X
  have := Scheme.quasiCompactFromGenericPointResidueFields X hfin
  have := Scheme.quasiSeparatedFromGenericPointResidueFields X
  have : IsFinite (X.normalization hfin) :=
    normalization_isFinite X (isJapaneseScheme_of_isNagataScheme X
      (isNagataScheme_of_locallyOfFiniteType_over_field k f))
  have : IsNormal (X.normalizationScheme hfin) := Scheme.isNormal_normalizationScheme X hfin
  refine fg_units_quotient_of_injective_appTop k f (X.normalization hfin)
    (fun a b hab => Stacks.AlgebraicGeometry.Normalization.injective_fromNormalization_app
      (Scheme.fromGenericPointResidueFields X) ⊤ hab) ?_
  exact fg_units_quotient_of_isNormal k (X.normalization hfin ≫ f)

end AlgebraicGeometry

end
