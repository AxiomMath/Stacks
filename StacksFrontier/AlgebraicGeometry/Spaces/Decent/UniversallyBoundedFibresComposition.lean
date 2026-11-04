module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedComposition
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Universally bounded fibres of a composite through a scheme

Let `X` be an algebraic space over `S`, let `V ⟶ U` be a morphism of schemes over `S` and let
`U ⟶ X` be a morphism over `S`. If the fibres of `V ⟶ U` and of `U ⟶ X` are universally
bounded, then so are the fibres of the composite `V ⟶ X`, and the product of the two bounds
is a bound for it.

The two notions of bounded fibres involved — that of Stacks 03JL for a morphism to a presheaf
and that of Stacks 03J4 for a morphism of schemes — agree for a morphism of schemes in the
site. One half tests a field-valued fibre at the spectrum of the residue field at a point,
which is again an object of the site because the canonical morphism from it is a quasi-compact
monomorphism; the other forms the fibre over a field-valued point of the site as a fibre
product taken in the site.

## Main results

* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_yoneda_map_iff`: for a morphism of
  schemes in the site, the two notions of universally bounded fibres agree — that of
  Stacks 03JL for the associated morphism of representable presheaves, and that of
  Stacks 03J4 for the morphism of schemes. Its two halves are
  `AlgebraicGeometry.Space.boundsFiberDegrees_toScheme_map_of_hasUniversallyBoundedFibers`
  and `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_yoneda_map_of_boundsFiberDegrees`.
* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_comp`: **Stacks 03JM**.
* `AlgebraicGeometry.exists_rank_le_of_boundsFiberDegrees_of_specTarget`: over the spectrum of a
  field, a bound on the degrees of the fibres is realised by a rank.

## Implementation notes

The target of the composite is an arbitrary presheaf on the big fppf site of `S` rather than an
algebraic space: only the degree bounds on field-valued fibres are used, and these make sense
for any presheaf.

Once the first morphism is replaced by its scheme-theoretic avatar, the argument is the
scheme-level bound for a composite, `AlgebraicGeometry.boundsFiberDegrees_comp` of Stacks 03J6,
applied to the base change of `V ⟶ U` along the fibre of `U ⟶ X` followed by that fibre. The
resulting bound is turned back into a rank by testing it on the base change along the identity
of the field spectrum, which is the morphism itself.

## References

* [Stacks Project, Tag 03JM](https://stacks.math.columbia.edu/tag/03JM)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 03J6](https://stacks.math.columbia.edu/tag/03J6)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-- A morphism to the spectrum of a field is finite locally free of some rank bounded by any
bound on the degrees of its fibres: the base change of the morphism along the identity of its
target is the morphism itself. -/
theorem exists_rank_le_of_boundsFiberDegrees_of_specTarget {k : Type u} [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of k)) {n : ℤ} (h : BoundsFiberDegrees g n) :
    ∃ r : ℕ, (r : ℤ) ≤ n ∧ IsFiniteLocallyFreeOfRank g r := by
  obtain ⟨r, hr, hrank⟩ := (boundsFiberDegrees_iff_field_baseChange g n).mp h k (𝟙 _)
  refine ⟨r, hr, ?_⟩
  have hsq : IsPullback (pullback.fst (𝟙 (Spec (CommRingCat.of k))) g)
      (pullback.snd (𝟙 (Spec (CommRingCat.of k))) g) (𝟙 _) g := IsPullback.of_hasPullback _ _
  have : IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of k))) g) := hsq.isIso_snd_of_isIso
  have h₁ : IsFiniteLocallyFreeOfRank.property r
      (pullback.snd (𝟙 (Spec (CommRingCat.of k))) g ≫ g) := by
    rw [← hsq.w]
    simpa using hrank
  exact ((IsFiniteLocallyFreeOfRank.property r).cancel_left_of_respectsIso _ _).mp h₁

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The object of the big fppf site of `S` given by the spectrum of the residue field at a point
of the scheme underlying an object `U`, with the structure morphism inherited from `U`. -/
noncomputable def residueFieldSiteObj (U : BigFppfOver B S hS)
    (y : (BigFppfOver.toScheme B S hS).obj U) : BigFppfOver B S hS :=
  Over.mk (⟨((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField y ≫ U.hom.hom⟩ :
    B.obj (Scheme.size_lt_of_mono_quasiCompact
      (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField y) U.left.property) ⟶
      B.obj hS)

/-- The canonical morphism to `U` from the spectrum of the residue field at a point of the
scheme underlying `U`, as a morphism of the site. -/
noncomputable def residueFieldSiteHom (U : BigFppfOver B S hS)
    (y : (BigFppfOver.toScheme B S hS).obj U) : residueFieldSiteObj B S hS U y ⟶ U :=
  Over.homMk ⟨((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField y⟩ rfl

/-- For a morphism of schemes in the big fppf site of `S`, a bound on the degrees of the
field-valued fibres of the associated morphism of representable presheaves bounds the degrees of
the scheme-theoretic fibres. -/
theorem boundsFiberDegrees_toScheme_map_of_hasUniversallyBoundedFibers
    {V U : BigFppfOver B S hS} (f : V ⟶ U)
    (hf : HasUniversallyBoundedFibers B S hS V (yoneda.map f)) :
    ∃ N : ℕ, BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map f) (N : ℤ) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n.toNat, fun y ↦ ?_⟩
  obtain ⟨W, q, i, r, hr, hrank, hpb⟩ :=
    hn (((BigFppfOver.toScheme B S hS).obj U).residueField y) (residueFieldSiteObj B S hS U y)
      (Iso.refl _) (yoneda.map (residueFieldSiteHom B S hS U y))
  obtain ⟨q', rfl⟩ : ∃ q' : W ⟶ V, yoneda.map q' = i := ⟨yoneda.preimage i, yoneda.map_preimage i⟩
  have hsiteSq : IsPullback q' q f (residueFieldSiteHom B S hS U y) :=
    IsPullback.of_map_of_faithful yoneda hpb
  have hschemeSq := hsiteSq.map (BigFppfOver.toScheme B S hS)
  rw [show (BigFppfOver.toScheme B S hS).map (residueFieldSiteHom B S hS U y) =
    ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField y from rfl] at hschemeSq
  have hfib := MorphismProperty.RespectsIso.precomp (IsFiniteLocallyFreeOfRank.property r)
    hschemeSq.isoPullback.inv ((BigFppfOver.toScheme B S hS).map q) hrank
  rw [hschemeSq.isoPullback_inv_snd] at hfib
  exact ⟨r, hr.trans (Int.self_le_toNat n), hfib⟩

/-- For a morphism of schemes in the big fppf site of `S`, a bound on the degrees of its
scheme-theoretic fibres bounds the degrees of the field-valued fibres of the associated
morphism of representable presheaves. A field-valued point of the target in the site is a
morphism of the site, so the fibre is a fibre product taken in the site. -/
theorem hasUniversallyBoundedFibers_yoneda_map_of_boundsFiberDegrees
    {V U : BigFppfOver B S hS} (f : V ⟶ U) (n : ℤ)
    (h : BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map f) n) :
    HasUniversallyBoundedFibers B S hS V (yoneda.map f) := by
  refine ⟨n, fun k _ T hT ξ ↦ ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t : T ⟶ U, yoneda.map t = ξ := ⟨yoneda.preimage ξ, yoneda.map_preimage ξ⟩
  have hsq : IsPullback (pullback.fst f t) (pullback.snd f t) f t := IsPullback.of_hasPullback f t
  have hbase : BoundsFiberDegrees
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f t)) n :=
    boundsFiberDegrees_of_isPullback (hsq.map (BigFppfOver.toScheme B S hS)) h
  have hiso : IsPullback (𝟙 ((BigFppfOver.toScheme B S hS).obj (pullback f t)))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f t) ≫ hT.hom)
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f t)) hT.inv :=
    IsPullback.of_horiz_isIso (CommSq.mk (by simp))
  have hfield : BoundsFiberDegrees
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f t) ≫ hT.hom) n :=
    boundsFiberDegrees_of_isPullback hiso hbase
  obtain ⟨r, hr, hrank⟩ := exists_rank_le_of_boundsFiberDegrees_of_specTarget _ hfield
  exact ⟨pullback f t, pullback.snd f t, yoneda.map (pullback.fst f t), r, hr,
    ((IsFiniteLocallyFreeOfRank.property r).cancel_right_of_respectsIso _ hT.hom).mp hrank,
    hsq.map yoneda⟩

/-- **Stacks 03JL** compared with **Stacks 03J4**: for a morphism of schemes in the big fppf
site of `S`, the fibres of the associated morphism of representable presheaves are universally
bounded exactly when the fibres of the morphism of schemes are. -/
theorem hasUniversallyBoundedFibers_yoneda_map_iff {V U : BigFppfOver B S hS} (f : V ⟶ U) :
    HasUniversallyBoundedFibers B S hS V (yoneda.map f) ↔
      _root_.AlgebraicGeometry.HasUniversallyBoundedFibers
        ((BigFppfOver.toScheme B S hS).map f) := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := boundsFiberDegrees_toScheme_map_of_hasUniversallyBoundedFibers B S hS f h
    exact ⟨(N : ℤ), hN⟩
  · rintro ⟨n, hn⟩
    exact hasUniversallyBoundedFibers_yoneda_map_of_boundsFiberDegrees B S hS f n hn

/-- **Stacks 03JM.** Let `X` be a presheaf on the big fppf site of `S`, let `f : V ⟶ U` be a
morphism of schemes over `S` and let `g : U ⟶ X` be a morphism over `S`. If the fibres of `f`
and of `g` are universally bounded, then so are the fibres of the composite `V ⟶ X`. -/
@[stacks 03JM]
theorem hasUniversallyBoundedFibers_comp
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V U : BigFppfOver B S hS}
    (f : V ⟶ U) (g : yoneda.obj U ⟶ X)
    (hf : HasUniversallyBoundedFibers B S hS V (yoneda.map f))
    (hg : HasUniversallyBoundedFibers B S hS U g) :
    HasUniversallyBoundedFibers B S hS V (yoneda.map f ≫ g) := by
  obtain ⟨N, hN⟩ :=
    boundsFiberDegrees_toScheme_map_of_hasUniversallyBoundedFibers B S hS f hf
  obtain ⟨m, hm⟩ := hg
  refine ⟨(N : ℤ) * max m 0, fun k _ A hA ξ ↦ ?_⟩
  obtain ⟨P, pA, i₀, r₀, hr₀, hrank₀, hP⟩ := hm k A hA ξ
  obtain ⟨pU, rfl⟩ : ∃ pU : P ⟶ U, yoneda.map pU = i₀ :=
    ⟨yoneda.preimage i₀, yoneda.map_preimage i₀⟩
  have hsite : IsPullback (pullback.fst f pU) (pullback.snd f pU) f pU :=
    IsPullback.of_hasPullback f pU
  -- The base change of `f` to the fibre of `g` still has fibre degrees bounded by `N`.
  have hbase : BoundsFiberDegrees
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f pU)) (N : ℤ) :=
    boundsFiberDegrees_of_isPullback (hsite.map (BigFppfOver.toScheme B S hS)) hN
  -- The fibre of `g` is finite locally free of degree `r₀` over the field spectrum.
  have hrank₀' : IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map pA ≫ hA.hom) r₀ :=
    ((IsFiniteLocallyFreeOfRank.property r₀).cancel_right_of_respectsIso _ hA.hom).mpr hrank₀
  have hcomp : BoundsFiberDegrees
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f pU) ≫
        ((BigFppfOver.toScheme B S hS).map pA ≫ hA.hom)) ((N : ℤ) * r₀) :=
    boundsFiberDegrees_comp _ _ _ _ (Int.natCast_nonneg N) hbase
      (boundsFiberDegrees_of_isFiniteLocallyFreeOfRank _ r₀)
  obtain ⟨r, hr, hrank⟩ := exists_rank_le_of_boundsFiberDegrees_of_specTarget _ hcomp
  refine ⟨pullback f pU, pullback.snd f pU ≫ pA, yoneda.map (pullback.fst f pU), r,
    hr.trans (mul_le_mul_of_nonneg_left (hr₀.trans (le_max_left m 0)) (Int.natCast_nonneg N)),
    ?_, ?_⟩
  · rw [Functor.map_comp]
    refine ((IsFiniteLocallyFreeOfRank.property r).cancel_right_of_respectsIso _ hA.hom).mp ?_
    rw [Category.assoc]
    exact hrank
  · rw [Functor.map_comp]
    exact IsPullback.paste_vert (hsite.map yoneda) hP

end Space

end AlgebraicGeometry

end
