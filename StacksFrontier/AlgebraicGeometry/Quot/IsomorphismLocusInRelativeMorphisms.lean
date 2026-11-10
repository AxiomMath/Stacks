module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismHom
public import Mathlib.CategoryTheory.Subfunctor.OfSection

/-!
# The isomorphism locus inside the relative morphism space (Stacks 0DPP)

Let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over a scheme `S` of a big
fppf site, with `z` flat, proper and of finite presentation and `x` separated and of finite
presentation, so that the relative morphism functor `Mor_Q(Z, X)` of Stacks 05Y2 is an algebraic
space locally of finite presentation over `Q` by Stacks 0D1C. A section of `Mor_Q(Z, X)` over a
test object `T` is a pair `(a, b)` of Stacks 05Y1: a morphism `a : T ⟶ Q` together with a
morphism `b : T ×_{a, Q} Z ⟶ X` lying over `Q`. Such a pair is the same thing as a morphism
`T ×_{a, Q} Z ⟶ T ×_{a, Q} X` over `T` — this is
`AlgebraicGeometry.Space.relativeMorphismEquivDiagram`, carrying the pair to
`AlgebraicGeometry.Space.RelativeMorphism.baseChangeMap` — and the pair deserves to be called a
*relative isomorphism* when that morphism is an isomorphism.

Stacks 0DPP asserts that, when in addition `x` is proper, the subfunctor
`Isom_Q(Z, X) ⊆ Mor_Q(Z, X)` of relative isomorphisms is an open subspace. This file constructs
that subfunctor and proves the assertion, following the source: the statement is the isomorphism
locus of Stacks 05XD for the universal relative morphism, the pair corresponding to the identity
of `Mor_Q(Z, X)` under the bijection of Stacks 05Y3.

## Main definitions

* `AlgebraicGeometry.Space.RelativeMorphism.IsRelativeIso`: a pair is a *relative isomorphism*
  when the morphism `T ×_{a, Q} Z ⟶ T ×_{a, Q} X` of base changes it determines is an
  isomorphism.
* `AlgebraicGeometry.Space.isomSubfunctor`: **Stacks 0DPP**, the subfunctor
  `Isom_Q(Z, X) ⊆ Mor_Q(Z, X)` of relative isomorphisms.

## Main results

* `AlgebraicGeometry.Space.RelativeMorphism.isRelativeIso_restrict`: a restriction of a relative
  isomorphism is a relative isomorphism. This is what makes the relative isomorphisms a
  subfunctor.
* `AlgebraicGeometry.Space.mem_isomSubfunctor_iff`: the sections of the subfunctor over a scheme
  are exactly the relative isomorphisms.
* `AlgebraicGeometry.Space.isOpenSubspace_isomSubfunctor`: **Stacks 0DPP**, the subfunctor is an
  open subspace.

## Implementation notes

The comparison between the two descriptions of a base change is the whole of the work. The
isomorphism locus of Stacks 05XD is an open subspace `W ⊆ Mor_Q(Z, X)` through which a morphism
`g : T ⟶ Mor_Q(Z, X)` factors exactly when the base change along `g` of the universal morphism
`Z_{Mor} ⟶ X_{Mor}` is an isomorphism, that base change being formed as
`AlgebraicGeometry.Space.baseChangeOverBase`, a fibre product over `Mor_Q(Z, X)`. The
subfunctor of relative isomorphisms, on the other hand, is described by the morphism of base
changes over `Q` attached to the restricted pair. The two agree up to the canonical isomorphism
between `T ×_{Mor} (Mor ×_Q Z)` and `T ×_Q Z`, which is provided here as
`CategoryTheory.Limits.pullback.isoMapFst`: both are cone points of cartesian squares on the
cospan formed by `g` and the projection `Mor ×_Q Z ⟶ Mor`, the first by
`CategoryTheory.Limits.pullback.isPullback_mapFst` and the second by the chosen fibre product.
Comparing the two morphisms is then two applications of
`CategoryTheory.Limits.pullback.hom_ext`, and it is also what makes the relative isomorphisms
closed under restriction, because `AlgebraicGeometry.Space.baseChangeOverBase` is manifestly a
base change and a base change of an isomorphism is an isomorphism.

The components of the morphism of base changes of a *restricted* pair are recorded separately,
as `AlgebraicGeometry.Space.baseChangeMap_restrict_comp_fst` and
`AlgebraicGeometry.Space.baseChangeMap_restrict_comp_snd`, with the first component of the
restricted pair written out as a composite: the general component lemmas hold of them only up to
unfolding `AlgebraicGeometry.Space.RelativeMorphism.restrict`, which happens in a type
ascription but not in the matching `rw` performs.

The algebraicity of `Mor_Q(Z, X)`, which is Stacks 0D1C and the standing fact of the source's
section, is an explicit hypothesis `hM` of
`AlgebraicGeometry.Space.isOpenSubspace_isomSubfunctor`. It cannot be dropped: being an *open
subspace* in the sense of Stacks 02YU includes being an algebraic space, and the finite
presentation and separatedness hypotheses on `x` of the source's section enter the statement only
through it.

Stacks 05XD is applied in the form
`AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isIso_baseChange`, which takes no further
input: its flat-locus ingredient, Stacks 05X3, is proved in the library.

## References

* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 05X3](https://stacks.math.columbia.edu/tag/05X3)
* [Stacks Project, Tag 05XD](https://stacks.math.columbia.edu/tag/05XD)
* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
* [Stacks Project, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-! ### Two base changes of a fibre product -/

namespace CategoryTheory.Limits

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- **The two base changes of `W ×_Y X` along `t : W' ⟶ W` agree.** Precomposing the first
factor with `t`, which is `CategoryTheory.Limits.pullback.mapFst`, exhibits `W' ×_Y X` as the
fibre product of `W ×_Y X` with `W'` over `W`, so it is canonically isomorphic to the chosen
such fibre product: both are cone points of cartesian squares on the same cospan. -/
noncomputable def pullback.isoMapFst {W W' X Y : C} (t : W' ⟶ W) (a : W ⟶ Y) (z : X ⟶ Y)
    [HasPullback a z] [HasPullback (t ≫ a) z] [HasPullback (pullback.fst a z) t] :
    pullback (t ≫ a) z ≅ pullback (pullback.fst a z) t :=
  (pullback.isPullback_mapFst t a z).isoIsPullback W' (pullback a z)
    (IsPullback.of_hasPullback (pullback.fst a z) t).flip

/-- The comparison isomorphism of the two base changes projects to the first factor of the
source. -/
@[reassoc (attr := simp)]
theorem pullback.isoMapFst_hom_comp_snd {W W' X Y : C} (t : W' ⟶ W) (a : W ⟶ Y) (z : X ⟶ Y)
    [HasPullback a z] [HasPullback (t ≫ a) z] [HasPullback (pullback.fst a z) t] :
    (pullback.isoMapFst t a z).hom ≫ pullback.snd (pullback.fst a z) t =
      pullback.fst (t ≫ a) z :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The comparison isomorphism of the two base changes is the comparison map of fibre
products. -/
@[reassoc (attr := simp)]
theorem pullback.isoMapFst_hom_comp_fst {W W' X Y : C} (t : W' ⟶ W) (a : W ⟶ Y) (z : X ⟶ Y)
    [HasPullback a z] [HasPullback (t ≫ a) z] [HasPullback (pullback.fst a z) t] :
    (pullback.isoMapFst t a z).hom ≫ pullback.fst (pullback.fst a z) t =
      pullback.mapFst t a z :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on the big fppf site, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_isomorphismLocusInRelativeMorphisms
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_isomorphismLocusInRelativeMorphisms
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_isomorphismLocusInRelativeMorphisms B S hS).has_limit _

/-! ### The morphism of base changes attached to a relative morphism -/

section BaseChangeMap

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}

/-- **A pair of Stacks 05Y1 is a relative isomorphism** when the morphism of base changes it
determines is an isomorphism. For a pair at a scheme `T` this says that the induced morphism
`Z_T ⟶ X_T` is an isomorphism, which is the condition cutting out the subfunctor
`Isom_Q(Z, X) ⊆ Mor_Q(Z, X)` of Stacks 0DPP. -/
def RelativeMorphism.IsRelativeIso (p : RelativeMorphism B S hS Z X Q z x T) : Prop :=
  IsIso p.baseChangeMap

attribute [local implicit_reducible] RelativeMorphism.restrict

/-- The morphism of base changes of a restricted pair lies over the new test presheaf. This is
`AlgebraicGeometry.Space.RelativeMorphism.baseChangeMap_comp_fst` with the first component of
the restricted pair written out, which is what makes it usable for rewriting. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_restrict_comp_fst (p : RelativeMorphism B S hS Z X Q z x T) (e : T' ⟶ T) :
    (RelativeMorphism.restrict e p).baseChangeMap ≫ pullback.fst (e ≫ p.base) x =
      pullback.fst (e ≫ p.base) z :=
  RelativeMorphism.baseChangeMap_comp_fst _

/-- The second component of the morphism of base changes of a restricted pair is the second
component of the pair, precomposed with the comparison map of fibre products. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_restrict_comp_snd (p : RelativeMorphism B S hS Z X Q z x T) (e : T' ⟶ T) :
    (RelativeMorphism.restrict e p).baseChangeMap ≫ pullback.snd (e ≫ p.base) x =
      pullback.mapFst e p.base z ≫ p.morphism := by
  refine (RelativeMorphism.baseChangeMap_comp_snd (RelativeMorphism.restrict e p)).trans ?_
  rw [RelativeMorphism.restrict_morphism, pullback.map_id_eq_mapFst]

/-- Restricting a pair along `e : T' ⟶ T` does not change its morphism of base changes, up to
the comparison of base changes: the square formed by the morphisms of base changes of `p` and of
its restriction and by the two comparison maps of fibre products commutes. -/
theorem mapFst_comp_baseChangeMap (p : RelativeMorphism B S hS Z X Q z x T) (e : T' ⟶ T) :
    pullback.mapFst e p.base z ≫ p.baseChangeMap =
      (RelativeMorphism.restrict e p).baseChangeMap ≫ pullback.mapFst e p.base x := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, RelativeMorphism.baseChangeMap_comp_fst, pullback.mapFst_fst,
      Category.assoc, pullback.mapFst_fst, ← Category.assoc,
      baseChangeMap_restrict_comp_fst]
  · rw [Category.assoc, RelativeMorphism.baseChangeMap_comp_snd, Category.assoc,
      pullback.mapFst_snd, baseChangeMap_restrict_comp_snd]

/-- **The morphism of base changes of a restricted pair is a base change of the morphism of base
changes.** The comparison isomorphisms `CategoryTheory.Limits.pullback.isoMapFst`, for the
source and for the target, carry the morphism of base changes of the restriction of a pair along
`e` to the base change along `e`, over the test presheaf, of the morphism of base changes of the
pair. -/
theorem isoMapFst_hom_comp_baseChangeOverBase (p : RelativeMorphism B S hS Z X Q z x T)
    (e : T' ⟶ T) :
    (pullback.isoMapFst e p.base z).hom ≫
        baseChangeOverBase B S hS p.baseChangeMap (pullback.fst p.base z)
          (pullback.fst p.base x) p.baseChangeMap_comp_fst e =
      (RelativeMorphism.restrict e p).baseChangeMap ≫ (pullback.isoMapFst e p.base x).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, baseChangeOverBase, pullback.lift_fst, Category.assoc,
      pullback.isoMapFst_hom_comp_fst_assoc, pullback.isoMapFst_hom_comp_fst,
      mapFst_comp_baseChangeMap]
  · rw [Category.assoc, baseChangeOverBase, pullback.lift_snd, Category.assoc,
      pullback.isoMapFst_hom_comp_snd, pullback.isoMapFst_hom_comp_snd,
      baseChangeMap_restrict_comp_fst]

/-- **The isomorphism locus of Stacks 05XD is the locus of relative isomorphisms.** A morphism
`e : T' ⟶ T` of test presheaves base changes the morphism of base changes of a pair at `T` to an
isomorphism exactly when the restriction of the pair along `e` is a relative isomorphism: the two
morphisms agree up to the comparison isomorphisms of the base changes. -/
theorem isIso_baseChangeOverBase_iff_isRelativeIso_restrict
    (p : RelativeMorphism B S hS Z X Q z x T) (e : T' ⟶ T) :
    IsIso (baseChangeOverBase B S hS p.baseChangeMap (pullback.fst p.base z)
        (pullback.fst p.base x) p.baseChangeMap_comp_fst e) ↔
      (RelativeMorphism.restrict e p).IsRelativeIso := by
  have key : (pullback.isoMapFst e p.base z).hom ≫
      baseChangeOverBase B S hS p.baseChangeMap (pullback.fst p.base z)
          (pullback.fst p.base x) p.baseChangeMap_comp_fst e ≫
        (pullback.isoMapFst e p.base x).inv =
      (RelativeMorphism.restrict e p).baseChangeMap := by
    rw [← Category.assoc, isoMapFst_hom_comp_baseChangeOverBase, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  change _ ↔ IsIso (RelativeMorphism.restrict e p).baseChangeMap
  rw [← key, isIso_comp_left_iff, isIso_comp_right_iff]

/-- **A restriction of a relative isomorphism is a relative isomorphism.** The morphism of base
changes of the restricted pair is, up to the comparison isomorphisms, a base change of the
morphism of base changes of the pair. -/
theorem RelativeMorphism.isRelativeIso_restrict (p : RelativeMorphism B S hS Z X Q z x T)
    (e : T' ⟶ T) (h : p.IsRelativeIso) : (RelativeMorphism.restrict e p).IsRelativeIso := by
  rw [← isIso_baseChangeOverBase_iff_isRelativeIso_restrict]
  have _ : IsIso p.baseChangeMap := h
  exact (isPullback_baseChangeOverBase B S hS p.baseChangeMap (pullback.fst p.base z)
    (pullback.fst p.base x) p.baseChangeMap_comp_fst e).isIso_snd_of_isIso

end BaseChangeMap

/-! ### Membership in a subfunctor, read as a factorisation -/

section Factors

universe v₂ u₂

variable {C : Type u₂} [Category.{v₂} C]

/-- A section of a presheaf of types lies in a subfunctor exactly when the morphism it
corresponds to under the Yoneda bijection factors through the subfunctor. -/
private theorem mem_obj_iff_exists_comp_ι {F : Cᵒᵖ ⥤ Type v₂} (W : Subfunctor F) (T : C)
    (s : F.obj (op T)) :
    s ∈ W.obj (op T) ↔ ∃ r : yoneda.obj T ⟶ W.toFunctor, r ≫ W.ι = yonedaEquiv.symm s := by
  rw [← Subfunctor.ofSection_le_iff, Subfunctor.ofSection_eq_range]
  exact ⟨fun h => ⟨Subfunctor.lift _ h, Subfunctor.lift_ι _ _⟩,
    fun ⟨r, hr⟩ => hr ▸ (Subfunctor.range_comp_le r W.ι).trans (Subfunctor.range_ι W).le⟩

end Factors

/-! ### The subfunctor of relative isomorphisms, Stacks 0DPP -/

section Isom

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- **Stacks 0DPP,** the subfunctor `Isom_Q(Z, X) ⊆ Mor_Q(Z, X)` of relative isomorphisms: its
sections over a scheme `T` are the pairs `(a, b)` of Stacks 05Y1 at `T` whose morphism of base
changes `Z_T ⟶ X_T` is an isomorphism.

This is a subfunctor because the restriction maps of `Mor_Q(Z, X)` are restriction of pairs
(`AlgebraicGeometry.Space.relativeHomSections_map`) and a restriction of a relative isomorphism
is a relative isomorphism. -/
@[stacks 0DPP "the subfunctor Isom_B(Y, X) of Mor_B(Y, X) of isomorphisms"]
def isomSubfunctor : Subfunctor (relativeHom B S hS Z X Q z x hZ hX hQ) where
  obj U := {s | (relativeHomSections B S hS Z X Q z x hZ hX hQ U.unop s).IsRelativeIso}
  map {U V} i s hs := by
    change ((relativeHomSections B S hS Z X Q z x hZ hX hQ V.unop)
      ((relativeHom B S hS Z X Q z x hZ hX hQ).map i.unop.op s)).IsRelativeIso
    rw [relativeHomSections_map B S hS Z X Q z x hZ hX hQ i.unop s]
    exact RelativeMorphism.isRelativeIso_restrict _ _ hs

/-- The sections of `Isom_Q(Z, X)` over a scheme are the pairs of Stacks 05Y1 which are relative
isomorphisms. -/
theorem mem_isomSubfunctor_iff (T : BigFppfOver B S hS)
    (s : (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op T)) :
    s ∈ (isomSubfunctor B S hS Z X Q z x hZ hX hQ).obj (op T) ↔
      (relativeHomSections B S hS Z X Q z x hZ hX hQ T s).IsRelativeIso :=
  Iff.rfl

/-- **Stacks 0DPP.** With `Z ⟶ Q` flat, proper and of finite presentation and `X ⟶ Q` proper,
the subfunctor `Isom_Q(Z, X) ⊆ Mor_Q(Z, X)` of relative isomorphisms is an open subspace.

This is the isomorphism locus of Stacks 05XD applied to the universal relative morphism, the
pair corresponding to the identity of `Mor_Q(Z, X)` under the bijection of Stacks 05Y3: the
source of that morphism is flat, locally of finite presentation and universally closed over
`Mor_Q(Z, X)` and its target is separated, locally of finite type and closed over
`Mor_Q(Z, X)`, both being base changes. A morphism from a scheme `T` factors through the locus
exactly when the base change of the universal morphism along it is an isomorphism, which is the
condition cutting out `Isom_Q(Z, X)`, so the locus *is* `Isom_Q(Z, X)`.

The algebraicity `hM` of `Mor_Q(Z, X)` is an explicit hypothesis: it is Stacks 0D1C, the standing
fact of the source's section, and the conclusion cannot do without it, because an open subspace
is in particular an algebraic space and the finite presentation and separatedness hypotheses on
`x` of the source's section enter the statement only through it. -/
@[stacks 0DPP "openness of the subfunctor of isomorphisms"]
theorem isOpenSubspace_isomSubfunctor (hzfp : IsFinitePresentation B S hS z)
    (hzflat : IsFlat B S hS z) (hzproper : IsProper B S hS z) (hxproper : IsProper B S hS x)
    (hM : IsAlgebraicSpace B S hS (relativeHom B S hS Z X Q z x hZ hX hQ)) :
    IsOpenSubspace B S hS (isomSubfunctor B S hS Z X Q z x hZ hX hQ) := by
  set M := relativeHom B S hS Z X Q z x hZ hX hQ
  -- the universal relative morphism, the pair corresponding to the identity of `M`
  set univ := relativeHomEquiv B S hS Z X Q z x hZ hX hQ M hM (𝟙 M)
  have hpbZ := AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk univ.base : (⟨M, hM⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)
    (ObjectProperty.homMk z : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)
  -- the source of the universal morphism is flat, locally of finite presentation and
  -- universally closed over `M`
  have hplfp : IsLocallyOfFinitePresentation B S hS (pullback.fst univ.base z) :=
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hpbZ.flip hzfp.1
  have hpflat : IsFlat B S hS (pullback.fst univ.base z) :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hpbZ.flip hzflat
  have hpuc : UniversallyClosed B S hS (pullback.fst univ.base z) :=
    (isProper_pullback_fst B S hS hZ hQ hM z univ.base hzproper).2.2
  -- the target of the universal morphism is separated, locally of finite type and closed
  -- over `M`
  have hqproper := isProper_pullback_fst B S hS hX hQ hM x univ.base hxproper
  have hqclosed : IsClosedMorphism B S hS (pullback.fst univ.base x) :=
    hxproper.2.2 M hM univ.base
  obtain ⟨W, hW, hWprop⟩ := exists_isOpenSubspace_iff_isIso_baseChange B S hS
    (isAlgebraicSpace_pullback B S hS univ.base z hM hZ hQ)
    (isAlgebraicSpace_pullback B S hS univ.base x hM hX hQ) hM univ.baseChangeMap
    (pullback.fst univ.base z) (pullback.fst univ.base x) univ.baseChangeMap_comp_fst
    hplfp hpflat hpuc hqproper.2.1.1 hqclosed hqproper.1
  -- the locus is the subfunctor of relative isomorphisms
  have hchar (T : BigFppfOver B S hS) (s : M.obj (op T)) :
      s ∈ W.obj (op T) ↔
        (relativeHomSections B S hS Z X Q z x hZ hX hQ T s).IsRelativeIso := by
    have hrestrict : RelativeMorphism.restrict (yonedaEquiv.symm s) univ =
        relativeHomSections B S hS Z X Q z x hZ hX hQ T s := by
      rw [← relativeHomEquiv_naturality hM (isAlgebraicSpace_yoneda B S hS T)
        (yonedaEquiv.symm s) (𝟙 M), Category.comp_id,
        relativeHomEquiv_yoneda T (isAlgebraicSpace_yoneda B S hS T) s]
    rw [mem_obj_iff_exists_comp_ι W T s,
      hWprop (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) (yonedaEquiv.symm s),
      isIso_baseChangeOverBase_iff_isRelativeIso_restrict univ (yonedaEquiv.symm s), hrestrict]
  have hEq : W = isomSubfunctor B S hS Z X Q z x hZ hX hQ :=
    Subfunctor.ext (funext fun U => Set.ext fun s => hchar U.unop s)
  rw [← hEq]
  exact hW

end Isom

end Space

end AlgebraicGeometry

end
