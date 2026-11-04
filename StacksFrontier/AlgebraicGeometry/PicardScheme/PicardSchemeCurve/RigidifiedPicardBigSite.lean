module

public import Mathlib.CategoryTheory.ShrinkYoneda
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RankOneLocusHilbert
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PointedCurveStructureSheaf
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Picard.SmallGroup
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Representability.BigSiteRestriction

/-!
# `Pic_{X/k, σ}` on a big fppf site is the Picard functor

Let `k` be a field, `X` a smooth projective curve over `k` with a `k`-rational point `σ`, and `B`
a big fppf site containing `X` and `Spec k`. The source (the running text of the chapter "Picard
Schemes of Curves" before [Stacks, Tag 0B9V]) observes that the functor

`Pic_{X/k, σ} : T ↦ Ker(Pic(X_T) ⟶ Pic(T))`

is isomorphic to the Picard functor `Pic_{X/k}` of [Stacks, Tag 0B9L] on `(Sch/k)_{fppf}`, by
[Stacks, Tag 0B9U] and [Stacks, Tag 0B9N]: the sequence `0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/k}(T) ⟶ 0`
is split exact with splitting `σ_T^*`, so the map `Pic(X_T) ⟶ Pic_{X/k}(T)` restricts to a
bijection on the kernel of `σ_T^*`. This file records that isomorphism on the objects of `B`, and
the consequences that `Pic_{X/k, σ}` restricted to `B` is an fppf sheaf and has `u`-small values.

## Main definitions

* `AlgebraicGeometry.RigidifiedPicard.bigSitePicardFunctor`: `Pic_{X/k, σ}` on the objects of the
  big fppf site, as a presheaf of sets.
* `AlgebraicGeometry.RigidifiedPicard.bigSitePicardFunctorIso`: its isomorphism with the Picard
  functor `Stacks.PicardFunctor.picardFunctor`.
* `AlgebraicGeometry.RigidifiedPicard.smallPicardFunctor`: the same presheaf with values shrunk
  to `Type u` (`CategoryTheory.FunctorToTypes.shrink`), the universe in which representability
  on the site is decided.
* `AlgebraicGeometry.RigidifiedPicard.translationIso`: translation by a class of
  `Pic_{X/k, σ}(k)`, an automorphism of `smallPicardFunctor`.

## Main results

* `AlgebraicGeometry.RigidifiedPicard.bijective_kernelToPicardFunctor`: the restriction of
  `Pic(X_T) ⟶ Pic_{X/k}(T)` to `Ker(σ_T^*)` is bijective.
* `AlgebraicGeometry.RigidifiedPicard.isSheaf_bigSitePicardFunctor`: `Pic_{X/k, σ}` is an fppf
  sheaf on the big site, being isomorphic to `Pic_{X/k}` (the first paragraph of the proof of
  [Stacks, Tag 0B9Z]).
* `AlgebraicGeometry.RigidifiedPicard.isSheaf_shrink_bigSitePicardFunctor`: the same for its
  values shrunk to `Type u`.
* `isRepresentable_picardFunctor_of_isRepresentable_smallPicardFunctor`: representing
  `Pic_{X/k, σ}` on the site represents `Pic_{X/k}`.

## References

* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 0B9U](https://stacks.math.columbia.edu/tag/0B9U)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 0B9Z](https://stacks.math.columbia.edu/tag/0B9Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RigidifiedPicard

variable (B : BigFppfSite.{u}) {k : Type u} [Field k] {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : X ⟶ Spec (.of k))
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- **`Pic_{X/k, σ}` on the objects of a big fppf site**, as a presheaf of sets: the composite of
`AlgebraicGeometry.RigidifiedPicard.picardFunctor` with the functor regarding an object of the
site as a `k`-scheme. -/
abbrev bigSitePicardFunctor : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type (u + 1) :=
  (BigFppfOver.toOver B (Spec (.of k)) hk).op ⋙ picardFunctor f σ hσ ⋙
    forget AddCommGrpCat.{u + 1}

/-- The map `Ker(σ_T^*) ⟶ Pic(X_T) ⟶ Pic_{X/k}(T)`, for an object `T` of the site. -/
def kernelToPicardFunctor (T : BigFppfOver B (Spec (.of k)) hk) :
    kernelAt f σ hσ ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T) →+
      (Stacks.PicardFunctor.picardFunctor B hX hk (ObjectProperty.homMk f)).obj (op T) :=
  (Stacks.PicardFunctor.toPicardFunctorHom B hX hk (ObjectProperty.homMk f) T).comp
    (kernelAt f σ hσ ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T)).subtype

include σ hσ in
/-- The hypothesis of [Stacks, Tag 0B9N] on the structure sheaves, supplied by
[Stacks, Tag 0B9U]. -/
theorem isIso_c_baseChangeProj [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    (U : BigFppfOver B (Spec (.of k)) hk) :
    IsIso (Stacks.PicardFunctor.baseChangeProj B hX hk (ObjectProperty.homMk f)
      U).toLRSHom.toHom.c :=
  isIso_c_baseChange_of_isCurve_of_section f σ hσ (B.inclusion.map U.hom)

/-- **The restriction of `Pic(X_T) ⟶ Pic_{X/k}(T)` to `Ker(σ_T^*)` is bijective**, by the split
exactness of [Stacks, Tag 0B9N], whose hypotheses hold by [Stacks, Tag 0B9U]. -/
theorem bijective_kernelToPicardFunctor [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    (T : BigFppfOver B (Spec (.of k)) hk) :
    Function.Bijective (kernelToPicardFunctor B hX hk f σ hσ T) := by
  have hOiso := isIso_c_baseChangeProj B hX hk f σ hσ
  refine ⟨fun a b hab => Subtype.ext ?_, fun y => ?_⟩
  · exact Stacks.PicardFunctor.eq_of_schemePullbackClass_baseChangeSection_eq_zero B hX hk
      (ObjectProperty.homMk f) σ hσ hOiso T a.1 b.1 a.2 b.2 hab
  · obtain ⟨x, rfl⟩ := Stacks.PicardFunctor.surjective_toPicardFunctorHom B hX hk
      (ObjectProperty.homMk f) σ hσ hOiso T y
    refine ⟨⟨Stacks.PicardFunctor.normalizedClass B hX hk (ObjectProperty.homMk f) σ hσ T x,
      Stacks.PicardFunctor.schemePullbackClass_baseChangeSection_normalizedClass B hX hk
        (ObjectProperty.homMk f) σ hσ T x⟩, ?_⟩
    exact Stacks.PicardFunctor.toPicardFunctorHom_normalizedClass B hX hk
      (ObjectProperty.homMk f) σ hσ T x

/-- The comparison `Ker(σ_T^*) ⟶ Pic_{X/k}(T)` is natural in the object `T` of the site. -/
theorem kernelToPicardFunctor_naturality {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U)
    (c : kernelAt f σ hσ ((BigFppfOver.toOver B (Spec (.of k)) hk).obj U)) :
    kernelToPicardFunctor B hX hk f σ hσ T
        (kernelMap f σ hσ ((BigFppfOver.toOver B (Spec (.of k)) hk).map g) c) =
      (Stacks.PicardFunctor.picardFunctor B hX hk (ObjectProperty.homMk f)).map g.op
        (kernelToPicardFunctor B hX hk f σ hσ U c) :=
  Stacks.PicardFunctor.toPicardFunctor_app_naturality B hX hk (ObjectProperty.homMk f) g c.1

/-- **`Pic_{X/k, σ}` is isomorphic to the Picard functor `Pic_{X/k}`** on the objects of the big
fppf site, by [Stacks, Tag 0B9N] and [Stacks, Tag 0B9U]. -/
def bigSitePicardFunctorIso [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] :
    bigSitePicardFunctor B hk f σ hσ ≅
      Stacks.PicardFunctor.picardFunctor B hX hk (ObjectProperty.homMk f) :=
  NatIso.ofComponents
    (fun T => Equiv.toIso (Equiv.ofBijective _
      (bijective_kernelToPicardFunctor B hX hk f σ hσ T.unop)))
    (fun {T U} g => by
      ext c
      exact kernelToPicardFunctor_naturality B hX hk f σ hσ g.unop c)

include hX in
/-- **`Pic_{X/k, σ}` is an fppf sheaf on the big site**, because it is isomorphic to `Pic_{X/k}`
(the first paragraph of the proof of [Stacks, Tag 0B9Z]). -/
theorem isSheaf_bigSitePicardFunctor [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] :
    Presieve.IsSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
      (bigSitePicardFunctor B hk f σ hσ) :=
  Presieve.isSheaf_iso _ (bigSitePicardFunctorIso B hX hk f σ hσ).symm
    ((isSheaf_iff_isSheaf_of_type _ _).1
      (Stacks.PicardFunctor.isSheaf_picardFunctor B hX hk (ObjectProperty.homMk f)))

/-- The values of `Pic_{X/k, σ}` are `u`-small: they are subgroups of Picard groups of schemes,
which are `u`-small by [Stacks, Tag 040B]. -/
instance small_bigSitePicardFunctor_obj (T : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ) :
    Small.{u} ((bigSitePicardFunctor B hk f σ hσ).obj T) :=
  small_subtype _ _

include hX in
/-- The values of `Pic_{X/k, σ}` on the site, shrunk to `Type u`, still form an fppf sheaf. -/
theorem isSheaf_shrink_bigSitePicardFunctor [IsCurve k f] [IsProjectiveVariety k f]
    [Smooth f] :
    Presieve.IsSheaf (BigFppfOver.topology B (Spec (.of k)) hk)
      (FunctorToTypes.shrink.{u} (bigSitePicardFunctor B hk f σ hσ)) :=
  Presieve.isSheaf_of_nat_equiv (fun _ => equivShrink _) (fun _ _ _ _ => by simp)
    (isSheaf_bigSitePicardFunctor B hX hk f σ hσ)

/-! ### Values in `Type u`, and translation by a `k`-point -/

/-- **`Pic_{X/k, σ}` on the site with values shrunk to `Type u`**, which is the universe in which
the representability criterion of the big fppf site is stated. -/
abbrev smallPicardFunctor : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u :=
  FunctorToTypes.shrink.{u} (bigSitePicardFunctor B hk f σ hσ)

/-- The structure morphism of an object of the site, as a morphism to the final `k`-scheme. -/
abbrev toBase (T : BigFppfOver B (Spec (.of k)) hk) :
    (BigFppfOver.toOver B (Spec (.of k)) hk).obj T ⟶ Over.mk (𝟙 (Spec (.of k))) :=
  Over.homMk ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T).hom (Category.comp_id _)

/-- The structure morphism of `T` composed with a morphism `T' ⟶ T` of the site is the structure
morphism of `T'`. -/
theorem toBase_comp {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T) :
    (BigFppfOver.toOver B (Spec (.of k)) hk).map g ≫ toBase B hk T = toBase B hk T' := by
  ext
  exact Over.w ((BigFppfOver.toOver B (Spec (.of k)) hk).map g)

/-- Restricting the pullback of a class of `Pic_{X/k, σ}(k)` to `T` along `T' ⟶ T` is its pullback
to `T'`. -/
theorem map_map_toBase {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T)
    (r : (picardFunctor f σ hσ).obj (op (Over.mk (𝟙 (Spec (.of k)))))) :
    (picardFunctor f σ hσ).map ((BigFppfOver.toOver B (Spec (.of k)) hk).map g).op
        ((picardFunctor f σ hσ).map (toBase B hk T).op r) =
      (picardFunctor f σ hσ).map (toBase B hk T').op r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, toBase_comp]

/-- The values of `Pic_{X/k, σ}` over `k`-schemes are `u`-small. -/
instance small_picardFunctor_obj (T : Over (Spec (.of k))) :
    Small.{u} ((picardFunctor f σ hσ).obj (op T)) :=
  small_subtype _ _

/-- A value of the shrunk functor is a class of `Pic_{X/k, σ}`. -/
def smallPicardFunctorEquiv (T : BigFppfOver B (Spec (.of k)) hk) :
    (smallPicardFunctor B hk f σ hσ).obj (op T) ≃
      (picardFunctor f σ hσ).obj (op ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T)) :=
  (equivShrink ((picardFunctor f σ hσ).obj
    (op ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T)))).symm

/-- Restriction in the shrunk functor is restriction in `Pic_{X/k, σ}`. -/
theorem smallPicardFunctorEquiv_map {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T)
    (x : (smallPicardFunctor B hk f σ hσ).obj (op T)) :
    smallPicardFunctorEquiv B hk f σ hσ T' ((smallPicardFunctor B hk f σ hσ).map g.op x) =
      (picardFunctor f σ hσ).map ((BigFppfOver.toOver B (Spec (.of k)) hk).map g).op
        (smallPicardFunctorEquiv B hk f σ hσ T x) := by
  simp [smallPicardFunctorEquiv, smallPicardFunctor, FunctorToTypes.shrink_map]

/-- The value at `T` of the translation by a class `r` of `Pic_{X/k, σ}(k)`: adding the pullback of
`r` to `T`. -/
def translationEquiv (r : (picardFunctor f σ hσ).obj (op (Over.mk (𝟙 (Spec (.of k))))))
    (T : BigFppfOver B (Spec (.of k)) hk) :
    (smallPicardFunctor B hk f σ hσ).obj (op T) ≃ (smallPicardFunctor B hk f σ hσ).obj (op T) :=
  ((smallPicardFunctorEquiv B hk f σ hσ T).trans
    (Equiv.addRight ((picardFunctor f σ hσ).map (toBase B hk T).op r))).trans
      (smallPicardFunctorEquiv B hk f σ hσ T).symm

/-- As a class of `Pic_{X/k, σ}(T)`, the translate of `x` by `r` is `x` plus the pullback of `r`
to `T`. -/
theorem symm_translationEquiv_apply
    (r : (picardFunctor f σ hσ).obj (op (Over.mk (𝟙 (Spec (.of k))))))
    (T : BigFppfOver B (Spec (.of k)) hk) (x : (smallPicardFunctor B hk f σ hσ).obj (op T)) :
    smallPicardFunctorEquiv B hk f σ hσ T (translationEquiv B hk f σ hσ r T x) =
      smallPicardFunctorEquiv B hk f σ hσ T x +
        (picardFunctor f σ hσ).map (toBase B hk T).op r := by
  simp [translationEquiv]

/-- **Translation by a class `r ∈ Pic_{X/k, σ}(k)`**, an automorphism of `Pic_{X/k, σ}` on the
site: it adds the pullback of `r`. -/
def translationIso (r : (picardFunctor f σ hσ).obj (op (Over.mk (𝟙 (Spec (.of k)))))) :
    smallPicardFunctor B hk f σ hσ ≅ smallPicardFunctor B hk f σ hσ :=
  NatIso.ofComponents (fun T => Equiv.toIso (translationEquiv B hk f σ hσ r T.unop))
    (fun {T U} g => by
      ext x
      apply (smallPicardFunctorEquiv B hk f σ hσ U.unop).injective
      change smallPicardFunctorEquiv B hk f σ hσ U.unop (translationEquiv B hk f σ hσ r U.unop
          ((smallPicardFunctor B hk f σ hσ).map g.unop.op x)) =
        smallPicardFunctorEquiv B hk f σ hσ U.unop ((smallPicardFunctor B hk f σ hσ).map g.unop.op
          (translationEquiv B hk f σ hσ r T.unop x))
      rw [symm_translationEquiv_apply, smallPicardFunctorEquiv_map, smallPicardFunctorEquiv_map,
        symm_translationEquiv_apply, map_add, map_map_toBase])

/-- As a class of `Pic_{X/k, σ}(T)`, the image of `x` under `translationIso r` at `T` is `x` plus
the pullback of `r` to `T`. -/
theorem symm_translationIso_hom_app
    (r : (picardFunctor f σ hσ).obj (op (Over.mk (𝟙 (Spec (.of k))))))
    (T : BigFppfOver B (Spec (.of k)) hk) (x : (smallPicardFunctor B hk f σ hσ).obj (op T)) :
    smallPicardFunctorEquiv B hk f σ hσ T ((translationIso B hk f σ hσ r).hom.app (op T) x) =
      smallPicardFunctorEquiv B hk f σ hσ T x + (picardFunctor f σ hσ).map (toBase B hk T).op r :=
  symm_translationEquiv_apply B hk f σ hσ r T x

/-- **Representing `Pic_{X/k, σ}` represents `Pic_{X/k}`**: the shrunk `Pic_{X/k, σ}` and the
Picard functor are in natural bijection on the objects of the site
(`AlgebraicGeometry.RigidifiedPicard.bigSitePicardFunctorIso`). -/
theorem isRepresentable_picardFunctor_of_isRepresentable_smallPicardFunctor [IsCurve k f]
    [IsProjectiveVariety k f] [Smooth f]
    (hG : (smallPicardFunctor B hk f σ hσ).IsRepresentable) :
    (Stacks.PicardFunctor.picardFunctor B hX hk (ObjectProperty.homMk f)).IsRepresentable := by
  obtain ⟨Y, ⟨eY⟩⟩ := hG.has_representation
  refine (eY.ofNatEquiv (F' := Stacks.PicardFunctor.picardFunctor B hX hk
    (ObjectProperty.homMk f)) (fun T => (smallPicardFunctorEquiv B hk f σ hσ T.unop).trans
      ((bigSitePicardFunctorIso B hX hk f σ hσ).app T).toEquiv) ?_).isRepresentable
  intro T T' g a
  show (bigSitePicardFunctorIso B hX hk f σ hσ).hom.app T'
      (smallPicardFunctorEquiv B hk f σ hσ T'.unop ((smallPicardFunctor B hk f σ hσ).map g a)) =
    (Stacks.PicardFunctor.picardFunctor B hX hk (ObjectProperty.homMk f)).map g
      ((bigSitePicardFunctorIso B hX hk f σ hσ).hom.app T
        (smallPicardFunctorEquiv B hk f σ hσ T.unop a))
  rw [← Quiver.Hom.op_unop g, smallPicardFunctorEquiv_map]
  exact ConcreteCategory.congr_hom
    ((bigSitePicardFunctorIso B hX hk f σ hσ).hom.naturality g.unop.op)
    (smallPicardFunctorEquiv B hk f σ hσ T.unop a)

end AlgebraicGeometry.RigidifiedPicard

end
