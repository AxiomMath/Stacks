module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFibreTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomClosedImmersion

/-!
# The homomorphism of inverse images attached to an object of the 2-fibre product

Let `y : (Sch/V)_{fppf} ⟶ Coh_{X/B}` be a scheme-valued point and `A = y(V)` its value at the
identity of `V`.  An object `P` of the 2-fibre product `(Sch/V) ×_{Coh_{X/B}} Quot_{F/X/B}` over
a scheme `T` carries a map `F_T ⟶ y(x)`
(`AlgebraicGeometry.Space.QuotSituation.fibreClassMap`), and `y(x)` is identified with the
inverse image of `A` along the morphism `y(x ⟶ V)` of `Coh_{X/B}`.  Reading the map through that
identification gives a section of the relative Hom functor `Hom(F_V, 𝒢)` of `A` at `T`; this is
the classifying map of the proof of Stacks 09TU.  This file defines it and proves that it is
compatible with the morphisms of the 2-fibre product.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.fibreArrow`: the morphism `y(x) ⟶ y(V)` of `Coh_{X/B}`.
* `AlgebraicGeometry.Space.QuotSituation.fibreClassHom`: the section of the relative Hom functor
  attached to an object of the 2-fibre product.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.homOfPullMap_conjHom`: reading pulled-back maps as
  homomorphisms of inverse images is natural, in the form of the conjugation of the relative Hom
  functor.
* `AlgebraicGeometry.Space.QuotSituation.fibreClassHom_map`: along a morphism of the 2-fibre
  product, the section attached to the source is the restriction of the one attached to the
  target.

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local implicit_reducible] AlgebraicGeometry.Space.QuotSituation.toCoherentSituation

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)

/-- The map out of `F_{E'.T}` attached through `a ≫ e` to the conjugate of a homomorphism `u`,
by the comparison of Stacks 03LU for any proof of `X_a ≫ X_e = X_{a ≫ e}`, is the pullback along
`a` of the map attached to `u` through `e`. -/
theorem pullMapOf_conjHom_comp {E' E A : CoherentObject D.toCoherentSituation}
    (a : CoherentHom E' E) (e : CoherentHom E A)
    (hk : D.relativeMap a.base ≫ D.relativeMap e.base = D.relativeMap (a.base ≫ e.base))
    (u : (modulePullback B S hS (D.relativeMap e.base)).obj
        ((modulePullback B S hS (D.sourceProjection A.T)).obj D.F) ⟶
      (modulePullback B S hS (D.relativeMap e.base)).obj A.F)
    (v : D.baseChangeModule E.T ⟶ E.F)
    (hu : (D.baseChangeComparison e.base).hom.app D.F ≫ u ≫ e.fibre = v) :
    (D.baseChangeComparison (a.base ≫ e.base)).hom.app D.F ≫
        ((modulePullbackTriangle B S hS hk).hom.app
            ((modulePullback B S hS (D.sourceProjection A.T)).obj D.F) ≫
          (modulePullback B S hS (D.relativeMap a.base)).map u ≫
          (modulePullbackTriangle B S hS hk).inv.app A.F) ≫
        (CoherentHom.comp a e).fibre =
      (D.baseChangeComparison a.base).hom.app D.F ≫
        (modulePullback B S hS (D.relativeMap a.base)).map v ≫ a.fibre :=
  Functor.conj_char_of_formulas (D.baseChangeComparison e.base)
    (D.baseChangeComparison a.base) (D.baseChangeComparison (a.base ≫ e.base))
    (modulePullbackTriangle B S hS hk) D.F e.fibre a.fibre (CoherentHom.comp a e).fibre
    (Functor.hom_app_of_eq_compWhisker (D.baseChangeComparison e.base)
      (D.baseChangeComparison a.base) (D.baseChangeComparison (a.base ≫ e.base))
      (modulePullbackTriangle B S hS hk)
      (D.baseChangeComparison_comp (modulePushforwardCoherence B S hS) a.base e.base) D.F)
    (CoherentHom.comp_fibre a e) u v hu

/-- **Reading pulled-back maps as homomorphisms of inverse images is natural, in the form of the
conjugation of the relative Hom functor**, along a composite `a ≫ e` of morphisms of
`Coh_{X/B}`. -/
theorem homOfPullMap_conjHom_comp {E' E A : CoherentObject D.toCoherentSituation}
    (a : CoherentHom E' E) (e : CoherentHom E A)
    (hk : D.relativeMap a.base ≫ D.relativeMap e.base = D.relativeMap (a.base ≫ e.base))
    (v : D.baseChangeModule E.T ⟶ E.F) :
    D.homOfPullMap (a.base ≫ e.base) (D.cohFibreIso (CoherentHom.comp a e))
        (D.pullMapOf a.base a.fibre v) =
      Functor.conjHom (P₁ := modulePullback B S hS (D.relativeMap e.base))
        (P₂ := modulePullback B S hS (D.relativeMap (a.base ≫ e.base)))
        (L := modulePullback B S hS (D.relativeMap a.base))
        (M := (modulePullback B S hS (D.sourceProjection A.T)).obj D.F) (N := A.F)
        (modulePullbackTriangle B S hS hk) (D.homOfPullMap e.base (D.cohFibreIso e) v) :=
  (D.homOfPullMap_unique (a.base ≫ e.base) (D.cohFibreIso (CoherentHom.comp a e))
    (D.pullMapOf a.base a.fibre v) _
    (D.pullMapOf_conjHom_comp a e hk (D.homOfPullMap e.base (D.cohFibreIso e) v) v
      (D.homOfPullMap_spec e.base (D.cohFibreIso e) v))).symm

/-- **Reading pulled-back maps as homomorphisms of inverse images is natural, in the form of the
conjugation of the relative Hom functor.**  For morphisms `a : E' ⟶ E`, `e : E ⟶ A` and
`e' = a ≫ e` of `Coh_{X/B}`, the homomorphism attached through `e'` to the pullback of `v` along
`a` is the conjugate, by the comparison of Stacks 03LU for `X_a ≫ X_e = X_{e'}`, of the
homomorphism attached to `v` through `e`. -/
theorem homOfPullMap_conjHom {E' E A : CoherentObject D.toCoherentSituation}
    (a : CoherentHom E' E) (e : CoherentHom E A) (e' : CoherentHom E' A)
    (he : e' = CoherentHom.comp a e)
    (hk : D.relativeMap a.base ≫ D.relativeMap e.base = D.relativeMap e'.base)
    (v : D.baseChangeModule E.T ⟶ E.F) :
    D.homOfPullMap e'.base (D.cohFibreIso e') (D.pullMapOf a.base a.fibre v) =
      Functor.conjHom (P₁ := modulePullback B S hS (D.relativeMap e.base))
        (P₂ := modulePullback B S hS (D.relativeMap e'.base))
        (L := modulePullback B S hS (D.relativeMap a.base))
        (M := (modulePullback B S hS (D.sourceProjection A.T)).obj D.F) (N := A.F)
        (modulePullbackTriangle B S hS hk) (D.homOfPullMap e.base (D.cohFibreIso e) v) := by
  subst he
  exact D.homOfPullMap_conjHom_comp a e hk v


/-- The action of the relative Hom functor of an object `A` of `Coh_{X/B}` along a morphism of
test schemes over its test scheme, written out as a conjugation by the comparison of Stacks 03LU
for `X_m ≫ X_Z = X_{Z'}`. -/
theorem fibreHomFunctor_map_eq (hc : ModulePushforwardCoherence B S hS)
    (A : CoherentObject D.toCoherentSituation) {Z' Z : Over A.T} (m : Z' ⟶ Z)
    (hk : D.relativeMap m.left ≫ D.relativeMap Z.hom = D.relativeMap Z'.hom) :
    (D.fibreHomFunctor A hc).map m.op =
      ↾(Functor.conjHom (P₁ := modulePullback B S hS (D.relativeMap Z.hom))
        (P₂ := modulePullback B S hS (D.relativeMap Z'.hom))
        (L := modulePullback B S hS (D.relativeMap m.left))
        (M := (modulePullback B S hS (D.sourceProjection A.T)).obj D.F) (N := A.F)
        (modulePullbackTriangle B S hS hk)) := by
  change (moduleHomOver hc (D.baseChangeModule A.T) A.F).map
    ((D.fibreRelativeFunctor A).map m).op = _
  rw [moduleHomOver_map]
  rfl

/-- The action of the relative Hom functor of an object `A` of `Coh_{X/B}` on a section, written
out as a conjugation. -/
theorem fibreHomFunctor_map_apply (hc : ModulePushforwardCoherence B S hS)
    (A : CoherentObject D.toCoherentSituation) {Z' Z : Over A.T} (m : Z' ⟶ Z)
    (hk : D.relativeMap m.left ≫ D.relativeMap Z.hom = D.relativeMap Z'.hom)
    (u : (D.fibreHomFunctor A hc).obj (Opposite.op Z)) :
    (D.fibreHomFunctor A hc).map m.op u =
      Functor.conjHom (P₁ := modulePullback B S hS (D.relativeMap Z.hom))
        (P₂ := modulePullback B S hS (D.relativeMap Z'.hom))
        (L := modulePullback B S hS (D.relativeMap m.left))
        (M := (modulePullback B S hS (D.sourceProjection A.T)).obj D.F) (N := A.F)
        (modulePullbackTriangle B S hS hk) u := by
  rw [D.fibreHomFunctor_map_eq hc A m hk]
  rfl

variable {V : BigFppfOver B S hS}
  (y : (Stack.schemeFibredCategory B S hS V).val ⥤ᵇ D.toCoherentSituation.coherentCFG.val)

/-- The object `A = y(V)` of `Coh_{X/B}` a scheme-valued point attaches to the identity of
`V`. -/
abbrev fibreBase : CoherentObject D.toCoherentSituation :=
  y.obj (Over.mk (𝟙 V))

/-- **The morphism `y(x) ⟶ y(V)` of `Coh_{X/B}`** a scheme-valued point attaches to a scheme `x`
over `V`, viewed as a morphism to the identity of `V`. -/
def fibreArrow (x : Over V) : CoherentHom (y.obj x) (D.fibreBase y) :=
  y.map (Over.homMk x.hom (Category.comp_id _) : x ⟶ Over.mk (𝟙 V))

/-- The morphism `y(x') ⟶ y(V)` is the composite of `y(a) : y(x') ⟶ y(x)` and `y(x) ⟶ y(V)`. -/
theorem fibreArrow_comp {x' x : Over V} (a : x' ⟶ x) :
    D.fibreArrow y x' = CoherentHom.comp (D.fibreMapHom y a) (D.fibreArrow y x) := by
  have h : a ≫ (Over.homMk x.hom (Category.comp_id _) : x ⟶ Over.mk (𝟙 V)) =
      Over.homMk x'.hom (Category.comp_id _) :=
    Over.OverMorphism.ext (Over.w a)
  exact (congrArg y.map h).symm.trans (y.toFunctor.map_comp _ _)

/-- The base map of `y(x') ⟶ y(V)` is that of `y(a)` followed by that of `y(x) ⟶ y(V)`. -/
theorem fibreArrow_base_comp {x' x : Over V} (a : x' ⟶ x) :
    (D.fibreMapHom y a).base ≫ (D.fibreArrow y x).base = (D.fibreArrow y x').base :=
  (congrArg CoherentHom.base (D.fibreArrow_comp y a)).symm

/-- **The section of the relative Hom functor of `A = y(V)` attached to an object of the 2-fibre
product**: the map `F_T ⟶ y(x)` of
`AlgebraicGeometry.Space.QuotSituation.fibreClassMap` read as a homomorphism of inverse images
along `y(x) ⟶ y(V)`. -/
def fibreClassHom (hc : ModulePushforwardCoherence B S hS) (P : (D.fibreProduct y).val.obj) :
    (D.fibreHomFunctor (D.fibreBase y) hc).obj
      (Opposite.op (Over.mk (D.fibreArrow y P.x).base)) :=
  D.homOfPullMap (D.fibreArrow y P.x).base (D.cohFibreIso (D.fibreArrow y P.x))
    (D.fibreClassMap y P)

/-- The morphism of test schemes over `y(V)` underlying a morphism of schemes over `V`. -/
def fibreOverHomOf {x' x : Over V} (a : x' ⟶ x) :
    (Over.mk (D.fibreArrow y x').base : Over (D.fibreBase y).T) ⟶
      Over.mk (D.fibreArrow y x).base :=
  Over.homMk (D.fibreMapHom y a).base (D.fibreArrow_base_comp y a)

/-- The morphism of test schemes over `y(V)` underlying a morphism of the 2-fibre product. -/
abbrev fibreOverHom {P' P : (D.fibreProduct y).val.obj} (m : P' ⟶ P) :
    (Over.mk (D.fibreArrow y P'.x).base : Over (D.fibreBase y).T) ⟶
      Over.mk (D.fibreArrow y P.x).base :=
  D.fibreOverHomOf y m.a

/-- **The restriction of the section attached to an object of the 2-fibre product along a
morphism `a : x' ⟶ x` of schemes over `V`** is the homomorphism attached to the pullback of its
surjection along `y(a)`. -/
theorem fibreHomFunctor_map_fibreClassHom (hc : ModulePushforwardCoherence B S hS)
    {x' : Over V} {P : (D.fibreProduct y).val.obj} (a : x' ⟶ P.x) :
    (D.fibreHomFunctor (D.fibreBase y) hc).map (D.fibreOverHomOf y a).op
        (D.fibreClassHom y hc P) =
      D.homOfPullMap (D.fibreArrow y x').base (D.cohFibreIso (D.fibreArrow y x'))
        (D.pullMapOf (D.fibreMapHom y a).base (D.fibreMapHom y a).fibre
          (D.fibreClassMap y P)) := by
  have hk₀ : D.relativeMap (D.fibreMapHom y a).base ≫ D.relativeMap (D.fibreArrow y P.x).base =
      D.relativeMap (D.fibreArrow y x').base := by
    rw [← baseChangeMap_comp, D.fibreArrow_base_comp y a]
  have hk : D.relativeMap (D.fibreOverHomOf y a).left ≫
        D.relativeMap (Over.mk (D.fibreArrow y P.x).base : Over (D.fibreBase y).T).hom =
      D.relativeMap (Over.mk (D.fibreArrow y x').base : Over (D.fibreBase y).T).hom := hk₀
  rw [D.fibreHomFunctor_map_apply hc (D.fibreBase y) (D.fibreOverHomOf y a) hk]
  exact (D.homOfPullMap_conjHom _ _ _ (D.fibreArrow_comp y a) hk₀ _).symm

/-- **Along a morphism of the 2-fibre product, the section attached to the source is the
restriction of the section attached to the target.** -/
theorem fibreClassHom_map (hc : ModulePushforwardCoherence B S hS)
    {P' P : (D.fibreProduct y).val.obj} (m : P' ⟶ P) :
    D.fibreClassHom y hc P' =
      (D.fibreHomFunctor (D.fibreBase y) hc).map (D.fibreOverHom y m).op
        (D.fibreClassHom y hc P) :=
  (congrArg (D.homOfPullMap (D.fibreArrow y P'.x).base
    (D.cohFibreIso (D.fibreArrow y P'.x))) (D.fibreClassMap_map y m)).trans
    (D.fibreHomFunctor_map_fibreClassHom y hc m.a).symm

/-- The homomorphism of inverse images attached to a map determines the map. -/
theorem homOfPullMap_injective {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    {G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2}
    {M : Modules.{u, u} B S hS (D.space T').1 (D.space T').2}
    (ψ : (modulePullback B S hS (D.relativeMap h)).obj G ≅ M)
    {v v' : D.baseChangeModule T' ⟶ M} (hv : D.homOfPullMap h ψ v = D.homOfPullMap h ψ v') :
    v = v' := by
  rw [← D.homOfPullMap_spec h ψ v, ← D.homOfPullMap_spec h ψ v', hv]

end AlgebraicGeometry.Space.QuotSituation

end
