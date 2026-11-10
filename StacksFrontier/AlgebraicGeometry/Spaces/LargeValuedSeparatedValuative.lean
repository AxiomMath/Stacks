module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperValuativeLifting
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition

/-!
# Separatedness from a quasi-compact immersive diagonal and valuative uniqueness

Let `f : F ⟶ G` be a morphism of presheaves on the big fppf site of a scheme `S`, with values in
a universe `max w u` independent of the universe `u` of the schemes. Suppose that the relative
diagonal `F ⟶ F ×_G F` is representable by quasi-compact immersions of schemes, and that `f`
satisfies the uniqueness part of the valuative criterion *up to an extension of valuation
rings*: whenever two points `a, b` of `F` over the spectrum of a valuation ring `R` have the
same image in `G` and agree over the fraction field of `R`, they agree after pulling back to the
spectrum of some valuation ring `R'` dominating `R`. Then `f` is separated, that is, its
relative diagonal is a closed immersion.

This is the argument of Stacks 03KV — a quasi-separated morphism satisfying the uniqueness part
of the valuative criterion is separated — for a morphism which is not known to be a morphism of
algebraic spaces, but whose diagonal is known to be representable by immersions. It is the form
in which the separatedness of the relative Picard functor (Stacks 0DNJ) is deduced: there the
diagonal is an immersion by Stacks 0D2D and quasi-compact by Stacks 0DMF, and a point of the
Picard functor over a valuation ring only comes from an invertible module after an extension of
the valuation ring, which is why the uniqueness hypothesis is allowed one.

## Main definitions

* `AlgebraicGeometry.Space.ValuativeUniquenessUpToExtension`: the uniqueness part of the
  valuative criterion, up to an extension of valuation rings.

## Main results

* `AlgebraicGeometry.Space.valuativeCriterion_existence_of_diagonal_uniqueness`: the represented
  base change `W ⟶ V` of the relative diagonal along a scheme-valued point `V ⟶ F ×_G F`
  satisfies the existence part of the valuative criterion of Stacks 03IX.
* `AlgebraicGeometry.Space.isSeparatedULift_of_diagonal_of_valuativeUniqueness`: the morphism
  is separated.

## Implementation notes

Each represented base change `W ⟶ V` of the relative diagonal is a quasi-compact immersion of
schemes of the site. It is shown to be universally closed by reading it as the morphism
`yoneda.map snd` of algebraic spaces with values in `Type u` and applying Stacks 03KA,
`AlgebraicGeometry.Space.universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence`;
the valuative squares of that Stacks 03KA uses already carry the size bounds that put the
valuation rings into the site. An immersion of schemes with closed image is a closed immersion.

The existence part for `yoneda.map snd` is where the hypothesis enters. A valuative square for
it is a point `Spec R ⟶ V` whose restriction to `Spec K` lifts to `W`; composing with
`V ⟶ F ×_G F` gives the two points `a, b` of `F` over `Spec R`, which agree over `G` by the
fibre product and agree over `Spec K` because the lift lands in the diagonal. After the
extension `R ⟶ R'` provided by the hypothesis they agree, so the point `Spec R' ⟶ F ×_G F`
factors through the diagonal and the cartesian square produces the lift `Spec R' ⟶ W`; the
dominating extension of the square is the one of the hypothesis.

## References

* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 03KA](https://stacks.math.columbia.edu/tag/03KA)
* [Stacks Project, Tag 03KV](https://stacks.math.columbia.edu/tag/03KV)
* [Stacks Project, Tag 0DNJ](https://stacks.math.columbia.edu/tag/0DNJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Two morphisms of site objects over `S` agree as soon as their underlying morphisms of
schemes do. -/
theorem siteObject_hom_ext {X Y : BigFppfOver B S hS} {p q : X ⟶ Y}
    (h : (B.inclusion).map p.left = (B.inclusion).map q.left) : p = q :=
  Over.OverMorphism.ext (B.inclusion.map_injective h)

section Diagonal

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}

/--
The hypothesis of `AlgebraicGeometry.Space.isSeparatedULift_of_diagonal_of_valuativeUniqueness`:
**the uniqueness part of the valuative criterion, up to an extension of valuation rings.** Two
points `a, b` of `F` over the spectrum of a valuation ring `R` of the site with the same image
in `G` which agree over the fraction field `K` of `R` agree over the spectrum of a valuation
ring `R'` dominating `R`, through a homomorphism of fraction fields compatible with it. -/
def ValuativeUniquenessUpToExtension (f : F ⟶ G) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (ring_mem : B.Contains (Spec (.of R))) (field_mem : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ S)
    (a b : uliftYoneda.{w}.obj (siteObject B S hS ring_mem base) ⟶ F),
    a ≫ f = b ≫ f →
    uliftYoneda.map (specSiteObjectMap (algebraMap R K) ring_mem field_mem base) ≫ a =
      uliftYoneda.map (specSiteObjectMap (algebraMap R K) ring_mem field_mem base) ≫ b →
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
      (K' : Type u) (_ : Field K') (_ : Algebra R' K') (_ : IsFractionRing R' K')
      (ring_mem' : B.Contains (Spec (.of R'))) (_ : B.Contains (Spec (.of K')))
      (φ : R →+* R') (ψ : K →+* K'),
      IsLocalHom φ ∧ (algebraMap R' K').comp φ = ψ.comp (algebraMap R K) ∧
        uliftYoneda.map (specSiteObjectMap φ ring_mem ring_mem' base) ≫ a =
          uliftYoneda.map (specSiteObjectMap φ ring_mem ring_mem' base) ≫ b

/-- **The represented base changes of the relative diagonal satisfy the existence part of the
valuative criterion.** Let `W ⟶ V` be the base change of the relative diagonal of `f` along a
scheme-valued point `g : V ⟶ F ×_G F`. If `f` satisfies the uniqueness part of the valuative
criterion up to an extension of valuation rings, then `yoneda.map snd` satisfies the existence
part of Stacks 03IX. -/
theorem valuativeCriterion_existence_of_diagonal_uniqueness (f : F ⟶ G)
    (hval : ValuativeUniquenessUpToExtension.{w} f) {V W : BigFppfOver B S hS}
    (g : uliftYoneda.{w}.obj V ⟶ pullback f f) (fst : uliftYoneda.{w}.obj W ⟶ F)
    (snd : W ⟶ V) (hp : IsPullback fst (uliftYoneda.{w}.map snd) (pullback.diagonal f) g) :
    ValuativeCriterion.Existence (yoneda.map snd) := by
  intro q
  -- The square in the site.
  obtain ⟨sR, hsR⟩ := yoneda.map_surjective q.special
  obtain ⟨gK, hgK⟩ := yoneda.map_surjective q.generic
  set fr := specSiteObjectMap (hS := hS) (algebraMap q.R q.K) q.ring_mem q.field_mem q.base
    with hfr
  have hcomm : gK ≫ snd = fr ≫ sR := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hgK, hsR]
    exact q.comm
  -- The two points of `F` over `Spec R`.
  set a := uliftYoneda.{w}.map sR ≫ g ≫ pullback.fst f f with ha
  set b := uliftYoneda.{w}.map sR ≫ g ≫ pullback.snd f f with hb
  have hab : a ≫ f = b ≫ f := by
    rw [ha, hb, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      pullback.condition]
  have hgen : ∀ (pr : pullback f f ⟶ F), pullback.diagonal f ≫ pr = 𝟙 F →
      uliftYoneda.{w}.map fr ≫ uliftYoneda.{w}.map sR ≫ g ≫ pr =
        uliftYoneda.{w}.map gK ≫ fst := by
    intro pr hpr
    rw [← Functor.map_comp_assoc, ← hcomm, Functor.map_comp_assoc, ← hp.w_assoc, hpr,
      Category.comp_id]
  have hK : uliftYoneda.{w}.map fr ≫ a = uliftYoneda.{w}.map fr ≫ b := by
    rw [ha, hb, hgen _ (pullback.diagonal_fst f), hgen _ (pullback.diagonal_snd f)]
  obtain ⟨R', _, _, _, K', _, _, _, ring_mem', field_mem', φ, ψ, hloc, hfrac, heq⟩ :=
    hval q.R q.K q.ring_mem q.field_mem q.base a b hab hK
  -- The dominating extension.
  set sO := specSiteObjectMap (hS := hS) φ q.ring_mem ring_mem' q.base with hsO
  set fr' := specSiteObjectMap (hS := hS) (algebraMap R' K') ring_mem' field_mem'
    (Spec.map (CommRingCat.ofHom φ) ≫ q.base) with hfr'
  have hSpec : Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hfrac]
  set gO : siteObject B S hS field_mem'
      (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
        (Spec.map (CommRingCat.ofHom φ) ≫ q.base)) ⟶
      siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom ψ)) :
      B.obj field_mem' ⟶ B.obj q.field_mem) (by
        ext1
        change Spec.map (CommRingCat.ofHom ψ) ≫
            (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) =
          Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫
            (Spec.map (CommRingCat.ofHom φ) ≫ q.base)
        rw [← Category.assoc, hSpec, Category.assoc]) with hgO
  have hsquare : gO ≫ fr = fr' ≫ sO := siteObject_hom_ext hSpec
  let square : ValuativeSquare (yoneda.map snd) :=
    { R := R', K := K', ring_mem := ring_mem', field_mem := field_mem'
      base := Spec.map (CommRingCat.ofHom φ) ≫ q.base
      generic := yoneda.map gO ≫ q.generic
      special := yoneda.map sO ≫ q.special
      comm := by
        change (yoneda.map gO ≫ q.generic) ≫ yoneda.map snd =
          yoneda.map fr' ≫ yoneda.map sO ≫ q.special
        rw [Category.assoc, q.comm]
        change yoneda.map gO ≫ yoneda.map fr ≫ q.special = _
        rw [← Functor.map_comp_assoc, hsquare, Functor.map_comp_assoc] }
  let ext : q.DominatingExtension :=
    { square := square
      ringMap := φ
      fieldMap := ψ
      isLocalHom := hloc
      fraction_comm := hfrac
      base_comm := rfl
      genericOver := gO
      genericOver_left := rfl
      specialOver := sO
      specialOver_left := rfl
      generic_comm := rfl
      special_comm := rfl }
  refine ⟨ext, ⟨?_⟩⟩
  -- The lift.
  have hdiag : (uliftYoneda.{w}.map sO ≫ a) ≫ pullback.diagonal f =
      uliftYoneda.{w}.map (sO ≫ sR) ≫ g := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Functor.map_comp,
        Category.assoc, Category.assoc, ha]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, heq, Functor.map_comp,
        Category.assoc, Category.assoc, hb]
  set l := hp.lift (uliftYoneda.{w}.map sO ≫ a) (uliftYoneda.{w}.map (sO ≫ sR)) hdiag with hl
  set l' := uliftYoneda.{w}.preimage l with hl'
  have hl'map : uliftYoneda.{w}.map l' = l := Functor.map_preimage _ _
  have hspecial : l' ≫ snd = sO ≫ sR := by
    apply uliftYoneda.{w}.map_injective
    rw [Functor.map_comp, hl'map, hl, hp.lift_snd]
  have hgeneric : fr' ≫ l' = gO ≫ gK := by
    apply uliftYoneda.{w}.map_injective
    apply hp.hom_ext
    · rw [Functor.map_comp, Category.assoc, hl'map, hl, hp.lift_fst, ← Functor.map_comp_assoc,
        ← hsquare, Functor.map_comp_assoc, ha, hgen _ (pullback.diagonal_fst f),
        Functor.map_comp, Category.assoc]
    · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc, hspecial,
        hcomm, reassoc_of% hsquare]
  exact
    { map := yoneda.map l'
      generic_comm := by
        change yoneda.map fr' ≫ yoneda.map l' = yoneda.map gO ≫ q.generic
        rw [← hgK, ← Functor.map_comp, ← Functor.map_comp, hgeneric]
      special_comm := by
        change yoneda.map l' ≫ yoneda.map snd = yoneda.map sO ≫ q.special
        rw [← hsR, ← Functor.map_comp, ← Functor.map_comp, hspecial] }

/-- **Separatedness from a quasi-compact immersive diagonal and the uniqueness part of the
valuative criterion.** Let `f : F ⟶ G` be a morphism of presheaves on the big fppf site of `S`
with values in `Type (max w u)`. If the relative diagonal of `f` is representable by
quasi-compact immersions of schemes, and `f` satisfies the uniqueness part of the valuative
criterion up to an extension of valuation rings, then `f` is separated: its relative diagonal is
a closed immersion.

This is the argument of Stacks 03KV, for a morphism whose diagonal is known to be representable
by immersions rather than a morphism of algebraic spaces: each represented base change of the
diagonal is a quasi-compact morphism satisfying the existence part of the valuative criterion,
hence universally closed by Stacks 03KA, and an immersion with closed image is a closed
immersion. -/
theorem isSeparatedULift_of_diagonal_of_valuativeUniqueness (f : F ⟶ G)
    (hΔ : (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) ⊓
        (@QuasiCompact.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{w} (pullback.diagonal f))
    (hval : ValuativeUniquenessUpToExtension.{w} f) :
    IsSeparatedULift.{w} B S hS f := by
  refine ⟨hΔ.1, fun V W g fst snd hp ↦ ?_⟩
  obtain ⟨himm, hqc⟩ := hΔ.2 g fst snd hp
  have himm' : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map snd) := himm
  have hqc' : QuasiCompact ((BigFppfOver.toScheme B S hS).map snd) := hqc
  have hqcY : IsQuasiCompact B S hS (yoneda.map snd) :=
    isQuasiCompact_of_presheaf_quasiCompact B S hS
      ((presheaf_yoneda_map_iff B S hS (P := @QuasiCompact.{u}) inferInstance snd).mpr hqc')
  have hUC : UniversallyClosed B S hS (yoneda.map snd) :=
    universallyClosed_of_isQuasiCompact_of_valuativeCriterion_existence
      (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS V) (yoneda.map snd)
      hqcY (valuativeCriterion_existence_of_diagonal_uniqueness f hval g fst snd hp)
  have hUC' : AlgebraicGeometry.UniversallyClosed ((BigFppfOver.toScheme B S hS).map snd) :=
    (presheaf_yoneda_map_iff B S hS (P := @AlgebraicGeometry.UniversallyClosed.{u})
      inferInstance snd).mp
      (presheaf_universallyClosed_of_universallyClosed B S hS
        (Functor.relativelyRepresentable.map yoneda snd) hUC)
  change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd)
  exact IsClosedImmersion.of_isPreimmersion _
    ((BigFppfOver.toScheme B S hS).map snd).isClosedMap.isClosed_range

end Diagonal

end AlgebraicGeometry.Space

end
