module

public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.RefinedProperness
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.DominatedLift
public import StacksFrontier.AlgebraicGeometry.Stacks.DenseTestValuative.Hypothesis

/-!
# The hypothesis of Stacks 0CQM for morphisms of schemes, at generic points

Let `a : W ⟶ Z` and `b : Z ⟶ V` be morphisms of the big fppf site of `S`, with `a` locally of
finite type, quasi-compact and dominant. Suppose that the 1-morphisms of algebraic stacks they
induce satisfy the hypothesis of **Stacks 0CQM**
(`AlgebraicGeometry.Stack.ValuativeCriterion.DenseTestExistence`). Then for every generic point
`η` of an irreducible component of `Z` and every discrete valuation ring `A ⊂ κ(η)` with
fraction field `κ(η)`, every commutative square
```
Spec κ(η) ---> Z
    |          | b
    v          v
  Spec A ----> V
```
with the canonical upper arrow has a dotted arrow. This is the existence half of condition (4)
of **Stacks 0208** for `b`.

## Main results

* `AlgebraicGeometry.Stack.nonempty_liftStruct_of_denseTestExistence`: the dotted arrow exists.

## Implementation notes

This is the step of the proof of Stacks 0CQM where the test morphism is used. The point `η` is
the image of a point `w` of `W`, because `a` is quasi-compact and dominant (Stacks 01RL), and
`κ(w)` is a finitely generated extension of `κ(η)` because `a` is locally of finite type, so the
discrete valuation ring `A` is dominated by a discrete valuation ring `A₁ ⊂ κ(w)` with fraction
field `κ(w)` (Stacks 00PH). The square over `A₁` whose generic arrow is
`Spec κ(w) ⟶ W ⟶ Z` is a valuative square for the composite of the two induced 1-morphisms, with
`Spec κ(w) ⟶ W` as test arrow; both spectra are small enough to lie in the site. The hypothesis
gives a dotted arrow over a valuation ring dominating `A₁`, hence dominating `A`, which is read
back as a morphism of schemes through the 2-Yoneda lemma
(`AlgebraicGeometry.Stack.schemeMapOfFunctor`) and descended to `A` by
`AlgebraicGeometry.exists_liftStruct_fromSpecResidueField_of_dominating`.

## References

* [Stacks Project, Tag 0CQM](https://stacks.math.columbia.edu/tag/0CQM)
* [Stacks Project, Tag 0208](https://stacks.math.columbia.edu/tag/0208)
* [Stacks Project, Tag 01RL](https://stacks.math.columbia.edu/tag/01RL)
* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory IsLocalRing

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The hypothesis of Stacks 0CQM for morphisms of schemes gives the existence half of
condition (4) of Stacks 0208.** Let `a : W ⟶ Z` be locally of finite type, quasi-compact and
dominant, and let `b : Z ⟶ V`. If the 1-morphisms of algebraic stacks induced by `a` and `b`
satisfy the hypothesis of Stacks 0CQM, then every canonical square at the residue field of a
generic point of `Z` with a discrete valuation ring of that residue field has a dotted arrow. -/
theorem nonempty_liftStruct_of_denseTestExistence {W Z V : BigFppfOver B S hS}
    (a : W ⟶ Z) (b : Z ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map a)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map a)]
    (hdense : DenseRange ((BigFppfOver.toScheme B S hS).map a).base)
    (hlift : ValuativeCriterion.DenseTestExistence.{u, w} B S hS
      (schemeStackMap.{u, w} B S hS a) (schemeStackMap.{u, w} B S hS b))
    (η : (BigFppfOver.toScheme B S hS).obj Z)
    (hη : η ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj Z))
    (A : Subring (((BigFppfOver.toScheme B S hS).obj Z).residueField η))
    (hA : IsDiscreteValuationRing A)
    (hAK : IsFractionRing A (((BigFppfOver.toScheme B S hS).obj Z).residueField η))
    (i₂ : Spec (.of A) ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (sq : CommSq (((BigFppfOver.toScheme B S hS).obj Z).fromSpecResidueField η)
      (Spec.map (CommRingCat.ofHom A.subtype)) ((BigFppfOver.toScheme B S hS).map b) i₂) :
    Nonempty sq.LiftStruct := by
  let T := BigFppfOver.toScheme B S hS
  let ha : T.obj W ⟶ T.obj Z := T.map a
  let hb : T.obj Z ⟶ T.obj V := T.map b
  have hdom : IsDominant ha := ⟨hdense⟩
  obtain ⟨w₀, rfl⟩ := (isDominant_iff_genericPoints_subset_range ha).mp hdom hη
  have _ : IsFractionRing A ((T.obj Z).residueField (ha.base w₀)) := hAK
  -- a discrete valuation ring of `κ(w₀)` dominating `A`
  let kη := (T.obj Z).residueField (ha.base w₀)
  let kw := (T.obj W).residueField w₀
  let _ : Algebra kη kw := (ha.residueFieldMap w₀).hom.toAlgebra
  have _ : Algebra.EssFiniteType kη kw :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap (f := ha) w₀)
  let _ : Algebra A kw := ((algebraMap kη kw).comp (algebraMap A kη)).toAlgebra
  have _ : IsScalarTower A kη kw := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨A₁, hA₁dvr, hA₁frac, hA₁loc⟩ :=
    _root_.exists_isDiscreteValuationRing_isFractionRing_of_not_isField
      (R := A) kη (L := kw) (IsDiscreteValuationRing.not_isField A)
  have hring : CommRingCat.ofHom (algebraMap A A₁) ≫ CommRingCat.ofHom (algebraMap A₁ kw) =
      CommRingCat.ofHom A.subtype ≫ ha.residueFieldMap w₀ := by
    ext x
    exact (IsScalarTower.algebraMap_apply A A₁ kw x).symm
  have hspec := congrArg Spec.map hring
  rw [Spec.map_comp, Spec.map_comp] at hspec
  -- the two spectra lie in the site
  have hK : B.Contains (Spec (.of kw)) :=
    BigFppfSite.residueField_spec_contains B W.left.property w₀
  have hR : B.Contains (Spec (.of A₁)) :=
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hK
      ((Cardinal.mk_le_of_injective (IsFractionRing.injective A₁ kw)).trans (le_max_right _ _))
  -- the valuative square
  let gen : Spec (.of kw) ⟶ Spec (.of A₁) := Spec.map (CommRingCat.ofHom (algebraMap A₁ kw))
  let toV : Spec (.of A₁) ⟶ T.obj V := Spec.map (CommRingCat.ofHom (algebraMap A A₁)) ≫ i₂
  let base : Spec (.of A₁) ⟶ S := toV ≫ B.inclusion.map V.hom
  let Aobj := siteObject B S hS hR base
  let Kobj := siteObject B S hS hK (gen ≫ base)
  have hab : ha ≫ hb ≫ B.inclusion.map V.hom = B.inclusion.map W.hom := by
    have h1 := congrArg B.inclusion.map (Over.w b)
    have h2 := congrArg B.inclusion.map (Over.w a)
    rw [B.inclusion.map_comp] at h1 h2
    calc ha ≫ hb ≫ B.inclusion.map V.hom
        = B.inclusion.map a.left ≫ B.inclusion.map b.left ≫ B.inclusion.map V.hom := rfl
      _ = B.inclusion.map a.left ≫ B.inclusion.map Z.hom := by rw [h1]
      _ = _ := h2
  have hsq : (T.obj W).fromSpecResidueField w₀ ≫ ha ≫ hb = gen ≫ toV := by
    calc (T.obj W).fromSpecResidueField w₀ ≫ ha ≫ hb
        = (Spec.map (ha.residueFieldMap w₀) ≫ (T.obj Z).fromSpecResidueField (ha.base w₀)) ≫
            hb := by
          rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
          rfl
      _ = Spec.map (ha.residueFieldMap w₀) ≫ (Spec.map (CommRingCat.ofHom A.subtype) ≫ i₂) := by
          rw [Category.assoc, sq.w]
      _ = (Spec.map (ha.residueFieldMap w₀) ≫ Spec.map (CommRingCat.ofHom A.subtype)) ≫ i₂ :=
          (Category.assoc _ _ _).symm
      _ = (gen ≫ Spec.map (CommRingCat.ofHom (algebraMap A A₁))) ≫ i₂ :=
          (congrArg (fun k => k ≫ i₂) hspec).symm
      _ = gen ≫ toV := Category.assoc _ _ _
  let hOver : Aobj ⟶ V := Over.homMk (⟨toV⟩ : Aobj.left ⟶ V.left)
    (B.inclusion.map_injective rfl)
  let jOver : Kobj ⟶ Aobj := Over.homMk (⟨gen⟩ : Kobj.left ⟶ Aobj.left)
    (B.inclusion.map_injective rfl)
  let kOver : Kobj ⟶ W := Over.homMk (⟨(T.obj W).fromSpecResidueField w₀⟩ : Kobj.left ⟶ W.left)
    (by
      apply B.inclusion.map_injective
      show (T.obj W).fromSpecResidueField w₀ ≫ B.inclusion.map W.hom = gen ≫ base
      rw [← hab, ← Category.assoc, ← Category.assoc, Category.assoc _ ha, hsq]
      rfl)
  let jCat := schemeFibredCategoryMap B S hS jOver
  let hCat := schemeFibredCategoryMap B S hS hOver
  let kCat := schemeFibredCategoryMap B S hS kOver
  have hmaps : schemeMapOfFunctor B S hS (jCat ≫ hCat).hom =
      schemeMapOfFunctor B S hS
        (kCat ≫ (schemeStackMap.{u, w} B S hS a ≫ schemeStackMap.{u, w} B S hS b).hom).hom := by
    show _ = schemeMapOfFunctor B S hS (kCat ≫ (schemeFibredCategoryMap B S hS a ≫
      schemeFibredCategoryMap B S hS b)).hom
    rw [schemeMapOfFunctor_comp, schemeMapOfFunctor_comp, schemeMapOfFunctor_comp,
      schemeMapOfFunctor_schemeFibredCategoryMap, schemeMapOfFunctor_schemeFibredCategoryMap,
      schemeMapOfFunctor_schemeFibredCategoryMap, schemeMapOfFunctor_schemeFibredCategoryMap,
      schemeMapOfFunctor_schemeFibredCategoryMap]
    exact Over.OverMorphism.ext (B.inclusion.map_injective hsq.symm)
  let q : ValuativeSquare B S hS
      (schemeStackMap.{u, w} B S hS a ≫ schemeStackMap.{u, w} B S hS b) :=
    { R := A₁
      K := kw
      ring_mem := hR
      field_mem := hK
      base := base
      genericMap := jOver
      genericMap_left := rfl
      j := jCat
      j_canonical := rfl
      x := kCat
      y := hCat
      γ := hom₂OfSchemeMapEq B S hS _ _ hmaps }
  obtain ⟨e, ⟨d⟩⟩ := hlift q hA₁dvr
  -- the dotted arrow, read as a morphism of schemes
  let l' : Spec (.of e.R') ⟶ T.obj Z := T.map (schemeMapOfFunctor B S hS d.a.hom)
  have hα := schemeMapOfFunctor_eq_of_hom₂ B S hS d.α
  have hβ := schemeMapOfFunctor_eq_of_hom₂ B S hS d.β
  change schemeMapOfFunctor B S hS (e.j ≫ d.a).hom =
    schemeMapOfFunctor B S hS (e.k ≫ kCat ≫ schemeFibredCategoryMap B S hS a).hom at hα
  change schemeMapOfFunctor B S hS (e.a ≫ hCat).hom =
    schemeMapOfFunctor B S hS (d.a ≫ schemeFibredCategoryMap B S hS b).hom at hβ
  rw [schemeMapOfFunctor_comp, schemeMapOfFunctor_comp, schemeMapOfFunctor_comp,
    schemeMapOfFunctor_eq_of_hom_toFunctor_eq B S hS _ _ e.j_canonical,
    schemeMapOfFunctor_eq_of_hom_toFunctor_eq B S hS _ _ e.k_canonical,
    schemeMapOfFunctor_schemeFibredCategoryMap,
    schemeMapOfFunctor_schemeFibredCategoryMap] at hα
  rw [schemeMapOfFunctor_comp, schemeMapOfFunctor_comp,
    schemeMapOfFunctor_eq_of_hom_toFunctor_eq B S hS _ _ e.a_canonical,
    schemeMapOfFunctor_schemeFibredCategoryMap,
    schemeMapOfFunctor_schemeFibredCategoryMap] at hβ
  have hα' := congrArg T.map hα
  have hβ' := congrArg T.map hβ
  simp only [Functor.map_comp] at hα' hβ'
  have hgenericMap : T.map e.genericMap = Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) :=
    e.genericMap_left
  have hgenericOver : T.map e.genericOver = Spec.map (CommRingCat.ofHom e.fieldMap) :=
    e.genericOver_left
  have hspecialOver : T.map e.specialOver = Spec.map (CommRingCat.ofHom e.ringMap) :=
    e.specialOver_left
  rw [hgenericMap, hgenericOver] at hα'
  rw [hspecialOver] at hβ'
  -- descend the dotted arrow to `A`
  let ψ : A →+* e.R' := e.ringMap.comp (algebraMap A A₁)
  let χ : kη →+* e.K' := e.fieldMap.comp (ha.residueFieldMap w₀).hom
  have _ : IsLocalHom e.ringMap := e.isLocalHom
  have _ : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
  have _ : ValuationRing A := inferInstance
  have hcomm : (algebraMap e.R' e.K').comp ψ = χ.comp A.subtype := by
    ext x
    have h1 := RingHom.congr_fun e.fraction_comm (algebraMap A A₁ x)
    have h2 := congrArg (fun k => k.hom x) hring
    simp only [RingHom.comp_apply] at h1 h2
    show algebraMap e.R' e.K' (e.ringMap (algebraMap A A₁ x)) =
      e.fieldMap ((ha.residueFieldMap w₀).hom (A.subtype x))
    rw [h1]
    exact congrArg e.fieldMap h2
  refine exists_liftStruct_fromSpecResidueField_of_dominating hb (ha.base w₀) A i₂ sq ψ χ hcomm
    l' ?_ ?_
  · refine hα'.trans ?_
    show Spec.map (CommRingCat.ofHom e.fieldMap) ≫ (T.obj W).fromSpecResidueField w₀ ≫ ha = _
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp]
    rfl
  · refine hβ'.symm.trans ?_
    show Spec.map (CommRingCat.ofHom e.ringMap) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A A₁)) ≫ i₂ = _
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

end AlgebraicGeometry.Stack

end
