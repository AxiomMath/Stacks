module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparablePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparableChartPoint

/-!
# The étale chart point over the diagonal, in an affine chart where it is closed

The proof of Stacks 0DSB compares deformation categories at an `L`-point of a smooth chart `V`
of `𝒳` and at an `L`-point `w₀` of an étale chart `W` of the self-intersection `R = V ×_𝒳 V`.
Prorepresenting the deformations of a scheme at an `L`-point through an affine chart
(`Deformation.Artin.SliceTangent.exists_sliceEquivalence_completion`) needs the chart ring map
to be a surjection onto a subfield `K ⊆ L` with `L/K` separable: the point must be closed in the
chart. On `V` the chart point of `AlgebraicGeometry.Stack.exists_smoothChart_point_residueField_eq`
has this with `K = l`. This file provides it on `W`.

Since `l` is of finite type over `Λ`, so is `L`, so `w₀ : Spec L ⟶ W` is locally of finite type,
and by `AlgebraicGeometry.finiteType_specField_tfae` some affine
open `U ∋ w₀` has `Γ(U) ⟶ L` finite. On a basic open inside `U` and over `Spec Λ` the ring map is
still finite; its image is a domain over which the field `L` is integral, hence a subfield `K`.
`L/K` is separable because `K` contains the image of `l` (the chart of `V` at `ν` maps onto `l`)
and `L/l` is separable.

## Main results

* `RingHom.Finite.exists_subfield_range_eq`: the image of a finite ring map to a field is a
  subfield.
* `AlgebraicGeometry.Stack.affineChart_ringMap_eq_appLE`: the chart ring map is the map on
  sections.
* `AlgebraicGeometry.Stack.exists_affineChart_subfield_of_comp_eq`: the chart.
* `AlgebraicGeometry.Stack.exists_etaleChart_point_affineChart_selfIntersection`: the
  strengthened étale step of the proof of Stacks 0DSB.

## Implementation notes

The ring map onto `L` itself need not be surjective: `L` is a residue field of
`W ×_R Spec l`, which can be strictly larger than the residue field `K` of `W` at `w₀` because
`R` need not be decent. The prorepresentation result consumes exactly the surjection onto `K`.

## References

* [Stacks Project, Tag 0DSB](https://stacks.math.columbia.edu/tag/0DSB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

/-- **The image of a finite ring map into a field is a subfield**, over which the field is
finite: the field is integral over the image, a domain, which is therefore a field. -/
theorem RingHom.Finite.exists_subfield_range_eq {R L : Type*} [CommRing R] [Field L]
    (ψ : R →+* L) (hψ : ψ.Finite) :
    ∃ K : Subfield L, (K : Set L) = Set.range ψ ∧ Module.Finite K L := by
  let R' := ψ.range
  let : Algebra R' L := R'.subtype.toAlgebra
  have hfin : Module.Finite R' L :=
    RingHom.Finite.of_comp_finite (f := ψ.rangeRestrict) (g := R'.subtype) hψ
  have hfield : IsField R' :=
    (Algebra.IsIntegral.isField_iff_isField (R := R') (S := L) Subtype.val_injective).mpr
      (Field.toIsField L)
  let K : Subfield L :=
    { R' with
      inv_mem' := fun x hx => by
        by_cases h0 : x = 0
        · simp [h0]
        · obtain ⟨y, hy⟩ :=
            hfield.mul_inv_cancel (a := ⟨x, hx⟩) (fun h => h0 (congrArg Subtype.val h))
          have hy' : x * (y : L) = 1 := congrArg Subtype.val hy
          rw [inv_eq_of_mul_eq_one_right hy']
          exact y.2 }
  exact ⟨K, rfl, hfin⟩

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion

open Deformation.Artin.SliceTangent

/-- The ring map of an affine chart attached to a morphism `Spec A ⟶ Y` is the map on sections
over the chart, read through `Γ(Spec A) ≅ A`. -/
theorem affineChart_ringMap_eq_appLE {S Y : Scheme.{u}} {s : Y ⟶ S} {Λ : Type u} [CommRing Λ]
    {iΛ : Spec (.of Λ) ⟶ S} [_root_.AlgebraicGeometry.IsOpenImmersion iΛ] {y₀ : Y}
    (c : AffineChart iΛ s y₀) {A : CommRingCat.{u}} (g : Spec A ⟶ Y)
    (hg : Set.range g.base ⊆ c.U) (hle : ⊤ ≤ g ⁻¹ᵁ c.U) :
    c.ringMap g hg = g.appLE c.U ⊤ hle ≫ (Scheme.ΓSpecIso A).hom := by
  apply Spec.map_injective
  apply (cancel_mono c.fromSpec).mp
  rw [c.spec_ringMap, Spec.map_comp, Category.assoc,
    c.isAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hle,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
  simp

/-- **An affine chart in which a field-valued point is closed, with its residue field.** Let
`g : Spec L ⟶ Y` be locally of finite type, lying over `e : Spec l ⟶ X` along `Spec L ⟶ Spec l`
through `q : Y ⟶ X` over `S`, with `L/l` separable, and suppose some affine chart of `X` at `e`
has ring map onto `l` surjective. Then some affine chart `c` of `Y` at `g`, lying over `Spec Λ`,
has ring map onto a subfield `K ⊆ L` with `L/K` finite and separable. (The point is closed in `c`
and `K` is its residue field.) -/
theorem exists_affineChart_subfield_of_comp_eq {S X Y : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S}
    (q : Y ⟶ X) (hq : q ≫ sX = sY) {Λ : Type u} [CommRing Λ] {iΛ : Spec (.of Λ) ⟶ S}
    [_root_.AlgebraicGeometry.IsOpenImmersion iΛ] {L l : Type u} [Field L] [Field l]
    [Algebra l L] [Algebra.IsSeparable l L] (g : Spec (.of L) ⟶ Y) [LocallyOfFiniteType g]
    (e : Spec (.of l) ⟶ X) (h : g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫ e)
    (cX : AffineChart iΛ sX (e.base (closedPt (.of l))))
    (hcX : Function.Surjective (cX.ringMap e (cX.range_subset e cX.mem))) :
    ∃ (c : AffineChart iΛ sY (g.base (closedPt (.of L)))) (K : Subfield L),
      Set.range (c.ringMap g (c.range_subset g c.mem)) = (K : Set L) ∧ Module.Finite K L ∧
        Algebra.IsSeparable K L := by
  classical
  set y := g.base (closedPt (.of L)) with hy
  have hqy : q.base y = e.base (closedPt (.of l)) := by
    show (g ≫ q).base (closedPt (.of L)) = _
    rw [h, Scheme.Hom.comp_base, TopCat.comp_app]
    exact congrArg e.base (Subsingleton.elim _ _)
  let O : Y.Opens := q ⁻¹ᵁ cX.U
  have hyO : y ∈ O := by change q.base y ∈ cX.U; rw [hqy]; exact cX.mem
  obtain ⟨U, hU, hfinU⟩ := ((finiteType_specField_tfae g).out 2 3).mp ‹LocallyOfFiniteType g›
  have hyU : y ∈ U.1 := hU (Set.mem_univ (closedPt (.of L)) : _ ∈ (⊤ : (Spec (.of L)).Opens))
  obtain ⟨r, hrle, hyr⟩ := U.2.exists_basicOpen_le (V := U.1 ⊓ O) ⟨y, hyU, hyO⟩ hyU
  let c : AffineChart iΛ sY y :=
    { U := Y.basicOpen r
      isAffineOpen := U.2.basicOpen r
      mem := hyr
      le := fun z hz => by
        show sY.base z ∈ Set.range iΛ.base
        rw [← hq]
        exact cX.le (hrle hz).2 }
  have hle : ⊤ ≤ g ⁻¹ᵁ c.U := (Scheme.preimage_eq_top_of_closedPoint_mem g hyr).ge
  set ψ := c.ringMap g (c.range_subset g c.mem) with hψ
  have hψeq : ψ = g.appLE c.U ⊤ hle ≫ (Scheme.ΓSpecIso (.of L)).hom :=
    affineChart_ringMap_eq_appLE c g _ hle
  have hψfin : ψ.hom.Finite := by
    have hcomp : (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op ≫ ψ) =
        g.appLE U.1 ⊤ hU ≫ (Scheme.ΓSpecIso (.of L)).hom := by
      rw [hψeq, g.map_appLE_assoc]
    have h' : (ψ.hom.comp (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom).Finite := by
      rw [← CommRingCat.hom_comp, hcomp]; exact hfinU
    exact RingHom.Finite.of_comp_finite h'
  obtain ⟨K, hK, hKfin⟩ := RingHom.Finite.exists_subfield_range_eq ψ.hom hψfin
  refine ⟨c, K, hK.symm, hKfin, ?_⟩
  -- the image of `l` lies in `K`
  have hcU : c.U ≤ q ⁻¹ᵁ cX.U := fun z hz => (hrle hz).2
  have hsq : q.appLE cX.U c.U hcU ≫ ψ =
      cX.ringMap e (cX.range_subset e cX.mem) ≫ CommRingCat.ofHom (algebraMap l L) := by
    apply Spec.map_injective
    apply (cancel_mono cX.fromSpec).mp
    rw [Spec.map_comp, Category.assoc, cX.isAffineOpen.SpecMap_appLE_fromSpec q c.isAffineOpen hcU,
      ← Category.assoc, c.spec_ringMap, h, Spec.map_comp, Category.assoc, cX.spec_ringMap]
  have hmem : ∀ a : l, algebraMap l L a ∈ K := by
    intro a
    obtain ⟨t, ht⟩ := hcX a
    have := congrArg (fun φ => φ t) hsq
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, ht] at this
    rw [← SetLike.mem_coe, hK]
    exact ⟨(q.appLE cX.U c.U hcU) t, this⟩
  let : Algebra l K := ((algebraMap l L).codRestrict K hmem).toAlgebra
  have : IsScalarTower l K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.isSeparable_tower_top_of_isSeparable l K L

/-- **An étale chart point over the diagonal point of a self-intersection, in a chart where it
is closed (the étale step of the proof of Stacks 0DSB).** This is
`AlgebraicGeometry.Stack.exists_etaleChart_point_isSeparable_selfIntersection`, with the residue
field hypothesis at `u₀` in the chart form produced by
`AlgebraicGeometry.Stack.exists_smoothChart_point_residueField_eq` and with `l` of finite type over
`Λ`, together with an affine chart `c` of `W` at `w₀`, lying over `Spec Λ`, whose ring map onto
`L` has image a subfield `K` with `L/K` finite separable: `w₀` is closed in `c`, and `K` is its
residue field there. -/
theorem exists_etaleChart_point_affineChart_selfIntersection (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (V : BigFppfOver B S hS) (g : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (T : Bicategory.TwoCommSq g g) (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hQ : IsAlgebraicSpace B S hS Q)
    (eV : StacksRepresentableCFG.EquivalenceOver
      (schemeStack.{u, w} B S hS V).val.val.p
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      T.pt.val.val.p (presheafOfCategories (Q ⋙ typeToCat)).p)
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS V g) T)
    {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l] [Algebra.FiniteType Λ l]
    {iΛ : Spec (.of Λ) ⟶ S} [_root_.AlgebraicGeometry.IsOpenImmersion iΛ]
    (u₀ : Over V)
    (hu₀ : (Over.forget V ⋙ Over.post B.inclusion).obj u₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (hchart : ∀ c : AffineChart iΛ (B.inclusion.map V.hom) ((pointMap hu₀).base (closedPt (.of l))),
      Function.Surjective (c.ringMap (pointMap hu₀) (range_pointMap c))) :
    ∃ (W : BigFppfOver B S hS) (a : yoneda.obj W ⟶ Q),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra l L) (_ : Algebra Λ L) (_ : IsScalarTower Λ l L),
        Module.Finite l L ∧ Algebra.IsSeparable l L ∧
        ∃ (w₀ : Over W)
          (hw₀ : (Over.forget W ⋙ Over.post B.inclusion).obj w₀ =
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ L)) ≫ iΛ))
          (π : w₀.left ⟶ u₀.left),
          eqToHom (congrArg Over.left hw₀).symm ≫ B.inclusion.map π.left ≫
              eqToHom (congrArg Over.left hu₀) = Spec.map (CommRingCat.ofHom (algebraMap l L)) ∧
          yoneda.map w₀.hom ≫ a = yoneda.map π ≫ yoneda.map u₀.hom ≫
            selfIntersectionDiagonalMap B S hS V g T Q eV eQ δ ∧
          (letI := (Scheme.SpecToEquivOfField L _ (pointMap hw₀)).2.hom.toAlgebra
          Algebra.IsSeparable ((B.inclusion.obj W.left).residueField
            (Scheme.SpecToEquivOfField L _ (pointMap hw₀)).1) L) ∧
          ∃ (c : AffineChart iΛ (B.inclusion.map W.hom) ((pointMap hw₀).base (closedPt (.of L))))
            (K : Subfield L),
            Set.range (c.ringMap (pointMap hw₀) (range_pointMap c)) = (K : Set L) ∧
              Module.Finite K L ∧ Algebra.IsSeparable K L := by
  obtain ⟨cV⟩ := nonempty_affineChart (s := B.inclusion.map V.hom) (iΛ := iΛ)
    (pointMap_mem_range (hv₀ := hu₀))
  obtain ⟨W, a, hsurj, het, L, _, _, _, _, hfin, hsep, w₀, hw₀, π, hπ, hyon, hsepw⟩ :=
    exists_etaleChart_point_isSeparable_selfIntersection B S hS V g T Q hQ eV eQ δ u₀ hu₀
      (surjective_residueFieldMap_of_surjective_ringMap _ cV (range_pointMap cV) (hchart cV))
  refine ⟨W, a, hsurj, het, L, inferInstance, inferInstance, inferInstance, inferInstance, hfin,
    hsep, w₀, hw₀, π, hπ, hyon, hsepw, ?_⟩
  -- the scheme morphism `W ⟶ V` underlying `a ≫ s`
  let qs : W ⟶ V := yoneda.preimage (a ≫ selfIntersectionSourceMap B S hS V g T Q eV eQ)
  have hq : w₀.hom ≫ qs = π ≫ u₀.hom := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, ← Category.assoc, hyon,
      Category.assoc, Category.assoc, selfIntersectionDiagonalMap_comp_sourceMap,
      Category.comp_id]
  have hcomp : pointMap hw₀ ≫ B.inclusion.map qs.left =
      Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫ pointMap hu₀ := by
    have h1 : B.inclusion.map w₀.hom.left ≫ B.inclusion.map qs.left =
        B.inclusion.map π.left ≫ B.inclusion.map u₀.hom.left := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun f => B.inclusion.map f.left) hq
    rw [← hπ]
    simp only [pointMap, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [h1]
  have hqV : B.inclusion.map qs.left ≫ B.inclusion.map V.hom = B.inclusion.map W.hom := by
    rw [← Functor.map_comp, Over.w qs]
  have hΛL : Algebra.FiniteType Λ L := .trans ‹Algebra.FiniteType Λ l› inferInstance
  have : LocallyOfFiniteType (pointMap hw₀) := by
    have hspec : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ L))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr hΛL)
    have : LocallyOfFiniteType (pointMap hw₀ ≫ B.inclusion.map W.hom) := by
      rw [pointMap_comp]; infer_instance
    exact locallyOfFiniteType_of_comp _ (B.inclusion.map W.hom)
  exact exists_affineChart_subfield_of_comp_eq
    (B.inclusion.map qs.left) hqV (pointMap hw₀) (pointMap hu₀) hcomp cV (hchart cV)

end AlgebraicGeometry.Stack

end
