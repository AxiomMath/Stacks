module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedImmersionAmbient
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Sections of the completion of a solution of the contraction problem

Let `s` be a solution of Artin's contraction problem of Stacks 0GH8 with target `X`, and suppose
that `W` is identified with the completion of a represented presheaf `h_P` along a point `p`. The
isomorphism `a : X_{/T} ≅ W` then gives, for every object `Y` of the site, a bijection, natural in
`Y`, between the sections of `X` over `Y` with point-set image in `T` and the morphisms `Y ⟶ P`
with point-set image `{p}`: both completions are the subfunctors of sections with the given
point-set image, `X` and `h_P` being fppf sheaves.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.Solution.completionEquiv`: the bijection.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.Solution.completionEquiv_map`,
  `AlgebraicGeometry.Artin.ContractionSituation.Solution.completionEquiv_symm_map`: its
  naturality.
* `AlgebraicGeometry.Space.hasImageIn_yoneda_iff_range_eq`: a morphism `Y ⟶ P` has point-set image
  in the point of `h_P` given by a point `p` of `P` exactly when its underlying map of schemes
  is constant with value `p`.
* `AlgebraicGeometry.Space.hasImageIn_app_of_forall_eq`: the image under a chart
  `h_V ⟶ X` of a morphism `Y ⟶ V` with constant value `v` has point-set image in a set
  containing the image of `v`.

## References

* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism `Y ⟶ P` of the site has point-set image in the point of `h_P` given by a point
`p` of the scheme `P` exactly when its underlying map of schemes is constant with value `p`. -/
theorem hasImageIn_yoneda_iff_range_eq {P Y : BigFppfOver B S hS}
    (p : (BigFppfOver.toScheme B S hS).obj P) (g : Y ⟶ P) :
    HasImageIn B S hS (yoneda.obj P) {(schemePointsHomeomorph B S hS P).symm p} Y g ↔
      ∀ y, (BigFppfOver.toScheme B S hS).map g y = p := by
  rw [hasImageIn_iff_range_subset,
    show yonedaEquiv.symm g = yoneda.map g from
      yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map g).symm,
    range_pointsMap_yoneda_map_eq_schemePointsHomeomorph_preimage]
  constructor
  · intro h y
    have hy : (schemePointsHomeomorph B S hS P).symm ((BigFppfOver.toScheme B S hS).map g y) ∈
        schemePointsHomeomorph B S hS P ⁻¹'
          Set.range ((BigFppfOver.toScheme B S hS).map g).base := by
      simp
    have := h hy
    rw [Set.mem_singleton_iff] at this
    simpa using congrArg (schemePointsHomeomorph B S hS P) this
  · rintro h z ⟨y, hy⟩
    rw [Set.mem_singleton_iff, ← hy.symm.trans (h y), Homeomorph.symm_apply_apply]

/-- The image under a morphism `a : h_V ⟶ X` of a morphism `k : Y ⟶ V` of the site whose
underlying map of schemes is constant with value `v` has point-set image in every set containing
the image of `v`. -/
theorem hasImageIn_app_of_forall_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : Set (points B S hS X)} {V Y : BigFppfOver B S hS} (a : yoneda.obj V ⟶ X) (k : Y ⟶ V)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hk : ∀ y, (BigFppfOver.toScheme B S hS).map k y = v)
    (hv : pointsMap B S hS (yoneda.obj V) a ((schemePointsHomeomorph B S hS V).symm v) ∈ T) :
    HasImageIn B S hS X T Y (a.app (op Y) k) := by
  have hka : yonedaEquiv.symm (a.app (op Y) k) = yoneda.map k ≫ a := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [hasImageIn_iff_range_subset, hka, pointsMap_comp, Set.range_comp,
    range_pointsMap_yoneda_map_eq_schemePointsHomeomorph_preimage]
  rintro _ ⟨z, ⟨y, hy⟩, rfl⟩
  have hz : z = (schemePointsHomeomorph B S hS V).symm v := by
    rw [← hk y, hy, Homeomorph.symm_apply_apply]
  rw [hz]
  exact hv

end Space

namespace Artin.ContractionSituation.Solution

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {c : ContractionSituation B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (s : Solution c X) {P : BigFppfOver B S hS} {p : Space.points B S hS (yoneda.obj P)}
    (eW : c.W ≅ Space.completionSheaf B S hS (yoneda.obj P) {p})

/-- The isomorphism between the subfunctor of sections of `X` with point-set image in `T` and the
subfunctor of morphisms to `P` with point-set image `{p}`, induced by `a : X_{/T} ≅ W` and an
identification of `W` with the completion of `h_P` along `p`. -/
def completionSubfunctorIso :
    (Space.completionSubfunctor B S hS X s.T).toFunctor ≅
      (Space.completionSubfunctor B S hS (yoneda.obj P) {p}).toFunctor :=
  (Space.completionSheafIsoSubfunctor B S hS s.isAlgebraicSpace_X.isSheaf s.T).symm ≪≫
    (sheafToPresheaf _ _).mapIso (s.a ≪≫ eW) ≪≫
    Space.completionSheafIsoSubfunctor B S hS (isAlgebraicSpace_yoneda B S hS P).isSheaf {p}

/-- For an object `Y` of the site, the bijection between the sections of `X` over `Y` with
point-set image in `T` and the morphisms `Y ⟶ P` with point-set image `{p}`. -/
def completionEquiv (Y : BigFppfOver B S hS) :
    {x : X.obj (op Y) // Space.HasImageIn B S hS X s.T Y x} ≃
      {g : Y ⟶ P // Space.HasImageIn B S hS (yoneda.obj P) {p} Y g} where
  toFun x := ⟨((s.completionSubfunctorIso eW).hom.app (op Y) ⟨ULift.up x.1, x.2⟩).1.down,
    ((s.completionSubfunctorIso eW).hom.app (op Y) ⟨ULift.up x.1, x.2⟩).2⟩
  invFun g := ⟨((s.completionSubfunctorIso eW).inv.app (op Y) ⟨ULift.up g.1, g.2⟩).1.down,
    ((s.completionSubfunctorIso eW).inv.app (op Y) ⟨ULift.up g.1, g.2⟩).2⟩
  left_inv x := by
    have h := (s.completionSubfunctorIso eW).hom_inv_id_app_apply (op Y)
      (⟨ULift.up x.1, x.2⟩ : (Space.completionSubfunctor B S hS X s.T).toFunctor.obj (op Y))
    exact Subtype.ext (congrArg (fun z => z.1.down) h)
  right_inv g := by
    have h := (s.completionSubfunctorIso eW).inv_hom_id_app_apply (op Y)
      (⟨ULift.up g.1, g.2⟩ :
        (Space.completionSubfunctor B S hS (yoneda.obj P) {p}).toFunctor.obj (op Y))
    exact Subtype.ext (congrArg (fun z => z.1.down) h)

/-- Naturality of `completionEquiv`: restricting a section along `h : Y' ⟶ Y` precomposes the
corresponding morphism to `P` with `h`. -/
theorem completionEquiv_map {Y Y' : BigFppfOver B S hS} (h : Y' ⟶ Y)
    (x : {x : X.obj (op Y) // Space.HasImageIn B S hS X s.T Y x})
    (hx : Space.HasImageIn B S hS X s.T Y' (X.map h.op x.1)) :
    (s.completionEquiv eW Y' ⟨X.map h.op x.1, hx⟩).1 = h ≫ (s.completionEquiv eW Y x).1 := by
  have hn := NatTrans.naturality_apply (s.completionSubfunctorIso eW).hom h.op
    (⟨ULift.up x.1, x.2⟩ : (Space.completionSubfunctor B S hS X s.T).toFunctor.obj (op Y))
  exact congrArg (fun z => z.1.down) hn

/-- Naturality of the inverse of `completionEquiv`: precomposing a morphism to `P` with
`h : Y' ⟶ Y` restricts the corresponding section along `h`. -/
theorem completionEquiv_symm_map {Y Y' : BigFppfOver B S hS} (h : Y' ⟶ Y)
    (g : {g : Y ⟶ P // Space.HasImageIn B S hS (yoneda.obj P) {p} Y g})
    (hg : Space.HasImageIn B S hS (yoneda.obj P) {p} Y' (h ≫ g.1)) :
    ((s.completionEquiv eW Y').symm ⟨h ≫ g.1, hg⟩).1 =
      X.map h.op ((s.completionEquiv eW Y).symm g).1 := by
  have hn := NatTrans.naturality_apply (s.completionSubfunctorIso eW).inv h.op
    (⟨ULift.up g.1, g.2⟩ :
      (Space.completionSubfunctor B S hS (yoneda.obj P) {p}).toFunctor.obj (op Y))
  exact congrArg (fun z => z.1.down) hn

end Artin.ContractionSituation.Solution

end AlgebraicGeometry

end
