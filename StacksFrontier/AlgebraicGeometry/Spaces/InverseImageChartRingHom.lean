module

public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageStructureSheafChartUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# The unit of `f⁻¹ ⊣ f_*` on charts as a ring homomorphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `d` be a commutative
diagram of étale scheme charts over `f`, with chart `V` of `X`, chart `W` of `Y` and vertical
morphism `g`.  This file packages the value on `d` of the unit `𝒪_Y ⟶ f_*f⁻¹𝒪_Y`
(`AlgebraicGeometry.Space.inverseImageUnitFMap`) as a ring homomorphism

`𝒪_Y(W) ⟶ (f⁻¹𝒪_Y)(V)`,

and proves that, followed by the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`, it is pullback of regular
functions along `g`.

Both statements are read off germs at the geometric points of `X`: sections of a sheaf on the
small étale site with the same germ at every geometric point agree, because the geometric
points detect coverings (Stacks 04K5).

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramImageFiber`: the lift of the image of a geometric point
  into the lower chart of a diagram, obtained from a lift into its upper chart.
* `AlgebraicGeometry.Space.inverseImageChartUnitRingHom`: the unit on charts, as a ring
  homomorphism.

## Main results

* `AlgebraicGeometry.Space.mem_topology_of_forall_geometricFiber`: a sieve of an étale chart
  through whose arrows every lift of every geometric point factors is a covering sieve.
* `AlgebraicGeometry.Space.eq_of_forall_toPresheafFiber_eq`: sections of a sheaf of commutative
  rings with the same germs at all geometric points agree.
* `AlgebraicGeometry.Space.toPresheafFiber_inverseImageChartUnit`: the germ formula.
* `AlgebraicGeometry.Space.structureSharpInverseImage_inverseImageChartUnit`: the structure
  map after the unit on charts is pullback of regular functions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Local

variable (Z : AlgebraicSpaces B S hS)

/-- **Geometric points detect coverings.**  A sieve of an étale chart `U` of an algebraic space
through one of whose arrows every lift to `U` of every geometric point factors is a covering
sieve of the small étale site. -/
theorem mem_topology_of_forall_geometricFiber (U : SmallEtale B S hS Z.1) (R : Sieve U)
    (hR : ∀ (x : GeometricPoint B S hS Z.1) (p : (etaleSitePoint B S hS Z.1 x Z.2).fiber.obj U),
      ∃ (V : SmallEtale B S hS Z.1) (g : V ⟶ U), R g ∧
        ∃ q : (etaleSitePoint B S hS Z.1 x Z.2).fiber.obj V,
          (etaleSitePoint B S hS Z.1 x Z.2).fiber.map g q = p) :
    R ∈ SmallEtale.topology B S hS Z.1 U := by
  refine smallEtale_sieve_of_pointwise_covering B S hS Z.1 U R fun z => ?_
  obtain ⟨x, p, z', hz⟩ := exists_geo_lift_at_chart_point B S hS Z.1 U z
  obtain ⟨V, g, hg, q, hq⟩ := hR x p
  refine ⟨V, g, hg, (BigFppfOver.toScheme B S hS).map q.1 z', ?_⟩
  have hq' : q.1 ≫ (SmallEtale.toOver B S hS Z.1).map g = p.1 := congrArg Subtype.val hq
  rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp, hq']

/-- **Sections are determined by their geometric germs.**  Two sections over an étale chart of a
sheaf of commutative rings on the small étale site of an algebraic space with the same germ at
every lift of every geometric point are equal. -/
theorem eq_of_forall_toPresheafFiber_eq (G : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u})
    (U : SmallEtale B S hS Z.1) (s t : ToType (G.obj.obj (op U)))
    (h : ∀ (x : GeometricPoint B S hS Z.1) (p : (etaleSitePoint B S hS Z.1 x Z.2).fiber.obj U),
      (etaleSitePoint B S hS Z.1 x Z.2).toPresheafFiber U p G.obj s =
        (etaleSitePoint B S hS Z.1 x Z.2).toPresheafFiber U p G.obj t) :
    s = t := by
  let P := G.obj ⋙ forget CommRingCat
  let R : Sieve U := Presheaf.equalizerSieve (F := P) s t
  have hR : R ∈ SmallEtale.topology B S hS Z.1 U := by
    refine mem_topology_of_forall_geometricFiber B S hS Z U R fun x p => ?_
    obtain ⟨V, g, q, hq, hgq⟩ :=
      ((etaleSitePoint B S hS Z.1 x Z.2).toPresheafFiber_eq_iff' U p s t).mp (h x p)
    exact ⟨V, g, hgq, q, hq⟩
  have hsheaf : Presieve.IsSheaf (SmallEtale.topology B S hS Z.1) P :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose (SmallEtale.topology B S hS Z.1) (forget CommRingCat)).obj G).property
  exact (hsheaf.isSeparated R hR).ext (fun _ _ hg => hg)

end Local

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The lift into the lower chart of a diagram of étale scheme charts over `f` of the image of a
geometric point, obtained from a lift into the upper chart. -/
def chartDiagramImageFiber (d : ChartDiagram B S hS X.1 Y.1 f.hom) {x : GeometricPoint B S hS X.1}
    (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj d.U) :
    (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).fiber.obj d.V :=
  ⟨p.1 ≫ d.g, by
    have h := congrArg (fun φ => φ.app (op x.val.siteObject) p.1) d.comm
    change f.hom.app _ (d.U.obj.hom.app _ p.1) = d.V.obj.hom.app _ (p.1 ≫ d.g) at h
    exact h.symm.trans (congrArg (f.hom.app _) p.2)⟩

/-- The unit on charts as a function between the rings of sections. -/
abbrev inverseImageChartUnitFun (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) →
      ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op d.U)) :=
  fun s => (inverseImageUnitFMap B S hS f).app d s

/-- The germ formula, for the unit on charts read as a function between rings of sections. -/
theorem toPresheafFiber_inverseImageChartUnitFun (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : GeometricPoint B S hS X.1) (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj d.U)
    (s : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) :
    (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber d.U p
        (inverseImageStructureSheaf B S hS f).obj (inverseImageChartUnitFun B S hS f d s) =
      ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber d.V
          (chartDiagramImageFiber B S hS f d p) (smallEtaleRingedTopos B S hS Y).O.obj ≫
        inverseImageFiberComparison B S hS f x) s :=
  (inverseImageUnitFMap_toPresheafFiber B S hS f x d p
    (chartDiagramImageFiber B S hS f d p) rfl s).symm

/-- **The unit of `f⁻¹ ⊣ f_*` on charts, as a ring homomorphism** `𝒪_Y(W) ⟶ (f⁻¹𝒪_Y)(V)`. -/
def inverseImageChartUnitRingHom (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) →+*
      ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op d.U)) :=
    { toFun := inverseImageChartUnitFun B S hS f d
      map_one' := by
        refine eq_of_forall_toPresheafFiber_eq B S hS X _ d.U _ _ fun x p => ?_
        rw [toPresheafFiber_inverseImageChartUnitFun, map_one, map_one]
        rfl
      map_mul' := fun a b => by
        refine eq_of_forall_toPresheafFiber_eq B S hS X _ d.U _ _ fun x p => ?_
        rw [toPresheafFiber_inverseImageChartUnitFun, map_mul, map_mul,
          toPresheafFiber_inverseImageChartUnitFun, toPresheafFiber_inverseImageChartUnitFun]
        rfl
      map_zero' := by
        refine eq_of_forall_toPresheafFiber_eq B S hS X _ d.U _ _ fun x p => ?_
        rw [toPresheafFiber_inverseImageChartUnitFun, map_zero, map_zero]
        rfl
      map_add' := fun a b => by
        refine eq_of_forall_toPresheafFiber_eq B S hS X _ d.U _ _ fun x p => ?_
        rw [toPresheafFiber_inverseImageChartUnitFun, map_add, map_add,
          toPresheafFiber_inverseImageChartUnitFun, toPresheafFiber_inverseImageChartUnitFun]
        rfl }

/-- **The germ formula for the unit on charts.** -/
theorem toPresheafFiber_inverseImageChartUnit (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : GeometricPoint B S hS X.1) (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj d.U)
    (s : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) :
    (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber d.U p
        (inverseImageStructureSheaf B S hS f).obj (inverseImageChartUnitRingHom B S hS f d s) =
      ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).toPresheafFiber d.V
          (chartDiagramImageFiber B S hS f d p) (smallEtaleRingedTopos B S hS Y).O.obj ≫
        inverseImageFiberComparison B S hS f x) s :=
  toPresheafFiber_inverseImageChartUnitFun B S hS f d x p s

/-- **The structure map after the unit on charts is pullback of regular functions.** -/
theorem structureSharpInverseImage_inverseImageChartUnit (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) :
    (structureSharpInverseImage B S hS f).hom.app (op d.U)
        (inverseImageChartUnitRingHom B S hS f d s) =
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s := by
  refine eq_of_forall_toPresheafFiber_eq B S hS X _ d.U _ _ fun x p => ?_
  refine (Point.toPresheafFiber_naturality_apply (etaleSitePoint B S hS X.1 x X.2)
    (structureSharpInverseImage B S hS f).hom d.U p
    (inverseImageChartUnitRingHom B S hS f d s)).symm.trans ?_
  rw [toPresheafFiber_inverseImageChartUnit]
  exact stalkStructureMap_toPresheafFiber B S hS f x d p
    (chartDiagramImageFiber B S hS f d p) rfl s

end AlgebraicGeometry.Space

end
