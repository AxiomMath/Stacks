module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAtGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleStalkLargeFiber

/-!
# The Zariski stalk of the chart restriction is the ordinary stalk

Let `X` be an algebraic space over a scheme `S`, let `F` be an `𝒪_X`-module and let `V` be a
small étale neighbourhood of a geometric point of `X` whose chart is a scheme `U` carrying the
point `u`.  Two objects compute the stalk of the restriction `F|_U` at `u`:
`AlgebraicGeometry.Space.chartZariskiModuleStalk`, the stalk at the point of the Zariski *site*
in which Stacks 05VP is stated, and `TopCat.Presheaf.stalk` of the underlying presheaf of
abelian groups, which is the module the ringed-space flatness predicate
`AlgebraicGeometry.IsFlatOverAt` of Stacks 08KT reads.  This file identifies them, with their
scalars, and deduces that condition (1) of Stacks 05VU at a point of a chart diagram is flatness
of the Zariski stalk over the local ring of the target chart.

## Main definitions

* `AlgebraicGeometry.Space.chartZariskiModuleStalkStalkEquiv`: the two stalks agree as modules
  over the local ring `𝒪_{U, u}` of the chart.
* `AlgebraicGeometry.Space.targetNeighborhood`: the small étale neighbourhood of the image
  geometric point given by the target chart of a commuting square and the image of the chosen
  lift.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_flat_chartZariskiModuleStalk`:
  **condition (1) of Stacks 05VU, read on the Zariski stalk.** The restriction of `F` to the
  source chart of a commuting square of étale scheme charts is flat over the target chart at
  the point under a chosen lift of a geometric point exactly when the Zariski stalk
  `(a^* F)_u` is flat over the local ring of the target chart at the image point.
* `AlgebraicGeometry.Space.chartPoint_targetNeighborhood`: the point of the target chart
  carried by `AlgebraicGeometry.Space.targetNeighborhood` is the image of the point of the
  source chart, on the nose.  So the ring of the predicate above is the local ring
  `𝒪_{V, v}` of a small étale neighbourhood of the image geometric point, with no transport.
* `AlgebraicGeometry.topIso_inv_comp_Γ_map_morphismRestrict`: restricting a morphism of schemes
  to an open of its target reads on global sections as the pullback of the sections over that
  open.  This is the sections-level comparison the commuting square of local rings of
  Stacks 05VU is checked on.

## Implementation notes

`AlgebraicGeometry.Space.chartZariskiModuleStalk` is `Stacks.moduleStalkLarge` with its scalars
restricted along `TopologicalSpace.Opens.pointFiberStalkIso`, so the identification is
`TopologicalSpace.Opens.moduleStalkLargeStalkIso` with one further restriction of scalars.  The
only computation is that the composite ring map is the identification of the two stalks of the
structure sheaf, after which the two actions on the stalk agree by
`AlgebraicGeometry.SemilinearStalk.comm_smul_eq`.

Both constructions exist only at module universe `m = u`, the universe of the structure rings:
`AlgebraicGeometry.Space.restrictToChart` lands in the modules of the chart there, and that is
where `AlgebraicGeometry.IsFlatOverAt` is stated.

The additive comparison is produced from bijectivity rather than from the two composition
identities of the isomorphism, and the semilinearity is a separate result, because the
underlying additive group of `Stacks.moduleStalkLarge` is a colimit whose cocone is opaque; every
statement is therefore read off the isomorphism in one step.

## References

* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Global sections of the restriction of a morphism to an open -/

/-- The inverse of the canonical isomorphism `Γ(X, W) ≅ Γ(W, ⊤)` is a restriction map. -/
private theorem topIso_inv_eq_map_presheaf {X : Scheme.{u}} (W : X.Opens) :
    (W.topIso.inv : Γ(X, W) ⟶ Γ(W.toScheme, ⊤)) =
      X.presheaf.map (homOfLE (le_of_eq W.ι_image_top)).op := rfl

/-- **Restricting a morphism of schemes to an open of its target reads on global sections as the
pullback of sections over that open.** The global functions on the open, pulled back along the
restricted morphism, are the pullback along the morphism itself of the functions on the open,
read as global functions on its preimage.

This is the sections-level input to the commuting square of local rings of Stacks 05VU: the
germ of a function on an open of the target chart is sent, going round the square either way,
to the germ of its pullback. -/
theorem topIso_inv_comp_Γ_map_morphismRestrict {A C : Scheme.{u}} (k : A ⟶ C) (W : C.Opens) :
    (W.topIso.inv ≫ Scheme.Γ.map (k ∣_ W).op : Γ(C, W) ⟶ Γ((k ⁻¹ᵁ W).toScheme, ⊤)) =
      k.app W ≫ (k ⁻¹ᵁ W).topIso.inv := by
  rw [topIso_inv_eq_map_presheaf W, topIso_inv_eq_map_presheaf (k ⁻¹ᵁ W), Scheme.Γ_map_op,
    Scheme.Hom.appTop, morphismRestrict_app' k W ⊤]
  refine Eq.trans (Scheme.Hom.map_appLE k _ (homOfLE (le_of_eq W.ι_image_top)).op) ?_
  refine Eq.trans ?_ (congrArg (fun φ => φ ≫ A.presheaf.map
    (homOfLE (le_of_eq (k ⁻¹ᵁ W).ι_image_top)).op) (Scheme.Hom.app_eq_appLE k)).symm
  exact (Scheme.Hom.appLE_map k le_rfl
    (homOfLE (le_of_eq (k ⁻¹ᵁ W).ι_image_top)).op).symm

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
  (F : Modules.{u, u} B S hS X hX)

/-! ### The two stalks of the chart restriction -/

/-- The structure sheaf of the scheme underlying an étale chart, as a sheaf of commutative rings
on its Zariski site. -/
noncomputable abbrev chartZariskiSheaf :
    Sheaf (Opens.grothendieckTopology (chartScheme V.chart)) CommRingCat.{u} :=
  (chartScheme V.chart).sheaf

/-- The restriction of an `𝒪_X`-module to an étale scheme chart, read as a presheaf of modules
over the composite of the structure sheaf with the forgetful functor to rings.  This is the
form in which the module carries the scalars of the `CommRingCat`-valued stalk. -/
noncomputable abbrev chartRestrictionPresheafOfModules :
    PresheafOfModules.{u}
      ((chartScheme V.chart).presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (restrictToChart B S hS hX F V.chart).val

/-- The comparison of the stalk of the chart restriction at the point of the Zariski site with
the ordinary stalk of its underlying presheaf of abelian groups. -/
noncomputable abbrev chartZariskiStalkIso :=
  Opens.moduleStalkLargeStalkIso (chartPoint B S hS X V) (chartZariskiSheaf B S hS V)
    (restrictToChart B S hS hX F V.chart)

/-- The action of the local ring of the chart on the ordinary stalk, read through the
comparison with the fibre of the structure sheaf at the point of the Zariski site, is the action
of Mathlib's `CommRingCat`-valued stalk. -/
theorem chartZariskiStalk_smul_aux (c : ↥(chartLocalRing B S hS X V))
    (m : ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (chartRestrictionPresheafOfModules B S hS hX V F).presheaf (chartPoint B S hS X V))) :
    (show ↥(TopCat.Presheaf.stalk (C := RingCat.{u})
        ((chartScheme V.chart).presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})
        (chartPoint B S hS X V)) from
      Opens.commRingFiberStalkHom (chartPoint B S hS X V) (chartZariskiSheaf B S hS V)
        ((chartZariskiFiberIso B S hS X V).inv c)) • m = c • m := by
  refine Eq.trans (congrArg (fun d => d • m)
    (Opens.commRingFiberStalkHom_pointFiberStalkIso_inv (chartPoint B S hS X V)
      (chartZariskiSheaf B S hS V) c)) ?_
  refine Eq.trans (SemilinearStalk.comm_smul_eq (chartScheme V.chart).presheaf
    (chartPoint B S hS X V) _ _ m).symm ?_
  exact congrArg (fun d => d • m)
    (ConcreteCategory.congr_hom
      (SemilinearStalk.commStalkIso (chartScheme V.chart).presheaf
        (chartPoint B S hS X V)).inv_hom_id c)

/-- The stalk of the chart restriction at the point of the Zariski site and the ordinary stalk
of its underlying presheaf of abelian groups have the same underlying additive group. -/
noncomputable def chartZariskiStalkAddEquiv :
    ↥(chartZariskiModuleStalk B S hS X hX V F) ≃+
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (chartRestrictionPresheafOfModules B S hS hX V F).presheaf
        (chartPoint B S hS X V)) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun z => (chartZariskiStalkIso B S hS hX V F).hom z)
      (fun z z' => map_add
        (ConcreteCategory.hom (chartZariskiStalkIso B S hS hX V F).hom) z z'))
    (ConcreteCategory.bijective_of_isIso (chartZariskiStalkIso B S hS hX V F).hom)

/-- The additive comparison of the two stalks is linear over the local ring of the chart. -/
theorem chartZariskiStalkAddEquiv_smul (c : ↥(chartLocalRing B S hS X V))
    (z : ↥(chartZariskiModuleStalk B S hS X hX V F)) :
    chartZariskiStalkAddEquiv B S hS hX V F (c • z) =
      c • chartZariskiStalkAddEquiv B S hS hX V F z :=
  (map_smul (ConcreteCategory.hom (chartZariskiStalkIso B S hS hX V F).hom)
      (show ↥(((chartZariskiPoint B S hS X V).presheafFiber (A := CommRingCat.{u})).obj
        (chartZariskiSheaf B S hS V).obj) from (chartZariskiFiberIso B S hS X V).inv c)
      (show ↥(Stacks.moduleStalkLarge.{u} (chartZariskiPoint B S hS X V)
        (chartZariskiSheaf B S hS V) (restrictToChart B S hS hX F V.chart)) from z)).trans
    (chartZariskiStalk_smul_aux B S hS hX V F c _)

/-- **The Zariski stalk of the chart restriction is the ordinary stalk**, as modules over the
local ring `𝒪_{U, u}` of the chart: the stalk at the point of the Zariski site in which
Stacks 05VP is stated is the stalk of the underlying presheaf of abelian groups which the
ringed-space predicate of Stacks 08KT reads. -/
noncomputable def chartZariskiModuleStalkStalkEquiv :
    ↥(chartZariskiModuleStalk B S hS X hX V F) ≃ₗ[↥(chartLocalRing B S hS X V)]
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (chartRestrictionPresheafOfModules B S hS hX V F).presheaf
        (chartPoint B S hS X V)) where
  toFun := chartZariskiStalkAddEquiv B S hS hX V F
  map_add' := map_add (chartZariskiStalkAddEquiv B S hS hX V F)
  map_smul' := chartZariskiStalkAddEquiv_smul B S hS hX V F
  invFun := (chartZariskiStalkAddEquiv B S hS hX V F).symm
  left_inv := (chartZariskiStalkAddEquiv B S hS hX V F).left_inv
  right_inv := (chartZariskiStalkAddEquiv B S hS hX V F).right_inv

/-! ### Condition (1) of Stacks 05VU on the Zariski stalk -/

section Diagram

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- **Condition (1) of Stacks 05VU at a lift of a geometric point, read on the Zariski
stalk.** In a commuting square of étale scheme charts over `f`, the restriction of `F` to the
source chart is flat over the target chart at the point under a chosen lift of a geometric
point exactly when the Zariski stalk of the restriction is flat over the local ring of the
target chart at the image of that point. -/
theorem isFlatOverAtOnChartDiagram_iff_flat_chartZariskiModuleStalk
    (N : SmallEtaleNeighborhood x) (W : SmallEtale B S hS Y)
    (g : (SmallEtale.toOver B S hS X).obj N.chart ⟶ (SmallEtale.toOver B S hS Y).obj W)
    (hcomm : N.chart.obj.hom ≫ f = yoneda.map g ≫ W.obj.hom) :
    IsFlatOverAtOnChartDiagram B S hS hX F
        { U := N.chart, V := W, g := g, comm := hcomm } (chartPoint B S hS X N) ↔
      letI : Module ↥((chartScheme W).presheaf.stalk
          (((BigFppfOver.toScheme B S hS).map g).base (chartPoint B S hS X N)))
          ↥(chartZariskiModuleStalk B S hS X hX N F) :=
        Module.compHom _ (((BigFppfOver.toScheme B S hS).map g).stalkMap
          (chartPoint B S hS X N)).hom
      Module.Flat ↥((chartScheme W).presheaf.stalk
          (((BigFppfOver.toScheme B S hS).map g).base (chartPoint B S hS X N)))
        ↥(chartZariskiModuleStalk B S hS X hX N F) := by
  let : Module ↥((chartScheme W).presheaf.stalk
      (((BigFppfOver.toScheme B S hS).map g).base (chartPoint B S hS X N)))
      ↥(chartZariskiModuleStalk B S hS X hX N F) :=
    Module.compHom _ (((BigFppfOver.toScheme B S hS).map g).stalkMap
      (chartPoint B S hS X N)).hom
  let : Module ↥((chartScheme W).presheaf.stalk
      (((BigFppfOver.toScheme B S hS).map g).base (chartPoint B S hS X N)))
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (chartRestrictionPresheafOfModules B S hS hX N F).presheaf
        (chartPoint B S hS X N)) :=
    Module.compHom _ (((BigFppfOver.toScheme B S hS).map g).stalkMap
      (chartPoint B S hS X N)).hom
  let Ψ : ↥(chartZariskiModuleStalk B S hS X hX N F) ≃ₗ[↥((chartScheme W).presheaf.stalk
      (((BigFppfOver.toScheme B S hS).map g).base (chartPoint B S hS X N)))]
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (chartRestrictionPresheafOfModules B S hS hX N F).presheaf (chartPoint B S hS X N)) :=
    { toFun := chartZariskiModuleStalkStalkEquiv B S hS hX N F
      map_add' := map_add (chartZariskiModuleStalkStalkEquiv B S hS hX N F)
      map_smul' := fun c z =>
        (chartZariskiModuleStalkStalkEquiv B S hS hX N F).map_smul _ z
      invFun := (chartZariskiModuleStalkStalkEquiv B S hS hX N F).symm
      left_inv := (chartZariskiModuleStalkStalkEquiv B S hS hX N F).left_inv
      right_inv := (chartZariskiModuleStalkStalkEquiv B S hS hX N F).right_inv }
  exact (Module.Flat.equiv_iff Ψ).symm

/-- **The target chart of a commuting square as a small étale neighbourhood of the image
geometric point.**  The chosen lift of the geometric point into the source chart, composed with
the vertical morphism of the square, lifts the image geometric point to the target chart. -/
noncomputable def targetNeighborhood (N : SmallEtaleNeighborhood x) (W : SmallEtale B S hS Y)
    (g : (SmallEtale.toOver B S hS X).obj N.chart ⟶ (SmallEtale.toOver B S hS Y).obj W)
    (hcomm : N.chart.obj.hom ≫ f = yoneda.map g ≫ W.obj.hom) :
    SmallEtaleNeighborhood (geometricPointMap f x) where
  chart := W
  point := N.point ≫ g
  point_comp := by
    change W.obj.hom.app _ (N.point ≫ g) = f.app _ x.val.value
    have hc := congrArg
      (fun k : yoneda.obj N.chart.obj.left ⟶ Y => k.app _ N.point) hcomm
    change f.app _ (N.chart.obj.hom.app _ N.point) = W.obj.hom.app _ (N.point ≫ g) at hc
    exact hc.symm.trans (congrArg (f.app _) N.point_comp)

/-- The point of the target chart carried by `AlgebraicGeometry.Space.targetNeighborhood` is the
image of the point of the source chart under the vertical morphism of the square.  It holds on
the nose, so the local ring in
`AlgebraicGeometry.Space.isFlatOverAtOnChartDiagram_iff_flat_chartZariskiModuleStalk` is the
local ring of a small étale neighbourhood of the image geometric point with no transport. -/
theorem chartPoint_targetNeighborhood (N : SmallEtaleNeighborhood x)
    (W : SmallEtale B S hS Y)
    (g : (SmallEtale.toOver B S hS X).obj N.chart ⟶ (SmallEtale.toOver B S hS Y).obj W)
    (hcomm : N.chart.obj.hom ≫ f = yoneda.map g ≫ W.obj.hom) :
    chartPoint B S hS Y (targetNeighborhood B S hS N W g hcomm) =
      ((BigFppfOver.toScheme B S hS).map g).base (chartPoint B S hS X N) :=
  rfl

end Diagram

end AlgebraicGeometry.Space

end
