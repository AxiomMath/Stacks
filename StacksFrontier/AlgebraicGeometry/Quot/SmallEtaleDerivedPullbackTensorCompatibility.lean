module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomTensorPairing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTransportAgreement

/-!
# The derived pullback of algebraic spaces is compatible with `⊗^L`, as a pullback datum

The derived pullbacks of `𝒪`-modules on the small étale ringed topoi of algebraic spaces form
the pullback pseudofunctor datum `AlgebraicGeometry.Space.toposDerivedPullbackData`, whose
composition comparison is the inverse of the comparison of Stacks 0D6D
(`Space.toposDerivedPullbackData_compIso_eq_smallEtaleDerivedModulePullbackCompIso_symm`).
The isomorphisms `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L` of Stacks 07A4 are natural and compatible with
that comparison (`AlgebraicGeometry.Space.smallEtaleDerivedPullbackTensorIso_comp`), so they make
the datum compatible with the derived tensor products in the sense of
`CategoryTheory.PullbackData.TensorCompatibility`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedTensorCompatibility`: the compatibility of
  `AlgebraicGeometry.Space.toposDerivedPullbackData` with the derived tensor products.

## Main results

* `CategoryTheory.PullbackData.tensorComp_of_whiskerLeft_comp_hom`: a composition law of tensor
  comparisons, stated with a compositor `C : Lg ⋙ Lf ≅ L(f ≫ g)`, gives the composition law of
  `CategoryTheory.PullbackData.TensorCompatibility` for `C⁻¹`.
* `CategoryTheory.PullbackData.tensorComparison_naturality_left`: a tensor comparison is natural
  in its first factor.
* `AlgebraicGeometry.Space.smallEtaleDerivedTensorCompatibility_μ`: the tensor comparison of
  `AlgebraicGeometry.Space.smallEtaleDerivedTensorCompatibility` is the isomorphism of
  Stacks 07A4.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace CategoryTheory.PullbackData

/-- **A composition law of tensor comparisons, read through the inverse compositor.** Let
`C : Lg ⋙ Lf ≅ Lc` and let `αg`, `αf`, `αc` compare the three functors with tensor products. If
`C` carries `αc` to `Lf αg` followed by `αf` and `C ⊗ C`, then for `c = C⁻¹` the comparison `αc`
followed by `c ⊗ c` is `c` followed by `Lf αg` and `αf`: the shape of
`CategoryTheory.PullbackData.TensorCompatibility.μ_comp`. -/
theorem tensorComp_of_whiskerLeft_comp_hom {CZ CY CX : Type*} [Category CZ] [Category CY]
    [Category CX] (TZ : CZ ⥤ CZ ⥤ CZ) (TY : CY ⥤ CY ⥤ CY) (TX : CX ⥤ CX ⥤ CX)
    {Lg : CZ ⥤ CY} {Lf : CY ⥤ CX} {Lc : CZ ⥤ CX} (C : Lg ⋙ Lf ≅ Lc) (c : Lc ≅ Lg ⋙ Lf)
    (hc : c = C.symm)
    (αg : Functor.uncurry.obj TZ ⋙ Lg ≅ Lg.prod Lg ⋙ Functor.uncurry.obj TY)
    (αf : Functor.uncurry.obj TY ⋙ Lf ≅ Lf.prod Lf ⋙ Functor.uncurry.obj TX)
    (αc : Functor.uncurry.obj TZ ⋙ Lc ≅ Lc.prod Lc ⋙ Functor.uncurry.obj TX)
    (h : Functor.whiskerLeft (Functor.uncurry.obj TZ) C.hom ≫ αc.hom =
      Functor.whiskerRight αg.hom Lf ≫ Functor.whiskerLeft (Lg.prod Lg) αf.hom ≫
        Functor.whiskerRight (NatTrans.prod C.hom C.hom) (Functor.uncurry.obj TX))
    (M N : CZ) :
    αc.hom.app (M, N) ≫ (TX.map (c.hom.app M)).app (Lc.obj N) ≫
        (TX.obj ((Lg ⋙ Lf).obj M)).map (c.hom.app N) =
      c.hom.app ((TZ.obj M).obj N) ≫ Lf.map (αg.hom.app (M, N)) ≫
        αf.hom.app (Lg.obj M, Lg.obj N) := by
  subst hc
  let p : ((Lg ⋙ Lf).obj M, (Lg ⋙ Lf).obj N) ⟶ (Lc.obj M, Lc.obj N) := (C.hom.app M, C.hom.app N)
  let q : (Lc.obj M, Lc.obj N) ⟶ ((Lg ⋙ Lf).obj M, (Lg ⋙ Lf).obj N) := (C.inv.app M, C.inv.app N)
  have e : C.hom.app ((TZ.obj M).obj N) ≫ αc.hom.app (M, N) =
      Lf.map (αg.hom.app (M, N)) ≫ αf.hom.app (Lg.obj M, Lg.obj N) ≫
        (Functor.uncurry.obj TX).map p :=
    NatTrans.congr_app h (M, N)
  have hpq : (Functor.uncurry.obj TX).map p ≫ (Functor.uncurry.obj TX).map q = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact (congrArg (Functor.uncurry.obj TX).map
      (Prod.ext (C.hom_inv_id_app M) (C.hom_inv_id_app N))).trans (Functor.map_id _ _)
  change αc.hom.app (M, N) ≫ (Functor.uncurry.obj TX).map q =
    C.inv.app ((TZ.obj M).obj N) ≫ Lf.map (αg.hom.app (M, N)) ≫ αf.hom.app (Lg.obj M, Lg.obj N)
  rw [← cancel_epi (C.hom.app ((TZ.obj M).obj N)), Iso.hom_inv_id_app_assoc, reassoc_of% e,
    hpq]
  exact congrArg (fun t => Lf.map (αg.hom.app (M, N)) ≫ t) (Category.comp_id _)

/-- **A tensor comparison is natural in its first factor.** -/
theorem tensorComparison_naturality_left {C D : Type*} [Category C] [Category D]
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) {F : C ⥤ D}
    (μ : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD) {M M' : C} (u : M ⟶ M')
    (N : C) :
    F.map ((TC.map u).app N) ≫ μ.hom.app (M', N) =
      μ.hom.app (M, N) ≫ (TD.map (F.map u)).app (F.obj N) := by
  simpa only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map, Functor.prod_obj,
    CategoryTheory.Functor.map_id, Category.comp_id] using
    μ.hom.naturality ((u, 𝟙 N) : (M, N) ⟶ (M', N))

end CategoryTheory.PullbackData

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The derived pullbacks of algebraic spaces are compatible with the derived tensor
products**: the isomorphisms `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L` of Stacks 07A4, natural in `K`
and compatible with the composition comparison of
`AlgebraicGeometry.Space.toposDerivedPullbackData`, which is the inverse of the comparison of
Stacks 0D6D. -/
def smallEtaleDerivedTensorCompatibility :
    PullbackData.TensorCompatibility (toposDerivedPullbackData B S hS)
      (fun X => smallEtaleDerivedTensor B S hS X) where
  μ := fun f M N => (smallEtaleDerivedPullbackTensorIso f).app (M, N)
  μ_naturality := fun {_ _} f {_ _} u N =>
    PullbackData.tensorComparison_naturality_left _ _ (smallEtaleDerivedPullbackTensorIso f) u N
  μ_comp := fun f g M N =>
    PullbackData.tensorComp_of_whiskerLeft_comp_hom _ _ _
      (smallEtaleDerivedModulePullbackCompIso B S hS f g)
      ((toposDerivedPullbackData B S hS).compIso f g)
      (toposDerivedPullbackData_compIso_eq_smallEtaleDerivedModulePullbackCompIso_symm B S hS f g)
      (smallEtaleDerivedPullbackTensorIso g) (smallEtaleDerivedPullbackTensorIso f)
      (smallEtaleDerivedPullbackTensorIso (f ≫ g))
      (smallEtaleDerivedPullbackTensorIso_comp f g) M N

/-- The tensor comparison of `AlgebraicGeometry.Space.smallEtaleDerivedTensorCompatibility` is the
isomorphism of Stacks 07A4. -/
theorem smallEtaleDerivedTensorCompatibility_μ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M N : toposDerived B S hS Y) :
    (smallEtaleDerivedTensorCompatibility B S hS).μ f M N =
      (smallEtaleDerivedPullbackTensorIso f).app (M, N) :=
  rfl

end AlgebraicGeometry.Space

end
