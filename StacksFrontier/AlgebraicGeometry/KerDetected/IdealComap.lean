module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.KerDetected.RingColimit

/-!
# The ideal of a kernel on an affine open

The kernel of a quasi-compact morphism of schemes, read on an affine open `U` of the
target, is the kernel of the restriction of that morphism to `f⁻¹ U ⟶ U` on global
sections. This is the companion of `Stacks.IdealSheaf.ideal_comap_appLE`, which computes
the ideal of `I.comap f` on a pair of affine opens `V ≤ f⁻¹ U` for an arbitrary morphism,
where Mathlib computes it only for an open immersion
(`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion`).

## Main results

* `AlgebraicGeometry.GoodDiagramKer.ker_resLE_appTop`: for a quasi-compact `f` and an
  affine open `U` of the target, the ideal of `f.ker` at `U`, transported to the global
  sections of `U` as a scheme, is the kernel of the restricted morphism `f.resLE U (f⁻¹ U)`
  on global sections.
* `AlgebraicGeometry.GoodDiagramKer.ker_morphismRestrict_appTop` and
  `AlgebraicGeometry.GoodDiagramKer.ideal_ker_eq_comap_ker_morphismRestrict_appTop`: the same
  statement in the `AlgebraicGeometry.morphismRestrict` spelling, in the two orientations —
  the ideal of `f.ker` at `U` pushed forward to `Γ(U, ⊤)`, and `f.ker.ideal U` itself read
  back from the kernel of `(f ∣_ U).appTop`.

## Route

Restricting to `U` turns both sides into statements about global sections:
`AlgebraicGeometry.Scheme.Hom.resLE_app_top` factors the restricted map through `f.app U`
and the two `topIso` identifications, a kernel is unchanged by precomposing or postcomposing
with an isomorphism, and `AlgebraicGeometry.Scheme.Hom.ker_apply` computes the ideal of
`f.ker` at `U` as the kernel of `f.app U`.

## References

* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GoodDiagramKer

/-- For a quasi-compact morphism and an affine open `U` of the target, the ideal of the
kernel at `U`, transported along the identification of `Γ(U, ⊤)` with the sections of `U` as
a scheme, is the kernel of the restricted morphism on global sections. -/
theorem ker_resLE_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) (V : X.Opens) (hV : V = f ⁻¹ᵁ (U : Y.Opens)) :
    Ideal.map (U : Y.Opens).topIso.inv.hom (f.ker.ideal U) =
      RingHom.ker (f.resLE U V hV.le).appTop.hom := by
  subst V
  let e := (U : Y.Opens).topIso.symm.commRingCatIsoToRingEquiv
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.hom_comp, CommRingCat.hom_comp,
    RingHom.comp_assoc,
    RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ (U : Y.Opens)).topIso.inv).1]
  rw [← Scheme.Hom.app_eq_appLE]
  change Ideal.map e.toRingHom (f.ker.ideal U) =
    (RingHom.ker (f.app U).hom).comap e.symm.toRingHom
  rw [f.ker_apply U]
  exact Ideal.map_comap_of_equiv e

/-- **The kernel ideal sheaf on an affine open, read off the restricted morphism.** The
`AlgebraicGeometry.morphismRestrict` spelling of
`AlgebraicGeometry.GoodDiagramKer.ker_resLE_appTop`: for a quasi-compact `f` and an affine open
`U` of the target, the ideal of `f.ker` at `U`, transported along the identification of
`Γ(Y, U)` with `Γ(U, ⊤)`, is the kernel of `(f ∣_ U).appTop`.

`AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict` identifies `f.resLE U (f⁻¹ U)` with
`f ∣_ U`, so nothing beyond that rewriting is needed. -/
theorem ker_morphismRestrict_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (U : Y.affineOpens) :
    Ideal.map (U : Y.Opens).topIso.inv.hom (f.ker.ideal U) =
      RingHom.ker (f ∣_ (U : Y.Opens)).appTop.hom := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact ker_resLE_appTop f U _ rfl

/-- **The ideal of the kernel on an affine open is the kernel of the restricted morphism pulled
back along `AlgebraicGeometry.Scheme.Opens.topIso`.** This is
`AlgebraicGeometry.GoodDiagramKer.ker_morphismRestrict_appTop` in the orientation that computes
`f.ker.ideal U` itself rather than its image; the two are interchangeable because
`AlgebraicGeometry.Scheme.Opens.topIso` is an isomorphism of rings, so `Ideal.map` along its
inverse is inverted by `Ideal.comap` along the same map. -/
theorem ideal_ker_eq_comap_ker_morphismRestrict_appTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) :
    f.ker.ideal U =
      (RingHom.ker (f ∣_ (U : Y.Opens)).appTop.hom).comap (U : Y.Opens).topIso.inv.hom := by
  rw [← ker_morphismRestrict_appTop f U,
    Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (U : Y.Opens).topIso.inv)]

end AlgebraicGeometry.GoodDiagramKer

end
