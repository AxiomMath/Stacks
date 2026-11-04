module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkInvertible
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The geometric stalk of a free module is a free module

Let `X` be an algebraic space over a scheme `S` of a big fppf site, let `F` be an `𝒪_X`-module
which is free on the small étale site of `X` — a coproduct of copies of `𝒪_X` indexed by an
arbitrary type, in the sense of `AlgebraicGeometry.Space.IsFreeModule` — and let `x̄` be a
geometric point of `X`.  Then the stalk `F_{x̄}` of Stacks 05VQ is a free module over the étale
local ring `𝒪_{X, x̄}`.

This is the fact the base-change clause of Tag 0CZT consumes at the point upstairs, where
membership in the étale free locus has to be turned into a condition on the geometric stalk.
Nothing here is a clause of a tag.

## Main results

* `AlgebraicGeometry.Space.preservesColimitsOfSize_smallEtaleModuleStalk`: the stalk at a point
  of the small étale site of an algebraic space preserves colimits of shapes in the universe of
  the module sections.
* `AlgebraicGeometry.Space.free_moduleStalk_of_isFreeModule`: the stalk before the extension of
  scalars is free over the stalk of the structure sheaf.
* `AlgebraicGeometry.Space.free_geometricModuleStalk_of_isFreeModule`: **the geometric stalk of
  a free module is free over the étale local ring**, at an arbitrary index type.

## Implementation notes

Freeness is read through the universal property of the coproduct, so the index type is
arbitrary in the universe `u` of the structure rings and no coproduct-existence instance is
available.  The colimiting cofan is therefore carried through the stalk functor
`Stacks.sheafModuleFiberOfCommRing` and compared with the concrete direct sum of
`ModuleCat.coproductCoconeIsColimit`; the stalk of the single copy `𝒪_X` is the stalk ring by
`Stacks.unitModuleStalkIso`.

Colimit preservation for that functor is available for shapes in `Type 0`
(`Stacks.preservesColimits_sheafModuleFiber`) and, at the size needed here, for a *represented*
algebraic space (`AlgebraicGeometry.Space.preservesColimitsOfSize_representedStalk`).  Neither
covers an arbitrary algebraic space at an index type in `Type u`, so the same four steps —
colimits of the forgetful functor to abelian sheaves shrunk from `Category.{u + 1}` shapes, the
stalk of an abelian sheaf being a left adjoint, the underlying-group identity
`Stacks.sheafModuleFiberCompForget₂`, and reflection along `forget₂` — are run again here at
that size, and both existing forms are specialisations of the result.

The passage to the étale local ring is the extension of scalars along the ring *isomorphism*
`AlgebraicGeometry.Space.pointStalkRingEquiv`, so it changes neither the underlying additive
group nor freeness: `AlgebraicGeometry.Space.geometricModuleStalkAddEquiv` is that additive
isomorphism, `AlgebraicGeometry.Space.geometricModuleStalkAddEquiv_smul` its semilinearity, and
`Module.Free.of_equiv` crosses a semilinear equivalence.

## References

* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The stalk at a point of the small étale site of an algebraic space preserves colimits**
of shapes in the universe of the module sections.  On underlying abelian groups it is the stalk
of the underlying abelian sheaf, which is a left adjoint of the skyscraper sheaf functor. -/
instance preservesColimitsOfSize_smallEtaleModuleStalk (V : AlgebraicSpaces B S hS)
    (vbar : GeometricPoint B S hS V.1) :
    PreservesColimitsOfSize.{u, u} (Stacks.sheafModuleFiberOfCommRing.{u, u, u + 1}
      (etaleSitePoint B S hS V.1 vbar V.2) (smallEtaleRingedTopos B S hS V).O) := by
  let Φ := etaleSitePoint B S hS V.1 vbar V.2
  let R : Sheaf (SmallEtale.topology B S hS V.1) RingCat.{u} :=
    Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O
  have h0 : PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) :=
    have hsize : PreservesColimitsOfSize.{u + 1, u} (SheafOfModules.toSheaf.{u} R) :=
      inferInstance
    preservesColimitsOfSize_shrink.{u, u, u, u + 1} _
  have hcomp : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.toSheaf.{u} R ⋙ Φ.sheafFiber (A := AddCommGrpCat.{u})) := inferInstance
  have hforget : PreservesColimitsOfSize.{u, u} (Stacks.sheafModuleFiber Φ R ⋙
      forget₂ (ModuleCat.{u} ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj))
        AddCommGrpCat.{u}) :=
    preservesColimits_of_natIso (Stacks.sheafModuleFiberCompForget₂ Φ R).symm
  have hreflects : ReflectsColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u} ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj))
        AddCommGrpCat.{u}) := reflectsColimits_of_reflectsIsomorphisms
  have hfib : PreservesColimitsOfSize.{u, u} (Stacks.sheafModuleFiber Φ R) :=
    preservesColimits_of_reflects_of_preserves _
      (forget₂ (ModuleCat.{u} ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj))
        AddCommGrpCat.{u})
  have hres : PreservesColimitsOfSize.{u, u} (ModuleCat.restrictScalars.{u}
      (Stacks.commRingSheafFiberIso Φ (smallEtaleRingedTopos B S hS V).O).inv.hom) :=
    (ModuleCat.restrictCoextendScalarsAdj _).leftAdjoint_preservesColimits
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ hfib hres

/-- The stalk of a coproduct of copies of `𝒪_X` indexed by `I` is `R^{(I)}`, `R` the stalk ring. -/
private theorem nonempty_linearEquiv_finsupp_moduleStalk (V : AlgebraicSpaces B S hS)
    (vbar : GeometricPoint B S hS V.1) (M : Modules.{u, u} B S hS V.1 V.2) (I : Type u)
    (ι : I → (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O) ⟶ M))
    (hc : IsColimit (Cofan.mk M ι)) :
    Nonempty ((I →₀ ↥(((etaleSitePoint B S hS V.1 vbar V.2).presheafFiber
        (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS V).O.obj)) ≃ₗ[
        ↥(((etaleSitePoint B S hS V.1 vbar V.2).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS V).O.obj)]
      ↥(Stacks.moduleStalk (etaleSitePoint B S hS V.1 vbar V.2)
        (smallEtaleRingedTopos B S hS V).O M)) := by
  classical
  let G := Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS V.1 vbar V.2)
    (smallEtaleRingedTopos B S hS V).O
  let Z : I → ModuleCat.{u}
      ↥(((etaleSitePoint B S hS V.1 vbar V.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS V).O.obj) := fun _ =>
    G.obj (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O))
  have hc1 : IsColimit (Cofan.mk (G.obj M) (fun i => G.map (ι i)) : Cofan Z) :=
    Cofan.isColimitMapCoconeEquiv G _ (Cofan.mk M ι) (isColimitOfPreserves G hc)
  let e := hc1.coconePointUniqueUpToIso (ModuleCat.coproductCoconeIsColimit Z)
  let u := Stacks.unitModuleStalkIso (etaleSitePoint B S hS V.1 vbar V.2)
    (smallEtaleRingedTopos B S hS V).O
  exact ⟨((Finsupp.mapRange.linearEquiv u.toLinearEquiv.symm).trans
    (finsuppLequivDFinsupp _)).trans e.symm.toLinearEquiv⟩

/-- **The stalk of a free module at a point of the small étale site is free**, before the
extension of scalars to the étale local ring: the stalk functor carries the colimiting cofan
exhibiting `F` as a coproduct of copies of `𝒪_X` to a colimiting cofan of copies of the stalk
of `𝒪_X`, which is the stalk ring. -/
theorem free_moduleStalk_of_isFreeModule (V : AlgebraicSpaces B S hS)
    (vbar : GeometricPoint B S hS V.1) (M : Modules.{u, u} B S hS V.1 V.2)
    (hM : IsFreeModule B S hS V M) :
    Module.Free
      ↥(((etaleSitePoint B S hS V.1 vbar V.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS V).O.obj)
      ↥(Stacks.moduleStalk (etaleSitePoint B S hS V.1 vbar V.2)
        (smallEtaleRingedTopos B S hS V).O M) := by
  obtain ⟨I, ι, ⟨hc⟩⟩ := hM
  obtain ⟨e⟩ := nonempty_linearEquiv_finsupp_moduleStalk B S hS V vbar M I ι hc
  exact Module.Free.of_equiv e

/-- **The geometric stalk of a free module is a free module.**  For an `𝒪_X`-module `F` on an
algebraic space `X` which is a coproduct of copies of `𝒪_X` on the small étale site, indexed by
an arbitrary type, and a geometric point `x̄`, the stalk `F_{x̄}` of Stacks 05VQ is free over the
étale local ring `𝒪_{X, x̄}`. -/
theorem free_geometricModuleStalk_of_isFreeModule (V : AlgebraicSpaces B S hS)
    (vbar : GeometricPoint B S hS V.1) (M : Modules.{u, u} B S hS V.1 V.2)
    (hM : IsFreeModule B S hS V M) :
    Module.Free ↥(etaleLocalRing B S hS V.1 vbar) ↥(geometricModuleStalk B S hS V vbar M) := by
  have h1 := free_moduleStalk_of_isFreeModule B S hS V vbar M hM
  have h2 : Module.Free
      ↥(((etaleSitePoint B S hS V.1 vbar V.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS V).O.obj)
      ↥(Stacks.moduleStalkLarge (etaleSitePoint B S hS V.1 vbar V.2)
        (smallEtaleRingedTopos B S hS V).O M) :=
    Module.Free.of_equiv (Stacks.moduleStalkLargeLinearEquiv
      (etaleSitePoint B S hS V.1 vbar V.2) (smallEtaleRingedTopos B S hS V).O M).symm
  let := RingHomInvPair.of_ringEquiv (pointStalkRingEquiv B S hS V vbar)
  let := RingHomInvPair.of_ringEquiv_symm (pointStalkRingEquiv B S hS V vbar)
  have e : ↥(Stacks.moduleStalkLarge (etaleSitePoint B S hS V.1 vbar V.2)
        (smallEtaleRingedTopos B S hS V).O M) ≃ₛₗ[(pointStalkRingEquiv B S hS V vbar :
        ↥(((etaleSitePoint B S hS V.1 vbar V.2).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS V).O.obj) →+* ↥(etaleLocalRing B S hS V.1 vbar))]
      ↥(geometricModuleStalk B S hS V vbar M) :=
    { toFun := geometricModuleStalkAddEquiv B S hS V vbar M
      map_add' := map_add _
      map_smul' := geometricModuleStalkAddEquiv_smul B S hS V vbar M
      invFun := (geometricModuleStalkAddEquiv B S hS V vbar M).symm
      left_inv := (geometricModuleStalkAddEquiv B S hS V vbar M).left_inv
      right_inv := (geometricModuleStalkAddEquiv B S hS V vbar M).right_inv }
  exact Module.Free.of_equiv e

/-- **An invertible module which is free has a single generator.**  If an `𝒪_V`-module `M` is
the coproduct of copies of `𝒪_V` indexed by `I`, through a colimiting cofan, and `M` is
invertible, then at a geometric point `v̄` of `V` the stalk of `M` is both `⊕_{i ∈ I} 𝒪_{V, v̄}`
and, by the triviality of the Picard group of the local ring `𝒪_{V, v̄}`, free of rank one;
comparing ranks over that nonzero commutative ring, `I` has exactly one element. -/
theorem nonempty_unique_of_isColimit_cofan_of_isInvertibleModule (V : AlgebraicSpaces B S hS)
    (vbar : GeometricPoint B S hS V.1) (M : Modules.{u, u} B S hS V.1 V.2) (I : Type u)
    (ι : I → (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O) ⟶ M))
    (hc : IsColimit (Cofan.mk M ι)) (hM : IsInvertibleModule V M) :
    Nonempty (Unique I) := by
  let R := ↥(((etaleSitePoint B S hS V.1 vbar V.2).presheafFiber (A := CommRingCat.{u})).obj
    (smallEtaleRingedTopos B S hS V).O.obj)
  let : IsLocalRing ↥(etaleLocalRing B S hS V.1 vbar) :=
    isLocalRing_etaleLocalRing B S hS V.1 V.2 vbar
  let : IsLocalRing R := (pointStalkRingEquiv B S hS V vbar).symm.isLocalRing
  obtain ⟨g⟩ := nonempty_linearEquiv_finsupp_moduleStalk B S hS V vbar M I ι hc
  obtain ⟨h⟩ := nonempty_linearEquiv_moduleStalkLarge_of_isInvertibleModule B S hS V vbar M hM
  let f := (Stacks.moduleStalkLargeLinearEquiv
    (etaleSitePoint B S hS V.1 vbar V.2) (smallEtaleRingedTopos B S hS V).O M).symm.trans h
  have hrank : Module.rank R (I →₀ R) = 1 := (g.trans f).rank_eq.trans (Module.rank_self R)
  rw [rank_finsupp_self'] at hrank
  obtain ⟨hsub, hne⟩ := Cardinal.eq_one_iff_unique.1 hrank
  exact ⟨@uniqueOfSubsingleton _ hsub hne.some⟩

end AlgebraicGeometry.Space

end
