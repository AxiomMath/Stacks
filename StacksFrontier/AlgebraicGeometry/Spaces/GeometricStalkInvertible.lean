module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkRankOneDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedReduced
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne

/-!
# The stalk of an invertible module at a geometric point is free of rank one

Let `X` be an algebraic space over a scheme `S`, let `ℒ` be an invertible `𝒪_X`-module and let
`x̄` be a geometric point of `X`.  Then the geometric stalk `ℒ_{x̄}` is free of rank one over
the étale local ring `𝒪_{X, x̄}`, and — by Stacks 05VP and faithfully flat descent — the
Zariski stalk `(φ^* ℒ)_u` of the restriction of `ℒ` to a scheme chart `U` of a small étale
neighbourhood is free of rank one over the local ring `𝒪_{U, u}` of the chart.

The argument is the one `Stacks.SheafOfModules.module_invertible_grpStalk` carries out for a
ringed space, transposed to a point of the small étale site: invertibility gives an `𝒪_X`-module
`𝒩` with `ℒ ⊗ 𝒩 ≅ 𝒪_X` (Stacks 0B8K), the stalk functor at the site point turns that into a
linear equivalence `ℒ_{x̄} ⊗_{𝒪_{X, x̄}} 𝒩_{x̄} ≃ 𝒪_{X, x̄}` of stalks, so `ℒ_{x̄}` is an
invertible module, and the Picard group of the local ring `𝒪_{X, x̄}` is trivial.

## Main definitions

* `Stacks.unitModuleStalkIso`: the stalk at a point of a site of a sheaf of commutative rings
  viewed as a module over itself is the stalk ring.
* `AlgebraicGeometry.Space.etaleLocalRingToGeometricModuleStalkAddEquiv`: a trivialisation of
  the stalk before the extension of scalars, read as an additive comparison of the étale local
  ring with the geometric stalk.

## Main results

* `AlgebraicGeometry.Space.module_invertible_moduleStalk`: the stalk of an invertible module at
  the point of the small étale site determined by a geometric point is an invertible module
  over the stalk of the structure sheaf there.
* `AlgebraicGeometry.Space.nonempty_linearEquiv_geometricModuleStalk_of_isInvertibleModule`:
  **the geometric stalk of an invertible module is free of rank one** over the étale local ring.
* `AlgebraicGeometry.Space.nonempty_linearEquiv_chartZariskiModuleStalk_of_isInvertibleModule`:
  the Zariski stalk of the chart restriction of an invertible module is free of rank one over
  the local ring of the chart.

## Implementation notes

Two presentations of the stalk are in play and both are needed.  Tensor compatibility,
`AlgebraicGeometry.Space.geometricModuleStalkTensorIso`, is stated for the stalk functor
`Stacks.sheafModuleFiberOfCommRing`, whose values are `Stacks.moduleStalk`, whereas
`AlgebraicGeometry.Space.geometricModuleStalk` is built from `Stacks.moduleStalkLarge`.
`Stacks.moduleStalkLargeLinearEquiv` is the comparison between them, available because the
module universe here is the universe of the structure rings.

The passage from the stalk over the fibre of the structure sheaf to the geometric stalk over
the étale local ring is the extension of scalars along
`AlgebraicGeometry.Space.pointStalkRingEquiv`, which is a ring *equivalence*; a trivialisation
of the one therefore transports to a trivialisation of the other.  The transport is written as
an additive equivalence plus its scalar law, exactly as
`AlgebraicGeometry.Space.etaleLocalRingToStructureSheafStalkAddEquiv` does for the structure
sheaf itself, the case of the statements below at `ℒ = 𝒪_X`.

Quasi-coherence of `ℒ`, which the Zariski-stalk statement needs because Stacks 05VP does, is
not an added hypothesis: it is supplied by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertibleModule`.

No `stacks` attribute is attached, matching the ringed-space statements
`Stacks.SheafOfModules.module_invertible_grpStalk` and
`Stacks.SheafOfModules.nonempty_grpStalk_linearEquiv`, which are the same mathematics and are
likewise untagged: each is a composition of Stacks 0B8K with the triviality of the Picard group
of a local ring, and the final statement adds Stacks 05VP, every part of which carries its own
tag where it is proved.

## References

* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 08AH](https://stacks.math.columbia.edu/tag/08AH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.SheafOfModules

universe w v t u

namespace Stacks

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

/-- **The stalk of a sheaf of commutative rings as a module over itself is the stalk ring**, in
the `Stacks.moduleStalk` presentation.  It is `Stacks.unitModuleStalkLargeEquiv` carried across
the comparison of the two presentations of the stalk. -/
noncomputable def unitModuleStalkIso :
    moduleStalk p O (SheafOfModules.unit (commRingSheafToRingSheaf O)) ≅
      ModuleCat.of ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj)
        ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) :=
  (moduleStalkLargeIso p O (SheafOfModules.unit (commRingSheafToRingSheaf O))).symm ≪≫
    (unitModuleStalkLargeEquiv p O).toModuleIso

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The stalk of an invertible module at a point of the small étale site is an invertible
module.**  By Stacks 0B8K there is an `𝒪_X`-module `𝒩` with `ℒ ⊗ 𝒩 ≅ 𝒪_X`; the stalk functor
takes that isomorphism to a linear equivalence `ℒ_{x̄} ⊗ 𝒩_{x̄} ≃ 𝒪_{X, x̄}` of stalks, and a
module admitting such a partner is invertible.  No hypothesis on the stalk ring is needed. -/
theorem module_invertible_moduleStalk (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : IsInvertibleModule X L) :
    Module.Invertible
      ↥(((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj)
      ↥(Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O L) := by
  obtain ⟨N, ⟨e⟩⟩ :=
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L).mp hL
  have hcomp := ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O).mapIso e).symm ≪≫
    geometricModuleStalkTensorIso B S hS X.1 X.2 (smallEtaleRingedTopos B S hS X).O x L N
  exact Module.Invertible.left (hcomp.symm ≪≫
    Stacks.unitModuleStalkIso (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O).toLinearEquiv

/-- **The stalk of an invertible module at a point of the small étale site is free of rank
one**, before the extension of scalars to the étale local ring.  The stalk of the structure
sheaf there is a local ring, being the étale local ring up to
`AlgebraicGeometry.Space.pointStalkRingEquiv`, and the Picard group of a local ring is
trivial. -/
theorem nonempty_linearEquiv_moduleStalkLarge_of_isInvertibleModule
    (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L) :
    Nonempty (↥(Stacks.moduleStalkLarge (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O L) ≃ₗ[
        ↥(((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS X).O.obj)]
      ↥(((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj)) := by
  let : IsLocalRing ↥(etaleLocalRing B S hS X.1 x) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  let : IsLocalRing ↥(((etaleSitePoint B S hS X.1 x X.2).presheafFiber
      (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O.obj) :=
    (pointStalkRingEquiv B S hS X x).symm.isLocalRing
  have := module_invertible_moduleStalk B S hS X x L hL
  obtain ⟨g⟩ := Stacks.SheafOfModules.Invertible.nonempty_linearEquiv_of_module_invertible
    ↥(((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X).O.obj)
    ↥(Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
      (smallEtaleRingedTopos B S hS X).O L)
  exact ⟨(Stacks.moduleStalkLargeLinearEquiv (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O L).trans g⟩

variable (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)
  (F : Modules.{u, u} B S hS X.1 X.2)
  (g : ↥(Stacks.moduleStalkLarge (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O F)
      ≃ₗ[↥(((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj)]
      ↥(((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (smallEtaleRingedTopos B S hS X).O.obj))

/-- **A trivialisation of the stalk before the extension of scalars gives one of the geometric
stalk**, as an additive comparison of the étale local ring with the geometric stalk: the
extension of scalars defining the geometric stalk is along the ring *equivalence*
`AlgebraicGeometry.Space.pointStalkRingEquiv`, so it changes neither the underlying additive
group nor the property of being free of rank one. -/
noncomputable def etaleLocalRingToGeometricModuleStalkAddEquiv :
    ↥(etaleLocalRing B S hS X.1 x) ≃+ ↥(geometricModuleStalk B S hS X x F) :=
  ((pointStalkRingEquiv B S hS X x).symm.toAddEquiv.trans g.symm.toAddEquiv).trans
    (geometricModuleStalkAddEquiv B S hS X x F)

/-- The comparison is the trivialisation read through the two identifications of the stalks. -/
theorem etaleLocalRingToGeometricModuleStalkAddEquiv_apply
    (a : ↥(etaleLocalRing B S hS X.1 x)) :
    etaleLocalRingToGeometricModuleStalkAddEquiv B S hS X x F g a =
      geometricModuleStalkAddEquiv B S hS X x F
        (g.symm ((pointStalkRingEquiv B S hS X x).symm a)) :=
  rfl

/-- The comparison of the étale local ring with the geometric stalk is linear over the étale
local ring. -/
theorem etaleLocalRingToGeometricModuleStalkAddEquiv_smul
    (a b : ↥(etaleLocalRing B S hS X.1 x)) :
    etaleLocalRingToGeometricModuleStalkAddEquiv B S hS X x F g (a • b) =
      a • etaleLocalRingToGeometricModuleStalkAddEquiv B S hS X x F g b := by
  refine Eq.trans
    (etaleLocalRingToGeometricModuleStalkAddEquiv_apply B S hS X x F g (a • b)) ?_
  refine Eq.trans ?_ (congrArg (fun w => a • w)
    (etaleLocalRingToGeometricModuleStalkAddEquiv_apply B S hS X x F g b)).symm
  refine Eq.trans (congrArg (fun r => geometricModuleStalkAddEquiv B S hS X x F (g.symm r))
    (map_mul (pointStalkRingEquiv B S hS X x).symm a b)) ?_
  refine Eq.trans (congrArg (geometricModuleStalkAddEquiv B S hS X x F)
    (map_smul g.symm ((pointStalkRingEquiv B S hS X x).symm a)
      ((pointStalkRingEquiv B S hS X x).symm b))) ?_
  refine Eq.trans (geometricModuleStalkAddEquiv_smul B S hS X x F
    ((pointStalkRingEquiv B S hS X x).symm a) _) ?_
  exact congrArg (fun c => c • geometricModuleStalkAddEquiv B S hS X x F
      (g.symm ((pointStalkRingEquiv B S hS X x).symm b)))
    ((pointStalkRingEquiv B S hS X x).apply_symm_apply a)

/-- **The geometric stalk of an invertible module is free of rank one.**  For an invertible
`𝒪_X`-module `ℒ` on an algebraic space `X` and a geometric point `x̄`, the stalk `ℒ_{x̄}` of
Stacks 05VQ is isomorphic to the étale local ring `𝒪_{X, x̄}` as a module over it. -/
theorem nonempty_linearEquiv_geometricModuleStalk_of_isInvertibleModule
    (L : Modules.{u, u} B S hS X.1 X.2) (hL : IsInvertibleModule X L) :
    Nonempty (↥(geometricModuleStalk B S hS X x L) ≃ₗ[↥(etaleLocalRing B S hS X.1 x)]
      ↥(etaleLocalRing B S hS X.1 x)) := by
  obtain ⟨h⟩ := nonempty_linearEquiv_moduleStalkLarge_of_isInvertibleModule B S hS X x L hL
  exact ⟨((etaleLocalRingToGeometricModuleStalkAddEquiv B S hS X x L h).toLinearEquiv
    (etaleLocalRingToGeometricModuleStalkAddEquiv_smul B S hS X x L h)).symm⟩

/-- **The Zariski stalk of an invertible module on a scheme chart is free of rank one.**  Let
`ℒ` be an invertible `𝒪_X`-module on an algebraic space `X`, let `x̄` be a geometric point and
let `V` be a small étale neighbourhood of `x̄` whose chart is a scheme `U`.  Then the Zariski
stalk `(φ^* ℒ)_u` is isomorphic to the local ring `𝒪_{U, u}` of the chart as a module over it.

The geometric stalk is free of rank one, Stacks 05VP identifies it with
`(φ^* ℒ)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}`, and that base change is faithfully flat with local target,
so the conclusion descends.  Quasi-coherence, which Stacks 05VP requires, comes from
invertibility and is not an extra hypothesis. -/
theorem nonempty_linearEquiv_chartZariskiModuleStalk_of_isInvertibleModule
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {y : GeometricPoint B S hS Y} (V : SmallEtaleNeighborhood y)
    (L : Modules.{u, u} B S hS Y hY) (hL : IsInvertibleModule ⟨Y, hY⟩ L) :
    Nonempty (↥(chartZariskiModuleStalk B S hS Y hY V L) ≃ₗ[↥(chartLocalRing B S hS Y V)]
      ↥(chartLocalRing B S hS Y V)) := by
  have : L.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertibleModule ⟨Y, hY⟩ L hL
  obtain ⟨e⟩ := nonempty_linearEquiv_geometricModuleStalk_of_isInvertibleModule
    B S hS ⟨Y, hY⟩ y L hL
  exact nonempty_linearEquiv_chartZariskiModuleStalk_of_geometricModuleStalk
    B S hS hY V L e

end AlgebraicGeometry.Space

end
