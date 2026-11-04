module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedReduced

/-!
# The geometric stalk of the structure sheaf of an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `x̄`
be a geometric point of `X`.  The structure sheaf `𝒪_X` is an `𝒪_X`-module — the free module of
rank one — and this file identifies its stalk at `x̄` with the étale local ring `𝒪_{X, x̄}` of
Stacks 04KG, as a module over that ring:

`(𝒪_X)_{x̄} ≃ₗ[𝒪_{X, x̄}] 𝒪_{X, x̄}`.

Two consequences are recorded.  The stalk is nonzero at every geometric point, because the
étale local ring is a local ring and so nontrivial; and therefore the support of `𝒪_X` in the
sense of Stacks 04KA is the whole of `|X|`.

## Main definitions

* `AlgebraicGeometry.Space.structureSheafModule`: the structure sheaf of an algebraic space
  regarded as a module over itself, the free `𝒪_X`-module of rank one.
* `AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv`: **the stalk of `𝒪_X` at a
  geometric point `x̄` is the étale local ring `𝒪_{X, x̄}`**, as `𝒪_{X, x̄}`-modules.

## Main results

* `AlgebraicGeometry.Space.ringSheaf_smallEtaleRingedSite_eq`: the sheaf of rings in which
  `𝒪_X`-modules are indexed has two spellings in this development, one coming from the small
  étale ringed *site* and one from the small étale ringed *topos*, and they are the same sheaf.
* `AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_structureSheafModule`: the stalk of
  `𝒪_X` at a geometric point is nonzero.
* `AlgebraicGeometry.Space.supportOfSheaf_structureSheafModule`: **`Supp(𝒪_X) = |X|`.**

## Implementation notes

**The two spellings of the structure sheaf of rings.**  `AlgebraicGeometry.Space.Modules`, the
`𝒪_X`-modules, are the sheaves of modules over
`AlgebraicGeometry.RingedSite.ringSheaf (AlgebraicGeometry.Space.smallEtaleRingedSite …)`,
which forgets commutativity using the instance
`AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat` carried by the ringed site.  The
stalk machinery of `Stacks.moduleStalkLarge` and the comparison
`Stacks.unitModuleStalkLargeEquiv` are instead phrased over
`Stacks.commRingSheafToRingSheaf (AlgebraicGeometry.Space.smallEtaleRingedTopos …).O`, which
takes that instance from the ambient context.  The two sheaves of rings have the same
underlying presheaf `𝒪_X ⋙ forget₂ CommRingCat RingCat` and differ only in the proof of the
sheaf condition, so they are equal, and `ringSheaf_smallEtaleRingedSite_eq` records this by
`rfl`.  Stating the comparison of the *stalks* as a linear equivalence across the two spellings
asks the elaborator to unfold both ringed structures at once while unifying the scalars, which
it does not do within its default budget; stating the equality of the two sheaves of rings on
its own does not, because proof irrelevance disposes of the only field that differs.  Every
statement below is therefore written in the ringed-site spelling, which is the one
`AlgebraicGeometry.Space.Modules` uses, and the results about `Stacks.moduleStalkLarge` are
applied to it directly in term mode; `rw` is avoided, since its motive check runs at a
transparency at which the two spellings are not interchangeable.

**The comparison.**  The two steps are `Stacks.unitModuleStalkLargeEquiv`, which identifies the
stalk of `𝒪_X` at the point of the small étale site with the stalk of the sheaf of rings there,
and `AlgebraicGeometry.Space.geometricModuleStalkAddEquiv`, which crosses the extension of
scalars along `AlgebraicGeometry.Space.pointStalkRingEquiv` separating that stalk from the
geometric one.  The second is only additive, and is semilinear along `pointStalkRingEquiv`, so
the composite is assembled as an `AddEquiv` whose linearity over `𝒪_{X, x̄}` is proved
separately in `etaleLocalRingToStructureSheafStalkAddEquiv_smul` and installed by
`AddEquiv.toLinearEquiv`.  The composite is formed in the direction
`𝒪_{X, x̄} → (𝒪_X)_{x̄}` because the semilinearity of `geometricModuleStalkAddEquiv` is recorded
in that direction, and inverted at the end.

**The support.**  `AlgebraicGeometry.Space.supportOfSheaf` is read at a geometric point by
Stacks 07TZ, whose hypothesis is quasi-coherence of the module; for `𝒪_X` that is
`SheafOfModules.isQuasicoherentOnSite_unit`, so no hypothesis is carried.  Every point of `|X|`
is the image of a geometric point by
`AlgebraicGeometry.Space.exists_geometricRepresentative`.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The two spellings of the structure sheaf of rings -/

/-- The sheaf of rings of the small étale ringed site of an algebraic space, in which
`AlgebraicGeometry.Space.Modules` indexes the `𝒪_X`-modules, is the sheaf of rings underlying
the structure sheaf of the small étale ringed topos.

Both are the presheaf `𝒪_X ⋙ forget₂ CommRingCat RingCat` together with a proof of the sheaf
condition, the two proofs being the instance carried by the ringed site and the one found in
the ambient context; proof irrelevance identifies them. -/
theorem ringSheaf_smallEtaleRingedSite_eq (X : AlgebraicSpaces B S hS) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) =
      Stacks.commRingSheafToRingSheaf (smallEtaleRingedTopos B S hS X).O :=
  rfl

/-- The structure sheaf of an algebraic space regarded as an `𝒪_X`-module: the free module of
rank one, whose sections over an étale chart are the regular functions on it. -/
abbrev structureSheafModule (X : AlgebraicSpaces B S hS) : Modules.{u, u} B S hS X.1 X.2 :=
  SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-! ### The geometric stalk of the structure sheaf -/

section Stalk

variable (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1)

/-- The étale local ring `𝒪_{X, x̄}` is the stalk of `𝒪_X` at `x̄`, as additive groups: the stalk
of the sheaf of rings at the point of the small étale site is the stalk of `𝒪_X` viewed as a
module over itself there (`Stacks.unitModuleStalkLargeEquiv`), and the extension of scalars to
the étale local ring does not change the underlying additive group
(`AlgebraicGeometry.Space.geometricModuleStalkAddEquiv`). -/
def etaleLocalRingToStructureSheafStalkAddEquiv :
    (etaleLocalRing B S hS X.1 x) ≃+
      (geometricModuleStalk B S hS X x (structureSheafModule B S hS X) : Type (u + 1)) :=
  ((pointStalkRingEquiv B S hS X x).symm.toAddEquiv.trans
      (Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).toAddEquiv.symm).trans
    (geometricModuleStalkAddEquiv B S hS X x (structureSheafModule B S hS X))

/-- The three steps of `AlgebraicGeometry.Space.etaleLocalRingToStructureSheafStalkAddEquiv`,
spelled out. -/
theorem etaleLocalRingToStructureSheafStalkAddEquiv_apply (a : etaleLocalRing B S hS X.1 x) :
    etaleLocalRingToStructureSheafStalkAddEquiv B S hS X x a =
      geometricModuleStalkAddEquiv B S hS X x (structureSheafModule B S hS X)
        ((Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O).symm
          ((pointStalkRingEquiv B S hS X x).symm a)) :=
  rfl

/-- The comparison of the étale local ring with the stalk of `𝒪_X` is linear over the étale
local ring.

The middle step is linear over the stalk of the sheaf of rings at the point of the site, and
the outer two steps are the ring isomorphism `AlgebraicGeometry.Space.pointStalkRingEquiv` and
its inverse, along which the extension of scalars is semilinear. -/
theorem etaleLocalRingToStructureSheafStalkAddEquiv_smul
    (a b : etaleLocalRing B S hS X.1 x) :
    etaleLocalRingToStructureSheafStalkAddEquiv B S hS X x (a • b) =
      a • etaleLocalRingToStructureSheafStalkAddEquiv B S hS X x b := by
  refine Eq.trans (etaleLocalRingToStructureSheafStalkAddEquiv_apply B S hS X x (a • b)) ?_
  refine Eq.trans ?_ (congrArg (fun w => a • w)
    (etaleLocalRingToStructureSheafStalkAddEquiv_apply B S hS X x b)).symm
  refine Eq.trans (congrArg (fun r =>
      geometricModuleStalkAddEquiv B S hS X x (structureSheafModule B S hS X)
        ((Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O).symm r))
      (map_mul (pointStalkRingEquiv B S hS X x).symm a b)) ?_
  refine Eq.trans
    (congrArg (geometricModuleStalkAddEquiv B S hS X x (structureSheafModule B S hS X))
      (map_smul (Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O).symm
        ((pointStalkRingEquiv B S hS X x).symm a)
        ((pointStalkRingEquiv B S hS X x).symm b))) ?_
  refine Eq.trans (geometricModuleStalkAddEquiv_smul B S hS X x
    (structureSheafModule B S hS X) ((pointStalkRingEquiv B S hS X x).symm a) _) ?_
  exact congrArg (fun c => c •
      geometricModuleStalkAddEquiv B S hS X x (structureSheafModule B S hS X)
        ((Stacks.unitModuleStalkLargeEquiv (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O).symm
          ((pointStalkRingEquiv B S hS X x).symm b)))
    ((pointStalkRingEquiv B S hS X x).apply_symm_apply a)

/-- **The stalk of the structure sheaf at a geometric point is the étale local ring.**  For a
geometric point `x̄` of an algebraic space `X`, the stalk of `𝒪_X` at `x̄` in the sense of
Stacks 05VQ is `𝒪_{X, x̄}` as a module over itself. -/
def structureSheafGeometricStalkEquiv :
    (geometricModuleStalk B S hS X x (structureSheafModule B S hS X) : Type (u + 1)) ≃ₗ[
        etaleLocalRing B S hS X.1 x] (etaleLocalRing B S hS X.1 x) :=
  ((etaleLocalRingToStructureSheafStalkAddEquiv B S hS X x).toLinearEquiv
    (etaleLocalRingToStructureSheafStalkAddEquiv_smul B S hS X x)).symm

/-- **The stalk of the structure sheaf at a geometric point is nonzero**: it is the étale local
ring, which is a local ring by Stacks 08AH and hence nontrivial. -/
theorem nontrivial_geometricModuleStalk_structureSheafModule :
    Nontrivial (geometricModuleStalk B S hS X x (structureSheafModule B S hS X)) := by
  let _ := isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  exact (etaleLocalRingToStructureSheafStalkAddEquiv B S hS X x).toEquiv.nontrivial_congr.mp
    inferInstance

end Stalk

/-! ### The support of the structure sheaf -/

/-- **`Supp(𝒪_X) = |X|`.**  The support of the structure sheaf of an algebraic space, in the
sense of Stacks 04KA, is the whole point set.

The structure sheaf is quasi-coherent, so by Stacks 07TZ its support is read on the stalk at
any geometric point above the given point; every point has such a geometric point, and the
stalk there is the étale local ring, which is nonzero. -/
theorem supportOfSheaf_structureSheafModule (X : AlgebraicSpaces B S hS) :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj (structureSheafModule B S hS X)) = Set.univ := by
  refine Set.eq_univ_of_forall fun pt => ?_
  obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X.1 pt
  subst hxbar
  exact (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk_of_liesOver B S hS X
      (structureSheafModule B S hS X) xbar _ rfl).2
    (nontrivial_geometricModuleStalk_structureSheafModule B S hS X xbar)

end AlgebraicGeometry.Space

end
