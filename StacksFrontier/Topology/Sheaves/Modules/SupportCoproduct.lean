module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# The support of a coproduct of sheaves of modules

Let `O` be a sheaf of rings on a topological space and let `(M j)` be a family of sheaves of
`O`-modules indexed by a small type. The stalk at a point of the coproduct `∐ M` is the coproduct
of the stalks, because the stalk functor preserves colimits
(`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`, Stacks 01AH), and a coproduct
of modules is nonzero exactly when one of its summands is. Combining the two, the support of a
coproduct of sheaves of modules on a scheme is the union of the supports:

`x ∈ Supp(∐ M) ↔ ∃ j, x ∈ Supp(M j)`.

Support is `AlgebraicGeometry.RingedSpace.ModuleSheaf.supp` of Stacks 01AT, the set of points at
which the stalk is nonzero.

## Main results

* `AlgebraicGeometry.SheafOfModules.nontrivial_coproduct_iff` — a coproduct in `ModuleCat R` is
  nontrivial exactly when one of its summands is.
* `AlgebraicGeometry.SheafOfModules.nontrivial_stalkFunctor_coproduct_iff` — the same one level
  up: the stalk of a coproduct of sheaves of modules is nontrivial exactly when the stalk of one
  of the summands is.
* `AlgebraicGeometry.SheafOfModules.mem_supp_iff_nontrivial_stalkFunctor` — the support of Stacks
  01AT, read through the stalk functor of Stacks 01AH.
* `AlgebraicGeometry.SheafOfModules.mem_supp_coproduct_iff` — **the support of a coproduct is the
  union of the supports.**

## Implementation notes

The index type lies in `Type 0`. That is where the intended consumer needs it — the family
`{j : ℤ // j ≤ i}` of Ext sheaves of a dualizing complex through a fixed degree — and it keeps the
coproduct inside the sizes for which this library knows `SheafOfModules O` to be cocomplete.

The passage from the stalk of the coproduct to the coproduct of the stalks is not a direct appeal
to `preservesColimitIso`: `stalkFunctor_preservesColimits` is stated for colimits of arbitrary
shape, so the discrete-shape instance is extracted from it and the comparison is then the
canonical isomorphism between two colimit cocone points. The diagram
`Discrete.functor M ⋙ stalkFunctor` is replaced by `Discrete.functor` of its own values along
`Discrete.natIso`, because `coproductIsCoproduct` is stated for the latter shape.

The support of Stacks 01AT is a notion about `AlgebraicGeometry.RingedSpace.ModuleSheaf`, a
structure bundling a presheaf of modules with the sheaf condition on its underlying presheaf of
abelian groups, whereas the stalk functor of Stacks 01AH is a functor on the categorical
`SheafOfModules`. The two are connected by the anonymous constructor `⟨M.val, M.isSheaf⟩`, which
is how the statements below are phrased; the comparison itself is `rfl`, since
`AlgebraicGeometry.SheafOfModules.stalkObj` is by definition the `AddCommGrpCat`-valued stalk of
the underlying presheaf equipped with the action of the stalk of the sheaf of rings, and that is
the stalk whose nonvanishing defines the support.

No `@[stacks]` attribute is placed. Stacks 01AT is the definition of support, already carried by
`AlgebraicGeometry.RingedSpace.ModuleSheaf.supp`, and Stacks 01AH by
`AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`; the statements here are neither
of those, and a second attribute would claim a tag twice.

## References

* [Stacks Project, Tag 01AT](https://stacks.math.columbia.edu/tag/01AT)
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DirectSum TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- A coproduct of modules over a ring is nontrivial exactly when one of its summands is. -/
public theorem nontrivial_coproduct_iff {R : Type u} [Ring R] {ι : Type}
    (M : ι → ModuleCat.{u} R) :
    Nontrivial (↑(∐ M : ModuleCat.{u} R)) ↔ ∃ j, Nontrivial (M j) := by
  classical
  refine (Equiv.nontrivial_congr
    (ModuleCat.coprodIsoDirectSum M).toLinearEquiv.toEquiv).trans ?_
  change Nontrivial (⨁ j, (M j : Type u)) ↔ _
  constructor
  · rintro ⟨a, b, hab⟩
    obtain ⟨j, hj⟩ := not_forall.mp fun h ↦ hab (DirectSum.ext_component R h)
    exact ⟨j, nontrivial_of_ne _ _ hj⟩
  · rintro ⟨j, hj⟩
    obtain ⟨a, b, hab⟩ := @exists_pair_ne (M j) hj
    refine ⟨DirectSum.lof R ι (fun j ↦ (M j : Type u)) j a,
      DirectSum.lof R ι (fun j ↦ (M j : Type u)) j b, fun h ↦ hab ?_⟩
    simpa using congrArg (DirectSum.component R ι (fun j ↦ (M j : Type u)) j) h

/-- The stalk at `x` of a coproduct of sheaves of modules is nontrivial exactly when the stalk of
one of the summands is.

The stalk functor preserves colimits (Stacks 01AH), so the stalk of the coproduct is the
coproduct of the stalks, to which
`AlgebraicGeometry.SheafOfModules.nontrivial_coproduct_iff` applies. -/
public theorem nontrivial_stalkFunctor_coproduct_iff {X : TopCat.{u}}
    (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) {ι : Type}
    (M : ι → _root_.SheafOfModules.{u} O) :
    Nontrivial ((stalkFunctor O x).obj (∐ M)) ↔
      ∃ j, Nontrivial ((stalkFunctor O x).obj (M j)) := by
  let G := stalkFunctor O x
  let D : Discrete ι ⥤ _root_.SheafOfModules.{u} O := Discrete.functor M
  have hPres : PreservesColimitsOfShape (Discrete ι) G :=
    (preservesSmallestColimits_of_preservesColimits G).preservesColimitsOfShape
  let N : ι → ModuleCat _ := fun j ↦ (D ⋙ G).obj (Discrete.mk j)
  let D' : Discrete ι ⥤ ModuleCat _ := Discrete.functor N
  let α : D ⋙ G ≅ D' := Discrete.natIso fun _ ↦ Iso.refl _
  have hN : IsColimit ((Cocone.precompose α.hom).obj (Sigma.cocone D')) :=
    (IsColimit.precomposeHomEquiv α (Sigma.cocone D')).symm (coproductIsCoproduct N)
  let e : G.obj (∐ M) ≅ ∐ N :=
    IsColimit.coconePointUniqueUpToIso
      ((hPres.preservesColimit (K := D)).preserves (coproductIsCoproduct M)).some hN
  exact (Equiv.nontrivial_congr e.toLinearEquiv.toEquiv).trans (nontrivial_coproduct_iff N)

/-- The support of Stacks 01AT, read through the stalk functor of Stacks 01AH: a point lies in the
support of a sheaf of modules on a scheme exactly when the stalk functor sends the sheaf to a
nontrivial module. -/
public theorem mem_supp_iff_nontrivial_stalkFunctor {X : Scheme.{u}} (M : X.Modules) (x : X) :
    x ∈ (⟨M.val, M.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ↔
      Nontrivial ((stalkFunctor X.ringCatSheaf x).obj M) :=
  (nontrivial_iff_exists_ne
    (0 : (⟨M.val, M.isSheaf⟩ :
      RingedSpace.ModuleSheaf.{u} X.toRingedSpace).abPresheaf.stalk x)).symm

/-- **The support of a coproduct of sheaves of modules is the union of the supports.** -/
public theorem mem_supp_coproduct_iff {X : Scheme.{u}} {ι : Type} (M : ι → X.Modules) (x : X) :
    x ∈ (⟨(∐ M).val, (∐ M).isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp ↔
      ∃ j, x ∈ (⟨(M j).val, (M j).isSheaf⟩ :
        RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp :=
  (mem_supp_iff_nontrivial_stalkFunctor (∐ M) x).trans
    ((nontrivial_stalkFunctor_coproduct_iff X.ringCatSheaf x M).trans
      (exists_congr fun j ↦ (mem_supp_iff_nontrivial_stalkFunctor (M j) x).symm))

end AlgebraicGeometry.SheafOfModules

end
