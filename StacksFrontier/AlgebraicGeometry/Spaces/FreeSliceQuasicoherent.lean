module

public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorFree

/-!
# Free modules on the slice at a chart are quasi-coherent

Granted Stacks 03DT, this makes the essential-surjectivity hypothesis of Descent, Proposition
03DX(2) non-vacuous.

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `Y` be
an étale chart of `F`.  The forward implication of Descent, Proposition 03DX(2) is carried
through this tree as the hypothesis `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_isQuasicoherentOnSite_of_essSurj`:
*every quasi-coherent module on the slice of the small étale site of `F` at an affine chart is an
`Mᵃ`*.  A hypothesis of that shape is exactly the kind no compiler check can detect — a theorem resting on a
false or unsatisfiable hypothesis compiles, is axiom-clean, and is vacuous — so it needs a
witness that its antecedent and its conclusion are simultaneously satisfiable at some module.

This file supplies one.  `StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFree` proves
the conclusion of `hEss` at the free modules; what is added here is that **the free modules are
quasi-coherent on the slice, unconditionally**, so they satisfy the antecedent too.

Every ingredient is already in the tree and only has to be joined: a free `𝒪_F`-module is
cartesian on affine charts (`AlgebraicGeometry.Space.isCartesianOnAffineCharts_free`, which is
Stacks 0935 and the finite affine refinement of an étale covering, with no cohomological input),
a cartesian module is quasi-coherent on the site
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`, the `←` half of
Descent, Proposition 03DX(2), which *is* proved here), quasi-coherence passes to a slice
(`Stacks.SheafOfModules.isQuasicoherent_over`), and the free module *on the slice* is the
restriction to the slice of the free module on the whole site
(`SheafOfModules.overFunctorFreeIso`).

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.freeSliceIso`: the free module on the slice at a chart,
  identified with the restriction to the slice of the free `𝒪_F`-module.  This is
  `SheafOfModules.overFunctorFreeIso` at this one site, named for use below.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.isQuasicoherentOnSite_free_slice`: **a free module on the
  slice of the small étale site of an algebraic space at a chart is quasi-coherent on that
  slice**, with no hypothesis on the chart and no undischarged input.
* `AlgebraicGeometry.Space.SmallEtale.exists_quasicoherent_sliceAssociatedModule_iso`: **the body
  of the essential-surjectivity hypothesis of Descent, Proposition 03DX(2) is satisfiable at an
  affine chart, granted the sheaf condition of Stacks 03DT there**: there is a quasi-coherent
  module on the slice which is isomorphic to an `Mᵃ`.

## Implementation notes

`AlgebraicGeometry.Space.SmallEtale.freeSliceIso` adds no mathematics: it is
`SheafOfModules.overFunctorFreeIso`
(`StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorFree`), which proves the same thing at an
arbitrary site, specialised to the small étale ringed site of `F`.  It exists only so that the
statement is available at the spellings
`AlgebraicGeometry.Space.SmallEtale.sliceRingSheaf` and
`AlgebraicGeometry.Space.SmallEtale.sliceModule` that these files use.

The specialisation is not an `exact` of the general lemma: the structure sheaf arrives as
`AlgebraicGeometry.Space.RingedSite.ringSheaf` of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, so its Grothendieck topology arrives as the
projection `.J`, which instance search does not unfold, and the sheafification hypotheses of the
general lemma are then unreachable — the specialised instance cannot even be *stated* at that
spelling, since `CategoryTheory.Over U` fails to acquire its category instance.
Binding the structure sheaf to a `let` whose type names
`AlgebraicGeometry.Space.SmallEtale.topology` directly fixes it, and is the whole proof.  This is
the same discipline as
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over`, which exists for the same
reason.

**What this does and does not establish.**  It establishes that `hEss` is not vacuous *granted
Stacks 03DT at the chart*: its antecedent is satisfied — unconditionally — by a module whose
conclusion then holds.  It does *not* prove `hEss`, which quantifies over every quasi-coherent
module of the slice, and it does not prove Stacks 03DV, which asserts quasi-coherence of `Mᵃ` for
every quasi-coherent `M` on the chart's scheme — what is proved here is quasi-coherence of a
*free* module on the site, which is the opposite side of the equivalence and needs no descent.

`AlgebraicGeometry.Space.SmallEtale.isQuasicoherentOnSite_free_slice` is a strict generalisation
of two cases the tree already has: `SheafOfModules.isQuasicoherentOnSite_unit`
(`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf`) is the rank-one case, and
`SheafOfModules.isQuasicoherentOnSite_containsZero` the empty one.  Neither extends to
an arbitrary index type: quasi-coherence on a site is closed under *finite* products only.

No `@[stacks]` attribute is claimed.  Stacks 03DL(6) is the definition of quasi-coherence and is
tagged elsewhere; Stacks 03DV and Stacks 03DX are not proved; and
`AlgebraicGeometry.Space.SmallEtale.exists_quasicoherent_sliceAssociatedModule_iso` is
conditional on the sheaf condition of Stacks 03DT.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe u

namespace AlgebraicGeometry.Space.SmallEtale

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (Y : SmallEtale B S hS F)

/-- **The free module on the slice at a chart is the restriction to the slice of the free module
on the whole site.**  This is `SheafOfModules.overFunctorFreeIso`, which proves it at an
arbitrary site, specialised to the small étale ringed site of `F` — the structure sheaf has to be
bound to a `let` naming `AlgebraicGeometry.Space.SmallEtale.topology`, because the projection `.J`
of `AlgebraicGeometry.Space.smallEtaleRingedSite` leaves the general lemma's sheafification
hypotheses unreachable. -/
noncomputable def freeSliceIso (I : Type u) :
    SheafOfModules.free (R := sliceRingSheaf B S hS F hF Y) I ≅
      sliceModule B S hS F hF Y
        (SheafOfModules.free
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          I) := by
  let RR : Sheaf (SmallEtale.topology B S hS F) RingCat.{u} :=
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)
  exact SheafOfModules.overFunctorFreeIso RR Y I

/-- **A free module on the slice of the small étale site at a chart is quasi-coherent on that
slice**, with no hypothesis on the chart.

The free `𝒪_F`-module on the whole site is cartesian on affine charts
(`AlgebraicGeometry.Space.isCartesianOnAffineCharts_free`) and therefore quasi-coherent
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`, the implication of
Descent, Proposition 03DX(2) that is proved in this tree); quasi-coherence passes to the slice by
`Stacks.SheafOfModules.isQuasicoherent_over`; and the restriction to the slice is the free module
of the slice by `AlgebraicGeometry.Space.SmallEtale.freeSliceIso`. -/
theorem isQuasicoherentOnSite_free_slice (I : Type u) :
    (SheafOfModules.free (R := sliceRingSheaf B S hS F hF Y) I).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (freeSliceIso B S hS F hF Y I).symm
    (Stacks.SheafOfModules.isQuasicoherent_over _
      (isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
        (isCartesianOnAffineCharts_free (hF := hF) I)) Y)

/-- **The essential-surjectivity hypothesis of Descent, Proposition 03DX(2) is not vacuous at an
affine chart, granted the sheaf condition of Tag 03DT there.**  There is a module on the slice of
the small étale site at `Y` which is quasi-coherent — so it satisfies the antecedent of that
hypothesis — and which is isomorphic to the module `Mᵃ` of Tag 03DU of a quasi-coherent module on
the chart's scheme, which is its conclusion.  The witness is the free module on any type, and its
quasi-coherence is unconditional.

This is an inhabitation check that compilation does not perform: a hypothesis quantifying over
every quasi-coherent module of the slice would make every theorem carrying it vacuous if no such
module ever satisfied the conclusion, and neither a build nor an
axiom check would notice.  The one hypothesis besides affineness of the chart is `hsh`, the sheaf
condition of Tag 03DT, which the module `Mᵃ` needs in order to exist at all; it is a theorem of
the source and is not proved in this tree. -/
theorem exists_quasicoherent_sliceAssociatedModule_iso
    (hY : IsAffine (chartScheme Y)) (I : Type u)
    (hsh : ∀ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent),
      Presheaf.IsSheaf ((topology B S hS F).over Y)
        (Stacks.Sites.associatedPresheaf (chartScheme Y) M
          (sliceToOver B S hS F Y))) :
    ∃ N : SheafOfModules.{u} (sliceRingSheaf B S hS F hF Y), N.IsQuasicoherentOnSite ∧
      ∃ (M : (chartScheme Y).Modules) (_ : M.IsQuasicoherent)
        (hM : Presheaf.IsSheaf ((topology B S hS F).over Y)
          (Stacks.Sites.associatedPresheaf (chartScheme Y) M
            (sliceToOver B S hS F Y))),
        Nonempty (N ≅ sliceAssociatedModule B S hS F hF Y M hM) :=
  ⟨SheafOfModules.free I, isQuasicoherentOnSite_free_slice B S hS F hF Y I,
    exists_sliceAssociatedModule_iso_free B S hS F hF Y hY I hsh⟩

end AlgebraicGeometry.Space.SmallEtale

end
