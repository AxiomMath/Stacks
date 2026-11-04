module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace

/-!
# Strictly perfect complexes on a ringed space are K-flat

A strictly perfect complex of `O_X`-modules on a ringed space is bounded and has every term a
direct summand of a finite free module (Tag 08C4).  Both clauses of K-flatness via Tag 06YQ are
therefore available: the complex is bounded above, and each of its terms is flat.  This file
proves the flatness of the terms and assembles the two into K-flatness.

## Main results

* `presheafIsFlat_of_isDirectSummandOfFiniteFree`: a direct summand of a finite free
  `O_X`-module is flat as a *presheaf* of modules.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isFlat_of_isDirectSummandOfFiniteFree`: it is
  flat as a *sheaf* of modules.
* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect`: a strictly
  perfect complex of `O_X`-modules is K-flat.

## Implementation notes

Flatness of a direct summand `M` of `O_X^{⊕ n}` is proved objectwise and then carried to the sheaf
level, which is the Tag 03ES/03ET route already used for `j_{U!}O_U` in this development's treatment
of Stacks Tag 03EX.  Objectwise, `M(U)` is a retract of `O_X(U)^n` by the image of the retract under
the sections functor, and `Module.Flat.of_retract` applies.

Two spellings of the ring of sections over `U` meet here and neither one can be left to
instance search.  `StrictlyPerfect.structureSheafOfRings X` is a `def`, so
`(structureSheafOfRings X).obj.obj U` does not unfold at `instances` transparency and no
`CommSemiring` is found for it, which is what `Module.Flat` needs; whereas the `Module`
instance on a module of sections is `ModuleCat.isModule` seated at exactly that spelling, so
writing the ring as `ringPresheaf X.presheaf` instead loses the `Module` instance.  The sections
functor is therefore introduced with its codomain *ascribed* to
`ModuleCat ((ringPresheaf X.presheaf).obj U)`: an ascription is a defeq check at default
transparency, where the two spellings do agree, and from then on both instances are found at
the one spelling the statement is written in.  Its additivity has to be passed by hand for the same
reason — the ascription hides the composite from instance search.

Passing from the presheaf to the sheaf uses
`Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification` at the identity map of rings, whose
locally injective and locally surjective hypotheses are the identity being injective and surjective,
applied to `(forget ⋙ restrictScalars) M` rather than to `M.val`.  That object is the one the
sheafification counit lands on, so the counit's component at `M` is already the comparison
isomorphism, and no separate identification of `restrictScalars` along the identity is needed.
Flatness is then transported along it by
`Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor` together with
`(exactFunctor _ _).prop_of_iso`, as in Tag 06YS.  The two directions of that `Iff` are applied as
terms rather than rewritten: `rw` synthesizes the instance arguments of
`AlgebraicGeometry.SheafOfModules.IsFlat` afresh and then fails to match the hypothesis.

Boundedness of a strictly perfect complex is recorded in `IsStrictlyPerfect` as finiteness of
the set of degrees with a nonzero term; `Set.Finite.bddAbove` turns that into the
`CochainComplex.IsStrictlyLE` bound that Tag 06YQ asks for.

Complexes are typed at `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X` rather than at
`StrictlyPerfect.OXMod X`.  The two are the same type by `rfl`, but the instance arguments of
`Stacks.SheafOfModules.Tensor.sheafTensor` are keyed on
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, and a binder given at the other spelling makes
instance search run before the two are unified.  Going the other way costs nothing, so
`IsStrictlyPerfect` and the summand hypotheses are consumed at this spelling.

## References

* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 08C5](https://stacks.math.columbia.edu/tag/08C5)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 03ES](https://stacks.math.columbia.edu/tag/03ES)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

universe u

/-- **A direct summand of a finite free `O_X`-module is flat as a presheaf of modules.**
Over each open `U` the sections `M(U)` are a retract of `O_X(U)^n`, because the retract
exhibiting `M` as a summand of `O_X^{⊕ n}` is carried to one by the functor taking sections
over `U`, and `O_X(U)^n` is free, hence flat.  Flatness of a presheaf of modules is this
objectwise condition, by Tag 03ES. -/
theorem presheafIsFlat_of_isDirectSummandOfFiniteFree {X : RingedSpace.{u, u}}
    (M : OXMod.{u, u} X) (hM : IsDirectSummandOfFiniteFree M) :
    AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat (O := X.presheaf) M.val := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract M).mp hM
  apply AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat
  intro U
  let G := SheafOfModules.forget (structureSheafOfRings X) ⋙
    PresheafOfModules.evaluation (structureSheafOfRings X).obj U
  let F : OXMod.{u, u} X ⥤ ModuleCat.{u}
      ((AlgebraicGeometry.SheafOfModules.ringPresheaf X.presheaf).obj U) := G
  have hadd : F.Additive := inferInstanceAs G.Additive
  let e : F.obj (finiteFree X n) ≅
      ModuleCat.of ((AlgebraicGeometry.SheafOfModules.ringPresheaf X.presheaf).obj U)
        (Fin n → ((AlgebraicGeometry.SheafOfModules.ringPresheaf X.presheaf).obj U)) :=
    F.mapBiproduct (fun _ : Fin n => structureModule X) ≪≫ ModuleCat.biproductIsoPi _
  have hfree : Module.Flat ((AlgebraicGeometry.SheafOfModules.ringPresheaf X.presheaf).obj U)
      (F.obj (finiteFree X n)) := Module.Flat.of_linearEquiv e.toLinearEquiv
  exact Module.Flat.of_retract (F.map ρ.i).hom (F.map ρ.r).hom
    (congrArg ModuleCat.Hom.hom (ρ.map F).retract)

/-- **A direct summand of a finite free `O_X`-module is flat as a sheaf of modules.**  It is
flat as a presheaf of modules, and sheafification along the identity map of rings preserves
flatness by Tag 03ET; the sheafification counit identifies the result with the module one
started from. -/
theorem isFlat_of_isDirectSummandOfFiniteFree {X : RingedSpace.{u, u}}
    (M : OXMod.{u, u} X) (hM : IsDirectSummandOfFiniteFree M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M := by
  let α := AlgebraicGeometry.SheafOfModules.associatedRingMap
    (Opens.grothendieckTopology X.carrier) (𝟙 X.sheaf.obj)
  have hinj : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier) α :=
    Presheaf.isLocallyInjective_of_injective _ α fun _ _ _ h => h
  have hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) α :=
    Presheaf.isLocallySurjective_of_surjective _ α fun _ x => ⟨x, rfl⟩
  let F' := (SheafOfModules.forget
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) ⋙
    PresheafOfModules.restrictScalars α).obj M
  have hsheaf := Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification
    (Opens.grothendieckTopology X.carrier) (O := X.sheaf.obj) (Osharp := X.sheaf)
    α F' (presheafIsFlat_of_isDirectSummandOfFiniteFree M hM)
  let ε : (PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)
      α).obj F' ≅ M :=
    (asIso (PresheafOfModules.sheafificationAdjunction α).counit).app M
  have hiff := Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u}
    X.sheaf
  exact (hiff M).2 ((exactFunctor _ _).prop_of_iso
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).flip.mapIso ε)
    ((hiff _).1 hsheaf))

/-- **A strictly perfect complex of `O_X`-modules on a ringed space is K-flat.**  Only finitely
many terms are nonzero, so the complex is bounded above, and every term is a direct summand of
a finite free module, hence flat; Tag 06YQ on a ringed space concludes. -/
theorem kFlat_of_isStrictlyPerfect {X : RingedSpace.{u, u}}
    (K : CochainComplex (Modules X) ℤ) (hK : IsStrictlyPerfect K) : KFlat X K := by
  obtain ⟨n, hn⟩ := hK.bounded.bddAbove
  refine kFlat_of_boundedAbove_of_flat X K ⟨n, ?_⟩
    (fun i => isFlat_of_isDirectSummandOfFiniteFree (K.X i) (hK.directSummand i))
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_contra hz
  exact absurd (hn hz) (by omega)

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

end
