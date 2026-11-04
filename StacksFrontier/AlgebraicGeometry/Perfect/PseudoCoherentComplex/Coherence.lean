module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.LocalNullHomotopy
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak

/-!
# Coherence of the terms and the cohomology of a strictly perfect complex

On a locally Noetherian scheme every term of a strictly perfect complex is coherent, because it
is a direct summand of a finite free module, and therefore every cohomology module of the
complex is coherent, because the coherent modules form a weak Serre subcategory and the
cohomology of a complex is a cokernel of a map into a kernel.

## Main results

* `SheafOfModules.IsCoherent.stacksIsCoherent` and
  `Stacks.SheafOfModules.IsCoherent.rootIsCoherent` translate between the library's two
  coherence classes, `_root_.SheafOfModules.IsCoherent` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation` and
  `Stacks.SheafOfModules.IsCoherent` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent`.
* `CategoryTheory.ObjectProperty.prop_homology`: a weak Serre subcategory containing the terms
  of a complex contains its cohomology.
* `Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_isDirectSummandOfFiniteFree`: on a
  locally Noetherian scheme a direct summand of a finite free module is coherent.
* `Stacks.AlgebraicGeometry.PerfectCohomology.isCoherentStacks_of_iso`: coherence is invariant
  under isomorphism.
* `Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology_of_isStrictlyPerfect`: on a
  locally Noetherian scheme the cohomology modules of a strictly perfect complex are coherent.

## Implementation notes

The two coherence classes have the same two fields with the same types but do not unify, so a
value of one has to be rebuilt as a value of the other; that is all the two translations do.
They are needed because the closure theory of coherent modules
(`Stacks.SheafOfModules.isCoherent_of_mono`, `Stacks.SheafOfModules.isCoherent_sigma` and the
weak Serre instance) is stated for `Stacks.SheafOfModules.IsCoherent`, while the scheme-level
theory of [Stacks, Tag 01XZ] (`Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae` and
`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit`) is stated for the root class.
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isCoherent'` and
`isCoherent'_of_isCoherent` are the same translation for `AlgebraicGeometry.Scheme.Modules`;
the pair here is the one for a bare `SheafOfModules`, which is the spelling the strictly perfect
theory of [Stacks, Tag 08C4] uses. Merging the two classes is the dedup owed.

`CategoryTheory.ObjectProperty.prop_homology` duplicates a private lemma of
`StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic`; de-privatising that one
and deleting this is a second dedup owed.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SheafOfModules

universe u

/-! ### Translating between the two coherence classes -/

section Bridge

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {M : SheafOfModules.{u} R}

/-- A module coherent in the sense of `_root_.SheafOfModules.IsCoherent` is coherent in the
sense of `Stacks.SheafOfModules.IsCoherent`: the two classes have the same fields. -/
theorem SheafOfModules.IsCoherent.stacksIsCoherent (h : _root_.SheafOfModules.IsCoherent M) :
    Stacks.SheafOfModules.IsCoherent M :=
  ⟨h.isFiniteType, h.kernel_isFiniteType⟩

/-- A module coherent in the sense of `Stacks.SheafOfModules.IsCoherent` is coherent in the
sense of `_root_.SheafOfModules.IsCoherent`: the two classes have the same fields. -/
theorem Stacks.SheafOfModules.IsCoherent.rootIsCoherent
    (h : Stacks.SheafOfModules.IsCoherent M) : _root_.SheafOfModules.IsCoherent M :=
  ⟨h.isFiniteType, h.kernel_isFiniteType⟩

end Bridge

/-! ### The cohomology of a complex with terms in a weak Serre subcategory -/

/-- **The cohomology of a complex whose terms lie in a weak Serre subcategory lies in it too.**
The cohomology at `j` is a cokernel of a map into a kernel of a map between terms, and a weak
Serre subcategory is closed under both. -/
theorem CategoryTheory.ObjectProperty.prop_homology {A : Type*} [Category A] [Abelian A]
    (P : ObjectProperty A) [P.IsWeakSerreClass] {ι : Type*} {c : ComplexShape ι}
    (L : HomologicalComplex A c) (j : ι) [L.HasHomology j] (hL : ∀ m, P (L.X m)) :
    P (L.homology j) :=
  P.prop_of_isColimit_cokernelCofork (L.homologyIsCokernel (c.prev j) j rfl) (hL _)
    (P.prop_of_isLimit_kernelFork (L.cyclesIsKernel j (c.next j) rfl) (hL j) (hL _))

namespace Stacks.AlgebraicGeometry.PerfectCohomology

/-! ### Coherence of finite free modules and of their direct summands -/

/-- **A finite free module on a locally Noetherian scheme is coherent.** The structure sheaf is
coherent by [Stacks, Tag 01XZ], a finite free module is a finite coproduct of copies of it by
`StrictlyPerfect.finiteFreeIsoFree`, and coherent modules are closed under finite
coproducts. -/
theorem isCoherent_finiteFree (X : Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    Stacks.SheafOfModules.IsCoherent (StrictlyPerfect.finiteFree X.toRingedSpace n) := by
  have hu : Stacks.SheafOfModules.IsCoherent
      (unit (StrictlyPerfect.structureSheafOfRings X.toRingedSpace)) :=
    (CoherentTFAE.isCoherent_unit X).stacksIsCoherent
  have hc := Stacks.SheafOfModules.isCoherent_sigma
    (fun _ : ULift.{u} (Fin n) => unit (StrictlyPerfect.structureSheafOfRings X.toRingedSpace))
    fun _ => hu
  refine (Stacks.SheafOfModules.coherentModules
      (StrictlyPerfect.structureSheafOfRings X.toRingedSpace)).prop_of_iso
    (StrictlyPerfect.finiteFreeIsoFree X.toRingedSpace n ≪≫ ?_).symm hc
  exact IsColimit.coconePointUniqueUpToIso
    (isColimitFreeCofan (R := StrictlyPerfect.structureSheafOfRings X.toRingedSpace)
      (ULift.{u} (Fin n)))
    (coproductIsCoproduct
      fun _ : ULift.{u} (Fin n) => unit (StrictlyPerfect.structureSheafOfRings X.toRingedSpace))

/-- **A direct summand of a finite free module on a locally Noetherian scheme is coherent.**
The retraction exhibits it as a quotient of a finite free module, hence of finite type, and the
section exhibits it as a subobject of one, so [Stacks, Tag 01BY] (1) applies. -/
theorem isCoherent_of_isDirectSummandOfFiniteFree (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
    (hE : StrictlyPerfect.IsDirectSummandOfFiniteFree E) :
    Stacks.SheafOfModules.IsCoherent E := by
  obtain ⟨n, ⟨ρ⟩⟩ := (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract E).mp hE
  have hfree := isCoherent_finiteFree X n
  have hsm : IsSplitMono ρ.i := IsSplitMono.mk' ⟨ρ.r, ρ.retract⟩
  have hse : IsSplitEpi ρ.r := IsSplitEpi.mk' ⟨ρ.i, ρ.retract⟩
  have : Mono ρ.i := IsSplitMono.mono ρ.i (hf := hsm)
  have : Epi ρ.r := IsSplitEpi.epi ρ.r (hf := hse)
  have : E.IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_epi
      (R := StrictlyPerfect.structureSheafOfRings X.toRingedSpace) ρ.r hfree.isFiniteType
  exact Stacks.SheafOfModules.isCoherent_of_mono
    (M := StrictlyPerfect.finiteFree X.toRingedSpace n) ρ.i

/-- Coherence in the sense of `Stacks.SheafOfModules.IsCoherent` is invariant under
isomorphism, with the hypothesis explicit. -/
theorem isCoherentStacks_of_iso {Y : Type u} [TopologicalSpace Y]
    {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}} {M N : SheafOfModules.{u} R}
    (e : M ≅ N) (h : Stacks.SheafOfModules.IsCoherent M) :
    Stacks.SheafOfModules.IsCoherent N :=
  (Stacks.SheafOfModules.coherentModules R).prop_of_iso e h

/-! ### Coherence of the cohomology of a strictly perfect complex -/

/-- **The cohomology modules of a strictly perfect complex on a locally Noetherian scheme are
coherent.** Its terms are coherent by
`Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_isDirectSummandOfFiniteFree`, and
coherent modules form a weak Serre subcategory. -/
theorem isCoherent_homology_of_isStrictlyPerfect (X : Scheme.{u}) [IsLocallyNoetherian X]
    (P : CochainComplex (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) ℤ)
    (hP : StrictlyPerfect.IsStrictlyPerfect P) (n : ℤ) :
    Stacks.SheafOfModules.IsCoherent (P.homology n) :=
  ObjectProperty.prop_homology
    (fun M : SheafOfModules.{u} (StrictlyPerfect.structureSheafOfRings X.toRingedSpace) =>
      Stacks.SheafOfModules.IsCoherent M) P n fun m =>
      isCoherent_of_isDirectSummandOfFiniteFree X (P.X m) (hP.directSummand m)

end Stacks.AlgebraicGeometry.PerfectCohomology

end
