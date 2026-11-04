module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.BoundedAbove

/-!
# Finite families of generating sections for a sheaf of modules

Finite type for a sheaf of `𝒪_X`-modules is the existence, near every point, of a finite family
of sections generating the sheaf there. This file collects the three steps that produce such a
family out of a surjection from a finite free module on an open subspace: the purely homological
observation that a cochain complex vanishing just above degree `m` surjects from its degree-`m`
term onto its degree-`m` cohomology, the translation of a surjection from a finite free module on
`X|_U` into a finite family of generating sections on the slice site over `U`, and the assembly of
such families over a covering into finite type for the sheaf itself.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_epi_to_homology_of_isZero_X_succ`: a cochain complex in
  an abelian category whose degree-`(m + 1)` term vanishes has an epimorphism from its degree-`m`
  term onto its degree-`m` cohomology.
* `AlgebraicGeometry.RingedSpace.exists_isFiniteType_generatingSections_of_epi`: a surjection
  from a finite free module on `X|_U` onto the restriction of `M` yields a finite family of
  sections generating `M` over `U`.
* `AlgebraicGeometry.RingedSpace.isFiniteType_of_forall_exists_generatingSections`: a sheaf of
  modules admitting such a family near every point is of finite type.

## Implementation notes

With `P^{m+1} = 0` the differential out of `P^m` vanishes, the inclusion of the degree-`m` cycles
into `P^m` is an isomorphism, and therefore the projection to homology becomes a map out of `P^m`
itself. Without that boundedness only the subobject of cycles surjects onto the cohomology, and a
subobject of a finite free module carries no finite family of generating sections.

Finite type is phrased in terms of `SheafOfModules.LocalGeneratorsData`, whose generators live
on the *slice site* over an open set `U`, whereas the approximation lives on the restricted
ringed space `X|_U`. The two are identified by
`TopologicalSpace.Opens.sheafOfModulesEquivOver`, and the composite of the restriction to the
slice site with that identification is `AlgebraicGeometry.RingedSpace.restrictModules` on the
nose (`AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp` is `Iso.refl`); so the unit
isomorphism of the equivalence alone carries a module restricted to `X|_U` back to the same
module on the slice site. The finite free module of rank `n` is the free module on
`ULift (Fin n)` (`StrictlyPerfect.finiteFreeIsoFree`), and
`SheafOfModules.mapFreeIso` transports free modules across the equivalence, so the generating
sections of a free module (`SheafOfModules.free.generatingSections`) can be pushed along the
epimorphism with `SheafOfModules.GeneratingSections.ofEpi`.

## References

* [Stacks Project, Lemma 20.46.12 (08DN)](https://stacks.math.columbia.edu/tag/08DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- **A cochain complex with vanishing term just above degree `m` has an epimorphism from its
degree-`m` term onto its degree-`m` cohomology.** The differential out of `P^m` lands in the zero
object, so `P^m` is the kernel of that differential, the inclusion of the degree-`m` cycles is an
isomorphism, and the projection onto homology may be precomposed with its inverse. This is purely
homological and holds in any abelian category. -/
theorem exists_epi_to_homology_of_isZero_X_succ {A : Type*} [Category A] [Abelian A]
    (P : CochainComplex A ℤ) (m : ℤ) (h : IsZero (P.X (m + 1))) :
    ∃ f : P.X m ⟶ P.homology m, Epi f := by
  have : IsIso (P.iCycles m) :=
    KernelFork.IsLimit.isIso_ι (KernelFork.ofι (P.iCycles m) (P.iCycles_d m (m + 1)))
      (P.cyclesIsKernel m (m + 1) (by simp)) (h.eq_of_tgt _ _)
  exact ⟨(asIso (P.iCycles m)).inv ≫ P.homologyπ m, inferInstance⟩

/-- **Finitely many generating sections over an open set, from a finite free module surjecting
onto the restriction.** An epimorphism from `𝒪_{X|_U}^{⊕n}` onto the restriction of `M` to the
open subspace `X|_U` is the same thing, through the equivalence between modules on the slice site
over `U` and modules on `X|_U`, as an epimorphism onto `M|_U` from the free module on
`ULift (Fin n)`; the images of the `n` tautological sections of the latter then generate `M|_U`. -/
theorem exists_isFiniteType_generatingSections_of_epi (M : OXMod.{u, u} X)
    (U : Opens X.carrier) (n : ℕ)
    (g : finiteFree (X.restrict U.isOpenEmbedding) n ⟶ (restrictModules X U).obj M)
    (hg : Epi g) :
    ∃ σ : (M.over U).GeneratingSections, σ.IsFiniteType := by
  let e : SheafOfModules.{u} ((structureSheafOfRings X).over U) ≌
      OXMod.{u, u} (X.restrict U.isOpenEmbedding) :=
    U.sheafOfModulesEquivOver (structureSheafOfRings X)
  let I := ULift.{u} (Fin n)
  let eFin : e.inverse.obj (finiteFree (X.restrict U.isOpenEmbedding) n) ≅
      SheafOfModules.free (R := (structureSheafOfRings X).over U) I :=
    e.inverse.mapIso (finiteFreeIsoFree (X.restrict U.isOpenEmbedding) n ≪≫
      SheafOfModules.mapFreeIso e.functor I (Iso.refl _)) ≪≫ (e.unitIso.app _).symm
  let eBack : e.inverse.obj ((restrictModules X U).obj M) ≅ M.over U :=
    (e.unitIso.app (M.over U)).symm
  exact ⟨(SheafOfModules.free.generatingSections I).ofEpi
    (eFin.inv ≫ e.inverse.map g ≫ eBack.hom), ⟨inferInstanceAs (Finite I)⟩⟩

/-- **A sheaf of modules generated by finitely many sections near every point is of finite
type.** The chosen neighbourhoods cover `X`, so they form the covering underlying a
`SheafOfModules.LocalGeneratorsData` whose families of generators are all finite. -/
theorem isFiniteType_of_forall_exists_generatingSections (M : OXMod.{u, u} X)
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ σ : (M.over U).GeneratingSections, σ.IsFiniteType) :
    M.IsFiniteType := by
  choose U hU σ hσ using h
  have hcov : (Opens.grothendieckTopology X.carrier).CoversTop U :=
    (Opens.coversTop_iff X.carrier U).mpr
      (IsOpenCover.mk (Opens.ext (Set.eq_univ_of_forall fun x => le_iSup U x (hU x))))
  exact { exists_localGeneratorsData :=
    ⟨{ I := X.carrier, X := U, coversTop := hcov, generators := σ },
      { isFiniteType := fun i => hσ i }⟩ }

end AlgebraicGeometry.RingedSpace

end
