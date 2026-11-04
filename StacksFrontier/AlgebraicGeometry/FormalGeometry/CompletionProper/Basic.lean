module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset
public import StacksFrontier.RingTheory.LocalCohomology.UniformCohomologyBound
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic

/-!
# Completion of coherent sheaves whose support is proper over an affine base

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `f : X ⟶ Spec A` a morphism locally of
finite type. Completing a coherent sheaf on `X` along the ideal sheaf `I · 𝒪_X` produces a
coherent adic system, and this file shows that the construction respects properness of the
support: if the support of a coherent sheaf `F` is proper over `A`, then so is the support of
the first term `F / I · F` of its completion. Consequently the completion functor of Stacks
0880 restricts to a functor

  `Coh_{support proper over A}(𝒪_X) ⥤ Coh_{support proper over A}(X, I)`,

which is the arrow of Stacks 088D and the first step of the route to Grothendieck's existence
theorem.

The reason properness is inherited is that the first term of the completion is a *quotient* of
`F`, so its support is contained in that of `F`; a closed subset of a closed subset proper over
the base is again proper over the base.

## Main definitions

* `Stacks.Algebraization.HasProperSupport` — the support of a sheaf of modules, as a closed
  subset, is proper over the base.
* `Stacks.Algebraization.CoherentModulesProperOver` and
  `Stacks.Algebraization.CoherentAdicSystemsProperOver` — the two full subcategories appearing
  in the arrow above.
* `Stacks.Algebraization.completionFunctorProperOver` — the restricted completion functor.

## Main results

* `Stacks.Algebraization.completion_hasProperSupport` — the first term of the completion of a
  coherent sheaf with support proper over the base again has support proper over the base.

## Implementation notes

The adic system is zero-indexed, as in `StacksDraft.AlgebraicGeometry.FormalGeometry`
`.CompletionFunctor.Basic`: its term at `op 0` is the quotient `F / I · F`, which is the source's
`F_1`. Since all terms of a coherent adic system have the same support, asking for properness at
`op 0` is the condition of the source.

Properness of a closed subset is expressed through the canonical *reduced* closed subscheme
structure, the subscheme of the vanishing ideal sheaf `Scheme.IdealSheafData.vanishingIdeal`;
`AlgebraicGeometry.isProperOver_of_le` then reduces to
`Scheme.IdealSheafData.inclusion_subschemeι`, which factors the smaller subscheme's immersion
through the larger one's.

That the support of a quotient is contained in the support of the sheaf is already proved, as
the `private` lemma `AlgebraicGeometry.support_subset_of_epi` of
`StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic`, and at the `X.Modules`
spelling this file needs. It is reached by the extra `import all` line rather than re-proved
here; only the proof below names it, which is the one position a private declaration reached
that way may appear in.

## References

* [Stacks Project, Tag 088D](https://stacks.math.columbia.edu/tag/088D)
* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
* [Stacks Project, Tag 0CYN](https://stacks.math.columbia.edu/tag/0CYN)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

/-- A sheaf of modules has support proper over the base when its support, regarded as a closed
subset, is proper over that base. -/
public def HasProperSupport {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) : Prop :=
  ∃ Z : Closeds X, (Z : Set X) = SheafOfModules.supp F ∧ IsProperOver f Z

/-- Coherent sheaves of modules on `X` whose support is proper over `S`. -/
public abbrev CoherentModulesProperOver {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] :=
  ObjectProperty.FullSubcategory
    (C := AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (fun F => HasProperSupport f F.obj)

/-- Coherent adic systems along `I` whose first term has support proper over `S`. -/
public abbrev CoherentAdicSystemsProperOver {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (I : X.IdealSheafData) :=
  ObjectProperty.FullSubcategory
    (C := Stacks.Coherent.CoherentAdicSystems I)
    (fun F => HasProperSupport f (F.obj.obj (op 0)))

/-- **Stacks 088D.** The first term of the completion of a coherent sheaf whose support is
proper over the base again has support proper over the base.

That term is the quotient `F / I · F`, so its support is a closed subset of the support of `F`,
and a closed subset of a closed subset proper over the base is proper over the base. -/
@[stacks 088D "proper support of the completion"]
public theorem completion_hasProperSupport
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : CoherentModulesProperOver f) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    HasProperSupport f
      (((completionFunctor X (baseIdealSheaf A I f)).obj F.obj).obj.obj (op 0)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set J := baseIdealSheaf A I f with hJ
  set Q := ((completionFunctor X J).obj F.obj).obj.obj (op 0) with hQ
  have : _root_.SheafOfModules.IsCoherent.{u} Q :=
    ((completionFunctor X J).obj F.obj).property.1 0
  have : Q.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := Q)
  obtain ⟨Z, hZF, hZproper⟩ := F.property
  have hQeq : Q = idealPowerQuotient J 1 F.obj.obj := by
    rw [hQ]
    simpa using completionFunctor_obj X J F.obj 0
  have hepiMod : Epi (C := X.Modules)
      (cokernel.π (C := X.Modules) (idealPowerMultiple J 1 F.obj.obj).ι) :=
    coequalizer.π_epi
  have hsub : _root_.SheafOfModules.supp Q ⊆ _root_.SheafOfModules.supp F.obj.obj := by
    rw [hQeq]
    exact AlgebraicGeometry.support_subset_of_epi
      (cokernel.π (C := X.Modules) (idealPowerMultiple J 1 F.obj.obj).ι)
  refine ⟨⟨_root_.SheafOfModules.supp Q, _root_.SheafOfModules.isClosed_supp Q⟩, rfl, ?_⟩
  refine isProperOver_of_le f ?_ hZproper
  show _root_.SheafOfModules.supp Q ≤ (Z : Set X)
  rw [hZF]
  exact hsub

/-- **Stacks 088D.** The completion functor of Stacks 0880, restricted to the coherent sheaves
and the coherent adic systems whose support is proper over the affine base. -/
@[stacks 088D "the functor"]
public noncomputable def completionFunctorProperOver
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    CoherentModulesProperOver f ⥤ CoherentAdicSystemsProperOver f (baseIdealSheaf A I f) :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  ObjectProperty.lift
    (fun F : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f) =>
      HasProperSupport f (F.obj.obj (op 0)))
    ((ObjectProperty.ι
      (fun F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf =>
        HasProperSupport f F.obj)) ⋙ completionFunctor X (baseIdealSheaf A I f))
    (fun F => completion_hasProperSupport A I f F)

end Stacks.Algebraization

end
