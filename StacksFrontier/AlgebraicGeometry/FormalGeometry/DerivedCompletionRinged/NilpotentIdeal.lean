module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Reflection
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived completion along a sheaf of ideals with nilpotent sections

Let `(𝒞, 𝒪)` be a ringed site and `ℐ ⊂ 𝒪` a sheaf of ideals all of whose local sections are
nilpotent. Then every object of `D(𝒪)` is derived complete along `ℐ`, the identity functor is a
derived completion functor, and the inclusion `D_comp(𝒪) ⥤ D(𝒪)` has a left adjoint. That last
conclusion is the conclusion of [Stacks, Tag 099F], here under the extra hypothesis that the
sections of `ℐ` are nilpotent.

This generalizes `AlgebraicGeometry.RingedSite.isDerivedComplete_of_forall_eq_zero` and
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_forall_eq_zero` of
`Reflection.lean`, which are the case of a sheaf of ideals whose sections vanish; a zero section
is nilpotent.

## Main results

* `AlgebraicGeometry.RingedSite.isDerivedComplete_of_forall_isNilpotent`: every object of `D(𝒪)`
  is derived complete along a sheaf of ideals with nilpotent local sections.
* `AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete_of_forall_isNilpotent`:
  the conclusion of [Stacks, Tag 099F] for such a sheaf of ideals, with the identity as left
  adjoint.

## Implementation notes

The predicate `AlgebraicGeometry.RingedSite.IsDerivedComplete` of [Stacks, Tag 0999] asks, for
every object `U` of the site and every section `g ∈ ℐ(U)`, that the Milnor difference map of
multiplication by `g` be invertible on the countable power of `K|_U`. The input available for
that is `isDerivedCompleteAt_of_isNilpotent`, which asks the scalar to be nilpotent in the
centre of the slice category. Multiplication by `g` has `n`-th power multiplication by `gⁿ`,
by `Stacks.SheafOfModules.terminalSectionToEnd_pow_apply`, so `gⁿ = 0` makes it nilpotent —
which is exactly the hypothesis here, and is why nilpotence rather than vanishing is the natural
condition. The rest of the proof is the slice-site bookkeeping of
`AlgebraicGeometry.RingedSite.isDerivedComplete_of_forall_eq_zero`, which this statement
subsumes.

The finite-type hypothesis is carried in
`isRightAdjoint_ι_isDerivedComplete_of_isFiniteType_of_forall_isNilpotent` even though the proof
does not use it. [Stacks, Tag 099F] itself, for an arbitrary sheaf of ideals of finite type and
at the universes `RingedSite.{u, u, u}`, is
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete`; the statements here are at the
independent universes `RingedSite.{u, v, max u v}` and need no finite-type hypothesis at all.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u v

namespace Stacks.SheafOfModules

universe w

/-- Multiplication by `fⁿ` over a terminal object is the `n`-th power of multiplication by
`f`. -/
theorem terminalSectionToEnd_pow {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [∀ U, IsMulCommutative (R.obj.obj U)]
    (T : C) (hT : IsTerminal T) (f : R.obj.obj (op T)) (n : ℕ) :
    terminalSectionToEnd.{v, u, w, w} R T hT (f ^ n) =
      terminalSectionToEnd.{v, u, w, w} R T hT f ^ n := by
  ext M U x
  simp only [CatCenter.app]
  rw [terminalSectionToEnd_apply, terminalSectionToEnd_pow_apply, map_pow]

/-- Multiplication by a nilpotent section over a terminal object is a nilpotent endomorphism of
the identity functor. -/
theorem isNilpotent_terminalSectionToEnd {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [∀ U, IsMulCommutative (R.obj.obj U)] (T : C) (hT : IsTerminal T)
    {f : R.obj.obj (op T)} (hf : IsNilpotent f) :
    IsNilpotent (terminalSectionToEnd.{v, u, w, w} R T hT f) := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by rw [← terminalSectionToEnd_pow, hn, terminalSectionToEnd_zero]⟩

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, v, max u v})
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **Every object is derived complete along a sheaf of ideals with nilpotent sections.** The
scalar whose Milnor difference map has to be invertible is multiplication by a local section of
the sheaf of ideals; a nilpotent section gives a nilpotent scalar, because the `n`-th power of
multiplication by `g` is multiplication by `gⁿ`. -/
theorem isDerivedComplete_of_forall_isNilpotent
    (hI : ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)),
      f ∈ I.toSubmodule.obj (op U) → IsNilpotent f)
    (K : DerivedCategory
      (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    IsDerivedComplete.{u, v, max u v, max u v} X I K := by
  intro V f hf
  let RV := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over V
  let A := SheafOfModules.{max u v} RV
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
  let : ∀ W : (Over V)ᵒᵖ, IsMulCommutative (RV.obj.obj W) := fun W ↦ by
    change IsMulCommutative (X.O.obj.obj (op W.unop.left))
    infer_instance
  have hLim : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have hColim : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  have hProd : HasProductsOfShape ℕ (DerivedCategory A) :=
    hasProductsOfShape_nat_derivedCategory_over.{u, v, max u v} X V
  refine ⟨inferInstance, hLim, hColim, hProd, ?_⟩
  obtain ⟨n, hn⟩ := Stacks.SheafOfModules.isNilpotent_terminalSectionToEnd
    (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over V) (Over.mk (𝟙 V)) Over.mkIdTerminal
    (hI V f hf)
  refine isDerivedCompleteAt_of_isNilpotent ⟨n, ?_⟩
  rw [smul_pow, one_pow, hn, zero_smul]

/-- **The inclusion `D_comp(𝒪) ⥤ D(𝒪)` has a left adjoint when the local sections of `ℐ` are
nilpotent.** Every object is then derived complete, so the identity functor together with the
identity natural transformation is a derived completion functor.

This is the conclusion of [Stacks, Tag 099B], under a hypothesis that is not the source's. The
source asks that `ℐ` be the ideal sheaf generated by finitely many global sections
`f_1, …, f_r`; that generation relation is *not* assumed here, so in that direction the
statement is more general than the tag, and it is restricted in the other direction by the
nilpotence of the sections. The explicit formula the tag also gives for the left adjoint,
`K^∧ = R𝑆heafHom_𝒪(Č(f), K)`, is constructed as
`AlgebraicGeometry.RingedSite.completionFunctor` and
`AlgebraicGeometry.RingedSite.completionUnit` in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/Completion.lean` and is
proved to be that left adjoint — *under* the tag's generation hypothesis — in
`CompletionIdempotent.lean`. Under the nilpotence hypothesis of this statement the left adjoint
is the identity, which is not that formula. -/
@[stacks 099B "the conclusion — the inclusion `D_comp(𝒪) ⥤ D(𝒪)` has a left adjoint — for a
  sheaf of ideals all of whose local sections are nilpotent, where that left adjoint is the
  identity. The source's hypothesis that `ℐ` be generated by finitely many global sections is
  not assumed; with that hypothesis the tag, including its Čech formula for the left adjoint,
  is carried by `CompletionIdempotent.lean`"]
theorem isRightAdjoint_ι_isDerivedComplete_of_forall_isNilpotent
    (hI : ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)),
      f ∈ I.toSubmodule.obj (op U) → IsNilpotent f) :
    (ObjectProperty.ι (IsDerivedComplete.{u, v, max u v, max u v} X I)).IsRightAdjoint :=
  isRightAdjoint_ι_isDerivedComplete_of_completionFunctor X I
    (𝟙 (𝟭 (DerivedCategory
      (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))))
    (fun _ ↦ isDerivedComplete_of_forall_isNilpotent X I hI _)
    (fun K _ ↦ by simpa using (inferInstance : IsIso (𝟙 K)))
    (fun _ ↦ rfl)

/-- **The conclusion of [Stacks, Tag 099F] for a sheaf of ideals of finite type whose local
sections are all nilpotent.** There every object of `D(𝒪)` is derived complete, so the identity
functor is a derived completion functor and the inclusion of the derived-complete objects has a
left adjoint. The tag, for an arbitrary sheaf of ideals of finite type, is
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete` of `FiniteTypeReflector.lean`. -/
theorem isRightAdjoint_ι_isDerivedComplete_of_isFiniteType_of_forall_isNilpotent
    [I.toSheafOfModules.IsFiniteType]
    (hI : ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)),
      f ∈ I.toSubmodule.obj (op U) → IsNilpotent f) :
    (ObjectProperty.ι (IsDerivedComplete.{u, v, max u v, max u v} X I)).IsRightAdjoint :=
  isRightAdjoint_ι_isDerivedComplete_of_forall_isNilpotent X I hI

end AlgebraicGeometry.RingedSite

end
