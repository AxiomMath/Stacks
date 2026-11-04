module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorGlobalPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-coherence of a tensor product of sheaves of modules on a ringed site

Stacks 03L6 asserts that each of the local module types of Stacks 03DL is inherited by a tensor
product.  This file proves the quasi-coherence clause for `SheafOfModules.IsQuasicoherentOnSite`,
the predicate of Stacks 03DL(6) phrased with the global condition of Stacks 03DE(6), and for the
tensor product of Stacks 0GMW, `Stacks.SheafOfModules.Tensor.sheafTensor`.

Each factor has a global presentation over the members of a family covering the final object
(Stacks 03DN); the objects admitting an arrow into a member of each of the two families again
cover, and over such an object both presentations restrict.  The tensor product of two globally
presented sheaves of modules is globally presented, so the restriction of the globally formed
tensor product is too, and Stacks 03DN turns that back into quasi-coherence.

## Main results

* `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite`: **the tensor
  product of two quasi-coherent sheaves of modules on a ringed site is quasi-coherent.**

## Implementation notes

The statement carries no `UnivLE` and no sheafification instance on any slice at the universe `w`
of the module sections, so nothing may be proved on a slice site at that universe — in particular
the tensor product cannot be formed there.  Everything instead happens at the raised universe
`max u v w` in which `SheafOfModules.HasGlobalPresentation` states its presentations, where
sheafification on the site and on every slice is free, and where
`max (max u v) v w = max u v w` makes the slice universe agree with the one on the whole site.

The isomorphism fed to
`Stacks.SheafOfModules.TensorRaised.hasGlobalPresentation_of_tensorIso` is assembled from the
universe lift commuting with the tensor product on the whole site, the tensor product commuting
with restriction at the raised universe, and the universe lift commuting with restriction, which
is `uliftOverIso` and is computed objectwise.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace Stacks.SheafOfModules.TensorLocalProperties

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Raising the universe of the sections commutes with restriction to a slice site, both being
computed objectwise. -/
noncomputable def uliftOverIso {R : Sheaf J RingCat.{w}} (N : SheafOfModules.{w} R) (V : C) :
    SheafOfModules.uliftForPresentation.{max u v, v, w, w, t} (N.over V) ≅
      (SheafOfModules.uliftForPresentation.{u, v, w, w, t} N).over V :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intro X Y f; ext x; rfl))

variable (J) [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Over an object on which both factors have a global presentation, so does the restriction of
their tensor product. -/
private theorem hasGlobalPresentation_tensorSheaf_over (R : Sheaf J CommRingCat.{w})
    (F G : SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J R)) (V : C)
    (hF : (F.over V).HasGlobalPresentation) (hG : (G.over V).HasGlobalPresentation) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj F).obj G).over
        V).HasGlobalPresentation := by
  have h1 : HasSheafify (J.over V) AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v} (J.over V)
  have h2 : (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
      max u v, v} (J.over V)
  have h3 : HasSheafify J AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, u} J
  have h4 : J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w, u, v} J
  have e (N : SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J R)) :=
    uliftOverIso.{u, v, w, max u v w} N V
  exact Stacks.SheafOfModules.TensorRaised.hasGlobalPresentation_of_tensorIso.{max u v, v, w}
    (R.over V) (F.over V) (G.over V) _
    (e _ ≪≫ (SheafOfModules.overFunctor.{max u v w}
      (CategoryTheory.Sheaf.toRingCat J R) V).mapIso
        (Stacks.SheafOfModules.UliftTensor.uliftTensorSheafIso.{u, v, w, max u v w} F G) ≪≫
      (Stacks.SheafOfModules.TensorRaised.tensorOverRaisedIso.{u, v, w, max u v w} R V _ _).symm ≪≫
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, max u v w, max u v w}
        (R.over V)).mapIso (e F)).app _ ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, max u v w, max u v w}
          (R.over V)).obj _).mapIso (e G)).symm)
    hF hG

/-- **Stacks Project, Tag 03L6, quasi-coherent case.** The tensor product of two quasi-coherent
sheaves of modules on a ringed site is quasi-coherent. -/
@[stacks 03L6 "quasi_coherent", ega "I 9.1.1" "more general"]
theorem tensorSheaf_isQuasicoherentOnSite (R : Sheaf J CommRingCat.{w})
    (F G : SheafOfModules.{w} (CategoryTheory.Sheaf.toRingCat J R))
    [SheafOfModules.IsQuasicoherentOnSite F] [SheafOfModules.IsQuasicoherentOnSite G] :
    SheafOfModules.IsQuasicoherentOnSite
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj F).obj G) := by
  classical
  obtain ⟨IA, UA, hUA, hA⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation
      F).1 inferInstance
  obtain ⟨IB, UB, hUB, hB⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation
      G).1 inferInstance
  let I := Σ i : IA, Σ j : IB, {V : C // Nonempty ((V ⟶ UA i) × (V ⟶ UB j))}
  let Y : I → C := fun z ↦ z.2.2.1
  have hY : J.CoversTop Y := by
    intro W
    exact J.transitive (hUA W) (Sieve.ofObjects Y W) (by
      intro V f hf
      refine J.superset_covering ?_ (hUB V)
      intro Z g hg
      obtain ⟨i, ⟨bb⟩⟩ := (Sieve.mem_ofObjects_iff UA f).mp hf
      obtain ⟨j, ⟨cc⟩⟩ := (Sieve.mem_ofObjects_iff UB g).mp hg
      exact (Sieve.mem_ofObjects_iff Y (g ≫ f)).2 ⟨⟨i, j, Z, ⟨(g ≫ bb, cc)⟩⟩, ⟨𝟙 Z⟩⟩)
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation
    _).2 ⟨I, Y, hY, fun z ↦ ?_⟩
  exact hasGlobalPresentation_tensorSheaf_over J R F G (Y z)
    (Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap F
      (Classical.choice z.2.2.2).1 (hA z.1))
    (Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap G
      (Classical.choice z.2.2.2).2 (hB z.2.1))

end Stacks.SheafOfModules.TensorLocalProperties

end
