module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactObjects.PerfectObjectsOnARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroUnitAtTerminal

/-!
# Compactness of the extension by zero of the structure sheaf, with the reduction discharged

Let `X` be a ringed space whose underlying topological space is quasi-compact, has a basis of
quasi-compact opens and has quasi-compact intersections of quasi-compact opens. The two clauses
of Stacks 09J7, `Stacks.Cohomology.RingedSpaceCompact.isCompactObject_of_isPerfect` and
`Stacks.Cohomology.RingedSpaceCompact.hom_coproduct_bijective_of_isPerfect`, carry a hypothesis
`hreduce` standing in for the first paragraph of the source's proof: a functor `T` commuting
with the relevant direct sums together with a natural additive bijection
`Hom(K, N) ≃+ Hom(j_{⊤!}O_⊤, T N)`.

This file discharges `hreduce` outright at `K = j_{⊤!}O_⊤[0]`, with `T` the identity functor
and the bijection the identity, for each of the two spellings of `j_{⊤!}O_⊤` that the two
clauses use. What is left of each clause's hypotheses is then only hypotheses of the source: in
clause (b) perfectness of `K` and the cohomological-dimension bound, and in clause (a)
perfectness of `K` and the boundedness below of `⨁ Mᵢ` — the latter being, verbatim, the
hypothesis the source states in clause (a) and which the general form charges to `hreduce`.

## Why this matters for the stand-in

`hreduce` is satisfiable by `K = 0` with `T = 0`, so the general statements are weak rather
than vacuous, and neither `#print axioms` nor a build can see the difference. The declarations
below are the
positive test: they exhibit `hreduce` inhabited at a **nonzero** `K` by a **nonzero** `T`,
using nothing beyond the ringed space itself. They also show what the identity witness costs:
`T = 𝟭` forces the source object of the bijection to be `K` itself, so the two statements below
are special cases of the tag rather than instances of its content, which is why neither carries
the project tag.

The identity witness is not available without the identifications of
`StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroUnitAtTerminal`
being genuine isomorphisms rather than equalities: the two spellings of `j_{⊤!}O_⊤` are not
definitionally equal to each other, nor either of them to `O[0]`, so each clause needs its own
source object, which is why both statements below are stated and why the general discharge of
`hreduce` at an arbitrary perfect `K` needs those isomorphisms and not a `rfl`.

## Main results

* `Stacks.Cohomology.RingedSpaceCompact.isCompactObject_derivedPullbackUnitTop`: clause (b) at
  `K = j_{⊤!}O_⊤[0]` in the pullback spelling, with `hreduce` discharged.
* `Stacks.Cohomology.RingedSpaceCompact.hom_coproduct_bijective_derivedExtensionByZeroUnitTop`:
  clause (a) at `K = j_{⊤!}O_⊤[0]` in the `ULift`ed spelling, with `hreduce` discharged down to
  the source's own boundedness hypothesis.

## No tag is carried

Both statements below are the tag's clauses at one particular `K`, so neither states the tag and
neither is registered for it. The two attribute sites of Stacks 09J7 are untouched.

## References

* [Stacks Project, Tag 09J7](https://stacks.math.columbia.edu/tag/09J7)
* [Stacks Project, Tag 09JC](https://stacks.math.columbia.edu/tag/09JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

namespace Stacks.Cohomology.RingedSpaceCompact

universe u i

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- `j_{⊤!}O_⊤[0]` in the pullback spelling, the source object of clause (b) of Stacks 09JC. -/
noncomputable abbrev derivedPullbackUnitTop :
    DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)) :=
  (DerivedCategory.singleFunctor
    (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)) 0).obj
      ((SheafOfModules.pullback.{u} (F := Over.forget (⊤ : (RingedSpace.ringedSite X).C))
        (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O).over
          (⊤ : (RingedSpace.ringedSite X).C)))).obj
            (SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O).over
                (⊤ : (RingedSpace.ringedSite X).C))))

/-- `j_{⊤!}O_⊤[0]` in the `ULift`ed spelling, the source object of clause (a) of Stacks 09JC. -/
noncomputable abbrev derivedExtensionByZeroUnitTop :
    DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)) :=
  (DerivedCategory.singleFunctor
    (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)) 0).obj
      (Stacks.Sites.OverModules.extensionByZeroUnit.{u, u, u, u}
        (RingedSpace.ringedSite X).J
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)
        (⊤ : (RingedSpace.ringedSite X).C))

/-- **Stacks 09J7 (b) at `K = j_{⊤!}O_⊤[0]`, with the reduction discharged.** The hypothesis
`hreduce` of `isCompactObject_of_isPerfect` is met by the identity functor and the identity
bijection, because at this `K` the source object of the bijection *is* `K`. Nothing is assumed
beyond the three topological hypotheses of the tag, perfectness of `K` and the
cohomological-dimension bound.

This is not the tag: it is the tag's clause (b) at one object. Its purpose is to witness that
`hreduce` is inhabited at a nonzero `K` by a nonzero `T`. -/
theorem isCompactObject_derivedPullbackUnitTop [CompactSpace X.carrier]
    (hBasis : PrespectralSpace X.carrier)
    (hInter : QuasiSeparatedSpace X.carrier)
    (hK : (RingedSpace.ringedSite X).IsPerfect (derivedPullbackUnitTop X))
    (hcd : ∃ d : ℤ, ∀ (p : ℕ)
      (F : SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)),
      d < (p : ℤ) →
        IsZero (Hgroup
          (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O) ⊤ p F)) :
    IsCompactObject.{u} (derivedPullbackUnitTop X) :=
  Stacks.Cohomology.RingedSpaceCompact.isCompactObject_of_isPerfect X hBasis hInter _ hK hcd
    (fun _ => ⟨Functor.id _, fun _ => inferInstance, fun _ => AddEquiv.refl _, fun _ _ => rfl⟩)

/-- **Stacks 09J7 (a) at `K = j_{⊤!}O_⊤[0]`, with the reduction discharged.** As for clause (b),
the identity functor and the identity bijection meet `hreduce`; the one component of `hreduce`
that the identity functor does not make trivial is the boundedness below of `T (⨁ Mᵢ)`, which
for `T = 𝟭` is the boundedness below of `⨁ Mᵢ` — the hypothesis the source itself states in
clause (a).

This is not the tag: it is the tag's clause (a) at one object. -/
theorem hom_coproduct_bijective_derivedExtensionByZeroUnitTop [CompactSpace X.carrier]
    (hBasis : PrespectralSpace X.carrier)
    (hInter : QuasiSeparatedSpace X.carrier)
    (hK : (RingedSpace.ringedSite X).IsPerfect (derivedExtensionByZeroUnitTop X))
    {I : Type i} [DecidableEq I]
    (M : I → DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O)))
    [HasCoproduct M]
    (hplus : (DerivedCategory.TStructure.t
      (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (RingedSpace.ringedSite X).O))).plus (∐ M)) :
    Function.Bijective
      (DirectSum.toAddMonoid fun j =>
        Preadditive.rightComp (derivedExtensionByZeroUnitTop X) (Limits.Sigma.ι M j)) :=
  Stacks.Cohomology.RingedSpaceCompact.hom_coproduct_bijective_of_isPerfect X hBasis hInter _ hK M
    (fun _ => ⟨Functor.id _, inferInstance, hplus, fun _ => AddEquiv.refl _, fun _ _ => rfl⟩)

end Stacks.Cohomology.RingedSpaceCompact

end
