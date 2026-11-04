module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBase

/-!
# Cohomology on a scheme over a ring is a right derived functor into modules over that ring

`StacksFrontier/RingTheory/LocalCohomology/HigherDegree/CohomologyOverBase.lean` defines the
left-hand side of Stacks 0DWR in positive degrees,
`Stacks.LocalCohomology.cohomologyOverBase A f F p`, as the `p`-th right derived functor of
global sections of `F` on `X` — a module over `Γ(X, ⊤)` — followed by restriction of scalars to
`A`. That is the order in which the source writes it, but it is the wrong order for comparing
the object with anything: a comparison produced one derived functor at a time is a map of
`Γ(X, ⊤)`-modules, and every statement that Stacks 0DWR has to be compared with — local
cohomology, Čech cohomology of the standard covering, the localization triangle — is a
statement about `A`-modules.

This file reverses the order. Restriction of scalars is exact, so it may be pulled out of a
right derived functor, and `cohomologyOverBase` is therefore the `p`-th right derived functor of
`A`-linear global sections

`Stacks.LocalCohomology.sectionsOverBase :`
`  SheafOfModules.{max u v} X.ringCatSheaf ⥤ ModuleCat.{max u v} A`,

a functor into `A`-modules. Consequences used immediately: the left-hand side of Stacks 0DWR is
functorial in the sheaf through `A`-linear maps, and an isomorphism of sheaves of modules
induces an `A`-linear equivalence of its cohomology. The second one removes the hypothesis
`Nonempty (F ≅ M̃|U)` of Stacks 0DWR from the problem: the comparison need only be proved for
`F = M̃|U` itself.

## Main definitions

* `Stacks.LocalCohomology.baseScalars` — the structure map `A ⟶ Γ(X, ⊤)` of a scheme over `A`.
* `Stacks.LocalCohomology.sectionsOverBase` — **`A`-linear global sections** on a scheme over
  `A`.
* `Stacks.LocalCohomology.cohomologyOverBaseFunctor` — the `p`-th right derived functor of
  `A`-linear global sections, as a functor into `ModuleCat A`.
* `Stacks.LocalCohomology.cohomologyOverBaseIsoRightDerived` — **the left-hand side of
  Stacks 0DWR is that right derived functor**, objectwise.
* `Stacks.LocalCohomology.cohomologyOverBaseLinearEquivOfIso` — isomorphic sheaves of modules
  have `A`-linearly isomorphic cohomology over the base.

## Main results

* `Stacks.LocalCohomology.sectionsOverBase_complementZeroLocus` and
  `Stacks.LocalCohomology.cohomologyOverBaseFunctor_complementZeroLocus` — **at the structure
  morphism of `U = Spec A \ V(I)` these are the development's own
  `Stacks.LocalCohomology.complementGlobalSectionsFunctor` and its right derived functors**, by
  definition. So nothing here forks that functor, and the comparison of
  `StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle/Sections.lean` between it and
  `Stacks.LocalCohomology.sectionsOnAffineComplement` applies to the left-hand side of
  Stacks 0DWR.
* `Stacks.LocalCohomology.nonempty_cohomologyOverBase_iso_of_complementTilde` — **the
  comparison of Stacks 0DWR for an arbitrary `F` follows from the comparison for the restricted
  associated sheaf.** This is a reduction, not the comparison: the hypothesis is the statement
  of Stacks 0DWR at `F = M̃|U`.

## Implementation notes

The exactness of restriction of scalars is `restrictScalars_preservesHomology` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage/SheafifiedCohomologyPresheaf.lean`,
which is stated with the module universe independent of the ring universe, and the natural
comparison is `CategoryTheory.Functor.rightDerivedCompIso` of
`StacksFrontier/CategoryTheory/Abelian/RightDerivedPostcompose.lean`.

Both of those take `Additive` and `PreservesHomology` as instance arguments, and Mathlib's
`Additive` instance for `ModuleCat.restrictScalars` is *not* found at the point of use. The
reason is not the universes: `CategoryTheory.Functor.rightDerivedCompIso` takes its target
category abelian, so the `Preadditive` instance in the `Additive` goal arrives as
`CategoryTheory.Abelian.toPreadditive` rather than as `ModuleCat`'s own, and the two do not
match at instance-reducible transparency. The comparison is therefore assembled with the two
functors passed explicitly and the `Additive` instance for restriction of scalars given as the
term `⟨by intros; rfl⟩` — which is also the instance the definition of
`Stacks.LocalCohomology.cohomologyOverBase` uses for evaluation. Since
`CategoryTheory.Functor.Additive` is a `Prop`-valued class, proof irrelevance makes that choice
immaterial, and `Stacks.LocalCohomology.cohomologyOverBaseIsoRightDerived` is a `.symm` of the
comparison with no transport at all.

The injective resolutions needed by the right derived functor are
`Stacks.LargeModuleUniverse.enoughInjectives`, an instance at every module universe above the
universe of the space; nothing here is restricted to `v = u`.

No Stacks tag attribute is placed here: this is the left-hand side of Stacks 0DWR read as a
derived functor, not a covering set for the tag.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The structure map `A ⟶ Γ(X, ⊤)` of a scheme over `A`**: the inverse of the
`Γ`–`Spec` adjunction isomorphism followed by `f` on global sections. This is the ring
homomorphism along which `Stacks.LocalCohomology.cohomologyOverBase` restricts scalars. -/
abbrev baseScalars : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom

/-- **`A`-linear global sections on a scheme over `A`**: sections over `⊤` of a sheaf of
modules on `X`, with scalars restricted to `A` along `Stacks.LocalCohomology.baseScalars`.

The module universe `max u v` may exceed the universe `u` of `X`, as it does in Stacks 0DWR. -/
def sectionsOverBase : SheafOfModules.{max u v} X.ringCatSheaf ⥤ ModuleCat.{max u v} A :=
  SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)) ⋙
    ModuleCat.restrictScalars (baseScalars A f)

/-- Evaluation of a sheaf of modules at the top open is additive; this is the instance the
definition of `Stacks.LocalCohomology.cohomologyOverBase` uses. -/
instance evaluationTop_additive :
    (SheafOfModules.evaluation.{max u v} X.ringCatSheaf (op (⊤ : X.Opens))).Additive :=
  ⟨by intros; rfl⟩

/-- `A`-linear global sections is an additive functor: both factors are. -/
instance sectionsOverBase_additive : (sectionsOverBase.{u, v} A f).Additive :=
  ⟨by intros; rfl⟩

/-- **The `p`-th right derived functor of `A`-linear global sections**, as a functor into
`A`-modules. -/
def cohomologyOverBaseFunctor (p : ℕ) :
    SheafOfModules.{max u v} X.ringCatSheaf ⥤ ModuleCat.{max u v} A :=
  (sectionsOverBase.{u, v} A f).rightDerived p

/-- **Restriction of scalars to `A` comes out of the derived functor of global sections.**
Restriction of scalars is exact, so the right derived functors of `A`-linear global sections
are the right derived functors of global sections with scalars restricted afterwards. -/
def rightDerivedSectionsOverBaseIso (p : ℕ) :
    cohomologyOverBaseFunctor.{u, v} A f p ≅
      (SheafOfModules.evaluation.{max u v} X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived p ⋙
        ModuleCat.restrictScalars (baseScalars A f) :=
  @Functor.rightDerivedCompIso _ _ _ _ _ _ _ _ _ _
    (SheafOfModules.evaluation.{max u v} X.ringCatSheaf (op (⊤ : X.Opens))) inferInstance
    (ModuleCat.restrictScalars.{max u v} (baseScalars A f)) ⟨by intros; rfl⟩
    (restrictScalars_preservesHomology _) p

/-- **The left-hand side of Stacks 0DWR is the right derived functor of `A`-linear global
sections.** `Stacks.LocalCohomology.cohomologyOverBase` derives global sections and then
restricts scalars; this identifies it with the derived functor of the composite, which is a
functor into `A`-modules and so can be compared with local cohomology `A`-linearly. -/
def cohomologyOverBaseIsoRightDerived (F : SheafOfModules.{max u v} X.ringCatSheaf) (p : ℕ) :
    cohomologyOverBase.{u, v} A f F p ≅ (cohomologyOverBaseFunctor.{u, v} A f p).obj F :=
  ((rightDerivedSectionsOverBaseIso.{u, v} A f p).app F).symm

/-- Cohomology over the base is functorial in the sheaf of modules, through `A`-linear maps:
an isomorphism `F ≅ G` induces an isomorphism of `A`-modules. -/
def cohomologyOverBaseIsoOfIso {F G : SheafOfModules.{max u v} X.ringCatSheaf} (e : F ≅ G)
    (p : ℕ) : cohomologyOverBase.{u, v} A f F p ≅ cohomologyOverBase.{u, v} A f G p :=
  cohomologyOverBaseIsoRightDerived A f F p ≪≫
    (cohomologyOverBaseFunctor.{u, v} A f p).mapIso e ≪≫
    (cohomologyOverBaseIsoRightDerived A f G p).symm

/-- **Isomorphic sheaves of modules have `A`-linearly isomorphic cohomology over the base.**
This is `Stacks.LocalCohomology.cohomologyOverBaseIsoOfIso` read as a linear equivalence, which
is the form in which Stacks 0DWR states its conclusion. -/
def cohomologyOverBaseLinearEquivOfIso {F G : SheafOfModules.{max u v} X.ringCatSheaf}
    (e : F ≅ G) (p : ℕ) :
    cohomologyOverBase.{u, v} A f F p ≃ₗ[A] cohomologyOverBase.{u, v} A f G p :=
  (cohomologyOverBaseIsoOfIso A f e p).toLinearEquiv

variable {A}

/-! ### The complement of a zero locus: the functor already in the development -/

/-- `Stacks.LocalCohomology.complementGlobalSectionsFunctor` is additive. Its two factors are,
and this is the instance the right derived functors below need. -/
instance complementGlobalSectionsFunctor_additive (A : Type u) [CommRing A] (I : Ideal A) :
    (complementGlobalSectionsFunctor.{u, v} A I).Additive :=
  ⟨by intros; rfl⟩

/-- **`A`-linear global sections on a general scheme over `A`, at the structure morphism of
`U = Spec A \ V(I)`, is the development's own
`Stacks.LocalCohomology.complementGlobalSectionsFunctor`** — by definition, at a free module
universe. The spelling of the structure map here uses `Scheme.Hom.appLE ⊤ ⊤` where
`StacksFrontier/RingTheory/LocalCohomology/LowDegree.lean` uses `Scheme.Hom.appTop`, and the two
are the same map. -/
theorem sectionsOverBase_complementZeroLocus (A : Type u) [CommRing A] (I : Ideal A) :
    sectionsOverBase.{u, v} A (complementZeroLocus A I).ι =
      complementGlobalSectionsFunctor.{u, max u v} A I := rfl

/-- Consequently the cohomology of Stacks 0DWR on `U = Spec A \ V(I)` is, as a functor, the
right derived functor of `Stacks.LocalCohomology.complementGlobalSectionsFunctor`. That is the
functor `StacksFrontier/RingTheory/LocalCohomology/LocalizationTriangle/Sections.lean` compares
with `Stacks.LocalCohomology.sectionsOnAffineComplement`, the sections functor on the open
`U ⊆ Spec A` whose derived functors the Čech comparison of
`StacksFrontier/RingTheory/LocalCohomology/HigherDegree/CechSheafCohomology.lean` computes. -/
theorem cohomologyOverBaseFunctor_complementZeroLocus (A : Type u) [CommRing A] (I : Ideal A)
    (p : ℕ) :
    cohomologyOverBaseFunctor.{u, v} A (complementZeroLocus A I).ι p =
      (complementGlobalSectionsFunctor.{u, max u v} A I).rightDerived p := rfl

/-- **The comparison of Stacks 0DWR for an arbitrary sheaf follows from the comparison for the
restricted associated sheaf.** Stacks 0DWR assumes only that `F` is isomorphic to `M̃|U`, and its
left-hand side takes an isomorphism of sheaves of modules to an `A`-linear equivalence, so the
hypothesis `Nonempty (F ≅ M̃|U)` carries no information beyond the case `F = M̃|U`.

This is a reduction and not the comparison: the hypothesis is exactly the statement of
Stacks 0DWR at `F = M̃|U`. -/
theorem nonempty_cohomologyOverBase_iso_of_complementTilde (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (p : ℕ)
    (h : Nonempty
      (cohomologyOverBase.{u, v} A (complementZeroLocus A I).ι (complementTilde A I M) p ≃ₗ[A]
        localCohomologyModule A I hI M (p + 1)))
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : Nonempty (F ≅ complementTilde A I M)) :
    Nonempty
      (cohomologyOverBase.{u, v} A (complementZeroLocus A I).ι F p ≃ₗ[A]
        localCohomologyModule A I hI M (p + 1)) := by
  obtain ⟨e⟩ := e
  obtain ⟨h⟩ := h
  exact ⟨(cohomologyOverBaseLinearEquivOfIso A (complementZeroLocus A I).ι e p).trans h⟩

end Stacks.LocalCohomology

end
