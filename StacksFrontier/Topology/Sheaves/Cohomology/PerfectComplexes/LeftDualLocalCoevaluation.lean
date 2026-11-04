module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectLocalRep
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.MonoidalStructure

/-!
# The coevaluation of a left dual in `D(O_X)` is locally a map of complexes

Let `(X, O_X)` be a ringed space, let `M` and `N` be objects of `D(O_X)` and let
`η : O_X ⟶ M ⊗^L_{O_X} N` be a morphism of `D(O_X)` out of the monoidal unit of Stacks 0FPB —
for instance the coevaluation of an exact pairing, Categories, Definition 0FFP, which is the
hypothesis of Stacks 0FPD. Represent `M` and `N` by **K-flat** complexes `M^•` and `N^•`. Then
every point of `X` has an open neighbourhood `U` over which `η` is induced by an honest **map of
complexes**

`β : O_X[0]|_U ⟶ Tot(M^• ⊗_{O_X} N^•)|_U`.

This is the step that the source of Stacks 0FPD performs without comment when it writes
*"Consider the map `η : O_X → Tot(M^• ⊗_{O_X} N^•)`"* and then speaks of `η(1)`. A morphism of
`D(O_X)` out of `O_X` is a hypercohomology class, not a global section of the kernel of the
degree-zero differential, so there is something to prove here: what makes it a map of complexes,
after shrinking, is that the monoidal unit of the complexes of `O_X`-modules — the structure
sheaf in degree zero — is a **strictly perfect** complex, and a morphism of the derived category
out of a strictly perfect complex is locally induced by a map of complexes. That is Stacks 08C9,
part (1), `AlgebraicGeometry.RingedSpace.exists_local_complex_map`, which is one of the lemmas
the source lists among the inputs of Stacks 0FPD.

Nothing below is a clause of a tag; it is a step of the proof of Stacks 0FPD, conclusion (a),
which is `Stacks.Cohomology.LeftDualPerfect.isPerfect_of_exactPairing`. No hypothesis below
stands in for a theorem: `M^•`,
`N^•` and `η` are data, and `hM`, `hN` are K-flatness of the two chosen representatives, which
Stacks 06YF (`AlgebraicGeometry.RingedSpace.exists_isKFlat_isFlat_quasiIso_epi`) supplies — with
flat terms, which is what the next step of the source argument needs.

## Main definitions

* `Stacks.Cohomology.LeftDualPerfect.unitComplex`: the structure sheaf in degree zero, which is
  the monoidal unit of the complexes of `O_X`-modules on the nose
  (`unitComplex_eq_tensorUnit`, by `rfl`) and the complex that `UnitIso` of Stacks 0FPB names.
* `Stacks.Cohomology.LeftDualPerfect.coevaluationUnitHom`: a morphism `η` of `D(O_X)` out of the
  monoidal unit into `Q(M^•) ⊗^L Q(N^•)`, read through the two comparisons of Stacks 0FPB as a
  morphism `Q(O_X[0]) ⟶ Q(Tot(M^• ⊗ N^•))` between the images of two complexes.

## Main results

* `Stacks.Cohomology.LeftDualPerfect.isStrictlyPerfect_unitComplex`: `O_X[0]` is strictly
  perfect.
* `Stacks.Cohomology.LeftDualPerfect.exists_local_complexMap_of_unitComplexHom`: Stacks 08C9,
  part (1), with the strictly perfect source specialized to `O_X[0]`.
* `Stacks.Cohomology.LeftDualPerfect.exists_local_complexMap_coevaluation`: **the statement
  above** — a morphism of `D(O_X)` out of the monoidal unit into the derived tensor product of
  two K-flat complexes is, over a neighbourhood of any point, induced by a map of complexes into
  the total tensor complex.

## What this is made of

* `Stacks.Cohomology.MonoidalDerived.symmetricMonoidalDerivedCategory` (Stacks 0FPB) carries both
  comparisons that turn `η` into a morphism between images of complexes: its `unitIso` identifies
  the monoidal unit of `D(O_X)` with `Q(O_X[0])`, and its `comparison` identifies
  `Q(M^•) ⊗ Q(N^•)` with `Q(Tot(M^• ⊗ N^•))` whenever both complexes are K-flat. The second is
  what "the derived tensor product is computed by the total tensor complex" means, and it is why
  the two representatives are taken K-flat.
* `StrictlyPerfect.isStrictlyPerfect_single` and
  `StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule`: the structure sheaf is free of
  rank one, and a direct summand of a finite free module placed in a single degree is a strictly
  perfect complex.
* `AlgebraicGeometry.RingedSpace.exists_local_complex_map_of_instances`: Stacks 08C9, part (1).

## Use

The proof of Stacks 0FPD, conclusion (a), reads `β` off in degree zero:
`Stacks.Cohomology.LeftDualPerfect.exists_local_cocycle_data` and
`Stacks.Cohomology.LeftDualPerfect.restrict_map_eq_cocycleHom` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualRetract` record the same
statement with the cocycle `β(1)` valid on every smaller open, which is the form the local
retract `Stacks.Cohomology.LeftDualPerfect.exists_local_retract` consumes.

## Implementation notes

**Two spellings of the modules, and which instance is ascribed where.** `O_X`-modules are spelled
`Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf` by the monoidal cluster and
`StrictlyPerfect.OXMod X` by the perfectness cluster. The two are the same type — `rfl` —
but they are not interchangeable for instance synthesis, their structure sheaves being
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` and
`AlgebraicGeometry.structureSheafOfRings X`. Everything below is therefore written in the `Mod`
spelling, where the monoidal structures live, with one ascription
`letI : HasDerivedCategory.{d} (OXMod X) := inst` in the statements that mention
`AlgebraicGeometry.RingedSpace.restrictModules`, whose source category is spelled `OXMod`. The
defeq crossing happens at the `:=`.

**The monoidal unit is not written `𝟙_`.** The monoidal structure on the complexes of
`O_X`-modules is not an instance, and at a ringed space it is not reachable by synthesis either:
even with the modules' monoidal structure and this cluster's additivity and total-complex
instances pinned by hand, `MonoidalCategoryStruct (CochainComplex (Mod X.sheaf) ℤ)` is not
synthesized. It is introduced by a `letI` as
`Stacks.Cohomology.MonoidalComplexes.cochainComplexMonoidalCategory`, the Stacks 0FP8 structure
read on a ringed space. But `𝟙_ _` carries no information other than its expected type, so
underneath `(restrictModules X U).mapHomologicalComplex.obj` the elaborator reads that expected
type as the `OXMod` spelling and then fails to find the `letI`. `unitComplex` below is the same
complex written without the monoidal structure, which is what the statements use; that it *is*
the monoidal unit is `unitComplex_eq_tensorUnit`, by `rfl`.

That the comparison isomorphism of Stacks 0FPB — whose type was elaborated against the
site-level instances — typechecks against `cochainComplexMonoidalCategory`'s tensor product of
complexes is a definitional crossing which the elaborator accepts; it is exercised by
`coevaluationUnitHom`.

The derived-category hom universes of `X` and of its open subspaces are free and independent, as
they are in Stacks 08C9 itself; the space, ring and module universes coincide, as they must for
the ringed-space perfectness machinery.

## References

* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
* [Stacks Project, Tag 0FP8](https://stacks.math.columbia.edu/tag/0FP8)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules.DerivedMonoidal Stacks.Cohomology.MonoidalDerived
open Stacks.Cohomology.MonoidalComplexes StrictlyPerfect

universe u d d'

namespace Stacks.Cohomology.LeftDualPerfect

variable (X : RingedSpace.{u, u})

/-- **The structure sheaf of a ringed space in degree zero.** This is the monoidal unit of the
complexes of `O_X`-modules — `unitComplex_eq_tensorUnit`, by `rfl` — and the complex that
`Stacks.SheafOfModules.DerivedMonoidal.UnitIso` identifies the monoidal unit of `D(O_X)` with.
It is written here without reference to the monoidal structure, which is not an instance. -/
abbrev unitComplex : CochainComplex (Mod X.sheaf) ℤ :=
  (CochainComplex.singleFunctor (Mod X.sheaf) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))

/-- **`unitComplex` is the monoidal unit of the complexes of `O_X`-modules**, for the monoidal
structure of Stacks 0FP8. -/
theorem unitComplex_eq_tensorUnit :
    letI := cochainComplexMonoidalCategory X
    unitComplex X = 𝟙_ (CochainComplex (Mod X.sheaf) ℤ) :=
  rfl

/-- **The structure sheaf in degree zero is a strictly perfect complex**, in the ringed-space
sense of Tag 08FL that Stacks 08C9 consumes. The structure sheaf is free of rank one, hence a
direct summand of a finite free module, and a direct summand of a finite free module placed in a
single degree is strictly perfect. -/
theorem isStrictlyPerfect_unitComplex : IsStrictlyPerfect (unitComplex X) :=
  isStrictlyPerfect_single (isDirectSummandOfFiniteFree_structureModule X) 0

variable [inst : HasDerivedCategory.{d} (Mod X.sheaf)]
  [∀ U : Opens X.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

/-- **Stacks 08C9, part (1), out of the structure sheaf in degree zero.** A morphism `α` of
`D(O_X)` from `Q(O_X[0])` to the image of a complex `F` is, over an open neighbourhood of any
given point, induced by a morphism of complexes `O_X[0]|_U ⟶ F|_U`; the comparison is made
through the canonical isomorphism `CategoryTheory.Functor.mapDerivedCategoryFactors` of the
exact functor `AlgebraicGeometry.RingedSpace.restrictModules X U`.

This is `AlgebraicGeometry.RingedSpace.exists_local_complex_map_of_instances` with the strictly
perfect source specialized to `unitComplex X`, which is strictly perfect by
`isStrictlyPerfect_unitComplex`. -/
theorem exists_local_complexMap_of_unitComplexHom (F : CochainComplex (Mod X.sheaf) ℤ)
    (α : DerivedCategory.Q.obj (unitComplex X) ⟶ DerivedCategory.Q.obj F) (x : X.carrier) :
    letI : HasDerivedCategory.{d} (OXMod.{u, u} X) := inst
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ β : ((RingedSpace.restrictModules.{u, u} X U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj (unitComplex X) ⟶
            ((RingedSpace.restrictModules.{u, u} X U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj F,
        (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategory.map α ≫
            (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app F =
          (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app
              (unitComplex X) ≫ DerivedCategory.Q.map β := by
  let : HasDerivedCategory.{d} (OXMod.{u, u} X) := inst
  exact AlgebraicGeometry.RingedSpace.exists_local_complex_map_of_instances
    (isStrictlyPerfect_unitComplex X) α x

/-- **A morphism of `D(O_X)` out of the monoidal unit, read as a morphism between the images of
two complexes.** For K-flat `M^•` and `N^•`, the two comparisons of Stacks 0FPB — the
identification of the monoidal unit of `D(O_X)` with `Q(O_X[0])` and the identification of
`Q(M^•) ⊗^L Q(N^•)` with `Q(Tot(M^• ⊗ N^•))` — turn `η : 𝟙 ⟶ Q(M^•) ⊗^L Q(N^•)` into a morphism

`Q(O_X[0]) ⟶ Q(Tot(M^• ⊗ N^•))`.

K-flatness of the two representatives is used exactly once, in the second comparison. -/
def coevaluationUnitHom (Mc Nc : CochainComplex (Mod X.sheaf) ℤ)
    (hM : KFlat X.sheaf Mc) (hN : KFlat X.sheaf Nc)
    (η : letI := derivedCategoryMonoidalCategory X
      𝟙_ (DerivedModules X.sheaf) ⟶
        DerivedCategory.Q.obj Mc ⊗ DerivedCategory.Q.obj Nc) :
    letI := cochainComplexMonoidalCategory X
    DerivedCategory.Q.obj (unitComplex X) ⟶
      DerivedCategory.Q.obj ((Mc ⊗ Nc : CochainComplex (Mod X.sheaf) ℤ)) :=
  letI := cochainComplexMonoidalCategory X
  letI := derivedCategoryMonoidalCategory X
  (symmetricMonoidalDerivedCategory X).unitIso.inv ≫ η ≫
    ((symmetricMonoidalDerivedCategory X).comparison Mc Nc hM hN).hom

/-- **A morphism of `D(O_X)` out of the monoidal unit into the derived tensor product of two
K-flat complexes is locally a map of complexes into the total tensor complex.** Let `M^•` and
`N^•` be K-flat complexes of `O_X`-modules and let `η : O_X ⟶ Q(M^•) ⊗^L Q(N^•)` be a morphism
of `D(O_X)` out of the monoidal unit of Stacks 0FPB — for instance the coevaluation `η_ M N` of
an exact pairing, which is the hypothesis of Stacks 0FPD. Then every point of `X` has an open
neighbourhood `U` carrying a morphism of complexes

`β : O_X[0]|_U ⟶ Tot(M^• ⊗ N^•)|_U`

inducing, in the derived category of `U`, the restriction of `η` read through the two comparisons
of Stacks 0FPB, namely of `coevaluationUnitHom`.

This is the step of the proof of Stacks 0FPD, conclusion (a), at which the coevaluation of a left
dual becomes a chain-level datum, so that the sections `fᵢ` and `gᵢ` of the source's
`η(1) = Σ fᵢ ⊗ gᵢ` can be extracted from it. It is a step of the proof and not a clause of the
tag, so it carries no `@[stacks]` attribute. -/
theorem exists_local_complexMap_coevaluation (Mc Nc : CochainComplex (Mod X.sheaf) ℤ)
    (hM : KFlat X.sheaf Mc) (hN : KFlat X.sheaf Nc)
    (η : letI := derivedCategoryMonoidalCategory X
      𝟙_ (DerivedModules X.sheaf) ⟶
        DerivedCategory.Q.obj Mc ⊗ DerivedCategory.Q.obj Nc)
    (x : X.carrier) :
    letI : HasDerivedCategory.{d} (OXMod.{u, u} X) := inst
    letI := cochainComplexMonoidalCategory X
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ β : ((RingedSpace.restrictModules.{u, u} X U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj (unitComplex X) ⟶
            ((RingedSpace.restrictModules.{u, u} X U).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj ((Mc ⊗ Nc : CochainComplex (Mod X.sheaf) ℤ)),
        (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategory.map
              (coevaluationUnitHom X Mc Nc hM hN η) ≫
            (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app
              ((Mc ⊗ Nc : CochainComplex (Mod X.sheaf) ℤ)) =
          (RingedSpace.restrictModules.{u, u} X U).mapDerivedCategoryFactors.hom.app
              (unitComplex X) ≫ DerivedCategory.Q.map β :=
  exists_local_complexMap_of_unitComplexHom X _ (coevaluationUnitHom X Mc Nc hM hN η) x

end Stacks.Cohomology.LeftDualPerfect

end
