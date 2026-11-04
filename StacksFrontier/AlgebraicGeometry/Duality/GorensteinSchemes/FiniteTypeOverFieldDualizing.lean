module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StructureSheafDualizing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedConeDepthDimension

/-!
# The structure sheaf of a Gorenstein scheme of finite type over a field is a dualizing complex

Let `k` be a field and `f : X ⟶ Spec k` a morphism locally of finite type with `X` Gorenstein.
Then `𝒪_X`, placed in degree zero, is a dualizing complex on `X` in the sense of
[Stacks, Tag 0A87] — that is, `Stacks.Duality.IsDualizingComplex` holds for it, with nothing
carried.

[Stacks, Tag 0BFQ] clause (2), formalized as `Stacks.Duality.exists_isDualizingComplex_iff_unit`,
says that on a Gorenstein scheme the structure sheaf is a dualizing complex as soon as *some*
dualizing complex exists; what is added here is the existence, which over a field comes from the
ring-level ubiquity of [Stacks, Tag 0BFR] clause (5).

## Main results

The elided prefix is `Stacks.Duality`.

* `exists_isDualizingComplex_sections_overField`: the ring of sections at an affine open of a
  scheme locally of finite type over a field has a dualizing complex.
* `isDualizingComplex_unit_overField`: **`𝒪_X` in degree zero is a dualizing complex** on a
  Gorenstein scheme locally of finite type over a field.
* `exists_isDualizingComplex_overField`: the resulting existence statement on `X`, which is the
  shape the consumers of a dualizing complex on a scheme take as a hypothesis.

## Why this is not an instance of Tag 0BFQ, and carries no attribute

Clause (2) of [Stacks, Tag 0BFQ] has exactly two hypotheses, that `X` be Gorenstein and that `X`
have a dualizing complex, and it is already registered unconditionally, as an equivalence, in
`StacksFrontier/AlgebraicGeometry/Duality/GorensteinSchemes/StructureSheafDualizing.lean`. The
statement below replaces the second of those hypotheses by a different one — that `X` be locally
of finite type over a field — which is not part of that tag's setup, so it is neither an
instance of the tag nor a strengthening of it, and no `@[stacks 0BFQ]` attribute belongs on it.
The ring-level existence it consumes is [Stacks, Tag 0BFR] clause (5), whose attribute sits on
the ring-level statements in `StacksFrontier/RingTheory/Dualizing/Ubiquity.lean` and
`StacksFrontier/RingTheory/Dualizing/UbiquityCompleteLocal.lean`; the composite of a scheme
statement with a ring statement is not an assertion of a tag of its own. Accordingly
nothing below is tagged.

## What this does and does not settle

It settles that `Stacks.Duality.IsDualizingComplex` holds of a concrete complex. Until now it
held of none: the comment at
`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingComplex.lean` recording that
"`IsDualizingComplex` is proved for no concrete complex in this development" was accurate, and
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts` — the only general producer — carries the
affine-chart description of `f^!` as a hypothesis.

It does **not** settle that the canonical complex `ω_X^• = f^×(𝒪_{Spec k})` of
[Stacks, Tag 0BS2], `Stacks.Duality.dualizingComplexOverField`, is a dualizing complex. That is
a statement about a *particular* complex and needs the affine-chart description of the twisted
inverse image, namely [Stacks, Tag 0AA1] together with clause (b) of [Stacks, Tag 0BV2], neither
of which this development has; `Stacks.Duality.IsDualizingComplex` of the structure sheaf is
about a different complex, and the two are identified only by the uniqueness of dualizing
complexes *after* both are known to be dualizing. In particular nothing here gives
[Stacks, Tag 0BS3] or clauses (1) and (2) of [Stacks, Tag 0BS6].

## Implementation notes

*The affine chart is a finite type `k`-algebra.* For an affine open `U ⊆ X` the ring map
`Γ(Spec k, ⊤) ⟶ Γ(X, U)` is `f.appLE ⊤ U` and is of finite type by
`AlgebraicGeometry.LocallyOfFiniteType.finiteType_appLE`; composing with the inverse of
`AlgebraicGeometry.Scheme.ΓSpecIso`, which is surjective, makes `Γ(X, U)` a finite type
`k`-algebra. This is the idiom of
`StacksFrontier/AlgebraicGeometry/Picard/SmoothCurveLocalDimension.lean`.

*The derived categories.* `Stacks.Duality.HasDualizingModelOn` seals the derived categories of
`U.toScheme.Modules` and of `ModuleCat Γ(X, U)` inside its body at
`CategoryTheory.HasDerivedCategory.standard`, so that instance is installed here with priority
`10000` — the import closure reaches the global locally small instance, against which an
unprioritised local attribute does not win. The derived category of `X.Modules` stays an
instance *argument*, matching `Stacks.Duality.IsDualizingComplex`.

*The model isomorphism.* The two sides of the required isomorphism are the structure sheaf of
`U` in degree zero read two ways, and the chain of identifications that compares them is the one
in the proof of `Stacks.Duality.exists_isDualizingComplex_iff_unit`; it is repeated below
because that proof reaches it only through its own existence hypothesis, which is the hypothesis
being discharged here, and the chain is a step inside a proof rather than a declaration that
could be reused.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **The chart ring of a scheme locally of finite type over a field has a dualizing complex.**
The sections over an affine open form a finite type `k`-algebra, and a finite type algebra over a
field has a dualizing complex by [Stacks, Tag 0BFR] clause (5). -/
public theorem exists_isDualizingComplex_sections_overField
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] :
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex ω := by
  have hft : (f.appLE ⊤ U (by simp)).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) hU (by simp)
  let : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
  have hftA : RingHom.FiniteType (algebraMap k Γ(X, U)) := by
    show (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom).FiniteType
    exact hft.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let : Algebra.FiniteType k Γ(X, U) := (RingHom.finiteType_algebraMap).mp hftA
  exact Stacks.Algebraization.exists_isDualizingComplex_of_finiteType_field k Γ(X, U)

/-- **The structure sheaf of a Gorenstein scheme locally of finite type over a field, placed in
degree zero, is a dualizing complex.** At an affine open `U` the model is `Γ(X, U)` itself in
degree zero: that ring is Gorenstein by `Stacks.Duality.isGorensteinRing_sections`, it has a
dualizing complex by `Stacks.Duality.exists_isDualizingComplex_sections_overField`, and
[Stacks, Tag 0DW9] clause (2) then makes the ring itself one. The two sides of the comparison are
the structure sheaf of `U` in degree zero read through the inclusion `U ⊆ X` and through
`U ≅ Spec Γ(X, U)`. -/
public theorem isDualizingComplex_unit_overField
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    [AlgebraicGeometry.IsGorenstein X] [HasDerivedCategory.{w} X.Modules] :
    IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
  intro U hU
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω⟩ := exists_isDualizingComplex_sections_overField f U hU
  refine ⟨(DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
    (ModuleCat.of Γ(X, U) Γ(X, U)),
    (Dualizing.exists_isDualizingComplex_iff_regularModule.{u, u} Γ(X, U)
      (isGorensteinRing_sections U hU)).mp ⟨ω, hω⟩, ⟨?_⟩⟩
  refine ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor U.toScheme.Modules 0).mapIso
      (Scheme.Modules.restrictUnitIso U.ι ≪≫
        (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm ≪≫
        (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso
          (tildeSelf (R := Γ(X, U))).symm) ≪≫
    (((tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategorySingleFunctor 0).app _).symm

/-- **A Gorenstein scheme locally of finite type over a field has a dualizing complex.** This is
the existential form of `Stacks.Duality.isDualizingComplex_unit_overField`, which is the shape in
which the consumers of a dualizing complex on a scheme — the Cohen--Macaulay locus of
[Stacks, Tag 0AWT] clause (3), the Gorenstein locus of [Stacks, Tag 0BFQ] clause (1)(c),
universal catenarity of [Stacks, Tag 0AWF] — take their hypothesis. -/
public theorem exists_isDualizingComplex_overField
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    [AlgebraicGeometry.IsGorenstein X] [HasDerivedCategory.{w} X.Modules] :
    ∃ K : DerivedCategory X.Modules, IsDualizingComplex K :=
  ⟨_, isDualizingComplex_unit_overField f⟩

end Stacks.Duality

end
