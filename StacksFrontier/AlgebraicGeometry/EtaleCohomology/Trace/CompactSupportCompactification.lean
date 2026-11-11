module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse

/-!
# Cohomology with compact support through a compactification over the base field

Let `k` be a field, `X` a separated finite type `k`-scheme, `k̄` an extension field of `k` and
`Λ` a ring.  Following the source, choose an open immersion `j : X ⟶ X̄` with `X̄` proper over
`k` and put

`RΓ_c(X_k̄, K) := RΓ(X̄_k̄, j_! K)`.

The ambient scheme is base changed with `X`: the fibre product `X̄_k̄ = X̄ ×_{Spec k} Spec k̄` is
proper over `Spec k̄` and the base change `X_k̄ ⟶ X̄_k̄` of `j` is again an open immersion, so a
compactification of `X` over `k` yields a compactification of `X_k̄` over `k̄`, and
`RΓ_c(X_k̄, -)` is the cohomology with compact support of [Stacks, Tag 0GJZ] taken through it.
That is the construction `Stacks.EtaleCohomology.compactificationFieldBaseChange`, and it is
what lets the compactification of `X_k̄` consumed by the trace formula be produced from a
compactification of `X` over the finite field, which is how the source prescribes it.

The chosen compactification is an explicit argument of every definition here, never a choice
extracted from an existence statement.  Its independence is therefore a comparison between the
values at two arguments: an isomorphism of the two derived lower shriek functors induces an
isomorphism of the two complexes `RΓ_c(X_k̄, -)` and of the two families of modules
`H^i_c(X_k̄, -)`, and the comparisons compose.  The canonical isomorphism of the derived lower
shriek functors for compactifications of dimension at most one, and with it the independence of
the compactification of Remark 03UI (2), is constructed in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricCompactSupportCanonicalComparison`
(`Stacks.EtaleCohomology.geometricCompactSupportCanonicalComparison`).

## Main definitions

* `Stacks.EtaleCohomology.compactificationFieldBaseChange` — the base change `X̄_k̄` of a
  compactification of `X` over `k`, as a compactification of `X_k̄` over `k̄`.
* `Stacks.EtaleCohomology.geometricCompactSupportCohomology` — the complex
  `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, j_! K)`.
* `Stacks.EtaleCohomology.geometricCompactSupportCohomologyGroup` — the module
  `H^i_c(X_k̄, K)`, the `i`-th cohomology of that complex.
* `Stacks.EtaleCohomology.geometricCompactSupportComparison` and
  `Stacks.EtaleCohomology.geometricCompactSupportGroupComparison` — the comparisons of the
  complexes and of the modules obtained from two compactifications of `X` over `k`, induced by
  an isomorphism of their derived lower shriek functors.

## Main results

* `Stacks.EtaleCohomology.compactificationFieldBaseChange_immersion_comp_fst` — the base
  changed open immersion lies over the given one.
* `Stacks.EtaleCohomology.geometricCompactSupportComparison_trans` and
  `Stacks.EtaleCohomology.geometricCompactSupportComparison_refl` — the comparisons compose,
  and the comparison of a compactification with itself along the identity is the identity.

## Implementation notes

The source asks `X̄` to be projective over `k` of dimension at most one.  Neither hypothesis is
imposed: the formula `RΓ(X̄_k̄, j_! K)` uses only that `X̄` is proper over `k`, which a
projective `k`-scheme is, so neither appears in the elaborated type of these definitions.  This
is the convention under which [Stacks, Tag 0GJZ] is already stated in this development, where
the finite type and separatedness of `X` are likewise absent from the formula.

Independence of the choice of `X̄` is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricCompactSupportCanonicalComparison`,
which constructs the canonical isomorphism of the derived lower shriek functors through the
closure of `X` in `X̄₁ ×_k X̄₂` and feeds it to
`Stacks.EtaleCohomology.geometricCompactSupportComparison`.  The latter takes an arbitrary
isomorphism of the derived lower shriek functors as an argument; its content is that the
comparison it induces on `RΓ_c` and on each `H^i_c` is natural in the coefficient complex and
compatible with composition.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section BaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The base change `X_k̄ ⟶ X̄_k̄` of the open immersion of a compactification of `X` over `k`
along the extension `k̄` of `k`: the morphism with components `X_k̄ ⟶ X ⟶ X̄` and
`X_k̄ ⟶ Spec k̄`. -/
public def compactificationFieldBaseChangeImmersion :
    pullback f (Stacks.Frobenius.specAlgebraMap k kbar) ⟶
      pullback j.toBase (Stacks.Frobenius.specAlgebraMap k kbar) :=
  pullback.lift (pullback.fst f (Stacks.Frobenius.specAlgebraMap k kbar) ≫ j.immersion)
    (pullback.snd f (Stacks.Frobenius.specAlgebraMap k kbar))
    (by
      have h : j.immersion ≫ j.toBase = f := Over.w j.obj.hom
      rw [Category.assoc, h]
      exact pullback.condition)

/-- The base change of the open immersion lies over it: its first component is the projection
to `X` followed by the open immersion. -/
@[reassoc (attr := simp)]
public lemma compactificationFieldBaseChange_immersion_comp_fst :
    compactificationFieldBaseChangeImmersion f j kbar ≫
        pullback.fst j.toBase (Stacks.Frobenius.specAlgebraMap k kbar) =
      pullback.fst f (Stacks.Frobenius.specAlgebraMap k kbar) ≫ j.immersion :=
  pullback.lift_fst _ _ _

/-- The base change of the open immersion is a morphism over `Spec k̄`. -/
@[reassoc (attr := simp)]
public lemma compactificationFieldBaseChange_immersion_comp_snd :
    compactificationFieldBaseChangeImmersion f j kbar ≫
        pullback.snd j.toBase (Stacks.Frobenius.specAlgebraMap k kbar) =
      pullback.snd f (Stacks.Frobenius.specAlgebraMap k kbar) :=
  pullback.lift_snd _ _ _

/-- The base change of the open immersion of a compactification is an open immersion, being a
base change of one. -/
public instance compactificationFieldBaseChangeImmersion_isOpenImmersion :
    IsOpenImmersion (compactificationFieldBaseChangeImmersion f j kbar) := by
  have h : f = j.immersion ≫ j.toBase := (Over.w j.obj.hom).symm
  exact MorphismProperty.pullbackLift_fst_snd (P := @IsOpenImmersion)
    (Stacks.Frobenius.specAlgebraMap k kbar) h inferInstance

/-- **The base change `X̄_k̄` of a compactification of `X` over `k`**, as a compactification of
`X_k̄` over `k̄`: the fibre product `X̄ ×_{Spec k} Spec k̄` is proper over `Spec k̄` because `X̄`
is proper over `Spec k`, and `X_k̄ ⟶ X̄_k̄` is an open immersion because `X ⟶ X̄` is one.  This
is the ambient scheme the source takes `RΓ_c(X_k̄, -)` on. -/
@[stacks 03UI "item (2): the base change X̄_k̄ of a compactification X̄ of X over k is a \
compactification of X_k̄ over k̄, which is where RΓ_c(X_k̄, -) is formed"]
public def compactificationFieldBaseChange :
    CompactificationOf (Over.mk (pullback.snd f (Stacks.Frobenius.specAlgebraMap k kbar))) where
  obj := StructuredArrow.mk
    (Y := Over.mk (pullback.snd j.toBase (Stacks.Frobenius.specAlgebraMap k kbar)))
    (Over.homMk (compactificationFieldBaseChangeImmersion f j kbar)
      (compactificationFieldBaseChange_immersion_comp_snd f j kbar))
  property := by
    refine ⟨compactificationFieldBaseChangeImmersion_isOpenImmersion f j kbar, ?_⟩
    change IsProper (pullback.snd j.toBase (Stacks.Frobenius.specAlgebraMap k kbar))
    infer_instance

end BaseChange

section CompactSupport

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (Λ : Type r) [Ring Λ]

/-- **The complex `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, j_! K)`** of the source: cohomology with compact
support of a bounded below complex of sheaves of `Λ`-modules on the small étale site of the
base change `X_k̄`, formed through the base change `X̄_k̄` of a compactification `X̄` of `X`
over `k`.  The compactification is an argument, not a choice. -/
@[stacks 03UI "item (2): RΓ_c(X_k̄, K) := RΓ(X̄_k̄, j_! K) for a chosen compactification j of X \
over k, taken through its base change"]
public abbrev geometricCompactSupportCohomology :
    DerivedCategory.Plus
        (EtaleModules.{u, r} Λ (pullback f (Stacks.Frobenius.specAlgebraMap k kbar))) ⥤
      DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  compactlySupportedCohomology.{u, r} kbar
    (pullback.snd f (Stacks.Frobenius.specAlgebraMap k kbar))
    (compactificationFieldBaseChange f j kbar) Λ

/-- **The module `H^i_c(X_k̄, K)`**: the `i`-th cohomology of `RΓ_c(X_k̄, K)`. -/
@[stacks 03UI "item (2): H^i_c(X_k̄, K) is the i-th cohomology of RΓ_c(X_k̄, K)"]
public abbrev geometricCompactSupportCohomologyGroup (i : ℤ) :
    DerivedCategory.Plus
        (EtaleModules.{u, r} Λ (pullback f (Stacks.Frobenius.specAlgebraMap k kbar))) ⥤
      ModuleCat.{max (u + 1) r} Λ :=
  geometricCompactSupportCohomology.{u, r} f j kbar Λ ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i

end CompactSupport

section Independence

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j₁ j₂ j₃ : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (Λ : Type r) [Ring Λ]

/-- The derived lower shriek functor `Rf_!` of `X_k̄` over `k̄` formed through the base change
of a compactification of `X` over `k`. -/
public abbrev geometricLowerShriek :
    DerivedCategory.Plus
        (EtaleModules.{u, r} Λ (pullback f (Stacks.Frobenius.specAlgebraMap k kbar))) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ (Spec (.of kbar))) :=
  derivedLowerShriek.{u, r} (pullback.snd f (Stacks.Frobenius.specAlgebraMap k kbar))
    (compactificationFieldBaseChange f j₁ kbar) Λ

/-- An isomorphism of the derived lower shriek functors attached to two compactifications of `X`
over `k` induces an isomorphism of the complexes `RΓ_c(X_k̄, -)` they present, natural in the
coefficient complex.  Applied to the canonical isomorphism of the derived lower shriek functors
it gives the independence of the compactification,
`Stacks.EtaleCohomology.geometricCompactSupportCanonicalComparison`. -/
public def geometricCompactSupportComparison
    (e : geometricLowerShriek.{u, r} f j₁ kbar Λ ≅ geometricLowerShriek.{u, r} f j₂ kbar Λ) :
    geometricCompactSupportCohomology.{u, r} f j₁ kbar Λ ≅
      geometricCompactSupportCohomology.{u, r} f j₂ kbar Λ :=
  Functor.isoWhiskerRight e (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar)))

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The comparison of a compactification with itself along the identity is the identity. -/
@[simp]
public lemma geometricCompactSupportComparison_refl :
    geometricCompactSupportComparison.{u, r} f j₁ j₁ kbar Λ
        (Iso.refl (geometricLowerShriek.{u, r} f j₁ kbar Λ)) =
      Iso.refl (geometricCompactSupportCohomology.{u, r} f j₁ kbar Λ) := by
  ext K
  simp [geometricCompactSupportComparison]

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- Comparisons through an intermediate compactification compose to the direct comparison. -/
public lemma geometricCompactSupportComparison_trans
    (e₁ : geometricLowerShriek.{u, r} f j₁ kbar Λ ≅ geometricLowerShriek.{u, r} f j₂ kbar Λ)
    (e₂ : geometricLowerShriek.{u, r} f j₂ kbar Λ ≅ geometricLowerShriek.{u, r} f j₃ kbar Λ) :
    geometricCompactSupportComparison.{u, r} f j₁ j₃ kbar Λ (e₁ ≪≫ e₂) =
      geometricCompactSupportComparison.{u, r} f j₁ j₂ kbar Λ e₁ ≪≫
        geometricCompactSupportComparison.{u, r} f j₂ j₃ kbar Λ e₂ := by
  ext K
  simp [geometricCompactSupportComparison]

/-- The comparison of the complexes induces an isomorphism of the modules `H^i_c(X_k̄, -)` in
every degree, natural in the coefficient complex.  Applied to the canonical isomorphism of the
derived lower shriek functors it gives
`Stacks.EtaleCohomology.geometricCompactSupportGroupCanonicalComparison`. -/
public def geometricCompactSupportGroupComparison
    (e : geometricLowerShriek.{u, r} f j₁ kbar Λ ≅ geometricLowerShriek.{u, r} f j₂ kbar Λ)
    (i : ℤ) :
    geometricCompactSupportCohomologyGroup.{u, r} f j₁ kbar Λ i ≅
      geometricCompactSupportCohomologyGroup.{u, r} f j₂ kbar Λ i :=
  Functor.isoWhiskerRight (geometricCompactSupportComparison.{u, r} f j₁ j₂ kbar Λ e)
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- The comparisons of the `H^i_c` compose, being induced by comparisons that compose. -/
public lemma geometricCompactSupportGroupComparison_trans
    (e₁ : geometricLowerShriek.{u, r} f j₁ kbar Λ ≅ geometricLowerShriek.{u, r} f j₂ kbar Λ)
    (e₂ : geometricLowerShriek.{u, r} f j₂ kbar Λ ≅ geometricLowerShriek.{u, r} f j₃ kbar Λ)
    (i : ℤ) :
    geometricCompactSupportGroupComparison.{u, r} f j₁ j₃ kbar Λ (e₁ ≪≫ e₂) i =
      geometricCompactSupportGroupComparison.{u, r} f j₁ j₂ kbar Λ e₁ i ≪≫
        geometricCompactSupportGroupComparison.{u, r} f j₂ j₃ kbar Λ e₂ i := by
  ext K
  simp [geometricCompactSupportGroupComparison, geometricCompactSupportComparison]

end Independence

end Stacks.EtaleCohomology

end
