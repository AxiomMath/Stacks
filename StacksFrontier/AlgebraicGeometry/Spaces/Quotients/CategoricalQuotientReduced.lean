module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPlusStrictlyFull
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CategoricalQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reducedness of a categorical quotient

A categorical quotient of a reduced algebraic space is reduced, and the same holds in each of
the four standard full subcategories of algebraic spaces — separated, quasi-separated, locally
separated and decent — and in the category of schemes.

The argument is one argument. If `φ : U ⟶ X` is a categorical quotient and `U` is reduced, the
reduction `Z ⊆ X` is a reduced closed subspace with all of `|X|` for its point set, so `φ`
factors through `Z` by Stacks 03JJ. The factorization is again invariant, so the universal
property applies to it, and the inclusion `Z ⟶ X` is a monomorphism split by the comparison
morphism `X ⟶ Z`; hence it is an isomorphism and `X` is reduced. The six statements differ only
in which category the universal property is taken in, which is why the core is stated once with
the ambient subcategory as a parameter.

## Main results

* `AlgebraicGeometry.Space.isReduced_of_isCategoricalQuotient`: **Stacks 049W** for algebraic
  spaces over the base.
* `AlgebraicGeometry.Space.isReduced_of_isCategoricalQuotientInSeparated`,
  `AlgebraicGeometry.Space.isReduced_of_isCategoricalQuotientInQuasiSeparated`,
  `AlgebraicGeometry.Space.isReduced_of_isCategoricalQuotientInLocallySeparated` and
  `AlgebraicGeometry.Space.isReduced_of_isCategoricalQuotientInDecent`: **Stacks 049W** in the
  four standard full subcategories.
* `AlgebraicGeometry.Space.isReduced_of_isCategoricalQuotientInSchemes`: **Stacks 049W** for
  schemes over a base scheme.

## Implementation notes

Reducedness of an algebraic space is the étale-local scheme property of Stacks 03E6; for a
scheme it is `AlgebraicGeometry.IsReduced` directly.

All six statements are unconditional. The one input about the reduction which is not purely
formal is that `AlgebraicGeometry.Space.reducedClosedSubspace` of `X` is a *closed subspace*;
that is `AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace` of
`StacksFrontier/AlgebraicGeometry/Spaces/ReducedClosedSubspace.lean`, which states that clause of
Stacks 03IQ with no hypothesis. The effective descent of closed immersions along the
surjective étale morphisms of the site which its proof consumes is itself a theorem,
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion` of
`StacksFrontier/AlgebraicGeometry/Descent/ClosedImmersionEffectiveDescent.lean`. The point set of
the reduction and its reducedness are unconditional too and are used as such. The scheme
statement uses the reduction of a scheme directly.

No separation or decency hypothesis is placed on the base `B`: preservation of reducedness by
the quotient does not use one. Each full-subcategory statement requires only that the
subcategory contain the reduction of `X`, which is where Stacks 04CH, 03KK, 04ZH and 03KF
enter, one of them per subcategory.

The subcategory is a parameter of `ObjectProperty (CategoryTheory.Over B)` rather than a
typeclass, matching `AlgebraicGeometry.Space.IsCategoricalQuotientIn`, and the core lemma asks
for membership of the reduction as a hypothesis so that the four instantiations supply only
that one fact.

## References

* [Stacks Project, Tag 049W](https://stacks.math.columbia.edu/tag/049W)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Base : AlgebraicSpaces B S hS}

/-! ### The categorical core -/

/-- An object with the universal property of a quotient is isomorphic to any object through
which the quotient map factors by a monomorphism, provided that object also receives the
quotient map in a way which the universal property can compare.

This is the categorical heart of Stacks 049W: `e` is split by the comparison morphism
`χ : X ⟶ Y`, because `χ ≫ e` and `𝟙 X` both make the triangle under `φ` commute, and a split
monomorphism is an isomorphism. -/
private noncomputable def isoOfCategoricalFactorization {C : Type v} [Category C]
    {U X Y : C} (φ : U ⟶ X) (ψ : U ⟶ Y) (e : Y ⟶ X) [Mono e]
    (hfac : ψ ≫ e = φ) (hχ : ∃! χ : X ⟶ Y, φ ≫ χ = ψ)
    (hδ : ∃! δ : X ⟶ X, φ ≫ δ = φ) : Y ≅ X := by
  classical
  let χ := Classical.choose hχ
  have hχeq := (Classical.choose_spec hχ).1
  have hδuniq := (Classical.choose_spec hδ).2
  have he : χ ≫ e = 𝟙 X :=
    (hδuniq _ (by change φ ≫ (χ ≫ e) = φ; rw [← Category.assoc, hχeq, hfac])).trans
      (hδuniq _ (by simp)).symm
  exact ⟨e, χ, (cancel_mono e).1 (by simp [Category.assoc, he]), he⟩

/-- If `ψ` factors `φ` through a monomorphism `i`, then two maps equalized by `φ` are equalized
by `ψ`. -/
private theorem comp_eq_comp_of_comp_mono_eq {C : Type v} [Category C] {W U Y X : C}
    {a b : W ⟶ U} {ψ : U ⟶ Y} {φ : U ⟶ X} (i : Y ⟶ X) [Mono i] (hfac : ψ ≫ i = φ)
    (h : a ≫ φ = b ≫ φ) : a ≫ ψ = b ≫ ψ :=
  (cancel_mono i).1 (by simp only [Category.assoc, hfac, h])

/-! ### Reducedness of a quotient of algebraic spaces -/

/-- A closed subspace of the underlying algebraic space of an object of `Over Base`, viewed as
an object of `Over Base` through the inclusion. -/
private abbrev closedSubspaceOver {X : Over Base}
    (Z : Subfunctor X.left.obj) (hZ : IsClosedSubspace B S hS Z) : Over Base :=
  Over.mk ((ObjectProperty.homMk Z.ι : (⟨Z.toFunctor, hZ.1⟩ :
    AlgebraicSpaces B S hS) ⟶ X.left) ≫ X.hom)

/-- The core of Stacks 049W. If `φ : U ⟶ X` is invariant under `j` and has the universal
property of a quotient against the objects of `Q`, if `U` is reduced, and if `Q` contains the
reduction of `X`, then `X` is reduced.

The hypothesis `hQred` is asked for an arbitrary reduced closed subspace of `X` with full point
set, so that the four full-subcategory instantiations each supply one permanence property and
nothing about the reduction as such. -/
private theorem hasEtaleLocalProperty_isReduced_of_universal
    {R U X : Over Base} (j : PreRelation R U) (φ : U ⟶ X)
    (Q : ObjectProperty (Over Base))
    (hQred : ∀ (Z : Subfunctor X.left.obj) (hZ : IsClosedSubspace B S hS Z),
      Set.range (pointsMap B S hS Z.toFunctor Z.ι) = Set.univ →
      HasEtaleLocalProperty B S hS Z.toFunctor (fun Y : Scheme.{u} => IsReduced Y) →
      Q (closedSubspaceOver (X := X) Z hZ))
    (hQX : Q X) (hInv : IsInvariant j φ.left)
    (hUniversal : ∀ (Y : Over Base), Q Y → ∀ (ψ : U ⟶ Y),
      IsInvariant j ψ.left → ∃! χ : X ⟶ Y, φ ≫ χ = ψ)
    (hU : HasEtaleLocalProperty B S hS U.left.obj (fun Y : Scheme.{u} => IsReduced Y)) :
    HasEtaleLocalProperty B S hS X.left.obj (fun Y : Scheme.{u} => IsReduced Y) := by
  classical
  set Z := reducedClosedSubspace B S hS X.left.obj X.left.property Set.univ isClosed_univ
    with hZdef
  have hZclosed : IsClosedSubspace B S hS Z :=
    isClosedSubspace_reducedClosedSubspace B S hS X.left.obj X.left.property Set.univ
      isClosed_univ
  have hZsupport : Set.range (pointsMap B S hS Z.toFunctor Z.ι) = Set.univ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS X.left.obj X.left.property Set.univ
      isClosed_univ
  have hZred : HasEtaleLocalProperty B S hS Z.toFunctor (fun Y : Scheme.{u} => IsReduced Y) :=
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X.left.obj X.left.property
      Set.univ isClosed_univ
  let Zsp : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZclosed.1⟩
  let zi : Zsp ⟶ X.left := ObjectProperty.homMk Z.ι
  let Y : Over Base := closedSubspaceOver (X := X) Z hZclosed
  have hQY : Q Y := hQred Z hZclosed hZsupport hZred
  -- `φ` factors through the reduction, by Stacks 03JJ: its image on points is everything.
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS
    X.left.property U.left.property Z hZclosed hU φ.left.hom).2
      (by rw [hZsupport]; exact fun x _ => Set.mem_univ x)
  let ψ : U ⟶ Y := Over.homMk (ObjectProperty.homMk g) (by
    apply ObjectProperty.hom_ext
    change (g ≫ Z.ι) ≫ X.hom.hom = U.hom.hom
    rw [hg]
    exact congrArg (fun f : U.left ⟶ Base => f.hom) φ.w)
  have hfacAS : ψ.left ≫ zi = φ.left := by
    apply ObjectProperty.hom_ext
    exact hg
  -- The inclusion of the reduction is a monomorphism of algebraic spaces.
  have hMonoRaw : Mono ((ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)).map zi) := by
    change Mono Z.ι
    infer_instance
  have : Mono zi := Functor.ReflectsMonomorphisms.reflects _ hMonoRaw
  have hψ : IsInvariant j ψ.left := comp_eq_comp_of_comp_mono_eq zi hfacAS hInv
  let e : Y ⟶ X := Over.homMk zi (by simp [Y, closedSubspaceOver, zi])
  have : Mono e.left := show Mono zi from inferInstance
  let eAS : Y.left ≅ X.left := (Over.forget Base).mapIso (isoOfCategoricalFactorization φ ψ e
    (Over.OverMorphism.ext hfacAS) (hUniversal Y hQY ψ hψ) (hUniversal X hQX φ hInv))
  exact hasEtaleLocalProperty_of_iso B S hS (fun Y : Scheme.{u} => IsReduced Y)
    ((ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F)).mapIso eAS) hZred

/-- **Stacks 049W**, for algebraic spaces over the base. A categorical quotient of a reduced
algebraic space is reduced. Unconditional. -/
@[stacks 049W "algebraic spaces"]
theorem isReduced_of_isCategoricalQuotient
    {R U X : Over Base} (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsCategoricalQuotient j φ)
    (hU : HasEtaleLocalProperty B S hS U.left.obj (fun Y : Scheme.{u} => IsReduced Y)) :
    HasEtaleLocalProperty B S hS X.left.obj (fun Y : Scheme.{u} => IsReduced Y) :=
  hasEtaleLocalProperty_isReduced_of_universal j φ (fun _ => True)
    (fun _ _ _ _ => trivial) trivial hφ.1 (fun Y _ => hφ.2 Y) hU

/-- **Stacks 049W**, for separated algebraic spaces. A categorical quotient in the full
subcategory of separated algebraic spaces, of a reduced algebraic space, is reduced.

The reduction of the target is separated because its inclusion is a closed immersion, hence a
separated morphism by Stacks 04CH, and the target is separated — Stacks 04ZH, part (1). -/
@[stacks 049W "separated algebraic spaces"]
theorem isReduced_of_isCategoricalQuotientInSeparated
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {R U X : Over Base} (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsCategoricalQuotientIn
      (fun Y : Over Base => IsAbsolutelySeparated B S hS hZ Y.left.obj) j φ)
    (hU : HasEtaleLocalProperty B S hS U.left.obj (fun Y : Scheme.{u} => IsReduced Y)) :
    HasEtaleLocalProperty B S hS X.left.obj (fun Y : Scheme.{u} => IsReduced Y) := by
  obtain ⟨-, -, hX, hInv, hUniversal⟩ := hφ
  refine hasEtaleLocalProperty_isReduced_of_universal j φ
    (fun Y : Over Base => IsAbsolutelySeparated B S hS hZ Y.left.obj) ?_ hX hInv
    hUniversal hU
  intro W hW _ _
  exact isAbsolutelySeparated_of_isSeparated B S hS hZ hX
    (isSeparated_of_isClosedImmersion B S hS W.ι hW.2)

/-- **Stacks 049W**, for quasi-separated algebraic spaces. A categorical quotient in the full
subcategory of quasi-separated algebraic spaces, of a reduced algebraic space, is reduced.

The inclusion of the reduction of the target is a closed immersion, hence separated by Stacks
04CH and so quasi-separated by Stacks 03KK; Stacks 04ZH, part (2) then transfers
quasi-separatedness from the target. -/
@[stacks 049W "quasi-separated algebraic spaces"]
theorem isReduced_of_isCategoricalQuotientInQuasiSeparated
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {R U X : Over Base} (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsCategoricalQuotientIn
      (fun Y : Over Base => IsAbsolutelyQuasiSeparated B S hS hZ Y.left.obj) j φ)
    (hU : HasEtaleLocalProperty B S hS U.left.obj (fun Y : Scheme.{u} => IsReduced Y)) :
    HasEtaleLocalProperty B S hS X.left.obj (fun Y : Scheme.{u} => IsReduced Y) := by
  obtain ⟨-, -, hX, hInv, hUniversal⟩ := hφ
  refine hasEtaleLocalProperty_isReduced_of_universal j φ
    (fun Y : Over Base => IsAbsolutelyQuasiSeparated B S hS hZ Y.left.obj) ?_ hX hInv
    hUniversal hU
  intro W hW _ _
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hW.1 hX
    (isQuasiSeparated_of_isSeparated B S hS
      (isSeparated_of_isClosedImmersion B S hS W.ι hW.2))

/-- **Stacks 049W**, for locally separated algebraic spaces. A categorical quotient in the full
subcategory of locally separated algebraic spaces, of a reduced algebraic space, is reduced.

The inclusion of the reduction of the target is a closed immersion, hence separated by Stacks
04CH and so locally separated by Stacks 03KK; Stacks 04ZH, part (3) then transfers local
separatedness from the target. -/
@[stacks 049W "locally separated algebraic spaces"]
theorem isReduced_of_isCategoricalQuotientInLocallySeparated
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {R U X : Over Base} (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsCategoricalQuotientIn
      (fun Y : Over Base => IsAbsolutelyLocallySeparated B S hS hZ Y.left.obj) j φ)
    (hU : HasEtaleLocalProperty B S hS U.left.obj (fun Y : Scheme.{u} => IsReduced Y)) :
    HasEtaleLocalProperty B S hS X.left.obj (fun Y : Scheme.{u} => IsReduced Y) := by
  obtain ⟨-, -, hX, hInv, hUniversal⟩ := hφ
  refine hasEtaleLocalProperty_isReduced_of_universal j φ
    (fun Y : Over Base => IsAbsolutelyLocallySeparated B S hS hZ Y.left.obj) ?_ hX hInv
    hUniversal hU
  intro W hW _ _
  exact isAbsolutelyLocallySeparated_of_isLocallySeparated B S hS hZ hX
    (isLocallySeparated_of_isSeparated B S hS
      (isSeparated_of_isClosedImmersion B S hS W.ι hW.2))

/-- **Stacks 049W**, for decent algebraic spaces. A categorical quotient in the full
subcategory of decent algebraic spaces, of a reduced algebraic space, is reduced.

The reduction of the target is decent because the inclusion of a closed subspace is
representable and decency passes to the source of a representable morphism — Stacks 03KF for
property `(γ)`, which is condition (4) of Stacks 03JV. -/
@[stacks 049W "decent algebraic spaces"]
theorem isReduced_of_isCategoricalQuotientInDecent
    {R U X : Over Base} (j : PreRelation R U) (φ : U ⟶ X)
    (hφ : IsCategoricalQuotientIn
      (fun Y : Over Base => IsDecentSpace B S hS Y.left.obj) j φ)
    (hU : HasEtaleLocalProperty B S hS U.left.obj (fun Y : Scheme.{u} => IsReduced Y)) :
    HasEtaleLocalProperty B S hS X.left.obj (fun Y : Scheme.{u} => IsReduced Y) := by
  obtain ⟨-, -, hX, hInv, hUniversal⟩ := hφ
  refine hasEtaleLocalProperty_isReduced_of_universal j φ
    (fun Y : Over Base => IsDecentSpace B S hS Y.left.obj) ?_ hX hInv hUniversal hU
  intro W hW _ _
  exact isDecentSpace_of_relativelyRepresentable B S hS hW.1 W.ι hW.2.rep hX

/-! ### Reducedness of a quotient of schemes -/

/-- **Stacks 049W**, for schemes. A categorical quotient in the category of schemes over a base
scheme, of a reduced scheme, is reduced.

Unconditional: the reduction of a scheme is its closed subscheme cut out by the nilradical, and
a morphism from a reduced scheme factors uniquely through it by Stacks 0356. -/
@[stacks 049W "schemes", sga "3 VIB 9.2" "more general"]
theorem isReduced_of_isCategoricalQuotientInSchemes
    {T : Scheme.{u}} {R U X : Over T} (j : Stacks.Groupoids.PreRelation R U)
    (φ : U ⟶ X) (hφ : IsCategoricalQuotientInSchemes j φ)
    (hU : IsReduced U.left) : IsReduced X.left := by
  have : IsReduced U.left := hU
  let i : X.left.nilradical.subscheme ⟶ X.left := X.left.nilradical.subschemeι
  obtain ⟨g, hg, -⟩ := Scheme.existsUnique_lift_nilradical_subschemeι φ.left
  let Y : Over T := Over.mk (i ≫ X.hom)
  let ψ : U ⟶ Y := Over.homMk g (by change (g ≫ i) ≫ X.hom = U.hom; rw [hg]; exact φ.w)
  have hψFactor : ψ.left ≫ i = φ.left := hg
  have : Mono i := inferInstance
  have hψ : j.target ≫ ψ = j.source ≫ ψ := by
    apply Over.OverMorphism.ext
    exact comp_eq_comp_of_comp_mono_eq i hψFactor
      (by simpa only [Over.comp_left] using congrArg Over.Hom.left hφ.1)
  let e : Y ⟶ X := Over.homMk i (by simp [Y])
  have : Mono e.left := show Mono i from inferInstance
  let eRed : Y.left ≅ X.left := (Over.forget T).mapIso (isoOfCategoricalFactorization φ ψ e
    (Over.OverMorphism.ext hψFactor) (hφ.2 Y ψ hψ) (hφ.2 X φ hφ.1))
  exact ObjectProperty.prop_of_iso IsReduced eRed X.left.isReduced_reduction

end AlgebraicGeometry.Space

end
