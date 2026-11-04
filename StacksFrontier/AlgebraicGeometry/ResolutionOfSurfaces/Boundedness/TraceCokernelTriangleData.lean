module

public import StacksFrontier.AlgebraicGeometry.Duality.StandardModelGlobalSections
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.TruncationTriangleCriterion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.FirstCohomologyFiniteLength
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.DerivedSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DerivedPushforwardDegreeZero

/-!
# `RΓ(X, 𝒪_X)[2]` as the object `C` of the duality step of Tag 0B4S

The duality step of [Stacks, Tag 0B4S], in the form
`Stacks.ResolutionOfSurfaces.smul_eq_zero_of_triangle_of_forall_hom_eq_zero` of
`ResolutionOfSurfaces/Boundedness/TraceCokernelDualitySequence.lean`, consumes an object `C` of
`D(A)` with cohomology in the two degrees `-2` and `-1` only, a morphism `u : A[-2] ⟶ C` which is
an isomorphism on `H^{-2}`, and the finite length of `H^{-1}(C)`. This file produces all of that,
for `C = RΓ(X, 𝒪_X)[2]` and a modification `f : X ⟶ Spec(A)` of a two-dimensional Noetherian
normal local domain with `X` normal.

## Main definitions

All in the namespace `AlgebraicGeometry`.

* `standardDerivedGlobalSectionsUnit` — `RΓ(X, 𝒪_X)`, at the standard model of `D(A)`; the
  object `AlgebraicGeometry.standardDerivedGlobalSectionsStructureSheaf`.
* `standardDerivedGlobalSectionsUnitShift` — its shift `RΓ(X, 𝒪_X)[2]`.

## Main results

* `exists_hom_singleFunctor_of_homologyIso` — in any `D(𝒜)`, an object with no cohomology
  below `n` and `Hⁿ ≅ M` receives a morphism from `M[n]` which is an isomorphism on `Hⁿ`.
* `isGE_standardDerivedGlobalSectionsUnit`, `isLE_standardDerivedGlobalSectionsUnit` —
  `RΓ(X, 𝒪_X)` lies in degrees `0` and `1`; the upper bound is `Hⁱ(X, 𝒪_X) = 0` for `i ≥ 2`.
* `standardHomologyIsoRightDerived` — `Hⁿ(RΓ(X, 𝒪_X)) ≅ Hⁿ(X, 𝒪_X)`.
* `nonempty_homologyIso_standardDerivedGlobalSectionsUnitShift_neg_two`,
  `nonempty_homologyIso_standardDerivedGlobalSectionsUnitShift_neg_one` — `H^{-2}` of the shift
  is `A`, because `f_*𝒪_X = 𝒪_{Spec A}` for a modification of a normal base, and `H^{-1}` is
  `H¹(X, 𝒪_X)`.
* `exists_triangle_data_standardDerivedGlobalSectionsUnitShift` — the components of the
  per-modification hypothesis of
  `Stacks.ResolutionOfSurfaces.isReductionToRationalSingularitiesPossible_of_triangle_data` that
  do not mention a dualizing complex, assembled.

## Implementation notes

*Which model.* The duality step is stated with `ModuleCat.hasDerivedCategory` erased and
`HasDerivedCategory.standard` installed, because the Matlis-dual comparison
`Dualizing.exists_naturalMatlisExtComparison` it rests on is at the standard model; so `C` must
be at the standard model, whose morphisms live one universe up. Two other spellings of
`RΓ(X, 𝒪_X)` are not at it: `AlgebraicGeometry.derivedGlobalSectionsStructureSheaf` of
`Vanishing/DerivedPushforwardStructureSheaf.lean` and
`AlgebraicGeometry.DualizingDivisor.derivedSections` of `DualizingDivisor/DerivedSections.lean`
both resolve `HasDerivedCategory (ModuleCat.{u} A)` to `ModuleCat.hasDerivedCategory`, the
locally small model, and nothing stated at them can be applied here. The standard-model spelling
is `AlgebraicGeometry.standardDerivedGlobalSectionsStructureSheaf` of
`Duality/StandardModelGlobalSections.lean`, and it is the object used below; the two readings are
not two objects, `AlgebraicGeometry.standardDerivedGlobalSectionsStructureSheafModelIso` carrying
the standard one to the locally small one along the comparison equivalence of the models.

What crosses is everything whose statement contains no derived category, and that is enough:
`AlgebraicGeometry.derivedGlobalSectionsOver` is an `abbrev` with the two models as instance
binders, and the two facts about it that are used —
`Stacks.DerivedFunctor.isZero_homologyFunctor_obj_derived_single` and
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` — carry their models as
binders too, so they hold at the standard model as stated. They are the same two facts from
which `isDerivedPushforwardStructureSheaf_derivedGlobalSectionsStructureSheaf` is built at the
other model. The remaining inputs are about Mathlib's `ℕ`-indexed right derived functors and
mention no derived category at all:
`AlgebraicGeometry.DualizingDivisor.isZero_rightDerived_globalSectionsOver_of_one_lt`
([Stacks, Tag 0B4X], clause (1)), `AlgebraicGeometry.modificationSecsOverUnitIso` (which is
`AlgebraicGeometry.IsModification.isIso_appTop`, `f_*𝒪_X = 𝒪_{Spec A}`),
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` and
`AlgebraicGeometry.DualizingDivisor.rightDerivedOneUnitIso`.

*The shift.* The two cohomology identifications of `RΓ(X, 𝒪_X)[2]` come from those of
`RΓ(X, 𝒪_X)` through `CategoryTheory.Functor.shiftIso` of the homology functor, which is the
shift sequence `Hⁱ(K[2]) ≅ H^{i+2}(K)`; the two concentration statements through
`CategoryTheory.Triangulated.TStructure.isGE_shift` and `isLE_shift`.

*The morphism `u`.* It is not canonical here: `H^{-2}(C) ≅ A` is produced as a `Nonempty`, and
`u` is built from a chosen such isomorphism through the truncation `τ^{<-1}C ≅ H^{-2}(C)[-2]` of
`Stacks.PurityRamification.nonempty_iso_singleFunctor_truncLT_succ` composed with
`τ^{<-1}C ⟶ C`, an isomorphism on `H^{-2}` by
`DerivedCategory.isIso_homologyMap_truncLTι_app`. So it too is produced existentially, which is
the shape the duality step asks for.

## References

* [Stacks Project, Tag 0B4S](https://stacks.math.columbia.edu/tag/0B4S)
* [Stacks Project, Tag 0B4X](https://stacks.math.columbia.edu/tag/0B4X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated Opposite

universe w u

namespace AlgebraicGeometry

/-! ### A morphism out of a single complex which is an isomorphism on cohomology -/

section Generic

variable {𝒜 : Type u} [Category.{w} 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- **An object of `D(𝒜)` with no cohomology below `n` and `Hⁿ ≅ M` receives a morphism from
`M[n]` which is an isomorphism on `Hⁿ`.** The truncation `τ^{<n+1}K` is `Hⁿ(K)[n]`
(`Stacks.PurityRamification.nonempty_iso_singleFunctor_truncLT_succ`) and the truncation
morphism `τ^{<n+1}K ⟶ K` is an isomorphism on `Hⁿ`. -/
theorem exists_hom_singleFunctor_of_homologyIso (K : DerivedCategory 𝒜) (n : ℤ) [K.IsGE n]
    (M : 𝒜) (e : (DerivedCategory.homologyFunctor 𝒜 n).obj K ≅ M) :
    ∃ u : (DerivedCategory.singleFunctor 𝒜 n).obj M ⟶ K,
      IsIso ((DerivedCategory.homologyFunctor 𝒜 n).map u) := by
  obtain ⟨e₁⟩ := Stacks.PurityRamification.nonempty_iso_singleFunctor_truncLT_succ K n
  have h₁ : IsIso ((DerivedCategory.homologyFunctor 𝒜 n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app K)) :=
    DerivedCategory.isIso_homologyMap_truncLTι_app (n + 1) n (by omega) K
  refine ⟨(DerivedCategory.singleFunctor 𝒜 n).map e.inv ≫ e₁.inv ≫
    (DerivedCategory.TStructure.t.truncLTι (n + 1)).app K, ?_⟩
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

end Generic

/-! ### `RΓ(X, 𝒪_X)` and `RΓ(X, 𝒪_X)[2]` at the standard model -/

section Shift

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`RΓ(X, 𝒪_X)` as an object of `D(A)` at the standard model**, the model the duality step of
[Stacks, Tag 0B4S] is stated at: the object
`AlgebraicGeometry.standardDerivedGlobalSectionsStructureSheaf`, under the name the rest of this
file uses it by. -/
def standardDerivedGlobalSectionsUnit : DerivedCategory (ModuleCat.{u} A) :=
  standardDerivedGlobalSectionsStructureSheaf f

/-- **`RΓ(X, 𝒪_X)[2]`**, the object `C` of the duality step of [Stacks, Tag 0B4S]: its cohomology
in degree `-2` is `Γ(X, 𝒪_X)` and in degree `-1` is `H¹(X, 𝒪_X)`. -/
def standardDerivedGlobalSectionsUnitShift : DerivedCategory (ModuleCat.{u} A) :=
  (standardDerivedGlobalSectionsUnit f)⟦(2 : ℤ)⟧

/-- **`Hⁿ(RΓ(X, 𝒪_X)) ≅ Hⁿ(X, 𝒪_X)`**, the `n`-th right derived functor of `A`-linear global
sections. -/
def standardHomologyIsoRightDerived (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj
        (standardDerivedGlobalSectionsUnit f) ≅
      ((globalSectionsOver f).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf) :=
  (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (globalSectionsOver f)
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
    (Scheme.Modules.exists_quasiIso_isKInjective X) n).app (SheafOfModules.unit X.ringCatSheaf)

/-- `RΓ(X, 𝒪_X)` has no cohomology in negative degrees. -/
theorem isGE_standardDerivedGlobalSectionsUnit :
    (standardDerivedGlobalSectionsUnit f).IsGE 0 :=
  (DerivedCategory.isGE_iff _ 0).2 fun i hi =>
    Stacks.DerivedFunctor.isZero_homologyFunctor_obj_derived_single (globalSectionsOver f)
      (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
      (Scheme.Modules.exists_quasiIso_isKInjective X) _ i hi

/-- `Hⁱ(RΓ(X, 𝒪_X)[2]) = H^{i+2}(RΓ(X, 𝒪_X))`. -/
def standardHomologyIsoShift (i j : ℤ) (h : 2 + i = j) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (standardDerivedGlobalSectionsUnitShift f) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        (standardDerivedGlobalSectionsUnit f) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso 2 i j h).app
    (standardDerivedGlobalSectionsUnit f)

variable [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]

/-- **`RΓ(X, 𝒪_X)` has no cohomology above degree one** on a modification of a two-dimensional
Noetherian normal local domain with normal source. This is
`AlgebraicGeometry.DualizingDivisor.isZero_rightDerived_globalSectionsOver_of_one_lt`
([Stacks, Tag 0B4X], clause (1)) read through `standardHomologyIsoRightDerived`. -/
theorem isLE_standardDerivedGlobalSectionsUnit [IsNormal X] (hdim : ringKrullDim A = 2)
    (hf : IsModification f) : (standardDerivedGlobalSectionsUnit f).IsLE 1 := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = (m : ℤ) := ⟨i.toNat, by omega⟩
  exact (DualizingDivisor.isZero_rightDerived_globalSectionsOver_of_one_lt hdim f hf
    (SheafOfModules.unit X.ringCatSheaf) m (by omega)).of_iso
      (standardHomologyIsoRightDerived f m)

omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] in
/-- `RΓ(X, 𝒪_X)[2]` has no cohomology below degree `-2`. -/
theorem isGE_standardDerivedGlobalSectionsUnitShift :
    (standardDerivedGlobalSectionsUnitShift f).IsGE (-2) := by
  have := isGE_standardDerivedGlobalSectionsUnit f
  exact DerivedCategory.TStructure.t.isGE_shift (standardDerivedGlobalSectionsUnit f) 0 2 (-2)
    (by norm_num)

/-- `RΓ(X, 𝒪_X)[2]` has no cohomology above degree `-1`. -/
theorem isLE_standardDerivedGlobalSectionsUnitShift [IsNormal X] (hdim : ringKrullDim A = 2)
    (hf : IsModification f) : (standardDerivedGlobalSectionsUnitShift f).IsLE (-1) := by
  have := isLE_standardDerivedGlobalSectionsUnit f hdim hf
  exact DerivedCategory.TStructure.t.isLE_shift (standardDerivedGlobalSectionsUnit f) 1 2 (-1)
    (by norm_num)

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- **`H^{-2}(RΓ(X, 𝒪_X)[2]) ≅ A`** for a modification of the spectrum of a normal domain: it is
`Γ(X, 𝒪_X)`, which is `A` because `f_*𝒪_X = 𝒪_{Spec A}`
(`AlgebraicGeometry.IsModification.isIso_appTop`, through
`AlgebraicGeometry.modificationSecsOverUnitIso`); the passage from `H⁰` of the derived functor to
the functor itself is `CategoryTheory.Functor.rightDerivedZeroIsoSelf`, available because
`A`-linear global sections is left exact. -/
theorem nonempty_homologyIso_standardDerivedGlobalSectionsUnitShift_neg_two
    (hf : IsModification f) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj
      (standardDerivedGlobalSectionsUnitShift f) ≅ ModuleCat.of A A) :=
  ⟨standardHomologyIsoShift f (-2) 0 (by norm_num) ≪≫
    standardHomologyIsoRightDerived f 0 ≪≫
    (globalSectionsOver f).rightDerivedZeroIsoSelf.app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    modificationSecsOverUnitIso f hf⟩

omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] in
/-- **`H^{-1}(RΓ(X, 𝒪_X)[2]) ≅ H¹(X, 𝒪_X)`**, the latter in the spelling
`AlgebraicGeometry.firstCohomologyAsBaseModule` that [Stacks, Tag 0B4N] uses. -/
theorem nonempty_homologyIso_standardDerivedGlobalSectionsUnitShift_neg_one [IsProper f]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).obj
      (standardDerivedGlobalSectionsUnitShift f) ≅ firstCohomologyAsBaseModule X f) :=
  ⟨standardHomologyIsoShift f (-1) 1 (by norm_num) ≪≫
    standardHomologyIsoRightDerived f 1 ≪≫
    DualizingDivisor.rightDerivedOneUnitIso (Over.mk f)⟩

/-- **The geometric input to the duality step of [Stacks, Tag 0B4S].** For a modification
`f : X ⟶ Spec(A)` with `X` normal, of a two-dimensional Noetherian normal local domain, the
object `C = RΓ(X, 𝒪_X)[2]` of `D(A)` has cohomology in the degrees `-2` and `-1` only, receives a
morphism `u : A[-2] ⟶ C` which is an isomorphism on `H^{-2}`, and has `H^{-1}(C) ≅ H¹(X, 𝒪_X)` of
finite length.

These are exactly the components of the per-modification hypothesis `hdata` of
`Stacks.ResolutionOfSurfaces.isReductionToRationalSingularitiesPossible_of_triangle_data` which
do not mention the dualizing complex; what that hypothesis asks beyond them is the vanishing of
`Hom(C[-1], ω_A^•)` — Grauert-Riemenschneider, [Stacks, Tag 0AXD], read through duality — and the
factorisation of `d · Hom(A[-2], ω_A^•)` through `u`, which is the tag's hypothesis on `d` read
through duality. -/
theorem exists_triangle_data_standardDerivedGlobalSectionsUnitShift [IsNormal X]
    (hdim : ringKrullDim A = 2) (hf : IsModification f) :
    ∃ (_ : (standardDerivedGlobalSectionsUnitShift f).IsGE (-2))
      (_ : (standardDerivedGlobalSectionsUnitShift f).IsLE (-1))
      (u : (DerivedCategory.singleFunctor (ModuleCat.{u} A) (-2)).obj (ModuleCat.of A A) ⟶
        standardDerivedGlobalSectionsUnitShift f),
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map u) ∧
      IsFiniteLength A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).obj
        (standardDerivedGlobalSectionsUnitShift f)) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).obj
        (standardDerivedGlobalSectionsUnitShift f) ≅ firstCohomologyAsBaseModule X f) := by
  have : IsProper f := hf.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hge := isGE_standardDerivedGlobalSectionsUnitShift f
  have hle := isLE_standardDerivedGlobalSectionsUnitShift f hdim hf
  obtain ⟨u, hu⟩ := exists_hom_singleFunctor_of_homologyIso
    (standardDerivedGlobalSectionsUnitShift f) (-2) (ModuleCat.of A A)
    (nonempty_homologyIso_standardDerivedGlobalSectionsUnitShift_neg_two f hf).some
  obtain ⟨e₁⟩ := nonempty_homologyIso_standardDerivedGlobalSectionsUnitShift_neg_one f
  have hinj : Function.Injective e₁.toLinearEquiv.toLinearMap := e₁.toLinearEquiv.injective
  exact ⟨hge, hle, u, hu,
    IsFiniteLength.of_injective (isFiniteLength_firstCohomologyAsBaseModule hdim f hf) hinj,
    ⟨e₁⟩⟩

end Shift

end AlgebraicGeometry

end
