module

public import StacksFrontier.Deformation.SquareZero.Torsor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.TwoTermComplex.BaseChange

/-!
# Base change of the first Ext group of the naive cotangent complex

Let `A' → A → B` be ring maps and let `N` be a `B`-module.  Regarding `N` as an `A`-module by
restriction of scalars, there are canonical identifications
```
Ext¹_A(NL_{A/A'}, N) = Ext¹_B(NL_{A/A'} ⊗^L_A B, N) = Ext¹_B(NL_{A/A'} ⊗_A B, N).
```
The first one is the adjunction between derived extension and derived restriction of scalars
(**Stacks 0GMT**).  The second one holds because `N`, placed in degree `0`, is shifted into
degree `-1` when it computes `Ext¹`, so that maps into it factor uniquely through the truncation
`τ_{≥ -1}`, and the termwise base change `NL_{A/A'} ⊗_A B` represents exactly
`τ_{≥ -1}(NL_{A/A'} ⊗^L_A B)` because the degree-zero term of `NL_{A/A'}` is flat
(**Stacks 0FUY**, the naive cotangent case of **Stacks 0G9G**).

## Main definitions

* `Stacks.Deformation.naiveCotangentCochainComplex`: the naive cotangent complex of `A` over `A'`
  read as a two-term cochain complex in cohomological degrees `-1` and `0`.
* `Stacks.Deformation.truncGEHomAddEquiv`: for a t-structure, maps out of a truncation
  `τ_{≥ n} X` into an object lying in degrees `≥ n` are the same as maps out of `X`.
* `Stacks.Deformation.derivedExtRestrictionModuleEquiv`: **Stacks 0GMT** read on extension
  groups, for an arbitrary coefficient module restricted along a ring map.

## Main results

* `Stacks.Deformation.naiveCotangentExtOneDerivedBaseChangeEquiv`: the first identification.
* `Stacks.Deformation.naiveCotangentDerivedBaseChangeExtOneEquiv`: the second identification.
* `Stacks.Deformation.naiveCotangentExtOneBaseChangeEquiv`: their composite.
* `Stacks.Deformation.naiveCotangentExtOneBaseChangeModuleEquiv`: the same composite with its
  left-hand side written as `Stacks.Deformation.naiveCotangentExtOne`.
* `Stacks.Deformation.flat_naiveCotangentCochainComplex_X_zero`: the degree-zero term of the
  two-term naive cotangent complex is flat, which is what feeds the second identification.

## Implementation notes

The remainder of the source remark discusses the maps
`NL_{A/A'} ⊗_A B → NL_{B/A'} → NL_{B/A}`, which it describes as "close to being" a distinguished
triangle and from which it draws conclusions only conditionally; that discussion is speculative
and is not formalized here.

The coefficient is an arbitrary object `M` of the module category over `B`; a `B`-module in any
universe yields such an object after a universe lift, which is how
`naiveCotangentExtOneBaseChangeModuleEquiv` is deduced.  Derived extension of scalars is the
chosen model `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, whose
universal property as a total left derived functor is what both halves consume.

The truncation index is `-1` because `Ext¹_B(X, M) = Hom_{D(B)}(X, M[0]⟦1⟧)` and `M[0]⟦1⟧` lies
in degrees `≥ -1`; so precomposition with `X → τ_{≥ -1} X` is bijective on maps into it.  The
two-term base change input is taken in the form **Stacks 0G9G**, applied to the two-term
presentation `HomologicalComplex.double` of `NL_{A/A'}` whose degree-zero term is the flat
cotangent space; **Stacks 0FUY** is that same statement for the mapping-cone presentation of the
same complex.

## References

* [Stacks Project, Tag 0GPY](https://stacks.math.columbia.edu/tag/0GPY)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0FUY](https://stacks.math.columbia.edu/tag/0FUY)
* [Stacks Project, Tag 0G9G](https://stacks.math.columbia.edu/tag/0G9G)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars

universe u₁ u₂ u₃ u₄ v

namespace Stacks.Deformation

attribute [local instance] HasDerivedCategory.standard

/-- Maps out of a truncation `τ_{≥ n} X` into an object lying in degrees `≥ n` are the same as
maps out of `X`, by precomposition with the truncation projection. -/
public noncomputable def truncGEHomAddEquiv {C : Type*} [Category C] [Preadditive C]
    [Limits.HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C]
    (t : Triangulated.TStructure C) (n : ℤ) (X Y : C) [t.IsGE Y n] :
    ((t.truncGE n).obj X ⟶ Y) ≃+ (X ⟶ Y) :=
  AddEquiv.ofBijective (Preadditive.leftComp Y ((t.truncGEπ n).app X))
    ⟨fun _ _ h ↦ t.from_truncGE_obj_ext h,
      fun g ↦ ⟨t.descTruncGE g n, t.π_descTruncGE g n⟩⟩

/-- Extension groups into a module restricted along `f : R →+* S` agree with extension groups
over `S` out of the derived extension of scalars.  This is the adjunction of Stacks 0GMT read on
Hom-groups, with the coefficient placed in degree `0`. -/
public noncomputable def derivedExtRestrictionModuleEquiv
    {R : Type u₂} {S : Type u₃} [CommRing R] [CommRing S] (f : R →+* S)
    (E : DerivedCategory (ModuleCat.{max u₂ u₃ v} R))
    (M : ModuleCat.{max u₂ u₃ v} S) (i : ℤ) :
    DerivedCategory.Ext E
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₂ u₃ v} R) 0).obj
          ((ModuleCat.restrictScalars f).obj M)) i ≃+
      DerivedCategory.Ext
        ((totalDerivedExtensionScalars.{u₂, u₃, v} f).functor.obj E)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₂ u₃ v} S) 0).obj M) i := by
  let Res := ModuleCat.restrictScalars.{max u₂ u₃ v} f
  let dRes := Res.mapDerivedCategory
  let D := totalDerivedExtensionScalars.{u₂, u₃, v} f
  let Y := (DerivedCategory.singleFunctor (ModuleCat.{max u₂ u₃ v} S) 0).obj M
  let e₀ := (Res.mapDerivedCategorySingleFunctor 0).app M
  let e : dRes.obj (Y⟦i⟧) ≅
      ((Res ⋙ DerivedCategory.singleFunctor (ModuleCat.{max u₂ u₃ v} R) 0).obj M)⟦i⟧ :=
    (dRes.commShiftIso i).app Y ≪≫ (shiftFunctor _ i).mapIso e₀
  let adj := @derivedExtensionScalarsAdjunction.{u₂, u₃, v} R S _ _ f _ _
    D.functor D.comparison D.isLeftDerived
  let postEquiv : AddEquiv (E ⟶ dRes.obj (Y⟦i⟧)) (E ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{max u₂ u₃ v} R) 0).obj (Res.obj M))⟦i⟧) := {
    toFun q := q ≫ e.hom
    invFun q := q ≫ e.inv
    left_inv q := by simp [Category.assoc]
    right_inv q := by simp [Category.assoc]
    map_add' q q' := by simp [Preadditive.add_comp] }
  exact postEquiv.symm.trans (adj.homAddEquiv E (Y⟦i⟧)).symm

/-- The naive cotangent complex `NL_{A/A'}` read as a two-term cochain complex of `A`-modules,
with `I/I²` in cohomological degree `-1` and `Ω_{A'[A]/A'} ⊗ A` in cohomological degree `0`,
both terms lifted into the module universe `max u₁ u₂ v`. -/
public noncomputable abbrev naiveCotangentCochainComplex (A' : Type u₁) (A : Type u₂)
    [CommRing A'] [CommRing A] [Algebra A' A] :
    CochainComplex (ModuleCat.{max u₁ u₂ v} A) ℤ :=
  HomologicalComplex.double
    ((((ModuleCat.uliftFunctor.{v} A).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.naiveCotangentComplex A' A)).d 1 0)
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)

/-- The degree-zero term of the two-term naive cotangent complex is flat, being a universe lift
of the cotangent space of the canonical presentation. -/
public theorem flat_naiveCotangentCochainComplex_X_zero (A' : Type u₁) (A : Type u₂)
    [CommRing A'] [CommRing A] [Algebra A' A] :
    Module.Flat A ((naiveCotangentCochainComplex.{u₁, u₂, v} A' A).X 0) := by
  have h₀ : Module.Flat A ((Algebra.naiveCotangentComplex A' A).X 0) :=
    Module.Flat.of_linearEquiv (HomologicalComplex.doubleXIso₁
      (ModuleCat.ofHom (Algebra.Generators.self A' A).toExtension.cotangentComplex)
      (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (by decide)).toLinearEquiv
  have h₁ : Module.Flat A
      ((((ModuleCat.uliftFunctor.{v} A).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (Algebra.naiveCotangentComplex A' A)).X 0) :=
    Module.Flat.of_linearEquiv
      (ULift.moduleEquiv (R := A) (M := ((Algebra.naiveCotangentComplex A' A).X 0)))
  exact Module.Flat.of_linearEquiv (HomologicalComplex.doubleXIso₁ _
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) (by decide)).toLinearEquiv

/-- **Stacks 0GPY**, first identification.  For `A' → A → B` and a `B`-module `M`, extension
classes of the naive cotangent complex of `A` over `A'` with coefficients in `M` regarded as an
`A`-module are the same as extension classes over `B` of its derived base change.  This is the
adjunction of Stacks 0GMT. -/
@[stacks 0GPY "Ext¹_A(NL_{A/A'}, N) = Ext¹_B(NL_{A/A'} ⊗^L_A B, N), via Tag 0GMT"]
public noncomputable def naiveCotangentExtOneDerivedBaseChangeEquiv
    (A' : Type u₁) (A : Type u₂) (B : Type u₃) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] (M : ModuleCat.{max u₁ u₂ u₃ v} B) :
    DerivedCategory.Ext
        (DerivedCategory.Q.obj (naiveCotangentCochainComplex.{u₁, u₂, max u₃ v} A' A))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ u₂ u₃ v} A) 0).obj
          ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) 1 ≃+
      DerivedCategory.Ext
        ((totalDerivedExtensionScalars.{u₂, u₃, max u₁ v} (algebraMap A B)).functor.obj
          (DerivedCategory.Q.obj (naiveCotangentCochainComplex.{u₁, u₂, max u₃ v} A' A)))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ u₂ u₃ v} B) 0).obj M) 1 :=
  derivedExtRestrictionModuleEquiv.{u₂, u₃, max u₁ v} (algebraMap A B)
    (DerivedCategory.Q.obj (naiveCotangentCochainComplex.{u₁, u₂, max u₃ v} A' A)) M 1

/-- **Stacks 0GPY**, second identification.  Extension classes over `B` out of the derived base
change of the naive cotangent complex are the same as extension classes out of its termwise base
change.  The coefficient `M`, placed in degree `0` and shifted into degree `-1`, only sees the
truncation `τ_{≥ -1}`, which the termwise base change computes by Stacks 0FUY. -/
@[stacks 0GPY "Ext¹_B(NL_{A/A'} ⊗^L_A B, N) = Ext¹_B(NL_{A/A'} ⊗_A B, N), via Tag 0FUY"]
public noncomputable def naiveCotangentDerivedBaseChangeExtOneEquiv
    (A' : Type u₁) (A : Type u₂) (B : Type u₃) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] (M : ModuleCat.{max u₁ u₂ u₃ v} B) :
    letI : (ModuleCat.extendScalars.{u₂, u₃, max u₁ u₂ u₃ v} (algebraMap A B)).IsLeftAdjoint :=
      ModuleCat.instIsLeftAdjointExtendScalars.{u₂, u₃, max u₁ u₂ v} (algebraMap A B)
    DerivedCategory.Ext
        ((totalDerivedExtensionScalars.{u₂, u₃, max u₁ v} (algebraMap A B)).functor.obj
          (DerivedCategory.Q.obj (naiveCotangentCochainComplex.{u₁, u₂, max u₃ v} A' A)))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ u₂ u₃ v} B) 0).obj M) 1 ≃+
      DerivedCategory.Ext
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u₂, u₃, max u₁ u₂ u₃ v}
            (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (naiveCotangentCochainComplex.{u₁, u₂, max u₃ v} A' A)))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ u₂ u₃ v} B) 0).obj M) 1 := by
  let L := naiveCotangentCochainComplex.{u₁, u₂, max u₃ v} A' A
  let D := totalDerivedExtensionScalars.{u₂, u₃, max u₁ v} (algebraMap A B)
  have hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → Limits.IsZero (L.X i) := fun i h₁ h₀ ↦
    HomologicalComplex.isZero_double_X _ _ i h₁ h₀
  have hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u₁ u₂ u₃ v} A) i).obj
        (DerivedCategory.Q.obj L)) := fun i h₁ h₀ ↦
    (HomologicalComplex.ExactAt.of_isZero (hL i h₁ h₀)).isZero_homology.of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u₁ u₂ u₃ v} A) i).app L)
  have key := @TwoTermComplex.twoTermBaseChange_iso_truncGE.{u₂, u₃, max u₁ v}
    A B _ _ (algebraMap A B) (DerivedCategory.Q.obj L) L (Iso.refl _) hK hL
    (flat_naiveCotangentCochainComplex_X_zero.{u₁, u₂, max u₃ v} A' A)
    D.functor D.comparison D.isLeftDerived
  let Y := (DerivedCategory.singleFunctor (ModuleCat.{max u₁ u₂ u₃ v} B) 0).obj M
  haveI : DerivedCategory.TStructure.t.IsGE (Y⟦(1 : ℤ)⟧) (-1) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 1 (-1) (by decide)
  exact (truncGEHomAddEquiv DerivedCategory.TStructure.t (-1)
      (D.functor.obj (DerivedCategory.Q.obj L)) (Y⟦(1 : ℤ)⟧)).symm.trans
    (extOneSourceIso (@asIso _ _ _ _ key.choose key.choose_spec.2))

/-- **Stacks 0GPY**.  For `A' → A → B` and a `B`-module `M`, the first extension group of the
naive cotangent complex of `A` over `A'` with coefficients in `M` regarded as an `A`-module is
canonically the first extension group over `B` of the termwise base change `NL_{A/A'} ⊗_A B`
with coefficients in `M`. -/
@[stacks 0GPY]
public noncomputable def naiveCotangentExtOneBaseChangeEquiv
    (A' : Type u₁) (A : Type u₂) (B : Type u₃) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] (M : ModuleCat.{max u₁ u₂ u₃ v} B) :
    letI : (ModuleCat.extendScalars.{u₂, u₃, max u₁ u₂ u₃ v} (algebraMap A B)).IsLeftAdjoint :=
      ModuleCat.instIsLeftAdjointExtendScalars.{u₂, u₃, max u₁ u₂ v} (algebraMap A B)
    DerivedCategory.Ext
        (DerivedCategory.Q.obj (naiveCotangentCochainComplex.{u₁, u₂, max u₃ v} A' A))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ u₂ u₃ v} A) 0).obj
          ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) 1 ≃+
      DerivedCategory.Ext
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u₂, u₃, max u₁ u₂ u₃ v}
            (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (naiveCotangentCochainComplex.{u₁, u₂, max u₃ v} A' A)))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ u₂ u₃ v} B) 0).obj M) 1 :=
  (naiveCotangentExtOneDerivedBaseChangeEquiv.{u₁, u₂, u₃, v} A' A B M).trans
    (naiveCotangentDerivedBaseChangeExtOneEquiv.{u₁, u₂, u₃, v} A' A B M)

/-- **Stacks 0GPY**, stated for a `B`-module `N` and the Ext group
`Stacks.Deformation.naiveCotangentExtOne`: the first extension group over `A` of the naive
cotangent complex of `A` over `A'` with coefficients in `N`, which is an `A`-module by
restriction of scalars, is the first extension group over `B` of `NL_{A/A'} ⊗_A B`. -/
@[stacks 0GPY "for a module `N` and the Ext group `naiveCotangentExtOne`"]
public noncomputable def naiveCotangentExtOneBaseChangeModuleEquiv
    (A' : Type u₁) (A : Type u₂) (B : Type u₃) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] (N : Type u₄) [AddCommGroup N] [Module B N] :
    letI : (ModuleCat.extendScalars.{u₂, u₃, max u₁ u₂ u₃ u₄} (algebraMap A B)).IsLeftAdjoint :=
      ModuleCat.instIsLeftAdjointExtendScalars.{u₂, u₃, max u₁ u₂ u₄} (algebraMap A B)
    letI : Module A (ULift.{u₃} N) := Module.compHom _ (algebraMap A B)
    naiveCotangentExtOne A' A (ULift.{u₃} N) ≃+
      DerivedCategory.Ext
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u₂, u₃, max u₁ u₂ u₃ u₄}
            (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (naiveCotangentCochainComplex.{u₁, u₂, max u₃ u₄} A' A)))
        ((DerivedCategory.singleFunctor (ModuleCat.{max u₁ u₂ u₃ u₄} B) 0).obj
          ((ModuleCat.uliftFunctor.{max u₁ u₂} B).obj
            (ModuleCat.of B (ULift.{u₃} N)))) 1 :=
  naiveCotangentExtOneBaseChangeEquiv.{u₁, u₂, u₃, u₄} A' A B
    ((ModuleCat.uliftFunctor.{max u₁ u₂} B).obj (ModuleCat.of B (ULift.{u₃} N)))

end Stacks.Deformation

end
