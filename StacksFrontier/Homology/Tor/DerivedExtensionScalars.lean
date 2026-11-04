module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Shift.Opposite
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.Opposite
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section


/-!
# Derived extension of scalars

Let `f : R →+* A` be a homomorphism of commutative rings. Extension of scalars
`M ↦ A ⊗_R M` is right exact but not exact, so it does not descend to the derived categories
as it stands; its left derived functor `- ⊗ᴸ_R A` does.

This file constructs that derived functor in two forms. On bounded-above derived categories it
is obtained without any choice of resolution: extension of scalars is right exact, its opposite
is left exact and carries projective modules to injective objects of the opposite category, so
the bounded-below right derived functor of the opposite functor exists, and derived duality
`D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)` transports it back to a functor `D⁻(R) ⥤ D⁻(A)`. On unbounded derived
categories it is the total left derived functor of degreewise extension of scalars, computed by
K-flat resolutions, which exist for every complex.

The two agree on bounded-above complexes, and both are computed by a bounded-above complex of
projectives and, more generally, by any K-flat complex.

The module and ring universes are independent throughout: a complex over `R` and a complex over
`A` have to live in a common module universe, which is therefore taken above both ring
universes.

## Main definitions

* `DerivedCategory.minusToPlusOp` and `DerivedCategory.plusOpToMinus`: derived duality read as
  an equivalence between the opposite of the bounded-above derived category of an abelian
  category and the bounded-below derived category of its opposite.
* `CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplex`: degreewise extension of
  scalars on complexes, followed by localization to the derived category.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalars`: the derived
  extension-of-scalars functor `D⁻(R) ⥤ D⁻(A)`.
* `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars`: the unbounded derived
  extension-of-scalars functor `D(R) ⥤ D(A)`, packaged with the comparison exhibiting it as the
  total left derived functor of degreewise extension of scalars, its exactness, its
  preservation of upper cohomological cutoffs, and the fact that bounded-above complexes of
  projectives and K-flat complexes compute it.
* `CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.extendsBounded`: its
  agreement with the bounded-above functor.
* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`: a choice of such a
  functor.

## Main results

* `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars_exists`: the unbounded
  derived extension-of-scalars functor exists, with all the structure above.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalars_isTriangulated`: the
  bounded-above functor is an exact functor of triangulated categories.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalars_maps_t_le`: it preserves each
  upper cohomological cutoff.
* `CochainComplex.DerivedExtensionScalars.derivedExtensionScalars_projective_model`: a
  bounded-above complex of projectives computes it.

## Implementation notes

The derived categories are **instance arguments** throughout — every declaration below takes
`[HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]` and
`[HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)]` — rather than being fixed by a file-level
`attribute [local instance] HasDerivedCategory.standard`. That matters because
`HasDerivedCategory` is `CategoryTheory.MorphismProperty.HasLocalization`, a class carrying
*data* (the localized category, the localization functor), so `DerivedCategory C` at two
instances is literally two different types and a functor constructed at the standard model says
nothing about any other. Keeping the models free is what lets consumers — in particular
`Dualizing.isDualizingComplex_localization` and the dualizing-complex development — speak of
derived extension of scalars at the locally small models of
`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean` and
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`.

The bounded-above functor `derivedExtensionScalars` is built through the duality
`D(𝒜)ᵒᵖ ≌ D(𝒜ᵒᵖ)`, so it also needs models of the derived categories of the **opposite** module
categories; it takes them as instance arguments too, as do `boundedExtensionIso` and
`TotalDerivedExtensionScalars.extendsBounded`, which compare it with the unbounded functor. The
structure `TotalDerivedExtensionScalars` does not involve those categories: its agreement with
the bounded-above functor is not a field but the construction
`TotalDerivedExtensionScalars.extendsBounded`, which follows from the comparison and its
invertibility on bounded-above complexes of projectives.

The unbounded construction goes through an abstract left derivability structure: the inclusion
of a class of objects which resolves every object of a category carrying a right calculus of
fractions is a left derivability structure, and a functor inverting the weak equivalences
between resolving objects therefore has a pointwise total left derived functor whose comparison
is invertible on the resolving class. Applied on the homotopy category with the K-flat complexes
as resolving class, this yields the derived functor; exactness comes from the same resolving
class, since the third object of a distinguished triangle on two K-flat complexes is K-flat.

The commutation with shifts of a left derived functor is obtained by reading the whole situation
in the opposite categories, where it becomes the commutation with shifts of a right derived
functor, which Mathlib provides.

Identifying `A ⊗_R -` with tensoring by the complex `A` concentrated in degree `0` requires the
tensor product of complexes of modules in a universe above the ring's; the tensor unit is then
`ULift R`, which is why the single-complex comparison is spelled out degreewise.

## References

* [The Stacks Project, Tag 064H](https://stacks.math.columbia.edu/tag/064H)
* [The Stacks Project, Tag 064F](https://stacks.math.columbia.edu/tag/064F)
* [The Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

universe uR uA u v w wR wA

namespace DerivedCategory

section Duality

variable (C : Type*) [Category* C] [Abelian C]
  [HasDerivedCategory C] [HasDerivedCategory Cᵒᵖ]

/-- Derived duality carries the opposite of the bounded-above category to the
bounded-below category of the opposite abelian category. -/
public def minusToPlusOp : (DerivedCategory.Minus C)ᵒᵖ ⥤ DerivedCategory.Plus Cᵒᵖ :=
  DerivedCategory.TStructure.t.plus.lift
    (DerivedCategory.Minus.ι.op ⋙ (DerivedCategory.derivedOpEquivalence (C := C)).functor)
    (fun X ↦ by
      obtain ⟨n, hn⟩ := X.unop.property
      refine ⟨-n, ?_⟩
      exact (DerivedCategory.isGE_derivedOpEquivalence_functor_obj_iff X.unop.obj n).2
        hn)

/-- The inverse derived duality carries bounded-below objects over the opposite category
to the opposite of the bounded-above category. -/
public def plusOpToMinus : DerivedCategory.Plus Cᵒᵖ ⥤ (DerivedCategory.Minus C)ᵒᵖ :=
  (DerivedCategory.TStructure.t.minus.lift
    ((DerivedCategory.Plus.ι ⋙ (DerivedCategory.derivedOpEquivalence (C := C)).inverse).leftOp)
    (fun X ↦ by
      obtain ⟨n, hn⟩ := X.unop.property
      refine ⟨-n, ?_⟩
      have : DerivedCategory.TStructure.t.IsGE
          ((𝟭 (DerivedCategory Cᵒᵖ)).obj X.unop.obj) n := hn
      have he := DerivedCategory.TStructure.t.isGE_of_iso
        ((DerivedCategory.derivedOpEquivalence (C := C)).counitIso.app X.unop.obj).symm n
      have hb := (DerivedCategory.isGE_derivedOpEquivalence_functor_obj_iff
        ((DerivedCategory.derivedOpEquivalence (C := C)).inverse.obj X.unop.obj).unop (-n)).1
        (by simpa using he)
      exact hb)).rightOp

end Duality

end DerivedCategory

namespace CochainComplex.DerivedExtensionScalars

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]

/-- Termwise extension of scalars on cochain complexes, followed by the localization functor to
the derived category. -/
public def extensionOfScalarsComplex (f : R →+* A)
    [HasDerivedCategory.{wA} (ModuleCat.{max uA (max uR v)} A)] :
    CochainComplex (ModuleCat.{max uA (max uR v)} R) ℤ ⥤
      DerivedCategory (ModuleCat.{max uA (max uR v)} A) := by
  letI : (ModuleCat.extendScalars.{uR, uA, max uA (max uR v)} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uA} f).isLeftAdjoint
  exact (ModuleCat.extendScalars.{uR, uA, max uA (max uR v)} f).mapHomologicalComplex
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Q


/-- **Stacks 064H.** Derived extension of scalars on bounded-above derived categories.
This is the dual of the bounded-below right derived functor of extension of scalars on
opposite module categories, where projective modules become injective objects. -/
@[stacks 064H, sga "4½ Rapport 4.1" "special case"]
public def derivedExtensionScalars (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max uA (max uR v)} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uA (max uR v)} A)]
    [HasDerivedCategory (ModuleCat.{max uA (max uR v)} R)ᵒᵖ]
    [HasDerivedCategory (ModuleCat.{max uA (max uR v)} A)ᵒᵖ] :
    DerivedCategory.Minus (ModuleCat.{max uA (max uR v)} R) ⥤
      DerivedCategory.Minus (ModuleCat.{max uA (max uR v)} A) := by
  letI : (ModuleCat.extendScalars.{uR, uA, max uA (max uR v)} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uA} f).isLeftAdjoint
  letI : (ModuleCat.extendScalars.{uR, uA, max uA (max uR v)} f).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits _; infer_instance)
  exact (DerivedCategory.minusToPlusOp (ModuleCat.{max uA (max uR v)} R) ⋙
    (ModuleCat.extendScalars.{uR, uA, max uA (max uR v)} f).op.rightDerivedFunctorPlus ⋙
    DerivedCategory.plusOpToMinus (ModuleCat.{max uA (max uR v)} A)).unop

/-- Termwise extension of scalars when the source and target rings live in independent
universes. -/
public def extensionOfScalarsComplexGeneral
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)] :
    CochainComplex (ModuleCat.{max v u w} R) ℤ ⥤
      DerivedCategory (ModuleCat.{max v u w} A) :=
  extensionOfScalarsComplex.{u, w, v, wA} f

/-- Degreewise extension of scalars, followed by localization, commutes with the translation
functors: extension of scalars is additive, so it acts degreewise on a shifted complex, and the
localization functor of the derived category commutes with shifts. -/
public instance extensionOfScalarsComplex_commShift (f : R →+* A)
    [HasDerivedCategory.{wA} (ModuleCat.{max uA (max uR v)} A)] :
    (extensionOfScalarsComplex.{uR, uA, v, wA} f).CommShift ℤ := by
  letI : (ModuleCat.extendScalars.{uR, uA, max uA (max uR v)} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uA} f).isLeftAdjoint
  letI : (ModuleCat.extendScalars.{uR, uA, max uA (max uR v)} f).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits _; infer_instance)
  exact inferInstanceAs
    (((ModuleCat.extendScalars.{uR, uA, max uA (max uR v)} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).CommShift ℤ)

/-- The same commutation with shifts for rings in independent universes. -/
public instance extensionOfScalarsComplexGeneral_commShift
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)] :
    (extensionOfScalarsComplexGeneral.{u, v, w, wA} f).CommShift ℤ :=
  extensionOfScalarsComplex_commShift.{u, w, v, wA} f

/-- The commutation with shifts of degreewise extension of scalars followed by localization is
the degreewise one followed by that of the localization functor. -/
public lemma extensionOfScalarsComplexGeneral_commShiftIso_hom_app
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)]
    [(ModuleCat.extendScalars.{u, w, max v u w} f).Additive]
    (n : ℤ) (X : CochainComplex (ModuleCat.{max v u w} R) ℤ) :
    ((extensionOfScalarsComplexGeneral.{u, v, w, wA} f).commShiftIso n).hom.app X =
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, w, max v u w} f).mapCochainComplexShiftIso n).hom.app X) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app
        (((ModuleCat.extendScalars.{u, w, max v u w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X) :=
  Functor.CommShift.comp_commShiftIso_hom_app
    ((ModuleCat.extendScalars.{u, w, max v u w} f).mapHomologicalComplex (ComplexShape.up ℤ))
    DerivedCategory.Q n X

/-- Total derived extension of scalars along `f : R →+* A`.

The comparison and its left-derived universal property characterize `functor` as
`- ⊗ᴸ_R A`. Its restriction to `D⁻(R) ⟶ D⁻(A)` is the bounded-above construction of
Equation 064H, as asserted in Section 06Y5: that is
`TotalDerivedExtensionScalars.extendsBounded`, which follows from the fields. -/
public structure TotalDerivedExtensionScalars
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)] where
  /-- The total derived extension-of-scalars functor. -/
  functor : DerivedCategory (ModuleCat.{max v u w} R) ⥤
    DerivedCategory (ModuleCat.{max v u w} A)
  /-- Derived extension of scalars is additive. -/
  additive : functor.Additive
  /-- Commutation with shifts, as in Lemma 06Y6. -/
  commShift : functor.CommShift ℤ
  /-- Exactness of derived change of rings (Lemma 06Y6). -/
  isTriangulated : letI := commShift; functor.IsTriangulated
  /-- The comparison from derived to termwise extension of scalars. -/
  comparison : DerivedCategory.Q ⋙ functor ⟶ extensionOfScalarsComplexGeneral.{u, v, w, wA} f
  /-- The comparison is compatible with the commutation with shifts: its component at a shifted
  complex is the shift of its component. Twisting `commShift` by signs leaves the other fields
  unchanged, so this does not follow from them. -/
  comparison_commShift : letI := commShift; NatTrans.CommShift comparison ℤ
  /-- The comparison exhibits `functor` as the total left derived functor of termwise extension
  of scalars. -/
  isLeftDerived : functor.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max v u w} R) (ComplexShape.up ℤ))
  /-- Preservation of each upper cohomological cutoff, by the dual of Lemma 05TC. -/
  maps_t_le (X : DerivedCategory (ModuleCat.{max v u w} R)) (n : ℤ)
    [X.IsLE n] : (functor.obj X).IsLE n
  /-- Bounded-above complexes of projectives compute derived extension of scalars, as in
  Section 064F and the proof of Lemma 0650. -/
  comparison_isIso_of_projective (P : CochainComplex (ModuleCat.{max v u w} R) ℤ)
    (n : ℤ) [P.IsStrictlyLE n] [∀ i, Projective (P.X i)] : IsIso (comparison.app P)
  /-- K-flat complexes compute derived extension of scalars: Section 06Y5 defines the functor as
  the left derived functor of termwise extension of scalars via K-flat resolutions. -/
  comparison_isIso_of_kFlat (P : CochainComplex (ModuleCat.{max v u w} R) ℤ)
    (hP : CochainComplex.KFlat.{u, max v w} P) : IsIso (comparison.app P)

attribute [instance] TotalDerivedExtensionScalars.additive
  TotalDerivedExtensionScalars.commShift TotalDerivedExtensionScalars.isTriangulated
  TotalDerivedExtensionScalars.isLeftDerived TotalDerivedExtensionScalars.comparison_commShift

/-- Preserving every upper cutoff implies preservation of bounded-above objects. -/
public theorem TotalDerivedExtensionScalars.maps_boundedAbove
    {R : Type u} {A : Type w} [CommRing R] [CommRing A]
    [HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)]
    {f : R →+* A} (D : TotalDerivedExtensionScalars.{u, v, w, wR, wA} f)
    (X : DerivedCategory.Minus (ModuleCat.{max v u w} R)) :
    DerivedCategory.TStructure.t.minus (D.functor.obj X.obj) := by
  obtain ⟨n, hn⟩ := X.property
  have := hn
  exact ⟨n, D.maps_t_le X.obj n⟩

/-- The derived extension-of-scalars functor restricted to bounded-above derived categories. -/
public def TotalDerivedExtensionScalars.boundedAboveFunctor
    {R : Type u} {A : Type w} [CommRing R] [CommRing A]
    [HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)]
    {f : R →+* A} (D : TotalDerivedExtensionScalars.{u, v, w, wR, wA} f) :
    DerivedCategory.Minus (ModuleCat.{max v u w} R) ⥤
      DerivedCategory.Minus (ModuleCat.{max v u w} A) :=
  DerivedCategory.TStructure.t.minus.lift
    (DerivedCategory.Minus.ι ⋙ D.functor) D.maps_boundedAbove

/-- The restriction of derived extension of scalars to bounded-above derived categories is
additive. -/
public instance TotalDerivedExtensionScalars.boundedAboveFunctor_additive
    {R : Type u} {A : Type w} [CommRing R] [CommRing A]
    [HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)]
    {f : R →+* A} (D : TotalDerivedExtensionScalars.{u, v, w, wR, wA} f) :
    D.boundedAboveFunctor.Additive := by
  dsimp [boundedAboveFunctor]
  infer_instance

/-- The bounded-above derived extension-of-scalars functor agrees with the total derived functor
after applying the inclusions into the unbounded derived categories. -/
public def TotalDerivedExtensionScalars.boundedAboveFunctorCompInclusionIso
    {R : Type u} {A : Type w} [CommRing R] [CommRing A]
    [HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)]
    {f : R →+* A} (D : TotalDerivedExtensionScalars.{u, v, w, wR, wA} f) :
    D.boundedAboveFunctor ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ D.functor :=
  Iso.refl _

section TotalDerivedConstruction

open CategoryTheory.Functor CategoryTheory.Pretriangulated CategoryTheory.LocalizerMorphism


universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Precomposition which is fully faithful on functor categories preserves the right Kan
universal property. -/
public lemma isRightKanExtension_precomp_of_fullyFaithful
    {C C' D H : Type*} [Category C] [Category C'] [Category D] [Category H]
    (E : C' ⥤ C) [((whiskeringLeft C' C H).obj E).Full]
    [((whiskeringLeft C' C H).obj E).Faithful]
    (L : C ⥤ D) (F : C ⥤ H) (G : D ⥤ H) (α : L ⋙ G ⟶ F)
    [G.IsRightKanExtension α] :
    G.IsRightKanExtension ((Functor.associator E L G).hom ≫ whiskerLeft E α) := by
  have : (RightExtension.precomp L F E).IsEquivalence := by
    dsimp only [RightExtension.precomp]
    infer_instance
  let h := (IsTerminal.isTerminalIffObj (RightExtension.precomp L F E)
    (RightExtension.mk G α)).1 (G.isUniversalOfIsRightKanExtension α)
  exact ⟨⟨IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl G))⟩⟩




section Op

variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]



attribute [local simp] opCounit_app




end Op

section Shift
variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (LF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : L ⋙ LF ⟶ F) (W : MorphismProperty C) [L.IsLocalization W]
  [LF.IsLeftDerivedFunctor α W]
  (B : Type*) [AddGroup B] [HasShift C B] [HasShift D B] [HasShift H B]
  [W.IsCompatibleWithShift B] [F.CommShift B] [L.CommShift B]
set_option backward.isDefEq.respectTransparency false in
/-- A total left derived functor commutes with the shift functors, as soon as the functor it
derives and the localization functor do and the weak equivalences are stable under shift.
Read in the opposite categories this is the corresponding statement for a right derived
functor. -/
@[instance_reducible]
private def leftDerivedCommShift : LF.CommShift B := by
  let Wo : MorphismProperty (OppositeShift C B) := W.op
  let Lo := OppositeShift.functor B L
  let Fo := OppositeShift.functor B F
  let LFo := OppositeShift.functor B LF
  let αo : Fo ⟶ Lo ⋙ LFo := NatTrans.op α
  have : Lo.IsLocalization Wo := inferInstanceAs (L.op.IsLocalization W.op)
  have : Wo.IsCompatibleWithShift B := ⟨fun b => by
    ext X Y f
    exact MorphismProperty.IsCompatibleWithShift.iff W f.unop b⟩
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension LF α W
  have : LFo.IsRightDerivedFunctor αo Wo := ⟨isLeftKanExtension_op LF α⟩
  let : LFo.CommShift B := Functor.IsRightDerivedFunctor.commShift LFo αo Wo B
  exact Functor.commShiftUnop B LF

set_option backward.isDefEq.respectTransparency false in
/-- The counit of a total left derived functor is compatible with the commutation with shifts of
`leftDerivedCommShift`. -/
private lemma leftDerivedCommShift_compatibility :
    let := leftDerivedCommShift LF α W B
    NatTrans.CommShift α B := by
  let Wo : MorphismProperty (OppositeShift C B) := W.op
  let Lo := OppositeShift.functor B L
  let Fo := OppositeShift.functor B F
  let LFo := OppositeShift.functor B LF
  let αo : Fo ⟶ Lo ⋙ LFo := NatTrans.op α
  have : Lo.IsLocalization Wo := inferInstanceAs (L.op.IsLocalization W.op)
  have : Wo.IsCompatibleWithShift B := ⟨fun b => by
    ext X Y f
    exact MorphismProperty.IsCompatibleWithShift.iff W f.unop b⟩
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension LF α W
  have : LFo.IsRightDerivedFunctor αo Wo := ⟨isLeftKanExtension_op LF α⟩
  let : LFo.CommShift B := Functor.IsRightDerivedFunctor.commShift LFo αo Wo B
  let := leftDerivedCommShift LF α W B
  refine ⟨fun b => ?_⟩
  ext X
  have h := congrArg Quiver.Hom.unop
    (Functor.IsRightDerivedFunctor.comp_map_commShiftIso_hom_app LFo αo Wo B b
      (Opposite.op X))
  change ((LF.commShiftIso b).inv.app (L.obj X) ≫
      LF.map ((L.commShiftIso b).inv.app X)) ≫ α.app (X⟦b⟧) =
    (α.app X)⟦b⟧' ≫ (F.commShiftIso b).inv.app X at h
  dsimp
  rw [Functor.commShiftIso_comp_hom_app, ← cancel_epi (LF.map ((L.commShiftIso b).inv.app X)),
    ← cancel_epi ((LF.commShiftIso b).inv.app (L.obj X))]
  simp only [Category.assoc, ← LF.map_comp_assoc, Iso.inv_hom_id_app,
    LF.map_id, Category.id_comp]
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Functor.comp_obj,
    Category.comp_id] using
    (h =≫ (F.commShiftIso b).hom.app X).symm
end Shift

section TensorSingle
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open MonoidalCategory
attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive
/-- Tensoring the complex `N` concentrated in degree `0` with `C` has vanishing antidiagonal
summands away from the row `0`. -/
theorem single_tlmHC_zsumm {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R)
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ) (i₁ i₂ : ℤ) (h : i₁ ≠ 0) :
    Limits.IsZero
      ((((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{max u v} R)) ℤ ℤ).obj
        ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N).X).obj C.X) (i₁, i₂)) := by
  have hz : Limits.IsZero
      (((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N).X i₁) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N i₁ h
  show Limits.IsZero (((curriedTensor (ModuleCat.{max u v} R)).obj
      (((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N).X i₁)).obj (C.X i₂))
  rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
  have : Subsingleton (TensorProduct R
      (↥(((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N).X i₁))
      (↥(C.X i₂))) :=
    Unique.instSubsingleton
  exact this

/-- An antidiagonal index with first coordinate `0` is the index `(0, j)`. -/
private theorem antidiagonal_eq_zero_left {j : ℤ}
    (b : ↑((fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {j})) (hi : b.1.1 = 0) :
    b = ⟨(0, j), by simp⟩ := by
  obtain ⟨⟨i₁, i₂⟩, hb⟩ := b
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb hi
  subst hi
  simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
  omega

/-- Auxiliary: the surviving `(0, j)` antidiagonal summand of `single₀ N ⊗ C` equals the degree-`j`
object of the degreewise complex `(tensorLeft N).mapHomologicalComplex C`. -/
theorem single_tlmHC_objeq {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R)
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ) (j : ℤ)
    (b : ↑((fun x : ℤ × ℤ => x.1 + x.2) ⁻¹' {j})) (hi : b.1.1 = 0) :
    (((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{max u v} R)) ℤ ℤ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N).X).obj C.X).mapObjFun
        (fun x => x.1 + x.2) j b
    = (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).X j := by
  obtain rfl := antidiagonal_eq_zero_left b hi
  rfl

/-- Per-degree component iso for Step A: the colimit-collapse of the antidiagonal coproduct
(all summands but `(0, j)` are zero) identifies `(single₀ N ⊗ C).X j` with `(N ⊗ C.X j)`. -/
noncomputable def single_tlmHC_comps {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R)
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ) (j : ℤ) :
    ((TleftCochain ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N)).obj
        C).X j
      ≅ (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).X
        j := by
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z : GradedObject (ℤ × ℤ) (ModuleCat.{max u v} R) :=
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{max u v} R)) ℤ ℤ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N).X).obj C.X
  let RHS : ModuleCat.{max u v} R := (((tensorLeft N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C).X j
  have iLHS : IsColimit (Z.cofanMapObj p j) := Z.isColimitCofanMapObj p j
  have h0 : p (0, j) = j := by change (0:ℤ) + j = j; ring
  let injFn : (b : ↑(p ⁻¹' {j})) → Z.mapObjFun p j b ⟶ RHS :=
    fun b => if hi : b.1.1 = 0 then eqToHom (single_tlmHC_objeq N C j b hi) else 0
  refine
    { hom := Cofan.IsColimit.desc iLHS injFn
      inv := Z.ιMapObj p (0, j) j h0
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Cofan.IsColimit.hom_ext iLHS
    intro b
    rw [← Category.assoc, Cofan.IsColimit.fac iLHS injFn b]
    erw [Category.comp_id]
    by_cases hi : b.1.1 = 0
    · obtain ⟨⟨i₁, i₂⟩, hb⟩ := b
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb
      dsimp only [p] at hb
      simp only at hi
      subst hi
      have hj : i₂ = j := by omega
      subst hj
      change injFn ⟨(0, i₂), _⟩ ≫ Z.ιMapObj p (0, i₂) i₂ h0 = (Z.cofanMapObj p i₂).inj ⟨(0, i₂), _⟩
      simp only [injFn, dite_eq_left]
      rw [show (eqToHom (single_tlmHC_objeq N C i₂ ⟨(0, i₂), hb⟩ rfl)) = 𝟙 _ from rfl,
          Category.id_comp]
      rfl
    · exact (single_tlmHC_zsumm N C b.1.1 b.1.2 hi).eq_of_src _ _
  · rw [show Z.ιMapObj p (0, j) j h0 = (Z.cofanMapObj p j).inj ⟨(0, j), h0⟩ from rfl,
      Cofan.IsColimit.fac iLHS injFn ⟨(0, j), h0⟩]
    change injFn ⟨(0, j), h0⟩ = 𝟙 RHS
    simp only [injFn, dite_eq_left]
    rfl

/-- Differential compatibility for Step A: the per-degree component isos
`single_tlmHC_comps` commute with the total differential of `single₀ N ⊗ C` (whose `d₁` part
vanishes, the single complex having zero differential) and the degreewise differential of
`(tensorLeft N).mapHomologicalComplex C` (the `d₂` part with Koszul sign `ε₂(0, ·)=1`). -/
theorem single_tlmHC_comm {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R)
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (single_tlmHC_comps N C i).hom ≫ (((tensorLeft N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).d i j
      = ((TleftCochain ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj
          N)).obj C).d i j
        ≫ (single_tlmHC_comps N C j).hom := by
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z : GradedObject (ℤ × ℤ) (ModuleCat.{max u v} R) :=
    ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{max u v} R)) ℤ ℤ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N).X).obj C.X
  have iLHS : IsColimit (Z.cofanMapObj p i) := Z.isColimitCofanMapObj p i
  apply Cofan.IsColimit.hom_ext iLHS
  intro b
  by_cases hi : b.1.1 = 0
  · obtain rfl := antidiagonal_eq_zero_left b hi
    obtain rfl : i + 1 = j := hij
    have hb : (0:ℤ) + i = i := zero_add i
    rw [← Category.assoc]
    have hL : (Z.cofanMapObj p i).inj ⟨(0, i), hb⟩ ≫ (single_tlmHC_comps N C i).hom = 𝟙 _ := by
      have he : (Z.cofanMapObj p i).inj ⟨(0, i), hb⟩ = (single_tlmHC_comps N C i).inv := rfl
      rw [he]; exact (single_tlmHC_comps N C i).inv_hom_id
    rw [hL, Category.id_comp]
    rw [← Category.assoc]
    have hR : (Z.cofanMapObj p i).inj ⟨(0, i), hb⟩
        ≫ ((TleftCochain ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj
            N)).obj C).d i (i+1)
      = HomologicalComplex.ιMapBifunctor
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N) C
          (curriedTensor (ModuleCat.{max u v} R)) (ComplexShape.up ℤ) 0 i i hb
        ≫ (HomologicalComplex.mapBifunctor
            ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N) C
            (curriedTensor (ModuleCat.{max u v} R)) (ComplexShape.up ℤ)).d i (i+1) :=
                rfl
    rw [hR]
    have hrel1 : (ComplexShape.up ℤ).Rel (0:ℤ) 1 := by change (0:ℤ)+1 = 1; ring
    have hrel2 : (ComplexShape.up ℤ).Rel i (i+1) := by change i+1 = i+1; ring
    have hπ1 :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ((0:ℤ)+1, i) = i+1 := by
      show (1:ℤ) + i = i+1; ring
    have hπ2 :
        (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ((0:ℤ), i+1) = i+1 := by
      show (0:ℤ) + (i+1) = i+1; ring
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
        HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hrel1 i (i+1) hπ1,
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0 hrel2 (i+1) hπ2]
    rw [CochainComplex.singleFunctor_obj_d N 0 0 1]
    simp only [Functor.map_zero, Limits.zero_app, Limits.zero_comp, smul_zero, zero_add]
    rw [show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (0, i) = 1 from rfl,
        one_smul, Category.assoc]
    rw [show HomologicalComplex.ιMapBifunctor ((CochainComplex.singleFunctor (ModuleCat.{max u v} R)
        0).obj N) C
          (curriedTensor (ModuleCat.{max u v} R)) (ComplexShape.up ℤ) 0 (i+1) (i+1) hπ2
        ≫ (single_tlmHC_comps N C (i+1)).hom = 𝟙 _ from (single_tlmHC_comps N C (i+1)).inv_hom_id]
    rw [Category.comp_id]
    rfl
  · exact (single_tlmHC_zsumm N C b.1.1 b.1.2 hi).eq_of_src _ _

set_option maxHeartbeats 1000000 in
-- Identifying the total-complex components unfolds the lifted tensor structure.
/-- The total complex of `single₀ N ⊗ C` is the degreewise tensor product `N ⊗ C`: in each degree
the antidiagonal coproduct collapses onto its single nonzero summand. -/
private def singleTensorObjIso {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R)
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (TleftCochain ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj
        N)).obj C
      ≅ ((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj C :=
  HomologicalComplex.Hom.isoOfComponents (fun j => single_tlmHC_comps N C j)
    (fun i j hij => single_tlmHC_comm N C i j hij)


/-- Tensoring with the complex `N` concentrated in degree `0` and totalizing is naturally
isomorphic to tensoring degreewise with the module `N`. -/
private def singleTensorIso {R : Type u} [CommRing R] (N : ModuleCat.{max u v} R) :
    TleftCochain ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N) ≅
      (tensorLeft N).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun K => singleTensorObjIso N K)
    (fun {K L} g => by
      apply (cancel_epi (singleTensorObjIso N K).inv).1
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      ext i : 1
      change HomologicalComplex.ιMapBifunctor
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N) K
          (curriedTensor (ModuleCat.{max u v} R)) (.up ℤ) 0 i i (zero_add i) ≫
          ((TleftCochain _).map g).f i ≫ (single_tlmHC_comps N L i).hom =
        (tensorLeft N).map (g.f i)
      change HomologicalComplex.ιMapBifunctor
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} R) 0).obj N) K
          (curriedTensor (ModuleCat.{max u v} R)) (.up ℤ) 0 i i (zero_add i) ≫
          (HomologicalComplex.mapBifunctorMap (𝟙 _ ) g
            (curriedTensor (ModuleCat.{max u v} R)) (.up ℤ)).f i ≫ _ = _
      rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
      dsimp only [HomologicalComplex.id_f]
      erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
      change _ ≫ (single_tlmHC_comps N L i).inv ≫
          (single_tlmHC_comps N L i).hom = _
      simp only [Iso.inv_hom_id, Category.comp_id]
      rfl)

end TensorSingle

section BaseChange
variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
open MonoidalCategory
set_option backward.isDefEq.respectTransparency false
/-- Extension of scalars along `f : R →+* A` followed by restriction of scalars is tensoring with
`A`, viewed as an `R`-module in the common module universe. -/
private def extensionUnderlyingIso (f : R →+* A) :
    let := ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA} (R := R)
    let := ModuleCat.liftedModuleMonoidal.{uR, max v uA} (R := R)
    let : Module R A := Module.compHom A f
    tensorLeft (ModuleCat.of R (ULift.{max uR v} A)) ≅
      ModuleCat.extendScalars.{uR, uA, max v uR uA} f ⋙ ModuleCat.restrictScalars f := by
  let : Module R A := Module.compHom A f
  refine NatIso.ofComponents (fun M => ?_) ?_
  · exact (TensorProduct.congr (ULift.moduleEquiv : ULift.{max uR v} A ≃ₗ[R] A)
      (LinearEquiv.refl R M)).toModuleIso
  · intro M N g
    ext : 1
    apply TensorProduct.ext'
    intro a m
    rfl

/-- Degreewise tensoring with a module preserves a quasi-isomorphism between K-flat complexes. -/
private lemma quasiIso_tensorLeft_map
    (N : ModuleCat.{max uR v} R)
    {K L : CochainComplex (ModuleCat.{max uR v} R) ℤ} (g : K ⟶ L) [QuasiIso g]
    (hK : CochainComplex.KFlat.{uR, v} K) (hL : CochainComplex.KFlat.{uR, v} L) :
    QuasiIso (((tensorLeft N).mapHomologicalComplex (.up ℤ)).map g) := by
  let e := singleTensorIso N
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality g).symm)).1
    (CochainComplex.DerivedTensor.quasiIso_tleftCochain_map.{uR, v} g hK hL
      ((CochainComplex.singleFunctor (ModuleCat.{max uR v} R) 0).obj N))

/-- Degreewise extension of scalars preserves a quasi-isomorphism between K-flat complexes: it
is tensoring with `A` up to restriction of scalars, which reflects quasi-isomorphism. -/
private lemma quasiIso_extendScalars_map (f : R →+* A)
    {K L : CochainComplex (ModuleCat.{max v uR uA} R) ℤ} (g : K ⟶ L) [QuasiIso g]
    (hK : CochainComplex.KFlat.{uR, max v uA} K)
    (hL : CochainComplex.KFlat.{uR, max v uA} L) :
    let : (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max v uR, uR, uA} f).isLeftAdjoint
    QuasiIso (((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
      (.up ℤ)).map g) := by
  let : (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR, uR, uA} f).isLeftAdjoint
  let : Module R A := Module.compHom A f
  let := ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA} (R := R)
  let := ModuleCat.liftedModuleMonoidal.{uR, max v uA} (R := R)
  let := ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA} (R := R)
  let N : ModuleCat.{max v uR uA} R := ModuleCat.of R (ULift.{max uR v} A)
  let e := NatIso.mapHomologicalComplex (extensionUnderlyingIso.{uR, uA, v} f) (.up ℤ)
  have h' := (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality g).symm)).1
      (quasiIso_tensorLeft_map N g hK hL)
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (ModuleCat.restrictScalars f)).1 h'

/-- Every object of the homotopy category receives a quasi-isomorphism from a K-flat complex. -/
private lemma exists_kFlat_resolution_homotopy
    (X : HomotopyCategory (ModuleCat.{max uR v} R) (.up ℤ)) :
    ∃ (Y : HomotopyCategory (ModuleCat.{max uR v} R) (.up ℤ))
      (_ : CochainComplex.KFlat.{uR, v} Y.as) (s : Y ⟶ X),
      HomotopyCategory.quasiIso (ModuleCat.{max uR v} R) (.up ℤ) s := by
  obtain ⟨K, s, hK, _, hs, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution X.as
  exact ⟨(HomotopyCategory.quotient _ _).obj K, hK,
    (HomotopyCategory.quotient _ _).map s,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩

/-- On the homotopy category, degreewise extension of scalars followed by localization inverts a
quasi-isomorphism between K-flat complexes. -/
private lemma isIso_extendScalars_homotopy_map (f : R →+* A)
    [Eadd : (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).Additive]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    {X Y : HomotopyCategory (ModuleCat.{max v uR uA} R) (.up ℤ)} (g : X ⟶ Y)
    (hg : HomotopyCategory.quasiIso (ModuleCat.{max v uR uA} R) (.up ℤ) g)
    (hX : CochainComplex.KFlat.{uR, max v uA} X.as)
    (hY : CochainComplex.KFlat.{uR, max v uA} Y.as) :
    IsIso (((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).map g) := by
  have : QuasiIso g.out :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff g.out).1 (by
      rwa [HomotopyCategory.quotient_map_out g])
  have h := quasiIso_extendScalars_map f g.out hX hY
  apply (DerivedCategory.isIso_Qh_map_iff _).2
  rw [← HomotopyCategory.quotient_map_out g, Functor.mapHomotopyCategory_map]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 h

/-- Degreewise extension of scalars, read on the homotopy category and followed by localization,
has a total left derived functor whose counit is invertible on K-flat complexes. The K-flat
complexes resolve every object, so they form a left derivability structure. -/
private lemma exists_leftDerivedExtension (f : R →+* A)
    [(ModuleCat.extendScalars.{uR, uA, max v uR uA} f).Additive]
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)] :
    ∃ (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
        DerivedCategory (ModuleCat.{max v uR uA} A))
      (α : DerivedCategory.Qh ⋙ F ⟶
        (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh),
      F.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso _ (.up ℤ)) ∧
      ∀ K : HomotopyCategory (ModuleCat.{max v uR uA} R) (.up ℤ),
        CochainComplex.KFlat.{uR, max v uA} K.as → IsIso (α.app K) := by
  let W := HomotopyCategory.quasiIso (ModuleCat.{max v uR uA} R) (.up ℤ)
  let P : ObjectProperty (HomotopyCategory (ModuleCat.{max v uR uA} R) (.up ℤ)) :=
    fun K => CochainComplex.KFlat.{uR, max v uA} K.as
  let U := (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh
  have hP := exists_kFlat_resolution_homotopy.{uR, max v uA} (R := R)
  have := LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions W P hP U
    (isIso_extendScalars_homotopy_map f)
  exact ⟨U.totalLeftDerived DerivedCategory.Qh W,
    U.totalLeftDerivedCounit DerivedCategory.Qh W, inferInstance,
    LeftDerivedByResolutions.isIso_app_of_resolutions W P hP U
      (isIso_extendScalars_homotopy_map f) DerivedCategory.Qh _ _⟩

/-- K-flatness is stable under cones: if two of the three objects of a distinguished triangle in
the homotopy category are K-flat, so is the third. -/
private lemma kFlat_third_of_distinguished
    (T : Pretriangulated.Triangle
      (HomotopyCategory (ModuleCat.{max uR v} R) (.up ℤ)))
    (hT : T ∈ distTriang _) (h₁ : CochainComplex.KFlat.{uR, v} T.obj₁.as)
    (h₂ : CochainComplex.KFlat.{uR, v} T.obj₂.as) :
    CochainComplex.KFlat.{uR, v} T.obj₃.as := by
  intro M hM
  obtain ⟨c, hc⟩ := TotalTensorComplex.tleft_isTriangulated M
  let := c
  have := hc
  have hTM := (Tleft M).map_distinguished T hT
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    (ObjectProperty.ext_of_isTriangulatedClosed₃
      (HomotopyCategory.subcategoryAcyclic (ModuleCat.{max uR v} R)) _ hTM
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (h₁ M hM))
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (h₂ M hM)))

/-- The left derived functor of degreewise extension of scalars is exact: every morphism of the
derived category is, up to isomorphism, the image of a morphism between K-flat complexes,
whose cone is again K-flat, and the counit is invertible there. -/
private lemma isTriangulated_leftDerivedExtension (f : R →+* A)
    [(ModuleCat.extendScalars.{uR, uA, max v uR uA} f).Additive]
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (α : DerivedCategory.Qh ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [F.CommShift ℤ] [NatTrans.CommShift α ℤ]
    (hα : ∀ K : HomotopyCategory (ModuleCat.{max v uR uA} R) (.up ℤ),
      CochainComplex.KFlat.{uR, max v uA} K.as → IsIso (α.app K)) :
    F.IsTriangulated := by
  let W := HomotopyCategory.quasiIso (ModuleCat.{max v uR uA} R) (.up ℤ)
  let P : ObjectProperty (HomotopyCategory (ModuleCat.{max v uR uA} R) (.up ℤ)) :=
    fun K => CochainComplex.KFlat.{uR, max v uA} K.as
  have : (LeftDerivedByResolutions.inclusionLocalizerMorphism W P).HasLeftResolutions :=
    fun X => by
      obtain ⟨Y, hY, s, hs⟩ := exists_kFlat_resolution_homotopy.{uR, max v uA} X
      exact ⟨{ X₁ := ⟨Y, hY⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism W P
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι W P
  have : (P.ι ⋙ DerivedCategory.Qh).IsLocalization (W.inverseImage P.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism W P) DerivedCategory.Qh
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    (P.ι ⋙ DerivedCategory.Qh) (W.inverseImage P.ι)
  apply Functor.isTriangulated_of_rightExtension F α
  intro X Y g
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := (P.ι ⋙ DerivedCategory.Qh).mapArrow) (Arrow.mk g)
  obtain ⟨Z, u, v, hT⟩ := Pretriangulated.distinguished_cocone_triangle (P.ι.map a.hom)
  let T := Pretriangulated.Triangle.mk (P.ι.map a.hom) u v
  have h₁ := a.left.property
  have h₂ := a.right.property
  exact ⟨T, hT, hα _ h₁, hα _ h₂,
    hα _ (kFlat_third_of_distinguished.{uR, max v uA} T hT h₁ h₂), ⟨ea⟩⟩

/-- A comparison invertible on K-flat complexes is invertible on bounded-above complexes of
projectives, projective modules being flat. -/
private lemma comparison_projective_of_kFlat (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (α : DerivedCategory.Q ⋙ F ⟶ extensionOfScalarsComplexGeneral.{uR, v, uA, wA} f)
    (hα : ∀ K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA} K → IsIso (α.app K))
    (P : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (n : ℤ)
    [P.IsStrictlyLE n] [∀ i, Projective (P.X i)] : IsIso (α.app P) := by
  have : ∀ i, Module.Flat R (P.X i) := fun _ => inferInstance
  exact hα P (CochainComplex.KFlat.kFlat_of_flat.{uR, max v uA} P n)

/-- A comparison invertible on bounded-above complexes of projectives forces the derived functor
to preserve every upper cohomological cutoff. -/
private lemma maps_t_le_of_comparison_projective (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (α : DerivedCategory.Q ⋙ F ⟶ extensionOfScalarsComplexGeneral.{uR, v, uA, wA} f)
    (hα : ∀ (P : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (n : ℤ),
      P.IsStrictlyLE n → (∀ i, Projective (P.X i)) → IsIso (α.app P))
    (X : DerivedCategory (ModuleCat.{max v uR uA} R)) (n : ℤ) [X.IsLE n] :
    (F.obj X).IsLE n := by
  let E := ModuleCat.extendScalars.{uR, uA, max v uR uA} f
  let : E.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR, uR, uA} f).isLeftAdjoint
  let P : ObjectProperty (ModuleCat.{max v uR uA} R) := fun M => Projective M
  have : P.ContainsZero := ⟨ModuleCat.of R (Fin 0 → ULift.{max v uA} R),
    ModuleCat.isZero_of_subsingleton _, inferInstance⟩
  have hP : ∀ M : ModuleCat.{max v uR uA} R,
      ∃ (N : ModuleCat.{max v uR uA} R) (_ : P N) (p : N ⟶ M), Epi p :=
    fun M => ⟨Projective.over M, inferInstance, Projective.π M, inferInstance⟩
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE n
  have := hK
  obtain ⟨L, π, _, hπ, hL, hn⟩ := (CochainComplex.exists_quasiIso_prop P hP n).1 K
  have := hπ
  have := hn
  have := hα L n hn hL
  have hLE : CochainComplex.IsStrictlyLE ((E.mapHomologicalComplex (.up ℤ)).obj L) n :=
    inferInstance
  have hQ : ((extensionOfScalarsComplexGeneral.{uR, v, uA, wA} f).obj L).IsLE n := by
    show (DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj L)).IsLE n
    infer_instance
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((F.mapIso (e ≪≫ (asIso (DerivedCategory.Q.map π)).symm)) ≪≫ asIso (α.app L)).symm n

end BaseChange
section ComplexComparison
set_option backward.isDefEq.respectTransparency false
/-- A comparison from a functor on the derived category to a functor on complexes which is
invertible on K-flat complexes exhibits the former as the total left derived functor of the
latter, provided the functor on complexes factors through the homotopy category. -/
private lemma isLeftDerivedFunctor_of_isIso_on_kFlat
    {R : Type u} [CommRing R] {H : Type*} [Category H]
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    (U : CochainComplex (ModuleCat.{max u v} R) ℤ ⥤ H)
    (Uh : HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ) ⥤ H)
    (e : HomotopyCategory.quotient _ _ ⋙ Uh ≅ U)
    (F : DerivedCategory (ModuleCat.{max u v} R) ⥤ H)
    (β : DerivedCategory.Q ⋙ F ⟶ U)
    (hβ : ∀ K : CochainComplex (ModuleCat.{max u v} R) ℤ,
      CochainComplex.KFlat.{u, v} K → IsIso (β.app K)) :
    F.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso _ (.up ℤ)) := by
  let Q := HomotopyCategory.quotient (ModuleCat.{max u v} R) (.up ℤ)
  let q := DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} R)
  let T := (whiskeringLeft _ _ H).obj Q
  have : T.Full := inferInstanceAs
    (((whiskeringLeft _ _ H).obj (CategoryTheory.Quotient.functor (homotopic _ _))).Full)
  let α₀ : Q ⋙ (DerivedCategory.Qh ⋙ F) ⟶ Q ⋙ Uh :=
    whiskerRight q.hom F ≫ β ≫ e.inv
  let α : DerivedCategory.Qh ⋙ F ⟶ Uh := T.preimage α₀
  have hα₀ : whiskerLeft Q α = α₀ := T.map_preimage α₀
  have hα : ∀ X : HomotopyCategory (ModuleCat.{max u v} R) (.up ℤ),
      CochainComplex.KFlat.{u, v} X.as → IsIso (α.app X) := by
    intro X hX
    have he : α.app X = α₀.app X.as := NatTrans.congr_app hα₀ X.as
    rw [he]
    have := hβ X.as hX
    dsimp [α₀]
    infer_instance
  have hUh : ∀ {X Y} (s : X ⟶ Y), HomotopyCategory.quasiIso _ (.up ℤ) s →
      CochainComplex.KFlat.{u, v} X.as → CochainComplex.KFlat.{u, v} Y.as →
        IsIso (Uh.map s) := by
    intro X Y s hs hX hY
    have := hα X hX
    have := hα Y hY
    have : IsIso (DerivedCategory.Qh.map s) := (DerivedCategory.isIso_Qh_map_iff s).2 hs
    rw [← isIso_comp_left_iff (α.app X), ← α.naturality s]
    dsimp only [Functor.comp_map]
    infer_instance
  have := LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))
    (fun X => CochainComplex.KFlat.{u, v} X.as)
    (exists_kFlat_resolution_homotopy.{u, v} (R := R))
    Uh hUh DerivedCategory.Qh F α hα
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension F α
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} R) (.up ℤ))
  have hk := isRightKanExtension_precomp_of_fullyFaithful Q DerivedCategory.Qh Uh F α
  have hke : F.IsRightKanExtension (whiskerRight q.hom F ≫ β) := by
    apply (Functor.isRightKanExtension_iff_of_iso₂
      ((Functor.associator Q DerivedCategory.Qh F).hom ≫ whiskerLeft Q α)
      (whiskerRight q.hom F ≫ β) e (Iso.refl F) ?_).mp hk
    rw [hα₀]
    ext X
    simp [α₀]
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  apply (Functor.isRightKanExtension_iff_postcomp₁ (𝟭 _)
    ((Q ⋙ DerivedCategory.Qh).rightUnitor ≪≫ q) β).2
  have := hke
  apply Functor.isRightKanExtension_of_iso F.leftUnitor.symm
    (whiskerRight q.hom F ≫ β)
  ext X
  simp only [comp_obj, Iso.symm_hom, Iso.trans_hom, whiskerRight_comp, Category.assoc,
    NatTrans.comp_app, id_obj, whiskerLeft_app, leftUnitor_inv_app, associator_inv_app,
    whiskerRight_app, rightUnitor_hom_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.id_comp _


end ComplexComparison
open DerivedCategory HomotopyCategory


section DualityComparison

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory Aᵒᵖ] [HasDerivedCategory Bᵒᵖ]

attribute [local instance] DerivedCategory.isLocalization_opQ
  HomotopyCategory.isLocalization_opQuotient


variable (F : A ⥤ B) [F.Additive]


end DualityComparison

section Transport

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory Aᵒᵖ] [HasDerivedCategory Bᵒᵖ]

attribute [local instance] DerivedCategory.isLocalization_opQ
  HomotopyCategory.isLocalization_opQuotient


variable (F : A ⥤ B) [F.Additive]


variable (LF : DerivedCategory A ⥤ DerivedCategory B)
  (α : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)







end Transport

section PlusComparison
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
set_option backward.isDefEq.respectTransparency false
/-- A functor on the unbounded derived category which receives an invertible comparison from a
left exact functor on bounded-below complexes of injectives agrees with the bounded-below
right derived functor after including into the unbounded derived category. -/
private def rightDerivedPlusCompIso (G : C ⥤ D) [G.Additive]
    (H : DerivedCategory C ⥤ DerivedCategory D)
    (α : G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ H)
    (hα : ∀ K : HomotopyCategory.Plus (InjectiveObject C),
      IsIso (α.app (((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj K).obj))) :
    G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ H := by
  let I := (InjectiveObject.ι C).mapHomotopyCategoryPlus
  let E := I ⋙ DerivedCategory.Plus.Qh
  have hKI : ∀ K : HomotopyCategory.Plus (InjectiveObject C),
      CochainComplex.IsKInjective (I.obj K).obj.as := by
    intro K
    obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff K.obj.as).1 K.property
    have := hn
    have : CochainComplex.IsStrictlyGE (I.obj K).obj.as n := by
      change CochainComplex.IsStrictlyGE
        (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj K.obj.as) n
      infer_instance
    exact CochainComplex.isKInjective_of_injective _ n
  have hbij : ∀ K L, Function.Bijective (E.map : (K ⟶ L) → _) := fun K L =>
    (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective (I.obj K) (I.obj L) (hKI L)).comp
      ⟨I.map_injective, I.map_surjective⟩
  have : E.Full := ⟨fun f => (hbij _ _).surjective f⟩
  have : E.Faithful := ⟨fun h => (hbij _ _).injective h⟩
  have : E.IsEquivalence := {}
  let U := I ⋙ G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι
  let β : U ⟶ E ⋙ (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) :=
    whiskerRight (whiskerLeft I G.rightDerivedFunctorPlusUnit) DerivedCategory.Plus.ι
  let γ : U ⟶ E ⋙ (DerivedCategory.Plus.ι ⋙ H) :=
    whiskerLeft (I ⋙ HomotopyCategory.Plus.ι C) α
  have : IsIso β := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    dsimp [β]
    infer_instance
  have : IsIso γ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact hα K
  let T := (whiskeringLeft _ _ (DerivedCategory D)).obj E
  have : T.Full := inferInstance
  have : T.Faithful := inferInstance
  exact T.preimageIso ((asIso β).symm ≪≫ asIso γ)
end PlusComparison

section BoundedComparison
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory Cᵒᵖ] [HasDerivedCategory Dᵒᵖ]
set_option backward.isDefEq.respectTransparency false
/-- The transported unit of a left derived functor is invertible on bounded-below complexes of
injective objects of the opposite category: those are the opposites of bounded-above
complexes of projectives, where the original counit is invertible by hypothesis. -/
private lemma isIso_opAlphaTransport_injective (G : C ⥤ D) [G.Additive]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (α : DerivedCategory.Qh ⋙ F ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hα : ∀ (P : CochainComplex C ℤ) (n : ℤ), P.IsStrictlyLE n →
      (∀ i, Projective (P.X i)) → IsIso (α.app ((HomotopyCategory.quotient _ _).obj P)))
    (K : HomotopyCategory.Plus (InjectiveObject Cᵒᵖ)) :
    IsIso ((opAlphaTransport G F α).app
      (((InjectiveObject.ι Cᵒᵖ).mapHomotopyCategoryPlus.obj K).obj)) := by
  let M := (((InjectiveObject.ι Cᵒᵖ).mapHomotopyCategoryPlus.obj K).obj).as
  let L := ((CochainComplex.opEquivalence C).inverse.obj M).unop
  obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff K.obj.as).1 K.property
  have := hn
  have hM : CochainComplex.IsStrictlyGE M n := by
    show CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι Cᵒᵖ).mapHomologicalComplex (.up ℤ)).obj K.obj.as) n
    infer_instance
  have hL : L.IsStrictlyLE (-n) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    show IsZero (M.X (-i)).unop
    exact (CochainComplex.isZero_of_isStrictlyGE M n (-i) (by omega)).unop
  have hproj : ∀ i, Projective (L.X i) := by
    intro i
    show Projective (M.X (-i)).unop
    have : Injective (M.X (-i)) := inferInstanceAs
      (Injective ((((InjectiveObject.ι Cᵒᵖ).mapHomotopyCategoryPlus.obj K).obj).as.X (-i)))
    infer_instance
  have := hα L (-n) hL hproj
  let e : ((homotopyOpEquivalence (C := C)).inverse.obj
      ((HomotopyCategory.quotient _ _).obj M)).unop ≅
      (HomotopyCategory.quotient _ _).obj L :=
    ((homotopyOpEquivalence (C := C)).inverse.mapIso
      ((HomotopyCategory.quotient _ _).mapIso
        ((CochainComplex.opEquivalence C).counitIso.app M))).unop ≪≫
      unopInverseObjQuotientIso L
  exact (isIso_opAlphaTransport_app_iff G F α _).2
    ((NatTrans.isIso_app_iff_of_iso α e).2 inferInstance)

/-- A left derived functor whose counit is invertible on bounded-above complexes of projectives
is, read in the opposite categories, the bounded-below right derived functor of the opposite
functor. -/
private def opLFPlusIso [EnoughProjectives C] (G : C ⥤ D) [G.Additive]
    (F : DerivedCategory C ⥤ DerivedCategory D)
    (α : DerivedCategory.Qh ⋙ F ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hα : ∀ (P : CochainComplex C ℤ) (n : ℤ), P.IsStrictlyLE n →
      (∀ i, Projective (P.X i)) → IsIso (α.app ((HomotopyCategory.quotient _ _).obj P))) :
    G.op.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ opLF F :=
  rightDerivedPlusCompIso G.op (opLF F) (opAlphaTransport G F α)
    (isIso_opAlphaTransport_injective G F α hα)
end BoundedComparison

section Construction
variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
set_option backward.isDefEq.respectTransparency false

/-- The bounded-above derived extension-of-scalars functor is the restriction of any left
derived functor of degreewise extension of scalars whose counit is invertible on
bounded-above complexes of projectives. -/
private def boundedExtensionIso (f : R →+* A)
    [(ModuleCat.extendScalars.{uR, uA, max v uR uA} f).Additive]
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    [HasDerivedCategory (ModuleCat.{max v uR uA} R)ᵒᵖ]
    [HasDerivedCategory (ModuleCat.{max v uR uA} A)ᵒᵖ]
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (α : DerivedCategory.Qh ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    (hα : ∀ (P : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (n : ℤ),
      P.IsStrictlyLE n → (∀ i, Projective (P.X i)) →
        IsIso (α.app ((HomotopyCategory.quotient _ _).obj P))) :
    derivedExtensionScalars.{uR, uA, v, wR, wA} f ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ F := by
  let C := ModuleCat.{max v uR uA} R
  let D := ModuleCat.{max v uR uA} A
  let G := ModuleCat.extendScalars.{uR, uA, max v uR uA} f
  let eC := derivedOpEquivalence (C := C)
  let eD := derivedOpEquivalence (C := D)
  let T := DerivedCategory.minusToPlusOp C ⋙ G.op.rightDerivedFunctorPlus ⋙
    DerivedCategory.plusOpToMinus D
  let i : DerivedCategory.plusOpToMinus D ⋙ DerivedCategory.Minus.ι.op ⋙ eD.functor ≅
      DerivedCategory.Plus.ι := by
    change DerivedCategory.Plus.ι ⋙ eD.inverse ⋙ eD.functor ≅ DerivedCategory.Plus.ι
    exact isoWhiskerLeft DerivedCategory.Plus.ι eD.counitIso ≪≫
      (Functor.rightUnitor _)
  let e₁ : (derivedExtensionScalars.{uR, uA, v, wR, wA} f ⋙ DerivedCategory.Minus.ι).op ⋙
      eD.functor ≅ DerivedCategory.minusToPlusOp C ⋙
        (G.op.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) :=
    isoWhiskerRight T.unopOpIso (DerivedCategory.Minus.ι.op ⋙ eD.functor) ≪≫
      isoWhiskerLeft (DerivedCategory.minusToPlusOp C ⋙ G.op.rightDerivedFunctorPlus) i
  let e₂ : DerivedCategory.minusToPlusOp C ⋙ (DerivedCategory.Plus.ι ⋙ opLF F) ≅
      (DerivedCategory.Minus.ι ⋙ F).op ⋙ eD.functor := by
    change DerivedCategory.Minus.ι.op ⋙ eC.functor ⋙ eC.inverse ⋙ F.op ⋙ eD.functor ≅
      DerivedCategory.Minus.ι.op ⋙ F.op ⋙ eD.functor
    exact isoWhiskerLeft DerivedCategory.Minus.ι.op (eC.funInvIdAssoc (F.op ⋙ eD.functor))
  let e := e₁ ≪≫ isoWhiskerLeft (DerivedCategory.minusToPlusOp C) (opLFPlusIso G F α hα) ≪≫ e₂
  let W := (whiskeringRight (DerivedCategory.Minus C)ᵒᵖ (DerivedCategory D)ᵒᵖ
    (DerivedCategory Dᵒᵖ)).obj eD.functor
  exact NatIso.removeOp (W.preimageIso e.symm)

/-- **The unbounded functor extends Equation 064H**, as asserted in Section 06Y5: on
bounded-above objects a total derived extension of scalars agrees with the bounded-above
functor `derivedExtensionScalars`. Its comparison, read on the homotopy category, is invertible
on bounded-above complexes of projectives, which is what `boundedExtensionIso` needs. -/
-- The body names `private` helpers, so it must not be exposed to importers.
@[no_expose]
public def TotalDerivedExtensionScalars.extendsBounded {f : R →+* A}
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    [HasDerivedCategory (ModuleCat.{max v uR uA} R)ᵒᵖ]
    [HasDerivedCategory (ModuleCat.{max v uR uA} A)ᵒᵖ]
    (D : TotalDerivedExtensionScalars.{uR, v, uA, wR, wA} f) :
    derivedExtensionScalars.{uR, uA, v, wR, wA} f ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ D.functor := by
  let E := ModuleCat.extendScalars.{uR, uA, max v uR uA} f
  let : E.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR, uR, uA} f).isLeftAdjoint
  have : E.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits E; infer_instance)
  let Q := HomotopyCategory.quotient (ModuleCat.{max v uR uA} R) (.up ℤ)
  let T := (whiskeringLeft _ _ (DerivedCategory (ModuleCat.{max v uR uA} A))).obj Q
  have : T.Full := inferInstanceAs
    (((whiskeringLeft _ _ _).obj (CategoryTheory.Quotient.functor (homotopic _ _))).Full)
  let e : Q ⋙ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      extensionOfScalarsComplexGeneral.{uR, v, uA, wA} f :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft (E.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso (ModuleCat.{max v uR uA} A))
  let α₀ : Q ⋙ (DerivedCategory.Qh ⋙ D.functor) ⟶
      Q ⋙ (E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :=
    whiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{max v uR uA} R)).hom D.functor ≫
      D.comparison ≫ e.inv
  refine boundedExtensionIso f D.functor (T.preimage α₀) fun P n _ _ => ?_
  have he : (T.preimage α₀).app (Q.obj P) = α₀.app P := NatTrans.congr_app (T.map_preimage α₀) P
  have := D.comparison_isIso_of_projective P n
  rw [he]
  dsimp [α₀]
  infer_instance

/-- Unbounded derived extension of scalars exists: there is a functor `D(R) ⥤ D(A)` which is
the total left derived functor of degreewise extension of scalars, is exact, preserves every
upper cohomological cutoff, and is computed by bounded-above complexes of projectives and by
K-flat complexes. It restricts on bounded-above objects to `derivedExtensionScalars`:
`TotalDerivedExtensionScalars.extendsBounded`. -/
@[sga "5 X 3.4" "special case"]
public theorem totalDerivedExtensionScalars_exists (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)] :
    Nonempty (TotalDerivedExtensionScalars.{uR, v, uA, wR, wA} f) := by
  let E := ModuleCat.extendScalars.{uR, uA, max v uR uA} f
  let : E.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR, uR, uA} f).isLeftAdjoint
  have : E.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits E; infer_instance)
  obtain ⟨F, α, hF, hα⟩ := exists_leftDerivedExtension.{uR, uA, v} f
  have := hF
  let W := HomotopyCategory.quasiIso (ModuleCat.{max v uR uA} R) (.up ℤ)
  let cF : F.CommShift ℤ := leftDerivedCommShift F α W ℤ
  have : NatTrans.CommShift α ℤ := leftDerivedCommShift_compatibility F α W ℤ
  have htri : F.IsTriangulated := isTriangulated_leftDerivedExtension f F α hα
  let Q := HomotopyCategory.quotient (ModuleCat.{max v uR uA} R) (.up ℤ)
  let U := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let q := DerivedCategory.quotientCompQhIso (ModuleCat.{max v uR uA} R)
  let e : Q ⋙ U ≅ extensionOfScalarsComplexGeneral.{uR, v, uA, wA} f :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft (E.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso (ModuleCat.{max v uR uA} A))
  let β : DerivedCategory.Q ⋙ F ⟶ extensionOfScalarsComplexGeneral.{uR, v, uA, wA} f :=
    whiskerRight q.inv F ≫ (Functor.associator Q DerivedCategory.Qh F).hom ≫
      whiskerLeft Q α ≫ e.hom
  have hqcs : NatTrans.CommShift q.inv ℤ :=
    inferInstanceAs (NatTrans.CommShift
      (DerivedCategory.quotientCompQhIso (ModuleCat.{max v uR uA} R)).inv ℤ)
  have hecs : NatTrans.CommShift e.hom ℤ := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
    infer_instance
  have hβcs : NatTrans.CommShift β ℤ := by
    simp only [β]
    infer_instance
  have hβ : ∀ K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA} K → IsIso (β.app K) := by
    intro K hK
    have := hα (Q.obj K) hK
    dsimp [β]
    infer_instance
  have hLE : ∀ (X : DerivedCategory (ModuleCat.{max v uR uA} R)) (n : ℤ),
      X.IsLE n → (F.obj X).IsLE n := by
    intro X n hn
    have := hn
    apply maps_t_le_of_comparison_projective f F β _ X n
    intro P m hP hproj
    have := hP
    have := hproj
    exact comparison_projective_of_kFlat f F β hβ P m
  exact ⟨{
    functor := F
    additive := inferInstance
    commShift := cF
    isTriangulated := htri
    comparison := β
    comparison_commShift := hβcs
    isLeftDerived := isLeftDerivedFunctor_of_isIso_on_kFlat _ U e F β hβ
    maps_t_le := fun X n hX => hLE X n hX
    comparison_isIso_of_projective := fun P n _ _ =>
      comparison_projective_of_kFlat f F β hβ P n
    comparison_isIso_of_kFlat := hβ }⟩

end Construction

end TotalDerivedConstruction

/-- A choice of unbounded derived extension of scalars along `f`. -/
public def totalDerivedExtensionScalars (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)] :
    TotalDerivedExtensionScalars.{uR, v, uA, wR, wA} f :=
  Classical.choice (totalDerivedExtensionScalars_exists f)

/-- Unbounded derived extension of scalars for rings in independent universes. -/
public def derivedExtensionScalarsGeneral
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)] :
    TotalDerivedExtensionScalars.{u, v, w, wR, wA} f :=
  totalDerivedExtensionScalars.{u, w, v, wR, wA} f

/-- The bounded-above functor commutes with shifts, transported along its agreement with the
unbounded functor. -/
public instance derivedExtensionScalars_commShift (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    [HasDerivedCategory (ModuleCat.{max v uR uA} R)ᵒᵖ]
    [HasDerivedCategory (ModuleCat.{max v uR uA} A)ᵒᵖ] :
    (derivedExtensionScalars.{uR, uA, v, wR, wA} f).CommShift ℤ :=
  Functor.CommShift.ofComp
    (totalDerivedExtensionScalars.{uR, uA, v, wR, wA} f).extendsBounded ℤ

/-- Exactness of the bounded-above functor, transported from Lemma 06Y6. -/
public instance derivedExtensionScalars_isTriangulated (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    [HasDerivedCategory (ModuleCat.{max v uR uA} R)ᵒᵖ]
    [HasDerivedCategory (ModuleCat.{max v uR uA} A)ᵒᵖ] :
    (derivedExtensionScalars.{uR, uA, v, wR, wA} f).IsTriangulated := by
  have : NatTrans.CommShift
      (totalDerivedExtensionScalars.{uR, uA, v, wR, wA} f).extendsBounded.hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ ℤ
  exact (Functor.isTriangulated_iff_comp_right
    (totalDerivedExtensionScalars.{uR, uA, v, wR, wA} f).extendsBounded).2 inferInstance

/-- The bounded-above functor preserves each upper cohomological cutoff (the dual of 05TC). -/
public theorem derivedExtensionScalars_maps_t_le (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    [HasDerivedCategory (ModuleCat.{max v uR uA} R)ᵒᵖ]
    [HasDerivedCategory (ModuleCat.{max v uR uA} A)ᵒᵖ]
    (X : DerivedCategory.Minus (ModuleCat.{max uA (max uR v)} R)) (n : ℤ)
    [X.obj.IsLE n] : ((derivedExtensionScalars f).obj X).obj.IsLE n := by
  have : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.Minus.ι ⋙
        (totalDerivedExtensionScalars.{uR, uA, v, wR, wA} f).functor).obj X)
      n := (totalDerivedExtensionScalars.{uR, uA, v, wR, wA} f).maps_t_le X.obj n
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((totalDerivedExtensionScalars.{uR, uA, v, wR, wA} f).extendsBounded.app X).symm n

/-- A bounded-above complex of projectives computes bounded-above derived extension of
scalars: its image is the degreewise extension of scalars of the complex. -/
public theorem derivedExtensionScalars_projective_model (f : R →+* A)
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR uA} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v uR uA} A)]
    [HasDerivedCategory (ModuleCat.{max v uR uA} R)ᵒᵖ]
    [HasDerivedCategory (ModuleCat.{max v uR uA} A)ᵒᵖ]
    (P : CochainComplex (ModuleCat.{max uA (max uR v)} R) ℤ)
    (hP : DerivedCategory.TStructure.t.minus (DerivedCategory.Q.obj P))
    (hb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hp : ∀ i : ℤ, Projective (P.X i)) :
    Nonempty (((derivedExtensionScalars f).obj ⟨DerivedCategory.Q.obj P, hP⟩).obj ≅
      (extensionOfScalarsComplex f).obj P) := by
  obtain ⟨n, hn⟩ := hb
  have : P.IsStrictlyLE n := (CochainComplex.isStrictlyLE_iff P n).2 hn
  have := hp
  let D := totalDerivedExtensionScalars.{uR, uA, v, wR, wA} f
  have hIso : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P n
  exact ⟨D.extendsBounded.app ⟨DerivedCategory.Q.obj P, hP⟩ ≪≫
    @asIso _ _ _ _ (D.comparison.app P) hIso⟩

end CochainComplex.DerivedExtensionScalars

end
