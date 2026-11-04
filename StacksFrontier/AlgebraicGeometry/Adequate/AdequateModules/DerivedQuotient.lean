module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedRestriction

/-!
# The quotient of the derived category of adequate modules by the parasitic part

Let `S` be a scheme and let `f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites
of [Stacks, Tag 070U]. Write `𝒞` for the parasitic adequate `𝒪`-modules and `D_𝒞(𝒪)` for the
complexes in `D_Adeq(𝒪)` with parasitic cohomology, which is the kernel of `Rf_*`. This file
carries [Stacks, Tag 070X]: the equivalence of derived categories

  `D_Adeq(𝒪)/D_𝒞(𝒪) ⟶ D_QCoh(S)`.

The source deduces it from the derived adjunction `Lf^* ⊣ Rf_*` with `Rf_* Lf^* ≅ id` of
[Stacks, Tag 070W] in three steps: `D_𝒞(𝒪)` is the kernel of `Rf_*`, so the functor descends;
the counit `Lf^*Rf_*X ⟶ X` becomes an isomorphism in the quotient, since `Rf_*` carries it to a
quasi-isomorphism; and `Hom_{D_Adeq(𝒪)/D_𝒞(𝒪)}(X, Y) ⟶ Hom_{D_QCoh(S)}(Rf_*X, Rf_*Y)` is
bijective because `Lf^*` provides an inverse. Those three steps are exactly the statement that
`Rf_*` is a localization functor, and they are available for an arbitrary right adjoint with a
fully faithful left adjoint.

## Main definitions

* `Stacks.Adequate.BigSite.fullyFaithfulDerivedAdequatePullback` — `Lf^*` is fully faithful,
  which is `Rf_* Lf^* ≅ id` of [Stacks, Tag 070W] read on the unit of the adjunction.
* `Stacks.Adequate.BigSite.derivedAdequateQuotientEquivalence` — [Stacks, Tag 070X], the
  equivalence of the localization of `D_Adeq(𝒪)` at the morphisms inverted by `Rf_*` with
  `D_QCoh(S)`.
* `Stacks.Adequate.BigSite.derivedParasiticQuotientEquivalence` — [Stacks, Tag 070X] in the
  source's own form `D_Adeq(𝒪)/D_𝒞(𝒪) ≌ D_QCoh(S)`, the quotient being taken at the morphisms
  whose cone lies in the kernel of `Rf_*`.

## Main results

* `CategoryTheory.ObjectProperty.trW_isZero_iff_isIso` — a morphism of a pretriangulated
  category is an isomorphism exactly when its cone is a zero object.
* `CategoryTheory.Functor.trW_kernel_eq_inverseImage_isomorphisms` — for a triangulated functor,
  the morphisms whose cone lies in its kernel are the morphisms it inverts; this is the
  identification of the Verdier quotient by the kernel with the localization.
* `CategoryTheory.Functor.isLocalization_trW_kernel_of_leftAdjoint` — a triangulated functor
  with a fully faithful left adjoint is the Verdier quotient by its kernel.
* `Stacks.Adequate.BigSite.isIso_map_derivedAdequateAdjunction_counit` — the middle step of
  [Stacks, Tag 070X]: `Rf_*` carries `Lf^*Rf_*X ⟶ X` to an isomorphism.
* `Stacks.Adequate.BigSite.isLocalization_derivedAdequatePushforward` and
  `Stacks.Adequate.BigSite.isLocalization_trW_kernel_derivedAdequatePushforward` —
  [Stacks, Tag 070X], that `Rf_*` is a localization functor, in the two descriptions of the
  class of morphisms.

## Implementation notes

**What is assumed and why.** The ambient derived adjunction `L ⊣ R` for the morphism of
[Stacks, Tag 070U], the two landing assertions `hL` and `hR`, and the invertibility `hunit` of
the ambient unit on `D_QCoh(S)` are hypotheses, exactly as they are for the [Stacks, Tag 070W]
declarations of `StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedRestriction` that
this file consumes; see the implementation notes there for why the adjunction of
[Stacks, Tag 07A6] does not apply to that morphism at the universes in which it is stated.

**Full faithfulness of `Lf^*` needs the unit, not merely `Rf_* Lf^* ≅ id`.** The
[Stacks, Tag 070W] declaration `BigSite.derivedAdequateCompIso` produces an abstract isomorphism
`Lf^* ⋙ Rf_* ≅ 𝟭`, and an abstract isomorphism of that shape does not make a left adjoint fully
faithful. What does is the invertibility of the *unit* of the restricted adjunction, which is
`DerivedCategoryB.isIso_restrictAdjunction_unit_app` from the same hypothesis `hunit`; that is
the route taken here.

**Two descriptions of the class of morphisms.** The source quotients `D_Adeq(𝒪)` by the
triangulated subcategory `D_𝒞(𝒪) = ker Rf_*`, i.e. localizes at the morphisms whose cone lies
in that kernel. For a triangulated functor that class is the class of morphisms the functor
inverts, which is `Functor.trW_kernel_eq_inverseImage_isomorphisms`. Both descriptions are
carried: the statements at the inverted morphisms need no triangulated structure, while the
statements in the source's own `D_𝒞(𝒪)` form carry the pretriangulated structures of the two
subcategories and the triangulatedness of the restricted `Rf_*` as instance arguments, those
not being constructed for the restricted functors in the library.

## References

* [Stacks Project, Tag 070X](https://stacks.math.columbia.edu/tag/070X)
* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
* [Stacks Project, Tag 070U](https://stacks.math.columbia.edu/tag/070U)
* [Stacks Project, Tag 06ZQ](https://stacks.math.columbia.edu/tag/06ZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-! ### The cone of a morphism inverted by a triangulated functor -/

section Triangulated

universe v v' u u'

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A morphism of a pretriangulated category is an isomorphism exactly when its cone is a zero
object. -/
public theorem ObjectProperty.trW_isZero_iff_isIso {X Y : C} (f : X ⟶ Y) :
    ObjectProperty.trW (IsZero (C := C)) f ↔ IsIso f := by
  constructor
  · rintro ⟨Z, g, h, hT, hZ⟩
    exact ((Triangle.mk f g h).isZero₃_iff_isIso₁ hT).1 hZ
  · intro hf
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
    exact ⟨Z, g, h, hT, ((Triangle.mk f g h).isZero₃_iff_isIso₁ hT).2 hf⟩

/-- A triangulated functor inverts a morphism exactly when the cone of that morphism lies in the
kernel of the functor. -/
public theorem Functor.trW_kernel_iff_isIso_map (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    {X Y : C} (f : X ⟶ Y) :
    ObjectProperty.trW F.kernel f ↔ IsIso (F.map f) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsZero (C := D)) :=
    ⟨fun e hX => hX.of_iso e.symm⟩
  exact (ObjectProperty.inverseImage_trW_iff (P := IsZero (C := D)) (F := F) f).trans
    (ObjectProperty.trW_isZero_iff_isIso _)

/-- **The Verdier quotient by the kernel of a triangulated functor is its localization.** The
morphisms whose cone lies in the kernel of a triangulated functor are exactly the morphisms the
functor inverts. -/
public theorem Functor.trW_kernel_eq_inverseImage_isomorphisms (F : C ⥤ D) [F.CommShift ℤ]
    [F.IsTriangulated] :
    ObjectProperty.trW F.kernel = (MorphismProperty.isomorphisms D).inverseImage F := by
  ext X Y f
  rw [F.trW_kernel_iff_isIso_map f, MorphismProperty.inverseImage_iff,
    MorphismProperty.isomorphisms.iff]

/-- **A triangulated functor with a fully faithful left adjoint is the Verdier quotient by its
kernel.** The counit `F G X ⟶ X` is inverted, so it becomes invertible in the quotient, and the
map on `Hom`-sets is bijective because `F` provides an inverse. -/
public theorem Functor.isLocalization_trW_kernel_of_leftAdjoint {F : D ⥤ C} {G : C ⥤ D}
    [F.Full] [F.Faithful] (adj : F ⊣ G) [G.CommShift ℤ] [G.IsTriangulated] :
    G.IsLocalization (ObjectProperty.trW G.kernel) := by
  rw [G.trW_kernel_eq_inverseImage_isomorphisms]
  exact adj.isLocalization_rightAdjoint'

end Triangulated

end CategoryTheory

namespace Stacks.Adequate

universe d u

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
  [HasSheafify B.topology AddCommGrpCat.{u}]
  [B.topology.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} B.structureSheaf)]
  [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  (L : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf) ⥤
    DerivedCategory (SheafOfModules.{u} B.structureSheaf))
  (R : DerivedCategory (SheafOfModules.{u} B.structureSheaf) ⥤
    DerivedCategory (SheafOfModules.{u} S.ringCatSheaf))
  (hL : ∀ K : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf),
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf) K →
      BigSite.derivedAdequate.{u, u, d} B (L.obj K))
  (hR : ∀ K : DerivedCategory (SheafOfModules.{u} B.structureSheaf),
    BigSite.derivedAdequate.{u, u, d} B K →
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)
        (R.obj K))
  (adj : L ⊣ R)
  (hunit : ∀ K : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf),
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf) K →
      IsIso (adj.unit.app K))

/-! ### `Lf^*` is fully faithful -/

include hL hR adj hunit in
/-- **[Stacks, Tag 070W] read as full faithfulness of `Lf^*`.** If the unit of the ambient
derived adjunction is invertible at every complex with quasi-coherent cohomology, then
`Lf^* : D_QCoh(S) ⥤ D_Adeq(𝒪)` is fully faithful. -/
public def BigSite.fullyFaithfulDerivedAdequatePullback :
    (BigSite.derivedAdequatePullback B L hL).FullyFaithful :=
  haveI : ∀ K, IsIso ((BigSite.derivedAdequateAdjunction B L R hL hR adj).unit.app K) :=
    fun K => DerivedCategoryB.isIso_restrictAdjunction_unit_app L R hL hR adj hunit K
  haveI : IsIso (BigSite.derivedAdequateAdjunction B L R hL hR adj).unit :=
    NatIso.isIso_of_isIso_app _
  Adjunction.fullyFaithfulLOfIsIsoUnit (BigSite.derivedAdequateAdjunction B L R hL hR adj)

/-! ### The quotient of `D_Adeq(𝒪)` by the parasitic part -/

/-- `Lf^*` is full and faithful, in the form needed to apply the localization criteria. -/
private theorem BigSite.full_and_faithful_derivedAdequatePullback
    (hR : ∀ K : DerivedCategory (SheafOfModules.{u} B.structureSheaf),
      BigSite.derivedAdequate.{u, u, d} B K →
        DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)
          (R.obj K))
    (hunit : ∀ K : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf),
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf) K →
        IsIso (adj.unit.app K)) :
    (BigSite.derivedAdequatePullback B L hL).Full ∧
      (BigSite.derivedAdequatePullback B L hL).Faithful :=
  let h := BigSite.fullyFaithfulDerivedAdequatePullback B L R hL hR adj hunit
  ⟨h.full, h.faithful⟩

include hL hR adj hunit in
/-- **The middle step of [Stacks, Tag 070X].** The map `Lf^*Rf_*X ⟶ X` is carried by `Rf_*` to an
isomorphism of `D_QCoh(S)`, hence becomes an isomorphism in `D_Adeq(𝒪)/D_𝒞(𝒪)`. -/
public theorem BigSite.isIso_map_derivedAdequateAdjunction_counit
    (X : (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory) :
    IsIso ((BigSite.derivedAdequatePushforward B R hR).map
      ((BigSite.derivedAdequateAdjunction B L R hL hR adj).counit.app X)) := by
  obtain ⟨_, _⟩ := BigSite.full_and_faithful_derivedAdequatePullback B L R hL adj hR hunit
  exact (BigSite.derivedAdequateAdjunction B L R hL hR adj)
    |>.functorCategory_inverseImage_isomorphisms_counit X

include hL hR adj hunit in
/-- **[Stacks, Tag 070X].** `Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)` is a localization functor for the
morphisms of `D_Adeq(𝒪)` that it carries to isomorphisms of `D_QCoh(S)`, so that
`D_Adeq(𝒪)/D_𝒞(𝒪) ⟶ D_QCoh(S)` is an equivalence. -/
@[stacks 070X "the equivalence `D_Adeq(𝒪)/D_𝒞(𝒪) ⟶ D_QCoh(S)`, with the quotient described as
the localization at the morphisms `Rf_*` inverts; the description by the subcategory
`D_𝒞(𝒪) = ker Rf_*` is the companion
`BigSite.isLocalization_trW_kernel_derivedAdequatePushforward`. The ambient derived adjunction
`adj`, both landing assertions `hL` and `hR`, and the invertibility `hunit` of the ambient unit
on `D_QCoh(S)` are hypotheses, exactly as for the Tag 070W declarations this consumes; none of
them is proved here"]
public theorem BigSite.isLocalization_derivedAdequatePushforward :
    (BigSite.derivedAdequatePushforward B R hR).IsLocalization
      ((MorphismProperty.isomorphisms _).inverseImage
        (BigSite.derivedAdequatePushforward B R hR)) := by
  obtain ⟨_, _⟩ := BigSite.full_and_faithful_derivedAdequatePullback B L R hL adj hR hunit
  exact (BigSite.derivedAdequateAdjunction B L R hL hR adj).isLocalization_rightAdjoint'

include hL hR adj hunit in
/-- **[Stacks, Tag 070X], the equivalence.** The localization of `D_Adeq(𝒪)` at the morphisms
inverted by `Rf_*` is equivalent to `D_QCoh(S)`. -/
@[stacks 070X "the equivalence of categories itself, for the quotient described as the
localization at the morphisms `Rf_*` inverts; the hypotheses are those of
`BigSite.isLocalization_derivedAdequatePushforward`"]
public def BigSite.derivedAdequateQuotientEquivalence :
    ((MorphismProperty.isomorphisms _).inverseImage
        (BigSite.derivedAdequatePushforward B R hR)).Localization ≌
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory :=
  haveI := BigSite.isLocalization_derivedAdequatePushforward B L R hL hR adj hunit
  Localization.equivalenceFromModel (BigSite.derivedAdequatePushforward B R hR) _

/-! ### The quotient in the source's form, by the subcategory `D_𝒞(𝒪) = ker Rf_*` -/

section Verdier

variable [HasZeroObject (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory]
  [Preadditive (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory]
  [HasShift (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory ℤ]
  [∀ n : ℤ, (shiftFunctor (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory n).Additive]
  [Pretriangulated (BigSite.derivedAdequate.{u, u, d} B).FullSubcategory]
  [HasZeroObject (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory]
  [Preadditive (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory]
  [HasShift (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory ℤ]
  [∀ n : ℤ, (shiftFunctor (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory n).Additive]
  [Pretriangulated (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory]
  [(BigSite.derivedAdequatePushforward B R hR).CommShift ℤ]
  [(BigSite.derivedAdequatePushforward B R hR).IsTriangulated]

include hL hR adj hunit in
/-- **[Stacks, Tag 070X] in the source's own form.** `Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)` is a
localization functor for the morphisms whose cone lies in `D_𝒞(𝒪)`, the kernel of `Rf_*`. -/
@[stacks 070X "the equivalence `D_Adeq(𝒪)/D_𝒞(𝒪) ⟶ D_QCoh(S)` with the quotient taken, as in the
source, at the morphisms whose cone lies in the subcategory `D_𝒞(𝒪)`, realised as the kernel of
`Rf_*`, which is the source's own description of it. Beyond the hypotheses of
`BigSite.isLocalization_derivedAdequatePushforward`, the pretriangulated structures of the two
subcategories and the triangulatedness of the restricted `Rf_*` are instance arguments; the
library does not construct them for the restricted functors"]
public theorem BigSite.isLocalization_trW_kernel_derivedAdequatePushforward :
    (BigSite.derivedAdequatePushforward B R hR).IsLocalization
      (ObjectProperty.trW (BigSite.derivedAdequatePushforward B R hR).kernel) := by
  obtain ⟨_, _⟩ := BigSite.full_and_faithful_derivedAdequatePullback B L R hL adj hR hunit
  exact Functor.isLocalization_trW_kernel_of_leftAdjoint
    (BigSite.derivedAdequateAdjunction B L R hL hR adj)

include hL hR adj hunit in
/-- **[Stacks, Tag 070X], the equivalence `D_Adeq(𝒪)/D_𝒞(𝒪) ≌ D_QCoh(S)`.** The quotient of
`D_Adeq(𝒪)` by the complexes with parasitic cohomology, the kernel of `Rf_*`, is equivalent to
`D_QCoh(S)`. -/
@[stacks 070X "the equivalence of categories itself, in the source's own form: the quotient of
`D_Adeq(𝒪)` by `D_𝒞(𝒪) = ker Rf_*`. The hypotheses are those of
`BigSite.isLocalization_trW_kernel_derivedAdequatePushforward`"]
public def BigSite.derivedParasiticQuotientEquivalence :
    (ObjectProperty.trW
        (BigSite.derivedAdequatePushforward B R hR).kernel).Localization ≌
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)).FullSubcategory :=
  haveI := BigSite.isLocalization_trW_kernel_derivedAdequatePushforward B L R hL hR adj hunit
  Localization.equivalenceFromModel (BigSite.derivedAdequatePushforward B R hR) _

end Verdier

end Stacks.Adequate

end
