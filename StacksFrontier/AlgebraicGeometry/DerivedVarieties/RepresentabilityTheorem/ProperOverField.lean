module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.RepresentabilityTheorem.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsPerfectIsCompact
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.StrongGenerator.PerfectProperSmooth
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentCharacterization
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentCharacterizationConverse
public import StacksCore.Tactic.StacksAttribute

/-!
# Representability of cohomological functors on perfect complexes

Let `X` be a quasi-compact quasi-separated scheme whose category of modules is `k`-linear. A
`k`-linear cohomological functor `F : D_perf(𝒪_X)^opp → Vect_k` with finite-dimensional values is
`E ↦ Hom_X(E, K)` for an object `K` of `D_QCoh(𝒪_X)`. For `X` proper over a field `k` and `F` of
finite total dimension, `K` lies in `D^b_Coh(𝒪_X)`: this is [Stacks, Tag 0FYH].

## Main results

* `isQuasicoherent_homology_of_isPerfect`: a perfect object of `D(𝒪_X)` has quasi-coherent
  cohomology, at the locally small model.
* `exists_iso_linearYoneda_of_isHomological`: the representability theorem on `D_perf(𝒪_X)` for
  a quasi-compact quasi-separated scheme, with a representing object in `D_QCoh(𝒪_X)`.
* `homologyModelIso`, `isPerfect_model_iff`, `extModelLinearEquiv`: cohomology sheaves,
  perfectness and `Ext` modules agree at the standard and the locally small model of `D(𝒪_X)`.
* `exists_iso_linearYoneda_of_converse`: Tag 0FYH from the implication (2) ⇒ (1) of Tag 0FYD.
* `exists_iso_linearYoneda_of_isHomological_of_isProper`: **[Stacks, Tag 0FYH]**.

## Implementation notes

The derived category is the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the global instance, whose morphisms live in
the universe of the scheme; `D_perf(𝒪_X)` is `AlgebraicGeometry.perfectDerived`, and its
triangulated structure is that of the perfect objects,
`Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect`.

The proof is the source's: `D_QCoh(𝒪_X)` has direct sums ([Stacks, Tag 08DT]) and is compactly
generated ([Stacks, Tag 09IS],
`Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory`), perfect objects
are compact in it ([Stacks, Tag 09M1], `Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect`),
and the representability theorem [Stacks, Tag 0FYG] applies, in the form
`CategoryTheory.exists_iso_comp_linearYoneda_of_isCompactObject_obj`, along the inclusion of the
perfect objects. That form does not need the perfect objects to exhaust the compact ones, so the
implication *compact ⇒ perfect* of [Stacks, Tag 09M1] is not used.

## References

* [Stacks Project, Tag 0FYH](https://stacks.math.columbia.edu/tag/0FYH)
* [Stacks Project, Tag 0FYG](https://stacks.math.columbia.edu/tag/0FYG)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite Stacks.Cohomology.PerfectComplexes

universe w u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Representability

/-! ### Perfect objects have quasi-coherent cohomology -/

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A perfect complex has quasi-coherent cohomology sheaves.** This is
`AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect` read on the
complex. -/
theorem isQuasicoherent_homology_of_isPerfectComplex (X : Scheme.{u})
    (E : CochainComplex X.Modules ℤ) (hE : IsPerfectComplex (X := X.toRingedSpace) E) (i : ℤ) :
    ((HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) i).obj E).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors X.Modules i).app E)
    (PerfectApproximation.isQuasicoherent_homology_of_isPerfect X _
      ⟨E, hE, ⟨Iso.refl ((DerivedCategory.Q (C := X.Modules)).obj E)⟩⟩ i)

end Standard

/-- **A perfect object of `D(𝒪_X)` has quasi-coherent cohomology**, at the locally small model:
perfectness implies pseudo-coherence, and the cohomology sheaves of a pseudo-coherent object are
quasi-coherent ([Stacks, Tag 08E5]). -/
theorem isQuasicoherent_homology_of_isPerfect (X : Scheme.{u}) (K : DerivedCategory X.Modules)
    (hK : IsPerfect.{u, u, u} (X := X.toRingedSpace) K) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) K := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  let E₀ : CochainComplex X.Modules ℤ := E
  let e₀ : (DerivedCategory.Q (C := X.Modules)).obj E₀ ≅ K := e
  intro i
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctorFactors X.Modules i).app E₀).symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules i).mapIso e₀)
    (isQuasicoherent_homology_of_isPerfectComplex X E₀ hE i)

/-! ### The standard and the locally small model of `D(𝒪_X)` -/

section Models

variable (X : Scheme.{u})

local notation "Dstd" => @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)
local notation "Qstd" => @DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard X.Modules)

/-- The comparison of the standard model of `D(𝒪_X)` with the locally small one, which is the
identity on objects. -/
abbrev modelComparison : Dstd ≌ DerivedCategory X.Modules :=
  StacksDraft.DerivedModel.schemeModulesComparison X

/-- The comparison of the two models is additive, being an equivalence. -/
instance modelComparison_functor_additive : (modelComparison X).functor.Additive := by
  rw [Localization.functor_additive_iff
    (@DerivedCategory.Qh X.Modules _ _ (HasDerivedCategory.standard X.Modules))
    (HomotopyCategory.subcategoryAcyclic X.Modules).trW]
  exact Functor.additive_of_iso (StacksDraft.DerivedModel.shrinkComparisonQhIso X.Modules)

/-- **The two models compute the same cohomology sheaves.** Both are the cohomology of a
representing complex. -/
def homologyModelIso (n : ℤ) (K : Dstd) :
    (DerivedCategory.homologyFunctor X.Modules n).obj ((modelComparison X).functor.obj K) ≅
      (@DerivedCategory.homologyFunctor X.Modules _ _
        (HasDerivedCategory.standard X.Modules) n).obj K :=
  (DerivedCategory.homologyFunctor X.Modules n).mapIso
      ((modelComparison X).functor.mapIso ((Qstd).objObjPreimageIso K)).symm ≪≫
    (DerivedCategory.homologyFunctorFactors X.Modules n).app ((Qstd).objPreimage K) ≪≫
    ((@DerivedCategory.homologyFunctorFactors X.Modules _ _
      (HasDerivedCategory.standard X.Modules) n).app ((Qstd).objPreimage K)).symm ≪≫
    (@DerivedCategory.homologyFunctor X.Modules _ _
      (HasDerivedCategory.standard X.Modules) n).mapIso ((Qstd).objObjPreimageIso K)

/-- `D_B(𝒪_X)`-membership does not depend on the model, for a property `B` of `𝒪_X`-modules
closed under isomorphisms. -/
theorem derivedCategoryB_model_iff (B : ObjectProperty X.Modules) [B.IsClosedUnderIsomorphisms]
    (K : Dstd) :
    DerivedCategoryB.derivedCategoryB B ((modelComparison X).functor.obj K) ↔
      @DerivedCategoryB.derivedCategoryB X.Modules _ _
        (HasDerivedCategory.standard X.Modules) B K :=
  ⟨fun h n => B.prop_of_iso (homologyModelIso X n K) (h n),
    fun h n => B.prop_of_iso (homologyModelIso X n K).symm (h n)⟩

/-- `D^b_B(𝒪_X)`-membership does not depend on the model. -/
theorem derivedCategoryBBounded_model_iff (B : ObjectProperty X.Modules)
    [B.IsClosedUnderIsomorphisms] (K : Dstd) :
    DerivedCategoryB.derivedCategoryBBounded B ((modelComparison X).functor.obj K) ↔
      @DerivedCategoryB.derivedCategoryBBounded X.Modules _ _
        (HasDerivedCategory.standard X.Modules) B K := by
  refine and_congr (and_congr ?_ ?_) (derivedCategoryB_model_iff X B K) <;>
    exact exists_congr fun _ => forall_congr' fun n => imp_congr_right fun _ =>
      ⟨fun h => h.of_iso (homologyModelIso X n K).symm,
        fun h => h.of_iso (homologyModelIso X n K)⟩

/-- **Perfectness does not depend on the model**, read on the canonical comparison: this is
`Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model` at a representing complex of `K`. -/
theorem isPerfect_model_iff (K : Dstd) :
    IsPerfect.{u, u, u} (X := X.toRingedSpace) ((modelComparison X).functor.obj K) ↔
      @IsPerfect.{u, u, u + 1} X.toRingedSpace (HasDerivedCategory.standard X.Modules) K :=
  (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model (X := X.toRingedSpace)
    (HasDerivedCategory.standard X.Modules) (Scheme.Modules.hasDerivedCategory X)
    (E := (Qstd).objPreimage K) ((Qstd).objObjPreimageIso K)
    ((modelComparison X).functor.mapIso ((Qstd).objObjPreimageIso K))).symm

variable {X} in
/-- The comparison of the two models is `k`-linear: both linear structures are induced from that
of the cochain complexes, and the comparison is compatible with the two localization functors. -/
theorem modelComparison_functor_linear (k : Type w) [Field k] [Linear k X.Modules] :
    (modelComparison X).functor.Linear k := by
  let : Localization.Lifting (Qstd)
      (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := X.Modules)) (modelComparison X).functor := ⟨Iso.refl _⟩
  exact (Localization.functor_linear_iff (Qstd)
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)) k
    (DerivedCategory.Q (C := X.Modules)) (modelComparison X).functor).1 inferInstance

/-- The comparison of the two models commutes with the shift, objectwise. -/
def modelComparisonShiftIso (K : Dstd) (n : ℤ) :
    (modelComparison X).functor.obj (K⟦n⟧) ≅ ((modelComparison X).functor.obj K)⟦n⟧ :=
  (modelComparison X).functor.mapIso ((shiftFunctor Dstd n).mapIso
      ((Qstd).objObjPreimageIso K).symm) ≪≫
    (modelComparison X).functor.mapIso (((Qstd).commShiftIso n).app ((Qstd).objPreimage K)).symm ≪≫
    ((DerivedCategory.Q (C := X.Modules)).commShiftIso n).app ((Qstd).objPreimage K) ≪≫
    (shiftFunctor (DerivedCategory X.Modules) n).mapIso
      ((modelComparison X).functor.mapIso ((Qstd).objObjPreimageIso K))

/-- **The two models have the same `Ext` modules**, as `k`-modules. -/
def extModelLinearEquiv (k : Type w) [Field k] [Linear k X.Modules] (E K : Dstd) (n : ℤ) :
    @DerivedCategory.Ext X.Modules _ _ (HasDerivedCategory.standard X.Modules) E K n ≃ₗ[k]
      DerivedCategory.Ext ((modelComparison X).functor.obj E)
        ((modelComparison X).functor.obj K) n :=
  letI := modelComparison_functor_linear (X := X) k
  { toEquiv := (modelComparison X).fullyFaithfulFunctor.homEquiv
    map_add' := fun _ _ => (modelComparison X).functor.map_add
    map_smul' := fun r f => (modelComparison X).functor.map_smul r f } ≪≫ₗ
    Linear.homCongr k (Iso.refl _) (modelComparisonShiftIso X K n)

end Models

/-! ### Representability on `D_perf(𝒪_X)` -/

attribute [local instance] AlgebraicGeometry.isTriangulated_isPerfect_locallySmall

/-- The inclusion of `D_perf(𝒪_X)` into `D_QCoh(𝒪_X)`. -/
abbrev perfectToQuasiCoherent (X : Scheme.{u}) :
    perfectDerived X ⥤ Stacks.Duality.quasiCoherentDerivedCategory X :=
  (DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)).lift (ObjectProperty.ι _)
    (fun E => isQuasicoherent_homology_of_isPerfect X E.obj E.property)

/-- **Representability on `D_perf(𝒪_X)`.** Let `X` be a quasi-compact quasi-separated scheme
whose category of `𝒪_X`-modules is `k`-linear, and let `F : D_perf(𝒪_X)^opp → Vect_k` be a
`k`-linear cohomological functor with finite-dimensional values. Then `F ≅ Hom_X(-, K)` for an
object `K` of `D(𝒪_X)` with quasi-coherent cohomology.

This is [Stacks, Tag 0FYG] along the inclusion `D_perf(𝒪_X) ⊆ D_QCoh(𝒪_X)`: `D_QCoh(𝒪_X)` has
direct sums ([Stacks, Tag 08DT]) and is compactly generated ([Stacks, Tag 09IS]), and perfect
objects are compact in it ([Stacks, Tag 09M1]). -/
theorem exists_iso_linearYoneda_of_isHomological {k : Type w} [Field k] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [Linear k X.Modules]
    (F : (perfectDerived X)ᵒᵖ ⥤ ModuleCat.{u} k) [F.IsHomological]
    (hF : ∀ {E E' : (perfectDerived X)ᵒᵖ} (f : E ⟶ E') (r : k),
      F.map ((r • f.unop).op) = r • F.map f)
    (hfin : ∀ E, FiniteDimensional k (F.obj E)) :
    ∃ K : DerivedCategory X.Modules,
      DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf) K ∧
        Nonempty (F ≅ (ObjectProperty.ι _).op ⋙
          (linearYoneda k (DerivedCategory X.Modules)).obj K) := by
  let Q := DerivedCategoryB.derivedCategoryB (A := X.Modules)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
  let L := perfectToQuasiCoherent X
  have := Stacks.Duality.DerivedPushforward.hasCoproducts_quasiCoherentDerivedCategory X
  have : L.Linear k := ⟨fun _ _ => Q.ι.map_injective rfl⟩
  obtain ⟨Y, ⟨e⟩⟩ := exists_iso_comp_linearYoneda_of_isCompactObject_obj k
    (Stacks.Duality.quasiCoherentDerivedCategory X)
    (Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory X)
    (perfectDerived X) L
    (fun E => Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect X (L.obj E) E.property)
    F hF hfin
  refine ⟨Y.obj, Y.property, ⟨e ≪≫ NatIso.ofComponents (fun E => ?_) ?_⟩⟩
  · exact LinearEquiv.toModuleIso
      { toEquiv := Q.fullyFaithfulι.homEquiv
        map_add' := fun f g => Q.ι.map_add
        map_smul' := fun r f => Q.ι.map_smul r f }
  · intro E E' f
    ext g
    exact Q.ι.map_comp _ _

/-! ### Proper schemes over a field -/

section ProperOverField

/-- `Hom(A, B⟦n⟧) ≃ Hom(A⟦-n⟧, B)`, `k`-linearly, in a `k`-linear category with a linear shift. -/
def homShiftLinearEquiv (k : Type w) [Field k] {C : Type*} [Category* C] [Preadditive C]
    [Linear k C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Linear k] (A B : C) (n : ℤ) :
    (A ⟶ B⟦n⟧) ≃ₗ[k] (A⟦-n⟧ ⟶ B) :=
  { toEquiv := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C (-n))).homEquiv
    map_add' := fun _ _ => (shiftFunctor C (-n)).map_add
    map_smul' := fun r f => (shiftFunctor C (-n)).map_smul r f } ≪≫ₗ
    Linear.homCongr k (Iso.refl _) ((shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).app B)

/-- Quasi-coherence of `𝒪_X`-modules is invariant under isomorphism. -/
theorem isClosedUnderIsomorphisms_isQuasicoherent (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (C := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) :=
  ⟨fun e h => (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e h⟩

/-- Membership in `D^b_B(𝒪_X)` is invariant under isomorphism. -/
theorem derivedCategoryBBounded_of_iso {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (B : ObjectProperty A) [B.IsClosedUnderIsomorphisms] {K L : DerivedCategory A} (e : K ≅ L)
    (hK : DerivedCategoryB.derivedCategoryBBounded B K) :
    DerivedCategoryB.derivedCategoryBBounded B L := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hB⟩ := hK
  exact ⟨⟨⟨a, fun n hn => (ha n hn).of_iso ((DerivedCategory.homologyFunctor A n).mapIso e).symm⟩,
    ⟨b, fun n hn => (hb n hn).of_iso ((DerivedCategory.homologyFunctor A n).mapIso e).symm⟩⟩,
    fun n => B.prop_of_iso ((DerivedCategory.homologyFunctor A n).mapIso e) (hB n)⟩

/-- Membership in `D_B(𝒪_X)` is invariant under isomorphism. -/
theorem derivedCategoryB_of_iso {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (B : ObjectProperty A) [B.IsClosedUnderIsomorphisms] {K L : DerivedCategory A} (e : K ≅ L)
    (hK : DerivedCategoryB.derivedCategoryB B K) : DerivedCategoryB.derivedCategoryB B L :=
  fun n => B.prop_of_iso ((DerivedCategory.homologyFunctor A n).mapIso e) (hK n)

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

attribute [local instance] AlgebraicGeometry.modulesLinear

/-- If `F ≅ Hom_X(-, K)` has finite total rank on the shifts of every perfect complex, then
`Ext^*_X(E, K)` is finite-dimensional in total for every perfect `E`. -/
theorem hasFiniteTotalExt_of_iso_linearYoneda
    (F : (perfectDerived X.left)ᵒᵖ ⥤ ModuleCat.{u} k)
    (hfin : ∀ E : perfectDerived X.left,
      Cardinal.sum (fun n : ℤ => Module.rank k (F.obj (op (E⟦n⟧)))) < Cardinal.aleph0)
    (K : DerivedCategory X.left.Modules)
    (e : F ≅ (ObjectProperty.ι _).op ⋙ (linearYoneda k (DerivedCategory X.left.Modules)).obj K)
    (E : @DerivedCategory X.left.Modules _ _ (HasDerivedCategory.standard X.left.Modules))
    (hE : @IsPerfect.{u, u, u + 1} X.left.toRingedSpace
      (HasDerivedCategory.standard X.left.Modules) E) :
    BeilinsonCoherentCharacterization.HasFiniteTotalExt k X E
      ((modelComparison X.left).inverse.obj K) := by
  have hfin' := fun E => CoherentCharacterization.lt_aleph0_cardinalSum_iff.1 (hfin E)
  let G := modelComparison X.left
  let K' := G.inverse.obj K
  let P : perfectDerived X.left := ⟨G.functor.obj E, (isPerfect_model_iff X.left E).2 hE⟩
  have φ : ∀ n : ℤ, @DerivedCategory.Ext X.left.Modules _ _
      (HasDerivedCategory.standard X.left.Modules) E K' n ≃ₗ[k] F.obj (op (P⟦-n⟧)) := fun n =>
    extModelLinearEquiv X.left k E K' n ≪≫ₗ
      Linear.homCongr k (Iso.refl _) ((shiftFunctor _ n).mapIso (G.counitIso.app K)) ≪≫ₗ
      homShiftLinearEquiv k (G.functor.obj E) K n ≪≫ₗ
      Linear.homCongr k
        ((((ObjectProperty.ι _).commShiftIso (-n)).app P).symm) (Iso.refl _) ≪≫ₗ
      (e.app (op (P⟦-n⟧))).symm.toLinearEquiv
  refine ⟨fun n => ?_, ?_⟩
  · have : Module.Finite k (F.obj (op (P⟦-n⟧))) :=
      Module.rank_lt_aleph0_iff.1 ((hfin' P).1 (-n))
    exact Module.Finite.equiv (φ n).symm
  · refine ((hfin' P).2.image (fun n => -n)).subset fun n hn => ?_
    refine ⟨-n, fun h0 => hn ?_, neg_neg n⟩
    have : Subsingleton (F.obj (op (P⟦-n⟧))) := rank_zero_iff.1 h0
    exact (φ n).toEquiv.subsingleton

include X in
/-- **Stacks Project, Tag 0FYH, from the implication (2) ⇒ (1) of Tag 0FYD.** Let `X` be a
proper scheme over a field `k` and let `F : D_perf(𝒪_X)^opp → Vect_k` be a `k`-linear
cohomological functor with `∑_{n ∈ ℤ} dim_k F(E[n]) < ∞` for every perfect `E`. Then
`F ≅ Hom_X(-, K)` for some `K` in `D^b_Coh(𝒪_X)`, provided the implication (2) ⇒ (1) of
[Stacks, Tag 0FYD] holds, which is the hypothesis `h0FYD`, stated at the standard model exactly as
the implication (1) ⇒ (2) is there.

The source's proof: by [Stacks, Tag 0FYG] `F ≅ Hom_X(-, K)` for some `K` in `D_QCoh(𝒪_X)`
(`exists_iso_linearYoneda_of_isHomological`), so `Ext^n_X(E, K) = Hom_X(E[-n], K) = F(E[-n])` has
finite total dimension for every perfect `E`, and `K` lies in `D^b_Coh(𝒪_X)` by
[Stacks, Tag 0FYD]. -/
theorem exists_iso_linearYoneda_of_converse
    (h0FYD : ∀ K : @DerivedCategory X.left.Modules _ _
        (HasDerivedCategory.standard X.left.Modules),
      @DerivedCategoryB.derivedCategoryB X.left.Modules _ _
        (HasDerivedCategory.standard X.left.Modules)
        (SheafOfModules.isQuasicoherent X.left.ringCatSheaf) K →
      (∀ E : @DerivedCategory X.left.Modules _ _ (HasDerivedCategory.standard X.left.Modules),
        @IsPerfect.{u, u, u + 1} X.left.toRingedSpace
          (HasDerivedCategory.standard X.left.Modules) E →
        BeilinsonCoherentCharacterization.HasFiniteTotalExt k X E K) →
      @DerivedCategoryB.derivedCategoryBBounded X.left.Modules _ _
        (HasDerivedCategory.standard X.left.Modules) (fun M : X.left.Modules => M.IsCoherent) K)
    [IsProper X.hom]
    (F : (perfectDerived X.left)ᵒᵖ ⥤ ModuleCat.{u} k) [F.IsHomological]
    (hF : ∀ {E E' : (perfectDerived X.left)ᵒᵖ} (f : E ⟶ E') (r : k),
      F.map ((r • f.unop).op) = r • F.map f)
    (hfin : ∀ E : perfectDerived X.left,
      Cardinal.sum (fun n : ℤ => Module.rank k (F.obj (op (E⟦n⟧)))) < Cardinal.aleph0) :
    ∃ K : DerivedCategory X.left.Modules,
      DerivedCategoryB.derivedCategoryBBounded (fun M : X.left.Modules => M.IsCoherent) K ∧
        Nonempty (F ≅ (ObjectProperty.ι _).op ⋙
          (linearYoneda k (DerivedCategory X.left.Modules)).obj K) := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : ObjectProperty.IsClosedUnderIsomorphisms (fun M : X.left.Modules => M.IsCoherent) :=
    AlgebraicGeometry.CoherentAbelian.coherentModules_isClosedUnderIsomorphisms
  have := isClosedUnderIsomorphisms_isQuasicoherent X.left
  have hdim : ∀ E, FiniteDimensional k (F.obj E) := fun E => by
    have : Module.Finite k (F.obj (op (E.unop⟦(0 : ℤ)⟧))) :=
      Module.rank_lt_aleph0_iff.1
        ((CoherentCharacterization.lt_aleph0_cardinalSum_iff.1 (hfin E.unop)).1 0)
    exact Module.Finite.equiv
      (F.mapIso ((shiftFunctorZero (perfectDerived X.left) ℤ).app E.unop).op).toLinearEquiv.symm
  obtain ⟨K, hqc, ⟨e⟩⟩ := exists_iso_linearYoneda_of_isHomological X.left F hF hdim
  let K' := (modelComparison X.left).inverse.obj K
  let eK : (modelComparison X.left).functor.obj K' ≅ K :=
    (modelComparison X.left).counitIso.app K
  exact ⟨K, derivedCategoryBBounded_of_iso (fun M : X.left.Modules => M.IsCoherent) eK
    ((derivedCategoryBBounded_model_iff X.left (fun M : X.left.Modules => M.IsCoherent) K').2
      (h0FYD K' ((derivedCategoryB_model_iff X.left _ K').1
        (derivedCategoryB_of_iso _ eK.symm hqc))
        (hasFiniteTotalExt_of_iso_linearYoneda X F hfin K e))),
    ⟨e⟩⟩

/-- **Stacks Project, Tag 0FYH.** Let `X` be a proper scheme over a field `k`. Let
`F : D_perf(𝒪_X)^opp → Vect_k` be a `k`-linear cohomological functor such that
`∑_{n ∈ ℤ} dim_k F(E[n]) < ∞` for all `E ∈ D_perf(𝒪_X)`. Then `F` is isomorphic to a functor of
the form `E ↦ Hom_X(E, K)` for some `K ∈ D^b_Coh(𝒪_X)`.

Here `D_perf(𝒪_X)` is `AlgebraicGeometry.perfectDerived`, the perfect objects of the derived
category of `𝒪_X`-modules with its triangulated structure; "cohomological" is
`CategoryTheory.Functor.IsHomological` on the opposite category; `k`-linearity is for the
`k`-structure induced by the structure morphism, `AlgebraicGeometry.modulesLinear`; the sum is the
cardinal sum of the `k`-ranks over all of `ℤ`, and `< ∞` is `< ℵ₀`; and `D^b_Coh(𝒪_X)` is
`DerivedCategoryB.derivedCategoryBBounded` at coherence.

The proof is the source's: by [Stacks, Tag 0FYG] `F ≅ Hom_X(-, K)` for some `K ∈ D_QCoh(𝒪_X)`
(`exists_iso_linearYoneda_of_isHomological`, through [Stacks, Tags 08DT, 09IS and 09M1]), and then
`K ∈ D^b_Coh(𝒪_X)` by [Stacks, Tag 0FYD]
(`CoherentCharacterizationConverse.derivedCategoryBBounded_of_hasFiniteTotalExt`),
`Ext^n_X(E, K) = Hom_X(E[-n], K) = F(E[-n])` having finite total dimension. -/
@[stacks 0FYH]
theorem exists_iso_linearYoneda_of_isHomological_of_isProper [IsProper X.hom]
    (F : (perfectDerived X.left)ᵒᵖ ⥤ ModuleCat.{u} k) [F.IsHomological]
    (hF : ∀ {E E' : (perfectDerived X.left)ᵒᵖ} (f : E ⟶ E') (r : k),
      F.map ((r • f.unop).op) = r • F.map f)
    (hfin : ∀ E : perfectDerived X.left,
      Cardinal.sum (fun n : ℤ => Module.rank k (F.obj (op (E⟦n⟧)))) < Cardinal.aleph0) :
    ∃ K : DerivedCategory X.left.Modules,
      DerivedCategoryB.derivedCategoryBBounded (fun M : X.left.Modules => M.IsCoherent) K ∧
        Nonempty (F ≅ (ObjectProperty.ι _).op ⋙
          (linearYoneda k (DerivedCategory X.left.Modules)).obj K) :=
  exists_iso_linearYoneda_of_converse X
    (CoherentCharacterizationConverse.derivedCategoryBBounded_of_hasFiniteTotalExt X) F hF hfin

end ProperOverField

end Stacks.AlgebraicGeometry.DerivedVarieties.Representability

end
