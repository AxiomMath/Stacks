module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineComparisonTransport
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedPushforwardScheme

/-!
# From the dévissage triangles to the equivalence of Stacks 06VT

This file carries out the formal half of [Stacks, Tag 09T6]. Fix a scheme `X`, write
`ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` for the inclusion of the quasi-coherent modules and let
`RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` be right adjoint to the functor `D(ι)` induced by `ι`. The
comparison functor `i_X` of [Stacks, Tag 06VT] is then left adjoint to the restriction of `RQ_X`
to the complexes with quasi-coherent cohomology, and it *reflects* isomorphisms, because the
inclusion of the quasi-coherent modules detects the vanishing of a cohomology object. A
conservative left adjoint whose counit is invertible is an equivalence, so all that is left is
the invertibility of the counit of `D(ι) ⊣ RQ_X` at every complex with quasi-coherent cohomology.
That is proved by the dévissage of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDevissage.lean` from the single assumption
that the dévissage step produces a distinguished triangle whose middle vertex has invertible
counit.

The second half of the file supplies that assumption on an affine open: the counit of
`D(ι) ⊣ RQ_X` is invertible at `Rj_*E` for `E` a complex with quasi-coherent cohomology on an
affine open `U ⊆ X`, by comparing the two adjunctions
`D(ι_X) ⋙ j^* ⊣ Rj_* ⋙ RQ_X` and `j^*_{QCoh} ⋙ D(ι_U) ⊣ RQ_U ⋙ Φ` — which have the same left
adjoint — and using that the comparison functor of `U` is an equivalence.

## Main results

* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_reflectsIsomorphisms` — the comparison
  functor reflects isomorphisms.
* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_supportedTriangles` — the
  comparison functor is an equivalence as soon as the dévissage step is available.
* `Stacks.DerivedQCoh.isIso_coheratorCounit_derivedOpenPushforward` — the dévissage step on an
  affine open: the counit of the derived coherator adjunction is invertible at `Rj_*E`.

## Implementation notes

The derived categories are the locally small ones; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDevissage.lean`.

The right derived functors of the coherators of `X` and of the affine open `U` are *arguments*,
presented as adjunctions `D(ι) ⊣ RQ`: that is exactly what the formal argument needs, it avoids
fixing a model, and it keeps this file independent of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/DerivedCoherator.lean`, which imports the module where
[Stacks, Tag 09T6] is stated.

## References

* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe u

namespace Stacks.DerivedQCoh

/-! ### Formal lemmas about adjunctions and triangulated functors -/

/-- **Invertibility of a transformation of triangulated functors propagates from the last two
vertices of a distinguished triangle to the first.** This is [Stacks, Tag 014A],
`CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃`, applied to the morphism of distinguished
triangles whose three components are the given natural transformation; the third square commutes
because the transformation commutes with translation. -/
theorem isIso_app₁_of_isIso_app₂₃ {D E : Type*} [Category* D] [Category* E]
    [HasZeroObject D] [HasZeroObject E] [Preadditive D] [Preadditive E]
    [HasShift D ℤ] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated D] [Pretriangulated E]
    (F G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (α : F ⟶ G) [NatTrans.CommShift α ℤ]
    (T : Triangle D) (hT : T ∈ distTriang D)
    (h₂ : IsIso (α.app T.obj₂)) (h₃ : IsIso (α.app T.obj₃)) :
    IsIso (α.app T.obj₁) := by
  let φ : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T :=
    { hom₁ := α.app T.obj₁
      hom₂ := α.app T.obj₂
      hom₃ := α.app T.obj₃
      comm₁ := α.naturality T.mor₁
      comm₂ := α.naturality T.mor₂
      comm₃ := by
        change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
          (α.app T.obj₁)⟦(1 : ℤ)⟧' = α.app T.obj₃ ≫
            (G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁)
        simpa only [Functor.comp_obj, Functor.comp_map] using
          (show (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
              (α.app T.obj₁)⟦(1 : ℤ)⟧' = _ from by
            rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc, α.naturality,
              Category.assoc]) }
  exact isIso₁_of_isIso₂₃ φ (F.map_distinguished T hT) (G.map_distinguished T hT) h₂ h₃

/-- **A conservative left adjoint whose counit is invertible is an equivalence.** The unit is
invertible after applying the left adjoint, by the triangle identity, hence invertible. -/
theorem isEquivalence_of_reflectsIsomorphisms_of_isIso_counit {D E : Type*}
    [Category* D] [Category* E] {F : D ⥤ E} {G : E ⥤ D} (adj : F ⊣ G)
    [F.ReflectsIsomorphisms] [IsIso adj.counit] : F.IsEquivalence := by
  have hu : ∀ A : D, IsIso (adj.unit.app A) := by
    intro A
    have hmap : IsIso (F.map (adj.unit.app A)) := by
      have hc : IsIso (F.map (adj.unit.app A) ≫ adj.counit.app (F.obj A)) :=
        (adj.left_triangle_components A).symm ▸ (show IsIso (𝟙 (F.obj A)) from inferInstance)
      exact IsIso.of_isIso_comp_right _ (adj.counit.app (F.obj A))
    exact isIso_of_reflects_iso (adj.unit.app A) F
  have := NatIso.isIso_of_isIso_app adj.unit
  exact adj.toEquivalence.isEquivalence_functor

/-- **An equivalence between a pair of full subcategories makes the ambient counit invertible on
the target subcategory.** If `adj : F ⊣ G` restricts, along fully faithful `iA` and `iB`, to an
adjunction whose left adjoint `F'` is an equivalence, then the counit of `adj` is invertible at
every object of the image of `iB`. -/
theorem isIso_counit_app_of_restrictFullyFaithful {A B A' B' : Type*}
    [Category* A] [Category* B] [Category* A'] [Category* B']
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) {iA : A' ⥤ A} {iB : B' ⥤ B}
    (hiA : iA.FullyFaithful) (hiB : iB.FullyFaithful)
    {F' : A' ⥤ B'} {G' : B' ⥤ A'} [F'.IsEquivalence]
    (eF : iA ⋙ F ≅ F' ⋙ iB) (eG : iB ⋙ G ≅ G' ⋙ iA) (Y : B') :
    IsIso (adj.counit.app (iB.obj Y)) := by
  let a := adj.restrictFullyFaithful hiA hiB eF eG
  have hc : IsIso (iB.map (a.counit.app Y)) := inferInstance
  rw [Adjunction.map_restrictFullyFaithful_counit_app] at hc
  have := IsIso.of_isIso_comp_left (eF.inv.app (G'.obj Y))
    (F.map (eG.inv.app Y) ≫ adj.counit.app (iB.obj Y))
  exact IsIso.of_isIso_comp_left (F.map (eG.inv.app Y)) _

/-! ### The comparison functor reflects isomorphisms -/

/-- **The comparison functor of [Stacks, Tag 06VT] reflects isomorphisms.** A morphism carried to
an isomorphism has a cone whose image vanishes; the derived inclusion of the quasi-coherent
modules detects that vanishing, so the cone itself is zero and the morphism is an
isomorphism. -/
theorem derivedQuasicoherentComparison_reflectsIsomorphisms (X : Scheme.{u}) :
    (derivedQuasicoherentComparison.{u} X).ReflectsIsomorphisms := by
  constructor
  intro A B f hf
  obtain ⟨D, g, δ, hT⟩ := distinguished_cocone_triangle f
  have hD : IsZero ((derivedQuasicoherentComparison.{u} X).obj D) :=
    Triangle.isZero₃_of_isIso₁
      ((derivedQuasicoherentComparison.{u} X).mapTriangle.obj (Triangle.mk f g δ))
      ((derivedQuasicoherentComparison.{u} X).map_distinguished _ hT) hf
  have hID : IsZero
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.obj D) :=
    (Functor.map_isZero (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι hD).of_iso
      ((derivedQuasicoherentComparisonCompι.{u} X).app D).symm
  exact (Triangle.isZero₃_iff_isIso₁ (Triangle.mk f g δ) hT).1
    (isZero_quasicoherent_of_isZero_derivedInclusion X D hID)

/-! ### The equivalence from the dévissage triangles -/

/-- **[Stacks, Tag 09T6] granted the dévissage step.** Let `X` be a quasi-compact scheme and let
`RQ_X` be right adjoint to the functor of derived categories induced by the inclusion of the
quasi-coherent modules. Suppose that for every affine open `U ⊆ X`, every closed `S ⊆ X` and
every complex `E` with quasi-coherent cohomology supported on `S` there is a distinguished
triangle starting at `E` whose middle vertex has invertible counit and whose third vertex again
has quasi-coherent cohomology, now supported on `S ∖ U`. Then the comparison functor of
[Stacks, Tag 06VT] is an equivalence.

The dévissage `Stacks.DerivedQCoh.property_of_finite_affine_support` makes the counit invertible
on all of `D_QCoh(𝒪_X)` — the property propagates along a distinguished triangle by
`Stacks.DerivedQCoh.isIso_app₁_of_isIso_app₂₃` and holds at zero — so the restricted adjunction
`i_X ⊣ J ⋙ RQ_X` has invertible counit; `i_X` reflects isomorphisms, and
`Stacks.DerivedQCoh.isEquivalence_of_reflectsIsomorphisms_of_isIso_counit` concludes. -/
theorem derivedQuasicoherentComparison_isEquivalence_of_supportedTriangles (X : Scheme.{u})
    [CompactSpace X]
    (RQ : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (Scheme.QuasicoherentModules X))
    (adj : (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ⊣ RQ)
    (hstep : ∀ U : X.Opens, IsAffineOpen U → ∀ S : Set X, IsClosed S →
      ∀ E : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf),
      DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf) E →
      Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf S E →
        ∃ T : Triangle (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)),
          T.obj₁ = E ∧ T ∈ distTriang _ ∧ IsIso (adj.counit.app T.obj₂) ∧
          DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherent X.ringCatSheaf) T.obj₃ ∧
          Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf (S \ U)
            T.obj₃) :
    (derivedQuasicoherentComparison.{u} X).IsEquivalence := by
  let : RQ.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : RQ.IsTriangulated := adj.isTriangulated_rightAdjoint
  have : RQ.Additive := adj.right_adjoint_additive
  have hP : ∀ E, DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) E → IsIso (adj.counit.app E) := by
    refine property_of_finite_affine_support X (fun E => IsIso (adj.counit.app E))
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf))
      (fun E hE => ((RQ ⋙ (SheafOfModules.isQuasicoherent
        X.ringCatSheaf).ι.mapDerivedCategory).map_isZero hE).isIso hE _) (fun T hT h₂ h₃ => ?_)
      hstep
    exact isIso_app₁_of_isIso_app₂₃
      (RQ ⋙ (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory) (𝟭 _)
      adj.counit T hT h₂ h₃
  let a : derivedQuasicoherentComparison.{u} X ⊣
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙ RQ :=
    adj.restrictFullyFaithful (Functor.FullyFaithful.id _)
      (Functor.FullyFaithful.ofFullyFaithful
        (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι)
      (Functor.leftUnitor _ ≪≫ (derivedQuasicoherentComparisonCompι.{u} X).symm)
      (Functor.rightUnitor _).symm
  have hc : ∀ E : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory,
      IsIso (a.counit.app E) := by
    intro E
    have h1 : IsIso (adj.counit.app ((DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.obj E)) := hP E.obj E.property
    have h2 : IsIso ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.map (a.counit.app E)) := by
      dsimp only [a]
      rw [Adjunction.map_restrictFullyFaithful_counit_app]
      infer_instance
    exact isIso_of_reflects_iso _ (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι
  have := NatIso.isIso_of_isIso_app a.counit
  have := derivedQuasicoherentComparison_reflectsIsomorphisms X
  exact isEquivalence_of_reflectsIsomorphisms_of_isIso_counit a

/-! ### The dévissage step on an affine open -/

/-- **The counit of the derived coherator adjunction is invertible on a derived direct image from
an affine open.** Let `U ⊆ X` be an affine open with quasi-compact quasi-separated inclusion, let
`RQ_X` and `RQ_U` be right adjoints of the functors induced by the two inclusions of the
quasi-coherent modules, and suppose the square of [Stacks, Tag 09T6] commutes for the chosen
models `Rj_*` and `Φ` of derived direct image. Then the counit of `D(ι_X) ⊣ RQ_X` is invertible
at `Rj_*E` for every complex `E` of `𝒪_U`-modules with quasi-coherent cohomology.

Both `Rj_* ⋙ RQ_X` and `RQ_U ⋙ Φ` are right adjoint to `D(ι_X) ⋙ j^*`, so they agree; the
square of the hypothesis and the equivalence
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isAffine` on `U` then put
`adj` in the situation of
`Stacks.DerivedQCoh.isIso_counit_app_of_restrictFullyFaithful`, whose remaining inputs are the
full faithfulness of `Φ` and of `Rj_*`. -/
theorem isIso_coheratorCounit_derivedOpenPushforward (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) [QuasiCompact U.ι] [QuasiSeparated U.ι]
    (RQ : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (Scheme.QuasicoherentModules X))
    (adj : (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ⊣ RQ)
    (RQU : DerivedCategory (SheafOfModules.{u} U.toScheme.ringCatSheaf) ⥤
      DerivedCategory (Scheme.QuasicoherentModules U.toScheme))
    (adjU : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι.mapDerivedCategory ⊣ RQU)
    (e : derivedQuasicoherentPushforward U.ι ⋙ derivedQuasicoherentComparison.{u} X ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≅
      derivedQuasicoherentComparison.{u} U.toScheme ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).ι ⋙
        Stacks.Duality.derivedPushforward U.ι)
    (E : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).FullSubcategory) :
    IsIso (adj.counit.app ((Stacks.Duality.derivedPushforward U.ι).obj E.obj)) := by
  have : IsAffine U.toScheme := hU
  have := derivedQuasicoherentComparison_isEquivalence_of_isAffine U.toScheme
  obtain ⟨ffΦ⟩ := fullyFaithful_derivedQuasicoherentPushforward U
  obtain ⟨ffRj⟩ := fullyFaithful_derivedPushforward U.ι
  let JU := (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).ι
  let eqG : Stacks.Duality.derivedPushforward U.ι ⋙ RQ ≅
      RQU ⋙ derivedQuasicoherentPushforward U.ι :=
    (adj.comp (Stacks.Duality.OpenImmersion.derivedRestrictPushforwardAdjunction
      U.ι)).rightAdjointUniq
      (((derivedQuasicoherentRestrictPushforwardAdjunction U).comp adjU).ofNatIsoLeft
        (derivedQuasicoherentRestrictCompι U))
  exact isIso_counit_app_of_restrictFullyFaithful adj (G' := JU ⋙ RQU) ffΦ
    ((Functor.FullyFaithful.ofFullyFaithful JU).comp ffRj)
    (Functor.isoWhiskerLeft (derivedQuasicoherentPushforward U.ι)
      (derivedQuasicoherentComparisonCompι.{u} X).symm ≪≫ e)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft JU eqG ≪≫
      (Functor.associator _ _ _).symm) E


/-! ### The equivalence clause, granted its two inputs -/

/-- **The equivalence clause of [Stacks, Tag 09T6], with its two geometric inputs as
hypotheses.** Let `X` be a quasi-compact quasi-separated scheme. Assume

* `hadj`: every scheme has a right derived functor of its coherator, presented as an adjunction
  `D(ι) ⊣ RQ`;
* `hsquare`: for every affine open `U ⊆ X` the square of [Stacks, Tag 09T6] commutes at the
  chosen models `Stacks.DerivedQCoh.derivedQuasicoherentPushforward` and
  `Stacks.Duality.derivedPushforward` of derived direct image.

Then the comparison functor of [Stacks, Tag 06VT] is an equivalence.

The dévissage step demanded by
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_supportedTriangles` is the
restriction triangle `E ⟶ Rj_*(E|_U) ⟶ G` of
`Stacks.DerivedQCoh.exists_derivedRestriction_triangle`: its middle vertex has invertible counit
by `Stacks.DerivedQCoh.isIso_coheratorCounit_derivedOpenPushforward`, has quasi-coherent
cohomology because `hsquare` exhibits it as the image of a complex of quasi-coherent sheaves, and
its third vertex is supported on `S ∖ U`. That the middle vertex is still supported on `S` — the
remaining input of the triangle — is the open-immersion case of [Stacks, Tag 08DF],
`Stacks.DerivedQCoh.cohomologySupportedOn_derivedPushforward_scheme`. -/
theorem derivedQuasicoherentComparison_isEquivalence_of_square (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hadj : ∀ Z : Scheme.{u}, ∃ RQ : DerivedCategory (SheafOfModules.{u} Z.ringCatSheaf) ⥤
        DerivedCategory (Scheme.QuasicoherentModules Z),
        Nonempty ((SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι.mapDerivedCategory ⊣ RQ))
    (hsquare : ∀ U : X.Opens, IsAffineOpen U →
      ∀ [QuasiCompact U.ι] [QuasiSeparated U.ι],
      Nonempty (derivedQuasicoherentPushforward U.ι ⋙ derivedQuasicoherentComparison.{u} X ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ≅
        derivedQuasicoherentComparison.{u} U.toScheme ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).ι ⋙
          Stacks.Duality.derivedPushforward U.ι)) :
    (derivedQuasicoherentComparison.{u} X).IsEquivalence := by
  obtain ⟨RQ, ⟨adj⟩⟩ := hadj X
  refine derivedQuasicoherentComparison_isEquivalence_of_supportedTriangles X RQ adj ?_
  intro U hU S hS E hE hsup
  have hclosed : (DerivedCategoryB.derivedCategoryB
      (A := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  have hclosed₃ : (DerivedCategoryB.derivedCategoryB
      (A := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulatedClosed₃ := inferInstance
  have hUaff : IsAffine U.toScheme := hU
  have : CompactSpace U.toScheme := Scheme.compactSpace_of_isAffine _
  have hcomp := derivedQuasicoherentComparison_isEquivalence_of_isAffine U.toScheme
  obtain ⟨e⟩ := hsquare U hU
  obtain ⟨RQU, ⟨adjU⟩⟩ := hadj U.toScheme
  have hEU : DerivedCategoryB.derivedCategoryB
      (A := SheafOfModules.{u} U.toScheme.ringCatSheaf)
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)
      ((Stacks.Duality.OpenImmersion.derivedRestrict U.ι).obj E) :=
    @isQuasicoherent_derivedRestriction X U (modulesRestrict U) (modulesRestrict_eq_jStar U)
      (modulesRestrict_additive_resRing U) (modulesRestrict_preservesFiniteLimits_resRing U)
      (modulesRestrict_preservesFiniteColimits_resRing U) E hE
  let EU : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).FullSubcategory :=
    ⟨(Stacks.Duality.OpenImmersion.derivedRestrict U.ι).obj E, hEU⟩
  have hsupU : Cohomology.PushforwardRestriction.CohomologySupportedOn
      (ExtensionByZeroModules.resRing U X.ringCatSheaf) (Subtype.val ⁻¹' S)
      ((Stacks.Duality.OpenImmersion.derivedRestrict U.ι).obj E) :=
    @cohomologySupportedOn_derivedRestriction _ X.ringCatSheaf U S (modulesRestrict U)
      (modulesRestrict_eq_jStar U) (modulesRestrict_additive_resRing U)
      (modulesRestrict_preservesFiniteLimits_resRing U)
      (modulesRestrict_preservesFiniteColimits_resRing U) E hsup
  obtain ⟨T, hT1, hT2, hTdist, hTsupp⟩ :=
    exists_derivedRestriction_triangle X U S hS E hsup
      (cohomologySupportedOn_derivedPushforward_scheme X U S hS _ hsupU)
  have hcounit : IsIso (adj.counit.app T.obj₂) := by
    rw [hT2]
    exact isIso_coheratorCounit_derivedOpenPushforward X U hU RQ adj RQU adjU e EU
  have hqcoh : DerivedCategoryB.derivedCategoryB
      (A := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) T.obj₂ := by
    rw [hT2]
    let B := (derivedQuasicoherentComparison.{u} U.toScheme).objPreimage EU
    exact (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).prop_of_iso
        (e.app B ≪≫ (Stacks.Duality.derivedPushforward U.ι).mapIso
          ((DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).ι.mapIso
            ((derivedQuasicoherentComparison.{u} U.toScheme).objObjPreimageIso EU)))
        ((derivedQuasicoherentComparison.{u} X).obj
          ((derivedQuasicoherentPushforward U.ι).obj B)).property
  have hqcoh₃ : DerivedCategoryB.derivedCategoryB
      (A := SheafOfModules.{u} X.ringCatSheaf)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) T.obj₃ :=
    @ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ _ _ _ _ _ _ hclosed₃ hclosed T hTdist
      (hT1.symm ▸ hE) hqcoh
  exact ⟨T, hT1, hTdist, hcounit, hqcoh₃, hTsupp⟩

end Stacks.DerivedQCoh

end
