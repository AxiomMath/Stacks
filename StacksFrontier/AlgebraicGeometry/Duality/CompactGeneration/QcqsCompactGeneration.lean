module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QuasiAffineQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineSituation
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineDetection
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.CategoryTheory.Triangulated.CompactGluing
public import StacksFrontier.CategoryTheory.Triangulated.CompactLift
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.Homology.DerivedComplete.KoszulTensorVanishing

/-!
# `D_QCoh(𝒪_X)` is compactly generated for a quasi-compact quasi-separated scheme

This is [Stacks, Tag 09IS] in the form [Stacks, Tag 09SQ] defines and Brown representability
consumes: for `X` quasi-compact and quasi-separated, `D_QCoh(𝒪_X)` has a set of compact objects
which jointly generate it — in fact a single one.

## The proof

The source's proof (Bondal–van den Bergh, after Thomason–Trobaugh) is an induction over the number
of affine opens needed to cover `X`. Write `X = U ∪ V` with `U` a quasi-compact open covered by
fewer affines, `V = Spec A` affine, `W = U ∩ V = D(f₁) ∪ … ∪ D(f_r) ⊆ V`, and `Z = X ∖ U ⊆ V`.

* *Lifting along `W ⊆ V`* ([Stacks, Tag 08EK]): every compact `P` of `D_QCoh(𝒪_W)` has `P ⊕ P[1]`
  equal to the restriction of a compact object of `D_QCoh(𝒪_V)`. This is
  `CategoryTheory.Pretriangulated.exists_isCompactObject_iso_biprod_shift`, fed with the affine
  case of compact generation and with the Koszul complex `K` on the `f_i`, which is compact, dies
  on `W`, and detects the kernel of restriction to `W` by [Stacks, Tag 09IR].
* *Glueing* ([Stacks, Tag 08DG]): an object of `D_QCoh(𝒪_U)` and one of `D_QCoh(𝒪_V)` with
  isomorphic restrictions to `W` come from an object of `D_QCoh(𝒪_X)`. This is
  `CategoryTheory.Pretriangulated.exists_glue`, fed with the base change isomorphisms of
  [Stacks, Tag 08FE] for the Cartesian square of open immersions.
* *Compactness is local*: an object of `D_QCoh(𝒪_X)` whose restrictions to `U` and `V` are compact
  is compact, `CategoryTheory.Pretriangulated.isCompactObject_of_isCompactObject_restrict`.
* *Generation*: the glued objects `R_P` with `R_P|_U ≅ P ⊕ P[1]` for `P` in a generating family of
  `D_QCoh(𝒪_U)`, together with the object `K'` glued from `0` on `U` and `K` on `V`, generate: an
  object `E` orthogonal to `K'` has `E|_V` orthogonal to `K`, hence `E ≅ Rj_{U,*}(E|_U)` by the
  detection half of [Stacks, Tag 09IR], and then orthogonality to the `R_P` forces `E|_U = 0`.

## Main results

* `Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory` —
  `D_QCoh(𝒪_X)` is compactly generated for every quasi-compact quasi-separated scheme `X`: the
  content of [Stacks, Tag 09IS] that Brown representability consumes, with the generators
  exhibited as compact objects rather than as perfect ones.
* `Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs` —
  **[Stacks, Tag 0A9E]**: for a morphism `f : X ⟶ Y` of quasi-compact quasi-separated schemes,
  `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint; and its companion
  `DerivedPushforward.exists_isTriangulated_rightAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs`,
  with the adjoint exhibited as exact.

## Implementation notes

**The model.** All derived categories are the locally small ones,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whose morphisms live in the universe `u` of
the schemes. Brown representability ([Stacks, Tag 0A8G]) asks for direct sums indexed by the
morphism universe; at `CategoryTheory.HasDerivedCategory.standard` that universe is `u + 1` and
those direct sums do not exist, so compact generation and [Stacks, Tag 0A9E] are stated where they
have content.

**Compact rather than perfect.** [Stacks, Tag 09IS] asks for a single *perfect* generator; the
generators built here are compact, which is what [Stacks, Tag 0A9E] consumes. Identifying the two
classes is [Stacks, Tag 09M1], not used here, so no `@[stacks 09IS]` attribute is placed.

## References

* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09SQ](https://stacks.math.columbia.edu/tag/09SQ)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated ZeroObject

universe u

namespace Stacks.Duality.QcqsGeneration

open Stacks.Duality.OpenImmersion

/-! ### Isomorphisms are local along a jointly surjective family of open immersions -/

/-- A morphism of sheaves of modules which becomes invertible on each member of a jointly
surjective family of open immersions is invertible: invertibility is tested on stalks, and the
stalks of a restriction are the stalks of the sheaf. -/
theorem isIso_of_isIso_restrictFunctor {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {I : Type*} {U : I → Scheme.{u}} (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcov : ∀ x : X, ∃ i y, j i y = x)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (j i)).map φ)) : IsIso φ := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk φ fun x => ?_
  obtain ⟨i, y, rfl⟩ := hcov x
  change IsIso ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} ((j i) y)).map φ)
  have : IsIso ((Scheme.Modules.restrictFunctor (j i)).map φ) := h i
  have h3 : IsIso ((Scheme.Modules.restrictFunctor (j i) ⋙ Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map φ) :=
    Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y) _
  have h2 : IsIso ((Scheme.Modules.restrictStalkNatIso (j i) y).hom.app M ≫
      (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} ((j i) y)).map φ) := by
    rw [← (Scheme.Modules.restrictStalkNatIso (j i) y).hom.naturality φ]
    infer_instance
  exact IsIso.of_isIso_comp_left ((Scheme.Modules.restrictStalkNatIso (j i) y).hom.app M) _

/-- A morphism of `D(𝒪_X)` which becomes invertible on each member of a jointly surjective family
of open immersions is invertible: restriction commutes with the cohomology sheaves. -/
theorem isIso_of_isIso_derivedRestrict {X : Scheme.{u}} {E F : DerivedCategory X.Modules}
    (φ : E ⟶ F) {I : Type*} {U : I → Scheme.{u}} (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ i y, j i y = x)
    (h : ∀ i, IsIso ((derivedRestrict (j i)).map φ)) : IsIso φ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_restrictFunctor _ j hcov fun i => ?_
  have := h i
  have h' : IsIso ((DerivedCategory.homologyFunctor _ n).map ((derivedRestrict (j i)).map φ)) :=
    inferInstance
  exact (NatIso.isIso_map_iff
    ((Scheme.Modules.restrictFunctor (j i)).mapDerivedCategoryHomologyIso n) φ).1 h'

/-- An object of `D(𝒪_X)` which vanishes on each member of a jointly surjective family of open
immersions vanishes. -/
theorem isZero_of_isZero_derivedRestrict {X : Scheme.{u}} {E : DerivedCategory X.Modules}
    {I : Type*} {U : I → Scheme.{u}} (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ i y, j i y = x)
    (h : ∀ i, IsZero ((derivedRestrict (j i)).obj E)) : IsZero E := by
  have : IsIso (0 : (0 : DerivedCategory X.Modules) ⟶ E) :=
    isIso_of_isIso_derivedRestrict _ j hcov fun i =>
      isIso_of_source_target_iso_zero _
        (((derivedRestrict (j i)).map_isZero (isZero_zero _)).isoZero)
        ((h i).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : (0 : DerivedCategory X.Modules) ⟶ E)).symm

/-! ### Base change for a Cartesian square of open immersions -/

attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

/-- **[Stacks, Tag 08FE] for a Cartesian square of schemes whose vertical sides are open
immersions**, at the locally small model and in the restriction spelling `derivedRestrict`: the
restriction to `V` of `Rf_* E` is the derived direct image along `g` of the restriction of `E` to
`U`. -/
def baseChangeIso {X Y U V : Scheme.{u}} (f : X ⟶ Y) (i : U ⟶ X) (j : V ⟶ Y) (g : U ⟶ V)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : IsPullback i g f j)
    (E : DerivedCategory X.Modules) :
    (derivedRestrict j).obj ((Stacks.Duality.derivedPushforward f).obj E) ≅
      (Stacks.Duality.derivedPushforward g).obj ((derivedRestrict i).obj E) := by
  let Fi := Scheme.Modules.pullback i
  let Fj := Scheme.Modules.pullback j
  let Ri := Fi.mapDerivedCategory
  let Rj := Fj.mapDerivedCategory
  let αi := Fi.mapDerivedCategoryFactorsh.inv
  let αj := Fj.mapDerivedCategoryFactorsh.inv
  have hiR : Ri.IsRightDerivedFunctor αi
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ Ri Fi.mapDerivedCategoryFactorsh
  have hjR : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ Rj Fj.mapDerivedCategoryFactorsh
  have hfR : (Stacks.Duality.derivedPushforward f).IsRightDerivedFunctor
      (Stacks.Duality.derivedPushforwardUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := inferInstance
  have hgR : (Stacks.Duality.derivedPushforward g).IsRightDerivedFunctor
      (Stacks.Duality.derivedPushforwardUnit g)
      (HomotopyCategory.quasiIso U.Modules (ComplexShape.up ℤ)) := inferInstance
  let e : Stacks.Duality.derivedPushforward f ⋙ Rj ≅ Ri ⋙ Stacks.Duality.derivedPushforward g :=
    @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _
      f.toLRSHom.toShHom i.toLRSHom.toShHom j.toLRSHom.toShHom g.toLRSHom.toShHom
      _ _ (isPullback_toShHom i g f j h) _ _ _ _
      (Stacks.Duality.derivedPushforward f) (Stacks.Duality.derivedPushforward g) Ri Rj
      (Stacks.Duality.derivedPushforwardUnit f) (Stacks.Duality.derivedPushforwardUnit g)
      αi αj hfR hgR hiR hjR
  exact (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso
        (Scheme.Modules.restrictFunctor j) Fj
        (Scheme.Modules.restrictFunctorIsoPullback j)).app _ ≪≫
    e.app E ≪≫
    (Stacks.Duality.derivedPushforward g).mapIso
      ((Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso
        (Scheme.Modules.restrictFunctor i) Fi
        (Scheme.Modules.restrictFunctorIsoPullback i)).app E).symm

/-! ### Restriction and direct image on the quasi-coherent derived categories -/

section Restricted

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- `j^*` on the quasi-coherent derived categories is exact. -/
instance isTriangulated_restrictedDerivedRestrict :
    (restrictedDerivedRestrict j).IsTriangulated := by
  have : NatTrans.CommShift (restrictedDerivedRestrictCompιIso j).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  rw [Functor.isTriangulated_iff_comp_right (restrictedDerivedRestrictCompιIso j)]
  infer_instance

variable [AlgebraicGeometry.QuasiCompact j] [CompactSpace X]

/-- The counit of `j^* ⊣ Rj_*` on the quasi-coherent derived categories is invertible: the
inclusions carry it to the counit on `D(𝒪)`, which is invertible because `j` is an open
immersion ([Stacks, Tag 08DF]). -/
instance isIso_restrictedDerivedRestrictAdjunction_counit :
    IsIso (restrictedDerivedRestrictAdjunction j).counit := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun L => ?_
  have h : (DerivedCategoryB.derivedCategoryB (A := U.Modules)
      (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι.map
        ((restrictedDerivedRestrictAdjunction j).counit.app L) =
      (derivedRestrictPushforwardAdjunction j).counit.app L.obj := by
    change (DerivedCategoryB.derivedCategoryB (A := U.Modules)
      (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι.map
        ((liftDerivedRestrictPushforwardAdjunction j _ _ _ _).counit.app L) = _
    unfold liftDerivedRestrictPushforwardAdjunction
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp [ObjectProperty.liftCompιIso]
  have : IsIso ((DerivedCategoryB.derivedCategoryB (A := U.Modules)
      (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι.map
        ((restrictedDerivedRestrictAdjunction j).counit.app L)) := by
    rw [h]
    infer_instance
  exact isIso_of_reflects_iso _ (DerivedCategoryB.derivedCategoryB (A := U.Modules)
    (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι

/-- The unit of `j^* ⊣ Rj_*` on the quasi-coherent derived categories is invertible exactly when
the unit on `D(𝒪)` is. -/
theorem isIso_restrictedDerivedRestrictAdjunction_unit_app_iff
    (E : Stacks.Duality.quasiCoherentDerivedCategory X) :
    IsIso ((restrictedDerivedRestrictAdjunction j).unit.app E) ↔
      IsIso ((derivedRestrictPushforwardAdjunction j).unit.app E.obj) :=
  isIso_liftDerivedRestrictPushforwardAdjunction_unit_app_iff j _ _ _ _ E

end Restricted

/-! ### Morphisms out of shifts, in the full subcategory and outside it -/

/-- An object `E` of a triangulated subcategory receives no nonzero morphism from the shifts of
`K` inside the subcategory exactly when it receives none from the shifts of `K` in the ambient
category: the inclusion is fully faithful and commutes with the shift. -/
theorem forall_hom_shift_eq_zero_iff {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.IsTriangulated] (K E : P.FullSubcategory) :
    (∀ (n : ℤ) (g : K⟦n⟧ ⟶ E), g = 0) ↔ (∀ (n : ℤ) (g : K.obj⟦n⟧ ⟶ E.obj), g = 0) := by
  constructor
  · intro h n g
    have e := (P.ι.commShiftIso n).app K
    have h0 : P.ι.map (P.fullyFaithfulι.preimage (e.hom ≫ g)) = 0 := by
      rw [h n (P.fullyFaithfulι.preimage (e.hom ≫ g)), Functor.map_zero]
    rw [P.fullyFaithfulι.map_preimage] at h0
    simpa using (cancel_epi e.hom).1 (h0.trans (comp_zero).symm)
  · intro h n g
    have e := (P.ι.commShiftIso n).app K
    refine P.ι.map_injective ?_
    rw [Functor.map_zero, ← cancel_epi e.inv]
    exact (h n _).trans (comp_zero).symm

/-! ### The Koszul complex -/

section Koszul

open Stacks.Koszul.Truncation

variable {A : Type u} [CommRing A]

/-- The Koszul complex of a finite sequence is a compact object of `D(A)`: it is built from `A`
in degree zero by finitely many cones of multiplication maps ([Stacks, Tag 0629]). -/
theorem isCompactObject_derivedKoszul : ∀ {r : ℕ} (f : Fin r → A),
    IsCompactObject.{u} (derivedKoszul f)
  | 0, f => by
      have := Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory (ModuleCat.{u} A)
      have : IsCompactObject.{u} (ModuleCat.of A A) :=
        StacksDraft.Perfect.isCompactObject_regularModule
      exact isCompactObject_of_iso (KoszulTensorVanishing.koszul_empty_iso_single f)
        (StacksDraft.Perfect.isCompactObject_derived_single _ 0)
  | r + 1, f => by
      have := Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory (ModuleCat.{u} A)
      obtain ⟨g, a, rfl⟩ : ∃ (g : Fin r → A) (a : A), Fin.snoc g a = f :=
        ⟨Fin.init f, f (Fin.last r), Fin.snoc_init_self f⟩
      obtain ⟨b, c, hT⟩ := exists_derivedKoszul_snoc_triangle g a
      have h := isCompactObject_derivedKoszul g
      exact isCompactObject_obj₃ _ hT h h

/-- Derived sheafification carries compact objects of `D(R)` to compact objects of
`D_QCoh(𝒪_{Spec R})`, being an equivalence ([Stacks, Tag 06Z0]). Stated at an opaque `R`, where
instance synthesis finds the equivalence. -/
theorem isCompactObject_derivedTilde_obj (R : CommRingCat.{u})
    (X : DerivedCategory (ModuleCat.{u} R)) (hX : IsCompactObject.{u} X) :
    IsCompactObject.{u} ((derivedTilde R).obj X) :=
  (isCompactObject_iff_isCompactObject_obj (derivedTilde R) _).mp hX

/-- The Koszul complex of a finite sequence in `A`, as an object of `D_QCoh(𝒪_{Spec A})`: the
derived sheafification of the Koszul complex of `D(A)`. Its underlying object is
`Stacks.Koszul.Truncation.koszulObject f`, by `koszulQC_obj_iso`. -/
abbrev koszulQC {r : ℕ} (f : Fin r → A) :
    Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of A)) :=
  (derivedTilde (CommRingCat.of A)).obj (derivedKoszul f)

/-- The underlying object of `koszulQC f` is the sheafified Koszul complex. -/
def koszulQC_obj_iso {r : ℕ} (f : Fin r → A) : (koszulQC f).obj ≅ koszulObject f :=
  (derivedTildeCompι (CommRingCat.of A)).app _ ≪≫
    ((tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors).app _

/-- An object of `D(𝒪_{Spec A})` receiving no nonzero morphism from the shifts of `koszulQC f`
receives none from the shifts of the sheafified Koszul complex. -/
private theorem eq_zero_of_forall_hom_koszulQC_eq_zero {r : ℕ} (f : Fin r → A)
    {E : DerivedCategory (Spec (CommRingCat.of A)).Modules}
    (h : ∀ (n : ℤ) (g : (koszulQC f).obj⟦n⟧ ⟶ E), g = 0) (n : ℤ)
    (g : (koszulObject f)⟦n⟧ ⟶ E) : g = 0 := by
  rw [← cancel_epi ((shiftFunctor _ n).map (koszulQC_obj_iso f).hom),
    h n ((shiftFunctor _ n).map (koszulQC_obj_iso f).hom ≫ g), comp_zero]

/-- The sheafified Koszul complex is compact in `D_QCoh(𝒪_{Spec A})`: derived sheafification is an
equivalence `D(A) ≌ D_QCoh(𝒪_{Spec A})` ([Stacks, Tag 06Z0]). -/
theorem isCompactObject_koszulQC {r : ℕ} (f : Fin r → A) :
    IsCompactObject.{u} (koszulQC f) :=
  isCompactObject_derivedTilde_obj _ _ (isCompactObject_derivedKoszul f)

/-- The sheafified Koszul complex restricts to zero on `D(f₁) ∪ … ∪ D(f_r)`. -/
theorem isZero_restrictedDerivedRestrict_koszulQC {r : ℕ} (f : Fin r → A) :
    IsZero ((restrictedDerivedRestrict (openComplement f).ι).obj (koszulQC f)) :=
  isZero_fullSubcategory_of_isZero_obj
    ((Stacks.Koszul.OpenComplement.isZero_derivedRestrict_koszulObject f).of_iso
      ((derivedRestrict (openComplement f).ι).mapIso (koszulQC_obj_iso f)))

/-- **[Stacks, Tag 09IR], (2) implies (1), on `D_QCoh(𝒪_{Spec A})`.** An object right orthogonal
to every shift of the Koszul complex has invertible unit `E ⟶ Rj_*(E|_U)`. -/
theorem isIso_unit_of_forall_hom_koszulQC_eq_zero {r : ℕ} (f : Fin r → A)
    (E : Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of A)))
    (h : ∀ (n : ℤ) (g : (koszulQC f)⟦n⟧ ⟶ E), g = 0) :
    IsIso ((restrictedDerivedRestrictAdjunction (openComplement f).ι).unit.app E) := by
  rw [isIso_restrictedDerivedRestrictAdjunction_unit_app_iff]
  have h' := (forall_hom_shift_eq_zero_iff _ _ _).1 h
  exact isIso_unit_of_hom_koszulObject_eq_zero f E.obj E.2
    (eq_zero_of_forall_hom_koszulQC_eq_zero f h')

end Koszul

/-! ### Lifting compact objects from `D(f₁) ∪ … ∪ D(f_r)` to `Spec A` -/

section AffineLift

open Stacks.Koszul.Truncation

variable {A : Type u} [CommRing A]

/-- **[Stacks, Tag 08EK] up to the passage from perfect to compact objects.** Let
`W = D(f₁) ∪ … ∪ D(f_r) ⊆ Spec A`. For every compact object `P` of `D_QCoh(𝒪_W)` there is a
compact object `Q` of `D_QCoh(𝒪_{Spec A})` whose restriction to `W` is `P ⊕ P[1]`.

This is `CategoryTheory.Pretriangulated.exists_isCompactObject_iso_biprod_shift` for restriction
to `W`, whose right adjoint `Rj_*` is fully faithful and commutes with direct sums
([Stacks, Tag 08DZ]): `D_QCoh(𝒪_{Spec A})` is compactly generated by the structure sheaf, and the
kernel of restriction is detected by the Koszul complex ([Stacks, Tag 09IR]). -/
theorem exists_isCompactObject_restrict_iso_biprod_shift {r : ℕ} (f : Fin r → A)
    (P : Stacks.Duality.quasiCoherentDerivedCategory (openComplement f).toScheme)
    (hP : IsCompactObject.{u} P) :
    ∃ Q : Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of A)),
      IsCompactObject.{u} Q ∧
        Nonempty ((restrictedDerivedRestrict (openComplement f).ι).obj Q ≅ P ⊞ P⟦(1 : ℤ)⟧) := by
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward (openComplement f).ι
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs
          (openComplement f).ι)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward (openComplement f).ι
  obtain ⟨G, hG, hgen⟩ :=
    QuasiAffineGeneration.exists_isCompactObject_isWeakTriangulatedGenerator_of_isQuasiAffine
      (Spec (CommRingCat.of A))
  let K : PUnit.{u + 1} → Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of A)) :=
    fun _ => koszulQC f
  have hK : ∀ i, IsCompactObject.{u} (K i) := fun _ => isCompactObject_koszulQC f
  let G₀ : PUnit.{u + 1} → Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of A)) :=
    fun _ => G
  have hG₀ : ∀ i, IsCompactObject.{u} (G₀ i) := fun _ => hG
  have hgen' : (ofObj G₀).IsWeakTriangulatedGenerator := by
    change (ofObj fun _ : PUnit.{u + 1} => G).IsWeakTriangulatedGenerator
    rw [Stacks.Duality.AffineGeneration.ofObj_const_eq_singleton]
    exact hgen
  exact exists_isCompactObject_iso_biprod_shift
    (restrictedDerivedRestrictAdjunction (openComplement f).ι) K hK
    (fun _ => isZero_restrictedDerivedRestrict_koszulQC f)
    (fun E hE => isIso_unit_of_forall_hom_koszulQC_eq_zero f E fun n g => hE PUnit.unit n g)
    G₀ hG₀ hgen' P hP

end AffineLift

/-! ### Two formal facts about an adjunction with invertible counit -/

section Formal

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
  {a : C ⥤ D} {R : D ⥤ C} (adj : a ⊣ R) [a.Additive] [R.Additive]

omit [a.Additive] in
include adj in
/-- A morphism `X ⟶ N` vanishes when `a X = 0` and the unit is invertible at `N`: it factors as
`X ⟶ R a X ⟶ R a N ≅ N`. -/
theorem eq_zero_of_isZero_obj_of_isIso_unit {X N : C} (hX : IsZero (a.obj X))
    (hN : IsIso (adj.unit.app N)) (h : X ⟶ N) : h = 0 := by
  have hnat := adj.unit.naturality h
  dsimp at hnat
  rw [hX.eq_of_src (a.map h) 0, R.map_zero, comp_zero] at hnat
  rw [← cancel_mono (adj.unit.app N), hnat, zero_comp]

omit [R.Additive] in
include adj in
/-- If the unit is invertible at `E`, morphisms `X ⟶ E` are the morphisms `a X ⟶ a E`: a morphism
`a X ⟶ a E` vanishes as soon as all morphisms `X ⟶ E` do. -/
theorem eq_zero_of_isIso_unit {X E : C} (hE : IsIso (adj.unit.app E))
    (h : ∀ g : X ⟶ E, g = 0) (k : a.obj X ⟶ a.obj E) : k = 0 := by
  have h₁ := h (adj.homEquiv _ _ k ≫ inv (adj.unit.app E))
  have h₂ : adj.homEquiv _ _ k = 0 := by
    rw [← cancel_mono (inv (adj.unit.app E)), h₁, zero_comp]
  rw [← (adj.homEquiv _ _).symm_apply_apply k, h₂, Adjunction.homEquiv_counit, a.map_zero,
    zero_comp]

end Formal

/-! ### The inductive step -/

/-- A morphism `g : X⟦n⟧ ⟶ F E` out of a retract `X` of `F Y` vanishes when its composite with the
comparison `F (Y⟦n⟧) ≅ (F Y)⟦n⟧` and the retraction does. -/
private theorem eq_zero_of_retract_commShift {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]
    {X : D} {Y E : C} (i : X ⟶ F.obj Y) (p : F.obj Y ⟶ X) (hip : i ≫ p = 𝟙 X) (n : ℤ)
    (g : X⟦n⟧ ⟶ F.obj E) (h : (F.commShiftIso n).hom.app Y ≫ (shiftFunctor D n).map p ≫ g = 0) :
    g = 0 := by
  calc g = (shiftFunctor D n).map i ≫ (F.commShiftIso n).inv.app Y ≫
        ((F.commShiftIso n).hom.app Y ≫ (shiftFunctor D n).map p ≫ g) := by
        simp [← Functor.map_comp_assoc, hip]
    _ = 0 := by rw [h, comp_zero, comp_zero]

section Step

open Stacks.Koszul.Truncation

variable {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
  {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
  {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
  {r : ℕ} (f : Fin r → A) (iU : (openComplement f).toScheme ⟶ U) [IsOpenImmersion iU]
  (hsq : IsPullback iU (openComplement f).ι jU jV)
  (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))

omit [QuasiSeparatedSpace Y] [CompactSpace Y] [CompactSpace U] [QuasiSeparatedSpace U] in
/-- For a commutative square of open immersions `a ≫ p = b ≫ q`, an object killed by restriction
along `q` is killed by restriction along `p` followed by `a`. -/
theorem isZero_derivedRestrict_comp_of_isZero {W₀ U₀ V₀ : Scheme.{u}} (a : W₀ ⟶ U₀) (b : W₀ ⟶ V₀)
    (p : U₀ ⟶ Y) (q : V₀ ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion p]
    [IsOpenImmersion q] (w : a ≫ p = b ≫ q) {E : DerivedCategory Y.Modules}
    (hE : IsZero ((derivedRestrict q).obj E)) :
    IsZero ((derivedRestrict a).obj ((derivedRestrict p).obj E)) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  have h₁ : IsZero ((Scheme.Modules.restrictFunctor q).obj
      ((DerivedCategory.homologyFunctor Y.Modules n).obj E)) :=
    isZero_restrictFunctor_homology_of_isZero_derivedRestrict q E hE n
  have h₂ : IsZero ((Scheme.Modules.restrictFunctor b).obj
      ((Scheme.Modules.restrictFunctor q).obj
        ((DerivedCategory.homologyFunctor Y.Modules n).obj E))) :=
    (Scheme.Modules.restrictFunctor b).map_isZero h₁
  have e₁ := (Scheme.Modules.restrictFunctorComp b q).app
    ((DerivedCategory.homologyFunctor Y.Modules n).obj E)
  have e₂ := (Scheme.Modules.restrictFunctorComp a p).app
    ((DerivedCategory.homologyFunctor Y.Modules n).obj E)
  have e₃ := (Scheme.Modules.restrictFunctorCongr w).app
    ((DerivedCategory.homologyFunctor Y.Modules n).obj E)
  have h₃ : IsZero ((Scheme.Modules.restrictFunctor a).obj
      ((Scheme.Modules.restrictFunctor p).obj
        ((DerivedCategory.homologyFunctor Y.Modules n).obj E))) :=
    h₂.of_iso (e₂.symm ≪≫ e₃ ≪≫ e₁)
  refine h₃.of_iso ?_
  exact ((Scheme.Modules.restrictFunctor a).mapDerivedCategoryHomologyIso n).app _ ≪≫
    (Scheme.Modules.restrictFunctor a).mapIso
      (((Scheme.Modules.restrictFunctor p).mapDerivedCategoryHomologyIso n).app E)

omit [QuasiSeparatedSpace Y] [CompactSpace Y] [CompactSpace U] [QuasiSeparatedSpace U] in
/-- Two open immersions covering `Y` jointly detect isomorphisms of `D(𝒪_Y)`. -/
theorem isIso_of_isIso_derivedRestrict₂ {E F : DerivedCategory Y.Modules} (φ : E ⟶ F)
    (hφU : IsIso ((derivedRestrict jU).map φ)) (hφV : IsIso ((derivedRestrict jV).map φ))
    (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y)) : IsIso φ := by
  let Us : Bool → Scheme.{u} := fun b => cond b U (Spec (CommRingCat.of A))
  let js : ∀ b, Us b ⟶ Y := fun b => match b with
    | true => jU
    | false => jV
  have : ∀ b, IsOpenImmersion (js b) := fun b => by cases b <;> (dsimp [js]; infer_instance)
  refine isIso_of_isIso_derivedRestrict φ js (fun y => ?_) fun b => ?_
  · rcases hcov y with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨true, x, hx⟩
    · exact ⟨false, x, hx⟩
  · cases b
    · exact hφV
    · exact hφU

omit [QuasiSeparatedSpace Y] [CompactSpace Y] [CompactSpace U] [QuasiSeparatedSpace U] in
/-- Two open immersions covering `Y` jointly detect the zero objects of `D(𝒪_Y)`. -/
theorem isZero_of_isZero_derivedRestrict₂ {E : DerivedCategory Y.Modules}
    (hU : IsZero ((derivedRestrict jU).obj E)) (hV : IsZero ((derivedRestrict jV).obj E))
    (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y)) : IsZero E := by
  have : IsIso (0 : (0 : DerivedCategory Y.Modules) ⟶ E) :=
    isIso_of_isIso_derivedRestrict₂ jU jV _
      (isIso_of_source_target_iso_zero _
        (((derivedRestrict jU).map_isZero (isZero_zero _)).isoZero) hU.isoZero)
      (isIso_of_source_target_iso_zero _
        (((derivedRestrict jV).map_isZero (isZero_zero _)).isoZero) hV.isoZero) hcov
  exact (isZero_zero _).of_iso (asIso (0 : (0 : DerivedCategory Y.Modules) ⟶ E)).symm

omit [QuasiSeparatedSpace U] in
include hsq hcov in
/-- **An object of `D_QCoh(𝒪_Y)` vanishing on `V` comes from `U`**: the unit
`N ⟶ Rj_{U,*}(N|_U)` is invertible. It is so on `U` because `Rj_{U,*}` is fully faithful, and on
`V` both sides vanish, the target by base change to the overlap. -/
theorem isIso_unit_of_isZero_restrict (N : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hN : IsZero ((restrictedDerivedRestrict jV).obj N)) :
    IsIso ((restrictedDerivedRestrictAdjunction jU).unit.app N) := by
  rw [isIso_restrictedDerivedRestrictAdjunction_unit_app_iff]
  have hNV : IsZero ((derivedRestrict jV).obj N.obj) :=
    (DerivedCategoryB.derivedCategoryB (A := Spec (CommRingCat.of A) |>.Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).ι.map_isZero hN
  refine isIso_of_isIso_derivedRestrict₂ jU jV _ ?_ ?_ hcov
  · exact isIso_map_unit_of_isIso_counit (derivedRestrictPushforwardAdjunction jU) N.obj
      inferInstance
  · have : (Stacks.Duality.derivedPushforward (openComplement f).ι).IsRightAdjoint :=
      inferInstance
    refine isIso_of_source_target_iso_zero _ hNV.isoZero ?_
    exact baseChangeIso jU iU jV (openComplement f).ι hsq _ ≪≫
      ((Stacks.Duality.derivedPushforward (openComplement f).ι).map_isZero
        (isZero_derivedRestrict_comp_of_isZero iU (openComplement f).ι jU jV hsq.w hNV)).isoZero

include hsq hcov in
/-- **The inductive step of [Stacks, Tag 09IS], at a given family of generators.** Let `Y` be a
quasi-compact quasi-separated scheme covered by a quasi-compact open `j_U : U ⟶ Y` and an affine
open `j_V : Spec A ⟶ Y` whose overlap is `D(f₁) ∪ … ∪ D(f_r) ⊆ Spec A`, and let
`P : ι → D_QCoh(𝒪_U)` be a family of compact objects generating `D_QCoh(𝒪_U)`. Then `D_QCoh(𝒪_Y)`
is generated by a family of compact objects indexed by `Option ι`: the glued objects `R_P` with
`R_P|_U ≅ P ⊕ P[1]`, and the object `K'` glued from `0` on `U` and the Koszul complex on `Spec A`.

Keeping the index type visible is what lets a finite family of generators propagate along the
induction over an affine cover; `Stacks.Duality.QcqsGeneration.isCompactlyGenerated_of_step` is
this statement with the index type forgotten. -/
theorem exists_compact_generators_option_of_step {ι : Type u}
    (P : ι → Stacks.Duality.quasiCoherentDerivedCategory U)
    (hPc : ∀ i, IsCompactObject.{u} (P i)) (hPgen : (ofObj P).IsWeakTriangulatedGenerator) :
    ∃ E : Option ι → Stacks.Duality.quasiCoherentDerivedCategory Y,
      (∀ o, IsCompactObject.{u} (E o)) ∧ (ofObj E).IsWeakTriangulatedGenerator := by
  -- the four adjunctions
  let adjU := restrictedDerivedRestrictAdjunction jU
  let adjV := restrictedDerivedRestrictAdjunction jV
  let adjU' := restrictedDerivedRestrictAdjunction iU
  let adjV' := restrictedDerivedRestrictAdjunction (openComplement f).ι
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).CommShift ℤ :=
    adjU.rightAdjointCommShift ℤ
  let : adjU.CommShift ℤ := adjU.commShift_of_leftAdjoint ℤ
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jV
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).CommShift ℤ :=
    adjV.rightAdjointCommShift ℤ
  let : adjV.CommShift ℤ := adjV.commShift_of_leftAdjoint ℤ
  let : adjV.IsTriangulated := Adjunction.IsTriangulated.mk' adjV
  have := adjV.isTriangulated_rightAdjoint
  have : PreservesBinaryBiproducts (restrictedDerivedRestrict iU) :=
    have := adjU'.leftAdjoint_preservesColimits
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).Additive :=
    adjU.right_adjoint_additive
  have : (Stacks.Duality.quasiCoherentDerivedPushforward jV
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).Additive :=
    adjV.right_adjoint_additive
  have : (Stacks.Duality.quasiCoherentDerivedPushforward iU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs iU)).Additive :=
    adjU'.right_adjoint_additive
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward jU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward jU
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward jV
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward jV
  have : ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward iU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs iU)) :=
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward iU
  -- base change
  let βVU : ∀ A' : Stacks.Duality.quasiCoherentDerivedCategory U,
      (restrictedDerivedRestrict jV).obj ((Stacks.Duality.quasiCoherentDerivedPushforward jU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).obj A') ≅
      (Stacks.Duality.quasiCoherentDerivedPushforward (openComplement f).ι
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs
          (openComplement f).ι)).obj ((restrictedDerivedRestrict iU).obj A') := fun A' =>
    (DerivedCategoryB.derivedCategoryB (A := Spec (CommRingCat.of A) |>.Modules)
      (SheafOfModules.isQuasicoherent
        (Spec (CommRingCat.of A)).ringCatSheaf)).fullyFaithfulι.preimageIso
      (baseChangeIso jU iU jV (openComplement f).ι hsq A'.obj)
  let βUV : ∀ Q' : Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of A)),
      (restrictedDerivedRestrict jU).obj ((Stacks.Duality.quasiCoherentDerivedPushforward jV
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).obj Q') ≅
      (Stacks.Duality.quasiCoherentDerivedPushforward iU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs iU)).obj
          ((restrictedDerivedRestrict (openComplement f).ι).obj Q') := fun Q' =>
    (DerivedCategoryB.derivedCategoryB (A := U.Modules)
      (SheafOfModules.isQuasicoherent U.ringCatSheaf)).fullyFaithfulι.preimageIso
      (baseChangeIso jV (openComplement f).ι jU iU hsq.flip Q'.obj)
  have hker : ∀ N : Stacks.Duality.quasiCoherentDerivedCategory Y,
      IsZero ((restrictedDerivedRestrict jV).obj N) → IsIso (adjU.unit.app N) :=
    fun N hN => isIso_unit_of_isZero_restrict jU jV f iU hsq hcov N hN
  -- the lifts and the glued objects
  have hPW : ∀ i, IsCompactObject.{u} ((restrictedDerivedRestrict iU).obj (P i)) := fun i =>
    isCompactObject_map_of_adjunction adjU' (hPc i)
  choose Q hQc hQ using fun i => exists_isCompactObject_restrict_iso_biprod_shift f
    ((restrictedDerivedRestrict iU).obj (P i)) (hPW i)
  let φ : ∀ i, (restrictedDerivedRestrict iU).obj (P i ⊞ (P i)⟦(1 : ℤ)⟧) ≅
      (restrictedDerivedRestrict (openComplement f).ι).obj (Q i) := fun i =>
    (restrictedDerivedRestrict iU).mapBiprod _ _ ≪≫
      biprod.mapIso (Iso.refl _) (((restrictedDerivedRestrict iU).commShiftIso (1 : ℤ)).app _) ≪≫
      (hQ i).some.symm
  choose R hRU hRV using fun i => exists_glue adjU adjV adjV' βVU βUV
    (P i ⊞ (P i)⟦(1 : ℤ)⟧) (Q i) (φ i)
  obtain ⟨K', hK'U, hK'V⟩ := exists_glue adjU adjV adjV' βVU βUV 0 (koszulQC f)
    (((restrictedDerivedRestrict iU).map_isZero (isZero_zero _)).iso
      (isZero_restrictedDerivedRestrict_koszulQC f))
  have hK'U0 : IsZero ((restrictedDerivedRestrict jU).obj K') :=
    (isZero_zero _).of_iso hK'U.some
  refine ⟨fun o => o.elim K' R, fun o => ?_, ?_⟩
  · -- compactness
    cases o with
    | none =>
      exact isCompactObject_of_isCompactObject_restrict adjU adjV hker K'
        (isCompactObject_of_iso hK'U.some
          (isCompactObject_zero' (T := Stacks.Duality.quasiCoherentDerivedCategory U)))
        (isCompactObject_of_iso hK'V.some (isCompactObject_koszulQC f))
    | some i =>
      exact isCompactObject_of_isCompactObject_restrict adjU adjV hker (R i)
        (isCompactObject_of_iso (hRU i).some
          (isCompactObject_biprod (hPc i) (isCompactObject_shift (hPc i) 1)))
        (isCompactObject_of_iso (hRV i).some (hQc i))
  · -- generation
    intro E hE
    rw [rightOrthogonal_shiftClosure_ofObj_iff] at hE
    -- Step 1: `E|_{Spec A}` is right orthogonal to the Koszul complex
    have h1 : ∀ (n : ℤ) (g : (koszulQC f)⟦n⟧ ⟶ (restrictedDerivedRestrict jV).obj E), g = 0 := by
      intro n g
      obtain ⟨N, π, δ, hT⟩ := distinguished_cocone_triangle (adjV.unit.app E)
      have hNV : IsZero ((restrictedDerivedRestrict jV).obj N) :=
        Triangle.isZero₃_of_isIso₁ _ ((restrictedDerivedRestrict jV).map_distinguished _ hT)
          (isIso_map_unit_of_isIso_counit adjV E inferInstance)
      have hK'n : IsZero ((restrictedDerivedRestrict jU).obj (K'⟦n⟧)) :=
        ((shiftFunctor _ n).map_isZero hK'U0).of_iso
          (((restrictedDerivedRestrict jU).commShiftIso n).app K')
      let g₁ : (restrictedDerivedRestrict jV).obj (K'⟦n⟧) ⟶ (restrictedDerivedRestrict jV).obj E :=
        ((restrictedDerivedRestrict jV).commShiftIso n).hom.app K' ≫
          (shiftFunctor _ n).map hK'V.some.hom ≫ g
      have hπ : adjV.homEquiv _ _ g₁ ≫ π = 0 :=
        eq_zero_of_isZero_obj_of_isIso_unit adjU hK'n (hker N hNV) _
      obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₂ _ hT _ hπ
      have hh0 : h = 0 := hE none n h
      refine eq_zero_of_retract_commShift _ hK'V.some.inv hK'V.some.hom (by simp) n g ?_
      change g₁ = 0
      rw [← (adjV.homEquiv _ _).symm_apply_apply g₁, hh, hh0, zero_comp,
        Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
    -- Step 2: `E ≅ Rj_{U,*}(E|_U)`
    have h2 : IsIso (adjU.unit.app E) := by
      obtain ⟨C, g₂, g₃, hT⟩ := distinguished_cocone_triangle (adjU.unit.app E)
      have hCU : IsZero ((restrictedDerivedRestrict jU).obj C) :=
        Triangle.isZero₃_of_isIso₁ _ ((restrictedDerivedRestrict jU).map_distinguished _ hT)
          (isIso_map_unit_of_isIso_counit adjU E inferInstance)
      have hE1 : ((ObjectProperty.singleton (koszulQC f)).shiftClosure ℤ).rightOrthogonal
          ((restrictedDerivedRestrict jV).obj E) := by
        rw [rightOrthogonal_shiftClosure_ofObj_iff]
        intro _ n g
        exact h1 n g
      have hE2 : ((ObjectProperty.singleton (koszulQC f)).shiftClosure ℤ).rightOrthogonal
          ((restrictedDerivedRestrict jV).obj ((Stacks.Duality.quasiCoherentDerivedPushforward jU
            (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).obj
              ((restrictedDerivedRestrict jU).obj E))) :=
        ObjectProperty.prop_of_iso _ (βVU _).symm
          (rightOrthogonal_shiftClosure_singleton_rightAdjoint_obj adjV'
            (isZero_restrictedDerivedRestrict_koszulQC f) _)
      have hC : ((ObjectProperty.singleton (koszulQC f)).shiftClosure ℤ).rightOrthogonal
          ((restrictedDerivedRestrict jV).obj C) :=
        ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
          ((restrictedDerivedRestrict jV).map_distinguished _ hT) hE1 hE2
      rw [rightOrthogonal_shiftClosure_ofObj_iff] at hC
      have hC' := (forall_hom_shift_eq_zero_iff _ _ _).1 (fun n g => hC PUnit.unit n g)
      have hCV : IsZero ((restrictedDerivedRestrict jV).obj C) := by
        refine isZero_fullSubcategory_of_isZero_obj
          (isZero_of_forall_hom_koszulObject_eq_zero f _ ((restrictedDerivedRestrict jV).obj C).2
            ?_ fun n g => ?_)
        · exact isZero_derivedRestrict_comp_of_isZero (openComplement f).ι iU jV jU hsq.w.symm
            ((DerivedCategoryB.derivedCategoryB (A := U.Modules)
              (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι.map_isZero hCU)
        · exact eq_zero_of_forall_hom_koszulQC_eq_zero f hC' n g
      have hC0 : IsZero C := isZero_fullSubcategory_of_isZero_obj
        (isZero_of_isZero_derivedRestrict₂ jU jV
          ((DerivedCategoryB.derivedCategoryB (A := U.Modules)
            (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι.map_isZero hCU)
          ((DerivedCategoryB.derivedCategoryB (A := Spec (CommRingCat.of A) |>.Modules)
            (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).ι.map_isZero
              hCV) hcov)
      exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hC0
    -- Step 3: `E|_U = 0`
    have h3 : IsZero ((restrictedDerivedRestrict jU).obj E) := by
      refine hPgen _ ?_
      rw [rightOrthogonal_shiftClosure_ofObj_iff]
      intro i n g
      have hz := eq_zero_of_isIso_unit adjU h2 (fun g' => hE (some i) n g')
      obtain ⟨e⟩ := hRU i
      exact eq_zero_of_retract_commShift _ (biprod.inl ≫ e.inv) (e.hom ≫ biprod.fst) (by simp) n g
        (hz _)
    exact ((Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).map_isZero h3).of_iso
        (asIso (adjU.unit.app E))

include hsq hcov in
/-- **The inductive step of [Stacks, Tag 09IS].** Let `Y` be a quasi-compact quasi-separated
scheme covered by a quasi-compact open `j_U : U ⟶ Y` and an affine open `j_V : Spec A ⟶ Y` whose
overlap is `D(f₁) ∪ … ∪ D(f_r) ⊆ Spec A`. If `D_QCoh(𝒪_U)` is compactly generated, so is
`D_QCoh(𝒪_Y)`.

For each compact generator `P` of `D_QCoh(𝒪_U)`, the restriction of `P ⊕ P[1]` to the overlap is
the restriction of a compact object `Q` of `D_QCoh(𝒪_{Spec A})` ([Stacks, Tag 08EK],
`Stacks.Duality.QcqsGeneration.exists_isCompactObject_restrict_iso_biprod_shift`), and `P ⊕ P[1]`
and `Q` glue to an object `R_P` of `D_QCoh(𝒪_Y)`, compact because its two restrictions are. With
`K'` glued from `0` on `U` and the Koszul complex `K` on `Spec A`, the `R_P` and `K'` generate:
an object `E` right orthogonal to them has `E|_{Spec A}` right orthogonal to `K`, so the cone of
`E ⟶ Rj_{U,*}(E|_U)` vanishes on `Spec A` by [Stacks, Tag 09IR]; then `E ≅ Rj_{U,*}(E|_U)`, and
`E|_U` is right orthogonal to every `P`, hence zero. -/
theorem isCompactlyGenerated_of_step
    (hU : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory U)) :
    IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory Y) := by
  obtain ⟨ι, P, hPc, hPgen⟩ := hU
  obtain ⟨E, hEc, hEgen⟩ := exists_compact_generators_option_of_step jU jV f iU hsq hcov P hPc hPgen
  exact ⟨Option ι, E, hEc, hEgen⟩

end Step

/-! ### The induction on the number of affine opens -/

section Induction

open Stacks.Koszul.Truncation

/-- `Stacks.Duality.QcqsGeneration.exists_compact_generators_option_of_step` with the overlap given
as an open of `Spec A` equal to `D(f₁) ∪ … ∪ D(f_r)`. -/
theorem exists_compact_generators_option_of_step' {Y : Scheme.{u}} [QuasiSeparatedSpace Y]
    [CompactSpace Y] {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y)
    [IsOpenImmersion jU] {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y)
    [IsOpenImmersion jV] {r : ℕ} (f : Fin r → A) {W : (Spec (CommRingCat.of A)).Opens}
    (hW : W = openComplement f) (iU : W.toScheme ⟶ U) [IsOpenImmersion iU]
    (hsq : IsPullback iU W.ι jU jV) (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))
    {ι : Type u} (P : ι → Stacks.Duality.quasiCoherentDerivedCategory U)
    (hPc : ∀ i, IsCompactObject.{u} (P i)) (hPgen : (ofObj P).IsWeakTriangulatedGenerator) :
    ∃ E : Option ι → Stacks.Duality.quasiCoherentDerivedCategory Y,
      (∀ o, IsCompactObject.{u} (E o)) ∧ (ofObj E).IsWeakTriangulatedGenerator := by
  subst hW
  exact exists_compact_generators_option_of_step jU jV f iU hsq hcov P hPc hPgen

/-- `Stacks.Duality.QcqsGeneration.isCompactlyGenerated_of_step` with the overlap given as an
open of `Spec A` equal to `D(f₁) ∪ … ∪ D(f_r)`. -/
theorem isCompactlyGenerated_of_step' {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
    {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
    {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
    {r : ℕ} (f : Fin r → A) {W : (Spec (CommRingCat.of A)).Opens} (hW : W = openComplement f)
    (iU : W.toScheme ⟶ U) [IsOpenImmersion iU] (hsq : IsPullback iU W.ι jU jV)
    (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))
    (hU : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory U)) :
    IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory Y) := by
  obtain ⟨ι, P, hPc, hPgen⟩ := hU
  obtain ⟨E, hEc, hEgen⟩ :=
    exists_compact_generators_option_of_step' jU jV f hW iU hsq hcov P hPc hPgen
  exact ⟨Option ι, E, hEc, hEgen⟩

/-- **The inductive step, for a cover by a quasi-compact open and an affine open, at a given
family of generators.** Let `Y` be a quasi-compact quasi-separated scheme covered by a
quasi-compact open `U` and the image of an open immersion `Spec A ⟶ Y`. A family
`P : ι → D_QCoh(𝒪_U)` of compact generators gives a family of compact generators of `D_QCoh(𝒪_Y)`
indexed by `Option ι`.

The preimage of `U` in `Spec A` is quasi-compact, `Y` being quasi-separated, hence a finite union
of basic opens `D(f₁) ∪ … ∪ D(f_r)`, and the square of open immersions it cuts out is Cartesian. -/
theorem exists_compact_generators_option_of_cover {Y : Scheme.{u}} [QuasiSeparatedSpace Y]
    [CompactSpace Y] (U : Y.Opens) (hUc : IsCompact (U : Set Y)) {A : Type u} [CommRing A]
    (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
    (hcov : ∀ y : Y, y ∈ U ∨ (∃ x, jV x = y)) {ι : Type u}
    (P : ι → Stacks.Duality.quasiCoherentDerivedCategory U.toScheme)
    (hPc : ∀ i, IsCompactObject.{u} (P i)) (hPgen : (ofObj P).IsWeakTriangulatedGenerator) :
    ∃ E : Option ι → Stacks.Duality.quasiCoherentDerivedCategory Y,
      (∀ o, IsCompactObject.{u} (E o)) ∧ (ofObj E).IsWeakTriangulatedGenerator := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
  have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  have hc := jV.isCompact_preimage hUc
  obtain ⟨s, hs⟩ := Stacks.AlgebraicGeometry.InductionPrinciple.exists_finset_basicOpen_of_isCompact
    (isAffineOpen_top (Spec (CommRingCat.of A))) hc le_top
  let e := s.equivFin
  let f : Fin s.card → A := fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (e.symm i)
  have hW : jV ⁻¹ᵁ U = openComplement f := by
    rw [hs]
    refine le_antisymm (iSup₂_le fun g hg => ?_) (iSup_le fun i => ?_)
    · refine le_trans (le_of_eq ?_) (le_iSup _ (e ⟨g, hg⟩))
      congr 1
      simp [f]
    · refine le_trans (le_of_eq ?_)
        (le_iSup₂ (f := fun g _ => (Spec (CommRingCat.of A)).basicOpen g) (e.symm i).1 (e.symm i).2)
      congr 1
      simp [f]
  refine exists_compact_generators_option_of_step' U.ι jV f hW (jV ∣_ U)
    (isPullback_morphismRestrict jV U) (fun y => ?_) P hPc hPgen
  rcases hcov y with hy | hy
  · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
  · exact Or.inr hy

/-- **The inductive step, for a cover by a quasi-compact open and an affine open.** Let `Y` be a
quasi-compact quasi-separated scheme covered by a quasi-compact open `U` and the image of an open
immersion `Spec A ⟶ Y`. If `D_QCoh(𝒪_U)` is compactly generated, so is `D_QCoh(𝒪_Y)`; this is
`Stacks.Duality.QcqsGeneration.exists_compact_generators_option_of_cover`. -/
theorem isCompactlyGenerated_of_cover {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
    (U : Y.Opens) (hUc : IsCompact (U : Set Y)) {A : Type u} [CommRing A]
    (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
    (hcov : ∀ y : Y, y ∈ U ∨ (∃ x, jV x = y))
    (hU : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory U.toScheme)) :
    IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory Y) := by
  obtain ⟨ι, P, hPc, hPgen⟩ := hU
  obtain ⟨E, hEc, hEgen⟩ := exists_compact_generators_option_of_cover U hUc jV hcov P hPc hPgen
  exact ⟨Option ι, E, hEc, hEgen⟩

/-- **A finite family of compact generators for a scheme covered by `n` affine opens**, by
induction on `n`. The base case is the affine case,
`Stacks.Duality.AffineGeneration.exists_isCompactObject_isWeakTriangulatedGenerator_of_isAffine`,
a single generator; the step is
`Stacks.Duality.QcqsGeneration.exists_compact_generators_option_of_cover`, which adds one
generator. -/
theorem exists_finite_compact_generators_of_affineCover : ∀ (n : ℕ) (Y : Scheme.{u})
    [QuasiSeparatedSpace Y] (V : Fin n → Y.Opens), (∀ i, IsAffineOpen (V i)) →
    (⨆ i, V i) = ⊤ →
    ∃ (ι : Type u) (_ : Finite ι) (E : ι → Stacks.Duality.quasiCoherentDerivedCategory Y),
      (∀ i, IsCompactObject.{u} (E i)) ∧ (ofObj E).IsWeakTriangulatedGenerator
  | 0, Y, _, V, _, hcov => by
      have : IsEmpty Y := ⟨fun y => by
        have hy : y ∈ (⊤ : Y.Opens) := trivial
        rw [← hcov] at hy
        simp at hy⟩
      have h : ∃ (ι : Type u) (_ : Finite ι) (E : ι → (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).FullSubcategory),
          (∀ i, IsCompactObject.{u} (E i)) ∧ (ofObj E).IsWeakTriangulatedGenerator := by
        obtain ⟨P, hc, hg⟩ :=
          AffineGeneration.exists_isCompactObject_isWeakTriangulatedGenerator_of_isAffine Y
        exact ⟨PUnit.{u + 1}, inferInstance, fun _ => P, fun _ => hc, by
          rw [Stacks.Duality.AffineGeneration.ofObj_const_eq_singleton (ι := PUnit.{u + 1})]
          exact hg⟩
      exact h
  | n + 1, Y, _, V, hV, hcov => by
      have hcomp : ∀ (m : ℕ) (W : Fin m → Y.Opens), (∀ i, IsAffineOpen (W i)) →
          IsCompact (((⨆ i, W i : Y.Opens)) : Set Y) := fun m W hW => by
        rw [TopologicalSpace.Opens.coe_iSup]
        exact isCompact_iUnion fun i => (hW i).isCompact
      have : CompactSpace Y := ⟨by
        have := hcomp _ V hV
        rwa [hcov, TopologicalSpace.Opens.coe_top] at this⟩
      let U : Y.Opens := ⨆ i : Fin n, V i.castSucc
      have hUc : IsCompact (U : Set Y) := hcomp _ _ fun i => hV _
      have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
      obtain ⟨ι, hι, P, hPc, hPgen⟩ := exists_finite_compact_generators_of_affineCover n
        U.toScheme (fun i => U.ι ⁻¹ᵁ V i.castSucc)
        (fun i => (hV i.castSucc).preimage_of_isOpenImmersion U.ι (by
          rw [Scheme.Opens.opensRange_ι]
          exact le_iSup (fun i : Fin n => V i.castSucc) i))
        (by
          rw [← Scheme.Hom.preimage_iSup]
          exact Scheme.Opens.ι_preimage_self U)
      have hcov' : ∀ y : Y, y ∈ U ∨ ∃ x, (hV (Fin.last n)).fromSpec x = y := by
        intro y
        have hy : y ∈ (⊤ : Y.Opens) := trivial
        rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hy
        obtain ⟨i, hi⟩ := hy
        refine Fin.lastCases
          (motive := fun i => y ∈ V i → y ∈ U ∨ ∃ x, (hV (Fin.last n)).fromSpec x = y)
          (fun h => Or.inr ?_) (fun j h => Or.inl ?_) i hi
        · have h' : y ∈ Set.range (hV (Fin.last n)).fromSpec := by
            rw [(hV (Fin.last n)).range_fromSpec]
            exact h
          obtain ⟨x, hx⟩ := h'
          exact ⟨x, hx⟩
        · exact (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, h⟩ : y ∈ U)
      obtain ⟨E, hEc, hEgen⟩ := exists_compact_generators_option_of_cover U hUc
        (A := Γ(Y, V (Fin.last n))) (hV (Fin.last n)).fromSpec hcov' P hPc hPgen
      exact ⟨Option ι, inferInstance, E, hEc, hEgen⟩

/-- **Compact generation for a scheme covered by `n` affine opens**: the finite family of
`Stacks.Duality.QcqsGeneration.exists_finite_compact_generators_of_affineCover`. -/
theorem isCompactlyGenerated_of_affineCover : ∀ (n : ℕ) (Y : Scheme.{u})
    [QuasiSeparatedSpace Y] (V : Fin n → Y.Opens), (∀ i, IsAffineOpen (V i)) →
    (⨆ i, V i) = ⊤ →
    IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory Y)
  | 0, Y, _, V, _, hcov => by
      have : IsEmpty Y := ⟨fun y => by
        have hy : y ∈ (⊤ : Y.Opens) := trivial
        rw [← hcov] at hy
        simp at hy⟩
      exact AffineGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory_of_isAffine Y
  | n + 1, Y, _, V, hV, hcov => by
      obtain ⟨ι, -, E, hEc, hEgen⟩ :=
        exists_finite_compact_generators_of_affineCover (n + 1) Y V hV hcov
      exact ⟨ι, E, hEc, hEgen⟩

end Induction

/-! ### Tag 09IS -/

/-- **A finite family of compact generators of `D_QCoh(𝒪_X)`** for a quasi-compact and
quasi-separated scheme `X`: there are finitely many compact objects of `D_QCoh(𝒪_X)` such that an
object receiving no nonzero morphism from any shift of any of them is zero. This is the form of
[Stacks, Tag 09IS] from which a single perfect generator is assembled, the direct sum of the
family; see `Stacks.SheafOfModules.exists_isPerfect_generator`.

The proof is the source's: induction over a finite affine cover,
`Stacks.Duality.QcqsGeneration.exists_finite_compact_generators_of_affineCover`. -/
theorem exists_finite_compact_generators (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (E : ι → Stacks.Duality.quasiCoherentDerivedCategory X),
      (∀ i, IsCompactObject.{u} (E i)) ∧ (ofObj E).IsWeakTriangulatedGenerator := by
  obtain ⟨s, hs, hX⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  let t := hs.toFinset
  let e := t.equivFin
  refine exists_finite_compact_generators_of_affineCover t.card X
    (fun i => ((e.symm i).1 : X.Opens)) (fun i => (e.symm i).1.2) ?_
  rw [hX]
  refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun W hW => ?_)
  · exact le_iSup₂ (f := fun (W : X.affineOpens) (_ : W ∈ s) => (W : X.Opens)) (e.symm i).1
      (hs.mem_toFinset.mp (e.symm i).2)
  · exact le_trans (le_of_eq rfl) (le_iSup (fun i => ((e.symm i).1 : X.Opens))
      (e ⟨W, hs.mem_toFinset.mpr hW⟩) |>.trans' (by simp))

/-- **[Stacks, Tag 09IS], in the compactly generated form of [Stacks, Tag 09SQ].** Let `X` be a
quasi-compact and quasi-separated scheme. Then `D_QCoh(𝒪_X)` is compactly generated: there is a
family of compact objects, indexed by a type of the universe of `X`, such that an object of
`D_QCoh(𝒪_X)` receiving no nonzero morphism from any shift of any of them is zero.

The proof is the source's: induction over a finite affine cover, the inductive step being
`Stacks.Duality.QcqsGeneration.isCompactlyGenerated_of_step`; the family is the finite one of
`Stacks.Duality.QcqsGeneration.exists_finite_compact_generators`. -/
theorem isCompactlyGenerated_quasiCoherentDerivedCategory (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory X) := by
  obtain ⟨ι, -, E, hEc, hEgen⟩ := exists_finite_compact_generators X
  exact ⟨ι, E, hEc, hEgen⟩

end Stacks.Duality.QcqsGeneration

/-! ### Tag 0A9E -/

namespace Stacks.Duality.DerivedPushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **Stacks Project, Tag 0A9E.** Let `f : X ⟶ Y` be a morphism between quasi-compact and
quasi-separated schemes. The functor `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint.

The proof is the source's: Brown representability ([Stacks, Tag 0A8G]) applies because
`D_QCoh(𝒪_X)` has direct sums ([Stacks, Tag 08DT]) and is compactly generated
([Stacks, Tag 09IS],
`Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory`), and because
`f`, a morphism between quasi-compact quasi-separated schemes, is quasi-compact and
quasi-separated, so that `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)` ([Stacks, Tag 08D5])
and commutes with direct sums ([Stacks, Tag 08DZ]); those two facts about `f` are found by
instance search (`AlgebraicGeometry.quasiCompact_of_compactSpace`,
`AlgebraicGeometry.QuasiSeparated.of_quasiSeparatedSpace`).

The derived categories are the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whose morphisms live in the universe `u`
of the schemes. This is the only model at which the statement has content: Brown representability
asks for direct sums indexed by the morphism universe, and at
`CategoryTheory.HasDerivedCategory.standard`, whose morphisms live in `Type (u + 1)`, those direct
sums do not exist in the category of `𝒪_X`-modules. The functor is the canonical
`Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward`. -/
@[stacks 0A9E]
theorem isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs :
    (qcqsRestrictedDerivedPushforward f).IsLeftAdjoint :=
  isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isCompactlyGenerated f
    (Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory X)

/-- Tag 0A9E as an instance: for a morphism between quasi-compact quasi-separated schemes, the
restriction of `Rf_*` to `D_QCoh` has a right adjoint, whichever proof of
[Stacks, Tag 08D5] is used to restrict it, so that `Stacks.Duality.twistedInverseImage f hpush`
is available with no adjointness argument. -/
instance isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs
    (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent) :
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint :=
  isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs f

/-- **Stacks Project, Tag 0A9E, with the adjoint exhibited as exact.** For a morphism
`f : X ⟶ Y` between quasi-compact and quasi-separated schemes there is a functor
`a : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`, an adjunction `Rf_* ⊣ a`, and a shift structure on `a` for which
the adjunction is triangulated: Brown representability returns the right adjoint as an exact
functor. -/
@[stacks 0A9E "the adjoint is exact"]
theorem exists_isTriangulated_rightAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs :
    ∃ (a : _) (adj : qcqsRestrictedDerivedPushforward f ⊣ a) (_ : a.CommShift ℤ),
      adj.IsTriangulated :=
  exists_isTriangulated_rightAdjoint_qcqsRestrictedDerivedPushforward_of_isCompactlyGenerated f
    (Stacks.Duality.QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory X)

end Stacks.Duality.DerivedPushforward
