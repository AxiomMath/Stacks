module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsCompactIsPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.QcqsPerfectIsCompact
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import Mathlib.CategoryTheory.Retract
public import StacksCore.Tactic.StacksAttribute

/-!
# A perfect object on a quasi-compact open is a summand of a restriction (qcqs case)

Let `X` be a quasi-compact quasi-separated scheme and `U ⊆ X` a quasi-compact open. Every perfect
object `P` of `D(𝒪_U)` is a direct summand of the restriction to `U` of a perfect object of
`D(𝒪_X)`. This is [Stacks, Tag 09IQ].

## The proof

The source deduces 09IQ from [Stacks, Tag 09IM], whose proof is an induction on the number of
affine opens `V₁, …, V_m` needed to cover `X ∖ U`: with `X_k = U ∪ V₁ ∪ … ∪ V_k`, a perfect object
on `X_k` is a summand of the restriction of one on `X_{k+1}`. The step, for `Y = W ∪ V` with `V`
affine and `W ∩ V = D(f₁) ∪ … ∪ D(f_r) ⊆ V`, lifts `P|_{W ∩ V}`, after adding `P|_{W ∩ V}[1]`, to
`V` ([Stacks, Tag 08EK]) and glues ([Stacks, Tag 08DG]); the glued object restricts to `P ⊕ P[1]`
on `W`.

Here the induction runs in `D_QCoh` at the locally small derived category, with *compact* objects
in place of perfect ones, because that is where both inputs of the step already exist: the
compact form of 08EK is
`Stacks.Duality.QcqsGeneration.exists_isCompactObject_restrict_iso_biprod_shift`, glueing is
`CategoryTheory.Pretriangulated.exists_glue`, and a glued object is compact because its two
restrictions are (`CategoryTheory.Pretriangulated.isCompactObject_of_isCompactObject_restrict`).
[Stacks, Tag 09M1] on the quasi-compact quasi-separated schemes `U` and `X`
(`Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect` and
`Stacks.Duality.QcqsPerfect.isPerfect_of_isCompactObject_of_qcqs`) translates back to perfect
objects, and
`StacksDraft.DerivedModel.modelEquiv` moves the result to an arbitrary model of `D(𝒪_U)`.

## Main results

* `Stacks.DerivedQCoh.OpenLift.exists_isCompactObject_retract_restrict`: the compact form, in
  `D_QCoh`.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfectComplex_retract_of_isPerfect_of_qcqs`:
  **[Stacks, Tag 09IQ]**, with the perfect object on `X` exhibited by a perfect complex and the
  derived category of `𝒪_U` arbitrary.
* `Stacks.DerivedQCoh.OpenLift.exists_isPerfect_retract_derivedRestrict`: the same with the
  perfect object on `X` an object of an arbitrary model of `D(𝒪_X)`.

## Implementation notes

"Direct summand" is `CategoryTheory.Retract`, as in the affine case
`Stacks.DerivedQCoh.OpenLift.exists_isPerfectComplex_retract_restrict_of_isPerfect`. The proof
gives more, namely that the complement is a sum of positive shifts of `P` ([Stacks, Tag 09IN]),
but the tag asserts nothing about it.

## References

* [Stacks Project, Tag 09IQ](https://stacks.math.columbia.edu/tag/09IQ)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
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
open Stacks.Duality.OpenImmersion Stacks.Duality.QcqsGeneration

universe d₁ d₂ u

namespace Stacks.DerivedQCoh.OpenLift

/-! ### Restriction along composites and identities, on `D_QCoh` -/

section Restriction

/-- Restricting along `b` and then along `a` is restricting along `a ≫ b`, on the quasi-coherent
derived categories. -/
def restrictedDerivedRestrictCompObjIso {W V Y : Scheme.{u}} (a : W ⟶ V) (b : V ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b] (K : Stacks.Duality.quasiCoherentDerivedCategory Y) :
    (restrictedDerivedRestrict a).obj ((restrictedDerivedRestrict b).obj K) ≅
      (restrictedDerivedRestrict (a ≫ b)).obj K :=
  (DerivedCategoryB.derivedCategoryB (A := W.Modules)
    (SheafOfModules.isQuasicoherent W.ringCatSheaf)).fullyFaithfulι.preimageIso
    ((restrictedDerivedRestrictCompιIso a).app _ ≪≫
      (derivedRestrict a).mapIso ((restrictedDerivedRestrictCompιIso b).app K) ≪≫
      (Stacks.Duality.QcqsPerfect.derivedRestrictCompIso a b).app K.obj ≪≫
      ((restrictedDerivedRestrictCompιIso (a ≫ b)).app K).symm)

/-- Restriction along the identity is the identity, on the quasi-coherent derived categories. -/
def restrictedDerivedRestrictIdObjIso {Y : Scheme.{u}}
    (K : Stacks.Duality.quasiCoherentDerivedCategory Y) :
    (restrictedDerivedRestrict (𝟙 Y)).obj K ≅ K :=
  (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).fullyFaithfulι.preimageIso
    ((restrictedDerivedRestrictCompιIso (𝟙 Y)).app K ≪≫
      (Stacks.DerivedQCoh.mapDerivedCategoryCongr _ _ Scheme.Modules.restrictFunctorId).app K.obj ≪≫
      Stacks.Homology.mapDerivedCategoryIdIso.app K.obj)

/-- Restriction along equal open immersions, on the quasi-coherent derived categories. -/
def restrictedDerivedRestrictCongrObjIso {V Y : Scheme.{u}} {a b : V ⟶ Y} [IsOpenImmersion a]
    [IsOpenImmersion b] (h : a = b) (K : Stacks.Duality.quasiCoherentDerivedCategory Y) :
    (restrictedDerivedRestrict a).obj K ≅ (restrictedDerivedRestrict b).obj K := by
  subst h
  exact Iso.refl _

end Restriction

/-! ### Extending compact objects along an open immersion, up to a summand -/

section Extension

/-- An open immersion `j : U ⟶ Y` *extends compact objects up to summands* when every compact
object of `D_QCoh(𝒪_U)` is a retract of the restriction of a compact object of `D_QCoh(𝒪_Y)`. -/
def ExtendsCompactUpToSummand {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] : Prop :=
  ∀ P : Stacks.Duality.quasiCoherentDerivedCategory U, IsCompactObject.{u} P →
    ∃ R : Stacks.Duality.quasiCoherentDerivedCategory Y, IsCompactObject.{u} R ∧
      Nonempty (Retract P ((restrictedDerivedRestrict j).obj R))

/-- Extension up to summands only depends on the open immersion. -/
theorem ExtendsCompactUpToSummand.of_eq {U Y : Scheme.{u}} {j j' : U ⟶ Y} [IsOpenImmersion j]
    [IsOpenImmersion j'] (h : j = j') (hj : ExtendsCompactUpToSummand j) :
    ExtendsCompactUpToSummand j' := by
  subst h
  exact hj

/-- Extension up to summands composes. -/
theorem ExtendsCompactUpToSummand.comp {W V Y : Scheme.{u}} {a : W ⟶ V} {b : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion b] (ha : ExtendsCompactUpToSummand a)
    (hb : ExtendsCompactUpToSummand b) : ExtendsCompactUpToSummand (a ≫ b) := by
  intro P hP
  obtain ⟨R₁, hR₁, ⟨r₁⟩⟩ := ha P hP
  obtain ⟨R₂, hR₂, ⟨r₂⟩⟩ := hb R₁ hR₁
  exact ⟨R₂, hR₂, ⟨r₁.trans ((r₂.map (restrictedDerivedRestrict a)).trans
    (Retract.ofIso (restrictedDerivedRestrictCompObjIso a b R₂)))⟩⟩

/-- The pushforward `Rj_*` on quasi-coherent derived categories is additive and preserves
direct sums indexed by `Type u`. -/
private theorem additive_and_preservesColimits_pushforward {U Y : Scheme.{u}} [CompactSpace Y]
    (j : U ⟶ Y) [IsOpenImmersion j] [AlgebraicGeometry.QuasiCompact j] :
    (Stacks.Duality.quasiCoherentDerivedPushforward j
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)).Additive ∧
    ∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward j
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)) :=
  ⟨(restrictedDerivedRestrictAdjunction j).right_adjoint_additive,
    preservesColimitsOfShape_discrete_restrictedDerivedPushforward j⟩

/-- An isomorphism out of a quasi-compact scheme extends compact objects: restrict along its
inverse. -/
theorem extendsCompactUpToSummand_of_iso {U Y : Scheme.{u}} [CompactSpace U] (e : U ≅ Y) :
    ExtendsCompactUpToSummand e.hom := by
  intro P hP
  obtain ⟨_, _⟩ := additive_and_preservesColimits_pushforward e.inv
  refine ⟨(restrictedDerivedRestrict e.inv).obj P,
    isCompactObject_map_of_adjunction (restrictedDerivedRestrictAdjunction e.inv) hP,
    ⟨Retract.ofIso ?_⟩⟩
  exact (restrictedDerivedRestrictIdObjIso P).symm ≪≫
    restrictedDerivedRestrictCongrObjIso e.hom_inv_id.symm P ≪≫
    (restrictedDerivedRestrictCompObjIso e.hom e.inv P).symm

end Extension

/-! ### The inductive step -/

section Step

open Stacks.Koszul.Truncation

variable {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
  {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
  {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
  {r : ℕ} (f : Fin r → A) (iU : (openComplement f).toScheme ⟶ U) [IsOpenImmersion iU]
  (hsq : IsPullback iU (openComplement f).ι jU jV)
  (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))

include hsq hcov in
/-- **The inductive step of [Stacks, Tag 09IM], for compact objects.** Let `Y` be a quasi-compact
quasi-separated scheme covered by a quasi-compact open `j_U : U ⟶ Y` and an affine open
`j_V : Spec A ⟶ Y` whose overlap is `D(f₁) ∪ … ∪ D(f_r) ⊆ Spec A`. Every compact object `P` of
`D_QCoh(𝒪_U)` has `P ⊕ P[1]` equal to the restriction of a compact object of `D_QCoh(𝒪_Y)`.

`(P ⊕ P[1])|_{D(f₁) ∪ … ∪ D(f_r)}` is the restriction of a compact object `Q` on `Spec A`
([Stacks, Tag 08EK] for compact objects), and `P ⊕ P[1]` and `Q` glue ([Stacks, Tag 08DG]) to an
object compact because both of its restrictions are. -/
theorem exists_isCompactObject_restrict_iso_biprod_shift_of_step
    (P : Stacks.Duality.quasiCoherentDerivedCategory U) (hP : IsCompactObject.{u} P) :
    ∃ R : Stacks.Duality.quasiCoherentDerivedCategory Y, IsCompactObject.{u} R ∧
      Nonempty ((restrictedDerivedRestrict jU).obj R ≅ P ⊞ P⟦(1 : ℤ)⟧) := by
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
  obtain ⟨_, _⟩ := additive_and_preservesColimits_pushforward jU
  obtain ⟨_, _⟩ := additive_and_preservesColimits_pushforward jV
  obtain ⟨_, _⟩ := additive_and_preservesColimits_pushforward iU
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
  have hPW : IsCompactObject.{u} ((restrictedDerivedRestrict iU).obj P) :=
    isCompactObject_map_of_adjunction adjU' hP
  obtain ⟨Q, hQc, ⟨eQ⟩⟩ := exists_isCompactObject_restrict_iso_biprod_shift f
    ((restrictedDerivedRestrict iU).obj P) hPW
  let φ : (restrictedDerivedRestrict iU).obj (P ⊞ P⟦(1 : ℤ)⟧) ≅
      (restrictedDerivedRestrict (openComplement f).ι).obj Q :=
    (restrictedDerivedRestrict iU).mapBiprod _ _ ≪≫
      biprod.mapIso (Iso.refl _) (((restrictedDerivedRestrict iU).commShiftIso (1 : ℤ)).app _) ≪≫
      eQ.symm
  obtain ⟨R, ⟨eU⟩, ⟨eV⟩⟩ := exists_glue adjU adjV adjV' βVU βUV (P ⊞ P⟦(1 : ℤ)⟧) Q φ
  exact ⟨R, isCompactObject_of_isCompactObject_restrict adjU adjV hker R
    (isCompactObject_of_iso eU (isCompactObject_biprod hP (isCompactObject_shift hP 1)))
    (isCompactObject_of_iso eV hQc), ⟨eU⟩⟩

include hsq hcov in
/-- The inductive step in the form of `ExtendsCompactUpToSummand`: `P` is a retract of
`P ⊕ P[1]`. -/
theorem extendsCompactUpToSummand_of_step : ExtendsCompactUpToSummand jU := by
  intro P hP
  obtain ⟨R, hR, ⟨e⟩⟩ :=
    exists_isCompactObject_restrict_iso_biprod_shift_of_step jU jV f iU hsq hcov P hP
  exact ⟨R, hR, ⟨(⟨biprod.inl, biprod.fst, biprod.inl_fst⟩ : Retract P (P ⊞ P⟦(1 : ℤ)⟧)).trans
    (Retract.ofIso e.symm)⟩⟩

end Step

/-! ### The induction on the number of affine opens -/

section Induction

open Stacks.Koszul.Truncation

/-- `Stacks.DerivedQCoh.OpenLift.extendsCompactUpToSummand_of_step` with the overlap given as an
open of `Spec A` equal to `D(f₁) ∪ … ∪ D(f_r)`. -/
theorem extendsCompactUpToSummand_of_step' {Y : Scheme.{u}} [QuasiSeparatedSpace Y]
    [CompactSpace Y] {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y)
    [IsOpenImmersion jU] {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y)
    [IsOpenImmersion jV] {r : ℕ} (f : Fin r → A) {W : (Spec (CommRingCat.of A)).Opens}
    (hW : W = openComplement f) (iU : W.toScheme ⟶ U) [IsOpenImmersion iU]
    (hsq : IsPullback iU W.ι jU jV) (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y)) :
    ExtendsCompactUpToSummand jU := by
  subst hW
  exact extendsCompactUpToSummand_of_step jU jV f iU hsq hcov

/-- **The inductive step, for a cover by a quasi-compact open and an affine open.** Let `Y` be a
quasi-compact quasi-separated scheme covered by a quasi-compact open `U` and the image of an open
immersion `Spec A ⟶ Y`. Then `U ⊆ Y` extends compact objects up to summands.

The preimage of `U` in `Spec A` is quasi-compact, `Y` being quasi-separated, hence a finite union
of basic opens `D(f₁) ∪ … ∪ D(f_r)`, and the square of open immersions it cuts out is Cartesian. -/
theorem extendsCompactUpToSummand_of_cover {Y : Scheme.{u}} [QuasiSeparatedSpace Y]
    [CompactSpace Y] (U : Y.Opens) (hUc : IsCompact (U : Set Y)) {A : Type u} [CommRing A]
    (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
    (hcov : ∀ y : Y, y ∈ U ∨ (∃ x, jV x = y)) : ExtendsCompactUpToSummand U.ι := by
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
  refine extendsCompactUpToSummand_of_step' U.ι jV f hW (jV ∣_ U)
    (isPullback_morphismRestrict jV U) (fun y => ?_)
  rcases hcov y with hy | hy
  · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
  · exact Or.inr hy

/-- **Extension up to summands along an open immersion whose image and `n` affine opens cover the
target**, by induction on `n`: the image of `j_U` together with the first `n - 1` affines is a
quasi-compact open `Y'`, the corestriction `U ⟶ Y'` extends by induction, and `Y' ⊆ Y` extends by
`Stacks.DerivedQCoh.OpenLift.extendsCompactUpToSummand_of_cover`. -/
theorem extendsCompactUpToSummand_of_affineCover : ∀ (n : ℕ) (Y : Scheme.{u})
    [QuasiSeparatedSpace Y] {U : Scheme.{u}} [CompactSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
    (V : Fin n → Y.Opens), (∀ i, IsAffineOpen (V i)) → jU.opensRange ⊔ (⨆ i, V i) = ⊤ →
    ExtendsCompactUpToSummand jU
  | 0, Y, _, U, _, jU, _, V, _, hcov => by
      have htop : jU.opensRange = ⊤ := by simpa using hcov
      have : IsIso jU := by
        rw [isIso_iff_isOpenImmersion_and_surjective]
        refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
        have hy : y ∈ jU.opensRange := by rw [htop]; trivial
        exact hy
      exact (extendsCompactUpToSummand_of_iso (asIso jU)).of_eq (asIso_hom jU)
  | n + 1, Y, _, U, _, jU, _, V, hV, hcov => by
      let Y' : Y.Opens := jU.opensRange ⊔ ⨆ i : Fin n, V i.castSucc
      have hcpt : ∀ {m : ℕ} (W : Fin m → Y.Opens), (∀ i, IsAffineOpen (W i)) →
          IsCompact ((jU.opensRange ⊔ ⨆ i, W i : Y.Opens) : Set Y) := fun W hW => by
        refine IsCompact.union (isCompact_range jU.continuous) ?_
        rw [TopologicalSpace.Opens.coe_iSup]
        exact isCompact_iUnion fun i => (hW i).isCompact
      have hY'c : IsCompact (Y' : Set Y) := hcpt _ fun i => hV _
      have hYc : IsCompact (Set.univ : Set Y) := by
        simpa [hcov] using hcpt V hV
      have : CompactSpace Y := ⟨hYc⟩
      have : QuasiSeparatedSpace Y'.toScheme := Y'.ι.isOpenEmbedding.quasiSeparatedSpace
      have hle : jU.opensRange ≤ Y' := le_sup_left
      let jU' : U ⟶ Y'.toScheme := jU.isoOpensRange.hom ≫ Y.homOfLE hle
      have hfac : jU' ≫ Y'.ι = jU := by simp [jU']
      have hIH := extendsCompactUpToSummand_of_affineCover n Y'.toScheme jU'
        (fun i => Y'.ι ⁻¹ᵁ V i.castSucc)
        (fun i => (hV i.castSucc).preimage_of_isOpenImmersion Y'.ι (by
          rw [Scheme.Opens.opensRange_ι]
          exact le_sup_of_le_right (le_iSup (fun i : Fin n => V i.castSucc) i)))
        (by
          have h1 : jU'.opensRange = Y'.ι ⁻¹ᵁ jU.opensRange := by
            simp only [jU', Scheme.Hom.opensRange_comp_of_isIso, Scheme.opensRange_homOfLE]
          rw [h1, ← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_sup]
          exact Scheme.Opens.ι_preimage_self Y')
      have hstep : ExtendsCompactUpToSummand Y'.ι := by
        refine extendsCompactUpToSummand_of_cover Y' hY'c (A := Γ(Y, V (Fin.last n)))
          (hV (Fin.last n)).fromSpec (fun y => ?_)
        have hy : y ∈ (⊤ : Y.Opens) := trivial
        rw [← hcov] at hy
        rcases hy with hy | hy
        · exact Or.inl (Or.inl hy)
        · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
          refine Fin.lastCases
            (motive := fun i => y ∈ V i → y ∈ Y' ∨ ∃ x, (hV (Fin.last n)).fromSpec x = y)
            (fun h => Or.inr ?_) (fun j h => Or.inl ?_) i hi
          · have h' : y ∈ Set.range (hV (Fin.last n)).fromSpec := by
              rw [(hV (Fin.last n)).range_fromSpec]
              exact h
            obtain ⟨x, hx⟩ := h'
            exact ⟨x, hx⟩
          · exact Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, h⟩)
      exact (hIH.comp hstep).of_eq hfac

/-- **Compact objects extend from a quasi-compact open up to summands**, on a quasi-compact
quasi-separated scheme: the compact form of [Stacks, Tag 09IQ]. Let `X` be quasi-compact and
quasi-separated and `U ⊆ X` a quasi-compact open. Every compact object `P` of `D_QCoh(𝒪_U)` is a
retract of the restriction of a compact object of `D_QCoh(𝒪_X)`. -/
theorem exists_isCompactObject_retract_restrict (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (P : Stacks.Duality.quasiCoherentDerivedCategory U.toScheme) (hP : IsCompactObject.{u} P) :
    ∃ R : Stacks.Duality.quasiCoherentDerivedCategory X, IsCompactObject.{u} R ∧
      Nonempty (Retract P ((restrictedDerivedRestrict U.ι).obj R)) := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  obtain ⟨s, hs, hX⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  let t := hs.toFinset
  let e := t.equivFin
  refine extendsCompactUpToSummand_of_affineCover t.card X U.ι (fun i => ((e.symm i).1 : X.Opens))
    (fun i => (e.symm i).1.2) (top_le_iff.mp (le_sup_of_le_right (le_of_eq ?_))) P hP
  rw [hX]
  refine le_antisymm (iSup₂_le fun W hW => ?_) (iSup_le fun i => ?_)
  · exact le_trans (le_of_eq rfl) (le_iSup (fun i => ((e.symm i).1 : X.Opens))
      (e ⟨W, hs.mem_toFinset.mpr hW⟩) |>.trans' (by simp))
  · exact le_iSup₂ (f := fun (W : X.affineOpens) (_ : W ∈ s) => (W : X.Opens)) (e.symm i).1
      (hs.mem_toFinset.mp (e.symm i).2)

end Induction

/-! ### Tag 09IQ -/

section Tag

open Stacks.Cohomology.PerfectComplexes

/-- **A retract between classes of complexes does not depend on the chosen derived category**:
conjugate by `StacksDraft.DerivedModel.modelCompQIso`, which identifies the two localization
functors through the comparison equivalence. -/
def retractOfModel {C : Type*} [Category C] [Abelian C] (h₁ : HasDerivedCategory.{d₁} C)
    (h₂ : HasDerivedCategory.{d₂} C) {E F : CochainComplex C ℤ}
    (ρ : Retract ((@DerivedCategory.Q C _ _ h₁).obj E) ((@DerivedCategory.Q C _ _ h₁).obj F)) :
    Retract ((@DerivedCategory.Q C _ _ h₂).obj E) ((@DerivedCategory.Q C _ _ h₂).obj F) :=
  (Retract.ofIso ((StacksDraft.DerivedModel.modelCompQIso h₁ h₂).app E).symm).trans
    ((ρ.map (StacksDraft.DerivedModel.modelEquiv h₁ h₂).functor).trans
      (Retract.ofIso ((StacksDraft.DerivedModel.modelCompQIso h₁ h₂).app F)))

/-- [Stacks, Tag 09IQ] at the locally small derived category of `𝒪_U`: the compact form
`Stacks.DerivedQCoh.OpenLift.exists_isCompactObject_retract_restrict`, read through
[Stacks, Tag 09M1] on `U` and on `X`. -/
private theorem exists_isPerfectComplex_retract_locallySmall (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X))
    (P : DerivedCategory U.toScheme.Modules)
    (hP : @IsPerfect U.toScheme.toRingedSpace (Scheme.Modules.hasDerivedCategory U.toScheme) P) :
    ∃ M : CochainComplex X.Modules ℤ, IsPerfectComplex (X := X.toRingedSpace) M ∧
      Nonempty (Retract P (DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          M))) := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  let P' : Stacks.Duality.quasiCoherentDerivedCategory U.toScheme :=
    ⟨P, isQuasicoherentDerived_of_isPseudoCoherent U.toScheme P
      (RingedSpace.IsPerfect.isPseudoCoherent hP)⟩
  obtain ⟨R, hR, ⟨ρ⟩⟩ := exists_isCompactObject_retract_restrict X U hU P'
    (Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect U.toScheme P' hP)
  obtain ⟨M, hM, ⟨eR⟩⟩ : ∃ M : CochainComplex X.Modules ℤ,
      IsPerfectComplex (X := X.toRingedSpace) M ∧
        Nonempty ((@DerivedCategory.Q X.Modules _ _ (Scheme.Modules.hasDerivedCategory X)).obj M ≅
          R.obj) :=
    Stacks.Duality.QcqsPerfect.isPerfect_of_isCompactObject_of_qcqs X R hR
  exact ⟨M, hM, ⟨(ρ.map (DerivedCategoryB.derivedCategoryB (A := U.toScheme.Modules)
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf)).ι).trans
      (Retract.ofIso ((restrictedDerivedRestrictCompιIso U.ι).app R ≪≫
        (derivedRestrict U.ι).mapIso eR.symm ≪≫
        (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryFactors.app M))⟩⟩

/-- **[Stacks, Tag 09IQ].** Let `X` be a quasi-compact and quasi-separated scheme and `U ⊆ X` a
quasi-compact open. Every perfect object `P` of `D(𝒪_U)` is a direct summand -- a retract -- of
the restriction to `U` of a perfect object of `D(𝒪_X)`, here exhibited by a perfect complex `M` of
`𝒪_X`-modules: `P` is a retract of the class of `M|_U`.

The derived category of `𝒪_U` is an arbitrary model, and none is needed on `X`. -/
@[stacks 09IQ "the perfect object on X exhibited by a perfect complex; any model of D(O_U)"]
theorem exists_isPerfectComplex_retract_of_isPerfect_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [hd : HasDerivedCategory.{d₁} U.toScheme.Modules] (P : DerivedCategory U.toScheme.Modules)
    (hP : @IsPerfect U.toScheme.toRingedSpace hd P) :
    ∃ M : CochainComplex X.Modules ℤ, IsPerfectComplex (X := X.toRingedSpace) M ∧
      Nonempty (Retract P (DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          M))) := by
  let hs : HasDerivedCategory.{u} U.toScheme.Modules :=
    Scheme.Modules.hasDerivedCategory U.toScheme
  let Q₁ := @DerivedCategory.Q U.toScheme.Modules _ _ hd
  let Qs := @DerivedCategory.Q U.toScheme.Modules _ _ hs
  let E := Q₁.objPreimage P
  let eP : Q₁.obj E ≅ P := Q₁.objObjPreimageIso P
  have hP' : @IsPerfect U.toScheme.toRingedSpace hs (Qs.obj E) :=
    (isPerfect_iff_of_model hd hs eP (Iso.refl (Qs.obj E))).1 hP
  obtain ⟨M, hM, ⟨ρ⟩⟩ := exists_isPerfectComplex_retract_locallySmall X U hU _ hP'
  exact ⟨M, hM, ⟨(Retract.ofIso eP.symm).trans (retractOfModel hs hd ρ)⟩⟩

/-- **[Stacks, Tag 09IQ], in `D(𝒪_X)`.** Let `X` be a quasi-compact and quasi-separated scheme
and `U ⊆ X` a quasi-compact open. Every perfect object `P` of `D(𝒪_U)` is a retract of the
restriction to `U` of a perfect object `R` of `D(𝒪_X)`, at any models of the two derived
categories, in independent universes; restriction is `j^*` for the open immersion `j : U ⟶ X`,
which `Stacks.Duality.OpenImmersion.derivedRestrict` names when the two universes agree. -/
@[stacks 09IQ "in D(O_X), at any models of the two derived categories"]
theorem exists_isPerfect_retract_derivedRestrict (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [hU' : HasDerivedCategory.{d₁} U.toScheme.Modules] [hX : HasDerivedCategory.{d₂} X.Modules]
    (P : DerivedCategory U.toScheme.Modules) (hP : @IsPerfect U.toScheme.toRingedSpace hU' P) :
    ∃ R : DerivedCategory X.Modules, @IsPerfect X.toRingedSpace hX R ∧
      Nonempty (Retract P ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj R)) := by
  obtain ⟨M, hM, ⟨ρ⟩⟩ := exists_isPerfectComplex_retract_of_isPerfect_of_qcqs X U hU P hP
  let QX := @DerivedCategory.Q X.Modules _ _ hX
  exact ⟨QX.obj M, ⟨M, hM, ⟨Iso.refl (QX.obj M)⟩⟩, ⟨ρ.trans (Retract.ofIso
    ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryFactors.app M).symm)⟩⟩

end Tag

end Stacks.DerivedQCoh.OpenLift

end
