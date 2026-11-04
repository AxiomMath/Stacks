module

public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexes
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.CategoryTheory.Monoidal.DualConjugatePseudofunctor
public import StacksFrontier.AlgebraicGeometry.Duality.GlueingDualizingComplexesStandardModel

/-!
# `f_new^!` is a pseudofunctor

Let `ω_X^•` be a chosen complex on each of the schemes considered, `D_X = R𝓗om(-, ω_X^•)` and
`f_new^! = D_X ∘ Lf^* ∘ D_Y` (`Stacks.Duality.fNewShriekStd`). For a factorisation `f ≫ g = k`,
[Stacks, Tag 0AUE] compares `k_new^! = D_X ∘ Lk^* ∘ D_Z` with
`f_new^! ∘ g_new^! = D_X ∘ Lf^* ∘ D_Y ∘ D_Y ∘ Lg^* ∘ D_Z` through the biduality
`η_Y : id ⟶ D_Y ∘ D_Y` of [Stacks, Tag 0A89] and the composition isomorphism
`Lf^* ∘ Lg^* ≅ Lk^*` of [Stacks, Tag 0D5S]. This file gives the comparison
`f_new^! ∘ g_new^! ⟶ k_new^!` (`fNewShriekCompHom`) and the unit comparison
`id ⟶ (id_X)_new^!` (`fNewShriekUnitHom`), and proves the associativity and the two unit laws of a
pseudofunctor, at every object; part (1) of [Stacks, Tag 0AUE].

## Implementation notes

The coherence laws are the abstract statements `dualConjComp_assoc`,
`dualConjUnit_comp_dualConjComp` and `map_dualConjUnit_comp_dualConjComp` about conjugates by
dualities, applied to the associativity and unit laws of the composition isomorphisms of `L(-)^*`.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std pull stdMonoidal stdSymmetric stdMonoidalClosed
  plusCoh qcoh sheafHom bidual)
open Stacks.DerivedPullback (schemeFactorIso)
open CategoryTheory.MonoidalClosed (dualInto)

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

variable {X Y Z T : Scheme.{u}}

/-- `f_new^!` is the conjugate of `Lf^*` by `D_X` and `D_Y`. -/
theorem fNewShriek_eq_dualConj (f : X ⟶ Y) (ωX : Std X) (ωY : Std Y) :
    fNewShriekStd f ωX ωY = dualConj (dualInto ωX) (dualInto ωY) (pull f) :=
  rfl

/-- The biduality `η : id ⟶ D ∘ D` for `D = R𝓗om(-, ω)`. -/
abbrev bidualityNat (ω : Std X) : 𝟭 (Std X) ⟶ (dualInto ω).rightOp ⋙ dualInto ω :=
  MonoidalClosed.closedBiduality ω

/-- The triangle identity for the biduality: `η_{D(M)} ≫ D(η_M) = 𝟙_{D(M)}`. -/
theorem bidualityNat_triangle (ω M : Std X) :
    (bidualityNat ω).app ((dualInto ω).obj (op M)) ≫
      (dualInto ω).map ((bidualityNat ω).app M).op = 𝟙 ((dualInto ω).obj (op M)) :=
  MonoidalClosed.closedBiduality_triangle ω M

/-- `L(𝟙_X)^* ≅ id` at the standard model. -/
def pullIdIso (X : Scheme.{u}) : pull (𝟙 X) ≅ 𝟭 (Std X) :=
  Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso X.toRingedSpace

/-- The composition isomorphism `Lg^* ⋙ Lf^* ≅ Lk^*` of [Stacks, Tag 0D5S] attached to a
factorisation `f ≫ g = k`, at the standard model. -/
def pullFactorIso (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (e : f ≫ g = k) :
    pull g ⋙ pull f ≅ pull k :=
  schemeFactorIso f g k e

/-- The composition isomorphisms `Lg^* ⋙ Lf^* ≅ Lk^*` of [Stacks, Tag 0D5S] attached to the
factorisations of `f ≫ g ≫ h` satisfy the cocycle identity. -/
theorem pullFactorIso_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) {k₁ : X ⟶ Z} {k₂ : Y ⟶ T}
    {k : X ⟶ T} (e₁ : f ≫ g = k₁) (e₂ : g ≫ h = k₂) (e₃ : k₁ ≫ h = k) (e₄ : f ≫ k₂ = k)
    (N : Std T) :
    (pull f).map ((pullFactorIso g h k₂ e₂).hom.app N) ≫ (pullFactorIso f k₂ k e₄).hom.app N =
      (pullFactorIso f g k₁ e₁).hom.app ((pull h).obj N) ≫
        (pullFactorIso k₁ h k e₃).hom.app N := by
  have c {A B : Scheme.{u}} {m m' : A ⟶ B} (h : m = m') :
      m.toLRSHom.toShHom = m'.toLRSHom.toShHom := congrArg (·.toLRSHom.toShHom) h
  exact (congrArg Iso.hom (Stacks.DerivedPullback.factorIso_assoc f.toLRSHom.toShHom
    g.toLRSHom.toShHom h.toLRSHom.toShHom k₂.toLRSHom.toShHom k₁.toLRSHom.toShHom
    k.toLRSHom.toShHom (c e₂) (c e₁) (c e₃) (c e₄) N)).symm

/-- For the factorisation `𝟙_Y ≫ g = g`, the composition isomorphism `Lg^* ⋙ L(𝟙_Y)^* ≅ Lg^*`
is `L(𝟙_Y)^* ≅ id` applied at `Lg^* N`. -/
theorem pullFactorIso_id_comp (g : Y ⟶ Z) (w : 𝟙 Y ≫ g = g) (N : Std Z) :
    (pullFactorIso (𝟙 Y) g g w).hom.app N = (pullIdIso Y).hom.app ((pull g).obj N) :=
  (congrArg (fun e => e.hom.app N)
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_id_comp
      g.toLRSHom.toShHom)).trans (Category.comp_id _)

/-- For the factorisation `f ≫ 𝟙_Y = f`, the composition isomorphism `L(𝟙_Y)^* ⋙ Lf^* ≅ Lf^*`
is `Lf^*` of `L(𝟙_Y)^* ≅ id`. -/
theorem pullFactorIso_comp_id (f : X ⟶ Y) (w : f ≫ 𝟙 Y = f) (N : Std Y) :
    (pullFactorIso f (𝟙 Y) f w).hom.app N = (pull f).map ((pullIdIso Y).hom.app N) :=
  (congrArg (fun e => e.hom.app N)
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_comp_id
      f.toLRSHom.toShHom)).trans (Category.comp_id _)

/-- **The comparison of [Stacks, Tag 0AUE] part (1)**, `f_new^! ∘ g_new^! ⟶ k_new^!` for a
factorisation `f ≫ g = k`: `D_X` applied to the composition isomorphism of `L(-)^*`
([Stacks, Tag 0D5S]) followed by `Lf^*(η_Y)`. -/
def fNewShriekCompHom {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (e : f ≫ g = k) (ωX : Std X)
    (ωY : Std Y) (ωZ : Std Z) :
    dualConj (dualInto ωY) (dualInto ωZ) (pull g) ⋙ dualConj (dualInto ωX) (dualInto ωY) (pull f) ⟶
      dualConj (dualInto ωX) (dualInto ωZ) (pull k) :=
  dualConjComp (bidualityNat ωY) (pullFactorIso f g k e)

/-- **Associativity of the comparisons** ([Stacks, Tag 0AUE] part (1)): for `f ≫ g ≫ h`, the
two comparisons `f_new^! ∘ g_new^! ∘ h_new^! ⟶ (f ≫ g ≫ h)_new^!` agree. -/
theorem fNewShriekCompHom_assoc {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T} {k₁ : X ⟶ Z} {k₂ : Y ⟶ T}
    {k : X ⟶ T} (e₁ : f ≫ g = k₁) (e₂ : g ≫ h = k₂) (e₃ : k₁ ≫ h = k) (e₄ : f ≫ k₂ = k)
    (ωX : Std X) (ωY : Std Y) (ωZ : Std Z) (ωT : Std T) (M : Std T) :
    (dualConj (dualInto ωX) (dualInto ωY) (pull f)).map ((fNewShriekCompHom e₂ ωY ωZ ωT).app M) ≫
        (fNewShriekCompHom e₄ ωX ωY ωT).app M =
      (fNewShriekCompHom e₁ ωX ωY ωZ).app ((dualConj (dualInto ωZ) (dualInto ωT) (pull h)).obj M) ≫
        (fNewShriekCompHom e₃ ωX ωZ ωT).app M :=
  dualConjComp_assoc (DA := dualInto ωX) (DD := dualInto ωT) (bidualityNat ωY)
    (bidualityNat ωZ) (pullFactorIso f g k₁ e₁) (pullFactorIso g h k₂ e₂)
    (pullFactorIso k₁ h k e₃) (pullFactorIso f k₂ k e₄)
    (fun N => pullFactorIso_assoc f g h e₁ e₂ e₃ e₄ N) M

/-- **The unit comparison** `id ⟶ (id_X)_new^!`: `η_X` followed by `D_X` of `L(𝟙_X)^* ≅ id`. -/
def fNewShriekUnitHom (ωX : Std X) :
    𝟭 (Std X) ⟶ dualConj (dualInto ωX) (dualInto ωX) (pull (𝟙 X)) :=
  dualConjUnit (bidualityNat ωX) (pullIdIso X)

/-- **The left unit law** of [Stacks, Tag 0AUE] part (1). -/
theorem fNewShriekUnitHom_comp_fNewShriekCompHom {g : Y ⟶ Z} (w : 𝟙 Y ≫ g = g)
    (ωY : Std Y) (ωZ : Std Z) (M : Std Z) :
    (fNewShriekUnitHom ωY).app ((dualConj (dualInto ωY) (dualInto ωZ) (pull g)).obj M) ≫
      (fNewShriekCompHom w ωY ωY ωZ).app M =
        𝟙 ((dualConj (dualInto ωY) (dualInto ωZ) (pull g)).obj M) :=
  dualConjUnit_comp_dualConjComp (bidualityNat ωY) (fun M => bidualityNat_triangle ωY M)
    (pullIdIso Y) (pullFactorIso (𝟙 Y) g g w) (fun N => pullFactorIso_id_comp g w N) M

/-- **The right unit law** of [Stacks, Tag 0AUE] part (1). -/
theorem map_fNewShriekUnitHom_comp_fNewShriekCompHom {f : X ⟶ Y} (w : f ≫ 𝟙 Y = f)
    (ωX : Std X) (ωY : Std Y) (M : Std Y) :
    (dualConj (dualInto ωX) (dualInto ωY) (pull f)).map ((fNewShriekUnitHom ωY).app M) ≫
      (fNewShriekCompHom w ωX ωY ωY).app M =
        𝟙 ((dualConj (dualInto ωX) (dualInto ωY) (pull f)).obj M) :=
  map_dualConjUnit_comp_dualConjComp (bidualityNat ωY) (fun M => bidualityNat_triangle ωY M)
    (pullIdIso Y) (pullFactorIso f (𝟙 Y) f w) (fun N => pullFactorIso_comp_id f w N) M

/-! ### The comparisons are isomorphisms on `D^+_Coh` -/

/-- `D_Coh(𝒪_X)` at the standard model: coherent cohomology sheaves. -/
abbrev cohStd (X : Scheme.{u}) : ObjectProperty (Std X) :=
  fun M => @DerivedCategoryB.derivedCategoryB X.Modules _ _
    (AlgebraicGeometry.PerfectApproximation.standardModel X) (isCoherentSheaf X) M

/-- `D^-_Coh(𝒪_X)` at the standard model: bounded above with coherent cohomology sheaves. -/
abbrev minusCoh (X : Scheme.{u}) : ObjectProperty (Std X) :=
  fun M => @DerivedCategoryB.derivedCategoryBMinus X.Modules _ _
    (AlgebraicGeometry.PerfectApproximation.standardModel X) (isCoherentSheaf X) M

/-- On a Noetherian scheme an object of `D^-_Coh` is pseudo-coherent ([Stacks, Tag 08E8]). -/
theorem isPseudoCoherent_of_minusCoh [IsNoetherian X] (E : Std X) (hE : minusCoh X E) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E :=
  (isPseudoCoherent_iff_boundedAbove_coherent_homology X ⟨E, fun i => by
    have : ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsCoherent := hE.2 i
    exact (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (X := X) ((DerivedCategory.homologyFunctor X.Modules i).obj E)).1⟩).2 ⟨hE.1, hE.2⟩

/-- **`Lg^*` preserves `D^-_Coh`** for a morphism of Noetherian schemes: on Noetherian schemes
`D^-_Coh` consists of the pseudo-coherent objects of `D_QCoh` ([Stacks, Tag 08E8]), and derived
pullback preserves pseudo-coherence ([Stacks, Tag 09U7]) and `D_QCoh`. -/
theorem minusCoh_pull [IsNoetherian X] [IsNoetherian Y] (g : X ⟶ Y) (E : Std Y)
    (hE : minusCoh Y E) : minusCoh X ((pull g).obj E) := by
  have hP := AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_derivedPullback g _
    (isPseudoCoherent_of_minusCoh E hE)
  have hQ := Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isDQCoh_derivedPullback_obj g E
    ((TwistedInverseImageDuality.qcoh_iff_isDQCoh E).1
      (TwistedInverseImageDuality.qcoh_of_isCoherent E hE.2))
  exact (isPseudoCoherent_iff_boundedAbove_coherent_homology X ⟨(pull g).obj E, hQ⟩).1 hP

/-- The dual of an object of `D^+_Coh` lies in `D^-_Coh` ([Stacks, Tag 0A89]). -/
theorem minusCoh_dual [IsNoetherian X] {ω : Std X} (hω : IsDualizingComplex ω) (M : Std X)
    (hM : plusCoh X M) : minusCoh X ((dualInto ω).obj (op M)) :=
  ⟨isBoundedAbove_derivedSheafHom_of_isDualizingComplex hω hM.2 hM.1,
    fun i => isCoherent_homology_derivedSheafHom_of_isDualizingComplex hω hM.2 i⟩

/-- The dual of an object of `D^-_Coh` lies in `D^+_Coh` ([Stacks, Tag 0A89]). -/
theorem plusCoh_dual [IsNoetherian X] {ω : Std X} (hω : IsDualizingComplex ω) (M : Std X)
    (hM : minusCoh X M) : plusCoh X ((dualInto ω).obj (op M)) :=
  ⟨isBoundedBelow_derivedSheafHom_of_isDualizingComplex hω hM.2 hM.1,
    fun i => isCoherent_homology_derivedSheafHom_of_isDualizingComplex hω hM.2 i⟩

/-- **Duality exchanges `D^+_Coh` and `D^-_Coh`** ([Stacks, Tag 0A89]): for `M ∈ D_Coh(𝒪_X)`,
`M ∈ D^+_Coh` iff `D(M) ∈ D^-_Coh`, and `M ∈ D^-_Coh` iff `D(M) ∈ D^+_Coh`. -/
theorem plusCoh_iff_minusCoh_dual [IsNoetherian X] {ω : Std X} (hω : IsDualizingComplex ω)
    (M : Std X) (hM : cohStd X M) :
    (plusCoh X M ↔ minusCoh X ((dualInto ω).obj (op M))) ∧
      (minusCoh X M ↔ plusCoh X ((dualInto ω).obj (op M))) := by
  obtain ⟨h1, h2⟩ := isBoundedBelow_iff_isBoundedAbove_derivedSheafHom X hω M hM
  have hD : cohStd X ((dualInto ω).obj (op M)) :=
    fun i => isCoherent_homology_derivedSheafHom_of_isDualizingComplex hω hM i
  exact ⟨⟨fun h => ⟨h1.1 h.1, hD⟩, fun h => ⟨h1.2 h.1, hM⟩⟩,
    ⟨fun h => ⟨h2.1 h.1, hD⟩, fun h => ⟨h2.2 h.1, hM⟩⟩⟩

/-- **`f_new^!` maps `D^+_Coh(𝒪_Y)` into `D^+_Coh(𝒪_X)`** for dualizing `ω_X`, `ω_Y`. -/
theorem plusCoh_fNewShriek [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) {ωX : Std X}
    {ωY : Std Y} (hωX : IsDualizingComplex ωX) (hωY : IsDualizingComplex ωY) (M : Std Y)
    (hM : plusCoh Y M) : plusCoh X ((dualConj (dualInto ωX) (dualInto ωY) (pull f)).obj M) :=
  plusCoh_dual hωX _ (minusCoh_pull f _ (minusCoh_dual hωY M hM))

/-- The biduality `η` is an isomorphism at objects with coherent cohomology
([Stacks, Tag 0A89]). -/
theorem isIso_bidualityNat_app [IsLocallyNoetherian X] {ω : Std X} (hω : IsDualizingComplex ω)
    (M : Std X) (hM : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj M).IsCoherent) :
    IsIso ((bidualityNat ω).app M) := by
  rw [bidualityNat, MonoidalClosed.closedBiduality_app,
    TwistedInverseImageDuality.closedBidualityApp_std]
  exact isIso_derivedBiduality_of_isDualizingComplex ω M hω hM

/-- **The comparisons of [Stacks, Tag 0AUE] part (1) are isomorphisms on `D^+_Coh`**:
for `f ≫ g = k` between Noetherian schemes with dualizing `ω_Y`, `ω_Z`, the comparison
`f_new^!(g_new^! M) ⟶ k_new^! M` is invertible for `M ∈ D^+_Coh(𝒪_Z)`. -/
theorem isIso_fNewShriekCompHom_app [IsNoetherian Y] [IsNoetherian Z] {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : X ⟶ Z} (e : f ≫ g = k) (ωX : Std X) {ωY : Std Y} {ωZ : Std Z}
    (hωY : IsDualizingComplex ωY) (hωZ : IsDualizingComplex ωZ) (M : Std Z) (hM : plusCoh Z M) :
    IsIso ((fNewShriekCompHom e ωX ωY ωZ).app M) := by
  have h := isIso_bidualityNat_app hωY _ (minusCoh_pull g _ (minusCoh_dual hωZ M hM)).2
  rw [fNewShriekCompHom, dualConjComp_app]
  infer_instance

/-- **The unit comparison of [Stacks, Tag 0AUE] part (1) is an isomorphism on `D_Coh`.** -/
theorem isIso_fNewShriekUnitHom_app [IsLocallyNoetherian X] {ωX : Std X}
    (hωX : IsDualizingComplex ωX) (M : Std X)
    (hM : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj M).IsCoherent) :
    IsIso ((fNewShriekUnitHom ωX).app M) := by
  have h := isIso_bidualityNat_app hωX M hM
  rw [fNewShriekUnitHom, dualConjUnit_app]
  infer_instance

end Stacks.Duality

end
