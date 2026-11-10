module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorLoc
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectRestrictOpen
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectFullAffine
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectCatPullbackLocComp
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquareIsoInvariance

/-!
# The square of Example 0EVH over a basic open, read as the square over the localisation

Over a basic open `D(x)` of `Spec A`, the almost blowup square of [Stacks, Example 0EVH] restricted
to the preimages of `D(x)` is isomorphic, by a cube of isomorphisms
(`AlgebraicGeometry.awayCube_faces`), to the two-generator square over the localisation `A_x`.
This file transports the comparison functor of [Stacks, Tag 0EXD] along that cube.

## Main results

* `AlgebraicGeometry.full_frobeniusColimitVectorBundlesCatPullbackLoc_of_isIso` and
  `…faithful_…`: restriction of the categorical fibre products along a cube of isomorphisms is
  full and faithful.
* `AlgebraicGeometry.fullyFaithful_frobeniusColimitVectorBundlesComparison_of_isIso`: full
  faithfulness of the comparison functor transfers along a cube of isomorphisms.
* `AlgebraicGeometry.fullyFaithful_frobeniusColimitComparisonRestrict_of_eq_basicOpen`: the
  comparison functor over `D(x)` is full and faithful.
* `AlgebraicGeometry.mem_essImage_frobeniusColimitComparisonRestrict_of_loc`: a local solution
  over `A_x` is a local solution over `D(x)`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Frobenius Stacks.AlmostBlowUp

universe u

namespace AlgebraicGeometry

section Generic

variable (p : ℕ) [Fact p.Prime]

/-- The diagram chase behind the fullness of restriction along a cube of isomorphisms, in an
arbitrary category: if `x` and `w` are conjugate to `α` and `β`, and `α`, `β` are compatible with
`y`, `z` through the conjugating isomorphisms, then `x ≫ y = z ≫ w`. -/
private theorem comp_eq_comp_of_conj {𝒞 : Type*} [Category 𝒞] {P P' Q Q' R R' S S' : 𝒞}
    (x : P ⟶ P') (y : P' ⟶ S') (z : P ⟶ S) (w : S ⟶ S') (α : Q ⟶ Q') (β : R ⟶ R')
    (s : P ≅ Q) (s' : P' ≅ Q') (t : S ≅ R) (t' : S' ≅ R')
    (hW : x ≫ s'.hom = s.hom ≫ α) (hV : w ≫ t'.hom = t.hom ≫ β)
    (hφ : α ≫ s'.inv ≫ y ≫ t'.hom = s.inv ≫ z ≫ t.hom ≫ β) : x ≫ y = z ≫ w := by
  have hx : x = s.hom ≫ α ≫ s'.inv := by simpa using hW =≫ s'.inv
  have hw : w = t.hom ≫ β ≫ t'.inv := by simpa using hV =≫ t'.inv
  rw [hx, hw]
  simpa using s.hom ≫= hφ =≫ t'.inv

section IsoCube

variable {X' Z E V' W D : Scheme.{u}} (q : E ⟶ X') (e : E ⟶ Z) (qV : D ⟶ V') (eV : D ⟶ W)
  (ιV' : V' ⟶ X') (ιW : W ⟶ Z) (ιD : D ⟶ E) [IsIso ιV'] [IsIso ιW] [IsIso ιD]
  (hX' : IsInCharacteristic X' p) (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
  (hV' : IsInCharacteristic V' p) (hW : IsInCharacteristic W p) (hD : IsInCharacteristic D p)
  (sq : qV ≫ ιV' = ιD ≫ q) (se : eV ≫ ιW = ιD ≫ e)

omit [IsIso ιD] in
/-- **Restriction of the categorical fibre products along a cube of isomorphisms is faithful.** -/
theorem faithful_frobeniusColimitVectorBundlesCatPullbackLoc_of_isIso :
    (frobeniusColimitVectorBundlesCatPullbackLoc p q e qV eV ιV' ιW ιD
      hX' hZ hE hV' hW hD sq se).Faithful where
  map_injective h := CategoricalPullback.hom_ext
    ((frobeniusColimitVectorBundlesPullback p ιW hW hZ).map_injective
      (congrArg CategoricalPullback.Hom.fst h))
    ((frobeniusColimitVectorBundlesPullback p ιV' hV' hX').map_injective
      (congrArg CategoricalPullback.Hom.snd h))

/-- **Restriction of the categorical fibre products along a cube of isomorphisms is full.** -/
theorem full_frobeniusColimitVectorBundlesCatPullbackLoc_of_isIso :
    (frobeniusColimitVectorBundlesCatPullbackLoc p q e qV eV ιV' ιW ιD
      hX' hZ hE hV' hW hD sq se).Full where
  map_surjective {T T'} φ := by
    let ΦW := frobeniusColimitVectorBundlesPullback p ιW hW hZ
    let ΦV := frobeniusColimitVectorBundlesPullback p ιV' hV' hX'
    let ΦD := frobeniusColimitVectorBundlesPullback p ιD hD hE
    let σW := frobeniusColimitVectorBundlesSquareIso p ιW e eV ιD hZ hW hE hD se
    let σV := frobeniusColimitVectorBundlesSquareIso p ιV' q qV ιD hX' hV' hE hD sq
    obtain ⟨a, ha⟩ := ΦW.map_surjective φ.fst
    obtain ⟨c, hc⟩ := ΦV.map_surjective φ.snd
    have hφ := φ.w
    have hW₁ := σW.hom.naturality a
    have hV₁ := σV.hom.naturality c
    simp only [Functor.comp_obj, Functor.comp_map] at hW₁ hV₁
    refine ⟨⟨a, c, ΦD.map_injective ?_⟩, CategoricalPullback.hom_ext ha hc⟩
    simp only [frobeniusColimitVectorBundlesCatPullbackLoc, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc] at hφ
    rw [ha] at hW₁
    rw [hc] at hV₁
    rw [Functor.map_comp, Functor.map_comp]
    exact comp_eq_comp_of_conj _ _ _ _ _ _ (σW.app T.fst) (σW.app T'.fst)
      (σV.app T.snd) (σV.app T'.snd) hW₁ hV₁ hφ

include sq se hD hE in
/-- **Full faithfulness of the comparison functor transfers along a cube of isomorphisms.**  If
the four vertical maps of a cube of commutative squares are isomorphisms and the comparison
functor of the top square is full and faithful, so is the comparison functor of the bottom one:
restriction to the top square identifies `G` followed by the restriction of the categorical fibre
products, which is fully faithful, with the restriction of modules, an equivalence, followed by
the comparison functor of the top square. -/
theorem fullyFaithful_frobeniusColimitVectorBundlesComparison_of_isIso
    {X V : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) (bV : V' ⟶ V) (zV : W ⟶ V) (ιV : V ⟶ X) [IsIso ιV]
    (hX : IsInCharacteristic X p) (hV : IsInCharacteristic V p)
    (hw : q ≫ b = e ≫ z) (hwV : qV ≫ bV = eV ≫ zV) (sb : bV ≫ ιV = ιV' ≫ b)
    (sz : zV ≫ ιV = ιW ≫ z)
    (hFF : (frobeniusColimitVectorBundlesComparison p bV zV qV eV hV hV' hW hD hwV).Full ∧
      (frobeniusColimitVectorBundlesComparison p bV zV qV eV hV hV' hW hD hwV).Faithful) :
    (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).Full ∧
      (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).Faithful := by
  obtain ⟨h₁, h₂⟩ := hFF
  let Φ := frobeniusColimitVectorBundlesCatPullbackLoc p q e qV eV ιV' ιW ιD
    hX' hZ hE hV' hW hD sq se
  have hΦf : Φ.Faithful :=
    faithful_frobeniusColimitVectorBundlesCatPullbackLoc_of_isIso p q e qV eV ιV' ιW ιD
      hX' hZ hE hV' hW hD sq se
  have hΦF : Φ.Full :=
    full_frobeniusColimitVectorBundlesCatPullbackLoc_of_isIso p q e qV eV ιV' ιW ιD
      hX' hZ hE hV' hW hD sq se
  let α : frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw ⋙ Φ ≅
      frobeniusColimitVectorBundlesPullback p ιV hV hX ⋙
        frobeniusColimitVectorBundlesComparison p bV zV qV eV hV hV' hW hD hwV :=
    NatIso.ofComponents
      (fun M => frobeniusColimitVectorBundlesCatPullbackLocIso p b z q e bV zV qV eV ιV ιV' ιW ιD
        hX hX' hZ hE hV hV' hW hD sq se hw hwV sb sz M)
      (fun f => frobeniusColimitVectorBundlesCatPullbackLocIso_naturality p b z q e bV zV qV eV
        ιV ιV' ιW ιD hX hX' hZ hE hV hV' hW hD hw hwV sb sz sq se f)
  have : (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw ⋙ Φ).Full :=
    Functor.Full.of_iso α.symm
  have : (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw ⋙ Φ).Faithful :=
    Functor.Faithful.of_iso α.symm
  exact ⟨Functor.Full.of_comp_faithful _ Φ, Functor.Faithful.of_comp _ Φ⟩

end IsoCube

end Generic

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- The base of the square over `A_x` is the basic open `D(x)`, as an open subscheme. -/
abbrev awayBaseIso (x : A) : Spec (.of (Localization.Away x)) ≅
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))).opensRange.toScheme :=
  (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))).isoOpensRange

/-- Two morphisms into a subobject `ι` agree if their composites with `ι` agree, as computed
through `hi`, `h`, `hj`, `hs`. -/
private theorem eq_of_comp_mono_eq {𝒞 : Type*} [Category 𝒞] {X Y N M E C : 𝒞} {a : X ⟶ Y}
    {i : Y ⟶ N} {ι : N ⟶ M} [Mono ι] {μ : Y ⟶ M} {j : X ⟶ E} {s : E ⟶ N} {ιE : E ⟶ C}
    {π : X ⟶ C} {q : C ⟶ M} (hi : i ≫ ι = μ) (h : a ≫ μ = π ≫ q) (hj : j ≫ ιE = π)
    (hs : s ≫ ι = ιE ≫ q) : a ≫ i = j ≫ s := by
  rw [← cancel_mono ι, Category.assoc, Category.assoc, hi, h, ← hj, hs, Category.assoc]

/-- **The four side faces of the cube from the square over `A_x` to the square of
[Stacks, Example 0EVH] restricted over `D(x)`.** -/
theorem awayCube_faces (x : A) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    letI := (twoGeneratorSquare (Localization.Away x) (algebraMap A (Localization.Away x) f₁)
      (algebraMap A (Localization.Away x) f₂)).modificationGraded
    let U := (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))).opensRange
    (modificationToBase _ _ _ ≫ (awayBaseIso A x).hom =
        (modificationAwayIsoPreimage A f₁ f₂ x).hom ≫ modificationToBase A f₁ f₂ ∣_ U) ∧
      (centerToBase _ _ _ ≫ (awayBaseIso A x).hom =
        (centerAwayIsoPreimage A f₁ f₂ x).hom ≫ centerToBase A f₁ f₂ ∣_ U) ∧
      (exceptionalToModification _ _ _ ≫ (modificationAwayIsoPreimage A f₁ f₂ x).hom =
        (exceptionalAwayIsoPreimage A f₁ f₂ x).hom ≫
          squareRestrictQ (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
            (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
            (twoGenerator_isPullback A f₁ f₂).w U) ∧
      (exceptionalToCenter _ _ _ ≫ (centerAwayIsoPreimage A f₁ f₂ x).hom =
        (exceptionalAwayIsoPreimage A f₁ f₂ x).hom ≫
          exceptionalToCenter A f₁ f₂ ∣_ (centerToBase A f₁ f₂ ⁻¹ᵁ U)) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  let := (twoGeneratorSquare (Localization.Away x) (algebraMap A (Localization.Away x) f₁)
      (algebraMap A (Localization.Away x) f₂)).modificationGraded
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact eq_of_comp_mono_eq (Scheme.Hom.isoOpensRange_hom_ι _)
      (isPullback_modificationToBase_coeff A (Localization.Away x) f₁ f₂).w
      (modificationAwayIsoPreimage_hom_ι A f₁ f₂ x) (morphismRestrict_ι _ _)
  · exact eq_of_comp_mono_eq (Scheme.Hom.isoOpensRange_hom_ι _)
      (isPullback_centerToBase_coeff A (Localization.Away x) f₁ f₂).w
      (centerAwayIsoPreimage_hom_ι A f₁ f₂ x) (morphismRestrict_ι _ _)
  · exact eq_of_comp_mono_eq (modificationAwayIsoPreimage_hom_ι A f₁ f₂ x)
      (exceptionalToModification_comp_modificationCoeffProjMap A _ f₁ f₂)
      (exceptionalAwayIsoPreimage_hom_ι A f₁ f₂ x) (squareRestrictQ_ι _ _ _ _ _ _)
  · exact eq_of_comp_mono_eq (centerAwayIsoPreimage_hom_ι A f₁ f₂ x)
      (isPullback_exceptionalToCenter_coeff A _ f₁ f₂).w
      (exceptionalAwayIsoPreimage_hom_ι A f₁ f₂ x) (morphismRestrict_ι _ _)

/-- **Q1a: the comparison functor of [Stacks, Tag 0EXD] for the square of
[Stacks, Example 0EVH] restricted over a basic open `D(x)` is full and faithful.**  The restricted
square is the square over the localisation `A_x` up to a cube of isomorphisms
(`AlgebraicGeometry.awayCube_faces`), and full faithfulness over `A_x` is
`AlgebraicGeometry.fullyFaithful_twoGeneratorFrobeniusColimitComparison`. -/
theorem fullyFaithful_frobeniusColimitComparisonRestrict_of_eq_basicOpen (p : ℕ) [Fact p.Prime]
    (hpA : (p : A) = 0) (hp : p.Prime) (x : A) (U : (Spec (.of A)).Opens)
    (hU : U = PrimeSpectrum.basicOpen x) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (frobeniusColimitComparisonRestrict p (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
        (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
        (isInCharacteristic_spec A p hpA)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (twoGenerator_isPullback A f₁ f₂).w U).Full ∧
    (frobeniusColimitComparisonRestrict p (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
        (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
        (isInCharacteristic_spec A p hpA)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (twoGenerator_isPullback A f₁ f₂).w U).Faithful := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  let := (twoGeneratorSquare (Localization.Away x) (algebraMap A (Localization.Away x) f₁)
      (algebraMap A (Localization.Away x) f₂)).modificationGraded
  obtain rfl : U = (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))).opensRange :=
    hU.trans (opensRange_specMap_algebraMap_localizationAway A x).symm
  have hpx := natCast_eq_zero_of_algebra A p hpA (Localization.Away x)
  obtain ⟨sb, sz, sq, se⟩ := awayCube_faces A f₁ f₂ x
  exact fullyFaithful_frobeniusColimitVectorBundlesComparison_of_isIso p _ _ _ _
    (modificationAwayIsoPreimage A f₁ f₂ x).hom (centerAwayIsoPreimage A f₁ f₂ x).hom
    (exceptionalAwayIsoPreimage A f₁ f₂ x).hom _ _ _
    (isInCharacteristic_twoGeneratorModification _ _ _ p hpx)
    (isInCharacteristic_twoGeneratorCenter _ _ _ p hpx)
    (isInCharacteristic_twoGeneratorExceptional _ _ _ p hpx) sq se _ _ _ _
    (awayBaseIso A x).hom _ (isInCharacteristic_spec _ p hpx) _
    (twoGenerator_isPullback _ _ _).w sb sz
    (fullyFaithful_twoGeneratorFrobeniusColimitComparison p hp _ _ _ hpx)

/-- **Q1b: a triple whose restriction to the square over `A_x` comes from a module over `A_x` has
a restriction to the square over `D(x)` in the essential image.**  Restricting from the square
over `D(x)` to the square over `A_x` along the cube of isomorphisms is fully faithful
(`AlgebraicGeometry.full_frobeniusColimitVectorBundlesCatPullbackLoc_of_isIso`), carries the
restriction over `D(x)` to the restriction over `A_x`
(`AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLocComp`) and commutes with the
comparison functors (`AlgebraicGeometry.frobeniusColimitVectorBundlesCatPullbackLocIso`); the
restriction of modules along `Spec A_x ≅ D(x)` is an equivalence. -/
theorem mem_essImage_frobeniusColimitComparisonRestrict_of_loc (p : ℕ) [Fact p.Prime]
    (hpA : (p : A) = 0) (x : A)
    (U : (Spec (.of A)).Opens) (hU : U = PrimeSpectrum.basicOpen x)
    (T : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      CategoricalPullback
        (frobeniusColimitVectorBundlesPullback p (exceptionalToCenter A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA))
        (frobeniusColimitVectorBundlesPullback p (exceptionalToModification A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)))
    (h : (twoGeneratorFrobeniusColimitComparison (Localization.Away x) _ _ p
        (natCast_eq_zero_of_algebra A p hpA _)).essImage
      ((twoGeneratorFrobeniusColimitLoc A f₁ f₂ p hpA (Localization.Away x)
        (natCast_eq_zero_of_algebra A p hpA _)).obj T)) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (frobeniusColimitComparisonRestrict p (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
        (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
        (isInCharacteristic_spec A p hpA)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (twoGenerator_isPullback A f₁ f₂).w U).essImage
      ((frobeniusColimitLocRestrict p (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
        (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (twoGenerator_isPullback A f₁ f₂).w U).obj T) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  let := (twoGeneratorSquare (Localization.Away x) (algebraMap A (Localization.Away x) f₁)
      (algebraMap A (Localization.Away x) f₂)).modificationGraded
  obtain rfl : U = (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))).opensRange :=
    hU.trans (opensRange_specMap_algebraMap_localizationAway A x).symm
  have hpx := natCast_eq_zero_of_algebra A p hpA (Localization.Away x)
  obtain ⟨sb, sz, sq, se⟩ := awayCube_faces A f₁ f₂ x
  obtain ⟨M, ⟨μ⟩⟩ := h
  set U := (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))).opensRange
  have hA := isInCharacteristic_spec A p hpA
  have hM := isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA
  have hC := isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA
  have hE := isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA
  have hw := (twoGenerator_isPullback A f₁ f₂).w
  let Ψ := frobeniusColimitVectorBundlesCatPullbackLoc p
    (squareRestrictQ (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
      (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂) hw U)
    (exceptionalToCenter A f₁ f₂ ∣_ (centerToBase A f₁ f₂ ⁻¹ᵁ U))
    (exceptionalToModification _ _ _) (exceptionalToCenter _ _ _)
    (modificationAwayIsoPreimage A f₁ f₂ x).hom (centerAwayIsoPreimage A f₁ f₂ x).hom
    (exceptionalAwayIsoPreimage A f₁ f₂ x).hom
    (isInCharacteristic_toScheme hM _) (isInCharacteristic_toScheme hC _)
    (isInCharacteristic_toScheme hE _)
    (isInCharacteristic_twoGeneratorModification _ _ _ p hpx)
    (isInCharacteristic_twoGeneratorCenter _ _ _ p hpx)
    (isInCharacteristic_twoGeneratorExceptional _ _ _ p hpx) sq se
  have : Ψ.Full := full_frobeniusColimitVectorBundlesCatPullbackLoc_of_isIso p _ _ _ _ _ _ _
    _ _ _ _ _ _ sq se
  have : Ψ.Faithful := faithful_frobeniusColimitVectorBundlesCatPullbackLoc_of_isIso p _ _ _ _
    _ _ _ _ _ _ _ _ _ sq se
  let ΦX := frobeniusColimitVectorBundlesPullback p (awayBaseIso A x).hom
    (isInCharacteristic_spec _ p hpx) (isInCharacteristic_toScheme hA U)
  let ι₁ := frobeniusColimitVectorBundlesCatPullbackLocIso p (modificationToBase A f₁ f₂ ∣_ U)
    (centerToBase A f₁ f₂ ∣_ U) _ _ (modificationToBase _ _ _) (centerToBase _ _ _) _ _
    (awayBaseIso A x).hom _ _ _ (isInCharacteristic_toScheme hA U)
    (isInCharacteristic_toScheme hM _) (isInCharacteristic_toScheme hC _)
    (isInCharacteristic_toScheme hE _) (isInCharacteristic_spec _ p hpx)
    (isInCharacteristic_twoGeneratorModification _ _ _ p hpx)
    (isInCharacteristic_twoGeneratorCenter _ _ _ p hpx)
    (isInCharacteristic_twoGeneratorExceptional _ _ _ p hpx) sq se
    (squareRestrict_w (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
      (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂) hw U)
    (twoGenerator_isPullback _ _ _).w sb sz (ΦX.objPreimage M)
  let ι₂ := (frobeniusColimitVectorBundlesCatPullbackLocComp p (exceptionalToModification A f₁ f₂)
    (exceptionalToCenter A f₁ f₂) _ _ (exceptionalToModification _ _ _) (exceptionalToCenter _ _ _)
    (modificationToBase A f₁ f₂ ⁻¹ᵁ U).ι (centerToBase A f₁ f₂ ⁻¹ᵁ U).ι
    (exceptionalToCenter A f₁ f₂ ⁻¹ᵁ centerToBase A f₁ f₂ ⁻¹ᵁ U).ι
    (modificationAwayIsoPreimage A f₁ f₂ x).hom (centerAwayIsoPreimage A f₁ f₂ x).hom
    (exceptionalAwayIsoPreimage A f₁ f₂ x).hom
    (modificationCoeffProjMap A (Localization.Away x) f₁ f₂)
    (Spec.map (CommRingCat.ofHom (centerCoeffHom A (Localization.Away x) f₁ f₂)))
    (Stacks.ProjectiveCohomology.projModelMap 1 (centerCoeffHom A (Localization.Away x) f₁ f₂))
    hM hC hE (isInCharacteristic_toScheme hM _) (isInCharacteristic_toScheme hC _)
    (isInCharacteristic_toScheme hE _)
    (isInCharacteristic_twoGeneratorModification _ _ _ p hpx)
    (isInCharacteristic_twoGeneratorCenter _ _ _ p hpx)
    (isInCharacteristic_twoGeneratorExceptional _ _ _ p hpx)
    (squareRestrictQ_ι (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
      (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂) hw U)
    (morphismRestrict_ι (exceptionalToCenter A f₁ f₂) (centerToBase A f₁ f₂ ⁻¹ᵁ U)) sq se
    (exceptionalToModification_comp_modificationCoeffProjMap A _ f₁ f₂)
    (isPullback_exceptionalToCenter_coeff A _ f₁ f₂).w
    (modificationAwayIsoPreimage_hom_ι A f₁ f₂ x) (centerAwayIsoPreimage_hom_ι A f₁ f₂ x)
    (exceptionalAwayIsoPreimage_hom_ι A f₁ f₂ x)).app T
  exact ⟨ΦX.objPreimage M, ⟨(Functor.FullyFaithful.ofFullyFaithful Ψ).preimageIso
    (ι₁ ≪≫ (twoGeneratorFrobeniusColimitComparison _ _ _ p hpx).mapIso
      (ΦX.objObjPreimageIso M) ≪≫ μ ≪≫ ι₂.symm)⟩⟩

end AlgebraicGeometry

end
