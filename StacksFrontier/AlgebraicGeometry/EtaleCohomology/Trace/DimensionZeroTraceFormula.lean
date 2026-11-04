module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroBlocks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionOne
public import StacksFrontier.Homology.Perfect.LargeUniverse

/-!
# The trace formula in dimension zero

Step 2 of the proof of [Stacks, Tag 03UG]: for a scheme `Y` finite étale over a finite field `k`
and a complex `C` on `Y`, the trace of the canonical Frobenius endomorphism `π_Y^*` of
`RΓ(Y_k̄, C|_{Y_k̄})` is the sum over the rational points `x ∈ Y(k)` of the traces of the geometric
Frobenius `π_x` on the stalks `C_x̄`.

The fixed points of `π̄ = π_Y × id` on the `k̄`-points of `Y_k̄` are exactly the points over the
rational points of `Y`, because the fixed field of the arithmetic Frobenius of `k̄` is `k`.

## Main results

* `Stacks.EtaleCohomology.exists_rationalPoint_of_specMap_comp_eq`: a `k̄`-point of a
  `k`-scheme fixed by the arithmetic Frobenius comes from a unique rational point.
* `Stacks.EtaleCohomology.fixedSectionsEquivRationalPoints`: the `π̄`-fixed `k̄`-points of `Y_k̄`
  are the rational points of `Y`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

/-! ### Frobenius-fixed points over a finite field -/

section FixedPoints

variable {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]

open Polynomial in
/-- An element of an extension field of the finite field `k` fixed by `z ↦ z ^ #k` lies in `k`. -/
lemma exists_algebraMap_eq_of_pow_card_eq (z : kbar) (hz : z ^ Fintype.card k = z) :
    ∃ c : k, algebraMap k kbar c = z := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hne : (Polynomial.X ^ Fintype.card k - Polynomial.X : kbar[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero kbar hq
  set S : Finset kbar := insert z (Finset.univ.image (algebraMap k kbar))
  have hsub : S.val ⊆ (Polynomial.X ^ Fintype.card k - Polynomial.X : kbar[X]).roots := by
    intro w hw
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
    rcases Finset.mem_insert.1 hw with rfl | hw
    · exact hz
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hw
      rw [← map_pow, FiniteField.pow_card]
  have hcard := (Multiset.card_le_card (Multiset.le_iff_subset S.nodup |>.2 hsub)).trans
    (card_roots' _)
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq kbar hq, Finset.card_val,
    Finset.card_insert_of_notMem (fun h => by
      obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h
      exact hcon c hc),
    Finset.card_image_of_injective _ (algebraMap k kbar).injective, Finset.card_univ] at hcard
  lia

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **A `k̄`-point fixed by the arithmetic Frobenius comes from a rational point**: a `k̄`-point
`a` of the `k`-scheme `X` with `Spec(σ) ≫ a = a` is `Spec k̄ ⟶ Spec k ⟶ X` for a section
`Spec k ⟶ X` of the structure morphism. -/
theorem exists_rationalPoint_of_specMap_comp_eq (σ : kbar ≃ₐ[k] kbar)
    (hσ : ∀ z : kbar, σ z = z ^ Fintype.card k) (a : Spec (.of kbar) ⟶ X)
    (ha : a ≫ f = specAlgebraMap k kbar)
    (hfix : Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ a = a) :
    ∃ x : Spec (.of k) ⟶ X, x ≫ f = 𝟙 _ ∧ specAlgebraMap k kbar ≫ x = a := by
  obtain ⟨⟨y, ι⟩, rfl⟩ := (Scheme.SpecToEquivOfField kbar X).symm.surjective a
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hfix ⊢
  have hι : fieldToResidue f y ≫ ι = CommRingCat.ofHom (algebraMap k kbar) :=
    (fromSpecResidueField_comp_eq_iff f kbar y ι).1 ha
  have hισ : ι ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom = ι := by
    have h1 :
        (Scheme.SpecToEquivOfField kbar X).symm ⟨y, ι ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom⟩ =
          (Scheme.SpecToEquivOfField kbar X).symm ⟨y, ι⟩ := by
      simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc]
      exact hfix
    exact eq_of_heq (Sigma.mk.inj_iff.1 ((Scheme.SpecToEquivOfField kbar X).symm.injective h1)).2
  have hsurj : Function.Surjective (fieldToResidue f y).hom := by
    intro t
    have ht : (ι.hom t) ^ Fintype.card k = ι.hom t := by
      rw [← hσ]
      exact congrArg (fun φ => φ.hom t) hισ
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_pow_card_eq kbar _ ht
    refine ⟨c, ι.hom.injective ?_⟩
    rw [← hc]
    exact congrArg (fun φ => φ.hom c) hι
  let e : k ≃+* X.residueField y :=
    RingEquiv.ofBijective (fieldToResidue f y).hom ⟨(fieldToResidue f y).hom.injective, hsurj⟩
  have he : ∀ c : k, e c = (fieldToResidue f y).hom c := fun _ => rfl
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecResidueField y, ?_, ?_⟩
  · exact ((fromSpecResidueField_comp_eq_iff f k y (CommRingCat.ofHom e.symm.toRingHom)).2 (by
      ext c
      change e.symm ((fieldToResidue f y).hom c) = c
      rw [← he, RingEquiv.symm_apply_apply])).trans (Spec.map_id (CommRingCat.of k))
  · rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext t
    change algebraMap k kbar (e.symm t) = ι.hom t
    have := congrArg (fun φ => φ.hom (e.symm t)) hι
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← this, ← he, RingEquiv.apply_symm_apply]

end FixedPoints

/-! ### The `π̄`-fixed points are the rational points -/

section Equiv

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [IsAlgClosed kbar] [Algebra k kbar] [Etale Y.hom] [IsFinite Y.hom] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

omit [Etale Y.hom] [IsFinite Y.hom] in
/-- On a `k̄`-point, the geometric Frobenius of `Y` is the arithmetic Frobenius of `k̄`:
`a ≫ π_Y = a ≫ F_Y^q = F_{Spec k̄}^q ≫ a = Spec(σ) ≫ a`. -/
lemma comp_geometricFrobenius_left (a : Spec (.of kbar) ⟶ Y.left) :
    a ≫ (geometricFrobenius Y p q hcard).left =
      Spec.map (CommRingCat.ofHom (arithmeticFrobenius k kbar p q hcard).toAlgHom.toRingHom) ≫
        a := by
  have hk : IsInCharacteristic (Spec (.of kbar)) p := isInCharacteristic_specAlgebraMap k kbar p
  rw [geometricFrobenius_left_eq_absoluteFrobeniusPow, ← absoluteFrobeniusPow_naturality a p hk,
    specMap_eq_absoluteFrobeniusPow _ p q hk (fun z => by
      simp [arithmeticFrobenius, iterateFrobenius_def])]

omit [Etale Y.hom] [IsFinite Y.hom] in
/-- The first projection of a `π̄`-fixed `k̄`-point is fixed by the arithmetic Frobenius. -/
lemma specMap_comp_fixedSection_fst (y : FixedSections Y kbar p q hcard) :
    Spec.map (CommRingCat.ofHom (arithmeticFrobenius k kbar p q hcard).toAlgHom.toRingHom) ≫
        y.1.1 ≫ pullback.fst Y.hom (specAlgebraMap k kbar) =
      y.1.1 ≫ pullback.fst Y.hom (specAlgebraMap k kbar) := by
  rw [← comp_geometricFrobenius_left, Category.assoc,
    ← geometricFrobeniusBaseChange_comp_fst, ← Category.assoc, ← y.2]

omit [IsAlgClosed kbar] [Etale Y.hom] [IsFinite Y.hom] [CharP kbar p] in
/-- The first projection of a `π̄`-fixed `k̄`-point is a `k̄`-point of `Y` over `k`. -/
lemma fixedSection_fst_comp (y : FixedSections Y kbar p q hcard) :
    (y.1.1 ≫ pullback.fst Y.hom (specAlgebraMap k kbar)) ≫ Y.hom = specAlgebraMap k kbar := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, y.1.2, Category.id_comp]

omit [Etale Y.hom] [IsFinite Y.hom] in
/-- The first projection of a `π̄`-fixed `k̄`-point comes from a rational point of `Y`. -/
lemma exists_rationalPoint_of_fixedSection (y : FixedSections Y kbar p q hcard) :
    ∃ x : Spec (.of k) ⟶ Y.left, x ≫ Y.hom = 𝟙 _ ∧
      specAlgebraMap k kbar ≫ x = y.1.1 ≫ pullback.fst Y.hom (specAlgebraMap k kbar) :=
  exists_rationalPoint_of_specMap_comp_eq kbar Y.hom (arithmeticFrobenius k kbar p q hcard)
    (fun z => arithmeticFrobenius_apply k kbar p q hcard z) _
    (fixedSection_fst_comp Y kbar p q hcard y) (specMap_comp_fixedSection_fst Y kbar p q hcard y)

/-- **The `π̄`-fixed `k̄`-points of `Y_k̄` are the rational points of `Y`**: a rational point `x`
corresponds to the `k̄`-point `ȳ = (x̄, id)` over it. -/
def fixedSectionsEquivRationalPoints : FixedSections Y kbar p q hcard ≃ rationalPoints Y.hom where
  toFun y := ⟨(exists_rationalPoint_of_fixedSection Y kbar p q hcard y).choose,
    (exists_rationalPoint_of_fixedSection Y kbar p q hcard y).choose_spec.1⟩
  invFun x := ⟨⟨rationalPointBaseChangeLift Y kbar x.1 x.2,
    rationalPointBaseChangeLift_snd Y kbar x.1 x.2⟩,
    (rationalPointBaseChangeLift_comp_geometricFrobeniusBaseChange Y kbar x.1 x.2 p q hcard).symm⟩
  left_inv y := Subtype.ext (Subtype.ext (pullback.hom_ext
    ((rationalPointBaseChangeLift_fst Y kbar _
        (exists_rationalPoint_of_fixedSection Y kbar p q hcard y).choose_spec.1).trans
      (exists_rationalPoint_of_fixedSection Y kbar p q hcard y).choose_spec.2)
    ((rationalPointBaseChangeLift_snd Y kbar _
        (exists_rationalPoint_of_fixedSection Y kbar p q hcard y).choose_spec.1).trans
      y.1.2.symm)))
  right_inv x := by
    have : Epi (specAlgebraMap k kbar) := Flat.epi_of_flat_of_surjective _
    exact Subtype.ext ((cancel_epi (specAlgebraMap k kbar)).1
      ((exists_rationalPoint_of_fixedSection Y kbar p q hcard _).choose_spec.2.trans
        (rationalPointBaseChangeLift_fst Y kbar x.1 x.2)))

omit [Etale Y.hom] [IsFinite Y.hom] in
/-- The `k̄`-point corresponding to a rational point `x` is `rationalPointBaseChangeLift`. -/
@[simp]
lemma fixedSectionsEquivRationalPoints_symm_apply (x : rationalPoints Y.hom) :
    ((fixedSectionsEquivRationalPoints Y kbar p q hcard).symm x).1.1 =
      rationalPointBaseChangeLift Y kbar x.1 x.2 :=
  rfl

end Equiv

/-! ### The trace formula on sections -/

section Trace

open CategoryTheory.FilteredDerived

attribute [local instance] moduleCat_hasLimitsOfSize HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Etale Y.hom] [IsFinite Y.hom]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- An isomorphism of complexes commuting termwise with two endomorphisms gives a commuting square
in the derived category. -/
private theorem Q_map_comp_mapIso_hom_eq {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {K L : CochainComplex A ℤ} (f : K ⟶ K) (g : L ⟶ L) (e : K ≅ L)
    (h : ∀ n, f.f n ≫ e.hom.f n = e.hom.f n ≫ g.f n) :
    DerivedCategory.Q.map f ≫ (DerivedCategory.Q.mapIso e).hom =
      (DerivedCategory.Q.mapIso e).hom ≫ DerivedCategory.Q.map g := by
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (HomologicalComplex.hom_ext _ _ h)

open scoped Classical in
/-- **Step 2 of [Stacks, Tag 03UG] on sections.**  For `Y` finite étale over `k` and a bounded
below complex `C` on `Y`, the trace of the canonical Frobenius twist on the sections of
`C|_{Y_k̄}` over the final object is `∑_{x ∈ Y(k)} Tr(π_x | C_x̄)`. -/
theorem perfectDerivedTrace_sectionsTwistEndo_eq_sum_rationalPoints
    [Fintype (rationalPoints Y.hom)] (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (hC : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((restrictionSections Λ Y kbar (baseChangeTop Y kbar)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.obj)))
    (hP : ∀ y, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((restrictionSections Λ Y kbar
        (etaleSectionObj (pullback.snd Y.hom (specAlgebraMap k kbar)) y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.obj)))
    (hstalk : ∀ x : rationalPoints Y.hom, StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ kbar x.1 C))) :
    perfectDerivedTrace Λ ⟨_, hC⟩ (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (sectionsTwistEndo Λ Y kbar p q hcard) _).app C.obj)) =
      ∑ x : rationalPoints Y.hom, perfectDerivedTrace Λ ⟨_, hstalk x⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard x.1 C)) := by
  rw [perfectDerivedTrace_sectionsTwistEndo_eq_sum Λ Y kbar p q hcard C.obj hC hP,
    ← Equiv.sum_comp (fixedSectionsEquivRationalPoints Y kbar p q hcard).symm]
  refine Fintype.sum_congr _ _ fun x => ?_
  exact perfectDerivedTrace_congr Λ _ _ (DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (rationalPointSectionsStalkIso Λ Y kbar x.1 x.2) _).app C.obj))
    _ _ (Q_map_comp_mapIso_hom_eq _ _ _ fun n =>
      rationalPointFrobeniusEndo_comp_rationalPointSectionsStalkIso_hom Λ Y kbar x.1 x.2 p q hcard
        (C.obj.X n))

/-- **Global sections of the direct image to `Spec k̄` are the sections over `baseChangeTop`**,
naturally in the sheaf on `Y`: global sections over `Spec k̄` are evaluation at its final
object. -/
def sectionsIso :
    etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar) ⋙
        etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)) ⋙
          etaleModuleGlobalSections.{u, r} Λ (Spec (.of kbar)) ≅
      restrictionSections Λ Y kbar (baseChangeTop Y kbar) :=
  Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar) ⋙
      etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleMkId (Spec (.of kbar))))

omit [IsAlgClosed kbar] [Etale Y.hom] [IsFinite Y.hom] [CharP kbar p] in
/-- The termwise endomorphism of `Γ(Spec k̄, pr_*(C|_{Y_k̄}))` is the twist on the sections over
`baseChangeTop` under `sectionsIso`. -/
lemma frobeniusRestrictionSectionsEndo_f_comp_sectionsIso_hom
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) (n : ℤ) :
    (frobeniusRestrictionSectionsEndo Λ Y kbar p q hcard C).hom.f n ≫
        (sectionsIso Λ Y kbar).hom.app (C.obj.X n) =
      (sectionsIso Λ Y kbar).hom.app (C.obj.X n) ≫
        (sectionsTwistEndo Λ Y kbar p q hcard).app (C.obj.X n) :=
  (Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{max (u + 1) r} Λ)
    (isTerminalEtaleMkId (Spec (.of kbar)))).hom.naturality
      ((etaleModuleDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          ((frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard).app (C.obj.X n)) ≫
        (etaleModuleDirectImageComp.{u, r} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm).hom.app
            ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).obj (C.obj.X n)))

/-- The complex `Γ(Spec k̄, pr_*(C|_{Y_k̄}))` is the complex of sections over `baseChangeTop`. -/
abbrev sectionsComplexIso (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    DerivedCategory.Q.obj (frobeniusRestrictionSectionsComplex Λ Y kbar C).obj ≅
      DerivedCategory.Q.obj (((restrictionSections Λ Y kbar
        (baseChangeTop Y kbar)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C.obj) :=
  DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (sectionsIso Λ Y kbar) _).app C.obj)

open scoped Classical in
/-- **Step 2 of [Stacks, Tag 03UG]: the trace formula for a scheme finite étale over `k`.**  For
a bounded below complex `C` on `Y`, the trace of the canonical Frobenius endomorphism `π_Y^*` of
`RΓ(Y_k̄, C|_{Y_k̄})` is `∑_{x ∈ Y(k)} Tr(π_x | C_x̄)`, provided the sections of `C|_{Y_k̄}` over
the `k̄`-points (which are its stalks there) are perfect. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_sum_of_etale
    [Fintype (rationalPoints Y.hom)] (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)))))
    (hP : ∀ y, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((restrictionSections Λ Y kbar
        (etaleSectionObj (pullback.snd Y.hom (specAlgebraMap k kbar)) y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.obj)))
    (hstalk : ∀ x : rationalPoints Y.hom, StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ kbar x.1 C))) :
    perfectDerivedTrace Λ ⟨_, hperf⟩
        (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C)) =
      ∑ x : rationalPoints Y.hom, perfectDerivedTrace Λ ⟨_, hstalk x⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard x.1 C)) := by
  have hC := StacksDraft.Perfect.isPerfect_of_iso (sectionsComplexIso Λ Y kbar C).symm
    ((isPerfect_frobeniusRestrictionSectionsComplex_iff Λ Y kbar C).1 hperf)
  rw [perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_isFinite Λ Y kbar p q hcard C
    hperf, ← perfectDerivedTrace_sectionsTwistEndo_eq_sum_rationalPoints Λ Y kbar p q hcard C hC hP
    hstalk]
  exact perfectDerivedTrace_congr Λ _ _ (sectionsComplexIso Λ Y kbar C) _ _
    (Q_map_comp_mapIso_hom_eq _ _ _ fun n =>
      frobeniusRestrictionSectionsEndo_f_comp_sectionsIso_hom Λ Y kbar p q hcard C n)

/-- **The sections over a `k̄`-point are the stalk there.**  For a `k̄`-point `ȳ` of `Y_k̄` over
`k̄`, the sections of `C|_{Y_k̄}` over `ȳ` are the stalk of `C` at the geometric point `ȳ ≫ pr`
of `Y`, naturally in `C`. -/
def sectionStalkIso (y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar))) :
    restrictionSections Λ Y kbar (etaleSectionObj _ y) ≅
      (Scheme.pointSmallEtale (y.1 ≫ fieldBaseChangeProj Y kbar)).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ) :=
  haveI := etale_of_section _ y.1 y.2
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      (presheafFiberSelfIso y.1 (ModuleCat.{max (u + 1) r} Λ))) ≪≫
    etaleModuleStalkPullbackIso Λ (fieldBaseChangeProj Y kbar) y.1

omit [Fintype k] [IsFinite Y.hom] in
/-- If the stalk of `C` at the geometric point `ȳ ≫ pr` of `Y` is perfect, then so are the
sections of `C|_{Y_k̄}` over the `k̄`-point `ȳ`. -/
lemma isPerfect_restrictionSections_of_stalk (C : CochainComplex (EtaleModules.{u, r} Λ Y.left) ℤ)
    (y : EtaleSections (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (h : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale (y.1 ≫ fieldBaseChangeProj Y kbar)).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj C))) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((restrictionSections Λ Y kbar
        (etaleSectionObj (pullback.snd Y.hom (specAlgebraMap k kbar)) y)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C)) :=
  StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (sectionStalkIso Λ Y kbar y) _).app C)) h

open scoped Classical in
/-- **Step 2 of [Stacks, Tag 03UG], with perfect geometric stalks.**  For `Y` finite étale over
`k` and a bounded below complex `C` on `Y` whose stalks at all geometric points are perfect,
`Tr(π_Y^* | RΓ(Y_k̄, C|_{Y_k̄})) = ∑_{x ∈ Y(k)} Tr(π_x | C_x̄)`. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_sum_of_etale'
    [Fintype (rationalPoints Y.hom)] (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)))))
    (hstalk : ∀ s : GeometricPoint Y.left, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          C.obj))) :
    perfectDerivedTrace Λ ⟨_, hperf⟩
        (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C)) =
      ∑ x : rationalPoints Y.hom, perfectDerivedTrace Λ
        ⟨_, hstalk (rationalGeometricPoint kbar x.1)⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard x.1 C)) :=
  perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_sum_of_etale Λ Y kbar p q hcard C hperf
    (fun y => isPerfect_restrictionSections_of_stalk Λ Y kbar C.obj y
      (hstalk ⟨kbar, y.1 ≫ fieldBaseChangeProj Y kbar⟩)) _

end Trace

end Stacks.EtaleCohomology

end
