module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Flat.LocalizationReduction

/-!
# Objects of `D(R)` isomorphic to a flat module placed in degree zero

For a commutative ring `R`, an object `N` of the derived category `D(R)` *is a flat module in
degree zero* when it is isomorphic to `F[0]` for a flat `R`-module `F`. This file records the
formal properties of that condition with respect to derived base change `- ⊗ᴸ_R R'` along a ring
map `φ : R → R'`, used in the converse of Stacks 0H89.

## Main definitions

* `StacksDraft.DerivedFlat.IsFlatInDegreeZero`: the condition.
* `StacksDraft.DerivedFlat.BaseChangeFlat`: the condition on the derived base change of a fixed
  object along a ring map out of its ring.
* `StacksDraft.DerivedFlat.BaseChangeLE`: the vanishing of the positive cohomology of such a
  derived base change.

## Main results

* `StacksDraft.DerivedFlat.isFlatInDegreeZero_iff_homology`: the condition says that the
  cohomology vanishes outside degree zero and is flat in degree zero.
* `StacksDraft.DerivedFlat.IsFlatInDegreeZero.baseChange`: it is preserved by derived base change,
  since a flat module in a single degree is K-flat (Stacks 064K).
* `StacksDraft.DerivedFlat.BaseChangeFlat.comp`, `BaseChangeFlat.of_comp_ringEquiv`: it moves
  along composites of ring maps, and back along ring isomorphisms.
* `StacksDraft.DerivedFlat.BaseChangeFlat.of_away_of_quotient`: Stacks 0H85 in this vocabulary.
* `StacksDraft.DerivedFlat.BaseChangeFlat.of_quotient_of_le_nilradical`: the condition descends
  along the quotient by a finitely generated ideal of nilpotent elements, by Stacks 0H85 applied
  once for each generator, the localization at a nilpotent element being the zero ring.

## Implementation notes

All rings and all modules are in one universe `u`, the derived categories are read at
`HasDerivedCategory.standard`, and derived base change is
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, as in Stacks 0H85.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace StacksDraft.DerivedFlat

section Definition

variable {R : Type u} [CommRing R]

/-- An object of `D(R)` *is a flat module in degree zero* when it is isomorphic to a flat
`R`-module placed in degree `0`. -/
def IsFlatInDegreeZero (N : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ F : ModuleCat.{u} R, Module.Flat R F ∧
    Nonempty (N ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj F)

/-- Being a flat module in degree zero is invariant under isomorphism in `D(R)`. -/
lemma IsFlatInDegreeZero.of_iso {N N' : DerivedCategory (ModuleCat.{u} R)}
    (h : IsFlatInDegreeZero N) (e : N ≅ N') : IsFlatInDegreeZero N' := by
  obtain ⟨F, hF, ⟨e'⟩⟩ := h
  exact ⟨F, hF, ⟨e.symm ≪≫ e'⟩⟩

/-- An object of `D(R)` is a flat module in degree zero exactly when its cohomology vanishes in
every nonzero degree and is a flat module in degree zero. -/
lemma isFlatInDegreeZero_iff_homology (N : DerivedCategory (ModuleCat.{u} R)) :
    IsFlatInDegreeZero N ↔
      (∀ i : ℤ, i ≠ 0 →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj N)) ∧
        Module.Flat R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj N) := by
  have key : ∀ F : ModuleCat.{u} R,
      (N ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj F) →
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj N ≅ F) := fun F e =>
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app F
  constructor
  · rintro ⟨F, hF, ⟨e⟩⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e)
      rcases lt_or_gt_of_ne hi with h | h
      · exact DerivedCategory.isZero_of_isGE _ 0 i h
      · exact DerivedCategory.isZero_of_isLE _ 0 i h
    · exact Module.Flat.of_linearEquiv (M := F) (key F e).toLinearEquiv
  · rintro ⟨h, hflat⟩
    have hGE : N.IsGE 0 := (DerivedCategory.isGE_iff N 0).2 (fun i hi => h i (by omega))
    have hLE : N.IsLE 0 := (DerivedCategory.isLE_iff N 0).2 (fun i hi => h i (by omega))
    obtain ⟨E, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE N 0
    refine ⟨E, ?_, ⟨e⟩⟩
    exact Module.Flat.of_linearEquiv
      (M := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj N)
      (key E e).symm.toLinearEquiv

/-- Over the zero ring every object of the derived category is a flat module in degree zero. -/
lemma isFlatInDegreeZero_of_subsingleton [Subsingleton R]
    (N : DerivedCategory (ModuleCat.{u} R)) : IsFlatInDegreeZero N := by
  have hzero : ∀ M : ModuleCat.{u} R, IsZero M := fun M => by
    have : Subsingleton M := Module.subsingleton R M
    exact ModuleCat.isZero_of_subsingleton M
  rw [isFlatInDegreeZero_iff_homology]
  refine ⟨fun i _ => hzero _, ?_⟩
  have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj N) :=
    Module.subsingleton R _
  infer_instance

end Definition

section BaseChange

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Derived extension of scalars of a flat module placed in degree zero is its extension of
scalars placed in degree zero: such a single complex is K-flat (Stacks 064K), so the comparison
from derived to termwise extension of scalars is invertible at it. -/
def baseChangeSingleIsoOfFlat (φ : R →+* S) (F : ModuleCat.{u} R) [Module.Flat R F] :
    (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj F) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj
        ((ModuleCat.extendScalars.{u, u, u} φ).obj F) := by
  let D := totalDerivedExtensionScalars.{u, u, u} φ
  let _ := D.additive
  let P := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj F
  have hflat : ∀ i : ℤ, Module.Flat R (P.X i) := by
    intro i
    rcases eq_or_ne i 0 with rfl | hi
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).toLinearEquiv
    · have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i hi)
      infer_instance
  have hP : CochainComplex.KFlat.{u, u} P := CochainComplex.KFlat.kFlat_of_flat.{u, u} P 0
  have hcomp : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  exact D.functor.mapIso ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app F) ≪≫
    @asIso _ _ _ _ _ hcomp ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars.{u, u, u} φ) (ComplexShape.up ℤ) 0).app F) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} S) 0).app _).symm

/-- **Derived base change preserves flat modules in degree zero.** -/
lemma IsFlatInDegreeZero.baseChange (φ : R →+* S) {N : DerivedCategory (ModuleCat.{u} R)}
    (h : IsFlatInDegreeZero N) :
    IsFlatInDegreeZero ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj N) := by
  obtain ⟨F, hF, ⟨e⟩⟩ := h
  refine ⟨(ModuleCat.extendScalars.{u, u, u} φ).obj F, ?_,
    ⟨(totalDerivedExtensionScalars.{u, u, u} φ).functor.mapIso e ≪≫
      baseChangeSingleIsoOfFlat φ F⟩⟩
  let _ : Algebra R S := φ.toAlgebra
  show Module.Flat S (TensorProduct R S F)
  infer_instance

end BaseChange

section BaseChangeFlat

variable {A : Type u} [CommRing A] (N : DerivedCategory (ModuleCat.{u} A))

/-- The derived base change of `N` along `φ : A → R` is a flat `R`-module in degree zero. -/
def BaseChangeFlat {R : Type u} [CommRing R] (φ : A →+* R) : Prop :=
  IsFlatInDegreeZero ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj N)

variable {N}

/-- If the derived base change of `N` along `φ` is a flat module in degree zero, so is its
derived base change along `ψ ∘ φ`. -/
lemma BaseChangeFlat.comp {R S : Type u} [CommRing R] [CommRing S] {φ : A →+* R}
    (h : BaseChangeFlat N φ) (ψ : R →+* S) : BaseChangeFlat N (ψ.comp φ) :=
  (h.baseChange ψ).of_iso ((totalDerivedExtensionScalarsComp.{u, u} φ ψ).app N)

/-- `BaseChangeFlat N φ` transported along an equality of ring maps. -/
lemma BaseChangeFlat.of_eq {R : Type u} [CommRing R] {φ φ' : A →+* R}
    (h : BaseChangeFlat N φ) (e : φ = φ') : BaseChangeFlat N φ' := e ▸ h

/-- If the derived base change of `N` along `ψ ∘ φ` is a flat module in degree zero for a ring
isomorphism `ψ`, so is its derived base change along `φ`. -/
lemma BaseChangeFlat.of_comp_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    {φ : A →+* R} (ψ : R ≃+* S) (h : BaseChangeFlat N (ψ.toRingHom.comp φ)) :
    BaseChangeFlat N φ :=
  (h.comp ψ.symm.toRingHom).of_eq (by ext; simp)

/-- The derived base change of `N` along the identity is a flat module in degree zero exactly
when `N` is. -/
lemma baseChangeFlat_id_iff : BaseChangeFlat N (RingHom.id A) ↔ IsFlatInDegreeZero N :=
  ⟨fun h => h.of_iso ((totalDerivedExtensionScalarsId.{u, u} A).app N).symm,
    fun h => h.of_iso ((totalDerivedExtensionScalarsId.{u, u} A).app N)⟩

/-- Every derived base change to the zero ring is a flat module in degree zero. -/
lemma baseChangeFlat_of_subsingleton {R : Type u} [CommRing R] [Subsingleton R]
    (φ : A →+* R) : BaseChangeFlat N φ :=
  isFlatInDegreeZero_of_subsingleton _

/-- If `N` has no cohomology in positive degrees, neither has any of its derived base changes. -/
lemma isLE_baseChange (hN : ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj N))
    {R : Type u} [CommRing R] (φ : A →+* R) (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj N)) := by
  have : N.IsLE 0 := (DerivedCategory.isLE_iff N 0).2 hN
  have := (totalDerivedExtensionScalars.{u, u, u} φ).maps_t_le N 0
  exact DerivedCategory.isZero_of_isLE _ 0 i hi

variable (N) in
/-- The derived base change of `N` along `φ : A → R` has no cohomology in positive degrees. -/
def BaseChangeLE {R : Type u} [CommRing R] (φ : A →+* R) : Prop :=
  ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
    ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj N))

/-- If the derived base change of `N` along `φ` has no positive cohomology, neither has its
derived base change along `ψ ∘ φ`. -/
lemma BaseChangeLE.comp {R S : Type u} [CommRing R] [CommRing S] {φ : A →+* R}
    (h : BaseChangeLE N φ) (ψ : R →+* S) : BaseChangeLE N (ψ.comp φ) := by
  intro i hi
  exact (isLE_baseChange h ψ i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).mapIso
      ((totalDerivedExtensionScalarsComp.{u, u} φ ψ).app N).symm)

/-- `BaseChangeLE N φ` transported along an equality of ring maps. -/
lemma BaseChangeLE.of_eq {R : Type u} [CommRing R] {φ φ' : A →+* R}
    (h : BaseChangeLE N φ) (e : φ = φ') : BaseChangeLE N φ' := e ▸ h

/-- If the derived base change of `N` along `ψ ∘ φ` has no positive cohomology for a ring
isomorphism `ψ`, neither has its derived base change along `φ`. -/
lemma BaseChangeLE.of_comp_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    {φ : A →+* R} (ψ : R ≃+* S) (h : BaseChangeLE N (ψ.toRingHom.comp φ)) :
    BaseChangeLE N φ :=
  (h.comp ψ.symm.toRingHom).of_eq (by ext; simp)

/-- The derived base change of `N` along the identity has no positive cohomology exactly when
`N` has none. -/
lemma baseChangeLE_id_iff : BaseChangeLE N (RingHom.id A) ↔
    ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj N) :=
  forall₂_congr fun i _ => Iso.isZero_iff
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      ((totalDerivedExtensionScalarsId.{u, u} A).app N).symm)

/-- **Stacks 0H85 for a derived base change.** Let `N ∈ D(A)` have no positive cohomology, let
`φ : A → R` be a ring map and `f ∈ R`. If the derived base changes of `N` to `R_f` and to `R/fR`
are flat modules in degree zero, so is its derived base change to `R`. -/
lemma BaseChangeFlat.of_away_of_quotient
    (hN : ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj N))
    {R : Type u} [CommRing R] (φ : A →+* R) (f : R)
    (hAway : BaseChangeFlat N ((algebraMap R (Localization.Away f)).comp φ))
    (hQuot : BaseChangeFlat N ((Ideal.Quotient.mk (Ideal.span {f})).comp φ)) :
    BaseChangeFlat N φ := by
  let K := (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj N
  exact
    Stacks.Flatness.LocalizationReduction.isomorphic_to_flat_module_of_localization_and_quotient
      f K
    (isLE_baseChange hN φ)
    (hAway.of_iso ((totalDerivedExtensionScalarsComp.{u, u} φ _).app N).symm)
    (hQuot.of_iso ((totalDerivedExtensionScalarsComp.{u, u} φ _).app N).symm)

/-- The condition descends along the quotient by a principal ideal generated by a nilpotent
element: the localization at that element is the zero ring. -/
lemma BaseChangeFlat.of_quotient_span_singleton
    (hN : ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj N))
    {R : Type u} [CommRing R] (φ : A →+* R) {x : R} (hx : IsNilpotent x)
    (h : BaseChangeFlat N ((Ideal.Quotient.mk (Ideal.span {x})).comp φ)) :
    BaseChangeFlat N φ := by
  refine BaseChangeFlat.of_away_of_quotient hN φ x ?_ h
  have : Subsingleton (Localization.Away x) :=
    IsLocalization.subsingleton ((Submonoid.mem_powers_iff 0 x).2 hx)
  exact baseChangeFlat_of_subsingleton _

/-- The condition descends along the quotient by an ideal generated by finitely many nilpotent
elements. -/
lemma BaseChangeFlat.of_quotient_span_range_of_isNilpotent
    (hN : ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj N)) :
    ∀ (n : ℕ) {R : Type u} [CommRing R] (φ : A →+* R) (s : Fin n → R),
      (∀ i, IsNilpotent (s i)) →
      BaseChangeFlat N ((Ideal.Quotient.mk (Ideal.span (Set.range s))).comp φ) →
      BaseChangeFlat N φ := by
  intro n
  induction n with
  | zero =>
    intro R _ φ s _ h
    have hbot : Ideal.span (Set.range s) = ⊥ := by simp [Set.range_eq_empty]
    let e := (Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot R)
    refine BaseChangeFlat.of_comp_ringEquiv e.symm (h.of_eq ?_)
    ext a
    apply e.injective
    simp [e]
  | succ n ih =>
    intro R _ φ s hs h
    let x := s 0
    let t : Fin n → R := fun i => s i.succ
    let π := Ideal.Quotient.mk (Ideal.span {x})
    refine BaseChangeFlat.of_quotient_span_singleton hN φ (hs 0) ?_
    refine ih (π.comp φ) (fun i => π (t i)) (fun i => (hs i.succ).map π) ?_
    have hsup : Ideal.span {x} ⊔ Ideal.span (Set.range t) = Ideal.span (Set.range s) := by
      rw [← Ideal.span_union, ← Set.insert_eq]
      congr 1
      ext y
      simp only [Set.mem_insert_iff, Set.mem_range]
      constructor
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨i.succ, rfl⟩
      · rintro ⟨i, rfl⟩
        refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
    have hmap : (Ideal.span (Set.range t)).map π = Ideal.span (Set.range fun i => π (t i)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    let e : (R ⧸ Ideal.span {x}) ⧸ Ideal.span (Set.range fun i => π (t i)) ≃+*
        R ⧸ Ideal.span (Set.range s) :=
      (Ideal.quotEquivOfEq hmap.symm).trans
        ((DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq hsup))
    refine BaseChangeFlat.of_comp_ringEquiv e (h.of_eq ?_)
    ext a
    show _ = (Ideal.quotEquivOfEq hsup) (DoubleQuot.quotQuotEquivQuotSup _ _
      (DoubleQuot.quotQuotMk (Ideal.span {x}) (Ideal.span (Set.range t)) (φ a)))
    rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk]
    simp

/-- **Descent along a nilpotent thickening.** The condition descends along the quotient by a
finitely generated ideal contained in the nilradical. -/
lemma BaseChangeFlat.of_quotient_of_le_nilradical
    (hN : ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj N))
    {R : Type u} [CommRing R] (φ : A →+* R) (I : Ideal R) (hfg : I.FG)
    (hnil : I ≤ nilradical R) (h : BaseChangeFlat N ((Ideal.Quotient.mk I).comp φ)) :
    BaseChangeFlat N φ := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  refine BaseChangeFlat.of_quotient_span_range_of_isNilpotent hN n φ s
    (fun i => hnil (hs ▸ Ideal.subset_span (Set.mem_range_self i))) ?_
  have hs' : Ideal.span (Set.range s) = I := hs
  exact (h.comp (Ideal.quotEquivOfEq hs'.symm).toRingHom).of_eq (by ext; simp)

end BaseChangeFlat

end StacksDraft.DerivedFlat

end
