module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationUniformInverse
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.ProZero
public import StacksFrontier.RingTheory.Module.AdicSystem.UniformDerivedReduction

/-!
# Derived base change of the quotients by the powers of an ideal

Let `P → A` be a finite ring map with `P` Noetherian and let `J ⊆ P` be an ideal. The inverse
system `A ⊗ᴸ_P P/Jⁿ` of derived base changes in `D(A)` is *strictly* pro-isomorphic to the system
`A ⊗_P P/Jⁿ`: the natural map from the derived to the underived base change has inverses over a
shift independent of `n`. This is system (4) in the proof of [Stacks, Tag 0GA5].

## Main definitions

* `Stacks.LocalCohomology.UniformityII.quotientSingleSystem`: the inverse system of complexes
  `n ↦ (P/Jⁿ⁺¹)[0]`.

## Main results

* `Stacks.LocalCohomology.UniformityII.hasUniformInverses_extensionCounit_quotientSingleSystem`:
  for any total left derived functor `B` of extension of scalars with counit `α`, the components
  `α : B((P/Jⁿ⁺¹)[0]) ⟶ (A ⊗_P P/Jⁿ⁺¹)[0]` have uniform inverses.

## Proof

Apply `DerivedCategory.hasUniformInverses_of_isLE_zero`. Its inputs are computed on projective
resolutions of the quotients `P/Jⁿ`, where the derived base change is degreewise base change:
* the transitions over a fixed number of steps kill everything in degrees `≤ -t-1`, because
  they lift to maps of resolutions vanishing in homological degrees above `t` by
  [Stacks, Tag 0GA3];
* in each negative degree `-p` they vanish on cohomology over a fixed number of steps, because
  that cohomology is `Tor_p^P(A, P/Jⁿ)` and these systems are strictly pro-zero for the finite
  `P`-module `A` by [Stacks, Tag 0911];
* on `H⁰` the counit is an isomorphism because extension of scalars is right exact.

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
* [Stacks Project, Tag 0GA3](https://stacks.math.columbia.edu/tag/0GA3)
* [Stacks Project, Tag 0911](https://stacks.math.columbia.edu/tag/0911)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.InverseSequence
  CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.LocalCohomology.UniformityII

universe u

section General

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- A right exact functor applied degreewise to a quasi-isomorphism from a complex in degrees
`≤ 0` onto an object in degree `0` is still an isomorphism on `H⁰`. -/
theorem quasiIsoAt_zero_map_of_isStrictlyLE (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {K : CochainComplex C ℤ} [K.IsStrictlyLE 0] {X : C}
    (π : K ⟶ (CochainComplex.singleFunctor C 0).obj X) [QuasiIsoAt π 0] :
    QuasiIsoAt ((F.mapHomologicalComplex _).map π) 0 := by
  have hπ : ShortComplex.QuasiIso ((HomologicalComplex.shortComplexFunctor C _ 0).map π) :=
    (quasiIsoAt_iff π 0).1 inferInstance
  have hK : K.d 0 ((ComplexShape.up ℤ).next 0) = 0 :=
    (K.isZero_of_isStrictlyLE 0 _ (by simp)).eq_of_tgt _ _
  rw [ShortComplex.quasiIso_iff_of_zeros' _ hK rfl rfl] at hπ
  obtain ⟨hex, hepi⟩ := hπ
  rw [quasiIsoAt_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros' _ (by
    show F.map (K.d 0 _) = 0
    rw [hK, F.map_zero]) (F.map_zero _ _) (F.map_zero _ _)]
  have : Epi (π.f 0) := hepi
  exact ⟨hex.map_of_epi_of_preservesCokernel F hepi inferInstance, F.map_epi _⟩

/-- Applying a functor degreewise preserves the vanishing of terms above a degree. -/
theorem isStrictlyLE_map_obj (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) (b : ℤ)
    [K.IsStrictlyLE b] : CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex _).obj K) b := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi ↦ F.map_isZero (K.isZero_of_isStrictlyLE b i hi)

/-- Applying a functor degreewise preserves the vanishing of terms below a degree. -/
theorem isStrictlyGE_map_obj (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyGE a] : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex _).obj K) a := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi ↦ F.map_isZero (K.isZero_of_isStrictlyGE a i hi)

end General

variable {P A : Type u} [CommRing P] [CommRing A] (f : P →+* A)

/-- `A`, viewed as a `P`-module through `f`: the left factor of the extension of scalars. -/
noncomputable abbrev restrictedRing : ModuleCat.{u} P :=
  (ModuleCat.restrictScalars f).obj (ModuleCat.of A A)

/-- A finite ring map makes the target a finite module. -/
theorem finite_restrictedRing (hf : f.Finite) : Module.Finite P (restrictedRing f) := by
  let := f.toAlgebra
  have : Module.Finite P A := hf
  exact Module.Finite.equiv (LinearEquiv.refl P A)

/-- Extension of scalars and tensoring with `restrictedRing f` agree elementwise. -/
theorem extendScalars_map_apply {M N : ModuleCat.{u} P} (g : M ⟶ N)
    (x : (ModuleCat.extendScalars.{u, u, u} f).obj M) :
    ((ModuleCat.extendScalars.{u, u, u} f).map g).hom x =
      ((tensorLeft (restrictedRing f)).map g).hom x := by
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a m => rfl
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

/-- Vanishing on homology passes from tensoring with `restrictedRing f` to extension of
scalars, for chain complexes. -/
theorem homologyMap_extendScalars_eq_zero {K L : ChainComplex (ModuleCat.{u} P) ℕ} (φ : K ⟶ L)
    (p : ℕ) (h : HomologicalComplex.homologyMap
      (((tensorLeft (restrictedRing f)).mapHomologicalComplex _).map φ) p = 0) :
    HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex _).map φ) p = 0 := by
  apply ShortComplex.homologyMap_eq_zero_of_mem_range
  intro x hx
  have hx' : ((tensorLeft (restrictedRing f)).map (K.d p ((ComplexShape.down ℕ).next p))).hom x
      = 0 := (extendScalars_map_apply f _ x).symm.trans hx
  obtain ⟨y, hy⟩ := NoetherianKoszulProIso.moduleCat_mem_range_d_of_homologyMap_eq_zero _ p h hx'
  exact ⟨y, (extendScalars_map_apply f _ y).trans (hy.trans (extendScalars_map_apply f _ x).symm)⟩

/-- The cochain lift, to the chosen projective resolutions, of a map of modules. -/
noncomputable def resolutionLift {X Y : ModuleCat.{u} P} (β : X ⟶ Y) :
    (ProjectiveResolution.of X).cochainComplex ⟶ (ProjectiveResolution.of Y).cochainComplex :=
  HomologicalComplex.extendMap (ProjectiveResolution.lift β _ _) ComplexShape.embeddingDownNat

/-- `resolutionLift β` lies over `β` through the augmentations of the resolutions. -/
theorem resolutionLift_comm {X Y : ModuleCat.{u} P} (β : X ⟶ Y) :
    resolutionLift β ≫ (ProjectiveResolution.of Y).π' =
      (ProjectiveResolution.of X).π' ≫ (CochainComplex.singleFunctor _ 0).map β := by
  let φ : ProjectiveResolution.Hom (ProjectiveResolution.of X) (ProjectiveResolution.of Y) β :=
    { hom := ProjectiveResolution.lift β _ _
      hom_f_zero_comp_π_f_zero := by
        simpa using ProjectiveResolution.lift_commutes_zero β
          (ProjectiveResolution.of X) (ProjectiveResolution.of Y) }
  exact φ.hom'_comp_π'

/-- **`Tor` computes the cohomology of degreewise extension of scalars.** If `β` induces the
zero map on `Tor_p^P(A, -)`, then its lift to the chosen projective resolutions, extended along
`P → A` degreewise, vanishes on `H^{-p}`. -/
theorem homologyMap_extendScalarsLarge_resolutionLift_eq_zero {X Y : ModuleCat.{u} P}
    (β : X ⟶ Y) (p : ℕ) (hβ : ((Tor (ModuleCat.{u} P) p).obj (restrictedRing f)).map β = 0) :
    HomologicalComplex.homologyMap
      ((CochainComplex.extendScalarsLarge.{u, u, u} f).map (resolutionLift β)) (-(p : ℤ)) = 0 := by
  let R := ProjectiveResolution.of X
  let R' := ProjectiveResolution.of Y
  let φ := ProjectiveResolution.lift β R R'
  have comm : φ.f 0 ≫ R'.π.f 0 = R.π.f 0 ≫ β := ProjectiveResolution.lift_commutes_zero β R R'
  let F := tensorLeft (restrictedRing f)
  have h₁ : HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) p = 0 := by
    have hn := ProjectiveResolution.isoLeftDerivedObj_hom_naturality β R R' φ comm F p
    change (F.leftDerived p).map β = 0 at hβ
    rw [hβ, zero_comp] at hn
    exact (cancel_epi (R.isoLeftDerivedObj F p).hom).1 (hn.symm.trans comp_zero.symm)
  have h₂ := homologyMap_extendScalars_eq_zero f φ p h₁
  let G := ModuleCat.extendScalars.{u, u, u} f
  have he : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
  have h₃ : HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap ((G.mapHomologicalComplex _).map φ)
        ComplexShape.embeddingDownNat) (-(p : ℤ)) = 0 := by
    have hn := HomologicalComplex.extendHomologyIso_hom_naturality
      ((G.mapHomologicalComplex _).map φ) ComplexShape.embeddingDownNat he
    rw [h₂, comp_zero] at hn
    exact (cancel_mono _).1 (hn.trans (zero_comp).symm)
  have hn := HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality G R.complex φ
    ComplexShape.embeddingDownNat
  have h₄ := congrArg (fun g => HomologicalComplex.homologyMap g (-(p : ℤ))) hn
  simp only [HomologicalComplex.homologyMap_comp, h₃, comp_zero] at h₄
  show HomologicalComplex.homologyMap ((G.mapHomologicalComplex _).map (resolutionLift β))
    (-(p : ℤ)) = 0
  exact (cancel_mono (HomologicalComplex.homologyMapIso
    (HomologicalComplex.mapHomologicalComplexExtendIso G R'.complex
      ComplexShape.embeddingDownNat).symm (-(p : ℤ))).hom).1 (h₄.trans zero_comp.symm)

/-! ### The system of quotients -/

/-- The inverse system of modules `n ↦ P/Jⁿ⁺¹`, with the canonical surjections as transition
maps. -/
noncomputable def quotientModuleSystem (J : Ideal P) : ℕᵒᵖ ⥤ ModuleCat.{u} P :=
  Functor.ofOpSequence (X := fun n ↦ torProZeroQuot J (n + 1))
    (fun n ↦ torProZeroTransition J (Nat.le_succ (n + 1)))

/-- The transition maps of `quotientModuleSystem J` are the canonical surjections. -/
theorem quotientModuleSystem_map (J : Ideal P) {n m : ℕ} (h : n ≤ m) :
    (quotientModuleSystem J).map (homOfLE h).op =
      torProZeroTransition J (Nat.add_le_add_right h 1) := by
  refine NoetherianAdicCompletion.ofOpSequence_map_eq _
    (fun m n h ↦ torProZeroTransition J (Nat.add_le_add_right h 1)) (fun n ↦ ?_)
    (fun m n h ↦ ?_) m n h
  · exact torProZeroTransition_refl J _
  · exact (torProZeroTransition_comp J _ _).symm

/-- The inverse system of complexes `n ↦ (P/Jⁿ⁺¹)[0]`. -/
noncomputable abbrev quotientSingleSystem (J : Ideal P) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} P) ℤ :=
  quotientModuleSystem J ⋙ CochainComplex.singleFunctor (ModuleCat.{u} P) 0

/-- The transition maps of `quotientSingleSystem J` are the canonical surjections in degree
`0`. -/
theorem quotientSingleSystem_map (J : Ideal P) {n m : ℕ} (h : n ≤ m) :
    (quotientSingleSystem J).map (homOfLE h).op =
      (CochainComplex.singleFunctor _ 0).map
        (torProZeroTransition J (Nat.add_le_add_right h 1)) := by
  rw [Functor.comp_map, quotientModuleSystem_map]
  rfl

/-! ### The counit on a quotient, computed on resolutions -/

section Counit

variable (B : DerivedCategory (ModuleCat.{u} P) ⥤ DerivedCategory (ModuleCat.{u} A))
  (α : DerivedCategory.Q ⋙ B ⟶ CochainComplex.extendScalarsLarge.{u, u, u} f ⋙ DerivedCategory.Q)
  [B.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} P) (ComplexShape.up ℤ))]

include α in
/-- The counit `α` is an isomorphism on the chosen projective resolution of a module. -/
theorem isIso_counit_resolution (X : ModuleCat.{u} P) :
    IsIso (α.app (ProjectiveResolution.of X).cochainComplex) :=
  CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat f B α _
    (CochainComplex.KFlat.kFlat_projectiveResolution _)

/-- The derived base change of a map of modules, read through the chosen resolutions. -/
theorem map_single_eq {X Y : ModuleCat.{u} P} (β : X ⟶ Y)
    (l : (ProjectiveResolution.of X).cochainComplex ⟶ (ProjectiveResolution.of Y).cochainComplex)
    (hl : l ≫ (ProjectiveResolution.of Y).π' =
      (ProjectiveResolution.of X).π' ≫ (CochainComplex.singleFunctor _ 0).map β) :
    haveI := isIso_counit_resolution f B α X
    haveI := isIso_counit_resolution f B α Y
    B.map (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map β)) =
      inv (B.map (DerivedCategory.Q.map (ProjectiveResolution.of X).π')) ≫
        α.app (ProjectiveResolution.of X).cochainComplex ≫
          DerivedCategory.Q.map ((CochainComplex.extendScalarsLarge.{u, u, u} f).map l) ≫
            inv (α.app (ProjectiveResolution.of Y).cochainComplex) ≫
              B.map (DerivedCategory.Q.map (ProjectiveResolution.of Y).π') := by
  have := isIso_counit_resolution f B α X
  have := isIso_counit_resolution f B α Y
  have hnat := α.naturality l
  simp only [Functor.comp_map] at hnat
  have h₁ : B.map (DerivedCategory.Q.map l) =
      α.app (ProjectiveResolution.of X).cochainComplex ≫
        DerivedCategory.Q.map ((CochainComplex.extendScalarsLarge.{u, u, u} f).map l) ≫
          inv (α.app (ProjectiveResolution.of Y).cochainComplex) := by
    rw [← reassoc_of% hnat, IsIso.hom_inv_id, Category.comp_id]
  rw [← reassoc_of% h₁, IsIso.eq_inv_comp, ← Functor.map_comp, ← Functor.map_comp, ← hl,
    Functor.map_comp, Functor.map_comp]

end Counit

/-! ### The main theorem -/

open DerivedCategory in
/-- **The derived base change of the quotients by the powers of an ideal is strictly
pro-isomorphic to the underived one.** Let `f : P → A` be a finite ring map with `P`
Noetherian and `J ⊆ P` an ideal, and let `B` be a total left derived functor of extension of
scalars along `f` with counit `α`. Then the components
`α : B((P/Jⁿ⁺¹)[0]) ⟶ (A ⊗_P P/Jⁿ⁺¹)[0]` form a morphism of inverse systems in `D(A)` with
uniform inverses. -/
theorem hasUniformInverses_extensionCounit_quotientSingleSystem [IsNoetherianRing P]
    (hf : f.Finite) (J : Ideal P)
    (B : DerivedCategory (ModuleCat.{u} P) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ B ⟶ CochainComplex.extendScalarsLarge.{u, u, u} f ⋙ DerivedCategory.Q)
    [B.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} P) (ComplexShape.up ℤ))] :
    HasUniformInverses (Functor.whiskerLeft (quotientSingleSystem J) α) := by
  classical
  let S := quotientSingleSystem J
  let E := CochainComplex.extendScalarsLarge.{u, u, u} f
  let G := ModuleCat.extendScalars.{u, u, u} f
  have hE : ∀ K : CochainComplex (ModuleCat.{u} P) ℤ, E.obj K = (G.mapHomologicalComplex _).obj K :=
    fun _ ↦ rfl
  have hZ : ∀ n : ℕᵒᵖ, ((S ⋙ Q ⋙ B).obj n).IsLE 0 := by
    intro n
    let R := ProjectiveResolution.of (torProZeroQuot J (n.unop + 1))
    have := isIso_counit_resolution f B α (torProZeroQuot J (n.unop + 1))
    let e : (S ⋙ Q ⋙ B).obj n ≅ Q.obj (E.obj R.cochainComplex) :=
      (B.mapIso (asIso (Q.map R.π'))).symm ≪≫ asIso (α.app R.cochainComplex)
    have : CochainComplex.IsStrictlyLE (E.obj R.cochainComplex) 0 :=
      isStrictlyLE_map_obj G R.cochainComplex 0
    exact TStructure.t.isLE_of_iso e.symm 0
  have hW : ∀ n : ℕᵒᵖ, ((S ⋙ E ⋙ Q).obj n).IsGE 0 ∧ ((S ⋙ E ⋙ Q).obj n).IsLE 0 := by
    intro n
    let K : CochainComplex (ModuleCat.{u} P) ℤ :=
      (CochainComplex.singleFunctor _ 0).obj (torProZeroQuot J (n.unop + 1))
    have := isStrictlyGE_map_obj G K 0
    have := isStrictlyLE_map_obj G K 0
    show (Q.obj ((G.mapHomologicalComplex _).obj K)).IsGE 0 ∧
      (Q.obj ((G.mapHomologicalComplex _).obj K)).IsLE 0
    exact ⟨inferInstance, inferInstance⟩
  have hφ : ∀ n : ℕᵒᵖ, IsIso ((homologyFunctor (ModuleCat.{u} A) 0).map
      ((Functor.whiskerLeft S α).app n)) := by
    intro n
    let X := torProZeroQuot J (n.unop + 1)
    let R := ProjectiveResolution.of X
    have := isIso_counit_resolution f B α X
    have hnat := α.naturality R.π'
    simp only [Functor.comp_map] at hnat
    have hα : α.app ((CochainComplex.singleFunctor _ 0).obj X) =
        inv (B.map (Q.map R.π')) ≫ α.app R.cochainComplex ≫ Q.map (E.map R.π') := by
      rw [IsIso.eq_inv_comp, ← hnat]
    have hq : QuasiIsoAt ((G.mapHomologicalComplex _).map R.π') 0 :=
      quasiIsoAt_zero_map_of_isStrictlyLE G R.π'
    have h₀ : IsIso ((homologyFunctor (ModuleCat.{u} A) 0).map (Q.map (E.map R.π'))) :=
      (NatIso.isIso_map_iff (homologyFunctorFactors (ModuleCat.{u} A) 0) _).2
        ((quasiIsoAt_iff_isIso_homologyMap _ 0).1 hq)
    show IsIso ((homologyFunctor (ModuleCat.{u} A) 0).map
      (α.app ((CochainComplex.singleFunctor _ 0).obj X)))
    rw [hα, Functor.map_comp, Functor.map_comp]
    infer_instance
  have hS : ∀ {n m : ℕ} (h : n ≤ m), tr (S ⋙ Q ⋙ B) h =
      B.map (Q.map ((CochainComplex.singleFunctor _ 0).map
        (torProZeroTransition J (Nat.add_le_add_right h 1)))) := by
    intro n m h
    show B.map (Q.map (S.map (homOfLE h).op)) = _
    rw [quotientSingleSystem_map]
    rfl
  obtain ⟨t, gens, hgens⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  obtain ⟨N, c, hNc⟩ := exists_uniform_hasLiftVanishingAbove_quotientFactor gens hgens.symm
  refine hasUniformInverses_of_isLE_zero (Functor.whiskerLeft S α) hZ (fun n ↦ (hW n).1)
    (fun n ↦ (hW n).2) hφ (-(t : ℤ) - 1) (by omega)
    ⟨N + c, fun n m h hm V hV g => ?_⟩ (fun d hd₁ hd₂ => ?_)
  · let X := ModuleCat.of P (P ⧸ J ^ (m + 1))
    let Y := ModuleCat.of P (P ⧸ J ^ (m + 1 - c))
    let R := ProjectiveResolution.of X
    let R' := ProjectiveResolution.of Y
    have := isProjectiveResolution_π' R
    have := isProjectiveResolution_π' R'
    obtain ⟨a, ha, hz⟩ := hNc (m + 1) (by omega) R.π' R'.π'
    let β : X ⟶ Y := torProZeroTransition J (Nat.sub_le (m + 1) c)
    let β' : Y ⟶ torProZeroQuot J (n + 1) :=
      torProZeroTransition J (show n + 1 ≤ m + 1 - c by omega)
    have hsplit : torProZeroTransition J (Nat.add_le_add_right h 1) = β ≫ β' :=
      (torProZeroTransition_comp J _ _).symm
    have := isIso_counit_resolution f B α X
    have := isIso_counit_resolution f B α Y
    have hβ := map_single_eq f B α β a ha
    have hzero : ∀ i : ℤ, i ≤ -(t : ℤ) - 1 → (E.map a).f i = 0 := by
      intro i hi
      have h₁ := hz (-i).toNat (by omega)
      rw [show (-(((-i).toNat : ℕ) : ℤ)) = i by omega] at h₁
      show G.map (a.f i) = 0
      rw [h₁, G.map_zero]
    let g' : V ⟶ B.obj (Q.obj ((CochainComplex.singleFunctor _ 0).obj X)) := g
    have h₀ : (g' ≫ inv (B.map (Q.map R.π')) ≫ α.app R.cochainComplex) ≫ Q.map (E.map a) = 0 :=
      DerivedCategory.comp_Q_map_eq_zero_of_f_eq_zero _ _ hzero V hV _
    rw [hS, hsplit]
    show g' ≫ B.map (Q.map ((CochainComplex.singleFunctor _ 0).map (β ≫ β'))) = 0
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, hβ]
    simp only [Category.assoc] at h₀ ⊢
    rw [reassoc_of% h₀, zero_comp]
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, d = -(p : ℤ) := ⟨(-d).toNat, by omega⟩
    have hp : 0 < p := by omega
    have := finite_restrictedRing f hf
    obtain ⟨c', -, hc'⟩ := tor_pro_zero J (restrictedRing f) hp
    refine ⟨c', fun n => ?_⟩
    have key : ∀ (k : ℕ) (hk : k - c' ≤ k) (hk' : n + 1 ≤ k), k - c' = n + 1 →
        ((Tor (ModuleCat.{u} P) p).obj (restrictedRing f)).map (torProZeroTransition J hk) = 0 →
        ((Tor (ModuleCat.{u} P) p).obj (restrictedRing f)).map
          (torProZeroTransition J hk') = 0 := by
      intro k hk hk' e H
      revert hk H
      rw [e]
      exact fun _ H => H
    let β := torProZeroTransition J (Nat.add_le_add_right (Nat.le_add_right n c') 1)
    have hTor : ((Tor (ModuleCat.{u} P) p).obj (restrictedRing f)).map β = 0 :=
      key (n + c' + 1) (Nat.sub_le _ c') _ (by omega) (hc' (n + c' + 1) (by omega))
    have hl := homologyMap_extendScalarsLarge_resolutionLift_eq_zero f β p hTor
    have := isIso_counit_resolution f B α (torProZeroQuot J (n + c' + 1))
    have := isIso_counit_resolution f B α (torProZeroQuot J (n + 1))
    rw [hS]
    show (homologyFunctor (ModuleCat.{u} A) (-(p : ℤ))).map
      (B.map (Q.map ((CochainComplex.singleFunctor _ 0).map β))) = 0
    rw [map_single_eq f B α β (resolutionLift β) (resolutionLift_comm β)]
    simp only [Functor.map_comp]
    rw [DerivedCategory.homologyFunctor_map_Q_map_eq_zero _ _ hl, zero_comp, comp_zero,
      comp_zero]

end Stacks.LocalCohomology.UniformityII

end
