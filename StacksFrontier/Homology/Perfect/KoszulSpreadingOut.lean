module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Perfect.BaseChange
public import StacksFrontier.Homology.Perfect.Colimit
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.Koszul.Defs
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Localization.AwayCocone
public import StacksFrontier.RingTheory.SpreadingOut.RegularSequence
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Spreading a Koszul description of a perfect complex out from a local ring

Let `R → S` be a flat map of finite type between Noetherian rings and let `q` be a prime of `S`.
Suppose a perfect object of the derived category of `S`-modules becomes, after derived base
change to the local ring `S_q`, the Koszul complex of a regular sequence whose quotient is flat
over `R`. Then the whole description — the sequence, its regularity, the flatness of its
quotient and the identification of the complex — already holds over a principal localization
`S_g` for some `g ∉ q`.

## Main results

* `StacksDraft.Perfect.exists_away_koszul_description` is the statement above.
* `Koszul.nonempty_seqComplex_extendScalars_iso`: extension of scalars carries the Koszul
  complex of a sequence to the Koszul complex of its image.
* `StacksDraft.Perfect.nonempty_koszul_derived_baseChange_iso`: the derived form of the previous
  item, after placing the Koszul complex in cohomological degrees.

## Implementation notes

Koszul complexes are indexed by `ℕ` and homological; `extend ComplexShape.embeddingDownNat`
places them in the cohomological degrees `-r, …, 0` before passing to the derived category. Their
terms are finite free, so the extended complex is a bounded complex of finite projectives, which
is what makes it perfect and what makes the comparison map of the derived extension of scalars
an isomorphism on it.

The local ring `S_q` is the filtered colimit of the principal localizations `S_g` for
`g ∉ q` (`Localization.isColimitAwayCocone`), and a perfect complex has only finitely much
information, so an isomorphism over `S_q` is already realized over some `S_g`: this is
`StacksDraft.Perfect.exists_stage_iso`, which feeds the two-sided colimit description of
morphisms between base changes of perfect complexes.

Uniqueness of the comparison between the two iterated derived base changes is needed to identify
the composites appearing on either side; it is proved by testing on K-flat representatives, where
the comparison maps are isomorphisms.

## References

* [Stacks Project, Tag 0G0P](https://stacks.math.columbia.edu/tag/0G0P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u uI

open scoped TensorProduct

namespace Koszul

/-- Extension of scalars along a ring map `q : A →+* B` carries the Koszul complex of a sequence
in `A` to the Koszul complex of its image in `B`: exterior powers of a finite free module commute
with base change, naturally enough to match the contraction differentials. -/
theorem nonempty_seqComplex_extendScalars_iso {A B : Type u} [CommRing A] [CommRing B]
    (q : A →+* B) {r : ℕ} (f : Fin r → A) :
    Nonempty
      (((ModuleCat.extendScalars q).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (Koszul.seqComplex f) ≅
        Koszul.seqComplex fun j => q (f j)) := by
  let : Algebra A B := q.toAlgebra
  let F := ModuleCat.extendScalars q
  choose β hβ using fun n => KoszulC.extPow_baseChange_natEquiv (R := A) (S := B) (r := r) n
  refine ⟨HomologicalComplex.Hom.isoOfComponents
    (fun n => by
      let e₀ : (F.obj (ModuleCat.of A (⋀[A]^n (Fin r → A))) : Type u) ≃ₗ[B]
          (B ⊗[A] (⋀[A]^n (Fin r → A))) :=
        { toFun := id
          invFun := id
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact (e₀.trans (β n)).toModuleIso) ?_⟩
  intro i j hij
  obtain rfl : j + 1 = i := hij
  simp only [Functor.mapHomologicalComplex_obj_d, Koszul.seqComplex_d]
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  change Koszul.d (Koszul.seqDual fun k => q (f k)) j (β (j + 1) (1 ⊗ₜ[A] z)) =
    β j (1 ⊗ₜ[A] Koszul.d (Koszul.seqDual f) j z)
  exact (KoszulC.d_baseChange_comm f β hβ j z).symm

/-- Every term of the Koszul complex placed in cohomological degrees is projective: it is either
zero or a finite exterior power of a finite free module. -/
theorem projective_extend_seqComplex_X {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (i : ℤ) :
    Projective (((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat).X i) := by
  classical
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i
  · obtain ⟨j, hj⟩ := h
    have hPJ : Projective ((Koszul.seqComplex f).X j) := by
      change Projective (ModuleCat.of A (⋀[A]^j (Fin r → A)))
      have : Module.Projective A (⋀[A]^j (Fin r → A)) :=
        Module.Projective.of_basis (Module.Free.chooseBasis _ _)
      infer_instance
    exact Projective.of_iso
      ((Koszul.seqComplex f).extendXIso ComplexShape.embeddingDownNat hj).symm hPJ
  · exact ((Koszul.seqComplex f).isZero_extend_X ComplexShape.embeddingDownNat i
      (by simpa using h)).projective

end Koszul

namespace StacksDraft.Perfect

/-- The terms of the Koszul complex placed in cohomological degrees vanish outside `-r, …, 0`. -/
private theorem isZero_extend_seqComplex_X {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (i : ℤ) (hi : i < -(r : ℤ) ∨ 0 < i) :
    IsZero (((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat).X i) := by
  by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i
  · obtain ⟨j, hj⟩ := h
    have hr : r < j := by
      change -(j : ℤ) = i at hj
      rcases hi with hi | hi <;> omega
    exact (Koszul.seqComplex_isZero_of_lt f j hr).of_iso
      ((Koszul.seqComplex f).extendXIso ComplexShape.embeddingDownNat hj)
  · exact (Koszul.seqComplex f).isZero_extend_X ComplexShape.embeddingDownNat i
      (by simpa using h)

/-- The Koszul complex of a sequence of length `r`, placed in the cohomological degrees
`-r, …, 0`, is a perfect object of the derived category: it is a bounded complex of finite
projective modules. -/
theorem isPerfect_extend_koszul {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj
        ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat)) := by
  classical
  let P : CochainComplex (ModuleCat.{u} A) ℤ :=
    (Koszul.seqComplex f).extend ComplexShape.embeddingDownNat
  have hge : P.IsStrictlyGE (-(r : ℤ)) :=
    (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => isZero_extend_seqComplex_X f i (Or.inl hi)
  have hle : P.IsStrictlyLE 0 :=
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => isZero_extend_seqComplex_X f i (Or.inr hi)
  have hfin (i : ℤ) : Module.Finite A (P.X i) := by
    by_cases h : ∃ j : ℕ, ComplexShape.embeddingDownNat.f j = i
    · obtain ⟨j, hj⟩ := h
      have hF : Module.Finite A ((Koszul.seqComplex f).X j) := by
        change Module.Finite A (⋀[A]^j (Fin r → A))
        infer_instance
      exact Module.Finite.equiv
        (((Koszul.seqComplex f).extendXIso ComplexShape.embeddingDownNat
          hj).toLinearEquiv.symm)
    · let : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.mp
        ((Koszul.seqComplex f).isZero_extend_X ComplexShape.embeddingDownNat i
          (by simpa using h))
      exact Module.Finite.of_finite
  have hproj (i : ℤ) : Module.Projective A (P.X i) := by
    let : Projective (P.X i) := Koszul.projective_extend_seqComplex_X f i
    exact ModuleCat.projective_of_module_projective (P.X i)
  exact ⟨P, -(r : ℤ), 0, hge, hle, hfin, hproj, ⟨Iso.refl _⟩⟩

/-- Derived base change along `A → B` carries the Koszul complex of a sequence to the Koszul
complex of its image: the complex has projective terms, so the comparison map of the derived
extension of scalars is an isomorphism on it, and the chain-level base-change isomorphism of
`Koszul.nonempty_seqComplex_extendScalars_iso` finishes. -/
theorem nonempty_koszul_derived_baseChange_iso {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {r : ℕ} (f : Fin r → A) :
    Nonempty
      ((derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A B)).functor.obj
        (DerivedCategory.Q.obj
          ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat)) ≅
        DerivedCategory.Q.obj
          ((Koszul.seqComplex fun i => algebraMap A B (f i)).extend
            ComplexShape.embeddingDownNat)) := by
  classical
  let P : CochainComplex (ModuleCat.{u} A) ℤ :=
    (Koszul.seqComplex f).extend ComplexShape.embeddingDownNat
  have hle : P.IsStrictlyLE 0 :=
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => isZero_extend_seqComplex_X f i (Or.inr hi)
  let (i : ℤ) : Projective (P.X i) := Koszul.projective_extend_seqComplex_X f i
  let D := derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A B)
  have hc : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P 0
  let F := ModuleCat.extendScalars (algebraMap A B)
  let e₁ := F.mapExtendIso (Koszul.seqComplex f) ComplexShape.embeddingDownNat
  obtain ⟨e₂⟩ := Koszul.nonempty_seqComplex_extendScalars_iso (algebraMap A B) f
  exact ⟨asIso (D.comparison.app P) ≪≫
    DerivedCategory.Q.mapIso
      (e₁ ≪≫ (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)).mapIso e₂)⟩

/-- Two natural transformations agree at an object as soon as they agree at an isomorphic one. -/
private theorem natTrans_app_eq_of_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α β : F ⟶ G) {X Y : C} (e : X ≅ Y) (h : α.app Y = β.app Y) :
    α.app X = β.app X := by
  apply (cancel_mono (G.map e.hom)).1
  rw [← α.naturality, ← β.naturality, h]

/-- The comparison of the two iterated derived base changes is unique: two natural isomorphisms
compatible with the chain-level comparison maps agree, because they agree on K-flat
representatives, where those comparison maps are isomorphisms. -/
private theorem derivedComp_eq_of_comparison {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C)
    (η θ : (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} g).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor)
    (hη : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ,
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (StacksDraft.Perfect.extensionOfScalarsComplexComp.{u} f g).inv.app P =
      η.hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P)
    (hθ : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ,
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (StacksDraft.Perfect.extensionOfScalarsComplexComp.{u} f g).inv.app P =
      θ.hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P) :
    η = θ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  obtain ⟨P, hP, ⟨e⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative X
  have hc : IsIso ((totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P) :=
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison_isIso_of_kFlat P hP
  have hP : η.hom.app (DerivedCategory.Q.obj P) = θ.hom.app (DerivedCategory.Q.obj P) := by
    apply (cancel_mono
      ((totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P)).1
    exact (hη P).symm.trans (hθ P)
  exact natTrans_app_eq_of_iso η.hom θ.hom e.symm hP

/-- Transition maps of a diagram of rings under `i₀` are compatible with the structure maps. -/
private theorem transition_comp_eq {I : Type uI} [Category.{uI} I] (T : I ⥤ CommRingCat.{u})
    {i₀ : I} {j k : Under i₀} (w : j ⟶ k) :
    (T.map w.right).hom.comp (T.map j.hom).hom = (T.map k.hom).hom := by
  rw [← CommRingCat.hom_comp, ← T.map_comp, Under.w]

/-- An endomorphism of a base change of a perfect complex which becomes the identity over the
colimit ring becomes the identity over some later stage, and then over all stages above it. -/
private theorem exists_stage_map_eq_id {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (T : I ⥤ CommRingCat.{u}) [PreservesColimit T (forget CommRingCat.{u})]
    (c : Cocone T) (hc : IsColimit c) (i₀ : I) (K : DerivedCategory (ModuleCat.{u} (T.obj i₀)))
    (hK : StacksDraft.Perfect.IsPerfect K)
    (comp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} g).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor)
    (hcomp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
      (P : CochainComplex (ModuleCat.{u} A) ℤ),
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (StacksDraft.Perfect.extensionOfScalarsComplexComp.{u} f g).inv.app P =
      (comp f g).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P)
    (l : Under i₀)
    (α : (totalDerivedExtensionScalars.{u, u, u} (T.map l.hom).hom).functor.obj K ⟶
      (totalDerivedExtensionScalars.{u, u, u} (T.map l.hom).hom).functor.obj K)
    (hα : let E := fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) =>
        totalDerivedExtensionScalars.{u, u, u} f
      let lc := comp (T.map l.hom).hom (c.ι.app l.right).hom ≪≫
        StacksDraft.Perfect.derivedExtensionScalarsCongr E
          (congrArg CommRingCat.Hom.hom (c.w l.hom))
      lc.inv.app K ≫ (E (c.ι.app l.right).hom).functor.map α ≫ lc.hom.app K = 𝟙 _) :
    ∃ (m : Under i₀) (w : l ⟶ m), ∀ (n : Under i₀) (v : m ⟶ n),
      (totalDerivedExtensionScalars.{u, u, u} (T.map (w ≫ v).right).hom).functor.map α = 𝟙 _ := by
  obtain ⟨comp', hcomp', H, eH, s, eT, hs, htrans, hleg⟩ :=
    (StacksDraft.Perfect.perfectComplexes_filteredColimit.{uI, u} T c hc).2 i₀ K K hK
  have hcompEq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C) : comp' f g = comp f g :=
    derivedComp_eq_of_comparison f g _ _ (hcomp' f g) (hcomp f g)
  let E := fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) =>
    totalDerivedExtensionScalars.{u, u, u} f
  let fₗ := (T.map l.hom).hom
  let gₗ := (c.ι.app l.right).hom
  have hₗ : gₗ.comp fₗ = (c.ι.app i₀).hom := congrArg CommRingCat.Hom.hom (c.w l.hom)
  let lc := comp fₗ gₗ ≪≫ StacksDraft.Perfect.derivedExtensionScalarsCongr E hₗ
  change lc.inv.app K ≫ (E gₗ).functor.map α ≫ lc.hom.app K = 𝟙 _ at hα
  have hlegα := hleg l α
  have hlegId := hleg l (𝟙 ((E fₗ).functor.obj K))
  rw [hcompEq fₗ gₗ] at hlegα hlegId
  change eT (s.ι.app l ((eH l).symm α)) =
    lc.inv.app K ≫ (E gₗ).functor.map α ≫ lc.hom.app K at hlegα
  change eT (s.ι.app l ((eH l).symm (𝟙 ((E fₗ).functor.obj K)))) =
    lc.inv.app K ≫ (E gₗ).functor.map (𝟙 ((E fₗ).functor.obj K)) ≫ lc.hom.app K at hlegId
  have hcolEq : s.ι.app l ((eH l).symm α) = s.ι.app l ((eH l).symm (𝟙 ((E fₗ).functor.obj K))) := by
    apply eT.injective
    rw [hlegα, hlegId, hα, (E gₗ).functor.map_id]
    exact (Iso.inv_hom_id_app lc K).symm.trans
      (congrArg (lc.inv.app K ≫ ·) (Category.id_comp _)).symm
  obtain ⟨m, w, hw⟩ := (Types.FilteredColimit.isColimit_eq_iff' hs _ _).mp hcolEq
  refine ⟨m, w, fun n v => ?_⟩
  have hn : H.map (w ≫ v) ((eH l).symm α) = H.map (w ≫ v) ((eH l).symm (𝟙 _)) := by
    have hh := congrArg (fun z => H.map v z) hw
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hh
  let t := (T.map (w ≫ v).right).hom
  let sc := comp fₗ t ≪≫
    StacksDraft.Perfect.derivedExtensionScalarsCongr E (transition_comp_eq T (w ≫ v))
  have htα := htrans (w ≫ v) ((eH l).symm α)
  have htId := htrans (w ≫ v) ((eH l).symm (𝟙 ((E fₗ).functor.obj K)))
  rw [hcompEq fₗ t] at htα htId
  simp only [Equiv.apply_symm_apply] at htα htId
  change eH n (H.map (w ≫ v) ((eH l).symm α)) =
    sc.inv.app K ≫ (E t).functor.map α ≫ sc.hom.app K at htα
  change eH n (H.map (w ≫ v) ((eH l).symm (𝟙 ((E fₗ).functor.obj K)))) =
    sc.inv.app K ≫ (E t).functor.map (𝟙 ((E fₗ).functor.obj K)) ≫ sc.hom.app K at htId
  change (E t).functor.map α = 𝟙 _
  apply (cancel_epi (sc.inv.app K)).1
  apply (cancel_mono (sc.hom.app K)).1
  have heq := congrArg (eH n) hn
  rw [htα, htId, (E t).functor.map_id] at heq
  simpa only [Category.assoc, Category.id_comp] using heq

/-- An isomorphism between the base changes of two perfect complexes to the colimit of a
filtered system of rings is realized over a stage of the system. -/
theorem exists_stage_iso {I : Type uI} [Category.{uI} I] [IsFiltered I]
    (T : I ⥤ CommRingCat.{u}) [PreservesColimit T (forget CommRingCat.{u})]
    (c : Cocone T) (hc : IsColimit c)
    (i₀ : I) (K L : DerivedCategory (ModuleCat.{u} (T.obj i₀)))
    (hK : StacksDraft.Perfect.IsPerfect K) (hL : StacksDraft.Perfect.IsPerfect L)
    (e : (totalDerivedExtensionScalars.{u, u, u} (c.ι.app i₀).hom).functor.obj K ≅
      (totalDerivedExtensionScalars.{u, u, u} (c.ι.app i₀).hom).functor.obj L) :
    ∃ j : Under i₀,
      Nonempty
        ((totalDerivedExtensionScalars.{u, u, u} (T.map j.hom).hom).functor.obj K ≅
         (totalDerivedExtensionScalars.{u, u, u} (T.map j.hom).hom).functor.obj L) := by
  let h := StacksDraft.Perfect.perfectComplexes_filteredColimit.{uI, u} T c hc
  obtain ⟨compKL, hcompKL, Hkl, eHkl, skl, eTargetKL, hsKL, htransKL, hlegKL⟩ := h.2 i₀ K L hK
  obtain ⟨compLK, hcompLK, Hlk, eHlk, slk, eTargetLK, hsLK, htransLK, hlegLK⟩ := h.2 i₀ L K hL
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hsKL (eTargetKL.symm e.hom)
  obtain ⟨k, y, hy⟩ := Types.jointly_surjective_of_isColimit hsLK (eTargetLK.symm e.inv)
  obtain ⟨l, jl, kl, _⟩ := IsFilteredOrEmpty.cocone_objs j k
  let αl := eHkl l (Hkl.map jl x)
  let βl := eHlk l (Hlk.map kl y)
  have hαleg : skl.ι.app l (Hkl.map jl x) = eTargetKL.symm e.hom :=
    by rw [← hx]; simp
  have hβleg : slk.ι.app l (Hlk.map kl y) = eTargetLK.symm e.inv :=
    by rw [← hy]; simp
  have hαlim := hlegKL l αl
  have hβlim := hlegLK l βl
  simp only [αl, Equiv.symm_apply_apply, hαleg, Equiv.apply_symm_apply] at hαlim
  simp only [βl, Equiv.symm_apply_apply, hβleg, Equiv.apply_symm_apply] at hβlim
  let E := fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) =>
    totalDerivedExtensionScalars.{u, u, u} f
  let fₗ := (T.map l.hom).hom
  let gₗ := (c.ι.app l.right).hom
  have hₗ : gₗ.comp fₗ = (c.ι.app i₀).hom := congrArg CommRingCat.Hom.hom (c.w l.hom)
  let lc := compKL fₗ gₗ ≪≫ StacksDraft.Perfect.derivedExtensionScalarsCongr E hₗ
  change e.hom = lc.inv.app K ≫ (E gₗ).functor.map αl ≫ lc.hom.app L at hαlim
  rw [show compLK fₗ gₗ = compKL fₗ gₗ from
    derivedComp_eq_of_comparison fₗ gₗ _ _ (hcompLK fₗ gₗ) (hcompKL fₗ gₗ)] at hβlim
  change e.inv = lc.inv.app L ≫ (E gₗ).functor.map βl ≫ lc.hom.app K at hβlim
  have hidK : lc.inv.app K ≫ (E gₗ).functor.map (αl ≫ βl) ≫ lc.hom.app K = 𝟙 _ := by
    calc
      _ = (lc.inv.app K ≫ (E gₗ).functor.map αl ≫ lc.hom.app L) ≫
          (lc.inv.app L ≫ (E gₗ).functor.map βl ≫ lc.hom.app K) := by
            simp [Functor.map_comp, Category.assoc]
      _ = e.hom ≫ e.inv := by rw [hαlim, hβlim]
      _ = 𝟙 _ := e.hom_inv_id
  have hidL : lc.inv.app L ≫ (E gₗ).functor.map (βl ≫ αl) ≫ lc.hom.app L = 𝟙 _ := by
    calc
      _ = (lc.inv.app L ≫ (E gₗ).functor.map βl ≫ lc.hom.app K) ≫
          (lc.inv.app K ≫ (E gₗ).functor.map αl ≫ lc.hom.app L) := by
            simp [Functor.map_comp, Category.assoc]
      _ = e.inv ≫ e.hom := by rw [hαlim, hβlim]
      _ = 𝟙 _ := e.inv_hom_id
  obtain ⟨mK, wK, hwK⟩ :=
    exists_stage_map_eq_id T c hc i₀ K hK compKL hcompKL l (αl ≫ βl) hidK
  obtain ⟨mL, wL, hwL⟩ :=
    exists_stage_map_eq_id T c hc i₀ L hL compKL hcompKL l (βl ≫ αl) hidL
  obtain ⟨n₀, uK, uL, _⟩ := IsFilteredOrEmpty.cocone_objs mK mL
  obtain ⟨n, v, hv⟩ := IsFilteredOrEmpty.cocone_maps (wK ≫ uK) (wL ≫ uL)
  let w : l ⟶ n := (wK ≫ uK) ≫ v
  have hmapK := hwK n (uK ≫ v)
  have hmapL := hwL n (uL ≫ v)
  rw [← Category.assoc] at hmapK hmapL
  rw [← hv] at hmapL
  let t := (T.map w.right).hom
  let sc := compKL fₗ t ≪≫
    StacksDraft.Perfect.derivedExtensionScalarsCongr E (transition_comp_eq T w)
  exact ⟨n, ⟨(sc.app K).symm ≪≫
    { hom := (E t).functor.map αl
      inv := (E t).functor.map βl
      hom_inv_id := by rw [← Functor.map_comp]; exact hmapK
      inv_hom_id := by rw [← Functor.map_comp]; exact hmapL } ≪≫ sc.app L⟩⟩

/-- **Stacks Project, Tag 0G0P.** A local Koszul presentation of a perfect complex, with flat
quotient, spreads to some principal neighbourhood of the prime. -/
@[stacks 0G0P]
theorem exists_away_koszul_description {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType R S] [Module.Flat R S]
    (q : Ideal S) [q.IsPrime]
    (K : DerivedCategory (ModuleCat.{u} S)) (hK : StacksDraft.Perfect.IsPerfect K)
    {r : ℕ} (f : Fin r → Localization.AtPrime q)
    (hf : RingTheory.Sequence.IsRegular (Localization.AtPrime q) (List.ofFn f))
    (hflat : Module.Flat R (Localization.AtPrime q ⧸ Ideal.span (Set.range f)))
    (hiso : Nonempty
      ((derivedExtensionScalarsGeneral.{u, u, u}
          (algebraMap S (Localization.AtPrime q))).functor.obj K ≅
        DerivedCategory.Q.obj
          ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat))) :
    ∃ (g : S) (hg : g ∉ q) (f' : Fin r → Localization.Away g),
      (∀ i, localizationAwayToAtPrime g q hg (f' i) = f i) ∧
      RingTheory.Sequence.IsRegular (Localization.Away g) (List.ofFn f') ∧
      Module.Flat R (Localization.Away g ⧸ Ideal.span (Set.range f')) ∧
      Nonempty
        ((derivedExtensionScalarsGeneral.{u, u, u}
            (algebraMap S (Localization.Away g))).functor.obj K ≅
          DerivedCategory.Q.obj
            ((Koszul.seqComplex f').extend ComplexShape.embeddingDownNat)) := by
  classical
  obtain ⟨g₀, hg₀, f₀, hf₀, hreg₀, hflat₀⟩ :=
    SpreadingOut.exists_away_regular_representation q f hf hflat
  let a : Localization.AwayIndex q.primeCompl := ⟨⟨g₀, hg₀⟩⟩
  let T := Localization.awayDiagram q.primeCompl
  let c := Localization.awayCocone q.primeCompl
  let φ := algebraMap S (Localization.Away g₀)
  let ψ := Localization.awayLeg a
  let K₀ := (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj K
  let L₀ := DerivedCategory.Q.obj
    ((Koszul.seqComplex f₀).extend ComplexShape.embeddingDownNat)
  have hK₀ : StacksDraft.Perfect.IsPerfect K₀ :=
    StacksDraft.Perfect.isPerfect_derivedExtensionScalars φ K hK
  have hL₀ : StacksDraft.Perfect.IsPerfect L₀ := isPerfect_extend_koszul f₀
  have hcol := StacksDraft.Perfect.perfectComplexes_filteredColimit.{u, u} T c
    (Localization.isColimitAwayCocone q.primeCompl)
  obtain ⟨comp, hcomp, _, _, _, _, _, _, _⟩ := hcol.2 a K₀ L₀ hK₀
  have hφψ : ψ.comp φ = algebraMap S (Localization.AtPrime q) :=
    Localization.awayLeg_comp_algebraMap a
  let E := fun {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) =>
    totalDerivedExtensionScalars.{u, u, u} f
  let lc := comp φ ψ ≪≫ StacksDraft.Perfect.derivedExtensionScalarsCongr E hφψ
  let : Algebra (Localization.Away g₀) (Localization.AtPrime q) := ψ.toAlgebra
  have hψ : algebraMap (Localization.Away g₀) (Localization.AtPrime q) = ψ := rfl
  obtain ⟨eKoszul⟩ :=
    nonempty_koszul_derived_baseChange_iso (B := Localization.AtPrime q) f₀
  have hseq : (fun i => ψ (f₀ i)) = f := by
    funext i
    change Localization.awayLeg a (f₀ i) = f i
    rw [Localization.awayLeg_eq_localizationAwayToAtPrime q a]
    exact hf₀ i
  rw [hψ, hseq] at eKoszul
  obtain ⟨eLocal⟩ := hiso
  let eStage : (E ψ).functor.obj K₀ ≅ (E ψ).functor.obj L₀ :=
    lc.app K ≪≫ eLocal ≪≫ eKoszul.symm
  obtain ⟨j, ⟨eLater⟩⟩ := exists_stage_iso T c
    (Localization.isColimitAwayCocone q.primeCompl) a K₀ L₀ hK₀ hL₀ eStage
  let g : S := (j.right.elem : S)
  have hg : g ∉ q := j.right.elem.property
  let τ := (T.map j.hom).hom
  let f' (i : Fin r) : Localization.Away g := τ (f₀ i)
  have himage : ∀ i, localizationAwayToAtPrime g q hg (f' i) = f i := by
    intro i
    have hleg : (Localization.awayLeg j.right).comp τ = ψ :=
      congrArg CommRingCat.Hom.hom (c.w j.hom)
    change (localizationAwayToAtPrime g q hg) (τ (f₀ i)) = f i
    rw [← Localization.awayLeg_eq_localizationAwayToAtPrime q j.right]
    change ((Localization.awayLeg j.right).comp τ) (f₀ i) = f i
    rw [hleg]
    exact congrFun hseq i
  have hφτ : τ.comp φ = algebraMap S (Localization.Away g) := by
    ext x
    exact Localization.awayTransition_algebraMap j.hom.le x
  let : Algebra (Localization.Away g₀) (Localization.Away g) := τ.toAlgebra
  have : IsScalarTower S (Localization.Away g₀) (Localization.Away g) :=
    IsScalarTower.of_algebraMap_eq' hφτ.symm
  have hunit : IsUnit (algebraMap S (Localization.Away g) g₀) :=
    Localization.isUnit_algebraMap_away_of_le j.hom.le
  have : IsLocalization.Away (algebraMap S (Localization.Away g) g₀) (Localization.Away g) :=
    IsLocalization.away_of_isUnit_of_bijective _ hunit Function.bijective_id
  have : IsLocalization.Away (algebraMap S (Localization.Away g₀) g) (Localization.Away g) :=
    IsLocalization.Away.commutes (Localization.Away g₀) (Localization.Away g)
      (Localization.Away g) g₀ g
  have : Module.Flat (Localization.Away g₀) (Localization.Away g) :=
    IsLocalization.flat _ (Submonoid.powers (algebraMap S (Localization.Away g₀) g))
  have hτ : algebraMap (Localization.Away g₀) (Localization.Away g) = τ := rfl
  refine ⟨g, hg, f', himage, ?_, ?_, ?_⟩
  · have hweak : RingTheory.Sequence.IsWeaklyRegular
        (Localization.Away g) (List.ofFn f') := by
      have h := hreg₀.1.of_flat_of_isBaseChange
        (IsBaseChange.linearMap (Localization.Away g₀) (Localization.Away g))
      have hlist : List.map (algebraMap (Localization.Away g₀) (Localization.Away g))
          (List.ofFn f₀) = List.ofFn f' := by
        simp only [List.map_ofFn, Function.comp_def, hτ, f']
        rfl
      rwa [hlist] at h
    refine ⟨hweak, ?_⟩
    intro htop
    have htopIdeal : Ideal.span (Set.range f') = ⊤ := by
      rw [← Ideal.ofList_ofFn]
      exact (by simpa using htop : (⊤ : Ideal (Localization.Away g)) = _).symm
    have hmap : (Ideal.span (Set.range f')).map (localizationAwayToAtPrime g q hg) =
        Ideal.span (Set.range f) := by
      rw [Ideal.map_span, ← Set.range_comp, Function.comp_def]
      exact congrArg Ideal.span (congrArg Set.range (funext fun i => himage i))
    have htopC : Ideal.span (Set.range f) = ⊤ := by
      rw [← hmap, htopIdeal, Ideal.map_top]
    apply hf.2
    rw [← Ideal.ofList_ofFn] at htopC
    simpa using htopC.symm
  · let I : Ideal (Localization.Away g₀) := Ideal.span (Set.range f₀)
    let J : Ideal (Localization.Away g) := I.map (algebraMap _ _)
    have hJ : J = Ideal.span (Set.range f') := by
      dsimp only [J, I]
      rw [Ideal.map_span, ← Set.range_comp, Function.comp_def]
      congr 1
    let : Algebra (Localization.Away g₀ ⧸ I) (Localization.Away g ⧸ J) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    have hflatQ : Module.Flat (Localization.Away g₀ ⧸ I) (Localization.Away g ⧸ J) :=
      Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor
          (Localization.Away g) I).toLinearEquiv
    have hmapR (x : R) :
        algebraMap (Localization.Away g₀) (Localization.Away g)
            (algebraMap R (Localization.Away g₀) x) =
          algebraMap R (Localization.Away g) x := by
      rw [hτ, IsScalarTower.algebraMap_apply R S (Localization.Away g₀),
        IsScalarTower.algebraMap_apply R S (Localization.Away g)]
      exact congrArg (fun h : S →+* Localization.Away g => h (algebraMap R S x)) hφτ
    have : IsScalarTower R (Localization.Away g₀ ⧸ I) (Localization.Away g ⧸ J) := by
      refine ⟨fun x y z => ?_⟩
      induction y using Quotient.inductionOn' with
      | _ y =>
        induction z using Quotient.inductionOn' with
        | _ z =>
          change Ideal.Quotient.mk J
              (algebraMap (Localization.Away g₀) (Localization.Away g) (x • y) * z) =
            Ideal.Quotient.mk J
              (x • (algebraMap (Localization.Away g₀) (Localization.Away g) y * z))
          congr 1
          rw [Algebra.smul_def, map_mul, hmapR, Algebra.smul_def, mul_assoc]
    have hflatR : Module.Flat R (Localization.Away g ⧸ J) :=
      Module.Flat.trans R (Localization.Away g₀ ⧸ I) (Localization.Away g ⧸ J)
    rwa [hJ] at hflatR
  · let κ := algebraMap S (Localization.Away g)
    let lcLater := comp φ τ ≪≫ StacksDraft.Perfect.derivedExtensionScalarsCongr E hφτ
    obtain ⟨eKoszulLater⟩ :=
      nonempty_koszul_derived_baseChange_iso (B := Localization.Away g) f₀
    change Nonempty ((E κ).functor.obj K ≅
      DerivedCategory.Q.obj ((Koszul.seqComplex f').extend ComplexShape.embeddingDownNat))
    rw [hτ] at eKoszulLater
    exact ⟨(lcLater.app K).symm ≪≫ eLater ≪≫ eKoszulLater⟩

end StacksDraft.Perfect

end
