module

public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.CategoryTheory.Triangulated.BrickShift
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Basic
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.PseudoCoherent.Noetherian
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality
public import StacksCore.Tactic.StacksAttribute

/-!
# The bounded coherent derived category: objects, truncations and torsion

Let `A` be a commutative ring. This file sets up the objects used to show that an `A`-linear
autoequivalence of `D^b_{Coh}(A)` sends the ring to an invertible object ([stacks 0A7E]):
finite modules and residue fields, placed in a given degree, as objects of `D^b_{Coh}(A)`, the
shift and triangulated structures of `D^b_{Coh}(A)`, and the truncation and torsion lemmas
producing a nonzero morphism from a complex to a negative shift of itself.

## Main definitions

* `Dualizing.finiteModuleObject`: a finite module, in degree zero, as an object of the bounded
  coherent derived category.
* `Dualizing.ringObject`: the ring itself, in degree zero, as such an object.
* `Dualizing.residueObject`: a residue field, in a given degree, as such an object.

## Implementation notes

`D^b_{Coh}(A)` is `Dualizing.BoundedCoherentDerivedCategory A`. Its shift and triangulated
structures are induced from the ambient derived category, by the four subcategory instances
proved here. The subcategory instances allow independent ring and module universes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe u v w x y

attribute [local instance] HasDerivedCategory.standard

namespace Dualizing

/-- A finite module, viewed as a degree-zero object of the bounded coherent derived category. -/
public noncomputable def finiteModuleObject (A : Type u) [CommRing A]
    (E : ModuleCat.{u} A) [Module.Finite A E] :
    BoundedCoherentDerivedCategory A := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E
  refine ⟨X, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      let e : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj X) ≃ₗ[A] E :=
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{u} A) 0).app E).toLinearEquiv
      exact Module.Finite.equiv e.symm
    · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X) := by
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE X 0 i hi
        · exact DerivedCategory.isZero_of_isLE X 0 i hi
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance
  · exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩

/-- The ring `A`, placed in degree zero, as an object of its bounded coherent derived
category. -/
public noncomputable def ringObject (A : Type u) [CommRing A] :
    BoundedCoherentDerivedCategory A :=
  finiteModuleObject A (ModuleCat.of A A)

/-- A finite module, placed in degree `n`, as an object of the bounded coherent derived
category. -/
public noncomputable def finiteModuleObjectAt (A : Type u) [CommRing A]
    (E : ModuleCat.{u} A) [Module.Finite A E] (n : ℤ) :
    BoundedCoherentDerivedCategory A := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj E
  refine ⟨X, ?_, ?_⟩
  · intro i
    by_cases hi : i = n
    · subst i
      let e : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X) ≃ₗ[A] E :=
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{u} A) n).app E).toLinearEquiv
      exact Module.Finite.equiv e.symm
    · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X) := by
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE X n i hi
        · exact DerivedCategory.isZero_of_isLE X n i hi
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance
  · exact ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩

/-- The residue field at a maximal ideal, placed in degree `n`, as an object of the bounded
coherent derived category. -/
public noncomputable abbrev residueObject {A : Type u} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (n : ℤ) : BoundedCoherentDerivedCategory.{u, u} A :=
  finiteModuleObjectAt A (ModuleCat.of A m.ResidueField) n


section Subcategory

variable (A : Type u) [CommRing A]

/-- Finite cohomology is invariant under isomorphisms in the derived category. -/
public instance finiteCohomology_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DerivedCategory (ModuleCat.{max u v} A) => ∀ i : ℤ,
        Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) where
  of_iso e h i := by
    have := h i
    exact Module.Finite.equiv
      (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso e).toLinearEquiv)

/-- Shifting a complex reindexes its finite cohomology modules. -/
public instance finiteCohomology_isStableUnderShift :
    ObjectProperty.IsStableUnderShift
      (fun K : DerivedCategory (ModuleCat.{max u v} A) => ∀ i : ℤ,
        Module.Finite A
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) ℤ where
  isStableUnderShiftBy n := ⟨by
    intro K h i
    have : Module.Finite A
        (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).shift (n + i)).obj K) :=
      h (n + i)
    exact Module.Finite.equiv
      (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).shiftIso
        n i (n + i) rfl).app K).toLinearEquiv.symm⟩

/-- Over a Noetherian ring, finite cohomology is closed under distinguished triangles. -/
public instance finiteCohomology_isTriangulated [IsNoetherianRing A] :
    ObjectProperty.IsTriangulated
      (fun K : DerivedCategory (ModuleCat.{max u v} A) => ∀ i : ℤ,
        Module.Finite A
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro i
    have := ModuleCat.isZero_iff_subsingleton.mp
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map_isZero (isZero_zero _))
    infer_instance
  toIsTriangulatedClosed₂ := .mk' (by
    intro T hT h₁ h₃ i
    have := h₁ i
    have := h₃ i
    let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i
    have hex := H.map_distinguished_exact T hT
    have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hex
    have := isNoetherian_of_range_eq_ker (H.map T.mor₁).hom (H.map T.mor₂).hom
      (LinearMap.exact_iff.mp he).symm
    infer_instance)

/-- Bounded coherent complexes form a triangulated subcategory of the derived category. -/
public instance boundedCoherent_isTriangulated [IsNoetherianRing A] :
    ObjectProperty.IsTriangulated
      (fun K : DerivedCategory (ModuleCat.{max u v} A) =>
        (∀ i : ℤ, Module.Finite A
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) ∧
        (DerivedCategory.TStructure.t).bounded K) := by
  change ObjectProperty.IsTriangulated
    ((fun K : DerivedCategory (ModuleCat.{max u v} A) => ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K)) ⊓
      (DerivedCategory.TStructure.t).bounded)
  infer_instance

end Subcategory

/-- Morphisms from a module in degree zero to a strictly negative shift of a module in degree
zero vanish. -/
public theorem hom_eq_zero_of_negative_shift_single_to
    (A : Type u) [CommRing A] (E M : ModuleCat.{u} A) (n : ℤ) (hn : n < 0) :
    ∀ f : ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)⟦n⟧, f = 0 := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  intro f
  have : ((S.obj M)⟦n⟧).IsGE (-n) := DerivedCategory.TStructure.t.isGE_shift (S.obj M) 0 n (-n)
  exact DerivedCategory.TStructure.t.zero f 0 (-n)

/-- The residue field at a maximal ideal is a simple module over the ring. -/
public theorem isSimpleModule_residueField
    {A : Type u} [CommRing A] (m : Ideal A) [hm : m.IsMaximal] :
    IsSimpleModule A m.ResidueField := by
  have hquot : IsSimpleModule A (A ⧸ m) := by
    rw [isSimpleModule_iff_quot_maximal]
    exact ⟨m, hm, ⟨LinearEquiv.refl A (A ⧸ m)⟩⟩
  exact hquot.congr (LinearEquiv.ofBijective
    ((Algebra.linearMap (A ⧸ m) m.ResidueField).restrictScalars A)
    m.bijective_algebraMap_quotient_residueField).symm

/-- A fully faithful linear functor identifies Hom groups as modules over the base ring. -/
public noncomputable def fullyFaithfulHomLinearEquiv
    {R : Type u} [CommSemiring R] {C₁ : Type v} {C₂ : Type w}
    [Category.{x, v} C₁] [Category.{y, w} C₂]
    [Preadditive C₁] [Preadditive C₂] [Linear R C₁] [Linear R C₂]
    (G : C₁ ⥤ C₂) (hG : G.FullyFaithful) [G.Linear R] [G.Additive] (X Y : C₁) :
    (X ⟶ Y) ≃ₗ[R] (G.obj X ⟶ G.obj Y) where
  toEquiv := hG.homEquiv
  map_add' := by simp [Functor.FullyFaithful.homEquiv_apply, Functor.map_add]
  map_smul' := by simp [Functor.FullyFaithful.homEquiv_apply, Functor.map_smul]

variable {A : Type u} [CommRing A]

/-- The maximal ideal annihilates the identity of the image of its residue field. -/
public theorem residueField_image_smul_id_eq_zero [IsNoetherianRing A]
    (F : BoundedCoherentDerivedCategory.{u, u} A ⥤ BoundedCoherentDerivedCategory.{u, u} A)
    [F.Linear A] [F.Additive]
    (m : Ideal A) [m.IsMaximal] (r : A) (hr : r ∈ m) :
    r • (𝟙 (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField)))) = 0 := by
  let E : ModuleCat.{u} A := ModuleCat.of A m.ResidueField
  let X := finiteModuleObject A E
  have hE : r • (𝟙 E) = 0 := by
    ext x
    change r • x = 0
    rw [Algebra.smul_def, Ideal.algebraMap_residueField_eq_zero.mpr hr, zero_mul]
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  have hsingle : r • (𝟙 (S.obj E)) = 0 := by
    simpa only [Functor.map_smul, Functor.map_zero, S.map_id] using congrArg S.map hE
  have hX : r • (𝟙 X) = 0 := ObjectProperty.hom_ext _ hsingle
  simpa only [Functor.map_smul, F.map_id, Functor.map_zero] using congrArg F.map hX

/-- The maximal ideal annihilates every cohomology module of the image of its residue field. -/
public theorem residueField_image_homology_annihilated [IsNoetherianRing A]
    (F : BoundedCoherentDerivedCategory.{u, u} A ⥤ BoundedCoherentDerivedCategory.{u, u} A)
    [F.IsEquivalence] [F.Linear A] [F.Additive]
    (m : Ideal A) [m.IsMaximal] (r : A) (hr : r ∈ m) (i : ℤ) :
    ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj, r • x = 0 := by
  let Y := F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  have hY : r • (𝟙 Y.obj) = 0 :=
    congrArg (fun f : Y ⟶ Y => f.hom) (residueField_image_smul_id_eq_zero F m r hr)
  let _ : Functor.Linear A H :=
    DerivedCategory.homologyFunctor_linear (C := ModuleCat.{u} A) A i
  have hH := congrArg H.map hY
  have hLinear : r • (LinearMap.id : (H.obj Y.obj) →ₗ[A] H.obj Y.obj) = 0 := by
    rw [Functor.map_smul, H.map_id (Y.obj), Functor.map_zero] at hH
    exact congrArg (fun f : (H.obj Y.obj) ⟶ (H.obj Y.obj) => f.hom) hH
  intro x
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply] using
    congrArg (fun f : (H.obj Y.obj) →ₗ[A] H.obj Y.obj => f x) hLinear

/-- Every cohomology module of the image of a residue field is torsion for the maximal ideal. -/
public theorem residueField_image_homology_torsionBySet [IsNoetherianRing A]
    (F : BoundedCoherentDerivedCategory.{u, u} A ⥤ BoundedCoherentDerivedCategory.{u, u} A)
    [F.IsEquivalence] [F.Linear A] [F.Additive]
    (m : Ideal A) [m.IsMaximal] (i : ℤ) :
    Module.IsTorsionBySet A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (F.obj (finiteModuleObject A (ModuleCat.of A m.ResidueField))).obj) m :=
  fun x r => residueField_image_homology_annihilated F m r r.property i x

/-- Over a Noetherian ring, a bounded complex with finite cohomology is pseudo-coherent. -/
public theorem boundedCoherentObject_isPseudoCoherent [IsNoetherianRing A]
    (X : BoundedCoherentDerivedCategory.{u, u} A) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent X.obj := by
  rcases X.property.2 with ⟨⟨_, _⟩, ⟨b, _⟩⟩
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    X.obj 0 (ModuleCat.of A A)).2.1.mpr
      ⟨⟨b, fun i hi => DerivedCategory.isZero_of_isLE X.obj b i hi⟩, X.property.1⟩

/-- A complex whose cohomology vanishes outside one degree is a shift of a module. -/
public theorem exists_iso_singleFunctor_obj_of_homology_vanish_off
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (h : ∀ i : ℤ, i ≠ n → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    ∃ E : ModuleCat.{u} A,
      Nonempty (K ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj E) := by
  have hGE : K.IsGE n := (DerivedCategory.isGE_iff K n).2 (fun i hi => h i (by omega))
  have hLE : K.IsLE n := (DerivedCategory.isLE_iff K n).2 (fun i hi => h i (by omega))
  exact DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K n

/-- A nonzero complex with cohomology in a bounded range has nonzero cohomology somewhere in
that range. -/
public theorem exists_nonzero_homology_of_bounded_nonzero
    (K : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    [K.IsGE a] [K.IsLE b] (hK : ¬ IsZero K) :
    ∃ i : ℤ, i ∈ Set.Icc a b ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  by_contra h
  push Not at h
  have : K.IsGE b := (DerivedCategory.isGE_iff K b).2 (by
    intro i hi
    by_cases hia : i < a
    · exact DerivedCategory.isZero_of_isGE K a i hia
    · exact h i ⟨not_lt.mp hia, le_of_lt hi⟩)
  obtain ⟨E, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K b
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) b
  have hB : IsZero (H.obj K) := by
    by_cases hab : a ≤ b
    · exact h b ⟨hab, le_rfl⟩
    · exact DerivedCategory.isZero_of_isGE K a b (lt_of_not_ge hab)
  have hE : IsZero E := hB.of_iso
    (((H.mapIso e) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) b).app E).symm)
  exact hK (((DerivedCategory.singleFunctor (ModuleCat.{u} A) b).map_isZero hE).of_iso e)

/-- The upper truncation of an object bounded above by `n` is also bounded above by `n`.
Together with its built-in lower bound, it is therefore concentrated in degree `n`. -/
public theorem isLE_truncGE_of_isLE
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) [K.IsLE n] :
    ((DerivedCategory.TStructure.t.truncGE n).obj K).IsLE n := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{u} A)
  let T := (t.triangleLTGE n).obj K
  have h₂ : t.IsLE T.obj₂ n := by simpa [T, t] using (inferInstance : K.IsLE n)
  have h₃ : t.IsLE (T.obj₁⟦(1 : ℤ)⟧) n := by
    have := t.isLE_shift T.obj₁ (n - 1) 1 (n - 2)
    exact t.isLE_of_le _ (n - 2) n
  have hh := t.isLE₂ T.rotate (rot_of_distTriang T (t.triangleLTGE_distinguished n K))
    n h₂ h₃
  simpa [T, t] using hh

/-- The lower truncation of an object bounded below by `n` is also bounded below by `n`.
Together with its built-in upper bound, it is therefore concentrated in degree `n`. -/
public theorem isGE_truncLT_of_isGE
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) [K.IsGE n] :
    ((DerivedCategory.TStructure.t.truncLT (n + 1)).obj K).IsGE n := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{u} A)
  let T := (t.triangleLTGE (n + 1)).obj K
  have h₁ : t.IsGE (T.obj₃⟦(-1 : ℤ)⟧) n := by
    have := t.isGE_shift T.obj₃ (n + 1) (-1) (n + 2)
    exact t.isGE_of_ge _ n (n + 2)
  have h₃ : t.IsGE T.obj₂ n := by simpa [T, t] using (inferInstance : K.IsGE n)
  have hh := t.isGE₂ T.invRotate
    (inv_rot_of_distTriang T (t.triangleLTGE_distinguished (n + 1) K)) n h₁ h₃
  simpa [T, t] using hh

/-- The upper truncation map induces an isomorphism on the top homology module. -/
public theorem isIso_homology_map_truncGEπ
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app K)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE n).obj K
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map T.mor₂)
  have hT : T ∈ distTriang _ := DerivedCategory.TStructure.t.triangleLTGE_distinguished n K
  have h₁ : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) (by omega)]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) (n + 1) (by omega)).eq_of_tgt _ _
  have h₂ : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT n]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) n (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- The lower truncation map induces an isomorphism below the truncation bound. -/
public theorem isIso_homology_map_truncLTι
    (K : DerivedCategory (ModuleCat.{u} A)) (n i : ℤ) (hi : i < n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((DerivedCategory.TStructure.t.truncLTι n).app K)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE n).obj K
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map T.mor₁)
  have hT : T ∈ distTriang _ := DerivedCategory.TStructure.t.triangleLTGE_distinguished n K
  have h₁ : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    exact (DerivedCategory.isZero_of_isGE T.obj₃ n i hi).eq_of_tgt _ _
  have h₂ : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)]
    exact (DerivedCategory.isZero_of_isGE T.obj₃ n (i - 1) (by omega)).eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- Between two nonzero modules killed by a maximal ideal there is a nonzero linear map: both
are nonzero vector spaces over the residue field. -/
public theorem exists_nonzero_linearMap_of_maximal_ideal_killed
    (m : Ideal A) [m.IsMaximal]
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (hM : Module.IsTorsionBySet A M m) (hN : Module.IsTorsionBySet A N m)
    (hMne : Nontrivial M) (hNne : Nontrivial N) :
    ∃ f : M →ₗ[A] N, f ≠ 0 := by
  classical
  let k := A ⧸ m
  let _ : Field k := Ideal.Quotient.field m
  let _ : Module k M := hM.module
  let _ : Module k N := hN.module
  let _ : IsScalarTower A k M := hM.isScalarTower
  let _ : IsScalarTower A k N := hN.isScalarTower
  obtain ⟨ι, ⟨bM⟩⟩ := Module.Basis.exists_basis k M
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hrepr : bM.repr x ≠ 0 := fun h => hx (bM.repr.injective (by simpa using h))
  obtain ⟨i, hi⟩ := (Finsupp.support_nonempty_iff).mpr hrepr
  have hcoord : bM.coord i x ≠ 0 := by
    simpa only [bM.coord_apply] using (Finsupp.mem_support_iff.mp hi)
  obtain ⟨y, hy⟩ := exists_ne (0 : N)
  let f : M →ₗ[k] N := (bM.coord i).smulRight y
  have hfx : f x ≠ 0 := smul_ne_zero hcoord hy
  exact ⟨f.restrictScalars A, fun h => hfx (congrArg (fun g : M →ₗ[A] N => g x) h)⟩

/-- Two nonzero cohomology modules in different degrees produce a nonzero morphism into a
strictly negative shift: the truncation triangles turn a map from the higher module to the
lower one into such a morphism. -/
public theorem exists_nonzero_negative_shift_hom_of_two_nonzero_homology
    (K : DerivedCategory (ModuleCat.{u} A))
    (a b : ℤ) (_hab : a < b) [K.IsGE a] [K.IsLE b]
    {f : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).obj K) →ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) a).obj K)} (hf : f ≠ 0) :
    ∃ g : K ⟶ K⟦a - b⟧, g ≠ 0 := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{u} A)
  let Hₐ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) a
  let Hᵦ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) b
  let S := DerivedCategory.singleFunctors (ModuleCat.{u} A)
  let U := (t.truncGE b).obj K
  let L := (t.truncLT (a + 1)).obj K
  have : U.IsLE b := isLE_truncGE_of_isLE K b
  obtain ⟨E, ⟨eU⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE U b
  have hπ : IsIso (Hᵦ.map ((t.truncGEπ b).app K)) := isIso_homology_map_truncGEπ K b
  let eUhom := (Hᵦ.mapIso eU) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) b).app E
  let topIso : U ≅ (S.functor b).obj (Hᵦ.obj K) :=
    eU ≪≫ (S.functor b).mapIso eUhom.symm ≪≫
      (S.functor b).mapIso (asIso (Hᵦ.map ((t.truncGEπ b).app K))).symm
  let top := (t.truncGEπ b).app K ≫ topIso.hom
  have : L.IsGE a := isGE_truncLT_of_isGE K a
  obtain ⟨E', ⟨eL⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L a
  have hι : IsIso (Hₐ.map ((t.truncLTι (a + 1)).app K)) :=
    isIso_homology_map_truncLTι K (a + 1) a (by omega)
  let eLhom := (Hₐ.mapIso eL) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) a).app E'
  let p := a - b
  let hShiftIso : (S.functor b).obj (Hₐ.obj K) ≅ ((S.functor a).obj (Hₐ.obj K))⟦p⟧ := by
    simpa only [Functor.comp_obj] using
      ((S.shiftIso p b a (by dsimp [p]; omega)).app (Hₐ.obj K)).symm
  let botIso : (S.functor b).obj (Hₐ.obj K) ≅ L⟦p⟧ :=
    hShiftIso ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) p).mapIso
        ((S.functor a).mapIso (asIso (Hₐ.map ((t.truncLTι (a + 1)).app K))).symm) ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) p).mapIso
        ((S.functor a).mapIso eLhom) ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) p).mapIso eL.symm
  let bot := botIso.hom ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) p).map
    ((t.truncLTι (a + 1)).app K)
  let mid := (S.functor b).map (ModuleCat.ofHom f)
  let g := top ≫ mid ≫ bot
  have htop : IsIso (Hᵦ.map top) := by
    dsimp [top]
    rw [Functor.map_comp]
    infer_instance
  have hmid : Hᵦ.map mid ≠ 0 := by
    dsimp [mid]
    let η := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) b)
    have hnat := η.hom.naturality (ModuleCat.ofHom f)
    change Hᵦ.map ((S.functor b).map (ModuleCat.ofHom f)) ≫ η.hom.app _ =
      η.hom.app _ ≫ ModuleCat.ofHom f at hnat
    intro hz
    apply hf
    have hz' : Hᵦ.map ((S.functor b).map (ModuleCat.ofHom f)) ≫
        η.hom.app (Hₐ.obj K) = 0 := by simp [hz]
    have hzero : η.hom.app (Hᵦ.obj K) ≫ ModuleCat.ofHom f =
        η.hom.app (Hᵦ.obj K) ≫ 0 := by simpa using hnat.symm.trans hz'
    have hmorph : ModuleCat.ofHom f = 0 := (cancel_epi (η.hom.app (Hᵦ.obj K))).mp hzero
    exact congrArg (fun q : Hᵦ.obj K ⟶ Hₐ.obj K => q.hom) hmorph
  have hbot : IsIso (Hᵦ.map bot) := by
    dsimp [bot]
    rw [Functor.map_comp]
    have : IsIso (Hᵦ.map ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) p).map
        ((t.truncLTι (a + 1)).app K))) := by
      let h := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso p b a
        (by dsimp [p]; omega)
      have hnat := h.hom.naturality ((t.truncLTι (a + 1)).app K)
      change Hᵦ.map ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) p).map
          ((t.truncLTι (a + 1)).app K)) ≫ (h.app K).hom =
        (h.app L).hom ≫ Hₐ.map ((t.truncLTι (a + 1)).app K) at hnat
      have hcomp : IsIso (Hᵦ.map ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) p).map
          ((t.truncLTι (a + 1)).app K)) ≫ (h.app K).hom) := by
        rw [hnat]
        exact IsIso.comp_isIso' ⟨⟨(h.app L).inv, (h.app L).hom_inv_id, (h.app L).inv_hom_id⟩⟩ hι
      exact (isIso_comp_right_iff _ (h.app K).hom).mp hcomp
    infer_instance
  have hg : Hᵦ.map g ≠ 0 := by
    intro hz
    apply hmid
    apply (cancel_epi (Hᵦ.map top)).mp
    apply (cancel_mono (Hᵦ.map bot)).mp
    simpa [g, Functor.map_comp, Category.assoc] using hz
  exact ⟨g, fun hz => hg (by simp [hz])⟩

end Dualizing

end
