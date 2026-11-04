module

public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayama
public import StacksFrontier.Homology.DerivedCategory.ModelComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence and the derived Nakayama lemma in any model of the derived category

`HasDerivedCategory` is a choice of a localization of cochain complexes at the
quasi-isomorphisms. This file states pseudo-coherence in an arbitrary model (by definition it is
`StacksDraft.PseudoCoherence.IsPseudoCoherent` at that model), shows that the comparison
equivalence between any two models preserves and reflects it, and proves in any model the
stability results of `StacksFrontier.Algebra.Homology.PseudoCoherentNakayama`: stability under
derived extension of scalars and under cones, and the derived Nakayama lemma.

## Main definitions

* `StacksDraft.PseudoCoherence.IsPseudoCoherentIn`: an object of a chosen model of `D(R)` is
  represented by a bounded-above complex of finite free `R`-modules.

## Main results

* `StacksDraft.PseudoCoherence.isPseudoCoherentIn_iff_isPseudoCoherent`: pseudo-coherence in a
  model is pseudo-coherence of the image in any other model.
* `StacksDraft.PseudoCoherence.IsPseudoCoherentIn.totalDerivedExtensionScalars_obj`: derived
  extension of scalars preserves pseudo-coherence.
* `StacksDraft.PseudoCoherence.IsPseudoCoherentIn.obj₃_of_distinguished`: cones of
  pseudo-coherent objects are pseudo-coherent.
* `IsPseudoCoherentIn.isZero_of_isZero_derivedExtensionScalars_quotient` and
  `IsPseudoCoherentIn.isIso_of_isIso_derivedExtensionScalars_quotient_map`, in the namespace
  `StacksDraft.PseudoCoherence`: the derived Nakayama lemma modulo an ideal contained in the
  Jacobson radical.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CochainComplex.DerivedExtensionScalars StacksDraft.DerivedModel
open scoped ZeroObject

universe u v w w' wR wA w''

namespace StacksDraft.PseudoCoherence

section Model

variable {R : Type u} [Ring R]

/-- An object `K` of a chosen model of the derived category `D(R)` is *pseudo-coherent* when it
is isomorphic to the image of a bounded-above complex of finite free `R`-modules. In every model
this is `IsPseudoCoherent`. -/
@[sga "6 II 2.3.2"]
def IsPseudoCoherentIn [HasDerivedCategory.{w'} (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  ∃ E : CochainComplex (ModuleCat.{v} R) ℤ,
    IsBoundedAboveFiniteFree E ∧ Nonempty ((DerivedCategory.Q).obj E ≅ K)

/-- `IsPseudoCoherentIn` is `IsPseudoCoherent`, in every model. -/
theorem isPseudoCoherentIn_iff [HasDerivedCategory.{w'} (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) : IsPseudoCoherentIn K ↔ IsPseudoCoherent K :=
  Iff.rfl

/-- Pseudo-coherence in a model only depends on the isomorphism class of the object. -/
theorem IsPseudoCoherentIn.ofIso [HasDerivedCategory.{w'} (ModuleCat.{v} R)]
    {K K' : DerivedCategory (ModuleCat.{v} R)} (hK : IsPseudoCoherentIn K) (e : K ≅ K') :
    IsPseudoCoherentIn K' := by
  obtain ⟨E, hE, ⟨e'⟩⟩ := hK
  exact ⟨E, hE, ⟨e' ≪≫ e⟩⟩

/-- **Pseudo-coherence does not depend on the model.** An object `K` of a chosen model of
`D(R)` is pseudo-coherent exactly when its image under the comparison equivalence to any other
model `h'` is pseudo-coherent. -/
theorem isPseudoCoherentIn_iff_isPseudoCoherent [h : HasDerivedCategory.{w'} (ModuleCat.{v} R)]
    (K : DerivedCategory (ModuleCat.{v} R)) (h' : HasDerivedCategory.{w''} (ModuleCat.{v} R)) :
    @IsPseudoCoherentIn _ _ h K ↔ IsPseudoCoherent ((modelEquiv h h').functor.obj K) := by
  let e := modelEquiv h h'
  constructor
  · rintro ⟨E, hE, ⟨i⟩⟩
    exact ⟨E, hE, ⟨((modelCompQIso h h').app E).symm ≪≫ e.functor.mapIso i⟩⟩
  · rintro ⟨E, hE, ⟨i⟩⟩
    exact ⟨E, hE, ⟨((modelInverseCompQIso h h').app E).symm ≪≫
      e.inverse.mapIso i ≪≫ (e.unitIso.app K).symm⟩⟩

/-- The degree-`i` cohomology of the image of a complex in any model of the derived category is
the degree-`i` homology of the complex. -/
noncomputable def homologyQObjIso [HasDerivedCategory.{w'} (ModuleCat.{v} R)]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj ((DerivedCategory.Q).obj E) ≅
      E.homology i :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app E

/-- A complex of finite free modules, bounded above, whose homology vanishes above degree `b` is
quasi-isomorphic, in any model of the derived category, to a complex of finite free modules
vanishing above degree `b`. -/
theorem exists_finiteFree_representative_le_of_homology
    [HasDerivedCategory.{w'} (ModuleCat.{v} R)]
    {E : CochainComplex (ModuleCat.{v} R) ℤ} (hE : IsBoundedAboveFiniteFree E) (b : ℤ)
    (hvan : ∀ i, b < i → IsZero (E.homology i)) :
    ∃ (P : CochainComplex (ModuleCat.{v} R) ℤ)
      (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj E),
      (∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) ∧
      P.IsStrictlyLE b ∧ IsIso α :=
  exists_finiteFree_representative_le _ b ⟨E, hE, ⟨Iso.refl _⟩⟩
    fun i hi => (hvan i hi).of_iso (homologyQObjIso E i)

/-- A pseudo-coherent object of any model of `D(R)` with no cohomology above degree `b` is
represented by a complex of finite free modules which vanishes above degree `b`. -/
theorem IsPseudoCoherentIn.exists_finiteFree_representative_le
    [HasDerivedCategory.{w'} (ModuleCat.{v} R)] {K : DerivedCategory (ModuleCat.{v} R)}
    (hK : IsPseudoCoherentIn K) (b : ℤ)
    (hvan : ∀ i, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) :
    ∃ (P : CochainComplex (ModuleCat.{v} R) ℤ) (α : DerivedCategory.Q.obj P ⟶ K),
      (∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) ∧
      P.IsStrictlyLE b ∧ IsIso α :=
  PseudoCoherence.exists_finiteFree_representative_le K b hK hvan

end Model

section Triangulated

variable {R : Type u} [Ring R]

/-- **Stacks 064V**, the cone case, in any model of `D(R)`. In a distinguished triangle
`K → L → C → K[1]` whose first two objects are pseudo-coherent, the third object is
pseudo-coherent. -/
@[sga "6 I 2.6" "partial"]
theorem IsPseudoCoherentIn.obj₃_of_distinguished [HasDerivedCategory.{w'} (ModuleCat.{v} R)]
    (T : Triangle (DerivedCategory (ModuleCat.{v} R))) (hT : T ∈ distTriang _)
    (h₁ : IsPseudoCoherentIn T.obj₁) (h₂ : IsPseudoCoherentIn T.obj₂) :
    IsPseudoCoherentIn T.obj₃ :=
  (isPseudoCoherent_of_distinguished T hT).1 h₁ h₂

end Triangulated

section ExtensionScalars

/-- Derived extension of scalars along `φ : R →+* B`, in any models of the two derived
categories, sends pseudo-coherent objects to pseudo-coherent objects. -/
theorem IsPseudoCoherentIn.totalDerivedExtensionScalars_obj
    {R : Type u} {B : Type w} [CommRing R] [CommRing B] {φ : R →+* B}
    [HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} B)]
    (D : TotalDerivedExtensionScalars.{u, v, w, wR, wA} φ)
    {K : DerivedCategory (ModuleCat.{max v u w} R)} (hK : IsPseudoCoherentIn K) :
    IsPseudoCoherentIn (D.functor.obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  have : ∀ i, Projective (E.X i) := fun i => by
    have := (hE.finiteFree i).2
    infer_instance
  have := D.comparison_isIso_of_projective E b
  let : (ModuleCat.extendScalars.{u, w, max v u w} φ).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v u w, u, w} φ).isLeftAdjoint
  let F := ModuleCat.extendScalars.{u, w, max v u w} φ
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E, ⟨⟨b, ?_⟩, fun i => ?_⟩,
    ⟨(asIso (D.comparison.app E)).symm ≪≫ D.functor.mapIso e⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact F.map_isZero (E.isZero_of_isStrictlyLE b i hi)
  · have := (hE.finiteFree i).1
    have := (hE.finiteFree i).2
    let : Algebra R B := φ.toAlgebra
    exact ⟨inferInstanceAs (Module.Finite B (TensorProduct R B (E.X i))),
      inferInstanceAs (Module.Free B (TensorProduct R B (E.X i)))⟩

variable {R : Type u} [CommRing R] {I : Ideal R}
  [HasDerivedCategory.{wR} (ModuleCat.{max v u} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{max v u} (R ⧸ I))]

/-- **One step of the derived Nakayama lemma**, in any models. Let `I` lie in the Jacobson
radical of `R` and let `C` be pseudo-coherent with no cohomology above degree `n`. If the derived
reduction `C ⊗ᴸ_R R/I` vanishes, then so does `Hⁿ(C)`. -/
theorem IsPseudoCoherentIn.isZero_homology_of_isZero_derivedExtensionScalars_quotient
    (hI : I ≤ Ideal.jacobson ⊥)
    (Dq : TotalDerivedExtensionScalars.{u, v, u, wR, wA} (Ideal.Quotient.mk I))
    {C : DerivedCategory (ModuleCat.{max v u} R)} (hC : IsPseudoCoherentIn C)
    (hDq : IsZero (Dq.functor.obj C)) (n : ℤ)
    (hvan : ∀ i, n < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj C)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) n).obj C) := by
  obtain ⟨P, α, hP, hPle, hα⟩ := hC.exists_finiteFree_representative_le n hvan
  have : ∀ i, Projective (P.X i) := fun i => by
    have := (hP i).2
    infer_instance
  have := Dq.comparison_isIso_of_projective P n
  let : (ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} (Ideal.Quotient.mk I)).isLeftAdjoint
  let F := ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)
  let FP := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  -- `C ⊗ᴸ_R R/I` is computed by the degreewise reduction `FP` of `P`.
  let e : DerivedCategory.Q.obj FP ≅ Dq.functor.obj C :=
    (asIso (Dq.comparison.app P)).symm ≪≫ Dq.functor.mapIso (asIso α)
  have hFP : IsZero (FP.homology n) :=
    ((DerivedCategory.homologyFunctor _ n).map_isZero (hDq.of_iso e)).of_iso
      (homologyQObjIso FP n).symm
  have hP1 : IsZero (P.X (n + 1)) := P.isZero_of_isStrictlyLE n (n + 1) (by omega)
  have hFepi : Epi (F.map (P.d (n - 1) n)) :=
    (isZero_homology_iff_epi_d_of_isZero FP n (F.map_isZero hP1)).1 hFP
  have := (hP n).1
  have hepi : Epi (P.d (n - 1) n) := epi_of_epi_extendScalars_quotient_map hI _ hFepi
  have hPn : IsZero (P.homology n) := (isZero_homology_iff_epi_d_of_isZero P n hP1).2 hepi
  exact (hPn.of_iso (homologyQObjIso P n)).of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso (asIso α)).symm

/-- **Derived Nakayama lemma**, in any models. Let `I` lie in the Jacobson radical of `R`. A
pseudo-coherent object `C` of `D(R)` whose derived reduction `C ⊗ᴸ_R R/I` vanishes is zero. -/
theorem IsPseudoCoherentIn.isZero_of_isZero_derivedExtensionScalars_quotient
    (hI : I ≤ Ideal.jacobson ⊥)
    (Dq : TotalDerivedExtensionScalars.{u, v, u, wR, wA} (Ideal.Quotient.mk I))
    {C : DerivedCategory (ModuleCat.{max v u} R)} (hC : IsPseudoCoherentIn C)
    (hDq : IsZero (Dq.functor.obj C)) :
    IsZero C := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hC
  obtain ⟨b, hb⟩ := hE.upperBound
  have : C.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e b
  have hstep : ∀ k : ℕ, ∀ i : ℤ, b - k < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj C) := by
    intro k
    induction k with
    | zero => exact fun i hi => DerivedCategory.isZero_of_isLE C b i (by simpa using hi)
    | succ k ih =>
      intro i hi
      by_cases hik : b - k < i
      · exact ih i hik
      · obtain rfl : i = b - k := by push_cast at hi; omega
        exact IsPseudoCoherentIn.isZero_homology_of_isZero_derivedExtensionScalars_quotient
          hI Dq ⟨E, hE, ⟨e⟩⟩ hDq _ ih
  have hall : ∀ i : ℤ,
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj C) := fun i =>
    hstep (b - i + 1).toNat i (by omega)
  have : IsIso (0 : (0 : DerivedCategory (ModuleCat.{max v u} R)) ⟶ C) := by
    rw [DerivedCategory.isIso_iff]
    intro i
    exact ((DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _)).isIso (hall i) _
  exact (isZero_zero _).of_iso (asIso (0 : (0 : DerivedCategory (ModuleCat.{max v u} R)) ⟶ C)).symm

/-- **Derived reduction modulo an ideal in the Jacobson radical detects isomorphisms of
pseudo-coherent objects**, in any models. If `f : K ⟶ L` is a morphism of pseudo-coherent
objects of `D(R)` and `f ⊗ᴸ_R R/I` is an isomorphism, then `f` is an isomorphism. -/
theorem IsPseudoCoherentIn.isIso_of_isIso_derivedExtensionScalars_quotient_map
    (hI : I ≤ Ideal.jacobson ⊥)
    (Dq : TotalDerivedExtensionScalars.{u, v, u, wR, wA} (Ideal.Quotient.mk I))
    {K L : DerivedCategory (ModuleCat.{max v u} R)} (hK : IsPseudoCoherentIn K)
    (hL : IsPseudoCoherentIn L) (f : K ⟶ L) (hf : IsIso (Dq.functor.map f)) :
    IsIso f := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle f
  have hC : IsPseudoCoherentIn C :=
    IsPseudoCoherentIn.obj₃_of_distinguished (Triangle.mk f g h) hT hK hL
  have hDC : IsZero (Dq.functor.obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _ (Dq.functor.map_distinguished _ hT)).2 hf
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (hC.isZero_of_isZero_derivedExtensionScalars_quotient hI Dq hDC)

end ExtensionScalars

end StacksDraft.PseudoCoherence
