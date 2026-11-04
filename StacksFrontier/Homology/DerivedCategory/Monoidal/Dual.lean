module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.Homology.HomComplex.Evaluation
public import StacksFrontier.Homology.HomComplex.KoszulBraiding
public import StacksFrontier.Homology.Perfect.Characterizing
public import StacksFrontier.Homology.Perfect.Duality
import StacksCore.Tactic.StacksAttribute

/-!
# Dualizable objects in the derived category

An object of the derived category of a commutative ring admits a left dual exactly when it is
perfect. For a perfect object the derived dual `RHom(M, R)` is a left dual, and every left dual
is isomorphic to it.

## Main definitions

* `DerivedCategory.Invertible.DerivedLeftDualPairing`: a left-dual pairing for the canonical
  derived tensor product -- a coevaluation, an evaluation, and the two triangle identities.
* `DerivedCategory.Invertible.derivedTensorRightUnitor`: the right unitor of the canonical
  derived tensor product, obtained from its symmetry and its left unitor.

## Main results

* `DerivedCategory.Invertible.isPerfect_iff_exists_leftDual` ([stacks 0FNS]): an object admits a
  left-dual pairing if and only if it is perfect; a perfect object is paired with its derived
  dual; and any object paired with it is isomorphic to that derived dual.

## Implementation notes

The unbounded derived tensor product is available as the explicit canonical adjunction data of
[stacks 0A63] rather than as a `MonoidalCategory` instance on all of `D(R)`, so
`DerivedLeftDualPairing` spells out Mathlib's `ExactPairing` for that data: the associator and
the left unitor are the canonical ones carried by
`DerivedHomData`, and the right unitor is derived from the symmetry.
As in [stacks 07VI], whose derived dual this consumes, the scalar ring is lifted so that the
module universe stays independent of the ring universe.

The proof follows the source. One direction is the left dual of a bounded complex of finite
projective modules, transported along a K-flat representative; the other direction identifies
objects admitting a pairing with the compact objects of `D(R)`, which are the perfect objects by
[stacks 07LT]. The homogeneous-component formula for the iterated evaluation map of
[stacks 0A60] is what makes the chain-level comparisons computable.

## References

* [Stacks Project, Tag 0FNS](https://stacks.math.columbia.edu/tag/0FNS)
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits StacksDraft.DerivedHom StacksDraft.Perfect
open scoped DirectSum CategoryTheory.Prod

universe u v w

namespace DerivedCategory.Invertible

variable {R : Type u} [CommRing R]
  [HasDerivedCategory.{w} (ModuleCat.{max u v} (ULift.{v} R))]

/-- The canonical right unitor for derived tensor, obtained from symmetry and the canonical left
unitor. -/
public def derivedTensorRightUnitor
    (K : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    (derivedHomData (R := R)).tensor.obj
        (K, unitObject (R := R)) ≅ K :=
  (derivedHomData (R := R)).tensorSwap K (unitObject (R := R)) ≪≫
    (derivedHomData (R := R)).tensorUnitLeft K

/-- A left-dual pairing in the derived category, expressed using the canonical derived tensor
product. Thus `N` is a left dual of `M` when there are maps `R ⟶ M ⊗ᴸ N` and
`N ⊗ᴸ M ⟶ R` satisfying the two triangle identities. -/
public structure DerivedLeftDualPairing
    (M N : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) where
  /-- The coevaluation `R ⟶ M ⊗ᴸ N`. -/
  coevaluation : unitObject (R := R) ⟶
    (derivedHomData (R := R)).tensor.obj (M, N)
  /-- The evaluation `N ⊗ᴸ M ⟶ R`. -/
  evaluation : (derivedHomData (R := R)).tensor.obj (N, M) ⟶
    unitObject (R := R)
  /-- The triangle identity on the dual object. -/
  coevaluation_evaluation :
    (derivedTensorRightUnitor N).inv ≫
        (derivedHomData (R := R)).tensor.map (𝟙 N, coevaluation) ≫
        ((derivedHomData (R := R)).tensorAssoc N M N).inv ≫
        (derivedHomData (R := R)).tensor.map (evaluation, 𝟙 N) ≫
        ((derivedHomData (R := R)).tensorUnitLeft N).hom =
      𝟙 N
  /-- The triangle identity on the original object. -/
  evaluation_coevaluation :
    ((derivedHomData (R := R)).tensorUnitLeft M).inv ≫
        (derivedHomData (R := R)).tensor.map (coevaluation, 𝟙 M) ≫
        ((derivedHomData (R := R)).tensorAssoc M N M).hom ≫
        (derivedHomData (R := R)).tensor.map (𝟙 M, evaluation) ≫
        (derivedTensorRightUnitor M).hom =
      𝟙 M

private theorem isCompactObject_of_injective_postcomp
    {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [∀ J : Type w, PreservesColimitsOfShape (Discrete J) F]
    (P : C) (U : D) [IsCompactObject.{w} U] (η : U ⟶ F.obj P)
    (hη : ∀ Y, Function.Injective (fun f : P ⟶ Y => η ≫ F.map f)) :
    IsCompactObject.{w} P := by
  classical
  constructor
  intro J _ E _
  refine ⟨StacksDraft.Perfect.injective_directSumToHom _ _, ?_⟩
  intro f
  let ι (j : J) := F.map (Sigma.ι E j)
  have hc : IsColimit (Cofan.mk (F.obj (∐ E)) ι) :=
    (isColimitMapCoconeCofanMkEquiv F E (Sigma.ι E))
      (isColimitOfPreserves F (coproductIsCoproduct E))
  obtain ⟨s, a, ha⟩ := StacksDraft.Perfect.exists_sum_cofan_of_isCompactObject U ι hc (η ≫ F.map f)
  let p (j : J) : (∐ E) ⟶ E j := Sigma.desc (Pi.single j (𝟙 (E j)))
  have hproj (j : J) (hj : j ∈ s) : η ≫ F.map f ≫ F.map (p j) = a j := by
    rw [← Category.assoc, ← ha, Preadditive.sum_comp]
    have hterm (i : J) : (a i ≫ ι i) ≫ F.map (p j) =
        if h : i = j then a j else 0 := by
      dsimp [ι, p]
      rw [Category.assoc, ← F.map_comp, Sigma.ι_desc]
      split_ifs with h
      · subst i
        simp
      · rw [Pi.single_eq_of_ne h, F.map_zero, comp_zero]
    simp [hterm, hj]
  refine ⟨∑ j ∈ s, DirectSum.of _ j (f ≫ p j), ?_⟩
  apply hη _
  simp only [map_sum, DirectSum.toAddMonoid_of, Preadditive.rightComp,
    AddMonoidHom.mk'_apply, Functor.map_sum, Functor.map_comp, Category.assoc,
    Preadditive.comp_sum]
  calc
    ∑ j ∈ s, η ≫ F.map f ≫ F.map (p j) ≫ F.map (Sigma.ι E j) =
        ∑ j ∈ s, a j ≫ ι j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← Category.assoc η, ← Category.assoc, Category.assoc η, hproj j hj]
    _ = η ≫ F.map f := ha

private theorem isCompactObject_map_equivalence
    {C : Type*} [Category C] [Preadditive C]
    {D : Type*} [Category D] [Preadditive D]
    (e : C ≌ D) [e.inverse.Additive] (P : C) [IsCompactObject.{w} P] :
    IsCompactObject.{w} (e.functor.obj P) :=
  isCompactObject_of_injective_postcomp e.inverse (e.functor.obj P) P (e.unitIso.app P).hom
    fun _ _ _ h => e.inverse.map_injective ((cancel_epi (e.unitIso.app P).hom).1 h)

section MonoidalPairings

open MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

private theorem snake_evaluation {M N : C} (η : 𝟙_ C ⟶ M ⊗ N) (ε : N ⊗ M ⟶ 𝟙_ C) :
    (((ρ_ N).inv ≫ N ◁ η ≫ (α_ N M N).inv ≫ ε ▷ N ≫ (λ_ N).hom) ▷ M) ≫ ε =
      N ◁ ((λ_ M).inv ≫ η ▷ M ≫ (α_ M N M).hom ≫ M ◁ ε ≫ (ρ_ M).hom) ≫ ε := by
  have he : (ε ▷ (N ⊗ M)) ⊗≫ ε = ((N ⊗ M) ◁ ε) ⊗≫ ε := by
    calc
      _ = (ε ▷ (N ⊗ M)) ≫ (λ_ (N ⊗ M)).hom ≫ ε := by monoidal
      _ = ((N ⊗ M) ◁ ε) ≫ (ρ_ (N ⊗ M)).hom ≫ ε := by
        rw [← leftUnitor_naturality ε, ← rightUnitor_naturality ε, ← Category.assoc,
          ← MonoidalCategory.tensorHom_def, ← Category.assoc, ← MonoidalCategory.tensorHom_def']
        congr 1
        monoidal
      _ = _ := by monoidal
  calc
    _ = 𝟙 (N ⊗ M) ⊗≫ N ◁ η ▷ M ⊗≫ (ε ▷ (N ⊗ M)) ⊗≫ ε := by monoidal
    _ = 𝟙 (N ⊗ M) ⊗≫ N ◁ η ▷ M ⊗≫ ((N ⊗ M) ◁ ε) ⊗≫ ε := by rw [he]
    _ = _ := by monoidal

private theorem coevaluation_evaluation_of_nondegenerate
    {M N : C} (η : 𝟙_ C ⟶ M ⊗ N) (ε : N ⊗ M ⟶ 𝟙_ C)
    (hε : Function.Injective (fun f : N ⟶ N => (f ▷ M) ≫ ε))
    (hη : (λ_ M).inv ≫ η ▷ M ≫ (α_ M N M).hom ≫ M ◁ ε ≫ (ρ_ M).hom = 𝟙 M) :
    (ρ_ N).inv ≫ N ◁ η ≫ (α_ N M N).inv ≫ ε ▷ N ≫ (λ_ N).hom = 𝟙 N := by
  apply hε
  dsimp only
  rw [snake_evaluation, hη]
  simp

end MonoidalPairings

section TensorAdjunction

universe x y z

variable {S : Type x} [CommRing S] [HasDerivedCategory.{z} (ModuleCat.{y} S)]

private def tensorRightAdjunction (d : DerivedHomAdjunction S)
    (N : DerivedCategory (ModuleCat.{y} S)) :
    (Prod.sectL _ N ⋙ d.tensor) ⊣ (Prod.sectR (Opposite.op N) _ ⋙ d.hom) :=
  Adjunction.mkOfHomEquiv {
    homEquiv X Y := (d.homEquiv X N Y).symm.toEquiv
    homEquiv_naturality_left_symm f g := d.homEquiv_naturality_left f g
    homEquiv_naturality_right {X Y Z} f g := by
      change d.tensor.obj (X, N) ⟶ Y at f
      apply (d.homEquiv _ _ _).injective
      change d.homEquiv _ _ _ ((d.homEquiv _ _ _).symm (f ≫ g)) =
        d.homEquiv _ _ _ ((d.homEquiv _ _ _).symm f ≫ d.hom.map (𝟙 (Opposite.op N) ×ₘ g))
      rw [AddEquiv.apply_symm_apply, d.homEquiv_naturality_right, AddEquiv.apply_symm_apply]
  }

private theorem tensorRight_additive (d : DerivedHomAdjunction S)
    (N : DerivedCategory (ModuleCat.{y} S)) :
    (Prod.sectL _ N ⋙ d.tensor).Additive := by
  constructor
  intro X Y f g
  let e := (d.homEquiv Y N (d.tensor.obj (Y, N))).symm (𝟙 _)
  have he (a : X ⟶ Y) :
      d.homEquiv X N (d.tensor.obj (Y, N)) (a ≫ e) = d.tensor.map (a ×ₘ 𝟙 N) := by
    rw [d.homEquiv_naturality_left]
    simp [e]
  show d.tensor.map ((f + g) ×ₘ 𝟙 N) = d.tensor.map (f ×ₘ 𝟙 N) + d.tensor.map (g ×ₘ 𝟙 N)
  rw [← he, ← he, ← he, Preadditive.add_comp, map_add]

/-- Evaluation after whiskering a map into the internal Hom is its transpose. -/
private theorem tensor_map_comp_evaluation (d : DerivedHomAdjunction S)
    {K L M : DerivedCategory (ModuleCat.{y} S)} (f : K ⟶ d.hom.obj (Opposite.op L, M)) :
    d.tensor.map (f ×ₘ 𝟙 L) ≫ d.evaluation L M = d.homEquiv K L M f := by
  rw [DerivedHomAdjunction.evaluation, ← d.homEquiv_naturality_left, Category.comp_id]

private theorem tensorAssoc_inv_naturality (d : DerivedHomAdjunction S)
    {A A' B B' C C' : DerivedCategory (ModuleCat.{y} S)}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') :
    d.tensor.map (f ×ₘ d.tensor.map (g ×ₘ h)) ≫ (d.tensorAssoc A' B' C').inv =
      (d.tensorAssoc A B C).inv ≫ d.tensor.map (d.tensor.map (f ×ₘ g) ×ₘ h) := by
  apply (cancel_mono (d.tensorAssoc A' B' C').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [d.tensorAssoc_naturality, Iso.inv_hom_id_assoc]

private theorem internalCurryMor_transpose_naturality
    (d : DerivedHomAdjunction S)
    {A B C L Z : DerivedCategory (ModuleCat.{y} S)}
    (a : A ⟶ d.hom.obj (Opposite.op L, Z))
    (c : C ⟶ d.hom.obj (Opposite.op B, L)) :
    d.tensor.map (d.tensor.map (a ×ₘ 𝟙 B) ×ₘ c) ≫
        d.homEquiv _ _ Z (d.internalCurryMor B L Z) =
      (d.tensorAssoc A B C).hom ≫
        d.tensor.map (𝟙 A ×ₘ ((d.tensorSwap B C).hom ≫ d.homEquiv C B L c)) ≫
        d.homEquiv A L Z a := by
  dsimp only [DerivedHomAdjunction.internalCurryMor]
  rw [AddEquiv.apply_symm_apply, d.tensorAssoc_naturality_assoc]
  have hswap :
      d.tensor.map (a ×ₘ d.tensor.map (𝟙 B ×ₘ c)) ≫
        d.tensor.map (𝟙 _ ×ₘ (d.tensorSwap B _).hom) =
      d.tensor.map (𝟙 A ×ₘ (d.tensorSwap B C).hom) ≫
        d.tensor.map (a ×ₘ d.tensor.map (c ×ₘ 𝟙 B)) := by
    simp only [d.tensor_map_comp, Category.comp_id, Category.id_comp,
      d.tensorSwap_naturality]
  rw [reassoc_of% hswap]
  rw [← tensor_map_comp_evaluation d a]
  simp only [d.tensor_map_comp_assoc, Category.comp_id, Category.id_comp,
    tensor_map_comp_evaluation d c]

private theorem isPerfect_iff_isCompactObject_of_hasDerivedCategory
    {S : Type x} [CommRing S] [hc : HasDerivedCategory.{z} (ModuleCat.{x} S)]
    (M : DerivedCategory (ModuleCat.{x} S)) :
    IsPerfect M ↔ IsCompactObject.{x} M := by
  let h₀ := HasDerivedCategory.standard (ModuleCat.{x} S)
  let Q₀ := @DerivedCategory.Q (ModuleCat.{x} S) _ _ h₀
  let Q := @DerivedCategory.Q (ModuleCat.{x} S) _ _ hc
  let W := HomologicalComplex.quasiIso (ModuleCat.{x} S) (ComplexShape.up ℤ)
  let e := Localization.uniq Q Q₀ W
  let i : Q ⋙ e.functor ≅ Q₀ := Localization.compUniqFunctor Q Q₀ W
  let := h₀
  have he : @IsPerfect S _ hc M ↔
      @IsPerfect S _ h₀ (e.functor.obj M) := by
    constructor
    · rintro ⟨P, a, b, ha, hb, hfin, hproj, ⟨j⟩⟩
      exact ⟨P, a, b, ha, hb, hfin, hproj, ⟨e.functor.mapIso j ≪≫ i.app P⟩⟩
    · rintro ⟨P, a, b, ha, hb, hfin, hproj, ⟨j⟩⟩
      exact ⟨P, a, b, ha, hb, hfin, hproj,
        ⟨e.functor.preimageIso (j ≪≫ (i.app P).symm)⟩⟩
  rw [he, isPerfect_iff_isCompactObject]
  have hF : e.functor.Additive := by
    let := hc
    exact Functor.additive_of_preserves_binary_products _
  have hG : e.inverse.Additive := by
    let := h₀
    exact Functor.additive_of_preserves_binary_products _
  constructor
  · intro h
    let := hc
    have := h
    let : e.symm.inverse.Additive := hF
    have hcompact : IsCompactObject.{x} (e.inverse.obj (e.functor.obj M)) :=
      isCompactObject_map_equivalence e.symm _
    have : IsCompactObject.{x} ((e.functor ⋙ e.inverse).obj M) := hcompact
    exact isCompactObject_of_injective_postcomp (𝟭 _) M _ (e.unitIso.app M).inv
      (fun _ _ _ h => (cancel_epi (e.unitIso.app M).inv).1 h)
  · intro h
    have := h
    exact isCompactObject_map_equivalence e M

end TensorAdjunction

section TensorModels

open MonoidalCategory

universe x z

variable {S : Type x} [CommRing S] [HasDerivedCategory.{z} (ModuleCat.{x} S)]

omit [HasDerivedCategory.{z} (ModuleCat.{x} S)] in
private theorem complexSwap_symmetry (K L : CochainComplex (ModuleCat.{x} S) ℤ) :
    (Model.complexSwap S K L).hom ≫ (Model.complexSwap S L K).hom = 𝟙 _ := by
  let := CochainComplex.Koszul.koszulSymmetric S
  exact SymmetricCategory.symmetry K L

private theorem tensorSwap_symmetry (d : DerivedHomData S)
    (X Y : DerivedCategory (ModuleCat.{x} S)) :
    (d.tensorSwap X Y).hom ≫ (d.tensorSwap Y X).hom = 𝟙 _ := by
  obtain ⟨K, hK, ⟨i⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative X
  obtain ⟨L, hL, ⟨j⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative Y
  have h : (d.tensorSwap (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫
      (d.tensorSwap (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj K)).hom = 𝟙 _ := by
    apply (cancel_mono (d.tensorIso K L hL).hom).1
    dsimp only [DerivedHomData.tensorIso]
    rw [Category.assoc, d.tensorSwap_comparison L K hL hK,
      ← Category.assoc, d.tensorSwap_comparison K L hK hL, Category.assoc,
      ← Functor.map_comp]
    rw [complexSwap_symmetry]
    have hm := (DerivedCategory.Q (C := ModuleCat.{x} S)).map_id
      (MonoidalCategoryStruct.tensorObj K L)
    rw [hm]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  have : IsIso (d.tensor.map (i.hom ×ₘ j.hom)) :=
    (d.tensor.mapIso (i.prod j)).isIso_hom
  apply (cancel_epi (d.tensor.map (i.hom ×ₘ j.hom))).1
  rw [← Category.assoc, d.tensorSwap_naturality, Category.assoc,
    d.tensorSwap_naturality, ← Category.assoc, h, Category.id_comp, Category.comp_id]

private theorem tensorAssoc_eq_internalCurryMor
    (d : DerivedHomData S)
    (A B C : DerivedCategory (ModuleCat.{x} S)) :
    let L := d.tensor.obj (B, C)
    let Z := d.tensor.obj (A, L)
    let a := (d.homEquiv A L Z).symm (𝟙 Z)
    let c := (d.homEquiv C B L).symm (d.tensorSwap C B).hom
    (d.tensorAssoc A B C).hom =
      d.tensor.map (d.tensor.map (a ×ₘ 𝟙 B) ×ₘ c) ≫
        d.homEquiv _ _ Z (d.internalCurryMor B L Z) := by
  dsimp only
  rw [internalCurryMor_transpose_naturality,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, tensorSwap_symmetry,
    d.tensor_map_id, Category.comp_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem internalCurryMor_precompose_models
    (d : DerivedHomData S)
    (A B C L I : CochainComplex (ModuleCat.{x} S) ℤ)
    (hB : B.KFlat) [L.IsKInjective] [I.IsKInjective]
    (a : A ⟶ CochainComplex.HomComplexR S L I)
    (c : C ⟶ CochainComplex.HomComplexR S B L) :
    let Q := DerivedCategory.Q (C := ModuleCat.{x} S)
    d.tensor.map ((Q.map a ≫ (d.homIso L I).inv) ×ₘ 𝟙 (Q.obj B)) ≫
        d.internalCurryMor (Q.obj B) (Q.obj L) (Q.obj I) ≫
        d.hom.map ((Q.map c ≫ (d.homIso B L).inv).op ×ₘ 𝟙 (Q.obj I)) ≫
        (d.homIso C I).hom =
      (d.tensorIso A B hB).hom ≫ Q.map
        ((a ⊗ₘ 𝟙 B) ≫
          ChainEvaluation.chainEvaluation B L I ≫
          Stacks.HomComplex.TensorHomMap.precomp S C (CochainComplex.HomComplexR S B L) I c ≫
          Stacks.HomComplex.TensorHomMap.postcomp S C I I (𝟙 I)) := by
  dsimp only
  rw [d.internalCurryMor_comparison B L I hB]
  simp only [Category.assoc]
  erw [d.tensor_map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  have ht := d.tensorIso_naturality a (𝟙 B) hB hB
  simp only [DerivedCategory.Q.map_id] at ht
  erw [reassoc_of% ht]
  have hh :
      d.hom.map ((d.homIso B L).hom.op ×ₘ 𝟙 (DerivedCategory.Q.obj I)) ≫
          d.hom.map ((DerivedCategory.Q.map c ≫ (d.homIso B L).inv).op ×ₘ
            𝟙 (DerivedCategory.Q.obj I)) =
        d.hom.map ((DerivedCategory.Q.map c).op ×ₘ 𝟙 (DerivedCategory.Q.obj I)) := by
    rw [← d.hom.map_comp]
    congr 1
    ext <;> simp
  erw [reassoc_of% hh]
  have hn := d.homIso_naturality c (𝟙 I)
  simp only [DerivedCategory.Q.map_id] at hn
  erw [hn, Iso.inv_hom_id_assoc]
  simp only [CategoryTheory.Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem internalCurryMor_transpose_models
    (d : DerivedHomData S)
    (A B C L I : CochainComplex (ModuleCat.{x} S) ℤ)
    (hB : B.KFlat) (hC : C.KFlat) [L.IsKInjective] [I.IsKInjective]
    (a : A ⟶ CochainComplex.HomComplexR S L I)
    (c : C ⟶ CochainComplex.HomComplexR S B L)
    (t : (A ⊗ B) ⊗ C ⟶ I)
    (ht : (a ⊗ₘ 𝟙 B) ≫
        ChainEvaluation.chainEvaluation B L I ≫
        Stacks.HomComplex.TensorHomMap.precomp S C (CochainComplex.HomComplexR S B L) I c ≫
        Stacks.HomComplex.TensorHomMap.postcomp S C I I (𝟙 I) =
      Stacks.HomComplex.TensorHomMap.Phi S (A ⊗ B) C ≫ Stacks.HomComplex.TensorHomMap.postcomp S C
        ((A ⊗ B) ⊗ C) I t) :
    let Q := DerivedCategory.Q (C := ModuleCat.{x} S)
    let a' := Q.map a ≫ (d.homIso L I).inv
    let c' := Q.map c ≫ (d.homIso B L).inv
    d.tensor.map (d.tensor.map (a' ×ₘ 𝟙 (Q.obj B)) ×ₘ c') ≫
        d.homEquiv _ _ (Q.obj I) (d.internalCurryMor (Q.obj B) (Q.obj L) (Q.obj I)) =
      d.tensor.map ((d.tensorIso A B hB).hom ×ₘ 𝟙 (Q.obj C)) ≫
        (d.tensorIso (A ⊗ B) C hC).hom ≫ Q.map t := by
  dsimp only
  let Q := DerivedCategory.Q (C := ModuleCat.{x} S)
  let a' := Q.map a ≫ (d.homIso L I).inv
  let c' := Q.map c ≫ (d.homIso B L).inv
  let f := d.tensor.map (a' ×ₘ 𝟙 (Q.obj B)) ≫
    d.internalCurryMor (Q.obj B) (Q.obj L) (Q.obj I) ≫
    d.hom.map (c'.op ×ₘ 𝟙 (Q.obj I))
  have hf : f = (d.tensorIso A B hB).hom ≫
      (d.homEquiv (Q.obj (A ⊗ B)) (Q.obj C) (Q.obj I)).symm
        ((d.tensorIso (A ⊗ B) C hC).hom ≫ Q.map t) := by
    apply (cancel_mono (d.homIso C I).hom).1
    dsimp only [f, a', c', Q]
    erw [d.homEquiv_symm_map_eq (A ⊗ B) C I hC t]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id, Category.comp_id]
    exact (internalCurryMor_precompose_models d A B C L I hB a c).trans
      (congrArg (fun g => (d.tensorIso A B hB).hom ≫ Q.map g) ht)
  have he : d.homEquiv _ (Q.obj C) (Q.obj I) f =
      d.tensor.map (d.tensor.map (a' ×ₘ 𝟙 (Q.obj B)) ×ₘ c') ≫
        d.homEquiv _ _ (Q.obj I)
          (d.internalCurryMor (Q.obj B) (Q.obj L) (Q.obj I)) := by
    dsimp only [f]
    rw [d.homEquiv_naturality_left, d.homEquiv_dinaturality,
      d.tensor_map_comp_assoc, Category.comp_id, Category.id_comp]
  rw [← he, hf, d.homEquiv_naturality_left, AddEquiv.apply_symm_apply]


open CochainComplex HomComplex HomologicalComplex


omit [HasDerivedCategory.{z} (ModuleCat.{x} S)] in
private theorem postcomp_apply {L I J : CochainComplex (ModuleCat.{x} S) ℤ}
    (f : I ⟶ J) (n : ℤ) (a : Cochain L I n) (p q : ℤ) (h : p + n = q) :
    (((Stacks.HomComplex.TensorHomMap.postcomp S L I J f).f n).hom a).v p q h =
      a.v p q h ≫ f.f q :=
  Cochain.comp_zero_cochain_v _ _ _ _ _

omit [HasDerivedCategory.{z} (ModuleCat.{x} S)] in
private theorem precomp_apply {K L I : CochainComplex (ModuleCat.{x} S) ℤ}
    (f : K ⟶ L) (n : ℤ) (a : Cochain L I n) (p q : ℤ) (h : p + n = q) :
    (((Stacks.HomComplex.TensorHomMap.precomp S K L I f).f n).hom a).v p q h =
      f.f p ≫ a.v p q h :=
  Cochain.zero_cochain_comp_v _ _ _ _ _

omit [HasDerivedCategory.{z} (ModuleCat.{x} S)] in
private theorem tensorHom_apply {K K' L L' : CochainComplex (ModuleCat.{x} S) ℤ}
    (f : K ⟶ K') (g : L ⟶ L') (p q n : ℤ) (h : p + q = n)
    (x : K.X p) (y : L.X q) :
    (f ⊗ₘ g).f n ((ιTensorObj K L p q n h).hom (x ⊗ₜ[S] y)) =
      (ιTensorObj K' L' p q n h).hom ((f.f p).hom x ⊗ₜ[S] (g.f q).hom y) :=
  congrArg (fun k => k.hom (x ⊗ₜ[S] y))
    (CochainComplex.ιTensorObj_tensorHom S f g p q n h)

omit [HasDerivedCategory.{z} (ModuleCat.{x} S)] in
private theorem curry_apply {A L I : CochainComplex (ModuleCat.{x} S) ℤ}
    (f : A ⊗ L ⟶ I) (n : ℤ) (a : A.X n) (p q : ℤ) (h : p + n = q)
    (l : L.X p) :
    (((Stacks.HomComplex.TensorHomMap.Phi S A L ≫ Stacks.HomComplex.TensorHomMap.postcomp S L (A ⊗
      L) I f).f n a).v p q h).hom l =
      f.f q ((ιTensorObj A L n p q (by omega)).hom (a ⊗ₜ[S] l)) := by
  show (((Stacks.HomComplex.TensorHomMap.postcomp S L (A ⊗ L) I f).f n
    (Stacks.HomComplex.TensorHomMap.Phiv S A L n a)).v p q h).hom l = _
  rw [postcomp_apply]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, phiv_v_apply]

omit [HasDerivedCategory.{z} (ModuleCat.{x} S)] in
private theorem curry_apply_components {A L I : CochainComplex (ModuleCat.{x} S) ℤ}
    (f : A ⊗ L ⟶ I) (n : ℤ) (a : A.X n) (p q : ℤ) (h : p + n = q)
    (l : L.X p) :
    (((Stacks.HomComplex.TensorHomMap.postcomp S L (A ⊗ L) I f).f n
      ((Stacks.HomComplex.TensorHomMap.Phi S A L).f n a)).v p q h).hom l =
      f.f q ((ιTensorObj A L n p q (by omega)).hom (a ⊗ₜ[S] l)) :=
  curry_apply f n a p q h l

omit [HasDerivedCategory.{z} (ModuleCat.{x} S)] in
private theorem evaluationToIteratedHomComplex_apply
    (B L I : CochainComplex (ModuleCat.{x} S) ℤ)
    (t r n : ℤ) (h : t + r = n) (a : Cochain L I t) (b : B.X r)
    (s p : ℤ) (hp : s + n = p) (c : Cochain B L s) :
    (((ιTensorObj (HomComplexR S L I) B t r n h ≫
      (ChainEvaluation.chainEvaluation B L I).f n).hom
      (a ⊗ₜ[S] b)).v s p hp).hom c =
        (r * s).negOnePow •
          (a.v (r + s) p (by omega)).hom ((c.v r (r + s) rfl).hom b) := by
  obtain rfl : n = t + r := by omega
  obtain rfl : p = (r + s) + t := by omega
  have he (q s : ℤ) (hs : q - r = s) (c : Cochain B L s) :
      (((ιTensorObj (HomComplexR S L I) B t r (t + r) rfl ≫
        (ChainEvaluation.chainEvaluation B L I).f
          (t + r)).hom (a ⊗ₜ[S] b)).v s (q + t) (by omega)).hom c =
        (r + -q * r).negOnePow •
          (a.v q (q + t) rfl).hom ((c.v r q (by omega)).hom b) := by
    subst s
    exact ChainEvaluation.chainEvaluation_tmul B L I t r (t + r) (q - r) (q + t) q
      rfl (by omega) (by omega) rfl a b c
  have he' := he (r + s) s (by omega) c
  have hs : (r + -(r + s) * r).negOnePow = (r * s).negOnePow := by
    apply (Int.negOnePow_eq_iff _ _).mpr
    refine ⟨-(r * (r - 1) / 2) - r * s, ?_⟩
    have hv : 2 ∣ r * (r - 1) := (Int.even_mul_pred_self r).two_dvd
    have := Int.ediv_mul_cancel hv
    nlinarith
  rwa [hs] at he'


omit [HasDerivedCategory.{z} (ModuleCat.{x} S)] in
private theorem associator_apply (A B C : CochainComplex (ModuleCat.{x} S) ℤ)
    (i j k n : ℤ) (h : i + j + k = n)
    (a : A.X i) (b : B.X j) (c : C.X k) :
    (α_ A B C).hom.f n
      ((ιTensorObj (A ⊗ B) C (i + j) k n h).hom
        ((ιTensorObj A B i j (i + j) rfl).hom (a ⊗ₜ[S] b) ⊗ₜ[S] c)) =
      (ιTensorObj A (B ⊗ C) i (j + k) n (by omega)).hom
        (a ⊗ₜ[S] (ιTensorObj B C j k (j + k) rfl).hom (b ⊗ₜ[S] c)) := by
  have he := ι_mapBifunctorAssociatorX_hom (curriedAssociatorNatIso (ModuleCat S))
    A B C (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    i j k n h
  rw [mapBifunctor₁₂.ι_eq _ _ A B C _ _ i j k (i + j) n rfl h,
    mapBifunctor₂₃.ι_eq _ _ A B C _ _ _ i j k (j + k) n rfl
      (by change i + (j + k) = n; omega)] at he
  exact ConcreteCategory.congr_hom he ((a ⊗ₜ[S] b) ⊗ₜ[S] c)

set_option backward.isDefEq.respectTransparency false in
-- Extensionality reduces the iterated Hom and two total tensor products to homogeneous elements.
omit [HasDerivedCategory.{z} (ModuleCat.{x} S)] in
private theorem evaluationToIteratedHomComplex_curry
    (A B C L I : CochainComplex (ModuleCat.{x} S) ℤ)
    (f : A ⊗ L ⟶ I) (g : C ⊗ B ⟶ L) :
    let a := Stacks.HomComplex.TensorHomMap.Phi S A L ≫ Stacks.HomComplex.TensorHomMap.postcomp S L
      (A ⊗ L) I f
    let c := Stacks.HomComplex.TensorHomMap.Phi S C B ≫ Stacks.HomComplex.TensorHomMap.postcomp S B
      (C ⊗ B) L g
    (a ⊗ₘ 𝟙 B) ≫
        ChainEvaluation.chainEvaluation B L I ≫
        Stacks.HomComplex.TensorHomMap.precomp S C (HomComplexR S B L) I c ≫
        Stacks.HomComplex.TensorHomMap.postcomp S C I I (𝟙 I) =
      Stacks.HomComplex.TensorHomMap.Phi S (A ⊗ B) C ≫ Stacks.HomComplex.TensorHomMap.postcomp S C
        ((A ⊗ B) ⊗ C) I
        ((α_ A B C).hom ≫ (𝟙 A ⊗ₘ ((Model.complexSwap S B C).hom ≫ g)) ≫ f) := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro n
  apply GradedObject.Monoidal.tensorObj_ext
  intro t r htr
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  apply Cochain.ext
  intro s p hsp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [postcomp_apply, precomp_apply]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]
  rw [show GradedObject.Monoidal.ιTensorObj A.X B.X t r n htr =
    ιTensorObj A B t r n htr from rfl]
  erw [tensorHom_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]
  rw [show ((ChainEvaluation.chainEvaluation B L I).f n
    ((ιTensorObj (HomComplexR S L I) B t r n htr).hom
      (((Stacks.HomComplex.TensorHomMap.Phi S A L ≫ Stacks.HomComplex.TensorHomMap.postcomp S L (A ⊗
        L) I f).f t).hom a ⊗ₜ[S] b))) =
    (ιTensorObj (HomComplexR S L I) B t r n htr ≫
      (ChainEvaluation.chainEvaluation B L I).f n).hom
      (((Stacks.HomComplex.TensorHomMap.Phi S A L ≫ Stacks.HomComplex.TensorHomMap.postcomp S L (A ⊗
        L) I f).f t).hom a ⊗ₜ[S] b) from rfl]
  rw [evaluationToIteratedHomComplex_apply B L I t r n htr
    ((Stacks.HomComplex.TensorHomMap.Phi S A L ≫ Stacks.HomComplex.TensorHomMap.postcomp S L (A ⊗ L)
      I f).f t a)
    b s p hsp ((Stacks.HomComplex.TensorHomMap.Phi S C B ≫ Stacks.HomComplex.TensorHomMap.postcomp S
      B (C ⊗ B) L g).f s c)]
  rw [curry_apply f t a (r + s) p (by omega), curry_apply g s c r (r + s) rfl b]
  erw [curry_apply_components
    ((α_ A B C).hom ≫ (𝟙 A ⊗ₘ ((Model.complexSwap S B C).hom ≫ g)) ≫ f)
    n ((ιTensorObj A B t r n htr).hom (a ⊗ₜ[S] b)) s p hsp c]
  subst n
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [associator_apply, tensorHom_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply,
    HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [complexSwap_apply]
  simp only [map_zsmul_unit, TensorProduct.tmul_smul]


omit [HasDerivedCategory.{z} (ModuleCat.{x} S)] in
private theorem curry_precomp
    (A B L I : CochainComplex (ModuleCat.{x} S) ℤ)
    (l : B ⟶ L) (f : A ⊗ L ⟶ I) :
    (Stacks.HomComplex.TensorHomMap.Phi S A L ≫ Stacks.HomComplex.TensorHomMap.postcomp S L (A ⊗ L)
      I f) ≫
        Stacks.HomComplex.TensorHomMap.precomp S B L I l ≫ Stacks.HomComplex.TensorHomMap.postcomp S
          B I I (𝟙 I) =
      Stacks.HomComplex.TensorHomMap.Phi S A B ≫ Stacks.HomComplex.TensorHomMap.postcomp S B (A ⊗ B)
        I ((𝟙 A ⊗ₘ l) ≫ f) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [postcomp_apply, precomp_apply]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, HomologicalComplex.id_f,
    ModuleCat.hom_id, LinearMap.id_apply]
  rw [curry_apply_components f n a p q hpq ((l.f p).hom b),
    curry_apply_components ((𝟙 A ⊗ₘ l) ≫ f) n a p q hpq b]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [tensorHom_apply]
  rfl

private theorem homEquiv_curry_precomp_models
    (d : DerivedHomData S)
    (A B L I : CochainComplex (ModuleCat.{x} S) ℤ) (hB : B.KFlat)
    [L.IsKInjective] [I.IsKInjective] (l : B ⟶ L) (f : A ⊗ L ⟶ I) :
    let Q := DerivedCategory.Q (C := ModuleCat.{x} S)
    let a := Stacks.HomComplex.TensorHomMap.Phi S A L ≫ Stacks.HomComplex.TensorHomMap.postcomp S L
      (A ⊗ L) I f
    d.tensor.map (𝟙 (Q.obj A) ×ₘ Q.map l) ≫
        d.homEquiv (Q.obj A) (Q.obj L) (Q.obj I) (Q.map a ≫ (d.homIso L I).inv) =
      (d.tensorIso A B hB).hom ≫ Q.map ((𝟙 A ⊗ₘ l) ≫ f) := by
  dsimp only
  let Q := DerivedCategory.Q (C := ModuleCat.{x} S)
  let a := Stacks.HomComplex.TensorHomMap.Phi S A L ≫ Stacks.HomComplex.TensorHomMap.postcomp S L (A
    ⊗ L) I f
  rw [← d.homEquiv_dinaturality]
  apply (d.homEquiv (Q.obj A) (Q.obj B) (Q.obj I)).symm.injective
  erw [AddEquiv.symm_apply_apply, d.homEquiv_symm_map_eq A B I hB]
  show (Q.map a ≫ (d.homIso L I).inv) ≫
      d.hom.map ((Q.map l).op ×ₘ 𝟙 (Q.obj I)) =
    Q.map (Stacks.HomComplex.TensorHomMap.Phi S A B ≫
      Stacks.HomComplex.TensorHomMap.postcomp S B (A ⊗ B) I ((𝟙 A ⊗ₘ l) ≫ f)) ≫ (d.homIso B I).inv
  apply (cancel_mono (d.homIso B I).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := d.homIso_naturality l (𝟙 I)
  simp only [DerivedCategory.Q.map_id] at hn
  rw [hn, Iso.inv_hom_id_assoc]
  simpa only [Q, a, Functor.map_comp, Category.assoc] using
    congrArg Q.map (curry_precomp A B L I l f)


private theorem isIso_Q_tensorLeft (d : DerivedHomData S)
    (A : CochainComplex (ModuleCat.{x} S) ℤ) (hA : A.KFlat)
    {B C : CochainComplex (ModuleCat.{x} S) ℤ} (f : B ⟶ C) [QuasiIso f] :
    IsIso (DerivedCategory.Q.map (𝟙 A ⊗ₘ f)) := by
  let Q := DerivedCategory.Q (C := ModuleCat.{x} S)
  have : IsIso (d.tensor.map (Q.map f ×ₘ Q.map (𝟙 A))) :=
    (d.tensor.mapIso ((asIso (Q.map f)).prod (asIso (Q.map (𝟙 A))))).isIso_hom
  have : IsIso ((d.tensorIso B A hA).hom ≫ Q.map (f ⊗ₘ 𝟙 A)) := by
    rw [← d.tensorIso_naturality f (𝟙 A) hA hA]
    infer_instance
  have : IsIso (Q.map (f ⊗ₘ 𝟙 A)) := IsIso.of_isIso_comp_left (d.tensorIso B A hA).hom _
  let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory S).choose
  have hb := congrArg Q.map (BraidedCategory.braiding_naturality (𝟙 A) f)
  simp only [Q.map_comp] at hb
  have : IsIso (Q.map (𝟙 A ⊗ₘ f) ≫ Q.map (β_ A C).hom) := by
    rw [hb]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Q.map (β_ A C).hom)

private theorem tensorAssoc_comparison (d : DerivedHomData S)
    (A B C : CochainComplex (ModuleCat.{x} S) ℤ)
    (hA : A.KFlat) (hB : B.KFlat) (hC : C.KFlat) :
    let Q := DerivedCategory.Q (C := ModuleCat.{x} S)
    (d.tensorAssoc (Q.obj A) (Q.obj B) (Q.obj C)).hom ≫
        d.tensor.map (𝟙 (Q.obj A) ×ₘ (d.tensorIso B C hC).hom) ≫
        (d.tensorIso A (B ⊗ C) (CochainComplex.KFlat.tensor S B C hB hC)).hom =
      d.tensor.map ((d.tensorIso A B hB).hom ×ₘ 𝟙 (Q.obj C)) ≫
        (d.tensorIso (A ⊗ B) C hC).hom ≫ Q.map (α_ A B C).hom := by
  dsimp only
  let Q := DerivedCategory.Q (C := ModuleCat.{x} S)
  obtain ⟨L, l, hl, hL⟩ := CochainComplex.exists_quasiIso_isKInjective (B ⊗ C)
  obtain ⟨I, f, hf, hI⟩ := CochainComplex.exists_quasiIso_isKInjective (A ⊗ L)
  let a := Stacks.HomComplex.TensorHomMap.Phi S A L ≫ Stacks.HomComplex.TensorHomMap.postcomp S L (A
    ⊗ L) I f
  let g := (Model.complexSwap S C B).hom ≫ l
  let c := Stacks.HomComplex.TensorHomMap.Phi S C B ≫ Stacks.HomComplex.TensorHomMap.postcomp S B (C
    ⊗ B) L g
  let a' := Q.map a ≫ (d.homIso L I).inv
  let c' := Q.map c ≫ (d.homIso B L).inv
  have hc : d.homEquiv (Q.obj C) (Q.obj B) (Q.obj L) c' =
      (d.tensorIso C B hB).hom ≫ Q.map g := by
    apply (d.homEquiv (Q.obj C) (Q.obj B) (Q.obj L)).symm.injective
    erw [AddEquiv.symm_apply_apply, d.homEquiv_symm_map_eq C B L hB]
    rfl
  have hg : (Model.complexSwap S B C).hom ≫ g = l := by
    dsimp only [g]
    rw [← Category.assoc, complexSwap_symmetry, Category.id_comp]
  have hs : (d.tensorSwap (Q.obj B) (Q.obj C)).hom ≫
      d.homEquiv (Q.obj C) (Q.obj B) (Q.obj L) c' =
        (d.tensorIso B C hC).hom ≫ Q.map l := by
    rw [hc, ← Category.assoc]
    erw [d.tensorSwap_comparison B C hB hC]
    rw [Category.assoc, ← Q.map_comp, hg]
    rfl
  have he := internalCurryMor_transpose_models d A B C L I hB hC a c
    ((α_ A B C).hom ≫ (𝟙 A ⊗ₘ ((Model.complexSwap S B C).hom ≫ g)) ≫ f)
    (evaluationToIteratedHomComplex_curry A B C L I f g)
  change d.tensor.map (d.tensor.map (a' ×ₘ 𝟙 (Q.obj B)) ×ₘ c') ≫ _ = _ at he
  rw [internalCurryMor_transpose_naturality, hs] at he
  have ha := homEquiv_curry_precomp_models d A (B ⊗ C) L I
    (CochainComplex.KFlat.tensor S B C hB hC) l f
  change d.tensor.map (𝟙 (Q.obj A) ×ₘ Q.map l) ≫
    d.homEquiv (Q.obj A) (Q.obj L) (Q.obj I) a' = _ at ha
  rw [show d.tensor.map (𝟙 (Q.obj A) ×ₘ ((d.tensorIso B C hC).hom ≫ Q.map l)) =
      d.tensor.map (𝟙 (Q.obj A) ×ₘ (d.tensorIso B C hC).hom) ≫
        d.tensor.map (𝟙 (Q.obj A) ×ₘ Q.map l) by
      rw [d.tensor_map_comp, Category.id_comp], Category.assoc, ha, hg] at he
  have : IsIso (Q.map (𝟙 A ⊗ₘ l)) := isIso_Q_tensorLeft d A hA l
  have : IsIso (Q.map ((𝟙 A ⊗ₘ l) ≫ f)) := by
    rw [Q.map_comp]
    infer_instance
  apply (cancel_mono (Q.map ((𝟙 A ⊗ₘ l) ≫ f))).1
  simpa only [Functor.map_comp, Category.assoc] using he


/-- A K-flat model of a derived object. -/
private structure TensorRepresentative (X : DerivedCategory (ModuleCat.{x} S)) where
  complex : CochainComplex (ModuleCat.{x} S) ℤ
  flat : complex.KFlat
  iso : X ≅ DerivedCategory.Q.obj complex

private def tensorRepresentative (X : DerivedCategory (ModuleCat.{x} S)) :
    TensorRepresentative X := by
  let h := CochainComplex.KFlat.exists_kFlat_representative X
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.some.symm⟩

private abbrev TensorRepresentative.tensor (d : DerivedHomData S)
    {X Y : DerivedCategory (ModuleCat.{x} S)}
    (A : TensorRepresentative X) (B : TensorRepresentative Y) :
    TensorRepresentative (d.tensor.obj (X, Y)) where
  complex := A.complex ⊗ B.complex
  flat := CochainComplex.KFlat.tensor S _ _ A.flat B.flat
  iso := d.tensor.mapIso (A.iso.prod B.iso) ≪≫ d.tensorIso _ _ B.flat

private abbrev unitRepresentative : TensorRepresentative
    (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{x} S) ℤ))) where
  complex := 𝟙_ _
  flat := DerivedHomData.unit_kFlat
  iso := Iso.refl _

private def Represents {X Y : DerivedCategory (ModuleCat.{x} S)}
    (A : TensorRepresentative X) (B : TensorRepresentative Y)
    (f : X ⟶ Y) (g : A.complex ⟶ B.complex) : Prop :=
  f ≫ B.iso.hom = A.iso.hom ≫ DerivedCategory.Q.map g

private theorem Represents.id {X : DerivedCategory (ModuleCat.{x} S)}
    (A : TensorRepresentative X) : Represents A A (𝟙 X) (𝟙 A.complex) := by
  simp [Represents]

private theorem Represents.comp {X Y Z : DerivedCategory (ModuleCat.{x} S)}
    {A : TensorRepresentative X} {B : TensorRepresentative Y} {C : TensorRepresentative Z}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : A.complex ⟶ B.complex} {g' : B.complex ⟶ C.complex}
    (hf : Represents A B f f') (hg : Represents B C g g') :
    Represents A C (f ≫ g) (f' ≫ g') := by
  dsimp only [Represents] at *
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc, Functor.map_comp]

private theorem Represents.eq {X Y : DerivedCategory (ModuleCat.{x} S)}
    {A : TensorRepresentative X} {B : TensorRepresentative Y}
    {f g : X ⟶ Y} {f' g' : A.complex ⟶ B.complex}
    (hf : Represents A B f f') (hg : Represents A B g g') (h : f' = g') : f = g := by
  subst h
  exact (cancel_mono B.iso.hom).1 (hf.trans hg.symm)

private theorem Represents.tensor (d : DerivedHomData S)
    {X Y X' Y' : DerivedCategory (ModuleCat.{x} S)}
    {A : TensorRepresentative X} {B : TensorRepresentative Y}
    {A' : TensorRepresentative X'} {B' : TensorRepresentative Y'}
    {f : X ⟶ X'} {g : Y ⟶ Y'} {f' : A.complex ⟶ A'.complex} {g' : B.complex ⟶ B'.complex}
    (hf : Represents A A' f f') (hg : Represents B B' g g') :
    Represents (A.tensor d B) (A'.tensor d B') (d.tensor.map (f ×ₘ g)) (f' ⊗ₘ g') := by
  dsimp only [Represents] at hf hg
  simp only [Represents, TensorRepresentative.tensor, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom]
  rw [← Category.assoc, d.tensor_map_comp, hf, hg, ← d.tensor_map_comp, Category.assoc,
    Category.assoc, d.tensorIso_naturality]

private theorem Represents.associator (d : DerivedHomData S)
    {X Y Z : DerivedCategory (ModuleCat.{x} S)}
    (A : TensorRepresentative X) (B : TensorRepresentative Y) (C : TensorRepresentative Z) :
    Represents ((A.tensor d B).tensor d C) (A.tensor d (B.tensor d C))
      (d.tensorAssoc X Y Z).hom (α_ A.complex B.complex C.complex).hom := by
  simp only [Represents, TensorRepresentative.tensor, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom]
  rw [show d.tensor.map (A.iso.hom ×ₘ
      (d.tensor.map (B.iso.hom ×ₘ C.iso.hom) ≫ (d.tensorIso B.complex C.complex C.flat).hom)) =
      d.tensor.map (A.iso.hom ×ₘ d.tensor.map (B.iso.hom ×ₘ C.iso.hom)) ≫
        d.tensor.map (𝟙 _ ×ₘ (d.tensorIso B.complex C.complex C.flat).hom) by
      rw [d.tensor_map_comp, Category.comp_id]]
  rw [show d.tensor.map ((d.tensor.map (A.iso.hom ×ₘ B.iso.hom) ≫
      (d.tensorIso A.complex B.complex B.flat).hom) ×ₘ C.iso.hom) =
      d.tensor.map (d.tensor.map (A.iso.hom ×ₘ B.iso.hom) ×ₘ C.iso.hom) ≫
        d.tensor.map ((d.tensorIso A.complex B.complex B.flat).hom ×ₘ 𝟙 _) by
      rw [d.tensor_map_comp, Category.comp_id]]
  simp only [Category.assoc]
  rw [← d.tensorAssoc_naturality_assoc,
    tensorAssoc_comparison d A.complex B.complex C.complex A.flat B.flat C.flat]

private theorem Represents.rightUnitor (d : DerivedHomData S)
    {X : DerivedCategory (ModuleCat.{x} S)} (A : TensorRepresentative X) :
    Represents (A.tensor d unitRepresentative) A (d.tensorRightUnitor.app X).hom
      (ρ_ A.complex).hom := by
  simp only [Represents, TensorRepresentative.tensor, unitRepresentative, Iso.trans_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  rw [Category.assoc, ← d.tensorRightUnitor_comparison]
  exact (d.tensorRightUnitor.hom.naturality A.iso.hom).symm

private theorem Represents.leftUnitor (d : DerivedHomData S)
    {X : DerivedCategory (ModuleCat.{x} S)} (A : TensorRepresentative X) :
    Represents (unitRepresentative.tensor d A) A (d.tensorUnitLeft X).hom
      (λ_ A.complex).hom := by
  simp only [Represents, TensorRepresentative.tensor, unitRepresentative, Iso.trans_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  rw [Category.assoc, d.tensorUnitLeft_comparison]
  exact (d.tensorUnitLeft_naturality A.iso.hom).symm

private theorem tensor_pentagon (d : DerivedHomData S)
    (W X Y Z : DerivedCategory (ModuleCat.{x} S)) :
    d.tensor.map ((d.tensorAssoc W X Y).hom ×ₘ 𝟙 Z) ≫
        (d.tensorAssoc W (d.tensor.obj (X, Y)) Z).hom ≫
        d.tensor.map (𝟙 W ×ₘ (d.tensorAssoc X Y Z).hom) =
      (d.tensorAssoc (d.tensor.obj (W, X)) Y Z).hom ≫
        (d.tensorAssoc W X (d.tensor.obj (Y, Z))).hom := by
  let A := tensorRepresentative W
  let B := tensorRepresentative X
  let C := tensorRepresentative Y
  let E := tensorRepresentative Z
  apply Represents.eq
    (((Represents.associator d A B C).tensor d (Represents.id E)).comp
      ((Represents.associator d A (B.tensor d C) E).comp
        ((Represents.id A).tensor d (Represents.associator d B C E))))
    ((Represents.associator d (A.tensor d B) C E).comp
      (Represents.associator d A B (C.tensor d E)))
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
    MonoidalCategory.pentagon A.complex B.complex C.complex E.complex

private theorem tensor_triangle (d : DerivedHomData S)
    (X Y : DerivedCategory (ModuleCat.{x} S)) :
    (d.tensorAssoc X (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{x} S) ℤ))) Y).hom ≫
      d.tensor.map (𝟙 X ×ₘ (d.tensorUnitLeft Y).hom) =
        d.tensor.map ((d.tensorRightUnitor.app X).hom ×ₘ 𝟙 Y) := by
  let A := tensorRepresentative X
  let B := tensorRepresentative Y
  apply Represents.eq
    ((Represents.associator d A unitRepresentative B).comp
      ((Represents.id A).tensor d (Represents.leftUnitor d B)))
    ((Represents.rightUnitor d A).tensor d (Represents.id B))
  simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
    MonoidalCategory.triangle A.complex B.complex

private abbrev derivedMonoidalStruct (d : DerivedHomData S) :
    MonoidalCategoryStruct (DerivedCategory (ModuleCat.{x} S)) where
  tensorObj X Y := d.tensor.obj (X, Y)
  whiskerLeft X _ _ g := d.tensor.map (𝟙 X ×ₘ g)
  whiskerRight f Y := d.tensor.map (f ×ₘ 𝟙 Y)
  tensorHom f g := d.tensor.map (f ×ₘ g)
  tensorUnit := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{x} S) ℤ))
  associator := d.tensorAssoc
  rightUnitor X := d.tensorRightUnitor.app X
  leftUnitor := d.tensorUnitLeft

@[instance_reducible]
private def derivedMonoidalCategory (d : DerivedHomData S) :
    MonoidalCategory (DerivedCategory (ModuleCat.{x} S)) := by
  letI := derivedMonoidalStruct d
  apply MonoidalCategory.ofTensorHom
  · exact d.tensor_map_id
  · exact fun X {Y₁ Y₂} f => rfl
  · exact fun {X₁ X₂} f Y => rfl
  · exact fun f g h k => d.tensor_map_comp f g h k
  · exact d.tensorAssoc_naturality
  · exact d.tensorUnitLeft_naturality
  · exact fun f => d.tensorRightUnitor.hom.naturality f
  · exact tensor_pentagon d
  · exact tensor_triangle d

end TensorModels

private theorem derivedTensorRightUnitor_eq
    (X : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    (derivedTensorRightUnitor X).hom =
      ((derivedHomData (R := R)).tensorRightUnitor.app X).hom := by
  dsimp only [derivedTensorRightUnitor, DerivedHomData.tensorUnitLeft,
    Iso.trans_hom]
  rw [← Category.assoc, tensorSwap_symmetry, Category.id_comp]

private theorem derivedTensorRightUnitor_naturality
    {X Y : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : X ⟶ Y) :
    (derivedHomData (R := R)).tensor.map
        (f, 𝟙 (unitObject (R := R))) ≫ (derivedTensorRightUnitor Y).hom =
      (derivedTensorRightUnitor X).hom ≫ f := by
  dsimp only [derivedTensorRightUnitor, Iso.trans_hom]
  rw [(derivedHomData (R := R)).tensorSwap_naturality_assoc,
    (derivedHomData (R := R)).tensorUnitLeft_naturality]
  simp only [Category.assoc]

private theorem derivedTensorRightUnitor_inv_naturality
    {X Y : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))} (f : X ⟶ Y) :
    f ≫ (derivedTensorRightUnitor Y).inv = (derivedTensorRightUnitor X).inv ≫
      (derivedHomData (R := R)).tensor.map (f ×ₘ 𝟙 (unitObject (R := R))) := by
  apply (cancel_mono (derivedTensorRightUnitor Y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [derivedTensorRightUnitor_naturality, Iso.inv_hom_id_assoc]

private theorem pairing_coevaluation_postcomp
    {M N Y : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))}
    (p : DerivedLeftDualPairing M N) (f : M ⟶ Y) :
    let d := derivedHomData (R := R)
    ((derivedHomData (R := R)).tensorUnitLeft M).inv ≫
        d.tensor.map ((p.coevaluation ≫ d.tensor.map (f ×ₘ 𝟙 N)) ×ₘ 𝟙 M) ≫
        (d.tensorAssoc Y N M).hom ≫ d.tensor.map (𝟙 Y ×ₘ p.evaluation) ≫
        (derivedTensorRightUnitor Y).hom = f := by
  dsimp only
  let d := derivedHomData (R := R)
  show _ ≫ d.tensor.map ((p.coevaluation ≫ d.tensor.map (f ×ₘ 𝟙 N)) ×ₘ 𝟙 M) ≫ _ = _
  rw [show d.tensor.map ((p.coevaluation ≫ d.tensor.map (f ×ₘ 𝟙 N)) ×ₘ 𝟙 M) =
    d.tensor.map (p.coevaluation ×ₘ 𝟙 M) ≫
      d.tensor.map (d.tensor.map (f ×ₘ 𝟙 N) ×ₘ 𝟙 M) by
        rw [d.tensor_map_comp, Category.id_comp]]
  simp only [Category.assoc]
  rw [d.tensorAssoc_naturality_assoc f (𝟙 N) (𝟙 M), d.tensor_map_id]
  have hmap : d.tensor.map (f ×ₘ 𝟙 (d.tensor.obj (N, M))) ≫ d.tensor.map (𝟙 Y ×ₘ p.evaluation) =
      d.tensor.map (𝟙 M ×ₘ p.evaluation) ≫ d.tensor.map (f ×ₘ 𝟙 _) := by
        simp only [d.tensor_map_comp, Category.comp_id, Category.id_comp]
  rw [reassoc_of% hmap]
  rw [derivedTensorRightUnitor_naturality]
  simpa only [Category.assoc, Category.id_comp] using
    congrArg (fun g => g ≫ f) p.evaluation_coevaluation

private theorem pairing_coevaluation_postcomp_injective
    {M N : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))}
    (p : DerivedLeftDualPairing M N)
    (Y : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    Function.Injective (fun f : M ⟶ Y => p.coevaluation ≫
      (derivedHomData (R := R)).tensor.map (f ×ₘ 𝟙 N)) := by
  intro f g h
  dsimp only at h
  rw [← pairing_coevaluation_postcomp p f, ← pairing_coevaluation_postcomp p g, h]

private theorem isPerfect_unitObject :
    IsPerfect (unitObject (R := R)) := by
  refine ⟨unitComplex (R := R), 0, 0,
    ?_, ?_, ?_, ?_, ⟨Iso.refl _⟩⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro i
    by_cases h : i = 0
    · subst i
      exact Module.Finite.equiv
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of (ULift.{v} R) (ULift.{v} R))).toLinearEquiv.symm
    · have : Subsingleton ((unitComplex (R := R)).X i) :=
        ModuleCat.isZero_iff_subsingleton.mp (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
      infer_instance
  · intro i
    by_cases h : i = 0
    · subst i
      exact Module.Projective.of_equiv
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of (ULift.{v} R) (ULift.{v} R))).toLinearEquiv.symm
    · have : Subsingleton ((unitComplex (R := R)).X i) :=
        ModuleCat.isZero_iff_subsingleton.mp (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
      infer_instance

private theorem isPerfect_of_pairing
    {M N : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))}
    (p : DerivedLeftDualPairing M N) : IsPerfect M := by
  apply (isPerfect_iff_isCompactObject_of_hasDerivedCategory M).mpr
  have : IsCompactObject.{max u v} (unitObject (R := R)) :=
    (isPerfect_iff_isCompactObject_of_hasDerivedCategory _).mp isPerfect_unitObject
  let d := (derivedHomData (R := R)).toDerivedHomAdjunction
  have : (Prod.sectL _ N ⋙ d.tensor).Additive := tensorRight_additive d N
  have : (Prod.sectL _ N ⋙ d.tensor).IsLeftAdjoint := (tensorRightAdjunction d N).isLeftAdjoint
  exact isCompactObject_of_injective_postcomp (Prod.sectL _ N ⋙ d.tensor) M
    (unitObject (R := R)) p.coevaluation (pairing_coevaluation_postcomp_injective p)

private theorem exists_coevaluation_of_isPerfect
    (M : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (hM : IsPerfect M) :
    let d := derivedHomData (R := R)
    let N := derivedDual M
    ∃ η : unitObject (R := R) ⟶ d.tensor.obj (M, N),
      ((derivedHomData (R := R)).tensorUnitLeft M).inv ≫
        d.tensor.map (η ×ₘ 𝟙 M) ≫ (d.tensorAssoc M N M).hom ≫
        d.tensor.map (𝟙 M ×ₘ d.evaluation M (unitObject (R := R))) ≫
        (derivedTensorRightUnitor M).hom = 𝟙 M := by
  let d := derivedHomData (R := R)
  let c := derivedHomData (R := R)
  let U := unitObject (R := R)
  have : IsIso (tensorDualHom M M) :=
    (isPerfect_derivedDual_and_naturalIsos M hM).tensorDualHom_isIso M
  let η := (d.homEquiv U M M).symm (c.tensorUnitLeft M).hom ≫
    inv (tensorDualHom M M)
  refine ⟨η, ?_⟩
  have hη : η ≫ tensorDualHom M M =
      (d.homEquiv U M M).symm (c.tensorUnitLeft M).hom := by
    simp [η]
  have ht : d.homEquiv U M M (η ≫ tensorDualHom M M) =
      d.tensor.map (η ×ₘ 𝟙 M) ≫ (d.tensorAssoc M (derivedDual M) M).hom ≫
        d.tensor.map (𝟙 M ×ₘ d.evaluation M U) ≫ (derivedTensorRightUnitor M).hom := by
    rw [d.homEquiv_naturality_left]
    dsimp only [tensorDualHom, derivedTensorRightUnitor, Iso.trans_hom]
    rw [AddEquiv.apply_symm_apply]
  show (c.tensorUnitLeft M).inv ≫ _ = 𝟙 M
  rw [← ht, hη, AddEquiv.apply_symm_apply, Iso.inv_hom_id]

private theorem nonempty_iso_of_pairing_compatible
    {M N P : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))}
    (p : DerivedLeftDualPairing M N) (q : DerivedLeftDualPairing M P)
    (f : N ⟶ P)
    (hη : p.coevaluation ≫ (derivedHomData (R := R)).tensor.map
      (𝟙 M ×ₘ f) = q.coevaluation)
    (hε : (derivedHomData (R := R)).tensor.map (f ×ₘ 𝟙 M) ≫
      q.evaluation = p.evaluation) : Nonempty (N ≅ P) := by
  let d := (derivedHomData (R := R)).toDerivedHomAdjunction
  let c := derivedHomData (R := R)
  let U := unitObject (R := R)
  let g : P ⟶ N := (derivedTensorRightUnitor P).inv ≫
    d.tensor.map (𝟙 P ×ₘ p.coevaluation) ≫ (d.tensorAssoc P M N).inv ≫
    d.tensor.map (q.evaluation ×ₘ 𝟙 N) ≫ (c.tensorUnitLeft N).hom
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · dsimp only [g]
    rw [← Category.assoc f, derivedTensorRightUnitor_inv_naturality]
    simp only [Category.assoc]
    have h₁ : d.tensor.map (f ×ₘ 𝟙 U) ≫ d.tensor.map (𝟙 P ×ₘ p.coevaluation) =
        d.tensor.map (𝟙 N ×ₘ p.coevaluation) ≫ d.tensor.map (f ×ₘ 𝟙 _) := by
      simp only [d.tensor_map_comp, Category.id_comp, Category.comp_id]
    rw [reassoc_of% h₁]
    have h₂ := tensorAssoc_inv_naturality d f (𝟙 M) (𝟙 N)
    rw [d.tensor_map_id] at h₂
    rw [reassoc_of% h₂]
    have h₃ : d.tensor.map (d.tensor.map (f ×ₘ 𝟙 M) ×ₘ 𝟙 N) ≫
        d.tensor.map (q.evaluation ×ₘ 𝟙 N) = d.tensor.map (p.evaluation ×ₘ 𝟙 N) := by
      rw [d.tensor_map_comp, Category.id_comp, hε]
    rw [reassoc_of% h₃]
    exact p.coevaluation_evaluation
  · dsimp only [g]
    simp only [Category.assoc]
    rw [← c.tensorUnitLeft_naturality f]
    have h₁ : d.tensor.map (q.evaluation ×ₘ 𝟙 N) ≫ d.tensor.map (𝟙 U ×ₘ f) =
        d.tensor.map (𝟙 _ ×ₘ f) ≫ d.tensor.map (q.evaluation ×ₘ 𝟙 P) := by
      dsimp only [U]
      simp only [d.tensor_map_comp, Category.id_comp, Category.comp_id]
    rw [reassoc_of% h₁]
    have h₂ := tensorAssoc_inv_naturality d (𝟙 P) (𝟙 M) f
    rw [d.tensor_map_id] at h₂
    rw [← reassoc_of% h₂]
    have h₃ : d.tensor.map (𝟙 P ×ₘ p.coevaluation) ≫
        d.tensor.map (𝟙 P ×ₘ d.tensor.map (𝟙 M ×ₘ f)) =
        d.tensor.map (𝟙 P ×ₘ q.coevaluation) := by
      rw [d.tensor_map_comp, Category.id_comp, hη]
    rw [reassoc_of% h₃]
    exact q.coevaluation_evaluation

private theorem pairing_coevaluation_tensorHom
    {M N : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))}
    (p : DerivedLeftDualPairing M N) (f : N ⟶ derivedDual M)
    (hf : (derivedHomData (R := R)).tensor.map (f ×ₘ 𝟙 M) ≫
      (derivedHomData (R := R)).evaluation M (unitObject (R := R)) =
      p.evaluation) :
    ((derivedHomData (R := R)).tensorUnitLeft M).inv ≫
      (derivedHomData (R := R)).homEquiv (unitObject (R := R)) M M
        ((p.coevaluation ≫ (derivedHomData (R := R)).tensor.map (𝟙 M ×ₘ f)) ≫
          tensorDualHom M M) = 𝟙 M := by
  let d := derivedHomData (R := R)
  rw [d.homEquiv_naturality_left]
  dsimp only [tensorDualHom]
  rw [AddEquiv.apply_symm_apply]
  show _ ≫ d.tensor.map ((p.coevaluation ≫ d.tensor.map (𝟙 M ×ₘ f)) ×ₘ 𝟙 M) ≫ _ = _
  rw [show d.tensor.map ((p.coevaluation ≫ d.tensor.map (𝟙 M ×ₘ f)) ×ₘ 𝟙 M) =
      d.tensor.map (p.coevaluation ×ₘ 𝟙 M) ≫
        d.tensor.map (d.tensor.map (𝟙 M ×ₘ f) ×ₘ 𝟙 M) by
      rw [d.tensor_map_comp, Category.id_comp]]
  simp only [Category.assoc]
  rw [d.tensorAssoc_naturality_assoc (𝟙 M) f (𝟙 M)]
  have he : d.tensor.map (𝟙 M ×ₘ d.tensor.map (f ×ₘ 𝟙 M)) ≫
      d.tensor.map (𝟙 M ×ₘ d.evaluation M (unitObject (R := R))) =
      d.tensor.map (𝟙 M ×ₘ p.evaluation) := by
    rw [d.tensor_map_comp, Category.id_comp, hf]
  rw [reassoc_of% he]
  exact p.evaluation_coevaluation

private theorem nonempty_iso_derivedDual_of_canonical_pairing
    {M N : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))}
    (p : DerivedLeftDualPairing M N)
    (q : DerivedLeftDualPairing M (derivedDual M))
    (hq : q.evaluation = (derivedHomData (R := R)).evaluation M
      (unitObject (R := R))) : Nonempty (N ≅ derivedDual M) := by
  let d := derivedHomData (R := R)
  let U := unitObject (R := R)
  let f : N ⟶ derivedDual M := (d.homEquiv N M U).symm p.evaluation
  have hf : d.tensor.map (f ×ₘ 𝟙 M) ≫ d.evaluation M U = p.evaluation := by
    rw [tensor_map_comp_evaluation, AddEquiv.apply_symm_apply]
  have : IsIso (tensorDualHom M M) :=
    (isPerfect_derivedDual_and_naturalIsos M (isPerfect_of_pairing p)).tensorDualHom_isIso M
  have hη : p.coevaluation ≫ d.tensor.map (𝟙 M ×ₘ f) = q.coevaluation := by
    apply (cancel_mono (tensorDualHom M M)).1
    apply (d.homEquiv U M M).injective
    apply (cancel_epi ((derivedHomData (R := R)).tensorUnitLeft M).inv).1
    rw [pairing_coevaluation_tensorHom p f hf]
    have hq' : d.tensor.map (𝟙 (derivedDual M) ×ₘ 𝟙 M) ≫ d.evaluation M U =
        q.evaluation := by rw [d.tensor_map_id, Category.id_comp, hq]
    simpa only [DerivedHomAdjunction.tensor_map_id, Category.comp_id] using
      (pairing_coevaluation_tensorHom q (𝟙 _) hq').symm
  exact nonempty_iso_of_pairing_compatible p q f hη (by rwa [hq])

private theorem canonical_dual_triangle
    (M : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)))
    (η : unitObject (R := R) ⟶
      (derivedHomData (R := R)).tensor.obj (M, derivedDual M))
    (hη : ((derivedHomData (R := R)).tensorUnitLeft M).inv ≫
        (derivedHomData (R := R)).tensor.map (η ×ₘ 𝟙 M) ≫
        ((derivedHomData (R := R)).tensorAssoc M (derivedDual M) M).hom ≫
        (derivedHomData (R := R)).tensor.map
          (𝟙 M ×ₘ (derivedHomData (R := R)).evaluation M unitObject) ≫
        (derivedTensorRightUnitor M).hom = 𝟙 M) :
    (derivedTensorRightUnitor (derivedDual M)).inv ≫
      (derivedHomData (R := R)).tensor.map (𝟙 (derivedDual M) ×ₘ η) ≫
      ((derivedHomData (R := R)).tensorAssoc (derivedDual M) M
        (derivedDual M)).inv ≫
      (derivedHomData (R := R)).tensor.map
        ((derivedHomData (R := R)).evaluation M unitObject ×ₘ
          𝟙 (derivedDual M)) ≫
      ((derivedHomData (R := R)).tensorUnitLeft (derivedDual M)).hom =
        𝟙 (derivedDual M) := by
  let d := derivedHomData (R := R)
  let := derivedMonoidalCategory d
  have hr (X : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
      derivedTensorRightUnitor X = d.tensorRightUnitor.app X :=
    Iso.ext (derivedTensorRightUnitor_eq X)
  rw [hr] at hη ⊢
  apply coevaluation_evaluation_of_nondegenerate η (d.evaluation M unitObject) _ hη
  intro f g h
  apply (d.homEquiv (derivedDual M) M unitObject).injective
  exact (tensor_map_comp_evaluation d.toDerivedHomAdjunction f).symm.trans
    (h.trans (tensor_map_comp_evaluation d.toDerivedHomAdjunction g))

/-- **Stacks 0FNS.** An object of the derived category has a left dual exactly when it is perfect.
For a perfect object the derived dual `RHom(M, R)` is a left dual, and every other left dual is
isomorphic to it. -/
@[stacks 0FNS]
public theorem isPerfect_iff_exists_leftDual
    (M : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))) :
    ((∃ N : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)),
        Nonempty (DerivedLeftDualPairing M N)) ↔
        IsPerfect M) ∧
      (IsPerfect M →
        Nonempty (DerivedLeftDualPairing M (derivedDual M))) ∧
      (∀ (N : DerivedCategory (ModuleCat.{max u v} (ULift.{v} R))),
        DerivedLeftDualPairing M N →
        Nonempty (N ≅ derivedDual M)) := by
  suffices hc : IsPerfect M →
      ∃ q : DerivedLeftDualPairing M (derivedDual M),
        q.evaluation = (derivedHomData (R := R)).evaluation M
          (unitObject (R := R)) by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rintro ⟨N, ⟨p⟩⟩
      exact isPerfect_of_pairing p
    · intro hM
      obtain ⟨q, -⟩ := hc hM
      exact ⟨derivedDual M, ⟨q⟩⟩
    · intro hM
      obtain ⟨q, -⟩ := hc hM
      exact ⟨q⟩
    · intro N p
      obtain ⟨q, hq⟩ := hc (isPerfect_of_pairing p)
      exact nonempty_iso_derivedDual_of_canonical_pairing p q hq
  intro hM
  obtain ⟨η, hη⟩ := exists_coevaluation_of_isPerfect M hM
  refine ⟨{
    coevaluation := η
    evaluation := (derivedHomData (R := R)).evaluation M
      (unitObject (R := R))
    coevaluation_evaluation := canonical_dual_triangle M η hη
    evaluation_coevaluation := hη
  }, rfl⟩

end DerivedCategory.Invertible

end
