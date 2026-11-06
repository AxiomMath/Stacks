module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Algebra.Homology.ShortComplex.InverseLimit
public import StacksFrontier.Homology.DerivedComplete.CompletionSequences
public import StacksFrontier.Homology.ProIsoBoundedTorsion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Comparison of completions at a principal ideal: the termwise short exact sequences

Auxiliary part of Stacks 0H32. This part defines the inverse system
`PrincipalCompletionDiagram.principalKoszulSystem` of two-term complexes `(A →[f^(n+1)] A)` in
`D(A)`, proves the naturality of the maps of systems, mapping cocones and Milnor triangles
induced by a map of complexes, the short exactness of the termwise cone sequences and of the
cohomology sequence of the Milnor triangle, the Mittag-Leffler condition for the quotient
system, and the isomorphism of first derived inverse limits induced by a termwise short exact
sequence of inverse systems.
-/

section


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory PrincipalTorsionTower

universe u v w x

namespace PrincipalCompletionDiagram

attribute [local instance] HasDerivedCategory.standard

/-- The inverse system in `D(A)` of the two-term complexes
`(A →[f^(n+1)] A)`, with transition map given by multiplication by `f` in degree `-1`
and the identity in degree `0`. -/
@[sga "2 II Lemma9" "special case"]
public noncomputable def principalKoszulSystem (A : Type u) [CommRing A] (f : A) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Functor.ofOpSequence
    (X := fun n ↦ ProTorsion.Kobj A f (n + 1))
    (fun n ↦ ProTorsion.KtransOne A f (n + 1))

/-- The `n`-th object of `principalKoszulSystem A f` is the complex `(A →[f^(n+1)] A)`. -/
@[simp]
public lemma principalKoszulSystem_obj (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    (principalKoszulSystem A f).obj ⟨n⟩ = ProTorsion.Kobj A f (n + 1) := rfl

/-- The transition map of `principalKoszulSystem A f` from index `n + 1` to index `n` is
`ProTorsion.KtransOne A f (n + 1)`. -/
@[simp]
public lemma principalKoszulSystem_map_succ (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    (principalKoszulSystem A f).map (homOfLE (Nat.le_succ n)).op =
      ProTorsion.KtransOne A f (n + 1) := by
  apply Functor.ofOpSequence_map_homOfLE_succ

private theorem reflector_hom_ext
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} [R.Full] [R.Faithful] (adj : L ⊣ R)
    {X : C} {Y : D} {a b : R.obj (L.obj X) ⟶ R.obj Y}
    (h : adj.unit.app X ≫ a = adj.unit.app X ≫ b) : a = b := by
  have h' : adj.homEquiv X Y (R.preimage a) =
      adj.homEquiv X Y (R.preimage b) := by
    simpa only [Adjunction.homEquiv_unit, R.map_preimage] using h
  simpa only [R.map_preimage] using
    congrArg R.map ((adj.homEquiv X Y).injective h')

set_option backward.isDefEq.respectTransparency false in
private def principalComplexSystemMap
    {A : Type u} [CommRing A] (f : A)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} (g : C ⟶ D) :
    PrincipalTorsionTower.principalComplexSystem A f C ⟶
      PrincipalTorsionTower.principalComplexSystem A f D :=
  NatTrans.ofOpSequence
    (fun n ↦ CochainComplex.mappingCone.map _ _ g g (by
      simp [smul_comp, comp_smul])) (by
    intro n
    simp only [PrincipalTorsionTower.principalComplexSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    rw [← CochainComplex.mappingCone.map_comp,
      ← CochainComplex.mappingCone.map_comp]
    congr 1
    simp [smul_comp, comp_smul])

private theorem principalComplexSystemMap_inr
    {A : Type u} [CommRing A] (f : A)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} (g : C ⟶ D) (n : ℕ) :
    CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C) ≫
        (principalComplexSystemMap f g).app ⟨n⟩ =
      g ≫ CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 D) :=
  (CochainComplex.mappingCone.triangleMap _ _ g g (by simp [smul_comp, comp_smul])).comm₂

private theorem complexDifference_naturality
    {A : Type u} [CommRing A]
    {E F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ} (α : E ⟶ F) :
    CompletionSequences.complexDifference A E ≫ Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩) =
      Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩) ≫ CompletionSequences.complexDifference A F := by
  apply Pi.hom_ext
  intro n
  simp [CompletionSequences.complexDifference, sub_comp, comp_sub, α.naturality]

set_option backward.isDefEq.respectTransparency false in
private theorem principalComplexUnit_naturality
    {A : Type u} [CommRing A] (f : A)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} (g : C ⟶ D) :
    CompletionSequences.principalComplexUnit A f C ≫
        Limits.Pi.map (fun n : ℕ ↦ (principalComplexSystemMap f g).app ⟨n⟩) =
      g ≫ CompletionSequences.principalComplexUnit A f D := by
  apply Pi.hom_ext
  intro n
  simpa only [Category.assoc, Pi.map_π,
    CompletionSequences.principalComplexUnit_π_assoc, CompletionSequences.principalComplexUnit_π]
      using
    principalComplexSystemMap_inr f g n

set_option backward.isDefEq.respectTransparency false in
private def mappingCoconeTriangleMap
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : d₁ ≫ b = a ≫ d₂) :
    CochainComplex.mappingCocone.triangle d₁ ⟶
      CochainComplex.mappingCocone.triangle d₂ :=
  (rotate _).preimage
    ((CochainComplex.mappingCocone.rotateTriangleIso d₁).hom ≫
      CochainComplex.mappingCone.triangleMap d₁ d₂ a b h ≫
        (CochainComplex.mappingCocone.rotateTriangleIso d₂).inv)

/-- Rotating `mappingCoconeTriangleMap` recovers the map of mapping cone triangles. -/
private theorem rotate_mappingCoconeTriangleMap
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : d₁ ≫ b = a ≫ d₂) :
    (rotate _).map (mappingCoconeTriangleMap d₁ d₂ a b h) =
      (CochainComplex.mappingCocone.rotateTriangleIso d₁).hom ≫
        CochainComplex.mappingCone.triangleMap d₁ d₂ a b h ≫
          (CochainComplex.mappingCocone.rotateTriangleIso d₂).inv :=
  (rotate _).map_preimage _

set_option backward.isDefEq.respectTransparency false in
private theorem mappingCoconeTriangleMap_hom₂
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : d₁ ≫ b = a ≫ d₂) :
    (mappingCoconeTriangleMap d₁ d₂ a b h).hom₂ = a := by
  exact (congrArg TriangleMorphism.hom₁ (rotate_mappingCoconeTriangleMap d₁ d₂ a b h)).trans (by
    show 𝟙 _ ≫ a ≫ 𝟙 _ = a
    simp)

set_option backward.isDefEq.respectTransparency false in
private theorem mappingCoconeTriangleMap_hom₃
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : d₁ ≫ b = a ≫ d₂) :
    (mappingCoconeTriangleMap d₁ d₂ a b h).hom₃ = b := by
  exact (congrArg TriangleMorphism.hom₂ (rotate_mappingCoconeTriangleMap d₁ d₂ a b h)).trans (by
    show 𝟙 _ ≫ b ≫ 𝟙 _ = b
    simp)

set_option backward.isDefEq.respectTransparency false in
private theorem mappingCoconeTriangleMap_fst
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : d₁ ≫ b = a ≫ d₂) :
    (mappingCoconeTriangleMap d₁ d₂ a b h).hom₁ ≫
        CochainComplex.mappingCocone.fst d₂ =
      CochainComplex.mappingCocone.fst d₁ ≫ a := by
  have hc := (mappingCoconeTriangleMap d₁ d₂ a b h).comm₁.symm
  rw [mappingCoconeTriangleMap_hom₂] at hc
  exact hc

set_option backward.isDefEq.respectTransparency false in
private theorem mappingCoconeTriangleMap_hom₁
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : d₁ ≫ b = a ≫ d₂) :
    (mappingCoconeTriangleMap d₁ d₂ a b h).hom₁ =
      (CochainComplex.mappingCone.map d₁ d₂ a b h)⟦(-1 : ℤ)⟧' := by
  apply (shiftFunctor _ (1 : ℤ)).map_injective
  exact (congrArg TriangleMorphism.hom₃ (rotate_mappingCoconeTriangleMap d₁ d₂ a b h)).trans (by
    dsimp [CochainComplex.mappingCocone.rotateTriangleIso, Triangle.isoMk]
    exact (shift_neg_shift' _ 1).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem mappingCoconeTriangleMap_snd
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : d₁ ≫ b = a ≫ d₂)
    (p q : ℤ) (hpq : p + -1 = q) :
    (mappingCoconeTriangleMap d₁ d₂ a b h).hom₁.f p ≫
        (CochainComplex.mappingCocone.snd d₂).v p q hpq =
      (CochainComplex.mappingCocone.snd d₁).v p q hpq ≫ b.f q := by
  rw [mappingCoconeTriangleMap_hom₁]
  subst q
  dsimp [CochainComplex.mappingCocone.snd]
  rw [CochainComplex.HomComplex.Cochain.leftShift_v _ (-1) (-1)
    (by omega) p (p + -1) (by omega) (p + -1) (by omega),
    CochainComplex.HomComplex.Cochain.leftShift_v _ (-1) (-1)
    (by omega) p (p + -1) (by omega) (p + -1) (by omega)]
  simp only [Int.reduceNeg, Int.reduceMul, Int.reduceSub, Int.reduceDiv, Int.reduceAdd,
    Int.negOnePow_even 2 ⟨1, rfl⟩, one_smul, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  erw [Category.id_comp, Category.id_comp]
  show (CochainComplex.mappingCone.map d₁ d₂ a b h).f (p + -1) ≫
      (CochainComplex.mappingCone.snd d₂).v (p + -1) (p + -1) (by omega) = _
  simp [CochainComplex.mappingCone.ext_from_iff _ p (p + -1) (by omega),
    CochainComplex.mappingCone.map]

private theorem mappingCocone_hom_ext
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K L M : CochainComplex C ℤ} (d : K ⟶ L)
    {a b : M ⟶ CochainComplex.mappingCocone d}
    (hfst : a ≫ CochainComplex.mappingCocone.fst d =
      b ≫ CochainComplex.mappingCocone.fst d)
    (hsnd : ∀ p q : ℤ, ∀ hpq : p + -1 = q,
      a.f p ≫ (CochainComplex.mappingCocone.snd d).v p q hpq =
        b.f p ≫ (CochainComplex.mappingCocone.snd d).v p q hpq) : a = b := by
  ext p
  calc
    a.f p = a.f p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = b.f p ≫ 𝟙 _ := by
      rw [← CochainComplex.mappingCocone.id_X d p (p + -1) rfl]
      simp only [comp_add, ← Category.assoc]
      rw [show a.f p ≫ (CochainComplex.mappingCocone.fst d).f p =
        b.f p ≫ (CochainComplex.mappingCocone.fst d).f p from
          congrArg (fun g ↦ g.f p) hfst, hsnd]
    _ = b.f p := Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
private theorem principalCompletionUnit_naturality
    {A : Type u} [CommRing A] (f : A)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} (g : C ⟶ D) :
    let α := principalComplexSystemMap f g
    let a := Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩)
    let φ := mappingCoconeTriangleMap
      (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f C))
      (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f D))
      a a (complexDifference_naturality α)
    CompletionSequences.principalCompletionUnit A f C ≫ φ.hom₁ =
      g ≫ CompletionSequences.principalCompletionUnit A f D := by
  dsimp only
  apply mappingCocone_hom_ext
  · rw [Category.assoc, mappingCoconeTriangleMap_fst,
      ← Category.assoc, CompletionSequences.principalCompletionUnit_fst,
      Category.assoc, CompletionSequences.principalCompletionUnit_fst]
    exact principalComplexUnit_naturality f g
  · intro p q hpq
    simp only [HomologicalComplex.comp_f, Category.assoc, mappingCoconeTriangleMap_snd]
    simp [CompletionSequences.principalCompletionUnit,
      ← Category.assoc, CochainComplex.mappingCocone.lift_f_snd_v]

private def milnorTriangleMap
    {A : Type u} [CommRing A]
    {E F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ} (α : E ⟶ F) :
    CompletionSequences.milnorTriangle A E ⟶ CompletionSequences.milnorTriangle A F :=
  Q.mapTriangle.map (mappingCoconeTriangleMap
    (CompletionSequences.complexDifference A E) (CompletionSequences.complexDifference A F)
    (Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩))
    (Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩)) (complexDifference_naturality α))

set_option backward.isDefEq.respectTransparency false in
private theorem milnorTriangleMap_hom₂
    {A : Type u} [CommRing A]
    {E F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ} (α : E ⟶ F) :
    (milnorTriangleMap α).hom₂ = Q.map (Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩)) := by
  show Q.map (mappingCoconeTriangleMap (C := ModuleCat.{v} A) _ _ _ _ _).hom₂ = _
  rw [mappingCoconeTriangleMap_hom₂]

set_option backward.isDefEq.respectTransparency false in
private theorem milnorTriangleMap_hom₃
    {A : Type u} [CommRing A]
    {E F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ} (α : E ⟶ F) :
    (milnorTriangleMap α).hom₃ = Q.map (Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩)) := by
  show Q.map (mappingCoconeTriangleMap (C := ModuleCat.{v} A) _ _ _ _ _).hom₃ = _
  rw [mappingCoconeTriangleMap_hom₃]

set_option backward.isDefEq.respectTransparency false in
private theorem completionComparison_naturality
    {A : Type u} [CommRing A] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} (g : C ⟶ D) :
    (completion ⋙ P.ι).map (Q.map g) ≫ (c.iso D).hom =
      (c.iso C).hom ≫ (milnorTriangleMap (principalComplexSystemMap f g)).hom₁ := by
  apply (cancel_mono (c.iso D).inv).1
  apply reflector_hom_ext adj
  simp only [Category.assoc]
  erw [adj.unit_naturality_assoc]
  show Q.map g ≫ adj.unit.app (Q.obj D) ≫ (c.iso D).hom ≫ (c.iso D).inv = _
  rw [← Category.assoc _ (c.iso D).hom, c.unit_iso]
  rw [← Category.assoc (adj.unit.app _) (c.iso C).hom, c.unit_iso]
  show Q.map g ≫ Q.map (CompletionSequences.principalCompletionUnit A f D) ≫ (c.iso D).inv =
    Q.map (CompletionSequences.principalCompletionUnit A f C) ≫ Q.map _ ≫ (c.iso D).inv
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  exact congrArg (fun k ↦ Q.map k ≫ (c.iso D).inv)
    (principalCompletionUnit_naturality f g).symm

attribute [local instance] DerivedCategory.homologyFunctor_linear

private theorem powerMultiplication_naturality
    {A : Type u} [CommRing A] (r : A) {M N : ModuleCat.{v} A} (g : M ⟶ N) :
    PrincipalTorsionTower.powerMultiplication A M r ≫ g =
      g ≫ PrincipalTorsionTower.powerMultiplication A N r := by
  show (r • 𝟙 M) ≫ g = g ≫ (r • 𝟙 N)
  simp [smul_comp, comp_smul]

set_option backward.isDefEq.respectTransparency false in
private def powerTorsionSystemMap
    {A : Type u} [CommRing A] (f : A) {M N : ModuleCat.{v} A} (g : M ⟶ N) :
    PrincipalTorsionTower.powerTorsionSystem A M f ⟶ PrincipalTorsionTower.powerTorsionSystem A N f
      :=
  NatTrans.ofOpSequence
    (fun n ↦ kernel.map (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1)))
      (PrincipalTorsionTower.powerMultiplication A N (f ^ (n + 1))) g g
        (powerMultiplication_naturality _ g)) (by
      intro n
      apply (cancel_mono (kernel.ι
        (PrincipalTorsionTower.powerMultiplication A N (f ^ (n + 1))))).1
      simp only [Category.assoc, kernel.map, kernel.lift_ι]
      rw [← Category.assoc, PrincipalTorsionTower.powerTorsionSystem_map_succ,
        PrincipalTorsionTower.powerTorsionTransition_ι,
        PrincipalTorsionTower.powerTorsionSystem_map_succ,
          PrincipalTorsionTower.powerTorsionTransition_ι]
      simp only [Category.assoc, kernel.lift_ι_assoc]
      rw [powerMultiplication_naturality])

private theorem powerTorsionSystemMap_ι
    {A : Type u} [CommRing A] (f : A) {M N : ModuleCat.{v} A} (g : M ⟶ N) (n : ℕ) :
    (powerTorsionSystemMap f g).app ⟨n⟩ ≫
        kernel.ι (PrincipalTorsionTower.powerMultiplication A N (f ^ (n + 1))) =
      kernel.ι (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1))) ≫ g :=
  kernel.lift_ι _ _ _

set_option backward.isDefEq.respectTransparency false in
private def powerQuotientSystemMap
    {A : Type u} [CommRing A] (f : A) {M N : ModuleCat.{v} A} (g : M ⟶ N) :
    CompletionSequences.powerQuotientSystem A M f ⟶ CompletionSequences.powerQuotientSystem A N f :=
  NatTrans.ofOpSequence
    (fun n ↦ cokernel.map (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1)))
      (PrincipalTorsionTower.powerMultiplication A N (f ^ (n + 1))) g g
        (powerMultiplication_naturality _ g)) (by
      intro n
      apply (cancel_epi (cokernel.π
        (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1 + 1))))).1
      rw [← Category.assoc, CompletionSequences.powerQuotientSystem_map_succ,
        CompletionSequences.π_powerQuotientTransition]
      simp only [cokernel.map, cokernel.π_desc, cokernel.π_desc_assoc, Category.assoc]
      rw [CompletionSequences.powerQuotientSystem_map_succ,
        CompletionSequences.π_powerQuotientTransition])

private theorem π_powerQuotientSystemMap
    {A : Type u} [CommRing A] (f : A) {M N : ModuleCat.{v} A} (g : M ⟶ N) (n : ℕ) :
    cokernel.π (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1))) ≫
        (powerQuotientSystemMap f g).app ⟨n⟩ =
      g ≫ cokernel.π (PrincipalTorsionTower.powerMultiplication A N (f ^ (n + 1))) :=
  cokernel.π_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem principalCone_inclusion_naturality
    {A : Type u} [CommRing A] (f : A)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} (g : C ⟶ D)
    {K L : DerivedCategory (ModuleCat.{v} A)} (eC : Q.obj C ≅ K) (eD : Q.obj D ≅ L)
    (p : ℤ)
    (iC : CompletionSequences.powerQuotientSystem A ((homologyFunctor (ModuleCat.{v} A) p).obj K) f
      ⟶
      PrincipalTorsionTower.principalComplexSystem A f C ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) p)
    (iD : CompletionSequences.powerQuotientSystem A ((homologyFunctor (ModuleCat.{v} A) p).obj L) f
      ⟶
      PrincipalTorsionTower.principalComplexSystem A f D ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) p)
    (hiC : ∀ n : ℕ, cokernel.π (PrincipalTorsionTower.powerMultiplication A
        ((homologyFunctor (ModuleCat.{v} A) p).obj K) (f ^ (n + 1))) ≫ iC.app ⟨n⟩ =
      (homologyFunctor (ModuleCat.{v} A) p).map
        (eC.inv ≫ Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 C))))
    (hiD : ∀ n : ℕ, cokernel.π (PrincipalTorsionTower.powerMultiplication A
        ((homologyFunctor (ModuleCat.{v} A) p).obj L) (f ^ (n + 1))) ≫ iD.app ⟨n⟩ =
      (homologyFunctor (ModuleCat.{v} A) p).map
        (eD.inv ≫ Q.map (CochainComplex.mappingCone.inr (f ^ (n + 1) • 𝟙 D)))) :
    powerQuotientSystemMap f ((homologyFunctor (ModuleCat.{v} A) p).map
        (eC.inv ≫ Q.map g ≫ eD.hom)) ≫ iD =
      iC ≫ Functor.whiskerRight (principalComplexSystemMap f g)
        (Q ⋙ homologyFunctor (ModuleCat.{v} A) p) := by
  apply NatTrans.ext
  funext n
  apply (cancel_epi (cokernel.π (PrincipalTorsionTower.powerMultiplication A
    ((homologyFunctor (ModuleCat.{v} A) p).obj K) (f ^ (n.unop + 1))))).1
  show _ ≫ ((powerQuotientSystemMap f _).app n ≫ iD.app n) =
    _ ≫ (iC.app n ≫ (homologyFunctor (ModuleCat.{v} A) p).map
      (Q.map ((principalComplexSystemMap f g).app n)))
  rw [← Category.assoc, π_powerQuotientSystemMap, Category.assoc, hiD n.unop]
  rw [reassoc_of% hiC n.unop]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [Functor.map_comp] using
    congrArg (fun k ↦ eC.inv ≫ Q.map k)
      (principalComplexSystemMap_inr f g n.unop).symm

set_option backward.isDefEq.respectTransparency false in
private theorem principalCone_projection_naturality
    {A : Type u} [CommRing A] (f : A)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} (g : C ⟶ D)
    {K L : DerivedCategory (ModuleCat.{v} A)} (eC : Q.obj C ≅ K) (eD : Q.obj D ≅ L)
    (p q : ℤ) (hpq : p + 1 = q)
    (sC : PrincipalTorsionTower.principalComplexSystem A f C ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A)
      p ⟶
      PrincipalTorsionTower.powerTorsionSystem A ((homologyFunctor (ModuleCat.{v} A) q).obj K) f)
    (sD : PrincipalTorsionTower.principalComplexSystem A f D ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A)
      p ⟶
      PrincipalTorsionTower.powerTorsionSystem A ((homologyFunctor (ModuleCat.{v} A) q).obj L) f)
    (hsC : ∀ n : ℕ, sC.app ⟨n⟩ ≫ kernel.ι (PrincipalTorsionTower.powerMultiplication A
        ((homologyFunctor (ModuleCat.{v} A) q).obj K) (f ^ (n + 1))) =
      (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
        (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C)))
        p q hpq ≫ (homologyFunctor (ModuleCat.{v} A) q).map eC.hom)
    (hsD : ∀ n : ℕ, sD.app ⟨n⟩ ≫ kernel.ι (PrincipalTorsionTower.powerMultiplication A
        ((homologyFunctor (ModuleCat.{v} A) q).obj L) (f ^ (n + 1))) =
      (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
        (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 D)))
        p q hpq ≫ (homologyFunctor (ModuleCat.{v} A) q).map eD.hom) :
    Functor.whiskerRight (principalComplexSystemMap f g)
        (Q ⋙ homologyFunctor (ModuleCat.{v} A) p) ≫ sD =
      sC ≫ powerTorsionSystemMap f ((homologyFunctor (ModuleCat.{v} A) q).map
        (eC.inv ≫ Q.map g ≫ eD.hom)) := by
  apply NatTrans.ext
  funext n
  apply (cancel_mono (kernel.ι (PrincipalTorsionTower.powerMultiplication A
    ((homologyFunctor (ModuleCat.{v} A) q).obj L) (f ^ (n.unop + 1))))).1
  show ((homologyFunctor (ModuleCat.{v} A) p).map
    (Q.map ((principalComplexSystemMap f g).app n)) ≫ sD.app n) ≫ _ =
      (sC.app n ≫ (powerTorsionSystemMap f _).app n) ≫ _
  rw [Category.assoc, hsD n.unop, Category.assoc, powerTorsionSystemMap_ι,
    ← Category.assoc (sC.app n), hsC n.unop]
  let φ := Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap
    (f ^ (n.unop + 1) • 𝟙 C) (f ^ (n.unop + 1) • 𝟙 D) g g
      (by simp [smul_comp, comp_smul]))
  have h := (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ_naturality φ p q hpq
  show (homologyFunctor (ModuleCat.{v} A) p).map φ.hom₃ ≫ _ = _
  erw [← Category.assoc, h, Category.assoc]
  have h₁ : φ.hom₁ = Q.map g := rfl
  rw [h₁]
  simp only [shift_homologyFunctor, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_assoc]

private theorem shortExact_cokernel_kernel
    {C : Type*} [Category C] [Abelian C] {X₀ X₁ X₂ X₃ X₄ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
    (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hcd : c ≫ d = 0)
    (h₁ : (ShortComplex.mk a b hab).Exact)
    (h₂ : (ShortComplex.mk b c hbc).Exact)
    (h₃ : (ShortComplex.mk c d hcd).Exact) :
    ∃ h : cokernel.desc a b hab ≫ kernel.lift d c hcd = 0,
      (ShortComplex.mk (cokernel.desc a b hab) (kernel.lift d c hcd) h).ShortExact := by
  let i := cokernel.desc a b hab
  let q := kernel.lift d c hcd
  have hiq : i ≫ q = 0 := by
    rw [← cancel_epi (cokernel.π a), ← cancel_mono (kernel.ι d)]
    simpa [i, q] using hbc
  have : Mono i := h₁.mono_cokernelDesc
  have : Epi q := h₃.epi_kernelLift
  refine ⟨hiq, { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }⟩
  let S := ShortComplex.mk i c (by
    rw [← cancel_epi (cokernel.π a)]
    simpa [i] using hbc)
  let φ : ShortComplex.mk b c hbc ⟶ S :=
    { τ₁ := cokernel.π a
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, i]
      comm₂₃ := by simp [S] }
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp h₂
  let ψ : ShortComplex.mk i q hiq ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι d
      comm₁₂ := by simp [S]
      comm₂₃ := by simp [S, q] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hS

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalCone_shortExact
    (A : Type u) [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ)
    (K : DerivedCategory (ModuleCat.{v} A)) (e : Q.obj C ≅ K)
    (p q : ℤ) (hpq : p + 1 = q) :
    let H := homologyFunctor (ModuleCat.{v} A)
    let E := PrincipalTorsionTower.principalComplexSystem A f C ⋙ Q ⋙ H p
    let T (n : ℕ) := Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C))
    ∃ (i : CompletionSequences.powerQuotientSystem A ((H p).obj K) f ⟶ E)
      (s : E ⟶ PrincipalTorsionTower.powerTorsionSystem A ((H q).obj K) f),
      (∀ n : ℕ, cokernel.π (PrincipalTorsionTower.powerMultiplication A ((H p).obj K)
        (f ^ (n + 1))) ≫ i.app ⟨n⟩ = (H p).map (e.inv ≫ (T n).mor₂)) ∧
      (∀ n : ℕ, s.app ⟨n⟩ ≫ kernel.ι (PrincipalTorsionTower.powerMultiplication A
        ((H q).obj K) (f ^ (n + 1))) =
          (H 0).homologySequenceδ (T n) p q hpq ≫ (H q).map e.hom) ∧
      ∃ h : i ≫ s = 0,
        ∀ n, ((ShortComplex.mk i s h).map
          ((evaluation ℕᵒᵖ (ModuleCat.{v} A)).obj n)).ShortExact := by
  let H := homologyFunctor (ModuleCat.{v} A)
  let E := PrincipalTorsionTower.principalComplexSystem A f C ⋙ Q ⋙ H p
  let T (n : ℕ) := Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C))
  have hT (n : ℕ) : T n ∈ distTriang _ := mappingCone_triangle_distinguished _
  let a (n : ℕ) := (H p).map (e.inv ≫ (T n).mor₂)
  let b (n : ℕ) := (H 0).homologySequenceδ (T n) p q hpq ≫ (H q).map e.hom
  let m (j : ℤ) (n : ℕ) := PrincipalTorsionTower.powerMultiplication A ((H j).obj K) (f ^ (n + 1))
  have hm (j : ℤ) (n : ℕ) : (H j).map (T n).mor₁ = f ^ (n + 1) • 𝟙 _ := by
    show (H j).map (Q.map (f ^ (n + 1) • 𝟙 C)) = _
    simp [H, T, Functor.map_smul]
  have hm' (j : ℤ) (n : ℕ) : m j n = f ^ (n + 1) • 𝟙 _ := rfl
  have ha (n : ℕ) : m p n ≫ a n = 0 := by
    have hc : m p n ≫ (H p).map e.inv =
        (H p).map e.inv ≫ (H p).map (T n).mor₁ := by
      rw [hm', hm]
      simp [T, smul_comp, comp_smul]
    dsimp only [a]
    rw [Functor.map_comp, ← Category.assoc, hc, Category.assoc, ← Functor.map_comp,
      comp_distTriang_mor_zero₁₂ _ (hT n), Functor.map_zero, comp_zero]
  have hb (n : ℕ) : b n ≫ m q n = 0 := by
    have hc : (H q).map e.hom ≫ m q n =
        (H q).map (T n).mor₁ ≫ (H q).map e.hom := by
      rw [hm', hm]
      simp [T, smul_comp, comp_smul]
    have hz : (H 0).homologySequenceδ (T n) p q hpq ≫ (H q).map (T n).mor₁ = 0 :=
      (H 0).homologySequenceδ_comp (T n) (hT n) p q hpq
    dsimp only [b]
    rw [Category.assoc, hc, ← Category.assoc, hz, zero_comp]
  have hab (n : ℕ) : a n ≫ b n = 0 := by
    dsimp only [a, b]
    erw [Functor.map_comp, Category.assoc, ← Category.assoc _ _ ((H q).map e.hom),
      (H 0).comp_homologySequenceδ (T n) (hT n) p q hpq, zero_comp, comp_zero]
  have ha_exact (n : ℕ) : (ShortComplex.mk (m p n) (a n) (ha n)).Exact := by
    apply ShortComplex.exact_of_iso _ ((H 0).homologySequence_exact₂ (T n) (hT n) p)
    refine ShortComplex.isoMk ((H p).mapIso e) ((H p).mapIso e) (Iso.refl _) ?_ ?_
    · show (H _).map e.hom ≫ m _ _ = (H _).map (T _).mor₁ ≫ (H _).map e.hom
      simp only [hm, hm', comp_smul, smul_comp, Category.comp_id, Category.id_comp]
    · simp [a, H, shift_homologyFunctor, ← Functor.map_comp]
  have hab_exact (n : ℕ) : (ShortComplex.mk (a n) (b n) (hab n)).Exact := by
    apply ShortComplex.exact_of_iso _
      ((H 0).homologySequence_exact₃ (T n) (hT n) p q hpq)
    refine ShortComplex.isoMk ((H p).mapIso e) (Iso.refl _) ((H q).mapIso e) ?_ ?_
    · simp [a, H, shift_homologyFunctor, ← Functor.map_comp]
    · simp [b]
  have hb_exact (n : ℕ) : (ShortComplex.mk (b n) (m q n) (hb n)).Exact := by
    apply ShortComplex.exact_of_iso _
      ((H 0).homologySequence_exact₁ (T n) (hT n) p q hpq)
    refine ShortComplex.isoMk (Iso.refl _) ((H q).mapIso e) ((H q).mapIso e) ?_ ?_
    · simp [b]
    · show (H _).map e.hom ≫ m _ _ = (H _).map (T _).mor₁ ≫ (H _).map e.hom
      simp only [hm, hm', comp_smul, smul_comp, Category.comp_id, Category.id_comp]
  let φ (n : ℕ) : T (n + 1) ⟶ T n :=
    Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap _ _
      (f • 𝟙 C) (𝟙 C) (by
        simp [comp_smul, smul_smul, pow_succ', mul_comm]))
  have hE (n : ℕ) : E.map (homOfLE (Nat.le_succ n)).op = (H p).map (φ n).hom₃ := by
    dsimp [E, PrincipalTorsionTower.principalComplexSystem, φ]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
  have ha_nat (n : ℕ) : a (n + 1) ≫ E.map (homOfLE (Nat.le_succ n)).op = a n := by
    dsimp only [a]
    rw [hE, ← Functor.map_comp, Category.assoc, (φ n).comm₂]
    have h₂ : (φ n).hom₂ = 𝟙 _ := Q.map_id C
    rw [h₂, Category.id_comp]
  have hb_nat (n : ℕ) : E.map (homOfLE (Nat.le_succ n)).op ≫ b n =
      b (n + 1) ≫ PrincipalTorsionTower.powerMultiplication A ((H q).obj K) f := by
    dsimp only [b]
    erw [hE, ← Category.assoc,
      (H 0).homologySequenceδ_naturality (φ n) p q hpq, Category.assoc]
    have h₁ : (H q).map (φ n).hom₁ = f • 𝟙 _ := by
      show (H q).map (Q.map (f • 𝟙 C)) = _
      simp [H, T, Functor.map_smul]
    show (H 0).homologySequenceδ (T (n + 1)) p q hpq ≫
      (H q).map (φ n).hom₁ ≫ (H q).map e.hom = _
    rw [h₁]
    show _ = b (n + 1) ≫ (f • 𝟙 _)
    simp [b, H, T, shift_homologyFunctor, comp_smul, smul_comp]
  let i : CompletionSequences.powerQuotientSystem A ((H p).obj K) f ⟶ E :=
    NatTrans.ofOpSequence (fun n ↦ cokernel.desc (m p n) (a n) (ha n)) (by
      intro n
      apply (cancel_epi (cokernel.π (m p (n + 1)))).1
      rw [← Category.assoc, CompletionSequences.powerQuotientSystem_map_succ,
        CompletionSequences.π_powerQuotientTransition, cokernel.π_desc,
        cokernel.π_desc_assoc]
      exact (ha_nat n).symm)
  let s : E ⟶ PrincipalTorsionTower.powerTorsionSystem A ((H q).obj K) f :=
    NatTrans.ofOpSequence (fun n ↦ kernel.lift (m q n) (b n) (hb n)) (by
      intro n
      apply (cancel_mono (kernel.ι (m q n))).1
      rw [Category.assoc, kernel.lift_ι, Category.assoc,
        PrincipalTorsionTower.powerTorsionSystem_map_succ,
          PrincipalTorsionTower.powerTorsionTransition_ι,
        kernel.lift_ι_assoc]
      exact hb_nat n)
  have hi (n : ℕ) : cokernel.π (m p n) ≫ i.app ⟨n⟩ = a n := cokernel.π_desc _ _ _
  have hs (n : ℕ) : s.app ⟨n⟩ ≫ kernel.ι (m q n) = b n := kernel.lift_ι _ _ _
  have hz : i ≫ s = 0 := by
    apply NatTrans.ext
    funext n
    show i.app n ≫ s.app n = 0
    apply (cancel_epi (cokernel.π (m p n.unop))).1
    apply (cancel_mono (kernel.ι (m q n.unop))).1
    simpa [Category.assoc, reassoc_of% hi n.unop, hs n.unop] using hab n.unop
  refine ⟨i, s, hi, hs, hz, ?_⟩
  intro n
  exact (shortExact_cokernel_kernel (m p n.unop) (a n.unop) (b n.unop) (m q n.unop)
    (ha n.unop) (hab n.unop) (hb n.unop)
    (ha_exact n.unop) (hab_exact n.unop) (hb_exact n.unop)).choose_spec

set_option backward.isDefEq.respectTransparency false in
private theorem milnorTriangle_homology_shortExact
    (A : Type u) [CommRing A]
    (E : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) (p : ℤ) :
    let H := homologyFunctor (ModuleCat.{v} A)
    let T := CompletionSequences.milnorTriangle A E
    let V (q : ℤ) := E ⋙ Q ⋙ H q
    ∃ (e : (H (p - 1)).obj T.obj₃ ≅ CompletionSequences.moduleProduct A (V (p - 1)))
      (i : CompletionSequences.firstDerivedLimit A (V (p - 1)) ⟶ (H p).obj T.obj₁)
      (q : (H p).obj T.obj₁ ⟶ limit (V p)) (h : i ≫ q = 0),
      (∀ n : ℕ, e.hom ≫ Pi.π (fun n : ℕ ↦ (V (p - 1)).obj ⟨n⟩) n =
        (H (p - 1)).map (Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n))) ∧
      e.hom ≫ cokernel.π (CompletionSequences.moduleDifference A (V (p - 1))) ≫ i =
        (H 0).homologySequenceδ T (p - 1) p (by omega) ∧
      (∀ n : ℕ, q ≫ limit.π (V p) ⟨n⟩ =
        (H p).map (T.mor₁ ≫ Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n))) ∧
      (ShortComplex.mk i q h).ShortExact := by
  let H := homologyFunctor (ModuleCat.{v} A)
  let T := CompletionSequences.milnorTriangle A E
  let V (q : ℤ) := E ⋙ Q ⋙ H q
  have hT := CompletionSequences.milnorTriangle_distinguished A E
  have hpres (q : ℤ) : PreservesLimitsOfShape (Discrete ℕ) (Q ⋙ H q) := by
    have := Stacks.DerivedProducts.preservesLimitsOfShape_homologyFunctor
      (A := ModuleCat.{v} A) (I := ℕ) q
    exact preservesLimitsOfShape_of_natIso (homologyFunctorFactors (ModuleCat.{v} A) q).symm
  let e (q : ℤ) := asIso (piComparison (Q ⋙ H q) (fun n : ℕ ↦ E.obj ⟨n⟩))
  have he (q : ℤ) (n : ℕ) : (e q).hom ≫ Pi.π (fun n : ℕ ↦ (V q).obj ⟨n⟩) n =
      (H q).map (Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n)) :=
    piComparison_comp_π _ _ _
  let d (q : ℤ) := CompletionSequences.moduleDifference A (V q)
  have hd (q : ℤ) : (H q).map T.mor₂ ≫ (e q).hom = (e q).hom ≫ d q := by
    apply Pi.hom_ext
    intro n
    erw [Category.assoc, he]
    show (H q).map (Q.map (CompletionSequences.complexDifference A E)) ≫ _ = _
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [CompletionSequences.complexDifference, Pi.lift_comp_π]
    show _ = (e q).hom ≫ CompletionSequences.moduleDifference A (V q) ≫
      Pi.π (fun n : ℕ ↦ (V q).obj ⟨n⟩) n
    rw [CompletionSequences.moduleDifference, Pi.lift_comp_π, comp_sub, ← Category.assoc,
      he, he]
    simp [Functor.map_sub, Functor.map_comp, V]
  let c := (e (p - 1)).inv ≫ (H 0).homologySequenceδ T (p - 1) p (by omega)
  let a := (H p).map T.mor₁ ≫ (e p).hom
  have hc : d (p - 1) ≫ c = 0 := by
    rw [← cancel_epi (e (p - 1)).hom, ← Category.assoc, ← hd]
    simp only [c, Category.assoc, Iso.hom_inv_id_assoc, comp_zero]
    exact (H 0).comp_homologySequenceδ T hT (p - 1) p (by omega)
  have hca : c ≫ a = 0 := by
    dsimp only [c, a]
    erw [Category.assoc, ← Category.assoc _ _ (e p).hom,
      (H 0).homologySequenceδ_comp T hT (p - 1) p (by omega), zero_comp, comp_zero]
  have ha : a ≫ d p = 0 := by
    dsimp only [a]
    rw [Category.assoc, ← hd, ← Category.assoc, ← Functor.map_comp,
      comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero, zero_comp]
  have hc_exact : (ShortComplex.mk (d (p - 1)) c hc).Exact := by
    apply ShortComplex.exact_of_iso _
      ((H 0).homologySequence_exact₃ T hT (p - 1) p (by omega))
    exact ShortComplex.isoMk (e (p - 1)) (e (p - 1)) (Iso.refl _)
      (hd (p - 1)).symm (by simp [c])
  have hca_exact : (ShortComplex.mk c a hca).Exact := by
    apply ShortComplex.exact_of_iso _
      ((H 0).homologySequence_exact₁ T hT (p - 1) p (by omega))
    exact ShortComplex.isoMk (e (p - 1)) (Iso.refl _) (e p)
      (by simp [c]) (by simp [a, H, shift_homologyFunctor])
  have ha_exact : (ShortComplex.mk a (d p) ha).Exact := by
    apply ShortComplex.exact_of_iso _ ((H 0).homologySequence_exact₂ T hT p)
    exact ShortComplex.isoMk (Iso.refl _) (e p) (e p)
      (by simp [a, H, shift_homologyFunctor]) (hd p).symm
  obtain ⟨hz, hse⟩ := shortExact_cokernel_kernel (d (p - 1)) c a (d p)
    hc hca ha hc_exact hca_exact ha_exact
  let eLim : limit (V p) ≅ kernel (d p) :=
    (inverseSystemLimitKernelForkIsLimit (V p)).conePointUniqueUpToIso (limit.isLimit _)
  have heLim : eLim.hom ≫ kernel.ι (d p) = Pi.lift (fun n : ℕ ↦ limit.π (V p) ⟨n⟩) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  let i := cokernel.desc (d (p - 1)) c hc
  let q := kernel.lift (d p) a ha ≫ eLim.inv
  have hiq : i ≫ q = 0 := by
    dsimp only [q]
    rw [← Category.assoc, hz, zero_comp]
  refine ⟨e (p - 1), i, q, hiq, he (p - 1), ?_, ?_, ?_⟩
  · show (e (p - 1)).hom ≫ cokernel.π (d (p - 1)) ≫ i =
      (H 0).homologySequenceδ T (p - 1) p (by omega)
    simp [i, c]
  · intro n
    have hq : q ≫ Pi.lift (fun n : ℕ ↦ limit.π (V p) ⟨n⟩) = a := by
      rw [← heLim]
      simp [q]
    have h := congrArg (fun g ↦ g ≫ Pi.π (fun n : ℕ ↦ (V p).obj ⟨n⟩) n) hq
    show q ≫ limit.π (V p) ⟨n⟩ = (H p).map (T.mor₁ ≫ Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n))
    simpa [Category.assoc, a, he, Functor.map_comp] using h
  · apply ShortComplex.shortExact_of_iso _ hse
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) eLim.symm (by simp [i]) (by simp [q])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem powerQuotientSystem_isMittagLeffler
    (A : Type u) [CommRing A] (M : ModuleCat.{v} A) (f : A) :
    (CompletionSequences.powerQuotientSystem A M f ⋙ forget (ModuleCat.{v} A)).IsMittagLeffler := by
  let Q := CompletionSequences.powerQuotientSystem A M f
  let π : (Functor.const ℕᵒᵖ).obj M ⟶ Q := NatTrans.ofOpSequence
    (fun n ↦ cokernel.π (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1)))) (by
      intro n
      show 𝟙 M ≫ cokernel.π (PrincipalTorsionTower.powerMultiplication A M (f ^ (n + 1))) = _
      rw [Category.id_comp, CompletionSequences.powerQuotientSystem_map_succ]
      exact (CompletionSequences.π_powerQuotientTransition A M f n).symm)
  have hπ (n : ℕᵒᵖ) : Epi (π.app n) := by dsimp [π]; infer_instance
  apply Functor.isMittagLeffler_of_surjective
  intro n m g
  apply (ModuleCat.epi_iff_surjective (Q.map g)).mp
  have h : π.app n ≫ Q.map g = π.app m := by simpa using (π.naturality g).symm
  have : Epi (π.app n ≫ Q.map g) := by rw [h]; infer_instance
  exact epi_of_epi (π.app n) (Q.map g)

private theorem isIso_cokernelMap_of_epi_left
    {C : Type*} [Category C] [Abelian C]
    {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₂ : S₂.Exact) [Epi S₁.g] [Epi S₂.g] [Epi φ.τ₁] :
    IsIso (cokernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃) := by
  have hf : S₂.f ≫ cokernel.π φ.τ₂ = 0 := by
    rw [← cancel_epi φ.τ₁, ← Category.assoc, φ.comm₁₂]
    simp
  let k := h₂.desc (cokernel.π φ.τ₂) hf
  have hk : S₂.g ≫ k = cokernel.π φ.τ₂ := h₂.g_desc _ hf
  have hk₀ : φ.τ₃ ≫ k = 0 := by
    rw [← cancel_epi S₁.g, ← Category.assoc, ← φ.comm₂₃, Category.assoc, hk,
      cokernel.condition, comp_zero]
  let r := cokernel.desc φ.τ₃ k hk₀
  let l := cokernel.map φ.τ₂ φ.τ₃ S₁.g S₂.g φ.comm₂₃
  refine ⟨⟨r, ?_, ?_⟩⟩
  · apply (cancel_epi (cokernel.π φ.τ₂)).1
    simp only [Category.assoc, cokernel.map, cokernel.π_desc_assoc, r, cokernel.π_desc,
      Category.comp_id]
    exact hk
  · apply (cancel_epi (cokernel.π φ.τ₃)).1
    apply (cancel_epi S₂.g).1
    simp only [r, cokernel.π_desc_assoc, Category.comp_id]
    rw [← Category.assoc, hk]
    exact cokernel.π_desc _ _ _

private theorem product_shortExact
    {C : Type*} [Category C] [Abelian C] [HasProductsOfShape ℕ C]
    [HasExactLimitsOfShape (Discrete ℕ) C]
    (S : ℕ → ShortComplex C) (hS : ∀ n, (S n).ShortExact) :
    ∃ h : Limits.Pi.map (fun n ↦ (S n).f) ≫ Limits.Pi.map (fun n ↦ (S n).g) = 0,
      (ShortComplex.mk (Limits.Pi.map (fun n ↦ (S n).f))
        (Limits.Pi.map (fun n ↦ (S n).g)) h).ShortExact := by
  have hf (n : ℕ) : Mono (S n).f := (hS n).mono_f
  have hg (n : ℕ) : Epi (S n).g := (hS n).epi_g
  let f := Limits.Pi.map (fun n ↦ (S n).f)
  let g := Limits.Pi.map (fun n ↦ (S n).g)
  have hfg : f ≫ g = 0 := by
    apply Pi.hom_ext
    intro n
    simp [f, g]
  have : Epi g := by
    let α : Discrete.functor (fun n ↦ (S n).X₂) ⟶
        Discrete.functor (fun n ↦ (S n).X₃) :=
      Discrete.natTrans fun n ↦ (S n.as).g
    have : ∀ n : Discrete ℕ, Epi (α.app n) := fun n ↦ hg n.as
    have : Epi α := NatTrans.epi_of_epi_app α
    show Epi (lim.map α)
    infer_instance
  refine ⟨hfg, { mono_f := inferInstance, epi_g := inferInstance, exact := ?_ }⟩
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro W k hk
  have hk' (n : ℕ) : (k ≫ Pi.π (fun n ↦ (S n).X₂) n) ≫ (S n).g = 0 := by
    simpa [g, Category.assoc] using congrArg
      (fun a ↦ a ≫ Pi.π (fun n ↦ (S n).X₃) n) hk
  refine ⟨Pi.lift (fun n ↦ (hS n).exact.lift _ (hk' n)), ?_⟩
  apply Pi.hom_ext
  intro n
  simp [(hS n).exact.lift_f]

private theorem moduleDifference_naturality
    {A : Type u} [CommRing A] {E F : ℕᵒᵖ ⥤ ModuleCat.{v} A} (α : E ⟶ F) :
    CompletionSequences.moduleDifference A E ≫ Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩) =
      Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩) ≫ CompletionSequences.moduleDifference A F := by
  apply Pi.hom_ext
  intro n
  simp [CompletionSequences.moduleDifference, sub_comp, comp_sub, α.naturality]

private theorem firstDerivedLimit_map_isIso
    {A : Type u} [CommRing A] (S : ShortComplex (ℕᵒᵖ ⥤ ModuleCat.{v} A))
    (hS : ∀ n, (S.map ((evaluation ℕᵒᵖ (ModuleCat.{v} A)).obj n)).ShortExact)
    [Epi (CompletionSequences.moduleDifference A S.X₁)] :
    IsIso (cokernel.map (CompletionSequences.moduleDifference A S.X₂)
      (CompletionSequences.moduleDifference A S.X₃)
      (Limits.Pi.map (fun n : ℕ ↦ S.g.app ⟨n⟩))
      (Limits.Pi.map (fun n : ℕ ↦ S.g.app ⟨n⟩)) (moduleDifference_naturality S.g)) := by
  obtain ⟨hz, he⟩ := product_shortExact
    (fun n : ℕ ↦ S.map ((evaluation ℕᵒᵖ (ModuleCat.{v} A)).obj ⟨n⟩)) (fun n ↦ hS ⟨n⟩)
  let P := ShortComplex.mk (Limits.Pi.map (fun n : ℕ ↦ S.f.app ⟨n⟩))
    (Limits.Pi.map (fun n : ℕ ↦ S.g.app ⟨n⟩)) hz
  let φ : P ⟶ P :=
    { τ₁ := CompletionSequences.moduleDifference A S.X₁
      τ₂ := CompletionSequences.moduleDifference A S.X₂
      τ₃ := CompletionSequences.moduleDifference A S.X₃
      comm₁₂ := moduleDifference_naturality S.f
      comm₂₃ := moduleDifference_naturality S.g }
  have : Epi P.g := he.epi_g
  exact isIso_cokernelMap_of_epi_left φ he.exact

end PrincipalCompletionDiagram
end

end
