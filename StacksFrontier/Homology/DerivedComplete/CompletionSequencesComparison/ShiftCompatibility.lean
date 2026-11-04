module

public import StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.ShortExactSequences
import all StacksFrontier.Homology.DerivedComplete.CompletionSequencesComparison.ShortExactSequences

/-!
# Comparison of completions at a principal ideal: naturality and shifts

Auxiliary part of Stacks 0H32. This part proves the naturality of the projection, product
and inclusion maps of the Milnor sequences, the isomorphism criteria for the induced maps of
systems and Milnor triangles, the naturality of the principal triangles, and the compatibility
of the mapping cocones, the completion maps and the cohomology of single complexes with shifts.
-/

section


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory PrincipalTorsionTower

universe u v w x

namespace PrincipalCompletionDiagram

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] DerivedCategory.homologyFunctor_linear

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem milnorProjection_naturality
    {A : Type u} [CommRing A]
    {E F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ} (α : E ⟶ F) (p : ℤ)
    (qE : (homologyFunctor (ModuleCat.{v} A) p).obj (CompletionSequences.milnorTriangle A E).obj₁ ⟶
      limit (E ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) p))
    (qF : (homologyFunctor (ModuleCat.{v} A) p).obj (CompletionSequences.milnorTriangle A F).obj₁ ⟶
      limit (F ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) p))
    (hqE : ∀ n : ℕ, qE ≫ limit.π _ ⟨n⟩ =
      (homologyFunctor (ModuleCat.{v} A) p).map
        ((CompletionSequences.milnorTriangle A E).mor₁ ≫ Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n)))
    (hqF : ∀ n : ℕ, qF ≫ limit.π _ ⟨n⟩ =
      (homologyFunctor (ModuleCat.{v} A) p).map
        ((CompletionSequences.milnorTriangle A F).mor₁ ≫ Q.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n))) :
    qE ≫ limMap (Functor.whiskerRight α (Q ⋙ homologyFunctor (ModuleCat.{v} A) p)) =
      (homologyFunctor (ModuleCat.{v} A) p).map (milnorTriangleMap α).hom₁ ≫ qF := by
  apply limit.hom_ext
  intro n
  rw [Category.assoc, limMap_π, ← Category.assoc, hqE n.unop,
    Category.assoc, hqF n.unop]
  show _ ≫ (homologyFunctor (ModuleCat.{v} A) p).map (Q.map (α.app n)) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [← Category.assoc, ← (milnorTriangleMap α).comm₁, milnorTriangleMap_hom₂]
  simp only [Category.assoc, ← Functor.map_comp, Pi.map_π]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem milnorProduct_naturality
    {A : Type u} [CommRing A]
    {E F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ} (α : E ⟶ F) (p : ℤ)
    (eE : (homologyFunctor (ModuleCat.{v} A) p).obj (CompletionSequences.milnorTriangle A E).obj₃ ≅
      CompletionSequences.moduleProduct A (E ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) p))
    (eF : (homologyFunctor (ModuleCat.{v} A) p).obj (CompletionSequences.milnorTriangle A F).obj₃ ≅
      CompletionSequences.moduleProduct A (F ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) p))
    (heE : ∀ n : ℕ, eE.hom ≫ Pi.π _ n =
      (homologyFunctor (ModuleCat.{v} A) p).map (Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n)))
    (heF : ∀ n : ℕ, eF.hom ≫ Pi.π _ n =
      (homologyFunctor (ModuleCat.{v} A) p).map (Q.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n))) :
    eE.hom ≫ Limits.Pi.map (fun n : ℕ ↦
      (homologyFunctor (ModuleCat.{v} A) p).map (Q.map (α.app ⟨n⟩))) =
        (homologyFunctor (ModuleCat.{v} A) p).map (milnorTriangleMap α).hom₃ ≫ eF.hom := by
  apply Pi.hom_ext
  intro n
  erw [Category.assoc, Pi.map_π, ← Category.assoc, heE, Category.assoc, heF,
    milnorTriangleMap_hom₃, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp, Pi.map_π]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem milnorInclusion_naturality
    {A : Type u} [CommRing A]
    {E F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ} (α : E ⟶ F) (p : ℤ)
    (eE : (homologyFunctor (ModuleCat.{v} A) (p - 1)).obj
        (CompletionSequences.milnorTriangle A E).obj₃ ≅
      CompletionSequences.moduleProduct A (E ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) (p - 1)))
    (eF : (homologyFunctor (ModuleCat.{v} A) (p - 1)).obj
        (CompletionSequences.milnorTriangle A F).obj₃ ≅
      CompletionSequences.moduleProduct A (F ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) (p - 1)))
    (heE : ∀ n : ℕ, eE.hom ≫ Pi.π _ n =
      (homologyFunctor (ModuleCat.{v} A) (p - 1)).map
        (Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n)))
    (heF : ∀ n : ℕ, eF.hom ≫ Pi.π _ n =
      (homologyFunctor (ModuleCat.{v} A) (p - 1)).map
        (Q.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n)))
    (iE : CompletionSequences.firstDerivedLimit A
        (E ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) (p - 1)) ⟶
      (homologyFunctor (ModuleCat.{v} A) p).obj (CompletionSequences.milnorTriangle A E).obj₁)
    (iF : CompletionSequences.firstDerivedLimit A
        (F ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) (p - 1)) ⟶
      (homologyFunctor (ModuleCat.{v} A) p).obj (CompletionSequences.milnorTriangle A F).obj₁)
    (hiE : eE.hom ≫ cokernel.π (CompletionSequences.moduleDifference A
      (E ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) (p - 1))) ≫ iE =
      (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
        (CompletionSequences.milnorTriangle A E) (p - 1) p (by omega))
    (hiF : eF.hom ≫ cokernel.π (CompletionSequences.moduleDifference A
      (F ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) (p - 1))) ≫ iF =
      (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
        (CompletionSequences.milnorTriangle A F) (p - 1) p (by omega)) :
    let β := Functor.whiskerRight α (Q ⋙ homologyFunctor (ModuleCat.{v} A) (p - 1))
    cokernel.map (CompletionSequences.moduleDifference A
        (E ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) (p - 1)))
      (CompletionSequences.moduleDifference A
        (F ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) (p - 1)))
      (Limits.Pi.map (fun n : ℕ ↦ β.app ⟨n⟩))
      (Limits.Pi.map (fun n : ℕ ↦ β.app ⟨n⟩)) (moduleDifference_naturality β) ≫ iF =
        iE ≫ (homologyFunctor (ModuleCat.{v} A) p).map (milnorTriangleMap α).hom₁ := by
  dsimp only
  apply (cancel_epi (cokernel.π (CompletionSequences.moduleDifference A
    (E ⋙ Q ⋙ homologyFunctor (ModuleCat.{v} A) (p - 1))))).1
  apply (cancel_epi eE.hom).1
  dsimp only [cokernel.map, Functor.whiskerRight_app, Functor.comp_map]
  simp only [Category.assoc, cokernel.π_desc_assoc]
  rw [← Category.assoc eE.hom (Limits.Pi.map _),
    milnorProduct_naturality α (p - 1) eE eF heE heF, Category.assoc, hiF,
    ← Category.assoc _ iE, ← Category.assoc eE.hom, hiE]
  exact (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ_naturality
    (milnorTriangleMap α) (p - 1) p (by omega)

end PrincipalCompletionDiagram
end

end

section


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory PrincipalTorsionTower

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace PrincipalCompletionDiagram

attribute [local instance] DerivedCategory.homologyFunctor_linear

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalComplexSystemMap_isIso
    {A : Type u} [CommRing A] (f : A)
    {C D : CochainComplex (ModuleCat.{v} A) ℤ} (g : C ⟶ D) [IsIso (Q.map g)] :
    IsIso (Functor.whiskerRight (principalComplexSystemMap f g) Q) := by
  have hi (n : ℕᵒᵖ) : IsIso
      ((Functor.whiskerRight (principalComplexSystemMap f g) Q).app n) := by
    let φ := Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap
      (f ^ (n.unop + 1) • 𝟙 C) (f ^ (n.unop + 1) • 𝟙 D) g g
        (by simp [smul_comp, comp_smul]))
    exact isIso₃_of_isIso₁₂ φ (mappingCone_triangle_distinguished _)
      (mappingCone_triangle_distinguished _) (by dsimp [φ]; infer_instance)
      (by dsimp [φ]; infer_instance)
  exact NatIso.isIso_of_isIso_app _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem milnorTriangleMap_isIso
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    {E F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ} (α : E ⟶ F)
    [IsIso (Functor.whiskerRight α Q)] : IsIso (milnorTriangleMap α) := by
  have := Stacks.DerivedProducts.preservesLimitsOfShape_Q (A := ModuleCat.{v} A) (I := ℕ)
  let cE := piComparison Q (fun n : ℕ ↦ E.obj ⟨n⟩)
  let cF := piComparison Q (fun n : ℕ ↦ F.obj ⟨n⟩)
  have hcE : IsIso cE := inferInstance
  have hcF : IsIso cF := inferInstance
  have hi (n : ℕ) : IsIso (Q.map (α.app ⟨n⟩)) :=
    inferInstanceAs (IsIso ((Functor.whiskerRight α Q).app ⟨n⟩))
  have heq : Q.map (Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩)) =
      cE ≫ Limits.Pi.map (fun n : ℕ ↦ Q.map (α.app ⟨n⟩)) ≫ inv cF := by
    apply (cancel_mono cF).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    apply Pi.hom_ext
    intro n
    simp [cE, cF, ← Functor.map_comp, piComparison_comp_π]
  have hprod : IsIso (Q.map (Limits.Pi.map (fun n : ℕ ↦ α.app ⟨n⟩))) := by
    rw [heq]
    infer_instance
  have h₂ : IsIso (milnorTriangleMap α).hom₂ := by
    rw [milnorTriangleMap_hom₂]
    exact hprod
  have h₃ : IsIso (milnorTriangleMap α).hom₃ := by
    rw [milnorTriangleMap_hom₃]
    exact hprod
  exact Triangle.isIso_of_isIsos _
    (isIso₁_of_isIso₂₃ _ (CompletionSequences.milnorTriangle_distinguished A E)
      (CompletionSequences.milnorTriangle_distinguished A F) h₂ h₃) h₂ h₃

/-- Transport the square `v ≫ pZ = pX ≫ b` along the isomorphisms `u` and `a`. -/
private theorem inv_comp_comp_eq_of_square
    {C : Type*} [Category C] {X Y Z X' Y' Z' : C}
    (u : X ⟶ Y) (v : X ⟶ Z) (a : X' ⟶ Y') (b : X' ⟶ Z')
    (pX : X ⟶ X') (pY : Y ⟶ Y') (pZ : Z ⟶ Z') [IsIso u] [IsIso a]
    (hu : u ≫ pY = pX ≫ a) (hv : v ≫ pZ = pX ≫ b) :
    (inv u ≫ v) ≫ pZ = pY ≫ inv a ≫ b := by
  rw [(IsIso.eq_inv_comp u).2 hu]
  simp [hv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalTriangles_naturality
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (C D : CochainComplex (ModuleCat.{v} A) ℤ) (g : Q.obj C ⟶ Q.obj D) :
    let E := PrincipalTorsionTower.principalComplexSystem A f C
    let F := PrincipalTorsionTower.principalComplexSystem A f D
    ∃ (α : E ⋙ Q ⟶ F ⋙ Q)
      (φ : CompletionSequences.milnorTriangle A E ⟶ CompletionSequences.milnorTriangle A F)
      (ψ : ∀ n : ℕ, Q.mapTriangle.obj
          (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C)) ⟶
        Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 D))),
      (∀ n, (ψ n).hom₁ = g) ∧ (∀ n, (ψ n).hom₂ = g) ∧
      (∀ n, (ψ n).hom₃ = α.app ⟨n⟩) ∧
      (∀ n : ℕ, φ.hom₂ ≫ Q.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) =
        Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n) ≫ α.app ⟨n⟩) ∧
      (∀ n : ℕ, φ.hom₃ ≫ Q.map (Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) =
        Q.map (Pi.π (fun n : ℕ ↦ E.obj ⟨n⟩) n) ≫ α.app ⟨n⟩) ∧
      (completion ⋙ P.ι).map g ≫ (c.iso D).hom = (c.iso C).hom ≫ φ.hom₁ := by
  obtain ⟨B, s, hs, t, rfl⟩ := DerivedCategory.right_fac g
  let αs := Functor.whiskerRight (principalComplexSystemMap f s) Q
  let αt := Functor.whiskerRight (principalComplexSystemMap f t) Q
  have : IsIso αs := principalComplexSystemMap_isIso f s
  let φs := milnorTriangleMap (principalComplexSystemMap f s)
  let φt := milnorTriangleMap (principalComplexSystemMap f t)
  have : IsIso φs := milnorTriangleMap_isIso _
  let ψs (n : ℕ) := Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap
    (f ^ (n + 1) • 𝟙 B) (f ^ (n + 1) • 𝟙 C) s s
      (by simp [smul_comp, comp_smul]))
  let ψt (n : ℕ) := Q.mapTriangle.map (CochainComplex.mappingCone.triangleMap
    (f ^ (n + 1) • 𝟙 B) (f ^ (n + 1) • 𝟙 D) t t
      (by simp [smul_comp, comp_smul]))
  have hψs (n : ℕ) : IsIso (ψs n) := by
    apply Triangle.isIso_of_isIsos
    · dsimp [ψs]
      infer_instance
    · dsimp [ψs]
      infer_instance
    · exact inferInstanceAs (IsIso (αs.app ⟨n⟩))
  have hinv₁ (n : ℕ) : (inv (ψs n)).hom₁ = inv (Q.map s) := Functor.map_inv Triangle.π₁ (ψs n)
  have hinv₂ (n : ℕ) : (inv (ψs n)).hom₂ = inv (Q.map s) := Functor.map_inv Triangle.π₂ (ψs n)
  have hinv₃ (n : ℕ) : (inv (ψs n)).hom₃ = (inv αs).app ⟨n⟩ := by
    show (Triangle.π₃).map (inv (ψs n)) = _
    rw [Functor.map_inv]
    exact (Functor.map_inv ((evaluation ℕᵒᵖ _).obj ⟨n⟩) αs).symm
  have hst : ∀ {D'} (h : B ⟶ D') (n : ℕ),
      Q.map (Limits.Pi.map (fun n : ℕ ↦ (principalComplexSystemMap f h).app ⟨n⟩)) ≫
        Q.map (Pi.π (fun n : ℕ ↦
          (PrincipalTorsionTower.principalComplexSystem A f D').obj ⟨n⟩) n) =
      Q.map (Pi.π (fun n : ℕ ↦
        (PrincipalTorsionTower.principalComplexSystem A f B).obj ⟨n⟩) n) ≫
          (Functor.whiskerRight (principalComplexSystemMap f h) Q).app ⟨n⟩ := by
    intro D' h n
    rw [← Functor.map_comp, Pi.map_π, Functor.map_comp]
    rfl
  have hα (n : ℕ) : (inv αs ≫ αt).app ⟨n⟩ = inv (αs.app ⟨n⟩) ≫ αt.app ⟨n⟩ := by simp
  refine ⟨inv αs ≫ αt, inv φs ≫ φt, fun n ↦ inv (ψs n) ≫ ψt n,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 3
    intro n
    simp only [triangleCategory_comp, TriangleMorphism.comp_hom₁, TriangleMorphism.comp_hom₂,
      TriangleMorphism.comp_hom₃, hinv₁, hinv₂, hinv₃, NatTrans.comp_app]
    rfl
  · intro n
    show ((inv φs).hom₂ ≫ φt.hom₂) ≫ _ = _
    have : IsIso φs.hom₂ := inferInstanceAs (IsIso (Triangle.π₂.map φs))
    rw [hα, show (inv φs).hom₂ = inv φs.hom₂ from Functor.map_inv Triangle.π₂ φs]
    exact inv_comp_comp_eq_of_square _ _ _ _ _ _ _
      ((congrArg (· ≫ _) (milnorTriangleMap_hom₂ _)).trans (hst s n))
      ((congrArg (· ≫ _) (milnorTriangleMap_hom₂ _)).trans (hst t n))
  · intro n
    show ((inv φs).hom₃ ≫ φt.hom₃) ≫ _ = _
    have : IsIso φs.hom₃ := inferInstanceAs (IsIso (Triangle.π₃.map φs))
    rw [hα, show (inv φs).hom₃ = inv φs.hom₃ from Functor.map_inv Triangle.π₃ φs]
    exact inv_comp_comp_eq_of_square _ _ _ _ _ _ _
      ((congrArg (· ≫ _) (milnorTriangleMap_hom₃ _)).trans (hst s n))
      ((congrArg (· ≫ _) (milnorTriangleMap_hom₃ _)).trans (hst t n))
  · apply (cancel_epi ((completion ⋙ P.ι).map (Q.map s))).1
    have hinv : φs.hom₁ ≫ (inv φs).hom₁ = 𝟙 _ :=
      congrArg TriangleMorphism.hom₁ (IsIso.hom_inv_id φs)
    simp only [← Functor.map_comp_assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, completionComparison_naturality f adj c s]
    simp only [triangleCategory_comp, TriangleMorphism.comp_hom₁, Category.assoc]
    show _ = (c.iso B).hom ≫ φs.hom₁ ≫ (inv φs).hom₁ ≫ φt.hom₁
    rw [← Category.assoc φs.hom₁, hinv, Category.id_comp]
    exact completionComparison_naturality f adj c t

private theorem cochain_XIsoOfEq_hom_comp_v
    {C : Type*} [Category C] [Preadditive C]
    {K L : CochainComplex C ℤ} {n : ℤ}
    (γ : CochainComplex.HomComplex.Cochain K L n)
    (p p' q : ℤ) (hpq : p + n = q) (hpp' : p' = p) :
    (K.XIsoOfEq hpp').hom ≫ γ.v p q hpq = γ.v p' q (by omega) := by
  subst p'
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def mappingCoconeShiftIso
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (d : K ⟶ L) (n : ℤ) :
    (CochainComplex.mappingCocone d)⟦n⟧ ≅ CochainComplex.mappingCocone (d⟦n⟧') :=
  n.negOnePow • ((shiftFunctorComm (CochainComplex C ℤ) (-1) n).app
    (CochainComplex.mappingCone d) ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso (CochainComplex.mappingCone.shiftIso d n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem mappingCoconeShiftIso_hom_fst
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (d : K ⟶ L) (n : ℤ) :
    (mappingCoconeShiftIso d n).hom ≫ CochainComplex.mappingCocone.fst (d⟦n⟧') =
      (CochainComplex.mappingCocone.fst d)⟦n⟧' := by
  ext p
  dsimp only [mappingCoconeShiftIso, CochainComplex.mappingCocone]
  simp only [smul_iso_hom, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, HomologicalComplex.comp_f, HomologicalComplex.units_smul_f_apply]
  rw [CochainComplex.shiftFunctorComm_hom_app_f]
  dsimp [CochainComplex.mappingCocone.fst]
  rw [CochainComplex.HomComplex.Cochain.leftShift_v _ (-1) 0
    (by omega) p p (by omega) (p + -1) (by omega),
    CochainComplex.HomComplex.Cochain.leftShift_v _ (-1) 0
    (by omega) (p + n) (p + n) (by omega) (p + n + -1) (by omega)]
  simp only [Int.reduceNeg, Int.reduceMul, Int.reduceSub, Int.reduceDiv,
    Int.reduceAdd, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  simp only [Int.reduceNeg, CochainComplex.mappingCone.shiftIso, CochainComplex.shiftFunctor_obj_X,
    CochainComplex.shiftFunctor_obj_X', Int.negOnePow_one, Category.id_comp, Units.neg_smul,
    one_smul, neg_neg, units_smul_comp, Category.assoc, CochainComplex.mappingCone.lift_f_fst_v,
    CochainComplex.HomComplex.Cocycle.coe_units_smul, CochainComplex.HomComplex.Cocycle.shift_coe,
    CochainComplex.HomComplex.Cochain.units_smul_v, CochainComplex.HomComplex.Cochain.shift_v',
    comp_units_smul, smul_smul, Int.units_mul_self]
  exact cochain_XIsoOfEq_hom_comp_v _ _ _ _ (by omega) (by omega)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem mappingCoconeShiftIso_hom_snd
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (d : K ⟶ L) (n p q : ℤ) (hpq : p + -1 = q) :
    (mappingCoconeShiftIso d n).hom.f p ≫
        (CochainComplex.mappingCocone.snd (d⟦n⟧')).v p q hpq =
      n.negOnePow • ((CochainComplex.mappingCocone.snd d).shift n).v p q hpq := by
  subst q
  dsimp only [mappingCoconeShiftIso, CochainComplex.mappingCocone]
  simp only [smul_iso_hom, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, HomologicalComplex.comp_f, HomologicalComplex.units_smul_f_apply]
  rw [CochainComplex.shiftFunctorComm_hom_app_f]
  dsimp only [CochainComplex.mappingCocone.snd]
  rw [CochainComplex.HomComplex.Cochain.leftShift_v _ (-1) (-1)
    (by omega) p (p + -1) (by omega) (p + -1) (by omega)]
  rw [CochainComplex.HomComplex.Cochain.shift_v']
  rw [CochainComplex.HomComplex.Cochain.leftShift_v _ (-1) (-1)
    (by omega) (p + n) (p + -1 + n) (by omega) (p + n + -1) (by omega)]
  simp only [Int.reduceNeg, Int.reduceMul, Int.reduceSub, Int.reduceDiv,
    Int.reduceAdd, Int.negOnePow_even 2 ⟨1, rfl⟩, one_smul,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom]
  simp only [CochainComplex.shiftFunctor_map_f', Linear.units_smul_comp,
    Category.assoc, CochainComplex.mappingCone.shiftIso]
  erw [Category.id_comp, Category.id_comp,
    CochainComplex.mappingCone.lift_f_snd_v,
    CochainComplex.HomComplex.Cochain.shift_v']
  congr 1
  exact cochain_XIsoOfEq_hom_comp_v _ _ _ _ (by omega) (by omega)

private theorem mappingCone_map_fst
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : d₁ ≫ b = a ≫ d₂)
    (p q : ℤ) (hpq : p + 1 = q) :
    (CochainComplex.mappingCone.map d₁ d₂ a b h).f p ≫
        (CochainComplex.mappingCone.fst d₂).1.v p q hpq =
      (CochainComplex.mappingCone.fst d₁).1.v p q hpq ≫ a.f q := by
  simp [CochainComplex.mappingCone.ext_from_iff _ q p hpq,
    CochainComplex.mappingCone.map]

private theorem mappingCone_map_snd
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : d₁ ≫ b = a ≫ d₂) (p : ℤ) :
    (CochainComplex.mappingCone.map d₁ d₂ a b h).f p ≫
        (CochainComplex.mappingCone.snd d₂).v p p (add_zero p) =
      (CochainComplex.mappingCone.snd d₁).v p p (add_zero p) ≫ b.f p := by
  simp [CochainComplex.mappingCone.ext_from_iff _ (p + 1) p rfl,
    CochainComplex.mappingCone.map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem mappingCone_shiftIso_naturality
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (d₁ : K₁ ⟶ L₁) (d₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h : d₁ ≫ b = a ≫ d₂) (n : ℤ) :
    (CochainComplex.mappingCone.map d₁ d₂ a b h)⟦n⟧' ≫
        (CochainComplex.mappingCone.shiftIso d₂ n).hom =
      (CochainComplex.mappingCone.shiftIso d₁ n).hom ≫
        CochainComplex.mappingCone.map (d₁⟦n⟧') (d₂⟦n⟧') (a⟦n⟧') (b⟦n⟧')
          (by simp only [← Functor.map_comp, h]) := by
  ext p
  apply (CochainComplex.mappingCone.ext_to_iff _ p (p + 1) rfl _ _).2
  constructor
  · simp [CochainComplex.mappingCone.shiftIso, Category.assoc,
      mappingCone_map_fst, CochainComplex.HomComplex.Cochain.shift_v',
      CochainComplex.HomComplex.Cocycle.shift_coe,
      Linear.units_smul_comp, Linear.comp_units_smul]
  · simp [CochainComplex.mappingCone.shiftIso, Category.assoc,
      mappingCone_map_snd, CochainComplex.HomComplex.Cochain.shift_v']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def principalComplexSystemShiftMap
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) :
    PrincipalTorsionTower.principalComplexSystem A f C ⋙ shiftFunctor _ m ⟶
      PrincipalTorsionTower.principalComplexSystem A f (C⟦m⟧) :=
  NatTrans.ofOpSequence
    (fun n ↦ (CochainComplex.mappingCone.shiftIso (f ^ (n + 1) • 𝟙 C) m).hom)
    (by
      intro n
      dsimp only [Functor.comp_map]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact mappingCone_shiftIso_naturality _ _ _ _ _ m)

private theorem principalComplexSystemShiftMap_isIso
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) :
    IsIso (principalComplexSystemShiftMap f C m) := by
  have hi (n : ℕᵒᵖ) : IsIso ((principalComplexSystemShiftMap f C m).app n) := by
    show IsIso (CochainComplex.mappingCone.shiftIso (f ^ (n.unop + 1) • 𝟙 C) m).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private def principalProductShiftMap
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) :
    (CompletionSequences.complexProduct A (PrincipalTorsionTower.principalComplexSystem A f C))⟦m⟧ ⟶
      CompletionSequences.complexProduct A (PrincipalTorsionTower.principalComplexSystem A f (C⟦m⟧))
        :=
  piComparison (shiftFunctor _ m)
      (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩) ≫
    Limits.Pi.map (fun n : ℕ ↦ (principalComplexSystemShiftMap f C m).app ⟨n⟩)

private theorem principalProductShiftMap_π
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) (n : ℕ) :
    principalProductShiftMap f C m ≫
        Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f (C⟦m⟧)).obj ⟨n⟩) n =
      (Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩) n)⟦m⟧' ≫
        (principalComplexSystemShiftMap f C m).app ⟨n⟩ := by
  simp [principalProductShiftMap, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalProductShiftMap_difference
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) :
    (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
      C))⟦m⟧' ≫
        principalProductShiftMap f C m =
      principalProductShiftMap f C m ≫
        CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
          (C⟦m⟧)) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, principalProductShiftMap_π, ← Category.assoc,
    ← Functor.map_comp]
  simp only [CompletionSequences.complexDifference, Pi.lift_π, Functor.map_sub,
    Functor.map_comp, sub_comp, comp_sub, Category.assoc]
  rw [← Category.assoc (principalProductShiftMap f C m),
    principalProductShiftMap_π, principalProductShiftMap_π]
  have h := (principalComplexSystemShiftMap f C m).naturality
    (homOfLE (Nat.le_succ n)).op
  dsimp only [Functor.comp_map] at h
  rw [h, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalProductShiftMap_unit
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) :
    (CompletionSequences.principalComplexUnit A f C)⟦m⟧' ≫ principalProductShiftMap f C m =
      CompletionSequences.principalComplexUnit A f (C⟦m⟧) := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, principalProductShiftMap_π, ← Category.assoc,
    ← Functor.map_comp, CompletionSequences.principalComplexUnit_π,
    CompletionSequences.principalComplexUnit_π]
  exact CompletionSequences.coneShiftIso_hom_inr _ _

private def principalCompletionShiftMap
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) :
    (CochainComplex.mappingCocone
      (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
        C)))⟦m⟧ ⟶
    CochainComplex.mappingCocone
      (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
        (C⟦m⟧))) :=
  (mappingCoconeShiftIso
      (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f C))
        m).hom ≫
    (mappingCoconeTriangleMap _ _ (principalProductShiftMap f C m)
      (principalProductShiftMap f C m) (principalProductShiftMap_difference f C m)).hom₁

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalCompletionShiftMap_fst
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) :
    principalCompletionShiftMap f C m ≫
      CochainComplex.mappingCocone.fst
        (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
          (C⟦m⟧))) =
    (CochainComplex.mappingCocone.fst
      (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
        C)))⟦m⟧' ≫
        principalProductShiftMap f C m := by
  dsimp only [principalCompletionShiftMap]
  rw [Category.assoc, mappingCoconeTriangleMap_fst,
    ← Category.assoc, mappingCoconeShiftIso_hom_fst]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalCompletionShiftMap_snd
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m p q : ℤ) (hpq : p + -1 = q) :
    (principalCompletionShiftMap f C m).f p ≫
      (CochainComplex.mappingCocone.snd
        (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
          (C⟦m⟧)))).v
          p q hpq =
    m.negOnePow • ((CochainComplex.mappingCocone.snd
      (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
        C))).shift m).v
        p q hpq ≫ (principalProductShiftMap f C m).f q := by
  dsimp only [principalCompletionShiftMap]
  rw [HomologicalComplex.comp_f, Category.assoc, mappingCoconeTriangleMap_snd,
    ← Category.assoc, mappingCoconeShiftIso_hom_snd]
  exact Linear.units_smul_comp _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalCompletionShiftMap_projection
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) (n : ℕ) :
    principalCompletionShiftMap f C m ≫
      CochainComplex.mappingCocone.fst
        (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f
          (C⟦m⟧))) ≫
      Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f (C⟦m⟧)).obj ⟨n⟩) n =
    (CochainComplex.mappingCocone.fst
      (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f C))
        ≫
      Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩) n)⟦m⟧' ≫
        (principalComplexSystemShiftMap f C m).app ⟨n⟩ := by
  rw [← Category.assoc, principalCompletionShiftMap_fst, Category.assoc,
    principalProductShiftMap_π, Functor.map_comp, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalCompletionUnit_shift
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) :
    (CompletionSequences.principalCompletionUnit A f C)⟦m⟧' ≫ principalCompletionShiftMap f C m =
      CompletionSequences.principalCompletionUnit A f (C⟦m⟧) := by
  apply mappingCocone_hom_ext
  · dsimp only [principalCompletionShiftMap]
    rw [Category.assoc, Category.assoc, mappingCoconeTriangleMap_fst,
      ← Category.assoc _ (CochainComplex.mappingCocone.fst _),
      mappingCoconeShiftIso_hom_fst,
      ← Category.assoc, ← Functor.map_comp, CompletionSequences.principalCompletionUnit_fst,
      principalProductShiftMap_unit, CompletionSequences.principalCompletionUnit_fst]
  · intro p q hpq
    dsimp only [principalCompletionShiftMap]
    simp only [HomologicalComplex.comp_f, Category.assoc, mappingCoconeTriangleMap_snd]
    rw [← Category.assoc _ ((CochainComplex.mappingCocone.snd _).v p q hpq),
      mappingCoconeShiftIso_hom_snd]
    simp [Linear.comp_units_smul, Linear.units_smul_comp,
      CochainComplex.HomComplex.Cochain.shift_v',
      ← Category.assoc, CompletionSequences.principalCompletionUnit,
      CochainComplex.mappingCocone.lift_f_snd_v]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem completionComparison_shift
    {A : Type u} [CommRing A] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (s : CompletionSequences.CompletionShift A (completion ⋙ P.ι) adj.unit)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) :
    (completion ⋙ P.ι).map ((Q.commShiftIso m).hom.app C) ≫
      (s.iso (Q.obj C) m).hom ≫ ((c.iso C).hom)⟦m⟧' ≫
        (Q.commShiftIso m).inv.app
          (CochainComplex.mappingCocone
            (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A
              f C))) ≫
          Q.map (principalCompletionShiftMap f C m) = (c.iso (C⟦m⟧)).hom := by
  apply (cancel_mono (c.iso (C⟦m⟧)).inv).1
  apply reflector_hom_ext adj
  simp only [Category.assoc]
  erw [adj.unit_naturality_assoc]
  erw [← Category.assoc _ (s.iso (Q.obj C) m).hom, s.unit_iso]
  simp only [← Functor.map_comp_assoc, c.unit_iso]
  rw [← Q.commShiftIso_hom_naturality_assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, principalCompletionUnit_shift, ← c.unit_iso (C⟦m⟧),
    Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem homologyShiftIso_hom_app_Q_obj
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (m a a' : ℤ) (h : m + a = a') :
    (homologyFunctor C a).map ((Q.commShiftIso m).hom.app K) ≫
      ((homologyFunctor C 0).shiftIso m a a' h).hom.app (Q.obj K) =
    (homologyFunctorFactors C a).hom.app (K⟦m⟧) ≫
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso m a a' h).hom.app K ≫
        (homologyFunctorFactors C a').inv.app K := by
  have := shiftMap_homologyFunctor_map_Q (C := C) (𝟙 (K⟦m⟧)) a a' h
  simp only [Functor.shiftMap, ShiftedHom.map, Q.map_id, Category.id_comp] at this
  refine this.trans ?_
  congr 2
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem singleHomology_shift_complex
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : C) (m a a' : ℤ) (h : m + a = a') :
    HomologicalComplex.homologyMap
      (((CochainComplex.singleFunctors C).shiftIso m a a' h).inv.app M) a ≫
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso m a a' h).hom.app
        ((CochainComplex.singleFunctor C a').obj M) ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) a' M).hom =
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) a M).hom := by
  apply (cancel_epi (((CochainComplex.singleFunctor C a).obj M).homologyπ a)).1
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  show _ ≫ _ ≫ (CochainComplex.ShiftSequence.shiftIso C m a a' h).hom.app _ ≫ _ = _
  rw [CochainComplex.ShiftSequence.shiftIso_hom_app]
  erw [ShortComplex.homologyπ_naturality_assoc]
  erw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
  simp only [HomologicalComplex.singleObjCyclesSelfIso_hom]
  erw [ShortComplex.cyclesMap_i_assoc, HomologicalComplex.cyclesMap_i_assoc]
  simp [CochainComplex.singleFunctors, HomologicalComplex.singleObjXSelf,
    CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₂,
    HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.XIsoOfEq]
  rfl
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem singleHomology_shift
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (M : C) (m a a' : ℤ) (h : m + a = a') :
    (homologyFunctor C a).map (((singleFunctors C).shiftIso m a a' h).inv.app M) ≫
      ((homologyFunctor C 0).shiftIso m a a' h).hom.app
        ((singleFunctor C a').obj M) ≫
      (singleFunctorCompHomologyFunctorIso C a').hom.app M =
    (singleFunctorCompHomologyFunctorIso C a).hom.app M := by
  simp only [DerivedCategory.singleFunctors, SingleFunctors.postcomp_shiftIso_inv_app]
  show (homologyFunctor C a).map
    (Q.map (((CochainComplex.singleFunctors C).shiftIso m a a' h).inv.app M) ≫
      (Q.commShiftIso m).hom.app ((CochainComplex.singleFunctor C a').obj M)) ≫ _ = _
  erw [Functor.map_comp, Category.assoc, ← Category.assoc _
    (((homologyFunctor C 0).shiftIso m a a' h).hom.app _),
    homologyShiftIso_hom_app_Q_obj]
  have hsingle (i : ℤ) :
      (singleFunctorCompHomologyFunctorIso C i).hom.app M =
      (homologyFunctorFactors C i).hom.app ((CochainComplex.singleFunctor C i).obj M) ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i M).hom := by
    simp only [Functor.comp_obj, Functor.id_obj, singleFunctorCompHomologyFunctorIso,
      SingleFunctors.evaluation_obj, SingleFunctors.postcomp_functor, singleFunctorsPostcompQIso,
      Functor.mapIso_refl, Functor.isoWhiskerRight_refl, Iso.refl_trans, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
      HomologicalComplex.homologyFunctor_obj, Functor.whiskerLeft_app,
      HomologicalComplex.homologyFunctorSingleIso_hom_app]
    exact Category.id_comp _
  rw [hsingle a, hsingle a']
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc]
  erw [(homologyFunctorFactors C a).hom.naturality_assoc]
  exact congrArg ((homologyFunctorFactors C a).hom.app _ ≫ ·)
    (singleHomology_shift_complex M m a a' h)

universe u₁ v₁

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem shiftMap_shift
    {C : Type u} [Category.{v} C] [HasShift C ℤ]
    {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ D) [F.ShiftSequence ℤ]
    {X Y : C} (f : X ⟶ Y⟦(1 : ℤ)⟧) (m a b a' b' : ℤ)
    (hab : a + 1 = b) (ha : m + a = a') (hb : m + b = b') :
    F.shiftMap (f⟦m⟧' ≫ (shiftFunctorComm C 1 m).hom.app Y) a b (by omega) ≫
      (F.shiftIso m b b' hb).hom.app Y =
    (F.shiftIso m a a' ha).hom.app X ≫ F.shiftMap f a' b' (by omega) := by
  rw [F.shiftIso_hom_app_comp_shiftMap f m (1 + m) rfl a a' b' ha (by omega)]
  rw [F.shiftIso_add'_hom_app 1 m (1 + m) (by omega) a b b' (by omega) hb]
  simp only [Functor.shiftMap, shiftFunctorComm, Functor.map_comp,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  simp only [← Functor.map_comp_assoc, shiftFunctorAdd'_eq_shiftFunctorAdd]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private abbrev completionConeBoundary
    {A : Type u} [CommRing A] (f : A)
    {F : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A)}
    {η : 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F}
    (c : CompletionSequences.CompletionComparison A f F η)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (p q : ℤ) (hpq : p + 1 = q) (n : ℕ) :=
  (homologyFunctor (ModuleCat.{v} A) p).map ((c.iso C).hom ≫
    (CompletionSequences.milnorTriangle A (PrincipalTorsionTower.principalComplexSystem A f C)).mor₁
      ≫
    Q.map (Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩) n)) ≫
  (homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ
    (Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C))) p q hpq

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem completionConeBoundary_naturality
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] (f : A)
    {P : ObjectProperty (DerivedCategory (ModuleCat.{v} A))}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory}
    (adj : completion ⊣ P.ι)
    (c : CompletionSequences.CompletionComparison A f (completion ⋙ P.ι) adj.unit)
    (C D : CochainComplex (ModuleCat.{v} A) ℤ) (g : Q.obj C ⟶ Q.obj D)
    (p q : ℤ) (hpq : p + 1 = q) (n : ℕ) :
    (homologyFunctor (ModuleCat.{v} A) p).map ((completion ⋙ P.ι).map g) ≫
      completionConeBoundary f c D p q hpq n =
    completionConeBoundary f c C p q hpq n ≫
      (homologyFunctor (ModuleCat.{v} A) q).map g := by
  obtain ⟨α, φ, ψ, hψ₁, hψ₂, hψ₃, hφ₂, hφ₃, hc⟩ :=
    principalTriangles_naturality f adj c C D g
  dsimp only [completionConeBoundary]
  rw [← Functor.map_comp_assoc]
  have he : (completion ⋙ P.ι).map g ≫ (c.iso D).hom ≫
      (CompletionSequences.milnorTriangle A (PrincipalTorsionTower.principalComplexSystem A f
        D)).mor₁ ≫
      Q.map (Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f D).obj ⟨n⟩) n) =
    (c.iso C).hom ≫
      (CompletionSequences.milnorTriangle A (PrincipalTorsionTower.principalComplexSystem A f
        C)).mor₁ ≫
      Q.map (Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩) n) ≫
      (ψ n).hom₃ := by
    rw [← Category.assoc, hc, Category.assoc, ← Category.assoc φ.hom₁,
      ← φ.comm₁, Category.assoc, hφ₂, hψ₃]
  rw [he]
  simp only [Functor.map_comp, Category.assoc]
  erw [(homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ_naturality,
    hψ₁]
  rfl
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private abbrev principalCompletionBoundary
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :=
  CochainComplex.mappingCocone.fst
    (CompletionSequences.complexDifference A (PrincipalTorsionTower.principalComplexSystem A f C)) ≫
  Pi.π (fun n : ℕ ↦ (PrincipalTorsionTower.principalComplexSystem A f C).obj ⟨n⟩) n ≫
  (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C)).mor₃

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem principalCompletionShiftMap_boundary
    {A : Type u} [CommRing A] (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m : ℤ) (n : ℕ) :
    principalCompletionShiftMap f C m ≫ principalCompletionBoundary f (C⟦m⟧) n =
      m.negOnePow • ((principalCompletionBoundary f C n)⟦m⟧' ≫
        (shiftFunctorComm (CochainComplex (ModuleCat.{v} A) ℤ) 1 m).hom.app C) := by
  dsimp only [principalCompletionBoundary]
  rw [reassoc_of% principalCompletionShiftMap_projection f C m n]
  have hc : (principalComplexSystemShiftMap f C m).app ⟨n⟩ ≫
      (CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 (C⟦m⟧))).mor₃ =
      m.negOnePow • ((CochainComplex.mappingCone.triangle (f ^ (n + 1) • 𝟙 C)).mor₃⟦m⟧' ≫
        (shiftFunctorComm (CochainComplex (ModuleCat.{v} A) ℤ) 1 m).hom.app C) :=
    CompletionSequences.coneShiftIso_hom_mor₃ _ m
  rw [hc, Linear.comp_units_smul, Functor.map_comp, Category.assoc]
  simp only [Functor.map_comp, Category.assoc]

end PrincipalCompletionDiagram
end

end
