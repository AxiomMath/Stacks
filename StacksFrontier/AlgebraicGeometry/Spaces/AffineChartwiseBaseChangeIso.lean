module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineBaseChangeCompCriterion

/-!
# Condition (2) of Stacks 0DKG is invariant under isomorphism

For a commutative square of algebraic spaces, `K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and
`φ : L(g')^*K ⟶ K'`, condition (2) of Stacks 0DKG
(`AlgebraicGeometry.Space.AffineChartwiseBaseChange`) depends on `(K, K', φ)` only up to
isomorphism: if `e : K₁ ≅ K₂` and `e' : K₁' ≅ K₂'` carry `φ₁` to `φ₂`, the condition holds for
`φ₁` exactly when it holds for `φ₂`.

## Main results

* `AlgebraicGeometry.Space.isIso_representedAffineSectionsBaseChangeComp_iff_of_iso`: the same on
  one affine square.
* `AlgebraicGeometry.Space.AffineChartwiseBaseChange.of_iso` and
  `AlgebraicGeometry.Space.affineChartwiseBaseChange_iff_of_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.Generic

/-- The transpose under `Φ' ⊣ Γ'` of `β⁻¹ ≫ L(ε_K) ≫ ψ` is natural in the triple `(K, K', ψ)`. -/
theorem homEquiv_counit_transpose_naturality {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁]
    [Category D₀] [Category D₁] {Φ : C₀ ⥤ D₀} {Γ : D₀ ⥤ C₀} (adj : Φ ⊣ Γ) {Φ' : C₁ ⥤ D₁}
    {Γ' : D₁ ⥤ C₁} (adj' : Φ' ⊣ Γ') (L : D₀ ⥤ D₁) (Dx : C₀ ⥤ C₁) (β : Φ ⋙ L ≅ Dx ⋙ Φ')
    {K₁ K₂ : D₀} {K₁' K₂' : D₁} (e : K₁ ⟶ K₂) (e' : K₁' ⟶ K₂') (ψ₁ : L.obj K₁ ⟶ K₁')
    (ψ₂ : L.obj K₂ ⟶ K₂') (h : ψ₁ ≫ e' = L.map e ≫ ψ₂) :
    Dx.map (Γ.map e) ≫ adj'.homEquiv _ _ (β.inv.app (Γ.obj K₂) ≫ L.map (adj.counit.app K₂) ≫ ψ₂) =
      adj'.homEquiv _ _ (β.inv.app (Γ.obj K₁) ≫ L.map (adj.counit.app K₁) ≫ ψ₁) ≫
        Γ'.map e' := by
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have hβ : Φ'.map (Dx.map (Γ.map e)) ≫ β.inv.app (Γ.obj K₂) =
      β.inv.app (Γ.obj K₁) ≫ L.map (Φ.map (Γ.map e)) := β.inv.naturality (Γ.map e)
  have hε : Φ.map (Γ.map e) ≫ adj.counit.app K₂ = adj.counit.app K₁ ≫ e :=
    adj.counit_naturality e
  rw [reassoc_of% hβ, ← L.map_comp_assoc, hε, L.map_comp_assoc, ← h]
  simp only [Category.assoc]

/-- A morphism conjugate to another by isomorphisms is invertible exactly when the other is. -/
theorem isIso_iff_of_comm_sq {C : Type*} [Category C] {a₁ a₂ b₁ b₂ : C} (x : a₁ ⟶ a₂)
    (y : b₁ ⟶ b₂) [IsIso x] [IsIso y] (f₁ : a₁ ⟶ b₁) (f₂ : a₂ ⟶ b₂) (h : x ≫ f₂ = f₁ ≫ y) :
    IsIso f₁ ↔ IsIso f₂ := by
  have h₂ : f₂ = inv x ≫ f₁ ≫ y := by rw [← h, IsIso.inv_hom_id_assoc]
  have h₁ : f₁ = x ≫ f₂ ≫ inv y := by rw [reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]
  exact ⟨fun _ => by rw [h₂]; infer_instance, fun _ => by rw [h₁]; infer_instance⟩

/-- The composite `σ_{ΓK} ≫ ρ(transpose of β⁻¹ ≫ L(ε_K) ≫ ψ)` is invertible for one triple
`(K, K', ψ)` exactly when it is for an isomorphic one. -/
theorem isIso_comp_transpose_iff_of_iso {C₀ C₁ D₀ D₁ E : Type*} [Category C₀] [Category C₁]
    [Category D₀] [Category D₁] [Category E] {Φ : C₀ ⥤ D₀} {Γ : D₀ ⥤ C₀} (adj : Φ ⊣ Γ)
    {Φ' : C₁ ⥤ D₁} {Γ' : D₁ ⥤ C₁} (adj' : Φ' ⊣ Γ') (L : D₀ ⥤ D₁) (Dx : C₀ ⥤ C₁)
    (β : Φ ⋙ L ≅ Dx ⋙ Φ') (P : C₀ ⥤ E) (ρ : C₁ ⥤ E) (σ : P ⟶ Dx ⋙ ρ)
    {K₁ K₂ : D₀} {K₁' K₂' : D₁} (e : K₁ ≅ K₂) (e' : K₁' ≅ K₂') (ψ₁ : L.obj K₁ ⟶ K₁')
    (ψ₂ : L.obj K₂ ⟶ K₂') (h : ψ₁ ≫ e'.hom = L.map e.hom ≫ ψ₂) :
    IsIso (σ.app (Γ.obj K₁) ≫ ρ.map (adj'.homEquiv _ _
        (β.inv.app (Γ.obj K₁) ≫ L.map (adj.counit.app K₁) ≫ ψ₁))) ↔
      IsIso (σ.app (Γ.obj K₂) ≫ ρ.map (adj'.homEquiv _ _
        (β.inv.app (Γ.obj K₂) ≫ L.map (adj.counit.app K₂) ≫ ψ₂))) := by
  have hnat := homEquiv_counit_transpose_naturality adj adj' L Dx β e.hom e'.hom ψ₁ ψ₂ h
  have hσ : P.map (Γ.map e.hom) ≫ σ.app (Γ.obj K₂) =
      σ.app (Γ.obj K₁) ≫ ρ.map (Dx.map (Γ.map e.hom)) := σ.naturality (Γ.map e.hom)
  refine isIso_iff_of_comm_sq (P.map (Γ.map e.hom)) (ρ.map (Γ'.map e'.hom)) _ _ ?_
  rw [reassoc_of% hσ, ← ρ.map_comp, hnat, ρ.map_comp, Category.assoc]

/-- Naturality of a composite of three transformations followed by a map induced by `φ`. -/
theorem three_trans_map_naturality {C D E : Type*} [Category C] [Category D] [Category E]
    {F₁ F₂ F₃ : C ⥤ D} (G : C ⥤ E) (M : E ⥤ D) (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃)
    (γ : F₃ ⟶ G ⋙ M) {K₁ K₂ : C} {K₁' K₂' : E} (e : K₁ ⟶ K₂) (e' : K₁' ⟶ K₂')
    (φ₁ : G.obj K₁ ⟶ K₁') (φ₂ : G.obj K₂ ⟶ K₂') (h : φ₁ ≫ e' = G.map e ≫ φ₂) :
    (α.app K₁ ≫ β.app K₁ ≫ γ.app K₁ ≫ M.map φ₁) ≫ M.map e' =
      F₁.map e ≫ α.app K₂ ≫ β.app K₂ ≫ γ.app K₂ ≫ M.map φ₂ := by
  have hγ : F₃.map e ≫ γ.app K₂ = γ.app K₁ ≫ M.map (G.map e) := γ.naturality e
  rw [Category.assoc, Category.assoc, Category.assoc, ← M.map_comp, h, M.map_comp,
    ← reassoc_of% hγ, ← β.naturality_assoc, ← α.naturality_assoc]

end Stacks.Generic

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Affine

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)

/-- **The map of condition (2) of Stacks 0DJ8 on an affine square is invariant under
isomorphism**: for `e : K₁ ≅ K₂`, `e' : K₁' ≅ K₂'` carrying `φ₁` to `φ₂`, the composite of
Stacks 065Z with the map induced by `φ₁` is invertible exactly when the one for `φ₂` is. -/
theorem isIso_representedAffineSectionsBaseChangeComp_iff_of_iso
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))}
    {K₁' K₂' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
      ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩))}
    (e : K₁ ≅ K₂) (e' : K₁' ≅ K₂')
    (φ₁ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K₁ ⟶ K₁')
    (φ₂ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).obj K₂ ⟶ K₂')
    (h : φ₁ ≫ e'.hom =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map e.hom ≫ φ₂) :
    IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ K₁ K₁' φ₁) ↔
      IsIso (representedAffineSectionsBaseChangeComp B S hS f₀ g₀ f₀' g₀' w₀ K₂ K₂' φ₂) := by
  unfold representedAffineSectionsBaseChangeComp representedAffineSectionsBaseChangeMap
  exact Stacks.Generic.isIso_comp_transpose_iff_of_iso
    (representedAffineDerivedAdjunction B S hS U) (representedAffineDerivedAdjunction B S hS U')
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀'))
    (representedAffineDerivedExtension B S hS g₀').functor
    (representedAffineToposDerivedBaseChangeIso B S hS g₀') _ _
    (RingTheory.TorIndependence.ringHomSquareComparison
      (representedAffineCommRingCatHom B S hS f₀).hom
      (representedAffineCommRingCatHom B S hS g₀).hom
      (representedAffineCommRingCatHom B S hS g₀').hom
      (representedAffineCommRingCatHom B S hS f₀').hom
      ((representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀).trans
        (representedAffineRingHom_comp B S hS f₀' g₀))) e e' φ₁ φ₂ h

end Affine

section Condition

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X)

/-- **Condition (2) of Stacks 0DKG transfers along isomorphisms** of `(K, K', φ)`. -/
theorem AffineChartwiseBaseChange.of_iso (w : g' ≫ f = f' ≫ g)
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {K₁' K₂' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (e : K₁ ≅ K₂) (e' : K₁' ≅ K₂')
    (φ₁ : (smallEtaleDerivedModulePullback B S hS g').obj K₁ ⟶ K₁')
    (φ₂ : (smallEtaleDerivedModulePullback B S hS g').obj K₂ ⟶ K₂')
    (h : φ₁ ≫ e'.hom = (smallEtaleDerivedModulePullback B S hS g').map e.hom ≫ φ₂)
    (h₁ : AffineChartwiseBaseChange B S hS f g f' g' w K₁ K₁' φ₁) :
    AffineChartwiseBaseChange B S hS f g f' g' w K₂ K₂' φ₂ := by
  refine ⟨fun U V V' U' _ _ _ _ a b c a' f₀ g₀ f₀' g₀' w₀ ha hb hc hpb h₁' h₂' h₃' ha' => ?_⟩
  have hc₀ := Stacks.Generic.three_trans_map_naturality
    (smallEtaleDerivedModulePullback B S hS g') (smallEtaleDerivedModulePullback B S hS a')
    (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀') a).hom
    (smallEtaleDerivedModulePullbackCongr B S hS ha').hom
    (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv e.hom e'.hom φ₁ φ₂ h
  exact (isIso_representedAffineSectionsBaseChangeComp_iff_of_iso f₀ g₀ f₀' g₀' w₀
    ((smallEtaleDerivedModulePullback B S hS a).mapIso e)
    ((smallEtaleDerivedModulePullback B S hS a').mapIso e') _ _ hc₀).mp
    (h₁.isIso U V V' U' a b c a' f₀ g₀ f₀' g₀' w₀ ha hb hc hpb h₁' h₂' h₃' ha')

/-- **Condition (2) of Stacks 0DKG is invariant under isomorphisms** of `(K, K', φ)`. -/
theorem affineChartwiseBaseChange_iff_of_iso (w : g' ≫ f = f' ≫ g)
    {K₁ K₂ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {K₁' K₂' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))}
    (e : K₁ ≅ K₂) (e' : K₁' ≅ K₂')
    (φ₁ : (smallEtaleDerivedModulePullback B S hS g').obj K₁ ⟶ K₁')
    (φ₂ : (smallEtaleDerivedModulePullback B S hS g').obj K₂ ⟶ K₂')
    (h : φ₁ ≫ e'.hom = (smallEtaleDerivedModulePullback B S hS g').map e.hom ≫ φ₂) :
    AffineChartwiseBaseChange B S hS f g f' g' w K₁ K₁' φ₁ ↔
      AffineChartwiseBaseChange B S hS f g f' g' w K₂ K₂' φ₂ := by
  refine ⟨AffineChartwiseBaseChange.of_iso f g f' g' w e e' φ₁ φ₂ h,
    AffineChartwiseBaseChange.of_iso f g f' g' w e.symm e'.symm φ₂ φ₁ ?_⟩
  rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, h, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

end Condition

end AlgebraicGeometry.Space

end
