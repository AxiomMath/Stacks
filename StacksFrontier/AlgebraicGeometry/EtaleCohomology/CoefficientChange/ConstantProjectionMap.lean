module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedConstantSheaf

/-!
# The projection map for constant coefficients

Let `g : X ⟶ Y` be a morphism of schemes, `Λ` a commutative ring, `F` an étale sheaf of
`Λ`-modules on `X` and `M` a `Λ`-module, with constant sheaves `c_X M` and `c_Y M`. There is a
canonical map of étale sheaves of `Λ`-modules on `Y`

  `g_*F ⊗_Λ c_Y M ⟶ g_*(F ⊗_Λ c_X M)`,

the unit `c_Y M ⟶ g_* c_X M` tensored with `g_*F`, followed by the lax monoidal structure map
`g_*F ⊗ g_*G ⟶ g_*(F ⊗ G)` of the direct image. It is natural in `F` and in `M`, it is an
isomorphism for `M = Λ`, and it is compatible with the right unitors there. This is the
sheaf-level map underlying the projection formula behind the second diagram of
[Stacks, Remark 0GL6].

## Main definitions

* `Stacks.SheafTensorSections.presheafToSheafTensorIso`: the tensor product of two sheaves is the
  sheafification of the sectionwise tensor product of their underlying presheaves.
* `Stacks.SheafTensorSections.tensorSectionMap`: for sheaves `S`, `T` on a site with values in a
  monoidal category, the map of presheaves from the sectionwise tensor product `U ↦ S(U) ⊗ T(U)`
  to the sheaf tensor product.
* `Stacks.SheafTensorSections.sheafPushforwardTensorMap`: for a continuous functor `G` of sites,
  the map `G_*S ⊗ G_*T ⟶ G_*(S ⊗ T)`.
* `Stacks.SheafTensorSections.pushforwardSheafifyMap`: the map
  `sheafify(P ∘ G^op) ⟶ G_*(sheafify P)`, and its constant case
  `Stacks.SheafTensorSections.constantSheafPushforwardMap : c(M) ⟶ G_* c(M)`.
* `Stacks.SheafTensorSections.constantSheafUnitIso`: the constant sheaf on the monoidal unit is
  the monoidal unit of sheaves.
* `Stacks.SheafTensorSections.constantProjectionMap`: the projection map
  `G_*S ⊗ c(M) ⟶ G_*(S ⊗ c(M))`.
* `Stacks.EtaleCohomology.etaleModuleConstantSheafUnitIso`: `c_X Λ ≅ 𝟙`.
* `Stacks.EtaleCohomology.etaleModuleConstantProjectionMap`: the projection map for étale
  sheaves of `Λ`-modules, as a natural transformation of bifunctors
  `Sh(X_étale, Λ) ⥤ Mod(Λ) ⥤ Sh(Y_étale, Λ)`; its components are
  `Stacks.EtaleCohomology.etaleModuleConstantProjectionMapApp`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleConstantProjectionMapApp_naturality_left` and
  `Stacks.EtaleCohomology.etaleModuleConstantProjectionMapApp_naturality_right`: naturality in the
  sheaf and in the module.
* `Stacks.EtaleCohomology.etaleModuleConstantProjectionMap_rightUnitor`: compatibility with the
  right unitors at `M = Λ`.
* `Stacks.EtaleCohomology.isIso_etaleModuleConstantProjectionMap_app_unit`: the projection map is
  an isomorphism at `M = Λ`.

## Implementation notes

The tensor product of sheaves is `CategoryTheory.Sheaf.monoidalCategory`, the localization of the
sectionwise tensor product of presheaves along sheafification. Every map out of `S ⊗ T` is
determined by its composite with `tensorSectionMap`, which is a morphism inverted by
sheafification; the two structure maps are defined, and all identities are proved, through this
universal property. The direct image of sheaves is precomposition with `G^op`, which commutes on
the nose with the sectionwise tensor product and with constant presheaves, so no comparison
isomorphism is needed on the presheaf side.

`Stacks.ModuleSheafTensorSection.moduleToTensorSection` is the map `tensorSectionMap` for
`ModuleCat.{w} Λ`-valued sheaves with `Λ : Type w`. Étale sheaves of `Λ`-modules take values in
`ModuleCat.{max (u + 1) r} Λ` with `Λ : Type r`, which that declaration excludes; the construction
here is stated for an arbitrary monoidal category of coefficients.

## References

* [Stacks Project, Remark 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ v₂ v₃ u₁ u₂ u₃ u r

namespace Stacks.SheafTensorSections

section Sections

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A] [HasWeakSheafify J A]
  [(J.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

/-- The tensor product of two sheaves is the sheafification of the sectionwise tensor product of
their underlying presheaves. -/
def presheafToSheafTensorIso (S T : Sheaf J A) :
    (presheafToSheaf J A).obj (S.obj ⊗ T.obj) ≅ S ⊗ T :=
  (Functor.Monoidal.μIso (presheafToSheaf J A) S.obj T.obj).symm ≪≫
    (asIso ((sheafificationAdjunction J A).counit.app S) ⊗ᵢ
      asIso ((sheafificationAdjunction J A).counit.app T))

/-- The map from the sectionwise tensor product of two sheaves to their sheaf tensor product. -/
def tensorSectionMap (S T : Sheaf J A) : S.obj ⊗ T.obj ⟶ (S ⊗ T).obj :=
  toSheafify J (S.obj ⊗ T.obj) ≫ (presheafToSheafTensorIso J S T).hom.hom

/-- Two maps out of a tensor product of sheaves agree as soon as they agree on the sectionwise
tensor product. -/
lemma tensorSectionMap_hom_ext {S T U : Sheaf J A} {f g : S ⊗ T ⟶ U}
    (h : tensorSectionMap J S T ≫ f.hom = tensorSectionMap J S T ≫ g.hom) : f = g := by
  have : (presheafToSheafTensorIso J S T).hom ≫ f = (presheafToSheafTensorIso J S T).hom ≫ g := by
    apply ((sheafificationAdjunction J A).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit]
    simpa [tensorSectionMap] using h
  simpa using this

/-- Naturality of `presheafToSheafTensorIso`. -/
@[reassoc]
lemma presheafToSheafTensorIso_hom_naturality {S S' T T' : Sheaf J A} (f : S ⟶ S') (g : T ⟶ T') :
    (presheafToSheaf J A).map (f.hom ⊗ₘ g.hom) ≫ (presheafToSheafTensorIso J S' T').hom =
      (presheafToSheafTensorIso J S T).hom ≫ (f ⊗ₘ g) := by
  simp only [presheafToSheafTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
    tensorIso_hom, asIso_hom, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 2
  · exact (sheafificationAdjunction J A).counit.naturality f
  · exact (sheafificationAdjunction J A).counit.naturality g

/-- Naturality of the map from the sectionwise tensor product to the sheaf tensor product. -/
@[reassoc]
lemma tensorSectionMap_naturality {S S' T T' : Sheaf J A} (f : S ⟶ S') (g : T ⟶ T') :
    (f.hom ⊗ₘ g.hom) ≫ tensorSectionMap J S' T' = tensorSectionMap J S T ≫ (f ⊗ₘ g).hom := by
  simp only [tensorSectionMap]
  rw [toSheafify_naturality_assoc, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    ← ObjectProperty.FullSubcategory.comp_hom,
    presheafToSheafTensorIso_hom_naturality]

/-- Naturality of the map from the sectionwise tensor product in the second variable. -/
@[reassoc]
lemma tensorSectionMap_whiskerLeft (S : Sheaf J A) {T T' : Sheaf J A} (g : T ⟶ T') :
    (S.obj ◁ g.hom) ≫ tensorSectionMap J S T' = tensorSectionMap J S T ≫ (S ◁ g).hom := by
  simpa using tensorSectionMap_naturality J (𝟙 S) g

/-- Naturality of the map from the sectionwise tensor product in the first variable. -/
@[reassoc]
lemma tensorSectionMap_whiskerRight {S S' : Sheaf J A} (f : S ⟶ S') (T : Sheaf J A) :
    (f.hom ▷ T.obj) ≫ tensorSectionMap J S' T = tensorSectionMap J S T ≫ (f ▷ T).hom := by
  simpa using tensorSectionMap_naturality J f (𝟙 T)

/-- The right unitor of a sheaf `S`, through the sheafification of `S ⊗ 𝟙`. -/
lemma presheafToSheafTensorIso_rightUnitor (S : Sheaf J A) :
    (presheafToSheaf J A).map (S.obj ◁ toSheafify J (𝟙_ (Cᵒᵖ ⥤ A))) ≫
        (presheafToSheafTensorIso J S ((presheafToSheaf J A).obj (𝟙_ (Cᵒᵖ ⥤ A)))).hom ≫
          (S ◁ Functor.OplaxMonoidal.η (presheafToSheaf J A)) ≫ (ρ_ S).hom =
      (presheafToSheaf J A).map (ρ_ S.obj).hom ≫ (sheafificationAdjunction J A).counit.app S := by
  simp only [presheafToSheafTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv,
    tensorIso_hom, asIso_hom, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc, whiskerLeft_comp_tensorHom_assoc,
    Adjunction.left_triangle_components, tensorHom_id, ← whisker_exchange_assoc,
    rightUnitor_naturality, Functor.OplaxMonoidal.right_unitality_hom_assoc]

/-- The sectionwise right unitor, with the unit of sheaves written as the sheafification of the
unit of presheaves. -/
private lemma whiskerLeft_toSheafify_tensorSectionMap_rightUnitor_aux (S : Sheaf J A) :
    (S.obj ◁ toSheafify J (𝟙_ (Cᵒᵖ ⥤ A))) ≫
        tensorSectionMap J S ((presheafToSheaf J A).obj (𝟙_ (Cᵒᵖ ⥤ A))) ≫
          (S ◁ Functor.OplaxMonoidal.η (presheafToSheaf J A)).hom ≫ (ρ_ S).hom.hom =
      (ρ_ S.obj).hom := by
  have h := congrArg (fun φ => toSheafify J (S.obj ⊗ 𝟙_ (Cᵒᵖ ⥤ A)) ≫ φ.hom)
    (presheafToSheafTensorIso_rightUnitor J S)
  simp only [ObjectProperty.FullSubcategory.comp_hom] at h
  simp only [tensorSectionMap, Category.assoc]
  rw [toSheafify_naturality_assoc]
  refine h.trans ?_
  rw [← toSheafify_naturality_assoc]
  simp

/-- The constant sheaf on the monoidal unit is the monoidal unit of sheaves: both are the
sheafification of the constant presheaf on the unit. -/
def constantSheafUnitIso : (constantSheaf J A).obj (𝟙_ A) ≅ 𝟙_ (Sheaf J A) :=
  (Functor.Monoidal.εIso (presheafToSheaf J A)).symm

/-- The sheafification unit of a constant presheaf, with target the constant sheaf. -/
def constantToSheafify (M : A) :
    (Functor.const Cᵒᵖ).obj M ⟶ ((constantSheaf J A).obj M).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj M)

/-- **The sectionwise right unitor.** On the sectionwise tensor product with the sheafification
unit of the constant presheaf on the unit, the right unitor of a sheaf is the right unitor of its
underlying presheaf. -/
lemma whiskerLeft_toSheafify_tensorSectionMap_rightUnitor (S : Sheaf J A) :
    (S.obj ◁ constantToSheafify J (𝟙_ A)) ≫
        tensorSectionMap J S ((constantSheaf J A).obj (𝟙_ A)) ≫
          (S ◁ (constantSheafUnitIso J).hom).hom ≫ (ρ_ S).hom.hom =
      (ρ_ S.obj).hom :=
  whiskerLeft_toSheafify_tensorSectionMap_rightUnitor_aux J S

end Sections

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A] [HasWeakSheafify J A]
  [HasWeakSheafify K A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]
  (G : C ⥤ D) [G.IsContinuous J K]

attribute [local instance] Sheaf.monoidalCategory

/-- **The lax monoidal structure map of the direct image** `G_*S ⊗ G_*T ⟶ G_*(S ⊗ T)`: the
sheafification of the sectionwise map, the direct image commuting on the nose with the
sectionwise tensor product. -/
def sheafPushforwardTensorMap (S T : Sheaf K A) :
    (G.sheafPushforwardContinuous A J K).obj S ⊗ (G.sheafPushforwardContinuous A J K).obj T ⟶
      (G.sheafPushforwardContinuous A J K).obj (S ⊗ T) :=
  (presheafToSheafTensorIso J _ _).inv ≫
    ((sheafificationAdjunction J A).homEquiv _ _).symm
      (Functor.whiskerLeft G.op (tensorSectionMap K S T))

/-- The lax monoidal structure map of the direct image, on the sectionwise tensor product. -/
@[reassoc]
lemma tensorSectionMap_sheafPushforwardTensorMap (S T : Sheaf K A) :
    tensorSectionMap J ((G.sheafPushforwardContinuous A J K).obj S)
        ((G.sheafPushforwardContinuous A J K).obj T) ≫ (sheafPushforwardTensorMap J K G S T).hom =
      Functor.whiskerLeft G.op (tensorSectionMap K S T) := by
  rw [tensorSectionMap, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom,
    sheafPushforwardTensorMap, Iso.hom_inv_id_assoc]
  exact toSheafify_sheafifyLift (D := A) J (Functor.whiskerLeft G.op (tensorSectionMap K S T))
    ((G.sheafPushforwardContinuous A J K).obj (S ⊗ T)).property

/-- **Naturality of the lax monoidal structure map of the direct image.** -/
@[reassoc]
lemma sheafPushforwardTensorMap_naturality {S S' T T' : Sheaf K A} (f : S ⟶ S') (g : T ⟶ T') :
    ((G.sheafPushforwardContinuous A J K).map f ⊗ₘ (G.sheafPushforwardContinuous A J K).map g) ≫
        sheafPushforwardTensorMap J K G S' T' =
      sheafPushforwardTensorMap J K G S T ≫ (G.sheafPushforwardContinuous A J K).map (f ⊗ₘ g) := by
  apply tensorSectionMap_hom_ext J
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [← tensorSectionMap_naturality_assoc, tensorSectionMap_sheafPushforwardTensorMap,
    tensorSectionMap_sheafPushforwardTensorMap_assoc]
  change Functor.whiskerLeft G.op (f.hom ⊗ₘ g.hom) ≫
      Functor.whiskerLeft G.op (tensorSectionMap K S' T') =
    Functor.whiskerLeft G.op (tensorSectionMap K S T) ≫ Functor.whiskerLeft G.op (f ⊗ₘ g).hom
  rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, tensorSectionMap_naturality]

/-- The map `sheafify(P ∘ G^op) ⟶ G_*(sheafify P)`, adjoint to the sheafification unit of `P`
read through `G`. -/
def pushforwardSheafifyMap (P : Dᵒᵖ ⥤ A) :
    (presheafToSheaf J A).obj (G.op ⋙ P) ⟶
      (G.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P) :=
  ((sheafificationAdjunction J A).homEquiv _ _).symm (Functor.whiskerLeft G.op (toSheafify K P))

omit [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal] in
/-- The map `sheafify(P ∘ G^op) ⟶ G_*(sheafify P)` on the sheafification unit. -/
@[reassoc]
lemma toSheafify_pushforwardSheafifyMap (P : Dᵒᵖ ⥤ A) :
    toSheafify J (G.op ⋙ P) ≫ (pushforwardSheafifyMap J K G P).hom =
      Functor.whiskerLeft G.op (toSheafify K P) := by
  exact toSheafify_sheafifyLift (D := A) J (Functor.whiskerLeft G.op (toSheafify K P))
    ((G.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj P)).property

omit [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal] in
/-- Naturality of `sheafify(P ∘ G^op) ⟶ G_*(sheafify P)` in the presheaf `P`. -/
@[reassoc]
lemma pushforwardSheafifyMap_naturality {P Q : Dᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (presheafToSheaf J A).map (Functor.whiskerLeft G.op f) ≫ pushforwardSheafifyMap J K G Q =
      pushforwardSheafifyMap J K G P ≫
        (G.sheafPushforwardContinuous A J K).map ((presheafToSheaf K A).map f) := by
  refine Sheaf.hom_ext (sheafify_hom_ext J _ _ (ObjectProperty.FullSubcategory.property _) ?_)
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  rw [← toSheafify_naturality_assoc, toSheafify_pushforwardSheafifyMap,
    toSheafify_pushforwardSheafifyMap_assoc]
  ext U
  exact NatTrans.congr_app (toSheafify_naturality K f) _

end Pushforward

section Constant

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A] [HasWeakSheafify J A]
  [HasWeakSheafify K A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]
  (G : C ⥤ D) [G.IsContinuous J K]

attribute [local instance] Sheaf.monoidalCategory

/-- The comparison `c(M) ⟶ G_* c(M)` of constant sheaves: the direct image of a constant
presheaf is the constant presheaf, and the map is adjoint to the sheafification unit. -/
def constantSheafPushforwardMap (M : A) :
    (constantSheaf J A).obj M ⟶
      (G.sheafPushforwardContinuous A J K).obj ((constantSheaf K A).obj M) :=
  pushforwardSheafifyMap J K G ((Functor.const Dᵒᵖ).obj M)

omit [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal] in
/-- The comparison of constant sheaves on the sheafification unit. -/
@[reassoc]
lemma constantToSheafify_constantSheafPushforwardMap (M : A) :
    constantToSheafify J M ≫ (constantSheafPushforwardMap J K G M).hom =
      Functor.whiskerLeft G.op (constantToSheafify K M) :=
  toSheafify_pushforwardSheafifyMap J K G ((Functor.const Dᵒᵖ).obj M)

omit [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal] in
/-- Naturality of the comparison of constant sheaves. -/
@[reassoc]
lemma constantSheafPushforwardMap_naturality {M N : A} (f : M ⟶ N) :
    (constantSheaf J A).map f ≫ constantSheafPushforwardMap J K G N =
      constantSheafPushforwardMap J K G M ≫
        (G.sheafPushforwardContinuous A J K).map ((constantSheaf K A).map f) :=
  pushforwardSheafifyMap_naturality J K G ((Functor.const Dᵒᵖ).map f)

/-- **The projection map for constant coefficients**
`G_*S ⊗ c(M) ⟶ G_*(S ⊗ c(M))`: the comparison `c(M) ⟶ G_* c(M)` tensored with `G_*S`, followed
by the lax monoidal structure map of the direct image. -/
def constantProjectionMap (S : Sheaf K A) (M : A) :
    (G.sheafPushforwardContinuous A J K).obj S ⊗ (constantSheaf J A).obj M ⟶
      (G.sheafPushforwardContinuous A J K).obj (S ⊗ (constantSheaf K A).obj M) :=
  (G.sheafPushforwardContinuous A J K).obj S ◁ constantSheafPushforwardMap J K G M ≫
    sheafPushforwardTensorMap J K G S ((constantSheaf K A).obj M)

/-- Naturality of the projection map in the sheaf. -/
@[reassoc]
lemma constantProjectionMap_naturality_left {S S' : Sheaf K A} (f : S ⟶ S') (M : A) :
    (G.sheafPushforwardContinuous A J K).map f ▷ (constantSheaf J A).obj M ≫
        constantProjectionMap J K G S' M =
      constantProjectionMap J K G S M ≫
        (G.sheafPushforwardContinuous A J K).map (f ▷ (constantSheaf K A).obj M) := by
  have h := sheafPushforwardTensorMap_naturality J K G f (𝟙 ((constantSheaf K A).obj M))
  rw [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at h
  rw [constantProjectionMap, constantProjectionMap, ← whisker_exchange_assoc, h, Category.assoc]

/-- Naturality of the projection map in the module. -/
@[reassoc]
lemma constantProjectionMap_naturality_right (S : Sheaf K A) {M N : A} (f : M ⟶ N) :
    (G.sheafPushforwardContinuous A J K).obj S ◁ (constantSheaf J A).map f ≫
        constantProjectionMap J K G S N =
      constantProjectionMap J K G S M ≫
        (G.sheafPushforwardContinuous A J K).map (S ◁ (constantSheaf K A).map f) := by
  have h := sheafPushforwardTensorMap_naturality J K G (𝟙 S) ((constantSheaf K A).map f)
  rw [CategoryTheory.Functor.map_id, id_tensorHom, id_tensorHom] at h
  rw [constantProjectionMap, constantProjectionMap, ← whiskerLeft_comp_assoc,
    constantSheafPushforwardMap_naturality, whiskerLeft_comp_assoc, h, Category.assoc]

/-- **The projection map is compatible with the right unitors** at the monoidal unit:
`ρ_{G_*S} ∘ (G_*S ◁ e) = G_*(ρ_S) ∘ G_*(S ◁ e) ∘ proj`, where `e : c(𝟙) ≅ 𝟙` identifies the
constant sheaf on the unit with the unit of sheaves. -/
lemma constantProjectionMap_rightUnitor (S : Sheaf K A) :
    (G.sheafPushforwardContinuous A J K).obj S ◁ (constantSheafUnitIso J).hom ≫
        (ρ_ ((G.sheafPushforwardContinuous A J K).obj S)).hom =
      constantProjectionMap J K G S (𝟙_ A) ≫
        (G.sheafPushforwardContinuous A J K).map (S ◁ (constantSheafUnitIso K).hom) ≫
          (G.sheafPushforwardContinuous A J K).map (ρ_ S).hom := by
  apply tensorSectionMap_hom_ext J
  refine (J.W.whiskerLeft_mem ((G.sheafPushforwardContinuous A J K).obj S).obj _
    (J.W_toSheafify ((Functor.const Cᵒᵖ).obj (𝟙_ A))) _
    (ObjectProperty.FullSubcategory.property _)).1 ?_
  change ((G.sheafPushforwardContinuous A J K).obj S).obj ◁ constantToSheafify J (𝟙_ A) ≫ _ =
    ((G.sheafPushforwardContinuous A J K).obj S).obj ◁ constantToSheafify J (𝟙_ A) ≫ _
  simp only [constantProjectionMap, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  rw [whiskerLeft_toSheafify_tensorSectionMap_rightUnitor J
    ((G.sheafPushforwardContinuous A J K).obj S)]
  rw [← tensorSectionMap_whiskerLeft_assoc, ← whiskerLeft_comp_assoc,
    constantToSheafify_constantSheafPushforwardMap,
    tensorSectionMap_sheafPushforwardTensorMap_assoc]
  have h := whiskerLeft_toSheafify_tensorSectionMap_rightUnitor K S
  ext U
  have hU := NatTrans.congr_app h (G.op.obj U)
  simp only [NatTrans.comp_app] at hU ⊢
  exact hU.symm

/-- **The projection map is an isomorphism at the monoidal unit.** -/
instance isIso_constantProjectionMap_unit (S : Sheaf K A) :
    IsIso (constantProjectionMap J K G S (𝟙_ A)) := by
  have h := constantProjectionMap_rightUnitor J K G S
  rw [← Functor.map_comp] at h
  have : IsIso (constantProjectionMap J K G S (𝟙_ A) ≫
      (G.sheafPushforwardContinuous A J K).map
        (S ◁ (constantSheafUnitIso K).hom ≫ (ρ_ S).hom)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((G.sheafPushforwardContinuous A J K).map (S ◁ (constantSheafUnitIso K).hom ≫ (ρ_ S).hom))

end Constant

end Stacks.SheafTensorSections

namespace Stacks.EtaleCohomology

open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

variable (Λ : Type r) [CommRing Λ]

/-- The constant sheaf on the monoidal unit `Λ` is the monoidal unit of étale sheaves of
`Λ`-modules: both are the sheafification of the constant presheaf with value `Λ`. -/
def etaleModuleConstantSheafUnitIso (X : Scheme.{u}) :
    (etaleModuleConstantSheafFunctor.{u, r} Λ X).obj (𝟙_ (ModuleCat.{max (u + 1) r} Λ)) ≅
      𝟙_ (EtaleModules.{u, r} Λ X) :=
  letI := isMonoidal_W_smallEtale_module.{u, r} Λ X
  SheafTensorSections.constantSheafUnitIso X.smallEtaleTopology

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The projection map `g_*F ⊗ c_Y M ⟶ g_*(F ⊗ c_X M)` for étale sheaves of `Λ`-modules, at a
sheaf `F` and a module `M`. -/
def etaleModuleConstantProjectionMapApp (F : EtaleModules.{u, r} Λ X)
    (M : ModuleCat.{max (u + 1) r} Λ) :
    (etaleModuleDirectImage.{u, r} Λ g).obj F ⊗ (etaleModuleConstantSheafFunctor.{u, r} Λ Y).obj M ⟶
      (etaleModuleDirectImage.{u, r} Λ g).obj
        (F ⊗ (etaleModuleConstantSheafFunctor.{u, r} Λ X).obj M) :=
  letI := isMonoidal_W_smallEtale_module.{u, r} Λ X
  letI := isMonoidal_W_smallEtale_module.{u, r} Λ Y
  SheafTensorSections.constantProjectionMap Y.smallEtaleTopology X.smallEtaleTopology
    (smallEtaleBaseChange g) F M

/-- Naturality of the projection map in the sheaf. -/
@[reassoc]
theorem etaleModuleConstantProjectionMapApp_naturality_left {F F' : EtaleModules.{u, r} Λ X}
    (f : F ⟶ F') (M : ModuleCat.{max (u + 1) r} Λ) :
    (etaleModuleDirectImage.{u, r} Λ g).map f ▷ (etaleModuleConstantSheafFunctor.{u, r} Λ Y).obj M ≫
        etaleModuleConstantProjectionMapApp Λ g F' M =
      etaleModuleConstantProjectionMapApp Λ g F M ≫
        (etaleModuleDirectImage.{u, r} Λ g).map
          (f ▷ (etaleModuleConstantSheafFunctor.{u, r} Λ X).obj M) :=
  let := isMonoidal_W_smallEtale_module.{u, r} Λ X
  let := isMonoidal_W_smallEtale_module.{u, r} Λ Y
  SheafTensorSections.constantProjectionMap_naturality_left Y.smallEtaleTopology
    X.smallEtaleTopology (smallEtaleBaseChange g) f M

/-- Naturality of the projection map in the module. -/
@[reassoc]
theorem etaleModuleConstantProjectionMapApp_naturality_right (F : EtaleModules.{u, r} Λ X)
    {M N : ModuleCat.{max (u + 1) r} Λ} (φ : M ⟶ N) :
    (etaleModuleDirectImage.{u, r} Λ g).obj F ◁ (etaleModuleConstantSheafFunctor.{u, r} Λ Y).map φ ≫
        etaleModuleConstantProjectionMapApp Λ g F N =
      etaleModuleConstantProjectionMapApp Λ g F M ≫
        (etaleModuleDirectImage.{u, r} Λ g).map
          (F ◁ (etaleModuleConstantSheafFunctor.{u, r} Λ X).map φ) :=
  let := isMonoidal_W_smallEtale_module.{u, r} Λ X
  let := isMonoidal_W_smallEtale_module.{u, r} Λ Y
  SheafTensorSections.constantProjectionMap_naturality_right Y.smallEtaleTopology
    X.smallEtaleTopology (smallEtaleBaseChange g) F φ

/-- **The projection map for constant coefficients**, as a natural transformation of bifunctors
`Sh(X_étale, Λ) ⥤ Mod(Λ) ⥤ Sh(Y_étale, Λ)`, with components
`g_*F ⊗_Λ c_Y M ⟶ g_*(F ⊗_Λ c_X M)`: the comparison `c_Y M ⟶ g_* c_X M` of constant sheaves
tensored with `g_*F`, followed by the lax monoidal structure map of the direct image. -/
def etaleModuleConstantProjectionMap :
    etaleModuleDirectImage.{u, r} Λ g ⋙ curriedTensor (EtaleModules.{u, r} Λ Y) ⋙
        (Functor.whiskeringLeft _ _ _).obj (etaleModuleConstantSheafFunctor.{u, r} Λ Y) ⟶
      curriedTensor (EtaleModules.{u, r} Λ X) ⋙
        (Functor.whiskeringLeft _ _ _).obj (etaleModuleConstantSheafFunctor.{u, r} Λ X) ⋙
          (Functor.whiskeringRight _ _ _).obj (etaleModuleDirectImage.{u, r} Λ g) where
  app F :=
    { app M := etaleModuleConstantProjectionMapApp Λ g F M
      naturality _ _ φ := etaleModuleConstantProjectionMapApp_naturality_right Λ g F φ }
  naturality _ _ f :=
    NatTrans.ext (funext fun M ↦ etaleModuleConstantProjectionMapApp_naturality_left Λ g f M)

/-- The component of `etaleModuleConstantProjectionMap` at `F` and `M` is
`etaleModuleConstantProjectionMapApp Λ g F M`. -/
@[simp]
theorem etaleModuleConstantProjectionMap_app_app (F : EtaleModules.{u, r} Λ X)
    (M : ModuleCat.{max (u + 1) r} Λ) :
    ((etaleModuleConstantProjectionMap Λ g).app F).app M =
      etaleModuleConstantProjectionMapApp Λ g F M :=
  rfl

/-- **Compatibility of the projection map with the right unitors**: at `M = Λ`, the right
unitor of `g_*F`, read through the identification `c_Y Λ ≅ 𝟙`, is the projection map followed by
the direct image of the right unitor of `F`, read through `c_X Λ ≅ 𝟙`. -/
theorem etaleModuleConstantProjectionMap_rightUnitor (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleDirectImage.{u, r} Λ g).obj F ◁ (etaleModuleConstantSheafUnitIso Λ Y).hom ≫
        (ρ_ ((etaleModuleDirectImage.{u, r} Λ g).obj F)).hom =
      ((etaleModuleConstantProjectionMap Λ g).app F).app (𝟙_ (ModuleCat.{max (u + 1) r} Λ)) ≫
        (etaleModuleDirectImage.{u, r} Λ g).map (F ◁ (etaleModuleConstantSheafUnitIso Λ X).hom) ≫
          (etaleModuleDirectImage.{u, r} Λ g).map (ρ_ F).hom :=
  let := isMonoidal_W_smallEtale_module.{u, r} Λ X
  let := isMonoidal_W_smallEtale_module.{u, r} Λ Y
  SheafTensorSections.constantProjectionMap_rightUnitor Y.smallEtaleTopology
    X.smallEtaleTopology (smallEtaleBaseChange g) F

/-- **The projection map is an isomorphism at the unit** `M = Λ`:
`g_*F ⊗_Λ c_Y Λ ≅ g_*(F ⊗_Λ c_X Λ)`. -/
theorem isIso_etaleModuleConstantProjectionMap_app_unit (F : EtaleModules.{u, r} Λ X) :
    IsIso (((etaleModuleConstantProjectionMap Λ g).app F).app
      (𝟙_ (ModuleCat.{max (u + 1) r} Λ))) :=
  let := isMonoidal_W_smallEtale_module.{u, r} Λ X
  let := isMonoidal_W_smallEtale_module.{u, r} Λ Y
  SheafTensorSections.isIso_constantProjectionMap_unit Y.smallEtaleTopology
    X.smallEtaleTopology (smallEtaleBaseChange g) F

end Stacks.EtaleCohomology

end
