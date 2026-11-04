module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# Exact functors on morphisms between classes of complexes

Let `F : C₁ ⥤ C₂` be an exact functor of abelian categories. For complexes `P`, `I` of `C₁` and a
morphism `d : Q(P) ⟶ Q(I)` of the derived category, `F` gives a morphism `Q(F P) ⟶ Q(F I)`:
the image of `d` under `F.mapDerivedCategory`, read through the canonical factorization
`F.mapDerivedCategoryFactors`. Given an isomorphism `γ : F ⋙ T ≅ F'` of functors with `T` exact,
a morphism `Q(F P) ⟶ Q(F I)` is carried by `T` to a morphism `Q(F' P) ⟶ Q(F' I)`.

## Main definitions

* `Stacks.DerivedCategoryComparisons.restrictQMap`: `F` on a morphism `Q(P) ⟶ Q(I)`.
* `Stacks.DerivedCategoryComparisons.transportQMap`: `T` on a morphism `Q(F P) ⟶ Q(F I)`, read
  through `γ : F ⋙ T ≅ F'`.

## Main results

* `Stacks.DerivedCategoryComparisons.transportQMap_restrictQMap`: transporting the restriction
  of `d` along `γ` gives the restriction of `d` along `F'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₄ w₃ w₂ w₁

namespace Stacks.DerivedCategoryComparisons

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {C₄ : Type*} [Category C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]

section Restrict

variable (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor on a morphism `Q(P) ⟶ Q(I)` of the derived category, as a morphism
`Q(F P) ⟶ Q(F I)`. -/
def restrictQMap {P I : CochainComplex C₁ ℤ}
    (d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (F.mapDerivedCategoryFactors.app P).inv ≫ F.mapDerivedCategory.map d ≫
    (F.mapDerivedCategoryFactors.app I).hom

/-- `restrictQMap` sends the image `Q(f)` of a morphism of complexes `f` to `Q(F f)`. -/
lemma restrictQMap_Q_map {P I : CochainComplex C₁ ℤ} (f : P ⟶ I) :
    restrictQMap F (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  dsimp only [restrictQMap, Iso.app_inv, Iso.app_hom]
  rw [Functor.mapDerivedCategoryFactors_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- `restrictQMap` preserves composition. -/
lemma restrictQMap_comp {P I J : CochainComplex C₁ ℤ}
    (d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I)
    (e : DerivedCategory.Q.obj I ⟶ DerivedCategory.Q.obj J) :
    restrictQMap F (d ≫ e) = restrictQMap F d ≫ restrictQMap F e := by
  simp [restrictQMap]

/-- `restrictQMap` preserves identities. -/
lemma restrictQMap_id (P : CochainComplex C₁ ℤ) :
    restrictQMap F (𝟙 (DerivedCategory.Q.obj P)) = 𝟙 _ := by
  simp [restrictQMap]

/-- `restrictQMap` is injective when `F.mapDerivedCategory` is faithful. -/
lemma restrictQMap_injective [F.mapDerivedCategory.Faithful] {P I : CochainComplex C₁ ℤ} :
    Function.Injective (restrictQMap F (P := P) (I := I)) := by
  intro d d' h
  apply F.mapDerivedCategory.map_injective
  have := congrArg (fun t => (F.mapDerivedCategoryFactors.app P).hom ≫ t ≫
    (F.mapDerivedCategoryFactors.app I).inv) h
  simpa [restrictQMap] using this

/-- `restrictQMap` is surjective when `F.mapDerivedCategory` is full. -/
lemma restrictQMap_surjective [F.mapDerivedCategory.Full] {P I : CochainComplex C₁ ℤ} :
    Function.Surjective (restrictQMap F (P := P) (I := I)) := by
  intro β
  obtain ⟨d, hd⟩ := F.mapDerivedCategory.map_surjective
    ((F.mapDerivedCategoryFactors.app P).hom ≫ β ≫ (F.mapDerivedCategoryFactors.app I).inv)
  exact ⟨d, by simp [restrictQMap, hd]⟩

/-- Restricting along `F` and then along `T` is restricting along `F ⋙ T`. -/
lemma restrictQMap_comp_functor (T : C₂ ⥤ C₃) [T.Additive] [PreservesFiniteLimits T]
    [PreservesFiniteColimits T] {P I : CochainComplex C₁ ℤ}
    (d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :
    restrictQMap T (restrictQMap F d) = restrictQMap (F ⋙ T) d := by
  let c := mapDerivedCategoryCompIso F T
  have hnat : (F ⋙ T).mapDerivedCategory.map d =
      c.hom.app _ ≫ (F.mapDerivedCategory ⋙ T.mapDerivedCategory).map d ≫ c.inv.app _ := by
    rw [← c.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hP : c.hom.app (DerivedCategory.Q.obj P) = (F ⋙ T).mapDerivedCategoryFactors.hom.app P ≫
      T.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        T.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) := by
    rw [← cancel_mono (c.inv.app _), Iso.hom_inv_id_app, mapDerivedCategoryCompIso_inv_app_Q]
    simp only [Category.assoc, ← T.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  dsimp only [restrictQMap, Iso.app_inv, Iso.app_hom]
  rw [hnat, hP, mapDerivedCategoryCompIso_inv_app_Q F T I]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [Iso.inv_hom_id_app]
  have h1 := Category.comp_id
    (T.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) h1.symm)))

/-- `restrictQMap` is natural in the exact functor: along an isomorphism `γ : F ≅ F'` the two
restrictions of `d` differ by the components of `γ`. -/
lemma restrictQMap_iso {F' : C₁ ⥤ C₂} [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (γ : F ≅ F') {P I : CochainComplex C₁ ℤ}
    (d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (ComplexShape.up ℤ)).inv.app P) ≫
        restrictQMap F d ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (ComplexShape.up ℤ)).hom.app I) =
      restrictQMap F' d := by
  let m := mapDerivedCategoryIsoOfNatIso F F' γ
  have hnat : F'.mapDerivedCategory.map d =
      m.inv.app _ ≫ F.mapDerivedCategory.map d ≫ m.hom.app _ := by
    rw [m.hom.naturality, Iso.inv_hom_id_app_assoc]
  have hP : m.inv.app (DerivedCategory.Q.obj P) = F'.mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex γ (ComplexShape.up ℤ)).inv.app P) ≫
        F.mapDerivedCategoryFactors.inv.app P := by
    rw [← cancel_epi (m.hom.app _), Iso.hom_inv_id_app, mapDerivedCategoryIsoOfNatIso_hom_app_Q]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app]
    simp
  dsimp only [restrictQMap, Iso.app_inv, Iso.app_hom]
  rw [hnat, hP, mapDerivedCategoryIsoOfNatIso_hom_app_Q F F' γ I]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp

end Restrict

section Transport

variable {F : C₁ ⥤ C₂} {T : C₂ ⥤ C₃} {F' : C₁ ⥤ C₃} [F.Additive] [F'.Additive]
  [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- The exact functor `T` on a morphism `Q(F P) ⟶ Q(F I)`, read through `γ : F ⋙ T ≅ F'` as a
morphism `Q(F' P) ⟶ Q(F' I)`. -/
def transportQMap (γ : F ⋙ T ≅ F') {P I : CochainComplex C₁ ℤ}
    (β : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    DerivedCategory.Q.obj ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).inv.app P) ≫
    restrictQMap T β ≫
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).hom.app I)

omit [HasDerivedCategory C₁] in
/-- `transportQMap γ` preserves composition. -/
lemma transportQMap_comp (γ : F ⋙ T ≅ F') {P I J : CochainComplex C₁ ℤ}
    (β : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (β' : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :
    transportQMap γ (β ≫ β') = transportQMap γ β ≫ transportQMap γ β' := by
  simp only [transportQMap, restrictQMap_comp, Category.assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app]
  simp

omit [HasDerivedCategory C₁] in
/-- `transportQMap γ` is injective when `T.mapDerivedCategory` is faithful. -/
lemma transportQMap_injective [T.mapDerivedCategory.Faithful] (γ : F ⋙ T ≅ F')
    {P I : CochainComplex C₁ ℤ} : Function.Injective (transportQMap γ (P := P) (I := I)) := by
  intro β β' h
  apply restrictQMap_injective T
  have := congrArg (fun t =>
    DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).hom.app P) ≫ t ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).inv.app I)) h
  simp only [transportQMap, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    ← Functor.map_comp] at this
  simpa using this

omit [HasDerivedCategory C₁] in
/-- `transportQMap γ` is surjective when `T.mapDerivedCategory` is full. -/
lemma transportQMap_surjective [T.mapDerivedCategory.Full] (γ : F ⋙ T ≅ F')
    {P I : CochainComplex C₁ ℤ} : Function.Surjective (transportQMap γ (P := P) (I := I)) := by
  intro β'
  obtain ⟨β, hβ⟩ := restrictQMap_surjective T
    (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).hom.app P) ≫
      β' ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).inv.app I))
  refine ⟨β, ?_⟩
  simp only [transportQMap, hβ, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp

omit [HasDerivedCategory C₁] in
/-- Transport along `γ` whiskered by a functor `G` on the left, at complexes `P`, `I`, is
transport along `γ` at `G P`, `G I`. -/
lemma transportQMap_isoWhiskerLeft_obj {C₀ : Type*} [Category C₀] [Abelian C₀]
    [HasDerivedCategory.{w₄} C₀] (G : C₀ ⥤ C₁) [G.Additive] (γ : F ⋙ T ≅ F')
    {P I : CochainComplex C₀ ℤ}
    (β : DerivedCategory.Q.obj (((G ⋙ F).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj (((G ⋙ F).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    transportQMap (F := G ⋙ F) (F' := G ⋙ F')
        (Functor.isoWhiskerLeft G γ : (G ⋙ F) ⋙ T ≅ G ⋙ F') β =
      transportQMap γ (P := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (I := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) β := by
  rw [transportQMap, transportQMap]
  congr 2

/-- Transporting along the identity of `F ⋙ T` is restricting along `T`. -/
lemma transportQMap_refl {P I : CochainComplex C₁ ℤ}
    (β : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    transportQMap (Iso.refl (F ⋙ T)) β = restrictQMap T β := by
  have hP : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ T)) (ComplexShape.up ℤ)).inv.app
      P = 𝟙 _ := by
    ext n
    simp
  have hI : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ T)) (ComplexShape.up ℤ)).hom.app
      I = 𝟙 _ := by
    ext n
    simp
  rw [transportQMap, hP, hI]
  simp

/-- **Transporting a restriction gives the restriction.** For `γ : F ⋙ T ≅ F'`, the transport
along `γ` of the restriction of `d` along `F` is the restriction of `d` along `F'`. -/
lemma transportQMap_restrictQMap [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (γ : F ⋙ T ≅ F')
    {P I : CochainComplex C₁ ℤ} (d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I) :
    transportQMap γ (restrictQMap F d) = restrictQMap F' d := by
  rw [transportQMap, restrictQMap_comp_functor]
  exact restrictQMap_iso (F ⋙ T) γ d

omit [HasDerivedCategory C₁] in
/-- The transport depends on `T` only up to isomorphism: transporting along `θ` whiskered by `F`,
followed by `γ`, is transporting along `γ`. -/
lemma transportQMap_isoWhiskerLeft {T' : C₂ ⥤ C₃} [T'.Additive] [PreservesFiniteLimits T']
    [PreservesFiniteColimits T'] (θ : T' ≅ T) (γ : F ⋙ T ≅ F') {P I : CochainComplex C₁ ℤ}
    (β : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    transportQMap (Functor.isoWhiskerLeft F θ ≪≫ γ) β = transportQMap γ β := by
  rw [transportQMap, transportQMap, ← restrictQMap_iso T' θ β]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp]
  congr 2

omit [HasDerivedCategory C₁] in
/-- **Two successive transports are one transport along the composite.** -/
lemma transportQMap_transportQMap {T' : C₃ ⥤ C₄} {F'' : C₁ ⥤ C₄} [F''.Additive] [T'.Additive]
    [PreservesFiniteLimits T'] [PreservesFiniteColimits T'] (γ : F ⋙ T ≅ F')
    (γ' : F' ⋙ T' ≅ F'') {P I : CochainComplex C₁ ℤ}
    (β : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    transportQMap γ' (transportQMap γ β) =
      transportQMap ((Functor.associator F T T').symm ≪≫ Functor.isoWhiskerRight γ T' ≪≫ γ') β := by
  rw [transportQMap, transportQMap, transportQMap, restrictQMap_comp, restrictQMap_comp,
    restrictQMap_Q_map, restrictQMap_Q_map, restrictQMap_comp_functor]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp]
  congr 3 <;> ext n <;> simp

/-- Restricting a transport along a further exact functor `H` is transporting along `T ⋙ H`. -/
lemma restrictQMap_transportQMap {C₄' : Type*} [Category C₄'] [Abelian C₄']
    [HasDerivedCategory.{w₄} C₄'] (H : C₃ ⥤ C₄') [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] (γ : F ⋙ T ≅ F') {P I : CochainComplex C₁ ℤ}
    (β : DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    restrictQMap H (transportQMap γ β) =
      transportQMap (T := T ⋙ H) ((Functor.associator F T H).symm ≪≫ Functor.isoWhiskerRight γ H)
        β := by
  rw [← transportQMap_refl (F := F') (T := H), transportQMap_transportQMap]
  congr 1
  ext X
  simp

omit [HasDerivedCategory C₁] in
/-- **Transport read through a functor isomorphic to the induced one.** If `L ≅ D(T)` and the
objects `X_P`, `Y_P` are identified with `Q(F P)`, `Q(F' P)` compatibly with an isomorphism
`σ_P : L X_P ≅ Y_P` (and likewise for `I`), then transporting a morphism read through `X_P`,
`X_I` along `γ` is applying `L` and reading the result through `Y_P`, `Y_I`. -/
lemma transportQMap_eq_of_iso (γ : F ⋙ T ≅ F') (L : DerivedCategory C₂ ⥤ DerivedCategory C₃)
    (ι : L ≅ T.mapDerivedCategory) {P I : CochainComplex C₁ ℤ} {XP XI : DerivedCategory C₂}
    {YP YI : DerivedCategory C₃}
    (ξP : XP ≅ DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (ξI : XI ≅ DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (ξ'P : YP ≅ DerivedCategory.Q.obj ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (ξ'I : YI ≅ DerivedCategory.Q.obj ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (σP : L.obj XP ≅ YP) (σI : L.obj XI ≅ YI)
    (hP : σP.hom ≫ ξ'P.hom = L.map ξP.hom ≫ ι.hom.app _ ≫
      T.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).hom.app P))
    (hI : σI.hom ≫ ξ'I.hom = L.map ξI.hom ≫ ι.hom.app _ ≫
      T.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).hom.app I))
    (β : XP ⟶ XI) :
    transportQMap γ (ξP.inv ≫ β ≫ ξI.hom) = ξ'P.inv ≫ (σP.inv ≫ L.map β ≫ σI.hom) ≫ ξ'I.hom := by
  have eP : σP ≪≫ ξ'P = L.mapIso ξP ≪≫ ι.app _ ≪≫
      T.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
        DerivedCategory.Q.mapIso
          ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).app P) := Iso.ext hP
  have eI : σI ≪≫ ξ'I = L.mapIso ξI ≪≫ ι.app _ ≪≫
      T.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≪≫
        DerivedCategory.Q.mapIso
          ((Functor.mapHomologicalComplexCompIso γ (ComplexShape.up ℤ)).app I) := Iso.ext hI
  rw [show ξ'P.inv ≫ (σP.inv ≫ L.map β ≫ σI.hom) ≫ ξ'I.hom =
      (σP ≪≫ ξ'P).inv ≫ L.map β ≫ (σI ≪≫ ξ'I).hom by simp, eP, eI]
  simp only [transportQMap, restrictQMap, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, Category.assoc]
  rw [← NatIso.naturality_1 ι (ξP.inv ≫ β ≫ ξI.hom)]
  simp only [Functor.map_comp, Category.assoc]

end Transport

/-- The factorization of the induced functor through `Q` is compatible with the transport along an
equality of exact functors. -/
lemma eqToHom_comp_mapDerivedCategoryFactors_hom_app {G G' : C₁ ⥤ C₂} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G'.Additive]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (h : G = G')
    (P : CochainComplex C₁ ℤ) :
    (eqToHom (by subst h; rfl) : G.mapDerivedCategory.obj (DerivedCategory.Q.obj P) ⟶
        G'.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        G'.mapDerivedCategoryFactors.hom.app P =
      G.mapDerivedCategoryFactors.hom.app P ≫ eqToHom (by subst h; rfl) := by
  subst h
  simp

end Stacks.DerivedCategoryComparisons

end
