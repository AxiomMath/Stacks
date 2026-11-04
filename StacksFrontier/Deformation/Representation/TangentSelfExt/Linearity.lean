module

public import StacksFrontier.Deformation.Representation.TangentSelfExt.TangentMap

/-!
# Linearity of the tangent map

The vector-space structure of the tangent space of a predeformation category, the
compatibility of `Deformation.tangentSelfExt` with scalar multiplication, and the linear
equivalence `Deformation.tangentSpaceEquivSelfExt` (Stacks 0DVT).
-/

@[expose] public noncomputable section

open CategoryTheory
open Deformation

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

universe u w m

namespace Deformation

attribute [local instance] coefficientOppositeModule

attribute [local instance] coefficientCentralScalar

-- The deformation category of a representation is spelled through
-- `deformationCategoryProjection` and `squareZeroExtensionRestriction`, and the module over the
-- monoid algebra through `Rep.toModuleMonoidAlgebra`, so the `Module` and `IsHomLift` instance
-- arguments of a goal about them are only found after unfolding those heads.
attribute [local implicit_reducible] Rep.equivalenceModuleMonoidAlgebra
  Rep.toModuleMonoidAlgebra deformationCategoryProjection representationProjection
  squareZeroExtensionRestriction

/-- Transport of a module structure along an equality of carrier types, as a linear
equivalence. -/
noncomputable def castModuleEquiv
    {R : Type*} {M N : Type m} [Semiring R] [AddCommGroup M] [Module R M] (h : M = N) :
    let d : Σ G : AddCommGroup N, @Module R N _ G.toAddCommMonoid :=
      h ▸ (⟨inferInstance, inferInstance⟩ :
        Σ G : AddCommGroup M, @Module R M _ G.toAddCommMonoid)
    letI := d.1
    letI := d.2
    M ≃ₗ[R] N := by
  subst N
  exact LinearEquiv.refl R M

/-- The identification of the tangent space of a predeformation category with the
carrier of its natural module structure. -/
noncomputable def associatedTangentSpaceLiftEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory (Deformation.ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hpre : Deformation.IsPredeformationCategory 𝓕.p)
    (hS2 : Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) :
    letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
    letI : Fact (Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
    ((Deformation.associatedTangentSpaceModuleStructureUnlifted 𝓕 hpre hS2).functor.obj
      (FGModuleCat.of k k)) ≃ₗ[k]
      Deformation.artinianTangentSpace Λ k
        (Deformation.isomorphismClasses 𝓕 hpre.cofibered) :=
  castModuleEquiv (Deformation.associatedTangentSpaceModuleStructure_carrierUnlifted 𝓕 hpre hS2)

/-- The transport of `castModuleEquiv` is the type cast. -/
theorem castModuleEquiv_apply
    {R : Type*} {M N : Type m} [Semiring R] [AddCommGroup M] [Module R M]
    (h : M = N) (x : M) : castModuleEquiv (R := R) h x = cast h x := by
  subst N
  rfl

/-- Transport along an equality of functors commutes with the action of the functors on
morphisms. -/
theorem functorMap_cast
    {C : Type*} [Category C] {F G : C ⥤ Type m} (h : F = G)
    {X Y : C} (f : X ⟶ Y) (z : F.obj X) :
    cast (congrArg (fun H : C ⥤ Type _ ↦ H.obj Y) h) (F.map f z) =
      G.map f (cast (congrArg (fun H : C ⥤ Type _ ↦ H.obj X) h) z) := by
  cases h
  rfl

/-- The action of the square-zero extension functor on the tangent space, read through the
identification with the module structure, is the action of the module structure. -/
private theorem associatedTangentSpace_map_cast
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory (Deformation.ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hpre : Deformation.IsPredeformationCategory 𝓕.p)
    (hS2 : Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) :
    letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
    letI : Fact (Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
    let L := Deformation.associatedTangentSpaceModuleStructureUnlifted 𝓕 hpre hS2
    ∀ (W : FGModuleCat k) (f : W ⟶ FGModuleCat.of k k) (z : L.functor.obj W),
      (show Deformation.artinianTangentSpace Λ k
          (Deformation.isomorphismClasses 𝓕 hpre.cofibered) from
        (Deformation.artinianSquareZeroExtensionFunctor Λ k ⋙
          Deformation.isomorphismClasses 𝓕 hpre.cofibered).map f
          (cast (congrArg (fun H : FGModuleCat k ⥤ Type _ ↦ H.obj W) L.forget_comp) z)) =
        associatedTangentSpaceLiftEquiv 𝓕 hpre hS2 ((L.functor.map f).hom z) := by
  intro L W f z
  exact (functorMap_cast L.forget_comp f z).symm.trans (castModuleEquiv_apply _ _).symm

/-- Scalar multiplication on the tangent space of a predeformation category is the action
of the corresponding map of square-zero extensions. -/
theorem associatedTangentSpace_smul_eq_map
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory (Deformation.ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hpre : Deformation.IsPredeformationCategory 𝓕.p)
    (hS2 : Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) :
    letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
    letI : Fact (Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
    ∀ (a : k) (t : Deformation.artinianTangentSpace Λ k
      (Deformation.isomorphismClasses 𝓕 hpre.cofibered)),
      a • t = (Deformation.isomorphismClasses 𝓕 hpre.cofibered).map
        ((Deformation.artinianSquareZeroExtensionFunctor Λ k).map
          (a • 𝟙 (FGModuleCat.of k k))) t := by
  let : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
  let : Fact (Deformation.SchlessingerConditionS2
    (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
  intro a t
  let L := Deformation.associatedTangentSpaceModuleStructureUnlifted 𝓕 hpre hS2
  let F := Deformation.tangentSpaceSetFunctor Λ k
    (Deformation.artinianLocalOver Λ k)
    (Deformation.squareZeroExtension_mem_artinianLocalOver Λ k)
    (Deformation.artinianLocalOverToArtinian Λ k ⋙
      Deformation.isomorphismClasses 𝓕 hpre.cofibered)
  let e := associatedTangentSpaceLiftEquiv 𝓕 hpre hS2
  obtain ⟨z, rfl⟩ := e.surjective t
  rw [← e.map_smul]
  have he (z) : e z = cast (congrArg (fun H : FGModuleCat k ⥤ Type _ ↦
      H.obj (FGModuleCat.of k k)) L.forget_comp) z :=
    castModuleEquiv_apply _ z
  have hm : (L.functor.map (a • 𝟙 (FGModuleCat.of k k))).hom z = a • z := by
    rw [Functor.map_smul, L.functor.map_id]
    rfl
  show e (a • z) = F.map (a • 𝟙 (FGModuleCat.of k k)) (e z)
  rw [he z, ← hm]
  exact (associatedTangentSpace_map_cast 𝓕 hpre hS2 _ _ z).symm

/-- The tangent space functor is additive in the map of finite-dimensional modules. -/
theorem associatedTangentSpace_map_add
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory (Deformation.ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hpre : Deformation.IsPredeformationCategory 𝓕.p)
    (hS2 : Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) :
    letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
    letI : Fact (Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
    let F := Deformation.artinianSquareZeroExtensionFunctor Λ k ⋙
      Deformation.isomorphismClasses 𝓕 hpre.cofibered
    ∀ (W : FGModuleCat k) (f g : W ⟶ FGModuleCat.of k k) (z : F.obj W),
      F.map (f + g) z =
        (show Deformation.artinianTangentSpace Λ k
          (Deformation.isomorphismClasses 𝓕 hpre.cofibered) from F.map f z) +
        (show Deformation.artinianTangentSpace Λ k
          (Deformation.isomorphismClasses 𝓕 hpre.cofibered) from F.map g z) := by
  let : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
  let : Fact (Deformation.SchlessingerConditionS2
    (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
  dsimp only
  intro W f g z
  let L := Deformation.associatedTangentSpaceModuleStructureUnlifted 𝓕 hpre hS2
  let e := associatedTangentSpaceLiftEquiv 𝓕 hpre hS2
  let hW := congrArg (fun H : FGModuleCat k ⥤ Type _ ↦ H.obj W) L.forget_comp
  obtain ⟨z, rfl⟩ := (Equiv.cast hW).surjective z
  have hmap (a : W ⟶ FGModuleCat.of k k) := associatedTangentSpace_map_cast 𝓕 hpre hS2 W a z
  calc
    _ = e ((L.functor.map (f + g)).hom z) := hmap (f + g)
    _ = e ((L.functor.map f).hom z + (L.functor.map g).hom z) := by
      rw [L.functor.map_add]
      rfl
    _ = e ((L.functor.map f).hom z) + e ((L.functor.map g).hom z) := e.map_add _ _
    _ = _ := congrArg₂ (· + ·) (hmap f).symm (hmap g).symm

/-- Two tangent vectors are the two projections of a single element over the rank-two
square-zero extension. -/
theorem associatedTangentSpace_joint
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory (Deformation.ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hpre : Deformation.IsPredeformationCategory 𝓕.p)
    (hS2 : Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) :
    letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
    letI : Fact (Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
    let F := Deformation.artinianSquareZeroExtensionFunctor Λ k ⋙
      Deformation.isomorphismClasses 𝓕 hpre.cofibered
    let W := FGModuleCat.of k (k × k)
    let p₁ : W ⟶ FGModuleCat.of k k := FGModuleCat.ofHom (LinearMap.fst k k k)
    let p₂ : W ⟶ FGModuleCat.of k k := FGModuleCat.ofHom (LinearMap.snd k k k)
    ∀ s t : Deformation.artinianTangentSpace Λ k
      (Deformation.isomorphismClasses 𝓕 hpre.cofibered),
      ∃ z : F.obj W, F.map p₁ z = s ∧ F.map p₂ z = t := by
  let : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
  let : Fact (Deformation.SchlessingerConditionS2
    (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
  let F := Deformation.artinianSquareZeroExtensionFunctor Λ k ⋙
    Deformation.isomorphismClasses 𝓕 hpre.cofibered
  let W := FGModuleCat.of k (k × k)
  let p₁ : W ⟶ FGModuleCat.of k k := FGModuleCat.ofHom (LinearMap.fst k k k)
  let p₂ : W ⟶ FGModuleCat.of k k := FGModuleCat.ofHom (LinearMap.snd k k k)
  let i₁ : FGModuleCat.of k k ⟶ W := FGModuleCat.ofHom (LinearMap.inl k k k)
  let i₂ : FGModuleCat.of k k ⟶ W := FGModuleCat.ofHom (LinearMap.inr k k k)
  let L := Deformation.associatedTangentSpaceModuleStructureUnlifted 𝓕 hpre hS2
  let e := associatedTangentSpaceLiftEquiv 𝓕 hpre hS2
  dsimp only
  intro s t
  let zL := (L.functor.map i₁).hom (e.symm s) +
    (L.functor.map i₂).hom (e.symm t)
  let hW := congrArg (fun H : FGModuleCat k ⥤ Type _ ↦ H.obj W) L.forget_comp
  have hproj (j : W ⟶ FGModuleCat.of k k) : (L.functor.map j).hom zL =
      (L.functor.map (i₁ ≫ j)).hom (e.symm s) + (L.functor.map (i₂ ≫ j)).hom (e.symm t) := by
    dsimp only [zL]
    rw [map_add, L.functor.map_comp, L.functor.map_comp]
    rfl
  refine ⟨cast hW zL, ?_, ?_⟩
  · refine (associatedTangentSpace_map_cast 𝓕 hpre hS2 _ _ zL).trans ?_
    rw [hproj, show i₁ ≫ p₁ = 𝟙 _ from rfl, show i₂ ≫ p₁ = 0 from rfl, L.functor.map_id,
      L.functor.map_zero]
    change e _ = _
    simp
  · refine (associatedTangentSpace_map_cast 𝓕 hpre hS2 _ _ zL).trans ?_
    rw [hproj, show i₁ ≫ p₂ = 0 from rfl, show i₂ ≫ p₂ = 𝟙 _ from rfl, L.functor.map_id,
      L.functor.map_zero]
    change e _ = _
    simp

/-- The element of `associatedTangentSpace_joint` also computes the sum of the two
tangent vectors, along the diagonal map. -/
theorem associatedTangentSpace_joint_sum
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory (Deformation.ArtinianLocalAlgCat.{u, w, w} Λ k))
    (hpre : Deformation.IsPredeformationCategory 𝓕.p)
    (hS2 : Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) :
    letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
    letI : Fact (Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
    let F := Deformation.artinianSquareZeroExtensionFunctor Λ k ⋙
      Deformation.isomorphismClasses 𝓕 hpre.cofibered
    let W := FGModuleCat.of k (k × k)
    let p₁ : W ⟶ FGModuleCat.of k k := FGModuleCat.ofHom (LinearMap.fst k k k)
    let p₂ : W ⟶ FGModuleCat.of k k := FGModuleCat.ofHom (LinearMap.snd k k k)
    ∀ s t : Deformation.artinianTangentSpace Λ k
      (Deformation.isomorphismClasses 𝓕 hpre.cofibered),
      ∃ z : F.obj W, F.map p₁ z = s ∧ F.map p₂ z = t ∧
        F.map (p₁ + p₂) z = s + t := by
  let : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
  let : Fact (Deformation.SchlessingerConditionS2
    (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
  dsimp only
  intro s t
  obtain ⟨z, hz₁, hz₂⟩ := associatedTangentSpace_joint 𝓕 hpre hS2 s t
  refine ⟨z, hz₁, hz₂, ?_⟩
  rw [associatedTangentSpace_map_add 𝓕 hpre hS2, hz₁, hz₂]

/-- A cofibered category supplies a pushforward of an object of one fibre along a
morphism of the base, as a morphism lying over it. -/
theorem exists_isHomLift_fiber_pushforward
    {C D : Type*} [Category C] [Category D] (p : C ⥤ D)
    (h : Deformation.IsCofiberedInGroupoids p)
    {A B : D} (f : A ⟶ B) (x : p.Fiber A) :
    ∃ (y : p.Fiber B) (b : x.1 ⟶ y.1), p.IsHomLift f b := by
  obtain ⟨y, b, hb⟩ := h.exists_lift f.op (Opposite.op x.1) (congrArg Opposite.op x.2)
  have hb' : p.IsHomLift f b.unop := by
    have hf := IsHomLift.fac p.op f.op b
    exact IsHomLift.of_fac p f b.unop x.2
      (congrArg Opposite.unop (IsHomLift.domain_eq p.op f.op b))
      (by simpa using congrArg Quiver.Hom.unop hf)
  exact ⟨⟨y.unop, IsHomLift.codomain_eq p f b.unop⟩, b.unop, hb'⟩

/-- A morphism of deformations lying over a map into the dual numbers acts on the coefficient
algebra through that map. -/
private theorem representationHom_base_apply_of_fiber
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) {A₀ : Deformation.ArtinianLocalAlgCat Λ k}
    {x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber A₀}
    {y : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))}
    (δ : A₀ ⟶ Deformation.augmentedDualNumbers)
    (b : x.1 ⟶ y.1) [(deformationCategoryProjection (Λ := Λ) V ρ₀).IsHomLift δ b]
    (r : A₀) (r' : Deformation.augmentedDualNumbers (Λ := Λ) (k := k)) (hd : δ.hom r = r') :
    let hxbase : x.1.left.base = A₀ := x.2
    let hybase : y.1.left.base = Deformation.augmentedDualNumbers := y.2
    b.left.base.hom (hxbase.symm ▸ r) = hybase.symm ▸ r' := by
  rcases x with ⟨⟨X, ⟨⟨⟩⟩, α⟩, hxbase⟩
  rcases y with ⟨⟨Y, ⟨⟨⟩⟩, β⟩, hybase⟩
  rcases X with @⟨A, U, hU, hmodU, hfinU, hprojU, ρU⟩
  rcases Y with @⟨B, W, hW, hmodW, hfinW, hprojW, ρW⟩
  change A = A₀ at hxbase
  change B = Deformation.augmentedDualNumbers at hybase
  cases hxbase
  cases hybase
  have he : b.left.base = δ := by
    simpa [deformationCategoryProjection, representationProjection] using
      (IsHomLift.fac (deformationCategoryProjection (Λ := Λ) V ρ₀) δ b).symm
  subst hd
  exact congrArg (fun q ↦ q.hom r) he

/-- A morphism of deformations over the dual numbers acts on the coefficient algebra by
the constant coordinate and a multiple of `ε`. -/
theorem representationHom_base_apply
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    {x y : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))}
    (δ : Deformation.augmentedDualNumbers (Λ := Λ) (k := k) ⟶
      Deformation.augmentedDualNumbers)
    (b : x.1 ⟶ y.1) [(deformationCategoryProjection (Λ := Λ) V ρ₀).IsHomLift δ b]
    (r : DualNumber k) :
    let hxbase : x.1.left.base = Deformation.augmentedDualNumbers := x.2
    let hybase : y.1.left.base = Deformation.augmentedDualNumbers := y.2
    b.left.base.hom (hxbase.symm ▸ r) = hybase.symm ▸ δ.hom r := by
  exact representationHom_base_apply_of_fiber V ρ₀ δ b r _ rfl

/-- A morphism out of a deformation over the rank-two square-zero extension acts on the
coefficient algebra by the constant coordinate and a combination of the two radicals. -/
theorem representationHom_pair_base_apply
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    {x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      ((Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
        (FGModuleCat.of k (k × k)))}
    {y : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))}
    (δ : (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
        (FGModuleCat.of k (k × k)) ⟶
      Deformation.augmentedDualNumbers)
    (b : x.1 ⟶ y.1) [(deformationCategoryProjection (Λ := Λ) V ρ₀).IsHomLift δ b]
    (r : TrivSqZeroExt k (k × k)) :
    let hxbase : x.1.left.base =
      (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
        (FGModuleCat.of k (k × k)) := x.2
    let hybase : y.1.left.base = Deformation.augmentedDualNumbers := y.2
    b.left.base.hom (hxbase.symm ▸ r) = hybase.symm ▸ δ.hom r := by
  exact representationHom_base_apply_of_fiber V ρ₀ δ b r _ rfl

/-- The square-zero extension functor sends a linear map to the map that is the identity
on constants and the given map on the square-zero part. -/
theorem pairSquareZeroMap_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (f : FGModuleCat.of k (k × k) ⟶ FGModuleCat.of k k)
    (r : TrivSqZeroExt k (k × k)) :
    ((Deformation.artinianSquareZeroExtensionFunctor Λ k).map f).hom r =
      (r.fst, f.hom r.snd) := by
  let : Module kᵐᵒᵖ
      ↑((forget₂ (FGModuleCat k) (ModuleCat k)).obj (FGModuleCat.of k (k × k))) :=
    Module.compHom _ {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }
  let : Module kᵐᵒᵖ
      ↑((forget₂ (FGModuleCat k) (ModuleCat k)).obj (FGModuleCat.of k k)) :=
    Module.compHom _ {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  let : IsCentralScalar k
      ↑((forget₂ (FGModuleCat k) (ModuleCat k)).obj (FGModuleCat.of k (k × k))) :=
    ⟨fun _ _ ↦ rfl⟩
  let : IsCentralScalar k
      ↑((forget₂ (FGModuleCat k) (ModuleCat k)).obj (FGModuleCat.of k k)) :=
    ⟨fun _ _ ↦ rfl⟩
  apply TrivSqZeroExt.ext
  · show (TrivSqZeroExt.map (ModuleCat.Hom.hom
        ((forget₂ (FGModuleCat k) (ModuleCat k)).map f)) r).fst = r.fst
    exact TrivSqZeroExt.fst_map _ _
  · show (TrivSqZeroExt.map (ModuleCat.Hom.hom
        ((forget₂ (FGModuleCat k) (ModuleCat k)).map f)) r).snd = f.hom r.snd
    exact TrivSqZeroExt.snd_map _ _

/-- Transport along an equality of objects of the base category is multiplicative. -/
theorem artinianLocalAlgCat_transport_mul
    {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : Deformation.ArtinianLocalAlgCat Λ k} (h : A = B) (r s : B) :
    (h.symm ▸ (r * s)) = (h.symm ▸ r) * (h.symm ▸ s) := by
  cases h
  rfl

/-- For a morphism of deformations lying over the collapse of the two coordinate radicals,
the associated pair and self extensions are compared by a morphism of short complexes
that is the identity on the quotient. -/
theorem associatedPairExtension_shortComplexHom_of_lift
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    {x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      ((Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
        (FGModuleCat.of k (k × k)))}
    {y : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))}
    (ψ : FGModuleCat.of k (k × k) ⟶ FGModuleCat.of k k)
    (a c : k) (hψ₁ : ψ.hom (1, 0) = a) (hψ₂ : ψ.hom (0, 1) = c)
    (b : x.1 ⟶ y.1)
    [(deformationCategoryProjection (Λ := Λ) V ρ₀).IsHomLift
      ((Deformation.artinianSquareZeroExtensionFunctor Λ k).map ψ) b]
    {M M' : ModuleCat (MonoidAlgebra k Γ)}
    {f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of (ρ₀.prod ρ₀)) ⟶ M}
    {g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    {f' : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M'}
    {g' : M' ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    {hfg : f ≫ g = 0} {hfg' : f' ≫ g' = 0}
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (hx : IsAssociatedPairExtension V ρ₀ x M f g)
    (hy : IsAssociatedSelfExtension V ρ₀ y M' f' g') :
    ∃ q : ShortComplex.mk f g hfg ⟶ ShortComplex.mk f' g' hfg',
      q.τ₁ = (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.map
        (pairCoefficientHom ρ₀ a c) ∧ q.τ₃ = 𝟙 _ := by
  let δ := (Deformation.artinianSquareZeroExtensionFunctor Λ k).map ψ
  have hinr (v : k × k) : δ.hom (TrivSqZeroExt.inr v : TrivSqZeroExt k (k × k)) =
      (TrivSqZeroExt.inl (ψ.hom v) : DualNumber k) * DualNumber.eps := by
    rw [pairSquareZeroMap_apply]
    simp only [TrivSqZeroExt.snd_inr]
    apply TrivSqZeroExt.ext
    · show (0 : k) = ψ.hom v * 0
      simp
    · show ψ.hom v = ψ.hom v * 1 + 0 * 0
      simp
  apply associatedPairExtension_shortComplexHom V ρ₀ a c b
  · dsimp only
    intro d
    exact representationHom_base_apply_of_fiber V ρ₀ δ b (TrivSqZeroExt.inl d) _
      (by rw [pairSquareZeroMap_apply]; apply TrivSqZeroExt.ext <;> simp)
  · exact (representationHom_base_apply_of_fiber V ρ₀ δ b (TrivSqZeroExt.inr (1, 0)) _
      (by rw [hinr, hψ₁]; rfl)).trans (artinianLocalAlgCat_transport_mul y.2 _ _)
  · exact (representationHom_base_apply_of_fiber V ρ₀ δ b (TrivSqZeroExt.inr (0, 1)) _
      (by rw [hinr, hψ₂]; rfl)).trans (artinianLocalAlgCat_transport_mul y.2 _ _)
  · exact h
  · exact hx
  · exact hy

/-- The map `tangentSelfExt` is compatible with scalar multiplication on the tangent space. -/
theorem tangentSelfExt_map_smul
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (hpre : Deformation.IsPredeformationCategory
      (deformationCategoryProjection (Λ := Λ) V ρ₀))
    (hS2 : Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses
        (BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀))
        hpre.cofibered))) :
    let 𝓕 := BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)
    letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
    letI : Fact (Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
    ∀ (a : k) (t : Deformation.artinianTangentSpace Λ k
      (Deformation.isomorphismClasses 𝓕 hpre.cofibered)),
      tangentSelfExt V ρ₀ hpre.cofibered (a • t) =
        a • tangentSelfExt V ρ₀ hpre.cofibered t := by
  let p := deformationCategoryProjection (Λ := Λ) V ρ₀
  let 𝓕 := BasedCategory.ofFunctor p
  let : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
  let : Fact (Deformation.SchlessingerConditionS2
    (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
  dsimp only
  intro a t
  obtain ⟨x, rfl⟩ := Deformation.classOf_surjective 𝓕 hpre.cofibered _ t
  let δ := (Deformation.artinianSquareZeroExtensionFunctor Λ k).map
    (a • 𝟙 (FGModuleCat.of k k))
  obtain ⟨y, b, hb⟩ := exists_isHomLift_fiber_pushforward p hpre.cofibered δ x
  have : 𝓕.p.IsHomLift δ b := hb
  have : (deformationCategoryProjection (Λ := Λ) V ρ₀).IsHomLift δ b := hb
  rw [associatedTangentSpace_smul_eq_map 𝓕 hpre hS2,
    Deformation.map_classOf 𝓕 hpre.cofibered δ x y b]
  obtain ⟨M, f, g, hfg, hexact, hx⟩ := exists_associatedSelfExtension V ρ₀ x
  obtain ⟨M', f', g', hfg', hexact', hy⟩ := exists_associatedSelfExtension V ρ₀ y
  rw [tangentSelfExt_classOf V ρ₀ hpre.cofibered x M f g hfg hexact hx,
    tangentSelfExt_classOf V ρ₀ hpre.cofibered y M' f' g' hfg' hexact' hy]
  apply associatedSelfExtension_extClass_smul_of_hom V ρ₀ a b _ _ hexact hexact' hx hy
  · dsimp only
    intro c
    exact representationHom_base_apply_of_fiber V ρ₀ δ b (TrivSqZeroExt.inl c) _ (by
      show (TrivSqZeroExt.map (a • (LinearMap.id : k →ₗ[k] k))
          (TrivSqZeroExt.inl c) : DualNumber k) = TrivSqZeroExt.inl c
      simp)
  · have hd : δ.hom DualNumber.eps = (TrivSqZeroExt.inl a : DualNumber k) *
        DualNumber.eps := by
      show (TrivSqZeroExt.map (a • (LinearMap.id : k →ₗ[k] k))
          DualNumber.eps : DualNumber k) = TrivSqZeroExt.inl a * DualNumber.eps
      rw [DualNumber.eps, TrivSqZeroExt.map_inr, TrivSqZeroExt.inl_mul_inr,
        LinearMap.smul_apply, LinearMap.id_apply]
    exact (representationHom_base_apply_of_fiber V ρ₀ δ b DualNumber.eps _ hd).trans
      (artinianLocalAlgCat_transport_mul y.2 _ _)

/-- The canonical tangent space of a finite-dimensional representation deformation category
is linearly equivalent to its first self-Ext over the group algebra. -/
@[stacks 0DVT "clause 1: `T Def_{V,ρ₀} = Ext¹_{k[Γ]}(V, V)`, the tangent space of the \
deformation category of a finite-dimensional representation `ρ₀` is its first self-extension \
group over the group algebra. The identification of that `Ext¹` with `H¹(Γ, End_k(V))` is \
clause 2, `Deformation.selfExtEquivGroupCohomologyOne`"]
public noncomputable def tangentSpaceEquivSelfExt
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) :
    let p := deformationCategoryProjection (Λ := Λ) V ρ₀
    let 𝓕 := BasedCategory.ofFunctor p
    let M₀ := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)
    let E := Abelian.Ext M₀ M₀ 1
    Σ' (hpre : Deformation.IsPredeformationCategory 𝓕.p)
      (hS2 : Deformation.SchlessingerConditionS2
        (CategoryOfElements.π
          (Deformation.isomorphismClasses 𝓕 hpre.cofibered))),
      letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
      letI : Fact (Deformation.SchlessingerConditionS2
        (CategoryOfElements.π
          (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
      letI : AddCommGroup
        (Deformation.artinianTangentSpace Λ k
          (Deformation.isomorphismClasses 𝓕 hpre.cofibered)) :=
        Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
      letI : Module k
        (Deformation.artinianTangentSpace Λ k
          (Deformation.isomorphismClasses 𝓕 hpre.cofibered)) :=
        Deformation.associatedTangentSpaceModuleUnlifted 𝓕
      { L : Deformation.artinianTangentSpace Λ k
          (Deformation.isomorphismClasses 𝓕 hpre.cofibered) ≃ₗ[k] E //
        (∀ x : p.Fiber (Deformation.augmentedDualNumbers (Λ := Λ) (k := k)),
          ∃ (M : ModuleCat (MonoidAlgebra k Γ)) (f : M₀ ⟶ M) (g : M ⟶ M₀)
            (hfg : f ≫ g = 0),
            (ShortComplex.mk f g hfg).ShortExact ∧
              IsAssociatedSelfExtension V ρ₀ x M f g) ∧
        (∀ (x : p.Fiber (Deformation.augmentedDualNumbers (Λ := Λ) (k := k)))
          (M : ModuleCat (MonoidAlgebra k Γ)) (f : M₀ ⟶ M) (g : M ⟶ M₀)
          (hfg : f ≫ g = 0) (hexact : (ShortComplex.mk f g hfg).ShortExact),
          IsAssociatedSelfExtension V ρ₀ x M f g →
            L (Deformation.classOf 𝓕 hpre.cofibered x) = hexact.extClass) } := by
  let p := deformationCategoryProjection (Λ := Λ) V ρ₀
  let 𝓕 := BasedCategory.ofFunctor p
  let hDef := Deformation.isDeformationCategory_deformationCategoryProjection (Λ := Λ) V ρ₀
  let hpre : Deformation.IsPredeformationCategory p := by
    simpa [p, deformationCategoryProjection,
      Deformation.RepresentationCategory.deformationCategory,
      Deformation.objectsOverFunctor,
      Deformation.RepresentationCategory.deformationCategory,
      Deformation.RepresentationCategory.specialFiber,
      Deformation.deformationCategoryProjection,
      Deformation.representationProjection,
      Deformation.representationProjection] using hDef.predeformation
  let hRS : Deformation.SatisfiesRS p := by
    simpa [p, deformationCategoryProjection,
      Deformation.RepresentationCategory.deformationCategory,
      Deformation.objectsOverFunctor,
      Deformation.RepresentationCategory.deformationCategory,
      Deformation.RepresentationCategory.specialFiber,
      Deformation.deformationCategoryProjection,
      Deformation.representationProjection,
      Deformation.representationProjection] using hDef.satisfiesRS
  let hS2base : Deformation.SchlessingerConditionS2 p :=
    Deformation.schlessingerConditionS2_of_satisfiesRS hRS
  let hS2 : Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered)) :=
    Deformation.schlessingerConditionS2_of_isIsomorphismClasses
      𝓕 hpre.cofibered hS2base (Or.inl hpre)
  refine ⟨hpre, hS2, ?_⟩
  letI : Fact (Deformation.IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
  letI : Fact (Deformation.SchlessingerConditionS2
      (CategoryOfElements.π (Deformation.isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
  letI : AddCommGroup
      (Deformation.artinianTangentSpace Λ k (Deformation.isomorphismClasses 𝓕 hpre.cofibered)) :=
    Deformation.associatedTangentSpaceAddCommGroupUnlifted 𝓕
  letI : Module k
      (Deformation.artinianTangentSpace Λ k (Deformation.isomorphismClasses 𝓕 hpre.cofibered)) :=
    Deformation.associatedTangentSpaceModuleUnlifted 𝓕
  let φ := tangentSelfExt V ρ₀ hpre.cofibered
  have hadd : ∀ s t, φ (s + t) = φ s + φ t := by
    intro s t
    let W := FGModuleCat.of k (k × k)
    let p₁ : W ⟶ FGModuleCat.of k k := FGModuleCat.ofHom (LinearMap.fst k k k)
    let p₂ : W ⟶ FGModuleCat.of k k := FGModuleCat.ofHom (LinearMap.snd k k k)
    let F := Deformation.artinianSquareZeroExtensionFunctor Λ k ⋙
      Deformation.isomorphismClasses 𝓕 hpre.cofibered
    let i₁ : FGModuleCat.of k k ⟶ W := FGModuleCat.ofHom (LinearMap.inl k k k)
    let i₂ : FGModuleCat.of k k ⟶ W := FGModuleCat.ofHom (LinearMap.inr k k k)
    let L := Deformation.associatedTangentSpaceModuleStructureUnlifted 𝓕 hpre hS2
    let e := associatedTangentSpaceLiftEquiv 𝓕 hpre hS2
    let zL := (L.functor.map i₁).hom (e.symm s) +
      (L.functor.map i₂).hom (e.symm t)
    let hW := congrArg (fun H : FGModuleCat k ⥤ Type _ ↦ H.obj W) L.forget_comp
    let z : F.obj W := cast hW zL
    have he (v) : e v = cast (congrArg (fun H : FGModuleCat k ⥤ Type _ ↦
        H.obj (FGModuleCat.of k k)) L.forget_comp) v :=
      castModuleEquiv_apply _ v
    have hz₁ : F.map p₁ z = s := by
      have h₁ : i₁ ≫ p₁ = 𝟙 _ := rfl
      have h₂ : i₂ ≫ p₁ = 0 := rfl
      have ha : (L.functor.map p₁).hom zL = e.symm s := by
        dsimp only [zL]
        rw [map_add]
        change ((L.functor.map i₁ ≫ L.functor.map p₁).hom) (e.symm s) +
          ((L.functor.map i₂ ≫ L.functor.map p₁).hom) (e.symm t) = _
        rw [← L.functor.map_comp, ← L.functor.map_comp, h₁, h₂,
          L.functor.map_id, L.functor.map_zero]
        simp
      exact (functorMap_cast L.forget_comp p₁ zL).symm.trans
        ((he _).symm.trans ((congrArg e ha).trans (e.apply_symm_apply s)))
    have hz₂ : F.map p₂ z = t := by
      have h₁ : i₁ ≫ p₂ = 0 := rfl
      have h₂ : i₂ ≫ p₂ = 𝟙 _ := rfl
      have ha : (L.functor.map p₂).hom zL = e.symm t := by
        dsimp only [zL]
        rw [map_add]
        change ((L.functor.map i₁ ≫ L.functor.map p₂).hom) (e.symm s) +
          ((L.functor.map i₂ ≫ L.functor.map p₂).hom) (e.symm t) = _
        rw [← L.functor.map_comp, ← L.functor.map_comp, h₁, h₂,
          L.functor.map_zero, L.functor.map_id]
        simp
      exact (functorMap_cast L.forget_comp p₂ zL).symm.trans
        ((he _).symm.trans ((congrArg e ha).trans (e.apply_symm_apply t)))
    have hz₃ : F.map (p₁ + p₂) z = s + t := by
      have hmap : (L.functor.map (p₁ + p₂)).hom zL =
          (L.functor.map p₁).hom zL + (L.functor.map p₂).hom zL := by
        rw [L.functor.map_add]
        rfl
      have hcast : F.map (p₁ + p₂) z =
          e ((L.functor.map (p₁ + p₂)).hom zL) :=
        (functorMap_cast L.forget_comp (p₁ + p₂) zL).symm.trans (he _).symm
      rw [hmap, e.map_add] at hcast
      exact hcast.trans (congrArg₂ (· + ·)
        ((he _).trans ((functorMap_cast L.forget_comp p₁ zL).trans hz₁))
        ((he _).trans ((functorMap_cast L.forget_comp p₂ zL).trans hz₂)))
    obtain ⟨z, hz₁, hz₂, hz₃⟩ : ∃ z : F.obj W,
        F.map p₁ z = s ∧ F.map p₂ z = t ∧ F.map (p₁ + p₂) z = s + t :=
      ⟨z, hz₁, hz₂, hz₃⟩
    obtain ⟨x, rfl⟩ := Deformation.classOf_surjective 𝓕 hpre.cofibered _ z
    let δ₁ := (Deformation.artinianSquareZeroExtensionFunctor Λ k).map p₁
    let δ₂ := (Deformation.artinianSquareZeroExtensionFunctor Λ k).map p₂
    let δ₃ := (Deformation.artinianSquareZeroExtensionFunctor Λ k).map (p₁ + p₂)
    obtain ⟨y₁, b₁, hb₁⟩ := exists_isHomLift_fiber_pushforward p hpre.cofibered δ₁ x
    obtain ⟨y₂, b₂, hb₂⟩ := exists_isHomLift_fiber_pushforward p hpre.cofibered δ₂ x
    obtain ⟨y₃, b₃, hb₃⟩ := exists_isHomLift_fiber_pushforward p hpre.cofibered δ₃ x
    have : 𝓕.p.IsHomLift δ₁ b₁ := hb₁
    have : 𝓕.p.IsHomLift δ₂ b₂ := hb₂
    have : 𝓕.p.IsHomLift δ₃ b₃ := hb₃
    have : p.IsHomLift δ₁ b₁ := hb₁
    have : p.IsHomLift δ₂ b₂ := hb₂
    have : p.IsHomLift δ₃ b₃ := hb₃
    have hy₁ : Deformation.classOf 𝓕 hpre.cofibered y₁ = s :=
      (Deformation.map_classOf 𝓕 hpre.cofibered δ₁ x y₁ b₁).symm.trans hz₁
    have hy₂ : Deformation.classOf 𝓕 hpre.cofibered y₂ = t :=
      (Deformation.map_classOf 𝓕 hpre.cofibered δ₂ x y₂ b₂).symm.trans hz₂
    have hy₃ : Deformation.classOf 𝓕 hpre.cofibered y₃ = s + t :=
      (Deformation.map_classOf 𝓕 hpre.cofibered δ₃ x y₃ b₃).symm.trans hz₃
    obtain ⟨M, f, g, hfg, hexact, hx⟩ := exists_associatedPairExtension V ρ₀ x
    obtain ⟨M₁, f₁, g₁, hfg₁, hexact₁, h₁⟩ := exists_associatedSelfExtension V ρ₀ y₁
    obtain ⟨M₂, f₂, g₂, hfg₂, hexact₂, h₂⟩ := exists_associatedSelfExtension V ρ₀ y₂
    obtain ⟨M₃, f₃, g₃, hfg₃, hexact₃, h₃⟩ := exists_associatedSelfExtension V ρ₀ y₃
    obtain ⟨q₁, hq₁, hq₁'⟩ :=
      associatedPairExtension_shortComplexHom_of_lift V ρ₀ p₁ 1 0
        (by rfl) (by rfl) b₁ hexact hx h₁
    obtain ⟨q₂, hq₂, hq₂'⟩ :=
      associatedPairExtension_shortComplexHom_of_lift V ρ₀ p₂ 0 1
        (by rfl) (by rfl) b₂ hexact hx h₂
    obtain ⟨q₃, hq₃, hq₃'⟩ :=
      associatedPairExtension_shortComplexHom_of_lift V ρ₀ (p₁ + p₂) 1 1
        (by change (LinearMap.fst k k k + LinearMap.snd k k k) (1, 0) = 1
            simp)
        (by change (LinearMap.fst k k k + LinearMap.snd k k k) (0, 1) = 1
            simp) b₃ hexact hx h₃
    have hq : q₃.τ₁ = q₁.τ₁ + q₂.τ₁ := by
      rw [hq₁, hq₂, hq₃]
      ext v
      change (pairCoefficientHom ρ₀ 1 1).hom v =
        (pairCoefficientHom ρ₀ 1 0).hom v +
          (pairCoefficientHom ρ₀ 0 1).hom v
      rw [pairCoefficientHom_add]
      simp only [Rep.add_hom]
      rfl
    have hext : hexact₃.extClass = hexact₁.extClass + hexact₂.extClass :=
      extClass_eq_add_of_common_extension _ hexact f₁ g₁ hfg₁ f₂ g₂ hfg₂
        f₃ g₃ hfg₃ hexact₁ hexact₂ hexact₃ q₁ q₂ q₃ hq₁' hq₂' hq₃' hq
    rw [← hy₃, ← hy₁, ← hy₂]
    exact (tangentSelfExt_classOf V ρ₀ hpre.cofibered y₃ M₃ f₃ g₃ hfg₃ hexact₃ h₃).trans
      (hext.trans (congrArg₂ (· + ·)
        (tangentSelfExt_classOf V ρ₀ hpre.cofibered y₁ M₁ f₁ g₁ hfg₁ hexact₁ h₁).symm
        (tangentSelfExt_classOf V ρ₀ hpre.cofibered y₂ M₂ f₂ g₂ hfg₂ hexact₂ h₂).symm))
  have hsmul : ∀ (a : k) t, φ (a • t) = a • φ t :=
    tangentSelfExt_map_smul V ρ₀ hpre hS2
  let l : _ →ₗ[k] _ := {
    toFun := φ
    map_add' := hadd
    map_smul' := hsmul }
  refine ⟨LinearEquiv.ofBijective l
    ⟨tangentSelfExt_injective V ρ₀ hpre.cofibered,
      tangentSelfExt_surjective V ρ₀ hpre.cofibered⟩, ?_, ?_⟩
  · exact exists_associatedSelfExtension V ρ₀
  · intro x M f g hfg hexact hx
    exact tangentSelfExt_classOf V ρ₀ hpre.cofibered x M f g hfg hexact hx

end Deformation
