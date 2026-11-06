module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.LiftsOfObjects.Action.Functoriality
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.SmallExtensionLift
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms

/-!
# A smooth morphism of deformation functors with bijective differential is an isomorphism

A morphism `φ : F ⟶ G` of deformation functors on `𝒞_Λ` which is smooth, in the sense that the
induced morphism of categories of elements is smooth, is an isomorphism as soon as its
component at the augmented dual numbers is bijective.

## Main results

* `Deformation.isIso_of_isSmooth_of_tangent_bijective`: the isomorphism criterion.

## Implementation notes

Bijectivity of `φ` is proved at every object `A` by factoring the canonical morphism
`A ⟶ k` into small extensions (Tag 06GE) and inducting down the chain from the residue field,
where both functors are singletons. Along one small extension, surjectivity is smoothness
(Tag 06HJ) and injectivity is the free transitive action of Tag 06JI: classes of lifts of a
fixed element form a torsor under `T ⊗_k ker f`, the map on classes of lifts intertwines the
two actions by the differential tensored with the identity (Tag 06JJ), and a bijective
differential therefore makes that map injective.

The differential of the induced morphism of categories of elements is bijective exactly when
the component at the augmented dual numbers is, because a fibre of a category of elements is
the value of the functor and two elements of a fibre are isomorphic only through the identity
of the base. Both halves of that are `elementsFiberEquiv` and `classOf_injective_elements`
below.

## References

* [Stacks Project, Tag 06JL](https://stacks.math.columbia.edu/tag/06JL)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory
universe u w t vF uF vG uG

/-! ### Fibres of a category of elements -/

/-- The fibre of a category of elements over `A` is the value of the functor at `A`. -/
private def elementsFiberEquiv {C : Type u} [Category.{w, u} C]
    (F : C ⥤ Type t) (A : C) :
    Functor.Fiber (CategoryOfElements.π F) A ≃ F.obj A where
  toFun x := by
    rcases x with ⟨@⟨B, b⟩, h⟩
    cases h
    exact b
  invFun x := ⟨F.elementsMk A x, rfl⟩
  left_inv x := by
    rcases x with ⟨@⟨B, b⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl

/-- A morphism of elements lying over the identity of `A` identifies its source and target. -/
private theorem eq_of_isHomLift_id {C : Type u} [Category.{w, u} C] {F : C ⥤ Type t} {A : C}
    {x y : F.obj A} (g : F.elementsMk A x ⟶ F.elementsMk A y)
    (hg : (CategoryOfElements.π F).IsHomLift (𝟙 A) g) : x = y := by
  have hfac : 𝟙 A = 𝟙 A ≫ g.hom ≫ 𝟙 A := IsHomLift.fac (p := CategoryOfElements.π F) (𝟙 A) g
  have hval : g.hom = 𝟙 A := by simpa using hfac.symm
  simpa [hval] using g.map_val

/-- In a category of elements the class map is injective: an isomorphism of two objects of
one fibre lies over the identity, so the two elements coincide. -/
private theorem classOf_injective_elements
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ Type t}
    (hcof : IsCofiberedInGroupoids (CategoryOfElements.π F))
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k) :
    Function.Injective
      (classOf (BasedCategory.ofFunctor (CategoryOfElements.π F)) hcof (A := A)) := by
  intro x y h
  rcases x with ⟨@⟨A₁, x⟩, hx⟩
  rcases y with ⟨@⟨A₂, y⟩, hy⟩
  change A₁ = A at hx
  change A₂ = A at hy
  cases hx
  cases hy
  apply Subtype.ext
  have hq := congrArg (fun z => cast
    (isomorphismClasses_obj
      (BasedCategory.ofFunctor (CategoryOfElements.π F)) hcof A) z) h
  have hqx := classOf_eq
    (BasedCategory.ofFunctor (CategoryOfElements.π F)) hcof (A := A) ⟨F.elementsMk A x, rfl⟩
  have hqy := classOf_eq
    (BasedCategory.ofFunctor (CategoryOfElements.π F)) hcof (A := A) ⟨F.elementsMk A y, rfl⟩
  rw [hqx, hqy] at hq
  obtain ⟨i⟩ := Quotient.exact hq
  show F.elementsMk A x = F.elementsMk A y
  rw [eq_of_isHomLift_id i.hom.1 i.hom.2]

/-! ### Propagating bijectivity along a small extension -/

/-- Smoothness propagates surjectivity of a component down a surjection of the base. -/
private theorem app_surjective_of_smooth_of_app_surjective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F G : ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ Type t}
    (φ : F ⟶ G)
    (hφ : IsSmooth (elementsBasedFunctor φ))
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hbase : Function.Surjective (φ.app A)) :
    Function.Surjective (φ.app A') := by
  have hsmooth := (isSmooth_elementsBasedFunctor_iff φ).mp hφ
  intro y
  obtain ⟨x, hx⟩ := hbase (G.map f y)
  obtain ⟨x', -, hxy⟩ := hsmooth f hf x y hx
  exact ⟨x', hxy⟩

/-- Bijectivity at the augmented dual numbers is bijectivity of the differential. -/
private theorem differential_bijective_of_app_bijective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F G : ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ Type t}
    (hF : IsDeformationFunctor F)
    (hG : IsDeformationFunctor G)
    (φ : F ⟶ G)
    (happ : Function.Bijective
      (φ.app (augmentedDualNumbers (Λ := Λ) (k := k)))) :
    Function.Bijective
      (differential
        ((isDeformationCategory_iff F).2 hF).predeformation.cofibered
        ((isDeformationCategory_iff G).2 hG).predeformation.cofibered
        (elementsBasedFunctor φ)) := by
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  let hFCat := (isDeformationCategory_iff F).2 hF
  let hGCat := (isDeformationCategory_iff G).2 hG
  let 𝓕 := BasedCategory.ofFunctor (CategoryOfElements.π F)
  let 𝓖 := BasedCategory.ofFunctor (CategoryOfElements.π G)
  let h𝓕 : IsCofiberedInGroupoids
      (BasedCategory.ofFunctor (CategoryOfElements.π F)).p := hFCat.predeformation.cofibered
  let h𝓖 : IsCofiberedInGroupoids
      (BasedCategory.ofFunctor (CategoryOfElements.π G)).p := hGCat.predeformation.cofibered
  have hGclass := classOf_injective_elements h𝓖 A
  have hcomm (z : 𝓕.p.Fiber A) :
      φ.app A (elementsFiberEquiv F A z) =
        elementsFiberEquiv G A ((fiberFunctor (elementsBasedFunctor φ) A).obj z) := by
    rcases z with ⟨@⟨B, z⟩, hz⟩
    change B = A at hz
    cases hz
    rfl
  have hFiberMap : Function.Injective
      ((fiberFunctor (elementsBasedFunctor φ) A).obj) := by
    intro x y hxy
    apply (elementsFiberEquiv F A).injective
    apply happ.1
    rw [hcomm x, hcomm y, hxy]
  constructor
  · intro z₁ z₂ h
    obtain ⟨x₁, rfl⟩ := classOf_surjective 𝓕 h𝓕 A z₁
    obtain ⟨x₂, rfl⟩ := classOf_surjective 𝓕 h𝓕 A z₂
    have h' :
        mapIsomorphismClasses h𝓕 h𝓖 (elementsBasedFunctor φ) A (classOf 𝓕 h𝓕 x₁) =
        mapIsomorphismClasses h𝓕 h𝓖 (elementsBasedFunctor φ) A (classOf 𝓕 h𝓕 x₂) := h
    rw [mapIsomorphismClasses_classOf h𝓕 h𝓖 (elementsBasedFunctor φ) x₁,
      mapIsomorphismClasses_classOf h𝓕 h𝓖 (elementsBasedFunctor φ) x₂] at h'
    exact congrArg (classOf 𝓕 h𝓕) (hFiberMap (hGclass h'))
  · intro z
    obtain ⟨y, rfl⟩ := classOf_surjective 𝓖 h𝓖 A z
    obtain ⟨xv, hxv⟩ := happ.2 (elementsFiberEquiv G A y)
    let x := (elementsFiberEquiv F A).symm xv
    have himage : (fiberFunctor (elementsBasedFunctor φ) A).obj x = y := by
      apply (elementsFiberEquiv G A).injective
      rw [← hcomm x]
      simpa [x] using hxv
    refine ⟨classOf 𝓕 h𝓕 x, ?_⟩
    show mapIsomorphismClasses h𝓕 h𝓖 (elementsBasedFunctor φ) A (classOf 𝓕 h𝓕 x) =
        classOf 𝓖 h𝓖 y
    rw [mapIsomorphismClasses_classOf h𝓕 h𝓖 (elementsBasedFunctor φ) x]
    exact congrArg (classOf 𝓖 h𝓖) himage

/-- A bijective differential makes the map on classes of lifts injective: both sides are
torsors under the tangent space tensored with the kernel, and the map intertwines the two
actions by the differential tensored with the identity. -/
private theorem mapLiftClasses_injective_of_differential_bijective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓕 : BasedCategory.{vF, uF} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓖 : BasedCategory.{vG, uG} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (h𝓕 : IsDeformationCategory 𝓕.p)
    (h𝓖 : IsDeformationCategory 𝓖.p)
    (φ : BasedFunctor 𝓕 𝓖)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (x : 𝓕.p.Fiber A)
    (hd : Function.Bijective
      (differential h𝓕.predeformation.cofibered h𝓖.predeformation.cofibered φ)) :
    Function.Injective (mapLiftClasses φ f x) := by
  let : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
  let hS2𝓕 := schlessingerConditionS2_of_isIsomorphismClasses
    𝓕 h𝓕.predeformation.cofibered
    (schlessingerConditionS2_of_satisfiesRS h𝓕.satisfiesRS)
    (.inl h𝓕.predeformation)
  let hS2𝓖 := schlessingerConditionS2_of_isIsomorphismClasses
    𝓖 h𝓖.predeformation.cofibered
    (schlessingerConditionS2_of_satisfiesRS h𝓖.satisfiesRS)
    (.inl h𝓖.predeformation)
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨h𝓕.predeformation⟩
  let : Fact (IsPredeformationCategory 𝓖.p) := ⟨h𝓖.predeformation⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.predeformation.cofibered))) := ⟨hS2𝓕⟩
  let : Fact (SchlessingerConditionS2
    (CategoryOfElements.π (isomorphismClasses 𝓖 h𝓖.predeformation.cofibered))) := ⟨hS2𝓖⟩
  let := liftAction 𝓕 h𝓕 f hf hann x
  let := liftAction 𝓖 h𝓖 f hf hann ((fiberFunctor φ A).obj x)
  let dφ := IsLinearMap.mk'
    (differential h𝓕.predeformation.cofibered h𝓖.predeformation.cofibered φ)
    (differential_isLinearMap 𝓕 𝓖 h𝓕.predeformation h𝓖.predeformation hS2𝓕 hS2𝓖 φ)
  let L := TensorProduct.map dφ
    (LinearMap.id : RingHom.ker f.hom.toRingHom →ₗ[k] RingHom.ker f.hom.toRingHom)
  have hL : Function.Bijective L :=
    TensorProduct.map_bijective hd Function.bijective_id
  intro a b hab
  have hsource := liftAction_bijective 𝓕 h𝓕 f hf hann x a
  have htarget := liftAction_bijective 𝓖 h𝓖 f hf hann
    ((fiberFunctor φ A).obj x) (mapLiftClasses φ f x a)
  let e := Equiv.ofBijective (fun t => t +ᵥ a) hsource
  let t₁ := e.symm a
  let t₂ := e.symm b
  have ht₁ : t₁ +ᵥ a = a := e.apply_symm_apply a
  have ht₂ : t₂ +ᵥ a = b := e.apply_symm_apply b
  have hact : L t₁ +ᵥ mapLiftClasses φ f x a = L t₂ +ᵥ mapLiftClasses φ f x a := by
    calc
      L t₁ +ᵥ mapLiftClasses φ f x a = mapLiftClasses φ f x (t₁ +ᵥ a) :=
        (mapLiftClasses_vadd 𝓕 𝓖 h𝓕 h𝓖 φ f hf hann x a t₁).symm
      _ = mapLiftClasses φ f x (t₂ +ᵥ a) := by rw [ht₁, ht₂, hab]
      _ = L t₂ +ᵥ mapLiftClasses φ f x a :=
        mapLiftClasses_vadd 𝓕 𝓖 h𝓕 h𝓖 φ f hf hann x a t₂
  calc
    a = t₁ +ᵥ a := ht₁.symm
    _ = t₂ +ᵥ a := by rw [hL.1 (htarget.1 hact)]
    _ = b := ht₂

set_option backward.isDefEq.respectTransparency false in
/-- Injectivity of a component propagates up a small extension. -/
private theorem injective_app_of_small_extension
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F G : ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ Type t}
    (hF : IsDeformationFunctor F)
    (hG : IsDeformationFunctor G)
    (φ : F ⟶ G)
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A)
    (hsmall : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f.hom.toRingHom))
    (hbase : Function.Injective (φ.app A))
    (hd : Function.Bijective
      (differential
        ((isDeformationCategory_iff F).2 hF).predeformation.cofibered
        ((isDeformationCategory_iff G).2 hG).predeformation.cofibered
        (elementsBasedFunctor φ))) :
    Function.Injective (φ.app A') := by
  have hf : Function.Surjective f.hom := hsmall.2.2.2.2.1
  have hann := smallExtension_kernel_annihilated f hsmall
  let hFCat := (isDeformationCategory_iff F).2 hF
  let hGCat := (isDeformationCategory_iff G).2 hG
  let 𝓕 := BasedCategory.ofFunctor (CategoryOfElements.π F)
  let 𝓖 := BasedCategory.ofFunctor (CategoryOfElements.π G)
  intro y₁ y₂ hy
  have hdown : F.map f y₁ = F.map f y₂ := by
    apply hbase
    calc
      φ.app A (F.map f y₁) = G.map f (φ.app A' y₁) := φ.naturality_apply f y₁
      _ = G.map f (φ.app A' y₂) := by rw [hy]
      _ = φ.app A (F.map f y₂) := (φ.naturality_apply f y₂).symm
  let xval := F.map f y₁
  let x : 𝓕.p.Fiber A := ⟨F.elementsMk A xval, rfl⟩
  let hm₁ : F.elementsMk A' y₁ ⟶ F.elementsMk A xval := Functor.Elements.homMk f rfl
  let hm₂ : F.elementsMk A' y₂ ⟶ F.elementsMk A xval :=
    Functor.Elements.homMk f hdown.symm
  let l₁ : Lift 𝓕.p f x :=
    { obj := F.elementsMk A' y₁
      hom := hm₁
      isHomLift := IsHomLift.map (p := 𝓕.p) hm₁ }
  let l₂ : Lift 𝓕.p f x :=
    { obj := F.elementsMk A' y₂
      hom := hm₂
      isHomLift := IsHomLift.map (p := 𝓕.p) hm₂ }
  let a₁ : LiftClasses 𝓕.p f x := ThinSkeleton.mk l₁
  let a₂ : LiftClasses 𝓕.p f x := ThinSkeleton.mk l₂
  have hmap : mapLiftClasses (elementsBasedFunctor φ) f x a₁ =
      mapLiftClasses (elementsBasedFunctor φ) f x a₂ := by
    let L₁ := (liftFunctor (elementsBasedFunctor φ) f x).obj l₁
    let L₂ := (liftFunctor (elementsBasedFunctor φ) f x).obj l₂
    show ThinSkeleton.mk L₁ = ThinSkeleton.mk L₂
    apply Quotient.sound
    let g : L₁.obj ⟶ L₂.obj := Functor.Elements.homMk (𝟙 A') (by
      show G.map (𝟙 A') (φ.app A' y₁) = φ.app A' y₂
      simpa using hy)
    let ginv : L₂.obj ⟶ L₁.obj := Functor.Elements.homMk (𝟙 A') (by
      show G.map (𝟙 A') (φ.app A' y₂) = φ.app A' y₁
      simpa using hy.symm)
    let gh : Lift.Hom L₁ L₂ :=
      { hom := g
        isHomLift := IsHomLift.map (p := 𝓖.p) g
        fac := by
          apply Functor.Elements.hom_ext
          show (g.hom ≫ f) = f
          exact Category.id_comp f }
    let gih : Lift.Hom L₂ L₁ :=
      { hom := ginv
        isHomLift := IsHomLift.map (p := 𝓖.p) ginv
        fac := by
          apply Functor.Elements.hom_ext
          show (ginv.hom ≫ f) = f
          exact Category.id_comp f }
    exact ⟨
      { hom := gh
        inv := gih
        hom_inv_id := by
          apply Lift.Hom.ext
          apply Functor.Elements.hom_ext
          show (𝟙 A' ≫ 𝟙 A') = 𝟙 A'
          simp
        inv_hom_id := by
          apply Lift.Hom.ext
          apply Functor.Elements.hom_ext
          show (𝟙 A' ≫ 𝟙 A') = 𝟙 A'
          simp }⟩
  have hclass := mapLiftClasses_injective_of_differential_bijective
    hFCat hGCat (elementsBasedFunctor φ) f hf hann x hd hmap
  obtain ⟨i⟩ := Quotient.exact hclass
  exact eq_of_isHomLift_id i.hom.hom i.hom.isHomLift

/-- Bijectivity propagates from the end of a chain of small extensions to its start. -/
private theorem app_bijective_of_small_chain
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F G : ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ Type t}
    (hF : IsDeformationFunctor F)
    (hG : IsDeformationFunctor G)
    (φ : F ⟶ G)
    (hφ : IsSmooth (elementsBasedFunctor φ))
    (hd : Function.Bijective
      (differential
        ((isDeformationCategory_iff F).2 hF).predeformation.cofibered
        ((isDeformationCategory_iff G).2 hG).predeformation.cofibered
        (elementsBasedFunctor φ))) :
    ∀ (n : ℕ) (D : ComposableArrows (ArtinianLocalAlgCat.{u, w, w} Λ k) n),
      (∀ (i : ℕ) (hi : i < n),
        InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom (D.map' i (i + 1)).hom.toRingHom)) →
      Function.Bijective (φ.app D.right) → Function.Bijective (φ.app D.left) := by
  intro n
  induction n with
  | zero =>
      intro D _ hright
      simpa [ComposableArrows.left, ComposableArrows.right] using hright
  | succ n ih =>
      intro D hsmall hright
      let T := D.δ₀
      have hsmallT : ∀ (i : ℕ) (hi : i < n),
          InfinitesimalLifting.IsSmallExtension
            (CommRingCat.ofHom (T.map' i (i + 1)).hom.toRingHom) :=
        fun i hi => hsmall (i + 1) (by omega)
      have htail := ih T hsmallT hright
      have hsmall₀ : InfinitesimalLifting.IsSmallExtension
          (CommRingCat.ofHom (D.map' 0 1).hom.toRingHom) := hsmall 0 (by omega)
      have hinj := injective_app_of_small_extension hF hG φ (D.map' 0 1)
        hsmall₀ htail.1 hd
      have hsurj := app_surjective_of_smooth_of_app_surjective φ hφ
        (D.map' 0 1) hsmall₀.2.2.2.2.1 htail.2
      have hleft : Function.Bijective (φ.app (D.obj' 0)) := ⟨hinj, hsurj⟩
      simpa [ComposableArrows.left] using hleft

/-- Bijectivity of a component transports along an isomorphism of the base. -/
private theorem app_bijective_of_iso_target
    {C : Type u} [Category.{w} C] {F G : C ⥤ Type t} (φ : F ⟶ G)
    {A B : C} (e : A ≅ B) (hB : Function.Bijective (φ.app B)) :
    Function.Bijective (φ.app A) := by
  have hF : Function.Bijective (F.map e.hom) :=
    (CategoryTheory.isIso_iff_bijective _).mp (by infer_instance)
  have hG : Function.Bijective (G.map e.hom) :=
    (CategoryTheory.isIso_iff_bijective _).mp (by infer_instance)
  constructor
  · intro x y hxy
    apply hF.1
    apply hB.1
    calc
      φ.app B (F.map e.hom x) = G.map e.hom (φ.app A x) := φ.naturality_apply e.hom x
      _ = G.map e.hom (φ.app A y) := congrArg (G.map e.hom) hxy
      _ = φ.app B (F.map e.hom y) := (φ.naturality_apply e.hom y).symm
  · intro y
    obtain ⟨xB, hxB⟩ := hB.2 (G.map e.hom y)
    obtain ⟨xA, hxA⟩ := hF.2 xB
    refine ⟨xA, ?_⟩
    apply hG.1
    calc
      G.map e.hom (φ.app A xA) = φ.app B (F.map e.hom xA) :=
        (φ.naturality_apply e.hom xA).symm
      _ = φ.app B xB := congrArg (φ.app B) hxA
      _ = G.map e.hom y := hxB

/-! ### The isomorphism criterion -/

/-- **Stacks Project, Tag 06JL.** A smooth morphism of deformation functors whose differential
is bijective is an isomorphism. -/
@[stacks 06JL]
public theorem isIso_of_isSmooth_of_tangent_bijective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F G : ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ Type t}
    (hF : IsDeformationFunctor F)
    (hG : IsDeformationFunctor G)
    (φ : F ⟶ G)
    (hφ : IsSmooth (elementsBasedFunctor φ))
    (hdφ : Function.Bijective
      (φ.app (augmentedDualNumbers (Λ := Λ) (k := k)))) :
    IsIso φ := by
  let K : ArtinianLocalAlgCat.{u, w, w} Λ k := residueFieldObject.{u, w, w} Λ k
  let : Unique (F.obj K) := hF.1.some
  let : Unique (G.obj K) := hG.1.some
  have hK : Function.Bijective (φ.app K) :=
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  have hd := differential_bijective_of_app_bijective hF hG φ hdφ
  have hApps : ∀ A : ArtinianLocalAlgCat.{u, w, w} Λ k,
      Function.Bijective (φ.app A) := by
    intro A
    let q : A ⟶ K := residueFieldMorphism
    have hq : Function.Surjective q.hom := residueFieldMorphism_surjective
    obtain ⟨n, D, hleft, e, -, hsmall⟩ := surjective_factors_into_smallExtensions q hq
    have hright := app_bijective_of_iso_target φ e hK
    have hchain := app_bijective_of_small_chain hF hG φ hφ hd n D hsmall hright
    cases hleft
    exact hchain
  exact (NatTrans.isIso_iff_isIso_app φ).2 fun A =>
    (CategoryTheory.isIso_iff_bijective _).2 (hApps A)

end

end Deformation
