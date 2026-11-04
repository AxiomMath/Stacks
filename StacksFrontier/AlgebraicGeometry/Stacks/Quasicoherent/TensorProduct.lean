module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor

/-!
# Bilinear maps of presheaves of modules

A bilinear map between presheaves of modules over a presheaf of commutative rings is a family
of bilinear maps on sections, one for each object, compatible with every restriction map.  The
three presheaves of modules may have sections in three different universes.

## Main definitions

* `Stacks.Modules.BilinearMap` is a bilinear map of presheaves of modules.
* `Stacks.Modules.BilinearMap.comp` postcomposes a bilinear map with a morphism of presheaves
  of modules.
* `Stacks.Modules.BilinearMap.homEquiv` identifies the bilinear maps out of a pair of
  presheaves of modules with the morphisms out of their objectwise tensor product.
* `Stacks.Modules.BilinearMap.descend` factors a bilinear map into a sheaf of modules through
  a bilinear map whose associated map out of the objectwise tensor product is locally
  bijective.

## Main results

* `Stacks.Modules.isLocallyInjective_of_le`: local injectivity of a map of presheaves passes to
  a finer topology.
* `Stacks.Modules.existsUnique_hom`: a bilinear map whose associated map out of the objectwise
  tensor product is locally bijective exhibits its target as the tensor product in the category
  of sheaves of modules: every bilinear map into a sheaf of modules factors through it
  uniquely.
* `Stacks.Modules.existsUnique_hom_of_le`: the same factorization holds in the category of
  sheaves of modules for every topology finer than the one on which local bijectivity holds.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u v w m n t

namespace Stacks.Modules

variable {C : Type v} [Category.{w} C] (R : Cᵒᵖ ⥤ CommRingCat.{u})

/-- A bilinear map of presheaves of modules over a presheaf of commutative rings: a family of
bilinear maps on sections, one for each object, compatible with every restriction map.  The
three universes of sections are independent. -/
public structure BilinearMap
    (F : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat))
    (G : PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat))
    (H : PresheafOfModules.{t} (R ⋙ forget₂ CommRingCat RingCat)) where
  /-- The bilinear map on sections at an object. -/
  app (U : Cᵒᵖ) : F.obj U →ₗ[(R ⋙ forget₂ CommRingCat RingCat).obj U]
    G.obj U →ₗ[(R ⋙ forget₂ CommRingCat RingCat).obj U] H.obj U
  /-- Compatibility with restriction of sections. -/
  naturality {U V : Cᵒᵖ} (f : U ⟶ V) (x : F.obj U) (y : G.obj U) :
    app V (F.map f x) (G.map f y) = H.map f (app U x y)

namespace BilinearMap

variable {R}
  {F : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat)}
  {H H' : PresheafOfModules.{t} (R ⋙ forget₂ CommRingCat RingCat)}

/-- Two bilinear maps with the same values on sections are equal. -/
@[ext] public theorem ext {b b' : BilinearMap R F G H}
    (h : ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U), b.app U x y = b'.app U x y) : b = b' := by
  obtain ⟨app, _⟩ := b
  obtain ⟨app', _⟩ := b'
  simp only [BilinearMap.mk.injEq]
  exact funext fun U ↦ LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ h U x y

/-- Postcompose a bilinear map with a morphism of presheaves of modules. -/
public def comp (b : BilinearMap R F G H) (f : H ⟶ H') : BilinearMap R F G H' where
  app U := LinearMap.compr₂ (b.app U) (f.app U).hom
  naturality g x y :=
    (congrArg (f.app _).hom (b.naturality g x y)).trans
      (PresheafOfModules.naturality_apply f g (b.app _ x y))

/-- The postcomposite `b.comp f` sends a pair of sections `x`, `y` to the image under `f` of
`b.app U x y`. -/
@[simp] public theorem comp_app (b : BilinearMap R F G H) (f : H ⟶ H') (U : Cᵒᵖ)
    (x : F.obj U) (y : G.obj U) : (b.comp f).app U x y = f.app U (b.app U x y) := rfl

end BilinearMap

section Tensor

variable {R} {F G H : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- The bilinear map of presheaves of modules determined by a morphism out of the objectwise
tensor product. -/
public noncomputable def BilinearMap.ofTensorHom (f : F ⊗ G ⟶ H) : BilinearMap R F G H where
  app U := LinearMap.compr₂
    (TensorProduct.mk ((R ⋙ forget₂ CommRingCat RingCat).obj U) (F.obj U) (G.obj U))
    (f.app U).hom
  naturality g x y := PresheafOfModules.naturality_apply f g (x ⊗ₜ y)

/-- The bilinear map `BilinearMap.ofTensorHom f` sends a pair of sections `x`, `y` to the image
under `f` of `x ⊗ₜ y`. -/
@[simp] public theorem BilinearMap.ofTensorHom_app (f : F ⊗ G ⟶ H) (U : Cᵒᵖ)
    (x : F.obj U) (y : G.obj U) :
    (BilinearMap.ofTensorHom f).app U x y = (f.app U).hom (x ⊗ₜ y) := rfl

/-- The morphism out of the objectwise tensor product determined by a bilinear map of
presheaves of modules. -/
public noncomputable def BilinearMap.tensorHom (b : BilinearMap R F G H) : F ⊗ G ⟶ H where
  app U := ModuleCat.MonoidalCategory.tensorLift (fun x y ↦ b.app U x y)
    (fun x x' y ↦ by rw [map_add]; rfl)
    (fun a x y ↦ by rw [map_smul]; rfl)
    (fun x y y' ↦ map_add _ _ _)
    (fun a x y ↦ map_smul _ _ _)
  naturality {U V} g := ModuleCat.MonoidalCategory.tensor_ext fun x y ↦ b.naturality g x y

/-- The morphism `b.tensorHom` sends a pure tensor `x ⊗ₜ y` of sections to `b.app U x y`. -/
@[simp] public theorem BilinearMap.tensorHom_app (b : BilinearMap R F G H) (U : Cᵒᵖ)
    (x : F.obj U) (y : G.obj U) :
    (b.tensorHom.app U).hom (x ⊗ₜ y) = b.app U x y := rfl

/-- Morphisms out of the objectwise tensor product of two presheaves of modules are the
bilinear maps out of the pair. -/
public noncomputable def BilinearMap.homEquiv : (F ⊗ G ⟶ H) ≃ BilinearMap R F G H where
  toFun := BilinearMap.ofTensorHom
  invFun := BilinearMap.tensorHom
  left_inv _ := PresheafOfModules.hom_ext fun _ ↦
    ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ rfl
  right_inv _ := BilinearMap.ext fun _ _ _ ↦ rfl

end Tensor

section Descent

open AlgebraicGeometry

variable {R} {F G T H : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- The map of type-valued presheaves of sections underlying a morphism of presheaves of
modules. -/
public noncomputable abbrev sectionsMap (f : F ⟶ G) :
    SheafOfModules.moduleTypes F ⟶ SheafOfModules.moduleTypes G :=
  Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map f) (forget AddCommGrpCat.{u})

variable (J : GrothendieckTopology C)

/-- Local injectivity of a map of presheaves passes to a finer topology, having more covering
sieves. -/
public theorem isLocallyInjective_of_le {K : GrothendieckTopology C} (hJK : J ≤ K)
    {P Q : Cᵒᵖ ⥤ Type u} (v : P ⟶ Q) (h : Presheaf.IsLocallyInjective J v) :
    Presheaf.IsLocallyInjective K v where
  equalizerSieve_mem x y hxy := hJK _ (h.equalizerSieve_mem x y hxy)

/-- The descent of a map to a sheaf along a locally bijective map is computed, after
restriction, from any local preimage. -/
public theorem descent_apply {P Q K : Cᵒᵖ ⥤ Type u} (v : P ⟶ Q)
    [Presheaf.IsLocallyInjective J v] [Presheaf.IsLocallySurjective J v]
    (hK : Presheaf.IsSheaf J K) (c : P ⟶ K) {U V : Cᵒᵖ} (g : U ⟶ V) (s : Q.obj U)
    (z : P.obj V) (hz : v.app V z = Q.map g s) :
    K.map g ((SheafOfModules.descent J v hK c).app U s) = c.app V z :=
  (SheafOfModules.descent_exists J v hK (fun X x ↦ c.app X x)
    (fun k x ↦ c.naturality_apply k x) U s).choose_spec g z hz

variable {J}

/-- Two morphisms out of the target of a bilinear map `u` whose associated map out of the
objectwise tensor product is locally surjective, into a presheaf of modules whose sections form a
sheaf, are equal when they agree on the values of `u`. -/
public theorem hom_ext_of_isLocallySurjective (u : BilinearMap R F G T)
    [Presheaf.IsLocallySurjective J (sectionsMap u.tensorHom)]
    (hH : Presheaf.IsSheaf J (SheafOfModules.moduleTypes H)) {f f' : T ⟶ H}
    (h : ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U),
      f.app U (u.app U x y) = f'.app U (u.app U x y)) : f = f' := by
  have hcomp : u.tensorHom ≫ f = u.tensorHom ≫ f' :=
    PresheafOfModules.hom_ext fun U ↦ ModuleCat.MonoidalCategory.tensor_ext fun x y ↦ h U x y
  refine PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  apply hH.isSeparated _ _ (Presheaf.imageSieve_mem J (sectionsMap u.tensorHom) s)
  rintro V g ⟨z, hz⟩
  have hz' : u.tensorHom.app (Opposite.op V) z = T.map g.op s := hz
  show H.map g.op (f.app U s) = H.map g.op (f'.app U s)
  rw [← PresheafOfModules.naturality_apply f g.op s, ← PresheafOfModules.naturality_apply f' g.op s,
    ← hz']
  exact congr(($hcomp).app (Opposite.op V) z)

/-- A section of the target of a bilinear map is, locally, the image of a section of the
objectwise tensor product of the two sources. -/
public theorem exists_preimage (u : BilinearMap R F G T) {U : Cᵒᵖ} {V : C} {g : V ⟶ U.unop}
    {s : T.obj U} (hg : (Presheaf.imageSieve (sectionsMap u.tensorHom) s).arrows g) :
    ∃ z : (F ⊗ G).obj (Opposite.op V), u.tensorHom.app (Opposite.op V) z = T.map g.op s :=
  ⟨hg.choose, hg.choose_spec⟩

/-- The morphism of presheaves of modules descending a bilinear map along a locally bijective
comparison with the objectwise tensor product. -/
public noncomputable def BilinearMap.descend (u : BilinearMap R F G T)
    [Presheaf.IsLocallyInjective J (sectionsMap u.tensorHom)]
    [Presheaf.IsLocallySurjective J (sectionsMap u.tensorHom)]
    (hH : Presheaf.IsSheaf J (SheafOfModules.moduleTypes H)) (b : BilinearMap R F G H) :
    T ⟶ H where
  app U := ModuleCat.ofHom
    { toFun := fun s ↦ (SheafOfModules.descent J (sectionsMap u.tensorHom) hH
        (sectionsMap b.tensorHom)).app U s
      map_add' := fun s s' ↦ by
        apply hH.isSeparated _ _ (J.intersection_covering
          (Presheaf.imageSieve_mem J (sectionsMap u.tensorHom) s)
          (Presheaf.imageSieve_mem J (sectionsMap u.tensorHom) s'))
        intro V g hg
        obtain ⟨z, hz₁⟩ := exists_preimage u hg.1
        obtain ⟨z', hz₂⟩ := exists_preimage u hg.2
        have hadd : (sectionsMap u.tensorHom).app (Opposite.op V) (z + z') =
            (SheafOfModules.moduleTypes T).map g.op (s + s') := by
          change u.tensorHom.app (Opposite.op V) (z + z') = T.map g.op (s + s')
          rw [map_add (ConcreteCategory.hom (u.tensorHom.app (Opposite.op V))), hz₁, hz₂]
          exact (map_add _ _ _).symm
        have e₀ : H.map g.op ((SheafOfModules.descent J (sectionsMap u.tensorHom) hH
            (sectionsMap b.tensorHom)).app U (s + s')) = b.tensorHom.app (Opposite.op V) (z + z') :=
          descent_apply J (sectionsMap u.tensorHom) hH (sectionsMap b.tensorHom)
            g.op (s + s') (z + z') hadd
        have e₁ : H.map g.op ((SheafOfModules.descent J (sectionsMap u.tensorHom) hH
            (sectionsMap b.tensorHom)).app U s) = b.tensorHom.app (Opposite.op V) z :=
          descent_apply J (sectionsMap u.tensorHom) hH (sectionsMap b.tensorHom) g.op s z hz₁
        have e₂ : H.map g.op ((SheafOfModules.descent J (sectionsMap u.tensorHom) hH
            (sectionsMap b.tensorHom)).app U s') = b.tensorHom.app (Opposite.op V) z' :=
          descent_apply J (sectionsMap u.tensorHom) hH (sectionsMap b.tensorHom) g.op s' z' hz₂
        change H.map g.op _ = H.map g.op _
        refine e₀.trans ?_
        rw [map_add (ConcreteCategory.hom (b.tensorHom.app (Opposite.op V))), ← e₁, ← e₂]
        exact (map_add _ _ _).symm
      map_smul' := fun a s ↦ by
        apply hH.isSeparated _ _ (Presheaf.imageSieve_mem J (sectionsMap u.tensorHom) s)
        intro V g hg
        obtain ⟨z, hz₁⟩ := exists_preimage u hg
        have hsmul : (sectionsMap u.tensorHom).app (Opposite.op V)
            ((R ⋙ forget₂ CommRingCat RingCat).map g.op a • z) =
            (SheafOfModules.moduleTypes T).map g.op (a • s) := by
          change u.tensorHom.app (Opposite.op V)
            ((R ⋙ forget₂ CommRingCat RingCat).map g.op a • z) = T.map g.op (a • s)
          rw [map_smul (ConcreteCategory.hom (u.tensorHom.app (Opposite.op V))), hz₁]
          exact (PresheafOfModules.map_smul T g.op a s).symm
        have e₀ : H.map g.op ((SheafOfModules.descent J (sectionsMap u.tensorHom) hH
            (sectionsMap b.tensorHom)).app U (a • s)) = b.tensorHom.app (Opposite.op V)
              ((R ⋙ forget₂ CommRingCat RingCat).map g.op a • z) :=
          descent_apply J (sectionsMap u.tensorHom) hH (sectionsMap b.tensorHom)
            g.op (a • s) _ hsmul
        have e₁ : H.map g.op ((SheafOfModules.descent J (sectionsMap u.tensorHom) hH
            (sectionsMap b.tensorHom)).app U s) = b.tensorHom.app (Opposite.op V) z :=
          descent_apply J (sectionsMap u.tensorHom) hH (sectionsMap b.tensorHom) g.op s z hz₁
        change H.map g.op _ = H.map g.op _
        refine e₀.trans ?_
        rw [map_smul (ConcreteCategory.hom (b.tensorHom.app (Opposite.op V))), ← e₁]
        exact (PresheafOfModules.map_smul H g.op a _).symm }
  naturality g := ModuleCat.hom_ext (LinearMap.ext fun s ↦
    CategoryTheory.congr_fun
      ((SheafOfModules.descent J (sectionsMap u.tensorHom) hH
        (sectionsMap b.tensorHom)).naturality g) s)

/-- The descended morphism recovers the bilinear map on the image of the comparison. -/
public theorem BilinearMap.descend_app (u : BilinearMap R F G T)
    [Presheaf.IsLocallyInjective J (sectionsMap u.tensorHom)]
    [Presheaf.IsLocallySurjective J (sectionsMap u.tensorHom)]
    (hH : Presheaf.IsSheaf J (SheafOfModules.moduleTypes H)) (b : BilinearMap R F G H)
    (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U) :
    (u.descend hH b).app U (u.app U x y) = b.app U x y := by
  have h : (sectionsMap u.tensorHom ≫ SheafOfModules.descent J (sectionsMap u.tensorHom) hH
      (sectionsMap b.tensorHom)).app U = (sectionsMap b.tensorHom).app U :=
    congrArg (fun k ↦ NatTrans.app k U) (SheafOfModules.descent_comp J
      (sectionsMap u.tensorHom) hH (sectionsMap b.tensorHom))
  exact CategoryTheory.congr_fun h (x ⊗ₜ y)

/-- A bilinear map of presheaves of modules whose associated map out of the objectwise tensor
product is locally bijective exhibits its target as the tensor product in the category of sheaves
of modules for that topology: a bilinear map into a sheaf of modules has a unique linear
factorization through it. -/
public theorem existsUnique_hom (u : BilinearMap R F G T)
    [Presheaf.IsLocallyInjective J (sectionsMap u.tensorHom)]
    [Presheaf.IsLocallySurjective J (sectionsMap u.tensorHom)]
    (hH : Presheaf.IsSheaf J (SheafOfModules.moduleTypes H)) (b : BilinearMap R F G H) :
    ∃! f : T ⟶ H, ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U),
      f.app U (u.app U x y) = b.app U x y :=
  ⟨u.descend hH b, u.descend_app hH b, fun _ hf ↦
    hom_ext_of_isLocallySurjective u hH fun U x y ↦
      (hf U x y).trans (u.descend_app hH b U x y).symm⟩

/-- A bilinear map of presheaves of modules whose associated map out of the objectwise tensor
product is locally bijective for a topology `J` exhibits its target as the tensor product in the
category of sheaves of modules for every topology `K` finer than `J`: a bilinear map into a
`K`-sheaf of modules has a unique linear factorization through it. -/
public theorem existsUnique_hom_of_le {J K : GrothendieckTopology C} (hJK : J ≤ K)
    (u : BilinearMap R F G T)
    (hinj : Presheaf.IsLocallyInjective J (sectionsMap u.tensorHom))
    (hsurj : Presheaf.IsLocallySurjective J (sectionsMap u.tensorHom))
    (hH : Presheaf.IsSheaf K (SheafOfModules.moduleTypes H)) (b : BilinearMap R F G H) :
    ∃! f : T ⟶ H, ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U),
      f.app U (u.app U x y) = b.app U x y := by
  have := hinj
  have := hsurj
  refine existsUnique_hom (J := J) u ?_ b
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_of_le _ hJK ((isSheaf_iff_isSheaf_of_type K _).mp hH)

end Descent

end Stacks.Modules

end
