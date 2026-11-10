module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorProduct
public import StacksFrontier.CategoryTheory.Sites.Modules.MixedUniverseTensor

/-!
# The tensor product of presheaves of modules in independent universes

A bilinear map of presheaves of modules over a presheaf of commutative rings
`R : Cᵒᵖ ⥤ CommRingCat.{u}` makes sense with the sections of the two sources and of the target
in three independent universes.  This file identifies the bilinear maps out of a pair of
presheaves of modules with sections in `Type m` and `Type n` with the morphisms out of their
objectwise tensor product, whose sections lie in `Type (max m n)`, and does the same for the
universe lift of that tensor product, whose sections lie in `Type (max u m n)`.  It then
descends the second identification to sheaves of modules: a bilinear map whose associated map
out of the objectwise tensor product is locally bijective exhibits its target as the tensor
product in the category of sheaves of modules, for every topology finer than the one on which
local bijectivity is checked.

## Main definitions

* `Stacks.Modules.BilinearMap.ofMixedTensorHom` and
  `Stacks.Modules.BilinearMap.mixedTensorHom` pass between bilinear maps out of a pair of
  presheaves of modules and morphisms out of their objectwise tensor product, and
  `Stacks.Modules.BilinearMap.mixedHomEquiv` is the resulting bijection.
* `Stacks.Modules.BilinearMap.ofUliftTensorHom`,
  `Stacks.Modules.BilinearMap.uliftTensorHom` and
  `Stacks.Modules.BilinearMap.uliftHomEquiv` are the same three for the objectwise tensor
  product whose sections are raised to the universe of the coefficient rings as well.
* `Stacks.Modules.sectionTypes` is the type-valued presheaf of sections of a presheaf of
  modules, and `Stacks.Modules.sectionTypesMap` the map of such presheaves underlying a
  morphism.
* `Stacks.Modules.BilinearMap.uliftDescend` factors a bilinear map into a sheaf of modules
  through a bilinear map whose associated map out of the objectwise tensor product is locally
  bijective.
* `Stacks.Modules.tensorSheafBifunctorMixed` is the tensor product of sheaves of modules with
  sections in independent universes `m` and `n`, landing in sheaves of modules with sections in
  `max u m n`.

## Main results

* `Stacks.Modules.existsUnique_hom_ulift`: a bilinear map whose associated map out of the
  objectwise tensor product is locally bijective exhibits its target as the tensor product in
  the category of sheaves of modules for that topology: every bilinear map into a sheaf of
  modules factors through it uniquely.
* `Stacks.Modules.existsUnique_hom_ulift_of_le`: one such comparison serves every topology
  finer than the one on which it is checked, which is the formal content of the agreement of
  the tensor products computed on the Zariski, étale and fppf sites.
* `Stacks.Modules.hom_ext_of_isLocallySurjective_ulift`: a morphism out of the target of a
  locally surjective bilinear map is determined by its values on the image of that map.

## Implementation notes

The sections of the target of a universal property lie in the universe of the sections of the
tensor product itself, not in a fourth independent universe.  This is forced: `ModuleCat.{v} S`
is a category at one universe `v`, so a morphism out of a module whose carrier lies in
`Type (max m n)` has its target there too.  The notion of bilinear map, by contrast, keeps the
three universes independent, since it is a family of bilinear maps on sections and not a
morphism in any one category.

Two universal properties are therefore proved: one for the objectwise tensor product itself,
whose sections lie in `Type (max m n)`, and one for its universe lift, whose sections lie in
`Type (max u m n)` with `u` the universe of the coefficient rings.  The second is the shape in
which the tensor product of quasi-coherent modules is formed, since a sheaf of modules obtained
by sheafification has its sections in the universe of the coefficient rings at least; neither
is a consequence of the other, because the two targets are different universes whenever the
coefficient rings lie above the sections.

The type-valued presheaf of sections is taken here with the universe of the sections
independent of the universe of the coefficient rings; at equal universes it is the one used for
the single-universe theory, definitionally.  The descent machinery it feeds, and the passage of
local injectivity to a finer topology, are already independent of the universes of the site and
are used unchanged.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TensorProduct

universe u v w m n t

namespace Stacks.Modules

open PresheafOfModules (tensorObj)

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

section Tensor

variable {F : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat)}
  {H : PresheafOfModules.{max m n} (R ⋙ forget₂ CommRingCat RingCat)}

/-- The bilinear map of presheaves of modules determined by a morphism out of the objectwise
tensor product, with the sections of the two sources in independent universes. -/
public noncomputable def BilinearMap.ofMixedTensorHom (f : tensorObj F G ⟶ H) :
    BilinearMap R F G H where
  app U := LinearMap.compr₂
    (TensorProduct.mk ((R ⋙ forget₂ CommRingCat RingCat).obj U) (F.obj U) (G.obj U))
    (f.app U).hom
  naturality g x y := PresheafOfModules.naturality_apply f g (x ⊗ₜ y)

/-- The bilinear map determined by a morphism `f` out of the objectwise tensor product sends
sections `x` and `y` to the image of `x ⊗ₜ y` under `f`. -/
@[simp] public theorem BilinearMap.ofMixedTensorHom_app (f : tensorObj F G ⟶ H) (U : Cᵒᵖ)
    (x : F.obj U) (y : G.obj U) :
    (BilinearMap.ofMixedTensorHom f).app U x y = (f.app U).hom (x ⊗ₜ y) := rfl

/-- The morphism out of the objectwise tensor product determined by a bilinear map of
presheaves of modules, with the sections of the two sources in independent universes. -/
public noncomputable def BilinearMap.mixedTensorHom (b : BilinearMap R F G H) :
    tensorObj F G ⟶ H where
  app U := ModuleCat.MixedTensor.tensorLift (fun x y ↦ b.app U x y)
    (fun x x' y ↦ by rw [map_add]; rfl)
    (fun a x y ↦ by rw [map_smul]; rfl)
    (fun x y y' ↦ map_add _ _ _)
    (fun a x y ↦ map_smul _ _ _)
  naturality g := ModuleCat.MixedTensor.tensor_ext fun x y ↦ b.naturality g x y

/-- The morphism out of the objectwise tensor product determined by a bilinear map `b` sends
`x ⊗ₜ y` to `b.app U x y`. -/
@[simp] public theorem BilinearMap.mixedTensorHom_app (b : BilinearMap R F G H) (U : Cᵒᵖ)
    (x : F.obj U) (y : G.obj U) :
    (b.mixedTensorHom.app U).hom (x ⊗ₜ y) = b.app U x y := rfl

/-- **Stacks 06WN(1).**  Morphisms out of the objectwise tensor product of two presheaves of
modules are the bilinear maps out of the pair, with the sections of the two sources in
independent universes. -/
public noncomputable def BilinearMap.mixedHomEquiv :
    (tensorObj F G ⟶ H) ≃ BilinearMap R F G H where
  toFun := BilinearMap.ofMixedTensorHom
  invFun := BilinearMap.mixedTensorHom
  left_inv _ := PresheafOfModules.hom_ext fun _ ↦
    ModuleCat.MixedTensor.tensor_ext fun _ _ ↦ rfl
  right_inv _ := BilinearMap.ext fun _ _ _ ↦ rfl

/-- At sections in the universe of the coefficient rings, the morphism associated with a
bilinear map here is the one associated with it by the single-universe theory. -/
public theorem BilinearMap.mixedTensorHom_eq
    {F G H : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (b : BilinearMap R F G H) : b.mixedTensorHom = b.tensorHom := rfl

end Tensor

section TensorUlift

variable {F : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat)}
  {H : PresheafOfModules.{max u m n} (R ⋙ forget₂ CommRingCat RingCat)}

/-- The bilinear map of presheaves of modules determined by a morphism out of the objectwise
tensor product with raised sections. -/
public noncomputable def BilinearMap.ofUliftTensorHom
    (f : (tensorObj F G).uliftSections.{u} ⟶ H) :
    BilinearMap R F G H where
  app U := ModuleCat.MixedTensor.uliftTensorBilinear (f.app U)
  naturality g x y := PresheafOfModules.naturality_apply f g (ULift.up (x ⊗ₜ y))

/-- The bilinear map determined by a morphism `f` out of the objectwise tensor product with
raised sections sends sections `x` and `y` to the image of `ULift.up (x ⊗ₜ y)` under `f`. -/
@[simp] public theorem BilinearMap.ofUliftTensorHom_app
    (f : (tensorObj F G).uliftSections.{u} ⟶ H) (U : Cᵒᵖ)
    (x : F.obj U) (y : G.obj U) :
    (BilinearMap.ofUliftTensorHom f).app U x y = (f.app U).hom (ULift.up (x ⊗ₜ y)) := rfl

/-- The morphism out of the objectwise tensor product with raised sections determined by a
bilinear map of presheaves of modules. -/
public noncomputable def BilinearMap.uliftTensorHom (b : BilinearMap R F G H) :
    (tensorObj F G).uliftSections.{u} ⟶ H where
  app U := ModuleCat.MixedTensor.uliftTensorLift (fun x y ↦ b.app U x y)
    (fun x x' y ↦ by rw [map_add]; rfl)
    (fun a x y ↦ by rw [map_smul]; rfl)
    (fun x y y' ↦ map_add _ _ _)
    (fun a x y ↦ map_smul _ _ _)
  naturality g := ModuleCat.MixedTensor.uliftTensor_ext fun x y ↦ b.naturality g x y

/-- The morphism out of the objectwise tensor product with raised sections determined by a
bilinear map `b` sends `ULift.up (x ⊗ₜ y)` to `b.app U x y`. -/
@[simp] public theorem BilinearMap.uliftTensorHom_app (b : BilinearMap R F G H) (U : Cᵒᵖ)
    (x : F.obj U) (y : G.obj U) :
    (b.uliftTensorHom.app U).hom (ULift.up (x ⊗ₜ y)) = b.app U x y := rfl

/-- **Stacks 06WN(1).**  Morphisms out of the objectwise tensor product with raised sections of
two presheaves of modules are the bilinear maps out of the pair.  The sections of the two
sources lie in independent universes `m` and `n`, and those of the target in `max u m n`, where
`u` is the universe of the coefficient rings. -/
public noncomputable def BilinearMap.uliftHomEquiv :
    ((tensorObj F G).uliftSections.{u} ⟶ H) ≃ BilinearMap R F G H where
  toFun := BilinearMap.ofUliftTensorHom
  invFun := BilinearMap.uliftTensorHom
  left_inv _ := PresheafOfModules.hom_ext fun _ ↦
    ModuleCat.MixedTensor.uliftTensor_ext fun _ _ ↦ rfl
  right_inv _ := BilinearMap.ext fun _ _ _ ↦ rfl

end TensorUlift

section Descent

open AlgebraicGeometry

/-- The type-valued presheaf of sections of a presheaf of modules, with the universe of the
sections independent of the universe of the coefficient rings. -/
public noncomputable abbrev sectionTypes {R₀ : Cᵒᵖ ⥤ RingCat.{u}}
    (F : PresheafOfModules.{t} R₀) : Cᵒᵖ ⥤ Type t :=
  F.presheaf ⋙ forget AddCommGrpCat.{t}

/-- The map of type-valued presheaves of sections underlying a morphism of presheaves of
modules, with the universe of the sections independent of the universe of the coefficient
rings. -/
public noncomputable abbrev sectionTypesMap {R₀ : Cᵒᵖ ⥤ RingCat.{u}}
    {F G : PresheafOfModules.{t} R₀} (f : F ⟶ G) : sectionTypes F ⟶ sectionTypes G :=
  Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map f) (forget AddCommGrpCat.{t})

variable {F : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat)}
  {T H : PresheafOfModules.{max u m n} (R ⋙ forget₂ CommRingCat RingCat)}
  {J : GrothendieckTopology C}

/-- A morphism from the target of a locally surjective bilinear map into a presheaf of modules
whose sections form a sheaf is determined by its values on the image of that bilinear map. -/
public theorem hom_ext_of_isLocallySurjective_ulift (b₀ : BilinearMap R F G T)
    [Presheaf.IsLocallySurjective J (sectionTypesMap b₀.uliftTensorHom)]
    (hH : Presheaf.IsSheaf J (sectionTypes H)) {f f' : T ⟶ H}
    (h : ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U),
      f.app U (b₀.app U x y) = f'.app U (b₀.app U x y)) : f = f' := by
  have hcomp : b₀.uliftTensorHom ≫ f = b₀.uliftTensorHom ≫ f' :=
    PresheafOfModules.hom_ext fun U ↦
      ModuleCat.MixedTensor.uliftTensor_ext fun x y ↦ h U x y
  refine PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  apply hH.isSeparated _ _ (Presheaf.imageSieve_mem J (sectionTypesMap b₀.uliftTensorHom) s)
  rintro V g ⟨z, hz⟩
  have hz' : b₀.uliftTensorHom.app (Opposite.op V) z = T.map g.op s := hz
  change H.map g.op (f.app U s) = H.map g.op (f'.app U s)
  rw [← PresheafOfModules.naturality_apply f g.op s, ← PresheafOfModules.naturality_apply f' g.op s,
    ← hz']
  exact congr(($hcomp).app (Opposite.op V) z)

/-- A section of the target of a bilinear map is, locally, the image of a section of the
objectwise tensor product with raised sections of the two sources. -/
public theorem exists_preimage_ulift (b₀ : BilinearMap R F G T) {U : Cᵒᵖ} {V : C}
    {g : V ⟶ U.unop} {s : T.obj U}
    (hg : (Presheaf.imageSieve (sectionTypesMap b₀.uliftTensorHom) s).arrows g) :
    ∃ z : ((tensorObj F G).uliftSections.{u}).obj (Opposite.op V),
      b₀.uliftTensorHom.app (Opposite.op V) z = T.map g.op s :=
  ⟨hg.choose, hg.choose_spec⟩

/-- The morphism of presheaves of modules descending a bilinear map along a locally bijective
comparison with the objectwise tensor product with raised sections. -/
public noncomputable def BilinearMap.uliftDescend (b₀ : BilinearMap R F G T)
    [Presheaf.IsLocallyInjective J (sectionTypesMap b₀.uliftTensorHom)]
    [Presheaf.IsLocallySurjective J (sectionTypesMap b₀.uliftTensorHom)]
    (hH : Presheaf.IsSheaf J (sectionTypes H)) (b : BilinearMap R F G H) : T ⟶ H where
  app U := ModuleCat.ofHom
    { toFun := fun s ↦ (SheafOfModules.descent J (sectionTypesMap b₀.uliftTensorHom) hH
        (sectionTypesMap b.uliftTensorHom)).app U s
      map_add' := fun s s' ↦ by
        apply hH.isSeparated _ _ (J.intersection_covering
          (Presheaf.imageSieve_mem J (sectionTypesMap b₀.uliftTensorHom) s)
          (Presheaf.imageSieve_mem J (sectionTypesMap b₀.uliftTensorHom) s'))
        intro V g hg
        obtain ⟨z, hz₁⟩ := exists_preimage_ulift b₀ hg.1
        obtain ⟨z', hz₂⟩ := exists_preimage_ulift b₀ hg.2
        have hadd : (sectionTypesMap b₀.uliftTensorHom).app (Opposite.op V) (z + z') =
            (sectionTypes T).map g.op (s + s') := by
          change b₀.uliftTensorHom.app (Opposite.op V) (z + z') = T.map g.op (s + s')
          rw [map_add (ConcreteCategory.hom (b₀.uliftTensorHom.app (Opposite.op V))), hz₁, hz₂]
          exact (map_add _ _ _).symm
        have e₀ : H.map g.op ((SheafOfModules.descent J
            (sectionTypesMap b₀.uliftTensorHom) hH
            (sectionTypesMap b.uliftTensorHom)).app U (s + s')) =
              b.uliftTensorHom.app (Opposite.op V) (z + z') :=
          descent_apply J (sectionTypesMap b₀.uliftTensorHom) hH
            (sectionTypesMap b.uliftTensorHom) g.op (s + s') (z + z') hadd
        have e₁ : H.map g.op ((SheafOfModules.descent J
            (sectionTypesMap b₀.uliftTensorHom) hH
            (sectionTypesMap b.uliftTensorHom)).app U s) =
              b.uliftTensorHom.app (Opposite.op V) z :=
          descent_apply J (sectionTypesMap b₀.uliftTensorHom) hH
            (sectionTypesMap b.uliftTensorHom) g.op s z hz₁
        have e₂ : H.map g.op ((SheafOfModules.descent J
            (sectionTypesMap b₀.uliftTensorHom) hH
            (sectionTypesMap b.uliftTensorHom)).app U s') =
              b.uliftTensorHom.app (Opposite.op V) z' :=
          descent_apply J (sectionTypesMap b₀.uliftTensorHom) hH
            (sectionTypesMap b.uliftTensorHom) g.op s' z' hz₂
        change H.map g.op _ = H.map g.op _
        refine e₀.trans ?_
        rw [map_add (ConcreteCategory.hom (b.uliftTensorHom.app (Opposite.op V))), ← e₁, ← e₂]
        exact (map_add _ _ _).symm
      map_smul' := fun a s ↦ by
        apply hH.isSeparated _ _
          (Presheaf.imageSieve_mem J (sectionTypesMap b₀.uliftTensorHom) s)
        intro V g hg
        obtain ⟨z, hz₁⟩ := exists_preimage_ulift b₀ hg
        have hsmul : (sectionTypesMap b₀.uliftTensorHom).app (Opposite.op V)
            ((R ⋙ forget₂ CommRingCat RingCat).map g.op a • z) =
            (sectionTypes T).map g.op (a • s) := by
          change b₀.uliftTensorHom.app (Opposite.op V)
            ((R ⋙ forget₂ CommRingCat RingCat).map g.op a • z) = T.map g.op (a • s)
          rw [map_smul (ConcreteCategory.hom (b₀.uliftTensorHom.app (Opposite.op V))), hz₁]
          exact (PresheafOfModules.map_smul T g.op a s).symm
        have e₀ : H.map g.op ((SheafOfModules.descent J
            (sectionTypesMap b₀.uliftTensorHom) hH
            (sectionTypesMap b.uliftTensorHom)).app U (a • s)) =
              b.uliftTensorHom.app (Opposite.op V)
                ((R ⋙ forget₂ CommRingCat RingCat).map g.op a • z) :=
          descent_apply J (sectionTypesMap b₀.uliftTensorHom) hH
            (sectionTypesMap b.uliftTensorHom) g.op (a • s) _ hsmul
        have e₁ : H.map g.op ((SheafOfModules.descent J
            (sectionTypesMap b₀.uliftTensorHom) hH
            (sectionTypesMap b.uliftTensorHom)).app U s) =
              b.uliftTensorHom.app (Opposite.op V) z :=
          descent_apply J (sectionTypesMap b₀.uliftTensorHom) hH
            (sectionTypesMap b.uliftTensorHom) g.op s z hz₁
        change H.map g.op _ = H.map g.op _
        refine e₀.trans ?_
        rw [map_smul (ConcreteCategory.hom (b.uliftTensorHom.app (Opposite.op V))), ← e₁]
        exact (PresheafOfModules.map_smul H g.op a _).symm }
  naturality g := ModuleCat.hom_ext (LinearMap.ext fun s ↦
    CategoryTheory.congr_fun
      ((SheafOfModules.descent J (sectionTypesMap b₀.uliftTensorHom) hH
        (sectionTypesMap b.uliftTensorHom)).naturality g) s)

/-- The descended morphism recovers the bilinear map on the image of the comparison. -/
public theorem BilinearMap.uliftDescend_app (b₀ : BilinearMap R F G T)
    [Presheaf.IsLocallyInjective J (sectionTypesMap b₀.uliftTensorHom)]
    [Presheaf.IsLocallySurjective J (sectionTypesMap b₀.uliftTensorHom)]
    (hH : Presheaf.IsSheaf J (sectionTypes H)) (b : BilinearMap R F G H)
    (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U) :
    (b₀.uliftDescend hH b).app U (b₀.app U x y) = b.app U x y := by
  have h : (sectionTypesMap b₀.uliftTensorHom ≫ SheafOfModules.descent J
      (sectionTypesMap b₀.uliftTensorHom) hH (sectionTypesMap b.uliftTensorHom)).app U =
      (sectionTypesMap b.uliftTensorHom).app U :=
    congrArg (fun k ↦ NatTrans.app k U) (SheafOfModules.descent_comp J
      (sectionTypesMap b₀.uliftTensorHom) hH (sectionTypesMap b.uliftTensorHom))
  exact (fun z ↦ CategoryTheory.congr_fun h z) (ULift.up (x ⊗ₜ y))

/-- **Stacks 06WN(2), formal half.**  A bilinear map of presheaves of modules whose associated
map out of the objectwise tensor product with raised sections is locally bijective exhibits its
target as the tensor product in the category of sheaves of modules for that topology: a
bilinear map into a sheaf of modules has a unique linear factorization through it.  The
sections of the two sources lie in independent universes `m` and `n`, and those of the target
in `max u m n`, where `u` is the universe of the coefficient rings. -/
public theorem existsUnique_hom_ulift (b₀ : BilinearMap R F G T)
    [Presheaf.IsLocallyInjective J (sectionTypesMap b₀.uliftTensorHom)]
    [Presheaf.IsLocallySurjective J (sectionTypesMap b₀.uliftTensorHom)]
    (hH : Presheaf.IsSheaf J (sectionTypes H)) (b : BilinearMap R F G H) :
    ∃! f : T ⟶ H, ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U),
      f.app U (b₀.app U x y) = b.app U x y :=
  ⟨b₀.uliftDescend hH b, b₀.uliftDescend_app hH b, fun _ hf ↦
    hom_ext_of_isLocallySurjective_ulift b₀ hH fun U x y ↦
      (hf U x y).trans (b₀.uliftDescend_app hH b U x y).symm⟩

/-- **Stacks 06WN(2), formal half.**  One comparison serves every finer topology: a bilinear
map whose associated map out of the objectwise tensor product with raised sections is locally
bijective for a topology `J` exhibits its target as the tensor product in the category of
sheaves of modules for *every* topology finer than `J`, because a sheaf for a finer topology is
a sheaf for `J`.  This is the formal content of the agreement, asserted by the source, of the
tensor products computed on the Zariski, étale and fppf sites. -/
public theorem existsUnique_hom_ulift_of_le {J K : GrothendieckTopology C} (hJK : J ≤ K)
    (b₀ : BilinearMap R F G T)
    (hinj : Presheaf.IsLocallyInjective J (sectionTypesMap b₀.uliftTensorHom))
    (hsurj : Presheaf.IsLocallySurjective J (sectionTypesMap b₀.uliftTensorHom))
    (hH : Presheaf.IsSheaf K (sectionTypes H)) (b : BilinearMap R F G H) :
    ∃! f : T ⟶ H, ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U),
      f.app U (b₀.app U x y) = b.app U x y := by
  have := hinj
  have := hsurj
  refine existsUnique_hom_ulift (J := J) b₀ ?_ b
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_of_le _ hJK ((isSheaf_iff_isSheaf_of_type K _).mp hH)

end Descent

section Sheafification

variable {J : GrothendieckTopology C} {Rsh : Sheaf J RingCat.{u}}
  (α : R ⋙ forget₂ CommRingCat RingCat ⟶ Rsh.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u m n}]
  [HasWeakSheafify J AddCommGrpCat.{max u m n}]

/-- The tensor product of sheaves of modules with sections in independent universes, obtained
by sheafifying the objectwise tensor product of the underlying presheaves of modules after
raising the universe of its sections to include that of the coefficient rings.  The two sources
have sections in independent universes `m` and `n`, and the result has sections in
`max u m n`, where `u` is the universe of the coefficient rings. -/
public noncomputable def tensorSheafBifunctorMixed :
    PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat) ⥤
        SheafOfModules.{max u m n} Rsh :=
  PresheafOfModules.tensorBifunctor R ⋙
    (Functor.whiskeringRight _ _ _).obj
      (PresheafOfModules.ulift.{u} ⋙ PresheafOfModules.sheafification α)

/-- The tensor product of sheaves of modules with sections in independent universes, evaluated
at `F` and `G`, is the sheafification of the objectwise tensor product of `F` and `G` with raised
sections. -/
@[simp] public theorem tensorSheafBifunctorMixed_obj_obj
    (F : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat))
    (G : PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat)) :
    ((tensorSheafBifunctorMixed α).obj F).obj G =
      (PresheafOfModules.sheafification α).obj ((tensorObj F G).uliftSections.{u}) := rfl

end Sheafification

end Stacks.Modules

end
