module

public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf

/-!
# Every 1-morphism `𝒞/U ⥤ 𝒴` over `𝒞` is `f ↦ f^* y` for its value `y` at `id_U`

Let `𝒴` be a category fibred in groupoids over `𝒞`, fix a choice of pullbacks `c` for it, an
object `U` of `𝒞` and a 1-morphism `G : 𝒞/U ⥤ 𝒴` over `𝒞`. The 2-Yoneda lemma (Stacks 004B) says
that `G` is determined up to 2-isomorphism by the object `y := G(id_U)` of the fibre `𝒴_U`. This
file produces that 2-isomorphism in the explicit form the criterion of Stacks 02Y9 needs: a
natural isomorphism

`G ≅ CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor c y`

all of whose components are vertical, comparing `G` with the 1-morphism `(f : V ⟶ U) ↦ f^* y`
built from the chosen pullbacks.

The comparison is constructed directly rather than extracted from the 2-Yoneda equivalence: an
object `f : V ⟶ U` of `𝒞/U` admits a canonical morphism `f ⟶ id_U` to the terminal object, whose
image `G(f) ⟶ y` lies over `f`; the chosen pullback `f^* y ⟶ y` also lies over `f` and is
strongly cartesian, so the first factors through the second by a unique morphism over `id_V`.
That morphism is an isomorphism because `𝒴` is fibred in groupoids, and its naturality is again
the uniqueness of such a factorisation.

## Main definitions

* `CategoryTheory.Functor.ChoiceOfPullbacks.sliceObj`: the value `G(id_U)` read as an object of
  the fibre `𝒴_U`.
* `CategoryTheory.Functor.ChoiceOfPullbacks.sliceComparison`: the comparison morphism
  `G(f) ⟶ f^* y`.

## Main results

* `CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctorIso`: the natural isomorphism
  `G ≅ sliceFunctor c (G(id_U))`.
* `CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctorIso_hom_app_isHomLift`: its components
  are vertical, so it is a 2-morphism in the 2-category of categories over `𝒞`.
-/

@[expose] public section

namespace CategoryTheory.Functor.ChoiceOfPullbacks

universe v₁ v₃ u₁ u₃

attribute [local implicit_reducible] Functor.Fiber Functor.ChoiceOfPullbacks.sliceFunctor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒴 : Type u₃} [Category.{v₃} 𝒴] {p𝒴 : 𝒴 ⥤ 𝒞}
  (c : p𝒴.ChoiceOfPullbacks) {U : 𝒞} (G : Over U ⥤ 𝒴) (hG : G ⋙ p𝒴 = Over.forget U)

/-- The canonical morphism from an object `f : V ⟶ U` of `𝒞/U` to the terminal object `id_U`,
namely `f` itself read as a morphism `V ⟶ U` over `U`. -/
def toTerminal (f : Over U) : f ⟶ Over.mk (𝟙 U) :=
  Over.homMk f.hom (by simp)

/-- The canonical morphism to the terminal object lies over the structure morphism of its
source. -/
instance toTerminal_isHomLift (f : Over U) : (Over.forget U).IsHomLift f.hom (toTerminal f) :=
  IsHomLift.of_fac' (Over.forget U) f.hom (toTerminal f) rfl rfl (by simp [toTerminal])

/-- The value `G(id_U)` of a 1-morphism `G : 𝒞/U ⥤ 𝒴` over `𝒞` at the terminal object of `𝒞/U`,
read as an object of the fibre `𝒴_U`. This is the object of `𝒴_U` to which the 2-Yoneda lemma
(Stacks 004B) attaches `G`. -/
def sliceObj : p𝒴.Fiber U :=
  ⟨G.obj (Over.mk (𝟙 U)), Functor.congr_obj hG (Over.mk (𝟙 U))⟩

attribute [local implicit_reducible] sliceObj

include hG in
/-- The image under `G` of a morphism of `𝒞/U` lies over its underlying morphism of `𝒞`. -/
lemma map_isHomLift {f' f : Over U} (h : f' ⟶ f) : p𝒴.IsHomLift h.left (G.map h) :=
  have : (Over.forget U).IsHomLift h.left h :=
    IsHomLift.of_fac' (Over.forget U) h.left h rfl rfl (by simp)
  Functor.isHomLift_map_of_comp_eq hG h.left h

include hG in
/-- The image under `G` of the canonical morphism `f ⟶ id_U` lies over the structure morphism of
`f`, since `G` is a 1-morphism over `𝒞`. -/
lemma map_toTerminal_isHomLift (f : Over U) :
    p𝒴.IsHomLift f.hom (G.map (toTerminal f)) :=
  Functor.isHomLift_map_of_comp_eq hG f.hom (toTerminal f)

/-- The comparison morphism `G(f) ⟶ f^* y` for `y = G(id_U)`: the unique morphism over `id_V`
through which `G(f) ⟶ y` factors past the chosen cartesian lift `f^* y ⟶ y`. -/
noncomputable def sliceComparison (f : Over U) :
    G.obj f ⟶ (c.obj f.hom (sliceObj G hG)).1 :=
  have := map_toTerminal_isHomLift G hG f
  IsStronglyCartesian.map p𝒴 f.hom (c.map f.hom (sliceObj G hG))
    (Category.id_comp f.hom).symm (G.map (toTerminal f))

/-- The defining factorisation of the comparison morphism. -/
@[reassoc]
lemma sliceComparison_fac (f : Over U) :
    sliceComparison c G hG f ≫ c.map f.hom (sliceObj G hG) = G.map (toTerminal f) :=
  have := map_toTerminal_isHomLift G hG f
  IsStronglyCartesian.fac p𝒴 f.hom (c.map f.hom (sliceObj G hG))
    (Category.id_comp f.hom).symm (G.map (toTerminal f))

/-- The comparison morphism is vertical. -/
instance sliceComparison_isHomLift (f : Over U) :
    p𝒴.IsHomLift (𝟙 f.left) (sliceComparison c G hG f) :=
  have := map_toTerminal_isHomLift G hG f
  IsStronglyCartesian.map_isHomLift p𝒴 f.hom (c.map f.hom (sliceObj G hG))
    (Category.id_comp f.hom).symm (G.map (toTerminal f))

/-- The comparison morphism is an isomorphism: it is a morphism of a category fibred in groupoids
lying over an identity. -/
lemma sliceComparison_isIso (h𝒴 : p𝒴.IsFiberedInGroupoids) (f : Over U) :
    IsIso (sliceComparison c G hG f) :=
  have := h𝒴.isStronglyCartesian_homLift (𝟙 f.left) (sliceComparison c G hG f)
  IsStronglyCartesian.isIso_of_base_isIso p𝒴 (𝟙 f.left) (sliceComparison c G hG f)

/-- A morphism `G(f') ⟶ f^* y` lying over `h.left`, for `h : f' ⟶ f`, is determined by its
composite with the chosen cartesian lift `f^* y ⟶ y`. -/
lemma hom_ext_of_fac {f' f : Over U} (h : f' ⟶ f)
    (ψ₁ ψ₂ : G.obj f' ⟶ (c.obj f.hom (sliceObj G hG)).1)
    (hψ₁ : p𝒴.IsHomLift h.left ψ₁) (hψ₂ : p𝒴.IsHomLift h.left ψ₂)
    (h₁ : ψ₁ ≫ c.map f.hom (sliceObj G hG) = G.map (toTerminal f'))
    (h₂ : ψ₂ ≫ c.map f.hom (sliceObj G hG) = G.map (toTerminal f')) : ψ₁ = ψ₂ :=
  have := hψ₁
  have := hψ₂
  IsStronglyCartesian.ext p𝒴 f.hom (c.map f.hom (sliceObj G hG)) h.left (h₁.trans h₂.symm)

/-- The canonical morphisms to the terminal object are compatible with every morphism of `𝒞/U`. -/
@[simp]
lemma comp_toTerminal {f' f : Over U} (h : f' ⟶ f) : h ≫ toTerminal f = toTerminal f' :=
  Over.OverMorphism.ext (by simp [toTerminal])

include hG in
/-- The comparison morphisms are natural in the object of `𝒞/U`: both `G.map h ≫ (comparison at
`f`)` and `(comparison at `f'`) ≫ f^*(h)` lie over `h.left` and factor the same morphism
`G(f') ⟶ y` through the chosen cartesian lift `f^* y ⟶ y`. -/
lemma sliceComparison_naturality {f' f : Over U} (h : f' ⟶ f) :
    G.map h ≫ sliceComparison c G hG f
      = sliceComparison c G hG f' ≫ (c.sliceFunctor (sliceObj G hG)).map h := by
  have := map_isHomLift G hG h
  refine hom_ext_of_fac c G hG h _ _
    (IsHomLift.comp_lift_id_right p𝒴 h.left (G.map h) (sliceComparison c G hG f))
    (IsHomLift.comp_lift_id_left p𝒴 h.left ((c.sliceFunctor (sliceObj G hG)).map h)
      (sliceComparison c G hG f')) ?_ ?_
  · rw [Category.assoc, sliceComparison_fac, ← G.map_comp, comp_toTerminal]
  · rw [Category.assoc, sliceFunctor_map_fac, sliceComparison_fac]

include hG in
/-- **The 2-Yoneda comparison (Stacks 004B) in the form Stacks 02Y9 uses it.** A 1-morphism
`G : 𝒞/U ⥤ 𝒴` over `𝒞` into a category fibred in groupoids is naturally isomorphic to the
1-morphism `(f : V ⟶ U) ↦ f^* y` built from the chosen pullbacks of `y = G(id_U)`. -/
noncomputable def sliceFunctorIso (h𝒴 : p𝒴.IsFiberedInGroupoids) :
    G ≅ c.sliceFunctor (sliceObj G hG) :=
  NatIso.ofComponents
    (fun f => have := sliceComparison_isIso c G hG h𝒴 f; asIso (sliceComparison c G hG f))
    fun h => by simpa using sliceComparison_naturality c G hG h

/-- The component of the 2-Yoneda comparison isomorphism at `f` is the comparison morphism. -/
@[simp]
lemma sliceFunctorIso_hom_app (h𝒴 : p𝒴.IsFiberedInGroupoids) (f : Over U) :
    (sliceFunctorIso c G hG h𝒴).hom.app f = sliceComparison c G hG f := rfl

include hG in
/-- Every component of the 2-Yoneda comparison isomorphism is vertical, so it is a 2-morphism in
the 2-category of categories over `𝒞`. -/
lemma sliceFunctorIso_hom_app_isHomLift (h𝒴 : p𝒴.IsFiberedInGroupoids) (f : Over U) :
    p𝒴.IsHomLift (𝟙 f.left) ((sliceFunctorIso c G hG h𝒴).hom.app f) :=
  sliceComparison_isHomLift c G hG f

end CategoryTheory.Functor.ChoiceOfPullbacks
