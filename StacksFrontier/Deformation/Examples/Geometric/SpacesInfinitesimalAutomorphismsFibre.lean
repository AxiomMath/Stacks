module

public import StacksFrontier.Deformation.Examples.Spaces
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.Cofibered.Over
public import StacksFrontier.Deformation.Terminal
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransport

/-!
# Infinitesimal automorphisms of the deformation category of an algebraic space are self-maps

Let `k` be a field and `X` an algebraic space over `k`, with deformation category `𝓓_X` of
[Stacks Project, Tag 0E3Z]: the category of flat families of algebraic spaces over objects of
`𝒞_Λ` lying over the family `(k, X)`.  This file connects the infinitesimal automorphism group
`Inf(𝓓_X)` of [Stacks Project, Tag 06JS] with honest self-maps of the total space of a
deformation over the dual numbers.

* `𝓓_X` is a predeformation category: `(k, X)` lies over the terminal object of `𝒞_Λ`, and the
  category of flat families is cofibred in groupoids ([Stacks Project, Tag 0E3Z]).
* **Every fibre automorphism is infinitesimal.**  The condition defining `Inf` is that an
  automorphism `a` commute with the canonical retraction `r` to the point `x₀` over the residue
  field.  On total spaces, `r` satisfies `x₀.special ≫ r = xε.special`, where `special` is the
  map from `X` given by the structure arrow to `(k, X)`, and `a` fixes `xε.special`; the map
  `x₀.special` is invertible, because `x₀` lies over the residue field, so `a ≫ r = r`.
* A fibre automorphism is determined by its self-map of the total space, and composition of
  automorphisms is composition of self-maps.

## Main definitions

* `Deformation.Examples.spaceFamilyOfPoint`, `spaceSpecialMap`: the total family of a point of
  `𝓓_X` and its special-fibre map `X ⟶ total space`.
* `Deformation.Examples.spaceFiberAutMap`: the self-map of the total space of an automorphism.
* `Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivAut`: `Inf(𝓓_X)` is the full
  automorphism group of the point in its fibre.

## Main results

* `Deformation.Examples.isPredeformationCategory_spaceDeformationProjection`.
* `Deformation.Examples.infinitesimalAutomorphisms_spaceDeformation_eq_top`.
* `Deformation.Examples.spaceFiberAutMap_mul`, `spaceFiberAutMap_injective`.

## References

* [Stacks Project, Tag 0E3Z](https://stacks.math.columbia.edu/tag/0E3Z)
* [Stacks Project, Tag 06JS](https://stacks.math.columbia.edu/tag/06JS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- **The deformation category of an algebraic space is a predeformation category**: the family
`(k, X)` lies over the terminal object `k` of `𝒞_Λ`, and the category of flat families of
algebraic spaces is cofibred in groupoids. -/
theorem isPredeformationCategory_spaceDeformationProjection :
    IsPredeformationCategory (spaceDeformationProjection B hΛ hSpec X hX toK) := by
  have ht : IsTerminal ((flatAlgebraicSpaceFamilyFunctor B hΛ hSpec).obj
      (spaceSpecialFiber B hΛ hSpec X hX toK)) := isTerminal_residueFieldBase
  have hs : IsTerminal (residueFieldObject.{u, u, u} Λ k) :=
    ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot _
      (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{u} k))
  refine ⟨isCofiberedInGroupoids_overForget
    (flatAlgebraicSpaceFamilyFunctor_isCofiberedInGroupoids B hΛ hSpec) _ ht, ?_⟩
  exact objectsOverFunctor_fiber_equiv_punit_of_isTerminal _
    (flatAlgebraicSpaceFamilyFunctor_isCofiberedInGroupoids B hΛ hSpec) _ ht _ hs

/-- The family underlying a point of the deformation category. -/
abbrev spaceFamilyOfPoint (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) :
    FlatAlgebraicSpaceFamily B hΛ hSpec :=
  y.left

/-- The special-fibre map `X ⟶ Y` of a point `(Y ⟶ (k, X))` of the deformation category: the
space component of its structure arrow. -/
abbrev spaceSpecialMap (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK)) : X ⟶ y.left.space :=
  y.hom.map

/-- The space component of a morphism of the deformation category is compatible with the
special-fibre maps. -/
theorem spaceSpecialMap_comp {y y' : Over (spaceSpecialFiber B hΛ hSpec X hX toK)}
    (f : y ⟶ y') :
    spaceSpecialMap B hΛ hSpec X hX toK y' ≫ f.left.map =
      spaceSpecialMap B hΛ hSpec X hX toK y :=
  congrArg (fun m : y.left ⟶ spaceSpecialFiber B hΛ hSpec X hX toK => m.map) (Over.w f)

/-- An arrow of the fibre over `A` from a point to itself acts as the identity on the base
object of the family. -/
theorem spaceFiberEnd_base_eq_id {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber A} (f : y ⟶ y) :
    f.val.left.base = 𝟙 y.1.left.base := by
  have := f.2
  rw [show f.val.left.base = eqToHom y.2 ≫ 𝟙 A ≫ eqToHom y.2.symm from
    IsHomLift.fac' (spaceDeformationProjection B hΛ hSpec X hX toK) (𝟙 A) f.val]
  simp

/-- The space component of an endomorphism of a point in its fibre commutes with the structure
morphism of the total space. -/
theorem spaceFiberEnd_map_comp_toBase {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber A} (f : y ⟶ y) :
    f.val.left.map ≫ y.1.left.toBase = y.1.left.toBase := by
  have h := f.val.left.cartesian.w
  rwa [spaceFiberEnd_base_eq_id, spaceBaseOverMap_id, CategoryTheory.Functor.map_id,
    Category.comp_id] at h

/-- A point of the deformation category over the residue-field object has an invertible
special-fibre map: its structure arrow lies over a morphism between two terminal objects of
`𝒞_Λ`, and the base change of an isomorphism is an isomorphism. -/
theorem isIso_spaceSpecialMap_of_residueFieldObject
    (x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      (residueFieldObject.{u, u, u} Λ k)) :
    IsIso (spaceSpecialMap B hΛ hSpec X hX toK x₀.1) := by
  have hs : IsTerminal (residueFieldObject.{u, u, u} Λ k) :=
    ArtinianLocalAlgCat.isTerminal_of_maximalIdeal_eq_bot _
      (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{u} k))
  have hx : IsTerminal x₀.1.left.base := by
    rwa [show x₀.1.left.base = residueFieldObject.{u, u, u} Λ k from x₀.2]
  have hb : IsIso x₀.1.hom.base := isIso_of_isTerminal hx isTerminal_residueFieldBase _
  have hm : IsIso (spaceBaseOverMap B hΛ hSpec x₀.1.hom.base) :=
    ⟨⟨spaceBaseOverMap B hΛ hSpec (inv x₀.1.hom.base), by
      rw [← spaceBaseOverMap_comp, IsIso.inv_hom_id, spaceBaseOverMap_id], by
      rw [← spaceBaseOverMap_comp, IsIso.hom_inv_id, spaceBaseOverMap_id]⟩⟩
  exact x₀.1.hom.cartesian.isIso_fst_of_isIso

/-- **Every automorphism of a point of the deformation category of an algebraic space in its
fibre is an infinitesimal automorphism.**  Membership means commuting with the canonical
retraction `r` to the chosen point `x₀` over the residue field.  On base objects both sides are
the base component of `r`, the automorphism acting as the identity there.  On total spaces,
`x₀.special ≫ r.map = xε.special` and the automorphism fixes `xε.special`, and `x₀.special` is
invertible, so it may be cancelled. -/
theorem infinitesimalAutomorphisms_spaceDeformation_eq_top
    (hp : IsCofiberedInGroupoids (spaceDeformationProjection B hΛ hSpec X hX toK))
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      (residueFieldObject.{u, u, u} Λ k)}
    {xε : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber Aε}
    (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift g i) :
    infinitesimalAutomorphisms hp g e hpair i hi = ⊤ := by
  have hx₀ := isIso_spaceSpecialMap_of_residueFieldObject B hΛ hSpec X hX toK x₀
  refine top_unique fun a _ => ?_
  rw [mem_infinitesimalAutomorphisms_iff]
  set r := (canonicalRetraction hp g e hpair.split i hi).1
  apply Over.OverMorphism.ext
  apply FlatAlgebraicSpaceFamily.Hom.ext
  · change a.asIso.hom.val.left.base ≫ r.left.base = r.left.base
    rw [spaceFiberEnd_base_eq_id, Category.id_comp]
  · change r.left.map ≫ a.asIso.hom.val.left.map = r.left.map
    refine (cancel_epi (spaceSpecialMap B hΛ hSpec X hX toK x₀.1)).mp ?_
    rw [← Category.assoc, spaceSpecialMap_comp B hΛ hSpec X hX toK r,
      spaceSpecialMap_comp B hΛ hSpec X hX toK a.asIso.hom.val]

/-- **`Inf(𝓓_X)` is the full automorphism group of the point in its fibre**, by
`Deformation.Examples.infinitesimalAutomorphisms_spaceDeformation_eq_top`. -/
def spaceInfinitesimalAutomorphismGroupMulEquivAut
    (hp : IsPredeformationCategory (spaceDeformationProjection B hΛ hSpec X hX toK))
    {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      (residueFieldObject.{u, u, u} Λ k)}
    {xε : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber Aε}
    (g : residueFieldObject.{u, u, u} Λ k ⟶ Aε) (e : Aε ⟶ residueFieldObject.{u, u, u} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift g i) :
    infinitesimalAutomorphismGroup hp g e hpair i hi ≃* Aut xε :=
  (MulEquiv.subgroupCongr
      (infinitesimalAutomorphisms_spaceDeformation_eq_top B hΛ hSpec X hX toK hp.cofibered
        g e hpair i hi)).trans
    (Subgroup.topEquiv (G := Aut xε))

/-! ### Fibre automorphisms as self-maps of the total space -/

/-- The self-map of the total space of a point induced by a fibre automorphism. -/
abbrev spaceFiberAutMap {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber A} (a : Aut y) :
    y.1.left.space ⟶ y.1.left.space :=
  a.asIso.hom.val.left.map

/-- The self-map of a fibre automorphism commutes with the structure morphism. -/
theorem spaceFiberAutMap_comp_toBase {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber A} (a : Aut y) :
    spaceFiberAutMap B hΛ hSpec X hX toK a ≫ y.1.left.toBase = y.1.left.toBase :=
  spaceFiberEnd_map_comp_toBase B hΛ hSpec X hX toK a.asIso.hom

/-- The self-map of a fibre automorphism fixes the special-fibre map. -/
theorem spaceSpecialMap_comp_spaceFiberAutMap {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber A} (a : Aut y) :
    spaceSpecialMap B hΛ hSpec X hX toK y.1 ≫ spaceFiberAutMap B hΛ hSpec X hX toK a =
      spaceSpecialMap B hΛ hSpec X hX toK y.1 :=
  spaceSpecialMap_comp B hΛ hSpec X hX toK a.asIso.hom.val

/-- **The group law of fibre automorphisms is composition of self-maps**, in the order of the
contravariance of the space component: `(a * b).map = a.map ≫ b.map`. -/
theorem spaceFiberAutMap_mul {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber A} (a b : Aut y) :
    spaceFiberAutMap B hΛ hSpec X hX toK (a * b) =
      spaceFiberAutMap B hΛ hSpec X hX toK a ≫ spaceFiberAutMap B hΛ hSpec X hX toK b :=
  rfl

/-- The identity automorphism has the identity self-map. -/
theorem spaceFiberAutMap_one {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber A} :
    spaceFiberAutMap B hΛ hSpec X hX toK (1 : Aut y) = 𝟙 _ :=
  rfl

/-- A fibre automorphism is determined by its self-map. -/
theorem spaceFiberAutMap_injective {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber A} :
    Function.Injective (spaceFiberAutMap B hΛ hSpec X hX toK (y := y)) := fun a b h =>
  Aut.ext <| Iso.ext <| Functor.Fiber.hom_ext <| Over.OverMorphism.ext <|
    FlatAlgebraicSpaceFamily.Hom.ext
    ((spaceFiberEnd_base_eq_id B hΛ hSpec X hX toK a.asIso.hom).trans
      (spaceFiberEnd_base_eq_id B hΛ hSpec X hX toK b.asIso.hom).symm) h

end Deformation.Examples

end
