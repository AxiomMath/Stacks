module

public import StacksFrontier.Deformation.Applications.TwoFibreProductBoundaryLinear
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.SpecialFibreThin

/-!
# The exact sequence of `k`-vector spaces of a self 2-fibre product (Stacks 06L6, part (2))

Let `U : 𝒞_Λ → Sets` be a deformation functor, `ℱ` a deformation category and `f : U → ℱ` a
`1`-morphism over `𝒞_Λ`. Part (1) of Tag 06L6 says that `𝒲 = U ×_{f, ℱ, f} U` is again a
deformation functor. Part (2) adds the exact sequence of `k`-vector spaces

`0 → Inf(ℱ) → T𝒲 → TU ⊕ TU`.

Exactness at `T𝒲` is part (2) of Tag 06L5 for the two legs, read for the `k`-linear boundary
map `Deformation.boundaryLinearMap` rather than for its underlying map of sets. Exactness at
`Inf(ℱ)` — injectivity of the boundary map — is what the self 2-fibre product adds: the fibres
of the category of elements of a set-valued functor are thin, so an isomorphism between two
quadruples `(k[M], y'₀, y'₀, c' ∘ α ∘ b')` has both of its components the identity and the
comparison square then reads `α = α'`.

## Main results

* `Deformation.eq_of_tangentClassAt_boundaryObject_eq`: the boundary map is injective when the
  fibres of the two legs over `k[M]` are thin.
* `Deformation.injective_boundaryLinearMap`: the same for the `k`-linear boundary map.
* `Deformation.exact_boundaryLinearMap_tangentProjPair`: **part (2) of Tag 06L5, exactness at
  `T𝒲`**, for the `k`-linear boundary map. This is the vector-space form of the assertion, and
  the one that carries the tag; the set-level
  `Deformation.exact_boundaryFun_tangentProjPair` is the auxiliary form.
* `Deformation.isDeformationCategory_comp_of_isDeformationFunctor`: the category of elements of
  a deformation functor, presented through a `1`-morphism over `𝒞_Λ`, is a deformation
  category.
* `Deformation.exact_boundaryLinearMap_tangentProjPair_self`: **Tag 06L6, part (2)**.

## Implementation notes

Exactness at `T𝒲` is obtained from the two halves of Tag 06L5 part (2) directly rather than by
specialising `Deformation.exact_boundaryFun_tangentProjPair`: that statement is about the map of
sets defined on `Deformation.infinitesimalAutomorphismsAlongSplitPair`, and carries both a
splitting of `k ⟶ k[M]` and the hypothesis that the basepoint lies over the residue field on the
nose. Neither is needed once the boundary map is read on the `k`-linear lift, because
`Deformation.ker_transportAutHom_squareZeroUnderRed_eq_top` identifies the infinitesimal
automorphisms indexing that lift with *all* automorphisms of the pushforward, so the image of
the linear map is already the image of the map of sets.

## References

* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
* [Stacks Project, Tag 06L6](https://stacks.math.columbia.edu/tag/06L6)
-/

@[expose] public section

namespace Deformation

/-! ### Comparison isomorphisms over thin leg fibres -/

section Comparison
open CategoryTheory CategoryTheory.Functor
universe vC uC vX uX vY uY vS uS

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y] {S : Type uS} [Category.{vS} S]
  {pX : X ⥤ C} {pY : Y ⥤ C} {pS : S ⥤ C} {Φ : X ⥤ S} {Ψ : Y ⥤ S} {U : C}

/-- **Over thin leg fibres the comparison isomorphism of a quadruple is an invariant of its
isomorphism class.** Two objects of the `2`-fibre product with the same base and the same two
components are isomorphic in the fibre over `U` only if their comparison isomorphisms agree:
the two components of an isomorphism between them lie over `𝟙 U` in the fibres of the two legs,
a thin fibre forces each of them to be an identity, and the comparison square then equates the
two comparison isomorphisms. -/
public theorem iso_hom_eq_of_isThin
    (hX : Quiver.IsThin (pX.Fiber U)) (hY : Quiver.IsThin (pY.Fiber U))
    {x : X} {y : Y} (hx : pX.obj x = U) (hy : pY.obj y = U) {ι ι' : Φ.obj x ≅ Ψ.obj y}
    (hι : pS.IsHomLift (𝟙 U) ι.hom) (hι' : pS.IsHomLift (𝟙 U) ι'.hom)
    (φ : (⟨U, x, y, hx, hy, ι, hι⟩ : TwoFibreProductOver pX pY pS Φ Ψ) ⟶
      ⟨U, x, y, hx, hy, ι', hι'⟩)
    (hφ : (TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).IsHomLift (𝟙 U) φ) :
    ι.hom = ι'.hom := by
  have hfa : pX.IsHomLift (𝟙 U) φ.a := TwoFibreProductOver.isHomLift_a φ (𝟙 U) hφ
  have hgb : pY.IsHomLift (𝟙 U) φ.b := TwoFibreProductOver.isHomLift_b φ (𝟙 U) hφ
  have hXsub := hX (Functor.Fiber.mk hx) (Functor.Fiber.mk hx)
  have hYsub := hY (Functor.Fiber.mk hy) (Functor.Fiber.mk hy)
  have hane : (⟨φ.a, hfa⟩ : Functor.Fiber.mk hx ⟶ Functor.Fiber.mk hx) =
      𝟙 (Functor.Fiber.mk hx) := Subsingleton.elim _ _
  have hbne : (⟨φ.b, hgb⟩ : Functor.Fiber.mk hy ⟶ Functor.Fiber.mk hy) =
      𝟙 (Functor.Fiber.mk hy) := Subsingleton.elim _ _
  have ha : φ.a = 𝟙 x :=
    congrArg (fun t : Functor.Fiber.mk hx ⟶ Functor.Fiber.mk hx => t.1) hane
  have hb : φ.b = 𝟙 y :=
    congrArg (fun t : Functor.Fiber.mk hy ⟶ Functor.Fiber.mk hy => t.1) hbne
  have hw : Φ.map φ.a ≫ ι'.hom = ι.hom ≫ Ψ.map φ.b := φ.w
  rw [ha, hb, Φ.map_id, Ψ.map_id, Category.id_comp, Category.comp_id] at hw
  exact hw.symm

end Comparison

/-! ### Injectivity of the boundary map over thin leg fibres -/

section Injective
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G] {F : Type u₃} [Category.{v₃} F]

attribute [local implicit_reducible] squareZeroCrossUnder

/-- **The boundary map is injective over thin leg fibres.** Two quadruples
`(k[M], y'₀, z'₀, c' ∘ α ∘ b')` and `(k[M], y'₀, z'₀, c' ∘ α' ∘ b')` have the same class in `T𝒲`
exactly when they are isomorphic in the fibre of `𝒲` over `k[M]`; such an isomorphism has two
components, lying over the identity in the fibres of the two legs, and a thin fibre forces each
to be an identity. The comparison square of the isomorphism then reads
`c' ∘ α ∘ b' = c' ∘ α' ∘ b'`, and `b'` and `c'` are isomorphisms. -/
public theorem eq_of_tangentClassAt_boundaryObject_eq
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k)
    (hXthin : Quiver.IsThin
      ((f ⋙ pF).Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)))
    (hYthin : Quiver.IsThin
      ((g ⋙ pF).Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)))
    {α α' : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))}
    (h : tangentClassAt.{u, v, w} (productBased.{u, v, w} pF f g)
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M
          ⟨boundaryObject.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered M α, rfl⟩ =
        tangentClassAt.{u, v, w} (productBased.{u, v, w} pF f g)
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M
          ⟨boundaryObject.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered M α',
            rfl⟩) :
    α = α' := by
  obtain ⟨e⟩ := (tangentClassAt_eq_iff.{u, v, w} (productBased.{u, v, w} pF f g)
    (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M _ _).mp h
  have hcomp : (boundaryCompareFst.{u, v, w} f PH PF hF.predeformation.cofibered M).inv ≫
        Functor.Fiber.fiberInclusion.map α.asIso.hom ≫
          (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hF.predeformation.cofibered M).hom =
      (boundaryCompareFst.{u, v, w} f PH PF hF.predeformation.cofibered M).inv ≫
        Functor.Fiber.fiberInclusion.map α'.asIso.hom ≫
          (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hF.predeformation.cofibered M).hom :=
    iso_hom_eq_of_isThin hXthin hYthin
      (PH.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M)).2
      (PG.obj (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj z₀) M)).2 _ _ e.hom.1 e.hom.2
  refine Aut.ext (Iso.ext (Functor.Fiber.hom_ext ?_))
  exact (cancel_mono
    (boundaryCompareSnd.{u, v, w} f g hzy hcmp PG PF hF.predeformation.cofibered M).hom).mp
      ((cancel_epi
        (boundaryCompareFst.{u, v, w} f PH PF hF.predeformation.cofibered M).inv).mp hcomp)

end Injective

/-! ### Transport of automorphisms along an isomorphism of coordinate objects -/

section Transport
open CategoryTheory
universe v₁ v₂ u₁ u₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C] {p : F ⥤ C} {x : F}

/-- Transport of automorphisms along the two directions of an isomorphism of objects under
`p.obj x` are mutually inverse. -/
public theorem ChosenPushforwardsAt.transportAut_inv_transportAut_hom
    (P : ChosenPushforwardsAt p x) {A B : Under (p.obj x)} (e : A ≅ B) (a : Aut (P.obj A)) :
    P.transportAut e.inv (P.transportAut e.hom a) = a := by
  rw [← P.transportAut_comp, e.hom_inv_id, P.transportAut_id]

/-- Transport of automorphisms along the two directions of an isomorphism of objects under
`p.obj x` are mutually inverse, in the other order. -/
public theorem ChosenPushforwardsAt.transportAut_hom_transportAut_inv
    (P : ChosenPushforwardsAt p x) {A B : Under (p.obj x)} (e : A ≅ B) (a : Aut (P.obj B)) :
    P.transportAut e.hom (P.transportAut e.inv a) = a := by
  rw [← P.transportAut_comp, e.inv_hom_id, P.transportAut_id]

end Transport

/-! ### The exact sequence of `k`-vector spaces -/

section Exact
open CategoryTheory CategoryTheory.Functor
universe z u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G] {F : Type u₃} [Category.{v₃} F]

attribute [local implicit_reducible] squareZeroCrossUnder

/-- Transporting along an equality of types and back is the identity. -/
private theorem cast_symm_cast {α β : Type z} (h : α = β) (a : α) : cast h.symm (cast h a) = a := by
  cases h
  rfl

/-- Transporting along the reverse of an equality of types and back is the identity. -/
private theorem cast_cast_symm {α β : Type z} (h : α = β) (b : β) : cast h (cast h.symm b) = b := by
  cases h
  rfl

/-- The boundary map is the class in `T𝒲` of the quadruple it produces. -/
public theorem boundaryFun_eq_tangentClassAt
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k)
    (α : Aut (PF.obj (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj y₀) M))) :
    boundaryFun.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation
        (tangentConditionS2.{u, v, w}
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)) M α =
      tangentClassAt.{u, v, w} (productBased.{u, v, w} pF f g)
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M
        ⟨boundaryObject.{u, v, w} f g hzy hcmp PH PG PF hF.predeformation.cofibered M α, rfl⟩ :=
  rfl

/-- **The `k`-linear boundary map is injective over thin leg fibres.** This is exactness of
`0 → Inf(ℱ) → T𝒲` at `Inf(ℱ)`. The value of the linear lift is carried to an automorphism of the
pushforward to the re-based square-zero extension by a transport along an isomorphism, which is
invertible, and the boundary map is injective on those automorphisms. -/
public theorem injective_boundaryLinearMap
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k)
    (hXthin : Quiver.IsThin
      ((f ⋙ pF).Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)))
    (hYthin : Quiver.IsThin
      ((g ⋙ pF).Fiber ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))) :
    Function.Injective
      (boundaryLinearMap.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF M) := by
  intro y y' hyy
  rw [boundaryLinearMap_apply.{u, v, w}, boundaryLinearMap_apply.{u, v, w},
    boundaryFun_eq_tangentClassAt.{u, v, w} pF f g hH hG hF,
    boundaryFun_eq_tangentClassAt.{u, v, w} pF f g hH hG hF] at hyy
  have hcross := eq_of_tangentClassAt_boundaryObject_eq.{u, v, w} pF f g hH hG hF hzy hcmp
    PH PG PF M hXthin hYthin hyy
  have key : ∀ z, PF.transportAut (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).inv
        (crossInfinitesimalAut.{u, v, w} f PF M
          (cast (infinitesimalAutomorphismLinearLift_carrier PF hF.satisfiesRS M) z)) =
      (cast (infinitesimalAutomorphismLinearLift_carrier PF hF.satisfiesRS M) z).1 := fun z =>
    PF.transportAut_inv_transportAut_hom
      (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M) _
  have hval : (cast (infinitesimalAutomorphismLinearLift_carrier PF hF.satisfiesRS M) y).1 =
      (cast (infinitesimalAutomorphismLinearLift_carrier PF hF.satisfiesRS M) y').1 := by
    rw [← key y, ← key y', hcross]
  exact (cast_inj _).1 (Subtype.ext hval)

/-- **Stacks Project, Tag 06L5, part (2), for the `k`-linear boundary map: exactness at `T𝒲`.**
The kernel of `c : T𝒲 → Tℋ ⊕ T𝒢` is the image of the `k`-linear boundary map
`δ : Inf(ℱ) → T𝒲`.

That the composite vanishes is `Deformation.tangentProjPair_boundaryFun_eq_zero`, which holds for
every automorphism of `x'₀`. Conversely an element of the kernel is the class of a quadruple
`(k[M], y'₀, z'₀, c' ∘ α ∘ b')` by `Deformation.exists_aut_boundaryObject_tangentClassAt_eq`, and
that `α` is in the image of the linear lift because
`Deformation.ker_transportAutHom_squareZeroUnderRed_eq_top` makes the lift's value *all* of the
automorphisms of the pushforward, transport along
`Deformation.squareZeroCrossUnderIso` matching the two normalizations of the square-zero
extension.

This is the statement of part (2) at `T𝒲`: both of its maps are `k`-linear maps of the vector
spaces of Tag 06IH, and it carries neither the splitting of `k ⟶ k[M]` nor the hypothesis that
the basepoint lies over the residue field that the set-level
`Deformation.exact_boundaryFun_tangentProjPair` needs. -/
@[stacks 06L5 "part (2), exactness at `T𝒲` of the six-term exact sequence, for the `k`-linear \
boundary map `Inf(ℱ) → T𝒲` and the map `T𝒲 → Tℋ ⊕ T𝒢`"]
public theorem exact_boundaryLinearMap_tangentProjPair
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {y₀ : H} {z₀ : G} (hzy : (g ⋙ pF).obj z₀ = (f ⋙ pF).obj y₀)
    {cmp : f.obj y₀ ≅ g.obj z₀}
    (hcmp : pF.IsHomLift (𝟙 ((f ⋙ pF).obj y₀)) cmp.hom)
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PG : ChosenPushforwardsAt (g ⋙ pF) z₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k) :
    Function.Exact (boundaryLinearMap.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF M)
      (tangentProjPair.{u, v, w} pF f g hH hG hF M) := by
  intro t
  constructor
  · intro ht
    obtain ⟨W, hW⟩ := tangentClassAt_surjective.{u, v, w} (productBased.{u, v, w} pF f g)
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF) M t
    subst hW
    obtain ⟨α, hα⟩ := exists_aut_boundaryObject_tangentClassAt_eq.{u, v, w}
      pF f g hH hG hF hzy hcmp PH PG PF M W ht
    have hker := ker_transportAutHom_squareZeroUnderRed_eq_top.{u, v, w}
      hF.predeformation.cofibered PF (isThin_specialFiber.{u, v, w} hF.predeformation) M
    obtain ⟨a, ha⟩ :
        ∃ a : infinitesimalAutomorphismKernel PF (squareZeroUnderRed pF (f.obj y₀) M),
          crossInfinitesimalAut.{u, v, w} f PF M a = α := by
      refine ⟨⟨PF.transportAut
        (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).inv α, ?_⟩, ?_⟩
      · rw [hker]
        exact Subgroup.mem_top _
      · exact PF.transportAut_hom_transportAut_inv
          (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M) α
    refine ⟨cast (infinitesimalAutomorphismLinearLift_carrier PF hF.satisfiesRS M).symm a, ?_⟩
    rw [boundaryLinearMap_apply.{u, v, w}, cast_cast_symm, ha,
      boundaryFun_eq_tangentClassAt.{u, v, w} pF f g hH hG hF]
    exact hα
  · rintro ⟨y, rfl⟩
    rw [boundaryLinearMap_apply.{u, v, w}]
    exact tangentProjPair_boundaryFun_eq_zero.{u, v, w} pF f g hH hG hF hzy hcmp PH PG PF M _

end Exact

/-! ### Tag 06L6, part (2): the self 2-fibre product of a deformation functor -/

section SelfFibreProduct
open CategoryTheory CategoryTheory.Functor
universe u v w t u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₃} [Category.{v₃} F]

/-- The category of elements of a deformation functor, presented through a `1`-morphism over
`𝒞_Λ`, is a deformation category. -/
public theorem isDeformationCategory_comp_of_isDeformationFunctor
    (U : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t)
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : U.Elements ⥤ F)
    (hf : f ⋙ pF = Functor.Elements.π U) (hU : IsDeformationFunctor.{u, v, w} U) :
    IsDeformationCategory.{u, v, w} (f ⋙ pF) := by
  rw [hf]
  exact (isDeformationCategory_iff U).mpr hU

/-- The fibres of a `1`-morphism presenting a set-valued functor over `𝒞_Λ` are thin: they are
the fibres of the functor's category of elements, where a morphism is determined by the morphism
of `𝒞_Λ` it lies over. This is the source's `Inf(U) = (0)`. -/
public theorem isThin_fiber_comp_elementsProjection
    (U : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t)
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : U.Elements ⥤ F)
    (hf : f ⋙ pF = Functor.Elements.π U) (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) :
    Quiver.IsThin ((f ⋙ pF).Fiber A) := by
  rw [hf]
  exact elementsFiber_isThin U A

/-- The `k`-linear boundary map `δ : Inf(ℱ) → T𝒲` of the self `2`-fibre product
`𝒲 = U ×_{f, ℱ, f} U` at a basepoint `y₀`, taken with the identity comparison. -/
public noncomputable abbrev selfBoundaryLinearMap
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (U : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t) (f : U.Elements ⥤ F)
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF) {y₀ : U.Elements}
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀)
    (PF : ChosenPushforwardsAt pF (f.obj y₀)) (M : FGModuleCat.{max v w} k) :=
  boundaryLinearMap.{u, v, w} pF f f hH hH hF (z₀ := y₀) (cmp := Iso.refl (f.obj y₀)) rfl
    (CategoryTheory.IsHomLift.id rfl) PH PH PF M

/-- **Stacks Project, Tag 06L6, part (2).** Let `U : 𝒞_Λ → Sets` be a deformation functor, `ℱ` a
deformation category and `f : U → ℱ` a `1`-morphism of categories cofibered in groupoids over
`𝒞_Λ`. Then the tangent space of `𝒲 = U ×_{f, ℱ, f} U` fits into an exact sequence of
`k`-vector spaces

`0 → Inf(ℱ) → T𝒲 → TU ⊕ TU`,

where the first map is the `k`-linear boundary map `δ` of the six-term sequence and the second
is the pair of the maps induced by the two projections. Exactness at `Inf(ℱ)` is injectivity of
`δ` and exactness at `T𝒲` is the kernel-equals-image statement; both maps are `k`-linear, and
the three terms are the `k`-vector spaces of Tag 06IH, taken at an arbitrary coordinate module.

Exactness at `T𝒲` is part (2) of Tag 06L5 for the two legs
(`Deformation.exact_boundaryLinearMap_tangentProjPair`). Exactness at `Inf(ℱ)` is what the self
`2`-fibre product adds, and it is the source's `Inf(U) = (0)`: the fibres of the category of
elements of a set-valued functor are thin
(`Deformation.isThin_fiber_comp_elementsProjection`), so an isomorphism between two quadruples
`(k[M], y'₀, y'₀, c' ∘ α ∘ b')` has both components the identity and its comparison square reads
`α = α'`. -/
@[stacks 06L6 "part (2), the exact sequence of k-vector spaces 0 → Inf(ℱ) → T(U ×_{f,ℱ,f} U) \
→ TU ⊕ TU"]
public theorem exact_selfBoundaryLinearMap_tangentProjPair
    (U : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t)
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : U.Elements ⥤ F)
    (hf : f ⋙ pF = Functor.Elements.π U) (hU : IsDeformationFunctor.{u, v, w} U)
    (hF : IsDeformationCategory.{u, v, w} pF) {y₀ : U.Elements}
    (PH : ChosenPushforwardsAt (f ⋙ pF) y₀) (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (M : FGModuleCat.{max v w} k) :
    Function.Injective (selfBoundaryLinearMap.{u, v, w} pF U f
        (isDeformationCategory_comp_of_isDeformationFunctor.{u, v, w} U pF f hf hU) hF PH PF M) ∧
      Function.Exact
        (selfBoundaryLinearMap.{u, v, w} pF U f
          (isDeformationCategory_comp_of_isDeformationFunctor.{u, v, w} U pF f hf hU) hF PH PF M)
        (tangentProjPair.{u, v, w} pF f f
          (isDeformationCategory_comp_of_isDeformationFunctor.{u, v, w} U pF f hf hU)
          (isDeformationCategory_comp_of_isDeformationFunctor.{u, v, w} U pF f hf hU) hF M) :=
  ⟨injective_boundaryLinearMap.{u, v, w} pF f f
      (isDeformationCategory_comp_of_isDeformationFunctor.{u, v, w} U pF f hf hU)
      (isDeformationCategory_comp_of_isDeformationFunctor.{u, v, w} U pF f hf hU) hF
      (z₀ := y₀) (cmp := Iso.refl (f.obj y₀)) rfl (CategoryTheory.IsHomLift.id rfl) PH PH PF M
      (isThin_fiber_comp_elementsProjection.{u, v, w} U pF f hf _)
      (isThin_fiber_comp_elementsProjection.{u, v, w} U pF f hf _),
    exact_boundaryLinearMap_tangentProjPair.{u, v, w} pF f f
      (isDeformationCategory_comp_of_isDeformationFunctor.{u, v, w} U pF f hf hU)
      (isDeformationCategory_comp_of_isDeformationFunctor.{u, v, w} U pF f hf hU) hF
      (z₀ := y₀) (cmp := Iso.refl (f.obj y₀)) rfl (CategoryTheory.IsHomLift.id rfl)
      PH PH PF M⟩

end SelfFibreProduct

end Deformation

end
