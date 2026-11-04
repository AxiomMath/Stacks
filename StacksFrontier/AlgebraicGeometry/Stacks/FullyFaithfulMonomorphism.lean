module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise

/-!
# A fully faithful 1-morphism is a monomorphism (Stacks 04ZZ, (2) ⟹ (1))

Let `S` be a scheme contained in a big fppf site and let `j : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over `(Sch/S)_fppf`. **Stacks 04ZZ** asserts, for algebraic
stacks, the equivalence of: (1) `j` is a monomorphism; (2) `j` is fully faithful; (3) the
diagonal of `j` is an equivalence; (4) a flat finitely presented surjective base change of `j`
is a monomorphism of algebraic spaces.

The implication (1) ⟹ (2) is
`AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_mono_representingMaps` in
`StacksFrontier/AlgebraicGeometry/Stacks/MonomorphismFullyFaithful.lean`. This file proves the
converse (2) ⟹ (1) for the monomorphy half of the conclusion: if `j` is fully faithful then
every algebraic space representing a base change of `j` along a scheme-valued point of `𝒴` has
monomorphic structural morphism. The source's argument is that full faithfulness leaves at most
one pair `(x, α)` with `x : T ⟶ 𝒳` and `α : j ∘ x ⟶ y` up to unique isomorphism, so the fibres
of `T ×_𝒴 𝒳` over `(Sch/T)_fppf` are connected and the representing space takes subsingleton
values.

## Main results

* `CategoryTheory.TwoFibreProductOver.nonempty_fst_fiber_hom_of_full_fiber`: a fibre of the
  first projection of a 2-fibre product along a fibrewise full 1-morphism is connected.
* `CategoryTheory.PresheafOfCategories.subsingleton_of_forall_nonempty_fiber_hom`: a presheaf
  whose category of elements is equivalent over the base to a fibration with connected fibre
  over `U` is a subsingleton at `U`.
* `AlgebraicGeometry.Stack.mono_hom_representingMaps_of_full_and_faithful` and
  `AlgebraicGeometry.Stack.mono_representingMaps_of_full_and_faithful`: the implication
  (2) ⟹ (1) of Stacks 04ZZ for the monomorphy clause, in the two forms the library states
  monomorphy of a base change in.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_of_full_and_faithful`: the implication
  (2) ⟹ (1) of Stacks 04ZZ read as `AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism`
  (**Stacks 04ZW**) for a fully faithful 1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.mono_representingMaps_fullSubcategoryInclusion`: the
  monomorphy clause for the inclusion of an algebraic substack, which is the form the residual
  gerbe of Stacks 06MU needs.

## Implementation notes

The monomorphy clause is stated in the longhand form of Stacks 04XB — a quantifier over every
algebraic space representing a base change — exactly as in
`AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_mono_representingMaps` and in
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism`, so the two match up directly. In that
form the clause carries **no** representability hypothesis: a representing space is quantified
over, not produced.

The remaining conjunct of (1), that `j` is representable by algebraic spaces, is deduced as in
the source from Stacks 04Y5, the implication (2) ⟹ (3),
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`
(`StacksFrontier/AlgebraicGeometry/Stacks/FaithfulRepresentable.lean`). The four conditions of
Stacks 04ZZ are assembled in
`StacksFrontier/AlgebraicGeometry/Stacks/MonomorphismEquivalentConditions.lean`.

The passage from subsingleton values of the representing presheaf to monomorphy of the
structural morphism is `AlgebraicGeometry.mono_algebraicSpaceMap_of_subsingleton`, already
available from Stacks 04YQ part (3); only the subsingleton statement is new. It is obtained by
reading the fibre of the 2-fibre product through
`CategoryTheory.PresheafOfCategories.elementsFiberEquiv`, which identifies the fibre of a
category of elements over `U` with the sections over `U`, so no presheaf of isomorphism classes
and no fibredness hypothesis on the 2-fibre product is needed.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

namespace CategoryTheory.TwoFibreProductOver

/-- **A fibre of the 2-fibre product along a fibrewise full 1-morphism is connected.** An object
of the fibre of `π₁ : 𝒟 ×_𝒴 𝒳 ⥤ 𝒟` over `V` is an object `y` of `𝒳` over `p𝒟 V` together with a
vertical isomorphism `G V ≅ F y`; given two of them, fullness of `F` on the fibre over `p𝒟 V`
produces the `𝒳`-component of a morphism between them, whose `𝒟`-component is the identity. -/
theorem nonempty_fst_fiber_hom_of_full_fiber
    {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟] {𝒳 : Type*} [Category 𝒳]
    {𝒴 : Type*} [Category 𝒴]
    (p𝒟 : 𝒟 ⥤ 𝒞) (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (G : 𝒟 ⥤ 𝒴) (F : 𝒳 ⥤ 𝒴) (hF : F ⋙ p𝒴 = p𝒳)
    (hfull : ∀ W : 𝒞, (Functor.Fiber.mapOfComp p𝒳 p𝒴 F hF W).Full)
    {V : 𝒟} (A C : (TwoFibreProductOver.fst p𝒟 p𝒳 p𝒴 G F).Fiber V) :
    Nonempty (A ⟶ C) := by
  obtain ⟨⟨baseP, xP, yP, hxP, hyP, isoP, vertP⟩, hP⟩ := A
  obtain ⟨⟨baseQ, xQ, yQ, hxQ, hyQ, isoQ, vertQ⟩, hQ⟩ := C
  change xP = V at hP
  change xQ = V at hQ
  subst hP hQ hxP hxQ
  have hψ : p𝒴.IsHomLift (𝟙 (p𝒟.obj xQ)) (isoP.inv ≫ isoQ.hom) := by
    have := IsHomLift.lift_id_inv p𝒴 (p𝒟.obj xQ) isoP
    infer_instance
  obtain ⟨b, hblift, hFb⟩ :
      ∃ b : yP ⟶ yQ, p𝒳.IsHomLift (𝟙 (p𝒟.obj xQ)) b ∧ F.map b = isoP.inv ≫ isoQ.hom := by
    let tt : (Functor.Fiber.mapOfComp p𝒳 p𝒴 F hF (p𝒟.obj xQ)).obj (Functor.Fiber.mk hyP) ⟶
        (Functor.Fiber.mapOfComp p𝒳 p𝒴 F hF (p𝒟.obj xQ)).obj (Functor.Fiber.mk hyQ) :=
      Functor.Fiber.homMk p𝒴 (p𝒟.obj xQ) (isoP.inv ≫ isoQ.hom)
    obtain ⟨bb, hbb⟩ := (hfull (p𝒟.obj xQ)).map_surjective tt
    refine ⟨Functor.Fiber.fiberInclusion.map bb, bb.2, ?_⟩
    have h := Functor.Fiber.fiberInclusion_map_mapOfComp_map p𝒳 p𝒴 F hF (p𝒟.obj xQ) bb
    rw [hbb] at h
    exact h.symm.trans
      (Functor.Fiber.fiberInclusion_homMk p𝒴 (p𝒟.obj xQ) (isoP.inv ≫ isoQ.hom))
  refine ⟨⟨{ hbase := 𝟙 (p𝒟.obj xQ), a := 𝟙 xQ, b := b, ha := IsHomLift.id rfl,
              hb := hblift, w := ?_ }, ?_⟩⟩
  · show G.map (𝟙 xQ) ≫ isoQ.hom = isoP.hom ≫ F.map b
    rw [hFb]
    simp
  · exact IsHomLift.of_fac' _ (𝟙 xQ) _ rfl rfl (by
      simp only [fst_map, Category.id_comp]
      exact ((eqToHom_trans _ _).trans (eqToHom_refl xQ _)).symm)

end CategoryTheory.TwoFibreProductOver

namespace CategoryTheory.PresheafOfCategories

/-- **A presheaf with connected fibre is a subsingleton there.** If the category of elements of
`F` is equivalent over the base to `p` and every two objects of the fibre of `p` over `U` are
connected by a morphism, then `F` has at most one section over `U`: the fibre of the category of
elements over `U` is `F(U)`, and connected objects of it name the same section. -/
theorem subsingleton_of_forall_nonempty_fiber_hom
    {C D : Type*} [Category C] [Category D] {p : D ⥤ C} (F : Cᵒᵖ ⥤ Type*)
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    (U : C) (hconn : ∀ a b : p.Fiber U, Nonempty (a ⟶ b)) :
    Subsingleton (F.obj (op U)) := by
  refine ⟨fun s₁ s₂ => ?_⟩
  set K := fiberFunctorOfComp e.inv.w U
  set H := fiberFunctorOfComp e.hom.w U
  obtain ⟨t₁, rfl⟩ := (elementsFiberEquiv F U).surjective s₁
  obtain ⟨t₂, rfl⟩ := (elementsFiberEquiv F U).surjective s₂
  obtain ⟨k⟩ := hconn (K.obj t₁) (K.obj t₂)
  have hiso : ∀ t : (presheafOfCategories (F ⋙ typeToCat)).p.Fiber U, H.obj (K.obj t) ≅ t :=
    fun t => Functor.Fiber.isoMk (e.counitIso.app t.1) (by
      have hl := e.isHomLift_counitIso_hom_app t.1
      rwa [t.2] at hl)
  rw [← elementsFiberEquiv_eq_of_hom F (hiso t₁).hom,
    ← elementsFiberEquiv_eq_of_hom F (hiso t₂).hom, elementsFiberEquiv_eq_of_hom F (H.map k)]

end CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04ZZ, the implication (2) ⟹ (1): a fully faithful 1-morphism has subsingleton
representing spaces.** Every algebraic space representing a base change of a fully faithful
1-morphism `j` along a scheme-valued point of `𝒴` takes subsingleton values: by Stacks 003Z (1)
the functor induced by `j` on each fibre is full, so the fibres of `(Sch/U)_fppf ×_𝒴 𝒳` are
connected, and the representing space names their isomorphism classes. -/
theorem subsingleton_representing_of_full_and_faithful
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hfull : (CatFiberedInGroupoids.homFunctor j).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor j).Faithful)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor j))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    ∀ V, Subsingleton (F.obj V) := by
  obtain ⟨e⟩ := he
  have hfib := (Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber 𝒳.val.p 𝒴.val.p
    𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor j)
    (CatFiberedInGroupoids.homFunctor_comp_p j)).1 ⟨hfull, hfaithful⟩
  exact fun V => PresheafOfCategories.subsingleton_of_forall_nonempty_fiber_hom F e V.unop
    fun a b => TwoFibreProductOver.nonempty_fst_fiber_hom_of_full_fiber (Over.map U.hom)
      𝒳.val.p 𝒴.val.p y (CatFiberedInGroupoids.homFunctor j)
      (CatFiberedInGroupoids.homFunctor_comp_p j) (fun W => (hfib W).1) a b

/-- **The implication (2) ⟹ (1) of Stacks 04ZZ.** A fully faithful 1-morphism `j : 𝒳 ⟶ 𝒴` of
categories fibred in groupoids over the big fppf site of `S` is a monomorphism in the sense of
Stacks 04XB: every algebraic space representing a base change of `j` along a scheme-valued point
of `𝒴` has monomorphic structural morphism.

This is the converse of
`AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_mono_representingMaps`, and it carries
no representability hypothesis. -/
@[stacks 04ZZ "(2) implies (1), the monomorphism clause for categories fibred in groupoids"]
theorem mono_hom_representingMaps_of_full_and_faithful
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hfull : (CatFiberedInGroupoids.homFunctor j).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor j).Faithful)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor j))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    Mono (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
  mono_hom_algebraicSpaceMap_of_subsingleton B S hS U F hF
    (subsingleton_representing_of_full_and_faithful B S hS j hfull hfaithful U y F he)

/-- **The implication (2) ⟹ (1) of Stacks 04ZZ, in the category of algebraic spaces.** This is
`AlgebraicGeometry.Stack.mono_hom_representingMaps_of_full_and_faithful` read in the category of
algebraic spaces over `S`, which is the form the relative properties of Stacks 03YK — and hence
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` — are stated in. -/
@[stacks 04ZZ "(2) implies (1), the monomorphism clause read in the category of algebraic \
spaces over S"]
theorem mono_representingMaps_of_full_and_faithful
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hfull : (CatFiberedInGroupoids.homFunctor j).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor j).Faithful)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor j))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    Mono (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) :=
  mono_algebraicSpaceMap_of_subsingleton B S hS U F hF
    (subsingleton_representing_of_full_and_faithful B S hS j hfull hfaithful U y F he)

namespace AlgebraicStacks

/-- **The implication (2) ⟹ (1) of Stacks 04ZZ, for a 1-morphism of algebraic stacks.** A fully
faithful 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is a monomorphism in the sense of
**Stacks 04ZW**.

The representability conjunct of `AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` is the
implication (2) ⟹ (3) of Stacks 04Y5,
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`;
the monomorphy conjunct is `AlgebraicGeometry.Stack.mono_representingMaps_of_full_and_faithful`. -/
@[stacks 04ZZ "(2) implies (1) for 1-morphisms of algebraic stacks"]
theorem isMonomorphism_of_full_and_faithful
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hfull : (CatFiberedInGroupoids.homFunctor f.hom).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor f.hom).Faithful) :
    AlgebraicStacks.IsMonomorphism B S hS f :=
  ⟨isRepresentableByAlgebraicSpaces_of_faithful B S hS f hfaithful,
    Stack.mono_representingMaps_of_full_and_faithful B S hS f.hom hfull hfaithful⟩

/-- **The inclusion of an algebraic substack satisfies the monomorphy clause of Stacks 04ZW.**
The inclusion of a full subcategory is fully faithful, so Stacks 04ZZ (2) ⟹ (1) applies to it:
every algebraic space representing a base change of the inclusion along a scheme-valued point of
`𝒳` has monomorphic structural morphism. No representability hypothesis is used.

This is the half of monomorphy of `𝒵_x ⟶ 𝒳` that `AlgebraicGeometry.Stack.IsResidualGerbeAt`
does not record and that Stacks 06MW and Stacks 06MX consume. -/
theorem mono_representingMaps_fullSubcategoryInclusion
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (P : ObjectProperty 𝒳.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom)
        (fullSubcategoryAlgebraicStack 𝒳 P hP).val.val.p 𝒳.val.val.p y
        (CatFiberedInGroupoids.homFunctor (fullSubcategoryInclusion 𝒳 P hP).hom))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    Mono (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) :=
  Stack.mono_representingMaps_of_full_and_faithful B S hS
    (fullSubcategoryInclusion 𝒳 P hP).hom
    (full_fullSubcategoryInclusion 𝒳 P hP) (faithful_fullSubcategoryInclusion 𝒳 P hP)
    U y hy F hF he

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
