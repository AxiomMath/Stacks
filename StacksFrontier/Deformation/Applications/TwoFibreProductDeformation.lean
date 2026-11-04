module

public import Mathlib.CategoryTheory.PUnit
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.RimSchlessinger.TwoFibreProduct
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# The 2-fibre product of deformation categories

Let `f : ℋ → ℱ` and `g : 𝒢 → ℱ` be `1`-morphisms of deformation categories over `𝒞_Λ`. Then
`𝒲 = ℋ ×_ℱ 𝒢` is again a deformation category, and when the two outer legs are deformation
*functors* it is again a deformation functor.

## Main results

* `Deformation.isDeformationCategory_twoFibreProductOver`: part (1) of Tag 06L5, that the
  `2`-fibre product of deformation categories is a deformation category.
* `Deformation.isDeformationFunctor_twoFibreProductOver_self`: part (1) of Tag 06L6, that
  `U ×_{f, ℱ, f} U` is a deformation functor when `U` is.

## Main definitions

* `Deformation.isThin_fibre_twoFibreProductOver`: thinness of the fibres passes to the
  `2`-fibre product.
* `Deformation.infinitesimalAutomorphisms_eq_bot_of_isThin`: infinitesimal automorphisms
  vanish over a thin fibre.

## Implementation notes

The `2`-fibre product is `CategoryTheory.TwoFibreProductOver`, the `2`-fibre product in the
`(2,1)`-category of categories *over* `𝒞_Λ`; Mathlib's
`CategoryTheory.Limits.CategoricalPullback` is a different and genuinely inequivalent object,
the `2`-fibre product of plain categories.

Condition (RS) for the `2`-fibre product is Tag 06L4,
`Deformation.satisfiesRS_twoFibreProductOver`. Since `Deformation.SatisfiesRS` bundles the
cofibered-in-groupoids condition, that single result supplies both the `satisfiesRS` field of
`Deformation.IsDeformationCategory` and the `cofibered` field of its
`Deformation.IsPredeformationCategory`, so only the special fibre remains.

For the special fibre the source says that `𝒲(k)` is "the fibre product of two setoids with a
unique isomorphism class over a setoid with a unique isomorphism class". Having a unique
isomorphism class is `CategoryTheory.equiv_punit_iff_unique`: a category is equivalent to the
one-object one-morphism category exactly when it is nonempty and has a unique morphism between
any two objects. The two halves are then proved separately, and both use the hypothesis on `ℱ`:

* nonemptiness needs the unique morphism `f(x₀) ⟶ g(y₀)` of `ℱ(k)`, which is invertible because
  `ℱ(k)` also has a unique morphism the other way, and which is vertical because it is a
  morphism of the fibre;
* uniqueness of a morphism `P ⟶ Q` of `𝒲(k)` needs the unique morphisms `P.x ⟶ Q.x` of `ℋ(k)`
  and `P.y ⟶ Q.y` of `𝒢(k)` *together with* the fact that the comparison square commutes
  automatically, both of its two composites being morphisms `f(P.x) ⟶ g(Q.y)` of `ℱ(k)`.

A morphism of the `2`-fibre product is determined by its two components
(`CategoryTheory.TwoFibreProductOver.Hom.ext'`), which is what makes the second half an
equality of pairs.

For Tag 06L6 the extra input over Tag 06L5 is the source's `Inf(U) = (0)`. A deformation
functor is presented here as a set-valued functor whose category of elements is a deformation
category (`Deformation.IsDeformationFunctor`, Tag 06JA), and the fibres of a category of
elements are thin, so the vanishing is the observation that a thin fibre has only the identity
automorphism. Tag 06K0, `Deformation.infinitesimalAutomorphisms_eq_bot_iff_isEquivalence`,
reads that vanishing back as the statement that the `2`-fibre product is itself a functor;
only that reformulation, not a second construction, is what "is a deformation functor" means
here.

## References

* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
* [Stacks Project, Tag 06L6](https://stacks.math.columbia.edu/tag/06L6)
-/

@[expose] public section

namespace Deformation

/-! ### The fibre of a 2-fibre product over a base object -/

section Fibre
open CategoryTheory CategoryTheory.Functor
universe vC uC vX uX vY uY vS uS

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y] {S : Type uS} [Category.{vS} S]
  {pX : X ⥤ C} {pY : Y ⥤ C} {pS : S ⥤ C} {Φ : X ⥤ S} {Ψ : Y ⥤ S} {U : C}

/-- The comparison isomorphism carried by an object of the fibre of the `2`-fibre product over
`U` lies over `𝟙 U`, since it lies over the identity of that object's own base. -/
private lemma isHomLift_fibreObj_iso_hom
    (P : (TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).Fiber U) :
    pS.IsHomLift (𝟙 U) P.1.iso.hom := by
  obtain ⟨P, rfl⟩ := P
  exact P.vertical

/-- The `X`-component of an object of the fibre of the `2`-fibre product over `U`, as an object
of the fibre of `pX` over `U`. -/
@[implicit_reducible]
private def fibreFst (P : (TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).Fiber U) :
    pX.Fiber U :=
  ⟨P.1.x, P.1.hx.trans P.2⟩

/-- The `Y`-component of an object of the fibre of the `2`-fibre product over `U`, as an object
of the fibre of `pY` over `U`. -/
@[implicit_reducible]
private def fibreSnd (P : (TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).Fiber U) :
    pY.Fiber U :=
  ⟨P.1.y, P.1.hy.trans P.2⟩

/-- The `X`-component of a morphism of the fibre of the `2`-fibre product over `U`, as a
morphism of the fibre of `pX` over `U`. -/
@[implicit_reducible]
private def fibreFstHom
    {P Q : (TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).Fiber U} (m : P ⟶ Q) :
    fibreFst P ⟶ fibreFst Q :=
  ⟨m.1.a, TwoFibreProductOver.isHomLift_a m.1 (𝟙 U) m.2⟩

/-- The `Y`-component of a morphism of the fibre of the `2`-fibre product over `U`, as a
morphism of the fibre of `pY` over `U`. -/
@[implicit_reducible]
private def fibreSndHom
    {P Q : (TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).Fiber U} (m : P ⟶ Q) :
    fibreSnd P ⟶ fibreSnd Q :=
  ⟨m.1.b, TwoFibreProductOver.isHomLift_b m.1 (𝟙 U) m.2⟩

section fibreHomMk

-- The base morphism and the two `IsHomLift` fields below compare the base object of `P` read
-- through the structure functor with the base object `U` of the fibre, so they are type-correct
-- only once that functor unfolds.
attribute [local implicit_reducible] TwoFibreProductOver.structureFunctor

/-- A pair of morphisms of the fibres of `pX` and `pY` over `U` whose comparison square
commutes, read as a morphism of the fibre of the `2`-fibre product over `U`. -/
private def fibreHomMk
    {P Q : (TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).Fiber U}
    (α : fibreFst P ⟶ fibreFst Q) (β : fibreSnd P ⟶ fibreSnd Q)
    (w : Φ.map α.1 ≫ Q.1.iso.hom = P.1.iso.hom ≫ Ψ.map β.1) : P ⟶ Q :=
  ⟨{ hbase := eqToHom P.2 ≫ eqToHom Q.2.symm
     a := α.1
     b := β.1
     ha := by
       have := α.2
       refine IsHomLift.of_fac' pX _ α.1 P.1.hx Q.1.hx ?_
       rw [IsHomLift.fac' pX (𝟙 U) α.1]
       simp
     hb := by
       have := β.2
       refine IsHomLift.of_fac' pY _ β.1 P.1.hy Q.1.hy ?_
       rw [IsHomLift.fac' pY (𝟙 U) β.1]
       simp
     w := w },
    IsHomLift.of_fac' (TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ) (𝟙 U) _
      P.2 Q.2 (by simp)⟩

end fibreHomMk

/-- A morphism of the fibre of the `2`-fibre product over `U` is determined by its two
components, so there is at most one when each component has at most one choice. -/
private lemma subsingleton_fibre_hom_twoFibreProductOver
    (P Q : (TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).Fiber U)
    [Subsingleton (fibreFst P ⟶ fibreFst Q)] [Subsingleton (fibreSnd P ⟶ fibreSnd Q)] :
    Subsingleton (P ⟶ Q) := by
  refine ⟨fun m n => Fiber.hom_ext (TwoFibreProductOver.Hom.ext' ?_ ?_)⟩
  · exact congrArg Subtype.val (Subsingleton.elim (fibreFstHom m) (fibreFstHom n))
  · exact congrArg Subtype.val (Subsingleton.elim (fibreSndHom m) (fibreSndHom n))

end Fibre

/-! ### The special fibre of a 2-fibre product -/

section SpecialFibre
open CategoryTheory CategoryTheory.Functor
universe vC uC vX uX vY uY vS uS

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y] {S : Type uS} [Category.{vS} S]
  {pX : X ⥤ C} {pY : Y ⥤ C} {pS : S ⥤ C} {Φ : X ⥤ S} {Ψ : Y ⥤ S} {U : C}

/-- If the fibres of `pX` and `pY` over `U` are nonempty and the fibre of `pS` over `U` has a
unique morphism between any two objects, then the fibre of the `2`-fibre product over `U` is
nonempty: the comparison isomorphism is the unique morphism `Φ(x₀) ⟶ Ψ(y₀)` of the fibre of
`pS`, which is invertible because that fibre also has a unique morphism the other way. -/
private lemma nonempty_fibre_twoFibreProductOver
    (hΦ : Φ ⋙ pS = pX) (hΨ : Ψ ⋙ pS = pY)
    (hX : Nonempty (pX.Fiber U)) (hY : Nonempty (pY.Fiber U))
    (hS : ∀ A B : pS.Fiber U, Nonempty (Unique (A ⟶ B))) :
    Nonempty ((TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).Fiber U) := by
  obtain ⟨x₀⟩ := hX
  obtain ⟨y₀⟩ := hY
  let A : pS.Fiber U := ⟨Φ.obj x₀.1, (Functor.congr_obj hΦ x₀.1).trans x₀.2⟩
  let B : pS.Fiber U := ⟨Ψ.obj y₀.1, (Functor.congr_obj hΨ y₀.1).trans y₀.2⟩
  obtain ⟨_uAB⟩ := hS A B
  obtain ⟨_uBA⟩ := hS B A
  obtain ⟨_uAA⟩ := hS A A
  obtain ⟨_uBB⟩ := hS B B
  let e : A ≅ B := ⟨default, default, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  exact ⟨⟨{ base := U
            x := x₀.1
            y := y₀.1
            hx := x₀.2
            hy := y₀.2
            iso := Fiber.fiberInclusion.mapIso e
            vertical := e.hom.2 }, rfl⟩⟩

/-- If the fibres of `pX`, `pY` and `pS` over `U` each have a unique morphism between any two
objects, then so does the fibre of the `2`-fibre product over `U`.

Existence takes the unique morphisms of the fibres of `pX` and `pY`; the comparison square they
have to make commute does so automatically, because its two composites are both morphisms
`Φ(P.x) ⟶ Ψ(Q.y)` of the fibre of `pS`. Uniqueness is uniqueness of the two components, a
morphism of the `2`-fibre product being determined by them. -/
private lemma unique_fibre_hom_twoFibreProductOver
    (hΦ : Φ ⋙ pS = pX) (hΨ : Ψ ⋙ pS = pY)
    (hX : ∀ A B : pX.Fiber U, Nonempty (Unique (A ⟶ B)))
    (hY : ∀ A B : pY.Fiber U, Nonempty (Unique (A ⟶ B)))
    (hS : ∀ A B : pS.Fiber U, Nonempty (Unique (A ⟶ B)))
    (P Q : (TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).Fiber U) :
    Nonempty (Unique (P ⟶ Q)) := by
  obtain ⟨_uX⟩ := hX (fibreFst P) (fibreFst Q)
  obtain ⟨_uY⟩ := hY (fibreSnd P) (fibreSnd Q)
  let α : fibreFst P ⟶ fibreFst Q := default
  let β : fibreSnd P ⟶ fibreSnd Q := default
  let A : pS.Fiber U := ⟨Φ.obj P.1.x, (Functor.congr_obj hΦ P.1.x).trans (fibreFst P).2⟩
  let B : pS.Fiber U := ⟨Ψ.obj Q.1.y, (Functor.congr_obj hΨ Q.1.y).trans (fibreSnd Q).2⟩
  -- The two composites of the comparison square are morphisms of the fibre of `pS` over `U`.
  have hΦα : pS.IsHomLift (𝟙 U) (Φ.map α.1) := by
    have := α.2
    exact Functor.isHomLift_map_of_comp_eq hΦ (𝟙 U) α.1
  have hΨβ : pS.IsHomLift (𝟙 U) (Ψ.map β.1) := by
    have := β.2
    exact Functor.isHomLift_map_of_comp_eq hΨ (𝟙 U) β.1
  have hleft : pS.IsHomLift (𝟙 U) (Φ.map α.1 ≫ Q.1.iso.hom) :=
    @IsHomLift.comp_of_lift_id _ _ _ _ pS U _ _ _ _ _ hΦα (isHomLift_fibreObj_iso_hom Q)
  have hright : pS.IsHomLift (𝟙 U) (P.1.iso.hom ≫ Ψ.map β.1) :=
    @IsHomLift.comp_of_lift_id _ _ _ _ pS U _ _ _ _ _ (isHomLift_fibreObj_iso_hom P) hΨβ
  obtain ⟨_uAB⟩ := hS A B
  -- Hence they agree, so the square commutes and the pair `(α, β)` is a morphism `P ⟶ Q`.
  have w : Φ.map α.1 ≫ Q.1.iso.hom = P.1.iso.hom ≫ Ψ.map β.1 :=
    congrArg Subtype.val
      (Subsingleton.elim (⟨_, hleft⟩ : A ⟶ B) (⟨_, hright⟩ : A ⟶ B))
  have := subsingleton_fibre_hom_twoFibreProductOver P Q
  exact ⟨uniqueOfSubsingleton (fibreHomMk α β w)⟩

end SpecialFibre

/-! ### The 2-fibre product of deformation categories -/

section
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

/-- **Stacks Project, Tag 06L5, part (1).** The `2`-fibre product `𝒲 = ℋ ×_ℱ 𝒢` of two
`1`-morphisms of deformation categories over `𝒞_Λ` is again a deformation category.

Condition (RS) is Tag 06L4, and it carries the cofibered-in-groupoids condition with it; the
special fibre `𝒲(k)` has a unique isomorphism class because `ℋ(k)`, `𝒢(k)` and `ℱ(k)` do. -/
@[stacks 06L5 "part (1)"]
theorem isDeformationCategory_twoFibreProductOver
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {H : Type u₁} [Category.{v₁} H]
    {G : Type u₂} [Category.{v₂} G]
    {F : Type u₃} [Category.{v₃} F]
    (pH : H ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pG : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F)
    (hf : f ⋙ pF = pH) (hg : g ⋙ pF = pG)
    (hH : IsDeformationCategory pH)
    (hG : IsDeformationCategory pG)
    (hF : IsDeformationCategory pF) :
    IsDeformationCategory (TwoFibreProductOver.structureFunctor pH pG pF f g) := by
  have hRS := satisfiesRS_twoFibreProductOver pH pG pF f g hf hg
    hH.satisfiesRS hG.satisfiesRS hF.satisfiesRS
  obtain ⟨hHne, hHu⟩ :=
    (equiv_punit_iff_unique _).mp hH.predeformation.specialFiber
  obtain ⟨hGne, hGu⟩ :=
    (equiv_punit_iff_unique _).mp hG.predeformation.specialFiber
  obtain ⟨-, hFu⟩ :=
    (equiv_punit_iff_unique _).mp hF.predeformation.specialFiber
  exact ⟨⟨hRS.1, (equiv_punit_iff_unique _).mpr
    ⟨nonempty_fibre_twoFibreProductOver hf hg hHne hGne hFu,
      unique_fibre_hom_twoFibreProductOver hf hg hHu hGu hFu⟩⟩, hRS⟩

end

/-! ### Thin fibres of a 2-fibre product -/

section ThinFibre
open CategoryTheory CategoryTheory.Functor
universe vC uC vX uX vY uY vS uS

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  {Y : Type uY} [Category.{vY} Y] {S : Type uS} [Category.{vS} S]
  {pX : X ⥤ C} {pY : Y ⥤ C} {pS : S ⥤ C} {Φ : X ⥤ S} {Ψ : Y ⥤ S} {U : C}

/-- If the fibres of `pX` and `pY` over `U` are thin, then so is the fibre of the `2`-fibre
product over `U`.

A morphism of the `2`-fibre product is determined by its two components
(`CategoryTheory.TwoFibreProductOver.Hom.ext'`), and each component is a morphism of one of
those two fibres, so there is at most one of it. Unlike
`Deformation.unique_fibre_hom_twoFibreProductOver` this assumes nothing about `pS`: thinness
is inherited from the two factors alone, because the comparison square a pair of components
has to make commute is a *condition* on them, not extra data. -/
theorem isThin_fibre_twoFibreProductOver
    (hX : Quiver.IsThin (pX.Fiber U)) (hY : Quiver.IsThin (pY.Fiber U)) :
    Quiver.IsThin ((TwoFibreProductOver.structureFunctor pX pY pS Φ Ψ).Fiber U) := by
  intro P Q
  have := hX (fibreFst P) (fibreFst Q)
  have := hY (fibreSnd P) (fibreSnd Q)
  exact subsingleton_fibre_hom_twoFibreProductOver P Q

end ThinFibre

/-! ### Vanishing of infinitesimal automorphisms over a thin fibre -/

section Vanishing
open CategoryTheory
universe u v w u₁ v₁

/-- A category cofibered in groupoids whose fibre over `Aε` is thin has no nontrivial
infinitesimal automorphisms at any object of that fibre: an infinitesimal automorphism is in
particular an automorphism in the fibre, and a thin fibre has only the identity.

Applied to the category of elements of a set-valued functor this is the vanishing
`Inf(U) = (0)` that the source uses, and Tag 06K0,
`Deformation.infinitesimalAutomorphisms_eq_bot_iff_isEquivalence`, turns it back into the
statement that such a category *is* a functor. -/
theorem infinitesimalAutomorphisms_eq_bot_of_isThin
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {A₀ Aε : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x₀ : p.Fiber A₀} {xε : p.Fiber Aε}
    (hp : IsCofiberedInGroupoids p)
    (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i)
    (hthin : Quiver.IsThin (p.Fiber Aε)) :
    infinitesimalAutomorphisms hp g e hpair i hi = ⊥ := by
  have := hthin xε xε
  exact (Subgroup.eq_bot_iff_forall _).2 fun a _ => Iso.ext (Subsingleton.elim _ _)

end Vanishing

/-! ### The 2-fibre product of a deformation functor with itself -/

section SelfFibreProduct
open CategoryTheory CategoryTheory.Functor
universe u v w t u₃ v₃

/-- **Stacks Project, Tag 06L6, part (1).** Let `U : 𝒞_Λ → Sets` be a deformation functor,
`ℱ` a deformation category and `f : U → ℱ` a `1`-morphism of categories cofibered in
groupoids over `𝒞_Λ`. Then `𝒲 = U ×_{f, ℱ, f} U` is a deformation functor: it is a
deformation category, and every one of its infinitesimal automorphism groups vanishes, which
by Tag 06K0 is exactly the statement that it is cofibered in setoids, i.e. that it is a
functor.

The deformation-category half is Tag 06L5 part (1),
`Deformation.isDeformationCategory_twoFibreProductOver`, read through
`Deformation.isDeformationCategory_iff` for the two outer legs. The vanishing is the source's
"the fact that `Inf(U) = (0)`": the fibres of the category of elements of a set-valued functor
are thin (`Deformation.elementsFiber_isThin`), hence so are the fibres of the `2`-fibre
product (`Deformation.isThin_fibre_twoFibreProductOver`), and over a thin fibre there is no
room for a nontrivial automorphism at all.

The cofibered-in-groupoids witness is quantified over rather than taken from the first
component because `Deformation.IsCofiberedInGroupoids` is a proposition, so the infinitesimal
automorphism group does not depend on which witness is supplied. -/
@[stacks 06L6 "part (1), that the 2-fibre product is a deformation functor; the exact sequence \
0 → Inf(ℱ) → T(U ×_{f,ℱ,f} U) → TU ⊕ TU of part (2) is not covered"]
theorem isDeformationFunctor_twoFibreProductOver_self
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (U : ArtinianLocalAlgCat.{u, max v w, w} Λ k ⥤ Type t)
    {F : Type u₃} [Category.{v₃} F]
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : U.Elements ⥤ F)
    (hf : f ⋙ pF = CategoryOfElements.π U)
    (hU : IsDeformationFunctor U)
    (hF : IsDeformationCategory pF) :
    let p𝒲 := TwoFibreProductOver.structureFunctor
      (CategoryOfElements.π U) (CategoryOfElements.π U) pF f f
    IsDeformationCategory p𝒲 ∧
      ∀ (hcof : IsCofiberedInGroupoids p𝒲)
        {A₀ Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
        {w₀ : p𝒲.Fiber A₀} {wε : p𝒲.Fiber Aε}
        (g : A₀ ⟶ Aε) (e : Aε ⟶ A₀) (hpair : IsCanonicalDualNumberPair g e)
        (i : w₀.1 ⟶ wε.1) (hi : p𝒲.IsHomLift g i),
        infinitesimalAutomorphisms hcof g e hpair i hi = ⊥ := by
  have hπU : IsDeformationCategory (CategoryOfElements.π U) :=
    (isDeformationCategory_iff U).mpr hU
  refine ⟨isDeformationCategory_twoFibreProductOver (CategoryOfElements.π U)
    (CategoryOfElements.π U) pF f f hf hf hπU hπU hF, ?_⟩
  intro hcof _ Aε _ _ g e hpair i hi
  exact infinitesimalAutomorphisms_eq_bot_of_isThin hcof g e hpair i hi
    (isThin_fibre_twoFibreProductOver (elementsFiber_isThin U Aε) (elementsFiber_isThin U Aε))

end SelfFibreProduct

end Deformation

end
