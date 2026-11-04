module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentStackFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.TwoFibreProductOverFullyFaithful

/-!
# The fibre product `Quot^P_{F/X/B} = Quot_{F/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}` (Stacks 0DP6)

Let `f : X ⟶ B` be a separated morphism of algebraic spaces of finite presentation and `F` a
quasi-coherent `𝒪_X`-module, and fix the data of Situation 0DNC: a set `I`, perfect objects
`E_i ∈ D(𝒪_X)` and a function `P : I → ℤ`, which cut out the full subcategory
`Coh^P_{X/B} ⊆ Coh_{X/B}` of the objects `(T, 𝓕)` with `χ(K_i ⊗^𝐋 κ(t)) = P(i)` for all `i` and
`t ∈ |T|`, where `K_i = Rf_{T,*}(E_{i,T} ⊗^𝐋 𝓕)`.  Remark 0DP6 composes the morphism
`Quot_{F/X/B} ⟶ Coh_{X/B}` of `AlgebraicGeometry.Space.QuotSituation.quotToCoherent` with the
inclusion of `Coh^P_{X/B}` and *defines* `Quot^P_{F/X/B}` by the fibre product square

```
Quot^P_{F/X/B} ⟶ Coh^P_{X/B}
      ↓               ↓
Quot_{F/X/B}   ⟶ Coh_{X/B}
```

This file forms that square in the 2-category of categories over the big fppf site of `S`: the
upper left corner is the 2-fibre product over the site of Stacks 0040,
`CategoryTheory.TwoFibreProductOver`, whose objects over a scheme `U` are a member of
`Quot_{F/X/B}` over `U`, an object of `Coh^P_{X/B}` over `U` and a vertical isomorphism between
their images in `Coh_{X/B}`.

## Main definitions

* `AlgebraicGeometry.Space.NumericalSituation.numericalBasedCategory`: `Coh^P_{X/B}` as a
  category over the big fppf site, and
  `AlgebraicGeometry.Space.NumericalSituation.numericalToCoherent` its inclusion into
  `Coh_{X/B}`.
* `AlgebraicGeometry.Space.QuotSituation.numericalQuot`: **Stacks 0DP6**, the fibre product
  `Quot^P_{F/X/B}`.
* `AlgebraicGeometry.Space.QuotSituation.numericalQuotToQuot` and
  `AlgebraicGeometry.Space.QuotSituation.numericalQuotToNumerical`: the two projections, and
  `AlgebraicGeometry.Space.QuotSituation.numericalQuotSquareIso` the 2-cell filling the square.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.numericalQuotSquareIso_hom_app`: the filling 2-cell has
  the comparison isomorphism of an object of the fibre product as its component there.
* `AlgebraicGeometry.Space.QuotSituation.faithful_numericalQuotToQuot` and
  `AlgebraicGeometry.Space.QuotSituation.full_numericalQuotToQuot`: the left vertical arrow is
  fully faithful, `Coh^P_{X/B}` being a full subcategory.
* `AlgebraicGeometry.Space.QuotSituation.exists_numericalQuot_x_eq_iff`: its essential image is
  the quotients whose object of `Coh_{X/B}` lies in `Coh^P_{X/B}`, so `Quot^P_{F/X/B}` is the
  subfunctor `AlgebraicGeometry.Space.QuotSituation.quotCondition` of `Quot_{F/X/B}`.
* `CategoryTheory.TwoFibreProductOver.exists_x_eq_iff` (with
  `CategoryTheory.TwoFibreProductOver.full_fst` and `faithful_fst_of_faithful`): in general,
  the base change of the inclusion of a full subcategory closed under isomorphisms is fully
  faithful, and its essential image consists of the objects whose image lies in the
  subcategory.

## References

* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- **An object of `𝒳` lifts to the 2-fibre product along the inclusion of a full subcategory
closed under isomorphisms exactly when its image lies in the subcategory**: it lifts with the
identity comparison when its image does, and conversely the image of a lift is isomorphic to an
object of the subcategory. -/
theorem exists_x_eq_iff {Z : ObjectProperty 𝒮} (hF : F ⋙ p𝒮 = p𝒳)
    (hZ : ∀ {s s' : 𝒮}, (s ≅ s') → Z s' → Z s) (x : 𝒳) :
    (∃ P : TwoFibreProductOver p𝒳 (Z.ι ⋙ p𝒮) p𝒮 F Z.ι, P.x = x) ↔ Z (F.obj x) := by
  constructor
  · rintro ⟨P, rfl⟩
    exact hZ P.iso P.y.property
  · intro hx
    have h := Functor.congr_obj hF x
    refine ⟨⟨_, x, ⟨_, hx⟩, rfl, h, Iso.refl _, IsHomLift.of_fac' p𝒮 _ _ h h ?_⟩, rfl⟩
    simp

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Space

universe u v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace NumericalSituation

variable {D : CoherentSituation B S hS} (N : NumericalSituation.{u, v, u} B S hS D)

/-- **`Coh^P_{X/B}` as a category over the big fppf site of `S`**: the full subcategory of
`Coh_{X/B}` of Situation 0DNC, projecting an object `(T, 𝓕)` to the scheme `T`. -/
def numericalBasedCategory : BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS) where
  obj := N.numericalSubstack
  category := inferInstanceAs (Category N.numericalSubstack)
  p := letI : Category.{u + 1} (CoherentObject D) :=
      CoherentSituation.coherentCategory (modulePushforwardCoherence B S hS) D
    ObjectProperty.ι N.HasNumericalInvariants ⋙ coherentSiteProjection D.categoryData

/-- **The inclusion `Coh^P_{X/B} ⟶ Coh_{X/B}`** as a 1-morphism of categories over the big fppf
site. -/
def numericalToCoherent :
    N.numericalBasedCategory ⥤ᵇ coherentBasedCategory D.categoryData where
  toFunctor := letI : Category.{u + 1} (CoherentObject D) :=
      CoherentSituation.coherentCategory (modulePushforwardCoherence B S hS) D
    ObjectProperty.ι N.HasNumericalInvariants
  w := rfl

/-- The inclusion `Coh^P_{X/B} ⟶ Coh_{X/B}` is faithful. -/
instance faithful_numericalToCoherent : N.numericalToCoherent.toFunctor.Faithful :=
  letI : Category.{u + 1} (CoherentObject D) :=
    CoherentSituation.coherentCategory (modulePushforwardCoherence B S hS) D
  ObjectProperty.faithful_ι N.HasNumericalInvariants

/-- The inclusion `Coh^P_{X/B} ⟶ Coh_{X/B}` is full. -/
instance full_numericalToCoherent : N.numericalToCoherent.toFunctor.Full :=
  letI : Category.{u + 1} (CoherentObject D) :=
    CoherentSituation.coherentCategory (modulePushforwardCoherence B S hS) D
  ObjectProperty.full_ι N.HasNumericalInvariants

/-- The inclusion sends an object of `Coh^P_{X/B}` to its underlying object of `Coh_{X/B}`. -/
theorem numericalToCoherent_obj (A : N.numericalBasedCategory.obj) :
    letI : Category.{u + 1} (CoherentObject D) :=
      CoherentSituation.coherentCategory (modulePushforwardCoherence B S hS) D
    N.numericalToCoherent.obj A =
      (A : ObjectProperty.FullSubcategory N.HasNumericalInvariants).obj :=
  rfl

end NumericalSituation

namespace QuotSituation

variable (D : QuotSituation B S hS) (N : NumericalSituation.{u, v, u} B S hS D.toCoherentSituation)

/-- The category underlying `Quot^P_{F/X/B}`: the 2-fibre product over the big fppf site of the
morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` and the inclusion `Coh^P_{X/B} ⟶ Coh_{X/B}`. -/
abbrev NumericalQuotObjects : Type (u + 1) :=
  TwoFibreProductOver D.quotBasedCategory.p N.numericalBasedCategory.p
    (coherentBasedCategory D.toCoherentSituation.categoryData).p D.quotToCoherent.toFunctor
    N.numericalToCoherent.toFunctor

/-- **The fibre product `Quot^P_{F/X/B} = Quot_{F/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`**, as a category
over the big fppf site of `S`: an object over a scheme `U` is a member `F_T ⟶ 𝒬` of
`Quot_{F/X/B}` over `U`, an object of `Coh^P_{X/B}` over `U` and a vertical isomorphism of their
images in `Coh_{X/B}`. -/
@[stacks 0DP6 "the fibre product Quot^P = Quot_{F/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}, as the 2-fibre \
product over the site of Stacks 0040 of the morphism Quot ⟶ Coh and the inclusion Coh^P ⟶ Coh"]
def numericalQuot : BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor
    (TwoFibreProductOver.structureFunctor D.quotBasedCategory.p N.numericalBasedCategory.p
      (coherentBasedCategory D.toCoherentSituation.categoryData).p D.quotToCoherent.toFunctor
      N.numericalToCoherent.toFunctor)

/-- **The left vertical arrow `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}`** of the square of Stacks 0DP6, as a
1-morphism of categories over the big fppf site. -/
def numericalQuotToQuot : D.numericalQuot N ⥤ᵇ D.quotBasedCategory where
  toFunctor := TwoFibreProductOver.fst _ _ _ _ _
  w := TwoFibreProductOver.fst_comp_eq

/-- **The upper arrow `Quot^P_{F/X/B} ⟶ Coh^P_{X/B}`** of the square of Stacks 0DP6, as a
1-morphism of categories over the big fppf site. -/
def numericalQuotToNumerical : D.numericalQuot N ⥤ᵇ N.numericalBasedCategory where
  toFunctor := TwoFibreProductOver.snd _ _ _ _ _
  w := TwoFibreProductOver.snd_comp_eq

/-- **The 2-cell filling the square of Stacks 0DP6**: the two composites
`Quot^P_{F/X/B} ⟶ Coh_{X/B}` are isomorphic, by the comparison isomorphism carried by the objects
of the fibre product. -/
def numericalQuotSquareIso :
    (D.numericalQuotToQuot N).toFunctor ⋙ D.quotToCoherent.toFunctor ≅
      (D.numericalQuotToNumerical N).toFunctor ⋙ N.numericalToCoherent.toFunctor :=
  TwoFibreProductOver.psiIso _ _ _ _ _

/-- The component of the filling 2-cell at an object of the fibre product is the comparison
isomorphism it carries. -/
theorem numericalQuotSquareIso_hom_app (P : D.NumericalQuotObjects N) :
    (D.numericalQuotSquareIso N).hom.app P = P.iso.hom :=
  rfl

/-- The filling 2-cell is vertical: its components lie over identities of the site. -/
theorem numericalQuotSquareIso_vertical (P : D.NumericalQuotObjects N) :
    (coherentBasedCategory D.toCoherentSituation.categoryData).p.IsHomLift (𝟙 P.base)
      ((D.numericalQuotSquareIso N).hom.app P) :=
  P.vertical

/-- **The left vertical arrow `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is faithful**: `Coh^P_{X/B}` is a
full subcategory of `Coh_{X/B}`. -/
theorem faithful_numericalQuotToQuot : (D.numericalQuotToQuot N).toFunctor.Faithful :=
  let : Category.{u + 1} (CoherentObject D.toCoherentSituation) :=
    CoherentSituation.coherentCategory (modulePushforwardCoherence B S hS) D.toCoherentSituation
  TwoFibreProductOver.faithful_fst_of_faithful

/-- **The left vertical arrow `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is full**: `Coh^P_{X/B}` is a full
subcategory of `Coh_{X/B}`, so a morphism of `Quot_{F/X/B}` between objects of the fibre product
lifts. -/
theorem full_numericalQuotToQuot : (D.numericalQuotToQuot N).toFunctor.Full :=
  let : Category.{u + 1} (CoherentObject D.toCoherentSituation) :=
    CoherentSituation.coherentCategory (modulePushforwardCoherence B S hS) D.toCoherentSituation
  TwoFibreProductOver.full_fst D.quotToCoherent.w N.numericalToCoherent.w

/-- **The essential image of the left vertical arrow `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}`**: a member
`F_T ⟶ 𝒬` of `Quot_{F/X/B}` lifts to the fibre product exactly when the object `(T, 𝒬)` of
`Coh_{X/B}` lies in `Coh^P_{X/B}`, as soon as the condition cutting out `Coh^P_{X/B}` is inherited
along the morphisms of `Coh_{X/B}`.  Together with the full faithfulness of the arrow, this
identifies `Quot^P_{F/X/B}` with the subfunctor of `Quot_{F/X/B}` of the quotients whose object of
`Coh_{X/B}` lies in `Coh^P_{X/B}`. -/
theorem exists_numericalQuot_x_eq_iff
    (hQ : ∀ {A' A : CoherentObject D.toCoherentSituation}, CoherentHom A' A →
      N.HasNumericalInvariants A → N.HasNumericalInvariants A') (x : D.QuotObjects) :
    (∃ P : D.NumericalQuotObjects N, P.x = x) ↔
      N.HasNumericalInvariants (D.cohObject x.T x.K x.mem) :=
  let : Category.{u + 1} (CoherentObject D.toCoherentSituation) :=
    CoherentSituation.coherentCategory (modulePushforwardCoherence B S hS) D.toCoherentSituation
  TwoFibreProductOver.exists_x_eq_iff (Z := N.HasNumericalInvariants) D.quotToCoherent.w
    (fun e h => hQ e.hom h) x

end QuotSituation

end AlgebraicGeometry.Space

end
