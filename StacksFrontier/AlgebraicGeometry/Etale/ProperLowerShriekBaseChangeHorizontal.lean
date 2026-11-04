module

public import StacksFrontier.AlgebraicGeometry.Etale.ProperLowerShriekBaseChange
public import StacksFrontier.CategoryTheory.Functor.Derived.BaseChangeHorizontalPasting
public import
  StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory

import StacksCore.Tactic.StacksAttribute

/-!
# Horizontal pasting of the base change maps `h_! ∘ Rf'_* ⟶ Rf_* ∘ g_!`

Consider a commutative diagram of a big étale site
```
X'' --g'--> X' --g--> X
|           |         |
f''         f'        f
v           v         v
Y'' --h'--> Y' --h--> Y
```
with `f`, `f'` and `f''` proper and `g`, `g'`, `h` and `h'` separated and locally quasi-finite.
Each square has the base change map of [Stacks, Tag 0F7B],
`AlgebraicGeometry.SmallEtale.properBaseChangeMap`, and so has the outer rectangle. This file
proves [Stacks, Tag 0F7D]: once `(h' ≫ h)_!` is identified with `h'_! ⋙ h_!` and `(g' ≫ g)_!`
with `g'_! ⋙ g_!` (Stacks 0F50), the map of the outer rectangle is the composite of the maps of
the two squares.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekFunctorCompIso`: Stacks 0F50 on the model
  `fShriekFunctor` of the direct image with compact support, and
  `AlgebraicGeometry.SmallEtale.etaleModuleLiftFShriekCompIso` its `Λ`-linear lift.

## Main results

* `AlgebraicGeometry.SmallEtale.properSupportSquareIso_horizontal_paste`,
  `AlgebraicGeometry.SmallEtale.pushforwardFShriekSquareIso_horizontal_paste` and
  `AlgebraicGeometry.SmallEtale.pushforwardFShriekModSquareIso_horizontal_paste`: the
  identifications `f'_* ⋙ h_! ≅ g_! ⋙ f_*` of two squares side by side paste to that of the
  rectangle, on the proper-support model of `f_!`, on abelian étale sheaves and on sheaves of
  `Λ`-modules.
* `AlgebraicGeometry.SmallEtale.properBaseChangeMap_horizontal_paste`: **[Stacks, Tag 0F7D]**.

## Implementation notes

The three pasting statements are instances of
`Stacks.DerivedBaseChange.HorizontalPasteLaw`, and each one is deduced from the previous one by
the formal transport lemmas `Stacks.DerivedBaseChange.HorizontalPasteLaw.conj` (along the
isomorphisms of Stacks 0F6N and 0F51 between the models of the functors) and
`Stacks.DerivedBaseChange.HorizontalPasteLaw.of_faithful` (along forgetting the `Λ`-module
structure); the passage to homotopy categories is
`Stacks.DerivedBaseChange.homotopySquareIso_horizontal_paste`, and the derived statement is
`Stacks.DerivedBaseChange.squareMap_horizontal_paste`, with the derived identification
`(h' ≫ h)_! = h'_! ⋙ h_!` taken to be `CategoryTheory.Functor.mapDerivedCategoryCompIso`, whose
value on the image of the homotopy category is
`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Qh`. Stating the transport lemmas over
functor variables, and instantiating them at the concrete functors in term mode, keeps the
identifications of the different spellings of the same functors out of the elaborator and the
kernel.

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F7D](https://stacks.math.columbia.edu/tag/0F7D)
* [Stacks Project, Tag 0F50](https://stacks.math.columbia.edu/tag/0F50)
* [Stacks Project, Tag 0F77](https://stacks.math.columbia.edu/tag/0F77)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace AlgebraicGeometry.SmallEtale

/-! ### The proper-support identifications of two squares side by side -/

section ProperSupport

variable (B : BigEtaleSite.{u}) {X'' X' X Y'' Y' Y : B.Scheme}

/-- **Horizontal pasting of the proper-support identifications.** For two commutative squares
`g' ≫ f' = f'' ≫ h'` and `g ≫ f = f' ≫ h` side by side, Stacks 0F50 for `h' ≫ h` followed by
the identification of the outer rectangle is the identification of the left square, followed by
that of the right square and by Stacks 0F50 for `g' ≫ g`. -/
lemma properSupportSquareIso_horizontal_paste (g' : X'' ⟶ X') (g : X' ⟶ X) (f'' : X'' ⟶ Y'')
    (f' : X' ⟶ Y') (f : X ⟶ Y) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y) (G : X'' ⟶ X) (H : Y'' ⟶ Y)
    (d₁ : X'' ⟶ Y') (d₂ : X' ⟶ Y) (d : X'' ⟶ Y)
    (hG : g' ≫ g = G) (hH : h' ≫ h = H) (hk₁ : g' ≫ f' = d₁) (hl₁ : f'' ≫ h' = d₁)
    (hk₂ : g ≫ f = d₂) (hl₂ : f' ≫ h = d₂) (hk : G ≫ f = d) (hl : f'' ≫ H = d)
    [LocallyOfFiniteType (B.inclusion.map g')] [LocallyOfFiniteType (B.inclusion.map g)]
    [LocallyOfFiniteType (B.inclusion.map f'')] [LocallyOfFiniteType (B.inclusion.map f')]
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map h')]
    [LocallyOfFiniteType (B.inclusion.map h)] [LocallyOfFiniteType (B.inclusion.map G)]
    [LocallyOfFiniteType (B.inclusion.map H)] [LocallyOfFiniteType (B.inclusion.map d₁)]
    [LocallyOfFiniteType (B.inclusion.map d₂)] [LocallyOfFiniteType (B.inclusion.map d)]
    [IsSeparated (B.inclusion.map g')] [IsSeparated (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map f'')] [IsSeparated (B.inclusion.map f')]
    [IsSeparated (B.inclusion.map f)] [IsSeparated (B.inclusion.map h')]
    [IsSeparated (B.inclusion.map h)] [IsSeparated (B.inclusion.map G)]
    [IsSeparated (B.inclusion.map H)] [IsSeparated (B.inclusion.map d₁)]
    [IsSeparated (B.inclusion.map d₂)] :
    Stacks.DerivedBaseChange.HorizontalPasteLaw
      (properSupportFactoredCompIso.{u, v} B g' g G hG)
      (properSupportFactoredCompIso.{u, v} B h' h H hH)
      (properSupportSquareIso.{u, v} B g' f'' f' h' d₁ hk₁ hl₁)
      (properSupportSquareIso.{u, v} B g f' f h d₂ hk₂ hl₂)
      (properSupportSquareIso.{u, v} B G f'' f H d hk hl) := by
  intro A
  have hd₁ : d₁ ≫ h = d := by rw [← hl₁, Category.assoc, hH, hl]
  have hd₂ : g' ≫ d₂ = d := by rw [← hk₂, ← Category.assoc, hG, hk]
  have E₁ := properSupportFactoredCompIso_assoc.{u, v} B f'' h' h d₁ H d hl₁ hH hd₁ hl A
  have E₂ := properSupportFactoredCompIso_assoc.{u, v} B g' f' h d₁ d₂ d hk₁ hl₂ hd₁ hd₂ A
  have E₃ := properSupportFactoredCompIso_assoc.{u, v} B g' g f G d₂ d hG hk₂ hk hd₂ A
  -- `E₂` and `E₃` with the inverses moved across
  have E₂' : (properSupportFunctor.{u, v} B h).map
        ((properSupportFactoredCompIso.{u, v} B g' f' d₁ hk₁).inv.app A) ≫
      (properSupportFactoredCompIso.{u, v} B f' h d₂ hl₂).hom.app
        ((properSupportFunctor.{u, v} B g').obj A) =
      (properSupportFactoredCompIso.{u, v} B d₁ h d hd₁).hom.app A ≫
        (properSupportFactoredCompIso.{u, v} B g' d₂ d hd₂).inv.app A := by
    rw [← cancel_epi ((properSupportFunctor.{u, v} B h).map
      ((properSupportFactoredCompIso.{u, v} B g' f' d₁ hk₁).hom.app A)),
      ← Functor.map_comp_assoc, reassoc_of% E₂]
    simp
  have E₃' : (properSupportFactoredCompIso.{u, v} B g f d₂ hk₂).inv.app
        ((properSupportFunctor.{u, v} B g').obj A) ≫
      (properSupportFunctor.{u, v} B f).map
        ((properSupportFactoredCompIso.{u, v} B g' g G hG).hom.app A) =
      (properSupportFactoredCompIso.{u, v} B g' d₂ d hd₂).hom.app A ≫
        (properSupportFactoredCompIso.{u, v} B G f d hk).inv.app A := by
    rw [← cancel_epi ((properSupportFactoredCompIso.{u, v} B g f d₂ hk₂).hom.app
      ((properSupportFunctor.{u, v} B g').obj A)), Iso.hom_inv_id_app_assoc,
      ← reassoc_of% E₃]
    simp
  simp only [properSupportSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% E₁.symm, reassoc_of% E₂', E₃', Iso.inv_hom_id_app_assoc]

end ProperSupport

/-! ### The identifications on abelian étale sheaves of two squares side by side -/

section Abelian

variable (B : BigEtaleSite.{u})

/-- **Stacks 0F50 for the direct image with compact support `fShriekFunctor`.** For morphisms
`a` and `b` separated and locally quasi-finite and an arrow `c` with `a ≫ b = c`, the composite
`a_! ⋙ b_!` is `c_!`: the comparison of Stacks 0F50 on the proper-support model of `f_!`, which
Stacks 0F6N identifies with `fShriekFunctor`. -/
def fShriekFunctorCompIso {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (hab : a ≫ b = c)
    [IsSeparated (B.inclusion.map a)] [LocallyQuasiFinite (B.inclusion.map a)]
    [LocallyOfFiniteType (B.inclusion.map a)]
    [IsSeparated (B.inclusion.map b)] [LocallyQuasiFinite (B.inclusion.map b)]
    [LocallyOfFiniteType (B.inclusion.map b)]
    [IsSeparated (B.inclusion.map c)] [LocallyQuasiFinite (B.inclusion.map c)]
    [LocallyOfFiniteType (B.inclusion.map c)] :
    fShriekFunctor.{u, u} B a ⋙ fShriekFunctor.{u, u} B b ≅ fShriekFunctor.{u, u} B c :=
  Functor.isoWhiskerRight (fShriekFunctorIsoProperSupport.{u, u} B a) _ ≪≫
    Functor.isoWhiskerLeft _ (fShriekFunctorIsoProperSupport.{u, u} B b) ≪≫
    properSupportFactoredCompIso.{u, u + 1} B a b c hab ≪≫
    (fShriekFunctorIsoProperSupport.{u, u} B c).symm

variable {X'' X' X Y'' Y' Y : B.Scheme}

/-- The outer rectangle of two commutative squares side by side commutes. -/
lemma rectangle_comm_horizontal {g' : X'' ⟶ X'} {g : X' ⟶ X} {f'' : X'' ⟶ Y''}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {h' : Y'' ⟶ Y'} {h : Y' ⟶ Y}
    (w₁ : g' ≫ f' = f'' ≫ h') (w₂ : g ≫ f = f' ≫ h) :
    (g' ≫ g) ≫ f = f'' ≫ h' ≫ h := by
  rw [Category.assoc, w₂, ← Category.assoc, w₁, Category.assoc]

/-- **Horizontal pasting of the identifications `f'_* ⋙ h_! ≅ g_! ⋙ f_*`** on abelian étale
sheaves, for two commutative squares `g' ≫ f' = f'' ≫ h'` and `g ≫ f = f' ≫ h` side by side:
the pasting law with respect to the comparisons `h'_! ⋙ h_! ≅ (h' ≫ h)_!` and
`g'_! ⋙ g_! ≅ (g' ≫ g)_!` of Stacks 0F50. -/
lemma pushforwardFShriekSquareIso_horizontal_paste (g' : X'' ⟶ X') (g : X' ⟶ X)
    (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
    (w₁ : g' ≫ f' = f'' ≫ h') (w₂ : g ≫ f = f' ≫ h)
    [IsProper (B.inclusion.map f'')] [IsProper (B.inclusion.map f')]
    [IsProper (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map g')] [LocallyQuasiFinite (B.inclusion.map g')]
    [LocallyOfFiniteType (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
    [LocallyOfFiniteType (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map h')] [LocallyQuasiFinite (B.inclusion.map h')]
    [LocallyOfFiniteType (B.inclusion.map h')]
    [IsSeparated (B.inclusion.map h)] [LocallyQuasiFinite (B.inclusion.map h)]
    [LocallyOfFiniteType (B.inclusion.map h)] :
    Stacks.DerivedBaseChange.HorizontalPasteLaw
      (fShriekFunctorCompIso B g' g (g' ≫ g) rfl) (fShriekFunctorCompIso B h' h (h' ≫ h) rfl)
      (pushforwardFShriekSquareIso B g' f'' f' h' w₁) (pushforwardFShriekSquareIso B g f' f h w₂)
      (pushforwardFShriekSquareIso B (g' ≫ g) f'' f (h' ≫ h) (rectangle_comm_horizontal B w₁ w₂)) :=
  Stacks.DerivedBaseChange.HorizontalPasteLaw.conj
    (fShriekFunctorIsoProperSupport.{u, u} B g') (fShriekFunctorIsoProperSupport.{u, u} B g)
    (fShriekFunctorIsoProperSupport.{u, u} B (g' ≫ g))
    (fShriekFunctorIsoProperSupport.{u, u} B h') (fShriekFunctorIsoProperSupport.{u, u} B h)
    (fShriekFunctorIsoProperSupport.{u, u} B (h' ≫ h))
    (properSupportIsoPushforward.{u, u + 1} B f'') (properSupportIsoPushforward.{u, u + 1} B f')
    (properSupportIsoPushforward.{u, u + 1} B f)
    (properSupportSquareIso_horizontal_paste.{u, u + 1} B g' g f'' f' f h' h
      (g' ≫ g) (h' ≫ h) (g' ≫ f') (g ≫ f) ((g' ≫ g) ≫ f) rfl rfl rfl w₁.symm rfl w₂.symm rfl
      (rectangle_comm_horizontal B w₁ w₂).symm)

end Abelian

/-! ### The identifications for sheaves of `Λ`-modules -/

section Module

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ]

/-- **Stacks 0F50 for the direct image with compact support with coefficients in `Λ`.** The
`Λ`-linear lift of `AlgebraicGeometry.SmallEtale.fShriekFunctorCompIso`. -/
abbrev etaleModuleLiftFShriekCompIso {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (hab : a ≫ b = c)
    [IsSeparated (B.inclusion.map a)] [LocallyQuasiFinite (B.inclusion.map a)]
    [LocallyOfFiniteType (B.inclusion.map a)]
    [IsSeparated (B.inclusion.map b)] [LocallyQuasiFinite (B.inclusion.map b)]
    [LocallyOfFiniteType (B.inclusion.map b)]
    [IsSeparated (B.inclusion.map c)] [LocallyQuasiFinite (B.inclusion.map c)]
    [LocallyOfFiniteType (B.inclusion.map c)] :
    etaleModuleLift B Λ (fShriekFunctor.{u, u} B a) ⋙
        etaleModuleLift B Λ (fShriekFunctor.{u, u} B b) ≅
      etaleModuleLift B Λ (fShriekFunctor.{u, u} B c) :=
  etaleModuleLiftCompIso B Λ (fShriekFunctor.{u, u} B a) (fShriekFunctor.{u, u} B b)
    (fShriekFunctor.{u, u} B c) (fShriekFunctorCompIso B a b c hab)

variable {X'' X' X Y'' Y' Y : B.Scheme}

/-- **Horizontal pasting of the identifications `f'_* ⋙ h_! ≅ g_! ⋙ f_*` for sheaves of
`Λ`-modules.** This is `pushforwardFShriekSquareIso_horizontal_paste` on the underlying abelian
sheaves, forgetting the `Λ`-module structure being faithful. -/
lemma pushforwardFShriekModSquareIso_horizontal_paste (g' : X'' ⟶ X') (g : X' ⟶ X)
    (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
    (w₁ : g' ≫ f' = f'' ≫ h') (w₂ : g ≫ f = f' ≫ h)
    [IsProper (B.inclusion.map f'')] [IsProper (B.inclusion.map f')]
    [IsProper (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map g')] [LocallyQuasiFinite (B.inclusion.map g')]
    [LocallyOfFiniteType (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
    [LocallyOfFiniteType (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map h')] [LocallyQuasiFinite (B.inclusion.map h')]
    [LocallyOfFiniteType (B.inclusion.map h')]
    [IsSeparated (B.inclusion.map h)] [LocallyQuasiFinite (B.inclusion.map h)]
    [LocallyOfFiniteType (B.inclusion.map h)] :
    Stacks.DerivedBaseChange.HorizontalPasteLaw
      (etaleModuleLiftFShriekCompIso B Λ g' g (g' ≫ g) rfl)
      (etaleModuleLiftFShriekCompIso B Λ h' h (h' ≫ h) rfl)
      (pushforwardFShriekModSquareIso B Λ g' f'' f' h' w₁)
      (pushforwardFShriekModSquareIso B Λ g f' f h w₂)
      (pushforwardFShriekModSquareIso B Λ (g' ≫ g) f'' f (h' ≫ h)
        (rectangle_comm_horizontal B w₁ w₂)) :=
  Stacks.DerivedBaseChange.HorizontalPasteLaw.of_faithful
    (etaleModuleLiftForgetIso B Λ (fShriekFunctor.{u, u} B g'))
    (etaleModuleLiftForgetIso B Λ (fShriekFunctor.{u, u} B g))
    (etaleModuleLiftForgetIso B Λ (fShriekFunctor.{u, u} B (g' ≫ g)))
    (etaleModuleLiftForgetIso B Λ (fShriekFunctor.{u, u} B h'))
    (etaleModuleLiftForgetIso B Λ (fShriekFunctor.{u, u} B h))
    (etaleModuleLiftForgetIso B Λ (fShriekFunctor.{u, u} B (h' ≫ h)))
    (etaleModuleLiftForgetIso B Λ (etalePushforward.{u, u + 1} B f''))
    (etaleModuleLiftForgetIso B Λ (etalePushforward.{u, u + 1} B f'))
    (etaleModuleLiftForgetIso B Λ (etalePushforward.{u, u + 1} B f))
    (forgetModuleSheaf_map_etaleModuleLiftCompIso_hom_app_conj B Λ _ _ _
      (fShriekFunctorCompIso B g' g (g' ≫ g) rfl))
    (forgetModuleSheaf_map_etaleModuleLiftCompIso_hom_app_conj B Λ _ _ _
      (fShriekFunctorCompIso B h' h (h' ≫ h) rfl))
    (forgetModuleSheaf_map_etaleModuleLiftSquareIso_hom_app_conj B Λ _ _ _ _
      (pushforwardFShriekSquareIso B g' f'' f' h' w₁))
    (forgetModuleSheaf_map_etaleModuleLiftSquareIso_hom_app_conj B Λ _ _ _ _
      (pushforwardFShriekSquareIso B g f' f h w₂))
    (forgetModuleSheaf_map_etaleModuleLiftSquareIso_hom_app_conj B Λ _ _ _ _
      (pushforwardFShriekSquareIso B (g' ≫ g) f'' f (h' ≫ h) (rectangle_comm_horizontal B w₁ w₂)))
    (pushforwardFShriekSquareIso_horizontal_paste B g' g f'' f' f h' h w₁ w₂)

end Module

/-! ### The base change maps on derived categories -/

section Derived

open Stacks.DerivedBaseChange

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X'' X' X Y'' Y' Y : B.Scheme}

/-- **[Stacks, Tag 0F7D].** Consider a commutative diagram of a big étale site
```
X'' --g'--> X' --g--> X
|           |         |
f''         f'        f
v           v         v
Y'' --h'--> Y' --h--> Y
```
with `f`, `f'` and `f''` proper and `g`, `g'`, `h` and `h'` separated and locally quasi-finite,
and let `Λ` be a ring. Then the maps of [Stacks, Tag 0F7B] for the two squares compose to the map
for the outer rectangle. Precisely, as the source states it in its proof: write
`(h' ≫ h)_! = h'_! ⋙ h_!` and `(g' ≫ g)_! = g'_! ⋙ g_!` on derived categories, through the
identifications of Stacks 0F50 (`AlgebraicGeometry.SmallEtale.etaleModuleLiftFShriekCompIso`)
induced on unbounded derived categories by `CategoryTheory.Functor.mapDerivedCategoryCompIso`;
then the map `(h' ≫ h)_! ∘ Rf''_* ⟶ Rf_* ∘ (g' ≫ g)_!` of the outer rectangle is the composite
```
h_! ∘ h'_! ∘ Rf''_* ⟶ h_! ∘ Rf'_* ∘ g'_! ⟶ Rf_* ∘ g_! ∘ g'_!
```
of the maps of the two squares. The statement holds for every choice of the three right derived
functors `Rf''_*`, `Rf'_*`, `Rf_*` of the direct images on the unbounded homotopy categories.

The source calls the maps of [Stacks, Tag 0F7B] isomorphisms; that they are is
[Stacks, Tag 0F7B] itself, whose proof rests on proper base change, [Stacks, Tag 0DDF], and it is
not used here: the content of this tag is the identity between the maps, from which the identity
between the isomorphisms follows whenever they are isomorphisms. -/
@[stacks 0F7D]
theorem properBaseChangeMap_horizontal_paste (g' : X'' ⟶ X') (g : X' ⟶ X)
    (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)
    (w₁ : g' ≫ f' = f'' ≫ h') (w₂ : g ≫ f = f' ≫ h)
    [IsProper (B.inclusion.map f'')] [IsProper (B.inclusion.map f')]
    [IsProper (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map g')] [LocallyQuasiFinite (B.inclusion.map g')]
    [LocallyOfFiniteType (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
    [LocallyOfFiniteType (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map h')] [LocallyQuasiFinite (B.inclusion.map h')]
    [LocallyOfFiniteType (B.inclusion.map h')]
    [IsSeparated (B.inclusion.map h)] [LocallyQuasiFinite (B.inclusion.map h)]
    [LocallyOfFiniteType (B.inclusion.map h)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X'' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y'' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    (RF'' : DerivedCategory (ModuleSheaf.{u, u, u} B X'' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y'' Λ))
    (αF'' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f'')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF'')
    (RF' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ))
    (αF' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    (RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
    (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF''.IsRightDerivedFunctor αF''
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X'' Λ) (ComplexShape.up ℤ))]
    [RF'.IsRightDerivedFunctor αF'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))] :
    properBaseChangeMap B Λ (g' ≫ g) f'' f (h' ≫ h) (rectangle_comm_horizontal B w₁ w₂)
        RF'' αF'' RF αF =
      Functor.whiskerLeft RF''
          (Functor.mapDerivedCategoryCompIso
            (etaleModuleLiftFShriekCompIso B Λ h' h (h' ≫ h) rfl)).inv ≫
        (Functor.associator RF''
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B h')).mapDerivedCategory
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B h)).mapDerivedCategory).inv ≫
        Functor.whiskerRight (properBaseChangeMap B Λ g' f'' f' h' w₁ RF'' αF'' RF' αF')
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B h)).mapDerivedCategory ≫
        (Functor.associator
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B g')).mapDerivedCategory RF'
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B h)).mapDerivedCategory).hom ≫
        Functor.whiskerLeft
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B g')).mapDerivedCategory
          (properBaseChangeMap B Λ g f' f h w₂ RF' αF' RF αF) ≫
        (Functor.associator
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B g')).mapDerivedCategory
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B g)).mapDerivedCategory RF).inv ≫
        Functor.whiskerRight
          (Functor.mapDerivedCategoryCompIso
            (etaleModuleLiftFShriekCompIso B Λ g' g (g' ≫ g) rfl)).hom RF := by
  have := isRightDerivedFunctor_comp_right _ RF'' αF''
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B h')).mapDerivedCategory
  have := isRightDerivedFunctor_comp_right _ RF' αF'
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B h)).mapDerivedCategory
  have := isRightDerivedFunctor_comp_right _ RF'' αF''
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B (h' ≫ h))).mapDerivedCategory
  exact squareMap_horizontal_paste
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X'' Λ) (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B g')).mapDerivedCategoryFactorsh
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B g)).mapDerivedCategoryFactorsh
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B (g' ≫ g))).mapDerivedCategoryFactorsh
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B h')).mapDerivedCategoryFactorsh
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B h)).mapDerivedCategoryFactorsh
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B (h' ≫ h))).mapDerivedCategoryFactorsh
    αF'' αF' αF
    (Functor.mapHomotopyCategoryCompIso (etaleModuleLiftFShriekCompIso B Λ g' g (g' ≫ g) rfl)
      (ComplexShape.up ℤ))
    (Functor.mapHomotopyCategoryCompIso (etaleModuleLiftFShriekCompIso B Λ h' h (h' ≫ h) rfl)
      (ComplexShape.up ℤ))
    (Functor.mapDerivedCategoryCompIso (etaleModuleLiftFShriekCompIso B Λ g' g (g' ≫ g) rfl))
    (Functor.mapDerivedCategoryCompIso (etaleModuleLiftFShriekCompIso B Λ h' h (h' ≫ h) rfl))
    (Functor.mapDerivedCategoryCompIso_hom_app_Qh
      (etaleModuleLiftFShriekCompIso B Λ g' g (g' ≫ g) rfl))
    (Functor.mapDerivedCategoryCompIso_hom_app_Qh
      (etaleModuleLiftFShriekCompIso B Λ h' h (h' ≫ h) rfl))
    (homotopySquareIso (ComplexShape.up ℤ) (pushforwardFShriekModSquareIso B Λ g' f'' f' h' w₁))
    (homotopySquareIso (ComplexShape.up ℤ) (pushforwardFShriekModSquareIso B Λ g f' f h w₂))
    (homotopySquareIso (ComplexShape.up ℤ) (pushforwardFShriekModSquareIso B Λ (g' ≫ g) f'' f
      (h' ≫ h) (rectangle_comm_horizontal B w₁ w₂)))
    (homotopySquareIso_horizontal_paste (ComplexShape.up ℤ)
      (pushforwardFShriekModSquareIso_horizontal_paste B Λ g' g f'' f' f h' h w₁ w₂))

end Derived

end AlgebraicGeometry.SmallEtale

end
