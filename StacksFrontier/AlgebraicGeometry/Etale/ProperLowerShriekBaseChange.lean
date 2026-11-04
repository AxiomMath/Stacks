module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekAssociativity
public import StacksFrontier.CategoryTheory.Functor.Derived.BaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftAdjunction

import StacksCore.Tactic.StacksAttribute

/-!
# The base change map `l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` and its compatibility with pasting

Consider a commutative square of a big étale site
```
X' --k--> X
|         |
f'        f
v         v
Y' --l--> Y
```
with `f` and `f'` proper and `k` and `l` separated and locally quasi-finite. The isomorphisms
`l_! f'_* = l_! f'_! = (f' ≫ l)_! = (k ≫ f)_! = f_! k_! = f_* k_!` of Stacks 0F51 and Stacks 0F50
identify `f'_* ⋙ l_!` with `k_! ⋙ f_*` on étale sheaves, and through the universal property of
the right derived functor `Rf'_*` they induce the map
```
l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!
```
of functors `D(X'_étale, Λ) ⥤ D(Y_étale, Λ)` of [Stacks, Tag 0F7B]. This file constructs that
map, for coefficients in a ring `Λ`, and proves [Stacks, Tag 0F7C]: for two such squares on top
of each other, the maps of the two squares compose to the map of the outer rectangle.

## Main definitions

* `AlgebraicGeometry.SmallEtale.properSupportSquareIso`: the identification
  `f'_! ⋙ l_! ≅ k_! ⋙ f_!` of proper-support direct images through `(f' ≫ l)_! = (k ≫ f)_!`.
* `AlgebraicGeometry.SmallEtale.pushforwardFShriekSquareIso`: the identification
  `f'_* ⋙ l_! ≅ k_! ⋙ f_*` on abelian étale sheaves, and
  `AlgebraicGeometry.SmallEtale.pushforwardFShriekModSquareIso` its `Λ`-linear lift.
* `AlgebraicGeometry.SmallEtale.properBaseChangeMap`: the map `l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` of
  [Stacks, Tag 0F7B].

## Main results

* `AlgebraicGeometry.SmallEtale.properBaseChangeMap_fac_app`: the characterization of the
  map through the unit of `Rf'_*`.
* `AlgebraicGeometry.SmallEtale.properBaseChangeMap_vertical_paste`: the pasting identity, through
  the comparisons `R(g ∘ f)_* ⟶ Rg_* ∘ Rf_*`.
* `AlgebraicGeometry.SmallEtale.isIso_compComparison_etalePushforwardMod`: those comparisons are
  isomorphisms, direct image preserving K-injective complexes
  (`AlgebraicGeometry.SmallEtale.isKInjective_etalePushforwardMod`).
* `AlgebraicGeometry.SmallEtale.properBaseChangeMap_rectangle_eq_comp`: **[Stacks, Tag 0F7C]**:
  with `R(g ∘ f)_* = Rg_* ∘ Rf_*`, the map of the rectangle is the composite of the maps of the
  squares.

## Implementation notes

The direct images `Rf_*` are arbitrary right derived functors of the degreewise direct image on
the unbounded homotopy categories, with their units; every statement holds for every such
choice. The lower shrieks `k_!` are exact (Stacks 0F5F) and are taken on derived categories as
`Functor.mapDerivedCategory` of the `Λ`-linear direct image with compact support, the lift
`etaleModuleLift B Λ (fShriekFunctor B k)`, which is `AlgebraicGeometry.SmallEtale.fShriekMod`
by definition (`AlgebraicGeometry.SmallEtale.fShriekMod_eq_etaleModuleLift`). The lift is
written out, and abelian étale sheaves are written as `Sheaf (SmallEtale.topology B X.obj
X.property) AddCommGrpCat` rather than through the abbreviations `fShriekMod`,
`etalePushforwardMod` and `AbelianSheaf`, because the statements here are instances of abstract
ones over functor variables, and the two spellings, although definitionally equal, cost the
elaborator and the kernel more than the heartbeat budget to identify at this size. Because the
source is a Grothendieck abelian category,
the composite `Rf'_* ⋙ l_!` is again a right derived functor
(`Stacks.DerivedBaseChange.isRightDerivedFunctor_comp_right`), which is what makes the map
defined; no K-injective resolution is chosen.

The underived identification is first built on the proper-support model `properSupportFunctor`
of `f_!`, where it is a composite of Stacks 0F50 isomorphisms, and its compatibility with
pasting is Stacks 0F77. It is then transported to the model `fShriekFunctor` of `f_!` used for
`k_!` and `l_!` by Stacks 0F6N, and to the ordinary direct images along the proper morphisms by
Stacks 0F51, and finally lifted to sheaves of `Λ`-modules.

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F7C](https://stacks.math.columbia.edu/tag/0F7C)
* [Stacks Project, Tag 0F50](https://stacks.math.columbia.edu/tag/0F50)
* [Stacks Project, Tag 0F51](https://stacks.math.columbia.edu/tag/0F51)
* [Stacks Project, Tag 0F77](https://stacks.math.columbia.edu/tag/0F77)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace AlgebraicGeometry.SmallEtale

/-! ### The proper-support identification of a square -/

section ProperSupport

variable (B : BigEtaleSite.{u})

/-- Stacks 0F50 for a composite presented by an arbitrary arrow `h` with `a ≫ b = h`. -/
def properSupportFactoredCompIso {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z) (h : X ⟶ Z)
    (hab : a ≫ b = h) [LocallyOfFiniteType (B.inclusion.map a)]
    [LocallyOfFiniteType (B.inclusion.map b)] [LocallyOfFiniteType (B.inclusion.map h)]
    [IsSeparated (B.inclusion.map a)] [IsSeparated (B.inclusion.map b)] :
    properSupportFunctor.{u, v} B a ⋙ properSupportFunctor.{u, v} B b ≅
      properSupportFunctor.{u, v} B h :=
  (properSupportFunctor_compIso.{u, v} B a b).val ≪≫ eqToIso (by subst hab; rfl)

/-- The associativity of Stacks 0F50, Stacks 0F77, for composites presented by arbitrary
arrows. -/
lemma properSupportFactoredCompIso_assoc {X Y Z T : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ T) (ab : X ⟶ Z) (bc : Y ⟶ T) (h : X ⟶ T) (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (h₁ : ab ≫ c = h) (h₂ : a ≫ bc = h)
    [LocallyOfFiniteType (B.inclusion.map a)] [LocallyOfFiniteType (B.inclusion.map b)]
    [LocallyOfFiniteType (B.inclusion.map c)] [LocallyOfFiniteType (B.inclusion.map ab)]
    [LocallyOfFiniteType (B.inclusion.map bc)] [LocallyOfFiniteType (B.inclusion.map h)]
    [IsSeparated (B.inclusion.map a)] [IsSeparated (B.inclusion.map b)]
    [IsSeparated (B.inclusion.map c)] [IsSeparated (B.inclusion.map ab)]
    [IsSeparated (B.inclusion.map bc)] (A) :
    (properSupportFunctor.{u, v} B c).map
        ((properSupportFactoredCompIso.{u, v} B a b ab hab).hom.app A) ≫
      (properSupportFactoredCompIso.{u, v} B ab c h h₁).hom.app A =
    (properSupportFactoredCompIso.{u, v} B b c bc hbc).hom.app
        ((properSupportFunctor.{u, v} B a).obj A) ≫
      (properSupportFactoredCompIso.{u, v} B a bc h h₂).hom.app A := by
  subst hab hbc h₁
  have h0 := congrArg (fun e => e.hom.app A) (properSupportFunctor_compIso_assoc B a b c)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp] at h0
  simp only [properSupportFactoredCompIso, Iso.trans_hom, NatTrans.comp_app, eqToIso_refl,
    Iso.refl_hom, Category.comp_id, eqToIso.hom, eqToHom_app]
  simp only [eqToIso.hom, eqToHom_app] at h0
  exact h0

variable {X' X Y' Y : B.Scheme}

/-- **The proper-support identification of a square.** For a commutative square
`k ≫ f = f' ≫ l` of morphisms separated and locally of finite type, the composite
`f'_! ⋙ l_! ≅ (f' ≫ l)_! = (k ≫ f)_! ≅ k_! ⋙ f_!` of Stacks 0F50 isomorphisms of
proper-support direct images, read through an arbitrary diagonal `h`. -/
def properSupportSquareIso (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y) (h : X' ⟶ Y)
    (hk : k ≫ f = h) (hl : f' ≫ l = h)
    [LocallyOfFiniteType (B.inclusion.map k)] [LocallyOfFiniteType (B.inclusion.map f')]
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map h)]
    [IsSeparated (B.inclusion.map k)] [IsSeparated (B.inclusion.map f')]
    [IsSeparated (B.inclusion.map f)] [IsSeparated (B.inclusion.map l)] :
    properSupportFunctor.{u, v} B f' ⋙ properSupportFunctor.{u, v} B l ≅
      properSupportFunctor.{u, v} B k ⋙ properSupportFunctor.{u, v} B f :=
  properSupportFactoredCompIso.{u, v} B f' l h hl ≪≫
    (properSupportFactoredCompIso.{u, v} B k f h hk).symm

variable {Z' Z : B.Scheme}

/-- **Vertical pasting of the proper-support identifications.** For two commutative squares
`k ≫ f = f' ≫ l` and `l ≫ g = g' ≫ m` on top of each other, the identification of the outer
rectangle, preceded by Stacks 0F50 for `f' ≫ g'` and followed by Stacks 0F50 for `f ≫ g`, is
the identification of the lower square followed by that of the upper square. -/
lemma properSupportSquareIso_vertical_paste (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (l : Y' ⟶ Y) (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z) (p' : X' ⟶ Z') (p : X ⟶ Z)
    (h₁ : X' ⟶ Y) (h₂ : Y' ⟶ Z) (h : X' ⟶ Z)
    (hp' : f' ≫ g' = p') (hp : f ≫ g = p) (hk₁ : k ≫ f = h₁) (hl₁ : f' ≫ l = h₁)
    (hl₂ : l ≫ g = h₂) (hm₂ : g' ≫ m = h₂) (hk : k ≫ p = h) (hm : p' ≫ m = h)
    [LocallyOfFiniteType (B.inclusion.map k)] [LocallyOfFiniteType (B.inclusion.map f')]
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map g')] [LocallyOfFiniteType (B.inclusion.map g)]
    [LocallyOfFiniteType (B.inclusion.map m)] [LocallyOfFiniteType (B.inclusion.map p')]
    [LocallyOfFiniteType (B.inclusion.map p)] [LocallyOfFiniteType (B.inclusion.map h₁)]
    [LocallyOfFiniteType (B.inclusion.map h₂)] [LocallyOfFiniteType (B.inclusion.map h)]
    [IsSeparated (B.inclusion.map k)] [IsSeparated (B.inclusion.map f')]
    [IsSeparated (B.inclusion.map f)] [IsSeparated (B.inclusion.map l)]
    [IsSeparated (B.inclusion.map g')] [IsSeparated (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map m)] [IsSeparated (B.inclusion.map p')]
    [IsSeparated (B.inclusion.map p)] [IsSeparated (B.inclusion.map h₁)]
    [IsSeparated (B.inclusion.map h₂)] (A) :
    (properSupportFunctor.{u, v} B m).map
        ((properSupportFactoredCompIso.{u, v} B f' g' p' hp').hom.app A) ≫
      (properSupportSquareIso.{u, v} B k p' p m h hk hm).hom.app A =
    (properSupportSquareIso.{u, v} B l g' g m h₂ hl₂ hm₂).hom.app
        ((properSupportFunctor.{u, v} B f').obj A) ≫
      (properSupportFunctor.{u, v} B g).map
        ((properSupportSquareIso.{u, v} B k f' f l h₁ hk₁ hl₁).hom.app A) ≫
      (properSupportFactoredCompIso.{u, v} B f g p hp).hom.app
        ((properSupportFunctor.{u, v} B k).obj A) := by
  subst hp' hp hk₁ hl₂ hk
  have hd : f' ≫ l ≫ g = k ≫ f ≫ g := by rw [← Category.assoc, hl₁, Category.assoc]
  have e₁ := properSupportFactoredCompIso_assoc.{u, v} B f' g' m _ _ _ rfl hm₂ hm hd A
  have e₂ := properSupportFactoredCompIso_assoc.{u, v} B k f g _ _ _ rfl rfl
    (Category.assoc _ _ _) rfl A
  have e₃ := properSupportFactoredCompIso_assoc.{u, v} B f' l g _ _ _ hl₁ rfl
    (Category.assoc _ _ _) hd A
  simp only [properSupportSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  have hT : (properSupportFactoredCompIso.{u, v} B f g (f ≫ g) rfl).hom.app
        ((properSupportFunctor.{u, v} B k).obj A) =
      (properSupportFunctor.{u, v} B g).map
          ((properSupportFactoredCompIso.{u, v} B k f (k ≫ f) rfl).hom.app A) ≫
        (properSupportFactoredCompIso.{u, v} B (k ≫ f) g (k ≫ f ≫ g)
          (Category.assoc _ _ _)).hom.app A ≫
        (properSupportFactoredCompIso.{u, v} B k (f ≫ g) (k ≫ f ≫ g) rfl).inv.app A := by
    rw [reassoc_of% e₂]
    simp
  rw [reassoc_of% e₁, hT]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [reassoc_of% e₃]
  simp

end ProperSupport

/-! ### The identification `f'_* ⋙ l_! ≅ k_! ⋙ f_*` on abelian étale sheaves -/

section Abelian

variable (B : BigEtaleSite.{u})

/-- A composite of proper morphisms of a big étale site is proper. -/
instance isProper_inclusion_map_comp {X Y Z : B.Scheme} {a : X ⟶ Y} {b : Y ⟶ Z}
    [IsProper (B.inclusion.map a)] [IsProper (B.inclusion.map b)] :
    IsProper (B.inclusion.map (a ≫ b)) := by
  change IsProper (B.inclusion.map a ≫ B.inclusion.map b)
  infer_instance

/-- The characterizing square of Stacks 0F50: the comparison of proper-support direct images,
followed by the inclusion into the direct image along the composite, is the iterated inclusion
followed by the comparison of direct images. -/
lemma properSupportFactoredCompIso_hom_app_arrow {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z)
    [LocallyOfFiniteType (B.inclusion.map a)] [LocallyOfFiniteType (B.inclusion.map b)]
    [IsSeparated (B.inclusion.map a)] [IsSeparated (B.inclusion.map b)]
    (A : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v}) :
    (properSupportFactoredCompIso.{u, v} B a b (a ≫ b) rfl).hom.app A ≫
        (fShriekSubsheaf B (a ≫ b) A).val.arrow =
      (fShriekSubsheaf B b ((properSupportFunctor.{u, v} B a).obj A)).val.arrow ≫
        (etalePushforward.{u, v} B b).map (fShriekSubsheaf B a A).val.arrow ≫
        (smallEtaleSheafPushforwardCompIso B X Y Z a b
          AddCommGrpCat.{v}).hom.app A := by
  have h := (properSupportSheaf_compIso.{u, v} B a b A).property
  simp only [properSupportFactoredCompIso, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id]
  exact h

variable {X' X Y' Y : B.Scheme}

/-- **The identification `f'_* ⋙ l_! ≅ k_! ⋙ f_*` of a square**, for a commutative square
`k ≫ f = f' ≫ l` with `f`, `f'` proper and `k`, `l` separated and locally quasi-finite, on
abelian étale sheaves: `l_! f'_* = l_! f'_! = (f' ≫ l)_! = (k ≫ f)_! = f_! k_! = f_* k_!`, by
Stacks 0F51 and Stacks 0F50 on the proper-support model of `f_!`, which Stacks 0F6N identifies
with the direct image with compact support `fShriekFunctor` used for `k_!` and `l_!`. -/
def pushforwardFShriekSquareIso (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
    (w : k ≫ f = f' ≫ l) [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)] :
    etalePushforward.{u, u + 1} B f' ⋙ fShriekFunctor.{u, u} B l ≅
      fShriekFunctor.{u, u} B k ⋙ etalePushforward.{u, u + 1} B f :=
  Stacks.DerivedBaseChange.squareIsoTransport (properSupportIsoPushforward.{u, u + 1} B f')
    (properSupportIsoPushforward.{u, u + 1} B f) (fShriekFunctorIsoProperSupport.{u, u} B k)
    (fShriekFunctorIsoProperSupport.{u, u} B l)
    (properSupportSquareIso.{u, u + 1} B k f' f l (k ≫ f) rfl w.symm)

variable {Z' Z : B.Scheme}

/-- The outer rectangle of two commutative squares on top of each other commutes. -/
lemma rectangle_comm {k : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {l : Y' ⟶ Y} {g' : Y' ⟶ Z'}
    {g : Y ⟶ Z} {m : Z' ⟶ Z} (w₁ : k ≫ f = f' ≫ l) (w₂ : l ≫ g = g' ≫ m) :
    k ≫ f ≫ g = (f' ≫ g') ≫ m := by
  rw [← Category.assoc, w₁, Category.assoc, w₂, Category.assoc]

/-- **Vertical pasting of the identifications `f'_* ⋙ l_! ≅ k_! ⋙ f_*`.** For two commutative
squares `k ≫ f = f' ≫ l` and `l ≫ g = g' ≫ m` on top of each other, the identification of the
outer rectangle, preceded by the comparison `g'_* f'_* ≅ (f' ≫ g')_*`, is the identification of
the lower square followed by that of the upper square and the comparison `g_* f_* ≅ (f ≫ g)_*`.
-/
lemma pushforwardFShriekSquareIso_vertical_paste (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (l : Y' ⟶ Y) (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z)
    (w₁ : k ≫ f = f' ≫ l) (w₂ : l ≫ g = g' ≫ m)
    [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
    [IsProper (B.inclusion.map g')] [IsProper (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    [IsSeparated (B.inclusion.map m)] [LocallyQuasiFinite (B.inclusion.map m)]
    [LocallyOfFiniteType (B.inclusion.map m)]
    (F : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1}) :
    (fShriekFunctor.{u, u} B m).map ((smallEtaleSheafPushforwardCompIso B X' Y' Z' f' g'
          AddCommGrpCat.{u + 1}).hom.app F) ≫
      (pushforwardFShriekSquareIso B k (f' ≫ g') (f ≫ g) m (rectangle_comm B w₁ w₂)).hom.app F =
    (pushforwardFShriekSquareIso B l g' g m w₂).hom.app ((etalePushforward.{u, u + 1} B f').obj F) ≫
      (etalePushforward.{u, u + 1} B g).map
        ((pushforwardFShriekSquareIso B k f' f l w₁).hom.app F) ≫
      (smallEtaleSheafPushforwardCompIso B X Y Z f g
          AddCommGrpCat.{u + 1}).hom.app ((fShriekFunctor.{u, u} B k).obj F) := by
  have h1 := Stacks.DerivedBaseChange.squareIsoTransport_vertical_paste
    (properSupportIsoPushforward.{u, u + 1} B f') (properSupportIsoPushforward.{u, u + 1} B f)
    (fShriekFunctorIsoProperSupport.{u, u} B k) (fShriekFunctorIsoProperSupport.{u, u} B l)
    (properSupportIsoPushforward.{u, u + 1} B g') (properSupportIsoPushforward.{u, u + 1} B g)
    (fShriekFunctorIsoProperSupport.{u, u} B m)
    (properSupportIsoPushforward.{u, u + 1} B (f' ≫ g'))
    (properSupportIsoPushforward.{u, u + 1} B (f ≫ g))
    (properSupportSquareIso.{u, u + 1} B k f' f l (k ≫ f) rfl w₁.symm)
    (properSupportSquareIso.{u, u + 1} B l g' g m (l ≫ g) rfl w₂.symm)
    (properSupportSquareIso.{u, u + 1} B k (f' ≫ g') (f ≫ g) m (k ≫ f ≫ g) rfl
      (rectangle_comm B w₁ w₂).symm)
    (properSupportFactoredCompIso.{u, u + 1} B f' g' (f' ≫ g') rfl)
    (properSupportFactoredCompIso.{u, u + 1} B f g (f ≫ g) rfl)
    (smallEtaleSheafPushforwardCompIso B X' Y' Z' f' g' AddCommGrpCat.{u + 1})
    (smallEtaleSheafPushforwardCompIso B X Y Z f g AddCommGrpCat.{u + 1})
    (properSupportFactoredCompIso_hom_app_arrow.{u, u + 1} B f' g')
    (properSupportFactoredCompIso_hom_app_arrow.{u, u + 1} B f g)
    (properSupportSquareIso_vertical_paste.{u, u + 1} B k f' f l g' g m (f' ≫ g') (f ≫ g)
      (k ≫ f) (l ≫ g) (k ≫ f ≫ g) rfl rfl rfl w₁.symm rfl w₂.symm rfl
      (rectangle_comm B w₁ w₂).symm) F
  have e1 : pushforwardFShriekSquareIso B k f' f l w₁ =
      Stacks.DerivedBaseChange.squareIsoTransport (properSupportIsoPushforward.{u, u + 1} B f')
        (properSupportIsoPushforward.{u, u + 1} B f) (fShriekFunctorIsoProperSupport.{u, u} B k)
        (fShriekFunctorIsoProperSupport.{u, u} B l)
        (properSupportSquareIso.{u, u + 1} B k f' f l (k ≫ f) rfl w₁.symm) := rfl
  have e3 : pushforwardFShriekSquareIso B k (f' ≫ g') (f ≫ g) m (rectangle_comm B w₁ w₂) =
      Stacks.DerivedBaseChange.squareIsoTransport
        (properSupportIsoPushforward.{u, u + 1} B (f' ≫ g'))
        (properSupportIsoPushforward.{u, u + 1} B (f ≫ g))
        (fShriekFunctorIsoProperSupport.{u, u} B k) (fShriekFunctorIsoProperSupport.{u, u} B m)
        (properSupportSquareIso.{u, u + 1} B k (f' ≫ g') (f ≫ g) m (k ≫ f ≫ g) rfl
          (rectangle_comm B w₁ w₂).symm) := rfl
  have e2 : pushforwardFShriekSquareIso B l g' g m w₂ =
      Stacks.DerivedBaseChange.squareIsoTransport (properSupportIsoPushforward.{u, u + 1} B g')
        (properSupportIsoPushforward.{u, u + 1} B g) (fShriekFunctorIsoProperSupport.{u, u} B l)
        (fShriekFunctorIsoProperSupport.{u, u} B m)
        (properSupportSquareIso.{u, u + 1} B l g' g m (l ≫ g) rfl w₂.symm) := rfl
  rw [e1, e2, e3]
  exact h1

end Abelian

/-! ### Sheaves of `Λ`-modules -/

section Module

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ]

section Lift

variable {X₁ X₂ X₃ X₄ : B.Scheme}
  (G₁ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
    Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1}) [G₁.Additive]
  (G₂ : Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1} ⥤
    Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [G₂.Additive]
  (G₃ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
    Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1}) [G₃.Additive]
  (G₄ : Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1} ⥤
    Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [G₄.Additive]
  (H : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
    Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [H.Additive]

/-- The `Λ`-linear lift of an isomorphism `G₁ ⋙ G₂ ≅ H`, as an isomorphism out of the composite
of the lifts. -/
def etaleModuleLiftCompIso (e : G₁ ⋙ G₂ ≅ H) :
    etaleModuleLift B Λ G₁ ⋙ etaleModuleLift B Λ G₂ ≅ etaleModuleLift B Λ H :=
  eqToIso (etaleModuleLift_comp B Λ G₁ G₂).symm ≪≫ etaleModuleLiftNatIso B Λ _ _ e

/-- The `Λ`-linear lift of an isomorphism `G₁ ⋙ G₂ ≅ G₃ ⋙ G₄` of a square, as an isomorphism
between composites of lifts. -/
def etaleModuleLiftSquareIso (e : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄) :
    etaleModuleLift B Λ G₁ ⋙ etaleModuleLift B Λ G₂ ≅
      etaleModuleLift B Λ G₃ ⋙ etaleModuleLift B Λ G₄ :=
  etaleModuleLiftCompIso B Λ G₁ G₂ _ e ≪≫ eqToIso (etaleModuleLift_comp B Λ G₃ G₄)

/-- On underlying abelian sheaves, the lift of `e : G₁ ⋙ G₂ ≅ H` is `e`. -/
lemma forgetModuleSheaf_map_etaleModuleLiftCompIso_hom_app (e : G₁ ⋙ G₂ ≅ H)
    (F : ModuleSheaf.{u, u, u} B X₁ Λ) :
    (forgetModuleSheaf.{u, u, u} B X₄ Λ).map ((etaleModuleLiftCompIso B Λ G₁ G₂ H e).hom.app F) =
      e.hom.app ((forgetModuleSheaf.{u, u, u} B X₁ Λ).obj F) := by
  have h : (eqToHom (etaleModuleLift_comp B Λ G₁ G₂).symm).app F = 𝟙 _ := rfl
  simp only [etaleModuleLiftCompIso, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app]
  rw [h]
  exact (congrArg (forgetModuleSheaf.{u, u, u} B X₄ Λ).map (Category.id_comp _)).trans rfl

/-- On underlying abelian sheaves, the lift of `e : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄` is `e`. -/
lemma forgetModuleSheaf_map_etaleModuleLiftSquareIso_hom_app (e : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄)
    (F : ModuleSheaf.{u, u, u} B X₁ Λ) :
    (forgetModuleSheaf.{u, u, u} B X₄ Λ).map
        ((etaleModuleLiftSquareIso B Λ G₁ G₂ G₃ G₄ e).hom.app F) =
      e.hom.app ((forgetModuleSheaf.{u, u, u} B X₁ Λ).obj F) := by
  have h : (eqToHom (etaleModuleLift_comp B Λ G₃ G₄)).app F = 𝟙 _ := rfl
  simp only [etaleModuleLiftSquareIso, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app]
  rw [h]
  exact (congrArg (forgetModuleSheaf.{u, u, u} B X₄ Λ).map (Category.comp_id _)).trans
    (forgetModuleSheaf_map_etaleModuleLiftCompIso_hom_app B Λ G₁ G₂ _ e F)

/-- Forgetting the `Λ`-module structure after the lift of `G₁` is `G₁` after forgetting. -/
abbrev etaleModuleLiftForgetIso :
    etaleModuleLift B Λ G₁ ⋙ forgetModuleSheaf.{u, u, u} B X₂ Λ ≅
      forgetModuleSheaf.{u, u, u} B X₁ Λ ⋙ G₁ :=
  Iso.refl _

/-- `etaleModuleLiftSquareIso` lifts the isomorphism of a square, in the sense of
`Stacks.DerivedBaseChange.vertical_paste_of_faithful`. -/
lemma forgetModuleSheaf_map_etaleModuleLiftSquareIso_hom_app_conj (e : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄)
    (F : ModuleSheaf.{u, u, u} B X₁ Λ) :
    (forgetModuleSheaf.{u, u, u} B X₄ Λ).map
        ((etaleModuleLiftSquareIso B Λ G₁ G₂ G₃ G₄ e).hom.app F) =
      (etaleModuleLiftForgetIso B Λ G₂).hom.app ((etaleModuleLift B Λ G₁).obj F) ≫
        G₂.map ((etaleModuleLiftForgetIso B Λ G₁).hom.app F) ≫
        e.hom.app ((forgetModuleSheaf.{u, u, u} B X₁ Λ).obj F) ≫
        G₄.map ((etaleModuleLiftForgetIso B Λ G₃).inv.app F) ≫
        (etaleModuleLiftForgetIso B Λ G₄).inv.app ((etaleModuleLift B Λ G₃).obj F) := by
  rw [forgetModuleSheaf_map_etaleModuleLiftSquareIso_hom_app]
  simp only [etaleModuleLiftForgetIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, G₂.map_id, Category.id_comp, G₄.map_id, Category.id_comp,
    Category.comp_id]

/-- `etaleModuleLiftCompIso` lifts the comparison of a composite, in the sense of
`Stacks.DerivedBaseChange.vertical_paste_of_faithful`. -/
lemma forgetModuleSheaf_map_etaleModuleLiftCompIso_hom_app_conj (e : G₁ ⋙ G₂ ≅ H)
    (F : ModuleSheaf.{u, u, u} B X₁ Λ) :
    (forgetModuleSheaf.{u, u, u} B X₄ Λ).map
        ((etaleModuleLiftCompIso B Λ G₁ G₂ H e).hom.app F) =
      (etaleModuleLiftForgetIso B Λ G₂).hom.app ((etaleModuleLift B Λ G₁).obj F) ≫
        G₂.map ((etaleModuleLiftForgetIso B Λ G₁).hom.app F) ≫
        e.hom.app ((forgetModuleSheaf.{u, u, u} B X₁ Λ).obj F) ≫
        (etaleModuleLiftForgetIso B Λ H).inv.app F := by
  rw [forgetModuleSheaf_map_etaleModuleLiftCompIso_hom_app]
  simp only [etaleModuleLiftForgetIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, G₂.map_id, Category.id_comp, Category.comp_id]

variable {X₅ X₆ : B.Scheme}

/-- **Vertical pasting is inherited by the `Λ`-linear lifts.** If isomorphisms of additive
functors on abelian étale sheaves paste, so do their `Λ`-linear lifts; forgetting the
`Λ`-module structure is faithful. -/
lemma etaleModuleLiftSquareIso_vertical_paste
    {F' : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1}} [F'.Additive]
    {F : Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}} [F.Additive]
    {K : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1}} [K.Additive]
    {L : Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}} [L.Additive]
    {G' : Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₅.obj X₅.property) AddCommGrpCat.{u + 1}} [G'.Additive]
    {G : Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₆.obj X₆.property) AddCommGrpCat.{u + 1}} [G.Additive]
    {M : Sheaf (SmallEtale.topology B X₅.obj X₅.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₆.obj X₆.property) AddCommGrpCat.{u + 1}} [M.Additive]
    {P' : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₅.obj X₅.property) AddCommGrpCat.{u + 1}} [P'.Additive]
    {P : Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₆.obj X₆.property) AddCommGrpCat.{u + 1}} [P.Additive]
    (e₁ : F' ⋙ L ≅ K ⋙ F) (e₂ : G' ⋙ M ≅ L ⋙ G) (e : P' ⋙ M ≅ K ⋙ P) (d' : F' ⋙ G' ≅ P')
    (d : F ⋙ G ≅ P)
    (h : ∀ A, M.map (d'.hom.app A) ≫ e.hom.app A =
      e₂.hom.app (F'.obj A) ≫ G.map (e₁.hom.app A) ≫ d.hom.app (K.obj A))
    (A : ModuleSheaf.{u, u, u} B X₁ Λ) :
    (etaleModuleLift B Λ M).map ((etaleModuleLiftCompIso B Λ F' G' P' d').hom.app A) ≫
        (etaleModuleLiftSquareIso B Λ P' M K P e).hom.app A =
      (etaleModuleLiftSquareIso B Λ G' M L G e₂).hom.app ((etaleModuleLift B Λ F').obj A) ≫
        (etaleModuleLift B Λ G).map ((etaleModuleLiftSquareIso B Λ F' L K F e₁).hom.app A) ≫
        (etaleModuleLiftCompIso B Λ F G P d).hom.app ((etaleModuleLift B Λ K).obj A) :=
  Stacks.DerivedBaseChange.vertical_paste_of_faithful
    (etaleModuleLiftForgetIso B Λ F') (etaleModuleLiftForgetIso B Λ F)
    (etaleModuleLiftForgetIso B Λ K) (etaleModuleLiftForgetIso B Λ L)
    (etaleModuleLiftForgetIso B Λ G') (etaleModuleLiftForgetIso B Λ G)
    (etaleModuleLiftForgetIso B Λ M) (etaleModuleLiftForgetIso B Λ P')
    (etaleModuleLiftForgetIso B Λ P)
    (etaleModuleLiftSquareIso B Λ F' L K F e₁) (etaleModuleLiftSquareIso B Λ G' M L G e₂)
    (etaleModuleLiftSquareIso B Λ P' M K P e) (etaleModuleLiftCompIso B Λ F' G' P' d')
    (etaleModuleLiftCompIso B Λ F G P d) e₁ e₂ e d' d
    (forgetModuleSheaf_map_etaleModuleLiftSquareIso_hom_app_conj B Λ F' L K F e₁)
    (forgetModuleSheaf_map_etaleModuleLiftSquareIso_hom_app_conj B Λ G' M L G e₂)
    (forgetModuleSheaf_map_etaleModuleLiftSquareIso_hom_app_conj B Λ P' M K P e)
    (forgetModuleSheaf_map_etaleModuleLiftCompIso_hom_app_conj B Λ F' G' P' d')
    (forgetModuleSheaf_map_etaleModuleLiftCompIso_hom_app_conj B Λ F G P d) h A

end Lift

/-- The comparison `f_* ⋙ g_* ≅ (f ≫ g)_*` of direct images of sheaves of `Λ`-modules: the
`Λ`-linear lift of Stacks 021J for abelian sheaves. -/
abbrev etalePushforwardModCompIso {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f) ⋙
        etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g) ≅
      etaleModuleLift B Λ (etalePushforward.{u, u + 1} B (f ≫ g)) :=
  etaleModuleLiftCompIso B Λ _ _ _
    (smallEtaleSheafPushforwardCompIso B X Y Z f g AddCommGrpCat.{u + 1})

variable {X' X Y' Y : B.Scheme}

/-- **The identification `f'_* ⋙ l_! ≅ k_! ⋙ f_*` of a square, for sheaves of `Λ`-modules**:
the `Λ`-linear lift of `AlgebraicGeometry.SmallEtale.pushforwardFShriekSquareIso`. -/
abbrev pushforwardFShriekModSquareIso (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
    (w : k ≫ f = f' ≫ l) [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)] :
    etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f') ⋙
        etaleModuleLift B Λ (fShriekFunctor.{u, u} B l) ≅
      etaleModuleLift B Λ (fShriekFunctor.{u, u} B k) ⋙
        etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f) :=
  etaleModuleLiftSquareIso B Λ (etalePushforward.{u, u + 1} B f') (fShriekFunctor.{u, u} B l)
    (fShriekFunctor.{u, u} B k) (etalePushforward.{u, u + 1} B f)
    (pushforwardFShriekSquareIso B k f' f l w)

variable {Z' Z : B.Scheme}

/-- **Vertical pasting of the identifications `f'_* ⋙ l_! ≅ k_! ⋙ f_*` for sheaves of
`Λ`-modules.** This is `AlgebraicGeometry.SmallEtale.pushforwardFShriekSquareIso_vertical_paste`
on the underlying abelian sheaves, forgetting the `Λ`-module structure being faithful. -/
lemma pushforwardFShriekModSquareIso_vertical_paste (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (l : Y' ⟶ Y) (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z)
    (w₁ : k ≫ f = f' ≫ l) (w₂ : l ≫ g = g' ≫ m)
    [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
    [IsProper (B.inclusion.map g')] [IsProper (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    [IsSeparated (B.inclusion.map m)] [LocallyQuasiFinite (B.inclusion.map m)]
    [LocallyOfFiniteType (B.inclusion.map m)] (F : ModuleSheaf.{u, u, u} B X' Λ) :
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).map
        ((etalePushforwardModCompIso B Λ f' g').hom.app F) ≫
      (pushforwardFShriekModSquareIso B Λ k (f' ≫ g') (f ≫ g) m
        (rectangle_comm B w₁ w₂)).hom.app F =
    (pushforwardFShriekModSquareIso B Λ l g' g m w₂).hom.app
        ((etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).obj F) ≫
      (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g)).map
        ((pushforwardFShriekModSquareIso B Λ k f' f l w₁).hom.app F) ≫
      (etalePushforwardModCompIso B Λ f g).hom.app
        ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).obj F) :=
  etaleModuleLiftSquareIso_vertical_paste B Λ (pushforwardFShriekSquareIso B k f' f l w₁)
    (pushforwardFShriekSquareIso B l g' g m w₂)
    (pushforwardFShriekSquareIso B k (f' ≫ g') (f ≫ g) m (rectangle_comm B w₁ w₂))
    (smallEtaleSheafPushforwardCompIso B X' Y' Z' f' g' AddCommGrpCat.{u + 1})
    (smallEtaleSheafPushforwardCompIso B X Y Z f g AddCommGrpCat.{u + 1})
    (pushforwardFShriekSquareIso_vertical_paste B k f' f l g' g m w₁ w₂) F

end Module

/-! ### The base change map on derived categories -/

section Derived

open Stacks.DerivedBaseChange

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ] {X' X Y' Y Z' Z : B.Scheme}

/-- **The map `l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` of [Stacks, Tag 0F7B].** For a commutative square
`k ≫ f = f' ≫ l` of a big étale site with `f`, `f'` proper and `k`, `l` separated and locally
quasi-finite, a ring `Λ`, and right derived functors `Rf'_*` (with unit `αF'`) and `Rf_*` (with
unit `αF`) of the direct images on the unbounded homotopy categories of étale sheaves of
`Λ`-modules, this is the transformation `l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` of functors
`D(X'_étale, Λ) ⥤ D(Y_étale, Λ)` induced, through the universal property of the right derived
functor `l_! ∘ Rf'_*`, by the identification `l_! f'_* = l_! f'_! = f_! k_! = f_* k_!` of
`AlgebraicGeometry.SmallEtale.pushforwardFShriekModSquareIso`: precomposed with the unit of
`Rf'_*` it is that identification followed by the unit of `Rf_*`
(`AlgebraicGeometry.SmallEtale.properBaseChangeMap_fac_app`). On a K-injective complex `J`
this is the map `l_! f'_* J = f_* k_! J ⟶ f_* I` of the source, for `k_! J ⟶ I` a K-injective
resolution.

The lower shrieks are the `Λ`-linear direct images with compact support, exact by Stacks 0F5F,
taken on derived categories by `Functor.mapDerivedCategory`. -/
def properBaseChangeMap (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
    (w : k ≫ f = f' ≫ l) [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    (RF' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ))
    (αF' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    (RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
    (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF'.IsRightDerivedFunctor αF'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))] :
    RF' ⋙ (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory ⟶
      (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapDerivedCategory ⋙ RF :=
  haveI := isRightDerivedFunctor_comp_right _ RF' αF'
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory
  squareMap (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapDerivedCategoryFactorsh
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategoryFactorsh αF' αF
    (homotopySquareIso (ComplexShape.up ℤ) (pushforwardFShriekModSquareIso B Λ k f' f l w))

/-- **Direct image of étale sheaves of `Λ`-modules preserves K-injective complexes**
([Stacks, Tag 0D6E]'s input, Cohomology on Sites, Lemma 21.20.10 in the source's proof of
[Stacks, Tag 0F7C]): it has an exact left adjoint, the `Λ`-linear lift of the inverse image of
abelian étale sheaves, exact by Stacks 03Q1. -/
theorem isKInjective_etalePushforwardMod {X Y : B.Scheme} (f : X ⟶ Y)
    (I : CochainComplex (ModuleSheaf.{u, u, u} B X Λ) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  have := additive_abPullback.{u, u} B f
  have := preservesFiniteLimits_abPullback.{u, u} B f
  have := preservesFiniteColimits_abPullback.{u, u} B f
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _
    (etaleModuleLift B Λ (abPullback.{u, u} B f))
    (Stacks.ModuleCatLift.moduleLiftAdjunction.{u + 1, u, _, _, _, _} Λ _ _ _ _
      (abPullbackAdjunction.{u, u} B f)) I

/-- **`R(g ∘ f)_* = Rg_* ∘ Rf_*`** for étale sheaves of `Λ`-modules: the canonical comparison
`R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*` of [Stacks, Tag 05T2] is an isomorphism, `f_*` preserving
K-injective complexes. This is the identification the source writes in its proof of
[Stacks, Tag 0F7C]. -/
theorem isIso_compComparison_etalePushforwardMod {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z Λ)]
    {RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ)}
    {RG : DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z Λ)}
    {RP : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z Λ)}
    (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (αG : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG)
    (αP : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B (f ≫ g))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    [RF.IsRightDerivedFunctor αF
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor αG
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y Λ) (ComplexShape.up ℤ))]
    [RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))] :
    IsIso (compComparison
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ)) αF αG αP
      (Functor.mapHomotopyCategoryCompIso (etalePushforwardModCompIso B Λ f g)
        (ComplexShape.up ℤ))) :=
  isIso_compComparison_of_isKInjective _ _ _ (etalePushforwardModCompIso B Λ f g) αF αG αP
    fun I _ => isKInjective_etalePushforwardMod B Λ f I

/-- The characterizing property of the map of [Stacks, Tag 0F7B]: precomposed with the unit
of `Rf'_*` at a complex `K`, it is the identification `l_! f'_* K ≅ f_* k_! K` followed by the
unit of `Rf_*` at `k_! K`. -/
lemma properBaseChangeMap_fac_app (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
    (w : k ≫ f = f' ≫ l) [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    (RF' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ))
    (αF' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    (RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
    (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF'.IsRightDerivedFunctor αF'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))]
    (K : HomotopyCategory (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ)) :
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory.map (αF'.app K) ≫
        (properBaseChangeMap B Λ k f' f l w RF' αF' RF αF).app (DerivedCategory.Qh.obj K) =
      (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategoryFactorsh.hom.app
          (((etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((homotopySquareIso (ComplexShape.up ℤ)
          (pushforwardFShriekModSquareIso B Λ k f' f l w)).hom.app K) ≫
        αF.app (((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
        RF.map ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapDerivedCategoryFactorsh.inv.app
          K) :=
  have := isRightDerivedFunctor_comp_right _ RF' αF'
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory
  squareMap_fac_app (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapDerivedCategoryFactorsh
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategoryFactorsh αF' αF
    (homotopySquareIso (ComplexShape.up ℤ) (pushforwardFShriekModSquareIso B Λ k f' f l w)) K

/-- **The pasting identity of [Stacks, Tag 0F7C], before identifying `R(g ∘ f)_*` with
`Rg_* ∘ Rf_*`.** For two commutative squares `k ≫ f = f' ≫ l` and `l ≫ g = g' ≫ m` on top of each
other, with `f`, `f'`, `g`, `g'` proper and `k`, `l`, `m` separated and locally quasi-finite, and
for arbitrary right derived functors `R(g ∘ f)_*` and `R(g' ∘ f')_*` of the direct images along
the composites, the map `m_! ∘ R(g' ∘ f')_* ⟶ R(g ∘ f)_* ∘ k_!` of [Stacks, Tag 0F7B] for the
outer rectangle, followed by the canonical comparison `R(g ∘ f)_* ⟶ Rg_* ∘ Rf_*` of
[Stacks, Tag 05T2], equals the comparison `R(g' ∘ f')_* ⟶ Rg'_* ∘ Rf'_*` followed by the composite
`m_! ∘ Rg'_* ∘ Rf'_* ⟶ Rg_* ∘ l_! ∘ Rf'_* ⟶ Rg_* ∘ Rf_* ∘ k_!` of the maps of the two squares.
No invertibility of the comparisons is used; with them inverted (they are isomorphisms,
`AlgebraicGeometry.SmallEtale.isIso_compComparison_etalePushforwardMod`) this is the statement of
the tag, `AlgebraicGeometry.SmallEtale.properBaseChangeMap_rectangle_eq_comp`. -/
theorem properBaseChangeMap_vertical_paste (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (l : Y' ⟶ Y) (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z)
    (w₁ : k ≫ f = f' ≫ l) (w₂ : l ≫ g = g' ≫ m)
    [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
    [IsProper (B.inclusion.map g')] [IsProper (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    [IsSeparated (B.inclusion.map m)] [LocallyQuasiFinite (B.inclusion.map m)]
    [LocallyOfFiniteType (B.inclusion.map m)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z Λ)]
    (RF' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ))
    (αF' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    (RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
    (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (RG' : DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z' Λ))
    (αG' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG')
    (RG : DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z Λ))
    (αG : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG)
    (RP' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z' Λ))
    (αP' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B (f' ≫ g'))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP')
    (RP : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z Λ))
    (αP : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B (f ≫ g))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    [RF'.IsRightDerivedFunctor αF'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))]
    [RF.IsRightDerivedFunctor αF
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))]
    [RG'.IsRightDerivedFunctor αG'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y' Λ) (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor αG
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y Λ) (ComplexShape.up ℤ))]
    [RP'.IsRightDerivedFunctor αP'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))]
    [RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))] :
    properBaseChangeMap B Λ k (f' ≫ g') (f ≫ g) m (rectangle_comm B w₁ w₂) RP' αP' RP αP ≫
        Functor.whiskerLeft (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapDerivedCategory
          (compComparison
            (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))
            αF αG αP (Functor.mapHomotopyCategoryCompIso (etalePushforwardModCompIso B Λ f g)
              (ComplexShape.up ℤ))) =
      Functor.whiskerRight
          (compComparison
            (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))
            αF' αG' αP' (Functor.mapHomotopyCategoryCompIso (etalePushforwardModCompIso B Λ f' g')
              (ComplexShape.up ℤ)))
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory ≫
        (Functor.associator RF' RG'
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory).hom ≫
        Functor.whiskerLeft RF' (properBaseChangeMap B Λ l g' g m w₂ RG' αG' RG αG) ≫
        (Functor.associator RF'
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory RG).inv ≫
        Functor.whiskerRight (properBaseChangeMap B Λ k f' f l w₁ RF' αF' RF αF) RG ≫
        (Functor.associator
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapDerivedCategory RF RG).hom := by
  have := isRightDerivedFunctor_comp_right _ RF' αF'
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory
  have := isRightDerivedFunctor_comp_right _ RG' αG'
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory
  have := isRightDerivedFunctor_comp_right _ RP' αP'
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory
  exact squareMap_vertical_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (homotopySquareIso_vertical_paste (ComplexShape.up ℤ) _ _ _ _ _
      (pushforwardFShriekModSquareIso_vertical_paste B Λ k f' f l g' g m w₁ w₂))


/-- **[Stacks, Tag 0F7C]**, in the form the source states it. Consider a commutative diagram of
a big étale site
```
X' --k--> X
|         |
f'        f
v         v
Y' --l--> Y
|         |
g'        g
v         v
Z' --m--> Z
```
with `f`, `f'`, `g` and `g'` proper and `k`, `l` and `m` separated and locally quasi-finite, and
let `Λ` be a ring. Write `R(g ∘ f)_* = Rg_* ∘ Rf_*` and `R(g' ∘ f')_* = Rg'_* ∘ Rf'_*` through
the canonical comparisons, which are isomorphisms
(`AlgebraicGeometry.SmallEtale.isIso_compComparison_etalePushforwardMod`). Then the map
`m_! ∘ Rg'_* ∘ Rf'_* ⟶ Rg_* ∘ Rf_* ∘ k_!` of [Stacks, Tag 0F7B] for the outer rectangle is the
composite
```
m_! ∘ Rg'_* ∘ Rf'_* ⟶ Rg_* ∘ l_! ∘ Rf'_* ⟶ Rg_* ∘ Rf_* ∘ k_!
```
of the maps of the two squares. This holds for every choice of the six right derived functors.

The source calls the maps of [Stacks, Tag 0F7B] isomorphisms; that is [Stacks, Tag 0F7B]
itself (whose proof rests on proper base change, [Stacks, Tag 0DDF], under its torsion
hypotheses), and is not needed here: the content of this tag is the identity between the maps,
which holds without any hypothesis on `Λ` or on the complexes. The identity before identifying
`R(g ∘ f)_*` with `Rg_* ∘ Rf_*`, which needs no invertibility of the comparisons, is
`AlgebraicGeometry.SmallEtale.properBaseChangeMap_vertical_paste`. -/
@[stacks 0F7C]
theorem properBaseChangeMap_rectangle_eq_comp (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (l : Y' ⟶ Y) (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z)
    (w₁ : k ≫ f = f' ≫ l) (w₂ : l ≫ g = g' ≫ m)
    [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
    [IsProper (B.inclusion.map g')] [IsProper (B.inclusion.map g)]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    [IsSeparated (B.inclusion.map m)] [LocallyQuasiFinite (B.inclusion.map m)]
    [LocallyOfFiniteType (B.inclusion.map m)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Z Λ)]
    (RF' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ))
    (αF' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    (RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
    (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (RG' : DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z' Λ))
    (αG' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG')
    (RG : DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z Λ))
    (αG : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B g)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RG)
    (RP' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z' Λ))
    (αP' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B (f' ≫ g'))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP')
    (RP : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Z Λ))
    (αP : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B (f ≫ g))).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    [RF'.IsRightDerivedFunctor αF'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))]
    [RF.IsRightDerivedFunctor αF
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))]
    [RG'.IsRightDerivedFunctor αG'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y' Λ) (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor αG
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B Y Λ) (ComplexShape.up ℤ))]
    [RP'.IsRightDerivedFunctor αP'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))]
    [RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))] :
    haveI := isIso_compComparison_etalePushforwardMod B Λ f' g' αF' αG' αP'
    Functor.whiskerRight (inv (compComparison
        (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))
        αF' αG' αP' (Functor.mapHomotopyCategoryCompIso (etalePushforwardModCompIso B Λ f' g')
          (ComplexShape.up ℤ))))
        (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory ≫
      properBaseChangeMap B Λ k (f' ≫ g') (f ≫ g) m (rectangle_comm B w₁ w₂) RP' αP' RP αP ≫
      Functor.whiskerLeft (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapDerivedCategory
        (compComparison
          (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))
          αF αG αP (Functor.mapHomotopyCategoryCompIso (etalePushforwardModCompIso B Λ f g)
            (ComplexShape.up ℤ))) =
      (Functor.associator RF' RG'
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B m)).mapDerivedCategory).hom ≫
        Functor.whiskerLeft RF' (properBaseChangeMap B Λ l g' g m w₂ RG' αG' RG αG) ≫
        (Functor.associator RF'
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory RG).inv ≫
        Functor.whiskerRight (properBaseChangeMap B Λ k f' f l w₁ RF' αF' RF αF) RG ≫
        (Functor.associator
          (etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapDerivedCategory RF RG).hom := by
  rw [properBaseChangeMap_vertical_paste B Λ k f' f l g' g m w₁ w₂ RF' αF' RF αF
    RG' αG' RG αG RP' αP' RP αP, ← Category.assoc, ← Functor.whiskerRight_comp,
    IsIso.inv_hom_id, Functor.whiskerRight_id', Category.id_comp]

end Derived

end AlgebraicGeometry.SmallEtale

end
