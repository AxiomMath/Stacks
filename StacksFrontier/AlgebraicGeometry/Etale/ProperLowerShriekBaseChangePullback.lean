module

public import StacksFrontier.AlgebraicGeometry.Etale.ProperLowerShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Etale.DirectImageBaseChangeCube
public import StacksFrontier.CategoryTheory.Functor.Derived.BaseChangeCube
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory

import StacksCore.Tactic.StacksAttribute

/-!
# The base change maps `l_! ∘ Rf'_* ⟶ Rf_* ∘ k_!` are compatible with change of base

Let `b : Y₁ ⟶ Y` be a morphism of a big étale site, and consider a commutative square
```
X' --k--> X
|         |
f'        f
v         v
Y' --l--> Y
```
with `f`, `f'` proper and `k`, `l` separated and locally quasi-finite, together with its base
change by `b`: cartesian squares `X₁ = X ×_Y Y₁` (projections `a`, `f₁`), `Y'₁ = Y' ×_Y Y₁`
(projections `b'`, `l₁`), `X'₁ = X' ×_{Y'} Y'₁` (projections `a'`, `f'₁`), and the induced
`k₁ : X'₁ ⟶ X₁`. This file proves [Stacks, Tag 0F7F]: for a ring `Λ` and `K` in
`D(X'_étale, Λ)` the diagram
```
b⁻¹ l_! Rf'_* K ⟶ l₁_! b'⁻¹ Rf'_* K ⟶ l₁_! Rf'₁_* a'⁻¹ K
      |                                      |
b⁻¹ Rf_* k_! K ⟶ Rf₁_* a⁻¹ k_! K  ⟶ Rf₁_* k₁_! a'⁻¹ K
```
commutes, where the vertical maps are those of [Stacks, Tag 0F7B]
(`AlgebraicGeometry.SmallEtale.properBaseChangeMap`), and the horizontal ones are the base change
maps of Étale Cohomology, Section 0EZQ (`AlgebraicGeometry.SmallEtale.etaleDerivedBaseChangeMap`)
and of [Stacks, Tag 0F55] (`AlgebraicGeometry.SmallEtale.derivedFShriekBaseChangeIso`).

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekProperSupportBaseChangeIso`: the isomorphism
  `g⁻¹ f_! ≅ f'_! p⁻¹` of Stacks 0F55, on the model `fShriekFunctor` of `f_!` (through 0F6N).
* `AlgebraicGeometry.SmallEtale.etaleDerivedBaseChangeMap`: the derived base change map
  `b⁻¹ Rf_* ⟶ Rf₁_* a⁻¹` for sheaves of `Λ`-modules (Cohomology on Sites, Remark 07A7).
* `AlgebraicGeometry.SmallEtale.derivedFShriekBaseChangeIso`: the isomorphism
  `b⁻¹ l_! ≅ l₁_! b'⁻¹` of Stacks 0F55 on derived categories of sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.SmallEtale.pushforwardFShriekSquareIso_baseChange`: the underived diagram
  commutes, on abelian sheaves.
* `AlgebraicGeometry.SmallEtale.properBaseChangeMap_baseChange`: **[Stacks, Tag 0F7F]**.

## Implementation notes

The proof is the one of the source. The source reduces the statement to the commutativity of the
underived diagram of complexes, checked after replacing every lower shriek by the corresponding
direct image (the lower shrieks being subfunctors of the direct images, and the base change maps of
Stacks 0F55 being restrictions of the pullback maps); there it is the compatibility of the pullback
maps of Sites, Section 06UM with stacking of squares
(`AlgebraicGeometry.SmallEtale.directImageBaseChange_cube`). The passage from the underived to
the derived diagram, which the source does by a choice of K-injective resolutions, is here the
universal property of the right derived functors (`Stacks.DerivedBaseChange.squareMapOfHom_cube`).

## References

* [Stacks Project, Tag 0F7F](https://stacks.math.columbia.edu/tag/0F7F)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F55](https://stacks.math.columbia.edu/tag/0F55)
* [Stacks Project, Tag 0EZQ](https://stacks.math.columbia.edu/tag/0EZQ)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.SmallEtale

/-! ### Base change of the hypotheses -/

section Hypotheses

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)

include sq in
/-- The base change of a proper morphism along a cartesian square is proper. -/
theorem isProper_of_isPullback [IsProper (B.inclusion.map f)] :
    IsProper (B.inclusion.map f') :=
  MorphismProperty.of_isPullback (P := @IsProper) (sq.map B.inclusion) inferInstance

variable {X'₁ X₁ Y'₁ Y₁ : B.Scheme} {k : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {l : Y' ⟶ Y}
  {b : Y₁ ⟶ Y} {a : X₁ ⟶ X} {f₁ : X₁ ⟶ Y₁} {b' : Y'₁ ⟶ Y'} {l₁ : Y'₁ ⟶ Y₁}
  {a' : X'₁ ⟶ X'} {f'₁ : X'₁ ⟶ Y'₁} {k₁ : X'₁ ⟶ X₁}

/-- In the base change of a commutative square `k ≫ f = f' ≫ l` by `b`, the square formed by
`k` and its base change `k₁` is cartesian: `X'₁ = X' ×_{Y'} Y'₁ = X' ×_Y Y₁ = X' ×_X X₁`. -/
theorem isPullback_baseChange_left (w : k ≫ f = f' ≫ l) (sqX : IsPullback a f₁ f b)
    (sqY : IsPullback b' l₁ l b) (sqX' : IsPullback a' f'₁ f' b') (hk₁ : k₁ ≫ a = a' ≫ k)
    (w₁ : k₁ ≫ f₁ = f'₁ ≫ l₁) : IsPullback a' k₁ k a := by
  have h := sqX'.paste_vert sqY
  rw [← w, ← w₁] at h
  exact IsPullback.of_bot h hk₁.symm sqX

end Hypotheses

/-! ### The underived diagram, on abelian sheaves -/

section Abelian

variable (B : BigEtaleSite.{u})

/-- The inclusion `f_! ⊆ f_*` of the direct image with compact support of a separated locally
quasi-finite morphism into the direct image, on the model `fShriekFunctor` of `f_!`: Stacks 0F6N
followed by the inclusion of the proper-support subsheaf. -/
def fShriekToPushforward {X Y : B.Scheme} (g : X ⟶ Y) [IsSeparated (B.inclusion.map g)]
    [LocallyQuasiFinite (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)] :
    fShriekFunctor.{u, u} B g ⟶ etalePushforward.{u, u + 1} B g :=
  (fShriekFunctorIsoProperSupport.{u, u} B g).hom ≫ properSupportToPushforward.{u, u + 1} B g

/-- The inclusion `f_! ⊆ f_*` is a monomorphism. -/
theorem mono_fShriekToPushforward_app {X Y : B.Scheme} (g : X ⟶ Y)
    [IsSeparated (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
    [LocallyOfFiniteType (B.inclusion.map g)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    Mono (C := Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
      ((fShriekToPushforward B g).app F) := by
  have : Mono (C := Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
      ((properSupportToPushforward.{u, u + 1} B g).app F) :=
    inferInstanceAs (Mono (fShriekSubsheaf.{u, u + 1} B g F).val.arrow)
  have h₁ : Mono (C := Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1})
      ((fShriekFunctorIsoProperSupport.{u, u} B g).hom.app F) :=
    IsIso.mono_of_iso _
  exact @mono_comp _ _ _ _ _ _ h₁ _ this

/-- **Stacks 0F55 on the model `fShriekFunctor` of `f_!`.** For a cartesian square with `f`
separated and locally quasi-finite, the isomorphism `g⁻¹ f_! ≅ f'_! p⁻¹` of
`AlgebraicGeometry.SmallEtale.properSupportBaseChangeIso`, read through the identifications
Stacks 0F6N of `fShriekFunctor` with the proper-support direct image. The hypotheses on `f'` are
read off the square. -/
@[sga "4 XVII 5.2.6" "Degree-zero clause"]
def fShriekProperSupportBaseChangeIso {X Y X' Y' : B.Scheme} (p : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g) [IsSeparated (B.inclusion.map f)]
    [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)] :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    fShriekFunctor.{u, u} B f ⋙ abPullback.{u, u} B g ≅
      abPullback.{u, u} B p ⋙ fShriekFunctor.{u, u} B f' :=
  letI := locallyOfFiniteType_of_isPullback B p f' f g sq
  letI := locallyQuasiFinite_of_isPullback B p f' f g sq
  haveI := isSeparated_of_isPullback B p f' f g sq
  Functor.isoWhiskerRight (fShriekFunctorIsoProperSupport.{u, u} B f) (abPullback.{u, u} B g) ≪≫
    properSupportBaseChangeIso.{u, u} B p f' f g sq ≪≫
    Functor.isoWhiskerLeft (abPullback.{u, u} B p) (fShriekFunctorIsoProperSupport.{u, u} B f').symm

/-- The isomorphism of Stacks 0F55 on `fShriekFunctor` is the restriction of the pullback map
`g⁻¹ f_* ⟶ f'_* p⁻¹` along the inclusions `f_! ⊆ f_*` and `f'_! ⊆ f'_*`. -/
lemma fShriekProperSupportBaseChangeIso_hom_app_comp {X Y X' Y' : B.Scheme} (p : X' ⟶ X)
    (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
    [IsSeparated (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    haveI := isSeparated_of_isPullback B p f' f g sq
    (fShriekProperSupportBaseChangeIso B p f' f g sq).hom.app F ≫
        (fShriekToPushforward B f').app ((abPullback.{u, u} B p).obj F) =
      (abPullback.{u, u} B g).map ((fShriekToPushforward B f).app F) ≫
        directImageBaseChange.{u, u} B p f' f g sq F := by
  let := locallyOfFiniteType_of_isPullback B p f' f g sq
  let := locallyQuasiFinite_of_isPullback B p f' f g sq
  have := isSeparated_of_isPullback B p f' f g sq
  have h := properSupportBaseChange_comp_arrow.{u, u} B p f' f g sq F
  simp only [fShriekProperSupportBaseChangeIso, fShriekToPushforward, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc, properSupportBaseChangeIso_hom_app, Functor.map_comp]
  exact congrArg ((abPullback.{u, u} B g).map
    ((fShriekFunctorIsoProperSupport.{u, u} B f).hom.app F) ≫ ·) h

/-- The comparison `a_* ⋙ b_* ≅ (a ≫ b)_*` read through the factorization `a ≫ b = a ≫ b` is
the comparison of Stacks 021J. -/
lemma pushforwardFactoredCompIso_rfl_hom_app {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (pushforwardFactoredCompIso B AddCommGrpCat.{u + 1} a b (a ≫ b) rfl).hom.app F =
      (smallEtaleSheafPushforwardCompIso B X Y Z a b AddCommGrpCat.{u + 1}).hom.app F := by
  ext ⟨V⟩ s
  rw [pushforwardFactoredCompIso_hom_app_hom_app]
  simp [smallEtaleBaseChange_factoredCompIso, smallEtaleSheafPushforwardCompIso,
    Functor.sheafPushforwardContinuousComp']
  rfl

/-- Stacks 0F50 for a factorization `a ≫ b = h`, followed by the inclusion `h_! ⊆ h_*`, is the
iterated inclusion followed by the comparison `b_* a_* ≅ h_*` of direct images. -/
lemma properSupportFactoredCompIso_hom_app_arrow_factored {X Y Z : B.Scheme} (a : X ⟶ Y)
    (b : Y ⟶ Z) (h : X ⟶ Z) (hab : a ≫ b = h) [LocallyOfFiniteType (B.inclusion.map a)]
    [LocallyOfFiniteType (B.inclusion.map b)] [LocallyOfFiniteType (B.inclusion.map h)]
    [IsSeparated (B.inclusion.map a)] [IsSeparated (B.inclusion.map b)]
    (A : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (properSupportFactoredCompIso.{u, u + 1} B a b h hab).hom.app A ≫
        (properSupportToPushforward.{u, u + 1} B h).app A =
      (properSupportToPushforward.{u, u + 1} B b).app
          ((properSupportFunctor.{u, u + 1} B a).obj A) ≫
        (etalePushforward.{u, u + 1} B b).map ((properSupportToPushforward.{u, u + 1} B a).app A) ≫
        (pushforwardFactoredCompIso B AddCommGrpCat.{u + 1} a b h hab).hom.app A := by
  subst hab
  rw [pushforwardFactoredCompIso_rfl_hom_app]
  exact properSupportFactoredCompIso_hom_app_arrow.{u, u + 1} B a b A

/-- The inverse form of `properSupportFactoredCompIso_hom_app_arrow_factored`. -/
lemma properSupportFactoredCompIso_inv_app_arrow_factored {X Y Z : B.Scheme} (a : X ⟶ Y)
    (b : Y ⟶ Z) (h : X ⟶ Z) (hab : a ≫ b = h) [LocallyOfFiniteType (B.inclusion.map a)]
    [LocallyOfFiniteType (B.inclusion.map b)] [LocallyOfFiniteType (B.inclusion.map h)]
    [IsSeparated (B.inclusion.map a)] [IsSeparated (B.inclusion.map b)]
    (A : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    (properSupportFactoredCompIso.{u, u + 1} B a b h hab).inv.app A ≫
        (properSupportToPushforward.{u, u + 1} B b).app
            ((properSupportFunctor.{u, u + 1} B a).obj A) ≫
        (etalePushforward.{u, u + 1} B b).map ((properSupportToPushforward.{u, u + 1} B a).app A) =
      (properSupportToPushforward.{u, u + 1} B h).app A ≫
        (pushforwardFactoredCompIso B AddCommGrpCat.{u + 1} a b h hab).inv.app A := by
  rw [← cancel_epi ((properSupportFactoredCompIso.{u, u + 1} B a b h hab).hom.app A),
    Iso.hom_inv_id_app_assoc, ← Category.assoc,
    properSupportFactoredCompIso_hom_app_arrow_factored, Category.assoc, Category.assoc,
    Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

variable {X' X Y' Y : B.Scheme}

/-- **The identification `f'_* ⋙ l_! ≅ k_! ⋙ f_*` is the restriction of the comparison of
direct images.** The identification of [Stacks, Tag 0F7B]'s proof,
`l_! f'_* = l_! f'_! = f_! k_! = f_* k_!`, followed by the inclusion `k_! ⊆ k_*`, is the inclusion
`l_! ⊆ l_*` followed by the comparison `l_* f'_* = (k ≫ f)_* = f_* k_*`. -/
lemma pushforwardFShriekSquareIso_hom_app_comp (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (l : Y' ⟶ Y) (w : k ≫ f = f' ≫ l) [IsProper (B.inclusion.map f')]
    [IsProper (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    (F : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1}) :
    (pushforwardFShriekSquareIso B k f' f l w).hom.app F ≫
        (etalePushforward.{u, u + 1} B f).map ((fShriekToPushforward B k).app F) =
      (fShriekToPushforward B l).app ((etalePushforward.{u, u + 1} B f').obj F) ≫
        (pushforwardSquareIso B AddCommGrpCat.{u + 1} k f' f l (k ≫ f) rfl w.symm).hom.app F := by
  have e1 : pushforwardFShriekSquareIso B k f' f l w =
      Stacks.DerivedBaseChange.squareIsoTransport (properSupportIsoPushforward.{u, u + 1} B f')
        (properSupportIsoPushforward.{u, u + 1} B f) (fShriekFunctorIsoProperSupport.{u, u} B k)
        (fShriekFunctorIsoProperSupport.{u, u} B l)
        (properSupportFactoredCompIso.{u, u + 1} B f' l (k ≫ f) w.symm ≪≫
          (properSupportFactoredCompIso.{u, u + 1} B k f (k ≫ f) rfl).symm) := rfl
  have e2 : fShriekToPushforward B k = (fShriekFunctorIsoProperSupport.{u, u} B k).hom ≫
      properSupportToPushforward.{u, u + 1} B k := rfl
  have key := Stacks.DerivedBaseChange.squareIsoTransport_hom_app_comp
    (properSupportIsoPushforward.{u, u + 1} B f') (properSupportIsoPushforward.{u, u + 1} B f)
    (fShriekFunctorIsoProperSupport.{u, u} B k) (fShriekFunctorIsoProperSupport.{u, u} B l)
    (properSupportFactoredCompIso.{u, u + 1} B f' l (k ≫ f) w.symm)
    (properSupportFactoredCompIso.{u, u + 1} B k f (k ≫ f) rfl)
    (properSupportToPushforward.{u, u + 1} B k) (properSupportToPushforward.{u, u + 1} B l)
    (properSupportToPushforward.{u, u + 1} B (k ≫ f))
    (pushforwardFactoredCompIso B AddCommGrpCat.{u + 1} f' l (k ≫ f) w.symm)
    (pushforwardFactoredCompIso B AddCommGrpCat.{u + 1} k f (k ≫ f) rfl)
    (properSupportFactoredCompIso_hom_app_arrow_factored B f' l (k ≫ f) w.symm)
    (properSupportFactoredCompIso_hom_app_arrow_factored B k f (k ≫ f) rfl) F
  rw [e1, e2]
  exact key

end Abelian

/-! ### The underived cube -/

section Cube

variable (B : BigEtaleSite.{u}) {X' X Y' Y X'₁ X₁ Y'₁ Y₁ : B.Scheme}
  (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y) (w : k ≫ f = f' ≫ l)
  (b : Y₁ ⟶ Y) (a : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (sqX : IsPullback a f₁ f b)
  (b' : Y'₁ ⟶ Y') (l₁ : Y'₁ ⟶ Y₁) (sqY : IsPullback b' l₁ l b)
  (a' : X'₁ ⟶ X') (f'₁ : X'₁ ⟶ Y'₁) (sqX' : IsPullback a' f'₁ f' b')
  (k₁ : X'₁ ⟶ X₁) (w₁ : k₁ ≫ f₁ = f'₁ ≫ l₁) (sqK : IsPullback a' k₁ k a)
  [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
  [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
  [LocallyOfFiniteType (B.inclusion.map k)]
  [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
  [LocallyOfFiniteType (B.inclusion.map l)]
  [IsProper (B.inclusion.map f'₁)] [IsProper (B.inclusion.map f₁)]
  [IsSeparated (B.inclusion.map k₁)] [LocallyQuasiFinite (B.inclusion.map k₁)]
  [LocallyOfFiniteType (B.inclusion.map k₁)]
  [IsSeparated (B.inclusion.map l₁)] [LocallyQuasiFinite (B.inclusion.map l₁)]
  [LocallyOfFiniteType (B.inclusion.map l₁)]

/-- **The underived diagram of [Stacks, Tag 0F7F] commutes**, on abelian sheaves: for an abelian
sheaf `F` on `X'`,
```
b⁻¹ l_! f'_* F = b⁻¹ f_* k_! F ⟶ f₁_* a⁻¹ k_! F ⟶ f₁_* k₁_! a'⁻¹ F
  equals
b⁻¹ l_! f'_* F ⟶ l₁_! b'⁻¹ f'_* F ⟶ l₁_! f'₁_* a'⁻¹ F = f₁_* k₁_! a'⁻¹ F,
```
the identifications being those of the proof of [Stacks, Tag 0F7B], the unnamed maps the
pullback maps of Sites, Section 06UM and the isomorphisms of Stacks 0F55. As in the source, it is
checked after including the lower shrieks into the direct images, where it is
`AlgebraicGeometry.SmallEtale.directImageBaseChange_cube`. -/
theorem pushforwardFShriekSquareIso_baseChange
    (F : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1}) :
    (abPullback.{u, u} B b).map ((pushforwardFShriekSquareIso B k f' f l w).hom.app F) ≫
      (directImageBaseChangeNatTrans.{u, u} B a f₁ f b sqX).app
        ((fShriekFunctor.{u, u} B k).obj F) ≫
      (etalePushforward.{u, u + 1} B f₁).map
        ((fShriekProperSupportBaseChangeIso B a' k₁ k a sqK).hom.app F) =
    (fShriekProperSupportBaseChangeIso B b' l₁ l b sqY).hom.app
        ((etalePushforward.{u, u + 1} B f').obj F) ≫
      (fShriekFunctor.{u, u} B l₁).map
        ((directImageBaseChangeNatTrans.{u, u} B a' f'₁ f' b' sqX').app F) ≫
      (pushforwardFShriekSquareIso B k₁ f'₁ f₁ l₁ w₁).hom.app ((abPullback.{u, u} B a').obj F) := by
  have : Mono ((etalePushforward.{u, u + 1} B f₁).map
      ((fShriekToPushforward B k₁).app ((abPullback.{u, u} B a').obj F))) := by
    have := mono_fShriekToPushforward_app B k₁ ((abPullback.{u, u} B a').obj F)
    have : (etalePushforward.{u, u + 1} B f₁).IsRightAdjoint :=
      (abPullbackAdjunction.{u, u} B f₁).isRightAdjoint
    exact Functor.map_mono _ _
  exact Stacks.DerivedBaseChange.cube_comm_of_mono
    (pushforwardFShriekSquareIso B k f' f l w).hom
    (pushforwardFShriekSquareIso B k₁ f'₁ f₁ l₁ w₁).hom
    (pushforwardSquareIso B AddCommGrpCat.{u + 1} k f' f l (k ≫ f) rfl w.symm).hom
    (pushforwardSquareIso B AddCommGrpCat.{u + 1} k₁ f'₁ f₁ l₁ (k₁ ≫ f₁) rfl w₁.symm).hom
    (directImageBaseChangeNatTrans.{u, u} B a f₁ f b sqX)
    (directImageBaseChangeNatTrans.{u, u} B a' f'₁ f' b' sqX')
    (fShriekProperSupportBaseChangeIso B a' k₁ k a sqK).hom
    (fShriekProperSupportBaseChangeIso B b' l₁ l b sqY).hom
    (directImageBaseChangeNatTrans.{u, u} B a' k₁ k a sqK)
    (directImageBaseChangeNatTrans.{u, u} B b' l₁ l b sqY)
    (fShriekToPushforward B k) (fShriekToPushforward B l) (fShriekToPushforward B k₁)
    (fShriekToPushforward B l₁)
    (pushforwardFShriekSquareIso_hom_app_comp B k f' f l w)
    (pushforwardFShriekSquareIso_hom_app_comp B k₁ f'₁ f₁ l₁ w₁)
    (fShriekProperSupportBaseChangeIso_hom_app_comp B a' k₁ k a sqK)
    (fShriekProperSupportBaseChangeIso_hom_app_comp B b' l₁ l b sqY)
    (directImageBaseChange_cube.{u, u} B k f' f l (k ≫ f) rfl w.symm b a f₁ sqX b' l₁ sqY a' f'₁
      sqX' k₁ sqK (k₁ ≫ f₁) rfl w₁.symm) F

end Cube

/-! ### Sheaves of `Λ`-modules and homotopy categories -/

section Module

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ]

attribute [local instance] additive_abPullback preservesFiniteLimits_abPullback
  preservesFiniteColimits_abPullback

/-- The `Λ`-linear lift of a transformation `G₁ ⋙ G₂ ⟶ G₃ ⋙ G₄` of a square of additive functors
on abelian étale sheaves, as a transformation between composites of lifts. -/
def etaleModuleLiftSquareHom {X₁ X₂ X₃ X₄ : B.Scheme}
    (G₁ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1}) [G₁.Additive]
    (G₂ : Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [G₂.Additive]
    (G₃ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1}) [G₃.Additive]
    (G₄ : Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [G₄.Additive]
    (e : G₁ ⋙ G₂ ⟶ G₃ ⋙ G₄) :
    etaleModuleLift B Λ G₁ ⋙ etaleModuleLift B Λ G₂ ⟶
      etaleModuleLift B Λ G₃ ⋙ etaleModuleLift B Λ G₄ :=
  Stacks.ModuleCatLift.moduleLiftNatTrans.{u + 1, u, _, _, _, _} Λ
    (SmallEtale.topology B X₁.obj X₁.property) (SmallEtale.topology B X₄.obj X₄.property)
    (G₁ ⋙ G₂) (G₃ ⋙ G₄) e

/-- On underlying abelian sheaves, the lift of a transformation of a square is the
transformation. -/
lemma forgetModuleSheaf_map_etaleModuleLiftSquareHom_app {X₁ X₂ X₃ X₄ : B.Scheme}
    (G₁ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1}) [G₁.Additive]
    (G₂ : Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [G₂.Additive]
    (G₃ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1}) [G₃.Additive]
    (G₄ : Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [G₄.Additive]
    (e : G₁ ⋙ G₂ ⟶ G₃ ⋙ G₄) (F : ModuleSheaf.{u, u, u} B X₁ Λ) :
    (forgetModuleSheaf.{u, u, u} B X₄ Λ).map
        ((etaleModuleLiftSquareHom B Λ G₁ G₂ G₃ G₄ e).app F) =
      e.app ((forgetModuleSheaf.{u, u, u} B X₁ Λ).obj F) :=
  rfl

/-- `forgetModuleSheaf_map_etaleModuleLiftSquareHom_app`, in the shape of
`Stacks.DerivedBaseChange.cube_of_faithful`. -/
lemma forgetModuleSheaf_map_etaleModuleLiftSquareHom_app_conj {X₁ X₂ X₃ X₄ : B.Scheme}
    (G₁ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1}) [G₁.Additive]
    (G₂ : Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [G₂.Additive]
    (G₃ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1}) [G₃.Additive]
    (G₄ : Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [G₄.Additive]
    (e : G₁ ⋙ G₂ ⟶ G₃ ⋙ G₄) (F : ModuleSheaf.{u, u, u} B X₁ Λ) :
    (forgetModuleSheaf.{u, u, u} B X₄ Λ).map
        ((etaleModuleLiftSquareHom B Λ G₁ G₂ G₃ G₄ e).app F) =
      (etaleModuleLiftForgetIso B Λ G₂).hom.app ((etaleModuleLift B Λ G₁).obj F) ≫
        G₂.map ((etaleModuleLiftForgetIso B Λ G₁).hom.app F) ≫
        e.app ((forgetModuleSheaf.{u, u, u} B X₁ Λ).obj F) ≫
        G₄.map ((etaleModuleLiftForgetIso B Λ G₃).inv.app F) ≫
        (etaleModuleLiftForgetIso B Λ G₄).inv.app ((etaleModuleLift B Λ G₃).obj F) := by
  rw [forgetModuleSheaf_map_etaleModuleLiftSquareHom_app]
  simp only [etaleModuleLiftForgetIso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  symm
  refine (Category.id_comp (obj := AbelianSheaf.{u, u} B X₄) _).trans ?_
  refine (congrArg (· ≫ _) (G₂.map_id _)).trans ?_
  refine (Category.id_comp (obj := AbelianSheaf.{u, u} B X₄) _).trans ?_
  refine (congrArg (e.app _ ≫ ·) ((congrArg (· ≫ _) (G₄.map_id _)).trans
    (Category.id_comp (obj := AbelianSheaf.{u, u} B X₄) _))).trans ?_
  exact Category.comp_id _

/-- On underlying abelian sheaves, the lift of an additive functor acts as the functor. -/
lemma forgetModuleSheaf_map_etaleModuleLift_map {X₁ X₂ : B.Scheme}
    (G : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1}) [G.Additive]
    {F₁ F₂ : ModuleSheaf.{u, u, u} B X₁ Λ} (φ : F₁ ⟶ F₂) :
    (forgetModuleSheaf.{u, u, u} B X₂ Λ).map ((etaleModuleLift B Λ G).map φ) =
      G.map ((forgetModuleSheaf.{u, u, u} B X₁ Λ).map φ) :=
  rfl

/-- The lift of an isomorphism of a square is the lift of the underlying transformation. -/
lemma etaleModuleLiftSquareIso_hom {X₁ X₂ X₃ X₄ : B.Scheme}
    (G₁ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1}) [G₁.Additive]
    (G₂ : Sheaf (SmallEtale.topology B X₂.obj X₂.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [G₂.Additive]
    (G₃ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1}) [G₃.Additive]
    (G₄ : Sheaf (SmallEtale.topology B X₃.obj X₃.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₄.obj X₄.property) AddCommGrpCat.{u + 1}) [G₄.Additive]
    (e : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄) :
    (etaleModuleLiftSquareIso B Λ G₁ G₂ G₃ G₄ e).hom =
      etaleModuleLiftSquareHom B Λ G₁ G₂ G₃ G₄ e.hom := by
  refine NatTrans.ext (funext fun F => ?_)
  apply (forgetModuleSheaf.{u, u, u} B X₄ Λ).map_injective
  rw [forgetModuleSheaf_map_etaleModuleLiftSquareIso_hom_app,
    forgetModuleSheaf_map_etaleModuleLiftSquareHom_app]

variable {X' X Y' Y X'₁ X₁ Y'₁ Y₁ : B.Scheme}

/-- **A commuting cube of additive functors on abelian étale sheaves lifts to sheaves of
`Λ`-modules**: forgetting the `Λ`-module structure is faithful and takes every lift to the functor
or transformation it was lifted from. -/
theorem etaleModuleLiftSquareHom_cube
    (F' : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B Y'.obj Y'.property) AddCommGrpCat.{u + 1}) [F'.Additive]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) [F.Additive]
    (F'₁ : Sheaf (SmallEtale.topology B X'₁.obj X'₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B Y'₁.obj Y'₁.property) AddCommGrpCat.{u + 1}) [F'₁.Additive]
    (F₁ : Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B Y₁.obj Y₁.property) AddCommGrpCat.{u + 1}) [F₁.Additive]
    (K : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) [K.Additive]
    (L : Sheaf (SmallEtale.topology B Y'.obj Y'.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) [L.Additive]
    (K₁ : Sheaf (SmallEtale.topology B X'₁.obj X'₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1}) [K₁.Additive]
    (L₁ : Sheaf (SmallEtale.topology B Y'₁.obj Y'₁.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B Y₁.obj Y₁.property) AddCommGrpCat.{u + 1}) [L₁.Additive]
    (A' : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X'₁.obj X'₁.property) AddCommGrpCat.{u + 1}) [A'.Additive]
    (A : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B X₁.obj X₁.property) AddCommGrpCat.{u + 1}) [A.Additive]
    (B' : Sheaf (SmallEtale.topology B Y'.obj Y'.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B Y'₁.obj Y'₁.property) AddCommGrpCat.{u + 1}) [B'.Additive]
    (Bb : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B Y₁.obj Y₁.property) AddCommGrpCat.{u + 1}) [Bb.Additive]
    (e : F' ⋙ L ⟶ K ⋙ F) (e₁ : F'₁ ⋙ L₁ ⟶ K₁ ⋙ F₁)
    (β : F ⋙ Bb ⟶ A ⋙ F₁) (β' : F' ⋙ B' ⟶ A' ⋙ F'₁)
    (σK : K ⋙ A ⟶ A' ⋙ K₁) (σL : L ⋙ Bb ⟶ B' ⋙ L₁)
    (h : ∀ G, Bb.map (e.app G) ≫ β.app (K.obj G) ≫ F₁.map (σK.app G) =
      σL.app (F'.obj G) ≫ L₁.map (β'.app G) ≫ e₁.app (A'.obj G))
    (G : ModuleSheaf.{u, u, u} B X' Λ) :
    (etaleModuleLift B Λ Bb).map ((etaleModuleLiftSquareHom B Λ F' L K F e).app G) ≫
        (etaleModuleLiftSquareHom B Λ F Bb A F₁ β).app ((etaleModuleLift B Λ K).obj G) ≫
        (etaleModuleLift B Λ F₁).map ((etaleModuleLiftSquareHom B Λ K A A' K₁ σK).app G) =
      (etaleModuleLiftSquareHom B Λ L Bb B' L₁ σL).app ((etaleModuleLift B Λ F').obj G) ≫
        (etaleModuleLift B Λ L₁).map ((etaleModuleLiftSquareHom B Λ F' B' A' F'₁ β').app G) ≫
        (etaleModuleLiftSquareHom B Λ F'₁ L₁ K₁ F₁ e₁).app ((etaleModuleLift B Λ A').obj G) :=
  Stacks.DerivedBaseChange.cube_of_faithful
    (etaleModuleLiftForgetIso B Λ F') (etaleModuleLiftForgetIso B Λ F)
    (etaleModuleLiftForgetIso B Λ F'₁) (etaleModuleLiftForgetIso B Λ F₁)
    (etaleModuleLiftForgetIso B Λ K) (etaleModuleLiftForgetIso B Λ L)
    (etaleModuleLiftForgetIso B Λ K₁) (etaleModuleLiftForgetIso B Λ L₁)
    (etaleModuleLiftForgetIso B Λ A') (etaleModuleLiftForgetIso B Λ A)
    (etaleModuleLiftForgetIso B Λ B') (etaleModuleLiftForgetIso B Λ Bb)
    (etaleModuleLiftSquareHom B Λ F' L K F e) (etaleModuleLiftSquareHom B Λ F'₁ L₁ K₁ F₁ e₁)
    (etaleModuleLiftSquareHom B Λ F Bb A F₁ β) (etaleModuleLiftSquareHom B Λ F' B' A' F'₁ β')
    (etaleModuleLiftSquareHom B Λ K A A' K₁ σK) (etaleModuleLiftSquareHom B Λ L Bb B' L₁ σL)
    e e₁ β β' σK σL
    (forgetModuleSheaf_map_etaleModuleLiftSquareHom_app_conj B Λ F' L K F e)
    (forgetModuleSheaf_map_etaleModuleLiftSquareHom_app_conj B Λ F'₁ L₁ K₁ F₁ e₁)
    (forgetModuleSheaf_map_etaleModuleLiftSquareHom_app_conj B Λ F Bb A F₁ β)
    (forgetModuleSheaf_map_etaleModuleLiftSquareHom_app_conj B Λ F' B' A' F'₁ β')
    (forgetModuleSheaf_map_etaleModuleLiftSquareHom_app_conj B Λ K A A' K₁ σK)
    (forgetModuleSheaf_map_etaleModuleLiftSquareHom_app_conj B Λ L Bb B' L₁ σL) h G

end Module

/-! ### The derived base change maps, and [Stacks, Tag 0F7F] -/

section Derived

open Stacks.DerivedBaseChange

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ]

attribute [local instance] additive_abPullback preservesFiniteLimits_abPullback
  preservesFiniteColimits_abPullback CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- The comparison of the functor induced on derived categories by the `Λ`-linear lift of an
exact functor with the localization functors, `Functor.mapDerivedCategoryFactorsh`, stated with
the functor induced on the homotopy categories of sheaves of `Λ`-modules as it is elaborated in
this file. All transformations of homotopy categories below are written against it. -/
def etaleModuleLiftFactorsh {X Y : B.Scheme}
    (G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{u + 1}) [G.Additive]
    [PreservesFiniteLimits (etaleModuleLift B Λ G)]
    [PreservesFiniteColimits (etaleModuleLift B Λ G)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)] :
    DerivedCategory.Qh ⋙ (etaleModuleLift B Λ G).mapDerivedCategory ≅
      (etaleModuleLift B Λ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (etaleModuleLift B Λ G).mapDerivedCategoryFactorsh

/-- **The derived base change map `b⁻¹ Rf_* ⟶ Rf₁_* a⁻¹`** of Étale Cohomology, Section 0EZQ
(Cohomology on Sites, Remark 07A7), for a cartesian square `a ≫ f = f₁ ≫ b` of a big étale site,
sheaves of `Λ`-modules, and right derived functors `Rf_*` (with unit `αF`) and `Rf₁_*` (with unit
`αF₁`) of the direct images on the unbounded homotopy categories. It is the transformation which,
precomposed with the unit of `Rf_*` at a complex `K`, is the pullback map
`b⁻¹ f_* K ⟶ f₁_* a⁻¹ K` of Sites, Section 06UM followed by the unit of `Rf₁_*`
(`Stacks.DerivedBaseChange.squareMapOfHom_fac_app`): on a K-injective complex `K` it is the
composite `b⁻¹ f_* K ⟶ f₁_* a⁻¹ K ⟶ f₁_* I` for `a⁻¹ K ⟶ I` a K-injective resolution, which is
how the source describes it. The inverse images, being exact, are taken on derived categories by
`Functor.mapDerivedCategory`. -/
def etaleDerivedBaseChangeMap {X Y X₁ Y₁ : B.Scheme} (a : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (f : X ⟶ Y)
    (b : Y₁ ⟶ Y) (sq : IsPullback a f₁ f b)
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X₁ Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y₁ Λ)]
    (RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
    (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (RF₁ : DerivedCategory (ModuleSheaf.{u, u, u} B X₁ Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y₁ Λ))
    (αF₁ : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f₁)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF₁)
    [RF.IsRightDerivedFunctor αF
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))] :
    RF ⋙ (etaleModuleLift B Λ (abPullback.{u, u} B b)).mapDerivedCategory ⟶
      (etaleModuleLift B Λ (abPullback.{u, u} B a)).mapDerivedCategory ⋙ RF₁ :=
  haveI := isRightDerivedFunctor_comp_right _ RF αF
    (etaleModuleLift B Λ (abPullback.{u, u} B b)).mapDerivedCategory
  squareMapOfHom (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))
    (etaleModuleLiftFactorsh B Λ (abPullback.{u, u} B a))
    (etaleModuleLiftFactorsh B Λ (abPullback.{u, u} B b)) αF αF₁
    (homotopySquareHom (ComplexShape.up ℤ)
      (etaleModuleLiftSquareHom B Λ (etalePushforward.{u, u + 1} B f) (abPullback.{u, u} B b)
        (abPullback.{u, u} B a) (etalePushforward.{u, u + 1} B f₁)
        (directImageBaseChangeNatTrans.{u, u} B a f₁ f b sq)))

/-- **Stacks 0F55 on derived categories of sheaves of `Λ`-modules**: the isomorphism
`g⁻¹ f_! ≅ f'_! p⁻¹` of exact functors, for a cartesian square with `f` separated and locally
quasi-finite, induces an isomorphism of the functors they induce on unbounded derived categories.
-/
def derivedFShriekBaseChangeIso {X Y X' Y' : B.Scheme} (p : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g) [IsSeparated (B.inclusion.map f)]
    [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)] :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B f)).mapDerivedCategory ⋙
        (etaleModuleLift B Λ (abPullback.{u, u} B g)).mapDerivedCategory ≅
      (etaleModuleLift B Λ (abPullback.{u, u} B p)).mapDerivedCategory ⋙
        (etaleModuleLift B Λ (fShriekFunctor.{u, u} B f')).mapDerivedCategory :=
  letI := locallyOfFiniteType_of_isPullback B p f' f g sq
  letI := locallyQuasiFinite_of_isPullback B p f' f g sq
  Functor.mapDerivedCategoryCompIsoOfCompIso
      (etaleModuleLiftSquareIso B Λ (fShriekFunctor.{u, u} B f) (abPullback.{u, u} B g)
        (abPullback.{u, u} B p) (fShriekFunctor.{u, u} B f')
        (fShriekProperSupportBaseChangeIso B p f' f g sq)) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso
      (Iso.refl (etaleModuleLift B Λ (abPullback.{u, u} B p) ⋙
        etaleModuleLift B Λ (fShriekFunctor.{u, u} B f')))).symm

/-- The derived isomorphism of Stacks 0F55 at a complex is the underived one, read through the
comparisons of the four exact functors with the localization functors. -/
lemma derivedFShriekBaseChangeIso_hom_app_Qh {X Y X' Y' : B.Scheme} (p : X' ⟶ X)
    (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
    [IsSeparated (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [LocallyOfFiniteType (B.inclusion.map f)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)]
    (J : HomotopyCategory (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ)) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    (derivedFShriekBaseChangeIso B Λ p f' f g sq).hom.app (DerivedCategory.Qh.obj J) =
      (etaleModuleLift B Λ (abPullback.{u, u} B g)).mapDerivedCategory.map
          ((etaleModuleLiftFactorsh B Λ (fShriekFunctor.{u, u} B f)).hom.app J) ≫
        (etaleModuleLiftFactorsh B Λ (abPullback.{u, u} B g)).hom.app
          (((etaleModuleLift B Λ (fShriekFunctor.{u, u} B f)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((homotopySquareHom (ComplexShape.up ℤ)
          (etaleModuleLiftSquareHom B Λ (fShriekFunctor.{u, u} B f) (abPullback.{u, u} B g)
            (abPullback.{u, u} B p) (fShriekFunctor.{u, u} B f')
            (fShriekProperSupportBaseChangeIso B p f' f g sq).hom)).app J) ≫
        (etaleModuleLiftFactorsh B Λ (fShriekFunctor.{u, u} B f')).inv.app
          (((etaleModuleLift B Λ (abPullback.{u, u} B p)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj J) ≫
        (etaleModuleLift B Λ (fShriekFunctor.{u, u} B f')).mapDerivedCategory.map
          ((etaleModuleLiftFactorsh B Λ (abPullback.{u, u} B p)).inv.app J) := by
  let := locallyOfFiniteType_of_isPullback B p f' f g sq
  let := locallyQuasiFinite_of_isPullback B p f' f g sq
  rw [← etaleModuleLiftSquareIso_hom, homotopySquareHom_hom]
  simp only [etaleModuleLiftFactorsh, derivedFShriekBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app,
    Functor.mapDerivedCategoryCompIso_hom_app_Qh, Functor.mapDerivedCategoryCompIso_inv_app_Qh,
    Category.assoc, Iso.inv_hom_id_app_assoc, homotopySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp]

/-- The map of [Stacks, Tag 0F7B] is the base change map of the underlying transformation of its
square. -/
lemma properBaseChangeMap_eq_squareMapOfHom {X' X Y' Y : B.Scheme} (k : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (l : Y' ⟶ Y)
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
    haveI := isRightDerivedFunctor_comp_right _ RF' αF'
      (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory
    properBaseChangeMap B Λ k f' f l w RF' αF' RF αF =
      squareMapOfHom (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ)
          (ComplexShape.up ℤ))
        (etaleModuleLiftFactorsh B Λ (fShriekFunctor.{u, u} B k))
        (etaleModuleLiftFactorsh B Λ (fShriekFunctor.{u, u} B l)) αF' αF
        (homotopySquareHom (ComplexShape.up ℤ)
          (etaleModuleLiftSquareHom B Λ (etalePushforward.{u, u + 1} B f')
            (fShriekFunctor.{u, u} B l) (fShriekFunctor.{u, u} B k)
            (etalePushforward.{u, u + 1} B f) (pushforwardFShriekSquareIso B k f' f l w).hom)) := by
  rw [← etaleModuleLiftSquareIso_hom, homotopySquareHom_hom]
  rfl

/-- **[Stacks, Tag 0F7F]: the base change maps of Tag 0F7B are compatible with change of base.**
Let `b : Y₁ ⟶ Y` be a morphism of a big étale site and `k ≫ f = f' ≫ l` a commutative square
```
X' --k--> X
|         |
f'        f
v         v
Y' --l--> Y
```
with `f`, `f'` proper and `k`, `l` separated and locally quasi-finite. Let its base change by `b`
be given by cartesian squares `X₁ = X ×_Y Y₁` (projections `a : X₁ ⟶ X`, `f₁ : X₁ ⟶ Y₁`),
`Y'₁ = Y' ×_Y Y₁` (projections `b' : Y'₁ ⟶ Y'`, `l₁ : Y'₁ ⟶ Y₁`), `X'₁ = X' ×_{Y'} Y'₁`
(projections `a' : X'₁ ⟶ X'`, `f'₁ : X'₁ ⟶ Y'₁`), and `k₁ : X'₁ ⟶ X₁` the induced morphism
(`k₁ ≫ a = a' ≫ k`, `k₁ ≫ f₁ = f'₁ ≫ l₁`); the base-changed square inherits the hypotheses.
For a ring `Λ`, right derived functors `Rf'_*`, `Rf_*`, `Rf'₁_*`, `Rf₁_*` of the direct images
(with their units), and `K` in `D(X'_étale, Λ)`, the diagram
```
b⁻¹ l_! Rf'_* K ⟶ l₁_! b'⁻¹ Rf'_* K ⟶ l₁_! Rf'₁_* a'⁻¹ K
      |                                        |
b⁻¹ Rf_* k_! K ⟶ Rf₁_* a⁻¹ k_! K  ⟶ Rf₁_* k₁_! a'⁻¹ K
```
in `D(Y₁_étale, Λ)` commutes, where the vertical maps are those of [Stacks, Tag 0F7B]
(`AlgebraicGeometry.SmallEtale.properBaseChangeMap`), and the horizontal maps are the base change
maps of Étale Cohomology, Section 0EZQ (`AlgebraicGeometry.SmallEtale.etaleDerivedBaseChangeMap`)
and the isomorphisms of [Stacks, Tag 0F55]
(`AlgebraicGeometry.SmallEtale.derivedFShriekBaseChangeIso`). The original square is not required
to be cartesian, and `Rf₁_*` may be any functor with a transformation from `f₁_*`. -/
@[stacks 0F7F]
theorem properBaseChangeMap_baseChange {X' X Y' Y X'₁ X₁ Y'₁ Y₁ : B.Scheme}
    (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y) (w : k ≫ f = f' ≫ l)
    (b : Y₁ ⟶ Y) (a : X₁ ⟶ X) (f₁ : X₁ ⟶ Y₁) (sqX : IsPullback a f₁ f b)
    (b' : Y'₁ ⟶ Y') (l₁ : Y'₁ ⟶ Y₁) (sqY : IsPullback b' l₁ l b)
    (a' : X'₁ ⟶ X') (f'₁ : X'₁ ⟶ Y'₁) (sqX' : IsPullback a' f'₁ f' b')
    (k₁ : X'₁ ⟶ X₁) (hk₁ : k₁ ≫ a = a' ≫ k) (w₁ : k₁ ≫ f₁ = f'₁ ≫ l₁)
    [IsProper (B.inclusion.map f')] [IsProper (B.inclusion.map f)]
    [IsSeparated (B.inclusion.map k)] [LocallyQuasiFinite (B.inclusion.map k)]
    [LocallyOfFiniteType (B.inclusion.map k)]
    [IsSeparated (B.inclusion.map l)] [LocallyQuasiFinite (B.inclusion.map l)]
    [LocallyOfFiniteType (B.inclusion.map l)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y' Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X'₁ Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B X₁ Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y'₁ Λ)]
    [HasDerivedCategory.{w} (ModuleSheaf.{u, u, u} B Y₁ Λ)]
    (RF' : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y' Λ))
    (αF' : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f')).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF')
    (RF : DerivedCategory (ModuleSheaf.{u, u, u} B X Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y Λ))
    (αF : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (RF'₁ : DerivedCategory (ModuleSheaf.{u, u, u} B X'₁ Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y'₁ Λ))
    (αF'₁ : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f'₁)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF'₁)
    (RF₁ : DerivedCategory (ModuleSheaf.{u, u, u} B X₁ Λ) ⥤
      DerivedCategory (ModuleSheaf.{u, u, u} B Y₁ Λ))
    (αF₁ : (etaleModuleLift B Λ (etalePushforward.{u, u + 1} B f₁)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF₁)
    [RF'.IsRightDerivedFunctor αF'
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))]
    [RF.IsRightDerivedFunctor αF
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))]
    [RF'₁.IsRightDerivedFunctor αF'₁
      (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X'₁ Λ) (ComplexShape.up ℤ))]
    (K : DerivedCategory (ModuleSheaf.{u, u, u} B X' Λ)) :
    haveI := isProper_of_isPullback B a f₁ f b sqX
    haveI := isProper_of_isPullback B a' f'₁ f' b' sqX'
    haveI := isSeparated_of_isPullback B b' l₁ l b sqY
    haveI := locallyQuasiFinite_of_isPullback B b' l₁ l b sqY
    haveI := locallyOfFiniteType_of_isPullback B b' l₁ l b sqY
    haveI := isSeparated_of_isPullback B a' k₁ k a
      (isPullback_baseChange_left B w sqX sqY sqX' hk₁ w₁)
    haveI := locallyQuasiFinite_of_isPullback B a' k₁ k a
      (isPullback_baseChange_left B w sqX sqY sqX' hk₁ w₁)
    haveI := locallyOfFiniteType_of_isPullback B a' k₁ k a
      (isPullback_baseChange_left B w sqX sqY sqX' hk₁ w₁)
    (etaleModuleLift B Λ (abPullback.{u, u} B b)).mapDerivedCategory.map
        ((properBaseChangeMap B Λ k f' f l w RF' αF' RF αF).app K) ≫
      (etaleDerivedBaseChangeMap B Λ a f₁ f b sqX RF αF RF₁ αF₁).app
        ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B k)).mapDerivedCategory.obj K) ≫
      RF₁.map ((derivedFShriekBaseChangeIso B Λ a' k₁ k a
        (isPullback_baseChange_left B w sqX sqY sqX' hk₁ w₁)).hom.app K) =
    (derivedFShriekBaseChangeIso B Λ b' l₁ l b sqY).hom.app (RF'.obj K) ≫
      (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l₁)).mapDerivedCategory.map
        ((etaleDerivedBaseChangeMap B Λ a' f'₁ f' b' sqX' RF' αF' RF'₁ αF'₁).app K) ≫
      (properBaseChangeMap B Λ k₁ f'₁ f₁ l₁ w₁ RF'₁ αF'₁ RF₁ αF₁).app
        ((etaleModuleLift B Λ (abPullback.{u, u} B a')).mapDerivedCategory.obj K) := by
  have sqK := isPullback_baseChange_left B w sqX sqY sqX' hk₁ w₁
  have := isProper_of_isPullback B a f₁ f b sqX
  have := isProper_of_isPullback B a' f'₁ f' b' sqX'
  have := isSeparated_of_isPullback B b' l₁ l b sqY
  have := locallyQuasiFinite_of_isPullback B b' l₁ l b sqY
  have := locallyOfFiniteType_of_isPullback B b' l₁ l b sqY
  have := isSeparated_of_isPullback B a' k₁ k a sqK
  have := locallyQuasiFinite_of_isPullback B a' k₁ k a sqK
  have := locallyOfFiniteType_of_isPullback B a' k₁ k a sqK
  have := isRightDerivedFunctor_comp_right _ RF' αF'
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory
  have := isRightDerivedFunctor_comp_right _ RF αF
    (etaleModuleLift B Λ (abPullback.{u, u} B b)).mapDerivedCategory
  have := isRightDerivedFunctor_comp_right _ RF' αF'
    (etaleModuleLift B Λ (abPullback.{u, u} B b')).mapDerivedCategory
  have := isRightDerivedFunctor_comp_right _ RF'₁ αF'₁
    (etaleModuleLift B Λ (fShriekFunctor.{u, u} B l₁)).mapDerivedCategory
  have := isRightDerivedFunctor_comp_right _ RF' αF'
    ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B l)).mapDerivedCategory ⋙
      (etaleModuleLift B Λ (abPullback.{u, u} B b)).mapDerivedCategory)
  have hcube := homotopySquareHom_cube (ComplexShape.up ℤ) _ _ _ _ _ _
    (etaleModuleLiftSquareHom_cube B Λ _ _ _ _ _ _ _ _ _ _ _ _
      (pushforwardFShriekSquareIso B k f' f l w).hom
      (pushforwardFShriekSquareIso B k₁ f'₁ f₁ l₁ w₁).hom
      (directImageBaseChangeNatTrans.{u, u} B a f₁ f b sqX)
      (directImageBaseChangeNatTrans.{u, u} B a' f'₁ f' b' sqX')
      (fShriekProperSupportBaseChangeIso B a' k₁ k a sqK).hom
      (fShriekProperSupportBaseChangeIso B b' l₁ l b sqY).hom
      (pushforwardFShriekSquareIso_baseChange B k f' f l w b a f₁ sqX b' l₁ sqY a' f'₁ sqX' k₁
        w₁ sqK))
  rw [properBaseChangeMap_eq_squareMapOfHom, properBaseChangeMap_eq_squareMapOfHom]
  exact squareMapOfHom_cube
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X' Λ) (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X Λ) (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (ModuleSheaf.{u, u, u} B X'₁ Λ) (ComplexShape.up ℤ))
    (etaleModuleLiftFactorsh B Λ (fShriekFunctor.{u, u} B k))
    (etaleModuleLiftFactorsh B Λ (fShriekFunctor.{u, u} B l))
    (etaleModuleLiftFactorsh B Λ (fShriekFunctor.{u, u} B k₁))
    (etaleModuleLiftFactorsh B Λ (fShriekFunctor.{u, u} B l₁))
    (etaleModuleLiftFactorsh B Λ (abPullback.{u, u} B a'))
    (etaleModuleLiftFactorsh B Λ (abPullback.{u, u} B a))
    (etaleModuleLiftFactorsh B Λ (abPullback.{u, u} B b'))
    (etaleModuleLiftFactorsh B Λ (abPullback.{u, u} B b))
    αF' αF αF'₁ αF₁ _ _ _ _ _ _
    (derivedFShriekBaseChangeIso B Λ b' l₁ l b sqY).hom
    (derivedFShriekBaseChangeIso B Λ a' k₁ k a sqK).hom
    (derivedFShriekBaseChangeIso_hom_app_Qh B Λ b' l₁ l b sqY)
    (derivedFShriekBaseChangeIso_hom_app_Qh B Λ a' k₁ k a sqK) hcube K

end Derived

end AlgebraicGeometry.SmallEtale

end
