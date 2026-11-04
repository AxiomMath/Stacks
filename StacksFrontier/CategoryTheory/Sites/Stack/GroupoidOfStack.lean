module

public import Mathlib.CategoryTheory.Widesubcategory

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.MultiplicativeClass
public import StacksFrontier.CategoryTheory.FiberedCategory.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-! # The category fibred in groupoids associated to a stack

Let `(𝒞, J)` be a site and let `p : 𝒮 ⥤ 𝒞` be a stack: a fibred category whose presheaves
`Mor(x, y)` are sheaves and whose descent data are effective (Stacks 026F). Restricting `𝒮` to the
subcategory `𝒮'` with the same objects and only the strongly cartesian morphisms gives the category
fibred in groupoids `p' : 𝒮' ⥤ 𝒞` associated to `𝒮` (Stacks 03WQ). The result of this file is that
`p'` is a stack in groupoids (Stacks 03YI).

The mathematics is that the passage from `𝒮` to `𝒮'` changes neither descent condition. Every
isomorphism of `𝒮` is strongly cartesian and strongly cartesian morphisms compose, so the
isomorphisms of the fibre of `p'` over an object of `𝒞` are those of the fibre of `p`, and a
descent datum in `𝒮'` relative to a covering family is a descent datum in `𝒮`. Hence conditions (2)
and (3) of Stacks 02ZI for `p'` are conditions (2) and (3) of Stacks 026F for `p`, and condition
(1) is Stacks 03WQ.

## Main results

* `CategoryTheory.Functor.IsStack.isStackInGroupoids_stronglyCartesianOver`: the category fibred in
  groupoids associated to a stack is a stack in groupoids (Stacks 03YI).

## Implementation notes

The subcategory `𝒮'` of Stacks 03WQ is `CategoryTheory.WideSubcategory (stronglyCartesianOver p)`:
its objects are the objects of `𝒮`, and its morphisms `x ⟶ y` are the morphisms of `𝒮` that are
strongly cartesian over their image under `p`. This is a subcategory precisely because that
morphism property contains the identities and is stable under composition
(`stronglyCartesianOver_isMultiplicative`), which is why the instance is supplied inside the
statement from clause (1) of the hypothesis rather than assumed. The functor `p'` is the
restriction of `p`, that is the composite of `CategoryTheory.wideSubcategoryInclusion` with `p`; no
new functor is introduced.

The hypothesis is read in the sieve-and-chosen-pullbacks rendering of a stack
(`CategoryTheory.Functor.IsStack`, Stacks 026F) and the conclusion in the rendering by covering
families with genuine fibre-product overlaps (`CategoryTheory.Functor.IsStackInGroupoids`,
Stacks 02ZI); the two are compared in
`StacksFrontier/CategoryTheory/Sites/Stack/StackBridge.lean`, which is also where the definition of a
stack in groupoids is shown to be the conjunction of the two conditions of Stacks 02ZJ. The
universe of the index type of the covering families is left free, so the conclusion is asserted for
families indexed in every universe.

The proof does not go through `p'.IsStack J`. Condition (2) of Stacks 026F for `p'` is the
statement that the presheaves `Isom(x, y)` of `p` are sheaves — Stacks 02ZF — which the library
does not have in this rendering. Instead the two nontrivial conditions of Stacks 02ZI are
transferred one by one along the inclusion `𝒮' ⥤ 𝒮`, and discharged by the *same* two bridge
results `CategoryTheory.Functor.isomIsSheafFor_of_isStack` and
`CategoryTheory.Functor.DescentDatum.isEffective_of_hasEffectiveDescent` applied to `p` itself.
Neither of those asks that `p` be fibred in groupoids, and both conditions of 02ZI mention only
fibre *isomorphisms*, so the transfer costs nothing: this is the content of the source's "descent
data in `𝒮'` are exactly the same thing as descent data in `𝒮`".

The transfer rests on `CategoryTheory.Functor.StronglyCartesianWide.resDown` and `.resUp`, which
move a cartesian lift between `p'` and `p`. Both directions use the defining property of `𝒮'`: a
morphism of `𝒮'` is strongly cartesian for `p` by fiat, and a morphism of `𝒮` that is strongly
cartesian for `p` is strongly cartesian for `p'` because a factor of a strongly cartesian morphism
through a strongly cartesian morphism is again one (`IsStronglyCartesian.of_comp`) and so lies in
`𝒮'`.

## References

* [StacksProject 03YI](https://stacks.math.columbia.edu/tag/03YI)
-/

@[expose] public section

open CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

-- The values of the restriction `p'` on objects and morphisms are those of `p` only after
-- unfolding the wide subcategory inclusion and the composite, which the defeq check does not do at
-- reducible transparency.
set_option backward.isDefEq.respectTransparency false

/-! ### The restriction of a fibred category to its strongly cartesian morphisms

The dictionary between `p : 𝒮 ⥤ 𝒞` and the functor `p' : 𝒮' ⥤ 𝒞` of Stacks 03WQ. Since `p'` is
the composite of the inclusion with `p`, the two functors have literally the same values on objects
and on the underlying morphisms, so lying over a base morphism is the same condition on either
side; what needs an argument is being *strongly cartesian*, and that is where membership in
`stronglyCartesianOver p` is used. -/

namespace StronglyCartesianWide

/-- The category `𝒮'` of Stacks 03WQ: the objects of `𝒮`, and as morphisms only those of `𝒮` that
are strongly cartesian over their image under `p`. -/
abbrev Wide (p : 𝒮 ⥤ 𝒞) [(stronglyCartesianOver p).IsMultiplicative] :=
  WideSubcategory (stronglyCartesianOver p)

/-- The functor `p' : 𝒮' ⥤ 𝒞` of Stacks 03WQ, the restriction of `p` to `𝒮'`. -/
abbrev res (p : 𝒮 ⥤ 𝒞) [(stronglyCartesianOver p).IsMultiplicative] : Wide p ⥤ 𝒞 :=
  wideSubcategoryInclusion (stronglyCartesianOver p) ⋙ p

section

variable {p : 𝒮 ⥤ 𝒞}

/-! #### Membership in the morphism property -/

/-- A morphism strongly cartesian over some base morphism is a morphism of `𝒮'`. -/
theorem mem_of_isStronglyCartesian {a b : 𝒮} (φ : a ⟶ b) {R S : 𝒞} (f : R ⟶ S)
    (h : p.IsStronglyCartesian f φ) : stronglyCartesianOver p φ := by
  have := h
  exact Functor.IsStronglyCartesian.isStronglyCartesian_map p φ f

/-- Every isomorphism of `𝒮` is a morphism of `𝒮'`. -/
theorem mem_of_isIso {a b : 𝒮} (φ : a ⟶ b) (h : IsIso φ) : stronglyCartesianOver p φ := by
  have := h
  exact Functor.IsStronglyCartesian.of_isIso p (p.map φ) φ

/-- A morphism of `𝒮'` is strongly cartesian for `p` over every base morphism it lifts. -/
theorem isStronglyCartesian_of_mem {a b : 𝒮} {φ : a ⟶ b} (hφ : stronglyCartesianOver p φ)
    {R S : 𝒞} (f : R ⟶ S) (h : p.IsHomLift f φ) : p.IsStronglyCartesian f φ := by
  have := h
  subst_hom_lift p f φ
  exact hφ

end

section

variable {p : 𝒮 ⥤ 𝒞} [(stronglyCartesianOver p).IsMultiplicative]

/-! #### Lying over a base morphism -/

/-- Lying over `f` for `p'` gives lying over `f` for `p`. -/
theorem isHomLift_hom {X Y : Wide p} {φ : X ⟶ Y} {R S : 𝒞} {f : R ⟶ S}
    (h : (res p).IsHomLift f φ) : p.IsHomLift f φ.hom := by
  have := h
  exact CategoryTheory.IsHomLift.of_fac' p f φ.hom
    (CategoryTheory.IsHomLift.domain_eq (res p) f φ)
    (CategoryTheory.IsHomLift.codomain_eq (res p) f φ)
    (CategoryTheory.IsHomLift.fac' (res p) f φ)

/-- Lying over `f` for `p` gives lying over `f` for `p'`. -/
theorem isHomLift_mk {X Y : Wide p} (φ : X ⟶ Y) {R S : 𝒞} {f : R ⟶ S}
    (h : p.IsHomLift f φ.hom) : (res p).IsHomLift f φ := by
  have := h
  exact CategoryTheory.IsHomLift.of_fac' (res p) f φ
    (CategoryTheory.IsHomLift.domain_eq p f φ.hom)
    (CategoryTheory.IsHomLift.codomain_eq p f φ.hom)
    (CategoryTheory.IsHomLift.fac' p f φ.hom)

/-- A morphism of the fibre of `p'` is a morphism of the fibre of `p`. -/
theorem fibreHom_hom {U : 𝒞} {A B : Wide p} {hA : (res p).obj A = U} {hB : (res p).obj B = U}
    {φ : A ⟶ B} (h : FibreHom (res p) A B hA hB φ) : FibreHom p A.obj B.obj hA hB φ.hom :=
  isHomLift_hom h

/-- A morphism of `𝒮'` which is a morphism of the fibre of `p` is one of the fibre of `p'`. -/
theorem fibreHom_mk {U : 𝒞} {A B : Wide p} {hA : (res p).obj A = U} {hB : (res p).obj B = U}
    (φ : A ⟶ B) (h : FibreHom p A.obj B.obj hA hB φ.hom) : FibreHom (res p) A B hA hB φ :=
  isHomLift_mk φ h

/-! #### Strongly cartesian morphisms -/

/-- The factorisation through a strongly cartesian morphism of `𝒮'` exists and is unique in `𝒮'`:
the fill-in produced in `𝒮` is a factor of a strongly cartesian morphism through a strongly
cartesian one, hence a morphism of `𝒮'`. -/
private theorem existsUnique_wide_factor {X Y Z : Wide p} (φ : Y ⟶ Z) (ψ : X ⟶ Z) {R S T : 𝒞}
    {f : S ⟶ T} {g : R ⟶ S} (hφ : p.IsStronglyCartesian f φ.hom)
    (hψ : p.IsHomLift (g ≫ f) ψ.hom) :
    ∃! χ : X ⟶ Y, (res p).IsHomLift g χ ∧ χ ≫ φ = ψ := by
  have hψsc : p.IsStronglyCartesian (g ≫ f) ψ.hom :=
    isStronglyCartesian_of_mem ψ.property _ inferInstance
  obtain ⟨χ, ⟨hχlift, hχfac⟩, hχuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property p f φ.hom g (g ≫ f) rfl ψ.hom
  have : p.IsStronglyCartesian (g ≫ f) (χ ≫ φ.hom) := by rw [hχfac]; exact hψsc
  have : p.IsStronglyCartesian g χ :=
    Functor.IsStronglyCartesian.of_comp p (g := f) (ψ := φ.hom)
  have hmem : stronglyCartesianOver p χ := mem_of_isStronglyCartesian χ g inferInstance
  refine ⟨⟨χ, hmem⟩, ⟨isHomLift_mk ⟨χ, hmem⟩ hχlift, ?_⟩, ?_⟩
  · exact WideSubcategory.hom_ext _ (by simpa using hχfac)
  · rintro χ' ⟨h1, h2⟩
    refine WideSubcategory.hom_ext _ (hχuniq χ'.hom ⟨isHomLift_hom h1, ?_⟩)
    simpa using congrArg (fun t => InducedWideCategory.Hom.hom t) h2

/-- A morphism of `𝒮'` whose underlying morphism is `p`-strongly cartesian over `f` is
`p'`-strongly cartesian over `f`. -/
theorem isStronglyCartesian_mk {X Y : Wide p} (φ : X ⟶ Y) {R S : 𝒞} {f : R ⟶ S}
    (hφ : p.IsStronglyCartesian f φ.hom) : (res p).IsStronglyCartesian f φ := by
  have := hφ
  have : (res p).IsHomLift f φ := isHomLift_mk φ inferInstance
  exact { universal_property' := fun g ψ hψ =>
    existsUnique_wide_factor φ ψ hφ (isHomLift_hom hψ) }

/-! #### Isomorphisms -/

/-- An isomorphism of `𝒮'` has an underlying isomorphism of `𝒮`. -/
theorem isIso_hom {X Y : Wide p} (φ : X ⟶ Y) (h : IsIso φ) : IsIso φ.hom := by
  have := h
  exact ⟨(CategoryTheory.inv φ).hom,
    congrArg (fun t => InducedWideCategory.Hom.hom t) (IsIso.hom_inv_id (f := φ)),
    congrArg (fun t => InducedWideCategory.Hom.hom t) (IsIso.inv_hom_id (f := φ))⟩

/-- A morphism of `𝒮'` whose underlying morphism is an isomorphism is an isomorphism: the inverse
is an isomorphism, hence strongly cartesian, hence again a morphism of `𝒮'`. -/
theorem isIso_mk {X Y : Wide p} (φ : X ⟶ Y) (h : IsIso φ.hom) : IsIso φ := by
  have := h
  refine ⟨⟨CategoryTheory.inv φ.hom,
      mem_of_isIso (CategoryTheory.inv φ.hom) inferInstance⟩, ?_, ?_⟩ <;>
    refine WideSubcategory.hom_ext _ ?_ <;> simp

end

/-! #### Restrictions -/

/-- A canonical comparison lies over the base morphism it is taken along. -/
theorem compTo_isHomLift {𝒳 : Type*} [Category 𝒳] (r : 𝒳 ⥤ 𝒞)
    {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U) {h : W ⟶ U} (hh : h = g ≫ f)
    {z : 𝒳} {hz : r.obj z = U}
    (xr : Restriction r f z hz) (xrW : Restriction r h z hz) :
    r.IsHomLift (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm)
      (Restriction.compTo r g f hh xr xrW) := by
  have : r.IsHomLift ((eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
      (eqToHom xr.hpt ≫ f ≫ eqToHom hz.symm)) xrW.hom := by
    have e : (eqToHom xrW.hpt ≫ g ≫ eqToHom xr.hpt.symm) ≫
        (eqToHom xr.hpt ≫ f ≫ eqToHom hz.symm)
        = eqToHom xrW.hpt ≫ h ≫ eqToHom hz.symm := by subst hh; simp
    rw [e]; exact xrW.isHomLift
  exact Functor.IsStronglyCartesian.map_isHomLift r
    (eqToHom xr.hpt ≫ f ≫ eqToHom hz.symm) xr.hom rfl xrW.hom

section

variable {p : 𝒮 ⥤ 𝒞} [(stronglyCartesianOver p).IsMultiplicative]

/-- A restriction for `p'` read as a restriction for `p`: the same object and the same cartesian
arrow, which is `p`-strongly cartesian because it is a morphism of `𝒮'`. -/
@[implicit_reducible]
def resDown {X : Wide p} {V U : 𝒞} {f : V ⟶ U} {hX : (res p).obj X = U}
    (R : Restriction (res p) f X hX) : Restriction p f X.obj hX where
  pt := R.pt.obj
  hpt := R.hpt
  hom := R.hom.hom
  isHomLift := isHomLift_hom R.isHomLift
  isCart := isStronglyCartesian_of_mem R.hom.property _ (isHomLift_hom R.isHomLift)

/-- A restriction for `p` read as a restriction for `p'`: the cartesian arrow is strongly
cartesian, hence a morphism of `𝒮'`, and it stays strongly cartesian for `p'`. -/
def resUp {x : 𝒮} {V U : 𝒞} {f : V ⟶ U} {hx : p.obj x = U}
    (R : Restriction p f x hx) : Restriction (res p) f (⟨x⟩ : Wide p) hx where
  pt := ⟨R.pt⟩
  hpt := R.hpt
  hom := ⟨R.hom, mem_of_isStronglyCartesian R.hom _ R.isCart⟩
  isHomLift := isHomLift_mk _ R.isHomLift
  isCart := isStronglyCartesian_mk _ R.isCart

/-- The source of `resDown R` is the underlying object of the source of `R`. -/
@[simp]
theorem resDown_pt {X : Wide p} {V U : 𝒞} {f : V ⟶ U} {hX : (res p).obj X = U}
    (R : Restriction (res p) f X hX) : (resDown R).pt = R.pt.obj := rfl

/-- The cartesian arrow of `resDown R` is the underlying morphism of that of `R`. -/
@[simp]
theorem resDown_hom {X : Wide p} {V U : 𝒞} {f : V ⟶ U} {hX : (res p).obj X = U}
    (R : Restriction (res p) f X hX) : (resDown R).hom = R.hom.hom := rfl

/-- The source of `resUp R` has underlying object the source of `R`. -/
@[simp]
theorem resUp_pt {x : 𝒮} {V U : 𝒞} {f : V ⟶ U} {hx : p.obj x = U}
    (R : Restriction p f x hx) : (resUp R).pt.obj = R.pt := rfl

/-- The cartesian arrow of `resUp R` has underlying morphism the cartesian arrow of `R`. -/
@[simp]
theorem resUp_hom {x : 𝒮} {V U : 𝒞} {f : V ⟶ U} {hx : p.obj x = U}
    (R : Restriction p f x hx) : (resUp R).hom.hom = R.hom := rfl

/-- Reading a restriction for `p` as one for `p'` and back gives the original restriction. -/
@[simp]
theorem resDown_resUp {x : 𝒮} {V U : 𝒞} {f : V ⟶ U} {hx : p.obj x = U}
    (R : Restriction p f x hx) : resDown (resUp R) = R := rfl

/-- The identity restriction for `p'` reads as the identity restriction for `p`. -/
@[simp]
theorem resDown_id {U : 𝒞} (X : Wide p) (hX : (res p).obj X = U) :
    resDown (Restriction.id (res p) X hX) = Restriction.id p X.obj hX := rfl

/-- The canonical comparison of two restrictions for `p'` has as underlying morphism the canonical
comparison of the two restrictions read for `p`. Both lie over the same base morphism and both
factor the second cartesian arrow through the first, so they agree by the universal property. -/
theorem resDown_compTo {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U) {h : W ⟶ U} (hh : h = g ≫ f)
    {X : Wide p} {hX : (res p).obj X = U}
    (Xr : Restriction (res p) f X hX) (XrW : Restriction (res p) h X hX) :
    (Restriction.compTo (res p) g f hh Xr XrW).hom
      = Restriction.compTo p g f hh (resDown Xr) (resDown XrW) := by
  have : p.IsHomLift (eqToHom XrW.hpt ≫ g ≫ eqToHom Xr.hpt.symm)
      (Restriction.compTo (res p) g f hh Xr XrW).hom :=
    isHomLift_hom (compTo_isHomLift (res p) g f hh Xr XrW)
  have : p.IsHomLift (eqToHom XrW.hpt ≫ g ≫ eqToHom Xr.hpt.symm)
      (Restriction.compTo p g f hh (resDown Xr) (resDown XrW)) :=
    compTo_isHomLift p g f hh (resDown Xr) (resDown XrW)
  refine Functor.IsStronglyCartesian.ext p
    (eqToHom (resDown Xr).hpt ≫ f ≫ eqToHom hX.symm) (resDown Xr).hom
    (eqToHom XrW.hpt ≫ g ≫ eqToHom Xr.hpt.symm) ?_
  rw [Restriction.compTo_hom p g f hh (resDown Xr) (resDown XrW)]
  simpa using congrArg (fun t => InducedWideCategory.Hom.hom t)
    (Restriction.compTo_hom (res p) g f hh Xr XrW)

/-- Being a canonical restriction transfers from `p'` to `p`. -/
theorem isRestrictionOf_hom {W V Ux Uy : 𝒞} {g : W ⟶ V} {fx : V ⟶ Ux} {fy : V ⟶ Uy}
    {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy} {hfx : hx_ = g ≫ fx} {hfy : hy_ = g ≫ fy}
    {X Y : Wide p} {hX : (res p).obj X = Ux} {hY : (res p).obj Y = Uy}
    {Xr : Restriction (res p) fx X hX} {Yr : Restriction (res p) fy Y hY}
    {XrW : Restriction (res p) hx_ X hX} {YrW : Restriction (res p) hy_ Y hY}
    {α : Xr.pt ⟶ Yr.pt} {β : XrW.pt ⟶ YrW.pt}
    (hβ : IsRestrictionOf (res p) g hfx hfy Xr Yr XrW YrW α β) :
    IsRestrictionOf p g hfx hfy (resDown Xr) (resDown Yr) (resDown XrW) (resDown YrW)
      α.hom β.hom := by
  unfold IsRestrictionOf
  rw [← resDown_compTo g fy hfy Yr YrW, ← resDown_compTo g fx hfx Xr XrW]
  simpa using congrArg (fun t => InducedWideCategory.Hom.hom t) hβ

/-- Being a canonical restriction transfers from `p` to `p'`. -/
theorem isRestrictionOf_mk {W V Ux Uy : 𝒞} (g : W ⟶ V) {fx : V ⟶ Ux} {fy : V ⟶ Uy}
    {hx_ : W ⟶ Ux} {hy_ : W ⟶ Uy} (hfx : hx_ = g ≫ fx) (hfy : hy_ = g ≫ fy)
    {X Y : Wide p} {hX : (res p).obj X = Ux} {hY : (res p).obj Y = Uy}
    (Xr : Restriction (res p) fx X hX) (Yr : Restriction (res p) fy Y hY)
    (XrW : Restriction (res p) hx_ X hX) (YrW : Restriction (res p) hy_ Y hY)
    (α : Xr.pt ⟶ Yr.pt) (β : XrW.pt ⟶ YrW.pt)
    (hβ : IsRestrictionOf p g hfx hfy (resDown Xr) (resDown Yr) (resDown XrW) (resDown YrW)
      α.hom β.hom) :
    IsRestrictionOf (res p) g hfx hfy Xr Yr XrW YrW α β := by
  unfold IsRestrictionOf at hβ
  rw [← resDown_compTo g fy hfy Yr YrW, ← resDown_compTo g fx hfx Xr XrW] at hβ
  exact WideSubcategory.hom_ext _ (by simpa using hβ)

/-! #### Descent data -/

/-- A descent datum for `p'` relative to a covering family read as a descent datum for `p`: every
piece of data is the underlying object or morphism of `𝒮`, and every condition is the transfer of
the corresponding condition for `p'`. This is the source's "descent data in `𝒮'` are exactly the
same thing as descent data in `𝒮`". -/
def ddDown {U : 𝒞} {I : Type w} {V : I → 𝒞} {f : ∀ i, V i ⟶ U}
    {Vij : I → I → 𝒞} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
    {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
    {Vijk : I → I → I → 𝒞}
    {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
    {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
    {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
    {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
    {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
    {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
    {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
    (D : DescentDatum (res p) V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ where
  x i := (D.x i).obj
  hx i := D.hx i
  xrij i j := resDown (D.xrij i j)
  xrji i j := resDown (D.xrji i j)
  φ i j := (D.φ i j).hom
  φ_fibreHom i j := fibreHom_hom (D.φ_fibreHom i j)
  φ_iso i j := isIso_hom _ (D.φ_iso i j)
  wi i j k := resDown (D.wi i j k)
  wj i j k := resDown (D.wj i j k)
  wk i j k := resDown (D.wk i j k)
  αij i j k := (D.αij i j k).hom
  αjk i j k := (D.αjk i j k).hom
  αik i j k := (D.αik i j k).hom
  αij_restr i j k := isRestrictionOf_hom (D.αij_restr i j k)
  αjk_restr i j k := isRestrictionOf_hom (D.αjk_restr i j k)
  s₁₃ i j k := D.s₁₃ i j k
  hs₁₃₁ i j k := D.hs₁₃₁ i j k
  hs₁₃₂ i j k := D.hs₁₃₂ i j k
  αik_restr i j k := isRestrictionOf_hom (D.αik_restr i j k)
  cocycle i j k := by
    simpa using congrArg (fun t => InducedWideCategory.Hom.hom t) (D.cocycle i j k)

/-! #### Stacks 03WQ: the restriction is fibred in groupoids -/

/-- **The restriction of a fibred category to its strongly cartesian morphisms is fibred in
groupoids** (the conclusion of Stacks 03WQ). Lifts exist because `p` is fibred and a strongly
cartesian lift is a morphism of `𝒮'`; fill-ins exist and are unique because the morphism of `𝒮'`
being lifted against is strongly cartesian for `p`, and the fill-in it produces is a factor of a
strongly cartesian morphism through a strongly cartesian one, hence a morphism of `𝒮'`. -/
theorem isFiberedInGroupoids (p : 𝒮 ⥤ 𝒞) [p.IsFibered]
    [(stronglyCartesianOver p).IsMultiplicative] : (res p).IsFiberedInGroupoids where
  exists_lift := by
    intro V U f X hX
    obtain ⟨W, a, ha⟩ :=
      Functor.IsFibered.exists_isStronglyCartesian p (Y := X.obj) (f ≫ eqToHom hX.symm)
    have := ha
    have hW : p.obj W = V := CategoryTheory.IsHomLift.domain_eq p (f ≫ eqToHom hX.symm) a
    have hlift : p.IsHomLift f a := by
      refine CategoryTheory.IsHomLift.of_fac' p f a hW hX ?_
      simpa using CategoryTheory.IsHomLift.fac' p (f ≫ eqToHom hX.symm) a
    exact ⟨⟨W⟩, ⟨a, mem_of_isStronglyCartesian a _ ha⟩, isHomLift_mk _ hlift⟩
  unique_lift := by
    intro X Y Z φ ψ g hg
    have hgp : g ≫ p.map φ.hom = p.map ψ.hom := hg
    have : p.IsStronglyCartesian (p.map φ.hom) φ.hom := φ.property
    obtain ⟨χ, ⟨hχlift, hχfac⟩, hχuniq⟩ := existsUnique_wide_factor φ ψ (g := g) this
      (by rw [hgp]; infer_instance)
    refine ⟨χ, ⟨(CategoryTheory.IsHomLift.eq_of_isHomLift (res p) g χ).symm, hχfac⟩,
      fun χ' ⟨h1, h2⟩ => hχuniq χ' ⟨?_, h2⟩⟩
    have : (res p).IsHomLift g χ' := by rw [← (h1 : p.map χ'.hom = g)]; infer_instance
    assumption

end

end StronglyCartesianWide

/-- **The category fibred in groupoids associated to a stack is a stack in groupoids.** Let
`(𝒞, J)` be a site and let `p : 𝒮 ⥤ 𝒞` be a stack (Stacks 026F). Let `p' : 𝒮' ⥤ 𝒞` be the category
fibred in groupoids associated to `𝒮` constructed in Stacks 03WQ: the objects of `𝒮'` are those
of `𝒮`, its morphisms are the strongly cartesian morphisms of `𝒮`, and `p'` is the restriction
of `p`. Then
`p'` is a stack in groupoids (Stacks 02ZI): it is fibred in groupoids, its presheaves `Isom(x, y)`
are sheaves, and every descent datum relative to a covering family of `J` is effective. -/
@[stacks 03YI]
public theorem IsStack.isStackInGroupoids_stronglyCartesianOver
    {p : 𝒮 ⥤ 𝒞} {J : GrothendieckTopology 𝒞} (hp : p.IsStack J) :
    haveI : p.IsFibered := hp.isFibered
    haveI : (stronglyCartesianOver p).IsMultiplicative :=
      stronglyCartesianOver_isMultiplicative p
    IsStackInGroupoids.{w} (wideSubcategoryInclusion (stronglyCartesianOver p) ⋙ p) J := by
  have : p.IsFibered := hp.isFibered
  have : (stronglyCartesianOver p).IsMultiplicative :=
    stronglyCartesianOver_isMultiplicative p
  refine
    { isFiberedInGroupoids := StronglyCartesianWide.isFiberedInGroupoids p
      isom_isSheaf := ?_
      effective_descent := ?_ }
  · -- Condition (2). Read the fibre isomorphisms and their overlap comparisons in `𝒮`, amalgamate
    -- them there with `isomIsSheafFor_of_isStack` for `p`, and read the amalgamation back in `𝒮'`:
    -- it is an isomorphism, hence a morphism of `𝒮'`.
    intro U X Y hX hY I V f hcov Vij pr₁ pr₂ hVij Xr Yr Xrij Yrij φ hfib hiso hcompat
    obtain ⟨g, ⟨hgfib, hgiso, hgfac⟩, hguniq⟩ :=
      isomIsSheafFor_of_isStack hp X.obj Y.obj hX hY V f hcov Vij pr₁ pr₂ hVij
        (fun i => StronglyCartesianWide.resDown (Xr i))
        (fun i => StronglyCartesianWide.resDown (Yr i))
        (fun i j => StronglyCartesianWide.resDown (Xrij i j))
        (fun i j => StronglyCartesianWide.resDown (Yrij i j))
        (fun i => (φ i).hom)
        (fun i => StronglyCartesianWide.fibreHom_hom (hfib i))
        (fun i => StronglyCartesianWide.isIso_hom _ (hiso i))
        (fun i j => by
          obtain ⟨γ, hγfib, hγ₁, hγ₂⟩ := hcompat i j
          exact ⟨γ.hom, StronglyCartesianWide.fibreHom_hom hγfib,
            StronglyCartesianWide.isRestrictionOf_hom hγ₁,
            StronglyCartesianWide.isRestrictionOf_hom hγ₂⟩)
    refine ⟨⟨g, StronglyCartesianWide.mem_of_isIso g hgiso⟩,
      ⟨StronglyCartesianWide.fibreHom_mk _ hgfib,
        StronglyCartesianWide.isIso_mk _ hgiso, fun i => ?_⟩, ?_⟩
    · exact WideSubcategory.hom_ext _ (by simpa using hgfac i)
    · rintro g' ⟨k₁, k₂, k₃⟩
      refine WideSubcategory.hom_ext _ (hguniq g'.hom
        ⟨StronglyCartesianWide.fibreHom_hom k₁,
          StronglyCartesianWide.isIso_hom _ k₂, fun i => ?_⟩)
      simpa using congrArg (fun t => InducedWideCategory.Hom.hom t) (k₃ i)
  · -- Condition (3). Read the descent datum in `𝒮`, descend it there with
    -- `DescentDatum.isEffective_of_hasEffectiveDescent` for `p`, and read the descended object and
    -- its comparison isomorphisms back in `𝒮'`.
    intro U I V f hcov Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D
    obtain ⟨x, hx, xr, ψ, hψfib, hψiso, hψcompat⟩ :=
      (StronglyCartesianWide.ddDown D).isEffective_of_hasEffectiveDescent
        hp.hasEffectiveDescent hcov
    refine ⟨⟨x⟩, hx, fun i => StronglyCartesianWide.resUp (xr i),
      fun i => ⟨ψ i, StronglyCartesianWide.mem_of_isIso _ (hψiso i)⟩,
      fun i => StronglyCartesianWide.fibreHom_mk _ (hψfib i),
      fun i => StronglyCartesianWide.isIso_mk _ (hψiso i), fun i j => ?_⟩
    obtain ⟨xrij, ψir, ψjr, hf₁, hf₂, hi₁, hi₂, hr₁, hr₂, heq⟩ := hψcompat i j
    refine ⟨StronglyCartesianWide.resUp xrij,
      ⟨ψir, StronglyCartesianWide.mem_of_isIso _ hi₁⟩,
      ⟨ψjr, StronglyCartesianWide.mem_of_isIso _ hi₂⟩,
      StronglyCartesianWide.fibreHom_mk _ hf₁, StronglyCartesianWide.fibreHom_mk _ hf₂,
      StronglyCartesianWide.isIso_mk _ hi₁, StronglyCartesianWide.isIso_mk _ hi₂,
      StronglyCartesianWide.isRestrictionOf_mk _ _ _ _ _ _ _ _ _ hr₁,
      StronglyCartesianWide.isRestrictionOf_mk _ _ _ _ _ _ _ _ _ hr₂, ?_⟩
    exact WideSubcategory.hom_ext _ heq

end CategoryTheory.Functor

end
