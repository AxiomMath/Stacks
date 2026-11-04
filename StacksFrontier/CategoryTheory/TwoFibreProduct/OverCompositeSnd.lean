module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverComparison
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# A 2-fibre product along a composite second leg is an iterated 2-fibre product

Fix a base category `𝒞` and categories `𝒰`, `𝒳`, `𝒴`, `𝒵` over `𝒞` with structure functors
`p𝒰`, `p𝒳`, `p𝒴`, `p𝒵`, together with 1-morphisms over `𝒞`

```text
z : 𝒰 ⥤ 𝒵,   f : 𝒳 ⥤ 𝒴,   g : 𝒴 ⥤ 𝒵.
```

The 2-fibre product over `𝒞` is `CategoryTheory.TwoFibreProductOver`. Taking the second leg to
be the composite `f ⋙ g` gives `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳`, and it is the 2-fibre product of `𝒳`
with the intermediate product `𝒰 ×_{z, 𝒵, g} 𝒴`, the latter viewed as a category over `𝒞`
through its structure functor and mapped to `𝒴` by its second projection:

```text
𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳  ≃  (𝒰 ×_{z, 𝒵, g} 𝒴) ×_{π₂, 𝒴, f} 𝒳.
```

This is the categorical form of the elementary identity `U ×_Z X = (U ×_Z Y) ×_Y X` for a point
`U ⟶ Z` and a factorization `X ⟶ Y ⟶ Z`.

The comparison is an *equivalence of categories*, not an isomorphism: an object of the
right-hand side carries an arbitrary vertical comparison isomorphism `π₂ m ≅ f x`, while the
comparison functor produces only the identity one, so the two categories are not isomorphic.
It commutes with the projection to `𝒰` on the nose, so
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence` turns it into an equivalence
over `𝒰` in the sense of `StacksRepresentableCFG.EquivalenceOver` once the two projections are
known to be fibred in groupoids.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.splitSndMiddle`: the object of the intermediate product
  `𝒰 ×_𝒵 𝒴` attached to an object of `𝒰 ×_𝒵 𝒳`, namely `(W, w, x, φ) ↦ (W, w, f x, φ)`.
* `CategoryTheory.TwoFibreProductOver.splitSndMiddleMap`: its action on morphisms.
* `CategoryTheory.TwoFibreProductOver.splitSnd`: the comparison functor
  `𝒰 ×_𝒵 𝒳 ⥤ (𝒰 ×_𝒵 𝒴) ×_𝒴 𝒳`, `(W, w, x, φ) ↦ (W, (W, w, f x, φ), x, 𝟙)`.

## Main results

* `CategoryTheory.TwoFibreProductOver.isEquivalence_splitSnd`: the comparison is an equivalence
  of categories.
* `CategoryTheory.TwoFibreProductOver.splitSnd_comp_fst_comp_fst`: it is strictly over `𝒰`.
* `CategoryTheory.TwoFibreProductOver.nonempty_equivalenceOver_splitSnd`: the decomposition as
  an equivalence over `𝒰`.
* `CategoryTheory.TwoFibreProductOver.nonempty_equivalenceOver_baseChange_splitSnd`: the
  decomposition base changed along a 1-morphism `w : 𝒯 ⥤ 𝒰 ×_𝒵 𝒴`, which identifies
  `𝒯 ×_{𝒰 ×_𝒵 𝒴} (𝒰 ×_𝒵 𝒳)` with `𝒯 ×_{w ⋙ π₂, 𝒴, f} 𝒳` over `𝒯`.

## Implementation notes

The comparison isomorphism of an object of `𝒰 ×_𝒵 𝒳` is literally reused as the comparison
isomorphism of the attached object of `𝒰 ×_𝒵 𝒴`: both have type `z w ≅ g (f x)`, since
`(f ⋙ g).obj x` and `g.obj (f.obj x)` are the same term. That is why
`CategoryTheory.TwoFibreProductOver.splitSndMiddle` needs no transport and the comparison
commutes with the projections definitionally.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe vC vT vU vX vY vZ uC uT uU uX uY uZ

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒰 : Type uU} [Category.{vU} 𝒰]
  {𝒳 : Type uX} [Category.{vX} 𝒳] {𝒴 : Type uY} [Category.{vY} 𝒴]
  {𝒵 : Type uZ} [Category.{vZ} 𝒵]
  (p𝒰 : 𝒰 ⥤ 𝒞) (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞)
  (z : 𝒰 ⥤ 𝒵) (f : 𝒳 ⥤ 𝒴) (g : 𝒴 ⥤ 𝒵) (hf : f ⋙ p𝒴 = p𝒳)

/-- The object `(W, w, f x, φ)` of the intermediate 2-fibre product `𝒰 ×_{z, 𝒵, g} 𝒴` attached
to an object `(W, w, x, φ : z w ≅ g (f x))` of `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳`. The comparison
isomorphism is the same term on both sides. -/
def splitSndMiddle (D : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)) :
    TwoFibreProductOver p𝒰 p𝒴 p𝒵 z g where
  base := D.base
  x := D.x
  y := f.obj D.y
  hx := D.hx
  hy := (Functor.congr_obj hf D.y).trans D.hy
  iso := D.iso
  vertical := D.vertical

/-- The base object of `splitSndMiddle D` is that of `D`. -/
@[simp] lemma splitSndMiddle_base (D : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)) :
    (splitSndMiddle p𝒰 p𝒳 p𝒴 p𝒵 z f g hf D).base = D.base := rfl

/-- The `𝒰`-component of `splitSndMiddle D` is that of `D`. -/
@[simp] lemma splitSndMiddle_x (D : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)) :
    (splitSndMiddle p𝒰 p𝒳 p𝒴 p𝒵 z f g hf D).x = D.x := rfl

/-- The `𝒴`-component of `splitSndMiddle D` is the image under `f` of the `𝒳`-component of
`D`. -/
@[simp] lemma splitSndMiddle_y (D : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)) :
    (splitSndMiddle p𝒰 p𝒳 p𝒴 p𝒵 z f g hf D).y = f.obj D.y := rfl

/-- The comparison isomorphism of `splitSndMiddle D` is that of `D`. -/
@[simp] lemma splitSndMiddle_iso (D : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)) :
    (splitSndMiddle p𝒰 p𝒳 p𝒴 p𝒵 z f g hf D).iso = D.iso := rfl

/-- The action of `CategoryTheory.TwoFibreProductOver.splitSndMiddle` on a morphism: the
`𝒰`-component is unchanged and the `𝒴`-component is the image under `f` of the
`𝒳`-component. -/
def splitSndMiddleMap {D D' : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)} (ψ : D ⟶ D') :
    splitSndMiddle p𝒰 p𝒳 p𝒴 p𝒵 z f g hf D ⟶ splitSndMiddle p𝒰 p𝒳 p𝒴 p𝒵 z f g hf D' where
  hbase := ψ.hbase
  a := ψ.a
  b := f.map ψ.b
  ha := ψ.ha
  hb := by
    have := ψ.hb
    exact Functor.isHomLift_map_of_comp_eq hf ψ.hbase ψ.b
  w := ψ.w

/-- The base morphism of `splitSndMiddleMap ψ` is that of `ψ`. -/
@[simp] lemma splitSndMiddleMap_hbase {D D' : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)}
    (ψ : D ⟶ D') : (splitSndMiddleMap p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ψ).hbase = ψ.hbase := rfl

/-- The `𝒰`-component of `splitSndMiddleMap ψ` is that of `ψ`. -/
@[simp] lemma splitSndMiddleMap_a {D D' : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)}
    (ψ : D ⟶ D') : (splitSndMiddleMap p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ψ).a = ψ.a := rfl

/-- The `𝒴`-component of `splitSndMiddleMap ψ` is the image under `f` of the `𝒳`-component of
`ψ`. -/
@[simp] lemma splitSndMiddleMap_b {D D' : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)}
    (ψ : D ⟶ D') : (splitSndMiddleMap p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ψ).b = f.map ψ.b := rfl

/-- The comparison `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳 ⥤ (𝒰 ×_{z, 𝒵, g} 𝒴) ×_{π₂, 𝒴, f} 𝒳`: an object
`(W, w, x, φ)` is sent to the object of the iterated product with first component the attached
object `(W, w, f x, φ)` of the intermediate product, second component `x`, and *identity*
comparison isomorphism. -/
def splitSnd :
    TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g) ⥤
      TwoFibreProductOver (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f where
  obj D :=
    { base := D.base
      x := splitSndMiddle p𝒰 p𝒳 p𝒴 p𝒵 z f g hf D
      y := D.y
      hx := rfl
      hy := D.hy
      iso := Iso.refl _
      vertical :=
        IsHomLift.id (show p𝒴.obj (f.obj D.y) = D.base from
          (Functor.congr_obj hf D.y).trans D.hy) }
  map {_ _} ψ :=
    { hbase := ψ.hbase
      a := splitSndMiddleMap p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ψ
      b := ψ.b
      ha := structureFunctor_isHomLift (splitSndMiddleMap p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ψ) ψ.hbase ψ.ha
      hb := ψ.hb
      w := (Category.comp_id _).trans (Category.id_comp _).symm }
  map_id D := Hom.ext' (Hom.ext' rfl (f.map_id D.y)) rfl
  map_comp ψ ψ' := Hom.ext' (Hom.ext' rfl (f.map_comp ψ.b ψ'.b)) rfl

/-- The first component of `(splitSnd …).obj D` is `splitSndMiddle D`. -/
@[simp] lemma splitSnd_obj_x (D : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)) :
    ((splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf).obj D).x = splitSndMiddle p𝒰 p𝒳 p𝒴 p𝒵 z f g hf D := rfl

/-- The second component of `(splitSnd …).obj D` is the `𝒳`-component of `D`. -/
@[simp] lemma splitSnd_obj_y (D : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)) :
    ((splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf).obj D).y = D.y := rfl

/-- The comparison isomorphism of `(splitSnd …).obj D` is the identity. -/
@[simp] lemma splitSnd_obj_iso (D : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)) :
    ((splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf).obj D).iso = Iso.refl _ := rfl

/-- The first component of `(splitSnd …).map ψ` is `splitSndMiddleMap ψ`. -/
@[simp] lemma splitSnd_map_a {D D' : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)} (ψ : D ⟶ D') :
    ((splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf).map ψ).a =
      splitSndMiddleMap p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ψ := rfl

/-- The second component of `(splitSnd …).map ψ` is the `𝒳`-component of `ψ`. -/
@[simp] lemma splitSnd_map_b {D D' : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g)} (ψ : D ⟶ D') :
    ((splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf).map ψ).b = ψ.b := rfl

/-- The comparison is a 1-morphism over `𝒞`: composing it with the structure functor of the
iterated product gives the structure functor of `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳`. -/
@[simp] lemma splitSnd_comp_structureFunctor :
    splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙
        structureFunctor (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f =
      structureFunctor p𝒰 p𝒳 p𝒵 z (f ⋙ g) :=
  rfl

/-- The comparison is strictly over `𝒰`: composing it with the two first projections gives the
first projection of `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳`. -/
@[simp] lemma splitSnd_comp_fst_comp_fst :
    splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙
        fst (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f ⋙
          fst p𝒰 p𝒴 p𝒵 z g =
      fst p𝒰 p𝒳 p𝒵 z (f ⋙ g) :=
  rfl

/-- The comparison composed with the first projection of the iterated product is the
1-morphism `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳 ⥤ 𝒰 ×_{z, 𝒵, g} 𝒴` induced by `f`. -/
@[simp] lemma splitSnd_comp_fst :
    splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙
        fst (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f =
      { obj := splitSndMiddle p𝒰 p𝒳 p𝒴 p𝒵 z f g hf
        map := splitSndMiddleMap p𝒰 p𝒳 p𝒴 p𝒵 z f g hf
        map_id := fun D => Hom.ext' rfl (f.map_id D.y)
        map_comp := fun ψ ψ' => Hom.ext' rfl (f.map_comp ψ.b ψ'.b) } :=
  rfl

/-- **The decomposition `𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳 ≃ (𝒰 ×_{z, 𝒵, g} 𝒴) ×_{π₂, 𝒴, f} 𝒳`.** The
comparison functor is an equivalence of categories. -/
theorem isEquivalence_splitSnd (hg : g ⋙ p𝒵 = p𝒴) :
    (splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf).IsEquivalence := by
  have hfaith : (splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf).Faithful := by
    constructor
    intro D D' φ φ' h
    exact Hom.ext' (by simpa using congrArg (fun t => t.a.a) h) (by simpa using congrArg Hom.b h)
  have hfull : (splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf).Full := by
    constructor
    intro D D' Θ
    have hb : Θ.a.b = f.map Θ.b :=
      (Category.comp_id _).symm.trans (Θ.w.trans (Category.id_comp _))
    refine ⟨⟨Θ.hbase, (Θ.a.a : D.x ⟶ D'.x), Θ.b,
      isHomLift_a Θ.a Θ.hbase Θ.ha, Θ.hb, ?_⟩, Hom.ext' (Hom.ext' rfl hb.symm) rfl⟩
    have hw := Θ.a.w
    rw [hb] at hw
    exact hw
  have hess : (splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf).EssSurj := by
    constructor
    intro Q
    obtain ⟨ι, hι⟩ : ∃ ι : Q.x.y ≅ f.obj Q.y, ι.hom = Q.iso.hom := ⟨Q.iso, rfl⟩
    have hQv : p𝒴.IsHomLift (𝟙 Q.base) ι.hom := hι ▸ Q.vertical
    have h1 : p𝒵.IsHomLift (𝟙 Q.base) Q.x.iso.hom := Q.hx ▸ Q.x.vertical
    have h2 : p𝒵.IsHomLift (𝟙 Q.base) (g.map ι.hom) :=
      Functor.isHomLift_map_of_comp_eq hg (𝟙 Q.base) ι.hom
    have hvert : p𝒵.IsHomLift (𝟙 Q.base) (Q.x.iso ≪≫ g.mapIso ι).hom := by
      simpa using IsHomLift.comp p𝒵 (𝟙 Q.base) (𝟙 Q.base) Q.x.iso.hom (g.map ι.hom)
    have hiU : p𝒰.IsHomLift (𝟙 Q.base) (Iso.refl Q.x.x).hom :=
      IsHomLift.id (Q.x.hx.trans Q.hx)
    have hjY : p𝒴.IsHomLift (𝟙 Q.base) ι.symm.hom :=
      IsHomLift.lift_id_inv p𝒴 Q.base ι
    have hwA : z.map (Iso.refl Q.x.x).hom ≫ Q.x.iso.hom =
        (Q.x.iso ≪≫ g.mapIso ι).hom ≫ g.map ι.symm.hom := by
      simp
    have hwR : ι.inv ≫ Q.iso.hom = 𝟙 (f.obj Q.y) ≫ f.map (𝟙 Q.y) := by
      rw [← hι]
      simp
    let D : TwoFibreProductOver p𝒰 p𝒳 p𝒵 z (f ⋙ g) :=
      { base := Q.base
        x := Q.x.x
        y := Q.y
        hx := Q.x.hx.trans Q.hx
        hy := Q.hy
        iso := Q.x.iso ≪≫ g.mapIso ι
        vertical := hvert }
    let A : splitSndMiddle p𝒰 p𝒳 p𝒴 p𝒵 z f g hf D ≅ Q.x :=
      isoMkVertical (U := Q.base) (Iso.refl Q.x.x) ι.symm hiU hjY hwA
    exact ⟨D, ⟨isoMkVertical (U := Q.base) A (Iso.refl Q.y)
      (structureFunctor_isHomLift A.hom (𝟙 Q.base) hiU) (IsHomLift.id Q.hy) hwR⟩⟩
  exact Functor.IsEquivalence.mk

include hf in
/-- **The decomposition as an equivalence over `𝒰`.** When the structure functors of the three
categories over `𝒞` are fibred in groupoids, the first projection of
`𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳` and the composite of the two first projections of
`(𝒰 ×_{z, 𝒵, g} 𝒴) ×_{π₂, 𝒴, f} 𝒳` are equivalent as categories over `𝒰`. -/
theorem nonempty_equivalenceOver_splitSnd (hg : g ⋙ p𝒵 = p𝒴)
    (h₁ : (fst p𝒰 p𝒳 p𝒵 z (f ⋙ g)).IsFiberedInGroupoids)
    (h₂ : (fst (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f ⋙
      fst p𝒰 p𝒴 p𝒵 z g).IsFiberedInGroupoids) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver (fst p𝒰 p𝒳 p𝒵 z (f ⋙ g))
      (fst (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f ⋙
        fst p𝒰 p𝒴 p𝒵 z g)) :=
  StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h₁ h₂ _
    (splitSnd_comp_fst_comp_fst p𝒰 p𝒳 p𝒴 p𝒵 z f g hf)
    (isEquivalence_splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf hg)

section BaseChange

variable {𝒯 : Type uT} [Category.{vT} 𝒯] (pT : 𝒯 ⥤ 𝒞)

include hf in
/-- **Base change of the decomposition.** Let `w : 𝒯 ⥤ 𝒰 ×_{z, 𝒵, g} 𝒴` be a 1-morphism over
`𝒞` into the intermediate 2-fibre product. Then the base change along `w` of
`𝒰 ×_{z, 𝒵, f ⋙ g} 𝒳`, taken along the 1-morphism that `f` induces into the intermediate
product, is the 2-fibre product of `𝒳` with `𝒯` over the point `w ⋙ π₂` of `𝒴`:

```text
𝒯 ×_{𝒰 ×_𝒵 𝒴} (𝒰 ×_𝒵 𝒳)  ≃  𝒯 ×_{w ⋙ π₂, 𝒴, f} 𝒳       over `𝒯`.
``` -/
theorem nonempty_equivalenceOver_baseChange_splitSnd (hg : g ⋙ p𝒵 = p𝒴)
    (w : 𝒯 ⥤ TwoFibreProductOver p𝒰 p𝒴 p𝒵 z g)
    (hw : w ⋙ structureFunctor p𝒰 p𝒴 p𝒵 z g = pT)
    (hpT : pT.IsFiberedInGroupoids)
    (hpL : (structureFunctor p𝒰 p𝒳 p𝒵 z (f ⋙ g)).IsFiberedInGroupoids)
    (hpR : (structureFunctor (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴
      (snd p𝒰 p𝒴 p𝒵 z g) f).IsFiberedInGroupoids)
    (h₁ : (fst pT (structureFunctor p𝒰 p𝒳 p𝒵 z (f ⋙ g)) (structureFunctor p𝒰 p𝒴 p𝒵 z g) w
      (splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙
        fst (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f)).IsFiberedInGroupoids)
    (h₂ : (fst pT (structureFunctor (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴
      (snd p𝒰 p𝒴 p𝒵 z g) f) (structureFunctor p𝒰 p𝒴 p𝒵 z g) w
      (fst (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴
        (snd p𝒰 p𝒴 p𝒵 z g) f)).IsFiberedInGroupoids) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (fst pT (structureFunctor p𝒰 p𝒳 p𝒵 z (f ⋙ g)) (structureFunctor p𝒰 p𝒴 p𝒵 z g) w
        (splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf ⋙
          fst (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f))
      (fst pT p𝒳 p𝒴 (w ⋙ snd p𝒰 p𝒴 p𝒵 z g) f)) := by
  have hKe : (splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf).IsEquivalence :=
    isEquivalence_splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf hg
  obtain ⟨e₁⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h₁ h₂
    (precomposeSnd (pT := pT) (pℬ := structureFunctor p𝒰 p𝒴 p𝒵 z g) w
      (fst (structureFunctor p𝒰 p𝒴 p𝒵 z g) p𝒳 p𝒴 (snd p𝒰 p𝒴 p𝒵 z g) f)
      (splitSnd p𝒰 p𝒳 p𝒴 p𝒵 z f g hf)
      (splitSnd_comp_structureFunctor p𝒰 p𝒳 p𝒴 p𝒵 z f g hf))
    (precomposeSnd_comp_fst _ _ _ _)
    (isEquivalence_precomposeSnd hpT hpL hpR
      (splitSnd_comp_structureFunctor p𝒰 p𝒳 p𝒴 p𝒵 z f g hf) fst_comp_eq)
  exact ⟨e₁.trans (cancelMiddleEquivalenceOver pT p𝒳 p𝒴
    (structureFunctor p𝒰 p𝒴 p𝒵 z g) w f (snd p𝒰 p𝒴 p𝒵 z g) hw snd_comp_eq)⟩

end BaseChange

end CategoryTheory.TwoFibreProductOver

end
