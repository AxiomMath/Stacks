module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre

/-!
# The fibre of the relative diagonal is the sheaf of vertical morphisms over the comparison

Fix a base category `𝒞`, let `p : X ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be categories over `𝒞` and let
`F : X ⥤ 𝒴` be a 1-morphism strictly over `𝒞`. Write `X ×_𝒴 X` for the 2-fibre product
`CategoryTheory.TwoFibreProductOver p p q F F` of Stacks 0040 and

`Δ_F : X ⟶ X ×_𝒴 X`

for its relative diagonal, `CategoryTheory.TwoFibreProductOver.diagonal`. For a category `𝒯`
over `𝒞` and a 1-morphism `Y : 𝒯 ⟶ X ×_𝒴 X` over `𝒞`, this file identifies the first
projection of the 2-fibre product

`𝒯 ×_{Y, X ×_𝒴 X, Δ_F} X ⟶ 𝒯`

with the category of elements of the presheaf on `𝒯` whose sections over `a` are the *vertical*
morphisms `m : Y₁ a ⟶ Y₂ a` of `X` satisfying `F m = α a`. Here `Y₁`, `Y₂` are the two
components of `Y` and `α a : F (Y₁ a) ≅ F (Y₂ a)` is the comparison isomorphism carried by the
object `Y a` of the 2-fibre product.

This is the displayed cartesian diagram in the proof of **Stacks 04XS**, labelled 04XT there:
writing `Isom(x, y)` for the presheaf of vertical morphisms of
`CategoryTheory.TwoFibreProductOver.DiagonalFibre`, which is the fibre of the *absolute*
diagonal, the presheaf of this file is the fibre of `Isom_X(Y₁, Y₂) ⟶ Isom_𝒴(F Y₁, F Y₂)` over
the section `α`. For `𝒯` the big fppf site over a scheme `T` and `Y` a `T`-valued point
`(x, x', α)` of `X ×_𝒴 X`, that is exactly the statement that
`X ×_{X ×_𝒴 X, (x, x', α)} T` is the fibre product
`Isom_X(x, x') ×_{Isom_𝒴(F x, F x'), α} T` of sheaves over `T`.

The absolute case is `CategoryTheory.TwoFibreProductOver.DiagonalFibre`, where `𝒴` is `𝒞` and
`F` is `p`; there the comparison isomorphism of a point is forced to be an `eqToHom`, so the
condition `F m = α a` is vacuous and the presheaf is the full presheaf of vertical morphisms.
The two files are therefore not instances of one another: the relative condition is extra data
on a section, and it is what makes the restriction maps need a hypothesis on `q`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.RelVertHom`: the type of vertical
  morphisms `Y₁ a ⟶ Y₂ a` whose image under `F` is the comparison isomorphism of `Y` at `a`.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.RelVertHom.restrict` and
  `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.RelVertHom.presheaf`: their
  restriction along a morphism of `𝒯`, and the resulting presheaf.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.objOf`: the direction of the
  identification on objects that attaches an object of the 2-fibre product to a vertical
  morphism. The other direction is `CategoryTheory.TwoFibreProductOver.sectOf`, which is
  already stated in this generality.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.pushforward` and
  `.presheafMap`: the image under `F` of a vertical morphism, and the resulting morphism of
  presheaves `Isom(Y₁, Y₂) ⟶ Isom(F Y₁, F Y₂)`.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.alphaSection`: the section of
  `Isom(F Y₁, F Y₂)` given by the comparison isomorphism of `Y`.

## Main results

* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.map_sectOf`: the section of an
  object of the 2-fibre product satisfies the fibre condition. This is the one computation that
  has no counterpart in the absolute case.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.map_restrict`: the fibre condition
  is preserved by restriction, so the presheaf exists.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.equivalenceOver`: the first
  projection of `𝒯 ×_{Y, X ×_𝒴 X, Δ_F} X` is equivalent over `𝒯` to the category of elements of
  `relVertHomPresheaf`. This is **Stacks 04XT**, the cartesian square in the proof of Stacks
  04XS.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.nonempty_equivalenceOver_fst_iff`:
  that equivalence read as a comparison of presheaves, which is the form a consumer of
  representability by algebraic spaces applies it in.
* `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.pushforward_restrict` and
  `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.restrict_alphaSection`: the two
  facts that make the other two sides of that square morphisms of presheaves.
* `CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.pushforward_eq_alphaSection_iff`:
  `relVertHomPresheaf` is the fibre of `presheafMap` over `alphaSection`.

## Implementation notes

An object of `𝒯 ×_{Y, X ×_𝒴 X, Δ_F} X` over `a` is a triple `(z, α', β)` of an object `z` of
`X` and two vertical isomorphisms `α' : Y₁ a ≅ z`, `β : Y₂ a ≅ z`, and `α' ∘ β⁻¹` is the
vertical morphism `Y₁ a ⟶ Y₂ a` it names; this is
`CategoryTheory.TwoFibreProductOver.sectOf`, the same declaration the absolute case uses, since
neither it nor the naturality of the comparison isomorphism
(`CategoryTheory.TwoFibreProductOver.sectOf_naturality` and the three component lemmas it is
built from) sees anything of `q` and `F` beyond `Δ_F` sending `f` to `(f, f)`. What is new
is that the comparison square of the ambient 2-fibre product now says `F (α' ∘ β⁻¹) = α a`
rather than being vacuous, which is `map_sectOf`; conversely `objOf` can only build an object
out of a vertical morphism that satisfies that identity, and its two comparison squares are
exactly the identity and its inverse.

That restriction preserves the condition is the one place a hypothesis on `q` is needed. The
restriction of `m` along `h : a' ⟶ a` is the unique vertical fill-in against the cartesian
morphism `Y₂ h`; applying `F` and using the naturality square of `α` shows that `F` of that
fill-in and `α a'` have the same composite with `F (Y₂ h)`, and `F (Y₂ h)` is strongly cartesian
in `𝒴` because `q` is fibred in groupoids, so the two agree. `p` is assumed fibred in groupoids
for the same reason as in the absolute case, namely so that the fill-in exists at all and so
that a vertical morphism is invertible.

The three general lemmas `CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.map_eq`,
`.isIso` and `.map_inv_eq` are added to the `VertHom` namespace here. They are the forms of
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.map_sect_eq`, `.isIso_vertHom` and
`.map_inv_sect_eq` with the two components left arbitrary rather than fixed to the components of
a point of the absolute product, which is what this file needs; the specialised versions are
their instances.

The four total categories have independent object and morphism universes, as the predicates of
Stacks 02ZW and 04SV require.

## References

* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ t

namespace CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {Y₁ Y₂ : 𝒯 ⥤ X}
variable {𝒴 : Type u₄} [Category.{v₄} 𝒴] {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}

/-- A morphism lying over an identity has, as its image, the identification of its endpoints. -/
private lemma map_eq_eqToHom_of_isHomLift_id {E : Type*} [Category E] {R : 𝒞}
    {x y : E} (P : E ⥤ 𝒞) (f : x ⟶ y) (hx : P.obj x = R) (hy : P.obj y = R) [P.IsHomLift (𝟙 R) f] :
    P.map f = eqToHom hx ≫ eqToHom hy.symm := by
  rw [IsHomLift.fac' P (𝟙 R) f]
  simp

/-- A vertical morphism between the values at `a` of two functors over `𝒞` has, as its image
under `p`, the canonical identification of the two images of `a`. -/
lemma map_eq (h₁ : Y₁ ⋙ p = p𝒯) (h₂ : Y₂ ⋙ p = p𝒯) {a : 𝒯} (m : VertHom p p𝒯 Y₁ Y₂ a) :
    p.map m.1 = eqToHom (Functor.congr_obj h₁ a) ≫ eqToHom (Functor.congr_obj h₂ a).symm := by
  have := m.2
  exact map_eq_eqToHom_of_isHomLift_id p m.1 (Functor.congr_obj h₁ a) (Functor.congr_obj h₂ a)

/-- A vertical morphism is invertible when `p` is fibred in groupoids: it lies over an
identity, hence over an isomorphism, and a strongly cartesian morphism over an isomorphism is
an isomorphism. -/
lemma isIso (hp : p.IsFiberedInGroupoids) {a : 𝒯} (m : VertHom p p𝒯 Y₁ Y₂ a) : IsIso m.1 := by
  have hm := m.2
  have := hp.isStronglyCartesian_homLift (𝟙 (p𝒯.obj a)) m.1
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p𝒯.obj a)) m.1

/-- The image under `p` of the inverse of a vertical morphism. -/
lemma map_inv_eq (hp : p.IsFiberedInGroupoids) (h₁ : Y₁ ⋙ p = p𝒯) (h₂ : Y₂ ⋙ p = p𝒯)
    {a : 𝒯} (m : VertHom p p𝒯 Y₁ Y₂ a) :
    letI := isIso hp m
    p.map (CategoryTheory.inv m.1) = eqToHom (Functor.congr_obj h₂ a) ≫
      eqToHom (Functor.congr_obj h₁ a).symm := by
  have := isIso hp m
  simp [p.map_inv, map_eq h₁ h₂ m]

/-- Composing a functor over `𝒞` with a 1-morphism over `𝒞` again gives a functor over `𝒞`. -/
lemma comp_comp_eq (hF : F ⋙ q = p) (h₁ : Y₁ ⋙ p = p𝒯) : (Y₁ ⋙ F) ⋙ q = p𝒯 := by
  rwa [Functor.assoc, hF]

/-- The image under `F` of a vertical morphism `Y₁ a ⟶ Y₂ a`. -/
def pushforward (hF : F ⋙ q = p) {a : 𝒯} (m : VertHom p p𝒯 Y₁ Y₂ a) :
    VertHom q p𝒯 (Y₁ ⋙ F) (Y₂ ⋙ F) a :=
  ⟨F.map m.1, by
    have := m.2
    exact Functor.isHomLift_map_of_comp_eq hF (𝟙 (p𝒯.obj a)) m.1⟩

/-- The underlying morphism of `pushforward`. -/
@[simp] lemma pushforward_coe (hF : F ⋙ q = p) {a : 𝒯} (m : VertHom p p𝒯 Y₁ Y₂ a) :
    (pushforward hF m).1 = F.map m.1 := rfl

/-- **Pushing forward along `F` commutes with restriction.** Both sides are vertical fill-ins of
`F (Y₁ h) ≫ F m` against `F (Y₂ h)`, which is strongly cartesian in `𝒴` because `q` is fibred
in groupoids, so they agree. -/
lemma pushforward_restrict (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (h₁ : Y₁ ⋙ p = p𝒯) (h₂ : Y₂ ⋙ p = p𝒯) (hF : F ⋙ q = p)
    (h₁' : (Y₁ ⋙ F) ⋙ q = p𝒯) (h₂' : (Y₂ ⋙ F) ⋙ q = p𝒯)
    {a' a : 𝒯} (h : a' ⟶ a) (m : VertHom p p𝒯 Y₁ Y₂ a) :
    pushforward hF (restrict hp h₁ h₂ h m) = restrict hq h₁' h₂' h (pushforward hF m) :=
  restrict_uniq hq h₁' h₂' h (pushforward hF m) (pushforward hF (restrict hp h₁ h₂ h m)) (by
    simp only [pushforward_coe, Functor.comp_map, ← Functor.map_comp]
    rw [restrict_fac hp h₁ h₂ h m])

section PresheafMap

variable {𝒴' : Type u₄} [Category.{v₃} 𝒴'] {q' : 𝒴' ⥤ 𝒞} {F' : X ⥤ 𝒴'}

/-- The morphism of presheaves `Isom(Y₁, Y₂) ⟶ Isom(F Y₁, F Y₂)` given by applying `F`.

Stated for a target whose morphism universe is that of the source, which is what a
`CategoryTheory.CatFiberedInGroupoids` at one fixed pair of universes supplies: a morphism of
presheaves needs both presheaves to take values in one `Type`, while
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.pushforward` itself is universe
polymorphic. -/
noncomputable def presheafMap (hq : q'.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (h₁ : Y₁ ⋙ p = p𝒯) (h₂ : Y₂ ⋙ p = p𝒯) (hF : F' ⋙ q' = p)
    (h₁' : (Y₁ ⋙ F') ⋙ q' = p𝒯) (h₂' : (Y₂ ⋙ F') ⋙ q' = p𝒯) :
    presheaf hp h₁ h₂ ⟶ presheaf hq h₁' h₂' where
  app _ := ↾fun m => pushforward hF m
  naturality _ _ h := by
    ext m
    exact pushforward_restrict hq hp h₁ h₂ hF h₁' h₂' h.unop m

/-- The components of `presheafMap` are `pushforward`. -/
@[simp] lemma presheafMap_app (hq : q'.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (h₁ : Y₁ ⋙ p = p𝒯) (h₂ : Y₂ ⋙ p = p𝒯) (hF : F' ⋙ q' = p)
    (h₁' : (Y₁ ⋙ F') ⋙ q' = p𝒯) (h₂' : (Y₂ ⋙ F') ⋙ q' = p𝒯) (a : 𝒯ᵒᵖ)
    (m : VertHom p p𝒯 Y₁ Y₂ a.unop) :
    (presheafMap hq hp h₁ h₂ hF h₁' h₂').app a m = pushforward hF m := rfl

end PresheafMap

end CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom

namespace CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

open CategoryTheory.TwoFibreProductOver.DiagonalFibre

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X : Type u₃} [Category.{v₃} X]
  {𝒯 : Type u₂} [Category.{v₂} 𝒯] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
variable {p : X ⥤ 𝒞} {p𝒯 : 𝒯 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : X ⥤ 𝒴}

attribute [local implicit_reducible] _root_.CategoryTheory.TwoFibreProductOver.fst
  _root_.CategoryTheory.TwoFibreProductOver.snd
  _root_.CategoryTheory.TwoFibreProductOver.diagonal

/-- The 2-fibre product `X ×_{F, 𝒴, F} X` over `𝒞`. -/
abbrev RelProd (p : X ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : X ⥤ 𝒴) := TwoFibreProductOver p p q F F

/-- The structure functor of `X ×_{F, 𝒴, F} X`. -/
abbrev RelProdP (p : X ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : X ⥤ 𝒴) : RelProd p q F ⥤ 𝒞 :=
  structureFunctor p p q F F

/-- The relative diagonal `Δ_F : X ⟶ X ×_{F, 𝒴, F} X`. -/
abbrev RelDiag (hF : F ⋙ q = p) : X ⥤ RelProd p q F := diagonal hF

/-- The first component of a point of `X ×_𝒴 X`. -/
abbrev Y₁' (Y : 𝒯 ⥤ RelProd p q F) : 𝒯 ⥤ X := Y ⋙ fst p p q F F

/-- The second component of a point of `X ×_𝒴 X`. -/
abbrev Y₂' (Y : 𝒯 ⥤ RelProd p q F) : 𝒯 ⥤ X := Y ⋙ snd p p q F F

variable {Y : 𝒯 ⥤ RelProd p q F} {hF : F ⋙ q = p}

/-- The first component of a point of `X ×_𝒴 X` over `𝒯` is a functor over `𝒞`. -/
lemma h1' (hY : Y ⋙ RelProdP p q F = p𝒯) : Y₁' Y ⋙ p = p𝒯 := by
  rwa [Functor.assoc, fst_comp_eq]

/-- The second component of a point of `X ×_𝒴 X` over `𝒯` is a functor over `𝒞`. -/
lemma h2' (hY : Y ⋙ RelProdP p q F = p𝒯) : Y₂' Y ⋙ p = p𝒯 := by
  rwa [Functor.assoc, snd_comp_eq]

/-- The section of an object of the 2-fibre product is vertical: the two base morphisms of the
comparison isomorphism compose to an identity. -/
lemma isHomLift_sectOf (hY : Y ⋙ RelProdP p q F = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF)) :
    p.IsHomLift (𝟙 (p𝒯.obj A.x)) (sectOf A) := by
  have hA := A.iso.hom.ha
  have hB := A.iso.inv.hb
  have hcomp : p.IsHomLift (A.iso.hom.hbase ≫ A.iso.inv.hbase)
      (A.iso.hom.a ≫ A.iso.inv.b) := inferInstance
  have hid : A.iso.hom.hbase ≫ A.iso.inv.hbase = 𝟙 (Y.obj A.x).base := by
    have h := congrArg Hom.hbase A.iso.hom_inv_id
    rwa [comp_hbase, id_hbase] at h
  rw [hid] at hcomp
  have hbase : (Y.obj A.x).base = p𝒯.obj A.x := Functor.congr_obj hY A.x
  rwa [hbase] at hcomp

/-- **The fibre condition.** The image under `F` of the section of an object of
`𝒯 ×_{Y, X ×_𝒴 X, Δ_F} X` is the comparison isomorphism of `Y` at that object. -/
lemma map_sectOf (A : TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF)) :
    F.map (sectOf A) = (Y.obj A.x).iso.hom := by
  have hw := A.iso.hom.w
  rw [show ((RelDiag hF).obj A.y).iso.hom = 𝟙 _ from rfl, Category.comp_id] at hw
  have hid : F.map (A.iso.hom.b ≫ A.iso.inv.b) = 𝟙 _ := by
    rw [iso_hom_b_comp_inv_b A]
    exact F.map_id _
  rw [sectOf_def, F.map_comp, hw, Category.assoc, ← F.map_comp, hid, Category.comp_id]

section Rel

/-- Naturality of the comparison isomorphism of a point of `X ×_𝒴 X`. -/
lemma iso_naturality {a' a : 𝒯} (h : a' ⟶ a) :
    F.map ((Y₁' Y).map h) ≫ (Y.obj a).iso.hom
      = (Y.obj a').iso.hom ≫ F.map ((Y₂' Y).map h) :=
  (Y.map h).w

/-- The image under `F` of a component of `Y` applied to `h` lies over `p𝒯 h`. -/
private lemma isHomLift_map_q_aux {Z : 𝒯 ⥤ X} (hZ : Z ⋙ p = p𝒯) (hF : F ⋙ q = p)
    {a' a : 𝒯} (h : a' ⟶ a) : q.IsHomLift (p𝒯.map h) (F.map (Z.map h)) := by
  have := VertHom.isHomLift_map (p := p) hZ (Y₂ := Z) h
  exact Functor.isHomLift_map_of_comp_eq hF (p𝒯.map h) (Z.map h)

/-- The image under `F` of the second component of `Y` applied to `h` lies over `p𝒯 h`. -/
lemma isHomLift_map_q (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p)
    {a' a : 𝒯} (h : a' ⟶ a) :
    q.IsHomLift (p𝒯.map h) (F.map ((Y₂' Y).map h)) :=
  isHomLift_map_q_aux (h2' hY) hF h

/-- The comparison isomorphism of a point of `X ×_𝒴 X` over `𝒯` is vertical over the base
object of `𝒯` it lies over. -/
lemma isHomLift_vertical_iso (hY : Y ⋙ RelProdP p q F = p𝒯) (a : 𝒯) :
    q.IsHomLift (𝟙 (p𝒯.obj a)) (Y.obj a).iso.hom := by
  have hv := (Y.obj a).vertical
  rwa [show (Y.obj a).base = p𝒯.obj a from Functor.congr_obj hY a] at hv

/-- The composite of the image under `F` of the first component of `Y` applied to `h` with the
comparison isomorphism lies over `p𝒯 h`. -/
lemma isHomLift_comp_q (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p)
    {a' a : 𝒯} (h : a' ⟶ a) :
    q.IsHomLift (p𝒯.map h) (F.map ((Y₁' Y).map h) ≫ (Y.obj a).iso.hom) := by
  have h1 := isHomLift_map_q_aux (h1' hY) hF h
  have h2 := isHomLift_vertical_iso hY a
  have : q.IsHomLift (p𝒯.map h ≫ 𝟙 (p𝒯.obj a))
      (F.map ((Y₁' Y).map h) ≫ (Y.obj a).iso.hom) := inferInstance
  rwa [Category.comp_id] at this

/-- **Restriction preserves the fibre condition.** If a vertical morphism `m : Y₁ a ⟶ Y₂ a` has
`F m` equal to the comparison isomorphism of `Y` at `a`, so does its restriction along
`h : a' ⟶ a`. -/
lemma map_restrict (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p)
    {a' a : 𝒯} (h : a' ⟶ a) (m : VertHom p p𝒯 (Y₁' Y) (Y₂' Y) a)
    (hm : F.map m.1 = (Y.obj a).iso.hom) :
    F.map (VertHom.restrict hp (h1' hY) (h2' hY) h m).1 = (Y.obj a').iso.hom := by
  set r := VertHom.restrict hp (h1' hY) (h2' hY) h m
  have hlift := isHomLift_map_q hY hF h
  have _hsc : q.IsStronglyCartesian (p𝒯.map h) (F.map ((Y₂' Y).map h)) :=
    hq.isStronglyCartesian_homLift _ _
  have hφ' := isHomLift_comp_q hY hF h
  have hr1 : q.IsHomLift (𝟙 (p𝒯.obj a')) (F.map r.1) := (VertHom.pushforward hF r).2
  have hr2 := isHomLift_vertical_iso hY a'
  have keyr : F.map r.1 ≫ F.map ((Y₂' Y).map h)
      = F.map ((Y₁' Y).map h) ≫ (Y.obj a).iso.hom := by
    rw [← F.map_comp, VertHom.restrict_fac hp (h1' hY) (h2' hY) h m, F.map_comp, hm]
  have key := Functor.IsStronglyCartesian.map_uniq q (p𝒯.map h) (F.map ((Y₂' Y).map h))
    (Category.id_comp _).symm (F.map ((Y₁' Y).map h) ≫ (Y.obj a).iso.hom)
  exact (key (F.map r.1) keyr).trans (key _ (iso_naturality h).symm).symm

end Rel

/-- The type of vertical morphisms `Y₁ a ⟶ Y₂ a` of `X` whose image under `F` is the comparison
isomorphism of `Y` at `a`. -/
def RelVertHom (p𝒯 : 𝒯 ⥤ 𝒞) (Y : 𝒯 ⥤ RelProd p q F) (a : 𝒯) : Type v₃ :=
  {m : VertHom p p𝒯 (Y₁' Y) (Y₂' Y) a // F.map m.1 = (Y.obj a).iso.hom}

namespace RelVertHom

/-- An element of `RelVertHom` is determined by the underlying morphism of `X`. -/
@[ext] lemma ext {a : 𝒯} {m n : RelVertHom p𝒯 Y a} (h : m.1.1 = n.1.1) : m = n :=
  Subtype.ext (Subtype.ext h)

/-- Restriction of an element of `RelVertHom` along `h : a' ⟶ a`. -/
noncomputable def restrict (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) {a' a : 𝒯} (h : a' ⟶ a)
    (m : RelVertHom p𝒯 Y a) : RelVertHom p𝒯 Y a' :=
  ⟨VertHom.restrict hp (h1' hY) (h2' hY) h m.1, map_restrict hq hp hY hF h m.1 m.2⟩

/-- Restriction is the unique vertical fill-in: an element of `RelVertHom` over `a'` whose
composite with `Y₂ h` is `Y₁ h` followed by a given element over `a` is its restriction. -/
lemma restrict_uniq (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) {a' a : 𝒯} (h : a' ⟶ a)
    (m : RelVertHom p𝒯 Y a) (n : RelVertHom p𝒯 Y a')
    (hn : n.1.1 ≫ (Y₂' Y).map h = (Y₁' Y).map h ≫ m.1.1) :
    n = restrict hq hp hY hF h m :=
  Subtype.ext (VertHom.restrict_uniq hp (h1' hY) (h2' hY) h m.1 n.1 hn)

/-- Restriction along an identity is the identity. -/
lemma restrict_id (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) {a : 𝒯} (m : RelVertHom p𝒯 Y a) :
    restrict hq hp hY hF (𝟙 a) m = m :=
  Subtype.ext (VertHom.restrict_id hp (h1' hY) (h2' hY) m.1)

/-- Restriction along a composite is the composite of restrictions. -/
lemma restrict_comp (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) {a'' a' a : 𝒯} (g : a'' ⟶ a') (f : a' ⟶ a)
    (m : RelVertHom p𝒯 Y a) :
    restrict hq hp hY hF (g ≫ f) m
      = restrict hq hp hY hF g (restrict hq hp hY hF f m) :=
  Subtype.ext (VertHom.restrict_comp hp (h1' hY) (h2' hY) g f m.1)

/-- The presheaf on `𝒯` whose sections over `a` are the vertical morphisms `Y₁ a ⟶ Y₂ a` whose
image under `F` is the comparison isomorphism of `Y` at `a`. -/
noncomputable def presheaf (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) : 𝒯ᵒᵖ ⥤ Type v₃ where
  obj a := RelVertHom p𝒯 Y a.unop
  map h := ↾fun m => restrict hq hp hY hF h.unop m
  map_id _ := by
    ext m
    exact congrArg Subtype.val (congrArg Subtype.val (restrict_id hq hp hY hF m))
  map_comp f g := by
    ext m
    exact congrArg Subtype.val
      (congrArg Subtype.val (restrict_comp hq hp hY hF g.unop f.unop m))

/-- The restriction maps of `presheaf` are `restrict`. -/
@[simp] lemma presheaf_map (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) {a' a : 𝒯} (h : a' ⟶ a)
    (m : RelVertHom p𝒯 Y a) :
    (presheaf hq hp hY hF).map h.op m = restrict hq hp hY hF h m := rfl

end RelVertHom


section Obj

/-- A point of `X ×_𝒴 X` over `𝒯` sends `a` to an object over `p𝒯 a`. -/
lemma base_eq_of_obj (hY : Y ⋙ RelProdP p q F = p𝒯) (a : 𝒯) :
    (Y.obj a).base = p𝒯.obj a := Functor.congr_obj hY a

/-- The object of `𝒯 ×_{Y, X ×_𝒴 X, Δ_F} X` attached to a vertical morphism `m : Y₁ a ⟶ Y₂ a`
with `F m` the comparison isomorphism of `Y` at `a`. -/
noncomputable def objOf (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (hF : F ⋙ q = p) (a : 𝒯) (m : RelVertHom p𝒯 Y a) :
    TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF) where
  base := p𝒯.obj a
  x := a
  y := (Y₂' Y).obj a
  hx := rfl
  hy := Functor.congr_obj (h2' hY) a
  iso :=
    have := VertHom.isIso hp m.1
    { hom :=
        { hbase := eqToHom ((base_eq_of_obj hY a).trans
            (Functor.congr_obj (h2' hY) a).symm)
          a := m.1.1
          b := 𝟙 _
          ha := by
            refine IsHomLift.of_fac' p _ _ (Y.obj a).hx rfl ?_
            rw [VertHom.map_eq (h1' hY) (h2' hY) m.1]
            simp
          hb := by
            refine IsHomLift.of_fac' p _ _ (Y.obj a).hy rfl ?_
            simp
          w := by
            rw [show ((RelDiag hF).obj ((Y₂' Y).obj a)).iso.hom = 𝟙 _ from rfl, m.2]
            simp }
      inv :=
        { hbase := eqToHom (((base_eq_of_obj hY a).trans
            (Functor.congr_obj (h2' hY) a).symm).symm)
          a := CategoryTheory.inv m.1.1
          b := 𝟙 _
          ha := by
            refine IsHomLift.of_fac' p _ _ rfl (Y.obj a).hx ?_
            rw [VertHom.map_inv_eq hp (h1' hY) (h2' hY) m.1]
            simp
          hb := by
            refine IsHomLift.of_fac' p _ _ rfl (Y.obj a).hy ?_
            simp
          w := by
            have hmm : F.map m.1.1 = (Y.obj a).iso.hom := m.2
            have hinv : F.map (CategoryTheory.inv m.1.1) ≫ F.map m.1.1
                = 𝟙 (F.obj ((Y₂' Y).obj a)) := by
              rw [← F.map_comp, IsIso.inv_hom_id]
              exact F.map_id _
            rw [hmm] at hinv
            rw [show ((RelDiag hF).obj ((Y₂' Y).obj a)).iso.hom = 𝟙 _ from rfl, hinv]
            simp }
      hom_inv_id := Hom.ext' (by simp) (by simp)
      inv_hom_id := Hom.ext' (by simp) (by simp) }
  vertical := by
    refine IsHomLift.of_fac' (RelProdP p q F) _ _ (base_eq_of_obj hY a)
      (Functor.congr_obj (h2' hY) a) ?_
    simp only [Category.id_comp, structureFunctor_map]
    exact (eqToHom_trans _ _).symm

/-- The base object of `objOf`. -/
@[simp] lemma objOf_base (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (hF : F ⋙ q = p) (a : 𝒯) (m : RelVertHom p𝒯 Y a) :
    (objOf hp hY hF a m).base = p𝒯.obj a := rfl

/-- The `𝒯`-component of `objOf`. -/
@[simp] lemma objOf_x (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (hF : F ⋙ q = p) (a : 𝒯) (m : RelVertHom p𝒯 Y a) : (objOf hp hY hF a m).x = a := rfl

/-- The `X`-component of `objOf`. -/
@[simp] lemma objOf_y (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (hF : F ⋙ q = p) (a : 𝒯) (m : RelVertHom p𝒯 Y a) :
    (objOf hp hY hF a m).y = (Y₂' Y).obj a := rfl

/-- The first component of the comparison isomorphism of `objOf`. -/
@[simp] lemma objOf_iso_hom_a (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (hF : F ⋙ q = p) (a : 𝒯) (m : RelVertHom p𝒯 Y a) :
    (objOf hp hY hF a m).iso.hom.a = m.1.1 := rfl

/-- The second component of the comparison isomorphism of `objOf`. -/
@[simp] lemma objOf_iso_hom_b (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (hF : F ⋙ q = p) (a : 𝒯) (m : RelVertHom p𝒯 Y a) :
    (objOf hp hY hF a m).iso.hom.b = 𝟙 ((Y₂' Y).obj a) := rfl

/-- The second component of the inverse comparison isomorphism of `objOf`. -/
@[simp] lemma objOf_iso_inv_b (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (hF : F ⋙ q = p) (a : 𝒯) (m : RelVertHom p𝒯 Y a) :
    (objOf hp hY hF a m).iso.inv.b = 𝟙 ((Y₂' Y).obj a) := rfl

/-- The section of the object attached to a vertical morphism is that morphism. -/
@[simp] lemma sectOf_objOf (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯)
    (hF : F ⋙ q = p) (a : 𝒯) (m : RelVertHom p𝒯 Y a) :
    sectOf (objOf hp hY hF a m) = m.1.1 := by
  rw [sectOf_def]
  exact Category.comp_id _

end Obj

section BaseLemmas

/-- The base object of `Y A.x` is the base object of `A`. -/
lemma baseEq (hY : Y ⋙ RelProdP p q F = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF)) :
    (Y.obj A.x).base = A.base := (base_eq_of_obj hY A.x).trans A.hx

/-- The inverse comparison isomorphism of an object of the 2-fibre product is vertical. -/
lemma vertical_inv (A : TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF)) :
    (RelProdP p q F).IsHomLift (𝟙 A.base) A.iso.inv := by
  have hv := A.vertical
  have h := IsHomLift.lift_id_inv_isIso (RelProdP p q F) A.base A.iso.hom
  rwa [show CategoryTheory.inv A.iso.hom = A.iso.inv from by simp] at h

/-- The base morphism of the comparison isomorphism is the canonical identification. -/
lemma hbase_hom_eq (hY : Y ⋙ RelProdP p q F = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF)) :
    A.iso.hom.hbase = eqToHom (baseEq hY A) ≫ eqToHom A.hy.symm := by
  have := A.vertical
  exact VertHom.map_eq_eqToHom_of_isHomLift_id (RelProdP p q F) A.iso.hom (baseEq hY A) A.hy

/-- The base morphism of the inverse comparison isomorphism is the canonical identification. -/
lemma hbase_inv_eq (hY : Y ⋙ RelProdP p q F = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF)) :
    A.iso.inv.hbase = eqToHom A.hy ≫ eqToHom (baseEq hY A).symm := by
  have := vertical_inv A
  exact VertHom.map_eq_eqToHom_of_isHomLift_id (RelProdP p q F) A.iso.inv A.hy (baseEq hY A)

/-- The second component of the inverse comparison isomorphism is vertical. -/
lemma isHomLift_b_inv (hY : Y ⋙ RelProdP p q F = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF)) :
    p.IsHomLift (𝟙 (p.obj A.y)) A.iso.inv.b := by
  have hb := A.iso.inv.hb
  refine IsHomLift.of_fac' p _ _ rfl
    (((Y.obj A.x).hy.trans (baseEq hY A)).trans A.hy.symm) ?_
  rw [IsHomLift.fac' p A.iso.inv.hbase A.iso.inv.b]
  simp only [hbase_inv_eq hY A, Category.id_comp, eqToHom_trans]

/-- The second component of the comparison isomorphism is vertical. -/
lemma isHomLift_b_hom (hY : Y ⋙ RelProdP p q F = p𝒯)
    (A : TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF)) :
    p.IsHomLift (𝟙 (p.obj ((Y.obj A.x).y))) A.iso.hom.b := by
  have hb := A.iso.hom.hb
  refine IsHomLift.of_fac' p _ _ rfl
    (A.hy.trans ((baseEq hY A).symm.trans ((Y.obj A.x).hy).symm)) ?_
  rw [IsHomLift.fac' p A.iso.hom.hbase A.iso.hom.b]
  simp only [hbase_hom_eq hY A, Category.id_comp, eqToHom_trans]

end BaseLemmas


section Equivalence

/-- The presheaf on `𝒯` of vertical morphisms `Y₁ ⟶ Y₂` lying over the comparison isomorphism
of `Y`. -/
noncomputable abbrev relVertHomPresheaf (hq : q.IsFiberedInGroupoids)
    (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    𝒯ᵒᵖ ⥤ Type v₃ :=
  RelVertHom.presheaf hq hp hY hF

/-- The comparison functor from `𝒯 ×_{Y, X ×_𝒴 X, Δ_F} X` to the category of elements of
`relVertHomPresheaf`. -/
noncomputable def toElements (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF) ⥤
      (presheafOfCategories (relVertHomPresheaf hq hp hY hF ⋙ typeToCat)).obj where
  obj A := ⟨A.x, Discrete.mk ⟨⟨sectOf A, isHomLift_sectOf hY A⟩, map_sectOf A⟩⟩
  map {A B} u := ⟨u.a, Discrete.eqToHom
    (RelVertHom.restrict_uniq hq hp hY hF u.a
      ⟨⟨sectOf B, isHomLift_sectOf hY B⟩, map_sectOf B⟩
      ⟨⟨sectOf A, isHomLift_sectOf hY A⟩, map_sectOf A⟩ (sectOf_naturality u))⟩
  map_id _ := PresheafOfCategories.elements_hom_ext _ _ rfl
  map_comp _ _ := PresheafOfCategories.elements_hom_ext _ _ rfl

/-- The comparison functor back from the category of elements. -/
noncomputable def ofElements (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    (presheafOfCategories (relVertHomPresheaf hq hp hY hF ⋙ typeToCat)).obj ⥤
      TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF) where
  obj P := objOf hp hY hF P.base P.fiber.as
  map {P Q} u :=
    { hbase := p𝒯.map u.base
      a := u.base
      b := (Y₂' Y).map u.base
      ha := IsHomLift.map p𝒯 u.base
      hb := VertHom.isHomLift_map (p := p) (h2' hY) (Y₂ := Y₂' Y) u.base
      w := by
        refine Hom.ext' ?_ ?_
        · have hfib : P.fiber.as
              = RelVertHom.restrict hq hp hY hF u.base Q.fiber.as :=
            Discrete.eq_of_hom u.fiber
          have hfac := VertHom.restrict_fac hp (h1' hY) (h2' hY) u.base Q.fiber.as.1
          simp only [comp_a]
          rw [hfib]
          exact hfac.symm
        · simp only [comp_b]
          exact (Category.comp_id _).trans (Category.id_comp _).symm }
  map_id P := Hom.ext' rfl (by
    change (Y₂' Y).map (𝟙 P.base) = _
    exact Functor.map_id _ _)
  map_comp u v := Hom.ext' rfl (by
    change (Y₂' Y).map (u.base ≫ v.base) = _
    exact Functor.map_comp _ _ _)

/-- The unit of the equivalence. -/
noncomputable def unitIso (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    𝟭 (TwoFibreProductOver p𝒯 p (RelProdP p q F) Y (RelDiag hF)) ≅
      toElements hq hp hY hF ⋙ ofElements hq hp hY hF :=
  NatIso.ofComponents
    (fun A =>
      { hom :=
          { hbase := eqToHom A.hx.symm
            a := 𝟙 A.x
            b := A.iso.inv.b
            ha := DiagonalFibre.isHomLift_eqToHom_of_id p𝒯 (𝟙 A.x) A.hx rfl A.hx.symm
              (IsHomLift.id rfl)
            hb := DiagonalFibre.isHomLift_eqToHom_of_id p A.iso.inv.b A.hy
              (Functor.congr_obj (h2' hY) A.x) A.hx.symm (isHomLift_b_inv hY A)
            w := by
              refine Hom.ext' ?_ ?_
              · change (Y.map (𝟙 A.x)).a ≫ sectOf A = A.iso.hom.a ≫ A.iso.inv.b
                rw [Functor.map_id, id_a, Category.id_comp, sectOf_def]
              · change (Y.map (𝟙 A.x)).b ≫ 𝟙 ((Y₂' Y).obj A.x) = A.iso.hom.b ≫ A.iso.inv.b
                rw [Functor.map_id, id_b, Category.id_comp, iso_hom_b_comp_inv_b A] }
        inv :=
          { hbase := eqToHom A.hx
            a := 𝟙 A.x
            b := A.iso.hom.b
            ha := DiagonalFibre.isHomLift_eqToHom_of_id p𝒯 (𝟙 A.x) rfl A.hx A.hx
              (IsHomLift.id rfl)
            hb := DiagonalFibre.isHomLift_eqToHom_of_id p A.iso.hom.b
              (Functor.congr_obj (h2' hY) A.x) A.hy A.hx (isHomLift_b_hom hY A)
            w := by
              refine Hom.ext' ?_ ?_
              · change (Y.map (𝟙 A.x)).a ≫ A.iso.hom.a = sectOf A ≫ A.iso.hom.b
                rw [Functor.map_id, id_a, Category.id_comp, sectOf_def, Category.assoc,
                  iso_inv_b_comp_hom_b A]
                exact (Category.comp_id _).symm
              · change (Y.map (𝟙 A.x)).b ≫ A.iso.hom.b
                  = 𝟙 ((Y₂' Y).obj A.x) ≫ A.iso.hom.b
                rw [Functor.map_id, id_b]
                rfl }
        hom_inv_id := Hom.ext' (Category.id_comp _) (iso_inv_b_comp_hom_b A)
        inv_hom_id := Hom.ext' (Category.id_comp _) (iso_hom_b_comp_inv_b A) })
    (by
      intro A B u
      refine Hom.ext' ?_ ?_
      · change u.a ≫ 𝟙 B.x = 𝟙 A.x ≫ u.a
        rw [Category.comp_id, Category.id_comp]
      · change u.b ≫ B.iso.inv.b = A.iso.inv.b ≫ (Y₂' Y).map u.a
        exact (inv_b_naturality u).symm)

/-- The counit of the equivalence. -/
noncomputable def counitIso (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    ofElements hq hp hY hF ⋙ toElements hq hp hY hF ≅
      𝟭 (presheafOfCategories (relVertHomPresheaf hq hp hY hF ⋙ typeToCat)).obj :=
  NatIso.ofComponents
    (fun P =>
      { hom := ⟨𝟙 P.base, Discrete.eqToHom
          ((RelVertHom.ext (sectOf_objOf hp hY hF P.base P.fiber.as)).trans
            (RelVertHom.restrict_id hq hp hY hF P.fiber.as).symm)⟩
        inv := ⟨𝟙 P.base, Discrete.eqToHom
          ((RelVertHom.ext (sectOf_objOf hp hY hF P.base P.fiber.as)).symm.trans
            (RelVertHom.restrict_id hq hp hY hF
              ⟨⟨sectOf (objOf hp hY hF P.base P.fiber.as),
                  isHomLift_sectOf hY (objOf hp hY hF P.base P.fiber.as)⟩,
                map_sectOf (objOf hp hY hF P.base P.fiber.as)⟩).symm)⟩
        hom_inv_id := PresheafOfCategories.elements_hom_ext _ _ (by
          change 𝟙 P.base ≫ 𝟙 P.base = 𝟙 P.base
          exact Category.id_comp _)
        inv_hom_id := PresheafOfCategories.elements_hom_ext _ _ (by
          change 𝟙 P.base ≫ 𝟙 P.base = 𝟙 P.base
          exact Category.id_comp _) })
    (by
      intro P Q u
      refine PresheafOfCategories.elements_hom_ext _ _ ?_
      change u.base ≫ 𝟙 Q.base = 𝟙 P.base ≫ u.base
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The fibre of the relative diagonal.** The 2-fibre product of a point `Y` of `X ×_𝒴 X`
with the relative diagonal `Δ_F` is equivalent, over the base, to the category of elements of
the presheaf of vertical morphisms `Y₁ ⟶ Y₂` whose image under `F` is the comparison
isomorphism of `Y`. -/
noncomputable def equivalenceOver (hq : q.IsFiberedInGroupoids) (hp : p.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p) :
    StacksRepresentableCFG.EquivalenceOver
      (fst p𝒯 p (RelProdP p q F) Y (RelDiag hF))
      (presheafOfCategories (relVertHomPresheaf hq hp hY hF ⋙ typeToCat)).p where
  hom := ⟨toElements hq hp hY hF, rfl⟩
  inv := ⟨ofElements hq hp hY hF, rfl⟩
  unitIso := unitIso hq hp hY hF
  counitIso := counitIso hq hp hY hF
  unit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ ?_
    intro A
    refine IsHomLift.of_fac' (fst p𝒯 p (RelProdP p q F) Y (RelDiag hF)) _ _ rfl rfl ?_
    change 𝟙 A.x = _
    simp only [Category.id_comp, eqToHom_trans]
    rfl
  counit_over := by
    refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ ?_
    intro P
    refine IsHomLift.of_fac'
      (presheafOfCategories (relVertHomPresheaf hq hp hY hF ⋙ typeToCat)).p _ _ rfl rfl ?_
    change 𝟙 P.base = _
    simp only [Category.id_comp, eqToHom_trans]
    rfl

/-- **The relative diagonal criterion as a comparison of presheaves.** The first projection of
`𝒯 ×_{Y, X ×_𝒴 X, Δ_F} X` is equivalent over `𝒯` to the category of elements of a presheaf of
sets `F` exactly when `F` and the presheaf of vertical morphisms `Y₁ ⟶ Y₂` lying over the
comparison isomorphism of `Y` become isomorphic after both are lifted to a common value
universe.

This is the relative counterpart of
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff`, and it is
the form in which Stacks 04XT is applied: the left-hand side is one clause of representability
by algebraic spaces (Stacks 02ZW) of the relative diagonal, and the right-hand side is one
clause of algebraicity of the relative isomorphism presheaves. Stating the `Nonempty` as the
conclusion is what lets a caller use it: the 2-fibre product appearing in Stacks 02ZW is formed
with the category of a `CategoryTheory.BasedCategory.ofFunctor`, which is not reducible, so its
category structure is found by unification against this conclusion rather than by instance
search. -/
theorem nonempty_equivalenceOver_fst_iff (hq : q.IsFiberedInGroupoids)
    (hp : p.IsFiberedInGroupoids) (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p)
    (G : 𝒯ᵒᵖ ⥤ Type t) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
        (fst p𝒯 p (RelProdP p q F) Y (RelDiag hF))
        (presheafOfCategories (G ⋙ typeToCat)).p) ↔
      Nonempty (relVertHomPresheaf hq hp hY hF ⋙ uliftFunctor.{t, v₃} ≅
        G ⋙ uliftFunctor.{v₃, t}) := by
  refine ⟨fun ⟨E⟩ => (PresheafOfCategories.nonempty_equivalenceOver_iff
      (relVertHomPresheaf hq hp hY hF) G).1 ⟨(equivalenceOver hq hp hY hF).symm.trans E⟩,
    fun h => ?_⟩
  obtain ⟨e⟩ := (PresheafOfCategories.nonempty_equivalenceOver_iff
    (relVertHomPresheaf hq hp hY hF) G).2 h
  exact ⟨(equivalenceOver hq hp hY hF).trans e⟩

end Equivalence

section AlphaSection

/-- The section of `Isom(F Y₁, F Y₂)` over `a` given by the comparison isomorphism of `Y`. -/
def alphaSection (hY : Y ⋙ RelProdP p q F = p𝒯) (a : 𝒯) :
    VertHom q p𝒯 (Y₁' Y ⋙ F) (Y₂' Y ⋙ F) a :=
  ⟨(Y.obj a).iso.hom, isHomLift_vertical_iso hY a⟩

/-- The underlying morphism of `alphaSection`. -/
@[simp] lemma alphaSection_coe (hY : Y ⋙ RelProdP p q F = p𝒯) (a : 𝒯) :
    (alphaSection hY a).1 = (Y.obj a).iso.hom := rfl

/-- **The fibre condition, intrinsically.** A vertical morphism `m : Y₁ a ⟶ Y₂ a` defines an
element of `RelVertHom` exactly when its image under `F` is the `α`-section at `a`, so
`relVertHomPresheaf` is the fibre of
`CategoryTheory.TwoFibreProductOver.DiagonalFibre.VertHom.presheafMap` over `alphaSection`. -/
lemma pushforward_eq_alphaSection_iff (hY : Y ⋙ RelProdP p q F = p𝒯) (hF : F ⋙ q = p)
    (a : 𝒯) (m : VertHom p p𝒯 (Y₁' Y) (Y₂' Y) a) :
    VertHom.pushforward hF m = alphaSection hY a ↔ F.map m.1 = (Y.obj a).iso.hom :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- **The `α`-section is a section of the presheaf**, i.e. it is compatible with restriction.
This is the naturality square of the comparison isomorphism of `Y` together with uniqueness of
vertical fill-ins in `𝒴`. -/
lemma restrict_alphaSection (hq : q.IsFiberedInGroupoids)
    (hY : Y ⋙ RelProdP p q F = p𝒯)
    (h₁' : (Y₁' Y ⋙ F) ⋙ q = p𝒯) (h₂' : (Y₂' Y ⋙ F) ⋙ q = p𝒯)
    {a' a : 𝒯} (h : a' ⟶ a) :
    VertHom.restrict hq h₁' h₂' h (alphaSection hY a) = alphaSection hY a' :=
  (VertHom.restrict_uniq hq h₁' h₂' h (alphaSection hY a) (alphaSection hY a') (by
    simp only [alphaSection_coe, Functor.comp_map]
    exact (iso_naturality h).symm)).symm

end AlphaSection

end CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

end
