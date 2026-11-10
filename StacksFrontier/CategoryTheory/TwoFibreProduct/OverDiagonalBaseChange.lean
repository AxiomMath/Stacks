module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# The diagonal is stable under base change, over a base (Stacks 04YR over `𝒞`)

Fix a base category `𝒞` and 1-morphisms `h : 𝒳 ⥤ 𝒴`, `s : 𝒱 ⥤ 𝒴` of categories over `𝒞`. Write
`𝒰 = 𝒳 ×_𝒴 𝒱` for their 2-fibre product over `𝒞` (`CategoryTheory.TwoFibreProductOver`, Stacks
0040), with projections `r : 𝒰 ⥤ 𝒳` and `g : 𝒰 ⥤ 𝒱`, and form the square

```text
          Δ_{𝒰/𝒱}
    𝒰  ------------>  𝒰 ×_𝒱 𝒰
    |                    |
  r |                    | r × r
    v                    v
    𝒳  ------------>  𝒳 ×_𝒴 𝒳
          Δ_{𝒳/𝒴}
```

whose right-hand leg `r × r` is the functor induced by `r` on both factors. **Stacks 04YR** says
that this square is 2-cartesian: the diagonal of a base change is the base change of the
diagonal. This file proves it in the 2-category of categories *over* `𝒞`.

The absolute version, for Mathlib's `CategoryTheory.Limits.CategoricalPullback` (Stacks 003R), is
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_baseChangeDiagonalComparison` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.DiagonalBaseChange`, and it does **not** give this
one: the comparison isomorphism of an object is arbitrary in the absolute 2-fibre product and
*vertical* in the relative one, and the two notions are inequivalent. This is the same split that
puts the over-`𝒞` form of Stacks 02XE in
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal` next to its absolute form in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Diagonal`, and this file mirrors that architecture.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.mapDiag`: the functor `r × r : 𝒰 ×_𝒱 𝒰 ⥤ 𝒳 ×_𝒴 𝒳`.
* `CategoryTheory.TwoFibreProductOver.DiagonalBaseChange`: the canonical 2-fibre product
  `(𝒰 ×_𝒱 𝒰) ×_{𝒳 ×_𝒴 𝒳} 𝒳` of the cospan `(r × r, Δ_{𝒳/𝒴})`.
* `CategoryTheory.TwoFibreProductOver.diagonalBaseChangeComparison`: the comparison functor
  `𝒰 ⥤ (𝒰 ×_𝒱 𝒰) ×_{𝒳 ×_𝒴 𝒳} 𝒳` of the square, and
  `CategoryTheory.TwoFibreProductOver.diagonalBaseChangeInverse` its quasi-inverse.
* `CategoryTheory.TwoFibreProductOver.theta`: the isomorphism `u₁ ≅ u₂` in `𝒰` attached to an
  object of the base change. This is the mathematical content.

## Main results

* `CategoryTheory.TwoFibreProductOver.isEquivalence_diagonalBaseChangeComparison`:
  **Stacks 04YR over `𝒞`**, the square is 2-cartesian.
* `CategoryTheory.TwoFibreProductOver.nonempty_equivalenceOver_diagonalBaseChange`: the same as
  an equivalence over `𝒞`, for the two categories fibred in groupoids a consumer has in hand.
* `diagonalBaseChangeComparison_comp_fst`, `_comp_snd` and `_comp_structureFunctor`: the two legs
  of the square are `Δ_{𝒰/𝒱}` and `r`, strictly, and the comparison is strictly over `𝒞`.

## Implementation notes

The proof is the one of the absolute case, carried out over `𝒞`. An object of the base change is
a point `(u₁, u₂, ψ)` of `𝒰 ×_𝒱 𝒰`, an object `x` of `𝒳`, and an isomorphism
`(r u₁, r u₂, χ) ≅ (x, x, 𝟙)` of `𝒳 ×_𝒴 𝒳` with `𝒳`-components `a : u₁.x ⟶ x`, `b : u₂.x ⟶ x`.
`CategoryTheory.TwoFibreProductOver.theta` is the isomorphism `u₁ ≅ u₂` of `𝒰` which is
`a ≫ b⁻¹` on `𝒳` and `ψ` on `𝒱`; it collapses the pair, and the comparison functor — which sends
`u` to the diagonal of `u` together with `r u` — is therefore an equivalence, with the first
factor of the `𝒰 ×_𝒱 𝒰`-component as quasi-inverse. The unit is an identity on the nose
(`diagonalBaseChangeComparison_comp_inverse`); all the content is in the counit.

Everything over `𝒞` that the absolute proof gets for free has to be checked here, and in every
case it holds because each ingredient is vertical: the comparison isomorphism of `mapDiag`
(`isHomLift_mapDiagIso`) is a composite of three vertical maps, and `theta` is vertical because
the components of a vertical isomorphism of a 2-fibre product are vertical
(`CategoryTheory.TwoFibreProductOver.isHomLift_a`, `isHomLift_b`). The compatibility square of
`theta` is the comparison square of `e` after cancelling `h b`, and it is the one step that uses
the verticality of `χ`.

One practical point dominates the file. The `𝒳`-components of the structural isomorphism of an
object `e` of the base change have endpoints spelled through `mapDiag` and `diagonal`; those
spellings are definitionally equal to `u₁.x`, `u₂.x` and `x`, but not syntactically so, and the
composite `a ≫ b⁻¹` does not even *typecheck* in the unnormalized spelling, because one factor
ends at `((diagonal hh).obj x).x` and the next starts at `((diagonal hh).obj x).y`.
`baseChangeFstHom`, `baseChangeSndHom`, `baseChangeFstInv` and `baseChangeSndInv` name the four
components with their endpoints spelled directly, and `sndIso` does the same for the structural
isomorphism of an object of `𝒰 ×_𝒱 𝒰`; after that every composite in the file is syntactic and
`rw` and instance search both work. Normalizing the spelling once, rather than relaxing
transparency, is the standard fix for this kind of problem.

No declaration here carries a `@[stacks]` attribute. Stacks 04YR is a lemma of the Categories
chapter, about the (2,1)-category of categories, and its faithful home is therefore the absolute
form `CategoryTheory.Limits.CategoricalPullback.isEquivalence_baseChangeDiagonalComparison`, which
already carries the tag. This is the same convention under which the `@[stacks 02XE]` tag stays on
the absolute form while the over-`𝒞` form in
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal` is untagged, and under which
`02XC`/`02XD` stay on `.Associativity`/`.Cancellation` rather than on `.OverComposable`/
`.OverComparison`. Tagging this file would claim a tag the absolute statement already covers.

## References

* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒱 : Type u₃} [Category.{v₃} 𝒱] {𝒴 : Type u₄} [Category.{v₄} 𝒴]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒱 : 𝒱 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {h : 𝒳 ⥤ 𝒴} {s : 𝒱 ⥤ 𝒴}

/-- `𝒰 = 𝒳 ×_𝒴 𝒱`, the base change of `h` along `s`. -/
local notation "𝒰" => TwoFibreProductOver p𝒳 p𝒱 p𝒴 h s

/-- `𝒲 = 𝒰 ×_𝒱 𝒰`, the self-product of `𝒰` over `𝒱`. -/
local notation "𝒲" =>
  TwoFibreProductOver (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
    (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s)

/-- `𝒟 = 𝒳 ×_𝒴 𝒳`, the target of the diagonal of `h`. -/
local notation "𝒟" => TwoFibreProductOver p𝒳 p𝒳 p𝒴 h h

/-- The structural isomorphism of `w : 𝒰 ×_𝒱 𝒰`, with its endpoints spelled as the `𝒱`-components
of the two factors rather than through the second projection. The two spellings are definitionally
equal, and naming this one keeps a single spelling in the rewriting below. -/
def sndIso (w : 𝒲) : w.x.y ≅ w.y.y := w.iso

/-- `sndIso` has the same underlying morphism as the structural isomorphism. -/
@[simp] lemma sndIso_hom (w : 𝒲) : (sndIso w).hom = w.iso.hom := rfl

/-- `sndIso` has the same underlying inverse as the structural isomorphism. -/
@[simp] lemma sndIso_inv (w : 𝒲) : (sndIso w).inv = w.iso.inv := rfl

/-- The comparison isomorphism of `mapDiag` at `w = (U, u₁, u₂, ψ)`: the composite
`h u₁.x ≅ s u₁.y ≅ s u₂.y ≅ h u₂.x` of the structural isomorphism of `u₁`, the image of `ψ`
under `s`, and the inverse of the structural isomorphism of `u₂`. -/
def mapDiagIso (w : 𝒲) : h.obj w.x.x ≅ h.obj w.y.x :=
  w.x.iso ≪≫ s.mapIso (sndIso w) ≪≫ w.y.iso.symm

/-- The underlying morphism of `mapDiagIso`. -/
@[simp] lemma mapDiagIso_hom (w : 𝒲) :
    (mapDiagIso w).hom = w.x.iso.hom ≫ s.map (sndIso w).hom ≫ w.y.iso.inv := rfl

/-- The comparison isomorphism of `mapDiag` is vertical: all three of its factors are. -/
lemma isHomLift_mapDiagIso (hs : s ⋙ p𝒴 = p𝒱) (w : 𝒲) :
    p𝒴.IsHomLift (𝟙 w.base) (mapDiagIso w).hom := by
  have e₁ : w.x.base = w.base := w.hx
  have e₂ : w.y.base = w.base := w.hy
  have h₁ : p𝒴.IsHomLift (𝟙 w.base) w.x.iso.hom := by
    have := w.x.vertical; rwa [e₁] at this
  have h₂ : p𝒴.IsHomLift (𝟙 w.base) (s.map (sndIso w).hom) := by
    have hv : p𝒱.IsHomLift (𝟙 w.base) (sndIso w).hom := w.vertical
    exact Functor.isHomLift_map_of_comp_eq hs (𝟙 w.base) (sndIso w).hom
  have h₃ : p𝒴.IsHomLift (𝟙 w.base) w.y.iso.inv := by
    have := w.y.vertical; rw [e₂] at this; infer_instance
  change p𝒴.IsHomLift (𝟙 w.base) (w.x.iso.hom ≫ s.map (sndIso w).hom ≫ w.y.iso.inv)
  infer_instance

/-- The functor `r × r : 𝒰 ×_𝒱 𝒰 ⥤ 𝒳 ×_𝒴 𝒳` induced by the first projection
`r : 𝒰 ⥤ 𝒳` on both factors: it sends `(U, u₁, u₂, ψ)` to `(U, u₁.x, u₂.x, mapDiagIso)`. -/
def mapDiag (hs : s ⋙ p𝒴 = p𝒱) : 𝒲 ⥤ 𝒟 where
  obj w :=
    { base := w.base
      x := w.x.x
      y := w.y.x
      hx := w.x.hx.trans w.hx
      hy := w.y.hx.trans w.hy
      iso := mapDiagIso w
      vertical := isHomLift_mapDiagIso hs w }
  map {w w'} f :=
    { hbase := f.hbase
      a := f.a.a
      b := f.b.a
      ha := isHomLift_a f.a f.hbase f.ha
      hb := isHomLift_a f.b f.hbase f.hb
      w := by
        have ha := f.a.w
        have hb := f.b.w
        have hf : f.a.b ≫ (sndIso w').hom = (sndIso w).hom ≫ f.b.b := f.w
        have key2 : s.map f.a.b ≫ s.map (sndIso w').hom
            = s.map (sndIso w).hom ≫ s.map f.b.b := by
          rw [← s.map_comp, ← s.map_comp, hf]
        have key : s.map f.b.b ≫ w'.y.iso.inv = w.y.iso.inv ≫ h.map f.b.a := by
          rw [Iso.comp_inv_eq, Category.assoc, eq_comm, Iso.inv_comp_eq]
          exact hb
        change h.map f.a.a ≫ (w'.x.iso.hom ≫ s.map (sndIso w').hom ≫ w'.y.iso.inv)
          = (w.x.iso.hom ≫ s.map (sndIso w).hom ≫ w.y.iso.inv) ≫ h.map f.b.a
        simp only [Category.assoc]
        rw [reassoc_of% ha, reassoc_of% key2, key] }
  map_id _ := Hom.ext' rfl rfl
  map_comp _ _ := Hom.ext' rfl rfl

/-- The `𝒳`-component of `mapDiag` at `w` is the `𝒳`-component of the first factor. -/
@[simp] lemma mapDiag_obj_x (hs : s ⋙ p𝒴 = p𝒱) (w : 𝒲) : ((mapDiag hs).obj w).x = w.x.x := rfl

/-- The second `𝒳`-component of `mapDiag` at `w` is the `𝒳`-component of the second factor. -/
@[simp] lemma mapDiag_obj_y (hs : s ⋙ p𝒴 = p𝒱) (w : 𝒲) : ((mapDiag hs).obj w).y = w.y.x := rfl

/-- The comparison isomorphism of `mapDiag` at `w` is `mapDiagIso`. -/
@[simp] lemma mapDiag_obj_iso (hs : s ⋙ p𝒴 = p𝒱) (w : 𝒲) :
    ((mapDiag hs).obj w).iso = mapDiagIso w := rfl

/-- The first component of `(mapDiag hs).map f`. -/
@[simp] lemma mapDiag_map_a (hs : s ⋙ p𝒴 = p𝒱) {w w' : 𝒲} (f : w ⟶ w') :
    ((mapDiag hs).map f).a = f.a.a := rfl

/-- The second component of `(mapDiag hs).map f`. -/
@[simp] lemma mapDiag_map_b (hs : s ⋙ p𝒴 = p𝒱) {w w' : 𝒲} (f : w ⟶ w') :
    ((mapDiag hs).map f).b = f.b.a := rfl


section BaseChange

variable (hh : h ⋙ p𝒴 = p𝒳) (hs : s ⋙ p𝒴 = p𝒱)

/-- The canonical 2-fibre product `(𝒰 ×_𝒱 𝒰) ×_{𝒳 ×_𝒴 𝒳} 𝒳` of the cospan `(r × r, Δ_{𝒳/𝒴})`:
the base change of the diagonal of `h` along `r × r`. -/
abbrev DiagonalBaseChange : Type _ :=
  TwoFibreProductOver
    (structureFunctor (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
      (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s))
    p𝒳 (structureFunctor p𝒳 p𝒳 p𝒴 h h) (mapDiag hs) (diagonal hh)

/-! ### The components of the structural isomorphism, with normalized spellings

The structural isomorphism of an object `e` of the base change is an isomorphism
`(r u₁, r u₂, χ) ≅ (x, x, 𝟙)` of `𝒳 ×_𝒴 𝒳`, so its `𝒳`-components have endpoints spelled through
`mapDiag` and `diagonal`. Those spellings are definitionally equal to `u₁.x`, `u₂.x` and `x`, but
not syntactically so, and the composite of the first component of the isomorphism with the second
component of its inverse — which is the whole content of Stacks 04YR — does not even *typecheck*
in the unnormalized spelling. The four accessors below name the four components with their
endpoints spelled directly, which is what makes every composite below syntactic. -/

/-- The first `𝒳`-component of the structural isomorphism of `e`, as `u₁.x ⟶ x`. -/
def baseChangeFstHom (e : DiagonalBaseChange hh hs) : e.x.x.x ⟶ e.y := e.iso.hom.a

/-- The second `𝒳`-component of the structural isomorphism of `e`, as `u₂.x ⟶ x`. -/
def baseChangeSndHom (e : DiagonalBaseChange hh hs) : e.x.y.x ⟶ e.y := e.iso.hom.b

/-- The first `𝒳`-component of the inverse structural isomorphism of `e`, as `x ⟶ u₁.x`. -/
def baseChangeFstInv (e : DiagonalBaseChange hh hs) : e.y ⟶ e.x.x.x := e.iso.inv.a

/-- The second `𝒳`-component of the inverse structural isomorphism of `e`, as `x ⟶ u₂.x`. -/
def baseChangeSndInv (e : DiagonalBaseChange hh hs) : e.y ⟶ e.x.y.x := e.iso.inv.b

/-- The first components of the structural isomorphism and of its inverse cancel. -/
lemma fstHom_comp_fstInv (e : DiagonalBaseChange hh hs) :
    baseChangeFstHom hh hs e ≫ baseChangeFstInv hh hs e = 𝟙 e.x.x.x :=
  congrArg Hom.a e.iso.hom_inv_id

/-- The first components of the structural isomorphism and of its inverse cancel, the other way. -/
lemma fstInv_comp_fstHom (e : DiagonalBaseChange hh hs) :
    baseChangeFstInv hh hs e ≫ baseChangeFstHom hh hs e = 𝟙 e.y :=
  congrArg Hom.a e.iso.inv_hom_id

/-- The second components of the structural isomorphism and of its inverse cancel. -/
lemma sndHom_comp_sndInv (e : DiagonalBaseChange hh hs) :
    baseChangeSndHom hh hs e ≫ baseChangeSndInv hh hs e = 𝟙 e.x.y.x :=
  congrArg Hom.b e.iso.hom_inv_id

/-- The second components of the structural isomorphism and of its inverse cancel, the other
way. -/
lemma sndInv_comp_sndHom (e : DiagonalBaseChange hh hs) :
    baseChangeSndInv hh hs e ≫ baseChangeSndHom hh hs e = 𝟙 e.y :=
  congrArg Hom.b e.iso.inv_hom_id

/-- Both `𝒳`-components of the structural isomorphism of an object of the base change are
vertical, because the isomorphism itself is and the components of a morphism of a 2-fibre product
lie over the same morphism of `𝒞` as the morphism itself. -/
lemma isHomLift_baseChangeFstHom (e : DiagonalBaseChange hh hs) :
    p𝒳.IsHomLift (𝟙 e.base) (baseChangeFstHom hh hs e) :=
  isHomLift_a e.iso.hom (𝟙 e.base) e.vertical

/-- The second `𝒳`-component of the inverse structural isomorphism is vertical: the inverse of a
vertical isomorphism is vertical. -/
lemma isHomLift_baseChangeSndInv (e : DiagonalBaseChange hh hs) :
    p𝒳.IsHomLift (𝟙 e.base) (baseChangeSndInv hh hs e) := by
  have hv := e.vertical
  have hinv : (structureFunctor p𝒳 p𝒳 p𝒴 h h).IsHomLift (𝟙 e.base) e.iso.inv := inferInstance
  exact isHomLift_b e.iso.inv (𝟙 e.base) hinv

/-- **The comparison square of an object of the base change, solved for `h a`.** The structural
isomorphism of `e` says `h a = φ₁ ∘ s ψ ∘ φ₂⁻¹ ∘ h b`, the comparison isomorphism of
`(diagonal hh).obj x` being an identity and that of `(mapDiag hs).obj (u₁, u₂, ψ)` being
`mapDiagIso`. -/
lemma map_baseChangeFstHom (e : DiagonalBaseChange hh hs) :
    h.map (baseChangeFstHom hh hs e)
      = e.x.x.iso.hom ≫ s.map (sndIso e.x).hom ≫ e.x.y.iso.inv ≫
          h.map (baseChangeSndHom hh hs e) := by
  have hw : h.map (baseChangeFstHom hh hs e) ≫ 𝟙 (h.obj e.y)
      = (e.x.x.iso.hom ≫ s.map (sndIso e.x).hom ≫ e.x.y.iso.inv) ≫
        h.map (baseChangeSndHom hh hs e) := e.iso.hom.w
  rw [Category.comp_id] at hw
  rw [hw]
  simp only [Category.assoc]

/-- **The key isomorphism of Stacks 04YR over `𝒞`, on `𝒳`.** For an object `e` of the base
change the two factors `u₁`, `u₂` of its `𝒰 ×_𝒱 𝒰`-component have isomorphic `𝒳`-components, by
`a ≫ b⁻¹` for the two `𝒳`-components `a`, `b` of the structural isomorphism of `e`. -/
def thetaFstIso (e : DiagonalBaseChange hh hs) : e.x.x.x ≅ e.x.y.x where
  hom := baseChangeFstHom hh hs e ≫ baseChangeSndInv hh hs e
  inv := baseChangeSndHom hh hs e ≫ baseChangeFstInv hh hs e
  hom_inv_id := by
    rw [Category.assoc, ← Category.assoc (baseChangeSndInv hh hs e),
      sndInv_comp_sndHom hh hs e, Category.id_comp, fstHom_comp_fstInv hh hs e]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc (baseChangeFstInv hh hs e),
      fstInv_comp_fstHom hh hs e, Category.id_comp, sndHom_comp_sndInv hh hs e]

/-- The underlying morphism of `thetaFstIso`. -/
@[simp] lemma thetaFstIso_hom (e : DiagonalBaseChange hh hs) :
    (thetaFstIso hh hs e).hom = baseChangeFstHom hh hs e ≫ baseChangeSndInv hh hs e := rfl

/-- `thetaFstIso` is vertical. -/
lemma isHomLift_thetaFstIso (e : DiagonalBaseChange hh hs) :
    p𝒳.IsHomLift (𝟙 e.base) (thetaFstIso hh hs e).hom := by
  have h₁ := isHomLift_baseChangeFstHom hh hs e
  have h₂ := isHomLift_baseChangeSndInv hh hs e
  rw [thetaFstIso_hom]
  infer_instance

/-- **The key isomorphism of Stacks 04YR over `𝒞`.** For an object `e` of the base change — a
point `(u₁, u₂, ψ)` of `𝒰 ×_𝒱 𝒰` together with an object `x` of `𝒳` and an isomorphism
`(r u₁, r u₂, χ) ≅ (x, x, 𝟙)` of `𝒳 ×_𝒴 𝒳` — the two factors `u₁` and `u₂` are isomorphic *in
`𝒰`*: on `𝒳` by `thetaFstIso` and on `𝒱` by `ψ`. The comparison square is the comparison square
of `e` after cancelling `h b`, and this is the one place where the verticality of `χ` is used.

This is what makes the base change of `Δ_{𝒳/𝒴}` along `r × r` equivalent to `𝒰`: an object of
the base change is a *pair* of objects of `𝒰` with isomorphic images, and this isomorphism
collapses the pair. -/
noncomputable def theta (e : DiagonalBaseChange hh hs) : e.x.x ≅ e.x.y :=
  isoMkVertical (U := e.base) (thetaFstIso hh hs e) (sndIso e.x)
    (isHomLift_thetaFstIso hh hs e)
    (by
      have hv : p𝒱.IsHomLift (𝟙 e.x.base) (sndIso e.x).hom := e.x.vertical
      rw [show e.x.base = e.base from e.hx] at hv
      exact hv)
    (by
      have hbb : h.map (baseChangeSndHom hh hs e) ≫ h.map (baseChangeSndInv hh hs e)
          = 𝟙 (h.obj e.x.y.x) := by
        rw [← h.map_comp, sndHom_comp_sndInv hh hs e, h.map_id]
      change h.map (baseChangeFstHom hh hs e ≫ baseChangeSndInv hh hs e) ≫ e.x.y.iso.hom
        = e.x.x.iso.hom ≫ s.map (sndIso e.x).hom
      rw [h.map_comp, Category.assoc, map_baseChangeFstHom hh hs e]
      simp only [Category.assoc]
      rw [reassoc_of% hbb]
      simp)

/-- The `𝒳`-component of `theta`. -/
@[simp] lemma theta_hom_a (e : DiagonalBaseChange hh hs) :
    (theta hh hs e).hom.a = baseChangeFstHom hh hs e ≫ baseChangeSndInv hh hs e := rfl

/-- The `𝒱`-component of `theta` is the structural isomorphism of the `𝒰 ×_𝒱 𝒰`-component. -/
@[simp] lemma theta_hom_b (e : DiagonalBaseChange hh hs) :
    (theta hh hs e).hom.b = (sndIso e.x).hom := rfl

/-- `theta` is vertical. -/
lemma isHomLift_theta (e : DiagonalBaseChange hh hs) :
    (structureFunctor p𝒳 p𝒱 p𝒴 h s).IsHomLift (𝟙 e.base) (theta hh hs e).hom := by
  refine structureFunctor_isHomLift (theta hh hs e).hom (𝟙 e.base) ?_
  exact isHomLift_thetaFstIso hh hs e

/-- The comparison isomorphism of the comparison functor at `u`: the image under `r × r` of the
diagonal of `u` is the diagonal of `r u`, both comparison isomorphisms being trivial. -/
noncomputable def comparisonIso (u : 𝒰) :
    (mapDiag hs).obj ((diagonal snd_comp_eq).obj u) ≅ (diagonal hh).obj u.x :=
  isoMkVertical (U := u.base) (Iso.refl u.x) (Iso.refl u.x)
    (IsHomLift.id u.hx) (IsHomLift.id u.hx)
    (by
      change h.map (𝟙 u.x) ≫ 𝟙 (h.obj u.x)
        = (u.iso.hom ≫ s.map (𝟙 u.y) ≫ u.iso.inv) ≫ h.map (𝟙 u.x)
      simp)

/-- The `𝒳`-component of `comparisonIso` is an identity. -/
@[simp] lemma comparisonIso_hom_a (u : 𝒰) : (comparisonIso hh hs u).hom.a = 𝟙 u.x := rfl

/-- The second `𝒳`-component of `comparisonIso` is an identity. -/
@[simp] lemma comparisonIso_hom_b (u : 𝒰) : (comparisonIso hh hs u).hom.b = 𝟙 u.x := rfl

/-- **The comparison functor of Stacks 04YR over `𝒞`.** It sends an object `u` of
`𝒰 = 𝒳 ×_𝒴 𝒱` to the diagonal of `u` in `𝒰 ×_𝒱 𝒰` together with `r u` and the trivial
comparison isomorphism. -/
noncomputable def diagonalBaseChangeComparison : 𝒰 ⥤ DiagonalBaseChange hh hs where
  obj u :=
    { base := u.base
      x := (diagonal snd_comp_eq).obj u
      y := u.x
      hx := rfl
      hy := u.hx
      iso := comparisonIso hh hs u
      vertical := by
        refine structureFunctor_isHomLift (comparisonIso hh hs u).hom (𝟙 u.base) ?_
        rw [comparisonIso_hom_a]
        exact IsHomLift.id u.hx }
  map {u u'} f :=
    { hbase := f.hbase
      a := (diagonal snd_comp_eq).map f
      b := f.a
      ha := by
        refine structureFunctor_isHomLift ((diagonal snd_comp_eq).map f) f.hbase ?_
        rw [diagonal_map_a]
        exact structureFunctor_isHomLift f f.hbase f.ha
      hb := f.ha
      w := Hom.ext' (by simp) (by simp) }
  map_id _ := Hom.ext' (Hom.ext' rfl rfl) rfl
  map_comp _ _ := Hom.ext' (Hom.ext' rfl rfl) rfl

/-- The quasi-inverse of the comparison functor: read off the first factor of the
`𝒰 ×_𝒱 𝒰`-component. -/
abbrev diagonalBaseChangeInverse : DiagonalBaseChange hh hs ⥤ 𝒰 :=
  fst (structureFunctor (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
      (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s))
    p𝒳 (structureFunctor p𝒳 p𝒳 p𝒴 h h) (mapDiag hs) (diagonal hh) ⋙
  fst (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
    (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s)

/-- The comparison functor followed by its quasi-inverse is the identity, on the nose. -/
lemma diagonalBaseChangeComparison_comp_inverse :
    diagonalBaseChangeComparison hh hs ⋙ diagonalBaseChangeInverse hh hs = 𝟭 _ := rfl

/-- The comparison functor is a 1-morphism over `𝒞`. -/
lemma diagonalBaseChangeComparison_comp_structureFunctor :
    diagonalBaseChangeComparison hh hs ⋙
        structureFunctor
          (structureFunctor (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
            (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s))
          p𝒳 (structureFunctor p𝒳 p𝒳 p𝒴 h h) (mapDiag hs) (diagonal hh) =
      structureFunctor p𝒳 p𝒱 p𝒴 h s := rfl

/-- The first leg of the base-change square is the diagonal of `𝒰` over `𝒱`. -/
lemma diagonalBaseChangeComparison_comp_fst :
    diagonalBaseChangeComparison hh hs ⋙
        fst (structureFunctor (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
            (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s))
          p𝒳 (structureFunctor p𝒳 p𝒳 p𝒴 h h) (mapDiag hs) (diagonal hh) =
      diagonal snd_comp_eq := rfl

/-- The second leg of the base-change square is the first projection `r : 𝒰 ⥤ 𝒳`. -/
lemma diagonalBaseChangeComparison_comp_snd :
    diagonalBaseChangeComparison hh hs ⋙
        snd (structureFunctor (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
            (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s))
          p𝒳 (structureFunctor p𝒳 p𝒳 p𝒴 h h) (mapDiag hs) (diagonal hh) =
      fst p𝒳 p𝒱 p𝒴 h s := rfl

/-- The `𝒰 ×_𝒱 𝒰`-component of the comparison functor is the diagonal of `𝒰` over `𝒱`. -/
@[simp] lemma diagonalBaseChangeComparison_obj_x (u : 𝒰) :
    ((diagonalBaseChangeComparison hh hs).obj u).x = (diagonal snd_comp_eq).obj u := rfl

/-- The `𝒳`-component of the comparison functor is the first projection. -/
@[simp] lemma diagonalBaseChangeComparison_obj_y (u : 𝒰) :
    ((diagonalBaseChangeComparison hh hs).obj u).y = u.x := rfl

/-- The structural isomorphism of the comparison functor is `comparisonIso`. -/
@[simp] lemma diagonalBaseChangeComparison_obj_iso (u : 𝒰) :
    ((diagonalBaseChangeComparison hh hs).obj u).iso = comparisonIso hh hs u := rfl

/-- The `𝒰 ×_𝒱 𝒰`-component of the comparison functor on morphisms. -/
@[simp] lemma diagonalBaseChangeComparison_map_a {u u' : 𝒰} (f : u ⟶ u') :
    ((diagonalBaseChangeComparison hh hs).map f).a = (diagonal snd_comp_eq).map f := rfl

/-- The `𝒳`-component of the comparison functor on morphisms. -/
@[simp] lemma diagonalBaseChangeComparison_map_b {u u' : 𝒰} (f : u ⟶ u') :
    ((diagonalBaseChangeComparison hh hs).map f).b = f.a := rfl

/-- The first `𝒳`-component of the structural isomorphism of `e`, as an isomorphism. -/
def baseChangeFstIso (e : DiagonalBaseChange hh hs) : e.x.x.x ≅ e.y where
  hom := baseChangeFstHom hh hs e
  inv := baseChangeFstInv hh hs e
  hom_inv_id := fstHom_comp_fstInv hh hs e
  inv_hom_id := fstInv_comp_fstHom hh hs e

/-- The `.a`-projection of the comparison square of a morphism of the base change. -/
lemma baseChangeFstHom_naturality {e e' : DiagonalBaseChange hh hs} (f : e ⟶ e') :
    f.a.a.a ≫ baseChangeFstHom hh hs e' = baseChangeFstHom hh hs e ≫ f.b := by
  have h₀ := congrArg Hom.a f.w
  simp only [comp_a, mapDiag_map_a, diagonal_map_a] at h₀
  exact h₀

/-- The `.b`-projection of the comparison square of a morphism of the base change. -/
lemma baseChangeSndHom_naturality {e e' : DiagonalBaseChange hh hs} (f : e ⟶ e') :
    f.a.b.a ≫ baseChangeSndHom hh hs e' = baseChangeSndHom hh hs e ≫ f.b := by
  have h₀ := congrArg Hom.b f.w
  simp only [comp_b, mapDiag_map_b, diagonal_map_b] at h₀
  exact h₀

/-- The same square solved for the inverse: the second `𝒳`-component of the inverse structural
isomorphism is natural. -/
lemma baseChangeSndInv_naturality {e e' : DiagonalBaseChange hh hs} (f : e ⟶ e') :
    f.b ≫ baseChangeSndInv hh hs e' = baseChangeSndInv hh hs e ≫ f.a.b.a := by
  have hb := baseChangeSndHom_naturality hh hs f
  rw [← Category.id_comp (f.b ≫ baseChangeSndInv hh hs e'),
    ← sndInv_comp_sndHom hh hs e, Category.assoc, ← Category.assoc _ f.b, ← hb]
  simp only [Category.assoc, sndHom_comp_sndInv hh hs e', Category.comp_id]

/-- **Naturality of the key isomorphism.** A morphism of the base change intertwines the two
instances of `theta`: on `𝒳` this is the comparison square of the morphism after cancelling the
second `𝒳`-component, and on `𝒱` it is the comparison square of its `𝒰 ×_𝒱 𝒰`-component. -/
lemma theta_naturality {e e' : DiagonalBaseChange hh hs} (f : e ⟶ e') :
    f.a.a ≫ (theta hh hs e').hom = (theta hh hs e).hom ≫ f.a.b := by
  refine Hom.ext' ?_ ?_
  · have ha := baseChangeFstHom_naturality hh hs f
    have hinv := baseChangeSndInv_naturality hh hs f
    simp only [comp_a, theta_hom_a]
    rw [← Category.assoc, ha, Category.assoc, hinv, Category.assoc]
  · have hw : f.a.a.b ≫ (sndIso e'.x).hom = (sndIso e.x).hom ≫ f.a.b.b := f.a.w
    simp only [comp_b, theta_hom_b]
    exact hw

/-- The `𝒰 ×_𝒱 𝒰`-component of the counit at `e`: the diagonal of `u₁` is isomorphic to
`(u₁, u₂, ψ)`, by the identity on the first factor and `theta` on the second. -/
noncomputable def counitFstIso (e : DiagonalBaseChange hh hs) :
    (diagonal snd_comp_eq).obj e.x.x ≅ e.x :=
  isoMkVertical (U := e.base) (Iso.refl e.x.x) (theta hh hs e)
    (IsHomLift.id (e.x.hx.trans e.hx)) (isHomLift_theta hh hs e)
    (by
      change (snd p𝒳 p𝒱 p𝒴 h s).map (𝟙 e.x.x) ≫ e.x.iso.hom
        = 𝟙 ((snd p𝒳 p𝒱 p𝒴 h s).obj e.x.x) ≫ (snd p𝒳 p𝒱 p𝒴 h s).map (theta hh hs e).hom
      simp only [Functor.map_id, Category.id_comp]
      rfl)

/-- The `𝒳`-component of the counit is an identity. -/
@[simp] lemma counitFstIso_hom_a (e : DiagonalBaseChange hh hs) :
    (counitFstIso hh hs e).hom.a = 𝟙 e.x.x := rfl

/-- The second `𝒰`-component of the counit is `theta`. -/
@[simp] lemma counitFstIso_hom_b (e : DiagonalBaseChange hh hs) :
    (counitFstIso hh hs e).hom.b = (theta hh hs e).hom := rfl

/-- The object component of the counit isomorphism: on the `𝒰 ×_𝒱 𝒰`-factor it is
`counitFstIso` and on the `𝒳`-factor the first component of the structural isomorphism. -/
noncomputable def counitIsoObj (e : DiagonalBaseChange hh hs) :
    (diagonalBaseChangeComparison hh hs).obj ((diagonalBaseChangeInverse hh hs).obj e) ≅ e :=
  isoMkVertical (U := e.base) (counitFstIso hh hs e) (baseChangeFstIso hh hs e)
    (structureFunctor_isHomLift (counitFstIso hh hs e).hom (𝟙 e.base)
      (by rw [counitFstIso_hom_a]; exact IsHomLift.id (e.x.hx.trans e.hx)))
    (isHomLift_baseChangeFstHom hh hs e)
    (by
      refine Hom.ext' ?_ ?_
      · change Hom.a (𝟙 e.x.x) ≫ baseChangeFstHom hh hs e
          = 𝟙 e.x.x.x ≫ baseChangeFstHom hh hs e
        rw [id_a]
      · change (theta hh hs e).hom.a ≫ baseChangeSndHom hh hs e
          = 𝟙 e.x.x.x ≫ baseChangeFstHom hh hs e
        rw [theta_hom_a, Category.id_comp, Category.assoc, sndInv_comp_sndHom hh hs e,
          Category.comp_id])

/-- The counit isomorphism of the equivalence. Naturality is checked componentwise: on the
`𝒰 ×_𝒱 𝒰`-factor it reduces to `theta_naturality`, and on the `𝒳`-factor to the `.a`-projection
of the comparison square. -/
noncomputable def counitIso :
    diagonalBaseChangeInverse hh hs ⋙ diagonalBaseChangeComparison hh hs ≅
      𝟭 (DiagonalBaseChange hh hs) :=
  NatIso.ofComponents (fun e => counitIsoObj hh hs e) (by
    intro e e' f
    refine Hom.ext' ?_ ?_
    · refine Hom.ext' ?_ ?_
      · change f.a.a ≫ 𝟙 e'.x.x = 𝟙 e.x.x ≫ f.a.a
        rw [Category.comp_id, Category.id_comp]
      · change f.a.a ≫ (theta hh hs e').hom = (theta hh hs e).hom ≫ f.a.b
        exact theta_naturality hh hs f
    · change f.a.a.a ≫ baseChangeFstHom hh hs e' = baseChangeFstHom hh hs e ≫ f.b
      exact baseChangeFstHom_naturality hh hs f)

/-- **Stacks 04YR, over the base category `𝒞`.** Let `h : 𝒳 ⥤ 𝒴` and `s : 𝒱 ⥤ 𝒴` be
1-morphisms of categories over `𝒞`, let `𝒰 = 𝒳 ×_𝒴 𝒱` be their 2-fibre product over `𝒞` with
projections `r : 𝒰 ⥤ 𝒳` and `g : 𝒰 ⥤ 𝒱`, and form the square

```text
          Δ_{𝒰/𝒱}
    𝒰  ------------>  𝒰 ×_𝒱 𝒰
    |                    |
  r |                    | r × r
    v                    v
    𝒳  ------------>  𝒳 ×_𝒴 𝒳
          Δ_{𝒳/𝒴}
```

Then the square is 2-cartesian over `𝒞`: the comparison functor from `𝒰` to the canonical
2-fibre product `(𝒰 ×_𝒱 𝒰) ×_{𝒳 ×_𝒴 𝒳} 𝒳` of the cospan `(r × r, Δ_{𝒳/𝒴})` is an equivalence.
In other words the diagonal of a base change is the base change of the diagonal.

The quasi-inverse reads off the first factor of the `𝒰 ×_𝒱 𝒰`-component, the unit is an identity
by `diagonalBaseChangeComparison_comp_inverse`, and the counit is `counitIso`, whose content is
`theta`. -/
theorem isEquivalence_diagonalBaseChangeComparison :
    (diagonalBaseChangeComparison hh hs).IsEquivalence :=
  Functor.IsEquivalence.mk' (diagonalBaseChangeInverse hh hs)
    (eqToIso (diagonalBaseChangeComparison_comp_inverse hh hs).symm)
    (counitIso hh hs)

/-- **Stacks 04YR over `𝒞`, as an equivalence over `𝒞`.** For a consumer whose two categories are
fibred in groupoids, the comparison functor of the base-change square for the diagonal is an
equivalence *over* `𝒞`: a quasi-inverse strictly over `𝒞` exists, with vertical unit and counit.
Only `Nonempty` is asserted, as in
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence`, because the quasi-inverse over
`𝒞` is produced by a choice inside an existential. -/
theorem nonempty_equivalenceOver_diagonalBaseChange
    (h₁ : (structureFunctor p𝒳 p𝒱 p𝒴 h s).IsFiberedInGroupoids)
    (h₂ : (structureFunctor
      (structureFunctor (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
        (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s))
      p𝒳 (structureFunctor p𝒳 p𝒳 p𝒴 h h) (mapDiag hs) (diagonal hh)).IsFiberedInGroupoids) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver (structureFunctor p𝒳 p𝒱 p𝒴 h s)
      (structureFunctor
        (structureFunctor (structureFunctor p𝒳 p𝒱 p𝒴 h s) (structureFunctor p𝒳 p𝒱 p𝒴 h s) p𝒱
          (snd p𝒳 p𝒱 p𝒴 h s) (snd p𝒳 p𝒱 p𝒴 h s))
        p𝒳 (structureFunctor p𝒳 p𝒳 p𝒴 h h) (mapDiag hs) (diagonal hh))) :=
  StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h₁ h₂
    (diagonalBaseChangeComparison hh hs)
    (diagonalBaseChangeComparison_comp_structureFunctor hh hs)
    (isEquivalence_diagonalBaseChangeComparison hh hs)

end BaseChange

end CategoryTheory.TwoFibreProductOver

end
