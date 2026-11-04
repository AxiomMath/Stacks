module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# A 2-fibre product over a base as a pullback along the relative diagonal, over `𝒞`

Fix a base category `𝒞` and 1-morphisms `F : 𝒳 ⥤ 𝒵`, `G : 𝒴 ⥤ 𝒵`, `H : 𝒵 ⥤ 𝒯` of categories
over `𝒞`, all strictly over `𝒞`. This file shows that the square

```text
          Θ
  𝒳 ×_𝒵 𝒴  ---->  𝒳 ×_𝒯 𝒴
    |                 |
  π |                 | ρ
    v                 v
    𝒵  --Δ_{𝒵/𝒯}-->  𝒵 ×_𝒯 𝒵
```

is a 2-fibre product diagram, where `Θ = mapBaseOver` sends `(U, x, y, φ)` to `(U, x, y, H φ)`,
`π = toBaseOver` sends it to `F x`, and `ρ = mapBothOver` sends `(U, x, y, ψ)` to
`(U, F x, G y, ψ)`. The square 2-commutes via `relativeDiagonalSquareIsoOver`, whose component at
`(U, x, y, φ)` is `(𝟙, φ⁻¹)`. Being a 2-fibre product diagram means that the induced functor
`toRelativeDiagonalPullbackOver` into the 2-fibre product of the cospan `(ρ, Δ_{𝒵/𝒯})` is an
equivalence of categories.

In the case `G = F`, the diagonal of a composite is the diagonal of the first factor followed by
`Θ`.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.mapBaseOver`: the top map `Θ`.
* `CategoryTheory.TwoFibreProductOver.mapBothOver`: the right-hand map `ρ`.
* `CategoryTheory.TwoFibreProductOver.toBaseOver`: the left-hand map `π`.
* `CategoryTheory.TwoFibreProductOver.relativeDiagonalSquareIsoOver`: the 2-cell `σ`.
* `CategoryTheory.TwoFibreProductOver.toRelativeDiagonalPullbackOver`: the comparison functor.

## Main results

* `CategoryTheory.TwoFibreProductOver.isEquivalence_toRelativeDiagonalPullbackOver`: the square is
  2-cartesian.
* `CategoryTheory.TwoFibreProductOver.diagonal_comp_mapBaseOver`: `Δ_{𝒳/𝒯} = Δ_{𝒳/𝒵} ⋙ Θ`.
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver



universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u₂} [Category.{v₂} 𝒳] {𝒴 : Type u₃} [Category.{v₃} 𝒴]
variable {𝒵 : Type u₄} [Category.{v₄} 𝒵] {𝒯 : Type u₅} [Category.{v₅} 𝒯]
variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒵 : 𝒵 ⥤ 𝒞) (p𝒯 : 𝒯 ⥤ 𝒞)
variable (F : 𝒳 ⥤ 𝒵) (G : 𝒴 ⥤ 𝒵) (H : 𝒵 ⥤ 𝒯)

section Maps

variable (hH : H ⋙ p𝒯 = p𝒵)

/-- **Functoriality of the 2-fibre product in its base, over `𝒞`.** For 1-morphisms
`F : 𝒳 ⥤ 𝒵`, `G : 𝒴 ⥤ 𝒵` and `H : 𝒵 ⥤ 𝒯` of categories over `𝒞` with `H` strictly over `𝒞`,
the functor `Θ : 𝒳 ×_𝒵 𝒴 ⥤ 𝒳 ×_𝒯 𝒴` sending `(U, x, y, φ)` to `(U, x, y, H φ)`: the identity
on both factors, applying `H` to the comparison isomorphism. -/
def mapBaseOver :
    TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G ⥤
      TwoFibreProductOver p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H) where
  obj P :=
    { base := P.base
      x := P.x
      y := P.y
      hx := P.hx
      hy := P.hy
      iso := H.mapIso P.iso
      vertical := by
        have := P.vertical
        exact Functor.isHomLift_map_of_comp_eq hH (𝟙 P.base) P.iso.hom }
  map φ :=
    { hbase := φ.hbase
      a := φ.a
      b := φ.b
      ha := φ.ha
      hb := φ.hb
      w := by
        simp only [Functor.comp_map, Functor.mapIso_hom]
        rw [← H.map_comp, φ.w, H.map_comp] }
  map_id P := by apply Hom.ext' <;> rfl
  map_comp φ ψ := by apply Hom.ext' <;> rfl

/-- `CategoryTheory.TwoFibreProductOver.mapBaseOver` is strictly a 1-morphism over `𝒞`: it
leaves the base object and the base morphism of a point of the 2-fibre product untouched. -/
theorem mapBaseOver_comp_structureFunctor :
    mapBaseOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hH ⋙
        structureFunctor p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H) =
      structureFunctor p𝒳 p𝒴 p𝒵 F G := rfl

end Maps

section Both

variable (hF : F ⋙ p𝒵 = p𝒳) (hG : G ⋙ p𝒵 = p𝒴)

/-- The functor `ρ : 𝒳 ×_𝒯 𝒴 ⥤ 𝒵 ×_𝒯 𝒵` of categories over `𝒞` sending `(U, x, y, φ)` to
`(U, F x, G y, φ)`, for `F` and `G` strictly over `𝒞`. -/
def mapBothOver :
    TwoFibreProductOver p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H) ⥤
      TwoFibreProductOver p𝒵 p𝒵 p𝒯 H H where
  obj P :=
    { base := P.base
      x := F.obj P.x
      y := G.obj P.y
      hx := (Functor.congr_obj hF P.x).trans P.hx
      hy := (Functor.congr_obj hG P.y).trans P.hy
      iso := P.iso
      vertical := P.vertical }
  map φ := by
    let _ : p𝒳.IsHomLift φ.hbase φ.a := φ.ha
    let _ : p𝒴.IsHomLift φ.hbase φ.b := φ.hb
    exact
      { hbase := φ.hbase
        a := F.map φ.a
        b := G.map φ.b
        ha := Functor.isHomLift_map_of_comp_eq hF φ.hbase φ.a
        hb := Functor.isHomLift_map_of_comp_eq hG φ.hbase φ.b
        w := by simpa only [Functor.comp_map] using φ.w }
  map_id P := by apply Hom.ext' <;> simp
  map_comp φ ψ := by apply Hom.ext' <;> simp

/-- The functor `π : 𝒳 ×_𝒵 𝒴 ⥤ 𝒵` sending `(U, x, y, φ)` to `F x`, i.e. the first projection
followed by `F`. -/
def toBaseOver : TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G ⥤ 𝒵 :=
  fst p𝒳 p𝒴 p𝒵 F G ⋙ F

include hF in
/-- `CategoryTheory.TwoFibreProductOver.toBaseOver` is strictly a 1-morphism over `𝒞`. -/
theorem toBaseOver_comp_p :
    toBaseOver p𝒳 p𝒴 p𝒵 F G ⋙ p𝒵 = structureFunctor p𝒳 p𝒴 p𝒵 F G := by
  rw [toBaseOver, Functor.assoc, hF]
  exact fst_comp_eq

variable (hH : H ⋙ p𝒯 = p𝒵)

/-- The component at a point `P = (U, x, y, φ)` of `𝒳 ×_𝒵 𝒴` of the 2-cell `π ⋙ Δ_{𝒵/𝒯} ≅ Θ ⋙ ρ`:
the isomorphism `Δ_{𝒵/𝒯}(F x) ≅ (F x, G y, H φ)` of `𝒵 ×_𝒯 𝒵` whose two components are `𝟙_{F x}`
and `φ`, and whose inverse has components `𝟙_{F x}` and `φ⁻¹`. -/
noncomputable def relativeDiagonalSquareObjectIsoOver
    (P : TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G) :
    (diagonal hH).obj (F.obj P.x) ≅
      (mapBothOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).obj
        ((mapBaseOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hH).obj P) := by
  let Q := (mapBothOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).obj
    ((mapBaseOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hH).obj P)
  let φ := homDiagonal hH Q P.iso.hom (by rfl)
  haveI : IsIso φ.hbase := by
    change IsIso (eqToHom Q.hx)
    infer_instance
  haveI : IsIso φ.a := by change IsIso (𝟙 _); infer_instance
  haveI : IsIso φ.b := by change IsIso P.iso.hom; infer_instance
  letI := isIso_of_components φ
  let e := asIso φ
  have ha : e.inv.a = 𝟙 _ := by
    have he := congrArg Hom.a e.hom_inv_id
    change 𝟙 _ ≫ e.inv.a = 𝟙 _ at he
    exact (Category.id_comp _).symm.trans he
  have hb : e.inv.b = P.iso.inv := by
    have he := congrArg Hom.b e.hom_inv_id
    change P.iso.hom ≫ e.inv.b = 𝟙 _ at he
    exact (cancel_epi P.iso.hom).mp (he.trans P.iso.hom_inv_id.symm)
  exact
    { hom := φ
      inv := { hbase := e.inv.hbase
               a := 𝟙 _
               b := P.iso.inv
               ha := by rw [← ha]; exact e.inv.ha
               hb := by rw [← hb]; exact e.inv.hb
               w := by rw [← ha, ← hb]; exact e.inv.w }
      hom_inv_id := Hom.ext' (Category.id_comp _) P.iso.hom_inv_id
      inv_hom_id := Hom.ext' (Category.id_comp _) P.iso.inv_hom_id }

/-- The 2-cell `π ⋙ Δ_{𝒵/𝒯} ≅ Θ ⋙ ρ` filling the square, over `𝒞`. -/
noncomputable def relativeDiagonalSquareIsoOverSymm :
    (toBaseOver p𝒳 p𝒴 p𝒵 F G ⋙ diagonal hH) ≅
      (mapBaseOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hH ⋙
        mapBothOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG) := by
  refine NatIso.ofComponents
    (relativeDiagonalSquareObjectIsoOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH) ?_
  intro P P' φ
  apply Hom.ext'
  · change F.map φ.a ≫ 𝟙 _ = 𝟙 _ ≫ F.map φ.a
    simp
  · change F.map φ.a ≫ P'.iso.hom = P.iso.hom ≫ G.map φ.b
    exact φ.w

/-- Every component of
`CategoryTheory.TwoFibreProductOver.relativeDiagonalSquareIsoOverSymm` is vertical: its base
morphism lies over the identity. -/
instance isHomLift_relativeDiagonalSquareIsoOverSymm
    (Q : TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G) :
    (structureFunctor p𝒵 p𝒵 p𝒯 H H).IsHomLift
      (𝟙 ((structureFunctor p𝒳 p𝒴 p𝒵 F G).obj Q))
      ((relativeDiagonalSquareIsoOverSymm p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).hom.app Q) := by
  have hsource : p𝒵.obj (F.obj Q.x) = Q.base :=
    (Functor.congr_obj hF Q.x).trans Q.hx
  have htarget :
      (structureFunctor p𝒵 p𝒵 p𝒯 H H).obj
          ((mapBaseOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hH ⋙
            mapBothOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).obj Q) = Q.base := rfl
  apply IsHomLift.of_fac'
    (structureFunctor p𝒵 p𝒵 p𝒯 H H) (𝟙 Q.base)
    ((relativeDiagonalSquareIsoOverSymm p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).hom.app Q)
    hsource htarget
  change (homDiagonal hH
    ((mapBothOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG).obj
      ((mapBaseOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hH).obj Q)) Q.iso.hom (by rfl)).hbase = _
  change eqToHom hsource = _
  change eqToHom hsource =
    eqToHom hsource ≫ 𝟙 Q.base ≫ eqToHom (rfl : Q.base = Q.base)
  simp

/-- The 2-cell `Θ ⋙ ρ ≅ π ⋙ Δ_{𝒵/𝒯}` filling the square, over `𝒞`. -/
noncomputable def relativeDiagonalSquareIsoOver :
    (mapBaseOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hH ⋙
        mapBothOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG) ≅
      (toBaseOver p𝒳 p𝒴 p𝒵 F G ⋙ diagonal hH) :=
  (relativeDiagonalSquareIsoOverSymm p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).symm

/-- Every component of
`CategoryTheory.TwoFibreProductOver.relativeDiagonalSquareIsoOver` is vertical. -/
theorem isHomLift_relativeDiagonalSquareIsoOver
    (Q : TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G) :
    (structureFunctor p𝒵 p𝒵 p𝒯 H H).IsHomLift
      (𝟙 ((structureFunctor p𝒳 p𝒴 p𝒵 F G).obj Q))
      ((relativeDiagonalSquareIsoOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).hom.app Q) := by
  have : (structureFunctor p𝒵 p𝒵 p𝒯 H H).IsHomLift
      (𝟙 ((structureFunctor p𝒳 p𝒴 p𝒵 F G).obj Q))
      ((relativeDiagonalSquareIsoOverSymm p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).app Q).hom :=
    isHomLift_relativeDiagonalSquareIsoOverSymm p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH Q
  exact IsHomLift.lift_id_inv (structureFunctor p𝒵 p𝒵 p𝒯 H H) _
    ((relativeDiagonalSquareIsoOverSymm p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).app Q)


/-! ### the comparison into the 2-fibre product of the cospan -/

/-- The comparison 1-morphism `𝒳 ×_𝒵 𝒴 ⥤ (𝒳 ×_𝒯 𝒴) ×_{𝒵 ×_𝒯 𝒵} 𝒵` induced by the square
`(Θ, π, σ)`: on objects it sends `(U, x, y, φ)` to `((U, x, y, H φ), F x, (𝟙, φ⁻¹))`. -/
noncomputable def toRelativeDiagonalPullbackOver :
    TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G ⥤
      TwoFibreProductOver
        (structureFunctor p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)) p𝒵
        (structureFunctor p𝒵 p𝒵 p𝒯 H H)
        (mapBothOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG) (diagonal hH) :=
  lift _ _ _ _ _ (structureFunctor p𝒳 p𝒴 p𝒵 F G)
    (mapBaseOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hH) (toBaseOver p𝒳 p𝒴 p𝒵 F G)
    (mapBaseOver_comp_structureFunctor p𝒳 p𝒴 p𝒵 p𝒯 F G H hH)
    (toBaseOver_comp_p p𝒳 p𝒴 p𝒵 F G hF)
    (relativeDiagonalSquareIsoOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH)
    (isHomLift_relativeDiagonalSquareIsoOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH)

attribute [local implicit_reducible] mapBaseOver mapBothOver toBaseOver
  CategoryTheory.TwoFibreProductOver.diagonal CategoryTheory.TwoFibreProductOver.lift

/-- `CategoryTheory.TwoFibreProductOver.toRelativeDiagonalPullbackOver` is strictly a
1-morphism over `𝒞`. -/
theorem toRelativeDiagonalPullbackOver_comp_structureFunctor :
    toRelativeDiagonalPullbackOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH ⋙
        structureFunctor (structureFunctor p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)) p𝒵
          (structureFunctor p𝒵 p𝒵 p𝒯 H H)
          (mapBothOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG) (diagonal hH) =
      structureFunctor p𝒳 p𝒴 p𝒵 F G :=
  lift_comp_structureFunctor ..

/-- `CategoryTheory.TwoFibreProductOver.toRelativeDiagonalPullbackOver` is faithful. -/
instance faithful_toRelativeDiagonalPullbackOver :
    (toRelativeDiagonalPullbackOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).Faithful where
  map_injective {_ _} _ _ hk :=
    Hom.ext' (congrArg (fun q => q.a.a) hk) (congrArg (fun q => q.a.b) hk)

set_option backward.isDefEq.respectTransparency false in
/-- `CategoryTheory.TwoFibreProductOver.toRelativeDiagonalPullbackOver` is full. -/
instance full_toRelativeDiagonalPullbackOver :
    (toRelativeDiagonalPullbackOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).Full := by
  constructor
  intro P Q φ
  have hw₁ := congrArg (fun q => q.a) φ.w
  have h₁ : F.map φ.a.a = φ.b := by
    change F.map φ.a.a ≫ 𝟙 _ = 𝟙 _ ≫ φ.b at hw₁
    simpa using hw₁
  have h₂ : G.map φ.a.b ≫ Q.iso.inv = P.iso.inv ≫ φ.b := congrArg (fun q => q.b) φ.w
  have hw₂' : G.map φ.a.b ≫ Q.iso.inv = P.iso.inv ≫ F.map φ.a.a := by
    simpa [h₁] using h₂
  let k : P ⟶ Q :=
    { hbase := φ.a.hbase
      a := φ.a.a
      b := φ.a.b
      ha := φ.a.ha
      hb := φ.a.hb
      w := by
        calc
          F.map φ.a.a ≫ Q.iso.hom =
              (P.iso.hom ≫ P.iso.inv) ≫ F.map φ.a.a ≫ Q.iso.hom := by simp
          _ = P.iso.hom ≫ (P.iso.inv ≫ F.map φ.a.a) ≫ Q.iso.hom := by
            simp only [Category.assoc]
          _ = P.iso.hom ≫ (G.map φ.a.b ≫ Q.iso.inv) ≫ Q.iso.hom := by
            rw [← hw₂']
          _ = P.iso.hom ≫ G.map φ.a.b := by simp [Category.assoc] }
  exact ⟨k, Hom.ext' (Hom.ext' rfl rfl) h₁⟩

set_option backward.isDefEq.respectTransparency false in
/-- `CategoryTheory.TwoFibreProductOver.toRelativeDiagonalPullbackOver` is essentially
surjective. -/
instance essSurj_toRelativeDiagonalPullbackOver :
    (toRelativeDiagonalPullbackOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).EssSurj := by
  constructor
  intro P
  rw [Functor.essImage]
  let L := toRelativeDiagonalPullbackOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH
  let e₁ : F.obj P.x.x ≅ P.y := (fst p𝒵 p𝒵 p𝒯 H H).mapIso P.iso
  let e₂ : G.obj P.x.y ≅ P.y := (snd p𝒵 p𝒵 p𝒯 H H).mapIso P.iso
  let bIso : P.x.base ≅ p𝒵.obj P.y := (structureFunctor p𝒵 p𝒵 p𝒯 H H).mapIso P.iso
  let q : TwoFibreProductOver p𝒳 p𝒴 p𝒵 F G :=
    { base := P.x.base
      x := P.x.x
      y := P.x.y
      hx := P.x.hx
      hy := P.x.hy
      iso := e₁ ≪≫ e₂.symm
      vertical := by
        have h₁ : p𝒵.IsHomLift bIso.hom e₁.hom := P.iso.hom.ha
        have h₂ : p𝒵.IsHomLift bIso.hom e₂.hom := P.iso.hom.hb
        have h₃ : p𝒵.IsHomLift bIso.inv e₂.inv := IsHomLift.inv_lift_inv p𝒵 bIso e₂
        have hv : p𝒵.IsHomLift (bIso.hom ≫ bIso.inv) (e₁.hom ≫ e₂.inv) := inferInstance
        simpa [bIso.hom_inv_id] using hv }
  have hw := P.iso.hom.w
  simp only [mapBothOver, diagonal, Iso.refl_hom, Category.comp_id] at hw
  have hPiso : P.x.iso.hom = H.map (e₁.hom ≫ e₂.inv) := by
    rw [Functor.map_comp, show e₁.hom = P.iso.hom.a from rfl, hw, Category.assoc,
      ← Functor.map_comp, show (P.iso.hom.b : _) = e₂.hom from rfl, e₂.hom_inv_id]
    simp
  let a : (L.obj q).x ⟶ P.x :=
    { hbase := eqToHom (rfl : P.x.base = P.x.base)
      a := 𝟙 P.x.x
      b := 𝟙 P.x.y
      ha := IsHomLift.id q.hx
      hb := IsHomLift.id q.hy
      w := by
        have h1 : F.map (𝟙 P.x.x) = 𝟙 (F.obj P.x.x) := F.map_id P.x.x
        have h2 : G.map (𝟙 P.x.y) = 𝟙 (G.obj P.x.y) := G.map_id P.x.y
        have h3 : H.map (𝟙 (F.obj P.x.x)) = 𝟙 (H.obj (F.obj P.x.x)) := H.map_id _
        have h4 : H.map (𝟙 (G.obj P.x.y)) = 𝟙 (H.obj (G.obj P.x.y)) := H.map_id _
        simp only [Functor.comp_map, h1, h2, h3, h4]
        exact (Category.id_comp _).trans (hPiso.trans (Category.comp_id _).symm) }
  have haIso : IsIso a := by
    apply isIso_of_isIso_components _ _ _ _ _ a
    · change IsIso (𝟙 P.x.x); infer_instance
    · change IsIso (𝟙 P.x.y); infer_instance
  have hvert : (structureFunctor p𝒵 p𝒵 p𝒯 H H).IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  have hbh : P.iso.hom.hbase = eqToHom P.hx ≫ eqToHom P.hy.symm := by
    have hh := IsHomLift.fac' (structureFunctor p𝒵 p𝒵 p𝒯 H H) (𝟙 P.base) P.iso.hom
    rw [Category.id_comp] at hh
    exact hh
  let θ : L.obj q ⟶ P := Hom.mk' a e₁.hom
    (by
      have hlift2 : p𝒵.IsHomLift (eqToHom P.hx ≫ eqToHom P.hy.symm) e₁.hom :=
        hbh ▸ P.iso.hom.ha
      rw [IsHomLift.fac' p𝒵 (eqToHom P.hx ≫ eqToHom P.hy.symm) e₁.hom]
      simp only [a, structureFunctor_map, eqToHom_trans])
    (by
      apply Hom.ext'
      · change F.map (𝟙 P.x.x) ≫ P.iso.hom.a = 𝟙 _ ≫ e₁.hom
        simp [e₁]
      · have hInvA : P.iso.inv.a ≫ P.iso.hom.a = 𝟙 P.y := e₁.inv_hom_id
        change G.map (𝟙 P.x.y) ≫ P.iso.hom.b =
          (P.iso.hom.b ≫ P.iso.inv.a) ≫ e₁.hom
        calc
          G.map (𝟙 P.x.y) ≫ P.iso.hom.b = P.iso.hom.b := by simp
          _ = (P.iso.hom.b ≫ P.iso.inv.a) ≫ e₁.hom := by
            rw [show e₁.hom = P.iso.hom.a from rfl, Category.assoc, hInvA]
            exact (Category.comp_id _).symm)
  have hθ : IsIso θ := isIso_of_isIso_components _ _ _ _ _ θ haIso (by
    change IsIso e₁.hom; infer_instance)
  exact ⟨q, ⟨@asIso _ _ _ _ θ hθ⟩⟩

/-- The square

```text
          Θ
  𝒳 ×_𝒵 𝒴  ---->  𝒳 ×_𝒯 𝒴
    |                 |
  π |                 | ρ
    v                 v
    𝒵  --Δ_{𝒵/𝒯}-->  𝒵 ×_𝒯 𝒵
```

of categories over `𝒞` is 2-cartesian: the comparison functor into the 2-fibre product of the
cospan `(ρ, Δ_{𝒵/𝒯})` is an equivalence of categories. -/
theorem isEquivalence_toRelativeDiagonalPullbackOver :
    (toRelativeDiagonalPullbackOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH).IsEquivalence :=
  { faithful := faithful_toRelativeDiagonalPullbackOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH
    full := full_toRelativeDiagonalPullbackOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH
    essSurj := essSurj_toRelativeDiagonalPullbackOver p𝒳 p𝒴 p𝒵 p𝒯 F G H hF hG hH }

/-- Extensionality for a point of the 2-fibre product over `𝒞` in terms of its base, its two
components and its comparison isomorphism. -/
theorem twoFibreProductOver_ext
    {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒯 (F ⋙ H) (G ⋙ H)}
    (hbase : P.base = Q.base) (hx : P.x = Q.x) (hy : P.y = Q.y)
    (hiso : HEq P.iso Q.iso) : P = Q := by
  cases P; cases Q
  cases hbase; cases hx; cases hy; cases hiso
  rfl

end Both

section DiagonalComp

variable (hF : F ⋙ p𝒵 = p𝒳) (hH : H ⋙ p𝒯 = p𝒵) (hFH : (F ⋙ H) ⋙ p𝒯 = p𝒳)

set_option backward.isDefEq.respectTransparency false in
/-- **The diagonal of a composite factors through the diagonal of the first factor.** For
1-morphisms `F : 𝒳 ⥤ 𝒵` and `H : 𝒵 ⥤ 𝒯` of categories over `𝒞`,

    Δ_{𝒳/𝒯} = Δ_{𝒳/𝒵} ⋙ Θ,

where `Θ = CategoryTheory.TwoFibreProductOver.mapBaseOver` is the comparison
`𝒳 ×_𝒵 𝒳 ⥤ 𝒳 ×_𝒯 𝒳`. -/
theorem diagonal_comp_mapBaseOver :
    diagonal hFH = diagonal hF ⋙ mapBaseOver p𝒳 p𝒳 p𝒵 p𝒯 F F H hH := by
  have hobj : ∀ x, (diagonal hFH).obj x =
      (diagonal hF ⋙ mapBaseOver p𝒳 p𝒳 p𝒵 p𝒯 F F H hH).obj x := fun x =>
    twoFibreProductOver_ext p𝒳 p𝒳 p𝒯 F F H rfl rfl rfl
      (heq_of_eq (Functor.mapIso_refl H _).symm)
  refine Functor.ext hobj ?_
  intro x y φ
  apply Hom.ext' <;> simp [mapBaseOver, diagonal]

end DiagonalComp



end CategoryTheory.TwoFibreProductOver

end
