module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# Functoriality of the finite Hilbert stacks

Let
```
  𝒳' --G--> 𝒳
   |         |
   F'        F
   v         v
  𝒴' --H--> 𝒴
```
be a 2-commutative diagram of stacks in groupoids over the big fppf site `(Sch/S)_fppf`, with the
2-commutativity witnessed by a 2-isomorphism `γ : H ∘ F' ⟶ F ∘ G`. Stacks 05XN produces from this
datum a canonical 1-morphism `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of degree-`d` finite Hilbert stacks,
compatible with the forgetful 1-morphisms of the diagram of Stacks 05WD. On objects it sends
`(U, Z, y, x, α)` to `(U, Z, H y, G x, γ ⋆ 1_H ⋆ α)` and on morphisms it sends `(f, g, b, a)` to
`(f, g, H b, G a)`.

## Main definitions

* `AlgebraicGeometry.Stack.mapRelative`: **Stacks 05XN**, the canonical 1-morphism
  `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)`.
* `AlgebraicGeometry.Stack.mapAbsolute`: the 1-morphism `ℋ_d(𝒳') ⟶ ℋ_d(𝒳)` induced by `G`, which
  is the same construction for the square whose columns are the structure morphisms of `𝒳'` and
  `𝒳`.
* `AlgebraicGeometry.Stack.squareComparison`: the component of the inverse of the given
  2-isomorphism, as a morphism `F (G x) ⟶ H (F' x)`.
* `AlgebraicGeometry.Stack.sourceSquare` and `AlgebraicGeometry.Stack.hilbertSquare`: the given
  square and the induced square of finite Hilbert categories, as squares in the 2-category of
  categories fibred in groupoids over the site.
* `AlgebraicGeometry.Stack.hilbertComparison`: the comparison functor from `ℋ_d(𝒳'/𝒴')` to the
  2-fibre product `𝒴' ×_𝒴 ℋ_d(𝒳/𝒴)`.

## Main results

* `AlgebraicGeometry.Stack.mapRelative_comp_forgetRelativeStructure`,
  `AlgebraicGeometry.Stack.mapRelative_comp_forgetTarget`,
  `AlgebraicGeometry.Stack.mapRelative_comp_forgetRelativeToFiniteCover` and
  `AlgebraicGeometry.Stack.mapAbsolute_comp_forgetAbsoluteStructure`: compatibility of the two
  induced 1-morphisms with each of the four forgetful 1-morphisms of Stacks 05WD.
* `AlgebraicGeometry.Stack.mapRelative_obj_α`: the induced 1-morphism transports the
  identification of an object across the given 2-isomorphism.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_hilbertSquare`: **Stacks 05XP**, a 2-cartesian
  square induces a 2-cartesian square of degree-`d` finite Hilbert stacks over the two targets.
* `AlgebraicGeometry.Stack.isEquivalence_hilbertComparison`: the comparison functor to the
  2-fibre product is an equivalence as soon as the one for the given square is.

## References

* [Stacks Project, Tag 05XN](https://stacks.math.columbia.edu/tag/05XN)
* [Stacks Project, Tag 05XP](https://stacks.math.columbia.edu/tag/05XP)
* [Stacks Project, Tag 003E](https://stacks.math.columbia.edu/tag/003E)
* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
-/

@[expose] public section

open CategoryTheory

universe u w v₁ u₁ v₂ u₂

namespace AlgebraicGeometry.Stack

section Comparison

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳' 𝒴' : StackInGroupoids.{w, u, v₁, u + 1, u₁} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F' : 𝒳'.toBasedCategory ⥤ᵇ 𝒴'.toBasedCategory}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}
  {G : 𝒳'.toBasedCategory ⥤ᵇ 𝒳.toBasedCategory}
  {H : 𝒴'.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- The component at an object `x` of `𝒳'` of the inverse of a 2-isomorphism
`γ : H ∘ F' ⟶ F ∘ G`, as a morphism `F (G x) ⟶ H (F' x)` of `𝒴`. It is `γ.inv.app x`. -/
def squareComparison (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    (x : 𝒳'.toBasedCategory.obj) : F.obj (G.obj x) ⟶ H.obj (F'.obj x) :=
  γ.inv.app x

/-- Naturality of the comparison morphisms of a 2-commutative square. -/
theorem squareComparison_naturality (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    {x y : 𝒳'.toBasedCategory.obj} (f : x ⟶ y) :
    F.map (G.map f) ≫ squareComparison γ y = squareComparison γ x ≫ H.map (F'.map f) :=
  γ.inv.naturality f

/-- The comparison morphisms of a 2-commutative square of stacks in groupoids lie over
identities. -/
theorem isHomLift_squareComparison (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    {x : 𝒳'.toBasedCategory.obj} {U : BigFppfOver B S hS}
    (hx : 𝒳'.toBasedCategory.p.obj x = U) :
    𝒴.toBasedCategory.p.IsHomLift (𝟙 U) (squareComparison γ x) :=
  γ.inv.isHomLift hx

end Comparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ)
  (𝒳' 𝒴' : StackInGroupoids.{w, u, v₁, u + 1, u₁} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS))
  (𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS))
  (F' : 𝒳'.toBasedCategory ⥤ᵇ 𝒴'.toBasedCategory)
  (F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory)
  (G : 𝒳'.toBasedCategory ⥤ᵇ 𝒳.toBasedCategory)
  (H : 𝒴'.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory)

/-! ### The absolute finite Hilbert stacks are functorial -/

/-- The functor underlying the 1-morphism `ℋ_d(𝒳') ⟶ ℋ_d(𝒳)` induced by a 1-morphism
`G : 𝒳' ⟶ 𝒳` of stacks in groupoids: it applies `G` to the object lying over the cover. -/
def mapAbsoluteFunctor :
    AbsoluteHilbert.Object B S hS d 𝒳' ⥤ AbsoluteHilbert.Object B S hS d 𝒳 where
  obj P :=
    { toFiniteCover := P.toFiniteCover
      x := G.obj P.x
      x_over := (G.w_obj P.x).trans P.x_over }
  map φ :=
    { cover := φ.cover
      a := G.map φ.a
      a_over := (BasedFunctor.isHomLift_iff G φ.cover.g φ.a).2 φ.a_over }
  map_id P := AbsoluteHilbert.Hom.ext rfl (G.map_id P.x)
  map_comp φ ψ := AbsoluteHilbert.Hom.ext rfl (G.map_comp φ.a ψ.a)

/-- The 1-morphism `ℋ_d(𝒳') ⟶ ℋ_d(𝒳)` of absolute degree-`d` finite Hilbert stacks induced by a
1-morphism `G : 𝒳' ⟶ 𝒳` of stacks in groupoids: the canonical 1-morphism of finite Hilbert
stacks for the 2-commutative square whose two columns are the structure morphisms of `𝒳'` and
`𝒳`. -/
@[stacks 05XN "the induced 1-morphism of absolute finite Hilbert stacks"]
def mapAbsolute :
    absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳') ⥤ᵇ
      absoluteHilbertCategory (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) where
  toFunctor := mapAbsoluteFunctor B S hS d 𝒳' 𝒳 G
  w := rfl

/-- The induced 1-morphism of absolute finite Hilbert stacks leaves the underlying degree-`d`
finite locally free cover unchanged. -/
@[stacks 05XN "compatibility with the forgetful 1-morphism `ℋ_d(𝒳) ⟶ ℋ_d`"]
theorem mapAbsolute_comp_forgetAbsoluteStructure :
    BasedFunctor.comp (mapAbsolute B S hS d 𝒳' 𝒳 G)
        (forgetAbsoluteStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳)) =
      forgetAbsoluteStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳') :=
  BasedCategory.BasedFunctor.ext' rfl

/-! ### The relative finite Hilbert stacks are functorial -/

variable (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)

/-- The functor underlying the canonical 1-morphism `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of Stacks 05XN: it
applies `H` to the object of `𝒴'`, applies `G` to the object of `𝒳'`, and transports the
identification across the given 2-isomorphism. -/
def mapRelativeFunctor :
    FiniteHilbert.Object B S hS 𝒳' 𝒴' F' d ⥤ FiniteHilbert.Object B S hS 𝒳 𝒴 F d where
  obj P :=
    { U := P.U
      Z := P.Z
      q := P.q
      finiteLocallyFree := P.finiteLocallyFree
      y := H.obj P.y
      y_over := (H.w_obj P.y).trans P.y_over
      x := G.obj P.x
      x_over := (G.w_obj P.x).trans P.x_over
      α := squareComparison γ P.x ≫ H.map P.α
      α_over := by
        have h₁ := isHomLift_squareComparison γ (𝒴 := 𝒴) P.x_over
        have h₂ : 𝒴.toBasedCategory.p.IsHomLift P.q (H.map P.α) :=
          (BasedFunctor.isHomLift_iff H P.q P.α).2 P.α_over
        infer_instance }
  map {P Q} φ :=
    { f := φ.f
      g := φ.g
      square := φ.square
      b := H.map φ.b
      b_over := (BasedFunctor.isHomLift_iff H φ.f φ.b).2 φ.b_over
      a := G.map φ.a
      a_over := (BasedFunctor.isHomLift_iff G φ.g φ.a).2 φ.a_over
      compatible := by
        have hcompat : H.map (F'.map φ.a) ≫ H.map Q.α = H.map P.α ≫ H.map φ.b := by
          simpa only [Functor.map_comp] using congrArg H.map φ.compatible
        change F.map (G.map φ.a) ≫ squareComparison γ Q.x ≫ H.map Q.α =
          (squareComparison γ P.x ≫ H.map P.α) ≫ H.map φ.b
        rw [← Category.assoc, squareComparison_naturality γ φ.a, Category.assoc, hcompat,
          Category.assoc] }
  map_id P := FiniteHilbert.Hom.ext rfl rfl (H.map_id P.y) (G.map_id P.x)
  map_comp φ ψ := FiniteHilbert.Hom.ext rfl rfl (H.map_comp φ.b ψ.b) (G.map_comp φ.a ψ.a)

/-- The canonical 1-morphism `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of degree-`d` finite Hilbert stacks
attached to a 2-commutative square of stacks in groupoids with horizontal arrows `G` and `H`,
vertical arrows `F'` and `F`, and 2-isomorphism `γ : H ∘ F' ⟶ F ∘ G`. -/
@[stacks 05XN "the canonical 1-morphism"]
def mapRelative :
    finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳') (𝒴 := 𝒴') (F := F') (d := d) ⥤ᵇ
      finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) where
  toFunctor := mapRelativeFunctor B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ
  w := rfl

/-- The canonical 1-morphism sends an object with identification `α` to one whose identification
is `α` transported across the given 2-isomorphism. -/
@[stacks 05XN "action on the identification"]
theorem mapRelative_obj_α (P : FiniteHilbert.Object B S hS 𝒳' 𝒴' F' d) :
    ((mapRelative B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).obj P).α =
      squareComparison γ P.x ≫ H.map P.α :=
  rfl

/-- The canonical 1-morphism is compatible with the forgetful 1-morphisms to the absolute finite
Hilbert stacks: on them it induces the 1-morphism attached to `G`. -/
@[stacks 05XN "compatibility with the forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)`"]
theorem mapRelative_comp_forgetRelativeStructure :
    BasedFunctor.comp (mapRelative B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ)
        (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
          (F := F)) =
      BasedFunctor.comp
        (forgetRelativeStructure (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳') (𝒴 := 𝒴')
          (F := F'))
        (mapAbsolute B S hS d 𝒳' 𝒳 G) :=
  BasedCategory.BasedFunctor.ext' rfl

/-- The canonical 1-morphism is compatible with the forgetful 1-morphisms to the target stacks: on
them it induces `H`. -/
@[stacks 05XN "compatibility with the forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ 𝒴`"]
theorem mapRelative_comp_forgetTarget :
    BasedFunctor.comp (mapRelative B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ)
        (forgetTarget (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)) =
      BasedFunctor.comp
        (forgetTarget (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳') (𝒴 := 𝒴') (F := F')) H :=
  BasedCategory.BasedFunctor.ext' rfl

/-- The canonical 1-morphism leaves the underlying degree-`d` finite locally free cover
unchanged. -/
@[stacks 05XN "compatibility with the forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d`"]
theorem mapRelative_comp_forgetRelativeToFiniteCover :
    BasedFunctor.comp (mapRelative B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ)
        (forgetRelativeToFiniteCover (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
          (F := F)) =
      forgetRelativeToFiniteCover (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳') (𝒴 := 𝒴')
        (F := F') :=
  BasedCategory.BasedFunctor.ext' rfl

/-! ### Base change of the relative finite Hilbert stacks -/

section Cartesian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ)
  (𝒳' 𝒴' 𝒳 𝒴 : StackInGroupoids.{w, u, max u v₁, u + 1, max (u + 1) (max v₁ v₂)}
    (BigFppfOver B S hS) (BigFppfOver.topology B S hS))
  (F' : 𝒳'.toBasedCategory ⥤ᵇ 𝒴'.toBasedCategory)
  (F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory)
  (G : 𝒳'.toBasedCategory ⥤ᵇ 𝒳.toBasedCategory)
  (H : 𝒴'.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory)
  (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)

/-- A stack in groupoids over the big fppf site of `S`, read as an object of the 2-category of
categories fibred in groupoids over that site. -/
abbrev toCatFiberedInGroupoids
    (𝒵 : StackInGroupoids.{w, u, max u v₁, u + 1, max (u + 1) (max v₁ v₂)}
      (BigFppfOver B S hS) (BigFppfOver.topology B S hS)) :
    CatFiberedInGroupoids.{u, max u v₁, u + 1, max (u + 1) (max v₁ v₂)} (BigFppfOver B S hS) :=
  ⟨𝒵.toBasedCategory, 𝒵.isStackInGroupoids.isFiberedInGroupoids⟩

/-- The relative degree-`d` finite Hilbert category `ℋ_d(𝒜/ℬ)` of a 1-morphism of stacks in
groupoids, read as an object of the 2-category of categories fibred in groupoids over the big
fppf site. -/
noncomputable abbrev finiteHilbertCatFiberedInGroupoids
    (𝒜 ℬ : StackInGroupoids.{w, u, max u v₁, u + 1, max (u + 1) (max v₁ v₂)}
      (BigFppfOver B S hS) (BigFppfOver.topology B S hS))
    (f : 𝒜.toBasedCategory ⥤ᵇ ℬ.toBasedCategory) :
    CatFiberedInGroupoids.{u, max u v₁, u + 1, max (u + 1) (max v₁ v₂)} (BigFppfOver B S hS) :=
  ⟨finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒜) (𝒴 := ℬ) (F := f) (d := d),
    isFiberedInGroupoids_finiteHilbertProjection⟩

/-- The given 2-commutative square of stacks in groupoids, with horizontal arrows `G` and `H`,
vertical arrows `F'` and `F` and filler `γ`, read as a 2-commutative square over the cospan
`(F, H)` in the 2-category of categories fibred in groupoids. -/
def sourceSquare : Bicategory.TwoCommSq
    (Bicategory.InducedBicategory.mkHom (X := toCatFiberedInGroupoids B S hS 𝒳)
      (Y := toCatFiberedInGroupoids B S hS 𝒴) F)
    (Bicategory.InducedBicategory.mkHom (X := toCatFiberedInGroupoids B S hS 𝒴')
      (Y := toCatFiberedInGroupoids B S hS 𝒴) H) where
  pt := toCatFiberedInGroupoids B S hS 𝒳'
  fst := Bicategory.InducedBicategory.mkHom G
  snd := Bicategory.InducedBicategory.mkHom F'
  iso := Bicategory.InducedBicategory.isoMk γ.symm

/-- The 2-commutative square of finite Hilbert categories induced by the given square: its
horizontal arrow is the canonical 1-morphism `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of Stacks 05XN, its
vertical arrows are the two forgetful 1-morphisms to the target stacks, and its filler is the
compatibility of the two. -/
noncomputable def hilbertSquare : Bicategory.TwoCommSq
    (Bicategory.InducedBicategory.mkHom
      (X := finiteHilbertCatFiberedInGroupoids B S hS d 𝒳 𝒴 F)
      (Y := toCatFiberedInGroupoids B S hS 𝒴)
      (forgetTarget (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)))
    (Bicategory.InducedBicategory.mkHom (X := toCatFiberedInGroupoids B S hS 𝒴')
      (Y := toCatFiberedInGroupoids B S hS 𝒴) H) where
  pt := finiteHilbertCatFiberedInGroupoids B S hS d 𝒳' 𝒴' F'
  fst := Bicategory.InducedBicategory.mkHom (mapRelative B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ)
  snd := Bicategory.InducedBicategory.mkHom
    (forgetTarget (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳') (𝒴 := 𝒴') (F := F'))
  iso := Bicategory.InducedBicategory.isoMk
    (eqToIso (mapRelative_comp_forgetTarget B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ))

/-- The comparison functor `𝒳' ⥤ 𝒳 ×_𝒴 𝒴'` into the 2-fibre product over the site attached to
the given square: it sends an object `x` to the triple `(G x, F' x, γ⁻¹ x)` and a morphism `a` to
the pair `(G a, F' a)`. -/
def sourceComparison : 𝒳'.toBasedCategory.obj ⥤
    TwoFibreProductOver 𝒳.toBasedCategory.p 𝒴'.toBasedCategory.p 𝒴.toBasedCategory.p
      F.toFunctor H.toFunctor :=
  TwoFibreProductOver.lift _ _ _ _ _ 𝒳'.toBasedCategory.p G.toFunctor F'.toFunctor
    G.w F'.w ((BasedNatTrans.forgetful _ _).mapIso γ.symm) γ.inv.isHomLift'

/-- The comparison functor `ℋ_d(𝒳'/𝒴') ⥤ ℋ_d(𝒳/𝒴) ×_𝒴 𝒴'` into the 2-fibre product over the
site attached to the induced square: it sends an object `P` to the triple consisting of its image
under the canonical 1-morphism of Stacks 05XN, its own object of `𝒴'`, and the identity
identification. -/
noncomputable def hilbertComparison :
    FiniteHilbert.Object B S hS 𝒳' 𝒴' F' d ⥤
      TwoFibreProductOver
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
        𝒴'.toBasedCategory.p 𝒴.toBasedCategory.p
        (forgetTarget (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
          (F := F)).toFunctor H.toFunctor :=
  TwoFibreProductOver.lift _ _ _ _ _ _
    (mapRelative B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).toFunctor
    (forgetTarget (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳') (𝒴 := 𝒴')
      (F := F')).toFunctor rfl
    (forgetTarget (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳') (𝒴 := 𝒴') (F := F')).w
    (Iso.refl _) (fun P => IsHomLift.id ((H.w_obj P.y).trans P.y_over))

attribute [local implicit_reducible] sourceComparison hilbertComparison mapRelative
  mapRelativeFunctor TwoFibreProductOver.lift forgetTarget finiteHilbertCategory
  BasedCategory.ofFunctor BasedFunctor.comp finiteHilbertProjection squareComparison

/-- If the given square is 2-cartesian, then its comparison functor is an equivalence. -/
theorem isEquivalence_sourceComparison
    (hcart : Bicategory.IsTwoFibreProduct (sourceSquare B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ)) :
    (sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).IsEquivalence :=
  Bicategory.isEquivalence_of_isTwoFibreProduct hcart
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _)
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare _ _
      (sourceSquare B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ))

/-- In a category fibred in groupoids, a morphism lying over an isomorphism of the base is itself
an isomorphism. -/
private theorem isIso_of_isHomLift_isIso {C E : Type*} [Category C] [Category E]
    (p : E ⥤ C) (hp : p.IsFiberedInGroupoids) {U V : C} (f : U ⟶ V)
    {x y : E} (a : x ⟶ y) [p.IsHomLift f a] [IsIso f] : IsIso a :=
  have := hp.isStronglyCartesian_homLift f a
  Functor.IsStronglyCartesian.isIso_of_base_isIso p f a

/-- In a category fibred in groupoids, two morphisms over the same base morphism that agree after
composing with a morphism `φ` are equal. -/
private theorem eq_of_comp_eq_of_isFiberedInGroupoids {C E : Type*} [Category C] [Category E]
    (p : E ⥤ C) (hp : p.IsFiberedInGroupoids) {R S R' : C} (f : R ⟶ S) (g : R' ⟶ R)
    {a b a' : E} (φ : a ⟶ b) [p.IsHomLift f φ] {ψ ψ' : a' ⟶ a} [p.IsHomLift g ψ]
    [p.IsHomLift g ψ'] (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' :=
  have := hp.isStronglyCartesian_homLift f φ
  Functor.IsStronglyCartesian.ext p f φ g h

/-- In a category fibred in groupoids, a morphism `φ'` lying over `g ≫ f` factors through a
morphism `φ` over `f` by a morphism lying over `g`. -/
private theorem exists_isHomLift_comp_eq {C E : Type*} [Category C] [Category E]
    (p : E ⥤ C) (hp : p.IsFiberedInGroupoids) {R S R' : C} (f : R ⟶ S) {g : R' ⟶ R} {f' : R' ⟶ S}
    (hf' : f' = g ≫ f) {a b a' : E} (φ : a ⟶ b) [p.IsHomLift f φ] (φ' : a' ⟶ b)
    [p.IsHomLift f' φ'] : ∃ c : a' ⟶ a, p.IsHomLift g c ∧ c ≫ φ = φ' :=
  have := hp.isStronglyCartesian_homLift f φ
  ⟨_, inferInstance, Functor.IsStronglyCartesian.fac p f φ hf' φ'⟩

/-- If the comparison functor of the given square is faithful, then so is the comparison functor
of the induced square. -/
theorem hilbertComparison_faithful
    (h : (sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).Faithful) :
    (hilbertComparison B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).Faithful := by
  constructor
  intro P Q φ ψ he
  have hf : φ.f = ψ.f := congrArg (fun t => t.a.f) he
  have hg : φ.g = ψ.g := congrArg (fun t => t.a.g) he
  have hb : φ.b = ψ.b := congrArg (fun t => t.b) he
  have ha : G.map φ.a = G.map ψ.a := congrArg (fun t => t.a.a) he
  apply FiniteHilbert.Hom.ext hf hg hb
  apply (sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).map_injective
  apply TwoFibreProductOver.Hom.ext' ha
  show F'.map φ.a = F'.map ψ.a
  have := Q.α_over
  have := φ.a_over
  have : 𝒳'.toBasedCategory.p.IsHomLift φ.g ψ.a := hg.symm ▸ ψ.a_over
  have : 𝒴'.toBasedCategory.p.IsHomLift φ.g (F'.map φ.a) := inferInstance
  have : 𝒴'.toBasedCategory.p.IsHomLift φ.g (F'.map ψ.a) := inferInstance
  refine eq_of_comp_eq_of_isFiberedInGroupoids _ 𝒴'.isStackInGroupoids.isFiberedInGroupoids
    Q.q φ.g Q.α ?_
  rw [φ.compatible, ψ.compatible, hb]

/-- If the comparison functor of the given square is full, then so is the comparison functor of
the induced square. -/
theorem hilbertComparison_full
    (h : (sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).Full) :
    (hilbertComparison B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).Full := by
  constructor
  intro P Q t
  dsimp only [hilbertComparison, TwoFibreProductOver.lift, mapRelative, mapRelativeFunctor,
    forgetTarget, finiteHilbertCategory, BasedCategory.ofFunctor, finiteHilbertProjection,
    Functor.comp_obj] at t
  have htf : t.a.f = t.hbase := by
    have hta : (finiteHilbertProjection (B := B) (S := S) (hS := hS)
        (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).IsHomLift t.hbase t.a := t.ha
    have hm := IsHomLift.fac'
      (finiteHilbertProjection (B := B) (S := S) (hS := hS)
        (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) t.hbase t.a
    change t.a.f = eqToHom _ ≫ t.hbase ≫ eqToHom _ at hm
    simpa using hm
  have htb : t.a.b = H.map t.b := by
    have hw := t.w
    change t.a.b ≫ 𝟙 _ = 𝟙 _ ≫ H.map t.b at hw
    simpa using hw
  have := t.a.a_over
  have := t.hb
  have hb : 𝒴'.toBasedCategory.p.IsHomLift t.a.f t.b := htf.symm ▸ t.hb
  have := P.α_over
  have := Q.α_over
  have hcomp : 𝒴'.toBasedCategory.p.IsHomLift (P.q ≫ t.a.f) (P.α ≫ t.b) := inferInstance
  have hs : P.q ≫ t.a.f = t.a.g ≫ Q.q := t.a.square.w.symm
  obtain ⟨c, hc, hcf⟩ := exists_isHomLift_comp_eq _
    𝒴'.isStackInGroupoids.isFiberedInGroupoids Q.q hs Q.α (P.α ≫ t.b)
  have hγP : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.Z) (squareComparison γ P.x) :=
    isHomLift_squareComparison γ P.x_over
  have hγQ : 𝒴.toBasedCategory.p.IsHomLift (𝟙 Q.Z) (squareComparison γ Q.x) :=
    isHomLift_squareComparison γ Q.x_over
  have hw : F.map t.a.a ≫ squareComparison γ Q.x = squareComparison γ P.x ≫ H.map c := by
    have hHα : 𝒴.toBasedCategory.p.IsHomLift Q.q (H.map Q.α) := inferInstance
    have : 𝒴.toBasedCategory.p.IsHomLift t.a.g (F.map t.a.a) := inferInstance
    have : 𝒴.toBasedCategory.p.IsHomLift t.a.g (H.map c) := inferInstance
    have : 𝒴.toBasedCategory.p.IsHomLift t.a.g (F.map t.a.a ≫ squareComparison γ Q.x) := by
      simpa using (inferInstance : 𝒴.toBasedCategory.p.IsHomLift
        (t.a.g ≫ 𝟙 Q.Z) (F.map t.a.a ≫ squareComparison γ Q.x))
    have : 𝒴.toBasedCategory.p.IsHomLift t.a.g (squareComparison γ P.x ≫ H.map c) := by
      simpa using (inferInstance : 𝒴.toBasedCategory.p.IsHomLift
        (𝟙 P.Z ≫ t.a.g) (squareComparison γ P.x ≫ H.map c))
    refine eq_of_comp_eq_of_isFiberedInGroupoids _ 𝒴.isStackInGroupoids.isFiberedInGroupoids
      Q.q t.a.g (H.map Q.α) ?_
    calc
      _ = F.map t.a.a ≫ (squareComparison γ Q.x ≫ H.map Q.α) := Category.assoc _ _ _
      _ = (squareComparison γ P.x ≫ H.map P.α) ≫ H.map t.b := by
        simpa only [htb] using t.a.compatible
      _ = (squareComparison γ P.x ≫ H.map c) ≫ H.map Q.α := by
        simp only [Category.assoc, ← H.map_comp, hcf]
  let m : (sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).obj P.x ⟶
      (sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).obj Q.x :=
    { hbase := eqToHom P.x_over ≫ t.a.g ≫ eqToHom Q.x_over.symm
      a := t.a.a
      b := c
      ha := by have := t.a.a_over; infer_instance
      hb := by have := hc; infer_instance
      w := hw }
  obtain ⟨a, ha⟩ := (sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).map_surjective m
  have haG : G.map a = t.a.a := congrArg (fun k => k.a) ha
  have haF : F'.map a = c := congrArg (fun k => k.b) ha
  have haBase : 𝒳'.toBasedCategory.p.map a =
      eqToHom P.x_over ≫ t.a.g ≫ eqToHom Q.x_over.symm :=
    congrArg (fun k => k.hbase) ha
  let φ : P ⟶ Q :=
    { f := t.a.f
      g := t.a.g
      square := t.a.square
      b := t.b
      b_over := hb
      a := a
      a_over := IsHomLift.of_fac' _ _ _ P.x_over Q.x_over haBase
      compatible := by rw [haF]; exact hcf }
  exact ⟨φ, TwoFibreProductOver.Hom.ext' (FiniteHilbert.Hom.ext rfl rfl htb.symm haG) rfl⟩

/-- If the comparison functor of the given square is an equivalence, then the comparison functor
of the induced square is essentially surjective. -/
theorem hilbertComparison_essSurj
    (h : (sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).IsEquivalence) :
    (hilbertComparison B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).EssSurj := by
  classical
  constructor
  intro t
  let P := t.x
  let q : P.Z ⟶ t.base := P.q ≫ eqToHom t.hx
  have := 𝒴'.isStackInGroupoids.isFiberedInGroupoids.isFibered
  let y := Functor.IsPreFibered.pullbackObj (p := 𝒴'.toBasedCategory.p) t.hy q
  let β : y ⟶ t.y := Functor.IsPreFibered.pullbackMap t.hy q
  have hy : 𝒴'.toBasedCategory.p.obj y = P.Z := Functor.IsPreFibered.pullbackObj_proj t.hy q
  have hβ : 𝒴'.toBasedCategory.p.IsHomLift q β := inferInstance
  have hHβ : 𝒴.toBasedCategory.p.IsHomLift q (H.map β) := inferInstance
  have hα : 𝒴.toBasedCategory.p.IsHomLift q P.α := by
    simpa only [q, IsHomLift.lift_comp_eqToHom_iff] using P.α_over
  have := t.vertical
  have hαβ : 𝒴.toBasedCategory.p.IsHomLift q (P.α ≫ t.iso.hom) := by
    simpa using (inferInstance : 𝒴.toBasedCategory.p.IsHomLift
      (q ≫ 𝟙 t.base) (P.α ≫ t.iso.hom))
  obtain ⟨c, hc, hcf⟩ := exists_isHomLift_comp_eq _ 𝒴.isStackInGroupoids.isFiberedInGroupoids
    q (Category.id_comp q).symm (H.map β) (P.α ≫ t.iso.hom)
  have hciso : IsIso c :=
    isIso_of_isHomLift_isIso _ 𝒴.isStackInGroupoids.isFiberedInGroupoids (𝟙 P.Z) c
  let R : TwoFibreProductOver 𝒳.toBasedCategory.p 𝒴'.toBasedCategory.p
      𝒴.toBasedCategory.p F.toFunctor H.toFunctor :=
    ⟨P.Z, P.x, y, P.x_over, hy, asIso c, hc⟩
  let pR := TwoFibreProductOver.structureFunctor 𝒳.toBasedCategory.p
    𝒴'.toBasedCategory.p 𝒴.toBasedCategory.p F.toFunctor H.toFunctor
  have hpR : pR.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
      𝒳.isStackInGroupoids.isFiberedInGroupoids
      𝒴'.isStackInGroupoids.isFiberedInGroupoids
      𝒴.isStackInGroupoids.isFiberedInGroupoids F.w H.w
  obtain ⟨x, hx, e, he⟩ := Functor.quasiInverse_choice 𝒳'.toBasedCategory.p pR
    𝒳'.isStackInGroupoids.isFiberedInGroupoids hpR
    (sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ) rfl h R
  change pR.IsHomLift (𝟙 P.Z) e.hom at he
  have hei : pR.IsHomLift (𝟙 P.Z) e.inv := by
    have := he
    simpa using IsHomLift.lift_id_inv_isIso pR P.Z e.hom
  have hea : 𝒳.toBasedCategory.p.IsHomLift (𝟙 P.Z) e.inv.a :=
    Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.fst_comp_eq _ e.inv
  have heb : 𝒴'.toBasedCategory.p.IsHomLift (𝟙 P.Z) e.inv.b :=
    Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.snd_comp_eq _ e.inv
  let Q : FiniteHilbert.Object B S hS 𝒳' 𝒴' F' d :=
    { U := P.U
      Z := P.Z
      q := P.q
      finiteLocallyFree := P.finiteLocallyFree
      y := t.y
      y_over := t.hy.trans t.hx.symm
      x := x
      x_over := hx
      α := e.inv.b ≫ β
      α_over := by
        have hh : 𝒴'.toBasedCategory.p.IsHomLift q (e.inv.b ≫ β) := by
          simpa using (inferInstance : 𝒴'.toBasedCategory.p.IsHomLift
            (𝟙 P.Z ≫ q) (e.inv.b ≫ β))
        simpa only [q, IsHomLift.lift_comp_eqToHom_iff] using hh }
  have htinv : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) t.iso.inv := by
    rw [show P.U = t.base from t.hx]
    infer_instance
  let φ : (mapRelative B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).obj Q ⟶ P :=
    { f := 𝟙 P.U
      g := 𝟙 P.Z
      square := CategoryTheory.IsPullback.id_horiz P.q
      b := t.iso.inv
      b_over := htinv
      a := e.inv.a
      a_over := hea
      compatible := by
        have hw : F.map e.inv.a ≫ c = squareComparison γ x ≫ H.map e.inv.b := e.inv.w
        show F.map e.inv.a ≫ P.α =
          (squareComparison γ x ≫ H.map (e.inv.b ≫ β)) ≫ t.iso.inv
        rw [H.map_comp, ← Category.assoc (squareComparison γ x), ← hw]
        simp only [Category.assoc, hcf, Iso.hom_inv_id, Category.comp_id] }
  have hφ : (finiteHilbertCategory (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p.IsHomLift (𝟙 P.U) φ :=
    IsHomLift.of_fac' _ _ _ rfl rfl (by
      show (𝟙 P.U) = eqToHom (rfl : P.U = P.U) ≫ 𝟙 P.U ≫ eqToHom rfl
      simp)
  have hφiso : IsIso φ :=
    isIso_of_isHomLift_isIso (finiteHilbertCategory (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
      isFiberedInGroupoids_finiteHilbertProjection (𝟙 P.U) φ
  let m : (hilbertComparison B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).obj Q ⟶ t :=
    { hbase := eqToHom t.hx
      a := φ
      b := 𝟙 t.y
      ha := by
        have hh : (finiteHilbertCategory (B := B) (S := S) (hS := hS)
            (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p.IsHomLift
            (𝟙 P.U ≫ eqToHom t.hx) φ := inferInstance
        simpa using hh
      hb := by
        have : 𝒴'.toBasedCategory.p.IsHomLift (𝟙 t.base) (𝟙 t.y) := IsHomLift.id t.hy
        have hh : 𝒴'.toBasedCategory.p.IsHomLift
            (eqToHom t.hx ≫ 𝟙 t.base) (𝟙 t.y) := inferInstance
        simpa using hh
      w := by change t.iso.inv ≫ t.iso.hom = 𝟙 _ ≫ H.map (𝟙 t.y); simp }
  have : IsIso m.a := hφiso
  have : IsIso m.b := by change IsIso (𝟙 t.y); infer_instance
  have : IsIso m := TwoFibreProductOver.isIso_of_components m
  exact ⟨Q, ⟨asIso m⟩⟩

/-- If the comparison functor of the given square is an equivalence, then so is the comparison
functor `ℋ_d(𝒳'/𝒴') ⥤ ℋ_d(𝒳/𝒴) ×_𝒴 𝒴'` of the induced square. -/
@[stacks 05XP "the comparison functor is an equivalence"]
theorem isEquivalence_hilbertComparison
    (h : (sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).IsEquivalence) :
    (hilbertComparison B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).IsEquivalence := by
  have := hilbertComparison_faithful B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ h.faithful
  have := hilbertComparison_full B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ h.full
  have := hilbertComparison_essSurj B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ h
  exact Functor.IsEquivalence.mk

/-- If the given 2-commutative square of stacks in groupoids is 2-cartesian, then so is the
induced square of degree-`d` finite Hilbert stacks: the canonical 1-morphism
`ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` and the forgetful 1-morphism `ℋ_d(𝒳'/𝒴') ⟶ 𝒴'` exhibit `ℋ_d(𝒳'/𝒴')`
as the 2-fibre product `𝒴' ×_𝒴 ℋ_d(𝒳/𝒴)`. -/
@[stacks 05XP]
noncomputable def isTwoFibreProduct_hilbertSquare
    (hcart : Bicategory.IsTwoFibreProduct (sourceSquare B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ)) :
    Bicategory.IsTwoFibreProduct (hilbertSquare B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare _ _)
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare _ _
      (hilbertSquare B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ))
    (isEquivalence_hilbertComparison B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ
      (isEquivalence_sourceComparison B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ hcart))

end Cartesian

end AlgebraicGeometry.Stack

end
