module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverChangeOfBase

/-!
# Comparing the 2-fibre products of a cospan over two bases (Stacks 050H)

Let `f : 𝒳 ⟶ 𝒵`, `g : 𝒴 ⟶ 𝒵` and `h : 𝒵 ⟶ 𝒯` be 1-morphisms of algebraic stacks over a scheme
`S` in a big fppf site `B`. Composing with `h` turns the cospan `(f, g)` into a cospan over `𝒯`,
and there is a canonical 1-morphism

```text
  i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴.
```

Stacks 050H describes `i`, and its whole content is one geometric fact: **`i` is a base change of
the relative diagonal `Δ_{𝒵/𝒯}`**, along the 1-morphism `𝒳 ×_𝒯 𝒴 ⟶ 𝒵 ×_𝒯 𝒵` which applies `f` to
the first factor and `g` to the second. This file constructs that square; once it is known to be
a 2-fibre product, every clause of Stacks 050H is read off it by Stacks 0302 and Stacks 045C.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.mapBase`: the 1-morphism `i`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.mapCospan`: the 1-morphism `𝒳 ×_𝒯 𝒴 ⟶ 𝒵 ×_𝒯 𝒵`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseSquare`: the 2-commutative square exhibiting
  `i` as a base change of `Δ_{𝒵/𝒯}`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseNatIso`: the natural isomorphism of underlying
  functors that fills it.
* `AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseLift` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseLiftCone`: the mediating 1-morphism of a test
  square and its two comparison 2-isomorphisms.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isHomLift_mapBaseNatIso_app`: the 2-cell filling that
  square is a 2-morphism of the 2-category, i.e. its components are vertical.
* `AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseLiftCone_rel`: the mediating morphism of
  2-commutative squares is the only one, up to the 2-cell equivalence of Stacks 003O.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_mapBaseSquare`: **Stacks 050H**, the
  geometric content — the square is a 2-fibre product, i.e. `i` is a base change of `Δ_{𝒵/𝒯}`.

## Implementation notes

The square is built in the 2-category of categories fibred in groupoids, which is where
Stacks 0302 (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`) and
Stacks 045C (`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`) are stated. Only the four
corners of the cospan happen to be algebraic stacks; nothing in the construction uses that.

The functor-level content — the comparison functor, the functor `f × g` and the natural
isomorphism filling the square — is
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverChangeOfBase`, stated for categories over an
arbitrary base category; this file is the bicategorical packaging.

The universal property is proved here, so Stacks 0302
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`) gives the representability
half of part (1) of Stacks 050H, and Stacks 045C
(`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`) gives, in *one* application at a
general property `P` of morphisms of algebraic spaces, every one of parts (2)–(7): each of those
names a property of `Δ_{𝒵/𝒯}` and asserts the same property of `i`, and
`AlgebraicGeometry.Stack.HasRelativeProperty` is definitionally the longhand condition of
Stacks 04XB that `StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms` states the separation
axioms with. The mediating 1-morphism is
`CategoryTheory.TwoFibreProductOver.changeOfBaseLift`, which is
`CategoryTheory.TwoFibreProductOver.lift` applied to the two projections of a test square and to
the 2-cell obtained from its filler by whiskering with the two projections of `𝒵 ×_𝒯 𝒵`;
uniqueness is `CategoryTheory.TwoFibreProductOver.changeOfBaseLiftIso`, built from
`CategoryTheory.TwoFibreProductOver.liftIso`.

The `Category` instance on the category of 2-commutative squares is passed to
`CategoryTheory.Limits.IsTerminal.ofUniqueHom` explicitly rather than left to instance search:
at the universes the 2-category of algebraic stacks is instantiated at, searching for it does not
terminate inside the default heartbeat budget, while the instance itself is
`CategoryTheory.Bicategory.TwoCommSq.category` with nothing to choose.

The *locally of finite type* half of part (1) stays open: it is Stacks 045C at the property
`locally of finite type`, whose input is part (2) of Stacks 04YQ — that `Δ_{𝒵/𝒯}` is locally of
finite type — which this library does not have; only parts (3) and (4) of Stacks 04YQ are proved,
in `StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism`.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 𝒯 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **The canonical 1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴`** attached to 1-morphisms `f : 𝒳 ⟶ 𝒵`,
`g : 𝒴 ⟶ 𝒵` and `h : 𝒵 ⟶ 𝒯` of algebraic stacks over `S`. It keeps both factors and applies `h`
to the comparison isomorphism. -/
def mapBase (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    twoFibreProduct B S hS f g ⟶ twoFibreProduct B S hS (f ≫ h) (g ≫ h) :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom
      ({ toFunctor := TwoFibreProductOver.mapBase (pT := 𝒳.val.val.p) (p𝒜 := 𝒴.val.val.p)
            (pℬ := 𝒵.val.val.p) (p𝒟 := 𝒯.val.val.p) (CatFiberedInGroupoids.homFunctor f.hom)
            (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor h.hom)
            (CatFiberedInGroupoids.homFunctor_comp_p h.hom)
         w := rfl } :
        (twoFibreProduct B S hS f g).val.val ⥤ᵇ
          (twoFibreProduct B S hS (f ≫ h) (g ≫ h)).val.val))

/-- **The 1-morphism `f × g : 𝒳 ×_𝒯 𝒴 ⟶ 𝒵 ×_𝒯 𝒵`** applying `f` to the first factor and `g` to
the second. It is the 1-morphism along which `AlgebraicGeometry.Stack.AlgebraicStacks.mapBase` is
a base change of the relative diagonal of `h`. -/
def mapCospan (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    twoFibreProduct B S hS (f ≫ h) (g ≫ h) ⟶ twoFibreProduct B S hS h h :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom
      ({ toFunctor := TwoFibreProductOver.mapCospan 𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p
            𝒯.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
            (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor h.hom)
            (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
            (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
         w := rfl } :
        (twoFibreProduct B S hS (f ≫ h) (g ≫ h)).val.val ⥤ᵇ
          (twoFibreProduct B S hS h h).val.val))

section Square

variable (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)

/-- **The natural isomorphism of underlying functors filling the square of
`AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseSquare`**: the functor-level identification
`CategoryTheory.TwoFibreProductOver.fstCompFCompDiagonalIso`, read at the structure functors of
the four algebraic stacks. -/
noncomputable abbrev mapBaseNatIso :=
  TwoFibreProductOver.fstCompFCompDiagonalIso 𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p 𝒯.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)
    (CatFiberedInGroupoids.homFunctor h.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom) (CatFiberedInGroupoids.homFunctor_comp_p h.hom)

/-- **The components of `AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseNatIso` are vertical.**
Each is the comparison morphism out of the diagonal determined by the comparison isomorphism of
an object of `𝒳 ×_𝒵 𝒴`, and its base morphism is the canonical identification of the two readings
of that object's base object; so it lies over an identity. -/
theorem isHomLift_mapBaseNatIso_app
    (Q : TwoFibreProductOver 𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)) :
    (TwoFibreProductOver.structureFunctor 𝒵.val.val.p 𝒵.val.val.p 𝒯.val.val.p
        (CatFiberedInGroupoids.homFunctor h.hom)
        (CatFiberedInGroupoids.homFunctor h.hom)).IsHomLift
      (𝟙 (TwoFibreProductOver.structureFunctor 𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor g.hom)|>.obj Q))
      ((mapBaseNatIso B S hS f g h).hom.app Q) := by
  have hsource : 𝒵.val.val.p.obj ((CatFiberedInGroupoids.homFunctor f.hom).obj Q.x) = Q.base :=
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p f.hom) Q.x).trans Q.hx
  refine IsHomLift.of_fac' _ (𝟙 Q.base) ((mapBaseNatIso B S hS f g h).hom.app Q) hsource
    rfl ?_
  change (TwoFibreProductOver.homDiagonal _ _ Q.iso.hom rfl).hbase = _
  change eqToHom hsource = eqToHom hsource ≫ 𝟙 Q.base ≫ eqToHom (rfl : Q.base = Q.base)
  simp

/-- **The square exhibiting `i` as a base change of the relative diagonal of `h`**:

```text
  𝒳 ×_𝒵 𝒴  --- i --->  𝒳 ×_𝒯 𝒴
     |                    |
  fst ≫ f           f × g
     v                    v
     𝒵   --- Δ_{𝒵/𝒯} --> 𝒵 ×_𝒯 𝒵
```

read in the 2-category of categories fibred in groupoids over the big fppf site of `S`, which is
where Stacks 0302 and Stacks 045C are stated. -/
noncomputable def mapBaseSquare : Bicategory.TwoCommSq (mapCospan B S hS f g h).hom
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom) where
  pt := (twoFibreProduct B S hS f g).val
  fst := (mapBase B S hS f g h).hom
  snd := ((twoFibreProductSquare B S hS f g).fst ≫ f).hom
  iso := (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (mapBaseNatIso B S hS f g h) (isHomLift_mapBaseNatIso_app B S hS f g h))).symm

variable (T : Bicategory.TwoCommSq (mapCospan B S hS f g h).hom
  (relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom))

/-- **The 2-cell of a test square, as a test cone over the cospan `(f × g, Δ_H)` of categories
over the site.** This is `CategoryTheory.CatFiberedInGroupoids.underlyingIso` of the 2-cell of
`T`, with its type written out: the comparison data that
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverChangeOfBase` consumes is the pair of structure
functors of the four algebraic stacks together with the three proofs that `f`, `g` and `h` are
1-morphisms over the site, and those proofs have to be visible in the type for the universal
property's statements to be instantiated at them. -/
noncomputable abbrev mapBaseConeIso :
    T.fst.hom.toFunctor ⋙ TwoFibreProductOver.mapCospan 𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p
        𝒯.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor g.hom) (CatFiberedInGroupoids.homFunctor h.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom) ≅
      T.snd.hom.toFunctor ⋙
        TwoFibreProductOver.diagonal (CatFiberedInGroupoids.homFunctor_comp_p h.hom) :=
  CatFiberedInGroupoids.underlyingIso T.iso

/-- **The components of the 2-cell of a test square are vertical.** This is clause (3) of
Stacks 02XS for the 2-cell of `T`, with the base category of the test square written out. -/
theorem isHomLift_mapBaseConeIso_hom_app (s : T.pt.val.obj) :
    (TwoFibreProductOver.structureFunctor 𝒵.val.val.p 𝒵.val.val.p 𝒯.val.val.p
        (CatFiberedInGroupoids.homFunctor h.hom)
        (CatFiberedInGroupoids.homFunctor h.hom)).IsHomLift
      (𝟙 (T.pt.val.p.obj s)) ((mapBaseConeIso B S hS f g h T).hom.app s) :=
  T.iso.hom.hom.isHomLift' s

/-- The mediating 1-morphism from a 2-commutative square `T` over the cospan
`(f × g, Δ_{𝒵/𝒯})` into the apex `𝒳 ×_𝒵 𝒴` of
`AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseSquare`: on an object `s` of `T` it is
`(p s, (T.fst s).x, (T.fst s).y, φ)` with `φ` read off the two components of the 2-cell of `T`. -/
noncomputable def mapBaseLift : T.pt ⟶ (mapBaseSquare B S hS f g h).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.changeOfBaseLift T.fst.hom.toFunctor T.snd.hom.toFunctor
        (mapBaseConeIso B S hS f g h T) (isHomLift_mapBaseConeIso_hom_app B S hS f g h T)
        T.fst.hom.w
      w := TwoFibreProductOver.changeOfBaseLift_comp_structureFunctor .. }

/-- `mapBaseLift` as a morphism of 2-commutative squares in the sense of Stacks 003O: its two
comparison 2-isomorphisms and their compatibility square. -/
noncomputable def mapBaseLiftCone :
    Bicategory.TwoCommSq.PreHom T (mapBaseSquare B S hS f g h) where
  hom := mapBaseLift B S hS f g h T
  isoFst := Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.changeOfBaseLiftCospanIso T.fst.hom.toFunctor T.snd.hom.toFunctor
      (mapBaseConeIso B S hS f g h T) (isHomLift_mapBaseConeIso_hom_app B S hS f g h T)
      T.fst.hom.w)
    (fun s => TwoFibreProductOver.changeOfBaseLiftCospanIso_hom_app_isHomLift
      T.fst.hom.toFunctor T.snd.hom.toFunctor (mapBaseConeIso B S hS f g h T)
      (isHomLift_mapBaseConeIso_hom_app B S hS f g h T) T.fst.hom.w s))
  isoSnd := Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.changeOfBaseLiftBaseIso T.fst.hom.toFunctor T.snd.hom.toFunctor
      (mapBaseConeIso B S hS f g h T) (isHomLift_mapBaseConeIso_hom_app B S hS f g h T)
      T.fst.hom.w)
    (fun s => TwoFibreProductOver.changeOfBaseLiftBaseIso_hom_app_isHomLift
      T.fst.hom.toFunctor T.snd.hom.toFunctor (mapBaseConeIso B S hS f g h T)
      (isHomLift_mapBaseConeIso_hom_app B S hS f g h T) T.fst.hom.w s))
  compat := Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext (funext
    (fun s => TwoFibreProductOver.changeOfBaseCompat_id T.fst.hom.toFunctor T.snd.hom.toFunctor
      (mapBaseConeIso B S hS f g h T) (isHomLift_mapBaseConeIso_hom_app B S hS f g h T)
      T.fst.hom.w s))))

variable (a : Bicategory.TwoCommSq.PreHom T (mapBaseSquare B S hS f g h))

/-- Uniqueness of the mediating morphism of 2-commutative squares: any other one is related to
`mapBaseLiftCone` by the 2-cell equivalence of Stacks 003O, so the two agree in the category
`CategoryTheory.Bicategory.TwoCommSq`. -/
lemma mapBaseLiftCone_rel :
    Bicategory.TwoCommSq.PreHom.Rel a (mapBaseLiftCone B S hS f g h T) := by
  have hid : ∀ s, (mapBaseConeIso B S hS f g h T).hom.app s ≫
      (TwoFibreProductOver.diagonal
          (CatFiberedInGroupoids.homFunctor_comp_p h.hom)).map
        ((CatFiberedInGroupoids.underlyingIso a.isoSnd).hom.app s) ≫ 𝟙 _ =
      (TwoFibreProductOver.mapCospan 𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p 𝒯.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)
            (CatFiberedInGroupoids.homFunctor h.hom)
            (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
            (CatFiberedInGroupoids.homFunctor_comp_p g.hom)).map
          ((CatFiberedInGroupoids.underlyingIso a.isoFst).hom.app s) ≫ 𝟙 _ ≫
        (mapBaseNatIso B S hS f g h).inv.app (a.hom.hom.toFunctor.obj s) :=
    fun s => congrArg (fun b => b.hom.app s) a.compat
  refine ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.changeOfBaseLiftIso T.fst.hom.toFunctor T.snd.hom.toFunctor
      (mapBaseConeIso B S hS f g h T) (isHomLift_mapBaseConeIso_hom_app B S hS f g h T)
      T.fst.hom.w a.hom.hom.toFunctor (CatFiberedInGroupoids.underlyingIso a.isoFst)
      (fun s => a.isoFst.hom.hom.isHomLift' s)
      (CatFiberedInGroupoids.underlyingIso a.isoSnd) hid)
    (fun s => TwoFibreProductOver.changeOfBaseLiftIso_hom_app_isHomLift T.fst.hom.toFunctor
      T.snd.hom.toFunctor (mapBaseConeIso B S hS f g h T)
      (isHomLift_mapBaseConeIso_hom_app B S hS f g h T) T.fst.hom.w a.hom.hom.toFunctor
      (CatFiberedInGroupoids.underlyingIso a.isoFst)
      (fun s => a.isoFst.hom.hom.isHomLift' s)
      (CatFiberedInGroupoids.underlyingIso a.isoSnd) hid s)), ?_, ?_⟩
  · exact Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext (funext
      (fun s => TwoFibreProductOver.changeOfBaseRelFst T.fst.hom.toFunctor T.snd.hom.toFunctor
        (mapBaseConeIso B S hS f g h T) (isHomLift_mapBaseConeIso_hom_app B S hS f g h T)
        T.fst.hom.w a.hom.hom.toFunctor (CatFiberedInGroupoids.underlyingIso a.isoFst)
        (fun s => a.isoFst.hom.hom.isHomLift' s)
        (CatFiberedInGroupoids.underlyingIso a.isoSnd) hid s))))
  · exact Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext (funext
      (fun s => TwoFibreProductOver.changeOfBaseRelSnd T.fst.hom.toFunctor T.snd.hom.toFunctor
        (mapBaseConeIso B S hS f g h T) (isHomLift_mapBaseConeIso_hom_app B S hS f g h T)
        T.fst.hom.w a.hom.hom.toFunctor (CatFiberedInGroupoids.underlyingIso a.isoFst)
        (fun s => a.isoFst.hom.hom.isHomLift' s)
        (CatFiberedInGroupoids.underlyingIso a.isoSnd) hid s))))

/-- **Stacks 050H, the geometric content: `i` is a base change of `Δ_{𝒵/𝒯}`.** The square
`AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseSquare` is a 2-fibre product in the 2-category of
categories fibred in groupoids over the big fppf site of `S`.

Together with Stacks 0302
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`) this makes
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` representable by algebraic spaces, and together with Stacks 045C
(`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`) it transfers every relative property
of `Δ_{𝒵/𝒯}` to `i`, which is parts (2)–(7) of Stacks 050H in one application. Those are proved
in `StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties`, which is where the
Stacks 050H tag sits; this is the geometric input to them and carries no tag of its own. -/
noncomputable def isTwoFibreProduct_mapBaseSquare (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    Bicategory.IsTwoFibreProduct (mapBaseSquare B S hS f g h) :=
  @CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (Bicategory.TwoCommSq (mapCospan B S hS f g h).hom
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom))
    Bicategory.TwoCommSq.category _
    (fun Q => _root_.Quotient.mk _ (mapBaseLiftCone B S hS f g h Q))
    (fun Q c => _root_.Quotient.inductionOn c
      (fun c => _root_.Quotient.sound (mapBaseLiftCone_rel B S hS f g h Q c)))

end Square

end AlgebraicGeometry.Stack.AlgebraicStacks

end
