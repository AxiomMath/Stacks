module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeFieldPointFactorization

/-!
# Factoring through a monomorphism of algebraic stacks

Two ways of factoring a 1-morphism of algebraic stacks through a monomorphism, both read off
the canonical 2-fibre product square of **Stacks 04T2**: if the first projection
`𝒴 ×_𝒱 𝒦 ⟶ 𝒴` of the base change of a monomorphism `a : 𝒦 ⟶ 𝒱` along `q : 𝒴 ⟶ 𝒱` is an
equivalence over the site, then a quasi-inverse composed with the second projection factors `q`
through `a`, up to a 2-isomorphism.

* **Descent along a flat cover.** If `q` precomposed with a surjective flat 1-morphism
  `b : T ⟶ 𝒴`, locally of finite presentation, out of the algebraic stack of a scheme factors
  through `a`, then so does `q`. The base change of `a` is a monomorphism, hence fully faithful
  (**Stacks 05UK**); the factorization of `b` makes it locally essentially surjective on fibres
  (**Stacks 07AN**), so it is an equivalence over the site (**Stacks 046N**).
* **Stacks 06MQ.** If `q` has source admitting a surjective flat 1-morphism, locally of finite
  presentation, from the spectrum of a field (condition (2) of **Stacks 06MP**), and some point of
  `𝒴` and some point of `𝒦` have the same image, then `q` factors through `a`: the base change of
  `a` is a monomorphism with nonempty source (**Stacks 04XH**) into `𝒴`, hence an equivalence.

## Main results

* `AlgebraicGeometry.Stack.exists_factorization_of_isMonomorphism_of_cover`: descent of a
  factorization through a monomorphism along a flat cover by a scheme.
* `AlgebraicGeometry.Stack.exists_factorization_of_isMonomorphism_of_fieldSpectrumCover`: a
  1-morphism out of an algebraic stack satisfying condition (2) of Stacks 06MP factors through
  every monomorphism whose image meets its image.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A base change which is an equivalence gives a factorization.** Let `q : 𝒴 ⟶ 𝒱` and
`a : 𝒦 ⟶ 𝒱` be 1-morphisms of algebraic stacks over `S`. If the first projection of the canonical
2-fibre product `𝒴 ×_𝒱 𝒦` is an equivalence over the site, then a quasi-inverse of it composed
with the second projection is a 1-morphism `g : 𝒴 ⟶ 𝒦` with `g ≫ a ≅ q`. -/
theorem exists_factorization_of_isEquivalenceOver_fst
    {𝒴 𝒦 𝒱 : AlgebraicStacks.{u, w} B S hS} (q : 𝒴 ⟶ 𝒱) (a : 𝒦 ⟶ 𝒱)
    (e : Functor.IsEquivalenceOver (twoFibreProductSquareAlgebraicStacks B S hS q a).pt.val.val.p
      𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor
        (twoFibreProductSquareAlgebraicStacks B S hS q a).fst.hom)) :
    ∃ g : 𝒴 ⟶ 𝒦, Nonempty (g ≫ a ≅ q) := by
  set Q := twoFibreProductSquareAlgebraicStacks B S hS q a
  have hcomp : (e.inv ⋙ CatFiberedInGroupoids.homFunctor Q.fst.hom) ⋙ 𝒴.val.val.p =
      𝒴.val.val.p :=
    calc (e.inv ⋙ CatFiberedInGroupoids.homFunctor Q.fst.hom) ⋙ 𝒴.val.val.p
        = e.inv ⋙ (CatFiberedInGroupoids.homFunctor Q.fst.hom ⋙ 𝒴.val.val.p) :=
          Functor.assoc _ _ _
      _ = e.inv ⋙ Q.pt.val.val.p :=
          congrArg (e.inv ⋙ ·) (CatFiberedInGroupoids.homFunctor_comp_p Q.fst.hom)
      _ = 𝒴.val.val.p := e.inv_over
  have hbase : ∀ y : 𝒴.val.val.obj,
      𝒴.val.val.p.obj ((e.inv ⋙ CatFiberedInGroupoids.homFunctor Q.fst.hom).obj y) =
        𝒴.val.val.p.obj y :=
    fun y => Functor.congr_obj hcomp y
  let s : 𝒴 ⟶ Q.pt := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ({ toFunctor := e.inv, w := e.inv_over } : 𝒴.val.val ⥤ᵇ Q.pt.val.val))
  have cu : s ≫ Q.fst ≅ 𝟙 𝒴 :=
    Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
      (BasedNatIso.mkNatIso e.counitIso fun y => by
        have h := e.counit_vertical y
        rwa [hbase y] at h))
  exact ⟨s ≫ Q.snd, ⟨(Bicategory.associator s Q.snd a).trans
    ((Bicategory.whiskerLeftIso s Q.iso).symm.trans
      ((Bicategory.associator s Q.fst q).symm.trans
        ((Bicategory.whiskerRightIso cu q).trans (Bicategory.leftUnitor q))))⟩⟩

/-- **A monomorphism through which a flat cover by a scheme factors is an equivalence.** Let
`j : 𝒦 ⟶ 𝒴` be a monomorphism of algebraic stacks over `S` and let `b` be a surjective flat
1-morphism, locally of finite presentation, from the algebraic stack of a scheme `T` to `𝒴`. If
`b` factors through `j` up to a 2-isomorphism, then `j` is an equivalence over the site.

The monomorphism is fully faithful (**Stacks 05UK**); the components of the 2-isomorphism are
vertical isomorphisms between the images of the objects of `Sch/T` under `b` and images of
objects of `𝒦` under `j`, which with **Stacks 07AN** is local essential surjectivity on fibres,
and **Stacks 046N** concludes. -/
theorem nonempty_isEquivalenceOver_of_isMonomorphism_of_cover
    {𝒦 𝒴 : AlgebraicStacks.{u, w} B S hS} (j : 𝒦 ⟶ 𝒴)
    (hj : AlgebraicStacks.IsMonomorphism B S hS j) (T : BigFppfOver B S hS)
    (b : schemeStack.{u, w} B S hS T ⟶ 𝒴)
    (hflat : AlgebraicStacks.IsFlat B S hS b)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS b)
    (hsurj : IsSurjective B S hS b)
    (c : schemeStack.{u, w} B S hS T ⟶ 𝒦) (η : c ≫ j ≅ b) :
    Nonempty (Functor.IsEquivalenceOver 𝒦.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor j.hom)) := by
  have hy : T.iteratedSliceBackward ⋙ (schemeStack.{u, w} B S hS T).val.val.p =
      Over.map T.hom := Over.iteratedSliceBackward_forget T
  have hlift : ∀ a : BigFppfOver B T.left.1 T.left.2,
      ∃ (x : 𝒦.val.val.obj)
        (i : (T.iteratedSliceBackward ⋙ CatFiberedInGroupoids.homFunctor b.hom).obj a ≅
          (CatFiberedInGroupoids.homFunctor j.hom).obj x),
        𝒴.val.val.p.IsHomLift (𝟙 ((Over.map T.hom).obj a)) i.hom := by
    intro a
    let t := T.iteratedSliceBackward.obj a
    refine ⟨(CatFiberedInGroupoids.homFunctor c.hom).obj t,
      ((CatFiberedInGroupoids.underlyingIso (Bicategory.InducedBicategory.isoHom η)).app t).symm,
      ?_⟩
    have ht : (schemeStack.{u, w} B S hS T).val.val.p.obj t = (Over.map T.hom).obj a :=
      Functor.congr_obj hy a
    have h := η.inv.hom.hom.isHomLift' t
    rwa [ht] at h
  obtain ⟨hfull, hfaith⟩ := full_and_faithful_homFunctor_of_mono_representingMaps B S hS j.hom
    hj.1 fun U z hz H hH he => (Space.mono_hom_iff_mono B S hS _).2 (hj.2 U z hz H hH he)
  exact (Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers
    (isStack_of_isAlgebraicStack.{u, w} B S hS 𝒦.property)
    (isStack_of_isAlgebraicStack.{u, w} B S hS 𝒴.property)
    (Functor.IsFibredOneMorphism.of_isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p j.hom))).2
    (locallyEssSurjOnFibers_of_forall_vertical_iso B S hS j T b hlift hflat hlfp hsurj)

/-- **Descent of a factorization through a monomorphism along a flat cover by a scheme.** Let
`a : 𝒦 ⟶ 𝒱` be a monomorphism and `q : 𝒴 ⟶ 𝒱` a 1-morphism of algebraic stacks over `S`, and let
`b` be a surjective flat 1-morphism, locally of finite presentation, from the algebraic stack of
a scheme `T` to `𝒴`. If `b ≫ q` factors through `a` up to a 2-isomorphism, then so does `q`.

The pair `(b, c)` lifts `b` to the canonical 2-fibre product `𝒴 ×_𝒱 𝒦`, whose first projection
is a monomorphism as a base change of `a` (**Stacks 04ZW**); by
`AlgebraicGeometry.Stack.nonempty_isEquivalenceOver_of_isMonomorphism_of_cover` it is an
equivalence, and `AlgebraicGeometry.Stack.exists_factorization_of_isEquivalenceOver_fst`
concludes. -/
theorem exists_factorization_of_isMonomorphism_of_cover
    {𝒴 𝒦 𝒱 : AlgebraicStacks.{u, w} B S hS} (q : 𝒴 ⟶ 𝒱) (a : 𝒦 ⟶ 𝒱)
    (ha : AlgebraicStacks.IsMonomorphism B S hS a) (T : BigFppfOver B S hS)
    (b : schemeStack.{u, w} B S hS T ⟶ 𝒴)
    (hflat : AlgebraicStacks.IsFlat B S hS b)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS b)
    (hsurj : IsSurjective B S hS b)
    (c : schemeStack.{u, w} B S hS T ⟶ 𝒦) (η : c ≫ a ≅ b ≫ q) :
    ∃ g : 𝒴 ⟶ 𝒦, Nonempty (g ≫ a ≅ q) := by
  set P := twoFibreProductSquareAlgebraicStacks B S hS q a
  have hPprod : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS q a
  have hfst : AlgebraicStacks.IsMonomorphism B S hS P.fst :=
    AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks B S hS q a ha
  let L := Bicategory.twoFibreProductPreHom hPprod
    { pt := schemeStack.{u, w} B S hS T, fst := b, snd := c, iso := η.symm }
  obtain ⟨e⟩ := nonempty_isEquivalenceOver_of_isMonomorphism_of_cover B S hS P.fst hfst T b
    hflat hlfp hsurj L.hom L.isoFst.symm
  exact exists_factorization_of_isEquivalenceOver_fst B S hS q a e

/-- **A 1-morphism out of a stack covered by the spectrum of a field factors through every
monomorphism whose image meets its image (Stacks 06MQ).** Let `h : 𝒲 ⟶ 𝒳` and a monomorphism
`m : 𝒵 ⟶ 𝒳` of algebraic stacks over `S` be given, with `𝒲` satisfying condition (2) of
**Stacks 06MP**. If a point of `𝒲` and a point of `𝒵` have the same image in `|𝒳|`, then `h`
factors through `m` up to a 2-isomorphism.

The first projection of `𝒲 ×_𝒳 𝒵` is a monomorphism as a base change of `m` (**Stacks 04ZW**),
and its source has a point by **Stacks 04XH**, so it is an equivalence by **Stacks 06MQ**. This
generalizes the argument of `AlgebraicGeometry.Stack.exists_factorization_of_hasUniquePointOver`
(Stacks 06MW) from the spectrum of a field to any such `𝒲`. -/
theorem exists_factorization_of_isMonomorphism_of_fieldSpectrumCover
    {𝒲 𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS} (h : 𝒲 ⟶ 𝒳) (m : 𝒵 ⟶ 𝒳)
    (hm : AlgebraicStacks.IsMonomorphism B S hS m)
    (hcov : HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒲)
    (w : AlgebraicStacks.points B S hS 𝒲) (z : AlgebraicStacks.points B S hS 𝒵)
    (hwz : AlgebraicStacks.pointsMap B S hS h w = AlgebraicStacks.pointsMap B S hS m z) :
    ∃ g : 𝒲 ⟶ 𝒵, Nonempty (g ≫ m ≅ h) := by
  set P := twoFibreProductSquareAlgebraicStacks B S hS h m with hP
  have hfst : AlgebraicStacks.IsMonomorphism B S hS P.fst :=
    AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks B S hS h m hm
  obtain ⟨r, -, -⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P
    (hP ▸ isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS h m) w z hwz
  rcases isEmpty_points_or_isEquivalenceOver_of_isMonomorphism B S hS P.pt 𝒲 P.fst hfst hcov
    with hempty | he
  · exact hempty.elim r
  obtain ⟨e⟩ := he
  exact exists_factorization_of_isEquivalenceOver_fst B S hS h m e

end AlgebraicGeometry.Stack

end
