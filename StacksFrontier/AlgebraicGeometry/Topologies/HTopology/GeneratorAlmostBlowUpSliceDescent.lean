module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSubterminal
public import StacksFrontier.AlgebraicGeometry.Topologies.H.Limits
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Descending a proposition along an h covering by testing it on the generating squares

Let `U` be an object of the big h category over `S` and let `Ψ` be a property of objects of the
slice `(Sch/S)_h / U` which is stable under precomposition — a property of morphisms `Y ⟶ U` of
the site which passes to a refinement.  The main result of this file,
`AlgebraicGeometry.BigHOver.of_localOnGenerators`, says that such a property holds for `𝟙 U` as
soon as

1. it is Zariski-local;
2. it descends along a flat proper surjection of finite presentation onto an affine object;
3. and 4. it descends along the two-member family `{Z ⟶ X, X' ⟶ X}` of an almost blowup square
   of the shape of Example 0EVG, resp. 0EVH;

and it holds for every member of one h covering family of `U`.

This is the sufficiency direction of Stacks 0EVI
(`AlgebraicGeometry.BigHOver.isSheaf_of_generatorSquares`) applied to the subterminal presheaf of
truth values of `Ψ` on the big h category over the underlying scheme of `U`.  Two identifications
make that application cheap, and both hold by `rfl` here: the big h category over the underlying
scheme of `U` *is* the slice `B.Schemes / U.left`, and its underlying-scheme functor *is* the
underlying-scheme functor of `(Sch/S)_h` precomposed with `CategoryTheory.Over.map U.hom`, which
is `CategoryTheory.Over.iteratedSliceBackward U` followed by `CategoryTheory.Over.forget U`.  So a
Zariski covering family, a flat proper surjection or an almost blowup square of that site is one
of the slice, with the same underlying schemes, and the four conditions of Stacks 0EVI for the
subterminal presheaf are the four hypotheses above.

The point of the subterminal presheaf is that the conditions of Stacks 0EVI simplify: a family of
elements of a presheaf whose values are subsingletons carries no data, so each condition becomes an
implication between nonemptiness statements, which is what
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSubterminal` records.

## Main definitions

* `AlgebraicGeometry.BigHOver.sliceToScheme`: the underlying scheme of an object of the slice of
  the big h category over `S` at an object `U`.

## Main results

* `AlgebraicGeometry.BigHOver.of_localOnGenerators`: the descent principle described above.

## References

* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigHOver B S hS)

/-- The underlying scheme of an object of the slice of the big h category over `S` at `U`. -/
public abbrev sliceToScheme : Over U ⥤ Scheme.{u} :=
  Over.forget U ⋙ BigHOver.toScheme B S hS

/-- The subterminal presheaf of truth values of a property of objects of the slice which is
stable under precomposition. -/
public def truthPresheaf (Ψ : Over U → Prop)
    (hmono : ∀ {Y Y' : Over U}, (Y' ⟶ Y) → Ψ Y → Ψ Y') : (Over U)ᵒᵖ ⥤ Type where
  obj Y := PLift (Ψ Y.unop)
  map k := ↾fun x ↦ ⟨hmono k.unop x.down⟩
  map_id _ := by ext x; cases x; rfl
  map_comp _ _ := by ext x; cases x; rfl

public instance (Ψ : Over U → Prop)
    (hmono : ∀ {Y Y' : Over U}, (Y' ⟶ Y) → Ψ Y → Ψ Y') (Y : (Over U)ᵒᵖ) :
    Subsingleton ((truthPresheaf B S hS U Ψ hmono).obj Y) :=
  ⟨fun a b ↦ by cases a; cases b; rfl⟩

/-- **A property of objects of the slice at `U` which is local for the generating families of the
h topology, and holds on one h covering of `U`, holds at `U`.**

The four hypotheses are the four conditions of Stacks 0EVI for the subterminal presheaf of truth
values of `Ψ`, read on the big h category over the underlying scheme of `U`. -/
public theorem of_localOnGenerators
    (Ψ : Over U → Prop)
    (hmono : ∀ {Y Y' : Over U}, (Y' ⟶ Y) → Ψ Y → Ψ Y')
    (hzar : ∀ (Y : Over U) (E : PreZeroHypercover.{u + 1} Y),
      (E.map (sliceToScheme B S hS U)).presieve₀ ∈
        Scheme.zariskiPrecoverage ((sliceToScheme B S hS U).obj Y) →
      (∀ i, Ψ (E.X i)) → Ψ Y)
    (haff : ∀ (Y Y' : Over U) (g : Y' ⟶ Y),
      IsAffine ((sliceToScheme B S hS U).obj Y) →
      Flat ((sliceToScheme B S hS U).map g) →
      IsProper ((sliceToScheme B S hS U).map g) →
      Surjective ((sliceToScheme B S hS U).map g) →
      FinitePresentation ((sliceToScheme B S hS U).map g) →
      Ψ Y' → Ψ Y)
    (hone : ∀ (X X' Z E : Over U) (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
        (I : ((sliceToScheme B S hS U).obj X).IdealSheafData),
      IsAffine ((sliceToScheme B S hS U).obj X) →
      IsAlmostBlowUpSquare I ((sliceToScheme B S hS U).map b) →
      Nonempty (Over.mk ((sliceToScheme B S hS U).map z) ≅ Over.mk I.subschemeι) →
      IsPullback ((sliceToScheme B S hS U).map e) ((sliceToScheme B S hS U).map q)
        ((sliceToScheme B S hS U).map z) ((sliceToScheme B S hS U).map b) →
      IsOneGeneratorAlmostBlowUpModel
        ((sliceToScheme B S hS U).map b) ((sliceToScheme B S hS U).map z) →
      Ψ Z → Ψ X' → Ψ X)
    (htwo : ∀ (X X' Z E : Over U) (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
        (I : ((sliceToScheme B S hS U).obj X).IdealSheafData),
      IsAffine ((sliceToScheme B S hS U).obj X) →
      IsAlmostBlowUpSquare I ((sliceToScheme B S hS U).map b) →
      Nonempty (Over.mk ((sliceToScheme B S hS U).map z) ≅ Over.mk I.subschemeι) →
      IsPullback ((sliceToScheme B S hS U).map e) ((sliceToScheme B S hS U).map q)
        ((sliceToScheme B S hS U).map z) ((sliceToScheme B S hS U).map b) →
      IsTwoGeneratorAlmostBlowUpModel
        ((sliceToScheme B S hS U).map b) ((sliceToScheme B S hS U).map z) →
      Ψ Z → Ψ X' → Ψ X)
    {I : Type (u + 1)} {V : I → BigHOver B S hS} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    (hV : ∀ i, Ψ (Over.mk (f i))) :
    Ψ (Over.mk (𝟙 U)) := by
  classical
  let β : Over U.left ⥤ Over U := Over.iteratedSliceBackward U
  set P := truthPresheaf B S hS U Ψ hmono with hP
  set G : (BigHOver B ((BigHOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ ⥤ Type :=
    β.op ⋙ P with hG
  have hsub : ∀ Y, Subsingleton (G.obj Y) := fun Y ↦ inferInstanceAs
    (Subsingleton (P.obj (op (β.obj Y.unop))))
  -- `Ψ` holds at an object of the slice at `U` iff the subterminal presheaf is inhabited there
  have hiff : ∀ Y, Nonempty (G.obj (op Y)) ↔ Ψ (β.obj Y) :=
    fun Y ↦ ⟨fun ⟨x⟩ ↦ x.down, fun h ↦ ⟨⟨h⟩⟩⟩
  have hsheaf : Presheaf.IsSheaf
      (BigHOver.topology B ((BigHOver.toScheme B S hS).obj U) U.left.property) G := by
    refine isSheaf_of_generatorSquares _ _ _ G
      (isZariskiSheaf_of_nonempty _ _ _ G ?_) (isAffineFlatProperFinitePresentationSheaf_of_nonempty
        _ _ _ G ?_) (isOneGeneratorAlmostBlowUpSheaf_of_nonempty _ _ _ G ?_)
      (isTwoGeneratorAlmostBlowUpSheaf_of_nonempty _ _ _ G ?_)
    · intro Y E hE hne
      exact (hiff Y).2 (hzar (β.obj Y) (E.map β) hE fun i ↦ (hiff (E.X i)).1 (hne i))
    · intro Y Y' g hAff hflat hproper hsurj hfp hne
      exact (hiff Y).2 (haff (β.obj Y) (β.obj Y') (β.map g) hAff hflat hproper hsurj hfp
        ((hiff Y').1 hne))
    · intro X X' Z E b z q e Id hAff hb hZ hsq hmod hZne hX'ne
      exact (hiff X).2 (hone (β.obj X) (β.obj X') (β.obj Z) (β.obj E) (β.map b) (β.map z)
        (β.map q) (β.map e) Id hAff hb hZ hsq hmod ((hiff Z).1 hZne) ((hiff X').1 hX'ne))
    · intro X X' Z E b z q e Id hAff hb hZ hsq hmod hZne hX'ne
      exact (hiff X).2 (htwo (β.obj X) (β.obj X') (β.obj Z) (β.obj E) (β.map b) (β.map z)
        (β.map q) (β.map e) Id hAff hb hZ hsq hmod ((hiff Z).1 hZne) ((hiff X').1 hX'ne))
  -- the covering family of `U`, read in the big h category over the underlying scheme of `U`
  have hcov : Sieve.ofArrows (fun i ↦ Over.mk (f i).left)
      (fun i ↦ (Over.homMk (f i).left : Over.mk (f i).left ⟶ Over.mk (𝟙 U.left))) ∈
      BigHOver.topology B ((BigHOver.toScheme B S hS).obj U) U.left.property
        (Over.mk (𝟙 U.left)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hf
    exact hf
  have hmem : ∀ i, Nonempty (G.obj (op (Over.mk (f i).left))) := by
    intro i
    refine (hiff _).2 (hmono (Y := Over.mk (f i)) ?_ (hV i))
    have hw : 𝟙 (V i).left ≫ (V i).hom = (f i).left ≫ U.hom := by simp
    exact Over.homMk (Over.homMk (𝟙 (V i).left) hw) (Over.OverMorphism.ext
      (by change 𝟙 (V i).left ≫ (f i).left = (f i).left; simp))
  obtain ⟨x⟩ := nonempty_of_isSheaf_of_covering _ _ _ G hsheaf _ hcov hmem
  refine hmono (Y := β.obj (Over.mk (𝟙 U.left))) ?_ ((hiff _).1 ⟨x⟩)
  have hw : 𝟙 U.left ≫ (𝟙 U.left ≫ U.hom) = U.hom := by simp
  exact Over.homMk (Over.homMk (𝟙 U.left) hw) (Over.OverMorphism.ext
    (by change 𝟙 U.left ≫ 𝟙 U.left = 𝟙 U.left; simp))

end BigHOver

end AlgebraicGeometry

end
