module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp

/-!
# The `mapHomologyIso` glue, read on complexes

`CategoryTheory.ShortComplex.mapHomologyIso_glue` is the composition law for
`CategoryTheory.ShortComplex.mapHomologyIso` and Mathlib's
`CategoryTheory.ShortComplex.mapHomologyIso_inv_naturality` composed, at a short complex and two
maps of short complexes. A chase that compares two readings of the right derived functors of a
composite meets it at the degree-`p` short complexes of **complexes**, with the two maps induced
by a comparison of resolutions and by an isomorphism of the two composite functors — and the two
spellings of those short complexes, `(S.map R)` against the degree-`p` short complex of the image
of the complex under `F ⋙ R`, are definitionally equal and distinct `simp` keys.

This file states the glue at that shape, so that the crossing is paid once here, at variables of
abstract categories, where it is cheap. A consumer at concrete categories then matches it
syntactically.

## Main results

* `CategoryTheory.ShortComplex.mapHomologyIso_glue_mapHomologicalComplex`: for functors
  `L : C₁ ⥤ C₃`, `Fp : C₃ ⥤ C₄`, `F : C₁ ⥤ C₂`, `R : C₂ ⥤ C₄`, `P : C₄ ⥤ C₅`, an isomorphism
  `ε : L ⋙ Fp ≅ F ⋙ R`, complexes `I` in `C₁` and `J` in `C₃` and a map
  `γ : J ⟶ L(I)`,

  > `P(Hᵖ(Fp(γ))) ≫ P(Hᵖ(ε.hom(I))) ≫ P((F(I).sc p).mapHomologyIso R).hom ≫`
  > `((F(I).sc p).mapHomologyIso (R ⋙ P)).inv ≫ Hᵖ((ε.inv whiskered by P)(I))`

  is `((Fp(J).sc p).mapHomologyIso P).inv ≫ Hᵖ((Fp ⋙ P)(γ))`.

  Only the pointwise homology hypotheses are asked, and nothing of `P` beyond additivity.

## Implementation notes

The one input beyond `mapHomologyIso_glue` is that `ε.hom` and `ε.inv`, read on the complex `I`,
compose to the identity — which the degree-`p` short complex functor then carries to a retraction
pair, the hypothesis the glue takes. It is checked degreewise, where it is `ε.hom_inv_id_app`.
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Category Limits

variable {C₁ C₂ C₃ C₄ C₅ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* C₅] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄] [Abelian C₅]
  (L : C₁ ⥤ C₃) (Fp : C₃ ⥤ C₄) (F : C₁ ⥤ C₂) (R : C₂ ⥤ C₄) (P : C₄ ⥤ C₅)
  [L.Additive] [Fp.Additive] [F.Additive] [R.Additive] [P.Additive]
  (ε : L ⋙ Fp ≅ F ⋙ R) {ι : Type*} (cs : ComplexShape ι) (p : ι)
  (I : HomologicalComplex C₁ cs) (J : HomologicalComplex C₃ cs)
  (γ : J ⟶ (L.mapHomologicalComplex cs).obj I)

/-- **`CategoryTheory.ShortComplex.mapHomologyIso_glue` at the degree-`p` short complexes of the
images of two complexes.** The two maps of short complexes the glue takes are the ones induced by
`γ` under `Fp` and by `ε.hom` on `I`, the retraction of the second being the one induced by
`ε.inv`.

Only the pointwise homology hypotheses are asked — `R` and `R ⋙ P` on the degree-`p` short complex
of `F(I)`, `P` on its image under `R`, and `P` on the degree-`p` short complex of `Fp(J)`. Nothing
is assumed of `P` beyond additivity, and in particular no exactness.

The point of stating it here rather than applying the short-complex glue at a use site is that the
two spellings of the short complex `(F(I).sc p).map R` — as that, and as the degree-`p` short
complex of the image of `I` under `F ⋙ R` — are definitionally equal but not syntactically so, and
the crossing between them is made once, here, at variables. -/
theorem mapHomologyIso_glue_mapHomologicalComplex
    [R.PreservesLeftHomologyOf (((F.mapHomologicalComplex cs).obj I).sc p)]
    [(R ⋙ P).PreservesLeftHomologyOf (((F.mapHomologicalComplex cs).obj I).sc p)]
    [P.PreservesLeftHomologyOf ((((F.mapHomologicalComplex cs).obj I).sc p).map R)]
    [P.PreservesLeftHomologyOf (((Fp.mapHomologicalComplex cs).obj J).sc p)] :
    P.map ((HomologicalComplex.homologyFunctor C₄ cs p).map
          ((Fp.mapHomologicalComplex cs).map γ)) ≫
        P.map ((HomologicalComplex.homologyFunctor C₄ cs p).map
          ((ε.hom.mapHomologicalComplex cs).app I)) ≫
        P.map ((((F.mapHomologicalComplex cs).obj I).sc p).mapHomologyIso R).hom ≫
        ((((F.mapHomologicalComplex cs).obj I).sc p).mapHomologyIso (R ⋙ P)).inv ≫
        (HomologicalComplex.homologyFunctor C₅ cs p).map
          (((Functor.whiskerRight ε.inv P).mapHomologicalComplex cs).app I) =
      ((((Fp.mapHomologicalComplex cs).obj J).sc p).mapHomologyIso P).inv ≫
        ((Fp ⋙ P).mapHomologicalComplex cs ⋙
          HomologicalComplex.homologyFunctor C₅ cs p).map γ := by
  have hiso : (ε.hom.mapHomologicalComplex cs).app I ≫
      (ε.inv.mapHomologicalComplex cs).app I = 𝟙 _ := by
    ext i
    simp
  exact mapHomologyIso_glue (((F.mapHomologicalComplex cs).obj I).sc p) R P
    ((HomologicalComplex.shortComplexFunctor C₄ cs p).map ((Fp.mapHomologicalComplex cs).map γ))
    ((HomologicalComplex.shortComplexFunctor C₄ cs p).map ((ε.hom.mapHomologicalComplex cs).app I))
    ((HomologicalComplex.shortComplexFunctor C₄ cs p).map ((ε.inv.mapHomologicalComplex cs).app I))
    ((((HomologicalComplex.shortComplexFunctor C₄ cs p).map_comp _ _).symm).trans
      ((congrArg (HomologicalComplex.shortComplexFunctor C₄ cs p).map hiso).trans
        ((HomologicalComplex.shortComplexFunctor C₄ cs p).map_id _)))

end CategoryTheory.ShortComplex

end
