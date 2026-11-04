module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBaseComposition
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import StacksFrontier.CategoryTheory.CompositeCancellation

/-!
# Grothendieck's collapse and the outer functor

`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso E F G n h` is Grothendieck's comparison
`E ⋙ RⁿF ⋙ G ≅ E ⋙ Rⁿ(F ⋙ G)` with the homology-preservation hypothesis on the outer functor `G`
asked only pointwise, at the degree-`n` short complexes of the images under `F` of the chosen
injective resolutions.  Two consumers of it that arise at the same object but write the outer
functor differently cannot be compared by any statement in the library: the comparison is
indexed by `G`, and nothing relates its values at two outer functors.  This file supplies the two
relations needed, both with nothing assumed beyond the pointwise hypotheses the collapses
themselves carry — in particular no exactness of the outer functor, which is what keeps them
available where that functor is sections over an affine open.

Conclusion (c) of [Stacks, Tag 0EX3] needs both.  The `γ⁺` side reads the collapse at the pair
`(f_*, Γ(V, -))` on the ambient base, while
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square` — the
comparison of that collapse with the one on the open subscheme — is stated at a general additive
`P` out of the modules on the open subspace, so that its ambient outer functor is
`(-|_V) ⋙ P`.  At `P` the composite of global sections of the open subscheme with a restriction
of scalars those two outer functors are `Γ(V.ι ''ᵁ ⊤, -) ⋙ res` and `Γ(V, -)`: isomorphic, by a
comparison in the library, but not equal — their targets are modules over two different rings — and
separated by exactly the two steps below.

## Main results

* `…AffineBase.rightDerivedCompIso_refl_hom_app_mapHomologyIso`: **the canonical transport the
  postcomposition square is applied at**, read on the chosen injective resolution — which is
  exactly that square's hypothesis `hσ`, so a consumer taking the transport to be
  `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at the identity comparison has it for
  free.
* `…AffineBase.rightDerivedCompNatIso_postcomp_square`: **the collapse at `G ⋙ R` is `R` of the
  collapse at `G`.** For an additive `R` out of `G`'s target, the image under `R` of the
  component of the collapse at `(F, G)`, followed by the derived transport
  `Rⁿ(F ⋙ G) ⋙ R ⟶ Rⁿ(F ⋙ G ⋙ R)`, is the component of the collapse at `(F, G ⋙ R)`.
* `…AffineBase.rightDerivedCompNatIso_natIso_square`: **the collapse transported along a natural
  isomorphism of the outer functor.** For `α : G ≅ G'`, the component of the collapse at
  `(F, G)` followed by the derived transport `Rⁿ(F ⋙ G) ⟶ Rⁿ(F ⋙ G')` is `α` at `RⁿF` followed by
  the component of the collapse at `(F, G')`.

In both statements the derived transport is hoisted onto a variable whose defining hypothesis is
its reading on the chosen injective resolution; a caller takes the variable to be that composite,
for which the hypothesis is `rfl`.  This is the discipline
`rightDerivedCompNatIso_restrictChosenResolution_square` follows for its own transport `τ`, and
for the same reason: the two transports are built by different universal properties at the two
pairs a consumer meets them at, and hoisting lets the statement be used without committing to
one.

## Implementation notes

*What the two reductions are.* Both proofs rewrite each collapse by
`…AffineBase.rightDerivedCompNatIso_hom_app`, which prints the component as
`CategoryTheory.ShortComplex.mapHomologyIso` for the outer functor on the degree-`n` short complex
of the image under `F` of the chosen resolution, conjugated by
`CategoryTheory.InjectiveResolution.isoRightDerivedObj`.  One conjugating factor of each path then
cancels against the hoisted transport's reading, and what is left is a `mapHomologyIso` identity:
the composition law `CategoryTheory.ShortComplex.mapHomologyIso_comp_inv` for the first statement,
and the naturality in the functor `CategoryTheory.ShortComplex.mapHomologyIso_inv_natTrans` for
the second.  Nothing else is used, and nothing new about homology is proved here.

*Why the steps after the rewrites are terms.* The `mapHomologyIso` factor of a collapse at the
pair `(F, G)` has target `(((F[I]).sc n).map G).homology`, while the `isoRightDerivedObj` factor
beside it is stated at `Hⁿ((F ⋙ G)[I])`; the two objects are definitionally equal and are distinct
keys, so a goal carrying both is not type-correct at `implicit` transparency and `simp only` on it
is refused with no progress.  The bookkeeping is therefore done at variables of an
abstract category, by `CategoryTheory.comp_conj_cancel_square` and
`CategoryTheory.map_comp₃_cancel_mid`, where it is syntactic — the same obstruction, at a new
shape, as the one met in the proof of
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square`.

*No `@[stacks …]` attribute is placed.*  These are compatibilities between two instantiations of
Grothendieck's collapse, not statements of a tagged result; [Stacks, Tag 01XK] carries its own
where the collapse is built.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.AffineBase

variable {Dc A B C : Type*} [Category* Dc] [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C] [EnoughInjectives A]
  (E : Dc ⥤ A) (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] (n : ℕ)

/-! ### Postcomposing the outer functor -/

section Postcomposition

variable {C' : Type*} [Category* C'] [Abelian C'] (R : C ⥤ C') [R.Additive]

/-- **The canonical derived transport the postcomposition square below is applied at, read on the
chosen injective resolution.** For `R` exact, `Stacks.Cohomology.ModuleComparison`
`.rightDerivedCompIso` at the identity comparison `(F ⋙ G) ⋙ R ≅ F ⋙ G ⋙ R` is the comparison
`Rⁿ(F ⋙ G) ⋙ R ≅ Rⁿ(F ⋙ G ⋙ R)`, and its component at `M` is
`CategoryTheory.ShortComplex.mapHomologyIso` for `R` on the degree-`n` short complex of the image
under `G` of the image under `F` of the chosen resolution, conjugated by
`CategoryTheory.InjectiveResolution.isoRightDerivedObj`.

This is exactly the hypothesis `hσ` of `rightDerivedCompNatIso_postcomp_square` below, so a
consumer that takes `σ` to be this comparison has `hσ` for free. It is
`Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app`, which is `rfl`, with its
middle factor replaced by `mapComplexHomologyIso_refl_hom_app`; the short complex is written in
the `((F[I]).sc n).map G` spelling the square carries rather than the `((F ⋙ G)[I]).sc n` one
that lemma produces, the two being definitionally equal and distinct keys. -/
theorem rightDerivedCompIso_refl_hom_app_mapHomologyIso [R.PreservesHomology] (M : A) :
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (F ⋙ G) R (F ⋙ G ⋙ R)
          (Iso.refl _) n).hom.app M =
      R.map ((injectiveResolution M).isoRightDerivedObj (F ⋙ G) n).hom ≫
        (((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution M).cocomplex).sc n).map G).mapHomologyIso R).inv ≫
          ((injectiveResolution M).isoRightDerivedObj (F ⋙ G ⋙ R) n).inv :=
  congrArg
    (fun x => R.map ((injectiveResolution M).isoRightDerivedObj (F ⋙ G) n).hom ≫ x ≫
      ((injectiveResolution M).isoRightDerivedObj (F ⋙ G ⋙ R) n).inv)
    (mapComplexHomologyIso_refl_hom_app (F ⋙ G) R n (injectiveResolution M).cocomplex)

/-- **Grothendieck's collapse at `G ⋙ R` is `R` of the collapse at `G`.** For `E : Dc ⥤ A`, an
additive `F : A ⥤ B`, additive `G : B ⥤ C` and `R : C ⥤ C'`, a degree `n` and an object `Z`, the
image under `R` of the component at `Z` of
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` at the pair `(F, G)`, followed by the
derived transport `σ : Rⁿ(F ⋙ G) ⋙ R ⟶ Rⁿ(F ⋙ G ⋙ R)`, is the component at `Z` of the collapse
at the pair `(F, G ⋙ R)`.

`σ` is hoisted onto a variable fixed by `hσ`, its reading on the chosen injective resolution of
`E Z`; a caller takes `σ` to be that composite, for which `hσ` is `rfl`.

**Nothing is assumed** of `E`, of `Z` or of `n`, and nothing of `F`, `G` or `R` beyond
additivity. Besides the two collapses' own pointwise hypotheses `hG` and `hGR`, the only thing
asked is the pointwise hypothesis for `R` at the image short complex, which the composition law
for `CategoryTheory.ShortComplex.mapHomologyIso` needs and which is free when `R` is exact. -/
theorem rightDerivedCompNatIso_postcomp_square
    (hG : ∀ Z : Dc, G.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (hGR : ∀ Z : Dc, (G ⋙ R).PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (σ : (F ⋙ G).rightDerived n ⋙ R ⟶ (F ⋙ G ⋙ R).rightDerived n)
    (Z : Dc)
    [G.PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj Z)).cocomplex).sc n)]
    [(G ⋙ R).PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj Z)).cocomplex).sc n)]
    [R.PreservesLeftHomologyOf
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n).map G)]
    (hσ : σ.app (E.obj Z) =
      R.map ((injectiveResolution (E.obj Z)).isoRightDerivedObj (F ⋙ G) n).hom ≫
        (((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution (E.obj Z)).cocomplex).sc n).map G).mapHomologyIso R).inv ≫
          ((injectiveResolution (E.obj Z)).isoRightDerivedObj (F ⋙ G ⋙ R) n).inv) :
    R.map ((rightDerivedCompNatIso E F G n hG).hom.app Z) ≫ σ.app (E.obj Z) =
      (rightDerivedCompNatIso E F (G ⋙ R) n hGR).hom.app Z := by
  rw [hσ, rightDerivedCompNatIso_hom_app, rightDerivedCompNatIso_hom_app]
  exact map_comp₃_cancel_mid R _ _ _ _ (Iso.inv_hom_id _)
    (ShortComplex.mapHomologyIso_comp_inv
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n) G R).symm _

end Postcomposition

/-! ### Transporting along an isomorphism of the outer functor -/

section NatIso

variable (G' : B ⥤ C) [G'.Additive]

omit [EnoughInjectives A] in
/-- The hinge of the square below, at a variable complex: the naturality in the functor of
`CategoryTheory.ShortComplex.mapHomologyIso`, read at the degree-`n` short complex of the image
under `F` of a complex of `A` and at the transformation `α` whiskered by `F`. Split off because
the goal the square leaves carries the complex's homology in two definitionally equal spellings,
so the identity has to be supplied as a term at variables. -/
private theorem mapHomologicalComplex_whiskerLeft_square (α : G ≅ G')
    (K : HomologicalComplex A (ComplexShape.up ℕ))
    [G.PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n)]
    [G'.PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n)] :
    α.hom.app ((HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≫
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n).mapHomologyIso G').inv =
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n).mapHomologyIso G).inv ≫
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft F α.hom)
            (ComplexShape.up ℕ)).app K) :=
  ShortComplex.mapHomologyIso_inv_natTrans
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n) α.hom

/-- **Grothendieck's collapse transported along a natural isomorphism of the outer functor.** For
`E : Dc ⥤ A`, an additive `F : A ⥤ B`, additive `G, G' : B ⥤ C`, an isomorphism `α : G ≅ G'`, a
degree `n` and an object `Z`, the component at `Z` of
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` at the pair `(F, G)`, followed by the
derived transport `ρ : Rⁿ(F ⋙ G) ⟶ Rⁿ(F ⋙ G')`, is `α` at `(RⁿF)(E Z)` followed by the component
at `Z` of the collapse at the pair `(F, G')`.

`ρ` is hoisted onto a variable fixed by `hρ`, its reading on the chosen injective resolution of
`E Z` — the degree-`n` homology of `α` whiskered by `F` and applied termwise to that resolution,
conjugated by the two `CategoryTheory.InjectiveResolution.isoRightDerivedObj`.  A caller takes
`ρ` to be that composite, for which `hρ` is `rfl`.

**Nothing is assumed** of `E`, of `Z` or of `n`, and nothing of `F`, `G` or `G'` beyond
additivity: the two collapses' own pointwise hypotheses `hG` and `hG'` are all that is asked, and
in particular neither functor need be exact. -/
theorem rightDerivedCompNatIso_natIso_square (α : G ≅ G')
    (hG : ∀ Z : Dc, G.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (hG' : ∀ Z : Dc, G'.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (ρ : (F ⋙ G).rightDerived n ⟶ (F ⋙ G').rightDerived n)
    (Z : Dc)
    [G.PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj Z)).cocomplex).sc n)]
    [G'.PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj Z)).cocomplex).sc n)]
    (hρ : ρ.app (E.obj Z) =
      ((injectiveResolution (E.obj Z)).isoRightDerivedObj (F ⋙ G) n).hom ≫
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) n).map
          ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft F α.hom)
            (ComplexShape.up ℕ)).app (injectiveResolution (E.obj Z)).cocomplex) ≫
          ((injectiveResolution (E.obj Z)).isoRightDerivedObj (F ⋙ G') n).inv) :
    (rightDerivedCompNatIso E F G n hG).hom.app Z ≫ ρ.app (E.obj Z) =
      α.hom.app ((F.rightDerived n).obj (E.obj Z)) ≫
        (rightDerivedCompNatIso E F G' n hG').hom.app Z := by
  rw [hρ, rightDerivedCompNatIso_hom_app, rightDerivedCompNatIso_hom_app]
  exact comp_conj_cancel_square (Iso.inv_hom_id _)
    (α.hom.naturality ((injectiveResolution (E.obj Z)).isoRightDerivedObj F n).hom).symm
    (mapHomologicalComplex_whiskerLeft_square F G n G' α
      (injectiveResolution (E.obj Z)).cocomplex)

end NatIso

end Stacks.Cohomology.AffineBase

end
