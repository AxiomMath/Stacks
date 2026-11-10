module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonOnResolutions

/-!
# Grothendieck's comparison with a pointwise hypothesis, read on the chosen resolution

`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` is Grothendieck's comparison
`R^n(G ∘ F) ≅ G ∘ R^n F` with the homology-preservation hypothesis on `G` asked only of the
short complexes that occur, which is what makes it available for a `G` that is merely acyclic on
those objects — the shape [Stacks, Tag 01XK] needs.  It is built by `NatIso.ofComponents` whose
component is produced after unfolding `CategoryTheory.Functor.rightDerived` and
`HomotopyCategory.homologyFunctor`, so its component satisfies no equation on its face.

This file supplies that equation.  Nothing is redefined: the comparison is identified with a
composite of *named* canonical isomorphisms — `CategoryTheory.ShortComplex.mapHomologyIso`
conjugated by `CategoryTheory.InjectiveResolution.isoRightDerivedObj` at either end — and, when
`G` is exact, with the already pinnable
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`.

## Main results

* `rightDerivedCompNatIso_hom_app`: **the component of
  `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` through the chosen injective
  resolution.**  It is `CategoryTheory.ShortComplex.mapHomologyIso` for `G` on the degree-`n`
  short complex of the image under `F` of that resolution, conjugated by
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj` for `F` and for `F ⋙ G`.  This is the
  form a consumer composes with, and it holds under the pointwise hypothesis alone.
* `mapComplexHomologyIso_refl_hom_app`: the component of
  `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` at the identity comparison
  `F ⋙ G ≅ F ⋙ G` is that same `CategoryTheory.ShortComplex.mapHomologyIso`.
* `rightDerivedCompNatIso_eq_rightDerivedCompIso`: **the two comparisons agree.**  For `G`
  exact, `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` is
  `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at the identity comparison,
  whiskered by `E`.  So the two are one map, and the pointwise-hypothesis spelling is the
  extension of the exact one to a `G` that only preserves the homology that occurs.

## Implementation notes

*Why the identity factors are not cancelled by `rw` or `simp`.*  At the chosen injective
resolution `Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution` identifies
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` with the component of
`HomotopyCategory.homologyFunctorFactors`, which is an identity.  But its source and target are
equal only after unfolding `HomotopyCategory.homologyFunctor`, which is `irreducible`, so the
goal `G.map (𝟙 _) ≫ m ≫ 𝟙 _ = m` is not type-correct at the `implicit` transparency level at
which a rewrite builds its motive: `CategoryTheory.Functor.map_id` does not match, because the
two implicit endpoints of `G.map` are the two spellings.  The cure is `isLift_conj_cancel`, a
statement at the level of `CategoryTheory.Quotient.lift.isLift` — where no definition is
irreducible, both identities are `rfl`, and the cancellation is one `change` — applied in argument
position, where the elaborator checks against the goal at default transparency.  The same
pattern, one identity further out, closes `mapComplexHomologyIso_refl_hom_app` through
`comp_homologyMap_id`.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.AffineBase

/-! ### Two identity cancellations at variables level -/

/-- **A functor's image of the identity of `CategoryTheory.Quotient.lift.isLift`, and that of a
second one, cancel off either end of a morphism.** Both components are `𝟙` by `rfl` here, which
is what makes the cancellation available: the statement is about
`CategoryTheory.Quotient.lift`, where nothing is `irreducible`, and it is applied to
`HomotopyCategory.homologyFunctorFactors` after that definition has been unfolded. -/
private theorem isLift_conj_cancel {V W V' W' : Type*} [Category* V] [Category* W]
    [Category* V'] [Category* W'] {r : HomRel V} {r' : HomRel V'}
    (P : V ⥤ W) (hP : ∀ (x y : V) (f₁ f₂ : x ⟶ y), r f₁ f₂ → P.map f₁ = P.map f₂)
    (P' : V' ⥤ W') (hP' : ∀ (x y : V') (f₁ f₂ : x ⟶ y), r' f₁ f₂ → P'.map f₁ = P'.map f₂)
    (G : W ⥤ W') (K : V) (K' : V') (m : G.obj (P.obj K) ⟶ P'.obj K') :
    G.map ((Quotient.lift.isLift r P hP).hom.app K) ≫ m ≫
        (Quotient.lift.isLift r' P' hP').inv.app K' = m := by
  change G.map (𝟙 (P.obj K)) ≫ m ≫ 𝟙 (P'.obj K') = m
  rw [G.map_id, Category.id_comp, Category.comp_id]

/-- The homology of an identity of complexes cancels off the right of a morphism. Stated
separately so that the cancellation happens where the two endpoints of the identity are the one
spelling. -/
private theorem comp_homologyMap_id {V : Type*} [Category* V] [Preadditive V]
    [CategoryWithHomology V] {Z : V} (Y : HomologicalComplex V (ComplexShape.up ℕ)) (n : ℕ)
    (m : Z ⟶ Y.homology n) : m ≫ HomologicalComplex.homologyMap (𝟙 Y) n = m := by
  simp

/-! ### The component of the comparison -/

section Composition

variable {D A B C : Type*} [Category* D] [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C] [EnoughInjectives A]
  (E : D ⥤ A) (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] (n : ℕ)

/-- **The component of `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` through the chosen
injective resolution.** It is `CategoryTheory.ShortComplex.mapHomologyIso` for `G` on the
degree-`n` short complex of the image under `F` of the chosen injective resolution of `E.obj X`,
conjugated by `CategoryTheory.InjectiveResolution.isoRightDerivedObj` for `F` on the left and
for `F ⋙ G` on the right.

Only the pointwise hypothesis `h` is used, so this is available wherever the comparison itself
is. The conjugating factors are kept in the statement rather than cancelled: each is an identity
at the chosen resolution, but only after `HomotopyCategory.homologyFunctor` is unfolded, and
keeping them is what a consumer transporting the comparison to another resolution wants
anyway. -/
public theorem rightDerivedCompNatIso_hom_app
    (h : ∀ X : D, G.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj X)).cocomplex).sc n))
    (X : D)
    [G.PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj X)).cocomplex).sc n)] :
    (rightDerivedCompNatIso E F G n h).hom.app X =
      G.map ((injectiveResolution (E.obj X)).isoRightDerivedObj F n).hom ≫
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution (E.obj X)).cocomplex).sc n).mapHomologyIso G).inv ≫
          ((injectiveResolution (E.obj X)).isoRightDerivedObj (F ⋙ G) n).inv := by
  rw [Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution,
    Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution_inv]
  unfold HomotopyCategory.homologyFunctorFactors Functor.rightDerived
    Functor.rightDerivedToHomotopyCategory HomotopyCategory.homologyFunctor
  exact (isLift_conj_cancel (r := _root_.homotopic B (ComplexShape.up ℕ))
    (r' := _root_.homotopic C (ComplexShape.up ℕ))
    (HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n) _
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) n) _ G
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj X)).cocomplex)
    (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj X)).cocomplex) _).symm

omit [EnoughInjectives A] in
/-- **`Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` at the identity comparison is
`CategoryTheory.ShortComplex.mapHomologyIso`.** Its second factor is the degree-`n` homology of
`CategoryTheory.Functor.mapHomologicalComplexCompIso` at `Iso.refl (F ⋙ G)`, which is the
identity of the complex, so only the first factor survives. -/
public theorem mapComplexHomologyIso_refl_hom_app [G.PreservesHomology]
    (L : HomologicalComplex A (ComplexShape.up ℕ)) :
    (Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso F G (F ⋙ G)
        (Iso.refl (F ⋙ G)) n).hom.app L =
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).sc n).mapHomologyIso G).inv := by
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (ComplexShape.up ℕ)).hom.app L =
        𝟙 (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj L) := by
    ext i
    simp [Functor.mapHomologicalComplexCompIso]
  have hfac : (Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso F G (F ⋙ G)
        (Iso.refl (F ⋙ G)) n).hom.app L =
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).sc n).mapHomologyIso G).inv ≫
        HomologicalComplex.homologyMap ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (F ⋙ G)) (ComplexShape.up ℕ)).hom.app L) n := rfl
  rw [hfac, hid]
  exact comp_homologyMap_id (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj L) n _

/-- **The two comparisons have the same component.** For `G` exact the component at `X` of
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` is the component at `E.obj X` of
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at the identity comparison
`F ⋙ G ≅ F ⋙ G`: both are the same `CategoryTheory.ShortComplex.mapHomologyIso` conjugated by
the same pair of `CategoryTheory.InjectiveResolution.isoRightDerivedObj`. -/
public theorem rightDerivedCompNatIso_hom_app_eq_rightDerivedCompIso [G.PreservesHomology]
    (h : ∀ X : D, G.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj X)).cocomplex).sc n))
    (X : D) :
    (rightDerivedCompNatIso E F G n h).hom.app X =
      (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G (F ⋙ G)
        (Iso.refl (F ⋙ G)) n).hom.app (E.obj X) := by
  rw [rightDerivedCompNatIso_hom_app E F G n h X,
    Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app,
    mapComplexHomologyIso_refl_hom_app F G n]
  rfl

/-- **Grothendieck's comparison with the pointwise hypothesis agrees with the one for an exact
functor.** When `G` is exact, `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` is
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` at the identity comparison
`F ⋙ G ≅ F ⋙ G`, whiskered by `E`.

So the two spellings of `R^n(G ∘ F) ≅ G ∘ R^n F` are one map, and the pointwise-hypothesis one
is the extension of the pinnable one to a `G` that preserves only the homology that occurs. -/
public theorem rightDerivedCompNatIso_eq_rightDerivedCompIso [G.PreservesHomology]
    (h : ∀ X : D, G.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj X)).cocomplex).sc n)) :
    rightDerivedCompNatIso E F G n h =
      Functor.isoWhiskerLeft E (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G
        (F ⋙ G) (Iso.refl (F ⋙ G)) n) :=
  Iso.ext (NatTrans.ext (funext fun X =>
    rightDerivedCompNatIso_hom_app_eq_rightDerivedCompIso E F G n h X))

end Composition

end Stacks.Cohomology.AffineBase

end
