module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBaseComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismExtendComposite

/-!
# Grothendieck's comparison against the `ℤ`-indexed homology comparison

`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` is Grothendieck's comparison
`R^n(G ∘ F) ≅ G ∘ R^n F` in the `ℕ`-indexing, with the homology-preservation hypothesis on `G`
asked only pointwise, and `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_hom_app` reads its
component as `CategoryTheory.ShortComplex.mapHomologyIso` conjugated by two components of
`HomotopyCategory.homologyFunctorFactors`. The edge morphism of an **unbounded** right derived
functor is built instead from
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparison` on a cochain
complex indexed by `ℤ`.

This file identifies the two. It is the residue of the `Gamma(V, -)`-exactness mirror of
[Stacks, Tag 01XK] — the statement left once the two model crossings, the comparison `θ` of the
iterated derived functors and the units of the derived functors have all been cancelled out of
that mirror, and the one statement in the reduction with no derived functor and no unit in it.

## Main results

* `rightDerivedIsoRes_comp_homologyComparison`: **Grothendieck's comparison is the `ℤ`-indexed
  homology comparison, conjugated by the two indexings.** The comparison of the two indexings of
  `R^n(G ∘ F)` at the object, the factorisation of the degree-`n` cohomology functor of the
  `ℤ`-indexing and the homology comparison of `G` on the image under `F` of the extended chosen
  injective resolution, equals `rightDerivedCompNatIso` inverted followed by `G` applied to the
  same two identifications for `F`.

  Both conjugating identifications are written out on either side rather than cancelled: each is
  invertible, but the two spellings of its endpoints — the homology of a complex and the
  homology computed in the homotopy category — are equal only after
  `HomotopyCategory.homologyFunctor` is unfolded, and that definition is `irreducible`.

## Implementation notes

*The chase is in three stages, and the middle one is where the two extensions meet.*
`Stacks.DerivedIndexing.extendMapHomologyIso_hom_comp_homologyFunctorFactors` turns either
indexing comparison into the factorisation of the `ℕ`-indexed cohomology functor followed by
`HomologicalComplex.extendHomologyIso` inverted and by the homology of
`Stacks.DerivedIndexing.mapExtendIso`; the leading factorisation is then common to the two sides
and is cancelled, and what remains relates the extension of `G` applied termwise to the image of
the resolution with `G` applied termwise to the extension of that image. That is
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.extendHomologyIso_comp_homologyComparison`, once
`Stacks.DerivedIndexing.mapExtendIso_comp` has split the comparison of the composite and the
naturality of the homology comparison has moved `G` across the remaining factor.

*Every cancellation is performed at variables of an abstract category.* The goals here carry two
spellings of the degree-`n` homology of `G ∘ F` applied termwise to the extended resolution —
`((F ⋙ G).mapHomologicalComplex _).obj _` and `(G.mapHomologicalComplex _).obj
((F.mapHomologicalComplex _).obj _)` — which are the same object definitionally and not
syntactically, so a rewrite cannot build its motive at the `implicit` transparency level. The
cancellations are therefore stated on plain morphisms and applied in argument position.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

namespace Stacks.Cohomology.AffineBase

/-! ### The cancellations, on variables -/

section Abstract

variable {C : Type*} [Category* C]

/-- **An isomorphism's inverse against a composite computing its forward morphism.** At
variables, so that the two definitionally equal spellings of an endpoint are reconciled in
argument position. -/
private theorem inv_comp_of_hom_comp_eq {P Q R : C} (i : P ≅ Q) {u : P ⟶ R} {v : Q ⟶ R}
    (hv : i.hom ≫ v = u) : i.inv ≫ u = v := by
  rw [← hv, Iso.inv_hom_id_assoc]

/-- **A mutually inverse pair cancelled out of the middle of a composite whose head is known.**
If `a ≫ b ≫ c = x ≫ y` and `c ≫ d = 𝟙`, then `x ≫ y ≫ d ≫ e = a ≫ b ≫ e`. At variables, with
the invertibility given on plain morphisms: the pair it is applied to is a functor's image of a
natural isomorphism's two components, and at variables the unifier meets each morphism directly
and reconciles the two definitionally equal spellings of an endpoint in argument position. -/
private theorem cancel_mid {P Q R S T U : C} {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S} {d : S ⟶ R}
    (hcd : c ≫ d = 𝟙 R) {e : R ⟶ T} {x : P ⟶ U} {y : U ⟶ S}
    (hab : a ≫ b ≫ c = x ≫ y) : x ≫ y ≫ d ≫ e = a ≫ b ≫ e := by
  rw [← Category.assoc x, ← hab]
  simp only [Category.assoc]
  rw [← Category.assoc c d e, hcd, Category.id_comp]

/-- **Two mutually inverse pairs cancelled off the tail of a composite.** At variables, with each
invertibility given on plain morphisms rather than as an `CategoryTheory.Iso`, so that the
components of two different natural isomorphisms are not identified by the unifier. -/
private theorem comp_cancel_two {P Q R S : C} (u : P ⟶ Q) {a : Q ⟶ R} {a' : R ⟶ Q}
    (ha : a ≫ a' = 𝟙 Q) {b : R ⟶ S} {b' : S ⟶ R} (hb : b ≫ b' = 𝟙 R) :
    (u ≫ a ≫ b) ≫ b' ≫ a' = u := by
  simp only [Category.assoc]
  rw [← Category.assoc b b' a', hb, Category.id_comp, ha, Category.comp_id]

/-- **The assembly of the residue, at variables.** The left-hand side's first two factors are
known (`hL`), the three remaining ones are the core identity (`hcore`), the right-hand side's
first two are Grothendieck's comparison against the `ℕ`-indexed factorisation (`hcomp`) and its
last two are the image under the outer functor of the left-hand side's first two (`hR`).

At variables, because the goal it closes carries two spellings of the degree-`n` homology of
`G ∘ F` applied termwise to the extended resolution and so is not type-correct at the `implicit`
transparency level at which a rewrite builds its motive. -/
private theorem assemble {P Q R S T U V W Z Y : C}
    {l₁ : P ⟶ Q} {l₂ : Q ⟶ R} {l₃ : R ⟶ S}
    {cf : P ⟶ T} {ei : T ⟶ U} {hm : U ⟶ R}
    {mhi : T ⟶ V} {gei : V ⟶ W} {ghm : W ⟶ S}
    {r₀ : P ⟶ Z} {gf : Z ⟶ V} {r₁ : Z ⟶ Y} {r₂ : Y ⟶ S}
    (hL : l₁ ≫ l₂ = cf ≫ ei ≫ hm)
    (hcore : ei ≫ hm ≫ l₃ = mhi ≫ gei ≫ ghm)
    (hcomp : r₀ ≫ gf = cf ≫ mhi)
    (hR : r₁ ≫ r₂ = gf ≫ gei ≫ ghm) :
    l₁ ≫ l₂ ≫ l₃ = r₀ ≫ r₁ ≫ r₂ := by
  rw [← Category.assoc l₁, hL, hR, ← Category.assoc r₀, hcomp]
  simp only [Category.assoc]
  rw [hcore]

/-- **A functor's image of a mutually inverse pair cancels.** Stated as a term, so that the
cancellation is checked at default transparency: the goal it closes carries the homology of a
complex in two spellings — `HomologicalComplex.homology` and the homology of the degree-`n` short
complex — which are equal only after the former is unfolded. -/
private theorem map_hom_inv_id {V W : Type*} [Category* V] [Category* W] (H : V ⥤ W) {P Q : V}
    (i : P ≅ Q) : H.map i.hom ≫ H.map i.inv = 𝟙 (H.obj P) :=
  (H.map_comp _ _).symm.trans ((congrArg H.map i.hom_inv_id).trans (H.map_id P))

end Abstract

/-! ### The residue -/

section CompositionResidue

variable {D A B C : Type*} [Category* D] [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C] [EnoughInjectives A]
  (E : D ⥤ A) (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [PreservesFiniteLimits G]
  (n : ℕ)

omit [EnoughInjectives A] in
/-- **The two extensions of `G ∘ F` applied termwise, compared on the homology comparison.** The
homology of `Stacks.DerivedIndexing.mapExtendIso` for the composite, followed by the homology
comparison of `G` at `F` applied termwise to the extended complex, is the homology of
`mapExtendIso` for `G` at the image of the complex, the homology comparison of `G` at the
extension of that image, and `G` applied to the homology of `mapExtendIso` for `F`.

This is `Stacks.DerivedIndexing.mapExtendIso_comp` followed by the naturality of the homology
comparison. -/
private theorem homologyMap_mapExtendIso_comp_homologyComparison (N : CochainComplex A ℕ) :
    HomologicalComplex.homologyMap
          (Stacks.DerivedIndexing.mapExtendIso (F ⋙ G) ComplexShape.embeddingUpNat N).hom
          (n : ℤ) ≫
        homologyComparison G ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (N.extend ComplexShape.embeddingUpNat)) (n : ℤ) =
      HomologicalComplex.homologyMap (Stacks.DerivedIndexing.mapExtendIso G
            ComplexShape.embeddingUpNat
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N)).hom (n : ℤ) ≫
        homologyComparison G (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extend
            ComplexShape.embeddingUpNat) (n : ℤ) ≫
          G.map (HomologicalComplex.homologyMap
            (Stacks.DerivedIndexing.mapExtendIso F ComplexShape.embeddingUpNat N).hom (n : ℤ)) := by
  rw [Stacks.DerivedIndexing.mapExtendIso_comp, HomologicalComplex.homologyMap_comp,
    Category.assoc, homologyComparison_naturality]

omit [EnoughInjectives A] in
/-- **The core of the residue: the homology comparison against
`CategoryTheory.ShortComplex.mapHomologyIso`.** With the extension identification of the image
complex inverted on the left, the homology of `Stacks.DerivedIndexing.mapExtendIso` for the
composite followed by the homology comparison of `G` is
`CategoryTheory.ShortComplex.mapHomologyIso` for `G` on the degree-`n` short complex of the image
of the complex, followed by `G` applied to the extension identification inverted and to the
homology of `mapExtendIso` for `F`.

`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.extendHomologyIso_comp_homologyComparison` supplies exactly the three leading factors against
`mapHomologyIso`, and the remaining factor of `F`'s extension is carried across by
`homologyMap_mapExtendIso_comp_homologyComparison`. -/
private theorem extendHomologyIso_inv_comp_homologyComparison (N : CochainComplex A ℕ)
    [G.PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).sc n)] :
    ((((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extendHomologyIso
          ComplexShape.embeddingUpNat
          (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv ≫
        HomologicalComplex.homologyMap
            (Stacks.DerivedIndexing.mapExtendIso (F ⋙ G) ComplexShape.embeddingUpNat N).hom
            (n : ℤ) ≫
          homologyComparison G ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (N.extend ComplexShape.embeddingUpNat)) (n : ℤ) =
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).sc n).mapHomologyIso G).hom ≫
        G.map ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extendHomologyIso
            ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv) ≫
          G.map (HomologicalComplex.homologyMap
            (Stacks.DerivedIndexing.mapExtendIso F ComplexShape.embeddingUpNat N).hom (n : ℤ)) := by
  refine inv_comp_of_hom_comp_eq _ ?_
  refine Eq.trans ?_ (homologyMap_mapExtendIso_comp_homologyComparison F G n N).symm
  exact cancel_mid
    (map_hom_inv_id G (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N).extendHomologyIso
      ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))))
    (extendHomologyIso_comp_homologyComparison ComplexShape.embeddingUpNat G
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N)
      (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ)))

/-- The comparison of the two indexings of `R^n K` at `X`, followed by the factorisation of the
`ℤ`-indexed cohomology functor at `K` applied termwise to the extended resolution of `X`, is the
`ℕ`-indexed factorisation followed by the extension identification inverted and the homology of
`mapExtendIso`. -/
private theorem rightDerivedIsoRes_hom_app_comp_homologyFunctorFactors
    {V : Type*} [Category* V] [Abelian V] (K : A ⥤ V) [K.Additive] (n : ℕ) (X : A) :
    (Stacks.DerivedIndexing.rightDerivedIsoRes K n).hom.app X ≫
        (HomotopyCategory.homologyFunctorFactors V (ComplexShape.up ℤ) (n : ℤ)).hom.app
          ((K.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((injectiveResolution X).cocomplex.extend ComplexShape.embeddingUpNat)) =
      (HomotopyCategory.homologyFunctorFactors V (ComplexShape.up ℕ) n).hom.app
          ((K.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex) ≫
        (((K.mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution X).cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv ≫
          HomologicalComplex.homologyMap (Stacks.DerivedIndexing.mapExtendIso K
            ComplexShape.embeddingUpNat (injectiveResolution X).cocomplex).hom (n : ℤ) :=
  (congrArg (· ≫ (HomotopyCategory.homologyFunctorFactors V (ComplexShape.up ℤ) (n : ℤ)).hom.app
      ((K.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((injectiveResolution X).cocomplex.extend ComplexShape.embeddingUpNat)))
    (Stacks.DerivedIndexing.rightDerivedIsoRes_hom_app_eq K X n)).trans
    (Stacks.DerivedIndexing.extendMapHomologyIso_hom_comp_homologyFunctorFactors K
      (injectiveResolution X).cocomplex n)

/-- **Grothendieck's comparison is the `ℤ`-indexed homology comparison, conjugated by the two
indexings.** For `E : D ⥤ A`, `F : A ⥤ B` and `G : B ⥤ C` additive with `G` left exact, a degree
`n` and the pointwise homology-preservation hypothesis `h` of
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso`, the composite

> the comparison of the two indexings of `R^n(G ∘ F)` at `E X`, the factorisation of the
> degree-`n` cohomology functor of the `ℤ`-indexing, and the homology comparison of `G` at `F`
> applied termwise to the extended chosen injective resolution of `E X`

equals `rightDerivedCompNatIso` inverted, followed by `G` applied to the comparison of the two
indexings of `R^n F` and to the same factorisation for `F`.

This is the statement left of the `Gamma(V, -)`-exactness mirror of [Stacks, Tag 01XK] once
every derived functor and every unit has been cancelled out of it. -/
public theorem rightDerivedIsoRes_comp_homologyComparison
    (h : ∀ X : D, G.PreservesLeftHomologyOf
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj X)).cocomplex).sc n))
    (X : D)
    [G.PreservesLeftHomologyOf (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution (E.obj X)).cocomplex).sc n)] :
    (Stacks.DerivedIndexing.rightDerivedIsoRes (F ⋙ G) n).hom.app (E.obj X) ≫
        (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (n : ℤ)).hom.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                ((injectiveResolution (E.obj X)).cocomplex.extend
                  ComplexShape.embeddingUpNat))) ≫
          homologyComparison G ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((injectiveResolution (E.obj X)).cocomplex.extend ComplexShape.embeddingUpNat))
            (n : ℤ) =
      (rightDerivedCompNatIso E F G n h).inv.app X ≫
        G.map ((Stacks.DerivedIndexing.rightDerivedIsoRes F n).hom.app (E.obj X)) ≫
          G.map ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (n : ℤ)).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((injectiveResolution (E.obj X)).cocomplex.extend
                ComplexShape.embeddingUpNat))) := by
  have hR : G.map ((Stacks.DerivedIndexing.rightDerivedIsoRes F n).hom.app (E.obj X)) ≫
        G.map ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) (n : ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((injectiveResolution (E.obj X)).cocomplex.extend
              ComplexShape.embeddingUpNat))) =
      G.map ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution (E.obj X)).cocomplex)) ≫
        G.map ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
              (injectiveResolution (E.obj X)).cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f n = (n : ℤ))).inv) ≫
          G.map (HomologicalComplex.homologyMap (Stacks.DerivedIndexing.mapExtendIso F
            ComplexShape.embeddingUpNat
            (injectiveResolution (E.obj X)).cocomplex).hom (n : ℤ)) := by
    exact (G.map_comp _ _).symm.trans ((congrArg G.map
      (rightDerivedIsoRes_hom_app_comp_homologyFunctorFactors F n (E.obj X))).trans
      ((G.map_comp _ _).trans (congrArg (G.map _ ≫ ·) (G.map_comp _ _))))
  have hcomp : (rightDerivedCompNatIso E F G n h).inv.app X ≫
        G.map ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution (E.obj X)).cocomplex)) =
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℕ) n).hom.app
          (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution (E.obj X)).cocomplex) ≫
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution (E.obj X)).cocomplex).sc n).mapHomologyIso G).hom := by
    refine inv_comp_of_hom_comp_eq ((rightDerivedCompNatIso E F G n h).app X) ?_
    rw [Iso.app_hom, rightDerivedCompNatIso_hom_app E F G n h X,
      Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution,
      Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution_inv]
    exact comp_cancel_two _
      (Iso.inv_hom_id ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj X)).cocomplex).sc n).mapHomologyIso G))
      (Iso.inv_hom_id_app (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℕ) n)
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution (E.obj X)).cocomplex))
  exact assemble (rightDerivedIsoRes_hom_app_comp_homologyFunctorFactors (F ⋙ G) n (E.obj X))
    (extendHomologyIso_inv_comp_homologyComparison F G n
      (injectiveResolution (E.obj X)).cocomplex)
    hcomp hR

end CompositionResidue

end Stacks.Cohomology.AffineBase

end
