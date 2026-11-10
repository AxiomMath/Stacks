module

public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareLocalization

/-!
# The derived base-change comparison, extended along the target corners of a square

Let `R → A` and `R → R'`, `A → A'`, `R' → A'` be a commuting square of commutative rings. Tag
065Z attaches to it a comparison `K ⊗ᴸ_R R' ⟶ (K ⊗ᴸ_A A')|_{R'}`, natural in `K ∈ D(A)`:
`RingTheory.TorIndependence.derivedBaseChangeComparison`.

Stack a second square below the first:

```
R  ---> A
|       |
v       v
R' ---> A'
|       |
v       v
R₃ ---> A₃
```

The outer rectangle `(R, A, R₃, A₃)` is again a commuting square, so it has a comparison of its
own, and this file identifies it: it is the comparison of the top square *extended* along
`R' → R₃`, followed by the comparison of the bottom square, under the composition isomorphisms
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` of derived extension of
scalars along the two outer edges `R → R' → R₃` and `A → A' → A₃`.

This is the law that moves the *target* corners of a square, dual to
`RingTheory.TorIndependence.squareComparison_localized`, which moves the source corners. The
affine reduction of Tag 0DJ8 needs both: the cube relating the four coordinate rings of a chart
to the four local rings at a point of `U'` is traversed by extending `R'` and `A'` to `R'_{p'}`
and `A'_{q'}` — that is what is proved here — and contracting `R` and `A` afterwards.

## Main definitions

* `RingTheory.TorIndependence.squareComparisonUnderivedComplex`: the underived comparison of a
  square, read degreewise on a complex, with both ends pinned to the spelling that iterates.
* `RingTheory.TorIndependence.pastedComparison`: the comparison of the top square extended along
  `R' → R₃` and followed by the comparison of the bottom square.

## Main results

* `RingTheory.TorIndependence.pastedSquare_comm`: the outer rectangle commutes.
* `RingTheory.TorIndependence.squareComparison_counit`: the counit equation of a single square,
  with the two coherence identities of
  `RingTheory.TorIndependence.squareComparison_fac_app` absorbed into
  `RingTheory.TorIndependence.squareComparisonUnderivedComplex`.
* `RingTheory.TorIndependence.squareComparison_pasted`: the comparison of the outer rectangle is
  `RingTheory.TorIndependence.pastedComparison`.
* `RingTheory.TorIndependence.pastedUnderived_compat` and
  `RingTheory.TorIndependence.pastedUnderived_compat_app`: the degreewise statement about the
  three UNDERIVED comparisons that the identification rests on -- both composites send `1 ⊗ x`
  to `1 ⊗ x`.

## Implementation notes

The proof is a uniqueness argument. Both sides are natural transformations into `- ⊗ᴸ_A A₃` read
over `R₃`, which is a total left derived functor, so they agree as soon as they agree after the
comparison with degreewise extension of scalars; and there the three counit equations and the two
compatibilities
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_comparison` reduce the
statement to a degreewise one about underived comparisons.

`RingTheory.TorIndependence.squareComparison_fac_app` states the counit equation with the two
coherence isomorphisms `Functor.mapHomologicalComplexCompIso (Iso.refl _)` that relate
`(F ⋙ G).mapHomologicalComplex` to `F.mapHomologicalComplex ⋙ G.mapHomologicalComplex` left
visible. They are identities, but the two spellings of their ends are not interchangeable by
`rw` or `simp`, and three counit equations composed in sequence need the end of one to be the
start of the next. `RingTheory.TorIndependence.squareComparisonUnderivedComplex` absorbs both
coherences, so that every statement below is written in the single spelling
`G.mapHomologicalComplex.obj (F.mapHomologicalComplex.obj P)` and the chase goes through.

The model of the derived category is a binder `[HasDerivedCategory.{w} (ModuleCat.{u} ·)]` for
each of the six rings, not `HasDerivedCategory.standard`: a statement proved at one model says
nothing about another, and the consumers of Tag 0DJ8 work at a locally small model.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

universe u w

namespace RingTheory.TorIndependence

section OneSquare

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
  (a : R →+* A) (b : R →+* R') (c : A →+* A') (d : R' →+* A')
  (sq : c.comp a = d.comp b)

/-- **The underived comparison of Tag 065Z, read degreewise on a complex**, with both ends
pinned: its source is the degreewise extension to `R'` of the degreewise restriction to `R` of
`P`, and its target the degreewise restriction to `R'` of the degreewise extension to `A'`, both
spelled as one `CategoryTheory.Functor.mapHomologicalComplex` applied to another. The two
coherence identities relating those spellings to
`(F ⋙ G).mapHomologicalComplex` are absorbed here. -/
public abbrev squareComparisonUnderivedComplex (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendScalars.{u, u, u} b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      ((ModuleCat.restrictScalars.{u} d).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, u} c).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  (Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.restrictScalars.{u} a ⋙ ModuleCat.extendScalars.{u, u, u} b))
        (ComplexShape.up ℤ)).hom.app P ≫
    (NatTrans.mapHomologicalComplex (squareComparisonUnderived.{u, w} a b c d sq)
        (ComplexShape.up ℤ)).app P ≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.extendScalars.{u, u, u} c ⋙ ModuleCat.restrictScalars.{u} d))
        (ComplexShape.up ℤ)).inv.app P

/-- **The counit equation of the derived base-change comparison of a square.** This is
`RingTheory.TorIndependence.squareComparison_fac_app` with the two coherence identities absorbed
into `RingTheory.TorIndependence.squareComparisonUnderivedComplex`, so that the two ends are in
the spelling that composes with the counit equation of a second square stacked on the first. -/
public theorem squareComparison_counit (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (squareComparison.{u, w} a b c d sq).app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} d).mapDerivedCategory.map
          (extendComparisonApp.{u, w} c P) ≫
        (ModuleCat.restrictScalars.{u} d).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} c).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (totalDerivedExtensionScalars.{u, u, u} b).functor.map
          ((ModuleCat.restrictScalars.{u} a).mapDerivedCategoryFactors.hom.app P) ≫
        extendComparisonApp.{u, w} b
            (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (squareComparisonUnderivedComplex.{u, w} a b c d sq P) := by
  have h := congrArg (fun z => z ≫ DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (ModuleCat.extendScalars.{u, u, u} c ⋙ ModuleCat.restrictScalars.{u} d))
        (ComplexShape.up ℤ)).inv.app P)) (squareComparison_fac_app.{u, w} a b c d sq P)
  simpa only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id,
    squareComparisonUnderivedComplex] using h

end OneSquare

section Pasted

variable {R A R' A' R₃ A₃ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₃] [CommRing A₃]
  (a : R →+* A) (b : R →+* R') (c : A →+* A') (d : R' →+* A')
  (e : R' →+* R₃) (v : A' →+* A₃) (t : R₃ →+* A₃)
  (sq : c.comp a = d.comp b) (sqb : v.comp d = t.comp e)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
  [HasDerivedCategory.{w} (ModuleCat.{u} R₃)] [HasDerivedCategory.{w} (ModuleCat.{u} A₃)]

omit [HasDerivedCategory (ModuleCat R)] [HasDerivedCategory (ModuleCat A)]
  [HasDerivedCategory (ModuleCat R')] [HasDerivedCategory (ModuleCat A')]
  [HasDerivedCategory (ModuleCat R₃)] [HasDerivedCategory (ModuleCat A₃)] in
include sq sqb in
/-- The outer rectangle of two stacked commuting squares of rings commutes. -/
public theorem pastedSquare_comm : (v.comp c).comp a = t.comp (e.comp b) := by
  have h1 := DFunLike.congr_fun sq
  have h2 := DFunLike.congr_fun sqb
  ext r
  change v (c (a r)) = t (e (b r))
  rw [show c (a r) = d (b r) from h1 r]
  exact h2 (b r)

/-- **The comparison of the top square, extended along the target corners.** The Tag 065Z
comparison of `(R, A, R', A')` is pushed along `R' → R₃` by derived extension of scalars and then
followed by the Tag 065Z comparison of the bottom square `(R', A', R₃, A₃)`; the two composition
isomorphisms of derived extension of scalars put the result between the two functors that the
comparison of the outer rectangle connects. -/
public abbrev pastedComparison :
    (ModuleCat.restrictScalars.{u} a).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} (e.comp b)).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} (v.comp c)).functor ⋙
        (ModuleCat.restrictScalars.{u} t).mapDerivedCategory :=
  Functor.whiskerLeft ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory)
      (totalDerivedExtensionScalarsComp.{u, u} b e).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (squareComparison.{u, w} a b c d sq)
        (totalDerivedExtensionScalars.{u, u, u} e).functor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((totalDerivedExtensionScalars.{u, u, u} c).functor)
          (squareComparison.{u, w} d e v t sqb) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (totalDerivedExtensionScalarsComp.{u, u} c v).hom
          ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory)

/-- **The underived heart of the pasting law, at a module.** The underived comparison of Tag 065Z
at the outer rectangle is the comparison of the top square extended along `R' → R₃`, followed by
the comparison of the bottom square, read between the two scalar-tower isomorphisms of underived
extension of scalars. Both composites send `1 ⊗ m` to `1 ⊗ m`: the underived comparison sends
`r' ⊗ m` to `d r' ⊗ m` at each of the three squares, and each scalar-tower isomorphism takes
`1 ⊗ m` to `1 ⊗ (1 ⊗ m)`.

The four readings of `M` share one underlying group, but a tensor product written over one of
them does not carry the module structure of another, so the element is rebound at the reading it
is used at -- a type ascription is not enough, it leaves the original instances in place. Every
step is taken with `congrArg` rather than `rw`: a goal about an element of a
`ModuleCat.restrictScalars`-wrapped tensor product is not type-correct at the transparency `rw`
and `simp` work at, which is what blocks every rewriting tactic here. -/
public theorem pastedUnderived_compat_app (M : ModuleCat.{u} A) :
    (squareComparisonUnderived.{u, w} a (e.comp b) (v.comp c) t
          (pastedSquare_comm a b c d e v t sq sqb)).app M =
      (ModuleCat.extendScalarsComp.{u, u} b e).hom.app
          ((ModuleCat.restrictScalars.{u} a).obj M) ≫
        (ModuleCat.extendScalars.{u, u, u} e).map
            ((squareComparisonUnderived.{u, w} a b c d sq).app M) ≫
          (squareComparisonUnderived.{u, w} d e v t sqb).app
              ((ModuleCat.extendScalars.{u, u, u} c).obj M) ≫
            (ModuleCat.restrictScalars.{u} t).map
              ((ModuleCat.extendScalarsComp.{u, u} c v).inv.app M) := by
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  let mA : (M : Type u) := m
  have hout := squareComparisonUnderived_tmul.{u, w} a (e.comp b) (v.comp c) t
    (pastedSquare_comm a b c d e v t sq sqb) M (1 : R₃) mA
  have ht : t (1 : R₃) = (1 : A₃) := map_one t
  have hd : d (1 : R') = (1 : A') := map_one d
  have h1 := ModuleCat.extendScalarsComp_hom_app_one_tmul b e
    ((ModuleCat.restrictScalars.{u} a).obj M) m
  have h2 := squareComparisonUnderived_tmul.{u, w} a b c d sq M (1 : R') mA
  have h3 := squareComparisonUnderived_tmul.{u, w} d e v t sqb
    ((ModuleCat.extendScalars.{u, u, u} c).obj M) (1 : R₃) ((1 : A') ⊗ₜ[A, c] mA)
  have h4 := ModuleCat.extendScalarsComp_hom_app_one_tmul c v M mA
  have hhi := ConcreteCategory.congr_hom
    ((ModuleCat.extendScalarsComp.{u, u} c v).hom_inv_id_app M)
    ((1 : A₃) ⊗ₜ[A, v.comp c] mA)
  refine Eq.trans (b := (1 : A₃) ⊗ₜ[A, v.comp c] mA)
    (hout.trans (congrArg (fun z : A₃ => z ⊗ₜ[A, v.comp c] mA) ht)) (Eq.symm ?_)
  refine Eq.trans (congrArg (fun y =>
      ((ModuleCat.restrictScalars.{u} t).map
            ((ModuleCat.extendScalarsComp.{u, u} c v).inv.app M)).hom
          (((squareComparisonUnderived.{u, w} d e v t sqb).app
              ((ModuleCat.extendScalars.{u, u, u} c).obj M)).hom
            (((ModuleCat.extendScalars.{u, u, u} e).map
              ((squareComparisonUnderived.{u, w} a b c d sq).app M)).hom y))) h1) ?_
  refine Eq.trans (congrArg (fun z : ((ModuleCat.restrictScalars.{u} d).obj
        ((ModuleCat.extendScalars.{u, u, u} c).obj M) : Type u) =>
      ((ModuleCat.restrictScalars.{u} t).map
            ((ModuleCat.extendScalarsComp.{u, u} c v).inv.app M)).hom
          (((squareComparisonUnderived.{u, w} d e v t sqb).app
              ((ModuleCat.extendScalars.{u, u, u} c).obj M)).hom
            ((1 : R₃) ⊗ₜ[R', e] z))) h2) ?_
  refine Eq.trans (congrArg (fun z : A' =>
      ((ModuleCat.restrictScalars.{u} t).map
            ((ModuleCat.extendScalarsComp.{u, u} c v).inv.app M)).hom
          (((squareComparisonUnderived.{u, w} d e v t sqb).app
              ((ModuleCat.extendScalars.{u, u, u} c).obj M)).hom
            ((1 : R₃) ⊗ₜ[R', e] (z ⊗ₜ[A, c] mA)))) hd) ?_
  refine Eq.trans (congrArg (fun y =>
      ((ModuleCat.restrictScalars.{u} t).map
        ((ModuleCat.extendScalarsComp.{u, u} c v).inv.app M)).hom y) h3) ?_
  refine Eq.trans (congrArg (fun z : A₃ =>
      ((ModuleCat.restrictScalars.{u} t).map
          ((ModuleCat.extendScalarsComp.{u, u} c v).inv.app M)).hom
        (z ⊗ₜ[A', v] ((1 : A') ⊗ₜ[A, c] mA))) ht) ?_
  exact (congrArg (fun y => ((ModuleCat.extendScalarsComp.{u, u} c v).inv.app M).hom y)
    h4).symm.trans hhi

/-- **The underived heart of the pasting law**, read degreewise on a complex: this is exactly
what `RingTheory.TorIndependence.squareComparison_pasted_of_compat` asks for, and it holds by
`RingTheory.TorIndependence.pastedUnderived_compat_app` in each degree.

Every structural step between the two -- the degreewise components of the two scalar-tower
isomorphisms and the coherence identities that
`RingTheory.TorIndependence.squareComparisonUnderivedComplex` carries -- is the identity on
elements, so the degreewise statement is the module statement verbatim. -/
public theorem pastedUnderived_compat (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    squareComparisonUnderivedComplex.{u, w} a (e.comp b) (v.comp c) t
        (pastedSquare_comm a b c d e v t sq sqb) P =
      (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp.{u, u} b e).symm
          (ComplexShape.up ℤ)).inv.app
          (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        ((ModuleCat.extendScalars.{u, u, u} e).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (squareComparisonUnderivedComplex.{u, w} a b c d sq P) ≫
          squareComparisonUnderivedComplex.{u, w} d e v t sqb
              (((ModuleCat.extendScalars.{u, u, u} c).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            ((ModuleCat.restrictScalars.{u} t).mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Functor.mapHomologicalComplexCompIso
                (ModuleCat.extendScalarsComp.{u, u} c v).symm
                (ComplexShape.up ℤ)).hom.app P) := by
  ext i : 1
  exact ModuleCat.ExtendScalars.hom_ext fun m =>
    ConcreteCategory.congr_hom
      (pastedUnderived_compat_app.{u, w} a b c d e v t sq sqb (P.X i)) _

include sq sqb in
/-- **The comparison of the outer rectangle, granted the degreewise statement.** -/
public theorem squareComparison_pasted_of_compat
    (hU : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ,
      squareComparisonUnderivedComplex.{u, w} a (e.comp b) (v.comp c) t
          (pastedSquare_comm a b c d e v t sq sqb) P =
        (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp.{u, u} b e).symm
            (ComplexShape.up ℤ)).inv.app
            (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          ((ModuleCat.extendScalars.{u, u, u} e).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (squareComparisonUnderivedComplex.{u, w} a b c d sq P) ≫
            squareComparisonUnderivedComplex.{u, w} d e v t sqb
                (((ModuleCat.extendScalars.{u, u, u} c).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P) ≫
              ((ModuleCat.restrictScalars.{u} t).mapHomologicalComplex (ComplexShape.up ℤ)).map
                ((Functor.mapHomologicalComplexCompIso
                  (ModuleCat.extendScalarsComp.{u, u} c v).symm
                  (ComplexShape.up ℤ)).hom.app P)) :
    squareComparison.{u, w} a (e.comp b) (v.comp c) t
        (pastedSquare_comm a b c d e v t sq sqb) =
      pastedComparison.{u, w} a b c d e v t sq sqb := by
  have hLD :=
    @CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp.{u, u, u}
      A A₃ _ _ (v.comp c) _ _ (totalDerivedExtensionScalars.{u, u, u} (v.comp c)).functor
      (totalDerivedExtensionScalars.{u, u, u} (v.comp c)).comparison
      (totalDerivedExtensionScalars.{u, u, u} (v.comp c)).isLeftDerived _ _
      ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory)
  refine @Functor.leftDerived_ext _ _ _ _ _ _ _ _ _ _ _ _ hLD _ _ _ ?_
  ext P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp, Category.assoc,
    Functor.comp_obj]
  change (squareComparison.{u, w} a (e.comp b) (v.comp c) t
          (pastedSquare_comm a b c d e v t sq sqb)).app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map
          (extendComparisonApp.{u, w} (v.comp c) P) =
      (totalDerivedExtensionScalarsComp.{u, u} b e).inv.app
          ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        (totalDerivedExtensionScalars.{u, u, u} e).functor.map
            ((squareComparison.{u, w} a b c d sq).app (DerivedCategory.Q.obj P)) ≫
          (squareComparison.{u, w} d e v t sqb).app
              ((totalDerivedExtensionScalars.{u, u, u} c).functor.obj
                (DerivedCategory.Q.obj P)) ≫
            (ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map
                ((totalDerivedExtensionScalarsComp.{u, u} c v).hom.app
                  (DerivedCategory.Q.obj P)) ≫
              (ModuleCat.restrictScalars.{u} t).mapDerivedCategory.map
                (extendComparisonApp.{u, w} (v.comp c) P)
  rw [← Iso.cancel_iso_hom_right _ _
    ((ModuleCat.restrictScalars.{u} t).mapDerivedCategoryFactors.app
      (((ModuleCat.extendScalars.{u, u, u} (v.comp c)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P))]
  simp only [Iso.app_hom, Category.assoc]
  rw [squareComparison_counit.{u, w} a (e.comp b) (v.comp c) t
    (pastedSquare_comm a b c d e v t sq sqb) P]
  have hcv : (totalDerivedExtensionScalars.{u, u, u} v).functor.map
          (extendComparisonApp.{u, w} c P) ≫
        extendComparisonApp.{u, w} v
            (((ModuleCat.extendScalars.{u, u, u} c).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
              (ModuleCat.extendScalarsComp.{u, u} c v).symm (ComplexShape.up ℤ)).hom.app P) =
      (totalDerivedExtensionScalarsComp.{u, u} c v).hom.app (DerivedCategory.Q.obj P) ≫
        extendComparisonApp.{u, w} (v.comp c) P :=
    totalDerivedExtensionScalarsComp_comparison.{u, u} c v P
  have hcv' := congrArg ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory).map hcv
  simp only [Functor.map_comp] at hcv'
  rw [← reassoc_of% hcv']
  have hn1 := (ModuleCat.restrictScalars.{u} t).mapDerivedCategoryFactors.hom.naturality
    ((Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp.{u, u} c v).symm
      (ComplexShape.up ℤ)).hom.app P)
  simp only [Functor.comp_map, Functor.comp_obj] at hn1
  rw [hn1]
  have hbnat := (squareComparison.{u, w} d e v t sqb).naturality
    (extendComparisonApp.{u, w} c P)
  simp only [Functor.comp_map, Functor.comp_obj] at hbnat
  rw [← reassoc_of% hbnat, reassoc_of% (squareComparison_counit.{u, w} d e v t sqb
    (((ModuleCat.extendScalars.{u, u, u} c).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))]
  have htop := congrArg (totalDerivedExtensionScalars.{u, u, u} e).functor.map
    (squareComparison_counit.{u, w} a b c d sq P)
  simp only [Functor.map_comp (totalDerivedExtensionScalars.{u, u, u} e).functor] at htop
  rw [reassoc_of% htop]
  have hcnat : (totalDerivedExtensionScalars.{u, u, u} e).functor.map
          (DerivedCategory.Q.map (squareComparisonUnderivedComplex.{u, w} a b c d sq P)) ≫
        extendComparisonApp.{u, w} e
          (((ModuleCat.restrictScalars.{u} d).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{u, u, u} c).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) =
      extendComparisonApp.{u, w} e
          (((ModuleCat.extendScalars.{u, u, u} b).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
            (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendScalars.{u, u, u} e).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            (squareComparisonUnderivedComplex.{u, w} a b c d sq P)) :=
    (totalDerivedExtensionScalars.{u, u, u} e).comparison.naturality
      (squareComparisonUnderivedComplex.{u, w} a b c d sq P)
  rw [reassoc_of% hcnat]
  have hΘnat := (totalDerivedExtensionScalarsComp.{u, u} b e).inv.naturality
    ((ModuleCat.restrictScalars.{u} a).mapDerivedCategoryFactors.hom.app P)
  simp only [Functor.comp_map, Functor.comp_obj] at hΘnat
  rw [← reassoc_of% hΘnat]
  have hbe : (totalDerivedExtensionScalars.{u, u, u} e).functor.map
          (extendComparisonApp.{u, w} b
            (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        extendComparisonApp.{u, w} e
            (((ModuleCat.extendScalars.{u, u, u} b).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso
                (ModuleCat.extendScalarsComp.{u, u} b e).symm (ComplexShape.up ℤ)).hom.app
              (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) =
      (totalDerivedExtensionScalarsComp.{u, u} b e).hom.app
          (DerivedCategory.Q.obj
            (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        extendComparisonApp.{u, w} (e.comp b)
          (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) :=
    totalDerivedExtensionScalarsComp_comparison.{u, u} b e
      (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have hbe' : (totalDerivedExtensionScalarsComp.{u, u} b e).inv.app
          (DerivedCategory.Q.obj
            (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        (totalDerivedExtensionScalars.{u, u, u} e).functor.map
            (extendComparisonApp.{u, w} b
              (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) ≫
          extendComparisonApp.{u, w} e
            (((ModuleCat.extendScalars.{u, u, u} b).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
              (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) =
      extendComparisonApp.{u, w} (e.comp b)
          (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
              (ModuleCat.extendScalarsComp.{u, u} b e).symm (ComplexShape.up ℤ)).inv.app
            (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) := by
    rw [← Iso.cancel_iso_hom_right _ _ (DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
          (ModuleCat.extendScalarsComp.{u, u} b e).symm (ComplexShape.up ℤ)).app
        (((ModuleCat.restrictScalars.{u} a).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)))]
    simp only [Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    rw [hbe, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [reassoc_of% hbe']
  rw [congrArg DerivedCategory.Q.map (hU P)]
  simp only [Functor.map_comp, Category.assoc]

include sq sqb in
/-- **The Tag 065Z comparison of a square, extended along its target corners.** Let
`(R, A, R', A')` be a commuting square of commutative rings and stack a second commuting square
`(R', A', R₃, A₃)` below it. The Tag 065Z comparison of the outer rectangle `(R, A, R₃, A₃)` is
the comparison of the top square pushed along `R' → R₃` by derived extension of scalars and then
followed by the comparison of the bottom square, under the composition isomorphisms
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` of derived extension of
scalars along `R → R' → R₃` and along `A → A' → A₃`.

Taking the bottom square to be `(R', A', R'_{p'}, A'_{q'})` at a prime `q'` of `A'` and its
preimage `p'` in `R'`, this moves the two *target* corners of the square to their localizations,
which is the step of the affine reduction of Tag 0DJ8 that
`RingTheory.TorIndependence.squareComparison_localized` — which moves the two *source* corners —
does not supply. -/
public theorem squareComparison_pasted :
    squareComparison.{u, w} a (e.comp b) (v.comp c) t
        (pastedSquare_comm a b c d e v t sq sqb) =
      pastedComparison.{u, w} a b c d e v t sq sqb :=
  squareComparison_pasted_of_compat.{u, w} a b c d e v t sq sqb
    (pastedUnderived_compat.{u, w} a b c d e v t sq sqb)

end Pasted

end RingTheory.TorIndependence

end
