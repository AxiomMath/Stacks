module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08GW, with nothing assumed and with the canonical triangle

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` be its intersection, write `(-)|_Y` for restriction of modules
along the étale morphism `j_Y : Y ⟶ X` and `j_{Y,*}` for the direct image.  Stacks 08GW says
that

1. every sheaf of `𝒪_X`-modules `F` sits in a short exact sequence

   `0 ⟶ F ⟶ j_{U,*}F|_U ⊕ j_{V,*}F|_V ⟶ j_{P,*}F|_P ⟶ 0`,

2. every object `E` of the unbounded derived category `D(𝒪_X)` sits in a distinguished triangle

   `E ⟶ Rj_{U,*}E|_U ⊕ Rj_{V,*}E|_V ⟶ Rj_{P,*}E|_P ⟶ E[1]`.

`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforward` proves both for an
arbitrary choice of the extension-by-zero data `j_{Y!}` and, in part (2), of the right derived
functors `R_Y` of `j_{Y,*}((-)|_Y)`.  This module removes every one of those choices, so that
the two statements carrying the tag depend on nothing but the square itself:

* extension by zero is the one the library constructs,
  `AlgebraicGeometry.Space.etaleModuleLowerShriek`, with its adjunction
  `AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction` — exactly as Stacks 08GV is stated
  in `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag`;
* the three derived functors are the chosen total right derived functors
  `CategoryTheory.Functor.totalRightDerived` of the three `j_{Y,*}((-)|_Y)`, which exist by
  `AlgebraicGeometry.Space.hasRightDerivedFunctor_mapHomotopyCategory_modules`, with their
  canonical units `CategoryTheory.Functor.totalRightDerivedUnit`;
* and the maps of the triangle of part (2) are **not existentially quantified**: they are the
  derived unit `E ⟶ Rj_{Y,*}E|_Y` of the adjunction `(-)|_Y ⊣ j_{Y,*}` and the derived
  transformation of the comparison `j_{Y,*}F|_Y ⟶ j_{P,*}F|_P` of part (1).

## Main definitions

* `CategoryTheory.PushforwardMayerVietoris.rightDerivedCochainComparison`: Stacks 070K as a
  natural transformation `Q(Φ K) ⟶ RΦ(Q K)` of functors on cochain complexes, and
  `…rightDerivedCochainComparisonIso`: the isomorphism it is at a K-injective complex.
* `CategoryTheory.PushforwardMayerVietoris.derivedUnitOfNatTrans`: the natural map
  `𝟭 D(A) ⟶ RΦ` that a natural map `η : 𝟭 ⟶ Φ` induces on the derived category, for `RΦ` a
  right derived functor of `Φ`.  *No exactness of `Φ` is assumed*, which is exactly why this
  construction is needed: a non-exact `Φ` has no functor on derived categories, so `η` has no
  image under `CategoryTheory.NatTrans.mapDerivedCategory`.
* `AlgebraicGeometry.Space.edsLowerShriekAdjOpen`, `…Etale`, `…Inter`: the three adjunctions
  `j_{Y!} ⊣ (-)|_Y` of the square, for the extension by zero the library constructs.
* `AlgebraicGeometry.Space.edsDerivedRestrictPushOpen`, `…Etale`, `…Inter`: the three
  `Rj_{Y,*}((-)|_Y)`, and `…edsTotalRightDerivedUnitOpen`, `…Etale`, `…Inter` the canonical
  comparisons exhibiting them as right derived functors.  The four maps of the triangle of
  part (2) are `derivedUnitOfNatTrans` and `CategoryTheory.Functor.rightDerivedNatTrans` at
  these, and are written out in the statement rather than abbreviated; see the implementation
  notes.

## Main results

* `CategoryTheory.PushforwardMayerVietoris.exists_mem_distTriang_derivedUnitBiprod`: the
  abstract passage from part (1) to part (2) **with the canonical maps**.  A natural short exact
  sequence `0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0` of additive endofunctors of an abelian category
  with K-injective resolutions gives, at every object `E` of `D(A)`, a distinguished triangle
  whose first two maps are the derived units of `η_U`, `η_V` and the derived transformations of
  the two comparisons.
* `AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietorisLowerShriek`: **Stacks 08GW
  part (1)**, with nothing assumed.
* `AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek`:
  **Stacks 08GW part (2)**, with nothing assumed and with the canonical triangle.

## Implementation notes

*Why the canonical maps can be written down at all.*  The triangle of part (2) is produced from
a short exact sequence of cochain complexes on a K-injective representative `I` of `E`, so the
maps the construction hands over are attached to `I` and to the chosen isomorphism `Q(I) ≅ E`;
they are not formulas in `E`.  What identifies them with canonical maps is that both kinds of
map are *natural in `E`* and that their values at `Q(I)` are computed by Stacks 070K.  For the
second map the construction is Mathlib's `CategoryTheory.Functor.rightDerivedNatTrans` and the
computation is `rightDerivedCochainComparison_comp_rightDerivedNatTrans` below — the square
saying that the comparison of Stacks 070K is natural in the functor as well as in the complex.
For the first map there is nothing to use, because `Φ_Y` is not exact; `derivedUnitOfNatTrans`
is that missing construction, the unique lift along the localization `DerivedCategory.Q` of the
degreewise `η` followed by the comparison of Stacks 070K, and `derivedUnitOfNatTrans_app_Q` is
its value at `Q(K)`.

*Only the connecting map stays existentially quantified.*  The library attaches a connecting map
to a short exact sequence of cochain complexes, `DerivedCategory.triangleOfSESδ`, but not to an
object of `D(𝒪_X)`: transporting it to `E` uses the chosen representative, and no canonical
`Rj_{P,*}E|_P ⟶ E[1]` is constructed anywhere in this development, nor is one asserted by the
source, which says only that the triangle is distinguished.  So part (2) reads `∃ δ, …` and
everything else in it is a named map.  The same `δ` is existential in Stacks 08GV part (2),
`AlgebraicGeometry.Space.mayerVietoris_shortExact_and_mem_distTriang`.

*Where the sheafification hypotheses go.*  Stacks 08GV, and with it part (1) of Stacks 08GW,
needs abelian presheaves on the small étale site of `X` to be sheafifiable and the local
isomorphisms there to be the locally bijective maps.  Both are theorems,
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat`, and they
are installed as local instances here, exactly as in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag`.  The derived category is fixed
to `HasDerivedCategory.standard`, again as there, so that it is not a parameter either.

*Why the four maps are written out rather than abbreviated.*  A definition for any of them —
for the conjugate comparison `j_{U,*}F|_U ⟶ j_{P,*}F|_P` of part (1), or for the derived unit
and the derived comparison of part (2) — makes the unification of these statements against the
theorems of `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforward` exceed the
heartbeat limit, while the same statements with the terms written out elaborate at once.  That
is the same hazard the implementation notes of that module record for an `abbrev` of the
conjugate comparison, and the same resolution.

*Why the comparison of Stacks 070K is repeated here.*
`CategoryTheory.PushforwardMayerVietoris.kinjIso` of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisSections` is the same isomorphism,
and `…kinjIso_trans_hom_rightDerivedNatTrans` there is the same square.  That module cannot be
imported: its own imports break the synthesis of `Abelian` for the `𝒪_X`-modules at the
spelling `AlgebraicGeometry.Space.Modules.{u, u}` used throughout this chapter — the search
reaches a `CategoryTheory.SheafOfModules` instance whose module universe is a `max` and stops
at the universe constraint.  The repetition is of the statements only; the proofs are the same
two diagram chases.

## References

* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 0152](https://stacks.math.columbia.edu/tag/0152)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe w v u

namespace CategoryTheory.PushforwardMayerVietoris

/-! ### The comparison of Stacks 070K, naturally in the complex -/

section Comparison

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {Φ Ψ : A ⥤ A} [Φ.Additive] [Ψ.Additive]

/-- **Stacks 070K as a natural transformation.**  For `RΦ` a right derived functor of an
additive endofunctor `Φ`, with comparison `α`, the composite of `α` with the two structural
isomorphisms relating `DerivedCategory.Q` to `DerivedCategory.Qh` is a natural transformation
`Q(Φ K) ⟶ RΦ(Q K)`.  Stacks 070K is the statement that it is invertible at a K-injective
complex, which is `rightDerivedCochainComparisonIso` below. -/
def rightDerivedCochainComparison (Φ : A ⥤ A) [Φ.Additive]
    (RΦ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ) :
    Φ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RΦ :=
  Functor.whiskerLeft (Φ.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso A).inv ≫
    Functor.whiskerRight (Φ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (ComplexShape.up ℤ)) α ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom RΦ

/-- The component of `rightDerivedCochainComparison` at a complex `K` is the composite of the
inverse of `DerivedCategory.quotientCompQhIso`, the inverse of `mapHomotopyCategoryFactors`,
the component of `α` at the image of `K`, and `RΦ` applied to `DerivedCategory.quotientCompQhIso`.
-/
lemma rightDerivedCochainComparison_app (Φ : A ⥤ A) [Φ.Additive]
    (RΦ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ) (K : CochainComplex A ℤ) :
    (rightDerivedCochainComparison Φ RΦ α).app K =
      (DerivedCategory.quotientCompQhIso A).inv.app
          ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
            ((Φ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
          α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≫
            RΦ.map ((DerivedCategory.quotientCompQhIso A).hom.app K) :=
  rfl

/-- **Stacks 070K.**  A right derived functor of `Φ` is computed on a K-injective complex by `Φ`
itself: there the comparison `rightDerivedCochainComparison` is an isomorphism.

The hypothesis is phrased as invertibility of `α` on the image of the complex in the homotopy
category, which is the form in which Stacks 070K produces it
(`isIso_rightDerivedComparison_app_of_isKInjective`). -/
def rightDerivedCochainComparisonIso (Φ : A ⥤ A) [Φ.Additive]
    (RΦ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ) (I : CochainComplex A ℤ)
    (hI : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      RΦ.obj (DerivedCategory.Q.obj I) :=
  (DerivedCategory.quotientCompQhIso A).symm.app
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≪≫
    DerivedCategory.Qh.mapIso
      ((Φ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm.app I) ≪≫
    @asIso _ _ _ _ (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) hI ≪≫
    RΦ.mapIso ((DerivedCategory.quotientCompQhIso A).app I)

/-- The forward map of `rightDerivedCochainComparisonIso` at `I` is the component at `I` of
`rightDerivedCochainComparison`. -/
lemma rightDerivedCochainComparisonIso_hom (Φ : A ⥤ A) [Φ.Additive]
    (RΦ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ) (I : CochainComplex A ℤ)
    (hI : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    (rightDerivedCochainComparisonIso Φ RΦ α I hI).hom =
      (rightDerivedCochainComparison Φ RΦ α).app I :=
  rfl

/-- **Stacks 070K, in the form the triangle of part (2) consumes it.**  The comparison `α` of a
right derived functor is invertible at the image in the homotopy category of a K-injective
complex, as soon as K-injective resolutions exist. -/
lemma isIso_rightDerivedComparison_app_of_isKInjective
    (hres : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (Φ : A ⥤ A) [Φ.Additive] (RΦ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ)
    (hRΦ : RΦ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
  have := hRΦ
  have := hI
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres).2
    DerivedCategory.Qh RΦ α I inferInstance

omit [HasDerivedCategory A] in
/-- The square relating the two ways of reading a natural transformation of additive functors on
the homotopy category: degreewise on complexes, or through the induced functors.  Both
structural isomorphisms are identities, so the square is the unit laws. -/
lemma comp_mapHomotopyCategoryFactors_inv_app (d : Φ ⟶ Ψ) (K : CochainComplex A ℤ) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex d (ComplexShape.up ℤ)).app K) ≫
      (Ψ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K =
      (Φ.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K ≫
        (NatTrans.mapHomotopyCategory d (ComplexShape.up ℤ)).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The comparison of Stacks 070K is natural in the functor too.**  For `d : Φ ⟶ Ψ` and `RΦ`,
`RΨ` right derived functors of `Φ`, `Ψ`, the derived transformation `RΦ ⟶ RΨ` of Mathlib's
`CategoryTheory.Functor.rightDerivedNatTrans` agrees, through the comparisons, with `d` applied
degreewise.  No K-injectivity is needed: this is a square of natural transformations. -/
lemma rightDerivedCochainComparison_comp_rightDerivedNatTrans (d : Φ ⟶ Ψ)
    (RΦ RΨ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ)
    (β : Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΨ)
    [RΦ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : CochainComplex A ℤ) :
    (rightDerivedCochainComparison Φ RΦ α).app K ≫
        (Functor.rightDerivedNatTrans RΦ RΨ α β
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
          (Functor.whiskerRight (NatTrans.mapHomotopyCategory d (ComplexShape.up ℤ))
            DerivedCategory.Qh)).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex d (ComplexShape.up ℤ)).app K) ≫
        (rightDerivedCochainComparison Ψ RΨ β).app K := by
  have hfac := Functor.rightDerivedNatTrans_app RΦ RΨ α β
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory d (ComplexShape.up ℤ))
      DerivedCategory.Qh) ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)
  have hnat := (Functor.rightDerivedNatTrans RΦ RΨ α β
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory d (ComplexShape.up ℤ))
      DerivedCategory.Qh)).naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
  simp only [rightDerivedCochainComparison_app, Category.assoc]
  rw [reassoc_of% (DerivedCategory.quotientCompQhIso_inv_naturality
      ((NatTrans.mapHomologicalComplex d (ComplexShape.up ℤ)).app K)),
    ← Functor.map_comp_assoc, comp_mapHomotopyCategoryFactors_inv_app,
    Functor.map_comp_assoc, hnat]
  simp only [Functor.comp_obj]
  rw [reassoc_of% hfac]
  simp only [Functor.whiskerRight_app]

end Comparison

/-! ### The unit a natural map `𝟭 ⟶ Φ` induces on the derived category -/

section DerivedUnit

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {Φ : A ⥤ A} [Φ.Additive]

/-- A natural map `η : 𝟭 ⟶ Φ` applied degreewise to cochain complexes, as a natural
transformation.  This is `CategoryTheory.PushforwardMayerVietoris.unitCochainMap` read naturally
in the complex. -/
def unitCochainNatTrans (η : 𝟭 A ⟶ Φ) :
    𝟭 (CochainComplex A ℤ) ⟶ Φ.mapHomologicalComplex (ComplexShape.up ℤ) where
  app K := unitCochainMap η K
  naturality _ _ f := by ext i; exact η.naturality (f.f i)

omit [HasDerivedCategory A] in
/-- The component of `unitCochainNatTrans η` at a complex `K` is `unitCochainMap η K`. -/
@[simp]
lemma unitCochainNatTrans_app (η : 𝟭 A ⟶ Φ) (K : CochainComplex A ℤ) :
    (unitCochainNatTrans η).app K = unitCochainMap η K :=
  rfl

/-- **The map `E ⟶ RΦ E` induced by a natural map `η : 𝟭 ⟶ Φ`.**  No exactness of `Φ` is
assumed, so `η` has no image under `CategoryTheory.NatTrans.mapDerivedCategory`; instead
the degreewise `η`, followed by the comparison of Stacks 070K, is a natural transformation
`Q ⟶ Q ⋙ RΦ`, and such a transformation lifts uniquely along the localization
`DerivedCategory.Q` to a natural transformation `𝟭 D(A) ⟶ RΦ`.

For `Φ = j_{Y,*}((-)|_Y)` and `η` the unit of `(-)|_Y ⊣ j_{Y,*}` this is the canonical map
`E ⟶ Rj_{Y,*}E|_Y`, the first map of Stacks 08GW part (2). -/
def derivedUnitOfNatTrans (η : 𝟭 A ⟶ Φ) (RΦ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ) :
    𝟭 (DerivedCategory A) ⟶ RΦ :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Q
    (DerivedCategory.Q ⋙ RΦ) (𝟭 (DerivedCategory A)) RΦ
    (Functor.whiskerRight (unitCochainNatTrans η) DerivedCategory.Q ≫
      rightDerivedCochainComparison Φ RΦ α)

/-- The derived unit at the image of a cochain complex is the degreewise unit followed by the
comparison of Stacks 070K.  This is the defining property of the lift. -/
lemma derivedUnitOfNatTrans_app_Q (η : 𝟭 A ⟶ Φ)
    (RΦ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ) (K : CochainComplex A ℤ) :
    (derivedUnitOfNatTrans η RΦ α).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (unitCochainMap η K) ≫
        (rightDerivedCochainComparison Φ RΦ α).app K := by
  simp [derivedUnitOfNatTrans, Localization.liftNatTrans_app, Localization.Lifting.iso]

/-- **The derived unit through a chosen representative.**  For any isomorphism `Q(I) ≅ E`, the
derived unit at `E` is the degreewise unit at `I` followed by the comparison of Stacks 070K.
This is what identifies the first map of the triangle produced on a representative with the
canonical one. -/
lemma derivedUnitOfNatTrans_app_eq (η : 𝟭 A ⟶ Φ)
    (RΦ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ) {I : CochainComplex A ℤ} {E : DerivedCategory A}
    (e : DerivedCategory.Q.obj I ≅ E) :
    e.hom ≫ (derivedUnitOfNatTrans η RΦ α).app E =
      DerivedCategory.Q.map (unitCochainMap η I) ≫
        (rightDerivedCochainComparison Φ RΦ α).app I ≫ RΦ.map e.hom := by
  have hnat : e.hom ≫ (derivedUnitOfNatTrans η RΦ α).app E =
      (derivedUnitOfNatTrans η RΦ α).app (DerivedCategory.Q.obj I) ≫ RΦ.map e.hom :=
    (derivedUnitOfNatTrans η RΦ α).naturality e.hom
  rw [hnat, derivedUnitOfNatTrans_app_Q, Category.assoc]

end DerivedUnit

/-! ### The canonical Mayer–Vietoris triangle -/

section MayerVietoris

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {ΦU ΦV ΦP : A ⥤ A} [ΦU.Additive] [ΦV.Additive] [ΦP.Additive]

/-- The derived unit at `E`, through an isomorphism `Q(I) ≅ E` and the comparison of
Stacks 070K at `I`. -/
private theorem derivedUnitOfNatTrans_app_eq_comp_iso {Φ : A ⥤ A} [Φ.Additive] (η : 𝟭 A ⟶ Φ)
    (RΦ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ) {I : CochainComplex A ℤ} {E : DerivedCategory A}
    (e : DerivedCategory.Q.obj I ≅ E)
    (hα : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    (derivedUnitOfNatTrans η RΦ α).app E =
      e.inv ≫ DerivedCategory.Q.map (unitCochainMap η I) ≫
        (rightDerivedCochainComparisonIso Φ RΦ α I hα ≪≫ RΦ.mapIso e).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, rightDerivedCochainComparisonIso_hom]
  rw [← derivedUnitOfNatTrans_app_eq η RΦ α e]
  simp

/-- The derived transformation of `d : Φ ⟶ Ψ` at `E`, through an isomorphism `Q(I) ≅ E` and the
comparisons of Stacks 070K at `I`. -/
private theorem rightDerivedNatTrans_app_eq_comp_iso {Φ Ψ : A ⥤ A} [Φ.Additive] [Ψ.Additive]
    (d : Φ ⟶ Ψ) (RΦ RΨ : DerivedCategory A ⥤ DerivedCategory A)
    (α : Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΦ)
    (β : Ψ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RΨ)
    [RΦ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {I : CochainComplex A ℤ} {E : DerivedCategory A} (e : DerivedCategory.Q.obj I ≅ E)
    (hα : IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (hβ : IsIso (β.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) :
    (Functor.rightDerivedNatTrans RΦ RΨ α β
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
        (Functor.whiskerRight (NatTrans.mapHomotopyCategory d (ComplexShape.up ℤ))
          DerivedCategory.Qh)).app E =
      (rightDerivedCochainComparisonIso Φ RΦ α I hα ≪≫ RΦ.mapIso e).inv ≫
        DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex d (ComplexShape.up ℤ)).app I) ≫
          (rightDerivedCochainComparisonIso Ψ RΨ β I hβ ≪≫ RΨ.mapIso e).hom := by
  have hnat := (Functor.rightDerivedNatTrans RΦ RΨ α β
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory d (ComplexShape.up ℤ))
      DerivedCategory.Qh)).naturality e.hom
  refine (cancel_epi (rightDerivedCochainComparisonIso Φ RΦ α I hα ≪≫ RΦ.mapIso e).hom).mp ?_
  rw [Iso.hom_inv_id_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom, rightDerivedCochainComparisonIso_hom,
    Category.assoc]
  rw [hnat, reassoc_of% rightDerivedCochainComparison_comp_rightDerivedNatTrans d RΦ RΨ α β I]

/-- **From part (1) to part (2), with the canonical maps.**  Let `Φ_U, Φ_V, Φ_P` be additive
endofunctors of an abelian category in which every cochain complex has a K-injective
resolution, and let `η_U : 𝟭 ⟶ Φ_U`, `η_V : 𝟭 ⟶ Φ_V`, `d_U : Φ_U ⟶ Φ_P`, `d_V : Φ_V ⟶ Φ_P` be
natural transformations making

`0 ⟶ M ⟶ Φ_U M ⊕ Φ_V M ⟶ Φ_P M ⟶ 0`

short exact at every object `M`.  Let `R_U`, `R_V`, `R_P` be right derived functors of the three
`Φ_Y`, with their comparisons `α_Y`.  Then every object `E` of `D(A)` sits in a distinguished
triangle

`E ⟶ R_U E ⊕ R_V E ⟶ R_P E ⟶ E[1]`

whose first map is the pair of derived units
`CategoryTheory.PushforwardMayerVietoris.derivedUnitOfNatTrans` of `η_U` and `η_V` and whose
second is the difference of the derived transformations
`CategoryTheory.Functor.rightDerivedNatTrans` of `d_U` and `d_V`.  *Only the connecting map is
existentially quantified*; see the implementation notes of this file.

No exactness of the three functors is assumed, which is what makes this the right statement for
direct images: the triangle is the one attached to the short exact sequence of cochain complexes
that the hypothesis gives degreewise on a K-injective representative of `E`, and the two
identifications of its maps with the canonical ones are
`CategoryTheory.PushforwardMayerVietoris.derivedUnitOfNatTrans_app_eq` and
`…rightDerivedCochainComparison_comp_rightDerivedNatTrans`. -/
theorem exists_mem_distTriang_derivedUnitBiprod
    (hres : ∀ K : CochainComplex A ℤ,
      ∃ (J : CochainComplex A ℤ) (i : K ⟶ J), J.IsKInjective ∧ QuasiIso i)
    (ηU : 𝟭 A ⟶ ΦU) (ηV : 𝟭 A ⟶ ΦV) (dU : ΦU ⟶ ΦP) (dV : ΦV ⟶ ΦP)
    (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
      biprod.desc (dU.app M) (-(dV.app M)) = 0)
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (RU RV RP : DerivedCategory A ⥤ DerivedCategory A)
    (αU : ΦU.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RU)
    (αV : ΦV.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RV)
    (αP : ΦP.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RP)
    [hRU : RU.IsRightDerivedFunctor αU (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [hRV : RV.IsRightDerivedFunctor αV (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [hRP : RP.IsRightDerivedFunctor αP (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (E : DerivedCategory A) :
    ∃ δ, Triangle.mk
        (biprod.lift ((derivedUnitOfNatTrans ηU RU αU).app E)
          ((derivedUnitOfNatTrans ηV RV αV).app E))
        (biprod.desc
          ((Functor.rightDerivedNatTrans RU RP αU αP
            (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
            (Functor.whiskerRight (NatTrans.mapHomotopyCategory dU (ComplexShape.up ℤ))
              DerivedCategory.Qh)).app E)
          (-((Functor.rightDerivedNatTrans RV RP αV αP
            (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
            (Functor.whiskerRight (NatTrans.mapHomotopyCategory dV (ComplexShape.up ℤ))
              DerivedCategory.Qh)).app E))) δ ∈
      distTriang (DerivedCategory A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative_of_universe hres E
  obtain ⟨δ, hδ⟩ := mem_distTriang_unitBiprod_of_natural_shortExact ηU ηV dU dV hzero hMV I
  have hαU := isIso_rightDerivedComparison_app_of_isKInjective hres ΦU RU αU hRU I hI
  have hαV := isIso_rightDerivedComparison_app_of_isKInjective hres ΦV RV αV hRV I hI
  have hαP := isIso_rightDerivedComparison_app_of_isKInjective hres ΦP RP αP hRP I hI
  have hU := derivedUnitOfNatTrans_app_eq_comp_iso ηU RU αU e hαU
  have hV := derivedUnitOfNatTrans_app_eq_comp_iso ηV RV αV e hαV
  have hgU := rightDerivedNatTrans_app_eq_comp_iso dU RU RP αU αP e hαU hαP
  have hgV := rightDerivedNatTrans_app_eq_comp_iso dV RV RP αV αP e hαV hαP
  rw [hU, hV, hgU, hgV]
  refine ⟨(rightDerivedCochainComparisonIso ΦP RP αP I hαP ≪≫ RP.mapIso e).inv ≫ δ ≫
      (shiftFunctor (DerivedCategory A) (1 : ℤ)).map e.hom,
    isomorphic_distinguished _ hδ _ (Triangle.isoMk _ _ e.symm
      (biprod.mapIso (rightDerivedCochainComparisonIso ΦU RU αU I hαU ≪≫ RU.mapIso e).symm
        (rightDerivedCochainComparisonIso ΦV RV αV I hαV ≪≫ RV.mapIso e).symm)
      (rightDerivedCochainComparisonIso ΦP RP αP I hαP ≪≫ RP.mapIso e).symm ?_ ?_ ?_)⟩
  · refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  · refine biprod.hom_ext' _ _ ?_ ?_ <;> simp
  · simp

end MayerVietoris

end CategoryTheory.PushforwardMayerVietoris

namespace AlgebraicGeometry.Space

open CategoryTheory.PushforwardMayerVietoris

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

section LowerShriek

attribute [local instance] HasDerivedCategory.standard
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat
  hasRightDerivedFunctor_mapHomotopyCategory_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-! #### The library's extension by zero at the three morphisms of the square -/

/-- The adjunction `j_{U!} ⊣ (-)|_U` at the open immersion of an elementary distinguished
square, for the extension by zero the library constructs. -/
def edsLowerShriekAdjOpen :
    etaleModuleLowerShriek B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) ⊣
      etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) :=
  etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)

/-- The adjunction `j_{V!} ⊣ (-)|_V` at the étale morphism of an elementary distinguished
square, for the extension by zero the library constructs. -/
def edsLowerShriekAdjEtale :
    etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) ⊣
      etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) :=
  etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)

/-- The adjunction `j_{P!} ⊣ (-)|_P` at the intersection of an elementary distinguished square,
for the extension by zero the library constructs. -/
def edsLowerShriekAdjInter :
    etaleModuleLowerShriek B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) ⊣
      etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) :=
  etaleModuleLowerShriekAdjunction B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq)

/-! #### Part (1)

The two maps `j_{U,*}F|_U ⟶ j_{P,*}F|_P` and `j_{V,*}F|_V ⟶ j_{P,*}F|_P` of Stacks 08GW
part (1) are *not* arbitrary transformations compatible with the units: they are the conjugates,
under the two adjunctions `j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)`, of the extension-by-zero
comparisons `AlgebraicGeometry.Space.edsShriekOpenComparison` and
`AlgebraicGeometry.Space.edsShriekEtaleComparison` that Stacks 08GV provides.  They are written
out below rather than abbreviated, because a definition for them makes the unification of the
statements below against the theorems of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforward` exceed the heartbeat
limit, while the same statements with the terms written out elaborate at once. -/

/-- The Mayer–Vietoris complex of direct images of Stacks 08GW part (1) is a complex, at the
library's extension by zero. -/
theorem zero_edsRestrictPushMayerVietorisLowerShriek (F : Modules.{u, u} B S hS W.1 W.2) :
    biprod.lift ((edsAdjOpen B S hS hsq).unit.app F)
        ((edsAdjEtale B S hS hsq).unit.app F) ≫
      biprod.desc ((conjugateEquiv ((edsAdjOpen B S hS hsq).comp
            (edsLowerShriekAdjOpen B S hS hsq))
          ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
          (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
            (edsLowerShriekAdjInter B S hS hsq))).app F)
        (-((conjugateEquiv ((edsAdjEtale B S hS hsq).comp
            (edsLowerShriekAdjEtale B S hS hsq))
          ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
          (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
            (edsLowerShriekAdjInter B S hS hsq))).app F)) = 0 :=
  zero_edsRestrictPushMayerVietoris B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
    (edsLowerShriekAdjEtale B S hS hsq) (edsLowerShriekAdjInter B S hS hsq)
    (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
      (edsLowerShriekAdjInter B S hS hsq))
    (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
      (edsLowerShriekAdjInter B S hS hsq))
    (zero_edsShriekMayerVietoris B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
      (edsLowerShriekAdjEtale B S hS hsq) (edsLowerShriekAdjInter B S hS hsq)) F

/-- **Stacks 08GW part (1), with nothing assumed.**  Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over a scheme `S`, let `P = U ×_X V`, write `(-)|_Y`
for restriction of modules along `j_Y : Y ⟶ X` and `j_{Y,*}` for the direct image of Stacks
03LU.  Then for every sheaf of `𝒪_X`-modules `F` the sequence

`0 ⟶ F ⟶ j_{U,*}F|_U ⊕ j_{V,*}F|_V ⟶ j_{P,*}F|_P ⟶ 0`

is short exact.  Its first map is the pair of canonical units `F ⟶ j_{Y,*}F|_Y` of the
adjunctions `(-)|_Y ⊣ j_{Y,*}` and its second is the difference of the conjugates, under the
adjunctions `j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)`, of the two extension-by-zero comparisons
`AlgebraicGeometry.Space.edsShriekOpenComparison` and
`AlgebraicGeometry.Space.edsShriekEtaleComparison` of Stacks 08GV.

This is `AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietorisComparison` at the
extension by zero the library constructs, `AlgebraicGeometry.Space.etaleModuleLowerShriek` with
its adjunction `AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction`, so nothing is a
parameter beyond the square itself: the exactness of extension by zero (Stacks 03DJ) is the
theorem `AlgebraicGeometry.Space.preservesFiniteLimits_etaleModuleLowerShriek` with its two
companions, the two sheafification hypotheses of the ambient site are the theorems
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_addCommGrpCat` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat`, part (1)
of Stacks 08GV is
`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`, and the surjectivity on the right
is `AlgebraicGeometry.Space.epi_edsRestrictPushMayerVietorisComparison`. -/
@[stacks 08GW "part (1)"]
theorem shortExact_edsRestrictPushMayerVietorisLowerShriek
    (F : Modules.{u, u} B S hS W.1 W.2) :
    (ShortComplex.mk
      (biprod.lift ((edsAdjOpen B S hS hsq).unit.app F)
        ((edsAdjEtale B S hS hsq).unit.app F))
      (biprod.desc ((conjugateEquiv ((edsAdjOpen B S hS hsq).comp
            (edsLowerShriekAdjOpen B S hS hsq))
          ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
          (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
            (edsLowerShriekAdjInter B S hS hsq))).app F)
        (-((conjugateEquiv ((edsAdjEtale B S hS hsq).comp
            (edsLowerShriekAdjEtale B S hS hsq))
          ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
          (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
            (edsLowerShriekAdjInter B S hS hsq))).app F)))
      (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq F)).ShortExact :=
  shortExact_edsRestrictPushMayerVietorisComparison B S hS hsq
    (edsLowerShriekAdjOpen B S hS hsq) (edsLowerShriekAdjEtale B S hS hsq)
    (edsLowerShriekAdjInter B S hS hsq) F

/-! #### The three derived direct images -/

/-- `Rj_{U,*}((-)|_U)`: the chosen total right derived functor of
`AlgebraicGeometry.Space.edsRestrictPushOpen`.  It exists by
`AlgebraicGeometry.Space.hasRightDerivedFunctor_mapHomotopyCategory_modules`. -/
abbrev edsDerivedRestrictPushOpen :
    DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2) :=
  ((edsRestrictPushOpen B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))

/-- `Rj_{V,*}((-)|_V)`: the chosen total right derived functor of
`AlgebraicGeometry.Space.edsRestrictPushEtale`. -/
abbrev edsDerivedRestrictPushEtale :
    DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2) :=
  ((edsRestrictPushEtale B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))

/-- `Rj_{P,*}((-)|_P)`: the chosen total right derived functor of
`AlgebraicGeometry.Space.edsRestrictPushInter`. -/
abbrev edsDerivedRestrictPushInter :
    DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2) :=
  ((edsRestrictPushInter B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))

/-- The canonical comparison exhibiting `AlgebraicGeometry.Space.edsDerivedRestrictPushOpen` as
a right derived functor of `AlgebraicGeometry.Space.edsRestrictPushOpen`. -/
abbrev edsTotalRightDerivedUnitOpen :
    (edsRestrictPushOpen B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ edsDerivedRestrictPushOpen B S hS hsq :=
  ((edsRestrictPushOpen B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))

/-- The canonical comparison exhibiting `AlgebraicGeometry.Space.edsDerivedRestrictPushEtale` as
a right derived functor of `AlgebraicGeometry.Space.edsRestrictPushEtale`. -/
abbrev edsTotalRightDerivedUnitEtale :
    (edsRestrictPushEtale B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ edsDerivedRestrictPushEtale B S hS hsq :=
  ((edsRestrictPushEtale B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))

/-- The canonical comparison exhibiting `AlgebraicGeometry.Space.edsDerivedRestrictPushInter` as
a right derived functor of `AlgebraicGeometry.Space.edsRestrictPushInter`. -/
abbrev edsTotalRightDerivedUnitInter :
    (edsRestrictPushInter B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ edsDerivedRestrictPushInter B S hS hsq :=
  ((edsRestrictPushInter B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))

/-! #### Part (2) -/

/-- **Stacks 08GW part (2), with nothing assumed and with the canonical triangle.**  Let
`(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a scheme
`S`, let `P = U ×_X V` and write `Rj_{Y,*}((-)|_Y)` for the total right derived functor of
`j_{Y,*}((-)|_Y)`.  Then every object `E` of the unbounded derived category `D(𝒪_X)` sits in a
distinguished triangle

`E ⟶ Rj_{U,*}E|_U ⊕ Rj_{V,*}E|_V ⟶ Rj_{P,*}E|_P ⟶ E[1]`.

**Its maps are the canonical ones, not existentially quantified.**  The first is the pair of
derived units `CategoryTheory.PushforwardMayerVietoris.derivedUnitOfNatTrans` of the units
`F ⟶ j_{Y,*}F|_Y` of the adjunctions `(-)|_Y ⊣ j_{Y,*}` of Stacks 03LU, and the second is the
difference of the derived transformations `CategoryTheory.Functor.rightDerivedNatTrans` of the
two comparisons of part (1) — the conjugates, under `j_{Y!}((-)|_Y) ⊣ j_{Y,*}((-)|_Y)`, of the
extension-by-zero comparisons of Stacks 08GV.  Only the connecting map
`Rj_{P,*}E|_P ⟶ E[1]` is existentially quantified, the library attaching no canonical such map
to an object of `D(𝒪_X)`; the source likewise asserts only that the triangle is distinguished,
and `δ` is existential in Stacks 08GV part (2) as well.

Nothing is a parameter beyond the square: part (1) is the unqualified
`AlgebraicGeometry.Space.shortExact_edsRestrictPushMayerVietorisLowerShriek`, the K-injective
resolutions are `AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules` (Stacks 079P),
and the three derived functors are the chosen ones, which exist by
`AlgebraicGeometry.Space.hasRightDerivedFunctor_mapHomotopyCategory_modules`. -/
@[stacks 08GW "part (2)"]
theorem exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ δ, Triangle.mk
        (biprod.lift
          ((derivedUnitOfNatTrans (edsAdjOpen B S hS hsq).unit
            (edsDerivedRestrictPushOpen B S hS hsq)
            (edsTotalRightDerivedUnitOpen B S hS hsq)).app E)
          ((derivedUnitOfNatTrans (edsAdjEtale B S hS hsq).unit
            (edsDerivedRestrictPushEtale B S hS hsq)
            (edsTotalRightDerivedUnitEtale B S hS hsq)).app E))
        (biprod.desc
          ((Functor.rightDerivedNatTrans (edsDerivedRestrictPushOpen B S hS hsq)
            (edsDerivedRestrictPushInter B S hS hsq)
            (edsTotalRightDerivedUnitOpen B S hS hsq)
            (edsTotalRightDerivedUnitInter B S hS hsq)
            (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
            (Functor.whiskerRight (NatTrans.mapHomotopyCategory
              (conjugateEquiv ((edsAdjOpen B S hS hsq).comp
                  (edsLowerShriekAdjOpen B S hS hsq))
                ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
                  (edsLowerShriekAdjInter B S hS hsq)))
              (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E)
          (-((Functor.rightDerivedNatTrans (edsDerivedRestrictPushEtale B S hS hsq)
            (edsDerivedRestrictPushInter B S hS hsq)
            (edsTotalRightDerivedUnitEtale B S hS hsq)
            (edsTotalRightDerivedUnitInter B S hS hsq)
            (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
            (Functor.whiskerRight (NatTrans.mapHomotopyCategory
              (conjugateEquiv ((edsAdjEtale B S hS hsq).comp
                  (edsLowerShriekAdjEtale B S hS hsq))
                ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
                  (edsLowerShriekAdjInter B S hS hsq)))
              (ComplexShape.up ℤ)) DerivedCategory.Qh)).app E))) δ ∈
      distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :=
  exists_mem_distTriang_derivedUnitBiprod
    (exists_quasiIso_isKInjective_modules B S hS W.1 W.2)
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (zero_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (shortExact_edsRestrictPushMayerVietorisLowerShriek B S hS hsq)
    (edsDerivedRestrictPushOpen B S hS hsq) (edsDerivedRestrictPushEtale B S hS hsq)
    (edsDerivedRestrictPushInter B S hS hsq) (edsTotalRightDerivedUnitOpen B S hS hsq)
    (edsTotalRightDerivedUnitEtale B S hS hsq) (edsTotalRightDerivedUnitInter B S hS hsq) E

end LowerShriek

end AlgebraicGeometry.Space

end
