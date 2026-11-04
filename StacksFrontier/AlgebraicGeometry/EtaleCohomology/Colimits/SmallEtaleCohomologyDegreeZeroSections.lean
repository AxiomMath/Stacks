module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalVanishingFromCechVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage

/-!
# The legs of Stacks 09YQ in degree zero, read on global sections

The cocone of [Stacks, Tag 09YQ] is built from `Stacks.EtaleCohomology.etaleCohomologyMapTo`, the
map on étale cohomology attached to a morphism of schemes `k : Y ⟶ X` and a map
`w : k^{-1}A ⟶ B` of abelian sheaves. In degree zero cohomology is global sections, by Mathlib's
`CategoryTheory.Sheaf.H.equiv₀` at the terminal object `AlgebraicGeometry.Scheme.Etale.mk (𝟙 X)`
of the small étale site. This file identifies the leg with the map on global sections, which is
what a degree-zero statement proved at the geometry can discharge.

## Main results

* `Stacks.EtaleCohomology.etaleSectionsRestriction` — **the pullback map on global sections along
  a morphism of schemes**: the unit of the inverse-image/direct-image adjunction read over the
  terminal object of the small étale site of `X`, followed by restriction along the unique map to
  the base change of that terminal object.
* `Stacks.EtaleCohomology.equiv₀_etaleCohomologyRestrictionMap` — **restriction on étale
  cohomology in degree zero is the pullback map on global sections**, through
  `CategoryTheory.Sheaf.H.equiv₀`.
* `Stacks.EtaleCohomology.equiv₀_etaleCohomologyMapTo` — **the leg of [Stacks, Tag 09YQ] in degree
  zero is the pullback map on global sections followed by `w`**, through `Sheaf.H.equiv₀`.

## Implementation notes

`CategoryTheory.Sheaf.H.equiv₀` applies here as it stands and is used verbatim; no wrapper around
it is introduced. What does **not** apply is
`Stacks.Cohomology.FreeYoneda.cohomologyPresheafIsoSections`:
`CategoryTheory.Sheaf.cohomologyPresheaf` is `Ext` out of the free abelian sheaf on a
representable, so it pins the coefficient universe to the *hom* universe of the site, which for
`AlgebraicGeometry.Scheme.Etale` is `u`; at the coefficients these statements are written at,
naming it is an `Application type mismatch` and not a usable identification.
`CategoryTheory.Sheaf.H` is `Ext` out of the *constant* sheaf and pins nothing.

The identification has two halves, and only the first is new here. The half along
`CategoryTheory.Sheaf.H.map` is Mathlib's `CategoryTheory.Sheaf.H.equiv₀_naturality`. The half
along `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` is
`equiv₀_etaleCohomologyRestrictionMap`, and its proof is a computation in degree zero and nothing
more: a degree-zero `Ext` class is a map of sheaves out of the constant sheaf
(`CategoryTheory.Abelian.Ext.addEquiv₀`), restriction applies the inverse image to it and then
precomposes with `Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`
(`addEquiv₀_etaleCohomologyRestrictionMap`), and the transpose of that comparison over an
arbitrary object of the site is already available as
`Stacks.EtaleCohomology.constantSheafSection_comp_homEquiv_constantIso`. So the only thing left is
to read both sides on the canonical section of the constant sheaf over the terminal object, which
is that transpose together with `Stacks.ConstantSheaf.constantSheafSection_restrict`.

**Why `etaleUnitSection` is a definition of its own.** The direct image is restriction along base
change, so the sections of `k_*k^{-1}A` over an étale `X`-scheme `U` *are* the sections of
`k^{-1}A` over `U ×_X Y`; but the two are spelled differently, as
`((k^{-1} ⋙ k_*).obj A).obj.obj (op U)` and as `(k^{-1}A).obj.obj (op (U ×_X Y))`, and the
equality is only definitional. A composite written through the first spelling is accepted when it
is elaborated and then stops being type-correct at `implicit` transparency, which is the
transparency `rewrite` builds its motive at: `rw [Category.assoc]` on such a composite fails with
an `Application type mismatch` between exactly those two spellings. Naming the component of the
unit in the second spelling seals that junction inside one definition, after which every
computation below is an ordinary composition of maps of abelian groups.

The terminal object is `AlgebraicGeometry.Scheme.Etale.mk (𝟙 X)`, with
`Stacks.EtaleCohomology.etaleMkIdIsTerminal` as its witness. The tree carries a second name for
the same object and the same witness, `Stacks.EtaleCohomology.etaleSiteTerminal` and
`etaleSiteTerminalIsTerminal`; the two objects are equal by `rfl` and the two witnesses by
`Subsingleton.elim`, `CategoryTheory.Limits.IsLimit` being a subsingleton, so the lemmas of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/ConstantSheafInverseImage.lean`
apply to the spelling used here without any transport.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w t

namespace Stacks.EtaleCohomology

/-- **The corepresentability equivalence `(ℤ ⟶ G) ≃+ G` is natural in `G`.** Postcomposing a map
out of `ULift ℤ` with a map of abelian groups is evaluating the latter on the element the former
corresponds to. Mathlib's `AddCommGrpCat.uliftZMultiplesAddEquiv` carries no naturality lemma, and
this is the only thing needed to read `CategoryTheory.Sheaf.H.equiv₀` through a map on sections. -/
public theorem uliftZMultiplesAddEquiv_comp {G H : AddCommGrpCat.{t}}
    (φ : AddCommGrpCat.of (ULift ℤ) ⟶ G) (ψ : G ⟶ H) :
    AddCommGrpCat.uliftZMultiplesAddEquiv H (φ ≫ ψ) =
      ψ (AddCommGrpCat.uliftZMultiplesAddEquiv G φ) :=
  rfl

section DegreeZero

variable {X Y : Scheme.{u}} (k : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- The base change along `k : Y ⟶ X` of the terminal object `𝟙 X` of the small étale site of `X`
is a terminal object of the small étale site of `Y`. -/
public def isTerminalSmallEtaleBaseChangeEtaleMkId :
    IsTerminal ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 X))) :=
  (etaleMkIdIsTerminal X).isTerminalObj (smallEtaleBaseChange k)

/-- **The unit of the inverse-image/direct-image adjunction, read on global sections.** The
component of `A ⟶ k_*k^{-1}A` over the terminal object `𝟙 X` of the small étale site of `X`, with
its target written as the sections of `k^{-1}A` over the base change of that object — the spelling
the direct image makes definitionally equal to the sections of `k_*k^{-1}A` over `𝟙 X`, and the
one every computation below needs; see the implementation notes. -/
public def etaleUnitSection
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    A.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      ((etaleAbelianInverseImage.{u, v} k).obj A).obj.obj
        (op ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 X)))) :=
  ((etaleAbelianInverseImageDirectImageAdj.{u, v} k).unit.app A).hom.app
    (op (Scheme.Etale.mk (𝟙 X)))

omit [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] in
/-- **The unit on global sections is natural in the sheaf.** This is the naturality of the unit of
the adjunction, read over the terminal object `𝟙 X`. -/
public theorem etaleUnitSection_naturality
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (φ : A ⟶ B) :
    etaleUnitSection.{u, v} k A ≫
        ((etaleAbelianInverseImage.{u, v} k).map φ).hom.app
          (op ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 X)))) =
      φ.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫ etaleUnitSection.{u, v} k B :=
  (congrArg
    (fun z : A ⟶ (etaleAbelianDirectImage.{u, v} k).obj
        ((etaleAbelianInverseImage.{u, v} k).obj B) =>
      z.hom.app (op (Scheme.Etale.mk (𝟙 X))))
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} k).unit.naturality φ)).symm

/-- **The pullback map on global sections along a morphism of schemes**, for abelian sheaves on
Mathlib's small étale sites: the unit `A ⟶ k_*k^{-1}A` of the inverse-image/direct-image
adjunction read over the terminal object `𝟙 X`, whose sections are the sections of `k^{-1}A` over
the base change of that object, followed by restriction along the unique morphism from the
terminal object `𝟙 Y`.

This is what `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` is in degree zero, by
`Stacks.EtaleCohomology.equiv₀_etaleCohomologyRestrictionMap`. -/
public def etaleSectionsRestriction
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    A.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      ((etaleAbelianInverseImage.{u, v} k).obj A).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) :=
  etaleUnitSection.{u, v} k A ≫
    ((etaleAbelianInverseImage.{u, v} k).obj A).obj.map
      ((isTerminalSmallEtaleBaseChangeEtaleMkId k).from (Scheme.Etale.mk (𝟙 Y))).op

omit [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] in
/-- **The pullback map on global sections is natural in the sheaf.** This is
`Stacks.EtaleCohomology.etaleUnitSection_naturality` together with the naturality of the inverse
image of a map of sheaves. -/
public theorem etaleSectionsRestriction_naturality
    {A B : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (φ : A ⟶ B) :
    etaleSectionsRestriction.{u, v} k A ≫
        ((etaleAbelianInverseImage.{u, v} k).map φ).hom.app
          (op (Scheme.Etale.mk (𝟙 Y))) =
      φ.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫ etaleSectionsRestriction.{u, v} k B := by
  rw [etaleSectionsRestriction, etaleSectionsRestriction, Category.assoc,
    ((etaleAbelianInverseImage.{u, v} k).map φ).hom.naturality
      ((isTerminalSmallEtaleBaseChangeEtaleMkId k).from (Scheme.Etale.mk (𝟙 Y))).op,
    ← Category.assoc, etaleUnitSection_naturality.{u, v} k φ, Category.assoc]

/-- **The canonical section of the constant sheaf on the small étale site of `Y` over the terminal
object, read through the constant-sheaf comparison.** It is the canonical section on the site of
`X` over the terminal object `𝟙 X`, pulled back on global sections and then carried across the
comparison `k^{-1}ℤ_X ≅ ℤ_Y`.

This is the one computation the degree-zero identification needs. It is
`Stacks.EtaleCohomology.constantSheafSection_comp_homEquiv_constantIso` — the transpose of the
comparison over an arbitrary object of the site — read at the terminal object `𝟙 X`, together with
`Stacks.ConstantSheaf.constantSheafSection_restrict`, the fact that the canonical sections of a
constant sheaf restrict to one another. -/
public theorem constantSheafSection_etaleMkId_eq :
    Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v} (AddCommGrpCat.of (ULift ℤ))
        (Scheme.Etale.mk (𝟙 Y)) =
      (Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology
            AddCommGrpCat.{max (u + 1) v} (AddCommGrpCat.of (ULift ℤ))
            (Scheme.Etale.mk (𝟙 X)) ≫
          etaleSectionsRestriction.{u, v} k
            ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
              (AddCommGrpCat.of (ULift ℤ)))) ≫
        ((etaleAbelianInverseImageConstantIso.{u, v} k).app
          (AddCommGrpCat.of (ULift ℤ))).hom.hom.app (op (Scheme.Etale.mk (𝟙 Y))) := by
  have hθ : ((etaleAbelianInverseImageDirectImageAdj.{u, v} k).homEquiv
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
            (AddCommGrpCat.of (ULift ℤ)))
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
            (AddCommGrpCat.of (ULift ℤ)))
          ((etaleAbelianInverseImageConstantIso.{u, v} k).app
            (AddCommGrpCat.of (ULift ℤ))).hom).hom.app
        (op (Scheme.Etale.mk (𝟙 X))) =
      etaleUnitSection.{u, v} k
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
            (AddCommGrpCat.of (ULift ℤ))) ≫
        ((etaleAbelianInverseImageConstantIso.{u, v} k).app
          (AddCommGrpCat.of (ULift ℤ))).hom.hom.app
          (op ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 X)))) := by
    rw [Adjunction.homEquiv_unit]
    rfl
  have hnat : ((etaleAbelianInverseImage.{u, v} k).obj
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
            (AddCommGrpCat.of (ULift ℤ)))).obj.map
          ((isTerminalSmallEtaleBaseChangeEtaleMkId k).from (Scheme.Etale.mk (𝟙 Y))).op ≫
        ((etaleAbelianInverseImageConstantIso.{u, v} k).app
          (AddCommGrpCat.of (ULift ℤ))).hom.hom.app (op (Scheme.Etale.mk (𝟙 Y))) =
      ((etaleAbelianInverseImageConstantIso.{u, v} k).app
          (AddCommGrpCat.of (ULift ℤ))).hom.hom.app
          (op ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 X)))) ≫
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of (ULift ℤ))).obj.map
          ((isTerminalSmallEtaleBaseChangeEtaleMkId k).from (Scheme.Etale.mk (𝟙 Y))).op :=
    ((etaleAbelianInverseImageConstantIso.{u, v} k).app
      (AddCommGrpCat.of (ULift ℤ))).hom.hom.naturality _
  have hcs : Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology
            AddCommGrpCat.{max (u + 1) v} (AddCommGrpCat.of (ULift ℤ))
            (Scheme.Etale.mk (𝟙 X)) ≫
          (etaleUnitSection.{u, v} k
              ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
                (AddCommGrpCat.of (ULift ℤ))) ≫
            ((etaleAbelianInverseImageConstantIso.{u, v} k).app
              (AddCommGrpCat.of (ULift ℤ))).hom.hom.app
              (op ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 X)))))  =
        Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology
          AddCommGrpCat.{max (u + 1) v} (AddCommGrpCat.of (ULift ℤ))
          ((smallEtaleBaseChange k).obj (Scheme.Etale.mk (𝟙 X))) :=
    (congrArg (fun z => Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v} (AddCommGrpCat.of (ULift ℤ))
        (Scheme.Etale.mk (𝟙 X)) ≫ z) hθ).symm.trans
      (constantSheafSection_comp_homEquiv_constantIso.{u, v} k (AddCommGrpCat.of (ULift ℤ))
        (Scheme.Etale.mk (𝟙 X)))
  rw [etaleSectionsRestriction, Category.assoc, Category.assoc, hnat,
    ← Category.assoc (etaleUnitSection.{u, v} k
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift ℤ)))), ← Category.assoc, hcs]
  exact (Stacks.ConstantSheaf.constantSheafSection_restrict Y.smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v} (AddCommGrpCat.of (ULift ℤ))
    ((isTerminalSmallEtaleBaseChangeEtaleMkId k).from (Scheme.Etale.mk (𝟙 Y)))).symm

/-- The constant-sheaf comparison `k^{-1}ℤ_X ≅ ℤ_Y` cancels on sections over the terminal
object. -/
public theorem constantIso_hom_inv_app_etaleMkId :
    ((etaleAbelianInverseImageConstantIso.{u, v} k).app
          (AddCommGrpCat.of (ULift ℤ))).hom.hom.app (op (Scheme.Etale.mk (𝟙 Y))) ≫
        ((etaleAbelianInverseImageConstantIso.{u, v} k).app
          (AddCommGrpCat.of (ULift ℤ))).inv.hom.app (op (Scheme.Etale.mk (𝟙 Y))) =
      𝟙 _ := by
  have h := congrArg
    (fun z : ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
          etaleAbelianInverseImage.{u, v} k).obj (AddCommGrpCat.of (ULift ℤ))) ⟶
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
          etaleAbelianInverseImage.{u, v} k).obj (AddCommGrpCat.of (ULift ℤ))) =>
      z.hom.app (op (Scheme.Etale.mk (𝟙 Y))))
    (((etaleAbelianInverseImageConstantIso.{u, v} k).app
      (AddCommGrpCat.of (ULift ℤ))).hom_inv_id)
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] using h

/-- **The canonical section of the constant sheaf, read through the inverse of the constant-sheaf
comparison.** `Stacks.EtaleCohomology.constantSheafSection_etaleMkId_eq` with the comparison
cancelled. -/
public theorem constantSheafSection_comp_constantIso_inv_app :
    Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology
          AddCommGrpCat.{max (u + 1) v} (AddCommGrpCat.of (ULift ℤ))
          (Scheme.Etale.mk (𝟙 Y)) ≫
        ((etaleAbelianInverseImageConstantIso.{u, v} k).app
          (AddCommGrpCat.of (ULift ℤ))).inv.hom.app (op (Scheme.Etale.mk (𝟙 Y))) =
      Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology
            AddCommGrpCat.{max (u + 1) v} (AddCommGrpCat.of (ULift ℤ))
            (Scheme.Etale.mk (𝟙 X)) ≫
          etaleSectionsRestriction.{u, v} k
            ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
              (AddCommGrpCat.of (ULift ℤ))) := by
  rw [constantSheafSection_etaleMkId_eq.{u, v} k, Category.assoc,
    constantIso_hom_inv_app_etaleMkId.{u, v} k]
  exact Category.comp_id _

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Restriction on étale cohomology in degree zero, as a map of sheaves out of the constant
sheaf.** A class in degree zero is a map out of the constant sheaf `ℤ`
(`CategoryTheory.Abelian.Ext.addEquiv₀`); its restriction along `k` is the inverse image of that
map, precomposed with the constant-sheaf comparison
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`. This is
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_apply` with both degree-zero classes written
as maps. -/
public theorem addEquiv₀_etaleCohomologyRestrictionMap
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (x : Sheaf.H.{w} A 0) :
    Ext.addEquiv₀ (etaleCohomologyRestrictionMap.{u, v, w} k A 0 x) =
      ((etaleAbelianInverseImageConstantIso.{u, v} k).app
          (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (etaleAbelianInverseImage.{u, v} k).map (Ext.addEquiv₀ x) := by
  rw [etaleCohomologyRestrictionMap_apply.{u, v, w}]
  conv_lhs => rw [← Ext.mk₀_addEquiv₀_apply x]
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  exact (congrArg Ext.addEquiv₀ (Ext.addEquiv₀_symm_apply _).symm).trans
    (Ext.addEquiv₀.apply_symm_apply _)

/-- **Restriction on étale cohomology in degree zero is the pullback map on global sections.**
Through `CategoryTheory.Sheaf.H.equiv₀` at the terminal objects `𝟙 X` and `𝟙 Y` of the two small
étale sites, `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` in degree zero is
`Stacks.EtaleCohomology.etaleSectionsRestriction`.

This is `addEquiv₀_etaleCohomologyRestrictionMap` transposed along the constant-sheaf adjunction,
where `Stacks.EtaleCohomology.constantSheafSection_comp_constantIso_inv_app` identifies the
canonical section read through the comparison and
`Stacks.EtaleCohomology.etaleSectionsRestriction_naturality` moves the inverse image of the class
past the pullback map. -/
public theorem equiv₀_etaleCohomologyRestrictionMap
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (x : Sheaf.H.{w} A 0) :
    Sheaf.H.equiv₀ ((etaleAbelianInverseImage.{u, v} k).obj A) (etaleMkIdIsTerminal Y)
        (etaleCohomologyRestrictionMap.{u, v, w} k A 0 x) =
      etaleSectionsRestriction.{u, v} k A
        (Sheaf.H.equiv₀ A (etaleMkIdIsTerminal X) x) := by
  have key : Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology
            AddCommGrpCat.{max (u + 1) v} (AddCommGrpCat.of (ULift ℤ))
            (Scheme.Etale.mk (𝟙 Y)) ≫
          (((etaleAbelianInverseImageConstantIso.{u, v} k).app
              (AddCommGrpCat.of (ULift ℤ))).inv ≫
            (etaleAbelianInverseImage.{u, v} k).map (Ext.addEquiv₀ x)).hom.app
            (op (Scheme.Etale.mk (𝟙 Y))) =
      (Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology
            AddCommGrpCat.{max (u + 1) v} (AddCommGrpCat.of (ULift ℤ))
            (Scheme.Etale.mk (𝟙 X)) ≫
          (Ext.addEquiv₀ x).hom.app (op (Scheme.Etale.mk (𝟙 X)))) ≫
        etaleSectionsRestriction.{u, v} k A := by
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ← Category.assoc,
      constantSheafSection_comp_constantIso_inv_app.{u, v} k, Category.assoc,
      etaleSectionsRestriction_naturality.{u, v} k (Ext.addEquiv₀ x), ← Category.assoc]
  simpa only [Sheaf.H.equiv₀, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    addEquiv₀_etaleCohomologyRestrictionMap.{u, v, w} k A x,
    Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply_eq,
    uliftZMultiplesAddEquiv_comp] using
    congrArg (AddCommGrpCat.uliftZMultiplesAddEquiv _) key

end DegreeZero

/-! ### The leg of the cocone -/

section Leg

variable {X Y : Scheme.{u}} (k : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The leg of the cocone of [Stacks, Tag 09YQ] in degree zero is the pullback map on global
sections followed by `w`.** For a morphism of schemes `k : Y ⟶ X`, an abelian sheaf `A` on the
small étale site of `X`, one `B` on that of `Y` and a map `w : k^{-1}A ⟶ B`, the map
`Stacks.EtaleCohomology.etaleCohomologyMapTo k w 0` on degree-zero cohomology is, through
`CategoryTheory.Sheaf.H.equiv₀` at the terminal objects of the two sites, the pullback map on
global sections `Stacks.EtaleCohomology.etaleSectionsRestriction` followed by `w` on sections over
the terminal object of the site of `Y`.

Both the legs and the diagram maps of the cocone of Tag 09YQ are of this shape — a leg is the case
`k = f_i`, `w = ι_i` and a diagram map the case `k = f_{ji}` with `w` the transition of the system
— so this is the whole of the degree-zero reading of the cocone. The two halves are
`Stacks.EtaleCohomology.equiv₀_etaleCohomologyRestrictionMap` and Mathlib's
`CategoryTheory.Sheaf.H.equiv₀_naturality`. -/
public theorem equiv₀_etaleCohomologyMapTo
    {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ B)
    (x : Sheaf.H.{u + 1, u + 1} A 0) :
    Sheaf.H.equiv₀ B (etaleMkIdIsTerminal Y) (etaleCohomologyMapTo k w 0 x) =
      w.hom.app (op (Scheme.Etale.mk (𝟙 Y)))
        (etaleSectionsRestriction.{u, u + 1} k A
          (Sheaf.H.equiv₀ A (etaleMkIdIsTerminal X) x)) := by
  have h0 : etaleCohomologyMapTo k w 0 x =
      Sheaf.H.map w 0 (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k A 0 x) := rfl
  rw [h0, ← equiv₀_etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k A x,
    Sheaf.H.equiv₀_naturality (etaleMkIdIsTerminal Y) w]

end Leg

/-! ### The degree-zero cocone of Stacks 09YQ, on global sections -/

namespace SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (Scheme.smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1}
    (Sheaf (Scheme.smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]
  {c : Cone D}
  [HasSheafify (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]

/-- **The transition map of the diagram of [Stacks, Tag 09YQ] in degree zero, on global
sections.** For a transition `a : i ⟶ j` of the index, the map `F_j(X_j) → F_i(X_i)`: the pullback
map on global sections along `X_i ⟶ X_j` followed by the transition of the system. This is
`Stacks.EtaleCohomology.etaleCohomologyTransition` in degree zero, by
`etaleSectionsTransition_eq`. -/
public def etaleSectionsTransition (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    (F.obj j).obj.obj (op (Scheme.Etale.mk (𝟙 (D.obj j)))) ⟶
      (F.obj i).obj.obj (op (Scheme.Etale.mk (𝟙 (D.obj i)))) :=
  etaleSectionsRestriction.{u, u + 1} (D.map a) (F.obj j) ≫
    (systemTransitionMap F a).hom.app (op (Scheme.Etale.mk (𝟙 (D.obj i))))

/-- **The transition map on cohomology in degree zero is the transition map on global
sections.** `Stacks.EtaleCohomology.equiv₀_etaleCohomologyMapTo` at the transition morphism of the
system. -/
public theorem etaleSectionsTransition_eq (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) (x : Sheaf.H.{u + 1, u + 1} (F.obj j) 0) :
    Sheaf.H.equiv₀ (F.obj i) (etaleMkIdIsTerminal (D.obj i))
        (etaleCohomologyTransition F a 0 x) =
      etaleSectionsTransition F a
        (Sheaf.H.equiv₀ (F.obj j) (etaleMkIdIsTerminal (D.obj j)) x) :=
  equiv₀_etaleCohomologyMapTo (D.map a) (systemTransitionMap F a) x

variable {P : (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) →
      (𝒢 : Sheaf (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) →
      (∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) → Prop}

/-- **The cocone leg of [Stacks, Tag 09YQ] in degree zero, on global sections.** The map
`F_i(X_i) → 𝒢(X)`: the pullback map on global sections along the projection `f_i : X ⟶ X_i` of the
limit cone, followed by the leg `ι_i` of the presentation. This is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg` in degree zero, by
`PresentedSystem.legSection_eq`. -/
public def PresentedSystem.legSection (E : PresentedSystem P) (i : Iᵒᵖ) :
    (E.sys.obj i).obj.obj (op (Scheme.Etale.mk (𝟙 (D.obj i)))) ⟶
      E.sheaf.obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))) :=
  etaleSectionsRestriction.{u, u + 1} (conePi c i) (E.sys.obj i) ≫
    (E.ι i).hom.app (op (Scheme.Etale.mk (𝟙 c.pt)))

/-- **The cocone leg on cohomology in degree zero is the cocone leg on global sections.**
`Stacks.EtaleCohomology.equiv₀_etaleCohomologyMapTo` at a projection of the limit cone and the leg
of the presentation. -/
public theorem PresentedSystem.legSection_eq (E : PresentedSystem P) (i : Iᵒᵖ)
    (x : Sheaf.H.{u + 1, u + 1} (E.sys.obj i) 0) :
    Sheaf.H.equiv₀ E.sheaf (etaleMkIdIsTerminal c.pt) (E.leg i 0 x) =
      E.legSection i (Sheaf.H.equiv₀ (E.sys.obj i) (etaleMkIdIsTerminal (D.obj i)) x) :=
  equiv₀_etaleCohomologyMapTo (conePi c i) (E.ι i) x

/-- **The degree-zero statement of [Stacks, Tag 09YQ] is a statement about global sections.** For
a presented system `E`, `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsCohomologyColimit E 0`
holds exactly when the global sections of `𝒢` on the limit are the filtered colimit of the global
sections of the `F_i`: every global section of `𝒢` is the image under some
`PresentedSystem.legSection` of a global section at a level, and a global section at a level
killed by its leg is killed by a transition to some further level.

This is the degree-zero hypothesis `H0` of
`isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic` (in namespace
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology`) with cohomology eliminated: no `Ext` group and
no `CategoryTheory.Sheaf.H` occurs on the right, only sections of sheaves over the terminal objects
of the small étale sites, which is what a degree-zero descent argument carried out at the geometry
produces.

Nothing is assumed: the identification is `CategoryTheory.Sheaf.H.equiv₀` at
`Stacks.EtaleCohomology.etaleMkIdIsTerminal`, an additive *equivalence*, and the two cocone maps
are carried across it by `PresentedSystem.legSection_eq` and `etaleSectionsTransition_eq`. -/
public theorem isCohomologyColimit_zero_iff (E : PresentedSystem P) :
    IsCohomologyColimit E 0 ↔
      ((∀ y : E.sheaf.obj.obj (op (Scheme.Etale.mk (𝟙 c.pt))),
          ∃ (i : Iᵒᵖ) (s : (E.sys.obj i).obj.obj (op (Scheme.Etale.mk (𝟙 (D.obj i))))),
            E.legSection i s = y) ∧
        ∀ (i : Iᵒᵖ) (s : (E.sys.obj i).obj.obj (op (Scheme.Etale.mk (𝟙 (D.obj i))))),
          E.legSection i s = 0 →
            ∃ (j : Iᵒᵖ) (a : j ⟶ i), etaleSectionsTransition E.sys a s = 0) := by
  let eG := Sheaf.H.equiv₀ E.sheaf (etaleMkIdIsTerminal c.pt)
  let eF := fun i : Iᵒᵖ => Sheaf.H.equiv₀ (E.sys.obj i) (etaleMkIdIsTerminal (D.obj i))
  have hleg : ∀ i s, eG (E.leg i 0 ((eF i).symm s)) = E.legSection i s := fun i s =>
    (E.legSection_eq i _).trans (congrArg _ ((eF i).apply_symm_apply s))
  refine ⟨fun h => ⟨fun y => ?_, fun i s hs => ?_⟩,
    fun h => ⟨fun y => ?_, fun i x hx => ?_⟩⟩
  · obtain ⟨i, x, hx⟩ := h.exists_leg_eq (eG.symm y)
    exact ⟨i, eF i x, (E.legSection_eq i x).symm.trans
      ((congrArg eG hx).trans (eG.apply_symm_apply y))⟩
  · obtain ⟨j, a, ha⟩ := h.exists_transition_eq_zero i ((eF i).symm s)
      (eG.map_eq_zero_iff.mp ((hleg i s).trans hs))
    refine ⟨j, a, ?_⟩
    exact ((congrArg (etaleSectionsTransition E.sys a) ((eF i).apply_symm_apply s)).symm.trans
      (etaleSectionsTransition_eq E.sys a _).symm).trans ((congrArg (eF j) ha).trans (map_zero _))
  · obtain ⟨i, s, hs⟩ := h.1 (eG y)
    exact ⟨i, (eF i).symm s, eG.injective ((hleg i s).trans hs)⟩
  · obtain ⟨j, a, ha⟩ := h.2 i (eF i x) ((E.legSection_eq i x).symm.trans
      ((congrArg eG hx).trans (map_zero eG)))
    exact ⟨j, a, (eF j).map_eq_zero_iff.mp ((etaleSectionsTransition_eq E.sys a x).trans ha)⟩

end SmallEtaleLimitCohomology

end Stacks.EtaleCohomology

end
