module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Sections of the inverse image of an abelian étale sheaf

Let `f : X ⟶ Y` be a morphism of schemes and `F` an abelian sheaf on the small étale site of
`Y`. The inverse image `f⁻¹F` is the sheafification of the presheaf sending an étale `X`-scheme
`U` to the colimit of the groups `F(W)` over the pairs `(W, U ⟶ W ×_Y X)` with `W` étale over
`Y`. Its sections are therefore described by two local statements, which this file proves for
the inverse image `Stacks.EtaleCohomology.smallEtalePullbackAb f` (the left adjoint of the
direct image):

* every section of `f⁻¹F` over `U` is, on a covering of `U`, the restriction of the image of a
  section of `F` over some `W` under the unit `F(W) ⟶ (f⁻¹F)(W ×_Y X)` of the adjunction;
* if the image of a section `h` of `F` over `W`, restricted along `U ⟶ W ×_Y X`, vanishes, then
  locally on `U` this restriction factors through some `W' ⟶ W` on which `h` vanishes.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePullbackAbUnitApp`: the unit `F(W) ⟶ (f⁻¹F)(W ×_Y X)`.

## Main results

* `Stacks.EtaleCohomology.exists_covering_smallEtalePullbackAb_eq_unitApp`: sections of `f⁻¹F`
  are locally images of sections of `F`.
* `Stacks.EtaleCohomology.exists_covering_of_smallEtalePullbackAb_unitApp_eq_zero`: a section of
  `F` whose image vanishes vanishes locally on a further restriction.

## Implementation notes

The inverse image `Functor.sheafPullback` is defined as an abstract left adjoint; it is compared
with Mathlib's construction `Functor.sheafPullbackConstruction.sheafPullback` (left Kan extension
along `smallEtaleBaseChange f` followed by sheafification) through
`Functor.sheafPullbackConstruction.sheafPullbackIso`, which intertwines the two units. The
statements are then the local surjectivity and local injectivity of sheafification together with
the description of sections of a left Kan extension as a colimit over the category of pairs
`(W, U ⟶ W ×_Y X)`, which is filtered because base change is representably flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The unit of the inverse image adjunction, on sections: `F(W) ⟶ (f⁻¹F)(W ×_Y X)`. -/
abbrev smallEtalePullbackAbUnitApp (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (W : Y.Etale) :
    F.obj.obj (op W) ⟶
      ((smallEtalePullbackAb f).obj F).obj.obj (op ((smallEtaleBaseChange f).obj W)) :=
  ((smallEtaleAdjunctionAb f).unit.app F).hom.app (op W)

section Construction

/-- The category of pairs `(W, U ⟶ W ×_Y X)` indexing the left Kan extension is filtered. -/
instance (U : X.Etale) :
    IsFiltered (CostructuredArrow (smallEtaleBaseChange f).op (op U)) :=
  IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange f) U)

/-- The left Kan extension along base change, at the coefficients of étale cohomology. -/
abbrev smallEtaleLanAb (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    X.Etaleᵒᵖ ⥤ Ab.{u + 1} :=
  (smallEtaleBaseChange f).op.lan.obj F.obj

/-- **A section of the left Kan extension is a pullback of a section of `F`.** -/
theorem exists_rep_smallEtaleLanAb (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (U : X.Etale)
    (t : ToType ((smallEtaleLanAb f F).obj (op U))) :
    ∃ (W : Y.Etale) (k : U ⟶ (smallEtaleBaseChange f).obj W) (s : ToType (F.obj.obj (op W))),
      (smallEtaleLanAb f F).map k.op
        (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) s) = t := by
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
  have hcolim := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      ((smallEtaleBaseChange f).op.lan.obj F.obj)
      ((smallEtaleBaseChange f).op.lanUnit.app F.obj) (op U)
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep _ hcolim t
  refine ⟨j.left.unop, j.hom.unop, y, ?_⟩
  exact hy

/-- **Vanishing in the left Kan extension is witnessed over a single object.** -/
theorem exists_eq_zero_of_smallEtaleLanAb_eq_zero (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    {U : X.Etale} {W : Y.Etale} (k : U ⟶ (smallEtaleBaseChange f).obj W)
    (h : ToType (F.obj.obj (op W)))
    (hz : (smallEtaleLanAb f F).map k.op
      (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h) = 0) :
    ∃ (W' : Y.Etale) (q : W' ⟶ W) (k' : U ⟶ (smallEtaleBaseChange f).obj W'),
      k' ≫ (smallEtaleBaseChange f).map q = k ∧ F.obj.map q.op h = 0 := by
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
  have hcolim := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      ((smallEtaleBaseChange f).op.lan.obj F.obj)
      ((smallEtaleBaseChange f).op.lanUnit.app F.obj) (op U)
  let j : CostructuredArrow (smallEtaleBaseChange f).op (op U) := CostructuredArrow.mk k.op
  obtain ⟨j', φ, φ₂, hφ⟩ := Concrete.isColimit_exists_of_rep_eq _ hcolim (i := j) (j := j) h 0
    (by
      show (smallEtaleLanAb f F).map k.op
        (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h) =
          (smallEtaleLanAb f F).map k.op
            (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) 0)
      rw [hz, map_zero, map_zero])
  exact ⟨j'.left.unop, φ.left.unop, j'.hom.unop,
    Quiver.Hom.op_inj (CostructuredArrow.w φ), hφ.trans (map_zero _)⟩

/-- The unit of Mathlib's construction of the inverse image, on underlying presheaves: the unit
of the left Kan extension followed by sheafification. -/
lemma sheafAdjunctionContinuous_unit_app_hom (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange f)
        Ab.{u + 1} (smallEtaleTopology Y) (smallEtaleTopology X)).unit.app F).hom =
      (smallEtaleBaseChange f).op.lanUnit.app F.obj ≫
        Functor.whiskerLeft (smallEtaleBaseChange f).op
          (toSheafify (smallEtaleTopology X) (smallEtaleLanAb f F)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (adj := ((smallEtaleBaseChange f).op.lanAdjunction Ab.{u + 1}).comp
      (sheafificationAdjunction (smallEtaleTopology X) Ab.{u + 1}))
    (hiC := fullyFaithfulSheafToPresheaf (smallEtaleTopology Y) Ab.{u + 1})
    (hiD := Functor.FullyFaithful.id _)
    (L := Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange f) Ab.{u + 1}
      (smallEtaleTopology Y) (smallEtaleTopology X))
    (R := (smallEtaleBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
      (smallEtaleTopology Y) (smallEtaleTopology X))
    (comm1 := Iso.refl _) (comm2 := Iso.refl _) F
  refine h.trans ?_
  ext W x
  rfl

/-- The comparison of the inverse image with Mathlib's construction. -/
abbrev smallEtalePullbackAbConstructionIso :
    smallEtalePullbackAb f ≅ Functor.sheafPullbackConstruction.sheafPullback
      (smallEtaleBaseChange f) Ab.{u + 1} (smallEtaleTopology Y) (smallEtaleTopology X) :=
  Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange f) Ab.{u + 1}
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- The comparison carries the unit to the unit of the construction. -/
lemma smallEtalePullbackAbConstructionIso_unitApp (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (W : Y.Etale) (h : ToType (F.obj.obj (op W))) :
    ((smallEtalePullbackAbConstructionIso f).hom.app F).hom.app
        (op ((smallEtaleBaseChange f).obj W)) (smallEtalePullbackAbUnitApp f F W h) =
      (toSheafify (smallEtaleTopology X) (smallEtaleLanAb f F)).app
        (op ((smallEtaleBaseChange f).obj W))
        (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h) := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleAdjunctionAb f)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange f)
      Ab.{u + 1} (smallEtaleTopology Y) (smallEtaleTopology X)) F
  have hu' := congrArg (fun φ => (φ.hom.app (op W)) h) hu
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, sheafAdjunctionContinuous_unit_app_hom f F,
    Functor.whiskerLeft_app] at hu'
  exact hu'

end Construction

/-- The comparison with Mathlib's construction carries the restricted unit image to the
sheafified restriction of the unit of the left Kan extension. -/
private theorem iso_map_unitApp_eq_toSheafify_map (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    {U : X.Etale} {W : Y.Etale} (m : U ⟶ (smallEtaleBaseChange f).obj W)
    (h : ToType (F.obj.obj (op W))) :
    ((smallEtalePullbackAbConstructionIso f).hom.app F).hom.app (op U)
        (((smallEtalePullbackAb f).obj F).obj.map m.op (smallEtalePullbackAbUnitApp f F W h)) =
      (toSheafify (smallEtaleTopology X) (smallEtaleLanAb f F)).app (op U)
        ((smallEtaleLanAb f F).map m.op
          (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h)) := by
  have nat₂ := congrArg (fun φ => φ (smallEtalePullbackAbUnitApp f F W h))
    (((smallEtalePullbackAbConstructionIso f).hom.app F).hom.naturality m.op)
  have nat₃ := congrArg
    (fun φ => φ (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h))
    ((toSheafify (smallEtaleTopology X) (smallEtaleLanAb f F)).naturality m.op)
  simp only [ConcreteCategory.comp_apply] at nat₂ nat₃
  rw [smallEtalePullbackAbConstructionIso_unitApp] at nat₂
  exact nat₂.trans nat₃.symm

/-- **Sections of an inverse image are locally images of sections of the sheaf.** Every section
`x` of `f⁻¹F` over an object `U` of the small étale site of `X` is, on a covering sieve of `U`,
the restriction along some `U' ⟶ W ×_Y X` of the image of a section of `F` over `W` under the
unit of the adjunction. -/
theorem exists_covering_smallEtalePullbackAb_eq_unitApp
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (U : X.Etale)
    (x : ToType (((smallEtalePullbackAb f).obj F).obj.obj (op U))) :
    ∃ S ∈ smallEtaleTopology X U, ∀ ⦃U' : X.Etale⦄ (g : U' ⟶ U), S g →
      ∃ (W : Y.Etale) (m : U' ⟶ (smallEtaleBaseChange f).obj W)
        (h : ToType (F.obj.obj (op W))),
        ((smallEtalePullbackAb f).obj F).obj.map g.op x =
          ((smallEtalePullbackAb f).obj F).obj.map m.op (smallEtalePullbackAbUnitApp f F W h) := by
  set ε := smallEtalePullbackAbConstructionIso f
  let P := smallEtaleLanAb f F
  set x' := (ε.hom.app F).hom.app (op U) x
  refine ⟨Presheaf.imageSieve (toSheafify (smallEtaleTopology X) P) x',
    (Presheaf.isLocallySurjective_toSheafify' _ P).imageSieve_mem x', ?_⟩
  rintro U' g ⟨y, hy⟩
  obtain ⟨W, k, s, hks⟩ := exists_rep_smallEtaleLanAb f F U' y
  refine ⟨W, k, s, ?_⟩
  have hinj : Function.Injective ((ε.hom.app F).hom.app (op U')) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
  apply hinj
  have nat₁ := congrArg (fun φ => φ x) ((ε.hom.app F).hom.naturality g.op)
  simp only [ConcreteCategory.comp_apply] at nat₁
  rw [iso_map_unitApp_eq_toSheafify_map, hks]
  exact nat₁.trans hy.symm

/-- **A section whose image in the inverse image vanishes vanishes locally further down.** If the
image of a section `h` of `F` over `W`, restricted along `m : U ⟶ W ×_Y X`, vanishes, then on a
covering sieve of `U` every restriction `U' ⟶ U` of `m` factors through `W' ×_Y X` for some
`q : W' ⟶ W` with `h|_{W'} = 0`. -/
theorem exists_covering_of_smallEtalePullbackAb_unitApp_eq_zero
    (F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) {U : X.Etale} {W : Y.Etale}
    (m : U ⟶ (smallEtaleBaseChange f).obj W) (h : ToType (F.obj.obj (op W)))
    (hz : ((smallEtalePullbackAb f).obj F).obj.map m.op
      (smallEtalePullbackAbUnitApp f F W h) = 0) :
    ∃ S ∈ smallEtaleTopology X U, ∀ ⦃U' : X.Etale⦄ (g : U' ⟶ U), S g →
      ∃ (W' : Y.Etale) (q : W' ⟶ W) (m' : U' ⟶ (smallEtaleBaseChange f).obj W'),
        m' ≫ (smallEtaleBaseChange f).map q = g ≫ m ∧ F.obj.map q.op h = 0 := by
  set ε := smallEtalePullbackAbConstructionIso f
  let P := smallEtaleLanAb f F
  let y := P.map m.op (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h)
  have hy : (toSheafify (smallEtaleTopology X) P).app (op U) y =
      (toSheafify (smallEtaleTopology X) P).app (op U) 0 := by
    rw [map_zero]
    rw [← iso_map_unitApp_eq_toSheafify_map, hz]
    exact map_zero _
  refine ⟨Presheaf.equalizerSieve y 0,
    (Presheaf.isLocallyInjective_toSheafify' _ P).equalizerSieve_mem y 0 hy, ?_⟩
  intro U' g hg
  have hg' : P.map (g ≫ m).op
      (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h) = 0 := by
    have : P.map g.op y = P.map g.op 0 := hg
    rw [map_zero] at this
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact this
  exact exists_eq_zero_of_smallEtaleLanAb_eq_zero f F (g ≫ m) h hg'

end Stacks.EtaleCohomology

end
