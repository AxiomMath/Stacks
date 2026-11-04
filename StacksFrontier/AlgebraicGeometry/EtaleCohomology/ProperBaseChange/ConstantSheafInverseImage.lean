module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeHorizontalMate
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusDescent

/-!
# The constant-sheaf comparison of an étale inverse image

Inverse image along a morphism of schemes carries the constant abelian sheaf to the constant
abelian sheaf, by `Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`. This comparison
is compatible with composition of inverse images, and at a constant sheaf it agrees with the
comparison of the inverse image along a self-map with the identity functor.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso_comp`: compatibility with
  composition of inverse images.
* `Stacks.EtaleCohomology.etaleSheafInverseImageComparison_app_constantSheaf`: at a constant
  sheaf the two comparisons agree.
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (A : Type*) [Category A]
  [HasWeakSheafify J A]

/-- The canonical section of the constant sheaf on `M` over an object of the site: the image of
`M` under the canonical map to the sheafification of the constant presheaf. -/
public def constantSheafSection (M : A) (U : C) :
    M ⟶ ((constantSheaf J A).obj M).obj.obj (op U) :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U)

/-- The unit of the constant-sheaf adjunction is the canonical section over the terminal
object. -/
public theorem constantSheafAdj_unit_app_eq {T : C} (hT : IsTerminal T) (M : A) :
    (constantSheafAdj J A hT).unit.app M = constantSheafSection J A M T :=
  constantSheafAdj_unit_app J A hT M

/-- The transpose of a map out of a constant sheaf is its value on the canonical section over the
terminal object. -/
public theorem constantSheafAdj_homEquiv_apply_eq {T : C} (hT : IsTerminal T) (M : A)
    (S : Sheaf J A) (φ : (constantSheaf J A).obj M ⟶ S) :
    (constantSheafAdj J A hT).homEquiv M S φ =
      constantSheafSection J A M T ≫ φ.hom.app (op T) :=
  constantSheafAdj_homEquiv_apply J A hT M S φ

/-- The canonical sections of a constant sheaf restrict to one another. -/
public theorem constantSheafSection_restrict (M : A) {U V : C} (h : V ⟶ U) :
    constantSheafSection J A M U ≫ ((constantSheaf J A).obj M).obj.map h.op =
      constantSheafSection J A M V :=
  (((toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality h.op).symm).trans
    (Category.id_comp _)

/-- The value of a map out of a constant sheaf on the canonical section over `V` is, for any
`h : V ⟶ U`, the restriction along `h` of its value on the canonical section over `U`. -/
public theorem constantSheafSection_comp (M : A) {S : Sheaf J A}
    (τ : (constantSheaf J A).obj M ⟶ S) {U V : C} (h : V ⟶ U) :
    constantSheafSection J A M V ≫ τ.hom.app (op V) =
      (constantSheafSection J A M U ≫ τ.hom.app (op U)) ≫ S.obj.map h.op := by
  rw [Category.assoc, ← τ.hom.naturality h.op, ← Category.assoc, constantSheafSection_restrict]

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

/-- Étale morphisms contain the identities. -/
public theorem etaleContainsIdentities :
    MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
  (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities

/-- The identity of `X`, the terminal object of the small étale site of `X`. -/
public def etaleSiteTerminal (X : Scheme.{u}) : X.Etale :=
  let := etaleContainsIdentities.{u}
  MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)

/-- The identity of `X` is terminal in the small étale site of `X`. -/
public def etaleSiteTerminalIsTerminal (X : Scheme.{u}) : IsTerminal (etaleSiteTerminal X) :=
  let := etaleContainsIdentities.{u}
  MorphismProperty.Over.mkIdTerminal _ _

section Constant

variable {X Y Z : Scheme.{u}}
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- The constant-sheaf comparison of an inverse image is the comparison of the two left adjoints
of evaluation at the terminal object of the source site. -/
public theorem etaleAbelianInverseImageConstantIso_eq (i : Y ⟶ X) :
    etaleAbelianInverseImageConstantIso.{u, v} i =
      ((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal X)).comp
          (etaleAbelianInverseImageDirectImageAdj.{u, v} i)).leftAdjointUniq
        (constantSheafAdj _ _
          ((etaleSiteTerminalIsTerminal X).isTerminalObj (smallEtaleBaseChange i))) :=
  rfl

/-- Along the constant-sheaf adjunction of the source site followed by the inverse-image
adjunction, the constant-sheaf comparison transposes to the canonical section of the constant
sheaf over the base change of the terminal object. -/
public theorem homEquiv_etaleAbelianInverseImageConstantIso (i : Y ⟶ X)
    (A : AddCommGrpCat.{max (u + 1) v}) :
    ((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal X)).comp
          (etaleAbelianInverseImageDirectImageAdj.{u, v} i)).homEquiv A
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A)
        ((etaleAbelianInverseImageConstantIso.{u, v} i).hom.app A) =
      Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology _ A
        ((smallEtaleBaseChange i).obj (etaleSiteTerminal X)) := by
  rw [etaleAbelianInverseImageConstantIso_eq, Adjunction.homEquiv_unit]
  exact (Adjunction.unit_leftAdjointUniq_hom_app _ _ A).trans
    (Stacks.ConstantSheaf.constantSheafAdj_unit_app_eq Y.smallEtaleTopology _ _ A)

/-- Composition of morphisms of sheaves is computed section by section. -/
public theorem sheaf_comp_hom_app {W : Type u} [Category.{v} W]
    {K : GrothendieckTopology W} {B : Type*} [Category B] {F G H : Sheaf K B} (f : F ⟶ G)
    (g : G ⟶ H) (U : Wᵒᵖ) : (f ≫ g).hom.app U = f.hom.app U ≫ g.hom.app U := rfl

omit [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] in
/-- The transpose along the constant-sheaf adjunction of the site of `X` followed by any
adjunction is the transpose along that adjunction, evaluated on the canonical section over the
terminal object. -/
public theorem constantSheaf_comp_homEquiv_apply {D : Type*} [Category D]
    {L : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤ D}
    {R : D ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (adj : L ⊣ R)
    (A : AddCommGrpCat.{max (u + 1) v}) (W : D)
    (θ : L.obj ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) ⟶ W) :
    ((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal X)).comp adj).homEquiv A W θ =
      Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _ A
          (etaleSiteTerminal X) ≫
        (adj.homEquiv _ W θ).hom.app (op (etaleSiteTerminal X)) := by
  rw [Adjunction.comp_homEquiv]
  exact Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply_eq X.smallEtaleTopology _ _ A _ _

/-- The transpose of the constant-sheaf comparison along the inverse-image adjunction carries the
canonical section of the constant sheaf over an étale `U` to the canonical section over the base
change of `U`. -/
public theorem constantSheafSection_comp_homEquiv_constantIso (i : Y ⟶ X)
    (A : AddCommGrpCat.{max (u + 1) v}) (U : X.Etale) :
    Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _ A U ≫
        ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).homEquiv _ _
          ((etaleAbelianInverseImageConstantIso.{u, v} i).hom.app A)).hom.app (op U) =
      Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology _ A
        ((smallEtaleBaseChange i).obj U) := by
  have hT := (constantSheaf_comp_homEquiv_apply
    (etaleAbelianInverseImageDirectImageAdj.{u, v} i) A _
    ((etaleAbelianInverseImageConstantIso.{u, v} i).hom.app A)).symm.trans
      (homEquiv_etaleAbelianInverseImageConstantIso.{u, v} i A)
  rw [Stacks.ConstantSheaf.constantSheafSection_comp X.smallEtaleTopology _ A
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} i).homEquiv _ _
      ((etaleAbelianInverseImageConstantIso.{u, v} i).hom.app A))
    ((etaleSiteTerminalIsTerminal X).from U), hT]
  exact Stacks.ConstantSheaf.constantSheafSection_restrict Y.smallEtaleTopology _ A
    ((smallEtaleBaseChange i).map ((etaleSiteTerminalIsTerminal X).from U))

/-- For a self-map `g` of `X` whose base change is isomorphic to the identity functor of the small
étale site, the comparison of `g^{-1}` with the identity functor agrees, at a constant sheaf, with
the canonical constant-sheaf comparison. -/
public theorem etaleSheafInverseImageComparison_app_constantSheaf (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange g).op.HasLeftKanExtension F]
    (A : AddCommGrpCat.{max (u + 1) v}) :
    (etaleSheafInverseImageComparison X g e AddCommGrpCat.{max (u + 1) v}).hom.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) =
      (etaleAbelianInverseImageConstantIso.{u, v} g).hom.app A := by
  have hunit : (etaleAbelianInverseImageDirectImageAdj.{u, v} g).unit.app
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) ≫
        (etaleAbelianDirectImage.{u, v} g).map
          ((etaleSheafInverseImageComparison X g e AddCommGrpCat.{max (u + 1) v}).hom.app
            ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A)) =
      (etaleSheafPushforwardComparison X g e AddCommGrpCat.{max (u + 1) v}).hom.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) :=
    sheafAdjunction_unit_comp_etaleSheafInverseImageComparison X g e _ _
  refine (((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal X)).comp
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g)).homEquiv A
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A)).injective ?_
  rw [homEquiv_etaleAbelianInverseImageConstantIso, constantSheaf_comp_homEquiv_apply,
    Adjunction.homEquiv_unit, hunit, etaleSheafPushforwardComparison_hom_app_hom_app]
  exact Stacks.ConstantSheaf.constantSheafSection_restrict X.smallEtaleTopology _ A
    (e.inv.app (etaleSiteTerminal X))

omit [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}] in
/-- The sections of the comparison of a composite direct image with the composite of the direct
images: restriction along the inverse of the base-change comparison. -/
public theorem etaleAbelianDirectImageCompIso'_inv_app_hom_app (f : Z ⟶ Y) (g : Y ⟶ X)
    (fg : Z ⟶ X) (hfg : fg = f ≫ g)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (U : (X.Etale)ᵒᵖ) :
    ((etaleAbelianDirectImageCompIso'.{u, v} f g fg hfg).inv.app F).hom.app U =
      F.obj.map (op ((smallEtaleBaseChangeComp' f g fg hfg).inv.app U.unop)) :=
  Category.comp_id _

/-- Taking the inverse image along `b` of the constant-sheaf comparison for `a` and then the
comparison for `b` is the comparison for the composite `b ≫ a`, read through the comparison of
the inverse image along the composite with the composite of the inverse images. -/
public theorem etaleAbelianInverseImageConstantIso_comp (a : Y ⟶ X) (b : Z ⟶ Y) (ba : Z ⟶ X)
    (hba : ba = b ≫ a) (A : AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImage.{u, v} b).map
          ((etaleAbelianInverseImageConstantIso.{u, v} a).hom.app A) ≫
        (etaleAbelianInverseImageConstantIso.{u, v} b).hom.app A =
      (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv.app
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) ≫
        (etaleAbelianInverseImageConstantIso.{u, v} ba).hom.app A := by
  have hconj := unit_conjugateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} ba)
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} a).comp
      (etaleAbelianInverseImageDirectImageAdj.{u, v} b))
    (etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A)
  rw [conjugateEquiv_etaleAbelianInverseImageCompIso'_inv.{u, v} b a ba hba] at hconj
  have hL : ((etaleAbelianInverseImageDirectImageAdj.{u, v} a).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} b)).homEquiv _ _
          ((etaleAbelianInverseImage.{u, v} b).map
              ((etaleAbelianInverseImageConstantIso.{u, v} a).hom.app A) ≫
            (etaleAbelianInverseImageConstantIso.{u, v} b).hom.app A) =
      (etaleAbelianInverseImageDirectImageAdj.{u, v} a).homEquiv _ _
          ((etaleAbelianInverseImageConstantIso.{u, v} a).hom.app A) ≫
        (etaleAbelianDirectImage.{u, v} a).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, v} b).homEquiv _ _
            ((etaleAbelianInverseImageConstantIso.{u, v} b).hom.app A)) := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right]
  have hR : ((etaleAbelianInverseImageDirectImageAdj.{u, v} a).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} b)).homEquiv _ _
          ((etaleAbelianInverseImageCompIso'.{u, v} b a ba hba).inv.app
              ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) ≫
            (etaleAbelianInverseImageConstantIso.{u, v} ba).hom.app A) =
      (etaleAbelianInverseImageDirectImageAdj.{u, v} ba).homEquiv _ _
          ((etaleAbelianInverseImageConstantIso.{u, v} ba).hom.app A) ≫
        (etaleAbelianDirectImageCompIso'.{u, v} b a ba hba).inv.app
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) := by
    have hnat : (etaleAbelianDirectImageCompIso'.{u, v} b a ba hba).inv.app
            ((etaleAbelianInverseImage.{u, v} ba).obj
              ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A)) ≫
          (etaleAbelianDirectImage.{u, v} b ⋙ etaleAbelianDirectImage.{u, v} a).map
            ((etaleAbelianInverseImageConstantIso.{u, v} ba).hom.app A) =
        (etaleAbelianDirectImage.{u, v} ba).map
            ((etaleAbelianInverseImageConstantIso.{u, v} ba).hom.app A) ≫
          (etaleAbelianDirectImageCompIso'.{u, v} b a ba hba).inv.app
            ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) :=
      ((etaleAbelianDirectImageCompIso'.{u, v} b a ba hba).inv.naturality _).symm
    conv_lhs => rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit, ← hconj]
    rw [Category.assoc, hnat, ← Category.assoc, ← Adjunction.homEquiv_unit]
  have hsec : Stacks.ConstantSheaf.constantSheafSection Z.smallEtaleTopology _ A
          ((smallEtaleBaseChange ba).obj (etaleSiteTerminal X)) ≫
        ((etaleAbelianDirectImageCompIso'.{u, v} b a ba hba).inv.app
            ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A)).hom.app
          (op (etaleSiteTerminal X)) =
      Stacks.ConstantSheaf.constantSheafSection Z.smallEtaleTopology _ A
        ((smallEtaleBaseChange b).obj
          ((smallEtaleBaseChange a).obj (etaleSiteTerminal X))) := by
    rw [etaleAbelianDirectImageCompIso'_inv_app_hom_app]
    exact Stacks.ConstantSheaf.constantSheafSection_restrict Z.smallEtaleTopology _ A
      ((smallEtaleBaseChangeComp' b a ba hba).inv.app (etaleSiteTerminal X))
  refine (((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal X)).comp
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} a).comp
      (etaleAbelianInverseImageDirectImageAdj.{u, v} b))).homEquiv A _).injective ?_
  rw [constantSheaf_comp_homEquiv_apply, constantSheaf_comp_homEquiv_apply, hL, hR]
  simp only [sheaf_comp_hom_app, ← Category.assoc]
  rw [constantSheafSection_comp_homEquiv_constantIso.{u, v} a A (etaleSiteTerminal X),
    constantSheafSection_comp_homEquiv_constantIso.{u, v} ba A (etaleSiteTerminal X)]
  exact (constantSheafSection_comp_homEquiv_constantIso.{u, v} b A
    ((smallEtaleBaseChange a).obj (etaleSiteTerminal X))).trans hsec.symm

end Constant

end Stacks.EtaleCohomology

end
