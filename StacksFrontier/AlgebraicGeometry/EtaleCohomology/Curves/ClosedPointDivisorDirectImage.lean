module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.DirectImageSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointSkyscraperSections

/-!
# The skyscraper sheaves `i_{x,*} 𝐙` along a morphism of schemes

Let `p : X' ⟶ X` be a morphism of schemes and `x'` a point of `X'`. Pulling locally constant
functions back along `Spec κ(x') ⟶ Spec κ(p x')` gives a morphism of sheaves on `X_ét`

`i_{p x',*} 𝐙 ⟶ p_* i_{x',*} 𝐙`,

which on sections over an étale `X`-scheme `U` is the pullback of locally constant `𝐙`-valued
functions along the natural map of fibres `(U ×_X X') ×_{X'} Spec κ(x') ⟶ U ×_X Spec κ(p x')`.
Given a map `σ` from the closed points of `X` to those of `X'` with `p (σ x) = x`, these assemble
into a morphism `⨁_x i_{x,*} 𝐙 ⟶ p_* ⨁_{x'} i_{x',*} 𝐙`, the third component of the morphism of
divisor sequences under scalar extension.

## Main definitions

* `Stacks.EtaleCohomology.constantSheafDirectImageMap`: `𝐙_Y ⟶ a_* 𝐙_{Y'}` for `a : Y' ⟶ Y`,
  pulling back locally constant functions.
* `Stacks.EtaleCohomology.integerSkyscraperDirectImageMap`: `i_{p x',*} 𝐙 ⟶ p_* i_{x',*} 𝐙`.
* `Stacks.EtaleCohomology.closedPointDivisorDirectImageMap`:
  `⨁_x i_{x,*} 𝐙 ⟶ p_* ⨁_{x'} i_{x',*} 𝐙` along a section `σ` of `p` on closed points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section Constant

variable {Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (A : Type (max (u + 1) v)) [AddCommGroup A]

/-- Pullback of locally constant functions along the projections `V ×_Y Y' ⟶ V`, as a morphism
of presheaves on `Y_ét`. -/
def locallyConstantMapsDirectImageMap :
    smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} Y A ⟶
      (smallEtaleBaseChange a).op ⋙ smallEtaleLocallyConstantMapsAb.{u, max (u + 1) v} Y' A :=
  Functor.whiskerRight (NatTrans.op (smallEtaleBaseChangeProjection a))
    (locallyConstantMapsAb.{u, max (u + 1) v} A)

/-- **The morphism `A_Y ⟶ a_* A_{Y'}` of constant sheaves**: on sections over an étale
`Y`-scheme `V`, read as locally constant functions, it is pullback along `V ×_Y Y' ⟶ V`. -/
def constantSheafDirectImageMap :
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of A) ⟶
      (etaleAbelianDirectImage.{u, v} a).obj
        ((constantSheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (AddCommGrpCat.of A)) :=
  ⟨(smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v} Y A).hom ≫
    locallyConstantMapsDirectImageMap.{u, v} a A ≫
      Functor.whiskerLeft (smallEtaleBaseChange a).op
        (smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v} Y' A).inv⟩

/-- **On sections, `A_Y ⟶ a_* A_{Y'}` is pullback of locally constant functions.** -/
theorem constantSheafDirectImageMap_app (V : Y.Etale)
    (s : ToType (((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
      (AddCommGrpCat.of A)).obj.obj (op V))) :
    (smallEtaleConstantSheafSectionsIsoLocallyConstantMapsAb.{u, v} Y' A
        ((smallEtaleBaseChange a).obj V)).hom
        ((constantSheafDirectImageMap.{u, v} a A).hom.app (op V) s) =
      ((smallEtaleConstantSheafSectionsIsoLocallyConstantMapsAb.{u, v} Y A V).hom s).comap
        (pullback.fst V.hom a).base.hom := by
  show ((smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v} Y' A).hom.app _)
      (((smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v} Y' A).inv.app _)
        ((locallyConstantMapsDirectImageMap.{u, v} a A).app _
          (((smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v} Y A).hom.app _) s))) = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app, ConcreteCategory.id_apply]
  rfl

end Constant

section Skyscraper

variable {X X' : Scheme.{u}} (p : X' ⟶ X)

/-- **The morphism `i_{p x',*} 𝐙 ⟶ p_* i_{x',*} 𝐙`** for a morphism of schemes `p : X' ⟶ X` and
a point `x'` of `X'`: pullback of locally constant functions along `Spec κ(x') ⟶ Spec κ(p x')`,
followed by the base change square of `i_{x'} ≫ p = (Spec κ(x') ⟶ Spec κ(p x')) ≫ i_{p x'}`. -/
def integerSkyscraperDirectImageMap (x' : X') :
    integerSkyscraper.{u, v} X (p.base x') ⟶
      (etaleAbelianDirectImage.{u, v} p).obj (integerSkyscraper.{u, v} X' x') :=
  (residueFieldDirectImage.{u, v} X (p.base x')).map
      (constantSheafDirectImageMap.{u, v} (Spec.map (p.residueFieldMap x'))
        (ULift.{max (u + 1) v} ℤ)) ≫
    etaleDirectImageSquareMap.{u, v} (p.SpecMap_residueFieldMap_fromSpecResidueField x').symm _

/-- **On sections, `i_{p x',*} 𝐙 ⟶ p_* i_{x',*} 𝐙` is pullback of locally constant functions**
along the map of fibres `(U ×_X X') ×_{X'} Spec κ(x') ⟶ U ×_X Spec κ(p x')`. -/
theorem integerSkyscraperDirectImageMap_app (x' : X') (U : X.Etale)
    (s : ToType ((integerSkyscraper.{u, v} X (p.base x')).obj.obj (op U))) :
    (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X' x'
        ((smallEtaleBaseChange p).obj U)).hom
        ((integerSkyscraperDirectImageMap.{u, v} p x').hom.app (op U) s) =
      ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X (p.base x') U).hom s).comap
        (smallEtaleBaseChangeSquareLeft (p.SpecMap_residueFieldMap_fromSpecResidueField x').symm U ≫
          pullback.fst _ _).base.hom := by
  have hnat := (smallEtaleConstantSheafIsoLocallyConstantMapsAb.{u, v}
    (Spec (X'.residueField x')) (ULift.{max (u + 1) v} ℤ)).hom.naturality
      ((smallEtaleBaseChangeSquare (p.SpecMap_residueFieldMap_fromSpecResidueField x').symm).hom.app
        U).op
  have h1 := ConcreteCategory.congr_hom hnat
    ((constantSheafDirectImageMap.{u, v} (Spec.map (p.residueFieldMap x'))
      (ULift.{max (u + 1) v} ℤ)).hom.app (op ((smallEtaleBaseChange
        (X.fromSpecResidueField (p.base x'))).obj U)) s)
  refine h1.trans ?_
  show LocallyConstant.comap _ ((smallEtaleConstantSheafSectionsIsoLocallyConstantMapsAb.{u, v}
    (Spec (X'.residueField x')) (ULift.{max (u + 1) v} ℤ) _).hom
      ((constantSheafDirectImageMap.{u, v} (Spec.map (p.residueFieldMap x'))
        (ULift.{max (u + 1) v} ℤ)).hom.app _ s)) = _
  exact (congrArg (LocallyConstant.comap _) (constantSheafDirectImageMap_app.{u, v}
    (Spec.map (p.residueFieldMap x')) (ULift.{max (u + 1) v} ℤ) _ s)).trans rfl

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- **The morphism `⨁_x i_{x,*} 𝐙 ⟶ p_* ⨁_{x'} i_{x',*} 𝐙`** along a map `σ` from the closed
points of `X` to those of `X'` lying over them: the summand at `x` is sent to the summand at
`σ x` by `Stacks.EtaleCohomology.integerSkyscraperDirectImageMap`. -/
def closedPointDivisorDirectImageMap (σ : closedPoints X → closedPoints X')
    (hσ : ∀ x, p.base (σ x).1 = x.1) :
    closedPointDivisorSheaf.{u, v} X ⟶
      (etaleAbelianDirectImage.{u, v} p).obj (closedPointDivisorSheaf.{u, v} X') :=
  Sigma.desc fun x => eqToHom (by rw [closedPointSkyscraper, hσ x]) ≫
    integerSkyscraperDirectImageMap.{u, v} p (σ x).1 ≫
      (etaleAbelianDirectImage.{u, v} p).map (closedPointDivisorSheaf.ι.{u, v} X' (σ x))

/-- The morphism `⨁_x i_{x,*} 𝐙 ⟶ p_* ⨁_{x'} i_{x',*} 𝐙` on the summand at `x`. -/
theorem ι_closedPointDivisorDirectImageMap (σ : closedPoints X → closedPoints X')
    (hσ : ∀ x, p.base (σ x).1 = x.1) (x : closedPoints X) :
    closedPointDivisorSheaf.ι.{u, v} X x ≫ closedPointDivisorDirectImageMap.{u, v} p σ hσ =
      eqToHom (by rw [closedPointSkyscraper, hσ x]) ≫
        integerSkyscraperDirectImageMap.{u, v} p (σ x).1 ≫
          (etaleAbelianDirectImage.{u, v} p).map (closedPointDivisorSheaf.ι.{u, v} X' (σ x)) :=
  Sigma.ι_desc _ x

end Skyscraper

end Stacks.EtaleCohomology

end
