module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.BoundaryRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists

/-!
# A section of a quotient sheaf, read as a class of `H¹` of an étale scheme

Let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact sequence of abelian sheaves on `Y_étale` and `c` a
section of `F₃` over an étale `Y`-scheme `W`. Restricting the sequence to the small étale site of
the scheme `W` and taking the boundary of `c`, read as a global section there, gives a class
`κ_W(c) ∈ H¹(W, F₁|_W)`. If `κ_W(c)` dies under the inverse image along `W' ⟶ W`, a morphism of
the small étale site of `Y`, then `c|_{W'}` lifts to a section of `F₂` over `W'`.

This is how the vanishing of a higher direct image is reduced to the vanishing of classes of
étale cohomology of schemes: the sections of the cokernel of an injective presentation compute
the cohomology presheaf of Stacks 072W.

## Main definitions

* `Stacks.EtaleCohomology.restrictedBoundaryClass` — the class `κ_W(c)`.

## Main results

* `Stacks.EtaleCohomology.exists_lift_of_restrictedBoundaryClass` — the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {Y : Scheme.{u}} {S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})}
  (hS : S.ShortExact) {W : Y.Etale} (c : S.X₃.obj.obj (op W))

/-- The final object of the small étale site of `W.left`, composed with `W ⟶ Y`, maps to `W`. -/
def composeTerminalHom (W : Y.Etale) :
    (smallEtaleCompose W.hom).obj (etaleSiteTerminal W.left) ⟶ W :=
  MorphismProperty.Over.homMk (𝟙 W.left) rfl

/-- The section `c`, read as a morphism from the constant sheaf `ℤ` on the small étale site of
`W.left` to the restriction of `F₃`. -/
def restrictedSection : (constantSheaf W.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ (etaleRestriction.{u, 0} W.hom).obj S.X₃ :=
  ((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal W.left)).homEquiv _ _).symm
    (Stacks.Cohomology.CechDegreeOneVanishing.genHom _
      (S.X₃.obj.map (composeTerminalHom W).op c))

/-- The section `restrictedSection c` sends the generator `1` over the final object to the
restriction of `c`. -/
private lemma restrictedSection_app_one :
    (restrictedSection c).hom.app (op (etaleSiteTerminal W.left))
      (Stacks.ConstantSheaf.constantSheafSection W.left.smallEtaleTopology _
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (etaleSiteTerminal W.left) (ULift.up 1)) =
      S.X₃.obj.map (composeTerminalHom W).op c := by
  refine (ConcreteCategory.congr_hom (Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply_eq
    W.left.smallEtaleTopology AddCommGrpCat.{u + 1} (etaleSiteTerminalIsTerminal W.left)
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) _ (restrictedSection c)).symm (ULift.up 1)).trans ?_
  rw [restrictedSection, Equiv.apply_symm_apply]
  exact Stacks.Cohomology.CechDegreeOneVanishing.genHom_apply _ _

/-- **The class `κ_W(c) ∈ H¹(W, F₁|_W)`**: the boundary of the section `c`, read on the small
étale site of the scheme `W`. -/
def restrictedBoundaryClass :
    Sheaf.H.{u + 1} ((etaleRestriction.{u, 0} W.hom).obj S.X₁) 1 :=
  (Ext.mk₀ (restrictedSection c)).comp (hS.map_of_exact (etaleRestriction.{u, 0} W.hom)).extClass
    (zero_add 1)

/-- **A section whose class dies on `W'` lifts over `W'`.** -/
theorem exists_lift_of_restrictedBoundaryClass {W' : Y.Etale} (r : W' ⟶ W)
    (h : (restrictedBoundaryClass hS c).mapExactFunctor
      (etaleAbelianInverseImage.{u, 0} r.left) = 0) :
    ∃ i : S.X₂.obj.obj (op W'), S.g.hom.app (op W') i = S.X₃.obj.map r.op c := by
  rw [mapExactFunctor_etaleAbelianInverseImage_eq_zero_iff_etaleRestriction] at h
  let E : W.left.Etale := Scheme.Etale.mk r.left
  obtain ⟨s, hs⟩ := exists_lift_of_mapExactFunctor_etaleRestriction_eq_zero
    (hS.map_of_exact (etaleRestriction.{u, 0} W.hom)) (restrictedSection c) E h
  have hs' : S.g.hom.app (op ((smallEtaleCompose W.hom).obj E)) s =
      S.X₃.obj.map ((smallEtaleCompose W.hom).map ((etaleSiteTerminalIsTerminal W.left).from E)).op
        (S.X₃.obj.map (composeTerminalHom W).op c) :=
    hs.trans (congrArg _ (restrictedSection_app_one c))
  let j : W' ⟶ (smallEtaleCompose W.hom).obj E :=
    MorphismProperty.Over.homMk (𝟙 W'.left) (by
      change 𝟙 W'.left ≫ (r.left ≫ W.hom) = W'.hom
      rw [Category.id_comp, MorphismProperty.Over.w r])
  refine ⟨S.X₂.obj.map j.op s, ?_⟩
  refine (NatTrans.naturality_apply S.g.hom j.op s).trans ?_
  change S.X₃.obj.map j.op (S.g.hom.app _ s) = _
  rw [hs']
  change (S.X₃.obj.map _ ≫ S.X₃.obj.map _ ≫ S.X₃.obj.map j.op) c = _
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  congr 3

end Stacks.EtaleCohomology

end
