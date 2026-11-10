module
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RestrictScalarsCoextension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImageUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence

/-!
# Inverse image of the Artin–Schreier sequence

Let `π : Y ⟶ X` be a morphism of schemes. Inverse image along `π` on abelian sheaves of the small
étale sites compares the additive group of `X` with that of `Y`: the comparison
`π⁻¹ 𝐆_{a,X} ⟶ 𝐆_{a,Y}` is the adjoint transpose of the direct-image comparison
`𝐆_{a,X} ⟶ π_* 𝐆_{a,Y}`, which pulls a function on an étale `X`-scheme `U` back along the
projection `U ×_X Y ⟶ U`. This file proves that the comparison is compatible with the three maps
the Artin–Schreier argument uses: the inclusion of the constant sheaf `𝐙/p𝐙`, the Frobenius
`x ↦ x ^ p`, and multiplication by a global function. On cohomology it gives a restriction map
`H ^ q (X_étale, 𝐆_a) ⟶ H ^ q (Y_étale, 𝐆_a)` and the corresponding commutative squares.

## Main definitions

* `Stacks.ArtinSchreier.additiveDirectImageComparisonGeneral`: `𝐆_{a,X} ⟶ π_* 𝐆_{a,Y}`.
* `Stacks.ArtinSchreier.additiveInverseImageComparisonGeneral`: `π⁻¹ 𝐆_{a,X} ⟶ 𝐆_{a,Y}`.
* `Stacks.ArtinSchreier.additiveCohomologyRestriction`: the induced map
  `H ^ q (X_étale, 𝐆_a) ⟶ H ^ q (Y_étale, 𝐆_a)`.

## Main results

* `Stacks.ArtinSchreier.zmodSheafHom_comp_additiveInverseImageComparison`: compatibility with the
  inclusions of `𝐙/p𝐙`, through the canonical comparison `π⁻¹ 𝐙/p𝐙 ≅ 𝐙/p𝐙`.
* `Stacks.ArtinSchreier.frobeniusMap_comp_additiveInverseImageComparison` and
  `Stacks.ArtinSchreier.scalarMap_comp_additiveInverseImageComparison`: compatibility with the
  Frobenius and with multiplication by a global function `c` of `X`, which becomes
  multiplication by its pullback `π^♯ c`.
* `Stacks.ArtinSchreier.additiveCohomologyRestriction_sheafH_map_zmodSheafHom`,
  `Stacks.ArtinSchreier.additiveCohomologyRestriction_sheafH_map_frobeniusMap` and
  `Stacks.ArtinSchreier.additiveCohomologyRestriction_sheafH_map_scalarMap`: the same on
  cohomology, the first against the restriction map of `𝐙/p𝐙`.

## References

* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the sequence.
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB): functoriality of the
  small étale topos.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology

universe u v w

namespace Stacks.ArtinSchreier

variable {X Y : Scheme.{u}} (π : Y ⟶ X)

/-- **The comparison `𝐆_{a,X} ⟶ π_* 𝐆_{a,Y}`** for a morphism of schemes `π : Y ⟶ X`: a function
on an étale `X`-scheme `U` is pulled back along the projection `U ×_X Y ⟶ U`, giving a function
on `U ×_X Y`, which is a section of `π_* 𝐆_{a,Y}` over `U`. -/
def additiveDirectImageComparisonGeneral :
    additiveSheaf.{u, v} X ⟶ (etaleAbelianDirectImage.{u, v} π).obj (additiveSheaf.{u, v} Y) :=
  ⟨Functor.whiskerRight (NatTrans.op (smallEtaleBaseChangeProjection π))
    (Scheme.Γ ⋙ additiveCoefficients.{u, v})⟩

/-- **On sections the comparison is pullback along `U ×_X Y ⟶ U`.** -/
@[simp]
theorem additiveDirectImageComparison_app_ofSection_general (U : X.Etale) (x : Γ(U.left, ⊤)) :
    (additiveDirectImageComparisonGeneral.{u, v} π).hom.app (op U) (ofSection x) =
      ofSection (U := (smallEtaleBaseChange π).obj U) ((pullback.fst U.hom π).appTop x) :=
  rfl

/-- **The comparison `π⁻¹ 𝐆_{a,X} ⟶ 𝐆_{a,Y}`**: the adjoint transpose of
`Stacks.ArtinSchreier.additiveDirectImageComparisonGeneral`. -/
def additiveInverseImageComparisonGeneral :
    (etaleAbelianInverseImage.{u, v} π).obj (additiveSheaf.{u, v} X) ⟶ additiveSheaf.{u, v} Y :=
  ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv _ _).symm
    (additiveDirectImageComparisonGeneral.{u, v} π)

/-- The transpose of the comparison on `𝐆_a` is the direct-image comparison. -/
theorem homEquiv_additiveInverseImageComparison :
    (etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv _ _
        (additiveInverseImageComparisonGeneral.{u, v} π) =
      additiveDirectImageComparisonGeneral.{u, v} π :=
  Equiv.apply_symm_apply _ _

/-- An endomorphism of `𝐆_{a,X}` and one of `𝐆_{a,Y}` which the direct-image comparison
intertwines are intertwined by the inverse-image comparison. -/
theorem map_comp_additiveInverseImageComparison {φX : additiveSheaf.{u, v} X ⟶ additiveSheaf X}
    {φY : additiveSheaf.{u, v} Y ⟶ additiveSheaf Y}
    (h : φX ≫ additiveDirectImageComparisonGeneral.{u, v} π =
      additiveDirectImageComparisonGeneral.{u, v} π ≫ (etaleAbelianDirectImage.{u, v} π).map φY) :
    (etaleAbelianInverseImage.{u, v} π).map φX ≫ additiveInverseImageComparisonGeneral.{u, v} π =
      additiveInverseImageComparisonGeneral.{u, v} π ≫ φY := by
  apply ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv _ _).injective
  rwa [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_additiveInverseImageComparison]

/-- The direct-image comparison commutes with the Frobenius. -/
theorem frobeniusMap_comp_additiveDirectImageComparison_general {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) :
    frobeniusMap.{u, v} X hp hX ≫ additiveDirectImageComparisonGeneral.{u, v} π =
      additiveDirectImageComparisonGeneral.{u, v} π ≫
        (etaleAbelianDirectImage.{u, v} π).map (frobeniusMap.{u, v} Y hp hY) := by
  ext U x
  obtain ⟨x, rfl⟩ := ofSection_surjective x
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  rw [frobeniusMap_app_ofSection, additiveDirectImageComparison_app_ofSection_general,
    additiveDirectImageComparison_app_ofSection_general]
  change _ = ofSection (U := (smallEtaleBaseChange π).obj U.unop)
    ((pullback.fst U.unop.hom π).appTop x ^ p)
  rw [map_pow]

/-- **The comparison on `𝐆_a` commutes with the Frobenius.** -/
theorem frobeniusMap_comp_additiveInverseImageComparison {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) :
    (etaleAbelianInverseImage.{u, v} π).map (frobeniusMap.{u, v} X hp hX) ≫
        additiveInverseImageComparisonGeneral.{u, v} π =
      additiveInverseImageComparisonGeneral.{u, v} π ≫ frobeniusMap.{u, v} Y hp hY :=
  map_comp_additiveInverseImageComparison π
    (frobeniusMap_comp_additiveDirectImageComparison_general π hp hX hY)

/-- Pulling back the pullback of a global function of `X` to an étale `U` along `U ×_X Y ⟶ U` is
pulling back its pullback to `Y`. -/
theorem pullback_fst_appTop_appTop (U : X.Etale) (c : Γ(X, ⊤)) :
    (pullback.fst U.hom π).appTop (U.hom.appTop (X := U.left) c) =
      (pullback.snd U.hom π).appTop (π.appTop c) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, pullback.condition]

/-- The direct-image comparison carries multiplication by a global function `c` of `X` to
multiplication by its pullback `π^♯ c`. -/
theorem scalarMap_comp_additiveDirectImageComparison (c : Γ(X, ⊤)) :
    scalarMap.{u, v} X c ≫ additiveDirectImageComparisonGeneral.{u, v} π =
      additiveDirectImageComparisonGeneral.{u, v} π ≫
        (etaleAbelianDirectImage.{u, v} π).map (scalarMap.{u, v} Y (π.appTop c)) := by
  ext U x
  obtain ⟨x, rfl⟩ := ofSection_surjective x
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  rw [scalarMap_app_ofSection, additiveDirectImageComparison_app_ofSection_general,
    additiveDirectImageComparison_app_ofSection_general]
  change _ = ofSection (U := (smallEtaleBaseChange π).obj U.unop)
    ((pullback.snd U.unop.hom π).appTop (π.appTop c) *
    (pullback.fst U.unop.hom π).appTop x)
  rw [map_mul, pullback_fst_appTop_appTop]

/-- **The comparison on `𝐆_a` carries multiplication by `c` to multiplication by `π^♯ c`.** -/
theorem scalarMap_comp_additiveInverseImageComparison (c : Γ(X, ⊤)) :
    (etaleAbelianInverseImage.{u, v} π).map (scalarMap.{u, v} X c) ≫
        additiveInverseImageComparisonGeneral.{u, v} π =
      additiveInverseImageComparisonGeneral.{u, v} π ≫ scalarMap.{u, v} Y (π.appTop c) :=
  map_comp_additiveInverseImageComparison π (scalarMap_comp_additiveDirectImageComparison π c)

/-- The canonical section of `𝐙/p𝐙` over `U` followed by the inclusion into `𝐆_a` is the scalar
map `𝐙/p𝐙 ⟶ Γ(U, 𝒪_U)`. -/
theorem constantSheafSection_comp_zmodSheafHom {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0) (U : X.Etale) :
    Stacks.ConstantSheaf.constantSheafSection X.smallEtaleTopology _
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p))) U ≫
        (zmodSheafHom.{u, v} X hX).hom.app (op U) =
      (zmodPresheafHom.{u, v} X hX).app (op U) :=
  congrArg (fun α => NatTrans.app α (op U)) (toSheafify_zmodSheafHom.{u, v} X hX)

/-- **The comparison on `𝐆_a` is compatible with the inclusions of `𝐙/p𝐙`**, through the
canonical comparison `π⁻¹ 𝐙/p𝐙 ≅ 𝐙/p𝐙` of
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`. -/
theorem zmodSheafHom_comp_additiveInverseImageComparison {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) :
    (etaleAbelianInverseImage.{u, v} π).map (zmodSheafHom.{u, v} X hX) ≫
        additiveInverseImageComparisonGeneral.{u, v} π =
      (etaleAbelianInverseImageConstantIso.{u, v} π).hom.app
          (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p))) ≫
        zmodSheafHom.{u, v} Y hY := by
  apply (((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal X)).comp
    (etaleAbelianInverseImageDirectImageAdj.{u, v} π)).homEquiv _ _).injective
  rw [constantSheaf_comp_homEquiv_apply.{u, v} (etaleAbelianInverseImageDirectImageAdj.{u, v} π),
    constantSheaf_comp_homEquiv_apply.{u, v} (etaleAbelianInverseImageDirectImageAdj.{u, v} π),
    Adjunction.homEquiv_naturality_left, homEquiv_additiveInverseImageComparison,
    Adjunction.homEquiv_naturality_right]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  ext ⟨m⟩
  have h1 := ConcreteCategory.congr_hom
    (constantSheafSection_comp_zmodSheafHom.{u, v} hX (etaleSiteTerminal X)) (ULift.up m)
  have h2 := ConcreteCategory.congr_hom
    (constantSheafSection_comp_homEquiv_constantIso.{u, v} π
      (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p))) (etaleSiteTerminal X)) (ULift.up m)
  have h3 := ConcreteCategory.congr_hom
    (constantSheafSection_comp_zmodSheafHom.{u, v} hY
      ((smallEtaleBaseChange π).obj (etaleSiteTerminal X))) (ULift.up m)
  simp only [ConcreteCategory.comp_apply] at h1 h2 h3 ⊢
  refine (congrArg (fun z => (additiveDirectImageComparisonGeneral.{u, v} π).hom.app
    (op (etaleSiteTerminal X)) z) h1).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => ((etaleAbelianDirectImage.{u, v} π).map
    (zmodSheafHom.{u, v} Y hY)).hom.app (op (etaleSiteTerminal X)) z) h2).symm
  refine Eq.trans ?_ h3.symm
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective m
  refine (congrArg (fun z => (additiveDirectImageComparisonGeneral.{u, v} π).hom.app
    (op (etaleSiteTerminal X)) z) (zmodPresheafHom_app.{u, v} X hX _ _)).trans ?_
  refine ((additiveDirectImageComparison_app_ofSection_general.{u, v} π _ _).trans ?_).trans
    (zmodPresheafHom_app.{u, v} Y hY _ _).symm
  refine congrArg (ofSection (U := (smallEtaleBaseChange π).obj (etaleSiteTerminal X))) ?_
  rw [constZModHom_intCast, constZModHom_intCast, map_intCast]
  rfl

section Cohomology

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Restriction on the étale cohomology of `𝐆_a`** along `π : Y ⟶ X`: restriction of a class to
the cohomology of `π⁻¹ 𝐆_{a,X}` followed by the comparison `π⁻¹ 𝐆_{a,X} ⟶ 𝐆_{a,Y}`. -/
def additiveCohomologyRestriction (q : ℕ) :
    Sheaf.H.{w} (additiveSheaf.{u, v} X) q →+ Sheaf.H.{w} (additiveSheaf.{u, v} Y) q :=
  (Sheaf.H.map (additiveInverseImageComparisonGeneral.{u, v} π) q).comp
    (etaleCohomologyRestrictionMap.{u, v, w} π (additiveSheaf.{u, v} X) q)

/-- Restriction on cohomology intertwines `φ : F ⟶ 𝐆_{a,X}` and `φ' : G ⟶ 𝐆_{a,Y}` along a map
`ψ : π⁻¹ F ⟶ G` which makes the comparison square commute. -/
private theorem additiveCohomologyRestriction_sheafH_map_aux
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ additiveSheaf.{u, v} X) (ψ : (etaleAbelianInverseImage.{u, v} π).obj F ⟶ G)
    (φ' : G ⟶ additiveSheaf.{u, v} Y)
    (h : (etaleAbelianInverseImage.{u, v} π).map φ ≫
        additiveInverseImageComparisonGeneral.{u, v} π = ψ ≫ φ') (q : ℕ) (y : Sheaf.H.{w} F q) :
    additiveCohomologyRestriction.{u, v, w} π q (Sheaf.H.map φ q y) =
      Sheaf.H.map φ' q (Sheaf.H.map ψ q (etaleCohomologyRestrictionMap.{u, v, w} π _ q y)) := by
  have key : etaleCohomologyRestrictionMap.{u, v, w} π _ q (Sheaf.H.map φ q y) =
      Sheaf.H.map ((etaleAbelianInverseImage.{u, v} π).map φ) q
        (etaleCohomologyRestrictionMap.{u, v, w} π _ q y) :=
    etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} π φ q y
  simp only [additiveCohomologyRestriction, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [key, ← Sheaf.H.map_comp_apply, h, Sheaf.H.map_comp_apply]

/-- Restriction on the cohomology of `𝐆_a` intertwines the maps induced by two endomorphisms
which the comparison intertwines. -/
theorem additiveCohomologyRestriction_sheafH_map {φX : additiveSheaf.{u, v} X ⟶ additiveSheaf X}
    {φY : additiveSheaf.{u, v} Y ⟶ additiveSheaf Y}
    (h : (etaleAbelianInverseImage.{u, v} π).map φX ≫
        additiveInverseImageComparisonGeneral.{u, v} π =
      additiveInverseImageComparisonGeneral.{u, v} π ≫ φY) (q : ℕ)
    (y : Sheaf.H.{w} (additiveSheaf.{u, v} X) q) :
    additiveCohomologyRestriction.{u, v, w} π q (Sheaf.H.map φX q y) =
      Sheaf.H.map φY q (additiveCohomologyRestriction.{u, v, w} π q y) :=
  additiveCohomologyRestriction_sheafH_map_aux π φX _ φY h q y

/-- **Restriction on the cohomology of `𝐆_a` commutes with the Frobenius.** -/
theorem additiveCohomologyRestriction_sheafH_map_frobeniusMap {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0) (q : ℕ)
    (y : Sheaf.H.{w} (additiveSheaf.{u, v} X) q) :
    additiveCohomologyRestriction.{u, v, w} π q (Sheaf.H.map (frobeniusMap.{u, v} X hp hX) q y) =
      Sheaf.H.map (frobeniusMap.{u, v} Y hp hY) q (additiveCohomologyRestriction.{u, v, w} π q y) :=
  additiveCohomologyRestriction_sheafH_map π
    (frobeniusMap_comp_additiveInverseImageComparison π hp hX hY) q y

/-- **Restriction on the cohomology of `𝐆_a` carries multiplication by `c` to multiplication by
`π^♯ c`.** -/
theorem additiveCohomologyRestriction_sheafH_map_scalarMap (c : Γ(X, ⊤)) (q : ℕ)
    (y : Sheaf.H.{w} (additiveSheaf.{u, v} X) q) :
    additiveCohomologyRestriction.{u, v, w} π q (Sheaf.H.map (scalarMap.{u, v} X c) q y) =
      Sheaf.H.map (scalarMap.{u, v} Y (π.appTop c)) q
        (additiveCohomologyRestriction.{u, v, w} π q y) :=
  additiveCohomologyRestriction_sheafH_map π (scalarMap_comp_additiveInverseImageComparison π c)
    q y

/-- **Restriction on cohomology is compatible with the inclusions of `𝐙/p𝐙` in `𝐆_a`**: the
restriction of the image of a class of `𝐙/p𝐙` is the image of its restriction, read in the
cohomology of `𝐙/p𝐙` on `Y` through the canonical comparison `π⁻¹ 𝐙/p𝐙 ≅ 𝐙/p𝐙`. -/
theorem additiveCohomologyRestriction_sheafH_map_zmodSheafHom {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (q : ℕ)
    (x : Sheaf.H.{w} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
      (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p)))) q) :
    additiveCohomologyRestriction.{u, v, w} π q (Sheaf.H.map (zmodSheafHom.{u, v} X hX) q x) =
      Sheaf.H.map (zmodSheafHom.{u, v} Y hY) q
        (Sheaf.H.map ((etaleAbelianInverseImageConstantIso.{u, v} π).hom.app
            (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p)))) q
          (etaleCohomologyRestrictionMap.{u, v, w} π _ q x)) :=
  additiveCohomologyRestriction_sheafH_map_aux π _ _ _
    (zmodSheafHom_comp_additiveInverseImageComparison π hX hY) q x

end Cohomology

end Stacks.ArtinSchreier

end
