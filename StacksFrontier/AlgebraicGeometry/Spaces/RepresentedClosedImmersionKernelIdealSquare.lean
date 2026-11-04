module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraPieceSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedImmersionKernelIdealNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit

/-!
# Naturality of the Zariski reading of the conormal module

# The map of kernel ideal sheaves of a commutative square, in degree one

For a commutative square `i_U ≫ φ = p ≫ i` of algebraic spaces, the map of kernel ideal sheaves
`φ^*𝓘_i ⟶ 𝓘_{i_U}` of `AlgebraicGeometry.Space.kernelIdealSheafZPowSquareMap` in degree one,
read through `𝓘¹ = 𝓘`, is compatible with the inclusions into the structure sheaves, and the
degree-one map of conormal algebras of the square is the square comparison `p^*i^* ≅ i_U^*φ^*`
followed by the inverse image of that map along `i_U`.

For a commutative square `j' ≫ b = a ≫ j` of test objects, the base change of the Zariski reading
along `a` after `j` is the base change along `j'` after `b` (from the cocycle law of the base
change of the Zariski reading), and the Zariski reading of the kernel ideal sheaf is compatible
with the map of kernel ideal sheaves of the square and the map of ideal sheaves of the scheme
square (Stacks 01R4).

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealSheafSquareMap`.

## Main results

* `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap_one`.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_square`.
* `AlgebraicGeometry.Space.zariskiReadingKernelIdealIso_square`.

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A composite `α ≪≫ eqToIso e ≪≫ β.symm` of natural isomorphisms, through a common target
`L` of `α` and `β`. -/
theorem CategoryTheory.Iso.trans_eqToIso_trans_symm_hom_app {C D : Type*} [Category C]
    [Category D] {F G H K L : C ⥤ D} (α : F ≅ G) (β : H ≅ K) (eG : G = L) (eK : K = L)
    (e : G = K) (M : C) :
    (α ≪≫ eqToIso e ≪≫ β.symm).hom.app M =
      (α ≪≫ eqToIso eG).hom.app M ≫ (β ≪≫ eqToIso eK).inv.app M := by
  subst eG
  subst eK
  simp

section Ideal

variable (B S hS) {U X Z ZU : AlgebraicSpaces B S hS}

/-- Naturality of the comparison of the two inverse images around a commutative square. -/
theorem modulePullbackSquareCompIso_hom_naturality (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i)
    {M M' : Modules.{u, u} B S hS X.1 X.2} (f : M ⟶ M') :
    (modulePullback B S hS p).map ((modulePullback B S hS i).map f) ≫
        (modulePullbackSquareCompIso B S hS p iU i φ hsq).hom.app M' =
      (modulePullbackSquareCompIso B S hS p iU i φ hsq).hom.app M ≫
        (modulePullback B S hS iU).map ((modulePullback B S hS φ).map f) :=
  (modulePullbackSquareCompIso B S hS p iU i φ hsq).hom.naturality f

/-- `AlgebraicGeometry.Space.modulePullbackCompIsoOfEq`, written out. -/
theorem modulePullbackCompIsoOfEq_hom (p : ZU ⟶ Z) (i : Z ⟶ X) (c : ZU ⟶ X) (h : p ≫ i = c) :
    (modulePullbackCompIsoOfEq B S hS p i h).hom =
      (modulePullbackCompIso B S hS p i).hom ≫ eqToHom (congrArg (modulePullback B S hS) h) := by
  rw [modulePullbackCompIsoOfEq]
  simp only [Iso.trans_hom, eqToIso.hom]

/-- `AlgebraicGeometry.Space.modulePullbackCompIsoOfEq`, written out. -/
theorem modulePullbackCompIsoOfEq_inv (p : ZU ⟶ Z) (i : Z ⟶ X) (c : ZU ⟶ X) (h : p ≫ i = c) :
    (modulePullbackCompIsoOfEq B S hS p i h).inv =
      eqToHom (congrArg (modulePullback B S hS) h).symm ≫ (modulePullbackCompIso B S hS p i).inv :=
          by
  rw [modulePullbackCompIsoOfEq]
  simp only [Iso.trans_inv, eqToIso.inv]

/-- The comparison of the two inverse images around a commutative square, through the
composition comparisons named along a common composite `c`. -/
theorem modulePullbackSquareCompIso_hom_eq (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) (c : ZU ⟶ X) (h₁ : p ≫ i = c) (h₂ : iU ≫ φ = c) :
    (modulePullbackSquareCompIso B S hS p iU i φ hsq).hom =
      (modulePullbackCompIsoOfEq B S hS p i h₁).hom ≫
        (modulePullbackCompIsoOfEq B S hS iU φ h₂).inv := by
  rw [modulePullbackSquareCompIso_hom, modulePullbackCompIsoOfEq_hom,
    modulePullbackCompIsoOfEq_inv]
  simp only [Category.assoc, eqToHom_trans_assoc]

/-- `AlgebraicGeometry.Space.modulePullbackSquareCompIso_hom_eq` at a module. -/
theorem modulePullbackSquareCompIso_hom_app_eq (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i)
    (c : ZU ⟶ X) (h₁ : p ≫ i = c) (h₂ : iU ≫ φ = c) (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackSquareCompIso B S hS p iU i φ hsq).hom.app M =
      (modulePullbackCompIsoOfEq B S hS p i h₁).hom.app M ≫
        (modulePullbackCompIsoOfEq B S hS iU φ h₂).inv.app M :=
  (congrArg (fun t => NatTrans.app t M)
    (modulePullbackSquareCompIso_hom_eq B S hS p iU i φ hsq c h₁ h₂)).trans
    (NatTrans.comp_app _ _ _)

/-- **The map of kernel ideal sheaves of a commutative square, in degree one**: the map
`φ^*𝓘_i ⟶ 𝓘_{i_U}` of `AlgebraicGeometry.Space.kernelIdealSheafZPowSquareMap` read through
`𝓘¹ = 𝓘`. -/
def kernelIdealSheafSquareMap (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    (modulePullback B S hS φ).obj (kernelIdealSheaf B S hS i).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS iU).toSheafOfModules :=
  (modulePullback B S hS φ).map (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS i).symm)) ≫
    kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq 1 ≫
        (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS iU)))

/-- `AlgebraicGeometry.Space.kernelIdealSheafSquareMap` is compatible with the inclusions into
the structure sheaves, through `φ^*𝒪 ≅ 𝒪`. -/
theorem kernelIdealSheafSquareMap_comp_ι (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    kernelIdealSheafSquareMap B S hS p iU i φ hsq ≫ (kernelIdealSheaf B S hS iU).ι =
      (modulePullback B S hS φ).map (kernelIdealSheaf B S hS i).ι ≫
        (modulePullbackUnitIso B S hS φ).hom := by
  have h1 := SheafOfModules.Submodule.eqToHom_toSheafOfModules_comp_ι
    (kernelIdealSheafZPow_one B S hS iU)
  have h2 := SheafOfModules.Submodule.eqToHom_toSheafOfModules_comp_ι
    (kernelIdealSheafZPow_one B S hS i).symm
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h1))).trans ?_
  refine (congrArg (_ ≫ ·)
    (kernelIdealSheafZPowSquareMap_comp_ι B S hS p iU i φ hsq 1)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (((modulePullback B S hS φ).map_comp _ _).symm.trans
    (congrArg (modulePullback B S hS φ).map h2))).trans ?_
  exact congrArg (_ ≫ ·) (structureModulePullbackMap_eq_modulePullbackUnitIso_hom B S hS φ)

/-- The inverse image of `AlgebraicGeometry.Space.kernelIdealSheafSquareMap` is the composite of
the inverse images of its three factors. -/
theorem modulePullback_map_kernelIdealSheafSquareMap (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    (modulePullback B S hS iU).map (kernelIdealSheafSquareMap B S hS p iU i φ hsq) =
      (modulePullback B S hS iU).map
          ((modulePullback B S hS φ).map
          (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS i).symm))) ≫
        (modulePullback B S hS iU).map (kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq 1) ≫
            (modulePullback B S hS iU).map
            (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS iU))) :=
  ((modulePullback B S hS iU).map_comp _ _).trans
    (congrArg (_ ≫ ·) ((modulePullback B S hS iU).map_comp _ _))

/-- The identification of the degree-one piece of the conormal algebra of `i` with `i^*𝓘` is the
inverse image along `i` of the identification of the first power of the kernel ideal sheaf of `i`
with that kernel ideal sheaf. -/
theorem eqToHom_conormalAlgebra_piece_one (i : Z ⟶ X) :
    eqToHom (conormalAlgebra_piece_one B S hS i) =
      (modulePullback B S hS i).map (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
        (kernelIdealSheafZPow_one B S hS i))) :=
  (eqToHom_map _ _).symm

/-- The inverse of the identification in `eqToHom_conormalAlgebra_piece_one` is the inverse image
along `i` of the identification of the kernel ideal sheaf with its first power. -/
theorem eqToHom_conormalAlgebra_piece_one_symm (i : Z ⟶ X) :
    eqToHom (conormalAlgebra_piece_one B S hS i).symm =
      (modulePullback B S hS i).map (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
        (kernelIdealSheafZPow_one B S hS i).symm)) :=
  (eqToHom_map _ _).symm

private theorem pieceSquareMap_one_step₁ (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    (modulePullback B S hS p).map (eqToHom (conormalAlgebra_piece_one B S hS i).symm) ≫
        conormalAlgebraPieceSquareMap B S hS p iU i φ hsq 1 ≫
            eqToHom (conormalAlgebra_piece_one B S hS iU) =
      (modulePullback B S hS p).map
          ((modulePullback B S hS i).map
          (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS i).symm))) ≫
              conormalAlgebraPieceSquareMap B S hS p iU i φ hsq 1 ≫
              eqToHom (conormalAlgebra_piece_one B S hS iU) :=
  congrArg (fun k => (modulePullback B S hS p).map k ≫
      conormalAlgebraPieceSquareMap B S hS p iU i φ hsq 1 ≫
      eqToHom (conormalAlgebra_piece_one B S hS iU))
    (eqToHom_conormalAlgebra_piece_one_symm B S hS i)

private theorem pieceSquareMap_one_step₂ (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    (modulePullback B S hS p).map
        ((modulePullback B S hS i).map (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS i).symm))) ≫
              conormalAlgebraPieceSquareMap B S hS p iU i φ hsq 1 ≫
              eqToHom (conormalAlgebra_piece_one B S hS iU) =
              (modulePullback B S hS p).map
              ((modulePullback B S hS i).map
              (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS i).symm))) ≫
              conormalAlgebraPieceSquareMap B S hS p iU i φ hsq 1 ≫
              (modulePullback B S hS iU).map
              (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS iU))) :=
  congrArg (fun k => (modulePullback B S hS p).map
      ((modulePullback B S hS i).map (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS i).symm))) ≫
              conormalAlgebraPieceSquareMap B S hS p iU i φ hsq 1 ≫ k)
              (eqToHom_conormalAlgebra_piece_one B S hS iU)

private theorem pieceSquareMap_one_step₃ (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    (modulePullback B S hS p).map
        ((modulePullback B S hS i).map (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS i).symm))) ≫
              conormalAlgebraPieceSquareMap B S hS p iU i φ hsq 1 ≫
              (modulePullback B S hS iU).map
              (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS iU))) =
              (modulePullback B S hS p).map
              ((modulePullback B S hS i).map
              (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS i).symm))) ≫
              ((modulePullbackSquareCompIso B S hS p iU i φ hsq).hom.app
          (kernelIdealSheafZPow B S hS i 1).toSheafOfModules ≫
        (modulePullback B S hS iU).map (kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq 1)) ≫
            (modulePullback B S hS iU).map
            (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS iU))) :=
  rfl

private theorem pieceSquareMap_one_step₄ (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    (modulePullback B S hS p).map
        ((modulePullback B S hS i).map (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS i).symm))) ≫
              ((modulePullbackSquareCompIso B S hS p iU i φ hsq).hom.app
          (kernelIdealSheafZPow B S hS i 1).toSheafOfModules ≫
        (modulePullback B S hS iU).map (kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq 1)) ≫
            (modulePullback B S hS iU).map
            (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS iU))) =
      (modulePullbackSquareCompIso B S hS p iU i φ hsq).hom.app
          (kernelIdealSheaf B S hS i).toSheafOfModules ≫
              (modulePullback B S hS iU).map (kernelIdealSheafSquareMap B S hS p iU i φ hsq) := by
  have hN := modulePullbackSquareCompIso_hom_naturality B S hS p iU i φ hsq
    (M := (kernelIdealSheaf B S hS i).toSheafOfModules)
    (M' := (kernelIdealSheafZPow B S hS i 1).toSheafOfModules)
        (eqToHom (congrArg SheafOfModules.Submodule.toSheafOfModules
          (kernelIdealSheafZPow_one B S hS i).symm))
  refine Eq.trans ?_ (congrArg (_ ≫ ·)
    (modulePullback_map_kernelIdealSheafSquareMap B S hS p iU i φ hsq).symm)
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hN).trans ?_
  exact Category.assoc _ _ _

/-- **The degree-one map of conormal algebras of a commutative square, through `𝒞_1 = i^*𝓘`**:
the square comparison followed by the inverse image along `i_U` of the map of kernel ideal
sheaves `φ^*𝓘_i ⟶ 𝓘_{i_U}`. -/
theorem conormalAlgebraPieceSquareMap_one (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    (modulePullback B S hS p).map (eqToHom (conormalAlgebra_piece_one B S hS i).symm) ≫
        conormalAlgebraPieceSquareMap B S hS p iU i φ hsq 1 ≫
            eqToHom (conormalAlgebra_piece_one B S hS iU) =
      (modulePullbackSquareCompIso B S hS p iU i φ hsq).hom.app
          (kernelIdealSheaf B S hS i).toSheafOfModules ≫
              (modulePullback B S hS iU).map (kernelIdealSheafSquareMap B S hS p iU i φ hsq) :=
  (pieceSquareMap_one_step₁ B S hS p iU i φ hsq).trans
    ((pieceSquareMap_one_step₂ B S hS p iU i φ hsq).trans
      ((pieceSquareMap_one_step₃ B S hS p iU i φ hsq).trans
        (pieceSquareMap_one_step₄ B S hS p iU i φ hsq)))

/-- `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap_one`, with the identification
`𝒞_1 = i^*𝓘` moved to the right. -/
theorem conormalAlgebraPieceSquareMap_one_comp_eqToHom (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    conormalAlgebraPieceSquareMap B S hS p iU i φ hsq 1 ≫
        eqToHom (conormalAlgebra_piece_one B S hS iU) =
      (modulePullback B S hS p).map (eqToHom (conormalAlgebra_piece_one B S hS i)) ≫
          (modulePullbackSquareCompIso B S hS p iU i φ hsq).hom.app
          (kernelIdealSheaf B S hS i).toSheafOfModules ≫
        (modulePullback B S hS iU).map (kernelIdealSheafSquareMap B S hS p iU i φ hsq) := by
  have hc : (modulePullback B S hS p).map (eqToHom (conormalAlgebra_piece_one B S hS i)) ≫
      (modulePullback B S hS p).map (eqToHom (conormalAlgebra_piece_one B S hS i).symm) = 𝟙 _ :=
    ((modulePullback B S hS p).map_comp _ _).symm.trans
      ((congrArg (modulePullback B S hS p).map (eqToHom_trans _ _)).trans
        ((congrArg (modulePullback B S hS p).map (eqToHom_refl _ _)).trans
          ((modulePullback B S hS p).map_id _)))
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (conormalAlgebraPieceSquareMap_one B S hS p iU i φ hsq))
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hc.symm))

end Ideal

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

section Square

variable {Z T Z' T' : BigFppfOver B S hS} (j : Z ⟶ T) (j' : Z' ⟶ T') (a : Z' ⟶ Z) (b : T' ⟶ T)

/-- **The base change of the Zariski reading around a commutative square** `j' ≫ b = a ≫ j` of
test objects: along `a` after `j` it is the base change along `j'` after `b`, through the
comparison of the two inverse images around the square on both sides. -/
theorem zariskiReadingPullbackHom_square (w : j' ≫ b = a ≫ j)
    (hsq : (representedSpaceMap B S hS j') ≫ (representedSpaceMap B S hS b) =
        (representedSpaceMap B S hS a) ≫ (representedSpaceMap B S hS j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackHom j).app N) ≫
        (zariskiReadingPullbackHom a).app
            ((modulePullback B S hS (representedSpaceMap B S hS j)).obj N) ≫
        (zariskiReadingFunctor Z').map
            ((modulePullbackSquareCompIso B S hS (representedSpaceMap B S hS a)
            (representedSpaceMap B S hS j') (representedSpaceMap B S hS j)
            (representedSpaceMap B S hS b) hsq).hom.app N) =
      (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          ((zariskiReadingFunctor T).obj N)).hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
            ((zariskiReadingPullbackHom b).app N) ≫
        (zariskiReadingPullbackHom j').app
            ((modulePullback B S hS (representedSpaceMap B S hS b)).obj N) := by
  have c1 := zariskiReadingPullbackHom_comp_of_eq a j (a ≫ j) rfl N
  have c2 := zariskiReadingPullbackHom_comp_of_eq j' b (a ≫ j) w N
  have hL := modulePullbackSquareCompIso_hom_app_eq B S hS (representedSpaceMap B S hS a)
      (representedSpaceMap B S hS j') (representedSpaceMap B S hS j)
    (representedSpaceMap B S hS b) hsq (representedSpaceMap B S hS (a ≫ j))
        (representedSpaceMap_comp_of_eq a j (a ≫ j) rfl)
    (representedSpaceMap_comp_of_eq j' b (a ≫ j) w) N
  have hC := schemePullbackCompOfEq_hom_app_comp_inv_app ((BigFppfOver.toScheme B S hS).map j')
      ((BigFppfOver.toScheme B S hS).map b) ((BigFppfOver.toScheme B S hS).map a)
    ((BigFppfOver.toScheme B S hS).map j) ((BigFppfOver.toScheme B S hS).map (a ≫ j))
        (toScheme_map_comp_of_eq a j (a ≫ j) rfl)
    (toScheme_map_comp_of_eq j' b (a ≫ j) w) ((zariskiReadingFunctor T).obj N)
  have c1' :=
      (Iso.inv_comp_eq
      ((schemePullbackCompOfEq ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map j) ((BigFppfOver.toScheme B S hS).map (a ≫ j))
    (toScheme_map_comp_of_eq a j (a ≫ j) rfl)).app ((zariskiReadingFunctor T).obj N))).1 c1
  have c2' := (Iso.comp_inv_eq ((zariskiReadingFunctor Z').mapIso ((modulePullbackCompIsoOfEq
    B S hS (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
        (representedSpaceMap_comp_of_eq j' b (a ≫ j) w)).app
      N))).2 (c2.symm.trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans
        (Category.assoc _ _ _).symm))
  refine (congrArg (fun k => _ ≫ _ ≫ (zariskiReadingFunctor Z').map k) hL).trans ?_
  refine (congrArg (fun k => _ ≫ _ ≫ k) ((zariskiReadingFunctor Z').map_comp _ _)).trans ?_
  refine (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) c1').trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) c2').trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) hC

end Square

section Conormal

variable {Z T Z' T' : BigFppfOver B S hS} (j : Z ⟶ T) (j' : Z' ⟶ T') (a : Z' ⟶ Z) (b : T' ⟶ T)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')]

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
  [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')] in
/-- The square of `AlgebraicGeometry.Space.zariskiReadingKernelIdealIso_naturality_left` for the
map of kernel ideal sheaves of an arbitrary commutative square. -/
theorem zariskiReadingKernelIdealIso_square_left
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    (zariskiReadingPullbackHom b).app (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        ≫ (zariskiReadingFunctor T').map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq) ≫ (zariskiReadingKernelIdealIso j').hom ≫
        Stacks.ClosedImmersion.idealSheafι ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map b)).map
          ((zariskiReadingFunctor T).map (kernelIdealSheaf B S hS (yonedaSpaceMap j)).ι) ≫
        (Stacks.RingedSpace.pullbackFunctor
            (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
          (zariskiReadingUnitHomIso T).inv ≫
        RingedSpaceModuleAdjunction.modulePullbackUnitToUnit
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b)) := by
  have hK' := zariskiReadingKernelIdealIso_hom_comp_ι j'
  have hBR := kernelIdealSheafSquareMap_comp_ι B S hS
    (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j) (yonedaSpaceMap b) hsq
  have hN := zariskiReadingPullbackHom_naturality_yonedaSpaceMap b
    (kernelIdealSheaf B S hS (yonedaSpaceMap j)).ι
  have hU := zariskiReadingPullbackHom_app_unit_comp_inv_yonedaSpaceMap b
  have e : (zariskiReadingFunctor T').map
      (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
      (yonedaSpaceMap b) hsq) ≫ zariskiReadingKernelIdealι j' =
      (zariskiReadingFunctor T').map ((modulePullback B S hS (yonedaSpaceMap b)).map
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).ι) ≫
        (zariskiReadingFunctor T').map (modulePullbackUnitIso B S hS (yonedaSpaceMap b)).hom ≫
        (zariskiReadingUnitHomIso T').inv := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine congrArg (· ≫ _) ?_
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _ hBR)).trans (Functor.map_comp _ _ _)
  refine (congrArg
      (fun k => (zariskiReadingPullbackHom b).app
      (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≫ _ ≫ k) hK').trans ?_
  refine (congrArg
      ((zariskiReadingPullbackHom b).app
      (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≫ ·) e).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hN.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) hU

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
  [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')] in
/-- **Naturality of `R_T 𝓘 ≅ 𝓘_j` along an arbitrary commutative square** `j' ≫ b = a ≫ j` of
test objects: the base change of the Zariski reading of the kernel ideal sheaf, the map of kernel
ideal sheaves of the square and the reading at `j'` give the reading at `j` pulled back along `b`
followed by the map of ideal sheaves of the scheme square. -/
theorem zariskiReadingKernelIdealIso_square
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (zariskiReadingPullbackHom b).app (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        ≫ (zariskiReadingFunctor T').map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq) ≫ (zariskiReadingKernelIdealIso j').hom =
        (Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
        ((zariskiReadingKernelIdealIso j).hom) ≫
        (Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm)) := by
  have : Mono (Stacks.ClosedImmersion.idealSheafι
      ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) :=
    inferInstanceAs (Mono (kernel.ι _))
  refine Mono.right_cancellation (f := Stacks.ClosedImmersion.idealSheafι
    ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom) _ _ ?_
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans ?_
  refine (zariskiReadingKernelIdealIso_square_left j j' a b hsq).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (zariskiReadingKernelIdealIso_naturality_right j j' a b comm).symm
  exact congrArg (· ≫ _) (scheme_modules_pullback_map_eq_pullbackFunctor_map _ _)

end Conormal

end AlgebraicGeometry.Space

end
