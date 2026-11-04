module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedImmersionKernelIdealSquare

/-!
# Naturality of the Zariski reading of the conormal module

# Naturality of the Zariski reading of the conormal module

Let `j' ≫ b = a ≫ j` be a commutative square of test objects whose scheme morphisms `j`, `j'` are
closed immersions.  The Zariski reading of the degree-one piece of the conormal algebra of `j` is
the conormal sheaf of `j` (`AlgebraicGeometry.Space.zariskiReadingConormalIso`).  This file proves
that these identifications carry the degree-one map of conormal algebras of the square of
represented algebraic spaces (`AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap`) to the
base-change map of conormal sheaves of the scheme square (Stacks 01R4), through the base change
of the Zariski reading.  At a cartesian square with `b` étale the map of conormal algebras is the
isomorphism of Stacks 09RR.

## Main results

* `AlgebraicGeometry.Space.zariskiReadingConormalIso_naturality_of_comm`: any commutative square.
* `AlgebraicGeometry.Space.zariskiReadingConormalIso_naturality`: étale cartesian squares.

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

section Conormal

variable {Z T Z' T' : BigFppfOver B S hS} (j : Z ⟶ T) (j' : Z' ⟶ T') (a : Z' ⟶ Z) (b : T' ⟶ T)

/-- The composition comparison of Stacks 03LU at two morphisms of represented algebraic spaces,
in the two spellings of the morphisms. -/
theorem modulePullbackCompIso_hom_yonedaSpaceMap {T₁ T₂ T₃ : BigFppfOver B S hS}
    (g : T₃ ⟶ T₂) (f : T₂ ⟶ T₁) :
    (modulePullbackCompIso B S hS (yonedaSpaceMap g) (yonedaSpaceMap f)).hom =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS g)
        (representedSpaceMap B S hS f)).hom :=
  rfl

/-- The composition comparison of Stacks 03LU at two morphisms of represented algebraic spaces,
in the two spellings of the morphisms. -/
theorem modulePullbackCompIso_inv_yonedaSpaceMap {T₁ T₂ T₃ : BigFppfOver B S hS}
    (g : T₃ ⟶ T₂) (f : T₂ ⟶ T₁) :
    (modulePullbackCompIso B S hS (yonedaSpaceMap g) (yonedaSpaceMap f)).inv =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS g)
        (representedSpaceMap B S hS f)).inv :=
  rfl

/-- The transport between the inverse images along the two composites of a commutative square,
in the two spellings of the morphisms of represented algebraic spaces. -/
theorem eqToHom_congrArg_modulePullback_yonedaSpaceMap
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (hsq' : (representedSpaceMap B S hS j') ≫ (representedSpaceMap B S hS b) =
    (representedSpaceMap B S hS a) ≫ (representedSpaceMap B S hS j)) :
    eqToHom (congrArg (fun k => modulePullback B S hS k) hsq.symm) =
      eqToHom (congrArg (fun k => modulePullback B S hS k) hsq'.symm) :=
  rfl

/-- The comparison `p^*i^* ≅ i_U^*φ^*` around the square of represented algebraic spaces, in the
two spellings of their morphisms. -/
theorem modulePullbackSquareCompIso_hom_yonedaSpaceMap
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (hsq' : (representedSpaceMap B S hS j') ≫ (representedSpaceMap B S hS b) =
    (representedSpaceMap B S hS a) ≫ (representedSpaceMap B S hS j)) :
    (modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
    (yonedaSpaceMap b) hsq).hom =
    (modulePullbackSquareCompIso B S hS (representedSpaceMap B S hS a)
    (representedSpaceMap B S hS j') (representedSpaceMap B S hS j) (representedSpaceMap B S hS b)
    hsq').hom :=
  (modulePullbackSquareCompIso_hom B S hS _ _ _ _ hsq).trans
    ((congrArg (· ≫ _) (modulePullbackCompIso_hom_yonedaSpaceMap a j)).trans
    ((congrArg (fun k => _ ≫ k ≫ _)
        (eqToHom_congrArg_modulePullback_yonedaSpaceMap j j' a b hsq hsq')).trans
      ((congrArg (fun k => _ ≫ _ ≫ k) (modulePullbackCompIso_inv_yonedaSpaceMap j' b)).trans
        (modulePullbackSquareCompIso_hom B S hS _ _ _ _ hsq').symm)))

/-- `AlgebraicGeometry.Space.modulePullbackSquareCompIso_hom_yonedaSpaceMap`, read on `Z'`. -/
theorem zariskiReadingFunctor_map_squareCompIso_yonedaSpaceMap
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (hsq' : (representedSpaceMap B S hS j') ≫ (representedSpaceMap B S hS b) =
    (representedSpaceMap B S hS a) ≫ (representedSpaceMap B S hS j))
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    (zariskiReadingFunctor Z').map
        ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app N) =
        (zariskiReadingFunctor Z').map
        ((modulePullbackSquareCompIso B S hS (representedSpaceMap B S hS a)
        (representedSpaceMap B S hS j') (representedSpaceMap B S hS j)
        (representedSpaceMap B S hS b) hsq').hom.app N) :=
  congrArg (fun t => (zariskiReadingFunctor Z').map (NatTrans.app t N))
    (modulePullbackSquareCompIso_hom_yonedaSpaceMap j j' a b hsq hsq')

/-- The base change of the Zariski reading at an inverse image, in the two spellings of the
morphism of represented algebraic spaces. -/
theorem zariskiReadingPullbackHom_app_modulePullback_yonedaSpaceMap {T₁ T₂ T₃ : BigFppfOver B S hS}
    (f : T₂ ⟶ T₁) (g : T₃ ⟶ T₂)
    (N : Modules.{u, u} B S hS (yoneda.obj T₁) (isAlgebraicSpace_yoneda B S hS T₁)) :
    (zariskiReadingPullbackHom g).app ((modulePullback B S hS (yonedaSpaceMap f)).obj N) =
      (zariskiReadingPullbackHom g).app
        ((modulePullback B S hS (representedSpaceMap B S hS f)).obj N) := by
  with_reducible rfl

/-- `AlgebraicGeometry.Space.zariskiReadingPullbackHom_square`, with the morphisms of represented
algebraic spaces spelled along `AlgebraicGeometry.Space.yonedaSpaceMap`. -/
theorem zariskiReadingPullbackHom_square_yonedaSpaceMap (w : j' ≫ b = a ≫ j)
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (hsq' : (representedSpaceMap B S hS j') ≫ (representedSpaceMap B S hS b) =
    (representedSpaceMap B S hS a) ≫ (representedSpaceMap B S hS j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackHom j).app N) ≫
        (zariskiReadingPullbackHom a).app ((modulePullback B S hS (yonedaSpaceMap j)).obj N) ≫
        (zariskiReadingFunctor Z').map
            ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
            (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app N) =
      (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          ((zariskiReadingFunctor T).obj N)).hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
            ((zariskiReadingPullbackHom b).app N) ≫
        (zariskiReadingPullbackHom j').app ((modulePullback B S hS (yonedaSpaceMap b)).obj N) :=
  (congrArg (fun k => _ ≫ k ≫ _)
      (zariskiReadingPullbackHom_app_modulePullback_yonedaSpaceMap j a N)).trans
    ((congrArg (fun k => _ ≫ _ ≫ k)
        (zariskiReadingFunctor_map_squareCompIso_yonedaSpaceMap j j' a b hsq hsq' N)).trans
      ((zariskiReadingPullbackHom_square j j' a b w hsq' comm N).trans
        (congrArg (fun k => _ ≫ _ ≫ k)
            (zariskiReadingPullbackHom_app_modulePullback_yonedaSpaceMap b j' N).symm)))

/-- `AlgebraicGeometry.Space.conormalAlgebraPieceOneIso` is the transport along
`AlgebraicGeometry.Space.conormalAlgebra_piece_one`. -/
theorem conormalAlgebraPieceOneIso_hom {Z₀ T₀ : BigFppfOver B S hS} (i : Z₀ ⟶ T₀) :
    (conormalAlgebraPieceOneIso i).hom =
        eqToHom (conormalAlgebra_piece_one B S hS (yonedaSpaceMap i)) :=
  rfl

private theorem pieceOneIso_step₁
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq 1 ≫ (conormalAlgebraPieceOneIso j').hom =
      conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1 ≫
          eqToHom (conormalAlgebra_piece_one B S hS (yonedaSpaceMap j')) :=
  congrArg (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
      (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1 ≫ ·) (conormalAlgebraPieceOneIso_hom j')

private theorem pieceOneIso_step₂
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq 1 ≫ eqToHom (conormalAlgebra_piece_one B S hS (yonedaSpaceMap j')) =
      (modulePullback B S hS (yonedaSpaceMap a)).map
          (eqToHom (conormalAlgebra_piece_one B S hS (yonedaSpaceMap j))) ≫
        (modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
            (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
            (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≫
            (modulePullback B S hS (yonedaSpaceMap j')).map
            (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
            (yonedaSpaceMap j) (yonedaSpaceMap b) hsq) :=
  conormalAlgebraPieceSquareMap_one_comp_eqToHom B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
      (yonedaSpaceMap j) (yonedaSpaceMap b) hsq

private theorem pieceOneIso_step₃ :
    (modulePullback B S hS (yonedaSpaceMap a)).map
        (eqToHom (conormalAlgebra_piece_one B S hS (yonedaSpaceMap j))) =
      (modulePullback B S hS (yonedaSpaceMap a)).map (conormalAlgebraPieceOneIso j).hom :=
  congrArg (modulePullback B S hS (yonedaSpaceMap a)).map (conormalAlgebraPieceOneIso_hom j).symm

private theorem pieceOneIso_step₄
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    (modulePullback B S hS (yonedaSpaceMap a)).map
        (eqToHom (conormalAlgebra_piece_one B S hS (yonedaSpaceMap j))) ≫
        (modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
            (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
            (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≫
            (modulePullback B S hS (yonedaSpaceMap j')).map
            (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
            (yonedaSpaceMap j) (yonedaSpaceMap b) hsq) =
      (modulePullback B S hS (yonedaSpaceMap a)).map (conormalAlgebraPieceOneIso j).hom ≫
        (modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
            (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
            (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≫
            (modulePullback B S hS (yonedaSpaceMap j')).map
            (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
            (yonedaSpaceMap j) (yonedaSpaceMap b) hsq) :=
  congrArg (· ≫
      (modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
      (yonedaSpaceMap b) hsq).hom.app (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
      ≫ (modulePullback B S hS (yonedaSpaceMap j')).map
      (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
      (yonedaSpaceMap b) hsq))
    (pieceOneIso_step₃ j a)

/-- `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap_one_comp_eqToHom` at test objects,
through `AlgebraicGeometry.Space.conormalAlgebraPieceOneIso`. -/
theorem conormalAlgebraPieceSquareMap_one_comp_pieceOneIso
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq 1 ≫ (conormalAlgebraPieceOneIso j').hom =
      (modulePullback B S hS (yonedaSpaceMap a)).map (conormalAlgebraPieceOneIso j).hom ≫
        (modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
            (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
            (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≫
            (modulePullback B S hS (yonedaSpaceMap j')).map
            (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
            (yonedaSpaceMap j) (yonedaSpaceMap b) hsq) :=
  (pieceOneIso_step₁ j j' a b hsq).trans ((pieceOneIso_step₂ j j' a b hsq).trans
    (pieceOneIso_step₄ j j' a b hsq))

variable [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
  [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')]

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] in
private theorem conormalSquare_step0
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    (zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
        (zariskiReadingFunctor Z').map
        (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1) ≫
        (zariskiReadingFunctor Z').map (conormalAlgebraPieceOneIso j').hom ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) =
      (zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
          ((zariskiReadingFunctor Z').map
          ((modulePullback B S hS (yonedaSpaceMap a)).map (conormalAlgebraPieceOneIso j).hom) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullback B S hS (yonedaSpaceMap j')).map
          (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq))) ≫
          (zariskiReadingPullbackIso j'
          (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingKernelIdealIso j').hom) := by
  have hA : (zariskiReadingFunctor Z').map
      (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
      (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1) ≫
      (zariskiReadingFunctor Z').map (conormalAlgebraPieceOneIso j').hom =
      (zariskiReadingFunctor Z').map
      ((modulePullback B S hS (yonedaSpaceMap a)).map (conormalAlgebraPieceOneIso j).hom) ≫
      (zariskiReadingFunctor Z').map
      ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
      (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
      (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
      (zariskiReadingFunctor Z').map
      ((modulePullback B S hS (yonedaSpaceMap j')).map
      (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
      (yonedaSpaceMap b) hsq)) :=
    ((zariskiReadingFunctor Z').map_comp _ _).symm.trans ((congrArg (zariskiReadingFunctor Z').map
      (conormalAlgebraPieceSquareMap_one_comp_pieceOneIso j j' a b hsq)).trans
          (((zariskiReadingFunctor Z').map_comp _ _).trans
          (congrArg (_ ≫ ·) ((zariskiReadingFunctor Z').map_comp _ _))))
  exact congrArg
      ((zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫ ·)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hA))

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] in
private theorem conormalSquare_step1
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    (zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
        ((zariskiReadingFunctor Z').map
        ((modulePullback B S hS (yonedaSpaceMap a)).map (conormalAlgebraPieceOneIso j).hom) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullback B S hS (yonedaSpaceMap j')).map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq))) ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) =
      ((zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullback B S hS (yonedaSpaceMap a)).map (conormalAlgebraPieceOneIso j).hom)) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullback B S hS (yonedaSpaceMap j')).map
          (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq)) ≫
          (zariskiReadingPullbackIso j'
          (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingKernelIdealIso j').hom) := by
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)))).trans ?_
  exact (Category.assoc _ _ _).symm

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] in
private theorem conormalSquare_step2
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    ((zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullback B S hS (yonedaSpaceMap a)).map (conormalAlgebraPieceOneIso j).hom)) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullback B S hS (yonedaSpaceMap j')).map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq)) ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) =
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (zariskiReadingPullbackHom a).app
          ((modulePullback B S hS (yonedaSpaceMap j)).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullback B S hS (yonedaSpaceMap j')).map
          (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq)) ≫
          (zariskiReadingPullbackIso j'
          (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingKernelIdealIso j').hom) := by
  have hn := zariskiReadingPullbackHom_naturality_yonedaSpaceMap a
    (conormalAlgebraPieceOneIso j).hom
  exact congrArg (· ≫ _) hn.symm

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] in
private theorem conormalSquare_step3
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (zariskiReadingPullbackHom a).app
        ((modulePullback B S hS (yonedaSpaceMap j)).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullback B S hS (yonedaSpaceMap j')).map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq)) ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          ((zariskiReadingPullbackHom a).app
          ((modulePullback B S hS (yonedaSpaceMap j)).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullback B S hS (yonedaSpaceMap j')).map
          (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq)) ≫
          (zariskiReadingPullbackIso j'
          (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingKernelIdealIso j').hom) := by
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _).symm

private theorem conormalSquare_step4
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        ((zariskiReadingPullbackHom a).app
        ((modulePullback B S hS (yonedaSpaceMap j)).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullback B S hS (yonedaSpaceMap j')).map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq)) ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          ((zariskiReadingFunctor T).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingPullbackHom b).app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
          (zariskiReadingPullbackHom j').app
          ((modulePullback B S hS (yonedaSpaceMap b)).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullback B S hS (yonedaSpaceMap j')).map
          (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq)) ≫
          (zariskiReadingPullbackIso j'
          (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingKernelIdealIso j').hom) := by
  have hM := zariskiReadingPullbackHom_square_yonedaSpaceMap j j' a b
    (yoneda.map_injective (congrArg (fun f => f.hom) hsq)) hsq hsq comm
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
  have hz : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
      ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
      (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
      ((zariskiReadingPullbackHom j).app
      (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) = 𝟙 _ :=
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        (zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
            (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv_hom_id).trans
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map_id _))
  have h5 : (zariskiReadingPullbackHom a).app
      ((modulePullback B S hS (yonedaSpaceMap j)).obj
      (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
      (zariskiReadingFunctor Z').map
      ((modulePullbackSquareCompIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
      (yonedaSpaceMap j) (yonedaSpaceMap b) hsq).hom.app
      (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
      ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
      (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
      (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
      ((zariskiReadingFunctor T).obj
      (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
      ((zariskiReadingPullbackHom b).app
      (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
      (zariskiReadingPullbackHom j').app
      ((modulePullback B S hS (yonedaSpaceMap b)).obj
      (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) :=
    ((Category.id_comp _).symm.trans (congrArg (· ≫ _) hz.symm)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hM))
  exact congrArg (fun k => _ ≫ k ≫ _) h5

private theorem conormalSquare_step5
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        ((zariskiReadingFunctor T).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingPullbackHom b).app
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
        (zariskiReadingPullbackHom j').app
        ((modulePullback B S hS (yonedaSpaceMap b)).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullback B S hS (yonedaSpaceMap j')).map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq)) ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          ((zariskiReadingFunctor T).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingPullbackHom b).app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
          ((zariskiReadingPullbackHom j').app
          ((modulePullback B S hS (yonedaSpaceMap b)).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
          (zariskiReadingFunctor Z').map
          ((modulePullback B S hS (yonedaSpaceMap j')).map
          (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq))) ≫
          (zariskiReadingPullbackIso j'
          (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingKernelIdealIso j').hom) := by
  refine congrArg (_ ≫ ·) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans ?_)
  refine congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans ?_)
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)

private theorem conormalSquare_step6
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        ((zariskiReadingFunctor T).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingPullbackHom b).app
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
        ((zariskiReadingPullbackHom j').app
        ((modulePullback B S hS (yonedaSpaceMap b)).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
        (zariskiReadingFunctor Z').map
        ((modulePullback B S hS (yonedaSpaceMap j')).map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq))) ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          ((zariskiReadingFunctor T).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingPullbackHom b).app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingFunctor T').map
          (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq)) ≫
          (zariskiReadingPullbackHom j').app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules) ≫
          (zariskiReadingPullbackIso j'
          (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingKernelIdealIso j').hom) := by
  have hn := zariskiReadingPullbackHom_naturality_yonedaSpaceMap j'
      (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
      (yonedaSpaceMap b) hsq)
  exact congrArg (fun k => _ ≫ _ ≫ _ ≫ _ ≫ k ≫ _) hn.symm

private theorem conormalSquare_step7
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        ((zariskiReadingFunctor T).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingPullbackHom b).app
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingFunctor T').map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq)) ≫
        (zariskiReadingPullbackHom j').app
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules) ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          ((zariskiReadingFunctor T).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingPullbackHom b).app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingFunctor T').map
          (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq)) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingKernelIdealIso j').hom) := by
  have hz : (zariskiReadingPullbackHom j').app
      (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules ≫
      (zariskiReadingPullbackIso j' (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
      (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
      ((zariskiReadingKernelIdealIso j').hom) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
      ((zariskiReadingKernelIdealIso j').hom) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (zariskiReadingPullbackIso j' (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).hom_inv_id).trans
          (Category.id_comp _))
  exact congrArg (fun k => _ ≫ _ ≫ _ ≫ _ ≫ k) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) hz))

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')] in
private theorem conormalSquare_step8
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        ((zariskiReadingFunctor T).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingPullbackHom b).app
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingFunctor T').map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq)) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          ((zariskiReadingFunctor T).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
          (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
          ((zariskiReadingPullbackHom b).app
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≫
          (zariskiReadingFunctor T').map
          (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq) ≫ (zariskiReadingKernelIdealIso j').hom) := by
  refine congrArg (fun k => _ ≫ _ ≫ _ ≫ k) ?_
  exact (congrArg (_ ≫ ·)
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map_comp _ _).symm).trans
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map_comp _ _).symm

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')] in
private theorem conormalSquare_step9
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        ((zariskiReadingFunctor T).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
        (Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
        ((zariskiReadingPullbackHom b).app
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules ≫
        (zariskiReadingFunctor T').map
        (kernelIdealSheafSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j)
        (yonedaSpaceMap b) hsq) ≫ (zariskiReadingKernelIdealIso j').hom) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          ((zariskiReadingFunctor T).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
          (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
          ((zariskiReadingKernelIdealIso j).hom) ≫
          (Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) :=
  congrArg
    (fun k => _ ≫ _ ≫ _ ≫
      (Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map k)
    (zariskiReadingKernelIdealIso_square j j' a b hsq comm)

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')] in
private theorem conormalSquare_step10
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        ((zariskiReadingFunctor T).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
        (Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
        ((Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
        ((zariskiReadingKernelIdealIso j).hom) ≫
        (Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          ((Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          ((zariskiReadingFunctor T).obj
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
          (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
          ((zariskiReadingKernelIdealIso j).hom))) ≫
          (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
          ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) := by
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  exact (congrArg (_ ≫ ·)
      ((Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map_comp _ _)).trans
    (Category.assoc _ _ _).symm

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j')] in
private theorem conormalSquare_step11
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        ((Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        ((zariskiReadingFunctor T).obj
        (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules)).hom ≫
        (Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
        ((Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map b))).map
        ((zariskiReadingKernelIdealIso j).hom))) ≫
        (Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
        ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map a))).map
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j))).map
          ((zariskiReadingKernelIdealIso j).hom)) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom) ≫
          (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
          ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) :=
  congrArg (fun k => _ ≫ _ ≫ k ≫ _)
    (Stacks.ClosedImmersion.pullbackCompIso_naturality (Stacks.Conormal.comm_toShHom comm)
      (zariskiReadingKernelIdealIso j).hom).symm

/-- The core of the naturality of the Zariski reading of the conormal module, before the
identifications of the conormal sheaves with the pullbacks of the ideal sheaves. -/
theorem zariskiReadingConormalIso_square_core
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
        (zariskiReadingFunctor Z').map
        (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1) ≫
        (zariskiReadingFunctor Z').map (conormalAlgebraPieceOneIso j').hom ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map a))).map
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j))).map
          ((zariskiReadingKernelIdealIso j).hom)) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom) ≫
          (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
          ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) :=
  ((((((((((((conormalSquare_step0 j j' a b hsq).trans
      (conormalSquare_step1 j j' a b hsq)).trans
      (conormalSquare_step2 j j' a b hsq)).trans
      (conormalSquare_step3 j j' a b hsq)).trans
      (conormalSquare_step4 j j' a b hsq comm)).trans
      (conormalSquare_step5 j j' a b hsq comm)).trans
      (conormalSquare_step6 j j' a b hsq comm)).trans
      (conormalSquare_step7 j j' a b hsq comm)).trans
      (conormalSquare_step8 j j' a b hsq comm)).trans
      (conormalSquare_step9 j j' a b hsq comm)).trans
      (conormalSquare_step10 j j' a b comm)).trans (conormalSquare_step11 j j' a b comm))

/-- The inverse images of modules on schemes in the spellings of Mathlib and of ringed spaces
agree on morphisms. -/
theorem scheme_modules_pullback_map_eq_modulePullback_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (g : M ⟶ N) :
    (Scheme.Modules.pullback f).map g =
      (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).map g :=
  rfl

/-- The inverse image of modules on ringed spaces, along a morphism of schemes, in the two
spellings of the morphism. -/
theorem modulePullback_map_eq_pullbackFunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace)} (g : M ⟶ N) :
    (RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).map g =
      (Stacks.RingedSpace.pullbackFunctor (ringedSpaceHom f)).map g :=
  rfl

/-- `AlgebraicGeometry.Space.zariskiReadingConormalIso`, written out. -/
theorem zariskiReadingConormalIso_hom_eq {Z₀ T₀ : BigFppfOver B S hS} (i : Z₀ ⟶ T₀)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i)] :
    (zariskiReadingConormalIso i).hom =
      (zariskiReadingFunctor Z₀).map (conormalAlgebraPieceOneIso i).hom ≫
        (zariskiReadingPullbackIso i (kernelIdealSheaf B S hS (yonedaSpaceMap i)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap i)).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map i)).map
            (zariskiReadingKernelIdealIso i).hom ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
            ((BigFppfOver.toScheme B S hS).map i)).inv :=
  rfl

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] in
private theorem conormalSquare_g0
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    (zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
        (zariskiReadingFunctor Z').map
        (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1) ≫ (zariskiReadingConormalIso j').hom =
      (zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
          (zariskiReadingFunctor Z').map
          (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1) ≫
          ((zariskiReadingFunctor Z').map (conormalAlgebraPieceOneIso j').hom ≫
          (zariskiReadingPullbackIso j'
          (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingKernelIdealIso j').hom) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j')).inv) :=
  congrArg (fun k => (zariskiReadingPullbackHom a).app
      ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
      (zariskiReadingFunctor Z').map
      (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
      (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1) ≫ k) (zariskiReadingConormalIso_hom_eq j')

omit [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)] in
private theorem conormalSquare_g1
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j)) :
    (zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
        (zariskiReadingFunctor Z').map
        (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1) ≫
        ((zariskiReadingFunctor Z').map (conormalAlgebraPieceOneIso j').hom ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j')).inv) =
      ((zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
          (zariskiReadingFunctor Z').map
          (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
          (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1) ≫
          (zariskiReadingFunctor Z').map (conormalAlgebraPieceOneIso j').hom ≫
          (zariskiReadingPullbackIso j'
          (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
          ((zariskiReadingKernelIdealIso j').hom)) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j')).inv :=
  ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (Category.assoc _ _ _))))))).symm

private theorem conormalSquare_g2
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    ((zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
        (zariskiReadingFunctor Z').map
        (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1) ≫
        (zariskiReadingFunctor Z').map (conormalAlgebraPieceOneIso j').hom ≫
        (zariskiReadingPullbackIso j'
        (kernelIdealSheaf B S hS (yonedaSpaceMap j')).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j')).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j')).map
        ((zariskiReadingKernelIdealIso j').hom)) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j')).inv =
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map a))).map
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j))).map
          ((zariskiReadingKernelIdealIso j).hom)) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom) ≫
          (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
          ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm)))) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j')).inv :=
  congrArg (· ≫
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
      ((BigFppfOver.toScheme B S hS).map j')).inv)
      (zariskiReadingConormalIso_square_core j j' a b hsq comm)

private theorem conormalSquare_h0
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingConormalIso j).hom) ≫ (Stacks.Conormal.conormalBaseChangeMap comm) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom ≫
          (zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).map
          ((zariskiReadingKernelIdealIso j).hom) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j)).inv) ≫
          ((RingedSpaceModuleAdjunction.modulePullback
          ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).map
          ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j)).hom) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
          (RingedSpaceModuleAdjunction.modulePullback
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom).map
          ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j')).inv) :=
  (congrArg (fun k => (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map (k) ≫
      (Stacks.Conormal.conormalBaseChangeMap comm)) (zariskiReadingConormalIso_hom_eq j)).trans
    (congrArg ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom ≫
        (zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).map
        ((zariskiReadingKernelIdealIso j).hom) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j)).inv) ≫ ·)
        (Stacks.Conormal.conormalBaseChangeMap_eq comm))

private theorem conormalSquare_h1
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom ≫
        (zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).map
        ((zariskiReadingKernelIdealIso j).hom) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j)).inv) ≫
        ((RingedSpaceModuleAdjunction.modulePullback
        ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).map
        ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j)).hom) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        (Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
        (RingedSpaceModuleAdjunction.modulePullback
        ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom).map
        ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j')).inv) =
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).map
          ((zariskiReadingKernelIdealIso j).hom)) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j)).inv)) ≫
          ((RingedSpaceModuleAdjunction.modulePullback
          ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).map
          ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j)).hom) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
          (RingedSpaceModuleAdjunction.modulePullback
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom).map
          ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j')).inv) :=
  congrArg (· ≫ _)
      (((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map_comp _ _).trans
    (congrArg (_ ≫ ·)
        (((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map_comp _ _).trans
      (congrArg (_ ≫ ·)
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map_comp _ _)))))

private theorem conormalSquare_h2
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).map
        ((zariskiReadingKernelIdealIso j).hom)) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j)).inv)) ≫
        ((RingedSpaceModuleAdjunction.modulePullback
        ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).map
        ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j)).hom) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        (Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
        (RingedSpaceModuleAdjunction.modulePullback
        ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom).map
        ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j')).inv) =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).map
          ((zariskiReadingKernelIdealIso j).hom)) ≫
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j)).inv) ≫
          (RingedSpaceModuleAdjunction.modulePullback
          ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).map
          ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j)).hom)) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
          (RingedSpaceModuleAdjunction.modulePullback
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom).map
          ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j')).inv :=
  (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (Category.assoc _ _ _).symm)))))

private theorem conormalSquare_h3
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).map
        ((zariskiReadingKernelIdealIso j).hom)) ≫
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j)).inv) ≫
        (RingedSpaceModuleAdjunction.modulePullback
        ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).map
        ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j)).hom)) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        (Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
        (RingedSpaceModuleAdjunction.modulePullback
        ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom).map
        ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j')).inv =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).map
          ((zariskiReadingKernelIdealIso j).hom)) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
          (RingedSpaceModuleAdjunction.modulePullback
          ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom).map
          ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j')).inv := by
  have e : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
      ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
      ((BigFppfOver.toScheme B S hS).map j)).inv) ≫
      (RingedSpaceModuleAdjunction.modulePullback
      ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).map
      ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
      ((BigFppfOver.toScheme B S hS).map j)).hom) = 𝟙 _ :=
    (congrArg (· ≫ _)
        (scheme_modules_pullback_map_eq_modulePullback_map ((BigFppfOver.toScheme B S hS).map a)
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j)).inv)).trans
      (((RingedSpaceModuleAdjunction.modulePullback
          ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).map_comp _ _).symm.trans
        ((congrArg (RingedSpaceModuleAdjunction.modulePullback
            ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).map
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
              ((BigFppfOver.toScheme B S hS).map j)).inv_hom_id).trans
          ((RingedSpaceModuleAdjunction.modulePullback
              ((BigFppfOver.toScheme B S hS).map a).toLRSHom.toShHom).map_id _)))
  exact congrArg (fun k => _ ≫ _ ≫ _ ≫ k) ((congrArg (· ≫ _) e).trans (Category.id_comp _))

private theorem conormalSquare_h4
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).map
        ((zariskiReadingKernelIdealIso j).hom)) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        (Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom ≫
        (RingedSpaceModuleAdjunction.modulePullback
        ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom).map
        ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j')).inv =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map a))).map
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j))).map
          ((zariskiReadingKernelIdealIso j).hom)) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom) ≫
          (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
          ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j')).inv := by
  have e₁ : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map j)).map
      ((zariskiReadingKernelIdealIso j).hom)) =
      (Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map a))).map
      ((Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j))).map
      ((zariskiReadingKernelIdealIso j).hom)) :=
    (scheme_modules_pullback_map_eq_pullbackFunctor_map ((BigFppfOver.toScheme B S hS).map a)
        _).trans
      (congrArg (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map a))).map
        (scheme_modules_pullback_map_eq_pullbackFunctor_map ((BigFppfOver.toScheme B S hS).map j)
            _))
  have e₂ : (RingedSpaceModuleAdjunction.modulePullback
      ((BigFppfOver.toScheme B S hS).map j').toLRSHom.toShHom).map
      ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) =
      (Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
      ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) :=
    modulePullback_map_eq_pullbackFunctor_map ((BigFppfOver.toScheme B S hS).map j') _
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  refine (congrArg (· ≫ _) e₁).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (· ≫ _) e₂))

private theorem conormalSquare_h5
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
        ((zariskiReadingPullbackIso j (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
        (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
        ((Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map a))).map
        ((Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j))).map
        ((zariskiReadingKernelIdealIso j).hom)) ≫
        (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
        (Stacks.ClosedImmersion.idealSheaf
        ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom) ≫
        (Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
        ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm))) ≫
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
        ((BigFppfOver.toScheme B S hS).map j')).inv =
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingFunctor Z).map (conormalAlgebraPieceOneIso j).hom) ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingPullbackIso j
          (kernelIdealSheaf B S hS (yonedaSpaceMap j)).toSheafOfModules
          (isQuasicoherentOnSite_kernelIdealSheaf_yonedaSpaceMap j)).inv) ≫
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map a))).map
          ((Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j))).map
          ((zariskiReadingKernelIdealIso j).hom)) ≫
          (Stacks.ClosedImmersion.pullbackCompIso (Stacks.Conormal.comm_toShHom comm)
          (Stacks.ClosedImmersion.idealSheaf
          ((BigFppfOver.toScheme B S hS).map j).toLRSHom.toShHom)).hom) ≫
          (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map j'))).map
          ((Stacks.ClosedImmersion.idealSheafMap (Stacks.Conormal.comm_toShHom comm)))) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf
          ((BigFppfOver.toScheme B S hS).map j')).inv :=
  ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _))))).symm

/-- **Naturality of the Zariski reading of the conormal module along a commutative square**
(Stacks 0B4I, the base change of the conormal identification at the level of points).  Let
`j' ≫ b = a ≫ j` be a commutative square of test objects whose scheme morphisms `j`, `j'` are
closed immersions.  The base change of the Zariski reading along `a`, the degree-one map of
conormal algebras of the square of represented algebraic spaces and the reading at `j'` give the
reading at `j` pulled back along `a` followed by the base-change map of conormal sheaves of the
scheme square (Stacks 01R4). -/
theorem zariskiReadingConormalIso_naturality_of_comm
    (hsq : (yonedaSpaceMap j') ≫ (yonedaSpaceMap b) = (yonedaSpaceMap a) ≫ (yonedaSpaceMap j))
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
        (zariskiReadingFunctor Z').map
        (conormalAlgebraPieceSquareMap B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) hsq 1) ≫ (zariskiReadingConormalIso j').hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingConormalIso j).hom) ≫ (Stacks.Conormal.conormalBaseChangeMap comm) :=
  ((conormalSquare_g0 j j' a b hsq).trans
      ((conormalSquare_g1 j j' a b hsq).trans (conormalSquare_g2 j j' a b hsq comm))).trans
      ((((((conormalSquare_h0 j j' a b comm).trans (conormalSquare_h1 j j' a b comm)).trans
      (conormalSquare_h2 j j' a b comm)).trans (conormalSquare_h3 j j' a b comm)).trans
      (conormalSquare_h4 j j' a b comm)).trans (conormalSquare_h5 j j' a b comm)).symm

/-- **Naturality of the Zariski reading of the conormal module along étale base change**: for a
cartesian square `j' ≫ b = a ≫ j` of represented algebraic spaces with `b` étale, the base change
of the Zariski reading, Stacks 09RR along the square and the reading of `j'` give the reading of
`j` pulled back along `a` followed by the base-change map of conormal sheaves of the scheme
square.  This is `AlgebraicGeometry.Space.zariskiReadingConormalIso_naturality_of_comm`, since
at an étale cartesian square the map of conormal algebras is the 09RR isomorphism. -/
theorem zariskiReadingConormalIso_naturality
    (sq : IsPullback (yonedaSpaceMap a) (yonedaSpaceMap j') (yonedaSpaceMap j) (yonedaSpaceMap b))
    (hb : IsEtale B S hS (yonedaSpaceMap b).hom)
    (comm : (BigFppfOver.toScheme B S hS).map j' ≫ (BigFppfOver.toScheme B S hS).map b =
        (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map j) :
    (zariskiReadingPullbackHom a).app ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫
        (zariskiReadingFunctor Z').map
        ((conormalAlgebraEtaleRestrictionPieceIso B S hS (yonedaSpaceMap a) (yonedaSpaceMap j')
        (yonedaSpaceMap j) (yonedaSpaceMap b) sq hb 1).hom) ≫ (zariskiReadingConormalIso j').hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map a)).map
          ((zariskiReadingConormalIso j).hom) ≫ (Stacks.Conormal.conormalBaseChangeMap comm) :=
  (congrArg (fun k => (zariskiReadingPullbackHom a).app
      ((conormalAlgebra B S hS (yonedaSpaceMap j)).piece 1) ≫ (zariskiReadingFunctor Z').map k ≫
      (zariskiReadingConormalIso j').hom)
    (conormalAlgebraPieceSquareMap_eq_etaleRestrictionPieceIso B S hS (yonedaSpaceMap a)
        (yonedaSpaceMap j') (yonedaSpaceMap j)
      (yonedaSpaceMap b) sq hb 1).symm).trans
    (zariskiReadingConormalIso_naturality_of_comm j j' a b sq.w.symm comm)

end Conormal

end AlgebraicGeometry.Space

end
