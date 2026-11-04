module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiDescended
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationAtlasFaithful
import all StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiChartSquare

/-!
# `ψ` of Stacks 084D restricted to a scheme point of the base

In Situation 0849 let `π : P = Proj_X(𝒜) ⟶ X` be the relative homogeneous spectrum of Stacks 084B,
`ψ_n : π^*𝒜_n ⟶ 𝒪_P(n)` the homomorphism of Stacks 084D
(`AlgebraicGeometry.Space.RelativeProjSituation.psiTwistHom`), and `f : T ⟶ X` a scheme point of
the base.  The base change clause of Stacks 084D asks that the identification
`(T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)` with the twist of Stacks 01NR on `T ×_X P = Proj_T(f^*𝒜)`
(`AlgebraicGeometry.Space.RelativeProjSituation.exists_fibreToSpace_twistModule_iso`) carry the
inverse image of `ψ_n` to `ψ` of Tag 01NR.  This file provides the pieces of that compatibility:

* the source of `ψ` at an arbitrary point: for a morphism `a : Q ⟶ P` over a scheme point
  `x : U ⟶ X` through `q : Q ⟶ U`, the identification `a^*π^*𝒜_n ≅ (q^*(x^*𝒜)_n)^a`
  (`AlgebraicGeometry.Space.pointChainPullbackIso`), its square along a further morphism of the
  site lying over a morphism of test objects
  (`AlgebraicGeometry.Space.modulePullback_map_pointChainPullbackIso_hom_comp₂_eq`), and its
  instance at the base change `T ×_X P ⟶ P`
  (`AlgebraicGeometry.Space.RelativeProjSituation.fibrePsiSourceIso`) together with Tag 01NR's
  `ψ` read through it (`AlgebraicGeometry.Space.RelativeProjSituation.fibrePsiHom`);
* the `ψ`-square of the comparison of twists of Stacks 085C along a morphism of base changes over
  a morphism `g : X' ⟶ X` of algebraic spaces
  (`…RelativeProjSituation.pullback_map_psiChartSchemeHom_comp_baseChange`, from the scheme-level
  `…RelativeProjBaseChangeTwist.congrBaseChangePsi_comp_congrBaseChangeTwistIso`),
  with the identification of the sources split into the comparison of restrictions of Stacks 084A
  and the comparison `v^*(g^*𝒜) ≅ (g ∘ v)^*𝒜`
  (`…RelativeProjSituation.baseChangePieceChainSchemeIso_hom_eq`), and the corresponding square of
  the source of `ψ` on the attached modules
  (`…RelativeProjSituation.modulePullback_map_pointChainPullbackIso_hom_comp₂_baseChange`);
* the identification of the sources of `ψ` along a morphism of base changes split, as an
  isomorphism of quasi-coherent modules, into the comparison of restrictions and the comparison
  `v^*(g^*𝒜) ≅ (g ∘ v)^*𝒜`
  (`…RelativeProjSituation.isoMk_baseChangePieceChainSchemeIso_eq_trans`);
* the abstract assembly of the two chains of squares
  (`AlgebraicGeometry.Space.comp_comp_eq_of_psi_squares`), the naturality of the identification
  along a square (`AlgebraicGeometry.Space.pullbackSquareHom_naturality`), and the squares of the
  assembly at a scheme point `f : T ⟶ X` on the atlas `T_U ×_T P' ⟶ T ×_X P`
  (`…RelativeProjSituation.pointPsi_chart_baseChange`,
  `…RelativeProjSituation.pointPsi_point_baseChange`,
  `…RelativeProjSituation.pointPsi_chart_source`, `…RelativeProjSituation.pointPsi_point_source`
  and the others named `pointPsi_*`).

## Implementation notes

Morphisms which contain a transport `AlgebraicGeometry.Space.pullbackTransport` are compared in the
named binary composites `CategoryTheory.comp₂`; the identifications of the sources are compared
with Tag 01NR's restricted algebras written over the site of the situation
(`(B := s.site)`), and the two spellings of the comparison of restrictions (through
`AlgebraicGeometry.Space.RelativeProjSituation.fibreToBase` and through the functor to schemes)
are identified at the level of isomorphisms
(`…RelativeProjSituation.isoMk_pullbackIsoOfSquare_eq_baseChangeRestrictChainSchemeIso`).

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-! ### The source of `ψ` along a morphism to `P` over a scheme point of the base -/

section PointChain

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Pa : AlgebraicSpaces B S hS} (p : Pa ⟶ X)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)
  {Q U : BigFppfOver B S hS}
  (a : (⟨yoneda.obj Q, isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS) ⟶ Pa)
  (q : Q ⟶ U) (x : yoneda.obj U ⟶ X.1)
  (ha : CategoryStruct.comp (obj := AlgebraicSpaces B S hS) a p =
    CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS q)
      (pointHom x))

/-- **The inverse image of `p^*𝒜_n` along a morphism `a : Q ⟶ P` lying over a scheme point
`x : U ⟶ X`**: for a square `a ≫ p = q ≫ x` with `q : Q ⟶ U` a morphism of the site, the
composition comparison of Stacks 03LU along the square, the identification of `x^*𝒜_n` with the
module attached to its Zariski reading (`AlgebraicGeometry.Space.zariskiReadingQuasicoherentIso`),
and the identification of the inverse image along `q` of an attached module
(`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`):
`a^*p^*𝒜_n ≅ (q^*(x^*𝒜)_n)^a`.  On the atlas of a presentation of `P = Proj_X(𝒜)` this is
`AlgebraicGeometry.Space.RelativeProjPoints.chartPullbackIso`. -/
def pointChainPullbackIso (n : ℤ) :
    (modulePullback B S hS a).obj ((modulePullback B S hS p).obj (A.piece n)) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Q).functor.obj
        (quasicoherentPullbackObj B S hS q (zariskiReadingQcoh U
          ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)))).obj :=
  (modulePullbackCompIso B S hS a p).app (A.piece n) ≪≫
    eqToIso (congrArg (fun f => (modulePullback B S hS f).obj (A.piece n)) ha) ≪≫
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS q) (pointHom x)).app
      (A.piece n)).symm ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS q)).mapIso
      (zariskiReadingQuasicoherentIso U ((etalePointAlgebra A U x).piece n)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n) :
        (modulePullback B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
          (pointHom x)).obj (A.piece n) ≅ _) ≪≫
    modulePullbackRepresentedQuasicoherentIso B S hS q
      (zariskiReadingQcoh U ((etalePointAlgebra A U x).piece n)
        (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n))

variable {Q' V : BigFppfOver B S hS} (q' : Q' ⟶ V) (x' : yoneda.obj V ⟶ X.1)

/-- **The square of `AlgebraicGeometry.Space.pointChainPullbackIso` along a morphism `y` of the
site lying over `k`**: for `y ≫ q = q' ≫ k` with `k ≫ x = x'`, the identification along `a`,
pulled back along `y`, read through `y^*(N^a) ≅ (y^*N)^a` and followed by the module attached to
the chain `y^*q^*(x^*𝒜)_n ≅ q'^*k^*(x^*𝒜)_n ⟶ q'^*(x'^*𝒜)_n` of the comparison of restrictions of
Stacks 084A, is the contraction `y^*a^* ≅ (y ≫ a)^*` followed by the identification along
`y ≫ a`. -/
theorem modulePullback_map_pointChainPullbackIso_hom_comp₂_eq (n : ℤ)
    (σ : (modulePullback B S hS a).obj ((modulePullback B S hS p).obj (A.piece n)) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS Q).functor.obj
        (quasicoherentPullbackObj B S hS q (zariskiReadingQcoh U
          ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)))).obj)
    (hσ : σ = pointChainPullbackIso p A hA a q x ha n) (k : V ⟶ U)
    (hv : yoneda.map k ≫ x = x')
    (y : Q' ⟶ Q) (e : y ≫
        q = q' ≫ k)
    (e' : CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS y)
        (representedSpaceMap B S hS q) =
      CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS
          q') (representedSpaceMap B S hS k))
    (ht : CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (Y :=
        Pa)
        (CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (Z :=
            Pa) (representedSpaceMap B S hS y) a) p =
      CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS
          q') (pointHom x'))
    (ch : quasicoherentPullbackObj B S hS y (quasicoherentPullbackObj B S hS
        q (zariskiReadingQcoh U
            ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n))) ⟶
      quasicoherentPullbackObj B S hS q' (zariskiReadingQcoh V
          ((etalePointAlgebra A V x').piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x' n)))
    (hch : ch = comp₂ (quasicoherentPullbackCompIso B S hS y q
        (zariskiReadingQcoh U ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n))).hom
      (comp₂ (eqToHom (congrArg (fun g => quasicoherentPullbackObj B S hS g
          (zariskiReadingQcoh U ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n))) e :
          quasicoherentPullbackObj B S hS (y ≫ q)
              (zariskiReadingQcoh U ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)) =
            quasicoherentPullbackObj B S hS (q' ≫ k)
                (zariskiReadingQcoh U ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n))))
        (comp₂ (quasicoherentPullbackCompIso B S hS q' k
            (zariskiReadingQcoh U ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n))).inv
          (quasicoherentPullbackMap B S hS q'
              (ObjectProperty.homMk ((pointComparison A k x x' hv).app n) :
          quasicoherentPullbackObj B S hS k (zariskiReadingQcoh U
              ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)) ⟶
              (zariskiReadingQcoh V ((etalePointAlgebra A V x').piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x' n))))))) :
    comp₂ ((modulePullback B S hS (representedSpaceMap B S hS y)).map (Iso.hom (X :=
        (modulePullback B S hS (X := (⟨yoneda.obj Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS))
          a).obj ((modulePullback B S hS
              p).obj (A.piece n)))
        (Y := ((representedQuasicoherentSchemeEquivalence B S hS
            Q).functor.obj
            (quasicoherentPullbackObj B S hS q (zariskiReadingQcoh U
                ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)))).obj)
        σ))
      (comp₂ (modulePullbackRepresentedQuasicoherentIso B S hS y (quasicoherentPullbackObj B S hS
          q (zariskiReadingQcoh U
              ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)))).hom
        ((representedQuasicoherentSchemeEquivalence B S hS Q').functor.map ch).hom) =
    comp₂ (comp₂ ((modulePullbackCompIso B S hS (Z := Pa)
        (representedSpaceMap B S hS y) a).hom.app
            ((modulePullback B S hS p).obj (A.piece n)))
        (comp₂ ((modulePullbackCompIso B S hS (Y := Pa)
            (CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (Z :=
                Pa) (representedSpaceMap B S hS y)
                    a) p).hom.app
            (A.piece n))
          (pullbackTransport (A.piece n) ht)))
      (comp₂ ((modulePullbackCompIso B S hS (representedSpaceMap B S hS q') (pointHom x')).inv.app
          (A.piece n))
        (comp₂ ((modulePullback B S hS (representedSpaceMap B S hS q')).map
            (zariskiReadingQuasicoherentIso V
                ((etalePointAlgebra A V x').piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x' n)).hom)
          (modulePullbackRepresentedQuasicoherentIso B S hS q'
              (zariskiReadingQcoh V ((etalePointAlgebra A V x').piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x' n))).hom)) := by
  subst hσ
  have hι := map_hom_eq_comp₂_of_eq_trans (modulePullback B S hS (representedSpaceMap B S hS y))
      (X₀ := (modulePullback B S hS (X := (⟨yoneda.obj Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS))
          a).obj ((modulePullback B S hS
              p).obj (A.piece n)))
    (X₅ := ((representedQuasicoherentSchemeEquivalence B S hS Q).functor.obj
            (quasicoherentPullbackObj B S hS q (zariskiReadingQcoh U
                ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)))).obj)
              (pointChainPullbackIso p A hA a q x ha n)
    ((modulePullbackCompIso B S hS (X := (⟨yoneda.obj Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS)) (Y :=
          Pa) (Z := X) a p).app (A.piece n))
    (eqToIso (X := (modulePullback B S hS (CategoryStruct.comp (obj := AlgebraicSpaces B S hS)
        (X := (⟨yoneda.obj Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS)) (Y :=
          Pa) (Z := X) a p)).obj (A.piece n))
          (Y := (modulePullback B S hS (CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (X :=
              (⟨yoneda.obj Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
              (Z := X) (representedSpaceMap B S hS q)
                  (pointHom x))).obj (A.piece n))
          (congrArg (fun f => (modulePullback B S hS f).obj (A.piece n))
            (ha : CategoryStruct.comp
                (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS)) (Y :=
          Pa) (Z := X) a p = CategoryStruct.comp
                      (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
              (Z := X) (representedSpaceMap B S hS q)
                  (pointHom x))))
    (((modulePullbackCompIso B S hS (representedSpaceMap B S hS q)
        (pointHom x)).app (A.piece n)).symm) ((modulePullback B S hS
            (representedSpaceMap B S hS q)).mapIso
                ((zariskiReadingQuasicoherentIso U
                    ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)) :
              (modulePullback B S hS (X :=
                  (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S
                      hS)) (pointHom x)).obj (A.piece n) ≅ _))
                          (modulePullbackRepresentedQuasicoherentIso B S hS
                              q (zariskiReadingQcoh U
                                  ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)))
    (rfl) (pullbackTransport (T := (⟨yoneda.obj
        Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS)) (X := X)
          (f := CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj
              Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS)) (Y :=
          Pa) (Z := X) a p)
      (g := CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (X := (⟨yoneda.obj
          Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS)) (Y :=
          (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
              (Z := X) (representedSpaceMap B S hS q)
                  (pointHom x)) (A.piece n) (ha)) rfl
  have hchA := map_hom_eq_comp₂_of_eq_comp₂
    (representedQuasicoherentSchemeEquivalence B S hS Q').functor ch _ _ _ _ hch
  have hLa := modulePullback_map_modulePullbackRepresentedQuasicoherentIso_comp_chain y
      q q' k
    e e' (zariskiReadingQcoh U ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n))
              (zariskiReadingQcoh V ((etalePointAlgebra A V x').piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x' n))
              (ObjectProperty.homMk ((pointComparison A k x x' hv).app n) :
          quasicoherentPullbackObj B S hS k (zariskiReadingQcoh U
              ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)) ⟶
              (zariskiReadingQcoh V ((etalePointAlgebra A V x').piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x' n)))
  have hnat := modulePullback_map_map_comp₂_modulePullbackCompIso_eq (W := (⟨yoneda.obj
      Q',
      isAlgebraicSpace_yoneda B S hS Q'⟩ : AlgebraicSpaces B S hS))
          (V := (⟨yoneda.obj Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS))
    (U := (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) (R :=
        (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
            (representedSpaceMap B S hS y) (representedSpaceMap B S hS q)
    (representedSpaceMap B S hS q')
        (representedSpaceMap B S hS k) e' (M := (modulePullback B S hS (X :=
            (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))
                (pointHom x)).obj (A.piece n))
    (N := ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj
        (zariskiReadingQcoh U ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n))).obj)
    ((zariskiReadingQuasicoherentIso U ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)) :
              (modulePullback B S hS (X :=
                  (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S
                      hS)) (pointHom x)).obj (A.piece n) ≅ _).hom
  have hK := modulePullback_map_zariskiReadingQuasicoherentIso_hom_comp_pointComparison_pullback
    k q' A hA x x' hv n
  have hLb := modulePullback_map_comp_modulePullbackCompIso_eq_of_squares (W := (⟨yoneda.obj
      Q',
      isAlgebraicSpace_yoneda B S hS Q'⟩ : AlgebraicSpaces B S hS))
          (V := (⟨yoneda.obj Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS))
    (P := Pa) (X := X) (U :=
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) (R :=
            (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
                (representedSpaceMap B S hS y) a
                    p
    (representedSpaceMap B S hS q) (pointHom x)
        (representedSpaceMap B S hS q')
            (representedSpaceMap B S hS k) (pointHom x')
                (ha)
    e' (pointHom_comp k hv) ht (A.piece n)
  exact comp₂_eq_of_chart_square_pieces hι hchA
    (map_app_hom_eq (modulePullback B S hS (representedSpaceMap B S hS y))
        (modulePullbackCompIso B S hS (X := (⟨yoneda.obj Q,
      isAlgebraicSpace_yoneda B S hS Q⟩ : AlgebraicSpaces B S hS)) (Y :=
          Pa) (Z := X) a p) (A.piece n))
    (map_app_symm_hom_eq (modulePullback B S hS (representedSpaceMap B S hS y))
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS q)
            (pointHom x)) (A.piece n))
    (map_mapIso_hom_eq (modulePullback B S hS (representedSpaceMap B S hS y))
        (modulePullback B S hS (representedSpaceMap B S hS q))
      ((zariskiReadingQuasicoherentIso U ((etalePointAlgebra A U x).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA x n)) :
              (modulePullback B S hS (X :=
                  (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S
                      hS)) (pointHom x)).obj (A.piece n) ≅ _)) hLa hnat hK hLb


end PointChain

/-- **The identification along a square `c'' ≫ h = Y ≫ c` is natural**. -/
theorem pullbackSquareHom_naturality {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U'' U X'' X : AlgebraicSpaces B S hS} (c'' : U'' ⟶ X'') (c : U ⟶ X) (h : X'' ⟶ X)
    (Y : U'' ⟶ U) (hY : c'' ≫ h = Y ≫ c) {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) :
    (modulePullback B S hS c'').map ((modulePullback B S hS h).map φ) ≫
        pullbackSquareHom c'' c h Y hY N =
      pullbackSquareHom c'' c h Y hY M ≫
        (modulePullback B S hS Y).map ((modulePullback B S hS c).map φ) := by
  rw [pullbackSquareHom_eq_comp, pullbackSquareHom_eq_comp]
  have n1 := (modulePullbackCompIso B S hS c'' h).hom.naturality φ
  have n3 := (modulePullbackCompIso B S hS Y c).inv.naturality φ
  simp only [Functor.comp_map] at n1 n3
  simp only [modulePullbackCompHom, modulePullbackCompInv]
  rw [reassoc_of% n1, pullbackTransport_naturality_assoc, n3]
  simp only [Category.assoc]

/-- The inverse image along `c''` of the inverse image along `h` of a morphism, with the source of
`h` spelled as its own underlying presheaf with its property (the spelling of the codomain of the
atlas of a presentation). -/
theorem modulePullback_map_map_eq_of_mk {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {U'' X'' X : AlgebraicSpaces B S hS}
    (c'' : U'' ⟶ (⟨X''.obj, X''.property⟩ : AlgebraicSpaces B S hS)) (h : X'' ⟶ X)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) :
    (modulePullback B S hS c'').map ((modulePullback B S hS h).map φ) =
      (modulePullback B S hS c'').map ((modulePullback B S hS
        (X := (⟨X''.obj, X''.property⟩ : AlgebraicSpaces B S hS)) h).map φ) := by
  obtain ⟨X'', hX''⟩ := X''
  dsimp only



/-- `AlgebraicGeometry.Space.pullbackTransport_comp_modulePullbackCompIso_hom_app` with the
comparison along `a` read through `a = b`. -/
theorem pullbackTransport_comp_modulePullbackCompIso_hom_app_of_eq {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {T Y X : AlgebraicSpaces B S hS} (π : Y ⟶ X)
    {a b : T ⟶ Y} (h : a = b) {Q : T ⟶ X} (hb : b ≫ π = Q) (M : Modules.{u, u} B S hS X.1 X.2) :
    pullbackTransport ((modulePullback B S hS π).obj M) h ≫
        (modulePullbackCompIso B S hS b π).hom.app M ≫ pullbackTransport M hb =
      (modulePullbackCompIso B S hS a π).hom.app M ≫
        pullbackTransport M ((congrArg (· ≫ π) h).trans hb) :=
  pullbackTransport_comp_modulePullbackCompIso_hom_app π h _ hb M

/-- Images of composites under a functor, followed by a common morphism. -/
theorem map_comp_comp_eq_of_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Y' Z : C} {W : D} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Y'} {d : Y' ⟶ Z} {o : F.obj Z ⟶ W}
    (h : (F.map a ≫ F.map b) ≫ o = (F.map c ≫ F.map d) ≫ o) :
    F.map (a ≫ b) ≫ o = F.map (c ≫ d) ≫ o := by
  rw [F.map_comp, F.map_comp, h]

/-- A left inverse of `r` followed by the inverse of `b`, composed with `b` followed by `r`. -/
theorem comp_inv_comp_comp_eq_id {C : Type*} [Category C] {X Y Z : C} (a : X ⟶ Y) (b : Z ⟶ Y)
    [IsIso b] (r : Y ⟶ X) (h : a ≫ r = 𝟙 X) : (a ≫ inv b) ≫ (b ≫ r) = 𝟙 X := by
  rw [Category.assoc, IsIso.inv_hom_id_assoc, h]

/-- The comparison along a square of a composite `T₁ ≪≫ T₂` is the comparison of `T₁` followed by
the pullback of `T₂`. -/
theorem pullbackIsoOfSquare_trans_hom {X X' Y Y' : Scheme.{u}} (ιX : X' ⟶ X) (ιY : Y' ⟶ Y)
    (y : Y' ⟶ X') (pc : Y ⟶ X) (e : y ≫ ιX = ιY ≫ pc) {M : X.Modules} {M' M'' : Y.Modules}
    (T₁ : (Scheme.Modules.pullback pc).obj M ≅ M') (T₂ : M' ≅ M'') :
    (pullbackIsoOfSquare ιX ιY y pc e (T₁ ≪≫ T₂)).hom =
      (pullbackIsoOfSquare ιX ιY y pc e T₁).hom ≫ (Scheme.Modules.pullback ιY).map T₂.hom := by
  simp only [pullbackIsoOfSquare, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]

/-- **The assembly of the compatibility of `ψ` with the base change to a scheme point**, at
variables: two chains of squares from a common source to a common target, sharing their last
factors, agree after an isomorphism. -/
theorem comp_comp_eq_of_psi_squares {C : Type*} [Category C]
    {S1 S2 S7 S8 Z Tt Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 K K' K1 K2 K3 R1 R3 R4 : C}
    {Lh : S1 ⟶ S2} {Le : S2 ⟶ Z} {oyc : Z ⟶ Tt} {ppc : S2 ⟶ Tt}
    {pSH2 : S2 ⟶ Y2} {Yκ : Y2 ⟶ Y3} {m2 : Y3 ⟶ Y4} {EΘA : Y4 ⟶ Tt}
    {pSH1 : S1 ⟶ Y1} {Yψ : Y1 ⟶ Y2} {YσU : Y1 ⟶ Y5} {YEψU : Y5 ⟶ Y3}
    {m1 : Y5 ⟶ Y6} {EψU : Y6 ⟶ Y4} {EchA : Y6 ⟶ K} {Ec2 : K ⟶ K'} {Eψ' : K' ⟶ Tt}
    {cA : Y1 ⟶ Y7} {c2A : Y7 ⟶ Y8} {trA : Y8 ⟶ K1} {b1 : K1 ⟶ K2} {b2 : K2 ⟶ K3} {b3 : K3 ⟶ K}
    {cH cH' : S1 ⟶ S7} {tr : S7 ⟶ Y7} {cAinv : Y7 ⟶ Y1} {c2B : S7 ⟶ S8} {trB : S8 ⟶ K1}
    {Rσ : S1 ⟶ R1} {REψ : R1 ⟶ Z} {m3 : Z ⟶ R3} {EΘB EΘB' : R3 ⟶ Tt}
    {m4 : R1 ⟶ R4} {EψT : R4 ⟶ R3} {EchB : R4 ⟶ K}
    (he : Le ≫ oyc = ppc) (hppc : ppc = pSH2 ≫ Yκ ≫ m2 ≫ EΘA)
    (hnat1 : Lh ≫ pSH2 = pSH1 ≫ Yψ) (hchart : Yψ ≫ Yκ = YσU ≫ YEψU)
    (hnat2 : YEψU ≫ m2 = m1 ≫ EψU) (hbA : EψU ≫ EΘA = EchA ≫ Ec2 ≫ Eψ')
    (hG2A : comp₂ YσU (comp₂ m1 EchA) = comp₂ (comp₂ cA (comp₂ c2A trA)) (comp₂ b1 (comp₂ b2 b3)))
    (hpSH1 : pSH1 = cH' ≫ tr ≫ cAinv) (hcH : cH' = cH) (hcA : cAinv ≫ cA = 𝟙 _)
    (htr : tr ≫ c2A ≫ trA = c2B ≫ trB) (hoyc : oyc = m3 ≫ EΘB') (hEΘB : EΘB' = EΘB)
    (hnat3 : REψ ≫ m3 = m4 ≫ EψT) (hbB : EψT ≫ EΘB = EchB ≫ Ec2 ≫ Eψ')
    (hG2B : comp₂ Rσ (comp₂ m4 EchB) = comp₂ (comp₂ cH (comp₂ c2B trB)) (comp₂ b1 (comp₂ b2 b3))) :
    (Lh ≫ Le) ≫ oyc = (Rσ ≫ REψ) ≫ oyc := by
  subst hcH hEΘB
  simp only [comp₂_eq, Category.assoc] at hG2A hG2B
  have hL : (Lh ≫ Le) ≫ oyc = cH' ≫ c2B ≫ trB ≫ b1 ≫ b2 ≫ b3 ≫ Ec2 ≫ Eψ' := by
    rw [Category.assoc, he, hppc, reassoc_of% hnat1, reassoc_of% hchart, reassoc_of% hnat2, hbA,
      reassoc_of% hG2A, hpSH1, Category.assoc, Category.assoc, reassoc_of% hcA,
      reassoc_of% htr]
  have hR : (Rσ ≫ REψ) ≫ oyc = cH' ≫ c2B ≫ trB ≫ b1 ≫ b2 ≫ b3 ≫ Ec2 ≫ Eψ' := by
    rw [Category.assoc, hoyc, reassoc_of% hnat3, hbB, reassoc_of% hG2B]
  rw [hL, hR]

/-- An isomorphism of a full subcategory made from an isomorphism of the ambient category is a
composite as soon as its underlying morphism is. -/
theorem isoMk_eq_trans_of_hom_eq {D : Type*} [Category D] {P : ObjectProperty D}
    {a b c : P.FullSubcategory} (i : a.obj ≅ c.obj) (j : a.obj ≅ b.obj) (l : b ≅ c)
    (m : b.obj ⟶ c.obj) (h : i.hom = j.hom ≫ m) (hm : l.hom.hom = m) :
    P.isoMk i = P.isoMk j ≪≫ l :=
  Iso.ext (ObjectProperty.hom_ext _ (h.trans (congrArg (j.hom ≫ ·) hm.symm)))

/-- A square of quasi-coherent modules whose comparison is a composite of two isomorphisms, read
through a functor into a full subcategory. -/
theorem map_hom_comp_map_hom_eq_of_comp_eq_trans {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty D} (F : C ⥤ P.FullSubcategory) {a b b' c d : C} {x : a ⟶ b}
    {θ : b ⟶ d} {i : a ≅ c} {j : a ≅ b'} {l : b' ≅ c} {ψ : c ⟶ d} (h : x ≫ θ = i.hom ≫ ψ)
    (hi : i = j ≪≫ l) :
    (F.map x).hom ≫ (F.map θ).hom = (F.map j.hom).hom ≫ (F.map l.hom).hom ≫ (F.map ψ).hom := by
  subst hi
  rw [← ObjectProperty.FullSubcategory.comp_hom, ← F.map_comp, h, Iso.trans_hom, F.map_comp,
    F.map_comp, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc]

/-- The images of a commutative square under a functor commute. -/
theorem map_comp_map_eq_of_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c d : C} {x : a ⟶ b} {k : b ⟶ c} {σ : a ⟶ d} {ψ : d ⟶ c} (h : x ≫ k = σ ≫ ψ) :
    F.map x ≫ F.map k = F.map σ ≫ F.map ψ := by
  rw [← F.map_comp, h, F.map_comp]

namespace RelativeProjSituation

open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (congrHom)
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (congrBaseChangePsi
  congrBaseChangePsi_comp_congrBaseChangeTwistIso)

variable (s : RelativeProjSituation.{u, m})

/-! ### `ψ` along a morphism of base changes over a morphism of algebraic spaces -/

section BaseChangeChain

variable {X' : AlgebraicSpaces s.site s.base s.containsBase} (g : X' ⟶ s.space)
  {W V : BigFppfOver s.site s.base s.containsBase} {w : yoneda.obj W ⟶ s.space.1}
  {v : yoneda.obj V ⟶ X'.1} (k : V ⟶ W) (hv : yoneda.map k ≫ w = v ≫ g.hom)
  (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre W w)
  (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
    (s.relativeProjBaseChangeHom g) y k)

include hy in
/-- A morphism of base changes lying over `k` and `P' ⟶ P` commutes, on schemes, with the
structure morphisms to the test objects. -/
theorem fibreToBase_comp_of_liesOverAlong :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map y ≫ s.fibreToBase W w =
      (s.pullback g).fibreToBase V v ≫
        (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k :=
  map_comp_map_eq_of_comp_eq _ hy.1

omit y hy in
/-- **The identification `k^*(w^*𝒜)_n ≅ v^*(g^*𝒜)_n` of the restricted algebras**, in degree
`n`: the comparison of the restrictions of Stacks 084A along `k` (to the point `g ∘ v` of `X`)
followed by the inverse of the comparison `v^*(g^*𝒜) ≅ (g ∘ v)^*𝒜` of the restriction data. -/
def baseChangePieceIso (n : ℤ) :
    (Scheme.Modules.pullback
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)).obj
        ((s.shrink.pointAlgebra W w).piece n) ≅
      ((s.pullback g).shrink.pointAlgebra V v).piece n :=
  @asIso _ _ _ _ ((pointComparisonUnital (s := s.shrink) k w (v ≫ g.hom) hv).app n)
      (isIso_pointComparisonUnital_app (s := s.shrink) k w (v ≫ g.hom) hv n) ≪≫
    (@asIso _ _ _ _ (((s.pullbackComapHom g).hom v).app n)
      ((s.pullbackComapHom g).isIso_hom_app v n)).symm

omit y hy in
/-- `AlgebraicGeometry.Space.RelativeProjSituation.baseChangePieceIso` is a left inverse of the
comparison of the restricted algebras along `k` and `g`. -/
theorem baseChangePieceIso_hom_comp_congrHom_app (n : ℤ) :
    (s.baseChangePieceIso g k hv n).hom ≫
      (congrHom (s.baseChangeAlgebraHom g k w v hv)).app n = 𝟙 _ := by
  have h := s.pointComparisonUnital_comp_congrHom_restrict k hv n
  have h2 : (s.baseChangePieceIso g k hv n).hom =
      (pointComparisonUnital (s := s.shrink) k w (v ≫ g.hom) hv).app n ≫
        @inv _ _ _ _ (((s.pullbackComapHom g).hom v).app n)
          ((s.pullbackComapHom g).isIso_hom_app v n) := rfl
  have h3 : (congrHom (s.baseChangeAlgebraHom g k w v hv)).app n =
      ((s.pullbackComapHom g).hom v).app n ≫
        (congrHom (A₁ := s.shrink.pointAlgebra V (v ≫ g.hom))
          (A₂ := (s.shrink.pointAlgebra W w).pullback
            ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k))
          (s.quadrupleRestriction.restrict k w (v ≫ g.hom) hv)).app n := rfl
  rw [h2, h3]
  exact @comp_inv_comp_comp_eq_id _ _ _ _ _ _ _ ((s.pullbackComapHom g).isIso_hom_app v n) _ h

/-- **The identification `y^*π_W^*(w^*𝒜)_n ≅ π_V'^*(v^*(g^*𝒜))_n` of the sources of `ψ`** along a
morphism `y : V ×_{X'} P' ⟶ W ×_X P` of base changes lying over `k` and `P' ⟶ P`: the comparison
along the square `y ≫ π_W = π'_V ≫ k` (`AlgebraicGeometry.Space.pullbackIsoOfSquare`) of
`AlgebraicGeometry.Space.RelativeProjSituation.baseChangePieceIso`. -/
def baseChangePieceChainSchemeIso (n : ℤ) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).obj
        ((Scheme.Modules.pullback (s.fibreToBase W w)).obj ((s.shrink.pointAlgebra W w).piece n)) ≅
      (Scheme.Modules.pullback ((s.pullback g).fibreToBase V v)).obj
        (((s.pullback g).shrink.pointAlgebra V v).piece n) :=
  pullbackIsoOfSquare (s.fibreToBase W w) ((s.pullback g).fibreToBase V v)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
    (s.fibreToBase_comp_of_liesOverAlong g k y hy) (s.baseChangePieceIso g k hv n)

/-- The underlying morphism of the comparison of the twists of Stacks 085C along `y` is the
comparison along the square of `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`. -/
theorem baseChangeTwistPieceComparison_hom_hom (n : ℤ) :
    (s.baseChangeTwistPieceComparison g k hv y hy n).hom.hom =
      (pullbackSheafIsoOfSquare (s.toRelativeProj W w)
        ((s.pullback g).toRelativeProj V v :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj
              ((s.pullback g).relativeProjPoints.fibre V v) ⟶
            (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.map_comp_toRelativeProj_baseChange g y)
        (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra W w)).scheme)
          (Y := (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.congrBaseChangeTwistIso
            (s.shrink.pointAlgebra W w)
            ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
            (A₁ := (s.pullback g).shrink.pointAlgebra V v) (s.baseChangeAlgebraHom g k w v hv)
            (s.isIso_baseChangeAlgebraHom_app g k w v hv)
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            (s.toScheme_map_eq_of_liesOverAlong g hv hy)) n)).hom :=
  (rfl : _ = (s.baseChangeTwistSheafIso g k hv y hy n).hom).trans rfl

/-- **Tag 01NR's `ψ` is carried along a morphism of base changes over `g : X' ⟶ X`**: on the
scheme of `V ×_{X'} P'`, the pullback along `y` of `ψ` at `W` (in adjoint form), followed by the
comparison of the twists of Stacks 085C along `y`, is the identification of the sources followed
by `ψ` of the pulled-back situation at `V`.  This is the comparison of twists carrying `ψ` to `ψ`
(`…RelativeProjBaseChangeTwist.congrBaseChangePsi_comp_congrBaseChangeTwistIso`) transposed
along `π'_V^* ⊣ π'_{V*}`. -/
theorem pullback_map_psiChartSchemeHom_comp_baseChange (n : ℕ) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).map
        (s.psiChartSchemeHomOfAdjoint W w n) ≫
        (s.baseChangeTwistPieceComparison g k hv y hy (n : ℤ)).hom.hom =
      (s.baseChangePieceChainSchemeIso g k hv y hy (n : ℤ)).hom ≫
        (s.pullback g).psiChartSchemeHomOfAdjoint V v n := by
  exact pullback_map_pullbackAdjointPsi_comp_eq_of_congr
    (hpcT := s.toScheme_map_comp_toBase_of_liesOverAlong g hy)
    (ψ₀ := congrBaseChangePsi (s.shrink.pointAlgebra W w)
      ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
      (s.baseChangeAlgebraHom g k w v hv)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (s.toScheme_map_comp_toBase_of_liesOverAlong g hy) n)
    (congrBaseChangePsi_comp_congrBaseChangeTwistIso _ _ _ _ _ _
      (s.toScheme_map_comp_toBase_of_liesOverAlong g hy) n) rfl rfl rfl
    (s.baseChangeTwistPieceComparison_hom_hom g k hv y hy (n : ℤ)) rfl
    (s.baseChangePieceIso_hom_comp_congrHom_app g k hv (n : ℤ))

/-- **`RelativeProjSituation.pullback_map_psiChartSchemeHom_comp_baseChange` as a square of
quasi-coherent modules** on the scheme of `V ×_{X'} P'`. -/
theorem quasicoherentPullbackMap_psiChartSchemeHom_comp_baseChange (n : ℕ) :
    quasicoherentPullbackMap s.site s.base s.containsBase y
        (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint W w n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W w) (zariskiReadingQcoh W ((etalePointAlgebra (B :=
                  s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece (n : ℤ))
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w (n :
                ℤ))) ⟶
            s.twistPieceQcoh W w (n : ℤ)) ≫
        (s.baseChangeTwistPieceComparison g k hv y hy (n : ℤ)).hom =
      (ObjectProperty.isoMk _ (s.baseChangePieceChainSchemeIso g k hv y hy (n : ℤ)) :
          quasicoherentPullbackObj s.site s.base s.containsBase y
              (quasicoherentPullbackObj s.site s.base s.containsBase
                (s.relativeProjPoints.fibreHom W w) (zariskiReadingQcoh W ((etalePointAlgebra (B
                    := s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece (n : ℤ))
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w (n :
                ℤ)))) ≅
            quasicoherentPullbackObj s.site s.base s.containsBase
              ((s.pullback g).relativeProjPoints.fibreHom V v)
              ((s.pullback g).pointPieceQcoh V v (n : ℤ))).hom ≫
        (ObjectProperty.homMk ((s.pullback g).psiChartSchemeHomOfAdjoint V v n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              ((s.pullback g).relativeProjPoints.fibreHom V v)
              ((s.pullback g).pointPieceQcoh V v (n : ℤ)) ⟶
            (s.pullback g).twistPieceQcoh V v (n : ℤ)) :=
  ObjectProperty.hom_ext _ (s.pullback_map_psiChartSchemeHom_comp_baseChange g k hv y hy n)

include hy in
/-- A morphism of base changes lying over `k` and `P' ⟶ P` commutes, on schemes, with the
structure morphisms to the test objects, read through the functor to schemes. -/
theorem toScheme_map_comp_fibreHom_of_liesOverAlong :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map y ≫
        (BigFppfOver.toScheme s.site s.base s.containsBase).map
          (s.relativeProjPoints.fibreHom W w) =
      (BigFppfOver.toScheme s.site s.base s.containsBase).map
          ((s.pullback g).relativeProjPoints.fibreHom V v) ≫
        (BigFppfOver.toScheme s.site s.base s.containsBase).map k :=
  map_comp_map_eq_of_comp_eq _ hy.1

/-- The comparison of the restrictions of Stacks 084A along `k`, to the point `g ∘ v` of `X`,
along the square `y ≫ π_W = π'_V ≫ k`: `y^*π_W^*(w^*𝒜)_n ≅ π'_V^*((g ∘ v)^*𝒜)_n`. -/
def baseChangeRestrictChainSchemeIso (n : ℤ) :=
  pullbackIsoOfSquare
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map (s.relativeProjPoints.fibreHom W w))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map
      ((s.pullback g).relativeProjPoints.fibreHom V v))
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map k)
    (s.toScheme_map_comp_fibreHom_of_liesOverAlong g k y hy)
    (M := (zariskiReadingQcoh W ((etalePointAlgebra (B := s.site) (S := s.base) (hS :=
        s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w
                n)).obj) (M' := (zariskiReadingQcoh V ((etalePointAlgebra (B := s.site) (S :=
                    s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n)).obj)
    (@asIso _ _ _ _ ((pointComparisonUnital (s := s.shrink) k w (v ≫ g.hom) hv).app n)
      (isIso_pointComparisonUnital_app (s := s.shrink) k w (v ≫ g.hom) hv n))

/-- The identification of the sources of `ψ` along `y` is the comparison of restrictions along
`k` followed by the inverse of the comparison `v^*(g^*𝒜) ≅ (g ∘ v)^*𝒜`. -/
theorem baseChangePieceChainSchemeIso_hom_eq (n : ℤ) :
    (s.baseChangePieceChainSchemeIso g k hv y hy n).hom =
      (pullbackIsoOfSquare (s.fibreToBase W w) ((s.pullback g).fibreToBase V v)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
        (s.fibreToBase_comp_of_liesOverAlong g k y hy)
        (M' := (s.shrink.pointAlgebra V (v ≫ g.hom)).piece n)
        (@asIso _ _ _ _ ((pointComparisonUnital (s := s.shrink) k w (v ≫ g.hom) hv).app n)
          (isIso_pointComparisonUnital_app (s := s.shrink) k w (v ≫ g.hom) hv n))).hom ≫
        (quasicoherentPullbackMap s.site s.base s.containsBase
            ((s.pullback g).relativeProjPoints.fibreHom V v)
            (ObjectProperty.homMk (@inv _ _ _ _ (((s.pullbackComapHom g).hom v).app n)
              ((s.pullbackComapHom g).isIso_hom_app v n)) :
              (zariskiReadingQcoh V ((etalePointAlgebra (B := s.site) (S := s.base) (hS :=
                  s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n)) ⟶ (s.pullback g).pointPieceQcoh V v n)).hom :=
  pullbackIsoOfSquare_trans_hom _ _ _ _ _ _ _

/-- The comparison of restrictions along `k`, in the two spellings of its base morphisms. -/
theorem isoMk_pullbackIsoOfSquare_eq_baseChangeRestrictChainSchemeIso (n : ℤ) :
    (ObjectProperty.isoMk _ (pullbackIsoOfSquare (s.fibreToBase W w)
        ((s.pullback g).fibreToBase V v)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
        (s.fibreToBase_comp_of_liesOverAlong g k y hy)
        (M' := (s.shrink.pointAlgebra V (v ≫ g.hom)).piece n)
        (@asIso _ _ _ _ ((pointComparisonUnital (s := s.shrink) k w (v ≫ g.hom) hv).app n)
          (isIso_pointComparisonUnital_app (s := s.shrink) k w (v ≫ g.hom) hv n))) :
        quasicoherentPullbackObj s.site s.base s.containsBase y
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W w) (zariskiReadingQcoh W ((etalePointAlgebra (B :=
                  s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w n))) ≅
          quasicoherentPullbackObj s.site s.base s.containsBase
            ((s.pullback g).relativeProjPoints.fibreHom V v) (zariskiReadingQcoh V
                ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n))) =
      (ObjectProperty.isoMk _ (s.baseChangeRestrictChainSchemeIso g k hv y hy n) :
        quasicoherentPullbackObj s.site s.base s.containsBase y
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W w) (zariskiReadingQcoh W ((etalePointAlgebra (B :=
                  s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w n))) ≅
          quasicoherentPullbackObj s.site s.base s.containsBase
            ((s.pullback g).relativeProjPoints.fibreHom V v) (zariskiReadingQcoh V
                ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n))) :=
  rfl


/-- The identification of the sources of `ψ` along `y`, with its base morphisms read through the
functor to schemes and its modules spelled as Zariski readings over the site of the situation. -/
theorem isoMk_baseChangePieceChainSchemeIso_eq_toScheme (n : ℤ) :
    (ObjectProperty.isoMk _ (s.baseChangePieceChainSchemeIso g k hv y hy n) :
        quasicoherentPullbackObj s.site s.base s.containsBase y
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W w) (zariskiReadingQcoh W ((etalePointAlgebra (B :=
                  s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w n))) ≅
                quasicoherentPullbackObj s.site s.base s.containsBase
                ((s.pullback g).relativeProjPoints.fibreHom V v) ((s.pullback g).pointPieceQcoh V v
                n)) =
      (ObjectProperty.isoMk _ (pullbackIsoOfSquare ((BigFppfOver.toScheme s.site s.base
          s.containsBase).map (s.relativeProjPoints.fibreHom W w))
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map
            ((s.pullback g).relativeProjPoints.fibreHom V v)) ((BigFppfOver.toScheme s.site s.base
            s.containsBase).map y) ((BigFppfOver.toScheme s.site s.base s.containsBase).map k)
        (s.toScheme_map_comp_fibreHom_of_liesOverAlong g k y hy)
        (M := (zariskiReadingQcoh W ((etalePointAlgebra (B := s.site) (S := s.base) (hS :=
        s.containsBase) (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w
                n)).obj) (M' := ((s.pullback g).pointPieceQcoh V v n).obj)
                    (Iso.trans (Y := (zariskiReadingQcoh V ((etalePointAlgebra (B := s.site)
                    (S := s.base) (hS :=
                s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n)).obj) (@asIso _ _ _ _ ((pointComparisonUnital (s := s.shrink) k w
                    (v ≫ g.hom) hv).app n)
          (isIso_pointComparisonUnital_app (s := s.shrink) k w (v ≫ g.hom) hv n) :
          (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map k)).obj
              (zariskiReadingQcoh W ((etalePointAlgebra (B := s.site) (S := s.base) (hS :=
        s.containsBase) (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w
                n)).obj ≅ (zariskiReadingQcoh V ((etalePointAlgebra (B := s.site) (S := s.base)
                    (hS :=
                s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n)).obj) ((@asIso _ _ _ _ (((s.pullbackComapHom g).hom v).app n)
              ((s.pullbackComapHom g).isIso_hom_app v n)).symm : (zariskiReadingQcoh V
                  ((etalePointAlgebra (B := s.site) (S := s.base) (hS :=
                s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n)).obj ≅ ((s.pullback g).pointPieceQcoh V v n).obj))) :
                    quasicoherentPullbackObj s.site s.base s.containsBase y
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W w) (zariskiReadingQcoh W ((etalePointAlgebra (B :=
                  s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w n))) ≅
                quasicoherentPullbackObj s.site s.base s.containsBase
                ((s.pullback g).relativeProjPoints.fibreHom V v) ((s.pullback g).pointPieceQcoh V v
                n)) :=
  rfl

/-- **The identification of the sources of `ψ` along `y`, split at the level of isomorphisms of
quasi-coherent modules**: the comparison of restrictions along `k` to the point `g ∘ v`, followed
by the pullback along `π'_V` of the inverse of the comparison `v^*(g^*𝒜) ≅ (g ∘ v)^*𝒜`. -/
theorem isoMk_baseChangePieceChainSchemeIso_eq_trans (n : ℤ) :
    (ObjectProperty.isoMk _ (s.baseChangePieceChainSchemeIso g k hv y hy n) :
        quasicoherentPullbackObj s.site s.base s.containsBase y
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W w) (zariskiReadingQcoh W ((etalePointAlgebra (B :=
                  s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w n))) ≅
                quasicoherentPullbackObj s.site s.base s.containsBase
                ((s.pullback g).relativeProjPoints.fibreHom V v) ((s.pullback g).pointPieceQcoh V v
                n)) =
      (ObjectProperty.isoMk _ (s.baseChangeRestrictChainSchemeIso g k hv y hy n) :
          quasicoherentPullbackObj s.site s.base s.containsBase y
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W w) (zariskiReadingQcoh W ((etalePointAlgebra (B :=
                  s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w n))) ≅
                quasicoherentPullbackObj s.site s.base s.containsBase
                ((s.pullback g).relativeProjPoints.fibreHom V v) (zariskiReadingQcoh V
                ((etalePointAlgebra (B := s.site) (S := s.base) (hS :=
                s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n))) ≪≫
        quasicoherentPullbackMapIso s.site s.base s.containsBase
            ((s.pullback g).relativeProjPoints.fibreHom V v) (ObjectProperty.isoMk _ (@asIso _ _ _ _
            (((s.pullbackComapHom g).hom v).app n)
              ((s.pullbackComapHom g).isIso_hom_app v n)).symm : zariskiReadingQcoh V
                  ((etalePointAlgebra (B := s.site) (S := s.base) (hS :=
                s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n) ≅ (s.pullback g).pointPieceQcoh V v n) :=
  (s.isoMk_baseChangePieceChainSchemeIso_eq_toScheme g k hv y hy n).trans
    (isoMk_eq_trans_of_hom_eq _ _ _ _
      (pullbackIsoOfSquare_trans_hom _ _ _ _ _ (@asIso _ _ _ _ ((pointComparisonUnital
          (s := s.shrink) k w (v ≫ g.hom) hv).app n)
          (isIso_pointComparisonUnital_app (s := s.shrink) k w (v ≫ g.hom) hv n) :
          (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map k)).obj
              (zariskiReadingQcoh W ((etalePointAlgebra (B := s.site) (S := s.base) (hS :=
        s.containsBase) (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w
                n)).obj ≅ (zariskiReadingQcoh V ((etalePointAlgebra (B := s.site) (S := s.base)
                    (hS :=
                s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n)).obj) ((@asIso _ _ _ _ (((s.pullbackComapHom g).hom v).app n)
              ((s.pullbackComapHom g).isIso_hom_app v n)).symm : (zariskiReadingQcoh V
                  ((etalePointAlgebra (B := s.site) (S := s.base) (hS :=
                s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n)).obj ≅ ((s.pullback g).pointPieceQcoh V v n).obj)) rfl)

include hy in
/-- A morphism of base changes lying over `k` and `P' ⟶ P`, followed by the base change
`W ×_X P ⟶ P` and `π`, is the structure morphism of `V ×_{X'} P'` followed by the point
`g ∘ v` of `X`. -/
theorem comp_homMk_fibreToSpace_comp_relativeProjSpaceHom :
    CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase)
        (CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase)
          (representedSpaceMap s.site s.base s.containsBase y)
          (ObjectProperty.homMk (s.relativeProjPoints.fibreToSpace W w) :
            (⟨yoneda.obj (s.relativeProjPoints.fibre W w), isAlgebraicSpace_yoneda s.site s.base
              s.containsBase (s.relativeProjPoints.fibre W w)⟩ :
                AlgebraicSpaces s.site s.base s.containsBase) ⟶
              ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩))
        s.relativeProjSpaceHom =
      CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase)
        (representedSpaceMap s.site s.base s.containsBase
          ((s.pullback g).relativeProjPoints.fibreHom V v))
        (pointHom (v ≫ g.hom)) :=
  ObjectProperty.hom_ext _ ((congrArg (· ≫ s.relativeProjπ) hy.2).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (s.relativeProjBaseChangeHom_comp_relativeProjπ g)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ g.hom) ((s.pullback g).relativeProjPoints.isPullback V v).w).trans
            (Category.assoc _ _ _))))))

/-- **The chart square of the source of `ψ` along a morphism of base changes over `g`**: for
`a : W ×_X P ⟶ P` over the point `w` (the base change, or the atlas of a presentation), the
identification `a^*π^*𝒜_n ≅ (π_W^*(w^*𝒜)_n)^a`, pulled back along `y`, followed by the comparison
of the restrictions along `k` to the point `g ∘ v`, is the contraction `y^*a^* ≅ (y ≫ a)^*`
followed by the identification along `y ≫ a` over the point `g ∘ v`
(`AlgebraicGeometry.Space.modulePullback_map_pointChainPullbackIso_hom_comp₂_eq`). -/
theorem modulePullback_map_pointChainPullbackIso_hom_comp₂_baseChange (n : ℤ)
    (a : (⟨yoneda.obj (s.relativeProjPoints.fibre W w), isAlgebraicSpace_yoneda s.site s.base
      s.containsBase (s.relativeProjPoints.fibre W w)⟩ :
        AlgebraicSpaces s.site s.base s.containsBase) ⟶
      ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩)
    (ha : CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase) a
        s.relativeProjSpaceHom =
      CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase)
        (representedSpaceMap s.site s.base s.containsBase (s.relativeProjPoints.fibreHom W w))
        (pointHom w))
    (σ : (modulePullback s.site s.base s.containsBase a).obj (s.psiSourceQcoh n).obj ≅
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
        (s.relativeProjPoints.fibre W w)).functor.obj
          (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom W w) (zariskiReadingQcoh W ((etalePointAlgebra (B :=
                s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w
                n)))).obj)
    (hσ : σ = pointChainPullbackIso s.relativeProjSpaceHom s.shrink.algebra
      s.shrink.isQuasicoherent a (s.relativeProjPoints.fibreHom W w) w ha n)
    (ht : CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase)
        (CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase)
          (representedSpaceMap s.site s.base s.containsBase y) a) s.relativeProjSpaceHom =
      CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase)
        (representedSpaceMap s.site s.base s.containsBase
          ((s.pullback g).relativeProjPoints.fibreHom V v))
        (pointHom (v ≫ g.hom))) :
    type_of% (modulePullback_map_pointChainPullbackIso_hom_comp₂_eq s.relativeProjSpaceHom
      s.shrink.algebra s.shrink.isQuasicoherent a (s.relativeProjPoints.fibreHom W w) w ha
      ((s.pullback g).relativeProjPoints.fibreHom V v) (v ≫ g.hom) n σ hσ k hv y hy.1
      (ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
        ((congrArg yoneda.map hy.1).trans (yoneda.map_comp _ _)))) ht
      (ObjectProperty.isoMk _ (s.baseChangeRestrictChainSchemeIso g k hv y hy n) :
        quasicoherentPullbackObj s.site s.base s.containsBase y
            (quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom W w) (zariskiReadingQcoh W ((etalePointAlgebra (B :=
                  s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w n))) ≅
          quasicoherentPullbackObj s.site s.base s.containsBase
            ((s.pullback g).relativeProjPoints.fibreHom V v)
            (zariskiReadingQcoh V ((etalePointAlgebra (B := s.site) (S := s.base) (hS :=
                s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n))).hom
      (isoMk_pullbackIsoOfSquare_hom_eq_comp₂ y (s.relativeProjPoints.fibreHom W w)
        ((s.pullback g).relativeProjPoints.fibreHom V v) k hy.1
        (s.toScheme_map_comp_fibreHom_of_liesOverAlong g k y hy) (zariskiReadingQcoh W
            ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra W w).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent w n))
        (zariskiReadingQcoh V ((etalePointAlgebra (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := s.space) s.shrink.algebra V (v ≫ g.hom)).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
            (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent (v ≫
                g.hom) n))
        (@asIso _ _ _ _ ((pointComparisonUnital (s := s.shrink) k w (v ≫ g.hom) hv).app n)
          (isIso_pointComparisonUnital_app (s := s.shrink) k w (v ≫ g.hom) hv n)) _
        (s.pointComparisonUnital_shrink_app_eq k hv n))) :=
  modulePullback_map_pointChainPullbackIso_hom_comp₂_eq s.relativeProjSpaceHom
      s.shrink.algebra s.shrink.isQuasicoherent a (s.relativeProjPoints.fibreHom W w) w ha
      ((s.pullback g).relativeProjPoints.fibreHom V v) (v ≫ g.hom) n σ hσ k hv y hy.1
      (ObjectProperty.hom_ext _ (map_comp_map_eq_of_comp_eq yoneda hy.1)) ht _
      (isoMk_pullbackIsoOfSquare_hom_eq_comp₂ y (s.relativeProjPoints.fibreHom W w)
        ((s.pullback g).relativeProjPoints.fibreHom V v) k hy.1
        (s.toScheme_map_comp_fibreHom_of_liesOverAlong g k y hy) _ _ _ _
        (s.asIso_pointComparisonUnital_shrink_app_hom k hv n))

end BaseChangeChain

/-! ### `ψ` at a scheme point of the base -/

section PointPsi

variable (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)

/-- The base change `T ×_X P ⟶ P` followed by `π` is the structure morphism of `T ×_X P` followed
by the point `f`. -/
theorem fibreToSpaceHom_comp_relativeProjSpaceHom :
    CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase)
        (s.fibreToSpaceHom T f) s.relativeProjSpaceHom =
      CategoryStruct.comp (obj := AlgebraicSpaces s.site s.base s.containsBase)
        (representedSpaceMap s.site s.base s.containsBase (s.relativeProjPoints.fibreHom T f))
        (pointHom f) :=
  ObjectProperty.hom_ext _ (s.relativeProjPoints.isPullback T f).w

/-- **The source of `ψ` restricted to a scheme point** (the analog at an arbitrary point `f` of
`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso`): the inverse image of `π^*𝒜_n`
along the base change `T ×_X P ⟶ P` is the module attached by Stacks 03DX (2) to `π_T^*(f^*𝒜)_n`,
for `π_T : T ×_X P ⟶ T` the structure morphism. -/
def fibrePsiSourceIso (n : ℤ) :
    (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).obj
        (s.psiSourceQcoh n).obj ≅
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
        (s.relativeProjPoints.fibre T f)).functor.obj
          (quasicoherentPullbackObj s.site s.base s.containsBase
            (s.relativeProjPoints.fibreHom T f) (zariskiReadingQcoh T ((etalePointAlgebra (B :=
                s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space) s.shrink.algebra T f).piece n)
              (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
                f n)))).obj :=
  pointChainPullbackIso s.relativeProjSpaceHom s.shrink.algebra s.shrink.isQuasicoherent
    (s.fibreToSpaceHom T f) (s.relativeProjPoints.fibreHom T f) f
    (s.fibreToSpaceHom_comp_relativeProjSpaceHom T f) n

/-- **Tag 01NR's `ψ` on `T ×_X P = Proj_T(f^*𝒜)`, as a morphism out of the restriction of
`π^*𝒜_n`**: the identification
`AlgebraicGeometry.Space.RelativeProjSituation.fibrePsiSourceIso` followed by the module attached
to `ψ` of Tag 01NR at the point `f` in adjoint form, `π_T^*(f^*𝒜)_n ⟶ 𝒪(n)`. -/
def fibrePsiHom (n : ℕ) :
    (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).obj
        (s.psiSourceQcoh (n : ℤ)).obj ⟶
      ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
        (s.relativeProjPoints.fibre T f)).functor.obj (s.twistPieceQcoh T f (n : ℤ))).obj :=
  (s.fibrePsiSourceIso T f (n : ℤ)).hom ≫
    ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      (s.relativeProjPoints.fibre T f)).functor.map
        (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint T f n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom T f) (zariskiReadingQcoh T ((etalePointAlgebra (B :=
                  s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space) s.shrink.algebra T f).piece (n : ℤ))
              (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
                f (n : ℤ))) ⟶
            s.twistPieceQcoh T f (n : ℤ))).hom

end PointPsi

section PointPsiCompat

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)


/-- The identification on the atlas of `T ×_X P` of the inverse image of `𝒪_P(n)`, as a
composite. -/
theorem pointPsi_presentationPullbackChartIso_hom (n : ℕ) :
    type_of% (presentationPullbackChartIso_hom (Presentation.ofIsoYoneda
        (RelativeProjPoints.spacePresentation
            (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f))
    (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.fibreToSpaceHom T f) (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
    (s.twistModule Px (n : ℤ)) (s.twistModuleChartIso Px (n : ℤ)) (s.chartTwistComparison
        (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f) (n : ℤ))) :=
  presentationPullbackChartIso_hom (Presentation.ofIsoYoneda (RelativeProjPoints.spacePresentation
            (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f))
    (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.fibreToSpaceHom T f) (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
    (s.twistModule Px (n : ℤ)) (s.twistModuleChartIso Px (n : ℤ)) (s.chartTwistComparison
        (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f) (n : ℤ))

/-- The identification along the square of the atlases is natural in `ψ_n`. -/
theorem pointPsi_pullbackSquareHom_naturality (n : ℕ) :
    type_of% (pullbackSquareHom_naturality (presentationAtlas (Presentation.ofIsoYoneda
        (RelativeProjPoints.spacePresentation
            (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f)))
    (presentationAtlas (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)) (s.fibreToSpaceHom T f)
    (representedSpaceMap s.site s.base s.containsBase (s.chartBaseChangeMap (s.schemePointHom T f)
        Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)))
                (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f) (s.psiTwistHom Px
                n)) :=
  pullbackSquareHom_naturality (presentationAtlas (Presentation.ofIsoYoneda
      (RelativeProjPoints.spacePresentation
            (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f)))
    (presentationAtlas (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)) (s.fibreToSpaceHom T f)
    (representedSpaceMap s.site s.base s.containsBase (s.chartBaseChangeMap (s.schemePointHom T f)
        Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)))
                (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f) (s.psiTwistHom Px n)

/-- `ψ_n` on the atlas of `P`, pulled back to the atlas of `T ×_X P`. -/
theorem pointPsi_chart_comp (n : ℕ) :
    type_of% (map_comp_map_eq_of_comp_eq
    (modulePullback s.site s.base s.containsBase (X := (presentationGroupoid
        (Presentation.ofIsoYoneda (RelativeProjPoints.spacePresentation
            (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f))).objects)
      (Y := (presentationGroupoid (s.relativeProjPoints.spacePresentation Px
          s.isAlgebraicSpace_relativeProjFunctor)).objects)
      (representedSpaceMap s.site s.base s.containsBase (s.chartBaseChangeMap (s.schemePointHom T f)
          Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))))
    (s.modulePullback_map_psiTwistHom_comp_twistModuleChartIso_hom Px n)) :=
  map_comp_map_eq_of_comp_eq
    (modulePullback s.site s.base s.containsBase (X := (presentationGroupoid
        (Presentation.ofIsoYoneda (RelativeProjPoints.spacePresentation
            (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f))).objects)
      (Y := (presentationGroupoid (s.relativeProjPoints.spacePresentation Px
          s.isAlgebraicSpace_relativeProjFunctor)).objects)
      (representedSpaceMap s.site s.base s.containsBase (s.chartBaseChangeMap (s.schemePointHom T f)
          Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))))
    (s.modulePullback_map_psiTwistHom_comp_twistModuleChartIso_hom Px n)

/-- Naturality of `y^*(M^a) ≅ (y^*M)^a` at `ψ` on the atlas of `P`. -/
theorem pointPsi_chart_naturality (n : ℕ) :
    type_of% (modulePullbackRepresentedQuasicoherentIso_naturality s.site s.base s.containsBase
    (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
    (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (n : ℤ)) ⟶
            s.twistPieceQcoh Px.U Px.toSpace (n : ℤ))) :=
  modulePullbackRepresentedQuasicoherentIso_naturality s.site s.base s.containsBase
    (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
    (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint Px.U Px.toSpace n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom Px.U Px.toSpace)
              (presentationPointPieceQcoh Px s.shrink.algebra s.shrink.isQuasicoherent (n : ℤ)) ⟶
            s.twistPieceQcoh Px.U Px.toSpace (n : ℤ))

/-- The `ψ`-square of the comparison of twists along the atlas map `T_U ×_T P' ⟶ U ×_X P`. -/
theorem pointPsi_chart_baseChange (n : ℕ) :
    type_of% (map_hom_comp_map_hom_eq_of_comp_eq_trans
    (representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      ((s.pullback (s.schemePointHom T f)).relativeProjPoints.fibre (Px.alongPoint f).U
          (Px.alongPoint f).toSpace)).functor
    (s.quasicoherentPullbackMap_psiChartSchemeHom_comp_baseChange (s.schemePointHom T f)
        (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f) (s.chartBaseChangeMap
        (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) n)
    (s.isoMk_baseChangePieceChainSchemeIso_eq_trans (s.schemePointHom T f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (s.chartBaseChangeMap (s.schemePointHom T f) Px
        (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) (n : ℤ))) :=
  map_hom_comp_map_hom_eq_of_comp_eq_trans
    (representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      ((s.pullback (s.schemePointHom T f)).relativeProjPoints.fibre (Px.alongPoint f).U
          (Px.alongPoint f).toSpace)).functor
    (s.quasicoherentPullbackMap_psiChartSchemeHom_comp_baseChange (s.schemePointHom T f)
        (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f) (s.chartBaseChangeMap
        (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) n)
    (s.isoMk_baseChangePieceChainSchemeIso_eq_trans (s.schemePointHom T f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (s.chartBaseChangeMap (s.schemePointHom T f) Px
        (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) (n : ℤ))

/-- The square of the source of `ψ` along the atlas map `T_U ×_T P' ⟶ U ×_X P`. -/
theorem pointPsi_chart_source (n : ℕ) :
    type_of% (s.modulePullback_map_pointChainPullbackIso_hom_comp₂_baseChange (s.schemePointHom T f)
        (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
    (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) (n : ℤ)
                (presentationAtlas (s.relativeProjPoints.spacePresentation Px
                s.isAlgebraicSpace_relativeProjFunctor))
    (s.relativeProjPoints.presentationAtlas_comp_homMk Px s.isAlgebraicSpace_relativeProjFunctor)
    (s.psiChartSourceIso Px (n : ℤ)) rfl
    (s.comp_homMk_fibreToSpace_comp_relativeProjSpaceHom (s.schemePointHom T f)
        (Px.alongPointToAtlas f) (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)))) :=
  s.modulePullback_map_pointChainPullbackIso_hom_comp₂_baseChange (s.schemePointHom T f)
      (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
    (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) (n : ℤ)
                (presentationAtlas (s.relativeProjPoints.spacePresentation Px
                s.isAlgebraicSpace_relativeProjFunctor))
    (s.relativeProjPoints.presentationAtlas_comp_homMk Px s.isAlgebraicSpace_relativeProjFunctor)
    (s.psiChartSourceIso Px (n : ℤ)) rfl
    (s.comp_homMk_fibreToSpace_comp_relativeProjSpaceHom (s.schemePointHom T f)
        (Px.alongPointToAtlas f) (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)))

/-- The identification along the square of the atlases at `π^*𝒜_n`, as a composite. -/
theorem pointPsi_pullbackSquareHom_eq_comp (n : ℕ) :
    type_of% (pullbackSquareHom_eq_comp (presentationAtlas (Presentation.ofIsoYoneda
        (RelativeProjPoints.spacePresentation
            (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f)))
    (presentationAtlas (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)) (s.fibreToSpaceHom T f)
    (representedSpaceMap s.site s.base s.containsBase (s.chartBaseChangeMap (s.schemePointHom T f)
        Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)))
                (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f) (s.psiSourceQcoh
                (n : ℤ)).obj) :=
  pullbackSquareHom_eq_comp (presentationAtlas (Presentation.ofIsoYoneda
      (RelativeProjPoints.spacePresentation
            (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f)))
    (presentationAtlas (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)) (s.fibreToSpaceHom T f)
    (representedSpaceMap s.site s.base s.containsBase (s.chartBaseChangeMap (s.schemePointHom T f)
        Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)))
                (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f) (s.psiSourceQcoh
                (n : ℤ)).obj

/-- The inverse comparison of Stacks 03LU followed by the comparison, at `π^*𝒜_n`. -/
theorem pointPsi_compInv_comp_compHom (n : ℕ) :
    type_of% (modulePullbackCompInv_comp_compHom s.site s.base s.containsBase
    (representedSpaceMap s.site s.base s.containsBase (s.chartBaseChangeMap (s.schemePointHom T f)
        Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))) (presentationAtlas
                (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))
    (s.psiSourceQcoh (n : ℤ)).obj) :=
  modulePullbackCompInv_comp_compHom s.site s.base s.containsBase
    (representedSpaceMap s.site s.base s.containsBase (s.chartBaseChangeMap (s.schemePointHom T f)
        Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))) (presentationAtlas
                (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))
    (s.psiSourceQcoh (n : ℤ)).obj

/-- The square of the source of `ψ` along `T_U ×_T P' ⟶ T ×_X P`, with the point of `T_U` written
as the chart of the atlas of `T` (the spelling of the squares along `T_U ×_T P' ⟶ U ×_X P`). -/
theorem pointPsi_point_source (n : ℕ) :
    type_of% (s.modulePullback_map_pointChainPullbackIso_hom_comp₂_baseChange (s.schemePointHom T f)
        (V := Px.alongPointChart f) (v := (Px.alongPoint f).toSpace)
      (Px.alongPointToPoint f) rfl
    (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f) (n : ℤ) (s.fibreToSpaceHom T f)
        (s.fibreToSpaceHom_comp_relativeProjSpaceHom T f)
    (s.fibrePsiSourceIso T f (n : ℤ)) rfl
    (s.comp_homMk_fibreToSpace_comp_relativeProjSpaceHom (s.schemePointHom T f)
        (Px.alongPointToPoint f) (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T
        f))) :=
  s.modulePullback_map_pointChainPullbackIso_hom_comp₂_baseChange (s.schemePointHom T f)
      (V := Px.alongPointChart f) (v := (Px.alongPoint f).toSpace)
      (Px.alongPointToPoint f) rfl
    (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f) (n : ℤ) (s.fibreToSpaceHom T f)
        (s.fibreToSpaceHom_comp_relativeProjSpaceHom T f)
    (s.fibrePsiSourceIso T f (n : ℤ)) rfl
    (s.comp_homMk_fibreToSpace_comp_relativeProjSpaceHom (s.schemePointHom T f)
        (Px.alongPointToPoint f) (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f))

/-- The transport along the square of the atlases, followed by the comparisons of Stacks 03LU. -/
theorem pointPsi_transport (n : ℕ) :
    type_of% (pullbackTransport_comp_modulePullbackCompIso_hom_app_of_eq s.relativeProjSpaceHom
        (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
    (s.comp_homMk_fibreToSpace_comp_relativeProjSpaceHom (s.schemePointHom T f)
        (Px.alongPointToAtlas f) (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)))
    (s.shrink.algebra.piece (n : ℤ))) :=
  pullbackTransport_comp_modulePullbackCompIso_hom_app_of_eq s.relativeProjSpaceHom
      (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
    (s.comp_homMk_fibreToSpace_comp_relativeProjSpaceHom (s.schemePointHom T f)
        (Px.alongPointToAtlas f) (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
                (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)))
    (s.shrink.algebra.piece (n : ℤ))

/-- The identification on the atlas of `𝒪(n)^a`, as a composite. -/
theorem pointPsi_ofIsoYonedaChartIso_hom (n : ℕ) :
    type_of% (Iso.trans_hom (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
      (s.pointChartMap Px T f) (s.twistPieceQcoh T f (n : ℤ)))
    ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence s.site s.base
      s.containsBase _).functor.mapIso (s.pointChartTwistComparison Px T f (n : ℤ))))) :=
  Iso.trans_hom (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
      (s.pointChartMap Px T f) (s.twistPieceQcoh T f (n : ℤ)))
    ((ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence s.site s.base
      s.containsBase _).functor.mapIso (s.pointChartTwistComparison Px T f (n : ℤ))))

/-- Naturality of `y^*(M^a) ≅ (y^*M)^a` at `ψ` on `T ×_X P`. -/
theorem pointPsi_point_naturality (n : ℕ) :
    type_of% (modulePullbackRepresentedQuasicoherentIso_naturality s.site s.base s.containsBase
    (s.pointChartMap Px T f)
    (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint T f n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom T f) (zariskiReadingQcoh T ((etalePointAlgebra (B :=
                  s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space) s.shrink.algebra T f).piece (n : ℤ))
              (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
                f (n : ℤ))) ⟶
            s.twistPieceQcoh T f (n : ℤ))) :=
  modulePullbackRepresentedQuasicoherentIso_naturality s.site s.base s.containsBase
    (s.pointChartMap Px T f)
    (ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint T f n) :
          quasicoherentPullbackObj s.site s.base s.containsBase
              (s.relativeProjPoints.fibreHom T f) (zariskiReadingQcoh T ((etalePointAlgebra (B :=
                  s.site) (S := s.base)
              (hS := s.containsBase) (X := s.space) s.shrink.algebra T f).piece (n : ℤ))
              (isQuasicoherentOnSite_etalePointAlgebra_piece (B := s.site) (S := s.base)
                (hS := s.containsBase) (X := s.space) s.shrink.algebra s.shrink.isQuasicoherent
                f (n : ℤ))) ⟶
            s.twistPieceQcoh T f (n : ℤ))

/-- The `ψ`-square of the comparison of twists along `T_U ×_T P' ⟶ T ×_X P`, with the point of
`T_U` written as the chart of the atlas of `T` (the spelling of the squares along
`T_U ×_T P' ⟶ U ×_X P`). -/
theorem pointPsi_point_baseChange (n : ℕ) :
    type_of% (map_hom_comp_map_hom_eq_of_comp_eq_trans
    (representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      ((s.pullback (s.schemePointHom T f)).relativeProjPoints.fibre (Px.alongPoint f).U
          (Px.alongPoint f).toSpace)).functor
    (s.quasicoherentPullbackMap_psiChartSchemeHom_comp_baseChange (s.schemePointHom T f)
        (V := Px.alongPointChart f) (v := (Px.alongPoint f).toSpace)
      (Px.alongPointToPoint f) rfl (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f)
          n)
    (s.isoMk_baseChangePieceChainSchemeIso_eq_trans (s.schemePointHom T f) (V := Px.alongPointChart
        f) (v := (Px.alongPoint f).toSpace)
      (Px.alongPointToPoint f) rfl (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f)
          (n : ℤ))) :=
  map_hom_comp_map_hom_eq_of_comp_eq_trans
    (representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
      ((s.pullback (s.schemePointHom T f)).relativeProjPoints.fibre (Px.alongPoint f).U
          (Px.alongPoint f).toSpace)).functor
    (s.quasicoherentPullbackMap_psiChartSchemeHom_comp_baseChange (s.schemePointHom T f)
        (V := Px.alongPointChart f) (v := (Px.alongPoint f).toSpace)
      (Px.alongPointToPoint f) rfl (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f)
          n)
    (s.isoMk_baseChangePieceChainSchemeIso_eq_trans (s.schemePointHom T f) (V := Px.alongPointChart
        f) (v := (Px.alongPoint f).toSpace)
      (Px.alongPointToPoint f) rfl (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f)
          (n : ℤ))

end PointPsiCompat

end RelativeProjSituation

end AlgebraicGeometry.Space

end
