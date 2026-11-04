module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangePsi
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.DegreeZero

/-!
# The base change map on the higher direct images of the twists of a projective bundle

Let `g : S' ⟶ S` be a morphism of schemes, `E` a quasi-coherent `𝒪_S`-module, `E' ≅ g^*E`, and
`b : 𝐏(E') ⟶ 𝐏(E)` the morphism of projective bundles over `g`, so that the square of `b`, `g`
and the two projections is cartesian. The base change map of higher direct images followed by the
identification `b^* 𝒪_{𝐏(E)}(d) ⟶ 𝒪_{𝐏(E')}(d)` of the twists is the base change map

`g^* R^q π_* 𝒪_{𝐏(E)}(d) ⟶ R^q π'_* 𝒪_{𝐏(E')}(d)`.

In degree zero, under `R⁰π_* 𝒪(d) = Sym^d(E)`, it is the identification
`g^* Sym^d(E) = Sym^d(E')`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaSharp`: `b^* 𝒪(d) ⟶ 𝒪'(d)`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.twistBaseChange`: the base change map on
  the higher direct images of the twists.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.twistBaseChange_zeroIso`: the base change
  map in degree zero is `g^* Sym^d(E) = Sym^d(E')`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) (E' : S'.Modules) [E'.IsQuasicoherent]
  (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))
  (D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc'))

/-- **The identification of the twists along the base change of the projective bundle**,
`b^* 𝒪_{𝐏(E)}(d) ⟶ 𝒪_{𝐏(E')}(d)`, adjoint to `θ♭`. -/
public def thetaSharp (d : ℤ) :
    (Scheme.Modules.pullback (bundleBaseChange g E hqc E' hqc' hE)).obj (D.algebra.piece d) ⟶
      D'.algebra.piece d :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (bundleBaseChange g E hqc E' hqc' hE)).homEquiv
    _ _).symm (thetaFlat g E hqc E' hqc' hE D D' d)

/-- **The base change map on the higher direct images of the twists**:
`g^* R^q π_* 𝒪_{𝐏(E)}(d) ⟶ R^q π'_*(b^* 𝒪_{𝐏(E)}(d)) ⟶ R^q π'_* 𝒪_{𝐏(E')}(d)`. -/
public def twistBaseChange (q : ℕ) (d : ℤ) :
    (Scheme.Modules.pullback g).obj (((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
          (q : ℤ)).obj (D.algebra.piece d)) ⟶
      ((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).rightDerivedPlus
          (q : ℤ)).obj (D'.algebra.piece d) :=
  Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.higherBaseChange
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) q
      (D.algebra.piece d) ≫
    ((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase).rightDerivedPlus
          (q : ℤ)).map (thetaSharp g E hqc E' hqc' hE D D' d)

/-- The base change map on the twists, in adjoint form, is the base change map attached to `θ♭`. -/
public theorem homEquiv_twistBaseChange (q : ℕ) (d : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        (twistBaseChange g E hqc E' hqc' hE D D' q d) =
      Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pairBaseChange
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
        (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
        (thetaFlat g E hqc E' hqc' hE D D' d) q := by
  have hθ : (Scheme.Modules.pullbackPushforwardAdjunction
        (bundleBaseChange g E hqc E' hqc' hE)).unit.app
        (D.algebra.piece d) ≫ (Scheme.Modules.pushforward (bundleBaseChange g E hqc E' hqc' hE)).map
          (thetaSharp g E hqc E' hqc' hE D D' d) = thetaFlat g E hqc E' hqc' hE D D' d :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  refine ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans ?_
  refine (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pairBaseChange_comp_map _ _ _ _ _
    _ _ q).symm.trans ?_
  exact congrArg (fun φ => Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pairBaseChange
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
        (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE) φ q) hθ

/-- The algebra of the degree-zero row: a composite rearranged along two commuting relations and
two pairs of inverse isomorphisms. -/
public theorem row_zero_aux {C C' : Type*} [Category C] [Category C'] (G : C' ⥤ C)
    {P F₀ Sd : C} {X P' F₀' Sd' : C'} (pBC : P ⟶ G.obj P') (rI : F₀ ⟶ P) (rH : P ⟶ F₀)
    (hr : rH ≫ rI = 𝟙 P) (m : F₀ ⟶ G.obj F₀') (rI' : F₀' ⟶ P') (rH' : P' ⟶ F₀')
    (hr' : rI' ≫ rH' = 𝟙 F₀') (ψ : Sd ⟶ F₀) [IsIso ψ] (ψ' : Sd' ⟶ F₀') [IsIso ψ']
    (η : Sd ⟶ G.obj X) (Φ : X ⟶ Sd') (h₀ : rI ≫ pBC = m ≫ G.map rI')
    (key : ψ ≫ m = η ≫ G.map (Φ ≫ ψ')) :
    pBC ≫ G.map (rH' ≫ inv ψ') = (rH ≫ inv ψ) ≫ η ≫ G.map Φ := by
  have hp : pBC = rH ≫ m ≫ G.map rI' := by
    rw [← h₀, ← Category.assoc, hr, Category.id_comp]
  have hm : m ≫ G.map (inv ψ') = inv ψ ≫ η ≫ G.map Φ := by
    rw [← cancel_epi ψ, IsIso.hom_inv_id_assoc, ← Category.assoc, key, Category.assoc,
      ← G.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hp, Category.assoc, Category.assoc, ← G.map_comp, ← Category.assoc rI', hr',
    Category.id_comp, hm]
  exact (Category.assoc _ _ _).symm

/-- The identification `R⁰π_* 𝒪(d) ≅ Sym^d(E)`, unfolded. -/
public theorem zeroIso_hom {n : ℕ} (hn : 0 < n)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) (d : ℕ) :
    haveI := isIso_psi E hqc D hn hfree d
    (zeroIso E hqc D hn hfree d).hom =
      (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase)).hom.app
          (D.algebra.piece (d : ℤ)) ≫ inv (D.ψ d) := rfl

/-- **The base change map on the twists in degree zero is `g^* Sym^d(E) = Sym^d(E')`**: under
the identifications `R⁰π_* 𝒪(d) ≅ Sym^d(E)` and `R⁰π'_* 𝒪'(d) ≅ Sym^d(E')`, for `n ≥ 1` and
`d ≥ 0`. -/
public theorem twistBaseChange_zeroIso {n : ℕ} (hn : 0 < n)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
    (hfree' : Scheme.Modules.IsFiniteLocallyFreeOfRank E' (n + 1)) (d : ℕ) :
    twistBaseChange g E hqc E' hqc' hE D D' 0 (d : ℤ) ≫ (zeroIso E' hqc' D' hn hfree' d).hom =
      (Scheme.Modules.pullback g).map (zeroIso E hqc D hn hfree d).hom ≫
        (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (d : ℤ) := by
  have := isIso_psi E hqc D hn hfree d
  have := isIso_psi E' hqc' D' hn hfree' d
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  rw [zeroIso_hom, zeroIso_hom]
  refine ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (· ≫ _) (homEquiv_twistBaseChange g E hqc E' hqc' hE D D' 0 (d : ℤ))).trans ?_
  refine Eq.trans ?_
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_left _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Adjunction.homEquiv_unit _ _ _ _).symm)
  have h₀ := HigherDirectImageBaseChange.rightDerivedPlusZeroIso_inv_comp_pairBaseChange
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
      (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
      (thetaFlat g E hqc E' hqc' hE D D' (d : ℤ))
  have hr := Iso.hom_inv_id_app (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
    (Scheme.Modules.pushforward
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase))
    (D.algebra.piece (d : ℤ))
  have hr' := Iso.inv_hom_id_app (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
    (Scheme.Modules.pushforward
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase))
    (D'.algebra.piece (d : ℤ))
  refine row_zero_aux (Scheme.Modules.pushforward g) _ _ _ hr
    ((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).map
        (thetaFlat g E hqc E' hqc' hE D D' (d : ℤ)) ≫
      (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
        (bundleBaseChange g E hqc E' hqc' hE)
        (bundleBaseChange_toBase g E hqc E' hqc' hE)).hom.app (D'.algebra.piece (d : ℤ)))
    _ _ hr' (D.ψ d) (D'.ψ d)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (d : ℤ)))
    ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (d : ℤ)) ?_ ?_
  · exact h₀.trans (Category.assoc _ _ _).symm
  · exact psi_comp_thetaFlat g E hqc E' hqc' hE D D' d

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
