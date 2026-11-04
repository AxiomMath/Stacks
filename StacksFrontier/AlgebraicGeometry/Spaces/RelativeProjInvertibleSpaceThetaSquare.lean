module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceThetaChartMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceTheta
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartScheme

/-!
# Clause (3) of Stacks 0D2Z for `θ` on an algebraic space: `θ'` is the pullback of `θ`

Let `f : X ⟶ Y` be a morphism of algebraic spaces towards the algebraic space `Y` of
Situation 0849, `ℒ` an invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of
graded algebras on the small étale site of `X`, with the open subspace `U(ψ) ⊆ X` and the map
`θ : r^*𝒪(d) ⟶ ℒ^{⊗ d}|_{U(ψ)}` of [Stacks, Tag 0D2Z] descended from the chart maps
(`…InvertibleTwistingRestriction.descendedTheta`).  The last sentence of clause (3) of the tag
reads: for a commutative square `g ∘ f' = f ∘ g'` with `g' : X' ⟶ X`, `f' : X' ⟶ Y'`,
`g : Y' ⟶ Y` and `X'`, `Y'` schemes, `𝒜' = g^*𝒜`, `ℒ' = (g')^*ℒ` and `ψ'` the pullback of `ψ`,
the map `θ'` of [Stacks, Tag 01O9] for `ψ'` is the pullback of `θ`.

This file proves it.  The restriction of `θ` to a scheme point `w : T ⟶ U(ψ)` is `θ` of
Tag 01O9 for `w^*ψ` on `T` (`…modulePullback_map_pointHom_descendedTheta`).  For `w` lying over a
test scheme `t : T ⟶ X'` of `U(ψ') = (g')^{-1}(U(ψ))`, both that map and the pullback `k^*θ'` along
the lift `k : T ⟶ U(ψ')` are compared with `θ` of Tag 01O9 for `(g')^*ψ` over `X'`: `θ'` by
clause (3) at a scheme point of the base for the square `X' = X' ⟶ Y'`
(`…RelativeProjSituation.invertibleTheta_baseChange_square`), the map at `g' ∘ t` by its
compatibility along `t` (`…InvertibleTwistingRestriction.theta_map_eq_pullback`).  The two
inverse images of `θ_{(g')^*ψ}` along `T ⟶ U(ψ') ⟶ U((g')^*ψ)` and along
`T ⟶ U((g' ∘ t)^*ψ) ⟶ U(t^*(g')^*ψ) ⟶ U((g')^*ψ)` agree through the pseudofunctoriality of the
inverse image (`AlgebraicGeometry.Space.pullback_map_eq_of_chain`).

## Main definitions

* `…InvertibleTwistingRestriction.squarePointSourceIso`,
  `…InvertibleTwistingRestriction.squarePointTargetIso`: the identifications of the sources and of
  the targets of `k^*θ'` and of `θ` at `g' ∘ t`.
* `…InvertibleTwistingRestriction.squarePointChartTheta`: `k^*θ'` read between the source and the
  target of `…chartSchemeTheta` at `g' ∘ t`.

## Main results

* `…InvertibleTwistingRestriction.chartTheta_eq_pullback_squarePsi_theta`: `θ` of Tag 01O9 at the
  scheme point `g' ∘ t` is `k^*θ'`, for any restriction datum.
* `…InvertibleTwistingRestriction.modulePullback_map_pointHom_descendedTheta_square`: **`θ'` is the
  pullback of `θ`**: for every test scheme `T ⟶ U(ψ')`, the restrictions of `θ` and of `θ'` to `T`
  agree through canonical identifications.
* `…InvertibleTwistingRestriction.modulePullback_map_squarePsiLocusPoint_descendedTheta`: the same
  for the scheme `U(ψ')` itself, along the restriction `U(ψ') ⟶ U(ψ)` of `g'`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.RingedSpace

universe u m

namespace AlgebraicGeometry.Space

section ChainComparison

variable {T U' U₀ Ut Usq : Scheme.{u}} (k : T ⟶ U') (e₁ : U' ⟶ U₀) (cl : T ⟶ Ut)
  (h : Ut ⟶ Usq) (e₂ : Usq ⟶ U₀) (hk : k ≫ e₁ = cl ≫ h ≫ e₂)

/-- The comparison `k^*(e₁^*M) ≅ (k ≫ e₁)^*M = (cl ≫ h ≫ e₂)^*M ≅ cl^*(h^*(e₂^*M))` of the
pseudofunctoriality of the inverse image of modules on schemes. -/
def pullbackChainIso (M : U₀.Modules) :
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback e₁).obj M) ≅
      (Scheme.Modules.pullback cl).obj
        ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback e₂).obj M)) :=
  (Scheme.Modules.pullbackComp k e₁).app M ≪≫ (Scheme.Modules.pullbackCongr hk).app M ≪≫
    ((Scheme.Modules.pullbackComp cl (h ≫ e₂)).app M).symm ≪≫
    (Scheme.Modules.pullback cl).mapIso ((Scheme.Modules.pullbackComp h e₂).app M).symm

/-- `pullbackChainIso` is natural in the module. -/
theorem pullbackChainIso_hom_naturality {M N : U₀.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback e₁).map φ) ≫
        (pullbackChainIso k e₁ cl h e₂ hk N).hom =
      (pullbackChainIso k e₁ cl h e₂ hk M).hom ≫
        (Scheme.Modules.pullback cl).map ((Scheme.Modules.pullback h).map
          ((Scheme.Modules.pullback e₂).map φ)) :=
  pullback_comp_naturality_of_eq k e₁ cl h e₂ hk φ

end ChainComparison

section PieceChain

variable {T U' U₀ Ut Usq : Scheme.{u}} (k : T ⟶ U') (e₁ : U' ⟶ U₀) (cl : T ⟶ Ut)
  (h : Ut ⟶ Usq) (e₂ : Usq ⟶ U₀) (hk : k ≫ e₁ = cl ≫ h ≫ e₂)
  {M : U₀.Modules} {S' : U'.Modules} {M₂ : Usq.Modules} {St : Ut.Modules}

/-- The identification `k^*S' ≅ cl^*S` of a module `S' ≅ e₁^*M` on `U'` and a module
`S ≅ h^*M₂`, `M₂ ≅ e₂^*M`, on `U_t`, through the comparison `k^*e₁^* ≅ cl^*h^*e₂^*` of the inverse
images along `k ≫ e₁ = cl ≫ h ≫ e₂`. -/
def pullbackChainTransportIso (E : (Scheme.Modules.pullback e₁).obj M ≅ S')
    (B : (Scheme.Modules.pullback e₂).obj M ≅ M₂) (A : (Scheme.Modules.pullback h).obj M₂ ≅ St) :
    (Scheme.Modules.pullback k).obj S' ≅ (Scheme.Modules.pullback cl).obj St :=
  (Scheme.Modules.pullback k).mapIso E.symm ≪≫ pullbackChainIso k e₁ cl h e₂ hk M ≪≫
    (Scheme.Modules.pullback cl).mapIso ((Scheme.Modules.pullback h).mapIso B ≪≫ A)

/-- **Two maps obtained from one map `φ` by inverse images along two chains
`k ≫ e₁ = cl ≫ h ≫ e₂` agree after pulling back to `T`**: if `φ' = E⁻¹ ≫ e₁^*φ ≫ G` on `U'` and
`φ_t = A⁻¹ ≫ h^*(B⁻¹ ≫ e₂^*φ ≫ C) ≫ D` on `U_t`, then `cl^*φ_t` is `k^*φ'` read through
`pullbackChainTransportIso` on the sources and on the targets. -/
theorem pullback_map_eq_of_chain {N : U₀.Modules} {Q' : U'.Modules} {N₂ : Usq.Modules}
    {Qt : Ut.Modules} (φ : M ⟶ N) (E : (Scheme.Modules.pullback e₁).obj M ≅ S')
    (G : (Scheme.Modules.pullback e₁).obj N ≅ Q') (φ' : S' ⟶ Q')
    (hφ' : φ' = E.inv ≫ (Scheme.Modules.pullback e₁).map φ ≫ G.hom)
    (B : (Scheme.Modules.pullback e₂).obj M ≅ M₂) (C : (Scheme.Modules.pullback e₂).obj N ≅ N₂)
    (A : (Scheme.Modules.pullback h).obj M₂ ≅ St) (D : (Scheme.Modules.pullback h).obj N₂ ≅ Qt)
    (φt : St ⟶ Qt)
    (hφt : φt = A.inv ≫ (Scheme.Modules.pullback h).map
      (B.inv ≫ (Scheme.Modules.pullback e₂).map φ ≫ C.hom) ≫ D.hom) :
    (Scheme.Modules.pullback cl).map φt =
      (pullbackChainTransportIso k e₁ cl h e₂ hk E B A).inv ≫
        (Scheme.Modules.pullback k).map φ' ≫
        (pullbackChainTransportIso k e₁ cl h e₂ hk G C D).hom := by
  subst hφ' hφt
  have hn := pullbackChainIso_hom_naturality k e₁ cl h e₂ hk φ
  simp only [pullbackChainTransportIso, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.symm_inv, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Iso.map_hom_inv_id_assoc]
  rw [reassoc_of% hn, Iso.inv_hom_id_assoc]

end PieceChain

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open SheafOfModules.GradedAlgebra (pieceIsoOfIso)
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)

variable {s : RelativeProjSituation.{u, m}}
  {X : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {f : X ⟶ s.space.1}
  (R : s.InvertibleTwistingRestriction f)
  {X' Y' T : BigFppfOver s.site s.base s.containsBase} (g' : yoneda.obj X' ⟶ X) (f' : X' ⟶ Y')
  (g : yoneda.obj Y' ⟶ s.space.1) (hsq : yoneda.map f' ≫ g = g' ≫ f) (t : T ⟶ X')

/-- The restriction `U(ψ') ⟶ U(g'^*ψ)` of the identity of `X'`, for the pullback `ψ'` of `ψ` to
the square `g ∘ f' = f ∘ g'` (`U(ψ') = U(g'^*ψ)`). -/
abbrev squarePsiRestrict :
    (toGradedPowerMap (R.squarePsi g' f' g hsq)).coveringOpen.toScheme ⟶
      (toGradedPowerMap (R.twisting X' g')).coveringOpen.toScheme :=
  Scheme.Hom.resLE ((BigFppfOver.toScheme s.site s.base s.containsBase).map (𝟙 X'))
    (toGradedPowerMap (R.twisting X' g')).coveringOpen
    (toGradedPowerMap (R.squarePsi g' f' g hsq)).coveringOpen
    (s.quadrupleRestriction.coveringOpen_squareTwisting s.shrink.contains_relativeProj_pointAlgebra
      s.shrink.space.property.isSheaf (R.twisting X' g') g f' (𝟙 X') (square_id g' f' g hsq)).le

/-- The restriction `U(t^*(g'^*ψ)) ⟶ U(g'^*ψ)` of `t : T ⟶ X'`. -/
abbrev squarePointRestrict :
    (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting X' g')
      ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t
      (yoneda_map_id_comp_assoc s f t g'))).coveringOpen.toScheme ⟶
      (toGradedPowerMap (R.twisting X' g')).coveringOpen.toScheme :=
  Scheme.Hom.resLE ((BigFppfOver.toScheme s.site s.base s.containsBase).map t)
    (toGradedPowerMap (R.twisting X' g')).coveringOpen
    (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting X' g')
      ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t (yoneda_map_id_comp_assoc s f t g'))).coveringOpen
    (s.quadrupleRestriction.coveringOpen_squareTwisting s.shrink.contains_relativeProj_pointAlgebra
      s.shrink.space.property.isSheaf (R.twisting X' g') ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t
      (yoneda_map_id_comp_assoc s f t g')).le

variable (hx : R.locusOpen T (yoneda.map t ≫ g') = ⊤)
  (k : (BigFppfOver.toScheme s.site s.base s.containsBase).obj T ⟶
    (toGradedPowerMap (R.squarePsi g' f' g hsq)).coveringOpen.toScheme)
  (hk : k ≫ (toGradedPowerMap (R.squarePsi g' f' g hsq)).coveringOpen.ι =
    (BigFppfOver.toScheme s.site s.base s.containsBase).map t)

include hk in
/-- The two ways from `T` to `U(g'^*ψ)`: through `U(ψ')` and through the chart lift
`T ⟶ U((g' ∘ t)^*ψ) ⊆ U(t^*(g'^*ψ))`. -/
theorem squarePsiRestrict_comp_eq :
    k ≫ R.squarePsiRestrict g' f' g hsq =
      R.chartLift (yoneda.map t ≫ g') hx ≫
        Scheme.homOfLE ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)
          (R.coveringOpen_twisting_map_le t g') ≫ R.squarePointRestrict g' t := by
  refine (cancel_mono (toGradedPowerMap (R.twisting X' g')).coveringOpen.ι).1 ?_
  have h₁ : (k ≫ R.squarePsiRestrict g' f' g hsq) ≫
      (toGradedPowerMap (R.twisting X' g')).coveringOpen.ι =
      (BigFppfOver.toScheme s.site s.base s.containsBase).map t :=
    (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (Scheme.Hom.resLE_comp_ι _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hk).trans
        ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ X')).trans (Category.comp_id _)))))
  have h₂ : (R.chartLift (yoneda.map t ≫ g') hx ≫
        Scheme.homOfLE ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)
          (R.coveringOpen_twisting_map_le t g') ≫ R.squarePointRestrict g' t) ≫
        (toGradedPowerMap (R.twisting X' g')).coveringOpen.ι =
      (BigFppfOver.toScheme s.site s.base s.containsBase).map t := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (Scheme.Hom.resLE_comp_ι _ _)))).trans ?_
    refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (Scheme.homOfLE_ι _ _)))).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (R.chartLift_ι (yoneda.map t ≫ g') hx)).trans (Category.id_comp _))
  exact h₁.trans h₂.symm

/-- **`k^*r_{ψ'}^*𝒪_{Y'}(d) ≅ c^*r_{x}^*𝒪(d)`** for a test scheme `t : T ⟶ X'` of `U(ψ')` with
lift `k : T ⟶ U(ψ')` and the scheme point `x = g' ∘ t` of `U(ψ)` with chart lift
`c : T ⟶ U(x^*ψ)`: the identification of the sources of `θ'` of [Stacks, Tag 01O9] for `ψ'` over
`Y'` and of `θ` for `x^*ψ` over `T`, both compared with the source of `θ` for `g'^*ψ` over `X'`
(`…squareThetaSourceIso` for the squares `X' = X' ⟶ Y'` and `T ⟶ X' = X'`, and the transport
`…thetaTransportSourceIso` along `x^*ψ = t^*(g'^*ψ)`). -/
def squarePointSourceIso (d : ℤ) :
    (Scheme.Modules.pullback k).obj ((Stacks.Conormal.gradedPullback
        ((toGradedPowerMap (R.squarePsi g' f' g hsq)).globalMorphism
          (relativeProj (s.relativeProjPoints.algebra Y' g)))
        (GradedPowerMap.twD (s.relativeProjPoints.algebra Y' g)).algebra).piece d) ≅
      (Scheme.Modules.pullback (R.chartLift (yoneda.map t ≫ g') hx)).obj
        ((Stacks.Conormal.gradedPullback
          ((toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).globalMorphism
            (relativeProj (s.relativeProjPoints.algebra T ((yoneda.map t ≫ g') ≫ f))))
          (GradedPowerMap.twD (s.relativeProjPoints.algebra T
              ((yoneda.map t ≫ g') ≫ f))).algebra).piece d) :=
  pullbackChainTransportIso (M := (Stacks.Conormal.gradedPullback
      ((toGradedPowerMap (R.twisting X' g')).globalMorphism
        (relativeProj (s.relativeProjPoints.algebra X' (g' ≫ f))))
      (GradedPowerMap.twD (s.relativeProjPoints.algebra X' (g' ≫ f))).algebra).piece d)
    k (R.squarePsiRestrict g' f' g hsq) (R.chartLift (yoneda.map t ≫ g') hx)
    (Scheme.homOfLE ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)
      (R.coveringOpen_twisting_map_le t g')) (R.squarePointRestrict g' t)
    (R.squarePsiRestrict_comp_eq g' f' g hsq t hx k hk)
    (pieceIsoOfIso (s.quadrupleRestriction.squareThetaSourceIso
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
      (R.twisting X' g') g f'
      (𝟙 X') (square_id g' f' g hsq)) d)
    (pieceIsoOfIso (s.quadrupleRestriction.squareThetaSourceIso
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting X' g')
      ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t (yoneda_map_id_comp_assoc s f t g')) d)
    (pieceIsoOfIso ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting X' g')
      ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t
      (yoneda_map_id_comp_assoc s f t g'))).thetaTransportSourceIso
      (R.coveringOpen_twisting_map_le t g')
      (homOfLE_globalMorphism_of_eq_congrBase_congrModule (CategoryTheory.Functor.map_id _ T) _
        (R.lineIso t g') _ (R.twisting_map t g'))) d)

/-- `squarePointSourceIso`, written out. -/
theorem squarePointSourceIso_eq (d : ℤ) :
    R.squarePointSourceIso g' f' g hsq t hx k hk d =
    pullbackChainTransportIso (M := (Stacks.Conormal.gradedPullback
        ((toGradedPowerMap (R.twisting X' g')).globalMorphism
          (relativeProj (s.relativeProjPoints.algebra X' (g' ≫ f))))
        (GradedPowerMap.twD (s.relativeProjPoints.algebra X' (g' ≫ f))).algebra).piece d)
      k (R.squarePsiRestrict g' f' g hsq) (R.chartLift (yoneda.map t ≫ g') hx)
      (Scheme.homOfLE ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)
        (R.coveringOpen_twisting_map_le t g')) (R.squarePointRestrict g' t)
      (R.squarePsiRestrict_comp_eq g' f' g hsq t hx k hk)
      (pieceIsoOfIso (s.quadrupleRestriction.squareThetaSourceIso
        s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
        (R.twisting X' g') g f'
        (𝟙 X') (square_id g' f' g hsq)) d)
      (pieceIsoOfIso (s.quadrupleRestriction.squareThetaSourceIso
        s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
        (R.twisting X' g')
        ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t (yoneda_map_id_comp_assoc s f t g')) d)
      (pieceIsoOfIso ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
        s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
        (R.twisting X' g')
        ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t
        (yoneda_map_id_comp_assoc s f t g'))).thetaTransportSourceIso
        (R.coveringOpen_twisting_map_le t g')
        (homOfLE_globalMorphism_of_eq_congrBase_congrModule (CategoryTheory.Functor.map_id _ T) _
          (R.lineIso t g') _ (R.twisting_map t g'))) d) :=
  rfl

/-- **`k^*((g'^*ℒ)^{⊗ d}|_{U(ψ')}) ≅ c^*((x^*ℒ)^{⊗ d}|_{U(x^*ψ)})`**, the identification of the
targets of `θ'` and of `θ` for `x^*ψ`, assembled as `squarePointSourceIso` is
(`…squareThetaTargetIso`, and `…thetaTransportTargetIso` for `t^*(g'^*ℒ) ≅ (g' ∘ t)^*ℒ`). -/
def squarePointTargetIso (d : ℤ) :
    (Scheme.Modules.pullback k).obj ((laurentOn (toGradedPowerMap (R.squarePsi g' f' g hsq)).L
        (toGradedPowerMap (R.squarePsi g' f' g hsq)).coveringOpen).piece d) ≅
      (Scheme.Modules.pullback (R.chartLift (yoneda.map t ≫ g') hx)).obj
        ((laurentOn (toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).L
          (toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).coveringOpen).piece d) :=
  pullbackChainTransportIso (M := (laurentOn (toGradedPowerMap (R.twisting X' g')).L
      (toGradedPowerMap (R.twisting X' g')).coveringOpen).piece d)
    k (R.squarePsiRestrict g' f' g hsq) (R.chartLift (yoneda.map t ≫ g') hx)
    (Scheme.homOfLE ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)
      (R.coveringOpen_twisting_map_le t g')) (R.squarePointRestrict g' t)
    (R.squarePsiRestrict_comp_eq g' f' g hsq t hx k hk)
    (pieceIsoOfIso (s.quadrupleRestriction.squareThetaTargetIso
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
      (R.twisting X' g') g f'
      (𝟙 X') (square_id g' f' g hsq)) d)
    (pieceIsoOfIso (s.quadrupleRestriction.squareThetaTargetIso
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting X' g')
      ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t (yoneda_map_id_comp_assoc s f t g')) d)
    (pieceIsoOfIso ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting X' g')
      ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t
      (yoneda_map_id_comp_assoc s f t g'))).thetaTransportTargetIso
      (R.lineIso t g') (R.coveringOpen_twisting_map_le t g')) d)

/-- `squarePointTargetIso`, written out. -/
theorem squarePointTargetIso_eq (d : ℤ) :
    R.squarePointTargetIso g' f' g hsq t hx k hk d =
    pullbackChainTransportIso (M := (laurentOn (toGradedPowerMap (R.twisting X' g')).L
        (toGradedPowerMap (R.twisting X' g')).coveringOpen).piece d)
      k (R.squarePsiRestrict g' f' g hsq) (R.chartLift (yoneda.map t ≫ g') hx)
      (Scheme.homOfLE ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)
        (R.coveringOpen_twisting_map_le t g')) (R.squarePointRestrict g' t)
      (R.squarePsiRestrict_comp_eq g' f' g hsq t hx k hk)
      (pieceIsoOfIso (s.quadrupleRestriction.squareThetaTargetIso
        s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
        (R.twisting X' g') g f'
        (𝟙 X') (square_id g' f' g hsq)) d)
      (pieceIsoOfIso (s.quadrupleRestriction.squareThetaTargetIso
        s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
        (R.twisting X' g')
        ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t (yoneda_map_id_comp_assoc s f t g')) d)
      (pieceIsoOfIso ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
        s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
        (R.twisting X' g')
        ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t
        (yoneda_map_id_comp_assoc s f t g'))).thetaTransportTargetIso
        (R.lineIso t g') (R.coveringOpen_twisting_map_le t g')) d) :=
  rfl

/-- **`θ` at the scheme point `g' ∘ t` is the pullback of `θ'`**: for a test scheme `t : T ⟶ X'`
of `U(ψ')` with lift `k : T ⟶ U(ψ')`, the map `θ` of [Stacks, Tag 01O9] for `(g' ∘ t)^*ψ`, read on
`T` (`…chartTheta`), is the inverse image `k^*θ'` of the map `θ'` for `ψ'` over `Y'`, through
`squarePointSourceIso` and `squarePointTargetIso`. -/
theorem chartTheta_eq_pullback_squarePsi_theta (d : ℤ) :
    R.chartTheta (yoneda.map t ≫ g') hx d =
      (Scheme.Modules.pullbackComp (R.chartLift (yoneda.map t ≫ g') hx)
          ((toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).globalMorphism
            (relativeProj (s.relativeProjPoints.algebra T ((yoneda.map t ≫ g') ≫ f))))).inv.app
          ((GradedPowerMap.twD (s.relativeProjPoints.algebra T
              ((yoneda.map t ≫ g') ≫ f))).algebra.piece d) ≫
        ((R.squarePointSourceIso g' f' g hsq t hx k hk d).inv ≫
          (Scheme.Modules.pullback k).map
            ((toGradedPowerMap (R.squarePsi g' f' g hsq)).theta.app d) ≫
          (R.squarePointTargetIso g' f' g hsq t hx k hk d).hom) ≫
        ((toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).laurentOnSectionPieceIso
          (R.chartLift (yoneda.map t ≫ g') hx) (R.chartLift_ι (yoneda.map t ≫ g') hx) d).hom := by
  have key := pullback_map_eq_of_chain (S' := (Stacks.Conormal.gradedPullback
      ((toGradedPowerMap (R.squarePsi g' f' g hsq)).globalMorphism
        (relativeProj (s.relativeProjPoints.algebra Y' g)))
      (GradedPowerMap.twD (s.relativeProjPoints.algebra Y' g)).algebra).piece d)
    (Q' := (laurentOn (toGradedPowerMap (R.squarePsi g' f' g hsq)).L
      (toGradedPowerMap (R.squarePsi g' f' g hsq)).coveringOpen).piece d)
    (St := (Stacks.Conormal.gradedPullback
      ((toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).globalMorphism
        (relativeProj (s.relativeProjPoints.algebra T ((yoneda.map t ≫ g') ≫ f))))
      (GradedPowerMap.twD (s.relativeProjPoints.algebra T
          ((yoneda.map t ≫ g') ≫ f))).algebra).piece d)
    (Qt := (laurentOn (toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).L
      (toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).coveringOpen).piece d)
    k (R.squarePsiRestrict g' f' g hsq)
    (R.chartLift (yoneda.map t ≫ g') hx)
    (Scheme.homOfLE ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)
      (R.coveringOpen_twisting_map_le t g')) (R.squarePointRestrict g' t)
    (R.squarePsiRestrict_comp_eq g' f' g hsq t hx k hk)
    ((toGradedPowerMap (R.twisting X' g')).theta.app d)
    (pieceIsoOfIso (s.quadrupleRestriction.squareThetaSourceIso
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
      (R.twisting X' g') g f'
      (𝟙 X') (square_id g' f' g hsq)) d)
    (pieceIsoOfIso (s.quadrupleRestriction.squareThetaTargetIso
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
      (R.twisting X' g') g f'
      (𝟙 X') (square_id g' f' g hsq)) d)
    ((toGradedPowerMap (R.squarePsi g' f' g hsq)).theta.app d)
    ((congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ d)
      (s.invertibleTheta_baseChange_square (R.twisting X' g') g f' (𝟙 X')
        (square_id g' f' g hsq))).trans rfl)
    (pieceIsoOfIso (s.quadrupleRestriction.squareThetaSourceIso
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting X' g')
      ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t (yoneda_map_id_comp_assoc s f t g')) d)
    (pieceIsoOfIso (s.quadrupleRestriction.squareThetaTargetIso
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting X' g')
      ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t (yoneda_map_id_comp_assoc s f t g')) d)
    (pieceIsoOfIso ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting X' g')
      ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t
      (yoneda_map_id_comp_assoc s f t g'))).thetaTransportSourceIso
      (R.coveringOpen_twisting_map_le t g')
      (homOfLE_globalMorphism_of_eq_congrBase_congrModule (CategoryTheory.Functor.map_id _ T) _
        (R.lineIso t g') _ (R.twisting_map t g'))) d)
    (pieceIsoOfIso ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting X' g')
      ((yoneda.map t ≫ g') ≫ f) (𝟙 T) t
      (yoneda_map_id_comp_assoc s f t g'))).thetaTransportTargetIso
      (R.lineIso t g') (R.coveringOpen_twisting_map_le t g')) d)
    ((toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).theta.app d)
    (app_eq_comp_pullback_map_app _ _ _ _ _ _ _ _ (R.theta_map_eq_pullback t g') d)
  have e₁ := GradedPowerMap.thetaOnSection_eq (toGradedPowerMap (R.twisting T (yoneda.map t ≫ g')))
    (R.chartLift (yoneda.map t ≫ g') hx) (R.chartLift_ι (yoneda.map t ≫ g') hx) d
  have key' : (Scheme.Modules.pullback (R.chartLift (yoneda.map t ≫ g') hx)).map
      ((toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).theta.app d) =
      (R.squarePointSourceIso g' f' g hsq t hx k hk d).inv ≫
        (Scheme.Modules.pullback k).map ((toGradedPowerMap (R.squarePsi g' f' g hsq)).theta.app d) ≫
        (R.squarePointTargetIso g' f' g hsq t hx k hk d).hom := by
    rw [squarePointSourceIso_eq, squarePointTargetIso_eq]
    exact key
  exact e₁.trans (congrArg (fun φ =>
    (Scheme.Modules.pullbackComp (R.chartLift (yoneda.map t ≫ g') hx)
      ((toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).globalMorphism
        (relativeProj (s.relativeProjPoints.algebra T ((yoneda.map t ≫ g') ≫ f))))).inv.app
          ((GradedPowerMap.twD (s.relativeProjPoints.algebra T
              ((yoneda.map t ≫ g') ≫ f))).algebra.piece d) ≫ φ ≫
      ((toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).laurentOnSectionPieceIso
        (R.chartLift (yoneda.map t ≫ g') hx) (R.chartLift_ι (yoneda.map t ≫ g') hx) d).hom) key')

/-- **`θ'` read at the scheme point `g' ∘ t` of `U(ψ)`**, in degree `d`, in the shape of
`…chartTheta`: the inverse image `k^*θ'` along the lift `k : T ⟶ U(ψ')` of the map `θ'` of
[Stacks, Tag 01O9] for `ψ'` over `Y'`, between `r_{g' ∘ t}^*𝒪(d)` and `((g' ∘ t)^*ℒ)^{⊗ d}`,
through the contraction along the chart lift, `squarePointSourceIso`, `squarePointTargetIso` and
`…laurentOnSectionPieceIso`. -/
def squarePointTheta (d : ℤ) :
    (Scheme.Modules.pullback (R.chartMorphism (yoneda.map t ≫ g') hx)).obj
        ((GradedPowerMap.twD (s.relativeProjPoints.algebra T
            ((yoneda.map t ≫ g') ≫ f))).algebra.piece d) ⟶
      Stacks.AmpleProjectiveImmersion.tensorPowerModule _ (R.line T (yoneda.map t ≫ g')) d :=
  (Scheme.Modules.pullbackComp (R.chartLift (yoneda.map t ≫ g') hx)
      ((toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).globalMorphism
        (relativeProj (s.relativeProjPoints.algebra T ((yoneda.map t ≫ g') ≫ f))))).inv.app
      ((GradedPowerMap.twD (s.relativeProjPoints.algebra T
          ((yoneda.map t ≫ g') ≫ f))).algebra.piece d) ≫
    ((R.squarePointSourceIso g' f' g hsq t hx k hk d).inv ≫
      (Scheme.Modules.pullback k).map ((toGradedPowerMap (R.squarePsi g' f' g hsq)).theta.app d) ≫
      (R.squarePointTargetIso g' f' g hsq t hx k hk d).hom) ≫
    ((toGradedPowerMap (R.twisting T (yoneda.map t ≫ g'))).laurentOnSectionPieceIso
      (R.chartLift (yoneda.map t ≫ g') hx) (R.chartLift_ι (yoneda.map t ≫ g') hx) d).hom

/-- `…chartTheta` at `g' ∘ t` is `squarePointTheta`. -/
theorem chartTheta_eq_squarePointTheta (d : ℤ) :
    R.chartTheta (yoneda.map t ≫ g') hx d = R.squarePointTheta g' f' g hsq t hx k hk d :=
  R.chartTheta_eq_pullback_squarePsi_theta g' f' g hsq t hx k hk d

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective


variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  {X' Y' T : BigFppfOver s.site s.base s.containsBase} (g' : yoneda.obj X' ⟶ X.1) (f' : X' ⟶ Y')
  (g : yoneda.obj Y' ⟶ s.space.1) (hsq : yoneda.map f' ≫ g = g' ≫ f.hom) (t : T ⟶ X')
  (hx : (ofUnitalHom s f L ψ).locusOpen T (yoneda.map t ≫ g') = ⊤)
  (k : (BigFppfOver.toScheme s.site s.base s.containsBase).obj T ⟶
    (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).coveringOpen.toScheme)
  (hk : k ≫ (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).coveringOpen.ι =
    (BigFppfOver.toScheme s.site s.base s.containsBase).map t)

/-- **`θ'` read at the scheme point `g' ∘ t` of `U(ψ)`, as a map of quasi-coherent modules on
`T`**: for a test scheme `t : T ⟶ X'` of `U(ψ')` with lift `k : T ⟶ U(ψ')`, the inverse image
`k^*θ'` of the degree-`d` part of the map `θ'` of [Stacks, Tag 01O9] for the pullback `ψ'` of `ψ`
over `Y'`, read between the source and target of `…chartSchemeTheta` at `g' ∘ t`: the
contraction `c^*(t'^*𝒪(d)) ≅ (c ≫ t')^*𝒪(d)`, the transport along `c ≫ t' = r_{g' ∘ t}`, the
contraction along the chart lift, `squarePointSourceIso` and, on the targets,
`squarePointTargetIso` and `…laurentOnSectionPieceIso`. -/
def squarePointChartTheta (d : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection (yoneda.map t ≫ g') hx)
        (s.twistPieceQcoh T ((yoneda.map t ≫ g') ≫ f.hom) d) ⟶
      pointLaurentPieceQcoh L T (yoneda.map t ≫ g') d :=
  ObjectProperty.homMk
    ((Scheme.Modules.pullbackComp _ _).hom.app _ ≫
      (Scheme.Modules.pullbackCongr
        (toScheme_map_chartSection_toRelativeProj s f L ψ (yoneda.map t ≫ g') hx)).hom.app _ ≫
      (ofUnitalHom s f L ψ).squarePointTheta g' f' g hsq t hx k hk d)

/-- Two morphisms `u`, `v` of a full subcategory with defining equations
`u = homMk (a ≫ b ≫ θ₁)` and `v = homMk (a ≫ b ≫ θ₂)` are equal once `θ₁ = θ₂`.  Instantiated at
the defining equations of two maps, it compares their values factor by factor, with the shared
factors `a`, `b` read off the first equation. -/
theorem eq_of_eq_homMk_comp_comp_of_eq {C : Type*} [Category C] {P : ObjectProperty C}
    {A B : P.FullSubcategory} {Y Z : C} {a : A.obj ⟶ Y} {b : Y ⟶ Z} {θ₁ θ₂ : Z ⟶ B.obj}
    {u v : A ⟶ B} (hu : u = ObjectProperty.homMk (a ≫ b ≫ θ₁))
    (hv : v = ObjectProperty.homMk (a ≫ b ≫ θ₂)) (h : θ₁ = θ₂) : u = v := by
  rw [hu, hv, h]

/-- **`θ` of the chart maps at the scheme point `g' ∘ t` is `θ'` read at `g' ∘ t`.**  The defining
equations of `…chartSchemeTheta` and of `squarePointChartTheta` are matched against
`eq_of_eq_homMk_comp_comp_of_eq`, so that their values are compared factor by factor rather than
by unfolding both. -/
theorem chartSchemeTheta_eq_squarePointChartTheta (d : ℤ) :
    chartSchemeTheta s f L ψ (yoneda.map t ≫ g') hx d =
      squarePointChartTheta s f L ψ g' f' g hsq t hx k hk d :=
  eq_of_eq_homMk_comp_comp_of_eq (chartSchemeTheta.eq_1 s f L ψ (yoneda.map t ≫ g') hx d)
    (squarePointChartTheta.eq_1 s f L ψ g' f' g hsq t hx k hk d)
    ((ofUnitalHom s f L ψ).chartTheta_eq_squarePointTheta g' f' g hsq t hx k hk d)

/-- The source of `…chartSchemeTheta` at equal scheme points. -/
theorem chartSchemeThetaSource_congr {W : BigFppfOver s.site s.base s.containsBase}
    {x x' : yoneda.obj W ⟶ X.1} (h : x = x') (hx : (ofUnitalHom s f L ψ).locusOpen W x = ⊤)
    (hx' : (ofUnitalHom s f L ψ).locusOpen W x' = ⊤) (d : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x hx) (s.twistPieceQcoh W (x ≫ f.hom) d) =
      quasicoherentPullbackObj s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x' hx') (s.twistPieceQcoh W (x' ≫ f.hom) d) := by
  subst h
  rfl

/-- **`…chartSchemeTheta` at equal scheme points**, through the equalities of its sources and of
its targets. -/
theorem chartSchemeTheta_congr {W : BigFppfOver s.site s.base s.containsBase}
    {x x' : yoneda.obj W ⟶ X.1} (h : x = x') (hx : (ofUnitalHom s f L ψ).locusOpen W x = ⊤)
    (hx' : (ofUnitalHom s f L ψ).locusOpen W x' = ⊤) (d : ℤ) :
    chartSchemeTheta s f L ψ x' hx' d =
      eqToHom (chartSchemeThetaSource_congr s f L ψ h hx hx' d).symm ≫
        chartSchemeTheta s f L ψ x hx d ≫
        eqToHom (congrArg (fun z => pointLaurentPieceQcoh L W z d) h) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

variable {s : RelativeProjSituation.{u, m}}
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} {f : X ⟶ s.shrink.space}
  {L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O)}
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  {ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L)}
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (P : Presentation s.shrink.site s.shrink.base s.shrink.containsBase
    (locusSpaceOfUnitalHom s f L ψ).obj (locusSpaceOfUnitalHom s f L ψ).property)
  {X' Y' : BigFppfOver s.site s.base s.containsBase} (g' : yoneda.obj X' ⟶ X.1) (f' : X' ⟶ Y')
  (g : yoneda.obj Y' ⟶ s.space.1) (hsq : yoneda.map f' ≫ g = g' ≫ f.hom)

/-- A scheme point `w` of `U(ψ)` lying over `t : T ⟶ X'` (`g' ∘ t = w`) puts `g' ∘ t` in `U(ψ)`. -/
theorem locusOpen_comp_eq_top_of_eq {T : BigFppfOver s.shrink.site s.shrink.base
    s.shrink.containsBase}
    (t : T ⟶ X') (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)
    (hw : yoneda.map t ≫ g' = locusPoint w) :
    (ofUnitalHom s f L ψ).locusOpen T (yoneda.map t ≫ g') = ⊤ :=
  hw ▸ locusOpen_locusPoint w

/-- **The last assertion of clause (3) of [Stacks, Tag 0D2Z] for `θ` on the algebraic space
`U(ψ)`: `θ'` is the pullback of `θ`.**  Consider a commutative square `g ∘ f' = f ∘ g'` with
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `g : Y' ⟶ Y` and `X'`, `Y'` schemes, and let `ψ'` be the pullback
of `ψ` (`…InvertibleTwistingRestriction.squarePsi`, over `Y'` for `𝒜' = g^*𝒜` and
`ℒ' = (g')^*ℒ`) with the map `θ'` of [Stacks, Tag 01O9] on `U(ψ') = (g')^{-1}(U(ψ))`.  Then for
    every
test scheme `t : T ⟶ X'` of `U(ψ')`, with lift `k : T ⟶ U(ψ')`, and the point `w : T ⟶ U(ψ)` over
it (`g' ∘ t = w`), the pullback along `w` of the degree-`d` part of `θ` on `U(ψ)`
(`…InvertibleTwistingRestriction.descendedTheta`) is the pullback `k^*θ'` of the degree-`d` part
of `θ'`, read through the canonical identifications of the sources
(`…chartSourceIso`, `…squarePointSourceIso`) and of the targets (`…squarePointTargetIso`,
`…chartTargetIso`): the restrictions of `θ` and of `θ'` to every scheme `T ⟶ U(ψ')` agree, and
`U(ψ')` itself is such a scheme. -/
theorem modulePullback_map_pointHom_descendedTheta_square (d : ℤ)
    {T : BigFppfOver s.shrink.site s.shrink.base s.shrink.containsBase} (t : T ⟶ X')
    (w : yoneda.obj T ⟶ (locusSpaceOfUnitalHom s f L ψ).obj)
    (hw : yoneda.map t ≫ g' = locusPoint w)
    (k : (BigFppfOver.toScheme s.site s.base s.containsBase).obj T ⟶
      (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).coveringOpen.toScheme)
    (hk : k ≫ (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).coveringOpen.ι =
      (BigFppfOver.toScheme s.site s.base s.containsBase).map t) :
    (modulePullback s.shrink.site s.shrink.base s.shrink.containsBase (pointHom w)).map
        (descendedTheta Px P d) =
      (chartSourceIso Px w (locusOpen_locusPoint w) d).hom ≫
        ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
            s.shrink.containsBase T).functor.map
          (eqToHom (chartSchemeThetaSource_congr s f L ψ hw
              (locusOpen_comp_eq_top_of_eq g' t w hw) (locusOpen_locusPoint w) d).symm ≫
            squarePointChartTheta s f L ψ g' f' g hsq t (locusOpen_comp_eq_top_of_eq g' t w hw)
              k hk d ≫
            eqToHom (congrArg (fun z => pointLaurentPieceQcoh L T z d) hw))).hom ≫
        (chartTargetIso w d).hom := by
  have e₁ := chartSchemeTheta_congr s f L ψ hw (locusOpen_comp_eq_top_of_eq g' t w hw)
    (locusOpen_locusPoint w) d
  have e₂ := chartSchemeTheta_eq_squarePointChartTheta s f L ψ g' f' g hsq t
    (locusOpen_comp_eq_top_of_eq g' t w hw) k hk d
  have e₃ := e₁.trans (congrArg (fun φ => eqToHom (chartSchemeThetaSource_congr s f L ψ hw
      (locusOpen_comp_eq_top_of_eq g' t w hw) (locusOpen_locusPoint w) d).symm ≫ φ ≫
        eqToHom (congrArg (fun z => pointLaurentPieceQcoh L T z d) hw)) e₂)
  refine (modulePullback_map_pointHom_descendedTheta Px P d w).trans ?_
  exact congrArg (fun φ => (chartSourceIso Px w (locusOpen_locusPoint w) d).hom ≫
    ((representedQuasicoherentSchemeEquivalence s.shrink.site s.shrink.base
      s.shrink.containsBase T).functor.map φ).hom ≫ (chartTargetIso w d).hom) e₃

/-- The open subscheme `U(ψ') ⊆ X'`, as an object of the site. -/
abbrev squarePsiLocusObject : BigFppfOver s.site s.base s.containsBase :=
  openSiteObject s.site s.base s.containsBase X'
    (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).coveringOpen

/-- The inclusion `U(ψ') ⟶ X'`, as a morphism of the site. -/
abbrev squarePsiLocusInclusion : squarePsiLocusObject g' f' g hsq (L := L) (ψ := ψ) ⟶ X' :=
  openSiteObjectHom s.site s.base s.containsBase X'
    (toGradedPowerMap ((ofUnitalHom s f L ψ).squarePsi g' f' g hsq)).coveringOpen

/-- `U(ψ') ⊆ X'` maps into `U(ψ)` along `g'`. -/
theorem mem_locus_squarePsiLocusInclusion :
    yonedaEquiv (yoneda.map (squarePsiLocusInclusion g' f' g hsq (L := L) (ψ := ψ)) ≫ g') ∈
      (ofUnitalHom s f L ψ).locus.obj (Opposite.op (squarePsiLocusObject g' f' g hsq (L := L)
        (ψ := ψ))) := by
  refine ((ofUnitalHom s f L ψ).mem_locus_iff _).2
    (((ofUnitalHom s f L ψ).locusOpen_map (squarePsiLocusInclusion g' f' g hsq) g').trans ?_)
  have key : ∀ {Z : Scheme.{u}} (U V : Z.Opens), U = V → U.ι ⁻¹ᵁ V = ⊤ := by
    rintro _ U _ rfl
    exact Scheme.Opens.ι_preimage_self U
  exact key _ _ ((ofUnitalHom s f L ψ).coveringOpen_squarePsi g' f' g hsq)

/-- **The restriction `U(ψ') ⟶ U(ψ)` of `g'`**, as a scheme point of `U(ψ)`. -/
abbrev squarePsiLocusPoint :
    yoneda.obj (squarePsiLocusObject g' f' g hsq (L := L) (ψ := ψ)) ⟶
      (locusSpaceOfUnitalHom s f L ψ).obj :=
  (ofUnitalHom s f L ψ).factor _ (mem_locus_squarePsiLocusInclusion g' f' g hsq)

/-- The scheme point `U(ψ') ⟶ U(ψ)` lies over the inclusion `U(ψ') ⊆ X'`. -/
theorem locusPoint_squarePsiLocusPoint :
    yoneda.map (squarePsiLocusInclusion g' f' g hsq (L := L) (ψ := ψ)) ≫ g' =
      locusPoint (squarePsiLocusPoint g' f' g hsq (L := L) (ψ := ψ)) :=
  ((congrArg (fun a => yonedaEquiv.symm (Subtype.val a)) (Equiv.apply_symm_apply yonedaEquiv
      _)).trans
    (Equiv.symm_apply_apply yonedaEquiv _)).symm

/-- **The last assertion of clause (3) of [Stacks, Tag 0D2Z] for `θ` on the algebraic space
`U(ψ)`, along `U(ψ') ⟶ U(ψ)`: `θ'` is the pullback of `θ`.**  For a commutative square
`g ∘ f' = f ∘ g'` with `X'`, `Y'` schemes and `ψ'` the pullback of `ψ`, the pullback of the
degree-`d` part of `θ` on `U(ψ)` along the restriction `U(ψ') ⟶ U(ψ)` of `g'` is the degree-`d`
part of the map `θ'` of [Stacks, Tag 01O9] on `U(ψ')` (read along the identity of `U(ψ')`),
through the canonical identifications of the sources and of the targets:
`modulePullback_map_pointHom_descendedTheta_square` at the scheme `U(ψ')` itself. -/
theorem modulePullback_map_squarePsiLocusPoint_descendedTheta (d : ℤ) :
    type_of% (modulePullback_map_pointHom_descendedTheta_square Px P g' f' g hsq d
      (squarePsiLocusInclusion g' f' g hsq) (squarePsiLocusPoint g' f' g hsq)
      (locusPoint_squarePsiLocusPoint g' f' g hsq) (𝟙 _) (Category.id_comp _)) :=
  modulePullback_map_pointHom_descendedTheta_square Px P g' f' g hsq d
    (squarePsiLocusInclusion g' f' g hsq) (squarePsiLocusPoint g' f' g hsq)
    (locusPoint_squarePsiLocusPoint g' f' g hsq) (𝟙 _) (Category.id_comp _)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
