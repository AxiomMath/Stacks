module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeBaseChange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothGroupFirstCohomologyTorsion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SmoothProductProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.RestrictionAlongContinuousFirstCohomology

/-!
# First fppf cohomology of an abelian scheme over a regular surface is torsion

Let `S` be a scheme, `G → S` an abelian scheme and `X → S` a morphism from a two dimensional
regular integral Noetherian scheme `X`. Then the first cohomology group `H¹(X, G)` of the big
fppf site over `S`, at the object `X`, is torsion. This is the step of the proof of Stacks 0AFB
which combines Stacks 0AF9 and Stacks 0AFA ("each `A₀`-torsor over `X` is torsion").

The cohomology here is that of the big fppf site *over `S`*, evaluated at `X`, while Stacks 0AF9
(`AlgebraicGeometry.fppfH1_restriction_genericPoint_injective_of_dim_two`) is a statement about
the big fppf site over `X` and Stacks 0AFA (`AlgebraicGeometry.Space.fppfH1_isAddTorsion`) one
about the big fppf site over the function field `K` of `X`. The two are connected by restriction
along postcomposition `Over.map`, which carries the points sheaf of `G` to the points sheaf of the
base change of `G` (`AlgebraicGeometry.restrictionPointsSheafIso`), and by the injective
comparison of first cohomology along a continuous functor
(`Stacks.Cohomology.ContinuousRestriction.restrictH1_injective`), which is natural in the object.

The argument: restriction `H¹(X, G) → H¹(Spec K, G)` on the site over `S` is injective, because
after comparison with the site over `X` it is the injective map of Stacks 0AF9; and
`H¹(Spec K, G)` on the site over `S` injects into `H¹` of the site over `Spec K`, which is
torsion by Stacks 0AFA, since `G_K` is a smooth commutative group scheme over `K`.

## Main results

* `AlgebraicGeometry.restrictionPointsSheafIso`: the points sheaf of `G` restricted along
  `X → S` is the points sheaf of `G ×_S X`.
* `AlgebraicGeometry.isAddTorsion_H1_pointsSheaf_of_field`: Stacks 0AFA for the points sheaf of
  a smooth commutative group scheme over a field, at the final object.
* `AlgebraicGeometry.isAddTorsion_H1_pointsSheaf_of_isRegular`: **`H¹(X, G)` is torsion.**

## References

* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
* [Stacks Project, Tag 0AFA](https://stacks.math.columbia.edu/tag/0AFA)
* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

universe w u

namespace AlgebraicGeometry

open Stacks.Cohomology.ContinuousRestriction

/-- An abelian group admitting an injective homomorphism into a torsion group is torsion. -/
private theorem isAddTorsion_of_injective {A A' : Type*} [AddCommGroup A] [AddCommGroup A']
    (φ : A →+ A') (hφ : Function.Injective φ) (hA' : IsAddTorsion A') : IsAddTorsion A :=
  fun a => by
    obtain ⟨n, hn, h⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hA' (φ a))
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hφ (by rw [map_nsmul, h, map_zero])⟩

/-! ### Postcomposition between big fppf sites -/

section Sites

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (φ : B.obj hT ⟶ B.obj hS)

/-- Postcomposition with a morphism of the big fppf site is continuous for the big fppf
topologies. -/
theorem isContinuous_overMap_bigFppfOver :
    (Over.map φ).IsContinuous (BigFppfOver.topology B T hT) (BigFppfOver.topology B S hS) :=
  inferInstanceAs ((Over.map φ).IsContinuous (B.topology.over _) (B.topology.over _))

/-- Postcomposition with a morphism of the big fppf site is cocontinuous for the big fppf
topologies. -/
theorem isCocontinuous_overMap_bigFppfOver :
    (Over.map φ).IsCocontinuous (BigFppfOver.topology B T hT) (BigFppfOver.topology B S hS) :=
  inferInstanceAs ((Over.map φ).IsCocontinuous (B.topology.over _) (B.topology.over _))

attribute [local instance] isContinuous_overMap_bigFppfOver isCocontinuous_overMap_bigFppfOver
  essentiallySmall_bigFppfOver

/-- Abelian presheaves on the big fppf site over a scheme sheafify. -/
theorem hasSheafify_addCommGrp_bigFppfOver :
    HasSheafify (BigFppfOver.topology B T hT) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- Restriction of abelian sheaves along postcomposition preserves finite limits. -/
theorem preservesFiniteLimits_restriction_overMap :
    PreservesFiniteLimits (restriction (BigFppfOver.topology B T hT)
      (BigFppfOver.topology B S hS) (Over.map φ)) :=
  inferInstance

/-- Restriction of abelian sheaves along postcomposition preserves finite colimits. -/
theorem preservesFiniteColimits_restriction_overMap :
    PreservesFiniteColimits (restriction (BigFppfOver.topology B T hT)
      (BigFppfOver.topology B S hS) (Over.map φ)) :=
  have : ∀ P : (BigFppfOver B T hT)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (Over.map φ).op.HasPointwiseRightKanExtension P := fun P =>
    Stacks.Cohomology.BiggerSite.hasPointwiseRightKanExtension_op _ P
  Stacks.Cohomology.BiggerSite.preservesFiniteColimits_sheafPushforwardContinuous _ _ _ _

/-- Restriction of abelian sheaves along postcomposition is additive. -/
theorem additive_restriction_overMap :
    (restriction (BigFppfOver.topology B T hT) (BigFppfOver.topology B S hS)
      (Over.map φ)).Additive :=
  have := preservesFiniteLimits_restriction_overMap B hT hS φ
  Functor.additive_of_preserves_binary_products _

end Sites

attribute [local instance] isContinuous_overMap_bigFppfOver isCocontinuous_overMap_bigFppfOver

/-! ### The points sheaf under restriction -/

section PointsSheaf

/-- For a group scheme `G` over `W` and `f : X ⟶ W`, the adjunction bijection
`(T → W ⟶ G) ≃ (T ⟶ G ×_W X)` between points of `G` and points of its base change is a group
isomorphism. -/
def overPullbackHomMulEquiv {X W : Scheme.{u}} (f : X ⟶ W) (G : Over W) [GrpObj G]
    (T : Over X) : ((Over.map f).obj T ⟶ G) ≃* (T ⟶ (Over.pullback f).obj G) where
  __ := (Over.mapPullbackAdj f).homEquiv T G
  map_mul' a b :=
    (congrArg (fun c => (Over.mapPullbackAdj f).unit.app T ≫ c)
      ((Over.pullback f).map_mul a b)).trans (MonObj.comp_mul _ _ _)

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}}

/-- The base change of a group scheme in the big fppf site lies in the big fppf site. -/
theorem contains_overPullbackObj_left (hX : B.Contains X) (f : X ⟶ S) (G : Over S)
    (hG : B.Contains G.left) : B.Contains ((Over.pullback f).obj G).left :=
  Scheme.size_pullback_lt G.hom f hG hX

variable {B} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : B.Contains G.left)

/-- **The points sheaf under restriction.** Restricting the points sheaf of a commutative group
scheme `G` over `S` along postcomposition with `f : X ⟶ S` gives the points sheaf of the base
change `G ×_S X` over `X`. -/
def restrictionPointsSheafIso :
    (restriction (BigFppfOver.topology B X hX) (BigFppfOver.topology B S hS)
        (Over.map (ObjectProperty.homMk f : B.obj hX ⟶ B.obj hS))).obj
        (pointsSheaf B S hS G hG) ≅
      pointsSheaf B X hX ((Over.pullback f).obj G) (contains_overPullbackObj_left B hX f G hG) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun T => (MulEquiv.toAdditive
        (overPullbackHomMulEquiv f G ((Over.post B.inclusion).obj T.unop))).toAddCommGrpIso)
      (by
        intro T T' φ
        ext a
        exact (Over.mapPullbackAdj f).homEquiv_naturality_left
          ((Over.post B.inclusion).map φ.unop) a))

end PointsSheaf

/-! ### Stacks 0AFA for the points sheaf of a group scheme over a field -/

section Field

variable (B : BigFppfSite.{u})

/-- The presheaf of sets underlying the points sheaf of a commutative group scheme is
represented by the group scheme. -/
def pointsSheafForgetIso (W : Scheme.{u}) (hW : B.Contains W) (G : Over W) [GrpObj G]
    [IsCommMonObj G] (hG : B.Contains G.left) :
    yoneda.obj (groupSchemeObj B W hW G hG) ≅
      (pointsSheaf B W hW G hG).obj ⋙ forget AddCommGrpCat.{u} :=
  have e₁ : yoneda.obj (groupSchemeObj B W hW G hG) ≅
      (Over.post (X := B.obj hW) B.inclusion).op ⋙ yoneda.obj G := by
    refine NatIso.ofComponents (fun Z => Equiv.toIso
      ((Functor.FullyFaithful.ofFullyFaithful
        (Over.post (X := B.obj hW) B.inclusion)).homEquiv)) ?_
    intro Z Z' φ
    ext g
    exact (Over.post (X := B.obj hW) B.inclusion).map_comp φ.unop g
  have e₂ : (Over.post (X := B.obj hW) B.inclusion).op ⋙ yoneda.obj G ≅
      pointsPresheaf B W hW G ⋙ forget AddCommGrpCat.{u} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intro Z Z' φ; ext g; rfl)
  e₁ ≪≫ e₂

/-- **Stacks 0AFA for a smooth commutative group scheme.** The first cohomology of the points
sheaf of a smooth commutative group scheme over a field `K`, at the final object of the big
fppf site over `Spec K`, is torsion. -/
theorem isAddTorsion_H1_pointsSheaf_of_field (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (G : Over (Spec (.of K))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (hG : B.Contains G.left)
    [HasSheafify (BigFppfOver.topology B (Spec (.of K)) hK) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) AddCommGrpCat.{u})] :
    IsAddTorsion (Sheaf.H' (pointsSheaf B (Spec (.of K)) hK G hG) 1
      (Over.mk (𝟙 (B.obj hK)))) := by
  let U := groupSchemeObj B (Spec (.of K)) hK G hG
  let e := pointsSheafForgetIso B (Spec (.of K)) hK G hG
  have hU := isAlgebraicSpace_yoneda B (Spec (.of K)) hK U
  have hA := hU.of_iso e
  have hT : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hK)) : BigFppfOver B _ hK)) :=
    Over.mkIdTerminal.isTerminalObj yoneda
  have hT' := isAlgebraicSpace_yoneda B (Spec (.of K)) hK (Over.mk (𝟙 (B.obj hK)))
  have hAT := hT'.of_iso (hT.uniqueUpToIso terminalIsTerminal)
  have hfac : terminal.from ((pointsSheaf B (Spec (.of K)) hK G hG).obj ⋙ forget _) =
      e.inv ≫ yoneda.map (Over.mkIdTerminal.from U) ≫
        (hT.uniqueUpToIso terminalIsTerminal).hom :=
    terminal.hom_ext _ _
  have hSm : Space.IsSmooth B (Spec (.of K)) hK
      (terminal.from ((pointsSheaf B (Spec (.of K)) hK G hG).obj ⋙ forget _)) := by
    rw [hfac]
    refine Space.isSmooth_comp B _ hK hA hU hAT _ _
      (Space.isSmooth_of_isIso B _ hK hA hU _) ?_
    refine Space.isSmooth_comp B _ hK hU hT' hAT _ _ ?_
      (Space.isSmooth_of_isIso B _ hK hT' hAT _)
    exact Space.isSmooth_yoneda_map_mkIdTerminal_from B _ hK U (by
      have hmap : (BigFppfOver.toScheme B (Spec (.of K)) hK).map (Over.mkIdTerminal.from U) =
          G.hom :=
        Space.toScheme_map_mkIdTerminal_from_siteObject B _ hK hG G.hom
      rw [hmap]
      assumption)
  exact isAddTorsion_of_injective
    (Stacks.Cohomology.TerminalCohomology.h'AddEquivH _ _ 1 _ Over.mkIdTerminal).toAddMonoidHom
    (AddEquiv.injective _)
    (Space.fppfH1_isAddTorsion K B hK (pointsSheaf B (Spec (.of K)) hK G hG) hA hSm)

end Field

/-! ### Torsion of `H¹(X, G)` -/

/-- The spectrum of the function field of an integral scheme of the big fppf site lies in the
site: the morphism from it is a monomorphism, which does not increase size. -/
theorem contains_spec_functionField (B : BigFppfSite.{u}) {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] (hX : B.Contains X) : B.Contains (Spec X.functionField) :=
  have : QuasiCompact (X.fromSpecStalk (genericPoint X)) := inferInstance
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (X.fromSpecStalk (genericPoint X))) hX

attribute [local instance] essentiallySmall_bigFppfOver

/-- **`H¹(X, G)` is torsion.** Let `G → S` be an abelian scheme and let `f : X ⟶ S` be a morphism
from a two dimensional regular integral Noetherian scheme `X`. Then the first fppf cohomology of
the points sheaf of `G`, on the big fppf site over `S` at the object `X`, is torsion.

Restriction to the generic point `Spec K ⟶ X` is injective on this group: comparing with the
big fppf site over `X` along `Over.map f`, where the points sheaf of `G` becomes the points sheaf
of the abelian scheme `G ×_S X`, it is the injective map of Stacks 0AF9. And the target injects,
comparing now with the big fppf site over `Spec K`, into the first cohomology of the smooth
commutative group scheme `G ×_S Spec K` over `K`, which is torsion by Stacks 0AFA. -/
theorem isAddTorsion_H1_pointsSheaf_of_isRegular (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (G : Over S) [GrpObj G] [IsAbelianScheme G] (hG : B.Contains G.left)
    {X : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ S) [IsIntegral X] [IsNoetherian X]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X = (2 : WithBot ℕ∞))
    [HasSheafify (BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})] :
    IsAddTorsion (Sheaf.H' (pointsSheaf B S hS G hG) 1
      (Over.mk (ObjectProperty.homMk f : B.obj hX ⟶ B.obj hS))) := by
  classical
  have hK : B.Contains (Spec X.functionField) := contains_spec_functionField B hX
  let F := pointsSheaf B S hS G hG
  let f' : B.obj hX ⟶ B.obj hS := ObjectProperty.homMk f
  let ξ := genericPointObj B X hX hK
  let π := genericPointToBase B X hX hK
  let tX : BigFppfOver B X hX := Over.mk (𝟙 (B.obj hX))
  -- the site over `X`
  have := hasSheafify_addCommGrp_bigFppfOver B hX
  have := Stacks.Cohomology.BiggerSite.hasExt_sheaf (BigFppfOver.topology B X hX)
  have := preservesFiniteLimits_restriction_overMap B hX hS f'
  have := preservesFiniteColimits_restriction_overMap B hX hS f'
  have := additive_restriction_overMap B hX hS f'
  let JX := BigFppfOver.topology B X hX
  let JS := BigFppfOver.topology B S hS
  -- Stacks 0AF9 for the base change of `G` to `X`, transported to the restriction of `F`
  let A := (Sheaf.cohomologyPresheafFunctor JX 1).mapIso
    (restrictionPointsSheafIso hX hS f G hG)
  have : IsAbelianScheme ((Over.pullback f).obj G) := isAbelianScheme_overPullbackObj f G
  have h0AF9 := fppfH1_restriction_genericPoint_injective_of_dim_two B X hX hreg hdim hK
    ((Over.pullback f).obj G) (contains_overPullbackObj_left B hX f G hG)
  have key : ∀ y, A.hom.app (op ξ)
      ((((restriction JX JS (Over.map f')).obj F).cohomologyPresheaf 1).map π.op y) =
      (((pointsSheaf B X hX ((Over.pullback f).obj G)
        (contains_overPullbackObj_left B hX f G hG)).cohomologyPresheaf 1).map π.op)
        (A.hom.app (op tX) y) :=
    fun y => NatTrans.naturality_apply A.hom π.op y
  have hπ : Function.Injective
      ((((restriction JX JS (Over.map f')).obj F).cohomologyPresheaf 1).map π.op) := by
    intro a b hab
    have h := congrArg (A.hom.app (op ξ)) hab
    rw [key, key] at h
    exact (A.app (op tX)).addCommGroupIsoToAddEquiv.injective (h0AF9 h)
  -- hence restriction along `Over.map f' π` is injective on the site over `S`
  have hu : Function.Injective ((F.cohomologyPresheaf 1).map ((Over.map f').map π).op) := by
    intro a b hab
    apply restrictH1_injective JX JS (Over.map f') F tX
    apply hπ
    have ha := restrictH1_naturality JX JS (Over.map f') F π a
    have hb := restrictH1_naturality JX JS (Over.map f') F π b
    exact ha.symm.trans ((congrArg _ hab).trans hb)
  let e₀ : (Over.map f').obj tX ≅ Over.mk f' := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ f' = 𝟙 _ ≫ f'
    rfl)
  have hρ : Function.Injective
      ((F.cohomologyPresheaf 1).map ((Over.map f').map π ≫ e₀.hom).op) := by
    rw [op_comp, Functor.map_comp]
    exact hu.comp ((F.cohomologyPresheaf 1).mapIso e₀.op).addCommGroupIsoToAddEquiv.injective
  -- the site over `Spec K`
  let g : Spec X.functionField ⟶ S := X.fromSpecStalk (genericPoint X) ≫ f
  let φ : B.obj hK ⟶ B.obj hS := ObjectProperty.homMk g
  let tK : BigFppfOver B (Spec X.functionField) hK := Over.mk (𝟙 (B.obj hK))
  have := hasSheafify_addCommGrp_bigFppfOver B hK
  have := Stacks.Cohomology.BiggerSite.hasExt_sheaf (BigFppfOver.topology B _ hK)
  have := preservesFiniteLimits_restriction_overMap B hK hS φ
  have := preservesFiniteColimits_restriction_overMap B hK hS φ
  have := additive_restriction_overMap B hK hS φ
  let JK := BigFppfOver.topology B (Spec X.functionField) hK
  have : IsAbelianScheme ((Over.pullback g).obj G) := isAbelianScheme_overPullbackObj g G
  have : Smooth ((Over.pullback g).obj G).hom := smooth_of_isAbelianScheme _
  have h0AFA := isAddTorsion_H1_pointsSheaf_of_field B X.functionField hK
    ((Over.pullback g).obj G) (contains_overPullbackObj_left B hK g G hG)
  let AK := (Sheaf.cohomologyPresheafFunctor JK 1).mapIso
    (restrictionPointsSheafIso hK hS g G hG)
  have hK1 : IsAddTorsion (Sheaf.H' F 1 ((Over.map φ).obj tK)) :=
    isAddTorsion_of_injective _ (restrictH1_injective JK JS (Over.map φ) F tK)
      (isAddTorsion_of_injective (AK.app (op tK)).hom.hom
        (AK.app (op tK)).addCommGroupIsoToAddEquiv.injective h0AFA)
  let e₁ : (Over.map φ).obj tK ≅ (Over.map f').obj ξ := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (𝟙 _ ≫ φ) = ξ.hom ≫ f'
    rw [Category.id_comp, Category.id_comp]
    rfl)
  have hξ : IsAddTorsion (Sheaf.H' F 1 ((Over.map f').obj ξ)) :=
    isAddTorsion_of_injective _
      ((F.cohomologyPresheaf 1).mapIso e₁.op).addCommGroupIsoToAddEquiv.injective hK1
  exact isAddTorsion_of_injective _ hρ hξ

end AlgebraicGeometry

end
