module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AlphaPCoverTriangle
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The abelian direct image along the structure morphism `τ_{X/S}`

The structure morphism of a global crystalline situation,
`Crystalline.GlobalCrystallineSituation.structureToposMorphism` of [Stacks, Tag 07IM], is the
composite
`τ_{X/S} : (X/S)_cris --u_{X/S}--> Sh(X_Zar) --(X ⟶ S)--> Sh(S_Zar)`
of morphisms of topoi valued in sheaves of sets.  On *abelian* sheaves it gives `τ_{X/S, *}`,
`Rτ_{X/S, *}` and `R^jτ_{X/S, *}`, and the Leray factorization of [Stacks, Tag 015M] identifies
`Rτ_{X/S, *}` with `Ru_{X/S, *}` followed by the derived Zariski pushforward along `X ⟶ S`.  The
second factor is restriction along the continuous functor `Opens.map (X ⟶ S)` of
[Stacks, Tag 00X2] at abelian coefficients, `spaceZariskiPushforward`, which is defined for an
arbitrary continuous map of spaces.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `spaceZariskiPushforward` — the abelian direct image `g_*` on small Zariski sites of
  topological spaces, for a continuous `g`, at the coefficients `AddCommGrpCat.{u + 1}`, with
  `spaceZariskiPullback`, `spaceZariskiPushforwardAdjunction`,
  `derivedSpaceZariskiPushforwardFunctor` and `higherSpaceZariskiPushforward`.
* `baseOpensTopology` — the small Zariski site `S_Zar` of the base scheme of a situation.
* `zariskiBaseDirectImage` — the abelian direct image `Ab(X_Zar) ⥤ Ab(S_Zar)` along `X ⟶ S`,
  the second factor of `τ_{X/S}`.
* `tauDirectImage` — `τ_{X/S, *} : Ab(Cris(X/S)) ⥤ Ab(S_Zar)`.
* `derivedTauDirectImageFunctor` — `Rτ_{X/S, *} : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(S_Zar))`, with
  `derivedTauDirectImage` its value on a single abelian sheaf and `higherTauDirectImage` its
  cohomology sheaves `R^jτ_{X/S, *}`.
* `pullbackTauDirectImage` and `derivedPullbackTauDirectImageFunctor` — `τ_{U/T, *}` and
  `Rτ_{U/T, *}` for the situation `U/T` of [Stacks, Tag 07MJ].

## Main results

* `derivedTauDirectImageIsoComp` — [Stacks, Tag 015M] for `τ_{X/S} = (X ⟶ S) ∘ u_{X/S}`:
  `Rτ_{X/S, *} ≅ Ru_{X/S, *} ⋙ R(X ⟶ S)_*`.
* `isZero_higherTauDirectImage_of_injective` and `higherTauDirectImageZeroIso` — `R^jτ_{X/S, *}`
  kills injectives for `j ≠ 0` and `R^0τ_{X/S, *} ≅ τ_{X/S, *}`.
* `preservesInjectiveObjects_tauDirectImage` — `τ_{X/S, *}` carries injective abelian sheaves to
  injective abelian sheaves.

## References

* [Stacks Project, Tag 07IM](https://stacks.math.columbia.edu/tag/07IM)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 00X2](https://stacks.math.columbia.edu/tag/00X2)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe w w' w'' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The abelian Zariski pushforward along a continuous map of spaces -/

section Space

variable {Z W : TopCat.{u}} (g : Z ⟶ W)

/-- Abelian sheaves on the small Zariski site of a space in `TopCat.{u}` admit sheafification at
the coefficient universe `u + 1`. -/
instance instHasSheafifyOpensSpaceAddCommGrpCat (Z : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _

/-- **The abelian direct image `g_* : Ab(Z_Zar) ⥤ Ab(W_Zar)`** along a continuous map `g : Z ⟶ W`,
at the coefficients `AddCommGrpCat.{u + 1}`.  It is restriction along the continuous functor
`Opens.map g` of [Stacks, Tag 00X2]; on sections it is `(g_*G)(V) = G(g⁻¹V)`. -/
def spaceZariskiPushforward :
    Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u + 1} :=
  (Opens.map g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z)

/-- **The abelian inverse image `g^{-1} : Ab(W_Zar) ⥤ Ab(Z_Zar)`**, the chosen left adjoint of
`g_*`: the sheafification of the left Kan extension along `Opens.map g`. -/
@[sga "4 III 1.7" "special case"]
def spaceZariskiPullback :
    Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u + 1} :=
  (Opens.map g).sheafPullback AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z)

/-- **The adjunction `g^{-1} ⊣ g_*`** on abelian sheaves, [Stacks, Tag 00X2] at abelian
coefficients. -/
def spaceZariskiPushforwardAdjunction :
    spaceZariskiPullback g ⊣ spaceZariskiPushforward g :=
  (Opens.map g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Z)

/-- **`g^{-1}` is left exact** on abelian sheaves. -/
@[sga "4 III 1.7" "partial"]
instance preservesFiniteLimits_spaceZariskiPullback :
    PreservesFiniteLimits (spaceZariskiPullback g) :=
  Stacks.Topology.preservesFiniteLimits_sheafPullbackOpensMap.{u + 1} g

/-- `g^{-1}` commutes with every colimit that exists, being a left adjoint. -/
instance preservesColimitsOfSize_spaceZariskiPullback :
    PreservesColimitsOfSize.{w, w'} (spaceZariskiPullback g) :=
  (spaceZariskiPushforwardAdjunction g).leftAdjoint_preservesColimits

/-- `g_*` commutes with every limit that exists, being a right adjoint; in particular it is left
exact. -/
instance preservesLimitsOfSize_spaceZariskiPushforward :
    PreservesLimitsOfSize.{w, w'} (spaceZariskiPushforward g) :=
  (spaceZariskiPushforwardAdjunction g).rightAdjoint_preservesLimits

/-- `g_*` is additive on abelian sheaves. -/
instance additive_spaceZariskiPushforward : (spaceZariskiPushforward g).Additive where
  map_add := by intros; rfl

/-- **`g_*` carries injective abelian sheaves to injective abelian sheaves.** -/
instance preservesInjectiveObjects_spaceZariskiPushforward :
    (spaceZariskiPushforward g).PreservesInjectiveObjects :=
  Stacks.Topology.preservesInjectiveObjects_sheafPushforwardOpensMap.{u + 1} g

/-- Abelian sheaves on the small Zariski site of a space in `TopCat.{u}` have enough injectives at
the coefficient universe `u + 1`. -/
@[sga "4 I 7.13" "special case", sga "4½ Arcata 1.6.3" "open-set sites"]
instance instEnoughInjectivesOpensSpace (Z : TopCat.{u}) :
    EnoughInjectives (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u + 1}) :=
  Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u, u + 2} (Opens.grothendieckTopology Z)
    AddCommGrpCat.{u + 1}

/-- **A derived category of the abelian sheaves on the small Zariski site of a space exists**,
with its morphisms one universe above theirs. -/
@[instance_reducible]
def hasDerivedCategorySpaceZariskiSheaf (Z : TopCat.{u}) :
    HasDerivedCategory.{u + 2} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

section Derived

variable [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u + 1})]

/-- **The derived Zariski direct image `Rg_* : D⁺(Ab(Z_Zar)) ⥤ D⁺(Ab(W_Zar))`**, the right derived
functor of `g_*`. -/
def derivedSpaceZariskiPushforwardFunctor :
    DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u + 1}) :=
  (spaceZariskiPushforward g).rightDerivedFunctorPlus

/-- **The higher direct image `R^j g_* : Ab(Z_Zar) ⥤ Ab(W_Zar)`**, the degree-`j` cohomology sheaf
of `Rg_*`. -/
def higherSpaceZariskiPushforward (j : ℤ) :
    Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u + 1} ⥤
      Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u + 1} :=
  (spaceZariskiPushforward g).rightDerivedPlus j

/-- **`R^j g_* I = 0` for `j ≠ 0` and `I` an injective abelian sheaf.** -/
theorem isZero_higherSpaceZariskiPushforward_of_injective
    (G : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u + 1}) [Injective G] (j : ℤ)
    (hj : j ≠ 0) : IsZero ((higherSpaceZariskiPushforward g j).obj G) :=
  Functor.isZero_rightDerivedPlus_obj_injective (spaceZariskiPushforward g) j hj G

/-- **`R^0 g_* ≅ g_*`**, the Zariski direct image being left exact. -/
def higherSpaceZariskiPushforwardZeroIso :
    higherSpaceZariskiPushforward g 0 ≅ spaceZariskiPushforward g :=
  haveI : PreservesFiniteLimits (spaceZariskiPushforward g) := inferInstance
  (Stacks.DerivedIndexing.rightDerivedIso (spaceZariskiPushforward g) 0).symm ≪≫
    (spaceZariskiPushforward g).rightDerivedZeroIsoSelf

end Derived

end Space

/-! ### `τ_{X/S, *}` on abelian sheaves -/

variable (S : GlobalCrystallineSituation.{u})

/-- **The small Zariski site `S_Zar` of the base scheme of a global crystalline situation.** -/
abbrev baseOpensTopology : GrothendieckTopology S.S.scheme.Opens :=
  Opens.grothendieckTopology S.S.scheme.carrier

/-- **The abelian direct image `Ab(X_Zar) ⥤ Ab(S_Zar)` along the structure morphism `X ⟶ S`**,
the second factor of `τ_{X/S}`. -/
abbrev zariskiBaseDirectImage :
    Sheaf (opensTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (baseOpensTopology S) AddCommGrpCat.{u + 1} :=
  spaceZariskiPushforward (sourceToBase S).base

/-- **The abelian direct image `τ_{X/S, *} : Ab(Cris(X/S)) ⥤ Ab(S_Zar)`** along the structure
morphism of [Stacks, Tag 07IM]: the composite of `u_{X/S, *}` with the Zariski pushforward
along `X ⟶ S`. -/
def tauDirectImage :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (baseOpensTopology S) AddCommGrpCat.{u + 1} :=
  zariskiDirectImage S ⋙ zariskiBaseDirectImage S

/-- `τ_{X/S, *}` commutes with every limit that exists, both of its factors being right
adjoints. -/
instance preservesLimitsOfSize_tauDirectImage :
    PreservesLimitsOfSize.{w, w'} (tauDirectImage S) :=
  inferInstanceAs (PreservesLimitsOfSize.{w, w'}
    (zariskiDirectImage S ⋙ zariskiBaseDirectImage S))

/-- `τ_{X/S, *}` is additive, being a composite of additive functors. -/
instance additive_tauDirectImage : (tauDirectImage S).Additive :=
  inferInstanceAs ((zariskiDirectImage S ⋙ zariskiBaseDirectImage S).Additive)

/-- **`τ_{X/S, *}` carries injective abelian sheaves to injective abelian sheaves**, both of its
factors doing so. -/
instance preservesInjectiveObjects_tauDirectImage :
    (tauDirectImage S).PreservesInjectiveObjects :=
  inferInstanceAs ((zariskiDirectImage S ⋙ zariskiBaseDirectImage S).PreservesInjectiveObjects)

/-- **The sections of `τ_{X/S, *}F` over an open `V` of `S` are the sections of `u_{X/S, *}F` over
its preimage in `X`**, by definition of the Zariski pushforward. -/
theorem tauDirectImage_obj_obj_obj (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (V : S.S.scheme.Opens) :
    ((tauDirectImage S).obj F).obj.obj (op V) =
      ((zariskiDirectImage S).obj F).obj.obj
        (op ((Opens.map (sourceToBase S).base).obj V)) :=
  rfl

/-! ### `Rτ_{X/S, *}` -/

section DerivedTau

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (baseOpensTopology S) AddCommGrpCat.{u + 1})]

/-- **The derived direct image `Rτ_{X/S, *} : D⁺(Ab(Cris(X/S))) ⥤ D⁺(Ab(S_Zar))`**, the right
derived functor of `τ_{X/S, *}`. -/
def derivedTauDirectImageFunctor :
    DerivedCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (baseOpensTopology S) AddCommGrpCat.{u + 1}) :=
  (tauDirectImage S).rightDerivedFunctorPlus

/-- **`Rτ_{X/S, *}F` for a single abelian sheaf `F`**: the sheaf placed in degree zero, then the
derived direct image. -/
def derivedTauDirectImage :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      DerivedCategory.Plus (Sheaf (baseOpensTopology S) AddCommGrpCat.{u + 1}) :=
  DerivedCategory.Plus.singleFunctor (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) 0 ⋙
    derivedTauDirectImageFunctor S

/-- **The higher direct image `R^jτ_{X/S, *} : Ab(Cris(X/S)) ⥤ Ab(S_Zar)`**, the degree-`j`
cohomology sheaf of `Rτ_{X/S, *}`. -/
def higherTauDirectImage (j : ℤ) :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (baseOpensTopology S) AddCommGrpCat.{u + 1} :=
  (tauDirectImage S).rightDerivedPlus j

/-- Taking the degree-`j` cohomology of `Rτ_{X/S, *}` is `R^jτ_{X/S, *}`, by definition of the
latter. -/
theorem derivedTauDirectImage_comp_homologyFunctor (j : ℤ) :
    derivedTauDirectImage S ⋙
        DerivedCategory.Plus.homologyFunctor
          (Sheaf (baseOpensTopology S) AddCommGrpCat.{u + 1}) j =
      higherTauDirectImage S j :=
  rfl

/-- **`R^jτ_{X/S, *} I = 0` for `j ≠ 0` and `I` an injective abelian sheaf**, so `Rτ_{X/S, *}I` is
concentrated in degree zero. -/
theorem isZero_higherTauDirectImage_of_injective
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) [Injective F] (j : ℤ) (hj : j ≠ 0) :
    IsZero ((higherTauDirectImage S j).obj F) :=
  Functor.isZero_rightDerivedPlus_obj_injective (tauDirectImage S) j hj F

/-- **`R^0τ_{X/S, *} ≅ τ_{X/S, *}`.** -/
def higherTauDirectImageZeroIso :
    higherTauDirectImage S 0 ≅ tauDirectImage S :=
  haveI : PreservesFiniteLimits (tauDirectImage S) := inferInstance
  (Stacks.DerivedIndexing.rightDerivedIso (tauDirectImage S) 0).symm ≪≫
    (tauDirectImage S).rightDerivedZeroIsoSelf

/-- **[Stacks, Tag 015M] for `τ_{X/S} = (X ⟶ S) ∘ u_{X/S}`:
`Rτ_{X/S, *} ≅ Ru_{X/S, *} ⋙ R(X ⟶ S)_*`.** -/
def derivedTauDirectImageIsoComp
    [HasDerivedCategory.{w''} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] :
    derivedTauDirectImageFunctor S ≅
      derivedZariskiDirectImageFunctor S ⋙
        derivedSpaceZariskiPushforwardFunctor (sourceToBase S).base :=
  Functor.rightDerivedFunctorPlusCompIso (zariskiDirectImage S) (zariskiBaseDirectImage S)

end DerivedTau

/-! ### `τ_{U/T, *}` and `Rτ_{U/T, *}` for the situation `U/T` of [Stacks, Tag 07MJ] -/

section Pullback

open DividedPowerScheme

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ closedFiberMap fS = fX ≫ S'.toClosedFiber)
  (A' : CrystallineThickening S')

/-- **The derived Zariski pushforward `R(T ⟶ T')_*`** along the second projection
`T = S ×_{S'} T' ⟶ T'`. -/
def derivedPullbackBaseZariskiPushforwardFunctor
    [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology
      (pullbackBase S S' fS A').scheme.carrier) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (Opens.grothendieckTopology
      A'.obj.thickening.target.scheme.carrier) AddCommGrpCat.{u + 1})] :
    DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology
        (pullbackBase S S' fS A').scheme.carrier) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology
        A'.obj.thickening.target.scheme.carrier) AddCommGrpCat.{u + 1}) :=
  derivedSpaceZariskiPushforwardFunctor (pullback.snd fS A'.obj.toBase).hom.base

include hf

/-- **The abelian direct image `τ_{U/T, *} : Ab(Cris(U/T)) ⥤ Ab(T_Zar)`** along the structure
morphism `τ_{U/T}` of [Stacks, Tag 07MJ], whose set-valued form is
`Crystalline.GlobalCrystallineSituation.pullbackStructureToposMorphism`. -/
def pullbackTauDirectImage :
    Sheaf (smallTopology (pullbackSituation S S' fS fX hf A')) AddCommGrpCat.{u + 1} ⥤
      Sheaf (baseOpensTopology (pullbackSituation S S' fS fX hf A')) AddCommGrpCat.{u + 1} :=
  tauDirectImage (pullbackSituation S S' fS fX hf A')

/-- **The derived direct image `Rτ_{U/T, *} : D⁺(Ab(Cris(U/T))) ⥤ D⁺(Ab(T_Zar))`** of
[Stacks, Tag 07MJ]. -/
def derivedPullbackTauDirectImageFunctor
    [HasDerivedCategory.{w} (Sheaf (smallTopology (pullbackSituation S S' fS fX hf A'))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (baseOpensTopology (pullbackSituation S S' fS fX hf A'))
      AddCommGrpCat.{u + 1})] :
    DerivedCategory.Plus (Sheaf (smallTopology (pullbackSituation S S' fS fX hf A'))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (baseOpensTopology (pullbackSituation S S' fS fX hf A'))
        AddCommGrpCat.{u + 1}) :=
  derivedTauDirectImageFunctor (pullbackSituation S S' fS fX hf A')

/-- **`Rτ_{U/T, *}F_U` for a single abelian sheaf on `Cris(U/T)`**, with the Zariski site of
`T = S ×_{S'} T'` spelled as the site of the divided power fibre product rather than as the base
site of the situation `U/T`; the two are definitionally equal. -/
def derivedPullbackTauDirectImage
    [HasDerivedCategory.{w} (Sheaf (smallTopology (pullbackSituation S S' fS fX hf A'))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (Opens.grothendieckTopology
      (pullbackBase S S' fS A').scheme.carrier) AddCommGrpCat.{u + 1})] :
    Sheaf (smallTopology (pullbackSituation S S' fS fX hf A')) AddCommGrpCat.{u + 1} ⥤
      DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology
        (pullbackBase S S' fS A').scheme.carrier) AddCommGrpCat.{u + 1}) :=
  letI : HasDerivedCategory.{w'} (Sheaf
      (baseOpensTopology (pullbackSituation S S' fS fX hf A')) AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (HasDerivedCategory.{w'} (Sheaf (Opens.grothendieckTopology
      (pullbackBase S S' fS A').scheme.carrier) AddCommGrpCat.{u + 1}))
  derivedTauDirectImage (pullbackSituation S S' fS fX hf A')

end Pullback

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
