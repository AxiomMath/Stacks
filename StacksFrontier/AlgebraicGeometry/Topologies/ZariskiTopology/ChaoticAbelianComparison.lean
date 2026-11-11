module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianSheavesOnSpace
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.ChaoticComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.FreeAbelianSheavesOfAPresheafSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.TriangleOfAPushoutSquare
import StacksCore.Tactic.StacksAttribute

/-!
# Comparing the chaotic and the Zariski topologies on the affine opens, for abelian sheaves

Let `B` be a big Zariski site containing a scheme `S`. Write `S_{affine,Zar}` for the affine opens
of `S` with the Zariski topology and `S_affine` for the same category with the chaotic topology,
for which every presheaf is a sheaf, and let `ε : S_{affine,Zar} ⟶ S_affine` be the comparison,
whose direct image `ε_*` regards an abelian Zariski sheaf as an abelian presheaf. This file proves
Stacks 0F1L: the derived direct image `Rε_* : D(S_{affine,Zar}) ⟶ D(S_affine)` is fully faithful,
and a bounded-below object `K` of `D(S_affine)` lies in its essential image if and only if

1. `RΓ(∅, K) = 0`, and
2. the canonical map `c^K_{U,V,W,V ∩ W}` of Stacks 0F16 is an isomorphism whenever `U = V ∪ W` with
   `V, W ⊆ U` standard opens of the affine open `U`.

## Main definitions

* `AlgebraicGeometry.SmallAffineZariski.abelianPushforward`: `ε_*` on abelian sheaves.
* `AlgebraicGeometry.SmallAffineZariski.abelianPullback`: `ε^{-1}`, Zariski sheafification.
* `AlgebraicGeometry.SmallAffineZariski.chaoticDerivedSections` and
  `AlgebraicGeometry.SmallAffineZariski.chaoticCSquareData`: derived sections `RΓ(U, -)` on
  `D(S_affine)`, and the canonical map of Stacks 0F16 for a square of affine opens.

## Main results

* `AlgebraicGeometry.SmallAffineZariski.abelian_fullyFaithful_and_essImage_iff`: **Stacks 0F1L.**

## Implementation notes

The proof is the source's, run directly for the chaotic topology rather than through the almost
chaotic one: the argument of Stacks 0F18 is carried out with the extra condition `RΓ(∅, -) = 0`.
An object `K` of `D⁺(S_affine)` satisfying the two conditions sits in a distinguished triangle
`K ⟶ Rε_* ε^{-1} K ⟶ M ⟶ K[1]`. The middle term satisfies both conditions: a K-injective complex of
injective Zariski sheaves computes it, its sections over an empty affine open vanish because the
empty sieve covers it, and its sections over a standard open cover square form a short exact
sequence because injective sheaves are flasque along open immersions. Hence `M` satisfies both
conditions as well — derived sections for the chaotic topology are exact, and the canonical maps
satisfy two out of three (Stacks 0EWP) — and `ε^{-1} M = 0`. Then `M = 0` by induction on the
lowest nonzero cohomology presheaf `Hⁿ(M)`: its sections over an empty affine open vanish, and its
sections over every standard open cover square form a pullback square, so it is a Zariski sheaf
(Stacks 0F1A), hence is `ε_*` of its sheafification `Hⁿ(ε^{-1} M) = 0`.

Condition (1) is genuinely needed: an abelian presheaf may have nonzero sections over the empty
affine open, and no such presheaf is a Zariski sheaf. The variant of this statement for modules
over a Zariski sheaf of rings is
`AlgebraicGeometry.SmallAffineZariski.essImage_iff_isZero_derivedSections_and_isCSquareIso`; there
condition (1) is automatic.

`Rε_*` is taken as an arbitrary right derived functor of `ε_*` with its unit, as in
`Stacks.Cohomology.MayerVietoris.essImage_iff_forall_isCSquareIso`.

## References

* [Stacks Project, Tag 0F1L](https://stacks.math.columbia.edu/tag/0F1L)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 0F18](https://stacks.math.columbia.edu/tag/0F18)
* [Stacks Project, Tag 0EWK](https://stacks.math.columbia.edu/tag/0EWK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.MayerVietoris Stacks.Cohomology.MayerVietoris

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.SmallAffineZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The chaotic topology on the affine opens of `S`: only the maximal sieve covers, so every
presheaf is a sheaf. -/
abbrev chaotic : GrothendieckTopology (SmallAffineZariski B S hS) :=
  GrothendieckTopology.trivial (SmallAffineZariski B S hS)

section Categories

/-- Every presheaf is a sheaf for the chaotic topology. -/
lemma isSheaf_chaotic {A : Type*} [Category* A] (F : (SmallAffineZariski B S hS)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (chaotic B S hS) F := by
  intro E X T hT
  rw [GrothendieckTopology.trivial_covering] at hT
  subst hT
  exact Presieve.isSheafFor_top _

/-- The affine opens of `S` form an essentially small category in the universe of their
sections. -/
instance essentiallySmall_succ : EssentiallySmall.{u + 1} (SmallAffineZariski B S hS) :=
  EssentiallySmall.mk' (AsSmall.equiv.{u, u + 1, u + 1} (C := SmallAffineZariski B S hS))

/-- Abelian Zariski sheaves on the affine opens of `S` form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_topology :
    IsGrothendieckAbelian.{u + 1} (Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) :=
  have _ : PreservesLimits (forget AddCommGrpCat.{u + 1}) := AddCommGrpCat.forget_preservesLimits
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ AddCommGrpCat.{u + 1}

/-- Abelian presheaves on the affine opens of `S` form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_chaotic :
    IsGrothendieckAbelian.{u + 1} (Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1}) :=
  have _ : PreservesLimits (forget AddCommGrpCat.{u + 1}) := AddCommGrpCat.forget_preservesLimits
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ AddCommGrpCat.{u + 1}

/-- For the chaotic topology the underlying presheaf functor is an equivalence. -/
instance sheafToPresheaf_chaotic_isEquivalence :
    (sheafToPresheaf (chaotic B S hS) AddCommGrpCat.{u + 1}).IsEquivalence where
  essSurj := ⟨fun F => ⟨⟨F, isSheaf_chaotic B S hS F⟩, ⟨Iso.refl _⟩⟩⟩

/-- **`ε_*` on abelian sheaves.** An abelian Zariski sheaf on the affine opens of `S`, regarded as
an abelian presheaf, that is, as an abelian sheaf for the chaotic topology. -/
def abelianPushforward :
    Sheaf (topology B S hS) AddCommGrpCat.{u + 1} ⥤
      Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1} where
  obj F := ⟨F.obj, isSheaf_chaotic B S hS F.obj⟩
  map f := ⟨f.hom⟩

/-- `ε_*` is fully faithful: it does not change underlying presheaves. -/
def fullyFaithfulAbelianPushforward : (abelianPushforward B S hS).FullyFaithful where
  preimage f := ⟨f.hom⟩

instance : (abelianPushforward B S hS).Full := (fullyFaithfulAbelianPushforward B S hS).full

instance : (abelianPushforward B S hS).Faithful := (fullyFaithfulAbelianPushforward B S hS).faithful

/-- `ε_*` is additive. -/
instance abelianPushforward_additive : (abelianPushforward B S hS).Additive where
  map_add := rfl

/-- **`ε^{-1}` on abelian sheaves**: Zariski sheafification of an abelian presheaf. -/
def abelianPullback :
    Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology B S hS) AddCommGrpCat.{u + 1} :=
  sheafToPresheaf _ _ ⋙ presheafToSheaf (topology B S hS) AddCommGrpCat.{u + 1}

/-- **`ε^{-1} ⊣ ε_*`.** This is the sheafification adjunction, restricted along the
underlying presheaf functor of the chaotic topology. -/
def abelianPullbackAdjPushforward : abelianPullback B S hS ⊣ abelianPushforward B S hS :=
  Adjunction.restrictFullyFaithful
    (sheafificationAdjunction (topology B S hS) AddCommGrpCat.{u + 1})
    (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- `ε^{-1}` is left exact. -/
instance abelianPullback_preservesFiniteLimits :
    PreservesFiniteLimits (abelianPullback B S hS) :=
  inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf _ _ ⋙ presheafToSheaf (topology B S hS) AddCommGrpCat.{u + 1}))

/-- `ε^{-1}` is right exact, being a left adjoint. -/
instance abelianPullback_preservesFiniteColimits :
    PreservesFiniteColimits (abelianPullback B S hS) :=
  letI : PreservesColimitsOfSize.{0, 0} (abelianPullback B S hS) :=
    (abelianPullbackAdjPushforward B S hS).leftAdjoint_preservesColimits
  inferInstance

/-- `ε^{-1}` is additive. -/
instance abelianPullback_additive : (abelianPullback B S hS).Additive :=
  (abelianPullbackAdjPushforward B S hS).left_adjoint_additive

/-- `ε_*` is left exact, being a right adjoint. -/
instance abelianPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (abelianPushforward B S hS) :=
  ⟨fun _ ↦
    (abelianPullbackAdjPushforward B S hS).rightAdjoint_preservesLimits.preservesLimitsOfShape⟩

/-- The sections functors of abelian presheaves on the affine opens of `S`. -/
abbrev chaoticSections :
    (SmallAffineZariski B S hS)ᵒᵖ ⥤
      (Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1}) :=
  sheafSections _ _

/-- Sections of abelian presheaves are exact: they are evaluation of the underlying presheaf. -/
instance chaoticSections_preservesFiniteLimits (U : (SmallAffineZariski B S hS)ᵒᵖ) :
    PreservesFiniteLimits ((chaoticSections B S hS).obj U) :=
  inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj U))

/-- Sections of abelian presheaves are exact: they are evaluation of the underlying presheaf. -/
instance chaoticSections_preservesFiniteColimits (U : (SmallAffineZariski B S hS)ᵒᵖ) :
    PreservesFiniteColimits ((chaoticSections B S hS).obj U) :=
  inferInstanceAs (PreservesFiniteColimits (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj U))

/-- Derived sections `RΓ(U, -)` of objects of the derived category of abelian presheaves on the
affine opens of `S`. -/
abbrev chaoticDerivedSections (U : SmallAffineZariski B S hS) :
    DerivedCategory (Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  (CanonicalMapOfComplexes.General.derivedSectionsData (chaoticSections B S hS)).functor.obj
    (op U)

/-- The canonical map `c^K` of Stacks 0F16 for a square of affine opens of `S`, on the derived
category of abelian presheaves. -/
abbrev chaoticCSquareData (sq : Square (SmallAffineZariski B S hS)) :
    CanonicalMapOfComplexes.General.DerivedCSquareData (chaoticSections B S hS) sq :=
  CanonicalMapOfComplexes.General.derivedCSquareDataOfIsGrothendieckAbelian
    (chaoticSections B S hS) sq

end Categories

section Sections

/-- Every abelian Zariski sheaf on the affine opens of `S` takes a standard open cover square to
a cartesian square of sections. -/
lemma op_map_isPullback_of_abelian {sq : Square (SmallAffineZariski B S hS)}
    (hsq : IsStandardOpenCoverSquare B S hS sq)
    (G : Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) : (sq.op.map G.obj).IsPullback := by
  have h := hsq.op_map_isPullback
    ⟨G.obj ⋙ forget AddCommGrpCat.{u + 1},
      Presheaf.isSheaf_comp_of_isSheaf _ _ _ G.property⟩
  exact Square.IsPullback.of_map (forget AddCommGrpCat.{u + 1})
    (h : ((sq.op.map G.obj).map (forget AddCommGrpCat.{u + 1})).IsPullback)

/-- **An injective abelian Zariski sheaf is flasque along a monomorphism of sheafified
representables.** A section over `U` is a map out of the free abelian sheaf on `h_U`, and an
injective sheaf extends it along the monomorphism of free abelian sheaves induced by `g`. -/
lemma epi_map_of_injective {U V : SmallAffineZariski B S hS} (g : U ⟶ V)
    (hmono : Mono ((Sheaf.sheafifiedYoneda (topology B S hS)).map g))
    (G : Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) [Injective G] :
    Epi (G.obj.map g.op) := by
  have : HasSheafify (topology B S hS) AddCommGrpCat.{u + 1} := inferInstance
  have : HasWeakSheafify (topology B S hS) (Type (u + 1)) := inferInstance
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let J := topology B S hS
  let adj : Presheaf.freeAbelianSheaf.{u + 1} J ⊣
      sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙ Presheaf.forgetAbelian :=
    Presheaf.freeAbelianSheafAdj.{u + 1} J
  have hm : Mono ((Presheaf.freeAbelianSheaf.{u + 1} J).map (uliftYoneda.{u + 1}.map g)) :=
    PresheafSquare.mono_freeAbelianSheaf_map J _ hmono
  let φ : (Presheaf.freeAbelianSheaf.{u + 1} J).obj (uliftYoneda.{u + 1}.obj U) ⟶ G :=
    (adj.homEquiv _ _).symm (uliftYonedaEquiv.{u + 1}.symm s)
  let ψ := Injective.factorThru φ ((Presheaf.freeAbelianSheaf.{u + 1} J).map
    (uliftYoneda.{u + 1}.map g))
  have hψ := Injective.comp_factorThru φ ((Presheaf.freeAbelianSheaf.{u + 1} J).map
    (uliftYoneda.{u + 1}.map g))
  refine ⟨uliftYonedaEquiv.{u + 1} (adj.homEquiv _ _ ψ), ?_⟩
  have hnat := adj.homEquiv_naturality_left (uliftYoneda.{u + 1}.map g) ψ
  rw [hψ] at hnat
  have hs : uliftYonedaEquiv.{u + 1} (adj.homEquiv _ _ φ) = s := by simp [φ]
  rw [← hs, hnat]
  exact uliftYonedaEquiv_naturality.{u + 1} (adj.homEquiv _ _ ψ) g.op

/-- **The sections short complex of an injective abelian Zariski sheaf over a standard open
cover square is short exact.** -/
lemma shortExact_sectionsShortComplex_of_injective {sq : Square (SmallAffineZariski B S hS)}
    (hsq : IsStandardOpenCoverSquare B S hS sq)
    (G : Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) [Injective G] :
    (General.sectionsShortComplex (chaoticSections B S hS) sq
      ((abelianPushforward B S hS).obj G)).ShortExact := by
  have := epi_map_of_injective B S hS sq.f₁₂ hsq.mono_sheafifiedYoneda_map_f₁₂ G
  have hpb : IsPullback (G.obj.map sq.f₃₄.op) (G.obj.map sq.f₂₄.op) (G.obj.map sq.f₁₃.op)
      (G.obj.map sq.f₁₂.op) :=
    (op_map_isPullback_of_abelian B S hS hsq G : IsPullback _ _ _ _).flip
  exact shortExact_of_isPullback hpb _

end Sections

section Derived

/-- **Derived sections of abelian presheaves are computed degreewise.** Sections for the chaotic
topology are exact, so the induced functor on derived categories is a right derived functor of
them, and right derived functors are unique. -/
def chaoticDerivedSectionsIso (U : SmallAffineZariski B S hS) :
    chaoticDerivedSections B S hS U ≅ ((chaoticSections B S hS).obj (op U)).mapDerivedCategory :=
  have := Functor.isRightDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ))
    ((chaoticSections B S hS).obj (op U)).mapDerivedCategory
    ((chaoticSections B S hS).obj (op U)).mapDerivedCategoryFactors
  Functor.rightDerivedUnique _ _
    ((CanonicalMapOfComplexes.General.derivedSectionsData (chaoticSections B S hS)).unit U)
    ((chaoticSections B S hS).obj (op U)).mapDerivedCategoryFactors.inv
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))

/-- Derived sections over an affine open vanish on the third vertex of a distinguished triangle
as soon as they vanish on the other two: they are a triangulated functor. -/
lemma isZero_chaoticDerivedSections_obj₃ (U : SmallAffineZariski B S hS)
    (T : Triangle (DerivedCategory (Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1})))
    (hT : T ∈ distTriang _) (h₁ : IsZero ((chaoticDerivedSections B S hS U).obj T.obj₁))
    (h₂ : IsZero ((chaoticDerivedSections B S hS U).obj T.obj₂)) :
    IsZero ((chaoticDerivedSections B S hS U).obj T.obj₃) :=
  (Triangle.isZero₃_of_isZero₁₂ _
    (((chaoticSections B S hS).obj (op U)).mapDerivedCategory.map_distinguished T hT)
    (h₁.of_iso ((chaoticDerivedSectionsIso B S hS U).app T.obj₁).symm)
    (h₂.of_iso ((chaoticDerivedSectionsIso B S hS U).app T.obj₂).symm)).of_iso
    ((chaoticDerivedSectionsIso B S hS U).app T.obj₃)

variable (Rε : DerivedCategory (Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) ⥤
    DerivedCategory (Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1}))
  (η : (abelianPushforward B S hS).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
  [Rε.IsRightDerivedFunctor η (HomotopyCategory.quasiIso
      (Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]

include η in
/-- A K-injective complex of abelian Zariski sheaves, regarded as a complex of abelian presheaves,
represents its derived direct image. -/
def derivedAbelianPushforwardIso
    (I : CochainComplex (Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) ℤ) [I.IsKInjective] :
    DerivedCategory.Q.obj
        (((abelianPushforward B S hS).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      Rε.obj (DerivedCategory.Q.obj I) :=
  have : IsIso (η.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    isIso_unit_app_of_isKInjective _ (exists_quasiIso_isKInjective _) DerivedCategory.Qh Rε η I
  (DerivedCategory.quotientCompQhIso _).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso
      (((abelianPushforward B S hS).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I).symm ≪≫
    asIso (η.app _) ≪≫ Rε.mapIso ((DerivedCategory.quotientCompQhIso _).app I)

include η in
/-- **The essential image of `Rε_*` satisfies the two conditions of Stacks 0F1L.** Represent the
object by `ε_* I` for a K-injective complex `I` of injective abelian Zariski sheaves: its sections
over an empty affine open vanish, and its sections over a standard open cover square form a short
exact sequence of complexes. -/
lemma isZero_and_isCSquareIso_of_essImage
    (K : DerivedCategory (Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1})) (hK : Rε.essImage K) :
    (∀ U : SmallAffineZariski B S hS, IsEmpty ((toScheme B S hS).obj U) →
        IsZero ((chaoticDerivedSections B S hS U).obj K)) ∧
      ∀ sq : Square (SmallAffineZariski B S hS), IsStandardOpenCoverSquare B S hS sq →
        (chaoticCSquareData B S hS sq).IsCSquareIso K := by
  obtain ⟨L, ⟨e⟩⟩ := hK
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor
    (Sheaf (topology B S hS) AddCommGrpCat.{u + 1})).obj (DerivedCategory.Q.objPreimage L)
  have hinj (p : ℤ) : Injective (I.X p) := inferInstance
  let eI : DerivedCategory.Q.obj I ≅ L :=
    (asIso (DerivedCategory.Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion
      (Sheaf (topology B S hS) AddCommGrpCat.{u + 1})).app _))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso L
  let I' := ((abelianPushforward B S hS).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  have : CochainComplex.IsKInjective I' :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact _
      (abelianPullback B S hS) (abelianPullbackAdjPushforward B S hS) I
  let e' : DerivedCategory.Q.obj I' ≅ K :=
    derivedAbelianPushforwardIso B S hS Rε η I ≪≫ Rε.mapIso eI ≪≫ e
  refine ⟨fun U hU => ?_, fun sq hsq => ?_⟩
  · let data := CanonicalMapOfComplexes.General.derivedSectionsData (chaoticSections B S hS)
    have hcomplex : IsZero
        ((CanonicalMapOfComplexes.General.complexFunctor (chaoticSections B S hS) U).obj I') := by
      rw [IsZero.iff_id_eq_zero]
      refine HomologicalComplex.hom_ext _ _ fun p => ?_
      have hterm : IsZero ((I.X p).obj.obj (op U)) :=
        (isZero_zero AddCommGrpCat.{u + 1}).of_iso
          (((I.X p).isTerminalOfBotCover U (bot_mem_topology B S hS hU)).uniqueUpToIso
            (isZero_zero _).isTerminal)
      exact hterm.eq_of_src _ _
    exact ((DerivedCategory.Q.map_isZero hcomplex).of_iso
      (asIso ((data.unit U).app I')).symm).of_iso ((data.functor.obj (op U)).mapIso e').symm
  · exact ((chaoticCSquareData B S hS sq).isCSquareIso_iff_quasiIso K I' e').mpr
      (General.quasiIso_cSquare_of_sectionsShortExact (chaoticSections B S hS) sq I'
        (fun p => by
          have := hinj p
          exact shortExact_sectionsShortComplex_of_injective B S hS hsq (I.X p)))

/-- **The vanishing criterion.** A bounded-below object `M` of the derived category of abelian
presheaves whose derived sections over every empty affine open vanish, whose canonical maps for
the standard open cover squares are isomorphisms, and whose Zariski sheafification vanishes, is
zero. If the cohomology presheaves of `M` vanish below `n`, then `Hⁿ(M)` vanishes over the empty
affine opens and takes standard open cover squares to pullback squares, so it is a Zariski sheaf;
it is then `ε_*` of its sheafification `Hⁿ(ε^{-1} M) = 0`. -/
lemma isZero_of_forall_isCSquareIso_of_abelianPullback_isZero
    (M : DerivedCategory (Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1}))
    (hplus : (DerivedCategory.TStructure.t
      (C := Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1})).plus M)
    (hempty : ∀ U : SmallAffineZariski B S hS, IsEmpty ((toScheme B S hS).obj U) →
      IsZero ((chaoticDerivedSections B S hS U).obj M))
    (hsquares : ∀ sq : Square (SmallAffineZariski B S hS), IsStandardOpenCoverSquare B S hS sq →
      (chaoticCSquareData B S hS sq).IsCSquareIso M)
    (hzero : IsZero ((abelianPullback B S hS).mapDerivedCategory.obj M)) : IsZero M := by
  let coarse := Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1}
  let data := CanonicalMapOfComplexes.General.derivedSectionsData (chaoticSections B S hS)
  have hbottom (n : ℤ)
      (hlower : ∀ i < n, IsZero ((DerivedCategory.homologyFunctor coarse i).obj M)) :
      IsZero ((DerivedCategory.homologyFunctor coarse n).obj M) := by
    let Mn := (DerivedCategory.homologyFunctor coarse n).obj M
    let presheaf : (SmallAffineZariski B S hS)ᵒᵖ ⥤ Type (u + 1) :=
      Mn.obj ⋙ forget AddCommGrpCat.{u + 1}
    have hpullback (sq : Square (SmallAffineZariski B S hS))
        (hsq : IsStandardOpenCoverSquare B S hS sq) : (sq.op.map presheaf).IsPullback :=
      (General.isPullback_sections_homology (chaoticSections B S hS) sq
        (chaoticCSquareData B S hS sq) M n hlower (hsquares sq hsq)).map
        (forget AddCommGrpCat.{u + 1})
    have hemptyZero (U : SmallAffineZariski B S hS) (hU : IsEmpty ((toScheme B S hS).obj U)) :
        Subsingleton (presheaf.obj (op U)) := by
      obtain ⟨e, -⟩ := exists_bottomDegreeIso_of_rightDerived
        ((chaoticSections B S hS).obj (op U)) (data.functor.obj (op U)) (data.unit U)
        (fun I _ ↦ data.isIso_unit_app U I) M n hlower
      have : IsZero (Mn.obj.obj (op U)) :=
        ((DerivedCategory.homologyFunctor _ n).map_isZero (hempty U hU)).of_iso e.symm
      exact AddCommGrpCat.isZero_iff_subsingleton.mp this
    have hac : Presheaf.IsSheaf (almostChaotic B S hS) presheaf := by
      rw [isSheaf_iff_isSheaf_of_type]
      intro U T hT
      by_cases hU : IsEmpty ((toScheme B S hS).obj U)
      · have := hemptyZero U hU
        intro x _
        refine ⟨(0 : Mn.obj.obj (op U)), fun Y f _ => ?_, fun _ _ => Subsingleton.elim _ _⟩
        have := hemptyZero Y ((toScheme B S hS).map f).base.hom.1.isEmpty
        exact Subsingleton.elim _ _
      · obtain htop | rfl := (mem_almostChaotic_iff B S hS).mp hT
        · exact absurd htop hU
        · exact Presieve.isSheafFor_top _
    have hzar : Presheaf.IsSheaf (topology B S hS) presheaf :=
      isSheaf_smallAffineZariski_of_almostChaotic B S hS ⟨presheaf, hac⟩
        (fun sq hsq => hpullback sq hsq)
    have hsheaf : Presheaf.IsSheaf (topology B S hS) Mn.obj :=
      Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u + 1}) hzar
    have himage : (abelianPushforward B S hS).essImage Mn :=
      ⟨⟨Mn.obj, hsheaf⟩, ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _)⟩⟩
    have : IsIso ((abelianPullbackAdjPushforward B S hS).unit.app Mn) :=
      ((abelianPullbackAdjPushforward B S hS).isIso_unit_app_iff_mem_essImage).2 himage
    have hpull : IsZero ((abelianPullback B S hS).obj Mn) :=
      ((DerivedCategory.homologyFunctor _ n).map_isZero hzero).of_iso
        (((abelianPullback B S hS).mapDerivedCategoryHomologyIso n).app M).symm
    exact ((abelianPushforward B S hS).map_isZero hpull).of_iso
      (asIso ((abelianPullbackAdjPushforward B S hS).unit.app Mn))
  obtain ⟨bound, hbound⟩ := hplus
  have hvanish : ∀ i < bound, IsZero ((DerivedCategory.homologyFunctor coarse i).obj M) :=
    (DerivedCategory.isGE_iff M bound).1 hbound
  have hall (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor coarse i).obj M) := by
    by_cases hi : i < bound
    · exact hvanish i hi
    · have hstep : ∀ offset : ℕ,
          IsZero ((DerivedCategory.homologyFunctor coarse (bound + offset)).obj M) := by
        intro offset
        induction offset using Nat.strong_induction_on with
        | h offset hypothesis =>
          apply hbottom
          intro j hj
          by_cases hsmall : j < bound
          · exact hvanish j hsmall
          · have heq : j = bound + (j - bound).toNat := by omega
            rw [heq]
            exact hypothesis (j - bound).toNat (by omega)
      have heq : i = bound + (i - bound).toNat := by omega
      rw [heq]
      exact hstep _
  have : IsIso (0 : M ⟶ M) := (DerivedCategory.isIso_iff coarse (0 : M ⟶ M)).2 (by
    intro i
    have heq : (DerivedCategory.homologyFunctor coarse i).map (0 : M ⟶ M) =
        𝟙 ((DerivedCategory.homologyFunctor coarse i).obj M) := (hall i).eq_of_src _ _
    rw [heq]
    infer_instance)
  exact (IsZero.iff_id_eq_zero M).2
    (by simpa only [zero_comp] using (IsIso.hom_inv_id (0 : M ⟶ M)).symm)

include η in
/-- **Stacks 0F1L.** Let `S_affine` be the affine opens of the scheme `S` with the chaotic
topology, for which abelian sheaves are abelian presheaves, let `S_{affine,Zar}` be the same
category with the Zariski topology, and let `ε : S_{affine,Zar} ⟶ S_affine` be the comparison.
Then the derived direct image `Rε_* : D(S_{affine,Zar}) ⟶ D(S_affine)` is fully faithful, and an
object `K` of `D⁺(S_affine)` is in its essential image if and only if

1. `RΓ(∅, K)` is zero in `D(Ab)`, and
2. whenever `U = V ∪ W` with `U, V, W` affine opens of `S` and `V, W ⊆ U` standard opens, the map
   `c^K_{U,V,W,V ∩ W}` of Stacks 0F16 is a quasi-isomorphism.

`Rε_*` is any right derived functor of `ε_*`, given with its unit `η`; condition (1) is stated
for every affine open with empty underlying scheme, and condition (2) for every square of affine
opens exhibiting `U` as the union of two standard opens with intersection the fourth corner. -/
@[stacks 0F1L]
theorem abelian_fullyFaithful_and_essImage_iff :
    Nonempty Rε.FullyFaithful ∧
      ∀ K : DerivedCategory (Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1}),
        (DerivedCategory.TStructure.t
          (C := Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1})).plus K →
        (Rε.essImage K ↔
          (∀ U : SmallAffineZariski B S hS, IsEmpty ((toScheme B S hS).obj U) →
              IsZero ((chaoticDerivedSections B S hS U).obj K)) ∧
            ∀ sq : Square (SmallAffineZariski B S hS), IsStandardOpenCoverSquare B S hS sq →
              (chaoticCSquareData B S hS sq).IsCSquareIso K) := by
  let derivedAdj := mapDerivedCategoryAdjunction (abelianPullback B S hS)
    (abelianPushforward B S hS) (abelianPullbackAdjPushforward B S hS) Rε η
  let fullyFaithful := fullyFaithfulOfDerivedAdjunction (abelianPullback B S hS)
    (abelianPushforward B S hS) (abelianPullbackAdjPushforward B S hS) Rε η derivedAdj
  refine ⟨⟨fullyFaithful⟩, fun K hplus =>
    ⟨isZero_and_isCSquareIso_of_essImage B S hS Rε η K, ?_⟩⟩
  rintro ⟨hempty, hsquares⟩
  have := fullyFaithful.full
  have := fullyFaithful.faithful
  obtain ⟨bound, hbound⟩ := hplus
  have hleft : ((abelianPullback B S hS).mapDerivedCategory.obj K).IsGE bound :=
    (DerivedCategory.isGE_iff _ _).2 (fun i hi ↦
      ((abelianPullback B S hS).map_isZero
        ((DerivedCategory.isGE_iff K _).1 hbound i hi)).of_iso
        (((abelianPullback B S hS).mapDerivedCategoryHomologyIso i).app K))
  have hright : (Rε.obj ((abelianPullback B S hS).mapDerivedCategory.obj K)).IsGE bound :=
    isGE_rightDerived_obj (abelianPushforward B S hS) Rε η _ _ hleft
  obtain ⟨cone, hconeplus, second, third, htriangle⟩ :=
    (DerivedCategory.TStructure.t
      (C := Sheaf (chaotic B S hS) AddCommGrpCat.{u + 1})).plus.distinguished_cocone_triangle
      (derivedAdj.unit.app K) ⟨bound, hbound⟩ ⟨bound, hright⟩
  have hmid := isZero_and_isCSquareIso_of_essImage B S hS Rε η _
    ⟨(abelianPullback B S hS).mapDerivedCategory.obj K, ⟨Iso.refl _⟩⟩
  have hconeSquares (sq : Square (SmallAffineZariski B S hS))
      (hsq : IsStandardOpenCoverSquare B S hS sq) :
      (chaoticCSquareData B S hS sq).IsCSquareIso cone :=
    ((chaoticCSquareData B S hS sq).isCSquareIso_two_out_of_three _ htriangle).1
      (hsquares sq hsq) (hmid.2 sq hsq)
  have hconeEmpty (U : SmallAffineZariski B S hS) (hU : IsEmpty ((toScheme B S hS).obj U)) :
      IsZero ((chaoticDerivedSections B S hS U).obj cone) :=
    isZero_chaoticDerivedSections_obj₃ B S hS U _ htriangle (hempty U hU) (hmid.1 U hU)
  have hmapUnit : IsIso ((abelianPullback B S hS).mapDerivedCategory.map
      (derivedAdj.unit.app K)) := by
    have hequal : (abelianPullback B S hS).mapDerivedCategory.map (derivedAdj.unit.app K) =
        inv (derivedAdj.counit.app ((abelianPullback B S hS).mapDerivedCategory.obj K)) := by
      apply (cancel_mono (derivedAdj.counit.app
        ((abelianPullback B S hS).mapDerivedCategory.obj K))).1
      simpa only [IsIso.inv_hom_id, Functor.id_obj] using
        derivedAdj.left_triangle_components K
    rw [hequal]
    infer_instance
  have hconeZero : IsZero ((abelianPullback B S hS).mapDerivedCategory.obj cone) :=
    ((abelianPullback B S hS).mapDerivedCategory.mapTriangle.obj
      (Triangle.mk (derivedAdj.unit.app K) second third)).isZero₃_of_isIso₁
      ((abelianPullback B S hS).mapDerivedCategory.map_distinguished _ htriangle) hmapUnit
  have : IsIso (derivedAdj.unit.app K) :=
    ((Triangle.mk (derivedAdj.unit.app K) second third).isZero₃_iff_isIso₁ htriangle).1
      (isZero_of_forall_isCSquareIso_of_abelianPullback_isZero B S hS cone hconeplus hconeEmpty
        hconeSquares hconeZero)
  exact derivedAdj.mem_essImage_of_unit_isIso K

end Derived

end AlgebraicGeometry.SmallAffineZariski

end
