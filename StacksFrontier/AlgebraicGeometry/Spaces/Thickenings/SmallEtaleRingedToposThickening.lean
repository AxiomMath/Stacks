module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionSetSheafEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceQuotientQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.Deformation.ToposThickening.MorphismOfThickenings

/-!
# A thickening of algebraic spaces gives a thickening of small étale ringed topoi

Let `i : Z ⟶ Z'` be a thickening of algebraic spaces over a scheme `S` (Stacks 05ZK, in the
morphism form `AlgebraicGeometry.Space.IsThickeningHom`).  This file proves that the morphism of
small étale ringed topoi `i_small : (Sh(Z_étale), 𝒪_Z) ⟶ (Sh(Z'_étale), 𝒪_{Z'})` of Stacks 03G8
is a thickening of ringed topoi in the sense of Stacks 08M6
(`Deformation.ToposThickening.IsThickening`): its direct image is an equivalence of topoi, and its
structure map `𝒪_{Z'} ⟶ i_*𝒪_Z` is surjective with locally nilpotent kernel.  This is the
implication (1) ⇒ (2) of Stacks 0D16.

The three clauses are proved as in the source.

* The direct image is fully faithful because `i` is a closed immersion (Stacks 04E5, part (1),
  `AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion`), and it is
  essentially surjective because its essential image consists of the sheaves which are a
  singleton on every chart avoiding the image of `i`
  (`AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff_of_isClosedImmersion`), while a
  chart avoiding the image of a surjective morphism is empty.
* The structure map is surjective by Stacks 03MB
  (`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`).
* A section of `𝒪_{Z'}` over an étale chart `V` killed by the structure map pulls back to zero on
  `Z ×_{Z'} V`, which over an affine chart `V = Spec A` is the closed subscheme `Spec (A / I)`
  with all the points of `V`; so the section lies in `I`, which is contained in the nilradical.
  The affine charts cover every chart, which gives local nilpotence.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_smallEtalePushforward_of_isThickeningHom`: the direct
  image along a thickening is an equivalence of topoi.
* `AlgebraicGeometry.Space.isLocallySurjective_fSharp_of_isClosedImmersion`: the structure map
  of a closed immersion, as a map of sheaves of commutative rings, is locally surjective.
* `AlgebraicGeometry.Space.hasLocallyNilpotentKernel_of_isThickeningHom`: the kernel of the
  structure map of a thickening is locally nilpotent.
* `AlgebraicGeometry.Space.isThickening_smallEtaleRingedToposHom_of_isThickeningHom`: the
  implication (1) ⇒ (2) of Stacks 0D16.

## References

* [Stacks Project, Tag 0D16](https://stacks.math.columbia.edu/tag/0D16)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 08M6](https://stacks.math.columbia.edu/tag/08M6)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

/-- An étale chart of `X` lying entirely off the image of a surjective morphism `i : Z ⟶ X` is
empty. -/
theorem isEmpty_chartSch_of_chartPreimage_eq_empty {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : Function.Surjective (pointsMap B S hS Z.1 i.hom)) (V : SmallEtale B S hS X.1)
    (hV : chartPreimage B S hS i V = ∅) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj V.obj.left) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨y, -⟩ := surjective_pointsToScheme B S hS V.obj.left z
  have hy : y ∈ chartPreimage B S hS i V := hi _
  rw [hV] at hy
  exact hy

/-- **The direct image along a thickening of algebraic spaces is an equivalence of topoi.**
It is fully faithful because a thickening is a closed immersion, and essentially surjective
because the only condition on its essential image concerns charts lying off the image of `i`,
which are empty. -/
theorem isEquivalence_smallEtalePushforward_of_isThickeningHom {Z X : AlgebraicSpaces B S hS}
    {i : Z ⟶ X} (hi : IsThickeningHom B S hS i) :
    (smallToposMorphismTypeU B S hS i).pushforward.IsEquivalence := by
  have hci := hi.isClosedImmersion
  let hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS i hci
  let := hff.full
  let := hff.faithful
  let : (smallToposMorphismTypeU B S hS i).pushforward.EssSurj := by
    refine ⟨fun F => ?_⟩
    refine (smallEtalePushforward_essImage_iff_of_isClosedImmersion B S hS i hci F).2 ?_
    intro V hV
    have := isEmpty_chartSch_of_chartPreimage_eq_empty i hi.surjective_pointsMap V hV
    exact ⟨F.isTerminalOfBotCover _ (SmallEtale.bot_mem_topology B S hS X.1 V this)⟩
  exact { }

/-! ### The structure map is surjective -/

/-- **The structure map of a closed immersion is surjective**, read as a map of sheaves of
*commutative* rings: this is Stacks 03MB's surjectivity clause
`AlgebraicGeometry.Space.isLocallySurjective_structureSharp`, the two maps having the same
underlying map of sheaves of sets. -/
theorem isLocallySurjective_fSharp_of_isClosedImmersion {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Y.1)
      (smallEtaleRingedToposHom B S hS f).fSharp.hom := by
  have h := isLocallySurjective_structureSharp B S hS f hf
  rw [← forgetCommRingSheaf_map_fSharp B S hS f] at h
  have h' := (Presheaf.isLocallySurjective_iff_whisker_forget _ _).1 h
  rw [Presheaf.isLocallySurjective_iff_whisker_forget]
  exact h'

/-! ### The kernel of the structure map is locally nilpotent -/

/-- For a representable morphism `f : X ⟶ Y` and an étale chart `V` of `Y`, a regular function
on `V` killed by the structure map pulls back to zero along the cartesian projection
`X ×_Y V ⟶ V`. -/
theorem appTop_snd_eq_zero_of_fSharp_app_eq_zero {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (a : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op V)))
    (ha : (smallEtaleRingedToposHom B S hS f).fSharp.hom.app (op V) a = 0) :
    ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).appTop a = 0 := by
  have hcomp : ∀ g, (chartProjection B S hS f V
      (chartBaseChangeArrow B S hS f hf V)).app (structureSetSheaf B S hS X)
        (structureMapApp B S hS f V g) =
      ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).appTop g := by
    intro g
    refine (chartProjection_structureMapApp B S hS f V
      (chartBaseChangeArrow B S hS f hf V) g).trans ?_
    rw [chartPullback, chartBaseChangeMap_chartBaseChangeArrow]
    rfl
  have hsharp : ((structureSharp B S hS f).hom.app (op V)).hom a =
      ((structureSharp B S hS f).hom.app (op V)).hom 0 := by
    have h := congrArg (fun φ => ((φ.hom.app (op V)).hom a))
      (forgetCommRingSheaf_map_fSharp B S hS f)
    refine h.symm.trans ?_
    refine Eq.trans ?_ (map_zero ((structureSharp B S hS f).hom.app (op V)).hom).symm
    exact ha
  have hinv : Function.Injective (((smallEtaleDirectImageRanIso B S hS f).inv.app
      (structureRingSheaf B S hS X).ringSheaf).hom.app (op V)) := by
    refine Function.LeftInverse.injective
      (g := ((smallEtaleDirectImageRanIso B S hS f).hom.app
        (structureRingSheaf B S hS X).ringSheaf).hom.app (op V)) fun x => ?_
    have h : ((smallEtaleDirectImageRanIso B S hS f).inv.app
        (structureRingSheaf B S hS X).ringSheaf).hom.app (op V) ≫
        ((smallEtaleDirectImageRanIso B S hS f).hom.app
          (structureRingSheaf B S hS X).ringSheaf).hom.app (op V) = 𝟙 _ :=
      congrArg (fun k => k.hom.app (op V))
        ((smallEtaleDirectImageRanIso B S hS f).inv_hom_id_app
          (structureRingSheaf B S hS X).ringSheaf)
    rw [← CategoryTheory.comp_apply, h, CategoryTheory.id_apply]
  have happ : structureMapApp B S hS f V a = structureMapApp B S hS f V
      (0 : ToType ((structureRingSheaf B S hS Y).obj.obj (op V))) := by
    apply hinv
    have e := structureSharp_app_hom_eq B S hS f (op V)
    exact (congr_fun e a).symm.trans (hsharp.trans (congr_fun e _))
  exact ((hcomp a).symm.trans ((congrArg _ happ).trans (hcomp _))).trans (map_zero _)

/-- A global function on a quasi-compact scheme which pulls back to zero along a surjective
morphism is nilpotent: its basic open has empty preimage, hence is empty. -/
theorem isNilpotent_of_appTop_eq_zero_of_surjective {W V : Scheme.{u}} [CompactSpace V]
    (g : W ⟶ V) (hg : Function.Surjective g.base) (a : Γ(V, ⊤)) (ha : g.appTop a = 0) :
    IsNilpotent a := by
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot]
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨w, rfl⟩ := hg x
  have hw : w ∈ g ⁻¹ᵁ V.basicOpen a := hx
  rw [Scheme.preimage_basicOpen_top, ha, Scheme.basicOpen_zero] at hw
  exact hw

/-- **The kernel of the structure map of a thickening is locally nilpotent.**  Over an affine
étale chart `V` a function killed by the structure map pulls back to zero on `Z ×_{Z'} V`, which
surjects onto `V`, so it is nilpotent; the affine charts cover every chart. -/
theorem hasLocallyNilpotentKernel_of_isThickeningHom {Z X : AlgebraicSpaces B S hS}
    {i : Z ⟶ X} (hi : IsThickeningHom B S hS i) :
    Deformation.ToposThickening.HasLocallyNilpotentKernel.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i) := by
  have hci := hi.isClosedImmersion
  have hsurj := hi.surjective
  have : (AffineEtale.inclusion B S hS X.1).IsCoverDense (SmallEtale.topology B S hS X.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS X.1 X.2).2.isCoverDense'
  rintro ⟨U⟩ a ha
  refine ⟨_, (AffineEtale.inclusion B S hS X.1).is_cover_of_isCoverDense
    (SmallEtale.topology B S hS X.1) U, ?_⟩
  rintro W p ⟨⟨A, l, m, rfl⟩⟩
  have hnat := ConcreteCategory.congr_hom
    ((smallEtaleRingedToposHom B S hS i).fSharp.hom.naturality m.op) a
  have hm : (smallEtaleRingedToposHom B S hS i).fSharp.hom.app
      (op ((AffineEtale.inclusion B S hS X.1).obj A))
      ((smallEtaleRingedTopos B S hS X).O.obj.map m.op a) = 0 := by
    rw [← CategoryTheory.comp_apply, hnat, CategoryTheory.comp_apply, ha]
    exact RingHom.map_zero _
  have hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.1.left) := A.2
  have h0 := appTop_snd_eq_zero_of_fSharp_app_eq_zero i hci.rep _ _ hm
  have hs : Function.Surjective
      ((BigFppfOver.toScheme B S hS).map
        (hci.rep.snd A.1.1.hom)).base :=
    (hsurj.property_snd _).surj
  have hnil := isNilpotent_of_appTop_eq_zero_of_surjective _ hs _ h0
  rw [op_comp, Functor.map_comp]
  exact hnil.map ((smallEtaleRingedTopos B S hS X).O.obj.map l.op).hom

/-! ### Stacks 0D16, (1) ⇒ (2) -/

/-- **Stacks 0D16, (1) ⇒ (2).**  If `i : Z ⟶ Z'` is a thickening of algebraic spaces over `S`
(Stacks 05ZK), then the morphism `i_small : (Sh(Z_étale), 𝒪_Z) ⟶ (Sh(Z'_étale), 𝒪_{Z'})` of small
étale ringed topoi of Stacks 03G8 is a thickening of ringed topoi in the sense of Stacks 08M6:
its direct image is an equivalence, and its structure map is surjective with locally nilpotent
kernel. -/
theorem isThickening_smallEtaleRingedToposHom_of_isThickeningHom
    {Z Z' : AlgebraicSpaces B S hS} {i : Z ⟶ Z'} (hi : IsThickeningHom B S hS i) :
    Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i) :=
  ⟨isEquivalence_smallEtalePushforward_of_isThickeningHom hi,
    isLocallySurjective_fSharp_of_isClosedImmersion i hi.isClosedImmersion,
    hasLocallyNilpotentKernel_of_isThickeningHom hi⟩

end AlgebraicGeometry.Space

end
