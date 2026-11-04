module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.ResolutionCotangentDerivedNaturality
public import StacksFrontier.Cotangent.StandardResolutionFunctoriality
public import StacksFrontier.Cotangent.StandardResolutionIsResolution
public import StacksFrontier.Cotangent.Triangle.DifferentialSequence
public import StacksFrontier.Cotangent.Triangle.Fundamental

/-!
# The canonical identification of the third vertex of the fundamental triangle

Let `A → B → C` be ring maps with `B → C` injective, and keep the notation of Tag 08SD: `P_•` and
`Q_•` are the standard resolutions of `B` and of `C` over `A` and `Q̄_• = Q_• ⊗_{P_•} B`. Let `R_•`
be the standard resolution of `C` over `B` and `S_•` the standard resolution of `B` over `B`. This
file carries out the comparison of Remark 08SE, which identifies `Ω[Q̄_•⁄B] ⊗_{Q̄_•} C` with
`L_{C/B} = Ω[R_•⁄B] ⊗_{R_•} C`.

The route is the source's. The functoriality map `S_• → R_•` presents `R_n` as a polynomial
algebra over `S_n` *because `B → C` is injective*, so `R̄_• = R_• ⊗_{S_•} B` is again a simplicial
polynomial algebra over `B`. The commutative diagram
```
Q_•  ⟶  R_•
 ↑        ↑
P_•  ⟶  S_•  ⟶  B
```
gives a canonical map `Q̄_• = Q_• ⊗_{P_•} B ⟶ R̄_•`, and the two induced maps

`L_{C/B} = Ω[R_•⁄B] ⊗_{R_•} C ⟶ Ω[R̄_•⁄B] ⊗_{R̄_•} C ⟵ Ω[Q̄_•⁄B] ⊗_{Q̄_•} C`

are quasi-isomorphisms; composing one with the inverse of the other is the desired
identification.

## Main definitions

* `CommAlgCat.algebraOver`: `C` read as an algebra over `B` along `f : B ⟶ C`; it is taken to be
  the augmentation point of the base-changed standard resolution of Tag 08SD, so that the three
  resolutions in play are augmented to one and the same object.
* `CommAlgCat.relativeBaseChange`: the augmented simplicial `B`-algebra `R̄_• = R_• ⊗_{S_•} B`.
* `CommAlgCat.relativeBaseChangeLeg` and `CommAlgCat.baseChangedComparison`: the two canonical
  maps `R_• ⟶ R̄_•` and `Q̄_• ⟶ R̄_•`.
* `CommAlgCat.relativeBaseChangeCotangentLeg` and `CommAlgCat.baseChangedCotangentComparison`: the
  two maps of complexes of relative differentials they induce.
* `CommAlgCat.baseChangedCotangentComplexIso`: **the identification of Remark 08SE**, the second
  of those two maps followed by the inverse of the first.

## Main results

* `CommAlgCat.standardResolutionSquareMap_baseRingSquare_comm`: the commutative diagram of
  standard resolutions displayed above.
* `CommAlgCat.baseChangedStandardResolution_isPolynomialAlgebra`: every term of the base change of
  a standard resolution along an injective map is a polynomial algebra over the base. **This is
  where `B → C` injective is consumed**; it is applied twice, to `Q̄_•` over `A` and to `R̄_•` over
  `B`.
* `CommAlgCat.isIso_q_relativeBaseChangeCotangentLeg` and
  `CommAlgCat.isIso_q_baseChangedCotangentComparison`: the two maps of complexes become
  isomorphisms in `D(C)`.
* `CommAlgCat.baseChangedCotangentComplexIso_hom_comp` and
  `CommAlgCat.eq_baseChangedCotangentComplexIso`: the identification is the unique isomorphism
  whose composite with the first map is the second. This is what makes it canonical rather than
  merely existent.

## Implementation notes

**No transport between the augmentation points.** `CommAlgCat.algebraOver` is *defined* as
`(baseChangedStandardResolution A f).right`, which unfolds to `CommAlgCat.of ↥B ↥C` for the
algebra structure `f.hom.toRingHom.toAlgebra`. With that choice the augmentation points of `Q̄_•`,
of `R̄_•` and of the standard resolution `R_•` of `C` over `B` are the same object on the nose, so
the three complexes are complexes of modules over one ring and the comparison maps compose
without `eqToHom`. Reading the `B`-algebra `C` as `CommAlgCat.of B C` for an ambient
`Algebra B C` instance instead would force a transport at every step, because the ambient scalar
multiplication is only propositionally the one induced by `f`.

**The commutative diagram is functoriality in the square.** The vertical maps `P_• → S_•` and
`Q_• → R_•` change the base ring and are `CommAlgCat.standardResolutionSquareMap`; the horizontal
ones are the functoriality of the standard resolution in the algebra. That these are the same
construction at different squares is `CommAlgCat.standardResolutionSquareMap_idSquare`, after
which the diagram is `CommAlgCat.standardResolutionSquareMap_comp` applied to the two factorisations
of one square.

**The two base changes are the same lemma.** `Q̄_n` is the pushout of `P_n → Q_n` along
`P_n → B` and `R̄_n` is the pushout of `S_n → R_n` along `S_n → B`
(`CommAlgCat.standardResolution_differentials_pushout`), and in both cases the upper map is a
polynomial extension by Tag 08SD. `CommAlgCat.baseChangedStandardResolution_isPolynomialAlgebra`
is proved once, from the general fact that a pushout of a polynomial algebra is a polynomial
algebra on the same variables.

**Quasi-isomorphy is functoriality of Tag 08PU in the resolution.** Both comparison arrows are
`CommAlgCat.resolutionCotangentComplexMap` at a morphism of resolutions, and
`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso_naturality` says that such a map,
followed by the comparison of the target resolution with `Lπ_!(i^*Ω_{𝒪/B})`, is the comparison of
the source resolution. Both comparisons being isomorphisms, so is the map.

### The two carried hypotheses

Remark 08SE assumes only that `B → C` is injective, and that hypothesis is genuinely used here.
What is carried are the two trivial-Kan-fibration conditions, named `hεQ` and `hεR`: that the
augmentations `Q̄_• → C` and `R̄_• → C` are trivial Kan fibrations on underlying simplicial sets.
These are the halves of the "key fact" of Tag 08SD and of its repetition for `R̄_•` in Remark 08SE
that the source deduces from Cohomology on Sites, Lemma 21.39.12, i.e. from Tag 08RX, of which
only the column step is available in this library
(`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/FlatBaseChangeOfSimplicialModules.lean`).
The other half of that key fact — degreewise polynomiality — is *not* carried: it is proved here
from the injectivity of `B → C`, which is also what removes the hypothesis `hP` that
`CommAlgCat.exists_distTriang_fundamentalVertex_of_isResolution` has to carry.

## References

* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE)
* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite Simplicial
open AlgebraicTopology

universe u

namespace CommAlgCat

variable {A : Type u} [CommRing A] {B C : CommAlgCat.{u} A}

/-! ### The three resolutions -/

/-- `C`, read as an algebra over `B` along `f : B ⟶ C`.

This is `CommAlgCat.of ↥B ↥C` for the algebra structure `f.hom.toRingHom.toAlgebra`; it is
*defined* as the augmentation point of the base-changed standard resolution of Tag 08SD so that no
transport is needed between the augmentation points of the resolutions compared below. -/
noncomputable def algebraOver (f : B ⟶ C) : CommAlgCat.{u} ↥B :=
  (baseChangedStandardResolution A f).right

/-- The structure map of `CommAlgCat.algebraOver` is `f`. -/
theorem algebraMap_algebraOver (f : B ⟶ C) :
    algebraMap ↥B ↥(algebraOver f) = f.hom.toRingHom := rfl

/-- `B → C` read as a map of algebras over `B`. -/
noncomputable def overBase (f : B ⟶ C) :
    (CommAlgCat.of ↥B ↥B : CommAlgCat.{u} ↥B) ⟶ algebraOver f :=
  ConcreteCategory.ofHom (C := CommAlgCat.{u} ↥B)
    (X := CommAlgCat.of ↥B ↥B) (Y := algebraOver f)
    { toRingHom := f.hom.toRingHom, commutes' := fun _ => rfl }

/-- `R̄_• = R_• ⊗_{S_•} B`: the base change of the standard resolution `R_•` of `C` over `B`
along the standard resolution `S_•` of `B` over `B`, augmented to `C`. -/
noncomputable abbrev relativeBaseChange (f : B ⟶ C) :
    SimplicialObject.Augmented (CommAlgCat.{u} ↥B) :=
  baseChangedStandardResolution ↥B (overBase f)

/-- `R̄_n` is the pushout of `S_n → R_n` along the augmentation `S_n → B`. -/
theorem relativeBaseChange_isPushout (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    IsPushout
      (CommRingCat.ofHom
        (((standardResolutionFunctor ↥B).map (overBase f)).left.app n).hom.toRingHom)
      (CommRingCat.ofHom
        (standardResolutionAugmentationHom ↥B (CommAlgCat.of ↥B ↥B : CommAlgCat.{u} ↥B) n))
      (CommRingCat.ofHom (canonicalBaseChangeMap ↥B (overBase f) n))
      (CommRingCat.ofHom (algebraMap ↥B ((relativeBaseChange f).left.obj n))) := by
  exact standardResolution_differentials_pushout ↥B (overBase f) n

/-- `Q̄_n` is the pushout of `P_n → Q_n` along the augmentation `P_n → B`. -/
theorem baseChanged_isPushout (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    IsPushout
      (CommRingCat.ofHom (((standardResolutionFunctor A).map f).left.app n).hom.toRingHom)
      (CommRingCat.ofHom (standardResolutionAugmentationHom A B n))
      (CommRingCat.ofHom (canonicalBaseChangeMap A f n))
      (CommRingCat.ofHom
        (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n))) := by
  exact standardResolution_differentials_pushout A f n

/-! ### The pushout leg `R_• ⟶ R̄_•` -/

/-- The pushout leg out of the standard resolution is a map of algebras over the base ring: it is
the leg of a square whose other leg is the structure map. -/
theorem canonicalBaseChangeMap_algebraMap {R : Type u} [CommRing R]
    {S : CommAlgCat.{u} R} (g : (CommAlgCat.of R R : CommAlgCat.{u} R) ⟶ S)
    (n : SimplexCategoryᵒᵖ) (b : R) :
    canonicalBaseChangeMap R g n
        (algebraMap R ((standardResolution R S).left.obj n) b) =
      algebraMap R ((baseChangedStandardResolution R g).left.obj n) b := by
  have hw := congrArg
    (fun φ : CommRingCat.of ((standardResolution R (CommAlgCat.of R R)).left.obj n) ⟶
        CommRingCat.of ((baseChangedStandardResolution R g).left.obj n) =>
      φ.hom (algebraMap R ((standardResolution R (CommAlgCat.of R R)).left.obj n) b))
    (standardResolution_differentials_pushout R g n).w
  have hg : (((standardResolutionFunctor R).map g).left.app n).hom.toRingHom
      (algebraMap R ((standardResolution R (CommAlgCat.of R R)).left.obj n) b) =
      algebraMap R ((standardResolution R S).left.obj n) b :=
    (((standardResolutionFunctor R).map g).left.app n).hom.commutes b
  have ha : standardResolutionAugmentationHom R (CommAlgCat.of R R) n
      (algebraMap R ((standardResolution R (CommAlgCat.of R R)).left.obj n) b) = b :=
    ((standardResolution R (CommAlgCat.of R R)).hom.app n).hom.commutes b
  change canonicalBaseChangeMap R g n
      ((((standardResolutionFunctor R).map g).left.app n).hom.toRingHom
        (algebraMap R ((standardResolution R (CommAlgCat.of R R)).left.obj n) b)) =
    algebraMap R ((baseChangedStandardResolution R g).left.obj n)
      (standardResolutionAugmentationHom R (CommAlgCat.of R R) n
        (algebraMap R ((standardResolution R (CommAlgCat.of R R)).left.obj n) b)) at hw
  rw [hg, ha] at hw
  exact hw

/-- **The canonical map `R_• ⟶ R̄_•`** of Remark 08SE: degreewise the pushout leg out of the
standard resolution of `C` over `B`. -/
@[stacks 08SE "the first arrow of the comparison, R_bullet ⟶ R_bullet ⊗_{S_bullet} B"]
noncomputable def relativeBaseChangeLeg (f : B ⟶ C) :
    (standardResolution ↥B (algebraOver f)).left ⟶ (relativeBaseChange f).left where
  app n := ConcreteCategory.ofHom (C := CommAlgCat.{u} ↥B)
    (X := (standardResolution ↥B (algebraOver f)).left.obj n)
    (Y := (relativeBaseChange f).left.obj n)
    { toRingHom := canonicalBaseChangeMap ↥B (overBase f) n
      commutes' := canonicalBaseChangeMap_algebraMap (overBase f) n }
  naturality i j φ := by
    ext p
    exact (standardResolution_differentials_toBaseChange_naturality ↥B (overBase f) φ p).symm

@[simp]
theorem relativeBaseChangeLeg_apply (f : B ⟶ C) (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution ↥B (algebraOver f)).left.obj n) :
    (relativeBaseChangeLeg f).app n p = canonicalBaseChangeMap ↥B (overBase f) n p := rfl

/-- The canonical map `R_• ⟶ R̄_•` lies over the augmentations to `C`. -/
theorem relativeBaseChangeLeg_comp_hom (f : B ⟶ C) :
    relativeBaseChangeLeg f ≫ (relativeBaseChange f).hom =
      (standardResolution ↥B (algebraOver f)).hom := by
  ext n p
  exact congrArg (fun φ : _ →+* _ => φ p)
    (standardResolution_differentials_toBaseChange_augmentation ↥B (overBase f) n)

/-! ### The commutative diagram of standard resolutions -/

/-- Two commutative squares of ring maps with the same two maps are equal. -/
private theorem algebraSquare_ext {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    {X : CommAlgCat.{u} R} {X' : CommAlgCat.{u} R'}
    {sq sq' : AlgebraSquare.{u, u, u} R R' X X'}
    (hb : sq.base = sq'.base) (hm : sq.map = sq'.map) : sq = sq' := by
  obtain ⟨b, m, hbm⟩ := sq
  obtain ⟨b', m', hbm'⟩ := sq'
  subst hb
  subst hm
  rfl

/-- The square of a map of algebras over a fixed base ring: the base ring does not move. -/
noncomputable def idSquare (f : B ⟶ C) : AlgebraSquare.{u, u, u} A A B C where
  base := RingHom.id A
  map := f.hom.toRingHom
  map_algebraMap a := f.hom.commutes a

/-- Over a fixed base ring, the canonical map of standard resolutions attached to a square is the
one the functoriality of the standard resolution gives.

Both are the "variables to variables" map; the proof is the recursion `P_0 = A[B]`,
`P_{n+1} = A[P_n]` on which both constructions rest. -/
theorem standardResolutionSquareMap_idSquare (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    standardResolutionSquareMap.{u, u, u} (idSquare f) n =
      (((standardResolutionFunctor.{u, u} A).map f).left.app n).hom.toRingHom := by
  have key : ∀ m : ℕ, standardTowerMap.{u, u, u} (idSquare f) m =
      (((polynomialComonad.{u, u} A).toFunctor.iterate m).map f).hom.toRingHom := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        show mvPolynomialMapRename (RingHom.id A) ⇑(standardTowerMap.{u, u, u} (idSquare f) m) = _
        rw [ih]
        refine RingHom.ext fun p => ?_
        show (MvPolynomial.rename _) ((MvPolynomial.map (RingHom.id A)) p) = _
        rw [MvPolynomial.map_id]
        rfl
  obtain ⟨m⟩ := n
  obtain ⟨m, rfl⟩ : ∃ k : ℕ, m = SimplexCategory.mk k := ⟨m.len, rfl⟩
  have h := Functor.congr_hom (standardEndofunctor_obj.{u, u} A m) f
  refine RingHom.ext fun p => ?_
  show _ = (((standardResolutionFunctor.{u, u} A).map f).left.app (op ⦋m⦌)) p
  rw [show (((standardResolutionFunctor.{u, u} A).map f).left.app (op ⦋m⦌)) =
    (((standardEndofunctor.{u, u} A).left.obj (op ⦋m⦌)).map f) from rfl, h]
  rw [standardResolutionSquareMap_apply, key]
  rfl

/-- The square `A → B`, `B → B` of the change of base ring: the bottom row `P_• → S_•` of the
diagram of Remark 08SE. -/
noncomputable def baseRingSquareBot (X : CommAlgCat.{u} A) :
    AlgebraSquare.{u, u, u} A ↥X X (CommAlgCat.of ↥X ↥X) where
  base := algebraMap A ↥X
  map := RingHom.id ↥X
  map_algebraMap _ := rfl

/-- The square `A → B`, `C → C` of the change of base ring: the top row `Q_• → R_•` of the
diagram of Remark 08SE. -/
noncomputable def baseRingSquareTop (f : B ⟶ C) :
    AlgebraSquare.{u, u, u} A ↥B C (algebraOver f) where
  base := algebraMap A ↥B
  map := RingHom.id ↥C
  map_algebraMap a := (f.hom.commutes a).symm

private theorem baseRingSquare_comm (f : B ⟶ C) :
    (idSquare f).comp (baseRingSquareTop f) =
      (baseRingSquareBot B).comp (idSquare (overBase f)) :=
  algebraSquare_ext (RingHom.ext fun _ => rfl) (RingHom.ext fun _ => rfl)

/-- **The commutative diagram of Remark 08SE.** The square

```
Q_•  ⟶  R_•
 ↑        ↑
P_•  ⟶  S_•
```

commutes, the vertical maps being the functoriality of the standard resolution in the algebra and
the horizontal ones the change of base ring from `A` to `B`. -/
@[stacks 08SE "the commutative diagram of standard resolutions from which the canonical map \
  Q_bullet ⊗_{P_bullet} B ⟶ R_bullet ⊗_{S_bullet} B is obtained"]
theorem standardResolutionSquareMap_baseRingSquare_comm (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    (standardResolutionSquareMap.{u, u, u} (baseRingSquareTop f) n).comp
        ((((standardResolutionFunctor.{u, u} A).map f).left.app n).hom.toRingHom) =
      ((((standardResolutionFunctor.{u, u} ↥B).map (overBase f)).left.app n).hom.toRingHom).comp
        (standardResolutionSquareMap.{u, u, u} (baseRingSquareBot B) n) := by
  rw [← standardResolutionSquareMap_idSquare f n,
    ← standardResolutionSquareMap_idSquare (overBase f) n,
    ← standardResolutionSquareMap_comp, ← standardResolutionSquareMap_comp,
    baseRingSquare_comm]

/-! ### The canonical map `Q̄_• ⟶ R̄_•` -/

theorem baseChangedComparison_w (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    CommRingCat.ofHom (((standardResolutionFunctor.{u, u} A).map f).left.app n).hom.toRingHom ≫
        CommRingCat.ofHom ((canonicalBaseChangeMap ↥B (overBase f) n).comp
          (standardResolutionSquareMap.{u, u, u} (baseRingSquareTop f) n)) =
      CommRingCat.ofHom (standardResolutionAugmentationHom A B n) ≫
        CommRingCat.ofHom (algebraMap ↥B ((relativeBaseChange f).left.obj n)) := by
  ext p
  show canonicalBaseChangeMap ↥B (overBase f) n
      (standardResolutionSquareMap.{u, u, u} (baseRingSquareTop f) n
        ((((standardResolutionFunctor.{u, u} A).map f).left.app n).hom.toRingHom p)) =
    algebraMap ↥B ((relativeBaseChange f).left.obj n)
      (standardResolutionAugmentationHom A B n p)
  rw [show standardResolutionSquareMap.{u, u, u} (baseRingSquareTop f) n
        ((((standardResolutionFunctor.{u, u} A).map f).left.app n).hom.toRingHom p) =
      ((((standardResolutionFunctor.{u, u} ↥B).map (overBase f)).left.app n).hom.toRingHom)
        (standardResolutionSquareMap.{u, u, u} (baseRingSquareBot B) n p) from
    congrArg (fun φ : _ →+* _ => φ p)
      (standardResolutionSquareMap_baseRingSquare_comm f n)]
  rw [show standardResolutionAugmentationHom A B n p =
      standardResolutionAugmentationHom ↥B (CommAlgCat.of ↥B ↥B) n
        (standardResolutionSquareMap.{u, u, u} (baseRingSquareBot B) n p) from
    (standardResolutionSquareMap_augmentation_app (baseRingSquareBot B) n p).symm]
  exact congrArg (fun φ : CommRingCat.of ((standardResolution ↥B (CommAlgCat.of ↥B ↥B)).left.obj n)
      ⟶ CommRingCat.of ((relativeBaseChange f).left.obj n) =>
    φ.hom (standardResolutionSquareMap.{u, u, u} (baseRingSquareBot B) n p))
    (relativeBaseChange_isPushout f n).w

/-- The canonical ring map `Q̄_n ⟶ R̄_n`, out of the pushout. -/
noncomputable def baseChangedComparisonHom (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    (baseChangedStandardResolution A f).left.obj n →+* (relativeBaseChange f).left.obj n :=
  ((baseChanged_isPushout f n).desc
    (CommRingCat.ofHom ((canonicalBaseChangeMap ↥B (overBase f) n).comp
      (standardResolutionSquareMap.{u, u, u} (baseRingSquareTop f) n)))
    (CommRingCat.ofHom (algebraMap ↥B ((relativeBaseChange f).left.obj n)))
    (baseChangedComparison_w f n)).hom

theorem baseChangedComparisonHom_canonical (f : B ⟶ C) (n : SimplexCategoryᵒᵖ)
    (q : (standardResolution A C).left.obj n) :
    baseChangedComparisonHom f n (canonicalBaseChangeMap A f n q) =
      canonicalBaseChangeMap ↥B (overBase f) n
        (standardResolutionSquareMap.{u, u, u} (baseRingSquareTop f) n q) :=
  congrArg (fun φ : CommRingCat.of ((standardResolution A C).left.obj n) ⟶
      CommRingCat.of ((relativeBaseChange f).left.obj n) => φ.hom q)
    ((baseChanged_isPushout f n).inl_desc _ _ (baseChangedComparison_w f n))

theorem baseChangedComparisonHom_algebraMap (f : B ⟶ C) (n : SimplexCategoryᵒᵖ)
    (b : ↥B) :
    baseChangedComparisonHom f n
        (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n) b) =
      algebraMap ↥B ((relativeBaseChange f).left.obj n) b :=
  congrArg (fun φ : CommRingCat.of ↥B ⟶
      CommRingCat.of ((relativeBaseChange f).left.obj n) => φ.hom b)
    ((baseChanged_isPushout f n).inr_desc _ _ (baseChangedComparison_w f n))

theorem baseChanged_ringHom_ext (f : B ⟶ C) (n : SimplexCategoryᵒᵖ)
    {W : Type u} [CommRing W]
    {φ ψ : (baseChangedStandardResolution A f).left.obj n →+* W}
    (h₁ : ∀ q, φ (canonicalBaseChangeMap A f n q) = ψ (canonicalBaseChangeMap A f n q))
    (h₂ : ∀ b : ↥B, φ (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n) b) =
      ψ (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n) b)) :
    φ = ψ := by
  have key : (CommRingCat.ofHom φ :
        CommRingCat.of ((baseChangedStandardResolution A f).left.obj n) ⟶ CommRingCat.of W) =
      CommRingCat.ofHom ψ :=
    (baseChanged_isPushout f n).hom_ext (by ext q; exact h₁ q) (by ext b; exact h₂ b)
  exact congrArg CommRingCat.Hom.hom key

/-- The pushout leg is simplicially natural, restated for `CommAlgCat.canonicalBaseChangeMap`. -/
theorem canonicalBaseChangeMap_naturality_apply (f : B ⟶ C) {i j : SimplexCategoryᵒᵖ}
    (m : i ⟶ j) (q : (standardResolution A C).left.obj i) :
    (baseChangedStandardResolution A f).left.map m (canonicalBaseChangeMap A f i q) =
      canonicalBaseChangeMap A f j ((standardResolution A C).left.map m q) :=
  standardResolution_differentials_toBaseChange_naturality A f m q

/-- The pushout leg is compatible with the augmentation, restated for
`CommAlgCat.canonicalBaseChangeMap`. -/
theorem canonicalBaseChangeMap_augmentation_apply (f : B ⟶ C) (n : SimplexCategoryᵒᵖ)
    (q : (standardResolution A C).left.obj n) :
    ((baseChangedStandardResolution A f).hom.app n).hom.toRingHom
        (canonicalBaseChangeMap A f n q) =
      standardResolutionAugmentationHom A C n q :=
  congrArg (fun φ : _ →+* _ => φ q)
    (standardResolution_differentials_toBaseChange_augmentation A f n)

/-- **The canonical map `Q̄_• ⟶ R̄_•`** of Remark 08SE, obtained from the commutative diagram of
standard resolutions by the pushout property of `Q̄_•`. -/
@[stacks 08SE "the canonical map Q_bullet ⊗_{P_bullet} B ⟶ R_bullet ⊗_{S_bullet} B obtained from \
  the commutative diagram"]
noncomputable def baseChangedComparison (f : B ⟶ C) :
    (baseChangedStandardResolution A f).left ⟶ (relativeBaseChange f).left where
  app n := ConcreteCategory.ofHom (C := CommAlgCat.{u} ↥B)
    (X := (baseChangedStandardResolution A f).left.obj n)
    (Y := (relativeBaseChange f).left.obj n)
    { toRingHom := baseChangedComparisonHom f n
      commutes' := baseChangedComparisonHom_algebraMap f n }
  naturality i j m := by
    ext x
    change baseChangedComparisonHom f j ((baseChangedStandardResolution A f).left.map m x) =
      (relativeBaseChange f).left.map m (baseChangedComparisonHom f i x)
    refine congrArg (fun φ : (baseChangedStandardResolution A f).left.obj i →+*
        (relativeBaseChange f).left.obj j => φ x)
      (baseChanged_ringHom_ext f i
        (φ := (baseChangedComparisonHom f j).comp
          ((baseChangedStandardResolution A f).left.map m).hom.toRingHom)
        (ψ := ((relativeBaseChange f).left.map m).hom.toRingHom.comp
          (baseChangedComparisonHom f i)) ?_ ?_)
    · intro q
      change baseChangedComparisonHom f j
          ((baseChangedStandardResolution A f).left.map m (canonicalBaseChangeMap A f i q)) =
        (relativeBaseChange f).left.map m
          (baseChangedComparisonHom f i (canonicalBaseChangeMap A f i q))
      rw [canonicalBaseChangeMap_naturality_apply f m q,
        baseChangedComparisonHom_canonical, baseChangedComparisonHom_canonical,
        standardResolutionSquareMap_naturality,
        canonicalBaseChangeMap_naturality_apply (overBase f) m]
    · intro b
      change baseChangedComparisonHom f j
          ((baseChangedStandardResolution A f).left.map m
            (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj i) b)) =
        (relativeBaseChange f).left.map m
          (baseChangedComparisonHom f i
            (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj i) b))
      rw [((baseChangedStandardResolution A f).left.map m).hom.commutes b,
        baseChangedComparisonHom_algebraMap, baseChangedComparisonHom_algebraMap,
        ((relativeBaseChange f).left.map m).hom.commutes b]

/-- The canonical map `Q̄_• ⟶ R̄_•` on the pushout leg out of `Q_•`. -/
theorem baseChangedComparison_apply (f : B ⟶ C) (n : SimplexCategoryᵒᵖ)
    (q : (standardResolution A C).left.obj n) :
    (baseChangedComparison f).app n (canonicalBaseChangeMap A f n q) =
      canonicalBaseChangeMap ↥B (overBase f) n
        (standardResolutionSquareMap.{u, u, u} (baseRingSquareTop f) n q) :=
  baseChangedComparisonHom_canonical f n q

/-- The canonical map `Q̄_• ⟶ R̄_•` on the structure map from `B`. -/
theorem baseChangedComparison_algebraMap (f : B ⟶ C) (n : SimplexCategoryᵒᵖ) (b : ↥B) :
    (baseChangedComparison f).app n
        (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n) b) =
      algebraMap ↥B ((relativeBaseChange f).left.obj n) b :=
  baseChangedComparisonHom_algebraMap f n b

/-- The canonical map `Q̄_• ⟶ R̄_•` lies over the augmentations to `C`. -/
theorem baseChangedComparison_comp_hom (f : B ⟶ C) :
    baseChangedComparison f ≫ (relativeBaseChange f).hom =
      (baseChangedStandardResolution A f).hom := by
  ext n x
  show ((relativeBaseChange f).hom.app n).hom.toRingHom
      (baseChangedComparisonHom f n x) =
    ((baseChangedStandardResolution A f).hom.app n).hom.toRingHom x
  refine congrArg (fun φ : (baseChangedStandardResolution A f).left.obj n →+*
      ↥(algebraOver f) => φ x)
    (baseChanged_ringHom_ext f n
      (φ := (((relativeBaseChange f).hom.app n).hom.toRingHom).comp
        (baseChangedComparisonHom f n))
      (ψ := ((baseChangedStandardResolution A f).hom.app n).hom.toRingHom) ?_ ?_)
  · intro q
    show ((relativeBaseChange f).hom.app n).hom.toRingHom
        (baseChangedComparisonHom f n (canonicalBaseChangeMap A f n q)) =
      ((baseChangedStandardResolution A f).hom.app n).hom.toRingHom
        (canonicalBaseChangeMap A f n q)
    rw [baseChangedComparisonHom_canonical]
    rw [canonicalBaseChangeMap_augmentation_apply (overBase f) n,
      standardResolutionSquareMap_augmentation_app (baseRingSquareTop f) n q]
    exact (canonicalBaseChangeMap_augmentation_apply f n q).symm
  · intro b
    show ((relativeBaseChange f).hom.app n).hom.toRingHom
        (baseChangedComparisonHom f n
          (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n) b)) =
      ((baseChangedStandardResolution A f).hom.app n).hom.toRingHom
        (algebraMap ↥B ((baseChangedStandardResolution A f).left.obj n) b)
    rw [baseChangedComparisonHom_algebraMap]
    exact (((relativeBaseChange f).hom.app n).hom.commutes b).trans
      (((baseChangedStandardResolution A f).hom.app n).hom.commutes b).symm

/-! ### Degreewise polynomiality of a base-changed standard resolution -/

/-- The base change of a polynomial algebra is a polynomial algebra on the same variables: if `Q`
is a polynomial algebra on `ι` over `P` and `R` is the pushout of `P → Q` along `P → T`, then `R`
is a polynomial algebra on `ι` over `T`. -/
private theorem nonempty_mvPolynomialAlgEquiv_of_isPushout {P Q T R : Type u}
    [CommRing P] [CommRing Q] [CommRing T] [CommRing R] [Algebra T R]
    (g : P →+* Q) (a : P →+* T) (w : Q →+* R)
    (hpo : IsPushout (CommRingCat.ofHom g) (CommRingCat.ofHom a)
      (CommRingCat.ofHom w) (CommRingCat.ofHom (algebraMap T R)))
    {ι : Type u} (e : letI := g.toAlgebra; MvPolynomial ι P ≃ₐ[P] Q) :
    Nonempty (MvPolynomial ι T ≃ₐ[T] R) := by
  let _ : Algebra P Q := g.toAlgebra
  have hcomm : ∀ p : P, w (g p) = algebraMap T R (a p) := fun p =>
    congrArg (fun k : CommRingCat.of P ⟶ CommRingCat.of R => k.hom p) hpo.w
  let ψ : MvPolynomial ι T →ₐ[T] R := MvPolynomial.aeval fun i => w (e (MvPolynomial.X i))
  let l : Q →+* MvPolynomial ι T := (MvPolynomial.map a).comp e.symm.toRingHom
  have hl : ∀ p : P, l (g p) = MvPolynomial.C (a p) := by
    intro p
    show (MvPolynomial.map a) (e.symm (algebraMap P Q p)) = MvPolynomial.C (a p)
    rw [AlgEquiv.commutes]
    exact MvPolynomial.map_C a p
  have hw : CommRingCat.ofHom g ≫ CommRingCat.ofHom l =
      CommRingCat.ofHom a ≫ CommRingCat.ofHom (algebraMap T (MvPolynomial ι T)) :=
    CommRingCat.hom_ext (RingHom.ext hl)
  let φ : R →+* MvPolynomial ι T :=
    (hpo.desc (CommRingCat.ofHom l) (CommRingCat.ofHom (algebraMap T (MvPolynomial ι T))) hw).hom
  have hφw : ∀ x : Q, φ (w x) = l x := fun x =>
    congrArg (fun k : CommRingCat.of Q ⟶ CommRingCat.of (MvPolynomial ι T) => k.hom x)
      (hpo.inl_desc _ _ hw)
  have hφv : ∀ t : T, φ (algebraMap T R t) = algebraMap T (MvPolynomial ι T) t := fun t =>
    congrArg (fun k : CommRingCat.of T ⟶ CommRingCat.of (MvPolynomial ι T) => k.hom t)
      (hpo.inr_desc _ _ hw)
  have hψl : ∀ p : MvPolynomial ι P, ψ ((MvPolynomial.map a) p) = w (e p) := by
    have key := MvPolynomial.ringHom_ext
      (f := (ψ : MvPolynomial ι T →+* R).comp (MvPolynomial.map a))
      (g := w.comp (e : MvPolynomial ι P →+* Q))
      (fun p => by
        show ψ ((MvPolynomial.map a) (MvPolynomial.C p)) = w (e (MvPolynomial.C p))
        rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
        show algebraMap T R (a p) = w (e (algebraMap P (MvPolynomial ι P) p))
        rw [e.commutes p]
        exact (hcomm p).symm)
      (fun i => by
        show ψ ((MvPolynomial.map a) (MvPolynomial.X i)) = w (e (MvPolynomial.X i))
        rw [MvPolynomial.map_X]
        exact MvPolynomial.aeval_X _ i)
    exact fun p => congrArg (fun k : MvPolynomial ι P →+* R => k p) key
  refine ⟨AlgEquiv.ofAlgHom ψ { toRingHom := φ, commutes' := hφv } ?_ ?_⟩
  · refine AlgHom.ext fun x => ?_
    show ψ (φ x) = x
    refine congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of R => k.hom x)
      (hpo.hom_ext (k := CommRingCat.ofHom ((ψ : MvPolynomial ι T →+* R).comp φ))
        (l := CommRingCat.ofHom (RingHom.id R)) ?_ ?_)
    · refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
      show ψ (φ (w y)) = w y
      rw [hφw]
      show ψ ((MvPolynomial.map a) (e.symm y)) = w y
      rw [hψl, AlgEquiv.apply_symm_apply]
    · refine CommRingCat.hom_ext (RingHom.ext fun t => ?_)
      show ψ (φ (algebraMap T R t)) = algebraMap T R t
      rw [hφv]
      exact MvPolynomial.aeval_C _ t
  · refine AlgHom.ext fun x => ?_
    show φ (ψ x) = x
    refine congrArg (fun k : MvPolynomial ι T →+* MvPolynomial ι T => k x)
      (MvPolynomial.ringHom_ext (f := φ.comp (ψ : MvPolynomial ι T →+* R))
        (g := RingHom.id _) (fun t => ?_) (fun i => ?_))
    · show φ (ψ (MvPolynomial.C t)) = MvPolynomial.C t
      rw [MvPolynomial.aeval_C]
      exact hφv t
    · show φ (ψ (MvPolynomial.X i)) = MvPolynomial.X i
      rw [MvPolynomial.aeval_X, hφw]
      show (MvPolynomial.map a) (e.symm (e (MvPolynomial.X i))) = MvPolynomial.X i
      rw [AlgEquiv.symm_apply_apply]
      exact MvPolynomial.map_X a i

/-- **Every term of the base-changed standard resolution `Q̄_• = Q_• ⊗_{P_•} B` is a polynomial
algebra over `B`, when `B → C` is injective.**

This is the elementary half of the "key fact" of Tag 08SD. Injectivity enters through the
polynomiality of Tag 08SD, `CommAlgCat.standardResolution_isPolynomialAlgebra`, which presents
`Q_n` as a polynomial algebra over `P_n`; the base change of that presentation along the
augmentation `P_n → B` presents `Q̄_n` as a polynomial algebra over `B` on the same variables. -/
@[stacks 08SE "the degreewise polynomiality of a base-changed standard resolution, applied in \
  the remark both to Q_bullet ⊗_{P_bullet} B and to R_bullet ⊗_{S_bullet} B; this is where the \
  injectivity of B → C is used"]
theorem baseChangedStandardResolution_isPolynomialAlgebra (f : B ⟶ C)
    (hf : Function.Injective f.hom) (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebra ↥B ((baseChangedStandardResolution A f).left.obj n) := by
  obtain ⟨ι, he⟩ := standardResolution_isPolynomialAlgebra A f hf n
  exact ⟨ι, nonempty_mvPolynomialAlgEquiv_of_isPushout
    (((standardResolutionFunctor.{u, u} A).map f).left.app n).hom.toRingHom
    (standardResolutionAugmentationHom A B n)
    (canonicalBaseChangeMap A f n)
    (baseChanged_isPushout f n) he.some⟩

/-- **Every term of `R̄_• = R_• ⊗_{S_•} B` is a polynomial algebra over `B`**, when `B → C` is
injective: the functoriality map `S_• → R_•` presents `R_n` as a polynomial algebra over `S_n`, so
this is `CommAlgCat.baseChangedStandardResolution_isPolynomialAlgebra` at the base ring `B`. -/
@[stacks 08SE "R_bullet ⊗_{S_bullet} B is a simplicial polynomial algebra over B, because \
  B → C is injective"]
theorem relativeBaseChange_isPolynomialAlgebra (f : B ⟶ C) (hf : Function.Injective f.hom)
    (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebra ↥B ((relativeBaseChange f).left.obj n) :=
  baseChangedStandardResolution_isPolynomialAlgebra (overBase f) hf n

/-! ### The identification in `D(C)` -/

attribute [local instance] HasDerivedCategory.standard

/-- The complex `Ω[P_•⁄R] ⊗_{P_•} D` of an augmented simplicial `R`-algebra `ε : P_• ⟶ D`, read in
cohomological degrees `≤ 0`. -/
noncomputable abbrev augmentedCotangentCochainComplex {R : Type u} [CommRing R]
    {D : CommAlgCat.{u} R} {P : SimplicialObject (CommAlgCat.{u} R)}
    (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} R)).obj D) :
    CochainComplex (ModuleCat.{u} ↥D) ℤ :=
  ((alternatingFaceMapComplex (ModuleCat.{u} ↥D)).obj
      (resolutionOver ε ⋙ overDifferentialsFunctor)).extend
    (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- For `Q̄_•` this is the third vertex `Ω[Q̄_•⁄B] ⊗_{Q̄_•} C` of the triangle of Tag 08SD. -/
theorem augmentedCotangentCochainComplex_baseChangedStandardResolution (f : B ⟶ C) :
    augmentedCotangentCochainComplex (baseChangedStandardResolution A f).hom =
      baseChangedRelativeCotangentComplex A f := rfl

/-- A degreewise polynomial simplicial algebra is bounded by some cardinal. -/
private theorem exists_isPolynomialAlgebraBelow {R : Type u} [CommRing R]
    (P : SimplicialObject (CommAlgCat.{u} R)) (hP : ∀ n, IsPolynomialAlgebra R (P.obj n)) :
    ∃ κ : Cardinal.{u}, ∀ n, IsPolynomialAlgebraBelow R κ (P.obj n) := by
  choose ι hι using hP
  refine ⟨Cardinal.mk (Σ n : SimplexCategoryᵒᵖ, ι n), fun n => ⟨ι n, ?_, hι n⟩⟩
  refine Cardinal.mk_le_of_injective (f := fun x => (⟨n, x⟩ : Σ m : SimplexCategoryᵒᵖ, ι m)) ?_
  intro x y hxy
  exact eq_of_heq (Sigma.mk.injEq .. ▸ hxy).2

/-- `L_{C/B}` is the complex of the standard resolution of `C` over `B`. -/
noncomputable def standardCotangentComplexIso (f : B ⟶ C) :
    augmentedCotangentCochainComplex (standardResolution ↥B (algebraOver f)).hom ≅
      cotangentComplex ↥B (algebraOver f) :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor (ModuleCat.{u} ↥(algebraOver f))).mapIso
    ((alternatingFaceMapComplex (ModuleCat.{u} ↥(algebraOver f))).mapIso
      (standardResolutionOverDifferentialsIso ↥B (algebraOver f)))

/-- **The first arrow of the comparison of Remark 08SE**, the map
`L_{C/B} = Ω[R_•⁄B] ⊗_{R_•} C ⟶ Ω[R̄_•⁄B] ⊗_{R̄_•} C` induced by `R_• ⟶ R̄_•`. -/
@[stacks 08SE "the induced map L_{C/B} = Omega[R_bullet/B] ⊗ C ⟶ Omega[R_bullet ⊗_{S_bullet} \
  B / B] ⊗ C"]
noncomputable def relativeBaseChangeCotangentLeg (f : B ⟶ C) :
    cotangentComplex ↥B (algebraOver f) ⟶
      augmentedCotangentCochainComplex (relativeBaseChange f).hom :=
  (standardCotangentComplexIso f).inv ≫
    resolutionCotangentComplexMap (standardResolution ↥B (algebraOver f)).hom
      (relativeBaseChange f).hom (relativeBaseChangeLeg f) (relativeBaseChangeLeg_comp_hom f)

/-- **The second arrow of the comparison of Remark 08SE**, the map
`Ω[Q̄_•⁄B] ⊗_{Q̄_•} C ⟶ Ω[R̄_•⁄B] ⊗_{R̄_•} C` induced by `Q̄_• ⟶ R̄_•`. -/
@[stacks 08SE "the induced map Omega[Q_bullet ⊗_{P_bullet} B / B] ⊗ C ⟶ Omega[R_bullet \
  ⊗_{S_bullet} B / B] ⊗ C"]
noncomputable def baseChangedCotangentComparison (f : B ⟶ C) :
    augmentedCotangentCochainComplex (baseChangedStandardResolution A f).hom ⟶
      augmentedCotangentCochainComplex (relativeBaseChange f).hom :=
  resolutionCotangentComplexMap (baseChangedStandardResolution A f).hom
    (relativeBaseChange f).hom (baseChangedComparison f) (baseChangedComparison_comp_hom f)

/-- A morphism of resolutions with polynomial terms bounded by `κ` induces an isomorphism in
`D(D)`. -/
private theorem isIso_q_resolutionCotangentComplexMap {R : Type u} [CommRing R]
    {D : CommAlgCat.{u} R} {P P' : SimplicialObject (CommAlgCat.{u} R)}
    (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} R)).obj D)
    (ε' : P' ⟶ (SimplicialObject.const (CommAlgCat.{u} R)).obj D) (κ : Cardinal.{u})
    (hPκ : ∀ n, IsPolynomialAlgebraBelow R κ (P.obj n))
    (hP'κ : ∀ n, IsPolynomialAlgebraBelow R κ (P'.obj n)) (w : P ⟶ P') (hw : w ≫ ε' = ε)
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} R))))
    (hε' : SSet.trivialKanFibrations (Functor.whiskerRight ε' (forget (CommAlgCat.{u} R)))) :
    IsIso (DerivedCategory.Q.map (resolutionCotangentComplexMap ε ε' w hw)) := by
  have hnat := smallResolutionCotangentDerivedLowerShriekIso_naturality ε ε' κ hPκ hP'κ w hw hε hε'
  have : IsIso (DerivedCategory.Q.map (resolutionCotangentComplexMap ε ε' w hw) ≫
      (smallResolutionCotangentDerivedLowerShriekIso ε' κ hP'κ hε').hom) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (smallResolutionCotangentDerivedLowerShriekIso ε' κ hP'κ hε').hom

/-- **The first arrow of the comparison is a quasi-isomorphism.**

Both `R_•` and `R̄_•` are resolutions of `C` over `B`, so by Tag 08PU each of their complexes is
`Lπ_!(i^*Ω_{𝒪/B})` in `D(C)`, compatibly with the morphism `R_• ⟶ R̄_•` between them
(`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso_naturality`).

That `R̄_•` is a resolution is used twice over: its degreewise polynomiality is
`CommAlgCat.relativeBaseChange_isPolynomialAlgebra`, which consumes the injectivity of `B → C`,
while the trivial Kan fibration condition `hεR` is carried. -/
@[stacks 08SE "the first of the two maps is a quasi-isomorphism. CARRIED as the hypothesis \
  `hεR`: that the augmentation of R_bullet ⊗_{S_bullet} B to C is a trivial Kan fibration, the \
  half of the source's appeal to Cohomology on Sites, Lemma 21.39.12 (Tag 08RX) that this \
  library lacks. Degreewise polynomiality is NOT carried: it is proved from B → C injective"]
theorem isIso_q_relativeBaseChangeCotangentLeg (f : B ⟶ C) (hf : Function.Injective f.hom)
    (hεR : SSet.trivialKanFibrations (Functor.whiskerRight (relativeBaseChange f).hom
      (forget (CommAlgCat.{u} ↥B)))) :
    IsIso (DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f)) := by
  obtain ⟨κ₂, h₂⟩ := exists_isPolynomialAlgebraBelow _
    (relativeBaseChange_isPolynomialAlgebra f hf)
  have hR : ∀ n, IsPolynomialAlgebraBelow ↥B
      (max (standardResolutionVarCardinal ↥B (algebraOver f)) κ₂)
      ((standardResolution ↥B (algebraOver f)).left.obj n) :=
    fun n => (standardResolution_isPolynomialAlgebraBelow ↥B (algebraOver f) n).mono
      (le_max_left _ _)
  have hRbar : ∀ n, IsPolynomialAlgebraBelow ↥B
      (max (standardResolutionVarCardinal ↥B (algebraOver f)) κ₂)
      ((relativeBaseChange f).left.obj n) :=
    fun n => (h₂ n).mono (le_max_right _ _)
  rw [relativeBaseChangeCotangentLeg, Functor.map_comp]
  have := isIso_q_resolutionCotangentComplexMap
    (standardResolution ↥B (algebraOver f)).hom (relativeBaseChange f).hom
    (max (standardResolutionVarCardinal ↥B (algebraOver f)) κ₂) hR hRbar
    (relativeBaseChangeLeg f) (relativeBaseChangeLeg_comp_hom f)
    (standardResolution_isResolution ↥B (algebraOver f)).trivialKanFibration hεR
  infer_instance

/-- **The second arrow of the comparison is a quasi-isomorphism**, by Tag 08PU at the two
resolutions `Q̄_•` and `R̄_•` of `C` over `B` and its functoriality in the resolution. -/
@[stacks 08SE "the second of the two maps is a quasi-isomorphism. CARRIED as the hypotheses \
  `hεQ` and `hεR`: that the augmentations of Q_bullet ⊗_{P_bullet} B and R_bullet ⊗_{S_bullet} B \
  to C are trivial Kan fibrations, the half of Tag 08RX this library lacks. Degreewise \
  polynomiality of both is NOT carried: it is proved from B → C injective"]
theorem isIso_q_baseChangedCotangentComparison (f : B ⟶ C) (hf : Function.Injective f.hom)
    (hεQ : SSet.trivialKanFibrations (Functor.whiskerRight
      (baseChangedStandardResolution A f).hom (forget (CommAlgCat.{u} ↥B))))
    (hεR : SSet.trivialKanFibrations (Functor.whiskerRight (relativeBaseChange f).hom
      (forget (CommAlgCat.{u} ↥B)))) :
    IsIso (DerivedCategory.Q.map (baseChangedCotangentComparison f)) := by
  obtain ⟨κ₁, h₁⟩ := exists_isPolynomialAlgebraBelow _
    (baseChangedStandardResolution_isPolynomialAlgebra f hf)
  obtain ⟨κ₂, h₂⟩ := exists_isPolynomialAlgebraBelow _
    (relativeBaseChange_isPolynomialAlgebra f hf)
  have hQ : ∀ n, IsPolynomialAlgebraBelow ↥B (max κ₁ κ₂)
      ((baseChangedStandardResolution A f).left.obj n) :=
    fun n => (h₁ n).mono (le_max_left _ _)
  have hRbar : ∀ n, IsPolynomialAlgebraBelow ↥B (max κ₁ κ₂)
      ((relativeBaseChange f).left.obj n) :=
    fun n => (h₂ n).mono (le_max_right _ _)
  exact isIso_q_resolutionCotangentComplexMap
    (baseChangedStandardResolution A f).hom (relativeBaseChange f).hom (max κ₁ κ₂) hQ hRbar
    (baseChangedComparison f) (baseChangedComparison_comp_hom f) hεQ hεR

/-- **Remark 08SE.** The canonical identification of `Ω[Q̄_•⁄B] ⊗_{Q̄_•} C` with
`L_{C/B} = Ω[R_•⁄B] ⊗_{R_•} C` in `D(C)`: the second arrow of the comparison composed with the
inverse of the first.

It is characterised by `CommAlgCat.baseChangedCotangentComplexIso_hom_comp` and
`CommAlgCat.eq_baseChangedCotangentComplexIso`. -/
@[stacks 08SE "the canonical identification of Omega[Q_bullet ⊗_{P_bullet} B / B] ⊗ C with \
  L_{C/B}: the second arrow of the comparison followed by the inverse of the first. CARRIED as \
  the hypotheses `hεQ` and `hεR`, the trivial-Kan-fibration halves of Tag 08RX, which this \
  library lacks. The remark's hypothesis that B → C be injective is NOT carried but consumed"]
noncomputable def baseChangedCotangentComplexIso (f : B ⟶ C) (hf : Function.Injective f.hom)
    (hεQ : SSet.trivialKanFibrations (Functor.whiskerRight
      (baseChangedStandardResolution A f).hom (forget (CommAlgCat.{u} ↥B))))
    (hεR : SSet.trivialKanFibrations (Functor.whiskerRight (relativeBaseChange f).hom
      (forget (CommAlgCat.{u} ↥B)))) :
    DerivedCategory.Q.obj
        (augmentedCotangentCochainComplex (baseChangedStandardResolution A f).hom) ≅
      DerivedCategory.Q.obj (cotangentComplex ↥B (algebraOver f)) :=
  letI := isIso_q_baseChangedCotangentComparison f hf hεQ hεR
  letI := isIso_q_relativeBaseChangeCotangentLeg f hf hεR
  asIso (DerivedCategory.Q.map (baseChangedCotangentComparison f)) ≪≫
    (asIso (DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f))).symm

/-- Cancelling an inverse on the right. -/
private theorem comp_inv_comp_hom {D : Type*} [Category* D] {X V W : D} (g : X ⟶ W) (e : V ≅ W) :
    (g ≫ e.inv) ≫ e.hom = g := by
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- **The identification of Remark 08SE commutes with the two arrows of the comparison.** -/
@[stacks 08SE "the characterising property of the identification: composed with the first arrow \
  of the comparison it is the second, which is what 'composing one with the inverse of the other' \
  means. Same two carried hypotheses as the identification itself"]
theorem baseChangedCotangentComplexIso_hom_comp (f : B ⟶ C) (hf : Function.Injective f.hom)
    (hεQ : SSet.trivialKanFibrations (Functor.whiskerRight
      (baseChangedStandardResolution A f).hom (forget (CommAlgCat.{u} ↥B))))
    (hεR : SSet.trivialKanFibrations (Functor.whiskerRight (relativeBaseChange f).hom
      (forget (CommAlgCat.{u} ↥B)))) :
    (baseChangedCotangentComplexIso f hf hεQ hεR).hom ≫
        DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f) =
      DerivedCategory.Q.map (baseChangedCotangentComparison f) := by
  have h₁ : IsIso (DerivedCategory.Q.map (baseChangedCotangentComparison f)) :=
    isIso_q_baseChangedCotangentComparison f hf hεQ hεR
  have h₂ : IsIso (DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f)) :=
    isIso_q_relativeBaseChangeCotangentLeg f hf hεR
  show (DerivedCategory.Q.map (baseChangedCotangentComparison f) ≫
      (asIso (DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f))).inv) ≫
      DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f) = _
  exact comp_inv_comp_hom _ _

/-- **The identification of Remark 08SE is the unique isomorphism commuting with the two arrows of
the comparison.** This is what pins it down: the first arrow is an isomorphism in `D(C)`, so the
commutation determines the identification outright. -/
@[stacks 08SE "uniqueness of the identification: it is the ONLY isomorphism whose composite with \
  the first arrow of the comparison is the second. Same two carried hypotheses as the \
  identification itself"]
theorem eq_baseChangedCotangentComplexIso (f : B ⟶ C) (hf : Function.Injective f.hom)
    (hεQ : SSet.trivialKanFibrations (Functor.whiskerRight
      (baseChangedStandardResolution A f).hom (forget (CommAlgCat.{u} ↥B))))
    (hεR : SSet.trivialKanFibrations (Functor.whiskerRight (relativeBaseChange f).hom
      (forget (CommAlgCat.{u} ↥B))))
    (e : DerivedCategory.Q.obj
        (augmentedCotangentCochainComplex (baseChangedStandardResolution A f).hom) ≅
      DerivedCategory.Q.obj (cotangentComplex ↥B (algebraOver f)))
    (he : e.hom ≫ DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f) =
      DerivedCategory.Q.map (baseChangedCotangentComparison f)) :
    e = baseChangedCotangentComplexIso f hf hεQ hεR := by
  have h₂ : IsIso (DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f)) :=
    isIso_q_relativeBaseChangeCotangentLeg f hf hεR
  refine Iso.ext ((cancel_mono
    (DerivedCategory.Q.map (relativeBaseChangeCotangentLeg f))).1 ?_)
  exact he.trans (baseChangedCotangentComplexIso_hom_comp f hf hεQ hεR).symm

end CommAlgCat

end
