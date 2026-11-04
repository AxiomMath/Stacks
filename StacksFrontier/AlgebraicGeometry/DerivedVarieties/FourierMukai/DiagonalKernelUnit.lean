module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeMergeCoherence
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.DiagonalKernelIdentity
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import StacksFrontier.AlgebraicGeometry.Etale.FrobeniusBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitKFlat
import StacksCore.Tactic.StacksAttribute

/-!
# The diagonal kernel is a unit for convolution

Section 0G0F of the source builds a category whose objects are the smooth proper schemes over a
base `S`, whose morphisms `X ⟶ Y` are the isomorphism classes of objects of
`D_{perf}(𝒪_{X ×_S Y})`, whose composition is the convolution

`K'' = R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K')`

of [Stacks, Tag 0FYS], and whose identity morphism of `X` is the class of
`𝒪_Δ = Δ_{X/S,*}𝒪_X`. Of the laws that construction needs, the source proves associativity and
writes *"we omit verifying that the identity morphisms are indeed identities"*.

This file supplies the omitted verification, at the level of kernels rather than of isomorphism
classes: convolving with the diagonal kernel on either side returns the kernel one started with,
by a canonical isomorphism.

## Main results

* `AlgebraicGeometry.diagonalKernelConvolutionIso` — the **left** unit law:
  `𝒪_{Δ_X} ∘ K' ≅ K'` in `D(𝒪_{X ×_S Z})`, for `f : X ⟶ S` separated and `h : Z ⟶ S` flat.
* `AlgebraicGeometry.convolutionDiagonalKernelIso` — the **right** unit law:
  `K ∘ 𝒪_{Δ_Y} ≅ K` in `D(𝒪_{X ×_S Y})`, for `g : Y ⟶ S` separated and `f : X ⟶ S` flat.

## The proof

Both laws run on the same four observations about one morphism. For the left law let
`Δ₁ : X ×_S Z ⟶ X ×_S X ×_S Z` be `(x, z) ↦ (x, x, z)`, which is
`AlgebraicGeometry.diagonalIntoTriple`. Then

1. the square with sides `Δ₁`, `pr_1 : X ×_S Z ⟶ X` over `pr_{12}` and `Δ_{X/S}` is cartesian,
   `AlgebraicGeometry.isPullback_diagonalIntoTriple`. In particular `Δ₁` is a closed immersion,
   being a base change of one;
2. `pr_{12}` is flat, being a base change of `h`, so `Δ_{X/S}` and `pr_{12}` are Tor independent
   and the derived base-change map along that square is invertible. That is [Stacks, Tag 0E23],
   `Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso` — the closed-immersion
   case of base change, which this library proves outright. The general base-change theorem
   [Stacks, Tag 08IB] is *not* used and is not needed: the morphism being pushed forward here is
   the diagonal, which is a closed immersion. Together with `Lpr_1^*𝒪_X ≅ 𝒪`
   (`Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso`) this gives
   `L pr_{12}^*𝒪_{Δ} ≅ RΔ_{1,*}𝒪`;
3. the projection formula along the closed immersion `Δ₁`, [Stacks, Tag 0B55] in the form
   `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding`,
   turns `RΔ_{1,*}𝒪 ⊗^𝐋 A` into `RΔ_{1,*}(𝒪 ⊗^𝐋 LΔ_1^*A)`, and the unit constraint of
   [Stacks, Tag 0FPT] cancels the `𝒪`. This is
   `AlgebraicGeometry.structPushforwardTensorIso`;
4. `Δ₁ ≫ pr_{23} = 𝟙` and `Δ₁ ≫ pr_{13} = 𝟙`, so the composition isomorphisms of
   [Stacks, Tag 0D5S] and [Stacks, Tag 0D5T] collapse `L pr_{23}^* ⋙ LΔ_1^*` and
   `RΔ_{1,*} ⋙ R pr_{13,*}` to the identity.

The right law is the same with `Δ₂ : X ×_S Y ⟶ X ×_S Y ×_S Y`, `(x, y) ↦ (x, y, y)`, whose
cartesian square sits over `pr_{23}` and `Δ_{Y/S}` and is obtained by pasting against
`AlgebraicGeometry.isPullback_fourierMukaiPr12_pr23`. There `pr_{23}` is flat because it is a
base change of `f`. One extra step is needed: the convolution puts the kernel being pushed
forward in the *second* tensor slot, and the projection formula wants it in the first, so the
commutativity constraint of [Stacks, Tag 0FPT] —
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.tensorFlipSlotIso` — is applied first.

## Implementation notes

*Hypotheses.* Section 0G0F takes all its schemes smooth and proper over `S`. What the two laws
actually use is separatedness of the morphism whose diagonal is taken (to make that diagonal a
closed immersion) and flatness of the other one (to make the relevant projection flat, hence Tor
independent from the diagonal). Both follow from smooth and proper, so these statements cover
the source's case and are strictly more general. No quasi-compactness, quasi-separatedness,
Noetherian or perfectness hypothesis occurs.

*Kernels, not isomorphism classes.* Morphisms of the category of Section 0G0F are isomorphism
classes, so what that construction needs is exactly an isomorphism of kernels, which is what is
produced below. Nothing here asserts that the isomorphisms are coherent with composition; the
category itself is not built, because two of the four clauses of its construction are not
available in this library — see below.

*No `@[stacks 0G0F]` attribute.* Tag 0G0F is the assertion that the category exists. Of its
construction, clause (4) — perfectness of the identity kernel — is
`AlgebraicGeometry.isPerfect_diagonalKernel_ringedSpace` in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/DiagonalKernelPerfect.lean`, and the
unit laws are here. Clause (3), that the convolution of two perfect kernels is perfect, is the
perfectness half of [Stacks, Tag 0B91] at a general base, which this library does not carry (see
the attribute note at
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatPushforwardBaseChange.lean:233`); and
associativity runs on [Stacks, Tag 08IB], carried as the hypothesis
`AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent` throughout
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Composition.lean`. So no declaration
here states the tag.

*The model of the derived categories.* As in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Composition.lean`, everything is
read at `CategoryTheory.HasDerivedCategory.standard`, given a raised local instance priority so
that the locally small model arriving with the imports does not compete.

## References

* [Stacks Project, Tag 0G0F](https://stacks.math.columbia.edu/tag/0G0F)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleFrobenius (derivedStructureSheaf)

universe u

namespace AlgebraicGeometry

-- The priority selects the standard model of the derived categories, the one the convolution
-- kernel and the diagonal kernel are read at, over the locally small model arriving with the
-- imports.
attribute [local instance 100000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula (projectionFormulaMap
  isIso_projectionFormulaMap_of_isClosedEmbedding)

/-! ### The structure sheaf in degree zero, and the projection formula at it -/

/-- **`Ri_*𝒪_V ⊗^𝐋 A ≅ Ri_*(Li^*A)` for a closed immersion `i : V ⟶ W`.**

The projection-formula morphism of [Stacks, Tag 0B53] is invertible along a morphism whose base
map is a closed embedding, [Stacks, Tag 0B55] — this is
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding`,
which needs nothing of `A` — and the unit constraint of [Stacks, Tag 0FPT] then removes the
`𝒪_V` from `𝒪_V ⊗^𝐋 Li^*A`.

This is the step of Section 0G0F's omitted unit verification that produces the kernel back out
of the convolution, and it is used for both unit laws. -/
def structPushforwardTensorIso {V W : Scheme.{u}} (i : V ⟶ W) [IsClosedImmersion i]
    (A : DerivedCategory W.Modules) :
    (dtenR W A).obj ((dpush i).obj (derivedStructureSheaf V)) ≅ (dpush i).obj ((dpull i).obj A) :=
  (@asIso _ _ _ _ _ (isIso_projectionFormulaMap_of_isClosedEmbedding i.toLRSHom.toShHom
      i.isClosedEmbedding _ A)) ≪≫
    (dpush i).mapIso
      ((Stacks.RingedSpace.derivedTensorLeftUnitorNatIso V.toRingedSpace).app ((dpull i).obj A))

/-! ### The left unit law -/

section Left

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (h : Z ⟶ S)

/-- `Δ₁ : X ×_S Z ⟶ X ×_S X ×_S Z`, the morphism `(x, z) ↦ (x, x, z)`: the diagonal of `f`
crossed with `Z`. It is the base change of `Δ_{X/S}` along `pr_{12}`. -/
def diagonalIntoTriple : pullback f h ⟶ fourierMukaiTripleProduct f f h :=
  pullback.lift (pullback.fst f h ≫ pullback.diagonal f) (pullback.snd f h) (by
    rw [Category.assoc, ← Category.assoc (pullback.diagonal f), pullback.diagonal_snd,
      Category.id_comp]
    exact pullback.condition)

/-- `pr_{12} ∘ Δ₁ = Δ_{X/S} ∘ pr_1`. -/
@[simp] lemma diagonalIntoTriple_pr12 :
    diagonalIntoTriple f h ≫ fourierMukaiPr12 f f h =
      pullback.fst f h ≫ pullback.diagonal f :=
  pullback.lift_fst _ _ _

/-- `pr_3 ∘ Δ₁ = pr_2`. -/
@[simp] lemma diagonalIntoTriple_pr3 :
    diagonalIntoTriple f h ≫ fourierMukaiPr3 f f h = pullback.snd f h :=
  pullback.lift_snd _ _ _

/-- `pr_{13} ∘ Δ₁ = 𝟙`: the morphism `(x, z) ↦ (x, x, z)` followed by the projection to the
first and third factors is the identity. -/
@[simp] lemma diagonalIntoTriple_pr13 :
    diagonalIntoTriple f h ≫ fourierMukaiPr13 f f h = 𝟙 _ := by
  ext <;> simp [reassoc_of% (diagonalIntoTriple_pr12 f h)]

/-- `pr_{23} ∘ Δ₁ = 𝟙`: the morphism `(x, z) ↦ (x, x, z)` followed by the projection to the
second and third factors is the identity. -/
@[simp] lemma diagonalIntoTriple_pr23 :
    diagonalIntoTriple f h ≫ fourierMukaiPr23 f f h = 𝟙 _ := by
  ext <;> simp [reassoc_of% (diagonalIntoTriple_pr12 f h)]

/-- **`Δ₁` is the base change of `Δ_{X/S}` along `pr_{12}`.** The square

`X ×_S Z ⟶ X ×_S X ×_S Z` over `X ⟶ X ×_S X`, with vertical maps `pr_1` and `pr_{12}`,

is cartesian: pasting it with the cartesian square defining the triple product gives the square
`X ×_S Z ⟶ Z` over `X ⟶ S`, which is cartesian, so the left square is by
`CategoryTheory.IsPullback.of_right`. -/
lemma isPullback_diagonalIntoTriple :
    IsPullback (diagonalIntoTriple f h) (pullback.fst f h) (fourierMukaiPr12 f f h)
      (pullback.diagonal f) := by
  have hb : pullback.diagonal f ≫ (pullback.snd f f ≫ f) = f := by
    rw [← Category.assoc, pullback.diagonal_snd, Category.id_comp]
  refine IsPullback.of_right (h₁₂ := fourierMukaiPr3 f f h) (v₁₃ := h) ?_
    (diagonalIntoTriple_pr12 f h)
    (IsPullback.of_hasPullback (pullback.snd f f ≫ f) h).flip
  rw [diagonalIntoTriple_pr3, hb]
  exact (IsPullback.of_hasPullback f h).flip

variable [IsSeparated f] [Flat h]

/-- `Δ₁` is a closed immersion, being a base change of the closed immersion `Δ_{X/S}`. -/
instance isClosedImmersion_diagonalIntoTriple :
    IsClosedImmersion (diagonalIntoTriple f h) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_diagonalIntoTriple f h).flip inferInstance

/-- **`L pr_{12}^*𝒪_Δ ≅ RΔ_{1,*}𝒪`.** Base change along the cartesian square of
`isPullback_diagonalIntoTriple`, which is invertible by [Stacks, Tag 0E23] — the diagonal is a
closed immersion and `pr_{12}`, a base change of the flat `h`, is Tor independent from it — and
then `L pr_1^*𝒪_X ≅ 𝒪`. -/
def diagonalKernelPullbackIso :
    (dpull (fourierMukaiPr12 f f h)).obj (diagonalKernel f) ≅
      (dpush (diagonalIntoTriple f h)).obj (derivedStructureSheaf (pullback f h)) :=
  (Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso
      (isPullback_diagonalIntoTriple f h) (torIndependent_of_flat_right _ _)).app _ ≪≫
    (dpush (diagonalIntoTriple f h)).mapIso
      (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso
        (pullback.fst f h).toLRSHom.toShHom)

/-- `L pr_{23}^* ⋙ LΔ_1^* ≅ 𝟭`: the composition isomorphism of [Stacks, Tag 0D5S] at
`Δ₁ ≫ pr_{23} = 𝟙`, followed by `L(𝟙)^* ≅ 𝟭`. -/
def diagonalIntoTriplePullbackCollapse :
    dpull (fourierMukaiPr23 f f h) ⋙ dpull (diagonalIntoTriple f h) ≅
      𝟭 (DerivedCategory (pullback f h).Modules) :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (diagonalIntoTriple f h).toLRSHom.toShHom (fourierMukaiPr23 f f h).toLRSHom.toShHom ≪≫
    eqToIso (congrArg
      (fun m : (pullback f h).toRingedSpace ⟶ (pullback f h).toRingedSpace => derivedPullback m)
      (congrArg (fun m : pullback f h ⟶ pullback f h => m.toLRSHom.toShHom)
        (diagonalIntoTriple_pr23 f h))) ≪≫
    Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso
      (pullback f h).toRingedSpace

/-- `RΔ_{1,*} ⋙ R pr_{13,*} ≅ 𝟭`: the composition isomorphism of [Stacks, Tag 0D5T] at
`Δ₁ ≫ pr_{13} = 𝟙`, followed by `R(𝟙)_* ≅ 𝟭`. -/
def diagonalIntoTriplePushforwardCollapse :
    dpush (diagonalIntoTriple f h) ⋙ dpush (fourierMukaiPr13 f f h) ≅
      𝟭 (DerivedCategory (pullback f h).Modules) :=
  derivedPushforwardCompIso (diagonalIntoTriple f h).toLRSHom.toShHom
      (fourierMukaiPr13 f f h).toLRSHom.toShHom ≪≫
    eqToIso (congrArg
      (fun m : (pullback f h).toRingedSpace ⟶ (pullback f h).toRingedSpace => derivedPushforward m)
      (congrArg (fun m : pullback f h ⟶ pullback f h => m.toLRSHom.toShHom)
        (diagonalIntoTriple_pr13 f h))) ≪≫
    Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso
      (pullback f h).toRingedSpace

/-- **The left unit law of Section 0G0F, at the level of kernels.** For `f : X ⟶ S` separated
and `h : Z ⟶ S` flat, convolving the diagonal kernel `𝒪_{Δ_{X/S}}` with a kernel `K'` on
`X ×_S Z` returns `K'`:

`R pr_{13,*}(L pr_{12}^*𝒪_Δ ⊗^𝐋 L pr_{23}^*K') ≅ K'`.

This is half of the verification the source omits when it says *"we omit verifying that the
identity morphisms are indeed identities"*. The proof is the chain of the module docstring:
base change along the cartesian square of `isPullback_diagonalIntoTriple`, the projection
formula along the closed immersion `Δ₁`, and the two composition isomorphisms at
`Δ₁ ≫ pr_{23} = 𝟙` and `Δ₁ ≫ pr_{13} = 𝟙`. -/
def diagonalKernelConvolutionIso (K' : DerivedCategory (pullback f h).Modules) :
    fourierMukaiConvolution f f h (diagonalKernel f) K' ≅ K' :=
  (dpush (fourierMukaiPr13 f f h)).mapIso
      ((dtenR (fourierMukaiTripleProduct f f h)
            ((dpull (fourierMukaiPr23 f f h)).obj K')).mapIso
          (diagonalKernelPullbackIso f h) ≪≫
        structPushforwardTensorIso (diagonalIntoTriple f h)
          ((dpull (fourierMukaiPr23 f f h)).obj K') ≪≫
        (dpush (diagonalIntoTriple f h)).mapIso
          ((diagonalIntoTriplePullbackCollapse f h).app K')) ≪≫
    (diagonalIntoTriplePushforwardCollapse f h).app K'

end Left

/-! ### The right unit law -/

section Right

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- `Δ₂ : X ×_S Y ⟶ X ×_S Y ×_S Y`, the morphism `(x, y) ↦ (x, y, y)`: `X` crossed with the
diagonal of `g`. It is the base change of `Δ_{Y/S}` along `pr_{23}`. -/
def diagonalIntoTripleRight : pullback f g ⟶ fourierMukaiTripleProduct f g g :=
  pullback.lift (𝟙 _) (pullback.snd f g) (by rw [Category.id_comp])

/-- `pr_{12} ∘ Δ₂ = 𝟙`. -/
@[simp] lemma diagonalIntoTripleRight_pr12 :
    diagonalIntoTripleRight f g ≫ fourierMukaiPr12 f g g = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- `pr_3 ∘ Δ₂ = pr_2`. -/
@[simp] lemma diagonalIntoTripleRight_pr3 :
    diagonalIntoTripleRight f g ≫ fourierMukaiPr3 f g g = pullback.snd f g :=
  pullback.lift_snd _ _ _

/-- `pr_{13} ∘ Δ₂ = 𝟙`. -/
@[simp] lemma diagonalIntoTripleRight_pr13 :
    diagonalIntoTripleRight f g ≫ fourierMukaiPr13 f g g = 𝟙 _ := by
  ext <;> simp [reassoc_of% (diagonalIntoTripleRight_pr12 f g)]

/-- `pr_{23} ∘ Δ₂ = Δ_{Y/S} ∘ pr_2`. -/
@[simp] lemma diagonalIntoTripleRight_pr23 :
    diagonalIntoTripleRight f g ≫ fourierMukaiPr23 f g g =
      pullback.snd f g ≫ pullback.diagonal g := by
  ext <;> simp [reassoc_of% (diagonalIntoTripleRight_pr12 f g)]

/-- **`Δ₂` is the base change of `Δ_{Y/S}` along `pr_{23}`.** Pasting the square against
`AlgebraicGeometry.isPullback_fourierMukaiPr12_pr23` — the statement that the triple product is
the fibre product of `X ×_S Y` and `Y ×_S Y` over `Y` — leaves the square with two identity
sides, which is cartesian. -/
lemma isPullback_diagonalIntoTripleRight :
    IsPullback (diagonalIntoTripleRight f g) (pullback.snd f g) (fourierMukaiPr23 f g g)
      (pullback.diagonal g) := by
  refine IsPullback.of_right (h₁₂ := fourierMukaiPr12 f g g) ?_
    (diagonalIntoTripleRight_pr23 f g) (isPullback_fourierMukaiPr12_pr23 f g g)
  rw [diagonalIntoTripleRight_pr12, pullback.diagonal_fst]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

/-- `pr_{23} : X ×_S Y ×_S Y ⟶ Y ×_S Y` is flat when `f` is: it is a base change of
`pr_2 : X ×_S Y ⟶ Y`, itself a base change of `f`. -/
instance flat_fourierMukaiPr23 [Flat f] : Flat (fourierMukaiPr23 f g g) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_fourierMukaiPr12_pr23 f g g)
    inferInstance

/-- `Δ₂` is a closed immersion, being a base change of the closed immersion `Δ_{Y/S}`. -/
instance isClosedImmersion_diagonalIntoTripleRight [IsSeparated g] :
    IsClosedImmersion (diagonalIntoTripleRight f g) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_diagonalIntoTripleRight f g).flip inferInstance

/-- **`L pr_{23}^*𝒪_{Δ_Y} ≅ RΔ_{2,*}𝒪`**, by [Stacks, Tag 0E23] along the cartesian square of
`isPullback_diagonalIntoTripleRight` followed by `L pr_2^*𝒪_Y ≅ 𝒪`. -/
def diagonalKernelPullbackIsoRight [IsSeparated g] [Flat f] :
    (dpull (fourierMukaiPr23 f g g)).obj (diagonalKernel g) ≅
      (dpush (diagonalIntoTripleRight f g)).obj (derivedStructureSheaf (pullback f g)) :=
  (Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso
      (isPullback_diagonalIntoTripleRight f g) (torIndependent_of_flat_right _ _)).app _ ≪≫
    (dpush (diagonalIntoTripleRight f g)).mapIso
      (Stacks.Cohomology.DerivedProjectionFormula.derivedPullbackUnitIso
        (pullback.snd f g).toLRSHom.toShHom)

/-- `L pr_{12}^* ⋙ LΔ_2^* ≅ 𝟭`, by [Stacks, Tag 0D5S] at `Δ₂ ≫ pr_{12} = 𝟙`. -/
def diagonalIntoTripleRightPullbackCollapse :
    dpull (fourierMukaiPr12 f g g) ⋙ dpull (diagonalIntoTripleRight f g) ≅
      𝟭 (DerivedCategory (pullback f g).Modules) :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      (diagonalIntoTripleRight f g).toLRSHom.toShHom
      (fourierMukaiPr12 f g g).toLRSHom.toShHom ≪≫
    eqToIso (congrArg
      (fun m : (pullback f g).toRingedSpace ⟶ (pullback f g).toRingedSpace => derivedPullback m)
      (congrArg (fun m : pullback f g ⟶ pullback f g => m.toLRSHom.toShHom)
        (diagonalIntoTripleRight_pr12 f g))) ≪≫
    Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso
      (pullback f g).toRingedSpace

/-- `RΔ_{2,*} ⋙ R pr_{13,*} ≅ 𝟭`, by [Stacks, Tag 0D5T] at `Δ₂ ≫ pr_{13} = 𝟙`. -/
def diagonalIntoTripleRightPushforwardCollapse :
    dpush (diagonalIntoTripleRight f g) ⋙ dpush (fourierMukaiPr13 f g g) ≅
      𝟭 (DerivedCategory (pullback f g).Modules) :=
  derivedPushforwardCompIso (diagonalIntoTripleRight f g).toLRSHom.toShHom
      (fourierMukaiPr13 f g g).toLRSHom.toShHom ≪≫
    eqToIso (congrArg
      (fun m : (pullback f g).toRingedSpace ⟶ (pullback f g).toRingedSpace => derivedPushforward m)
      (congrArg (fun m : pullback f g ⟶ pullback f g => m.toLRSHom.toShHom)
        (diagonalIntoTripleRight_pr13 f g))) ≪≫
    Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso
      (pullback f g).toRingedSpace

/-- **The right unit law of Section 0G0F, at the level of kernels.** For `g : Y ⟶ S` separated
and `f : X ⟶ S` flat, convolving a kernel `K` on `X ×_S Y` with the diagonal kernel
`𝒪_{Δ_{Y/S}}` returns `K`:

`R pr_{13,*}(L pr_{12}^*K ⊗^𝐋 L pr_{23}^*𝒪_{Δ_Y}) ≅ K`.

This is the other half of the verification the source omits. The proof is that of
`diagonalKernelConvolutionIso` preceded by the commutativity constraint of [Stacks, Tag 0FPT],
which moves the pushed-forward factor into the slot the projection formula of
[Stacks, Tag 0B53] puts a direct image in. -/
def convolutionDiagonalKernelIso [IsSeparated g] [Flat f]
    (K : DerivedCategory (pullback f g).Modules) :
    fourierMukaiConvolution f g g K (diagonalKernel g) ≅ K :=
  (dpush (fourierMukaiPr13 f g g)).mapIso
      ((DerivedTensorProduct.tensorFlipSlotIso
            (Stacks.RingedSpace.toRingedSite (fourierMukaiTripleProduct f g g).toRingedSpace)
            (canonicalDerivedTensorProduct (fourierMukaiTripleProduct f g g).toRingedSpace.sheaf)
            ((dpull (fourierMukaiPr23 f g g)).obj (diagonalKernel g))).symm.app
          ((dpull (fourierMukaiPr12 f g g)).obj K) ≪≫
        ((derivedTensorProductFunctor (fourierMukaiTripleProduct f g g).toRingedSpace.sheaf).mapIso
          (diagonalKernelPullbackIsoRight f g)).app ((dpull (fourierMukaiPr12 f g g)).obj K) ≪≫
        structPushforwardTensorIso (diagonalIntoTripleRight f g)
          ((dpull (fourierMukaiPr12 f g g)).obj K) ≪≫
        (dpush (diagonalIntoTripleRight f g)).mapIso
          ((diagonalIntoTripleRightPullbackCollapse f g).app K)) ≪≫
    (diagonalIntoTripleRightPushforwardCollapse f g).app K

end Right

end AlgebraicGeometry

end
