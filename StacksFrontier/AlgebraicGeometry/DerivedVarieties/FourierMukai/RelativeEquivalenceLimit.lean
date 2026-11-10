module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitPerfectObjects
import StacksCore.Tactic.StacksAttribute

/-!
# A relative equivalence over a limit of schemes comes from a finite stage

Let `S = lim_{i ∈ I} S_i` be the limit of a directed inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms `g_{i'i} : S_{i'} ⟶ S_i`, and let `0 ∈ I`
be a chosen index — the situation of [Stacks, Tag 09RD], `AlgebraicGeometry.DescentSituation`.
Let `X_0 ⟶ S_0` and `Y_0 ⟶ S_0` be smooth and proper, and put `X_i = X_0 ×_{S_0} S_i`,
`X = X_0 ×_{S_0} S`, and likewise for `Y_0`. If `K` is the Fourier-Mukai kernel of a relative
equivalence from `X` to `Y` over `S` ([Stacks, Tag 0G0I]), then for **some** `i ≥ 0` there is a
Fourier-Mukai kernel of a relative equivalence from `X_i` to `Y_i` over `S_i`. This is
[Stacks, Tag 0G0L].

## Main definitions

* `AlgebraicGeometry.baseChangeStage` — the comparison `X_0 ×_{S_0} T' ⟶ X_0 ×_{S_0} T`
  attached to a factorisation `T' ⟶ T ⟶ S_0`.
* `AlgebraicGeometry.baseChangeProduct` — the induced comparison of fibre products
  `X_{T'} ×_{T'} Y_{T'} ⟶ X_T ×_T Y_T`. Taking `T` a stage and `T' = S` gives the projection of
  the tower of fibre products, and taking two stages gives its transition morphism.
* `AlgebraicGeometry.fourierMukaiConvolutionMapIso` — the convolution kernel of
  [Stacks, Tag 0FYS] transported along isomorphisms of its two arguments.

## Main results

* `AlgebraicGeometry.exists_isRelativeEquivalenceKernel_of_descentSituation` —
  **[Stacks, Tag 0G0L]**.

## Implementation notes

*The tower.* With `X_T = X_0 ×_{S_0} T` for a scheme `T` over `S_0`, written as the chosen
`pullback x s` for `x : X_0 ⟶ S_0` and `s : T ⟶ S_0` with structure morphism
`pullback.snd x s : X_T ⟶ T`, both the stages `X_i` and the limit `X` are *direct* base changes
of one fixed morphism `X_0 ⟶ S_0`: the stage `i` is `s = g_{i0}` and the limit is `s = f_0`.
So no iterated fibre product has to be identified anywhere, and the comparison morphisms of the
tower are all instances of one construction, `baseChangeProduct`, attached to a factorisation
`u ≫ s = s'`. Its cocycle identity is `baseChangeProduct_comp`, and the composition
isomorphism of derived pullback along it is `Stacks.DerivedPullback.schemeFactorIso`.

*Which side of the fibre product.* The source writes `X_i = S_i ×_{S_0} X_0`; here the base
change is taken on the other side, as `X_0 ×_{S_0} S_i` with structure morphism `pullback.snd`.
The two differ by the symmetry of the fibre product, so nothing of the statement changes, and
this is the side at which
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/RelativeEquivalenceBaseChange.lean`
states [Stacks, Tag 0G0K], whose base change `X ×_S S₁` the stages below are instances of.

*What is proved here and what is granted.* The source's proof of [Stacks, Tag 0G0L] cites
exactly five inputs, and this tree has none of them in a form that can be applied; each is
therefore carried as an explicit hypothesis, and what is proved below is the assembly that the
source's proof performs with them. Nothing about relative equivalences is assumed: every carried
hypothesis is a statement about perfect objects, diagonal kernels and convolution kernels alone,
so the theorem is not vacuous — see the attribute string on the main theorem for the one-by-one
account.

* `h09RFobj` and `h09RFiso` are the two halves of [Stacks, Tag 09RF], essential surjectivity and
  the descent of an isomorphism, read along the tower of fibre products. The tower *is* a
  situation of [Stacks, Tag 09RD]: its transitions are affine and its stages quasi-compact and
  quasi-separated, both by base change, and its limit is `X ×_S Y`, which is
  `AlgebraicGeometry.Scheme.isLimitBaseChangeCone`
  (`StacksFrontier/AlgebraicGeometry/Limits/FinitePresentationDescent.lean:243`), packaged as
  `AlgebraicGeometry.directedBaseChangeDescentSituation`
  (`StacksFrontier/AlgebraicGeometry/Flatness/PureModules/PurityLimitStageDirected.lean:191`). What
  is missing is the colimit property itself: the module
  `StacksFrontier/AlgebraicGeometry/Perfect/LimitPerfectObjects.lean` proves only that the
  comparison functors `D_perf(𝒪_{S_i}) ⥤ D_perf(𝒪_S)` exist and cohere, and its own clause
  labels (lines 142, 154, 246, 286) record that neither full faithfulness nor essential
  surjectivity is included.
* `hbc` is the pair of base-change isomorphisms that the source's proof of [Stacks, Tag 0G0K]
  establishes: that the diagonal kernel of [Stacks, Tag 0FYV] and the convolution kernel of
  [Stacks, Tag 0FYS] both commute with base change. They are proved in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/RelativeEquivalenceBaseChange.lean`
  as `diagonalKernelBaseChangeIso` (line 404) and `convolutionBaseChangeIso` (line 427), but both
  are `private` there, and only their combination
  `AlgebraicGeometry.isRelativeEquivalenceKernel_derivedPullback` (line 518, the public
  [Stacks, Tag 0G0K]) is exported; that combination transports the kernel property from a base to
  a base change, which is the direction opposite to the one the proof below needs.
* `hperf` is the perfectness of those same two objects: for the diagonal kernel this is
  [Stacks, Tag 0FDP] together with [Stacks, Tag 0B6G], and for the convolution kernel it is
  [Stacks, Tag 0B91]. This tree's [Stacks, Tag 0B6G]
  (`StacksFrontier/AlgebraicGeometry/MoreMorphisms/PerfectMorphism/ProperDirectImage.lean:190`)
  grants the finite-Tor-dimension half of its own input, and its [Stacks, Tag 0B91]
  (`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatPushforwardBaseChange.lean:263`) proves only
  the base-change half of that lemma's conclusion, in tensor form, and not the perfectness half.

*Why the conclusion is an existential over the index.* The source asserts the existence of
*some* `i ≥ 0` carrying a kernel; the index produced below is obtained twice from the descent of
an isomorphism, once for each of the two displayed isomorphisms of [Stacks, Tag 0G0I], and is in
general strictly larger than the index at which the kernel itself first descends.

## References

* [Stacks Project, Tag 0G0L](https://stacks.math.columbia.edu/tag/0G0L)
* [Stacks Project, Tag 0G0I](https://stacks.math.columbia.edu/tag/0G0I)
* [Stacks Project, Tag 0G0K](https://stacks.math.columbia.edu/tag/0G0K)
* [Stacks Project, Tag 09RD](https://stacks.math.columbia.edu/tag/09RD)
* [Stacks Project, Tag 09RF](https://stacks.math.columbia.edu/tag/09RF)
* [Stacks Project, Tag 0B6G](https://stacks.math.columbia.edu/tag/0B6G)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0FDP](https://stacks.math.columbia.edu/tag/0FDP)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

universe v u

/-! ### The comparison morphisms of a tower of base changes -/

section Comparison

variable {S₀ X₀ Y₀ T T' T'' : Scheme.{u}} {s : T ⟶ S₀} {s' : T' ⟶ S₀} {s'' : T'' ⟶ S₀}
  {u : T' ⟶ T} {v : T'' ⟶ T'} {w : T'' ⟶ T}

/-- The comparison `X₀ ×_{S₀} T' ⟶ X₀ ×_{S₀} T` attached to a factorisation `u ≫ s = s'` of a
morphism `s' : T' ⟶ S₀` through `s : T ⟶ S₀`. -/
def baseChangeStage (x : X₀ ⟶ S₀) (hu : u ≫ s = s') : pullback x s' ⟶ pullback x s :=
  pullback.map x s' x s (𝟙 X₀) u (𝟙 S₀) (by simp) (by simp [hu])

@[reassoc (attr := simp)]
lemma baseChangeStage_fst (x : X₀ ⟶ S₀) (hu : u ≫ s = s') :
    baseChangeStage x hu ≫ pullback.fst x s = pullback.fst x s' := by
  simp [baseChangeStage, pullback.map]

@[reassoc (attr := simp)]
lemma baseChangeStage_snd (x : X₀ ⟶ S₀) (hu : u ≫ s = s') :
    baseChangeStage x hu ≫ pullback.snd x s = pullback.snd x s' ≫ u := by
  simp [baseChangeStage, pullback.map]

/-- The comparison morphisms of a tower of base changes compose. -/
lemma baseChangeStage_comp (x : X₀ ⟶ S₀) (hu : u ≫ s = s') (hv : v ≫ s' = s'')
    (hw : w ≫ s = s'') (hvu : v ≫ u = w) :
    baseChangeStage x hv ≫ baseChangeStage x hu = baseChangeStage x hw := by
  apply pullback.hom_ext <;> simp [← hvu]

/-- The comparison `X_{T'} ×_{T'} Y_{T'} ⟶ X_T ×_T Y_T` of the fibre products of two base
changes, attached to a factorisation `u ≫ s = s'`. -/
def baseChangeProduct (x : X₀ ⟶ S₀) (y : Y₀ ⟶ S₀) (hu : u ≫ s = s') :
    pullback (pullback.snd x s') (pullback.snd y s') ⟶
      pullback (pullback.snd x s) (pullback.snd y s) :=
  pullback.map _ _ _ _ (baseChangeStage x hu) (baseChangeStage y hu) u
    (baseChangeStage_snd x hu).symm (baseChangeStage_snd y hu).symm

@[reassoc (attr := simp)]
lemma baseChangeProduct_fst (x : X₀ ⟶ S₀) (y : Y₀ ⟶ S₀) (hu : u ≫ s = s') :
    baseChangeProduct x y hu ≫ pullback.fst (pullback.snd x s) (pullback.snd y s) =
      pullback.fst (pullback.snd x s') (pullback.snd y s') ≫ baseChangeStage x hu := by
  simp [baseChangeProduct, pullback.map]

@[reassoc (attr := simp)]
lemma baseChangeProduct_snd (x : X₀ ⟶ S₀) (y : Y₀ ⟶ S₀) (hu : u ≫ s = s') :
    baseChangeProduct x y hu ≫ pullback.snd (pullback.snd x s) (pullback.snd y s) =
      pullback.snd (pullback.snd x s') (pullback.snd y s') ≫ baseChangeStage y hu := by
  simp [baseChangeProduct, pullback.map]

/-- **The cocycle identity of the tower of fibre products.** -/
lemma baseChangeProduct_comp (x : X₀ ⟶ S₀) (y : Y₀ ⟶ S₀) (hu : u ≫ s = s') (hv : v ≫ s' = s'')
    (hw : w ≫ s = s'') (hvu : v ≫ u = w) :
    baseChangeProduct x y hv ≫ baseChangeProduct x y hu = baseChangeProduct x y hw := by
  apply pullback.hom_ext <;>
    simp [baseChangeStage_comp x hu hv hw hvu, baseChangeStage_comp y hu hv hw hvu]

end Comparison

/-! ### The convolution kernel is functorial in its two arguments -/

section Functoriality

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The complex `L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K'` transported along isomorphisms of `K` and
`K'`. -/
def fourierMukaiConvolutionTensorMapIso {K₁ K₂ : DerivedCategory (pullback f g).Modules}
    (eK : K₁ ≅ K₂) {K'₁ K'₂ : DerivedCategory (pullback g h).Modules} (eK' : K'₁ ≅ K'₂) :
    fourierMukaiConvolutionTensor f g h K₁ K'₁ ≅ fourierMukaiConvolutionTensor f g h K₂ K'₂ :=
  ((derivedTensorProductFunctor (fourierMukaiTripleProduct f g h).toRingedSpace.sheaf).flip.obj
        ((derivedPullback (fourierMukaiPr23 f g h).toLRSHom.toShHom).obj K'₁)).mapIso
      ((derivedPullback (fourierMukaiPr12 f g h).toLRSHom.toShHom).mapIso eK) ≪≫
    ((derivedTensorProductFunctor
        (fourierMukaiTripleProduct f g h).toRingedSpace.sheaf).flip.mapIso
      ((derivedPullback (fourierMukaiPr23 f g h).toLRSHom.toShHom).mapIso eK')).app _

/-- **The convolution kernel of [Stacks, Tag 0FYS] transported along isomorphisms of its two
arguments.** -/
def fourierMukaiConvolutionMapIso {K₁ K₂ : DerivedCategory (pullback f g).Modules} (eK : K₁ ≅ K₂)
    {K'₁ K'₂ : DerivedCategory (pullback g h).Modules} (eK' : K'₁ ≅ K'₂) :
    fourierMukaiConvolution f g h K₁ K'₁ ≅ fourierMukaiConvolution f g h K₂ K'₂ :=
  (derivedPushforward (fourierMukaiPr13 f g h).toLRSHom.toShHom).mapIso
    (fourierMukaiConvolutionTensorMapIso f g h eK eK')

end Functoriality

/-! ### The carried inputs -/

/-- **[Stacks, Tag 09RF], essential surjectivity along the tower of fibre products.** In the
situation of [Stacks, Tag 09RD], for `X₀ ⟶ S₀` and `Y₀ ⟶ S₀` smooth and proper, every perfect
object of `D(𝒪_{X ×_S Y})` is the derived pullback of a perfect object of
`D(𝒪_{X_i ×_{S_i} Y_i})` for some stage `i ≥ 0`. -/
abbrev PerfectDescendsAlongBaseChangedTower : Prop :=
  ∀ {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation.{v, u} I)
    {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base),
    Smooth x → IsProper x → Smooth y → IsProper y →
    ∀ E : DerivedCategory (pullback (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base))).Modules,
      IsPerfect (X := (pullback (pullback.snd x (D.projection D.base))
        (pullback.snd y (D.projection D.base))).toRingedSpace) E →
      ∃ (i : I) (hi : D.base ≤ i) (Ei : DerivedCategory (pullback
        (pullback.snd x (D.transition hi)) (pullback.snd y (D.transition hi))).Modules),
        IsPerfect (X := (pullback (pullback.snd x (D.transition hi))
          (pullback.snd y (D.transition hi))).toRingedSpace) Ei ∧
          Nonempty ((derivedPullback (baseChangeProduct x y
            (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ei ≅ E)

/-- **[Stacks, Tag 09RF], descent of an isomorphism along the tower of fibre products.** In the
situation of [Stacks, Tag 09RD], for `X₀ ⟶ S₀` and `Y₀ ⟶ S₀` smooth and proper, two perfect
objects of `D(𝒪_{X_i ×_{S_i} Y_i})` whose derived pullbacks to `X ×_S Y` are isomorphic already
have isomorphic derived pullbacks to `X_j ×_{S_j} Y_j` for some `j ≥ i`. -/
abbrev PerfectIsoDescendsAlongBaseChangedTower : Prop :=
  ∀ {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation.{v, u} I)
    {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base),
    Smooth x → IsProper x → Smooth y → IsProper y →
    ∀ (i : I) (hi : D.base ≤ i) (E F : DerivedCategory (pullback
      (pullback.snd x (D.transition hi)) (pullback.snd y (D.transition hi))).Modules),
      IsPerfect (X := (pullback (pullback.snd x (D.transition hi))
        (pullback.snd y (D.transition hi))).toRingedSpace) E →
      IsPerfect (X := (pullback (pullback.snd x (D.transition hi))
        (pullback.snd y (D.transition hi))).toRingedSpace) F →
      Nonempty ((derivedPullback (baseChangeProduct x y
            (D.projection_comp_transition hi)).toLRSHom.toShHom).obj E ≅
          (derivedPullback (baseChangeProduct x y
            (D.projection_comp_transition hi)).toLRSHom.toShHom).obj F) →
      ∃ (j : I) (hij : i ≤ j),
        Nonempty ((derivedPullback (baseChangeProduct x y
            (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj E ≅
          (derivedPullback (baseChangeProduct x y
            (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj F)

/-- **The diagonal kernel of [Stacks, Tag 0FYV] and the convolution kernel of
[Stacks, Tag 0FYS] commute with base change.** This is the computation that the source's proof of
[Stacks, Tag 0G0K] performs, stated for a tower of base changes of two fixed smooth proper
morphisms `X₀ ⟶ S₀` and `Y₀ ⟶ S₀`. -/
abbrev DiagonalKernelAndConvolutionBaseChange : Prop :=
  ∀ {S₀ X₀ Y₀ T T' : Scheme.{u}} (x : X₀ ⟶ S₀) (y : Y₀ ⟶ S₀) {s : T ⟶ S₀} {s' : T' ⟶ S₀}
    {u : T' ⟶ T} (hu : u ≫ s = s'), Smooth x → IsProper x → Smooth y → IsProper y →
    Nonempty ((derivedPullback (baseChangeProduct x x hu).toLRSHom.toShHom).obj
        (diagonalKernel (pullback.snd x s)) ≅ diagonalKernel (pullback.snd x s')) ∧
      ∀ (K : DerivedCategory (pullback (pullback.snd x s) (pullback.snd y s)).Modules)
        (K' : DerivedCategory (pullback (pullback.snd y s) (pullback.snd x s)).Modules),
        IsPerfect (X := (pullback (pullback.snd x s) (pullback.snd y s)).toRingedSpace) K →
        IsPerfect (X := (pullback (pullback.snd y s) (pullback.snd x s)).toRingedSpace) K' →
        Nonempty ((derivedPullback (baseChangeProduct x x hu).toLRSHom.toShHom).obj
            (fourierMukaiConvolution (pullback.snd x s) (pullback.snd y s)
              (pullback.snd x s) K K') ≅
          fourierMukaiConvolution (pullback.snd x s') (pullback.snd y s') (pullback.snd x s')
            ((derivedPullback (baseChangeProduct x y hu).toLRSHom.toShHom).obj K)
            ((derivedPullback (baseChangeProduct y x hu).toLRSHom.toShHom).obj K'))

/-- **The diagonal kernel and the convolution kernel of perfect kernels are perfect.** For
`f : X ⟶ S` and `g : Y ⟶ S` smooth and proper, the first assertion is [Stacks, Tag 0FDP]
together with [Stacks, Tag 0B6G] and the second is [Stacks, Tag 0B91]. -/
abbrev DiagonalKernelAndConvolutionPerfect : Prop :=
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S), Smooth f → IsProper f → Smooth g → IsProper g →
    IsPerfect (X := (pullback f f).toRingedSpace) (diagonalKernel f) ∧
      ∀ (K : DerivedCategory (pullback f g).Modules)
        (K' : DerivedCategory (pullback g f).Modules),
        IsPerfect (X := (pullback f g).toRingedSpace) K →
        IsPerfect (X := (pullback g f).toRingedSpace) K' →
        IsPerfect (X := (pullback f f).toRingedSpace)
          (fourierMukaiConvolution f g f K K')

/-! ### Transporting the first displayed isomorphism along the tower -/

section Transport

/-- The base-change isomorphisms turn the comparison of the diagonal kernel with the convolution
kernel after derived pullback into the same comparison one stage up, and conversely. -/
private lemma nonempty_pullback_iso_iff
    (hbc : DiagonalKernelAndConvolutionBaseChange.{u}) {S₀ X₀ Y₀ T T' : Scheme.{u}}
    (x : X₀ ⟶ S₀) (y : Y₀ ⟶ S₀) {s : T ⟶ S₀} {s' : T' ⟶ S₀} {u : T' ⟶ T} (hu : u ≫ s = s')
    [Smooth x] [IsProper x] [Smooth y] [IsProper y]
    (K : DerivedCategory (pullback (pullback.snd x s) (pullback.snd y s)).Modules)
    (K' : DerivedCategory (pullback (pullback.snd y s) (pullback.snd x s)).Modules)
    (hK : IsPerfect (X := (pullback (pullback.snd x s) (pullback.snd y s)).toRingedSpace) K)
    (hK' : IsPerfect (X := (pullback (pullback.snd y s) (pullback.snd x s)).toRingedSpace) K') :
    Nonempty ((derivedPullback (baseChangeProduct x x hu).toLRSHom.toShHom).obj
        (diagonalKernel (pullback.snd x s)) ≅
      (derivedPullback (baseChangeProduct x x hu).toLRSHom.toShHom).obj
        (fourierMukaiConvolution (pullback.snd x s) (pullback.snd y s)
          (pullback.snd x s) K K')) ↔
    Nonempty (diagonalKernel (pullback.snd x s') ≅
      fourierMukaiConvolution (pullback.snd x s') (pullback.snd y s') (pullback.snd x s')
        ((derivedPullback (baseChangeProduct x y hu).toLRSHom.toShHom).obj K)
        ((derivedPullback (baseChangeProduct y x hu).toLRSHom.toShHom).obj K')) := by
  obtain ⟨⟨a⟩, b⟩ := hbc x y hu inferInstance inferInstance inferInstance inferInstance
  obtain ⟨b⟩ := b K K' hK hK'
  exact ⟨fun ⟨e⟩ => ⟨a.symm ≪≫ e ≪≫ b⟩, fun ⟨e⟩ => ⟨a ≪≫ e ≪≫ b.symm⟩⟩

/-- **The two sides of the first displayed isomorphism of [Stacks, Tag 0G0I], compared after
derived pullback along the comparison of the tower.** -/
lemma nonempty_pullback_iso_of_diagonal_iso
    (hbc : DiagonalKernelAndConvolutionBaseChange.{u}) {S₀ X₀ Y₀ T T' : Scheme.{u}}
    (x : X₀ ⟶ S₀) (y : Y₀ ⟶ S₀) {s : T ⟶ S₀} {s' : T' ⟶ S₀} {u : T' ⟶ T} (hu : u ≫ s = s')
    [Smooth x] [IsProper x] [Smooth y] [IsProper y]
    (K : DerivedCategory (pullback (pullback.snd x s) (pullback.snd y s)).Modules)
    (K' : DerivedCategory (pullback (pullback.snd y s) (pullback.snd x s)).Modules)
    (hK : IsPerfect (X := (pullback (pullback.snd x s) (pullback.snd y s)).toRingedSpace) K)
    (hK' : IsPerfect (X := (pullback (pullback.snd y s) (pullback.snd x s)).toRingedSpace) K')
    (e : Nonempty (diagonalKernel (pullback.snd x s') ≅
      fourierMukaiConvolution (pullback.snd x s') (pullback.snd y s') (pullback.snd x s')
        ((derivedPullback (baseChangeProduct x y hu).toLRSHom.toShHom).obj K)
        ((derivedPullback (baseChangeProduct y x hu).toLRSHom.toShHom).obj K'))) :
    Nonempty ((derivedPullback (baseChangeProduct x x hu).toLRSHom.toShHom).obj
        (diagonalKernel (pullback.snd x s)) ≅
      (derivedPullback (baseChangeProduct x x hu).toLRSHom.toShHom).obj
        (fourierMukaiConvolution (pullback.snd x s) (pullback.snd y s)
          (pullback.snd x s) K K')) := by
  exact (nonempty_pullback_iso_iff hbc x y hu K K' hK hK').2 e

/-- **The first displayed isomorphism of [Stacks, Tag 0G0I] descends through the comparison of
the tower.** -/
lemma nonempty_diagonal_iso_of_pullback_iso
    (hbc : DiagonalKernelAndConvolutionBaseChange.{u}) {S₀ X₀ Y₀ T T' : Scheme.{u}}
    (x : X₀ ⟶ S₀) (y : Y₀ ⟶ S₀) {s : T ⟶ S₀} {s' : T' ⟶ S₀} {u : T' ⟶ T} (hu : u ≫ s = s')
    [Smooth x] [IsProper x] [Smooth y] [IsProper y]
    (K : DerivedCategory (pullback (pullback.snd x s) (pullback.snd y s)).Modules)
    (K' : DerivedCategory (pullback (pullback.snd y s) (pullback.snd x s)).Modules)
    (hK : IsPerfect (X := (pullback (pullback.snd x s) (pullback.snd y s)).toRingedSpace) K)
    (hK' : IsPerfect (X := (pullback (pullback.snd y s) (pullback.snd x s)).toRingedSpace) K')
    (e : Nonempty ((derivedPullback (baseChangeProduct x x hu).toLRSHom.toShHom).obj
        (diagonalKernel (pullback.snd x s)) ≅
      (derivedPullback (baseChangeProduct x x hu).toLRSHom.toShHom).obj
        (fourierMukaiConvolution (pullback.snd x s) (pullback.snd y s)
          (pullback.snd x s) K K'))) :
    Nonempty (diagonalKernel (pullback.snd x s') ≅
      fourierMukaiConvolution (pullback.snd x s') (pullback.snd y s') (pullback.snd x s')
        ((derivedPullback (baseChangeProduct x y hu).toLRSHom.toShHom).obj K)
        ((derivedPullback (baseChangeProduct y x hu).toLRSHom.toShHom).obj K')) := by
  exact (nonempty_pullback_iso_iff hbc x y hu K K' hK hK').1 e

end Transport

/-! ### Stacks 0G0L -/

section Main

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation.{v, u} I)

/-- **One descent step.** Given a stage `i`, perfect kernels `Ki` and `Ki'` there whose derived
pullbacks to the limit are `K` and `K'`, and the first displayed isomorphism of
[Stacks, Tag 0G0I] over the limit, the first displayed isomorphism holds at some stage `j ≥ i`
for the derived pullbacks of `Ki` and `Ki'` to that stage. -/
lemma exists_stage_diagonal_iso (h09RFiso : PerfectIsoDescendsAlongBaseChangedTower.{v, u})
    (hbc : DiagonalKernelAndConvolutionBaseChange.{u})
    (hperf : DiagonalKernelAndConvolutionPerfect.{u})
    {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base)
    [Smooth x] [IsProper x] [Smooth y] [IsProper y] (i : I) (hi : D.base ≤ i)
    (Ki : DerivedCategory (pullback (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi))).Modules)
    (Ki' : DerivedCategory (pullback (pullback.snd y (D.transition hi))
      (pullback.snd x (D.transition hi))).Modules)
    (hKi : IsPerfect (X := (pullback (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi))).toRingedSpace) Ki)
    (hKi' : IsPerfect (X := (pullback (pullback.snd y (D.transition hi))
      (pullback.snd x (D.transition hi))).toRingedSpace) Ki')
    (e : Nonempty (diagonalKernel (pullback.snd x (D.projection D.base)) ≅
      fourierMukaiConvolution (pullback.snd x (D.projection D.base))
        (pullback.snd y (D.projection D.base)) (pullback.snd x (D.projection D.base))
        ((derivedPullback (baseChangeProduct x y
          (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki)
        ((derivedPullback (baseChangeProduct y x
          (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki'))) :
    ∃ (j : I) (hij : i ≤ j),
      Nonempty (diagonalKernel (pullback.snd x (D.transition (hi.trans hij))) ≅
        fourierMukaiConvolution (pullback.snd x (D.transition (hi.trans hij)))
          (pullback.snd y (D.transition (hi.trans hij)))
          (pullback.snd x (D.transition (hi.trans hij)))
          ((derivedPullback (baseChangeProduct x y
            (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki)
          ((derivedPullback (baseChangeProduct y x
            (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki')) := by
  have hcmp := nonempty_pullback_iso_of_diagonal_iso hbc x y
    (D.projection_comp_transition hi) Ki Ki' hKi hKi' e
  obtain ⟨hdiag, hconv⟩ := hperf (pullback.snd x (D.transition hi))
    (pullback.snd y (D.transition hi)) inferInstance inferInstance inferInstance inferInstance
  obtain ⟨j, hij, hj⟩ := h09RFiso D x x inferInstance inferInstance inferInstance inferInstance
    i hi (diagonalKernel (pullback.snd x (D.transition hi)))
    (fourierMukaiConvolution (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi)) (pullback.snd x (D.transition hi)) Ki Ki')
    hdiag (hconv Ki Ki' hKi hKi') hcmp
  exact ⟨j, hij, nonempty_diagonal_iso_of_pullback_iso hbc x y
    (D.transition_comp_transition hi hij) Ki Ki' hKi hKi' hj⟩

/-- **The cocycle identity of the tower of fibre products along the situation.** Comparing the
limit to the stage `j` and then the stage `j` to the stage `i` is comparing the limit to `i`. -/
lemma baseChangeProduct_projection_transition {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base)
    (y : Y₀ ⟶ D.stage D.base) {i j : I} (hi : D.base ≤ i) (hij : i ≤ j) :
    baseChangeProduct x y (D.projection_comp_transition (hi.trans hij)) ≫
        baseChangeProduct x y (D.transition_comp_transition hi hij) =
      baseChangeProduct x y (D.projection_comp_transition hi) :=
  baseChangeProduct_comp x y (D.transition_comp_transition hi hij)
    (D.projection_comp_transition (hi.trans hij)) (D.projection_comp_transition hi)
    (D.projection_comp_transition hij)

/-- **Transporting an object from a stage to a later stage does not change its derived pullback
to the limit.** -/
lemma nonempty_limitPullback_iso_transition {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base)
    (y : Y₀ ⟶ D.stage D.base) {i j : I} (hi : D.base ≤ i) (hij : i ≤ j)
    (Ki : DerivedCategory (pullback (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi))).Modules)
    {K : DerivedCategory (pullback (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base))).Modules}
    (e : Nonempty ((derivedPullback (baseChangeProduct x y
      (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki ≅ K)) :
    Nonempty ((derivedPullback (baseChangeProduct x y
        (D.projection_comp_transition (hi.trans hij))).toLRSHom.toShHom).obj
      ((derivedPullback (baseChangeProduct x y
        (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki) ≅ K) := by
  obtain ⟨e⟩ := e
  exact ⟨(Stacks.DerivedPullback.schemeFactorIso _ _ _
    (baseChangeProduct_projection_transition D x y hi hij)).app Ki ≪≫ e⟩

/-- **The descent of a relative equivalence, starting from a stage at which the kernel and its
partner already live.** Given a stage `i`, perfect objects `Ki` and `Ki'` there whose derived
pullbacks to the limit are the kernel `K` of a relative equivalence over the limit and its
partner `K'`, there is a stage carrying a Fourier-Mukai kernel of a relative equivalence. -/
lemma exists_isRelativeEquivalenceKernel_of_stage
    (h09RFiso : PerfectIsoDescendsAlongBaseChangedTower.{v, u})
    (hbc : DiagonalKernelAndConvolutionBaseChange.{u})
    (hperf : DiagonalKernelAndConvolutionPerfect.{u})
    {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base)
    [Smooth x] [IsProper x] [Smooth y] [IsProper y]
    {K : DerivedCategory (pullback (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base))).Modules}
    {K' : DerivedCategory (pullback (pullback.snd y (D.projection D.base))
      (pullback.snd x (D.projection D.base))).Modules}
    (i : I) (hi : D.base ≤ i)
    (Ki : DerivedCategory (pullback (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi))).Modules)
    (Ki' : DerivedCategory (pullback (pullback.snd y (D.transition hi))
      (pullback.snd x (D.transition hi))).Modules)
    (hKi : IsPerfect (X := (pullback (pullback.snd x (D.transition hi))
      (pullback.snd y (D.transition hi))).toRingedSpace) Ki)
    (hKi' : IsPerfect (X := (pullback (pullback.snd y (D.transition hi))
      (pullback.snd x (D.transition hi))).toRingedSpace) Ki')
    (eKi : Nonempty ((derivedPullback (baseChangeProduct x y
      (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki ≅ K))
    (eKi' : Nonempty ((derivedPullback (baseChangeProduct y x
      (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki' ≅ K'))
    (e₁ : Nonempty (diagonalKernel (pullback.snd x (D.projection D.base)) ≅
      fourierMukaiConvolution (pullback.snd x (D.projection D.base))
        (pullback.snd y (D.projection D.base)) (pullback.snd x (D.projection D.base)) K K'))
    (e₂ : Nonempty (diagonalKernel (pullback.snd y (D.projection D.base)) ≅
      fourierMukaiConvolution (pullback.snd y (D.projection D.base))
        (pullback.snd x (D.projection D.base)) (pullback.snd y (D.projection D.base)) K' K)) :
    ∃ (j : I) (hj : D.base ≤ j) (Kj : DerivedCategory (pullback
      (pullback.snd x (D.transition hj)) (pullback.snd y (D.transition hj))).Modules),
      IsRelativeEquivalenceKernel (pullback.snd x (D.transition hj))
        (pullback.snd y (D.transition hj)) Kj := by
  obtain ⟨eKi⟩ := eKi
  obtain ⟨eKi'⟩ := eKi'
  obtain ⟨e₁⟩ := e₁
  have f₁ : Nonempty (diagonalKernel (pullback.snd x (D.projection D.base)) ≅
      fourierMukaiConvolution (pullback.snd x (D.projection D.base))
        (pullback.snd y (D.projection D.base)) (pullback.snd x (D.projection D.base))
        ((derivedPullback (baseChangeProduct x y
          (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki)
        ((derivedPullback (baseChangeProduct y x
          (D.projection_comp_transition hi)).toLRSHom.toShHom).obj Ki')) :=
    ⟨e₁ ≪≫ fourierMukaiConvolutionMapIso _ _ _ eKi.symm eKi'.symm⟩
  obtain ⟨j, hij, g₁⟩ := exists_stage_diagonal_iso D h09RFiso hbc hperf x y i hi Ki Ki'
    hKi hKi' f₁
  have hLj := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (baseChangeProduct x y (D.transition_comp_transition hi hij)).toLRSHom.toShHom Ki hKi
  have hLj' := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
    (baseChangeProduct y x (D.transition_comp_transition hi hij)).toLRSHom.toShHom Ki' hKi'
  have eLj := nonempty_limitPullback_iso_transition D x y hi hij Ki ⟨eKi⟩
  have eLj' := nonempty_limitPullback_iso_transition D y x hi hij Ki' ⟨eKi'⟩
  have f₂ : Nonempty (diagonalKernel (pullback.snd y (D.projection D.base)) ≅
      fourierMukaiConvolution (pullback.snd y (D.projection D.base))
        (pullback.snd x (D.projection D.base)) (pullback.snd y (D.projection D.base))
        ((derivedPullback (baseChangeProduct y x
            (D.projection_comp_transition (hi.trans hij))).toLRSHom.toShHom).obj
          ((derivedPullback (baseChangeProduct y x
            (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki'))
        ((derivedPullback (baseChangeProduct x y
            (D.projection_comp_transition (hi.trans hij))).toLRSHom.toShHom).obj
          ((derivedPullback (baseChangeProduct x y
            (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki))) := by
    obtain ⟨e₂⟩ := e₂
    obtain ⟨a⟩ := eLj
    obtain ⟨b⟩ := eLj'
    exact ⟨e₂ ≪≫ fourierMukaiConvolutionMapIso _ _ _ b.symm a.symm⟩
  obtain ⟨k, hjk, g₂⟩ := exists_stage_diagonal_iso D h09RFiso hbc hperf y x j (hi.trans hij)
    ((derivedPullback (baseChangeProduct y x
      (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki')
    ((derivedPullback (baseChangeProduct x y
      (D.transition_comp_transition hi hij)).toLRSHom.toShHom).obj Ki)
    hLj' hLj f₂
  obtain ⟨g₁⟩ := g₁
  refine ⟨k, (hi.trans hij).trans hjk, _,
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _ hLj, _,
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _ hLj', ?_, g₂⟩
  exact nonempty_diagonal_iso_of_pullback_iso hbc x y
    (D.transition_comp_transition (hi.trans hij) hjk) _ _ hLj hLj'
    ⟨(derivedPullback (baseChangeProduct x x
      (D.transition_comp_transition (hi.trans hij) hjk)).toLRSHom.toShHom).mapIso g₁⟩

/-- **[Stacks, Tag 0G0L]: a relative equivalence over a limit of schemes comes from a finite
stage.** Let `S = lim S_i` be the limit of a directed inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms, with a chosen index `0`, let
`X_0 ⟶ S_0` and `Y_0 ⟶ S_0` be smooth and proper, and put `X_i = X_0 ×_{S_0} S_i`,
`X = X_0 ×_{S_0} S` and likewise for `Y_0`. If `K` is the Fourier-Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, then for some `i ≥ 0` there is a Fourier-Mukai kernel of a
relative equivalence from `X_i` to `Y_i` over `S_i`.

The proof is the source's. The kernel `K` and its partner `K'` descend to perfect objects `K_i`
and `K'_i` at a common stage `i` by [Stacks, Tag 09RF]; both displayed isomorphisms of
[Stacks, Tag 0G0I] then hold over the limit for the derived pullbacks of `K_i` and `K'_i`, since
the diagonal kernel and the convolution kernel commute with base change, so by
[Stacks, Tag 09RF] again the first of them already holds at some stage `j ≥ i`, and, after
transporting `K_i` and `K'_i` to `j`, the second at some stage `k ≥ j`. Transporting the first
isomorphism from `j` to `k` puts both at the stage `k`. -/
@[stacks 0G0L "the existence of a relative-equivalence kernel at SOME stage i >= 0 of a directed \
inverse system of qcqs schemes with affine transitions, given one over the limit. GRANTED, each \
an input the source's own proof cites and this tree lacks in applicable form: h09RFobj and \
h09RFiso, the two halves of Tag 09RF read along the tower of fibre products (the tree has only \
the coherent cocone); hbc, the two \
base-change isomorphisms established inside the proof of Tag 0G0K but private there \
(RelativeEquivalenceBaseChange.lean:404 and :427, exported only in the opposite direction as \
:518); hperf, perfectness of the diagonal kernel (Tag 0FDP with Tag 0B6G, whose tree form \
the proper direct image theorem grants its own Tor-dimension input) and of the convolution kernel \
(Tag 0B91, whose tree form \
StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatPushforwardBaseChange.lean:263 proves \
only the base-change \
half in tensor form). No hypothesis mentions relative equivalences, so nothing of the conclusion \
is assumed; the affineness of the transitions and the qcqs hypothesis on every stage enter \
through DescentSituation, and smoothness and properness of X_0 -> S_0 and Y_0 -> S_0 are \
instance hypotheses"]
theorem exists_isRelativeEquivalenceKernel_of_descentSituation
    (h09RFobj : PerfectDescendsAlongBaseChangedTower.{v, u})
    (h09RFiso : PerfectIsoDescendsAlongBaseChangedTower.{v, u})
    (hbc : DiagonalKernelAndConvolutionBaseChange.{u})
    (hperf : DiagonalKernelAndConvolutionPerfect.{u})
    {X₀ Y₀ : Scheme.{u}} (x : X₀ ⟶ D.stage D.base) (y : Y₀ ⟶ D.stage D.base)
    [Smooth x] [IsProper x] [Smooth y] [IsProper y]
    {K : DerivedCategory (pullback (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base))).Modules}
    (hK : IsRelativeEquivalenceKernel (pullback.snd x (D.projection D.base))
      (pullback.snd y (D.projection D.base)) K) :
    ∃ (i : I) (hi : D.base ≤ i) (Ki : DerivedCategory (pullback
      (pullback.snd x (D.transition hi)) (pullback.snd y (D.transition hi))).Modules),
      IsRelativeEquivalenceKernel (pullback.snd x (D.transition hi))
        (pullback.snd y (D.transition hi)) Ki := by
  obtain ⟨hKp, K', hK'p, e₁, e₂⟩ := hK
  obtain ⟨i₁, hi₁, K₁, hK₁p, eK₁⟩ := h09RFobj D x y inferInstance inferInstance inferInstance
    inferInstance K hKp
  obtain ⟨i₂, hi₂, K₂, hK₂p, eK₂⟩ := h09RFobj D y x inferInstance inferInstance inferInstance
    inferInstance K' hK'p
  obtain ⟨i, hii₁, hii₂⟩ := directed_of (· ≤ ·) i₁ i₂
  exact exists_isRelativeEquivalenceKernel_of_stage D h09RFiso hbc hperf x y i (hi₁.trans hii₁)
    ((derivedPullback (baseChangeProduct x y
      (D.transition_comp_transition hi₁ hii₁)).toLRSHom.toShHom).obj K₁)
    ((derivedPullback (baseChangeProduct y x
      (D.transition_comp_transition hi₂ hii₂)).toLRSHom.toShHom).obj K₂)
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K₁ hK₁p)
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K₂ hK₂p)
    (nonempty_limitPullback_iso_transition D x y hi₁ hii₁ K₁ eK₁)
    (nonempty_limitPullback_iso_transition D y x hi₂ hii₂ K₂ eK₂) e₁ e₂

end Main

end AlgebraicGeometry

end
