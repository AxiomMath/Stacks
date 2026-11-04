module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalence
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TorIndependenceBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedFlatRepresentative
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the Fourier-Mukai kernel of a relative equivalence

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes and let `K` be the Fourier-Mukai kernel
of a relative equivalence from `X` to `Y` over `S`, the predicate `IsRelativeEquivalenceKernel`
of [Stacks, Tag 0G0I]. Let `s : S₁ ⟶ S` be an arbitrary morphism of schemes and put
`X₁ = X ×_S S₁` and `Y₁ = Y ×_S S₁`, each over `S₁` by its second projection. Then

`K₁ = L(X₁ ×_{S₁} Y₁ ⟶ X ×_S Y)^* K`

is the Fourier-Mukai kernel of a relative equivalence from `X₁` to `Y₁` over `S₁`. This is
[Stacks, Tag 0G0K].

## Main definitions

* `AlgebraicGeometry.fourierMukaiBaseChangeMap` — the canonical comparison
  `X₁ ×_{S₁} Y₁ ⟶ X ×_S Y`, the morphism the source pulls `K` back along.

## Main results

* `AlgebraicGeometry.isRelativeEquivalenceKernel_derivedPullback` — **[Stacks, Tag 0G0K]**.

## Implementation notes

*Which side of the fibre product.* The source writes `X₁ = S₁ ×_S X`; here `X₁` is the chosen
pullback `X ×_S S₁`, with structure morphism `pullback.snd f s : X ×_S S₁ ⟶ S₁`. The two differ
by the symmetry of the fibre product, so nothing of the statement changes; taking this side is
what makes the Tor-independence input [Stacks, Tag 0CTA] apply at the spelling this tree proves
it at, namely `AlgebraicGeometry.torIndependent_pullback_product_of_flat`, whose base-changed
fibre product is `pullback (pullback.snd x s) (pullback.snd y s)`.

*The hypotheses on `f` and `g`, and the absence of hypotheses on `s`.* The source's Section
0G0F fixes `X ⟶ S` and `Y ⟶ S` **smooth and proper**. Only four consequences of that are used
below: flatness (smooth implies flat), separatedness, quasi-compactness and
quasi-separatedness (all implied by proper). So the result proved here is more general than the
source's, not less. The morphism `s : S₁ ⟶ S` carries **no** hypothesis at all — in particular
neither flatness nor Tor independence — exactly as the source states it.

*The one granted input, and why.* `h08IB` is the conclusion of [Stacks, Tag 08IB], the
assertion that the derived base-change map of [Stacks, Tag 08HY] is invertible on complexes
with quasi-coherent cohomology over a Tor-independent cartesian square of schemes with
quasi-compact quasi-separated right-hand morphism. It is carried as an explicit hypothesis, in
exactly the spelling `AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent` that
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/Composition.lean` already carries
for [Stacks, Tag 0FYS]: this tree has the map
(`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`) and the Tor-independence input on
a cartesian affine-open chart, but not the globalization of the latter to the former, which is
[Stacks, Tag 0DJ9]. Nothing else is granted.

*Where the source uses [Stacks, Tag 0B91] this proof uses [Stacks, Tag 08IB].* The source
reduces the convolution half to a base-change statement for `R pr_{13,*}` and quotes
[Stacks, Tag 0B91], proper flat pushforward base change. This tree's [Stacks, Tag 0B91],
`AlgebraicGeometry.ProperFlatBaseChange.isIso_tensorFlatBaseChangeMap_structure`, is stated for
the map `AlgebraicGeometry.tensorFlatBaseChangeMap` at the complex `𝒪_X` in degree zero and does
not perform the transport to `Rf_*E`, so it cannot be applied to `R pr_{13,*}` of the
convolution tensor. Instead the proof below observes that `pr_{13}` is **flat**, being a base
change of `pr_X : X ×_S Y ⟶ X` along `pr_X : X ×_S X ⟶ X` (the lemma
`isPullback_tripleP12_P13`, which also says the triple product is the fibre product of
`X ×_S Y` and `X ×_S X` over `X`), hence Tor independent from everything over `X ×_S X`; so
[Stacks, Tag 08IB] applies there with no properness used at all. This is a weaker input than
the source's, not a stronger one.

*The two cartesian squares are proved, not assumed.* `isPullback_bcMap_fst`,
`isPullback_bcMap_snd`, `isPullback_bcMap_diagonal` and `isPullback_tripleP13` are pure
category theory in a category with pullbacks: a fibre product of two base changes is the base
change of the fibre product, and the diagonal and `pr_{13}` inherit that. They are obtained by
pasting cartesian squares, with no universal-property computation.

*Symmetry of Tor independence.* [Stacks, Tag 0CTA] delivers Tor independence with the
base-changed fibre product in the first slot, while [Stacks, Tag 08IB] wants the pushed-forward
morphism there. `torIndependent_symm` supplies the swap: on a compatible triple of affine opens
Tor independence is a symmetric condition on two algebras over a common ring, by the balancing
of Tor ([Stacks, Tag 00M3]), and the affine criterion of [Stacks, Tag 0FXV] transfers that to
the two morphisms.

## References

* [Stacks Project, Tag 0G0K](https://stacks.math.columbia.edu/tag/0G0K)
* [Stacks Project, Tag 0G0I](https://stacks.math.columbia.edu/tag/0G0I)
* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0FXV](https://stacks.math.columbia.edu/tag/0FXV)
* [Stacks Project, Tag 00M3](https://stacks.math.columbia.edu/tag/00M3)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Base change of fibre products: the cartesian squares -/

section Geometry

universe v' u'

variable {C : Type u'} [Category.{v'} C] [HasPullbacks C]

section
variable {S S₁ X Y X₁ Y₁ : C} {f : X ⟶ S} {g : Y ⟶ S} {s : S₁ ⟶ S}
  {cX : X₁ ⟶ X} {f₁ : X₁ ⟶ S₁} {cY : Y₁ ⟶ Y} {g₁ : Y₁ ⟶ S₁}

/-- The comparison from the fibre product of two base changes to the original fibre product. -/
private def bcMap (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    pullback f₁ g₁ ⟶ pullback f g :=
  pullback.map f₁ g₁ f g cX cY s hX.w.symm hY.w.symm

@[reassoc (attr := simp)]
private lemma bcMap_fst (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    bcMap hX hY ≫ pullback.fst f g = pullback.fst f₁ g₁ ≫ cX :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma bcMap_snd (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    bcMap hX hY ≫ pullback.snd f g = pullback.snd f₁ g₁ ≫ cY :=
  pullback.lift_snd _ _ _

/-- The first projection of a fibre product is compatible with base change. -/
private lemma isPullback_bcMap_fst (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    IsPullback (bcMap hX hY) (pullback.fst f₁ g₁) (pullback.fst f g) cX := by
  refine IsPullback.of_right ?_ (bcMap_fst hX hY) (IsPullback.of_hasPullback f g).flip
  have h := ((IsPullback.of_hasPullback f₁ g₁).flip).paste_horiz hY
  rw [bcMap_snd hX hY, ← hX.w] at *
  exact h

/-- The second projection of a fibre product is compatible with base change. -/
private lemma isPullback_bcMap_snd (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    IsPullback (bcMap hX hY) (pullback.snd f₁ g₁) (pullback.snd f g) cY := by
  refine IsPullback.of_right ?_ (bcMap_snd hX hY) (IsPullback.of_hasPullback f g)
  have h := (IsPullback.of_hasPullback f₁ g₁).paste_horiz hX
  rw [bcMap_fst hX hY, ← hY.w] at *
  exact h

/-- The fibre product of two base changes is the base change of the fibre product. -/
private lemma isPullback_bcMap_base (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    IsPullback (bcMap hX hY) (pullback.fst f₁ g₁ ≫ f₁) (pullback.fst f g ≫ f) s :=
  (isPullback_bcMap_fst hX hY).paste_vert hX

/-- The same, read through the second projection. -/
private lemma isPullback_bcMap_base' (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s) :
    IsPullback (bcMap hX hY) (pullback.snd f₁ g₁ ≫ g₁) (pullback.snd f g ≫ g) s :=
  (isPullback_bcMap_snd hX hY).paste_vert hY

/-- The diagonal is compatible with base change. -/
private lemma isPullback_bcMap_diagonal (hX : IsPullback cX f₁ f s) :
    IsPullback cX (pullback.diagonal f₁) (pullback.diagonal f) (bcMap hX hX) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_bcMap_snd hX hX)
  · simpa using (IsPullback.of_id_snd (f := cX))
  · apply pullback.hom_ext <;> simp

end

section Triple

variable {S S₁ X Y Z X₁ Y₁ Z₁ : C} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {s : S₁ ⟶ S}
  {cX : X₁ ⟶ X} {f₁ : X₁ ⟶ S₁} {cY : Y₁ ⟶ Y} {g₁ : Y₁ ⟶ S₁} {cZ : Z₁ ⟶ Z} {h₁ : Z₁ ⟶ S₁}

/-- The projection `pr₁₃` of the left-associated triple fibre product. -/
private def tripleP13 (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    pullback (pullback.snd f g ≫ g) h ⟶ pullback f h :=
  pullback.lift (pullback.fst (pullback.snd f g ≫ g) h ≫ pullback.fst f g)
    (pullback.snd (pullback.snd f g ≫ g) h)
    (by
      have h₁ : pullback.fst f g ≫ f = pullback.snd f g ≫ g := pullback.condition
      have h₂ : pullback.fst (pullback.snd f g ≫ g) h ≫ (pullback.snd f g ≫ g) =
          pullback.snd (pullback.snd f g ≫ g) h ≫ h := pullback.condition
      rw [Category.assoc, h₁, h₂])

@[reassoc (attr := simp)]
private lemma tripleP13_fst :
    tripleP13 f g h ≫ pullback.fst f h =
      pullback.fst (pullback.snd f g ≫ g) h ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma tripleP13_snd :
    tripleP13 f g h ≫ pullback.snd f h = pullback.snd (pullback.snd f g ≫ g) h :=
  pullback.lift_snd _ _ _

/-- **`pr₁₃` is compatible with base change.** -/
private lemma isPullback_tripleP13 (hX : IsPullback cX f₁ f s) (hY : IsPullback cY g₁ g s)
    (hZ : IsPullback cZ h₁ h s) :
    IsPullback (bcMap (isPullback_bcMap_base' hX hY) hZ) (tripleP13 f₁ g₁ h₁)
      (tripleP13 f g h) (bcMap hX hZ) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_bcMap_snd hX hZ)
  · simpa using isPullback_bcMap_snd (isPullback_bcMap_base' hX hY) hZ
  · apply pullback.hom_ext <;> simp

/-- **`pr₁₃` exhibits the triple fibre product as the fibre product of `X ×_S Y` and `X ×_S Z`
over `X`.** In particular `pr₁₃` is a base change of `pr_X : X ×_S Y ⟶ X`. -/
private lemma isPullback_tripleP12_P13 (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    IsPullback (pullback.fst (pullback.snd f g ≫ g) h) (tripleP13 f g h)
      (pullback.fst f g) (pullback.fst f h) := by
  refine IsPullback.of_bot ?_ (tripleP13_fst).symm (IsPullback.of_hasPullback f h)
  have h1 : pullback.fst f g ≫ f = pullback.snd f g ≫ g := pullback.condition
  rw [tripleP13_snd, h1]
  exact IsPullback.of_hasPullback _ _

end Triple

end Geometry

/-! ### `pr₁₃` is `fourierMukaiPr13` -/

universe u

section Identification

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

private lemma tripleP13_eq : tripleP13 f g h = fourierMukaiPr13 f g h := by
  apply pullback.hom_ext <;> simp [tripleP13, fourierMukaiPr13]

end Identification

/-! ### Symmetry of Tor independence -/

private alias algebraTorIndependent_symm := Algebra.TorIndependent.symm

/-- **Tor independence is symmetric.** On a compatible triple of affine opens the condition is
Tor independence of two algebras over a common ring, which is symmetric by the balancing of
Tor ([Stacks, Tag 00M3]); the affine criterion of [Stacks, Tag 0FXV] transfers that to the
two morphisms. -/
private alias torIndependent_symm := TorIndependent.symm

/-! ### Notation for the three derived operations -/

section Notation

variable {V W : Scheme.{u}}

/-- The derived tensor product transported along isomorphisms in both factors. -/
private def dtenRIso {A A' B B' : DerivedCategory W.Modules} (eA : A ≅ A') (eB : B ≅ B') :
    (dtenR W A).obj B ≅ (dtenR W A').obj B' :=
  (dtenR W A).mapIso eB ≪≫
    ((derivedTensorProductFunctor W.toRingedSpace.sheaf).flip.mapIso eA).app B'

/-- A quasi-coherent module in degree zero has quasi-coherent cohomology. -/
private lemma isQCohAll_single (M : W.Modules) (hM : M.IsQuasicoherent) :
    IsQCohAll ((DerivedCategory.singleFunctor W.Modules 0).obj M) := by
  intro j
  have : (SheafOfModules.isQuasicoherent W.ringCatSheaf).ContainsZero :=
    containsZero_isQuasicoherent W
  have e := (DerivedCategory.homologyFunctorFactors W.Modules j).app
    ((HomologicalComplex.single W.Modules (ComplexShape.up ℤ) 0).obj M)
  by_cases h0 : j = 0
  · subst h0
    exact (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso
      (e ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _).symm hM
  · exact (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso e.symm
      ((SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_isZero
        (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M j h0))

/-- **The derived pullback of the structure sheaf is the structure sheaf**, both placed in
degree zero: `𝒪_W` is a flat `𝒪_W`-module, so `L p^*` of it is the ordinary pullback. -/
private def dpullUnitIso (p : V ⟶ W) :
    (dpull p).obj ((DerivedCategory.singleFunctor W.Modules 0).obj
        (SheafOfModules.unit W.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor V.Modules 0).obj (SheafOfModules.unit V.ringCatSheaf) :=
  Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso p.toLRSHom.toShHom _
      (Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_structureSheafModule
        W.toRingedSpace) ≪≫
    (DerivedCategory.singleFunctor V.Modules 0).mapIso
      (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso p.toLRSHom.toShHom)

end Notation

/-! ### The base-changed situation -/

section BaseChange

/-- **The canonical comparison `X₁ ×_{S₁} Y₁ ⟶ X ×_S Y`** attached to a morphism `S₁ ⟶ S`,
where `X₁ = X ×_S S₁` and `Y₁ = Y ×_S S₁` with their projections to `S₁`. This is the morphism
along which [Stacks, Tag 0G0K] pulls a Fourier-Mukai kernel back. -/
def fourierMukaiBaseChangeMap {S X Y S₁ : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (s : S₁ ⟶ S) :
    pullback (pullback.snd f s) (pullback.snd g s) ⟶ pullback f g :=
  pullback.map (pullback.snd f s) (pullback.snd g s) f g (pullback.fst f s) (pullback.fst g s) s
    pullback.condition.symm pullback.condition.symm

private lemma fourierMukaiBaseChangeMap_eq {S X Y S₁ : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (s : S₁ ⟶ S) : fourierMukaiBaseChangeMap f g s =
      bcMap (IsPullback.of_hasPullback f s) (IsPullback.of_hasPullback g s) := rfl

private lemma diagonalKernel_eq {S X : Scheme.{u}} (f : X ⟶ S) :
    diagonalKernel f = (dpush (pullback.diagonal f)).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  rfl

/-- Derived base change along a Tor-independent cartesian square, as an isomorphism on a complex
with quasi-coherent cohomology; this is [Stacks, Tag 08IB] in the form `h08IB`. -/
private def dbaseChangeIso (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hsqP : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (htor : TorIndependent f g) {M : DerivedCategory X.Modules} (hM : IsQCohAll M) :
    (dpull g).obj ((dpush f).obj M) ≅ (dpush f').obj ((dpull g').obj M) :=
  haveI : IsIso ((dbaseChange g' f' f g (shHom_comp_eq hsqP.w)).app M) :=
    h08IB _ _ _ _ hsqP inferInstance inferInstance htor _ _ hM
  asIso ((dbaseChange g' f' f g (shHom_comp_eq hsqP.w)).app M)

/-- **The diagonal kernel commutes with base change.** For `f : X ⟶ S` flat and separated and
any `s : S₁ ⟶ S`, the pullback of `𝒪_{Δ_{X/S}}` along `X₁ ×_{S₁} X₁ ⟶ X ×_S X` is
`𝒪_{Δ_{X₁/S₁}}`.

The square with sides `X₁ ⟶ X` and the two diagonals is cartesian, `X₁ ×_{S₁} X₁` and `X` are
Tor independent over `X ×_S X` by [Stacks, Tag 0CTA] applied to the square with corners
`X, X, X, S`, and the derived pullback of `𝒪_X` in degree zero is `𝒪_{X₁}` in degree zero
because `𝒪_X` is flat. -/
private def diagonalKernelBaseChangeIso (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    {S X S₁ : Scheme.{u}} (f : X ⟶ S) (s : S₁ ⟶ S) [IsSeparated f] [Flat f] :
    (dpull (fourierMukaiBaseChangeMap f f s)).obj (diagonalKernel f) ≅
      diagonalKernel (pullback.snd f s) := by
  have hsqP : IsPullback (pullback.fst f s) (pullback.diagonal (pullback.snd f s))
      (pullback.diagonal f) (fourierMukaiBaseChangeMap f f s) :=
    isPullback_bcMap_diagonal (IsPullback.of_hasPullback f s)
  have htor : TorIndependent (pullback.diagonal f) (fourierMukaiBaseChangeMap f f s) :=
    torIndependent_symm (torIndependent_pullback_product_of_flat s f f (𝟙 X) (𝟙 X) rfl)
  rw [diagonalKernel_eq, diagonalKernel_eq]
  exact dbaseChangeIso h08IB hsqP htor (isQCohAll_single _ inferInstance) ≪≫
    (dpush (pullback.diagonal (pullback.snd f s))).mapIso (dpullUnitIso (pullback.fst f s))

/-- **The convolution kernel commutes with base change.** -/
private def convolutionBaseChangeIso (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    {S X Y S₁ : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (s : S₁ ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] [Flat g]
    {K : DerivedCategory (pullback f g).Modules} (hK : IsQCohAll K)
    {K' : DerivedCategory (pullback g f).Modules} (hK' : IsQCohAll K') :
    (dpull (fourierMukaiBaseChangeMap f f s)).obj (fourierMukaiConvolution f g f K K') ≅
      fourierMukaiConvolution (pullback.snd f s) (pullback.snd g s) (pullback.snd f s)
        ((dpull (fourierMukaiBaseChangeMap f g s)).obj K)
        ((dpull (fourierMukaiBaseChangeMap g f s)).obj K') := by
  have hX := IsPullback.of_hasPullback f s
  have hY := IsPullback.of_hasPullback g s
  have hA1 : IsPullback (bcMap (isPullback_bcMap_base' hX hY) hX)
      (fourierMukaiPr13 (pullback.snd f s) (pullback.snd g s) (pullback.snd f s))
      (fourierMukaiPr13 f g f) (fourierMukaiBaseChangeMap f f s) := by
    rw [← tripleP13_eq, ← tripleP13_eq]
    exact isPullback_tripleP13 hX hY hX
  haveI hfl : Flat (fourierMukaiPr13 f g f) := by
    rw [← tripleP13_eq]
    exact MorphismProperty.of_isPullback (isPullback_tripleP12_P13 f g f) inferInstance
  have htor : TorIndependent (fourierMukaiPr13 f g f) (fourierMukaiBaseChangeMap f f s) :=
    torIndependent_of_flat_left _ _
  have hM : IsQCohAll (fourierMukaiConvolutionTensor f g f K K') :=
    isQCohAll_dtenR (isQCohAll_dpull _ hK) (isQCohAll_dpull _ hK')
  have h12 : bcMap (isPullback_bcMap_base' hX hY) hX ≫ fourierMukaiPr12 f g f =
      fourierMukaiPr12 (pullback.snd f s) (pullback.snd g s) (pullback.snd f s) ≫
        fourierMukaiBaseChangeMap f g s := bcMap_fst _ _
  have h23 : bcMap (isPullback_bcMap_base' hX hY) hX ≫ fourierMukaiPr23 f g f =
      fourierMukaiPr23 (pullback.snd f s) (pullback.snd g s) (pullback.snd f s) ≫
        fourierMukaiBaseChangeMap g f s := by
    apply pullback.hom_ext <;>
      simp [fourierMukaiPr23, fourierMukaiBaseChangeMap_eq, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  refine dbaseChangeIso h08IB hA1 htor hM ≪≫
    (dpush (fourierMukaiPr13 (pullback.snd f s) (pullback.snd g s)
      (pullback.snd f s))).mapIso ?_
  refine (dpullTensorIso (bcMap (isPullback_bcMap_base' hX hY) hX)
      ((dpull (fourierMukaiPr23 f g f)).obj K')).app
      ((dpull (fourierMukaiPr12 f g f)).obj K) ≪≫ ?_
  exact dtenRIso
    ((dpullCompIsoEq (bcMap (isPullback_bcMap_base' hX hY) hX) (fourierMukaiPr23 f g f)
      (fourierMukaiPr23 (pullback.snd f s) (pullback.snd g s) (pullback.snd f s))
      (fourierMukaiBaseChangeMap g f s) h23).app K')
    ((dpullCompIsoEq (bcMap (isPullback_bcMap_base' hX hY) hX) (fourierMukaiPr12 f g f)
      (fourierMukaiPr12 (pullback.snd f s) (pullback.snd g s) (pullback.snd f s))
      (fourierMukaiBaseChangeMap f g s) h12).app K)

end BaseChange

/-! ### Stacks 0G0K -/

section Main

/-- **[Stacks, Tag 0G0K]: a relative equivalence is stable under base change.** Let `f : X ⟶ S`
and `g : Y ⟶ S` and let `K` be the Fourier-Mukai kernel of a relative equivalence from `X` to
`Y` over `S` ([Stacks, Tag 0G0I]). Let `s : S₁ ⟶ S` be *any* morphism of schemes, and write
`X₁ = X ×_S S₁` and `Y₁ = Y ×_S S₁` with their projections to `S₁`. Then

`K₁ = L(X₁ ×_{S₁} Y₁ ⟶ X ×_S Y)^* K`

is the Fourier-Mukai kernel of a relative equivalence from `X₁` to `Y₁` over `S₁`.

The proof is the source's. Take the partner `K'` of `K` and pull it back to `K'₁` along
`Y₁ ×_{S₁} X₁ ⟶ Y ×_S X`. The square carrying `pr₁₃` on `X₁ ×_{S₁} Y₁ ×_{S₁} X₁` to `pr₁₃` on
`X ×_S Y ×_S X` is cartesian, and `pr₁₃` is flat because `g` is, so derived base change
([Stacks, Tag 08IB], granted) identifies `L^*` of the convolution with the convolution of the
pulled back kernels — the monoidality of derived pullback ([Stacks, Tag 079U]) and the
composition isomorphism ([Stacks, Tag 0D5S]) being what turn the pullback of
`L pr_{12}^*K ⊗^𝐋 L pr_{23}^*K'` into `L pr_{12}^*K₁ ⊗^𝐋 L pr_{23}^*K'₁`. On the other side the
square carrying `Δ_{X₁/S₁}` to `Δ_{X/S}` is cartesian, `X₁ ×_{S₁} X₁` and `X` are Tor
independent over `X ×_S X` by [Stacks, Tag 0CTA] (which is where flatness of `f` is used), and
`L^*𝒪_X[0] ≅ 𝒪_{X₁}[0]` because `𝒪_X` is flat; so `L^*` of the diagonal kernel is the diagonal
kernel. Perfectness transports by [Stacks, Tag 09UA].

Where the source uses smooth proper `f` and `g`, only flatness, separatedness and
quasi-compactness/quasi-separatedness are used here, so the hypotheses are weaker than the
source's; and `s` is arbitrary, as the source demands. The one granted input is `h08IB`. -/
@[stacks 0G0K "stability of relative-equivalence kernels under an ARBITRARY base change S1 -> S; \
f and g are only flat, separated and qcqs, all implied by the source's ambient smooth proper \
hypotheses. GRANTED: h08IB, the conclusion of Tag 08IB, which this tree lacks (it has the map of \
Tag 08HY and the affine input, not the globalization Tag 0DJ9) -- the same carry Tag 0FYS makes. \
All else (Tag 0CTA, Tag 09UA, flatness of pr13, Lp^*O_X[0] iso O_X1[0]) is proved here"]
theorem isRelativeEquivalenceKernel_derivedPullback
    (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    {S X Y S₁ : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (s : S₁ ⟶ S)
    [IsSeparated f] [IsSeparated g] [Flat f] [Flat g]
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    {K : DerivedCategory (pullback f g).Modules}
    (hK : IsRelativeEquivalenceKernel f g K) :
    IsRelativeEquivalenceKernel (pullback.snd f s) (pullback.snd g s)
      ((derivedPullback (fourierMukaiBaseChangeMap f g s).toLRSHom.toShHom).obj K) := by
  obtain ⟨hKperf, K', hK'perf, ⟨e₁⟩, ⟨e₂⟩⟩ := hK
  have hKq : IsQCohAll K := fun j =>
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K hKperf j
  have hK'q : IsQCohAll K' := fun j =>
    PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ K' hK'perf j
  refine ⟨RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K hKperf,
    (dpull (fourierMukaiBaseChangeMap g f s)).obj K',
    RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ K' hK'perf, ⟨?_⟩, ⟨?_⟩⟩
  · exact (diagonalKernelBaseChangeIso h08IB f s).symm ≪≫
      (dpull (fourierMukaiBaseChangeMap f f s)).mapIso e₁ ≪≫
      convolutionBaseChangeIso h08IB f g s hKq hK'q
  · exact (diagonalKernelBaseChangeIso h08IB g s).symm ≪≫
      (dpull (fourierMukaiBaseChangeMap g g s)).mapIso e₂ ≪≫
      convolutionBaseChangeIso h08IB g f s hK'q hKq

end Main

end AlgebraicGeometry

end
