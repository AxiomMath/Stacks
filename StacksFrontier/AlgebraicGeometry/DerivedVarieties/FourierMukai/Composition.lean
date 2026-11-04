module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.QuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeFour.FlatBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of Fourier-Mukai functors

Let `S` be a scheme and let `X`, `Y`, `Z` be schemes over `S` whose structure morphisms are
quasi-compact and quasi-separated.  Let `K` be a complex on `X ×_S Y` and `K'` a complex on
`Y ×_S Z`, both with quasi-coherent cohomology sheaves, and let

`Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`,  `Φ_{K'} : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_Z)`

be the Fourier-Mukai functors they define ([Stacks, Tag 0FYQ], [Stacks, Tag 0FYR]).  If `X` and
`Z` are tor independent over `S` and `Y ⟶ S` is flat, then `Φ_{K'} ∘ Φ_K = Φ_{K''}` where

`K'' = R pr_{13,*}(L pr_{12}^* K ⊗^𝐋_{𝒪_{X ×_S Y ×_S Z}} L pr_{23}^* K')`

on `X ×_S Z`.  This is [Stacks, Tag 0FYS].

The source's proof is a seven-step chain of equalities, run here as a chain of natural
isomorphisms: derived base change for the cartesian square `X ×_S Y ×_S Z ⟶ Y ×_S Z` over
`X ×_S Y ⟶ Y`, the monoidality of derived pullback ([Stacks, Tag 079U]), the projection formula
at `pr_{23}`, associativity of `⊗^𝐋`, the composition isomorphisms for derived pullback and
derived direct image ([Stacks, Tag 0D5S], [Stacks, Tag 079W]), and the projection formula at
`pr_{13}` together with the commutativity of `⊗^𝐋`.

## Main definitions

* `AlgebraicGeometry.fourierMukaiTripleProduct`, `AlgebraicGeometry.fourierMukaiPr12`,
  `AlgebraicGeometry.fourierMukaiPr23`, `AlgebraicGeometry.fourierMukaiPr13` — the triple fibre
  product `(X ×_S Y) ×_S Z` and the three projections it carries.
* `AlgebraicGeometry.fourierMukaiConvolution` — the convolution kernel `K''` on `X ×_S Z`.
* `AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent`,
  `AlgebraicGeometry.ProjectionFormulaIsIsoOnQuasicoherent` — the statements of
  [Stacks, Tag 08IB] and [Stacks, Tag 08EU], which are carried as hypotheses.

## Main results

* `AlgebraicGeometry.torIndependent_fourierMukaiMiddle` — **`X ×_S Y` and `Y ×_S Z` are tor
  independent over `Y`** when `X` and `Z` are tor independent over `S` and `Y ⟶ S` is flat.
  This is the source's first step, [Stacks, Tag 0FXW], and it is proved, not assumed.
* `AlgebraicGeometry.isPullback_fourierMukaiPr12_pr23` — the square
  `X ×_S Y ×_S Z ⟶ Y ×_S Z` over `X ×_S Y ⟶ Y` is cartesian.
* `AlgebraicGeometry.isQuasicoherent_homology_fourierMukaiConvolution` — the convolution kernel
  has quasi-coherent cohomology sheaves, so it is a Fourier-Mukai kernel in the sense of
  [Stacks, Tag 0FYR].
* `AlgebraicGeometry.quasiCoherentFourierMukaiComp` — **[Stacks, Tag 0FYS]**: the composite
  `Φ_{K'} ∘ Φ_K` is isomorphic to `Φ_{K''}` as a functor `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Z)`.

## Implementation notes

*An isomorphism, not an equality.*  The source writes `Φ_{K'} ∘ Φ_K = Φ_{K''}`.  Here the two
functors are built from derived pullback, the derived tensor product and derived direct image,
which are characterized by universal properties and so agree only up to canonical isomorphism;
each of the source's seven equalities is such a canonical isomorphism.  The honest rendering of
the conclusion is therefore a natural isomorphism of functors, and that is what is proved.
Nothing is weakened: every comparison in the chain is invertible, and the conclusion is an
isomorphism of the two functors on all of `D_QCoh(𝒪_X)`.

*Two carried hypotheses, each a Stacks result this library does not prove.*  The source's proof
uses two results that are present here only as maps, and each is carried as an explicit
hypothesis rather than silently assumed:

* `DerivedBaseChangeIsIsoOnQuasicoherent` is **[Stacks, Tag 08IB]**.  The library has the map,
  `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` ([Stacks, Tag 08HY]), and the
  Tor-independence input on a cartesian affine-open chart,
  `AlgebraicGeometry.BaseChangeChart.isIso_derivedBaseChangeComparison`, but not the
  globalization of the latter to the former, which is [Stacks, Tag 0DJ9].
* `ProjectionFormulaIsIsoOnQuasicoherent` is **[Stacks, Tag 08EU]**.  The library has the map,
  `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap` ([Stacks, Tag 0B53]), its
  naturality in both variables, and the case `A = 𝒪_W[0]` under four further hypotheses
  (`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject`), but not
  the dévissage in `A` that the general case needs.

Everything else is derived: [Stacks, Tag 0FXW] for the tor independence of the two factors over
`Y`, [Stacks, Tag 08DW], [Stacks, Tag 08DX] and [Stacks, Tag 08D5] for quasi-coherence of every
intermediate object, Schemes [Stacks, Tag 01K5] and [Stacks, Tag 01KU] for quasi-compactness and
quasi-separatedness of the projections, [Stacks, Tag 079U] for the monoidality of derived
pullback, [Stacks, Tag 0FPB] for the associativity and commutativity of `⊗^𝐋`, and
[Stacks, Tag 0D5S] and [Stacks, Tag 079W] for the two composition isomorphisms.

*The monoidal structure.*  Associativity and commutativity of `⊗^𝐋` are read through
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` and
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`, the symmetric monoidal
structure of [Stacks, Tag 0FPB] whose tensor bifunctor *is*
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`.  That identification is an
equality of bifunctors, so `CategoryTheory.MonoidalCategory.tensorRight` is on the nose the
tensor factor of `AlgebraicGeometry.fourierMukaiTensor`, and the Mathlib natural isomorphisms
`CategoryTheory.MonoidalCategory.tensorRightTensor` and
`CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight` apply without transport.  Only
naturality of those two constraints is used, never a coherence axiom.

*The triple product is left associated,* `(X ×_S Y) ×_S Z`, so that `pr_{12}` is a structural
projection and `pr_{23}`, `pr_{13}` are induced.  Quasi-compactness and quasi-separatedness of
the two induced maps are obtained by cancelling the structure morphism to `S`, rather than by
exhibiting each as a base change, which would need the associativity isomorphism of fibre
products.

## References

* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 0FYR](https://stacks.math.columbia.edu/tag/0FYR)
* [Stacks Project, Tag 0FXW](https://stacks.math.columbia.edu/tag/0FXW)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The triple fibre product and the three projections it carries -/

section Geometry

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The triple fibre product `X ×_S Y ×_S Z`, left associated as `(X ×_S Y) ×_S Z`. -/
abbrev fourierMukaiTripleProduct : Scheme.{u} := pullback (pullback.snd f g ≫ g) h

/-- The projection `pr_{12} : X ×_S Y ×_S Z ⟶ X ×_S Y`. -/
abbrev fourierMukaiPr12 : fourierMukaiTripleProduct f g h ⟶ pullback f g :=
  pullback.fst (pullback.snd f g ≫ g) h

/-- The projection `pr_3 : X ×_S Y ×_S Z ⟶ Z`. -/
abbrev fourierMukaiPr3 : fourierMukaiTripleProduct f g h ⟶ Z :=
  pullback.snd (pullback.snd f g ≫ g) h

/-- The projection `pr_{23} : X ×_S Y ×_S Z ⟶ Y ×_S Z`. -/
def fourierMukaiPr23 : fourierMukaiTripleProduct f g h ⟶ pullback g h :=
  pullback.lift (fourierMukaiPr12 f g h ≫ pullback.snd f g) (fourierMukaiPr3 f g h)
    ((Category.assoc _ _ _).trans pullback.condition)

/-- The projection `pr_{13} : X ×_S Y ×_S Z ⟶ X ×_S Z`. -/
def fourierMukaiPr13 : fourierMukaiTripleProduct f g h ⟶ pullback f h :=
  pullback.lift (fourierMukaiPr12 f g h ≫ pullback.fst f g) (fourierMukaiPr3 f g h)
    (by
      have h₁ : pullback.fst f g ≫ f = pullback.snd f g ≫ g := pullback.condition
      have h₂ : fourierMukaiPr12 f g h ≫ (pullback.snd f g ≫ g) =
          fourierMukaiPr3 f g h ≫ h := pullback.condition
      rw [Category.assoc, h₁, h₂])

/-- `pr_{23}` followed by the projection to `Y` is `pr_{12}` followed by the projection
to `Y`. -/
@[simp] lemma fourierMukaiPr23_fst :
    fourierMukaiPr23 f g h ≫ pullback.fst g h = fourierMukaiPr12 f g h ≫ pullback.snd f g :=
  pullback.lift_fst _ _ _

/-- `pr_{23}` followed by the projection to `Z` is `pr_3`. -/
@[simp] lemma fourierMukaiPr23_snd :
    fourierMukaiPr23 f g h ≫ pullback.snd g h = fourierMukaiPr3 f g h :=
  pullback.lift_snd _ _ _

/-- `pr_{13}` followed by the projection to `X` is `pr_{12}` followed by the projection
to `X`. -/
@[simp] lemma fourierMukaiPr13_fst :
    fourierMukaiPr13 f g h ≫ pullback.fst f h = fourierMukaiPr12 f g h ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

/-- `pr_{13}` followed by the projection to `Z` is `pr_3`. -/
@[simp] lemma fourierMukaiPr13_snd :
    fourierMukaiPr13 f g h ≫ pullback.snd f h = fourierMukaiPr3 f g h :=
  pullback.lift_snd _ _ _

/-- **The triple fibre product is the fibre product of `X ×_S Y` and `Y ×_S Z` over `Y`**:
the square with sides `pr_{12}`, `pr_{23}` over the two projections to `Y` is cartesian.
This is the square the source takes base change along. -/
lemma isPullback_fourierMukaiPr12_pr23 :
    IsPullback (fourierMukaiPr12 f g h) (fourierMukaiPr23 f g h) (pullback.snd f g)
      (pullback.fst g h) :=
  IsPullback.of_isLimit (pullbackPullbackLeftIsPullback f g g h)

/-- `pr_{12}` is quasi-compact when `h` is, being a base change of `h`. -/
instance quasiCompact_fourierMukaiPr12 [QuasiCompact h] :
    QuasiCompact (fourierMukaiPr12 f g h) :=
  inferInstanceAs (QuasiCompact (pullback.fst (pullback.snd f g ≫ g) h))

/-- `pr_{12}` is quasi-separated when `h` is, being a base change of `h`. -/
instance quasiSeparated_fourierMukaiPr12 [QuasiSeparated h] :
    QuasiSeparated (fourierMukaiPr12 f g h) :=
  inferInstanceAs (QuasiSeparated (pullback.fst (pullback.snd f g ≫ g) h))

/-- `pr_{23}` is quasi-compact: its composite with the quasi-separated structure morphism
`Y ×_S Z ⟶ S` is the quasi-compact structure morphism of the triple fibre product. -/
instance quasiCompact_fourierMukaiPr23 [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
    [QuasiSeparated g] [QuasiSeparated h] : QuasiCompact (fourierMukaiPr23 f g h) := by
  have : QuasiCompact (fourierMukaiPr23 f g h ≫ (pullback.snd g h ≫ h)) := by
    rw [← Category.assoc, fourierMukaiPr23_snd]; infer_instance
  exact QuasiCompact.of_comp (fourierMukaiPr23 f g h) (pullback.snd g h ≫ h)

/-- `pr_{23}` is quasi-separated: its composite with the structure morphism `Y ×_S Z ⟶ S` is
the quasi-separated structure morphism of the triple fibre product. -/
instance quasiSeparated_fourierMukaiPr23 [QuasiSeparated f] [QuasiSeparated g]
    [QuasiSeparated h] : QuasiSeparated (fourierMukaiPr23 f g h) := by
  have : QuasiSeparated (fourierMukaiPr23 f g h ≫ (pullback.snd g h ≫ h)) := by
    rw [← Category.assoc, fourierMukaiPr23_snd]; infer_instance
  exact QuasiSeparated.of_comp (fourierMukaiPr23 f g h) (pullback.snd g h ≫ h)

/-- `pr_{13}` is quasi-compact: its composite with the quasi-separated structure morphism
`X ×_S Z ⟶ S` is the quasi-compact structure morphism of the triple fibre product. -/
instance quasiCompact_fourierMukaiPr13 [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
    [QuasiSeparated f] [QuasiSeparated h] : QuasiCompact (fourierMukaiPr13 f g h) := by
  have : QuasiCompact (fourierMukaiPr13 f g h ≫ (pullback.snd f h ≫ h)) := by
    rw [← Category.assoc, fourierMukaiPr13_snd]; infer_instance
  exact QuasiCompact.of_comp (fourierMukaiPr13 f g h) (pullback.snd f h ≫ h)

/-- `pr_{13}` is quasi-separated: its composite with the structure morphism `X ×_S Z ⟶ S` is
the quasi-separated structure morphism of the triple fibre product. -/
instance quasiSeparated_fourierMukaiPr13 [QuasiSeparated f] [QuasiSeparated g]
    [QuasiSeparated h] : QuasiSeparated (fourierMukaiPr13 f g h) := by
  have : QuasiSeparated (fourierMukaiPr13 f g h ≫ (pullback.snd f h ≫ h)) := by
    rw [← Category.assoc, fourierMukaiPr13_snd]; infer_instance
  exact QuasiSeparated.of_comp (fourierMukaiPr13 f g h) (pullback.snd f h ≫ h)

end Geometry

/-! ### Tor independence of the two factors over the middle scheme -/

/-- Tor independence of two schemes over a base is unchanged when the second structure morphism
is precomposed with an isomorphism: the two sources have identified stalks, compatibly with the
algebra structures over the stalks of the base. -/
private lemma torIndependent_comp_iso_right {S X Y Y' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (e : Y' ≅ Y) (hTor : TorIndependent f g) : TorIndependent f (e.hom ≫ g) := by
  intro x y hxy
  let R := S.presheaf.stalk (f.base x)
  let A := X.presheaf.stalk x
  let B := Y.presheaf.stalk (e.hom.base y)
  let B' := Y'.presheaf.stalk y
  let _ : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let _ : Algebra R B :=
    (eqToHom (congrArg S.presheaf.stalk hxy) ≫ g.stalkMap (e.hom.base y)).hom.toAlgebra
  let _ : Algebra R B' :=
    (eqToHom (congrArg S.presheaf.stalk hxy) ≫ (e.hom ≫ g).stalkMap y).hom.toAlgebra
  let l : B →ₗ[R] B' :=
    { toFun := (e.hom.stalkMap y).hom
      map_add' := map_add _
      map_smul' := by
        intro r b
        change (e.hom.stalkMap y).hom
            (((eqToHom (congrArg S.presheaf.stalk hxy) ≫
              g.stalkMap (e.hom.base y)).hom r) * b) =
            ((eqToHom (congrArg S.presheaf.stalk hxy) ≫
              (e.hom ≫ g).stalkMap y).hom r) * (e.hom.stalkMap y).hom b
        rw [map_mul, Scheme.Hom.stalkMap_comp]
        rfl }
  let i := (LinearEquiv.ofBijective l
    (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap y))).toModuleIso
  intro n hn
  exact (((Tor (ModuleCat R) n).obj (ModuleCat.of R A)).mapIso i).isZero_iff.mp
    (hTor x (e.hom.base y) hxy n hn)

/-- **The two factors of the triple fibre product are tor independent over the middle scheme.**
If `X` and `Z` are tor independent over `S` and `Y ⟶ S` is flat, then `X ×_S Y` and `Y ×_S Z`
are tor independent over `Y`.  This is [Stacks, Tag 0FXW] for the flat base change `Y ⟶ S`,
followed by the symmetry `Y ×_S Z ≅ Z ×_S Y`.

No `@[stacks 0FXW]` attribute is carried here: Tag 0FXW is
`AlgebraicGeometry.torIndependent_pullback_of_flat`, and this is an application of it at a
particular pair of projections, not a clause of its statement. -/
lemma torIndependent_fourierMukaiMiddle {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : Z ⟶ S) [Flat g] (htor : TorIndependent f h) :
    TorIndependent (pullback.snd f g) (pullback.fst g h) := by
  have H := torIndependent_comp_iso_right (pullback.snd f g) (pullback.snd h g)
    (pullbackSymmetry g h) (torIndependent_pullback_of_flat f h g htor)
  simpa only [pullbackSymmetry_hom_comp_snd] using H

/-! ### The convolution kernel -/

section Convolution

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The complex `L pr_{12}^* K ⊗^𝐋 L pr_{23}^* K'` on the triple fibre product
`X ×_S Y ×_S Z`. -/
def fourierMukaiConvolutionTensor (K : DerivedCategory (pullback f g).Modules)
    (K' : DerivedCategory (pullback g h).Modules) :
    DerivedCategory (fourierMukaiTripleProduct f g h).Modules :=
  (((derivedTensorProductFunctor
        (fourierMukaiTripleProduct f g h).toRingedSpace.sheaf).flip.obj
      ((derivedPullback (fourierMukaiPr23 f g h).toLRSHom.toShHom).obj K')).obj
    ((derivedPullback (fourierMukaiPr12 f g h).toLRSHom.toShHom).obj K))

/-- **The convolution kernel of [Stacks, Tag 0FYS]**:
`K'' = R pr_{13,*}(L pr_{12}^* K ⊗^𝐋_{𝒪_{X ×_S Y ×_S Z}} L pr_{23}^* K')`, a complex
on `X ×_S Z`. -/
@[stacks 0FYS "the convolution kernel `K''`"]
def fourierMukaiConvolution (K : DerivedCategory (pullback f g).Modules)
    (K' : DerivedCategory (pullback g h).Modules) : DerivedCategory (pullback f h).Modules :=
  (derivedPushforward (fourierMukaiPr13 f g h).toLRSHom.toShHom).obj
    (fourierMukaiConvolutionTensor f g h K K')

end Convolution

/-! ### The two carried Stacks inputs -/

/-- **[Stacks, Tag 08IB] for complexes with quasi-coherent cohomology.**  For a cartesian square
of schemes with `f` quasi-compact and quasi-separated and `X`, `S'` tor independent over `S`, the
derived base change map `L g^*(R f_* K) ⟶ R f'_*(L g'^* K)` of [Stacks, Tag 08HY] is an
isomorphism for every `K` whose cohomology sheaves are quasi-coherent.

This library carries the map but not its invertibility; the globalization of the affine-chart
comparison that would prove it is [Stacks, Tag 0DJ9]. -/
abbrev DerivedBaseChangeIsIsoOnQuasicoherent : Prop :=
  ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S),
    IsPullback g' f' f g → QuasiCompact f → QuasiSeparated f → TorIndependent f g →
      ∀ (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
          f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom) (K : DerivedCategory X.Modules),
        (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent) →
        IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
          g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K)

/-- **[Stacks, Tag 08EU].**  For a quasi-compact and quasi-separated morphism of schemes
`p : V ⟶ W` and complexes `E` on `V` and `A` on `W` with quasi-coherent cohomology sheaves, the
projection-formula map `R p_* E ⊗^𝐋_{𝒪_W} A ⟶ R p_*(E ⊗^𝐋_{𝒪_V} L p^* A)` of
[Stacks, Tag 0B53] is an isomorphism.

This library carries the map, its naturality in both variables, and the case `A = 𝒪_W[0]` under
four further hypotheses, but not the dévissage in `A`. -/
abbrev ProjectionFormulaIsIsoOnQuasicoherent : Prop :=
  ∀ {V W : Scheme.{u}} (p : V ⟶ W), QuasiCompact p → QuasiSeparated p →
    ∀ (E : DerivedCategory V.Modules) (A : DerivedCategory W.Modules),
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor V.Modules j).obj E).IsQuasicoherent) →
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor W.Modules j).obj A).IsQuasicoherent) →
      IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
        p.toLRSHom.toShHom E A)

/-! ### Notation for the three derived operations -/

section Notation

variable {V W : Scheme.{u}}

/-- `L p^* : D(𝒪_W) ⥤ D(𝒪_V)`, the derived pullback along a morphism of schemes. -/
public abbrev dpull (p : V ⟶ W) : DerivedCategory W.Modules ⥤ DerivedCategory V.Modules :=
  derivedPullback p.toLRSHom.toShHom

/-- `R p_* : D(𝒪_V) ⥤ D(𝒪_W)`, the derived direct image along a morphism of schemes. -/
public abbrev dpush (p : V ⟶ W) : DerivedCategory V.Modules ⥤ DerivedCategory W.Modules :=
  derivedPushforward p.toLRSHom.toShHom

/-- `- ⊗^𝐋_{𝒪_W} A`, the derived tensor product with a fixed complex `A` on `W`. -/
public abbrev dtenR (W : Scheme.{u}) (A : DerivedCategory W.Modules) :
    DerivedCategory W.Modules ⥤ DerivedCategory W.Modules :=
  (derivedTensorProductFunctor W.toRingedSpace.sheaf).flip.obj A

/-- `A ⊗^𝐋_{𝒪_W} -`, the derived tensor product with a fixed complex `A` on the left. -/
private abbrev dtenL (W : Scheme.{u}) (A : DerivedCategory W.Modules) :
    DerivedCategory W.Modules ⥤ DerivedCategory W.Modules :=
  (derivedTensorProductFunctor W.toRingedSpace.sheaf).obj A

/-- Quasi-coherence of every cohomology sheaf of a complex on a scheme. -/
public abbrev IsQCohAll (A : DerivedCategory W.Modules) : Prop :=
  ∀ j : ℤ, ((DerivedCategory.homologyFunctor W.Modules j).obj A).IsQuasicoherent

/-- The morphism of ringed spaces underlying a composite of morphisms of schemes is the
composite of the underlying morphisms of ringed spaces. -/
public lemma shHom_comp {U : Scheme.{u}} (p : U ⟶ V) (q : V ⟶ W) :
    (p ≫ q).toLRSHom.toShHom = p.toLRSHom.toShHom ≫ q.toLRSHom.toShHom := by
  rw [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom]

/-- Two equal composites of morphisms of schemes have equal underlying composites of morphisms
of ringed spaces. -/
public lemma shHom_comp_eq {U V V' W : Scheme.{u}} {p : U ⟶ V} {q : V ⟶ W} {p' : U ⟶ V'}
    {q' : V' ⟶ W} (hpq : p ≫ q = p' ≫ q') :
    p.toLRSHom.toShHom ≫ q.toLRSHom.toShHom =
      p'.toLRSHom.toShHom ≫ q'.toLRSHom.toShHom := by
  rw [← shHom_comp p q, ← shHom_comp p' q', hpq]

/-- **[Stacks, Tag 0D5S] for schemes**, at two factorizations of one morphism:
`L q^* ⋙ L p^* ≅ L q'^* ⋙ L p'^*` when `p ≫ q = p' ≫ q'`, both sides being the derived
pullback along that common composite. -/
public def dpullCompIsoEq {U V V' W : Scheme.{u}} (p : U ⟶ V) (q : V ⟶ W) (p' : U ⟶ V')
    (q' : V' ⟶ W) (hpq : p ≫ q = p' ≫ q') : dpull q ⋙ dpull p ≅ dpull q' ⋙ dpull p' := by
  refine Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      p.toLRSHom.toShHom q.toLRSHom.toShHom ≪≫ ?_ ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      p'.toLRSHom.toShHom q'.toLRSHom.toShHom).symm
  exact eqToIso (by rw [shHom_comp_eq hpq])

/-- **[Stacks, Tag 079W] for schemes**, at two factorizations of one morphism:
`R p_* ⋙ R q_* ≅ R p'_* ⋙ R q'_*` when `p ≫ q = p' ≫ q'`, both sides being the derived direct
image along that common composite. -/
private def dpushCompIsoEq {U V V' W : Scheme.{u}} (p : U ⟶ V) (q : V ⟶ W) (p' : U ⟶ V')
    (q' : V' ⟶ W) (hpq : p ≫ q = p' ≫ q') : dpush p ⋙ dpush q ≅ dpush p' ⋙ dpush q' := by
  refine derivedPushforwardCompIso p.toLRSHom.toShHom q.toLRSHom.toShHom ≪≫ ?_ ≪≫
    (derivedPushforwardCompIso p'.toLRSHom.toShHom q'.toLRSHom.toShHom).symm
  exact eqToIso (by rw [shHom_comp_eq hpq])

/-- Quasi-coherence is preserved by derived pullback, [Stacks, Tag 08DW] part (1). -/
public lemma isQCohAll_dpull (p : V ⟶ W) {A : DerivedCategory W.Modules} (hA : IsQCohAll A) :
    IsQCohAll ((dpull p).obj A) :=
  fun j => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel p A hA j

/-- Quasi-coherence is preserved by the derived tensor product, [Stacks, Tag 08DX] part (1). -/
public lemma isQCohAll_dtenR {A B : DerivedCategory W.Modules} (hA : IsQCohAll A)
    (hB : IsQCohAll B) : IsQCohAll ((dtenR W B).obj A) :=
  fun j => TorFormula.isQuasicoherent_homology_derivedTensor W A B hA hB j

/-- Quasi-coherence is preserved by derived direct image along a quasi-compact and
quasi-separated morphism, [Stacks, Tag 08D5] part (1). -/
private lemma isQCohAll_dpush (p : V ⟶ W) [QuasiCompact p] [QuasiSeparated p]
    {A : DerivedCategory V.Modules} (hA : IsQCohAll A) : IsQCohAll ((dpush p).obj A) :=
  fun j => isQuasicoherent_derivedPushforward_affineLocal p ⟨A, hA⟩ j

end Notation

/-! ### Quasi-coherence of the convolution kernel -/

section ConvolutionQCoh

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)

/-- The cohomology sheaves of `L pr_{12}^* K ⊗^𝐋 L pr_{23}^* K'` are quasi-coherent, by
[Stacks, Tag 08DW] part (1) and [Stacks, Tag 08DX] part (1). -/
private lemma isQCohAll_fourierMukaiConvolutionTensor
    {K : DerivedCategory (pullback f g).Modules} (hK : IsQCohAll K)
    {K' : DerivedCategory (pullback g h).Modules} (hK' : IsQCohAll K') :
    IsQCohAll (fourierMukaiConvolutionTensor f g h K K') :=
  isQCohAll_dtenR (isQCohAll_dpull _ hK) (isQCohAll_dpull _ hK')

variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  [QuasiCompact h] [QuasiSeparated h]

/-- **The convolution kernel has quasi-coherent cohomology sheaves**, so the Fourier-Mukai
functor it defines carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Z)` by [Stacks, Tag 0FYR]: pull back by
[Stacks, Tag 08DW] part (1), tensor by [Stacks, Tag 08DX] part (1), and push forward along the
quasi-compact and quasi-separated morphism `pr_{13}` by [Stacks, Tag 08D5] part (1). -/
@[stacks 0FYS "quasi-coherence of the convolution kernel; the clause making the statement \
  of the lemma meaningful"]
theorem isQuasicoherent_homology_fourierMukaiConvolution
    {K : DerivedCategory (pullback f g).Modules}
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (pullback f g).Modules j).obj
      K).IsQuasicoherent)
    {K' : DerivedCategory (pullback g h).Modules}
    (hK' : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (pullback g h).Modules j).obj
      K').IsQuasicoherent)
    (j : ℤ) :
    ((DerivedCategory.homologyFunctor (pullback f h).Modules j).obj
      (fourierMukaiConvolution f g h K K')).IsQuasicoherent :=
  isQCohAll_dpush _ (isQCohAll_fourierMukaiConvolutionTensor f g h hK hK') j

end ConvolutionQCoh

/-! ### The comparison maps, as natural transformations -/

section Comparisons

/-- Specializing a bifunctorial comparison at its second argument: an isomorphism of
bifunctors `T(-, -) ∘ P ≅ T'(P -, P -)` gives, for each `A`, an isomorphism of functors
`(- ⊗ A) ⋙ P ≅ P ⋙ (- ⊗ P A)`. -/
public def flipWhiskerIso {C D : Type*} [Category C] [Category D]
    {T : C ⥤ C ⥤ C} {T' : D ⥤ D ⥤ D} {P : C ⥤ D}
    (e : Functor.uncurry.obj T ⋙ P ≅ P.prod P ⋙ Functor.uncurry.obj T') (A : C) :
    T.flip.obj A ⋙ P ≅ P ⋙ T'.flip.obj (P.obj A) := by
  refine NatIso.ofComponents (fun M => e.app (M, A)) ?_
  intro M N a
  have hn := e.hom.naturality (X := (M, A)) (Y := (N, A)) (a, 𝟙 A)
  dsimp at hn ⊢
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn

variable {V W : Scheme.{u}}

/-- **[Stacks, Tag 079U] at a fixed second factor**: the monoidality of derived pullback read as
an isomorphism of functors in the first factor,
`(- ⊗^𝐋 A) ⋙ L p^* ≅ L p^* ⋙ (- ⊗^𝐋 L p^* A)`. -/
public def dpullTensorIso (p : V ⟶ W) (A : DerivedCategory W.Modules) :
    dtenR W A ⋙ dpull p ≅ dpull p ⋙ dtenR V ((dpull p).obj A) :=
  flipWhiskerIso (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
    p.toLRSHom.toShHom) A

/-- The derived base change transformation `R f_* ⋙ L g^* ⟶ L g'^* ⋙ R f'_*` of
[Stacks, Tag 08HY], attached to a commutative square of schemes. -/
public abbrev dbaseChange {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S)
    (g : S' ⟶ S) (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom) :
    dpush f ⋙ dpull g ⟶ dpull g' ⋙ dpush f' :=
  Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare g'.toLRSHom.toShHom
    f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq

/-- The projection-formula transformation of [Stacks, Tag 0B53] read in the source complex:
`R p_* ⋙ (- ⊗^𝐋 A) ⟶ (- ⊗^𝐋 L p^* A) ⋙ R p_*`. -/
private def dprojectionLeft (p : V ⟶ W) (A : DerivedCategory W.Modules) :
    dpush p ⋙ dtenR W A ⟶ dtenR V ((dpull p).obj A) ⋙ dpush p where
  app E := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
    p.toLRSHom.toShHom E A
  naturality _ _ e := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_left
    p.toLRSHom.toShHom e A

/-- The projection-formula transformation of [Stacks, Tag 0B53] read in the target complex:
`(R p_* E) ⊗^𝐋 - ⟶ L p^* ⋙ (E ⊗^𝐋 -) ⋙ R p_*`. -/
private def dprojectionRight (p : V ⟶ W) (E : DerivedCategory V.Modules) :
    dtenL W ((dpush p).obj E) ⟶ dpull p ⋙ dtenL V E ⋙ dpush p where
  app A := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
    p.toLRSHom.toShHom E A
  naturality _ _ a :=
    Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
      p.toLRSHom.toShHom E a

end Comparisons

/-! ### Associativity and commutativity of the derived tensor product -/

section Monoidal

variable (W : Scheme.{u})

/-- The monoidal structure of [Stacks, Tag 0FPB] on `D(𝒪_W)`, whose tensor bifunctor is
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` on the nose. -/
private abbrev dmonoidal : MonoidalCategory (DerivedCategory W.Modules) :=
  Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal W.toRingedSpace.sheaf

/-- The commutativity constraint of the structure of [Stacks, Tag 0FPB] on `D(𝒪_W)`. -/
private abbrev dsymmetric :
    letI := dmonoidal W
    SymmetricCategory (DerivedCategory W.Modules) :=
  Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric W.toRingedSpace.sheaf

/-- **Associativity of the derived tensor product**, as an isomorphism of functors
`(- ⊗^𝐋 A) ⋙ (- ⊗^𝐋 B) ≅ - ⊗^𝐋 (A ⊗^𝐋 B)`.  Only naturality of the associator is used. -/
private def dtenRCompIso (A B : DerivedCategory W.Modules) :
    dtenR W A ⋙ dtenR W B ≅ dtenR W ((dtenR W B).obj A) :=
  letI := dmonoidal W
  (tensorRightTensor A B).symm

/-- **Commutativity of the derived tensor product**, as an isomorphism of functors
`- ⊗^𝐋 A ≅ A ⊗^𝐋 -`.  Only naturality of the braiding is used. -/
private def dtenSwapIso (A : DerivedCategory W.Modules) : dtenR W A ≅ dtenL W A :=
  letI := dmonoidal W
  letI := dsymmetric W
  (BraidedCategory.tensorLeftIsoTensorRight A).symm

end Monoidal

/-! ### The composition of Fourier-Mukai functors -/

section Main

/-- The inclusion of the complexes with quasi-coherent cohomology into the derived category. -/
private abbrev qcohι (W : Scheme.{u}) :
    QuasicoherentDerivedCategory W ⥤ DerivedCategory W.Modules :=
  (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent W.ringCatSheaf)).ι

/-- A natural transformation whiskered on the left by `F` is an isomorphism once it is an
isomorphism at every object of the form `F.obj M`. -/
private lemma isIso_whiskerLeft_of_isIso_app {C D E : Type*} [Category C] [Category D]
    [Category E] (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) (hα : ∀ M, IsIso (α.app (F.obj M))) :
    IsIso (Functor.whiskerLeft F α) :=
  haveI : ∀ M, IsIso ((Functor.whiskerLeft F α).app M) := hα
  NatIso.isIso_of_isIso_app _

/-- **The last equality of [Stacks, Tag 0FYS]**: the projection formula at a quasi-compact and
quasi-separated `p`, read in the target complex and transported by the commutativity constraint.
For a functor `F` whose values have quasi-coherent cohomology,
`F ⋙ L p^* ⋙ (- ⊗^𝐋 E) ⋙ R p_* ≅ F ⋙ (- ⊗^𝐋 R p_* E)`. -/
private def dprojectionRightIso (h08EU : ProjectionFormulaIsIsoOnQuasicoherent.{u})
    {C : Type*} [Category C] {V W : Scheme.{u}} (p : V ⟶ W) [QuasiCompact p]
    [QuasiSeparated p] (F : C ⥤ DerivedCategory W.Modules)
    (hF : ∀ M, IsQCohAll (F.obj M)) {E : DerivedCategory V.Modules} (hE : IsQCohAll E) :
    F ⋙ dpull p ⋙ dtenR V E ⋙ dpush p ≅ F ⋙ dtenR W ((dpush p).obj E) := by
  haveI := isIso_whiskerLeft_of_isIso_app F (dprojectionRight p E) fun M =>
    h08EU p inferInstance inferInstance E (F.obj M) hE (hF M)
  exact (Functor.isoWhiskerLeft F (dtenSwapIso W ((dpush p).obj E)) ≪≫
    asIso (Functor.whiskerLeft F (dprojectionRight p E)) ≪≫
    Functor.isoWhiskerLeft (F ⋙ dpull p)
      (Functor.isoWhiskerRight (dtenSwapIso V E).symm (dpush p))).symm

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  [QuasiCompact h] [QuasiSeparated h]

/-- **[Stacks, Tag 0FYS] before restricting to the quasi-coherent subcategories**: the composite
`Φ_{K'} ∘ Φ_K` and `Φ_{K''}`, read on `D(𝒪_X)` but precomposed with the inclusion of the
complexes with quasi-coherent cohomology, are naturally isomorphic.

This is the source's chain, in its seven steps: derived base change for the cartesian square
`X ×_S Y ×_S Z ⟶ Y ×_S Z` over `X ×_S Y ⟶ Y`, which applies because the two factors are tor
independent over `Y`; the monoidality of derived pullback; the projection formula at `pr_{23}`;
associativity of `⊗^𝐋`; the composition isomorphism `L pr_1^* ≅ L pr_{12}^* L p_X^*`; the
composition isomorphism `R pr_{3,*} ≅ R p_{Z,*} R pr_{23,*}`; and the projection formula at
`pr_{13}`. -/
private def fourierMukaiCompIsoAux (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    (h08EU : ProjectionFormulaIsIsoOnQuasicoherent.{u}) [Flat g] (htor : TorIndependent f h)
    {K : DerivedCategory (pullback f g).Modules} (hK : IsQCohAll K)
    {K' : DerivedCategory (pullback g h).Modules} (hK' : IsQCohAll K') :
    qcohι X ⋙ fourierMukai f g K ⋙ fourierMukai g h K' ≅
      qcohι X ⋙ fourierMukai f h (fourierMukaiConvolution f g h K K') := by
  have hsq := shHom_comp_eq (isPullback_fourierMukaiPr12_pr23 f g h).w
  -- the first factor of the composite, which takes values in quasi-coherent complexes
  have hAq : ∀ M, IsQCohAll ((qcohι X ⋙ dpull (pullback.fst f g) ⋙
      dtenR (pullback f g) K).obj M) := fun M =>
    isQCohAll_dtenR (isQCohAll_dpull _ M.property) hK
  -- the pulled back kernels and their tensor product
  have hK₁₂ : IsQCohAll ((dpull (fourierMukaiPr12 f g h)).obj K) := isQCohAll_dpull _ hK
  have hK₂₃ : IsQCohAll ((dpull (fourierMukaiPr23 f g h)).obj K') := isQCohAll_dpull _ hK'
  have hE : IsQCohAll (fourierMukaiConvolutionTensor f g h K K') :=
    isQCohAll_fourierMukaiConvolutionTensor f g h hK hK'
  -- the functor entering the projection formula at `pr₂₃`
  have hBq : ∀ M, IsQCohAll ((qcohι X ⋙ dpull (pullback.fst f g) ⋙
      dpull (fourierMukaiPr12 f g h) ⋙
      dtenR (fourierMukaiTripleProduct f g h)
        ((dpull (fourierMukaiPr12 f g h)).obj K)).obj M) := fun M =>
    isQCohAll_dtenR (isQCohAll_dpull _ (isQCohAll_dpull _ M.property)) hK₁₂
  -- step 1: derived base change along the cartesian square, [Stacks, Tag 08IB]
  haveI := isIso_whiskerLeft_of_isIso_app (qcohι X ⋙ dpull (pullback.fst f g) ⋙
      dtenR (pullback f g) K)
      (dbaseChange (fourierMukaiPr12 f g h) (fourierMukaiPr23 f g h) (pullback.snd f g)
        (pullback.fst g h) hsq) fun M =>
    h08IB (fourierMukaiPr12 f g h) (fourierMukaiPr23 f g h) (pullback.snd f g)
      (pullback.fst g h) (isPullback_fourierMukaiPr12_pr23 f g h) inferInstance inferInstance
      (torIndependent_fourierMukaiMiddle f g h htor) hsq _ (hAq M)
  -- step 3: the projection formula at `pr₂₃`, [Stacks, Tag 08EU]
  haveI := isIso_whiskerLeft_of_isIso_app (qcohι X ⋙ dpull (pullback.fst f g) ⋙
      dpull (fourierMukaiPr12 f g h) ⋙
      dtenR (fourierMukaiTripleProduct f g h) ((dpull (fourierMukaiPr12 f g h)).obj K))
      (dprojectionLeft (fourierMukaiPr23 f g h) K') fun M =>
    h08EU (fourierMukaiPr23 f g h) inferInstance inferInstance _ K' (hBq M) hK'
  -- the two commutativities of projections used in steps 5 and 6
  have hx : fourierMukaiPr12 f g h ≫ pullback.fst f g =
      fourierMukaiPr13 f g h ≫ pullback.fst f h := (fourierMukaiPr13_fst f g h).symm
  have hz : fourierMukaiPr23 f g h ≫ pullback.snd g h =
      fourierMukaiPr13 f g h ≫ pullback.snd f h :=
    (fourierMukaiPr23_snd f g h).trans (fourierMukaiPr13_snd f g h).symm
  calc qcohι X ⋙ fourierMukai f g K ⋙ fourierMukai g h K'
      -- step 1
      ≅ (qcohι X ⋙ dpull (pullback.fst f g) ⋙ dtenR (pullback f g) K) ⋙
          (dpull (fourierMukaiPr12 f g h) ⋙ dpush (fourierMukaiPr23 f g h)) ⋙
          dtenR (pullback g h) K' ⋙ dpush (pullback.snd g h) :=
        Functor.isoWhiskerRight (asIso (Functor.whiskerLeft
          (qcohι X ⋙ dpull (pullback.fst f g) ⋙ dtenR (pullback f g) K)
          (dbaseChange (fourierMukaiPr12 f g h) (fourierMukaiPr23 f g h) (pullback.snd f g)
            (pullback.fst g h) hsq)))
          (dtenR (pullback g h) K' ⋙ dpush (pullback.snd g h))
      -- step 2: monoidality of derived pullback
    _ ≅ (qcohι X ⋙ dpull (pullback.fst f g) ⋙ dpull (fourierMukaiPr12 f g h) ⋙
          dtenR (fourierMukaiTripleProduct f g h)
            ((dpull (fourierMukaiPr12 f g h)).obj K)) ⋙
          dpush (fourierMukaiPr23 f g h) ⋙ dtenR (pullback g h) K' ⋙
          dpush (pullback.snd g h) :=
        Functor.isoWhiskerLeft (qcohι X ⋙ dpull (pullback.fst f g))
          (Functor.isoWhiskerRight (dpullTensorIso (fourierMukaiPr12 f g h) K)
            (dpush (fourierMukaiPr23 f g h) ⋙ dtenR (pullback g h) K' ⋙
              dpush (pullback.snd g h)))
      -- step 3: the projection formula at `pr₂₃`
    _ ≅ (qcohι X ⋙ dpull (pullback.fst f g) ⋙ dpull (fourierMukaiPr12 f g h) ⋙
          dtenR (fourierMukaiTripleProduct f g h)
            ((dpull (fourierMukaiPr12 f g h)).obj K)) ⋙
          dtenR (fourierMukaiTripleProduct f g h)
            ((dpull (fourierMukaiPr23 f g h)).obj K') ⋙
          dpush (fourierMukaiPr23 f g h) ⋙ dpush (pullback.snd g h) :=
        Functor.isoWhiskerRight (asIso (Functor.whiskerLeft
          (qcohι X ⋙ dpull (pullback.fst f g) ⋙ dpull (fourierMukaiPr12 f g h) ⋙
            dtenR (fourierMukaiTripleProduct f g h)
              ((dpull (fourierMukaiPr12 f g h)).obj K))
          (dprojectionLeft (fourierMukaiPr23 f g h) K'))) (dpush (pullback.snd g h))
      -- step 4: associativity of the derived tensor product
    _ ≅ qcohι X ⋙ dpull (pullback.fst f g) ⋙ dpull (fourierMukaiPr12 f g h) ⋙
          dtenR (fourierMukaiTripleProduct f g h)
            (fourierMukaiConvolutionTensor f g h K K') ⋙
          dpush (fourierMukaiPr23 f g h) ⋙ dpush (pullback.snd g h) :=
        Functor.isoWhiskerLeft
          (qcohι X ⋙ dpull (pullback.fst f g) ⋙ dpull (fourierMukaiPr12 f g h))
          (Functor.isoWhiskerRight
            (dtenRCompIso (fourierMukaiTripleProduct f g h)
              ((dpull (fourierMukaiPr12 f g h)).obj K)
              ((dpull (fourierMukaiPr23 f g h)).obj K'))
            (dpush (fourierMukaiPr23 f g h) ⋙ dpush (pullback.snd g h)))
      -- step 5: `L pr_1^* ≅ L pr_{12}^* L p_X^*` read the other way round
    _ ≅ qcohι X ⋙ dpull (pullback.fst f h) ⋙ dpull (fourierMukaiPr13 f g h) ⋙
          dtenR (fourierMukaiTripleProduct f g h)
            (fourierMukaiConvolutionTensor f g h K K') ⋙
          dpush (fourierMukaiPr23 f g h) ⋙ dpush (pullback.snd g h) :=
        Functor.isoWhiskerLeft (qcohι X) (Functor.isoWhiskerRight
          (dpullCompIsoEq (fourierMukaiPr12 f g h) (pullback.fst f g)
            (fourierMukaiPr13 f g h) (pullback.fst f h) hx)
          (dtenR (fourierMukaiTripleProduct f g h)
            (fourierMukaiConvolutionTensor f g h K K') ⋙
            dpush (fourierMukaiPr23 f g h) ⋙ dpush (pullback.snd g h)))
      -- step 6: `R pr_{3,*} ≅ R p_{Z,*} R pr_{23,*}` read the other way round
    _ ≅ (qcohι X ⋙ dpull (pullback.fst f h)) ⋙ dpull (fourierMukaiPr13 f g h) ⋙
          dtenR (fourierMukaiTripleProduct f g h)
            (fourierMukaiConvolutionTensor f g h K K') ⋙
          dpush (fourierMukaiPr13 f g h) ⋙ dpush (pullback.snd f h) :=
        Functor.isoWhiskerLeft (qcohι X ⋙ dpull (pullback.fst f h) ⋙
          dpull (fourierMukaiPr13 f g h) ⋙
          dtenR (fourierMukaiTripleProduct f g h)
            (fourierMukaiConvolutionTensor f g h K K'))
          (dpushCompIsoEq (fourierMukaiPr23 f g h) (pullback.snd g h)
            (fourierMukaiPr13 f g h) (pullback.snd f h) hz)
      -- step 7: the projection formula at `pr₁₃`
    _ ≅ qcohι X ⋙ fourierMukai f h (fourierMukaiConvolution f g h K K') :=
        Functor.isoWhiskerRight
          (dprojectionRightIso h08EU (fourierMukaiPr13 f g h)
            (qcohι X ⋙ dpull (pullback.fst f h))
            (fun M => isQCohAll_dpull _ M.property) hE)
          (dpush (pullback.snd f h))

/-- **[Stacks, Tag 0FYS].**  Let `S` be a scheme and let `X`, `Y`, `Z` be schemes over `S` with
`f : X ⟶ S`, `g : Y ⟶ S` and `h : Z ⟶ S` quasi-compact and quasi-separated.  Let `K` on
`X ×_S Y` and `K'` on `Y ×_S Z` have quasi-coherent cohomology sheaves, and consider the
Fourier-Mukai functors `Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` and
`Φ_{K'} : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_Z)`.  If `X` and `Z` are tor independent over `S` and `g` is
flat, then `Φ_{K'} ∘ Φ_K ≅ Φ_{K''}` where
`K'' = R pr_{13,*}(L pr_{12}^* K ⊗^𝐋 L pr_{23}^* K')` on `X ×_S Z`.

The source states the conclusion as an equality of functors; since both sides are built from
derived functors, which are determined only up to canonical isomorphism, the faithful rendering
is this natural isomorphism, and each of the source's seven equalities supplies one invertible
comparison in the chain that builds it. -/
@[stacks 0FYS "composition of Fourier-Mukai functors, as the natural isomorphism of functors \
  D_QCoh(O_X) to D_QCoh(O_Z) that the source writes as an equality; granted Stacks 08IB (whose \
  route, Stacks 0DJ9, the library does not carry) as the hypothesis h08IB and Stacks 08EU as \
  the hypothesis h08EU", no_expose]
def quasiCoherentFourierMukaiComp (h08IB : DerivedBaseChangeIsIsoOnQuasicoherent.{u})
    (h08EU : ProjectionFormulaIsIsoOnQuasicoherent.{u}) [Flat g] (htor : TorIndependent f h)
    {K : DerivedCategory (pullback f g).Modules}
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (pullback f g).Modules j).obj
      K).IsQuasicoherent)
    {K' : DerivedCategory (pullback g h).Modules}
    (hK' : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (pullback g h).Modules j).obj
      K').IsQuasicoherent) :
    quasiCoherentFourierMukai f g K hK ⋙ quasiCoherentFourierMukai g h K' hK' ≅
      quasiCoherentFourierMukai f h (fourierMukaiConvolution f g h K K')
        (isQuasicoherent_homology_fourierMukaiConvolution f g h hK hK') := by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    ((fourierMukaiCompIsoAux f g h h08IB h08EU htor hK hK').app M)) ?_
  intro M N v
  apply ObjectProperty.hom_ext
  exact (fourierMukaiCompIsoAux f g h h08IB h08EU htor hK hK').hom.naturality v

end Main

end AlgebraicGeometry

end
