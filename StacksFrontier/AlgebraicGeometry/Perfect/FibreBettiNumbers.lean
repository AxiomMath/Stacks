module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# The Betti numbers of the fibres of a flat proper family

Let `f : X ⟶ S` be a proper morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of
finite presentation, flat over `S`.  For an integer `i` the `i`-th Betti-number function of the
family is

`β_i : S → ℕ`,   `β_i(s) = dim_{κ(s)} H^i(X_s, ℱ_s)`,

where `X_s` is the scheme-theoretic fibre of `f` at `s`, a scheme over `Spec κ(s)`, and `ℱ_s` is
the pullback of `ℱ` to it.  [Stacks, Tag 0BDN] asserts three things about `β_i`: its formation
commutes with arbitrary base change, it is upper semi-continuous, and its level sets are locally
constructible. This file sets up `β_i` and the hypotheses on the family; the three parts are
proved in `StacksFrontier/AlgebraicGeometry/Perfect/FibreBettiNumbersCohomologyBaseChange.lean`, as
`AlgebraicGeometry.FibreBetti.fibreBetti_baseChange_upperSemicontinuous_isLocallyConstructible`.

## Main definitions

* `AlgebraicGeometry.FibreBetti.totalDirectImage` is `Rf_*ℱ`, the derived pushforward of `ℱ`
  placed in degree zero.
* `AlgebraicGeometry.FibreBetti.fibreBetti` is `β_i`: the dimension over `κ(s)` of the degree-`i`
  cohomology of `ℱ_s` on the fibre `X_s`, read as the global sections on `Spec κ(s)` of the
  degree-`i` cohomology of the derived pushforward of `ℱ_s` along `X_s ⟶ Spec κ(s)`.
* `AlgebraicGeometry.FibreBetti.IsFlatFamily` collects the four hypotheses of
  [Stacks, Tag 0BDN]: `f` is proper and of finite presentation, and `ℱ` is of finite presentation
  and flat over `S`.
* `AlgebraicGeometry.FibreBetti.CohomologyAndBaseChange` adds to those that `Rf_*ℱ` is
  pseudo-coherent and that `β_i` is the derived-fibre Betti function of `Rf_*ℱ`.
* `AlgebraicGeometry.FibreBetti.BaseChangeCompatible` is the compatibility of the formation of
  `Rf_*ℱ` with a cartesian square.

## Main results

* `AlgebraicGeometry.FibreBetti.derivedFiberBetti_eq_of_iso`: the derived-fibre Betti function of
  an object of the derived category depends only on its isomorphism class.
* `AlgebraicGeometry.FibreBetti.fibreBetti_baseChange`: the formation of `β_i` commutes with base
  change, given `CohomologyAndBaseChange` and `BaseChangeCompatible`.
* `AlgebraicGeometry.FibreBetti.upperSemicontinuous_fibreBetti`: `β_i` is upper semi-continuous,
  given `CohomologyAndBaseChange` and upper semi-continuity on each affine open of `S`.

Both data hold for every family satisfying the hypotheses of [Stacks, Tag 0BDN], by
[Stacks, Tag 0B91].

## References

* [Stacks Project, Tag 0BDN](https://stacks.math.columbia.edu/tag/0BDN)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.FibreBetti

/-! ### The Betti numbers of the fibres -/

/-- The derived pushforward `Rf_*ℱ` along `f` of the `𝒪_X`-module `ℱ` placed in degree zero. -/
public def totalDirectImage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    DerivedCategory S.Modules :=
  (derivedPushforward f.toLRSHom.toShHom).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj F)

/-- The `i`-th Betti-number function of the family `(f, ℱ)`: its value at `s` is
`dim_{κ(s)} H^i(X_s, ℱ_s)`, the dimension over the residue field `κ(s)` of the degree-`i`
cohomology on the fibre `X_s` of the pullback of `ℱ` to that fibre, read through the derived
pushforward to `Spec κ(s)` and global sections there. -/
public def fibreBetti {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (i : ℤ) : S → ℕ :=
  fun s =>
    Module.finrank (S.residueField s)
      ((moduleSpecΓFunctor (R := S.residueField s)).obj
        ((DerivedCategory.homologyFunctor (Spec (S.residueField s)).Modules i).obj
          ((derivedPushforward (f.fiberToSpecResidueField s).toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor (f.fiber s).Modules 0).obj
              ((Scheme.Modules.pullback (f.fiberι s)).obj F)))))

/-- The defining formula for the Betti-number function of a family. -/
@[simp]
public theorem fibreBetti_apply {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (i : ℤ) (s : S) :
    fibreBetti f F i s =
      Module.finrank (S.residueField s)
        ((moduleSpecΓFunctor (R := S.residueField s)).obj
          ((DerivedCategory.homologyFunctor (Spec (S.residueField s)).Modules i).obj
            ((derivedPushforward (f.fiberToSpecResidueField s).toLRSHom.toShHom).obj
              ((DerivedCategory.singleFunctor (f.fiber s).Modules 0).obj
                ((Scheme.Modules.pullback (f.fiberι s)).obj F))))) :=
  rfl

/-! ### The hypotheses on the family -/

/-- The hypotheses of [Stacks, Tag 0BDN] on the pair `(f, ℱ)`: `f` is a proper morphism of
finite presentation and `ℱ` is an `𝒪_X`-module of finite presentation, flat over `S`. -/
public structure IsFlatFamily {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Prop where
  /-- `f` is of finite presentation. -/
  finitePresentation : FinitePresentation f
  /-- `f` is proper. -/
  isProper : IsProper f
  /-- `ℱ` is of finite presentation. -/
  isFinitePresentation : F.IsFinitePresentation
  /-- `ℱ` is flat over `S`. -/
  isFlatOver : IsFlatOver f.toLRSHom.toShHom F

/-- Cohomology and base change for the family `(f, ℱ)`: on top of the hypotheses of
[Stacks, Tag 0BDN], `Rf_*ℱ` is pseudo-coherent and `β_i` is its derived-fibre Betti function,
that is, `H^i(X_s, ℱ_s) = H^i(Rf_*ℱ ⊗^L_{𝒪_S} κ(s))` for every `s` and `i`. -/
public structure CohomologyAndBaseChange {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Prop
    extends IsFlatFamily f F where
  /-- `Rf_*ℱ` is pseudo-coherent. -/
  isPseudoCoherent : RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) (totalDirectImage f F)
  /-- `β_i` is the derived-fibre Betti function of `Rf_*ℱ`. -/
  fibreBetti_eq : ∀ i : ℤ, fibreBetti f F i =
    DerivedFibreBetti.derivedFiberBetti S (totalDirectImage f F) isPseudoCoherent i

/-- Compatibility of the formation of `Rf_*ℱ` with a cartesian square: for a cartesian
square with vertical morphisms `f : X ⟶ S` and `f' : X' ⟶ S'` and horizontal morphisms
`g' : X' ⟶ X` and `g : S' ⟶ S`, the total direct image of the pullback of `ℱ` is the derived
pullback along `g` of the total direct image of `ℱ`. -/
public structure BaseChangeCompatible {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X) (F : X.Modules) : Prop where
  /-- The square is cartesian. -/
  isPullback : IsPullback g' f' f g
  /-- `Rf'_*(g')^*ℱ ≅ Lg^*Rf_*ℱ`. -/
  nonempty_iso : Nonempty (totalDirectImage f' ((Scheme.Modules.pullback g').obj F) ≅
    (derivedPullback g.toLRSHom.toShHom).obj (totalDirectImage f F))

/-! ### The derived-fibre Betti function of isomorphic objects -/

/-- Isomorphic objects of `D(𝒪_X)` have the same derived-fibre Betti functions. -/
public theorem derivedFiberBetti_eq_of_iso (X : Scheme.{u})
    {E E' : DerivedCategory X.Modules}
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE' : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E')
    (e : E ≅ E') (i : ℤ) :
    DerivedFibreBetti.derivedFiberBetti X E hE i =
      DerivedFibreBetti.derivedFiberBetti X E' hE' i := by
  funext x
  exact ((moduleSpecΓFunctor (R := X.residueField x)).mapIso
    ((DerivedCategory.homologyFunctor (Spec (X.residueField x)).Modules i).mapIso
      ((derivedPullback
        (X.fromSpecResidueField x).toLRSHom.toShHom).mapIso e))).toLinearEquiv.finrank_eq

/-! ### Part (1): base change -/

/-- The formation of `β_i` commutes with base change along one cartesian square, given the
cohomology-and-base-change data for both families and for the square. All of these data hold for
every family satisfying the hypotheses of [Stacks, Tag 0BDN], by [Stacks, Tag 0B91]; the statement
with no hypotheses beyond the source's is
`AlgebraicGeometry.FibreBetti.fibreBetti_baseChange_upperSemicontinuous_isLocallyConstructible`
in `StacksFrontier/AlgebraicGeometry/Perfect/FibreBettiNumbersCohomologyBaseChange.lean`. -/
public theorem fibreBetti_baseChange {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X) (F : X.Modules)
    (h : CohomologyAndBaseChange f F)
    (h' : CohomologyAndBaseChange f' ((Scheme.Modules.pullback g').obj F))
    (hbc : BaseChangeCompatible f g f' g' F) (i : ℤ) :
    fibreBetti f' ((Scheme.Modules.pullback g').obj F) i = fibreBetti f F i ∘ g.base := by
  obtain ⟨e⟩ := hbc.nonempty_iso
  rw [h'.fibreBetti_eq i, derivedFiberBetti_eq_of_iso S' h'.isPseudoCoherent
      (DerivedFibreBetti.isPseudoCoherent_derivedPullback g _ h.isPseudoCoherent) e i,
    DerivedFibreBetti.derivedFiberBetti_derivedPullback g _ h.isPseudoCoherent i,
    h.fibreBetti_eq i]

/-! ### Part (2): upper semi-continuity -/

/-- The Betti-number function `β_i` is upper semi-continuous, given cohomology-and-base-change data
for the family and upper semi-continuity of the derived-fibre Betti function of `Rf_*ℱ` restricted
to each affine open of `S`. This is the reduction of upper semi-continuity to an affine cover; the
statement with no hypotheses beyond those of [Stacks, Tag 0BDN] is
`AlgebraicGeometry.FibreBetti.fibreBetti_baseChange_upperSemicontinuous_isLocallyConstructible`
in `StacksFrontier/AlgebraicGeometry/Perfect/FibreBettiNumbersCohomologyBaseChange.lean`. -/
public theorem upperSemicontinuous_fibreBetti {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (h : CohomologyAndBaseChange f F) (i : ℤ)
    (hloc : ∀ U : S.affineOpens, UpperSemicontinuous
      (DerivedFibreBetti.derivedFiberBetti U.1.toScheme
        ((derivedPullback U.1.ι.toLRSHom.toShHom).obj (totalDirectImage f F))
        (DerivedFibreBetti.isPseudoCoherent_derivedPullback U.1.ι (totalDirectImage f F)
          h.isPseudoCoherent) i)) :
    UpperSemicontinuous (fibreBetti f F i) := by
  rw [h.fibreBetti_eq i]
  refine DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti_of_openImmersions S
    (totalDirectImage f F) h.isPseudoCoherent i fun s => ?_
  obtain ⟨U, hsU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top S).ge (Set.mem_univ s))
  exact ⟨U.1.toScheme, U.1.ι, inferInstance, ⟨s, hsU⟩, rfl, hloc U⟩

end AlgebraicGeometry.FibreBetti

end
