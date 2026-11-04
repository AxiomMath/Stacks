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
constructible.

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
* `AlgebraicGeometry.FibreBetti.fibreBetti_baseChange` is part (1): the formation of `β_i`
  commutes with arbitrary base change.
* `AlgebraicGeometry.FibreBetti.upperSemicontinuous_fibreBetti` is part (2): `β_i` is upper
  semi-continuous, given upper semi-continuity of the derived-fibre Betti function of `Rf_*ℱ` on
  each affine open of `S`.

## References

* [Stacks Project, Tag 0BDN](https://stacks.math.columbia.edu/tag/0BDN)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 054C](https://stacks.math.columbia.edu/tag/054C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open scoped Set.Notation

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

/-- The formation of `β_i` commutes with arbitrary base change: for a cartesian square whose
right-hand vertical morphism is `f : X ⟶ S` and whose base is changed along an arbitrary
`g : S' ⟶ S`, the `i`-th Betti-number function of the family `(f', (g')^*ℱ)` is the pullback
along `g` of the `i`-th Betti-number function of `(f, ℱ)`. -/
@[stacks 0BDN "part (1): formation of the Betti functions beta_i of the fibres commutes with \
arbitrary base change. The function beta_i is fibreBetti, dim over kappa(s) of H^i of the \
pullback of F to the scheme-theoretic fibre X_s, and all four hypotheses of the source are \
fields of IsFlatFamily, which CohomologyAndBaseChange extends. WHAT IS ASSUMED rather than \
proved: the source's cohomology-and-base-change step, carried as the fields isPseudoCoherent \
and fibreBetti_eq of CohomologyAndBaseChange (that Rf_*F is pseudo-coherent and that beta_i is \
its derived-fibre Betti function) and as BaseChangeCompatible (that the formation of Rf_*F \
commutes with the cartesian square). Both are consequences of Stacks 0B91, of which this \
library carries ONLY the base-change half of the conclusion and that half in the tensor form of \
the source's own reduction, namely \
AlgebraicGeometry.ProperFlatBaseChange.isIso_tensorFlatBaseChangeMap_module in \
StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatPushforwardBaseChange.lean line 334, tagged at \
line 309: invertibility of tensorFlatBaseChangeMap at F in degree zero, hence for \
Rf_*(O_X tensor^L F) and not for Rf_*F, with the perfection half absent from the library \
altogether. WHAT IS PROVED here: the transport of the conclusion across those identifications, \
using derivedFiberBetti_eq_of_iso and part (1) of Stacks 0BDI, \
AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti_derivedPullback"]
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

/-- The Betti-number function `β_i` is upper semi-continuous, provided that for every affine
open `U` of `S` the derived-fibre Betti function of the restriction of `Rf_*ℱ` to `U` is upper
semi-continuous. -/
@[stacks 0BDN "part (2): the Betti functions beta_i of the fibres are upper semi-continuous, for \
beta_i the function fibreBetti and all four hypotheses of the source present as fields of \
IsFlatFamily. WHAT IS ASSUMED rather than proved: first the cohomology-and-base-change step, as \
the fields isPseudoCoherent and fibreBetti_eq of CohomologyAndBaseChange, which is the half of \
Stacks 0B91 this library does not carry (see the attribute on fibreBetti_baseChange and \
AlgebraicGeometry.ProperFlatBaseChange.isIso_tensorFlatBaseChangeMap_module in \
StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatPushforwardBaseChange.lean line 334, tagged at \
line 309); and second part (2) of Stacks 0BDI for Rf_*F, which is NOT in the library -- the only \
@[stacks 0BDI] attributes in the library are on its base-change half -- and which is assumed \
here in its LOCAL form only, as upper semi-continuity of the derived-fibre Betti function of \
the derived pullback of Rf_*F to each affine open of S. The affine case of that input is \
available for an object of D(R) on PrimeSpectrum R as \
StacksDraft.Perfect.upperSemicontinuous_fibreBetti_of_isPseudoCoherent in \
StacksFrontier/Homology/Perfect/BettiSemicontinuity.lean line 395, but no bridge from it to \
AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti on Spec R exists in the library. WHAT IS \
PROVED here: the passage from that local form to upper semi-continuity on S, by the \
reduction \
AlgebraicGeometry.DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti_of_openImmersions \
applied to the cover of S by its affine opens, and the transport of the conclusion to beta_i"]
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
