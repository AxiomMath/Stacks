module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation

/-!
# The rank of a perfect complex presented by finite locally free modules

Let `Y` be a scheme and `P` a bounded complex of finite locally free `𝒪_Y`-modules whose `i`-th
term has constant rank `r i`.  The derived-fibre Euler characteristic of the class of `P` in
`D(𝒪_Y)` is the constant `∑ (-1)^i r i`.  Consequently, if a perfect object `E` of `D(𝒪_X)` has
constant rank `r₀` and its derived pullback along `f : Y ⟶ X` is represented by such a `P`, with
`Y` nonempty, then `∑ (-1)^i r i = r₀`.

## Main results

* `AlgebraicGeometry.DerivedFibreBetti.eq_of_finiteFree_iso`: on a nonempty scheme
  `𝒪^{⊕ a} ≅ 𝒪^{⊕ b}` forces `a = b`.
* `AlgebraicGeometry.DerivedFibreBetti.exists_free_iso_over_near_of_rank`: a finite locally free
  module of rank `r` is free of rank `r` near any point.
* `AlgebraicGeometry.DerivedFibreBetti.isPerfect_Q_of_bounded_finiteLocallyFree`: a bounded
  complex of finite locally free modules represents a perfect object.
* `AlgebraicGeometry.DerivedFibreBetti.isPseudoCoherent_Q_of_bounded_finiteLocallyFree`: hence a
  pseudo-coherent one, so that its derived-fibre Euler characteristic is defined.
* `AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_eq_of_bounded_finiteLocallyFreeOfRank`:
  the derived-fibre Euler characteristic of a bounded complex of finite locally free modules of
  constant ranks `r i` is `∑ (-1)^i r i`.
* `AlgebraicGeometry.DerivedFibreBetti.finsum_rank_eq_of_derivedPullback_iso`: the alternating
  sum of the ranks of a presenting complex of a derived pullback is the rank of the object.

## References

* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
* [Stacks Project, Tag 0FAF](https://stacks.math.columbia.edu/tag/0FAF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.DerivedFibreBetti

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **The rank of a finite free module on a nonempty scheme is determined.**  An isomorphism
`𝒪^{⊕ a} ≅ 𝒪^{⊕ b}` pulls back to the residue field `κ(x)` of a point to an isomorphism
`κ(x)^a ≅ κ(x)^b` of vector spaces. -/
public theorem eq_of_finiteFree_iso (X : Scheme.{u}) (x : X) {a b : ℕ}
    (e : StrictlyPerfect.finiteFree X.toRingedSpace a ≅
      StrictlyPerfect.finiteFree X.toRingedSpace b) :
    a = b := by
  let k := X.residueField x
  let f := (X.fromSpecResidueField x).toLRSHom.toShHom
  let e' : ModuleCat.of k (Fin a → k) ≅ ModuleCat.of k (Fin b → k) :=
    (fibreFiniteFreeIso f a).symm ≪≫
      (moduleSpecΓFunctor (R := k)).mapIso ((modulePullback f).mapIso e) ≪≫
        fibreFiniteFreeIso f b
  simpa using e'.toLinearEquiv.finrank_eq

/-- **A finite locally free module of rank `r` is free of rank `r` near any point**: the
point lies in a member of a covering carrying local free presentations, and there the basis is
indexed by a type in bijection with `Fin r`. -/
public theorem exists_free_iso_over_near_of_rank {X : RingedSpace.{u, u}}
    {M : StrictlyPerfect.OXMod.{u, u} X} {r : ℕ}
    (hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := StrictlyPerfect.structureSheafOfRings X) M r)
    (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty (M.over U ≅ _root_.SheafOfModules.free
        (R := (StrictlyPerfect.structureSheafOfRings X).over U) (ULift.{u} (Fin r))) := by
  obtain ⟨q, hq, hr⟩ := hM.exists_isFiniteLocallyFreeOfRankData
  have hxcover : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff X.carrier q.X).mp q.coversTop]
    trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxcover
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨q.X i, hxi, ⟨(asIso (q.generators i).π).symm ≪≫
    (_root_.SheafOfModules.freeFunctor
      (R := (StrictlyPerfect.structureSheafOfRings X).over (q.X i))).mapIso
      (Equiv.toIso ((hr i).some.trans Equiv.ulift.symm))⟩⟩

/-- Restricting a bounded complex of modules to an open subset gives a bounded complex. -/
private theorem finite_not_isZero_restrictComplex {X : RingedSpace.{u, u}}
    (P : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ)
    (hbounded : {i : ℤ | ¬ IsZero (P.X i)}.Finite) (V : Opens X.carrier) :
    {i : ℤ | ¬ IsZero ((RingedSpace.restrictComplex P V).X i)}.Finite :=
  hbounded.subset fun _ hj hz => hj (Functor.map_isZero (RingedSpace.restrictModules X V) hz)

/-- **A bounded complex of finite locally free modules represents a perfect object.**  Near
every point all its terms are free, so the complex restricted to such a neighbourhood is its
own bounded finite free model. -/
public theorem isPerfect_Q_of_bounded_finiteLocallyFree {X : RingedSpace.{u, u}}
    (P : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ)
    (hbounded : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hterms : ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := StrictlyPerfect.structureSheafOfRings X) (P.X i)) :
    RingedSpace.IsPerfect.{u, u + 1} (X := X) (DerivedCategory.Q.obj P) := by
  classical
  choose V hV hchart using fun x : X.carrier =>
    RingedSpace.exists_free_iso_over_of_bounded P hbounded hterms x
  refine RingedSpace.isPerfect_of_hasFiniteFreeRepresentation.{u, u + 1} (X := X)
    ⟨P, ⟨Iso.refl _⟩, X.carrier, V, ?_, fun x => ⟨RingedSpace.restrictComplex P (V x), ?_, ?_,
      𝟙 _, inferInstance⟩⟩
  · exact top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hV x⟩
  · exact finite_not_isZero_restrictComplex P hbounded (V x)
  · intro j
    obtain ⟨n, ⟨e⟩⟩ := hchart x j
    exact ⟨n, RingedSpace.nonempty_restrictModules_obj_iso_finiteFree (P.X j) (V x) n e⟩

/-- **A bounded complex of finite locally free modules on a scheme represents a pseudo-coherent
object**, being perfect. -/
public theorem isPseudoCoherent_Q_of_bounded_finiteLocallyFree (Y : Scheme.{u})
    (P : CochainComplex Y.Modules ℤ) (hbounded : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (hterms : ∀ i : ℤ, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := StrictlyPerfect.structureSheafOfRings Y.toRingedSpace) (P.X i)) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) (DerivedCategory.Q.obj P) :=
  isPseudoCoherent_of_isPerfect _ (isPerfect_Q_of_bounded_finiteLocallyFree P hbounded hterms)

/-- **The derived-fibre Euler characteristic of a bounded complex of finite locally free modules
of constant ranks.**  If the `i`-th term of the bounded complex `P` of `𝒪_Y`-modules is finite
locally free of rank `r i`, the derived-fibre Euler characteristic of its class is
`∑ (-1)^i r i` at every point.

Near `y` every term is free; comparing with a local free presentation of rank `r i` at `y`
identifies the rank of the `i`-th term there as `r i`; base change along the inclusion of that
neighbourhood (Tag 0BDI) and the computation for bounded complexes of finite free modules
conclude. -/
public theorem chiDerivedFibre_eq_of_bounded_finiteLocallyFreeOfRank (Y : Scheme.{u})
    (P : CochainComplex Y.Modules ℤ) (hbounded : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (r : ℤ → ℕ) (hrank : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X i) (r i))
    (hpc : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) (DerivedCategory.Q.obj P))
    (y : Y) :
    chiDerivedFibre Y (DerivedCategory.Q.obj P) hpc y =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (r i : ℤ) := by
  classical
  have hlf (j : ℤ) : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := StrictlyPerfect.structureSheafOfRings Y.toRingedSpace) (P.X j) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (P.X j) (r j) (hM := hrank j)
  obtain ⟨V₀, hyV, hchart⟩ :=
    RingedSpace.exists_free_iso_over_of_bounded (X := Y.toRingedSpace) P hbounded hlf y
  set V : Y.Opens := V₀
  have hterm (j : ℤ) : Nonempty ((RingedSpace.restrictComplex P V).X j ≅
      StrictlyPerfect.finiteFree V.toScheme.toRingedSpace (r j)) := by
    obtain ⟨n, ⟨eV⟩⟩ := hchart j
    obtain ⟨U, hyU, ⟨eU⟩⟩ := exists_free_iso_over_near_of_rank (hrank j) y
    obtain ⟨eW⟩ := RingedSpace.nonempty_free_iso_over_of_le (P.X j)
      (inf_le_left : V ⊓ U ≤ V) n eV
    obtain ⟨eW'⟩ := RingedSpace.nonempty_free_iso_over_of_le (P.X j)
      (inf_le_right : V ⊓ U ≤ U) (r j) eU
    obtain ⟨fn⟩ := RingedSpace.nonempty_restrictModules_obj_iso_finiteFree (P.X j) (V ⊓ U) n eW
    obtain ⟨fr⟩ :=
      RingedSpace.nonempty_restrictModules_obj_iso_finiteFree (P.X j) (V ⊓ U) (r j) eW'
    obtain rfl : n = r j :=
      eq_of_finiteFree_iso (Scheme.Opens.toScheme (X := Y) (V ⊓ U)) ⟨y, hyV, hyU⟩ (fn.symm ≪≫ fr)
    exact RingedSpace.nonempty_restrictModules_obj_iso_finiteFree (P.X j) V _ eV
  let eModel : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      V.ι.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (RingedSpace.restrictComplex P V) :=
    derivedPullbackOpenQIso (X := Y.toRingedSpace) V P
  have hpcV : RingedSpace.IsPseudoCoherent (X := V.toScheme.toRingedSpace)
      (DerivedCategory.Q.obj (RingedSpace.restrictComplex P V)) :=
    (isPseudoCoherent_derivedPullback V.ι (DerivedCategory.Q.obj P) hpc).of_iso eModel
  calc chiDerivedFibre Y (DerivedCategory.Q.obj P) hpc y
      = chiDerivedFibre V.toScheme
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            V.ι.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P))
          (isPseudoCoherent_derivedPullback V.ι _ hpc) ⟨y, hyV⟩ :=
        (congrFun (chiDerivedFibre_derivedPullback V.ι (DerivedCategory.Q.obj P) hpc)
          ⟨y, hyV⟩).symm
    _ = chiDerivedFibre V.toScheme _ hpcV ⟨y, hyV⟩ :=
        congrFun (chiDerivedFibre_congr V.toScheme _ hpcV eModel) ⟨y, hyV⟩
    _ = ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (r i : ℤ) :=
        chiDerivedFibre_eq_of_bounded_finiteFree V.toScheme _
          (finite_not_isZero_restrictComplex (X := Y.toRingedSpace) P hbounded V) r hterm hpcV
          ⟨y, hyV⟩

/-- **The rank of a perfect object read off a presenting complex.**  Let `E` be a
pseudo-coherent object of `D(𝒪_X)` whose derived-fibre Euler characteristic is the constant
`r₀`, and let `f : Y ⟶ X` be a morphism from a nonempty scheme such that `Lf^* E` is represented
by a bounded complex `P` whose `i`-th term is finite locally free of rank `r i`.  Then
`∑ (-1)^i r i = r₀`.

At a point `y` of `Y` the Euler characteristic of `Lf^* E` is `r₀` by base change (Tag 0BDI),
and it is `∑ (-1)^i r i` by the computation for `P`. -/
public theorem finsum_rank_eq_of_derivedPullback_iso {X Y : Scheme.{u}} [Nonempty Y]
    (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (r₀ : ℤ)
    (hconst : ∀ x : X, chiDerivedFibre X E hE x = r₀) (f : Y ⟶ X)
    (P : CochainComplex Y.Modules ℤ) (hbounded : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (r : ℤ → ℕ) (hrank : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X i) (r i))
    (e : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f.toLRSHom.toShHom).obj E ≅ DerivedCategory.Q.obj P) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (r i : ℤ) = r₀ := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  have hpcP : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) (DerivedCategory.Q.obj P) :=
    (isPseudoCoherent_derivedPullback f E hE).of_iso e
  refine (chiDerivedFibre_eq_of_bounded_finiteLocallyFreeOfRank Y P hbounded r hrank hpcP
    y).symm.trans ?_
  refine (congrFun (chiDerivedFibre_congr Y (isPseudoCoherent_derivedPullback f E hE) hpcP e)
    y).symm.trans ?_
  exact (congrFun (chiDerivedFibre_derivedPullback f E hE) y).trans (hconst (f.base y))

example (Y : Scheme.{u}) (P : CochainComplex Y.Modules ℤ)
    (hbounded : {i : ℤ | ¬ IsZero (P.X i)}.Finite) (r : ℤ → ℕ) (hrank : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X i) (r i))
    (y : Y) :
    chiDerivedFibre Y (DerivedCategory.Q.obj P) (isPseudoCoherent_Q_of_bounded_finiteLocallyFree
      Y P hbounded fun i => SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (P.X i)
        (r i) (hM := hrank i)) y = ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (r i : ℤ) :=
  chiDerivedFibre_eq_of_bounded_finiteLocallyFreeOfRank Y P hbounded r hrank _ y

end AlgebraicGeometry.DerivedFibreBetti

end
