module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback on `H²_ét(-, μ_n)` of a curve is multiplication by the degree

Let `k` be an algebraically closed field, let `π : X ⟶ Y` be a nonconstant morphism of smooth
proper curves over `k`, and let `n ≥ 1` be invertible in `k`.  Each of `H²_ét(Y, μ_n)` and
`H²_ét(X, μ_n)` is cyclic of order `n`, and in those coordinates the pullback `π^*` is
multiplication by the degree of `π`.

The argument is the source's.  Every class in `H²_ét(Y, μ_n)` is the Kummer coboundary of the
class in `H¹_ét(Y, 𝐆_m)` of a line bundle `L`, and the coordinate of that coboundary is the degree
of `L` modulo `n`.  Restriction along `π` commutes with the Kummer coboundary and carries the
class of `L` to the class of `π^*L`, so the coordinate of the restricted class is the degree of
`π^*L`, which is `deg(π)·deg(L)`.

## Main definitions

The elided prefix throughout is `Stacks.EtaleCohomology`.

* `rootsOfUnityPullbackMap`: the pullback `H^q_ét(Y, μ_n) ⟶ H^q_ét(X, μ_n)` along a morphism of
  schemes, namely restriction followed by the comparison `π^{-1} μ_{n,Y} ⟶ μ_{n,X}`.
* `kummerCoboundary`: the class in `Ext¹(𝐆_m, μ_n)` of the Kummer short exact sequence.
* `LineBundleClass`: the class in `H¹_ét(-, 𝐆_m)` of a line bundle, together with its
  compatibility with pullback.
* `RootsOfUnityH2Degree`: the identification `H²_ét(X, μ_n) ≃ ℤ/n` of a smooth proper curve,
  together with its normalisation by the degree of a line bundle.

## Main results

* `equiv_rootsOfUnityPullbackMap_eq_degreeOver_mul`: in the coordinates furnished by
  `RootsOfUnityH2Degree`, the pullback along a nonconstant morphism of smooth proper curves over
  an algebraically closed field is multiplication by the degree of that morphism.

## Implementation notes

Properness, dimension one and smoothness are carried separately rather than through a notion of
projective variety, because that is the shape in which the degree formula
`AlgebraicGeometry.curveDegree_pullback_eq_degreeOver_mul` and the degree
`AlgebraicGeometry.curveDegree` consume them.  Over a field this is no loss: a smooth proper curve
is projective.  A line bundle is taken to be a finite locally free module of constant rank one;
this is the same thing as an invertible module by clause (2) of [Stacks, Tag 0B8M], and
`AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree` identifies the two degrees.

Two inputs of the source are carried as hypotheses rather than discharged.  Neither of them
mentions `π`, two curves at once, or the degree of a morphism.

* `RootsOfUnityH2Degree` is the `q = 2` clause of [Stacks, Tag 03RQ], for a single curve.  The
  library has only the `q = 0` clause of that computation, as
  `AlgebraicGeometry.baseRootsToEtaleH0_bijective_of_isIntegral`, which carries
  [Stacks, Tag 03RR]; the `q = 2` clause rests on [Stacks, Tag 03P8] and [Stacks, Tag 03RM].  Of
  those, [Stacks, Tag 03RM] is proved, as
  `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_smoothCurve`;
  [Stacks, Tag 03P8] is not, for the small étale site that this file needs.
* `LineBundleClass` is the Picard half of [Stacks, Tag 03P8], for a single scheme and for an
  arbitrary morphism of schemes.  The library has the torsor half, as
  `Stacks.Kummer.multiplicativeTorsorIsoClassesEquivH1`, and nothing identifying `𝐆_m`-torsor
  classes on a small étale site with a Picard group.

The `HasExt` hypotheses are carried rather than discharged because the universe in which the
`Ext`-groups live is a parameter of `HasExt` and is not determined by the site, exactly as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage`.

## References

* [Stacks Project, Tag 0AMB](https://stacks.math.columbia.edu/tag/0AMB): the statement proved
  here.
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ): the cohomology of
  `μ_n` on a smooth projective curve.
* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ): the degree of a
  pullback.
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8): `H¹(X, 𝐆_m) = Pic(X)`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.Kummer

universe u v w

namespace Stacks.EtaleCohomology

/-- A natural number invertible in a field is invertible in the global functions of any scheme
over that field, its image under the structure morphism being a ring map. -/
theorem isUnit_natCast_sections (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {n : ℕ} (hn : IsUnit (n : k)) :
    IsUnit ((n : ℕ) : Γ(X, ⊤)) := by
  have h := hn.map ((Scheme.ΓSpecIso (.of k)).inv ≫ Scheme.Γ.map f.op).hom
  rwa [map_natCast] at h

/-- **The pullback `H^q_ét(Y, μ_n) ⟶ H^q_ét(X, μ_n)`** along a morphism of schemes `π : X ⟶ Y`:
restriction of cohomology classes along `π`, which lands in the cohomology of `π^{-1} μ_{n,Y}`,
followed by the comparison `π^{-1} μ_{n,Y} ⟶ μ_{n,X}`.

When `n` is invertible on `Y` that comparison is an isomorphism, by
`Stacks.Kummer.isIso_rootsOfUnityInverseImageComparison`, so this is the canonical identification
of the two groups of coefficients and not merely a choice of map between them. -/
def rootsOfUnityPullbackMap {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (q : ℕ) :
    Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) q →+
      Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) q :=
  (Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, v} π n) q).comp
    (etaleCohomologyRestrictionMap.{u, v, w} π (rootsOfUnitySheaf.{u, v} Y n) q)

@[simp]
theorem rootsOfUnityPullbackMap_apply {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (q : ℕ)
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) q) :
    rootsOfUnityPullbackMap.{u, v, w} π n q x =
      Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, v} π n) q
        (etaleCohomologyRestrictionMap.{u, v, w} π (rootsOfUnitySheaf.{u, v} Y n) q x) :=
  rfl

/-- **The Kummer coboundary of a scheme**, the class in `Ext¹(𝐆_m, μ_n)` of the Kummer short
exact sequence `μ_n ⟶ 𝐆_m ⟶ 𝐆_m` on the small étale site.  Composing with it is the coboundary
`H^q_ét(X, 𝐆_m) ⟶ H^{q+1}_ét(X, μ_n)` of the associated long exact sequence.

This names the two ends of the Kummer sequence, which the short complex refers to as its first
and third objects. -/
def kummerCoboundary (X : Scheme.{u}) (n : ℕ)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (hX : (kummerSequence.{u, v} X n).ShortExact) :
    Abelian.Ext (multiplicativeSheaf.{u, v} X) (rootsOfUnitySheaf.{u, v} X n) 1 :=
  hX.extClass

/-- **The class of a line bundle in `H¹_ét(-, 𝐆_m)`, compatibly with pullback.**  A line bundle is
a finite locally free module of constant rank one.

This is the Picard half of [Stacks, Tag 03P8], the identification of `H¹_ét(X, 𝐆_m)` with the
Picard group of `X`: the class map in one direction, and its naturality.  The library has only the
torsor half of that tag, `Stacks.Kummer.multiplicativeTorsorIsoClassesEquivH1`, which identifies
`H¹_ét(X, 𝐆_m)` with the group of isomorphism classes of `𝐆_m`-torsors on the small étale site of
`X`; nothing relates those torsor classes to invertible modules.  Carrying the data is therefore
not a weakening of 03P8 but the statement of what remains of it, and the bijectivity of the class
map — the rest of 03P8 — is deliberately not assumed, since it is not needed.

The naturality is stated for an arbitrary morphism of schemes, and in the form in which the
Kummer coboundary square `Stacks.Kummer.etaleCohomologyRestrictionMap_kummerExtClass` produces a
restricted class: restriction along `π` followed by the comparison `π^{-1} 𝐆_{m,Y} ⟶ 𝐆_{m,X}`. -/
structure LineBundleClass where
  /-- The class in `H¹_ét(X, 𝐆_m)` of a line bundle on `X`. -/
  classOf : ∀ (X : Scheme.{u})
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (L : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1],
    Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) 1
  /-- The class of a line bundle pulled back along a morphism of schemes is the restriction of
  its class, read in `H¹_ét(X, 𝐆_m)` through the comparison on `𝐆_m`. -/
  classOf_pullback : ∀ {X Y : Scheme.{u}} (π : X ⟶ Y)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (L : Y.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1],
    letI := isFiniteLocallyFreeOfRank_pullback π L 1
    Sheaf.H.map (multiplicativeInverseImageComparison.{u, v} π) 1
        (etaleCohomologyRestrictionMap.{u, v, w} π (multiplicativeSheaf.{u, v} Y) 1
          (classOf Y L)) =
      classOf X ((Scheme.Modules.pullback π).obj L)

/-- **The identification `H²_ét(X, μ_n) ≃ ℤ/n` of a smooth proper curve over an algebraically
closed field, with its normalisation.**  The identification is an isomorphism of abelian groups;
the normalisation says that the Kummer coboundary of the class of a line bundle is sent to the
degree of that line bundle modulo `n`, and that every class is such a coboundary.

This is the `q = 2` clause of [Stacks, Tag 03RQ], which computes `H^q_ét(X, μ_n)` for a smooth
projective curve `X` over an algebraically closed field and `n` invertible in that field.  The
library carries only the `q = 0` clause of that computation, as
`AlgebraicGeometry.baseRootsToEtaleH0_bijective_of_isIntegral`, which carries
[Stacks, Tag 03RR].  The `q = 2` clause is the
statement that the Kummer coboundary makes `H²_ét(X, μ_n)` the quotient `Pic(X)/n·Pic(X)`, which
the degree identifies with `ℤ/n`; it waits on [Stacks, Tag 03P8], the identification of
`H¹_ét(X, 𝐆_m)` with `Pic(X)`, and on [Stacks, Tag 03RM], the vanishing of `H²_ét(X, 𝐆_m)`.  It
is therefore carried here as data, and no tag is attached to it: a hypothesis is not a proof.

The short exactness of the Kummer sequence is quantified over rather than derived from
invertibility of `n`, so that the witness produced by any lemma may be supplied; being a
proposition, it is unique.  The three fields concern the single curve `πX` only.  No field
mentions a morphism of curves, a second curve, or the degree of a morphism; the degrees appearing
are degrees of line bundles on `X`. -/
structure RootsOfUnityH2Degree (c : LineBundleClass.{u, v, w}) (k : Type u) [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (πX : X ⟶ Spec (.of k)) [IsCurve k πX] [IsProper πX]
    [Smooth πX] (n : ℕ)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] where
  /-- The second étale cohomology of `μ_n` is cyclic of order `n`. -/
  equiv : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 2 ≃+ ZMod n
  /-- The Kummer coboundary of the class of a line bundle has coordinate the degree of that line
  bundle modulo `n`. -/
  equiv_kummerExtClass : ∀ (hX : (kummerSequence.{u, v} X n).ShortExact) (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1],
    equiv ((c.classOf X L).comp (kummerCoboundary.{u, v, w} X n hX) rfl) =
      ((curveDegree k πX (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πX))) L 1 : ℤ) :
        ZMod n)
  /-- Every class in the second étale cohomology of `μ_n` is the Kummer coboundary of the class
  of a line bundle. -/
  exists_lineBundle : ∀ (hX : (kummerSequence.{u, v} X n).ShortExact)
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 2),
    ∃ (L : X.Modules) (_ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1),
      x = (c.classOf X L).comp (kummerCoboundary.{u, v, w} X n hX) rfl

/-- **[Stacks, Tag 0AMB].**  Let `k` be an algebraically closed field, let `π : X ⟶ Y` be a
nonconstant morphism of smooth proper curves over `k`, and let `n ≥ 1` be invertible in `k`.  In
the coordinates of `Stacks.EtaleCohomology.RootsOfUnityH2Degree`, which identify both
`H²_ét(Y, μ_n)` and `H²_ét(X, μ_n)` with `ℤ/n`, the pullback

`π^* : H²_ét(Y, μ_n) ⟶ H²_ét(X, μ_n)`

is multiplication by the degree of `π`, the degree `deg(X/Y) = [R(X) : R(Y)]` of the extension of
function fields ([Stacks, Tag 02NY]).

The proof is the source's.  A class in `H²_ét(Y, μ_n)` is the Kummer coboundary of the class of a
line bundle `L` on `Y`.  Restriction along `π` commutes with the Kummer coboundary, by
`Stacks.Kummer.etaleCohomologyRestrictionMap_kummerExtClass`, and carries the class of `L` to the
class of `π^*L`, so the coordinate of the restricted class is the degree of `π^*L`.  That degree
is `deg(X/Y)` times the degree of `L` by
`AlgebraicGeometry.curveDegree_pullback_eq_degreeOver_mul`, which is where nonconstancy of `π` is
used, and the degree of `L` is the coordinate of the original class. -/
@[stacks 0AMB "with two inputs carried as hypotheses, neither of them about the conclusion: \
`SX`/`SY`, the q = 2 clause of Stacks 03RQ with its normalisation, since the library has only \
the q = 0 clause and the q = 2 clause needs Stacks 03P8 and 03RM; and `c`, the class of a line \
bundle in `H¹_ét(-, 𝐆_m)` with its naturality, which is the Picard half of Stacks 03P8"]
theorem equiv_rootsOfUnityPullbackMap_eq_degreeOver_mul (c : LineBundleClass.{u, v, w})
    (k : Type u) [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (πX : X ⟶ Spec (.of k))
    (πY : Y ⟶ Spec (.of k)) [IsCurve k πX] [IsCurve k πY] [IsProper πX] [IsProper πY]
    [Smooth πX] [Smooth πY] (π : X ⟶ Y) (hπ : π ≫ πY = πX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, π.base x = y) {n : ℕ} (hn0 : n ≠ 0) (hnk : IsUnit (n : k))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (SX : RootsOfUnityH2Degree.{u, v, w} c k πX n)
    (SY : RootsOfUnityH2Degree.{u, v, w} c k πY n)
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) 2) :
    SX.equiv (rootsOfUnityPullbackMap.{u, v, w} π n 2 x) =
      ((@degreeOver X Y π _ _ (locallyOfFiniteType_of_isCurve_comp k πX πY π hπ)
          (isDominant_of_not_constant k πX πY π hnc) : ℕ) : ZMod n) * SY.equiv x := by
  have hnY : IsUnit ((n : ℕ) : Γ(Y, ⊤)) := isUnit_natCast_sections k πY hnk
  have hSY := kummerSequence_shortExact.{u, v} Y hn0 hnY
  have hSX := kummerSequence_shortExact.{u, v} X hn0 (isUnit_natCast_of_hom π hnY)
  obtain ⟨L, instL, rfl⟩ := SY.exists_lineBundle hSY x
  have hbox : Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, v} π n) 2
        (etaleCohomologyRestrictionMap.{u, v, w} π (rootsOfUnitySheaf.{u, v} Y n) 2
          ((c.classOf Y L).comp (kummerCoboundary.{u, v, w} Y n hSY) rfl)) =
      (Sheaf.H.map (multiplicativeInverseImageComparison.{u, v} π) 1
          (etaleCohomologyRestrictionMap.{u, v, w} π (multiplicativeSheaf.{u, v} Y) 1
            (c.classOf Y L))).comp (kummerCoboundary.{u, v, w} X n hSX) rfl :=
    etaleCohomologyRestrictionMap_kummerExtClass.{u, v, w} π hn0 hnY 1 2 rfl (c.classOf Y L)
  rw [rootsOfUnityPullbackMap_apply, hbox, c.classOf_pullback π L,
    SX.equiv_kummerExtClass, SY.equiv_kummerExtClass,
    curveDegree_pullback_eq_degreeOver_mul k πX πY π hπ hnc L 1]
  push_cast
  ring

end Stacks.EtaleCohomology

end
