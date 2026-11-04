module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFreeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The étale free loci under an inverse image

Let `p : X' ⟶ X` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be an `𝒪_X`-module.  The loci of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocus.lean` — the points of `|X|` at which `F`
becomes free of rank one on an étale neighbourhood — satisfies

```
|p|⁻¹(W₁(F)) ⊆ W₁(p^* F),
```

which is the inclusion of the base-change clause of Stacks 0CZT that holds for an *arbitrary*
morphism `p`, with no flatness, finite presentation or openness anywhere.

## Main results

* `AlgebraicGeometry.Space.preimage_etaleRankOneFreeLocus_subset`: the inclusion for the
  rank-one locus.
* `AlgebraicGeometry.Space.preimage_etaleFreeLocus_subset`: the inclusion for the locus of
  Stacks 0CZT itself, at an arbitrary rank.
* `AlgebraicGeometry.Space.isFreeModule_of_iso_free` and
  `AlgebraicGeometry.Space.exists_iso_free_of_isFreeModule`: freeness in the sense of
  `AlgebraicGeometry.Space.IsFreeModule` is being isomorphic to a free module on some index
  type.

## Implementation notes

The étale neighbourhood over a point of `|X'|` is the fibre product `V ×_X X'` of the given
trivializing neighbourhood `a : V ⟶ X` with `p`, which is étale over `X'` by Stacks 03FU
(`AlgebraicGeometry.Space.isEtale_of_isPullback`) and carries a point over the given one by
Stacks 03H4 (`AlgebraicGeometry.Space.exists_points_of_isPullback`, the surjectivity of the
comparison map of a cartesian square onto the fibre product of the point sets — which is
exactly what is needed, the point of `|V ×_X X'|` being produced from the compatible pair).

The trivialization transports because the inverse image of Stacks 03LU is pseudofunctorial and
carries the structure sheaf to the structure sheaf: the two legs of the cartesian square give
two factorizations of one inverse image, compared by
`AlgebraicGeometry.Space.modulePullbackCompIso` on each side, and
`AlgebraicGeometry.Space.modulePullbackUnitIso` turns the inverse image of `𝒪_V` into
`𝒪_{V ×_X X'}`.

**This is the easy half of the base-change clause of Stacks 0CZT**, and only the easy half.  The
clause asserts the *equality* `W(F_{T'}) = |X_g|⁻¹(W(F))`; the opposite inclusion is a descent
statement, which the source obtains from clause (4) of Stacks 0CZS together with a transport of
clause (1) across the base change.  That equality is proved, as
`AlgebraicGeometry.Space.etaleFreeLocus_modulePullback_eq` of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocusBaseChange.lean`, which consumes the
inclusions below and is downstream of this module.  No attribute for Tag 0CZT is carried here: a
hypothesis-free inclusion is not the clause, and the two carriers of that tag are
`AlgebraicGeometry.Space.isOpen_etaleFreeLocus` for openness and that equality for the base
change.

The statements are for an arbitrary morphism of algebraic spaces rather than for the relative map
`X_{T'} ⟶ X_T` of a base change, which is the shape the second part of the proof of Stacks 0D03
uses it in: nothing in the argument is about test schemes, and the relative map is an instance.

## References

* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- In a cartesian square over `a` and `p`, with `a` étale and `x'` above a point of `V`, the
projection to `X'` is étale and has `x'` in the image on points. -/
private theorem isEtale_and_mem_range_of_isPullback {X X' V W : AlgebraicSpaces B S hS}
    {a : V ⟶ X} {p : X' ⟶ X} {fst : W ⟶ V} {snd : W ⟶ X'} (sq : IsPullback fst snd a p)
    (hae : IsEtale B S hS a.hom) {v : points B S hS V.1} {x' : points B S hS X'.1}
    (hv : pointsMap B S hS V.1 a.hom v = pointsMap B S hS X'.1 p.hom x') :
    IsEtale B S hS snd.hom ∧ x' ∈ Set.range (pointsMap B S hS W.1 snd.hom) := by
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS sq) v x' hv
  exact ⟨isEtale_of_isPullback B S hS _ _ a p sq hae, w, hw⟩

/-- **A rank-one trivialization pulls back to a rank-one trivialization.**  For a morphism
`p : X' ⟶ X` of algebraic spaces and an étale `a : V ⟶ X` along which the inverse image of `F`
is isomorphic to `𝒪_V`, the inverse image of `p^* F` along the projection
`V ×_X X' ⟶ X'` is isomorphic to `𝒪_{V ×_X X'}`.

The square is cartesian (Stacks 02X2), so the two composites `V ×_X X' ⟶ X` agree; the inverse
image along each is compared with the two-step inverse image by
`AlgebraicGeometry.Space.modulePullbackCompIso`, and the inverse image of the structure sheaf is
the structure sheaf by `AlgebraicGeometry.Space.modulePullbackUnitIso`. -/
def modulePullbackFiberProductUnitIso {X X' V : AlgebraicSpaces B S hS} (p : X' ⟶ X) (a : V ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (e : (modulePullback B S hS a).obj F ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O)) :
    (modulePullback B S hS
          (ObjectProperty.homMk (pullback.snd a.hom p.hom) :
            AlgebraicSpaces.fiberProduct B S hS a p ⟶ X')).obj
        ((modulePullback B S hS p).obj F) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (AlgebraicSpaces.fiberProduct B S hS a p).1
        (AlgebraicSpaces.fiberProduct B S hS a p).2).O) :=
  (modulePullbackCompIso B S hS
      (ObjectProperty.homMk (pullback.snd a.hom p.hom) :
        AlgebraicSpaces.fiberProduct B S hS a p ⟶ X') p).app F ≪≫
    eqToIso (congrArg (fun k => (modulePullback B S hS k).obj F)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS a p).w.symm) ≪≫
    ((modulePullbackCompIso B S hS
      (ObjectProperty.homMk (pullback.fst a.hom p.hom) :
        AlgebraicSpaces.fiberProduct B S hS a p ⟶ V) a).app F).symm ≪≫
    (modulePullback B S hS
      (ObjectProperty.homMk (pullback.fst a.hom p.hom) :
        AlgebraicSpaces.fiberProduct B S hS a p ⟶ V)).mapIso e ≪≫
    modulePullbackUnitIso B S hS
      (ObjectProperty.homMk (pullback.fst a.hom p.hom) :
        AlgebraicSpaces.fiberProduct B S hS a p ⟶ V)

/-- **The rank-one étale free locus of an inverse image contains the inverse image of the
rank-one étale free locus.**  For a morphism `p : X' ⟶ X` of algebraic spaces and an
`𝒪_X`-module `F`, a point of `|X'|` above a point at which `F` is free of rank one on an étale
neighbourhood is a point at which `p^* F` is free of rank one on an étale neighbourhood.

This is the inclusion `|p|⁻¹(W₁(F)) ⊆ W₁(p^* F)`, the easy half of the base-change clause of
Stacks 0CZT at the rank-one locus, and it holds for an arbitrary `p`.  The neighbourhood is the
fibre product `V ×_X X'` of the given one with `p`; it is étale over `X'` by Stacks 03FU, it
carries a point above the given one by Stacks 03H4, and the trivialization transports by
`AlgebraicGeometry.Space.modulePullbackFiberProductUnitIso`. -/
theorem preimage_etaleRankOneFreeLocus_subset {X X' : AlgebraicSpaces B S hS} (p : X' ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    pointsMap B S hS X'.1 p.hom ⁻¹' etaleRankOneFreeLocus B S hS F ⊆
      etaleRankOneFreeLocus B S hS ((modulePullback B S hS p).obj F) := by
  rintro x' ⟨V, a, hae, ⟨v, hv⟩, ⟨e⟩⟩
  obtain ⟨het, hw⟩ := isEtale_and_mem_range_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS a p) hae hv
  exact ⟨AlgebraicSpaces.fiberProduct B S hS a p, _, het, hw,
    ⟨modulePullbackFiberProductUnitIso B S hS p a F e⟩⟩

/-! ### The same at an arbitrary rank -/

/-- **A module isomorphic to a free module is free.**  This is
`AlgebraicGeometry.Space.isFreeModule_of_iso_unit` at an arbitrary index type: the cofan of the
free module is a coproduct diagram, so transporting it along the isomorphism exhibits `M` as a
coproduct of copies of the structure sheaf. -/
theorem isFreeModule_of_iso_free (V : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS V.1 V.2) (I : Type u)
    (e : SheafOfModules.free
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O) I ≅ M) :
    IsFreeModule B S hS V M :=
  ⟨I, (Stacks.SheafOfModules.exists_isColimitCofan_of_iso_free e).choose,
    (Stacks.SheafOfModules.exists_isColimitCofan_of_iso_free e).choose_spec⟩

/-- **A free module is isomorphic to a free module on its index type.**  The converse of
`AlgebraicGeometry.Space.isFreeModule_of_iso_free`, obtained from the colimiting cofan that
`AlgebraicGeometry.Space.IsFreeModule` provides. -/
theorem exists_iso_free_of_isFreeModule (V : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS V.1 V.2) (hM : IsFreeModule B S hS V M) :
    ∃ I : Type u, Nonempty (M ≅ SheafOfModules.free
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O) I) := by
  obtain ⟨I, ι, hι⟩ := hM
  exact ⟨I, ⟨(Stacks.SheafOfModules.nonempty_iso_free_of_exists_isColimitCofan
    (I := I) ⟨ι, hι⟩).some.symm⟩⟩

/-- **A trivialization at an arbitrary rank pulls back to one of the same rank.**  This is
`AlgebraicGeometry.Space.modulePullbackFiberProductUnitIso` with `SheafOfModules.free I` in place
of the unit module; the comparison chain is the same, and the last step is
`AlgebraicGeometry.Space.modulePullbackFreeIso` — the inverse image of Stacks 03LU preserves
coproducts, being a left adjoint — in place of
`AlgebraicGeometry.Space.modulePullbackUnitIso`. -/
def modulePullbackFiberProductFreeIso {X X' V : AlgebraicSpaces B S hS} (p : X' ⟶ X) (a : V ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) (I : Type u)
    (e : (modulePullback B S hS a).obj F ≅ SheafOfModules.free
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O) I) :
    (modulePullback B S hS
          (ObjectProperty.homMk (pullback.snd a.hom p.hom) :
            AlgebraicSpaces.fiberProduct B S hS a p ⟶ X')).obj
        ((modulePullback B S hS p).obj F) ≅
      SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (AlgebraicSpaces.fiberProduct B S hS a p).1
        (AlgebraicSpaces.fiberProduct B S hS a p).2).O) I :=
  (modulePullbackCompIso B S hS
      (ObjectProperty.homMk (pullback.snd a.hom p.hom) :
        AlgebraicSpaces.fiberProduct B S hS a p ⟶ X') p).app F ≪≫
    eqToIso (congrArg (fun k => (modulePullback B S hS k).obj F)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS a p).w.symm) ≪≫
    ((modulePullbackCompIso B S hS
      (ObjectProperty.homMk (pullback.fst a.hom p.hom) :
        AlgebraicSpaces.fiberProduct B S hS a p ⟶ V) a).app F).symm ≪≫
    (modulePullback B S hS
      (ObjectProperty.homMk (pullback.fst a.hom p.hom) :
        AlgebraicSpaces.fiberProduct B S hS a p ⟶ V)).mapIso e ≪≫
    (modulePullbackFreeIso B S hS
      (ObjectProperty.homMk (pullback.fst a.hom p.hom) :
        AlgebraicSpaces.fiberProduct B S hS a p ⟶ V) I).symm

/-- **The étale free locus of an inverse image contains the inverse image of the étale free
locus.**  This is `AlgebraicGeometry.Space.preimage_etaleRankOneFreeLocus_subset` at an arbitrary
rank: the inclusion `|p|⁻¹(W(F)) ⊆ W(p^* F)`, which is the easy half of the base-change clause of
Stacks 0CZT, for an arbitrary morphism `p` of algebraic spaces and with no hypothesis on `F`.

The neighbourhood is again the fibre product `V ×_X X'`, étale over `X'` by Stacks 03FU and
carrying a point above the given one by Stacks 03H4; the trivialization transports by
`AlgebraicGeometry.Space.modulePullbackFiberProductFreeIso`, the index type being unchanged
because the inverse image preserves coproducts. -/
theorem preimage_etaleFreeLocus_subset {X X' : AlgebraicSpaces B S hS} (p : X' ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    pointsMap B S hS X'.1 p.hom ⁻¹' etaleFreeLocus B S hS F ⊆
      etaleFreeLocus B S hS ((modulePullback B S hS p).obj F) := by
  rintro x' ⟨V, a, hae, ⟨v, hv⟩, hfree⟩
  obtain ⟨I, ⟨e⟩⟩ := exists_iso_free_of_isFreeModule B S hS V _ hfree
  obtain ⟨het, hw⟩ := isEtale_and_mem_range_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS a p) hae hv
  exact ⟨AlgebraicSpaces.fiberProduct B S hS a p, _, het, hw,
    isFreeModule_of_iso_free B S hS _ _ I
      (modulePullbackFiberProductFreeIso B S hS p a F I e).symm⟩

end AlgebraicGeometry.Space

end
