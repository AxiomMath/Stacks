module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Flatness.Impurity.HenselizationDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Purity along a fibre for a morphism which is only locally of finite type

The notions of impurity and of purity along a fibre are stated for a morphism of finite type,
that is, one which is locally of finite type *and* quasi-compact. Dropping quasi-compactness,
the four conditions which the source shows to be equivalent in the finite type case still make
sense:

1. there is no impurity over an elementary étale neighbourhood of the chosen point;
2. there is no impurity whose test family is quasi-finite at its distinguished point;
3. there is no impurity whose test family is the spectrum of a henselization `S^h` of the local
   ring of the base at the chosen point;
4. every point of the relative assassin `Ass_{X^h/S^h}(ℱ^h)` specializes to a point of the
   fibre of `X^h` over the closed point of `S^h`.

The source records that (1) and (2) remain equivalent, that (3) and (4) remain equivalent, and
that it does not know whether (1) and (3) are equivalent. The equivalence of (3) and (4) is
proved here. The equivalence of (1) and (2) is not: its substantial half is Tag 05J0, whose
proof — which indeed never uses quasi-compactness — is not available in this library;
only the easy half is proved below.

## Main definitions

* `AlgebraicGeometry.ImpurityData` is an impurity diagram for a morphism which is not assumed
  quasi-compact, so that it needs no `AlgebraicGeometry.PrePureSituation` to be formed, and
  `AlgebraicGeometry.ImpurityData.IsImpurity` says that it defines an impurity.
* `AlgebraicGeometry.NoElementaryEtaleImpurity`,
  `AlgebraicGeometry.NoQuasiFiniteImpurity`, `AlgebraicGeometry.NoHenselianImpurity` and
  `AlgebraicGeometry.RelativeAssassinSpecializesIntoClosedFibre` are conditions (1), (2), (3)
  and (4) above.

## Main results

* `AlgebraicGeometry.impurityDataEquiv` and
  `AlgebraicGeometry.isImpurity_impurityDataEquiv` identify the unbundled impurity data of a
  pre-pure situation with its impurity diagrams, and the two impurity predicates; so
  `AlgebraicGeometry.isPureAlong_iff_noElementaryEtaleImpurity` identifies condition (1) with
  purity along the fibre whenever the morphism happens to be quasi-compact.
* `AlgebraicGeometry.eq_closedPoint_of_specHenselizationToBase_apply_eq`: a point of the
  spectrum of a henselization lying over the chosen point of the base is its closed point.
* `AlgebraicGeometry.noHenselianImpurity_iff_relativeAssassinSpecializesIntoClosedFibre` is the
  equivalence of conditions (3) and (4).
* `AlgebraicGeometry.noElementaryEtaleImpurity_of_noQuasiFiniteImpurity` is the easy half of the
  equivalence of conditions (1) and (2).

## Implementation notes

`AlgebraicGeometry.ImpurityData` repeats the fields of `AlgebraicGeometry.ImpurityDiagram`
because the latter is indexed by an `AlgebraicGeometry.PrePureSituation`, which carries the
quasi-compactness of the morphism as a field and so cannot be formed here. The two are the same
notion, which is what `AlgebraicGeometry.impurityDataEquiv` records; the standing hypotheses on
the morphism and the module are carried by the statements below instead of by a structure.

Conditions (3) and (4) are stated for an arbitrary model `(T, g)` of `S^h → S`, that is, for a
scheme over `S` presented as isomorphic over `S` to the spectrum of a henselization, and for an
arbitrary cartesian square presenting `X^h`; this is the convention of
`AlgebraicGeometry.ImpurityDiagram`, whose base change is an arbitrary cartesian square rather
than a chosen pullback. The closed point of such a model is the image of the closed point of the
henselization, and the fibre of `X^h` over it is the fibre `X_s` of the source, the residue field
of the closed point of `S^h` being that of `s`.

## References

* [Stacks Project, Tag 05J5](https://stacks.math.columbia.edu/tag/05J5)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-! ### Impurities without a quasi-compactness hypothesis -/

/-- An impurity diagram for a morphism `f : X ⟶ S` and a point `s` of `S`, with no
quasi-compactness hypothesis on `f`: a base change of `f`, a specialization over `s`, and a
point of the base change above the generalization. These are the data of
`AlgebraicGeometry.ImpurityDiagram`, which is indexed by an
`AlgebraicGeometry.PrePureSituation` and hence unavailable when `f` is not quasi-compact. -/
structure ImpurityData (f : X ⟶ S) (s : S) where
  /-- The scheme used to change the base. -/
  T : Scheme.{u}
  /-- The base-change morphism. -/
  g : T ⟶ S
  /-- The point specializing to `t`. -/
  t' : T
  /-- The point above the distinguished point `s`. -/
  t : T
  /-- The specified specialization `t' ⤳ t`. -/
  specializes : t' ⤳ t
  /-- The point `t` maps to the distinguished point of the base. -/
  mapsToChosenPoint : g.base t = s
  /-- The base change of `X` along `g`. -/
  X_T : Scheme.{u}
  /-- The projection of the base change to `X`. -/
  toX : X_T ⟶ X
  /-- The projection of the base change to `T`. -/
  toT : X_T ⟶ T
  /-- The displayed square is cartesian. -/
  isPullback : IsPullback toX toT f g
  /-- The chosen point of the base change. -/
  xi : X_T
  /-- The chosen point lies above `t'`. -/
  xi_liesOver : toT.base xi = t'

namespace ImpurityData

variable {f : X ⟶ S} {s : S}

/-- The pullback `ℱ_T` of a module `ℱ` on `X` to the base change `X_T`. -/
noncomputable abbrev pulledBack (D : ImpurityData f s) (F : X.Modules) : D.X_T.Modules :=
  (Scheme.Modules.pullback D.toX).obj F

/-- An impurity datum defines an *impurity of `ℱ` above `s`* when its chosen point belongs to
the relative assassin of the pulled-back module and its closure is disjoint from the fibre over
the specialized point. -/
abbrev IsImpurity (D : ImpurityData f s) (F : X.Modules) : Prop :=
  D.xi ∈ Stacks.Divisors.relativeAssassin D.toT (D.pulledBack F) ∧
    closure {D.xi} ∩ Set.range (D.toT.fiberι D.t) = ∅

/-- An impurity datum is an impurity exactly when its chosen point specializes to no point
lying over its distinguished point. -/
theorem isImpurity_iff (D : ImpurityData f s) (F : X.Modules) :
    D.IsImpurity F ↔
      D.xi ∈ Stacks.Divisors.relativeAssassin D.toT (D.pulledBack F) ∧
        ∀ y : D.X_T, D.toT.base y = D.t → ¬ D.xi ⤳ y := by
  refine and_congr_right fun _ => ?_
  rw [Set.eq_empty_iff_forall_notMem, D.toT.range_fiberι]
  refine ⟨fun h y hy hsp => h y ⟨specializes_iff_mem_closure.mp hsp, hy⟩, fun h y hy => ?_⟩
  exact h y hy.2 (specializes_iff_mem_closure.mpr hy.1)

end ImpurityData

/-- The impurity data of the morphism, the module and the point of a pre-pure situation are
exactly its impurity diagrams. -/
def impurityDataEquiv (P : PrePureSituation.{u}) : ImpurityData P.f P.s ≃ ImpurityDiagram P where
  toFun D :=
    { T := D.T, g := D.g, t' := D.t', t := D.t, specializes := D.specializes
      mapsToChosenPoint := D.mapsToChosenPoint, X_T := D.X_T, toX := D.toX, toT := D.toT
      isPullback := D.isPullback, xi := D.xi, xi_liesOver := D.xi_liesOver }
  invFun D :=
    { T := D.T, g := D.g, t' := D.t', t := D.t, specializes := D.specializes
      mapsToChosenPoint := D.mapsToChosenPoint, X_T := D.X_T, toX := D.toX, toT := D.toT
      isPullback := D.isPullback, xi := D.xi, xi_liesOver := D.xi_liesOver }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The two impurity predicates agree under `AlgebraicGeometry.impurityDataEquiv`. -/
theorem isImpurity_impurityDataEquiv (P : PrePureSituation.{u}) (D : ImpurityData P.f P.s) :
    IsImpurity P (impurityDataEquiv P D) ↔ D.IsImpurity P.F :=
  Iff.rfl

/-! ### The four conditions -/

/-- **Condition (1).** There is no impurity of `ℱ` above `s` over an elementary étale
neighbourhood of `s`. For a quasi-compact `f` this is purity along the fibre over `s`. -/
abbrev NoElementaryEtaleImpurity (f : X ⟶ S) (F : X.Modules) (s : S) : Prop :=
  ∀ (D : ImpurityData f s) (h : Etale D.g),
    EtaleNeighborhood.IsElementary
        ({ scheme := D.T
           point := D.t
           toBase := D.g
           etale_toBase := h
           map_point := D.mapsToChosenPoint } : EtaleNeighborhood S s) →
      ¬ D.IsImpurity F

/-- **Condition (2).** There is no impurity of `ℱ` above `s` whose test family is quasi-finite
at its distinguished point. -/
abbrev NoQuasiFiniteImpurity (f : X ⟶ S) (F : X.Modules) (s : S) : Prop :=
  ∀ D : ImpurityData f s, quasiFiniteAt D.g D.t → ¬ D.IsImpurity F

variable (f : X ⟶ S) (F : X.Modules) (s : S) (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
  [Algebra (S.presheaf.stalk s) Rh]

/-- **Condition (3).** There is no impurity of `ℱ` above `s` whose test family is a model of
`S^h → S`, for `S^h` the spectrum of a henselization of the local ring of `S` at `s`. -/
abbrev NoHenselianImpurity : Prop :=
  ∀ (D : ImpurityData f s) (e : D.T ≅ Spec (CommRingCat.of Rh)),
    D.g = e.hom ≫ specHenselizationToBase s Rh → ¬ D.IsImpurity F

/-- **Condition (4).** Every point of the relative assassin `Ass_{X^h/S^h}(ℱ^h)` specializes to
a point of the fibre of `X^h` over the closed point of `S^h`. -/
abbrev RelativeAssassinSpecializesIntoClosedFibre : Prop :=
  ∀ (T : Scheme.{u}) (g : T ⟶ S) (e : T ≅ Spec (CommRingCat.of Rh)),
    g = e.hom ≫ specHenselizationToBase s Rh →
      ∀ (X_T : Scheme.{u}) (toX : X_T ⟶ X) (toT : X_T ⟶ T), IsPullback toX toT f g →
        ∀ ξ ∈ Stacks.Divisors.relativeAssassin toT ((Scheme.Modules.pullback toX).obj F),
          ∃ y : X_T, toT.base y = e.inv.base (IsLocalRing.closedPoint Rh) ∧ ξ ⤳ y

/-! ### Condition (1) for a quasi-compact morphism -/

/-- For a quasi-compact morphism, condition (1) is purity along the fibre over `s`. -/
theorem isPureAlong_iff_noElementaryEtaleImpurity (P : PrePureSituation.{u}) :
    IsPureAlong P ↔ NoElementaryEtaleImpurity P.f P.F P.s :=
  ⟨fun h D hg hel => h (impurityDataEquiv P D) hg hel,
    fun h D hg hel => h ((impurityDataEquiv P).symm D) hg hel⟩

/-! ### The easy half of the equivalence of conditions (1) and (2) -/

/-- Condition (2) implies condition (1): an elementary étale neighbourhood is étale, hence
quasi-finite at its distinguished point.

This is one direction of the equivalence of conditions (1) and (2), and is unconditional. The
converse is Tag 05J0, whose proof does not use quasi-compactness but which is not available in
this library, so the equivalence itself is not claimed here. -/
@[stacks 05J5 "condition (2) implies condition (1)"]
theorem noElementaryEtaleImpurity_of_noQuasiFiniteImpurity {f : X ⟶ S} {F : X.Modules} {s : S}
    (h : NoQuasiFiniteImpurity f F s) : NoElementaryEtaleImpurity f F s :=
  fun D _ _ => h D ((forall_quasiFiniteAt_iff D.g).mpr (locallyQuasiFinite_of_etale D.g) D.t)

/-! ### Points of the spectrum of a henselization over the chosen point -/

variable [IsLocalRing.IsHenselization (S.presheaf.stalk s)
  (IsLocalRing.ResidueField (S.presheaf.stalk s)) Rh]

/-- The canonical morphism from the spectrum of a henselization of the local ring of `S` at `s`
carries the closed point to `s`. -/
theorem specHenselizationToBase_closedPoint :
    (specHenselizationToBase s Rh).base (IsLocalRing.closedPoint Rh) = s := by
  have : IsLocalHom (algebraMap (S.presheaf.stalk s) Rh) :=
    IsLocalRing.IsHenselization.isLocalHom (L := IsLocalRing.ResidueField (S.presheaf.stalk s))
  change (S.fromSpecStalk s).base
      ((Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh))).base
        (IsLocalRing.closedPoint Rh)) = s
  rw [Spec_closedPoint]
  exact Scheme.fromSpecStalk_closedPoint

/-- A point of the spectrum of a henselization of the local ring of `S` at `s` which lies over
`s` is its closed point: its image in the spectrum of the local ring is the closed point there,
because `Spec` of the local ring at `s` is injective over `S`, and the maximal ideal of the
henselization is extended from that of the local ring. -/
theorem eq_closedPoint_of_specHenselizationToBase_apply_eq
    (y : Spec (CommRingCat.of Rh)) (hy : (specHenselizationToBase s Rh).base y = s) :
    y = IsLocalRing.closedPoint Rh := by
  let R := S.presheaf.stalk s
  have hz' : (Spec.map (CommRingCat.ofHom (algebraMap R Rh))).base y =
      IsLocalRing.closedPoint R :=
    (S.fromSpecStalk s).isEmbedding.injective (hy.trans Scheme.fromSpecStalk_closedPoint.symm)
  have hmax : IsLocalRing.maximalIdeal Rh ≤ y.asIdeal := by
    rw [← IsLocalRing.IsHenselization.map_maximalIdeal (R := R)
      (L := IsLocalRing.ResidueField R) (Rh := Rh), Ideal.map_le_iff_le_comap]
    exact (congrArg PrimeSpectrum.asIdeal hz').ge
  exact PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal y.2.1) hmax)

/-! ### The equivalence of conditions (3) and (4) -/

/-- **Stacks Project, Tag 05J5.** For a morphism which is only locally of finite type,
conditions (3) and (4) are still equivalent: the impurities above `s` whose test family is a
model of `S^h → S` are exactly the points of `Ass_{X^h/S^h}(ℱ^h)` which fail to specialize into
the fibre of `X^h` over the closed point of `S^h`.

What makes this work is that the auxiliary data of such an impurity carry no information: its
distinguished point is forced to be the closed point of the model, because every point of
`S^h` over `s` is the closed point, and the specialization to it is automatic, because every
point of the spectrum of a local ring specializes to its closed point. -/
@[stacks 05J5 "conditions (3) and (4) are equivalent"]
theorem noHenselianImpurity_iff_relativeAssassinSpecializesIntoClosedFibre
    [LocallyOfFiniteType f] [F.IsFiniteType] [F.IsQuasicoherent] :
    NoHenselianImpurity f F s Rh ↔ RelativeAssassinSpecializesIntoClosedFibre f F s Rh := by
  constructor
  · intro h3 T g e hg X_T toX toT hp ξ hξ
    by_contra hcon
    have hhom : ∀ p : Spec (CommRingCat.of Rh), e.hom.base (e.inv.base p) = p := fun p => by
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
      rfl
    have hinv : ∀ q : T, e.inv.base (e.hom.base q) = q := fun q => by
      rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    refine h3 { T := T, g := g, t' := toT.base ξ
                t := e.inv.base (IsLocalRing.closedPoint Rh)
                specializes := ?_, mapsToChosenPoint := ?_
                X_T := X_T, toX := toX, toT := toT, isPullback := hp
                xi := ξ, xi_liesOver := rfl } e hg
      ((ImpurityData.isImpurity_iff _ F).mpr ⟨hξ, fun y hy hsp => hcon ⟨y, hy, hsp⟩⟩)
    · simpa only [hinv] using
        (IsLocalRing.specializes_closedPoint (R := Rh) (e.hom.base (toT.base ξ))).map
          e.inv.continuous
    · rw [hg, Scheme.Hom.comp_apply]
      exact (congrArg (specHenselizationToBase s Rh).base (hhom _)).trans
        (specHenselizationToBase_closedPoint s Rh)
  · intro h4 D e hg hD
    have hclosed : e.hom.base D.t = IsLocalRing.closedPoint Rh := by
      refine eq_closedPoint_of_specHenselizationToBase_apply_eq s Rh _ ?_
      rw [← Scheme.Hom.comp_apply, ← hg]
      exact D.mapsToChosenPoint
    have ht : e.inv.base (IsLocalRing.closedPoint Rh) = D.t := by
      rw [← hclosed, ← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    obtain ⟨hass, hnot⟩ := (ImpurityData.isImpurity_iff D F).mp hD
    obtain ⟨y, hy, hsp⟩ := h4 D.T D.g e hg D.X_T D.toX D.toT D.isPullback D.xi hass
    exact hnot y (hy.trans ht) hsp

end AlgebraicGeometry
