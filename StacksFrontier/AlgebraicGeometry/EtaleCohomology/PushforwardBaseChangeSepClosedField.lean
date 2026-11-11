module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed
public import StacksFrontier.Topology.Noetherian.LocallyConnected

/-!
# Base change for pushforward over a separably closed field

Let `k` be a separably closed field and let `f : X ⟶ Spec k` be locally of finite type. Then
every object `U` of the small étale site of `X` is covered by open subschemes which are
connected and quasi-compact, and over a separably closed field a connected scheme is
geometrically connected (Tag 0363). Each such open subscheme therefore factors through the
terminal étale `Spec k`-scheme by a quasi-compact morphism with geometrically connected
fibres, which is the covering condition of Tag 0EZX. Since `f` is automatically flat, Tag 0EZX
applies and the canonical base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` of a cartesian square over
`f` is an isomorphism for every sheaf of sets `F` on the small étale site of `T`.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed` — the case of Tag 0EZY
  of `X` locally of finite type over the separably closed field, deduced from Tag 0EZX with the
  bijectivity on sections over the étale `X`-schemes of the covering kept as the hypothesis
  `hlocal`. That hypothesis is discharged in
  `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_locallyOfFiniteType`, and
  Tag 0EZY itself, for an arbitrary `X`, is
  `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_of_quasiCompact`.

## Implementation notes

The covering is built one point at a time: a point of `U` lies in an affine open of `U`, which
is locally of finite type over `Spec k` and hence locally Noetherian, so by Tag 04MF it is
locally connected and the connected component of the point in it is open. That component is
also closed, hence quasi-compact, and connected, hence geometrically connected over `k` by Tag
0363.

The source reduces the general case to the finite-type case by writing an affine `X` as a
cofiltered limit of affine schemes of finite type over `Spec k` and appealing to Tag 0EZT part
(1). The general case is proved by a stalkwise argument instead, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/PushforwardBaseChangeSepClosedFieldGeneral.lean`.

The bijectivity on sections which Tag 0EZX feeds on is the hypothesis `hlocal` of the theorem
below; it is proved as `Stacks.EtaleCohomology.local_baseChange_compatible`, by which
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_locallyOfFiniteType` removes
it.

## References

* [Stacks Project, Tag 0EZY](https://stacks.math.columbia.edu/tag/0EZY)
* [Stacks Project, Tag 0EZX](https://stacks.math.columbia.edu/tag/0EZX)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0363](https://stacks.math.columbia.edu/tag/0363)
* [Stacks Project, Tag 04MF](https://stacks.math.columbia.edu/tag/04MF)
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section SepClosedField

/-- For `X` locally of finite type over a separably closed field `k`, every point of an étale
`X`-scheme `U` lies in the image of an étale `X`-scheme over `U` whose structure morphism to
`Spec k` is quasi-compact with geometrically connected fibres: take the connected component of
the point in an affine open of `U`, which is open because that affine open is Noetherian. -/
private theorem exists_connectedFactorization_at (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (U : X.Etale) (x : U.left) :
    ∃ (U' : X.Etale) (a : U' ⟶ U) (V : (Spec (.of k)).Etale) (q : U'.left ⟶ V.left),
      (∃ y : U'.left, a.left y = x) ∧ q ≫ V.hom = U'.hom ≫ f ∧
        QuasiCompact q ∧ GeometricallyConnected q := by
  classical
  let c := U.left.affineCover
  obtain ⟨i, y, hy⟩ := c.exists_eq x
  have hAff : IsAffine (c.X i) := Scheme.isAffine_affineCover _ _
  have hCS : CompactSpace (c.X i) := Scheme.compactSpace_of_isAffine _
  have hLN : IsLocallyNoetherian (c.X i) :=
    LocallyOfFiniteType.isLocallyNoetherian (c.f i ≫ U.hom ≫ f)
  have hNoeth : AlgebraicGeometry.IsNoetherian (c.X i) := { }
  have hNS : TopologicalSpace.NoetherianSpace (c.X i) := inferInstance
  have hLC : LocallyConnectedSpace (c.X i) :=
    TopologicalSpace.IsLocallyNoetherianSpace.locallyConnectedSpace _
      (isLocallyNoetherianSpace_of_noetherianSpace (c.X i))
  let O : (c.X i).Opens := ⟨connectedComponent y, isOpen_connectedComponent⟩
  let W : Scheme.{u} := O.toScheme
  let jW : W ⟶ U.left := O.ι ≫ c.f i
  have hWcompact : CompactSpace W := by
    change CompactSpace ↥(O : Set (c.X i))
    exact isCompact_iff_compactSpace.mp (isClosed_connectedComponent (x := y)).isCompact
  have hWconn : ConnectedSpace W := by
    change ConnectedSpace ↥(O : Set (c.X i))
    exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hQS : QuasiSeparatedSpace (Spec (CommRingCat.of k)) :=
    AlgebraicGeometry.quasiSeparatedSpace_of_isAffine _
  have hQC : QuasiCompact (jW ≫ U.hom ≫ f) :=
    AlgebraicGeometry.quasiCompact_of_compactSpace _
  refine ⟨Scheme.Etale.mk (jW ≫ U.hom), MorphismProperty.Over.homMk jW rfl,
    Scheme.Etale.mk (𝟙 (Spec (.of k))), jW ≫ U.hom ≫ f,
    ⟨⟨y, mem_connectedComponent⟩, ?_⟩,
    (Category.comp_id _).trans (Category.assoc jW U.hom f).symm, hQC,
    (AlgebraicGeometry.geometricallyConnected_iff_connectedSpace k (jW ≫ U.hom ≫ f)).2 hWconn⟩
  change c.f i y = x
  exact hy

/-- For `X` locally of finite type over a separably closed field `k`, every object of the small
étale site of `X` has an étale covering whose members factor through an étale `Spec k`-scheme
by a quasi-compact morphism with geometrically connected fibres: the covering condition of Tag
0EZX. -/
private theorem exists_etaleLocalFactorization_of_isSepClosed (k : Type u) [Field k]
    [IsSepClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (U : X.Etale) :
    ∃ (ι : Type (u + 1)) (U' : ι → X.Etale) (a : ∀ i, U' i ⟶ U)
      (V : ι → (Spec (.of k)).Etale) (q : ∀ i, (U' i).left ⟶ (V i).left),
      Sieve.ofArrows U' a ∈ smallEtaleTopology X U ∧
        ∀ i, q i ≫ (V i).hom = (U' i).hom ≫ f ∧
          QuasiCompact (q i) ∧ GeometricallyConnected (q i) := by
  classical
  choose U₀ a₀ V₀ q₀ hpt hfac hqc hgc using
    fun x : U.left => exists_connectedFactorization_at k f U x
  refine ⟨ULift.{u + 1} U.left, fun i => U₀ i.down, fun i => a₀ i.down,
    fun i => V₀ i.down, fun i => q₀ i.down, ?_, fun i => ⟨hfac i.down, hqc i.down, hgc i.down⟩⟩
  rw [ofArrows_mem_smallEtaleTopology_iff (fun i : ULift.{u + 1} U.left => a₀ i.down)]
  refine Set.eq_univ_iff_forall.mpr fun x => Set.mem_iUnion.mpr ⟨ULift.up x, ?_⟩
  obtain ⟨y, hyx⟩ := hpt x
  exact ⟨y, hyx⟩

variable {X Y T : Scheme.{u}}

/-- **Base change for pushforward over a separably closed field, `X` locally of finite type,
from the bijectivity on sections over the covering.** Let `k` be a separably closed field and
let `f : X ⟶ Spec k` be locally of finite type. If, in a cartesian square over `f`, the base
change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is bijective on sections over every étale `X`-scheme carrying
a flat quasi-compact factorization with geometrically connected fibres (`hlocal`), then it is
an isomorphism. The hypothesis `hlocal` is always satisfied, by
`Stacks.EtaleCohomology.local_baseChange_compatible`, which gives
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_locallyOfFiniteType`; and
Stacks Tag 0EZY for an arbitrary `X` is
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_of_quasiCompact`. -/
theorem isIso_smallEtaleSetBaseChange_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (h : Y ⟶ X) (e : Y ⟶ T)
    (g : T ⟶ Spec (.of k)) (sq : IsPullback h e f g)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    (hlocal : ∀ ⦃U : X.Etale⦄, HasFlatConnectedFactorization f U →
      Function.Bijective
        (((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F).hom.app (op U))) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) := by
  have : Flat f := inferInstance
  exact isIso_smallEtaleSetBaseChange_of_etaleLocalFactorization.{u, v} f h e g sq F
    (fun U => exists_etaleLocalFactorization_of_isSepClosed k f U) hlocal

end SepClosedField

end Stacks.EtaleCohomology

end
