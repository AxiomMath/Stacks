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

* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed` — **Tag 0EZY** in the
  case of `X` locally of finite type over the separably closed field, which contains the
  source's finite-type case.

## Implementation notes

The covering is built one point at a time: a point of `U` lies in an affine open of `U`, which
is locally of finite type over `Spec k` and hence locally Noetherian, so by Tag 04MF it is
locally connected and the connected component of the point in it is open. That component is
also closed, hence quasi-compact, and connected, hence geometrically connected over `k` by Tag
0363.

The source reduces the general case to the finite-type case by writing an affine `X` as a
cofiltered limit of affine schemes of finite type over `Spec k` and appealing to Tag 0EZT part
(1), the compatibility of the base change map with such limits. Tag 0EZT has no carrier in the
library, so only the finite-type case is asserted here.

The chain of identifications of sections which Tag 0EZX feeds on rests on Tag 0A3H read through
Tag 03EF, which is not available in that form; exactly as for Tags 0EZX, 0EYS and 0EZZ it is
carried as the declared hypothesis `hlocal`.

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

/-- **Stacks Project, Tag 0EZY**, in the case of `X` locally of finite type over the separably
closed field. Let `k` be a separably closed field and let `f : X ⟶ Spec k` be locally of finite
type. Then in a cartesian square over `f` the canonical base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F`
is an isomorphism for every sheaf of sets `F` on the small étale site of `T`. -/
@[stacks 0EZY "the case of `X` of finite type over the separably closed field, stated for `X`
locally of finite type. What is proved unconditionally is the covering condition of Tag 0EZX:
an affine open of an étale `X`-scheme is Noetherian, hence locally connected by Tag 04MF, so
the connected component of any of its points is an open quasi-compact subscheme, and over a
separably closed field a connected scheme is geometrically connected by Tag 0363; flatness of
`f` is automatic over a field. The source's reduction of the general case to this one -- write
an affine `X` as a cofiltered limit of affine finite-type `Spec k`-schemes and use the
compatibility of the base change map with such limits -- is Tag 0EZT part (1), which has no
carrier in the library, so the general case is not asserted. The chain of identifications of
sections on which Tag 0EZX feeds rests on Tag 0A3H read through Tag 03EF, a separate cited tag
unavailable in that form, and is carried -- exactly as in Tags 0EZX, 0EYS and 0EZZ -- as the
declared hypothesis `hlocal`."]
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
