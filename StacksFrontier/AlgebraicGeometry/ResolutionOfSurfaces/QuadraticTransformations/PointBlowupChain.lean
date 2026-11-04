module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.RegularPullback
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumPullback
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk

/-!
# Sequences of blowups at closed points

Let `X` be a scheme and `T` a set of points of `X`. A *point blowup chain* over `T` is a finite
composition `Xₙ → Xₙ₋₁ → … → X₀ = X` in which each `Xᵢ₊₁ → Xᵢ` is the blowup of `Xᵢ` at a closed
point whose image in `X` lies in `T`; the reduced closed subscheme supported at a closed point
`x` is the vanishing ideal sheaf of `{x}`, so this blowup is the blowup in that ideal sheaf.
Chains compose, and the inverse image of an effective Cartier divisor along a chain is again an
effective Cartier divisor.

Principalizing a quasi-coherent sheaf of ideals supported on a finite set of closed points whose
local rings are regular of dimension two is an induction on the total colength: if one blowup at
a point of the support splits the pulled-back ideal as a power of the exceptional divisor times
an ideal of strictly smaller total colength, then iterating produces a chain along which the
ideal becomes invertible.

Such a chain also dominates any proper morphism `Y → X` which is an isomorphism over the
complement of the finite set: principalizing the centre of a blowup that dominates `Y` makes the
composite morphism to `X` factor through `Y`, by the universal property of blowing up.

## Main definitions

* `Stacks.ResolutionOfSurfaces.PointBlowupChain` — a finite sequence of blowups at closed points
  lying over a given set of points, indexed by its composite morphism.
* `Stacks.ResolutionOfSurfaces.totalColength` — the sum, over a finite set of points, of the
  length of the quotient of the local ring by the stalk of a sheaf of ideals.

## Main results

* `Stacks.ResolutionOfSurfaces.length_quotient_stalk_eq_zero_of_notMem_support` — points off the
  support of a sheaf of ideals contribute nothing to its total colength.
* `Stacks.ResolutionOfSurfaces.PointBlowupChain.comp` — a chain over a set of points of the
  source of a chain composes with it to a chain over the original set.
* `Stacks.ResolutionOfSurfaces.PointBlowupChain.isEffectiveCartierDivisor_comap` — the inverse
  image of an effective Cartier divisor along a point blowup chain is an effective Cartier
  divisor.
* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_isEffectiveCartierDivisor` — an ideal
  sheaf supported on a finite set of closed points with regular two-dimensional local rings
  becomes an invertible ideal sheaf along a chain of blowups at closed points over that set,
  granted at each point of the support the local splitting of the pulled-back ideal into a power
  of the exceptional divisor times an ideal of smaller total colength.
* `Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_factorization` — a proper morphism to `X`
  which is an isomorphism away from a finite set of closed points with regular two-dimensional
  local rings is dominated by a chain of blowups at closed points lying over that set.

## Implementation notes

The local splitting at a point of the support is a hypothesis of the main theorem: it is the
content of [Stacks, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT), the local statement for
a regular two-dimensional local ring, which is not among the results proved here. Everything
else — the recursion on the total colength, the composition of the chains it produces, and the
invertibility of the resulting inverse image — is unconditional.

The dominating result consumes a second statement that is not proved here, and it too is threaded
through as a hypothesis rather than discharged: the existence of a `U`-admissible blowup of `X`
dominating a proper morphism which is an isomorphism over `U`, which is
[Stacks, Tag 081T](https://stacks.math.columbia.edu/tag/081T). Admissibility is
`Stacks.Blowup.IsAdmissibleBlowup`, and the morphism from the chain to that blowup is produced by
the universal property of blowing up,
[Stacks, Tag 0806](https://stacks.math.columbia.edu/tag/0806).

Invertibility of a sheaf of ideals is `Stacks.Divisors.IsEffectiveCartierDivisor`, and the
`d`-fold multiple `dE` of the exceptional divisor is the `d`-th power of
`AlgebraicGeometry.exceptionalIdeal`. Finite sets of points are `Finset`s, so that the total
colength is a `Finset` sum; points off the support contribute nothing to it, their stalk being
the unit ideal.

## References

* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 0AHI](https://stacks.math.columbia.edu/tag/0AHI)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- A finite sequence of blowups at closed points lying over `T ⊆ X`, indexed by the composite
morphism to `X`: either the identity of `X`, or the blowup of such a sequence at a closed point
of its source whose image in `X` belongs to `T`. -/
public inductive PointBlowupChain (X : Scheme.{u}) (T : Set X) :
    ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop
  | refl : PointBlowupChain X T X (𝟙 X)
  | step {W : Scheme.{u}} {h : W ⟶ X} (hh : PointBlowupChain X T W h) (w : W)
      (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T) :
      PointBlowupChain X T
        (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)

/-- The total colength of a sheaf of ideals along a finite set of points: the sum over those
points of the length of the quotient of the local ring by the stalk of the ideal. -/
public noncomputable def totalColength {X : Scheme.{u}} (I : X.IdealSheafData) (S : Finset X) :
    ℕ∞ :=
  ∑ x ∈ S, Module.length (X.presheaf.stalk x)
    (X.presheaf.stalk x ⧸ AlgebraicGeometry.IdealSheafData.stalk I x)

/-- A point outside the support of a sheaf of ideals contributes nothing to the total colength:
the stalk of the ideal there is the unit ideal, so the quotient of the local ring vanishes. -/
public theorem length_quotient_stalk_eq_zero_of_notMem_support {X : Scheme.{u}}
    (I : X.IdealSheafData) {x : X} (hx : x ∉ (I.support : Set X)) :
    Module.length (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ AlgebraicGeometry.IdealSheafData.stalk I x) = 0 := by
  rw [(AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support I x).mpr hx,
    Module.length_eq_zero_iff]
  exact Ideal.Quotient.subsingleton_iff.mpr rfl

/-- A point blowup chain over a set of points of the source of another point blowup chain
composes with it, provided that set maps into the set of the outer chain. -/
public theorem PointBlowupChain.comp {X Y Z : Scheme.{u}} {T : Set X} {S : Set Y}
    {f : Y ⟶ X} {g : Z ⟶ Y} (hf : PointBlowupChain X T Y f)
    (hg : PointBlowupChain Y S Z g) (hST : ∀ y ∈ S, f.base y ∈ T) :
    PointBlowupChain X T Z (g ≫ f) := by
  induction hg with
  | refl => simpa using hf
  | step hh w hw hwS ih =>
    rw [Category.assoc]
    exact ih.step w hw (by simpa using hST _ hwS)

/-- The inverse image of an effective Cartier divisor along a point blowup chain is an effective
Cartier divisor. -/
public theorem PointBlowupChain.isEffectiveCartierDivisor_comap {X Y : Scheme.{u}} {T : Set X}
    {f : Y ⟶ X} (hf : PointBlowupChain X T Y f) {D : X.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Stacks.Divisors.IsEffectiveCartierDivisor (D.comap f) := by
  induction hf with
  | refl => simpa using hD
  | step hh w hw hwT ih =>
    rw [Scheme.IdealSheafData.comap_comp]
    exact AlgebraicGeometry.isPullbackDefined_blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) _ ih

/-- **Stacks Project, Tag 0AHH**, the induction on the total colength. Let `T` be a finite set of
closed points of a scheme `X` whose local rings are regular of dimension two, and let `I` be a
quasi-coherent sheaf of ideals whose quotient is supported on `T`. Assume that at every point `y`
of the support of such an ideal the pulled-back ideal splits as `dE + I'` for the exceptional
divisor `E` of the blowup at `y` and an ideal `I'` again supported on a finite set of closed
points with regular two-dimensional local rings lying over `T` and of strictly smaller total
colength — the local statement of Tag 0AGT. Then there is a sequence of blowups at closed points
lying over `T` along which `I` becomes an invertible sheaf of ideals. -/
@[stacks 0AHH "the induction on the total colength, granted the local splitting of Tag 0AGT"]
public theorem exists_pointBlowupChain_isEffectiveCartierDivisor
    (descent : ∀ (Y : Scheme.{u}) (S : Finset Y) (J : Y.IdealSheafData),
      (∀ y ∈ S, IsClosed ({y} : Set Y)) →
      (∀ y ∈ S, IsRegularLocalRing (Y.presheaf.stalk y)) →
      (∀ y ∈ S, ringKrullDim (Y.presheaf.stalk y) = 2) →
      (J.support : Set Y) ⊆ (S : Set Y) →
      ∀ y ∈ (J.support : Set Y), ∀ hy : IsClosed ({y} : Set Y),
      ∀ M : Y.IdealSheafData, M = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ →
        ∃ (d : ℕ) (S' : Finset (blowUp M)) (J' : (blowUp M).IdealSheafData),
          exceptionalIdeal M ^ d * J' = J.comap (blowUpToBase M) ∧
          (∀ z ∈ S', IsClosed ({z} : Set (blowUp M))) ∧
          (∀ z ∈ S', IsRegularLocalRing ((blowUp M).presheaf.stalk z)) ∧
          (∀ z ∈ S', ringKrullDim ((blowUp M).presheaf.stalk z) = 2) ∧
          (J'.support : Set (blowUp M)) ⊆ (S' : Set (blowUp M)) ∧
          (∀ z ∈ S', (blowUpToBase M).base z ∈ S) ∧
          totalColength J' S' < totalColength J S)
    {X : Scheme.{u}} (T : Finset X)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hregular : ∀ x ∈ T, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2)
    (I : X.IdealSheafData) (hI : (I.support : Set X) ⊆ (T : Set X)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), PointBlowupChain X (T : Set X) Y f ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) := by
  suffices H : ∀ (m : ℕ∞) (X : Scheme.{u}) (T : Finset X),
      (∀ x ∈ T, IsClosed ({x} : Set X)) →
      (∀ x ∈ T, IsRegularLocalRing (X.presheaf.stalk x)) →
      (∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2) →
      ∀ I : X.IdealSheafData, (I.support : Set X) ⊆ (T : Set X) →
      totalColength I T = m →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), PointBlowupChain X (T : Set X) Y f ∧
        Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) by
    exact H _ X T hclosed hregular hdim I hI rfl
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  intro X T hclosed hregular hdim I hI hm
  by_cases hItop : I = ⊤
  · subst hItop
    refine ⟨X, 𝟙 X, .refl, ?_⟩
    rw [Scheme.IdealSheafData.comap_id]
    exact Stacks.Divisors.isEffectiveCartierDivisor_top
  · obtain ⟨x, hx⟩ : ((I.support : Set X)).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hemp
      exact hItop ((Scheme.IdealSheafData.support_eq_bot_iff (I := I)).mp
        (TopologicalSpace.Closeds.coe_eq_empty.mp hemp))
    have hxT : x ∈ T := Finset.mem_coe.mp (hI hx)
    have hxclosed : IsClosed ({x} : Set X) := hclosed x hxT
    set M : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hxclosed⟩ with hM
    obtain ⟨d, S', J', hsplit, hS'closed, hS'reg, hS'dim, hJ'supp, hS'over, hlt⟩ :=
      descent X T I hclosed hregular hdim hI x hx hxclosed M hM
    obtain ⟨Y, g, hchain, hcartier⟩ :=
      ih (totalColength J' S') (hm ▸ hlt) (blowUp M) S' hS'closed hS'reg hS'dim J' hJ'supp rfl
    have hbase : PointBlowupChain X (T : Set X) (blowUp M) (blowUpToBase M) := by
      simpa using (PointBlowupChain.refl (X := X) (T := (T : Set X))).step x hxclosed hxT
    refine ⟨Y, g ≫ blowUpToBase M, hbase.comp hchain (fun z hz => hS'over z hz), ?_⟩
    rw [Scheme.IdealSheafData.comap_comp, ← hsplit, AlgebraicGeometry.comap_mul]
    exact AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _
      (hchain.isEffectiveCartierDivisor_comap
        (Stacks.Divisors.isEffectiveCartierDivisor_pow
          (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal M) d))
      hcartier

/-- **Stacks Project, Tag 0AHI.** Let `X` be a Noetherian scheme, let `T` be a finite set of
closed points of `X` whose local rings are regular of dimension two, and let `U` be the
complement of `T`. A proper morphism `f : Y ⟶ X` which is an isomorphism over `U` is dominated by
a sequence `Xₙ → … → X₁ → X` of blowups at closed points lying over `T`, in the sense that the
composite `Xₙ ⟶ X` factors through `f`.

Two statements are threaded through as hypotheses rather than discharged: the local splitting of
[Stacks, Tag 0AGT] that the formalized form of [Stacks, Tag 0AHH] consumes, and the dominating
`U`-admissible blowup of [Stacks, Tag 081T]. -/
@[stacks 0AHI "granted Tag 081T and the local splitting of Tag 0AGT"]
public theorem exists_pointBlowupChain_factorization
    (descent : ∀ (Y : Scheme.{u}) (S : Finset Y) (J : Y.IdealSheafData),
      (∀ y ∈ S, IsClosed ({y} : Set Y)) →
      (∀ y ∈ S, IsRegularLocalRing (Y.presheaf.stalk y)) →
      (∀ y ∈ S, ringKrullDim (Y.presheaf.stalk y) = 2) →
      (J.support : Set Y) ⊆ (S : Set Y) →
      ∀ y ∈ (J.support : Set Y), ∀ hy : IsClosed ({y} : Set Y),
      ∀ M : Y.IdealSheafData, M = Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hy⟩ →
        ∃ (d : ℕ) (S' : Finset (blowUp M)) (J' : (blowUp M).IdealSheafData),
          exceptionalIdeal M ^ d * J' = J.comap (blowUpToBase M) ∧
          (∀ z ∈ S', IsClosed ({z} : Set (blowUp M))) ∧
          (∀ z ∈ S', IsRegularLocalRing ((blowUp M).presheaf.stalk z)) ∧
          (∀ z ∈ S', ringKrullDim ((blowUp M).presheaf.stalk z) = 2) ∧
          (J'.support : Set (blowUp M)) ⊆ (S' : Set (blowUp M)) ∧
          (∀ z ∈ S', (blowUpToBase M).base z ∈ S) ∧
          totalColength J' S' < totalColength J S)
    {X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X] (T : Finset X) (U : X.Opens)
    (hU : (U : Set X) = (T : Set X)ᶜ)
    (hclosed : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hregular : ∀ x ∈ T, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) = 2)
    (f : Y ⟶ X) [IsProper f] [IsIso (f ∣_ U)]
    (dominated : ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      Stacks.Blowup.IsAdmissibleBlowup U b ∧ ∃ h : X' ⟶ Y, h ≫ f = b) :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ X), PointBlowupChain X (T : Set X) Z p ∧
      ∃ g : Z ⟶ Y, g ≫ f = p := by
  obtain ⟨X', b, hadm, h, hhb⟩ := dominated
  obtain ⟨I, -, hdisj, e, he⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff U b).mp hadm
  have hI : (I.support : Set X) ⊆ (T : Set X) := by
    intro x hx
    by_contra hxT
    have hxU : x ∈ (U : Set X) := by rw [hU]; exact hxT
    exact Set.disjoint_left.mp hdisj hxU hx
  obtain ⟨Z, p, hchain, hcartier⟩ :=
    exists_pointBlowupChain_isEffectiveCartierDivisor descent T hclosed hregular hdim I hI
  obtain ⟨q, hq⟩ := Stacks.Blowup.exists_hom_blowUp_of_isEffectiveCartierDivisor I p hcartier
  have hinv : e.inv ≫ b = blowUpToBase I := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  refine ⟨Z, p, hchain, q ≫ e.inv ≫ h, ?_⟩
  simp only [Category.assoc]
  rw [hhb, hinv]
  exact hq

/-- A scheme proper over a Noetherian scheme is Noetherian. -/
public theorem isNoetherian_of_isProper_over_noetherian {A B : Scheme.{u}} [IsNoetherian B]
    (f : A ⟶ B) [IsProper f] : IsNoetherian A := by
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  constructor

/-- The blowup of a Noetherian scheme is Noetherian. -/
public theorem isNoetherian_blowUp {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) :
    IsNoetherian (blowUp I) :=
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  isNoetherian_of_isProper_over_noetherian (blowUpToBase I)

/-- A chain of blowups of a Noetherian scheme at closed points has Noetherian source. -/
public theorem isNoetherian_of_pointBlowupChain {X W : Scheme.{u}} [IsNoetherian X] {T : Set X}
    {f : W ⟶ X} (h : PointBlowupChain X T W f) : IsNoetherian W := by
  induction h with
  | refl => infer_instance
  | step hh w hw hwT ih =>
      have := ih
      exact isNoetherian_blowUp _


end Stacks.ResolutionOfSurfaces

end
