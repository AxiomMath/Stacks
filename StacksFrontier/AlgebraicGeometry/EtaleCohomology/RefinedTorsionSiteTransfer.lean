module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.RefinedTorsionLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# The refined torsion conditions move between the two spellings of the small étale site

This development has two small étale sites of a scheme `S`: the size-bounded one of
[Stacks, Tag 021B], `AlgebraicGeometry.SmallEtale.topology B S hS`, cut out of a big étale site
`B`, and Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology`. They have the same sheaves,
because the embedding `AlgebraicGeometry.SmallEtale.toEtaleSite` exhibits the first as a dense
subsite of the second; but a *condition* on a sheaf still has to be carried across, and for the
unrefined torsion condition only one direction was available, as
`Stacks.EtaleCohomology.torsionSheafProperty_of_pushforward`.

Both directions are proved here, for `Stacks.Torsion.IsLocallyAnnihilatedBy` and hence for both
refinements of torsion. Neither is formal, local annihilation being a condition on a covering
sieve. Restricting the condition to a subsite uses only cocontinuity of the embedding: a covering
sieve of `S.Etale` pulls back to a covering sieve of the bounded site. Extending it from the
subsite uses cover-density: a section over an object of `S.Etale` is, on the covering family of
all morphisms from objects of the subsite, pulled back from a section over such an object, where
the condition is available, and transitivity of the topology assembles the two coverings.

## Main results

* `Stacks.Torsion.isLocallyAnnihilatedBy_pushforward` and
  `Stacks.Torsion.isLocallyAnnihilatedBy_of_pushforward` — the two directions for a dense
  subsite inclusion, packaged as
  `Stacks.Torsion.isLocallyAnnihilatedBy_pushforward_iff`.
* `AlgebraicGeometry.SmallEtale.isPrimePowerTorsion_toEtaleSite_iff` and
  `AlgebraicGeometry.SmallEtale.isPrimeToCharacteristicTorsion_toEtaleSite_iff` — an abelian
  sheaf on Mathlib's small étale site of `S` is `l`-power torsion, respectively of torsion prime
  to `p`, exactly when its restriction to the size-bounded small étale site of `B` is.
* `AlgebraicGeometry.SmallEtale.torsionSheafProperty_toEtaleSite_iff` — the same for the
  unrefined torsion condition, which strengthens
  `Stacks.EtaleCohomology.torsionSheafProperty_of_pushforward` at this inclusion to an
  equivalence.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
* [Stacks Project, Tag 0DV7](https://stacks.math.columbia.edu/tag/0DV7)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.Torsion

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)

section Pushforward

variable [G.IsContinuous J K] (N : Set ℕ) (F : Sheaf K AddCommGrpCat.{w})

/-- **Local annihilation by `N` restricts along a cocontinuous functor.** A covering sieve of
`G.obj U` on which a section is annihilated pulls back to a covering sieve of `U`, and the
restriction of the section along an arrow of the pullback is its restriction along the image of
that arrow. -/
public theorem isLocallyAnnihilatedBy_pushforward [G.IsCocontinuous J K]
    (hF : IsLocallyAnnihilatedBy K N F.obj) :
    IsLocallyAnnihilatedBy J N
      ((G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj F).obj := by
  intro U x
  obtain ⟨R, hR, hkill⟩ := hF (G.obj U) x
  exact ⟨R.functorPullback G, G.cover_lift J K hR,
    fun V f hf => hkill (G.obj V) (G.map f) hf⟩

/-- **Local annihilation by `N` extends from a dense subsite.** A section over an object of the
larger site is, on the covering family of all morphisms from objects of the subsite, the
restriction of a section over such an object; there a covering sieve annihilates it by members of
`N`, and the image of that sieve is covering because the subsite is dense. So the annihilator
sieve of the original section is covering by transitivity.

For `N` the positive integers this is
`Stacks.EtaleCohomology.torsionSheafProperty_of_pushforward`, whose proof this is. -/
public theorem isLocallyAnnihilatedBy_of_pushforward [G.IsDenseSubsite J K]
    (hF : IsLocallyAnnihilatedBy J N
      ((G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj F).obj) :
    IsLocallyAnnihilatedBy K N F.obj := by
  have := Functor.IsDenseSubsite.isCoverDense J K G
  intro U x
  refine ⟨annihilatorSieve N F.obj x, ?_, fun V f hf => hf⟩
  refine K.transitive (G.is_cover_of_isCoverDense K U) _ ?_
  rintro V' g ⟨⟨W, l, m, rfl⟩⟩
  rw [Sieve.pullback_comp]
  refine K.pullback_stable l ?_
  obtain ⟨R, hR, hRx⟩ := hF W (F.obj.map m.op x)
  apply K.superset_covering (S := R.functorPushforward G) _
    ((G.functorPushforward_mem_iff J K).mpr hR)
  rintro V f ⟨W', g', h, hg', rfl⟩
  obtain ⟨n, hn, hx⟩ := hRx W' g' hg'
  refine ⟨n, hn, ?_⟩
  change n • (F.obj.map (G.map g').op).hom ((F.obj.map m.op).hom x) = 0 at hx
  simpa using congrArg (F.obj.map h.op).hom hx

/-- **Local annihilation by `N` is the same condition on a dense subsite and on the site.** -/
public theorem isLocallyAnnihilatedBy_pushforward_iff [G.IsDenseSubsite J K] :
    IsLocallyAnnihilatedBy J N
        ((G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj F).obj ↔
      IsLocallyAnnihilatedBy K N F.obj :=
  ⟨isLocallyAnnihilatedBy_of_pushforward J K G N F,
    fun hF => isLocallyAnnihilatedBy_pushforward J K G N F hF⟩

end Pushforward

end Stacks.Torsion

namespace AlgebraicGeometry.SmallEtale

open Stacks.Torsion

universe w u

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{w})

/-- **`l`-power torsion is the same condition on the two small étale sites.** An abelian sheaf on
Mathlib's small étale site of `S` is `l`-power torsion exactly when its restriction along
`AlgebraicGeometry.SmallEtale.toEtaleSite` to the size-bounded small étale site of
[Stacks, Tag 021B] is. -/
public theorem isPrimePowerTorsion_toEtaleSite_iff (l : ℕ) :
    IsPrimePowerTorsion (SmallEtale.topology B S hS) l
        (((toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{w}
          (SmallEtale.topology B S hS) S.smallEtaleTopology).obj F) ↔
      IsPrimePowerTorsion S.smallEtaleTopology l F :=
  Iff.trans
    (isPrimePowerTorsion_iff_isLocallyAnnihilatedBy l _)
    (Iff.trans
      (isLocallyAnnihilatedBy_pushforward_iff (SmallEtale.topology B S hS)
        S.smallEtaleTopology (toEtaleSite B S hS) (primePowerAnnihilators l) F)
      (isPrimePowerTorsion_iff_isLocallyAnnihilatedBy l F).symm)

/-- **Torsion prime to `p` is the same condition on the two small étale sites.** -/
public theorem isPrimeToCharacteristicTorsion_toEtaleSite_iff (p : ℕ) :
    IsPrimeToCharacteristicTorsion (SmallEtale.topology B S hS) p
        (((toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{w}
          (SmallEtale.topology B S hS) S.smallEtaleTopology).obj F) ↔
      IsPrimeToCharacteristicTorsion S.smallEtaleTopology p F :=
  Iff.trans
    (isPrimeToCharacteristicTorsion_iff_isLocallyAnnihilatedBy p _)
    (Iff.trans
      (isLocallyAnnihilatedBy_pushforward_iff (SmallEtale.topology B S hS)
        S.smallEtaleTopology (toEtaleSite B S hS) (coprimeAnnihilators p) F)
      (isPrimeToCharacteristicTorsion_iff_isLocallyAnnihilatedBy p F).symm)

/-- **Torsion is the same condition on the two small étale sites.** The direction that was
already available is `Stacks.EtaleCohomology.torsionSheafProperty_of_pushforward`. -/
public theorem torsionSheafProperty_toEtaleSite_iff :
    torsionSheafProperty (SmallEtale.topology B S hS)
        (((toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{w}
          (SmallEtale.topology B S hS) S.smallEtaleTopology).obj F) ↔
      torsionSheafProperty S.smallEtaleTopology F :=
  isLocallyAnnihilatedBy_pushforward_iff (SmallEtale.topology B S hS)
    S.smallEtaleTopology (toEtaleSite B S hS) positiveAnnihilators F

end AlgebraicGeometry.SmallEtale

end
