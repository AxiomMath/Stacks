module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalk
public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkModuleComparison
public import StacksFrontier.AlgebraicGeometry.Algebraization.StalkOfIdealOnOpen

/-!
# The completed local ring at a point of a chart is the completion of `B_𝔮`

Fix an algebraization situation, a point `y` of `U` and an `f` with `y ∈ D(f)`. Write `A_f` for
the chart ring, `B = (A_f)^∧_{I A_f}` for its `I`-adic completion and `𝔮` for the prime of `B`
above the prime of `A_f` under `y`. This file identifies

  `𝒪_{U,y}^∧ ≅ (B_𝔮)^∧_{I B_𝔮}`

and does the same for a module, so that a statement read over `(B_𝔮)^∧` can be read at `y` and
conversely. Both sides are the `I`-adic completion of the local ring of `A` at the prime under
`y`: that is the whole content, and it is what the route of [Stacks, Tag 0EHK] uses to move its
per-point step between the chart ring and the points of `U ∩ Y`.

The comparison itself is not new here. `Stacks.Algebraization.adicCompletionLocalizationAlgEquiv`
already identifies the `J`-adic completion of `R_𝔭` with the `J`-adic completion of `(R^∧)_𝔮`
for *any* ring `R`, finitely generated `J` and prime `𝔭 ⊇ J`, and
`Stacks.Algebraization.adicCompletionLocalizationAddEquiv` does the same for a module. What is
new is reading those at `R = A_f`, which needs `𝒪_{U,y}` to be recognised as a localization of
the chart ring, and that is what the first half of this file supplies.

## Main definitions

* `Stacks.Algebraization.chartPrimeOfPoint` — the prime `𝔭 A_f` of the chart ring under `y`.
* `Stacks.Algebraization.completedChartPrime` — the prime `𝔮` of `B` above it, namely
  `Stacks.Algebraization.adicPrimeOver`.

## Main results

* `Stacks.Algebraization.isLocalization_pointStalk` — **`𝒪_{U,y}` is the localization of `A` at
  the prime under `y`**, for the structure map `Stacks.Algebraization.baseToPointStalk`.
* `Stacks.Algebraization.isLocalization_chartPrimeOfPoint` — **`𝒪_{U,y}` is also the
  localization of the chart ring `A_f` at `𝔭 A_f`**, which is the form the comparison needs.
* `Stacks.Algebraization.nonempty_algEquiv_completedLocalRing_completedChartPrime` — **the ring
  comparison**: `𝒪_{U,y}^∧ ≅ (B_𝔮)^∧`, as `A_f`-algebras.
* `Stacks.Algebraization.nonempty_addEquiv_adicCompletion_completedChartPrime` — **the module
  side**, for a module presented as a localization of a chart-side module.

## Implementation notes

**The `A`-algebra structure on the stalk is a hypothesis, not an instance.** `𝒪_{U,y}` is a
stalk of a sheaf of rings and carries no canonical `A`-algebra structure; the one meant is
`Stacks.Algebraization.baseToPointStalk`, the germ of the structure map at the image of `y` in
`Spec A`. So the statements below take `[Algebra S.A _]` together with the equation `halg`
pinning its structure map to `baseToPointStalk`, which a consumer discharges with
`(baseToPointStalk S y).toAlgebra` and `rfl`. The `A_f`-algebra structure is a hypothesis for the
same reason; `IsLocalization.localizationAlgebraOfSubmonoidLe` with
`Stacks.Algebraization.powers_le_primeCompl` produces one, and
`IsLocalization.localization_isScalarTower_of_submonoid_le` the matching tower. Primality of
`Stacks.Algebraization.chartPrimeOfPoint` is likewise an instance hypothesis rather than
rederived in each statement: `Ideal.primeCompl` consumes it, so it is needed to *state* the
localization, and `Stacks.Algebraization.isPrime_chartPrimeOfPoint` is what discharges it.

**Why `𝒪_{U,y}` is a localization of `A_f` and not merely of `A`.** `IsLocalization` at
`(𝔭 A_f).primeCompl` is not the statement `IsLocalization.isLocalization_of_submonoid_le`
delivers: that gives a localization at the *image* of `𝔭.primeCompl`, a smaller submonoid. The
two give the same localization because an element `x` of `A_f` outside `𝔭 A_f` satisfies
`f^k · x = a` for an `a` of `A` outside `𝔭` — the powers of `f` being units of `A_f`, so they
cannot lie in a prime — and that is `IsLocalization.isLocalization_of_is_exists_mul_mem`.

**The module side is stated for an abstract module.**
`nonempty_addEquiv_adicCompletion_completedChartPrime` takes a module `Mp` over `𝒪_{U,y}` presented
as a localization at `𝔭 A_f` of an `A_f`-module, exactly as
`Stacks.Algebraization.adicCompletionLocalizationAddEquiv` asks for its `Mp`. The formal stalk of a
coherent adic system is *not* of this form in general (it is `I`-adically complete, a localization
is not), and it is compared with the chart side level by level instead, through
`Stacks.Algebraization.isLocalizedModule_restrictedTildeSystemToStalk`.

None of these declarations carries a `stacks` attribute: each is a step in the route of
[Stacks, Tag 0EHK], and none of them is the content of a tag.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK), the consumer.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the paragraph
  introducing `𝒪_{U,y}^∧`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

/-! ### The local ring of `U` at `y` as a localization of `A` -/

section PointStalk

variable (S : AlgebraizationSituation.{u}) (y : S.U.toScheme)

/-- **The local ring of `U` at `y` is the localization of `A` at the prime under `y`.**

The stalk of `Spec A` at the image of `y` is the localization of `A` there, by
`AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`, and the stalk map of the open
immersion carries it isomorphically to `𝒪_{U,y}`. The composite sends the image of `a : A` to the
germ of `a`, which is the last factor of `Stacks.Algebraization.baseToPointStalk`, and the
hypothesis `halg` says that germ map is the `A`-algebra structure in play on `𝒪_{U,y}`.

`Stacks.Algebraization.pointStalkRingEquiv` is the same comparison, built instead from
`AlgebraicGeometry.Scheme.Opens.stalkIso` and `AlgebraicGeometry.Spec.stalkIso`. It is not used
here, and nor is `Spec.stalkIso`: the point of `Spec A` under `y` has to be coerced from
`PrimeSpectrum A`, that coercion is not type-correct at reducible transparency, and computing
through it forces the stalk's colimit open — a heartbeat timeout rather than a wrong proof. The
`structurePresheafInCommRingCat` spelling used below carries no such coercion. -/
theorem isLocalization_pointStalk [Algebra S.A (S.U.toScheme.presheaf.stalk y)]
    (halg : algebraMap S.A (S.U.toScheme.presheaf.stalk y) = baseToPointStalk S y) :
    IsLocalization.AtPrime (S.U.toScheme.presheaf.stalk y) (underlyingPrime S y).asIdeal := by
  let : Algebra S.A (S.X.presheaf.stalk (S.U.ι.base y)) :=
    inferInstanceAs
      (Algebra S.A ((structurePresheafInCommRingCat S.A).stalk (underlyingPrime S y)))
  have : IsLocalization.AtPrime (S.X.presheaf.stalk (S.U.ι.base y))
      (underlyingPrime S y).asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime
      ((structurePresheafInCommRingCat S.A).stalk (underlyingPrime S y))
      (underlyingPrime S y).asIdeal)
  have hstalk : ∀ a : S.A, algebraMap S.A (S.X.presheaf.stalk (S.U.ι.base y)) a =
      (S.X.presheaf.germ ⊤ (S.U.ι.base y) (Set.mem_univ _)).hom
        ((Scheme.ΓSpecIso (.of S.A)).inv.hom a) := by
    intro a
    have h1 : algebraMap S.A (S.X.presheaf.stalk (S.U.ι.base y)) a =
        (StructureSheaf.toStalk S.A (underlyingPrime S y)).hom a :=
      StructureSheaf.stalkAlgebra_map S.A (underlyingPrime S y) a
    have h2 : ((S.X.presheaf.germ ⊤ (S.U.ι.base y) (Set.mem_univ _)).hom).comp
        (Scheme.ΓSpecIso (.of S.A)).inv.hom =
        (StructureSheaf.toStalk S.A (underlyingPrime S y)).hom := by
      dsimp only [StructureSheaf.toStalk]
      rw [Scheme.ΓSpecIso_inv]
      rfl
    rw [h1, ← h2]
    rfl
  have hbij : Function.Bijective (S.U.ι.stalkMap y).hom :=
    ConcreteCategory.bijective_of_isIso (S.U.ι.stalkMap y)
  refine IsLocalization.isLocalization_of_algEquiv (underlyingPrime S y).asIdeal.primeCompl
    (AlgEquiv.ofRingEquiv (R := S.A)
      (f := RingEquiv.ofBijective (S.U.ι.stalkMap y).hom hbij) ?_)
  intro a
  rw [halg, RingEquiv.ofBijective_apply, hstalk a]
  rfl

end PointStalk

/-! ### The prime of the chart ring under `y`, and the prime of `B` above it -/

section Chart

variable (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) (f : S.A)

/-- **The prime of the chart ring `A_f` under `y`**, that is, the extension of the prime of `A`
under `y` along `A → A_f`. It is prime because `y` lies in `D(f)`, by
`Stacks.Algebraization.isPrime_chartPrimeOfPoint`. -/
abbrev chartPrimeOfPoint : Ideal (Localization.Away f) :=
  (underlyingPrime S y).asIdeal.map (algebraMap S.A (Localization.Away f))

/-- A point of `D(f)` has `f` outside its prime, so every power of `f` is outside it. -/
theorem powers_le_primeCompl (hf : f ∉ (underlyingPrime S y).asIdeal) :
    Submonoid.powers f ≤ (underlyingPrime S y).asIdeal.primeCompl :=
  Submonoid.powers_le.mpr hf

/-- The powers of `f` are disjoint from the prime under a point of `D(f)`. -/
theorem disjoint_powers_underlyingPrime (hf : f ∉ (underlyingPrime S y).asIdeal) :
    Disjoint (Submonoid.powers f : Set S.A) ((underlyingPrime S y).asIdeal : Set S.A) :=
  Set.disjoint_left.mpr fun _ hx hx' => powers_le_primeCompl S y f hf hx hx'

/-- `Stacks.Algebraization.chartPrimeOfPoint` is a prime ideal. -/
theorem isPrime_chartPrimeOfPoint (hf : f ∉ (underlyingPrime S y).asIdeal) :
    (chartPrimeOfPoint S y f).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f) _
    (underlyingPrime S y).isPrime (disjoint_powers_underlyingPrime S y f hf)

/-- `Stacks.Algebraization.chartPrimeOfPoint` contracts to the prime under `y`. -/
theorem comap_chartPrimeOfPoint (hf : f ∉ (underlyingPrime S y).asIdeal) :
    (chartPrimeOfPoint S y f).comap (algebraMap S.A (Localization.Away f)) =
      (underlyingPrime S y).asIdeal :=
  IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f)
    (underlyingPrime S y).isPrime (disjoint_powers_underlyingPrime S y f hf)

variable [hp : (chartPrimeOfPoint S y f).IsPrime]

/-- **The local ring of `U` at `y` is the localization of the chart ring at
`Stacks.Algebraization.chartPrimeOfPoint`.**

`IsLocalization.isLocalization_of_submonoid_le` gives a localization at the image of
`𝔭.primeCompl` in `A_f`, which is a smaller submonoid than `(𝔭 A_f).primeCompl`. The two agree
because an element `x` of `A_f` outside `𝔭 A_f` satisfies `f^k · x = a` for some `a : A`, and
that `a` is outside `𝔭`: the powers of `f` are units of `A_f`, so they cannot lie in the prime
`𝔭 A_f`. -/
theorem isLocalization_chartPrimeOfPoint
    [Algebra S.A (S.U.toScheme.presheaf.stalk y)]
    [Algebra (Localization.Away f) (S.U.toScheme.presheaf.stalk y)]
    [IsScalarTower S.A (Localization.Away f) (S.U.toScheme.presheaf.stalk y)]
    (halg : algebraMap S.A (S.U.toScheme.presheaf.stalk y) = baseToPointStalk S y)
    (hf : f ∉ (underlyingPrime S y).asIdeal) :
    IsLocalization (chartPrimeOfPoint S y f).primeCompl
      (S.U.toScheme.presheaf.stalk y) := by
  have := isLocalization_pointStalk S y halg
  have himg : IsLocalization
      ((underlyingPrime S y).asIdeal.primeCompl.map (algebraMap S.A (Localization.Away f)))
      (S.U.toScheme.presheaf.stalk y) :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away f)
      (S.U.toScheme.presheaf.stalk y) (Submonoid.powers f)
      (underlyingPrime S y).asIdeal.primeCompl (powers_le_primeCompl S y f hf)
  have hnotmem : ∀ a : S.A, a ∉ (underlyingPrime S y).asIdeal →
      algebraMap S.A (Localization.Away f) a ∉ chartPrimeOfPoint S y f := by
    intro a ha hmem
    exact ha (by rw [← comap_chartPrimeOfPoint S y f hf]; exact hmem)
  refine IsLocalization.isLocalization_of_is_exists_mul_mem
    (S.U.toScheme.presheaf.stalk y)
    ((underlyingPrime S y).asIdeal.primeCompl.map (algebraMap S.A (Localization.Away f)))
    (chartPrimeOfPoint S y f).primeCompl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hnotmem a ha
  · rintro ⟨x, hx⟩
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) x
    have hunit : IsUnit (algebraMap S.A (Localization.Away f) (s : S.A)) :=
      IsLocalization.map_units (Localization.Away f) s
    have hs : algebraMap S.A (Localization.Away f) (s : S.A) ∉ chartPrimeOfPoint S y f :=
      fun hmem => hp.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)
    have hax : algebraMap S.A (Localization.Away f) a ∉ chartPrimeOfPoint S y f := by
      rw [← e]
      exact fun hmem => (hp.mem_or_mem hmem).elim hx hs
    refine ⟨algebraMap S.A (Localization.Away f) (s : S.A), ?_⟩
    change algebraMap S.A (Localization.Away f) (s : S.A) * x ∈ _
    rw [mul_comm, e]
    exact ⟨a, fun ha => hax (Ideal.mem_map_of_mem _ ha), rfl⟩

/-- **The prime `𝔮` of `B = (A_f)^∧_{I A_f}` attached to a point `y` of `U ∩ Y` on the chart
`D(f)`**: the prime `Stacks.Algebraization.adicPrimeOver` of the completion above the prime
`Stacks.Algebraization.chartPrimeOfPoint` of the chart ring. The hypothesis `hI` is that `y`
lies on `Y`. -/
def completedChartPrime (hI : S.I ≤ (underlyingPrime S y).asIdeal) :
    PrimeSpectrum (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
      (Localization.Away f)) :=
  adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f))) (Ideal.map_mono hI)

end Chart

/-! ### The ring comparison -/

section RingComparison

variable (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) (f : S.A)
  [Algebra S.A (S.U.toScheme.presheaf.stalk y)]
  [Algebra (Localization.Away f) (S.U.toScheme.presheaf.stalk y)]
  [IsScalarTower S.A (Localization.Away f) (S.U.toScheme.presheaf.stalk y)]
  (halg : algebraMap S.A (S.U.toScheme.presheaf.stalk y) = baseToPointStalk S y)

include halg in
/-- The extension of `I` to `𝒪_{U,y}` through the chart ring is the stalk of `I𝒪_U` at `y`. -/
theorem map_map_chartIdeal_eq_stalk_idealOnOpen :
    (S.I.map (algebraMap S.A (Localization.Away f))).map
        (algebraMap (Localization.Away f) (S.U.toScheme.presheaf.stalk y)) =
      IdealSheafData.stalk (idealOnOpen S) y := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, halg, stalk_idealOnOpen_eq_map]

variable [(chartPrimeOfPoint S y f).IsPrime]
  (hf : f ∉ (underlyingPrime S y).asIdeal) (hI : S.I ≤ (underlyingPrime S y).asIdeal)

include halg hf in
/-- **The completed local ring at a point of a chart is the `I`-adic completion of `B_𝔮`.**

Let `y` be a point of `U ∩ Y` lying on the chart `D(f)`, write `B = (A_f)^∧_{I A_f}` and let
`𝔮 = Stacks.Algebraization.completedChartPrime` be the prime of `B` above the prime of `A_f`
under `y`. Then `𝒪_{U,y}^∧` is the `I`-adic completion of any localization of `B` at `𝔮`, as
`A_f`-algebras — hence also as `A`-algebras, every ring in sight being an `A_f`-algebra over `A`.

This is `Stacks.Algebraization.adicCompletionLocalizationAlgEquiv` read at `R = A_f`: both sides
are the `I`-adic completion of the local ring of `A` at the prime under `y`, the left by
`Stacks.Algebraization.isLocalization_chartPrimeOfPoint` and the right by the correspondence of
primes of `A_f` with primes of `B` containing `I B`. -/
theorem nonempty_algEquiv_completedLocalRing_completedChartPrime
    (Rq : Type u) [CommRing Rq]
    [Algebra (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
      (Localization.Away f)) Rq]
    [Algebra (Localization.Away f) Rq]
    [IsScalarTower (Localization.Away f)
      (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
        (Localization.Away f)) Rq]
    [IsLocalization (completedChartPrime S y f hI).asIdeal.primeCompl Rq] :
    Nonempty (completedLocalRing (idealOnOpen S) y ≃ₐ[Localization.Away f]
      AdicCompletion ((S.I.map (algebraMap S.A (Localization.Away f))).map
        (algebraMap (Localization.Away f) Rq)) Rq) := by
  have := isLocalization_chartPrimeOfPoint S y f halg hf
  have : IsLocalization
      (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
        (Ideal.map_mono hI)).asIdeal.primeCompl Rq :=
    inferInstanceAs (IsLocalization (completedChartPrime S y f hI).asIdeal.primeCompl Rq)
  have e := adicCompletionLocalizationAlgEquiv
    (S.I.map (algebraMap S.A (Localization.Away f))) (Ideal.fg_of_isNoetherianRing _)
    (Ideal.map_mono hI)
    (S.U.toScheme.presheaf.stalk y) Rq
  rw [map_map_chartIdeal_eq_stalk_idealOnOpen S y f halg] at e
  exact ⟨e⟩

end RingComparison

/-! ### The module side -/

section ModuleComparison

variable (S : AlgebraizationSituation.{u}) (y : S.U.toScheme) (f : S.A)
  [Algebra S.A (S.U.toScheme.presheaf.stalk y)]
  [Algebra (Localization.Away f) (S.U.toScheme.presheaf.stalk y)]
  [IsScalarTower S.A (Localization.Away f) (S.U.toScheme.presheaf.stalk y)]
  (halg : algebraMap S.A (S.U.toScheme.presheaf.stalk y) = baseToPointStalk S y)
  [(chartPrimeOfPoint S y f).IsPrime]
  (hf : f ∉ (underlyingPrime S y).asIdeal) (hI : S.I ≤ (underlyingPrime S y).asIdeal)
  {N : Type u} [AddCommGroup N] [Module (Localization.Away f) N]
  {Mp : Type u} [AddCommGroup Mp] [Module (Localization.Away f) Mp]
    [Module (S.U.toScheme.presheaf.stalk y) Mp]
    [IsScalarTower (Localization.Away f) (S.U.toScheme.presheaf.stalk y) Mp]
  (fp : N →ₗ[Localization.Away f] Mp)
    [IsLocalizedModule (chartPrimeOfPoint S y f).primeCompl fp]
  (Rq : Type u) [CommRing Rq]
    [Algebra (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
      (Localization.Away f)) Rq]
    [Algebra (Localization.Away f) Rq]
    [IsScalarTower (Localization.Away f)
      (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
        (Localization.Away f)) Rq]
    [IsLocalization (completedChartPrime S y f hI).asIdeal.primeCompl Rq]
  {Mq : Type u} [AddCommGroup Mq]
    [Module (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
      (Localization.Away f)) Mq]
    [Module Rq Mq] [Module (Localization.Away f) Mq]
    [IsScalarTower (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
      (Localization.Away f)) Rq Mq]
    [IsScalarTower (Localization.Away f) Rq Mq]
    [IsScalarTower (Localization.Away f)
      (AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f)))
        (Localization.Away f)) Mq]
  (fq : AdicCompletion (S.I.map (algebraMap S.A (Localization.Away f))) N →ₗ[AdicCompletion
      (S.I.map (algebraMap S.A (Localization.Away f))) (Localization.Away f)] Mq)

include halg hf fp fq in
/-- **The module side of the chart comparison.**

For an `A_f`-module `N`, a localization `Mp` of `N` at the prime of `A_f` under `y` and a
localization `Mq` of the `I`-adic completion `N^∧` at the prime `𝔮` of `B`, the `I`-adic
completion of `Mp` is the `I`-adic completion of `Mq`. The left side is the completion of a
module over `𝒪_{U,y}` for the stalk `I𝒪_{U,y}` of the ideal, which is what makes it the
`completedStalk`-shaped side.

This is `Stacks.Algebraization.adicCompletionLocalizationAddEquiv` read at `R = A_f`, and it
lies over the ring comparison
`Stacks.Algebraization.nonempty_algEquiv_completedLocalRing_completedChartPrime` level by
level. -/
theorem nonempty_addEquiv_adicCompletion_completedChartPrime
    [IsLocalizedModule (completedChartPrime S y f hI).asIdeal.primeCompl fq] :
    Nonempty (AdicCompletion (IdealSheafData.stalk (idealOnOpen S) y) Mp ≃+
      AdicCompletion ((S.I.map (algebraMap S.A (Localization.Away f))).map
        (algebraMap (Localization.Away f) Rq)) Mq) := by
  have := isLocalization_chartPrimeOfPoint S y f halg hf
  have : IsLocalization
      (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
        (Ideal.map_mono hI)).asIdeal.primeCompl Rq :=
    inferInstanceAs (IsLocalization (completedChartPrime S y f hI).asIdeal.primeCompl Rq)
  have : IsLocalizedModule
      (adicPrimeOver (S.I.map (algebraMap S.A (Localization.Away f)))
        (Ideal.map_mono hI)).asIdeal.primeCompl fq :=
    inferInstanceAs
      (IsLocalizedModule (completedChartPrime S y f hI).asIdeal.primeCompl fq)
  have e := adicCompletionLocalizationAddEquiv
    (S.I.map (algebraMap S.A (Localization.Away f))) (Ideal.fg_of_isNoetherianRing _)
    (Ideal.map_mono hI)
    (S.U.toScheme.presheaf.stalk y) fp Rq fq
  rw [map_map_chartIdeal_eq_stalk_idealOnOpen S y f halg] at e
  exact ⟨e⟩

end ModuleComparison


end Stacks.Algebraization

end
