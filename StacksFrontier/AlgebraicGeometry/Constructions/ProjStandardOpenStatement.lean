module

public import StacksFrontier.RingTheory.GradedAlgebra.Proj.AwayGradedPrimesDiagram
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjModuleRestriction

/-!
# Tag 01M4 in one statement

Let `A = ⨁_{i ≥ 0} 𝒜 i` be a graded ring and let `f ∈ 𝒜 d` be homogeneous of positive degree.
Tag 01M4 makes ten assertions about the standard open `D₊(f)`:

* part (1), for every homogeneous `g` of positive degree with `D₊(g) ⊆ D₊(f)`:
  * (a) `f` is invertible in `A[1/g]`, and `f ^ deg g / g ^ deg f` is invertible in `A₍g₎`;
  * (b) `g ^ k = a * f` for some `k ≥ 1` and homogeneous `a`;
  * (c) there is a canonical `A`-algebra map `A[1/f] → A[1/g]`;
  * (d) there is a canonical `𝒜 0`-algebra map `A₍f₎ → A₍g₎`, compatible with `A[1/f] → A[1/g]`;
  * (e) that map exhibits `A₍g₎` as `(A₍f₎)` localized at `g ^ deg f / f ^ deg g`;
  * (f) the maps induce a commutative diagram of topological spaces whose horizontal arrows are
    homeomorphisms and whose vertical arrows are open immersions;
  * (g) for every graded `A`-module `M` there are compatible canonical maps `M_f → M_g` and
    `M₍f₎ → M₍g₎`, semilinear over the ring maps of (c) and (d);
  * (h) the second of those exhibits `M₍g₎` as `M₍f₎` localized at `g ^ deg f / f ^ deg g`;
* part (2), every open covering of `D₊(f)` admits a finite refinement by standard opens;
* part (3), `D₊(f) ⊆ ⋃ D₊(gᵢ)` holds exactly when the fractions `gᵢ ^ deg f / f ^ deg gᵢ`
  generate the unit ideal of `A₍f₎`.

The ten are established separately across four modules — `ProjBasicOpen` proves (a), (b), (2)
and (3), `ProjLocalizedRingMap` proves (c), (d) and (e), `AwayGradedPrimesDiagram` proves (f),
and `ProjModuleRestriction` proves (g) and (h) — so no single declaration said what the tag
says; this file states all ten together.

The binders of part (1) — the element `g`, its degree, and the containment `D₊(g) ⊆ D₊(f)` —
are quantified inside the conjunct for part (1), and the graded module `M` of (g) and (h) is
quantified inside the conjunct that speaks about it. So parts (2) and (3) carry no hypothesis
on `g` that the source does not impose on them, and (a)–(f) carry none about a module.

Each of the canonical maps of (c), (d) and (g) appears by name rather than under an
existential, and is accompanied by the property that pins it down: the map of (c) is the
unique `A`-algebra map between the two localizations, the map of (d) is the only `𝒜 0`-algebra
map whose values are those of (c), and the pair of (g) is induced by the identity of `M` — its
first map is the only one so induced, and its second the only one restricting the first.

## Implementation notes

The graded ring is presented as `𝒜 : ℕ → Submodule R A` for a base ring `R`, the form the
construction of the middle column of the diagram of (f) is written in. Taking `R = ℤ` makes
`Submodule R A` the additive subgroups of `A`, so this is the general graded ring.

The grading of a module by `ℤ` under a ring graded by `ℕ` uses the action `n +ᵥ z = n + z`,
supplied as a file-local instance just as the modules proving (g) and (h) do, since `ℕ` acting
on `ℤ` by addition is not an instance Mathlib wants globally. It is the same function as theirs,
so `SetLike.GradedSMul 𝒜 𝒨` means the same thing here as there and the instances unify. It
carries its own name rather than being anonymous, because two anonymous `VAdd ℕ ℤ` instances at
the root namespace receive the same generated name and cannot both be imported.

## Main results

* `Stacks.ProjStandardOpenStatement.tag01M4`: the ten assertions of the tag in one statement.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public section

open Stacks.ProjStandardOpenBaseChange HomogeneousLocalization

/-- The grading action used for a naturally graded ring acting on an integer-graded module. -/
local instance instVAddNatIntProjStandardOpenStatement : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

namespace Stacks.ProjStandardOpenStatement

universe u v w t s s'

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- **[Stacks, Tag 01M4].** For a graded ring `A` and `f ∈ 𝒜 d` homogeneous of positive degree:

* part (1), for homogeneous `g` of positive degree with `D₊(g) ⊆ D₊(f)`, the eight assertions
  (a)–(h) of the source, the module assertions (g) and (h) quantified over the graded module
  inside their own conjuncts;
* part (2), the finite refinement of an open covering of `D₊(f)` by standard opens;
* part (3), the unit-ideal criterion for `D₊(f) ⊆ ⋃ D₊(gᵢ)`. -/
@[stacks 01M4 "the ten assertions of the tag in one statement: part (1)(a)-(h) for a standard \
open D+(g) contained in D+(f), part (2) the finite refinement of an open covering of D+(f) by \
standard opens, part (3) the unit-ideal criterion"]
theorem tag01M4 (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f : A} {d : ℕ}
    (hfd : f ∈ 𝒜 d) (hd : 0 < d) :
    -- part (1)
    (∀ (g : A) (e : ℕ) (hge : g ∈ 𝒜 e) (he : 0 < e)
        (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f),
        -- (a) `f` is invertible in `A[1/g]`, and `f ^ deg g / g ^ deg f` is invertible in `A₍g₎`
        (IsUnit (algebraMap A (Localization.Away g) f) ∧
          IsUnit (Away.isLocalizationElem hge hfd)) ∧
        -- (b) a positive power of `g` is a homogeneous multiple of `f`
        (∃ k : ℕ, 1 ≤ k ∧ ∃ a : A, SetLike.IsHomogeneousElem 𝒜 a ∧ g ^ k = a * f) ∧
        -- (c) the canonical, and only, `A`-algebra map `A[1/f] → A[1/g]`
        ((∀ x : A,
            ProjectiveSpectrum.localizedRingMap 𝒜 f g ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg
                (algebraMap A (Localization.Away f) x) = algebraMap A (Localization.Away g) x) ∧
          Subsingleton (Localization.Away f →ₐ[A] Localization.Away g)) ∧
        -- (d) the canonical `𝒜 0`-algebra map `A₍f₎ → A₍g₎`, compatible with the map of (c),
        -- and the only `𝒜 0`-algebra map compatible with it
        ((∀ x : Away 𝒜 f,
            (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg x).val =
              ProjectiveSpectrum.localizedRingMap 𝒜 f g ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg x.val) ∧
          ∀ ψ : Away 𝒜 f →ₐ[𝒜 0] Away 𝒜 g,
            (∀ x : Away 𝒜 f, (ψ x).val =
              ProjectiveSpectrum.localizedRingMap 𝒜 f g ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg x.val) →
            ψ = ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg) ∧
        -- (e) that map exhibits `A₍g₎` as `A₍f₎` localized at `g ^ deg f / f ^ deg g`
        (letI : Algebra (Away 𝒜 f) (Away 𝒜 g) :=
          (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g
            ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).toRingHom.toAlgebra
         IsLocalization.Away
           (Away.mk 𝒜 hfd e (g ^ d) (by simpa [mul_comm] using SetLike.pow_mem_graded d hge))
           (Away 𝒜 g)) ∧
        -- (f) the commutative diagram of topological spaces, with horizontal arrows
        -- homeomorphisms and vertical arrows open immersions
        (letI := gradedRingTwistAway 𝒜 hfd
         letI := gradedRingTwistAway 𝒜 hge
         IsHomeomorph (gradedPrimeToBasicOpen 𝒜 hge he) ∧
           IsHomeomorph (gradedPrimesAwayToSpec 𝒜 hge) ∧
           IsHomeomorph (gradedPrimeToBasicOpen 𝒜 hfd hd) ∧
           IsHomeomorph (gradedPrimesAwayToSpec 𝒜 hfd) ∧
           Topology.IsOpenEmbedding (basicOpenInclusion 𝒜 hfg) ∧
           Topology.IsOpenEmbedding
             (gradedPrimesVertical 𝒜 hfd hge ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg) ∧
           Topology.IsOpenEmbedding (specDegreeZeroVertical 𝒜 f g d e hd he hfd hge hfg) ∧
           (∀ q : gradedPrimes (twistAway 𝒜 g e),
             basicOpenInclusion 𝒜 hfg (gradedPrimeToBasicOpen 𝒜 hge he q) =
               gradedPrimeToBasicOpen 𝒜 hfd hd
                 (gradedPrimesVertical 𝒜 hfd hge ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg q)) ∧
           (∀ q : gradedPrimes (twistAway 𝒜 g e),
             specDegreeZeroVertical 𝒜 f g d e hd he hfd hge hfg
                 (gradedPrimesAwayToSpec 𝒜 hge q) =
               gradedPrimesAwayToSpec 𝒜 hfd
                 (gradedPrimesVertical 𝒜 hfd hge ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg q))) ∧
        -- (g) and (h), for an arbitrary graded `A`-module `M`
        (∀ {M : Type w} {τ : Type t} [AddCommGroup M] [Module A M] [SetLike τ M]
            [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
            [SetLike.GradedSMul 𝒜 𝒨],
          -- (g) compatible maps `M_f → M_g` and `M₍f₎ → M₍g₎`, induced by the identity of `M`,
          -- each the only such map
          ((∀ m : M,
              (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
                    ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).localizedMap
                  (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
                LocalizedModule.mkLinearMap (Submonoid.powers g) M m) ∧
            (∀ x : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f,
              (((ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
                      ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).degreeZeroMap x :
                    GradedModuleDegreeZeroLocalization 𝒜 𝒨 g) :
                  LocalizedModule.Away (R := A) g M) =
                (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
                  ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).localizedMap x) ∧
            (∀ L :
                letI := Module.compHom (R := Localization.Away g) (S := Localization.Away f)
                  (LocalizedModule.Away (R := A) g M)
                  (ProjectiveSpectrum.localizedRingMap 𝒜 f g
                    ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).toRingHom
                LocalizedModule.Away (R := A) f M →ₗ[Localization.Away f]
                  LocalizedModule.Away (R := A) g M,
              (∀ m : M, L (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) =
                LocalizedModule.mkLinearMap (Submonoid.powers g) M m) →
              L = (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
                ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).localizedMap) ∧
            (∀ N :
                letI := Module.compHom (R := Localization.Away f)
                  (LocalizedModule.Away (R := A) f M)
                  (algebraMap (Away 𝒜 f) (Localization.Away f))
                letI := Module.compHom (R := Localization.Away g)
                  (LocalizedModule.Away (R := A) g M)
                  (algebraMap (Away 𝒜 g) (Localization.Away g))
                letI := Module.compHom (R := Away 𝒜 g)
                  (GradedModuleDegreeZeroLocalization 𝒜 𝒨 g)
                  (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g
                    ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).toRingHom
                GradedModuleDegreeZeroLocalization 𝒜 𝒨 f →ₗ[Away 𝒜 f]
                  GradedModuleDegreeZeroLocalization 𝒜 𝒨 g,
              (∀ x : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f,
                (N x : LocalizedModule.Away (R := A) g M) =
                  (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
                    ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).localizedMap x) →
              N = (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
                ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).degreeZeroMap)) ∧
          -- (h) `M₍g₎` is `M₍f₎` localized at `g ^ deg f / f ^ deg g`
          (letI : Algebra (Away 𝒜 f) (Away 𝒜 g) :=
             (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g
               ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).toRingHom.toAlgebra
           letI := Module.compHom (R := Away 𝒜 g)
             (GradedModuleDegreeZeroLocalization 𝒜 𝒨 g)
             (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g
               ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).toRingHom
           IsLocalizedModule
             (Submonoid.powers
               (Away.mk 𝒜 hfd e (g ^ d) (by simpa [mul_comm] using SetLike.pow_mem_graded d hge)))
             (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
               ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).degreeZeroMap))) ∧
    -- part (2)
    (∀ {ι : Type s} (U : ι → TopologicalSpace.Opens (ProjectiveSpectrum 𝒜)),
        ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⨆ i, U i →
        ∃ (n : ℕ) (g : Fin n → A) (e : Fin n → ℕ),
          (∀ i, 0 < e i ∧ g i ∈ 𝒜 (e i)) ∧
          ProjectiveSpectrum.basicOpen 𝒜 f = ⨆ i, ProjectiveSpectrum.basicOpen 𝒜 (g i) ∧
          ∀ i, ∃ j, ProjectiveSpectrum.basicOpen 𝒜 (g i) ≤ U j) ∧
    -- part (3)
    (∀ {ι : Type s'} (g : ι → A) (e : ι → ℕ) (hg : ∀ i, g i ∈ 𝒜 (e i)) (_he : ∀ i, 0 < e i),
        AlgebraicGeometry.Proj.basicOpen 𝒜 f ≤ ⨆ i, AlgebraicGeometry.Proj.basicOpen 𝒜 (g i) ↔
          Ideal.span (Set.range fun i => Away.isLocalizationElem hfd (hg i)) = ⊤) :=
  ⟨fun g e hge he hfg =>
      ⟨⟨ProjectiveSpectrum.isUnit_algebraMap_away_of_basicOpen_le 𝒜 hfd hd hge he hfg,
          ProjectiveSpectrum.isUnit_isLocalizationElem_of_basicOpen_le 𝒜 hfd hd hge he hfg⟩,
        ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le 𝒜 hfd hd hge he hfg,
        ⟨fun x =>
            (ProjectiveSpectrum.localizedRingMap 𝒜 f g ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).commutes x,
          ⟨fun ψ χ => Localization.algHom_ext _
            (AlgHom.ext fun x => (ψ.commutes x).trans (χ.commutes x).symm)⟩⟩,
        ⟨ProjectiveSpectrum.val_degreeZeroRingMap 𝒜 f g ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg,
          fun ψ hψ => AlgHom.ext fun x => HomogeneousLocalization.val_injective _
            ((hψ x).trans (ProjectiveSpectrum.val_degreeZeroRingMap 𝒜 f g
              ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg x).symm)⟩,
        ProjectiveSpectrum.isLocalizationAway_degreeZeroRingMap 𝒜 f g d e hd he hfd hge hfg,
        (by
          let := gradedRingTwistAway 𝒜 hfd
          let := gradedRingTwistAway 𝒜 hge
          exact topologicalDiagram 𝒜 hfd hd hge he ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg),
        fun 𝒨 =>
          ⟨⟨(ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
                ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).map_mk,
              (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
                ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).degreeZeroMap_val,
              fun L hL => (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
                ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).localizedMap_unique L hL,
              fun N hN => (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
                ⟨d, hd, hfd⟩ ⟨e, he, hge⟩ hfg).degreeZeroMap_unique N hN⟩,
            ProjectiveSpectrum.isLocalizedModule_degreeZeroMap 𝒜 𝒨 f g d e hd he hfd hge hfg⟩⟩,
    fun U hU => ProjectiveSpectrum.exists_finite_basicOpen_refinement 𝒜 hfd hd U hU,
    fun g e hg he =>
      AlgebraicGeometry.Proj.basicOpen_le_iSup_iff_span_isLocalizationElem_eq_top 𝒜 hfd hd g e
        hg he⟩

end Stacks.ProjStandardOpenStatement

end
