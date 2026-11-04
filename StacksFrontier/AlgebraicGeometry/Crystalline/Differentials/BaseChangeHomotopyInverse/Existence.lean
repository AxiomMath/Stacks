module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChange
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChangeHomotopyInverse.HomotopyCalculus

/-!
# A homotopy inverse up to `a` for the base change map of de Rham complexes

Let `B → B'` be a ring map sitting in a commutative square over `A → A'`, let `Ω_{B/A} → Ω`
and `Ω_{B'/A'} → Ω'` be quotients to which the de Rham differential descends, and let
`ψ : Ω → Ω'` be a compatible map, so that a `B`-module `M` with an integrable connection
`∇ : M → M ⊗_B Ω` has a base change `(M ⊗_B B', ∇')` and there is a canonical map of de Rham
complexes

`c_M^• : M ⊗_B Ω^• ⟶ M ⊗_B (Ω')^•`.

Assume further given `a ∈ B`, `z ∈ B'` and a `B`-linear `θ : B' → B'` subject to the seven
standing assumptions: `d(a) = 0`; `Ω' = (B' ⊗_B Ω) ⊕ B' dz`, which lets one write
`d(f) = d₁(f) + ∂_z(f) dz`; `θ` is `B`-linear; `∂_z ∘ θ` is multiplication by `a`; `B → B'` is
universally injective; `a f - θ(∂_z(f)) ∈ B` for all `f ∈ B'`; and
`(θ ⊗ 1)(d₁(f)) - d₁(θ(f)) ∈ Ω` for all `f ∈ B'`. In this situation there is a map of
complexes `e_M^• : M ⊗_B (Ω')^• ⟶ M ⊗_B Ω^•` such that both `c_M^• ∘ e_M^•` and
`e_M^• ∘ c_M^•` are homotopic to multiplication by `a`.

## Main definitions

* `Crystalline.DzDecomposition` — the decomposition `Ω' = (B' ⊗_B Ω) ⊕ B' dz` of the one-forms
  of `B'` into the base change of the one-forms of `B` and the free rank-one piece spanned by
  `dz`, with the two summand inclusions pinned down to be the canonical ones.
* `Crystalline.DzDecomposition.dOne` and `Crystalline.DzDecomposition.partialZ` — the two
  components `d₁(f)` and `∂_z(f)` of `d(f)` with respect to that decomposition.

## Main results

* `Crystalline.exists_homotopyInverse_baseChangeDeRhamMap` — existence of `e_M^•` together
  with the two homotopies.

## Implementation notes

The ambient situation, the instance assumptions and the presentation of the two complexes are
those of the canonical base-change map of de Rham complexes, so that its map `c_M^•` can be
used directly. In particular the degree-`p` terms are `M ⊗_B Ω^p = M ⊗[B] ⋀[B]^p Ω` and
`(M ⊗_B B') ⊗_{B'} (Ω')^p = (B' ⊗[B] M) ⊗[B'] ⋀[B']^p Ω'`, read as `A`-modules by restriction
of scalars, since the de Rham differentials are only `A`-linear; and the differentials are
those of the canonical extensions `Crystalline.extendedConnection` of `∇` and of its base
change `Crystalline.Connection.baseChange`.

The map `c_M^•` is taken as a hypothesis, pinned down by the two properties that
`Crystalline.existsUnique_baseChangeDeRhamMap` shows determine it uniquely — its value on pure
wedges and its commuting with the differentials. This is not a weakening: by that uniqueness
there is exactly one such family, so the statement quantifies over a single map.

Assumption (2) is the structure `DzDecomposition`: a `B'`-linear isomorphism
`(B' ⊗_B Ω) × B' ≃ Ω'` whose restriction to the first summand is the canonical map
`b' ⊗ ω ↦ b' ψ(ω)` and whose restriction to the second is `c ↦ c dz`, with `dz = d z`. Those
two equations pin the isomorphism down, so giving the structure is exactly giving the direct
sum decomposition of the source. `dOne` and `partialZ` are then *defined* as the two components
of `d f`, which is `d(f) = d₁(f) + ∂_z(f) dz`; no further hypothesis is needed to introduce
them.

`B`-linearity of `θ` is carried by the type `B' →ₗ[B] B'` rather than by a separate hypothesis.
In the last two assumptions the memberships "`∈ B`" and "`∈ Ω`" are membership in the image of
`B → B'`, respectively in the image of the canonical `Ω → B' ⊗_B Ω`, `ω ↦ 1 ⊗ ω`; and `θ ⊗ 1`
is `TensorProduct.map θ id`.

`UniversallyInjective` quantifies over the `B`-modules of one universe, given as its first
explicit universe argument; it is assumed only for the universe of the terms
`M ⊗_B Ω^p` of the source complex, where the proof uses it (to see that `c_M^•` is injective).
Assuming it only there rather than in every universe keeps the hypothesis as weak as the proof
needs.

The mathematics here puts no constraint on universes, and the statement would be happier with
seven independent ones. Three is what the surrounding API permits: `SourceDeRham` is declared
as `SourceDeRham (A B : Type u)`, which identifies the universes of `A` and `B`, and
`SourceDeRham.targetD`, `SourceDeRham.GenerationHypothesis` and
`SourceDeRham.SatisfiesRule` are all stated for `Ω : Type u` in that same universe, which
identifies the universe of the one-forms with it as well. `Crystalline.extendedConnection` and
`Crystalline.Connection.baseChange` repeat the identification, the latter over
`{A B Omega : Type u} {A' B' Omega' : Type u'} {M : Type w}`. So `u` for the base data, `u'` for
the primed data and `w` for the module `M` is the maximal generality available without first
re-universe-polymorphising that API; `M` is kept independent because nothing forces it.

"Map of complexes" and "homotopic" are spelled out degreewise: the two complexes are families
of `A`-linear maps with vanishing consecutive composites, not `HomologicalComplex` objects, so
a chain map is a degreewise family commuting with the differentials and a homotopy is a
degreewise family `h^p : (Ω')^p → (Ω')^{p-1}` with `d ∘ h + h ∘ d` equal to the difference of
the two maps. The degree-`0` instance of that identity is stated separately because `h^0 = 0`
there is forced, the target of `h^0` being zero.

Multiplication by `a` on a term of either complex is `RestrictScalars.lsmul`, the `A`-linear
endomorphism given by the action of the original coefficient ring, rather than `a • ·`: the
terms carry the `A`-action coming from `RestrictScalars` and not the `B`- or `B'`-action, which
is only available through that algebra map. The base-changed differential is used on terms
written with `RestrictScalars A B'`, the form in which `c_M^•` lands, rather than as the
`A'`-linear map it is on the nose; these have the same underlying abelian groups.

## References

* [Stacks Project, Tag 07Q1](https://stacks.math.columbia.edu/tag/07Q1)
* [Stacks Project, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
-/

@[expose] public section

open scoped TensorProduct DirectSum


universe u u' w

namespace Crystalline

open Stacks.DeRham.DifferentialDescent


variable {A B Omega : Type u} {A' B' Omega' : Type u'} {M : Type w}
variable
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
  [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup Omega'] [Module B' Omega']
  [AddCommGroup M] [Module B M]


/-- **Stacks 07Q7 (Lemma 60.25.1).** In the situation of Section 60.25 — a commutative square
`B → B'` over `A → A'`, quotients `Ω_{B/A} → Ω` and `Ω_{B'/A'} → Ω'` to which the de Rham
differential descends, a compatible `ψ : Ω → Ω'`, a `B`-module `M` with integrable connection
`∇`, the canonical map of complexes `c_M^•` of equation 07PY, and data `a ∈ B`, `z ∈ B'`,
`θ : B' → B'` satisfying assumptions (1)–(7) — there exists a map of complexes

`e_M^• : M ⊗_B (Ω')^• ⟶ M ⊗_B Ω^•`

such that `c_M^• ∘ e_M^•` and `e_M^• ∘ c_M^•` are homotopic to multiplication by `a`. -/
@[stacks 07Q7 "with the B-linearity of the reverse map e and of the homotopy h, which the \
p-adically completed form of Tag 07N1 needs"]
public theorem exists_homotopyInverse_baseChangeDeRhamMap_baseLinear
    (S : SourceDeRham A B) (S' : SourceDeRham A' B')
    (pi : Ω[B⁄A] →ₗ[B] Omega) (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (hpi' : Function.Surjective pi') (hgen' : S'.GenerationHypothesis pi')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega')
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
    (nabla : Connection A B pi M)
    (hintegrable : Connection.IsIntegrable S pi hpi hgen nabla)
    (c : ∀ p : ℕ,
      RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
        RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))
    (hc_wedge : ∀ (p : ℕ) (m : M) (omega : Fin p → Omega),
      c p (m ⊗ₜ[B] exteriorPower.ιMulti B p omega) =
        (1 ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ omega))
    (hc_comm : ∀ (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)),
      c (p + 1)
          ((extendedConnection S pi hpi hgen nabla).toLinearMap p x) =
        (extendedConnection S' pi' hpi' hgen'
          (Connection.baseChange psi nabla hpsi)).toLinearMap p (c p x))
    (a : B) (z : B') (theta : B' →ₗ[B] B')
    (dec : DzDecomposition pi' psi z)
    (hd_a_eq_zero : SourceDeRham.targetD pi a = 0)
    (hpartialZ_theta : ∀ f : B', dec.partialZ (theta f) = a • f)
    (huniv :
      Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{max u w}
        (Algebra.linearMap B B'))
    (hepsilon : ∀ f : B',
      a • f - theta (dec.partialZ f) ∈ Set.range (algebraMap B B'))
    (hepsilonPrime : ∀ f : B',
      TensorProduct.map theta (LinearMap.id (R := B) (M := Omega)) (dec.dOne f) -
          dec.dOne (theta f) ∈
        LinearMap.range (TensorProduct.mk B B' Omega 1)) :
    ∃ e : ∀ p : ℕ,
      RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) →ₗ[A]
        RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)),
      (∀ (p : ℕ) (x : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))),
          e (p + 1)
              ((extendedConnection S' pi' hpi' hgen'
                (Connection.baseChange psi nabla hpsi)).toLinearMap
                p x) =
            (extendedConnection S pi hpi hgen nabla).toLinearMap
              p (e p x)) ∧
        (∀ (p : ℕ) (b : B) (y : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))),
            e p (RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
                (algebraMap B B' b) y) =
              RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^p Omega)) b (e p y)) ∧
        (∃ h : ∀ p : ℕ,
            RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega')) →ₗ[A]
              RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')),
          (∀ x : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^0 Omega')),
              h 0 ((extendedConnection S' pi' hpi' hgen'
                (Connection.baseChange psi nabla hpsi)).toLinearMap
                0 x) =
                RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^0 Omega'))
                    (algebraMap B B' a) x -
                  c 0 (e 0 x)) ∧
            (∀ (p : ℕ)
                (x : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))),
              (show RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega')) from
                (extendedConnection S' pi' hpi' hgen'
                  (Connection.baseChange psi nabla hpsi)).toLinearMap
                    p (h p x)) +
                  h (p + 1)
                    ((extendedConnection S' pi' hpi' hgen'
                      (Connection.baseChange psi nabla hpsi)).toLinearMap
                      (p + 1) x) =
                RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
                    (algebraMap B B' a) x -
                  c (p + 1) (e (p + 1) x)) ∧
            (∀ (p : ℕ) (b : B)
                (y : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))),
              h p (RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
                  (algebraMap B B' b) y) =
                RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
                  (algebraMap B B' b) (h p y))) ∧
        (∃ k : ∀ p : ℕ,
            RestrictScalars A B (M ⊗[B] (⋀[B]^(p + 1) Omega)) →ₗ[A]
              RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)),
          (∀ x : RestrictScalars A B (M ⊗[B] (⋀[B]^0 Omega)),
              k 0 ((extendedConnection S pi hpi hgen nabla).toLinearMap
                0 x) =
                RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^0 Omega)) a x - e 0 (c 0 x)) ∧
            (∀ (p : ℕ) (x : RestrictScalars A B (M ⊗[B] (⋀[B]^(p + 1) Omega))),
              (extendedConnection S pi hpi hgen nabla).toLinearMap
                  p (k p x) +
                k (p + 1)
                  ((extendedConnection S pi hpi hgen nabla).toLinearMap
                    (p + 1) x) =
                RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^(p + 1) Omega)) a x -
                  e (p + 1) (c (p + 1) x)) ∧
            (∀ (p : ℕ) (b : B) (x : RestrictScalars A B (M ⊗[B] (⋀[B]^(p + 1) Omega))),
              k p (RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^(p + 1) Omega)) b x) =
                RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^p Omega)) b (k p x))) := by
  classical
  have hc_injective : ∀ p, Function.Injective (c p) := fun p =>
    baseChangeMap_injective pi' psi z dec huniv p (c p) (hc_wedge p)
  let h := integratingHomotopy (A := A) (M := M) pi' psi z dec theta
  let X : ℕ → Type _ := fun p => RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega))
  let Y : ℕ → Type _ := fun p =>
    RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
  let xGroup : ∀ p, AddCommGroup (X p) := fun p =>
    inferInstanceAs (AddCommGroup (RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega))))
  let xModule : ∀ p, Module A (X p) := fun p =>
    inferInstanceAs (Module A (RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega))))
  let yGroup : ∀ p, AddCommGroup (Y p) := fun p =>
    inferInstanceAs (AddCommGroup
      (RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))))
  let yModule : ∀ p, Module A (Y p) := fun p =>
    inferInstanceAs (Module A
      (RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))))
  let dX : ∀ p, X p →ₗ[A] X (p + 1) :=
    (extendedConnection S pi hpi hgen nabla).toLinearMap
  let nabla' := Connection.baseChange psi nabla hpsi
  let dY : ∀ p, Y p →ₗ[A] Y (p + 1) := fun p =>
    restrictLinearMapTower A A' B'
      (X := (B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
      (Y := (B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
      ((extendedConnection S' pi' hpi' hgen' nabla').toLinearMap p)
  let s : ∀ p, Y p →ₗ[A] Y p := fun p =>
    RestrictScalars.lsmul A B' _ (algebraMap B B' a)
  let t : ∀ p, X p →ₗ[A] X p := fun p => RestrictScalars.lsmul A B _ a
  let g : ∀ p, Y p →ₗ[A] Y p := @cartanRemainder A _ Y yGroup yModule dY h s
  have hc_base (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)) :
      c p x = baseTerm pi' psi z dec p 1 x :=
    baseChangeMap_eq_coefficientInclusion pi' psi z dec p (c p) (hc_wedge p) x
  have hrange : ∀ p y, g p y ∈ LinearMap.range (c p) :=
    cartanRemainder_mem_range S S' pi pi' hpi hgen hpi' hgen' psi hpsi nabla c hc_wedge
      hc_comm a z theta dec hpartialZ_theta hepsilon hepsilonPrime
  have hYzero : ∀ p, (dY (p + 1)).comp (dY p) = 0 := by
    intro p
    ext x
    exact LinearMap.congr_fun
      (extendedConnection_comp_self_eq_zero
        S' pi' hpi' hgen' nabla'
        (baseChange_isIntegrable S S' pi pi' hpi hgen hpi' hgen'
          psi hpsi nabla hintegrable) p) x
  have hd_a' : SourceDeRham.targetD pi' (algebraMap B B' a) = 0 := by
    show pi' (KaehlerDifferential.D A' B' (algebraMap B B' a)) = 0
    rw [← hpsi]
    show psi (SourceDeRham.targetD pi a) = 0
    rw [hd_a_eq_zero, map_zero]
  have hs : ∀ p x, dY p (s p x) = s (p + 1) (dY p x) := by
    intro p x
    show connectionDifferentialAddHom S' pi' hpi' hgen' nabla' p
        (algebraMap B B' a • (show (B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega') from x)) =
      algebraMap B B' a • connectionDifferentialAddHom S' pi' hpi' hgen' nabla' p x
    rw [extendedConnection_leibniz, hd_a', formWedge_zero, add_zero]
  have hc : ∀ p x, dY p (c p x) = c (p + 1) (dX p x) :=
    fun p x => (hc_comm p x).symm
  have hsc : ∀ p x, s p (c p x) = c p (t p x) := by
    intro p x
    exact (congrArg (s p) (hc_base p x)).trans
      ((baseTerm_smul_one pi' psi z dec p (algebraMap B B' a) x).symm.trans
        ((baseTerm_algebraMap pi' psi z dec p a x).trans (hc_base p (t p x)).symm))
  have hzero : ∀ p x, h p (c (p + 1) x) = 0 := by
    intro p x
    exact (congrArg (h p) (hc_base (p + 1) x)).trans
      (integratingHomotopyAddHom_base pi' psi z dec theta p 1 x)
  let sb : B → ∀ q, Y q →ₗ[A] Y q := fun b q =>
    RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^q Omega')) (algebraMap B B' b)
  let tb : B → ∀ q, X q →ₗ[A] X q := fun b q =>
    RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^q Omega)) b
  have hreverse : ∃ e : ∀ p, Y p →ₗ[A] X p,
      (∀ p y, dX p (e p y) = e (p + 1) (dY p y)) ∧
      (∀ p y, c p (e p y) = g p y) ∧
      (∀ p x, e p (c p x) = t p x) ∧
      (∀ (b : B) p y, e p (sb b p y) = tb b p (e p y)) :=
    @reverseChainMap_of_cartanRemainder A _ B X Y xGroup xModule yGroup yModule dX dY c h s t
      sb tb (fun b q y => formWedge q (psi (SourceDeRham.targetD pi b)) y)
      hYzero hs hc hsc hc_injective hrange hzero
      (fun b _ y => smul_comm (algebraMap B B' a) (algebraMap B B' b) y)
      (fun b q y => by
        show connectionDifferentialAddHom S' pi' hpi' hgen' nabla' q
            (algebraMap B B' b •
              (show (B' ⊗[B] M) ⊗[B'] (⋀[B']^q Omega') from y)) = _
        rw [extendedConnection_leibniz]
        exact congrArg
          (fun w => algebraMap B B' b •
              connectionDifferentialAddHom S' pi' hpi' hgen' nabla' q y + formWedge q w y)
          (hpsi b).symm)
      (fun b q y => integratingHomotopyAddHom_smul pi' psi z dec theta q b y)
      (fun b y => (anticommAddHom_zero_apply pi' psi z dec theta
            (SourceDeRham.targetD pi b) y).symm.trans
          (anticommAddHom_eq_zero pi' psi z dec theta (SourceDeRham.targetD pi b) 0 y))
      (fun b n y => (anticommAddHom_succ_apply pi' psi z dec theta
            (SourceDeRham.targetD pi b) n y).symm.trans
          (anticommAddHom_eq_zero pi' psi z dec theta
            (SourceDeRham.targetD pi b) (n + 1) y))
      (fun b q x => ((hc_base q (tb b q x)).trans
          (baseTerm_one_smul pi' psi z dec q b x)).trans
        (congrArg (fun w => algebraMap B B' b • w) (hc_base q x).symm))
  obtain ⟨e, hecomm, he, hec, hesm⟩ := hreverse
  refine ⟨e, (fun p x => (hecomm p x).symm), ?_, ⟨h, ?_, ?_, ?_⟩,
    ⟨fun _ => 0, ?_, ?_, ?_⟩⟩
  · exact fun q b y => hesm b q y
  · intro x
    have hx := he 0 x
    change c 0 (e 0 x) = s 0 x - h 0 (dY 0 x) at hx
    show h 0 (dY 0 x) = s 0 x - c 0 (e 0 x)
    rw [hx]
    abel
  · intro p x
    have hx := he (p + 1) x
    change c (p + 1) (e (p + 1) x) =
      s (p + 1) x - dY p (h p x) - h (p + 1) (dY (p + 1) x) at hx
    show dY p (h p x) + h (p + 1) (dY (p + 1) x) =
      s (p + 1) x - c (p + 1) (e (p + 1) x)
    rw [hx]
    abel
  · exact fun q b y => integratingHomotopyAddHom_smul pi' psi z dec theta q b y
  · intro x
    show 0 = t 0 x - e 0 (c 0 x)
    rw [hec, sub_self]
  · intro p x
    show dX p 0 + 0 = t (p + 1) x - e (p + 1) (c (p + 1) x)
    rw [hec, sub_self, map_zero, add_zero]
  · intro q b x
    exact (map_zero (RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^q Omega)) b)).symm

/-- Let `c_M^• : M ⊗_B Ω^• ⟶ (M ⊗_B B') ⊗_{B'} (Ω')^•` be the base change map of de Rham
complexes of a `B`-module `M` with integrable connection `∇`. Given `a ∈ B` with `d(a) = 0`, a
decomposition `Ω' = (B' ⊗_B Ω) ⊕ B' dz`, and a `B`-linear `θ : B' → B'` with `∂_z ∘ θ = a`,
`a f - θ(∂_z(f)) ∈ B` and `(θ ⊗ 1)(d₁(f)) - d₁(θ(f)) ∈ Ω` for all `f ∈ B'`, and with `B → B'`
universally injective, there is a map of complexes
`e_M^• : (M ⊗_B B') ⊗_{B'} (Ω')^• ⟶ M ⊗_B Ω^•` such that `c_M^• ∘ e_M^•` and `e_M^• ∘ c_M^•`
are both homotopic to multiplication by `a`. -/
@[stacks 07Q7]
public theorem exists_homotopyInverse_baseChangeDeRhamMap
    (S : SourceDeRham A B) (S' : SourceDeRham A' B')
    (pi : Ω[B⁄A] →ₗ[B] Omega) (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (hpi' : Function.Surjective pi') (hgen' : S'.GenerationHypothesis pi')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega')
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
    (nabla : Connection A B pi M)
    (hintegrable : Connection.IsIntegrable S pi hpi hgen nabla)
    (c : ∀ p : ℕ,
      RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
        RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))
    (hc_wedge : ∀ (p : ℕ) (m : M) (omega : Fin p → Omega),
      c p (m ⊗ₜ[B] exteriorPower.ιMulti B p omega) =
        (1 ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ omega))
    (hc_comm : ∀ (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)),
      c (p + 1)
          ((extendedConnection S pi hpi hgen nabla).toLinearMap p x) =
        (extendedConnection S' pi' hpi' hgen'
          (Connection.baseChange psi nabla hpsi)).toLinearMap p (c p x))
    (a : B) (z : B') (theta : B' →ₗ[B] B')
    (dec : DzDecomposition pi' psi z)
    (hd_a_eq_zero : SourceDeRham.targetD pi a = 0)
    (hpartialZ_theta : ∀ f : B', dec.partialZ (theta f) = a • f)
    (huniv :
      Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{max u w}
        (Algebra.linearMap B B'))
    (hepsilon : ∀ f : B',
      a • f - theta (dec.partialZ f) ∈ Set.range (algebraMap B B'))
    (hepsilonPrime : ∀ f : B',
      TensorProduct.map theta (LinearMap.id (R := B) (M := Omega)) (dec.dOne f) -
          dec.dOne (theta f) ∈
        LinearMap.range (TensorProduct.mk B B' Omega 1)) :
    ∃ e : ∀ p : ℕ,
      RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) →ₗ[A]
        RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)),
      (∀ (p : ℕ) (x : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))),
          e (p + 1)
              ((extendedConnection S' pi' hpi' hgen'
                (Connection.baseChange psi nabla hpsi)).toLinearMap
                p x) =
            (extendedConnection S pi hpi hgen nabla).toLinearMap
              p (e p x)) ∧
        (∃ h : ∀ p : ℕ,
            RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega')) →ₗ[A]
              RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')),
          (∀ x : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^0 Omega')),
              h 0 ((extendedConnection S' pi' hpi' hgen'
                (Connection.baseChange psi nabla hpsi)).toLinearMap
                0 x) =
                RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^0 Omega'))
                    (algebraMap B B' a) x -
                  c 0 (e 0 x)) ∧
            ∀ (p : ℕ)
                (x : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))),
              (show RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega')) from
                (extendedConnection S' pi' hpi' hgen'
                  (Connection.baseChange psi nabla hpsi)).toLinearMap
                    p (h p x)) +
                  h (p + 1)
                    ((extendedConnection S' pi' hpi' hgen'
                      (Connection.baseChange psi nabla hpsi)).toLinearMap
                      (p + 1) x) =
                RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
                    (algebraMap B B' a) x -
                  c (p + 1) (e (p + 1) x)) ∧
        (∃ k : ∀ p : ℕ,
            RestrictScalars A B (M ⊗[B] (⋀[B]^(p + 1) Omega)) →ₗ[A]
              RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)),
          (∀ x : RestrictScalars A B (M ⊗[B] (⋀[B]^0 Omega)),
              k 0 ((extendedConnection S pi hpi hgen nabla).toLinearMap
                0 x) =
                RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^0 Omega)) a x - e 0 (c 0 x)) ∧
            ∀ (p : ℕ) (x : RestrictScalars A B (M ⊗[B] (⋀[B]^(p + 1) Omega))),
              (extendedConnection S pi hpi hgen nabla).toLinearMap
                  p (k p x) +
                k (p + 1)
                  ((extendedConnection S pi hpi hgen nabla).toLinearMap
                    (p + 1) x) =
                RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^(p + 1) Omega)) a x -
                  e (p + 1) (c (p + 1) x)) :=
  Exists.elim (exists_homotopyInverse_baseChangeDeRhamMap_baseLinear S S' pi pi' hpi hgen hpi'
      hgen' psi hpsi nabla hintegrable c hc_wedge hc_comm a z theta dec hd_a_eq_zero
      hpartialZ_theta huniv hepsilon hepsilonPrime) fun e he ↦
    ⟨e, he.1, Exists.elim he.2.2.1 fun hm hh ↦ ⟨hm, hh.1, hh.2.1⟩,
      Exists.elim he.2.2.2 fun km hk ↦ ⟨km, hk.1, hk.2.1⟩⟩

end Crystalline

end

public section

open scoped TensorProduct

universe u u' w

namespace Crystalline

open Stacks.DeRham.DifferentialDescent

variable {A B Omega : Type u} {A' B' Omega' : Type u'} {M : Type w}
variable
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
  [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup Omega'] [Module B' Omega']
  [AddCommGroup M] [Module B M]

/-! ### The integrating homotopy, exposed

The homotopy `h` of the proof of Lemma 07Q7 is an explicit construction out of `θ` and the
decomposition `Ω' = (B' ⊗_B Ω) ⊕ B' dz`, and it does not involve the connection at all.  The
declarations below make it available by name, together with its values on the generators of the
target terms, its naturality in the module, the injectivity of `c_M^•`, and the form of Lemma
07Q7 in which `c_M^• ∘ e_M^•` is the Cartan remainder `a - d h - h d` of *this* homotopy.  That
form is what is needed when the lemma is applied to the members of an inverse system of
modules: the reverse maps it produces are then compatible with the transition maps, because
`c_M^•` is injective and everything else in the Cartan remainder is natural. -/

section IntegratingHomotopyExposed

variable (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
  (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
  (dec : DzDecomposition pi' psi z) (theta : B' →ₗ[B] B')

/-- **The integrating homotopy of the proof of Lemma 07Q7**, for a `B`-module `N`: on
`(B' ⊗_B N) ⊗_{B'} (Ω')^{p+1}` it extracts the coefficient of `dz` through the decomposition
`Ω' = (B' ⊗_B Ω) ⊕ B' dz` and applies `θ` to it.  It kills the terms with no `dz` and sends
`(f ⊗ m) ⊗ (dz ∧ ψ ω)` to `(θ f ⊗ m) ⊗ ψ ω`. -/
public noncomputable def integratingHomotopyMap (N : Type w) [AddCommGroup N] [Module B N]
    (p : ℕ) :
    RestrictScalars A B' ((B' ⊗[B] N) ⊗[B'] (⋀[B']^(p + 1) Omega')) →ₗ[A]
      RestrictScalars A B' ((B' ⊗[B] N) ⊗[B'] (⋀[B']^p Omega')) :=
  integratingHomotopy (A := A) (M := N) pi' psi z dec theta p

omit [SMulCommClass A' B B'] in
/-- The integrating homotopy kills a term with no `dz`. -/
public theorem integratingHomotopyMap_base (N : Type w) [AddCommGroup N] [Module B N] (p : ℕ)
    (f : B') (m : N) (v : Fin (p + 1) → Omega) :
    integratingHomotopyMap (A := A) pi' psi z dec theta N p
        ((f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' (p + 1) (psi ∘ v)) = 0 := by
  have h := integratingHomotopyAddHom_base (M := N) pi' psi z dec theta p f
    (m ⊗ₜ[B] exteriorPower.ιMulti B (p + 1) v)
  rw [baseTerm_tmul] at h
  exact h

omit [SMulCommClass A' B B'] in
/-- The integrating homotopy on a term with a `dz`: `(f ⊗ m) ⊗ (dz ∧ ψ ω) ↦ (θ f ⊗ m) ⊗ ψ ω`. -/
public theorem integratingHomotopyMap_dz (N : Type w) [AddCommGroup N] [Module B N] (p : ℕ)
    (f : B') (m : N) (v : Fin p → Omega) :
    integratingHomotopyMap (A := A) pi' psi z dec theta N p
        ((f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' (p + 1)
          (Fin.cons (SourceDeRham.targetD pi' z) (psi ∘ v))) =
      (theta f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ v) := by
  have h := integratingHomotopyAddHom_dz (M := N) pi' psi z dec theta p f
    (m ⊗ₜ[B] exteriorPower.ιMulti B p v)
  rw [baseTerm_tmul, formWedge_tmul, leftWedge_ιMulti, baseTerm_tmul] at h
  exact h

omit [SMulCommClass A' B B'] in
/-- **The integrating homotopy is natural in the module**: it commutes with the map induced by
any `B`-linear map `φ : N → N'` on the target terms. -/
public theorem integratingHomotopyMap_naturality {N N' : Type w} [AddCommGroup N] [Module B N]
    [AddCommGroup N'] [Module B N'] (φ : N →ₗ[B] N') (p : ℕ)
    (y : (B' ⊗[B] N) ⊗[B'] (⋀[B']^(p + 1) Omega')) :
    integratingHomotopyMap (A := A) pi' psi z dec theta N' p
        (TensorProduct.map (φ.baseChange B') LinearMap.id y) =
      TensorProduct.map (φ.baseChange B') LinearMap.id
        (integratingHomotopyMap (A := A) pi' psi z dec theta N p y) := by
  let F : ∀ q, (B' ⊗[B] N) ⊗[B'] (⋀[B']^q Omega') →ₗ[B']
      (B' ⊗[B] N') ⊗[B'] (⋀[B']^q Omega') := fun q =>
    TensorProduct.map (φ.baseChange B') LinearMap.id
  let H : ∀ q, AddSubgroup ((B' ⊗[B] N) ⊗[B'] (⋀[B']^q Omega')) := fun q =>
    match q with
    | 0 => ⊤
    | k + 1 =>
      { carrier := {y | integratingHomotopyAddHom (M := N') pi' psi z dec theta k (F (k + 1) y) =
          F k (integratingHomotopyAddHom (M := N) pi' psi z dec theta k y)}
        zero_mem' := by simp
        add_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
          rw [ha, hb]
        neg_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq, map_neg] at ha ⊢
          rw [ha] }
  have hall := tensorExterior_dz_induction (M := N) pi' psi z dec H
    (fun q f m v => by
      cases q with
      | zero => exact AddSubgroup.mem_top _
      | succ k =>
        show integratingHomotopyAddHom (M := N') pi' psi z dec theta k (F (k + 1) _) =
          F k (integratingHomotopyAddHom (M := N) pi' psi z dec theta k _)
        have h1 := integratingHomotopyMap_base (A := A) pi' psi z dec theta N k f m v
        have h2 := integratingHomotopyMap_base (A := A) pi' psi z dec theta N' k f (φ m) v
        simp only [F, TensorProduct.map_tmul, LinearMap.baseChange_tmul, LinearMap.id_apply]
        exact h2.trans ((congrArg (F k) h1).trans (map_zero (F k))).symm)
    (fun q f m v => by
      show integratingHomotopyAddHom (M := N') pi' psi z dec theta q (F (q + 1) _) =
        F q (integratingHomotopyAddHom (M := N) pi' psi z dec theta q _)
      have h1 : integratingHomotopyAddHom (M := N) pi' psi z dec theta q
          ((f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' (q + 1)
            (Fin.cons (SourceDeRham.targetD pi' z) (psi ∘ v))) =
          (theta f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' q (psi ∘ v) :=
        integratingHomotopyMap_dz (A := A) pi' psi z dec theta N q f m v
      have h2 : integratingHomotopyAddHom (M := N') pi' psi z dec theta q
          ((f ⊗ₜ[B] φ m) ⊗ₜ[B'] exteriorPower.ιMulti B' (q + 1)
            (Fin.cons (SourceDeRham.targetD pi' z) (psi ∘ v))) =
          (theta f ⊗ₜ[B] φ m) ⊗ₜ[B'] exteriorPower.ιMulti B' q (psi ∘ v) :=
        integratingHomotopyMap_dz (A := A) pi' psi z dec theta N' q f (φ m) v
      simp only [F, TensorProduct.map_tmul, LinearMap.baseChange_tmul, LinearMap.id_apply, h1,
        h2])
  exact hall (p + 1) y

omit [Algebra A A'] [IsScalarTower A B B'] [IsScalarTower A A' B'] in
omit [SMulCommClass A' B B'] in
include dec in
/-- **The canonical map `c_M^•` is injective** as soon as `B → B'` is universally injective and the
one-forms of `B'` decompose as `(B' ⊗_B Ω) ⊕ B' dz`. -/
public alias injective_of_dzDecomposition := baseChangeMap_injective

end IntegratingHomotopyExposed

/-- **Lemma 07Q7 with the homotopy on the target named.**  The hypotheses are those of
`Crystalline.exists_homotopyInverse_baseChangeDeRhamMap_baseLinear`.  The reverse map `e_M^•` is
a `B`-linear map of complexes with `e_M^• ∘ c_M^• = a` on the nose, and `c_M^• ∘ e_M^•` is
`a - d h - h d` for the integrating homotopy `h = Crystalline.integratingHomotopyMap` built from
`θ` and the decomposition, which is natural in `M` by
`Crystalline.integratingHomotopyMap_naturality`.  Since `c_M^•` is injective
(`Crystalline.injective_of_dzDecomposition`), these identities pin `e_M^•` down. -/
public theorem exists_homotopyInverse_baseChangeDeRhamMap_integrating
    (S : SourceDeRham A B) (S' : SourceDeRham A' B')
    (pi : Ω[B⁄A] →ₗ[B] Omega) (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (hpi' : Function.Surjective pi') (hgen' : S'.GenerationHypothesis pi')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega')
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
    (nabla : Connection A B pi M)
    (hintegrable : Connection.IsIntegrable S pi hpi hgen nabla)
    (c : ∀ p : ℕ,
      RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
        RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))
    (hc_wedge : ∀ (p : ℕ) (m : M) (omega : Fin p → Omega),
      c p (m ⊗ₜ[B] exteriorPower.ιMulti B p omega) =
        (1 ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ omega))
    (hc_comm : ∀ (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)),
      c (p + 1)
          ((extendedConnection S pi hpi hgen nabla).toLinearMap p x) =
        (extendedConnection S' pi' hpi' hgen'
          (Connection.baseChange psi nabla hpsi)).toLinearMap p (c p x))
    (a : B) (z : B') (theta : B' →ₗ[B] B')
    (dec : DzDecomposition pi' psi z)
    (hd_a_eq_zero : SourceDeRham.targetD pi a = 0)
    (hpartialZ_theta : ∀ f : B', dec.partialZ (theta f) = a • f)
    (huniv :
      Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{max u w}
        (Algebra.linearMap B B'))
    (hepsilon : ∀ f : B',
      a • f - theta (dec.partialZ f) ∈ Set.range (algebraMap B B'))
    (hepsilonPrime : ∀ f : B',
      TensorProduct.map theta (LinearMap.id (R := B) (M := Omega)) (dec.dOne f) -
          dec.dOne (theta f) ∈
        LinearMap.range (TensorProduct.mk B B' Omega 1)) :
    ∃ e : ∀ p : ℕ,
      RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) →ₗ[A]
        RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)),
      (∀ (p : ℕ) (x : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))),
          e (p + 1)
              ((extendedConnection S' pi' hpi' hgen'
                (Connection.baseChange psi nabla hpsi)).toLinearMap
                p x) =
            (extendedConnection S pi hpi hgen nabla).toLinearMap
              p (e p x)) ∧
        (∀ (p : ℕ) (b : B) (y : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))),
            e p (RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
                (algebraMap B B' b) y) =
              RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^p Omega)) b (e p y)) ∧
        (∀ (p : ℕ) (x : RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega))),
            e p (c p x) = RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^p Omega)) a x) ∧
        (∀ x : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^0 Omega')),
            integratingHomotopyMap (A := A) pi' psi z dec theta M 0
                ((extendedConnection S' pi' hpi' hgen'
                  (Connection.baseChange psi nabla hpsi)).toLinearMap 0 x) =
              RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^0 Omega'))
                  (algebraMap B B' a) x -
                c 0 (e 0 x)) ∧
        ∀ (p : ℕ) (x : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))),
          (show RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega')) from
            (extendedConnection S' pi' hpi' hgen'
              (Connection.baseChange psi nabla hpsi)).toLinearMap
                p (integratingHomotopyMap (A := A) pi' psi z dec theta M p x)) +
              integratingHomotopyMap (A := A) pi' psi z dec theta M (p + 1)
                ((extendedConnection S' pi' hpi' hgen'
                  (Connection.baseChange psi nabla hpsi)).toLinearMap
                  (p + 1) x) =
            RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
                (algebraMap B B' a) x -
              c (p + 1) (e (p + 1) x) := by
  classical
  have hc_injective : ∀ p, Function.Injective (c p) := fun p =>
    baseChangeMap_injective pi' psi z dec huniv p (c p) (hc_wedge p)
  let h := integratingHomotopy (A := A) (M := M) pi' psi z dec theta
  let X : ℕ → Type _ := fun p => RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega))
  let Y : ℕ → Type _ := fun p =>
    RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
  let xGroup : ∀ p, AddCommGroup (X p) := fun p =>
    inferInstanceAs (AddCommGroup (RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega))))
  let xModule : ∀ p, Module A (X p) := fun p =>
    inferInstanceAs (Module A (RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega))))
  let yGroup : ∀ p, AddCommGroup (Y p) := fun p =>
    inferInstanceAs (AddCommGroup
      (RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))))
  let yModule : ∀ p, Module A (Y p) := fun p =>
    inferInstanceAs (Module A
      (RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))))
  let dX : ∀ p, X p →ₗ[A] X (p + 1) :=
    (extendedConnection S pi hpi hgen nabla).toLinearMap
  let nabla' := Connection.baseChange psi nabla hpsi
  let dY : ∀ p, Y p →ₗ[A] Y (p + 1) := fun p =>
    restrictLinearMapTower A A' B'
      (X := (B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
      (Y := (B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
      ((extendedConnection S' pi' hpi' hgen' nabla').toLinearMap p)
  let s : ∀ p, Y p →ₗ[A] Y p := fun p =>
    RestrictScalars.lsmul A B' _ (algebraMap B B' a)
  let t : ∀ p, X p →ₗ[A] X p := fun p => RestrictScalars.lsmul A B _ a
  let g : ∀ p, Y p →ₗ[A] Y p := @cartanRemainder A _ Y yGroup yModule dY h s
  have hc_base (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)) :
      c p x = baseTerm pi' psi z dec p 1 x :=
    baseChangeMap_eq_coefficientInclusion pi' psi z dec p (c p) (hc_wedge p) x
  have hrange : ∀ p y, g p y ∈ LinearMap.range (c p) :=
    cartanRemainder_mem_range S S' pi pi' hpi hgen hpi' hgen' psi hpsi nabla c hc_wedge
      hc_comm a z theta dec hpartialZ_theta hepsilon hepsilonPrime
  have hYzero : ∀ p, (dY (p + 1)).comp (dY p) = 0 := by
    intro p
    ext x
    exact LinearMap.congr_fun
      (extendedConnection_comp_self_eq_zero
        S' pi' hpi' hgen' nabla'
        (baseChange_isIntegrable S S' pi pi' hpi hgen hpi' hgen'
          psi hpsi nabla hintegrable) p) x
  have hd_a' : SourceDeRham.targetD pi' (algebraMap B B' a) = 0 := by
    show pi' (KaehlerDifferential.D A' B' (algebraMap B B' a)) = 0
    rw [← hpsi]
    show psi (SourceDeRham.targetD pi a) = 0
    rw [hd_a_eq_zero, map_zero]
  have hs : ∀ p x, dY p (s p x) = s (p + 1) (dY p x) := by
    intro p x
    show connectionDifferentialAddHom S' pi' hpi' hgen' nabla' p
        (algebraMap B B' a • (show (B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega') from x)) =
      algebraMap B B' a • connectionDifferentialAddHom S' pi' hpi' hgen' nabla' p x
    rw [extendedConnection_leibniz, hd_a', formWedge_zero, add_zero]
  have hc : ∀ p x, dY p (c p x) = c (p + 1) (dX p x) :=
    fun p x => (hc_comm p x).symm
  have hsc : ∀ p x, s p (c p x) = c p (t p x) := by
    intro p x
    exact (congrArg (s p) (hc_base p x)).trans
      ((baseTerm_smul_one pi' psi z dec p (algebraMap B B' a) x).symm.trans
        ((baseTerm_algebraMap pi' psi z dec p a x).trans (hc_base p (t p x)).symm))
  have hzero : ∀ p x, h p (c (p + 1) x) = 0 := by
    intro p x
    exact (congrArg (h p) (hc_base (p + 1) x)).trans
      (integratingHomotopyAddHom_base pi' psi z dec theta p 1 x)
  let sb : B → ∀ q, Y q →ₗ[A] Y q := fun b q =>
    RestrictScalars.lsmul A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^q Omega')) (algebraMap B B' b)
  let tb : B → ∀ q, X q →ₗ[A] X q := fun b q =>
    RestrictScalars.lsmul A B (M ⊗[B] (⋀[B]^q Omega)) b
  have hreverse : ∃ e : ∀ p, Y p →ₗ[A] X p,
      (∀ p y, dX p (e p y) = e (p + 1) (dY p y)) ∧
      (∀ p y, c p (e p y) = g p y) ∧
      (∀ p x, e p (c p x) = t p x) ∧
      (∀ (b : B) p y, e p (sb b p y) = tb b p (e p y)) :=
    @reverseChainMap_of_cartanRemainder A _ B X Y xGroup xModule yGroup yModule dX dY c h s t
      sb tb (fun b q y => formWedge q (psi (SourceDeRham.targetD pi b)) y)
      hYzero hs hc hsc hc_injective hrange hzero
      (fun b _ y => smul_comm (algebraMap B B' a) (algebraMap B B' b) y)
      (fun b q y => by
        show connectionDifferentialAddHom S' pi' hpi' hgen' nabla' q
            (algebraMap B B' b •
              (show (B' ⊗[B] M) ⊗[B'] (⋀[B']^q Omega') from y)) = _
        rw [extendedConnection_leibniz]
        exact congrArg
          (fun w => algebraMap B B' b •
              connectionDifferentialAddHom S' pi' hpi' hgen' nabla' q y + formWedge q w y)
          (hpsi b).symm)
      (fun b q y => integratingHomotopyAddHom_smul pi' psi z dec theta q b y)
      (fun b y => (anticommAddHom_zero_apply pi' psi z dec theta
            (SourceDeRham.targetD pi b) y).symm.trans
          (anticommAddHom_eq_zero pi' psi z dec theta (SourceDeRham.targetD pi b) 0 y))
      (fun b n y => (anticommAddHom_succ_apply pi' psi z dec theta
            (SourceDeRham.targetD pi b) n y).symm.trans
          (anticommAddHom_eq_zero pi' psi z dec theta
            (SourceDeRham.targetD pi b) (n + 1) y))
      (fun b q x => ((hc_base q (tb b q x)).trans
          (baseTerm_one_smul pi' psi z dec q b x)).trans
        (congrArg (fun w => algebraMap B B' b • w) (hc_base q x).symm))
  obtain ⟨e, hecomm, he, hec, hesm⟩ := hreverse
  refine ⟨e, (fun p x => (hecomm p x).symm), (fun q b y => hesm b q y), hec, ?_, ?_⟩
  · intro x
    have hx := he 0 x
    change c 0 (e 0 x) = s 0 x - h 0 (dY 0 x) at hx
    show h 0 (dY 0 x) = s 0 x - c 0 (e 0 x)
    rw [hx]
    abel
  · intro p x
    have hx := he (p + 1) x
    change c (p + 1) (e (p + 1) x) =
      s (p + 1) x - dY p (h p x) - h (p + 1) (dY (p + 1) x) at hx
    show dY p (h p x) + h (p + 1) (dY (p + 1) x) =
      s (p + 1) x - c (p + 1) (e (p + 1) x)
    rw [hx]
    abel

end Crystalline

end

add_to_stacks 07Q1 "the decomposition of one-forms" Crystalline.DzDecomposition
add_to_stacks 07Q1 "the component d_1 of the differential" Crystalline.DzDecomposition.dOne
add_to_stacks 07Q1 "the coefficient of dz in the differential"
  Crystalline.DzDecomposition.partialZ
add_to_stacks 07Q1 "the equation d(f) = d_1(f) + the coefficient of dz times dz"
  Crystalline.DzDecomposition.dOne_add_partialZ_smul
