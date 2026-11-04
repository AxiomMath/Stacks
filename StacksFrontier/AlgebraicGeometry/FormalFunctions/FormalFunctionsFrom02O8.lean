module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AdicCompletionLimitComparison
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyIdealPowerSystem

/-!
# The affine side of the theorem on formal functions, on Tag 02O8 alone

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` a proper morphism, `ℱ` a
coherent sheaf of modules on `X` and `p ≥ 0`. Write `𝓘 = I · 𝒪_X`.

Three links of the chain of the theorem on formal functions are already in the library, each
carrying the next one as a named hypothesis:

* [Stacks, Tag 02OA] — `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology`,
  granted [Stacks, Tag 02O8];
* [Stacks, Tag 02OB] —
  `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient`,
  granted [Stacks, Tag 02OA];
* [Stacks, Tag 02OC] — `Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv` and
  `formalFunctionsEquiv_proj_of`, granted [Stacks, Tag 02OB].

This file wires them together, so that the whole affine side of the theorem on formal functions
stands on the single hypothesis [Stacks, Tag 02O8]: the finiteness of `⨁ₙ Hᵖ(X, 𝓘ⁿℱ)` over the
Rees algebra `⨁ₙ Iⁿ`, carried in the general form in which
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology` consumes it.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.cohomologyBaseEquiv` — the identity map of `Hᵖ(X, ℱ)`, as
  an `A`-linear equivalence between the two `A`-module structures the library puts on it.

## Main results

* `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`
  — the three clauses of [Stacks, Tag 02OB], granted [Stacks, Tag 02O8].
* `Stacks.Cohomology.FormalFunctions.exists_formalFunctionsEquiv_of_02O8` — the comparison
  isomorphism of [Stacks, Tag 02OC], with its projection normalisation, granted
  [Stacks, Tag 02O8].

## Implementation notes

The conclusion of [Stacks, Tag 02OA] and the hypotheses of [Stacks, Tag 02OB] are the same
mathematics in four different spellings, and each identification is proved rather than assumed.

*The maps.* `cohomologyProj I (Over.mk f) ℱ p n` and
`cohomologyOverBaseMap A f p (idealPowerMultiple (baseIdealSheaf A I f) n ℱ).ι` are the same
function — `idealPowerSub I X ℱ n` is by definition `idealPowerMultiple (baseIdealSheaf A I
X.hom) n ℱ`, and both maps are the image of its inclusion under `Hᵖ`, read through a
restriction of scalars that changes neither types nor functions. Likewise
`cohomologyTr I (Over.mk f) ℱ p h` is `Hᵖ` of `idealPowerMultipleMap`, which is
`SheafOfModules.Submodule.homOfLE (idealPowerMultiple_antitone ..)`, and so is
`submoduleInclusion (idealPowerMultiple_antitone ..)`: the two are the same term, and every
identification of maps below is `rfl`.

*The scalars.* The two `A`-module structures on `Hᵖ(X, ℱ)` are **not** definitionally equal.
`cohomologyOverBase A f p ℱ` restricts scalars along `baseRingHom A f`, while
`cohomology (Over.mk f) ℱ p` is an object of `ModuleCat Γ(X, 𝒪_X)` read as an `A`-module
through `Stacks.Cohomology.AffineBase.baseSectionsAlgebra`, that is along
`AlgebraicGeometry.baseRingToSections A (Over.mk f) (op ⊤)`. Those two ring maps differ by
`X.presheaf.map` of the identity inclusion `⊤ ≤ ⊤`, so they are equal
(`baseRingToSections_op_top_eq_baseRingHom`) but only after `Functor.map_id`, which is not an
identity of terms for an abstract sheaf. The two `Module A` instances are therefore distinct
terms, the two `Submodule A` types are distinct, and clause (2) of [Stacks, Tag 02OA] — the only
clause that mentions `I ^ (r - c) • ⊤` — has to be transported. `cohomologyBaseEquiv` is that
transport: the identity map, `A`-linear because the two actions agree after the ring maps are
identified. Clause (3) needs no transport at all: it is an identity of kernels, and
`[Stacks, Tag 02OB]` states it over `Γ(X, 𝒪_X)`, where a kernel has the same carrier as the
kernel of the restriction of scalars.

*The index shift.* [Stacks, Tag 02OA] gives the kernel identity for all `m, k` with `m + c ≤ k`;
[Stacks, Tag 02OB] consumes it at `m = k - c`, where the two `≤` proofs differ and are
definitionally equal by proof irrelevance.

Quasi-coherence of `ℱ`, which [Stacks, Tag 02OC] needs, is not an extra hypothesis: it is
produced from coherence inside the proof, through the field-by-field identification of
`Stacks.SheafOfModules.IsCoherent` with the root-level `SheafOfModules.IsCoherent` and
`isQuasicoherent_of_isCoherent`.

## References

* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra

universe u

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Cohomology.AffineBase Stacks.Algebraization Stacks.IntertwinedFiltration

attribute [local instance] baseSectionsAlgebra

/-! ### The two `A`-module structures on the cohomology of `X` -/

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (F : X.Modules) (p : ℕ)

/-- The ring map `A ⟶ Γ(X, 𝒪_X)` along which a scheme over `Spec A` is an `A`-algebra is
`baseRingHom`: `AlgebraicGeometry.baseRingToSections` restricts a global function along the
inclusion `⊤ ≤ ⊤`, and that restriction is the identity. -/
public lemma baseRingToSections_op_top_eq_baseRingHom :
    (AlgebraicGeometry.baseRingToSections A (Over.mk f) (op ⊤) : A →+* Γ(X, ⊤)) =
      baseRingHom A f := by
  ext a
  show (X.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op).hom (baseRingHom A f a) =
    baseRingHom A f a
  rw [show (homOfLE (le_top (a := (⊤ : X.Opens)))).op = 𝟙 (op (⊤ : X.Opens)) from rfl,
    CategoryTheory.Functor.map_id]
  rfl

/-- **The two `A`-module structures on `Hᵖ(X, ℱ)` agree.** `cohomology (Over.mk f) ℱ p` is an
`A`-module through `baseSectionsAlgebra`, `cohomologyOverBase A f p ℱ` through restriction of
scalars along `baseRingHom A f`; the underlying type and addition are the same, and the two
actions agree because the two ring maps do. -/
public def cohomologyBaseEquiv :
    cohomology (Over.mk f) F p ≃ₗ[A] cohomologyOverBase A f p F where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' a x :=
    Eq.trans
      (show a • x = (baseRingHom A f a : Γ(X, ⊤)) • x from
        congrArg (fun r : Γ(X, ⊤) => r • x)
          (DFunLike.congr_fun (baseRingToSections_op_top_eq_baseRingHom A f) a))
      rfl
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

/-- `I ^ m · Hᵖ(X, ℱ)` for the `baseSectionsAlgebra` structure is carried into `I ^ m · Hᵖ(X, ℱ)`
for the `cohomologyOverBase` structure: the generators `a • x` agree by `cohomologyBaseEquiv`, so
the induction on membership in a product of an ideal and a submodule goes through. -/
public lemma mem_pow_smul_top_cohomologyOverBase (m : ℕ) (x : cohomology (Over.mk f) F p)
    (hx : x ∈ I ^ m • (⊤ : Submodule A (cohomology (Over.mk f) F p))) :
    cohomologyBaseEquiv A f F p x ∈
      I ^ m • (⊤ : Submodule A (cohomologyOverBase A f p F)) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) fun y z hy hz => ?_
  · rw [map_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [map_add]
    exact add_mem hy hz

/-! ### The clauses of [Stacks, Tag 02OA] in the shape [Stacks, Tag 02OB] consumes -/

/-- Clause (2) of [Stacks, Tag 02OA] at `n = 0`, moved to the `A`-module structure of
`cohomologyOverBase`. -/
public lemma range_cohomologyOverBaseMap_le_pow_smul_top {c k : ℕ}
    (himg : LinearMap.range (cohomologyProj I (Over.mk f) F p k) ≤
      I ^ (k - c) • (⊤ : Submodule A (cohomology (Over.mk f) F p))) :
    LinearMap.range (cohomologyOverBaseMap A f p
        (idealPowerMultiple (baseIdealSheaf A I f) k F).ι).hom ≤
      I ^ (k - c) • (⊤ : Submodule A (cohomologyOverBase A f p F)) := by
  rintro y ⟨z, rfl⟩
  exact mem_pow_smul_top_cohomologyOverBase A f I F p (k - c)
    (cohomologyProj I (Over.mk f) F p k z) (himg ⟨z, rfl⟩)

/-- Clause (3) of [Stacks, Tag 02OA], moved from the `A`-module structure to the
`Γ(X, 𝒪_X)`-module structure: restriction of scalars changes neither the maps nor their
kernels. -/
public lemma ker_cohomology_idealPowerMultiple_eq {q k m : ℕ} (h : m ≤ k)
    (hker : LinearMap.ker (cohomologyProj I (Over.mk f) F q k) =
      LinearMap.ker (cohomologyTr I (Over.mk f) F q h)) :
    LinearMap.ker (((moduleGlobalSections X).rightDerived q).map
        (idealPowerMultiple (baseIdealSheaf A I f) k F).ι).hom =
      LinearMap.ker (((moduleGlobalSections X).rightDerived q).map
        (submoduleInclusion (idealPowerMultiple_antitone (baseIdealSheaf A I f) F h))).hom :=
  Submodule.ext fun x =>
    Iff.trans (LinearMap.mem_ker (f := cohomologyProj I (Over.mk f) F q k) (y := x)).symm
      (Iff.trans (SetLike.ext_iff.1 hker x)
        (LinearMap.mem_ker (f := cohomologyTr I (Over.mk f) F q h) (y := x)))

/-! ### The wired statements -/

/-- **Stacks Project, Tag 02OB**, granted [Stacks, Tag 02O8].

This is `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient`
with its two hypotheses discharged by
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology`, applied in each degree `q`
and transported along the identifications described in the implementation notes of this file.
Nothing of the mathematics is new: the content is that the affine side of the theorem on formal
functions rests on [Stacks, Tag 02O8] alone, which is carried here as the hypothesis `h02O8` in
the same general form `exists_uniform_bound_cohomology` consumes it. -/
@[stacks 02OB "granted Tag 02O8, carried as the hypothesis h02O8"]
public theorem exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (hX : AlgebraicGeometry.IsProper f) (I : Ideal A) (F : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (p : ℕ)
    (h02O8 : ∀ (A' : Type u) [CommRing A'] [IsNoetherianRing A'] (I' : Ideal A')
      (X' : Over (Spec (.of A'))) (_ : AlgebraicGeometry.IsProper X'.hom)
      (F' : X'.left.Modules) (_ : SheafOfModules.IsCoherent F') (p' : ℕ),
      (cohomologyIdealPowerSystem I' X' F' p').IsReesFinite) :
    ∃ c : ℕ,
      (∀ n : ℕ, c ≤ n →
          LinearMap.ker (cohomologyOverBaseMap A f p
              (cokernel.π (C := X.Modules)
                (idealPowerMultiple (baseIdealSheaf A I f) n F).ι)).hom ≤
            I ^ (n - c) • (⊤ : Submodule A (cohomologyOverBase A f p F))) ∧
        IsMittagLefflerCategorical
          (adicQuotientSystem (baseIdealSheaf A I f) F ⋙
            (moduleGlobalSections X).rightDerived p) ∧
        ∀ n k : ℕ, (hk : n + c ≤ k) →
          LinearMap.range (((moduleGlobalSections X).rightDerived p).map
              (idealPowerQuotientDrop (baseIdealSheaf A I f)
                ((Nat.le_add_right n c).trans hk) F)).hom =
            LinearMap.range (((moduleGlobalSections X).rightDerived p).map
              (cokernel.π (C := X.Modules)
                (idealPowerMultiple (baseIdealSheaf A I f) n F).ι)).hom :=
  have key := fun q => exists_uniform_bound_cohomology I (Over.mk f) F hX hF q h02O8
  exists_uniform_bound_cohomology_idealPowerQuotient A f I F p
    (fun q => (key q).imp fun _ h k hk =>
      range_cohomologyOverBaseMap_le_pow_smul_top A f I F q (h.1 k hk))
    (fun q => (key q).imp fun c h k hk =>
      ker_cohomology_idealPowerMultiple_eq A f I F (Nat.sub_le k c) (h.2 (k - c) k (by omega)))

/-- **Stacks Project, Tag 02OC**, granted [Stacks, Tag 02O8], and for the `A`-module
isomorphism only.

With `𝓘 = I · 𝒪_X`, the `I`-adic completion of `Hᵖ(X, ℱ)` is the limit of the tower
`n ↦ Hᵖ(X, ℱ / 𝓘ⁿℱ)`, by *the* comparison map: the projection normalisation says that the
`n`-th component of the equivalence carries the image of a class `x ∈ Hᵖ(X, ℱ)` to the image of
`x` in `Hᵖ(X, ℱ / 𝓘ⁿℱ)`. The constant `c` is existentially bound because
`Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv` is indexed by it.

[Stacks, Tag 02OC] further asserts that the comparison is a homeomorphism for the limit
topologies; that is **not** proved here, exactly as in
`Stacks.Cohomology.FormalFunctions.formalFunctionsEquiv`, and this statement does not claim it.

Quasi-coherence of `ℱ` is not assumed: it follows from `hF`. -/
@[stacks 02OC "granted Tag 02O8, carried as the hypothesis h02O8"]
public theorem exists_formalFunctionsEquiv_of_02O8
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (hX : AlgebraicGeometry.IsProper f) (I : Ideal A) (F : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (p : ℕ)
    (h02O8 : ∀ (A' : Type u) [CommRing A'] [IsNoetherianRing A'] (I' : Ideal A')
      (X' : Over (Spec (.of A'))) (_ : AlgebraicGeometry.IsProper X'.hom)
      (F' : X'.left.Modules) (_ : SheafOfModules.IsCoherent F') (p' : ℕ),
      (cohomologyIdealPowerSystem I' X' F' p').IsReesFinite) :
    ∃ (c : ℕ) (e : AdicCompletion I (cohomologyOverBase A f p F) ≃ₗ[A]
        towerLimit (adicCohomologyTower A f I F p) (adicCohomologyTowerMap A f I F p)),
      ∀ (n : ℕ) (x : cohomologyOverBase A f p F),
        towerLimit.proj n (e (AdicCompletion.of I (cohomologyOverBase A f p F) x)) =
          adicCohomologyProj A f I F p n x := by
  have : _root_.SheafOfModules.IsCoherent F := ⟨hF.1, hF.2⟩
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨c, hker, -, hrange⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 A f hX I F hF p h02O8
  exact ⟨c, formalFunctionsEquiv A f I F p c hker hrange,
    formalFunctionsEquiv_proj_of A f I F p c hker hrange⟩

end Stacks.Cohomology.FormalFunctions

end
