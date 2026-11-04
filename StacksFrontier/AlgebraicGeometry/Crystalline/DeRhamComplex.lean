module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymExtPowFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystallineDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureSheaf
public import StacksFrontier.RingTheory.DeRham.Complex

/-!
# The de Rham complex on the crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  The module of crystalline differentials
`Ω_{X/S}` of [Stacks, Tag 07IX] is a presheaf of modules over the structure presheaf of rings of
the crystalline category, and it carries the universal `S`-derivation `d_{X/S}`.  Its exterior
powers

`Ω^i_{X/S} = ⋀^i_{𝒪_{X/S}} Ω_{X/S}`, `i ≥ 0`,

are built here, both on the big crystalline category `CRIS(X/S)` and on the small crystalline
site `Cris(X/S)`, together with the exterior multiplication that makes them a graded algebra of
presheaves of modules, the identification of `Ω^0_{X/S}` with `𝒪_{X/S}` and of `Ω^1_{X/S}` with
`Ω_{X/S}`.

The universal `S`-derivation gives rise to the de Rham complex

`𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯`

on the site, which is built here as well.  Its differential is only additive and linear over the
global sections of the divided power base, not `𝒪_{X/S}`-linear — already the Leibniz rule in
degree zero forbids that — so it is not a morphism of presheaves of modules, and the complex is
recorded as data on additive maps instead.  Over an object `(U, T, δ)` the sections of `Ω_{X/S}`
are the divided power differentials of `Γ(T, 𝒪_T)` relative to `Γ(S, 𝒪_S)` modulo the
differentials of the sections pulled back from the divided power base, and the de Rham
differential there is the one of [Stacks, Tag 07HY]; it is determined by its values on the
standard generators `b₀ · d b₁ ∧ ⋯ ∧ d b_i`, which span each exterior power already over
`Γ(S, 𝒪_S)`.

The sections of `Ω^i_{X/S}` over an object `(U, T, δ)` are the `i`-th exterior power of the
sections of `Ω_{X/S}` there over the ring `Γ(T, 𝒪_T)`, and the transition maps are the exterior
powers of the transition maps of `Ω_{X/S}`, taken in the semilinear sense because the scalars
change along the map on sections.  Over the small site the same presheaf is obtained by
restricting the big-site one along the inclusion `Cris(X/S) ⥤ CRIS(X/S)`: forming exterior powers
is computed object by object and therefore commutes with that restriction.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.crysDifferentialForms` — `Ω^i_{X/S}` on the big
  crystalline category `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.crysFormVal` — a local differential form read as an
  element of the exterior algebra of the sections of `Ω_{X/S}`, the spelling in which all
  computations with forms are done.
* `Crystalline.GlobalCrystallineSituation.crysFormsZeroIso` — the degree-zero identification
  `𝒪_{X/S} ≅ Ω^0_{X/S}`, and `Crystalline.GlobalCrystallineSituation.crysFormsOneGen` the
  degree-one generator `Ω_{X/S} ⟶ Ω^1_{X/S}`, whose sectionwise inverse is
  `Crystalline.GlobalCrystallineSituation.crysFormsOneApp`.
* `Crystalline.GlobalCrystallineSituation.crysWedge` — the exterior multiplication
  `Ω^i_{X/S} × Ω^j_{X/S} → Ω^{i+j}_{X/S}`, and
  `Crystalline.GlobalCrystallineSituation.crysFormsGradedAlgebra` the resulting `ℕ`-graded
  algebra of presheaves of modules.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentials` and
  `Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentialForms` — `Ω_{X/S}` and
  `Ω^i_{X/S}` on the small crystalline site `Cris(X/S)`, the site the source works on.
* `Crystalline.canonicalSourceDeRham` — the de Rham complex of a commutative algebra, packaged as
  the data of the descent of [Stacks, Tag 07HY].
* `Crystalline.GlobalCrystallineSituation.crysD` — the universal differential `d_{X/S}` at an
  object, with its codomain spelled at the sections of `Ω_{X/S}` as a presheaf of modules.
* `Crystalline.GlobalCrystallineSituation.crysFormMap` — the transition map of `Ω^i_{X/S}` as a
  homomorphism of additive groups, and `crysGen` the standard degree-`i` generator
  `b₀ · d b₁ ∧ ⋯ ∧ d b_i`.
* `Crystalline.GlobalCrystallineSituation.CrysDeRhamComplex` — **the de Rham complex
  `𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯` on the crystalline site**: the degreewise differential, its
  linearity over the base, the formula on the standard generators, its compatibility with the
  transition maps of the site and its square-zero property.
* `Crystalline.GlobalCrystallineSituation.crysDeRhamComplex` — the canonical such complex.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamDifferential` — **the de Rham
  differential on the small crystalline site `Cris(X/S)`**, the site the source states the complex
  on, with `SmallSite.crysFormMap` and `SmallSite.crysD` the transition map and the universal
  differential there.

## Main results

* `Crystalline.GlobalCrystallineSituation.crysFormVal_map` — the transition maps of `Ω^i_{X/S}`
  are the exterior powers of the transition maps of `Ω_{X/S}`.
* `Crystalline.GlobalCrystallineSituation.crysFormVal_wedge` and
  `Crystalline.GlobalCrystallineSituation.crysWedge_self` — the exterior multiplication on
  degree-one generators, and the vanishing of the square of a differential.
* `Crystalline.GlobalCrystallineSituation.crysFormsOneApp_oneGen` — the degree-one generator is
  inverted by the degree-one identification on the sections over every object.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentialForms_eq_restriction` — the
  small-site `Ω^i_{X/S}` is the restriction of the big-site one along the inclusion of sites.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentialForms_obj` and
  `SmallSite.crysFormVal_map` — the sections of the small-site `Ω^i_{X/S}` over an object and the
  behaviour of its transition maps.
* `Crystalline.goodGenerator_comp` and `Crystalline.goodGenerator_D` — being a good generator of
  [Stacks, Tag 07HY] survives pushing forward, and the differential of an element is a good
  generator as soon as it is killed.
* `Crystalline.generationHypothesis_of_ker_eq_sup` — **the generation hypothesis of [Stacks, Tag
  07HY] for a divided power quotient killing a set of constants**.
* `Crystalline.exists_dpConstDeRham` and `Crystalline.dpConstDeRham_unique` — **the de Rham
  complex of the divided power differentials killing a set of constants**, and the fact that the
  rule on standard generators determines it.
* `Crystalline.GlobalCrystallineSituation.crysD_map` and `crysD_span` — the universal differential
  is carried to the universal differential of the image, and the universal differentials span the
  sections of `Ω_{X/S}` over an object.
* `Crystalline.GlobalCrystallineSituation.crysFormVal_map_ιMulti` — the transition maps of
  `Ω^i_{X/S}` carry a wedge of universal differentials to the wedge of the universal differentials
  of the images; `crysFormMap_crysGen` is the same statement for the standard generators and
  `crysFormMap_smul` the semilinearity of the transition maps.
* `Crystalline.GlobalCrystallineSituation.crysGen_span` — the standard generators span
  `Ω^i_{X/S}` over an object already over the global sections of the divided power base.
* `Crystalline.GlobalCrystallineSituation.exists_crysDeRhamComplex` — **the de Rham complex exists
  on the crystalline site**, naturality in the object included.
* `Crystalline.GlobalCrystallineSituation.CrysDeRhamComplex.unique` and the accompanying
  `Subsingleton` instance — the formula on the standard generators determines it.
* `Crystalline.GlobalCrystallineSituation.SmallSite.crysDeRhamDifferential_generator`,
  `SmallSite.crysDeRhamDifferential_naturality` and `SmallSite.crysDeRhamDifferential_squared` —
  the three defining properties of the de Rham differential on `Cris(X/S)`.

## Implementation notes

The scalars of a presheaf of modules are a presheaf of possibly noncommutative rings, while an
exterior algebra needs a commutative one; accordingly the scalars here are always written
`Crystalline.GlobalCrystallineSituation.crysFormRing`, the sections of the structure presheaf in
the `RingCat`-valued spelling that a presheaf of modules is indexed by, whose `CommRing` instance
comes from the commutative presheaf it is the image of.

Spelling a term as an element of `⋀^i` where a section of `Ω^i_{X/S}` is expected is expensive to
elaborate, as the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseAlgebras` record.  Every declaration
below therefore moves between the two spellings only through
`PresheafOfModules.extPowSections`, which is the identity map, and never by supplying a term of
one type where the other is expected.

**Two rings of sections.**  A presheaf of modules is indexed by a presheaf of `RingCat`-valued
rings, while every divided power construction is indexed by `CommRingCat`; the ring of sections
`Γ(T, 𝒪_T)` therefore carries two `Ring` structures that are definitionally but not syntactically
equal, and the sections of `Ω_{X/S}` over an object accordingly have two spellings —
`Crystalline.GlobalCrystallineSituation.crysDifferentialsObj` and
`(crysDifferentials _).obj (op _)`.  They are interchangeable by `rfl`, but not at the
transparency `rw` uses, so a rewrite cannot cross between them.  The ring-level results below are
stated purely in the `CommRingCat` spelling and the presheaf-level ones purely in the `RingCat`
spelling; `Crystalline.GlobalCrystallineSituation.crysD` is the retyped universal differential
that lets the second group be stated without mentioning the first.

The differentials are recorded as `AddMonoidHom`s together with an explicit base-linearity
hypothesis rather than as linear maps over the base ring.  Linear maps would need the algebra
structure that `Γ(S, 𝒪_S) ⟶ Γ(T, 𝒪_T)` induces, which the divided power constructions keep inside
their own bodies; carrying additivity and base-linearity separately keeps every statement free of
that instance, which is then introduced only inside the proofs that need it.

**Retyping across the two spellings.**  A type ascription written inside a term does not move a
subterm from one spelling of the ring of sections to the other, because the resolution of
`FunLike`, `HSMul` and `Module` looks at the type as inferred rather than as ascribed.  Retyping
therefore happens in exactly two ways below: through the declared result type of an `abbrev` or
`def` — this is what `Crystalline.GlobalCrystallineSituation.crysD`, `crysRingMap`, `crysBase` and
`crysFormMap` are for — or by giving a whole bundled homomorphism where the other spelling is
expected, which is definitional and so accepted.  For the same reason the per-object existence
statement inside `Crystalline.GlobalCrystallineSituation.exists_crysDeRhamComplex` is written
entirely in the presheaf spelling and crosses to the ring-level statement once, at the very
inside; every rewrite in the naturality argument then stays within one spelling.

`Crystalline.GlobalCrystallineSituation.baseAlgebra`, `baseModule` and `baseTower` are `scoped`.
Their subjects are the ring and the module of sections over an object, so as global instances they
would be found for every ring of sections of a scheme and compete with whatever algebra structure
is intended there; they are needed only to state that the standard generators span over the base
ring, and that is local to this file.

The small crystalline site is a full subcategory of the big crystalline category, so a presheaf
on the latter restricts to one on the former by precomposition; for presheaves of modules this is
`PresheafOfModules.pushforward₀`.  Because that restriction changes neither the sections over an
object nor the transition maps, the small-site exterior powers agree with the restrictions of the
big-site ones on the nose, which is
`Crystalline.GlobalCrystallineSituation.SmallSite.crysDifferentialForms_eq_restriction`.  Every
computation with forms happens on `CRIS(X/S)` and is read off on `Cris(X/S)` through that
restriction.

## References

* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
* [Stacks Project, Tag 07IG](https://stacks.math.columbia.edu/tag/07IG)
* [Stacks Project, Tag 01CF](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

noncomputable section

open Stacks.DeRham.DifferentialDescent

namespace Crystalline

/-! ### The de Rham complex of a divided power quotient of the Kähler differentials

The de Rham differential of `B` over `A` descends along a surjection `π : Ω[B⁄A] → M` whose
kernel is generated by elements that `π` kills and whose own differential is killed in the second
exterior power of `M` ([Stacks, Tag 07HY]).  The module of divided power differentials *killing a
set of constants* `T` is such a quotient: its kernel in `Ω[B⁄A]` is the join of the divided power
relations with the span of the differentials of `T`.
-/

/-- **The de Rham complex of `B` over `A`**, packaged as the data of the descent of [Stacks,
Tag 07HY]: the family of `A`-linear differentials on the exterior powers of the Kähler
differentials together with the defining rule on generators.  This is
`Stacks.DeRham.DifferentialDescent.sourceDeRham`, the construction of [Stacks, Tag 0FKF]. -/
abbrev canonicalSourceDeRham (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    SourceDeRham A B :=
  sourceDeRham A B

section GoodGenerators

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **Composing with a further linear map preserves being a good generator.** -/
theorem goodGenerator_comp {Ω Ω' : Type u} [AddCommGroup Ω] [Module B Ω]
    [AddCommGroup Ω'] [Module B Ω'] (π : Ω[B⁄A] →ₗ[B] Ω) (q : Ω →ₗ[B] Ω') {ω : Ω[B⁄A]}
    (h : (canonicalSourceDeRham A B).GoodGenerator π ω) :
    (canonicalSourceDeRham A B).GoodGenerator (q ∘ₗ π) ω := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp [h1], ?_⟩
  rw [exteriorPower.map_comp π q]
  show exteriorPower.map 2 q (exteriorPower.map 2 π
    ((canonicalSourceDeRham A B).d 1 ((exteriorPower.oneEquiv B (Ω[B⁄A])).symm ω))) = 0
  rw [h2, map_zero]

/-- **The differential of a single element is a good generator as soon as it is killed.** -/
theorem goodGenerator_D {Ω : Type u} [AddCommGroup Ω] [Module B Ω]
    (π : Ω[B⁄A] →ₗ[B] Ω) {s : B} (hs : π (KaehlerDifferential.D A B s) = 0) :
    (canonicalSourceDeRham A B).GoodGenerator π (KaehlerDifferential.D A B s) := by
  refine ⟨hs, ?_⟩
  have hgen := KaehlerDifferential.deRhamDifferential_smul_ιMulti_D (A := A) (B := B) 1
    (Fin.cons 1 (fun _ : Fin 1 ↦ s))
  simp only [Fin.cons_zero, Fin.cons_succ, one_smul] at hgen
  have h0 : (exteriorPower.oneEquiv B (Ω[B⁄A])).symm (KaehlerDifferential.D A B s) =
      exteriorPower.ιMulti B 1 (fun _ : Fin 1 ↦ KaehlerDifferential.D A B s) :=
    exteriorPower.oneEquiv_symm_apply _ _ _
  have hz : (canonicalSourceDeRham A B).d 1
      ((exteriorPower.oneEquiv B (Ω[B⁄A])).symm (KaehlerDifferential.D A B s)) = 0 := by
    rw [h0]
    show KaehlerDifferential.deRhamDifferential (A := A) 1 _ = 0
    rw [hgen]
    exact (exteriorPower.ιMulti B 2).map_coord_zero (i := 0) (by simp)
  rw [hz]
  exact map_zero _

variable {J : Ideal B}

/-- **The generation hypothesis of [Stacks, Tag 07HY] for a divided power quotient killing a set
of constants.**  A surjection out of the Kähler differentials whose kernel is the join of the
divided power relations with the span of the differentials of a set `T` is generated by good
generators. -/
theorem generationHypothesis_of_ker_eq_sup (hJ : DividedPowers J) (T : Set B)
    {M : Type u} [AddCommGroup M] [Module B M] (π : Ω[B⁄A] →ₗ[B] M)
    (hker : LinearMap.ker π = Submodule.span B (KaehlerDifferential.D A B '' T) ⊔
      dividedPowerDifferentialRelations (A := A) hJ) :
    (canonicalSourceDeRham A B).GenerationHypothesis π := by
  refine le_antisymm ?_ ?_
  · rw [hker]
    refine sup_le ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨s, hs, rfl⟩
      refine Submodule.subset_span (goodGenerator_D π ?_)
      rw [← LinearMap.mem_ker, hker]
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨s, hs, rfl⟩)
    · have hle : dividedPowerDifferentialRelations (A := A) hJ ≤ LinearMap.ker π :=
        hker ▸ le_sup_right
      have hfac : (dividedPowerDifferentialRelations (A := A) hJ).liftQ π hle ∘ₗ
          (dividedPowerDifferentialRelations (A := A) hJ).mkQ = π :=
        Submodule.liftQ_mkQ _ _ _
      have hgen1 := generationHypothesis_of_ker_eq_relations hJ (canonicalSourceDeRham A B)
        (dividedPowerDifferentialRelations (A := A) hJ).mkQ (Submodule.ker_mkQ _)
      rw [← Submodule.ker_mkQ (dividedPowerDifferentialRelations (A := A) hJ), hgen1]
      refine Submodule.span_le.mpr fun ω hω ↦ Submodule.subset_span ?_
      have hc := goodGenerator_comp
        (dividedPowerDifferentialRelations (A := A) hJ).mkQ
        ((dividedPowerDifferentialRelations (A := A) hJ).liftQ π hle) hω
      rwa [hfac] at hc
  · exact Submodule.span_le.mpr fun ω hω ↦ LinearMap.mem_ker.mpr hω.1

/-- The kernel of the quotient by a submodule followed by the quotient by the image of a second
submodule is the join of the two. -/
theorem ker_mkQ_comp_mkQ {M : Type u} [AddCommGroup M] [Module B M] (P N : Submodule B M) :
    LinearMap.ker ((Submodule.map P.mkQ N).mkQ ∘ₗ P.mkQ) = N ⊔ P := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_map_eq, Submodule.ker_mkQ]

/-- The kernel of the quotient by a submodule `P` followed by the quotient by the span of the
classes of a family of elements is the join of `P` with the span of that family. -/
theorem ker_mkQ_comp_mkQ_image {M X : Type u} [AddCommGroup M] [Module B M] (P : Submodule B M)
    (v : X → M) (s : Set X) :
    LinearMap.ker ((Submodule.span B ((fun x ↦ P.mkQ (v x)) '' s)).mkQ ∘ₗ P.mkQ) =
      Submodule.span B (v '' s) ⊔ P := by
  rw [show ((fun x ↦ P.mkQ (v x)) '' s) = P.mkQ '' (v '' s) from (Set.image_image _ _ _).symm,
    ← Submodule.map_span, ker_mkQ_comp_mkQ]

end GoodGenerators

section ConstDeRham

variable {A B : CommRingCat.{u}} {J : Ideal B}

/-- **The de Rham complex of the divided power differentials killing a set of constants.**  There
is a family of additive differentials `d : ⋀^i Ω¹_{B/A,δ,T} → ⋀^{i+1} Ω¹_{B/A,δ,T}`, linear over
the base ring, characterised on the standard generators by
`d (b₀ · d b₁ ∧ ⋯ ∧ d b_i) = d b₀ ∧ ⋯ ∧ d b_i`, and consecutive differentials compose to zero. -/
theorem exists_dpConstDeRham (f : A ⟶ B) (hJ : DividedPowers J) (T : Set B) :
    ∃ d : ∀ i : ℕ, ↥(⋀[↥B]^i ↥(dpConstDifferentials f hJ T)) →+
        ↥(⋀[↥B]^(i + 1) ↥(dpConstDifferentials f hJ T)),
      (∀ (i : ℕ) (a : A) (ω : ↥(⋀[↥B]^i ↥(dpConstDifferentials f hJ T))),
          d i (f a • ω) = f a • d i ω) ∧
      (∀ (i : ℕ) (b : Fin (i + 1) → B),
          d i (b 0 • exteriorPower.ιMulti ↥B i (fun j ↦ (dpConstD f hJ T).d (b j.succ))) =
            exteriorPower.ιMulti ↥B (i + 1) (fun j ↦ (dpConstD f hJ T).d (b j))) ∧
      (∀ (i : ℕ) (ω : ↥(⋀[↥B]^i ↥(dpConstDifferentials f hJ T))),
          d (i + 1) (d i ω) = 0) := by
  let _ := f.hom.toAlgebra
  have hker := ker_mkQ_comp_mkQ_image (dividedPowerDifferentialRelations (A := ↥A) hJ)
    (KaehlerDifferential.D ↥A ↥B) T
  have hsurj : Function.Surjective
      ((Submodule.span ↥B ((fun x ↦ (dividedPowerDifferentialRelations (A := ↥A) hJ).mkQ
            (KaehlerDifferential.D ↥A ↥B x)) '' T)).mkQ ∘ₗ
        (dividedPowerDifferentialRelations (A := ↥A) hJ).mkQ) :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  obtain ⟨d, -, hrule, -, hsq⟩ := exists_unique_quotient_deRhamDifferential
    (canonicalSourceDeRham ↥A ↥B) _ hsurj
    (generationHypothesis_of_ker_eq_sup hJ T _ hker)
  exact ⟨fun i ↦ AddMonoidHom.mk' (fun ω ↦ d i ω) (d i).map_add,
    fun i a ω ↦ (d i).map_smul a ω, fun i b ↦ hrule i b,
    fun i ω ↦ LinearMap.congr_fun (hsq i) ω⟩

/-- Two additive maps agreeing on a spanning set of a module are equal, provided agreement is
preserved by scalar multiplication. -/
private theorem addMonoidHom_eq_of_span_eq_top {R M N : Type*} [Semiring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] (d d' : M →+ N) (s : Set M) (hs : Submodule.span R s = ⊤)
    (hgen : ∀ x ∈ s, d x = d' x) (hsmul : ∀ (r : R) x, d x = d' x → d (r • x) = d' (r • x)) :
    d = d' := by
  refine AddMonoidHom.ext fun ω ↦ ?_
  have hmem : ω ∈ Submodule.span R s := by simp [hs]
  induction hmem using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => rw [map_zero, map_zero]
  | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy]
  | smul c x _ ih => exact hsmul c x ih

/-- **The generator rule determines the de Rham differential** of the divided power differentials
killing a set of constants: a base-linear additive map obeying the rule in degree `i` is
unique. -/
theorem dpConstDeRham_unique (f : A ⟶ B) (hJ : DividedPowers J) (T : Set B) (i : ℕ)
    {d d' : ↥(⋀[↥B]^i ↥(dpConstDifferentials f hJ T)) →+
      ↥(⋀[↥B]^(i + 1) ↥(dpConstDifferentials f hJ T))}
    (hsmul : ∀ (a : A) (ω : ↥(⋀[↥B]^i ↥(dpConstDifferentials f hJ T))),
      d (f a • ω) = f a • d ω)
    (hsmul' : ∀ (a : A) (ω : ↥(⋀[↥B]^i ↥(dpConstDifferentials f hJ T))),
      d' (f a • ω) = f a • d' ω)
    (hgen : ∀ b : Fin (i + 1) → B,
      d (b 0 • exteriorPower.ιMulti ↥B i (fun j ↦ (dpConstD f hJ T).d (b j.succ))) =
        exteriorPower.ιMulti ↥B (i + 1) (fun j ↦ (dpConstD f hJ T).d (b j)))
    (hgen' : ∀ b : Fin (i + 1) → B,
      d' (b 0 • exteriorPower.ιMulti ↥B i (fun j ↦ (dpConstD f hJ T).d (b j.succ))) =
        exteriorPower.ιMulti ↥B (i + 1) (fun j ↦ (dpConstD f hJ T).d (b j))) :
    d = d' := by
  let _ := f.hom.toAlgebra
  let _ : Module ↥A ↥(dpConstDifferentials f hJ T) :=
    Module.compHom (↥(dpConstDifferentials f hJ T)) f.hom
  let _ : IsScalarTower ↥A ↥B ↥(dpConstDifferentials f hJ T) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hspan : Submodule.span ↥A (Set.range fun c : Fin (i + 1) → ↥B ↦
      c 0 • exteriorPower.ιMulti ↥B i fun j ↦ (dpConstD f hJ T).d (c j.succ)) = ⊤ :=
    span_range_smul_ιMulti_eq_top (R := ↥A) (dpConstD f hJ T).d
      (dpConstDifferentials_span f hJ T) i
  refine addMonoidHom_eq_of_span_eq_top d d' _ hspan ?_ fun c x ih ↦ ?_
  · rintro _ ⟨b, rfl⟩
    rw [hgen, hgen']
  · rw [show (c • x : ↥(⋀[↥B]^i ↥(dpConstDifferentials f hJ T))) = f c • x from rfl,
      hsmul, hsmul', ih]

end ConstDeRham

end Crystalline

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})

/-! ### The exterior powers of `Ω_{X/S}` on the big crystalline category -/

/-- The ring of sections of `𝒪_{X/S}` over an object of `CRIS(X/S)`, in the `RingCat`-valued
spelling that a presheaf of modules is indexed by.  It is `Γ(T, 𝒪_T)` for `(U, T, δ)` the
object. -/
abbrev crysFormRing (A : Thickening S) : Type u :=
  ((structureRingCatPresheaf S).obj (op A) : Type u)

/-- **The presheaf `Ω^i_{X/S}` of crystalline differential forms of degree `i` on the big
crystalline category.**  Its sections over an object `(U, T, δ)` are the `i`-th exterior power
over `Γ(T, 𝒪_T)` of the sections of `Ω_{X/S}` there, and its transition maps are the exterior
powers of those of `Ω_{X/S}`. -/
@[stacks 07J4 "Ω^i_{X/S} = ∧^i Ω_{X/S}, on the big crystalline category CRIS(X/S)"]
abbrev crysDifferentialForms (i : ℕ) : PresheafOfModules.{u} (structureRingCatPresheaf S) :=
  PresheafOfModules.extPow i (crysDifferentials S)

/-- The sections of `Ω^i_{X/S}` over an object of `CRIS(X/S)` are the `i`-th exterior power of the
sections of `Ω_{X/S}` there. -/
abbrev crysFormSections (i : ℕ) (A : Thickening S) :
    (crysDifferentialForms S i).obj (op A) ≃ₗ[crysFormRing S A]
      ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A)) :=
  PresheafOfModules.extPowSections i (crysDifferentials S) (op A)

/-- The exterior algebra of the sections of `Ω_{X/S}` over an object of `CRIS(X/S)`, the ambient
algebra in which all the degrees of `Ω^*_{X/S}` sit. -/
abbrev crysFormAmbient (A : Thickening S) : Type u :=
  ExteriorAlgebra (crysFormRing S A) ((crysDifferentials S).obj (op A))

/-- A local crystalline differential form, read as an element of the exterior algebra of the
sections of `Ω_{X/S}`. -/
def crysFormVal {i : ℕ} {A : Thickening S} (z : (crysDifferentialForms S i).obj (op A)) :
    crysFormAmbient S A :=
  (crysFormSections S i A z).1

/-- A local crystalline differential form is determined by the element of the exterior algebra it
reads as. -/
theorem crysFormVal_injective {i : ℕ} {A : Thickening S}
    {z z' : (crysDifferentialForms S i).obj (op A)}
    (h : crysFormVal S z = crysFormVal S z') : z = z' := Subtype.ext h

/-- The zero form reads as the zero element of the exterior algebra. -/
@[simp]
theorem crysFormVal_zero (i : ℕ) (A : Thickening S) :
    crysFormVal S (0 : (crysDifferentialForms S i).obj (op A)) = 0 := rfl

/-- Reading a form in the exterior algebra is additive. -/
@[simp]
theorem crysFormVal_add {i : ℕ} {A : Thickening S}
    (z z' : (crysDifferentialForms S i).obj (op A)) :
    crysFormVal S (z + z') = crysFormVal S z + crysFormVal S z' := rfl

/-- Reading a form in the exterior algebra is homogeneous for the action of the sections of
`𝒪_{X/S}`. -/
@[simp]
theorem crysFormVal_smul {i : ℕ} {A : Thickening S} (c : crysFormRing S A)
    (z : (crysDifferentialForms S i).obj (op A)) :
    crysFormVal S (c • z) = c • crysFormVal S z := rfl

/-- **The transition maps of `Ω^i_{X/S}` are the exterior powers of those of `Ω_{X/S}`.**  Along a
morphism `(U, T, δ) → (U', T', δ')` of `CRIS(X/S)` a form of degree `i` over `(U', T', δ')` is
carried to the semilinear `i`-th exterior power of the transition map of `Ω_{X/S}`. -/
theorem crysFormVal_map {i : ℕ} {A B : Thickening S} (k : A ⟶ B)
    (z : (crysDifferentialForms S i).obj (op B)) :
    crysFormVal S ((crysDifferentialForms S i).map k.op z) =
      ExteriorAlgebra.mapₛₗ ((structureRingCatPresheaf S).map k.op).hom
        ((crysDifferentials S).restrictₛₗ k.op) (crysFormVal S z) :=
  PresheafOfModules.extPowSections_map i (crysDifferentials S) k.op z

/-! ### The universal differential at an object, retyped -/

/-- **The universal differential `d_{X/S}` at an object of `CRIS(X/S)`**, with its codomain
spelled at the sections of `Ω_{X/S}` as a presheaf of modules. -/
def crysD (A : Thickening S) (b : crysFormRing S A) : (crysDifferentials S).obj (op A) :=
  (crysDifferentialsD S A).d b

/-- **The universal differential is carried to the universal differential of the image.** -/
@[simp]
theorem crysD_map {A A' : Thickening S} (k : A ⟶ A') (b : crysFormRing S A') :
    (crysDifferentials S).map k.op (crysD S A' b) =
      crysD S A (k.targetHom.hom.appTop b) :=
  crysDifferentialsMap_d S k b

/-- **The universal differentials span the sections of `Ω_{X/S}` over an object.** -/
theorem crysD_span (A : Thickening S) :
    Submodule.span (crysFormRing S A) (Set.range (crysD S A)) = ⊤ :=
  dpConstDifferentials_span (crysBaseAppLE S A) (crysDividedPowers S A) (crysBaseSections S A)

/-- **The transition maps of `Ω^i_{X/S}` on a wedge of universal differentials.**  Along a
morphism of `CRIS(X/S)` the wedge of the universal differentials of a tuple of sections is carried
to the wedge of the universal differentials of the images of that tuple. -/
theorem crysFormVal_map_ιMulti {i : ℕ} {A A' : Thickening S} (k : A ⟶ A')
    (c : Fin i → crysFormRing S A') (z : (crysDifferentialForms S i).obj (op A'))
    (hz : crysFormVal S z =
      ((exteriorPower.ιMulti (crysFormRing S A') i (fun j ↦ crysD S A' (c j)) :
        ⋀[crysFormRing S A']^i ((crysDifferentials S).obj (op A'))) : crysFormAmbient S A')) :
    crysFormVal S ((crysDifferentialForms S i).map k.op z) =
      ((exteriorPower.ιMulti (crysFormRing S A) i
          (fun j ↦ crysD S A (k.targetHom.hom.appTop (c j))) :
        ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A))) : crysFormAmbient S A) := by
  rw [crysFormVal_map, hz, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  refine congrArg (fun g : Fin i → crysFormAmbient S A ↦ (List.ofFn g).prod) (funext fun j ↦ ?_)
  rw [Function.comp_apply, ExteriorAlgebra.mapₛₗ_ι]
  exact congrArg (ExteriorAlgebra.ι (crysFormRing S A)) (crysD_map S k (c j))

/-! ### The degree-zero and degree-one identifications -/

/-- **`Ω^0_{X/S} = 𝒪_{X/S}`.**  The zeroth exterior power of `Ω_{X/S}` is the free presheaf of
modules of rank one over the structure presheaf of `CRIS(X/S)`. -/
def crysFormsZeroIso :
    PresheafOfModules.unit (structureRingCatPresheaf S) ≅ crysDifferentialForms S 0 :=
  PresheafOfModules.extPowZeroIso (crysDifferentials S)

/-- **The degree-one generator `Ω_{X/S} ⟶ Ω^1_{X/S}`**, which sends a local differential to the
corresponding element of the first exterior power. -/
def crysFormsOneGen : crysDifferentials S ⟶ crysDifferentialForms S 1 :=
  PresheafOfModules.extPowGen (crysDifferentials S)

/-- The degree-one generator sends a local differential to its image under the canonical
injection of `Ω_{X/S}` into its exterior algebra. -/
@[simp]
theorem crysFormVal_oneGen (A : Thickening S) (x : (crysDifferentials S).obj (op A)) :
    crysFormVal S (PresheafOfModules.Hom.app (crysFormsOneGen S) (op A) x) =
      ExteriorAlgebra.ι (crysFormRing S A) x := rfl

/-- The degree-one identification on the sections over an object of `CRIS(X/S)`, as a linear
equivalence. -/
def crysFormsOneApp (A : Thickening S) :
    (crysDifferentialForms S 1).obj (op A) ≃ₗ[crysFormRing S A]
      (crysDifferentials S).obj (op A) :=
  (crysFormSections S 1 A).trans
    (exteriorPower.oneEquiv (crysFormRing S A) ((crysDifferentials S).obj (op A)))

/-- The inverse of the degree-one identification also sends a local differential to its image
under the canonical injection into the exterior algebra. -/
@[simp]
theorem crysFormsOneApp_symm_val (A : Thickening S) (x : (crysDifferentials S).obj (op A)) :
    crysFormVal S ((crysFormsOneApp S A).symm x) = ExteriorAlgebra.ι (crysFormRing S A) x := by
  have h : (exteriorPower.oneEquiv (crysFormRing S A)
      ((crysDifferentials S).obj (op A))).symm x =
      exteriorPower.ιMulti (crysFormRing S A) 1 (fun _ ↦ x) :=
    exteriorPower.oneEquiv_symm_apply _ _ x
  show ((exteriorPower.oneEquiv (crysFormRing S A)
    ((crysDifferentials S).obj (op A))).symm x : crysFormAmbient S A) = _
  rw [h, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, List.ofFn_succ,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]

/-- **`Ω^1_{X/S} = Ω_{X/S}`, on the sections over an object.**  The degree-one generator is the
inverse of the degree-one identification, so on every object of `CRIS(X/S)` it is bijective. -/
theorem crysFormsOneApp_symm_eq_oneGen (A : Thickening S)
    (x : (crysDifferentials S).obj (op A)) :
    (crysFormsOneApp S A).symm x =
      PresheafOfModules.Hom.app (crysFormsOneGen S) (op A) x :=
  crysFormVal_injective S
    ((crysFormsOneApp_symm_val S A x).trans (crysFormVal_oneGen S A x).symm)

/-- The degree-one identification inverts the degree-one generator, so the generator is a
bijection on the sections over every object. -/
@[simp]
theorem crysFormsOneApp_oneGen (A : Thickening S) (x : (crysDifferentials S).obj (op A)) :
    crysFormsOneApp S A (PresheafOfModules.Hom.app (crysFormsOneGen S) (op A) x) = x := by
  rw [← crysFormsOneApp_symm_eq_oneGen, LinearEquiv.apply_symm_apply]

/-! ### The exterior multiplication -/

/-- **The exterior multiplication `Ω^i_{X/S} × Ω^j_{X/S} → Ω^{i+j}_{X/S}`**, computed on sections
by multiplying in the exterior algebra of the sections of `Ω_{X/S}`. -/
def crysWedge (i j : ℕ) :
    Stacks.BilinearMap (crysDifferentialForms S i) (crysDifferentialForms S j)
      (crysDifferentialForms S (i + j)) :=
  PresheafOfModules.extPowMul (crysDifferentials S) i j

/-- The exterior multiplication of two forms reads as the product of the elements of the exterior
algebra they read as. -/
@[simp]
theorem crysFormVal_wedge (i j : ℕ) (A : Thickening S)
    (z : (crysDifferentialForms S i).obj (op A)) (z' : (crysDifferentialForms S j).obj (op A)) :
    crysFormVal S ((crysWedge S i j).app (op A) z z') =
      crysFormVal S z * crysFormVal S z' := rfl

/-- **The exterior product of a local crystalline differential with itself vanishes.** -/
theorem crysWedge_self (A : Thickening S) (x : (crysDifferentials S).obj (op A)) :
    (crysWedge S 1 1).app (op A) (PresheafOfModules.Hom.app (crysFormsOneGen S) (op A) x)
        (PresheafOfModules.Hom.app (crysFormsOneGen S) (op A) x) = 0 :=
  PresheafOfModules.extPowGen_sq_eq_zero (crysDifferentials S) (op A) x

/-- **The family `Ω^*_{X/S}` is an `ℕ`-graded algebra of presheaves of modules** on `CRIS(X/S)`,
the sectionwise exterior algebra of `Ω_{X/S}`. -/
def crysFormsGradedAlgebra :
    Stacks.GradedAlgebra (fun i : ℕ ↦ crysDifferentialForms S i) :=
  PresheafOfModules.extPowGradedAlgebra (crysDifferentials S)

/-! ### The de Rham complex on the crystalline site -/

/-- **The map on sections induced by a morphism of `CRIS(X/S)`**, at the spelling the structure
presheaf of rings uses. -/
abbrev crysRingMap {A A' : Thickening S} (k : A ⟶ A') (c : crysFormRing S A') :
    crysFormRing S A := (structureRingCatPresheaf S).map k.op c

/-- **A section of the divided power base, read over an object of `CRIS(X/S)`**, at the spelling
the structure presheaf of rings uses. -/
abbrev crysBase (A : Thickening S) (a : Γ(S.S.scheme, ⊤)) : crysFormRing S A :=
  crysBaseAppLE S A a

/-- **The transition map of `Ω^i_{X/S}` as a homomorphism of additive groups**, retyped at the
exterior powers. -/
def crysFormMap {i : ℕ} {A A' : Thickening S} (k : A ⟶ A') :
    ⋀[crysFormRing S A']^i ((crysDifferentials S).obj (op A')) →+
      ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A)) :=
  ((crysDifferentialForms S i).map k.op).hom.toAddMonoidHom

/-- The retyped transition map is the transition map of `Ω^i_{X/S}` itself. -/
theorem crysFormMap_eq {i : ℕ} {A A' : Thickening S} (k : A ⟶ A') :
    (crysFormMap S k : ⋀[crysFormRing S A']^i ((crysDifferentials S).obj (op A')) →+
        ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A))) =
      ((crysDifferentialForms S i).map k.op).hom.toAddMonoidHom := rfl

/-- **The transition maps of `Ω^i_{X/S}` are semilinear**: a scalar is carried along the map on
sections of the structure presheaf. -/
theorem crysFormMap_smul {i : ℕ} {A A' : Thickening S} (k : A ⟶ A')
    (c : crysFormRing S A') (z : ⋀[crysFormRing S A']^i ((crysDifferentials S).obj (op A'))) :
    crysFormMap S k (c • z) = crysRingMap S k c • crysFormMap S k z :=
  PresheafOfModules.map_smul (crysDifferentialForms S i) k.op c z

/-- **The transition maps carry a wedge of universal differentials to the wedge of the universal
differentials of the images**, in the retyped form. -/
theorem crysFormMap_ιMulti {i : ℕ} {A A' : Thickening S} (k : A ⟶ A')
    (c : Fin i → crysFormRing S A') :
    crysFormMap S k (exteriorPower.ιMulti (crysFormRing S A') i (fun j ↦ crysD S A' (c j))) =
      exteriorPower.ιMulti (crysFormRing S A) i
        (fun j ↦ crysD S A (crysRingMap S k (c j))) :=
  crysFormVal_injective S (crysFormVal_map_ιMulti S k c _ rfl)

/-- **The standard degree-`i` generator `b₀ · d b₁ ∧ ⋯ ∧ d b_i` of `Ω^i_{X/S}`** over an object of
`CRIS(X/S)`, on which the de Rham differential is prescribed. -/
abbrev crysGen (A : Thickening S) (i : ℕ) (b : Fin (i + 1) → crysFormRing S A) :
    ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A)) :=
  b 0 • exteriorPower.ιMulti (crysFormRing S A) i (fun j ↦ crysD S A (b j.succ))

/-- **The transition maps carry the standard generators to the standard generators**, over the
images of the defining tuple of sections. -/
theorem crysFormMap_crysGen {i : ℕ} {A A' : Thickening S} (k : A ⟶ A')
    (b : Fin (i + 1) → crysFormRing S A') :
    crysFormMap S k (crysGen S A' i b) =
      crysGen S A i (fun j ↦ crysRingMap S k (b j)) := by
  rw [crysFormMap_smul, crysFormMap_ιMulti]

/-- **A section pulled back from the divided power base is carried to the corresponding section of
the source.** -/
theorem crysRingMap_crysBase {A A' : Thickening S} (k : A ⟶ A') (c : Γ(S.S.scheme, ⊤)) :
    crysRingMap S k (crysBase S A' c) = crysBase S A c := by
  have h := crysBaseAppLE_fac S k
  rw [Category.id_comp] at h
  exact (CommRingCat.comp_apply _ _ c).symm.trans
    (congrArg (fun φ : Γ(S.S.scheme, ⊤) ⟶ Γ(A.thickening.target.scheme, ⊤) ↦ φ c) h).symm

/-- The sections of `𝒪_{X/S}` over an object of `CRIS(X/S)` form an algebra over the global
sections of the divided power base, along the structure morphism to the base. -/
scoped instance baseAlgebra (A : Thickening S) :
    Algebra ↥Γ(S.S.scheme, ⊤) (crysFormRing S A) := (crysBaseAppLE S A).hom.toAlgebra

/-- The sections of `Ω_{X/S}` over an object of `CRIS(X/S)` are a module over the global sections
of the divided power base, by restriction of scalars along the structure morphism. -/
scoped instance baseModule (A : Thickening S) :
    Module ↥Γ(S.S.scheme, ⊤) ((crysDifferentials S).obj (op A)) :=
  Module.compHom _ (crysBaseAppLE S A).hom

/-- The actions of the base ring and of the ring of sections on `Ω_{X/S}` form a tower. -/
scoped instance baseTower (A : Thickening S) :
    IsScalarTower ↥Γ(S.S.scheme, ⊤) (crysFormRing S A) ((crysDifferentials S).obj (op A)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- **The standard generators span `Ω^i_{X/S}` over an object already over the base ring**, not
merely over the ring of sections. -/
theorem crysGen_span (A : Thickening S) (i : ℕ) :
    Submodule.span ↥Γ(S.S.scheme, ⊤) (Set.range (crysGen S A i)) = ⊤ :=
  span_range_smul_ιMulti_eq_top (R := ↥Γ(S.S.scheme, ⊤)) (crysD S A) (crysD_span S A) i

/-- **The de Rham complex `𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯` on the crystalline site.**  The
differential in degree `i` over an object is additive and linear over the global sections of the
divided power base — not over `𝒪_{X/S}`, already because of the Leibniz rule in degree zero — it
is characterised on the standard generators by `d (b₀ · d b₁ ∧ ⋯ ∧ d b_i) = d b₀ ∧ ⋯ ∧ d b_i`, it
commutes with the transition maps of the site, and consecutive differentials compose to zero. -/
@[ext]
structure CrysDeRhamComplex where
  /-- The differential in degree `i` over an object of the site. -/
  differential : ∀ (i : ℕ) (A : Thickening S),
    ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A)) →+
      ⋀[crysFormRing S A]^(i + 1) ((crysDifferentials S).obj (op A))
  /-- The differential is linear over the global sections of the divided power base. -/
  differential_base_smul : ∀ (i : ℕ) (A : Thickening S) (a : Γ(S.S.scheme, ⊤))
      (ω : ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A))),
    differential i A (crysBase S A a • ω) = crysBase S A a • differential i A ω
  /-- The formula defining the differential on the standard generators. -/
  differential_generator : ∀ (i : ℕ) (A : Thickening S) (b : Fin (i + 1) → crysFormRing S A),
    differential i A (crysGen S A i b) =
      exteriorPower.ιMulti (crysFormRing S A) (i + 1) (fun j ↦ crysD S A (b j))
  /-- The differentials commute with the transition maps of the site. -/
  differential_naturality : ∀ (i : ℕ) {A A' : Thickening S} (k : A ⟶ A')
      (ω : ⋀[crysFormRing S A']^i ((crysDifferentials S).obj (op A'))),
    crysFormMap S k (differential i A' ω) = differential i A (crysFormMap S k ω)
  /-- Consecutive differentials compose to zero. -/
  differential_squared : ∀ (i : ℕ) (A : Thickening S)
      (ω : ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A))),
    differential (i + 1) A (differential i A ω) = 0

/-- **The de Rham complex exists on the crystalline site.** -/
theorem exists_crysDeRhamComplex : Nonempty (CrysDeRhamComplex S) := by
  have key : ∀ A : Thickening S, ∃ d : ∀ i : ℕ,
      ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A)) →+
        ⋀[crysFormRing S A]^(i + 1) ((crysDifferentials S).obj (op A)),
      (∀ (i : ℕ) (a : Γ(S.S.scheme, ⊤))
          (ω : ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A))),
            d i (crysBase S A a • ω) = crysBase S A a • d i ω) ∧
      (∀ (i : ℕ) (b : Fin (i + 1) → crysFormRing S A),
            d i (crysGen S A i b) =
              exteriorPower.ιMulti (crysFormRing S A) (i + 1) (fun j ↦ crysD S A (b j))) ∧
      (∀ (i : ℕ) (ω : ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A))),
            d (i + 1) (d i ω) = 0) := by
    intro A
    obtain ⟨d, hs, hg, hq⟩ :=
      exists_dpConstDeRham (crysBaseAppLE S A) (crysDividedPowers S A) (crysBaseSections S A)
    exact ⟨d, fun i a ω ↦ hs i a ω, fun i b ↦ hg i b, fun i ω ↦ hq i ω⟩
  choose D hsmul hgen hsq using key
  refine ⟨{ differential := fun i A ↦ D A i
            differential_base_smul := fun i A ↦ hsmul A i
            differential_generator := fun i A ↦ hgen A i
            differential_squared := fun i A ↦ hsq A i
            differential_naturality := ?_ }⟩
  intro i A A' k
  refine DFunLike.congr_fun (addMonoidHom_eq_of_span_eq_top
    ((crysFormMap S k).comp (D A' i)) ((D A i).comp (crysFormMap S k)) _ (crysGen_span S A' i)
    ?_ fun c x ih ↦ ?_)
  · rintro _ ⟨b, rfl⟩
    simp only [AddMonoidHom.comp_apply]
    rw [hgen A' i b, crysFormMap_crysGen, hgen A i (fun j ↦ crysRingMap S k (b j)),
      crysFormMap_ιMulti]
  · have hc : (c • x : ⋀[crysFormRing S A']^i ((crysDifferentials S).obj (op A'))) =
        crysBase S A' c • x := (algebraMap_smul (crysFormRing S A') c x).symm
    simp only [AddMonoidHom.comp_apply] at ih ⊢
    rw [hc, hsmul A' i c x, crysFormMap_smul, crysFormMap_smul, crysRingMap_crysBase,
      hsmul A i c (crysFormMap S k x), ih]

/-- **The canonical de Rham complex on the crystalline site**, the complex
`𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯` that the universal `S`-derivation `d_{X/S}` gives rise to. -/
@[stacks 07J4 "the de Rham complex 𝒪_{X/S} → Ω¹ → Ω² → ⋯, on CRIS(X/S)"]
def crysDeRhamComplex : CrysDeRhamComplex S := Classical.choice (exists_crysDeRhamComplex S)

/-- **The formula on the standard generators determines the de Rham complex on the crystalline
site**, degreewise over every object. -/
theorem CrysDeRhamComplex.unique (C : CrysDeRhamComplex S) : C = crysDeRhamComplex S := by
  refine CrysDeRhamComplex.ext ?_
  funext i A
  exact dpConstDeRham_unique (crysBaseAppLE S A) (crysDividedPowers S A) (crysBaseSections S A) i
    (C.differential_base_smul i A) ((crysDeRhamComplex S).differential_base_smul i A)
    (C.differential_generator i A) ((crysDeRhamComplex S).differential_generator i A)

/-- Any two de Rham complexes on the crystalline site agree. -/
instance instSubsingletonCrysDeRhamComplex : Subsingleton (CrysDeRhamComplex S) where
  allEq C C' := (C.unique).trans (C'.unique).symm

/-! ### `Ω^i_{X/S}` on the small crystalline site -/

namespace SmallSite

/-- The restriction of a presheaf of `𝒪_{X/S}`-modules from the big crystalline category to the
small crystalline site, by precomposition with the inclusion of the latter in the former. -/
abbrev restrictModules :
    PresheafOfModules.{u} (GlobalCrystallineSituation.structureRingCatPresheaf S) ⥤
      PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.pushforward₀OfCommRingCat (CrystallineThickening.ι S)
    (GlobalCrystallineSituation.structureRingPresheaf S)

/-- **The module of crystalline differentials `Ω_{X/S}` on the small crystalline site**, the
restriction to `Cris(X/S)` of the presheaf of crystalline differentials on `CRIS(X/S)`.  Its
sections over an object `(U, T, δ)` of `Cris(X/S)` are the divided power differentials of
`Γ(T, 𝒪_T)` relative to `Γ(S, 𝒪_S)` modulo the differentials of the sections pulled back from the
divided power base. -/
def crysDifferentials :
    PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat) :=
  (restrictModules S).obj (GlobalCrystallineSituation.crysDifferentials S)

/-- The sections of the small-site `Ω_{X/S}` over an object are the sections of the big-site
`Ω_{X/S}` over the same object of `CRIS(X/S)`. -/
@[simp]
theorem crysDifferentials_obj (A : CrystallineThickening S) :
    (crysDifferentials S).obj (op A) =
      GlobalCrystallineSituation.crysDifferentialsObj S A.obj := rfl

/-- **The presheaf `Ω^i_{X/S}` of crystalline differential forms of degree `i` on the small
crystalline site `Cris(X/S)`**, the `i`-th exterior power of `Ω_{X/S}` over `𝒪_{X/S}`. -/
@[stacks 07J4 "Ω^i_{X/S} = ∧^i_{𝒪_{X/S}} Ω_{X/S} on the small crystalline site Cris(X/S)"]
abbrev crysDifferentialForms (i : ℕ) :
    PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.extPow i (crysDifferentials S)

/-- **Forming exterior powers commutes with restricting from the big crystalline category to the
small crystalline site.**  Both presheaves have the `i`-th exterior power of the sections of
`Ω_{X/S}` as their sections over an object of `Cris(X/S)`, with the same transition maps. -/
theorem crysDifferentialForms_eq_restriction (i : ℕ) :
    crysDifferentialForms S i =
      (restrictModules S).obj (GlobalCrystallineSituation.crysDifferentialForms S i) := rfl

/-- The ring of sections of `𝒪_{X/S}` over an object of `Cris(X/S)`, in the `RingCat`-valued
spelling that a presheaf of modules is indexed by. -/
abbrev crysFormRing (A : CrystallineThickening S) : Type u :=
  ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).obj (op A) : Type u)

/-- The sections of the small-site `Ω^i_{X/S}` over an object are the `i`-th exterior power of the
sections of `Ω_{X/S}` there. -/
abbrev crysFormSections (i : ℕ) (A : CrystallineThickening S) :
    (crysDifferentialForms S i).obj (op A) ≃ₗ[crysFormRing S A]
      ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A)) :=
  PresheafOfModules.extPowSections i (crysDifferentials S) (op A)

/-- The exterior algebra of the sections of `Ω_{X/S}` over an object of `Cris(X/S)`. -/
abbrev crysFormAmbient (A : CrystallineThickening S) : Type u :=
  ExteriorAlgebra (crysFormRing S A) ((crysDifferentials S).obj (op A))

/-- A local crystalline differential form on the small site, read as an element of the exterior
algebra of the sections of `Ω_{X/S}`. -/
def crysFormVal {i : ℕ} {A : CrystallineThickening S}
    (z : (crysDifferentialForms S i).obj (op A)) : crysFormAmbient S A :=
  (crysFormSections S i A z).1

/-- A local crystalline differential form on the small site is determined by the element of the
exterior algebra it reads as. -/
theorem crysFormVal_injective {i : ℕ} {A : CrystallineThickening S}
    {z z' : (crysDifferentialForms S i).obj (op A)}
    (h : crysFormVal S z = crysFormVal S z') : z = z' := Subtype.ext h

/-- **The transition maps of the small-site `Ω^i_{X/S}` are the exterior powers of those of
`Ω_{X/S}`.** -/
theorem crysFormVal_map {i : ℕ} {A B : CrystallineThickening S} (k : A ⟶ B)
    (z : (crysDifferentialForms S i).obj (op B)) :
    crysFormVal S ((crysDifferentialForms S i).map k.op z) =
      ExteriorAlgebra.mapₛₗ
        ((structurePresheaf S ⋙ forget₂ CommRingCat RingCat).map k.op).hom
        ((crysDifferentials S).restrictₛₗ k.op) (crysFormVal S z) :=
  PresheafOfModules.extPowSections_map i (crysDifferentials S) k.op z

/-- **`Ω^0_{X/S} = 𝒪_{X/S}` on the small crystalline site.** -/
def crysFormsZeroIso :
    PresheafOfModules.unit (structurePresheaf S ⋙ forget₂ CommRingCat RingCat) ≅
      crysDifferentialForms S 0 :=
  PresheafOfModules.extPowZeroIso (crysDifferentials S)

/-- **The degree-one generator `Ω_{X/S} ⟶ Ω^1_{X/S}` on the small crystalline site.** -/
def crysFormsOneGen : crysDifferentials S ⟶ crysDifferentialForms S 1 :=
  PresheafOfModules.extPowGen (crysDifferentials S)

/-- **The exterior multiplication `Ω^i_{X/S} × Ω^j_{X/S} → Ω^{i+j}_{X/S}` on the small crystalline
site.** -/
def crysWedge (i j : ℕ) :
    Stacks.BilinearMap (crysDifferentialForms S i) (crysDifferentialForms S j)
      (crysDifferentialForms S (i + j)) :=
  PresheafOfModules.extPowMul (crysDifferentials S) i j

/-- **The family `Ω^*_{X/S}` on the small crystalline site is an `ℕ`-graded algebra of presheaves
of modules**, the sectionwise exterior algebra of `Ω_{X/S}`. -/
def crysFormsGradedAlgebra :
    Stacks.GradedAlgebra (fun i : ℕ ↦ crysDifferentialForms S i) :=
  PresheafOfModules.extPowGradedAlgebra (crysDifferentials S)

/-! ### The de Rham complex on the small crystalline site -/

/-- **The transition map of the small-site `Ω^i_{X/S}` as a homomorphism of additive groups**,
retyped at the exterior powers. -/
def crysFormMap {i : ℕ} {A A' : CrystallineThickening S} (k : A ⟶ A') :
    ⋀[crysFormRing S A']^i ((crysDifferentials S).obj (op A')) →+
      ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A)) :=
  ((crysDifferentialForms S i).map k.op).hom.toAddMonoidHom

/-- **The universal differential `d_{X/S}` at an object of `Cris(X/S)`**, retyped at the sections
of the small-site `Ω_{X/S}`. -/
def crysD (A : CrystallineThickening S) (b : crysFormRing S A) :
    (crysDifferentials S).obj (op A) :=
  GlobalCrystallineSituation.crysD S A.obj b

/-- **The de Rham complex `𝒪_{X/S} → Ω¹_{X/S} → Ω²_{X/S} → ⋯` on the small crystalline site
`Cris(X/S)`**: the differential of the canonical complex on `CRIS(X/S)` at an object of the full
subcategory `Cris(X/S)`. -/
@[stacks 07J4 "the de Rham complex 𝒪_{X/S} → Ω¹ → Ω² → ⋯ on Cris(X/S)"]
def crysDeRhamDifferential (i : ℕ) (A : CrystallineThickening S) :
    ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A)) →+
      ⋀[crysFormRing S A]^(i + 1) ((crysDifferentials S).obj (op A)) :=
  (GlobalCrystallineSituation.crysDeRhamComplex S).differential i A.obj

/-- **The defining formula of the de Rham differential on the standard generators**, over an
object of the small crystalline site. -/
theorem crysDeRhamDifferential_generator (i : ℕ) (A : CrystallineThickening S)
    (b : Fin (i + 1) → crysFormRing S A) :
    crysDeRhamDifferential S i A
        (b 0 • exteriorPower.ιMulti (crysFormRing S A) i (fun j ↦ crysD S A (b j.succ))) =
      exteriorPower.ιMulti (crysFormRing S A) (i + 1) (fun j ↦ crysD S A (b j)) :=
  (GlobalCrystallineSituation.crysDeRhamComplex S).differential_generator i A.obj b

/-- **The de Rham differential commutes with the transition maps of the small crystalline
site**, so the complex is a complex of presheaves of abelian groups on `Cris(X/S)`. -/
theorem crysDeRhamDifferential_naturality (i : ℕ) {A A' : CrystallineThickening S} (k : A ⟶ A')
    (ω : ⋀[crysFormRing S A']^i ((crysDifferentials S).obj (op A'))) :
    crysFormMap S k (crysDeRhamDifferential S i A' ω) =
      crysDeRhamDifferential S i A (crysFormMap S k ω) :=
  (GlobalCrystallineSituation.crysDeRhamComplex S).differential_naturality i
    ((CrystallineThickening.ι S).map k) ω

/-- **Consecutive de Rham differentials compose to zero** over an object of the small crystalline
site. -/
theorem crysDeRhamDifferential_squared (i : ℕ) (A : CrystallineThickening S)
    (ω : ⋀[crysFormRing S A]^i ((crysDifferentials S).obj (op A))) :
    crysDeRhamDifferential S (i + 1) A (crysDeRhamDifferential S i A ω) = 0 :=
  (GlobalCrystallineSituation.crysDeRhamComplex S).differential_squared i A.obj ω

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
