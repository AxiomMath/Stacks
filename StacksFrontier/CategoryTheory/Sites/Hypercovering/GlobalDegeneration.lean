module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CohomologyAsColimit
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.TerminalRefinement
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.GlobalPageDegeneration
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Degeneration for hypercoverings of the final presheaf

For hypercoverings of the final presheaf, this file proves that the coefficients of the second
page of the hypercovering spectral sequence are locally zero off the bottom row, that every term of
that spectral sequence off the bottom row dies after a refinement, and, in every degree, that two
Čech classes with the same image under the canonical comparison with cohomology agree on a common
refinement of the two hypercoverings they live on.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.IsLocallyZeroPresheaf`: a presheaf of abelian groups all of
  whose sections are killed by restriction along a covering, with no size restriction on the site
  or on the coefficients.
* `Stacks.CategoryTheory.Hypercovering.globalSpectralSequenceAt` and
  `globalSpectralSequenceAtMap`: the hypercovering spectral sequence at the final presheaf and a
  fixed coefficient sheaf, as a family indexed by the hypercoverings of the final presheaf,
  together with the morphism a refinement induces.
* `Stacks.CategoryTheory.Hypercovering.globalPageTwoIso`: its second page at `(p, q')`.
* `Stacks.CategoryTheory.Hypercovering.cechToPageTwoZero`: the identification of
  `Ȟ^i(K, 𝓕)` with the bottom row `E₂^{i,0}` of the second page, and
  `cechCohomologyToPageTwoZero`: the same morphism with its source written as the Čech cohomology
  group `cechCohomology`.

## Main results

* `Stacks.CategoryTheory.Hypercovering.exists_sieve_apply_eq_zero_of_injectiveResolution`: for
  `n > 0` the `n`-th homology presheaf of the complex of sections of an injective resolution of an
  abelian sheaf is locally zero, with the site and the coefficients unrestricted.
* `Stacks.CategoryTheory.Hypercovering.isLocallyZeroPresheaf_rightDerived`: for `q > 0` the
  `q`-th right derived functor of the inclusion of abelian sheaves into presheaves, evaluated at a
  sheaf, is locally zero.
* `Stacks.CategoryTheory.Hypercovering.exists_hom_factoring_through_covering`: a covering of the
  term of a hypercovering of the final presheaf in a fixed degree is refined by a
  `HypercoveringOf.Hom`.
* `Stacks.CategoryTheory.Hypercovering.exists_hom_presheafCechCohomologyFunctorMap_apply_eq_zero`:
  every Čech cohomology class of a hypercovering of the final presheaf with locally zero
  coefficients dies after a refinement.
* `Stacks.CategoryTheory.Hypercovering.exists_hom_pageTwo_apply_eq_zero`,
  `exists_hom_page_apply_eq_zero` and `exists_hom_pageInfinity_apply_eq_zero`: for `q' > 0`
  every element of `E₂^{p,q'}`, of every page `E_r^{p,q'}` with `r ≥ 2`, and of the infinity page
  `E_∞^{p,q'}` of the spectral sequence of a hypercovering of the final presheaf dies after a
  refinement.
* `CategoryTheory.CohomologicalSpectralSequenceNat.exists_rel_map_pageTwo_eq_zero` and
  `exists_rel_map_eq_zero_of_edgeEpi_apply_eq_zero`: for a family of first-quadrant spectral
  sequences indexed by a type with refinements, whose terms off the bottom row die after a
  refinement, the kernel of the edge epimorphism out of `E₂^{n,0}` dies after a refinement.
* `Stacks.CategoryTheory.Hypercovering.cechToPageTwoZero_comp_bottomRowEdge` and
  `cechCohomologyFunctorMap_comp_cechToPageTwoZero`: the canonical comparison is
  `cechToPageTwoZero` followed by the bottom-row edge map of the abutment, and
  `cechToPageTwoZero` is natural in the hypercovering.
* `Stacks.CategoryTheory.Hypercovering.cechToPageTwoZero_comp_edgeEpi_comp`: the canonical
  comparison factors as `cechToPageTwoZero` followed by the edge epimorphism
  `E₂^{i,0} ⟶ E_∞^{i,0}` followed by a monomorphism.
* `Stacks.CategoryTheory.Hypercovering.hom_apply_eq_zero_of_comp_eq`,
  `hom_apply_eq_zero_of_mono_comp`, `hom_apply_eq_zero_of_mono_mono_comp`,
  `hom_apply_eq_zero_of_mono_of_comp_eq`, `hom_sub_apply_eq_zero_of_comp_eq` and
  `hom_apply_eq_of_hom_sub_apply_eq_zero`: element-level consequences of commuting triangles and
  squares of morphisms of abelian groups.
* `Stacks.CategoryTheory.Hypercovering.exists_hom_pageTwoZero_apply_eq_zero` and
  `exists_hom_cechCohomologyMap_apply_eq_zero`: the kernel of the canonical comparison dies after
  a refinement of the hypercovering, in every degree.
* `Stacks.CategoryTheory.Hypercovering.exists_hom_cechCohomologyEdge_eq`: in every degree, two
  Čech classes on hypercoverings `K` and `L` of the final presheaf with the same image under the
  canonical comparison agree on a common refinement.

## Implementation notes

The results take as hypotheses sheafification, enough injectives and `HasExt` at the coefficient
universe, together with `GrothendieckTopology.WEqualsLocallyBijective`, which makes the unit of
sheafification locally injective and holds for every essentially small site
(`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`).

The hypercoverings are taken at the universe `max u v w` wherever
`exists_hypercoveringOfTerminal_map_factoring_through_covering` is used, since that lemma is
stated for `HypercoveringOfTerminal.{max w u v}`; the family, its second page and
`cechToPageTwoZero` are stated at a free `w`.

## References

* [Stacks Project, Tag 09VZ](https://stacks.math.columbia.edu/tag/09VZ)
* [Stacks Project, Tag 09VY](https://stacks.math.columbia.edu/tag/09VY)
* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
* [Stacks Project, Tag 01ER](https://stacks.math.columbia.edu/tag/01ER)
* [Stacks Project, Tag 01GJ](https://stacks.math.columbia.edu/tag/01GJ)
* [Stacks Project, Tag 01G3](https://stacks.math.columbia.edu/tag/01G3)
* [Stacks Project, Tag 01H0](https://stacks.math.columbia.edu/tag/01H0)
-/

@[expose] public noncomputable section

universe t w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

/-! ### The kernel of the edge epimorphism, for a `Rel`-shaped family of spectral sequences -/

namespace CategoryTheory.CohomologicalSpectralSequenceNat

variable {D : Type*} {Rel : D → D → Type*}

/-- **A composite of two refinements acts on a page as the composite of what each does**, read on
an element, for a family of spectral sequences with a composition of refinements. -/
lemma rel_map_comp_apply (E : D → CohomologicalSpectralSequenceNat AddCommGrpCat.{t} 2)
    (Φ : ∀ {K L : D}, Rel K L → (E K ⟶ E L))
    (relComp : ∀ {K L M : D}, Rel K L → Rel L M → Rel K M)
    (hrelComp : ∀ {K L M : D} (g₁ : Rel K L) (g₂ : Rel L M),
      Φ (relComp g₁ g₂) = Φ g₁ ≫ Φ g₂)
    (r : ℤ) (hr : 2 ≤ r) {K L M : D} (g₁ : Rel K L) (g₂ : Rel L M)
    (pq : ℕ × ℕ) (z : ToType (((E K).page r hr).X pq)) :
    ConcreteCategory.hom (((Φ (relComp g₁ g₂)).hom r hr).f pq) z =
      ConcreteCategory.hom (((Φ g₂).hom r hr).f pq)
        (ConcreteCategory.hom (((Φ g₁).hom r hr).f pq) z) := by
  have h : ((Φ (relComp g₁ g₂)).hom r hr).f pq =
      ((Φ g₁).hom r hr).f pq ≫ ((Φ g₂).hom r hr).f pq := by
    rw [hrelComp g₁ g₂]
    rfl
  rw [h]
  exact ConcreteCategory.comp_apply _ _ z

/-- **For a `Rel`-shaped family of first-quadrant spectral sequences of abelian groups whose terms
off the bottom row all die after a refinement, the kernel of the composite edge epimorphism
`E₂^{n,0} ⟶ E_r^{n,0}` dies after a refinement.**

The family is a bare family `E` together with a family `Rel` of refinements, a morphism of
spectral sequences for each refinement, a composition of refinements and an identity refinement;
no category structure on the index type is required.

The composite to `E_r^{n,0}` is the composite to `E_{r-1}^{n,0}` followed by one one-step edge
epimorphism, whose kernel is the image of the differential into `(n, 0)` on the page `r - 1`; the
source of that differential lies off the bottom row, so it dies, and with it the image on
`E_{r-1}^{n,0}`. -/
theorem exists_rel_map_pageTwo_eq_zero
    (E : D → CohomologicalSpectralSequenceNat AddCommGrpCat.{t} 2)
    (Φ : ∀ {K L : D}, Rel K L → (E K ⟶ E L))
    (relComp : ∀ {K L M : D}, Rel K L → Rel L M → Rel K M)
    (hrelComp : ∀ {K L M : D} (g₁ : Rel K L) (g₂ : Rel L M),
      Φ (relComp g₁ g₂) = Φ g₁ ≫ Φ g₂)
    (relId : ∀ K : D, Rel K K) (n : ℕ)
    (hdeg : ∀ (q : ℕ), 0 < q → ∀ (r : ℤ) (hr : 2 ≤ r) (p : ℕ) (K : D)
      (x : ToType (((E K).page r hr).X (p, q))),
      ∃ (L : D) (g : Rel K L), ConcreteCategory.hom (((Φ g).hom r hr).f (p, q)) x = 0)
    (k : ℕ) :
    ∀ (r : ℤ) (hr : 2 ≤ r) (_ : 2 + (k : ℤ) = r) (K : D)
      (z : ToType (((E K).page 2 le_rfl).X (n, 0)))
      (_ : ConcreteCategory.hom ((E K).edgeEpiSteps (n, 0) 2 r hr) z = 0),
      ∃ (L : D) (g : Rel K L),
        ConcreteCategory.hom (((Φ g).hom 2 le_rfl).f (n, 0)) z = 0 := by
  induction k with
  | zero =>
    intro r hr hk K z hz
    refine ⟨K, relId K, ?_⟩
    rw [SpectralSequence.eq_zero_of_edgeEpiSteps_apply_eq_zero (n, 0) 2 r (by omega) z hz,
      map_zero]
  | succ k ih =>
    intro r hr hk K z hz
    have hr' : (2 : ℤ) ≤ r - 1 := by omega
    have := hasEdgeEpiAt (E K) (n, 0) (r - 1) (by omega) hr'
    rcases eq_zero_or_exists_d_apply_eq (E K) n (r - 1) r hr' (by omega) hr z hz with
      h0 | ⟨p, q, hq, zz, hzz⟩
    · exact ih (r - 1) hr' (by omega) K z h0
    · obtain ⟨L, g, hg⟩ := hdeg q hq (r - 1) hr' p K zz
      obtain ⟨M, g', hg'⟩ := ih (r - 1) hr' (by omega) L
        (ConcreteCategory.hom (((Φ g).hom 2 le_rfl).f (n, 0)) z)
        (SpectralSequence.edgeEpiSteps_map_apply_eq_zero (Φ g) (p, q) (n, 0) 2
          (r - 1) hr' le_rfl hr' z zz hzz hg)
      exact ⟨M, relComp g g',
        (rel_map_comp_apply E Φ relComp hrelComp 2 le_rfl g g' (n, 0) z).trans hg'⟩

/-- **For a `Rel`-shaped family of first-quadrant spectral sequences of abelian groups whose terms
off the bottom row all die after a refinement, the kernel of the edge epimorphism
`E₂^{n,0} ⟶ E_∞^{n,0}` dies after a refinement.**

`exists_rel_map_pageTwo_eq_zero` at the page `n + 2`, from which the position `(n, 0)` is stable:
the differentials into it come from `(n - r, r - 1)` and those out of it go to `(n + r, 1 - r)`,
both outside the first quadrant for `r > n + 1`. -/
theorem exists_rel_map_eq_zero_of_edgeEpi_apply_eq_zero
    (E : D → CohomologicalSpectralSequenceNat AddCommGrpCat.{t} 2)
    (Φ : ∀ {K L : D}, Rel K L → (E K ⟶ E L))
    (relComp : ∀ {K L M : D}, Rel K L → Rel L M → Rel K M)
    (hrelComp : ∀ {K L M : D} (g₁ : Rel K L) (g₂ : Rel L M),
      Φ (relComp g₁ g₂) = Φ g₁ ≫ Φ g₂)
    (relId : ∀ K : D, Rel K K) (n : ℕ)
    (hdeg : ∀ (q : ℕ), 0 < q → ∀ (r : ℤ) (hr : 2 ≤ r) (p : ℕ) (K : D)
      (x : ToType (((E K).page r hr).X (p, q))),
      ∃ (L : D) (g : Rel K L), ConcreteCategory.hom (((Φ g).hom r hr).f (p, q)) x = 0)
    (K : D) (z : ToType (((E K).page 2 le_rfl).X (n, 0)))
    (hz : ConcreteCategory.hom ((E K).edgeEpi (n, 0) 2) z = 0) :
    ∃ (L : D) (g : Rel K L),
      ConcreteCategory.hom (((Φ g).hom 2 le_rfl).f (n, 0)) z = 0 := by
  have : (E K).HasEdgeMonoAtFrom (n, 0) ((n : ℤ) + 2) :=
    hasEdgeMonoAtFrom (E K) (n, 0) ((n : ℤ) + 2)
  have : (E K).HasEdgeEpiAtFrom (n, 0) ((n : ℤ) + 2) :=
    hasEdgeEpiAtFrom (E K) (n, 0) ((n : ℤ) + 2)
  exact exists_rel_map_pageTwo_eq_zero E Φ relComp hrelComp relId n hdeg n ((n : ℤ) + 2)
    (by omega) (by omega) K z
    (SpectralSequence.edgeEpiSteps_apply_eq_zero_of_edgeEpi_apply_eq_zero (n, 0) 2
      ((n : ℤ) + 2) (by omega) z hz)

end CategoryTheory.CohomologicalSpectralSequenceNat

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-! ### Element-level steps between bare objects of `AddCommGrpCat` -/

/-- **A triangle of morphisms of abelian groups, read on an element that the composite kills.** -/
lemma hom_apply_eq_zero_of_comp_eq {A B D : AddCommGrpCat.{t}} {f : A ⟶ B} {g : B ⟶ D}
    {k : A ⟶ D} (e : f ≫ g = k) {x : ToType A} (hx : ConcreteCategory.hom k x = 0) :
    ConcreteCategory.hom g (ConcreteCategory.hom f x) = 0 :=
  (ConcreteCategory.comp_apply f g x).symm.trans ((ConcreteCategory.congr_hom e x).trans hx)

/-- **A square of morphisms of abelian groups whose right-hand side is a monomorphism, read on an
element the other way round kills.** -/
lemma hom_apply_eq_zero_of_mono_of_comp_eq {A A' B B' : AddCommGrpCat.{t}} {m : A ⟶ A'}
    {wTarget : A' ⟶ B'} {wSource : A ⟶ B} {φ : B ⟶ B'} (hmono : Mono wTarget)
    (e : m ≫ wTarget = wSource ≫ φ) {x : ToType A}
    (hx : ConcreteCategory.hom φ (ConcreteCategory.hom wSource x) = 0) :
    ConcreteCategory.hom m x = 0 := by
  refine (AddCommGrpCat.mono_iff_injective wTarget).1 hmono ?_
  rw [map_zero, ← ConcreteCategory.comp_apply, e, ConcreteCategory.comp_apply]
  exact hx

/-- **A triangle of morphisms of abelian groups whose second leg is a monomorphism, read on an
element the composite kills.** -/
lemma hom_apply_eq_zero_of_mono_comp {A B D : AddCommGrpCat.{t}} {f : A ⟶ B} {g : B ⟶ D}
    (hmono : Mono g) {k : A ⟶ D} (e : f ≫ g = k) {x : ToType A}
    (hx : ConcreteCategory.hom k x = 0) : ConcreteCategory.hom f x = 0 := by
  refine hom_apply_eq_zero_of_mono_of_comp_eq (wSource := k) (φ := 𝟙 D) hmono
    (by rw [e, Category.comp_id]) (by simpa using hx)

/-- **A chain of morphisms of abelian groups whose last two legs are monomorphisms, read on an
element the whole composite kills.** -/
lemma hom_apply_eq_zero_of_mono_mono_comp {A B B₁ B' D : AddCommGrpCat.{t}} {f₁ : A ⟶ B}
    {f₂ : B ⟶ B₁} {m : B₁ ⟶ B'} {g : B' ⟶ D} (hm : Mono m) (hg : Mono g) {k : A ⟶ D}
    (e : f₁ ≫ (f₂ ≫ m) ≫ g = k) {x : ToType A}
    (hx : ConcreteCategory.hom k x = 0) :
    ConcreteCategory.hom f₂ (ConcreteCategory.hom f₁ x) = 0 := by
  have e' : (f₁ ≫ f₂) ≫ m ≫ g = k := by
    rw [← e]
    simp only [Category.assoc]
  have h0 : ConcreteCategory.hom (f₁ ≫ f₂) x = 0 :=
    hom_apply_eq_zero_of_mono_comp (mono_comp' hm hg) e' hx
  exact (ConcreteCategory.comp_apply f₁ f₂ x).symm.trans h0

/-- **Two elements of abelian groups with the same image along two maps into a common group have
difference zero there**, read through two triangles. -/
lemma hom_sub_apply_eq_zero_of_comp_eq {A A' B D : AddCommGrpCat.{t}} {f : A ⟶ B} {f' : A' ⟶ B}
    {e : B ⟶ D} {k : A ⟶ D} {k' : A' ⟶ D} (hf : f ≫ e = k) (hf' : f' ≫ e = k')
    {x : ToType A} {y : ToType A'}
    (h : ConcreteCategory.hom k x = ConcreteCategory.hom k' y) :
    ConcreteCategory.hom e
      (ConcreteCategory.hom f x - ConcreteCategory.hom f' y) = 0 := by
  rw [map_sub, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hf, hf', h, sub_self]

/-- **Two elements of abelian groups whose difference is killed by a further map have the same
image along the two composites.**  This is the converse direction of
`hom_sub_apply_eq_zero_of_comp_eq`. -/
lemma hom_apply_eq_of_hom_sub_apply_eq_zero {A A' B B' : AddCommGrpCat.{t}} {f : A ⟶ B}
    {f' : A' ⟶ B} {p : B ⟶ B'} {k : A ⟶ B'} {k' : A' ⟶ B'} (hk : f ≫ p = k) (hk' : f' ≫ p = k')
    {x : ToType A} {y : ToType A'}
    (h : ConcreteCategory.hom p
      (ConcreteCategory.hom f x - ConcreteCategory.hom f' y) = 0) :
    ConcreteCategory.hom k x = ConcreteCategory.hom k' y := by
  rw [map_sub, sub_eq_zero] at h
  rw [← hk, ← hk', ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact h

/-- **A square of morphisms of abelian groups whose two vertical sides are isomorphisms, read on
an element the top side kills.** -/
lemma hom_apply_eq_zero_of_comp_eq_of_iso {A A' B B' : AddCommGrpCat.{t}} {φ : A ⟶ B}
    {eA : A ≅ A'} {eB : B ≅ B'} {g : A' ⟶ B'} (e : φ ≫ eB.hom = eA.hom ≫ g) {y : ToType A'}
    (hy : ConcreteCategory.hom φ (ConcreteCategory.hom eA.inv y) = 0) :
    ConcreteCategory.hom g y = 0 := by
  have hinv : ConcreteCategory.hom eA.hom (ConcreteCategory.hom eA.inv y) = y := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  have key := ConcreteCategory.congr_hom e (ConcreteCategory.hom eA.inv y)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hy, map_zero, hinv] at key
  exact key.symm

/-! ### Locally zero presheaves of abelian groups -/

/-- **A presheaf of abelian groups is locally zero** when every one of its sections, over every
object of the site, is killed by restriction along every member of some covering family of that
object.  There is no size restriction on the site or on the coefficients. -/
def IsLocallyZeroPresheaf (J : Pretopology C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{t}) : Prop :=
  ∀ (U : C) (ξ : ToType (P.obj (op U))), ∃ R ∈ J U,
    ∀ ⦃Y : C⦄ (g : Y ⟶ U), R g → ConcreteCategory.hom (P.map g.op) ξ = 0

/-- **Being locally zero is invariant under isomorphism of presheaves.** -/
lemma IsLocallyZeroPresheaf.of_iso {J : Pretopology C} {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{t}}
    (hP : IsLocallyZeroPresheaf J P) (e : P ≅ Q) : IsLocallyZeroPresheaf J Q := by
  intro U ξ
  obtain ⟨R, hR, hR0⟩ := hP U (ConcreteCategory.hom (e.inv.app (op U)) ξ)
  exact ⟨R, hR, fun {Y} g hg ↦ hom_apply_eq_zero_of_mono_of_comp_eq
    (wTarget := e.inv.app (op Y)) inferInstance (e.inv.naturality g.op) (hR0 g hg)⟩

/-! ### Local vanishing of the homology of an injective resolution -/

section Locality

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

omit [HasPullbacks C] in
/-- **A section of a presheaf of abelian groups whose sheafification is zero dies on a covering
sieve**: the unit of sheafification is locally injective, so the equalizer sieve of the section
and zero is covering. -/
lemma exists_sieve_apply_eq_zero_of_isZero_presheafToSheaf (P : Cᵒᵖ ⥤ AddCommGrpCat.{t})
    (hz : IsZero ((presheafToSheaf J AddCommGrpCat.{t}).obj P)) (U : C)
    (η : ToType (P.obj (op U))) :
    ∃ S ∈ J U, ∀ ⦃Y : C⦄ (g : Y ⟶ U), S g →
      ConcreteCategory.hom (P.map g.op) η = 0 := by
  have h0 : ConcreteCategory.hom ((toSheafify J P).app (op U)) η = 0 := by
    have hzsh : IsZero (sheafify J P) :=
      Functor.map_isZero (sheafToPresheaf J AddCommGrpCat.{t}) hz
    have hzU : IsZero ((sheafify J P).obj (op U)) :=
      Functor.map_isZero ((evaluation Cᵒᵖ AddCommGrpCat.{t}).obj (op U)) hzsh
    have hsub : Subsingleton (ToType ((sheafify J P).obj (op U))) := by
      rw [AddCommGrpCat.isZero_iff_subsingleton] at hzU
      exact hzU
    exact Subsingleton.elim _ _
  have hli : Presheaf.IsLocallyInjective J (toSheafify J P) := inferInstance
  have hmem : Presheaf.equalizerSieve (F := P) (X := op U) η 0 ∈ J U := by
    refine hli.equalizerSieve_mem η 0 ?_
    rw [h0, map_zero]
  refine ⟨_, hmem, fun {Y} g hg ↦ ?_⟩
  have hg' : ConcreteCategory.hom (P.map g.op) η = ConcreteCategory.hom (P.map g.op) 0 := hg
  rw [hg', map_zero]

/-- **The complex of sections of an injective resolution of an abelian sheaf**: the cocomplex of
the resolution read as a complex of presheaves. -/
abbrev resolutionSectionComplex (G : Sheaf J AddCommGrpCat.{t}) (I : InjectiveResolution G) :
    CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{t}) ℕ :=
  ((sheafToPresheaf J AddCommGrpCat.{t}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex

omit [HasPullbacks C] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- **The sheafification of a positive-degree homology presheaf of the complex of sections of an
injective resolution is zero.**  Sheafification is exact, so it computes the homology of the
cocomplex of the resolution in the abelian sheaves, which is zero in positive degree because the
cocomplex is a resolution. -/
lemma isZero_presheafToSheaf_homology_resolutionSectionComplex
    (G : Sheaf J AddCommGrpCat.{t}) (I : InjectiveResolution G) (n : ℕ) (hn : 0 < n) :
    IsZero ((presheafToSheaf J AddCommGrpCat.{t}).obj
      ((resolutionSectionComplex J G I).homology n)) := by
  have e1 : (presheafToSheaf J AddCommGrpCat.{t}).obj
        ((resolutionSectionComplex J G I).homology n) ≅
      (((presheafToSheaf J AddCommGrpCat.{t}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (resolutionSectionComplex J G I)).homology n :=
    (ShortComplex.mapHomologyIso ((resolutionSectionComplex J G I).sc n)
      (presheafToSheaf J AddCommGrpCat.{t})).symm
  have ecpx : ((presheafToSheaf J AddCommGrpCat.{t}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (resolutionSectionComplex J G I) ≅ I.cocomplex := by
    refine (?_ : _ ≅ ((𝟭 (Sheaf J AddCommGrpCat.{t})).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex) ≪≫ ?_
    · exact ((NatIso.mapHomologicalComplex (sheafificationNatIso J AddCommGrpCat.{t})
        (ComplexShape.up ℕ)).app I.cocomplex).symm
    · exact (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℕ)).app I.cocomplex
  have e2 : (((presheafToSheaf J AddCommGrpCat.{t}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (resolutionSectionComplex J G I)).homology n ≅
      I.cocomplex.homology n :=
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso ecpx
  have ezero : IsZero (I.cocomplex.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact I.cocomplex_exactAt_succ m
  exact IsZero.of_iso ezero (e1 ≪≫ e2)

omit [HasPullbacks C] in
/-- **For `n > 0` every section of the `n`-th homology presheaf of the complex of sections of an
injective resolution of an abelian sheaf is killed on a covering sieve**, with the site not
assumed small and the coefficients in any universe.  The section dies in the sheafification,
which is zero (`isZero_presheafToSheaf_homology_resolutionSectionComplex`), and the unit of
sheafification is locally injective, so the equalizer sieve of the section and zero is
covering. -/
theorem exists_sieve_apply_eq_zero_of_injectiveResolution
    (G : Sheaf J AddCommGrpCat.{t}) (I : InjectiveResolution G) (n : ℕ) (hn : 0 < n) (U : C)
    (η : ToType (((resolutionSectionComplex J G I).homology n).obj (op U))) :
    ∃ S ∈ J U, ∀ ⦃Y : C⦄ (g : Y ⟶ U), S g →
      ConcreteCategory.hom (((resolutionSectionComplex J G I).homology n).map g.op) η = 0 :=
  exists_sieve_apply_eq_zero_of_isZero_presheafToSheaf J _
    (isZero_presheafToSheaf_homology_resolutionSectionComplex J G I n hn) U η

end Locality

section LocalityPretopology

variable (J : Pretopology C) [HasSheafify J.toGrothendieck AddCommGrpCat.{t}]
  [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **For a pretopology and `n > 0`, the `n`-th homology presheaf of the complex of sections of
an injective resolution of an abelian sheaf is locally zero.**  A covering sieve of the topology
generated by a pretopology contains a covering family of that pretopology
(`Pretopology.mem_toGrothendieck`). -/
lemma isLocallyZeroPresheaf_homology_resolutionSectionComplex
    (G : Sheaf J.toGrothendieck AddCommGrpCat.{t}) (I : InjectiveResolution G) (n : ℕ)
    (hn : 0 < n) :
    IsLocallyZeroPresheaf J
      ((resolutionSectionComplex J.toGrothendieck G I).homology n) := by
  intro U η
  obtain ⟨S, hS, hS0⟩ :=
    exists_sieve_apply_eq_zero_of_injectiveResolution J.toGrothendieck G I n hn U η
  obtain ⟨R, hRmem, hRle⟩ := (Pretopology.mem_toGrothendieck J U S).1 hS
  exact ⟨R, hRmem, fun {Y} g hg ↦ hS0 g (hRle _ _ hg)⟩

/-- **The coefficient presheaf on the second page of the hypercovering spectral sequence is
locally zero off the bottom row**: for `q > 0` the `q`-th right derived functor of the inclusion
of abelian sheaves into presheaves, evaluated at a sheaf, is locally zero.  A chosen injective
resolution computes the right derived functor
(`CategoryTheory.InjectiveResolution.isoRightDerivedObj`), and local vanishing is invariant under
isomorphism of presheaves. -/
lemma isLocallyZeroPresheaf_rightDerived
    [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{t})]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{t}) (q : ℕ) (hq : 0 < q) :
    IsLocallyZeroPresheaf J
      (((sheafToPresheaf J.toGrothendieck AddCommGrpCat.{t}).rightDerived q).obj F) :=
  (isLocallyZeroPresheaf_homology_resolutionSectionComplex J F (injectiveResolution F) q
    hq).of_iso
      ((injectiveResolution F).isoRightDerivedObj
        (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{t}) q).symm

end LocalityPretopology

/-! ### A Čech class with locally zero coefficients dies on a refinement -/

section CechBase

variable [HasEqualizers C] [HasBinaryProducts C] (J : Pretopology C)

omit [HasBinaryProducts C] in
/-- **A refinement of a hypercovering of the final presheaf whose underlying simplicial object is
equal to `R` is a morphism of hypercoverings**: a morphism `f : R ⟶ H` whose degree-`k` component
factors through `u` gives a morphism `H' ⟶ H` whose degree-`k` component factors through `u`. -/
lemma exists_hom_of_toSimplicialObject_eq {H H' : HypercoveringOfTerminal.{w} J}
    {R : SimplicialObject (FormalCoproduct.{w} C)} (hR : H'.toSimplicialObject = R)
    (k : ℕ) {Z : FormalCoproduct.{w} C} (u : Z ⟶ H.toSimplicialObject.obj (op ⦋k⦌))
    (f : R ⟶ H.toSimplicialObject) (g : R.obj (op ⦋k⦌) ⟶ Z)
    (hfg : g ≫ u = f.app (op ⦋k⦌)) :
    ∃ (ψ : H'.Hom H) (g' : H'.toSimplicialObject.obj (op ⦋k⦌) ⟶ Z),
      g' ≫ u = ψ.simplicialHom.app (op ⦋k⦌) := by
  subst hR
  exact ⟨homOfSimplicialHom.{w} f, g, hfg⟩

/-- **A covering of the term of a hypercovering of the final presheaf in a fixed degree can be
incorporated into a refinement** `ψ : H' ⟶ H`, a morphism of hypercoverings whose component in
that degree factors through the covering. -/
@[sga "4 V 7.3.2" "clause 2, special case"]
theorem exists_hom_factoring_through_covering
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (H : HypercoveringOfTerminal.{max u v w} J) (k : ℕ)
    {Z : FormalCoproduct.{max u v w} C} (u : Z ⟶ H.toSimplicialObject.obj (op ⦋k⦌))
    (hu : IsCovering J u) :
    ∃ (H' : HypercoveringOfTerminal.{max u v w} J) (ψ : H'.Hom H)
      (g : H'.toSimplicialObject.obj (op ⦋k⦌) ⟶ Z),
      g ≫ u = ψ.simplicialHom.app (op ⦋k⦌) := by
  obtain ⟨H', hH', f, g, hfg⟩ :=
    exists_hypercoveringOfTerminal_map_factoring_through_covering.{w} J H k u hu
  obtain ⟨ψ, g', hg'⟩ := exists_hom_of_toSimplicialObject_eq J hH' k u f g hfg
  exact ⟨H', ψ, g', hg'⟩

/-- **Every Čech cohomology class of a hypercovering of the final presheaf with locally zero
coefficients dies after a refinement.**

The class is lifted to a cocycle, a section of `P` on `K_p`; local vanishing of `P` kills each of
its components on a covering of the corresponding summand; those coverings assemble into a
covering morphism `u : Z ⟶ K_p` (`exists_isCovering_of_presieves`) along which the whole cocycle
restricts to zero; and `exists_hom_factoring_through_covering` produces a refinement whose
degree-`p` component factors through `u`, on which the class therefore dies
(`homologyπ_cochainComplexFunctorMap_eq_zero`). -/
theorem exists_hom_presheafCechCohomologyFunctorMap_apply_eq_zero
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max (max u v) (max v w)})
    (hP : IsLocallyZeroPresheaf J P) (K : HypercoveringOfTerminal.{max u v w} J) (p : ℕ)
    (x : ToType ((presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K p).obj P)) :
    ∃ (L : HypercoveringOfTerminal.{max u v w} J) (ψ : L.Hom K),
      ConcreteCategory.hom
        ((presheafCechCohomologyFunctorMap J (⊤_ (Cᵒᵖ ⥤ Type v)) ψ p).app P) x = 0 := by
  classical
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective
    (((FormalCoproduct.cochainComplexFunctor K.toSimplicialObject).obj P).homologyπ p)).1
      inferInstance x
  choose R hR hR0 using fun i : (K.toSimplicialObject.obj (op ⦋p⦌)).I ↦
    hP ((K.toSimplicialObject.obj (op ⦋p⦌)).obj i)
      (ConcreteCategory.hom (evalBaseπ P (K.toSimplicialObject.obj (op ⦋p⦌)) i)
        (ConcreteCategory.hom
          (((FormalCoproduct.cochainComplexFunctor K.toSimplicialObject).obj P).iCycles p) z))
  obtain ⟨Z, u, hu, hmem⟩ :=
    exists_isCovering_of_presieves J (K.toSimplicialObject.obj (op ⦋p⦌)) R hR
  obtain ⟨L, ψ, g, hfg⟩ := exists_hom_factoring_through_covering.{w} J K p u hu
  refine ⟨L, ψ, ?_⟩
  rw [← hz]
  exact homologyπ_cochainComplexFunctorMap_eq_zero P ψ.simplicialHom p u g hfg z
    (fun i ↦ hR0 (u.f i) (u.φ i) (hmem i))

end CechBase

/-! ### The spectral sequence of a hypercovering of the final presheaf as a `Rel`-shaped family -/

section Family

variable [HasEqualizers C] [HasBinaryProducts C] (J : Pretopology C)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]
  (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})

/-- **The hypercovering spectral sequence at the final presheaf and a fixed coefficient sheaf, as
a family indexed by the hypercoverings of the final presheaf.** -/
abbrev globalSpectralSequenceAt (K : HypercoveringOfTerminal.{w} J) :
    E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max (max u v) (max v w)} :=
  (hypercoverPresheafSpectralSequenceFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K).obj F

/-- **A refinement of hypercoverings of the final presheaf induces a morphism of their spectral
sequences**, contravariantly: `hypercoverPresheafSpectralSequenceFunctorMap` at a fixed
coefficient sheaf. -/
@[sga "4 V 7.4.0" "partial"]
abbrev globalSpectralSequenceAtMap {K L : HypercoveringOfTerminal.{w} J} (ψ : L.Hom K) :
    globalSpectralSequenceAt.{w} J F K ⟶ globalSpectralSequenceAt.{w} J F L :=
  (hypercoverPresheafSpectralSequenceFunctorMap.{v, w, v, u} J
    (⊤_ (Cᵒᵖ ⥤ Type v)) ψ.simplicialHom).app F

omit [HasBinaryProducts C] in
/-- The identity refinement induces the identity morphism of spectral sequences. -/
@[sga "4 V 7.4.0" "partial"]
lemma globalSpectralSequenceAtMap_id (K : HypercoveringOfTerminal.{w} J) :
    globalSpectralSequenceAtMap.{w} J F (homOfSimplicialHom.{w} (𝟙 _) : K.Hom K) =
      𝟙 _ :=
  congrArg (fun t ↦ NatTrans.app t F)
    (hypercoverPresheafSpectralSequenceFunctorMap_id.{v, w, v, u} J
      (⊤_ (Cᵒᵖ ⥤ Type v)) K)

omit [HasBinaryProducts C] in
/-- **Composing two refinements composes the induced morphisms of spectral sequences**, in the
reverse order. -/
@[sga "4 V 7.4.0" "partial"]
lemma globalSpectralSequenceAtMap_comp {K L M : HypercoveringOfTerminal.{w} J}
    (ψ : L.Hom K) (χ : M.Hom L) :
    globalSpectralSequenceAtMap.{w} J F (χ.comp ψ) =
      globalSpectralSequenceAtMap.{w} J F ψ ≫ globalSpectralSequenceAtMap.{w} J F χ :=
  congrArg (fun t ↦ NatTrans.app t F)
    (hypercoverPresheafSpectralSequenceFunctorMap_comp.{v, w, v, u} J
      (⊤_ (Cᵒᵖ ⥤ Type v)) χ.simplicialHom ψ.simplicialHom)

/-- **The second page of the hypercovering spectral sequence at the final presheaf and `(p, q')`
is `Ȟ^p(K, H̲^{q'}(F))`**: the component at `F` of `hypercoverPresheafPageTwoIso`. -/
def globalPageTwoIso (p q' : ℕ) (K : HypercoveringOfTerminal.{w} J) :
    ((globalSpectralSequenceAt.{w} J F K).page 2 le_rfl).X (p, q') ≅
      (presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K p).obj
        (((sheafToPresheaf J.toGrothendieck
          AddCommGrpCat.{max (max u v) (max v w)}).rightDerived q').obj F) :=
  (hypercoverPresheafPageTwoIso J (⊤_ (Cᵒᵖ ⥤ Type v)) K p q').app F

omit [HasBinaryProducts C] in
/-- `globalPageTwoIso` is natural in the hypercovering. -/
lemma globalPageTwoIso_naturality (p q' : ℕ) {K L : HypercoveringOfTerminal.{w} J}
    (ψ : L.Hom K) :
    ((globalSpectralSequenceAtMap.{w} J F ψ).hom 2 le_rfl).f (p, q') ≫
        (globalPageTwoIso.{w} J F p q' L).hom =
      (globalPageTwoIso.{w} J F p q' K).hom ≫
        (presheafCechCohomologyFunctorMap J (⊤_ (Cᵒᵖ ⥤ Type v)) ψ p).app
          (((sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max v w)}).rightDerived q').obj F) :=
  ψ.hypercoverPresheafPageTwoIso_naturality J (⊤_ (Cᵒᵖ ⥤ Type v)) p q' F

/-- **Every element of the second page `E₂^{p,q'}` of the spectral sequence of a hypercovering of
the final presheaf dies after a refinement**, for `q' > 0`.  The coefficient presheaf is locally
zero off the bottom row (`isLocallyZeroPresheaf_rightDerived`), a Čech class with locally zero
coefficients dies on a refinement
(`exists_hom_presheafCechCohomologyFunctorMap_apply_eq_zero`), and the second-page
identification is natural in the hypercovering (`globalPageTwoIso_naturality`). -/
theorem exists_hom_pageTwo_apply_eq_zero
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max (max u v) (max v w)}]
    [Precoverage.IsStableUnderComposition J.toPrecoverage] (q' : ℕ) (hq' : 0 < q') (p : ℕ)
    (K : HypercoveringOfTerminal.{max u v w} J)
    (x : ToType (((globalSpectralSequenceAt.{max u v w} J F K).page 2 le_rfl).X (p, q'))) :
    ∃ (L : HypercoveringOfTerminal.{max u v w} J) (ψ : L.Hom K),
      ConcreteCategory.hom
        (((globalSpectralSequenceAtMap.{max u v w} J F ψ).hom 2 le_rfl).f (p, q')) x = 0 := by
  obtain ⟨L, ψ, hψ⟩ := exists_hom_presheafCechCohomologyFunctorMap_apply_eq_zero.{w} J _
    (isLocallyZeroPresheaf_rightDerived J F q' hq') K p
    (ConcreteCategory.hom (globalPageTwoIso.{max u v w} J F p q' K).hom x)
  exact ⟨L, ψ, hom_apply_eq_zero_of_mono_of_comp_eq inferInstance
    (globalPageTwoIso_naturality.{max u v w} J F p q' ψ) hψ⟩

section Degeneration

variable [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max (max u v) (max v w)}]
  [Precoverage.IsStableUnderComposition J.toPrecoverage]

/-- **For `q' > 0` and every page `r ≥ 2`, every element of `E_r^{p,q'}` of the spectral sequence
of a hypercovering of the final presheaf dies after a refinement.** -/
theorem exists_hom_page_apply_eq_zero (q' : ℕ) (hq' : 0 < q') (r : ℤ) (hr : 2 ≤ r) (p : ℕ)
    (K : HypercoveringOfTerminal.{max u v w} J)
    (x : ToType (((globalSpectralSequenceAt.{max u v w} J F K).page r hr).X (p, q'))) :
    ∃ (L : HypercoveringOfTerminal.{max u v w} J) (ψ : L.Hom K),
      ConcreteCategory.hom
        (((globalSpectralSequenceAtMap.{max u v w} J F ψ).hom r hr).f (p, q')) x = 0 :=
  CategoryTheory.SpectralSequence.exists_rel_page_apply_eq_zero
    (globalSpectralSequenceAt.{max u v w} J F) (globalSpectralSequenceAtMap.{max u v w} J F) (p, q')
    (fun K x ↦ exists_hom_pageTwo_apply_eq_zero.{w} J F q' hq' p K x) r hr K x

/-- **For `q' > 0` every element of the infinity page `E_∞^{p,q'}` of the spectral sequence of a
hypercovering of the final presheaf dies after a refinement.** -/
theorem exists_hom_pageInfinity_apply_eq_zero (q' : ℕ) (hq' : 0 < q') (p : ℕ)
    (K : HypercoveringOfTerminal.{max u v w} J)
    (x : ToType ((globalSpectralSequenceAt.{max u v w} J F K).pageInfinity (p, q'))) :
    ∃ (L : HypercoveringOfTerminal.{max u v w} J) (ψ : L.Hom K),
      ConcreteCategory.hom (CategoryTheory.SpectralSequence.Hom.mapPageInfinity
        (globalSpectralSequenceAtMap.{max u v w} J F ψ) (p, q')) x = 0 :=
  CategoryTheory.SpectralSequence.exists_rel_pageInfinity_apply_eq_zero
    (globalSpectralSequenceAt.{max u v w} J F) (p, q') (globalSpectralSequenceAtMap.{max u v w} J F)
    (fun K x ↦ exists_hom_pageTwo_apply_eq_zero.{w} J F q' hq' p K x) K x

end Degeneration

end Family

/-! ### The canonical comparison as the bottom row of the second page -/

section Edge

variable [HasEqualizers C] [HasBinaryProducts C] (J : Pretopology C)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]
  [HasExt.{max (max u v) (max v w)}
    (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})]
  (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})

/-- **The Čech cohomology of a hypercovering of the final presheaf is the bottom row of the second
page of its spectral sequence**: the degree-zero coefficient identification followed by the
inverse of the second-page identification `globalPageTwoIso`. -/
abbrev cechToPageTwoZero (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :=
  (presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K i).map
      ((sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{max (max u v) (max v w)}).rightDerivedZeroIsoSelf.inv.app F) ≫
    (globalPageTwoIso.{w} J F i 0 K).inv

/-- `cechToPageTwoZero` is an isomorphism: both of its factors are. -/
lemma isIso_cechToPageTwoZero (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    IsIso (cechToPageTwoZero.{w} J F K i) := by
  have h₁ : IsIso ((presheafCechCohomologyFunctor J (⊤_ (Cᵒᵖ ⥤ Type v)) K i).map
      ((sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{max (max u v) (max v w)}).rightDerivedZeroIsoSelf.inv.app F)) :=
    inferInstance
  have h₂ : IsIso ((globalPageTwoIso.{w} J F i 0 K).inv) := inferInstance
  exact IsIso.comp_isIso' h₁ h₂

/-- **The canonical comparison `globalCechEdge` is `cechToPageTwoZero` followed by the bottom-row
edge map of the abutment.** -/
lemma cechToPageTwoZero_comp_bottomRowEdge (K : HypercoveringOfTerminal.{w} J)
    (i : ℕ) :
    cechToPageTwoZero.{w} J F K i ≫ ((globalAbutment J K).bottomRowEdge i).app F =
      (globalCechEdge.{w} J K i).app F :=
  (Category.assoc _ _ _).trans (globalCechEdge_app J K i F).symm

omit [HasBinaryProducts C]
  [HasExt (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})] in
/-- **`cechToPageTwoZero` is natural in the hypercovering**: the Čech pullback corresponds to the
map a refinement induces on the second page at `(i, 0)`.

The degree-zero coefficient identification moves past the Čech pullback by the naturality of the
latter in the coefficient presheaf, and the second-page identification by
`HypercoveringOf.Hom.hypercoverPresheafPageTwoIso_naturality` read in the inverse direction. -/
lemma cechCohomologyFunctorMap_comp_cechToPageTwoZero
    {K L : HypercoveringOfTerminal.{w} J} (ψ : L.Hom K) (i : ℕ) :
    (presheafCechCohomologyFunctorMap J (⊤_ (Cᵒᵖ ⥤ Type v)) ψ i).app
          ((sheafToPresheaf J.toGrothendieck
            AddCommGrpCat.{max (max u v) (max v w)}).obj F) ≫
        cechToPageTwoZero.{w} J F L i =
      cechToPageTwoZero.{w} J F K i ≫
        ((globalSpectralSequenceAtMap.{w} J F ψ).hom 2 le_rfl).f (i, 0) := by
  have hA := ((presheafCechCohomologyFunctorMap J (⊤_ (Cᵒᵖ ⥤ Type v)) ψ i).naturality
    ((sheafToPresheaf J.toGrothendieck
      AddCommGrpCat.{max (max u v) (max v w)}).rightDerivedZeroIsoSelf.inv.app F)).symm
  have hB := StacksDraft.DerivedSectionsComparison.inv_comp_eq_comp_inv
    (globalPageTwoIso.{w} J F i 0 K) (globalPageTwoIso.{w} J F i 0 L)
    (((globalSpectralSequenceAtMap.{w} J F ψ).hom 2 le_rfl).f (i, 0))
    ((presheafCechCohomologyFunctorMap J (⊤_ (Cᵒᵖ ⥤ Type v)) ψ i).app
      (((sheafToPresheaf J.toGrothendieck
        AddCommGrpCat.{max (max u v) (max v w)}).rightDerived 0).obj F))
    (globalPageTwoIso_naturality.{w} J F i 0 ψ)
  rw [← Category.assoc, hA]
  simp only [Category.assoc]
  rw [← hB]

/-- `cechToPageTwoZero` is a monomorphism, being an isomorphism. -/
lemma mono_cechToPageTwoZero (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    Mono (cechToPageTwoZero.{w} J F K i) := by
  have := isIso_cechToPageTwoZero.{w} J F K i
  infer_instance

/-- **The canonical comparison `globalCechEdge` factors as `cechToPageTwoZero` followed by the
edge epimorphism `E₂^{i,0} ⟶ E_∞^{i,0}` followed by a monomorphism**: the bottom-row edge map of
the abutment, unfolded into its four factors. -/
lemma cechToPageTwoZero_comp_edgeEpi_comp (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    cechToPageTwoZero.{w} J F K i ≫
        (((globalSpectralSequenceAt.{w} J F K).edgeEpi (i, 0) 2 ≫
            ((globalAbutment J K).bottomGradedIso i F).hom) ≫
          ((globalAbutment J K).grIsoEval i).hom.app F ≫
            (((globalAbutment J K).evalHomForget i).app F ≫
              ((globalAbutment J K).abutmentIso i).hom.app F)) =
      (globalCechEdge.{w} J K i).app F := by
  rw [← cechToPageTwoZero_comp_bottomRowEdge.{w} J F K i,
    (globalAbutment J K).bottomRowEdge_app_eq' i F]
  dsimp only [Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo.bottomRowGrHom,
    globalSpectralSequenceAt]
  rfl

/-! ### The canonical comparison with its source written as the Čech cohomology group -/

/-- **`cechToPageTwoZero` with its source written as the Čech cohomology group**
`cechCohomology J ⊤ K 𝓕 i`, the source of the Čech pullback
`HypercoveringOf.Hom.cechCohomologyMap` and of the canonical comparison `cechCohomologyEdge`. -/
def cechCohomologyToPageTwoZero (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) K F i ⟶
      ((globalSpectralSequenceAt.{w} J F K).page 2 le_rfl).X (i, 0) :=
  cechToPageTwoZero.{w} J F K i

/-- `cechCohomologyToPageTwoZero` is a monomorphism, being `cechToPageTwoZero`, which is an
isomorphism. -/
lemma mono_cechCohomologyToPageTwoZero (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    Mono (cechCohomologyToPageTwoZero.{w} J F K i) :=
  mono_cechToPageTwoZero.{w} J F K i

/-- **The canonical comparison `cechCohomologyEdge` factors as `cechCohomologyToPageTwoZero`
followed by the edge epimorphism `E₂^{i,0} ⟶ E_∞^{i,0}` followed by a monomorphism.** -/
lemma cechCohomologyToPageTwoZero_comp_edgeEpi_comp (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    cechCohomologyToPageTwoZero.{w} J F K i ≫
        (((globalSpectralSequenceAt.{w} J F K).edgeEpi (i, 0) 2 ≫
            ((globalAbutment J K).bottomGradedIso i F).hom) ≫
          ((globalAbutment J K).grIsoEval i).hom.app F ≫
            (((globalAbutment J K).evalHomForget i).app F ≫
              ((globalAbutment J K).abutmentIso i).hom.app F)) =
      cechCohomologyEdge.{w} J K i F :=
  cechToPageTwoZero_comp_edgeEpi_comp.{w} J F K i

omit [HasBinaryProducts C]
  [HasExt (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})] in
/-- **`cechCohomologyToPageTwoZero` is natural in the hypercovering**, the Čech pullback being
`HypercoveringOf.Hom.cechCohomologyMap`. -/
lemma cechCohomologyMap_comp_cechCohomologyToPageTwoZero
    {K L : HypercoveringOfTerminal.{w} J} (ψ : L.Hom K) (i : ℕ) :
    ψ.cechCohomologyMap F i ≫ cechCohomologyToPageTwoZero.{w} J F L i =
      cechCohomologyToPageTwoZero.{w} J F K i ≫
        ((globalSpectralSequenceAtMap.{w} J F ψ).hom 2 le_rfl).f (i, 0) :=
  cechCohomologyFunctorMap_comp_cechToPageTwoZero.{w} J F ψ i

omit [HasBinaryProducts C] in
/-- **The tail of the factorisation of the canonical comparison past the edge epimorphism is a
monomorphism**: the graded identification, the identification of `gr^i H^i` with the filtration
step `F^i H^i`, the inclusion of that step and the abutment identification.  All but the third
are isomorphisms, and the third is a filtration inclusion. -/
lemma mono_edgeEpi_tail (K : HypercoveringOfTerminal.{w} J) (i : ℕ) :
    Mono (((globalAbutment J K).grIsoEval i).hom.app F ≫
      (((globalAbutment J K).evalHomForget i).app F ≫
        ((globalAbutment J K).abutmentIso i).hom.app F)) :=
  mono_comp' (IsIso.mono_of_iso (((globalAbutment J K).grIsoEval i).hom.app F))
    (mono_comp' ((globalAbutment J K).mono_evalHomForget_app i F)
      (IsIso.mono_of_iso (((globalAbutment J K).abutmentIso i).hom.app F)))

/-- **A Čech class that the canonical comparison `cechCohomologyEdge` kills is killed, after
`cechCohomologyToPageTwoZero`, by the edge epimorphism `E₂^{i,0} ⟶ E_∞^{i,0}` of the second
page.** -/
lemma edgeEpi_apply_cechCohomologyToPageTwoZero_apply_eq_zero
    (K : HypercoveringOfTerminal.{w} J) (i : ℕ)
    (ξ : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) K F i)
    (hξ : ConcreteCategory.hom (cechCohomologyEdge.{w} J K i F) ξ = 0) :
    ConcreteCategory.hom ((globalSpectralSequenceAt.{w} J F K).edgeEpi (i, 0) 2)
        (ConcreteCategory.hom (cechCohomologyToPageTwoZero.{w} J F K i) ξ) = 0 :=
  hom_apply_eq_zero_of_mono_mono_comp
    (IsIso.mono_of_iso ((globalAbutment J K).bottomGradedIso i F).hom)
    (mono_edgeEpi_tail.{w} J F K i)
    (cechCohomologyToPageTwoZero_comp_edgeEpi_comp.{w} J F K i) hξ

section PartTwo

variable [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max (max u v) (max v w)}]
  [Precoverage.IsStableUnderComposition J.toPrecoverage]

omit [HasExt (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max v w)})] in
/-- **The kernel of the edge epimorphism `E₂^{i,0} ⟶ E_∞^{i,0}` of the spectral sequence of a
hypercovering of the final presheaf dies after a refinement.** -/
theorem exists_hom_pageTwoZero_apply_eq_zero (i : ℕ)
    (K : HypercoveringOfTerminal.{max u v w} J)
    (z : ToType (((globalSpectralSequenceAt.{max u v w} J F K).page 2 le_rfl).X (i, 0)))
    (hz : ConcreteCategory.hom
      ((globalSpectralSequenceAt.{max u v w} J F K).edgeEpi (i, 0) 2) z = 0) :
    ∃ (L : HypercoveringOfTerminal.{max u v w} J) (ψ : L.Hom K),
      ConcreteCategory.hom
        (((globalSpectralSequenceAtMap.{max u v w} J F ψ).hom 2 le_rfl).f (i, 0)) z = 0 :=
  CategoryTheory.CohomologicalSpectralSequenceNat.exists_rel_map_eq_zero_of_edgeEpi_apply_eq_zero
    (globalSpectralSequenceAt.{max u v w} J F) (globalSpectralSequenceAtMap.{max u v w} J F)
    (fun g₁ g₂ ↦ g₂.comp g₁)
    (fun g₁ g₂ ↦ globalSpectralSequenceAtMap_comp.{max u v w} J F g₁ g₂)
    (fun K ↦ (homOfSimplicialHom.{max u v w} (𝟙 _) : K.Hom K)) i
    (fun q hq r hr p K x ↦ exists_hom_page_apply_eq_zero.{w} J F q hq r hr p K x) K z hz

/-- **A Čech class killed by the canonical comparison `Ȟ^i(K, 𝓕) ⟶ H^i(𝓕)` dies after a
refinement of the hypercovering**, in every degree.  The comparison factors as
`cechCohomologyToPageTwoZero` followed by the edge epimorphism `E₂^{i,0} ⟶ E_∞^{i,0}` followed by
a monomorphism (`cechCohomologyToPageTwoZero_comp_edgeEpi_comp`), so the class is killed by that
edge epimorphism; its kernel dies after a refinement (`exists_hom_pageTwoZero_apply_eq_zero`);
and `cechCohomologyToPageTwoZero` is natural in the hypercovering and a monomorphism, so the
vanishing comes back to the Čech side. -/
theorem exists_hom_cechCohomologyMap_apply_eq_zero (i : ℕ)
    (K : HypercoveringOfTerminal.{max u v w} J)
    (ξ : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) K F i)
    (hξ : ConcreteCategory.hom (cechCohomologyEdge.{max u v w} J K i F) ξ = 0) :
    ∃ (L : HypercoveringOfTerminal.{max u v w} J) (ψ : L.Hom K),
      ConcreteCategory.hom (ψ.cechCohomologyMap F i) ξ = 0 := by
  obtain ⟨L, ψ, hψ⟩ := exists_hom_pageTwoZero_apply_eq_zero.{w} J F i K
    (ConcreteCategory.hom (cechCohomologyToPageTwoZero.{max u v w} J F K i) ξ)
    (edgeEpi_apply_cechCohomologyToPageTwoZero_apply_eq_zero.{max u v w} J F K i ξ hξ)
  exact ⟨L, ψ, hom_apply_eq_zero_of_mono_of_comp_eq
    (mono_cechCohomologyToPageTwoZero.{max u v w} J F L i)
    (cechCohomologyMap_comp_cechCohomologyToPageTwoZero.{max u v w} J F ψ i) hψ⟩

/-- **In every degree `i`, two Čech classes in `Ȟ^i(K, 𝓕)` and `Ȟ^i(L, 𝓕)`, for hypercoverings
`K` and `L` of the final presheaf, whose images under the canonical comparison
`Ȟ^i(-, 𝓕) ⟶ H^i(𝓕)` agree restrict to the same class on a common refinement.**

The coefficients are the sheaf `𝓕` itself, not its degree-zero cohomology presheaf.  On the
common refinement `exists_hom_of_prod` the difference of the two restrictions is killed by the
comparison, so it dies after a further refinement (`exists_hom_cechCohomologyMap_apply_eq_zero`),
and on that refinement the two restrictions agree. -/
@[stacks 09VZ "part (2) in every degree, at the hypercovering universe `max u v w`, which is \
what Tag 01GJ forces; the canonical map is the bottom-row edge map of the spectral sequence of \
Tag 09VY, i.e. the comparison of Tag 01GY.  The size binders are those the chapter's \
presheaf-side tags carry -- sheafification, enough injectives and `HasExt` at the coefficient \
universe -- together with `WEqualsLocallyBijective`, a theorem for every essentially small site.  \
See `exists_hom_cechCohomologyEdge_zero_eq` for degree zero at a free universe `w`"]
theorem exists_hom_cechCohomologyEdge_eq (i : ℕ)
    (K L : HypercoveringOfTerminal.{max u v w} J)
    (ξK : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) K F i)
    (ξL : cechCohomology J (⊤_ (Cᵒᵖ ⥤ Type v)) L F i)
    (h : ConcreteCategory.hom (cechCohomologyEdge.{max u v w} J K i F) ξK =
      ConcreteCategory.hom (cechCohomologyEdge.{max u v w} J L i F) ξL) :
    ∃ (M : HypercoveringOfTerminal.{max u v w} J) (f : M.Hom K) (g : M.Hom L),
      ConcreteCategory.hom (f.cechCohomologyMap F i) ξK =
        ConcreteCategory.hom (g.cechCohomologyMap F i) ξL := by
  obtain ⟨M, ⟨f⟩, ⟨g⟩⟩ := exists_hom_of_prod.{max u v w} J K L
  obtain ⟨N, ψ, hψ⟩ := exists_hom_cechCohomologyMap_apply_eq_zero.{w} J F i M _
    (hom_sub_apply_eq_zero_of_comp_eq
      (cechCohomologyMap_comp_cechCohomologyEdge.{max u v w} J f i F)
      (cechCohomologyMap_comp_cechCohomologyEdge.{max u v w} J g i F) h)
  exact ⟨N, ψ.comp f, ψ.comp g, hom_apply_eq_of_hom_sub_apply_eq_zero
    (HypercoveringOf.Hom.cechCohomologyMap_comp ψ f F i).symm
    (HypercoveringOf.Hom.cechCohomologyMap_comp ψ g F i).symm hψ⟩

end PartTwo

end Edge

end Stacks.CategoryTheory.Hypercovering

end
