module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineLocalSpanning

/-!
# Generation by global sections is tested over one covering family

A sheaf of modules on a site with a terminal object is locally spanned by its global sections
when every section lies, after restriction along the arrows of some covering sieve, in the
submodule spanned by the restrictions of the sections over the terminal object.  The condition is
local in a stronger sense than "testable on a covering family of each object": it is testable on
a covering family of the *terminal* object alone, because the sieve of arrows along which a given
section becomes a combination of global sections is a sieve, and a Grothendieck topology is
transitive.

This file records that locality and uses it to confine the condition to the affine objects lying
over one chosen covering family.  On a slice of the fppf site associated with a category fibred in
groupoids, the resulting criterion reads: if a covering family `Y i ⟶ T` of the terminal object is
given and the sections of the module over every *affine* object admitting a morphism to some
`Y i` are spanned by the restrictions of the global sections, then the module is locally spanned
by its global sections.  Compared with
`AlgebraicGeometry.FibredSite.isLocallySpannedBySections_over_of_forall_affine`, which asks for
the span at every affine object of the slice, the affine objects are here restricted to those
sitting over a member of a single covering family — which is what a module known only to be
quasi-coherent provides, since quasi-coherence produces presentations over the members of one
covering of the terminal object and says nothing at the terminal object itself.

The spans compose.  The submodule of sections over `W` spanned by the restrictions of the
sections over `V` along one morphism `W ⟶ V` is `SheafOfModules.sectionSpan`, of which the span of
the global sections is the case of the structural morphism to the terminal object; and if the
sections over `V` are spanned by the restrictions of the sections over `U`, and the sections over
`W` by the restrictions of those over `V`, then the sections over `W` are spanned by the
restrictions of the sections over `U`.  So the criterion splits into two independent inputs: the
span of the global sections at the members of the covering family, and the span of the sections
over a member at the affine objects over that member.  The second is what a global presentation
over a member supplies; the first is the descent statement, and it is the only part that is not
formal.

## Main definitions

* `SheafOfModules.sectionSpan`: the submodule of sections over an object spanned by the
  restrictions of the sections over another along a given morphism.
* `SheafOfModules.IsLocallySpannedBySectionsAt`: the span condition at a single object.

## Main results

* `SheafOfModules.sectionSpan_eq_top_comp`: **spanning by restricted sections is transitive.**
* `SheafOfModules.sectionSpan_eq_top_of_baseChangeEquiv` and
  `SheafOfModules.sectionSpan_eq_top_of_surjective_val_app`: **the two span criteria of
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineLocalSpanning` with
  the terminal object replaced by an arbitrary target**, so that they apply at the members of a
  covering family, where the module is presented but no terminal object is in sight.
* `SheafOfModules.isLocallySpannedBySectionsAt_of_sieve`: **the span condition at an object
  follows from the span condition at the sources of a covering sieve of that object**, which is
  the locality making the criterion below possible.
* `AlgebraicGeometry.FibredSite.isLocallySpannedBySections_over_of_forall_affine_of_cover`:
  **being locally spanned by global sections is a condition at the affine objects lying over the
  members of one covering family of the terminal object.**
* `AlgebraicGeometry.FibredSite.isLocallySpannedBySections_over_of_sectionSpan_eq_top`: the same
  criterion split into the span of the global sections at the members of the family and the span
  of a member's sections at the affine objects over it.
* `AlgebraicGeometry.FibredSite.isGeneratedByUnit_over_of_sectionSpan_eq_top`: the generators half
  of a global presentation from those two inputs.
* `AlgebraicGeometry.FibredSite.hasLocallySpannedRelations_over_of_cover`: the relations half with
  the affine objects likewise restricted to those over the covering family.

## Implementation notes

`SheafOfModules.IsLocallySpannedBySectionsAt` is the body of
`SheafOfModules.IsLocallySpannedBySections` at one object, so that the transitivity of the
topology can be applied object by object; the two are related by
`SheafOfModules.isLocallySpannedBySections_iff_forall_isLocallySpannedBySectionsAt`, which is a
propositional identity.

Memberships are stated for `PresheafOfModules.restrictₛₗ`, the restriction bundled as a semilinear
map, as everywhere in this development: `PresheafOfModules.map` lands in a restriction of scalars
whose additive structure is only definitionally that of the target, so a membership written with
it is not closed by the submodule lemmas.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe w' w v u r m

namespace SheafOfModules

universe uC vC t

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- The submodule of the sections of `N` over `W` spanned by the restrictions along `h : W ⟶ V`
of the sections over `V`.  For `h` the structural morphism to a terminal object this is
`SheafOfModules.globalSectionSpan`. -/
noncomputable def sectionSpan (N : SheafOfModules.{m} R) {V W : C} (h : W ⟶ V) :
    _root_.Submodule (R.obj.obj (op W)) (N.val.obj (op W)) :=
  _root_.Submodule.span _ (Set.range (N.val.restrictₛₗ h.op))

/-- The span of the global sections is the span of the sections over the terminal object along
the structural morphism. -/
lemma globalSectionSpan_eq_sectionSpan {T : C} (hT : IsTerminal T) (N : SheafOfModules.{m} R)
    (W : C) : N.globalSectionSpan hT W = N.sectionSpan (hT.from W) := rfl

/-- A restricted section lies in the span of the sections it is restricted from. -/
lemma restrictₛₗ_mem_sectionSpan (N : SheafOfModules.{m} R) {V W : C} (h : W ⟶ V)
    (n : N.val.obj (op V)) : N.val.restrictₛₗ h.op n ∈ N.sectionSpan h :=
  _root_.Submodule.subset_span ⟨n, rfl⟩

/-- Restriction along a composite is the composite of the restrictions. -/
lemma restrictₛₗ_comp_apply (N : SheafOfModules.{m} R) {U V W : C} (h : V ⟶ U) (g : W ⟶ V)
    (n : N.val.obj (op U)) :
    N.val.restrictₛₗ (g ≫ h).op n = N.val.restrictₛₗ g.op (N.val.restrictₛₗ h.op n) := by
  simp only [PresheafOfModules.restrictₛₗ_apply, op_comp]
  exact N.val.map_comp_apply _ _ n

/-- Restriction carries the span of the sections restricted along `h : V ⟶ U` into the span of
the sections restricted along the composite. -/
lemma restrict_mem_sectionSpan (N : SheafOfModules.{m} R) {U V W : C} (h : V ⟶ U) (g : W ⟶ V)
    {n : N.val.obj (op V)} (hn : n ∈ N.sectionSpan h) :
    N.val.restrictₛₗ g.op n ∈ N.sectionSpan (g ≫ h) := by
  refine (_root_.Submodule.span_le (p := (N.sectionSpan (g ≫ h)).comap (N.val.restrictₛₗ g.op))
    |>.2 ?_) hn
  rintro _ ⟨z, rfl⟩
  rw [SetLike.mem_coe, _root_.Submodule.mem_comap, ← N.restrictₛₗ_comp_apply h g z]
  exact N.restrictₛₗ_mem_sectionSpan (g ≫ h) z

/-- **Spanning by restricted sections is transitive.**  If the sections over `V` are spanned by
the restrictions of the sections over `U`, and the sections over `W` by the restrictions of the
sections over `V`, then the sections over `W` are spanned by the restrictions of the sections
over `U`. -/
theorem sectionSpan_eq_top_comp (N : SheafOfModules.{m} R) {U V W : C} (k : V ⟶ U) (h : W ⟶ V)
    (hk : N.sectionSpan k = ⊤) (hh : N.sectionSpan h = ⊤) : N.sectionSpan (h ≫ k) = ⊤ := by
  rw [eq_top_iff, ← hh, sectionSpan]
  refine _root_.Submodule.span_le.2 ?_
  rintro _ ⟨n, rfl⟩
  exact N.restrict_mem_sectionSpan k h (_root_.Submodule.eq_top_iff'.1 hk n)

/-- **The sections over an object are spanned by the restrictions of the sections over another
when they are a quotient of their base change.**  Suppose the sections of `N` over `W` are, as a
module over a ring `B` acting through the ring of sections of the structure sheaf there, a
quotient of the base change along `A → B` of the sections of `N` over `V`, in such a way that
`1 ⊗ n` is the restriction of `n` along `f : W ⟶ V`.  Then every section over `W` is a
`B`-combination, hence a combination over the sections of the structure sheaf, of restrictions of
sections over `V`.

This is `SheafOfModules.globalSectionSpan_eq_top_of_baseChangeEquiv` with the terminal object
replaced by an arbitrary target: terminality is used there only to name the morphism along which
the sections restrict, so the criterion applies verbatim to the members of a covering family,
where the module is presented but no terminal object is in sight.  Only surjectivity of the
comparison is used. -/
theorem sectionSpan_eq_top_of_baseChangeEquiv {V W : C} (f : W ⟶ V) (N : SheafOfModules.{m} R)
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module A (N.val.obj (op V))] [Module B (N.val.obj (op W))]
    (ψ : B →+* R.obj.obj (op W))
    (hψ : ∀ (b : B) (n : N.val.obj (op W)), b • n = ψ b • n)
    (e : B ⊗[A] N.val.obj (op V) →ₗ[B] N.val.obj (op W)) (he : Function.Surjective e)
    (hone : ∀ n, e ((1 : B) ⊗ₜ[A] n) = N.val.restrictₛₗ f.op n) :
    N.sectionSpan f = ⊤ := by
  refine _root_.Submodule.eq_top_iff'.2 fun n => ?_
  obtain ⟨y, rfl⟩ := he n
  induction y with
  | tmul b x =>
    rw [show b ⊗ₜ[A] x = b • ((1 : B) ⊗ₜ[A] x) by rw [smul_tmul', smul_eq_mul, mul_one],
      map_smul, hψ, hone]
    exact _root_.Submodule.smul_mem _ _ (N.restrictₛₗ_mem_sectionSpan f x)
  | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'

/-- **The sections over an object are spanned by the restrictions of the sections over another at
an object where a presenting morphism is surjective on sections.**  Let `b : P ⟶ N` be surjective
on the sections over `W`, with `P` a coproduct of copies of the structure sheaf whose tautological
generators are a basis of its sections both over `V` and over `W`.  Then the sections of `N` over
`W` are spanned by the restrictions along `f : W ⟶ V` of its sections over `V`.

This is `SheafOfModules.globalSectionSpan_eq_top_of_surjective_val_app` with the terminal object
replaced by an arbitrary target.  The relations of the presentation play no part, and neither does
exactness of its sections over `V`: the sections of `N` over `W` are only shown to be a quotient
of a base change of its sections over `V`, which is all a span condition needs. -/
theorem sectionSpan_eq_top_of_surjective_val_app {V W : C} (f : W ⟶ V) {I : Type w'}
    {P N : SheafOfModules.{max t r} R}
    (ι : ∀ _ : I, uliftForPresentation.{uC, vC, r, r, t} (unit R) ⟶ P) (b : P ⟶ N)
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module A (P.val.obj (op V))] [Module A (N.val.obj (op V))]
    [Module A (P.val.obj (op W))] [Module B (P.val.obj (op W))]
    [IsScalarTower A B (P.val.obj (op W))]
    [Module A (N.val.obj (op W))] [Module B (N.val.obj (op W))]
    [IsScalarTower A B (N.val.obj (op W))]
    (basPV : Module.Basis I A (P.val.obj (op V))) (basPW : Module.Basis I B (P.val.obj (op W)))
    (hbasPV : ∀ i, basPV i = tautGen ι i (op V))
    (hbasPW : ∀ i, basPW i = tautGen ι i (op W))
    (rP : P.val.obj (op V) →ₗ[A] P.val.obj (op W))
    (hrP : ∀ x, rP x = P.val.restrictₛₗ f.op x)
    (rN : N.val.obj (op V) →ₗ[A] N.val.obj (op W))
    (hrN : ∀ x, rN x = N.val.restrictₛₗ f.op x)
    (bV : P.val.obj (op V) →ₗ[A] N.val.obj (op V))
    (hbV : ∀ x, bV x = b.val.app (op V) x)
    (bW : P.val.obj (op W) →ₗ[B] N.val.obj (op W))
    (hbW : ∀ x, bW x = b.val.app (op W) x)
    (hsurj : Function.Surjective (b.val.app (op W)))
    (ψ : B →+* R.obj.obj (op W))
    (hψ : ∀ (c : B) (n : N.val.obj (op W)), c • n = ψ c • n) :
    N.sectionSpan f = ⊤ := by
  refine sectionSpan_eq_top_of_baseChangeEquiv f N A B ψ hψ (rN.liftBaseChange B) ?_
    fun n => by rw [LinearMap.liftBaseChange_tmul, one_smul, hrN]
  refine Module.BaseChange.surjective_liftBaseChange_of_generators bV bW rP rN (fun x => ?_)
    (bijective_liftBaseChange_of_tautBasis ι f A B basPV basPW hbasPV hbasPW rP hrP).2
    fun n => ?_
  · rw [hbV, hrN, hbW, hrP]
    exact (PresheafOfModules.naturality_apply b.val f.op x).symm
  · obtain ⟨x, hx⟩ := hsurj n
    exact ⟨x, by rw [hbW]; exact hx⟩

/-- The span condition of `SheafOfModules.IsLocallySpannedBySections` at a single object: every
section over that object is, after restriction along the arrows of some covering sieve, a
combination of the restrictions of the sections over the terminal object. -/
def IsLocallySpannedBySectionsAt {T : C} (hT : IsTerminal T) (N : SheafOfModules.{m} R)
    (V : C) : Prop :=
  ∀ n : N.val.obj (op V), ∃ S : Sieve V, S ∈ J V ∧
    ∀ ⦃W : C⦄ (g : W ⟶ V), S g → N.val.restrictₛₗ g.op n ∈ N.globalSectionSpan hT W

/-- Being locally spanned by global sections is the span condition at every object. -/
lemma isLocallySpannedBySections_iff_forall_isLocallySpannedBySectionsAt {T : C}
    (hT : IsTerminal T) (N : SheafOfModules.{m} R) :
    N.IsLocallySpannedBySections hT ↔ ∀ V : C, N.IsLocallySpannedBySectionsAt hT V := Iff.rfl

/-- The span condition holds at an object whose sections are all combinations of the restrictions
of the global sections, the testing sieve being the maximal one. -/
lemma isLocallySpannedBySectionsAt_of_globalSectionSpan_eq_top {T : C} (hT : IsTerminal T)
    (N : SheafOfModules.{m} R) {V : C} (h : N.globalSectionSpan hT V = ⊤) :
    N.IsLocallySpannedBySectionsAt hT V := fun n =>
  ⟨⊤, J.top_mem V, fun {_W} g _ =>
    N.restrict_mem_globalSectionSpan hT g (_root_.Submodule.eq_top_iff'.1 h n)⟩

/-- The span condition at an object follows from the span being everything at the members of one
covering family of that object. -/
theorem isLocallySpannedBySectionsAt_of_exists_cover {T : C} (hT : IsTerminal T)
    (N : SheafOfModules.{m} R) {V : C} {I : Type w'} (Y : I → C) (g : ∀ i, Y i ⟶ V)
    (hcov : Sieve.ofArrows Y g ∈ J V) (htop : ∀ i, N.globalSectionSpan hT (Y i) = ⊤) :
    N.IsLocallySpannedBySectionsAt hT V := by
  intro n
  refine ⟨Sieve.ofArrows Y g, hcov, fun {W} a ha => ?_⟩
  rw [Sieve.mem_ofArrows_iff] at ha
  obtain ⟨i, c, rfl⟩ := ha
  rw [N.restrictₛₗ_comp_apply (g i) c n]
  exact N.restrict_mem_globalSectionSpan hT c
    (_root_.Submodule.eq_top_iff'.1 (htop i) (N.val.restrictₛₗ (g i).op n))

/-- **The span condition is local.**  If every source of a covering sieve of an object satisfies
the span condition, so does the object: the arrows along which a given section becomes a
combination of the global sections form a sieve, because restriction carries that span into that
span, and a sieve which is covering after pullback along every arrow of a covering sieve is
itself covering. -/
theorem isLocallySpannedBySectionsAt_of_sieve {T : C} (hT : IsTerminal T)
    (N : SheafOfModules.{m} R) {V : C} (Sv : Sieve V) (hSv : Sv ∈ J V)
    (h : ∀ ⦃Z : C⦄ (f : Z ⟶ V), Sv f → N.IsLocallySpannedBySectionsAt hT Z) :
    N.IsLocallySpannedBySectionsAt hT V := by
  intro n
  refine ⟨{ arrows := fun W g => N.val.restrictₛₗ g.op n ∈ N.globalSectionSpan hT W
            downward_closed := fun {W W'} {g} hg c => ?_ }, ?_, fun {W} g hg => hg⟩
  · rw [N.restrictₛₗ_comp_apply g c n]
    exact N.restrict_mem_globalSectionSpan hT c hg
  · refine J.transitive hSv _ fun {Z} {f} hf => ?_
    obtain ⟨Sz, hSz, hmem⟩ := h f hf (N.val.restrictₛₗ f.op n)
    refine J.superset_covering (fun {W} c hc => ?_) hSz
    change N.val.restrictₛₗ (c ≫ f).op n ∈ N.globalSectionSpan hT W
    rw [N.restrictₛₗ_comp_apply f c n]
    exact hmem c hc

/-- **Being locally spanned by global sections is testable on one covering sieve of each
object.**  This is `SheafOfModules.isLocallySpannedBySectionsAt_of_sieve` at every object. -/
theorem isLocallySpannedBySections_of_forall_sieve {T : C} (hT : IsTerminal T)
    (N : SheafOfModules.{m} R)
    (h : ∀ V : C, ∃ Sv : Sieve V, Sv ∈ J V ∧
      ∀ ⦃Z : C⦄ (f : Z ⟶ V), Sv f → N.IsLocallySpannedBySectionsAt hT Z) :
    N.IsLocallySpannedBySections hT := fun V =>
  let ⟨Sv, hSv, hZ⟩ := h V
  isLocallySpannedBySectionsAt_of_sieve hT N Sv hSv hZ

end SheafOfModules

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **Being locally spanned by global sections is a condition at the affine objects lying over
the members of one covering family of the terminal object.**

A covering family `Y i ⟶ T` of the terminal object of a slice of the associated fppf site is
given.  For an arbitrary object `V` of the slice, pulling that family's sieve back along the
structural morphism of `V` produces a covering sieve of `V` each of whose sources admits a
morphism to some `Y i`; such a source carries a covering family by affine objects
(`AlgebraicGeometry.FibredSite.exists_affine_ofArrows_over`), whose members again admit a morphism
to that `Y i`, so the hypothesis makes the span everything there, and the span condition holds at
the source.  It then holds at `V` by the locality of the condition
(`SheafOfModules.isLocallySpannedBySectionsAt_of_sieve`).

Compared with `AlgebraicGeometry.FibredSite.isLocallySpannedBySections_over_of_forall_affine` the
affine objects at which the span is demanded are restricted to those lying over a member of the
given family. -/
theorem isLocallySpannedBySections_over_of_forall_affine_of_cover (hp : p.IsFiberedInGroupoids)
    (x : 𝒳) {R : Sheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) RingCat.{r}}
    {T : Over x} (hT : IsTerminal T) (N : SheafOfModules.{m} R)
    {ι : Type w'} (Y : ι → Over x) (g : ∀ i, Y i ⟶ T)
    (hcov : Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) T)
    (h : ∀ (i : ι) (W : Over x), IsAffineOver B S hS (p.obj W.left) → (W ⟶ Y i) →
      N.globalSectionSpan hT W = ⊤) :
    N.IsLocallySpannedBySections hT := by
  refine SheafOfModules.isLocallySpannedBySections_of_forall_sieve hT N fun V => ?_
  refine ⟨(Sieve.ofArrows Y g).pullback (hT.from V),
    ((BigFppfOver.associatedTopology B S hS p .fppf).over x).pullback_stable _ hcov,
    fun {Z} f hf => ?_⟩
  have hf' : Sieve.ofArrows Y g (f ≫ hT.from V) := hf
  rw [Sieve.mem_ofArrows_iff] at hf'
  obtain ⟨i, c, -⟩ := hf'
  obtain ⟨I, W, a, hWaff, hWcov⟩ := exists_affine_ofArrows_over B S hS p hp x Z
  exact SheafOfModules.isLocallySpannedBySectionsAt_of_exists_cover hT N W a hWcov
    fun j => h i (W j) (hWaff j) (a j ≫ c)

/-- **The span condition from the span of the global sections at the members of a covering family
and the span of a member's sections at the affine objects over it.**

The two inputs compose by `SheafOfModules.sectionSpan_eq_top_comp`: an affine object `W` of the
slice with a morphism `a` to a member `Y i` has `hT.from W = a ≫ g i` by terminality, so the span
of the global sections at `W` contains, and hence equals, the span of the restrictions along `a`
of the sections over `Y i`.

The second input is what a global presentation of the module over `Y i` supplies
(`AlgebraicGeometry.FibredSite.globalSectionSpan_eq_top_of_hasGlobalPresentation_of_isAffineOver`
at the slice over `Y i`), so for a quasi-coherent module the whole criterion reduces to the first
input: that the sections over the members of a covering family of the terminal object are spanned
by the restrictions of the sections over the terminal object. -/
theorem isLocallySpannedBySections_over_of_sectionSpan_eq_top (hp : p.IsFiberedInGroupoids)
    (x : 𝒳) {R : Sheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) RingCat.{r}}
    {T : Over x} (hT : IsTerminal T) (N : SheafOfModules.{m} R)
    {ι : Type w'} (Y : ι → Over x) (g : ∀ i, Y i ⟶ T)
    (hcov : Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) T)
    (hY : ∀ i, N.sectionSpan (g i) = ⊤)
    (haff : ∀ (i : ι) (W : Over x), IsAffineOver B S hS (p.obj W.left) → ∀ a : W ⟶ Y i,
      N.sectionSpan a = ⊤) :
    N.IsLocallySpannedBySections hT :=
  isLocallySpannedBySections_over_of_forall_affine_of_cover B S hS p hp x hT N Y g hcov
    fun i W hW a => by
      rw [SheafOfModules.globalSectionSpan_eq_sectionSpan, hT.hom_ext (hT.from W) (a ≫ g i)]
      exact N.sectionSpan_eq_top_comp (g i) a (hY i) (haff i W hW a)

/-- **The generators half of a global presentation from the span of the global sections at the
members of a covering family and the span of a member's sections at the affine objects over
it.**  This is `AlgebraicGeometry.FibredSite.isLocallySpannedBySections_over_of_sectionSpan_eq_top`
followed by `SheafOfModules.isGeneratedByUnit_of_isLocallySpannedBySections`. -/
theorem isGeneratedByUnit_over_of_sectionSpan_eq_top (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    {R : Sheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) RingCat.{r}}
    {T : Over x} (hT : IsTerminal T) (N : SheafOfModules.{m} R)
    {ι : Type w'} (Y : ι → Over x) (g : ∀ i, Y i ⟶ T)
    (hcov : Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) T)
    (hY : ∀ i, N.sectionSpan (g i) = ⊤)
    (haff : ∀ (i : ι) (W : Over x), IsAffineOver B S hS (p.obj W.left) → ∀ a : W ⟶ Y i,
      N.sectionSpan a = ⊤) :
    N.IsGeneratedByUnit :=
  SheafOfModules.isGeneratedByUnit_of_isLocallySpannedBySections hT
    (isLocallySpannedBySections_over_of_sectionSpan_eq_top B S hS p hp x hT N Y g hcov hY haff)

/-- **The relations half of a global presentation with the affine objects restricted to those
lying over the members of one covering family.**  This is
`SheafOfModules.hasLocallySpannedRelations_of_hasSpannedRelationsOn` whose locality criterion is
discharged by
`AlgebraicGeometry.FibredSite.isLocallySpannedBySections_over_of_forall_affine_of_cover`; the
class of testing objects is the affine objects of the slice admitting a morphism to a member of
the family, which includes the members themselves. -/
theorem hasLocallySpannedRelations_over_of_cover (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    {R : Sheaf ((BigFppfOver.associatedTopology B S hS p .fppf).over x) RingCat.{r}}
    {T : Over x} (hT : IsTerminal T) (M : SheafOfModules.{m} R)
    {ι : Type w'} (Y : ι → Over x) (g : ∀ i, Y i ⟶ T)
    (hcov : Sieve.ofArrows Y g ∈ ((BigFppfOver.associatedTopology B S hS p .fppf).over x) T)
    (h : M.HasSpannedRelationsOn hT fun W =>
      IsAffineOver B S hS (p.obj W.left) ∧ ∃ i, Nonempty (W ⟶ Y i)) :
    M.HasLocallySpannedRelations hT :=
  SheafOfModules.hasLocallySpannedRelations_of_hasSpannedRelationsOn hT M _
    (fun Z hZ => isLocallySpannedBySections_over_of_forall_affine_of_cover B S hS p hp x hT Z Y g
      hcov fun i W hW a => hZ W ⟨hW, i, ⟨a⟩⟩) h

end AlgebraicGeometry.FibredSite

end
