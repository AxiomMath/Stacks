module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.CoproductSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of a coproduct of copies of the structure sheaf over a quasi-compact object

A coproduct of copies of the structure sheaf of a ringed site is the sheafification of the
presheaf which assigns to an object the direct sum of the sections of the structure sheaf, and
that presheaf is not a sheaf: a section of the coproduct may use a different summand on each
member of a covering, so over an object admitting an infinite covering it can fail to be a
finite combination of the tautological generators.  Over an object all of whose coverings admit
a finite subcovering this cannot happen, and the sections of the coproduct are exactly the
direct sum of the sections of the structure sheaf.  That is what this file proves, in the
elementwise form `(I →₀ R(V)) ≃ₗ[R(V)] (⊕ I, 𝒪)(V)`.

The argument has three ingredients and no cohomology.

*Locality.*  Every section of the coproduct is, after restriction along the arrows of some
covering sieve, an `R`-combination of the tautological generators.  This is the retraction
argument of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.CoproductSections` run on
the submodule `SheafOfModules.localTautSpan` of sections locally in the span of the generators,
rather than on the sections over a terminal object; no terminal object is needed.

*Finiteness.*  A membership in a span is a finite combination, so each member of a covering
family uses only finitely many generators.  If the covering family may be taken finite — which
is the only place quasi-compactness enters — then one finite set `F` of indices serves the whole
family.

*Truncation.*  The universal property of the coproduct supplies, for each index, a projection
`SheafOfModules.tautProj` onto the corresponding copy of the structure sheaf, and hence the
endomorphism `SheafOfModules.tautTrunc` of the sections which keeps only the summands in `F`.
It fixes the span of the generators indexed by `F` and takes values in it, and it is compatible
with restriction.  So a section whose restrictions to the finite covering family lie in the
`F`-span is fixed by it on that family, hence fixed by it, hence lies in the `F`-span.  This
replaces the gluing of the local coefficient families: the retraction does the gluing.

Injectivity is separate and needs no quasi-compactness: the projections read the coefficients
of a combination back off it.

## Main definitions

* `CategoryTheory.GrothendieckTopology.HasFiniteSubcovering`: every covering sieve of an object
  contains a finite family which still generates a covering sieve.  This is the sieve-level form
  of the finite subcovering property of Stacks 0D05(3).
* `SheafOfModules.tautGen`: the tautological generator of a coproduct attached to an index.
* `SheafOfModules.tautSpanOn`: the span of the tautological generators indexed by a set.
* `SheafOfModules.localTautSpan`: the sections which are locally in that span, as a submodule of
  a sheaf of modules.
* `SheafOfModules.tautProj`: the projection of a coproduct onto one of its summands.
* `SheafOfModules.tautTrunc`: the endomorphism of the sections keeping the summands in a finite
  set of indices.
* `SheafOfModules.sectionsEquivFinsupp`: **the sections of a coproduct of copies of the structure
  sheaf over an object with the finite subcovering property are the finitely supported families
  of sections of the structure sheaf.**

## Main results

* `SheafOfModules.exists_mem_tautSpan_of_isColimit_cofan`: every section of a coproduct of copies
  of the structure sheaf is locally an `R`-combination of the tautological generators.
* `SheafOfModules.tautSpanOn_univ_eq_top`: **over an object with the finite subcovering property
  the tautological generators span the sections.**
* `SheafOfModules.injective_linearCombination_tautGen`: the tautological generators are
  independent on sections over any object.
* `SheafOfModules.bijective_linearCombination_tautGen` and
  `SheafOfModules.sectionsEquivFinsupp`: the two combined.
* `SheafOfModules.restrict_linearCombination_tautGen`: the identification is compatible with
  restriction, the coefficients being restricted summandwise.

## Implementation notes

The index type of the coproduct is an arbitrary `Type w`, independent of the universe of the
sections; the consumers take it in `max u v r m`.

`SheafOfModules.tautTrunc` is built as a sum of linear maps on sections rather than as an
endomorphism of the coproduct, so that the preadditive structure of the category of sheaves of
modules is used only through `SheafOfModules.tautProj`, which is a plain `Cofan.IsColimit.desc`.
The equations identifying its value on a tautological generator are stated as their own lemmas
rather than rewritten through, since the values of the summands are definitionally but not
syntactically the values of the composites they come from.

`SheafOfModules.localTautSpan` repeats the construction of
`SheafOfModules.localGlobalSections` with the span of the tautological generators in place of
the span of the sections over a terminal object; the two spans are different submodules, and the
tautological version needs no terminal object, so neither statement specialises to the other.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0D05](https://stacks.math.columbia.edu/tag/0D05)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v r t

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- An object `V` *has the finite subcovering property* for a topology when every covering sieve
of `V` contains a finite family of arrows which still generates a covering sieve.  This is the
sieve-level form of Stacks 0D05(3); for an affine scheme in a big site of schemes it is
quasi-compactness of the underlying space together with the fact that a covering family may be
refined inside a covering sieve. -/
@[sga "4 VI 1.1", sga "6 II 2.1.1"]
def HasFiniteSubcovering (J : GrothendieckTopology C) (V : C) : Prop :=
  ∀ S : Sieve V, S ∈ J V → ∃ (n : ℕ) (W : Fin n → C) (g : ∀ i, W i ⟶ V),
    (∀ i, S (g i)) ∧ Sieve.ofArrows W g ∈ J V

end CategoryTheory.GrothendieckTopology

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  {I : Type w} {N : SheafOfModules.{max t r} R}
  (ι : ∀ _ : I, uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ N)

/-- **The tautological generator** of a family of morphisms out of the universe lift of the
structure sheaf: the image of the unit section under the morphism indexed by `i`.  For a
coproduct of copies of the structure sheaf this is the `i`-th standard basis section. -/
noncomputable def tautGen (i : I) (X : Cᵒᵖ) : N.val.obj X :=
  (ι i).val.app X (uliftUnitGen.{u, v, r, t} R X)

/-- A morphism out of the universe lift of the structure sheaf is multiplication by its value on
the unit section, so its values are the multiples of the tautological generator. -/
lemma val_app_eq_smul (i : I) (X : Cᵒᵖ) (a : ULift.{t} (R.obj.obj X)) :
    (ι i).val.app X a = a.down • tautGen ι i X := by
  conv_lhs => rw [← ModuleCat.uliftSelfHom_eq (A := R.obj.obj X) ((ι i).val.app X)]
  rfl

/-- The tautological generators form a compatible family: the unit section does. -/
lemma restrict_tautGen (i : I) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    N.val.restrictₛₗ f (tautGen ι i X) = tautGen ι i Y := by
  rw [tautGen, PresheafOfModules.restrictₛₗ_apply, ← PresheafOfModules.naturality_apply,
    uliftForPresentation_unit_val_map_uliftUnitGen.{u, v, r, t}]
  rfl

/-- The submodule of the sections over `X` spanned by the tautological generators indexed by a
set `s` of indices. -/
noncomputable def tautSpanOn (s : Set I) (X : Cᵒᵖ) :
    _root_.Submodule (R.obj.obj X) (N.val.obj X) :=
  _root_.Submodule.span _ ((fun i ↦ tautGen ι i X) '' s)

/-- A tautological generator indexed by a member of `s` lies in the span over `s`. -/
lemma tautGen_mem_tautSpanOn {s : Set I} {i : I} (hi : i ∈ s) (X : Cᵒᵖ) :
    tautGen ι i X ∈ tautSpanOn ι s X :=
  _root_.Submodule.subset_span ⟨i, hi, rfl⟩

/-- The span over a larger set of indices is larger. -/
lemma tautSpanOn_mono {s s' : Set I} (h : s ⊆ s') (X : Cᵒᵖ) :
    tautSpanOn ι s X ≤ tautSpanOn ι s' X :=
  _root_.Submodule.span_mono (Set.image_mono h)

/-- Restriction carries the span of the tautological generators over a set of indices into the
span of the same generators. -/
lemma restrict_mem_tautSpanOn (s : Set I) {X Y : Cᵒᵖ} (f : X ⟶ Y) {n : N.val.obj X}
    (hn : n ∈ tautSpanOn ι s X) : N.val.restrictₛₗ f n ∈ tautSpanOn ι s Y := by
  induction hn using _root_.Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [restrict_tautGen]
    exact tautGen_mem_tautSpanOn ι hi Y
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact _root_.Submodule.smul_mem _ _ hx

/-- Every value of the morphism indexed by a member of `s` lies in the span over `s`. -/
lemma val_app_mem_tautSpanOn {s : Set I} {i : I} (hi : i ∈ s) (X : Cᵒᵖ)
    (a : (uliftForPresentation.{u, v, r, r, t} (unit R)).val.obj X) :
    (ι i).val.app X a ∈ tautSpanOn ι s X := by
  rw [val_app_eq_smul ι i X a]
  exact _root_.Submodule.smul_mem _ _ (tautGen_mem_tautSpanOn ι hi X)

/-- A section in the span of the tautological generators is a finite combination of them. -/
private lemma exists_finsupp_sum_eq_of_mem_tautSpanOn_univ {X : Cᵒᵖ} {n : N.val.obj X}
    (hn : n ∈ tautSpanOn ι Set.univ X) :
    ∃ c : I →₀ R.obj.obj X, (c.sum fun i a ↦ a • tautGen ι i X) = n := by
  rw [tautSpanOn, Set.image_univ] at hn
  exact Finsupp.mem_span_range_iff_exists_finsupp.1 hn

/-- The sieve of arrows along which a section becomes an `R`-combination of the tautological
generators.  It is a sieve because restriction carries that span into that span. -/
def tautSieve {X : Cᵒᵖ} (n : N.val.obj X) : Sieve X.unop where
  arrows W g := N.val.restrictₛₗ g.op n ∈ tautSpanOn ι Set.univ (op W)
  downward_closed := @fun W W' g hg a ↦ by
    have key : N.val.restrictₛₗ (a ≫ g).op n =
        N.val.restrictₛₗ a.op (N.val.restrictₛₗ g.op n) := by
      simp only [PresheafOfModules.restrictₛₗ_apply, op_comp]
      exact N.val.map_comp_apply _ _ n
    rw [key]
    exact restrict_mem_tautSpanOn ι Set.univ a.op hg

/-- Restricting a section pulls its sieve of combinations of tautological generators back. -/
lemma tautSieve_pullback_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : N.val.obj X) {W : C}
    (g : W ⟶ Y.unop) :
    (tautSieve ι (N.val.restrictₛₗ f n)).arrows g ↔
      ((tautSieve ι n).pullback f.unop).arrows g := by
  refine Iff.of_eq (congrArg (· ∈ tautSpanOn ι Set.univ (op W)) ?_)
  exact (N.val.map_comp_apply f g.op n).symm

/-- **The sections which are locally combinations of the tautological generators**, as a
submodule of a sheaf of modules.  Membership is local by the transitivity axiom of the topology:
a section which is, on a covering, locally such a combination is locally one. -/
noncomputable def localTautSpan : N.Submodule where
  obj X :=
    { carrier := {n | tautSieve ι n ∈ J X.unop}
      add_mem' := @fun n n' hn hn' ↦
        J.superset_covering (fun W g hg ↦ by
          change N.val.restrictₛₗ g.op (n + n') ∈ tautSpanOn ι Set.univ (op W)
          rw [map_add]
          exact add_mem hg.1 hg.2) (J.intersection_covering hn hn')
      zero_mem' :=
        J.superset_covering (fun W g _ ↦ by
          change N.val.restrictₛₗ g.op 0 ∈ tautSpanOn ι Set.univ (op W)
          rw [map_zero]
          exact zero_mem _) (J.top_mem _)
      smul_mem' := fun a n hn ↦
        J.superset_covering (fun W g hg ↦ by
          change N.val.restrictₛₗ g.op (a • n) ∈ tautSpanOn ι Set.univ (op W)
          rw [map_smulₛₗ]
          exact _root_.Submodule.smul_mem _ _ hg) hn }
  map {X Y} f := fun n hn ↦
    J.superset_covering (fun W g hg ↦ (tautSieve_pullback_iff ι f n g).2 hg)
      (J.pullback_stable f.unop hn)
  isSheaf := @fun X s hs ↦
    J.transitive hs _ @fun Y f hf ↦
      J.superset_covering (fun W g hg ↦ (tautSieve_pullback_iff ι f.op s g).1 hg) hf

/-- The span of the tautological generators is contained in the sections which are locally such
combinations. -/
lemma tautSpanOn_univ_le_localTautSpan (X : Cᵒᵖ) :
    tautSpanOn ι Set.univ X ≤ (localTautSpan ι).obj X := fun _ hn ↦
  J.superset_covering (fun _ g _ ↦ restrict_mem_tautSpanOn ι Set.univ g.op hn) (J.top_mem _)

/-- **Every section of a coproduct of copies of the universe lift of the structure sheaf is
locally an `R`-combination of the tautological generators.**  Each inclusion of a summand lands
in the submodule of sections which are locally such combinations, so the universal property of
the coproduct retracts the inclusion of that submodule, and a submodule whose inclusion has a
retraction is everything.  No terminal object, no quasi-compactness and no sheafification
instance are needed. -/
theorem exists_mem_tautSpan_of_isColimit_cofan (hN : IsColimit (Cofan.mk N ι)) (V : C)
    (n : N.val.obj (op V)) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), S g →
      N.val.restrictₛₗ g.op n ∈ tautSpanOn ι Set.univ (op W) := by
  obtain ⟨k, hk⟩ : ∃ k : N ⟶ (localTautSpan ι).toSheafOfModules,
      k ≫ (localTautSpan ι).ι = 𝟙 N := by
    refine ⟨Cofan.IsColimit.desc hN fun i ↦ (localTautSpan ι).lift (ι i)
      (fun X a ↦ tautSpanOn_univ_le_localTautSpan ι X
        (val_app_mem_tautSpanOn ι (Set.mem_univ i) X a)),
      Cofan.IsColimit.hom_ext hN _ _ fun i ↦ ?_⟩
    rw [← Category.assoc, Cofan.IsColimit.fac hN _ i, Submodule.lift_ι]
    simp
  exact ⟨tautSieve ι n, (localTautSpan ι).mem_of_retraction k hk (op V) n, fun {_} _ hg ↦ hg⟩

section Projections

variable [DecidableEq I] (hN : IsColimit (Cofan.mk N ι))

/-- **The projection of a coproduct of copies of the universe lift of the structure sheaf onto
one of its summands**, the morphism induced by the identity on that summand and zero on the
others. -/
noncomputable def tautProj (i : I) : N ⟶ uliftForPresentation.{u, v, r, r, t} (unit R) :=
  Cofan.IsColimit.desc hN fun j ↦ if j = i then 𝟙 _ else 0

/-- The projection onto the `i`-th summand restricted to the `j`-th summand is the identity when
`j = i` and zero otherwise. -/
lemma ι_tautProj (i j : I) : ι j ≫ tautProj ι hN i = if j = i then 𝟙 _ else 0 :=
  Cofan.IsColimit.fac hN _ j

/-- **The projections read the tautological generators.** -/
lemma tautProj_tautGen (i j : I) (X : Cᵒᵖ) :
    (tautProj ι hN i).val.app X (tautGen ι j X) =
      if j = i then uliftUnitGen.{u, v, r, t} R X else 0 := by
  by_cases hji : j = i
  · have h : ι j ≫ tautProj ι hN i = 𝟙 _ := (ι_tautProj ι hN i j).trans (ite_eq_left hji)
    rw [ite_eq_left hji]
    exact congrArg (fun φ : uliftForPresentation.{u, v, r, r, t} (unit R) ⟶
      uliftForPresentation.{u, v, r, r, t} (unit R) ↦
        φ.val.app X (uliftUnitGen.{u, v, r, t} R X)) h
  · have h : ι j ≫ tautProj ι hN i = 0 := (ι_tautProj ι hN i j).trans (ite_eq_right hji)
    rw [ite_eq_right hji]
    exact congrArg (fun φ : uliftForPresentation.{u, v, r, r, t} (unit R) ⟶
      uliftForPresentation.{u, v, r, r, t} (unit R) ↦
        φ.val.app X (uliftUnitGen.{u, v, r, t} R X)) h

/-- **The truncation of the sections to a finite set of summands**, the sum over that set of the
inclusion of a summand after the projection onto it. -/
noncomputable def tautTrunc (F : Finset I) (X : Cᵒᵖ) :
    N.val.obj X →ₗ[R.obj.obj X] N.val.obj X :=
  ∑ i ∈ F, ((ι i).val.app X).hom ∘ₗ ((tautProj ι hN i).val.app X).hom

/-- The value of `SheafOfModules.tautTrunc` on a section, summand by summand. -/
lemma tautTrunc_apply (F : Finset I) (X : Cᵒᵖ) (n : N.val.obj X) :
    tautTrunc ι hN F X n = ∑ i ∈ F, (ι i).val.app X ((tautProj ι hN i).val.app X n) := by
  simp [tautTrunc]

/-- `SheafOfModules.tautTrunc` takes values in the span of the generators it keeps. -/
lemma tautTrunc_mem (F : Finset I) (X : Cᵒᵖ) (n : N.val.obj X) :
    tautTrunc ι hN F X n ∈ tautSpanOn ι (F : Set I) X := by
  rw [tautTrunc_apply]
  exact sum_mem fun i hi ↦ val_app_mem_tautSpanOn ι hi X _

/-- `SheafOfModules.tautTrunc` commutes with restriction: the inclusions and the projections are
morphisms of sheaves of modules. -/
lemma tautTrunc_restrict (F : Finset I) {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : N.val.obj X) :
    N.val.restrictₛₗ f (tautTrunc ι hN F X n) = tautTrunc ι hN F Y (N.val.restrictₛₗ f n) := by
  rw [tautTrunc_apply, tautTrunc_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [PresheafOfModules.restrictₛₗ_apply]
  rw [← PresheafOfModules.naturality_apply (ι i).val f,
    ← PresheafOfModules.naturality_apply (tautProj ι hN i).val f]

/-- `SheafOfModules.tautTrunc` fixes the span of the generators it keeps. -/
lemma tautTrunc_eq_self {F : Finset I} {X : Cᵒᵖ} {n : N.val.obj X}
    (hn : n ∈ tautSpanOn ι (F : Set I) X) : tautTrunc ι hN F X n = n := by
  induction hn using _root_.Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    have key : ∀ i ∈ F, (ι i).val.app X ((tautProj ι hN i).val.app X (tautGen ι j X)) =
        if j = i then tautGen ι i X else 0 := fun i _ ↦ by
      rw [tautProj_tautGen]
      by_cases hji : j = i
      · rw [ite_eq_left hji, ite_eq_left hji]; rfl
      · rw [ite_eq_right hji, ite_eq_right hji, map_zero]
    rw [tautTrunc_apply, Finset.sum_congr rfl key,
      Finset.sum_ite_eq F j fun i ↦ tautGen ι i X, ite_eq_left (Finset.mem_coe.1 hj)]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

/-- **The projections read the coefficients of a combination of tautological generators.** -/
lemma tautProj_linearCombination (X : Cᵒᵖ) (c : I →₀ R.obj.obj X) (i : I) :
    (tautProj ι hN i).val.app X
        (Finsupp.linearCombination (R.obj.obj X) (fun j ↦ tautGen ι j X) c) =
      c i • uliftUnitGen.{u, v, r, t} R X := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  have key : ∀ j ∈ c.support, (tautProj ι hN i).val.app X (c j • tautGen ι j X) =
      if j = i then c j • uliftUnitGen.{u, v, r, t} R X else 0 := fun j _ ↦ by
    rw [map_smul, tautProj_tautGen]
    by_cases hji : j = i
    · rw [ite_eq_left hji, ite_eq_left hji]
    · rw [ite_eq_right hji, ite_eq_right hji, smul_zero]
  rw [Finset.sum_congr rfl key,
    Finset.sum_ite_eq' c.support i fun j ↦ c j • uliftUnitGen.{u, v, r, t} R X]
  by_cases hi : i ∈ c.support
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, Finsupp.notMem_support_iff.1 hi, zero_smul]

end Projections

/-- **The tautological generators span the sections over an object with the finite subcovering
property.**  A section is locally a combination of the generators; a finite subfamily of the
covering sieve so obtained uses only finitely many generators between them; the truncation to
those finitely many fixes the restriction of the section to each member of the family, hence
fixes the section itself, and takes values in their span. -/
theorem tautSpanOn_univ_eq_top (hN : IsColimit (Cofan.mk N ι)) {V : C}
    (hV : J.HasFiniteSubcovering V) :
    tautSpanOn ι Set.univ (op V) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro n _
  obtain ⟨S, hS, hspan⟩ := exists_mem_tautSpan_of_isColimit_cofan ι hN V n
  obtain ⟨k, W, g, hgS, hcov⟩ := hV S hS
  have hw : ∀ j, ∃ c : I →₀ R.obj.obj (op (W j)),
      (c.sum fun i a ↦ a • tautGen ι i (op (W j))) = N.val.restrictₛₗ (g j).op n := fun j ↦
    exists_finsupp_sum_eq_of_mem_tautSpanOn_univ ι (hspan (g j) (hgS j))
  choose c hc using hw
  set F : Finset I := Finset.univ.biUnion fun j ↦ (c j).support with hFdef
  have hmemF : ∀ j, N.val.restrictₛₗ (g j).op n ∈ tautSpanOn ι (F : Set I) (op (W j)) := by
    intro j
    rw [← hc j, Finsupp.sum]
    refine sum_mem fun i hi ↦ _root_.Submodule.smul_mem _ _
      (tautGen_mem_tautSpanOn ι (s := (F : Set I)) ?_ _)
    exact Finset.mem_coe.2 (hFdef ▸ Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, hi⟩)
  have htrunc : ∀ j, N.val.restrictₛₗ (g j).op (tautTrunc ι hN F (op V) n) =
      N.val.restrictₛₗ (g j).op n := fun j ↦ by
    rw [tautTrunc_restrict]
    exact tautTrunc_eq_self ι hN (hmemF j)
  have hfix : tautTrunc ι hN F (op V) n = n := by
    refine N.isSheaf.isSeparated V _ hcov _ _ ?_
    intro W' a ha
    rw [Sieve.mem_ofArrows_iff] at ha
    obtain ⟨j, b, rfl⟩ := ha
    have key : ∀ x : N.val.obj (op V), N.val.restrictₛₗ (b ≫ g j).op x =
        N.val.restrictₛₗ b.op (N.val.restrictₛₗ (g j).op x) := fun x ↦ by
      simp only [PresheafOfModules.restrictₛₗ_apply, op_comp]
      exact N.val.map_comp_apply _ _ x
    show N.val.restrictₛₗ (b ≫ g j).op (tautTrunc ι hN F (op V) n) =
      N.val.restrictₛₗ (b ≫ g j).op n
    rw [key, key, htrunc j]
  rw [← hfix]
  exact tautSpanOn_mono ι (Set.subset_univ _) _ (tautTrunc_mem ι hN F (op V) n)

/-- **The tautological generators of a coproduct are independent on sections over any object.**
No quasi-compactness is involved: the projections recover the coefficients. -/
theorem injective_linearCombination_tautGen (hN : IsColimit (Cofan.mk N ι)) (X : Cᵒᵖ) :
    Function.Injective
      (Finsupp.linearCombination (R.obj.obj X) fun i ↦ tautGen ι i X) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ Finsupp.ext fun i ↦ ?_
  have h := tautProj_linearCombination ι hN X c i
  have h2 : c i • uliftUnitGen.{u, v, r, t} R X = ULift.up (c i) :=
    ModuleCat.smul_uliftSelfGen.{r, t} (ULift.up (c i))
  rw [hc, map_zero, h2] at h
  exact congrArg ULift.down h.symm

/-- **The sections of a coproduct of copies of the universe lift of the structure sheaf over an
object with the finite subcovering property are the finitely supported families of sections of
the structure sheaf.**  This is the affine form of the statement that a coproduct of copies of
the structure sheaf is computed section by section; it fails without the finiteness hypothesis,
because the presheaf direct sum is not a sheaf. -/
theorem bijective_linearCombination_tautGen (hN : IsColimit (Cofan.mk N ι)) {V : C}
    (hV : J.HasFiniteSubcovering V) :
    Function.Bijective
      (Finsupp.linearCombination (R.obj.obj (op V)) fun i ↦ tautGen ι i (op V)) := by
  refine ⟨injective_linearCombination_tautGen ι hN (op V), fun n ↦ ?_⟩
  have h : n ∈ tautSpanOn ι Set.univ (op V) := by
    rw [tautSpanOn_univ_eq_top ι hN hV]; exact _root_.Submodule.mem_top
  exact exists_finsupp_sum_eq_of_mem_tautSpanOn_univ ι h

/-- **(⊕ I, 𝒪)(V) = ⊕ I, 𝒪(V) at an object with the finite subcovering property**, as a linear
equivalence.  This is `SheafOfModules.bijective_linearCombination_tautGen` bundled. -/
noncomputable def sectionsEquivFinsupp (hN : IsColimit (Cofan.mk N ι)) {V : C}
    (hV : J.HasFiniteSubcovering V) :
    (I →₀ R.obj.obj (op V)) ≃ₗ[R.obj.obj (op V)] N.val.obj (op V) :=
  LinearEquiv.ofBijective _ (bijective_linearCombination_tautGen ι hN hV)

/-- `SheafOfModules.sectionsEquivFinsupp` is the linear combination of the tautological
generators. -/
lemma sectionsEquivFinsupp_apply (hN : IsColimit (Cofan.mk N ι)) {V : C}
    (hV : J.HasFiniteSubcovering V) (c : I →₀ R.obj.obj (op V)) :
    sectionsEquivFinsupp ι hN hV c =
      Finsupp.linearCombination (R.obj.obj (op V)) (fun i ↦ tautGen ι i (op V)) c := rfl

/-- **Restriction acts on the coefficients summand by summand.**  Restricting a combination of
tautological generators restricts each coefficient, because the generators form a compatible
family. -/
lemma restrict_linearCombination_tautGen {X Y : Cᵒᵖ} (f : X ⟶ Y) (c : I →₀ R.obj.obj X) :
    N.val.restrictₛₗ f
        (Finsupp.linearCombination (R.obj.obj X) (fun i ↦ tautGen ι i X) c) =
      Finsupp.linearCombination (R.obj.obj Y) (fun i ↦ tautGen ι i Y)
        (c.mapRange (R.obj.map f) (map_zero _)) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.linearCombination_apply,
    Finsupp.sum]
  rw [Finset.sum_subset (Finsupp.support_mapRange (f := R.obj.map f))
    (fun i _ hi ↦ by rw [Finsupp.notMem_support_iff.1 hi, zero_smul])]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smulₛₗ, restrict_tautGen]
  rfl

end SheafOfModules

end
