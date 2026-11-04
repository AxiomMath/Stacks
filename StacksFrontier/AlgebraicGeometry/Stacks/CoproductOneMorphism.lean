module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreObjectTwoYoneda
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactDiagonalGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Defs
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.OfFiber

/-!
# The coproduct of a family of 1-morphisms into a stack in groupoids

Let `W` be an object of the big fppf site over `S` which is, in schemes, the coproduct of a
family `Z i` of objects of the site, and let `f i : schemeFibredCategory (Z i) ⟶ 𝒳` be a family
of 1-morphisms into a category fibred in groupoids over the site which is a stack for the fppf
topology. This file produces the 1-morphism
`g : schemeFibredCategory W ⟶ 𝒳` restricting, up to 2-isomorphism, to each `f i`. It is the
1-morphism
the Stacks project writes `f = ∐_x f_x` in the proofs of **Stacks 06MF** and **Stacks 06N3**,
where the chart is assembled as `W = ∐_x Z_x` over the finite type points of `𝒳`.

The mathematics is not a bookkeeping bridge: gluing the objects of `𝒳(Z i)` that the `f i` name
under the 2-Yoneda lemma into an object of `𝒳(W)` is the *descent* condition of the stack `𝒳`
along the covering family `{ Z i ⟶ W }`. What makes it cheap is that this family is a
**disjoint cover** — its members are monomorphisms and an object mapping compatibly into two
distinct members is covered by the empty sieve — so the gluing isomorphisms over the overlaps
carry no information and the cocycle condition is automatic. That half of the argument is proved
here for an arbitrary site and an arbitrary stack in groupoids.

## Main definitions

* `CategoryTheory.Functor.disjointCoverDatum`: the descent datum, relative to the sieve a
  disjoint cover generates, whose object over an arrow of the sieve is the chosen pullback of
  the object at the member that arrow factors through.
* `CategoryTheory.Functor.coverComparison`: its gluing isomorphism, the canonical comparison of
  two chosen pullbacks of one object of the family.

## Main results

* `CategoryTheory.Functor.nonempty_fiberHom_of_bot_mem`,
  `CategoryTheory.Functor.subsingleton_fiberHom_of_bot_mem` and
  `CategoryTheory.Functor.fiberIsoOfBotMem`: over an object covered by the empty sieve the
  fibre of a stack is a contractible groupoid — any two of its objects are joined by exactly
  one morphism, which is therefore an isomorphism.
* `CategoryTheory.Functor.exists_fiber_glue_of_disjointCover` and
  `CategoryTheory.Functor.exists_fiber_glue_of_disjointCover_of_isStack`: **objects of the
  fibres of a stack glue along a disjoint cover**, with no compatibility datum. This is the
  object-level companion of `AlgebraicGeometry.Stack.exists_section_of_disjoint_cover`, which
  glues sections of a sheaf of sets, and of
  `AlgebraicGeometry.Stack.exists_iso_of_disjoint_cover`, which glues isomorphisms of two
  objects of a fibre.
* `AlgebraicGeometry.Stack.exists_stackMap_comp_iso_of_isColimit`: **the universal property of
  a coproduct of objects of the site for 1-morphisms into a stack in groupoids.**
* `AlgebraicGeometry.Stack.exists_stackMap_comp_iso_sigmaOver` and
  `AlgebraicGeometry.Stack.exists_stackMap_comp_iso_sigmaOver_of_lt_cof`: the same at
  `AlgebraicGeometry.BigFppfOver.sigmaOver`, and for every index type of cardinality below the
  site's cutoff, where the size bound on the coproduct of the underlying schemes is discharged
  by `AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof`.

## Implementation notes

The descent datum is assembled in the *sieve-indexed* shape
`CategoryTheory.Functor.SieveDescentDatum` of **Stacks 026B**, not the family-indexed
`CategoryTheory.Functor.DescentDatum` of **Stacks 02ZI**: the sieve-indexed gluing data live
over an arbitrary object of the base rather than over chosen fibre products of the cover, so no
fibre products of the site are needed and `HasPullbacks` is not assumed. Accordingly the stack
condition is consumed in the form `CategoryTheory.Functor.IsStack` (**Stacks 026F**), the first
conjunct of the stack clause of `AlgebraicGeometry.Stack.IsAlgebraicStack`, which carries no
descent universe; this is why the index type of the family is unrestricted apart from the
`Small.{u}` the coproduct of schemes needs anyway.

Each arrow of the generated sieve factors through some member, by a factorisation which is
unique whenever the base of the arrow is not covered by the empty sieve — if it factored
through two distinct members, its base would be covered by the empty sieve. A choice of
factorisation is made once, and the two gluing data over an object `Z` are compared by the
canonical `CategoryTheory.Functor.pullbackFiberComparison` when the two chosen members agree,
and by the unique fibre morphism when they do not, which is exactly the case `⊥ ∈ J Z`. Both
the cocycle condition and compatibility with base change are read off this dichotomy: in the
degenerate branch every parallel pair of fibre morphisms agrees, and in the other branch the
condition is the one `CategoryTheory.Functor.SieveDescentDatum.ofFiber` already proves for the
chosen pullbacks of a single object, at the maximal sieve on that member.

The contractibility of the fibre over an object covered by the empty sieve uses only condition
(2) of Stacks 026F, that `Mor(x, y)` is a sheaf: a sheaf of sets has exactly one section over
such an object, and the sections of `Mor(x, y)` over the identity arrow are the morphisms
`x ⟶ y` of the fibre, read through `CategoryTheory.Functor.pullbackFiberIdIso`.

The passage between the glued object and the 1-morphism is the 2-Yoneda lemma
(**Stacks 004B**) as the library already has it, at a target that is only a category fibred in
groupoids: `AlgebraicGeometry.Stack.stackMapFibreObject` evaluates a 1-morphism out of a
represented category at an object of a fibre,
`AlgebraicGeometry.Stack.fibreObjectFibredMap` goes back,
`AlgebraicGeometry.Stack.fibreObjectStackMapEvaluationIso` is the 2-isomorphism
between a 1-morphism and the one its object names, and
`AlgebraicGeometry.Stack.fibreObjectStackMapFactorIso` is the naturality of
that passage over an arrow of the site, used here at the identity 1-morphism of `𝒳`. The arrow
of `𝒳` it consumes is the inverse of the gluing isomorphism followed by the cartesian arrow of
the chosen pullback, which is what lies over the summand inclusion.

Only the 2-Yoneda lemma and the stack condition are consumed, so the target of the glued
1-morphism is an object of `CategoryTheory.CatFiberedInGroupoids` carrying
`CategoryTheory.Functor.IsStack`, not an algebraic stack. The readings in the 2-category of
algebraic stacks of **Stacks 03YP** — `exists_stackMap_comp_iso_sigmaOver` and
`exists_stackMap_comp_iso_sigmaOver_of_lt_cof` below — add one
`CategoryTheory.Bicategory.InducedBicategory.mkHom` to the 1-morphism and one
`CategoryTheory.Bicategory.InducedBicategory.isoMk` to each 2-isomorphism.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 026B](https://stacks.math.columbia.edu/tag/026B)
* [Stacks Project, Tag 026E](https://stacks.math.columbia.edu/tag/026E)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ vD uD zP

namespace CategoryTheory.Functor

/-! ### Sheaves and fibres over an object covered by the empty sieve -/

section Empty

variable {D : Type uD} [Category.{vD} D] (J : GrothendieckTopology D) {P : Dᵒᵖ ⥤ Type zP}

/-- The sieve generated by the empty family of arrows into `Z` is the empty sieve. -/
theorem ofArrows_pempty_eq_bot {Z : D} :
    Sieve.ofArrows (fun e : PEmpty.{1} => e.elim) (fun e : PEmpty.{1} => (e.elim : _ ⟶ Z))
      = (⊥ : Sieve Z) := by
  simp [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty]

/-- A sheaf of sets has a section over an object covered by the empty sieve: the empty family of
elements is compatible, so it has an amalgamation. -/
theorem nonempty_sections_of_bot_mem (hP : Presheaf.IsSheaf J P) {Z : D}
    (hZ : (⊥ : Sieve Z) ∈ J Z) : Nonempty (P.obj (op Z)) := by
  obtain ⟨g, -, -⟩ := hP.existsUnique_amalgamation_ofArrows
    (X := fun e : PEmpty.{1} => e.elim) (fun e : PEmpty.{1} => (e.elim : _ ⟶ Z))
    (by rw [ofArrows_pempty_eq_bot]; exact hZ) (fun e => e.elim) (fun _ i => i.elim)
  exact ⟨g PUnit.unit⟩

/-- A sheaf of sets has at most one section over an object covered by the empty sieve: it is
separated for that sieve, whose condition is vacuous. -/
theorem subsingleton_sections_of_bot_mem (hP : Presheaf.IsSheaf J P) {Z : D}
    (hZ : (⊥ : Sieve Z) ∈ J Z) : Subsingleton (P.obj (op Z)) :=
  ⟨fun s t => hP.isSeparated Z ⊥ hZ s t (fun _ _ hf => hf.elim)⟩

end Empty

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {J : GrothendieckTopology 𝒮}

/-- If `Z` is covered by the empty sieve then so is the identity arrow of `Z`, as an object of
the slice site over `Z`. -/
theorem bot_mem_over_of_bot_mem {Z : 𝒮} (hZ : (⊥ : Sieve Z) ∈ J Z) :
    (⊥ : Sieve (Over.mk (𝟙 Z))) ∈ (J.over Z) (Over.mk (𝟙 Z)) := by
  rw [GrothendieckTopology.mem_over_iff, map_bot]
  exact hZ

/-- **The fibre over an object covered by the empty sieve has at most one morphism between any
two of its objects.** The sections of `Mor(y, z)` over the identity arrow of `Z` are the
morphisms `y ⟶ z` of the fibre, and a sheaf has at most one section over `Z`. -/
theorem subsingleton_fiberHom_of_bot_mem
    (hmor : ∀ (U : 𝒮) (y z : p.Fiber U), p.IsMorSheaf J U y z)
    {Z : 𝒮} (hZ : (⊥ : Sieve Z) ∈ J Z)
    (y z : p.Fiber Z) : Subsingleton (y ⟶ z) := by
  have hsub := subsingleton_sections_of_bot_mem (J.over Z) (hmor Z y z)
    (bot_mem_over_of_bot_mem hZ)
  refine ⟨fun φ ψ => ?_⟩
  have h : (pullbackFiberIdIso y).hom ≫ φ ≫ (pullbackFiberIdIso z).inv
      = (pullbackFiberIdIso y).hom ≫ ψ ≫ (pullbackFiberIdIso z).inv := hsub.allEq _ _
  simpa using h

/-- **The fibre over an object covered by the empty sieve has a morphism between any two of its
objects.** This is the existence half of the previous statement. -/
theorem nonempty_fiberHom_of_bot_mem
    (hmor : ∀ (U : 𝒮) (y z : p.Fiber U), p.IsMorSheaf J U y z)
    {Z : 𝒮} (hZ : (⊥ : Sieve Z) ∈ J Z)
    (y z : p.Fiber Z) : Nonempty (y ⟶ z) := by
  obtain ⟨m⟩ := nonempty_sections_of_bot_mem (J.over Z) (hmor Z y z)
    (bot_mem_over_of_bot_mem hZ)
  exact ⟨(pullbackFiberIdIso y).inv ≫ m ≫ (pullbackFiberIdIso z).hom⟩

/-- **The fibre over an object covered by the empty sieve is a contractible groupoid.** Any two
of its objects are isomorphic: the unique morphisms in the two directions compose to the unique
endomorphisms, which are therefore the identities. -/
noncomputable def fiberIsoOfBotMem
    (hmor : ∀ (U : 𝒮) (y z : p.Fiber U), p.IsMorSheaf J U y z)
    {Z : 𝒮} (hZ : (⊥ : Sieve Z) ∈ J Z) (y z : p.Fiber Z) :
    y ≅ z where
  hom := (nonempty_fiberHom_of_bot_mem hmor hZ y z).some
  inv := (nonempty_fiberHom_of_bot_mem hmor hZ z y).some
  hom_inv_id := (subsingleton_fiberHom_of_bot_mem hmor hZ y y).allEq _ _
  inv_hom_id := (subsingleton_fiberHom_of_bot_mem hmor hZ z z).allEq _ _


/-! ### The comparison isomorphisms attached to a disjoint cover -/

section DisjointCover

variable {K : Type*} {X : K → 𝒮} {V : 𝒮} {jj : ∀ i, X i ⟶ V}

/-- Every arrow of the sieve generated by a family of arrows factors through one of its
members. -/
theorem exists_factor_of_ofArrows {T : 𝒮} {f : T ⟶ V} (hf : Sieve.ofArrows X jj f) :
    ∃ (i : K) (a : T ⟶ X i), a ≫ jj i = f := by
  obtain ⟨Y, g, h, ⟨i⟩, rfl⟩ := hf
  exact ⟨i, g, rfl⟩

/-- The chosen member of a disjoint cover that an arrow of the generated sieve factors
through. -/
noncomputable def coverIdx {T : 𝒮} {f : T ⟶ V} (hf : Sieve.ofArrows X jj f) : K :=
  (exists_factor_of_ofArrows hf).choose

/-- The chosen factorisation of an arrow of the generated sieve through
`CategoryTheory.Functor.coverIdx`. -/
noncomputable def coverMap {T : 𝒮} {f : T ⟶ V} (hf : Sieve.ofArrows X jj f) :
    T ⟶ X (coverIdx hf) :=
  (exists_factor_of_ofArrows hf).choose_spec.choose

/-- The chosen factorisation is a factorisation. -/
theorem coverMap_comp {T : 𝒮} {f : T ⟶ V} (hf : Sieve.ofArrows X jj f) :
    coverMap hf ≫ jj (coverIdx hf) = f :=
  (exists_factor_of_ofArrows hf).choose_spec.choose_spec

/-- The canonical comparison of two chosen pullbacks of one object `x i` of a family, over an
object `Z` mapping into the two sources compatibly over `V`. The two maps into `X i` agree
because `j i` is a monomorphism, so this is
`CategoryTheory.Functor.pullbackFiberComparison`. -/
noncomputable def coverComparisonAt (hm : ∀ i, Mono (jj i)) (x : ∀ i, p.Fiber (X i)) (i : K)
    {T T' Z : 𝒮} {a : T ⟶ X i} {b : T' ⟶ X i}
    (ε : Z ⟶ T) (ε' : Z ⟶ T') (heq : (ε ≫ a) ≫ jj i = (ε' ≫ b) ≫ jj i) :
    pullbackFiber p (pullbackFiber p (x i) a) ε ≅
      pullbackFiber p (pullbackFiber p (x i) b) ε' :=
  have := hm i
  pullbackFiberComparison (x i) ε ε' ((cancel_mono (jj i)).mp heq)

/-- Two maps into members of a disjoint cover which agree over `V` agree, as the members are
monomorphisms. -/
private theorem eq_of_comp_jj_eq (hm : ∀ i, Mono (jj i)) {i : K} {T T' Z : 𝒮} {a : T ⟶ X i}
    {b : T' ⟶ X i} (ε : Z ⟶ T) (ε' : Z ⟶ T') (heq : (ε ≫ a) ≫ jj i = (ε' ≫ b) ≫ jj i) :
    ε ≫ a = ε' ≫ b :=
  have := hm i
  (cancel_mono (jj i)).mp heq

/-- `CategoryTheory.Functor.coverComparisonAt` is pinned down by its composite with the chosen
cartesian lifts it compares. -/
theorem coverComparisonAt_fac (hm : ∀ i, Mono (jj i)) (x : ∀ i, p.Fiber (X i)) (i : K)
    {T T' Z : 𝒮} {a : T ⟶ X i} {b : T' ⟶ X i}
    (ε : Z ⟶ T) (ε' : Z ⟶ T') (heq : (ε ≫ a) ≫ jj i = (ε' ≫ b) ≫ jj i) :
    Fiber.fiberInclusion.map (coverComparisonAt hm x i ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (pullbackFiber p (x i) b).2 ε' ≫
          IsPreFibered.pullbackMap (x i).2 b =
      IsPreFibered.pullbackMap (pullbackFiber p (x i) a).2 ε ≫
        IsPreFibered.pullbackMap (x i).2 a :=
  pullbackFiberComparison_hom_fac (x i) ε ε' (eq_of_comp_jj_eq hm ε ε' heq)

/-- The cocycle condition for `CategoryTheory.Functor.coverComparisonAt`: this is the cocycle
condition of `CategoryTheory.Functor.SieveDescentDatum.ofFiber` at the object `x i` and the
maximal sieve on `X i`. -/
theorem coverComparisonAt_cocycle (hm : ∀ i, Mono (jj i)) (x : ∀ i, p.Fiber (X i)) (i : K)
    {T₁ T₂ T₃ Z : 𝒮} {a₁ : T₁ ⟶ X i} {a₂ : T₂ ⟶ X i} {a₃ : T₃ ⟶ X i}
    (ε₁ : Z ⟶ T₁) (ε₂ : Z ⟶ T₂) (ε₃ : Z ⟶ T₃)
    (e₁₂ : (ε₁ ≫ a₁) ≫ jj i = (ε₂ ≫ a₂) ≫ jj i)
    (e₂₃ : (ε₂ ≫ a₂) ≫ jj i = (ε₃ ≫ a₃) ≫ jj i)
    (e₁₃ : (ε₁ ≫ a₁) ≫ jj i = (ε₃ ≫ a₃) ≫ jj i) :
    (coverComparisonAt hm x i ε₁ ε₂ e₁₂).hom ≫ (coverComparisonAt hm x i ε₂ ε₃ e₂₃).hom =
      (coverComparisonAt hm x i ε₁ ε₃ e₁₃).hom :=
  (SieveDescentDatum.ofFiber (x i) (⊤ : Sieve (X i))).cocycle
    (f := a₁) trivial (g := a₂) trivial (h := a₃) trivial ε₁ ε₂ ε₃
    (eq_of_comp_jj_eq hm ε₁ ε₂ e₁₂) (eq_of_comp_jj_eq hm ε₂ ε₃ e₂₃)
    (eq_of_comp_jj_eq hm ε₁ ε₃ e₁₃)

/-- Compatibility of `CategoryTheory.Functor.coverComparisonAt` with base change: this is the
base-change condition of `CategoryTheory.Functor.SieveDescentDatum.ofFiber` at the object `x i`
and the maximal sieve on `X i`. -/
theorem coverComparisonAt_pullback (hm : ∀ i, Mono (jj i)) (x : ∀ i, p.Fiber (X i)) (i : K)
    {T T' Z Z' : 𝒮} {a : T ⟶ X i} {b : T' ⟶ X i}
    (ε : Z ⟶ T) (ε' : Z ⟶ T') (heq : (ε ≫ a) ≫ jj i = (ε' ≫ b) ≫ jj i) (γ : Z' ⟶ Z)
    (heq' : ((γ ≫ ε) ≫ a) ≫ jj i = ((γ ≫ ε') ≫ b) ≫ jj i) :
    (pullbackFiberCompIso (pullbackFiber p (x i) a) ε γ).inv ≫
        (pullbackFiberIso (coverComparisonAt hm x i ε ε' heq) γ).hom ≫
        (pullbackFiberCompIso (pullbackFiber p (x i) b) ε' γ).hom =
      (coverComparisonAt hm x i (γ ≫ ε) (γ ≫ ε') heq').hom :=
  (SieveDescentDatum.ofFiber (x i) (⊤ : Sieve (X i))).iso_pullback
    (f := a) trivial (g := b) trivial ε ε' (eq_of_comp_jj_eq hm ε ε' heq) γ

/-- The same comparison when the two chosen members of the cover are only equal, not
syntactically the same. -/
noncomputable def coverComparison (hm : ∀ i, Mono (jj i)) (x : ∀ i, p.Fiber (X i)) {i i' : K}
    (h : i = i') {T T' Z : 𝒮} {a : T ⟶ X i} {b : T' ⟶ X i'}
    (ε : Z ⟶ T) (ε' : Z ⟶ T') (heq : (ε ≫ a) ≫ jj i = (ε' ≫ b) ≫ jj i') :
    pullbackFiber p (pullbackFiber p (x i) a) ε ≅
      pullbackFiber p (pullbackFiber p (x i') b) ε' := by
  subst h
  exact coverComparisonAt hm x _ ε ε' heq

/-- `CategoryTheory.Functor.coverComparison` at a reflexivity proof is
`CategoryTheory.Functor.coverComparisonAt`. -/
theorem coverComparison_rfl (hm : ∀ i, Mono (jj i)) (x : ∀ i, p.Fiber (X i)) {i : K}
    {T T' Z : 𝒮} {a : T ⟶ X i} {b : T' ⟶ X i}
    (ε : Z ⟶ T) (ε' : Z ⟶ T') (heq : (ε ≫ a) ≫ jj i = (ε' ≫ b) ≫ jj i) :
    coverComparison hm x (rfl : i = i) ε ε' heq = coverComparisonAt hm x i ε ε' heq := rfl

/-- The cocycle condition for `CategoryTheory.Functor.coverComparison`. -/
theorem coverComparison_cocycle (hm : ∀ i, Mono (jj i)) (x : ∀ i, p.Fiber (X i))
    {i₁ i₂ i₃ : K} (h₁₂ : i₁ = i₂) (h₂₃ : i₂ = i₃) (h₁₃ : i₁ = i₃)
    {T₁ T₂ T₃ Z : 𝒮} {a₁ : T₁ ⟶ X i₁} {a₂ : T₂ ⟶ X i₂} {a₃ : T₃ ⟶ X i₃}
    (ε₁ : Z ⟶ T₁) (ε₂ : Z ⟶ T₂) (ε₃ : Z ⟶ T₃)
    (e₁₂ : (ε₁ ≫ a₁) ≫ jj i₁ = (ε₂ ≫ a₂) ≫ jj i₂)
    (e₂₃ : (ε₂ ≫ a₂) ≫ jj i₂ = (ε₃ ≫ a₃) ≫ jj i₃)
    (e₁₃ : (ε₁ ≫ a₁) ≫ jj i₁ = (ε₃ ≫ a₃) ≫ jj i₃) :
    (coverComparison hm x h₁₂ ε₁ ε₂ e₁₂).hom ≫ (coverComparison hm x h₂₃ ε₂ ε₃ e₂₃).hom =
      (coverComparison hm x h₁₃ ε₁ ε₃ e₁₃).hom := by
  subst h₁₂
  subst h₂₃
  rw [proof_irrel h₁₃ rfl, coverComparison_rfl, coverComparison_rfl, coverComparison_rfl]
  exact coverComparisonAt_cocycle hm x _ ε₁ ε₂ ε₃ e₁₂ e₂₃ e₁₃

/-- Compatibility of `CategoryTheory.Functor.coverComparison` with base change. -/
theorem coverComparison_pullback (hm : ∀ i, Mono (jj i)) (x : ∀ i, p.Fiber (X i)) {i i' : K}
    (h : i = i') {T T' Z Z' : 𝒮} {a : T ⟶ X i} {b : T' ⟶ X i'}
    (ε : Z ⟶ T) (ε' : Z ⟶ T') (heq : (ε ≫ a) ≫ jj i = (ε' ≫ b) ≫ jj i') (γ : Z' ⟶ Z)
    (heq' : ((γ ≫ ε) ≫ a) ≫ jj i = ((γ ≫ ε') ≫ b) ≫ jj i') :
    (pullbackFiberCompIso (pullbackFiber p (x i) a) ε γ).inv ≫
        (pullbackFiberIso (coverComparison hm x h ε ε' heq) γ).hom ≫
        (pullbackFiberCompIso (pullbackFiber p (x i') b) ε' γ).hom =
      (coverComparison hm x h (γ ≫ ε) (γ ≫ ε') heq').hom := by
  subst h
  rw [coverComparison_rfl, coverComparison_rfl]
  exact coverComparisonAt_pullback hm x _ ε ε' heq γ heq'

/-! ### The descent datum of a family of objects along a disjoint cover -/

/-- In a disjoint cover, two arrows of the generated sieve joined over `V` by two maps out of an
object `Z` which is *not* covered by the empty sieve factor through the same member: if they
factored through different members, the disjointness hypothesis would cover `Z`. -/
theorem coverIdx_eq_of_not_bot_mem
    (hd : ∀ {i k : K}, i ≠ k → ∀ {Y : 𝒮} (a : Y ⟶ X i) (b : Y ⟶ X k),
      a ≫ jj i = b ≫ jj k → (⊥ : Sieve Y) ∈ J Y)
    {T T' Z : 𝒮} {f : T ⟶ V} (hf : Sieve.ofArrows X jj f) {g : T' ⟶ V}
    (hg : Sieve.ofArrows X jj g) (ε : Z ⟶ T) (ε' : Z ⟶ T') (heq : ε ≫ f = ε' ≫ g)
    (hb : (⊥ : Sieve Z) ∉ J Z) : coverIdx hf = coverIdx hg := by
  by_contra hne
  refine hb (hd hne (ε ≫ coverMap hf) (ε' ≫ coverMap hg) ?_)
  rw [Category.assoc, coverMap_comp, Category.assoc, coverMap_comp]
  exact heq

/-- The composite factorisation of an arrow of the generated sieve precomposed with a map into
its source. -/
theorem comp_coverMap_comp {T Z : 𝒮} {f : T ⟶ V} (hf : Sieve.ofArrows X jj f) (ε : Z ⟶ T) :
    (ε ≫ coverMap hf) ≫ jj (coverIdx hf) = ε ≫ f := by
  rw [Category.assoc, coverMap_comp]

/-- **The descent datum of a family of objects along a disjoint cover.** The object attached to
an arrow of the generated sieve is the chosen pullback of the object at the member that arrow
was chosen to factor through, and two of them are glued by the canonical comparison of
`CategoryTheory.Functor.coverComparison` when the two members agree — which is the case over
every object not covered by the empty sieve — and by the unique fibre morphism otherwise. -/
noncomputable def disjointCoverDatum
    (hmor : ∀ (U : 𝒮) (y z : p.Fiber U), p.IsMorSheaf J U y z) (hm : ∀ i, Mono (jj i))
    (hd : ∀ {i k : K}, i ≠ k → ∀ {Y : 𝒮} (a : Y ⟶ X i) (b : Y ⟶ X k),
      a ≫ jj i = b ≫ jj k → (⊥ : Sieve Y) ∈ J Y)
    (x : ∀ i, p.Fiber (X i)) : SieveDescentDatum p (Sieve.ofArrows X jj) where
  obj _ _ hf := pullbackFiber p (x (coverIdx hf)) (coverMap hf)
  iso {_ _ Z} _ hf _ hg ε ε' heq :=
    haveI := Classical.propDecidable ((⊥ : Sieve Z) ∈ J Z)
    if hb : (⊥ : Sieve Z) ∈ J Z then fiberIsoOfBotMem hmor hb _ _
    else coverComparison hm x (coverIdx_eq_of_not_bot_mem hd hf hg ε ε' heq hb) ε ε'
      ((comp_coverMap_comp hf ε).trans (heq.trans (comp_coverMap_comp hg ε').symm))
  cocycle {_ _ _ Z} _ _ _ _ _ _ ε₁ ε₂ ε₃ _ _ _ := by
    by_cases hb : (⊥ : Sieve Z) ∈ J Z
    · exact (subsingleton_fiberHom_of_bot_mem hmor hb _ _).allEq _ _
    · rw [dite_eq_right hb, dite_eq_right hb, dite_eq_right hb]
      exact coverComparison_cocycle hm x _ _ _ ε₁ ε₂ ε₃ _ _ _
  iso_pullback {_ _ Z Z'} _ _ _ _ ε ε' _ γ := by
    by_cases hb' : (⊥ : Sieve Z') ∈ J Z'
    · exact (subsingleton_fiberHom_of_bot_mem hmor hb' _ _).allEq _ _
    · have hb : (⊥ : Sieve Z) ∉ J Z := by
        intro hc
        exact hb' (by simpa using J.pullback_stable γ hc)
      rw [dite_eq_right hb, dite_eq_right hb']
      exact coverComparison_pullback hm x _ ε ε' _ γ _

/-! ### Gluing the objects -/

/-- A chosen pullback along a map into a member of the cover which is forced to be an identity
is canonically isomorphic, in the fibre, to the object itself. -/
noncomputable def fiberIsoOfFactorId (hm : ∀ i, Mono (jj i)) (x : ∀ i, p.Fiber (X i))
    {i i' : K} (h : i' = i) {a : X i ⟶ X i'} (ha : a ≫ jj i' = jj i) :
    pullbackFiber p (x i') a ≅ x i := by
  subst h
  have := hm i'
  have ha' : a = 𝟙 (X i') := by
    refine (cancel_mono (jj i')).mp ?_
    rw [ha, Category.id_comp]
  subst ha'
  exact pullbackFiberIdIso (x i')

/-- **Objects of the fibres of a stack glue along a disjoint cover.** Let `{ j i : X i ⟶ V }` be
a covering family of monomorphisms whose pairwise overlaps are covered by the empty sieve, and
let `p` satisfy conditions (2) and (3) of **Stacks 026F**. Then every family of objects of the
fibres over the members comes, up to isomorphism in each fibre, from one object of the fibre
over `V`.

This is the statement that needs no compatibility datum, in the shape in which
`AlgebraicGeometry.Stack.exists_section_of_disjoint_cover` and
`AlgebraicGeometry.Stack.exists_iso_of_disjoint_cover` give the corresponding statements for
sections of a sheaf of sets and for isomorphisms of two objects of a fibre. -/
theorem exists_fiber_glue_of_disjointCover
    (hmor : ∀ (U : 𝒮) (y z : p.Fiber U), p.IsMorSheaf J U y z)
    (heff : HasEffectiveDescent p J) (hm : ∀ i, Mono (jj i))
    (hj : Sieve.ofArrows X jj ∈ J V)
    (hd : ∀ {i k : K}, i ≠ k → ∀ {Y : 𝒮} (a : Y ⟶ X i) (b : Y ⟶ X k),
      a ≫ jj i = b ≫ jj k → (⊥ : Sieve Y) ∈ J Y)
    (x : ∀ i, p.Fiber (X i)) :
    ∃ y : p.Fiber V, ∀ i, Nonempty (pullbackFiber p y (jj i) ≅ x i) := by
  obtain ⟨y, ζ, hcart, -⟩ := heff (Sieve.ofArrows X jj) hj
    (disjointCoverDatum hmor hm hd x)
  refine ⟨y, fun i => ?_⟩
  have hfi : Sieve.ofArrows X jj (jj i) := Sieve.ofArrows_mk X jj i
  have hc1 : p.IsCartesian (jj i) (IsPreFibered.pullbackMap y.2 (jj i)) :=
    IsPreFibered.pullbackMap.IsCartesian _ _
  have iso1 : pullbackFiber p y (jj i) ≅
      pullbackFiber p (x (coverIdx hfi)) (coverMap hfi) :=
    fiberIsoOfCartesian (jj i) (IsPreFibered.pullbackMap y.2 (jj i))
      (ζ (jj i) hfi) hc1 (hcart (jj i) hfi)
  by_cases hii : coverIdx hfi = i
  · exact ⟨iso1 ≪≫ fiberIsoOfFactorId hm x hii (coverMap_comp hfi)⟩
  · have hbot : (⊥ : Sieve (X i)) ∈ J (X i) :=
      hd hii (coverMap hfi) (𝟙 (X i)) (by rw [coverMap_comp, Category.id_comp])
    exact ⟨iso1 ≪≫ fiberIsoOfBotMem hmor hbot _ _⟩

/-- `CategoryTheory.Functor.exists_fiber_glue_of_disjointCover` at a stack in groupoids in the
sense of **Stacks 026F**. -/
theorem exists_fiber_glue_of_disjointCover_of_isStack (hst : p.IsStack J)
    (hm : ∀ i, Mono (jj i)) (hj : Sieve.ofArrows X jj ∈ J V)
    (hd : ∀ {i k : K}, i ≠ k → ∀ {Y : 𝒮} (a : Y ⟶ X i) (b : Y ⟶ X k),
      a ≫ jj i = b ≫ jj k → (⊥ : Sieve Y) ∈ J Y)
    (x : ∀ i, p.Fiber (X i)) :
    ∃ y : p.Fiber V, ∀ i, Nonempty (pullbackFiber p y (jj i) ≅ x i) :=
  exists_fiber_glue_of_disjointCover hst.isMorSheaf hst.hasEffectiveDescent hm hj
    (hd := fun {_ _} => hd) x

end DisjointCover

end CategoryTheory.Functor

/-! ### The coproduct of a family of 1-morphisms into a stack in groupoids -/

namespace AlgebraicGeometry.Stack

open CategoryTheory.Functor AlgebraicGeometry.BigFppfOver

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The summand inclusions of a cofan in the big fppf site over `S` whose underlying cofan of
schemes is a colimit form a disjoint cover: a `V` of the site mapping into two distinct summands
compatibly over the vertex is covered by the empty sieve, because its underlying scheme has no
points. -/
theorem bot_mem_topology_of_commSq_of_isColimit_toScheme {I : Type v} [Small.{u} I]
    (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS) (jj : ∀ i, Z i ⟶ W)
    (hW : Limits.IsColimit (Limits.Cofan.mk ((toScheme B S hS).obj W)
      (fun i => (toScheme B S hS).map (jj i))))
    {i i' : I} (hii' : i ≠ i') {Y : BigFppfOver B S hS} (a : Y ⟶ Z i) (b : Y ⟶ Z i')
    (hab : a ≫ jj i = b ≫ jj i') : (⊥ : Sieve Y) ∈ topology B S hS Y := by
  refine bot_mem_topology Y (isEmpty_of_commSq_of_isColimit_cofanMk hW hii'
    (a := (toScheme B S hS).map a) (b := (toScheme B S hS).map b) ?_)
  rw [← Functor.map_comp, ← Functor.map_comp, hab]

/-- **The universal property of a coproduct of objects of the site for 1-morphisms into a stack
in groupoids.** Let `W` be an object of the big fppf site over `S` which is, in schemes, the
coproduct of a family `Z i` of objects of the site, and let
`f i : schemeFibredCategory (Z i) ⟶ 𝒳` be a family of 1-morphisms into a category `𝒳` fibred in
groupoids over the site which is a stack for the fppf topology. Then there is a 1-morphism
`g : schemeFibredCategory W ⟶ 𝒳` whose restriction to each summand is 2-isomorphic to `f i`.

This is the 1-morphism the Stacks project writes `f = ∐_x f_x` in the proofs of **Stacks 06MF**
and **Stacks 06N3**. The index type is arbitrary: only `Small.{u} I` is needed, which the
existence of the coproduct of the underlying schemes already forces.

Nothing beyond clause (1) of **Stacks 026O** — that `𝒳` is fibred in groupoids — and the stack
condition of **Stacks 026F** is used, so `𝒳` need not be an algebraic stack. That is what lets
the charts of a family be glued into a scheme-valued point of a category fibred in groupoids
whose algebraicity is being proved, as in **Stacks 06DC**. -/
theorem exists_stackMap_comp_iso_of_isColimit
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (hst : 𝒳.val.p.IsStack (topology B S hS))
    {I : Type v} [Small.{u} I] (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS)
    (jj : ∀ i, Z i ⟶ W)
    (hW : Limits.IsColimit (Limits.Cofan.mk ((toScheme B S hS).obj W)
      (fun i => (toScheme B S hS).map (jj i))))
    (f : ∀ i, schemeFibredCategory B S hS (Z i) ⟶ 𝒳) :
    ∃ g : schemeFibredCategory B S hS W ⟶ 𝒳,
      ∀ i, Nonempty (schemeFibredCategoryMap B S hS (jj i) ≫ g ≅ f i) := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  obtain ⟨y, hy⟩ := CategoryTheory.Functor.exists_fiber_glue_of_disjointCover_of_isStack hst
    (hm := fun i => Space.mono_of_isColimit_toScheme B S hS Z W jj hW i)
    (hj := sieve_ofArrows_mem_topology_of_isColimit B S hS Z W jj hW)
    (hd := fun {_ _} hii' {_} a b hab =>
      bot_mem_topology_of_commSq_of_isColimit_toScheme B S hS Z W jj hW hii' a b hab)
    (x := fun i => stackMapFibreObject B S hS (Z i) (f i))
  refine ⟨fibreObjectFibredMap B S hS 𝒳 W y, fun i => ?_⟩
  set xi := stackMapFibreObject B S hS (Z i) (f i) with hxi
  have h₁ : 𝒳.val.p.IsHomLift (𝟙 (Z i))
      (Functor.Fiber.fiberInclusion.map (hy i).some.inv) := (hy i).some.inv.2
  have h₂ : 𝒳.val.p.IsHomLift (jj i)
      (Functor.IsPreFibered.pullbackMap y.2 (jj i)) :=
    (Functor.IsPreFibered.pullbackMap.IsCartesian y.2 (jj i)).toIsHomLift
  have hψ : 𝒳.val.p.IsHomLift (jj i)
      (Functor.Fiber.fiberInclusion.map (hy i).some.inv ≫
        Functor.IsPreFibered.pullbackMap y.2 (jj i)) :=
    @CategoryTheory.IsHomLift.comp_lift_id_left' _ _ _ _ 𝒳.val.p _ _ _ (Z i)
      (Functor.Fiber.fiberInclusion.map (hy i).some.inv) h₁ _ _ (jj i)
      (Functor.IsPreFibered.pullbackMap y.2 (jj i)) h₂
  have iso := fibreObjectStackMapFactorIso B S hS (𝟙 𝒳) (jj i) xi y _ hψ
  exact ⟨(((Bicategory.rightUnitor (fibreObjectFibredMap B S hS 𝒳 (Z i) xi)).symm ≪≫
      iso).symm) ≪≫ fibreObjectStackMapEvaluationIso B S hS (Z i) (f i)⟩

/-- **The coproduct of a family of 1-morphisms into an algebraic stack**, at the coproduct
`AlgebraicGeometry.BigFppfOver.sigmaOver` of the family of site objects.

This is `AlgebraicGeometry.Stack.exists_stackMap_comp_iso_of_isColimit` read in the 2-category of
algebraic stacks of **Stacks 03YP**, a full sub-2-category of the 2-category of categories fibred
in groupoids: the stack condition comes from algebraicity of `𝒳`, and the 1-morphism and the
2-isomorphisms are those of the ambient 2-category, wrapped. -/
theorem exists_stackMap_comp_iso_sigmaOver {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {I : Type v} [Small.{u} I] (Z : I → BigFppfOver B S hS)
    (hsum : B.Contains (∐ fun i => (toScheme B S hS).obj (Z i)))
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳) :
    ∃ g : schemeStack.{u, w} B S hS (sigmaOver B S hS Z hsum) ⟶ 𝒳,
      ∀ i, Nonempty (schemeStackMap.{u, w} B S hS (sigmaOverInj B S hS Z hsum i) ≫ g ≅ f i) := by
  have hst : 𝒳.val.val.p.IsStack (topology B S hS) := by
    obtain ⟨-, ⟨h, -⟩, -⟩ := 𝒳.property
    exact h
  obtain ⟨g, hg⟩ := exists_stackMap_comp_iso_of_isColimit B S hS hst Z _ _
    (isColimit_toScheme_sigmaOver B S hS Z hsum) (fun i => (f i).hom)
  refine ⟨Bicategory.InducedBicategory.mkHom
    (X := schemeStack.{u, w} B S hS (sigmaOver B S hS Z hsum)) (Y := 𝒳) g, fun i => ?_⟩
  exact ⟨Bicategory.InducedBicategory.isoMk
    (f := schemeStackMap.{u, w} B S hS (sigmaOverInj B S hS Z hsum i) ≫
      Bicategory.InducedBicategory.mkHom
        (X := schemeStack.{u, w} B S hS (sigmaOver B S hS Z hsum)) (Y := 𝒳) g)
    (g := f i) (hg i).some⟩

/-- **The coproduct of a family of 1-morphisms into an algebraic stack** for every family
indexed by a type of cardinality below the site's cutoff, where the coproduct of the underlying
schemes satisfies the size bound of its own accord
(`AlgebraicGeometry.BigFppfSite.contains_sigma_of_lt_cof`). This is the form the chart
`W = ∐_x Z_x` of the proofs of **Stacks 06MF** and **Stacks 06N3** is built in: the index type
is the type of finite type points of `𝒳`, with no countability restriction. -/
theorem exists_stackMap_comp_iso_sigmaOver_of_lt_cof {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {I : Type u} (hI : Cardinal.mk I < B.cutoff.ord.cof) (Z : I → BigFppfOver B S hS)
    (f : ∀ i, schemeStack.{u, w} B S hS (Z i) ⟶ 𝒳) :
    ∃ g : schemeStack.{u, w} B S hS (sigmaOver B S hS Z
        (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2)) ⟶ 𝒳,
      ∀ i, Nonempty (schemeStackMap.{u, w} B S hS (sigmaOverInj B S hS Z
        (B.contains_sigma_of_lt_cof hI _ fun i => (Z i).left.2) i) ≫ g ≅ f i) :=
  exists_stackMap_comp_iso_sigmaOver B S hS Z _ f

end AlgebraicGeometry.Stack

end
