module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.SimplicialObject.SSetHom
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Skeleton
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic

/-!
# Permanence of coverings, and restriction of `Hom` objects along finite inclusions

Let `C` be a site given by a pretopology `J`, let `C` have fibre products and let `X : C`. The
category of semi-representable objects over `X` — written `SR(C, X)` in the source — is the
category `FormalCoproduct (Over X)`, and a morphism of it is *covering* when its family of
components over each index of the target is a covering family of `C` (Tag 01G3, defined in
`StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic`).

This file proves the permanence properties of coverings of Tag 01G4 — stability under
composition, under base change and under products, in `SR(C)` and in `SR(C, X)` — and then
Tags 01GM and 01GN: for a hypercovering `K` of `X`, restriction along an inclusion `U ⊆ V` of
finite nonempty simplicial sets induces a covering morphism `Hom(V, K)₀ ⟶ Hom(U, K)₀` of
`SR(C, X)`. Along the way it records the *skeleton identity*
`i_{k!} sk_k Δ[k + 1] = ∂Δ[k + 1]`, which Stacks asserts in prose in Section 25.7 and which is
what identifies the matching object `(cosk_k sk_k K)_{k + 1}` with `Hom(∂Δ[k + 1], K)₀`.

## Main definitions

* `SSet.skObjStdSimplexIsoBoundary`: the skeleton identity
  `i_{k!} sk_k Δ[k + 1] ≅ ∂Δ[k + 1]`, with
  `SSet.skObjStdSimplexIsoBoundary_hom_ι` saying it is compatible with the counit of
  `i_{k!} ⊣ sk_k`.
* `pullbackFormalCoproduct`, with `.fst`, `.snd`, `.cone`, `.homEquiv` and `.isLimit`: the
  componentwise fibre product of two morphisms of formal coproducts, built from a chosen fibre
  product of each pair of components. See the implementation notes.
* `overPullbackCone` and `isLimitOverPullbackCone`: fibre products in a slice category,
  computed in the base.
* `representableByAppZero`, `representableByStdSimplex`, `representableByBoundaryZero` and
  `representableByBoundarySucc`: the four representing data that the proof of Tag 01GM feeds
  to Tag 017N — for `Hom(A, K)₀` with `A` arbitrary, `A = Δ[n]` (where the representing object
  is `K_n`), `A = ∂Δ[0]` (the terminal object) and `A = ∂Δ[k + 1]` (the matching object
  `(cosk_k sk_k K)_{k + 1}`).
* `homFromSSetMap`: the restriction morphism between two chosen models of `Hom` objects.
* `homFromSSet` and `homFromSSetIsHom`: a chosen `Hom(U, K)` for a finite simplicial set `U`,
  and its representing datum, obtained from Tag 017L.
* `homFromSSetRestriction`: restriction `Hom(V, K) ⟶ Hom(U, K)` along `U ⟶ V`.
* `transportHomFromSSet`: transport of a representing datum along an isomorphism of
  simplicial sets.

## Main results

* `IsCovering.comp` / `IsCoveringOver.comp`, `IsCovering.pullback` /
  `IsCoveringOver.pullback` and `IsCovering.prod_map` / `IsCoveringOver.prod_map` are the
  three parts of Tag 01G4, in `SR(C)` and in `SR(C, X)`. `IsCovering.of_isPullback` and
  `IsCoveringOver.of_isPullback` are the base-change part for an arbitrary fibre product
  square, which is the form the later proofs use.
* `isCoveringOver_homFromSSetMap_app_zero_of_oneMoreSimplex` is Tag 01GM: when `V` is obtained
  from a subcomplex `U` by adjoining a single `n`-simplex, with all new simplices in degrees
  above `n` degenerate, restriction is a covering. The proof writes `V` as the pushout
  `U ∐_{∂Δ[n]} Δ[n]` (Tag 018R), turns that into a fibre product of `Hom` objects
  (Tag 017N), and identifies the resulting arrow with `K_n ⟶ (cosk_{n - 1} sk_{n - 1} K)_n`,
  a covering by the definition of a hypercovering.
* `isCoveringOver_homFromSSetRestriction_app_zero` is Tag 01GN: restriction along any
  inclusion of finite nonempty simplicial sets is a covering. The proof filters the inclusion
  into one-cell attachments (`exists_ordered_filtration`, a refinement of Tag 018S) and
  composes.
* `boundarySucc_induced_eq_coskAdj_unit` identifies the morphism of `Hom` objects induced by
  `∂Δ[k + 1] ⟶ Δ[k + 1]` with the canonical morphism `K_{k + 1} ⟶ (cosk_k sk_k K)_{k + 1}`.
* `hasFiniteLimits_formalCoproductOver`: `SR(C, X)` has finite limits, which is what makes
  the `Hom` objects of Tag 017L exist.

## Implementation notes

The componentwise fibre product of formal coproducts is built here rather than taken from
Mathlib. `CategoryTheory.Limits.FormalCoproduct.pullbackCone` and its universal property
cannot be used from a module-ized file at the Mathlib revision this project pins: the binder
type of their family-of-cones argument mentions `eqToHom (by rw [i.2])`, which the elaborator
lifts to a constant private to Mathlib's own module, so any reference to those declarations
fails in the kernel with `unknown constant _private.…._proof_107`. The definitions here take
the family of cones with an explicitly written proof and so have no such dependency.
`FormalCoproduct.hom_ext_heq` is the `eqToHom`-free form of `FormalCoproduct.hom_ext`, used
where the two index maps agree only definitionally.

The universes are forced. For formal coproducts over `X` in a category `C : Type u` with
`Category.{v} C`, the index universe `w` is independent, and the hom-universe of
`FormalCoproduct.{w} (Over X)` is `max v w`; so the simplicial sets whose `Hom` objects live
in `SR(C, X)` are `SSet.{max w v}`, and that is the universe in which Tags 01GM and 01GN are
stated. The auxiliary results about `Hom` objects and matching objects are stated for an
arbitrary category `D : Type u'` with `Category.{v'} D` and `SSet.{v'}`, since they use
nothing about formal coproducts.

The `Hom` objects are only determined up to isomorphism, so the statements of Tags 01GM and
01GN quantify over a representing datum (`SimplicialObject.IsHomFromSSet`) rather than fixing
one; `homFromSSet` makes a choice for the places that need a specific object.

## References

* [Stacks Project, Tag 01G4](https://stacks.math.columbia.edu/tag/01G4)
* [Stacks Project, Tag 01GM](https://stacks.math.columbia.edu/tag/01GM)
* [Stacks Project, Tag 01GN](https://stacks.math.columbia.edu/tag/01GN)
-/

@[expose] public section

universe w v u v' u' uS

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SSet

/-- A subcomplex of `A` is contained in the `n`-skeleton as soon as it contains every
nondegenerate simplex of `A` in degrees below `n`. -/
private theorem skeleton_le_of_forall_mem {A : SSet.{uS}} (n : ℕ) {U : A.Subcomplex}
    (h : ∀ i < n, ∀ y : A.nonDegenerate i, y.1 ∈ U.obj (op ⦋i⦌)) : A.skeleton n ≤ U := by
  rw [SSet.skeleton]
  refine iSup_le fun i ↦ iSup_le fun y ↦ ?_
  rw [SSet.Subcomplex.ofSimplex_le_iff]
  exact h i i.2 y

/-- A subcomplex of bounded dimension is contained in the corresponding skeleton. -/
private theorem le_skeleton_of_hasDimensionLT_aux {A : SSet.{uS}} (B : A.Subcomplex) (n : ℕ)
    [SSet.HasDimensionLT B n] : B ≤ A.skeleton n := by
  rw [SSet.Subcomplex.le_iff_contains_nonDegenerate]
  intro m z hz
  obtain ⟨y, hy⟩ : ∃ y : (B : SSet) _⦋m⦌, B.ι.app _ y = z.1 := ⟨⟨z.1, hz⟩, rfl⟩
  have hy' : y ∈ (B : SSet).nonDegenerate m := by
    rw [← SSet.nonDegenerate_iff_of_mono B.ι, hy]
    exact z.2
  exact A.mem_skeleton _ (SSet.dim_lt_of_nonDegenerate (X := B) ⟨y, hy'⟩ n)

/-- The `n`-skeleton of the standard `n`-simplex is its boundary: a simplex of `Δ[n]` is
generated by simplices of dimension `< n` exactly when it is not surjective. This is the
identity `i_{n - 1 !} sk_{n - 1} Δ[n] = ∂Δ[n]` of Stacks, Section 25.7. -/
theorem stdSimplex.skeleton_eq_boundary (n : ℕ) :
    (Δ[n] : SSet.{uS}).skeleton n = ∂Δ[n] := by
  refine le_antisymm ?_ ?_
  · refine skeleton_le_of_forall_mem n fun i hi y ↦ ?_
    rw [SSet.boundary_obj_eq_univ i n hi]
    trivial
  · exact le_skeleton_of_hasDimensionLT_aux ∂Δ[n] n

/-- **The skeleton identity** `i_{k!} sk_k Δ[k + 1] = ∂Δ[k + 1]`: the `k`-skeleton of the
standard `(k + 1)`-simplex is its boundary. This is the identity asserted in prose in Stacks,
Section 25.7 (the proof of Tag 01GM), where it is used to identify the matching object
`(cosk_k sk_k K)_{k + 1}` with `Hom(∂Δ[k + 1], K)₀`. -/
noncomputable def skObjStdSimplexIsoBoundary (k : ℕ) :
    (SSet.sk k).obj (Δ[k + 1] : SSet.{uS}) ≅ (∂Δ[k + 1] : SSet.{uS}) :=
  Classical.choose (SSet.exists_iso_skeleton_hom_ι_eq_skAdj_counit
      (Δ[k + 1] : SSet.{uS}) k) ≪≫
    SSet.Subcomplex.eqToIso (stdSimplex.skeleton_eq_boundary (k + 1))

/-- The skeleton identity is compatible with the counit of `i_{k!} ⊣ sk_k`: the isomorphism
`i_{k!} sk_k Δ[k + 1] ≅ ∂Δ[k + 1]` followed by the boundary inclusion is that counit. -/
theorem skObjStdSimplexIsoBoundary_hom_ι (k : ℕ) :
    (skObjStdSimplexIsoBoundary.{uS} k).hom ≫ ∂Δ[k + 1].ι =
      (SSet.skAdj k).counit.app (Δ[k + 1] : SSet.{uS}) := by
  simpa [skObjStdSimplexIsoBoundary, SSet.Subcomplex.eqToIso]
    using Classical.choose_spec (SSet.exists_iso_skeleton_hom_ι_eq_skAdj_counit
      (Δ[k + 1] : SSet.{uS}) k)

end SSet

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-! ### Tag 01G4: permanence of coverings -/

section Permanence

/-- An isomorphism of formal coproducts is a covering morphism. -/
theorem IsCovering.of_isIso (J : Pretopology C) {U V : FormalCoproduct.{w} C} (e : U ⟶ V)
    [IsIso e] : IsCovering J e := by
  intro j
  let _ : Unique { i : U.I // e.f i = j } :=
    { default := ⟨(inv e).f j, f_inv_f e j⟩
      uniq := by
        rintro ⟨i, hi⟩
        exact Subtype.ext ((inv_f_f e i).symm.trans (congrArg (inv e).f hi)) }
  rw [Presieve.ofArrows_of_unique]
  exact J.has_isos _

/-- An isomorphism of formal coproducts of objects over `X` is a covering morphism. -/
theorem IsCoveringOver.of_isIso (J : Pretopology C) {X : C}
    {U V : FormalCoproduct.{w} (Over X)} (e : U ⟶ V) [IsIso e] : IsCoveringOver J e := by
  rw [isCoveringOver_iff_isCovering]
  exact IsCovering.of_isIso J _

/-- **Stacks Project, Tag 01G4, part (1).** The composition of two covering morphisms of
semi-representable objects is a covering morphism. -/
@[stacks 01G4 "part (1), for `SR(C)`"]
theorem IsCovering.comp (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {U V W : FormalCoproduct.{w} C} {f : U ⟶ V} {g : V ⟶ W}
    (hf : IsCovering J f) (hg : IsCovering J g) : IsCovering J (f ≫ g) := by
  intro k
  have h := Precoverage.comp_mem_coverings (J := J.toPrecoverage)
    (fun j : { j : V.I // g.f j = k } ↦ g.φ j.1 ≫ eqToHom (congrArg W.obj j.2)) (hg k)
    (fun j (i : { i : U.I // f.f i = j.1 }) ↦ f.φ i.1 ≫ eqToHom (congrArg V.obj i.2))
    (fun j ↦ hf j.1)
  convert h using 1
  refine le_antisymm ?_ ?_
  · rintro Y a ⟨i⟩
    exact .mk' ⟨⟨f.f i.1, i.2⟩, ⟨i.1, rfl⟩⟩ rfl (by simp)
  · rintro Y a ⟨⟨⟨j, hj⟩, ⟨i, hi⟩⟩⟩
    dsimp at hi
    subst j
    exact .mk' ⟨i, hj⟩ rfl (by simp)

/-- **Stacks Project, Tag 01G4, part (1).** The composition of two covering morphisms of
semi-representable objects over `X` is a covering morphism. -/
@[stacks 01G4 "part (1), for `SR(C, X)`"]
theorem IsCoveringOver.comp (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {U V W : FormalCoproduct.{w} (Over X)} {f : U ⟶ V} {g : V ⟶ W}
    (hf : IsCoveringOver J f) (hg : IsCoveringOver J g) : IsCoveringOver J (f ≫ g) := by
  rw [isCoveringOver_iff_isCovering] at hf hg ⊢
  rw [Functor.map_comp]
  exact hf.comp J hg

end Permanence

/-! ### Componentwise fibre products of formal coproducts -/

section FormalCoproductPullback

variable {D : Type u} [Category.{v} D] {U V W : FormalCoproduct.{w} D}

/-- Two morphisms of formal coproducts with equal index maps and heterogeneously equal
component families are equal. Unlike `FormalCoproduct.hom_ext` this has no `eqToHom`, so it
applies when the index maps agree only definitionally. -/
theorem FormalCoproduct.hom_ext_heq {a b : U ⟶ V} (h₁ : a.f = b.f) (h₂ : HEq a.φ b.φ) :
    a = b := by
  obtain ⟨af, aφ⟩ := a
  obtain ⟨bf, bφ⟩ := b
  cases h₁
  cases h₂
  rfl

variable (f : U ⟶ V) (g : W ⟶ V)
  (P : ∀ i : Function.Pullback f.f g.f,
    PullbackCone (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)) (g.φ i.1.2))

/-- The componentwise fibre product of two morphisms of formal coproducts: it is indexed by
the pairs of indices with a common image, and its component at such a pair is the given fibre
product of the corresponding component morphisms. -/
@[simps] def pullbackFormalCoproduct : FormalCoproduct.{w} D where
  I := Function.Pullback f.f g.f
  obj i := (P i).pt

namespace pullbackFormalCoproduct

/-- The first projection of the componentwise fibre product of formal coproducts. -/
@[simps] def fst : pullbackFormalCoproduct f g P ⟶ U where
  f i := i.1.1
  φ i := (P i).fst

/-- The second projection of the componentwise fibre product of formal coproducts. -/
@[simps] def snd : pullbackFormalCoproduct f g P ⟶ W where
  f i := i.1.2
  φ i := (P i).snd

/-- The two projections of the componentwise fibre product of formal coproducts form a
commuting square. -/
theorem condition : fst f g P ≫ f = snd f g P ≫ g :=
  FormalCoproduct.hom_ext (funext fun i ↦ i.2)
    (fun i ↦ (Category.assoc _ _ _).trans (P i).condition)

/-- The componentwise fibre product cone of two morphisms of formal coproducts. -/
def cone : PullbackCone f g := PullbackCone.mk _ _ (condition f g P)

variable (hP : ∀ i, IsLimit (P i))

/-- The universal property of the componentwise fibre product of formal coproducts: a
morphism into it is a commuting pair of morphisms into the two factors. -/
def homEquiv (T : FormalCoproduct.{w} D) :
    (T ⟶ pullbackFormalCoproduct f g P) ≃
      { p : (T ⟶ U) × (T ⟶ W) // p.1 ≫ f = p.2 ≫ g } where
  toFun m := ⟨⟨m ≫ fst f g P, m ≫ snd f g P⟩,
    by rw [Category.assoc, Category.assoc, condition]⟩
  invFun s :=
    { f := fun i ↦ ⟨(s.1.1.f i, s.1.2.f i), congrFun (congrArg FormalCoproduct.Hom.f s.2) i⟩
      φ := fun i ↦ (hP _).lift (PullbackCone.mk (s.1.1.φ i) (s.1.2.φ i)
        (by simpa [Category.assoc] using ((FormalCoproduct.hom_ext_iff' _ _).1 s.2 i).2)) }
  left_inv m := FormalCoproduct.hom_ext_heq rfl (heq_of_eq (funext fun i ↦
    (hP _).hom_ext ((P _).equalizer_ext
      ((hP _).fac _ WalkingCospan.left) ((hP _).fac _ WalkingCospan.right))))
  right_inv s := Subtype.ext (Prod.ext
    (FormalCoproduct.hom_ext_heq rfl
      (heq_of_eq (funext fun i ↦ (hP _).fac _ WalkingCospan.left)))
    (FormalCoproduct.hom_ext_heq rfl
      (heq_of_eq (funext fun i ↦ (hP _).fac _ WalkingCospan.right))))

/-- The componentwise fibre product cone of two morphisms of formal coproducts is a fibre
product. -/
def isLimit : IsLimit (cone f g P) := by
  refine PullbackCone.IsLimit.mk _
    (fun s ↦ (homEquiv f g P hP s.pt).symm ⟨(s.fst, s.snd), s.condition⟩)
    (fun s ↦ congrArg (·.1.fst)
      ((homEquiv f g P hP s.pt).right_inv ⟨(s.fst, s.snd), s.condition⟩))
    (fun s ↦ congrArg (·.1.snd)
      ((homEquiv f g P hP s.pt).right_inv ⟨(s.fst, s.snd), s.condition⟩))
    (fun s m h₁ h₂ ↦ ?_)
  convert! ((homEquiv f g P hP s.pt).left_inv m).symm using 3
  rw [← h₁, ← h₂]
  rfl

end pullbackFormalCoproduct

end FormalCoproductPullback

section Permanence2

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The fibre product cone over `X` whose underlying object is the chosen fibre product
in `C`. -/
noncomputable def overPullbackCone {X : C} {U V W : Over X} (f : U ⟶ V) (g : W ⟶ V) :
    PullbackCone f g :=
  PullbackCone.mk
    (W := Over.mk (pullback.snd f.left g.left ≫ W.hom))
    (Over.homMk (pullback.fst f.left g.left) (by
      change pullback.fst f.left g.left ≫ U.hom = pullback.snd f.left g.left ≫ W.hom
      rw [← Over.w f, ← Over.w g, pullback.condition_assoc]))
    (Over.homMk (pullback.snd f.left g.left))
    (by ext; exact pullback.condition)

/-- The fibre product cone in the slice built from the one in `C` is a fibre product. -/
@[sga "4 IV 5.11.1" "special case"]
noncomputable def isLimitOverPullbackCone {X : C} {U V W : Over X} (f : U ⟶ V) (g : W ⟶ V) :
    IsLimit (overPullbackCone f g) :=
  (IsPullback.of_map_of_faithful (Over.forget X)
    (f := (overPullbackCone f g).fst) (g := (overPullbackCone f g).snd)
    (h := f) (i := g) (IsPullback.of_hasPullback f.left g.left)).isLimit

/-- The componentwise fibre products of two morphisms of semi-representable objects. -/
noncomputable abbrev pullbackConeFamily {U V W : FormalCoproduct.{w} C} (f : U ⟶ V)
    (g : W ⟶ V) (i : Function.Pullback f.f g.f) :
    PullbackCone (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)) (g.φ i.1.2) :=
  pullback.cone (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)) (g.φ i.1.2)

/-- The componentwise fibre products of two morphisms of semi-representable objects
over `X`. -/
noncomputable abbrev pullbackConeFamilyOver {X : C} {U V W : FormalCoproduct.{w} (Over X)}
    (f : U ⟶ V) (g : W ⟶ V) (i : Function.Pullback f.f g.f) :
    PullbackCone (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)) (g.φ i.1.2) :=
  overPullbackCone (f.φ i.1.1 ≫ eqToHom (congrArg V.obj i.2)) (g.φ i.1.2)

/-- **Stacks Project, Tag 01G4, part (2).** The base change of a covering morphism of
semi-representable objects along any morphism exists and is a covering morphism. -/
@[stacks 01G4 "part (2), for `SR(C)`"]
theorem IsCovering.pullback (J : Pretopology C) {U V W : FormalCoproduct.{w} C}
    (f : U ⟶ V) (g : W ⟶ V) (hf : IsCovering J f) :
    IsCovering J (pullbackFormalCoproduct.snd f g (pullbackConeFamily f g)) := by
  intro k
  show Presieve.ofArrows
    (fun i : { i : Function.Pullback f.f g.f // i.1.2 = k } ↦
      Limits.pullback (f.φ i.1.1.1 ≫ eqToHom (congrArg V.obj i.1.2)) (g.φ i.1.1.2))
    (fun i ↦ pullback.snd (f.φ i.1.1.1 ≫ eqToHom (congrArg V.obj i.1.2)) (g.φ i.1.1.2) ≫
      eqToHom (congrArg W.obj i.2)) ∈ _
  have h := J.pullbacks (g.φ k) _ (hf (g.f k))
  rw [← Presieve.ofArrows_pullback] at h
  convert h using 1
  refine le_antisymm ?_ ?_
  · rintro Y a ⟨⟨⟨⟨i, k'⟩, hi⟩, hk⟩⟩
    change k' = k at hk
    subst k'
    exact .mk' ⟨i, hi⟩ rfl (by simp)
  · rintro Y a ⟨⟨i, hi⟩⟩
    exact .mk' ⟨⟨⟨i, k⟩, hi⟩, rfl⟩ rfl (by simp)

/-- **Stacks Project, Tag 01G4, part (2).** The base change of a covering morphism of
semi-representable objects over `X` along any morphism exists and is a covering morphism. -/
@[stacks 01G4 "part (2), for `SR(C, X)`"]
theorem IsCoveringOver.pullback (J : Pretopology C) {X : C}
    {U V W : FormalCoproduct.{w} (Over X)} (f : U ⟶ V) (g : W ⟶ V) (hf : IsCoveringOver J f) :
    IsCoveringOver J (pullbackFormalCoproduct.snd f g (pullbackConeFamilyOver f g)) := by
  intro k
  show Presieve.ofArrows
    (fun i : { i : Function.Pullback f.f g.f // i.1.2 = k } ↦
      Limits.pullback (f.φ i.1.1.1 ≫ eqToHom (congrArg V.obj i.1.2)).left (g.φ i.1.1.2).left)
    (fun i ↦ pullback.snd (f.φ i.1.1.1 ≫ eqToHom (congrArg V.obj i.1.2)).left
      (g.φ i.1.1.2).left ≫ eqToHom (congrArg (fun j ↦ (W.obj j).left) i.2)) ∈ _
  have hf' : Presieve.ofArrows
      (fun i : { i : U.I // f.f i = g.f k } ↦ (U.obj i.1).left)
      (fun i ↦ (f.φ i.1 ≫ eqToHom (congrArg V.obj i.2)).left) ∈ J (V.obj (g.f k)).left := by
    simpa only [Over.comp_left, Over.eqToHom_left] using hf (g.f k)
  have h := J.pullbacks (g.φ k).left _ hf'
  rw [← Presieve.ofArrows_pullback] at h
  convert h using 1
  refine le_antisymm ?_ ?_
  · rintro Y a ⟨⟨⟨⟨i, k'⟩, hi⟩, hk⟩⟩
    change k' = k at hk
    subst k'
    exact .mk' ⟨i, hi⟩ rfl (by simp)
  · rintro Y a ⟨⟨i, hi⟩⟩
    exact .mk' ⟨⟨⟨i, k⟩, hi⟩, rfl⟩ rfl (by simp)

/-- Base change of a covering morphism of semi-representable objects along an arbitrary
fibre product square. -/
theorem IsCovering.of_isPullback (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {P U V W : FormalCoproduct.{w} C} {p : P ⟶ U} {q : P ⟶ W} {f : U ⟶ V} {g : W ⟶ V}
    (h : IsPullback p q f g) (hf : IsCovering J f) : IsCovering J q := by
  have hc := IsPullback.of_isLimit (pullbackFormalCoproduct.isLimit f g
    (pullbackConeFamily f g) (fun i ↦ pullback.isLimit _ _))
  rw [← h.isoIsPullback_hom_snd _ _ hc]
  exact (IsCovering.of_isIso J (h.isoIsPullback _ _ hc).hom).comp J
    (IsCovering.pullback J f g hf)

/-- Base change of a covering morphism of semi-representable objects over `X` along an
arbitrary fibre product square. -/
theorem IsCoveringOver.of_isPullback (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    {P U V W : FormalCoproduct.{w} (Over X)} {p : P ⟶ U} {q : P ⟶ W} {f : U ⟶ V} {g : W ⟶ V}
    (h : IsPullback p q f g) (hf : IsCoveringOver J f) : IsCoveringOver J q := by
  have hc := IsPullback.of_isLimit (pullbackFormalCoproduct.isLimit f g
    (pullbackConeFamilyOver f g) (fun i ↦ isLimitOverPullbackCone _ _))
  rw [← h.isoIsPullback_hom_snd _ _ hc]
  exact (IsCoveringOver.of_isIso J (h.isoIsPullback _ _ hc).hom).comp J
    (IsCoveringOver.pullback J f g hf)

omit [HasPullbacks C] in
/-- The second projection of a binary product is the base change of the morphism to the
terminal factor along itself. -/
theorem isPullback_prod_snd [HasBinaryProducts C] {B K L : C} (g : K ⟶ L) :
    IsPullback (prod.snd : B ⨯ K ⟶ K) (prod.map (𝟙 B) g) g (prod.snd : B ⨯ L ⟶ L) := by
  refine IsPullback.mk' (by simp) (fun T φ φ' h₁ h₂ ↦ ?_) (fun T a b hab ↦ ?_)
  · refine prod.hom_ext ?_ h₁
    simpa using congrArg (fun q ↦ q ≫ prod.fst) h₂
  · exact ⟨prod.lift (b ≫ prod.fst) a, by simp, prod.hom_ext (by simp) (by simpa using hab)⟩

/-- **Stacks Project, Tag 01G4, part (3).** The product of two covering morphisms of
semi-representable objects is a covering morphism. -/
@[stacks 01G4 "part (3), for `SR(C)`"]
theorem IsCovering.prod_map (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    [HasBinaryProducts (FormalCoproduct.{w} C)]
    {A B K L : FormalCoproduct.{w} C} {f : A ⟶ B} {g : K ⟶ L}
    (hf : IsCovering J f) (hg : IsCovering J g) : IsCovering J (prod.map f g) := by
  rw [show prod.map f g = prod.map f (𝟙 K) ≫ prod.map (𝟙 B) g by
    refine prod.hom_ext ?_ ?_ <;> simp]
  exact (IsCovering.of_isPullback J (IsPullback.of_prod_fst_with_id f K) hf).comp J
    (IsCovering.of_isPullback J (isPullback_prod_snd (B := B) g) hg)

/-- **Stacks Project, Tag 01G4, part (3).** The product of two covering morphisms of
semi-representable objects over `X` is a covering morphism. -/
@[stacks 01G4 "part (3), for `SR(C, X)`"]
theorem IsCoveringOver.prod_map (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    [HasBinaryProducts (FormalCoproduct.{w} (Over X))]
    {A B K L : FormalCoproduct.{w} (Over X)} {f : A ⟶ B} {g : K ⟶ L}
    (hf : IsCoveringOver J f) (hg : IsCoveringOver J g) :
    IsCoveringOver J (prod.map f g) := by
  rw [show prod.map f g = prod.map f (𝟙 K) ≫ prod.map (𝟙 B) g by
    refine prod.hom_ext ?_ ?_ <;> simp]
  exact (IsCoveringOver.of_isPullback J (IsPullback.of_prod_fst_with_id f K) hf).comp J
    (IsCoveringOver.of_isPullback J (isPullback_prod_snd (B := B) g) hg)

end Permanence2

/-! ### Degree-zero `Hom` objects as representing objects -/

section HomZero

variable {D : Type u'} [Category.{v'} D]

/-- Evaluation of simplicial objects in degree zero is right adjoint to the constant
simplicial object functor. -/
noncomputable def constEvalZeroAdj :
    SimplicialObject.const D ⊣ (evaluation SimplexCategoryᵒᵖ D).obj (op ⦋0⦌) where
  unit := (Functor.constCompEvaluationObj D (op ⦋0⦌)).hom
  counit :=
    { app := fun F ↦
        { app := fun X ↦ F.map (SimplexCategory.isTerminalZero.from X.unop).op
          naturality := fun _ _ _ ↦ by
            simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.id_obj,
              Functor.const_obj_map, Category.id_comp, ← Functor.map_comp]
            congr 1 }
      naturality := by intros; ext; simp }
  left_triangle_components X := by ext; simp
  right_triangle_components F := by simp

/-- Morphisms of simplicial sets `A ⟶ K ⋙ Mor(X, -)` are the `A`-indexed families of
morphisms from the constant simplicial object at `X` to `K`. -/
def constHomObjEquiv (A : SSet.{v'}) (K : SimplicialObject D) (X : D) :
    Functor.HomObj ((SimplicialObject.const D).obj X) K A ≃
      (A ⟶ K ⋙ coyoneda.obj (op X)) where
  toFun z :=
    { app := fun m ↦ ↾fun a ↦ z.app m a
      naturality := by
        intro m m' φ
        ext a
        simpa using z.naturality φ a }
  invFun z :=
    { app := fun m a ↦ z.app m a
      naturality := by
        intro m m' φ a
        simp }
  left_inv z := by ext m a; rfl
  right_inv z := by ext m a; rfl

/-- The degree-zero object of a `Hom(A, K)` represents the presheaf
`X ↦ Mor(A, K ⋙ Mor(X, -))`, i.e. `X ↦ Mor(X × A, K)`. -/
noncomputable def representableByAppZero (A : SSet.{v'}) (K H : SimplicialObject D)
    (h : SimplicialObject.IsHomFromSSet A K H) :
    (coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ D (Type v')).obj K ⋙
      coyoneda.obj (op A)).RepresentableBy (H.obj (op ⦋0⦌)) where
  homEquiv {X} :=
    ((constEvalZeroAdj (D := D)).homEquiv X H).symm.trans h.homEquiv |>.trans
      (Functor.functorHomEquiv ((SimplicialObject.const D).obj X) K A) |>.trans
      (constHomObjEquiv A K X)
  homEquiv_comp {X Y} f g := by
    change (constHomObjEquiv A K X)
      ((Functor.functorHomEquiv ((SimplicialObject.const D).obj X) K A)
        (h.homEquiv ((constEvalZeroAdj (D := D)).homEquiv X H |>.symm (f ≫ g)))) = _
    rw [(constEvalZeroAdj (D := D)).homEquiv_naturality_left_symm f g, h.homEquiv_comp]
    ext m a
    rfl

/-- `K_n` represents `X ↦ Mor(Δ[n], K ⋙ Mor(X, -))`: this is the Yoneda lemma, and it is the
identification `Hom(Δ[n], K)₀ = K_n` of Tag 017L. -/
noncomputable def representableByStdSimplex (K : SimplicialObject D) (n : ℕ) :
    (coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ D (Type v')).obj K ⋙
      coyoneda.obj (op Δ[n])).RepresentableBy (K.obj (op ⦋n⦌)) where
  homEquiv {X} :=
    (SSet.yonedaEquiv (X := K ⋙ coyoneda.obj (op X)) (n := ⦋n⦌)).symm
  homEquiv_comp {X Y} f g := by
    change (SSet.yonedaEquiv (X := K ⋙ coyoneda.obj (op X)) (n := ⦋n⦌)).symm (f ≫ g) = _
    exact (SSet.yonedaEquiv_symm_comp g (Functor.whiskerLeft K (coyoneda.map f.op))).symm

/-- The boundary of the standard `0`-simplex is empty. -/
def isInitialBoundaryZero : IsInitial (∂Δ[0] : SSet.{v'}) := by
  rw [SSet.boundary_zero]
  exact SSet.Subcomplex.isInitialBot

/-- The terminal object represents `X ↦ Mor(∂Δ[0], K ⋙ Mor(X, -))`, since `∂Δ[0]` is empty:
this is `Hom(∂Δ[0], K)₀ = *`. -/
noncomputable def representableByBoundaryZero [HasTerminal D] (K : SimplicialObject D) :
    (coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ D (Type v')).obj K ⋙
      coyoneda.obj (op (∂Δ[0] : SSet.{v'}))).RepresentableBy (⊤_ D) where
  homEquiv {_X} :=
    { toFun := fun _ ↦ isInitialBoundaryZero.to _
      invFun := fun _ ↦ terminal.from _
      left_inv := fun _ ↦ terminal.hom_ext _ _
      right_inv := fun _ ↦ isInitialBoundaryZero.hom_ext _ _ }
  homEquiv_comp _ _ := isInitialBoundaryZero.hom_ext _ _

end HomZero

/-! ### The matching object as `Hom(∂Δ[k + 1], K)₀` -/

section Matching

variable {D : Type u'} [Category.{v'} D] (K : SimplicialObject D) (k : ℕ)
  [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ D,
    (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]

/-- The counit of the coskeleton adjunction after applying `Mor(X, -)`. -/
noncomputable def matchingCoyonedaCounit (X : D) :
    (SimplexCategory.Truncated.inclusion k).op ⋙
      (((SimplicialObject.cosk k).obj K) ⋙ coyoneda.obj (op X)) ⟶
      ((SimplicialObject.truncation k).obj K) ⋙ coyoneda.obj (op X) :=
  (Functor.associator (SimplexCategory.Truncated.inclusion k).op
    ((SimplicialObject.cosk k).obj K) (coyoneda.obj (op X))).inv ≫
      Functor.whiskerRight
        ((SimplicialObject.coskAdj k).counit.app
          ((SimplicialObject.truncation k).obj K)) (coyoneda.obj (op X))

/-- Since `Mor(X, -)` preserves limits and `cosk_k sk_k K` is a pointwise right Kan extension,
so is `(cosk_k sk_k K) ⋙ Mor(X, -)`. -/
instance matchingCoyonedaIsRightKanExtension (X : D) :
    (((SimplicialObject.cosk k).obj K) ⋙ coyoneda.obj (op X)).IsRightKanExtension
      (matchingCoyonedaCounit K k X) :=
  Functor.PreservesRightKanExtension.preserves
    (G := coyoneda.obj (op X)) (F := (SimplicialObject.truncation k).obj K)
    (L := (SimplexCategory.Truncated.inclusion k).op)
    ((SimplicialObject.cosk k).obj K)
    ((SimplicialObject.coskAdj k).counit.app ((SimplicialObject.truncation k).obj K))

/-- The bijection `Mor(X, (cosk_k sk_k K)_{k + 1}) = Mor(i_{k!} sk_k Δ[k + 1], K ⋙ Mor(X, -))`:
the Yoneda lemma, then the universal property of the right Kan extension, then the
adjunction `i_{k!} ⊣ sk_k`. -/
noncomputable def matchingSkeletonHomEquiv (X : D) :
    (X ⟶ ((SimplicialObject.cosk k).obj K).obj (op ⦋k + 1⦌)) ≃
      ((SSet.sk k).obj (Δ[k + 1] : SSet.{v'}) ⟶ K ⋙ coyoneda.obj (op X)) :=
  (SSet.yonedaEquiv
    (X := ((SimplicialObject.cosk k).obj K) ⋙ coyoneda.obj (op X)) (n := ⦋k + 1⦌)).symm.trans
    ((Functor.homEquivOfIsRightKanExtension
        (((SimplicialObject.cosk k).obj K) ⋙ coyoneda.obj (op X))
        (matchingCoyonedaCounit K k X) Δ[k + 1]).trans
      ((SSet.skAdj k).homEquiv ((SSet.truncation k).obj (Δ[k + 1] : SSet.{v'}))
        (K ⋙ coyoneda.obj (op X))).symm)

/-- The interchange law between the coskeleton counit and the transformation induced by a
morphism of `D`. -/
theorem matchingCoyonedaCounit_naturality_right {X Y : D} (f : X ⟶ Y) :
    Functor.whiskerLeft (SimplexCategory.Truncated.inclusion k).op
        (Functor.whiskerLeft ((SimplicialObject.cosk k).obj K) (coyoneda.map f.op)) ≫
      matchingCoyonedaCounit K k X =
    matchingCoyonedaCounit K k Y ≫
      Functor.whiskerLeft (SimplexCategory.Truncated.inclusion k).op
        (Functor.whiskerLeft K (coyoneda.map f.op)) :=
  NatTrans.ext (funext fun _ ↦ ((coyoneda.map f.op).naturality _).symm)

end Matching

/-- Postcomposition with a morphism of right Kan extensions corresponds, under the universal
property, to postcomposition with the morphism it extends. -/
alias rightKanHomEquiv_naturality_right :=
  CategoryTheory.SimplicialObject.homEquivOfIsRightKanExtension_naturality_right

section Matching

variable {D : Type u'} [Category.{v'} D] (K : SimplicialObject D) (k : ℕ)
  [∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ D,
    (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]

/-- Naturality in `X` of `matchingSkeletonHomEquiv`. -/
theorem matchingSkeletonHomEquiv_comp {X Y : D} (f : X ⟶ Y)
    (g : Y ⟶ ((SimplicialObject.cosk k).obj K).obj (op ⦋k + 1⦌)) :
    matchingSkeletonHomEquiv K k X (f ≫ g) =
      matchingSkeletonHomEquiv K k Y g ≫ Functor.whiskerLeft K (coyoneda.map f.op) := by
  have hy : SSet.yonedaEquiv.symm (f ≫ g) = SSet.yonedaEquiv.symm g ≫
      Functor.whiskerLeft ((SimplicialObject.cosk k).obj K) (coyoneda.map f.op) := by
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  refine Eq.trans (congrArg ((SSet.skAdj k).homEquiv
    ((SSet.truncation k).obj (Δ[k + 1] : SSet.{v'}))
    (K ⋙ coyoneda.obj (op X))).symm ?_)
    ((SSet.skAdj k).homEquiv_naturality_right_symm _ _)
  rw [hy]
  exact rightKanHomEquiv_naturality_right (matchingCoyonedaCounit_naturality_right K k f) _ _

/-- **The matching object as a `Hom` object.** The degree-`(k + 1)` object of `cosk_k sk_k K`
represents `X ↦ Mor(∂Δ[k + 1], K ⋙ Mor(X, -))`, i.e. it is `Hom(∂Δ[k + 1], K)₀`. This combines
Tag 018V with the skeleton identity `i_{k!} sk_k Δ[k + 1] = ∂Δ[k + 1]`. -/
noncomputable def representableByBoundarySucc :
    (coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ D (Type v')).obj K ⋙
      coyoneda.obj (op (∂Δ[k + 1] : SSet.{v'}))).RepresentableBy
        (((SimplicialObject.cosk k).obj K).obj (op ⦋k + 1⦌)) where
  homEquiv {X} :=
    (matchingSkeletonHomEquiv K k X).trans
      { toFun := fun f ↦ (SSet.skObjStdSimplexIsoBoundary.{v'} k).inv ≫ f
        invFun := fun f ↦ (SSet.skObjStdSimplexIsoBoundary.{v'} k).hom ≫ f
        left_inv f := by simp
        right_inv f := by simp }
  homEquiv_comp {X Y} f g := by
    simp only [Equiv.trans_apply]
    rw [matchingSkeletonHomEquiv_comp K k f g]
    rfl

/-- The coskeleton unit, restricted to the truncated level through the universal property of
the right Kan extension, is the universal element: this is the computation behind the
identification of `K_{k + 1} ⟶ (cosk_k sk_k K)_{k + 1}` with restriction along the boundary
inclusion. -/
theorem homEquivOfIsRightKanExtension_coskAdj_unit :
    Functor.homEquivOfIsRightKanExtension
        (((SimplicialObject.cosk k).obj K) ⋙ coyoneda.obj (op (K.obj (op ⦋k + 1⦌))))
        (matchingCoyonedaCounit K k (K.obj (op ⦋k + 1⦌))) Δ[k + 1]
        (SSet.yonedaEquiv.symm
          (((SimplicialObject.coskAdj k).unit.app K).app (op ⦋k + 1⦌))) =
      Functor.whiskerLeft (SimplexCategory.Truncated.inclusion k).op
        ((SSet.yonedaEquiv (X := K ⋙ coyoneda.obj (op (K.obj (op ⦋k + 1⦌))))
          (n := ⦋k + 1⦌)).symm (𝟙 (K.obj (op ⦋k + 1⦌)))) := by
  ext m a
  let φ := SSet.stdSimplex.objEquiv a
  let η := (SimplicialObject.coskAdj k).unit.app K
  let ε := (SimplicialObject.coskAdj k).counit.app
    ((SimplicialObject.truncation k).obj K)
  have ht : η.app ((SimplexCategory.Truncated.inclusion k).op.obj m) ≫ ε.app m =
      𝟙 (K.obj ((SimplexCategory.Truncated.inclusion k).op.obj m)) := by
    have h := congrArg (fun t : (SimplicialObject.truncation k).obj K ⟶
      (SimplicialObject.truncation k).obj K ↦ t.app m)
      ((SimplicialObject.coskAdj k).left_triangle_components K)
    dsimp only [NatTrans.comp_app, NatTrans.id_app] at h
    exact h
  have hn := η.naturality φ.op
  change K.map φ.op ≫ η.app ((SimplexCategory.Truncated.inclusion k).op.obj m) =
    η.app (op ⦋k + 1⦌) ≫ ((SimplicialObject.cosk k).obj K).map φ.op at hn
  have h₀ : (η.app (op ⦋k + 1⦌) ≫ ((SimplicialObject.cosk k).obj K).map φ.op) ≫ ε.app m =
      (K.map φ.op ≫ η.app ((SimplexCategory.Truncated.inclusion k).op.obj m)) ≫ ε.app m :=
    congrArg (· ≫ ε.app m) hn.symm
  have hc : (η.app (op ⦋k + 1⦌) ≫ ((SimplicialObject.cosk k).obj K).map φ.op) ≫
      ε.app m = K.map φ.op :=
    h₀.trans ((Category.assoc _ _ _).trans (by rw [ht]; exact Category.comp_id _))
  rw [Functor.homEquivOfIsRightKanExtension_apply_app]
  simp only [matchingCoyonedaCounit]
  show (((SSet.yonedaEquiv
      (X := ((SimplicialObject.cosk k).obj K) ⋙
        coyoneda.obj (op (K.obj (op ⦋k + 1⦌))))
      (n := ⦋k + 1⦌)).symm (η.app (op ⦋k + 1⦌))).app
        ((SimplexCategory.Truncated.inclusion k).op.obj m) a) ≫ ε.app m =
    ((SSet.yonedaEquiv
      (X := K ⋙ coyoneda.obj (op (K.obj (op ⦋k + 1⦌))))
      (n := ⦋k + 1⦌)).symm (𝟙 (K.obj (op ⦋k + 1⦌)))).app
        ((SimplexCategory.Truncated.inclusion k).op.obj m) a
  have h₁ : ((SSet.yonedaEquiv
      (X := ((SimplicialObject.cosk k).obj K) ⋙
        coyoneda.obj (op (K.obj (op ⦋k + 1⦌))))
      (n := ⦋k + 1⦌)).symm (η.app (op ⦋k + 1⦌))).app
        ((SimplexCategory.Truncated.inclusion k).op.obj m) a =
      η.app (op ⦋k + 1⦌) ≫ ((SimplicialObject.cosk k).obj K).map φ.op := rfl
  have h₂ : ((SSet.yonedaEquiv
      (X := K ⋙ coyoneda.obj (op (K.obj (op ⦋k + 1⦌))))
      (n := ⦋k + 1⦌)).symm (𝟙 (K.obj (op ⦋k + 1⦌)))).app
        ((SimplexCategory.Truncated.inclusion k).op.obj m) a = K.map φ.op := by
    show (𝟙 (K.obj (op ⦋k + 1⦌))) ≫ K.map φ.op = K.map φ.op
    exact Category.id_comp _
  rw [h₁, h₂]
  exact hc

/-- The coskeleton unit, read through the bijection
`Mor(X, (cosk_k sk_k K)_{k + 1}) = Mor(i_{k!} sk_k Δ[k + 1], K ⋙ Mor(X, -))`, is the counit of
`i_{k!} ⊣ sk_k` followed by the universal element. -/
theorem matchingSkeletonHomEquiv_coskAdj_unit :
    matchingSkeletonHomEquiv K k (K.obj (op ⦋k + 1⦌))
      (((SimplicialObject.coskAdj k).unit.app K).app (op ⦋k + 1⦌)) =
    (SSet.skAdj k).counit.app (Δ[k + 1] : SSet.{v'}) ≫
      (SSet.yonedaEquiv (X := K ⋙ coyoneda.obj (op (K.obj (op ⦋k + 1⦌))))
        (n := ⦋k + 1⦌)).symm (𝟙 (K.obj (op ⦋k + 1⦌))) := by
  let s : (Δ[k + 1] : SSet.{v'}) ⟶ K ⋙ coyoneda.obj (op (K.obj (op ⦋k + 1⦌))) :=
    SSet.yonedaEquiv.symm (𝟙 (K.obj (op ⦋k + 1⦌)))
  have he : ((SSet.skAdj k).homEquiv
      ((SSet.truncation k).obj (Δ[k + 1] : SSet.{v'})) (Δ[k + 1] : SSet.{v'}))
        ((SSet.skAdj k).counit.app (Δ[k + 1] : SSet.{v'})) =
      𝟙 ((SSet.truncation k).obj (Δ[k + 1] : SSet.{v'})) := by
    rw [← (SSet.skAdj k).homEquiv_symm_id (Δ[k + 1] : SSet.{v'})]
    exact Equiv.apply_symm_apply _ _
  have hnat := (SSet.skAdj k).homEquiv_naturality_right
    ((SSet.skAdj k).counit.app (Δ[k + 1] : SSet.{v'})) s
  have hright : ((SSet.skAdj k).homEquiv
        ((SSet.truncation k).obj (Δ[k + 1] : SSet.{v'}))
        (K ⋙ coyoneda.obj (op (K.obj (op ⦋k + 1⦌)))))
        ((SSet.skAdj k).counit.app (Δ[k + 1] : SSet.{v'}) ≫ s) =
      Functor.whiskerLeft (SimplexCategory.Truncated.inclusion k).op s := by
    simp only [Functor.id_obj] at hnat
    rw [hnat, he, Category.id_comp]
    rfl
  have hd : matchingSkeletonHomEquiv K k (K.obj (op ⦋k + 1⦌))
      (((SimplicialObject.coskAdj k).unit.app K).app (op ⦋k + 1⦌)) =
      ((SSet.skAdj k).homEquiv
        ((SSet.truncation k).obj (Δ[k + 1] : SSet.{v'}))
        (K ⋙ coyoneda.obj (op (K.obj (op ⦋k + 1⦌))))).symm
          (Functor.homEquivOfIsRightKanExtension
            (((SimplicialObject.cosk k).obj K) ⋙
              coyoneda.obj (op (K.obj (op ⦋k + 1⦌))))
            (matchingCoyonedaCounit K k (K.obj (op ⦋k + 1⦌))) Δ[k + 1]
            (SSet.yonedaEquiv.symm
              (((SimplicialObject.coskAdj k).unit.app K).app (op ⦋k + 1⦌)))) := rfl
  rw [hd, homEquivOfIsRightKanExtension_coskAdj_unit K k]
  exact ((SSet.skAdj k).homEquiv
    ((SSet.truncation k).obj (Δ[k + 1] : SSet.{v'}))
    (K ⋙ coyoneda.obj (op (K.obj (op ⦋k + 1⦌))))).symm_apply_eq.2 hright.symm

/-- The morphism of `Hom` objects induced by the boundary inclusion `∂Δ[k + 1] ⟶ Δ[k + 1]` is
the canonical map from `K_{k + 1}` to the matching object `(cosk_k sk_k K)_{k + 1}`. -/
theorem boundarySucc_induced_eq_coskAdj_unit :
    (representableByBoundarySucc K k).homEquiv.symm
      (∂Δ[k + 1].ι ≫ (representableByStdSimplex K (k + 1)).homEquiv
        (𝟙 (K.obj (op ⦋k + 1⦌)))) =
      ((SimplicialObject.coskAdj k).unit.app K).app (op ⦋k + 1⦌) := by
  apply (representableByBoundarySucc K k).homEquiv.injective
  simp only [Equiv.apply_symm_apply]
  dsimp [representableByStdSimplex, representableByBoundarySucc]
  rw [matchingSkeletonHomEquiv_coskAdj_unit, ← SSet.skObjStdSimplexIsoBoundary_hom_ι]
  simp only [← Category.assoc, (SSet.skObjStdSimplexIsoBoundary.{v'} k).inv_hom_id,
    Category.id_comp]

end Matching

/-! ### Tag 01GM: adjoining one simplex -/

section OneMoreSimplex

/-- The canonical restriction morphism between two chosen models of `Hom` objects, obtained
from the universal property of the target model. -/
noncomputable def homFromSSetMap {D : Type u'} [Category.{v'} D] {A B : SSet.{v'}}
    {K HA HB : SimplicialObject D} (hB : SimplicialObject.IsHomFromSSet B K HB)
    (hA : SimplicialObject.IsHomFromSSet A K HA) (i : A ⟶ B) : HB ⟶ HA :=
  hA.homEquiv.symm (i ≫ hB.homEquiv (𝟙 HB))

/-- In degree zero, the restriction morphism of `Hom` objects is the morphism induced by the
representing data of the degree-zero objects. -/
theorem homFromSSetMap_app_zero {D : Type u'} [Category.{v'} D] {A B : SSet.{v'}}
    {K HA HB : SimplicialObject D} (hB : SimplicialObject.IsHomFromSSet B K HB)
    (hA : SimplicialObject.IsHomFromSSet A K HA) (i : A ⟶ B) :
    (homFromSSetMap hB hA i).app (op ⦋0⦌) =
      (representableByAppZero A K HA hA).homEquiv.symm
        (i ≫ (representableByAppZero B K HB hB).homEquiv (𝟙 (HB.obj (op ⦋0⦌)))) := by
  apply (representableByAppZero A K HA hA).homEquiv.injective
  simp only [Equiv.apply_symm_apply]
  let b : (SimplicialObject.const D).obj (HB.obj (op ⦋0⦌)) ⟶ HB :=
    ((constEvalZeroAdj (D := D)).homEquiv _ HB).symm (𝟙 _)
  have hadj : ((constEvalZeroAdj (D := D)).homEquiv _ HA).symm
      ((homFromSSetMap hB hA i).app (op ⦋0⦌)) = b ≫ homFromSSetMap hB hA i := by
    simpa [b, evaluation] using
      ((constEvalZeroAdj (D := D)).homEquiv_naturality_right_symm
        (𝟙 _) (homFromSSetMap hB hA i))
  have heq : hA.homEquiv (b ≫ homFromSSetMap hB hA i) = i ≫ hB.homEquiv b := by
    rw [hA.homEquiv_comp, homFromSSetMap, Equiv.apply_symm_apply]
    have hbcomp := hB.homEquiv_comp b (𝟙 HB)
    simp only [Category.comp_id] at hbcomp
    rw [hbcomp]
    rfl
  show (constHomObjEquiv A K (HB.obj (op ⦋0⦌)))
      ((Functor.functorHomEquiv _ K A)
        (hA.homEquiv (((constEvalZeroAdj (D := D)).homEquiv _ HA).symm
          ((homFromSSetMap hB hA i).app (op ⦋0⦌))))) =
    i ≫ (constHomObjEquiv B K (HB.obj (op ⦋0⦌)))
      ((Functor.functorHomEquiv _ K B)
        (hB.homEquiv (((constEvalZeroAdj (D := D)).homEquiv _ HB).symm (𝟙 _))))
  rw [hadj, heq]
  rfl

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- If a subcomplex contains every simplex of the ambient simplicial set in each degree below
`n`, it contains the `n`-skeleton. -/
theorem skeleton_le_of_bijective_below {V : SSet.{uS}} (U : V.Subcomplex) (n : ℕ)
    (h : ∀ m < n, Function.Bijective (U.ι.app (op ⦋m⦌))) : V.skeleton n ≤ U := by
  refine SSet.skeleton_le_of_forall_mem n fun i hi y ↦ ?_
  obtain ⟨z, hz⟩ := (h i hi).2 y.1
  rw [← hz]
  exact z.2

/-- The image of the boundary of the standard `n`-simplex under the map classifying an
`n`-simplex lies in the `n`-skeleton. -/
theorem range_boundary_le_skeleton {V : SSet.{uS}} (n : ℕ) (x : V.obj (op ⦋n⦌)) :
    SSet.Subcomplex.range (∂Δ[n].ι ≫ SSet.yonedaEquiv.symm x) ≤ V.skeleton n := by
  rw [← SSet.Subcomplex.image_eq_range, ← SSet.stdSimplex.skeleton_eq_boundary,
    SSet.Subcomplex.image_le_iff]
  exact SSet.skeleton_le_of_forall_mem n fun i hi y ↦ V.mem_skeleton _ hi

/-- **Stacks Project, Tag 01GM.** Let `K` be a hypercovering of `X`. If the finite simplicial
set `V` is obtained from a subcomplex `U` by adjoining a single `n`-simplex `x`, with every
simplex of `V` outside `U` in degree above `n` degenerate, then the restriction morphism
`Hom(V, K)₀ ⟶ Hom(U, K)₀` is a covering in `SR(C, X)`. -/
@[stacks 01GM]
theorem isCoveringOver_homFromSSetMap_app_zero_of_oneMoreSimplex (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hK : IsHypercovering J K)
    (V : SSet.{max w v}) (U : V.Subcomplex)
    [SSet.Finite (U : SSet.{max w v})]
    (_hUnonempty : ∀ m : ℕ, Nonempty (U.obj (op ⦋m⦌)))
    (_hVfinite : ∀ m : ℕ, Finite (V.obj (op ⦋m⦌)))
    (_hVnonempty : ∀ m : ℕ, Nonempty (V.obj (op ⦋m⦌)))
    (n : ℕ) (x : V.obj (op ⦋n⦌))
    (hx : x ∉ Set.range (U.ι.app (op ⦋n⦌)))
    (hbelow : ∀ m < n, Function.Bijective (U.ι.app (op ⦋m⦌)))
    (hat : ∀ y : V.obj (op ⦋n⦌), y ∈ Set.range (U.ι.app (op ⦋n⦌)) ∨ y = x)
    (habove : ∀ m, n < m → ∀ y : V.obj (op ⦋m⦌),
      y ∉ Set.range (U.ι.app (op ⦋m⦌)) → y ∈ V.degenerate m)
    (HV HU : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hV : SimplicialObject.IsHomFromSSet V K HV)
    (hU : SimplicialObject.IsHomFromSSet U K HU) :
    IsCoveringOver J ((homFromSSetMap hV hU U.ι).app (op ⦋0⦌)) := by
  have hrange (m : ℕ) (y : V.obj (op ⦋m⦌)) :
      y ∈ Set.range (U.ι.app (op ⦋m⦌)) ↔ y ∈ U.obj (op ⦋m⦌) := by
    refine ⟨?_, fun hy ↦ ⟨⟨y, hy⟩, rfl⟩⟩
    rintro ⟨⟨z, hz⟩, rfl⟩
    exact hz
  have hx' : x ∉ U.obj (op ⦋n⦌) := (hrange n x).not.mp hx
  have hlt : V.skeleton n ≤ U := skeleton_le_of_bijective_below U n hbelow
  have hat' : ∀ y : V.obj (op ⦋n⦌), y ∈ U.obj (op ⦋n⦌) ∨ y = x :=
    fun y ↦ (hat y).imp (hrange n y).mp id
  have habove' : ∀ m, n < m → ∀ y : V.obj (op ⦋m⦌),
      y ∉ U.obj (op ⦋m⦌) → y ∈ V.degenerate m :=
    fun m hm y hy ↦ habove m hm y ((hrange m y).not.mpr hy)
  have hbd : SSet.Subcomplex.range (∂Δ[n].ι ≫ SSet.yonedaEquiv.symm x) ≤ U :=
    (range_boundary_le_skeleton n x).trans hlt
  have hp := U.isPushout_boundary_ι x hx' hlt hat' habove' hbd
  have key (H₀ : FormalCoproduct.{w} (Over X))
      (R : (coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ _ (Type (max w v))).obj K ⋙
        coyoneda.obj (op (∂Δ[n] : SSet.{max w v}))).RepresentableBy H₀)
      (hc : IsCoveringOver J (R.homEquiv.symm (∂Δ[n].ι ≫
        (representableByStdSimplex K n).homEquiv (𝟙 (K.obj (op ⦋n⦌))))))  :
      IsCoveringOver J ((homFromSSetMap hV hU U.ι).app (op ⦋0⦌)) := by
    have hpb := SimplicialObject.isPullback_hom_of_isPushout K hp R
      (representableByAppZero U K HU hU) (representableByStdSimplex K n)
      (representableByAppZero V K HV hV)
    rw [homFromSSetMap_app_zero]
    exact IsCoveringOver.of_isPullback J hpb.flip hc
  cases n with
  | zero =>
    refine key _ (representableByBoundaryZero K) ?_
    rw [show (representableByBoundaryZero K).homEquiv.symm
        (∂Δ[0].ι ≫ (representableByStdSimplex K 0).homEquiv (𝟙 (K.obj (op ⦋0⦌)))) =
        terminal.from (K.obj (op ⦋0⦌)) from terminal.hom_ext _ _]
    exact hK.1
  | succ k =>
    let _ := hasPointwiseRightKanExtension_formalCoproductOver.{w} (X := X) k
    refine key _ (representableByBoundarySucc K k) ?_
    rw [boundarySucc_induced_eq_coskAdj_unit]
    exact hK.2 k

end OneMoreSimplex

/-! ### Tag 01GN: restriction along a finite inclusion of simplicial sets -/

section FiniteInclusion

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- **Stacks Project, Tag 01G2**, finite limits clause for `SR(C, X)`, first half. If `C` has
fibre products then `SR(C, X)` has finite limits: it has a terminal object, namely `{X → X}`, and
it has fibre products, computed componentwise.

The second half of the clause, that `F : SR(C, X) ⥤ PSh(C)/h_X` commutes with those finite
limits, is the instance `CategoryTheory.Limits.FormalCoproduct.preservesLimitsOfSize_yonedaOver`
in `StacksFrontier.CategoryTheory.Sites.Localization.SemiRepresentableOver`, for limits of every
shape. -/
@[stacks 01G2 "SR(C, X) has finite limits"]
instance hasFiniteLimits_formalCoproductOver {X : C} :
    HasFiniteLimits (FormalCoproduct.{w} (Over X)) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- A chosen simplicial object representing `Hom(U, K)`, for a finite simplicial set `U`. -/
noncomputable def homFromSSet {X : C} (U : SSet.{max w v}) [U.Finite]
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    SimplicialObject (FormalCoproduct.{w} (Over X)) :=
  Classical.choose (SimplicialObject.exists_representableBy_sHom U K)

/-- The representing datum for the chosen object `homFromSSet U K`. -/
noncomputable def homFromSSetIsHom {X : C} (U : SSet.{max w v}) [U.Finite]
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    SimplicialObject.IsHomFromSSet U K (homFromSSet U K) :=
  Classical.choice (Classical.choose_spec
    (SimplicialObject.exists_representableBy_sHom U K)).1

/-- Restriction `Hom(V, K) ⟶ Hom(U, K)` along a morphism `U ⟶ V` of finite simplicial sets:
the morphism corresponding, under the representing equivalence for `U`, to precomposition of
the universal element for `V` with `U ⟶ V`. -/
noncomputable def homFromSSetRestriction {X : C} {U V : SSet.{max w v}} [U.Finite] [V.Finite]
    (i : U ⟶ V) (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    homFromSSet V K ⟶ homFromSSet U K :=
  (homFromSSetIsHom U K).homEquiv.symm (i ≫ (homFromSSetIsHom V K).homEquiv (𝟙 _))

/-- Restriction of `Hom` objects is the morphism induced by the chosen representing data. -/
theorem homFromSSetRestriction_eq_homFromSSetMap {X : C} {U V : SSet.{max w v}} [U.Finite]
    [V.Finite] (i : U ⟶ V) (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    homFromSSetRestriction i K =
      homFromSSetMap (homFromSSetIsHom V K) (homFromSSetIsHom U K) i :=
  rfl

/-- Restriction along a composite is the composite of the restrictions. -/
theorem homFromSSetRestriction_comp {X : C} {A B E : SSet.{max w v}}
    [A.Finite] [B.Finite] [E.Finite] (f : A ⟶ B) (g : B ⟶ E)
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    homFromSSetRestriction g K ≫ homFromSSetRestriction f K =
      homFromSSetRestriction (f ≫ g) K := by
  apply (homFromSSetIsHom A K).homEquiv.injective
  rw [(homFromSSetIsHom A K).homEquiv_comp]
  let F := (SimplicialCategory.sHomFunctor
      (SimplicialObject (FormalCoproduct.{w} (Over X)))).flip.obj K ⋙ coyoneda.obj (op B)
  have hB := (homFromSSetIsHom B K).homEquiv_comp (homFromSSetRestriction g K) (𝟙 _)
  have hB' : (F.map (homFromSSetRestriction g K).op)
      ((homFromSSetIsHom B K).homEquiv (𝟙 _)) =
      g ≫ (homFromSSetIsHom E K).homEquiv (𝟙 _) := by
    refine hB.symm.trans ?_
    simp [homFromSSetRestriction]
  have hfa : (homFromSSetIsHom A K).homEquiv (homFromSSetRestriction f K) =
      f ≫ (homFromSSetIsHom B K).homEquiv (𝟙 _) := by
    simp [homFromSSetRestriction]
  rw [hfa]
  show f ≫ (F.map (homFromSSetRestriction g K).op
    ((homFromSSetIsHom B K).homEquiv (𝟙 _))) = _
  rw [hB']
  symm
  simp [homFromSSetRestriction]

/-- Restriction along the identity is the identity. -/
theorem homFromSSetRestriction_id {X : C} {A : SSet.{max w v}} [A.Finite]
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    homFromSSetRestriction (𝟙 A) K = 𝟙 (homFromSSet A K) := by
  apply (homFromSSetIsHom A K).homEquiv.injective
  simp [homFromSSetRestriction]

/-- Restriction along an isomorphism of finite simplicial sets is an isomorphism. -/
theorem homFromSSetRestriction_isIso {X : C} {A B : SSet.{max w v}} [A.Finite] [B.Finite]
    (e : A ≅ B) (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    IsIso (homFromSSetRestriction e.hom K) := by
  refine ⟨⟨homFromSSetRestriction e.inv K, ?_, ?_⟩⟩
  · rw [homFromSSetRestriction_comp]
    simpa using homFromSSetRestriction_id K (A := B)
  · rw [homFromSSetRestriction_comp]
    simpa using homFromSSetRestriction_id K (A := A)

/-- A representing datum for `Hom(B, K)` transports along an isomorphism `A ≅ B` to one for
`Hom(A, K)`, with the same representing object. -/
noncomputable def transportHomFromSSet {A B : SSet.{max w v}} (e : A ≅ B) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    {H : SimplicialObject (FormalCoproduct.{w} (Over X))}
    (hB : SimplicialObject.IsHomFromSSet B K H) :
    SimplicialObject.IsHomFromSSet A K H := by
  let G := (SimplicialCategory.sHomFunctor
    (SimplicialObject (FormalCoproduct.{w} (Over X)))).flip.obj K
  have hIso : (G ⋙ coyoneda.obj (op B)) ≅ (G ⋙ coyoneda.obj (op A)) :=
    NatIso.ofComponents (fun Y ↦ (coyoneda.mapIso e.op).app (G.obj Y))
      (fun {Y Y'} f ↦ (coyoneda.mapIso e.op).hom.naturality (G.map f))
  exact Functor.RepresentableBy.ofIso hB hIso

omit [HasPullbacks C] in
/-- The transported representing datum differs from the original by precomposition with the
isomorphism. -/
theorem transportHomFromSSet_homEquiv {A B : SSet.{max w v}} (e : A ≅ B) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    {H H' : SimplicialObject (FormalCoproduct.{w} (Over X))}
    (hB : SimplicialObject.IsHomFromSSet B K H) (g : H' ⟶ H) :
    (transportHomFromSSet e K hB).homEquiv g = e.hom ≫ hB.homEquiv g := by
  simp [transportHomFromSSet, Functor.RepresentableBy.ofIso]

end FiniteInclusion

/-! ### Cell filtrations of inclusions of simplicial sets -/

section Filtration

/-- A subcomplex of bounded dimension is contained in the corresponding skeleton. -/
theorem le_skeleton_of_hasDimensionLT {A : SSet.{uS}} (B : A.Subcomplex) (n : ℕ)
    [SSet.HasDimensionLT B n] : B ≤ A.skeleton n :=
  SSet.le_skeleton_of_hasDimensionLT_aux B n

/-- A subcomplex with no nondegenerate simplices outside it is the whole simplicial set. -/
theorem eq_top_of_isEmpty_N {A : SSet.{uS}} {B : A.Subcomplex} (h : IsEmpty B.N) : B = ⊤ := by
  refine le_antisymm le_top ?_
  rw [SSet.Subcomplex.le_iff_contains_nonDegenerate]
  intro n x _
  by_contra hx
  exact h.elim (SSet.Subcomplex.N.mk x.1 x.2 hx)

/-- Enlarging a subcomplex injects the nondegenerate simplices outside the larger one into
those outside the smaller one. -/
theorem exists_injective_N_of_le {A : SSet.{uS}} {B E : A.Subcomplex} (h : B ≤ E) :
    ∃ f : E.N → B.N, Function.Injective f ∧ ∀ t, (f t).toN = t.toN :=
  ⟨fun t ↦ .mk' t.toN (fun ht ↦ t.notMem (h _ ht)), fun t₁ t₂ e ↦ by
    rw [SSet.Subcomplex.N.ext_iff] at e
    exact (SSet.Subcomplex.N.ext_iff _ _).mpr e, fun _ ↦ rfl⟩

/-
`Stacks.CategoryTheory.Hypercovering.card_lt_of_injective_of_notMem` lived here and was a
duplicate of what is now public as `SSet.Subcomplex.card_lt_of_injective_of_notMem`:
`StacksFrontier/AlgebraicTopology/SimplicialObject/Skeleton.lean:455`, a file this one imports.
-/

/-- **Tag 018S, in the refined form needed for Tag 01GM.** An inclusion of simplicial sets
with finitely many nondegenerate simplices outside the source is a finite sequence of one-cell
attachments, and each attached cell can be taken of minimal dimension, so that the stage it is
attached to already contains the whole skeleton of that dimension. -/
theorem exists_ordered_filtration (k : ℕ) : ∀ {A : SSet.{uS}} (B : A.Subcomplex),
    Finite B.N → Nat.card B.N ≤ k →
    ∃ (r : ℕ) (W : ℕ → A.Subcomplex), Monotone W ∧ W 0 = B ∧ W r = (⊤ : A.Subcomplex) ∧
      ∀ i < r, ∃ (n : ℕ) (x : A _⦋n⦌), x ∉ (W i).obj (op ⦋n⦌) ∧
        SSet.Subcomplex.range (∂Δ[n].ι ≫ SSet.yonedaEquiv.symm x) ≤ W i ∧
        W (i + 1) = W i ⊔ SSet.Subcomplex.ofSimplex x ∧ A.skeleton n ≤ W i := by
  induction k with
  | zero =>
    intro A B hB hk
    have hzero : Nat.card B.N = 0 := by omega
    rw [Nat.card_eq_zero] at hzero
    have hempty : IsEmpty B.N :=
      hzero.resolve_right (fun h ↦ (not_finite_iff_infinite.mpr h) hB)
    exact ⟨0, fun _ ↦ B, monotone_const, rfl, eq_top_of_isEmpty_N hempty,
      fun i hi ↦ absurd hi (by omega)⟩
  | succ k ih =>
    intro A B hB hk
    rcases isEmpty_or_nonempty B.N with hempty | hnonempty
    · exact ih B hB (by simp [Nat.card_of_isEmpty])
    · obtain ⟨s, hs⟩ := Finite.exists_min (fun t : B.N ↦ t.dim)
      have hsk : A.skeleton s.dim ≤ B := by
        rw [SSet.Subcomplex.le_iff_contains_nonDegenerate]
        intro m z hz
        by_contra hzB
        have h₁ : s.dim ≤ m := by simpa using hs (SSet.Subcomplex.N.mk z.1 z.2 hzB)
        rw [A.mem_skeleton_obj_iff_of_nonDegenerate z s.dim] at hz
        omega
      have hbd : SSet.Subcomplex.range
          (∂Δ[s.dim].ι ≫ SSet.yonedaEquiv.symm s.simplex) ≤ B :=
        (le_skeleton_of_hasDimensionLT (SSet.Subcomplex.range
          (∂Δ[s.dim].ι ≫ SSet.yonedaEquiv.symm s.simplex)) s.dim).trans hsk
      obtain ⟨f, hfinj, hftoN⟩ := exists_injective_N_of_le
        (le_sup_left : B ≤ B ⊔ SSet.Subcomplex.ofSimplex s.simplex)
      have hfin : Finite (B ⊔ SSet.Subcomplex.ofSimplex s.simplex : A.Subcomplex).N :=
        Finite.of_injective f hfinj
      have hmem : s.simplex ∈
          (B ⊔ SSet.Subcomplex.ofSimplex s.simplex : A.Subcomplex).obj (op ⦋s.dim⦌) :=
        (le_sup_right : SSet.Subcomplex.ofSimplex s.simplex ≤
          B ⊔ SSet.Subcomplex.ofSimplex s.simplex) _ (SSet.Subcomplex.mem_ofSimplex_obj _)
      have hnotrange : s ∉ Set.range f := by
        rintro ⟨t, ht⟩
        rw [SSet.Subcomplex.N.ext_iff, hftoN t] at ht
        have ht' := t.notMem
        rw [ht] at ht'
        exact ht' hmem
      have hcard : Nat.card (B ⊔ SSet.Subcomplex.ofSimplex s.simplex : A.Subcomplex).N <
          Nat.card B.N :=
        SSet.Subcomplex.card_lt_of_injective_of_notMem f hfinj hnotrange
      obtain ⟨r, W, hmono, hW0, hWr, hstep⟩ :=
        ih (B ⊔ SSet.Subcomplex.ofSimplex s.simplex) hfin (by omega)
      refine ⟨r + 1, Nat.rec (motive := fun _ ↦ A.Subcomplex) B (fun j _ ↦ W j),
        ?_, rfl, hWr, ?_⟩
      · refine monotone_nat_of_le_succ (fun i ↦ ?_)
        cases i with
        | zero => exact le_sup_left.trans hW0.ge
        | succ j => exact hmono.imp (Nat.le_succ j)
      · intro i hi
        cases i with
        | zero => exact ⟨s.dim, s.simplex, s.notMem, hbd, hW0, hsk⟩
        | succ j => exact hstep j (by omega)

/-- The image of a simplex under an operator whose image is smaller than its source is
degenerate. -/
private theorem degenerate_map_of_image_len_lt {A : SSet.{uS}} {n m : ℕ} (x : A _⦋n⦌)
    (f : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (h : (image f).len < m) :
    A.map f.op x ∈ A.degenerate m := by
  rw [SSet.mem_degenerate_iff]
  refine ⟨(image f).len, h, factorThruImage f, inferInstance, ⟨A.map (image.ι f).op x, ?_⟩⟩
  rw [← Functor.map_comp_apply, ← op_comp, image.fac]

/-- The image of a simplex under an operator raising the dimension is degenerate. -/
theorem degenerate_map_of_simplex_of_dim_lt {A : SSet.{uS}} {n m : ℕ} (x : A _⦋n⦌)
    (f : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (hm : n < m) : A.map f.op x ∈ A.degenerate m := by
  have h : (image f).len ≤ n := by simpa using SimplexCategory.len_le_of_mono (image.ι f)
  exact degenerate_map_of_image_len_lt x f (by omega)

/-- The image of a simplex under a non-surjective operator of the same dimension is
degenerate. -/
theorem degenerate_map_of_simplex_of_not_epi {A : SSet.{uS}} {n : ℕ} (x : A _⦋n⦌)
    (f : (⦋n⦌ : SimplexCategory) ⟶ ⦋n⦌) (hf : ¬ Epi f) : A.map f.op x ∈ A.degenerate n := by
  have hle : (image f).len ≤ n := SimplexCategory.len_le_of_mono (image.ι f)
  have hne : (image f).len ≠ n := by
    intro h
    have hi : IsIso (image.ι f) := (SimplexCategory.isIso_iff_of_mono (image.ι f)).2 h
    have hep : Epi f := by
      have hfac : factorThruImage f ≫ image.ι f = f := image.fac f
      exact hfac ▸ (inferInstance : Epi (factorThruImage f ≫ image.ι f))
    exact hf hep
  exact degenerate_map_of_image_len_lt x f (by omega)

/-- A degenerate simplex of degree `n` lies in the `n`-skeleton. -/
theorem mem_skeleton_of_degenerate {A : SSet.{uS}} {n : ℕ} {x : A _⦋n⦌}
    (hx : x ∈ SSet.degenerate A n) : x ∈ (SSet.skeleton A n).obj (op ⦋n⦌) := by
  rw [SSet.mem_degenerate_iff] at hx
  obtain ⟨m, hm, f, hf, y, hy⟩ := hx
  simpa [hy] using (SSet.skeleton A n).map f.op (A.mem_skeleton y (n := n) hm)

end Filtration

section FiniteInclusion

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- Restriction along a one-cell attachment of subcomplexes of a finite simplicial set is a
covering: this is Tag 01GM applied to the attachment. -/
theorem isCoveringOver_homFromSSetRestriction_app_zero_of_oneCell (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (hK : IsHypercovering J K)
    {V : SSet.{max w v}} [V.Finite] {A B : V.Subcomplex} [SSet.Nonempty (A : SSet)]
    (hAB : A ≤ B) (n : ℕ) (x : V _⦋n⦌) (hx : x ∉ A.obj (op ⦋n⦌))
    (hadd : B = A ⊔ SSet.Subcomplex.ofSimplex x) (hlt : V.skeleton n ≤ A) :
    IsCoveringOver J
      ((homFromSSetRestriction (SSet.Subcomplex.homOfLE hAB) K).app (op ⦋0⦌)) := by
  classical
  let f : (A : SSet) ⟶ (B : SSet) := SSet.Subcomplex.homOfLE hAB
  have _ : Mono f := SSet.Subcomplex.mono_homOfLE hAB
  let E : (B : SSet).Subcomplex := SSet.Subcomplex.range f
  let e : (A : SSet) ≅ (E : SSet) := asIso (SSet.Subcomplex.toRange f)
  have _ : SSet.Nonempty (B : SSet) := SSet.nonempty_of_hom f
  have _ : SSet.Nonempty (E : SSet) :=
    ⟨e.hom.app (op ⦋0⦌) (Classical.choice ‹SSet.Nonempty (A : SSet)›)⟩
  let hA := homFromSSetIsHom (A : SSet) K
  let hB := homFromSSetIsHom (B : SSet) K
  let hE : SimplicialObject.IsHomFromSSet (E : SSet) K (homFromSSet (A : SSet) K) :=
    transportHomFromSSet e.symm K hA
  have memRange (m : ℕ) (y : (B : SSet) _⦋m⦌) (hyA : y.val ∈ A.obj (op ⦋m⦌)) :
      y ∈ Set.range (E.ι.app (op ⦋m⦌)) := by
    refine ⟨⟨y, ⟨⟨y.val, hyA⟩, ?_⟩⟩, rfl⟩
    show (SSet.Subcomplex.homOfLE hAB).app (op ⦋m⦌) ⟨y.val, hyA⟩ = y
    exact Subtype.ext rfl
  have hsplit (m : ℕ) (y : (B : SSet) _⦋m⦌) : y.val ∈ A.obj (op ⦋m⦌) ∨
      ∃ g : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌, V.map g.op x = y.val := by
    have hyB : y.val ∈ (A ⊔ SSet.Subcomplex.ofSimplex x).obj (op ⦋m⦌) := hadd ▸ y.property
    exact hyB.imp id ((SSet.Subcomplex.mem_ofSimplex_obj_iff x y.val).mp)
  have hbelow : ∀ m < n, Function.Bijective (E.ι.app (op ⦋m⦌)) := by
    intro m hm
    refine ⟨injective_of_mono (E.ι.app (op ⦋m⦌)), fun y ↦ memRange m y ?_⟩
    rcases hsplit m y with hyA | ⟨g, hg⟩
    · exact hyA
    · exact hlt _ (hg ▸ V.mem_skeleton _ hm)
  have hxB : x ∈ B.obj (op ⦋n⦌) := by
    rw [hadd]
    exact Or.inr (SSet.Subcomplex.mem_ofSimplex_obj x)
  let xB : (B : SSet) _⦋n⦌ := ⟨x, hxB⟩
  have hxE : xB ∉ Set.range (E.ι.app (op ⦋n⦌)) := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha⟩ := y.property
    have hy' : y.val = xB := by simpa using hy
    have hfval : (f.app (op ⦋n⦌) a).val = a.val := rfl
    have hv := congrArg (fun z : (B : SSet) _⦋n⦌ ↦ z.val) (ha.trans hy')
    have hax : a.val = x := hfval.symm.trans (by simpa [xB] using hv)
    exact hx (hax ▸ a.property)
  have hat : ∀ y : (B : SSet) _⦋n⦌, y ∈ Set.range (E.ι.app (op ⦋n⦌)) ∨ y = xB := by
    intro y
    rcases hsplit n y with hyA | ⟨g, hg⟩
    · exact Or.inl (memRange n y hyA)
    · by_cases hgepi : Epi g
      · refine Or.inr (Subtype.ext ?_)
        simpa [SimplexCategory.eq_id_of_epi g] using hg.symm
      · refine Or.inl (memRange n y (hlt _ ?_))
        simpa [hg] using mem_skeleton_of_degenerate
          (degenerate_map_of_simplex_of_not_epi x g hgepi)
  have habove : ∀ m, n < m → ∀ y : (B : SSet) _⦋m⦌,
      y ∉ Set.range (E.ι.app (op ⦋m⦌)) → y ∈ (B : SSet).degenerate m := by
    intro m hm y hy
    rcases hsplit m y with hyA | ⟨g, hg⟩
    · exact absurd (memRange m y hyA) hy
    · exact (SSet.Subcomplex.mem_degenerate_iff B y).2
        (by simpa [hg] using degenerate_map_of_simplex_of_dim_lt x g hm)
  have hmap : homFromSSetMap hB hE E.ι = homFromSSetRestriction f K := by
    apply hE.homEquiv.injective
    rw [homFromSSetMap, Equiv.apply_symm_apply, transportHomFromSSet_homEquiv,
      homFromSSetRestriction, Equiv.apply_symm_apply]
    have hRange : e.symm.hom ≫ f = E.ι := by
      rw [show f = SSet.Subcomplex.toRange f ≫ E.ι from (SSet.Subcomplex.toRange_ι f).symm]
      simp [e]
    rw [← hRange, Category.assoc]
  rw [← hmap]
  exact isCoveringOver_homFromSSetMap_app_zero_of_oneMoreSimplex J K hK (B : SSet) E
    (fun m ↦ ⟨e.hom.app (op ⦋m⦌)
      (Classical.choice (inferInstance : Nonempty ((A : SSet).obj (op ⦋m⦌))))⟩)
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
    n xB hxE hbelow hat habove _ _ hB hE

/-- The isomorphism identifying a subcomplex equal to `⊤` with the ambient simplicial set has
the inclusion of that subcomplex as its underlying morphism. -/
theorem topSubcomplexIso_hom {V : SSet.{uS}} {A : V.Subcomplex} (h : A = ⊤) :
    (eqToIso (congrArg (fun T : V.Subcomplex ↦ (T : SSet.{uS})) h) ≪≫
      SSet.Subcomplex.topIso V).hom = A.ι := by
  cases h
  simp [SSet.Subcomplex.topIso_hom]

/-- Restriction along a finite chain of inclusions is a covering as soon as each step is. -/
theorem isCoveringOver_homFromSSetRestriction_app_zero_of_chain (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    {V : SSet.{max w v}} [V.Finite] (W : ℕ → V.Subcomplex) (hmono : Monotone W) :
    ∀ r : ℕ, (∀ i < r, IsCoveringOver J
        ((homFromSSetRestriction
          (SSet.Subcomplex.homOfLE (hmono (Nat.le_succ i))) K).app (op ⦋0⦌))) →
      IsCoveringOver J
        ((homFromSSetRestriction
          (SSet.Subcomplex.homOfLE (hmono (Nat.zero_le r))) K).app (op ⦋0⦌)) := by
  intro r
  induction r with
  | zero =>
    intro _
    rw [SSet.Subcomplex.homOfLE_refl, homFromSSetRestriction_id]
    exact IsCoveringOver.of_isIso J _
  | succ r ih =>
    intro hsteps
    let a : (W 0 : SSet) ⟶ (W r : SSet) := SSet.Subcomplex.homOfLE (hmono (Nat.zero_le r))
    let b : (W r : SSet) ⟶ (W (r + 1) : SSet) :=
      SSet.Subcomplex.homOfLE (hmono (Nat.le_succ r))
    have hfac : (homFromSSetRestriction
        (SSet.Subcomplex.homOfLE (hmono (Nat.zero_le (r + 1)))) K).app (op ⦋0⦌) =
        (homFromSSetRestriction b K).app (op ⦋0⦌) ≫
          (homFromSSetRestriction a K).app (op ⦋0⦌) :=
      (congrArg (fun t ↦ t.app (op ⦋0⦌)) (homFromSSetRestriction_comp a b K)).symm
    rw [hfac]
    exact IsCoveringOver.comp J (hsteps r (by omega)) (ih fun i hi ↦ hsteps i (by omega))

/-- **Stacks Project, Tag 01GN.** Let `K` be a hypercovering of `X` and let `U ⊆ V` be finite
nonempty simplicial sets. Then restriction `Hom(V, K)₀ ⟶ Hom(U, K)₀` is a covering morphism in
`SR(C, X)`. -/
@[stacks 01GN]
theorem isCoveringOver_homFromSSetRestriction_app_zero (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage] (X : C)
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (hK : IsHypercovering J K)
    (V : SSet.{max w v}) [V.Finite] [V.Nonempty]
    (U : V.Subcomplex) [SSet.Finite (U : SSet)] [SSet.Nonempty (U : SSet)] :
    IsCoveringOver J ((homFromSSetRestriction U.ι K).app (op ⦋0⦌)) := by
  classical
  have hUN : Finite (U : V.Subcomplex).N :=
    Finite.of_injective (fun t : (U : V.Subcomplex).N ↦ t.toN) fun a b hab ↦
      (SSet.Subcomplex.N.ext_iff _ _).2 hab
  obtain ⟨r, W, hmono, hW0, hWr, hstep⟩ :=
    exists_ordered_filtration (Nat.card (U : V.Subcomplex).N) (U : V.Subcomplex) hUN le_rfl
  have hW0nonempty : SSet.Nonempty (W 0 : SSet) :=
    hW0.symm ▸ (inferInstance : SSet.Nonempty (U : SSet))
  have hsteps : ∀ i < r, IsCoveringOver J
      ((homFromSSetRestriction
        (SSet.Subcomplex.homOfLE (hmono (Nat.le_succ i))) K).app (op ⦋0⦌)) := by
    intro i hi
    obtain ⟨n, x, hx, _, hadd, hlt⟩ := hstep i hi
    have _ : SSet.Nonempty (W i : SSet) :=
      SSet.nonempty_of_hom (SSet.Subcomplex.homOfLE (hmono (Nat.zero_le i)))
    exact isCoveringOver_homFromSSetRestriction_app_zero_of_oneCell J K hK
      (A := W i) (B := W (i + 1)) (hmono (Nat.le_succ i)) n x hx hadd hlt
  have hchain := isCoveringOver_homFromSSetRestriction_app_zero_of_chain J K W hmono r hsteps
  let e : (W r : SSet.{max w v}) ≅ (V : SSet.{max w v}) :=
    eqToIso (congrArg (fun A : V.Subcomplex ↦ (A : SSet.{max w v})) hWr) ≪≫
      SSet.Subcomplex.topIso (V : SSet.{max w v})
  have _ : IsIso (homFromSSetRestriction e.hom K) := homFromSSetRestriction_isIso e K
  cases hW0
  have hfactor : SSet.Subcomplex.homOfLE (hmono (Nat.zero_le r)) ≫ e.hom = (W 0).ι := by
    rw [topSubcomplexIso_hom hWr]
    exact SSet.Subcomplex.homOfLE_ι _
  have hrestr : homFromSSetRestriction e.hom K ≫
      homFromSSetRestriction (SSet.Subcomplex.homOfLE (hmono (Nat.zero_le r))) K =
        homFromSSetRestriction (W 0).ι K := by
    rw [← hfactor, homFromSSetRestriction_comp
      (f := SSet.Subcomplex.homOfLE (hmono (Nat.zero_le r))) (g := e.hom)]
  rw [← congrArg (fun t ↦ t.app (op ⦋0⦌)) hrestr]
  exact IsCoveringOver.comp J (IsCoveringOver.of_isIso J _) hchain

end FiniteInclusion

end Stacks.CategoryTheory.Hypercovering

end
