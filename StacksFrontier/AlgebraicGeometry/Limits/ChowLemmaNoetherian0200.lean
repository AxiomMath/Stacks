module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.DenseAffineCover
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Gluing
public import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.Dominant
public import StacksFrontier.AlgebraicGeometry.Limits.AffineIntoProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints

/-!
# Chow's lemma over a Noetherian base

**Stacks 0200** is Chow's lemma over a Noetherian base: a separated morphism `f : X ⟶ S` of
finite type with `S` Noetherian admits a proper surjective `π : X' ⟶ X` together with an
immersion `X' ⟶ ℙⁿ_S` over `S`, and `π` may be taken to be an isomorphism over a dense open of
`X`. It is the geometric heart of Chow's lemma: the general case, Stacks 0202, is this result
combined with absolute Noetherian approximation.

This file carries out the whole of the Stacks proof of 0200 from **two** geometric inputs, each
named as an explicit hypothesis:

* `AlgebraicGeometry.HasAffineProjectiveImmersions S` -- every affine scheme locally of finite
  type over `S` admits an immersion into some projective space over `S`. Over a general base
  this is Stacks 01QE together with Stacks 01VS (Serre's embedding theorem), neither of which
  is available. Over an **affine** base it is proved here, in
  `AlgebraicGeometry.hasAffineProjectiveImmersions_of_isAffine`, from the affine-space
  factorization `AlgebraicGeometry.exists_isClosedImmersion_affineSpace` and the standard
  affine chart `AlgebraicGeometry.ProjectiveSpace.affineChart`.
* `AlgebraicGeometry.HasSegreEmbeddings S` -- the fibre product over `S` of two projective
  spaces over `S` closed-immerses into a projective space over `S`. This is Stacks 01WD, the
  Segre embedding, which is not available.

Neither hypothesis mentions a modification, properness or surjectivity, and neither says
anything about a non-affine source, so neither is a restatement of the conclusion; see the
implementation notes.

## Main definitions

* `AlgebraicGeometry.ChowModification` is the conclusion of Stacks 0200 for a morphism: a
  proper surjective modification immersed in a projective space over the base, together with
  the dense open over which it is an isomorphism.
* `AlgebraicGeometry.HasAffineProjectiveImmersions` and
  `AlgebraicGeometry.HasSegreEmbeddings` are the two inputs described above.

## Main results

* `AlgebraicGeometry.hasAffineProjectiveImmersions_of_isAffine`: the first input holds over an
  affine base.
* `AlgebraicGeometry.nonempty_chowModification`: **Stacks 0200**, granted the two inputs.
* `AlgebraicGeometry.nonempty_chowModification_of_isAffine_base`: Stacks 0200 over an affine
  Noetherian base, granted the Segre embedding and nothing else.
* `AlgebraicGeometry.hasChowModification_of_hasSegreEmbeddings`: the same, stated with the
  development's `AlgebraicGeometry.HasChowModification`.

Three results proved along the way are independent of Chow's lemma and stated for general
schemes:

* `AlgebraicGeometry.isSchemeTheoreticallyDominant_of_comp_isOpenImmersion`: scheme-theoretic
  dominance descends through an open immersion.
* `AlgebraicGeometry.isIso_pullbackLift_of_isProper_of_dense`: a proper morphism that is an
  isomorphism over a dense open of an open subscheme is one over the whole of it.
* `AlgebraicGeometry.surjective_of_isProper_of_dense`: a proper morphism dominating a dense open
  is surjective.

## Implementation notes

Projective space is `AlgebraicGeometry.ProjectiveSpace`, the model
`AlgebraicGeometry.HasChowModification` is written with, and its structure morphism is `↘ S`.
That morphism is `pullback.fst (terminal.from S) (terminal.from (ProjectiveSpaceZ n))` by
`AlgebraicGeometry.ProjectiveSpace.over_hom`, which is how the conclusion here matches the
phrasing of Stacks 0200 in terms of `AlgebraicGeometry.projectiveSpaceOver`; see
`AlgebraicGeometry.hasChowModification_iff_projectiveSpaceOver`.

Both inputs are stated over a **fixed** base `S`, which is all the proof uses and is what
allows `AlgebraicGeometry.HasAffineProjectiveImmersions` to be discharged for an affine base.
`AlgebraicGeometry.HasSegreEmbeddings` asks only for the *existence* of a projective space
receiving the product, not for the dimension `n * m + n + m` that Stacks 01WD produces; that is
weaker than 01WD, hence makes the theorems below stronger.

Why neither hypothesis is a restatement of the conclusion. `HasSegreEmbeddings S` mentions no
scheme other than projective spaces over `S`, so it cannot specialize to the conclusion for any
`X` at all. `HasAffineProjectiveImmersions S` quantifies only over affine sources, and for an
affine source the conclusion of 0200 is *already* available from it with no further work --
which is exactly what the degenerate branch of the proof does -- whereas the content of 0200 is
the non-affine case, obtained here only through the scheme-theoretic closure of the common open
inside a product of projective spaces. A separating instance: `X = ℙ¹_S ⟶ S` lies in the class
0200 speaks about, and `HasAffineProjectiveImmersions S` says nothing whatever about it.

`MorphismProperty.IsStableUnderComposition @IsClosedImmersion` and
`MorphismProperty.ContainsIdentities @IsClosedImmersion` are *not* found by instance search on
this Mathlib pin, although `MorphismProperty.IsMultiplicative @IsClosedImmersion`, of which they
are the two projections, is an instance. The first is therefore supplied as the explicit term
`MorphismProperty.IsMultiplicative.toIsStableUnderComposition`; the second is sidestepped by
writing the identity morphism at the target's own spelling, since `IsClosedImmersion (𝟙 _)` is
otherwise sought at a source type that is only definitionally the target.

The finite relative product of projective spaces is built by recursion on a `List` of factors
rather than as a limit over a `Finset`, so that the Segre embedding can be applied one factor at
a time and the recursion's base case is a single projective space. The empty list is sent to `S`
itself, which keeps the recursion total; the lemmas about it all carry `l ≠ []`.

## References

* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 01ZX](https://stacks.math.columbia.edu/tag/01ZX)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The conclusion of **Chow's lemma over a Noetherian base** (Stacks 0200) for a morphism
`f : X ⟶ S`: a proper surjective morphism `toX : scheme ⟶ X` and an immersion of `scheme` into
a projective space over `S` making the triangle over `S` commute, together with a dense open of
`X` over which `toX` is an isomorphism. -/
structure ChowModification {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The dimension of the projective space the modification immerses into. -/
  n : ℕ
  /-- The underlying scheme of the modification. -/
  scheme : Scheme.{u}
  /-- The modification itself, a proper surjection onto `X`. -/
  toX : scheme ⟶ X
  /-- The immersion of the modification into a projective space over `S`. -/
  toProjectiveSpace : scheme ⟶ ProjectiveSpace n S
  /-- The dense open of `X` over which the modification is an isomorphism. -/
  denseOpen : X.Opens
  /-- The morphism `toX` is proper. -/
  isProper : IsProper toX
  /-- The morphism `toX` is surjective. -/
  surjective : Surjective toX
  /-- The morphism `toProjectiveSpace` is an immersion. -/
  isImmersion : IsImmersion toProjectiveSpace
  /-- The maps of `scheme` to `S` through `X` and through the projective space agree. -/
  commutes : toX ≫ f = toProjectiveSpace ≫ (ProjectiveSpace n S ↘ S)
  /-- The open `denseOpen` is dense in `X`. -/
  dense : Dense (denseOpen : Set X)
  /-- The restriction of `toX` over `denseOpen` is an isomorphism. -/
  isIso_restrict : IsIso (toX ∣_ denseOpen)

/-- **The first input of Chow's lemma over a Noetherian base**: every affine scheme locally of
finite type over `S` admits an immersion into some projective space over `S`, compatibly with
the maps to `S`.

Over a general base this is Stacks 01QE (an affine, hence quasi-affine, scheme has ample
structure sheaf) together with Stacks 01VS (a sufficiently high power of an ample invertible
sheaf embeds the scheme in a projective space over the base). Over an affine base it is proved
below as `AlgebraicGeometry.hasAffineProjectiveImmersions_of_isAffine`. -/
def HasAffineProjectiveImmersions (S : Scheme.{u}) : Prop :=
  ∀ (Y : Scheme.{u}) (g : Y ⟶ S), IsAffine Y → LocallyOfFiniteType g →
    ∃ (n : ℕ) (i : Y ⟶ ProjectiveSpace n S),
      IsImmersion i ∧ i ≫ (ProjectiveSpace n S ↘ S) = g

/-- **The second input of Chow's lemma over a Noetherian base**: the fibre product over `S` of
two projective spaces over `S` admits a closed immersion over `S` into a projective space over
`S`. This is Stacks 01WD, the Segre embedding, except that only the existence of a receiving
projective space is asked for, not that its dimension is `n * m + n + m`. -/
def HasSegreEmbeddings (S : Scheme.{u}) : Prop :=
  ∀ n m : ℕ, ∃ (N : ℕ) (e : pullback (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ⟶
      ProjectiveSpace N S), IsClosedImmersion e ∧
    e ≫ (ProjectiveSpace N S ↘ S) =
      pullback.fst (ProjectiveSpace n S ↘ S) (ProjectiveSpace m S ↘ S) ≫
        (ProjectiveSpace n S ↘ S)

/-- **The first input holds over an affine base.** An affine scheme locally of finite type over
an affine base factors as a closed immersion into an affine space over the base followed by the
structure morphism, and the standard affine chart realizes that affine space as an open
subscheme of a projective space over the base; a closed immersion followed by an open immersion
is an immersion.

This is the affine case of Stacks 01VS, proved without any ampleness: the morphism to
projective space is built from a finite algebra generating family rather than from sections of
an invertible sheaf. -/
theorem hasAffineProjectiveImmersions_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    HasAffineProjectiveImmersions S := by
  intro Y g hY hg
  have : IsAffine Y := hY
  have : LocallyOfFiniteType g := hg
  obtain ⟨m, i, hi, hcomm⟩ := exists_isClosedImmersion_affineSpace g
  have : IsClosedImmersion i := hi
  refine ⟨m, i ≫ ProjectiveSpace.affineChart m S, inferInstance, ?_⟩
  rw [Category.assoc, ProjectiveSpace.affineChart_over]
  exact hcomm

/-- **A proper morphism whose image contains a dense open is surjective.** If `π` is proper and
some section over a dense open `U` of the target factors `U.ι` through `π`, then `π` is
dominant, and a dominant proper morphism is surjective because its image is closed. -/
theorem surjective_of_isProper_of_dense {X Y : Scheme.{u}} (π : Y ⟶ X) [IsProper π]
    (U : X.Opens) (s : U.toScheme ⟶ Y) (hs : s ≫ π = U.ι) (hU : Dense (U : Set X)) :
    Surjective π := by
  have hdom : IsDominant (s ≫ π) := by
    rw [hs]
    exact Opens.isDominant_ι hU
  have : IsDominant π := IsDominant.of_comp s π
  infer_instance

/-- **Scheme-theoretic dominance descends through an open immersion.** If `a ≫ b` is
scheme-theoretically dominant and quasi-compact with `b` an open immersion, then `a` is
scheme-theoretically dominant: `a` is the base change of `a ≫ b` along `b`. -/
theorem isSchemeTheoreticallyDominant_of_comp_isOpenImmersion {U V Z : Scheme.{u}} (a : U ⟶ V)
    (b : V ⟶ Z) [IsOpenImmersion b] [QuasiCompact (a ≫ b)]
    [IsSchemeTheoreticallyDominant (a ≫ b)] : IsSchemeTheoreticallyDominant a := by
  have H : Set.range (a ≫ b) ⊆ Set.range b := by
    rintro _ ⟨x, rfl⟩
    exact ⟨a x, rfl⟩
  have ht : IsOpenImmersion.lift b (a ≫ b) H = a := (cancel_mono b).mp (by simp)
  have hp := (IsOpenImmersion.isPullback_lift_id (a ≫ b) b H).flip
  rw [ht] at hp
  exact IsSchemeTheoreticallyDominant.of_isPullback hp

/-- **A proper morphism that is an isomorphism over a dense open of an open subscheme is an
isomorphism over the whole of that open subscheme.** Concretely: if `a : V ⟶ Y` is a dominant
open immersion, `b : V ⟶ U` is proper, `i : U ⟶ X` is an open immersion, `p : Y ⟶ X` is
separated and `a ≫ p = b ≫ i`, then the induced morphism `V ⟶ Y ×_X U` is an isomorphism. It is
an open immersion and proper, hence a surjective open immersion, hence an isomorphism. -/
theorem isIso_pullbackLift_of_isProper_of_dense {V Y U X : Scheme.{u}} (a : V ⟶ Y) (b : V ⟶ U)
    (i : U ⟶ X) (p : Y ⟶ X) [IsOpenImmersion a] [IsDominant a] [IsOpenImmersion i]
    [IsProper b] [IsSeparated p] (h : a ≫ p = b ≫ i) : IsIso (pullback.lift a b h) := by
  set t := pullback.lift a b h with htdef
  have ht : t ≫ pullback.fst p i = a := pullback.lift_fst _ _ _
  have : IsOpenImmersion (t ≫ pullback.fst p i) := ht ▸ inferInstance
  have : IsOpenImmersion t := IsOpenImmersion.of_comp t (pullback.fst p i)
  have : IsProper (t ≫ pullback.snd p i) := by
    rw [htdef, pullback.lift_snd]
    infer_instance
  have : IsProper t := IsProper.of_comp t (pullback.snd p i)
  have : IsDominant t := by
    constructor
    rw [denseRange_iff_closure_range,
      (pullback.fst p i).isEmbedding.closure_eq_preimage_closure_image]
    have he : pullback.fst p i '' Set.range t = Set.range a := by
      rw [← Set.range_comp]
      change Set.range (t ≫ pullback.fst p i) = Set.range a
      rw [ht]
    rw [he, a.denseRange.closure_range, Set.preimage_univ]
  have : Surjective t := inferInstance
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  ext x
  simp

/-- One of the projective factors of the product used in the proof of Stacks 0200: an immersion
of `X` into a projective space over `S`, over `S`. -/
structure ProjectiveFactor {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The dimension of the projective space. -/
  n : ℕ
  /-- The immersion into it. -/
  map : X ⟶ ProjectiveSpace n S
  isImmersion : IsImmersion map
  commutes : map ≫ (ProjectiveSpace n S ↘ S) = f

/-- A scheme over `S`, used as the value of the recursion building the finite fibre product of a
list of projective spaces over `S`. -/
structure RelativeProjectiveProductData (S : Scheme.{u}) where
  /-- The product scheme. -/
  space : Scheme.{u}
  /-- Its structure morphism to the base. -/
  toBase : space ⟶ S

/-- The finite fibre product over `S` of the projective spaces of a list of factors, built by
recursion. The empty list is sent to `S` itself, which keeps the recursion total; every lemma
below about the product carries `l ≠ []`. -/
noncomputable def relativeProjectiveProductData {X S : Scheme.{u}} (f : X ⟶ S) :
    List (ProjectiveFactor f) → RelativeProjectiveProductData S
  | [] => ⟨S, 𝟙 S⟩
  | [a] => ⟨ProjectiveSpace a.n S, ProjectiveSpace a.n S ↘ S⟩
  | a :: b :: rest =>
      let d := relativeProjectiveProductData f (b :: rest)
      let p := ProjectiveSpace a.n S ↘ S
      ⟨pullback p d.toBase, pullback.fst p d.toBase ≫ p⟩

/-- The finite fibre product over `S` of a list of projective spaces over `S`. -/
noncomputable abbrev relativeProjectiveProduct {X S : Scheme.{u}} {f : X ⟶ S}
    (l : List (ProjectiveFactor f)) : Scheme.{u} :=
  (relativeProjectiveProductData f l).space

/-- The structure morphism of the finite fibre product to its base. -/
noncomputable abbrev relativeProjectiveProductBase {X S : Scheme.{u}} {f : X ⟶ S}
    (l : List (ProjectiveFactor f)) : relativeProjectiveProduct l ⟶ S :=
  (relativeProjectiveProductData f l).toBase

/-- **The diagonal morphism into the finite fibre product**, together with the fact that it is a
morphism over `S`. Its components are the immersions carried by the factors. -/
noncomputable def relativeProjectiveProductMap {X S : Scheme.{u}} (f : X ⟶ S) :
    (l : List (ProjectiveFactor f)) →
      {g : X ⟶ relativeProjectiveProduct (f := f) l //
        g ≫ relativeProjectiveProductBase (f := f) l = f}
  | [] => ⟨f, Category.comp_id _⟩
  | [a] => ⟨a.map, a.commutes⟩
  | a :: b :: rest =>
      let t := relativeProjectiveProductMap f (b :: rest)
      let p := ProjectiveSpace a.n S ↘ S
      let q := relativeProjectiveProductBase (f := f) (b :: rest)
      have hcond : a.map ≫ p = t.1 ≫ q := a.commutes.trans t.2.symm
      ⟨pullback.lift a.map t.1 hcond, by
        calc pullback.lift a.map t.1 hcond ≫ pullback.fst p q ≫ p = a.map ≫ p := by
              simpa only [Category.assoc] using
                congrArg (fun k => k ≫ p) (pullback.lift_fst a.map t.1 hcond)
          _ = f := a.commutes⟩

/-- **One step of the Segre induction, at abstract data.** If `i : Z ⟶ ℙᵐ_S` is a closed
immersion over `S`, then `ℙⁿ_S ×_S Z` closed-immerses over `S` into a projective space over `S`:
base change `i` to get `ℙⁿ_S ×_S Z ⟶ ℙⁿ_S ×_S ℙᵐ_S` and compose with Segre.

The statement keeps `Z`, `q` and `i` as variables. Instantiating it at the recursively built
product is then a single term application, which is checked at default transparency; writing the
same argument out at the product itself does not elaborate, because
`AlgebraicGeometry.relativeProjectiveProduct` of a two-or-more-element list is only
definitionally, not reducibly, a `pullback`. -/
theorem exists_isClosedImmersion_pullback_projectiveSpace {S : Scheme.{u}}
    (hsegre : HasSegreEmbeddings S) (n m : ℕ) {Z : Scheme.{u}} (q : Z ⟶ S)
    (i : Z ⟶ ProjectiveSpace m S) (hi : IsClosedImmersion i)
    (hcomm : i ≫ (ProjectiveSpace m S ↘ S) = q) :
    ∃ (N : ℕ) (j : pullback (ProjectiveSpace n S ↘ S) q ⟶ ProjectiveSpace N S),
      IsClosedImmersion j ∧ j ≫ (ProjectiveSpace N S ↘ S) =
        pullback.fst (ProjectiveSpace n S ↘ S) q ≫ (ProjectiveSpace n S ↘ S) := by
  have hcomp : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    (inferInstance :
      MorphismProperty.IsMultiplicative @IsClosedImmersion).toIsStableUnderComposition
  obtain ⟨N, e, he, hbase⟩ := hsegre n m
  refine ⟨N, pullback.map (ProjectiveSpace n S ↘ S) q (ProjectiveSpace n S ↘ S)
    (ProjectiveSpace m S ↘ S) (𝟙 _) i (𝟙 _) (by simp) (by simp [hcomm]) ≫ e, ?_, ?_⟩
  · exact hcomp.comp_mem _ _
      (MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance hi rfl hcomm.symm) he
  · rw [Category.assoc, hbase, ← Category.assoc, pullback.lift_fst, Category.comp_id]

/-- **The finite fibre product of projective spaces closed-immerses into a single projective
space**, granted the Segre embedding. The induction peels off one factor at a time: the product
of the remaining factors is already closed-immersed in a projective space, so the whole product
is closed-immersed in a product of two projective spaces, and Segre finishes. -/
theorem exists_isClosedImmersion_relativeProjectiveProduct {X S : Scheme.{u}} {f : X ⟶ S}
    (hsegre : HasSegreEmbeddings S) (l : List (ProjectiveFactor f)) (hne : l ≠ []) :
    ∃ (n : ℕ) (i : relativeProjectiveProduct l ⟶ ProjectiveSpace n S),
      IsClosedImmersion i ∧
        i ≫ (ProjectiveSpace n S ↘ S) = relativeProjectiveProductBase l := by
  induction l with
  | nil => simp at hne
  | cons a rest ih =>
      cases rest with
      | nil =>
          exact ⟨a.n, 𝟙 (ProjectiveSpace a.n S),
            (inferInstance : IsClosedImmersion (𝟙 (ProjectiveSpace a.n S))),
            Category.id_comp _⟩
      | cons b tail =>
          obtain ⟨m, i, hi, hcomm⟩ := ih (by simp)
          exact exists_isClosedImmersion_pullback_projectiveSpace hsegre a.n m
            (relativeProjectiveProductBase (f := f) (b :: tail)) i hi hcomm

/-- **The diagonal morphism into a nonempty finite fibre product of projective spaces is an
immersion**, because its first component already is and immersions descend along a
precomposition whose composite is an immersion. -/
theorem isImmersion_relativeProjectiveProductMap {X S : Scheme.{u}} (f : X ⟶ S)
    (l : List (ProjectiveFactor f)) (hne : l ≠ []) :
    IsImmersion (relativeProjectiveProductMap f l).1 := by
  cases l with
  | nil => simp at hne
  | cons a rest =>
      cases rest with
      | nil => exact a.isImmersion
      | cons b tail =>
          set t := relativeProjectiveProductMap f (b :: tail) with htdef
          set p := ProjectiveSpace a.n S ↘ S with hp
          set q := relativeProjectiveProductBase (f := f) (b :: tail) with hq
          have hfst : (relativeProjectiveProductMap f (a :: b :: tail)).1 ≫
              pullback.fst p q = a.map := pullback.lift_fst _ _ _
          set g := (relativeProjectiveProductMap f (a :: b :: tail)).1 with hg
          have : IsImmersion (g ≫ pullback.fst p q) := by
            rw [hg, hfst]
            exact a.isImmersion
          exact IsImmersion.of_comp g (pullback.fst p q)

/-- **Each factor of a finite fibre product of projective spaces is a quotient of it**, by a
projection over `S` through which the diagonal morphism recovers that factor's immersion. -/
theorem exists_relativeProjectiveProductProjection {X S : Scheme.{u}} (f : X ⟶ S)
    (l : List (ProjectiveFactor f)) (b : ProjectiveFactor f) (hb : b ∈ l) :
    ∃ r : relativeProjectiveProduct l ⟶ ProjectiveSpace b.n S,
      r ≫ (ProjectiveSpace b.n S ↘ S) = relativeProjectiveProductBase l ∧
        (relativeProjectiveProductMap f l).1 ≫ r = b.map := by
  induction l with
  | nil => simp at hb
  | cons a rest ih =>
      cases rest with
      | nil =>
          obtain rfl : b = a := by simpa using hb
          exact ⟨𝟙 _, Category.id_comp _, Category.comp_id _⟩
      | cons c tail =>
          rcases List.mem_cons.mp hb with h | h
          · subst h
            exact ⟨pullback.fst _ _, rfl, pullback.lift_fst _ _ _⟩
          · obtain ⟨r, hr, hm⟩ := ih h
            have hsnd : (relativeProjectiveProductMap f (a :: c :: tail)).1 ≫
                pullback.snd (ProjectiveSpace a.n S ↘ S)
                  (relativeProjectiveProductBase (f := f) (c :: tail)) =
                (relativeProjectiveProductMap f (c :: tail)).1 :=
              pullback.lift_snd _ _ _
            refine ⟨pullback.snd (ProjectiveSpace a.n S ↘ S)
              (relativeProjectiveProductBase (f := f) (c :: tail)) ≫ r, ?_, ?_⟩
            · have key : (pullback.snd (ProjectiveSpace a.n S ↘ S)
                  (relativeProjectiveProductBase (f := f) (c :: tail)) ≫ r) ≫
                    (ProjectiveSpace b.n S ↘ S) =
                  pullback.fst (ProjectiveSpace a.n S ↘ S)
                    (relativeProjectiveProductBase (f := f) (c :: tail)) ≫
                      (ProjectiveSpace a.n S ↘ S) := by
                rw [Category.assoc, hr]
                exact pullback.condition.symm
              exact key
            · calc (relativeProjectiveProductMap f (a :: c :: tail)).1 ≫
                    (pullback.snd (ProjectiveSpace a.n S ↘ S)
                      (relativeProjectiveProductBase (f := f) (c :: tail)) ≫ r)
                  = ((relativeProjectiveProductMap f (a :: c :: tail)).1 ≫
                      pullback.snd (ProjectiveSpace a.n S ↘ S)
                        (relativeProjectiveProductBase (f := f) (c :: tail))) ≫ r :=
                    (Category.assoc _ _ _).symm
                _ = (relativeProjectiveProductMap f (c :: tail)).1 ≫ r := by rw [hsnd]
                _ = b.map := hm

/-- **The scheme-theoretic image of the common open carries a proper chart over each member of
the cover.** With `a : U ⟶ P` an immersion into a proper `P` over `S` and `j : V ⟶ ℙⁿ_S` an
immersion of a larger open `V ⊇ U`, compatible through a projection `r : P ⟶ ℙⁿ_S`, the fibre
product of the scheme-theoretic images is open in the image of `a` and proper over `V`.

The morphism `a.image ⟶ j.image` exists because the kernel of `j.imageι` is contained in that of
`a.imageι ≫ r`, and it is proper because its composition with the proper
`j.imageι ≫ (ℙⁿ_S ↘ S)` is `a.imageι ≫ q`, which is proper.

`a` is not required to be an immersion: only quasi-compactness of `a` is used, through
`AlgebraicGeometry.isSchemeTheoreticallyDominant_toImage_of_quasiCompact`. It *is* an immersion
where this is applied in the proof of Stacks 0200, which is what makes `a.toImage` an open
immersion there, but that fact is not needed here. Dropping it is the only difference from
`AlgebraicGeometry.exists_chart_of_image`, which asks for `IsImmersion a` as well; hence the
prime. -/
theorem exists_chart_of_image' {X S P : Scheme.{u}} (f : X ⟶ S) (q : P ⟶ S) [IsProper q]
    (U V : X.Opens) (hUV : U ≤ V) (a : U.toScheme ⟶ P) [QuasiCompact a]
    (n : ℕ) (j : V.toScheme ⟶ ProjectiveSpace n S) [IsImmersion j] [QuasiCompact j]
    (hj : j ≫ (ProjectiveSpace n S ↘ S) = V.ι ≫ f) (r : P ⟶ ProjectiveSpace n S)
    (hr : r ≫ (ProjectiveSpace n S ↘ S) = q) (har : a ≫ r = X.homOfLE hUV ≫ j) :
    ∃ (W : Scheme.{u}) (e : W ⟶ a.image) (p : W ⟶ V.toScheme) (s : U.toScheme ⟶ W),
      IsOpenImmersion e ∧ IsProper p ∧ s ≫ e = a.toImage ∧ s ≫ p = X.homOfLE hUV ∧
        e ≫ a.imageι ≫ q = p ≫ V.ι ≫ f := by
  have hadom : IsSchemeTheoreticallyDominant a.toImage :=
    isSchemeTheoreticallyDominant_toImage_of_quasiCompact a
  have hk : j.imageι.ker ≤ (a.imageι ≫ r).ker := by
    rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
    have H : (a.toImage ≫ (a.imageι ≫ r)).ker = (a.imageι ≫ r).ker := by
      rw [Scheme.Hom.ker_comp, a.toImage.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [← H, ← Category.assoc, a.toImage_imageι, har]
    exact Scheme.Hom.le_ker_comp _ _
  let r' : a.image ⟶ j.image := IsClosedImmersion.lift j.imageι (a.imageι ≫ r) hk
  have hr' : r' ≫ j.imageι = a.imageι ≫ r := IsClosedImmersion.lift_fac _ _ _
  have hr'base : r' ≫ (j.imageι ≫ (ProjectiveSpace n S ↘ S)) = a.imageι ≫ q := by
    rw [← Category.assoc, hr', Category.assoc, hr]
  have : IsProper (r' ≫ (j.imageι ≫ (ProjectiveSpace n S ↘ S))) := by
    rw [hr'base]; infer_instance
  have : IsProper r' := IsProper.of_comp r' (j.imageι ≫ (ProjectiveSpace n S ↘ S))
  have ha : a.toImage ≫ r' = X.homOfLE hUV ≫ j.toImage := by
    apply (cancel_mono j.imageι).mp
    rw [Category.assoc, hr', ← Category.assoc, a.toImage_imageι, Category.assoc,
      j.toImage_imageι, har]
  refine ⟨pullback r' j.toImage, pullback.fst _ _, pullback.snd _ _,
    pullback.lift a.toImage (X.homOfLE hUV) ha, inferInstance, inferInstance,
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  rw [← hr'base, pullback.condition_assoc]
  simp only [Scheme.Hom.toImage_imageι_assoc]
  rw [hj]

/-- **Stacks Project, Tag 0200: Chow's lemma over a Noetherian base**, granted the two inputs
`AlgebraicGeometry.HasAffineProjectiveImmersions` and `AlgebraicGeometry.HasSegreEmbeddings`.

The proof is the one in Stacks. A Noetherian `X` has a finite affine open cover `F` with dense
intersection `U` (`AlgebraicGeometry.exists_finite_dense_affine_open_cover`). Each member is
immersed in a projective space over `S` by the first input, so `U` is immersed in their fibre
product `P` over `S`, which closed-immerses into a single projective space over `S` by the second
input. The scheme-theoretic image of `U` in `P` carries, over each member of the cover, a proper
chart (`AlgebraicGeometry.exists_chart_of_image'`), and those charts glue
(`AlgebraicGeometry.exists_modification_of_dense_charts`) to the required modification; it is
surjective because it is proper and dominates the dense `U`.

This statement carries no Stacks 0200 attribute: it assumes Stacks 01VS and Stacks 01WD, neither
of which this development proves, so tagging it would assert 0200 on the strength of unproved
hypotheses. -/
theorem nonempty_chowModification {X S : Scheme.{u}} (hemb : HasAffineProjectiveImmersions S)
    (hsegre : HasSegreEmbeddings S) (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] : Nonempty (ChowModification f) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian X := ⟨⟩
  obtain ⟨F, U, hAffine, hcover, hSubset, hdense⟩ :=
    exists_finite_dense_affine_open_cover (X := X)
  have : NoetherianSpace (U : Scheme.{u}) := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  by_cases hF : F.Nonempty
  · let I := {V : X.Opens // V ∈ F}
    have : Nonempty I := by
      obtain ⟨V, hV⟩ := hF
      exact ⟨⟨V, hV⟩⟩
    have hnoeth : ∀ V : I, NoetherianSpace (V.1 : Scheme.{u}) :=
      fun V => V.1.ι.isOpenEmbedding.isInducing.noetherianSpace
    have hcharts (V : I) : ∃ (n : ℕ) (i : (V.1 : Scheme.{u}) ⟶ ProjectiveSpace n S),
        IsImmersion i ∧ i ≫ (ProjectiveSpace n S ↘ S) = V.1.ι ≫ f :=
      hemb _ (V.1.ι ≫ f) (hAffine V.1 V.2) inferInstance
    choose n j hj hcomm using hcharts
    have hjI : ∀ V, IsImmersion (j V) := hj
    let A (V : I) : ProjectiveFactor (U.ι ≫ f) :=
      { n := n V
        map := X.homOfLE (hSubset V.1 V.2) ≫ j V
        isImmersion := inferInstance
        commutes := by rw [Category.assoc, hcomm, Scheme.homOfLE_ι_assoc] }
    let l := F.attach.toList.map A
    have hmem (V : I) : A V ∈ l :=
      List.mem_map.mpr ⟨V, Finset.mem_toList.mpr (F.mem_attach V), rfl⟩
    have hl : l ≠ [] := by
      intro h
      have := hmem (Classical.choice inferInstance)
      simp [h] at this
    let P := relativeProjectiveProduct l
    let q : P ⟶ S := relativeProjectiveProductBase l
    let a : U.toScheme ⟶ P := (relativeProjectiveProductMap (U.ι ≫ f) l).1
    have : IsImmersion a := isImmersion_relativeProjectiveProductMap _ l hl
    have : IsOpenImmersion a.toImage := isOpenImmersion_toImage a (.inl inferInstance)
    obtain ⟨N, e, he, heq⟩ := exists_isClosedImmersion_relativeProjectiveProduct hsegre l hl
    have : IsClosedImmersion e := he
    have hqproper : IsProper q := by
      have : q = e ≫ (ProjectiveSpace N S ↘ S) := heq.symm
      rw [this]
      infer_instance
    have hr (V : I) := exists_relativeProjectiveProductProjection (U.ι ≫ f) l (A V) (hmem V)
    choose r hrbase hramap using hr
    have hlocal (V : I) := exists_chart_of_image' f q U V.1 (hSubset V.1 V.2) a (n V) (j V)
      (hcomm V) (r V) (hrbase V) (hramap V)
    choose W k p s hk hp hsk hsp hkbase using hlocal
    have hkI : ∀ V, IsOpenImmersion (k V) := hk
    have hpI : ∀ V, IsProper (p V) := hp
    have : IsSchemeTheoreticallyDominant a.toImage :=
      isSchemeTheoreticallyDominant_toImage_of_quasiCompact a
    obtain ⟨Y, i, π, t, hi, hπ, hiq, hti, htπ, hiso⟩ :=
      exists_modification_of_dense_charts f (a.imageι ≫ q) U a.toImage
        (fun V : I => V.1) (fun x => by
          obtain ⟨V, hV, hxV⟩ := hcover x
          exact ⟨⟨V, hV⟩, hxV⟩)
        (fun V => hSubset V.1 V.2) W k p s hsk hsp hkbase
    have : IsOpenImmersion i := hi
    have : IsProper π := hπ
    refine ⟨{ n := N
              scheme := Y
              toX := π
              toProjectiveSpace := i ≫ a.imageι ≫ e
              denseOpen := U
              isProper := hπ
              surjective := surjective_of_isProper_of_dense π U t htπ hdense
              isImmersion := inferInstance
              commutes := ?_
              dense := hdense
              isIso_restrict := hiso }⟩
    rw [← hiq]
    simp only [Category.assoc, heq]
    rfl
  · have : IsEmpty X := ⟨fun x => by
      obtain ⟨V, hV, -⟩ := hcover x
      exact hF ⟨V, hV⟩⟩
    have : IsAffine X := inferInstance
    obtain ⟨m, i, hi, hcomm⟩ := hemb X f inferInstance inferInstance
    have : IsImmersion i := hi
    exact ⟨{ n := m
             scheme := X
             toX := 𝟙 X
             toProjectiveSpace := i
             denseOpen := ⊤
             isProper := inferInstance
             surjective := ⟨fun x => ⟨x, rfl⟩⟩
             isImmersion := hi
             commutes := by rw [Category.id_comp, hcomm]
             dense := by simp
             isIso_restrict := inferInstance }⟩

/-- **Chow's lemma over an affine Noetherian base, granted the Segre embedding and nothing
else.** Over an affine base the first input of
`AlgebraicGeometry.nonempty_chowModification` is discharged by
`AlgebraicGeometry.hasAffineProjectiveImmersions_of_isAffine`, so Stacks 0200 over such a base
rests on Stacks 01WD alone. -/
theorem nonempty_chowModification_of_isAffine_base {X S : Scheme.{u}} [IsAffine S]
    (hsegre : HasSegreEmbeddings S) (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] : Nonempty (ChowModification f) :=
  nonempty_chowModification (hasAffineProjectiveImmersions_of_isAffine S) hsegre f

/-- A `AlgebraicGeometry.ChowModification` witnesses
`AlgebraicGeometry.HasChowModification`, forgetting the dense open. -/
theorem HasChowModification.of_chowModification {X S : Scheme.{u}} {f : X ⟶ S}
    (m : ChowModification f) : HasChowModification f :=
  ⟨m.n, m.scheme, m.toX, m.toProjectiveSpace, m.isProper, m.surjective, m.isImmersion,
    m.commutes⟩

/-- **Chow's lemma over an affine Noetherian base in the form the rest of this development
consumes it**, granted the Segre embedding. -/
theorem hasChowModification_of_hasSegreEmbeddings {X S : Scheme.{u}} [IsAffine S]
    (hsegre : HasSegreEmbeddings S) (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] : HasChowModification f :=
  HasChowModification.of_chowModification
    (nonempty_chowModification_of_isAffine_base hsegre f).some

end AlgebraicGeometry

end
