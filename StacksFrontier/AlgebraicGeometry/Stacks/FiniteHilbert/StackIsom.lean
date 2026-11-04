module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical

/-!
# The `Isom` presheaves of the relative finite Hilbert stack are sheaves

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. This file proves the second of the three conditions of Stacks
05WB for the relative finite Hilbert category `ℋ_d(𝒳/𝒴)` of
`AlgebraicGeometry.Stack.finiteHilbertCategory`: for two objects `(U, Z, y, x, α)` and
`(U, Z', y', x', α')` over one and the same object `U` of the site, the presheaf
`Isom((U, Z, y, x, α), (U, Z', y', x', α'))` on the site over `U` is a sheaf.

An isomorphism of two such objects is a quadruple: an isomorphism of the base objects, an
isomorphism of the covers over it, an isomorphism of the objects of `𝒴` and an isomorphism of
the objects of `𝒳`, the last two compatible with the two identifications. Each of the three
non-trivial components is glued by a separate input, and all three inputs are already available:

* the cover component is glued because the big fppf site is **subcanonical**
  (`AlgebraicGeometry.BigFppfOver.subcanonical_topology`), so a compatible family of morphisms
  of the site over a covering family descends;
* the `𝒴` component is glued by the `Isom` sheaf condition **of `𝒴`**, over the given covering
  family of `U`;
* the `𝒳` component is glued by the `Isom` sheaf condition **of `𝒳`**, over the covering family
  of `Z` obtained by pulling the given one back along the cover `Z ⟶ U`.

Both sheaf conditions are taken from the ambient hypotheses that `𝒳` and `𝒴` are stacks in
groupoids; neither is reproved here. The compatibility of the glued `𝒴` and `𝒳` components with
the two identifications is itself an instance of the uniqueness half of the `Isom` sheaf
condition of `𝒴`, applied over the covering family of `Z`.

## Main results

* `AlgebraicGeometry.Stack.isom_isSheaf_finiteHilbertProjection`: the `Isom` presheaves of the
  relative finite Hilbert category are sheaves, which is the second field of
  `CategoryTheory.Functor.IsStackInGroupoids` and hence the second of the three conditions of
  Stacks 05WB.
* `AlgebraicGeometry.Stack.FiniteHilbert.ofArrows_mem_of_isPullback`: a family of cartesian
  squares over a covering family generates a covering sieve of the common source.
* `AlgebraicGeometry.Stack.FiniteHilbert.existsUnique_site_hom`,
  `AlgebraicGeometry.Stack.FiniteHilbert.site_hom_ext`,
  `AlgebraicGeometry.Stack.FiniteHilbert.existsUnique_site_hom_of_pullback` and
  `AlgebraicGeometry.Stack.FiniteHilbert.exists_site_iso_of_covers`: subcanonicality of the big
  fppf site in the four shapes a gluing argument for the cover component uses.

## Implementation notes

The three other conditions of Stacks 05WB are not in this file and are in two different states.

* **Condition (1)**, that the relative finite Hilbert category is fibred in groupoids, is
  **already proved**: it is `AlgebraicGeometry.Stack.isFiberedInGroupoids_finiteHilbertProjection`
  in `StacksFrontier/AlgebraicGeometry/Stacks/FiniteHilbert/Basic.lean`, line 256. It is used here
  only to upgrade a glued morphism whose base component is an isomorphism to an isomorphism of
  the relative finite Hilbert category.
* **Condition (3)**, effectivity of descent data — which the source calls the hardest part —
  is not proved here *for the relative category* `ℋ_d(𝒳/𝒴)`. It is proved for the
  specialisation `𝒳 = 𝒴 = S`, the category `ℋ_d` of covers, as
  `AlgebraicGeometry.Stack.descentDatum_isEffective_finiteCoverProjection` in
  `StacksFrontier/AlgebraicGeometry/Stacks/FiniteHilbert/FiniteCoverDescent.lean`, and that proof
  is what the relative case would extend: its scheme-theoretic input is effectivity of descent
  data for schemes with affine structure morphisms along an fpqc covering of an arbitrary base,
  [Stacks, Tag 0245](https://stacks.math.columbia.edu/tag/0245), available as
  `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex` in
  `StacksFrontier/AlgebraicGeometry/Descent/FamilyEffectivityLargeIndex.lean`, line 246, and the
  translation between a descent datum of the fibred category over the site and a
  scheme-theoretic `AlgebraicGeometry.DescentData` is carried out there for `ℋ_d`. What the
  relative case still owes is the same translation for the `𝒳` and `𝒴` components. Nothing in
  this file asserts condition (3), and consequently nothing in this file assembles a term of
  `CategoryTheory.Functor.IsStackInGroupoids` for the relative finite Hilbert category.

The main result is therefore deliberately stated as the *field* `isom_isSheaf` of
`CategoryTheory.Functor.IsStackInGroupoids` spelled out. It carries no `@[stacks 05WB]`
attribute of its own: the tag is registered on
`AlgebraicGeometry.Stack.isStackInGroupoids_finiteCoverProjection`, the assembled stack
condition for `ℋ_d`, so that the covering set of 05WB records an asserted term rather than a
single one of its three fields.

The `CategoryTheory.Functor.Restriction` presentation of the sheaf condition is converted once,
at the start of the main proof, into a presentation by *cocones*: a chosen restriction of an
object `P` of `ℋ_d(𝒳/𝒴)` along `f i : V i ⟶ U` is recorded as an object `t i` of
`ℋ_d(𝒳/𝒴)` together with a morphism `ν i : t i ⟶ P` lying over `f i`, and the canonical
comparisons on the overlaps become morphisms `c i j, e i j : t i j ⟶ t i, t j`. In that language
the sheaf condition reads: a cocone `μ i : t i ⟶ Q` which agrees with `ν` on the overlaps
extends uniquely to a fibre isomorphism `P ⟶ Q`. Every component argument is then a statement
about cocones, which is what makes the three gluing inputs applicable componentwise: taking the
`𝒴` or the `𝒳` component of a cocone of `ℋ_d(𝒳/𝒴)` is immediate, whereas taking the component
of a `Restriction` would require comparing the canonical comparison of `ℋ_d(𝒳/𝒴)` with the
canonical comparison of `𝒴` or of `𝒳`.

The cocone form of the `Isom` sheaf condition of a stack in groupoids
(`existsUnique_hom_of_local_cocones` and its two companions) and the component lemmas for
morphisms of `ℋ_d(𝒳/𝒴)` are `private`: they are stated generally enough to be promoted, but
promoting them belongs with the effective-descent half, which uses the same calculus. The
covering-sieve lemma `ofArrows_mem_of_isPullback` and the four subcanonicality shapes are not
private: they mention neither `ℋ_d(𝒳/𝒴)` nor a stack in groupoids, and the same `Isom` sheaf
condition for the category `ℋ_d` of covers alone
(`StacksFrontier/AlgebraicGeometry/Stacks/FiniteHilbert/FiniteCoverIsom.lean`) is exactly the cover
component of the argument below and reuses them unchanged.

## References

* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
* [Stacks Project, Tag 05WA](https://stacks.math.columbia.edu/tag/05WA)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245), which condition (3)
  needs and which is available
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w v₁ u₁ v₂ u₂

namespace AlgebraicGeometry.Stack

namespace FiniteHilbert

/-! ### Generic preliminaries -/

section Generic

variable {C : Type u₁} [Category.{v₁} C]

/-- A morphism lying over an identity of the base is a morphism of the fibre category, read
backwards: a morphism of the fibre category over `V` lies over the identity of `V`. This is the
converse of `CategoryTheory.Functor.fibreHom_of_isHomLift_id`. -/
private theorem isHomLift_id_of_fibreHom {X : Type u₂} [Category.{v₂} X] (q : X ⥤ C)
    {V : C} {a b : X} {ha : q.obj a = V} {hb : q.obj b = V} {φ : a ⟶ b}
    (h : Functor.FibreHom q a b ha hb φ) : q.IsHomLift (𝟙 V) φ := by
  have := h
  refine IsHomLift.of_fac' q (𝟙 V) φ ha hb ?_
  simpa using IsHomLift.fac' q (eqToHom ha ≫ eqToHom hb.symm) φ

/-- **A family of cartesian squares over a covering family generates a covering sieve of the
common source.** An arrow into `Z` whose composite with `q : Z ⟶ T` factors through a member of
the covering family of `T` factors, by the universal property of the square at that member,
through the corresponding member of the pulled-back family. -/
theorem ofArrows_mem_of_isPullback (J : GrothendieckTopology C) {T Z : C} {ι : Type*}
    {V : ι → C} (f : ∀ i, V i ⟶ T) (hf : Sieve.ofArrows V f ∈ J T) (q : Z ⟶ T)
    {W : ι → C} (g : ∀ i, W i ⟶ Z) (r : ∀ i, W i ⟶ V i)
    (sq : ∀ i, IsPullback (g i) (r i) q (f i)) :
    Sieve.ofArrows W g ∈ J Z := by
  refine J.superset_covering ?_ (J.pullback_stable q hf)
  rintro T' a ⟨T'', b, c, ⟨i⟩, hbc⟩
  exact ⟨W i, (sq i).lift a b hbc.symm, g i, ⟨i⟩, (sq i).lift_fst _ _ _⟩

end Generic

/-! ### Gluing a morphism of a stack in groupoids from local cocones

The `Isom` sheaf condition of a stack in groupoids, read not through chosen restrictions but
through cocones: a family of morphisms `a i : t i ⟶ x` lying over a covering family, agreeing on
the overlaps, together with a second such family `b i : t i ⟶ y`, determines a unique fibre
isomorphism `x ⟶ y` carrying `a` to `b`. -/

section LocalCocones

variable {C : Type u₁} [Category.{v₁} C] {E : BasedCategory.{v₂, u₂} C}
  {U : C} {I : Type w} {V : I → C} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → C} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))

include hVij in
/-- **The `Isom` sheaf condition of a stack in groupoids, in cocone form.** Let `x` and `y` lie
over `U`, let `{f i : V i ⟶ U}` be a covering family with genuine fibre-product overlaps, and let
`a i : t i ⟶ x` and `b i : t i ⟶ y` be two cocones lying over that family and agreeing on the
overlaps. Then there is a unique fibre isomorphism `φ : x ⟶ y` with `a i ≫ φ = b i`.

In a category fibred in groupoids every morphism over a base morphism exhibits its source as a
restriction of its target along that morphism, so the two cocones *are* families of chosen
restrictions, and the gluing family relating them is the family of identities. -/
private theorem existsUnique_hom_of_local_cocones {J : GrothendieckTopology C}
    (hs : E.p.IsStackInGroupoids.{w} J) (hf : Sieve.ofArrows V f ∈ J U)
    (x y : E.obj) (hx : E.p.obj x = U) (hy : E.p.obj y = U)
    (t : I → E.obj) (ht : ∀ i, E.p.obj (t i) = V i)
    (a : ∀ i, t i ⟶ x) (b : ∀ i, t i ⟶ y)
    (ha : ∀ i, E.p.IsHomLift (f i) (a i)) (hb : ∀ i, E.p.IsHomLift (f i) (b i))
    (tij : I → I → E.obj) (htij : ∀ i j, E.p.obj (tij i j) = Vij i j)
    (c : ∀ i j, tij i j ⟶ t i) (e : ∀ i j, tij i j ⟶ t j)
    (hc : ∀ i j, E.p.IsHomLift (pr₁ i j) (c i j))
    (he : ∀ i j, E.p.IsHomLift (pr₂ i j) (e i j))
    (hca : ∀ i j, c i j ≫ a i = e i j ≫ a j)
    (hcb : ∀ i j, c i j ≫ b i = e i j ≫ b j) :
    ∃! φ : x ⟶ y, Functor.FibreHom E.p x y hx hy φ ∧ IsIso φ ∧ ∀ i, a i ≫ φ = b i := by
  have cart {R S : C} {A B : E.obj} {g : R ⟶ S} {u : A ⟶ B} (hu : E.p.IsHomLift g u) :
      E.p.IsStronglyCartesian g u := by
    have := hu
    exact hs.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  have hcomp {z : E.obj} {hz : E.p.obj z = U} (r : ∀ i, Functor.Restriction E.p (f i) z hz)
      (rij : ∀ i j, Functor.Restriction E.p (pr₁ i j ≫ f i) z hz) (i j : I)
      (c' : (rij i j).pt ⟶ (r i).pt) (e' : (rij i j).pt ⟶ (r j).pt)
      (hc' : E.p.IsHomLift (pr₁ i j) c') (he' : E.p.IsHomLift (pr₂ i j) e')
      (h₁ : c' ≫ (r i).hom = (rij i j).hom) (h₂ : e' ≫ (r j).hom = (rij i j).hom) :
      c' = Functor.Restriction.compTo E.p (pr₁ i j) (f i) rfl (r i) (rij i j) ∧
      e' = Functor.Restriction.compTo E.p (pr₂ i j) (f j) (hVij i j).w (r j) (rij i j) :=
    ⟨Functor.Restriction.eq_compTo (p := E.p) _ _ rfl (r i) (rij i j) _ hc' h₁,
      Functor.Restriction.eq_compTo (p := E.p) _ _ (hVij i j).w (r j) (rij i j) _ he' h₂⟩
  let xr i := Functor.Restriction.ofCartesian (ht i) hx (a i) (cart (ha i))
  let yr i := Functor.Restriction.ofCartesian (ht i) hy (b i) (cart (hb i))
  let xrij i j := Functor.Restriction.ofCartesian (htij i j) hx (c i j ≫ a i)
    (cart (g := pr₁ i j ≫ f i) (by have := hc i j; have := ha i; infer_instance))
  let yrij i j := Functor.Restriction.ofCartesian (htij i j) hy (c i j ≫ b i)
    (cart (g := pr₁ i j ≫ f i) (by have := hc i j; have := hb i; infer_instance))
  obtain ⟨φ, hφ, huniq⟩ :=
    hs.isom_isSheaf x y hx hy V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij
      (fun i => 𝟙 (t i))
      (fun i => Functor.fibreHom_of_isHomLift_id (ht i) (ht i) (IsHomLift.id (ht i)))
      (fun i => IsIso.id _) (by
        intro i j
        have hx := hcomp xr xrij i j (c i j) (e i j) (hc i j) (he i j) rfl (hca i j).symm
        have hy := hcomp yr yrij i j (c i j) (e i j) (hc i j) (he i j) rfl (hcb i j).symm
        refine ⟨𝟙 (tij i j),
          Functor.fibreHom_of_isHomLift_id _ _ (IsHomLift.id (htij i j)), ?_, ?_⟩
        · unfold Functor.IsRestrictionOf
          rw [← hx.1, ← hy.1]
          exact (Category.id_comp _).trans (Category.comp_id _).symm
        · unfold Functor.IsRestrictionOf
          rw [← hx.2, ← hy.2]
          exact (Category.id_comp _).trans (Category.comp_id _).symm)
  refine ⟨φ, ⟨hφ.1, hφ.2.1, ?_⟩, ?_⟩
  · intro i
    have h := hφ.2.2 i
    change a i ≫ φ = 𝟙 (t i) ≫ b i at h
    simpa only [Category.id_comp] using h
  · rintro ψ ⟨hl, hi, hψ⟩
    refine huniq ψ ⟨hl, hi, fun i => ?_⟩
    change a i ≫ ψ = 𝟙 (t i) ≫ b i
    simpa only [Category.id_comp] using hψ i

include hVij in
/-- **Gluing a morphism of a stack in groupoids over a prescribed base morphism.** The variant of
`AlgebraicGeometry.Stack.FiniteHilbert.existsUnique_hom_of_local_cocones` in which the target `y`
lies over another object `T` and the sought morphism is to lie over a given `q : U ⟶ T`: factor
the second cocone through a chosen restriction of `y` along `q`, glue there, and compose back. -/
private theorem exists_hom_over_of_local_cocones {J : GrothendieckTopology C}
    (hs : E.p.IsStackInGroupoids.{w} J) (hf : Sieve.ofArrows V f ∈ J U)
    {T : C} (q : U ⟶ T) (x y : E.obj) (hx : E.p.obj x = U) (hy : E.p.obj y = T)
    (t : I → E.obj) (ht : ∀ i, E.p.obj (t i) = V i)
    (a : ∀ i, t i ⟶ x) (b : ∀ i, t i ⟶ y)
    (ha : ∀ i, E.p.IsHomLift (f i) (a i)) (hb : ∀ i, E.p.IsHomLift (f i ≫ q) (b i))
    (tij : I → I → E.obj) (htij : ∀ i j, E.p.obj (tij i j) = Vij i j)
    (c : ∀ i j, tij i j ⟶ t i) (e : ∀ i j, tij i j ⟶ t j)
    (hc : ∀ i j, E.p.IsHomLift (pr₁ i j) (c i j))
    (he : ∀ i j, E.p.IsHomLift (pr₂ i j) (e i j))
    (hca : ∀ i j, c i j ≫ a i = e i j ≫ a j)
    (hcb : ∀ i j, c i j ≫ b i = e i j ≫ b j) :
    ∃ φ : x ⟶ y, E.p.IsHomLift q φ ∧ ∀ i, a i ≫ φ = b i := by
  classical
  let yr := Functor.Restriction.ofIsFiberedInGroupoids E.p hs.isFiberedInGroupoids q y hy
  have hcart := yr.isStronglyCartesian_hom
  have hylift := yr.isHomLift_hom
  let β (i : I) : t i ⟶ yr.pt := by
    have := hb i
    exact Functor.IsStronglyCartesian.map E.p q yr.hom (g := f i) rfl (b i)
  have hβ (i : I) : E.p.IsHomLift (f i) (β i) := by
    have := hb i
    dsimp only [β]
    infer_instance
  have hβfac (i : I) : β i ≫ yr.hom = b i := by
    have := hb i
    exact Functor.IsStronglyCartesian.fac E.p q yr.hom (g := f i) rfl (b i)
  have hβcompat (i j : I) : c i j ≫ β i = e i j ≫ β j := by
    have := hc i j
    have := he i j
    have := hβ i
    have := hβ j
    have h₁ : E.p.IsHomLift (pr₁ i j ≫ f i) (c i j ≫ β i) := inferInstance
    have h₂ : E.p.IsHomLift (pr₁ i j ≫ f i) (e i j ≫ β j) := by
      rw [(hVij i j).w]
      infer_instance
    refine Functor.IsStronglyCartesian.ext E.p q yr.hom (pr₁ i j ≫ f i) ?_
    rw [Category.assoc, Category.assoc, hβfac, hβfac, hcb]
  obtain ⟨φ, ⟨hφlift, -, hφfac⟩, -⟩ :=
    existsUnique_hom_of_local_cocones (hVij := hVij) hs hf x yr.pt hx yr.hpt
      t ht a β ha hβ tij htij c e hc he hca hβcompat
  refine ⟨φ ≫ yr.hom, ?_, fun i => ?_⟩
  · have := isHomLift_id_of_fibreHom E.p hφlift
    exact Functor.isHomLift_of_eq (n := 𝟙 U ≫ q) inferInstance (by simp)
  · rw [← Category.assoc, hφfac, hβfac]

include hVij in
/-- **Two morphisms of a stack in groupoids agreeing on a cocone over a covering family are
equal.** The uniqueness half of
`AlgebraicGeometry.Stack.FiniteHilbert.exists_hom_over_of_local_cocones`: both morphisms factor
through a chosen restriction of the target along the common base morphism, and the two
factorizations glue the same cocone. -/
private theorem hom_ext_of_local_cocones {J : GrothendieckTopology C}
    (hs : E.p.IsStackInGroupoids.{w} J) (hf : Sieve.ofArrows V f ∈ J U)
    {T : C} (q : U ⟶ T) (x y : E.obj) (hx : E.p.obj x = U) (hy : E.p.obj y = T)
    (t : I → E.obj) (ht : ∀ i, E.p.obj (t i) = V i)
    (a : ∀ i, t i ⟶ x) (ha : ∀ i, E.p.IsHomLift (f i) (a i))
    (tij : I → I → E.obj) (htij : ∀ i j, E.p.obj (tij i j) = Vij i j)
    (c : ∀ i j, tij i j ⟶ t i) (e : ∀ i j, tij i j ⟶ t j)
    (hc : ∀ i j, E.p.IsHomLift (pr₁ i j) (c i j))
    (he : ∀ i j, E.p.IsHomLift (pr₂ i j) (e i j))
    (hca : ∀ i j, c i j ≫ a i = e i j ≫ a j)
    (φ ψ : x ⟶ y) (hφ : E.p.IsHomLift q φ) (hψ : E.p.IsHomLift q ψ)
    (h : ∀ i, a i ≫ φ = a i ≫ ψ) : φ = ψ := by
  classical
  let r := Functor.Restriction.ofIsFiberedInGroupoids E.p hs.isFiberedInGroupoids q y hy
  have hcart := r.isStronglyCartesian_hom
  have hr := r.isHomLift_hom
  have key (χ : x ⟶ y) (hχ : E.p.IsHomLift q χ) : ∃ α : x ⟶ r.pt,
      E.p.IsHomLift (𝟙 U) α ∧ IsIso α ∧ α ≫ r.hom = χ ∧ ∀ i, E.p.IsHomLift (f i) (a i ≫ α) := by
    let α : x ⟶ r.pt := Functor.IsStronglyCartesian.map E.p q r.hom
      (g := 𝟙 U) (show q = 𝟙 U ≫ q by simp) χ
    have hα : E.p.IsHomLift (𝟙 U) α := by dsimp only [α]; infer_instance
    refine ⟨α, hα, ?_, Functor.IsStronglyCartesian.fac E.p q r.hom (g := 𝟙 U)
      (show q = 𝟙 U ≫ q by simp) χ, fun i => ?_⟩
    · have := hs.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 U) α
      exact Functor.IsStronglyCartesian.isIso_of_base_isIso E.p (𝟙 U) α
    · have := ha i
      exact Functor.isHomLift_of_eq (n := f i ≫ 𝟙 U) inferInstance (by simp)
  obtain ⟨α, hα, hαiso, hαfac, halift⟩ := key φ hφ
  obtain ⟨β, hβ, hβiso, hβfac, hblift⟩ := key ψ hψ
  obtain ⟨δ, -, huniq⟩ := existsUnique_hom_of_local_cocones (hVij := hVij) hs hf
    x r.pt hx r.hpt t ht a (fun i => a i ≫ α) ha halift tij htij c e hc he hca
    (fun i j => by rw [← Category.assoc, ← Category.assoc, hca])
  have heq : α = β := by
    refine (huniq α ⟨Functor.fibreHom_of_isHomLift_id hx r.hpt hα, hαiso,
      fun _ => rfl⟩).trans (huniq β ⟨Functor.fibreHom_of_isHomLift_id hx r.hpt hβ, hβiso,
        fun i => ?_⟩).symm
    have := halift i
    have := hblift i
    refine Functor.IsStronglyCartesian.ext E.p q r.hom (f i) ?_
    rw [Category.assoc, Category.assoc, hαfac, hβfac, h]
  rw [← hαfac, ← hβfac, heq]

end LocalCocones

/-! ### Gluing morphisms of the big fppf site along a covering family -/

section Subcanonical

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The big fppf site of `S` is subcanonical**, in the form the gluing argument uses it: a
family of morphisms to `X` which agree on every overlap of a covering family descends to a single
morphism of the site, uniquely. -/
theorem existsUnique_site_hom {T : BigFppfOver B S hS} {ι : Type*}
    {V : ι → BigFppfOver B S hS} (f : ∀ i, V i ⟶ T)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS T)
    (X : BigFppfOver B S hS) (a : ∀ i, V i ⟶ X)
    (ha : ∀ {W : BigFppfOver B S hS} {i j : ι} (g : W ⟶ V i) (h : W ⟶ V j),
      g ≫ f i = h ≫ f j → g ≫ a i = h ≫ a j) :
    ∃! φ : T ⟶ X, ∀ i, f i ≫ φ = a i :=
  (Presieve.isSheafFor_arrows_iff (yoneda.obj X) f).mp
    ((Presieve.isSheafFor_iff_generate _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := BigFppfOver.topology B S hS) (yoneda.obj X) _ hf)) a
    (fun _ _ _ _ _ h => ha _ _ h)

/-- Two morphisms of the big fppf site of `S` which agree after restriction along every member of
a covering family are equal. -/
theorem site_hom_ext {T X : BigFppfOver B S hS} {ι : Type*}
    {V : ι → BigFppfOver B S hS} (f : ∀ i, V i ⟶ T)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS T)
    {a b : T ⟶ X} (h : ∀ i, f i ≫ a = f i ≫ b) : a = b := by
  obtain ⟨c, -, huniq⟩ := existsUnique_site_hom f hf X (fun i => f i ≫ a)
    (fun g k hgk => by rw [← Category.assoc, hgk, Category.assoc])
  exact (huniq a fun _ => rfl).trans (huniq b fun i => (h i).symm).symm

/-- The descent condition of `AlgebraicGeometry.Stack.FiniteHilbert.existsUnique_site_hom`,
checked on a chosen family of fibre products of the covering family with itself: an arbitrary
pair of morphisms into two members of the family agreeing over the base factors through the
fibre product. -/
theorem existsUnique_site_hom_of_pullback {T : BigFppfOver B S hS} {ι : Type*}
    {V : ι → BigFppfOver B S hS} (f : ∀ i, V i ⟶ T)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS T)
    {W : ι → ι → BigFppfOver B S hS} (c : ∀ i j, W i j ⟶ V i) (e : ∀ i j, W i j ⟶ V j)
    (sq : ∀ i j, IsPullback (c i j) (e i j) (f i) (f j))
    (X : BigFppfOver B S hS) (a : ∀ i, V i ⟶ X)
    (ha : ∀ i j, c i j ≫ a i = e i j ≫ a j) :
    ∃! φ : T ⟶ X, ∀ i, f i ≫ φ = a i := by
  refine existsUnique_site_hom f hf X a ?_
  intro T' i j g h hgh
  have h₁ : (sq i j).lift g h hgh ≫ c i j = g := (sq i j).lift_fst _ _ _
  have h₂ : (sq i j).lift g h hgh ≫ e i j = h := (sq i j).lift_snd _ _ _
  calc g ≫ a i = ((sq i j).lift g h hgh ≫ c i j) ≫ a i := by rw [h₁]
    _ = ((sq i j).lift g h hgh ≫ e i j) ≫ a j := by
        rw [Category.assoc, Category.assoc, ha]
    _ = h ≫ a j := by rw [h₂]

/-- Two objects of the big fppf site of `S` covered by one and the same family, compatibly with a
chosen family of fibre products of it with itself, are isomorphic by an isomorphism matching the
two covering families. -/
theorem exists_site_iso_of_covers {X Y : BigFppfOver B S hS} {ι : Type*}
    {V : ι → BigFppfOver B S hS} (f : ∀ i, V i ⟶ X) (g : ∀ i, V i ⟶ Y)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS X)
    (hg : Sieve.ofArrows V g ∈ BigFppfOver.topology B S hS Y)
    {W : ι → ι → BigFppfOver B S hS} (c : ∀ i j, W i j ⟶ V i) (e : ∀ i j, W i j ⟶ V j)
    (sqf : ∀ i j, IsPullback (c i j) (e i j) (f i) (f j))
    (sqg : ∀ i j, IsPullback (c i j) (e i j) (g i) (g j)) :
    ∃ φ : X ≅ Y, ∀ i, f i ≫ φ.hom = g i := by
  obtain ⟨a, ha, -⟩ := existsUnique_site_hom_of_pullback f hf c e sqf Y g
    (fun i j => (sqg i j).w)
  obtain ⟨b, hb, -⟩ := existsUnique_site_hom_of_pullback g hg c e sqg X f
    (fun i j => (sqf i j).w)
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · exact site_hom_ext f hf fun i => by rw [← Category.assoc, ha, hb, Category.comp_id]
  · exact site_hom_ext g hg fun i => by rw [← Category.assoc, hb, ha, Category.comp_id]

end Subcanonical

/-! ### Morphisms of the relative finite Hilbert category and their components -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- The base component of a morphism of the relative finite Hilbert category which lies in the
fibre over `U` is the identification of its two base objects with `U`. -/
private theorem Hom.f_eq_of_fibreHom {P Q : Object B S hS 𝒳 𝒴 F d} {U : BigFppfOver B S hS}
    (hP : P.U = U) (hQ : Q.U = U) (φ : P ⟶ Q)
    (hφ : Functor.FibreHom (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) P Q hP hQ φ) :
    φ.f = eqToHom hP ≫ eqToHom hQ.symm := by
  have := hφ
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (eqToHom hP ≫ eqToHom hQ.symm) φ).symm

/-- **A commuting square of morphisms of the relative finite Hilbert category whose base
components form a cartesian square has cartesian cover components.** The two cover squares of the
morphisms present the covers as base changes, so the composite square is cartesian and the cover
square is obtained by cancelling the cartesian square on its right. -/
private theorem Hom.isPullback_g {P Q R T : Object B S hS 𝒳 𝒴 F d}
    (a : P ⟶ Q) (b : P ⟶ R) (c : Q ⟶ T) (e : R ⟶ T) (h : a ≫ c = b ≫ e)
    (sq : IsPullback a.f b.f c.f e.f) : IsPullback a.g b.g c.g e.g := by
  have houter := (a.square.paste_vert sq).flip
  rw [← b.square.w, ← c.square.w] at houter
  have hcomm : b.g ≫ e.g = a.g ≫ c.g := (congrArg Hom.g h).symm
  exact (houter.of_right hcomm e.square.flip).flip

/-- The cover components of a cocone over a covering family of the base again form a covering
family of the source cover, since the cover squares are cartesian. -/
private theorem Hom.ofArrows_g_mem {P : Object B S hS 𝒳 𝒴 F d} {ι : Type w}
    (t : ι → Object B S hS 𝒳 𝒴 F d) (ν : ∀ i, t i ⟶ P)
    (hf : Sieve.ofArrows (fun i => (t i).U) (fun i => (ν i).f) ∈
      BigFppfOver.topology B S hS P.U) :
    Sieve.ofArrows (fun i => (t i).Z) (fun i => (ν i).g) ∈ BigFppfOver.topology B S hS P.Z :=
  ofArrows_mem_of_isPullback _ (fun i => (ν i).f) hf P.q
    (fun i => (ν i).g) (fun i => (t i).q) (fun i => (ν i).square)

/-! ### The cocone form of the `Isom` sheaf condition for the relative finite Hilbert category -/

/-- **Two morphisms of the relative finite Hilbert category agreeing on a cocone over a covering
family are equal**, provided their base components agree. The four components are compared
separately: the base components by hypothesis; the cover components by subcanonicality of the
site, over the covering family of `P.Z` obtained by pulling the given one back along `P.q`; the
`𝒴` components by the `Isom` sheaf condition of `𝒴` over the given covering family; and the `𝒳`
components by the `Isom` sheaf condition of `𝒳` over the pulled-back family. -/
private theorem Hom.ext_of_local_cocones {P Q : Object B S hS 𝒳 𝒴 F d} {ι : Type w}
    (t : ι → Object B S hS 𝒳 𝒴 F d) (ν : ∀ i, t i ⟶ P)
    (hf : Sieve.ofArrows (fun i => (t i).U) (fun i => (ν i).f) ∈
      BigFppfOver.topology B S hS P.U)
    (tij : ι → ι → Object B S hS 𝒳 𝒴 F d)
    (c : ∀ i j, tij i j ⟶ t i) (e : ∀ i j, tij i j ⟶ t j)
    (hca : ∀ i j, c i j ≫ ν i = e i j ≫ ν j)
    (sq : ∀ i j, IsPullback (c i j).f (e i j).f (ν i).f (ν j).f)
    {φ ψ : P ⟶ Q} (hbase : φ.f = ψ.f) (h : ∀ i, ν i ≫ φ = ν i ≫ ψ) : φ = ψ := by
  have hgcover := Hom.ofArrows_g_mem t ν hf
  have hsource : φ.g = ψ.g := site_hom_ext (fun i => (ν i).g) hgcover
    (fun i => congrArg Hom.g (h i))
  refine Hom.ext hbase hsource ?_ ?_
  · refine hom_ext_of_local_cocones (E := 𝒴.toBasedCategory) (hVij := sq)
      𝒴.isStackInGroupoids hf φ.f P.y Q.y P.y_over Q.y_over
      (fun i => (t i).y) (fun i => (t i).y_over)
      (fun i => (ν i).b) (fun i => (ν i).b_over)
      (fun i j => (tij i j).y) (fun i j => (tij i j).y_over)
      (fun i j => (c i j).b) (fun i j => (e i j).b)
      (fun i j => (c i j).b_over) (fun i j => (e i j).b_over)
      (fun i j => congrArg Hom.b (hca i j)) φ.b ψ.b φ.b_over
      (by rw [hbase]; exact ψ.b_over) ?_
    exact fun i => congrArg Hom.b (h i)
  · refine hom_ext_of_local_cocones (E := 𝒳.toBasedCategory)
      (V := fun i => (t i).Z) (f := fun i => (ν i).g)
      (Vij := fun i j => (tij i j).Z)
      (pr₁ := fun i j => (c i j).g) (pr₂ := fun i j => (e i j).g)
      (hVij := fun i j => Hom.isPullback_g _ _ _ _ (hca i j) (sq i j))
      𝒳.isStackInGroupoids hgcover φ.g P.x Q.x P.x_over Q.x_over
      (fun i => (t i).x) (fun i => (t i).x_over)
      (fun i => (ν i).a) (fun i => (ν i).a_over)
      (fun i j => (tij i j).x) (fun i j => (tij i j).x_over)
      (fun i j => (c i j).a) (fun i j => (e i j).a)
      (fun i j => (c i j).a_over) (fun i j => (e i j).a_over)
      (fun i j => congrArg Hom.a (hca i j)) φ.a ψ.a φ.a_over
      (by rw [hsource]; exact ψ.a_over) ?_
    exact fun i => congrArg Hom.a (h i)

/-- **Assembling a morphism of the relative finite Hilbert category from a cocone**, given its
base and cover components and its `𝒴` component. Only the `𝒳` component is glued here, by the
`Isom` sheaf condition of `𝒳` over the covering family of `P.Z`; the compatibility of the
assembled quadruple with the two identifications is the uniqueness half of the `Isom` sheaf
condition of `𝒴`, applied to the two morphisms `F x ⟶ Q.y` lying over `P.q ≫ f`. -/
private theorem Hom.exists_of_local_cocones {P Q : Object B S hS 𝒳 𝒴 F d} {ι : Type w}
    (t : ι → Object B S hS 𝒳 𝒴 F d) (ν : ∀ i, t i ⟶ P) (μ : ∀ i, t i ⟶ Q)
    (hf : Sieve.ofArrows (fun i => (t i).U) (fun i => (ν i).f) ∈
      BigFppfOver.topology B S hS P.U)
    (tij : ι → ι → Object B S hS 𝒳 𝒴 F d)
    (c : ∀ i j, tij i j ⟶ t i) (e : ∀ i j, tij i j ⟶ t j)
    (hν : ∀ i j, c i j ≫ ν i = e i j ≫ ν j)
    (hμ : ∀ i j, c i j ≫ μ i = e i j ≫ μ j)
    (sq : ∀ i j, IsPullback (c i j).f (e i j).f (ν i).f (ν j).f)
    (fU : P.U ≅ Q.U) (gZ : P.Z ≅ Q.Z) (hfg : gZ.hom ≫ Q.q = P.q ≫ fU.hom)
    (hνf : ∀ i, (ν i).f ≫ fU.hom = (μ i).f)
    (hνg : ∀ i, (ν i).g ≫ gZ.hom = (μ i).g)
    (b : P.y ⟶ Q.y) (hb : 𝒴.toBasedCategory.p.IsHomLift fU.hom b)
    (hνb : ∀ i, (ν i).b ≫ b = (μ i).b) :
    ∃ φ : P ⟶ Q, φ.f = fU.hom ∧ ∀ i, ν i ≫ φ = μ i := by
  have hgcover := Hom.ofArrows_g_mem t ν hf
  have hsq (i j : ι) := Hom.isPullback_g _ _ _ _ (hν i j) (sq i j)
  have hμlift (i : ι) : 𝒳.toBasedCategory.p.IsHomLift ((ν i).g ≫ gZ.hom) (μ i).a := by
    rw [hνg]; exact (μ i).a_over
  obtain ⟨a, ha, hνa⟩ := exists_hom_over_of_local_cocones
    (E := 𝒳.toBasedCategory) (hVij := hsq) 𝒳.isStackInGroupoids hgcover
    gZ.hom P.x Q.x P.x_over Q.x_over
    (fun i => (t i).x) (fun i => (t i).x_over)
    (fun i => (ν i).a) (fun i => (μ i).a) (fun i => (ν i).a_over) hμlift
    (fun i j => (tij i j).x) (fun i j => (tij i j).x_over)
    (fun i j => (c i j).a) (fun i j => (e i j).a)
    (fun i j => (c i j).a_over) (fun i j => (e i j).a_over)
    (fun i j => congrArg Hom.a (hν i j)) (fun i j => congrArg Hom.a (hμ i j))
  have hcompat : F.map a ≫ Q.α = P.α ≫ b := by
    have := P.α_over
    have := Q.α_over
    have h₁ : 𝒴.toBasedCategory.p.IsHomLift (P.q ≫ fU.hom) (F.map a ≫ Q.α) := by
      rw [← hfg]
      have := ha
      have : 𝒴.toBasedCategory.p.IsHomLift gZ.hom (F.map a) := inferInstance
      infer_instance
    have h₂ : 𝒴.toBasedCategory.p.IsHomLift (P.q ≫ fU.hom) (P.α ≫ b) := by
      have := hb
      infer_instance
    refine hom_ext_of_local_cocones (E := 𝒴.toBasedCategory) (hVij := hsq)
      𝒴.isStackInGroupoids hgcover (P.q ≫ fU.hom) (F.obj P.x) Q.y
      ((F.w_obj _).trans P.x_over) Q.y_over
      (fun i => F.obj (t i).x) (fun i => (F.w_obj _).trans (t i).x_over)
      (fun i => F.map (ν i).a) (fun i => by have := (ν i).a_over; infer_instance)
      (fun i j => F.obj (tij i j).x) (fun i j => (F.w_obj _).trans (tij i j).x_over)
      (fun i j => F.map (c i j).a) (fun i j => F.map (e i j).a)
      (fun i j => by have := (c i j).a_over; infer_instance)
      (fun i j => by have := (e i j).a_over; infer_instance)
      (fun i j => by
        have hh := congrArg Hom.a (hν i j)
        change (c i j).a ≫ (ν i).a = (e i j).a ≫ (ν j).a at hh
        simpa only [Functor.map_comp] using congrArg F.map hh) _ _ h₁ h₂ (fun i => ?_)
    calc F.map (ν i).a ≫ F.map a ≫ Q.α = F.map (μ i).a ≫ Q.α := by
          rw [← Category.assoc, ← F.map_comp, hνa]
      _ = (t i).α ≫ (μ i).b := (μ i).compatible
      _ = (t i).α ≫ (ν i).b ≫ b := by rw [hνb]
      _ = F.map (ν i).a ≫ P.α ≫ b := by rw [← Category.assoc, ← (ν i).compatible,
          Category.assoc]
  exact ⟨⟨fU.hom, gZ.hom, IsPullback.of_horiz_isIso ⟨hfg⟩, b, hb, a, ha, hcompat⟩, rfl,
    fun i => Hom.ext (hνf i) (hνg i) (hνb i) (hνa i)⟩

/-- **A cocone over a covering family extends to an isomorphism of the relative finite Hilbert
category**, given an isomorphism of the base objects compatible with it. The cover component is
produced by subcanonicality of the site, the two covering families of `P.Z` and `Q.Z` being the
pullbacks of the given family along `P.q` and `Q.q`; the `𝒴` component is glued by the `Isom`
sheaf condition of `𝒴`; and the remaining data is assembled by
`AlgebraicGeometry.Stack.FiniteHilbert.Hom.exists_of_local_cocones`. The result is an isomorphism
because its base component is one and the relative finite Hilbert category is fibred in
groupoids. -/
private theorem Hom.exists_iso_of_local_cocones {P Q : Object B S hS 𝒳 𝒴 F d} {ι : Type w}
    (t : ι → Object B S hS 𝒳 𝒴 F d) (ν : ∀ i, t i ⟶ P) (μ : ∀ i, t i ⟶ Q)
    (hf : Sieve.ofArrows (fun i => (t i).U) (fun i => (ν i).f) ∈
      BigFppfOver.topology B S hS P.U)
    (tij : ι → ι → Object B S hS 𝒳 𝒴 F d)
    (c : ∀ i j, tij i j ⟶ t i) (e : ∀ i j, tij i j ⟶ t j)
    (hν : ∀ i j, c i j ≫ ν i = e i j ≫ ν j)
    (hμ : ∀ i j, c i j ≫ μ i = e i j ≫ μ j)
    (sq : ∀ i j, IsPullback (c i j).f (e i j).f (ν i).f (ν j).f)
    (fU : P.U ≅ Q.U) (hνf : ∀ i, (ν i).f ≫ fU.hom = (μ i).f) :
    ∃ φ : P ⟶ Q, φ.f = fU.hom ∧ IsIso φ ∧ ∀ i, ν i ≫ φ = μ i := by
  have hμcover : Sieve.ofArrows (fun i => (t i).U) (fun i => (μ i).f) ∈
      BigFppfOver.topology B S hS Q.U := by
    have hpb := (BigFppfOver.topology B S hS).pullback_stable fU.inv hf
    have heq : Sieve.pullback fU.inv
          (Sieve.ofArrows (fun i => (t i).U) (fun i => (ν i).f)) =
        Sieve.ofArrows (fun i => (t i).U) (fun i => (ν i).f ≫ fU.hom) :=
      Sieve.pullback_ofArrows_of_iso _ _ fU.symm
    rw [heq] at hpb
    simpa only [hνf] using hpb
  have sqμ (i j : ι) : IsPullback (c i j).f (e i j).f (μ i).f (μ j).f :=
    (sq i j).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) fU
      (by simp) (by simp) (by simpa using hνf i) (by simpa using hνf j)
  have hνsource := Hom.ofArrows_g_mem t ν hf
  have hμsource := Hom.ofArrows_g_mem t μ hμcover
  obtain ⟨gZ, hg⟩ := exists_site_iso_of_covers (fun i => (ν i).g) (fun i => (μ i).g)
    hνsource hμsource (fun i j => (c i j).g) (fun i j => (e i j).g)
    (fun i j => Hom.isPullback_g _ _ _ _ (hν i j) (sq i j))
    (fun i j => Hom.isPullback_g _ _ _ _ (hμ i j) (sqμ i j))
  have hfg : gZ.hom ≫ Q.q = P.q ≫ fU.hom := by
    refine site_hom_ext (fun i => (ν i).g) hνsource fun i => ?_
    rw [← Category.assoc, hg, (μ i).square.w, ← hνf, ← Category.assoc, ← (ν i).square.w,
      Category.assoc]
  obtain ⟨b, hb, hνb⟩ := exists_hom_over_of_local_cocones
    (E := 𝒴.toBasedCategory) (hVij := sq) 𝒴.isStackInGroupoids hf fU.hom
    P.y Q.y P.y_over Q.y_over
    (fun i => (t i).y) (fun i => (t i).y_over)
    (fun i => (ν i).b) (fun i => (μ i).b) (fun i => (ν i).b_over)
    (fun i => by rw [hνf]; exact (μ i).b_over)
    (fun i j => (tij i j).y) (fun i j => (tij i j).y_over)
    (fun i j => (c i j).b) (fun i j => (e i j).b)
    (fun i j => (c i j).b_over) (fun i j => (e i j).b_over)
    (fun i j => congrArg Hom.b (hν i j)) (fun i j => congrArg Hom.b (hμ i j))
  obtain ⟨φ, hφf, hφ⟩ := Hom.exists_of_local_cocones t ν μ hf tij c e hν hμ sq
    fU gZ hfg hνf hg b hb hνb
  refine ⟨φ, hφf, ?_, hφ⟩
  have : IsIso φ.f := hφf ▸ inferInstance
  have : (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).IsHomLift φ.f φ :=
    CategoryTheory.IsHomLift.map _ φ
  have := (isFiberedInGroupoids_finiteHilbertProjection (B := B) (S := S) (hS := hS)
    (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).isStronglyCartesian_homLift φ.f φ
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso
    (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) φ.f φ

end FiniteHilbert

/-! ### The `Isom` sheaf condition -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- **Condition (2) of Stacks 05WB: the `Isom` presheaves of the relative finite Hilbert category
`ℋ_d(𝒳/𝒴)` are sheaves.** For two objects `P` and `Q` of `ℋ_d(𝒳/𝒴)` lying over one and the same
object `U` of the big fppf site and a covering family `{V i ⟶ U}` whose overlaps are genuine
fibre products `V i ×_U V j`, a family of isomorphisms `P|_{V i} ⟶ Q|_{V i}` which agree on the
overlaps glues to a unique isomorphism `P ⟶ Q` of the fibre over `U` restricting to the given
ones.

The three non-trivial components of the glued isomorphism come from three separate inputs: the
cover component from subcanonicality of the big fppf site, the `𝒴` component from the `Isom`
sheaf condition of `𝒴` over the given covering family, and the `𝒳` component from the `Isom`
sheaf condition of `𝒳` over the covering family of `P.Z` obtained by pulling the given one back
along the cover `P.Z ⟶ U`. Compatibility of the glued components with the two identifications is
the uniqueness half of the `Isom` sheaf condition of `𝒴` over that same pulled-back family.

Condition (1) of Stacks 05WB is
`AlgebraicGeometry.Stack.isFiberedInGroupoids_finiteHilbertProjection`. Condition (3),
effectivity of descent data, is not proved here for the relative category `ℋ_d(𝒳/𝒴)`; it is
proved for the specialisation `𝒳 = 𝒴 = S` as
`AlgebraicGeometry.Stack.descentDatum_isEffective_finiteCoverProjection`, and the three
conditions for that specialisation are assembled in
`AlgebraicGeometry.Stack.isStackInGroupoids_finiteCoverProjection`, which is where the
`@[stacks 05WB]` attribute sits. -/
theorem isom_isSheaf_finiteHilbertProjection {U : BigFppfOver B S hS}
    (P Q : FiniteHilbert.Object B S hS 𝒳 𝒴 F d)
    (hP : (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).obj P = U)
    (hQ : (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).obj Q = U)
    {I : Type w} (V : I → BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U)
    (Vij : I → I → BigFppfOver B S hS)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Functor.Restriction (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (f i) P hP)
    (yr : ∀ i, Functor.Restriction (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (f i) Q hQ)
    (xrij : ∀ i j, Functor.Restriction (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (pr₁ i j ≫ f i) P hP)
    (yrij : ∀ i j, Functor.Restriction (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (pr₁ i j ≫ f i) Q hQ) :
    Functor.IsomIsSheafFor (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) P Q hP hQ V f Vij pr₁ pr₂ hVij
      xr yr xrij yrij := by
  intro φ hφ hiso hcompat
  -- the identifications of the base objects, spelled without the projection
  have hP' : P.U = U := hP
  have hQ' : Q.U = U := hQ
  have hxpt (i : I) : (xr i).pt.U = V i := (xr i).hpt
  have hypt (i : I) : (yr i).pt.U = V i := (yr i).hpt
  have hxptij (i j : I) : (xrij i j).pt.U = Vij i j := (xrij i j).hpt
  let t i := (xr i).pt
  let ν i := (xr i).hom
  let μ i := φ i ≫ (yr i).hom
  let tij i j := (xrij i j).pt
  let c i j := Functor.Restriction.compTo (finiteHilbertProjection (B := B) (S := S) (hS := hS)
    (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (pr₁ i j) (f i) rfl (xr i) (xrij i j)
  let e i j := Functor.Restriction.compTo (finiteHilbertProjection (B := B) (S := S) (hS := hS)
    (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (pr₂ i j) (f j) (hVij i j).w (xr j) (xrij i j)
  have hν (i j : I) : c i j ≫ ν i = e i j ≫ ν j := by
    dsimp only [c, e, ν]
    rw [Functor.Restriction.compTo_hom, Functor.Restriction.compTo_hom]
  have hμ (i j : I) : c i j ≫ μ i = e i j ≫ μ j := by
    obtain ⟨γ, -, hγi, hγj⟩ := hcompat i j
    change γ ≫ _ = c i j ≫ φ i at hγi
    change γ ≫ _ = e i j ≫ φ j at hγj
    dsimp only [μ]
    rw [← Category.assoc, ← hγi, Category.assoc, Functor.Restriction.compTo_hom,
      ← Category.assoc, ← hγj, Category.assoc, Functor.Restriction.compTo_hom]
  have hνf (i : I) : (ν i).f = eqToHom (hxpt i) ≫ f i ≫ eqToHom hP'.symm := by
    have := (xr i).isHomLift_hom
    exact CategoryTheory.IsHomLift.fac'
      (finiteHilbertProjection (B := B) (S := S) (hS := hS)
        (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (f i) (xr i).hom
  have hνcover : Sieve.ofArrows (fun i => (t i).U) (fun i => (ν i).f) ∈
      BigFppfOver.topology B S hS P.U := by
    refine FiniteHilbert.ofArrows_mem_of_isPullback _ f hf (eqToHom hP') (fun i => (ν i).f)
      (fun i => eqToHom (hxpt i)) fun i => ?_
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [hνf]
    simp
  have hcf (i j : I) : (c i j).f =
      eqToHom (hxptij i j) ≫ pr₁ i j ≫ eqToHom (hxpt i).symm :=
    Functor.Restriction.compTo_map _ (pr₁ i j) (f i) rfl (xr i) (xrij i j)
  have hef (i j : I) : (e i j).f =
      eqToHom (hxptij i j) ≫ pr₂ i j ≫ eqToHom (hxpt j).symm :=
    Functor.Restriction.compTo_map _ (pr₂ i j) (f j) (hVij i j).w (xr j) (xrij i j)
  have sq (i j : I) : IsPullback (c i j).f (e i j).f (ν i).f (ν j).f := by
    rw [hcf i j, hef i j, hνf, hνf]
    exact (hVij i j).of_iso (eqToIso (hxptij i j).symm) (eqToIso (hxpt i).symm)
      (eqToIso (hxpt j).symm) (eqToIso hP'.symm) (by simp) (by simp) (by simp) (by simp)
  let fU : P.U ≅ Q.U := eqToIso (hP'.trans hQ'.symm)
  have hfU : fU.hom = eqToHom hP' ≫ eqToHom hQ'.symm := (eqToHom_trans hP' hQ'.symm).symm
  have hμf (i : I) : (ν i).f ≫ fU.hom = (μ i).f := by
    have := (yr i).isHomLift_hom
    have hy : (yr i).hom.f = eqToHom (hypt i) ≫ f i ≫ eqToHom hQ'.symm :=
      CategoryTheory.IsHomLift.fac'
        (finiteHilbertProjection (B := B) (S := S) (hS := hS)
          (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (f i) (yr i).hom
    have hi := FiniteHilbert.Hom.f_eq_of_fibreHom (hxpt i) (hypt i) (φ i) (hφ i)
    change (ν i).f ≫ fU.hom = (φ i).f ≫ (yr i).hom.f
    rw [hνf, hi, hy, hfU]
    simp
  obtain ⟨g, hgf, hgiso, hg⟩ := FiniteHilbert.Hom.exists_iso_of_local_cocones
    t ν μ hνcover tij c e hν hμ sq fU hμf
  have hglift : Functor.FibreHom (finiteHilbertProjection (B := B) (S := S) (hS := hS)
      (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) P Q hP hQ g := by
    refine Functor.fibreHom_of_isHomLift_id hP hQ ?_
    refine CategoryTheory.IsHomLift.of_fac'
      (finiteHilbertProjection (B := B) (S := S) (hS := hS)
        (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) (𝟙 U) g hP' hQ' ?_
    change g.f = _
    rw [hgf, hfU, Category.id_comp]
    exact rfl
  refine ⟨g, ⟨hglift, hgiso, hg⟩, ?_⟩
  rintro ψ ⟨hψ, -, hψlocal⟩
  refine FiniteHilbert.Hom.ext_of_local_cocones t ν hνcover tij c e hν sq ?_ fun i => ?_
  · exact (FiniteHilbert.Hom.f_eq_of_fibreHom hP' hQ' ψ hψ).trans (hgf.trans hfU).symm
  · exact (hψlocal i).trans (hg i).symm

end AlgebraicGeometry.Stack

end
