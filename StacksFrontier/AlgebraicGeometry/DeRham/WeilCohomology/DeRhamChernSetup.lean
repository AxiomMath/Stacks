module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.EvenDegreeBundleFormula
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.PicardFirstChernClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacterUniqueness

/-!
# Even-degree de Rham cohomology as the functor `A` of Section 45.12

Let `𝒞` be a category of schemes over a base scheme `S`, presented by a functor `T : 𝒞 ⥤ Sch/S`.
The proofs of Lemmas 0FW9 and 0FWB in the Stacks project apply the discussion of Weil Cohomology
Theories, Section 45.12 (Tag 0FI4) to

`A(X) = ⨁_{i ≥ 0} H^{2i}_{dR}(X/S)`,

graded by `A^i(X) = H^{2i}_{dR}(X/S)`, with pullback along morphisms over `S` (Section 0FL6), the
cup product (Section 0FM1) and the de Rham first Chern class `c₁^{dR} : Pic(X) ⟶ H^2_{dR}(X/S)`
(Section 0FLE). This file assembles those data for an arbitrary such `T` and proves the axioms of
the section that hold for every `T`:

* `A(X)` is a commutative graded ring and pullback is a functorial graded ring homomorphism;
* the first Chern class lands in degree one and is central (axiom (1), via Tag 0FM3);
* the first Chern class commutes with pullback (axiom (3), via Tag 0FMD);
* the even-degree projective bundle formula (axiom (4)) follows from the degreewise one of
  Proposition 0FMT.

Given the projective bundles of clause (3)(a) and the bundle formula, they form a
`Stacks.WeilCohomology.ChernSetup` (`Stacks.DeRhamChern.chernSetup`), on which the properties of a
Chern character in the sense of Tag 0FI9 are the de Rham ones of Tag 0FWB
(`Stacks.DeRhamChern.isChernCharacterOnLocallyFree_chernSetup_iff`). Over `S = Spec 𝐐` every
`A(X)` is a `𝐐`-algebra with `𝐐 ⊆ A^0(X)`.

## Main definitions

* `Stacks.DeRhamChern.pull`: the graded ring homomorphism `f^* : A(Y) ⟶ A(X)`.
* `Stacks.DeRhamChern.c₁`: `c₁^{dR} : Pic(X) ⟶ A^1(X) = H^2_{dR}(X/S)`.
* `Stacks.DeRhamChern.chernSetup`: the standing situation of Section 45.12 for `A`.
* `Stacks.DeRhamChern.IsDeRhamChernCharacter`: the three properties of Tag 0FWB.

## References

* [Stacks Project, Section 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
* [Stacks Project, Tag 0FWB](https://stacks.math.columbia.edu/tag/0FWB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.WeilCohomology Stacks.DeRhamBaseChange

universe u v₁ w

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

namespace Stacks.DeRhamChern

variable {S : Scheme.{u}} {C : Type w} [Category.{v₁} C] (T : C ⥤ Over S)

/-! ### Pullback -/

/-- **The pullback `f^* : ⨁ H^{2i}_{dR}(Y/S) ⟶ ⨁ H^{2i}_{dR}(X/S)`** of a morphism `f : X ⟶ Y` of
`𝒞`, a ring homomorphism: the pullback of the square `f ≫ (Y ⟶ S) = (X ⟶ S) ≫ 𝟙 S`. -/
def pull {X Y : C} (f : X ⟶ Y) : evenDeRhamRing (T.obj Y).hom →+* evenDeRhamRing (T.obj X).hom :=
  evenDeRhamPullback (T.map f).left (T.obj X).hom (T.obj Y).hom (𝟙 S)
    (by rw [Over.w, Category.comp_id])

/-- The pullback of a square depends only on its two morphisms. -/
theorem evenDeRhamPullback_congr {X X' S₀ S' : Scheme.{u}} {g'₁ g'₂ : X' ⟶ X} {g₁ g₂ : S' ⟶ S₀}
    (f' : X' ⟶ S') (f : X ⟶ S₀) (hg' : g'₁ = g'₂) (hg : g₁ = g₂) (w₁ : g'₁ ≫ f = f' ≫ g₁)
    (w₂ : g'₂ ≫ f = f' ≫ g₂) :
    evenDeRhamPullback g'₁ f' f g₁ w₁ = evenDeRhamPullback g'₂ f' f g₂ w₂ := by
  subst hg' hg
  rfl

/-- Pullback along an identity is the identity. -/
theorem pull_id (X : C) : pull T (𝟙 X) = RingHom.id _ :=
  (evenDeRhamPullback_congr _ _ (by rw [T.map_id, Over.id_left]) rfl _
    (by rw [Category.id_comp, Category.comp_id])).trans (evenDeRhamPullback_id _ _)

/-- Pullback is contravariantly functorial. -/
theorem pull_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull T (f ≫ g) = (pull T f).comp (pull T g) :=
  (evenDeRhamPullback_congr _ _ (by rw [T.map_comp, Over.comp_left]) (Category.comp_id _).symm _
    (by rw [Category.assoc, Over.w, Over.w, Category.comp_id, Category.comp_id])).trans
    (evenDeRhamPullback_comp _ _ _ _ _ _ _ _ _ _)

/-- Pullback preserves the grading. -/
theorem pull_mem_grade {X Y : C} (f : X ⟶ Y) (i : ℕ) {a : evenDeRhamRing (T.obj Y).hom}
    (ha : a ∈ AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _ i) :
    pull T f a ∈ AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _ i :=
  evenDeRhamPullback_mem_grade _ _ _ _ _ i ha

/-! ### The first Chern class -/

/-- **The first Chern class `c₁^{dR} : Pic(X) ⟶ A^1(X) = H^2_{dR}(X/S)`**, in the even-degree
ring. -/
def c₁ (X : C) : (T.obj X).left.picardGroup →+ evenDeRhamRing (T.obj X).hom :=
  (DirectSum.of _ 1).comp (deRhamFirstChernClassPicard (T.obj X).hom)

/-- The first Chern class lies in degree one. -/
theorem c₁_mem (X : C) (L : (T.obj X).left.picardGroup) :
    c₁ T X L ∈ AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _ 1 :=
  ⟨_, rfl⟩

/-- **Axiom (1): the first Chern class is central**, the even-degree ring being commutative
(Tag 0FM3). -/
theorem c₁_central (X : C) (L : (T.obj X).left.picardGroup) (a : evenDeRhamRing (T.obj X).hom) :
    c₁ T X L * a = a * c₁ T X L :=
  mul_comm _ _

/-- **Axiom (3): the first Chern class commutes with pullback**, `f^*c₁^{dR}(ℒ) = c₁^{dR}(f^*ℒ)`
(Tag 0FMD). -/
theorem pull_c₁ {X Y : C} (f : X ⟶ Y) (L : (T.obj Y).left.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (T.obj Y).left.presheaf
      (T.obj Y).left.ringCatSheaf.2 L) :
    pull T f (c₁ T Y (picardClassOf (T.obj Y).left L hL)) =
      c₁ T X (picardClassOf (T.obj X).left ((Scheme.Modules.pullback (T.map f).left).obj L)
        (isInvertible_pullback_obj (T.map f).left L hL)) := by
  rw [c₁, c₁, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, pull, evenDeRhamPullback_of]
  exact congrArg (DirectSum.of _ 1)
    (deRhamPullbackSquare_deRhamFirstChernClassPicard _ _ _ _ _ L hL)

/-! ### The projective bundle formula -/

/-- **Axiom (4) on the even-degree ring, from the degreewise projective bundle formula.** For a
morphism `p : P ⟶ X` of `𝒞` and a class `ℒ ∈ Pic(P)`, if in every even degree `2n` the map
`(a_i)_{i ≤ r} ↦ ∑_i c₁^{dR}(ℒ)^i ∪ p^*(a_i)`, `a_i ∈ H^{2n - 2i}_{dR}(X/S)`, is bijective, then
so is `(a_i)_{i ≤ r} ↦ ∑_i c₁^{dR}(ℒ)^i · p^*(a_i)` on `r + 1` copies of `A(X)`. -/
theorem bijective_bundleFormula_of_degreewise {P X : C} (p : P ⟶ X)
    (L : (T.obj P).left.picardGroup) (r : ℕ)
    (hdeg : ∀ n : ℕ, Function.Bijective
      (AlgebraicGeometry.SheafOfModules.degreewiseBundleFormula _ _ _ _
        (deRhamPullbackSquare (T.map p).left (T.obj P).hom (T.obj X).hom (𝟙 S)
          (by rw [Over.w, Category.comp_id]))
        (deRhamFirstChernClassPicard (T.obj P).hom L) (r + 1) n)) :
    Function.Bijective fun a : Fin (r + 1) → evenDeRhamRing (T.obj X).hom =>
      ∑ i : Fin (r + 1), c₁ T P L ^ (i : ℕ) * pull T p (a i) :=
  AlgebraicGeometry.SheafOfModules.bijective_evenDeRhamBundleFormula _ _ _ _ _
    (deRhamPullbackSquare_one _ _ _ _ _) (deRhamPullbackSquare_cup _ _ _ _ _) _ _
    (fun k hk => AlgebraicGeometry.SheafOfModules.subsingleton_deRhamCohomology_of_neg _ _ k hk)
    hdeg

/-! ### The standing situation of Section 45.12 -/

/-- **The standing situation of Section 45.12 for even-degree de Rham cohomology**, given the
projective bundles of clause (3)(a) and the projective bundle formula: `A(X) = ⨁ H^{2i}_{dR}(X/S)`
graded by `A^i = H^{2i}_{dR}`, pullback along the morphisms of `𝒞`, and `c₁^A = c₁^{dR}`. -/
def chernSetup
    (bundleDatum : ∀ (X : C) (E : ((T ⋙ Over.forget S).obj X).Modules) (r : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1) →
        BundleDatum (T ⋙ Over.forget S) X E r)
    (bijective_bundleFormula : ∀ (X : C) (E : ((T ⋙ Over.forget S).obj X).Modules) (r : ℕ)
      (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)),
      Function.Bijective fun a : Fin (r + 1) → evenDeRhamRing (T.obj X).hom =>
        ∑ i : Fin (r + 1),
          c₁ T (bundleDatum X E r hE).bundle (bundleDatum X E r hE).twistClass ^ (i : ℕ) *
            pull T (bundleDatum X E r hE).proj (a i)) :
    ChernSetup.{u, u, v₁, w} C (T ⋙ Over.forget S) where
  A X := evenDeRhamRing (T.obj X).hom
  grade _ := AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _
  one_mem _ := AlgebraicGeometry.SheafOfModules.one_mem_evenDeRhamGrade _ _
  mul_mem _ i j _ _ ha hb := AlgebraicGeometry.SheafOfModules.mul_mem_evenDeRhamGrade _ _ i j ha hb
  pull f := pull T f
  pull_id X := pull_id T X
  pull_comp f g := pull_comp T f g
  pull_grade f i _ ha := pull_mem_grade T f i ha
  c₁ X := c₁ T X
  c₁_mem X L := c₁_mem T X L
  c₁_central X L a := c₁_central T X L a
  bundleDatum := bundleDatum
  bijective_bundleFormula := bijective_bundleFormula

/-! ### The properties of the de Rham Chern character -/

/-- **The three properties of the de Rham Chern character of Tag 0FWB.** A rule `ch` assigns to
every object `X` of `𝒞` and every class `α ∈ K₀(Vect(X))` the components
`ch X α n ∈ H^{2n}_{dR}(X/S)` of an element of `∏_{n ≥ 0} H^{2n}_{dR}(X/S)`, read in the
even-degree ring; and

1. `ch` is a ring map, the ring structure of `∏_n H^{2n}_{dR}(X/S)` being the componentwise sum
   and the convolution of cup products;
2. `f^* ∘ ch = ch ∘ f^*` for every morphism `f : X ⟶ Y` of `𝒞`, on all of `K₀(Vect(Y))`;
3. `ch([ℒ]) = exp(c₁^{dR}(ℒ))` for every invertible module `ℒ`, read coefficientwise:
   the component in degree `2n` is `c₁^{dR}(ℒ)^n / n!`. -/
structure IsDeRhamChernCharacter [∀ X : C, Algebra ℚ (evenDeRhamRing (T.obj X).hom)]
    (ch : ∀ X : C, VectorBundleKZero (T.obj X).left → ℕ → evenDeRhamRing (T.obj X).hom) :
    Prop where
  /-- The `n`-th component lies in `H^{2n}_{dR}(X/S)`. -/
  mem_grade : ∀ (X : C) (α : VectorBundleKZero (T.obj X).left) (n : ℕ),
    ch X α n ∈ AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _ n
  /-- **Property (1)**: `ch` is additive. -/
  map_add : ∀ (X : C) (α β : VectorBundleKZero (T.obj X).left) (n : ℕ),
    ch X (α + β) n = ch X α n + ch X β n
  /-- **Property (1)**: `ch` is multiplicative. -/
  map_mul : ∀ (X : C) (α β : VectorBundleKZero (T.obj X).left) (n : ℕ),
    ch X (α * β) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ch X α p.1 * ch X β p.2
  /-- **Property (1)**: `ch` sends `1 = [𝒪_X]` to `1`. -/
  map_one : ∀ (X : C) (n : ℕ), ch X 1 n = if n = 0 then 1 else 0
  /-- **Property (2)**: `f^* ∘ ch = ch ∘ f^*` on `K₀(Vect(Y))`, for the pullback homomorphism
  `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom` of `K₀(Vect(-))`. -/
  map_pull : ∀ {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (T.obj Y).left) (n : ℕ),
    pull T f (ch Y α n) = ch X (VectorBundleKZero.pullbackRingHom (T.map f).left α) n
  /-- **Property (3)**: `ch([ℒ]) = exp(c₁^{dR}(ℒ))`. -/
  invertible : ∀ (X : C) (L : (T.obj X).left.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (T.obj X).left.presheaf
      (T.obj X).left.ringCatSheaf.2 L) (n : ℕ),
    ch X (VectorBundleKZero.classOf (T.obj X).left L) n =
      algebraMap ℚ (evenDeRhamRing (T.obj X).hom) ((n.factorial : ℚ)⁻¹) *
        c₁ T X (picardClassOf (T.obj X).left L hL) ^ n

/-- **On the standing situation of even-degree de Rham cohomology, a Chern character in the sense
of Tag 0FI9 is a de Rham Chern character in the sense of Tag 0FWB.** Property (2) is read on the
classes of finite locally free modules on the left and on all of `K₀(Vect(-))` on the right; the
two agree because those classes generate. -/
theorem isChernCharacterOnLocallyFree_chernSetup_iff
    [hQ : ∀ X : C, Algebra ℚ (evenDeRhamRing (T.obj X).hom)] (bundleDatum bijective_bundleFormula)
    (ch : ∀ X : C, VectorBundleKZero (T.obj X).left → ℕ → evenDeRhamRing (T.obj X).hom) :
    @IsChernCharacterOnLocallyFree _ _ _ (chernSetup T bundleDatum bijective_bundleFormula) hQ ch ↔
      IsDeRhamChernCharacter T ch := by
  let : ∀ X : C, Algebra ℚ ((chernSetup T bundleDatum bijective_bundleFormula).A X) := hQ
  exact ⟨fun h =>
    { mem_grade := h.mem_grade
      map_add := h.map_add
      map_mul := h.map_mul
      map_one := h.map_one
      map_pull := fun f α n => h.map_pull_kzero f α n
      invertible := h.invertible },
    fun h =>
    { mem_grade := h.mem_grade
      map_add := h.map_add
      map_mul := h.map_mul
      map_one := h.map_one
      map_pull := fun f E hE n => (h.map_pull f (VectorBundleKZero.classOf _ E) n).trans
        (congrArg (fun β => ch _ β n)
          (VectorBundleKZero.pullbackRingHom_classOf (T.map f).left E hE))
      invertible := h.invertible }⟩

/-! ### Rational coefficients -/

/-- **Over `Spec 𝐐`, even-degree de Rham cohomology is a `𝐐`-algebra**: through
`𝐐 = Γ(Spec 𝐐, 𝒪) ⟶ Γ(X, p^{-1}𝒪_{Spec 𝐐})` and the unit `1 ∈ H^0_{dR}(X/𝐐)`. -/
instance algebraRat {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℚ)) :
    Algebra ℚ (evenDeRhamRing p) :=
  RingHom.toAlgebra
    ((AlgebraicGeometry.SheafOfModules.evenDeRhamAlgebraMap _ _).comp
      ((Scheme.Hom.inverseImageGlobalSections p).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom))

/-- **The rationals lie in degree zero**: `𝐐 ⊆ H^0_{dR}(X/𝐐) = A^0(X)`. -/
theorem algebraMap_rat_mem_grade_zero {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℚ))
    (q : ℚ) :
    algebraMap ℚ (evenDeRhamRing p) q ∈ AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _ 0 :=
  AlgebraicGeometry.SheafOfModules.evenDeRhamAlgebraMap_mem_grade_zero _ _ _

end Stacks.DeRhamChern
