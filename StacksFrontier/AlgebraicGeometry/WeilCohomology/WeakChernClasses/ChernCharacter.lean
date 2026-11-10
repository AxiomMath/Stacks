module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacterUniqueness
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.RankReduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.TotalChernClass

/-!
# The Chern character of a Weil cohomology theory, in the weak standing situation

The results of `StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacter`, stated
for `Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation
of Stacks Section 45.12 in which the projective bundle formula, condition (4), is only asked to be
injective and to resolve the top power `c₁^A(𝒪_P(1))^{r+1}` of the twist class (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`, which explains why Tag
0FIE needs this generality). The arguments are those of the original module, which use condition
(4) only through these two properties.

## References

* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **The three properties of Tag 0FI9's Chern character.** A rule `ch` assigns to every object
`X` of `𝒞` and every class `α` of `K₀(Vect(X))` the components `ch X α n` of its Chern
character, the `n`-th lying in `A^n(X)`; it is a ring map to `∏_{i ≥ 0} A^i(X)`, it is
compatible with pullback on the classes of modules, and it takes the value `exp(c₁^A(ℒ))` on an
invertible module. -/
structure IsChernCharacter (𝔚 : ChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔚.A X)]
    (ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X) : Prop where
  /-- The `n`-th component lies in `A^n(X)`, so that `ch` lands in `∏_{i ≥ 0} A^i(X)`. -/
  mem_grade : ∀ (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ), ch X α n ∈ 𝔚.grade X n
  /-- **Property (1).** `ch^A` is additive, the addition of `∏_{i ≥ 0} A^i(X)` being
  componentwise. -/
  map_add : ∀ (X : C) (α β : VectorBundleKZero (S.obj X)) (n : ℕ),
    ch X (α + β) n = ch X α n + ch X β n
  /-- **Property (1).** `ch^A` is multiplicative, the multiplication of `∏_{i ≥ 0} A^i(X)` being
  the convolution. -/
  map_mul : ∀ (X : C) (α β : VectorBundleKZero (S.obj X)) (n : ℕ),
    ch X (α * β) n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ch X α p.1 * ch X β p.2
  /-- **Property (1).** `ch^A` sends the unit `[𝒪_X]` of `K₀(Vect(X))` to the unit. -/
  map_one : ∀ (X : C) (n : ℕ), ch X 1 n = if n = 0 then 1 else 0
  /-- **Property (2).** `f^* ∘ ch^A = ch^A ∘ f^*`, on the class of a finite locally free
  module. Those classes generate `K₀(Vect(X))`, so this is the source's property (2); see
  `Stacks.WeilCohomology.IsChernCharacterOnLocallyFree.map_pull_kzero`. -/
  map_pull : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E → ∀ n : ℕ,
    𝔚.pull f (ch Y (VectorBundleKZero.classOf (S.obj Y) E) n) =
      ch X (VectorBundleKZero.classOf (S.obj X)
        ((Scheme.Modules.pullback (S.map f)).obj E)) n
  /-- **Property (3).** `ch^A([ℒ]) = exp(c₁^A(ℒ))` for an invertible module `ℒ`, read
  coefficientwise. -/
  invertible : ∀ (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (n : ℕ),
    ch X (VectorBundleKZero.classOf (S.obj X) L) n =
      algebraMap ℚ (𝔚.A X) ((n.factorial : ℚ)⁻¹) *
        𝔚.c₁ X (picardClassOf (S.obj X) L hL) ^ n

namespace IsChernCharacter

variable {𝔚 : ChernSetup.{u, v, v₁, w} C S} [∀ X : C, Algebra ℚ (𝔚.A X)]
  {ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X}

/-- The Chern character of the zero class vanishes in every degree. -/
theorem map_zero (h : IsChernCharacter 𝔚 ch) (X : C) (n : ℕ) : ch X 0 n = 0 := by
  simpa using h.map_add X 0 0 n

/-- **A Chern character is additive on a finite sum of classes**, componentwise. -/
theorem map_sum (h : IsChernCharacter 𝔚 ch) (X : C) {ι : Type*} (s : Finset ι)
    (α : ι → VectorBundleKZero (S.obj X)) (n : ℕ) :
    ch X (∑ i ∈ s, α i) n = ∑ i ∈ s, ch X (α i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_zero X n
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, h.map_add, ih, Finset.sum_insert ha]

/-- The degree-`n` component of a Chern character, as an additive map out of `K₀(Vect(X))`. -/
def componentHom (h : IsChernCharacter 𝔚 ch) (X : C) (n : ℕ) :
    VectorBundleKZero (S.obj X) →+ 𝔚.A X :=
  AddMonoidHom.mk' (fun α => ch X α n) fun α β => h.map_add X α β n

/-- The degree-`n` component homomorphism sends a class `α` to `ch X α n`. -/
@[simp] theorem componentHom_apply (h : IsChernCharacter 𝔚 ch) (X : C) (n : ℕ)
    (α : VectorBundleKZero (S.obj X)) : h.componentHom X n α = ch X α n := rfl

/-- **Property (2) of Tag 0FI9 in the source's own form**, `f^* ∘ ch^A = ch^A ∘ f^*` with the
right-hand `f^*` the induced ring map on `K₀(Vect(-))`, on all of `K₀(Vect(X))`.

The structure states property (2) on the generators `[ℰ]`, which is the form the source's own proof
uses. The pullback homomorphism of `K₀(Vect(-))` is not a hypothesis here: it is
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, whose defining property `f^*[ℰ] = [f^*ℰ]` is
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom_classOf` — the two together being
`AlgebraicGeometry.VectorBundleKZero.exists_pullback_ringHom`, which is exactly the datum Tags
0FEJ, 0FIA and 0FIC take as given. Read against it the two forms agree: both sides of the equation
are additive in `α` and the classes of the finite locally free modules generate `K₀(Vect(X))`. -/
theorem map_pull_kzero (h : IsChernCharacter 𝔚 ch)
    {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)) (n : ℕ) :
    𝔚.pull f (ch Y α n) = ch X (VectorBundleKZero.pullbackRingHom (S.map f) α) n := by
  refine DFunLike.congr_fun (VectorBundleKZero.addHom_ext
    (φ := (𝔚.pull f).toAddMonoidHom.comp (h.componentHom Y n))
    (ψ := (h.componentHom X n).comp
      (VectorBundleKZero.pullbackRingHom (S.map f)).toAddMonoidHom) fun E hE => ?_) α
  change 𝔚.pull f (ch Y (VectorBundleKZero.classOf (S.obj Y) E) n) =
    ch X (VectorBundleKZero.pullbackRingHom (S.map f) (VectorBundleKZero.classOf (S.obj Y) E)) n
  rw [VectorBundleKZero.pullbackRingHom_classOf (S.map f) E hE, h.map_pull f E hE n]

end IsChernCharacter

/-- **Two rules with the three properties of Tag 0FI9 agree on the class of a finite locally free
module of constant rank.** `eq_of_isChernCharacter'` removes the rank and reaches all of
`K₀(Vect(X))`.

The splitting principle of Tag 0FI7 supplies `p : P ⟶ X` with `p^*` injective on `A` and a
filtration of `p^*ℰ` with invertible successive quotients. That filtration writes `[p^*ℰ]` as a
sum of classes of invertible modules in `K₀(Vect(P))`, where additivity and the value on an
invertible module determine the Chern character; property (2) identifies the result with
`p^*ch^A([ℰ])`, and `p^*` is injective. -/
theorem eq_of_isChernCharacter {𝔚 : ChernSetup.{u, v, v₁, w} C S}
    [∀ X : C, Algebra ℚ (𝔚.A X)]
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X}
    (hch : IsChernCharacter 𝔚 ch) (hch' : IsChernCharacter 𝔚 ch') (X : C)
    (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (n : ℕ) :
    ch X (VectorBundleKZero.classOf (S.obj X) E) n =
      ch' X (VectorBundleKZero.classOf (S.obj X) E) n := by
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔚.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  have hEflf : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr
      hE.isFiniteLocallyFree
  refine hinj ?_
  rw [hch.map_pull p E hEflf n, hch'.map_pull p E hEflf n, hsum, hch.map_sum, hch'.map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [hch.invertible P (L j) (hL j) n, hch'.invertible P (L j) (hL j) n]

/-- **The uniqueness half of Stacks Tag 0FI9.** Properties (1), (2) and (3) determine the Chern
character on all of `K₀(Vect(X))`: any two rules with those properties are equal. This is
`eq_of_isChernCharacter` with the constant rank removed and the class an arbitrary element of
`K₀(Vect(X))`; that statement is kept as it stands for its existing consumers.

Three steps, described in the module documentation: the class of a module of constant rank, by
the splitting principle of Tag 0FI7; the class of an arbitrary finite locally free module, by
restriction to the pieces on which the rank is constant; and all of `K₀(Vect(X))`, those classes
generating it and both rules being additive. -/
theorem eq_of_isChernCharacter' {𝔚 : ChernSetup.{u, v, v₁, w} C S}
    [∀ X : C, Algebra ℚ (𝔚.A X)]
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔚.A X}
    (hch : IsChernCharacter 𝔚 ch) (hch' : IsChernCharacter 𝔚 ch') (X : C)
    (α : VectorBundleKZero (S.obj X)) (n : ℕ) :
    ch X α n = ch' X α n := by
  have hgen : ∀ (Y : C) (M : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
      ch Y (VectorBundleKZero.classOf (S.obj Y) M) n =
        ch' Y (VectorBundleKZero.classOf (S.obj Y) M) n := by
    intro Y M hM
    obtain ⟨ι, -, P, p, r, -, hr, hinj⟩ := 𝔚.exists_clopenRankPieces Y M
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp hM)
    refine hinj (funext fun i => ?_)
    dsimp only
    rw [hch.map_pull (p i) M hM n, hch'.map_pull (p i) M hM n]
    exact eq_of_isChernCharacter hch hch' (P i) _ (r i) (hr i) n
  exact DFunLike.congr_fun (VectorBundleKZero.addHom_ext
    (φ := hch.componentHom X n) (ψ := hch'.componentHom X n) fun M hM => hgen X M hM) α

end Stacks.WeilCohomology.Weak

end
