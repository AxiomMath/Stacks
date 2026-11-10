module

public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroupPullback
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.ChernCharacter
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankReduction

/-!
# The Chern character of Tag 0FI9, with property (2) on finite locally free classes

`Stacks.WeilCohomology.IsChernCharacter` asks property (2), `f^*ch^A([ℰ]) = ch^A([f^*ℰ])`, for
every sheaf of modules `ℰ`; `Stacks.WeilCohomology.IsChernCharacterOnLocallyFree` asks it only on
the classes of finite locally free modules, which generate `K₀(Vect(X))`. The first predicate
implies the second (`Stacks.WeilCohomology.IsChernCharacter.isChernCharacterOnLocallyFree`).

The pullback homomorphism of `K₀(Vect(-))` is
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`, constructed from the universal property of
the Grothendieck ring (Tag 0FEM), with `f^*[ℰ] = [f^*ℰ]` as its defining property; read against it
the two forms of property (2) agree, both sides being additive.

## Main results

* `Stacks.WeilCohomology.IsChernCharacterOnLocallyFree.map_pull_kzero`: property (2) in the
  source's own form, on all of `K₀(Vect(X))`.
* `Stacks.WeilCohomology.eq_classOf_of_isChernCharacterOnLocallyFree`: two such rules agree on the
  class of a finite locally free module of constant rank.
* `Stacks.WeilCohomology.eq_of_isChernCharacterOnLocallyFree`: **the uniqueness half of Tag
  0FI9**, on all of `K₀(Vect(X))` and with no restriction on the rank.

## References

* [Stacks Project, Tag 0FI9](https://stacks.math.columbia.edu/tag/0FI9)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-- **The three properties of Tag 0FI9's Chern character, property (2) read on the classes of
finite locally free modules.** A rule `ch` assigns to every object
`X` of `𝒞` and every class `α` of `K₀(Vect(X))` the components `ch X α n` of its Chern
character, the `n`-th lying in `A^n(X)`; it is a ring map to `∏_{i ≥ 0} A^i(X)`, it is
compatible with pullback on the classes of modules, and it takes the value `exp(c₁^A(ℒ))` on an
invertible module. -/
structure IsChernCharacterOnLocallyFree (𝔄 : ChernSetup.{u, v, v₁, w} C S)
    [∀ X : C, Algebra ℚ (𝔄.A X)]
    (ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X) : Prop where
  /-- The `n`-th component lies in `A^n(X)`, so that `ch` lands in `∏_{i ≥ 0} A^i(X)`. -/
  mem_grade : ∀ (X : C) (α : VectorBundleKZero (S.obj X)) (n : ℕ), ch X α n ∈ 𝔄.grade X n
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
  module. -/
  map_pull : ∀ {X Y : C} (f : X ⟶ Y) (E : (S.obj Y).Modules),
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E → ∀ n : ℕ,
    𝔄.pull f (ch Y (VectorBundleKZero.classOf (S.obj Y) E) n) =
      ch X (VectorBundleKZero.classOf (S.obj X)
        ((Scheme.Modules.pullback (S.map f)).obj E)) n
  /-- **Property (3).** `ch^A([ℒ]) = exp(c₁^A(ℒ))` for an invertible module `ℒ`, read
  coefficientwise. -/
  invertible : ∀ (X : C) (L : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L) (n : ℕ),
    ch X (VectorBundleKZero.classOf (S.obj X) L) n =
      algebraMap ℚ (𝔄.A X) ((n.factorial : ℚ)⁻¹) *
        𝔄.c₁ X (picardClassOf (S.obj X) L hL) ^ n

/-- **A rule with the three properties of `Stacks.WeilCohomology.IsChernCharacter` has those of
`Stacks.WeilCohomology.IsChernCharacterOnLocallyFree`**: property (2) on the class of every module
gives it on the class of every finite locally free module. -/
theorem IsChernCharacter.isChernCharacterOnLocallyFree {𝔄 : ChernSetup.{u, v, v₁, w} C S}
    [∀ X : C, Algebra ℚ (𝔄.A X)] {ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (h : IsChernCharacter 𝔄 ch) : IsChernCharacterOnLocallyFree 𝔄 ch where
  mem_grade := h.mem_grade
  map_add := h.map_add
  map_mul := h.map_mul
  map_one := h.map_one
  map_pull f E _ n := h.map_pull f E n
  invertible := h.invertible

namespace IsChernCharacterOnLocallyFree

variable {𝔄 : ChernSetup.{u, v, v₁, w} C S} [∀ X : C, Algebra ℚ (𝔄.A X)]
  {ch : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}

/-- The Chern character of the zero class vanishes in every degree. -/
theorem map_zero (h : IsChernCharacterOnLocallyFree 𝔄 ch) (X : C) (n : ℕ) : ch X 0 n = 0 := by
  simpa using h.map_add X 0 0 n

/-- **A Chern character is additive on a finite sum of classes**, componentwise. -/
theorem map_sum (h : IsChernCharacterOnLocallyFree 𝔄 ch) (X : C) {ι : Type*} (s : Finset ι)
    (α : ι → VectorBundleKZero (S.obj X)) (n : ℕ) :
    ch X (∑ i ∈ s, α i) n = ∑ i ∈ s, ch X (α i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.map_zero X n
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, h.map_add, ih, Finset.sum_insert ha]

/-- The degree-`n` component of a Chern character, as an additive map out of `K₀(Vect(X))`. -/
def componentHom (h : IsChernCharacterOnLocallyFree 𝔄 ch) (X : C) (n : ℕ) :
    VectorBundleKZero (S.obj X) →+ 𝔄.A X :=
  AddMonoidHom.mk' (fun α => ch X α n) fun α β => h.map_add X α β n

/-- The degree-`n` component homomorphism sends `α` to `ch X α n`. -/
@[simp] theorem componentHom_apply (h : IsChernCharacterOnLocallyFree 𝔄 ch) (X : C) (n : ℕ)
    (α : VectorBundleKZero (S.obj X)) : h.componentHom X n α = ch X α n := rfl

/-- **Property (2) of Tag 0FI9 in the source's own form**, `f^* ∘ ch^A = ch^A ∘ f^*` with the
right-hand `f^*` the ring map `AlgebraicGeometry.VectorBundleKZero.pullbackRingHom` on
`K₀(Vect(-))`, on all of `K₀(Vect(X))`. -/
theorem map_pull_kzero (h : IsChernCharacterOnLocallyFree 𝔄 ch)
    {X Y : C} (f : X ⟶ Y) (α : VectorBundleKZero (S.obj Y)) (n : ℕ) :
    𝔄.pull f (ch Y α n) = ch X (VectorBundleKZero.pullbackRingHom (S.map f) α) n := by
  refine DFunLike.congr_fun (VectorBundleKZero.addHom_ext
    (φ := (𝔄.pull f).toAddMonoidHom.comp (h.componentHom Y n))
    (ψ := (h.componentHom X n).comp
      (VectorBundleKZero.pullbackRingHom (S.map f)).toAddMonoidHom) fun E hE => ?_) α
  change 𝔄.pull f (ch Y (VectorBundleKZero.classOf (S.obj Y) E) n) =
    ch X (VectorBundleKZero.pullbackRingHom (S.map f) (VectorBundleKZero.classOf (S.obj Y) E)) n
  rw [VectorBundleKZero.pullbackRingHom_classOf (S.map f) E hE, h.map_pull f E hE n]

end IsChernCharacterOnLocallyFree

/-- **Two rules with the three properties of Tag 0FI9 agree on the class of a finite locally free
module of constant rank.** -/
theorem eq_classOf_of_isChernCharacterOnLocallyFree {𝔄 : ChernSetup.{u, v, v₁, w} C S}
    [∀ X : C, Algebra ℚ (𝔄.A X)]
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hch : IsChernCharacterOnLocallyFree 𝔄 ch) (hch' : IsChernCharacterOnLocallyFree 𝔄 ch') (X : C)
    (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r) (n : ℕ) :
    ch X (VectorBundleKZero.classOf (S.obj X) E) n =
      ch' X (VectorBundleKZero.classOf (S.obj X) E) n := by
  obtain ⟨P, p, -, hinj, hfil⟩ :=
    𝔄.exists_injective_hasInvertibleFiltration X Unit (fun _ => E) (fun _ => r) fun _ => hE
  obtain ⟨-, L, hL, hsum⟩ := (hfil ()).exists_classOf_eq_sum
  have hEflf : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} E :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).mpr
      hE.isFiniteLocallyFree
  refine hinj ?_
  rw [hch.map_pull p E hEflf n, hch'.map_pull p E hEflf n, hsum, hch.map_sum, hch'.map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [hch.invertible P (L j) (hL j) n, hch'.invertible P (L j) (hL j) n]

/-- **The uniqueness half of Stacks Tag 0FI9.** Properties (1), (2) and (3) determine the Chern
character on all of `K₀(Vect(X))`: any two rules with those properties are equal. -/
@[stacks 0FI9 "uniqueness, on all of `K₀(Vect(X))` and with no restriction on the rank: two \
  rules with properties (1), (2) and (3) are equal. Property (2) is stated on the generators, \
  which `IsChernCharacterOnLocallyFree.map_pull_kzero` upgrades to the source's form, read \
  against the \
  CONSTRUCTED pullback homomorphism AlgebraicGeometry.VectorBundleKZero.pullbackRingHom of \
  `K₀(Vect(-))`"]
theorem eq_of_isChernCharacterOnLocallyFree {𝔄 : SourceChernSetup.{u, v, v₁, w} C S}
    [∀ X : C, Algebra ℚ (𝔄.A X)]
    {ch ch' : ∀ X : C, VectorBundleKZero (S.obj X) → ℕ → 𝔄.A X}
    (hch : IsChernCharacterOnLocallyFree 𝔄.toChernSetup ch)
    (hch' : IsChernCharacterOnLocallyFree 𝔄.toChernSetup ch') (X : C)
    (α : VectorBundleKZero (S.obj X)) (n : ℕ) :
    ch X α n = ch' X α n := by
  have hgen : ∀ (Y : C) (M : (S.obj Y).Modules),
      Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} M →
      ch Y (VectorBundleKZero.classOf (S.obj Y) M) n =
        ch' Y (VectorBundleKZero.classOf (S.obj Y) M) n := by
    intro Y M hM
    obtain ⟨ι, -, P, p, r, -, hr, hinj⟩ := 𝔄.exists_clopenRankPieces Y M
      ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry M).mp hM)
    refine hinj (funext fun i => ?_)
    dsimp only
    rw [hch.map_pull (p i) M hM n, hch'.map_pull (p i) M hM n]
    exact eq_classOf_of_isChernCharacterOnLocallyFree hch hch' (P i) _ (r i) (hr i) n
  exact DFunLike.congr_fun (VectorBundleKZero.addHom_ext
    (φ := hch.componentHom X n) (ψ := hch'.componentHom X n) fun M hM => hgen X M hM) α

end Stacks.WeilCohomology

end
