module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# Exactness tested on hom-groups

An abelian category's exactness is detected by the hom-functors, in both directions that an
argument of the shape "apply `Hom(-, I)` to a resolution, with `I` injective" needs.

In one direction, `Hom(-, I)` is exact for an injective `I`, so it carries an exact short complex
to an exact sequence of abelian groups (as a `Function.Exact` of the two precomposition maps).

In the other, a complex `X₁ ⟶ X₂ ⟶ X₃` is exact as soon as `Hom(T, -)` of it is exact for every
`T`. That `Hom(T, -)` is only left exact is no obstruction here: taking `T` to be the kernel of
the second map produces the factorisation of that kernel through the first map, which is
exactness.

Between the two sits the transposition step. For a pair of adjunctions and a 2-cell between the
right adjoints, precomposing with the conjugate of that 2-cell corresponds, under the hom-set
bijections, to postcomposing with the 2-cell; so the hom-exactness of a complex built from
2-cells between right adjoints is the hom-exactness of the complex built from their conjugates
between the left adjoints.

## Main results

* `Stacks.CategoryTheory.ExactOnHom.function_exact_hom_of_exact`: `Hom(-, I)` of an exact short
  complex is exact when `I` is injective.
* `Stacks.CategoryTheory.ExactOnHom.exact_of_forall_function_exact`: a complex is exact at its
  middle term as soon as `Hom(T, -)` of it is exact for every `T`.
* `Stacks.CategoryTheory.ExactOnHom.function_exact_congr` and `.function_exact_congr_symm`:
  transporting the exactness of a pair of maps of types along bijections commuting with them.
* `Stacks.CategoryTheory.ExactOnHom.function_exact_of_conjugate`: the hom-exactness of a pair of
  2-cells between right adjoints follows from that of their conjugates between the left
  adjoints.
* `Stacks.CategoryTheory.ExactOnHom.additive_of_adjunction`: a left adjoint between preadditive
  categories with binary biproducts is additive.

## Implementation notes

`Function.Exact f g` is the statement that the fibre of `g` over zero is the image of `f`, which
for maps of hom-groups is exactness of the sequence of abelian groups; it is used rather than a
`ShortComplex` of `AddCommGrpCat` so that no additive structure has to be carried through the
adjunction bijections, only the vanishing of zero, which the caller supplies.

## References

* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂ v u

namespace Stacks.CategoryTheory.ExactOnHom

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **`Hom(-, I)` is exact for an injective `I`.** Applied to an exact short complex it gives an
exact sequence of hom-groups: a morphism out of the middle term killing the first map descends
along the second, because the short complex is exact and the target is injective. -/
theorem function_exact_hom_of_exact (T : ShortComplex C) (hT : T.Exact) {I : C} [Injective I] :
    Function.Exact (fun h : T.X₃ ⟶ I => T.g ≫ h) (fun h : T.X₂ ⟶ I => T.f ≫ h) := by
  intro h
  constructor
  · intro hh
    exact ⟨hT.descToInjective h hh, hT.comp_descToInjective h hh⟩
  · rintro ⟨h', rfl⟩
    simp

/-- **Exactness is detected by the hom-functors.** A complex `X₁ ⟶ X₂ ⟶ X₃` is exact at `X₂` as
soon as, for every object `T`, the two precomposition maps on hom-groups out of `T` are exact.
Taking `T` to be the kernel of the second map factors that kernel through the first, which splits
the comparison of the first map with the kernel and so makes it epimorphic. -/
theorem exact_of_forall_function_exact {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hfg : f ≫ g = 0)
    (h : ∀ T : C, Function.Exact (fun k : T ⟶ X₁ => k ≫ f) (fun k : T ⟶ X₂ => k ≫ g)) :
    (ShortComplex.mk f g hfg).Exact := by
  obtain ⟨q, hq⟩ := (h (kernel g) (kernel.ι g)).mp (kernel.condition g)
  have hsplit : q ≫ kernel.lift g f hfg = 𝟙 (kernel g) :=
    (cancel_mono (kernel.ι g)).1 (by simpa using hq)
  exact (ShortComplex.mk f g hfg).exact_iff_epi_kernel_lift.2 (SplitEpi.mk q hsplit).epi

end Abelian

section Transport

variable {A B C A' B' C' : Type*}
  [Zero A] [Zero B] [Zero C] [Zero A'] [Zero B'] [Zero C']

omit [Zero A] [Zero B] [Zero A'] [Zero B'] in
/-- Exactness of a pair of maps transports backwards along bijections commuting with them. -/
theorem function_exact_congr (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃ C')
    (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
    (heC : eC 0 = 0) (hf : ∀ a, eB (f a) = f' (eA a)) (hg : ∀ b, eC (g b) = g' (eB b))
    (hExact : Function.Exact f' g') : Function.Exact f g := by
  intro b
  constructor
  · intro hgb
    obtain ⟨a', ha'⟩ := (hExact _).mp (by rw [← hg, hgb, heC])
    exact ⟨eA.symm a', eB.injective (by rw [hf, Equiv.apply_symm_apply, ha'])⟩
  · rintro ⟨a, rfl⟩
    exact eC.injective (by rw [hg, hf, (hExact (f' (eA a))).mpr ⟨eA a, rfl⟩, heC])

omit [Zero A] [Zero B] [Zero A'] [Zero B'] in
/-- Exactness of a pair of maps transports forwards along bijections commuting with them. -/
theorem function_exact_congr_symm (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃ C')
    (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C')
    (heC : eC 0 = 0) (hf : ∀ a, eB (f a) = f' (eA a)) (hg : ∀ b, eC (g b) = g' (eB b))
    (hExact : Function.Exact f g) : Function.Exact f' g' := by
  refine function_exact_congr eA.symm eB.symm eC.symm f' g' f g
    (eC.symm_apply_eq.mpr heC.symm) (fun a => eB.injective ?_) (fun b => eC.injective ?_) hExact
  · simpa using (hf (eA.symm a)).symm
  · simpa using (hg (eB.symm b)).symm

end Transport

section Adjunction

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- A left adjoint between preadditive categories with binary biproducts is additive: it
preserves colimits, hence binary coproducts, hence binary biproducts. -/
theorem additive_of_adjunction [Preadditive A] [Preadditive B]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) : L.Additive := by
  let : L.IsLeftAdjoint := adj.isLeftAdjoint
  let : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
  let : PreservesColimitsOfShape (Discrete WalkingPair) L := inferInstance
  let : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  exact Functor.additive_of_preservesBinaryBiproducts L

variable [Preadditive A] [Preadditive B]
  {L₀ L₁ L₂ : A ⥤ B} {R₀ R₁ R₂ : B ⥤ A}

omit [Preadditive A] [Preadditive B] in
/-- The conjugate of a 2-cell between right adjoints, evaluated at an object: the transpose of
the unit followed by the 2-cell. This is what makes the conjugate additive in the 2-cell. -/
theorem conjugateEquiv_symm_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (t : R₁ ⟶ R₂) (X : A) :
    ((conjugateEquiv adj₁ adj₂).symm t).app X =
      (adj₂.homEquiv X (L₁.obj X)).symm (adj₁.unit.app X ≫ t.app (L₁.obj X)) := by
  refine ((adj₂.homEquiv X (L₁.obj X)).eq_symm_apply).mpr ?_
  refine Eq.trans (congrArg (adj₂.homEquiv X (L₁.obj X)) (Category.comp_id _).symm) ?_
  refine Eq.trans (Stacks.CategoryTheory.homEquiv_conjugate adj₁ adj₂ t
    (𝟙 (L₁.obj X))) ?_
  rw [Adjunction.homEquiv_id]

/-- Conjugating a finite sum of 2-cells between right adjoints is the sum of the conjugates. -/
theorem conjugateEquiv_symm_app_sum [L₂.Additive] (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {ι : Type*} (s : Finset ι) (α : ι → (R₁ ⟶ R₂)) (X : A) :
    ((conjugateEquiv adj₁ adj₂).symm (∑ i ∈ s, α i)).app X =
      ∑ i ∈ s, ((conjugateEquiv adj₁ adj₂).symm (α i)).app X := by
  simp only [conjugateEquiv_symm_app, NatTrans.app_sum, Preadditive.comp_sum]
  exact map_sum (adj₂.homAddEquiv X (L₁.obj X)).symm _ _

/-- Conjugating an integer multiple of a 2-cell between right adjoints. -/
theorem conjugateEquiv_symm_app_zsmul [L₂.Additive] (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (r : ℤ) (α : R₁ ⟶ R₂) (X : A) :
    ((conjugateEquiv adj₁ adj₂).symm (r • α)).app X =
      r • ((conjugateEquiv adj₁ adj₂).symm α).app X := by
  simp only [conjugateEquiv_symm_app, NatTrans.app_zsmul, Preadditive.comp_zsmul]
  exact map_zsmul (adj₂.homAddEquiv X (L₁.obj X)).symm _ _

/-- **The transposition step.** If the two conjugates, between the left adjoints, of a pair of
2-cells between right adjoints are exact on the hom-groups out of `L₀ X`, `L₁ X` into `Y`, then
the 2-cells themselves are exact on the hom-groups from `X` into `R₀ Y`, `R₁ Y`: the hom-set
bijections of the three adjunctions carry one pair of maps to the other. -/
theorem function_exact_of_conjugate [L₂.Additive]
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α₀₁ : R₀ ⟶ R₁) (α₁₂ : R₁ ⟶ R₂) (X : A) (Y : B)
    (hExact : Function.Exact
      (fun h : L₀.obj X ⟶ Y => ((conjugateEquiv adj₀ adj₁).symm α₀₁).app X ≫ h)
      (fun h : L₁.obj X ⟶ Y => ((conjugateEquiv adj₁ adj₂).symm α₁₂).app X ≫ h)) :
    Function.Exact (fun h : X ⟶ R₀.obj Y => h ≫ α₀₁.app Y)
      (fun h : X ⟶ R₁.obj Y => h ≫ α₁₂.app Y) := by
  refine function_exact_congr (adj₀.homEquiv X Y).symm (adj₁.homEquiv X Y).symm
    (adj₂.homEquiv X Y).symm _ _ _ _ ?_ (fun h => ?_) (fun h => ?_) hExact
  · simp [Adjunction.homEquiv_counit]
  all_goals
    refine (Equiv.symm_apply_eq _).mpr ?_
    rw [Stacks.CategoryTheory.homEquiv_conjugate, Equiv.apply_symm_apply]

end Adjunction

end Stacks.CategoryTheory.ExactOnHom

end
