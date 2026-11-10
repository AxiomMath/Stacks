module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.CategoryTheory.Triangulated.HomFiveLemma
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.SurjectiveTowerDifference

/-!
# Maps out of a test object into the image of an inverse limit

Let `Φ : 𝒜' ⥤ 𝒜` be an additive functor between abelian categories and let `F : ℕᵒᵖ ⥤ 𝒜'` be an
inverse system. The comparison `Φ (lim F) ⟶ lim (Φ ∘ F)` is the first component of a morphism of
short complexes

`Φ (lim F) ⟶ Φ (∏ F_n) ⟶ Φ (∏ F_n)`  to  `lim (Φ ∘ F) ⟶ ∏ Φ F_n ⟶ ∏ Φ F_n`,

whose other two components are the comparison `Φ (∏ F_n) ⟶ ∏ Φ F_n`, the second maps being
`1 - shift`. When both rows are short exact they are distinguished triangles in `D(𝒜)` after
placing them in degree zero, and the five lemma for the homological functor `Hom(P, -)` gives:
if composition with the product comparison is bijective on morphisms out of every shift of an
object `P` of `D(𝒜)`, then so is composition with the limit comparison.

This is the shape of the proof of Stacks 0D3F: there `Φ = 𝒪_X ⊗_R -`, `F = (M_n)` has surjective
transition maps, the first row is exact because `Φ` is exact for `X` flat over `R`, the second
row is exact because the transition maps of `𝒪_X ⊗_R M_n` are surjective on affine étale charts,
and `P` is perfect.

## Main definitions

* `CategoryTheory.Limits.inverseLimitSequenceComparison`: the morphism of short complexes above.

## Main results

* `CategoryTheory.Limits.bijective_comp_single_limitComparison`: the five lemma statement.
* `CategoryTheory.Limits.bijective_comp_single_piComparison`: composition with the product
  comparison is bijective on maps out of `Y` once the derived product is the ordinary one and maps
  from `Y` into `Φ (∏ F_n)` are the families of maps into the `Φ F_n`.
* `CategoryTheory.Limits.shortExact_inverseLimitSequence_of_surjective`: for a tower of modules
  with surjective transition maps, `lim M_n ⟶ ∏ M_n ⟶ ∏ M_n` is short exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {𝒜' 𝒜 : Type*} [Category 𝒜'] [Category 𝒜]

/-- The product of the composite system `F ⋙ Φ` is the product of the images `Φ F_n`; the two
families are definitionally equal, but instance search does not see through the composite. -/
instance hasProduct_comp_obj (Φ : 𝒜' ⥤ 𝒜) (F : ℕᵒᵖ ⥤ 𝒜')
    [HasProduct fun n : ℕ => Φ.obj (F.obj ⟨n⟩)] : HasProduct fun n : ℕ => (F ⋙ Φ).obj ⟨n⟩ :=
  inferInstanceAs (HasProduct fun n : ℕ => Φ.obj (F.obj ⟨n⟩))

section Comparison

variable [Preadditive 𝒜'] [Preadditive 𝒜] (Φ : 𝒜' ⥤ 𝒜) [Φ.Additive] (F : ℕᵒᵖ ⥤ 𝒜')
  [HasProduct fun n : ℕ => F.obj ⟨n⟩] [HasLimit F]
  [HasProduct fun n : ℕ => Φ.obj (F.obj ⟨n⟩)] [HasLimit (F ⋙ Φ)]

/-- The morphism from the image under `Φ` of the sequence `lim F ⟶ ∏ F_n ⟶ ∏ F_n` to the
sequence `lim (Φ ∘ F) ⟶ ∏ Φ F_n ⟶ ∏ Φ F_n`: the limit comparison, then twice the product
comparison. -/
def inverseLimitSequenceComparison :
    Φ.mapShortComplex.obj (inverseLimitSequence F) ⟶ inverseLimitSequence (F ⋙ Φ) where
  τ₁ := limit.post F Φ
  τ₂ := piComparison Φ (fun n : ℕ => F.obj ⟨n⟩)
  τ₃ := piComparison Φ (fun n : ℕ => F.obj ⟨n⟩)
  comm₁₂ := by
    apply Pi.hom_ext
    intro n
    simp [inverseLimitSequence, inverseSystemLimitKernelFork]
  comm₂₃ := (map_inverseLimitSequence_g F Φ).symm

/-- The first component of `inverseLimitSequenceComparison Φ F` is the limit comparison
`limit.post F Φ`. -/
@[simp]
theorem inverseLimitSequenceComparison_τ₁ :
    (inverseLimitSequenceComparison Φ F).τ₁ = limit.post F Φ := rfl

/-- The second component of `inverseLimitSequenceComparison Φ F` is the product comparison of
`Φ` at the family `F_n`. -/
@[simp]
theorem inverseLimitSequenceComparison_τ₂ :
    (inverseLimitSequenceComparison Φ F).τ₂ = piComparison Φ (fun n : ℕ => F.obj ⟨n⟩) := rfl

/-- The third component of `inverseLimitSequenceComparison Φ F` is the product comparison of
`Φ` at the family `F_n`. -/
@[simp]
theorem inverseLimitSequenceComparison_τ₃ :
    (inverseLimitSequenceComparison Φ F).τ₃ = piComparison Φ (fun n : ℕ => F.obj ⟨n⟩) := rfl

end Comparison

section Derived

variable [Abelian 𝒜'] [Abelian 𝒜] [HasDerivedCategory 𝒜] (Φ : 𝒜' ⥤ 𝒜) [Φ.Additive]
  (F : ℕᵒᵖ ⥤ 𝒜') [HasProduct fun n : ℕ => F.obj ⟨n⟩] [HasLimit F]
  [HasProduct fun n : ℕ => Φ.obj (F.obj ⟨n⟩)] [HasLimit (F ⋙ Φ)]

/-- **Maps out of a test object into the image of an inverse limit.** Suppose that `Φ` carries
`lim F ⟶ ∏ F_n ⟶ ∏ F_n` to a short exact sequence, and that `lim (Φ ∘ F) ⟶ ∏ Φ F_n ⟶ ∏ Φ F_n`
is short exact. If composition with the product comparison `Φ (∏ F_n) ⟶ ∏ Φ F_n`, placed in
degree zero, is bijective on morphisms out of every shift of an object `P` of `D(𝒜)`, then so is
composition with the limit comparison `Φ (lim F) ⟶ lim (Φ ∘ F)`. -/
theorem bijective_comp_single_limitComparison
    (h₁ : (Φ.mapShortComplex.obj (inverseLimitSequence F)).ShortExact)
    (h₂ : (inverseLimitSequence (F ⋙ Φ)).ShortExact) (P : DerivedCategory 𝒜)
    (hP : ∀ k : ℤ, Function.Bijective
      (fun a : P⟦k⟧ ⟶ (DerivedCategory.singleFunctor 𝒜 0).obj (Φ.obj (∏ᶜ fun n : ℕ => F.obj ⟨n⟩)) =>
        a ≫ (DerivedCategory.singleFunctor 𝒜 0).map (piComparison Φ (fun n : ℕ => F.obj ⟨n⟩))))
    (k : ℤ) :
    Function.Bijective
      (fun a : P⟦k⟧ ⟶ (DerivedCategory.singleFunctor 𝒜 0).obj (Φ.obj (limit F)) =>
        a ≫ (DerivedCategory.singleFunctor 𝒜 0).map (limit.post F Φ)) :=
  Pretriangulated.bijective_comp_hom₁_of_forall_shift h₁.singleTriangle_distinguished
    h₂.singleTriangle_distinguished
    (ShortComplex.ShortExact.singleTriangle.map h₁ h₂ (inverseLimitSequenceComparison Φ F)) P hP
    hP k

omit [Abelian 𝒜'] [Φ.Additive] [HasLimit F] [HasLimit (F ⋙ Φ)] in
/-- **The product comparison on maps out of a test object.** Suppose that placing objects in
degree zero preserves the product `∏ Φ F_n`, so that `∏ Φ F_n` in degree zero is the product of the
`Φ F_n` in degree zero in `D(𝒜)`. If the maps from `Y` to `Φ (∏ F_n)` in degree zero are determined
by, and can be prescribed through, their composites with the images of the projections, then
composition with the product comparison `Φ (∏ F_n) ⟶ ∏ Φ F_n`, placed in degree zero, is bijective
on morphisms out of `Y`. -/
theorem bijective_comp_single_piComparison
    [PreservesLimit (Discrete.functor fun n : ℕ => Φ.obj (F.obj ⟨n⟩))
      (DerivedCategory.singleFunctor 𝒜 0)] (Y : DerivedCategory 𝒜)
    (hY : Function.Bijective
      (fun a : Y ⟶ (DerivedCategory.singleFunctor 𝒜 0).obj (Φ.obj (∏ᶜ fun n : ℕ => F.obj ⟨n⟩)) =>
        fun n : ℕ => a ≫ (DerivedCategory.singleFunctor 𝒜 0).map
          (Φ.map (Pi.π (fun n : ℕ => F.obj ⟨n⟩) n)))) :
    Function.Bijective
      (fun a : Y ⟶ (DerivedCategory.singleFunctor 𝒜 0).obj (Φ.obj (∏ᶜ fun n : ℕ => F.obj ⟨n⟩)) =>
        a ≫ (DerivedCategory.singleFunctor 𝒜 0).map (piComparison Φ (fun n : ℕ => F.obj ⟨n⟩))) := by
  set G := DerivedCategory.singleFunctor 𝒜 0
  have hl := isLimitFanMkObjOfIsLimit G _ (Pi.π fun n : ℕ => Φ.obj (F.obj ⟨n⟩))
    (productIsProduct fun n : ℕ => Φ.obj (F.obj ⟨n⟩))
  have he : Function.Bijective
      (fun b : Y ⟶ G.obj (∏ᶜ fun n : ℕ => Φ.obj (F.obj ⟨n⟩)) =>
        fun n : ℕ => b ≫ G.map (Pi.π (fun n : ℕ => Φ.obj (F.obj ⟨n⟩)) n)) :=
    ⟨fun b b' h => Fan.IsLimit.hom_ext hl _ _ fun n => congrFun h n,
      fun c => ⟨Fan.IsLimit.lift hl c, funext fun n => Fan.IsLimit.fac hl c n⟩⟩
  refine (Function.Bijective.of_comp_iff' he _).1 ?_
  convert hY using 1
  funext a n
  simp only [Function.comp_apply, Category.assoc, ← G.map_comp, piComparison_comp_π]

end Derived

section Modules

universe v u

/-- **A tower of modules with surjective transition maps.** The sequence
`0 ⟶ lim M_n ⟶ ∏ M_n ⟶ ∏ M_n ⟶ 0`, the second map being `1 - shift`, is short exact: the limit is
the kernel of `1 - shift` in any abelian category, and `1 - shift` is surjective because a preimage
can be built one transition map at a time. -/
theorem shortExact_inverseLimitSequence_of_surjective {R : Type u} [Ring R]
    (M : ℕᵒᵖ ⥤ ModuleCat.{v} R)
    (hsurj : ∀ n : ℕ, Function.Surjective (M.map (homOfLE (Nat.le_succ n)).op)) :
    (inverseLimitSequence M).ShortExact := by
  obtain ⟨hexact, hmono⟩ := inverseLimitSequence_exact_and_mono M
  refine { exact := hexact, mono_f := hmono, epi_g := ?_ }
  let X : ℕ → ModuleCat.{v} R := fun n => M.obj ⟨n⟩
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  obtain ⟨x, hx⟩ := Stacks.InverseSystem.surjective_pi_sub_shift
    (fun n => (M.map (homOfLE (Nat.le_succ n)).op : X (n + 1) → X n)) hsurj
    ((ModuleCat.piIsoPi X).hom y)
  refine ⟨(ModuleCat.piIsoPi X).inv x, ?_⟩
  apply (ModuleCat.piIsoPi X).toLinearEquiv.injective
  funext n
  change ((Pi.lift (fun n : ℕ => Pi.π X n - Pi.π X (n + 1) ≫ M.map (homOfLE (Nat.le_succ n)).op) ≫
    Pi.π X n) ((ModuleCat.piIsoPi X).inv x)) = _
  rw [Pi.lift_comp_π]
  change (Pi.π X n) ((ModuleCat.piIsoPi X).inv x) -
    (M.map (homOfLE (Nat.le_succ n)).op) ((Pi.π X (n + 1)) ((ModuleCat.piIsoPi X).inv x)) =
      (ModuleCat.piIsoPi X).hom y n
  rw [ModuleCat.piIsoPi_inv_kernel_ι_apply, ModuleCat.piIsoPi_inv_kernel_ι_apply]
  exact congrFun hx n

end Modules

end CategoryTheory.Limits

end
