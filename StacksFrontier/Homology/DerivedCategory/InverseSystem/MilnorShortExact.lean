module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit

/-!
# The Milnor short exact sequence for the cohomology of a derived limit

Let `A` be an abelian category with exact countable products and countable inverse limits, and
let `(Xₙ)` be an inverse system in `D(A)` with derived limit `K`, so that `K` sits in a
distinguished triangle `K → ∏ Xₙ → ∏ Xₙ → K⟦1⟧` whose middle map is the difference map
`1 - shift`. Its long exact cohomology sequence breaks into short exact sequences: in each degree
`r` the cohomology `Hʳ(K)` is squeezed between the cokernel of `1 - shift` on
`∏ H^{r-1}(Xₙ)` — the first derived inverse limit `R¹lim H^{r-1}(Xₙ)` — and the inverse limit
`lim Hʳ(Xₙ)`.

Two auxiliary facts about countable inverse limits come first: the limit projections form a
kernel fork of `1 - shift` on the product, and that fork is a limit. Together they identify
`lim` with `ker (1 - shift)`, which is what turns the long exact sequence into the stated short
exact sequence.

## Main definitions

* `CategoryTheory.Limits.inverseSystemLimitKernelFork`: the limit projections as a kernel fork of
  the difference map on the product.
* `CategoryTheory.Limits.inverseSystemLimitKernelForkIsLimit`: that fork is a limit, i.e. the
  inverse limit of a countable system is the kernel of `1 - shift`.

## Main results

* `DerivedCategory.isDerivedLimit_homology_shortExact`: the canonical Milnor short exact sequence
  for the cohomology of a derived limit.

## Implementation notes

The statement is about an arbitrary `CategoryTheory.Pretriangulated.IsDerivedLimit`, so it does
not depend on any choice of right-derived inverse-limit functor. The inclusion is obtained by
descending the connecting morphism of the triangle through the cokernel of the degree-`(r-1)`
difference map, and the projection to the inverse limit is characterized by its composites with
the limit projections; both characterizations are part of the conclusion, so the maps are pinned
rather than merely asserted to exist.

This module supplies the declarations that PR901 added to the end of its own derived-limits
support file and that the corresponding conceptual module in main does not yet carry.

Two short technical lemmas about `piComparison` are restated here as `private` because they are
`private` in `StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits`, where PR901's copy of
this material sat next to them. The cleaner end state is for these three declarations to move
into that module and reuse its copies; that file is in the derived-category seam shared by
several clusters, so the move is left to the final integrator.

## References

* [The Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [The Stacks Project, Tag 07KZ](https://stacks.math.columbia.edu/tag/07KZ)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive

/-! ### Cohomology of a derived limit -/

namespace CategoryTheory.Limits

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- The inverse-limit projections define a kernel fork of `1 - shift` on the product. -/
public noncomputable def inverseSystemLimitKernelFork (F : ℕᵒᵖ ⥤ A)
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] [HasLimit F] :
    KernelFork (Pi.lift fun n : ℕ =>
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) :=
  KernelFork.ofι (Pi.lift fun n : ℕ => limit.π F ⟨n⟩)
    (Pi.hom_ext _ _ fun n => by simp [Preadditive.comp_sub, limit.w])

/-- The inverse limit of a countable system is the kernel of `1 - shift`. -/
public noncomputable def inverseSystemLimitKernelForkIsLimit (F : ℕᵒᵖ ⥤ A)
    [HasProduct fun n : ℕ => F.obj ⟨n⟩] [HasLimit F] :
    IsLimit (inverseSystemLimitKernelFork F) := by
  let δ : (∏ᶜ fun n : ℕ => F.obj ⟨n⟩) ⟶ ∏ᶜ fun n : ℕ => F.obj ⟨n⟩ := Pi.lift fun n : ℕ =>
    Pi.π (fun n : ℕ => F.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let coneOf {W : A} (g : W ⟶ ∏ᶜ fun n : ℕ => F.obj ⟨n⟩) (hg : g ≫ δ = 0) : Cone F :=
    { pt := W
      π := NatTrans.ofOpSequence (fun n => g ≫ Pi.π _ n) (fun n => by
        have h := congrArg (fun f => f ≫ Pi.π (fun n : ℕ => F.obj ⟨n⟩) n) hg
        simp only [δ, Category.assoc, Pi.lift_π, Preadditive.comp_sub, zero_comp] at h
        simpa using (sub_eq_zero.mp h)) }
  have hπ : ∀ {W : A} (g : W ⟶ ∏ᶜ fun n : ℕ => F.obj ⟨n⟩) (hg : g ≫ δ = 0) (n : ℕᵒᵖ),
      (coneOf g hg).π.app n = g ≫ Pi.π _ n.unop := fun g hg n => by
    simp [coneOf]
  have hι : Pi.lift (fun n : ℕ => limit.π F ⟨n⟩) ≫ δ = 0 :=
    Pi.hom_ext _ _ fun n => by simp [δ, Preadditive.comp_sub, limit.w]
  exact KernelFork.IsLimit.ofι _ hι (fun g hg => limit.lift F (coneOf g hg))
    (fun g hg => Pi.hom_ext _ _ fun n => by
      rw [Category.assoc, Pi.lift_π, limit.lift_π, hπ g hg])
    (fun g hg m hm => limit.hom_ext fun n => by
      rw [limit.lift_π, hπ g hg, ← hm, Category.assoc, Pi.lift_π])

/-- An inverse limit of zero objects is zero. -/
public lemma isZero_limit_of_forall_isZero {C : Type*} [Category* C] {J : Type*} [Category* J]
    [HasZeroMorphisms C] (G : J ⥤ C) [HasLimit G] (hG : ∀ j, IsZero (G.obj j)) :
    IsZero (limit G) := by
  rw [IsZero.iff_id_eq_zero]
  exact limit.hom_ext fun j ↦ (hG j).eq_of_tgt _ _

/-- The cokernel of an endomorphism of a zero object is zero. -/
public lemma isZero_cokernel_of_isZero {C : Type*} [Category* C] [HasZeroMorphisms C] {P : C}
    (hP : IsZero P) (d : P ⟶ P) [HasCokernel d] : IsZero (cokernel d) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (cokernel.π d), hP.eq_of_src (cokernel.π d) 0]
  simp

/-- The middle term of a short exact sequence whose outer terms are zero is zero. -/
public lemma isZero_X₂_of_shortExact {C : Type*} [Category* C] [Abelian C] {S : ShortComplex C}
    (hS : S.ShortExact) (h₁ : IsZero S.X₁) (h₃ : IsZero S.X₃) : IsZero S.X₂ :=
  hS.exact.isZero_X₂ (h₁.eq_zero_of_src _) (h₃.eq_zero_of_tgt _)

/-- The map induced from `coker f` to `ker h` by a composable `c ≫ g = 0` is zero. -/
private lemma cokernelDesc_comp_kernelLift {C : Type*} [Category* C] [Preadditive C]
    {X₁ X₂ X₃ X₄ X₅ : C} {f : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {g : X₃ ⟶ X₄} {h : X₄ ⟶ X₅}
    [HasCokernel f] [HasKernel h] (hfc : f ≫ c = 0) (hcg : c ≫ g = 0) (hgh : g ≫ h = 0) :
    cokernel.desc f c hfc ≫ kernel.lift h g hgh = 0 := by
  rw [← cancel_epi (cokernel.π f), ← cancel_mono (kernel.ι h)]
  simp [hcg]

/-- For an exact sequence `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₄ ⟶ X₅`, the induced sequence
`0 ⟶ coker f ⟶ X₃ ⟶ ker h ⟶ 0` is short exact. -/
private lemma shortExact_cokernelDesc_kernelLift {C : Type*} [Category* C] [Abelian C]
    {X₁ X₂ X₃ X₄ X₅ : C} {f : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {g : X₃ ⟶ X₄} {h : X₄ ⟶ X₅}
    (hfc : f ≫ c = 0) (hcg : c ≫ g = 0) (hgh : g ≫ h = 0)
    (h₁ : (ShortComplex.mk f c hfc).Exact) (h₂ : (ShortComplex.mk c g hcg).Exact)
    (h₃ : (ShortComplex.mk g h hgh).Exact) :
    (ShortComplex.mk (cokernel.desc f c hfc) (kernel.lift h g hgh)
      (cokernelDesc_comp_kernelLift hfc hcg hgh)).ShortExact := by
  have := h₁.mono_cokernelDesc
  have := h₃.epi_kernelLift
  refine { exact := ?_ }
  let S := ShortComplex.mk (cokernel.desc f c hfc) g (by
    rw [← cancel_epi (cokernel.π f)]
    simp [hcg])
  let φ : ShortComplex.mk c g hcg ⟶ S :=
    { τ₁ := cokernel.π f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S]
      comm₂₃ := by simp [S] }
  let ψ : ShortComplex.mk (cokernel.desc f c hfc) (kernel.lift h g hgh)
      (cokernelDesc_comp_kernelLift hfc hcg hgh) ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι h
      comm₁₂ := by simp [S]
      comm₂₃ := by simp [S] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp h₂)

end CategoryTheory.Limits

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]

/-- **The Milnor short exact sequence of a presenting triangle.** For a distinguished triangle
`K ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ K[1]` whose middle map is `1 - shift`, the cohomology of `K` in degree `r`
sits in a short exact sequence between the cokernel of `1 - shift` on `∏ H^{r-1}(Fₙ)` and
`lim H^r(Fₙ)`, the projection being characterized by the given first map `a`. This is
`DerivedCategory.isDerivedLimit_homology_shortExact` with the presenting triangle fixed, so that
the projection is known in terms of `a`. -/
public theorem homology_shortExact_of_distinguished
    (F : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    (K : DerivedCategory A) (a : K ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (Opposite.op n))
    (b : (∏ᶜ fun n : ℕ ↦ F.obj (Opposite.op n)) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk a (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op)
      b ∈ distTriang (DerivedCategory A)) :
    let X : ℕ → DerivedCategory A := fun n ↦ F.obj (Opposite.op n)
    let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n : ℕ ↦
      Pi.π X n - Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    let T := Pretriangulated.Triangle.mk a d b
        ∀ r : ℤ,
          let H := DerivedCategory.homologyFunctor A r
          let H₁ := DerivedCategory.homologyFunctor A (r - 1)
          let homologySystem : ℕᵒᵖ ⥤ A := F ⋙ H
          let shiftedHomologySystem : ℕᵒᵖ ⥤ A := F ⋙ H₁
          let P : A :=
            ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)
          let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)) n -
              Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)) (n + 1) ≫
                shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
          ∃ (e : H₁.obj (∏ᶜ X) ≅ P)
            (i : cokernel δ ⟶ H.obj K) (q : H.obj K ⟶ limit homologySystem)
            (w : i ≫ q = 0),
            e.hom = piComparison H₁ X ∧
              cokernel.π δ ≫ i = e.inv ≫
                DerivedCategory.HomologySequence.δ T (r - 1) r ∧
              (∀ n : ℕ, q ≫ limit.π homologySystem (Opposite.op n) =
                H.map a ≫ H.map (Pi.π X n)) ∧
              (ShortComplex.mk i q w).ShortExact := by
  intro X d T r
  let H := homologyFunctor A r
  let H₁ := homologyFunctor A (r - 1)
  let δ₁ := Pi.lift fun n : ℕ => Pi.π (fun n => H₁.obj (X n)) n -
    Pi.π (fun n => H₁.obj (X n)) (n + 1) ≫ H₁.map (F.map (homOfLE (Nat.le_succ n)).op)
  let δ₀ := Pi.lift fun n : ℕ => Pi.π (fun n => H.obj (X n)) n -
    Pi.π (fun n => H.obj (X n)) (n + 1) ≫ H.map (F.map (homOfLE (Nat.le_succ n)).op)
  have := Stacks.DerivedProducts.hasProductsOfShape_derivedCategory (A := A) (I := ℕ)
  have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X (r - 1)
  have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X r
  let e₁ := asIso (piComparison H₁ X)
  let e₀ := asIso (piComparison H X)
  have hd₁ : H₁.map d ≫ e₁.hom = e₁.hom ≫ δ₁ :=
    CochainComplex.map_pi_lift_sub_comp_piComparison H₁ X _
  have hd₀ : H.map d ≫ e₀.hom = e₀.hom ≫ δ₀ :=
    CochainComplex.map_pi_lift_sub_comp_piComparison H X _
  let c := HomologySequence.δ T (r - 1) r
  have hc : δ₁ ≫ e₁.inv ≫ c = 0 := by
    rw [← cancel_epi e₁.hom, ← reassoc_of% hd₁, Iso.hom_inv_id_assoc, comp_zero]
    exact HomologySequence.comp_δ T hT (r - 1) r
  have hca : c ≫ H.map a = 0 := HomologySequence.δ_comp T hT (r - 1) r
  have ha : (H.map a ≫ e₀.hom) ≫ δ₀ = 0 := by
    rw [Category.assoc, ← hd₀, ← Category.assoc, ← H.map_comp,
      show a ≫ d = 0 from comp_distTriang_mor_zero₁₂ T hT, H.map_zero, zero_comp]
  let i := cokernel.desc δ₁ (e₁.inv ≫ c) hc
  let eLim : limit (F ⋙ H) ≅ kernel δ₀ :=
    (inverseSystemLimitKernelForkIsLimit (F ⋙ H)).conePointUniqueUpToIso (limit.isLimit _)
  let q := kernel.lift δ₀ (H.map a ≫ e₀.hom) ha ≫ eLim.inv
  have heLim : eLim.hom ≫ kernel.ι δ₀ = Pi.lift (fun n : ℕ => limit.π (F ⋙ H) ⟨n⟩) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have hq : q ≫ Pi.lift (fun n : ℕ => limit.π (F ⋙ H) ⟨n⟩) = H.map a ≫ e₀.hom := by
    rw [← heLim]
    simp [q]
  have hqn : ∀ n : ℕᵒᵖ, q ≫ limit.π (F ⋙ H) n = H.map a ≫ H.map (Pi.π X n.unop) := fun n => by
    simpa [e₀, X, Functor.comp_obj] using congrArg (· ≫ Pi.π (fun n => H.obj (X n)) n.unop) hq
  have hcg : (e₁.inv ≫ c) ≫ H.map a ≫ e₀.hom = 0 := by simp [reassoc_of% hca]
  have hiq : i ≫ q = 0 := by simp [i, q, ← Category.assoc, cokernelDesc_comp_kernelLift hc hcg ha]
  have hprev : (ShortComplex.mk δ₁ (e₁.inv ≫ c) hc).Exact := by
    refine ShortComplex.exact_of_iso ?_ (HomologySequence.exact₃ T hT (r - 1) r)
    exact ShortComplex.isoMk e₁ e₁ (Iso.refl _) (by simpa [T, H₁] using hd₁.symm) (by simp [c])
  have hmid : (ShortComplex.mk (e₁.inv ≫ c) (H.map a ≫ e₀.hom) hcg).Exact := by
    refine ShortComplex.exact_of_iso ?_ (HomologySequence.exact₁ T hT (r - 1) r)
    exact ShortComplex.isoMk e₁ (Iso.refl _) e₀ (by simp [c]) (by simp [T, H])
  have hcurr : (ShortComplex.mk (H.map a ≫ e₀.hom) δ₀ ha).Exact := by
    refine ShortComplex.exact_of_iso ?_ (HomologySequence.exact₂ T hT r)
    exact ShortComplex.isoMk (Iso.refl _) e₀ e₀ (by simp [T, H]) (by simpa [T, H] using hd₀.symm)
  refine ⟨e₁, i, q, hiq, rfl, cokernel.π_desc _ _ _, fun n => hqn ⟨n⟩, ?_⟩
  refine ShortComplex.shortExact_of_iso ?_
    (shortExact_cokernelDesc_kernelLift hc hcg ha hprev hmid hcurr)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) eLim.symm (by simp [i]) (by simp [q])


/-- The canonical Milnor short exact sequence of a derived limit. The inclusion descends the
connecting morphism through the cokernel of `1 - shift` in degree `r - 1`, and the projection to
the inverse limit is characterized by the maps to the degree-`r` cohomologies of the terms.

This is the direct long-exact-sequence argument of Stacks 07KY and 07KZ. It applies to every
`IsDerivedLimit`, independently of any choice of right-derived inverse-limit functor. -/
@[stacks 07KY]
public theorem isDerivedLimit_homology_shortExact
    (F : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    (K : DerivedCategory A) (hK : IsDerivedLimit F K) :
    let X : ℕ → DerivedCategory A := fun n ↦ F.obj (Opposite.op n)
    let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n : ℕ ↦
      Pi.π X n - Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : K ⟶ ∏ᶜ X) (b : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧),
      let T := Pretriangulated.Triangle.mk a d b
      T ∈ distTriang (DerivedCategory A) ∧
        ∀ r : ℤ,
          let H := DerivedCategory.homologyFunctor A r
          let H₁ := DerivedCategory.homologyFunctor A (r - 1)
          let homologySystem : ℕᵒᵖ ⥤ A := F ⋙ H
          let shiftedHomologySystem : ℕᵒᵖ ⥤ A := F ⋙ H₁
          let P : A :=
            ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)
          let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)) n -
              Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)) (n + 1) ≫
                shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
          ∃ (e : H₁.obj (∏ᶜ X) ≅ P)
            (i : cokernel δ ⟶ H.obj K) (q : H.obj K ⟶ limit homologySystem)
            (w : i ≫ q = 0),
            e.hom = piComparison H₁ X ∧
              cokernel.π δ ≫ i = e.inv ≫
                DerivedCategory.HomologySequence.δ T (r - 1) r ∧
              (∀ n : ℕ, q ≫ limit.π homologySystem (Opposite.op n) =
                H.map a ≫ H.map (Pi.π X n)) ∧
              (ShortComplex.mk i q w).ShortExact := by
  obtain ⟨a, b, hT⟩ := hK
  exact ⟨a, b, hT, homology_shortExact_of_distinguished F K a b hT⟩

end DerivedCategory

end
