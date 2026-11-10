module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Homology.DerivedLinear
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsHypotheses

/-!
# The cohomology of a scheme is its own `I`-multiple when the `I`-quotient is acyclic

Let `X` be a quasi-compact quasi-separated scheme, `I` an ideal of the ring `Γ(X, ⊤)` of global
functions, `ℱ` a sheaf of `𝒪_X`-modules and

`ψ : ⨁_{a ∈ I} ℱ ⟶ ℱ`

the morphism assembled from multiplication by the elements of `I`, whose image is the subsheaf
`I ℱ` and whose cokernel is `ℱ / I ℱ`. This file proves that

* `Hᵖ(X, ψ)` is an epimorphism as soon as `Hᵖ(X, ℱ/Iℱ) = 0` and `Hᵖ⁺¹` vanishes on the kernel of
  `⨁_{a ∈ I} ℱ ⟶ Iℱ`, and
* in that case `Hᵖ(X, ℱ) = I · Hᵖ(X, ℱ)`.

The second statement is the step that the proof of [Stacks, Tag 02V7] takes with the theorem on
formal functions ([Stacks, Tag 02OD]): there the vanishing of `Hᵖ(X_n, ℱ_n)` on the
infinitesimal neighbourhoods of a fibre is converted into the vanishing of the completed stalk
`(Rᵖ f_* ℱ)^∧_y`, and Nakayama's lemma then kills the stalk itself. The route taken here reaches
`Hᵖ = I · Hᵖ` — which is what Nakayama consumes — from the acyclicity of the single quotient
`ℱ/Iℱ` together with one degree of vanishing on a kernel, with no completion, no inverse system
and no appeal to the theorem on formal functions. What it needs instead is the vanishing of
`Hᵖ⁺¹` on an auxiliary quasi-coherent module, which over an affine base is available for `p` at
least the length of a finite affine cover
(`AlgebraicGeometry.exists_isZero_rightDerived_moduleGlobalSections_of_isProper`) and hence by
descending induction on the degree.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.idealMultiples`: the morphism
  `⨁_{a ∈ I} ℱ ⟶ ℱ` assembled from multiplication by the elements of `I`.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `epi_map_rightDerived_f_of_isZero`: one window of the long exact sequence that this
  directory did not have — `Hᵖ(X, 𝒜) ⟶ Hᵖ(X, ℬ)` is an epimorphism when `Hᵖ(X, 𝒞) = 0`.
  (`exact_and_epi_map_rightDerived_of_isZero` is the other one, at the right-hand term.)
* `epi_map_rightDerived_idealMultiples`: `Hᵖ(X, ψ)` is an epimorphism.
* `eq_zero_of_forall_smul_eq_zero`: a morphism out of `Hᵖ(X, ℱ)` killed by every element of `I`
  vanishes.
* `top_le_smul_top_rightDerived`: hence `Hᵖ(X, ℱ) = I · Hᵖ(X, ℱ)`.
* `isZero_rightDerived_of_isZero_cokernel`: hence `Hᵖ(X, ℱ) = 0`, when the cohomology is finite
  over `Γ(X, ⊤)` and `I` lies in the Jacobson radical — the two hypotheses Nakayama's lemma
  makes.

## Implementation notes

**The `Γ(X, ⊤)`-linear structure.** `Stacks.Cohomology.AffineBase.moduleGlobalSections X` lands
in `ModuleCat Γ(X, ⊤)`, so a scalar `a ∈ Γ(X, ⊤)` acts on `Hᵖ(X, ℱ)`; that this action is the
image under `Hᵖ(X, -)` of multiplication by `a` on `ℱ` is exactly `Functor.Linear`, and it is
what identifies the image of `Hᵖ(X, ψ)` with `I · Hᵖ(X, ℱ)`. The linear structure on `X.Modules`
is `AlgebraicGeometry.Scheme.linearOfRingHom` at the identity of `Γ(X, ⊤)` — declared here as an
instance, which its source cannot do because there the base ring is arbitrary and so not
determined by the category — and the linearity of the derived functors is
`Stacks.DerivedLinear.rightDerived_linear`.

**The index type is the whole of `I`, not a generating set.** `Hᵖ(X, -)` commutes with arbitrary
direct sums on a quasi-compact quasi-separated scheme ([Stacks, Tag 01FF], here
`preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections`), so nothing is gained by
cutting `I` down to finitely many generators, and no Noetherian hypothesis is needed anywhere in
this file.

**The two short exact sequences.** `ψ` factors as `⨁_{a ∈ I} ℱ ⟶ Iℱ ⟶ ℱ` with
`Iℱ = ker(ℱ ⟶ ℱ/Iℱ)` the image, through `CategoryTheory.Abelian.factorThruImage`, which is an
epimorphism. The right-hand map is the kernel inclusion of the cokernel projection, and the two
sequences `0 → ker ⟶ ⨁ℱ ⟶ Iℱ → 0` and `0 → Iℱ ⟶ ℱ ⟶ ℱ/Iℱ → 0` give the two epimorphisms whose
composite is `Hᵖ(X, ψ)`.

**Nothing here is quasi-coherent and no morphism is in sight.** The statements are about an
arbitrary sheaf of modules on a quasi-compact quasi-separated scheme; the hypotheses on the
cokernel and on the kernel are what a geometric input has to supply.

## References

* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable (X : Scheme.{u})

/-- **Sheaves of modules on a scheme are linear over the ring of global functions.** This is
`AlgebraicGeometry.Scheme.linearOfRingHom` at the identity ring map of `Γ(X, ⊤)`; there the base
ring is arbitrary, hence not determined by the category and not an instance. -/
instance linear_modules : Linear ↥Γ(X, ⊤) X.Modules :=
  AlgebraicGeometry.Scheme.linearOfRingHom X ↥Γ(X, ⊤) (RingHom.id _)

/-- **Global sections is `Γ(X, ⊤)`-linear.** A scalar acts on a morphism by multiplying its
source, and over the whole space that is multiplication by the scalar itself. -/
instance linear_moduleGlobalSections : Functor.Linear ↥Γ(X, ⊤) (moduleGlobalSections X) := by
  rw [Functor.linear_iff]
  intro M a
  ext x
  exact AlgebraicGeometry.Scheme.smul_val_app_top X ↥Γ(X, ⊤) (RingHom.id _) a (𝟙 M) x

/-- **A scalar acts on `Hᵖ(X, ℱ)` as the cohomology of multiplication by that scalar.** The
right derived functors of a linear functor are linear. -/
instance linear_rightDerived_moduleGlobalSections (p : ℕ) :
    Functor.Linear ↥Γ(X, ⊤) ((moduleGlobalSections X).rightDerived p) :=
  Stacks.DerivedLinear.rightDerived_linear _ p

/-! ### One window of the long exact sequence -/

/-- **`Hᵖ(X, 𝒜) ⟶ Hᵖ(X, ℬ)` is an epimorphism when `Hᵖ(X, 𝒞) = 0`.** For a short exact sequence
`0 → 𝒜 → ℬ → 𝒞 → 0` of sheaves of modules, exactness of
`Hᵖ(X, 𝒜) ⟶ Hᵖ(X, ℬ) ⟶ Hᵖ(X, 𝒞)` is the `exact_map` field of the `δ`-functor of
[Stacks, Tag 010Q], and a map whose composite with the next one is zero and which is exact there
is an epimorphism. -/
theorem epi_map_rightDerived_f_of_isZero {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (p : ℕ) (h : IsZero (((moduleGlobalSections X).rightDerived p).obj S.X₃)) :
    Epi (((moduleGlobalSections X).rightDerived p).map S.f) :=
  ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (moduleGlobalSections X)).exact_map hS p).epi_f (h.eq_of_tgt _ _)

/-! ### The multiples of a module by an ideal of global functions -/

variable (I : Ideal ↥Γ(X, ⊤)) (F : X.Modules)

/-- **The multiples of `ℱ` by the elements of `I`, assembled into one morphism**
`⨁_{a ∈ I} ℱ ⟶ ℱ`. Its image is the subsheaf `I ℱ` and its cokernel is `ℱ / I ℱ`. -/
def idealMultiples : (∐ fun _ : ↥I => F) ⟶ F := Sigma.desc fun a => a.1 • 𝟙 F

/-- The `a`-th component of `idealMultiples` is multiplication by `a`. -/
theorem ι_idealMultiples (a : ↥I) :
    Sigma.ι (fun _ : ↥I => F) a ≫ idealMultiples X I F = a.1 • 𝟙 F :=
  Sigma.ι_comp_desc _ _

/-- The kernel inclusion and an epimorphism form a short exact sequence. -/
private theorem shortExact_kernel_ι {C : Type*} [Category C] [Abelian C] {A B : C} (g : A ⟶ B)
    [Epi g] : (ShortComplex.mk (kernel.ι g) g (kernel.condition g)).ShortExact :=
  { exact := ShortComplex.exact_kernel g }

/-- **`Hᵖ(X, ψ)` is an epimorphism**, for `ψ : ⨁_{a ∈ I} ℱ ⟶ ℱ` the multiples of `ℱ` by `I`,
as soon as `Hᵖ(X, ℱ/Iℱ) = 0` and `Hᵖ⁺¹` vanishes on the kernel of `⨁_{a ∈ I} ℱ ⟶ Iℱ`.

`ψ` is the composite of the epimorphism onto its image with the kernel inclusion of its cokernel
projection. The first factor has `Hᵖ` an epimorphism by
`exact_and_epi_map_rightDerived_of_isZero` applied to `0 → ker ⟶ ⨁ℱ ⟶ Iℱ → 0`, the second by
`epi_map_rightDerived_f_of_isZero` applied to `0 → Iℱ ⟶ ℱ ⟶ ℱ/Iℱ → 0`. -/
theorem epi_map_rightDerived_idealMultiples (p : ℕ)
    (hcoker : IsZero (((moduleGlobalSections X).rightDerived p).obj
      (cokernel (idealMultiples X I F))))
    (hker : IsZero (((moduleGlobalSections X).rightDerived (p + 1)).obj
      (kernel (Abelian.factorThruImage (idealMultiples X I F))))) :
    Epi (((moduleGlobalSections X).rightDerived p).map (idealMultiples X I F)) := by
  set ψ := idealMultiples X I F
  have hS₂ := shortExact_kernel_ι (cokernel.π ψ)
  have hS₁ := shortExact_kernel_ι (Abelian.factorThruImage ψ)
  have hker' : IsZero (((moduleGlobalSections X).rightDerivedPlus (((p : ℕ) : ℤ) + 1)).obj
      (kernel (Abelian.factorThruImage ψ))) :=
    hker.of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections X) (p + 1)).app _).symm
  have hfac : Abelian.factorThruImage ψ ≫ kernel.ι (cokernel.π ψ) = ψ := kernel.lift_ι _ _ _
  rw [← hfac, Functor.map_comp]
  exact epi_comp'
    (exact_and_epi_map_rightDerived_of_isZero (moduleGlobalSections X) hS₁ p hker').2
    (epi_map_rightDerived_f_of_isZero X hS₂ p hcoker)

/-! ### The Nakayama step -/

variable [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]

/-- **A morphism out of `Hᵖ(X, ℱ)` killed by every element of `I` vanishes**, under the two
vanishing hypotheses of `epi_map_rightDerived_idealMultiples`.

`Hᵖ(X, -)` commutes with the direct sum ([Stacks, Tag 01FF]), so a morphism out of
`Hᵖ(X, ⨁_{a ∈ I} ℱ)` vanishes as soon as each of its components does; the `a`-th component of
`Hᵖ(X, ψ) ≫ q` is `a • q`, which is zero by hypothesis. So `Hᵖ(X, ψ) ≫ q = 0`, and
`Hᵖ(X, ψ)` is an epimorphism. -/
theorem eq_zero_of_forall_smul_eq_zero (p : ℕ)
    (hcoker : IsZero (((moduleGlobalSections X).rightDerived p).obj
      (cokernel (idealMultiples X I F))))
    (hker : IsZero (((moduleGlobalSections X).rightDerived (p + 1)).obj
      (kernel (Abelian.factorThruImage (idealMultiples X I F)))))
    {Z : ModuleCat.{u} ↥Γ(X, ⊤)} (q : ((moduleGlobalSections X).rightDerived p).obj F ⟶ Z)
    (hq : ∀ a ∈ I, a • q = 0) : q = 0 := by
  have hpres : PreservesColimitsOfShape (Discrete ↥I)
      ((moduleGlobalSections X).rightDerived p) :=
    preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections X p ↥I
  have : PreservesColimit (Discrete.functor fun _ : ↥I => F)
      ((moduleGlobalSections X).rightDerived p) := hpres.preservesColimit
  have hcolim : IsColimit (((moduleGlobalSections X).rightDerived p).mapCocone
      (colimit.cocone (Discrete.functor fun _ : ↥I => F))) :=
    isColimitOfPreserves _ (colimit.isColimit _)
  have hzero : ((moduleGlobalSections X).rightDerived p).map (idealMultiples X I F) ≫ q = 0 := by
    refine hcolim.hom_ext fun j => ?_
    obtain ⟨a⟩ := j
    rw [comp_zero]
    change ((moduleGlobalSections X).rightDerived p).map (Sigma.ι (fun _ : ↥I => F) a) ≫
      ((moduleGlobalSections X).rightDerived p).map (idealMultiples X I F) ≫ q = 0
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, ι_idealMultiples X I F a,
      Functor.map_smul, CategoryTheory.Functor.map_id, Linear.smul_comp, Category.id_comp]
    exact hq a.1 a.2
  have := epi_map_rightDerived_idealMultiples X I F p hcoker hker
  exact zero_of_epi_comp _ hzero

/-- **The cohomology of `ℱ` is its own `I`-multiple** as soon as `Hᵖ(X, ℱ/Iℱ) = 0` and `Hᵖ⁺¹`
vanishes on the kernel of `⨁_{a ∈ I} ℱ ⟶ Iℱ`.

This is `eq_zero_of_forall_smul_eq_zero` at the projection onto the quotient by
`I · Hᵖ(X, ℱ)`, which every element of `I` kills. It is the hypothesis Nakayama's lemma consumes:
for a module finite over a ring in which `I` lies in the Jacobson radical, `M = I M` forces
`M = 0`. -/
theorem top_le_smul_top_rightDerived (p : ℕ)
    (hcoker : IsZero (((moduleGlobalSections X).rightDerived p).obj
      (cokernel (idealMultiples X I F))))
    (hker : IsZero (((moduleGlobalSections X).rightDerived (p + 1)).obj
      (kernel (Abelian.factorThruImage (idealMultiples X I F))))) :
    (⊤ : Submodule ↥Γ(X, ⊤) ↥(((moduleGlobalSections X).rightDerived p).obj F)) ≤ I • ⊤ := by
  let N : Submodule ↥Γ(X, ⊤) ↥(((moduleGlobalSections X).rightDerived p).obj F) := I • ⊤
  have hq : ∀ a ∈ I, a • (ModuleCat.ofHom N.mkQ) = 0 := by
    intro a ha
    ext x
    exact (Submodule.Quotient.mk_eq_zero N).2 (Submodule.smul_mem_smul ha Submodule.mem_top)
  have h0 := eq_zero_of_forall_smul_eq_zero X I F p hcoker hker (ModuleCat.ofHom N.mkQ) hq
  intro x _
  exact (Submodule.Quotient.mk_eq_zero N).1 (congrArg (fun f => (ModuleCat.Hom.hom f) x) h0)

/-- **`Hᵖ(X, ℱ) = 0`**, when on top of the two vanishing hypotheses the cohomology is a finite
`Γ(X, ⊤)`-module and `I` lies in the Jacobson radical of `Γ(X, ⊤)`.

`top_le_smul_top_rightDerived` makes `Hᵖ(X, ℱ)` its own `I`-multiple, and Nakayama's lemma
(`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`) kills a finite module with that property. This
is the shape in which the proof of [Stacks, Tag 02V7] concludes, with the completed stalk of the
higher direct image replaced by the cohomology over an affine base and the theorem on formal
functions replaced by the acyclicity of `ℱ/Iℱ`. -/
theorem isZero_rightDerived_of_isZero_cokernel (p : ℕ)
    (hjac : I ≤ Ideal.jacobson (⊥ : Ideal ↥Γ(X, ⊤)))
    (hfin : Module.Finite ↥Γ(X, ⊤) ↥(((moduleGlobalSections X).rightDerived p).obj F))
    (hcoker : IsZero (((moduleGlobalSections X).rightDerived p).obj
      (cokernel (idealMultiples X I F))))
    (hker : IsZero (((moduleGlobalSections X).rightDerived (p + 1)).obj
      (kernel (Abelian.factorThruImage (idealMultiples X I F))))) :
    IsZero (((moduleGlobalSections X).rightDerived p).obj F) := by
  have hbot : (⊤ : Submodule ↥Γ(X, ⊤) ↥(((moduleGlobalSections X).rightDerived p).obj F)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top
      (top_le_smul_top_rightDerived X I F p hcoker hker) hjac
  have hz : ∀ z : ↥(((moduleGlobalSections X).rightDerived p).obj F), z = 0 := fun z =>
    (Submodule.mem_bot _).1 (hbot.le (Submodule.mem_top (x := z)))
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => by rw [hz x, hz y]⟩

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
