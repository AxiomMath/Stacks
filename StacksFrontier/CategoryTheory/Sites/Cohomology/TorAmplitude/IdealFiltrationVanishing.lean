module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.AdicQuotients
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealTensorVanishing

/-!
# Derived tensor products with a sheaf of modules filtered by the powers of an ideal

Let `(C, O)` be a ringed site, `I ⊆ O` a sheaf of ideals, `T` a derived tensor product on
`D(O)` and `K` an object of `D(O)`. A sheaf of `O`-modules `M` carrying a finite decreasing
filtration `M = N₀ ⊇ N₁ ⊇ … ⊇ Nₘ = 0` with `I · N_k ⊆ N_{k+1}` is built out of modules killed
by `I`: every successive quotient `N_k/N_{k+1}` is one. So a cohomological vanishing in a
single degree that holds for `K ⊗^L_O G` for every `G` killed by `I` holds for `K ⊗^L_O M`.

## Main results

* `Stacks.Sites.isZero_homologyTensorSingle_of_idealSmul_filtration_sections`: the vanishing for
  the bottom term `N 0` of such a filtration, with the hypothesis on the modules killed by `I`
  stated on sections.
* `Stacks.Sites.isZero_homologyTensorSingle_of_idealSmul_filtration`: the same with that
  hypothesis stated as the vanishing of `I ⊗_O G ⟶ O ⊗_O G`.
* `Stacks.Sites.isZero_homologyTensorSingle_of_idealSmul_filtration_top` and
  `Stacks.Sites.isZero_homologyTensorSingle_of_idealSmul_filtration_top_sections`: both stated
  for the module itself, when the filtration starts at the whole module.

## Implementation notes

This is the dévissage of the proof of Stacks 0942 part (2) — "`F` has a finite filtration whose
successive quotients are sheaves of `O/I`-modules, thus it suffices to show the vanishing for
all `O/I`-modules `G`" — with "sheaf of `O/I`-modules" replaced throughout by the property it
is used for, namely that `I` kills the module. The two halves of the argument are kept apart:
`Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_of_filtration` runs
the induction along the filtration knowing nothing about ideals, and
`Stacks.Sites.sheafTensor_map_idealι_app_cokernel_homOfLE_eq_zero` identifies the successive
quotients as modules killed by `I`.

The hypothesis on the modules killed by `I` is stated twice, because its two consumers ask for
two different spellings of "killed by `I`" and neither implies the other at the level of the
dévissage. The retract argument of
`Stacks.Sites.isBoundedAboveBy_tensor_single_of_idealι_app_eq_zero` both produces and consumes
the vanishing of the ordinary map `I ⊗_O G ⟶ O ⊗_O G`; the identification of `Mod(O/I)` with the
`I`-annihilated `O`-modules,
`Stacks.SheafOfModules.ChangeOfRings.essImage_restrictScalars_iff`, consumes instead the
sectionwise statement that the sections of `I` kill the sections of `G`. The sectionwise version
is the *primary* one here: it is the stronger lemma, since a hypothesis quantified over the
modules with vanishing `I ⊗_O G ⟶ O ⊗_O G` implies one quantified over the `I`-annihilated
modules (`Stacks.Sites.sheafTensor_map_idealι_app_eq_zero`) and not conversely, so the two
`_sections` statements below subsume the other two, which are deduced from them.

The filtration is indexed by all of `ℕ` and asked to vanish at the stage `m`; the terms beyond
`m` are unconstrained, since the induction never reaches them.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.Sites

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (I : IdealSubsheaf.{v, u, w} X.O)
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, v, w, d} X)
  (K : RingedSite.DerivedModules.{u, v, w, d} X)

/-- **A module filtered by submodules absorbing the product with `I` inherits a vanishing from
the modules annihilated by `I`.** Let `N : ℕ → M.Submodule` be decreasing with
`I · N k ⊆ N (k + 1)` and with `N m` zero. If the cohomology of `K ⊗^L_O G[0]` in the degree `i`
vanishes for every sheaf of modules `G` whose sections are killed by the sections of `I`, then so
does that of `K ⊗^L_O (N 0)[0]`: the sections of `I` kill the sections of every successive
quotient of the filtration, and the vanishing climbs the filtration. -/
theorem isZero_homologyTensorSingle_of_idealSmul_filtration_sections (i : ℤ) (m : ℕ)
    {M : RingedSite.Modules.{u, v, w} X} (N : ℕ → M.Submodule)
    (hmono : ∀ k, N (k + 1) ≤ N k) (hsmul : ∀ k, idealSmul I (N k) ≤ N (k + 1))
    (hm : IsZero ((N m).toSheafOfModules))
    (hG : ∀ G : RingedSite.Modules.{u, v, w} X,
      (∀ (U : X.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U),
        a ∈ I.obj U → ∀ g : G.val.obj U, a • g = 0) →
      IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i G)) :
    IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i
      ((N 0).toSheafOfModules)) :=
  Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_of_filtration T K i m
    (fun k => (N k).toSheafOfModules)
    (fun k => Stacks.SheafOfModules.Submodule.homOfLE (hmono k))
    (fun k => Stacks.SheafOfModules.Submodule.mono_homOfLE (hmono k)) hm
    (fun k => hG _ (smul_cokernel_homOfLE_eq_zero I (hmono k) (hsmul k)))

/-- **The same with the hypothesis stated as the vanishing of `I ⊗_O G ⟶ O ⊗_O G`**, which is
the form the retract argument of
`Stacks.Sites.isBoundedAboveBy_tensor_single_of_idealι_app_eq_zero` produces. It is weaker than
the sectionwise form, the sectionwise hypothesis being the one that implies the other. -/
theorem isZero_homologyTensorSingle_of_idealSmul_filtration (i : ℤ) (m : ℕ)
    {M : RingedSite.Modules.{u, v, w} X} (N : ℕ → M.Submodule)
    (hmono : ∀ k, N (k + 1) ≤ N k) (hsmul : ∀ k, idealSmul I (N k) ≤ N (k + 1))
    (hm : IsZero ((N m).toSheafOfModules))
    (hG : ∀ G : RingedSite.Modules.{u, v, w} X,
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map I.ι).app G = 0 →
      IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i G)) :
    IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i
      ((N 0).toSheafOfModules)) :=
  isZero_homologyTensorSingle_of_idealSmul_filtration_sections I T K i m N hmono hsmul hm
    (fun G hs => hG G (sheafTensor_map_idealι_app_eq_zero I G hs))

/-- **The same vanishing for the module itself**, when the filtration starts at the whole
module, with the hypothesis on the annihilated modules stated on sections. The inclusion of the
largest submodule is an isomorphism, being a monomorphism which is split epi by
`Stacks.SheafOfModules.isSplitEpi_ι_top`. -/
theorem isZero_homologyTensorSingle_of_idealSmul_filtration_top_sections (i : ℤ) (m : ℕ)
    {M : RingedSite.Modules.{u, v, w} X} (N : ℕ → M.Submodule) (h0 : N 0 = ⊤)
    (hmono : ∀ k, N (k + 1) ≤ N k) (hsmul : ∀ k, idealSmul I (N k) ≤ N (k + 1))
    (hm : IsZero ((N m).toSheafOfModules))
    (hG : ∀ G : RingedSite.Modules.{u, v, w} X,
      (∀ (U : X.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U),
        a ∈ I.obj U → ∀ g : G.val.obj U, a • g = 0) →
      IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i G)) :
    IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i M) := by
  have : Epi (N 0).ι := h0 ▸ Stacks.SheafOfModules.epi_ι_top
  have : IsIso (N 0).ι := isIso_of_mono_of_epi _
  exact Stacks.SheafOfModules.DerivedTensorProduct.isZero_homologyTensorSingle_of_iso T K i
    (asIso (N 0).ι).symm
    (isZero_homologyTensorSingle_of_idealSmul_filtration_sections I T K i m N hmono hsmul hm hG)

/-- **The same vanishing for the module itself**, with the hypothesis stated as the vanishing of
`I ⊗_O G ⟶ O ⊗_O G`. -/
theorem isZero_homologyTensorSingle_of_idealSmul_filtration_top (i : ℤ) (m : ℕ)
    {M : RingedSite.Modules.{u, v, w} X} (N : ℕ → M.Submodule) (h0 : N 0 = ⊤)
    (hmono : ∀ k, N (k + 1) ≤ N k) (hsmul : ∀ k, idealSmul I (N k) ≤ N (k + 1))
    (hm : IsZero ((N m).toSheafOfModules))
    (hG : ∀ G : RingedSite.Modules.{u, v, w} X,
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map I.ι).app G = 0 →
      IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i G)) :
    IsZero (Stacks.SheafOfModules.DerivedTensorProduct.homologyTensorSingle T K i M) :=
  isZero_homologyTensorSingle_of_idealSmul_filtration_top_sections I T K i m N h0 hmono hsmul hm
    (fun G hs => hG G (sheafTensor_map_idealι_app_eq_zero I G hs))

end Stacks.Sites

end
