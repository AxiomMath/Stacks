module

public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IrreducibleSupportCriterion
public import StacksFrontier.AlgebraicGeometry.FullSupport.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Irreducible
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Coherent modules supported on a closed subset, and maps that are isomorphisms generically

This file collects the dévissage tools that the induction on the dimension in the proof of
[Stacks, Tag 0A3M] runs on.

* The criterion of [Stacks, Tag 01YG] restricted to the coherent modules supported inside a fixed
  set `T`: a property stable under extensions which holds on the zero module and on the direct
  images of nonzero quasi-coherent ideals along the integral closed subschemes contained in `T`
  holds on every coherent module supported in `T`.
* Grothendieck's vanishing for such modules: on a scheme of finite type over a field, the
  cohomology of a coherent module supported in a closed set of dimension at most `d` vanishes in
  every degree above `d` ([Stacks, Tag 02UZ] on the integral closed subschemes of that set).
* Two finiteness transfers along a morphism `φ : ℱ ⟶ 𝒢` of modules, which only see the
  kernel and the cokernel of `φ` through finiteness of their cohomology in the neighbouring
  degrees. Applied to a map which is an isomorphism at the generic point of an integral scheme,
  the kernel and the cokernel are supported in smaller dimension and these are the two steps
  "arguing as before using our induction hypothesis" of the source's proof.
* The support of the middle term of a short exact sequence, read through stalk lengths
  (`AlgebraicGeometry.length_stalk_add_of_shortExact`), which is how those generic isomorphisms
  are recognised.

## References

* [Stacks Project, Tag 0A3M](https://stacks.math.columbia.edu/tag/0A3M)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.TopDegreeFiniteness

/-! ### Stalk lengths along a short exact sequence -/

/-- A point lies in the support of a module exactly when the stalk there has nonzero length. -/
theorem mem_supp_iff_length_ne_zero {X : Scheme.{u}} (F : X.Modules) (x : X) :
    x ∈ SheafOfModules.supp F ↔
      Module.length (X.presheaf.stalk x) (F.presheaf.stalk x) ≠ 0 := by
  refine (SheafOfModules.mem_supp_iff_nontrivial_stalk F x).trans ?_
  rw [← pos_iff_ne_zero, Module.length_pos_iff]
  exact Iff.rfl

/-- The support of the first term of a short exact sequence lies in that of the middle term. -/
theorem supp_X₁_subset {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    SheafOfModules.supp S.X₁ ⊆ SheafOfModules.supp S.X₂ := by
  intro x hx
  rw [mem_supp_iff_length_ne_zero] at hx ⊢
  rw [AlgebraicGeometry.length_stalk_add_of_shortExact hS x]
  exact fun h => hx (add_eq_zero.mp h).1

/-- The support of the last term of a short exact sequence lies in that of the middle term. -/
theorem supp_X₃_subset {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    SheafOfModules.supp S.X₃ ⊆ SheafOfModules.supp S.X₂ := by
  intro x hx
  rw [mem_supp_iff_length_ne_zero] at hx ⊢
  rw [AlgebraicGeometry.length_stalk_add_of_shortExact hS x]
  exact fun h => hx (add_eq_zero.mp h).2

/-- A point of the support of the middle term of a short exact sequence lies in the support of
one of the outer terms. -/
theorem mem_supp_X₁_or_mem_supp_X₃ {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) {x : X} (hx : x ∈ SheafOfModules.supp S.X₂) :
    x ∈ SheafOfModules.supp S.X₁ ∨ x ∈ SheafOfModules.supp S.X₃ := by
  rw [mem_supp_iff_length_ne_zero, AlgebraicGeometry.length_stalk_add_of_shortExact hS x] at hx
  by_contra h
  rw [not_or, mem_supp_iff_length_ne_zero, mem_supp_iff_length_ne_zero, not_not, not_not] at h
  exact hx (by rw [h.1, h.2, add_zero])

/-! ### The dévissage restricted to modules supported in a fixed set -/

/-- The short complex `0 ⟶ G ⟶ 0` for a zero object `G`, with the terminal module on both sides,
is short exact. -/
theorem shortExact_terminal_of_isZero {X : Scheme.{u}} {G : X.Modules} (hG : IsZero G) :
    (ShortComplex.mk (0 : ⊤_ X.Modules ⟶ G) (0 : G ⟶ ⊤_ X.Modules) (by simp)).ShortExact := by
  have hT : IsZero (⊤_ X.Modules) := IsTerminal.isZero terminalIsTerminal
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ hG) ?_ ?_
  · exact ⟨fun a b _ => hT.eq_of_tgt a b⟩
  · exact ⟨fun a b _ => hT.eq_of_src a b⟩

/-- **The direct image of a nonzero quasi-coherent ideal on an integral closed subscheme is
supported exactly on that subscheme.** The ideal has full support on the integral scheme
([`Stacks.AlgebraicGeometry.Tag01YHFullSupport.supp_eq_univ_of_not_isZero`]) and the support of
a direct image along a closed immersion is the image of the support. -/
theorem supp_pushforward_submodule_eq_range {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hH : H.toSheafOfModules.IsQuasicoherent) (hne : ¬ IsZero H.toSheafOfModules) :
    SheafOfModules.supp ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) =
      Set.range i.base := by
  refine (AlgebraicGeometry.supp_pushforward_of_isClosedImmersion i H.toSheafOfModules).trans ?_
  rw [Stacks.AlgebraicGeometry.Tag01YHFullSupport.supp_eq_univ_of_not_isZero H hH hne,
    Set.image_univ]

/-- **[Stacks, Tag 01YG] for the coherent modules supported in a fixed set.** Let `X` be a
Noetherian scheme, `T ⊆ X` a set and `P` a property of coherent modules which holds on the zero
module, is stable under extensions of coherent modules, and holds on the direct image `i_* ℐ` of
every nonzero quasi-coherent ideal `ℐ ⊆ 𝒪_Z` along every closed immersion `i : Z ⟶ X` of an
integral scheme whose image lies in `T`. Then `P` holds on every coherent module supported
in `T`.

The property "`P`, or the support is not contained in `T`" is again stable under extensions,
since the outer terms of a short exact sequence are supported inside the support of the middle
one, and it holds on every direct image `i_* ℐ`: on the zero ideal through the zero module, and
otherwise because `i_* ℐ` is supported exactly on the image of `i`. So [Stacks, Tag 01YG]
applies to it. -/
theorem property_of_isCoherent_of_supp_subset (X : Scheme.{u}) [IsNoetherian X]
    (P : X.Modules → Prop) (T : Set X) (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      H.toSheafOfModules.IsQuasicoherent → ¬ IsZero H.toSheafOfModules →
      Set.range i.base ⊆ T → P ((Scheme.Modules.pushforward i).obj H.toSheafOfModules)) :
    ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → SheafOfModules.supp F ⊆ T → P F := by
  let Q : X.Modules → Prop := fun F => P F ∨ ¬ SheafOfModules.supp F ⊆ T
  have hQ : ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → Q F := by
    refine Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent X Q
      (Or.inl hzero) ?_ ?_
    · intro S hS h1 h2 h3 hP1 hP3
      by_cases hT : SheafOfModules.supp S.X₂ ⊆ T
      · exact Or.inl (hext S hS h1 h2 h3
          (hP1.resolve_right (not_not.mpr ((supp_X₁_subset hS).trans hT)))
          (hP3.resolve_right (not_not.mpr ((supp_X₃_subset hS).trans hT))))
      · exact Or.inr hT
    · intro Z i _ _ H hH
      by_cases hHz : IsZero H.toSheafOfModules
      · have hz : IsZero ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) :=
          (Scheme.Modules.pushforward i).map_isZero hHz
        have hS := shortExact_terminal_of_isZero hz
        refine Or.inl (hext _ hS Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_terminal
          ?_ Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_terminal hzero hzero)
        exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero hz
      · by_cases hT : Set.range i.base ⊆ T
        · exact Or.inl (hideal i H hH hHz hT)
        · refine Or.inr fun hsub => hT ?_
          rw [← supp_pushforward_submodule_eq_range i H hH hHz]
          exact hsub
  intro F hF hFT
  exact (hQ F hF).resolve_right (not_not.mpr hFT)

/-! ### Vanishing above the dimension -/

section Vanishing

variable (k : Type u) [Field k]

/-- A scheme locally of finite type and quasi-compact over a field is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType_aux {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact { }

/-- **[Stacks, Tag 02UZ] for a scheme of finite type over a field.** If `X` is of finite type over
`k` and of dimension at most `d`, then `Hⁱ(X, ℱ) = 0` for every module `ℱ` and every `i > d`.

`X` is a Noetherian scheme, hence a Noetherian space, where Grothendieck's theorem is
`Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le`; the
comparisons of [Stacks, Tag 01F1] read it in the spelling of
`AlgebraicGeometry.cohomologyOverField`. -/
theorem isZero_cohomologyOverField_of_finiteType_of_topologicalKrullDim_le {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules)
    {d i : ℕ} (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hi : d < i) :
    IsZero (cohomologyOverField k f F i) := by
  have hnoeth : IsNoetherian X := isNoetherian_of_locallyOfFiniteType_aux k f
  refine (isZero_cohomologyOverField_iff_isZero_hgroup k f F i).mpr ?_
  refine
    (Stacks.Cohomology.ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
      (J := Opens.grothendieckTopology (X : Type u)) (R := X.ringCatSheaf)
      (U := (⊤ : Opens (X : Type u))) (n := i) (F := F)).mpr ?_
  have hsub := (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) i).mp
    (Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
      (d := d) hdim hi _)
  exact @AddCommGrpCat.isZero_of_subsingleton _ hsub

/-- The dimension of an integral closed subscheme contained in a set `T` is at most that of `T`:
the closed immersion is an embedding, landing in `T`. -/
theorem topologicalKrullDim_le_of_range_subset {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {T : Set X} (hT : Set.range i.base ⊆ T) :
    topologicalKrullDim (Z : Type u) ≤ topologicalKrullDim T :=
  (i.isClosedEmbedding.isInducing.codRestrict (fun z => hT ⟨z, rfl⟩)).topologicalKrullDim_le

/-- **Vanishing above the dimension of the support.** Let `X` be of finite type over `k` and let
`ℱ` be a coherent module supported in a set `T` of dimension at most `d`. Then `Hⁱ(X, ℱ) = 0` for
every `i > d`.

By the dévissage `property_of_isCoherent_of_supp_subset` it suffices to treat `ℱ = i_* ℐ` for an
integral closed subscheme `i : Z ⟶ X` contained in `T`; then `Hⁱ(X, i_* ℐ) = Hⁱ(Z, ℐ)`, which
vanishes because `dim Z ≤ dim T ≤ d`. -/
theorem isZero_cohomologyOverField_of_supp_subset {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (T : Set X) {d : ℕ}
    (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (hFT : SheafOfModules.supp F ⊆ T) {i : ℕ}
    (hi : d < i) : IsZero (cohomologyOverField k f F i) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType_aux k f
  refine property_of_isCoherent_of_supp_subset X (fun G => IsZero (cohomologyOverField k f G i))
    T (isZero_cohomologyOverField_of_isZero k f
      Stacks.AlgebraicGeometry.CoherentDevissage.isZero_terminal i) ?_ ?_ F hF hFT
  · intro S hS _ _ _ h1 h3
    exact isZero_cohomologyOverField_of_shortExact k f hS i h1 h3
  · intro Z j _ _ H _ _ hjT
    refine IsZero.of_iso ?_ (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k j f
      H.toSheafOfModules i).symm
    exact isZero_cohomologyOverField_of_finiteType_of_topologicalKrullDim_le k (j ≫ f)
      H.toSheafOfModules ((topologicalKrullDim_le_of_range_subset j hjT).trans hT) hi

end Vanishing

/-! ### Finiteness transfers along a morphism -/

section Transfer

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Alias of `AlgebraicGeometry.finiteDimensional_cohomologyOverField_three_of_shortExact`. -/
alias finiteDimensional_X₃_of_shortExact :=
  AlgebraicGeometry.finiteDimensional_cohomologyOverField_three_of_shortExact

/-- Alias of `AlgebraicGeometry.finiteDimensional_cohomologyOverField_one_of_shortExact_succ`. -/
alias finiteDimensional_X₁_succ_of_shortExact :=
  AlgebraicGeometry.finiteDimensional_cohomologyOverField_one_of_shortExact_succ

/-- The short exact sequence `0 ⟶ ker φ ⟶ ℱ ⟶ coim φ ⟶ 0`. -/
theorem shortExact_cokernelSequence_kernel {F G : X.Modules} (φ : F ⟶ G) :
    (ShortComplex.cokernelSequence (kernel.ι φ)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
    (show Mono (kernel.ι φ) from inferInstance) (by exact inferInstance)

/-- The short exact sequence `0 ⟶ ℱ ⟶ 𝒢 ⟶ coker φ ⟶ 0` of a monomorphism `φ`. -/
theorem shortExact_cokernelSequence_of_mono {F G : X.Modules} (φ : F ⟶ G) (hφ : Mono φ) :
    (ShortComplex.cokernelSequence φ).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _) hφ
    (by exact inferInstance)

/-- The short exact sequence `0 ⟶ im φ ⟶ 𝒢 ⟶ coker φ ⟶ 0`. -/
theorem shortExact_kernelSequence_cokernel {F G : X.Modules} (φ : F ⟶ G) :
    (ShortComplex.kernelSequence (cokernel.π φ)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _)
    (by exact inferInstance) (show Epi (cokernel.π φ) from inferInstance)

/-- **Finiteness descends along a morphism, one degree up from its cokernel.** For
`φ : ℱ ⟶ 𝒢`, if `Hᵐ⁺¹(X, 𝒢)`, `Hᵐ⁺¹(X, ker φ)` and `Hᵐ(X, coker φ)` are finite-dimensional, so is
`Hᵐ⁺¹(X, ℱ)`.

From `0 ⟶ im φ ⟶ 𝒢 ⟶ coker φ ⟶ 0` the group `Hᵐ⁺¹(X, im φ)` sits between `Hᵐ(X, coker φ)` and
`Hᵐ⁺¹(X, 𝒢)`; the coimage is isomorphic to the image; and from
`0 ⟶ ker φ ⟶ ℱ ⟶ coim φ ⟶ 0` the group `Hᵐ⁺¹(X, ℱ)` sits between those of `ker φ` and of
`coim φ`. -/
theorem finiteDimensional_cohomologyOverField_of_hom {F G : X.Modules} (φ : F ⟶ G) (m : ℕ)
    (hG : FiniteDimensional k (cohomologyOverField k f G (m + 1)))
    (hK : FiniteDimensional k (cohomologyOverField k f (kernel φ) (m + 1)))
    (hC : FiniteDimensional k (cohomologyOverField k f (cokernel φ) m)) :
    FiniteDimensional k (cohomologyOverField k f F (m + 1)) := by
  have hI : FiniteDimensional k (cohomologyOverField k f (Abelian.image φ) (m + 1)) :=
    finiteDimensional_X₁_succ_of_shortExact k f (shortExact_kernelSequence_cokernel φ) m hC hG
  have hCo : FiniteDimensional k (cohomologyOverField k f (Abelian.coimage φ) (m + 1)) :=
    Module.Finite.equiv
      (cohomologyOverFieldIso k f (Abelian.coimageIsoImage φ) (m + 1)).symm.toLinearEquiv
  exact finiteDimensional_cohomologyOverField_of_shortExact k f
    (shortExact_cokernelSequence_kernel φ) (m + 1) hK hCo

/-- **Finiteness ascends along a morphism.** For `φ : ℱ ⟶ 𝒢`, if `Hⁿ(X, ℱ)`, `Hⁿ⁺¹(X, ker φ)`
and `Hⁿ(X, coker φ)` are finite-dimensional, so is `Hⁿ(X, 𝒢)`. -/
theorem finiteDimensional_cohomologyOverField_of_hom' {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (hF : FiniteDimensional k (cohomologyOverField k f F n))
    (hK : FiniteDimensional k (cohomologyOverField k f (kernel φ) (n + 1)))
    (hC : FiniteDimensional k (cohomologyOverField k f (cokernel φ) n)) :
    FiniteDimensional k (cohomologyOverField k f G n) := by
  have hCo : FiniteDimensional k (cohomologyOverField k f (Abelian.coimage φ) n) :=
    finiteDimensional_X₃_of_shortExact k f (shortExact_cokernelSequence_kernel φ) n hF hK
  have hI : FiniteDimensional k (cohomologyOverField k f (Abelian.image φ) n) :=
    Module.Finite.equiv (cohomologyOverFieldIso k f (Abelian.coimageIsoImage φ) n).toLinearEquiv
  exact finiteDimensional_cohomologyOverField_of_shortExact k f
    (shortExact_kernelSequence_cokernel φ) n hI hC

end Transfer

end AlgebraicGeometry.TopDegreeFiniteness

end
