module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusGenericPoint
public import StacksFrontier.AlgebraicGeometry.DepthTwoReflexiveExtension.Restrict
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DepthCoherence.ReflexiveExtension
public import StacksFrontier.Topology.Dimension.MaximalPointDrop
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.CodimensionOne
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.AlgebraicGeometry.Properties.CodimensionLocalRing
public import StacksCore.Tactic.StacksAttribute

/-!
# The codimension of the complement of the locus where a section is an isomorphism

Let `X` be an integral locally Noetherian normal scheme, `ℱ` a coherent reflexive `𝒪_X`-module
of rank one, `s` a nonzero global section of `ℱ`, and
`U = {x ∈ X | s : 𝒪_{X, x} → ℱ_x is an isomorphism}` the open locus of [Stacks, Tag 0EBN]
(`AlgebraicGeometry.sectionIsomorphismLocus`). [Stacks, Tag 0EBP] asserts that every
irreducible component of `X \ U` has codimension one in `X`.

## Main results

* `AlgebraicGeometry.isIso_of_forall_two_le_ringKrullDim_notMem`: a morphism of coherent
  reflexive modules which is a stalkwise isomorphism over an open whose complement has
  codimension at least two is an isomorphism.
* `AlgebraicGeometry.isIso_stalkMapOfHom_of_forall_two_le_ringKrullDim_on_open`: the same
  conclusion at the points of an open `V`, needing the codimension bound only on `V`.
* `AlgebraicGeometry.sectionIsomorphismLocus_eq_univ_of_forall_two_le_ringKrullDim`: the first
  of these for `s : 𝒪_X ⟶ ℱ`.
* `AlgebraicGeometry.ringKrullDim_stalk_le_one_of_notMem_sectionIsomorphismLocus`: the
  codimension bound at a point of `X \ U` maximal there for specialization.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_notMem_sectionIsomorphismLocus` and
  `AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_maximal_irreducible_compl_locus`: the same
  with the lower bound, at a maximal point of `X \ U` and at a point whose closure is an
  irreducible component of `X \ U`.
* `AlgebraicGeometry.exists_ringKrullDim_stalk_eq_one_of_maximal_irreducible_compl_locus` and
  `AlgebraicGeometry.codimension_eq_one_of_maximal_irreducible_compl_locus`:
  **[Stacks, Tag 0EBP]**: every irreducible component of `X \ U` has codimension one in `X`.

## Implementation notes

An irreducible component `Z` of `X \ U` is `closure {ξ}` for its generic point `ξ`, and the
codimension of `Z` in `X` is `ringKrullDim 𝒪_{X, ξ}`
(`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`, [Stacks, Tag 02IZ]). Several statements
below take maximality of `ξ` in `X \ U` for specialization, `∀ x ∉ U, x ⤳ ξ → x = ξ`, in place
of `Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ (X \ U)) (closure {ξ})`; on a scheme the two agree.

## References

* [Stacks Project, Tag 0EBP](https://stacks.math.columbia.edu/tag/0EBP)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0345](https://stacks.math.columbia.edu/tag/0345)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 02I4](https://stacks.math.columbia.edu/tag/02I4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexiveEquivalence

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Stalkwise isomorphy across a complement of codimension at least two -/

/-- The stalk map of a restricted morphism at `w` is an isomorphism exactly when the stalk map of
the morphism itself is one at `j w`. -/
theorem isIso_stalkMapOfHom_restrictFunctor_map_iff {W : Scheme.{u}} (j : W ⟶ X)
    [IsOpenImmersion j] {F G : X.Modules} (f : F ⟶ G) (w : W) :
    IsIso (stalkMapOfHom ((Scheme.Modules.restrictFunctor j).map f) w) ↔
      IsIso (stalkMapOfHom f (j w)) := by
  have hn := (Scheme.Modules.restrictStalkNatIso j w).hom.naturality f
  simp only [Functor.comp_map] at hn
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} w).map
      ((Scheme.Modules.toPresheaf W).map ((Scheme.Modules.restrictFunctor j).map f))) ↔
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} (j w)).map ((Scheme.Modules.toPresheaf X).map f))
  rw [← isIso_comp_right_iff _ ((Scheme.Modules.restrictStalkNatIso j w).hom.app G), hn,
    isIso_comp_left_iff]

/-- A morphism `f : ℱ ⟶ 𝒢` of coherent reflexive modules on a locally Noetherian normal scheme
which is an isomorphism on the stalks at the points of an open `U` and whose complement consists of
points of codimension at least two is an isomorphism. -/
theorem isIso_of_forall_two_le_ringKrullDim_notMem [IsLocallyNoetherian X] [IsNormal X]
    {F G : X.Modules} [_root_.SheafOfModules.IsCoherent F]
    [_root_.SheafOfModules.IsCoherent G] (hF : IsReflexive F) (hG : IsReflexive G) (f : F ⟶ G)
    (U : X.Opens) (hiso : ∀ x : X, x ∈ U → IsIso (stalkMapOfHom f x))
    (hdim : ∀ x : X, x ∉ (U : Set X) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x)) :
    IsIso f := by
  have hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
    fun x hx => two_le_depth_stalk_of_two_le_ringKrullDim x (hdim x hx)
  have hFunit :=
    Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive U F hF hdepth
  have hGunit :=
    Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive U G hG hdepth
  have hres : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) :=
    isIso_restrict_of_isIso_stalkMapOfHom_on_range U.ι _ fun x hx =>
      hiso x (by rwa [Scheme.Opens.opensRange_ι] at hx)
  exact isIso_of_restrict_of_isIso_unit U f hFunit hGunit hres

/-- If `f : ℱ ⟶ 𝒢` is a morphism of coherent reflexive modules which is an isomorphism on the
stalks at the points of an open `U`, and if every point of an open `V` outside `U` has
codimension at least two, then the stalk map of `f` is an isomorphism at every point of `V`. -/
theorem isIso_stalkMapOfHom_of_forall_two_le_ringKrullDim_on_open [IsLocallyNoetherian X]
    [IsNormal X] {F G : X.Modules} [_root_.SheafOfModules.IsCoherent F]
    [_root_.SheafOfModules.IsCoherent G] (hF : IsReflexive F) (hG : IsReflexive G) (f : F ⟶ G)
    (U V : X.Opens) (hiso : ∀ x : X, x ∈ U → IsIso (stalkMapOfHom f x))
    (hdim : ∀ x : X, x ∈ V → x ∉ (U : Set X) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    {ξ : X} (hξ : ξ ∈ V) : IsIso (stalkMapOfHom f ξ) := by
  have hFV : _root_.SheafOfModules.IsCoherent (F.restrict V.ι) := isCoherent_restrict V F
  have hGV : _root_.SheafOfModules.IsCoherent (G.restrict V.ι) := isCoherent_restrict V G
  have hFVr : IsReflexive (F.restrict V.ι) :=
    Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension.isReflexive_restrict V F inferInstance hF
  have hGVr : IsReflexive (G.restrict V.ι) :=
    Stacks.AlgebraicGeometry.DepthTwoReflexiveExtension.isReflexive_restrict V G inferInstance hG
  have key : IsIso ((Scheme.Modules.restrictFunctor V.ι).map f) := by
    refine isIso_of_forall_two_le_ringKrullDim_notMem (X := V.toScheme) hFVr hGVr _
      (V.ι ⁻¹ᵁ U) (fun v hv => ?_) fun v hv => ?_
    · exact (isIso_stalkMapOfHom_restrictFunctor_map_iff V.ι f v).mpr (hiso (V.ι v) hv)
    · have hdimv := hdim (V.ι v) v.2 hv
      rwa [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion V.ι,
        ← ringKrullDim_stalk_eq_coheight] at hdimv
  have hpt : IsIso (stalkMapOfHom ((Scheme.Modules.restrictFunctor V.ι).map f)
      (⟨ξ, hξ⟩ : V.toScheme)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_stalkMapOfHom ((Scheme.Modules.restrictFunctor V.ι).map f) key ⟨ξ, hξ⟩)
  exact (isIso_stalkMapOfHom_restrictFunctor_map_iff V.ι f (⟨ξ, hξ⟩ : V.toScheme)).mp hpt

/-! ### The locus is everything when the complement has codimension at least two -/

/-- If every point outside the locus where `s` trivializes `ℱ` has a local ring of dimension at
least two, then that locus is all of `X`. -/
theorem sectionIsomorphismLocus_eq_univ_of_forall_two_le_ringKrullDim [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F)
    (s : F.sections)
    (hcodim : ∀ x : X, x ∉ sectionIsomorphismLocus F s →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x)) :
    sectionIsomorphismLocus F s = Set.univ := by
  have hiso : IsIso (F.unitHomEquiv.symm s) :=
    isIso_of_forall_two_le_ringKrullDim_notMem (isReflexive_unit X) hF _
      (sectionIsomorphismOpen X F s) (fun _ hx => hx) hcodim
  exact Set.eq_univ_of_forall fun x => (mem_sectionIsomorphismLocus_iff F s x).mpr
    (bijective_stalkMapOfHom (F.unitHomEquiv.symm s) hiso x)

/-! ### The codimension bound -/

/-- Let `ξ` be a point outside the locus `U` where the global section `s` of the coherent reflexive
module `ℱ` trivializes it, and suppose `ξ` is *maximal* in `X \ U` for specialization: no other
point of `X \ U` has `ξ` in its closure. On a scheme that is exactly to say that `closure {ξ}` is
an irreducible component of `X \ U` with generic point `ξ`. Then the local ring at `ξ` has
dimension at most one, i.e. that component has codimension at most one in `X`. -/
theorem ringKrullDim_stalk_le_one_of_notMem_sectionIsomorphismLocus [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F)
    (s : F.sections) {ξ : X}
    (hξ : ξ ∉ sectionIsomorphismLocus F s)
    (hmax : ∀ x : X, x ∉ sectionIsomorphismLocus F s → x ⤳ ξ → x = ξ) :
    ringKrullDim (X.presheaf.stalk ξ) ≤ 1 := by
  by_contra hgt
  have h2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk ξ) := by
    rw [ringKrullDim_stalk_eq_coheight] at hgt ⊢
    rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) by norm_num, WithBot.coe_le_coe]
    exact not_lt.mp (ENat.lt_two_iff.not.mpr (by exact_mod_cast hgt))
  obtain ⟨N, hNaff, hξN, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := ξ) (by simp)
  have hNring : IsNoetherianRing Γ(X, N) := IsLocallyNoetherian.component_noetherian ⟨N, hNaff⟩
  have hNnoeth : NoetherianSpace ↥(N : Set X) := noetherianSpace_of_isAffineOpen N hNaff
  obtain ⟨V, hVopen, hξV, -, hVsub⟩ :=
    exists_isOpen_inter_subset_closure_singleton
      (isOpen_sectionIsomorphismLocus X F s).isClosed_compl hmax N.isOpen hξN
  have hdim : ∀ x : X, x ∈ (⟨V, hVopen⟩ : X.Opens) →
      x ∉ (sectionIsomorphismOpen X F s : Set X) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
    intro x hxV hxU
    have hle : x ≤ ξ := specializes_iff_mem_closure.mpr (hVsub ⟨hxU, hxV⟩)
    refine le_trans h2 ?_
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
    exact_mod_cast Order.coheight_anti hle
  have hkey := isIso_stalkMapOfHom_of_forall_two_le_ringKrullDim_on_open (isReflexive_unit X) hF
    (F.unitHomEquiv.symm s) (sectionIsomorphismOpen X F s) ⟨V, hVopen⟩ (fun _ hx => hx) hdim hξV
  exact hξ ((mem_sectionIsomorphismLocus_iff F s ξ).mpr
    ((ConcreteCategory.isIso_iff_bijective _).mp hkey))

/-- Assumptions and notation as in [Stacks, Tag 0EBN]: `X` is an integral locally Noetherian normal
scheme, `ℱ` is a coherent reflexive `𝒪_X`-module of rank one, `s` is a global section of `ℱ`, and
`sectionIsomorphismLocus F s` is the open locus `U` where `s` induces an isomorphism
`𝒪_{X, x} ⟶ ℱ_x`. If `s` is nonzero and `ξ ∈ X \ U` is maximal there for specialization, then
`closure {ξ}` has codimension one in `X`: the local ring at `ξ` has Krull dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_notMem_sectionIsomorphismLocus [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F)
    (hrank : Scheme.Modules.fiberRank F (genericPoint X) = 1)
    (s : F.sections) (hs : s.eval (Opposite.op (⊤ : X.Opens)) ≠ 0) {ξ : X}
    (hξ : ξ ∉ sectionIsomorphismLocus F s)
    (hmax : ∀ x : X, x ∉ sectionIsomorphismLocus F s → x ⤳ ξ → x = ξ) :
    ringKrullDim (X.presheaf.stalk ξ) = 1 :=
  ringKrullDim_stalk_eq_one
    (fun h => hξ (h ▸ mem_sectionIsomorphismLocus_genericPoint F hF hrank s hs))
    (ringKrullDim_stalk_le_one_of_notMem_sectionIsomorphismLocus F hF s hξ hmax)

/-- Assumptions and notation as in [Stacks, Tag 0EBN]: `X` is an integral locally Noetherian normal
scheme, `ℱ` is a coherent reflexive `𝒪_X`-module of rank one, `s` is a global section of `ℱ`, and
`U = sectionIsomorphismLocus F s` is the open locus where `s` induces an isomorphism
`𝒪_{X, x} ⟶ ℱ_x`. If `s` is nonzero and `closure {ξ}` is an irreducible component of `X \ U`, then
that component has codimension one in `X`: the local ring at `ξ` has Krull dimension one. -/
theorem ringKrullDim_stalk_eq_one_of_maximal_irreducible_compl_locus
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F)
    (hrank : Scheme.Modules.fiberRank F (genericPoint X) = 1)
    (s : F.sections) (hs : s.eval (Opposite.op (⊤ : X.Opens)) ≠ 0) {ξ : X}
    (hZ : Maximal (fun Z : Set X =>
      IsIrreducible Z ∧ Z ⊆ (sectionIsomorphismLocus F s)ᶜ) (closure {ξ})) :
    ringKrullDim (X.presheaf.stalk ξ) = 1 := by
  have hclosed : IsClosed ((sectionIsomorphismLocus F s)ᶜ) :=
    (isOpen_sectionIsomorphismLocus X F s).isClosed_compl
  have hξ : ξ ∉ sectionIsomorphismLocus F s := hZ.prop.2 (subset_closure rfl)
  refine ringKrullDim_stalk_eq_one_of_notMem_sectionIsomorphismLocus F hF hrank s hs hξ
    fun x hx hsp => ?_
  have hxcl : closure {x} ⊆ (sectionIsomorphismLocus F s)ᶜ :=
    hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)
  have hle : closure {x} ⊆ closure {ξ} :=
    hZ.2 ⟨isIrreducible_singleton.closure, hxcl⟩ (specializes_iff_closure_subset.mp hsp)
  exact (hsp.antisymm (specializes_iff_closure_subset.mpr hle)).eq

/-- Assumptions and notation as in [Stacks, Tag 0EBN]: `X` is an integral locally Noetherian normal
scheme, `ℱ` is a coherent reflexive `𝒪_X`-module of rank one, `s` is a global section of `ℱ`, and
`U = sectionIsomorphismLocus F s` is the open locus where `s` induces an isomorphism
`𝒪_{X, x} ⟶ ℱ_x`. If `s` is nonzero then every irreducible component `Z` of `X \ U` has codimension
one in `X`: `Z` is the closure of a point `ξ`, its generic point, and the local ring `𝒪_{X, ξ}` has
Krull dimension one, which is the codimension of `Z` in `X` by [Stacks, Tag 02IZ]. -/
@[stacks 0EBP]
theorem exists_ringKrullDim_stalk_eq_one_of_maximal_irreducible_compl_locus [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F)
    (hrank : Scheme.Modules.fiberRank F (genericPoint X) = 1)
    (s : F.sections) (hs : s.eval (Opposite.op (⊤ : X.Opens)) ≠ 0) {Z : Set X}
    (hZ : Maximal (fun Z : Set X =>
      IsIrreducible Z ∧ Z ⊆ (sectionIsomorphismLocus F s)ᶜ) Z) :
    ∃ ξ : X, closure {ξ} = Z ∧ ringKrullDim (X.presheaf.stalk ξ) = 1 := by
  have hclosed : IsClosed ((sectionIsomorphismLocus F s)ᶜ) :=
    (isOpen_sectionIsomorphismLocus X F s).isClosed_compl
  have hZcl : IsClosed Z :=
    closure_subset_iff_isClosed.mp
      (hZ.2 ⟨hZ.prop.1.closure, hclosed.closure_subset_iff.mpr hZ.prop.2⟩ subset_closure)
  have hgen : closure {hZ.prop.1.genericPoint} = Z :=
    hZ.prop.1.genericPoint_closure_eq.trans hZcl.closure_eq
  exact ⟨hZ.prop.1.genericPoint, hgen,
    ringKrullDim_stalk_eq_one_of_maximal_irreducible_compl_locus F hF hrank s hs
      (hgen.symm ▸ hZ)⟩

/-- Let `X` be an integral locally Noetherian normal scheme, `ℱ` a coherent reflexive `𝒪_X`-module
of rank one, `s` a nonzero global section, and `U = sectionIsomorphismLocus ℱ s` the open locus of
[Stacks, Tag 0EBN] where `s` induces an isomorphism `𝒪_{X, x} ⟶ ℱ_x`. Then every irreducible
component `Z` of `X \ U` has codimension one in `X`, in the sense of [Stacks, Tag 02I3]. -/
@[stacks 0EBP "every irreducible component of the complement of the isomorphism locus has \
codimension one in X"]
theorem codimension_eq_one_of_maximal_irreducible_compl_locus [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F)
    (hrank : Scheme.Modules.fiberRank F (genericPoint X) = 1)
    (s : F.sections) (hs : s.eval (Opposite.op (⊤ : X.Opens)) ≠ 0)
    (Z : IrreducibleCloseds X)
    (hZ : Maximal (fun W : Set X =>
      IsIrreducible W ∧ W ⊆ (sectionIsomorphismLocus F s)ᶜ) (Z : Set X)) :
    codimension Z = 1 := by
  obtain ⟨ξ, hξ, hk⟩ := exists_ringKrullDim_stalk_eq_one_of_maximal_irreducible_compl_locus
    F hF hrank s hs hZ
  have hgen : Z.isIrreducible.genericPoint = ξ :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).eq hξ
  exact_mod_cast (codimension_eq_ringKrullDim_stalk_genericPoint Z).trans (hgen ▸ hk)

end AlgebraicGeometry

end
