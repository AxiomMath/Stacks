module

public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.ChowWitness
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericIdealCoproduct
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Coproduct
public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite dimensionality of the top-degree cohomology of a coherent module

[Stacks, Tag 0A3M]: let `X` be a separated scheme of finite type over a field `k`, `ℱ` a coherent
`𝒪_X`-module and `d = dim(X)`. Then `H^d(X, ℱ)` is a finite-dimensional `k`-vector space.

The proof is the source's induction on `d`, run on the stronger statement in which `d` is any
bound for the dimension of the support of `ℱ` rather than the dimension of `X`:

* `AlgebraicGeometry.TopDegreeFiniteness.finiteDimensional_cohomologyOverField_of_supp_subset`:
  if `ℱ` is coherent and supported in a set of dimension at most `d`, then `H^d(X, ℱ)` is
  finite-dimensional.

The dévissage of [Stacks, Tag 01YG], restricted to modules supported in a fixed set
(`AlgebraicGeometry.TopDegreeFiniteness.property_of_isCoherent_of_supp_subset`), reduces this to
a nonzero ideal sheaf `ℐ` on an integral closed subscheme `Z` of dimension at most `d`. If
`dim Z < d` the group vanishes. Otherwise the source compares `ℐ` with `𝒪_Z`, and `𝒪_Z` with the
coherent module `𝒢 = π_* ℳ` built from Chow's lemma in
`AlgebraicGeometry.TopDegreeFiniteness.exists_isCoherent_genericPoint_mem_supp_finiteDimensional`,
along maps which are isomorphisms at the generic point of `Z`, so that their kernels and cokernels
are supported in dimension `< d` and are handled by the induction hypothesis and by the vanishing
above the dimension. The source's map `𝒪_Z ⟶ 𝒢`, which uses a global section of `ℳ`, is replaced
by the monomorphism `ℐ'^{⊕ r} ⟶ 𝒢` of [Stacks, Tag 01YE] (for some coherent ideal `ℐ'`), which
is an isomorphism near the generic point: then `H^d(ℐ')` is finite, hence `H^d(𝒪_Z)` and
`H^d(ℐ)` are.

## Main results

* `AlgebraicGeometry.TopDegreeFiniteness.finiteDimensional_topCohomology_of_isSeparated`:
  for a coherent module `ℱ` on a separated scheme `X` of finite type over `k`, the cohomology
  `H^{dim X}(X, ℱ)` is a finite-dimensional `k`-vector space.

## References

* [Stacks Project, Tag 0A3M](https://stacks.math.columbia.edu/tag/0A3M)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.TopDegreeFiniteness

/-! ### The generic stalk of the quotient by a nonzero ideal -/

/-- The stalk of the structure sheaf of an integral scheme at its generic point has length one:
it is the function field. -/
theorem length_stalk_unit_genericPoint (Z : Scheme.{u}) [IsIntegral Z] :
    Module.length (Z.presheaf.stalk (genericPoint Z))
      ((structureSheafModule Z).presheaf.stalk (genericPoint Z)) = 1 := by
  have hfield : IsField (Z.presheaf.stalk (genericPoint Z)) := Field.toIsField Z.functionField
  refine (structureSheafStalkLinearEquiv Z (genericPoint Z)).length_eq.trans
    (Module.length_eq_one_iff.mpr ?_)
  rw [isSimpleModule_self_iff_isUnit]
  exact ⟨⟨hfield.exists_pair_ne⟩, fun x hx => isUnit_iff_exists_inv.mpr (hfield.mul_inv_cancel hx)⟩

/-- In `ℕ∞`, if `1 = a + b` and `a ≠ 0` then `b = 0`. -/
theorem eq_zero_of_one_eq_add {a b : ℕ∞} (h : 1 = a + b) (ha : a ≠ 0) : b = 0 := by
  by_contra hb
  have : (2 : ℕ∞) ≤ 1 := by
    rw [h]
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ a + b := add_le_add (Order.one_le_iff_ne_zero.mpr ha) (Order.one_le_iff_ne_zero.mpr hb)
  exact absurd this (by decide)

/-- The quotient of the structure sheaf of an integral scheme by a nonzero quasi-coherent ideal
vanishes at the generic point. -/
theorem genericPoint_notMem_supp_cokernel_ι {Z : Scheme.{u}} [IsIntegral Z]
    (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hH : H.toSheafOfModules.IsQuasicoherent) (hne : ¬ IsZero H.toSheafOfModules) :
    genericPoint Z ∉ SheafOfModules.supp
      (cokernel (show (H.toSheafOfModules : Z.Modules) ⟶ structureSheafModule Z from H.ι)) := by
  let ι' : (H.toSheafOfModules : Z.Modules) ⟶ structureSheafModule Z := H.ι
  have hS := shortExact_cokernelSequence_of_mono (X := Z) ι' (SheafOfModules.Submodule.instMonoι H)
  have hlen := AlgebraicGeometry.length_stalk_add_of_shortExact hS (genericPoint Z)
  have h1 := length_stalk_unit_genericPoint Z
  have hmem := (mem_supp_iff_length_ne_zero _ _).1
    (Stacks.AlgebraicGeometry.Tag01YHFullSupport.genericPoint_mem_supp_of_not_isZero H hH hne)
  exact fun hc => (mem_supp_iff_length_ne_zero _ _).1 hc
    (eq_zero_of_one_eq_add (h1.symm.trans hlen) hmem)

/-! ### Retracts and finite coproducts -/

/-- A finite coproduct of copies of a module is a zero object as soon as the index is empty or
the module is. -/
theorem isZero_sigma_const_of {X : Scheme.{u}} (I : X.Modules) (r : ℕ)
    (h : r = 0 ∨ IsZero I) : IsZero (∐ fun _ : Fin r => I) := by
  refine (IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ fun j => ?_)
  rcases h with rfl | hI
  · exact j.elim0
  · exact hI.eq_of_src _ _

/-- The cohomology of a module is finite-dimensional when that of a finite nonempty coproduct of
copies of it is. -/
theorem finiteDimensional_of_sigma_const (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (I : X.Modules) {r : ℕ} (j : Fin r) (n : ℕ)
    (h : FiniteDimensional k (cohomologyOverField k f (∐ fun _ : Fin r => I) n)) :
    FiniteDimensional k (cohomologyOverField k f I n) := by
  have hsplit : Sigma.ι (fun _ : Fin r => I) j ≫ Sigma.desc (fun _ : Fin r => 𝟙 I) = 𝟙 I :=
    Sigma.ι_comp_desc _ _
  have hinj :
      Function.Injective (cohomologyOverFieldMap k f (Sigma.ι (fun _ : Fin r => I) j) n) := by
    intro a b hab
    have := congrArg (cohomologyOverFieldMap k f (Sigma.desc (fun _ : Fin r => 𝟙 I)) n) hab
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← cohomologyOverFieldMap_comp, hsplit, cohomologyOverFieldMap_id] at this
  exact Module.Finite.of_injective
    (cohomologyOverFieldMap k f (Sigma.ι (fun _ : Fin r => I) j) n).hom hinj

/-! ### The induction -/

section Induction

variable (k : Type u) [Field k]

/-- The dimension of the support of a module of finite type which misses the generic point of an
integral scheme of dimension at most `e + 1` is at most `e`. -/
theorem topologicalKrullDim_supp_le_of_notMem {Z : Scheme.{u}} [IsIntegral Z] {e : ℕ}
    (hdim : topologicalKrullDim Z ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) (M : Z.Modules) [M.IsFiniteType]
    (hM : genericPoint Z ∉ SheafOfModules.supp M) :
    topologicalKrullDim (SheafOfModules.supp M) ≤ (e : WithBot ℕ∞) := by
  have hfin : topologicalKrullDim Z ≠ ⊤ := fun h => by
    rw [h] at hdim
    exact absurd hdim (not_le.mpr (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top (e + 1))))
  exact ENat.WithBot.lt_add_one_iff.mp
    (by exact_mod_cast (topologicalKrullDim_supp_lt_of_notMem hfin M hM).trans_le hdim)

/-- Let `Z` be an integral scheme, separated and of finite type over `k`, of dimension at most
`d`, and suppose the statement holds one degree lower for every coherent module supported in
dimension `< d` on `Z`. Then `H^d(Z, ℐ)` is finite-dimensional for every nonzero quasi-coherent
ideal `ℐ ⊆ 𝒪_Z`. -/
theorem finiteDimensional_cohomologyOverField_ideal {Z : Scheme.{u}} [IsIntegral Z]
    (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g] (e : ℕ)
    (hdim : topologicalKrullDim Z ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (ih : ∀ F : Z.Modules, _root_.SheafOfModules.IsCoherent F →
      topologicalKrullDim (SheafOfModules.supp F) ≤ (e : WithBot ℕ∞) →
        FiniteDimensional k (cohomologyOverField k g F e))
    (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hH : H.toSheafOfModules.IsQuasicoherent) (hne : ¬ IsZero H.toSheafOfModules) :
    FiniteDimensional k (cohomologyOverField k g H.toSheafOfModules (e + 1)) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Z := { }
  have hO : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z
  -- Vanishing of `H^{e+1}` for modules supported off the generic point.
  have hvan : ∀ M : Z.Modules, _root_.SheafOfModules.IsCoherent M →
      genericPoint Z ∉ SheafOfModules.supp M → IsZero (cohomologyOverField k g M (e + 1)) := by
    intro M hM hξ
    have := hM.isFiniteType
    exact isZero_cohomologyOverField_of_supp_subset k g (SheafOfModules.supp M)
      (topologicalKrullDim_supp_le_of_notMem hdim M hξ) M hM subset_rfl (by omega)
  have hlow : ∀ M : Z.Modules, _root_.SheafOfModules.IsCoherent M →
      genericPoint Z ∉ SheafOfModules.supp M →
        FiniteDimensional k (cohomologyOverField k g M e) := by
    intro M hM hξ
    have := hM.isFiniteType
    exact ih M hM (topologicalKrullDim_supp_le_of_notMem hdim M hξ)
  -- The quotient by a nonzero ideal is supported off the generic point.
  have hcoh_ideal : ∀ H' : (SheafOfModules.unit Z.ringCatSheaf).Submodule,
      H'.toSheafOfModules.IsQuasicoherent → H'.toSheafOfModules.IsCoherent := by
    intro H' hH'
    exact @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono Z inferInstance
      (SheafOfModules.unit Z.ringCatSheaf) H'.toSheafOfModules hO hH' H'.ι
      (SheafOfModules.Submodule.instMonoι H')
  have hquot : ∀ H' : (SheafOfModules.unit Z.ringCatSheaf).Submodule,
      H'.toSheafOfModules.IsQuasicoherent →
        (cokernel (show (H'.toSheafOfModules : Z.Modules) ⟶ structureSheafModule Z
          from H'.ι)).IsCoherent := by
    intro H' hH'
    have := hcoh_ideal H' hH'
    have : (structureSheafModule Z).IsCoherent := hO
    exact isCoherent_cokernel _
  -- The coherent module with finite top cohomology and full support.
  obtain ⟨G, hG, hξG, hGfin⟩ :=
    exists_isCoherent_genericPoint_mem_supp_finiteDimensional k g (e + 1) hdim
  obtain ⟨r, I, hI, β, hβ, V, hξV, hβV⟩ :=
    Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_idealCoproduct_mono_isIso_near_genericPoint
      G (genericPoint Z) (genericPoint_spec Z)
  have hξC : genericPoint Z ∉ SheafOfModules.supp (cokernel β) :=
    Stacks.AlgebraicGeometry.ConfinedDevissage.notMem_supp_cokernel_of_isIso_restrict β V hβV _ hξV
  have hIqc : I.toSheafOfModules.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : HasBiproduct (fun _ : Fin r => I.toSheafOfModules) := HasBiproduct.of_hasCoproduct _
  have hsum : (∐ fun _ : Fin r => I.toSheafOfModules).IsCoherent :=
    Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso'
      (biproduct.isoCoproduct (fun _ : Fin r => I.toSheafOfModules)).symm
      (Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_biproduct_const _ hI r (Fin r)
        inferInstance inferInstance (Fintype.card_fin r))
  have hCcoh : (cokernel β).IsCoherent := isCoherent_cokernel β
  -- `H^{e+1}` of the coproduct is finite.
  have hsumfin : FiniteDimensional k
      (cohomologyOverField k g (∐ fun _ : Fin r => I.toSheafOfModules) (e + 1)) :=
    finiteDimensional_cohomologyOverField_of_hom k g β e hGfin
      (finiteDimensional_of_isZero k (isZero_cohomologyOverField_of_isZero k g
        (isZero_kernel_of_mono β) (e + 1)))
      (hlow _ hCcoh hξC)
  -- The coproduct is nonzero, since the cokernel of `β` misses the generic point while `𝒢` does
  -- not; so `r ≥ 1` and `I ≠ 0`.
  have hnz : ¬ IsZero (∐ fun _ : Fin r => I.toSheafOfModules) := fun h => by
    rcases mem_supp_X₁_or_mem_supp_X₃ (shortExact_cokernelSequence_of_mono β hβ) hξG with h1 | h3
    · exact (Set.eq_empty_iff_forall_notMem.mp
        (Stacks.AlgebraicGeometry.ConfinedDevissage.supp_eq_empty_of_isZero
          (∐ fun _ : Fin r => I.toSheafOfModules : Z.Modules) h)) _ h1
    · exact hξC h3
  have hr : r ≠ 0 := fun h => hnz (isZero_sigma_const_of _ r (Or.inl h))
  have hIne : ¬ IsZero I.toSheafOfModules := fun h => hnz (isZero_sigma_const_of _ r (Or.inr h))
  have hIfin : FiniteDimensional k (cohomologyOverField k g I.toSheafOfModules (e + 1)) :=
    finiteDimensional_of_sigma_const k g I.toSheafOfModules ⟨0, Nat.pos_of_ne_zero hr⟩ (e + 1)
      hsumfin
  -- `H^{e+1}(𝒪_Z)` is finite, a quotient of `H^{e+1}(I)`.
  have hOfin : FiniteDimensional k
      (cohomologyOverField k g (structureSheafModule Z) (e + 1)) :=
    finiteDimensional_cohomologyOverField_of_hom' k g
      (show (I.toSheafOfModules : Z.Modules) ⟶ structureSheafModule Z from I.ι) (e + 1) hIfin
      (finiteDimensional_of_isZero k (isZero_cohomologyOverField_of_isZero k g
        (@isZero_kernel_of_mono _ _ _ _ _
          (show (I.toSheafOfModules : Z.Modules) ⟶ structureSheafModule Z from I.ι)
          (SheafOfModules.Submodule.instMonoι I) _) (e + 2)))
      (finiteDimensional_of_isZero k (hvan _ (hquot I hIqc)
        (genericPoint_notMem_supp_cokernel_ι I hIqc hIne)))
  -- `H^{e+1}(ℐ)` is finite.
  exact finiteDimensional_cohomologyOverField_of_hom k g
    (show (H.toSheafOfModules : Z.Modules) ⟶ structureSheafModule Z from H.ι) e hOfin
    (finiteDimensional_of_isZero k (isZero_cohomologyOverField_of_isZero k g
      (@isZero_kernel_of_mono _ _ _ _ _
        (show (H.toSheafOfModules : Z.Modules) ⟶ structureSheafModule Z from H.ι)
        (SheafOfModules.Submodule.instMonoι H) _) (e + 1)))
    (hlow _ (hquot H hH) (genericPoint_notMem_supp_cokernel_ι H hH hne))

/-- A nonempty irreducible space of dimension at most `0` has dimension `0`. -/
theorem topologicalKrullDim_eq_zero_of_le_zero (Z : Type u) [TopologicalSpace Z]
    [IrreducibleSpace Z] (h : topologicalKrullDim Z ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim Z = 0 := by
  have : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
  exact le_antisymm (by simpa using h) Order.krullDim_nonneg

/-- Let `X` be separated and of finite type over a field `k`, let `ℱ` be a coherent `𝒪_X`-module
and let `T ⊆ X` be a set containing the support of `ℱ` with `dim T ≤ d`. Then `H^d(X, ℱ)` is a
finite-dimensional `k`-vector space. -/
theorem finiteDimensional_cohomologyOverField_of_supp_subset (d : ℕ) :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated f] (F : X.Modules), _root_.SheafOfModules.IsCoherent F → ∀ T : Set X,
      topologicalKrullDim T ≤ (d : WithBot ℕ∞) → SheafOfModules.supp F ⊆ T →
        FiniteDimensional k (cohomologyOverField k f F d) := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro X f _ _ _ F hF T hT hFT
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := { }
  refine property_of_isCoherent_of_supp_subset X
    (fun G => FiniteDimensional k (cohomologyOverField k f G d)) T
    (finiteDimensional_of_isZero k (isZero_cohomologyOverField_of_isZero k f
      Stacks.AlgebraicGeometry.CoherentDevissage.isZero_terminal d))
    (fun S hS _ _ _ h1 h3 => finiteDimensional_cohomologyOverField_of_shortExact k f hS d h1 h3)
    ?_ F hF hFT
  intro Z i _ _ H hH hne hiT
  refine finiteDimensional_cohomologyOverField_pushforward_of_isClosedImmersion k i f
    H.toSheafOfModules d ?_
  have hdimZ : topologicalKrullDim Z ≤ (d : WithBot ℕ∞) :=
    (topologicalKrullDim_le_of_range_subset i hiT).trans hT
  rcases d with _ | e
  · have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
    have hO : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z
    have hHc : H.toSheafOfModules.IsCoherent :=
      @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono Z inferInstance
        (SheafOfModules.unit Z.ringCatSheaf) H.toSheafOfModules hO hH H.ι
        (SheafOfModules.Submodule.instMonoι H)
    exact finiteDimensional_cohomologyOverField_of_finiteType_of_dimension_zero k (i ≫ f)
      (topologicalKrullDim_eq_zero_of_le_zero Z hdimZ) H.toSheafOfModules 0
  · exact finiteDimensional_cohomologyOverField_ideal k (i ≫ f) e hdimZ
      (fun G hG hdG => IH e (by omega) (i ≫ f) G hG (SheafOfModules.supp G) hdG subset_rfl)
      H hH hne

/-- Let `X` be a separated scheme of finite type over a field `k`, let `ℱ` be a coherent
`𝒪_X`-module and let `d = dim(X)`. Then `H^d(X, ℱ)` is a finite-dimensional `k`-vector space. -/
@[stacks 0A3M]
theorem finiteDimensional_topCohomology_of_isSeparated {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (F : X.Modules) [F.IsCoherent]
    (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    FiniteDimensional k (cohomologyOverField k f F d) :=
  finiteDimensional_cohomologyOverField_of_supp_subset k d f F inferInstance Set.univ
    (((Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq).trans hd).le
    (Set.subset_univ _)

end Induction

end AlgebraicGeometry.TopDegreeFiniteness

end
