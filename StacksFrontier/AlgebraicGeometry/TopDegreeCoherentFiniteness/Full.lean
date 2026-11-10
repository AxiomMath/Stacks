module

public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.ChowTwist
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleLength
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.HgroupOfSheafCohomology
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0A3M]: finite dimensionality of top-degree coherent cohomology

Let `X` be a separated scheme of finite type over a field `k` and `ℱ` a coherent `𝒪_X`-module.
Then `H^d(X, ℱ)` is a finite-dimensional `k`-vector space, `d = dim(X)`.

The proof is the source's, by induction on `d`. The dévissage of [Stacks, Tag 01YG] reduces to an
ideal sheaf `ℐ` on an integral closed subscheme `Z`; if `dim Z < d` the group vanishes, and
otherwise the sequence `0 → ℐ → 𝒪_Z → 𝒪_Z/ℐ → 0` together with the induction hypothesis reduces
to `𝒪_Z`. For `𝒪_Z` the Chow twist `π : Y ⟶ Z` with its module `M` gives a coherent `π_* M`,
generically of rank one, with `H^d(Z, π_* M) = H^d(Y, M)` finite-dimensional because `Y` is open
in a projective scheme of dimension at most `d` (Tags 0A3G and 02O6); [Stacks, Tag 01YE] compares
`π_* M` with a nonzero ideal of `𝒪_Z` near the generic point, and the induction hypothesis
controls the cokernels, which are supported in a proper closed subset.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.TopDegree

attribute [local instance] Stacks.Topology.hasExt_sheafOpens

variable (k : Type u) [Field k]

/-- **Cohomology of a module above the dimension is finite-dimensional, because it vanishes.** -/
theorem finiteDimensional_of_topologicalKrullDim_lt {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) (m n : ℕ)
    (hdim : topologicalKrullDim X ≤ (m : WithBot ℕ∞)) (hmn : m < n) :
    FiniteDimensional k (cohomologyOverField k f F n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := { }
  have : SpectralSpace X := ⟨⟩
  have : QuasiSeparatedSpace X := inferInstance
  exact finiteDimensional_cohomologyOverField_of_isZero_Hgroup k f F n
    (Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology F n (by omega)
      (Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le m X
        inferInstance inferInstance _ n hdim hmn))

/-- The statement of [Stacks, Tag 0A3M] in degree `d`, for schemes of dimension at most `d`. -/
def TopFin (d : ℕ) : Prop :=
  ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f], topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
    ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F →
      FiniteDimensional k (cohomologyOverField k f F d)

/-- A morphism of modules which is an isomorphism over an open has its cokernel supported off
that open. -/
theorem supp_cokernel_subset_compl {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens)
    (hφ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) :
    SheafOfModules.supp (cokernel φ) ⊆ (U : Set X)ᶜ := by
  refine Stacks.Algebraization.supp_subset_compl_of_isZero_restrict U (cokernel φ) ?_
  have := CohomologyScalars.restrictFunctor_preservesFiniteColimits' U.ι
  have : PreservesColimit (parallelPair φ 0) (Scheme.Modules.restrictFunctor U.ι) :=
    inferInstance
  refine (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor U.ι).map φ)).of_iso ?_
  exact PreservesCokernel.iso (Scheme.Modules.restrictFunctor U.ι) φ

/-- A closed set of an irreducible scheme of dimension at most `d + 1` avoiding a point of a
nonempty open has dimension at most `d`. -/
theorem topologicalKrullDim_compl_le {Z : Scheme.{u}} [IrreducibleSpace Z] (d : ℕ)
    (hdim : topologicalKrullDim Z ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) (V : Z.Opens)
    (hV : (V : Set Z).Nonempty) :
    topologicalKrullDim ((V : Set Z)ᶜ : Set Z) ≤ (d : WithBot ℕ∞) := by
  have hne : ((V : Set Z)ᶜ) ≠ Set.univ := Set.compl_ne_univ.mpr hV
  have hfin : topologicalKrullDim Z < ⊤ := lt_of_le_of_lt hdim (by
    change (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞)
    exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))
  have hlt' :=
    (topologicalKrullDim_lt_of_isClosed_ne_univ V.isOpen.isClosed_compl hne hfin).trans_le hdim
  generalize topologicalKrullDim ((V : Set Z)ᶜ : Set Z) = t at hlt' ⊢
  induction t using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe t =>
    have h1 : t < ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hlt'
    have h2 : t ≤ (d : ℕ∞) := by
      induction t using ENat.recTopCoe with
      | top => exact absurd h1 (not_lt.mpr le_top)
      | coe t => exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h1)
    exact_mod_cast h2

/-- The dimension of a closed subscheme whose range lies in a closed set is at most that of the
set. -/
theorem topologicalKrullDim_le_of_range_subset {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] (T : Set X) (hT : Set.range i.base ⊆ T) :
    topologicalKrullDim W ≤ topologicalKrullDim T := by
  let g : W → T := fun w => ⟨i.base w, hT ⟨w, rfl⟩⟩
  have hg : Topology.IsInducing g :=
    (Topology.IsInducing.subtypeVal (t := T)).of_comp_iff.mp i.isClosedEmbedding.isInducing
  exact hg.topologicalKrullDim_le

variable {k}

/-- **Supported finiteness in degree `d`, from the statement in degree `d`.** -/
theorem finiteDimensional_of_supp_subset_of_topFin {d : ℕ} (ih : TopFin.{u} k d)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] (T : Set X) (hTc : IsClosed T)
    (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (Q : X.Modules) (hQ : _root_.SheafOfModules.IsCoherent Q)
    (hsupp : SheafOfModules.supp Q ⊆ T) :
    FiniteDimensional k (cohomologyOverField k f Q d) := by
  refine finiteDimensional_of_supp_subset k f d T hTc ?_ Q hQ hsupp
  intro W i _ _ I hI _ hrange
  exact ih W (i ≫ f) ((topologicalKrullDim_le_of_range_subset i T hrange).trans hT) _ hI

/-- **Supported finiteness in degree `d + 1`**: the groups vanish. -/
theorem finiteDimensional_succ_of_supp_subset {d : ℕ}
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (T : Set X) (hTc : IsClosed T) (hT : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (Q : X.Modules) (hQ : _root_.SheafOfModules.IsCoherent Q)
    (hsupp : SheafOfModules.supp Q ⊆ T) :
    FiniteDimensional k (cohomologyOverField k f Q (d + 1)) := by
  refine finiteDimensional_of_supp_subset k f (d + 1) T hTc ?_ Q hQ hsupp
  intro W i _ _ I _ _ hrange
  exact finiteDimensional_of_topologicalKrullDim_lt k (i ≫ f) _ d (d + 1)
    ((topologicalKrullDim_le_of_range_subset i T hrange).trans hT) (Nat.lt_succ_self d)

/-- **Top-degree finiteness for a scheme immersed in projective space.** -/
theorem finiteDimensional_top_of_isImmersion {Y : Scheme.{u}} (n : ℕ)
    (j : Y ⟶ ProjectiveSpace n (Spec (.of k))) [IsImmersion j] [QuasiCompact j]
    [LocallyOfFiniteType (j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)))]
    (e : ℕ) (hdim : topologicalKrullDim Y ≤ (e : WithBot ℕ∞)) (M : Y.Modules)
    (hM : _root_.SheafOfModules.IsCoherent M) :
    FiniteDimensional k (cohomologyOverField k
      (j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k))) M e) := by
  have : IsOpenImmersion j.toImage := isOpenImmersion_toImage j (Or.inl inferInstance)
  have : IsDominant j.toImage := isDominant_toImage j (Or.inl inferInstance)
  let g := j.imageι ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k))
  have : IsProper g := inferInstance
  have hLN : IsLocallyNoetherian j.image := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace j.image := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian j.image := { }
  have hcomp : j.toImage ≫ g = j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) := by
    simp only [g, ← Category.assoc, Scheme.Hom.toImage_imageι]
  have hdimI : topologicalKrullDim j.image ≤ (e : WithBot ℕ∞) :=
    (Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion k
      j.toImage (j.toImage ≫ g) g rfl j.toImage.denseRange).trans hdim
  have h := CohomologyScalars.finiteDimensional_top_of_isOpenImmersion_of_isProper k j.toImage g e
    hdimI M hM
  rwa [hcomp] at h

/-- The short exact sequence of a monomorphism and its cokernel. -/
theorem shortExact_cokernel {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) [Mono φ] :
    (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ)

/-- **Top-degree finiteness for the pushforward of a module along a Chow twist.** -/
private theorem finiteDimensional_pushforward_of_chowTwist {d n : ℕ} {Y Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g] (π : Y ⟶ Z) [IsProper π]
    (j : Y ⟶ ProjectiveSpace n (Spec (.of k))) [IsImmersion j]
    (hcomm : π ≫ g = j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)))
    (hdim : topologicalKrullDim Y ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) (M : Y.Modules)
    (hM : _root_.SheafOfModules.IsCoherent M)
    (hvan : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward π).rightDerived q).obj M)) :
    FiniteDimensional k
      (cohomologyOverField k g ((Scheme.Modules.pushforward π).obj M) (d + 1)) := by
  let P := ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)
  have : QuasiCompact (j ≫ P) := by
    rw [← hcomm]
    infer_instance
  have : QuasiCompact j := QuasiCompact.of_comp j P
  have : LocallyOfFiniteType (j ≫ P) := by
    rw [← hcomm]
    infer_instance
  have : FiniteDimensional k (cohomologyOverField k (π ≫ g) M (d + 1)) := by
    have h := finiteDimensional_top_of_isImmersion n j (d + 1) hdim M hM
    rwa [← hcomm] at h
  exact CohomologyScalars.finiteDimensional_pushforward_of_isZero_rightDerived k π g M hvan (d + 1)

/-- A coproduct of copies of a zero object, or an empty coproduct, is zero. -/
theorem isZero_sigma_const {X : Scheme.{u}} (r : ℕ) (I : X.Modules) (h : r = 0 ∨ IsZero I) :
    IsZero (∐ fun _ : Fin r => I) := by
  refine (IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ fun j => ?_)
  rcases h with rfl | h
  · exact j.elim0
  · exact h.eq_of_src _ _

/-- **Finiteness passes from a coproduct of copies of a module to the module.** -/
theorem finiteDimensional_of_sigma {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (r : ℕ) (hr : 0 < r)
    (I : X.Modules) (n : ℕ)
    [FiniteDimensional k (cohomologyOverField k f (∐ fun _ : Fin r => I) n)] :
    FiniteDimensional k (cohomologyOverField k f I n) := by
  let ι := Sigma.ι (fun _ : Fin r => I) ⟨0, hr⟩
  let p : (∐ fun _ : Fin r => I) ⟶ I := Sigma.desc fun j => if j = ⟨0, hr⟩ then 𝟙 I else 0
  have hp : ι ≫ p = 𝟙 I := by simp [ι, p]
  have hinj : Function.Injective (cohomologyOverFieldMap k f ι n) := by
    intro x y hxy
    have h := congrArg (cohomologyOverFieldMap k f p n) hxy
    rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← cohomologyOverFieldMap_comp, hp, cohomologyOverFieldMap_id] at h
  exact FiniteDimensional.of_injective (cohomologyOverFieldMap k f ι n).hom hinj

/-- The generic point lies in the support of the pushforward of an invertible module along a
morphism which is an isomorphism over a dense open. -/
private theorem genericPoint_mem_supp_pushforward {Y Z : Scheme.{u}} [IsIntegral Z] (π : Y ⟶ Z)
    (U : Z.Opens) (hU : Dense (U : Set Z)) [IsIso (π ∣_ U)] (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] :
    genericPoint Z ∈ SheafOfModules.supp
      ((Scheme.Modules.pushforward (𝟙 Z)).obj ((Scheme.Modules.pushforward π).obj M)) := by
  have hgen : IsGenericPoint (genericPoint Z) (Set.range (𝟙 Z : Z ⟶ Z).base) := by
    rw [show Set.range (𝟙 Z : Z ⟶ Z).base = Set.univ by simp]
    exact genericPoint_spec Z
  have hsimple := Module.length_eq_one_iff.mp
    (ProperCoherenceWitness.length_stalk_pushforward_chowTwist (𝟙 Z) π U hU M hgen)
  have hnt : Nontrivial
      (((Scheme.Modules.pushforward (π ≫ 𝟙 Z)).obj M).presheaf.stalk (genericPoint Z)) :=
    @IsSimpleModule.nontrivial _ _ _ _ _ hsimple
  have heq := SheafOfModules.supp_eq_of_iso ((Scheme.Modules.pushforwardComp π (𝟙 Z)).app M)
  have hmem : genericPoint Z ∈ SheafOfModules.supp
      ((Scheme.Modules.pushforward (π ≫ 𝟙 Z)).obj M) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk _ _).mpr hnt
  exact heq ▸ hmem

/-- A morphism from a coproduct of copies of `I` which is an isomorphism over an open meeting the
support of its target has a nonempty index set and a nonzero `I`. -/
private theorem pos_and_not_isZero_of_isIso_restrict {Z : Scheme.{u}} {r : ℕ} {I F : Z.Modules}
    (φ : (Scheme.Modules.pushforward (𝟙 Z)).obj (∐ fun _ : Fin r => I) ⟶ F) (V : Z.Opens)
    (hφ : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ)) {ξ : Z}
    (hξsupp : ξ ∈ SheafOfModules.supp F) (hξV : ξ ∈ V) : 0 < r ∧ ¬ IsZero I := by
  by_contra! hcon
  have hzero := isZero_sigma_const r I ((Nat.eq_zero_or_pos r).imp_right hcon)
  have hF : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj F) :=
    ((Scheme.Modules.restrictFunctor V.ι).map_isZero
      ((Scheme.Modules.pushforward (𝟙 Z)).map_isZero hzero)).of_iso
        (asIso ((Scheme.Modules.restrictFunctor V.ι).map φ)).symm
  exact Stacks.Algebraization.supp_subset_compl_of_isZero_restrict V F hF hξsupp hξV

/-- **From a nonzero coherent ideal sheaf to the structure sheaf, in the top degree.** -/
private theorem finiteDimensional_unit_of_ideal {d : ℕ} {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g] [IsIntegral Z]
    (hdim : topologicalKrullDim Z ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule) [I.toSheafOfModules.IsCoherent]
    (hz : ¬ IsZero I.toSheafOfModules)
    (hI : FiniteDimensional k (cohomologyOverField k g I.toSheafOfModules (d + 1))) :
    FiniteDimensional k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) (d + 1)) := by
  have hZln : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have hZn : IsNoetherian Z := { }
  obtain ⟨W, hξW, hW⟩ := exists_isIso_restrict_ideal_ι I hz
  have : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z
  exact finiteDimensional_cohomologyOverField_of_shortExact k g
    (@shortExact_cokernel _ _ _ I.ι (SheafOfModules.Submodule.instMonoι I)) (d + 1) hI
    (finiteDimensional_succ_of_supp_subset g ((W : Set Z)ᶜ) W.isOpen.isClosed_compl
      (topologicalKrullDim_compl_le d hdim W ⟨_, hξW⟩) (cokernel I.ι)
      (AlgebraicGeometry.isCoherent_cokernel I.ι) (supp_cokernel_subset_compl I.ι W hW))

/-- **The structure sheaf of a variety, in the top degree.** Let `Z` be integral, separated and
of finite type over `k`, of dimension at most `d + 1`, and assume [Stacks, Tag 0A3M] in degree
`d`. Then `H^{d+1}(Z, 𝒪_Z)` is finite-dimensional. -/
theorem finiteDimensional_unit_of_topFin {d : ℕ} (ih : TopFin.{u} k d) {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    [IsIntegral Z] (hdim : topologicalKrullDim Z ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    FiniteDimensional k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) (d + 1)) := by
  have hZln : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have hZn : IsNoetherian Z := { }
  obtain ⟨Y, π, U, M, n, j, hπ, hU, hiso, hj, hcomm, hdimY, hMinv, hMcoh, hGcoh, hvan⟩ :=
    exists_chowTwist k g
  -- the top-degree cohomology of `M`
  have hZfin := finiteDimensional_pushforward_of_chowTwist g π j hcomm (hdimY.trans hdim) M hMcoh
    hvan
  set G := (Scheme.Modules.pushforward π).obj M
  set F' := (Scheme.Modules.pushforward (𝟙 Z)).obj G
  have hF'coh : F'.IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite (𝟙 Z) G
  have hkill : Stacks.ClosedImmersion.StalkKilledByMaximalIdeal F'
      ((𝟙 Z : Z ⟶ Z).base (genericPoint Z)) :=
    Stacks.AlgebraicGeometry.ProperCoherenceWitnessStalk.stalkKilledByMaximalIdeal_pushforward
      (𝟙 Z) (genericPoint Z) (genericPoint_spec Z) G
  have hF'fin : FiniteDimensional k (cohomologyOverField k g F' (d + 1)) :=
    finiteDimensional_cohomologyOverField_pushforward_of_isClosedImmersion k (𝟙 Z) g G (d + 1)
      (by rwa [Category.id_comp])
  -- [Stacks, Tag 01YE]
  obtain ⟨r, I, hIcoh, hPcoh, φ, hmono, V, hξV, hφV⟩ :=
    Stacks.ClosedImmersion.exists_idealCoproduct_pushforward_mono_isIso_near_genericPoint
      (𝟙 Z) (genericPoint Z) (genericPoint_spec Z) F' hkill
  -- the cokernel is supported off `V`, in dimension at most `d`
  have hcokfin : FiniteDimensional k (cohomologyOverField k g (cokernel φ) d) :=
    finiteDimensional_of_supp_subset_of_topFin ih g ((V : Set Z)ᶜ) V.isOpen.isClosed_compl
      (topologicalKrullDim_compl_le d hdim V ⟨_, hξV⟩) (cokernel φ)
      (AlgebraicGeometry.isCoherent_cokernel φ) (supp_cokernel_subset_compl φ V hφV)
  have hPfin := finiteDimensional_cohomologyOverField_one_of_shortExact_succ k g
    (shortExact_cokernel φ) d hcokfin hF'fin
  have hSfin : FiniteDimensional k (cohomologyOverField k g
      (∐ fun _ : Fin r => I.toSheafOfModules) (d + 1)) := by
    have h := (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k (𝟙 Z) g
      (∐ fun _ : Fin r => I.toSheafOfModules) (d + 1)).toLinearEquiv.symm.finiteDimensional
    rwa [Category.id_comp] at h
  -- the ideal is nonzero and the coproduct is not empty
  have hnz := pos_and_not_isZero_of_isIso_restrict φ V hφV
    (genericPoint_mem_supp_pushforward π U hU M) hξV
  -- from the ideal to the structure sheaf
  exact finiteDimensional_unit_of_ideal g hdim I hnz.2
    (finiteDimensional_of_sigma g r hnz.1 I.toSheafOfModules (d + 1))

/-- **Ideal sheaves of a variety, in the top degree.** -/
theorem finiteDimensional_ideal_of_topFin {d : ℕ} (ih : TopFin.{u} k d) {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    [IsIntegral Z] (hdim : topologicalKrullDim Z ≤ ((d + 1 : ℕ) : WithBot ℕ∞))
    (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hIqc : I.toSheafOfModules.IsQuasicoherent) :
    FiniteDimensional k (cohomologyOverField k g I.toSheafOfModules (d + 1)) := by
  have hZln : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have hZn : IsNoetherian Z := { }
  by_cases hz : IsZero I.toSheafOfModules
  · exact finiteDimensional_of_isZero k (isZero_cohomologyOverField_of_isZero k g hz (d + 1))
  obtain ⟨W, hξW, hW⟩ := exists_isIso_restrict_ideal_ι I hz
  have : Mono I.ι := SheafOfModules.Submodule.instMonoι I
  have hO : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z
  have hIcoh : I.toSheafOfModules.IsCoherent :=
    @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono Z inferInstance
      (SheafOfModules.unit Z.ringCatSheaf) I.toSheafOfModules hO inferInstance I.ι
      (SheafOfModules.Submodule.instMonoι I)
  have hcokfin : FiniteDimensional k (cohomologyOverField k g (cokernel I.ι) d) :=
    finiteDimensional_of_supp_subset_of_topFin ih g ((W : Set Z)ᶜ) W.isOpen.isClosed_compl
      (topologicalKrullDim_compl_le d hdim W ⟨genericPoint Z, hξW⟩) (cokernel I.ι)
      (AlgebraicGeometry.isCoherent_cokernel I.ι) (supp_cokernel_subset_compl I.ι W hW)
  exact finiteDimensional_cohomologyOverField_one_of_shortExact_succ k g
    (@shortExact_cokernel _ _ _ I.ι (SheafOfModules.Submodule.instMonoι I)) d hcokfin
    (finiteDimensional_unit_of_topFin ih g hdim)

variable (k)

/-- **[Stacks, Tag 0A3M] in every degree**, for schemes of dimension at most that degree. -/
theorem topFin : ∀ d : ℕ, TopFin.{u} k d
  | 0 => by
    intro X f _ _ _ hdim F hF
    refine finiteDimensional_cohomologyOverField_of_forall_integralIdeal k f 0 ?_ F hF
    intro Z i hi hZ I hI
    have hZln : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f)
    have hdimZ : topologicalKrullDim Z ≤ ((0 : ℕ) : WithBot ℕ∞) :=
      (StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion i).trans hdim
    have hne : Nonempty (IrreducibleCloseds Z) :=
      ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
    have hdim0 : topologicalKrullDim (Z : Type u) = 0 :=
      le_antisymm (by simpa using hdimZ) Order.krullDim_nonneg
    have hO : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z
    have : I.toSheafOfModules.IsCoherent :=
      @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono Z inferInstance
        (SheafOfModules.unit Z.ringCatSheaf) I.toSheafOfModules hO inferInstance I.ι
        (SheafOfModules.Submodule.instMonoι I)
    exact finiteDimensional_cohomologyOverField_of_finiteType_of_dimension_zero k (i ≫ f) hdim0
      I.toSheafOfModules 0
  | d + 1 => by
    intro X f _ _ _ hdim F hF
    refine finiteDimensional_cohomologyOverField_of_forall_integralIdeal k f (d + 1) ?_ F hF
    intro Z i hi hZ I hI
    exact finiteDimensional_ideal_of_topFin (topFin d) (i ≫ f)
      ((StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion i).trans hdim) I hI

end AlgebraicGeometry.TopDegree

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0A3M].** Let `X` be a separated scheme of finite type over a field `k` and let
`ℱ` be a coherent `𝒪_X`-module. Then `dim_k H^d(X, ℱ) < ∞`, where `d = dim(X)`. -/
@[stacks 0A3M]
theorem finiteDimensional_cohomologyOverField_topologicalKrullDim (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) (d : ℕ)
    (hd : topologicalKrullDim (X : Type u) = (d : WithBot ℕ∞)) :
    FiniteDimensional k (cohomologyOverField k f F d) :=
  TopDegree.topFin k d X f hd.le F hF

end AlgebraicGeometry

end
