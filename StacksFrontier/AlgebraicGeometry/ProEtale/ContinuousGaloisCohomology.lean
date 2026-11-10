module

public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedGaloisSheaf
public import StacksFrontier.AlgebraicGeometry.ProEtale.PointCohomology.CompletedSheafComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.PointCohomology.ContinuousResolution

/-!
# Pro-étale cohomology of a field with completed coefficients

Let `K` be a field with absolute Galois group `G`, and let `M` be a topological `G`-module which
is the inverse limit of its discrete quotients `M/Nⱼ` by a system of open submodules. The
completed sheaf `M^∧ = limⱼ ε⁻¹(M/Nⱼ)` on the pro-étale site of `Spec K` has cohomology Tate's
continuous cohomology:

  `Hⁱ(Spec(K)_proét, M^∧) = Hⁱ_cont(G, M)`.

The completed sheaf is the sheaf of continuous equivariant functions on geometric points with
values in `M`, and the standard resolution of `M` by the coinduced modules `C(G, ⋯ C(G, M))`
sheafifies to a resolution of it by sheaves without higher cohomology, whose global sections are
the homogeneous continuous cochains. This applies to a profinite abelian group, the system being
that of all open Galois-stable subgroups, and to an `I`-adically complete module over a
Noetherian ring, the system being that of the `IⁿM`.

## Main results

* `AlgebraicGeometry.GaloisSheaf.rightDerivedCompletionIso`: the comparison for a general
  quotient system.
* `AlgebraicGeometry.GaloisSheaf.rightDerivedProfiniteSheafIso`: the comparison for a profinite
  abelian group.
* `AlgebraicGeometry.GaloisSheaf.rightDerivedAdicSheafIso`: the comparison for an `I`-adically
  complete module over a Noetherian ring.

## Implementation notes

Continuous cohomology is Mathlib's `continuousCohomology`, the homology of the homogeneous
continuous cochains `C(G, C(G, ⋯ C(G, M)))ᴳ`, for the topological representation `M` lifted to a
universe containing that of `G`, which is what the coinduction `C(G, -)` requires. Pro-étale
cohomology is the right derived functor of global sections of abelian sheaves; the identification
is of abelian groups, after the universe lift.

## References

* [Stacks Project, Tag 09B4](https://stacks.math.columbia.edu/tag/09B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology

universe t t' u r w

namespace AlgebraicGeometry.GaloisSheaf

variable {K : Type u} [Field K]

/-! ### The representation lifted to a universe containing the Galois group -/

section ULift

variable {Λ : Type r} [Ring Λ] [TopologicalSpace Λ] {M : Type w} [AddCommGroup M] [Module Λ M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul Λ M]
  (ρ : Representation Λ (galoisGroup K) M) (hρ : Continuous fun p : galoisGroup K × M ↦ ρ p.1 p.2)

omit [TopologicalSpace Λ] [IsTopologicalAddGroup M] [ContinuousSMul Λ M] in
include hρ in
/-- Each element of the Galois group acts continuously on `M` when the action is jointly
continuous. -/
lemma continuous_rep_apply (g : galoisGroup K) : Continuous (ρ g) :=
  hρ.comp (continuous_const.prodMk continuous_id)

/-- The universe lift of a topological additive group is a topological additive group. -/
instance : IsTopologicalAddGroup (ULift.{u} M) where
  continuous_add := continuous_uliftUp.comp
    ((continuous_uliftDown.comp continuous_fst).add (continuous_uliftDown.comp continuous_snd))
  continuous_neg := continuous_uliftUp.comp continuous_uliftDown.neg

/-- Scalar multiplication by `Λ` on the universe lift of `M` is continuous. -/
instance : ContinuousSMul Λ (ULift.{u} M) where
  continuous_smul := continuous_uliftUp.comp
    (continuous_fst.smul (continuous_uliftDown.comp continuous_snd))

/-- A representation with jointly continuous action, lifted to the universe of the Galois
group, as a topological representation. -/
def uliftRep : TopRep.{max u w} Λ (galoisGroup K) :=
  TopRep.of (X := ULift.{u} M) (ContRepresentation.ofMonoidHom
    { toFun g :=
        { toFun m := ⟨ρ g m.down⟩
          map_add' _ _ := congrArg ULift.up (map_add _ _ _)
          map_smul' _ _ := congrArg ULift.up (map_smul _ _ _)
          cont :=
            continuous_uliftUp.comp ((continuous_rep_apply ρ hρ g).comp continuous_uliftDown) }
      map_one' := by
        ext m
        change ρ 1 m.down = m.down
        rw [map_one]
        rfl
      map_mul' g h := by
        ext m
        change ρ (g * h) m.down = ρ g (ρ h m.down)
        rw [map_mul]
        rfl })

/-- The action of `g` on the lifted representation is the action of `g` on `M`, lifted. -/
lemma uliftRep_ρ_apply (g : galoisGroup K) (m : ULift.{u} M) :
    (uliftRep ρ hρ).ρ g m = ⟨ρ g m.down⟩ := rfl

/-- The sheaf of continuous equivariant functions with values in `M` is the one with values in
the lift of `M`. -/
def contSheafIsoRepSheaf :
    contSheaf Λ ρ ≅ (repSheaf Λ).obj (uliftRep.{u} ρ hρ) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun _ ↦
    LinearEquiv.toModuleIso
      { toFun a := ⟨⟨fun φ ↦ ⟨a.down.1 φ⟩, fun g φ ↦ congrArg ULift.up (a.down.2.1 g φ),
          fun A f hA ↦ continuous_uliftUp.comp (a.down.2.2 A f hA)⟩⟩
        invFun a := ⟨⟨fun φ ↦ (a.down.1 φ).down, fun g φ ↦ congrArg ULift.down (a.down.2.1 g φ),
          fun A f hA ↦ continuous_uliftDown.comp (a.down.2.2 A f hA)⟩⟩
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        left_inv _ := rfl
        right_inv _ := rfl }) (fun _ ↦ rfl))

end ULift

/-! ### Good coefficients from a complete quotient system -/

section Good

variable {M : Type w} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The universe lift of a nonarchimedean additive group is nonarchimedean. -/
instance nonarchimedeanAddGroup_ulift [NonarchimedeanAddGroup M] :
    NonarchimedeanAddGroup (ULift.{u} M) where
  is_nonarchimedean U hU := by
    obtain ⟨N, hN⟩ := NonarchimedeanAddGroup.is_nonarchimedean (ULift.up ⁻¹' U)
      (continuous_uliftUp.continuousAt.preimage_mem_nhds hU)
    exact ⟨N.comap (AddEquiv.ulift : ULift.{u} M ≃+ M).toAddMonoidHom continuous_uliftDown,
      fun x hx ↦ hN hx⟩

omit [IsTopologicalAddGroup M] in
/-- The universe lift of a pro-discrete group is pro-discrete. -/
lemma isProDiscrete_ulift (h : Stacks.ProfiniteCech.IsProDiscrete M) :
    Stacks.ProfiniteCech.IsProDiscrete (ULift.{u} M) := by
  intro f hf
  let dn := (AddEquiv.ulift : ULift.{u} M ≃+ M).toAddMonoidHom
  let up := (AddEquiv.ulift : ULift.{u} M ≃+ M).symm.toAddMonoidHom
  obtain ⟨y, hy⟩ := h (fun N ↦ (f (N.comap dn continuous_uliftDown)).down) fun N N' hNN' ↦
    hf (N.comap dn continuous_uliftDown) (N'.comap dn continuous_uliftDown) fun x hx ↦ hNN' hx
  exact ⟨⟨y⟩, fun N ↦ hy (N.comap up continuous_uliftUp)⟩

variable {Λ : Type r} [Ring Λ] [Module Λ M] (ρ : Representation Λ (galoisGroup K) M)
  {J : Type t} [Category.{t'} J] (D : J ⥤ Subrepresentation ρ)
  (hopen : ∀ j, IsOpen ((D.obj j).toSubmodule : Set M))
  (hbasis : ∀ U ∈ 𝓝 (0 : M), ∃ j, ((D.obj j).toSubmodule : Set M) ⊆ U)
  (hsep : ∀ m : M, (∀ j, m ∈ (D.obj j).toSubmodule) → m = 0)
  (hcomp : ∀ x : ∀ j, M ⧸ (D.obj j).toSubmodule,
    (∀ j j' (f : j ⟶ j'), (D.obj j).toSubmodule.mapQ (D.obj j').toSubmodule LinearMap.id
      (leOfHom (D.map f)) (x j) = x j') →
    ∃ m : M, ∀ j, (D.obj j).toSubmodule.mkQ m = x j)

/-- A member of the quotient system, as an open subgroup. -/
def quotientSystemSubgroup (j : J) : OpenAddSubgroup M :=
  ⟨(D.obj j).toSubmodule.toAddSubgroup, hopen j⟩

include hopen hbasis in
/-- A group with a basis of neighbourhoods of zero consisting of open subgroups is
nonarchimedean. -/
lemma nonarchimedean_of_quotientSystem : NonarchimedeanAddGroup M where
  is_nonarchimedean U hU := by
    obtain ⟨j, hj⟩ := hbasis U hU
    exact ⟨quotientSystemSubgroup ρ D hopen j, hj⟩

include hopen hsep in
/-- A topological group whose open subgroups `Nⱼ` of a system intersect in zero is Hausdorff. -/
lemma t2Space_of_quotientSystem : T2Space M := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx ↦ ?_
  by_contra! h
  exact hx (hsep x fun j ↦ h _ ((hopen j).mem_nhds (D.obj j).toSubmodule.zero_mem))

omit [IsTopologicalAddGroup M] in
include hopen hbasis hcomp in
/-- A group which is complete with respect to a system of open subgroups forming a basis of
neighbourhoods of zero is pro-discrete. -/
lemma isProDiscrete_of_quotientSystem : Stacks.ProfiniteCech.IsProDiscrete M := by
  intro f hf
  let N := quotientSystemSubgroup ρ D hopen
  obtain ⟨m, hm⟩ := hcomp (fun j ↦ (D.obj j).toSubmodule.mkQ (f (N j))) fun j j' g ↦ by
    change (D.obj j').toSubmodule.mkQ (f (N j)) = (D.obj j').toSubmodule.mkQ (f (N j'))
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact hf (N j) (N j') (leOfHom (D.map g))
  refine ⟨m, fun N' ↦ ?_⟩
  obtain ⟨j, hj⟩ := hbasis _ (N'.isOpen.mem_nhds N'.zero_mem)
  have h₁ : m - f (N j) ∈ N j := (Submodule.Quotient.eq _).1 (hm j)
  simpa using N'.add_mem (hj h₁) (hf (N j) N' hj)

end Good

/-! ### The comparison for a complete quotient system -/

section Comparison

variable {Λ : Type r} [Ring Λ] [TopologicalSpace Λ] {M : Type w} [AddCommGroup M] [Module Λ M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul Λ M]
  (ρ : Representation Λ (galoisGroup K) M) (hρ : Continuous fun p : galoisGroup K × M ↦ ρ p.1 p.2)
  {J : Type t} [Category.{t'} J] (D : J ⥤ Subrepresentation ρ)
  (hopen : ∀ j, IsOpen ((D.obj j).toSubmodule : Set M))
  (hbasis : ∀ U ∈ 𝓝 (0 : M), ∃ j, ((D.obj j).toSubmodule : Set M) ⊆ U)
  (hsep : ∀ m : M, (∀ j, m ∈ (D.obj j).toSubmodule) → m = 0)
  (hcomp : ∀ x : ∀ j, M ⧸ (D.obj j).toSubmodule,
    (∀ j j' (f : j ⟶ j'), (D.obj j).toSubmodule.mapQ (D.obj j').toSubmodule LinearMap.id
      (leOfHom (D.map f)) (x j) = x j') →
    ∃ m : M, ∀ j, (D.obj j).toSubmodule.mkQ m = x j)

include hopen hbasis hsep hcomp in
/-- The lift of `M` is a good coefficient representation when `M` is separated and complete
with respect to a system of open submodules forming a basis of neighbourhoods of zero. -/
lemma goodCoefficients_uliftRep : GoodCoefficients (uliftRep.{u} ρ hρ) := by
  have := nonarchimedean_of_quotientSystem ρ D hopen hbasis
  have := t2Space_of_quotientSystem ρ D hopen hsep
  refine ⟨?_, nonarchimedeanAddGroup_ulift,
    (Homeomorph.ulift.{u} (X := M)).isEmbedding.t2Space,
    isProDiscrete_ulift (isProDiscrete_of_quotientSystem ρ D hopen hbasis hcomp)⟩
  exact continuous_uliftUp.comp (hρ.comp (continuous_fst.prodMk
    (continuous_uliftDown.comp continuous_snd)))

/-- **The pro-étale cohomology of the completed sheaf `limⱼ ε⁻¹(M/Nⱼ)` is the continuous
cohomology of `M`**, for a system of open submodules which is a basis of neighbourhoods of zero
for which `M` is separated and complete. -/
def rightDerivedCompletionIso [Small.{max (u + 1) r w} J] (n : ℕ) :
    letI := hasSheafify_galois.{u, r, w} K
    letI := enoughInjectives_galois.{u, r, w} K
    letI := Stacks.Cohomology.GlobalSections.additive_Γ.{max r w, u, u + 1}
      (Scheme.ProEt.topology (base K))
    ((Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).rightDerived n).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat)).obj
        (completion.{t, t', u, r, w} ρ D)) ≅
      (underlyingAb.{u, r, w} Λ).obj (continuousCohomology n (uliftRep.{u} ρ hρ)) :=
  letI := hasSheafify_galois.{u, r, w} K
  letI := enoughInjectives_galois.{u, r, w} K
  letI := Stacks.Cohomology.GlobalSections.additive_Γ.{max r w, u, u + 1}
    (Scheme.ProEt.topology (base K))
  ((Sheaf.Γ _ _).rightDerived n).mapIso ((sheafCompose _ _).mapIso
      (completionIsoContSheaf ρ D hopen hbasis hsep hcomp ≪≫ contSheafIsoRepSheaf ρ hρ)) ≪≫
    rightDerivedRepAbSheafIso (uliftRep.{u} ρ hρ)
      (goodCoefficients_uliftRep ρ hρ D hopen hbasis hsep hcomp) n

end Comparison

/-! ### Case (2): adically complete modules -/

section Adic

variable (K) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ) (M : Type w)
  [AddCommGroup M] [Module Λ M] [IsAdicComplete I M]

omit [IsNoetherianRing Λ] [IsAdicComplete I M] in
/-- Each submodule `IⁿM` is open for the `I`-adic topology on `M`. -/
lemma adic_hopen (ρ : Representation Λ (galoisGroup K) M) (j : ℕᵒᵖ) :
    letI := I.adicModuleTopology M
    IsOpen (((adicDiagram Λ I ρ).obj j).toSubmodule : Set M) :=
  let : TopologicalSpace Λ := I.ringFilterBasis.topology
  let := I.adicModuleTopology M
  ((I.ringFilterBasis.submodulesBasisIsBasis (I.adic_module_basis M)).openAddSubgroup
    j.unop).isOpen

omit [IsNoetherianRing Λ] [IsAdicComplete I M] in
/-- The submodules `IⁿM` form a basis of neighbourhoods of zero for the `I`-adic topology. -/
lemma adic_hbasis (ρ : Representation Λ (galoisGroup K) M) :
    letI := I.adicModuleTopology M
    ∀ U ∈ 𝓝 (0 : M), ∃ j, (((adicDiagram Λ I ρ).obj j).toSubmodule : Set M) ⊆ U := by
  let : TopologicalSpace Λ := I.ringFilterBasis.topology
  let := I.adicModuleTopology M
  intro U hU
  obtain ⟨-, ⟨i, rfl⟩, hi⟩ := (I.ringFilterBasis.submodulesBasisIsBasis
    (I.adic_module_basis M)).toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp
      hU
  exact ⟨Opposite.op i, hi⟩

omit [IsNoetherianRing Λ] in
/-- An element of an `I`-adically complete module lying in every `IⁿM` is zero. -/
lemma adic_hsep (ρ : Representation Λ (galoisGroup K) M) (m : M)
    (hm : ∀ j, m ∈ ((adicDiagram Λ I ρ).obj j).toSubmodule) : m = 0 :=
  IsHausdorff.haus (I := I) inferInstance m fun n ↦ by
    rw [SModEq.zero]
    exact hm (Opposite.op n)

omit [IsNoetherianRing Λ] in
/-- A compatible family of elements of the quotients `M/IⁿM` of an `I`-adically complete module
comes from an element of `M`. -/
lemma adic_hcomp (ρ : Representation Λ (galoisGroup K) M)
    (x : ∀ j, M ⧸ ((adicDiagram Λ I ρ).obj j).toSubmodule)
    (hx : ∀ j j' (f : j ⟶ j'), ((adicDiagram Λ I ρ).obj j).toSubmodule.mapQ
      ((adicDiagram Λ I ρ).obj j').toSubmodule LinearMap.id
      (leOfHom ((adicDiagram Λ I ρ).map f)) (x j) = x j') :
    ∃ m : M, ∀ j, ((adicDiagram Λ I ρ).obj j).toSubmodule.mkQ m = x j := by
  let f : ℕ → M := fun n ↦ (x (Opposite.op n)).out
  have hf : ∀ n, ((adicDiagram Λ I ρ).obj (Opposite.op n)).toSubmodule.mkQ (f n) =
      x (Opposite.op n) := fun n ↦ Quotient.out_eq _
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance (f := f) fun {m n} hmn ↦ by
    have h := hx (Opposite.op n) (Opposite.op m) (homOfLE hmn).op
    rw [← hf n, ← hf m] at h
    exact h.symm
  refine ⟨L, fun j ↦ ?_⟩
  rw [← hf j.unop]
  exact (hL j.unop).symm

/-- Let `K` be a field with absolute Galois group `G`, let `Λ` be a Noetherian ring with an ideal
`I`, and let `M` be an `I`-adically complete `Λ`-module with a continuous action of `G` for the
`I`-adic topology. Then the pro-étale cohomology of `Spec K` with coefficients in the completed
sheaf `M^∧ = limₙ ε⁻¹(M/IⁿM)` is the continuous cohomology of `G` with coefficients in `M`:

  `Hⁱ(Spec(K)_proét, M^∧) ≅ Hⁱ_cont(G, M)`.

Here `Λ` and `M` carry their `I`-adic topologies, pro-étale cohomology is the `i`-th right
derived functor of global sections of the underlying abelian sheaf, and the identification is of
abelian groups, the right hand side being lifted to the coefficient universe of the site. -/
@[stacks 09B4 "case (2), the cohomology comparison"]
def rightDerivedAdicSheafIso
    (ρ : Representation Λ (galoisGroup K) M)
    (hρ : letI := I.adicModuleTopology M
      Continuous fun p : galoisGroup K × M ↦ ρ p.1 p.2) (i : ℕ) :
    letI : TopologicalSpace Λ := I.adicTopology
    letI := I.adicModuleTopology M
    letI := hasSheafify_galois.{u, r, w} K
    letI := enoughInjectives_galois.{u, r, w} K
    letI := Stacks.Cohomology.GlobalSections.additive_Γ.{max r w, u, u + 1}
      (Scheme.ProEt.topology (base K))
    ((Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) r w}).rightDerived i).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat)).obj
        (adicSheaf Λ K I M ρ hρ)) ≅
      (underlyingAb.{u, r, w} Λ).obj (continuousCohomology i (uliftRep.{u} ρ hρ)) :=
  letI : TopologicalSpace Λ := I.adicTopology
  letI := I.adicModuleTopology M
  rightDerivedCompletionIso ρ hρ (adicDiagram Λ I ρ) (adic_hopen K Λ I M ρ)
    (adic_hbasis K Λ I M ρ) (adic_hsep K Λ I M ρ) (adic_hcomp K Λ I M ρ) i

end Adic

/-! ### Case (1): profinite abelian groups -/

section Profinite

variable (K) {M : Type w} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
  (ρ : Representation ℤ (galoisGroup K) M) (hρ : Continuous fun p : galoisGroup K × M ↦ ρ p.1 p.2)

/-- Every neighbourhood of zero in a profinite abelian group contains an open subgroup. -/
lemma exists_openAddSubgroup_subset_of_profinite {U : Set M} (hU : U ∈ 𝓝 (0 : M)) :
    ∃ N : OpenAddSubgroup M, (N : Set M) ⊆ U := by
  obtain ⟨W, hW, h0W, hWU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.1 hU
  obtain ⟨N, hN⟩ := IsTopologicalAddGroup.exist_openAddSubgroup_sub_clopen_nhds_of_zero hW h0W
  exact ⟨N, hN.trans hWU⟩

include hρ in
/-- In a profinite abelian group with a continuous action of the Galois group, the open
Galois-stable subgroups form a basis of neighbourhoods of zero. -/
lemma profinite_hbasis :
    ∀ U ∈ 𝓝 (0 : M), ∃ j, (((openStableDiagram ρ).obj j).toSubmodule : Set M) ⊆ U := by
  intro U hU
  obtain ⟨N₀, hN₀⟩ := exists_openAddSubgroup_subset_of_profinite hU
  have hev : ∀ᶠ m in 𝓝 (0 : M), ∀ g ∈ (Set.univ : Set (galoisGroup K)), ρ g m ∈ N₀ :=
    isCompact_univ.eventually_forall_of_forall_eventually fun g _ ↦ by
      have hc : ContinuousAt (fun z : M × galoisGroup K ↦ ρ z.2 z.1) (0, g) :=
        (hρ.comp continuous_swap).continuousAt
      have h0 : ρ g 0 ∈ N₀ := by rw [map_zero]; exact N₀.zero_mem
      exact hc.eventually_mem (N₀.isOpen.mem_nhds h0)
  obtain ⟨N₁, hN₁⟩ := exists_openAddSubgroup_subset_of_profinite hev
  let S : AddSubgroup M := AddSubgroup.closure (⋃ g, ρ g '' N₁)
  have hSN₀ : S ≤ N₀ := (AddSubgroup.closure_le _).2 (Set.iUnion_subset fun g ↦ by
    rintro _ ⟨m, hm, rfl⟩
    exact hN₁ hm g trivial)
  have hN₁S : N₁.toAddSubgroup ≤ S := fun m hm ↦
    AddSubgroup.subset_closure (Set.mem_iUnion.2 ⟨1, m, hm, by rw [map_one]; rfl⟩)
  have hstable : ∀ g, S ≤ S.comap (ρ g).toAddMonoidHom := fun g ↦
    (AddSubgroup.closure_le _).2 (Set.iUnion_subset fun h ↦ by
      rintro _ ⟨n, hn, rfl⟩
      refine AddSubgroup.subset_closure (Set.mem_iUnion.2 ⟨g * h, n, hn, ?_⟩)
      rw [map_mul]
      rfl)
  let R : Subrepresentation ρ := ⟨S.toIntSubmodule, fun g m hm ↦ hstable g hm⟩
  exact ⟨⟨R, AddSubgroup.isOpen_mono hN₁S N₁.isOpen⟩, fun m hm ↦ hN₀ (hSN₀ hm)⟩

include hρ in
/-- An element of a profinite abelian group with a continuous Galois action lying in every open
Galois-stable subgroup is zero. -/
lemma profinite_hsep (m : M) (hm : ∀ j, m ∈ ((openStableDiagram ρ).obj j).toSubmodule) :
    m = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := profinite_hbasis K ρ hρ _ (isOpen_compl_singleton.mem_nhds (Ne.symm h))
  exact hj (hm j) rfl

omit [T2Space M] [TotallyDisconnectedSpace M] in
/-- A compatible family of elements of the quotients `M/N` of a profinite abelian group by its
open Galois-stable subgroups comes from an element of `M`. -/
lemma profinite_hcomp (x : ∀ j, M ⧸ ((openStableDiagram ρ).obj j).toSubmodule)
    (hx : ∀ j j' (f : j ⟶ j'), ((openStableDiagram ρ).obj j).toSubmodule.mapQ
      ((openStableDiagram ρ).obj j').toSubmodule LinearMap.id
      (leOfHom ((openStableDiagram ρ).map f)) (x j) = x j') :
    ∃ m : M, ∀ j, ((openStableDiagram ρ).obj j).toSubmodule.mkQ m = x j := by
  let C : OpenStable ρ → Set M := fun j ↦
    {m | ((openStableDiagram ρ).obj j).toSubmodule.mkQ m = x j}
  have hC : ∀ j, C j = (fun m ↦ m - (x j).out) ⁻¹' (j.1.toSubmodule : Set M) := fun j ↦ by
    ext m
    change ((openStableDiagram ρ).obj j).toSubmodule.mkQ m = x j ↔ _
    conv_lhs => rw [← Quotient.out_eq (x j)]
    exact Submodule.Quotient.eq _
  have : Nonempty (OpenStable ρ) := ⟨⟨⊤, isOpen_univ⟩⟩
  have hclosed : ∀ j, IsClosed (C j) := fun j ↦ by
    rw [hC]
    exact (OpenAddSubgroup.isClosed ⟨j.1.toSubmodule.toAddSubgroup, j.2⟩).preimage
      (continuous_id.sub continuous_const)
  have hmono : ∀ k j : OpenStable ρ, k.1 ≤ j.1 → C k ⊆ C j := fun k j hkj m hm ↦ by
    have := hx k j (homOfLE (show k ≤ j from hkj))
    change _ = x j
    rw [← this, ← hm]
    rfl
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C
    (fun j j' ↦ ⟨⟨j.1 ⊓ j'.1, j.2.inter j'.2⟩, hmono _ _ inf_le_left, hmono _ _ inf_le_right⟩)
    (fun j ↦ ⟨(x j).out, Quotient.out_eq _⟩) (fun j ↦ (hclosed j).isCompact) hclosed
  exact ⟨m, fun j ↦ Set.mem_iInter.1 hm j⟩

/-- Let `K` be a field with absolute Galois group `G` and let `M` be a profinite abelian group
with a continuous action of `G`. Then the pro-étale cohomology of `Spec K` with coefficients in
the completed sheaf `M^∧ = lim_N ε⁻¹(M/N)`, the limit over the open `G`-stable subgroups `N`, is
the continuous cohomology of `G` with coefficients in `M`:

  `Hⁱ(Spec(K)_proét, M^∧) ≅ Hⁱ_cont(G, M)`.

Pro-étale cohomology is the `i`-th right derived functor of global sections of the underlying
abelian sheaf, and the identification is of abelian groups, the right hand side being lifted to
the coefficient universe of the site. -/
@[stacks 09B4 "case (1), the cohomology comparison"]
def rightDerivedProfiniteSheafIso (i : ℕ) :
    letI := hasSheafify_galois.{u, 0, w} K
    letI := enoughInjectives_galois.{u, 0, w} K
    letI := Stacks.Cohomology.GlobalSections.additive_Γ.{max 0 w, u, u + 1}
      (Scheme.ProEt.topology (base K))
    ((Sheaf.Γ (Scheme.ProEt.topology (base K)) AddCommGrpCat.{max (u + 1) w}).rightDerived i).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{max (u + 1) w} ℤ) AddCommGrpCat)).obj
        (profiniteSheaf K M ρ hρ)) ≅
      (underlyingAb.{u, 0, w} ℤ).obj (continuousCohomology i (uliftRep.{u} ρ hρ)) :=
  rightDerivedCompletionIso ρ hρ (openStableDiagram ρ) (fun j ↦ j.2) (profinite_hbasis K ρ hρ)
    (profinite_hsep K ρ hρ) (profinite_hcomp K ρ) i

end Profinite

end AlgebraicGeometry.GaloisSheaf
