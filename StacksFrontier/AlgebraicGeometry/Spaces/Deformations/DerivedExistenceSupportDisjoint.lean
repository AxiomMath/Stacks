module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportedVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportedAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedAffinePullbackGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePseudoCoherentSections
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsAnnihilatorSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperConnectedFibresOverAffine
public import StacksFrontier.Algebra.Homology.PseudoCoherentLocalVanishing

/-!
# The derived existence theorem: the cohomology of `K` has no support off `X₀`

In the situation of `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` let
`K = DQ_X(R lim Kₙ)` be the object of the existence theorem, and let `Q ⊆ |X|` be closed, with
quasi-compact complement, disjoint from the image of every `|Xₙ|`. Then no cohomology sheaf
`Hⁱ(K)` has a point of its support in `Q`. This is step (L1)(b) of the errata entry
0DIR(support of K), per-degree clause.

## The proof

By `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.isZero_smallEtaleDerivedTensor_…`,
`E ⊗^L K = 0` for every perfect `E` supported on `Q`. Let `u : V = Spec R ⟶ X` be an affine
étale chart. `u` is affine (`X` is separated), so the pullbacks of the perfect objects supported
on `Q` generate the perfect objects of `D(𝒪_V)` supported on `u⁻¹Q` (Stacks 0AEC, 0GFD), and
`P ⊗^L Lu^*K = 0` for all of them. The closed subset `u⁻¹Q ⊆ Spec R` has quasi-compact complement,
so it is `V(f₁, …, f_r)`; the associated object `Φ(N)` of the Koszul object `N = N(f₁, …, f_r)` of
`D(R)` is perfect and supported on `V(f₁, …, f_r)`. Through `D_QCoh(𝒪_V) ≃ D(R)`, this says
`M ⊗^L_R N = 0` for the pseudo-coherent `M = RΓ(V, K)`, and then
`StacksDraft.PseudoCoherence.exists_smul_eq_zero_of_isZero_tensor_iteratedSmulCone` (Nakayama on
the top cohomology over `R_𝔭`) gives `Hⁱ(M)_𝔭 = Γ(V, Hⁱ(K))_𝔭 = 0` for every `𝔭 ∈ V(f)`.

## Main results

* `AlgebraicGeometry.Space.isZero_smallEtaleDerivedTensor_smallEtaleDerivedModulePullback_of_…`:
  the transfer of the vanishing to an affine morphism, by the supported generator.
* `…SupportedDerivedExistenceSystem.disjoint_supportOfSheaf_homology_quasicoherentLimit`: the main
  statement.

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 0AEC](https://stacks.math.columbia.edu/tag/0AEC)
* [Stacks Project, Tag 0GFD](https://stacks.math.columbia.edu/tag/0GFD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite ZeroObject
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] pointTopology

/-! ### Transfer of a tensor vanishing along an affine morphism -/

section Transfer

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A tensor vanishing against the perfect objects supported on `Q` passes to an affine
morphism.** Let `g : W ⟶ X` be an affine morphism of quasi-compact and quasi-separated algebraic
spaces, `Q ⊆ |X|` closed with quasi-compact complement, and `K ∈ D(𝒪_X)` with `E ⊗^L K = 0` for
every perfect `E` with quasi-coherent cohomology supported on `Q`. Then `P ⊗^L Lg^*K = 0` for every
perfect `P ∈ D(𝒪_W)` supported on `g⁻¹Q`: the objects `P` with this property form a thick
subcategory containing the `Lg^*E` (Stacks 07A4), and these generate (Stacks 0AEC, 0GFD). -/
theorem isZero_smallEtaleDerivedTensor_smallEtaleDerivedModulePullback_of_isPerfect
    {X W : AlgebraicSpaces B S hS} (g : W ⟶ X) (hg : IsAffineHom B S hS g.hom)
    (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (Q : Set (points B S hS X.1)) (hQ : IsClosed Q) (hQc : IsCompact Qᶜ)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E → QcohDerived B S hS X E →
        CohomologySupportedOn B S hS X.1 X.2 Q E →
          IsZero (((smallEtaleDerivedTensor B S hS X).obj E).obj K))
    (P : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hP : (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect P)
    (hPs : CohomologySupportedOn B S hS W.1 W.2 (pointsMap B S hS W.1 g.hom ⁻¹' Q) P) :
    IsZero (((smallEtaleDerivedTensor B S hS W).obj P).obj
      ((smallEtaleDerivedModulePullback B S hS g).obj K)) := by
  let L : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) :=
    (smallEtaleDerivedModulePullback B S hS g).obj K
  let F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2) :=
    (smallEtaleDerivedTensorProduct B S hS W).tensor.flip.obj L
  let : F.CommShift ℤ := (smallEtaleDerivedTensorProduct B S hS W).commShift_left L
  have : F.IsTriangulated := (smallEtaleDerivedTensorProduct B S hS W).exact_left L
  let Φ : ObjectProperty (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :=
    fun P => IsZero (F.obj P)
  have : Φ.IsClosedUnderIsomorphisms := ⟨fun e h => h.of_iso (F.mapIso e).symm⟩
  have : Φ.IsStableUnderRetracts := ⟨fun {P P'} r h => by
    change IsZero (F.obj P)
    rw [IsZero.iff_id_eq_zero, ← (r.map F).retract, h.eq_of_src (r.map F).r 0, comp_zero]⟩
  have : Φ.IsTriangulated :=
    { exists_zero := ⟨0, isZero_zero _, F.map_isZero (isZero_zero _)⟩
      isStableUnderShiftBy := fun n => ⟨fun P hP =>
        ((shiftFunctor _ n).map_isZero hP).of_iso ((F.commShiftIso n).app P)⟩
      ext₂' := fun T hT h₁ h₃ => ObjectProperty.le_isoClosure _ _
        (Triangle.isZero₂_of_isZero₁₃ _ (F.map_distinguished T hT) h₁ h₃) }
  refine prop_of_isPerfect_of_cohomologySupportedOn_preimage g hg hWqc hWqs hXqc hXqs Q hQ hQc Φ
    (fun G₀ hG₀ hG₀q hG₀s => ?_) P hP hPs
  exact ((smallEtaleDerivedModulePullback B S hS g).map_isZero (hK G₀ hG₀ hG₀q hG₀s)).of_iso
    ((smallEtaleDerivedPullbackTensorIso g).app (G₀, K)).symm

end Transfer

/-! ### Sections over a chart and supports -/

section Chart

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A point of the support of a quasi-coherent module on an affine chart carries a section whose
annihilator lies in its prime**: on an affine scheme the support of a quasi-coherent module is the
support of its module of global sections (Stacks 056I), and the global sections of `F|_U` are
`F(A)`. -/
theorem exists_forall_smul_eq_zero_mem_of_mem_supp_restrictToChart (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1)
    [IsAffine (chartScheme A)] (x : chartScheme A)
    (hx : x ∈ SheafOfModules.supp (restrictToChart B S hS X.2 M A)) :
    ∃ m : M.val.obj (op A), ∀ r : Γ(chartScheme A, ⊤), r • m = 0 →
      r ∈ ((chartScheme A).isoSpec.hom x).asIdeal := by
  let F : (chartScheme A).Modules := @id (chartScheme A).Modules (restrictToChart B S hS X.2 M A)
  have : F.IsQuasicoherent := isQuasicoherent_restrictToChart B S hS X M hM A
  have hx' : x ∈ SheafOfModules.supp F := hx
  rw [← mem_support_sections_iff_mem_supp_top] at hx'
  obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.1 hx'
  let φ : (Γ(F, ⊤) : Type u) ≃ₗ[Γ(chartScheme A, ⊤)] (M.val.obj (op A) : Type u) :=
    ((moduleGlobalSections (chartScheme A)).mapIso
        (restrictToChartIsoChartRestrictionSheaf B S hS X M A)).toLinearEquiv.trans
      (chartRestrictionSheafTopEquiv B S hS X M A).symm
  refine ⟨φ m, fun r hr => hm ?_⟩
  rw [Submodule.mem_annihilator_span_singleton]
  apply φ.injective
  rw [map_smul, hr, map_zero]

/-- **The cohomology of the derived sections over an affine chart, through the étale
restriction.** For `E ∈ D_QCoh(𝒪_X)` and an affine chart `U` with chart morphism `u`,
`Hⁱ(RΓ_U(u^*E)) ≅ Γ(U, Hⁱ(E))`, for the étale restriction `u^*`. -/
def homologyRepresentedAffineDerivedSectionsEtaleIso (X : AlgebraicSpaces B S hS)
    (U : SmallEtale B S hS X.1) (hU : IsAffineChart B S hS X.1 U)
    (E : spaceDerivedCategory B S hS X) (hE : spaceQuasicoherentProp B S hS X E) (i : ℤ) :
    haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)) :=
      hU
    (DerivedCategory.homologyFunctor _ i).obj
        ((representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj U)).obj
          ((etaleModulePullback.{u, u} B S hS (representedChartToSpace X U)
            (isEtale_representedChartToSpace X U)).mapDerivedCategory.obj E)) ≅
      ((spaceDerivedHomology B S hS X i).obj E).val.obj (op U) :=
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)) :=
    hU
  (DerivedCategory.homologyFunctor _ i).mapIso
      ((asIso (chartDerivedSectionsComparison X U)).app E).symm ≪≫
    (chartDerivedSectionsHomologyIso B S hS X E hE U hU i).symm

/-- **A closed subset of `|X|` with quasi-compact complement is cut out on an affine chart by
finitely many functions.** For an affine chart `U = Spec R` of a quasi-separated `X` and
`Q ⊆ |X|` closed with quasi-compact complement, there are `f₁, …, f_r ∈ R` such that a point `z`
of `U` lies over `Q` exactly when every `fᵢ` vanishes at `z`. -/
theorem exists_list_forall_mem_iff_pointsMap_mem (X : AlgebraicSpaces B S hS)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (U : SmallEtale B S hS X.1) (hU : IsAffineChart B S hS X.1 U)
    (Q : Set (points B S hS X.1)) (hQ : IsClosed Q) (hQc : IsCompact Qᶜ) :
    haveI : IsAffine (chartScheme U) := hU
    ∃ l : List Γ(chartScheme U, ⊤), ∀ z : chartScheme U,
      (∀ a ∈ l, a ∈ ((chartScheme U).isoSpec.hom z).asIdeal) ↔
        pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom
          ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj U)).symm z) ∈ Q := by
  classical
  have : IsAffine (chartScheme U) := hU
  let T := (SmallEtale.toOver B S hS X.1).obj U
  have hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hU
  let g := representedChartToSpace X U
  have hYqc : IsQuasiCompactSpace B S hS (yoneda.obj T) :=
    isQuasiCompactSpace_yoneda_of_isAffine _ _ _ _ hT
  have hc := isCompact_compl_preimage_of_isQuasiCompact g hYqc hXqs Q hQ hQc
  let e := pointsEquivScheme B S hS T
  have he : Continuous e := by
    rw [continuous_def]
    intro O hO
    rw [isOpen_pointTopology_yoneda_iff_isOpen_image]
    rwa [show pointsToScheme B S hS T '' (e ⁻¹' O) = O from
      Set.image_preimage_eq O e.surjective]
  let C : Set (chartScheme U) := e.symm ⁻¹' (pointsMap B S hS (yoneda.obj T) g.hom ⁻¹' Q)
  have hCc : IsClosed C :=
    hQ.preimage ((continuous_pointsMap B S hS g.hom).comp (continuous_pointsEquivScheme_symm T))
  have hCcc : IsCompact Cᶜ := by
    rw [show Cᶜ = e '' (pointsMap B S hS (yoneda.obj T) g.hom ⁻¹' Q)ᶜ by
      rw [e.image_eq_preimage_symm]
      rfl]
    exact hc.image he
  let h : chartScheme U ≃ₜ PrimeSpectrum Γ(chartScheme U, ⊤) :=
    Scheme.homeoOfIso (chartScheme U).isoSpec
  obtain ⟨t, ht⟩ := (PrimeSpectrum.isCompact_isOpen_iff (s := (h '' C)ᶜ)).1
    ⟨by rw [← h.image_compl]; exact hCcc.image h.continuous,
      (h.isClosedMap C hCc).isOpen_compl⟩
  refine ⟨t.toList, fun z => ?_⟩
  have hzt : (∀ a ∈ t.toList, a ∈ ((chartScheme U).isoSpec.hom z).asIdeal) ↔
      h z ∈ PrimeSpectrum.zeroLocus (t : Set Γ(chartScheme U, ⊤)) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    simp only [Finset.mem_toList]
    exact Iff.rfl
  rw [hzt, show PrimeSpectrum.zeroLocus (t : Set Γ(chartScheme U, ⊤)) = h '' C from
    compl_injective ht, h.injective.mem_set_image]
  rfl

end Chart

/-! ### The Koszul object on an affine represented algebraic space -/

section Koszul

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The associated object of a Koszul object is supported on the zero locus of its list.** For
`T` affine with ring `R` and `l` a list of elements of `R`, the cohomology sheaves of `Φ(N(l))`
are supported on the points of `h_T` at which every member of `l` vanishes: each member of `l`
kills a power of every `Hⁱ(N(l))`, and `Γ(Hⁱ(Φ(N(l)))) = Hⁱ(N(l))`. -/
theorem cohomologySupportedOn_representedAffineDerivedAssociated_iteratedSmulCone
    (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (l : List Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    CohomologySupportedOn B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
      {y | ∀ a ∈ l, a ∈ (((BigFppfOver.toScheme B S hS).obj T).isoSpec.hom
        (pointsEquivScheme B S hS T y)).asIdeal}
      ((representedAffineDerivedAssociated B S hS T).obj
        (StacksDraft.PseudoCoherence.iteratedSmulCone l)) := by
  intro i y hy a ha
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let A := representedAffineFinalChart B S hS T
  have hA : IsAffineChart B S hS (yoneda.obj T) A :=
    isAffineChart_representedAffineFinalChart B S hS T
  have : IsAffine (chartScheme A) := hA
  let N := StacksDraft.PseudoCoherence.iteratedSmulCone l
  let E := (representedAffineDerivedAssociated B S hS T).obj N
  have hE : QcohDerived B S hS Y E := qcohDerived_representedAffineDerivedAssociated_obj B S hS T N
  let F := (spaceDerivedHomology B S hS Y i).obj E
  have hF : F.IsQuasicoherentOnSite := hE i
  let z := pointsEquivScheme B S hS T y
  have hz : z ∈ SheafOfModules.supp (restrictToChart B S hS Y.2 F A) := by
    rw [supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS Y A F,
      Set.mem_preimage]
    change pointsMap B S hS (yoneda.obj T) (𝟙 _) ((pointsEquivScheme B S hS T).symm z) ∈
      supportOfSheaf B S hS (yoneda.obj T) ((SheafOfModules.toSheaf _).obj F)
    rw [pointsMap_id, id_eq, Equiv.symm_apply_apply]
    exact hy
  obtain ⟨m, hm⟩ := exists_forall_smul_eq_zero_mem_of_mem_supp_restrictToChart Y F hF A z hz
  obtain ⟨k, hk⟩ := StacksDraft.PseudoCoherence.exists_pow_smul_homology_iteratedSmulCone_eq_zero
    l a ha
  let e : (DerivedCategory.homologyFunctor _ i).obj N ≅ F.val.obj (op A) :=
    (DerivedCategory.homologyFunctor _ i).mapIso
      (asIso ((representedAffineDerivedAdjunction B S hS T).unit.app N) ≪≫
        (representedAffineDerivedSections B S hS T).mapIso
          ((etaleRestrictIdIso B S hS Y (isEtale_representedChartToSpace Y A)).app E).symm) ≪≫
      homologyRepresentedAffineDerivedSectionsEtaleIso Y A hA E hE i
  refine (((chartScheme A).isoSpec.hom z).isPrime).mem_of_pow_mem k (hm (a ^ k) ?_)
  have := congrArg e.toLinearEquiv (hk i (e.toLinearEquiv.symm m))
  rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] at this
  exact this

end Koszul

/-! ### The cohomology of `K` off `X₀` -/

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance 10000] HasDerivedCategory.standard

namespace SupportedDerivedExistenceSystem

variable (D : SupportedDerivedExistenceSystem.{u})

/-- **On an affine chart, the sections of `Hⁱ(K)` vanish at the points over `Q`.** Let
`Q ⊆ |X|` be closed, with quasi-compact complement, disjoint from the image of every `|Xₙ|`, and
let `U = Spec R` be an affine étale chart of `X`. Every section of `Hⁱ(K)` over `U` is killed by
a function not vanishing at a given point `z` of `U` over `Q`: with `Q ∩ U = V(f₁, …, f_r)`,
`M ⊗^L_R N(f) = 0` for `M = RΓ(U, K)` (`Φ(N(f))` is perfect and supported on `Q ∩ U`), and
`M` is pseudo-coherent. -/
theorem exists_smul_eq_zero_homology_quasicoherentLimit_of_mem
    (Q : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1)) (hQ : IsClosed Q)
    (hQc : IsCompact Qᶜ)
    (hdisj : ∀ n : ℕ, Disjoint (Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase
      _ (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom)) Q)
    (U : SmallEtale D.B (limitBase D.system) D.containsLimitBase D.X.left.1)
    (hU : IsAffineChart D.B (limitBase D.system) D.containsLimitBase D.X.left.1 U) (i : ℤ)
    (z : chartScheme U)
    (hz : pointsMap D.B (limitBase D.system) D.containsLimitBase
      (yoneda.obj ((SmallEtale.toOver D.B (limitBase D.system) D.containsLimitBase
        D.X.left.1).obj U)) U.obj.hom
      ((pointsEquivScheme D.B (limitBase D.system) D.containsLimitBase
        ((SmallEtale.toOver D.B (limitBase D.system) D.containsLimitBase D.X.left.1).obj U)).symm
        z) ∈ Q)
    (m : ((spaceDerivedHomology D.B (limitBase D.system) D.containsLimitBase D.X.left i).obj
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
        D.quasicoherentLimit)).val.obj (op U)) :
    haveI : IsAffine (chartScheme U) := hU
    ∃ s : Γ(chartScheme U, ⊤), s ∉ ((chartScheme U).isoSpec.hom z).asIdeal ∧ s • m = 0 := by
  classical
  let B := D.B
  let S := limitBase D.system
  let hS := D.containsLimitBase
  let X := D.X.left
  let K := (spaceQuasicoherentProp B S hS X).ι.obj D.quasicoherentLimit
  have : IsAffine (chartScheme U) := hU
  let T := (SmallEtale.toOver B S hS X.1).obj U
  have hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hU
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩
  let u := representedChartToSpace X U
  have hYqc : IsQuasiCompactSpace B S hS Y.1 := isQuasiCompactSpace_yoneda_of_isAffine _ _ _ _ hT
  have hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1 :=
    isAbsolutelyQuasiSeparated_of_isAffineSpace _ _ _ _ (isAffineSpace_yoneda _ _ _ _ hT)
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS D.X.hom
      D.finitePresentation.2.1
      (isAffineSpace_yoneda _ _ _ _ D.isAffine_limitBaseObject)
  have hXqs := D.isAbsolutelyQuasiSeparated
  have hu : IsAffineHom B S hS u.hom :=
    isAffineHom_of_isAffineSpace_source_of_isAbsolutelySeparated B S hS B.contains_terminal u.hom
      (isAffineSpace_yoneda _ _ _ _ hT) D.isAbsolutelySeparated
  obtain ⟨l, hl⟩ := exists_list_forall_mem_iff_pointsMap_mem X hXqs U hU Q hQ hQc
  let p := ((chartScheme U).isoSpec.hom z).asIdeal
  have : p.IsPrime := ((chartScheme U).isoSpec.hom z).isPrime
  have hlp : ∀ a ∈ l, a ∈ p := (hl z).2 hz
  -- the Koszul object and its associated object `P`, perfect and supported on `u⁻¹Q`
  let N := StacksDraft.PseudoCoherence.iteratedSmulCone l
  let P := (representedAffineDerivedAssociated B S hS T).obj N
  have hP : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect P :=
    isPerfect_representedAffineDerivedAssociated_obj B S hS T N
      (StacksDraft.PseudoCoherence.isPerfect_iteratedSmulCone l)
  have hPs : CohomologySupportedOn B S hS Y.1 Y.2 (pointsMap B S hS Y.1 u.hom ⁻¹' Q) P :=
    fun j => (cohomologySupportedOn_representedAffineDerivedAssociated_iteratedSmulCone T l j).trans
      fun y hy => by
        have := (hl _).1 hy
        rwa [Equiv.symm_apply_apply] at this
  -- `P ⊗^L Lu^*K = 0`
  have hz0 := isZero_smallEtaleDerivedTensor_smallEtaleDerivedModulePullback_of_isPerfect u hu hYqc
    hYqs hXqc hXqs Q hQ hQc K (fun E hE _ hEs =>
      D.isZero_smallEtaleDerivedTensor_quasicoherentLimit_of_cohomologySupportedOn E hE Q hQ hEs
        hdisj) P hP hPs
  -- the module side: `M ⊗^L N = 0` for `M = RΓ(U, K)`
  let L := (smallEtaleDerivedModulePullback B S hS u).obj K
  have hLq : QcohDerived B S hS Y L :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS u K D.quasicoherentLimit.property
  let M := (representedAffineDerivedSections B S hS T).obj L
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS T L hLq
  let cL : (representedAffineDerivedAssociated B S hS T).obj M ≅ L :=
    asIso ((representedAffineDerivedAdjunction B S hS T).counit.app L)
  have h1 : IsZero (((smallEtaleDerivedTensor B S hS Y).obj P).obj
      ((representedAffineDerivedAssociated B S hS T).obj M)) :=
    hz0.of_iso (((smallEtaleDerivedTensor B S hS Y).obj P).mapIso cL)
  have h2 : IsZero ((representedAffineDerivedAssociated B S hS T).obj
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor _).obj N).obj M)) :=
    h1.of_iso (((representedAffineDerivedTensorBifunctorIso B S hS T).app N).app M).symm
  have h3 : IsZero (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor _).obj
      N).obj M) :=
    ((representedAffineDerivedSections B S hS T).map_isZero h2).of_iso
      (asIso ((representedAffineDerivedAdjunction B S hS T).unit.app _))
  have h4 : IsZero (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor _).obj
      M).obj N) :=
    h3.of_iso (((CochainComplex.DerivedTensor.derivedTensorProductKoszulBraiding _).iso.app
      M).app N)
  -- `M` is pseudo-coherent
  have hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M := by
    obtain ⟨K', ψ, hK'eq, hpc, -⟩ :=
      D.exists_eq_quasicoherentLimit_isPseudoCoherentOnLimit_stageDerivedPullback_iso
        D.stageSectionsPseudoCoherent
    rw [hK'eq] at hpc
    rw [@StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _ _ (_)]
    intro m'
    obtain ⟨L', hL', e'⟩ := hpc
    exact isPseudoCoherentFrom_representedAffineDerivedSections_obj B S hS T L hLq m'
      (isPseudoCoherentFrom_smallEtaleDerivedModulePullback_general u K m' ⟨L', hL' m', e'⟩)
  -- vanishing at `𝔭`, and transport to the sections of `Hⁱ(K)` over `U`
  have hloc := StacksDraft.PseudoCoherence.exists_smul_eq_zero_of_isZero_tensor_iteratedSmulCone
    p hM l hlp h4 i
  let e : (DerivedCategory.homologyFunctor _ i).obj M ≅
      ((spaceDerivedHomology B S hS X i).obj K).val.obj (op U) :=
    (DerivedCategory.homologyFunctor _ i).mapIso
        ((representedAffineDerivedSections B S hS T).mapIso
          ((smallEtaleDerivedModulePullbackIsoEtale B S hS u
            (isEtale_representedChartToSpace X U)).app K)) ≪≫
      homologyRepresentedAffineDerivedSectionsEtaleIso X U hU K D.quasicoherentLimit.property i
  obtain ⟨s, hs, hsm⟩ := hloc (e.toLinearEquiv.symm m)
  refine ⟨s, hs, ?_⟩
  have := congrArg e.toLinearEquiv hsm
  rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] at this
  exact this

/-- **The cohomology sheaves of `K` have no support on a closed subset missing `X₀`.** In the
situation of `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem` let
`K = DQ_X(R lim Kₙ)`, and let `Q ⊆ |X|` be closed, with quasi-compact complement, and disjoint
from the image of every `|Xₙ|`. Then for every `i` the support of `Hⁱ(K)` is disjoint from `Q`.
This is step (L1)(b) of the errata entry 0DIR(support of K), per-degree clause. -/
theorem disjoint_supportOfSheaf_homology_quasicoherentLimit
    (Q : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1)) (hQ : IsClosed Q)
    (hQc : IsCompact Qᶜ)
    (hdisj : ∀ n : ℕ, Disjoint (Set.range (pointsMap D.B (limitBase D.system) D.containsLimitBase
      _ (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n).hom)) Q)
    (i : ℤ) :
    Disjoint
      (supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
            D.X.left.2).O)).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} D.B (limitBase D.system)
            D.containsLimitBase D.X.left.1 D.X.left.2) i).obj
            ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
              D.X.left).ι.obj D.quasicoherentLimit)))) Q := by
  let B := D.B
  let S := limitBase D.system
  let hS := D.containsLimitBase
  let X := D.X.left
  let K := (spaceQuasicoherentProp B S hS X).ι.obj D.quasicoherentLimit
  rw [Set.disjoint_left]
  intro x hx hxQ
  obtain ⟨W, b, hWaff, hb, w, hw⟩ := exists_affine_etale_chart_at_point B S hS X.1 X.2 x
  let U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk b, hb⟩
  have hU : IsAffineChart B S hS X.1 U := hWaff
  have : IsAffine (chartScheme U) := hWaff
  let F := (spaceDerivedHomology B S hS X i).obj K
  have hF : F.IsQuasicoherentOnSite := D.quasicoherentLimit.property i
  let z := pointsEquivScheme B S hS W w
  have hzx :
      pointsMap B S hS (yoneda.obj W) U.obj.hom ((pointsEquivScheme B S hS W).symm z) = x := by
    rw [Equiv.symm_apply_apply]
    exact hw
  have hz : z ∈ SheafOfModules.supp (restrictToChart B S hS X.2 F U) := by
    rw [supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent, Set.mem_preimage]
    change pointsMap B S hS (yoneda.obj W) U.obj.hom ((pointsEquivScheme B S hS W).symm z) ∈ _
    rw [hzx]
    exact hx
  obtain ⟨m, hm⟩ := exists_forall_smul_eq_zero_mem_of_mem_supp_restrictToChart X F hF U z hz
  obtain ⟨s, hs, hsm⟩ := D.exists_smul_eq_zero_homology_quasicoherentLimit_of_mem Q hQ hQc hdisj U
    hU i z (hzx ▸ hxQ) m
  exact hs (hm s hsm)

end SupportedDerivedExistenceSystem


end AlgebraicGeometry.Space

end
