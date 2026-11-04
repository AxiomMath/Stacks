module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveOpcyclesOfPerfectRepresentative
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.RingShriekCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatOfProjectiveStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Constructible flat representatives of complexes with perfect stalks

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site and `Λ` a (left)
Noetherian ring, **not necessarily commutative**. Let `K ∈ D(X_étale, Λ)` be a bounded object
whose cohomology sheaves are constructible and whose stalk at every geometric point is a perfect
complex of `Λ`-modules. Then `K` is represented by a bounded complex of constructible flat sheaves
of `Λ`-modules, i.e. it satisfies condition (2) of [Stacks, Tag 03TT].

This is the implication (1) ⟹ (2) of Tag 03TT in the form available for the finite, possibly
noncommutative, coefficient rings of the trace formula (Tag 03SZ). The source states (1) as
"constructible cohomology and finite Tor dimension" for a commutative Noetherian ring; for a
noncommutative ring finite Tor dimension is formulated here through the stalks: a bounded complex
with constructible cohomology on a quasi-compact quasi-separated scheme has finite Tor dimension
exactly when its stalks are perfect. On a quasi-compact quasi-separated scheme condition (2) is
`Stacks.EtaleCohomology.IsCtf` (`Stacks.EtaleCohomology.isCtf_iff_of_qcqs`).

## Main results

* `Stacks.EtaleCohomology.isRepresentedByConstructibleFlatEtaleComplex_of_isPerfect`: a bounded
  object with constructible cohomology sheaves and perfect stalks is represented by a bounded
  complex of constructible flat sheaves.
* `Stacks.EtaleCohomology.isCtf_of_isPerfect_derivedEtaleModuleStalk`: such an object lies in
  `D_ctf(X_étale, Λ)`.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
* [Stacks Project, Tag 03SZ](https://stacks.math.columbia.edu/tag/03SZ)
* [Stacks Project, Tag 093B](https://stacks.math.columbia.edu/tag/093B)
* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ZeroObject

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModules_ab5OfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]

/-- Projectivity of a module is invariant under linear equivalence. -/
private theorem module_projective_iff_of_linearEquiv {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    Module.Projective R M ↔ Module.Projective R N :=
  ⟨fun _ => .of_equiv' e, fun _ => .of_equiv' e.symm⟩

/-- **Tag 03TT, (1) ⟹ (2), over a noncommutative Noetherian ring.** Let `X` be a quasi-compact
and quasi-separated scheme of a big étale site and `Λ` a Noetherian ring, not necessarily
commutative. An object `K` of `D(X_étale, Λ)` with cohomology sheaves vanishing outside `[a, b]`,
all constructible, and with perfect stalks at every geometric point, is represented by a bounded
complex of constructible flat sheaves of `Λ`-modules. Stalks at geometric points over the same
point of `X` are isomorphic, so perfectness is asked only at the geometric point
`AlgebraicGeometry.GeometricPoint.ofPoint` over each point, whose residue field is an algebraic
closure of the residue field there. -/
theorem isRepresentedByConstructibleFlatEtaleComplex_of_isPerfect
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] [IsNoetherianRing Λ]
    (K : DerivedCategory (EtaleModules.{u, r} Λ X.obj))
    (hc : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ ((etaleModulesToSmallEtale B X Λ).obj
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ X.obj) i).obj K)))
    (a b : ℤ)
    (hge : ∀ i < a,
      IsZero ((DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ X.obj) i).obj K))
    (hle : ∀ i, b < i →
      IsZero ((DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ X.obj) i).obj K))
    (hperf : ∀ x : X.obj, StacksDraft.Perfect.IsPerfect
      ((derivedEtaleModuleStalk.{u, r} B X Λ (GeometricPoint.ofPoint X.obj x)).obj K)) :
    IsRepresentedByConstructibleFlatEtaleComplex B X Λ K := by
  classical
  let := SmallEtale.hasSheafify_moduleCat.{u, r, r} B X Λ
  have : HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ) :=
    ModuleCat.hasLimitsOfSize.{u, u, max (u + 1) r, r}
  let ρ := etaleModulesToSmallEtale B X Λ
  let e := SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)
  let P₀ := isConstructibleModuleSheafProperty.{u, max (u + 1) r, r} B X Λ
  have : P₀.IsWeakSerreClass := isWeakSerreClass_isConstructibleModuleSheafProperty B X Λ
  let R : ObjectProperty (EtaleModules.{u, r} Λ X.obj) := P₀.inverseImage ρ
  have : R.IsWeakSerreClass := inferInstance
  let G : EtaleModules.{u, r} Λ X.obj → Prop := IsConstructibleFlatEtaleModule B X Λ
  have : ρ.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesBinaryBiproducts ρ := preservesBinaryBiproducts_of_preservesBinaryProducts ρ
  have hKle : K.IsLE b := by rw [DerivedCategory.isLE_iff]; exact hle
  obtain ⟨A, hA, ⟨eA⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  have hAhom : ∀ i, R (A.homology i) := fun i =>
    R.prop_of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eA ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app A) (hc i)
  have hcov : Stacks.Homology.BoundedAboveResolution.CoversEpis R G := by
    intro V W f hf hW
    have := hf
    obtain ⟨V₁, g, hG, hR, hepi⟩ :=
      coversEpis_isConstructibleFlatModuleSheaf B X Λ (ρ.map f) inferInstance hW
    refine ⟨e.functor.obj V₁, e.functor.map g ≫ e.counitIso.hom.app V, ?_, ?_, ?_⟩
    · exact isConstructibleFlatModuleSheaf_congr B X Λ (e.unitIso.app V₁) hG
    · exact P₀.prop_of_iso (e.unitIso.app V₁) hR
    · have hmap : ρ.map (e.functor.map g ≫ e.counitIso.hom.app V) =
          e.unitIso.inv.app V₁ ≫ g := by
        show e.inverse.map _ = _
        have h2 : e.unit.app (ρ.obj V) ≫ e.inverse.map (e.counitIso.hom.app V) = 𝟙 _ :=
          e.unit_inverse_comp V
        simp [Equivalence.inv_fun_map, h2]
      apply ρ.epi_of_epi_map
      rw [Functor.map_comp, hmap, Category.assoc]
      infer_instance
  have hQzero : G 0 := isConstructibleFlatEtaleModule_of_isZero B Λ X (isZero_zero _)
  have hQbiprod : ∀ ⦃C E : EtaleModules.{u, r} Λ X.obj⦄, G C → G E → G (C ⊞ E) :=
    fun C E hC hE => isConstructibleFlatModuleSheaf_congr B X Λ (ρ.mapBiprod C E).symm
      (isConstructibleFlatModuleSheaf_biprod B X Λ hC hE)
  have hQiso : ∀ ⦃V W : EtaleModules.{u, r} Λ X.obj⦄ (f : V ⟶ W), IsIso f → G V → G W :=
    fun V W f hf hV => IsConstructibleFlatEtaleModule.of_iso B X Λ (asIso f) hV
  obtain ⟨Y, hY, φ, hφ, hGY⟩ :=
    Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis R G A hcov
      hQzero hQbiprod hQiso b hAhom
  let eY : DerivedCategory.Q.obj Y ≅ K := asIso (DerivedCategory.Q.map φ) ≪≫ eA.symm
  have hYhom : ∀ i < a, IsZero (Y.homology i) := fun i hi =>
    (hge i hi).of_iso (((DerivedCategory.homologyFunctorFactors _ i).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso eY)
  have hYR : ∀ i, R (Y.X i) := fun i =>
    isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hGY i)
  have hRop : ∀ m, R (Y.opcycles m) := fun m =>
    R.prop_of_iso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (Y.opcyclesIsCokernel (m - 1) m (by simp)))
      (R.prop_cokernel (Y.d (m - 1) m) (hYR _) (hYR _))
  let st := fun s : GeometricPoint X.obj => etaleModuleStalk.{u, r} B X Λ s
  let Ys : GeometricPoint X.obj → CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ := fun s =>
    ((st s).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y
  let stB := fun (t : GeometricPoint X.obj)
      (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ)) =>
    (etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ t).obj F
  let eT : ∀ (t : GeometricPoint X.obj) (F : EtaleModules.{u, r} Λ X.obj),
      (st t).obj F ≅ stB t (ρ.obj F) := fun t F =>
    (etaleModuleStalkIsoTransport.{u, r} B X Λ t).app F
  have hYsLE : ∀ s, CochainComplex.IsStrictlyLE (Ys s) b := fun s => by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (st s).map_isZero (Y.isZero_of_isStrictlyLE b i hi)
  have hYsProj : ∀ s i, Projective ((Ys s).X i) := fun s i => by
    have : Module.Projective Λ ((Ys s).X i) :=
      (module_projective_iff_of_linearEquiv (eT s (Y.X i)).toLinearEquiv).2
      (etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf B X Λ (ρ.obj (Y.X i))
        (hGY i) s)
    exact ModuleCat.projective_of_categoryTheory_projective _
  have hYsGE : ∀ s m, m ≤ a → CochainComplex.IsGE (Ys s) m := fun s m hm => by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (st s).map_isZero (hYhom i (by omega)) |>.of_iso ((Y.sc i).mapHomologyIso (st s))
  have hiff : ∀ (s : GeometricPoint X.obj) (m : ℤ),
      Module.Projective Λ (stB s (ρ.obj (Y.opcycles m))) ↔
        Projective ((Ys s).opcycles m) := fun s m => by
    let i₁ : (Ys s).opcycles m ≅ stB s (ρ.obj (Y.opcycles m)) :=
      (Y.sc m).mapOpcyclesIso (st s) ≪≫ eT s (Y.opcycles m)
    refine (module_projective_iff_of_linearEquiv i₁.symm.toLinearEquiv).trans
      ⟨fun _ => inferInstance, fun _ => ModuleCat.projective_of_module_projective _⟩
  have hbound : ∀ x : X.obj, ∃ c : ℤ, ∀ n ≤ c,
      Projective ((Ys (GeometricPoint.ofPoint X.obj x)).opcycles n) := by
    intro x
    let s := GeometricPoint.ofPoint X.obj x
    obtain ⟨P, c, d, hPc, hPd, hPfin, hPproj, ⟨eP⟩⟩ := hperf x
    have : ∀ i, Projective (P.X i) := fun i => ModuleCat.projective_of_categoryTheory_projective _
    have : CochainComplex.IsStrictlyLE (Ys s) b := hYsLE s
    have : ∀ i, Projective ((Ys s).X i) := hYsProj s
    let es : DerivedCategory.Q.obj (Ys s) ≅ DerivedCategory.Q.obj P :=
      ((st s).mapDerivedCategoryFactors.app Y).symm ≪≫
        (derivedEtaleModuleStalk.{u, r} B X Λ s).mapIso eY ≪≫ eP
    exact ⟨c, fun n hn => CochainComplex.projective_opcycles_of_iso_Q_obj (Ys s) b P c d es n hn⟩
  let T : ℤ → Set X.obj := fun m => {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
    ¬ Module.Projective Λ (stB t (ρ.obj (Y.opcycles m)))}
  have hwlb : ∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
      ((SmallEtale.topology B Z.obj Z.property).over V).WEqualsLocallyBijective
        (ModuleCat.{max (u + 1) r} Λ) := fun Z V =>
    Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, r, r}
      ((SmallEtale.topology B Z.obj Z.property).over V) Λ
  have := preservesFilteredColimits_forget_moduleCatMax_of_ring.{u, r} Λ
  have hTcons : ∀ m, Topology.IsConstructible (T m) := fun m =>
    isConstructible_setOf_exists_geometricPoint_etaleStalk_of_ring.{u, r, max (u + 1) r} B X Λ
      (ρ.obj (Y.opcycles m)) (hRop m) (fun E => ¬ Module.Projective Λ E)
      (fun {E E'} f => not_congr (module_projective_iff_of_linearEquiv f.toLinearEquiv))
  have hTstep : ∀ m, m ≤ a → T (m - 1) ⊆ T m := by
    intro m hm x hx
    by_contra hxm
    obtain ⟨t, ht, hnp⟩ := hx
    apply hnp
    have hm' : Module.Projective Λ (stB t (ρ.obj (Y.opcycles m))) := by
      by_contra h
      exact hxm ⟨t, ht, h⟩
    have : CochainComplex.IsStrictlyLE (Ys t) b := hYsLE t
    have : ∀ i, Projective ((Ys t).X i) := hYsProj t
    have : CochainComplex.IsGE (Ys t) m := hYsGE t m hm
    exact (hiff t (m - 1)).2 (CochainComplex.projective_opcycles_of_projective_opcycles (Ys t) b m
      ((hiff t m).1 hm') (m - 1) (by omega))
  have hanti : Antitone fun k : ℕ => T (a - k) := by
    refine antitone_nat_of_succ_le fun k => ?_
    have := hTstep (a - k) (by omega)
    rwa [show a - k - 1 = a - (k + 1 : ℕ) by push_cast; ring] at this
  have hempty : (⋂ k : ℕ, T (a - k)) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨c, hc⟩ := hbound x
    let k : ℕ := (a - c).toNat
    obtain ⟨t, ht, hnp⟩ := Set.mem_iInter.1 hx k
    apply hnp
    have h0 := (hiff (GeometricPoint.ofPoint X.obj x) (a - k)).2 (hc (a - k) (by omega))
    have hbase : t.hom default = (GeometricPoint.ofPoint X.obj x).hom default :=
      ht.trans (GeometricPoint.ofPoint_liesOver X.obj x).symm
    exact (module_projective_iff_of_linearEquiv ((etaleStalkPresheafFunctorIsoOfEqBase B X.obj
      X.property hbase (ModuleCat.{max (u + 1) r} Λ)).app
        (ρ.obj (Y.opcycles (a - k))).obj).symm.toLinearEquiv).1 h0
  obtain ⟨k, hk⟩ : ∃ k : ℕ, T (a - k) = ∅ := by
    by_contra hcon
    have hne : ∀ k : ℕ, (WithConstructibleTopology.ofConstructible ⁻¹' T (a - k)).Nonempty := by
      intro k
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 fun h => hcon ⟨k, h⟩
      exact ⟨WithConstructibleTopology.toConstructible y, by simpa using hy⟩
    have hcl : ∀ k : ℕ, IsClosed (WithConstructibleTopology.ofConstructible ⁻¹' T (a - k)) := by
      intro k
      rw [← isOpen_compl_iff, ← Set.preimage_compl,
        WithConstructibleTopology.isOpen_preimage_ofConstructible,
        constructibleTopology_eq_generateFrom_isConstructible ↥X.obj]
      exact TopologicalSpace.isOpen_generateFrom_of_mem (hTcons _).compl
    have hdir : Directed (· ⊇ ·)
        fun k : ℕ => WithConstructibleTopology.ofConstructible ⁻¹' T (a - k) :=
      fun k k' => ⟨max k k', Set.preimage_mono (hanti (le_max_left k k')),
        Set.preimage_mono (hanti (le_max_right k k'))⟩
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun k : ℕ => WithConstructibleTopology.ofConstructible ⁻¹' T (a - k))
      hdir hne (fun k => (hcl k).isCompact) hcl
    have hmem : WithConstructibleTopology.ofConstructible y ∈ ⋂ k : ℕ, T (a - k) :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    simp [hempty] at hmem
  let n : ℤ := a - k
  have hYge : Y.IsGE n := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hYhom i (by omega)
  have hflat_n : G (Y.opcycles n) := by
    refine isConstructibleFlatModuleSheaf_of_projective_etaleModuleStalk B X Λ
      (ρ.obj (Y.opcycles n)) (hRop n) fun t => ?_
    by_contra h
    have hx : t.hom default ∈ T n := ⟨t, rfl, h⟩
    rw [hk] at hx
    exact hx
  have hLE : (Y.truncGE n).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have : Epi ((Y.πTruncGE n).f i) := by
      unfold CochainComplex.πTruncGE
      infer_instance
    exact IsZero.of_epi ((Y.πTruncGE n).f i) (Y.isZero_of_isStrictlyLE b i hi)
  have hterms : ∀ i, G ((Y.truncGE n).X i) := by
    intro i
    by_cases hi : i < n
    · exact isConstructibleFlatEtaleModule_of_isZero B Λ X
        ((Y.truncGE n).isZero_of_isStrictlyGE n i hi)
    · rcases (le_of_not_gt hi).eq_or_lt with h | hni
      · rw [← h]
        exact IsConstructibleFlatEtaleModule.of_iso B X Λ (Y.truncGEXIsoOpcycles n).symm hflat_n
      · exact IsConstructibleFlatEtaleModule.of_iso B X Λ (Y.truncGEXIso n i hni).symm (hGY i)
  exact ⟨Y.truncGE n, n, b, inferInstance, hLE, hterms,
    ⟨(asIso (DerivedCategory.Q.map (Y.πTruncGE n))).symm ≪≫ eY⟩⟩

/-- **Membership of `D_ctf(X_étale, Λ)` from constructible cohomology and perfect stalks**, on a
quasi-compact quasi-separated scheme and for a Noetherian ring `Λ`, not necessarily commutative:
a bounded object of `D(X_étale, Λ)` with constructible cohomology sheaves and perfect stalks at
all geometric points lies in `D_ctf(X_étale, Λ)`. -/
theorem isCtf_of_isPerfect_derivedEtaleModuleStalk
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] [IsNoetherianRing Λ]
    (K : DerivedCategory (EtaleModules.{u, r} Λ X.obj))
    (hc : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ ((etaleModulesToSmallEtale B X Λ).obj
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ X.obj) i).obj K)))
    (a b : ℤ)
    (hge : ∀ i < a,
      IsZero ((DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ X.obj) i).obj K))
    (hle : ∀ i, b < i →
      IsZero ((DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ X.obj) i).obj K))
    (hperf : ∀ x : X.obj, StacksDraft.Perfect.IsPerfect
      ((derivedEtaleModuleStalk.{u, r} B X Λ (GeometricPoint.ofPoint X.obj x)).obj K)) :
    IsCtf B X Λ K :=
  (isCtf_iff_of_qcqs B Λ K).2
    (isRepresentedByConstructibleFlatEtaleComplex_of_isPerfect B X Λ K hc a b hge hle hperf)

end Stacks.EtaleCohomology
