module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.RegularExtVanishing.LocalExt
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtLocalToGlobal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSectionsOfTheRingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.BoundedAmplitude
public import StacksFrontier.Topology.Dimension.CoheightClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleVanishingOnClosedSupport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SeparatedCohomologyHomVanishing
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalBoxGenerator

/-!
# `Ext` between coherent modules vanishes above the dimension of a regular scheme

Let `X` be a regular Noetherian scheme of dimension `d < ∞`. For coherent `𝒪_X`-modules `F` and
`G`, `Ext^n_X(F, G) = 0` for every `n > d`. This is part (1) of [Stacks, Tag 0FZ3].

## The argument

The source uses the local-to-global spectral sequence
`H^p(X, SheafExt^q(F, G)) ⇒ Ext^{p+q}_X(F, G)`. Here the same three inputs are assembled
without the spectral sequence.

1. `Ext^n_X(F, G)` is the degree-`n` hypercohomology of the internal Hom complex
   `C = SheafHom^•(F, I)`, for `I` an injective resolution of `G`
   ([Stacks, Tag 08DK], [Stacks, Tag 0B6E]). The cohomology sheaves of `C` are the sheaves
   `SheafExt^q(F, G)`.
2. Near a point `x` with `dim 𝒪_{X,x} = c`, the sections of `C` over small affine opens have no
   cohomology above degree `c`. This is because `𝒪_{X,x}` has global dimension `c`
   ([Stacks, Tag 00O7]), see
   `Stacks.RegularExtVanishing.exists_nbhd_subsingleton_zExt`. Hence `H^q(C)` vanishes on the
   open set covered by these neighbourhoods for all points with `c < q`. Its complement is a
   closed set of points of codimension `≥ q`, so it has dimension `≤ d - q`
   (`Stacks.Topology.topologicalKrullDim_le_of_le_coheight`). By Grothendieck's vanishing
   theorem for a sheaf supported on a closed subset ([Stacks, Tag 02UZ]),
   `H^p(X, H^q(C)) = 0` for `p + q > d`.
3. A complex with no cohomology below `0` whose cohomology sheaves satisfy this has no
   hypercohomology above `d`. This is proved by induction along its truncation triangles
   (`Stacks.DerivedFunctor.isZero_homology_totalRightDerived_of_isGE`), and it replaces the
   spectral sequence.

## Main results

* `Stacks.RegularExtVanishing.isZero_stalkFunctor_homology_of_locally_exactAt`: a complex of
  sheaves of modules whose complexes of sections are exact in degree `n` on opens forming a
  basis at `x` has zero degree-`n` cohomology stalk at `x`.
* `Stacks.RegularExtVanishing.subsingleton_zExt_of_isRegular`: **[Stacks, Tag 0FZ3] (1)**, for
  every model of the derived category.
* `Stacks.RegularExtVanishing.subsingleton_hom_of_homology_separated_of_isRegular`:
  **[Stacks, Tag 0FZ3] (2)**.
* `AlgebraicGeometry.separatedCohomologyHomVanishing` and
  `AlgebraicGeometry.homVanishingAcrossCohomologyGap`: the predicates that [Stacks, Tag 0FZ4],
  [Stacks, Tag 0FZ5] and [Stacks, Tag 0FZ9] are stated against hold.

## References

* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
* [Stacks Project, Tag 0BQP](https://stacks.math.columbia.edu/tag/0BQP)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 00O7](https://stacks.math.columbia.edu/tag/00O7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.RegularExtVanishing

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Stalks of the cohomology of a complex of sheaves of modules -/

section Stalk

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- **Vanishing of a cohomology stalk from sections over a basis.** If the complexes of
sections of `K` are exact in degree `n` over a family of opens which is a basis at `x`, then the
degree-`n` cohomology sheaf of `K` has zero stalk at `x`. -/
theorem isZero_stalkFunctor_homology_of_locally_exactAt
    (K : CochainComplex (_root_.SheafOfModules.{u} O) ℤ) (n : ℤ) (x : X)
    (P : Opens X → Prop)
    (hP : ∀ U : Opens X, x ∈ U → ∃ V : Opens X, x ∈ V ∧ V ≤ U ∧ P V)
    (hK : ∀ U, P U →
      ((((_root_.SheafOfModules.evaluation O (op U)) ⋙
        forget₂ (ModuleCat.{u} (O.obj.obj (op U))) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).ExactAt n) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor O x).obj (K.homology n)) := by
  let S := (K.sc n).map (AlgebraicGeometry.SheafOfModules.toTopSheaf O)
  have hS : ∀ U, P U → ∀ s : S.X₂.obj.obj (op U),
      S.g.hom.app (op U) s = 0 → ∃ t : S.X₁.obj.obj (op U), S.f.hom.app (op U) t = s :=
    fun U hU => (ShortComplex.ab_exact_iff _).mp (hK U hU)
  have hex : (S.map (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro s hs
    obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.obj s
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
      (TopCat.Presheaf.germ S.X₂.obj U x hxU t) = 0 at hs
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hs
    have hz : (TopCat.Presheaf.germ S.X₃.obj U x hxU) (0 : S.X₃.obj.obj (op U)) = 0 :=
      map_zero _
    obtain ⟨V, hxV, fVU, _, he⟩ :=
      TopCat.Presheaf.germ_eq S.X₃.obj x hxU hxU _ _ (hs.trans hz.symm)
    obtain ⟨W, hxW, hWV, hW⟩ := hP V hxV
    let fWU : W ⟶ U := homOfLE hWV ≫ fVU
    have ht : S.g.hom.app (op W) (S.X₂.obj.map fWU.op t) = 0 := by
      rw [← ConcreteCategory.comp_apply, S.g.hom.naturality]
      change S.X₃.obj.map fWU.op (S.g.hom.app (op U) t) = 0
      dsimp [fWU]
      rw [Functor.map_comp]
      change S.X₃.obj.map (homOfLE hWV).op
        (S.X₃.obj.map fVU.op (S.g.hom.app (op U) t)) = 0
      simpa using congrArg (fun a => S.X₃.obj.map (homOfLE hWV).op a) he
    obtain ⟨v, hv⟩ := hS W hW _ ht
    refine ⟨TopCat.Presheaf.germ S.X₁.obj W x hxW v, ?_⟩
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
      (TopCat.Presheaf.germ S.X₁.obj W x hxW v) = _
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hv]
    exact TopCat.Presheaf.germ_res_apply S.X₂.obj fWU x hxW _
  have hT : ((K.sc n).map (AlgebraicGeometry.SheafOfModules.stalkFunctor O x)).Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _
      (forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))
        AddCommGrpCat.{u})]
    exact (ShortComplex.exact_iff_of_iso
      ((K.sc n).mapNatIso (AlgebraicGeometry.SheafOfModules.stalkFunctorCompForget₂ O x))).mpr hex
  exact (ShortComplex.exact_iff_isZero_homology _).mp hT |>.of_iso
    ((K.sc n).mapHomologyIso (AlgebraicGeometry.SheafOfModules.stalkFunctor O x)).symm

end Stalk

/-! ### `Ext` between coherent modules above the dimension -/

section Main

open _root_.AlgebraicGeometry Stacks.SheafOfModules

/-- [Stacks, Tag 0FZ3] (1) for the `Ext` groups of the standard model of the derived category:
on a regular Noetherian scheme of dimension `d`, `Ext^n(F, G) = 0` for coherent `F`, `G` and
`n > d`. The model-independent statement is `subsingleton_zExt_of_isRegular`. -/
theorem subsingleton_zExt_of_isRegular_standard (X : Scheme.{u}) [IsNoetherian X] (hX : IsRegular X)
    (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) (F G : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (hG : _root_.SheafOfModules.IsCoherent G)
    (n : ℤ) (hn : (d : ℤ) < n) :
    Subsingleton (Abelian.zExt F G n) := by
  have _ : (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive :=
    Tensor.sheafTensor_additive.{u, u, u, u, u} (J := Opens.grothendieckTopology (X : TopCat.{u}))
      X.sheaf
  have _ : ∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj A).Additive :=
    Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
      (J := Opens.grothendieckTopology (X : TopCat.{u})) X.sheaf
  have _ : ∀ K₁ K₂ : CochainComplex
      (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ,
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.sheaf)
        (ComplexShape.up ℤ) := fun K₁ K₂ =>
    Tensor.hasMapBifunctor_sheafTensor (J := Opens.grothendieckTopology (X : TopCat.{u}))
      X.sheaf K₁ K₂
  have _ := hG
  have hGqc : G.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
  -- the internal Hom complex out of `F` into an injective resolution of `G`
  let K : CochainComplex X.Modules ℤ := (CochainComplex.singleFunctor X.Modules 0).obj F
  obtain ⟨R, -, hRGE⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE (0 : ℤ)
    ((CochainComplex.singleFunctor X.Modules 0).obj G)
  have _ : R.cocomplex.IsKInjective := CochainComplex.isKInjective_of_injective R.cocomplex 0
  have _ : QuasiIso R.ι := R.quasiIso
  let I := R.cocomplex
  have hIK : (show CochainComplex (StructureSheafModules X.sheaf) ℤ from I).IsKInjective :=
    CochainComplex.isKInjective_of_injective R.cocomplex 0
  let eM : DerivedCategory.Q.obj I ≅ (DerivedCategory.singleFunctor X.Modules 0).obj G :=
    (asIso (DerivedCategory.Q.map R.ι)).symm
  let C := (sheafHomComplex X.sheaf K I).obj
  -- morphisms on the slice site over `W` are morphisms between the restrictions
  have hconv : ∀ (W : X.Opens) (j : ℤ), Subsingleton (ShiftedHom
      ((DerivedCategory.singleFunctor _ 0).obj
        ((_root_.SheafOfModules.overFunctor (structureSheaf X.sheaf) W).obj F))
      ((DerivedCategory.singleFunctor _ 0).obj
        ((_root_.SheafOfModules.overFunctor (structureSheaf X.sheaf) W).obj G)) j) →
      Subsingleton (ShiftedHom (DerivedCategory.Q.obj (restrictComplex X.sheaf K W))
        (DerivedCategory.Q.obj (restrictComplex X.sheaf I W)) j) := by
    intro W j h
    let Fo := _root_.SheafOfModules.overFunctor (structureSheaf X.sheaf) W
    let _ : PreservesFiniteLimits Fo := LocalCokernel.overFunctor_preservesFiniteLimits W
    let _ : PreservesFiniteColimits Fo := LocalCokernel.overFunctor_preservesFiniteColimits W
    let _ : Fo.Additive := ⟨fun {_ _} _ _ => rfl⟩
    let eN := mapComplexSingleIso Fo K F (Iso.refl _)
    let eI := mapComplexSingleIso Fo I G eM
    exact (Equiv.subsingleton_congr (Iso.homCongr eN ((shiftFunctor _ j).mapIso eI))).mpr h
  have hloc : ∀ (W : X.Opens) (j : ℤ),
      Subsingleton (Abelian.zExt (F.restrict W.ι) (G.restrict W.ι) j) →
      (sectionComplex X.sheaf C W).ExactAt j := by
    intro W j h
    exact ((sectionComplex X.sheaf C W).exactAt_iff_isZero_homology j).mpr
      (AddCommGrpCat.isZero_iff_subsingleton.mpr
        (subsingleton_homology_sectionComplex_sheafHomComplex X.sheaf K I W j
          (hconv W j (subsingleton_shiftedHom_over_of_restrict X W F G j h))))
  -- `C` has no cohomology in negative degrees
  have hCGE : C.IsGE 0 :=
    isGE_sheafHomComplex_of_locally_subsingleton X.sheaf K I 0 (fun _ => True)
      (fun _ U hx => ⟨U, hx, le_rfl, trivial⟩)
      (fun W _ m hm => hconv W m (subsingleton_shiftedHom_single_of_neg _ _ m hm))
  have hQGE : (DerivedCategory.Q.obj C).IsGE 0 := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    exact hCGE
  -- the local neighbourhoods of the points
  have hle : ∀ x : X, Order.coheight x ≤ (d : ℕ∞) := fun x => by
    have h := Stacks.Topology.coheight_le_of_topologicalKrullDim_le hd.le x
    exact_mod_cast h
  have hne : ∀ x : X, Order.coheight x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (ENat.natCast_ne_top d) (hle x)
  have hcoh : ∀ x : X, ((Order.coheight x).toNat : ℕ∞) = Order.coheight x := fun x =>
    ENat.natCast_toNat (hne x)
  choose V hxV hV using fun x : X =>
    exists_nbhd_subsingleton_zExt hX F hF x (Order.coheight x).toNat (hcoh x).ge
  -- the cohomology sheaves of `C` have no cohomology above `d` minus their degree
  have hE : ∀ (j : ℤ) (p : ℕ), (d : ℤ) < j + p →
      IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived p).obj
        ((DerivedCategory.homologyFunctor X.Modules j).obj (DerivedCategory.Q.obj C))) := by
    intro j p hjp
    let Hj := (DerivedCategory.homologyFunctor X.Modules j).obj (DerivedCategory.Q.obj C)
    let eH : Hj ≅ C.homology j := (DerivedCategory.homologyFunctorFactors X.Modules j).app C
    let S : Set X := (⋃ x ∈ {x : X | ((Order.coheight x).toNat : ℤ) < j}, (V x : Set X))ᶜ
    have hS : IsClosed S := by
      refine isOpen_compl_iff.mp ?_
      rw [compl_compl]
      exact isOpen_biUnion fun x _ => (V x).isOpen
    have hstalkM : ∀ y : X, y ∉ S →
        IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf y).obj Hj) := by
      intro y hy
      simp only [S, Set.mem_compl_iff, not_not, Set.mem_iUnion, Set.mem_ofPred_eq] at hy
      obtain ⟨x, hx, hyx⟩ := hy
      have hz := isZero_stalkFunctor_homology_of_locally_exactAt C j y
        (fun W => IsAffineOpen W ∧ W ≤ V x)
        (fun U hyU => by
          obtain ⟨W, hW, hyW, hWU⟩ : ∃ W : X.Opens, W ∈ X.affineOpens ∧ y ∈ W ∧ W ≤ U ⊓ V x :=
            (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show y ∈ U ⊓ V x from ⟨hyU, hyx⟩)
          exact ⟨W, hyW, hWU.trans inf_le_left, hW, hWU.trans inf_le_right⟩)
        (fun W hW => hloc W j (hV x W hW.1 hW.2 G hGqc j hx))
      exact hz.of_iso ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf y).mapIso eH)
    have hstalk : ∀ y : X, y ∉ S →
        IsZero (TopCat.Presheaf.stalk (X := X.toTopCat) Hj.val.presheaf y) := fun y hy =>
      (forget₂ _ AddCommGrpCat.{u}).map_isZero (hstalkM y hy)
    rcases lt_or_ge (d : ℤ) j with hdj | hdj
    · -- above the dimension the cohomology sheaf vanishes outright
      have hall : ∀ y : X, y ∉ S := by
        intro y hyS
        refine hyS (Set.mem_iUnion₂.mpr ⟨y, ?_, hxV y⟩)
        change ((Order.coheight y).toNat : ℤ) < j
        have : (Order.coheight y).toNat ≤ d := by exact_mod_cast (hcoh y).le.trans (hle y)
        omega
      have hT : IsZero ((AlgebraicGeometry.SheafOfModules.toTopSheaf X.ringCatSheaf).obj Hj) :=
        (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr fun y => hstalk y (hall y)
      have hz : IsZero Hj := (IsZero.iff_id_eq_zero _).mpr
        ((AlgebraicGeometry.SheafOfModules.toTopSheaf X.ringCatSheaf).map_injective
          (hT.eq_of_src _ _))
      exact Functor.map_isZero _ hz
    · -- at or below the dimension the support has dimension at most `d - j`
      have hdim : topologicalKrullDim S ≤ ((d - j.toNat : ℕ) : WithBot ℕ∞) := by
        refine Stacks.Topology.topologicalKrullDim_le_of_le_coheight S hS hd.le ?_
        intro s hs
        have hsV : ¬ ((Order.coheight s).toNat : ℤ) < j := fun h =>
          hs (Set.mem_iUnion₂.mpr ⟨s, h, hxV s⟩)
        have h1 : (j.toNat : ℕ∞) ≤ ((Order.coheight s).toNat : ℕ∞) := by
          exact_mod_cast (show j.toNat ≤ (Order.coheight s).toNat by omega)
        exact h1.trans (ENat.natCast_toNat_le_self _)
      exact
        Stacks.CohomologyVanishing.isZero_rightDerived_moduleGlobalSections_of_forall_stalk_isZero
          X S hS hdim (by omega) Hj hstalk
  -- assemble
  have hQGE' : (DerivedCategory.Q.obj (show CochainComplex X.Modules ℤ from C)).IsGE 0 := hQGE
  have hRΓ : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
        (Stacks.SheafOfModules.ringedSite X.sheaf)).obj (DerivedCategory.Q.obj C))) := by
    refine (isZero_homology_derivedModuleGlobalSections_iff X
      (Stacks.DerivedFunctor.totalRightDerived (Stacks.Cohomology.sectionsFunctor X ⊤))
      ((Stacks.DerivedFunctor.homotopyMap
        (Stacks.Cohomology.sectionsFunctor X ⊤)).totalRightDerivedUnit
          DerivedCategory.Qh (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
      (DerivedCategory.Q.obj C) n).mpr ?_
    exact Stacks.DerivedFunctor.isZero_homology_totalRightDerived_of_isGE
      (Stacks.Cohomology.sectionsFunctor X ⊤) d (DerivedCategory.Q.obj C) 0 hE n hn
  have h1 : Subsingleton ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      (((RingedSite.globalDerivedHom (Stacks.SheafOfModules.ringedSite X.sheaf)).obj
        (op (DerivedCategory.Q.obj K))).obj (DerivedCategory.Q.obj I))) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp (hRΓ.of_iso
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
        ((Stacks.Cohomology.ModuleSections.derivedModuleGlobalSections
          (Stacks.SheafOfModules.ringedSite X.sheaf)).mapIso
            (derivedSheafHomComparison X.sheaf K I))))
  have h2 : Subsingleton (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj I)⟦n⟧) :=
    (RingedSite.globalDerivedHomDegreeEquiv (Stacks.SheafOfModules.ringedSite X.sheaf)
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I) n).toEquiv.subsingleton_congr.mp h1
  exact (Equiv.subsingleton_congr (Iso.homCongr (Iso.refl _)
    ((shiftFunctor _ n).mapIso eM))).mp h2

end Main

end Standard

/-! ### The two parts of Tag 0FZ3 -/

section Parts

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} [IsNoetherian X]

/-- **Stacks Project, Tag 0FZ3, part (1).** Let `X` be a regular Noetherian scheme of dimension
`d < ∞`. For coherent `𝒪_X`-modules `F` and `G`, `Ext^n_X(F, G) = 0` for every `n > d`.

The statement holds for every model of the derived category of `𝒪_X`-modules, since in
non-negative degrees all of them compute the same `Ext` groups (`Abelian.Ext.homEquiv`). -/
@[stacks 0FZ3 "part (1)"]
theorem subsingleton_zExt_of_isRegular [HasDerivedCategory.{u + 1} X.Modules]
    (hX : IsRegular X) (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (F G : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F)
    (hG : _root_.SheafOfModules.IsCoherent G) (n : ℤ) (hn : (d : ℤ) < n) :
    Subsingleton (Abelian.zExt F G n) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)
  let := HasExt.standard X.Modules
  have e₀ := (let := HasDerivedCategory.standard X.Modules
    Abelian.Ext.homEquiv (X := F) (Y := G) (n := k))
  exact (Abelian.Ext.homEquiv (X := F) (Y := G) (n := k)).subsingleton_congr.mp
    (e₀.subsingleton_congr.mpr (subsingleton_zExt_of_isRegular_standard X hX d hd F G hF hG k hn))

/-- **Stacks Project, Tag 0FZ3, part (2).** Let `X` be a regular Noetherian scheme of dimension
`d < ∞`, let `K` and `L` be objects of `D^b_{Coh}(𝒪_X)` and let `a` be an integer. If
`H^i(K) = 0` for `i < a + d` and `H^i(L) = 0` for `i ≥ a`, then `Hom_X(K, L) = 0`.

This is the formal consequence of part (1), `subsingleton_zExt_of_isRegular`, that the source
draws by induction along the truncation triangles, which is
`Stacks.SeparatedCohomology.subsingleton_hom_of_isGE_of_isLE`. -/
@[stacks 0FZ3 "part (2)"]
theorem subsingleton_hom_of_homology_separated_of_isRegular
    [HasDerivedCategory.{u + 1} X.Modules] (hX : IsRegular X) (d : ℕ)
    (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (K L : DerivedCategory X.Modules) (a : ℤ)
    (hKb : DerivedCategory.TStructure.t.bounded K)
    (hLb : DerivedCategory.TStructure.t.bounded L)
    (hKcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent)
    (hLcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent)
    (hK : ∀ i : ℤ, i < a + d → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K))
    (hL : ∀ i : ℤ, a ≤ i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L)) :
    Subsingleton (K ⟶ L) :=
  Stacks.SeparatedCohomology.subsingleton_hom_of_isGE_of_isLE
    (fun M : X.Modules => M.IsCoherent) d
    (subsingleton_zExt_of_isRegular hX d hd)
    K L a hKb hLb hKcoh hLcoh
    ((DerivedCategory.isGE_iff K (a + d)).2 hK)
    ((DerivedCategory.isLE_iff L (a - 1)).2 fun i hi => hL i (by omega))

end Parts

end Stacks.RegularExtVanishing

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- The predicate `AlgebraicGeometry.SeparatedCohomologyHomVanishing`, which [Stacks, Tag 0FZ4]
is stated against, holds on every Noetherian scheme in every dimension: it is [Stacks, Tag 0FZ3]
(2), `Stacks.RegularExtVanishing.subsingleton_hom_of_homology_separated_of_isRegular`. -/
theorem separatedCohomologyHomVanishing (X : Scheme.{u}) [IsNoetherian X] (d : ℕ) :
    SeparatedCohomologyHomVanishing X d :=
  fun hX hd K L hKb hLb hKcoh hLcoh a hK hL =>
    Stacks.RegularExtVanishing.subsingleton_hom_of_homology_separated_of_isRegular hX d hd K L a
      hKb hLb hKcoh hLcoh hK hL

/-- The predicate `AlgebraicGeometry.HomVanishingAcrossCohomologyGap` holds: it is
`AlgebraicGeometry.separatedCohomologyHomVanishing` quantified over the scheme and the
dimension. -/
theorem homVanishingAcrossCohomologyGap : HomVanishingAcrossCohomologyGap.{u} :=
  fun W _ e => separatedCohomologyHomVanishing W e

end AlgebraicGeometry

end
