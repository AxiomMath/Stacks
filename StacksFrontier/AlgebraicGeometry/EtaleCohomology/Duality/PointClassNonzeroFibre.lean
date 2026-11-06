module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TopDegreeTest
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzeroFibreSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurvePointClassNonzero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt

/-!
# The class of a `k`-point of a family of curves through its fibre

Let `k` be algebraically closed, `ℓ` a prime invertible in `k`, `Λ = ℤ/ℓ`, and let `g : U → S` be
smooth of relative dimension one, separated of finite type, `U` noetherian, with a
compactification. Let `p : Spec k → U` be a `k`-point over the closed `k`-point `i' = g ∘ p`
of `S`, whose fibre `C = U ×_S Spec k` is irreducible. Then some `δ ∈ Ext²_U(p_* Λ, g⁻¹ i'_* Λ)`
has `H⁰(Rg_!(δ)) ≠ 0` (`Stacks.EtaleCohomology.exists_ext_homology_map_ne_zero_of_fibre`).

Indeed, the class of the point `p` of the smooth irreducible curve `C` is nonzero in `H²_c(C)`
(`Stacks.EtaleCohomology.curvePointClassNonzero`): some `δ_C ∈ Ext²_C(p_* Λ, Λ_C)` and
`ẑ : Λ_k[0] ⟶ R(C → k)_!(p_* Λ)` have `R(C → k)_!(δ_C) ∘ ẑ ≠ 0`, and since `Spec k` has
cohomological dimension zero this forces `H⁰(R(C → k)_!(δ_C)) ≠ 0`
(`Stacks.TopTruncationExt.eq_zero_of_homologyFunctor_map_eq_zero`). The class `δ` is the image of
`δ_C` under the closed immersion `c : C → U`, read through `c_* Λ_C ≅ g⁻¹ i'_* Λ` (Tag 0959), and
`Rg_! ∘ Rc_* ≅ R(c ≫ g)_! = R(C → k ≫ i')_! ≅ i'_* ∘ R(C → k)_!` (Tag 0F7J, in degree zero), with
`i'_*` exact and faithful.

This is the curve input of the step of the class of a point through an elementary fibration, in
the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.subsingleton_ext_unitSheaf_spec_of_isSepClosed`.
* `Stacks.EtaleCohomology.exists_ext_homology_map_ne_zero_of_fibre`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

-- `Stacks.EtaleCohomology.PointClassNonzeroAt` reads `ZMod ℓ` as a ring through `ZMod.commRing`.
attribute [-instance] ZMod.instField

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe, on which instance
-- problems below get stuck.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- **`Spec k` has cohomological dimension zero** for `k` separably closed:
`Ext^i(Λ, M) = 0` for `i ≥ 1` (Tag 095U in dimension zero). -/
theorem subsingleton_ext_unitSheaf_spec_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    (N : ℕ) [NeZero N] (M : EtaleModules.{u, 0} (ZMod N) (Spec (.of k))) (i : ℕ) (hi : 1 ≤ i) :
    Subsingleton (Ext (unitSheaf (X := Spec (.of k)) N) M i) :=
  subsingleton_ext_constantModuleSheaf_zmod_of_proper (𝟙 (Spec (.of k))) 0
    (by exact_mod_cast topologicalKrullDim_zero_of_discreteTopology (Spec (.of k))) N M i
    (by omega)

variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] {k : Type u} [Field k] [IsAlgClosed k]

/-- Every bounded below complex of `ℤ/ℓ`-modules is torsion. -/
private theorem isTorsionPlus_zmod (n : ℕ) [NeZero n] (C : Scheme.{u})
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod n) C)) :
    isTorsionPlus.{u, 0} (ZMod n) C K := fun _ =>
  isTorsionEtaleModule_of_natCast_eq_zero (ZMod n) n (Nat.pos_of_ne_zero (NeZero.ne n))
    (ZMod.natCast_self n) _

omit [Fact (Nat.Prime ℓ)] in
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus in
/-- **A class of `Rf_!` detected from `Λ_k` has nonzero top image**, for `f : C ⟶ Spec k` of fibre
dimension at most one: `Spec k` has cohomological dimension zero. -/
theorem homologyFunctor_zero_map_derivedLowerShriek_ne_zero_of_comp_ne_zero {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) (jf : CompactificationOf (Over.mk f))
    (hf : ∀ y : Spec (.of k), topologicalKrullDim (jf.toBase.fiber y) ≤ (1 : ℕ))
    {M : EtaleModules.{u, 0} (ZMod ℓ) C} (β : Ext M (unitSheaf (X := C) ℓ) (2 * 1))
    (w₀ : (DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ) ⟶
      (derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M))
    (hw₀ : w₀ ≫ (derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).map
      (Stacks.TopTruncationExt.extPlus β) ≠ 0) :
    (DerivedCategory.Plus.homologyFunctor _ 0).map
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).map (Stacks.TopTruncationExt.extPlus β)) ≠ 0 := by
  intro h0
  apply hw₀
  let Rf := derivedLowerShriek.{u, 0} f jf (ZMod ℓ)
  let φ := Stacks.TopTruncationExt.extPlus β
  let L₀ := (DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := C) ℓ)
  have hL₀ : isTorsionPlus.{u, 0} (ZMod ℓ) C L₀ := isTorsionPlus_zmod ℓ C _
  let K := DerivedCategory.Plus.ι.obj (Rf.obj L₀)
  have : K.IsLE 2 := by
    have h := isLE_derivedLowerShriek_of_isTorsionPlus (ZMod ℓ) f jf 1 hf L₀ hL₀ 0 inferInstance
    rwa [show (0 : ℤ) + ((2 * 1 : ℕ) : ℤ) = 2 by norm_num] at h
  have : K.IsGE (2 - ((2 : ℕ) : ℤ)) := by
    have : (Rf.obj L₀).IsGE 0 := isGE_derivedLowerShriek_obj (ZMod ℓ) f jf L₀ 0
    simpa using (inferInstance : K.IsGE 0)
  let w : (DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ) ⟶ K⟦(2 : ℤ)⟧ :=
    DerivedCategory.Plus.ι.map (w₀ ≫ Rf.map φ) ≫
      ((Rf ⋙ DerivedCategory.Plus.ι).commShiftIso ((2 * 1 : ℕ) : ℤ)).hom.app L₀
  have hw : (DerivedCategory.homologyFunctor _ 0).map w = 0 := by
    have h1 : (DerivedCategory.homologyFunctor _ 0).map
        (DerivedCategory.Plus.ι.map (Rf.map φ)) = 0 := h0
    have e : (DerivedCategory.homologyFunctor _ 0).map w =
        ((DerivedCategory.homologyFunctor _ 0).map (DerivedCategory.Plus.ι.map w₀) ≫
          (DerivedCategory.homologyFunctor _ 0).map (DerivedCategory.Plus.ι.map (Rf.map φ))) ≫
        (DerivedCategory.homologyFunctor _ 0).map
          (((Rf ⋙ DerivedCategory.Plus.ι).commShiftIso ((2 * 1 : ℕ) : ℤ)).hom.app L₀) :=
      ((DerivedCategory.homologyFunctor _ 0).map_comp _ _).trans
        (congrArg (· ≫ _) ((DerivedCategory.homologyFunctor _ 0).map_comp _ _))
    rw [e, h1, comp_zero, zero_comp]
    rfl
  have hw0 := Stacks.TopTruncationExt.eq_zero_of_homologyFunctor_map_eq_zero
    (unitSheaf (X := Spec (.of k)) ℓ)
    (fun i M hi => subsingleton_ext_unitSheaf_spec_of_isSepClosed ℓ M i hi) 2 K 2 w hw
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.map_zero]
  exact (Preadditive.IsIso.comp_right_eq_zero _
    (((Rf ⋙ DerivedCategory.Plus.ι).commShiftIso ((2 * 1 : ℕ) : ℤ)).hom.app L₀)).1 hw0

omit [NeZero ℓ] [IsAlgClosed k] in
/-- **`Rg_! ∘ Rc_*` keeps nonzero top images from a curve over a closed point**: for closed
immersions `c : C ⟶ U` and `i' : Spec k ⟶ S` with `c ≫ g = f ≫ i'`, a map `φ` of torsion complexes
on `C` with `H⁰(Rf_!(φ)) ≠ 0` has `H⁰(Rg_!(Rc_*(φ))) ≠ 0` (Tag 0F7J, with `i'_*` exact and
faithful). -/
theorem homologyFunctor_zero_map_derivedLowerShriek_directImage_ne_zero {U S C : Scheme.{u}}
    (g : U ⟶ S) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [CompactSpace S]
    [QuasiSeparatedSpace S] (jg : CompactificationOf (Over.mk g)) (i' : Spec (.of k) ⟶ S)
    [IsClosedImmersion i'] (c : C ⟶ U) [IsClosedImmersion c] [CompactSpace C]
    [QuasiSeparatedSpace C] (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    (jf : CompactificationOf (Over.mk f)) (hcond : c ≫ g = f ≫ i')
    {A B : DerivedCategory.Plus (EtaleModules.{u, 0} (ZMod ℓ) C)}
    (hA : isTorsionPlus.{u, 0} (ZMod ℓ) C A) (hB : isTorsionPlus.{u, 0} (ZMod ℓ) C B) (φ : A ⟶ B)
    (hφ : (DerivedCategory.Plus.homologyFunctor _ 0).map
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).map φ) ≠ 0) :
    (DerivedCategory.Plus.homologyFunctor _ 0).map ((derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).map
      ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) c).map φ)) ≠ 0 := by
  let Rf := derivedLowerShriek.{u, 0} f jf (ZMod ℓ)
  have : QuasiCompact (f ≫ i') := quasiCompact_of_compactSpace _
  have : LocallyOfFiniteType i' := instLocallyOfFiniteTypeOfIsClosedImmersion i'
  have : IsSeparated i' := inferInstance
  have : LocallyOfFiniteType (f ≫ i') := inferInstance
  have : IsSeparated (f ≫ i') := inferInstance
  obtain ⟨jY⟩ : Nonempty (CompactificationOf (Over.mk (f ≫ i'))) :=
    (isCofiltered_compactificationOf (f ≫ i')).nonempty
  let Θ := (derivedLowerShriekCompDirectImageIsoOfIsFinite (ZMod ℓ) c g jg
      (hcond.symm ▸ jY)).symm ≪≫
    Functor.isoWhiskerLeft (isTorsionPlus.{u, 0} (ZMod ℓ) C).ι
      (derivedLowerShriekIsoOfEq hcond jY (ZMod ℓ)) ≪≫
    derivedLowerShriekCompIso (ZMod ℓ) f i' jf (CompactificationOf.ofProper i') jY ≪≫
    Functor.isoWhiskerLeft ((isTorsionPlus.{u, 0} (ZMod ℓ) C).ι ⋙ Rf)
      (derivedLowerShriekOfProperIso (ZMod ℓ) i')
  have hnat : (derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).map
      ((etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) c).map φ) ≫ Θ.hom.app ⟨B, hB⟩ =
      Θ.hom.app ⟨A, hA⟩ ≫ (etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) i').map (Rf.map φ) :=
    Θ.hom.naturality (ObjectProperty.homMk (P := isTorsionPlus.{u, 0} (ZMod ℓ) C)
      (X := ⟨A, hA⟩) (Y := ⟨B, hB⟩) φ)
  have := (etaleModuleDirectImageFullyFaithful (ZMod ℓ) i').faithful
  let η := Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
    (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i') 0
  have h1 : (DerivedCategory.Plus.homologyFunctor _ 0).map
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').rightDerivedFunctorPlus.map (Rf.map φ)) ≠ 0 := by
    intro h0
    apply hφ
    apply (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').map_injective
    rw [Functor.map_zero]
    have h2 : η.hom.app _ ≫ (DerivedCategory.Plus.homologyFunctor _ 0 ⋙
        etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').map (Rf.map φ) = 0 := by
      rw [← η.hom.naturality (Rf.map φ)]
      exact (congrArg (· ≫ η.hom.app _) h0).trans zero_comp
    exact (Preadditive.IsIso.comp_left_eq_zero (η.hom.app _) _).1 h2
  intro h0
  apply h1
  have h4 := congrArg (DerivedCategory.Plus.homologyFunctor _ 0).map hnat
  rw [Functor.map_comp, Functor.map_comp, h0, zero_comp] at h4
  exact (Preadditive.IsIso.comp_left_eq_zero
    ((DerivedCategory.Plus.homologyFunctor _ 0).map (Θ.hom.app ⟨A, hA⟩)) _).1 h4.symm

omit [IsAlgClosed k] in
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus in
/-- **A class of `Ext²_U(p_* Λ, g⁻¹ i'_* Λ)` with nonzero top image, from a class on the fibre**:
the image of `δ_C ∈ Ext²_C(σ_* Λ, Λ_C)` under the closed immersion `c` of the fibre, read through
`c_* Λ_C ≅ g⁻¹ i'_* Λ` (Tag 0959). -/
theorem exists_ext_homology_map_ne_zero_of_fibre_class {U S C : Scheme.{u}}
    (g : U ⟶ S) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [CompactSpace S]
    [QuasiSeparatedSpace S] (jg : CompactificationOf (Over.mk g)) (i' : Spec (.of k) ⟶ S)
    [IsClosedImmersion i'] {p : Spec (.of k) ⟶ U} {c : C ⟶ U} {gC : C ⟶ Spec (.of k)}
    (hsq : IsPullback c gC g i') [CompactSpace C] [QuasiSeparatedSpace C]
    (σC : Spec (.of k) ⟶ C) (hσc : σC ≫ c = p) (f : C ⟶ Spec (.of k)) [IsSeparated f]
    [LocallyOfFiniteType f] (hf : f = gC) (jf : CompactificationOf (Over.mk f))
    (δC : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) σC).obj (unitSheaf (X := Spec (.of k)) ℓ))
      (unitSheaf (X := C) ℓ) (2 * 1))
    (hδC : (DerivedCategory.Plus.homologyFunctor _ 0).map
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).map (Stacks.TopTruncationExt.extPlus δC)) ≠ 0) :
    ∃ δ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj (unitSheaf (X := Spec (.of k)) ℓ))
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := Spec (.of k)) ℓ))) 2,
      (DerivedCategory.Plus.homologyFunctor _ 0).map ((derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).map
        (Stacks.TopTruncationExt.extPlus δ)) ≠ 0 := by
  have : IsClosedImmersion c := MorphismProperty.of_isPullback hsq.flip inferInstance
  have := isIso_etaleModuleBaseChange_of_isIntegralHom (ZMod ℓ) i' c g gC hsq
  let Rc := etaleModuleDerivedDirectImage.{u, 0} (ZMod ℓ) c
  let eB : (etaleModuleDirectImage.{u, 0} (ZMod ℓ) c).obj (unitSheaf (X := C) ℓ) ≅
      (etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := Spec (.of k)) ℓ)) :=
    (etaleModuleDirectImage.{u, 0} (ZMod ℓ) c).mapIso
        ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) gC).app
          (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))).symm ≪≫
      (asIso ((etaleModuleBaseChange (ZMod ℓ) i' c g gC hsq.w).app
        (unitSheaf (X := Spec (.of k)) ℓ))).symm
  let isoA : Rc.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) σC).obj (unitSheaf (X := Spec (.of k)) ℓ))) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj (unitSheaf (X := Spec (.of k)) ℓ)) :=
    ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
      (etaleModuleDirectImage.{u, 0} (ZMod ℓ) c) 0).app _).symm ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso
        ((etaleModuleDirectImageComp (ZMod ℓ) σC c p hσc.symm).app _)
  let isoB : Rc.obj (((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := C) ℓ))⟦
        ((2 * 1 : ℕ) : ℤ)⟧) ≅
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj
            (unitSheaf (X := Spec (.of k)) ℓ))))⟦((2 * 1 : ℕ) : ℤ)⟧ :=
    (Rc.commShiftIso ((2 * 1 : ℕ) : ℤ)).app _ ≪≫
      (shiftFunctor _ ((2 * 1 : ℕ) : ℤ)).mapIso
        (((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
          (etaleModuleDirectImage.{u, 0} (ZMod ℓ) c) 0).app _).symm ≪≫
          (DerivedCategory.Plus.singleFunctor _ 0).mapIso eB)
  have htors := isTorsionPlus_zmod ℓ C
  obtain ⟨δ, hδ⟩ := Stacks.TopTruncationExt.extPlus_surjective _ _ (2 * 1)
    (isoA.inv ≫ Rc.map (Stacks.TopTruncationExt.extPlus δC) ≫ isoB.hom)
  refine ⟨δ, fun h0 => homologyFunctor_zero_map_derivedLowerShriek_directImage_ne_zero ℓ g jg i'
    c f jf (by rw [hf, hsq.w]) (htors _) (htors _) _ hδC ?_⟩
  simp only [hδ, Functor.map_comp] at h0
  exact (Preadditive.IsIso.comp_right_eq_zero _ _).1
    ((Preadditive.IsIso.comp_left_eq_zero _ _).1 h0)

/-- **A class of `Ext²_U(p_* Λ, g⁻¹ i'_* Λ)` with nonzero top image, from the fibre curve.** -/
theorem exists_ext_homology_map_ne_zero_of_fibre (hℓ : IsUnit (ℓ : k)) {U S : Scheme.{u}}
    (g : U ⟶ S) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [CompactSpace S]
    [QuasiSeparatedSpace S] [TopologicalSpace.NoetherianSpace U] [SmoothOfRelativeDimension 1 g]
    (jg : CompactificationOf (Over.mk g)) (i' : Spec (.of k) ⟶ S) [IsClosedImmersion i']
    (p : Spec (.of k) ⟶ U) (hp : p ≫ g = i') {C : Scheme.{u}} {c : C ⟶ U}
    {gC : C ⟶ Spec (.of k)} (hsq : IsPullback c gC g i') [IrreducibleSpace C] :
    ∃ δ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj (unitSheaf (X := Spec (.of k)) ℓ))
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) g).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i').obj (unitSheaf (X := Spec (.of k)) ℓ))) 2,
      (DerivedCategory.Plus.homologyFunctor _ 0).map ((derivedLowerShriek.{u, 0} g jg (ZMod ℓ)).map
        (Stacks.TopTruncationExt.extPlus δ)) ≠ 0 := by
  let σC : Spec (.of k) ⟶ C := hsq.lift p (𝟙 _) (by rw [hp, Category.id_comp])
  have hσg : σC ≫ gC = 𝟙 _ := hsq.lift_snd _ _ _
  have : IsClosedImmersion c := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : IsClosedImmersion σC := isClosedImmersion_of_comp_eq_id gC σC hσg
  have : TopologicalSpace.NoetherianSpace C := c.isClosedEmbedding.isInducing.noetherianSpace
  have : QuasiSeparatedSpace C := NoetherianSpace.to_quasiSeparatedSpace
  have : SmoothOfRelativeDimension 1 gC :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hsq inferInstance
  have : QuasiCompact gC := quasiCompact_of_compactSpace gC
  have : IsSeparated gC := MorphismProperty.of_isPullback hsq inferInstance
  have : LocallyOfFiniteType gC := MorphismProperty.of_isPullback hsq inferInstance
  obtain ⟨c₀⟩ : Nonempty (CompactificationOf (Over.mk gC)) := IsCofiltered.nonempty
  let gC' := 𝟙 C ≫ 𝟙 C ≫ gC
  have hgC' : gC' = gC := by simp [gC']
  let jC : CompactificationOf (Over.mk gC') := (c₀.restrictOpen (𝟙 C)).restrictClosed (𝟙 C)
  have : SmoothOfRelativeDimension 1 gC' := by
    rw [hgC']
    infer_instance
  have : QuasiCompact (𝟙 C ≫ gC) := quasiCompact_of_compactSpace _
  have hdim : topologicalKrullDim jC.space ≤ (1 : ℕ) :=
    topologicalKrullDim_restrictClosed_space_le gC c₀ (𝟙 C) (𝟙 C) 1
  have hfC : ∀ y : Spec (.of k), topologicalKrullDim (jC.toBase.fiber y) ≤ (1 : ℕ) := fun y =>
    ((jC.toBase.fiberι y).isEmbedding.isInducing.topologicalKrullDim_le).trans hdim
  have : SmoothOfRelativeDimension 0 (σC ≫ 𝟙 C ≫ gC') := by
    rw [show σC ≫ 𝟙 C ≫ gC' = 𝟙 _ by simp [gC', hσg]]
    infer_instance
  have hcurve := curvePointClassNonzero ℓ k hℓ C gC' jC C (Spec (.of k)) (𝟙 C) σC
  rw [pointClassNonzeroAt_id_iff] at hcurve
  obtain ⟨δC, w₀, hw₀⟩ := hcurve
  exact exists_ext_homology_map_ne_zero_of_fibre_class ℓ g jg i' hsq σC (hsq.lift_fst _ _ _) gC'
    hgC' jC δC
    (homologyFunctor_zero_map_derivedLowerShriek_ne_zero_of_comp_ne_zero ℓ gC' jC hfC δC w₀ hw₀)

end Stacks.EtaleCohomology

end
