module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.DerivedGeometricStalkGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekComposition
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeGeometry

/-!
# The stalks of a proper direct image of an extension by zero

Let `h : X ⟶ Y` be proper, `j_U : U ⟶ X` an open immersion and `C` a bounded below complex of
sheaves of `Λ`-modules on `U`, `Λ` a finite ring. The stalk at a geometric point `ȳ` of
`Rh_*(j_{U!} C)` is the compactly supported cohomology of the geometric fibre `U_ȳ`, and it may be
computed on any compactification of `U_ȳ` over `ȳ`: this is proper base change (Tags 095T, 0GK0)
and the independence of the compactification (Tag 0F7I). When the fibres of `U ⟶ Y` have dimension
at most one the compactification may be taken proper of dimension at most one (Tag 0BXV), so the
stalk is `RΓ(Z, j_! C|_{U_ȳ})` for a proper scheme `Z` of dimension at most one over an
algebraically closed field. This is the reduction of the perfectness and the amplitude of the
stalks of `Rh_*(j_{U!} C)`, in the proof of [Stacks, Tag 03UI], to curves.

## Main results

* `Stacks.EtaleCohomology.nonempty_compactlySupportedCohomologyUnboundedIso` — `RΓ_c` computed
  through a compactification `j` is `RΓ(j.space, j_! -)`, on bounded below complexes.

## References

* [Stacks Project, Tag 0GK0](https://stacks.math.columbia.edu/tag/0GK0)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0BXV](https://stacks.math.columbia.edu/tag/0BXV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModules_ab5OfSize etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ]

/-- **`RΓ⁺(X, D) ≅ Q(Γ(X, I))` for a quasi-isomorphism `φ : D ⟶ I` to a complex of
injectives**: bounded below derived global sections are computed by an injective resolution. -/
theorem nonempty_etaleModuleDerivedGlobalSectionsIso_of_injective (X : Scheme.{u})
    {D I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} (φ : D ⟶ I) (hφ : QuasiIso φ.hom)
    (hI : ∀ n, Injective (I.obj.X n)) :
    Nonempty (DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} Λ X).obj
        (DerivedCategory.Plus.Q.obj D)) ≅
      DerivedCategory.Q.obj (((etaleModuleGlobalSections.{u, 0} Λ X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj)) := by
  have : EnoughInjectives (EtaleModules.{u, 0} Λ X) := etaleModules_enoughInjectives.{u, 0} Λ X
  have := hI
  let Γ := etaleModuleGlobalSections.{u, 0} Λ X
  have : IsIso (DerivedCategory.Plus.Q.map φ) := by
    have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map φ)) := by
      show IsIso (DerivedCategory.Q.map ((CochainComplex.Plus.ι _).map φ))
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hφ
    exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  have : IsIso (Γ.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient _).obj I)) := inferInstance
  have : IsIso (Γ.mapHomologicalComplexDerivedUnit I.property) :=
    inferInstanceAs (IsIso ((Γ.mapHomologicalComplexQhIso I.property).inv ≫
      DerivedCategory.Plus.ι.map (Γ.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient _).obj I))))
  exact ⟨DerivedCategory.Plus.ι.mapIso (Γ.rightDerivedFunctorPlus.mapIso
      (asIso (DerivedCategory.Plus.Q.map φ) ≪≫
        ((DerivedCategory.Plus.quotientCompQhIso _).app I).symm)) ≪≫
    (asIso (Γ.mapHomologicalComplexDerivedUnit I.property)).symm⟩

/-- A bounded below complex of injectives is K-injective. -/
private theorem isKInjective_of_forall_injective_plus {C : Type*} [Category C] [Abelian C]
    (I : CochainComplex.Plus C) (hI : ∀ n, Injective (I.obj.X n)) : I.obj.IsKInjective := by
  obtain ⟨c, _⟩ := I.property
  exact CochainComplex.isKInjective_of_injective I.obj c

/-- Extension by zero along an open immersion, derived, is computed termwise on complexes. -/
private def extensionByZeroDerivedIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : CochainComplex (EtaleModules.{u, 0} Λ U) ℤ) :
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ j).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((etaleModuleExtensionByZero.{u, 0} Λ j).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, 0} Λ j).app _ ≪≫
    (etaleModuleExtensionByZero.{u, 0} Λ j).mapDerivedCategoryFactors.app K

/-- **Compactly supported cohomology through a compactification is the cohomology of the
extension by zero**: for a compactification `j` of `f : V ⟶ Spec k` and a bounded below complex
`E` on `V`, `RΓ_c(V, E) = RΓ(Spec k, Rf̄_* Rj_! E) ≅ RΓ(V̄, j_! E)`. -/
theorem nonempty_compactlySupportedCohomologyUnboundedIso (k : Type u) [Field k] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (E : CochainComplex.Plus (EtaleModules.{u, 0} Λ V)) :
    Nonempty ((compactlySupportedCohomologyUnbounded.{u, 0} k f j Λ).obj
        (DerivedCategory.Q.obj E.obj) ≅
      DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} Λ j.space).obj
        (DerivedCategory.Plus.Q.obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj E)))) := by
  have : EnoughInjectives (EtaleModules.{u, 0} Λ j.space) :=
    etaleModules_enoughInjectives.{u, 0} Λ j.space
  let D := (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj E
  obtain ⟨I, φ, hφ, hI, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution
    (𝟭 (EtaleModules.{u, 0} Λ j.space)) D (𝟙 _)
  have := hI
  have : I.obj.IsKInjective := isKInjective_of_forall_injective_plus I hI
  let qI := (etaleModuleDirectImage.{u, 0} Λ j.toBase).mapCochainComplexPlus.obj I
  have : ∀ m, Injective (qI.obj.X m) := fun m =>
    inferInstanceAs (Injective ((etaleModuleDirectImage.{u, 0} Λ j.toBase).obj (I.obj.X m)))
  have : qI.obj.IsKInjective := isKInjective_of_forall_injective_plus qI this
  have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, 0} Λ j.toBase I.obj
    inferInstance
  have := isIso_etaleModuleDerivedGlobalSectionsUnboundedUnit_app.{u, 0} Λ (Spec (.of k))
    qI.obj inferInstance
  have : IsIso (DerivedCategory.Q.map φ.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ φ.hom).2 hφ
  let e₂ : (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase).obj
      (DerivedCategory.Q.obj D.obj) ≅ DerivedCategory.Q.obj qI.obj :=
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase).mapIso
        (asIso (DerivedCategory.Q.map φ.hom)) ≪≫
      (asIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ j.toBase).app I.obj)).symm
  let e₃ : (etaleModuleDerivedGlobalSectionsUnbounded.{u, 0} Λ (Spec (.of k))).obj
      (DerivedCategory.Q.obj qI.obj) ≅
        DerivedCategory.Q.obj (((etaleModuleGlobalSections.{u, 0} Λ j.space).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I.obj) :=
    (asIso ((etaleModuleDerivedGlobalSectionsUnboundedUnit.{u, 0} Λ (Spec (.of k))).app
        qI.obj)).symm ≪≫
      DerivedCategory.Q.mapIso
        (((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app I.obj) ≪≫
          (NatIso.mapHomologicalComplex (etaleModuleGlobalSectionsDirectImageIso j.toBase Λ)
            (ComplexShape.up ℤ)).app I.obj)
  obtain ⟨e₄⟩ := nonempty_etaleModuleDerivedGlobalSectionsIso_of_injective Λ j.space φ hφ hI
  exact ⟨(etaleModuleDerivedGlobalSectionsUnbounded.{u, 0} Λ (Spec (.of k))).mapIso
      ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase).mapIso
        (extensionByZeroDerivedIso Λ j.immersion E.obj) ≪≫ e₂) ≪≫ e₃ ≪≫
    e₄.symm⟩

/-- **`Rf_! K ≅ Q(f̄_* I)` for a resolution `I` of `j_! K` by injectives**, on the unbounded
derived category of the base, for any compactification `j` of `f : V ⟶ Y`. This is the
computation of `Rf_! = Rf̄_* ∘ Rj_!` on a bounded below complex. -/
theorem nonempty_derivedLowerShriekUnboundedIsoDirectImage_of_injective {V Y : Scheme.{u}}
    {f : V ⟶ Y} (j : CompactificationOf (Over.mk f))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ V))
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ j.space))
    (ψ : (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K ⟶ I)
    [QuasiIso ψ.hom] (hI : ∀ n, Injective (I.obj.X n)) :
    Nonempty (DerivedCategory.Q.obj
        ((etaleModuleDirectImage.{u, 0} Λ j.toBase).mapCochainComplexPlus.obj I).obj ≅
      (derivedLowerShriekUnbounded.{u, 0} f j Λ).obj (DerivedCategory.Q.obj K.obj)) := by
  have := hI
  have : I.obj.IsKInjective := isKInjective_of_forall_injective_plus I hI
  have hu := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, 0} Λ j.toBase I.obj
    inferInstance
  have : IsIso (DerivedCategory.Q.map ψ.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 inferInstance
  exact ⟨@asIso _ _ _ _ _ hu ≪≫
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ j.toBase).mapIso
      ((asIso (DerivedCategory.Q.map ψ.hom)).symm ≪≫
        (extensionByZeroDerivedIso Λ j.immersion K.obj).symm)⟩

/-- The spectrum of an algebraic closure of a residue field of a scheme of a big étale site lies
in the site: `Spec κ(y)` does, being a quasi-compact monomorphism into the scheme, and the
algebraic closure is no larger than `max ℵ₀ #κ(y)`. -/
theorem contains_spec_algebraicClosure_residueField (B : BigEtaleSite.{u}) (Y : B.Scheme)
    (y : Y.obj) : B.Contains (Spec (.of (AlgebraicClosure (Y.obj.residueField y)))) := by
  have : QuasiCompact (Y.obj.fromSpecResidueField y) := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    exact fun W _ => (Set.toFinite (Y.obj.fromSpecResidueField y ⁻¹' (W : Set Y.obj))).isCompact
  have hκ : B.Contains (Spec (Y.obj.residueField y)) :=
    Scheme.size_lt_of_mono_quasiCompact (Y.obj.fromSpecResidueField y) Y.property
  have hK : Cardinal.mk (AlgebraicClosure (Y.obj.residueField y)) ≤
      (Spec (Y.obj.residueField y)).size ^ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max (Y.obj.residueField y) _).trans
      ((max_le (mk_le_size_of_nonempty (𝟙 (Spec (Y.obj.residueField y))))
        (Spec (Y.obj.residueField y)).aleph0_le_size).trans
          (Cardinal.self_le_power _ Cardinal.one_le_aleph0))
  exact Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit _ hκ hK

/-- The compactification `j_U : U ⟶ X` of `j_U ≫ h` over `Y`, for `h : X ⟶ Y` proper. -/
def compactificationOfOpenImmersionProper {U X Y : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU]
    (h : X ⟶ Y) [IsProper h] : CompactificationOf (Over.mk (jU ≫ h)) :=
  ⟨StructuredArrow.mk (Y := Over.mk h) (Over.homMk jU rfl : Over.mk (jU ≫ h) ⟶ Over.mk h),
    ⟨inferInstanceAs (IsOpenImmersion jU), inferInstanceAs (IsProper h)⟩⟩

/-- **Extension by zero along a quasi-compact open immersion into a quasi-compact and
quasi-separated scheme preserves `D_ctf`**, on complexes. -/
theorem IsCtf.extensionByZero_of_isOpenImmersion (B : BigEtaleSite.{u}) {U X : B.Scheme}
    [CompactSpace U.obj] [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (j : U ⟶ X)
    [IsOpenImmersion (B.inclusion.map j)] {C : CochainComplex (EtaleModules.{u, 0} Λ U.obj) ℤ}
    (hC : IsCtf B U Λ (DerivedCategory.Q.obj C)) :
    IsCtf B X Λ (DerivedCategory.Q.obj
      (((etaleModuleExtensionByZero.{u, 0} Λ (B.inclusion.map j)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C)) := by
  let Cl : TopologicalSpace.Closeds X.obj :=
    ⟨(Set.range j.hom.base)ᶜ, (B.inclusion.map j).isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal Cl).subschemeι
  let ii : (⟨_, Scheme.size_lt_of_isClosedImmersion i X.property⟩ : B.Scheme) ⟶ X :=
    ObjectProperty.homMk i
  have : IsClosedImmersion (B.inclusion.map ii) := inferInstanceAs (IsClosedImmersion i)
  have hrange : Set.range i.base = (Set.range j.hom.base)ᶜ :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _
  refine IsCtf.extensionByZero B Λ j ii ?_ hC
  show Set.range j.hom.base = (Set.range i.base)ᶜ
  rw [hrange, compl_compl]

/-- The geometric fibre of a morphism locally of finite type over the geometric point of `y` with
residue field an algebraic closure of `κ(y)` has the dimension of the fibre over `y`. -/
theorem topologicalKrullDim_pullback_geometricPointOfPoint {U Y : Scheme.{u}} (f : U ⟶ Y)
    [LocallyOfFiniteType f] (y : Y) :
    topologicalKrullDim (pullback f (GeometricPoint.ofPoint Y y).hom : Scheme.{u}) =
      topologicalKrullDim (f.fiber y) := by
  let φ : Y.residueField y ⟶ CommRingCat.of (GeometricPoint.ofPoint Y y).residueField :=
    CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))
  have hs : (GeometricPoint.ofPoint Y y).hom = Spec.map φ ≫ Y.fromSpecResidueField y :=
    Scheme.SpecToEquivOfField_symm_apply _ _ _
  let e : pullback f (GeometricPoint.ofPoint Y y).hom ≅
      pullback (pullback.snd f (Y.fromSpecResidueField y)) (Spec.map φ) :=
    pullback.congrHom rfl hs ≪≫
      (pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) (Spec.map φ)).symm
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
  exact topologicalKrullDim_pullback_spec_algebraMap (Y.residueField y)
    (AlgebraicClosure (Y.residueField y)) (pullback.snd f (Y.fromSpecResidueField y))

/-- **Compactly supported cohomology of a curve is the cohomology of a proper curve.** Let `V` be
a scheme of the big étale site, separated, quasi-compact and locally of finite type over a field
`k` with `Spec k` in the site, of dimension at most one, `j` a compactification of `V` over `k`,
and `E` a complex on `V` concentrated in degrees `[a, b]` lying in `D_ctf(V, Λ)`. Then `RΓ_c(V, E)`
is `RΓ(Z, D)` for a scheme `Z` of the site, proper of dimension at most one over `k`, and a
complex `D` on `Z` concentrated in degrees `[a, b]` lying in `D_ctf(Z, Λ)`. -/
theorem exists_compactlySupportedCohomologyUnboundedIso_of_topologicalKrullDim_le_one
    (B : BigEtaleSite.{u}) [Finite Λ] (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (V : Scheme.{u}) (hV : B.Contains V) (f : V ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] (hdim : topologicalKrullDim V ≤ 1)
    (j : CompactificationOf (Over.mk f)) (E : CochainComplex (EtaleModules.{u, 0} Λ V) ℤ)
    (a b : ℤ) [E.IsStrictlyGE a] [E.IsStrictlyLE b]
    (hE : IsCtf B ⟨V, hV⟩ Λ (DerivedCategory.Q.obj E)) :
    ∃ (Z : B.Scheme) (q : Z.obj ⟶ Spec (.of k)) (_ : IsProper q), topologicalKrullDim Z.obj ≤ 1 ∧
      ∃ (D : CochainComplex (EtaleModules.{u, 0} Λ Z.obj) ℤ) (_ : D.IsStrictlyGE a)
        (_ : D.IsStrictlyLE b), IsCtf B Z Λ (DerivedCategory.Q.obj D) ∧
        Nonempty ((compactlySupportedCohomologyUnbounded.{u, 0} k f j Λ).obj
            (DerivedCategory.Q.obj E) ≅
          DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} Λ Z.obj).obj
            (DerivedCategory.Plus.Q.obj ⟨D, ⟨a, inferInstance⟩⟩))) := by
  obtain ⟨Zs, q, jZ', hjZ', hcomm, hproj, -, hdimZ, -, -, -, -⟩ :=
    Stacks.CurveProjectiveCompletion.exists_projective_completion_aux
      (fun W _ _ hdimW =>
        AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one
          W hdimW) k f hdim
  have := hjZ'
  have hqP : IsProper q := isProper_of_isProjectiveMorphism q hproj
  let jZ : CompactificationOf (Over.mk f) :=
    ⟨StructuredArrow.mk (Y := Over.mk q) (Over.homMk jZ' hcomm : Over.mk f ⟶ Over.mk q),
      ⟨hjZ', hqP⟩⟩
  have : (DerivedCategory.Q.obj E).IsGE a := (DerivedCategory.isGE_Q_obj_iff _ _).2 inferInstance
  obtain ⟨e⟩ := nonempty_compactlySupportedCohomologyUnboundedIso Λ k f jZ ⟨E, ⟨a, inferInstance⟩⟩
  let Z : B.Scheme := ⟨Zs, Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact q hk⟩
  let D := ((etaleModuleExtensionByZero.{u, 0} Λ jZ').mapHomologicalComplex
    (ComplexShape.up ℤ)).obj E
  have : CochainComplex.IsStrictlyGE D a := inferInstanceAs (CochainComplex.IsStrictlyGE
    (((etaleModuleExtensionByZero.{u, 0} Λ jZ').mapHomologicalComplex (ComplexShape.up ℤ)).obj E) a)
  have : CochainComplex.IsStrictlyLE D b := inferInstanceAs (CochainComplex.IsStrictlyLE
    (((etaleModuleExtensionByZero.{u, 0} Λ jZ').mapHomologicalComplex (ComplexShape.up ℤ)).obj E) b)
  have hD : IsCtf B Z Λ (DerivedCategory.Q.obj D) := by
    let Vb : B.Scheme := ⟨V, hV⟩
    have : CompactSpace Vb.obj := QuasiCompact.compactSpace_of_compactSpace f
    have : CompactSpace Z.obj := QuasiCompact.compactSpace_of_compactSpace q
    have : QuasiSeparatedSpace Z.obj := quasiSeparatedSpace_of_quasiSeparated q
    let jj : Vb ⟶ Z := ObjectProperty.homMk jZ'
    have : IsOpenImmersion (B.inclusion.map jj) := hjZ'
    exact IsCtf.extensionByZero_of_isOpenImmersion Λ B jj hE
  exact ⟨Z, q, hqP, hdimZ, D, inferInstance, inferInstance, hD,
    ⟨(etaleModuleDerivedGlobalSectionsUnbounded.{u, 0} Λ (Spec (.of k))).mapIso
      (derivedLowerShriekUnboundedIndependenceIso Λ j jZ (DerivedCategory.Q.obj E) a
        (torsionCohomologyProperty_etaleModuleForgetDerived_of_finite Λ _)) ≪≫ e⟩⟩

/-- **The stalk of `Rh_*(j_{U!} C)` at a geometric point is the cohomology of a proper scheme of
dimension at most one.** Let `h : X ⟶ Y` be proper, `j_U : U ⟶ X` a quasi-compact open immersion
such that the fibres of `j_U ≫ h` have dimension at most one, `Λ` a finite ring, `C` a complex of
sheaves of `Λ`-modules on `U` concentrated in degrees `[a, b]` lying in `D_ctf(U, Λ)`, and `I` a
resolution of `j_{U!} C` by injectives. For every point `y` of `Y` the stalk of `h_* I` at the
geometric point `ȳ` over `y` (with residue field an algebraic closure of `κ(y)`) is
`RΓ(Z, D)` for a scheme `Z` of the big étale site, proper of dimension at most one over `κ(ȳ)`,
and a complex `D` on `Z` concentrated in degrees `[a, b]` lying in `D_ctf(Z, Λ)`. -/
theorem exists_derivedEtaleModuleStalk_directImage_iso (B : BigEtaleSite.{u}) [Finite Λ]
    (X Y U : B.Scheme) (h : X.obj ⟶ Y.obj) [IsProper h] (jU : U.obj ⟶ X.obj) [IsOpenImmersion jU]
    [QuasiCompact jU] (hfib : ∀ y : Y.obj, topologicalKrullDim ((jU ≫ h).fiber y) ≤ 1)
    (C : CochainComplex (EtaleModules.{u, 0} Λ U.obj) ℤ) (a b : ℤ) [C.IsStrictlyGE a]
    [C.IsStrictlyLE b] (hC : IsCtf B U Λ (DerivedCategory.Q.obj C))
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (ψ : (etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj ⟨C, ⟨a, inferInstance⟩⟩
      ⟶ I) [QuasiIso ψ.hom] (hI : ∀ n, Injective (I.obj.X n)) (y : Y.obj) :
    ∃ (Z : B.Scheme) (fZ : Z.obj ⟶ Spec (.of (GeometricPoint.ofPoint Y.obj y).residueField))
      (_ : IsProper fZ), topologicalKrullDim Z.obj ≤ 1 ∧
      ∃ (D : CochainComplex (EtaleModules.{u, 0} Λ Z.obj) ℤ) (_ : D.IsStrictlyGE a)
        (_ : D.IsStrictlyLE b), IsCtf B Z Λ (DerivedCategory.Q.obj D) ∧
        Nonempty ((derivedEtaleModuleStalk.{u, 0} B Y Λ (GeometricPoint.ofPoint Y.obj y)).obj
          (DerivedCategory.Q.obj ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj
            I).obj) ≅
          DerivedCategory.Plus.ι.obj ((etaleModuleDerivedGlobalSections.{u, 0} Λ Z.obj).obj
            (DerivedCategory.Plus.Q.obj ⟨D, ⟨a, inferInstance⟩⟩))) := by
  classical
  let f := jU ≫ h
  have : LocallyOfFiniteType f :=
    @locallyOfFiniteType_comp _ _ _ jU h (locallyOfFiniteType_of_isOpenImmersion jU)
      IsProper.toLocallyOfFiniteType
  let jX := compactificationOfOpenImmersionProper jU h
  let s := GeometricPoint.ofPoint Y.obj y
  let Ω := s.residueField
  let K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U.obj) := ⟨C, ⟨a, inferInstance⟩⟩
  obtain ⟨eA⟩ := nonempty_derivedEtaleModuleStalkIsoGlobalSectionsInverseImage B Y Λ s
    ((etaleModuleDirectImage.{u, 0} Λ h).mapCochainComplexPlus.obj I)
  let ψ' : (etaleModuleExtensionByZero.{u, 0} Λ jX.immersion).mapCochainComplexPlus.obj K ⟶ I := ψ
  have : QuasiIso ψ'.hom := ‹QuasiIso ψ.hom›
  obtain ⟨e₂⟩ := nonempty_derivedLowerShriekUnboundedIsoDirectImage_of_injective Λ jX K I ψ' hI
  have : (DerivedCategory.Q.obj C).IsGE a := (DerivedCategory.isGE_Q_obj_iff _ _).2 inferInstance
  let eF := derivedLowerShriekUnboundedGeometricFibreIso.{u, 0} Λ f jX s
    (fun _ _ p _ ↦ cohomologyCommutesWithBaseChange_of_isProper p) (DerivedCategory.Q.obj C) a
    (torsionCohomologyProperty_etaleModuleForgetDerived_of_finite Λ _)
  let V := pullback f s.hom
  let fs : V ⟶ Spec (.of Ω) := pullback.snd f s.hom
  let pV : V ⟶ U.obj := pullback.fst f s.hom
  let jXs := jX.baseChange (IsPullback.of_hasPullback f s.hom)
  let E := ((etaleModuleInverseImage.{u, 0} Λ pV).mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  let eL : (etaleModuleRingDerivedInverseImage.{u, 0} Λ pV).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj E :=
    (etaleModuleInverseImage.{u, 0} Λ pV).mapDerivedCategoryFactors.app C
  have : CochainComplex.IsStrictlyGE E a := inferInstanceAs (CochainComplex.IsStrictlyGE
    (((etaleModuleInverseImage.{u, 0} Λ pV).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) a)
  have : CochainComplex.IsStrictlyLE E b := inferInstanceAs (CochainComplex.IsStrictlyLE
    (((etaleModuleInverseImage.{u, 0} Λ pV).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) b)
  have hΩ : B.Contains (Spec (.of Ω)) := contains_spec_algebraicClosure_residueField B Y y
  have hVB : B.Contains V := Scheme.size_pullback_lt f s.hom U.property hΩ
  have hE : IsCtf B ⟨V, hVB⟩ Λ (DerivedCategory.Q.obj E) :=
    (IsCtf.pullback B Λ (ObjectProperty.homMk pV : (⟨V, hVB⟩ : B.Scheme) ⟶ U) hC).of_iso B _ Λ eL
  obtain ⟨Z, q, hqP, hdimZ, D, hDa, hDb, hD, ⟨e⟩⟩ :=
    exists_compactlySupportedCohomologyUnboundedIso_of_topologicalKrullDim_le_one Λ B Ω hΩ V hVB
      fs ((topologicalKrullDim_pullback_geometricPointOfPoint f y).le.trans (hfib y)) jXs E a b hE
  exact ⟨Z, q, hqP, hdimZ, D, hDa, hDb, hD, ⟨eA ≪≫
    (etaleModuleDerivedGlobalSectionsUnbounded.{u, 0} Λ (Spec (.of Ω))).mapIso
      ((etaleModuleRingDerivedInverseImage.{u, 0} Λ s.hom).mapIso e₂) ≪≫ eF ≪≫
    (compactlySupportedCohomologyUnbounded.{u, 0} Ω fs jXs Λ).mapIso eL ≪≫ e⟩⟩

end Stacks.EtaleCohomology

end
