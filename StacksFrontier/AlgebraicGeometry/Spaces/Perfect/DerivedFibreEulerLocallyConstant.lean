module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardTensorGenericCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.EulerCharacteristicOnPoints
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtalePerfectConverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# The derived-fibre Euler characteristic of a perfect object is locally constant

Let `Y` be an algebraic space over a scheme `S` and let `K` be a perfect object of `D(𝒪_Y)`
(Stacks 08G5).  The derived-fibre Euler characteristic
`χ_K(y) = ∑ (-1)^n dim_k H^n(K ⊗^𝐋 k)`, for a field-valued point `Spec(k) ⟶ Y` representing
`y ∈ |Y|`, is a locally constant function on `|Y|`.  This is Stacks 0D1Z, for the actual
function `AlgebraicGeometry.Space.derivedFibreEuler`.

The source's proof is "étale localization reduces to the case of schemes".  Here: every point
of `|Y|` lies in the image of an étale chart `W` over which a fixed perfect representative `E`
of `K` has a strictly perfect model `P` (perfectness at an atlas, and a covering sieve is
jointly surjective on points).  On the chart, `Lψ^*K` is the class of the strictly perfect
complex `ψ^*P`, so it has quasi-coherent cohomology and is `ε^*ω` (Stacks 071Q); transporting
`ψ^*P` to the small étale site of the scheme `T` of the chart shows that `ε^*ω` is perfect there,
whence `ω` is a perfect object of `D(𝒪_T)` (Stacks 08HG).  By
`AlgebraicGeometry.Space.derivedFibreBettiAt_representedDerivedAssociatedModule` the function
`χ_K` read on the chart is the Zariski derived-fibre Euler characteristic of `ω`, which is
locally constant (Stacks 0BDJ), and the chart is open on points.

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_iso_derivedPullback_chartToSpace`: on an étale
  chart carrying a strictly perfect model of `E`, `Lψ^*E ≅ ε^*ω` for a perfect `ω` on the scheme
  of the chart.
* `AlgebraicGeometry.Space.isLocallyConstant_derivedFibreEuler`: **Stacks 0D1Z**.

## Implementation notes

The base registration of Stacks 0D1Z,
`AlgebraicGeometry.Space.isLocallyConstant_of_isEtaleLocallyDerivedFibreChi`, takes the Euler
function as data together with the property that on *every* étale chart it is the Euler
characteristic of a perfect object of the chart's scheme.  The statement here concerns the
constructed function and assumes only that `K` is perfect.  Its proof needs a perfect object on
charts carrying strictly perfect models only, which avoids transporting perfectness from the
small étale site of `Y` to the slice at an arbitrary chart.

## References

* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (Y : AlgebraicSpaces B S hS) (W : SmallEtale B S hS Y.1)

/-- Restriction to the slice at an étale chart, read on the small étale site of the chart, is
left exact: it is the direct image along a continuous functor. -/
theorem preservesFiniteLimits_chartSmallEtaleRestrictionFunctor :
    PreservesFiniteLimits (chartSmallEtaleRestrictionFunctor Y W) :=
  @SheafOfModules.preservesFiniteLimits_pushforward _ _ _ _
    (SmallEtale.chartLocalizationEquivalence B S hS Y.1 W).functor _ _
    (isContinuous_chartLocalization_chartSpace B S hS Y W) _ _ _

/-- Restriction to the slice at an étale chart, read on the small étale site of the chart, is
right exact: the comparison functor of Stacks 04M0 is continuous and cocontinuous. -/
theorem preservesFiniteColimits_chartSmallEtaleRestrictionFunctor :
    PreservesFiniteColimits (chartSmallEtaleRestrictionFunctor Y W) :=
  have : PreservesColimitsOfSize.{u, u} (chartSmallEtaleRestrictionFunctor Y W) :=
    @Stacks.SheafOfModules.pushforward_preservesColimits.{u + 1, u, u, u + 1, u, u} _ _ _ _
      (SmallEtale.topology B S hS (chartSpace B S hS Y W).1)
      ((SmallEtale.topology B S hS Y.1).over W) _ _ _ _
      (SmallEtale.chartLocalizationEquivalence B S hS Y.1 W).functor
      (isContinuous_chartLocalization_chartSpace B S hS Y W)
      (isCocontinuous_chartLocalizationEquivalence_functor B S hS Y W) _ _ (𝟙 _)
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Restriction to the slice at an étale chart is additive. -/
instance additive_chartSmallEtaleRestrictionFunctor :
    (chartSmallEtaleRestrictionFunctor Y W).Additive :=
  ⟨rfl⟩

/-- Restriction to the slice at a chart followed by the comparison of Stacks 04M0 is étale
restriction along the chart, degreewise on complexes. -/
noncomputable def chartSmallEtaleRestrictionComplexIso
    (E : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) :
    haveI := etaleModulePullback_additive.{u, u} B S hS (chartToSpace B S hS Y W)
      (isEtale_chartToSpace B S hS Y W)
    ((chartSmallEtaleRestrictionFunctor Y W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((smallEtaleRingedSite B S hS Y.1 Y.2).restrictComplex E W) ≅
      ((etaleModulePullback.{u, u} B S hS (chartToSpace B S hS Y W)
        (isEtale_chartToSpace B S hS Y W)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E :=
  haveI := etaleModulePullback_additive.{u, u} B S hS (chartToSpace B S hS Y W)
    (isEtale_chartToSpace B S hS Y W)
  HomologicalComplex.Hom.isoOfComponents
    (fun i => chartSmallEtaleRestrictionFunctorObjIso Y (E.X i) W)
    (fun i j _ => by ext; rfl)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
/- The standard model of the derived category is forced by
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
attribute [local instance 10000] HasDerivedCategory.standard

/-- **The derived pullback along an étale morphism is étale restriction of a representative**:
`Lf^*` of the class of `E` is the class of the degreewise étale restriction of `E`. -/
theorem nonempty_derivedPullback_iso_etaleModulePullback {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (E : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ) :
    haveI := etaleModulePullback_additive.{u, u} B S hS f hf
    Nonempty ((smallEtaleDerivedModulePullback B S hS f).obj (DerivedCategory.Q.obj E) ≅
      DerivedCategory.Q.obj (((etaleModulePullback.{u, u} B S hS f hf).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E)) := by
  have := etaleModulePullback_additive.{u, u} B S hS f hf
  have := preservesFiniteLimits_etaleModulePullback B S hS f hf
  have := preservesFiniteColimits_etaleModulePullback B S hS f hf
  obtain ⟨Kh, hK, s, hs⟩ :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
      (Y := smallEtaleRingedTopos B S hS Y)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj E)
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective Kh
  obtain ⟨s', rfl⟩ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective s
  have hs' : QuasiIso s' := by
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hs
  let F := etaleModulePullback.{u, u} B S hS f hf
  have : F.Additive := etaleModulePullback_additive.{u, u} B S hS f hf
  have : PreservesFiniteLimits F := preservesFiniteLimits_etaleModulePullback B S hS f hf
  have : PreservesFiniteColimits F := preservesFiniteColimits_etaleModulePullback B S hS f hf
  let e₀ : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj E := asIso (DerivedCategory.Q.map s')
  have e₂ : Nonempty (DerivedCategory.Q.obj
      (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≅ DerivedCategory.Q.obj
      (((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    (@mapHomologicalComplex_obj_congr _ _ _ _ _ _ _ _
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (pullbackModules_smallEtaleRingedToposHom_additive B S hS f))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
        (modulePullback B S hS f) (modulePullback_additive f))
      (pullbackModules_eq_modulePullback B S hS f) P
      (fun C => Nonempty (DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj
      (((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))).2
        ⟨Iso.refl _⟩
  let e₃ : ((modulePullback B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
    ((NatIso.mapHomologicalComplex (modulePullbackIsoEtaleModulePullback B S hS f hf)
      (ComplexShape.up ℤ)).app P)
  exact ⟨(smallEtaleDerivedModulePullback B S hS f).mapIso e₀.symm ≪≫
    derivedPullbackObjIsoOfIsKFlat B S hS f P hK ≪≫ e₂.some ≪≫ DerivedCategory.Q.mapIso e₃ ≪≫
    (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e₀ ≪≫
    F.mapDerivedCategoryFactors.app E⟩

/-- The comparison of modules on the small étale site of a scheme with modules on the small étale
site of the algebraic space it represents carries the structure sheaf to the structure sheaf. -/
noncomputable def representedSmallEtaleModuleEquivalenceFunctorUnitIso (T : BigFppfOver B S hS) :
    (representedSmallEtaleModuleEquivalence B S hS T).functor.obj
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T)) ≅
      SheafOfModules.unit (representedStructureRingSheaf B S hS T) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (fun _ _ _ => by ext; rfl))

/-- An exact additive functor carries a quasi-isomorphism of cochain complexes to a
quasi-isomorphism: it preserves homology. -/
theorem _root_.CategoryTheory.Functor.quasiIso_map_of_exact {A A' : Type*}
    [Category A] [Abelian A] [Category A'] [Abelian A'] (F : A ⥤ A') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {P Q : CochainComplex A ℤ}
    (φ : P ⟶ Q) (h : QuasiIso φ) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have := h
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  infer_instance

variable (Y : AlgebraicSpaces B S hS)

/-- **A strictly perfect model on an étale chart gives a perfect object on its scheme.**  Let
`E` be a complex of `𝒪_Y`-modules with a strictly perfect model over the étale chart `W`, with
scheme `T` and structure morphism `ψ : h_T ⟶ Y`.  Then `Lψ^*E ≅ ε^*ω` for a perfect object `ω`
of `D(𝒪_T)`.

The class of `E` restricted to `W` is that of the strictly perfect `P` read on the small étale
site of `h_T`; it has quasi-coherent cohomology, so it is `ε^*ω` (Stacks 071Q), and transported
to the small étale site of `T` it is the class of a strictly perfect complex, so `ε^*ω` is
perfect there and `ω` is perfect by Stacks 08HG. -/
theorem exists_isPerfect_iso_derivedPullback_chartToSpace
    (E : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ)
    (W : SmallEtale B S hS Y.1)
    (hW : (smallEtaleRingedSite B S hS Y.1 Y.2).HasStrictlyPerfectQuasiIso E W) :
    ∃ ω : DerivedCategory
        ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W)).Modules,
      RingedSpace.IsPerfect.{u, u + 1}
          (X := ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS Y.1).obj W)).toRingedSpace) ω ∧
        Nonempty ((representedDerivedAssociatedModule B S hS
            ((SmallEtale.toOver B S hS Y.1).obj W)).obj ω ≅
          (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj
            (DerivedCategory.Q.obj E)) := by
  obtain ⟨P, hP, q, hq⟩ := hW
  let T := (SmallEtale.toOver B S hS Y.1).obj W
  have : PreservesFiniteLimits (chartSmallEtaleRestrictionFunctor Y W) :=
    preservesFiniteLimits_chartSmallEtaleRestrictionFunctor B S hS Y W
  have : PreservesFiniteColimits (chartSmallEtaleRestrictionFunctor Y W) :=
    preservesFiniteColimits_chartSmallEtaleRestrictionFunctor B S hS Y W
  let P₁ := ((chartSmallEtaleRestrictionFunctor Y W).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  have hP₁ : IsStrictlyPerfect (representedStructureRingSheaf B S hS T) P₁ :=
    SheafOfModules.isStrictlyPerfect_map (chartSmallEtaleRestrictionFunctor Y W)
      (chartSmallEtaleRestrictionFunctorUnitIso Y W) hP
  have := Functor.quasiIso_map_of_exact (chartSmallEtaleRestrictionFunctor Y W) q hq
  obtain ⟨e₂⟩ := nonempty_derivedPullback_iso_etaleModulePullback B S hS (chartToSpace B S hS Y W)
    (isEtale_chartToSpace B S hS Y W) E
  let eM : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj
      (DerivedCategory.Q.obj E) ≅ DerivedCategory.Q.obj P₁ :=
    e₂ ≪≫ (DerivedCategory.Q.mapIso
      (chartSmallEtaleRestrictionComplexIso B S hS Y W E)).symm ≪≫ (asIso (DerivedCategory.Q.map
      (((chartSmallEtaleRestrictionFunctor Y W).mapHomologicalComplex
        (ComplexShape.up ℤ)).map q))).symm
  have hMperf : (smallEtaleRingedSite B S hS (chartSpace B S hS Y W).1
      (chartSpace B S hS Y W).2).IsPerfect
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj
        (DerivedCategory.Q.obj E)) :=
    let ⟨E', hE', ⟨i⟩⟩ := RingedSite.isPerfect_Q_obj_of_isStrictlyPerfect _ P₁ hP₁
    ⟨E', hE', ⟨i ≪≫ eM.symm⟩⟩
  obtain ⟨ω, -, ⟨eω⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS T _
    (derivedCategoryB_of_isPerfect B S hS (chartSpace B S hS Y W) _ hMperf)
  refine ⟨ω, ?_, ⟨eω⟩⟩
  let X := (BigFppfOver.toScheme B S hS).obj T
  let eqv := representedSmallEtaleModuleEquivalence B S hS T
  let εs := _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B) X
    T.left.property
  have : PreservesFiniteLimits εs :=
    _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule _ _ _
  have : (εs ⋙ eqv.functor).Additive :=
    additive_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  have : PreservesFiniteLimits (εs ⋙ eqv.functor) :=
    preservesFiniteLimits_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  have : PreservesFiniteColimits (εs ⋙ eqv.functor) :=
    preservesFiniteColimits_representedAssociatedModule B S hS T
      (isAlgebraicSpace_yoneda B S hS T)
  let ηΨ : eqv.inverse.obj (SheafOfModules.unit (representedStructureRingSheaf B S hS T)) ≅
      SheafOfModules.unit (representedSchemeStructureSheaf B S hS T) :=
    eqv.inverse.mapIso (representedSmallEtaleModuleEquivalenceFunctorUnitIso B S hS T).symm ≪≫
      eqv.unitIso.symm.app _
  let P₂ := (eqv.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj P₁
  have hP₂ : IsStrictlyPerfect (representedSchemeStructureSheaf B S hS T) P₂ :=
    SheafOfModules.isStrictlyPerfect_map eqv.inverse ηΨ hP₁
  let c := Stacks.DerivedQCoh.mapDerivedCategoryCompIso (εs ⋙ eqv.functor) eqv.inverse εs
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft εs eqv.unitIso.symm ≪≫
      Functor.rightUnitor εs)
  let e₃ : εs.mapDerivedCategory.obj ω ≅ DerivedCategory.Q.obj P₂ :=
    (c.app ω).symm ≪≫ eqv.inverse.mapDerivedCategory.mapIso (eω ≪≫ eM) ≪≫
      eqv.inverse.mapDerivedCategoryFactors.app P₁
  have hEt : (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) X
      T.left.property).IsPerfect (εs.mapDerivedCategory.obj ω) :=
    let ⟨E', hE', ⟨i⟩⟩ := RingedSite.isPerfect_Q_obj_of_isStrictlyPerfect
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B) X
        T.left.property) P₂ hP₂
    ⟨E', hE', ⟨i ≪≫ e₃.symm⟩⟩
  exact Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace ω
    (_root_.AlgebraicGeometry.SmallEtale.isPerfectZariski_of_isPerfectSmallEtale
      (associatedBigEtaleSite B) X T.left.property ω hEt)

attribute [local instance] pointTopology

open _root_.AlgebraicGeometry.Space.Topology

/-- **Stacks 0D1Z.**  Let `Y` be an algebraic space and `K` a perfect object of `D(𝒪_Y)`.  The
derived-fibre Euler characteristic `y ↦ ∑ (-1)^n dim_k H^n(K ⊗^𝐋 k)` is locally constant on
`|Y|`.

The function is `AlgebraicGeometry.Space.derivedFibreEuler`, the alternating sum of the
dimensions of the cohomology of `Lp^*K` for a field-valued point `p` representing the point; by
`AlgebraicGeometry.Space.derivedFibreEuler_class` it may be computed at any representative. -/
@[stacks 0D1Z, sga "6 III 5.5" "(i), special case"]
theorem isLocallyConstant_derivedFibreEuler (Y : AlgebraicSpaces B S hS)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K) :
    IsLocallyConstant (derivedFibreEuler Y K) := by
  have hKq := derivedCategoryB_of_isPerfect B S hS Y K hK
  obtain ⟨E, hE, ⟨eK⟩⟩ := hK
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨U, φ, hsurj, het⟩ := Y.2.exists_atlas
  let V₀ : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk φ, het⟩
  have hx : x ∈ Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V₀)) V₀.obj.hom) :=
    (surjective_iff_surjective_pointsMap B S hS Y.1 Y.2 U φ).mp hsurj x
  obtain ⟨Sv, hSv, hmod⟩ := hE V₀
  obtain ⟨W, k, hk, hxW⟩ :=
    SmallEtale.exists_mem_range_pointsMap_of_mem_topology B S hS Y V₀ hSv x hx
  obtain ⟨V', h, f, hf, -⟩ := hk
  have hW := RingedSite.hasStrictlyPerfectQuasiIso_of_hom _ E h (hmod f hf)
  obtain ⟨ω, hω, ⟨eω⟩⟩ := exists_isPerfect_iso_derivedPullback_chartToSpace B S hS Y E W hW
  let T := (SmallEtale.toOver B S hS Y.1).obj W
  have hpc := DerivedFibreBetti.isPseudoCoherent_of_isPerfect ω hω
  have key : ∀ p : FieldValuedPoint B S hS (yoneda.obj T),
      derivedFibreEuler Y K (pointsMap B S hS (yoneda.obj T) W.obj.hom (p.class B S hS _)) =
        DerivedFibreBetti.chiDerivedFibre _ ω hpc (schemePoint B S hS T p) := by
    intro p
    refine (derivedFibreEuler_class B S hS Y K hKq
      (p.map B S hS (yoneda.obj T) W.obj.hom)).trans (Eq.trans (finsum_congr fun n => ?_)
        (DerivedFibreBetti.chiDerivedFibre_apply _ ω hpc _).symm)
    refine congrArg (fun m : ℕ => (n.negOnePow : ℤ) * (m : ℤ)) ?_
    calc derivedFibreBettiAt Y K n (p.map B S hS (yoneda.obj T) W.obj.hom)
        = derivedFibreBettiAt (chartSpace B S hS Y W)
            ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj K) n p :=
          (derivedFibreBettiAt_derivedPullback Y (chartToSpace B S hS Y W) K n p).symm
      _ = derivedFibreBettiAt (schemeSpace T)
            ((representedDerivedAssociatedModule B S hS T).obj ω) n p :=
          (derivedFibreBettiAt_congr _ (eω ≪≫
            (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).mapIso eK) n p).symm
      _ = _ := (derivedFibreBettiAt_representedDerivedAssociatedModule B S hS T ω n p).trans
            (DerivedFibreBetti.derivedFiberBetti_apply _ ω hpc n _).symm
  let g := derivedFibreEuler Y K ∘ pointsMap B S hS (yoneda.obj T) W.obj.hom
  have hg : g = DerivedFibreBetti.chiDerivedFibre _ ω hpc ∘ schemePointsHomeomorph B S hS T := by
    funext z
    induction z using Quot.ind with
    | mk p => exact key p
  have hloc : IsLocallyConstant g := by
    rw [hg]
    exact (DerivedFibreBetti.isLocallyConstant_chiDerivedFibre _ ω hω).comp_continuous
      (schemePointsHomeomorph B S hS T).continuous
  obtain ⟨z, rfl⟩ := hxW
  refine ⟨pointsMap B S hS (yoneda.obj T) W.obj.hom '' (g ⁻¹' {g z}),
    isOpenMap_pointsMap_of_etale B S hS Y.2 T W.obj.hom W.property _ (hloc.isOpen_fiber _),
    ⟨z, rfl, rfl⟩, ?_⟩
  rintro _ ⟨_, hz', rfl⟩
  exact hz'

end AlgebraicGeometry.Space

end
