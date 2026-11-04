module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ChartLocalPerfectness
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.Homology.PseudoCoherent.Coherent
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence on a Noetherian algebraic space

Let `X` be a Noetherian algebraic space over a scheme `S` and `E` an object of `D_QCoh(𝒪_X)`.
For `m ∈ ℤ`, `E` is `m`-pseudo-coherent if and only if `Hⁱ(E)` is coherent for `i ≥ m` and zero
for `i ≫ 0`. In particular `E` is pseudo-coherent if and only if it lies in `D⁻_Coh(𝒪_X)`. This
is Stacks 08IK.

## Main results

All in the namespace `AlgebraicGeometry.Space`.

* `exists_approximation_of_isPseudoCoherentFrom_representedAffineDerivedSections`: on a
  represented affine algebraic space `Spec R`, an `m`-pseudo-coherent `RΓ(E)` gives a bounded
  complex of finite free modules approximating `E` above `m`.
* `isPseudoCoherentFrom_of_isCoherent_homology_of_qcohDerived`: the implication (1) ⇒ (2) over a
  locally Noetherian algebraic space.
* `isCoherent_homology_iff_isPseudoCoherentFrom`: **Stacks 08IK**.
* `isPseudoCoherent_iff_isCoherent_homology`: **Stacks 08IK**, the final statement.

## Implementation notes

The implication (1) ⇒ (2) is checked on the affine étale charts `W = Spec R` of `X`
(`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_chart_approximation`). There `E|_W` is the
associated object of `RΓ(E|_W)` in `D(R)`, whose cohomology `Hⁱ(RΓ(E|_W)) = Γ(W, Hⁱ(E))` is a
finite `R`-module for `i ≥ m` and vanishes for `i ≫ 0`. As `R` is Noetherian, `RΓ(E|_W)` is
`m`-pseudo-coherent (Stacks 066E), and the associated complex of a bounded complex of finite free
`R`-modules approximating it approximates `E|_W`. The source reduces instead to the Zariski site
of a representable `X` and to Stacks 08E8.

The implication (2) ⇒ (1) is the coherence clause
`AlgebraicGeometry.Space.isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_isNoetherian`
together with the vanishing
`AlgebraicGeometry.Space.exists_isZero_homology_of_isPseudoCoherentFrom`.

## References

* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

section Affine

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- **An `m`-pseudo-coherent `RΓ(E)` approximates `E` above `m`.** Let `U = Spec R` be affine and
`E ∈ D_QCoh(𝒪_U)`. If `RΓ(E)` is an `m`-pseudo-coherent object of `D(R)`, there are a bounded
complex `P` of retracts of finite free `𝒪_U`-modules and a map `P ⟶ E` inducing isomorphisms on
`Hʲ` for `j > m` and a surjection on `Hᵐ`: the associated complex of an approximation of `RΓ(E)`
by a bounded complex of finite free `R`-modules, followed by the counit `Φ(RΓ(E)) ≅ E`. -/
theorem exists_approximation_of_isPseudoCoherentFrom_representedAffineDerivedSections
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)))
    (hE : QcohDerived B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ E) (m : ℤ)
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((representedAffineDerivedSections B S hS U).obj E) m) :
    ∃ P : CochainComplex (Modules.{u, u} B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U)) ℤ,
      (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O))
          (P.X j)) ∧
      (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
      ∃ φ : (DerivedCategory.Q).obj P ⟶ E,
        (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map φ)) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map φ) := by
  obtain ⟨N, hN, α, hiso, hepi⟩ := hM
  obtain ⟨a, ha⟩ := hN.lowerBound
  obtain ⟨b, hb⟩ := hN.upperBound
  have hSP := isStrictlyPerfect_representedAffineAssociated_mapHomologicalComplex B S hS U N a b
    ha hb (fun j => (hN.finiteFree j).1)
    (fun j => have := (hN.finiteFree j).2; Module.Projective.of_free)
  let Φ₀ := representedAffineAssociated B S hS U
  let P := (Φ₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj N
  have hc := isIso_representedAffineDerivedAdjunction_counit_app B S hS U E hE
  let φ : (DerivedCategory.Q).obj P ⟶ E :=
    (Φ₀.mapDerivedCategoryFactors.app N).inv ≫ Φ₀.mapDerivedCategory.map α ≫
      (representedAffineDerivedAdjunction B S hS U).counit.app E
  have hL : Φ₀.IsLeftAdjoint := (representedAffineAssociatedAdjunction B S hS U).isLeftAdjoint
  have key : ∀ j : ℤ, (DerivedCategory.homologyFunctor _ j).map (Φ₀.mapDerivedCategory.map α) =
      ((Φ₀.mapDerivedCategoryHomologyIso j).app _).hom ≫
        Φ₀.map ((DerivedCategory.homologyFunctor _ j).map α) ≫
          ((Φ₀.mapDerivedCategoryHomologyIso j).app _).inv := fun j =>
    (NatIso.naturality_2 (Φ₀.mapDerivedCategoryHomologyIso j) α).symm
  have hφ : ∀ j : ℤ, (DerivedCategory.homologyFunctor _ j).map φ =
      (DerivedCategory.homologyFunctor _ j).map (Φ₀.mapDerivedCategoryFactors.app N).inv ≫
        (((Φ₀.mapDerivedCategoryHomologyIso j).app _).hom ≫
          Φ₀.map ((DerivedCategory.homologyFunctor _ j).map α) ≫
            ((Φ₀.mapDerivedCategoryHomologyIso j).app _).inv) ≫
          (DerivedCategory.homologyFunctor _ j).map
            ((representedAffineDerivedAdjunction B S hS U).counit.app E) := fun j => by
    simp only [φ, Functor.map_comp, key, Category.assoc]
  refine ⟨P, fun j => ?_, exists_isStrictlyGE_isStrictlyLE_of_isStrictlyPerfect B S hS U P hSP,
    φ, fun j hj => ?_, ?_⟩
  · obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free _ _).1
      (hSP.termDirectSummand j)
    let O₁ := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O)
    let eb : SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O)
        (ULift.{u} (Fin n)) ≅ ⨁ fun _ : Fin n => O₁ :=
      (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) => O₁)).symm ≪≫
        (biproduct.isoCoproduct _).symm
    exact ⟨n, i ≫ eb.hom, eb.inv ≫ r, by rw [Category.assoc, Iso.hom_inv_id_assoc, hir]⟩
  · have := hiso j hj
    rw [hφ j]
    infer_instance
  · have : Epi (Φ₀.map ((DerivedCategory.homologyFunctor _ m).map α)) := Functor.map_epi _ _
    rw [hφ m]
    infer_instance

end Affine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The sections over an affine chart of an object of `D_QCoh` with coherent cohomology.** Let
`X` be locally Noetherian, `E ∈ D_QCoh(𝒪_X)` with coherent cohomology in degrees `≥ m`, vanishing
in degrees `> b`, and `p : W ⟶ X` an affine étale chart, `W = Spec R`. Then `RΓ(W, Lp^*E)` is an
`m`-pseudo-coherent object of `D(R)`: its cohomology `Γ(W, Hⁱ(E))` is a finite `R`-module for
`i ≥ m` and vanishes for `i > b`, and `R` is Noetherian (Stacks 066E). -/
theorem isPseudoCoherentFrom_representedAffineDerivedSections_chart (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) E)
    (m : ℤ)
    (hcoh : ∀ i : ℤ, m ≤ i → IsCoherent B S hS X.1 X.2
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))
    (b : ℤ) (hb : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))
    (W : SmallEtale B S hS X.1) (hW : IsAffineChart B S hS X.1 W) :
    haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W)) :=
      hW
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj W)).obj
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X W)).obj E)) m := by
  have hWa : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W)) :=
    hW
  let U₀ := (SmallEtale.toOver B S hS X.1).obj W
  let p := chartToSpace B S hS X W
  have hp := isEtale_chartToSpace B S hS X W
  let L := smallEtaleDerivedModulePullback B S hS p
  have hLE := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ p E hE
  have hLE' : QcohDerived B S hS ⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩ (L.obj E) :=
    hLE
  have hnoeth : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤) := by
    have := isLocallyNoetherian_chart B S hS hN W
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  -- the cohomology of the restriction is the restriction of the cohomology
  let N' : ℤ → Modules.{u, u} B S hS (yoneda.obj U₀) (isAlgebraicSpace_yoneda B S hS U₀) :=
    fun i => (etaleModulePullback.{u, u} B S hS p hp).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E)
  let eH : ∀ i : ℤ, (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj U₀)
      (isAlgebraicSpace_yoneda B S hS U₀)) i).obj (L.obj E) ≅ N' i := fun i =>
    smallEtaleDerivedModulePullbackHomologyIsoOfIsEtale p hp E i ≪≫
      (modulePullbackIsoEtaleModulePullback B S hS p hp).app _
  let RΓ := representedAffineDerivedSections B S hS U₀
  have hfin : ∀ i : ℤ, m ≤ i → Module.Finite Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)) i).obj (RΓ.obj (L.obj E))) := by
    intro i hi
    let N := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS (yoneda.obj U₀)
      (isAlgebraicSpace_yoneda B S hS U₀)) i).obj (L.obj E)
    have hNq : N.IsQuasicoherentOnSite := hLE i
    have hTa : IsAffineChart B S hS (yoneda.obj U₀) (idEtaleChart B S hS U₀) := hWa
    have : Module.Finite (chartRing B S hS (yoneda.obj U₀) (isAlgebraicSpace_yoneda B S hS U₀)
        (idEtaleChart B S hS U₀)) ((N' i).val.obj (op (idEtaleChart B S hS U₀))) :=
      moduleFinite_sections_of_isCoherent B S hS X.1 X.2 _ (hcoh i hi) (V := W) hWa
    have hNT : Module.Finite (chartRing B S hS (yoneda.obj U₀) (isAlgebraicSpace_yoneda B S hS U₀)
        (idEtaleChart B S hS U₀)) (N.val.obj (op (idEtaleChart B S hS U₀))) :=
      Module.Finite.equiv (show (N' i).val.obj (op (idEtaleChart B S hS U₀)) ≃ₗ[chartRing B S hS
          (yoneda.obj U₀) (isAlgebraicSpace_yoneda B S hS U₀) (idEtaleChart B S hS U₀)]
          N.val.obj (op (idEtaleChart B S hS U₀)) from
        ((PresheafOfModules.evaluation _ (op (idEtaleChart B S hS U₀))).mapIso
          ((SheafOfModules.forget _).mapIso (eH i))).toLinearEquiv.symm)
    have := moduleFinite_representedAffineSections B S hS U₀ N hNq _
      (isTerminalIdEtaleChart B S hS U₀) hTa hNT
    exact Module.Finite.equiv
      (representedAffineDerivedSectionsHomologyIso B S hS U₀ (L.obj E) hLE' i).toLinearEquiv.symm
  have hzero : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)) i).obj (RΓ.obj (L.obj E))) := by
    intro i hi
    have := etaleModulePullback_additive.{u, u} B S hS p hp
    exact ((representedAffineSections B S hS U₀).map_isZero
      (((etaleModulePullback.{u, u} B S hS p hp).map_isZero (hb i hi)).of_iso (eH i))).of_iso
      (representedAffineDerivedSectionsHomologyIso B S hS U₀ (L.obj E) hLE' i)
  exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (RΓ.obj (L.obj E)) m Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤)).1.2
        ⟨⟨b, hzero⟩, hfin⟩

/-- **Stacks 08IK, (1) ⇒ (2)**, over a locally Noetherian algebraic space. Let `E` be an object of
`D_QCoh(𝒪_X)` whose cohomology sheaves are coherent in degrees `≥ m` and vanish in all
sufficiently large degrees. Then `E` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_isCoherent_homology_of_qcohDerived (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) E)
    (m : ℤ)
    (hcoh : ∀ i : ℤ, m ≤ i → IsCoherent B S hS X.1 X.2
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E)) :
    RingedSite.IsPseudoCoherentFrom (smallEtaleRingedSite B S hS X.1 X.2) E m := by
  obtain ⟨b, hb⟩ := hb
  refine isPseudoCoherentFrom_of_chart_approximation E m fun U =>
    ⟨fun W _ => IsAffineChart B S hS X.1 W, generate_isAffineChart_mem_topology B S hS X U,
      fun W g hW => ?_⟩
  have hWa : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W)) :=
    hW
  exact exists_approximation_of_isPseudoCoherentFrom_representedAffineDerivedSections B S hS _
    _ (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (chartToSpace B S hS X W) E hE) m
    (isPseudoCoherentFrom_representedAffineDerivedSections_chart X hN E hE m hcoh b hb W hW)

/-- **Stacks 08IK.** Let `S` be a scheme, `X` a Noetherian algebraic space over `S` and `E` an
object of `D_QCoh(𝒪_X)`. For `m ∈ ℤ` the following are equivalent:
1. `Hⁱ(E)` is coherent for `i ≥ m` and zero for `i ≫ 0`, and
2. `E` is `m`-pseudo-coherent. -/
@[stacks 08IK]
theorem isCoherent_homology_iff_isPseudoCoherentFrom (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZ X.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ) :
    ((∀ i : ℤ, m ≤ i → IsCoherent B S hS X.1 X.2
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E.obj)) ∧
      ∃ b : ℤ, ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E.obj)) ↔
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E.obj m :=
  ⟨fun h => isPseudoCoherentFrom_of_isCoherent_homology_of_qcohDerived X hX.2.2 E.obj
      E.property m h.1 h.2,
    fun h => ⟨fun i hi =>
      { toIsQuasicoherentOnSite := E.property i
        toIsCoherentOnSite := isCoherentOnSite_homology_of_isPseudoCoherentFrom_of_isNoetherian
          B S hS X.1 X.2 hZ hX E.obj m i h hi (E.property i) },
      exists_isZero_homology_of_isPseudoCoherentFrom B S hS X hX.1 E.obj m h⟩⟩

/-- **Stacks 08IK, the final statement.** Let `X` be a Noetherian algebraic space over `S`. An
object `E` of `D_QCoh(𝒪_X)` is pseudo-coherent if and only if it lies in `D⁻_Coh(𝒪_X)`: its
cohomology sheaves are coherent and vanish in all sufficiently large degrees. -/
@[stacks 08IK "pseudo-coherent objects of D_QCoh are those of D⁻_Coh"]
theorem isPseudoCoherent_iff_isCoherent_homology (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZ X.1)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E.obj ↔
      (∃ b : ℤ, ∀ i : ℤ, b < i →
          IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E.obj)) ∧
        ∀ i : ℤ, IsCoherent B S hS X.1 X.2
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E.obj) := by
  constructor
  · rintro ⟨K, hK, e⟩
    exact ⟨((isCoherent_homology_iff_isPseudoCoherentFrom hZ X hX E 0).2 ⟨K, hK 0, e⟩).2,
      fun i =>
        ((isCoherent_homology_iff_isPseudoCoherentFrom hZ X hX E i).2 ⟨K, hK i, e⟩).1 i le_rfl⟩
  · rintro ⟨hb, hcoh⟩
    have h : ∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E.obj n := fun n =>
      (isCoherent_homology_iff_isPseudoCoherentFrom hZ X hX E n).1 ⟨fun i _ => hcoh i, hb⟩
    obtain ⟨P, -, ⟨e⟩⟩ := h 0
    exact ⟨P, fun n => RingedSite.isPseudoCoherentComplexFrom_of_iso_general _ E.obj n (h n) P e,
      ⟨e⟩⟩

end AlgebraicGeometry.Space

end
