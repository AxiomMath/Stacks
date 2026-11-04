module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives

/-!
# Derived pullback of pseudo-coherent objects of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. The derived pullback
`Lf^*` carries `m`-pseudo-coherent objects of `D(𝒪_Y)` to
`m`-pseudo-coherent objects of `D(𝒪_X)`, hence pseudo-coherent objects to pseudo-coherent
objects. This is Stacks 08H4 read on the small étale ringed topoi of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_smallEtaleDerivedModulePullback_general` and
  `AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedModulePullback`: Stacks 08H4.

## Implementation notes

The `m`-pseudo-coherent form is named `…_general`: the base's
`AlgebraicGeometry.Space.isPseudoCoherentFrom_smallEtaleDerivedModulePullback` states it only for
objects of `D_QCoh`, while this one has no quasi-coherence hypothesis.

Pseudo-coherence is tested on the étale charts by
`AlgebraicGeometry.Space.isPseudoCoherentFrom_of_chart_approximation`, exactly as perfectness
is in `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback`: an approximation of
the restriction of `E` to a chart of `Y` by a bounded complex of retracts of finite free modules
pulls back along the morphism of chart spaces, because `Lf^*` computes the pullback of such a
complex degreewise and keeps the cone of the approximation bounded above.

## References

* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

variable (B S hS) in
/-- An object `K` of `D(𝒪_Y)` *has an approximation in degrees `> m`* by a strictly perfect
complex: a bounded complex `P` of retracts of finite free `𝒪_Y`-modules with a map
`P ⟶ K` inducing isomorphisms on cohomology in degrees `> m` and an epimorphism in degree
`m`. -/
def HasStrictlyPerfectApproximation {Y : AlgebraicSpaces B S hS}
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (m : ℤ) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) ℤ,
    (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))
      (P.X j)) ∧
    (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
    ∃ φ : (DerivedCategory.Q).obj P ⟶ K,
      (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map φ)) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map φ)

/-- Strictly perfect approximations are invariant under isomorphism. -/
theorem HasStrictlyPerfectApproximation.of_iso
    {K K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    {m : ℤ} (hK : HasStrictlyPerfectApproximation B S hS K m) (e : K ≅ K') :
    HasStrictlyPerfectApproximation B S hS K' m := by
  obtain ⟨P, hP, hb, φ, hiso, hepi⟩ := hK
  obtain ⟨hiso', hepi'⟩ :=
    Stacks.Cohomology.DerivedPullbackOnRingedTopoi.approximation_comp_iso φ e m hiso hepi
  exact ⟨P, hP, hb, φ ≫ e.hom, hiso', hepi'⟩

/-- A strictly perfect approximation is carried by every derived pullback to a strictly
perfect approximation. -/
theorem HasStrictlyPerfectApproximation.smallEtaleDerivedModulePullback_obj (f : X ⟶ Y)
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    {m : ℤ} (hK : HasStrictlyPerfectApproximation B S hS K m) :
    HasStrictlyPerfectApproximation B S hS
      ((smallEtaleDerivedModulePullback B S hS f).obj K) m := by
  obtain ⟨P, hP, ⟨a, b, ha, hb⟩, φ, hiso, hepi⟩ := hK
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f).toModulesHom
  let G : type_of% F := modulePullback B S hS f
  have : G.Additive := modulePullback_additive f
  obtain ⟨e'⟩ := nonempty_smallEtaleDerivedModulePullback_obj_Q_iso_modulePullback f P b
    (fun i ↦ isFlat_of_isRetractOfFiniteFree B S hS _ (hP i))
  obtain ⟨hiso₁, hepi₁⟩ := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.map_approximation_of_isLE
    (smallEtaleDerivedModulePullback B S hS f)
    (fun K n hK => isLE_smallEtaleDerivedModulePullback_obj f K n hK) φ m hiso hepi
  obtain ⟨hiso₂, hepi₂⟩ := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.iso_comp_approximation
    e'.symm _ m hiso₁ hepi₁
  exact ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    fun j ↦ IsRetractOfFiniteFree.map (F := modulePullback B S hS f)
      (modulePullbackUnitIso B S hS f) (hP j), ⟨a, b, inferInstance, inferInstance⟩,
    _, hiso₂, hepi₂⟩

/-- **Restriction of a strictly perfect approximation along a morphism of charts.** -/
theorem HasStrictlyPerfectApproximation.chartRestriction
    {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    {m : ℤ} {V V' : SmallEtale B S hS X.1} (k : V' ⟶ V)
    (hV : HasStrictlyPerfectApproximation B S hS
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) m) :
    HasStrictlyPerfectApproximation B S hS
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V')).obj E) m :=
  (hV.smallEtaleDerivedModulePullback_obj (chartMap B S hS X k)).of_iso
    ((smallEtaleDerivedModulePullbackCompIso B S hS (chartMap B S hS X k)
        (chartToSpace B S hS X V)).app E ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS
        (chartMap_comp_chartToSpace B S hS X k)).app E)

/-- A direct summand of a finite free module over a chart slice is a retract of a finite
biproduct of copies of the structure sheaf. -/
private theorem isRetractOfFiniteFree_unit_over_of_isDirectSummandOfFiniteFree
    {V : SmallEtale B S hS X.1} {M : SheafOfModules.{u} ((structureRingSheaf B S hS X).over V)}
    (hM : IsDirectSummandOfFiniteFree ((structureRingSheaf B S hS X).over V) M) :
    IsRetractOfFiniteFree (SheafOfModules.unit ((structureRingSheaf B S hS X).over V)) M := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free _ _).1 hM
  let O₁ := SheafOfModules.unit ((structureRingSheaf B S hS X).over V)
  let eb : SheafOfModules.free (R := (structureRingSheaf B S hS X).over V)
      (ULift.{u} (Fin n)) ≅ ⨁ fun _ : Fin n => O₁ :=
    (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) => O₁)).symm ≪≫
      (biproduct.isoCoproduct _).symm
  exact ⟨n, i ≫ eb.hom, eb.inv ≫ r, by simp [hir]⟩

/-- **An `m`-pseudo-coherent object has strictly perfect approximations on an étale covering of
every chart.** -/
theorem exists_hasStrictlyPerfectApproximation_chart_of_isPseudoCoherentFrom
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (m : ℤ)
    (hE : RingedSite.IsPseudoCoherentFrom (smallEtaleRingedSite B S hS X.1 X.2) E m)
    (U : SmallEtale B S hS X.1) :
    ∃ R : Presieve U, Sieve.generate R ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), R g →
        HasStrictlyPerfectApproximation B S hS
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) m := by
  obtain ⟨E', hE', ⟨eE⟩⟩ := hE
  obtain ⟨R, hR, hP⟩ := hE' U
  refine ⟨R, hR, fun V g hg ↦ ?_⟩
  obtain ⟨P, ⟨hbd, hterm⟩, α, hαi, hαe⟩ := hP g hg
  let E₀ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ := E'
  have eE₀ : (DerivedCategory.Q).obj E₀ ≅ E := eE
  let O := SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) V
  let P₀ : CochainComplex (SheafOfModules.{u} ((structureRingSheaf B S hS X).over V)) ℤ := P
  let α₀ : P₀ ⟶ (O.mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀ := α
  let Fr := chartModuleSliceReindex B S hS X V
  have : PreservesFiniteLimits Fr := inferInstance
  have : Fr.Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryProducts Fr
    Functor.additive_of_preservesBinaryBiproducts Fr
  have : PreservesFiniteColimits Fr := inferInstance
  have : Fr.PreservesHomology := Functor.preservesHomologyOfExact _
  let P' := (Fr.mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀
  obtain ⟨hi₁, he₁⟩ := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.approximation_Q_map
    ((Fr.mapHomologicalComplex (ComplexShape.up ℤ)).map α₀) m
    (fun j hj ↦ RingedSite.isIso_homologyMap_map Fr α₀ j (hαi j hj))
    (RingedSite.epi_homologyMap_map Fr α₀ m hαe)
  have e1 : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E ≅
      (DerivedCategory.Q).obj
        (((modulePullback B S hS (chartToSpace B S hS X V)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E₀) :=
    (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).mapIso eE₀.symm ≪≫
      smallEtaleDerivedModulePullbackObjQIsoOfIsEtale _ (isEtale_chartToSpace B S hS X V) E₀
  have e2 : ((modulePullback B S hS (chartToSpace B S hS X V)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E₀ ≅
      (Fr.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((O.mapHomologicalComplex (ComplexShape.up ℤ)).obj E₀) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (chartModuleRestrictionSliceIso B S hS X V).app (E₀.X i))
      (fun i j _ ↦ ((chartModuleRestrictionSliceIso B S hS X V).hom.naturality (E₀.d i j)).symm)
  obtain ⟨hi₂, he₂⟩ := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.approximation_comp_iso
    _ ((DerivedCategory.Q).mapIso e2.symm ≪≫ e1.symm) m hi₁ he₁
  refine ⟨P', fun j ↦ ?_, ?_, _, hi₂, he₂⟩
  · exact IsRetractOfFiniteFree.map (F := Fr)
      ((chartModuleRestrictionSliceIso B S hS X V).symm.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) ≪≫
        modulePullbackUnitIso B S hS (chartToSpace B S hS X V))
      (isRetractOfFiniteFree_unit_over_of_isDirectSummandOfFiniteFree (M := P₀.X j) (hterm j))
  · obtain ⟨b, hb⟩ := hbd.bddAbove
    obtain ⟨a, ha⟩ := hbd.bddBelow
    have hz : ∀ i, i < a ∨ b < i → IsZero (Fr.obj (P.X i)) := fun i hi ↦
      Fr.map_isZero (by_contra fun h ↦ by have := ha h; have := hb h; omega)
    exact ⟨a, b, (CochainComplex.isStrictlyGE_iff P' a).2 fun i hi ↦ hz i (.inl hi),
      (CochainComplex.isStrictlyLE_iff P' b).2 fun i hi ↦ hz i (.inr hi)⟩

/-- **Stacks 08H4 for algebraic spaces, `m`-pseudo-coherent form.** The derived pullback of an
`m`-pseudo-coherent object of `D(𝒪_Y)` along a morphism `f : X ⟶ Y` of algebraic spaces is
`m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_smallEtaleDerivedModulePullback_general (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) (m : ℤ)
    (hE : RingedSite.IsPseudoCoherentFrom (smallEtaleRingedSite B S hS Y.1 Y.2) E m) :
    RingedSite.IsPseudoCoherentFrom (smallEtaleRingedSite B S hS X.1 X.2)
      ((smallEtaleDerivedModulePullback B S hS f).obj E) m := by
  refine isPseudoCoherentFrom_of_chart_approximation _ m fun U => ?_
  let R : Presieve U := fun V _ => ∃ (W : SmallEtale B S hS Y.1) (q : V.1.left ⟶ W.1.left),
    yoneda.map q ≫ W.1.hom = V.1.hom ≫ f.hom ∧
      HasStrictlyPerfectApproximation B S hS
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS Y W)).obj E) m
  refine ⟨R, ?_, fun V g ⟨W, q, hq, hW⟩ => ?_⟩
  · rw [SmallEtale.mem_topology_iff_exists_mem_range]
    intro z
    obtain ⟨A₀, a₀, ha₀S, ha₀E⟩ := Y.2.exists_atlas
    let W₀ : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk a₀, ha₀E⟩
    obtain ⟨V₁, π₁, q₁, hq₁, z₁, hz₁⟩ := exists_chart_over B S hS f U W₀ ha₀S z
    obtain ⟨R₀, hR₀, hR₀mod⟩ := exists_hasStrictlyPerfectApproximation_chart_of_isPseudoCoherentFrom
      E m hE W₀
    obtain ⟨W', m₀, ⟨W'', m', m'', hm'', rfl⟩, w, hw⟩ :=
      (SmallEtale.mem_topology_iff_exists_mem_range B S hS Y.1 _).1 hR₀
        (((BigFppfOver.toScheme B S hS).map q₁) z₁)
    obtain ⟨T', π, p', hp', -, w', hw'₁, -⟩ :=
      exists_chart_pullback B S hS f V₁ q₁ hq₁ (m' ≫ m'') z₁ w hw.symm
    refine ⟨T', π ≫ π₁, Sieve.le_generate R _ _ (show R (π ≫ π₁) from ⟨W', p', hp',
      (hR₀mod m'' hm'').chartRestriction m'⟩), w', ?_⟩
    rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hw'₁, hz₁]
  · exact (hW.smallEtaleDerivedModulePullback_obj (chartSpaceHom q)).of_iso
      ((smallEtaleDerivedModulePullbackCompIso B S hS (chartSpaceHom q)
          (chartToSpace B S hS Y W)).app E ≪≫
        (smallEtaleDerivedModulePullbackCongr B S hS
          (chartSpaceHom_comp_chartToSpace f q hq)).app E ≪≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS (chartToSpace B S hS X V) f).app E).symm)

/-- **Stacks 08H4 for algebraic spaces.** The derived pullback of a pseudo-coherent object of
`D(𝒪_Y)` along a morphism `f : X ⟶ Y` of algebraic spaces is pseudo-coherent. -/
theorem isPseudoCoherent_smallEtaleDerivedModulePullback (f : X ⟶ Y)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS Y.1 Y.2) E) :
    RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2)
      ((smallEtaleDerivedModulePullback B S hS f).obj E) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  have h : ∀ m, RingedSite.IsPseudoCoherentFrom (smallEtaleRingedSite B S hS X.1 X.2)
      ((smallEtaleDerivedModulePullback B S hS f).obj E) m := fun m =>
    isPseudoCoherentFrom_smallEtaleDerivedModulePullback_general f E m ⟨K, hK m, ⟨e⟩⟩
  obtain ⟨P, _, ⟨e'⟩⟩ := h 0
  exact ⟨P, fun m => RingedSite.isPseudoCoherentComplexFrom_of_iso_general _ _ m (h m) P e',
    ⟨e'⟩⟩

end AlgebraicGeometry.Space

end
