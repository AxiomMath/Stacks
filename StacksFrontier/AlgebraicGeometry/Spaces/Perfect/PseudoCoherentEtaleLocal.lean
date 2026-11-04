module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartPointLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart

/-!
# `m`-pseudo-coherence is étale local

Let `E` be an object of `D(𝒪_X)` for an algebraic space `X`. If the derived pullbacks of `E`
along a family of étale morphisms `fᵢ : Yᵢ ⟶ X` whose images cover `|X|` are
`m`-pseudo-coherent, then so is `E`. In particular `m`-pseudo-coherence can be checked on the
affine étale charts of `X`.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_forall_etale`
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_forall_isAffineChart`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **`m`-pseudo-coherence is local along a jointly surjective family of étale morphisms**: if
the derived pullbacks of `E` along étale morphisms `fᵢ : Yᵢ ⟶ X` whose images cover `|X|` are
`m`-pseudo-coherent, then `E` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_forall_etale {ι : Type*} (Y : ι → AlgebraicSpaces B S hS)
    (f : ∀ i, Y i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, ∃ y : points B S hS (Y i).1,
      pointsMap B S hS _ (f i).hom y = x)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (m : ℤ)
    (hE : ∀ i, (smallEtaleRingedSite B S hS (Y i).1 (Y i).2).IsPseudoCoherentFrom
      ((smallEtaleDerivedModulePullback B S hS (f i)).obj E) m) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m := by
  refine isPseudoCoherentFrom_of_chart_approximation _ m fun U => ?_
  let R : Presieve U := fun V _ => ∃ P : CochainComplex (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) ℤ,
    (∀ j, IsRetractOfFiniteFree (SheafOfModules.unit
      (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X V))) (P.X j)) ∧
    (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
    ∃ φ : (DerivedCategory.Q).obj P ⟶
        (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E,
      (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map φ)) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map φ)
  refine ⟨R, ?_, fun V g hg => hg⟩
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro z
  obtain ⟨u, rfl⟩ := surjective_pointsToScheme B S hS U.1.left z
  obtain ⟨i, y, hy⟩ := hsurj (pointsMap B S hS _ U.1.hom u)
  obtain ⟨V, p, hp, w, hw⟩ := exists_chart_lift_of_isEtale B S hS (f i) (hf i) U u y hy.symm
  obtain ⟨R₀, hR₀, hR₀mod⟩ := exists_chart_approximation_of_isPseudoCoherentFrom B S hS _ m (hE i) V
  obtain ⟨W', m₁, ⟨W'', m', m'', hm'', rfl⟩, w', hw'⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS (Y i).1 _).1 hR₀ w
  let Wx : SmallEtale B S hS X.1 := (smallEtalePostcomp B S hS (f i) (hf i)).obj W''
  have hm''w : yoneda.map ((SmallEtale.toOver B S hS (Y i).1).map m'') ≫ V.1.hom = W''.1.hom :=
    CostructuredArrow.w m''.hom
  let gx : Wx ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk
    ((SmallEtale.toOver B S hS (Y i).1).map m'' ≫ p) (by
      show yoneda.map (_ ≫ p) ≫ U.1.hom = W''.1.hom ≫ (f i).hom
      rw [Functor.map_comp, Category.assoc, hp, ← Category.assoc, hm''w]))
  have hc : chartToSpace B S hS (Y i) W'' ≫ f i = chartToSpace B S hS X Wx := rfl
  refine ⟨Wx, gx, Sieve.le_generate R _ _ ?_, ?_⟩
  · obtain ⟨P, hP, hb, φ, hiso, hepi⟩ := hR₀mod m'' hm''
    let e := (smallEtaleDerivedModulePullbackCompIso B S hS (chartToSpace B S hS (Y i) W'')
        (f i)).app E ≪≫ (smallEtaleDerivedModulePullbackCongr B S hS hc).app E
    exact ⟨P, hP, hb, φ ≫ e.hom, DerivedCategory.ApproximatesFrom.comp_iso φ e m ⟨hiso, hepi⟩⟩
  · refine ⟨(BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (Y i).1).map m') w',
      ?_⟩
    show (BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS (Y i).1).map m'' ≫ p) _ = _
    rw [← hw, ← hw', Functor.map_comp, Functor.map_comp, Functor.map_comp,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]

/-- **`m`-pseudo-coherence is local on the affine étale charts.** If the derived pullback of `E`
to every affine étale chart of `X` is `m`-pseudo-coherent, then `E` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_forall_isAffineChart
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (m : ℤ)
    (h : ∀ V : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 V →
      (smallEtaleRingedSite B S hS (chartSpace B S hS X V).1
        (chartSpace B S hS X V).2).IsPseudoCoherentFrom
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V)).obj E) m) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E m :=
  isPseudoCoherentFrom_of_forall_etale
    (fun V : {V : SmallEtale B S hS X.1 // IsAffineChart B S hS X.1 V} => chartSpace B S hS X V.1)
    (fun V => chartToSpace B S hS X V.1) (fun V => isEtale_chartToSpace B S hS X V.1)
    (fun x => SmallEtale.exists_mem_range_of_coversTop B S hS X.2
      (SmallEtale.coversTop_affineCharts B S hS X.1) x) E m fun V => h V.1 V.2

end AlgebraicGeometry.Space

end
