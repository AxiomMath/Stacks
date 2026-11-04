module

public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# Quasi-coherence on an algebraic space is tested on its étale charts

Stacks 03M0 characterizes the quasi-coherent `𝒪_X`-modules on an algebraic space `X` by four
equivalent conditions.  This file proves the equivalence of its conditions (1), (3) and (4): a
sheaf of `𝒪_X`-modules on the small étale site of `X` is quasi-coherent exactly when its
restriction along *one* surjective étale morphism from a scheme is quasi-coherent, and exactly
when its restriction along *every* étale morphism from an affine scheme is quasi-coherent.

The mathematical content is two geometric facts about the small étale site: a surjective étale
chart covers the final object, and so does the family of affine étale charts, both in the sense
of `GrothendieckTopology.CoversTop`.  Once those are available, the equivalences are the clause
of Stacks 03DN for quasi-coherence
(`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite`) applied
to those covering families, together with stability of quasi-coherence under restriction
(`Stacks.SheafOfModules.isQuasicoherent_over`).

## Main results

* `AlgebraicGeometry.BigFppfSite.presieve₀_mem_etalePrecoverage` and
  `AlgebraicGeometry.BigFppfSite.singleton_mem_etalePrecoverage`: an étale covering family of
  `Sch_κ`, in particular a one-element family consisting of a surjective étale morphism,
  generates a presieve of the chosen étale precoverage.
* `AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`: an étale chart of an
  algebraic space whose structure morphism is surjective on points covers the final object of
  the small étale site.
* `AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`: the étale charts whose
  underlying scheme is affine cover the final object of the small étale site.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_over_of_isSurjective`: **Stacks 03M0,
  conditions (1) and (3)**.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_affine_over`: **Stacks 03M0,
  conditions (1) and (4)**.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_over`: quasi-coherence is tested on
  every étale chart at once; this needs no geometry, since the family of all objects of a site
  covers the final object.

## Implementation notes

The restriction of a module along an étale chart `φ : U → X` is here the restriction
`SheafOfModules.over` to the slice of `X_étale` at the chart, not the pullback `φ^*` along the
morphism of small étale ringed topoi.  That is the identification which Stacks 03M0 invokes as
the abuse of notation of its Equation 03LW: the slice of `X_étale` at `φ` is the small étale
site of `U`, which in this development is
`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart` (Stacks 04M0).  Transporting
quasi-coherence across that equivalence of *sites* additionally requires matching the two
structure sheaves, which is not done here.

Condition (2) of Stacks 03M0, about an étale morphism `f : Y ⟶ X` of algebraic spaces, is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback_iff` in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism`.  It needs no comparison of
two constructions of a pullback of modules: `AlgebraicGeometry.Space.etaleModulePullback` is
restriction along `AlgebraicGeometry.Space.smallEtalePostcomp` with no change of scalars, so
the two structure sheaves on a slice of the small étale site agree on the nose, and the
geometric input is instead the slice form of Stacks 04M0 proved in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice`.

The first covering fact is proved by base change.  For an étale chart `W` of `X`, the fibre
product `U ×_X W` is representable because the structure morphism of `U` is relatively
representable — that is part of being an étale chart — and
`CategoryTheory.Functor.relativelyRepresentable` supplies it together with the two projections.
The projection to `W` is surjective and étale because those two properties of the structure
morphism of `U` are asserted for *every* represented base change, so the fibre product is an
étale chart of `X` admitting a morphism to `U`, and its one-element family covers `W`.  The
second is Zariski-local: the affine opens of the scheme underlying `W` cover it, and each of
them is an affine étale chart of `X` over `W` by `AlgebraicGeometry.Space.openChart`.

In both cases being a covering family of charts is being a *chosen* étale covering family of
the underlying schemes (`AlgebraicGeometry.Space.SmallEtale.precoverage_eq_comap`), so the index
bound of the big fppf site intervenes; `AlgebraicGeometry.Space.exists_chosen_etaleCovering`
replaces the family by a combinatorially equivalent chosen one, which generates the same
presieve.  That is `AlgebraicGeometry.BigFppfSite.presieve₀_mem_etalePrecoverage`.

The module universe is the universe `u` of the schemes, as in
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite`, whose
statement takes the module sections in the universe of the coefficient rings.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The presieve generated by an étale covering family of `Sch_κ` belongs to the chosen étale
precoverage of a big fppf site.

An étale covering family need not be one of the *chosen* families, whose index types the big
fppf site bounds; `AlgebraicGeometry.Space.exists_chosen_etaleCovering` replaces it by a
combinatorially equivalent chosen one, and combinatorially equivalent families generate the
same presieve. -/
theorem BigFppfSite.presieve₀_mem_etalePrecoverage (B : BigFppfSite.{u}) {X : B.Schemes}
    (E : PreZeroHypercover.{u + 1} X) (hE : IsEtaleCovering (⟨X, E⟩ : Covering B.Schemes)) :
    E.presieve₀ ∈ B.etalePrecoverage X := by
  obtain ⟨E', hE', hX, hcomb⟩ := Space.exists_chosen_etaleCovering B _ hE
  cases hX
  exact ⟨E'.2, PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb, hE'⟩

/-- A one-element family consisting of a surjective étale morphism of `Sch_κ` belongs to the
chosen étale precoverage of a big fppf site. -/
theorem BigFppfSite.singleton_mem_etalePrecoverage
    (B : BigFppfSite.{u}) {X Y : B.Schemes} (g : Y ⟶ X)
    (hs : Surjective (B.inclusion.map g)) (he : Etale (B.inclusion.map g)) :
    Presieve.singleton g ∈ B.etalePrecoverage X := by
  have hEt : IsEtaleCovering (⟨X, PreZeroHypercover.singleton g⟩ : Covering B.Schemes) := by
    change ((PreZeroHypercover.singleton g).map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj X)
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_singleton,
      Presieve.map_singleton]
    exact (Scheme.singleton_mem_precoverage_iff (@Etale.{u} : MorphismProperty Scheme.{u})
      (B.inclusion.map g)).2 ⟨hs.surj, he⟩
  rw [← PreZeroHypercover.presieve₀_singleton g]
  exact B.presieve₀_mem_etalePrecoverage _ hEt

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A presieve in the chosen étale precoverage of `W`, all of whose members factor through some
member of a family of charts, makes that family cover `W`. -/
private theorem ofObjects_mem_topology_of_mem_precoverage {ι : Type*}
    (Y : ι → SmallEtale B S hS F) {W : SmallEtale B S hS F} (R : Presieve W)
    (hR : R ∈ SmallEtale.precoverage B S hS F W)
    (h : ∀ ⦃Z⦄ (f : Z ⟶ W), R f → ∃ i, Nonempty (Z ⟶ Y i)) :
    Sieve.ofObjects Y W ∈ SmallEtale.topology B S hS F W := by
  refine (SmallEtale.topology B S hS F).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck hR)
  rintro Z f ⟨T, h', k, hk, rfl⟩
  obtain ⟨i, ⟨g⟩⟩ := h k hk
  exact ⟨i, ⟨h' ≫ g⟩⟩

/-- An étale chart of an algebraic space whose structure morphism is surjective on points
covers the final object of the small étale site: every étale chart `W` is covered by the
one-element family consisting of the fibre product of `W` with the given chart, which maps to
the given chart.

This is the geometric input of the equivalence of conditions (1) and (3) of Stacks 03M0. -/
theorem SmallEtale.coversTop_of_isSurjective (hF : IsAlgebraicSpace B S hS F)
    (U : SmallEtale B S hS F) (hsurj : IsSurjective B S hS U.1.hom) :
    (SmallEtale.topology B S hS F).CoversTop (fun _ : PUnit.{u + 2} => U) := by
  have hsurjP := (presheafSurjective_iff_isSurjective_yoneda B S hS F hF
    U.1.left U.1.hom).2 hsurj
  intro W
  have hrep : yoneda.relativelyRepresentable U.1.hom := U.property.rep
  set g := W.1.hom
  -- The fibre product `U ×_F W`, with its two projections.
  set V := hrep.pullback g
  set q : V ⟶ W.1.left := hrep.snd g
  set p : V ⟶ U.1.left := hrep.fst' g with hp
  have hw : yoneda.map p ≫ U.1.hom = yoneda.map q ≫ g := by
    rw [hp, Functor.relativelyRepresentable.map_fst']
    exact hrep.w g
  have hqEtale : Etale ((BigFppfOver.toScheme B S hS).map q) :=
    U.property.property g (hrep.fst g) (hrep.snd g) (hrep.isPullback g)
  have hqSurj : Surjective ((BigFppfOver.toScheme B S hS).map q) :=
    hsurjP.property g (hrep.fst g) (hrep.snd g) (hrep.isPullback g)
  -- The fibre product is an étale chart of `F`, over `W` and over `U`.
  set Vc : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (yoneda.map q ≫ W.1.hom),
      etale_comp_of_scheme B S hS q W.1.hom hqEtale W.property⟩
  set a : Vc ⟶ W := ObjectProperty.homMk (CostructuredArrow.homMk q rfl)
  set b : Vc ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk p hw)
  have hpre : Presieve.singleton a ∈ SmallEtale.precoverage B S hS F W := by
    rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_singleton]
    exact B.singleton_mem_etalePrecoverage _ hqSurj hqEtale
  refine ofObjects_mem_topology_of_mem_precoverage B S hS F _ _ hpre ?_
  rintro Z _ ⟨⟩
  exact ⟨PUnit.unit, ⟨b⟩⟩

/-- The étale charts of an algebraic space whose underlying scheme is affine cover the final
object of the small étale site: every étale chart `W` is covered by the affine opens of its
underlying scheme, each of which is an affine étale chart over `W`.

This is the geometric input of the equivalence of conditions (1) and (4) of Stacks 03M0. -/
theorem SmallEtale.coversTop_affineCharts :
    (SmallEtale.topology B S hS F).CoversTop
      (fun U : {U : SmallEtale B S hS F //
          IsAffine ((BigFppfOver.toScheme B S hS).obj
            ((SmallEtale.toOver B S hS F).obj U))} => U.1) := by
  intro W
  set E : PreZeroHypercover.{u + 1} W :=
    { I₀ := ULift.{u + 1}
        ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W)).affineOpens
      X := fun O => openChart B S hS F W O.down.1
      f := fun O => openChartInclusion B S hS F W O.down.1 }
  have hcov : IsEtaleCovering
      (⟨(SmallEtale.toSchemes B S hS F).obj W, E.map (SmallEtale.toSchemes B S hS F)⟩ :
        Covering B.Schemes) := by
    refine (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
      ((E.map (SmallEtale.toSchemes B S hS F)).map B.inclusion)).2 ⟨?_, ?_⟩
    · intro x
      have hx : x ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS F).obj W)).Opens) := trivial
      rw [← iSup_affineOpens_eq_top] at hx
      obtain ⟨O, hO⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      refine ⟨ULift.up O, ?_⟩
      have heq := toScheme_map_toOver_map_openChartInclusion B S hS F W (O : _)
      obtain ⟨y, hy⟩ := (Scheme.Opens.range_ι (X := (BigFppfOver.toScheme B S hS).obj
        ((SmallEtale.toOver B S hS F).obj W)) (O : _)).ge hO
      refine ⟨y, ?_⟩
      change ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
        (openChartInclusion B S hS F W (O : _)))) y = x
      rw [heq]
      exact hy
    · intro O
      exact etale_toScheme_toOver_map B S hS F (openChartInclusion B S hS F W O.down.1)
  have hpre : E.presieve₀ ∈ SmallEtale.precoverage B S hS F W := by
    rw [SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff,
      ← PreZeroHypercover.presieve₀_map]
    exact B.presieve₀_mem_etalePrecoverage _ hcov
  refine ofObjects_mem_topology_of_mem_precoverage B S hS F _ _ hpre ?_
  rintro Z _ ⟨O⟩
  exact ⟨⟨E.X O, inferInstanceAs (IsAffine (O.down : _))⟩, ⟨𝟙 _⟩⟩

variable (hF : IsAlgebraicSpace B S hS F)

/-- A sheaf of modules is quasi-coherent if its restrictions to a family of charts covering the
final object are. -/
private theorem isQuasicoherentOnSite_of_coversTop (M : Modules.{u, u} B S hS F hF)
    {ι : Type (u + 1)} (Y : ι → (smallEtaleRingedSite B S hS F hF).C)
    (hY : (SmallEtale.topology B S hS F).CoversTop Y)
    (h : ∀ i, (M.over (Y i)).IsQuasicoherentOnSite) : M.IsQuasicoherentOnSite :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite
    M).2 ⟨ι, Y, hY, h⟩

/-- **Stacks 03M0, conditions (1) and (3).** A sheaf of `𝒪_F`-modules on the small étale site
of an algebraic space `F` is quasi-coherent if and only if its restriction along one étale
chart whose structure morphism is surjective on points is quasi-coherent.

The restriction is restriction to the slice of the small étale site at the chart; see the
implementation notes. -/
@[stacks 03M0 "(1) iff (3)"]
theorem isQuasicoherentOnSite_iff_over_of_isSurjective (M : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hsurj : IsSurjective B S hS U.1.hom) :
    M.IsQuasicoherentOnSite ↔ (M.over U).IsQuasicoherentOnSite := by
  exact ⟨fun hM => Stacks.SheafOfModules.isQuasicoherent_over M hM U, fun h =>
    isQuasicoherentOnSite_of_coversTop B S hS F hF M (fun _ : PUnit.{u + 2} => U)
      (SmallEtale.coversTop_of_isSurjective B S hS F hF U hsurj) fun _ => h⟩

/-- **Stacks 03M0, conditions (1) and (4).** A sheaf of `𝒪_F`-modules on the small étale site
of an algebraic space `F` is quasi-coherent if and only if its restriction along every étale
chart whose underlying scheme is affine is quasi-coherent.

The restriction is restriction to the slice of the small étale site at the chart; see the
implementation notes. -/
@[stacks 03M0 "(1) iff (4)"]
theorem isQuasicoherentOnSite_iff_forall_affine_over (M : Modules.{u, u} B S hS F hF) :
    M.IsQuasicoherentOnSite ↔
      ∀ U : (smallEtaleRingedSite B S hS F hF).C,
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) →
        (M.over U).IsQuasicoherentOnSite := by
  exact ⟨fun hM U _ => Stacks.SheafOfModules.isQuasicoherent_over M hM U, fun h =>
    isQuasicoherentOnSite_of_coversTop B S hS F hF M _
      (SmallEtale.coversTop_affineCharts B S hS F) fun U => h U.1 U.2⟩

/-- A sheaf of `𝒪_F`-modules on the small étale site of an algebraic space `F` is
quasi-coherent if and only if its restriction to every étale chart is quasi-coherent.

Unlike `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_over_of_isSurjective` this needs no
geometry: the family of all objects of a site covers the final object. -/
theorem isQuasicoherentOnSite_iff_forall_over (M : Modules.{u, u} B S hS F hF) :
    M.IsQuasicoherentOnSite ↔
      ∀ U : (smallEtaleRingedSite B S hS F hF).C, (M.over U).IsQuasicoherentOnSite := by
  refine ⟨fun hM U => Stacks.SheafOfModules.isQuasicoherent_over M hM U, fun h => ?_⟩
  refine isQuasicoherentOnSite_of_coversTop B S hS F hF M (fun U => U) (fun W => ?_) h
  refine (smallEtaleRingedSite B S hS F hF).J.superset_covering ?_
    ((smallEtaleRingedSite B S hS F hF).J.top_mem W)
  exact fun V f _ => ⟨V, ⟨𝟙 V⟩⟩

end Space

end AlgebraicGeometry

end
