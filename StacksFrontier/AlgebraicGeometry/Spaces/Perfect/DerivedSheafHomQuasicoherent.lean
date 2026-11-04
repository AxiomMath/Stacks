module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomChart
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomApproximation
import StacksCore.Tactic.StacksAttribute

/-!
# The derived internal Hom of an algebraic space preserves quasi-coherence

Let `X` be an algebraic space and `K`, `L` objects of `D(𝒪_X)`. Stacks 0A8A says that
`R𝓗om(K, L)` lies in `D_QCoh(𝒪_X)` if either `K` is perfect and `L` lies in `D_QCoh(𝒪_X)`, or
`K` is pseudo-coherent and `L` lies in `D^+_QCoh(𝒪_X)`.

For `K` perfect, `R𝓗om(K, L) ≅ K^∨ ⊗^L L` (Stacks 08JJ), the dual `K^∨` is perfect, perfect
objects lie in `D_QCoh`, and `D_QCoh` is closed under the derived tensor product (Stacks 08F5).

For `K` pseudo-coherent and `L` with no cohomology below `b`, fix a degree `n`. Pseudo-coherence
gives, on a family of étale charts covering `X`, a bounded complex `P` of retracts of finite free
modules with a map `P ⟶ K|_U` that is an isomorphism on cohomology above `m = b - n - 1` and
surjective in degree `m`. The derived internal Hom commutes with restriction to a chart, and the
map `R𝓗om(K|_U, L|_U) ⟶ R𝓗om(P, L|_U)` is an isomorphism on cohomology in degree `n`, so the
`n`-th cohomology sheaf of `R𝓗om(K, L)` restricted to `U` is that of `R𝓗om(P, L|_U)`, which is
quasi-coherent by the perfect case. Quasi-coherence is local (Stacks 03DN).

## Main results

* `AlgebraicGeometry.Space.HasStrictlyPerfectModel.isPerfect`: an object with a strictly perfect
  model is perfect.
* `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect`: the perfect case.
* `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedSheafHom_of_isPseudoCoherent`: the
  pseudo-coherent case.
* `AlgebraicGeometry.Space.qcohDerived_smallEtaleDerivedSheafHom`: **Stacks 0A8A**.

## References

* [Stacks Project, Tag 0A8A](https://stacks.math.columbia.edu/tag/0A8A)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A retract of a finite free `𝒪_Y`-module is a direct summand of a finite free module. -/
theorem isDirectSummandOfFiniteFree_of_isRetractOfFiniteFree {Y : AlgebraicSpaces B S hS}
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hM : IsRetractOfFiniteFree (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)) M) :
    IsDirectSummandOfFiniteFree (ringedToposStructureRingSheaf B S hS Y) M := by
  obtain ⟨n, i, r, hir⟩ := hM
  let O₁ := SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)
  let eb : SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS Y) (ULift.{u} (Fin n)) ≅
      ⨁ fun _ : Fin n => O₁ :=
    (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u} (Fin n) => O₁)).symm ≪≫
      (biproduct.isoCoproduct _).symm
  exact (isDirectSummandOfFiniteFree_iff_free _ _).2
    ⟨n, i ≫ eb.inv, eb.hom ≫ r, by simp [hir]⟩

/-- **An object of `D(𝒪_Y)` with a strictly perfect model is perfect.** -/
theorem HasStrictlyPerfectModel.isPerfect {Y : AlgebraicSpaces B S hS}
    {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hE : HasStrictlyPerfectModel B S hS E) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) E := by
  obtain ⟨P, hP, ⟨a, b, hGE, hLE⟩, ⟨e⟩⟩ := hE
  have hSP : IsStrictlyPerfect (ringedToposStructureRingSheaf B S hS Y) P := by
    refine ⟨(Set.finite_Icc a b).subset fun j hj => ?_, fun j =>
      isDirectSummandOfFiniteFree_of_isRetractOfFiniteFree _ (hP j)⟩
    simp only [Set.mem_setOf_eq] at hj
    simp only [Set.mem_Icc]
    by_contra hne
    apply hj
    rcases not_and_or.mp hne with h | h
    · exact P.isZero_of_isStrictlyGE a j (by omega)
    · exact P.isZero_of_isStrictlyLE b j (by omega)
  exact RingedSite.IsPerfect.of_iso _
    (RingedSite.isPerfect_Q_obj_of_isStrictlyPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) P hSP)
    e.symm

/-- **Stacks 0A8A, perfect case.** For `K` perfect and `L` in `D_QCoh(𝒪_X)`, `R𝓗om(K, L)` lies in
`D_QCoh(𝒪_X)`. -/
theorem qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect (X : AlgebraicSpaces B S hS)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) K)
    (hL : QcohDerived B S hS X L) :
    QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj L) :=
  (QcohDerived B S hS X).prop_of_iso (smallEtaleDerivedSheafHomIsoTensorDual B S hS X K L hK).symm
    (qcohDerived_smallEtaleDerivedTensor X _ L
      (qcohDerived_of_isPerfect_derivedCategoryB X _
        (isPerfect_smallEtaleDerivedDual B S hS X K hK)) hL)

/-- An exact equivalence detects the invertibility of the cohomology of a morphism. -/
theorem isIso_homologyFunctor_map_mapDerivedCategory_map_iff_of_equivalence
    {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂] (E : C₁ ≌ C₂) [E.functor.Additive]
    {K L : DerivedCategory C₁} (φ : K ⟶ L) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C₂ n).map (E.functor.mapDerivedCategory.map φ)) ↔
      IsIso ((DerivedCategory.homologyFunctor C₁ n).map φ) := by
  rw [Functor.isIso_homologyFunctor_map_mapDerivedCategory_map_iff]
  exact ⟨fun _ => isIso_of_reflects_iso _ E.functor, fun _ => inferInstance⟩

/-- An exact equivalence carries a morphism surjective on cohomology in degree `n` to one. -/
theorem epi_homologyFunctor_map_mapDerivedCategory_map_of_equivalence
    {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂] (E : C₁ ≌ C₂) [E.functor.Additive]
    {K L : DerivedCategory C₁} (φ : K ⟶ L) (n : ℤ)
    (h : Epi ((DerivedCategory.homologyFunctor C₁ n).map φ)) :
    Epi ((DerivedCategory.homologyFunctor C₂ n).map (E.functor.mapDerivedCategory.map φ)) := by
  refine (epi_comp_iff_of_isIso _
    ((E.functor.mapDerivedCategoryHomologyIso n).hom.app L)).1 ?_
  rw [← Functor.comp_map, (E.functor.mapDerivedCategoryHomologyIso n).hom.naturality φ]
  exact epi_comp' inferInstance (E.functor.map_epi _)

/-- An object whose cohomology is the image of that of an object with no cohomology below `b`
under a functor preserving zero objects has no cohomology below `b`. -/
private theorem isGE_of_iso_map_homology {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    [Abelian C₁] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂] (F : C₁ ⥤ C₂)
    [F.PreservesZeroMorphisms] {L : DerivedCategory C₁} {L' : DerivedCategory C₂} {b : ℤ}
    (hL : ∀ i < b, IsZero ((DerivedCategory.homologyFunctor C₁ i).obj L))
    (e : ∀ i, (DerivedCategory.homologyFunctor C₂ i).obj L' ≅
      F.obj ((DerivedCategory.homologyFunctor C₁ i).obj L)) : L'.IsGE b :=
  (DerivedCategory.isGE_iff _ b).2 fun i hi =>
    (F.map_isZero (hL i hi)).of_iso (e i)

/-- An exact equivalence carries an object with no cohomology below `b` to one. -/
theorem isGE_mapDerivedCategory_obj_of_equivalence
    {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂] (E : C₁ ≌ C₂) [E.functor.Additive]
    (L : DerivedCategory C₁) (b : ℤ) (hL : L.IsGE b) :
    (E.functor.mapDerivedCategory.obj L).IsGE b :=
  isGE_of_iso_map_homology E.functor ((DerivedCategory.isGE_iff _ b).1 hL) fun i =>
    (E.functor.mapDerivedCategoryHomologyIso i).app L

/-- **The derived internal Hom of an algebraic space out of an approximation.** If `α : P ⟶ M`
is an isomorphism on cohomology in degrees `> m` and surjective in degree `m`, and `L` has no
cohomology below `b`, then `R𝓗om(M, L) ⟶ R𝓗om(P, L)` is an isomorphism on cohomology in every
degree `n < b - m`. -/
theorem isIso_homologyMap_smallEtaleDerivedSheafHom_map_of_approximation
    (Y : AlgebraicSpaces B S hS)
    {P M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (α : P ⟶ M) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor _ m).map α))
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (b n : ℤ) (hL : L.IsGE b) (hn : n < b - m) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      (((smallEtaleDerivedSheafHom B S hS Y).map α.op).app L)) := by
  let E := smallEtaleModelModulesEquivalence B S hS Y
  have h : ((smallEtaleDerivedSheafHom B S hS Y).map α.op).app L =
      E.inverse.mapDerivedCategory.map
        (((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS Y.1 Y.2)).map
          (E.functor.mapDerivedCategory.map α).op).app (E.functor.mapDerivedCategory.obj L)) :=
    rfl
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : E.symm.functor.Additive := ‹E.inverse.Additive›
  rw [h]
  exact (isIso_homologyFunctor_map_mapDerivedCategory_map_iff_of_equivalence E.symm _ n).2
    (RingedSite.isIso_homologyMap_derivedSheafHom_map_of_approximation _ _ m
      (fun i hi =>
        (isIso_homologyFunctor_map_mapDerivedCategory_map_iff_of_equivalence E α i).2 (hiso i hi))
      (epi_homologyFunctor_map_mapDerivedCategory_map_of_equivalence E α m hepi) _ b n
      (isGE_mapDerivedCategory_obj_of_equivalence E L b hL) hn)

/-- **Stacks 0A8A, pseudo-coherent case.** For `K` pseudo-coherent and `L` in
`D^+_QCoh(𝒪_X)`, `R𝓗om(K, L)` lies in `D_QCoh(𝒪_X)`. -/
theorem qcohDerived_smallEtaleDerivedSheafHom_of_isPseudoCoherent (X : AlgebraicSpaces B S hS)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) K)
    (hL : DerivedCategoryB.derivedCategoryBPlus
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) L) :
    QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj L) := by
  intro n
  obtain ⟨⟨b, hb⟩, hLq⟩ := hL
  have hKm : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom K (b - n - 1) := by
    obtain ⟨E, hE, e⟩ := hK
    exact ⟨E, hE (b - n - 1), e⟩
  choose R hR hdata using exists_chart_approximation_of_isPseudoCoherentFrom B S hS K _ hKm
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite
    _).2 ⟨Σ W : SmallEtale B S hS X.1, Σ V : SmallEtale B S hS X.1, {g : V ⟶ W // R W g},
      fun k => k.2.1, fun W => ?_, fun k => ?_⟩
  · refine (SmallEtale.topology B S hS X.1).superset_covering ?_ (hR W)
    rintro Z g ⟨V, a, f, hf, rfl⟩
    exact ⟨⟨W, V, f, hf⟩, ⟨a⟩⟩
  obtain ⟨P, hP, hbd, φ, hφi, hφe⟩ := hdata k.1 k.2.2.1 k.2.2.2
  let hom : ∀ (j : ℤ) (Z : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS X))),
      (DerivedCategory.homologyFunctor _ j).obj
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X k.2.1)).obj Z) ≅
        (chartModules B S hS X k.2.1).obj ((DerivedCategory.homologyFunctor _ j).obj Z) :=
    fun j Z => (DerivedCategory.homologyFunctor _ j).mapIso
        ((smallEtaleDerivedModulePullbackIsoEtale B S hS (chartToSpace B S hS X k.2.1)
          (isEtale_chartToSpace B S hS X k.2.1)).app Z) ≪≫
      ((chartModules B S hS X k.2.1).mapDerivedCategoryHomologyIso j).app Z
  have hL' : ((smallEtaleDerivedModulePullback B S hS
      (chartToSpace B S hS X k.2.1)).obj L).IsGE b :=
    isGE_of_iso_map_homology (chartModules B S hS X k.2.1) hb fun i => hom i L
  have hiso := isIso_homologyMap_smallEtaleDerivedSheafHom_map_of_approximation
    (chartSpace B S hS X k.2.1) φ (b - n - 1) hφi hφe
    ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X k.2.1)).obj L) b n hL'
    (by omega)
  have hQ := qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect (chartSpace B S hS X k.2.1) _
    ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X k.2.1)).obj L)
    (HasStrictlyPerfectModel.isPerfect ⟨P, hP, hbd, ⟨Iso.refl _⟩⟩)
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _
      (chartToSpace B S hS X k.2.1) L hLq) n
  refine (isQuasicoherentOnSite_etaleModulePullback_chartToSpace_iff B S hS X _ k.2.1).1 ?_
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso ?_ hQ
  exact (asIso ((DerivedCategory.homologyFunctor _ n).map
      (((smallEtaleDerivedSheafHom B S hS (chartSpace B S hS X k.2.1)).map φ.op).app
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X k.2.1)).obj L)))).symm ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso
      (smallEtaleDerivedSheafHomChartIso B S hS X k.2.1 K L).symm ≪≫ hom n _

/-- **Stacks 0A8A.** Let `X` be an algebraic space and `K`, `L` objects of `D(𝒪_X)`. If either
`L` lies in `D^+_QCoh(𝒪_X)` and `K` is pseudo-coherent, or `L` lies in `D_QCoh(𝒪_X)` and `K` is
perfect, then `R𝓗om(K, L)` lies in `D_QCoh(𝒪_X)`. -/
@[stacks 0A8A]
theorem qcohDerived_smallEtaleDerivedSheafHom (X : AlgebraicSpaces B S hS)
    (K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (h : (RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) K ∧
        DerivedCategoryB.derivedCategoryBPlus
          (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) L) ∨
      (RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) K ∧ QcohDerived B S hS X L)) :
    QcohDerived B S hS X (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj L) := by
  rcases h with ⟨hK, hL⟩ | ⟨hK, hL⟩
  · exact qcohDerived_smallEtaleDerivedSheafHom_of_isPseudoCoherent X K L hK hL
  · exact qcohDerived_smallEtaleDerivedSheafHom_of_isPerfect X K L hK hL

end AlgebraicGeometry.Space
