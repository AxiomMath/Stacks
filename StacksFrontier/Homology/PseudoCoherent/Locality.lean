module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.RingTheory.LocalProperties.StandardCover

@[expose] public section

/-!
# Derived localization away from an element, and its effect on pseudo-coherence

Let `R` be a commutative ring and let `f : R` be an element. Localization
`R → Localization.Away f` is flat, so termwise extension of scalars along it is exact and descends
to a functor `D(R) ⥤ D(R_f)` on derived categories: this is `localizationAwayFunctorAux`. This
module constructs that functor, equips it with the shift comparison and the triangulated structure
that exactness provides, and identifies its effect on cohomology: the `n`-th cohomology of the
localization is the localization of the `n`-th cohomology.

The remainder of the module proves that pseudo-coherence is local on a finite principal open cover:
if the elements `f i` generate the unit ideal and an object of `D(R)` becomes (`m`-)pseudo-coherent
after localization at every `f i`, then it is (`m`-)pseudo-coherent.

## Main definitions

* `StacksDraft.PseudoCoherence.localizationAwayFunctorAux`: derived extension of scalars from `R`
  to `Localization.Away f`.
* `StacksDraft.PseudoCoherence.localizationAwayCommShift`,
  `StacksDraft.PseudoCoherence.localizationAway_isTriangulated`: the shift comparison and the
  triangulated structure carried by that functor.
* `StacksDraft.PseudoCoherence.localizationAwayHomologyIso`: the identification
  `Hⁿ(K ⊗_R R_f) ≅ (Hⁿ K)_f`.
* `StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso`: an exact functor
  commutes with the cohomology functors of the derived category.

## Main results

* `StacksDraft.PseudoCoherence.isPseudoCoherentFrom_and_isPseudoCoherent_of_localizationAux`: both
  `m`-pseudo-coherence and pseudo-coherence descend along a finite principal open cover.
* `StacksDraft.PseudoCoherence.isPseudoCoherentFrom_of_localization`: the `m`-pseudo-coherent half,
  stated on its own.
* `StacksDraft.PseudoCoherence.isPseudoCoherentFrom_of_finite_top_homology`: an object whose
  cohomology vanishes above `m` and is finite in degree `m` is `m`-pseudo-coherent.
* `StacksDraft.PseudoCoherence.localizationAway_homology_isZero`: derived localization kills a
  vanishing cohomology module.
* `StacksDraft.PseudoCoherence.extendScalars_isBoundedFiniteFree`: extension of scalars preserves
  bounded finite free complexes.
* `StacksDraft.PseudoCoherence.localizationAway_isPseudoCoherentFrom_of_boundedFiniteFree`: the
  derived localization of a bounded finite free complex is `m`-pseudo-coherent for every `m`.
* `StacksDraft.PseudoCoherence.isPseudoCoherentFrom_boundedAbove`: an `m`-pseudo-coherent object
  has cohomology vanishing in all large degrees.
* `StacksDraft.PseudoCoherence.homology_isZero_of_epi_of_mono`: the cohomological criterion, read
  off the long exact sequence, for the third vertex of a distinguished triangle to be acyclic in
  a given degree.

## Implementation notes

The ring universe `u` and the module carrier universe are kept independent: the functor acts on
`ModuleCat.{max v u}`, the smallest carrier universe containing both. Accordingly the
left-exactness input is `extendScalars_preservesFiniteLimits_of_flat'` rather than Mathlib's
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`, which only treats the carrier universe
equal to the ring universe.

`localizationAwayFunctorAux` is `Functor.mapDerivedCategory` applied to termwise extension of
scalars. That construction needs additivity together with preservation of finite limits and of
finite colimits; extension of scalars is a left adjoint, which gives additivity and the colimit
half, and flatness of a localization gives the limit half. The same four instances are rebuilt
inside each statement about the functor rather than being placed in the root instance set, because
they are keyed on a `Fact`-wrapped flatness hypothesis and searching for them unguarded is
expensive.

`localizationAwayCommShift` and `localizationAway_isTriangulated` are provided as data and as a
plain lemma rather than as instances, again to keep instance search cheap.

## References

* [Stacks Project, Tag 064W](https://stacks.math.columbia.edu/tag/064W)
* [Stacks Project, Tag 066D](https://stacks.math.columbia.edu/tag/066D)
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v u' v' w w'

namespace StacksDraft.PseudoCoherence

/-! ### Exact functors and the cohomology of the derived category -/

/-- An exact additive functor commutes with the cohomology functors on cochain complexes. -/
noncomputable def mapHomologicalComplexCompHomologyFunctorIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso F) (fun φ ↦
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map φ) F)

/-- An exact additive functor commutes with the cohomology functors of the derived category. -/
noncomputable def mapDerivedCategoryCompHomologyFunctorIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _ _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors
        (DerivedCategory.homologyFunctor D n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors D n) ≪≫
      mapHomologicalComplexCompHomologyFunctorIso F n ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n).symm F)

set_option backward.isDefEq.respectTransparency false in
/-- Extension of scalars along `algebraMap R S` sends `M` to the base change `S ⊗_R M`. -/
noncomputable def extendScalarsTensorIso
    {R : Type u} {S : Type u'} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{v} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅
      ModuleCat.of S (TensorProduct R S M) := by
  change (letI := (algebraMap R S).toAlgebra; ModuleCat.of S (TensorProduct R S M)) ≅ _
  rw [toAlgebra_algebraMap]

/-! ### Derived localization away from an element -/

/-- Derived extension of scalars from `R` to its localization away from `f`. -/
noncomputable def localizationAwayFunctorAux {R : Type u} [CommRing R] (f : R) :
    DerivedCategory (ModuleCat.{max v u} R) ⥤
      DerivedCategory (ModuleCat.{max v u} (Localization.Away f)) := by
  let F := ModuleCat.extendScalars.{u, u, max v u}
    (algebraMap R (Localization.Away f))
  letI : F.Additive := extendScalars_additive.{u, u, max v u} _
  letI : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away f) (Submonoid.powers f)))
  letI : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u}
      (algebraMap R (Localization.Away f))).leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits F :=
    PreservesColimitsOfSize.preservesFiniteColimits F
  exact F.mapDerivedCategory

/-- Extension of scalars to a localization away from `g` is additive and preserves finite limits
and finite colimits. -/
private theorem extendScalars_localizationAway_exact {R : Type u} [CommRing R] (g : R) :
    (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization.Away g))).Additive ∧
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization.Away g))) ∧
    PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization.Away g))) := by
  let F := ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization.Away g))
  have : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u}
      (algebraMap R (Localization.Away g))).leftAdjoint_preservesColimits
  exact ⟨extendScalars_additive.{u, u, max v u} _,
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away g) (Submonoid.powers g))),
    PreservesColimitsOfSize.preservesFiniteColimits F⟩

/-- The shift comparison carried by derived localization, inherited from the one carried by
`Functor.mapDerivedCategory`. -/
@[instance_reducible] noncomputable def localizationAwayCommShift
    {R : Type u} [CommRing R] (g : R) :
    (localizationAwayFunctorAux.{u, v} g).CommShift ℤ := by
  let F := ModuleCat.extendScalars.{u, u, max v u}
    (algebraMap R (Localization.Away g))
  let : F.Additive := extendScalars_additive.{u, u, max v u} _
  let : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away g) (Submonoid.powers g)))
  let : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u}
      (algebraMap R (Localization.Away g))).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits F :=
    PreservesColimitsOfSize.preservesFiniteColimits F
  change F.mapDerivedCategory.CommShift ℤ
  infer_instance

attribute [local instance] localizationAwayCommShift

/-- Derived localization, with the shift comparison `localizationAwayCommShift`, is a triangulated
functor. -/
lemma localizationAway_isTriangulated {R : Type u} [CommRing R] (g : R) :
    (localizationAwayFunctorAux.{u, v} g).IsTriangulated := by
  let F := ModuleCat.extendScalars.{u, u, max v u}
    (algebraMap R (Localization.Away g))
  obtain ⟨_, _, _⟩ := extendScalars_localizationAway_exact.{u, v} g
  change F.mapDerivedCategory.IsTriangulated
  infer_instance

attribute [local instance] localizationAway_isTriangulated

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `n`-th cohomology of the derived localization of `K` is the localization of the `n`-th
cohomology of `K`. -/
noncomputable def localizationAwayHomologyIso {R : Type u} [CommRing R] (g : R)
    (K : DerivedCategory (ModuleCat.{max v u} R)) (n : ℤ) :
    (DerivedCategory.homologyFunctor
      (ModuleCat.{max v u} (Localization.Away g)) n).obj
        ((localizationAwayFunctorAux.{u, v} g).obj K) ≅
      ModuleCat.of (Localization.Away g)
        (LocalizedModule (Submonoid.powers g)
          ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) n).obj K)) := by
  let F := ModuleCat.extendScalars.{u, u, max v u}
    (algebraMap R (Localization.Away g))
  let : F.Additive := extendScalars_additive.{u, u, max v u} _
  let : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away g) (Submonoid.powers g)))
  let : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u}
      (algebraMap R (Localization.Away g))).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits F :=
    PreservesColimitsOfSize.preservesFiniteColimits F
  exact (mapDerivedCategoryCompHomologyFunctorIso F n).app K ≪≫
    extendScalarsTensorIso (S := Localization.Away g) _ ≪≫
    LinearEquiv.toModuleIso
      ((IsLocalizedModule.isBaseChange (Submonoid.powers g)
        (Localization.Away g)
        (LocalizedModule.mkLinearMap (Submonoid.powers g)
          ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) n).obj K))).equiv)

/-- Derived localization preserves vanishing of a cohomology module. -/
lemma localizationAway_homology_isZero {R : Type u} [CommRing R] (g : R)
    (K : DerivedCategory (ModuleCat.{max v u} R)) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) n).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max v u} (Localization.Away g)) n).obj
        ((localizationAwayFunctorAux.{u, v} g).obj K)) := by
  let F := ModuleCat.extendScalars.{u, u, max v u}
    (algebraMap R (Localization.Away g))
  obtain ⟨_, _, _⟩ := extendScalars_localizationAway_exact.{u, v} g
  exact ((mapDerivedCategoryCompHomologyFunctorIso F n).app K).isZero_iff.mpr (F.map_isZero h)

/-! ### Cohomological criteria -/

/-- If the first morphism of a distinguished triangle is epi on cohomology in degree `n` and mono
on cohomology in degree `n + 1`, then the third vertex is acyclic in degree `n`. -/
lemma homology_isZero_of_epi_of_mono
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (T : Pretriangulated.Triangle (DerivedCategory C))
    (hT : T ∈ Pretriangulated.distinguishedTriangles) (n : ℤ)
    [Epi ((DerivedCategory.homologyFunctor C n).map T.mor₁)]
    [Mono ((DerivedCategory.homologyFunctor C (n + 1)).map T.mor₁)] :
    IsZero ((DerivedCategory.homologyFunctor C n).obj T.obj₃) :=
  (DerivedCategory.HomologySequence.exact₃ T hT n (n + 1)).isZero_X₂
    ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT n).mp inferInstance)
    ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT n (n + 1)).mp
      inferInstance)

/-! ### Pseudo-coherence and bounded finite free complexes -/

/-- An `m`-pseudo-coherent object is `b`-pseudo-coherent for every `b ≥ m`. -/
lemma isPseudoCoherentFrom_mono {R : Type u} [Ring R]
    {K : DerivedCategory (ModuleCat.{v} R)} {a b : ℤ}
    (h : IsPseudoCoherentFrom K a) (hab : a ≤ b) : IsPseudoCoherentFrom K b := by
  obtain ⟨E, hE, α, hα, eα⟩ := h
  refine ⟨E, hE, α, fun i hi ↦ hα i (lt_of_le_of_lt hab hi), ?_⟩
  rcases hab.eq_or_lt with rfl | hab
  · exact eα
  · have := hα b hab
    infer_instance

/-- An `m`-pseudo-coherent object has vanishing cohomology in all sufficiently large degrees. -/
lemma isPseudoCoherentFrom_boundedAbove {R : Type u} [Ring R]
    {K : DerivedCategory (ModuleCat.{v} R)} {m : ℤ} (h : IsPseudoCoherentFrom K m) :
    ∃ b : ℤ, ∀ i : ℤ, b ≤ i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
  obtain ⟨E, hE, α, hα, -⟩ := h
  obtain ⟨b, hb⟩ := hE.upperBound
  refine ⟨max (m + 1) (b + 1), fun i hi ↦ ?_⟩
  have hEi : IsZero ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℤ) i).obj E) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (E.sc i)
      ((CochainComplex.isStrictlyLE_iff E b).mp hb i (by omega))
  have hQEi : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
      (DerivedCategory.Q.obj E)) :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app E).isZero_iff.mpr hEi
  have := hα i (by omega)
  exact hQEi.of_iso (asIso ((DerivedCategory.homologyFunctor
    (ModuleCat.{v} R) i).map α)).symm

/-- A bounded finite free complex represents an `m`-pseudo-coherent object for every `m`. -/
lemma isPseudoCoherentFrom_of_boundedFiniteFree
    {R : Type u} [Ring R] (E : CochainComplex (ModuleCat.{v} R) ℤ)
    (hE : IsBoundedFiniteFree E) {K : DerivedCategory (ModuleCat.{v} R)}
    (e : DerivedCategory.Q.obj E ≅ K) (m : ℤ) : IsPseudoCoherentFrom K m :=
  ⟨E, hE, e.hom, fun _ _ ↦ inferInstance, inferInstance⟩

/-- Extension of scalars preserves bounded finite free complexes. -/
lemma extendScalars_isBoundedFiniteFree
    {R : Type u} {S : Type u'} [CommRing R] [CommRing S] [Algebra R S]
    (E : CochainComplex (ModuleCat.{v} R) ℤ) (hE : IsBoundedFiniteFree E)
    [(ModuleCat.extendScalars (algebraMap R S)).Additive] :
    IsBoundedFiniteFree
      (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj E) := by
  refine ⟨?_, ?_, fun i ↦ ?_⟩
  · obtain ⟨a, ha⟩ := hE.lowerBound
    exact ⟨a, inferInstance⟩
  · obtain ⟨a, ha⟩ := hE.upperBound
    exact ⟨a, inferInstance⟩
  · have := (hE.finiteFree i).1
    have := (hE.finiteFree i).2
    let e := (extendScalarsTensorIso (S := S) (E.X i)).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩

/-- The derived localization of a bounded finite free complex is `m`-pseudo-coherent for every
`m`. -/
lemma localizationAway_isPseudoCoherentFrom_of_boundedFiniteFree
    {R : Type u} [CommRing R] (g : R)
    (E : CochainComplex (ModuleCat.{max v u} R) ℤ) (hE : IsBoundedFiniteFree E) (m : ℤ) :
    IsPseudoCoherentFrom ((localizationAwayFunctorAux.{u, v} g).obj
      (DerivedCategory.Q.obj E)) m := by
  let F := ModuleCat.extendScalars.{u, u, max v u}
    (algebraMap R (Localization.Away g))
  obtain ⟨_, _, _⟩ := extendScalars_localizationAway_exact.{u, v} g
  exact isPseudoCoherentFrom_of_boundedFiniteFree _
    (extendScalars_isBoundedFiniteFree E hE)
    (F.mapDerivedCategoryFactors.app E).symm m

/-! ### Recognizing pseudo-coherence from the top cohomology module -/

/-- An object of `D(R)` whose cohomology vanishes above degree `m` and is finite in degree `m` is
`m`-pseudo-coherent. -/
lemma isPseudoCoherentFrom_of_finite_top_homology
    {R : Type u} [Ring R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v} R)) (m : ℤ)
    (hK : ∀ i : ℤ, m < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    [Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K)] :
    IsPseudoCoherentFrom K m := by
  let L := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eh : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K ≅ L.homology m :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) m).app L
  obtain ⟨P, hfin, hfree, f, hf⟩ := exists_finite_free_epi
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).obj K)
  obtain ⟨φ, hφ⟩ := exists_hom_from_single_of_projective L m P (f ≫ eh.hom)
  refine ⟨_, isBoundedFiniteFree_single P m, DerivedCategory.Q.map φ ≫ e.hom,
    fun i hi ↦ IsZero.isIso (DerivedCategory.isZero_of_isLE _ m i hi) (hK i hi) _, ?_⟩
  rw [Functor.map_comp]
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map
      (DerivedCategory.Q.map φ)) :=
    (epi_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) m) φ).2 hφ
  infer_instance

/-! ### Descent of pseudo-coherence along a finite principal open cover -/

/-- `m`-pseudo-coherence descends along a finite principal open cover once the cohomology of `K` is
known to vanish above `m + d`. -/
lemma isPseudoCoherentFrom_of_localization_of_bound
    {R : Type u} [CommRing R] {ι : Type*} [Finite ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤) (m : ℤ) (d : ℕ)
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hK : ∀ j : ℤ, m + d ≤ j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) j).obj K))
    (hlocal : ∀ i, IsPseudoCoherentFrom ((localizationAwayFunctorAux.{u, v} (f i)).obj K) m) :
    IsPseudoCoherentFrom K m := by
  induction d generalizing K with
  | zero =>
    exact StacksDraft.PseudoCoherence.isPseudoCoherentFrom_of_homology_isZero K m
      (by simpa using hK)
  | succ d ih =>
    let n : ℤ := m + d
    have hvanish (j : ℤ) (hj : n < j) :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) j).obj K) :=
      hK j (by dsimp [n] at hj; omega)
    have hfinite : Module.Finite R
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) n).obj K) := by
      apply Module.Finite.of_localizationSpan_range f hf
      intro i
      have := _root_.PseudoCoherence.finite_homology_of_isPseudoCoherentFrom _ n
        (isPseudoCoherentFrom_mono (hlocal i) (by dsimp [n]; omega))
        (fun j hj ↦ localizationAway_homology_isZero (f i) K j (hvanish j hj))
      exact Module.Finite.equiv (localizationAwayHomologyIso (f i) K n).toLinearEquiv
    obtain ⟨E, hE, α, hα, eα⟩ := isPseudoCoherentFrom_of_finite_top_homology K n hvanish
    obtain ⟨C, β, γ, hT⟩ := Pretriangulated.distinguished_cocone_triangle α
    let T := Pretriangulated.Triangle.mk α β γ
    have hC : ∀ j : ℤ, m + d ≤ j →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) j).obj C) := by
      intro j hj
      have hepi : Epi
          ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) j).map T.mor₁) := by
        rcases (show n ≤ j from hj).eq_or_lt with rfl | hnj
        · exact eα
        · have hIso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R)
              j).map T.mor₁) := hα j hnj
          infer_instance
      have hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R)
          (j + 1)).map T.mor₁) := hα (j + 1) (by dsimp [n]; omega)
      exact homology_isZero_of_epi_of_mono T hT j
    have hClocal (i : ι) :
        IsPseudoCoherentFrom ((localizationAwayFunctorAux.{u, v} (f i)).obj C) m :=
      _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_one m
        ((localizationAwayFunctorAux.{u, v} (f i)).mapTriangle.obj T)
        ((localizationAwayFunctorAux.{u, v} (f i)).map_distinguished T hT)
        (localizationAway_isPseudoCoherentFrom_of_boundedFiniteFree (f i) E hE (m + 1))
        (hlocal i)
    exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m T hT
      (isPseudoCoherentFrom_of_boundedFiniteFree E hE (Iso.refl _) m)
      (ih C hC hClocal)

/-- `m`-pseudo-coherence descends along a finite principal open cover. -/
lemma isPseudoCoherentFrom_of_localization
    {R : Type u} [CommRing R] {ι : Type*} [Finite ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{max v u} R)) (m : ℤ)
    (hlocal : ∀ i, IsPseudoCoherentFrom ((localizationAwayFunctorAux.{u, v} (f i)).obj K) m) :
    IsPseudoCoherentFrom K m := by
  classical
  choose b hb using fun i ↦ isPseudoCoherentFrom_boundedAbove (hlocal i)
  obtain ⟨B, hB⟩ := Finite.bddAbove_range b
  let N := max m B
  have localVanish (j : ℤ) (hj : N ≤ j) (i : ι) :
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{max v u} (Localization.Away (f i))) j).obj
          ((localizationAwayFunctorAux.{u, v} (f i)).obj K)) :=
    hb i j (le_trans (hB ⟨i, rfl⟩) (le_trans (le_max_right _ _) hj))
  have globalVanish (j : ℤ) (hj : N ≤ j) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) j).obj K) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact Module.subsingleton_of_localizationSpan_range f hf fun i ↦
      ModuleCat.isZero_iff_subsingleton.mp
        ((localVanish j hj i).of_iso (localizationAwayHomologyIso (f i) K j).symm)
  have hmN : m ≤ N := le_max_left _ _
  exact isPseudoCoherentFrom_of_localization_of_bound f hf m (N - m).toNat K
    (fun j hj ↦ globalVanish j (by omega)) hlocal

/-- Both `m`-pseudo-coherence and pseudo-coherence descend along a finite principal open cover:
if the elements `f i` generate the unit ideal and `K` becomes (`m`-)pseudo-coherent after
localization at every `f i`, then `K` is (`m`-)pseudo-coherent. -/
theorem isPseudoCoherentFrom_and_isPseudoCoherent_of_localizationAux
    {R : Type u} [CommRing R] {ι : Type*} [Finite ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{max v u} R)) (m : ℤ) :
    ((∀ i, IsPseudoCoherentFrom ((localizationAwayFunctorAux.{u, v} (f i)).obj K) m) →
      IsPseudoCoherentFrom K m) ∧
    ((∀ i, StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((localizationAwayFunctorAux.{u, v} (f i)).obj K)) →
      StacksDraft.PseudoCoherence.IsPseudoCoherent K) :=
  ⟨isPseudoCoherentFrom_of_localization f hf K m, fun h ↦
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all K).2 fun n ↦
      isPseudoCoherentFrom_of_localization f hf K n fun i ↦
        (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all
          ((localizationAwayFunctorAux.{u, v} (f i)).obj K)).1 (h i) n⟩

end StacksDraft.PseudoCoherence
