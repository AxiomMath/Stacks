module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.TopCohomology
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedCharacterization
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.PseudoCoherent.Triangle
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedCharacterization
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Pseudo-coherence on an affine scheme

Let `A` be a commutative ring and let `M` be a cochain complex of `A`-modules. Applying the
associated-sheaf functor `~` degreewise produces a complex of `𝒪`-modules on `Spec A`. This file
proves that the two notions of pseudo-coherence agree across that construction: the complex of
sheaves is `m`-pseudo-coherent in the sense of Stacks 08CB exactly when the complex of modules is
`m`-pseudo-coherent in the sense of Stacks 064Q, and likewise without the degree bound.

Both directions are genuine. The easy one is that a bounded complex of finite free `A`-modules
sheafifies to a strictly perfect complex, so a module-level approximation sheafifies to a global
strictly perfect approximation on `Spec A`, which Stacks 08CC turns into sheaf-level
pseudo-coherence. The converse is a downward induction on the length of the window in which the
cohomology of `M` can be nonzero: the top cohomology sheaf of a sheaf-level `m`-pseudo-coherent
object is of finite type (Stacks 08DN), so by Stacks 01PB the top cohomology module is finite,
which makes the module-level object `n`-pseudo-coherent at the top degree `n`; the cone on that
approximation has a shorter window and is still sheaf-level pseudo-coherent by Stacks 08CD, and
the induction hypothesis applies to it.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_tilde_iff` is Tag 08E7 for
  `m`-pseudo-coherence.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_tilde_iff` is Tag 08E7 for pseudo-coherence.

## Implementation notes

The module universe, the ring universe and the space universe all coincide, as they must for
`StrictlyPerfect.OXMod` to exist at all; this is the universe signature of the whole
strictly-perfect ladder. For a commutative ring `A : Type u` the ringed space is
`(Spec (CommRingCat.of A)).toRingedSpace` and the category of modules on it is
`StrictlyPerfect.OXMod.{u, u}` of that space, which is definitionally
`(Spec (CommRingCat.of A)).Modules`, the codomain of `AlgebraicGeometry.tilde.functor`.

The instances `Additive`, `PreservesZeroMorphisms`, `PreservesFiniteLimits` and `IsLeftAdjoint`
for `AlgebraicGeometry.tilde.functor` exist in Mathlib and in
`StacksFrontier/AlgebraicGeometry/Modules/TildeExactness.lean`, but are stated with the codomain
spelled `(Spec R).Modules`, which is not the spelling instance search meets here. They are
therefore re-registered as local instances at the `StrictlyPerfect.OXMod` spelling and in the
`A : Type u` form, which is the form in which the two main statements present the coefficient
ring. No new mathematics is involved; the terms are the existing ones.

Boundedness of the cohomology of a sheaf-level pseudo-coherent object on `Spec A` — the input to
the induction — uses quasi-compactness of the spectrum: each point has a neighbourhood on which a
strictly perfect approximation exists, hence on which the cohomology vanishes above the top degree
of that approximation, and finitely many such neighbourhoods cover.

## References

* [Stacks Project, Lemma 36.61.4 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.46.9 (08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Lemma 20.46.6 (08CD)](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Lemma 20.46.12 (08DN)](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Definition 15.64.1 (064Q)](https://stacks.math.columbia.edu/tag/064Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  TopologicalSpace
open StrictlyPerfect
open Stacks.PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

universe v v' u u' d d'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{d} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{d'} D]

/-- The image under an exact functor of a morphism of the derived category, read as a morphism
between the images of the two representing complexes. -/
def mapDerivedCategoryHom (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {P M : CochainComplex C ℤ}
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  F.mapDerivedCategoryFactors.inv.app P ≫ F.mapDerivedCategory.map α ≫
    F.mapDerivedCategoryFactors.hom.app M

/-- **An exact functor preserves isomorphy on the cohomology of a derived morphism.** This is the
derived-category analogue of `AlgebraicGeometry.RingedSpace.isIso_homologyMap_map`; the comparison
is `StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso`, and the two outer
factors of `mapDerivedCategoryHom` are isomorphisms. -/
theorem isIso_homologyMap_mapDerivedCategoryHom (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {P M : CochainComplex C ℤ}
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) (i : ℤ)
    (hα : IsIso ((DerivedCategory.homologyFunctor C i).map α)) :
    IsIso ((DerivedCategory.homologyFunctor D i).map (mapDerivedCategoryHom F α)) := by
  have hmap : IsIso ((DerivedCategory.homologyFunctor D i).map
      (F.mapDerivedCategory.map α)) :=
    (NatIso.isIso_map_iff
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i) α).mpr
      (Functor.map_isIso F _)
  rw [mapDerivedCategoryHom, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **An exact functor preserves surjectivity on the cohomology of a derived morphism.** This is
the derived-category analogue of `AlgebraicGeometry.RingedSpace.epi_homologyMap_map`. -/
theorem epi_homologyMap_mapDerivedCategoryHom (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {P M : CochainComplex C ℤ}
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) (i : ℤ)
    (hα : Epi ((DerivedCategory.homologyFunctor C i).map α)) :
    Epi ((DerivedCategory.homologyFunctor D i).map (mapDerivedCategoryHom F α)) := by
  have hmap : Epi ((DerivedCategory.homologyFunctor D i).map
      (F.mapDerivedCategory.map α)) :=
    (Stacks.PseudoCoherence.DerivedCharacterization.epi_map_iff_of_natIso
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i) α).mpr
      (preserves_epi_of_preservesColimit F _)
  rw [mapDerivedCategoryHom, Functor.map_comp, Functor.map_comp]
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

universe u d

/-- **A sheaf of modules with vanishing restrictions to an open covering is zero.** The sections
of the restriction to an open subspace are the sections over the opens contained in it, so if every
member of a covering family has zero restriction then every section of the sheaf is locally zero,
hence zero. -/
public theorem isZero_of_restrictModules (X : RingedSpace.{u, u}) (M : OXMod.{u, u} X)
    {ι : Type*} (U : ι → Opens X.carrier) (hU : ∀ x : X.carrier, ∃ i, x ∈ U i)
    (hM : ∀ i, IsZero ((restrictModules X (U i)).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).2
  ext V s
  show s = 0
  apply (show TopCat.Presheaf.IsSheaf M.val.presheaf from M.isSheaf).section_ext
    (U := V) (s := s) (t := 0)
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  refine ⟨V.unop ⊓ U i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  have hW : (U i).isOpenEmbedding.functor.obj ((Opens.map (U i).inclusion').obj V.unop) =
      V.unop ⊓ U i := by
    ext y
    simp [Topology.IsOpenEmbedding.functor]
  have hZ : IsZero (M.val.obj (Opposite.op (V.unop ⊓ U i))) := by
    rw [← hW]
    exact (IsZero.iff_id_eq_zero _).2
      (congrArg (fun f : (restrictModules X (U i)).obj M ⟶ (restrictModules X (U i)).obj M =>
          f.val.app (Opposite.op ((Opens.map (U i).inclusion').obj V.unop)))
        ((IsZero.iff_id_eq_zero _).1 (hM i)))
  exact @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.mp hZ) _ _

/-! ### The associated-sheaf functor on an affine spectrum

The exactness instances for `AlgebraicGeometry.tilde.functor` are registered at the
`StrictlyPerfect.OXMod` spelling of its codomain and in the form in which the statements below
present the coefficient ring. -/

section Tilde

variable (A : Type u) [CommRing A]

/-- The associated-sheaf functor is additive: it is additive on sections. -/
instance tilde_functor_additive :
    (tilde.functor (CommRingCat.of A) :
      ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace).Additive :=
  ⟨fun {_ _} f g => tilde.map_add f g⟩

/-- The associated-sheaf functor preserves zero morphisms. -/
instance tilde_functor_preservesZeroMorphisms :
    (tilde.functor (CommRingCat.of A) :
      ModuleCat.{u} A ⥤
        OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace).PreservesZeroMorphisms :=
  ⟨fun _ _ => tilde.map_zero (R := CommRingCat.of A)⟩

/-- The associated-sheaf functor preserves finite limits. -/
instance tilde_functor_preservesFiniteLimits :
    PreservesFiniteLimits (tilde.functor (CommRingCat.of A) :
      ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace) :=
  AlgebraicGeometry.tilde.preservesFiniteLimits (CommRingCat.of A)

/-- The associated-sheaf functor is a left adjoint, hence preserves finite colimits. -/
instance tilde_functor_isLeftAdjoint :
    (tilde.functor (CommRingCat.of A) :
      ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace).IsLeftAdjoint :=
  tilde.adjunction.isLeftAdjoint

end Tilde

/-- **The associated sheaf of a finite free module on an affine spectrum is a direct summand of a
finite free `𝒪`-module.** Choosing a basis identifies the module with `A^{⊕n}`, over the zero ring
with `A^{⊕0}`; `AlgebraicGeometry.tildeFinsupp` identifies the associated sheaf of `A^{⊕n}` with
the free `𝒪`-module on `n` generators, and that is `StrictlyPerfect.finiteFree` after reindexing
the `ULift`. -/
public theorem isDirectSummandOfFiniteFree_tilde_of_finite_free {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) [Module.Finite A M] [Module.Free A M] :
    IsDirectSummandOfFiniteFree
      ((tilde.functor (CommRingCat.of A) :
        ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace).obj M) := by
  classical
  let F : ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace :=
    tilde.functor (CommRingCat.of A)
  obtain ⟨n, ⟨eM⟩⟩ : ∃ n : ℕ, Nonempty
      (M ≅ ModuleCat.of A (ULift.{u} (Fin n) →₀ A)) := by
    by_cases hA : Nontrivial A
    · let b := Module.Free.chooseBasis A M
      have : Finite (Module.Free.ChooseBasisIndex A M) := Module.Finite.finite_basis b
      let : Fintype (Module.Free.ChooseBasisIndex A M) := Fintype.ofFinite _
      exact ⟨Fintype.card (Module.Free.ChooseBasisIndex A M),
        ⟨(b.repr.trans (Finsupp.domLCongr
          ((Fintype.equivFin _).trans Equiv.ulift.symm))).toModuleIso⟩⟩
    · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
      have : Subsingleton M := Module.subsingleton A M
      exact ⟨0, ⟨{
        hom := ModuleCat.ofHom (0 : M →ₗ[A] (ULift.{u} (Fin 0) →₀ A))
        inv := ModuleCat.ofHom (0 : (ULift.{u} (Fin 0) →₀ A) →ₗ[A] M)
        hom_inv_id := ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)
        inv_hom_id := ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _) }⟩⟩
  let U₀ : ULift.{u} (Fin n) → OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace :=
    fun _ => structureModule (Spec (CommRingCat.of A)).toRingedSpace
  let V₀ : Fin n → OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace :=
    fun _ => structureModule (Spec (CommRingCat.of A)).toRingedSpace
  let eFree : SheafOfModules.free.{u} (ULift.{u} (Fin n)) ≅
      finiteFree (Spec (CommRingCat.of A)).toRingedSpace n := by
    show SheafOfModules.free.{u} (ULift.{u} (Fin n)) ≅ ⨁ V₀
    exact (biproduct.isoCoproduct U₀).symm ≪≫
      biproduct.whiskerEquiv (f := U₀) (g := V₀) Equiv.ulift (fun _ => Iso.refl _)
  let e : F.obj M ≅ finiteFree (Spec (CommRingCat.of A)).toRingedSpace n :=
    F.mapIso eM ≪≫ AlgebraicGeometry.tildeFinsupp (R := CommRingCat.of A)
      (ULift.{u} (Fin n)) ≪≫ eFree
  exact (isDirectSummandOfFiniteFree_iff_retract (F.obj M)).2
    ⟨n, ⟨⟨e.hom, e.inv, e.hom_inv_id⟩⟩⟩

/-- **A bounded complex of finite free modules sheafifies to a strictly perfect complex.** Only
finitely many of its terms are nonzero, and each of them sheafifies to a direct summand of a finite
free `𝒪`-module. -/
public theorem isStrictlyPerfect_tilde_of_isBoundedFiniteFree {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedFiniteFree P) :
    IsStrictlyPerfect
      (((tilde.functor (CommRingCat.of A) :
        ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
        ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  classical
  let F : ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace :=
    tilde.functor (CommRingCat.of A)
  let : F.PreservesZeroMorphisms := tilde_functor_preservesZeroMorphisms A
  obtain ⟨a, ha⟩ := hP.lowerBound
  obtain ⟨b, hb⟩ := hP.upperBound
  refine ⟨(Set.finite_Icc a b).subset fun i hi => ?_, fun i => ?_⟩
  · simp only [Set.mem_ofPred_eq] at hi
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · by_contra hia
      exact hi (Functor.map_isZero F ((CochainComplex.isStrictlyGE_iff P a).mp ha i (by omega)))
    · by_contra hib
      exact hi (Functor.map_isZero F ((CochainComplex.isStrictlyLE_iff P b).mp hb i (by omega)))
  · obtain ⟨_, _⟩ := hP.finiteFree i
    exact isDirectSummandOfFiniteFree_tilde_of_finite_free (P.X i)

/-! ### The easy direction -/

/-- **A module-level `m`-pseudo-coherent complex sheafifies to a sheaf-level `m`-pseudo-coherent
object.** The bounded finite free approximation sheafifies to a strictly perfect complex on all of
`Spec A`, and the associated-sheaf functor is exact, so the two conditions on cohomology survive;
the covering in the definition of sheaf-level `m`-pseudo-coherence is then the trivial one by
`⊤`. -/
public theorem isPseudoCoherentFrom_tilde_of_module {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (m : ℤ)
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj M) m) :
    IsPseudoCoherentFrom (X := (Spec (CommRingCat.of A)).toRingedSpace)
      (DerivedCategory.Q.obj
        (((tilde.functor (CommRingCat.of A) :
          ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
          ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) m := by
  obtain ⟨P, hP, α, hαgt, hαepi⟩ := hM
  let X := (Spec (CommRingCat.of A)).toRingedSpace
  let F : ModuleCat.{u} A ⥤ OXMod.{u, u} X := tilde.functor (CommRingCat.of A)
  let : F.Additive := tilde_functor_additive A
  let : PreservesFiniteLimits F := tilde_functor_preservesFiniteLimits A
  let : F.IsLeftAdjoint := tilde_functor_isLeftAdjoint A
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let R := restrictModules X ⊤
  let : R.Additive := restrictModules_additive X ⊤
  let : PreservesFiniteLimits R := restrictModules_preservesFiniteLimits X ⊤
  let : PreservesFiniteColimits R := restrictModules_preservesFiniteColimits X ⊤
  let αF := mapDerivedCategoryHom F α
  let αU := mapDerivedCategoryHom R αF
  have hlocal : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ Q : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect Q ∧
        ∃ β : DerivedCategory.Q.obj Q ⟶ DerivedCategory.Q.obj (restrictComplex (Fc.obj M) U),
          (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β)) ∧
          Epi ((DerivedCategory.homologyFunctor _ m).map β) := by
    intro _
    exact ⟨⊤, trivial, restrictComplex (Fc.obj P) ⊤,
      isStrictlyPerfect_restrictComplex
        (isStrictlyPerfect_tilde_of_isBoundedFiniteFree P hP) ⊤, αU,
      fun i hi => isIso_homologyMap_mapDerivedCategoryHom R αF i
        (isIso_homologyMap_mapDerivedCategoryHom F α i (hαgt i hi)),
      epi_homologyMap_mapDerivedCategoryHom R αF m
        (epi_homologyMap_mapDerivedCategoryHom F α m hαepi)⟩
  exact DerivedCharacterization.isPseudoCoherentFrom_of_local_derived_approximation
    (DerivedCategory.Q.obj (Fc.obj M)) m (Fc.obj M) (Iso.refl _) hlocal

/-! ### Cohomology of a sheaf-level pseudo-coherent object is bounded above -/

/-- **On a quasi-compact ringed space the cohomology of an `m`-pseudo-coherent object of the
derived category vanishes in all sufficiently large degrees.** A strictly perfect local
approximation is a bounded complex, so above its top nonzero degree the cohomology of the
approximated complex vanishes after restriction to the open set the approximation lives on.
Finitely many of those open sets cover the space, and a sheaf of modules whose restrictions to a
covering family vanish is zero. -/
public theorem exists_isZero_homology_of_isPseudoCoherentFrom {X : RingedSpace.{u, u}}
    [CompactSpace X.carrier] [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ) (hE : IsPseudoCoherentFrom E m) :
    ∃ b : ℤ, ∀ i : ℤ, b ≤ i →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) := by
  classical
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  have hlocal : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ b : ℤ, ∀ i : ℤ, b ≤ i → IsZero ((restrictModules X U).obj (K.homology i)) := by
    intro x
    obtain ⟨U, hx, P, hP, α, hα, -⟩ := hK x
    obtain ⟨b, hb⟩ := hP.bounded.bddAbove
    refine ⟨U, hx, max (m + 1) (b + 1), fun i hi => ?_⟩
    have hPi : IsZero (P.X i) := by
      by_contra hn
      have := hb hn
      omega
    have hαi : IsIso (HomologicalComplex.homologyMap α i) := hα i (by omega)
    have htarget : IsZero ((restrictComplex K U).homology i) :=
      ((P.sc i).isZero_homology_of_isZero_X₂ hPi).of_iso
        (asIso (HomologicalComplex.homologyMap α i)).symm
    have := restrictModules_preservesFiniteLimits X U
    have := restrictModules_preservesFiniteColimits X U
    exact htarget.of_iso ((K.sc i).mapHomologyIso (restrictModules X U)).symm
  choose U hx b hb using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X.carrier => (U x : Set X.carrier)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  obtain ⟨c, hc⟩ := (s.finite_toSet.image b).bddAbove
  refine ⟨c, fun i hi => ?_⟩
  have hKH : IsZero (K.homology i) := by
    refine isZero_of_restrictModules X (K.homology i) (fun x : s => U x) (fun x => ?_)
      (fun x => hb x i (le_trans (hc (Set.mem_image_of_mem b x.property)) hi))
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, hxy⟩
  exact hKH.of_iso (((DerivedCategory.homologyFunctorFactors _ i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso eK).symm

/-! ### The hard direction, by induction on the cohomological window -/

/-- **Descending induction on the window.** If the cohomology of `K` vanishes in degrees `≥ m + d`
and the associated derived sheaf of `K` is sheaf-level `m`-pseudo-coherent, then `K` is
`m`-pseudo-coherent. For `d = 0` the object is acyclic in degrees `≥ m` and the zero complex is an
approximation. For `d + 1`, Tag 08DN makes the top cohomology sheaf of finite type, Tag 01PB turns
that into finiteness of the degree-`(m + d)` cohomology module, and a finite free cover of it is an
`(m + d)`-pseudo-coherent approximation `α`. Its cone has a window one shorter, and is still
sheaf-level `m`-pseudo-coherent by Tag 08CD part (1), so the induction hypothesis applies to it;
Stacks 064R (2) then assembles `K` from the two outer terms of the triangle. -/
private theorem module_isPseudoCoherentFrom_of_tilde_of_window {A : Type u} [CommRing A]
    (m : ℤ) (d : ℕ) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ j : ℤ, m + d ≤ j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K))
    (hS : IsPseudoCoherentFrom (X := (Spec (CommRingCat.of A)).toRingedSpace)
      ((tilde.functor (CommRingCat.of A) :
        ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
        ).mapDerivedCategory.obj K) m) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom K m := by
  induction d generalizing K with
  | zero =>
    exact StacksDraft.PseudoCoherence.isPseudoCoherentFrom_of_homology_isZero K m
      (by simpa using hK)
  | succ d ih =>
    let F : ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace :=
      tilde.functor (CommRingCat.of A)
    let : F.Additive := tilde_functor_additive A
    let : PreservesFiniteLimits F := tilde_functor_preservesFiniteLimits A
    let : F.IsLeftAdjoint := tilde_functor_isLeftAdjoint A
    have hvanish (j : ℤ) (hj : m + (d : ℤ) < j) :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K) :=
      hK j (by omega)
    have hfinite : Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (m + (d : ℤ))).obj K) := by
      have htop : ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor
          (OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace)
            (m + (d : ℤ))).obj K).IsFiniteType := isFiniteType_homology_of_isPseudoCoherentFrom
        (X := (Spec (CommRingCat.of A)).toRingedSpace) (F.mapDerivedCategory.obj K) (m + (d : ℤ))
        (hS.mono (by omega))
        (fun j hj => (Functor.map_isZero F (hvanish j hj)).of_iso
          ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F j).app K))
      exact (AlgebraicGeometry.tilde_isFiniteType_iff _).mp
        (Stacks.SheafOfModules.isFiniteType_of_iso
          (N := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (m + (d : ℤ)) ⋙ F).obj K)
          ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F
            (m + (d : ℤ))).app K))
    obtain ⟨P, hP, α, hα, hepi⟩ :=
      StacksDraft.PseudoCoherence.isPseudoCoherentFrom_of_finite_top_homology K
        (m + (d : ℤ)) hvanish
    obtain ⟨C, β, γ, hT⟩ := Pretriangulated.distinguished_cocone_triangle α
    let T := Pretriangulated.Triangle.mk α β γ
    have hC : ∀ j : ℤ, m + d ≤ j →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj C) := by
      intro j hj
      have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map T.mor₁) := by
        rcases (show m + (d : ℤ) ≤ j from hj).eq_or_lt with rfl | hnj
        · exact hepi
        · have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map T.mor₁) :=
            hα j hnj
          infer_instance
      have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (j + 1)).map T.mor₁) :=
        hα (j + 1) (by omega)
      exact StacksDraft.PseudoCoherence.homology_isZero_of_epi_of_mono T hT j
    have hP' : ∀ n, StacksDraft.PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj P) n :=
      fun _ => ⟨P, hP, 𝟙 _, fun _ _ => inferInstance, inferInstance⟩
    have hPS : IsPseudoCoherentFrom (X := (Spec (CommRingCat.of A)).toRingedSpace)
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) (m + 1) :=
      (isPseudoCoherentFrom_tilde_of_module P (m + 1) (hP' _)).of_iso
        (F.mapDerivedCategoryFactors.app P).symm
    have hCS : IsPseudoCoherentFrom (X := (Spec (CommRingCat.of A)).toRingedSpace)
        (F.mapDerivedCategory.obj C) m :=
      isPseudoCoherentFrom_obj₃_of_distinguished m (F.mapDerivedCategory.mapTriangle.obj T)
        (F.mapDerivedCategory.map_distinguished T hT) hPS hS
    exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m T hT (hP' m)
      (ih C hC hCS)

/-! ### Tag 08E7 -/

/-- **Tag 08E7 for `m`-pseudo-coherence.** A complex of `A`-modules is `m`-pseudo-coherent exactly
when the complex of `𝒪`-modules it determines on `Spec A` is `m`-pseudo-coherent. -/
@[stacks 08E7 "m-pseudo-coherent"]
public theorem isPseudoCoherentFrom_tilde_iff {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (m : ℤ) :
    IsPseudoCoherentFrom (X := (Spec (CommRingCat.of A)).toRingedSpace)
        (DerivedCategory.Q.obj
          (((tilde.functor (CommRingCat.of A) :
            ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
            ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj M) m := by
  refine ⟨fun hS => ?_, isPseudoCoherentFrom_tilde_of_module M m⟩
  let F : ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace :=
    tilde.functor (CommRingCat.of A)
  let : F.Additive := tilde_functor_additive A
  let : PreservesFiniteLimits F := tilde_functor_preservesFiniteLimits A
  let : F.IsLeftAdjoint := tilde_functor_isLeftAdjoint A
  have hS' : IsPseudoCoherentFrom (X := (Spec (CommRingCat.of A)).toRingedSpace)
      (F.mapDerivedCategory.obj (DerivedCategory.Q.obj M)) m :=
    hS.of_iso (F.mapDerivedCategoryFactors.app M).symm
  obtain ⟨b, hb⟩ := exists_isZero_homology_of_isPseudoCoherentFrom _ m hS'
  have hbound : ∀ i : ℤ, b ≤ i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (DerivedCategory.Q.obj M)) := by
    intro i hi
    have : F.Faithful := tilde.fullyFaithfulFunctor.faithful
    have : F.Full := tilde.fullyFaithfulFunctor.full
    exact IsZero.of_full_of_faithful_of_isZero F _ ((hb i hi).of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i).app
        (DerivedCategory.Q.obj M)).symm)
  exact module_isPseudoCoherentFrom_of_tilde_of_window m (b - m).toNat
    (DerivedCategory.Q.obj M) (fun i hi => hbound i (by omega)) hS'

/-- **Tag 08E7 for pseudo-coherence.** A complex of `A`-modules is pseudo-coherent exactly when the
complex of `𝒪`-modules it determines on `Spec A` is pseudo-coherent. Both sides are equivalent to
the conjunction over all degrees of the fixed-degree condition: on the module side by Stacks 064W,
on the sheaf side because Tag 08CC part (2) lets the one complex representing the object serve as
the `m`-pseudo-coherent representative for every `m`. -/
@[stacks 08E7 "pseudo-coherent"]
public theorem isPseudoCoherent_tilde_iff {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsPseudoCoherent (X := (Spec (CommRingCat.of A)).toRingedSpace)
        (DerivedCategory.Q.obj
          (((tilde.functor (CommRingCat.of A) :
            ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace
            ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj M) := by
  let F : ModuleCat.{u} A ⥤ OXMod.{u, u} (Spec (CommRingCat.of A)).toRingedSpace :=
    tilde.functor (CommRingCat.of A)
  let : F.PreservesZeroMorphisms := tilde_functor_preservesZeroMorphisms A
  let E := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  have hsheaf : IsPseudoCoherent (X := (Spec (CommRingCat.of A)).toRingedSpace)
      (DerivedCategory.Q.obj E) ↔
      ∀ m : ℤ, IsPseudoCoherentFrom (X := (Spec (CommRingCat.of A)).toRingedSpace)
        (DerivedCategory.Q.obj E) m :=
    ⟨fun h m => h.isPseudoCoherentFrom m, fun h => ⟨E, fun m =>
      DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso
        (DerivedCategory.Q.obj E) m (h m) E (Iso.refl _), ⟨Iso.refl _⟩⟩⟩
  refine hsheaf.trans ?_
  rw [StacksDraft.PseudoCoherence.pseudoCoherent_iff_all]
  exact forall_congr' fun m => isPseudoCoherentFrom_tilde_iff M m

end AlgebraicGeometry.RingedSpace

end
