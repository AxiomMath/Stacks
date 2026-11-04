module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ImmersionIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero

/-!
# Finite type modules are exactly the `0`-pseudo-coherent ones

Let `X` be a ringed space and let `ℱ` be a sheaf of `𝒪_X`-modules. Then `ℱ`, viewed as an object
of the derived category of `𝒪_X`-modules through the degree-zero single functor, is
`0`-pseudo-coherent if and only if `ℱ` is an `𝒪_X`-module of finite type (Stacks 09V9(1)).

## Main results

* `SheafOfModules.IsFiniteType.of_iso` transports finite type along an isomorphism.
* `AlgebraicGeometry.RingedSpace.exists_epi_finiteFree_of_epi_free_over` turns an epimorphism onto
  the restriction of `ℱ` to the slice `Over W`, out of a free module on a finite index type, into
  an epimorphism onto the restriction of `ℱ` to the open subspace `W`, out of `𝒪_W^{⊕n}`.
* `AlgebraicGeometry.RingedSpace.exists_epi_finiteFree_of_isFiniteType`: a sheaf of modules of
  finite type receives, near every point, an epimorphism from a finite free module on the
  corresponding open subspace.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_zero_of_isFiniteType` and
  `AlgebraicGeometry.RingedSpace.isFiniteType_of_isPseudoCoherentFrom_singleFunctor_zero` are the
  two halves of Stacks 09V9(1), and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_zero_iff_isFiniteType` is
  their conjunction.

## Implementation notes

`SheafOfModules.IsFiniteType` is phrased in the **slice** idiom: it asks for a covering `W i` of
the site of opens of `X` and, over each `W i`, finitely many generating sections of the
restriction `ℱ.over (W i)` of `ℱ` to the slice category `Over (W i)`. Stacks 08CB, and therefore
`AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom`, is phrased in the **open subspace** idiom:
the approximating strictly perfect complex lives on the ringed space
`X.restrict W.isOpenEmbedding`. The bridge between the two is
`AlgebraicGeometry.RingedSpace.restrictModulesIsoOverComp`, which exhibits restriction to
an open subspace as restriction to the slice followed by the equivalence
`AlgebraicGeometry.RingedSpace.overToRestricted`.

All universes coincide, as everywhere in this directory: `StrictlyPerfect.OXMod` is only defined
when the ring universe and the space universe of the ringed space agree.

## References

* [The Stacks Project, Lemma 36.60.11 (09V9)](https://stacks.math.columbia.edu/tag/09V9)
* [The Stacks Project, Lemma 20.47.4 (08DN)](https://stacks.math.columbia.edu/tag/08DN)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect AlgebraicGeometry

namespace SheafOfModules

universe u v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ Y, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A sheaf of modules isomorphic to a sheaf of modules of finite type is of finite type. -/
public theorem IsFiniteType.of_iso {M N : SheafOfModules.{u} R} (h : M.IsFiniteType) (e : M ≅ N) :
    N.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := h.exists_localGeneratorsData
  exact ⟨Stacks.FiniteLocallyFree.localGeneratorsDataOfIsIso e.hom σ, inferInstance⟩

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- An epimorphism onto the restriction of an `𝒪_X`-module `ℳ` to the slice `Over W`, out of the
free module on a finite index type `I`, gives an epimorphism onto the restriction of `ℳ` to the
open subspace `W`, out of `𝒪_W^{⊕n}` for `n` the cardinality of `I`. -/
public theorem exists_epi_finiteFree_of_epi_free_over (M : OXMod.{u, u} X) (W : Opens X.carrier)
    {I : Type u} [Finite I]
    (p : SheafOfModules.free (R := (structureSheafOfRings X).over W) I ⟶ M.over W) (hp : Epi p) :
    ∃ (n : ℕ) (q : finiteFree (X.restrict W.isOpenEmbedding) n ⟶ (restrictModules X W).obj M),
      Epi q := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  have eFree : SheafOfModules.free (R := (structureSheafOfRings X).over W)
      (ULift.{u} (Fin (Fintype.card I))) ≅
      SheafOfModules.free (R := (structureSheafOfRings X).over W) I :=
    (SheafOfModules.freeFunctor (R := (structureSheafOfRings X).over W)).mapIso
      (Equiv.toIso (Equiv.ulift.trans (Fintype.equivFin I).symm))
  have eOver : SheafOfModules.free (R := structureSheafOfRings (X.restrict W.isOpenEmbedding))
      (ULift.{u} (Fin (Fintype.card I))) ≅
      (overToRestricted X W).obj (SheafOfModules.free
        (R := (structureSheafOfRings X).over W) (ULift.{u} (Fin (Fintype.card I)))) :=
    equivOverFreeIso X W (ULift.{u} (Fin (Fintype.card I)))
  have eTgt : (overToRestricted X W).obj (M.over W) ≅ (restrictModules X W).obj M :=
    ((restrictModulesIsoOverComp X W).symm.app M).symm
  exact ⟨Fintype.card I, (finiteFreeIsoFree (X.restrict W.isOpenEmbedding) _).hom ≫ eOver.hom ≫
    (overToRestricted X W).map (eFree.hom ≫ p) ≫ eTgt.hom, inferInstance⟩

/-- An `𝒪_X`-module of finite type receives, near every point of `X`, an epimorphism from a finite
free module on the corresponding open subspace. -/
public theorem exists_epi_finiteFree_of_isFiniteType (F : OXMod.{u, u} X)
    (hF : SheafOfModules.IsFiniteType (R := structureSheafOfRings X) F) (x : X.carrier) :
    ∃ W : Opens X.carrier, x ∈ W ∧ ∃ (n : ℕ)
      (q : finiteFree (X.restrict W.isOpenEmbedding) n ⟶ (restrictModules X W).obj F), Epi q := by
  obtain ⟨σ, hσ⟩ := hF.exists_localGeneratorsData
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff X.carrier σ.X).mp σ.coversTop).exists_mem x
  have hgen : (σ.generators i).IsFiniteType := hσ.isFiniteType i
  exact ⟨σ.X i, hxi,
    exists_epi_finiteFree_of_epi_free_over F (σ.X i) (σ.generators i).π (σ.generators i).epi⟩

/-- **Stacks 09V9(1), the implication from finite type to pseudo-coherence.** An `𝒪_X`-module of
finite type is `0`-pseudo-coherent when viewed in degree zero as an object of the derived category
of `𝒪_X`-modules. -/
public theorem isPseudoCoherentFrom_singleFunctor_zero_of_isFiniteType
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (F : OXMod.{u, u} X)
    (hF : SheafOfModules.IsFiniteType (R := structureSheafOfRings X) F) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) 0 :=
  isPseudoCoherentFrom_singleFunctor_zero_of_exists_epi F fun x => by
    obtain ⟨W, hxW, n, q, hq⟩ := exists_epi_finiteFree_of_isFiniteType F hF x
    exact ⟨W, hxW, finiteFree (X.restrict W.isOpenEmbedding) n, ⟨n, ⟨Retract.refl _⟩⟩, q, hq⟩

/-- **Stacks 09V9(1), the implication from pseudo-coherence to finite type.** An `𝒪_X`-module
which is `0`-pseudo-coherent when viewed in degree zero as an object of the derived category of
`𝒪_X`-modules is of finite type. -/
public theorem isFiniteType_of_isPseudoCoherentFrom_singleFunctor_zero
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (F : OXMod.{u, u} X)
    (hF : IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) 0) :
    SheafOfModules.IsFiniteType (R := structureSheafOfRings X) F := by
  have hvanish : ∀ i : ℤ, 0 < i → IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)) := fun i hi =>
    IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 F i
      (by lia)) (derivedHomologyIso _ i)
  exact SheafOfModules.IsFiniteType.of_iso (R := structureSheafOfRings X)
    (isFiniteType_homology_of_isPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) 0 hF hvanish)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (OXMod.{u, u} X) 0).app F)

/-- Let `X` be a ringed space and let `ℱ` be a sheaf of `𝒪_X`-modules. Then `ℱ`, viewed in degree
zero as an object of the derived category of `𝒪_X`-modules, is `0`-pseudo-coherent if and only if
`ℱ` is an `𝒪_X`-module of finite type. -/
@[stacks 09V9 "finite_type_iff_zero_pseudo_coherent"]
public theorem isPseudoCoherentFrom_singleFunctor_zero_iff_isFiniteType
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (F : OXMod.{u, u} X) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) 0 ↔
      SheafOfModules.IsFiniteType (R := structureSheafOfRings X) F :=
  ⟨isFiniteType_of_isPseudoCoherentFrom_singleFunctor_zero F,
    isPseudoCoherentFrom_singleFunctor_zero_of_isFiniteType F⟩

end AlgebraicGeometry.RingedSpace

end
