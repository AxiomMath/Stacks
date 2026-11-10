module

public import StacksFrontier.Algebra.Homology.KoszulConeTensor
public import StacksFrontier.AlgebraicGeometry.Etale.EmptyClosedFibreCover
public import StacksFrontier.AlgebraicGeometry.SheafComplexLocality.Basic
public import StacksFrontier.Homology.Tor.DerivedTensorKFlatModel
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.DerivedSectionsInjectiveModel
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.SectionsOverBaseLinear
public import StacksFrontier.RingTheory.RegularLocalRing.KoszulResidueFieldModel

/-!
# The derived sections of a scheme over a punctured spectrum die modulo the maximal ideal

Let `(A, 𝔪)` be a regular local ring and let `f : V ⟶ Spec A` be a morphism of schemes which
factors through the punctured spectrum `Spec A ∖ {𝔪}`. For every sheaf of modules `F` on `V` the
derived tensor product `RΓ(V, F) ⊗^L_A A/𝔪` vanishes.

This is the input of [Stacks, Tag 0ECC] which the source takes from cohomology and base change
along the empty closed fibre. The proof here does not go through base change: it computes the
derived tensor product on explicit complexes and checks the resulting complex of `A`-modules to be
acyclic.

Write `𝔪 = (x₁, …, x_r)` for a Koszul-regular generating family, which a regular local ring has
(`IsRegularLocalRing.exists_isKoszulRegular_span_eq_maximalIdeal`). Then:

* `RΓ(V, F)` is the complex `Γ(V, J)` of global sections of an injective resolution `J` of `F`
  (`Stacks.LocalCohomology.exists_nonempty_Q_obj_iso_derivedSectionsOverBase`), and `A/𝔪` is the
  cochain Koszul complex of `x`, which is K-flat
  (`Koszul.nonempty_Q_obj_seqCochainComplex_iso_single`), so the derived tensor product vanishes as
  soon as `Γ(V, J) ⊗_A Kos(x)` is acyclic
  (`Stacks.DerivedTensor.isZero_derivedTensor_of_acyclic_tensor_kFlat_of_iso`);
* `Γ(V, J) ⊗_A Kos(x)` is the image under global sections of `J ⊗_A Kos(x)`, the complex of
  sheaves of modules built in `StacksFrontier/Algebra/Homology/KoszulConeTensor.lean`, whose terms
  are again injective and which is bounded below;
* `J ⊗_A Kos(x)` is acyclic, because the standard opens of the `x_i` cover `V` — that is the
  emptiness of the closed fibre, in the form
  `Stacks.PuncturedSpectrum.iSup_basicOpen_baseHom_eq_top_puncturedSpectrum` — and on each of them
  one `x_i` is invertible, which makes the Koszul complex acyclic there.

## Main definitions

* `Stacks.PuncturedSpectrum.sectionsOnOpen` — the sections of a sheaf of modules over an open set
  of `V`, as a functor to modules over the sections of the structure sheaf there.

## Main results

* `Stacks.PuncturedSpectrum.acyclic_koszulTensor_of_puncturedSpectrum` — the Koszul cone complex
  of a generating family of `𝔪` on a complex of sheaves of modules over the punctured spectrum is
  acyclic.
* `Stacks.PuncturedSpectrum.isZero_derivedTensor_derivedSectionsOverBase_residueField` — the
  vanishing of `RΓ(V, F) ⊗^L_A A/𝔪`.

## Implementation notes

Acyclicity of a complex of sheaves of modules is checked on the sections over the open sets
contained in the members of an open cover
(`Stacks.SheafOfModules.ComplexLocality.acyclic_of_isOpenCover`). Over such an open set `W` the
sections functor is `SheafOfModules.evaluation`, with values in modules over `Γ(V, W)`; it is
additive and carries multiplication by `a ∈ A` on a sheaf of modules to multiplication by the
restriction `Stacks.PuncturedSpectrum.baseHomLE f W a`, which is exactly the hypothesis that
`Stacks.KoszulCone.nonempty_mapHomologicalComplex_koszulTensor_iso` consumes. On a member of the
cover one of the `x_i` restricts to a unit
(`Stacks.PuncturedSpectrum.isUnit_baseHomLE_of_le`), so
`Stacks.KoszulCone.acyclic_koszulTensor_of_isUnit` applies over `Γ(V, W)`.

The `A`-linear structure on sheaves of modules on `V` is
`AlgebraicGeometry.Scheme.linearOfRingHom` applied to `Stacks.LocalCohomology.baseScalars`, the
same one for which `Stacks.LocalCohomology.sectionsOverBase` is `A`-linear; `baseScalars` and
`Stacks.PuncturedSpectrum.baseHom` are the same ring map, which is
`Stacks.PuncturedSpectrum.baseHom_eq_appLE`.

## References

* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
* [Stacks Project, Tag 0629](https://stacks.math.columbia.edu/tag/0629)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.LocalCohomology CochainComplex.DerivedTensor

universe u

namespace Stacks.PuncturedSpectrum

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] {V : Scheme.{u}}

/-- `Stacks.LocalCohomology.baseScalars` is `Stacks.PuncturedSpectrum.baseHom`. -/
theorem baseScalars_eq_baseHom (f : V ⟶ Spec (CommRingCat.of A)) :
    baseScalars A f = baseHom f :=
  (baseHom_eq_appLE f (by simp)).symm

/-- The sections of a sheaf of modules over an open set of `V`, as a functor to modules over the
ring of sections of the structure sheaf there. -/
abbrev sectionsOnOpen (W : V.Opens) :
    SheafOfModules.{u} V.ringCatSheaf ⥤ ModuleCat.{u} Γ(V, W) :=
  SheafOfModules.evaluation.{u} V.ringCatSheaf (op W)

/-- The sections functor over an open set is additive. -/
instance sectionsOnOpen_additive (W : V.Opens) : (sectionsOnOpen (V := V) W).Additive where
  map_add := rfl

/-- **Sections over an open set carry multiplication by `a ∈ A` to multiplication by the
restriction of `a`.** This is the hypothesis of
`Stacks.KoszulCone.nonempty_mapHomologicalComplex_koszulTensor_iso` for the sections functor. -/
theorem sectionsOnOpen_map_smul_id (f : V ⟶ Spec (CommRingCat.of A)) (W : V.Opens) (a : A)
    (M : SheafOfModules.{u} V.ringCatSheaf) :
    letI := Scheme.linearOfRingHom.{u, u} V A (baseScalars A f)
    (sectionsOnOpen W).map (a • 𝟙 M) = baseHomLE f W a • 𝟙 ((sectionsOnOpen W).obj M) := by
  let _ := Scheme.linearOfRingHom.{u, u} V A (baseScalars A f)
  have hhom : (isTerminalTop.from (op W).unop).op = (homOfLE (le_top : W ≤ ⊤)).op :=
    congrArg Quiver.Hom.op (isTerminalTop.hom_ext _ _)
  ext y
  change (a • 𝟙 M).val.app (op W) y = baseHomLE f W a • y
  rw [Stacks.SheafOfModules.smul_val_app V.ringCatSheaf A ⊤ isTerminalTop
    (baseScalars A f) a (𝟙 M) (op W) y, hhom, baseScalars_eq_baseHom]
  rfl

/-- **The Koszul cone complex of a generating family of the maximal ideal is acyclic on a scheme
over the punctured spectrum.** The standard opens of the generators cover `V`, and on each of them
the corresponding generator is invertible. -/
theorem acyclic_koszulTensor_of_puncturedSpectrum [IsLocalRing A]
    {f : V ⟶ Spec (CommRingCat.of A)}
    (g : V ⟶ (LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme))
    (hg : g ≫ (LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f)
    {r : ℕ} (x : Fin r → A) (hspan : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A)
    (J : CochainComplex (SheafOfModules.{u} V.ringCatSheaf) ℤ) :
    letI := Scheme.linearOfRingHom.{u, u} V A (baseScalars A f)
    (Stacks.KoszulCone.koszulTensor r x J).Acyclic := by
  let _ := Scheme.linearOfRingHom.{u, u} V A (baseScalars A f)
  have hcover : TopologicalSpace.IsOpenCover (fun i => V.basicOpen (baseHom f (x i))) :=
    iSup_basicOpen_baseHom_eq_top_puncturedSpectrum g hg x hspan
  refine Stacks.SheafOfModules.ComplexLocality.acyclic_of_isOpenCover _ _ hcover
    fun n i W hW z hz => ?_
  obtain ⟨e⟩ := Stacks.KoszulCone.nonempty_mapHomologicalComplex_koszulTensor_iso
    (sectionsOnOpen W) (baseHomLE f W) (fun a M => sectionsOnOpen_map_smul_id A f W a M) r x J
  have hac := Stacks.KoszulCone.acyclic_koszulTensor_of_isUnit
    (((sectionsOnOpen W).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) r
    (baseHomLE f W ∘ x) ⟨i, isUnit_baseHomLE_of_le f hW⟩
  have hex := (hac n).of_iso e.symm
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff] at hex
  exact hex z hz

/-- **[Stacks, Tag 0ECC], the vanishing of `RΓ(V, F) ⊗^L_A A/𝔪`.** For `A` a regular local ring
and `f : V ⟶ Spec A` factoring through the punctured spectrum, the derived tensor product of the
derived sections of any sheaf of modules on `V` with the residue field of `A` vanishes. -/
theorem isZero_derivedTensor_derivedSectionsOverBase_residueField [IsRegularLocalRing A]
    {f : V ⟶ Spec (CommRingCat.of A)}
    (g : V ⟶ (LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme))
    (hg : g ≫ (LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f)
    (F : SheafOfModules.{u} V.ringCatSheaf) :
    IsZero (((canonicalDerivedTensorProductFunctor A).obj (derivedSectionsOverBase A f F)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A)))) := by
  obtain ⟨r, x, hspan, hreg⟩ := IsRegularLocalRing.exists_isKoszulRegular_span_eq_maximalIdeal A
  obtain ⟨eL⟩ := Koszul.nonempty_Q_obj_seqCochainComplex_iso_single x hreg
  rw [hspan] at eL
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := exists_nonempty_Q_obj_iso_derivedSectionsOverBase A f F
  let _ := Scheme.linearOfRingHom.{u, u} V A (baseScalars A f)
  let _ : Functor.Linear A (sectionsOverBase.{u, u} A f) := sectionsOverBase_linear A f
  set Jsh : CochainComplex (SheafOfModules.{u} V.ringCatSheaf) ℤ :=
    ((InjectiveObject.ι (SheafOfModules.{u} V.ringCatSheaf)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J.obj with hJsh
  have : CochainComplex.IsStrictlyGE Jsh 0 := by
    rwa [hJsh, CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff]
  have : ∀ i, Injective (Jsh.X i) := fun i => inferInstanceAs
    (Injective ((InjectiveObject.ι (SheafOfModules.{u} V.ringCatSheaf)).obj (J.obj.X i)))
  have : ∀ i, Injective ((Stacks.KoszulCone.koszulTensor r x Jsh).X i) :=
    Stacks.KoszulCone.injective_X_koszulTensor Jsh (fun i => inferInstance) r x
  have : CochainComplex.IsStrictlyGE (Stacks.KoszulCone.koszulTensor r x Jsh) (0 - r) :=
    Stacks.KoszulCone.isStrictlyGE_koszulTensor Jsh 0 r x
  have hacM := Stacks.InjectiveModel.acyclic_mapHomologicalComplex_of_acyclic
    (sectionsOverBase.{u, u} A f) (Stacks.KoszulCone.koszulTensor r x Jsh) (0 - r)
    (acyclic_koszulTensor_of_puncturedSpectrum A g hg x hspan Jsh)
  obtain ⟨eG⟩ := Stacks.KoszulCone.nonempty_mapHomologicalComplex_koszulTensor_iso_of_linear
    (sectionsOverBase.{u, u} A f) r x Jsh
  obtain ⟨eT⟩ := Stacks.KoszulCone.nonempty_tensorObj_seqCochainComplex_iso_koszulTensor r x
    (((sectionsOverBase.{u, u} A f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Jsh)
  refine Stacks.DerivedTensor.isZero_derivedTensor_of_acyclic_tensor_kFlat_of_iso A
    (((sectionsOverBase.{u, u} A f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Jsh)
    (Koszul.seqCochainComplex x) (Koszul.kFlat_seqCochainComplex x) eJ eL (fun n => ?_)
  exact (hacM n).of_iso (eT ≪≫ eG.symm).symm

end Stacks.PuncturedSpectrum

end
