module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.PerfectFibreBands
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChange

/-!
# Inhabiting the derived-tensor comparisons on a fibre product

`AlgebraicGeometry.FibreTensorComparisons f g` bundles the three general comparisons for the
derived tensor product on `D(𝒪_{X ×_S Y})` that the reflection step of [Stacks, Tag 0FZ9]
consumes, together with a derived tensor product on each stalk ring. This file builds three of
its four fields outright, so that the bundle is carried only by the derived form of
[Stacks, Tag 01CB] — the one genuinely missing comparison.

The stalk rings get the canonical derived tensor product of [Stacks, Tag 0BYI]. Quasi-coherence
of the cohomology of a derived tensor product is [Stacks, Tag 08DX] part (1), which holds with
no hypothesis on the scheme. The support statement is proved stalkwise, exactly as the Tor
sheaves of [Stacks, Tag 0AZT] are: write both factors as classes of K-flat complexes, so that
their derived tensor product is a total tensor complex, and take stalks, which carries a total
tensor complex to the total tensor complex of the stalks ([Stacks, Tag 01CB] at the level of
complexes). Away from `pr_1^{-1}Z` the stalk of `pr_1^*𝓕` vanishes, hence so does the complex of
stalks of its K-flat representative, and the total tensor complex of an acyclic complex with a
K-flat one is acyclic.

## Main definitions

* `AlgebraicGeometry.fibreRingTensor`: the canonical derived tensor product on
  `D(𝒪_{X ×_S Y, z})` at each point `z`.
* `AlgebraicGeometry.stalkHomologyDerivedTensorIso`: the stalk of a cohomology sheaf of a derived
  tensor product, read as a cohomology module of the complex of stalks of a total tensor complex.
* `AlgebraicGeometry.fibreTensorComparisonsOfStalkIso` and
  `AlgebraicGeometry.fibreTensorComparisons`: the bundle `FibreTensorComparisons f g`, assembled
  from the derived form of [Stacks, Tag 01CB] alone.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_singleFunctor_obj`: a quasi-coherent module placed
  in degree `0` has quasi-coherent cohomology sheaves.
* `AlgebraicGeometry.cohomologySupportedOn_fourierMukaiTensor_singleFunctor_pullback`: tensoring
  with the `pr_1`-pullback of a module supported in `Z`, placed in degree `0`, gives an object
  whose cohomology is supported over `pr_1^{-1}Z`.

## Implementation notes

*The model of the derived categories.* Everything is read at
`CategoryTheory.HasDerivedCategory.standard`, the model `AlgebraicGeometry.fourierMukai` and
`AlgebraicGeometry.FibreTensorComparisons` are stated at; the priority of the local instance
selects it over the locally small model arriving with the imports. For the same reason the
derived tensor product used here is `AlgebraicGeometry.TorFormula.derivedTensor`, which is that
model's reading of [Stacks, Tag 06YU], and not `Stacks.Duality.derivedTensor`.

*Why the stalk comparison is carried.* The derived form of [Stacks, Tag 01CB] is available in
this repository only in the underived shape `Stacks.SheafOfModules.KFlatStalkCriterion`
`.stalkTensorComplexIso`, over the `RingCat`-valued stalk of the ring sheaf, whereas
`CochainComplex.DerivedTensor.DerivedTensorProduct` is stated over the local ring `𝒪_{X ×_S Y,z}`
and the two stalk rings differ by `AlgebraicGeometry.ringCatStalkRingEquiv`. Transporting a
tensor product of complexes along that ring isomorphism needs restriction of scalars along a ring
isomorphism to be monoidal, which the repository does not have — only the corresponding transport
of K-flatness, `AlgebraicGeometry.kFlat_modulesStalkFunctor`.

**That is out of date.** The transport does exist, as
`CochainComplex.KFlatBifunctor.restrictScalarsDerivedTensorObjIso`, and
`AlgebraicGeometry.derivedStalkFibreTensorIso` of
`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/FibreTensorStalkInstance.lean` discharges the
carried comparison with it, so `AlgebraicGeometry.fibreTensorComparisonsOfPullback` of that file
is an unconditional inhabitant of `AlgebraicGeometry.FibreTensorComparisons` for a fibre product
of schemes. The shape of the carried field is still as described next, and that is still why it
is a field rather than a hypothesis of each statement that uses it:
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.hasTorAmplitudeIn_iff_forall_stalk`
and of `AlgebraicGeometry.isZero_homology_derivedStalk_of_isZero_homology_sheafTensor`: quantified
over the point and over both of its arguments, mentioning no vanishing and no particular complex.

*Why the support statement needs no such comparison.* It lives entirely on the `RingCat`-valued
side: `AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff` identifies the vanishing that
`Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn` asks for with the vanishing of
the stalk over that ring, which is the ring `stalkTensorComplexIso` is stated over.

## References

* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The derived tensor product on the stalk rings -/

/-- The canonical derived tensor product of [Stacks, Tag 0BYI] on `D(𝒪_{X ×_S Y, z})`. -/
def fibreRingTensor {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : ↥(Limits.pullback f g)) :
    CochainComplex.DerivedTensor.DerivedTensorProduct
      ((Limits.pullback f g).presheaf.stalk z) :=
  CochainComplex.DerivedTensor.canonicalDerivedTensorProduct _

/-! ### Quasi-coherence of a module placed in degree zero -/

/-- **A quasi-coherent module placed in degree `0` has quasi-coherent cohomology sheaves**: the
sheaf in degree `0` is the module itself, and the ones in the other degrees vanish. -/
theorem isQuasicoherent_homology_singleFunctor_obj (W : Scheme.{u}) (M : W.Modules)
    (hM : M.IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((DerivedCategory.singleFunctor W.Modules 0).obj M)).IsQuasicoherent := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact isQuasicoherent_of_isZero W _
      (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor W.Modules 0).obj M) 0 i hi)
  · exact (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso W.Modules 0).app M).symm hM
  · exact isQuasicoherent_of_isZero W _
      (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor W.Modules 0).obj M) 0 i hi)

/-! ### The stalks of the cohomology of a derived tensor product -/

/-- **The stalk of a cohomology sheaf of a derived tensor product, computed from K-flat
representatives.** If `P` and `Q` are K-flat complexes whose classes in `D(𝒪_W)` are `A` and `B`,
then the stalk at `w` of `H^i(A ⊗ᴸ_{𝒪_W} B)` is the `i`-th cohomology module of the complex of
stalks of `Tot(P ⊗_{𝒪_W} Q)`. -/
def stalkHomologyDerivedTensorIso (W : Scheme.{u}) (A B : DerivedCategory W.Modules) (i : ℤ)
    (w : W) (P Q : Stacks.Duality.TensorComplex W)
    (hP : Stacks.Duality.KFlatComplex P) (hQ : Stacks.Duality.KFlatComplex Q)
    (eP : (DerivedCategory.Q.obj P : DerivedCategory W.Modules) ≅ A)
    (eQ : (DerivedCategory.Q.obj Q : DerivedCategory W.Modules) ≅ B) :
    (Scheme.Modules.stalkFunctor W w).obj
        ((DerivedCategory.homologyFunctor W.Modules i).obj
          (((TorFormula.derivedTensor W).obj A).obj B)) ≅
      (AlgebraicGeometry.SheafOfModules.stalkComplex W.sheaf w
        (Stacks.Duality.totalTensorComplex P Q)).homology i :=
  let O := Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} W.sheaf
  let E := ((TorFormula.derivedTensor W).obj A).obj B
  let eG : (DerivedCategory.Q.obj (Stacks.Duality.totalTensorComplex P Q) :
      DerivedCategory W.Modules) ≅ E :=
    ((Stacks.Cohomology.TorAmplitude.derTensor W.toRingedSpace).comparison P Q hP hQ).symm ≪≫
      ((TorFormula.derivedTensor W).mapIso eP).app _ ≪≫
      ((TorFormula.derivedTensor W).obj A).mapIso eQ
  ((AlgebraicGeometry.SheafOfModules.derivedStalkHomologyIso O w i).app E).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor O w).mapIso eG.symm) ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctorFactors O w).app
        (Stacks.Duality.totalTensorComplex P Q)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app
      (AlgebraicGeometry.SheafOfModules.stalkComplex W.sheaf w
        (Stacks.Duality.totalTensorComplex P Q))

/-! ### The support of a derived tensor product with a pullback -/

section Supported

open RingedSpaceModuleAdjunction
open Stacks.Cohomology.PushforwardRestriction (CohomologySupportedOn)

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The stalk of the pullback of a module vanishes wherever the stalk of the module does**, the
stalk of `f^*𝓕` at `x` being the base change of the stalk of `𝓕` at `f x` ([Stacks, Tag 0098]). -/
theorem isZero_stalk_pullback_of_isZero_stalk {W : Scheme.{u}} (h : W ⟶ X) (F : X.Modules)
    (w : W) (hF : IsZero ((Scheme.Modules.stalkFunctor X (h.base w)).obj F)) :
    IsZero ((Scheme.Modules.stalkFunctor W w).obj ((Scheme.Modules.pullback h).obj F)) :=
  (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ w _).2
    (Stacks.Cohomology.ExtensionByZeroBaseChange.isZero_stalk_modulePullback_obj
      h.toLRSHom.toShHom F w
      ((AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ (h.base w) _).1 hF))

/-- **Tensoring with the `pr₁`-pullback of a module supported in `Z`, placed in degree `0`, gives
an object whose cohomology is supported over `pr₁⁻¹ Z`.** Both factors are replaced by K-flat
representatives, on which the derived tensor product is the total tensor complex; outside
`pr₁⁻¹ Z` the complex of stalks of the representative of the pullback is acyclic, and the total
tensor complex of an acyclic complex with a K-flat one is acyclic. -/
theorem cohomologySupportedOn_fourierMukaiTensor_singleFunctor_pullback
    (E : DerivedCategory (Limits.pullback f g).Modules) (F : X.Modules) (Z : Set ↥X)
    (hF : SheafOfModules.supp F ⊆ Z) :
    CohomologySupportedOn (structureSheafRing (Limits.pullback f g).toRingedSpace)
      ((Limits.pullback.fst f g).base ⁻¹' Z)
      ((fourierMukaiTensor f g E).obj
        ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F))) := by
  intro i w hw
  let _stalkCommRing :=
    StacksDraft.StalkTensor.commRing_stalk_ringSheaf (Limits.pullback f g).sheaf w
  set M := (Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F with hM
  have hMw : IsZero ((Scheme.Modules.stalkFunctor (Limits.pullback f g) w).obj M) :=
    isZero_stalk_pullback_of_isZero_stalk (Limits.pullback.fst f g) F w
      ((Scheme.Modules.notMem_supp_iff_isZero_stalk F _).1 fun hmem => hw (hF hmem))
  obtain ⟨P, hP, ⟨eP⟩⟩ := TorFormula.exists_kFlatComplex_iso (Limits.pullback f g)
    ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj M)
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := TorFormula.exists_kFlatComplex_iso (Limits.pullback f g) E
  have hac : (AlgebraicGeometry.SheafOfModules.stalkComplex (Limits.pullback f g).sheaf w
      (Stacks.Duality.totalTensorComplex P Q)).Acyclic :=
    HomologicalComplex.Acyclic.of_iso
      (Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorComplexIso
        (Limits.pullback f g).sheaf w P Q).symm
      ((Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise
          (Limits.pullback f g).sheaf Q).mp hQ w
        (AlgebraicGeometry.SheafOfModules.stalkComplex (Limits.pullback f g).sheaf w P)
        (TorFormula.acyclic_stalkComplex_of_isZero_stalk (Limits.pullback f g) M w P eP hMw))
  refine (AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff _ w _).1 ?_
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (hac i)).of_iso
    (stalkHomologyDerivedTensorIso (Limits.pullback f g)
      ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj M) E i w P Q hP hQ
      eP eQ)

end Supported

/-! ### The bundle of comparisons -/

section Bundle

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The comparisons of [Stacks, Tag 0FZ9] for `X ×_S Y`, carried by the derived form of
[Stacks, Tag 01CB] alone.** Given a derived tensor product on each stalk ring and the
isomorphism identifying the stalk of a sheaf-level derived tensor product with the stalk-level
one, the quasi-coherence and support fields of `AlgebraicGeometry.FibreTensorComparisons` are
supplied by [Stacks, Tag 08DX] part (1) and by the stalkwise computation of the derived tensor
product on K-flat representatives. -/
def fibreTensorComparisonsOfStalkIso
    (𝒯 : ∀ z : ↥(Limits.pullback f g),
      CochainComplex.DerivedTensor.DerivedTensorProduct
        ((Limits.pullback f g).presheaf.stalk z))
    (hstalk : ∀ (z : ↥(Limits.pullback f g))
      (E F : DerivedCategory (Limits.pullback f g).Modules),
      (derivedStalkFunctor z).obj ((fourierMukaiTensor f g E).obj F) ≅
        ((𝒯 z).tensor.obj ((derivedStalkFunctor z).obj E)).obj
          ((derivedStalkFunctor z).obj F)) :
    FibreTensorComparisons f g where
  ringTensor := 𝒯
  stalk := hstalk
  quasicoherent E M hM hE j :=
    TorFormula.isQuasicoherent_homology_derivedTensor (Limits.pullback f g)
      ((DerivedCategory.singleFunctor (Limits.pullback f g).Modules 0).obj M) E
      (isQuasicoherent_homology_singleFunctor_obj (Limits.pullback f g) M hM) hE j
  supported E F Z hF :=
    cohomologySupportedOn_fourierMukaiTensor_singleFunctor_pullback f g E F Z hF

/-- **The comparisons of [Stacks, Tag 0FZ9] for `X ×_S Y`** with the canonical derived tensor
product on each stalk ring, so that the derived form of [Stacks, Tag 01CB] is the only datum
carried. -/
def fibreTensorComparisons
    (hstalk : ∀ (z : ↥(Limits.pullback f g))
      (E F : DerivedCategory (Limits.pullback f g).Modules),
      (derivedStalkFunctor z).obj ((fourierMukaiTensor f g E).obj F) ≅
        ((fibreRingTensor f g z).tensor.obj ((derivedStalkFunctor z).obj E)).obj
          ((derivedStalkFunctor z).obj F)) :
    FibreTensorComparisons f g :=
  fibreTensorComparisonsOfStalkIso f g (fibreRingTensor f g) hstalk

/-- **The comparisons of [Stacks, Tag 0FZ9] when `X` has no points.** The fibre product then has
no points either, so the two pointwise fields are vacuous and the other two are the general
constructions above. -/
def fibreTensorComparisonsOfIsEmpty [IsEmpty ↥X] : FibreTensorComparisons f g :=
  fibreTensorComparisons f g fun z _ _ =>
    (IsEmpty.false ((Limits.pullback.fst f g).base z)).elim

/-- `AlgebraicGeometry.FibreTensorComparisons` is an inhabited type: the empty scheme over any
base, with any second factor, carries the bundle. -/
def fibreTensorComparisonsEmpty (S Y : Scheme.{u}) (g : Y ⟶ S) :
    FibreTensorComparisons (Scheme.emptyTo S) g :=
  fibreTensorComparisonsOfIsEmpty (Scheme.emptyTo S) g

end Bundle

end AlgebraicGeometry

end
