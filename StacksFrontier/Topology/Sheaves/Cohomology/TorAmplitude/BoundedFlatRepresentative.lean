module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.MonoidalStructure
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatCokernel
public import StacksFrontier.Topology.Sheaves.Modules.ExtensionByZero.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor amplitude in `[a, b]` is a bounded flat representative

An object of the derived category of `O_X`-modules on a ringed space has Tor amplitude in
`[a, b]` if and only if it is isomorphic to the image of a complex of flat `O_X`-modules which
vanishes in every degree outside `[a, b]`.

## Main definitions

* `Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.structureSheafModule`: the
  structure sheaf of a ringed space, viewed as a module over itself.

## Main results

* `hasTorAmplitude_iff_exists_flat_representative`: Tor amplitude in `[a, b]` is
  equivalent to the existence of a representative which is a complex of flat modules
  concentrated in `[a, b]`.
* `exists_flat_representative_of_hasTorAmplitude`: the direction producing the
  representative.
* `Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_structureSheafModule` and
  `kFlat_single_structureSheafModule`: the structure sheaf is a flat module, and in degree zero
  it is a K-flat complex.
* `Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.derivedTensorUnitIso`: derived
  tensoring with the structure sheaf in degree zero is the identity on `D(O_X)`.

## Implementation notes

The direction from a representative to Tor amplitude is
`Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative`, and is not
redone here.

For the other direction: tensoring with the structure sheaf is the
identity, so Tor amplitude in `[a, b]` already bounds the object itself: it is `IsGE a` and
`IsLE b`. Hence it is the image of a complex which is strictly `LE b`, and
`CochainComplex.propCoresolution.exists_quasiIso_prop` resolves that complex by one which is
termwise flat and still strictly `LE b` — flat modules cover, by Tag 05NI. That resolution `P`
need not vanish below `a`, and the truncation `P.truncGE a` is the required representative:
its terms above `a` are those of `P`, its term in degree `a` is `P.opcycles a`, which is the
cokernel of `d^{a-1}` and is flat by Tag 08CH, and its terms below `a` are zero.

Both the unit laws used -- that `- ⊗_{O_X} O_X` is the identity on modules and that
`Tot(K ⊗_{O_X} O_X[0])` is `K` on complexes -- are read off the monoidal structures of Tags
0FPQ and 0FP8 rather than recomputed: `SheafOfModules.curriedTensor_sheafTensor` and
`SheafOfModules.tensorUnit_sheafTensor` identify the monoidal data of `Mod(O_X)` with the
tensor bifunctor and the structure sheaf, and
`Stacks.Cohomology.MonoidalComplexesOfModules.SymmetricMonoidalComplexes.tensor_eq_total` and
`unit_eq_structureSheaf` do the same for complexes.

The universes of the space, its structure sheaf and its modules coincide, as they already must
for `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`; the derived category's own hom universe
stays independent.

## References

* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 08CH](https://stacks.math.columbia.edu/tag/08CH)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 05NI](https://stacks.math.columbia.edu/tag/05NI)
* [Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry TopologicalSpace
open StrictlyPerfect AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative

universe u d

variable {X : RingedSpace.{u, u}}

/-- The structure sheaf of a ringed space, viewed as a module over itself. It is the unit of
the tensor product of `O_X`-modules. -/
def structureSheafModule (X : RingedSpace.{u, u}) : Modules X :=
  SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)

/-- **Tensoring on the right with the structure sheaf is the identity.** This is the right
unitor of the monoidal structure on `Mod(O_X)` whose tensor product is the sheaf tensor
product and whose unit is the structure sheaf. -/
def tensorStructureSheafIso (X : RingedSpace.{u, u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj (structureSheafModule X) ≅
      𝟭 (Modules X) := by
  letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
  rw [show structureSheafModule X = 𝟙_ (Modules X) from
      (SheafOfModules.tensorUnit_sheafTensor X.sheaf).symm,
    show Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf = curriedTensor (Modules X) from
      (SheafOfModules.curriedTensor_sheafTensor X.sheaf).symm]
  exact MonoidalCategory.rightUnitorNatIso (Modules X)

/-- Flatness is transported along an isomorphism of `O_X`-modules. -/
theorem isFlat_of_iso {M N : Modules X} (e : M ≅ N)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) N :=
  Stacks.SheafOfModules.isFlat_of_exactFunctor_sheafTensorFlip X.sheaf N
    ((exactFunctor _ _).prop_of_iso
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.mapIso e)
      (Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat X.sheaf M hM))

/-- **The structure sheaf is a flat `O_X`-module.** Tensoring with it is the identity
functor. -/
theorem isFlat_structureSheafModule (X : RingedSpace.{u, u}) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (structureSheafModule X) :=
  Stacks.SheafOfModules.isFlat_of_exactFunctor_sheafTensorFlip X.sheaf _
    ((exactFunctor _ _).prop_of_iso (tensorStructureSheafIso X).symm
      (by rw [exactFunctor_iff]; exact ⟨inferInstance, inferInstance⟩))

/-- A zero `O_X`-module is flat: it is the kernel of the identity of the structure sheaf, which
sits in a short exact sequence whose other two terms are the flat structure sheaf. -/
theorem isFlat_kernel_id_structureSheafModule (X : RingedSpace.{u, u}) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (kernel (𝟙 (structureSheafModule X))) :=
  Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact X.sheaf
    (ShortComplex.mk (kernel.ι (𝟙 (structureSheafModule X))) (𝟙 (structureSheafModule X))
      (kernel.condition _))
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
    (isFlat_structureSheafModule X) (isFlat_structureSheafModule X)

/-- **The structure sheaf in degree zero is a K-flat complex.** `Tot(G ⊗_{O_X} O_X[0])` is `G`,
by the right unitor of the monoidal structure on complexes of `O_X`-modules, so it is acyclic
whenever `G` is. -/
theorem kFlat_single_structureSheafModule (X : RingedSpace.{u, u}) :
    KFlat X ((CochainComplex.singleFunctor (Modules X) 0).obj (structureSheafModule X)) := by
  let mono := Stacks.Cohomology.MonoidalComplexes.symmetricMonoidalComplexes X
  let _ := mono.monoidal
  intro G hG
  have eG : ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj G).obj
      ((CochainComplex.singleFunctor (Modules X) 0).obj (structureSheafModule X)) ≅ G := by
    rw [← mono.tensor_eq_total, show (CochainComplex.singleFunctor (Modules X) 0).obj
      (structureSheafModule X) = 𝟙_ (Stacks.Cohomology.MonoidalComplexes.Complexes X) from
      mono.unit_eq_structureSheaf.symm]
    exact MonoidalCategory.rightUnitor G
  rw [HomologicalComplex.acyclic_iff] at hG ⊢
  exact fun i => HomologicalComplex.ExactAt.of_iso (hG i) eG.symm

/-- If `P` is termwise flat and `Coker(d_P^{a-1})` is flat, then `P.truncGE a` is termwise
flat. -/
private theorem isFlat_truncGE_X_of_isFlat_cokernel_d (P : CochainComplex (Modules X) ℤ) (a : ℤ)
    (hP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (P.X i))
    (ha : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (cokernel (P.d (a - 1) a))) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) ((P.truncGE a).X i) := by
  rcases lt_trichotomy i a with hlt | heq | hgt
  · exact isFlat_of_iso
      (IsZero.iso (isZero_kernel_of_mono (𝟙 (structureSheafModule X)))
        ((P.truncGE a).isZero_of_isStrictlyGE a i hlt))
      (isFlat_kernel_id_structureSheafModule X)
  · have e : P.opcycles a ≅ (cokernel (P.d (a - 1) a) : Modules X) :=
      IsColimit.coconePointUniqueUpToIso
        (P.opcyclesIsCokernel (a - 1) a (by simp)) (colimit.isColimit _)
    rw [heq]
    exact isFlat_of_iso (e.symm ≪≫ (P.truncGEXIsoOpcycles a).symm) ha
  · exact isFlat_of_iso (P.truncGEXIso a i hgt).symm (hP i)

section Derived

variable [HasDerivedCategory.{d} (OXMod.{u} X)]

-- `HasDerivedCategory` at the spelling of Stacks 06YU: the type is `OXMod X` by `rfl`, but
-- `structureSheafOfRings` is not reducible, so an instance proved at one spelling does not fire
-- at the other.
attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **Derived tensoring a K-flat complex with the structure sheaf in degree zero is the
identity.** K-flatness makes the derived tensor product the total tensor complex, which the
right unitor identifies with the complex itself. -/
def derivedTensorUnitIsoOfKFlat (K : CochainComplex (Modules X) ℤ) (hK : KFlat X K) :
    ((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Modules X) 0).obj (structureSheafModule X))) ≅
      DerivedCategory.Q.obj K :=
  let mono := Stacks.Cohomology.MonoidalComplexes.symmetricMonoidalComplexes X
  letI := mono.monoidal
  have eK : ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj K).obj
      ((CochainComplex.singleFunctor (Modules X) 0).obj (structureSheafModule X)) ≅ K := by
    rw [← mono.tensor_eq_total, show (CochainComplex.singleFunctor (Modules X) 0).obj
      (structureSheafModule X) = 𝟙_ (Stacks.Cohomology.MonoidalComplexes.Complexes X) from
      mono.unit_eq_structureSheaf.symm]
    exact MonoidalCategory.rightUnitor K
  (Stacks.Cohomology.TorAmplitude.derTensor X).comparison K _ hK
      (kFlat_single_structureSheafModule X) ≪≫
    DerivedCategory.Q.mapIso eK

/-- **Derived tensoring with the structure sheaf in degree zero is the identity on
`D(O_X)`.** Every object is the image of a K-flat complex, by Tag 06YS. -/
def derivedTensorUnitIso (E : DerivedCategory (Modules X)) :
    ((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.obj E).obj
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Modules X) 0).obj (structureSheafModule X))) ≅ E :=
  let K := Classical.choose (exists_kFlatResolution X (DerivedCategory.Q.objPreimage E))
  let hK := Classical.choose_spec (exists_kFlatResolution X (DerivedCategory.Q.objPreimage E))
  let q := Classical.choose hK
  letI : QuasiIso q := (Classical.choose_spec hK).2.2.1
  let eK : DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.mapIso eK).app
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Modules X) 0).obj (structureSheafModule X)))).symm ≪≫
    derivedTensorUnitIsoOfKFlat K (Classical.choose_spec hK).1 ≪≫ eK

/-- **An object of Tor amplitude in `[a, b]` is concentrated in `[a, b]`.** Its derived tensor
product with the structure sheaf is itself. -/
theorem isZero_homology_of_hasTorAmplitude (E : DerivedCategory (Modules X)) (a b : ℤ)
    (hE : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a b) (i : ℤ)
    (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor (Modules X) i).obj E) :=
  (hE (structureSheafModule X) i hi).of_iso
    ((DerivedCategory.homologyFunctor (Modules X) i).mapIso (derivedTensorUnitIso E).symm)

/-- **The direction of Tag 08CI producing the representative.** An object of `D(O_X)` with Tor
amplitude in `[a, b]` is the image of a complex of flat `O_X`-modules vanishing in every degree
outside `[a, b]`.

A flat resolution `P` of a strictly `LE b` representative is truncated at `a`; the only term
that changes is the one in degree `a`, which becomes `Coker(d_P^{a-1})`, flat by Tag 08CH. -/
theorem exists_flat_representative_of_hasTorAmplitude (E : DerivedCategory (Modules X))
    (a b : ℤ) (hab : a ≤ b)
    (hE : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a b) :
    ∃ K : CochainComplex (Modules X) ℤ,
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := X.sheaf) (K.X i)) ∧
      (∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i)) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  classical
  have hEGE : E.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    exact fun i hi => isZero_homology_of_hasTorAmplitude E a b hE i
      (by simp only [Set.mem_Icc]; omega)
  have hELE : E.IsLE b := by
    rw [DerivedCategory.isLE_iff]
    exact fun i hi => isZero_homology_of_hasTorAmplitude E a b hE i
      (by simp only [Set.mem_Icc]; omega)
  obtain ⟨M, hMLE, ⟨eM⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE E b
  let Pflat : ObjectProperty (Modules X) := fun F =>
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) F
  let _ : Pflat.ContainsZero :=
    ⟨⟨kernel (𝟙 (structureSheafModule X)), isZero_kernel_of_mono _,
      isFlat_kernel_id_structureSheafModule X⟩⟩
  have hcover : ∀ F : Modules X, ∃ (G : Modules X) (_ : Pflat G) (f : G ⟶ F), Epi f := by
    intro F
    obtain ⟨G, f, hG, hf⟩ := Stacks.SheafOfModules.exists_epi_from_flat X.sheaf F
    exact ⟨G, hG, f, hf⟩
  obtain ⟨P, f, -, hf, hPflat, hPLE⟩ :=
    (CochainComplex.exists_quasiIso_prop Pflat hcover b).1 M
  let _ : QuasiIso f := hf
  have eP : DerivedCategory.Q.obj P ≅ E := asIso (DerivedCategory.Q.map f) ≪≫ eM.symm
  let _ : P.IsGE a :=
    (DerivedCategory.isGE_Q_obj_iff P a).1 (DerivedCategory.TStructure.t.isGE_of_iso eP.symm a)
  have hPamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      (DerivedCategory.Q.obj P) a b := fun F i hi =>
    (hE F i hi).of_iso ((DerivedCategory.homologyFunctor (Modules X) i).mapIso
      (((Stacks.Cohomology.TorAmplitude.derTensor X).tensor.mapIso eP).app
        ((DerivedCategory.singleFunctor (Modules X) 0).obj F)))
  have hCokerFlat := Stacks.Cohomology.TorAmplitude.FlatCokernel.isFlat_cokernel_of_hasTorAmplitude
    P a b ⟨b, hPLE⟩ hPflat hPamp
  have hTruncLE : (P.truncGE a).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => (P.isZero_of_isStrictlyLE b i hi).of_iso (P.truncGEXIso a i (by omega))
  refine ⟨P.truncGE a, isFlat_truncGE_X_of_isFlat_cokernel_d P a hPflat hCokerFlat,
    fun i hi => ?_, ⟨(asIso (DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫ eP⟩⟩
  obtain hlt | hgt : i < a ∨ b < i := by simpa only [Set.mem_Icc, not_and_or, not_le] using hi
  · exact (P.truncGE a).isZero_of_isStrictlyGE a i hlt
  · exact (P.truncGE a).isZero_of_isStrictlyLE b i hgt

/-- An object of `D(O_X)` has Tor amplitude in `[a, b]` exactly when some complex
of flat `O_X`-modules vanishing in every degree outside `[a, b]` represents it. -/
@[stacks 08CI, sga "4 XVII 4.1.9" "(i), (iii)", sga "6 I 5.1" "ringed space case"]
theorem hasTorAmplitude_iff_exists_flat_representative (E : DerivedCategory (Modules X))
    (a b : ℤ) (hab : a ≤ b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X E a b ↔
      ∃ K : CochainComplex (Modules X) ℤ,
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
          (O := X.sheaf) (K.X i)) ∧
        (∀ i : ℤ, i ∉ Set.Icc a b → IsZero (K.X i)) ∧
        Nonempty (DerivedCategory.Q.obj K ≅ E) where
  mp hE := exists_flat_representative_of_hasTorAmplitude E a b hab hE
  mpr := fun ⟨K, hKflat, hKzero, ⟨eK⟩⟩ =>
    Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative
      E a b K hKflat hKzero eK

end Derived

end Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative

end
