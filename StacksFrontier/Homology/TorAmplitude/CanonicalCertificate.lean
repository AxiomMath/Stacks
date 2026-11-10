module

public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.Composition
public import StacksFrontier.Homology.TorAmplitude.ExtendScalars
public import StacksFrontier.Homology.TorAmplitude.Local
public import StacksFrontier.Homology.TorAmplitude.Module
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical certificate of the canonical derived tensor product

Let `R` be a commutative ring. For the canonical derived tensor product
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R` and every `R`-module `M`, this file
constructs the natural comparison map from `- ⊗ᴸ M[0]` to termwise tensoring by `M`, and shows
that it exhibits `- ⊗ᴸ M[0]` as the total left derived functor of `- ⊗ M`. Tor amplitude, finite
Tor dimension and their characterizations by flat representatives are then stated at this derived
tensor product.

## Main definitions

* `StacksDraft.TorAmplitude.canonicalTensorComparison`: for every `R`-module `M`, the natural
  comparison map from `- ⊗ᴸ M[0]`, precomposed with the localization `Q`, to termwise tensoring
  by `M` followed by `Q`.
* `StacksDraft.TorAmplitude.HasTorAmplitudeCanonical`,
  `StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical`,
  `StacksDraft.TorAmplitude.HasTorDimensionLECanonical`,
  `StacksDraft.TorAmplitude.ModuleHasFiniteTorDimensionCanonical`: Tor amplitude, finite Tor
  dimension, Tor dimension at most `d` and finite Tor dimension of a module, at the canonical
  derived tensor product.
* `StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring`: the canonical derived tensor
  product as a `CertifiedDerivedTensoring`.

## Main results

* `StacksDraft.TorAmplitude.isLeftDerivedFunctor_canonicalTensorComparison` and its
  `∀`-form `StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived`: `- ⊗ᴸ M[0]` is the total
  left derived functor of termwise tensoring by `M`, with counit `canonicalTensorComparison`.
* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonical_iff`: the translation into the derived
  tensoring datum of Stacks 0655 determined by the canonical bifunctor.
* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative`: Tor amplitude in
  `[a, b]` is representability by a complex of flat modules in degrees `[a, b]`.
* `StacksDraft.TorAmplitude.hasTorDimensionLECanonical_iff_hasFlatRepresentative`: Tor dimension
  at most `d` is the existence of a flat resolution of length `d`.
* `StacksDraft.TorAmplitude.hasTorDimensionLECanonical_extendScalars_of_flat`: Tor dimension at
  most `d` is preserved by flat base change.
* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_of_faithfullyFlat`: Tor amplitude descends
  along a faithfully flat ring map.

## References

* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 0655](https://stacks.math.columbia.edu/tag/0655)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.MonoidalCategory HomologicalComplex
  CochainComplex.DerivedTensor CochainComplex.DerivedTensor.KFlatDerived

namespace StacksDraft.TorAmplitude

universe u v w

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-! ### Tensoring with a K-flat complex, descended to the derived category -/

/-- Tensoring on the right with a K-flat complex inverts quasi-isomorphisms, so it descends
along the localization `Q`. -/
private lemma tensorRight_inverts (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
      (tensorRight P ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : QuasiIso f := hf
  have : QuasiIso ((tensorRight P).map f) := quasiIso_tensorRight_map hP f
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((tensorRight P).map f)))

/-- The descent of `tensorRight P`, for `P` K-flat, to an endofunctor of `D(R)`. -/
private noncomputable abbrev liftedTensor (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.KFlat) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (tensorRight P ⋙ DerivedCategory.Q) (tensorRight_inverts P hP)
    DerivedCategory.Q

/-- The isomorphism `Q ⋙ liftedTensor P ≅ tensorRight P ⋙ Q`. -/
private noncomputable def liftedTensorFactors (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.KFlat) :
    DerivedCategory.Q ⋙ liftedTensor P hP ≅ tensorRight P ⋙ DerivedCategory.Q :=
  Localization.fac _ (tensorRight_inverts P hP) DerivedCategory.Q

/-- On the K-flat objects of the homotopy category, the derived tensor product with `Q P` is the
descent of the ordinary tensor product with `P`. -/
private noncomputable def tensorFlatComparison (T : DerivedTensorProduct R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) :
    kFlatHomotopyQ R ⋙ T.tensor.flip.obj (DerivedCategory.Q.obj P) ≅
      kFlatHomotopyQ R ⋙ liftedTensor P hP := by
  refine NatIso.ofComponents (fun X =>
    (T.tensor.flip.obj (DerivedCategory.Q.obj P)).mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app X.obj.as) ≪≫
    T.comparison X.obj.as P X.property hP ≪≫
    ((liftedTensorFactors P hP).app X.obj.as).symm ≪≫
    (liftedTensor P hP).mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app X.obj.as).symm) ?_
  intro X Y f
  obtain ⟨g, hg⟩ : ∃ g : X.obj.as ⟶ Y.obj.as,
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map g = f.hom :=
    ⟨f.hom.out, HomotopyCategory.quotient_map_out _⟩
  have hcmp : (T.tensor.map (DerivedCategory.Q.map g)).app (DerivedCategory.Q.obj P) ≫
      (T.comparison Y.obj.as P Y.property hP).hom =
      (T.comparison X.obj.as P X.property hP).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom g (𝟙 P)) := by
    have h := T.comparison_naturality g (𝟙 P) X.property Y.property hP hP
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality (C := ModuleCat.{u} R) g
  have key : (T.tensor.flip.obj (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map g) ≫
      (T.comparison Y.obj.as P Y.property hP).hom ≫
        (liftedTensorFactors P hP).inv.app Y.obj.as =
      (T.comparison X.obj.as P X.property hP).hom ≫
        (liftedTensorFactors P hP).inv.app X.obj.as ≫
          (liftedTensor P hP).map (DerivedCategory.Q.map g) := by
    have h1 : (T.tensor.flip.obj (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map g)
        = (T.tensor.map (DerivedCategory.Q.map g)).app (DerivedCategory.Q.obj P) := rfl
    rw [h1, reassoc_of% hcmp]
    have h2 : (tensorRight P).map g = HomologicalComplex.tensorHom g (𝟙 P) := rfl
    rw [← h2]
    exact congrArg (fun z => (T.comparison X.obj.as P X.property hP).hom ≫ z)
      ((liftedTensorFactors P hP).inv.naturality g)
  have hqi := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.naturality g
  dsimp only [Functor.comp_map] at hqi
  dsimp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, ObjectProperty.ι_map]
  rw [← hg, ← Functor.map_comp_assoc, hq, Functor.map_comp_assoc, reassoc_of% key]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← hqi]

/-! ### The comparison map of a certified bifunctor at a module in degree zero -/

/-- The isomorphism of `- ⊗ᴸ Q P` with the descent `liftedTensor P` of `- ⊗ P` on the whole
derived category, restricting to `tensorFlatComparison` on the K-flat objects. -/
private noncomputable def tensorFlatIso (T : DerivedTensorProduct R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) :
    T.tensor.flip.obj (DerivedCategory.Q.obj P) ≅ liftedTensor P hP :=
  letI := kFlatHomotopyQ_isLocalization R
  (Localization.fullyFaithfulWhiskeringLeft (kFlatHomotopyQ R) (kFlatHomotopyQuasiIso R)
    (DerivedCategory (ModuleCat.{u} R))).preimageIso (tensorFlatComparison T P hP)

/-- There is a K-flat complex `P` with a quasi-isomorphism `P ⟶ M[0]`. -/
private lemma exists_projRes (M : ModuleCat.{u} R) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (π : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M),
      P.KFlat ∧ QuasiIso π := by
  obtain ⟨P, m, π, hLE, hproj, hπ⟩ := exists_projective_resolution
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) 0
  have := hLE
  exact ⟨P, π, kFlat_of_isStrictlyLE_projective P m hproj, hπ⟩

/-- The chosen bounded above projective resolution of the module `M`. -/
private noncomputable def projRes (M : ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (exists_projRes M).choose

/-- The augmentation `projRes M ⟶ M[0]`. -/
private noncomputable def projResπ (M : ModuleCat.{u} R) :
    projRes M ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M :=
  (exists_projRes M).choose_spec.choose

private lemma projRes_kFlat (M : ModuleCat.{u} R) : (projRes M).KFlat :=
  (exists_projRes M).choose_spec.choose_spec.1

private instance quasiIso_projResπ (M : ModuleCat.{u} R) : QuasiIso (projResπ M) :=
  (exists_projRes M).choose_spec.choose_spec.2

/-- The derived tensor product with `M[0]` is computed, on a representative complex, by the
ordinary tensor product with the chosen projective resolution of `M`. -/
private noncomputable def tensorModuleFactors (T : DerivedTensorProduct R)
    (M : ModuleCat.{u} R) :
    DerivedCategory.Q ⋙ T.tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
      tensorRight (projRes M) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (T.tensor.flip.mapIso (asIso (DerivedCategory.Q.map (projResπ M)))).symm ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q (tensorFlatIso T _ (projRes_kFlat M)) ≪≫
    liftedTensorFactors _ (projRes_kFlat M)

/-- The comparison map of a certified derived tensor product at the module `M` placed in degree
zero, from `- ⊗ᴸ M[0]` read through `Q` to termwise tensoring by `M` followed by `Q`. -/
private noncomputable def tensorModuleComparison (T : DerivedTensorProduct R)
    (M : ModuleCat.{u} R) :
    DerivedCategory.Q ⋙ T.tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (tensorModuleFactors T M).hom ≫
    Functor.whiskerRight
      ((curriedTensor (CochainComplex (ModuleCat.{u} R) ℤ)).flip.map (projResπ M))
      DerivedCategory.Q ≫
    Functor.whiskerRight (termwiseTensorSingleIso M).inv DerivedCategory.Q

/-- At a K-flat complex the comparison map is invertible. -/
private lemma tensorModuleComparison_isIso (T : DerivedTensorProduct R)
    (M : ModuleCat.{u} R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) :
    IsIso ((tensorModuleComparison T M).app K) := by
  have : QuasiIso ((tensorLeft K).map (projResπ M)) :=
    quasiIso_tensorLeft_map K hK (projResπ M)
  change IsIso ((tensorModuleFactors T M).hom.app K ≫
    DerivedCategory.Q.map ((tensorLeft K).map (projResπ M)) ≫
      (Functor.whiskerRight (termwiseTensorSingleIso M).inv DerivedCategory.Q).app K)
  infer_instance

/-! ### The canonical certificate -/

/-- For an `R`-module `M`, the natural transformation from the derived tensor product with `M[0]`,
read on complexes through the localization `Q`, to termwise tensoring by `M` followed by `Q`, for
the canonical derived tensor product of Stacks 0BYI. -/
public noncomputable def canonicalTensorComparison (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) :
    DerivedCategory.Q ⋙ (canonicalDerivedTensorProduct R).tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  tensorModuleComparison (canonicalDerivedTensorProduct R) M

/-- Tensoring with `M[0]` in the canonical derived tensor product of Stacks 0BYI is the total
left derived functor of termwise tensoring by `M`, with counit `canonicalTensorComparison`. -/
public instance isLeftDerivedFunctor_canonicalTensorComparison (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) :
    ((canonicalDerivedTensorProduct R).tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
      (canonicalTensorComparison R M)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  isLeftDerivedFunctor_of_isIso_on_kFlat.{u, u} _ (termwiseTensorHomotopy M)
    (quotientCompTermwiseTensorIso M) _ (canonicalTensorComparison R M)
    (fun K hK => tensorModuleComparison_isIso (canonicalDerivedTensorProduct R) M K hK)

/-- For every `R`-module `M`, tensoring with `M[0]` in the canonical derived tensor product is
the total left derived functor of termwise tensoring by `M`, with counit
`canonicalTensorComparison R M`. -/
public lemma canonicalTensorIsLeftDerived (R : Type u) [CommRing R] :
    ∀ M : ModuleCat.{u} R,
      ((canonicalDerivedTensorProduct R).tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
        (canonicalTensorComparison R M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  fun M => isLeftDerivedFunctor_canonicalTensorComparison R M

/-- Tor amplitude in `[a, b]`, Stacks 0652 (1), at the canonical derived tensor product. -/
public def HasTorAmplitudeCanonical (R : Type u) [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) : Prop :=
  HasTorAmplitude (canonicalDerivedTensorProduct R).tensor (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R) K a b

/-- Finite Tor dimension, Stacks 0652 (2), at the canonical derived tensor product. -/
public def HasFiniteTorDimensionCanonical (R : Type u) [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  HasFiniteTorDimension (canonicalDerivedTensorProduct R).tensor (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R) K

/-- Finite Tor dimension at the canonical derived tensor product is Tor amplitude in some
interval. -/
public theorem hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical
    (R : Type u) [CommRing R] (K : DerivedCategory (ModuleCat.{u} R)) :
    HasFiniteTorDimensionCanonical R K ↔ ∃ a b : ℤ, HasTorAmplitudeCanonical R K a b :=
  Iff.rfl

/-- Tor dimension at most `d` of a module, Stacks 0652 (3), at the canonical derived tensor
product. -/
public def HasTorDimensionLECanonical (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) (d : ℤ) : Prop :=
  HasTorDimensionLE (canonicalDerivedTensorProduct R).tensor (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R) M d

/-- Finite Tor dimension of a module, Stacks 0652 (4), at the canonical derived tensor
product. -/
public def ModuleHasFiniteTorDimensionCanonical (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) : Prop :=
  ModuleHasFiniteTorDimension (canonicalDerivedTensorProduct R).tensor
    (canonicalTensorComparison R) (canonicalTensorIsLeftDerived R) M

/-- Tor amplitude against the derived tensoring datum of Stacks 0655 determined by the canonical
derived tensor product is the canonical Tor amplitude of Stacks 0652. -/
public theorem hasTorAmplitudeIn_canonical_iff (R : Type u) [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn
        (derivedTensoringOfCertified (canonicalDerivedTensorProduct R)) K a b ↔
      HasTorAmplitudeCanonical R K a b :=
  hasTorAmplitudeIn_iff_hasTorAmplitude (canonicalDerivedTensorProduct R)
    (canonicalTensorComparison R) (canonicalTensorIsLeftDerived R) K a b

/-- The canonical derived tensor product of Stacks 0BYI, as a `CertifiedDerivedTensoring`. -/
public noncomputable def canonicalCertifiedDerivedTensoring (R : Type u) [CommRing R] :
    CertifiedDerivedTensoring.{u, u} R where
  tensor := (canonicalDerivedTensorProduct R).tensor
  comparison := canonicalTensorComparison R
  isLeftDerived := canonicalTensorIsLeftDerived R

/-- Tor amplitude read off `canonicalCertifiedDerivedTensoring` is the canonical Tor
amplitude. -/
public theorem hasTorAmplitudeIn_canonicalCertified_iff (R : Type u) [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    (canonicalCertifiedDerivedTensoring R).HasTorAmplitudeIn K a b ↔
      HasTorAmplitudeCanonical R K a b := Iff.rfl

/-! ### The flat-resolution results at the canonical derived tensor product -/

/-- An object `K` of `D(R)` has Tor amplitude in `[a, b]` — at the canonical derived tensor
product of Stacks 0BYI — if and only if it is represented by a complex of flat
`R`-modules concentrated in degrees `[a, b]`. -/
@[stacks 0654, sga "6 I 5.1" "affine case", sga "4 XVII 4.1.9" "over a ring, (i)<=>(iii)"]
public theorem hasTorAmplitudeCanonical_iff_hasFlatRepresentative (R : Type u) [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    HasTorAmplitudeCanonical R K a b ↔ HasFlatRepresentative K a b :=
  hasTorAmplitude_iff_hasFlatRepresentative (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R) K a b

/-- An `R`-module `M` has Tor dimension at most `d` — at the canonical derived
tensor product — if and only if it admits a flat resolution of length `d`, that is, a complex of
flat modules concentrated in degrees `[-d, 0]` representing `M[0]`.  In particular `M` has Tor
dimension at most `0` if and only if `M` is flat. -/
@[stacks 066F,
  sga "4 XVII 4.1.9" "module over a ring",
  sga "6 I 5.4" "commutative ring",
  sga "6 I 5.1" "module over a ring"]
public theorem hasTorDimensionLECanonical_iff_hasFlatRepresentative (R : Type u) [CommRing R]
    (M : ModuleCat.{u} R) (d : ℕ) :
    (HasTorDimensionLECanonical R M d ↔
        HasFlatRepresentative
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) (-(d : ℤ)) 0) ∧
      (HasTorAmplitudeCanonical R
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) 0 0 ↔
        Module.Flat R M) :=
  hasTorDimensionLE_iff_hasFlatRepresentative (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R) M d

/-- Let `f : A →+* B` be a flat homomorphism of commutative rings.  If the
`A`-module `M` has Tor dimension at most `d`, then the `B`-module `B ⊗_A M` has Tor dimension at
most `d`.  Both Tor dimensions are read at the canonical derived tensor product of the ring in
question. -/
@[stacks 066M]
public theorem hasTorDimensionLECanonical_extendScalars_of_flat {A B : Type u} [CommRing A]
    [CommRing B] (f : A →+* B) (hf : f.Flat) (M : ModuleCat.{u} A) (d : ℕ)
    (hM : HasTorDimensionLECanonical A M d) :
    HasTorDimensionLECanonical B ((ModuleCat.extendScalars.{u, u, u} f).obj M) d :=
  hasTorDimensionLE_extendScalars_of_flat f hf (canonicalTensorComparison A)
    (canonicalTensorIsLeftDerived A) (canonicalTensorComparison B)
    (canonicalTensorIsLeftDerived B) M d hM

/-- Tor amplitude descends along a faithfully flat ring map `f : R →+* S`: if the base change of
`K` along `f` has Tor amplitude in `[a, b]`, then so does `K`. Both sides are read at the
canonical derived tensor products of the two rings lifted by `ULift` into the universe of the
modules, and the base change is extension of scalars along the lifted ring map. -/
@[stacks 068S]
public theorem hasTorAmplitudeCanonical_of_faithfullyFlat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{max u v w} (ULift.{max v w} R)) ℤ) (a b : ℤ)
    (h : HasTorAmplitudeCanonical (ULift.{max u w} S)
      (DerivedCategory.Q.obj
        ((CochainComplex.extendScalars (f.ulift.{max v w, max u w})).obj K)) a b) :
    HasTorAmplitudeCanonical (ULift.{max v w} R) (DerivedCategory.Q.obj K) a b :=
  hasTorAmplitude_of_faithfullyFlat f hf
    (canonicalTensorComparison (ULift.{max v w} R))
    (canonicalTensorIsLeftDerived (ULift.{max v w} R))
    (canonicalTensorComparison (ULift.{max u w} S))
    (canonicalTensorIsLeftDerived (ULift.{max u w} S)) K a b h

end StacksDraft.TorAmplitude
