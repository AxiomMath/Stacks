module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Algebra.Module.ProjResComplexFlat
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.TorAmplitude.ProjResKFlat

@[expose] public noncomputable section

/-!
# Vanishing of positive cohomology after derived tensoring with power-torsion objects

Let `R` be a commutative ring and `I ⊆ R` an ideal. If the derived tensor product of an object
`K` of `D(R)` with `R / I` has no positive cohomology, then the same holds after derived
tensoring `K` with every quotient `R / I ^ n`, with every `I`-power-torsion module, and with
every bounded object of `D(R)` whose cohomology is `I`-power torsion and concentrated in
nonpositive degrees.

## Main results

* `StacksDraft.PowerTorsionVanishing.positive_homology_derivedTensorProduct_isZero_of_mod_ideal`:
  the three vanishing statements above, Stacks 0H82.

## Implementation notes

Modules are regarded as objects of `D(R)` concentrated in degree zero and the bounded derived
category is `DerivedCategory.Bounded`; ideal-power torsion is the elementwise predicate
`IsIPowerTorsion`.

The derived tensor product is the canonical one of
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct`, which is pinned down by its
comparison with the ordinary total tensor product of K-flat representatives. Everything is
therefore computed through a fixed K-flat resolution `P` of `K` with flat terms: tensoring `P`
termwise with a module computes the derived tensor product
(`derivedTensor_single_iso_termwise`),
which turns the three conclusions into vanishing statements about the termwise complexes
`N ⊗ P`. The reduction to modules killed by `I` is a base change along `R → R / I`: the
extension of scalars of `P` is again K-flat, and
  `StacksDraft.TorAmplitude.FaithfullyFlat.restrictTensorLeftExtendIso`
identifies the two termwise complexes.

## References

* [The Stacks Project, Tag 0H82](https://stacks.math.columbia.edu/tag/0H82)
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.PowerTorsionVanishing

universe u v w w'

/-! ### Right `t`-exactness along a bounded object

An exact functor between derived categories which is right `t`-exact on the cohomology objects
of a bounded object is right `t`-exact on that object. This is proved by induction along the
canonical truncation triangles, so it needs the comparison of the cohomology of an object with
that of its truncations. -/

private lemma isIso_homology_truncLT
    {C : Type u} [Category.{v} C] [Abelian C]
    (c i : ℤ) (hi : i < c) (X : DerivedCategory C) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncLTι c).app X)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE c).obj X
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished c X
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    exact (DerivedCategory.isZero_of_isGE _ c i hi).eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT (i - 1) i (by omega)]
    exact (DerivedCategory.isZero_of_isGE _ c (i - 1) (by omega)).eq_of_src _ _
  change IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁)
  exact isIso_of_mono_of_epi _

private lemma isIso_homology_truncGE
    {C : Type u} [Category.{v} C] [Abelian C]
    (c i : ℤ) (hi : c ≤ i) (X : DerivedCategory C) :
    IsIso ((DerivedCategory.homologyFunctor C i).map
      ((DerivedCategory.TStructure.t.truncGEπ c).app X)) := by
  let T := (DerivedCategory.TStructure.t.triangleLTGE c).obj X
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished c X
  have : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (c - 1) (i + 1) (by omega)).eq_of_tgt _ _
  have : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₂) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i]
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (c - 1) i (by omega)).eq_of_src _ _
  change IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₂)
  exact isIso_of_mono_of_epi _

private lemma isLE_map_of_single_homology
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{w'} D] [Abelian D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    (X : DerivedCategory C) (c b : ℤ) [X.IsGE c] [X.IsLE c]
    (h : (F.obj ((DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C c).obj X))).IsLE (b - c)) :
    (F.obj X).IsLE b := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X c
  let q : (DerivedCategory.homologyFunctor C c).obj X ≅ Y :=
    (DerivedCategory.homologyFunctor C c).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C c).app Y
  let s := ((DerivedCategory.singleFunctors C).shiftIso (-c) c 0 (by omega)).app
    ((DerivedCategory.homologyFunctor C c).obj X)
  have := DerivedCategory.TStructure.t.isLE_shift
    (F.obj ((DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C c).obj X))) (b - c) (-c) b (by omega)
  let e'' : (F.obj ((DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C c).obj X)))⟦-c⟧ ≅ F.obj X :=
    (F.commShiftIso (-c)).symm.app _ ≪≫
      F.mapIso (s ≪≫ (DerivedCategory.singleFunctor C c).mapIso q ≪≫ e.symm)
  exact DerivedCategory.TStructure.t.isLE_of_iso e'' b

private lemma isLE_map_of_homology_aux
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{w'} D] [Abelian D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
    (b c : ℤ) (n : ℕ) (X : DerivedCategory C)
    [X.IsGE c] [hle : X.IsLE (c + n)]
    (h : ∀ i : ℤ, (F.obj ((DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C i).obj X))).IsLE (b - i)) :
    (F.obj X).IsLE b := by
  induction n generalizing X with
  | zero =>
      have : X.IsLE c := by simpa only [Nat.cast_zero, add_zero] using hle
      exact isLE_map_of_single_homology F X c b (h c)
  | succ n ih =>
      let d : ℤ := c + n + 1
      have h₁ : (F.obj ((DerivedCategory.TStructure.t.truncLT d).obj X)).IsLE b := by
        have : ((DerivedCategory.TStructure.t.truncLT d).obj X).IsLE (c + (n : ℤ)) :=
          DerivedCategory.TStructure.t.isLE_of_le _ (d - 1) _ (by dsimp [d]; omega)
        apply ih
        intro i
        by_cases hi : i < d
        · have := isIso_homology_truncLT d i hi X
          have := h i
          let e : F.obj ((DerivedCategory.singleFunctor C 0).obj
              ((DerivedCategory.homologyFunctor C i).obj X)) ≅
              F.obj ((DerivedCategory.singleFunctor C 0).obj
                ((DerivedCategory.homologyFunctor C i).obj
                  ((DerivedCategory.TStructure.t.truncLT d).obj X))) :=
            F.mapIso ((DerivedCategory.singleFunctor C 0).mapIso
              (asIso ((DerivedCategory.homologyFunctor C i).map
                ((DerivedCategory.TStructure.t.truncLTι d).app X))).symm)
          exact DerivedCategory.TStructure.t.isLE_of_iso e (b - i)
        · apply DerivedCategory.TStructure.t.isLE_of_isZero
          exact F.map_isZero ((DerivedCategory.singleFunctor C 0).map_isZero
            (DerivedCategory.isZero_of_isLE _ (d - 1) i (by omega)))
      have : X.IsLE d :=
        DerivedCategory.TStructure.t.isLE_of_le _ (c + (n + 1 : ℕ)) d (by dsimp [d]; omega)
      have h₃ : (F.obj ((DerivedCategory.TStructure.t.truncGE d).obj X)).IsLE b := by
        apply isLE_map_of_single_homology F _ d b
        have := isIso_homology_truncGE d d le_rfl X
        have := h d
        let e : F.obj ((DerivedCategory.singleFunctor C 0).obj
            ((DerivedCategory.homologyFunctor C d).obj X)) ≅
            F.obj ((DerivedCategory.singleFunctor C 0).obj
              ((DerivedCategory.homologyFunctor C d).obj
                ((DerivedCategory.TStructure.t.truncGE d).obj X))) :=
          F.mapIso ((DerivedCategory.singleFunctor C 0).mapIso
            (asIso ((DerivedCategory.homologyFunctor C d).map
              ((DerivedCategory.TStructure.t.truncGEπ d).app X))))
        exact DerivedCategory.TStructure.t.isLE_of_iso e (b - d)
      exact DerivedCategory.TStructure.t.isLE₂
        (F.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLTGE d).obj X))
        (F.map_distinguished _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished d X))
        b h₁ h₃

/-- An exact functor of derived categories which is right `t`-exact, up to a shift by the
degree, on each cohomology object of a bounded object `X` is right `t`-exact on `X`. -/
private lemma isLE_map_of_homology
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type w} [Category.{w'} D] [Abelian D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
    (X : DerivedCategory.Bounded C) (b : ℤ)
    (h : ∀ i : ℤ, (F.obj ((DerivedCategory.singleFunctor C 0).obj
      ((DerivedCategory.homologyFunctor C i).obj X.obj))).IsLE (b - i)) :
    (F.obj X.obj).IsLE b := by
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := X.property
  by_cases hcd : c ≤ d
  · have := hc
    have : X.obj.IsLE (c + ((d - c).toNat : ℤ)) :=
      DerivedCategory.TStructure.t.isLE_of_le _ d _ (by omega)
    exact isLE_map_of_homology_aux F b c (d - c).toNat X.obj h
  · apply DerivedCategory.TStructure.t.isLE_of_isZero
    exact F.map_isZero (DerivedCategory.TStructure.t.isZero X.obj d c (by omega))

/-! ### Computing the derived tensor product with a module

The canonical derived tensor product is pinned down by its comparison with the ordinary total
tensor product of K-flat representatives. Since the chosen projective resolution of a module is
a bounded-above complex of projectives, it is K-flat, so it may be used as the second
representative for an arbitrary first argument; and once the first argument is K-flat as well,
the projective resolution may be replaced by the module itself. -/

open CochainComplex.DerivedTensor in
/-- Tensoring on the right with a K-flat complex and totalizing preserves
quasi-isomorphisms of cochain complexes; the cochain-level form of Stacks 06Y0. -/
private lemma quasiIso_trightCochain_map {R : Type u} [CommRing R]
    (G : CochainComplex (ModuleCat.{u} R) ℤ) (hG : G.KFlat)
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) [QuasiIso f] :
    QuasiIso ((TrightCochain G).map f) := by
  have hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 ‹QuasiIso f›
  have h := CochainComplex.KFlat.kFlat_tright_preserves_quasiIso G
    (hG) ((HomotopyCategory.quotient _ _).map f) hf
  change HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient _ _ ⋙ Tright G).map f) at h
  unfold Tright at h
  rw [descendF_comp_quotient] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 h

/-- The augmentation of the chosen projective resolution, as a quasi-isomorphism of cochain
complexes onto the module placed in degree zero. -/
private def projResAugmentation {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M ⟶ (CochainComplex.singleFunctor
      (ModuleCat.{u} R) 0).obj M :=
  (ProjectiveResolution.of M).π'

private instance quasiIso_projResAugmentation {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    QuasiIso (projResAugmentation M) :=
  inferInstanceAs (QuasiIso (ProjectiveResolution.of M).π')

/-- The chosen projective resolution of a module is isomorphic to it in the derived category. -/
private def projResIso {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    DerivedCategory.Q.obj (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N :=
  asIso (DerivedCategory.Q.map (projResAugmentation N))

/-- The derived tensor product of an arbitrary representative `P` with a module `N` placed in
degree zero is computed by the ordinary total tensor product of `P` with the chosen projective
resolution of `N`. -/
private lemma derivedTensor_single_iso_projRes {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) :
    Nonempty
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
          (DerivedCategory.Q.obj P)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ≅
        DerivedCategory.Q.obj
          (P ⊗ StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N)) := by
  obtain ⟨F, g, hF, -, hg, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} P
  have hgi : QuasiIso g := hg
  have hFflat : F.KFlat := hF
  let eQ : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj P := asIso (DerivedCategory.Q.map g)
  have := quasiIso_trightCochain_map
    (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N)
    (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex_kFlat N) g
  let eT := asIso (DerivedCategory.Q.map ((TrightCochain
    (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N)).map g))
  exact ⟨((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).mapIso eQ.symm ≪≫
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
      (DerivedCategory.Q.obj F)).mapIso (projResIso N).symm ≪≫
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).comparison F
      (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N) hFflat
      (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex_kFlat N) ≪≫ eT⟩

/-- Derived tensoring with a module is right `t`-exact. -/
private lemma isLE_derivedTensor_single {R : Type u} [CommRing R]
    (K : CochainComplex.DerivedTensor.DObj R) (N : ModuleCat.{u} R) (b : ℤ) [K.IsLE b] :
    (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLE b := by
  obtain ⟨P, hP, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  have := hP
  have : (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N).IsStrictlyLE 0 := by
    change CochainComplex.IsStrictlyLE
      ((ProjectiveResolution.of N).complex.extend ComplexShape.embeddingDownNat) 0
    infer_instance
  have : CochainComplex.IsStrictlyLE
      (HomologicalComplex.tensorObj P
        (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N)) b := by
    simpa only [add_zero] using TotalTensorComplex.tensor_isStrictlyLE P
      (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N) b 0
  obtain ⟨q⟩ := derivedTensor_single_iso_projRes P N
  let q' : (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≅
      DerivedCategory.Q.obj (P ⊗ StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N) :=
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).mapIso e ≪≫ q
  exact DerivedCategory.TStructure.t.isLE_of_iso q'.symm b

/-- For a K-flat representative `P` of `K`, the derived tensor product of `K` with a module `N`
is computed by tensoring `P` termwise with `N`. -/
private lemma derivedTensor_single_iso_termwise {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (K : CochainComplex.DerivedTensor.DObj R) (e : DerivedCategory.Q.obj P ≅ K)
    (N : ModuleCat.{u} R) :
    Nonempty
      ((((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≅
        DerivedCategory.Q.obj
          (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  have := quasiIso_trightCochain_map P hP (projResAugmentation N)
  let eT := asIso (DerivedCategory.Q.map ((TrightCochain P).map (projResAugmentation N)))
  exact ⟨CochainComplex.DerivedTensor.derivedTensorProductCommIso K
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ≪≫
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).flip.obj K).mapIso
      (projResIso N).symm ≪≫
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
      (DerivedCategory.Q.obj (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N))).mapIso
        e.symm ≪≫
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).comparison
      (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex N) P
      (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex_kFlat N) hP ≪≫
    eT ≪≫ DerivedCategory.Q.mapIso
      (StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso N P)⟩

/-- A complex has no cohomology above `b` iff its image in the derived category is `≤ b`. -/
private lemma isLE_Q_obj_iff {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) :
    (DerivedCategory.Q.obj C).IsLE b ↔ ∀ i : ℤ, b < i → IsZero (C.homology i) := by
  rw [DerivedCategory.isLE_iff]
  exact forall₂_congr fun i _ => ((DerivedCategory.homologyFunctorFactors _ i).app C).isZero_iff

/-! ### The termwise tensor complex

For a K-flat representative the derived tensor product with a module is computed by the
complex obtained by tensoring termwise with that module. This subsection records the
elementary functoriality of that complex and its behaviour under a change of rings. -/

/-- A natural isomorphism of additive functors induces an isomorphism between the induced
functors on homological complexes. -/
private def mapHomologicalComplexIsoOfNatIso {ι : Type*} {W₁ W₂ : Type*} [Category W₁]
    [Category W₂] [Preadditive W₁] [Preadditive W₂] {F G : W₁ ⥤ W₂} [F.Additive] [G.Additive]
    (α : F ≅ G) (c : ComplexShape ι) :
    F.mapHomologicalComplex c ≅ G.mapHomologicalComplex c where
  hom := NatTrans.mapHomologicalComplex α.hom c
  inv := NatTrans.mapHomologicalComplex α.inv c
  hom_inv_id := by
    rw [← NatTrans.mapHomologicalComplex_comp, α.hom_inv_id, NatTrans.mapHomologicalComplex_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomologicalComplex_comp, α.inv_hom_id, NatTrans.mapHomologicalComplex_id]

/-- An isomorphism of modules induces one of the functors of tensoring with them. -/
private def tensorLeftIsoOfIso {R : Type u} [CommRing R] {M M' : ModuleCat.{u} R} (e : M ≅ M') :
    tensorLeft M ≅ tensorLeft M' :=
  NatIso.ofComponents (fun X => whiskerRightIso e X) (fun f => whisker_exchange e.hom f)

/-- Tensoring termwise with an isomorphic module gives an isomorphic complex. -/
private def termwiseTensorIsoOfIso {R : Type u} [CommRing R] {M M' : ModuleCat.{u} R} (e : M ≅ M')
    (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅
      ((tensorLeft M').mapHomologicalComplex (ComplexShape.up ℤ)).obj C :=
  (mapHomologicalComplexIsoOfNatIso (tensorLeftIsoOfIso e) (ComplexShape.up ℤ)).app C

/-- Tensoring with the ring itself is the identity functor on modules. -/
private def tensorLeftUnitIso (R : Type u) [CommRing R] :
    tensorLeft (ModuleCat.of R R) ≅ 𝟭 (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun X => MonoidalCategoryStruct.leftUnitor X)
    (fun f => leftUnitor_naturality f)

/-- Tensoring termwise with the ring itself does not change the complex. -/
private def termwiseTensorUnitIso {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((tensorLeft (ModuleCat.of R R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅ C :=
  (mapHomologicalComplexIsoOfNatIso (tensorLeftUnitIso R) (ComplexShape.up ℤ)).app C ≪≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).app C

/-- Restriction of scalars neither creates nor destroys vanishing of cohomology. -/
private lemma isZero_homology_restrictScalars_iff {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (D : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    IsZero (((CochainComplex.restrictScalars (algebraMap R A)).obj D).homology i) ↔
      IsZero (D.homology i) := by
  have e : (ModuleCat.restrictScalars (algebraMap R A)).obj (D.homology i) ≅
      ((CochainComplex.restrictScalars (algebraMap R A)).obj D).homology i :=
    (ShortComplex.mapHomologyIso (D.sc i) (ModuleCat.restrictScalars (algebraMap R A))).symm
  rw [← e.isZero_iff, StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff]

/-- Base change: tensoring a complex of `R`-modules termwise with an `A`-module is, as a
complex of `R`-modules, the extension of scalars of the complex tensored termwise over `A`. -/
private def termwiseTensorBaseChangeIso {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} A) :
    (CochainComplex.restrictScalars (algebraMap R A)).obj
        (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.extendScalars (algebraMap R A)).obj P)) ≅
      ((tensorLeft ((ModuleCat.restrictScalars (algebraMap R A)).obj N)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P :=
  (CochainComplex.restrictScalars (algebraMap R A)).mapIso
      (StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso N
        ((CochainComplex.extendScalars (algebraMap R A)).obj P)).symm ≪≫
    StacksDraft.TorAmplitude.FaithfullyFlat.restrictTensorLeftExtendIso R A
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj N) P ≪≫
    (tensorRight P).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars (algebraMap R A)) (ComplexShape.up ℤ) 0).app N) ≪≫
    StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso
      ((ModuleCat.restrictScalars (algebraMap R A)).obj N) P

/-- Vanishing of the cohomology of a termwise tensor complex is unchanged by a change of
rings. -/
private lemma isZero_homology_termwiseTensor_restrictScalars_iff
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} A) (i : ℤ) :
    IsZero ((((tensorLeft
          ((ModuleCat.restrictScalars (algebraMap R A)).obj N)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology i) ↔
      IsZero ((((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.extendScalars (algebraMap R A)).obj P)).homology i) := by
  have e : (((CochainComplex.restrictScalars (algebraMap R A)).obj
        (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.extendScalars (algebraMap R A)).obj P))).homology i) ≅
      ((((tensorLeft
            ((ModuleCat.restrictScalars (algebraMap R A)).obj N)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P).homology i) :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      (termwiseTensorBaseChangeIso P N)
  rw [← e.isZero_iff, isZero_homology_restrictScalars_iff]

/-! ### Directed unions of submodules

An `I`-power-torsion module is the directed union of its `I ^ n`-torsion submodules, and
tensoring a complex of flat modules termwise commutes with that union in the sense that
exactness in a degree passes to the union. -/

private lemma exists_rTensor_subtype_eq
    {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    {N : Type w} [AddCommMonoid N] [Module R N]
    (S : ℕ → Submodule R N) (hS : Monotone S) (hN : ∀ x : N, ∃ n, x ∈ S n)
    (x : TensorProduct R N M) :
    ∃ (n : ℕ) (y : TensorProduct R (S n) M), (S n).subtype.rTensor M y = x := by
  induction x using TensorProduct.inductionOn with
  | tmul y z =>
      obtain ⟨n, hn⟩ := hN y
      exact ⟨n, TensorProduct.tmul R ⟨y, hn⟩ z, rfl⟩
  | add x y hx hy =>
      obtain ⟨n, x', hx'⟩ := hx
      obtain ⟨m, y', hy'⟩ := hy
      let f := (Submodule.inclusion (hS (Nat.le_max_left n m))).rTensor M
      let g := (Submodule.inclusion (hS (Nat.le_max_right n m))).rTensor M
      refine ⟨max n m, f x' + g y', ?_⟩
      rw [map_add]
      have hf : (S (max n m)).subtype.rTensor M ∘ₗ f = (S n).subtype.rTensor M := by
        dsimp [f]
        rw [← LinearMap.rTensor_comp]
        rfl
      have hg : (S (max n m)).subtype.rTensor M ∘ₗ g = (S m).subtype.rTensor M := by
        dsimp [g]
        rw [← LinearMap.rTensor_comp]
        rfl
      exact congrArg₂ (· + ·) ((LinearMap.congr_fun hf x').trans hx')
        ((LinearMap.congr_fun hg y').trans hy')

private lemma exists_preimage_lTensor_of_directed_union
    {R : Type u} [CommRing R]
    {A B C N : Type v}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup N] [Module R N] [Module.Flat R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (S : ℕ → Submodule R N) (hS : Monotone S) (hN : ∀ x : N, ∃ n, x ∈ S n)
    (hex : ∀ n (x : TensorProduct R (S n) B),
      g.lTensor (S n) x = 0 → ∃ y, f.lTensor (S n) y = x)
    (x : TensorProduct R N B) (hx : g.lTensor N x = 0) :
    ∃ y, f.lTensor N y = x := by
  obtain ⟨n, x', hx'⟩ := exists_rTensor_subtype_eq S hS hN x
  have hg : (S n).subtype.rTensor C ∘ₗ g.lTensor (S n) =
      g.lTensor N ∘ₗ (S n).subtype.rTensor B := by
    ext y b
    rfl
  have hx'' : g.lTensor (S n) x' = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (S n).subtype
      (S n).subtype_injective
    rw [map_zero]
    exact (LinearMap.congr_fun hg x').trans (by rw [LinearMap.comp_apply, hx', hx])
  obtain ⟨y, hy⟩ := hex n x' hx''
  refine ⟨(S n).subtype.rTensor A y, ?_⟩
  have hf : f.lTensor N ∘ₗ (S n).subtype.rTensor A =
      (S n).subtype.rTensor B ∘ₗ f.lTensor (S n) := by
    ext z a
    rfl
  exact (LinearMap.congr_fun hf y).trans (by rw [LinearMap.comp_apply, hy, hx'])

private lemma exactAt_termwiseTensor_of_directed_union
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (N : ModuleCat.{u} R) (i : ℤ) [Module.Flat R (P.X ((ComplexShape.up ℤ).next i))]
    (S : ℕ → Submodule R N) (hS : Monotone S) (hN : ∀ x : N, ∃ n, x ∈ S n)
    (hex : ∀ n, (((tensorLeft (ModuleCat.of R (S n))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).ExactAt i) :
    (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
  intro x hx
  apply exists_preimage_lTensor_of_directed_union
    (P.d ((ComplexShape.up ℤ).prev i) i).hom (P.d i ((ComplexShape.up ℤ).next i)).hom
    S hS hN ?_ x hx
  intro n
  have hh := hex n
  rwa [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff] at hh

/-! ### Reduction to modules killed by the ideal

A module killed by `I` is a module over `R / I`, and the extension of scalars of a K-flat
complex along `R → R / I` is again K-flat. Since derived tensoring with a module is right
`t`-exact, the vanishing over `R / I` propagates to every `R / I`-module. -/

private lemma isZero_homology_termwiseTensor_of_isTorsionBySet {R : Type u} [CommRing R]
    (I : Ideal R) (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (b : ℤ)
    (hI : ∀ i : ℤ, b < i →
      IsZero ((((tensorLeft (ModuleCat.of R (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology i))
    (M : ModuleCat.{u} R) (hM : Module.IsTorsionBySet R M (I : Set R)) :
    ∀ i : ℤ, b < i →
      IsZero ((((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology i) := by
  let := hM.module
  let C := (CochainComplex.extendScalars (algebraMap R (R ⧸ I))).obj P
  have hC : C.KFlat := kFlat_baseChange (algebraMap R (R ⧸ I)) P hP
  have hCLE : (DerivedCategory.Q.obj C).IsLE b := by
    rw [isLE_Q_obj_iff]
    intro i hi
    have h1 : IsZero ((((tensorLeft (ModuleCat.of (R ⧸ I) (R ⧸ I))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).homology i) :=
      (isZero_homology_termwiseTensor_restrictScalars_iff P
        (ModuleCat.of (R ⧸ I) (R ⧸ I)) i).1 (hI i hi)
    exact ((HomologicalComplex.homologyFunctor (ModuleCat.{u} (R ⧸ I)) (ComplexShape.up ℤ)
      i).mapIso (termwiseTensorUnitIso C)).isZero_iff.1 h1
  have key : ∀ (N : ModuleCat.{u} (R ⧸ I)) (i : ℤ), b < i →
      IsZero ((((tensorLeft ((ModuleCat.restrictScalars
          (algebraMap R (R ⧸ I))).obj N)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).homology i) := by
    intro N i hi
    rw [isZero_homology_termwiseTensor_restrictScalars_iff]
    obtain ⟨q⟩ := derivedTensor_single_iso_termwise C hC (DerivedCategory.Q.obj C) (Iso.refl _) N
    have h2 := isLE_derivedTensor_single (DerivedCategory.Q.obj C) N b
    exact (isLE_Q_obj_iff _ b).1 (DerivedCategory.TStructure.t.isLE_of_iso q b) i hi
  intro i hi
  have hMN := key (ModuleCat.of (R ⧸ I) M) i hi
  let e : (ModuleCat.restrictScalars (algebraMap R (R ⧸ I))).obj (ModuleCat.of (R ⧸ I) M) ≅ M :=
    (LinearEquiv.refl R M).toModuleIso
  exact ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
    (termwiseTensorIsoOfIso e P)).isZero_iff.1 hMN

/-! ### The vanishing for power-torsion modules -/

private lemma isLE_derivedTensor_single_of_shortExact {R : Type u} [CommRing R]
    (K : CochainComplex.DerivedTensor.DObj R)
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (b : ℤ)
    (h₁ : (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S.X₁)).IsLE b)
    (h₃ : (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S.X₃)).IsLE b) :
    (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S.X₂)).IsLE b := by
  let F := (CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K
  exact DerivedCategory.TStructure.t.isLE₂ (F.mapTriangle.obj hS.singleTriangle)
    (F.map_distinguished _ hS.singleTriangle_distinguished) b h₁ h₃

private lemma isLE_derivedTensor_single_of_isTorsionBySet_pow {R : Type u} [CommRing R]
    (I : Ideal R) (K : CochainComplex.DerivedTensor.DObj R) (b : ℤ)
    (h : ∀ M : ModuleCat.{u} R, Module.IsTorsionBySet R M (I : Set R) →
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLE b)
    (n : ℕ) (M : ModuleCat.{u} R)
    (hM : Module.IsTorsionBySet R M ((I ^ n : Ideal R) : Set R)) :
    (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLE b := by
  induction n generalizing M with
  | zero =>
      apply h M
      intro x a
      exact @hM x ⟨a, by simp⟩
  | succ n ih =>
      let L : Submodule R M := I • (⊤ : Submodule R M)
      let S : ShortComplex (ModuleCat.{u} R) :=
        ShortComplex.mk (ModuleCat.ofHom L.subtype) (ModuleCat.ofHom L.mkQ) (by
          ext x
          exact (Submodule.Quotient.mk_eq_zero L).2 x.property)
      have hS : S.ShortExact := by
        refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
        · rw [ShortComplex.moduleCat_exact_iff]
          intro x hx
          exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero L).1 hx⟩, rfl⟩
        · exact (ModuleCat.mono_iff_injective _).2 L.subtype_injective
        · exact (ModuleCat.epi_iff_surjective _).2 L.mkQ_surjective
      apply isLE_derivedTensor_single_of_shortExact K hS b
      · apply ih
        intro x a
        apply Subtype.ext
        change (a : R) • (x : M) = 0
        refine Submodule.smul_induction_on x.property ?_ ?_
        · intro r hr y _
          have hz := @hM y ⟨a * r, by
            change (a : R) * r ∈ (I ^ (n + 1) : Ideal R)
            rw [pow_succ]
            exact Ideal.mul_mem_mul a.property hr⟩
          simpa only [mul_smul] using hz
        · intro x y hx hy
          rw [smul_add, hx, hy, add_zero]
      · exact h (ModuleCat.of R (M ⧸ L)) (Module.isTorsionBySet_quotient_ideal_smul M I)

/-- If the derived tensor product of `K` with `R / I` has no cohomology above `b`, neither has
the derived tensor product of `K` with any `I`-power-torsion module. -/
private lemma isLE_derivedTensor_single_of_isIPowerTorsion {R : Type u} [CommRing R]
    (I : Ideal R) (K : CochainComplex.DerivedTensor.DObj R) (b : ℤ)
    (hI : (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (R ⧸ I)))).IsLE b)
    (N : ModuleCat.{u} R) (hN : IsIPowerTorsion R N I) :
    (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLE b := by
  obtain ⟨P, f, hP, hflat, hf, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage K)
  have hfi : QuasiIso f := hf
  have hPK : P.KFlat := hP
  have : IsIso (DerivedCategory.Q.map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hfi
  let eP : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have bridge : ∀ M : ModuleCat.{u} R,
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLE b ↔
      ∀ i : ℤ, b < i →
        IsZero ((((tensorLeft M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P).homology i) := by
    intro M
    obtain ⟨q⟩ := derivedTensor_single_iso_termwise P hPK K eP M
    constructor
    · exact fun hle i hi =>
        (isLE_Q_obj_iff _ b).1 (DerivedCategory.TStructure.t.isLE_of_iso q b) i hi
    · intro hz
      have := (isLE_Q_obj_iff _ b).2 hz
      exact DerivedCategory.TStructure.t.isLE_of_iso q.symm b
  have hTorsion : ∀ M : ModuleCat.{u} R, Module.IsTorsionBySet R M (I : Set R) →
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLE b := by
    intro M hM
    rw [bridge]
    exact isZero_homology_termwiseTensor_of_isTorsionBySet I P hPK b
      ((bridge (ModuleCat.of R (R ⧸ I))).1 hI) M hM
  rw [bridge]
  intro i hi
  let Sub : ℕ → Submodule R N := fun n => Submodule.torsionBySet R N ((I ^ n : Ideal R) : Set R)
  have hSub : Monotone Sub := fun n m hnm =>
    Submodule.torsionBySet_le_torsionBySet_pow n m hnm I
  have hexh : ∀ x : N, ∃ n, x ∈ Sub n := by
    intro x
    obtain ⟨n, -, hn⟩ := hN x
    exact ⟨n, (Submodule.mem_torsionBySet_iff _ _).2 (fun a => hn a a.property)⟩
  have hflatX : Module.Flat R (P.X ((ComplexShape.up ℤ).next i)) :=
    hflat ((ComplexShape.up ℤ).next i)
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ i).1 ?_
  refine exactAt_termwiseTensor_of_directed_union P N i Sub hSub hexh ?_
  intro n
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ i).2 ?_
  refine (bridge (ModuleCat.of R (Sub n))).1 ?_ i hi
  exact isLE_derivedTensor_single_of_isTorsionBySet_pow I K b hTorsion n
    (ModuleCat.of R (Sub n))
    (Submodule.torsionBySet_isTorsionBySet (R := R) (M := N) ((I ^ n : Ideal R) : Set R))

/-! ### Stacks 0H82 -/

/-- **Stacks 0H82.** If `K ⊗ᴸ[R] R / I` has no positive cohomology, then positive cohomology
also vanishes after derived tensoring `K` with every positive-power quotient of `R`, with
every `I`-power-torsion module, and with every bounded, nonpositively concentrated object of
`D(R)` whose cohomology is `I`-power torsion. -/
@[stacks 0H82]
public theorem positive_homology_derivedTensorProduct_isZero_of_mod_ideal
    {R : Type u} [CommRing R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (R ⧸ I)))))) :
    (∀ (n : ℕ), 0 < n → ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R (R ⧸ I ^ n)))))) ∧
    (∀ (N : ModuleCat.{u} R), IsIPowerTorsion R N I → ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)))) ∧
    (∀ (M : DerivedCategory.Bounded (ModuleCat.{u} R)),
      (∀ i : ℤ, IsIPowerTorsion R
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M.obj) I) →
      (∀ i : ℤ, 0 < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M.obj)) →
      ∀ i : ℤ, 0 < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
            M.obj))) := by
  have hModules : ∀ N : ModuleCat.{u} R, IsIPowerTorsion R N I →
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLE 0 :=
    isLE_derivedTensor_single_of_isIPowerTorsion I K 0 ((DerivedCategory.isLE_iff _ 0).2 hK)
  refine ⟨?_, fun N hN => (DerivedCategory.isLE_iff _ 0).1 (hModules N hN), ?_⟩
  · intro n hn
    apply (DerivedCategory.isLE_iff _ 0).1 (hModules _ ?_)
    intro x
    refine ⟨n, hn, fun a ha => ?_⟩
    change (Ideal.Quotient.mk (I ^ n) a) * x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
  · intro M hM hMpos
    apply (DerivedCategory.isLE_iff _ 0).1
    apply isLE_map_of_homology
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj K) M 0
    intro i
    by_cases hi : 0 < i
    · apply DerivedCategory.TStructure.t.isLE_of_isZero
      exact ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).obj
        K).map_isZero
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map_isZero (hMpos i hi))
    · have := hModules _ (hM i)
      exact DerivedCategory.TStructure.t.isLE_of_le _ 0 (0 - i) (by omega)

end StacksDraft.PowerTorsionVanishing

end
