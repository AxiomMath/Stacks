module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.SpecResidueFieldCongr
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedGenericPoints
public import StacksFrontier.FieldTheory.PurelyInseparable.BaseChange
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.DiscreteValuationRing.ReducedTensorTower
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Geometric reducedness after a finite purely inseparable extension

A scheme locally of finite type over a field, with finitely many irreducible components, becomes
geometrically reduced after reduction and a suitable finite purely inseparable extension of the
ground field.

## Main results

* `AlgebraicGeometry.exists_finite_purelyInseparable_extension_geometricallyReduced_reduction`
  gives the field extension and geometric reducedness of the reduced base change.

## Implementation notes

The reduction of the base-changed scheme is the closed subscheme cut out by the vanishing ideal
of the entire underlying space. Its structure morphism is the composite of the closed immersion
with the second projection of the pullback.

Geometric reducedness is tested at the generic points, where the local ring is a field. The
residue field at a generic point is an essentially finite type extension of the ground field,
so it has a finite purely inseparable subextension over which it becomes separably generated;
the compositum of those subextensions, taken over the finitely many generic points, is the
required finite purely inseparable extension.

## References

* [Stacks Project, Tag 04KT](https://stacks.math.columbia.edu/tag/04KT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- Flat maps carry generic points to generic points: flatness lifts generalizations, while a
generic point has no proper generalizations. -/
private lemma genericPoints_map_of_flat {X Y : Scheme} (f : X ⟶ Y) [Flat f]
    (x : X) (hx : x ∈ genericPoints X) : f x ∈ genericPoints Y := by
  rw [mem_genericPoints_iff_forall_specializes_eq]
  intro y hy
  obtain ⟨x', hx'x, hfx'⟩ := Flat.generalizingMap f hy
  have : x' = x := (mem_genericPoints_iff_forall_specializes_eq x).1 hx x' hx'x
  simpa [this] using hfx'.symm

/-- A closed immersion with full support identifies generic points in its source and target. -/
private lemma genericPoints_map_of_closedImmersion_fullRange {X Y : Scheme}
    (f : X ⟶ Y) [IsClosedImmersion f] (hfull : Set.range f = Set.univ)
    (x : X) (hx : x ∈ genericPoints X) : f x ∈ genericPoints Y := by
  rw [mem_genericPoints_iff_forall_specializes_eq]
  intro y hy
  obtain ⟨x', rfl⟩ : y ∈ Set.range f := hfull ▸ Set.mem_univ y
  simp [(mem_genericPoints_iff_forall_specializes_eq x).1 hx x'
    (f.isClosedEmbedding.isInducing.specializes_iff.mp hy)]

/-- The `k`-algebra structure on the residue field of a point of a scheme over `Spec k`. -/
private abbrev residueFieldAlgebra {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : Algebra k (X.residueField x) :=
  letI : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
    StructureSheaf.stalkAlgebra k (f.base x)
  ((X.residue x).hom.comp ((f.stalkMap x).hom.comp
    (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x))))).toAlgebra

/-- Residue fields on a locally finite type scheme over a field are essentially finite type
extensions of that field. -/
private lemma residueField_essFiniteType {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    letI := residueFieldAlgebra f x
    Algebra.EssFiniteType k (X.residueField x) := by
  let R := (Spec (.of k)).presheaf.stalk (f.base x)
  let S := X.presheaf.stalk x
  let K := X.residueField x
  let : Algebra k R := StructureSheaf.stalkAlgebra k (f.base x)
  let a : k →+* R := algebraMap k R
  let b : R →+* S := (f.stalkMap x).hom
  let c : S →+* K := (X.residue x).hom
  let h := c.comp (b.comp a)
  let : Algebra k K := h.toAlgebra
  have hqclosed : f.base x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  let eR : R ≅ .of k :=
    (Spec (.of k)).presheaf.stalkCongr (Inseparable.of_eq hqclosed) ≪≫
      stalkClosedPointIso (.of k)
  have heq : a = eR.inv.hom := by
    ext s
    change (StructureSheaf.toStalk k (f.base x)).hom s = _
    dsimp only [eR, Iso.trans_inv]
    rw [stalkClosedPointIso_inv]
    change (StructureSheaf.toStalk k (f.base x)).hom s =
      (StructureSheaf.toStalk k (IsLocalRing.closedPoint k) ≫
        (Spec (.of k)).presheaf.stalkSpecializes (Inseparable.of_eq hqclosed).le).hom s
    exact congrArg
      (fun t : .of k ⟶ (Spec (.of k)).presheaf.stalk (f.base x) => t.hom s)
      (StructureSheaf.toStalk_stalkSpecializes (R := k)
        (Inseparable.of_eq hqclosed).le).symm
  have ha : a.EssFiniteType := by
    rw [heq]
    exact (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso eR.inv).2).essFiniteType
  have hb : b.EssFiniteType := LocallyOfFiniteType.stalkMap f x
  have hc : c.EssFiniteType :=
    (RingHom.FiniteType.of_surjective c IsLocalRing.residue_surjective).essFiniteType
  change h.EssFiniteType
  exact (ha.comp hb).comp hc

/-- The nilradical is contained in the kernel of any ring map to a reduced ring. -/
private lemma nilradical_le_ker_of_isReduced {R S : Type*} [CommRing R] [CommRing S]
    [_root_.IsReduced S] (φ : R →+* S) : nilradical R ≤ RingHom.ker φ := fun _ hx =>
  RingHom.mem_ker.mpr (isNilpotent_iff_eq_zero.mp ((mem_nilradical.mp hx).map φ))

/-- Geometric reducedness is preserved by algebraic extensions of the ground field. -/
private theorem isGeometricallyReduced_baseChange_of_algebraic
    (k E B : Type*) [Field k] [Field E] [CommRing B] [Algebra k E] [Algebra k B]
    [Algebra.IsAlgebraic k E]
    (hB : Algebra.IsGeometricallyReduced k B) :
    letI : Algebra E (E ⊗[k] B) := Algebra.TensorProduct.leftAlgebra
    Algebra.IsGeometricallyReduced E (E ⊗[k] B) := by
  let e₀ : E →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let : Algebra E (AlgebraicClosure k) := e₀.toAlgebra
  let e₁ : AlgebraicClosure E →ₐ[E] AlgebraicClosure k := IsAlgClosed.lift
  let e : AlgebraicClosure E →ₐ[k] AlgebraicClosure k := e₁.restrictScalars k
  let g : AlgebraicClosure E ⊗[k] B →ₐ[k] AlgebraicClosure k ⊗[k] B :=
    Algebra.TensorProduct.map e (AlgHom.id k B)
  have hg : Function.Injective g :=
    Module.Flat.rTensor_preserves_injective_linearMap e.toLinearMap e.injective
  have : _root_.IsReduced (AlgebraicClosure k ⊗[k] B) :=
    (Algebra.isGeometricallyReduced_field_iff k B).mp hB
  have : _root_.IsReduced (AlgebraicClosure E ⊗[k] B) := isReduced_of_injective g hg
  let e' : AlgebraicClosure E ⊗[E] (E ⊗[k] B) ≃ₐ[AlgebraicClosure E]
      AlgebraicClosure E ⊗[k] B :=
    Algebra.TensorProduct.cancelBaseChange k E (AlgebraicClosure E) (AlgebraicClosure E) B
  exact (Algebra.isGeometricallyReduced_field_iff E (E ⊗[k] B)).mpr
    (isReduced_of_injective e'.toRingEquiv.toRingHom e'.toRingEquiv.injective)

/-- If a separable compositum is enlarged by a purely inseparable extension of its constant
field, it still describes the reduction of the corresponding tensor product. -/
private theorem isGeometricallyReduced_reducedTensorProduct_of_extension
    (k k₀ K K₁ F : Type*) [Field k] [Field k₀] [Field K] [Field K₁] [Field F]
    [Algebra k k₀] [IsPurelyInseparable k k₀] [Algebra k K]
    [Algebra k K₁] [Algebra K K₁] [IsScalarTower k K K₁]
    [Algebra k₀ K₁] [IsScalarTower k k₀ K₁]
    [Algebra.IsSeparableExtension k₀ K₁]
    [Algebra k F] [Algebra k₀ F] [IsScalarTower k k₀ F]
    [Algebra.IsAlgebraic k₀ F] [IsPurelyInseparable k₀ F]
    [IsPurelyInseparable k F] :
    letI : Algebra F (F ⊗[k] K) := Algebra.TensorProduct.leftAlgebra
    Algebra.IsGeometricallyReduced F (ReducedTensorTower.Reduction (F ⊗[k] K)) := by
  let B := F ⊗[k₀] K₁
  let : Algebra F B := Algebra.TensorProduct.leftAlgebra
  let : Algebra k₀ B := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower k₀ F B :=
    IsScalarTower.of_algebraMap_eq (R := k₀) (S := F) (A := B) fun _ => rfl
  let : Algebra k B := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower k F B := IsScalarTower.of_algebraMap_eq' rfl
  have hmap : algebraMap k B = (algebraMap k₀ B).comp (algebraMap k k₀) := by
    ext x
    change algebraMap F B (algebraMap k F x) =
      algebraMap k₀ B (algebraMap k k₀ x)
    rw [IsScalarTower.algebraMap_apply k₀ F B,
      IsScalarTower.algebraMap_apply k k₀ F]
  let : IsScalarTower k k₀ B := IsScalarTower.of_algebraMap_eq' hmap
  have hred : _root_.IsReduced (K₁ ⊗[k₀] F) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated
      (Or.inl (inferInstance : Algebra.IsSeparableExtension k₀ K₁))
  have hspec : Subsingleton (PrimeSpectrum (K₁ ⊗[k₀] F)) :=
    ⟨fun x y => (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k₀ F K₁).injective
      (Subsingleton.elim _ _)⟩
  have hfield : IsField B :=
    MulEquiv.isField (PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp hspec)
      (Algebra.TensorProduct.comm k₀ K₁ F).symm.toRingEquiv.toMulEquiv
  let : Field B := hfield.toField
  have hKgeo : Algebra.IsGeometricallyReduced k₀ K₁ :=
    Stacks.FormallySmooth.SeparableTFAE.isGeometricallyReduced_of_isSeparableExtension k₀ K₁
  have hBgeo : Algebra.IsGeometricallyReduced F B :=
    isGeometricallyReduced_baseChange_of_algebraic k₀ F K₁ hKgeo
  let f₁ : F →ₐ[k] B := IsScalarTower.toAlgHom k F B
  let f₂ : K →ₐ[k] B :=
    (Algebra.TensorProduct.includeRight : K₁ →ₐ[k₀] B).restrictScalars k |>.comp
      (IsScalarTower.toAlgHom k K K₁)
  let f : F ⊗[k] K →ₐ[k] B := Algebra.TensorProduct.productMap f₁ f₂
  let fF : F ⊗[k] K →ₐ[F] B := {
    toRingHom := f.toRingHom
    commutes' := by
      intro x
      simp [f, f₁, Algebra.TensorProduct.productMap] }
  have hker : RingHom.ker f.toRingHom = nilradical (F ⊗[k] K) := by
    apply le_antisymm
    · intro x hx
      let c := Algebra.TensorProduct.comm k F K
      obtain ⟨n, hn, y, hy⟩ :=
        IsPurelyInseparable.exists_pow_mem_range_tensorProduct (c x)
      have hxpow : x ^ n =
          (Algebra.TensorProduct.includeRight : K →ₐ[k] F ⊗[k] K) y := by
        have h := congrArg c.symm hy
        simpa [c, Algebra.TensorProduct.comm_symm_tmul] using h.symm
      have hmap := congrArg f.toRingHom hxpow
      rw [map_pow, RingHom.mem_ker.mp hx] at hmap
      obtain rfl : y = 0 := by
        have hfy' : f
            ((Algebra.TensorProduct.includeRight : K →ₐ[k] F ⊗[k] K) y) = 0 := by
          simpa [hn.ne'] using hmap.symm
        have hfy : f₂ y = 0 := by
          simpa [f, Algebra.TensorProduct.productMap] using hfy'
        exact f₂.injective (by simpa using hfy)
      exact mem_nilradical.mpr ⟨n, by simpa using hxpow⟩
    · exact nilradical_le_ker_of_isReduced f.toRingHom
  let lift : ReducedTensorTower.Reduction (F ⊗[k] K) →ₐ[F] B :=
    Ideal.Quotient.liftₐ (nilradical (F ⊗[k] K)) fF (fun x hx =>
      RingHom.mem_ker.mp (hker.symm ▸ hx))
  have hinj : Function.Injective lift := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [show lift (Ideal.Quotient.mk _ a) = fF a from rfl,
      show lift (Ideal.Quotient.mk _ b) = fF b from rfl] at hxy
    have hab : a - b ∈ RingHom.ker f.toRingHom := by
      rw [RingHom.mem_ker]
      change f (a - b) = 0
      have hxy' : f a = f b := hxy
      rw [map_sub, hxy', sub_self]
    rw [hker] at hab
    exact (Ideal.Quotient.eq).2 hab
  exact Algebra.IsGeometricallyReduced.of_injective lift hinj

/-- A finite purely inseparable extension embeds over the base into its algebraic closure. -/
private theorem exists_embedding_finite_purelyInseparable_extension
    (k E : Type*) [Field k] [Field E] [Algebra k E] [Module.Finite k E]
    [IsPurelyInseparable k E] :
    ∃ F : IntermediateField k (AlgebraicClosure k), Module.Finite k F ∧
      IsPurelyInseparable k F ∧ Nonempty (E ≃ₐ[k] ↥F) := by
  let : Algebra.IsAlgebraic k E := Algebra.IsAlgebraic.of_finite k E
  let φ : E →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let F : IntermediateField k (AlgebraicClosure k) := φ.fieldRange
  let e : E ≃ₐ[k] ↥F := AlgEquiv.ofInjectiveField φ
  exact ⟨F, Module.Finite.of_surjective e.toLinearMap e.surjective, e.isPurelyInseparable, ⟨e⟩⟩

/-- Finite composita of finite purely inseparable extensions are still finite and purely
inseparable. -/
private theorem exists_finite_common_purelyInseparable_extension
    (k : Type*) [Field k] {ι : Type*} [Finite ι]
    (F : ι → IntermediateField k (AlgebraicClosure k))
    (hfinite : ∀ i, Module.Finite k (F i))
    (hpure : ∀ i, IsPurelyInseparable k (F i)) :
    ∃ E : IntermediateField k (AlgebraicClosure k), Module.Finite k E ∧
      IsPurelyInseparable k E ∧ ∀ i, F i ≤ E := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let E : IntermediateField k (AlgebraicClosure k) := ⨆ i, F i
  have hfd : Module.Finite k E := by
    have hsup : ∀ s : Finset ι,
        FiniteDimensional k (Finset.sup s F : IntermediateField k (AlgebraicClosure k)) := by
      intro s
      induction s using Finset.induction with
      | empty =>
          change FiniteDimensional k (⊥ : IntermediateField k (AlgebraicClosure k))
          infer_instance
      | @insert i s hi ih =>
          rw [Finset.sup_insert]
          let : FiniteDimensional k
              (Finset.sup s F : IntermediateField k (AlgebraicClosure k)) := ih
          let : Module.Finite k (F i) := hfinite i
          infer_instance
    have heq : Finset.sup Finset.univ F = E := by
      rw [Finset.sup_eq_iSup]
      simp [E]
    rw [← heq]
    let : FiniteDimensional k
        (Finset.sup Finset.univ F : IntermediateField k (AlgebraicClosure k)) :=
      hsup Finset.univ
    exact inferInstance
  have hpi : IsPurelyInseparable k E := by
    let : ∀ i, IsPurelyInseparable k (F i) := hpure
    infer_instance
  exact ⟨E, hfd, hpi, le_iSup F⟩

/-- The data extracted from an essentially finite type field extension: a separably generated
subextension over a finite purely inseparable constant field extension, together with a model
of that constant field inside the algebraic closure of the base. -/
private structure GeometricFieldWitness (k K : Type*) [Field k] [Field K]
    [Algebra k K] where
  /-- A subextension of the algebraic closure of `K` containing `K`. -/
  K' : IntermediateField K (AlgebraicClosure K)
  /-- The constant field of `K'`, purely inseparable over `k`. -/
  k' : IntermediateField k ↥K'
  /-- A model of `k'` inside the algebraic closure of `k`. -/
  G : IntermediateField k (AlgebraicClosure k)
  /-- `k'` is purely inseparable over `k`. -/
  k'_pure : IsPurelyInseparable k ↥k'
  /-- `G` is finite over `k`. -/
  G_finite : Module.Finite k ↥G
  /-- `G` is purely inseparable over `k`. -/
  G_pure : IsPurelyInseparable k ↥G
  /-- `k'` and `G` are isomorphic over `k`. -/
  e : Nonempty (↥k' ≃ₐ[k] ↥G)
  /-- `K'` is a separable extension of `k'`. -/
  hsep : Algebra.IsSeparableExtension ↥k' ↥K'

/-- Every essentially finite type field extension carries such data. -/
private theorem exists_geometricFieldWitness
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] : Nonempty (GeometricFieldWitness k K) := by
  let Ω := AlgebraicClosure K
  let : IsScalarTower k K Ω := inferInstance
  obtain ⟨K', k', _, _, hkfin, hkpi, hsep, _⟩ :=
    exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType k K Ω
  obtain ⟨G, hGfin, hGpi, ⟨e⟩⟩ :=
    exists_embedding_finite_purelyInseparable_extension k ↥k'
  exact ⟨⟨K', k', G, hkpi, hGfin, hGpi, ⟨e⟩, hsep⟩⟩

/-- For finitely many essentially finite type field extensions there is one finite purely
inseparable extension of the base after which the reduction of every base change becomes
geometrically reduced. The compositum carries the scalar towers of all the chosen intermediate
fields. -/
private theorem exists_finite_common_purelyInseparable_extension_geometricallyReduced_fields
    (k : Type*) [Field k] {ι : Type*} [Finite ι] (K : ι → Type*)
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    [∀ i, Algebra.EssFiniteType k (K i)] :
    ∃ F : IntermediateField k (AlgebraicClosure k), Module.Finite k ↥F ∧
      IsPurelyInseparable k ↥F ∧
      ∀ i, letI : Algebra ↥F (↥F ⊗[k] K i) := Algebra.TensorProduct.leftAlgebra
        Algebra.IsGeometricallyReduced ↥F
          (ReducedTensorTower.Reduction (↥F ⊗[k] K i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let W : ∀ i, GeometricFieldWitness k (K i) := fun i =>
    Classical.choice (exists_geometricFieldWitness k (K i))
  let G : ι → IntermediateField k (AlgebraicClosure k) := fun i => (W i).G
  obtain ⟨F, hFfin, hFpure, hFle⟩ := exists_finite_common_purelyInseparable_extension k G
    (fun i => (W i).G_finite) (fun i => (W i).G_pure)
  refine ⟨F, hFfin, hFpure, fun i => ?_⟩
  let Wi := W i
  let e : ↥Wi.k' ≃ₐ[k] ↥Wi.G := Wi.e.some
  let : IsPurelyInseparable k ↥Wi.k' := Wi.k'_pure
  let φ : ↥Wi.k' →ₐ[k] ↥F :=
    (IntermediateField.inclusion (hFle i)).comp e.toAlgHom
  let : Algebra ↥Wi.k' ↥F := φ.toAlgebra
  let : SMul ↥Wi.k' ↥F := φ.toAlgebra.toSMul
  let : IsScalarTower k ↥Wi.k' ↥F :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := ↥Wi.k') (A := ↥F) fun x =>
      (φ.commutes x).symm
  let : IsPurelyInseparable ↥Wi.k' ↥F := IsPurelyInseparable.tower_top k ↥Wi.k' ↥F
  let : Algebra.IsAlgebraic ↥Wi.k' ↥F := IsPurelyInseparable.isAlgebraic ↥Wi.k' ↥F
  let : Algebra.IsSeparableExtension ↥Wi.k' ↥Wi.K' := Wi.hsep
  exact isGeometricallyReduced_reducedTensorProduct_of_extension
    k ↥Wi.k' (K i) ↥Wi.K' ↥F

/-- A morphism from the spectrum of a field through which the canonical map from the residue
field factors is an isomorphism on sections. -/
private lemma isIso_of_specMap_comp_eq_fromSpecResidueField
    {Z : Scheme.{u}} (z : Z) {K : Type u} [Field K]
    (φ : CommRingCat.of K ⟶ Z.residueField z) (a : Spec (.of K) ⟶ Z)
    (h : Spec.map φ ≫ a = Z.fromSpecResidueField z) : IsIso φ := by
  obtain ⟨⟨y, j⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective a
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h
  have hy := congrArg (fun m : Spec (Z.residueField z) ⟶ Z => m default) h
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at hy
  subst y
  have : Mono φ := ConcreteCategory.mono_of_injective φ φ.hom.injective
  have : IsSplitEpi φ := ⟨⟨j, by
    simpa only [← Spec.map_inj, Spec.map_comp, Spec.map_id,
      ← cancel_mono (Z.fromSpecResidueField z), Category.assoc, Category.id_comp] using h⟩⟩
  exact isIso_of_mono_of_isSplitEpi φ

/-- The reduction of a tensor product with a purely inseparable extension of the base field is
a field. -/
private lemma isField_reducedTensorProduct (k F K : Type*)
    [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
    [IsPurelyInseparable k F] :
    IsField (ReducedTensorTower.Reduction (F ⊗[k] K)) := by
  have h : Subsingleton (PrimeSpectrum (K ⊗[k] F)) :=
    ⟨fun x y => (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k F K).injective
      (Subsingleton.elim _ _)⟩
  have h' : Subsingleton (PrimeSpectrum (F ⊗[k] K)) :=
    ⟨fun x y => (PrimeSpectrum.isHomeomorph_comap_of_bijective
      (f := (Algebra.TensorProduct.comm k K F).toRingHom)
      (Algebra.TensorProduct.comm k K F).bijective).injective (Subsingleton.elim _ _)⟩
  have hQ : Subsingleton (PrimeSpectrum (ReducedTensorTower.Reduction (F ⊗[k] K))) :=
    ⟨fun x y => (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
      (R := F ⊗[k] K) le_rfl).injective (Subsingleton.elim _ _)⟩
  have : _root_.IsReduced (ReducedTensorTower.Reduction (F ⊗[k] K)) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (by
      change (⊥ : Ideal (F ⊗[k] K)).radical.IsRadical
      exact Ideal.radical_isRadical _)
  have : Nontrivial (ReducedTensorTower.Reduction (F ⊗[k] K)) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      change (⊥ : Ideal (F ⊗[k] K)).radical ≠ ⊤
      simpa only [ne_eq, Ideal.radical_eq_top] using
        (bot_ne_top : (⊥ : Ideal (F ⊗[k] K)) ≠ ⊤))
  exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp hQ

/-- Under the identifications of the residue fields of the spectrum of a field with the field,
the residue-field map of `Spec K ⟶ Spec k` is the algebra map `k → K`. -/
private lemma specMap_residueFieldMap_comp_residueFieldEquiv (k K : Type u) [Field k] [Field K]
    [Algebra k K] (s : Spec (.of k)) (y : Spec (.of K))
    (hxy : Spec.map (CommRingCat.ofHom (algebraMap k K)) y = s) :
    letI : s.asIdeal.IsPrime := s.isPrime
    letI : y.asIdeal.IsPrime := y.isPrime
    (((Spec.map (CommRingCat.ofHom (algebraMap k K))).residueFieldMap y).hom.comp
        ((Spec (.of k)).residueFieldCongr hxy).inv.hom).comp
      (s.asIdeal.algEquivResidueFieldOfField.toRingEquiv.trans
        (Scheme.Spec.residueFieldIso (.of k) s).symm.commRingCatIsoToRingEquiv).toRingHom =
    (y.asIdeal.algEquivResidueFieldOfField.toRingEquiv.trans
        (Scheme.Spec.residueFieldIso (.of K) y).symm.commRingCatIsoToRingEquiv).toRingHom.comp
      (algebraMap k K) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : s.asIdeal.IsPrime := s.isPrime
  let : y.asIdeal.IsPrime := y.isPrime
  let : (g y).asIdeal.IsPrime := (g y).isPrime
  let eR : k ≃+* (Spec (.of k)).residueField s :=
    (s.asIdeal.algEquivResidueFieldOfField).toRingEquiv.trans
      (Scheme.Spec.residueFieldIso (.of k) s).symm.commRingCatIsoToRingEquiv
  let eC : K ≃+* (Spec (.of K)).residueField y :=
    (y.asIdeal.algEquivResidueFieldOfField).toRingEquiv.trans
      (Scheme.Spec.residueFieldIso (.of K) y).symm.commRingCatIsoToRingEquiv
  let eRg : k ≃+* (Spec (.of k)).residueField (g y) :=
    ((g y).asIdeal.algEquivResidueFieldOfField).toRingEquiv.trans
      (Scheme.Spec.residueFieldIso (.of k) (g y)).symm.commRingCatIsoToRingEquiv
  change ((g.residueFieldMap y).hom.comp ((Spec (.of k)).residueFieldCongr hxy).inv.hom).comp
    eR.toRingHom = eC.toRingHom.comp (algebraMap k K)
  ext z'
  apply (Scheme.Spec.residueFieldIso (.of K) y).commRingCatIsoToRingEquiv.injective
  have hbridge := specResidueFieldMap_bridge
    (CommRingCat.ofHom (algebraMap k K)) y
  have hbridge' := congrArg
    (fun φ => φ ((g y).asIdeal.algEquivResidueFieldOfField z')) hbridge
  have hbridge'' :
      (Scheme.Spec.residueFieldIso (.of K) y).commRingCatIsoToRingEquiv
        ((g.residueFieldMap y).hom (eRg z')) =
      y.asIdeal.algEquivResidueFieldOfField (algebraMap k K z') := by
    rw [Ideal.algEquivResidueFieldOfField_apply,
      Ideal.ResidueField.map_algebraMap] at hbridge'
    change (Scheme.Spec.residueFieldIso (.of K) y).hom.hom
        ((g.residueFieldMap y).hom
          ((Scheme.Spec.residueFieldIso (.of k) (g y)).inv.hom
            ((g y).asIdeal.algEquivResidueFieldOfField z'))) =
      (algebraMap K y.asIdeal.ResidueField) (algebraMap k K z') at hbridge'
    simpa [eRg, CategoryTheory.Iso.commRingCatIsoToRingEquiv,
      Ideal.algEquivResidueFieldOfField_apply] using hbridge'
  have htransport : (Scheme.residueFieldCongr hxy).inv.hom (eR z') = eRg z' := by
    simpa [eR, eRg, Scheme.residueFieldCongr] using
      spec_residueFieldEquiv_congr k s (g y) hxy.symm z'
  change (Scheme.Spec.residueFieldIso (.of K) y).commRingCatIsoToRingEquiv
      (g.residueFieldMap y ((Scheme.residueFieldCongr hxy).inv (eR z'))) =
    (Scheme.Spec.residueFieldIso (.of K) y).commRingCatIsoToRingEquiv
      (eC (algebraMap k K z'))
  rw [htransport]
  calc
    (Scheme.Spec.residueFieldIso (.of K) y).commRingCatIsoToRingEquiv
        ((g.residueFieldMap y).hom (eRg z')) =
      y.asIdeal.algEquivResidueFieldOfField (algebraMap k K z') := hbridge''
    _ = (Scheme.Spec.residueFieldIso (.of K) y).commRingCatIsoToRingEquiv
        (eC (algebraMap k K z')) := by
      simp [eC, RingEquiv.trans_apply,
        CategoryTheory.Iso.commRingCatIsoToRingEquiv]

/-- Geometric reducedness of the reduction of the residue-field tensor product at a generic
point gives geometric reducedness there. The residue-field comparison involves several nested
tensor-product maps. -/
private theorem isGeometricallyReducedAt_of_reducedTensorProduct
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {Y : Scheme.{u}} [IsReduced Y]
    (q : Y ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [IsClosedImmersion q] (ξ : Y) (hξ : ξ ∈ genericPoints Y)
    (hgeo :
      let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
      let x := pullback.fst f g (q ξ)
      letI := residueFieldAlgebra f x
      letI : Algebra K (K ⊗[k] X.residueField x) := Algebra.TensorProduct.leftAlgebra
      Algebra.IsGeometricallyReduced K
        (ReducedTensorTower.Reduction (K ⊗[k] X.residueField x))) :
    IsGeometricallyReducedAt
      (q ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ξ := by
  classical
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p : pullback f g ⟶ Spec (.of K) := pullback.snd f g
  let z := q ξ
  let C : irreducibleComponents Y := genericPoints.component ⟨ξ, hξ⟩
  have hC : closure ({ξ} : Set Y) ∈ irreducibleComponents Y := by
    rw [(genericPoints.isGenericPoint ⟨ξ, hξ⟩).def]
    exact C.property
  have hfieldY : IsField (Y.presheaf.stalk ξ) :=
    isField_stalk_of_closure_mem_irreducibleComponents Y ξ hC
  let : Field (Y.presheaf.stalk ξ) := hfieldY.toField
  apply (isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk (q ≫ p) ξ).2
  have hqres : IsIso (q.residueFieldMap ξ) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    refine ⟨(q.residueFieldMap ξ).hom.injective, ?_⟩
    intro b
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective b
    obtain ⟨a, ha⟩ := q.stalkMap_surjective ξ b
    refine ⟨IsLocalRing.residue _ a, ?_⟩
    change IsLocalRing.ResidueField.map (q.stalkMap ξ).hom (IsLocalRing.residue _ a) = _
    rw [IsLocalRing.ResidueField.map_residue, ha]
  let T := Scheme.Pullback.Triplet.ofPoint z
  let R := (Spec (.of k)).residueField (f T.x)
  let R₀ := (Spec (.of k)).residueField T.s
  let A := X.residueField T.x
  let : Algebra k A := residueFieldAlgebra f T.x
  let C₀ := (Spec (.of K)).residueField T.y
  have hxy : g T.y = f T.x := T.hy.trans T.hx.symm
  have hbase : T.s = f T.x := T.hy.symm.trans hxy
  let : T.s.asIdeal.IsPrime := T.s.isPrime
  let : T.y.asIdeal.IsPrime := T.y.isPrime
  let : (f T.x).asIdeal.IsPrime := (f T.x).isPrime
  let eR : k ≃+* R :=
    ((f T.x).asIdeal.algEquivResidueFieldOfField).toRingEquiv.trans
      (Scheme.Spec.residueFieldIso (.of k) (f T.x)).symm.commRingCatIsoToRingEquiv
  let eC : K ≃+* C₀ :=
    (T.y.asIdeal.algEquivResidueFieldOfField).toRingEquiv.trans
      (Scheme.Spec.residueFieldIso (.of K) T.y).symm.commRingCatIsoToRingEquiv
  let a : R →+* A := (f.residueFieldMap T.x).hom
  let b : R →+* C₀ := (g.residueFieldMap T.y).hom.comp
    ((Spec (.of k)).residueFieldCongr hxy).inv.hom
  let a₀ : R₀ →+* A := (f.residueFieldMap T.x).hom.comp
    ((Spec (.of k)).residueFieldCongr T.hx).inv.hom
  let b₀ : R₀ →+* C₀ := (g.residueFieldMap T.y).hom.comp
    ((Spec (.of k)).residueFieldCongr T.hy).inv.hom
  have hpo₀ : IsPushout (CommRingCat.ofHom a₀) (CommRingCat.ofHom b₀)
      T.tensorInl T.tensorInr := IsPushout.of_hasPushout _ _
  have hpo : IsPushout (CommRingCat.ofHom a) (CommRingCat.ofHom b)
      T.tensorInl T.tensorInr := by
    apply hpo₀.of_iso (Scheme.residueFieldCongr hbase) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · ext z'
      simp [a₀, a, Scheme.residueFieldCongr]
    · ext z'
      simp [b₀, b, Scheme.residueFieldCongr]
    · simp
    · simp
  have hcommf : a.comp eR.toRingHom = algebraMap k A := by
    have H := Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) (f T.x)
    have H' := congrArg (fun t => t ≫ f.residueFieldMap T.x) H
    simp only [Category.assoc, Scheme.residue_residueFieldMap] at H'
    exact (congrArg CommRingCat.Hom.hom H')
  have hcommg : b.comp eR.toRingHom = eC.toRingHom.comp (algebraMap k K) :=
    specMap_residueFieldMap_comp_residueFieldEquiv k K (f T.x) T.y hxy
  have hpo' : IsPushout (CommRingCat.ofHom (algebraMap k A))
      (CommRingCat.ofHom (algebraMap k K))
      (CommRingCat.ofHom T.tensorInl.hom)
      (CommRingCat.ofHom (T.tensorInr.hom.comp eC.toRingHom)) := by
    apply hpo.of_iso eR.symm.toCommRingCatIso (Iso.refl _)
      eC.symm.toCommRingCatIso (Iso.refl _)
    · ext z'
      simpa using DFunLike.congr_fun hcommf (eR.symm z')
    · ext z'
      have hz' := DFunLike.congr_fun hcommg (eR.symm z')
      change eC.symm (b z') = algebraMap k K (eR.symm z')
      simpa only [RingHom.comp_apply, RingEquiv.apply_symm_apply,
        RingEquiv.symm_apply_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using
        congrArg eC.symm hz'
    · simp
    · ext z'
      simp [eC]
  have hTensor := CommRingCat.isPushout_tensorProduct k A K
  let eTensor := hpo'.isoIsPushout _ _ hTensor
  let D := K ⊗[k] A
  let Q := ReducedTensorTower.Reduction D
  let : Field Q := (isField_reducedTensorProduct k K A).toField
  let c : D ≃+* T.tensor := (Algebra.TensorProduct.comm k K A).toRingEquiv.trans
    eTensor.symm.commRingCatIsoToRingEquiv
  let β : D →+* (pullback f g).residueField z :=
    (Scheme.Pullback.ofPointTensor z).hom.comp c.toRingHom
  let ψ : Q →+* (pullback f g).residueField z :=
    Ideal.Quotient.lift (nilradical D) β fun _ hr => nilradical_le_ker_of_isReduced β hr
  let π : T.tensor →+* Q := (Ideal.Quotient.mk (nilradical D)).comp c.symm.toRingHom
  have hπψ : CommRingCat.ofHom π ≫ CommRingCat.ofHom ψ =
      Scheme.Pullback.ofPointTensor z := by
    ext r
    change β (c.symm r) = _
    simp [β]
  have hψ : IsIso (CommRingCat.ofHom ψ) :=
    isIso_of_specMap_comp_eq_fromSpecResidueField z (CommRingCat.ofHom ψ)
      (Spec.map (CommRingCat.ofHom π) ≫ T.SpecTensorTo) (by
        have H : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom π) =
            Spec.map (Scheme.Pullback.ofPointTensor z) :=
          (Spec.map_comp (CommRingCat.ofHom π) (CommRingCat.ofHom ψ)).symm.trans
            (congrArg Spec.map hπψ)
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ T.SpecTensorTo) H).trans
            (Scheme.Pullback.ofPointTensor_SpecTensorTo z)))
  have hresY : IsIso (Y.residue ξ) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      ⟨(Y.residue ξ).hom.injective, Y.residue_surjective ξ⟩
  let d : CommRingCat.of Q ≅ Y.presheaf.stalk ξ :=
    asIso (CommRingCat.ofHom ψ) ≪≫ asIso (q.residueFieldMap ξ) ≪≫ (asIso (Y.residue ξ)).symm
  let : Algebra K D := Algebra.TensorProduct.leftAlgebra
  let : Algebra K (Y.presheaf.stalk ξ) :=
    let : Algebra K ((Spec (.of K)).presheaf.stalk ((q ≫ p).base ξ)) :=
      StructureSheaf.stalkAlgebra K ((q ≫ p).base ξ)
    ((q ≫ p).stalkMap ξ).hom.comp
      (algebraMap K ((Spec (.of K)).presheaf.stalk ((q ≫ p).base ξ))) |>.toAlgebra
  have hd (t : K) : d.hom (algebraMap K Q t) =
      algebraMap K (Y.presheaf.stalk ξ) t := by
    apply (Y.residue ξ).hom.injective
    have hc : c (algebraMap K D t) = T.tensorInr (eC t) := by
      have H := hpo'.inr_isoIsPushout_inv _ _ hTensor
      exact congrArg (fun h => h.hom t) H
    have hβ : ψ (algebraMap K Q t) = (p.residueFieldMap z) (eC t) := by
      change (Scheme.Pullback.ofPointTensor z) (c (algebraMap K D t)) = _
      rw [hc]
      exact congrArg (fun h => h.hom (eC t))
        (pushout.inr_desc _ _ (Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_ofPoint z))
    have heC : eC t = (Spec (.of K)).residue T.y
        ((StructureSheaf.toStalk K T.y).hom t) :=
      congrArg (fun h => h.hom t)
        (Scheme.Spec.algebraMap_residueFieldIso_inv (.of K) T.y)
    change (Y.residue ξ) (d.hom (algebraMap K Q t)) = _
    have hdres : d.hom ≫ Y.residue ξ =
        CommRingCat.ofHom ψ ≫ q.residueFieldMap ξ := by simp [d]
    rw [← CommRingCat.comp_apply, hdres, CommRingCat.comp_apply]
    change (q.residueFieldMap ξ).hom (ψ (algebraMap K Q t)) = _
    rw [hβ, heC]
    have H := Scheme.residue_residueFieldMap (q ≫ p) ξ
    rw [Scheme.residueFieldMap_comp] at H
    exact congrArg (fun h => h.hom ((StructureSheaf.toStalk K T.y).hom t)) H
  let e : Q ≃ₐ[K] (Y.presheaf.stalk ξ) :=
    { d.commRingCatIsoToRingEquiv with commutes' := hd }
  have : Algebra.IsGeometricallyReduced K Q := hgeo
  exact Algebra.IsGeometricallyReduced.of_injective e.symm.toAlgHom e.symm.injective

/-- **Stacks Project, Tag 04KT.** After a finite purely inseparable extension of the ground
field, the reduction of the base change of a scheme with finitely many irreducible components
is geometrically reduced. -/
@[stacks 04KT,
  ega "IV 17.15.14.2" "geom. reduced reduction",
  ega "IV 4.6.6" "more general",
  ega "IV 4.6.8" "First clause"]
public theorem exists_finite_purelyInseparable_extension_geometricallyReduced_reduction
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hX : (irreducibleComponents X).Finite) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : Module.Finite k k') (_ : IsPurelyInseparable k k'),
      let g : Spec (.of k') ⟶ Spec (.of k) :=
        Spec.map (CommRingCat.ofHom (algebraMap k k'))
      let p : pullback f g ⟶ Spec (.of k') := pullback.snd f g
      let I := Scheme.IdealSheafData.vanishingIdeal
        (X := (pullback f g : Scheme.{u})) (⊤ : Closeds (pullback f g : Scheme.{u}))
      GeometricallyReduced (I.subschemeι ≫ p) := by
  classical
  let ι := genericPoints X
  let : Finite ι := genericPoints.finite hX
  let (x : ι) : Algebra k (X.residueField x) := residueFieldAlgebra f x
  let (x : ι) : Algebra.EssFiniteType k (X.residueField x) :=
    residueField_essFiniteType f x
  obtain ⟨F, hFfin, hFpure, hFgeo⟩ :=
    exists_finite_common_purelyInseparable_extension_geometricallyReduced_fields
      k (fun x : ι => X.residueField x)
  refine ⟨↥F, inferInstance, inferInstance, hFfin, hFpure, ?_⟩
  let g : Spec (.of ↥F) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k ↥F))
  let p : pullback f g ⟶ Spec (.of ↥F) := pullback.snd f g
  let I := Scheme.IdealSheafData.vanishingIdeal
    (X := (pullback f g : Scheme.{u})) (⊤ : Closeds (pullback f g : Scheme.{u}))
  let Y := I.subscheme
  let q := I.subschemeι
  have hfull : Set.range q = Set.univ := by
    simp [q, I, Scheme.IdealSheafData.range_subschemeι]
  have : IsReduced Y := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  change GeometricallyReduced (q ≫ p)
  apply geometricallyReduced_of_isGeometricallyReducedAt_genericPoints (q ≫ p)
  intro ξ hξ
  let z := q ξ
  have hz : z ∈ genericPoints (pullback f g : Scheme.{u}) :=
    genericPoints_map_of_closedImmersion_fullRange q hfull ξ hξ
  have hx : pullback.fst f g z ∈ genericPoints X :=
    genericPoints_map_of_flat (pullback.fst f g) z hz
  let x : ι := ⟨pullback.fst f g z, hx⟩
  exact isGeometricallyReducedAt_of_reducedTensorProduct k ↥F f q ξ hξ (hFgeo x)

end AlgebraicGeometry
