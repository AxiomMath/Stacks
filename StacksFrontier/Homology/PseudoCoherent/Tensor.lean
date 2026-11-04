module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.DerivedTensorBoundedAbove
public import StacksFrontier.Homology.Tor.DerivedTensorFunctorLargeUniverse

/-!
# Pseudo-coherence of derived tensor products

Let `R` be a commutative ring. The derived tensor product of two pseudo-coherent objects of
`D(R)` is pseudo-coherent, and quantitatively: if `K` is `n`-pseudo-coherent with no cohomology
above `a` and `L` is `m`-pseudo-coherent with no cohomology above `b`, then `K ⊗ᴸ L` is
`max (m + a) (n + b)`-pseudo-coherent.

## Main results

* `StacksDraft.PseudoCoherence.pseudoCoherent_derivedTensorProduct_largeUniverse`: Stacks 0DJE,
  for the derived tensor product `CochainComplex.DerivedTensor.derivedTensorProduct` of
  Stacks 064M, with the modules in a universe independent of the ring's.
* `StacksDraft.PseudoCoherence.pseudoCoherent_canonicalDerivedTensorProduct`: the equal-universe
  reading, for the canonical derived tensor bifunctor
  `CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R` (Stacks 0BYI).
* `StacksDraft.PseudoCoherence.pseudoCoherent_derivedTensorProduct`: the same conclusion for an
  arbitrary bifunctor on `D(R)` carrying a certificate identifying it with the termwise tensor
  product on K-flat complexes.

## Implementation notes

The argument is carried out for a family of triangulated endofunctors `derivedTensor M` of
`D(R)`, indexed by the object tensored with, together with a certificate: on a pair of K-flat
complexes `P`, `Y` the object `Q(P) ⊗ᴸ Q(Y)` is `Q(P ⊗ Y)`. The derived tensor product of
Stacks 064M is such a family, with one endofunctor per object and no functoriality in that
object; a bifunctor induces one through `kFlatPairComparison_of_bifunctor`.

The module universe is `max u v`, independent of the ring's universe `u`. The termwise tensor
product is taken with the monoidal structure of
`StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse`, a local instance in the section
that uses it; at `v := u` its tensor product is Mathlib's.

## References

* [Stacks Project, Tag 0DJE](https://stacks.math.columbia.edu/tag/0DJE)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.Pretriangulated

open scoped ZeroObject

namespace StacksDraft.PseudoCoherence

universe u v

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-! ### Projective representatives -/

/-- An object of `D^{≤ a}(R)` is represented by a complex of projective modules vanishing in
degrees above `a`: this is Stacks 05T7 for the class of projective modules,
`CochainComplex.DerivedTensor.exists_projective_isStrictlyLE_representative`. -/
private lemma exists_projective_representative
    (K : DerivedCategory (ModuleCat.{max u v} R)) (a : ℤ) [K.IsLE a] :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∀ i, Projective (P.X i)) ∧ P.IsStrictlyLE a ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) :=
  CochainComplex.DerivedTensor.exists_projective_isStrictlyLE_representative K a

/-- Alias of `CochainComplex.DerivedTensor.kFlat_of_projective_isStrictlyLE`. -/
private alias kFlat_of_projective := CochainComplex.DerivedTensor.kFlat_of_projective_isStrictlyLE

/-- A coproduct of finite modules all but finitely many of which vanish is finite. -/
private lemma finite_coproduct_of_isZero {ι : Type} (F : ι → ModuleCat.{max u v} R)
    [∀ j, Module.Finite R (F j)] [HasCoproduct F] (s : Finset ι)
    (hs : ∀ j, j ∉ s → IsZero (F j)) : Module.Finite R (∐ F : ModuleCat R) := by
  classical
  let G : s → ModuleCat.{max u v} R := fun j => F j
  have : Module.Finite R (∐ G : ModuleCat R) :=
    Module.Finite.equiv (ModuleCat.coprodIsoDirectSum G).symm.toLinearEquiv
  let f : (∐ G : ModuleCat R) ⟶ ∐ F := Sigma.desc (fun j => Sigma.ι F j)
  have : Epi f := by
    constructor
    intro Z g h heq
    apply Sigma.hom_ext
    intro j
    by_cases hj : j ∈ s
    · simpa only [f, Category.assoc, Sigma.ι_desc_assoc] using
        congrArg (fun k => Sigma.ι G ⟨j, hj⟩ ≫ k) heq
    · exact (hs j hj).eq_of_src _ _
  exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance)

/-! ### Termwise tensor products of complexes -/

section LargeUniverse

attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive

/-- The termwise tensor product of two bounded above complexes of finite free modules has finite
free terms. -/
private lemma tensor_finiteFree (P Q : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hP : IsBoundedAboveFiniteFree P) (hQ : IsBoundedAboveFiniteFree Q) (i : ℤ) :
    Module.Finite R ((HomologicalComplex.tensorObj P Q).X i) ∧
      Module.Free R ((HomologicalComplex.tensorObj P Q).X i) := by
  classical
  obtain ⟨a, ha⟩ := hP.upperBound
  obtain ⟨b, hb⟩ := hQ.upperBound
  have := ha
  have := hb
  let F : {pq : ℤ × ℤ // pq.1 + pq.2 = i} → ModuleCat.{max u v} R :=
    fun pq => P.X pq.1.1 ⊗ Q.X pq.1.2
  have : ∀ j, Module.Finite R (F j) := fun j => by
    have := (hP.finiteFree j.1.1).1
    have := (hQ.finiteFree j.1.2).1
    exact Module.Finite.tensorProduct R _ _
  have : ∀ j, Module.Free R (F j) := fun j => by
    have := (hP.finiteFree j.1.1).2
    have := (hQ.finiteFree j.1.2).2
    show Module.Free R (TensorProduct R (P.X j.1.1) (Q.X j.1.2))
    infer_instance
  show Module.Finite R (∐ F : ModuleCat R) ∧ Module.Free R (∐ F : ModuleCat R)
  refine ⟨?_, Module.Free.of_equiv (ModuleCat.coprodIsoDirectSum F).symm.toLinearEquiv⟩
  let s : Finset {pq : ℤ × ℤ // pq.1 + pq.2 = i} :=
    (Finset.Icc (i - b) a).map
      ⟨fun p => ⟨(p, i - p), by omega⟩, fun p q h => congrArg (fun z => z.1.1) h⟩
  apply finite_coproduct_of_isZero F s
  intro j hj
  have hj' : ¬(i - b ≤ j.1.1 ∧ j.1.1 ≤ a) := by
    intro h
    apply hj
    apply Finset.mem_map.mpr
    refine ⟨j.1.1, Finset.mem_Icc.mpr h, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl (show i - j.1.1 = j.1.2 from by have := j.2; omega)
  by_cases hp : a < j.1.1
  · exact (tensorRight _).map_isZero (P.isZero_of_isStrictlyLE a _ hp)
  · exact (tensorLeft _).map_isZero (Q.isZero_of_isStrictlyLE b _ (by
      have := j.2
      omega))

/-- The flip isomorphism of the termwise tensor product of two complexes. -/
private lemma tensor_flip_iso (P Q : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    Nonempty (HomologicalComplex.tensorObj P Q ≅ HomologicalComplex.tensorObj Q P) := by
  let e : (((curriedTensor (ModuleCat.{max u v} R)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).obj Q ≅
      (((curriedTensor (ModuleCat.{max u v} R)).flip.mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj P).obj Q :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p => HomologicalComplex.Hom.isoOfComponents
        (fun q => (TensorProduct.comm R (P.X p) (Q.X q)).toModuleIso)
        (by intros; ext : 1; apply TensorProduct.ext'; intros; rfl))
      (by intros; ext q : 2; apply TensorProduct.ext'; intros; rfl)
  exact ⟨HomologicalComplex₂.total.mapIso e (ComplexShape.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso Q P
      (curriedTensor (ModuleCat.{max u v} R)) (ComplexShape.up ℤ)⟩

/-! ### A certified derived tensor product -/

variable (derivedTensor : DerivedCategory (ModuleCat.{max u v} R) →
  (DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R)))

/-- The certificate: on a pair of K-flat complexes, the derived tensor product is computed by
their termwise tensor product, transported along representatives. This is verbatim the
`comparison` field of `CochainComplex.DerivedTensor.DerivedTensorProduct` at
`K = Q(P)`, `L = Q(Y)`. -/
private abbrev KFlatPairComparison : Prop :=
  ∀ (K L : DerivedCategory (ModuleCat.{max u v} R))
    (P Y : CochainComplex (ModuleCat.{max u v} R) ℤ),
    (K ≅ DerivedCategory.Q.obj P) → (L ≅ DerivedCategory.Q.obj Y) → P.KFlat → Y.KFlat →
    Nonempty ((derivedTensor L).obj K ≅
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Y))

/-- A certified derived tensor product of objects of `D^{≤ a}` and `D^{≤ b}` lies in
`D^{≤ a + b}`. -/
private lemma derivedTensor_isLE (cert : KFlatPairComparison derivedTensor)
    (K L : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ) [K.IsLE a] [L.IsLE b] :
    ((derivedTensor L).obj K).IsLE (a + b) :=
  CochainComplex.DerivedTensor.isLE_of_kFlatComparison ((derivedTensor L).obj K) K L a b
    (cert K L)

/-- A certified derived tensor product is symmetric on bounded above objects. -/
private lemma derivedTensor_flip_iso (cert : KFlatPairComparison derivedTensor)
    (K L : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ) [K.IsLE a] [L.IsLE b] :
    Nonempty ((derivedTensor L).obj K ≅ (derivedTensor K).obj L) := by
  obtain ⟨P, hP, hPa, ⟨eP⟩⟩ := exists_projective_representative K a
  obtain ⟨Q, hQ, hQb, ⟨eQ⟩⟩ := exists_projective_representative L b
  have := hPa
  have := hQb
  obtain ⟨e₁⟩ := cert K L P Q eP eQ (kFlat_of_projective P a hP) (kFlat_of_projective Q b hQ)
  obtain ⟨e₂⟩ := cert L K Q P eQ eP (kFlat_of_projective Q b hQ) (kFlat_of_projective P a hP)
  obtain ⟨e⟩ := tensor_flip_iso P Q
  exact ⟨e₁ ≪≫ DerivedCategory.Q.mapIso e ≪≫ e₂.symm⟩

/-- A certified derived tensor product of pseudo-coherent objects is pseudo-coherent. -/
private lemma pseudoCoherent_tensor (cert : KFlatPairComparison derivedTensor)
    (K L : DerivedCategory (ModuleCat.{max u v} R))
    (hK : IsPseudoCoherent K) (hL : IsPseudoCoherent L) :
    IsPseudoCoherent ((derivedTensor L).obj K) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := hK
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := hL
  obtain ⟨a, ha⟩ := hP.upperBound
  obtain ⟨b, hb⟩ := hQ.upperBound
  have := ha
  have := hb
  have kflat (X : CochainComplex (ModuleCat.{max u v} R) ℤ) (c : ℤ) [X.IsStrictlyLE c]
      (hX : IsBoundedAboveFiniteFree X) : X.KFlat := by
    have : ∀ i : ℤ, Module.Flat R (X.X i) := fun i => by
      have := (hX.finiteFree i).2
      infer_instance
    exact CochainComplex.KFlat.kFlat_of_flat X c
  obtain ⟨e⟩ := cert K L P Q eP.symm eQ.symm (kflat P a hP) (kflat Q b hQ)
  exact ⟨HomologicalComplex.tensorObj P Q,
    ⟨⟨a + b, TotalTensorComplex.tensor_isStrictlyLE P Q a b⟩,
      tensor_finiteFree P Q hP hQ⟩, ⟨e.symm⟩⟩

/-! ### Transport of approximations -/

/-- A morphism which is an isomorphism on cohomology above `n` and surjective in degree `n` is
surjective on cohomology in every degree `i ≥ n`. -/
private lemma epi_homologyMap_of_le
    {X Y : DerivedCategory (ModuleCat.{max u v} R)} (f : X ⟶ Y) (n : ℤ)
    (hf : ∀ i : ℤ, n < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map f))
    (he : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map f))
    (i : ℤ) (hi : n ≤ i) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map f) := by
  rcases hi.eq_or_lt with rfl | hn
  · exact he
  · have := hf i hn
    infer_instance

/-- An `m`-pseudo-coherent approximation composes with a morphism which is an isomorphism on
cohomology above `n` and surjective in degree `n`. -/
private lemma pseudoCoherentFrom_of_map
    {X Y : DerivedCategory (ModuleCat.{max u v} R)} (f : X ⟶ Y) (n : ℤ)
    (hf : ∀ i : ℤ, n < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map f))
    (he : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map f))
    (hX : IsPseudoCoherentFrom X n) : IsPseudoCoherentFrom Y n := by
  obtain ⟨E, hE, α, hα, hαe⟩ := hX
  refine ⟨E, hE, α ≫ f, fun i hi => ?_, ?_⟩
  · have := hf i hi
    have := hα i hi
    rw [Functor.map_comp]
    infer_instance
  · rw [Functor.map_comp]
    infer_instance

/-- The same, transporting `t`-pseudo-coherence for `t ≥ n`. -/
private lemma pseudoCoherentFrom_of_map_of_le
    {X Y : DerivedCategory (ModuleCat.{max u v} R)} (f : X ⟶ Y) (n t : ℤ) (hnt : n ≤ t)
    (hf : ∀ i : ℤ, n < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map f))
    (he : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map f))
    (hX : IsPseudoCoherentFrom X t) : IsPseudoCoherentFrom Y t := by
  exact pseudoCoherentFrom_of_map f t (fun i hi => hf i (lt_of_le_of_lt hnt hi))
    (epi_homologyMap_of_le f n hf he t hnt) hX

/-- An object of `D^{≤ n - 1}` is `n`-pseudo-coherent, approximated by the zero complex. -/
private lemma pseudoCoherentFrom_of_isLE
    (K : DerivedCategory (ModuleCat.{max u v} R)) (n : ℤ) [K.IsLE (n - 1)] :
    IsPseudoCoherentFrom K n := by
  let E : CochainComplex (ModuleCat.{max u v} R) ℤ := 0
  have hE : IsBoundedFiniteFree E := by
    refine ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩, fun i => ?_⟩
    have : Subsingleton (E.X i) := ModuleCat.isZero_iff_subsingleton.mp
      ((HomologicalComplex.eval (ModuleCat.{max u v} R) (ComplexShape.up ℤ) i).map_isZero
        (isZero_zero _))
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton R _⟩
  refine ⟨E, hE, 0, fun i hi => ?_, ?_⟩
  · exact ((DerivedCategory.homologyFunctor _ i).map_isZero
      (DerivedCategory.Q.map_isZero (isZero_zero _))).isIso
      (DerivedCategory.isZero_of_isLE K (n - 1) i (by omega)) _
  · exact (DerivedCategory.isZero_of_isLE K (n - 1) n (by omega)).epi _

/-- A pseudo-coherent object has vanishing cohomology in all sufficiently large degrees. -/
private lemma pseudoCoherent_vanishes_above {K : DerivedCategory (ModuleCat.{max u v} R)}
    (hK : IsPseudoCoherent K) :
    ∃ a : ℤ, ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨a, ha⟩ := hE.upperBound
  have := ha
  exact ⟨a, fun i hi => (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj E) a i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).mapIso e.symm)⟩

/-- Tensoring an approximation with an object of `D^{≤ b}` shifts its range by `b`. -/
private lemma tensor_map_approximation (cert : KFlatPairComparison derivedTensor)
    [∀ M : DerivedCategory (ModuleCat.{max u v} R), (derivedTensor M).CommShift ℤ]
    [∀ M : DerivedCategory (ModuleCat.{max u v} R), (derivedTensor M).IsTriangulated]
    {X Y : DerivedCategory (ModuleCat.{max u v} R)}
    (f : X ⟶ Y) (L : DerivedCategory (ModuleCat.{max u v} R)) (n b : ℤ)
    (hf : ∀ i : ℤ, n < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map f))
    (he : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map f))
    [L.IsLE b] :
    (∀ i : ℤ, n + b < i → IsIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map
        ((derivedTensor L).map f))) ∧
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) (n + b)).map
        ((derivedTensor L).map f)) := by
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  have hZ : Z.IsLE (n - 1) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    have hfi := epi_homologyMap_of_le f n hf he i (by omega)
    have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) (i + 1)).map
        T.mor₁) := hf (i + 1) (by omega)
    exact (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1)).isZero_of_both_zeros
      ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mp hfi)
      ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
        T hT i (i + 1)).mp inferInstance)
  have hTZ := derivedTensor_isLE derivedTensor cert Z L (n - 1) b
  let S := (derivedTensor L).mapTriangle.obj T
  have hS : S ∈ distTriang _ := (derivedTensor L).map_distinguished T hT
  have : S.obj₃.IsLE (n - 1 + b) := hTZ
  have hz (i : ℤ) (hi : n + b ≤ i) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj S.obj₃) :=
    DerivedCategory.isZero_of_isLE _ (n - 1 + b) i (by omega)
  have epi (i : ℤ) (hi : n + b ≤ i) :
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map S.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff S hS i).mpr
      ((hz i hi).eq_zero_of_tgt _)
  refine ⟨fun i hi => ?_, epi (n + b) le_rfl⟩
  have := epi i (by omega)
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map S.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      S hS (i - 1) i (by omega)).mpr ((hz (i - 1) (by omega)).eq_zero_of_src _)
  show IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map S.mor₁)
  exact isIso_of_mono_of_epi _

/-! ### Stacks 0DJE -/

/-- If `K` is `n`-pseudo-coherent with no cohomology above `a` and `L` is `m`-pseudo-coherent
with no cohomology above `b`, then a certified `K ⊗ᴸ L` is
`max (m + a) (n + b)`-pseudo-coherent. -/
private lemma pseudoCoherentFrom_derivedTensor (cert : KFlatPairComparison derivedTensor)
    [∀ M : DerivedCategory (ModuleCat.{max u v} R), (derivedTensor M).CommShift ℤ]
    [∀ M : DerivedCategory (ModuleCat.{max u v} R), (derivedTensor M).IsTriangulated]
    (K L : DerivedCategory (ModuleCat.{max u v} R)) (n m a b : ℤ)
    (hK : IsPseudoCoherentFrom K n)
    (hKa : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K))
    (hL : IsPseudoCoherentFrom L m)
    (hLb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) j).obj L)) :
    IsPseudoCoherentFrom ((derivedTensor L).obj K) (max (m + a) (n + b)) := by
  have hKa' : K.IsLE a := (DerivedCategory.isLE_iff K a).mpr hKa
  have hLb' : L.IsLE b := (DerivedCategory.isLE_iff L b).mpr hLb
  set t := max (m + a) (n + b) with ht
  by_cases hna : n ≤ a
  · obtain ⟨E, hE, α, hα, hαe⟩ := hK
    have hpc {X : CochainComplex (ModuleCat.{max u v} R) ℤ} (hX : IsBoundedAboveFiniteFree X) :
        IsPseudoCoherent (DerivedCategory.Q.obj X) := ⟨X, hX, ⟨Iso.refl _⟩⟩
    have hEa : ∀ i : ℤ, a < i → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
          (DerivedCategory.Q.obj E)) := by
      intro i hi
      have := hα i (lt_of_le_of_lt hna hi)
      exact (hKa i hi).of_iso (asIso
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map α))
    obtain ⟨P, ε, hP, hPa, hε⟩ :=
      (pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
        (DerivedCategory.Q.obj E) a).2.2 (hpc hE.isBoundedAboveFiniteFree) hEa
    have := hPa
    have := hε
    let α' := ε ≫ α
    have hα' : ∀ i : ℤ, n < i → IsIso
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map α') := by
      intro i hi
      have := hα i hi
      dsimp only [α']
      rw [Functor.map_comp]
      infer_instance
    have hα'e : Epi
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n).map α') := by
      dsimp only [α']
      rw [Functor.map_comp]
      infer_instance
    obtain ⟨F, hF, β, hβ, hβe⟩ := hL
    have hFP := pseudoCoherent_tensor derivedTensor cert (DerivedCategory.Q.obj F)
      (DerivedCategory.Q.obj P) (hpc hF.isBoundedAboveFiniteFree)
      (hpc ⟨⟨a, hPa⟩, fun i => ⟨(hP i).1, (hP i).2⟩⟩)
    have hFPt : IsPseudoCoherentFrom
        ((derivedTensor (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj F)) t :=
      (pseudoCoherent_iff_all _).mp hFP t
    obtain ⟨hβt, hβte⟩ := tensor_map_approximation derivedTensor cert β
      (DerivedCategory.Q.obj P) m a hβ hβe
    have hLP : IsPseudoCoherentFrom
        ((derivedTensor (DerivedCategory.Q.obj P)).obj L) t :=
      pseudoCoherentFrom_of_map_of_le _ (m + a) t (le_max_left _ _) hβt hβte hFPt
    obtain ⟨e⟩ := derivedTensor_flip_iso derivedTensor cert L
      (DerivedCategory.Q.obj P) b a
    have hPL : IsPseudoCoherentFrom
        ((derivedTensor L).obj (DerivedCategory.Q.obj P)) t :=
      pseudoCoherentFrom_of_map e.hom t (fun _ _ => inferInstance) inferInstance hLP
    obtain ⟨hαt, hαte⟩ := tensor_map_approximation derivedTensor cert α' L n b hα' hα'e
    exact pseudoCoherentFrom_of_map_of_le _ (n + b) t (le_max_right _ _) hαt hαte hPL
  · have := derivedTensor_isLE derivedTensor cert K L a b
    have : ((derivedTensor L).obj K).IsLE (t - 1) :=
      DerivedCategory.TStructure.t.isLE_of_le _ (a + b) (t - 1) (by rw [ht]; omega)
    exact pseudoCoherentFrom_of_isLE _ t

/-- Both halves of Stacks 0DJE for a family certified on pairs of K-flat complexes: the
quantitative bound and the qualitative statement. -/
private lemma pseudoCoherent_tensor_core (cert : KFlatPairComparison derivedTensor)
    [∀ M : DerivedCategory (ModuleCat.{max u v} R), (derivedTensor M).CommShift ℤ]
    [∀ M : DerivedCategory (ModuleCat.{max u v} R), (derivedTensor M).IsTriangulated]
    (K L : DerivedCategory (ModuleCat.{max u v} R)) :
    (∀ n m a b : ℤ,
      IsPseudoCoherentFrom K n →
      (∀ i : ℤ, a < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K)) →
      IsPseudoCoherentFrom L m →
      (∀ j : ℤ, b < j →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) j).obj L)) →
      IsPseudoCoherentFrom ((derivedTensor L).obj K) (max (m + a) (n + b))) ∧
      (IsPseudoCoherent K → IsPseudoCoherent L →
        IsPseudoCoherent ((derivedTensor L).obj K)) := by
  refine ⟨fun n m a b hK hKa hL hLb =>
    pseudoCoherentFrom_derivedTensor derivedTensor cert K L n m a b hK hKa hL hLb, ?_⟩
  intro hK hL
  apply (pseudoCoherent_iff_all ((derivedTensor L).obj K)).mpr
  intro q
  obtain ⟨a, hKa⟩ := pseudoCoherent_vanishes_above hK
  obtain ⟨b, hLb⟩ := pseudoCoherent_vanishes_above hL
  have hKn : IsPseudoCoherentFrom K (q - b) := (pseudoCoherent_iff_all K).mp hK _
  have hLm : IsPseudoCoherentFrom L (q - a) := (pseudoCoherent_iff_all L).mp hL _
  simpa only [sub_add_cancel, max_self] using
    pseudoCoherentFrom_derivedTensor derivedTensor cert K L (q - b) (q - a) a b
      hKn hKa hLm hLb

/-- A bifunctor whose comparison with the termwise tensor product is given at a pair of K-flat
complexes certifies the family `L ↦ - ⊗ᴸ L` it induces. -/
private lemma kFlatPairComparison_of_bifunctor
    (derivedTensor : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R))
    (cert : ∀ P Y : CochainComplex (ModuleCat.{max u v} R) ℤ, P.KFlat → Y.KFlat →
      ((derivedTensor.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Y) ≅
        DerivedCategory.Q.obj (HomologicalComplex.tensorObj P Y))) :
    KFlatPairComparison (fun M => derivedTensor.flip.obj M) := by
  intro K L P Y eP eY hP hY
  exact ⟨(derivedTensor.flip.mapIso eY).app K ≪≫
    (derivedTensor.flip.obj (DerivedCategory.Q.obj Y)).mapIso eP ≪≫ cert P Y hP hY⟩

/-- A family compared, as in Stacks 064M, with the tensor-total functor of every K-flat
resolution is certified. -/
private lemma kFlatPairComparison_of_resolutionComparison
    (hcomp : ∀ (M : DerivedCategory (ModuleCat.{max u v} R))
      (P Y : CochainComplex (ModuleCat.{max u v} R) ℤ) (f : Y ⟶ P), QuasiIso f → Y.KFlat →
      ((DerivedCategory.Qh (C := ModuleCat.{max u v} R)).obj
        ((HomotopyCategory.quotient (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).obj P) ≅ M) →
      Nonempty (DerivedCategory.Qh ⋙ derivedTensor M ≅ Tright Y ⋙ DerivedCategory.Qh)) :
    KFlatPairComparison derivedTensor := by
  intro K L P Y eP eY _hP hY
  have eY' : (DerivedCategory.Qh (C := ModuleCat.{max u v} R)).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Y) ≅ L :=
    (DerivedCategory.quotientCompQhIso _).app Y ≪≫ eY.symm
  obtain ⟨e⟩ := hcomp L Y Y (𝟙 Y) inferInstance hY eY'
  exact ⟨(derivedTensor L).mapIso (eP ≪≫ ((DerivedCategory.quotientCompQhIso _).app P).symm) ≪≫
    e.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≪≫
    (DerivedCategory.quotientCompQhIso _).app (HomologicalComplex.tensorObj P Y)⟩

/-- **Stacks 0DJE.** If `K` is `n`-pseudo-coherent and has no cohomology above `a`, and `L` is
`m`-pseudo-coherent and has no cohomology above `b`, then their derived tensor product
`K ⊗ᴸ L` is `max (m + a) (n + b)`-pseudo-coherent. Moreover, the derived tensor product of two
pseudo-coherent objects is pseudo-coherent.

The modules live in a universe `max u v` independent of the ring's universe `u`, as in the
source, and the derived tensor product is the one of Stacks 064M,
`CochainComplex.DerivedTensor.derivedTensorProduct`: one endofunctor
`derivedTensorProduct L` of `D(R)` for each object `L`. -/
@[stacks 0DJE]
public theorem pseudoCoherent_derivedTensorProduct_largeUniverse
    (K L : DerivedCategory (ModuleCat.{max u v} R)) :
    (∀ n m a b : ℤ,
      IsPseudoCoherentFrom K n →
      (∀ i : ℤ, a < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K)) →
      IsPseudoCoherentFrom L m →
      (∀ j : ℤ, b < j →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) j).obj L)) →
      IsPseudoCoherentFrom
        ((CochainComplex.DerivedTensor.derivedTensorProduct L).obj K)
        (max (m + a) (n + b))) ∧
      (IsPseudoCoherent K → IsPseudoCoherent L →
        IsPseudoCoherent ((CochainComplex.DerivedTensor.derivedTensorProduct L).obj K)) :=
  pseudoCoherent_tensor_core CochainComplex.DerivedTensor.derivedTensorProduct
    (kFlatPairComparison_of_resolutionComparison _
      (fun M P Y f _ hY e =>
        (CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution
          M P Y f hY e).1)) K L

end LargeUniverse

/-- Let `derivedTensor` be a bifunctor on `D(R)` whose functors `- ⊗ᴸ L` are triangulated and
which is identified with the termwise tensor product whenever the second variable is the image of
a K-flat complex. If `K` is `n`-pseudo-coherent with no cohomology above `a`, and `L` is
`m`-pseudo-coherent with no cohomology above `b`, then their derived tensor product is
`max (m + a) (n + b)`-pseudo-coherent; moreover the derived tensor product of two
pseudo-coherent objects is pseudo-coherent. -/
public theorem pseudoCoherent_derivedTensorProduct
    (derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    [∀ M : DerivedCategory (ModuleCat.{u} R), (derivedTensor.flip.obj M).CommShift ℤ]
    [∀ M : DerivedCategory (ModuleCat.{u} R), (derivedTensor.flip.obj M).IsTriangulated]
    (cert : ∀ Y : CochainComplex (ModuleCat.{u} R) ℤ, Y.KFlat →
      (DerivedCategory.Q ⋙ derivedTensor.flip.obj (DerivedCategory.Q.obj Y) ≅
        MonoidalCategory.tensorRight Y ⋙ DerivedCategory.Q))
    (K L : DerivedCategory (ModuleCat.{u} R)) :
    (∀ n m a b : ℤ,
      IsPseudoCoherentFrom K n →
      (∀ i : ℤ, a < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) →
      IsPseudoCoherentFrom L m →
      (∀ j : ℤ, b < j →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj L)) →
      IsPseudoCoherentFrom ((derivedTensor.flip.obj L).obj K) (max (m + a) (n + b))) ∧
      (IsPseudoCoherent K → IsPseudoCoherent L →
        IsPseudoCoherent ((derivedTensor.flip.obj L).obj K)) :=
  pseudoCoherent_tensor_core.{u, u} (fun M => derivedTensor.flip.obj M)
    (kFlatPairComparison_of_bifunctor.{u, u} derivedTensor
      (fun P Y _ hY => (cert Y hY).app P)) K L

/-- **Stacks 0DJE** at a module universe equal to the ring's, for the canonical derived tensor
bifunctor of Stacks 0BYI, `CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R`. -/
public theorem pseudoCoherent_canonicalDerivedTensorProduct
    (K L : DerivedCategory (ModuleCat.{u} R)) :
    (∀ n m a b : ℤ,
      IsPseudoCoherentFrom K n →
      (∀ i : ℤ, a < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) →
      IsPseudoCoherentFrom L m →
      (∀ j : ℤ, b < j →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).obj L)) →
      IsPseudoCoherentFrom
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.flip.obj L).obj K)
        (max (m + a) (n + b))) ∧
      (IsPseudoCoherent K → IsPseudoCoherent L →
        IsPseudoCoherent
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.flip.obj
            L).obj K)) :=
  pseudoCoherent_tensor_core.{u, u} _
    (kFlatPairComparison_of_bifunctor.{u, u} _
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).comparison) K L

end StacksDraft.PseudoCoherence
