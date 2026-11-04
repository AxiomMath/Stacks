module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import StacksFrontier.Algebra.Homology.Resolution.Existence
public import StacksFrontier.Algebra.Homology.Resolution.FreeResolutionLargeUniverse
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Cycles
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
public import StacksFrontier.Algebra.Homology.SpectralSequence.HomologicalFiltration
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Algebra.Homology.Embedding.ExtendMap

@[expose] public section

/-!
# Spectral sequences for tensoring a chain complex with a module

For a bounded-below chain complex `K` of modules and a module `M`, a free resolution of
`M` gives a double complex. Its two filtrations give spectral sequences computing the
homology of the derived tensor product. One starts with the Tor groups of the homology
of `K`; the other starts with the Tor groups of the terms of `K`.

## Main definitions

* `moduleTensorBifunctor` is the tensor-product bifunctor for modules whose
  carriers may lie in a larger universe than the ring.
* `TorInDegree` extends Tor to an integer grading by zero in negative degrees.
* `torInDegreeMap` is the map induced on integrally graded Tor in the first variable.
* `tensorFiltrationSteps` defines the two coordinate filtrations.
* `TorSpectralSequences` packages the two spectral sequences of the tensor product with a free
  resolution together with the resolution and the data of their convergence. Its fields are the
  clauses of Tag 061Z.

## Main results

* `nonempty_torSpectralSequences` produces a `TorSpectralSequences`, i.e. the two spectral
  sequences associated to the tensor product with a free resolution.
* `exists_spectral_sequences_tor_homology_and_terms` is the same statement with the fields of
  `TorSpectralSequences` spelled out as an iterated existential. It is the form Tag 061Z is
  stated in and the one consumers destructure.

## Implementation notes

The chain complex is represented by the cochain complex obtained by degree
reversal, so that `K_i` is written `K.X (-i)`. The derived tensor product is represented
by the total tensor complex with a free resolution of the module. We use the underlying
tensor-product bifunctor directly, allowing the module carriers to lie in a universe
larger than that of the ring. The ring, the terms of `K`, and `M` have independent
universes; `ULift` puts both arguments in a common module category before taking the
tensor product. The coordinate filtrations are sums of the images of the canonical
summand inclusions. Page projections identify the entire spectral sequences with these
filtered-complex constructions, including differentials and transition isomorphisms.
Convergence uses the induced filtration on homology and the unique comparison
compatible with cycle classes. The two spectral-sequence shapes use respectively the
bidegrees `(r - 1, -r)` and `(-r, r - 1)`, which reproduce the differentials in the
homological indexing.

Two definitions here are deliberately opaque `def`s rather than reducible abbreviations:
`tensorBicomplex`, the double complex, and `tensorStep`, the step of a coordinate filtration.
Reducible, every `isDefEq` on a type mentioning either descends into
`mapBifunctorHomologicalComplex` and into `Subobject.underlying` -- hence `ThinSkeleton`
representatives and `Classical.choose` -- and that descent, not the size of any one term, is what
exhausted the budget of every declaration downstream. The comparisons that genuinely need the
unfolding ask for it in declarations that carry their own budget. The package is assembled from
two halves, `TorSpectralSequenceSecond` and `TorSpectralSequenceFirst`, for the same reason: a
heartbeat ceiling is per declaration.

## References

* [The Stacks Project, Tag 061Z](https://stacks.math.columbia.edu/tag/061Z)
* [The Stacks Project, Tag 012X](https://stacks.math.columbia.edu/tag/012X)
* [The Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CochainComplex.Tor

universe u v w

/-- The tensor-product bifunctor on modules, formulated without requiring the ring and
the module carriers to lie in the same universe. -/
@[simps]
public noncomputable def moduleTensorBifunctor (R : Type u) [CommRing R] :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R where
  obj X :=
    { obj := fun Y ↦ ModuleCat.of R (TensorProduct R X Y)
      map := fun f ↦ ModuleCat.ofHom (f.hom.lTensor X)
      map_id := fun Y ↦ by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        rfl
      map_comp := fun f g ↦ ModuleCat.hom_ext (LinearMap.lTensor_comp _ _ _) }
  map f :=
    { app := fun Y ↦ ModuleCat.ofHom (f.hom.rTensor Y)
      naturality := by
        intro Y Z g
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        rfl }
  map_id X := by
    ext Y x y
    rfl
  map_comp f g := by
    ext Y x y
    rfl

/-- Tensoring with a fixed module is additive. -/
public instance (R : Type u) [CommRing R] (X : ModuleCat.{max u v} R) :
    ((moduleTensorBifunctor R).obj X).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.lTensor_add X f.hom g.hom)

/-- The tensor-product bifunctor preserves zero morphisms in the first variable. -/
public instance (R : Type u) [CommRing R] :
    (moduleTensorBifunctor.{u, v} R).PreservesZeroMorphisms where
  map_zero X Y := by
    ext Z z
    change ((0 : X →ₗ[R] Y).rTensor Z)
      (show TensorProduct R X Z from z) =
        (0 : TensorProduct R X Z →ₗ[R] TensorProduct R Y Z) z
    rw [LinearMap.rTensor_zero]

/-- Tor in an integral degree, extended by the zero object in negative degrees. -/
public noncomputable abbrev TorInDegree (R : Type u) [CommRing R] (n : ℤ)
    (X Y : ModuleCat.{max u v} R) : ModuleCat.{max u v} R :=
  if _h : 0 ≤ n then (((moduleTensorBifunctor R).obj X).leftDerived n.toNat).obj Y
  else ModuleCat.of R (ULift.{v} (Fin 0 → R))

/-- The map on integrally graded Tor induced in the first variable. -/
public noncomputable def torInDegreeMap (R : Type u) [CommRing R] (n : ℤ)
    {X X' : ModuleCat.{max u v} R} (f : X ⟶ X') (Y : ModuleCat.{max u v} R) :
    TorInDegree R n X Y ⟶ TorInDegree R n X' Y := by
  unfold TorInDegree
  split
  next h => exact (NatTrans.leftDerived ((moduleTensorBifunctor R).map f) n.toNat).app Y
  next h => exact 0

/-- The two canonical filtrations of the tensor total complex. Each step is the
sum of the images of precisely the summands whose selected chain degree is at most `p`.
In cochain indexing these are the direct sums with coordinate at least `-p` of 012X. -/
public noncomputable def tensorFiltrationSteps (R : Type u) [CommRing R]
    (K P : CochainComplex (ModuleCat.{max u v} R) ℤ) (axis : Bool) (p n : ℤ) :
    Submodule R ((HomologicalComplex.mapBifunctor K P (moduleTensorBifunctor R)
      (ComplexShape.up ℤ)).X (-n)) :=
  ⨆ (i : ℤ) (j : ℤ) (_ : if axis then -i ≤ p else -j ≤ p),
    LinearMap.range (HomologicalComplex.ιMapBifunctorOrZero K P (moduleTensorBifunctor R)
      (ComplexShape.up ℤ) i j (-n)).hom

private noncomputable def freeChain {R : Type u} [CommRing R]
    {M : ModuleCat.{max u v} R} (D : FreeResolutionData R M)
    (hD : D.IsExact) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (D.F n))
    (fun n ↦ ModuleCat.ofHom (D.d n))
    (fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ (hD.2.2 n).le ⟨x, rfl⟩))

private noncomputable def freeChainAug {R : Type u} [CommRing R]
    {M : ModuleCat.{max u v} R} (D : FreeResolutionData R M)
    (hD : D.IsExact) :
    freeChain D hD ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj M :=
  (ChainComplex.toSingle₀Equiv (freeChain D hD) M).symm
    ⟨ModuleCat.ofHom D.ε, ModuleCat.hom_ext (LinearMap.ext fun x ↦ hD.2.1.le ⟨x, rfl⟩)⟩

private theorem freeChain_exactAt_succ {R : Type u} [CommRing R]
    {M : ModuleCat.{max u v} R} (D : FreeResolutionData R M)
    (hD : D.IsExact) (n : ℕ) : (freeChain D hD).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
  show LinearMap.range (((freeChain D hD).d (n + 2) (n + 1)).hom) =
    LinearMap.ker (((freeChain D hD).d (n + 1) n).hom)
  simp only [freeChain, ChainComplex.of.d, dite_true,
    show n + 2 = (n + 1) + 1 by omega]
  convert hD.2.2 n using 1
  rfl

private theorem freeChainAug_quasiIso {R : Type u} [CommRing R]
    {M : ModuleCat.{max u v} R} (D : FreeResolutionData R M)
    (hD : D.IsExact) : QuasiIso (freeChainAug D hD) := by
  constructor
  intro n
  cases n with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) (by rfl) (by rfl)]
      constructor
      · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
        show LinearMap.range (((freeChain D hD).d 1 0).hom) =
          LinearMap.ker ((freeChainAug D hD).f 0).hom
        simp only [freeChain, freeChainAug]
        exact hD.2.1
      · apply (ModuleCat.epi_iff_surjective _).2
        convert hD.1 using 1 <;> rfl
  | succ n =>
      exact (quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj M n)).2
        (freeChain_exactAt_succ D hD n)

private noncomputable def freeProjectiveResolution {R : Type u} [CommRing R]
    {M : ModuleCat.{max u v} R} (D : FreeResolutionData R M)
    (hD : D.IsExact) (hFree : D.IsFree) : ProjectiveResolution M where
  complex := freeChain D hD
  π := freeChainAug D hD
  projective n := by
    have := hFree n
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis R (D.F n))
  quasiIso := freeChainAug_quasiIso D hD

private theorem freeCochain_terms {R : Type u} [CommRing R]
    {M : ModuleCat.{max u v} R} (D : FreeResolutionData R M)
    (hD : D.IsExact) (hFree : D.IsFree) (i : ℤ) :
    Module.Free R ((freeProjectiveResolution D hD hFree).cochainComplex.X i) := by
  let Q := freeProjectiveResolution D hD hFree
  by_cases hi : i ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hi
    have hFk : Module.Free R (Q.complex.X k) := hFree k
    exact Module.Free.of_equiv (Q.cochainComplexXIso (-k) k).symm.toLinearEquiv
  · have := ModuleCat.isZero_iff_subsingleton.mp
      (CochainComplex.isZero_of_isStrictlyLE Q.cochainComplex 0 i (by omega))
    exact Module.Free.of_subsingleton R _

private noncomputable def torIsoFreeResolution
    (R : Type u) [CommRing R] (X M : ModuleCat.{max u v} R)
    (D : FreeResolutionData R M) (hD : D.IsExact) (hFree : D.IsFree)
    (j : ℕ) :
    TorInDegree R (j : ℤ) X M ≅
      (((moduleTensorBifunctor R).obj X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (freeProjectiveResolution D hD hFree).complex |>.homology j := by
  simpa [TorInDegree] using
    (freeProjectiveResolution D hD hFree).isoLeftDerivedObj
      ((moduleTensorBifunctor R).obj X) j

private theorem torInDegree_isZero_of_neg
    (R : Type u) [CommRing R] (X M : ModuleCat.{max u v} R)
    (j : ℤ) (hj : j < 0) : IsZero (TorInDegree R j X M) := by
  have h : TorInDegree.{u, v} R j X M = ModuleCat.of R (ULift.{v} (Fin 0 → R)) :=
    dite_eq_right (by omega : ¬ 0 ≤ j)
  rw [h]
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

/-- The decidability instance of `0 ≤ (k : ℤ)` evaluates to `isTrue`. -/
private theorem decLe_zero_natCast (k : ℕ) : Int.decLe 0 (k : ℤ) = isTrue (by omega) :=
  Subsingleton.elim _ _

private theorem torInDegreeMap_id
    (R : Type u) [CommRing R] (n : ℤ)
    (X M : ModuleCat.{max u v} R) :
    torInDegreeMap R n (𝟙 X) M = 𝟙 (TorInDegree R n X M) := by
  cases n with
  | ofNat k =>
      simp [torInDegreeMap, decLe_zero_natCast]
  | negSucc k =>
      exact (torInDegree_isZero_of_neg R X M (Int.negSucc k) (by omega)).eq_of_src _ _

private theorem torInDegreeMap_comp
    (R : Type u) [CommRing R] (n : ℤ)
    {X Y Z : ModuleCat.{max u v} R} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : ModuleCat.{max u v} R) :
    torInDegreeMap R n (f ≫ g) M =
      torInDegreeMap R n f M ≫ torInDegreeMap R n g M := by
  cases n with
  | ofNat k =>
      simp [torInDegreeMap, NatTrans.leftDerived_comp, decLe_zero_natCast]
  | negSucc k =>
      exact (torInDegree_isZero_of_neg R X M (Int.negSucc k) (by omega)).eq_of_src _ _

private noncomputable def torInDegreeFunctor
    (R : Type u) [CommRing R] (n : ℤ)
    (M : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R where
  obj X := TorInDegree R n X M
  map f := torInDegreeMap R n f M
  map_id X := torInDegreeMap_id R n X M
  map_comp f g := torInDegreeMap_comp R n f g M

/-- Tensoring with a fixed module in the second argument. -/
private noncomputable def tensorRight
    (R : Type u) [CommRing R] (P : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R where
  obj X := ((moduleTensorBifunctor R).obj X).obj P
  map f := ((moduleTensorBifunctor R).map f).app P
  map_id X := by
    change ((moduleTensorBifunctor R).map (𝟙 X)).app P = 𝟙 _
    exact congrArg (fun α ↦ α.app P) ((moduleTensorBifunctor R).map_id X)
  map_comp f g := by
    change ((moduleTensorBifunctor R).map (f ≫ g)).app P =
      ((moduleTensorBifunctor R).map f).app P ≫
        ((moduleTensorBifunctor R).map g).app P
    simp only [Functor.map_comp, NatTrans.comp_app]

private theorem tensorRight_additive
    (R : Type u) [CommRing R] (P : ModuleCat.{max u v} R) :
    (tensorRight R P).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.rTensor_add P f.hom g.hom)

attribute [local instance] tensorRight_additive

private theorem tensorRight_preservesHomology_of_flat
    (R : Type u) [CommRing R] (P : ModuleCat.{max u v} R)
    (hFlat : Module.Flat R P) : (tensorRight R P).PreservesHomology := by
  have := hFlat
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
  exact Module.Flat.rTensor_exact P
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS)

private theorem tensorRight_preservesHomology_of_free
    (R : Type u) [CommRing R] (P : ModuleCat.{max u v} R)
    (hFree : Module.Free R P) : (tensorRight R P).PreservesHomology := by
  have := hFree
  exact tensorRight_preservesHomology_of_flat R P inferInstance

private noncomputable def tensorRight_homologyIso_of_free
    (R : Type u) [CommRing R] (P : ModuleCat.{max u v} R)
    (hFree : Module.Free R P)
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ) :
    (((tensorRight R P).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i ≅
      (tensorRight R P).obj (K.homology i) := by
  let : (tensorRight R P).PreservesHomology :=
    tensorRight_preservesHomology_of_free R P hFree
  exact (K.sc i).mapHomologyIso (tensorRight R P)

private theorem coordinateSubmodule_eq_iSup
    {R : Type u} [CommRing R]
    (B : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [B.HasTotal (ComplexShape.up ℤ)] (axis : Bool) (p n : ℤ)
    (Z : Subobject ((B.total (ComplexShape.up ℤ)).X n))
    (hι : ∀ i j (hij : i + j = n), (if axis then p ≤ i else p ≤ j) →
      imageSubobject (B.ιTotal (ComplexShape.up ℤ) i j n hij) ≤ Z)
    (hZ : ∀ W : Subobject ((B.total (ComplexShape.up ℤ)).X n),
      (∀ i j (hij : i + j = n), (if axis then p ≤ i else p ≤ j) →
        imageSubobject (B.ιTotal (ComplexShape.up ℤ) i j n hij) ≤ W) → Z ≤ W) :
    ModuleCat.subobjectModule _ Z =
      ⨆ (i : ℤ) (j : ℤ) (_ : if axis then p ≤ i else p ≤ j),
        LinearMap.range (B.ιTotalOrZero (ComplexShape.up ℤ) i j n).hom := by
  classical
  let e := ModuleCat.subobjectModule ((B.total (ComplexShape.up ℤ)).X n)
  apply le_antisymm
  · apply (e.le_symm_apply).mp
    apply hZ
    intro i j hij hp
    apply (e.le_symm_apply).mpr
    show ModuleCat.subobjectModule _ (imageSubobject _) ≤ _
    rw [subobjectModule_imageSubobject]
    exact le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le hp (by
      rw [B.ιTotalOrZero_eq (ComplexShape.up ℤ) i j n hij])))
  · refine iSup_le fun i ↦ iSup_le fun j ↦ iSup_le fun hp ↦ ?_
    by_cases hij : i + j = n
    · rw [B.ιTotalOrZero_eq (ComplexShape.up ℤ) i j n hij,
        ← subobjectModule_imageSubobject]
      exact e.monotone (hι i j hij hp)
    · rw [B.ιTotalOrZero_eq_zero (ComplexShape.up ℤ) i j n hij]
      simp

/-- A termwise tensor product vanishes when either factor does. -/
private theorem isZero_tensor_of_bound
    (R : Type u) [CommRing R] (K P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (a b : ℤ) (hK : ∀ i, a < i → IsZero (K.X i)) (hP : ∀ j, b < j → IsZero (P.X j))
    (i j : ℤ) (h : a < i ∨ b < j) :
    IsZero (((moduleTensorBifunctor R).obj (K.X i)).obj (P.X j)) := by
  rcases h with h | h
  · exact ((moduleTensorBifunctor R).map_isZero (hK i h)).obj (P.X j)
  · exact ((moduleTensorBifunctor R).obj (K.X i)).map_isZero (hP j h)

private theorem tensorFiltrationSteps_eq_bot
    (R : Type u) [CommRing R]
    (K P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (a b : ℤ) (hK : ∀ i, a < i → IsZero (K.X i))
    (hP : ∀ j, b < j → IsZero (P.X j)) (axis : Bool) (p n : ℤ)
    (hp : if axis then p < -a else p < -b) :
    tensorFiltrationSteps R K P axis p n = ⊥ := by
  apply le_antisymm ?_ bot_le
  refine iSup_le fun i ↦ iSup_le fun j ↦ iSup_le fun h ↦ ?_
  have hz := isZero_tensor_of_bound R K P a b hK hP i j
    (by cases axis <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp h <;> omega)
  rw [hz.eq_of_src
    (HomologicalComplex.ιMapBifunctorOrZero K P (moduleTensorBifunctor R)
      (ComplexShape.up ℤ) i j (-n)) 0]
  simp

private theorem tensorFiltrationSteps_eq_top
    (R : Type u) [CommRing R]
    (K P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (a b : ℤ) (hK : ∀ i, a < i → IsZero (K.X i))
    (hP : ∀ j, b < j → IsZero (P.X j)) (axis : Bool) (p n : ℤ)
    (hp : if axis then n + b ≤ p else n + a ≤ p) :
    tensorFiltrationSteps R K P axis p n = ⊤ := by
  let L := tensorFiltrationSteps R K P axis p n
  have hz : ModuleCat.ofHom L.mkQ = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    change i + j = -n at hij
    by_cases h : if axis then -i ≤ p else -j ≤ p
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (Submodule.Quotient.mk_eq_zero L).mpr
      apply (le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le h le_rfl)) :
        LinearMap.range (HomologicalComplex.ιMapBifunctorOrZero K P
          (moduleTensorBifunctor R) (ComplexShape.up ℤ) i j (-n)).hom ≤ L)
      refine ⟨x, ?_⟩
      rw [HomologicalComplex.ιMapBifunctorOrZero_eq K P (moduleTensorBifunctor R)
        (ComplexShape.up ℤ) i j (-n) hij]
      rfl
    · exact (isZero_tensor_of_bound R K P a b hK hP i j
        (by cases axis <;> simp only [Bool.false_eq_true, ↓reduceIte] at hp h <;> omega)).eq_of_src
        _ _
  exact Submodule.eq_top_iff'.mpr fun x ↦
    (Submodule.Quotient.mk_eq_zero L).mp (congrArg (fun f ↦ f x) hz)

private theorem tensorFiltrationSteps_finite
    (R : Type u) [CommRing R]
    (K P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (a b : ℤ) (hK : ∀ i, a < i → IsZero (K.X i))
    (hP : ∀ j, b < j → IsZero (P.X j)) (axis : Bool) (n : ℤ) :
    ∃ c d : ℤ, c ≤ d ∧ tensorFiltrationSteps R K P axis c n = ⊥ ∧
      tensorFiltrationSteps R K P axis d n = ⊤ := by
  refine ⟨min (-a) (-b) - 1, max (min (-a) (-b) - 1) (max (n + a) (n + b)),
    le_max_left _ _, ?_, ?_⟩
  · apply tensorFiltrationSteps_eq_bot R K P a b hK hP
    cases axis <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · apply tensorFiltrationSteps_eq_top R K P a b hK hP
    cases axis <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

section TorBridge

variable (R : Type u) [CommRing R]

private noncomputable def tensorComplexFunctor (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    ModuleCat.{max u v} R ⥤ CochainComplex (ModuleCat.{max u v} R) ℤ where
  obj X := (((moduleTensorBifunctor R).obj X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  map f := (NatTrans.mapHomologicalComplex ((moduleTensorBifunctor R).map f) _).app P
  map_id X := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp]
    rfl

private theorem tensorComplexFunctor_additive (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (tensorComplexFunctor R P).Additive where
  map_add {X Y f g} := by
    ext j : 1
    exact ModuleCat.hom_ext (LinearMap.rTensor_add _ f.hom g.hom)

attribute [local instance] tensorComplexFunctor_additive

private theorem torInDegreeMap_projectiveResolution
    {X X' : ModuleCat.{max u v} R} (f : X ⟶ X') {M : ModuleCat.{max u v} R}
    (Q : ProjectiveResolution M) (k : ℕ) :
    torInDegreeMap R (k : ℤ) f M =
      (Q.isoLeftDerivedObj ((moduleTensorBifunctor R).obj X) k).hom ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R)
        (ComplexShape.down ℕ) k).map
        ((NatTrans.mapHomologicalComplex ((moduleTensorBifunctor R).map f)
          (ComplexShape.down ℕ)).app Q.complex) ≫
      (Q.isoLeftDerivedObj ((moduleTensorBifunctor R).obj X') k).inv := by
  unfold torInDegreeMap
  simpa [TorInDegree, decLe_zero_natCast, Int.toNat_natCast] using
    Q.leftDerived_app_eq ((moduleTensorBifunctor R).map f) k

private noncomputable def torComponentIso {M : ModuleCat.{max u v} R} (Q : ProjectiveResolution M)
    (k : ℕ) (X : ModuleCat.{max u v} R) :
    ((tensorComplexFunctor R Q.cochainComplex).obj X).homology (-(k : ℤ)) ≅
      TorInDegree R (k : ℤ) X M :=
  (HomologicalComplex.homologyFunctor _ _ (-(k : ℤ))).mapIso
      (HomologicalComplex.mapHomologicalComplexExtendIso ((moduleTensorBifunctor R).obj X)
        Q.complex ComplexShape.embeddingDownNat).symm ≪≫
    HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingDownNat (j := k) rfl ≪≫
    (Q.isoLeftDerivedObj ((moduleTensorBifunctor R).obj X) k).symm

/-- Tor in nonnegative degree `k` is the homology in degree `-k` of the tensor product with
the cochain complex of a projective resolution, naturally in the first variable. -/
private noncomputable def torNatIsoNat {M : ModuleCat.{max u v} R} (Q : ProjectiveResolution M)
    (k : ℕ) :
    tensorComplexFunctor R Q.cochainComplex ⋙
        HomologicalComplex.homologyFunctor _ _ (-(k : ℤ)) ≅
      torInDegreeFunctor R (k : ℤ) M :=
  NatIso.ofComponents (fun X ↦ torComponentIso R Q k X) (by
    intro X Y f
    change _ = _ ≫ torInDegreeMap R (k : ℤ) f M
    rw [torInDegreeMap_projectiveResolution R f Q k]
    simp only [torComponentIso]
    have h1 := congrArg (HomologicalComplex.homologyMap · (-(k : ℤ)))
      (HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality_functor
        ((moduleTensorBifunctor R).obj X) Q.complex ((moduleTensorBifunctor R).map f)
        ComplexShape.embeddingDownNat)
    simp only [HomologicalComplex.homologyMap_comp] at h1
    erw [reassoc_of% h1]
    erw [HomologicalComplex.extendHomologyIso_hom_naturality_assoc]
    have key : ∀ {A B C' D' E' : ModuleCat.{max u v} R} (a : A ≅ B) (b : B ≅ C')
        (c : D' ≅ C') (g : C' ⟶ E'),
        (a ≪≫ b ≪≫ c.symm).hom ≫ c.hom ≫ g = a.hom ≫ b.hom ≫ g := by
      simp
    refine Eq.trans ?_ (key _ _ _ _).symm
    rfl)

/-- Tor in every integral degree `j` is the homology in degree `-j` of the tensor product with
the cochain complex of a projective resolution, naturally in the first variable. -/
private noncomputable def torNatIso {M : ModuleCat.{max u v} R} (Q : ProjectiveResolution M)
    (j : ℤ) :
    tensorComplexFunctor R Q.cochainComplex ⋙
        HomologicalComplex.homologyFunctor _ _ (-j) ≅
      torInDegreeFunctor R j M := by
  cases j with
  | ofNat k => exact torNatIsoNat R Q k
  | negSucc k =>
      have h₁ : ∀ X : ModuleCat.{max u v} R,
          IsZero (((tensorComplexFunctor R Q.cochainComplex).obj X).homology
            (-(Int.negSucc k))) := fun X ↦
        ShortComplex.isZero_homology_of_isZero_X₂ _
          (((moduleTensorBifunctor R).obj X).map_isZero
            (CochainComplex.isZero_of_isStrictlyLE Q.cochainComplex 0 _ (by omega)))
      exact NatIso.ofComponents
        (fun X ↦ (h₁ X).iso (torInDegree_isZero_of_neg R X M (Int.negSucc k) (by omega)))
        (fun _ ↦ (h₁ _).eq_of_src _ _)

/-- Tensoring a complex of modules termwise with a complex of free modules preserves
homology. -/
private theorem tensorComplexFunctor_preservesHomology
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (hP : ∀ i, Module.Free R (P.X i)) :
    (tensorComplexFunctor R P).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  rw [HomologicalComplex.exact_iff_degreewise_exact]
  intro j
  have := tensorRight_preservesHomology_of_free R (P.X j) (hP j)
  exact hS.map (tensorRight R (P.X j))

private noncomputable def tensorHomologyIso
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (hP : ∀ i, Module.Free R (P.X i))
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ) :
    (((tensorComplexFunctor R P).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i ≅
      (tensorComplexFunctor R P).obj (K.homology i) := by
  let := tensorComplexFunctor_preservesHomology R P hP
  exact (K.sc i).mapHomologyIso (tensorComplexFunctor R P)

private theorem freeProjectiveResolution_cochainComplex
    {M : ModuleCat.{max u v} R} (D : FreeResolutionData R M)
    (hD : D.IsExact) (hFree : D.IsFree) :
    (∀ i : ℤ, Module.Free R ((freeProjectiveResolution D hD hFree).cochainComplex.X i)) ∧
      (∀ i : ℤ, 0 < i → IsZero ((freeProjectiveResolution D hD hFree).cochainComplex.X i)) ∧
      Nonempty ((freeProjectiveResolution D hD hFree).cochainComplex.homology 0 ≅ M) ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((freeProjectiveResolution D hD hFree).cochainComplex.homology i)) := by
  let Q := freeProjectiveResolution D hD hFree
  exact ⟨freeCochain_terms D hD hFree,
    fun i hi ↦ CochainComplex.isZero_of_isStrictlyLE Q.cochainComplex 0 i hi,
    ⟨isoOfQuasiIsoAt Q.π' 0 ≪≫
      HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M⟩,
    fun i hi ↦ IsZero.of_iso
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M i hi)
      (isoOfQuasiIsoAt Q.π' i)⟩

end TorBridge
section Assembly

open FilteredComplexSpectralSequence Opposite

/-- The double complex of termwise tensor products of two cochain complexes of modules.

Deliberately a `def` and not an `abbrev`. As a reducible abbreviation every `isDefEq` on a type
mentioning it unfolds `mapBifunctorHomologicalComplex` applied to the module tensor bifunctor,
and that descent -- not the size of any one term -- is what exhausts the elaboration budget of
every declaration downstream. Opaque, the comparisons that genuinely need the unfolding ask for
it explicitly, in declarations that carry their own budget. -/
@[ega "III 6.3.2" "special case", ega "III 7.6.4" "more general"]
private noncomputable def tensorBicomplex (R : Type u) [CommRing R]
    (K P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((moduleTensorBifunctor R).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj P

/-- The tensor bicomplex has a total complex. Needed because `tensorBicomplex` is opaque, so the
instance for the underlying `mapBifunctorHomologicalComplex` term is not found through it. -/
private instance tensorBicomplex_hasTotal (R : Type u) [CommRing R]
    (K P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (tensorBicomplex R K P).HasTotal (ComplexShape.up ℤ) := by
  unfold tensorBicomplex
  infer_instance

variable (R : Type u) [CommRing R] (K P : CochainComplex (ModuleCat.{max u v} R) ℤ)

/-- The step of the filtration of the tensor total complex cut out by the weight `w`.

Deliberately a `def` wrapping `HomologicalComplex₂.stepSubobject`, which is a reducible
abbreviation. Left reducible, every `isDefEq` on a term mentioning the filtration descends into
`imageSubobject (… totalProjector …)`, and that descent -- not the size of any one term -- is
what exhausts the elaboration budget of the assembly. Opaque, the two comparisons that do need
the unfolding ask for it in their own declarations. -/
private noncomputable def tensorStep (w : ℤ → ℤ → ℤ) (p n : ℤ) :
    Subobject (((tensorBicomplex R K P).total (ComplexShape.up ℤ)).X n) :=
  (tensorBicomplex R K P).stepSubobject w p n


private theorem homologicalFiltrationOfSubobjects_step_eq (axis : Bool) (w : ℤ → ℤ → ℤ)
    (hw : ∀ q i j : ℤ, q ≤ w i j ↔ if axis then q ≤ i else q ≤ j)
    (hanti : ∀ p p' n : ℤ, p ≤ p' →
      tensorStep R K P w p' n ≤ tensorStep R K P w p n)
    (hd : ∀ p n m : ℤ, m = n + 1 →
      (tensorStep R K P w p m).Factors
        ((tensorStep R K P w p n).arrow ≫
          ((tensorBicomplex R K P).total (ComplexShape.up ℤ)).d n m)) :
    (homologicalFiltrationOfSubobjects _ (tensorStep R K P w)
      hanti hd).step = tensorFiltrationSteps R K P axis := by
  funext p n
  rw [homologicalFiltrationOfSubobjects_step]
  refine (coordinateSubmodule_eq_iSup (tensorBicomplex R K P) axis (-p) (-n)
      (tensorStep R K P w (-p) (-n))
      (fun i j hij hp ↦ HomologicalComplex₂.imageSubobject_ιTotal_le_totalProjector
        (K := tensorBicomplex R K P) (fun i j ↦ -p ≤ w i j) i j (-n) hij ((hw (-p) i j).2 hp))
      (fun W hW ↦ HomologicalComplex₂.totalProjector_le_of_forall
        (K := tensorBicomplex R K P) (fun i j ↦ -p ≤ w i j) (-n) W
        (fun i j hij hP ↦ hW i j hij ((hw (-p) i j).1 hP)))).trans ?_
  simp only [tensorBicomplex, tensorFiltrationSteps,
    HomologicalComplex.ιMapBifunctorOrZero, neg_le]
  rfl

/-- Conjugating a morphism by two composite isomorphisms. -/
private theorem conj_iso_trans {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : ModuleCat.{max u v} R}
    (a₁ : X₁ ≅ Y₁) (a₂ : X₂ ≅ Y₂) (n₁ : Y₁ ≅ Z₁) (n₂ : Y₂ ≅ Z₂) (d : X₁ ⟶ X₂) (h : Y₁ ⟶ Y₂)
    (hh : a₁.inv ≫ d ≫ a₂.hom = h) :
    (a₁ ≪≫ n₁).inv ≫ d ≫ (a₂ ≪≫ n₂).hom = n₁.inv ≫ h ≫ n₂.hom := by
  subst hh
  simp

-- The next two definitions read a page of the spectral sequence of a filtration by subobjects
-- through the cohomology of the underlying double complex, for an *arbitrary* double complex
-- `B` and an arbitrary filtration `G`, with the page comparison (`γ`, resp. `β`) taken as a
-- parameter. Stating them at that generality is what makes them elaborate at all. Specialized
-- to the concrete tensor bicomplex they do not: the specialized forms
-- produce three deterministic timeouts at 1600000 heartbeats (two at `isDefEq`, one at `whnf`),
-- while these generic forms compile with no error and no timeout. The reason is that `B`, `G`
-- and `hanti` are opaque binders here, so `isDefEq` cannot descend into `tensorBicomplex` and
-- `stepSubobject`, which are reducible abbreviations; specializing hands that unfolding path
-- back to the elaborator, and the search — not the size of any one term — is the cost.

/-- Read on the reindexed second page, the spectral sequence of a decreasing filtration by
subobjects of a double complex is the iterated cohomology of the double complex. -/
private noncomputable def reindexed_page_two_iso
    (B : HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [B.HasTotal (ComplexShape.up ℤ)]
    (G : ℤ → ∀ n : ℤ, Subobject ((B.total (ComplexShape.up ℤ)).X n))
    (hanti : ∀ p p' n : ℤ, p ≤ p' → G p' n ≤ G p n)
    (γ : ∀ p q : ℤ,
      ((spectralSequence (B.total (ComplexShape.up ℤ)) G hanti).page 2 zero_le_two).X (p, q) ≅
        (B.homology q).homology p)
    (i j : ℤ) :
    ((homologicalSpectralSequence (B.total (ComplexShape.up ℤ)) G hanti false 2
        (by omega)).page 2).X (i, j) ≅ (B.homology (-i)).homology (-j) :=
  torIndexedSpectralSequence_pageIso
      (spectralSequence (B.total (ComplexShape.up ℤ)) G hanti) false 2 (by omega) 2 (by omega)
      (i, j) ≪≫ γ (-j) (-i)

/-- Read on the reindexed first page, the spectral sequence of a decreasing filtration by
subobjects of a double complex is the cohomology of the columns of the double complex. -/
private noncomputable def reindexed_page_one_iso
    (B : HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [B.HasTotal (ComplexShape.up ℤ)]
    (G : ℤ → ∀ n : ℤ, Subobject ((B.total (ComplexShape.up ℤ)).X n))
    (hanti : ∀ p p' n : ℤ, p ≤ p' → G p' n ≤ G p n)
    (β : ∀ p q : ℤ,
      ((spectralSequence (B.total (ComplexShape.up ℤ)) G hanti).page 1 zero_le_one).X (p, q) ≅
        (B.X p).homology q)
    (i j : ℤ) :
    ((homologicalSpectralSequence (B.total (ComplexShape.up ℤ)) G hanti true 1
        (by omega)).page 1).X (i, j) ≅ (B.X (-i)).homology (-j) :=
  torIndexedSpectralSequence_pageIso
      (spectralSequence (B.total (ComplexShape.up ℤ)) G hanti) true 1 (by omega) 1 (by omega)
      (i, j) ≪≫ β (-i) (-j)

/-- Read on the reindexed first page, the differential of the spectral sequence of the first
filtration is the map induced on the cohomology of the columns of the double complex. -/
private theorem reindexed_first_page_d
    (B : HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [B.HasTotal (ComplexShape.up ℤ)]
    (G : ℤ → ∀ n : ℤ, Subobject ((B.total (ComplexShape.up ℤ)).X n))
    (hanti : ∀ p p' n : ℤ, p ≤ p' → G p' n ≤ G p n)
    (β : ∀ p q : ℤ,
      ((spectralSequence (B.total (ComplexShape.up ℤ)) G hanti).page 1 zero_le_one).X (p, q) ≅
        (B.X p).homology q)
    (hβd : ∀ p q : ℤ,
      ((spectralSequence (B.total (ComplexShape.up ℤ)) G hanti).page 1 zero_le_one).d
          (p, q) (p + 1, q) ≫ (β (p + 1) q).hom =
        (β p q).hom ≫ HomologicalComplex.homologyMap (B.d p (p + 1)) q)
    (i j : ℤ) :
    (reindexed_page_one_iso R B G hanti β i j).inv ≫
        ((homologicalSpectralSequence (B.total (ComplexShape.up ℤ)) G hanti true 1
          (by omega)).page 1).d (i, j) (i - 1, j) ≫
        (reindexed_page_one_iso R B G hanti β (i - 1) j).hom =
      HomologicalComplex.homologyMap (B.d (-i) (-(i - 1))) (-j) := by
  -- The conclusion is stated through `reindexed_page_one_iso` and `homologicalSpectralSequence`,
  -- which is how every consumer spells it. Converting to the raw spelling is one definitional
  -- step, but a costly one: the codomain of the page identification is indexed by
  -- `reverseBidegree true (i, j)` and the domain of `β` by `(-i, -j)`, and `reverseBidegree` is
  -- not reducible, so the unifier compares the two page objects instead -- descending through
  -- `Subobject.underlying` into `ThinSkeleton` representatives and `Classical.choose`, with
  -- 38452 unfoldings of `Subobject.representative`. It is paid once, here.
  show (torIndexedSpectralSequence_pageIso
          (spectralSequence (B.total (ComplexShape.up ℤ)) G hanti) true 1 zero_le_one 1 le_rfl
          (i, j) ≪≫ β (-i) (-j)).inv ≫
        ((torIndexedSpectralSequence (spectralSequence (B.total (ComplexShape.up ℤ)) G hanti)
          true 1 zero_le_one).page 1 le_rfl).d (i, j) (i - 1, j) ≫
        (torIndexedSpectralSequence_pageIso
          (spectralSequence (B.total (ComplexShape.up ℤ)) G hanti) true 1 zero_le_one 1 le_rfl
          (i - 1, j) ≪≫ β (-(i - 1)) (-j)).hom =
      HomologicalComplex.homologyMap (B.d (-i) (-(i - 1))) (-j)
  have hβd' : ∀ p q p' : ℤ, p' = p + 1 →
      ((spectralSequence (B.total (ComplexShape.up ℤ)) G hanti).page 1 zero_le_one).d
          (p, q) (p', q) ≫ (β p' q).hom =
        (β p q).hom ≫ HomologicalComplex.homologyMap (B.d p p') q := by
    rintro p q _ rfl
    exact hβd p q
  refine (conj_iso_trans R _ _ _ _ _ _
    (torIndexedSpectralSequence_d_true_conj
      (spectralSequence (B.total (ComplexShape.up ℤ)) G hanti) 1 zero_le_one 1 le_rfl
      i j (i - 1) j)).trans ?_
  -- `conj_iso_trans` fixes the middle objects from the codomains of the page identifications,
  -- so the goal spells them `(E.page _).X (reverseBidegree true (i - 1, j))` while `hβd'`
  -- spells them `(E.page _).X (-(i - 1), -j)`. The two agree by `rfl`, but `reverseBidegree`
  -- is not reducible, so `rw` cannot see through it; discharging the goal by `exact`, which
  -- unifies at default transparency, avoids the mismatch entirely.
  exact (Iso.inv_comp_eq (β (-i) (-j))).mpr (hβd' (-i) (-j) (-(i - 1)) (by omega))

-- The nine arguments of the double-complex page comparison are each instantiated at the whole
-- total complex, so this application alone exceeds the default elaboration budget. Isolating it
-- in its own declaration keeps that cost out of the budget of the main assembly below, which
-- would otherwise pay for it inside a deeply nested existential.
/-- Read on the first page, the spectral sequence of the filtration by the first coordinate of a
double complex is the cohomology of its columns, compatibly with the differentials. This is the
second conclusion of `HomologicalComplex₂.exists_iso_pages_totalFiltration₁`. -/
private theorem exists_first_page_iso_totalFiltration₁
    (B : HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [B.HasTotal (ComplexShape.up ℤ)]
    (G : ℤ → ∀ n : ℤ, Subobject ((B.total (ComplexShape.up ℤ)).X n))
    (hG : ∀ p n : ℤ, G p n =
      Subobject.mk ((B.totalFiltration₁.filtration.ι.app (op p)).f n))
    (hanti : ∀ p p' n : ℤ, p ≤ p' → G p' n ≤ G p n) :
    ∃ β : ∀ p q : ℤ,
        ((spectralSequence (B.total (ComplexShape.up ℤ)) G hanti).page 1 zero_le_one).X (p, q) ≅
          (B.X p).homology q,
      ∀ p q : ℤ,
        ((spectralSequence (B.total (ComplexShape.up ℤ)) G hanti).page 1 zero_le_one).d
            (p, q) (p + 1, q) ≫ (β (p + 1) q).hom =
          (β p q).hom ≫ HomologicalComplex.homologyMap (B.d p (p + 1)) q :=
  (B.exists_iso_pages_totalFiltration₁ G hG
    _ (fun _ _ _ ↦ rfl) _ (fun _ _ _ ↦ rfl)
    (spectralSequence _ _ hanti) (fun r p q n hr hn ↦ eIso _ _ hanti r p q n hr hn)
    (fun r p q n hr hn ↦ ⟨deltaCycles _ _ r p n, deltaCycles_arrow _ _ r p n,
      den_π_eIso_inv_comp_d _ _ hanti r hr p q n hn⟩)).2.1

-- As for the first filtration, this one application of the page comparison is budgeted on its
-- own rather than inside the main assembly.
/-- Read on the second page, the spectral sequence of the filtration by the second coordinate of
a double complex is the iterated cohomology of the double complex. This is the third conclusion
of `HomologicalComplex₂.exists_iso_pages_totalFiltration₂`. -/
@[ega "0 11.3.2" "special case"]
private theorem nonempty_second_page_iso_totalFiltration₂
    (B : HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [B.HasTotal (ComplexShape.up ℤ)]
    (G : ℤ → ∀ n : ℤ, Subobject ((B.total (ComplexShape.up ℤ)).X n))
    (hG : ∀ p n : ℤ, G p n =
      Subobject.mk ((B.totalFiltration₂.filtration.ι.app (op p)).f n))
    (hanti : ∀ p p' n : ℤ, p ≤ p' → G p' n ≤ G p n) :
    ∀ p q : ℤ, Nonempty
      (((spectralSequence (B.total (ComplexShape.up ℤ)) G hanti).page 2 zero_le_two).X (p, q) ≅
        (B.homology q).homology p) :=
  (B.exists_iso_pages_totalFiltration₂ G hG
    _ (fun _ _ _ ↦ rfl) _ (fun _ _ _ ↦ rfl)
    (spectralSequence _ _ hanti) (fun r p q n hr hn ↦ eIso _ _ hanti r p q n hr hn)
    (fun r p q n hr hn ↦ ⟨deltaCycles _ _ r p n, deltaCycles_arrow _ _ r p n,
      den_π_eIso_inv_comp_d _ _ hanti r hr p q n hn⟩)).2.2

-- The rows of the tensor bicomplex and the termwise tensor product with the resolution are the
-- same complex by unfolding, but not syntactically, so composing the page identification of the
-- second filtration with the Tor identification forces that comparison. Doing it here gives it
-- its own budget: a heartbeat ceiling is per declaration, so performing it inside the assembly
-- below charged it to the same budget as everything else there.
/-- The second page of the spectral sequence of the second filtration, read through the iterated
cohomology of the tensor bicomplex, is the Tor of the homology of `K`. -/
private noncomputable def page_two_iso_tor
    {M : ModuleCat.{max u v} R} (Q : ProjectiveResolution M)
    (Pres : CochainComplex (ModuleCat.{max u v} R) ℤ) (hPres : Pres = Q.cochainComplex)
    (hPfree : ∀ i : ℤ, Module.Free R (Pres.X i)) (i j : ℤ) :
    ((tensorBicomplex R K Pres).homology (-i)).homology (-j) ≅
      TorInDegree.{u, v} R j (K.homology (-i)) M := by
  subst hPres
  exact (HomologicalComplex.homologyFunctor _ _ (-j)).mapIso
      (tensorHomologyIso R Q.cochainComplex hPfree K (-i)) ≪≫
    (torNatIso R Q j).app (K.homology (-i))

-- As for `page_two_iso_tor`, the row of the bicomplex at `-i` and the tensor product of `K.X (-i)`
-- with the resolution agree by unfolding only, so this identification is budgeted on its own.
/-- The first page of the spectral sequence of the first filtration, read through the cohomology
of the columns of the tensor bicomplex, is the Tor of the terms of `K`. -/
private noncomputable def page_one_iso_tor
    {M : ModuleCat.{max u v} R} (Q : ProjectiveResolution M)
    (Pres : CochainComplex (ModuleCat.{max u v} R) ℤ) (hPres : Pres = Q.cochainComplex)
    (i j : ℤ) :
    ((tensorBicomplex R K Pres).X (-i)).homology (-j) ≅
      TorInDegree.{u, v} R j (K.X (-i)) M := by
  subst hPres
  exact (torNatIso R Q j).app (K.X (-i))

set_option maxHeartbeats 1600000 in
-- Conjugating the first differential by the Tor identification of the columns exceeds the
-- default elaboration budget.
/-- For an arbitrary double complex `B`, a decreasing filtration `G` of its total complex by
subobjects and an arbitrary identification `τ` of the cohomology of the columns of `B` with Tor
satisfying `hτ`, the first differential of the reindexed spectral sequence read through the page
identification and `τ` is the map `hτ` transports.

Every argument is a binder, and every spelling matches `reindexed_first_page_d` syntactically, so
instantiating this at the tensor bicomplex in the assembly leaves the unifier nothing to solve. -/
private theorem conj_first_page_d_tor (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (B : HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [B.HasTotal (ComplexShape.up ℤ)]
    (G : ℤ → ∀ n : ℤ, Subobject ((B.total (ComplexShape.up ℤ)).X n))
    (hanti : ∀ p p' n : ℤ, p ≤ p' → G p' n ≤ G p n)
    (β : ∀ p q : ℤ,
      ((spectralSequence (B.total (ComplexShape.up ℤ)) G hanti).page 1 zero_le_one).X (p, q) ≅
        (B.X p).homology q)
    (hβd : ∀ p q : ℤ,
      ((spectralSequence (B.total (ComplexShape.up ℤ)) G hanti).page 1 zero_le_one).d
          (p, q) (p + 1, q) ≫ (β (p + 1) q).hom =
        (β p q).hom ≫ HomologicalComplex.homologyMap (B.d p (p + 1)) q)
    {M : ModuleCat.{max u v} R}
    (τ : ∀ i j : ℤ, (B.X (-i)).homology (-j) ≅ TorInDegree.{u, v} R j (K.X (-i)) M)
    (hτ : ∀ i j : ℤ,
      (τ i j).inv ≫
          HomologicalComplex.homologyMap (B.d (-i) (-(i - 1))) (-j) ≫ (τ (i - 1) j).hom =
        torInDegreeMap.{u, v} R j (K.d (-i) (-(i - 1))) M)
    (i j : ℤ) :
    (reindexed_page_one_iso R B G hanti β i j ≪≫ τ i j).inv ≫
        ((homologicalSpectralSequence (B.total (ComplexShape.up ℤ)) G hanti true 1
          (by omega)).page 1).d (i, j) (i - 1, j) ≫
        (reindexed_page_one_iso R B G hanti β (i - 1) j ≪≫ τ (i - 1) j).hom =
      torInDegreeMap.{u, v} R j (K.d (-i) (-(i - 1))) M :=
  Eq.trans
    (conj_iso_trans R
      (reindexed_page_one_iso R B G hanti β i j)
      (reindexed_page_one_iso R B G hanti β (i - 1) j)
      (τ i j) (τ (i - 1) j)
      (((homologicalSpectralSequence (B.total (ComplexShape.up ℤ)) G hanti true 1
        (by omega)).page 1).d (i, j) (i - 1, j))
      (HomologicalComplex.homologyMap (B.d (-i) (-(i - 1))) (-j))
      (reindexed_first_page_d R B G hanti β hβd i j))
    (hτ i j)

private theorem stepSubobject_eq_two : ∀ p n : ℤ,
    tensorStep R K P (fun (_ : ℤ) j ↦ j) p n =
      Subobject.mk (((tensorBicomplex R K P).totalFiltration₂.filtration.ι.app (op p)).f n) :=
  fun p n ↦ ((tensorBicomplex R K P).mk_totalFiltration_ι_f
    (fun (_ : ℤ) j ↦ j) (fun _ _ ↦ le_rfl) (fun _ _ ↦ by omega) p n).symm

private theorem stepSubobject_eq_one : ∀ p n : ℤ,
    tensorStep R K P (fun i (_ : ℤ) ↦ i) p n =
      Subobject.mk (((tensorBicomplex R K P).totalFiltration₁.filtration.ι.app (op p)).f n) :=
  fun p n ↦ ((tensorBicomplex R K P).mk_totalFiltration_ι_f
    (fun i (_ : ℤ) ↦ i) (fun _ _ ↦ by omega) (fun _ _ ↦ le_rfl) p n).symm

private theorem antitone_stepSubobject_two : ∀ p p' n : ℤ, p ≤ p' →
    tensorStep R K P (fun (_ : ℤ) j ↦ j) p' n ≤
      tensorStep R K P (fun (_ : ℤ) j ↦ j) p n :=
  CochainComplex.antitone_of_eq (tensorBicomplex R K P).totalFiltration₂
    (tensorStep R K P (fun (_ : ℤ) j ↦ j)) (stepSubobject_eq_two R K P)

private theorem antitone_stepSubobject_one : ∀ p p' n : ℤ, p ≤ p' →
    tensorStep R K P (fun i (_ : ℤ) ↦ i) p' n ≤
      tensorStep R K P (fun i (_ : ℤ) ↦ i) p n :=
  CochainComplex.antitone_of_eq (tensorBicomplex R K P).totalFiltration₁
    (tensorStep R K P (fun i (_ : ℤ) ↦ i)) (stepSubobject_eq_one R K P)

private theorem factors_d_stepSubobject_two : ∀ p n m : ℤ, m = n + 1 →
    (tensorStep R K P (fun (_ : ℤ) j ↦ j) p m).Factors
      ((tensorStep R K P (fun (_ : ℤ) j ↦ j) p n).arrow ≫
        ((tensorBicomplex R K P).total (ComplexShape.up ℤ)).d n m) :=
  fun p n m hm ↦ factors_filtration_arrow_comp_d
    (tensorBicomplex R K P).totalFiltration₂
    (tensorStep R K P (fun (_ : ℤ) j ↦ j))
    (stepSubobject_eq_two R K P) p n m hm

private theorem factors_d_stepSubobject_one : ∀ p n m : ℤ, m = n + 1 →
    (tensorStep R K P (fun i (_ : ℤ) ↦ i) p m).Factors
      ((tensorStep R K P (fun i (_ : ℤ) ↦ i) p n).arrow ≫
        ((tensorBicomplex R K P).total (ComplexShape.up ℤ)).d n m) :=
  fun p n m hm ↦ factors_filtration_arrow_comp_d
    (tensorBicomplex R K P).totalFiltration₁
    (tensorStep R K P (fun i (_ : ℤ) ↦ i))
    (stepSubobject_eq_one R K P) p n m hm

private theorem torFiltration_step_two :
    (homologicalFiltrationOfSubobjects
      ((tensorBicomplex R K P).total (ComplexShape.up ℤ))
      (tensorStep R K P (fun (_ : ℤ) j ↦ j))
      (antitone_stepSubobject_two R K P) (factors_d_stepSubobject_two R K P)).step =
        tensorFiltrationSteps.{u, v} R K P false :=
  homologicalFiltrationOfSubobjects_step_eq R K P false (fun (_ : ℤ) j ↦ j)
    (fun _ _ _ ↦ Iff.rfl) (antitone_stepSubobject_two R K P)
    (factors_d_stepSubobject_two R K P)

private theorem torFiltration_step_one :
    (homologicalFiltrationOfSubobjects
      ((tensorBicomplex R K P).total (ComplexShape.up ℤ))
      (tensorStep R K P (fun i (_ : ℤ) ↦ i))
      (antitone_stepSubobject_one R K P) (factors_d_stepSubobject_one R K P)).step =
        tensorFiltrationSteps.{u, v} R K P true :=
  homologicalFiltrationOfSubobjects_step_eq R K P true (fun i (_ : ℤ) ↦ i)
    (fun _ _ _ ↦ Iff.rfl) (antitone_stepSubobject_one R K P)
    (factors_d_stepSubobject_one R K P)

private theorem torFiltration_finite_two (a : ℤ) (ha : ∀ i : ℤ, a < i → IsZero (K.X i))
    (hPbound : ∀ i : ℤ, 0 < i → IsZero (P.X i)) : ∀ n, ∃ c d : ℤ, c ≤ d ∧
    (homologicalFiltrationOfSubobjects
      ((tensorBicomplex R K P).total (ComplexShape.up ℤ))
      (tensorStep R K P (fun (_ : ℤ) j ↦ j))
      (antitone_stepSubobject_two R K P) (factors_d_stepSubobject_two R K P)).step c n = ⊥ ∧
    (homologicalFiltrationOfSubobjects
      ((tensorBicomplex R K P).total (ComplexShape.up ℤ))
      (tensorStep R K P (fun (_ : ℤ) j ↦ j))
      (antitone_stepSubobject_two R K P) (factors_d_stepSubobject_two R K P)).step d n = ⊤ := by
  intro n
  rw [torFiltration_step_two]
  exact tensorFiltrationSteps_finite R K P a 0 ha hPbound false n

private theorem torFiltration_finite_one (a : ℤ) (ha : ∀ i : ℤ, a < i → IsZero (K.X i))
    (hPbound : ∀ i : ℤ, 0 < i → IsZero (P.X i)) : ∀ n, ∃ c d : ℤ, c ≤ d ∧
    (homologicalFiltrationOfSubobjects
      ((tensorBicomplex R K P).total (ComplexShape.up ℤ))
      (tensorStep R K P (fun i (_ : ℤ) ↦ i))
      (antitone_stepSubobject_one R K P) (factors_d_stepSubobject_one R K P)).step c n = ⊥ ∧
    (homologicalFiltrationOfSubobjects
      ((tensorBicomplex R K P).total (ComplexShape.up ℤ))
      (tensorStep R K P (fun i (_ : ℤ) ↦ i))
      (antitone_stepSubobject_one R K P) (factors_d_stepSubobject_one R K P)).step d n = ⊤ := by
  intro n
  rw [torFiltration_step_one]
  exact tensorFiltrationSteps_finite R K P a 0 ha hPbound true n

/-- STEP 1 (concrete, small). The row differential of the tensor bicomplex, read through the Tor
identification of the rows, is the map induced on Tor by the differential of `K`.

This is the one definitional comparison that has to be paid -- the row of the bicomplex at `-i`
and the termwise tensor product of `K.X (-i)` with the resolution are the same complex by
unfolding only -- and it is paid here, in a statement that mentions no spectral sequence, no
filtration and no subobject. Paid instead inside the assembly, where it arrives as a
metavariable in the second argument of `Eq.trans`, it exhausts that budget. -/
private theorem row_d_iso_torMap
    {M : ModuleCat.{max u v} R} (Q : ProjectiveResolution M)
    (Pres : CochainComplex (ModuleCat.{max u v} R) ℤ) (hPres : Pres = Q.cochainComplex)
    (i j : ℤ) :
    (page_one_iso_tor R K Q Pres hPres i j).inv ≫
        HomologicalComplex.homologyMap ((tensorBicomplex R K Pres).d (-i) (-(i - 1))) (-j) ≫
        (page_one_iso_tor R K Q Pres hPres (i - 1) j).hom =
      torInDegreeMap.{u, v} R j (K.d (-i) (-(i - 1))) M := by
  subst hPres
  exact NatIso.naturality_1 (torNatIso R Q j) (K.d (-i) (-(i - 1)))

/-- The second-filtration half of the data of `TorSpectralSequences`, for a given resolution.

Split from the first half because a heartbeat ceiling is per declaration: assembled together the
two halves exceed any budget we were willing to set, and separately each is comfortable. -/
private structure TorSpectralSequenceSecond (M : ModuleCat.{max u v} R)
    (Pres : CochainComplex (ModuleCat.{max u v} R) ℤ) where
  /-- The spectral sequence of the second filtration. -/
  E : FirstTorSpectralSequence (ModuleCat.{max u v} R)
  /-- Its second page is the Tor of the homology of `K`. -/
  e₂ : ∀ i j : ℤ, (E.page 2).X (i, j) ≅ TorInDegree.{u, v} R j (K.homology (-i)) M
  /-- The filtration it abuts to. -/
  F : HomologicalFiltration ((tensorBicomplex R K Pres).total (ComplexShape.up ℤ))
  /-- The comparison data. -/
  S : TorFiltrationData E F false
  /-- `F` is the second coordinate filtration. -/
  hF : F.step = tensorFiltrationSteps.{u, v} R K Pres false
  /-- `F` is finite in each degree. -/
  hFin : ∀ n, ∃ a b : ℤ, a ≤ b ∧ F.step a n = ⊥ ∧ F.step b n = ⊤
  /-- The spectral sequence converges. -/
  conv : S.Converges

/-- The first-filtration half of the data of `TorSpectralSequences`, for a given resolution. -/
private structure TorSpectralSequenceFirst (M : ModuleCat.{max u v} R)
    (Pres : CochainComplex (ModuleCat.{max u v} R) ℤ) where
  /-- The spectral sequence of the first filtration. -/
  E' : SecondTorSpectralSequence (ModuleCat.{max u v} R)
  /-- Its first page is the Tor of the terms of `K`. -/
  e₁ : ∀ i j : ℤ, (E'.page 1).X (i, j) ≅ TorInDegree.{u, v} R j (K.X (-i)) M
  /-- The filtration it abuts to. -/
  F' : HomologicalFiltration ((tensorBicomplex R K Pres).total (ComplexShape.up ℤ))
  /-- The comparison data. -/
  S' : TorFiltrationData E' F' true
  /-- `F'` is the first coordinate filtration. -/
  hF' : F'.step = tensorFiltrationSteps.{u, v} R K Pres true
  /-- `F'` is finite in each degree. -/
  hFin' : ∀ n, ∃ a b : ℤ, a ≤ b ∧ F'.step a n = ⊥ ∧ F'.step b n = ⊤
  /-- The spectral sequence converges. -/
  conv' : S'.Converges
  /-- Under `e₁`, the first differential is the map induced on Tor by the differential of `K`. -/
  hd : ∀ i j : ℤ,
    (e₁ i j).inv ≫ (E'.page 1).d (i, j) (i - 1, j) ≫ (e₁ (i - 1) j).hom =
      torInDegreeMap.{u, v} R j (K.d (-i) (-(i - 1))) M

/-- The second-filtration spectral sequence of the tensor product with a given free
resolution. -/
private theorem nonempty_torSpectralSequenceSecond
    (M : ModuleCat.{max u v} R) (a : ℤ) (ha : ∀ i : ℤ, a < i → IsZero (K.X i))
    (Q : ProjectiveResolution M)
    (Pres : CochainComplex (ModuleCat.{max u v} R) ℤ) (hPres : Pres = Q.cochainComplex)
    (hPfree : ∀ i : ℤ, Module.Free R (Pres.X i))
    (hPbound : ∀ i : ℤ, 0 < i → IsZero (Pres.X i)) :
    Nonempty (TorSpectralSequenceSecond R K M Pres) := by
  obtain ⟨S⟩ := nonempty_torFiltrationData
    ((tensorBicomplex R K Pres).total (ComplexShape.up ℤ))
    (tensorStep R K Pres (fun (_ : ℤ) j ↦ j))
    (antitone_stepSubobject_two R K Pres) (factors_d_stepSubobject_two R K Pres) false 2 (by omega)
  have hγ := nonempty_second_page_iso_totalFiltration₂ R (tensorBicomplex R K Pres)
    (tensorStep R K Pres (fun (_ : ℤ) j ↦ j))
    (stepSubobject_eq_two R K Pres) (antitone_stepSubobject_two R K Pres)
  exact ⟨{ E := homologicalSpectralSequence
             ((tensorBicomplex R K Pres).total (ComplexShape.up ℤ))
             (tensorStep R K Pres (fun (_ : ℤ) j ↦ j))
             (antitone_stepSubobject_two R K Pres) false 2 (by omega)
           e₂ := fun i j ↦
             reindexed_page_two_iso R (tensorBicomplex R K Pres)
                 (tensorStep R K Pres (fun (_ : ℤ) q ↦ q))
                 (antitone_stepSubobject_two R K Pres) (fun p q ↦ (hγ p q).some) i j ≪≫
               page_two_iso_tor R K Q Pres hPres hPfree i j
           F := homologicalFiltrationOfSubobjects
             ((tensorBicomplex R K Pres).total (ComplexShape.up ℤ))
             (tensorStep R K Pres (fun (_ : ℤ) j ↦ j))
             (antitone_stepSubobject_two R K Pres) (factors_d_stepSubobject_two R K Pres)
           S := S
           hF := torFiltration_step_two R K Pres
           hFin := torFiltration_finite_two R K Pres a ha hPbound
           conv := TorFiltrationData.converges_of_finite
             (homologicalFiltrationOfSubobjects
               ((tensorBicomplex R K Pres).total (ComplexShape.up ℤ))
               (tensorStep R K Pres (fun (_ : ℤ) j ↦ j))
               (antitone_stepSubobject_two R K Pres) (factors_d_stepSubobject_two R K Pres))
             S (torFiltration_finite_two R K Pres a ha hPbound) }⟩

set_option maxHeartbeats 1600000 in
-- Assembling one half of the package exceeds the default elaboration budget.
/-- The first-filtration spectral sequence of the tensor product with a given free
resolution. -/
private theorem nonempty_torSpectralSequenceFirst
    (M : ModuleCat.{max u v} R) (a : ℤ) (ha : ∀ i : ℤ, a < i → IsZero (K.X i))
    (Q : ProjectiveResolution M)
    (Pres : CochainComplex (ModuleCat.{max u v} R) ℤ) (hPres : Pres = Q.cochainComplex)
    (hPbound : ∀ i : ℤ, 0 < i → IsZero (Pres.X i)) :
    Nonempty (TorSpectralSequenceFirst R K M Pres) := by
  obtain ⟨S'⟩ := nonempty_torFiltrationData
    ((tensorBicomplex R K Pres).total (ComplexShape.up ℤ))
    (tensorStep R K Pres (fun i (_ : ℤ) ↦ i))
    (antitone_stepSubobject_one R K Pres) (factors_d_stepSubobject_one R K Pres) true 1 (by omega)
  obtain ⟨β, hβd⟩ :=
    exists_first_page_iso_totalFiltration₁ R (tensorBicomplex R K Pres)
      (tensorStep R K Pres (fun i (_ : ℤ) ↦ i))
      (stepSubobject_eq_one R K Pres) (antitone_stepSubobject_one R K Pres)
  exact ⟨{ E' := homologicalSpectralSequence
             ((tensorBicomplex R K Pres).total (ComplexShape.up ℤ))
             (tensorStep R K Pres (fun i (_ : ℤ) ↦ i))
             (antitone_stepSubobject_one R K Pres) true 1 (by omega)
           e₁ := fun i j ↦
             reindexed_page_one_iso R (tensorBicomplex R K Pres)
                 (tensorStep R K Pres (fun i (_ : ℤ) ↦ i))
                 (antitone_stepSubobject_one R K Pres) β i j ≪≫
               page_one_iso_tor R K Q Pres hPres i j
           F' := homologicalFiltrationOfSubobjects
             ((tensorBicomplex R K Pres).total (ComplexShape.up ℤ))
             (tensorStep R K Pres (fun i (_ : ℤ) ↦ i))
             (antitone_stepSubobject_one R K Pres) (factors_d_stepSubobject_one R K Pres)
           S' := S'
           hF' := torFiltration_step_one R K Pres
           hFin' := torFiltration_finite_one R K Pres a ha hPbound
           conv' := TorFiltrationData.converges_of_finite
             (homologicalFiltrationOfSubobjects
               ((tensorBicomplex R K Pres).total (ComplexShape.up ℤ))
               (tensorStep R K Pres (fun i (_ : ℤ) ↦ i))
               (antitone_stepSubobject_one R K Pres) (factors_d_stepSubobject_one R K Pres))
             S' (torFiltration_finite_one R K Pres a ha hPbound)
           hd := conj_first_page_d_tor R K (tensorBicomplex R K Pres)
             (tensorStep R K Pres (fun i (_ : ℤ) ↦ i))
             (antitone_stepSubobject_one R K Pres) β hβd
             (page_one_iso_tor R K Q Pres hPres) (row_d_iso_torMap R K Q Pres hPres) }⟩

end Assembly

/-- The two spectral sequences of the tensor product of a bounded-below chain complex `K` of
`R`-modules with an `R`-module `M`, packaged with the free resolution they are built from and
with the data that makes "converging to `H_*(K ⊗_R^{\mathbf L} M)`" precise.

The fields are the clauses of the source statement, in order.

* A resolution of `M` by free modules: the complex `P`, its augmentation `ε`, the fact
  `quasiIso` that the augmentation is a quasi-isomorphism, the freeness `free` of its terms,
  its concentration `bounded` in nonpositive chain degrees, and the two homology clauses
  `homologyZero` and `homologyNe`.
* The two spectral sequences `E`, `E'` of the double complex `K ⊗_R P`. Their differentials have
  bidegrees `(r - 1, -r)` and `(-r, r - 1)`, recorded in the types `FirstTorSpectralSequence`
  and `SecondTorSpectralSequence` themselves; at `r = 2` and `r = 1` these are the `d₂` and `d₁`
  of the source.
* The page identifications `e₂ : (E₂)_{i, j} ≅ Torⱼᴿ(Hᵢ(K), M)` and
  `e₁ : (E'₁)_{i, j} ≅ Torⱼᴿ(Kᵢ, M)`.
* The abutment. `F` and `F'` are the two filtrations of the total complex of `K ⊗_R P`; `hF` and
  `hF'` say they are its filtrations by the second and the first coordinate; `S` and `S'` are the
  comparison data identifying the graded pieces of those filtrations with the pages of `E` and
  `E'`; `hFin` and `hFin'` say each filtration is finite in every degree; and `conv`, `conv'`
  are the resulting convergence of the two sequences to the homology of `K ⊗_R P`.
* `hd`, which says that under `e₁` the first differential of `E'` is the map induced on Tor by
  the differential `Kᵢ ⟶ Kᵢ₋₁` of `K`.

The chain complex is represented by the cochain complex obtained by degree reversal, so `Kᵢ` is
written `K.X (-i)`, and `Torⱼᴿ(Kᵢ, M)` sits in bidegree `(i, j)`. -/
public structure TorSpectralSequences (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (M : ModuleCat.{max u v} R) where
  /-- The complex of a resolution of `M` by free modules. -/
  P : CochainComplex (ModuleCat.{max u v} R) ℤ
  /-- The augmentation of the resolution. -/
  ε : P ⟶ (HomologicalComplex.single (ModuleCat.{max u v} R) (ComplexShape.up ℤ) 0).obj M
  /-- The augmentation is a quasi-isomorphism. -/
  quasiIso : QuasiIso ε
  /-- The terms of `P` are free. -/
  free : ∀ i : ℤ, Module.Free R (P.X i)
  /-- `P` comes from a chain complex: it vanishes in positive cochain degree. -/
  bounded : ∀ i : ℤ, 0 < i → IsZero (P.X i)
  /-- `H₀(P) ≅ M`. -/
  homologyZero : Nonempty (P.homology 0 ≅ M)
  /-- `P` has no homology away from degree `0`. -/
  homologyNe : ∀ i : ℤ, i ≠ 0 → IsZero (P.homology i)
  /-- The spectral sequence of the filtration by the second coordinate. Its `r`-th differential
  has bidegree `(r - 1, -r)`, so `d₂ : (E₂)_{i, j} ⟶ (E₂)_{i + 1, j - 2}`. -/
  E : FirstTorSpectralSequence (ModuleCat.{max u v} R)
  /-- The spectral sequence of the filtration by the first coordinate. Its `r`-th differential
  has bidegree `(-r, r - 1)`, so `d₁ : (E'₁)_{i, j} ⟶ (E'₁)_{i - 1, j}`. -/
  E' : SecondTorSpectralSequence (ModuleCat.{max u v} R)
  /-- The second page of `E` is the Tor of the homology of `K`. -/
  e₂ : ∀ i j : ℤ, (E.page 2).X (i, j) ≅ TorInDegree.{u, v} R j (K.homology (-i)) M
  /-- The first page of `E'` is the Tor of the terms of `K`. -/
  e₁ : ∀ i j : ℤ, (E'.page 1).X (i, j) ≅ TorInDegree.{u, v} R j (K.X (-i)) M
  /-- The filtration of `K ⊗_R P` that `E` abuts to. -/
  F : HomologicalFiltration (HomologicalComplex.mapBifunctor K P
    (moduleTensorBifunctor.{u, v} R) (ComplexShape.up ℤ))
  /-- The filtration of `K ⊗_R P` that `E'` abuts to. -/
  F' : HomologicalFiltration (HomologicalComplex.mapBifunctor K P
    (moduleTensorBifunctor.{u, v} R) (ComplexShape.up ℤ))
  /-- `E` is the spectral sequence of `F`. -/
  S : TorFiltrationData E F false
  /-- `E'` is the spectral sequence of `F'`. -/
  S' : TorFiltrationData E' F' true
  /-- `F` is the filtration by the second coordinate of the double complex. -/
  hF : F.step = tensorFiltrationSteps.{u, v} R K P false
  /-- `F'` is the filtration by the first coordinate of the double complex. -/
  hF' : F'.step = tensorFiltrationSteps.{u, v} R K P true
  /-- `F` is finite in each degree. -/
  hFin : ∀ n, ∃ a b : ℤ, a ≤ b ∧ F.step a n = ⊥ ∧ F.step b n = ⊤
  /-- `F'` is finite in each degree. -/
  hFin' : ∀ n, ∃ a b : ℤ, a ≤ b ∧ F'.step a n = ⊥ ∧ F'.step b n = ⊤
  /-- `E` converges to the homology of `K ⊗_R P`. -/
  conv : S.Converges
  /-- `E'` converges to the homology of `K ⊗_R P`. -/
  conv' : S'.Converges
  /-- Under `e₁`, the first differential of `E'` is the map induced on Tor by the differential
  of `K`. -/
  hd : ∀ i j : ℤ,
    (e₁ i j).inv ≫ (E'.page 1).d (i, j) (i - 1, j) ≫ (e₁ (i - 1) j).hom =
      torInDegreeMap.{u, v} R j (K.d (-i) (-(i - 1))) M

/-- The two spectral sequences of the tensor product with a free resolution, at a single module
universe.

The resolution is produced here and handed to the two half-assemblies as a binder. -/
@[ega "III 6.3.2" "special case", ega "III 6.7.3" "special case"]
private theorem nonempty_torSpectralSequences_of_common_universe
    (R : Type u) [CommRing R] (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hK : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (K.X i)) (M : ModuleCat.{max u v} R) :
    Nonempty (TorSpectralSequences.{u, v} R K M) := by
  obtain ⟨D₀, hD, hFree⟩ := exists_free_resolution_largeUniverse.{u, max u v} R M
  obtain ⟨hPfree, hPbound, hH₀, hH⟩ := freeProjectiveResolution_cochainComplex R D₀ hD hFree
  obtain ⟨a, ha⟩ := hK
  obtain ⟨d₂⟩ := nonempty_torSpectralSequenceSecond R K M a ha
    (freeProjectiveResolution D₀ hD hFree) _ rfl hPfree hPbound
  obtain ⟨d₁⟩ := nonempty_torSpectralSequenceFirst R K M a ha
    (freeProjectiveResolution D₀ hD hFree) _ rfl hPbound
  exact ⟨{ P := (freeProjectiveResolution D₀ hD hFree).cochainComplex
           ε := (freeProjectiveResolution D₀ hD hFree).π'
           quasiIso := inferInstance
           free := hPfree
           bounded := hPbound
           homologyZero := hH₀
           homologyNe := hH
           E := d₂.E
           E' := d₁.E'
           e₂ := d₂.e₂
           e₁ := d₁.e₁
           F := d₂.F
           F' := d₁.F'
           S := d₂.S
           S' := d₁.S'
           hF := d₂.hF
           hF' := d₁.hF'
           hFin := d₂.hFin
           hFin' := d₁.hFin'
           conv := d₂.conv
           conv' := d₁.conv'
           hd := d₁.hd }⟩

/-- Let `K` be a bounded-below chain complex of `R`-modules and let `M` be an `R`-module. There
is a resolution `P` of `M` by free `R`-modules, and the two filtrations of the double complex
`K ⊗_R P` give spectral sequences converging to the homology of `K ⊗_R^{\mathbf L} M`.

The first has second page `Torⱼᴿ(Hᵢ(K), M)` and differential `d₂` of bidegree `(1, -2)`. The
second has first page `Torⱼᴿ(Kᵢ, M)`; under the displayed identifications its differential `d₁`
is the map on Tor induced by `Kᵢ ⟶ Kᵢ₋₁`.

The conclusion is `Nonempty` of `TorSpectralSequences`, whose fields are exactly the clauses
listed above; see its documentation for the correspondence.

`exists_spectral_sequences_tor_homology_and_terms` below is the same statement with the fields
spelled out as an iterated existential; it carries the tag. -/
@[ega "III 6.3.2" "special case"]
public theorem nonempty_torSpectralSequences
    (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hK : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (K.X i))
    (M : ModuleCat.{w} R) :
    Nonempty (TorSpectralSequences.{u, max v w} R
      (((ModuleCat.uliftFunctor.{max u w, v} R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)
      ((ModuleCat.uliftFunctor.{max u v, w} R).obj M)) := by
  refine nonempty_torSpectralSequences_of_common_universe.{u, max v w} R _ ?_ _
  obtain ⟨a, ha⟩ := hK
  exact ⟨a, fun i hi ↦ (ModuleCat.uliftFunctor.{max u w, v} R).map_isZero (ha i hi)⟩

/-- Let `K` be a bounded-below chain complex of `R`-modules and let `M` be an `R`-module. There
is a bounded-below free resolution `P` of `M`, and the two filtrations of `K ⊗[R] P` give
spectral sequences abutting to its homology.

The first has second page `Torⱼᴿ(Hᵢ(K), M)` and differential of bidegree `(1, -2)`. The second
has first page `Torⱼᴿ(Kᵢ, M)`; under the displayed identifications, its first differential is
the map on Tor induced by `Kᵢ ⟶ Kᵢ₋₁`. -/
@[stacks 061Z, ega "III 6.3.2" "Q• = module M, K bdd", ega "III 7.6.4" "(i) spectral sequence"]
public theorem exists_spectral_sequences_tor_homology_and_terms
    (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hK : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (K.X i))
    (M : ModuleCat.{w} R) :
    let K' := ((ModuleCat.uliftFunctor.{max u w, v} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    let M' := (ModuleCat.uliftFunctor.{max u v, w} R).obj M
    ∃ (P : CochainComplex (ModuleCat.{max u v w} R) ℤ),
      ∃ (ε : P ⟶ (HomologicalComplex.single (ModuleCat.{max u v w} R)
        (ComplexShape.up ℤ) 0).obj M')
        (_ : QuasiIso ε),
      (∀ i : ℤ, Module.Free R (P.X i)) ∧
      (∀ i : ℤ, 0 < i → IsZero (P.X i)) ∧
      Nonempty (P.homology 0 ≅ M') ∧
      (∀ i : ℤ, i ≠ 0 → IsZero (P.homology i)) ∧
      ∃ (E : FirstTorSpectralSequence (ModuleCat.{max u v w} R))
        (E' : SecondTorSpectralSequence (ModuleCat.{max u v w} R))
        (_e₂ : ∀ i j : ℤ, (E.page 2).X (i, j) ≅ TorInDegree.{u, max v w} R j (K'.homology (-i)) M')
        (e₁ : ∀ i j : ℤ, (E'.page 1).X (i, j) ≅ TorInDegree.{u, max v w} R j (K'.X (-i)) M'),
        let T := HomologicalComplex.mapBifunctor K' P (moduleTensorBifunctor.{u, max v w} R)
          (ComplexShape.up ℤ)
        ∃ (F F' : HomologicalFiltration T)
          (S : TorFiltrationData E F false)
          (S' : TorFiltrationData E' F' true),
          F.step = tensorFiltrationSteps.{u, max v w} R K' P false ∧
          F'.step = tensorFiltrationSteps.{u, max v w} R K' P true ∧
          (∀ n, ∃ a b : ℤ, a ≤ b ∧ F.step a n = ⊥ ∧ F.step b n = ⊤) ∧
          (∀ n, ∃ a b : ℤ, a ≤ b ∧ F'.step a n = ⊥ ∧ F'.step b n = ⊤) ∧
          S.Converges ∧ S'.Converges ∧
          ∀ i j : ℤ,
            (e₁ i j).inv ≫ (E'.page 1).d (i, j) (i - 1, j) ≫ (e₁ (i - 1) j).hom =
              torInDegreeMap.{u, max v w} R j (K'.d (-i) (-(i - 1))) M' := by
  intro K' M'
  obtain ⟨D⟩ := nonempty_torSpectralSequences.{u, v, w} R K hK M
  exact ⟨D.P, D.ε, D.quasiIso, D.free, D.bounded, D.homologyZero, D.homologyNe,
    D.E, D.E', D.e₂, D.e₁, D.F, D.F', D.S, D.S', D.hF, D.hF', D.hFin, D.hFin',
    D.conv, D.conv', D.hd⟩

end CochainComplex.Tor

end
