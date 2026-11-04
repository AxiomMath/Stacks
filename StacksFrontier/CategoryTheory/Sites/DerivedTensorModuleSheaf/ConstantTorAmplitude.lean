module

public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Constant
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.DerivedTensorSingle
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Fiber
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Transport
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.TorAmplitude

/-!
# Tor amplitude of a constant complex

Let `(C, J)` be a site with a point `Φ`, `S` a commutative ring and `P` a bounded above complex
of free `S`-modules. If the constant complex `\underline{P}` has Tor amplitude in a set of
degrees `T` in `D(C, S)`, then `P` itself has Tor amplitude in `T`, in the form that for every
module `M` and every free resolution `F → M[0]`, the complex `P ⊗ F` has vanishing cohomology
outside `T`.

Conversely, the constant complex of a complex of flat modules concentrated in degrees `[a, b]`
has Tor amplitude in `[a, b]`.

## Main results

* `Stacks.ModuleSheaf.isZero_homology_tensor_of_hasTorAmplitude_constantSheaf`: if
  `\underline{P} ⊗_S^L \underline{N}` has cohomology sheaves vanishing outside `T` for every
  module `N`, then `P ⊗ F` has cohomology vanishing outside `T` for every free resolution `F` of a
  module.
* `Stacks.ModuleSheaf.hasTorAmplitude_constantSheaf_of_flat`: the constant complex of a complex of
  flat modules concentrated in degrees `[a, b]` has Tor amplitude in `[a, b]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace Stacks.ModuleSheaf

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Sheaf.symmetricCategory monoidalClosed CochainComplex.braidedCategory derivedMonoidal
  derivedSymmetric

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [UnivLE.{max u v, w}]
  [LocallySmall.{w} C] (Φ : J.Point.{w}) {S : Type w} [CommRing S]

open CochainComplex.KFlatBifunctor

omit [LocallySmall.{w} C] in
/-- **The constant complex of a bounded complex of flat modules has Tor amplitude in its
range.** For a complex `E` of flat `S`-modules concentrated in degrees `[a, b]`, the constant
complex `\underline{E}` has Tor amplitude in `[a, b]` in `D(C, S)`. -/
theorem hasTorAmplitude_constantSheaf_of_flat (E : CochainComplex (ModuleCat.{w} S) ℤ) (a b : ℤ)
    [E.IsStrictlyGE a] [E.IsStrictlyLE b] (hE : ∀ n, Module.Flat S (E.X n)) :
    HasTorAmplitude (J := J) (DerivedCategory.Q.obj
      (((constantSheaf J (ModuleCat.{w} S)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E))
      (Set.Icc a b) := by
  let c := constantSheaf J (ModuleCat.{w} S)
  have : c.Additive :=
    Functor.additive_of_preserves_binary_products (constantSheaf J (ModuleCat.{w} S))
  let K : CochainComplex (Sheaf J (ModuleCat.{w} S)) ℤ :=
    (c.mapHomologicalComplex (ComplexShape.up ℤ)).obj E
  have : K.IsStrictlyLE b := isStrictlyLE_mapHomologicalComplex c E b
  have : K.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => c.map_isZero (E.isZero_of_isStrictlyGE a i hi)
  have hK : KFlat (curriedTensor (Sheaf J (ModuleCat.{w} S))) K :=
    kFlat_of_isStrictlyLE_of_isStrictlyGE _ (L := K) (b := b) a fun q =>
      have : PreservesFiniteLimits (tensorRight (K.X q)) :=
        preservesFiniteLimits_tensorRight_presheafToSheaf_obj J
          ((Functor.const Cᵒᵖ).obj (E.X q)) fun _ => hE q
      kFlat_single_of_exact (curriedTensor (Sheaf J (ModuleCat.{w} S))) (K.X q) q
        (fun G hG => HomologicalComplex.Acyclic.map (tensorRight (K.X q)) hG)
  intro F i hi
  have hz : IsZero ((rowComplex (curriedTensor (Sheaf J (ModuleCat.{w} S))) K F).homology i) := by
    refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
    change IsZero ((K.X i) ⊗ F)
    refine (tensorRight F).map_isZero ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    exacts [K.isZero_of_isStrictlyGE a i hi, K.isZero_of_isStrictlyLE b i hi]
  exact (hz.of_iso ((DerivedCategory.homologyFunctorFactors _ i).app _)).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      ((Iso.refl _ ⊗ᵢ (DerivedCategory.singleFunctorIsoCompQ _ 0).app F) ≪≫
        (derivedTensorSingleIso (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hK)).app F))

omit [LocallySmall.{w} C] in
include Φ in
/-- **Tor amplitude of a constant complex bounds the Tor of its coefficients.** On a site with
a point `Φ`, let `P` be a bounded above complex of free `S`-modules such that
`\underline{P} ⊗_S^L \underline{N}` has vanishing cohomology sheaves outside `T` for every
module `N` (as when `\underline{P}` has Tor amplitude in `T`). Then for every module `M` and every
free resolution `F → M[0]` concentrated in degrees `≤ 0`, the complex `P ⊗ F` has vanishing
cohomology outside `T`. -/
theorem isZero_homology_tensor_of_hasTorAmplitude_constantSheaf
    (P : CochainComplex (ModuleCat.{w} S) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hP : ∀ i, Module.Free S (P.X i)) {T : Set ℤ}
    (h : ∀ (N : ModuleCat.{w} S) (j : ℤ), j ∉ T →
      IsZero ((DerivedCategory.homologyFunctor _ j).obj (DerivedCategory.Q.obj
        (((constantSheaf J (ModuleCat.{w} S)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⊗
          (DerivedCategory.singleFunctor _ 0).obj ((constantSheaf J (ModuleCat.{w} S)).obj N))))
    (M : ModuleCat.{w} S) (F : CochainComplex (ModuleCat.{w} S) ℤ)
    (f : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{w} S) 0).obj M) [QuasiIso f]
    [F.IsStrictlyLE 0] (hF : ∀ n, Module.Free S (F.X n)) {i : ℤ} (hi : i ∉ T) :
    IsZero ((P ⊗ F).homology i) := by
  let c := constantSheaf J (ModuleCat.{w} S)
  have : PreservesFiniteColimits c := by unfold c constantSheaf; infer_instance
  have : PreservesFiniteLimits c := preservesFiniteLimits_constantSheaf J S
  have : c.Additive := Functor.additive_of_preserves_binary_products _
  let e₁ : DerivedCategory.Q.obj ((c.mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj (c.obj M) :=
    asIso (DerivedCategory.Q.map ((c.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex c (ComplexShape.up ℤ) 0).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (c.obj M)).symm
  obtain ⟨e₂⟩ := nonempty_homology_constantSheaf_tensor_iso (J := J) P F b 0 hP hF i
  have hz : IsZero (c.obj ((P ⊗ F).homology i)) :=
    (h M i hi).of_iso (e₂.symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (Iso.refl _ ⊗ᵢ e₁))
  exact ((moduleSheafFiber S Φ).map_isZero hz).of_iso
    ((CategoryTheory.Sites.constantSheafFiberNatIso Φ).app _).symm

end Stacks.ModuleSheaf

end
