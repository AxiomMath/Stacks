module

public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.Tor.KFlatResolutionSingleTensor

/-!
# The derived tensor product of a module flat over the base with a base-changed module

Let `A → P` be a flat homomorphism of commutative rings, let `M` be a `P`-module which is flat
as an `A`-module, and let `W` be an `A`-module. Then

`M ⊗^𝐋_P (P ⊗_A W) ≅ (M ⊗_P (P ⊗_A W))[0]`  in `D(P)`,

that is, all higher Tor modules of `M` against a module base-changed from `A` vanish. A free
resolution of `W` over `A` base-changes to a resolution of `P ⊗_A W` by free `P`-modules, and
tensoring that resolution with `M` over `P` is, after restriction of scalars, tensoring it with
`M` over `A`, which is exact.

## Main results

* `CochainComplex.DerivedTensor.quasiIso_tleftCochain_map_extendScalars`: tensoring with a
  complex of `P`-modules which is K-flat over `A` preserves quasi-isomorphisms between
  complexes base-changed from `A`.
* `CochainComplex.DerivedTensor.derivedTensorIsoTensorRightKFlatResolution` and
  `CochainComplex.DerivedTensor.derivedTensorIsoTensorLeftKFlatResolution`: the comparison of
  the derived tensor product of two modules with the degreewise tensor product of a K-flat
  resolution, as an isomorphism rather than an existence statement.
* `CochainComplex.DerivedTensor.derivedTensorSingleExtendScalarsIso`: the derived tensor
  product above is the ordinary one, placed in degree zero.

## Implementation notes

The isomorphism is a definition, not an existence statement: both K-flat resolutions are
arguments, and the body is the canonical comparison `DerivedTensorProduct.comparison` of the
derived tensor product on those two representatives, composed with the two resolution maps and
with the single-complex comparisons. Nothing is chosen inside, so a consumer may rewrite with
it. Independence of the choice of resolutions is not proved and is not needed: a consumer
testing vanishing of a morphism into the obstruction target uses only invertibility.

## References

* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

namespace CochainComplex.DerivedTensor

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]
variable {A P : Type u} [CommRing A] [CommRing P]

/-- A complex of `A`-modules which is zero outside degree `0`, where it is a flat module, is
K-flat. -/
private theorem kFlat_of_isZero_of_flat_zero (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ModuleCat.{u} A) [Module.Flat A M] (e : K.X 0 ≅ M) (hz : ∀ i, i ≠ 0 → IsZero (K.X i)) :
    CochainComplex.KFlat.{u, u} K := by
  have : K.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hz i (by omega)
  have (i : ℤ) : Module.Flat A (K.X i) := by
    by_cases hi : i = 0
    · subst hi
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
    · exact Module.Flat.of_linearEquiv (hz i hi).isoZero.toLinearEquiv
  exact CochainComplex.KFlat.kFlat_of_flat.{u, u} K 0

/-- A module placed in degree zero gives a K-flat complex as soon as the module is flat: the
complex is bounded above and its only nonzero term is the module. -/
theorem kFlat_single_of_flat (M : ModuleCat.{u} A) [Module.Flat A M] :
    CochainComplex.KFlat.{u, u}
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M) :=
  kFlat_of_isZero_of_flat_zero _ M
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M 0 rfl)
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M)

/-- **Tensoring with a complex which is K-flat over the base preserves quasi-isomorphisms of
base-changed complexes.** For `L` a complex of `P`-modules whose underlying complex of
`A`-modules is K-flat, the functor `X ↦ Tot(L ⊗_P (P ⊗_A X))` carries a quasi-isomorphism of
complexes of `A`-modules to a quasi-isomorphism: after restriction of scalars it is
`X ↦ Tot(L ⊗_A X)`, and restriction of scalars reflects quasi-isomorphism. -/
theorem quasiIso_tleftCochain_map_extendScalars (φ : A →+* P)
    (L : CochainComplex (ModuleCat.{u} P) ℤ)
    (hL : CochainComplex.KFlat.{u, u} ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L))
    {K K' : CochainComplex (ModuleCat.{u} A) ℤ} (g : K ⟶ K') (hg : QuasiIso g) :
    QuasiIso ((TleftCochain L).map ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map g)) := by
  have hnat := CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso_naturality.{u, u, u}
    φ g L
  rw [← CochainComplex.quasiIso_restrictScalarsLarge_map_iff.{u} φ]
  exact (quasiIso_iff_of_arrow_mk_iso _
      ((TleftCochain ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L)).map g)
      (Arrow.isoMk
        (CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso.{u, u, u} φ K L)
        (CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso.{u, u, u} φ K' L)
        hnat.symm)).mpr (quasiIso_tleftCochain_map_of_kFlat _ hL g hg)

/-- A single complex on a `P`-module whose restriction to `A` is flat is K-flat over `A`. -/
theorem kFlat_restrictScalars_single_of_flat (φ : A →+* P) (M : ModuleCat.{u} P)
    [Module.Flat A ((ModuleCat.restrictScalars.{u} φ).obj M)] :
    CochainComplex.KFlat.{u, u} ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M)) := by
  exact kFlat_of_isZero_of_flat_zero _ ((ModuleCat.restrictScalars.{u} φ).obj M)
    ((ModuleCat.restrictScalars.{u} φ).mapIso
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 M 0 rfl))
    fun i hi => Functor.map_isZero (ModuleCat.restrictScalars.{u} φ)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)

/-- **Tensoring with a single complex flat over the base preserves base-changed
quasi-isomorphisms**, read degreewise. -/
theorem quasiIso_tensorLeft_map_extendScalars (φ : A →+* P) (M : ModuleCat.{u} P)
    [Module.Flat A ((ModuleCat.restrictScalars.{u} φ).obj M)]
    {K K' : CochainComplex (ModuleCat.{u} A) ℤ} (g : K ⟶ K') (hg : QuasiIso g) :
    QuasiIso ((((curriedTensor (ModuleCat.{u} P)).obj M).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map g)) := by
  set h := (CochainComplex.extendScalarsLarge.{u, u, u} φ).map g with hh
  have hn := TotalTensorComplex.SingleTensor.singleTensorIso_naturality (C := ModuleCat.{u} P) M h
  refine (quasiIso_iff_of_arrow_mk_iso
    ((TleftCochain ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M)).map h) _
    (Arrow.isoMk
      (TotalTensorComplex.SingleTensor.singleTensorIso M _).symm
      (TotalTensorComplex.SingleTensor.singleTensorIso M _).symm hn).symm).mp ?_
  exact quasiIso_tleftCochain_map_extendScalars φ _
    (kFlat_restrictScalars_single_of_flat φ M) g hg


/-- **A K-flat resolution of each factor computes `M ⊗^𝐋_R N` as `P^• ⊗_R N`.** This is
`nonempty_derivedTensor_iso_tensorRight_kFlat_resolution` with the resolution of the second
factor supplied by the caller, so that the isomorphism is a definition rather than an
existence statement: it is the canonical comparison of the derived tensor product on the two
K-flat representatives, read through the two resolutions. -/
noncomputable def derivedTensorIsoTensorRightKFlatResolution (M N : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (g : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) (hg : QuasiIso g)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : CochainComplex.KFlat.{u, u} L)
    (f : L ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) (hf : QuasiIso f) :
    ((canonicalDerivedTensorProduct R).tensor.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≅
      DerivedCategory.Q.obj
        ((((curriedTensor (ModuleCat.{u} R)).flip.obj N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  have hg' := hg
  have hf' := hf
  have h₁ : IsIso (DerivedCategory.Q.map g) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  have h₂ : IsIso (DerivedCategory.Q.map f) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  have hqi := quasiIso_tleftCochain_map_of_kFlat P hP f hf
  have h₃ : IsIso (DerivedCategory.Q.map ((TleftCochain P).map f)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  Iso.app ((canonicalDerivedTensorProduct R).tensor.mapIso
      (@asIso _ _ _ _ _ h₁).symm) _ ≪≫
    ((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj P)).mapIso
      (@asIso _ _ _ _ _ h₂).symm ≪≫
    (canonicalDerivedTensorProduct R).comparison P L hP hL ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map ((TleftCochain P).map f)) h₃ ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.mapBifunctorSingleRightIso
      (curriedTensor (ModuleCat.{u} R)) P N)

/-- **A K-flat resolution of each factor computes `M ⊗^𝐋_R N` as `N ⊗_R P^•`.** The previous
definition moved across the symmetry of the tensor product of modules. -/
noncomputable def derivedTensorIsoTensorLeftKFlatResolution (M N : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (g : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) (hg : QuasiIso g)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : CochainComplex.KFlat.{u, u} L)
    (f : L ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) (hf : QuasiIso f) :
    ((canonicalDerivedTensorProduct R).tensor.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≅
      DerivedCategory.Q.obj
        ((((curriedTensor (ModuleCat.{u} R)).obj N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  derivedTensorIsoTensorRightKFlatResolution M N P hP g hg L hL f hf ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex
        ((BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} R)).app N).symm
        (ComplexShape.up ℤ)).app P)

/-- **The derived tensor product of a module flat over the base with a base-changed module.**
Let `A → P` be a flat ring homomorphism, let `M` be a `P`-module which is flat over `A`, and
let `W` be an `A`-module. Then `M ⊗^𝐋_P (P ⊗_A W)` is `M ⊗_P (P ⊗_A W)` placed in degree
zero: the given resolution of `W` over `A` base-changes to a K-flat resolution of `P ⊗_A W`,
and tensoring it with `M` over `P` is, after restriction of scalars, tensoring with the
`A`-flat module `M` over `A`, which is exact. The two resolutions are arguments, so that the
isomorphism is the canonical comparison read through them. -/
noncomputable def derivedTensorSingleExtendScalarsIso (φ : A →+* P) (hφ : φ.Flat)
    (M : ModuleCat.{u} P)
    [Module.Flat A ((ModuleCat.restrictScalars.{u} φ).obj M)] (W : ModuleCat.{u} A)
    (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : CochainComplex.KFlat.{u, u} L)
    (f : L ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj W) (hf : QuasiIso f)
    (N : CochainComplex (ModuleCat.{u} P) ℤ) (hN : CochainComplex.KFlat.{u, u} N)
    (p : N ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M) (hp : QuasiIso p) :
    ((canonicalDerivedTensorProductFunctor P).obj
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M))).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj
          ((ModuleCat.extendScalars.{u, u, u} φ).obj W))) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj
        (((curriedTensor (ModuleCat.{u} P)).obj M).obj
          ((ModuleCat.extendScalars.{u, u, u} φ).obj W)))   := by
  have hGflat := CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} φ L hL
  let e : (CochainComplex.extendScalarsLarge.{u, u, u} φ).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj W) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj
        ((ModuleCat.extendScalars.{u, u, u} φ).obj W) :=
    (HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.extendScalars.{u, u, u} φ) (ComplexShape.up ℤ) 0).app W
  have : (ModuleCat.extendScalars.{u, u, u} φ).PreservesHomology :=
    extendScalars_preservesHomology_of_flat.{u, u} φ hφ
  have hf' := hf
  have hqe : QuasiIso ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map f) :=
    inferInstanceAs (QuasiIso
      (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f))
  have hg : QuasiIso ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map f ≫ e.hom) :=
    (quasiIso_iff_comp_right _ e.hom).mpr hqe
  have hten : QuasiIso ((((curriedTensor (ModuleCat.{u} P)).obj M).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map f ≫
        e.hom)) := by
    have h1 := quasiIso_tensorLeft_map_extendScalars φ M f hf
    have hei : IsIso ((((curriedTensor (ModuleCat.{u} P)).obj M).mapHomologicalComplex
        (ComplexShape.up ℤ)).map e.hom) :=
      inferInstanceAs (IsIso ((((curriedTensor (ModuleCat.{u} P)).obj M).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso e).hom)
    have heq : QuasiIso ((((curriedTensor (ModuleCat.{u} P)).obj M).mapHomologicalComplex
        (ComplexShape.up ℤ)).map e.hom) := quasiIso_of_isIso _
    rw [Functor.map_comp]
    exact (quasiIso_iff_comp_right _ _).mpr h1
  have hiso : IsIso (DerivedCategory.Q.map
      ((((curriedTensor (ModuleCat.{u} P)).obj M).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map f ≫
          e.hom))) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hten
  exact derivedTensorProductCommIso _ _ ≪≫
    derivedTensorIsoTensorLeftKFlatResolution ((ModuleCat.extendScalars.{u, u, u} φ).obj W) M
      ((CochainComplex.extendScalarsLarge.{u, u, u} φ).obj L) hGflat
      ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map f ≫ e.hom) hg N hN p hp ≪≫
    (@asIso _ _ _ _ _ hiso) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        ((curriedTensor (ModuleCat.{u} P)).obj M) (ComplexShape.up ℤ) 0).app
          ((ModuleCat.extendScalars.{u, u, u} φ).obj W))

/-- **Stacks 0DZ2, the footnote.** `M ⊗^𝐋_P (P ⊗_A W)` is `M ⊗_P (P ⊗_A W)` in degree zero,
with the resolutions discharged by existence of free K-flat resolutions. -/
theorem nonempty_derivedTensor_single_extendScalars_iso_single (φ : A →+* P) (hφ : φ.Flat)
    (M : ModuleCat.{u} P)
    [Module.Flat A ((ModuleCat.restrictScalars.{u} φ).obj M)] (W : ModuleCat.{u} A) :
    Nonempty (((canonicalDerivedTensorProductFunctor P).obj
          (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M))).obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj
          ((ModuleCat.extendScalars.{u, u, u} φ).obj W))) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj
        (((curriedTensor (ModuleCat.{u} P)).obj M).obj
          ((ModuleCat.extendScalars.{u, u, u} φ).obj W)))) := by
  obtain ⟨L, f, hL, -, -, hf⟩ := CochainComplex.KFlat.exists_free_kFlat_resolution W
  obtain ⟨N, p, hN, -, -, hp⟩ := CochainComplex.KFlat.exists_free_kFlat_resolution M
  exact ⟨derivedTensorSingleExtendScalarsIso φ hφ M W L hL f hf N hN p hp⟩

end CochainComplex.DerivedTensor

end
