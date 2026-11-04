module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.BaseChangeAcyclicity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A kernel is a quotient of an external tensor product

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` with `X` quasi-compact,
separated and flat over `R`, and let `K` be a quasi-coherent kernel on `X ×_R Y` satisfying the
two conditions of [Stacks, Tag 0FZH] part (2).  Writing `F_K` for the integral transform of `K`,
this file proves [Stacks, Tag 0FZJ]:  there is a surjection
`𝒪_X ⊠ F_K(𝒪_X) ⟶ K`.

## Main definitions

* `AlgebraicGeometry.diagonalOver` is the diagonal `X ⟶ X ×_R X` as a morphism of schemes over
  `R`, and `AlgebraicGeometry.diagonalTripleMap` is `Δ × id_Y : X ×_R Y ⟶ (X ×_R X) ×_R Y`.
* `AlgebraicGeometry.diagonalIntegrand` is the integrand `pr_{12}^*(-) ⊗ pr_{23}^*K` of
  [Stacks, Tag 0FZI] on `X ×_R X ×_R Y`, as a functor of all `𝒪_{X ×_R X}`-modules.
* `AlgebraicGeometry.diagonalUnitMap` is the surjection `𝒪_{X ×_R X} ⟶ 𝒪_Δ`.

## Main results

* `AlgebraicGeometry.isPullback_projections`: the square relating `pr_{13}` and `pr_{23}` to the
  second projection of `X ×_R Y` is cartesian.
* `AlgebraicGeometry.exactFunctor_diagonalIntegrand`: **the integrand is exact**, which is
  [Stacks, Tag 0GMU] for the kernel `pr_{23}^*K`, flat over `X ×_R X` because `K` is flat over
  `X`.
* `AlgebraicGeometry.epi_pushforward_diagonalIntegrand_map`: **the direct image along `pr_{13}`
  of the integrand of `𝒪_{X ×_R X} ⟶ 𝒪_Δ` is a surjection**, by [Stacks, Tag 0FZI] applied to
  the two left-hand terms of the diagonal short exact sequence.
* `AlgebraicGeometry.externalTensorUnitIso`: the source `𝒪_X ⊠ F_K(𝒪_X)` is `pr_2^*pr_{2,*}K`.
* `AlgebraicGeometry.flatBaseChangeKernelIso`: **flat base change**, [Stacks, Tag 02KH] in
  degree zero, identifying `pr_2^*pr_{2,*}K` with `pr_{13,*}(pr_{23}^*K)`.
* `AlgebraicGeometry.pushforwardDiagonalIntegrandDiagonalIso`: **the projection formula**,
  [Stacks, Tag 0B55], identifying the target `pr_{13,*}(pr_{12}^*𝒪_Δ ⊗ pr_{23}^*K)` with `K`.
* `AlgebraicGeometry.exists_epi_externalTensorProduct_unit`: **[Stacks, Tag 0FZJ]**.

## Implementation notes

The triple product is `(X ×_R X) ×_R Y`, associated to the left, and all three of its
projections are instances of `AlgebraicGeometry.sourceChangeMap`:  `pr_{12}` is the first
projection of the pullback, while `pr_{13}` and `pr_{23}` are induced by the two projections of
`X ×_R X`.  Consequently `Δ × id_Y` followed by either of `pr_{13}` and `pr_{23}` is the
identity, by `AlgebraicGeometry.sourceChangeMap_comp` and
`AlgebraicGeometry.sourceChangeMap_id`;  this is what makes the projection formula collapse
`pr_{13,*}(Δ × id_Y)_*` to the identity.

The diagonal short exact sequence is taken in the form `0 → ker q → 𝒪_{X ×_R X} → 𝒪_Δ → 0` with
`q` the comparison `AlgebraicGeometry.diagonalUnitMap` of the structure sheaves;  that it is
epimorphic with quasi-coherent kernel is two of the equivalent conditions of
`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae` for the diagonal, which is a
closed immersion exactly because `X` is separated over `R`.

The exactness of `AlgebraicGeometry.diagonalIntegrand` is used through
`CategoryTheory.ShortComplex.ShortExact.map_of_exact`, and the passage from the short exact
sequence on `X ×_R X ×_R Y` to one on `X ×_R Y` is
`CategoryTheory.Functor.rightAcyclic_and_shortExact_map_of_shortExact`, whose two acyclicity
hypotheses are [Stacks, Tag 0FZI] at the kernel and at the structure sheaf.  Degrees are
therefore converted between `CategoryTheory.Functor.rightDerived` and
`CategoryTheory.Functor.rightDerivedPlus` by `Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`.

The statement is an existence statement, as in the source:  the surjection is not canonical, it
is the composite of the surjection above with the two identifications, each of which involves a
choice of inverse.

## References

* [Stacks Project, Tag 0FZJ](https://stacks.math.columbia.edu/tag/0FZJ)
* [Stacks Project, Tag 0FZI](https://stacks.math.columbia.edu/tag/0FZI)
* [Stacks Project, Tag 0FZH](https://stacks.math.columbia.edu/tag/0FZH)
* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The standard derived category of the module sheaves on a scheme.  Declared in this folded
spelling because the universe level of `CategoryTheory.HasDerivedCategory.standard` is a maximum
that instance search does not solve against `AlgebraicGeometry.Scheme.Modules`. -/
local instance hasDerivedCategory_modules_diagonal (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules :=
  HasDerivedCategory.standard _

variable (R : Type u) [CommRing R]

/-! ### The diagonal and the projections of the triple product -/

/-- A scheme separated over an affine base is a separated scheme. -/
instance isSeparated_of_isSeparated_hom (X : Over (Spec (.of R))) [IsSeparated X.hom] :
    X.left.IsSeparated := by
  constructor
  rw [← terminal.comp_from X.hom]
  infer_instance

/-- The structure morphism of a scheme separated over `R` is quasi-separated:  its diagonal is a
closed immersion, hence affine, hence quasi-compact. -/
@[ega "II 7.2.3" "a⇒b", sga "1 VIII 3.6"]
instance quasiSeparated_of_isSeparated_hom (X : Over (Spec (.of R))) [IsSeparated X.hom] :
    QuasiSeparated X.hom :=
  ⟨inferInstance⟩

/-- **The diagonal `Δ : X ⟶ X ×_R X`**, as a morphism of schemes over `R`. -/
abbrev diagonalOver (X : Over (Spec (.of R))) : X ⟶ baseChangeSourceOver R X X :=
  Over.homMk (pullback.diagonal X.hom) (by
    change pullback.diagonal X.hom ≫ pullback.fst X.hom X.hom ≫ X.hom = X.hom
    rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp])

/-- The diagonal of a scheme separated over `R` is an affine morphism. -/
instance isAffineHom_diagonalOver (X : Over (Spec (.of R))) [IsSeparated X.hom] :
    IsAffineHom (diagonalOver R X).left :=
  inferInstanceAs (IsAffineHom (pullback.diagonal X.hom))

/-- The diagonal followed by the first projection is the identity. -/
theorem diagonalOver_comp_fst (X : Over (Spec (.of R))) :
    diagonalOver R X ≫ baseChangeSourceOverFst R X X = 𝟙 X :=
  Over.OverMorphism.ext (pullback.diagonal_fst X.hom)

/-- The diagonal followed by the second projection is the identity. -/
theorem diagonalOver_comp_snd (X : Over (Spec (.of R))) :
    diagonalOver R X ≫ baseChangeSourceOverSnd R X X = 𝟙 X :=
  Over.OverMorphism.ext (pullback.diagonal_snd X.hom)

/-- **`Δ × id_Y : X ×_R Y ⟶ (X ×_R X) ×_R Y`.** -/
abbrev diagonalTripleMap (X Y : Over (Spec (.of R))) :
    pullback X.hom Y.hom ⟶ pullback (baseChangeSourceOver R X X).hom Y.hom :=
  sourceChangeMap R (baseChangeSourceOver R X X) X Y (diagonalOver R X)

/-- **`Δ × id_Y` followed by `pr_{13}` is the identity.** -/
theorem diagonalTripleMap_comp_targetMap (X Y : Over (Spec (.of R))) :
    diagonalTripleMap R X Y ≫ baseChangeTargetMap R X X Y = 𝟙 _ := by
  rw [baseChangeTargetMap, sourceChangeMap_comp, diagonalOver_comp_fst, sourceChangeMap_id]

/-- **`Δ × id_Y` followed by `pr_{23}` is the identity.** -/
theorem diagonalTripleMap_comp_kernelMap (X Y : Over (Spec (.of R))) :
    diagonalTripleMap R X Y ≫
        sourceChangeMap R X (baseChangeSourceOver R X X) Y (baseChangeSourceOverSnd R X X) =
      𝟙 _ := by
  rw [sourceChangeMap_comp, diagonalOver_comp_snd, sourceChangeMap_id]

/-- **The square relating `pr_{23}` and `pr_{13}` to the second projection of `X ×_R Y` is
cartesian.**  Pasting the cartesian square of `pr_{13}` with the cartesian square of the two
projections of `X ×_R X` gives the outer rectangle over `Spec R`, and the square of the two
projections of `X ×_R Y` cuts the right half off. -/
theorem isPullback_projections (X Y : Over (Spec (.of R))) :
    IsPullback
      (sourceChangeMap R X (baseChangeSourceOver R X X) Y (baseChangeSourceOverSnd R X X))
      (baseChangeTargetMap R X X Y) (pullback.snd X.hom Y.hom) (pullback.snd X.hom Y.hom) := by
  have h13 := isPullback_sourceChangeMap R X (baseChangeSourceOver R X X) Y
    (baseChangeSourceOverFst R X X)
  have h23 := isPullback_sourceChangeMap R X (baseChangeSourceOver R X X) Y
    (baseChangeSourceOverSnd R X X)
  have hright : IsPullback (pullback.snd X.hom X.hom) (pullback.fst X.hom X.hom) X.hom X.hom :=
    (IsPullback.of_hasPullback X.hom X.hom).flip
  have houter := h13.paste_horiz hright
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback X.hom Y.hom)
  · rw [← h23.w, ← pullback.condition]
    exact houter
  · simp only [sourceChangeMap_comp_snd]

/-! ### The integrand of `pr_23^*K` and its exactness -/

/-- **The integrand `pr_{12}^*(-) ⊗ pr_{23}^*K` of [Stacks, Tag 0FZI]**, on all
`𝒪_{X ×_R X}`-modules.  Its restriction to the quasi-coherent modules is
`AlgebraicGeometry.integralTransformIntegrand` at the kernel
`AlgebraicGeometry.baseChangeKernel`. -/
abbrev diagonalIntegrand (X Y : Over (Spec (.of R)))
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    (baseChangeSourceOver R X X).left.Modules ⥤
      (pullback (baseChangeSourceOver R X X).hom Y.hom).Modules :=
  Scheme.Modules.pullback (pullback.fst (baseChangeSourceOver R X X).hom Y.hom) ⋙
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨(pullback (baseChangeSourceOver R X X).hom Y.hom).presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _
            ((pullback (baseChangeSourceOver R X X).hom Y.hom).presheaf)
            (forget₂ CommRingCat RingCat)
            ((pullback (baseChangeSourceOver R X X).hom Y.hom).ringCatSheaf.2)⟩).obj
      ((baseChangeKernel R X X Y K).obj))

/-- **The integrand is exact.**  This is [Stacks, Tag 0GMU] for the kernel `pr_{23}^*K`, which
is flat over `X ×_R X` because `K` is flat over `X` and flatness is stable under base change
([Stacks, Tag 01U8]). -/
theorem exactFunctor_diagonalIntegrand (X Y : Over (Spec (.of R)))
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (hK : integralTransformExactKernel R X Y K) :
    exactFunctor _ _ (diagonalIntegrand R X Y K) := by
  have hKq : K.obj.IsQuasicoherent := K.property
  have hflat : AlgebraicGeometry.IsFlatOver
      (pullback.fst (baseChangeSourceOver R X X).hom Y.hom).toLRSHom.toShHom
      (baseChangeKernel R X X Y K).obj :=
    @modulePullback_isFlatOver _ _ _ _ _ _ _ _
      (isPullback_sourceChangeMap R X (baseChangeSourceOver R X X) Y
        (baseChangeSourceOverSnd R X X)).flip K.obj hKq hK.1
  exact (exactFunctor _ _).prop_of_iso
    (Functor.isoWhiskerLeft
      (Scheme.Modules.pullback (pullback.fst (baseChangeSourceOver R X X).hom Y.hom))
      ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
        ((pullback (baseChangeSourceOver R X X).hom Y.hom)).presheaf
        ((pullback (baseChangeSourceOver R X X).hom Y.hom)).ringCatSheaf.2
        ((baseChangeKernel R X X Y K).obj)))).symm
    (Stacks.SheafOfModules.pullbackTensorFunctor_exact
      (pullback.fst (baseChangeSourceOver R X X).hom Y.hom).toLRSHom.toShHom
      (baseChangeKernel R X X Y K).obj hflat)

/-- **[Stacks, Tag 0FZI] read as acyclicity.**  The integrand at a quasi-coherent module is
acyclic for the direct image along `pr_{13}`. -/
theorem rightAcyclic_pushforward_diagonalIntegrand (X Y : Over (Spec (.of R)))
    [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (hK : integralTransformExactKernel R X Y K)
    (M : (baseChangeSourceOver R X X).left.Modules) (hM : M.IsQuasicoherent) :
    (Scheme.Modules.pushforward (baseChangeTargetMap R X X Y)).rightAcyclic
      ((diagonalIntegrand R X Y K).obj M) := by
  refine (((Scheme.Modules.pushforward
    (baseChangeTargetMap R X X Y)).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
      _).2 inferInstance).2 ?_
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi.le).symm⟩
  rw [← Stacks.DerivedIndexing.isZero_rightDerived_obj_iff]
  exact isZero_rightDerived_pushforward_baseChangeKernel R X X Y K hK ⟨M, hM⟩ n
    (by exact_mod_cast hi)

/-! ### The diagonal short exact sequence -/

/-- **The comparison `𝒪_{X ×_R X} ⟶ 𝒪_Δ`** of the structure sheaf of `X ×_R X` with the direct
image of the structure sheaf of `X` along the diagonal. -/
abbrev diagonalUnitMap (X : Over (Spec (.of R))) :
    SheafOfModules.unit (baseChangeSourceOver R X X).left.ringCatSheaf ⟶
      (Scheme.Modules.pushforward (pullback.diagonal X.hom)).obj
        (SheafOfModules.unit X.left.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom (pullback.diagonal X.hom).toLRSHom.toShHom)

/-- The comparison `𝒪_{X ×_R X} ⟶ 𝒪_Δ` is surjective, because the diagonal of a scheme
separated over `R` is a closed immersion. -/
instance epi_diagonalUnitMap (X : Over (Spec (.of R))) [IsSeparated X.hom] :
    Epi (diagonalUnitMap R X) :=
  (((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae
    (pullback.diagonal X.hom)).out 1 4
      (a := IsClosedImmersion (pullback.diagonal X.hom))
      (b := Topology.IsClosedEmbedding (pullback.diagonal X.hom).base ∧
        Epi (diagonalUnitMap R X))).mp inferInstance).2

/-- The ideal sheaf of the diagonal is quasi-coherent. -/
theorem isQuasicoherent_kernel_diagonalUnitMap (X : Over (Spec (.of R))) [IsSeparated X.hom] :
    (kernel (diagonalUnitMap R X)).IsQuasicoherent :=
  (((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae
    (pullback.diagonal X.hom)).out 1 5
      (a := IsClosedImmersion (pullback.diagonal X.hom))
      (b := (Topology.IsClosedEmbedding (pullback.diagonal X.hom).base ∧
          Epi (diagonalUnitMap R X)) ∧
        (kernel (diagonalUnitMap R X)).IsQuasicoherent)).mp inferInstance).2

/-- **The direct image along `pr_{13}` of the integrand of `𝒪_{X ×_R X} ⟶ 𝒪_Δ` is a
surjection.**  The integrand carries the diagonal short exact sequence to a short exact sequence
on `X ×_R X ×_R Y` because it is exact, and the direct image along `pr_{13}` carries that one to
a short exact sequence because its first two terms are `pr_{13}`-acyclic by
[Stacks, Tag 0FZI]. -/
theorem epi_pushforward_diagonalIntegrand_map (X Y : Over (Spec (.of R)))
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (hK : integralTransformExactKernel R X Y K) :
    Epi ((Scheme.Modules.pushforward (baseChangeTargetMap R X X Y)).map
      ((diagonalIntegrand R X Y K).map (diagonalUnitMap R X))) := by
  have hGex := exactFunctor_diagonalIntegrand R X Y K hK
  have hGlim : PreservesFiniteLimits (diagonalIntegrand R X Y K) :=
    ((exactFunctor_iff _).mp hGex).1
  have hGcolim : PreservesFiniteColimits (diagonalIntegrand R X Y K) :=
    ((exactFunctor_iff _).mp hGex).2
  have hGempty : PreservesLimitsOfShape (Discrete PEmpty.{1}) (diagonalIntegrand R X Y K) :=
    hGlim.preservesFiniteLimits _
  have hGzero : (diagonalIntegrand R X Y K).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have hSES := ShortComplex.shortExact_mk_kernel_ι (diagonalUnitMap R X)
  have hmapped := @ShortComplex.ShortExact.map_of_exact _ _ _ _ _ _ _ hSES
    (diagonalIntegrand R X Y K) hGzero hGlim hGcolim
  have h1 := rightAcyclic_pushforward_diagonalIntegrand R X Y K hK
    (kernel (diagonalUnitMap R X)) (isQuasicoherent_kernel_diagonalUnitMap R X)
  have h2 := rightAcyclic_pushforward_diagonalIntegrand R X Y K hK
    (SheafOfModules.unit (baseChangeSourceOver R X X).left.ringCatSheaf)
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _)
  exact (((Functor.rightAcyclic_and_shortExact_map_of_shortExact
    (Scheme.Modules.pushforward (baseChangeTargetMap R X X Y)) _ hmapped).2.1 h1 h2).2).epi_g

/-! ### Identification of the source: flat base change -/

/-- **The integral transform of `K` at the structure sheaf is `pr_{2,*}K`.**  The inverse image
of the structure sheaf along the first projection is the structure sheaf, and tensoring by it is
the identity. -/
def integralTransformUnitObjIso (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [IsSeparated X.hom]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    ((quasicoherentIntegralTransform R X Y K).obj
        ⟨SheafOfModules.unit X.left.ringCatSheaf,
          Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩).obj ≅
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj :=
  (quasicoherentIntegralTransformData R X Y K).comparison.app
      ⟨SheafOfModules.unit X.left.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩ ≪≫
    (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).mapIso
      (Stacks.SheafOfModules.Invertible.tensorProductIso (pullback X.hom Y.hom).presheaf
          (pullback X.hom Y.hom).ringCatSheaf.2 (Iso.refl K.obj)
          (Scheme.Modules.pullbackUnitIso (pullback.fst X.hom Y.hom)) ≪≫
        Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
          (pullback X.hom Y.hom).presheaf (pullback X.hom Y.hom).ringCatSheaf.2 K.obj)

/-- **`𝒪_X ⊠ F_K(𝒪_X)` is `pr_2^*pr_{2,*}K`.**  The first factor is the structure sheaf after
inverse image, so the external tensor product is the inverse image of the second factor, which
is `pr_{2,*}K` by `AlgebraicGeometry.integralTransformUnitObjIso`. -/
def externalTensorUnitIso (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [IsSeparated X.hom]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    externalTensorProduct X.hom Y.hom (SheafOfModules.unit X.left.ringCatSheaf)
        ((quasicoherentIntegralTransform R X Y K).obj
          ⟨SheafOfModules.unit X.left.ringCatSheaf,
            Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩).obj ≅
      (Scheme.Modules.pullback (pullback.snd X.hom Y.hom)).obj
        ((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj) :=
  Stacks.SheafOfModules.Invertible.tensorProductIso (pullback X.hom Y.hom).presheaf
      (pullback X.hom Y.hom).ringCatSheaf.2
      (Scheme.Modules.pullbackUnitIso (pullback.fst X.hom Y.hom))
      ((Scheme.Modules.pullback (pullback.snd X.hom Y.hom)).mapIso
        (integralTransformUnitObjIso R X Y K)) ≪≫
    ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
        ((pullback X.hom Y.hom)).presheaf ((pullback X.hom Y.hom)).ringCatSheaf.2
        ((SheafOfModules.unit (pullback X.hom Y.hom).ringCatSheaf)))).app
      ((Scheme.Modules.pullback (pullback.snd X.hom Y.hom)).obj
        ((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj)) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor (pullback X.hom Y.hom).presheaf
      (pullback X.hom Y.hom).ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.snd X.hom Y.hom)).obj
        ((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj))

/-- The integrand at the structure sheaf of `X ×_R X` is the kernel `pr_{23}^*K`. -/
def diagonalIntegrandUnitIso (X Y : Over (Spec (.of R)))
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    (diagonalIntegrand R X Y K).obj
        (SheafOfModules.unit (baseChangeSourceOver R X X).left.ringCatSheaf) ≅
      (baseChangeKernel R X X Y K).obj :=
  Stacks.SheafOfModules.Invertible.tensorProductIso
      (pullback (baseChangeSourceOver R X X).hom Y.hom).presheaf
      (pullback (baseChangeSourceOver R X X).hom Y.hom).ringCatSheaf.2
      (Iso.refl _)
      (Scheme.Modules.pullbackUnitIso
        (pullback.fst (baseChangeSourceOver R X X).hom Y.hom)) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
      (pullback (baseChangeSourceOver R X X).hom Y.hom).presheaf
      (pullback (baseChangeSourceOver R X X).hom Y.hom).ringCatSheaf.2 _

/-- **Flat base change, [Stacks, Tag 02KH] in degree zero**, for the cartesian square of
`AlgebraicGeometry.isPullback_projections`:  the inverse image along `pr_2` of `pr_{2,*}K` is the
direct image along `pr_{13}` of `pr_{23}^*K`.  The flat morphism is the second projection of
`X ×_R Y`, a base change of the flat structure morphism of `X`. -/
def flatBaseChangeKernelIso (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [IsSeparated X.hom] [Flat X.hom]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    (Scheme.Modules.pullback (pullback.snd X.hom Y.hom)).obj
        ((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj) ≅
      (Scheme.Modules.pushforward (baseChangeTargetMap R X X Y)).obj
        (baseChangeKernel R X X Y K).obj :=
  have _hKq : K.obj.IsQuasicoherent := K.property
  @asIso _ _ _ _ _
    (Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
      (isPullback_projections R X Y) K.obj)

/-! ### Identification of the target: the projection formula -/

/-- **The inverse image of `𝒪_Δ` along `pr_{12}` is the direct image of the structure sheaf
along `Δ × id_Y`.**  This is affine base change ([Stacks, Tag 02KG]) for the cartesian square
relating `Δ` and `Δ × id_Y`, whose affine leg is the diagonal. -/
def pullbackDiagonalUnitIso (X Y : Over (Spec (.of R))) [IsSeparated X.hom] :
    (Scheme.Modules.pullback (pullback.fst (baseChangeSourceOver R X X).hom Y.hom)).obj
        ((Scheme.Modules.pushforward (pullback.diagonal X.hom)).obj
          (SheafOfModules.unit X.left.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward (diagonalTripleMap R X Y)).obj
        (SheafOfModules.unit (pullback X.hom Y.hom).ringCatSheaf) :=
  (baseChangeIsoOfFunctor
        (isPullback_sourceChangeMap R (baseChangeSourceOver R X X) X Y (diagonalOver R X))
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf))
        (fun A => A.property)).app
      ⟨SheafOfModules.unit X.left.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X.left⟩ ≪≫
    (Scheme.Modules.pushforward (diagonalTripleMap R X Y)).mapIso
      (Scheme.Modules.pullbackUnitIso (pullback.fst X.hom Y.hom))

/-- The inverse image of `pr_{23}^*K` along `Δ × id_Y` is `K`:  `Δ × id_Y` followed by `pr_{23}`
is the identity. -/
def pullbackDiagonalKernelIso (X Y : Over (Spec (.of R)))
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    (Scheme.Modules.pullback (diagonalTripleMap R X Y)).obj
        (baseChangeKernel R X X Y K).obj ≅ K.obj :=
  (Scheme.Modules.pullbackComp (diagonalTripleMap R X Y)
        (sourceChangeMap R X (baseChangeSourceOver R X X) Y
          (baseChangeSourceOverSnd R X X))).app K.obj ≪≫
    (Scheme.Modules.pullbackCongr (diagonalTripleMap_comp_kernelMap R X Y)).app K.obj ≪≫
    (Scheme.Modules.pullbackId (pullback X.hom Y.hom)).app K.obj

/-- The direct image along `pr_{13}` of a direct image along `Δ × id_Y` is the module itself:
`Δ × id_Y` followed by `pr_{13}` is the identity. -/
def pushforwardDiagonalTripleIso (X Y : Over (Spec (.of R)))
    (M : (pullback X.hom Y.hom).Modules) :
    (Scheme.Modules.pushforward (baseChangeTargetMap R X X Y)).obj
        ((Scheme.Modules.pushforward (diagonalTripleMap R X Y)).obj M) ≅ M :=
  ((Scheme.Modules.pushforwardComp (diagonalTripleMap R X Y)
        (baseChangeTargetMap R X X Y)).app M).symm ≪≫
    (Scheme.Modules.pushforwardCongr (diagonalTripleMap_comp_targetMap R X Y)).app M ≪≫
    (Scheme.Modules.pushforwardId (pullback X.hom Y.hom)).app M

/-- **The direct image along `pr_{13}` of the integrand at `𝒪_Δ` is `K`.**  The integrand at
`𝒪_Δ` is `(Δ × id_Y)_*𝒪_{X ×_R Y} ⊗ pr_{23}^*K`, which the projection formula
([Stacks, Tag 0B55]) rewrites as `(Δ × id_Y)_*(Δ × id_Y)^*pr_{23}^*K`;  both `Δ × id_Y`
followed by `pr_{23}` and `Δ × id_Y` followed by `pr_{13}` are the identity. -/
def pushforwardDiagonalIntegrandDiagonalIso (X Y : Over (Spec (.of R))) [IsSeparated X.hom]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    (Scheme.Modules.pushforward (baseChangeTargetMap R X X Y)).obj
        ((diagonalIntegrand R X Y K).obj
          ((Scheme.Modules.pushforward (pullback.diagonal X.hom)).obj
            (SheafOfModules.unit X.left.ringCatSheaf))) ≅ K.obj :=
  have _hKq : K.obj.IsQuasicoherent := K.property
  have hKK : (baseChangeKernel R X X Y K).obj.IsQuasicoherent :=
    (baseChangeKernel R X X Y K).property
  (Scheme.Modules.pushforward (baseChangeTargetMap R X X Y)).mapIso
      (((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
          ((pullback (baseChangeSourceOver R X X).hom Y.hom)).presheaf
          ((pullback (baseChangeSourceOver R X X).hom Y.hom)).ringCatSheaf.2
          ((baseChangeKernel R X X Y K).obj))).app
          ((Scheme.Modules.pullback (pullback.fst (baseChangeSourceOver R X X).hom Y.hom)).obj
            ((Scheme.Modules.pushforward (pullback.diagonal X.hom)).obj
              (SheafOfModules.unit X.left.ringCatSheaf))) ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (pullback (baseChangeSourceOver R X X).hom Y.hom).sheaf).flip.obj
              (baseChangeKernel R X X Y K).obj).mapIso (pullbackDiagonalUnitIso R X Y) ≪≫
          Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent
            (diagonalTripleMap R X Y)
            (SheafOfModules.unit (pullback X.hom Y.hom).ringCatSheaf)
            (baseChangeKernel R X X Y K).obj
            (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _) hKK ≪≫
          (Scheme.Modules.pushforward (diagonalTripleMap R X Y)).mapIso
            (((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
                ((pullback X.hom Y.hom)).presheaf ((pullback X.hom Y.hom)).ringCatSheaf.2
                ((SheafOfModules.unit (pullback X.hom Y.hom).ringCatSheaf)))).app
                ((Scheme.Modules.pullback (diagonalTripleMap R X Y)).obj
                  (baseChangeKernel R X X Y K).obj) ≪≫
              Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
                (pullback X.hom Y.hom).presheaf (pullback X.hom Y.hom).ringCatSheaf.2
                ((Scheme.Modules.pullback (diagonalTripleMap R X Y)).obj
                  (baseChangeKernel R X X Y K).obj) ≪≫
              pullbackDiagonalKernelIso R X Y K)) ≪≫
    pushforwardDiagonalTripleIso R X Y K.obj

/-! ### Tag 0FZJ -/

/-- **Stacks Project, Tag 0FZJ.**  Let `R` be a ring, let `X` and `Y` be schemes over `R` with
`X` quasi-compact, separated and flat over `R`, and let `K` be a quasi-coherent kernel on
`X ×_R Y` satisfying the two conditions of [Stacks, Tag 0FZH] part (2).  Then there is a
surjection `𝒪_X ⊠ F_K(𝒪_X) ⟶ K`, where `F_K` is the integral transform of `K`.

The diagonal short exact sequence `0 → I → 𝒪_{X ×_R X} → 𝒪_Δ → 0` is sent by the exact
integrand `pr_{12}^*(-) ⊗ pr_{23}^*K` to a short exact sequence on `X ×_R X ×_R Y`, and
[Stacks, Tag 0FZI] makes its direct image along `pr_{13}` short exact again;  the surjection it
exhibits is the one asserted, once flat base change identifies its source with
`pr_2^*pr_{2,*}K = 𝒪_X ⊠ F_K(𝒪_X)` and the projection formula identifies its target with
`K`. -/
@[stacks 0FZJ "the surjection O_X ⊠ F(O_X) ⟶ K"]
theorem exists_epi_externalTensorProduct_unit (X Y : Over (Spec (.of R)))
    [CompactSpace X.left] [IsSeparated X.hom] [Flat X.hom]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (hK : integralTransformExactKernel R X Y K) :
    ∃ e : externalTensorProduct X.hom Y.hom (SheafOfModules.unit X.left.ringCatSheaf)
        ((quasicoherentIntegralTransform R X Y K).obj
          ⟨SheafOfModules.unit X.left.ringCatSheaf,
            Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
              X.left⟩).obj ⟶ K.obj, Epi e := by
  have hqc : QuasiCompact X.hom := quasiCompact_of_compactSpace X.hom
  have hepi := epi_pushforward_diagonalIntegrand_map R X Y K hK
  refine ⟨(externalTensorUnitIso R X Y K).hom ≫ (flatBaseChangeKernelIso R X Y K).hom ≫
      ((Scheme.Modules.pushforward (baseChangeTargetMap R X X Y)).mapIso
        (diagonalIntegrandUnitIso R X Y K)).inv ≫
      (Scheme.Modules.pushforward (baseChangeTargetMap R X X Y)).map
        ((diagonalIntegrand R X Y K).map (diagonalUnitMap R X)) ≫
      (pushforwardDiagonalIntegrandDiagonalIso R X Y K).hom, ?_⟩
  exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' (IsIso.epi_of_iso _)
    (epi_comp' (IsIso.epi_of_iso _) (epi_comp' hepi (Iso.isIso_hom _).epi_of_iso)))

end AlgebraicGeometry

end
