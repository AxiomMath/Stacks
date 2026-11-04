module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Ample.Defs

/-!
# Ampleness of positive tensor powers

An invertible sheaf of modules on a scheme is ample if and only if one, equivalently any, of its
positive tensor powers is ample.

Both directions compare nonvanishing loci. A global section `s` of `L` has an `n`th tensor power
`s^{⊗ n}`, a section of `L^{⊗ n}`, and the two have the same nonvanishing locus, because the
germ of a tensor product of sections avoids the maximal ideal exactly when both factors do. So an
affine nonvanishing locus for a section of `L^{⊗ k}` produces one for a section of
`(L^{⊗ n})^{⊗ k}`, which is `L^{⊗ nk}`, and conversely.

## Main results

* `AlgebraicGeometry.isAmple_iff_tensorPower_isAmple`: an invertible sheaf is ample if and only
  if its `n`th tensor power is, for any `n ≥ 1`.
* `AlgebraicGeometry.exists_section_power_nonvanishingOpen_eq`: a section of `L^{⊗ n}` has, in
  every higher multiple `L^{⊗ nm}` of that power, a section with the same nonvanishing open.
* `AlgebraicGeometry.isAmple_iff_of_moduleIso` and `AlgebraicGeometry.ample_of_moduleIso`:
  ampleness of an invertible module depends only on its isomorphism class.

## Implementation notes

The natural-number exponent is cast to an integer, since the tensor powers of Tag 01CU are
indexed by `ℤ`. Ampleness is `AlgebraicGeometry.Scheme.Modules.IsAmple` of Tag 01PS and the
nonvanishing locus is `Stacks.SheafOfModules.nonvanishingLocus` of Tag 01CY.

The multiplication `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}` is built here for *natural* exponents by
induction on `b`, from the successor comparison, the associator and the right unitor of the
sheaf tensor product; natural exponents are all this file needs.

A tensor product of sections vanishes exactly where one of its factors does: the stalk of
`F ⊗ G` at `x` is `F_x ⊗ G_x`, and `m ⊗ n` lies in `𝔪_x · (F_x ⊗ G_x)` if and only if
`m ∈ 𝔪_x · F_x` or `n ∈ 𝔪_x · G_x`, as one sees by mapping both factors to the residue field.

## References

* [EGA II, Proposition 4.5.6(i)]
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.SheafOfModules

universe v₁ u₁ w₁ u

namespace AlgebraicGeometry

/-- The two developments of Tag 01CS — `AlgebraicGeometry.SheafOfModules.IsInvertible`, for
which the tensor powers of Tag 01CU are stated, and `Stacks.SheafOfModules.IsInvertible`, for
which the nonvanishing locus of Tag 01CY is — ask for a tensor functor with the same universal
property, so the datum witnessing one witnesses the other. Transporting it is all this does. -/
local instance stacksIsInvertible_of_isInvertible {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} (O : Cᵒᵖ ⥤ CommRingCat.{w₁})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    (L : _root_.SheafOfModules.{w₁} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
    [SheafOfModules.IsInvertible O hO L] :
    Stacks.SheafOfModules.IsInvertible O hO L := by
  obtain ⟨F, hF, ⟨u⟩⟩ :=
    Stacks.SheafOfModules.IsInvertible.exists_tensorFunctor (O := O) (hO := hO) (L := L)
  exact ⟨F, hF, ⟨{ ι := u.ι, bijective := u.bijective }⟩⟩

/-- Presheaves of abelian groups on the opens of a scheme can be sheafified. -/
noncomputable local instance (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the opens of a scheme, a morphism of presheaves of abelian groups is inverted by
sheafification exactly when it is locally bijective. -/
noncomputable local instance (X : Scheme.{u}) :
    (Opens.grothendieckTopology ↥X).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

/-- Every integer tensor power of an invertible sheaf of modules over the structure ring sheaf of
a scheme is invertible. This is
`Stacks.SheafOfModules.Invertible.tensorPower_isInvertible` restated with the structure presheaf
spelled as `X.toRingedSpace.presheaf`, which is the form the statements below are in and the form
typeclass search can match. -/
noncomputable local instance isInvertible_tensorPowerOfSheaf (X : Scheme.{u})
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property))
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M] (n : ℤ) :
    SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property M n) :=
  Invertible.tensorPower_isInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property M n

/-- The same statement for the sheaves of modules of the scheme itself, whose ring sheaf is only
reducibly the structure ring sheaf of the underlying ringed space. -/
noncomputable local instance isInvertible_tensorPowerOfScheme (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (n : ℤ) :
    SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L n) :=
  Invertible.tensorPower_isInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L n

/-- The stalk of a sheaf of modules over the structure ring sheaf of the ringed space underlying
a scheme, as a module over the stalk of the structure sheaf:
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` with the ring presheaf spelled as
`X.toRingedSpace.presheaf`. -/
noncomputable local instance stalkModuleOfSheaf {X : Scheme.{u}}
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property)) (x : X) :
    Module (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace M.val x) :=
  Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace M.val x

/-- The stalk of a sheaf of modules on a scheme at a point, as a module over the stalk of the
structure sheaf. This is `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule` restated for
the sheaves of modules of a scheme, whose ring sheaf is only reducibly the structure ring sheaf of
the underlying ringed space, so that typeclass search finds it. -/
noncomputable local instance stalkModuleOfSchemeModules {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace F.val x) :=
  Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace F.val x

open Opposite TensorProduct

/-- The tensor product `s ⊗ t` of a global section `s` of `F` and a global section `t` of `G`, as
a global section of `F ⊗ G`: over each open `U` it is the image of `s|_U ⊗ t|_U` in the
sheafified tensor product. -/
noncomputable def tensorSections {X : Scheme.{u}} (F G : X.Modules)
    (s : F.sections) (t : G.sections) :
    (Invertible.tensorProduct X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property F G).sections := by
  classical
  let T := Invertible.tensorProduct X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property F G
  refine PresheafOfModules.sectionsMk (fun U =>
    Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace F G U
      ((s.eval U) ⊗ₜ[X.presheaf.obj U] (t.eval U))) ?_
  intro U V f
  change ((T.val.map f).hom
    (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace F G U
      ((s.eval U) ⊗ₜ[X.presheaf.obj U] (t.eval U)))) = _
  have h := (Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X.toRingedSpace
    ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (F.val) (G.val)))).naturality f
  have h' := congrArg (fun q => q.hom
    ((s.eval U) ⊗ₜ[X.presheaf.obj U] (t.eval U))) h.symm
  change ((T.val.map f).hom
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace F G U
        ((s.eval U) ⊗ₜ[X.presheaf.obj U] (t.eval U)))) =
    Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace F G V
      ((F.val.map f).hom (s.eval U)
        ⊗ₜ[X.presheaf.obj V]
        (G.val.map f).hom (t.eval U))
    at h'
  have hs := PresheafOfModules.sections_property s f
  have ht := PresheafOfModules.sections_property t f
  change (F.val.map f).hom (s.eval U) = _ at hs
  change (G.val.map f).hom (t.eval U) = _ at ht
  rwa [hs, ht] at h'

private noncomputable def tensorPowerSection {X : Scheme.{u}} {L : X.Modules}
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (s : L.sections) : (n : ℕ) →
      (Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L ((n + 1 : ℕ) : ℤ)).sections
  | 0 => SheafOfModules.sectionsMap
      (Invertible.tensorPowerOneIso X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L).symm.hom s
  | n + 1 => SheafOfModules.sectionsMap
      (Invertible.tensorPowerSuccIso X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L ((n + 1 : ℕ) : ℤ)).hom
      (tensorSections
        (Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L ((n + 1 : ℕ) : ℤ)) L
        (tensorPowerSection s n) s)

private theorem tensorSections_stalk {X : Scheme.{u}} {F G : X.Modules}
    (s : F.sections) (t : G.sections) (x : X) :
    let T := Invertible.tensorProduct X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property F G
    (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace x F G)
        (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace T.val x ⊤ (by simp)
          ((tensorSections F G s t).eval (op ⊤))) =
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace F.val x ⊤ (by simp)
        (s.eval (op ⊤))) ⊗ₜ[
        Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x]
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace G.val x ⊤ (by simp)
        (t.eval (op ⊤))) :=
  Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ X.toRingedSpace x F G ⊤ (by simp)
    (s.eval (op ⊤)) (t.eval (op ⊤))

private theorem exists_residueLinearMap {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (m : M)
    (hm : m ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) :
    ∃ f : M →ₗ[R] IsLocalRing.ResidueField R, f m ≠ 0 := by
  let I := IsLocalRing.maximalIdeal R
  let Q := M ⧸ (I • (⊤ : Submodule R M))
  let k := IsLocalRing.ResidueField R
  let : Module k Q := Module.instQuotientIdealSubmoduleHSMulTop M I
  let : IsScalarTower R k Q :=
    inferInstanceAs (IsScalarTower R (R ⧸ I) Q)
  let v : Q := (I • (⊤ : Submodule R M)).mkQ m
  have hv : v ≠ 0 := fun h => hm ((Submodule.Quotient.mk_eq_zero _).mp h)
  let b := Module.Free.chooseBasis k Q
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp (b.repr.map_ne_zero_iff.mpr hv)
  let g : Q →ₗ[k] k := b.coord i
  let f : M →ₗ[R] k := (g.restrictScalars R).comp
    (I • (⊤ : Submodule R M)).mkQ
  refine ⟨f, ?_⟩
  show b.coord i v ≠ 0
  simpa [Module.Basis.coord] using hi

private noncomputable def residueTensorMulMap {R : Type*} [CommRing R] [IsLocalRing R] :
    IsLocalRing.ResidueField R ⊗[R] IsLocalRing.ResidueField R →ₗ[R]
      IsLocalRing.ResidueField R :=
  TensorProduct.lift (LinearMap.mul R (IsLocalRing.ResidueField R))

private theorem tensor_not_mem_maximalIdeal_iff {R : Type*} [CommRing R] [IsLocalRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (m : M) (n : N) :
    m ⊗ₜ[R] n ∉ IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R (M ⊗[R] N)) ↔
      m ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ∧
        n ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) := by
  constructor
  · exact fun h => ⟨fun hm => h (Submodule.smul_top_le_comap_smul_top _ ((mk R M N).flip n) hm),
      fun hn => h (Submodule.smul_top_le_comap_smul_top _ (mk R M N m) hn)⟩
  · rintro ⟨hm, hn⟩ hmem
    let k := IsLocalRing.ResidueField R
    obtain ⟨f, hf⟩ := exists_residueLinearMap m hm
    obtain ⟨g, hg⟩ := exists_residueLinearMap n hn
    let ψ : M ⊗[R] N →ₗ[R] k :=
      (residueTensorMulMap (R := R)).comp (TensorProduct.map f g)
    have hz (z : M ⊗[R] N) (hz : z ∈ IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R (M ⊗[R] N))) : ψ z = 0 := by
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr z hz
        have hr0 : algebraMap R k r = 0 := (IsLocalRing.residue_eq_zero_iff r).mpr hr
        rw [map_smul, Algebra.smul_def, hr0, zero_mul]
      · intro a b ha hb
        simp [map_add, ha, hb]
    have hval : ψ (m ⊗ₜ[R] n) = f m * g n := by
      show residueTensorMulMap ((TensorProduct.map f g) (m ⊗ₜ[R] n)) = _
      rw [TensorProduct.map_tmul, residueTensorMulMap, TensorProduct.lift.tmul]
      rfl
    exact mul_ne_zero hf hg (hval.symm.trans (hz _ hmem))

private theorem linearEquiv_mem_maximalIdeal_smul_iff
    {R : Type*} [CommRing R] [IsLocalRing R]
    {M N : Type*} [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (m : M) :
    e m ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) ↔
      m ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) :=
  ⟨fun hm => by simpa using Submodule.smul_top_le_comap_smul_top _ (e.symm : N →ₗ[R] M) hm,
    fun hm => Submodule.smul_top_le_comap_smul_top _ (e : M →ₗ[R] N) hm⟩

/-- The tensor product of two global sections is nonvanishing at a point exactly when both
factors are. -/
theorem tensorSections_nonvanishing_iff {X : Scheme.{u}}
    {F G : X.Modules} (s : F.sections) (t : G.sections) (x : X) :
    x ∈ nonvanishingLocus (X := X.toRingedSpace)
        (Invertible.tensorProduct X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property F G)
        (tensorSections F G s t) ↔
      x ∈ nonvanishingLocus (X := X.toRingedSpace) F s ∧
      x ∈ nonvanishingLocus (X := X.toRingedSpace) G t := by
  have hs := tensorSections_stalk s t x
  have hlin := @linearEquiv_mem_maximalIdeal_smul_iff
    (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x) _ _ _ _ _
    (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
        F).obj G).val x) _ _
    (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace x F G)
    (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace
      (Invertible.tensorProduct X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property F G).val x ⊤ (by simp)
      ((tensorSections F G s t).eval (op ⊤)))
  have hlin := (Iff.of_eq (congrArg
    (fun tensorValue :
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace F.val x) ⊗[
        Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x]
        (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace G.val x) =>
      tensorValue ∈ IsLocalRing.maximalIdeal
        (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x) • ⊤)
    hs)).symm.trans hlin
  show Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace
        (Invertible.tensorProduct X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property F G).val x ⊤ (by simp)
        ((tensorSections F G s t).eval (op ⊤)) ∉
      IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
        X.toRingedSpace x) •
        (⊤ : Submodule (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
          (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace
            (Invertible.tensorProduct X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property F G).val x)) ↔
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace F.val x ⊤ (by simp)
        (s.eval (op ⊤)) ∉
        IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
          X.toRingedSpace x) •
          (⊤ : Submodule (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
            (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace F.val x))) ∧
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace G.val x ⊤ (by simp)
        (t.eval (op ⊤)) ∉
        IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
          X.toRingedSpace x) •
          (⊤ : Submodule (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
            (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace G.val x)))
  exact (not_congr hlin).symm.trans (tensor_not_mem_maximalIdeal_iff
    (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace F.val x ⊤ (by simp)
      (s.eval (op ⊤)))
    (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace G.val x ⊤ (by simp)
      (t.eval (op ⊤))))

private noncomputable def tensorPowerIso {X : Scheme.{u}} {L M : X.Modules}
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (e : L ≅ M) : (n : ℕ) →
      Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ) ≅
      Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property M (n : ℤ)
  | 0 => Iso.refl _
  | n + 1 =>
      (Invertible.tensorPowerSuccIso X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).symm ≪≫
      Invertible.tensorProductIso X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
        (tensorPowerIso e n) e ≪≫
      Invertible.tensorPowerSuccIso X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property M (n : ℤ)

/-- Transporting a global section along an isomorphism of sheaves of modules does not change its
nonvanishing locus. -/
theorem nonvanishingLocus_iso {X : Scheme.{u}} {L M : X.Modules}
    (e : L ≅ M) (s : L.sections) (x : X) :
    x ∈ nonvanishingLocus (X := X.toRingedSpace) M (SheafOfModules.sectionsMap e.hom s) ↔
      x ∈ nonvanishingLocus (X := X.toRingedSpace) L s := by
  have hbij : Function.Bijective
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace L.val M.val e.hom.val
        x) := by
    have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorStalkRingedSpace.O
          X.toRingedSpace)).map e.hom.val)) :=
      inferInstanceAs (IsIso (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
        ((PresheafOfModules.toPresheaf
          (Stacks.SheafOfModules.TensorStalkRingedSpace.O X.toRingedSpace)).mapIso
            ((SheafOfModules.forget _).mapIso e))).hom))
    exact (ConcreteCategory.isIso_iff_bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorStalkRingedSpace.O
          X.toRingedSpace)).map e.hom.val))).mp
      this
  have hgerm : Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace M.val x ⊤ (by
    simp)
      ((SheafOfModules.sectionsMap e.hom s).eval (op ⊤)) =
      Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X.toRingedSpace L.val M.val e.hom.val x
        (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace L.val x ⊤ (by simp)
          (s.eval (op ⊤))) :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply' ⊤ x (by simp)
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorStalkRingedSpace.O
        X.toRingedSpace)).map e.hom.val)
      (s.eval (op ⊤))).symm
  show Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace M.val x ⊤ (by simp)
        ((SheafOfModules.sectionsMap e.hom s).eval (op ⊤)) ∉
      IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
        X.toRingedSpace x) •
        (⊤ : Submodule (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
          (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace M.val x)) ↔
      Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace L.val x ⊤ (by simp)
        (s.eval (op ⊤)) ∉
        IsLocalRing.maximalIdeal (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
          X.toRingedSpace x) •
          (⊤ : Submodule (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace x)
            (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace L.val x))
  rw [hgerm]
  exact not_congr (linearEquiv_mem_maximalIdeal_smul_iff
    (LinearEquiv.ofBijective _ hbij)
    (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace L.val x ⊤ (by simp)
      (s.eval (op ⊤))))

/-- Transporting a global section along an isomorphism of sheaves of modules does not change its
nonvanishing open. -/
private theorem nonvanishingOpen_sectionsMap_iso {X : Scheme.{u}} {L M : X.Modules}
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (e : L ≅ M) (s : L.sections) :
    nonvanishingOpen (X := X.toRingedSpace) M (SheafOfModules.sectionsMap e.hom s) =
      nonvanishingOpen (X := X.toRingedSpace) L s := by
  ext y
  exact nonvanishingLocus_iso e s y

/-- Ampleness of `L` transfers to `M` if every section of a positive power of `L` has, in some
positive power of `M`, a section with the same nonvanishing open. -/
private theorem isAmple_of_exists_section_nonvanishingOpen_eq {X : Scheme.{u}} (L M : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (hL : Scheme.Modules.IsAmple X L)
    (h : ∀ k : ℕ, 1 ≤ k → ∀ s : (Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (k : ℤ)).sections,
      ∃ k' : ℕ, 1 ≤ k' ∧ ∃ t : (Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property M (k' : ℤ)).sections,
        nonvanishingOpen (X := X.toRingedSpace) _ t =
          nonvanishingOpen (X := X.toRingedSpace) _ s) :
    Scheme.Modules.IsAmple X M := by
  obtain ⟨hc, hx⟩ := (Scheme.Modules.isAmple_iff X L).1 hL
  refine (Scheme.Modules.isAmple_iff X M).2 ⟨hc, fun x => ?_⟩
  obtain ⟨k, hk, s, hs, haff⟩ := hx x
  obtain ⟨k', hk', t, ht⟩ := h k hk s
  exact ⟨k', hk', t, ht ▸ hs, ht ▸ haff⟩

/-- **Ampleness is carried along an isomorphism of invertible modules.** A global section of
`M^{⊗ n}` with affine nonvanishing open is obtained from one of `L^{⊗ n}` by transporting it
along the `n`th tensor power of the isomorphism, which preserves the nonvanishing locus. -/
theorem ample_of_moduleIso {X : Scheme.{u}} {L M : X.Modules}
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (e : L ≅ M) (hL : Scheme.Modules.IsAmple X L) : Scheme.Modules.IsAmple X M :=
  isAmple_of_exists_section_nonvanishingOpen_eq L M hL fun n hn s =>
    ⟨n, hn, SheafOfModules.sectionsMap (tensorPowerIso e n).hom s,
      nonvanishingOpen_sectionsMap_iso _ s⟩

/-- **Ampleness of an invertible module depends only on its isomorphism class.** -/
theorem isAmple_iff_of_moduleIso {X : Scheme.{u}} {L M : X.Modules}
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    (e : L ≅ M) : Scheme.Modules.IsAmple X L ↔ Scheme.Modules.IsAmple X M :=
  ⟨ample_of_moduleIso e, ample_of_moduleIso e.symm⟩

private noncomputable def powerAddIso (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (a : ℕ) : (b : ℕ) →
      Invertible.tensorProduct X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
        (Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (a : ℤ))
        (Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (b : ℤ)) ≅
      Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L ((a + b : ℕ) : ℤ)
  | 0 =>
      Invertible.tensorProductIso X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property (Iso.refl _)
          (Invertible.tensorPowerReindex X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L
            (by simp : (((0 : ℕ) : ℤ)) = 0)) ≪≫
        Invertible.tensorProductRightUnitor X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property _ ≪≫
        Invertible.tensorPowerReindex X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (by simp)
  | b + 1 =>
      Invertible.tensorProductIso X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property (Iso.refl _)
          (Invertible.tensorPowerSuccIso X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (b : ℤ)).symm ≪≫
        (Invertible.tensorProductAssociator X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property _ _ _).symm ≪≫
        Invertible.tensorProductIso X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property (powerAddIso X L a b)
          (Iso.refl _) ≪≫
        Invertible.tensorPowerSuccIso X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L ((a + b : ℕ) : ℤ) ≪≫
        Invertible.tensorPowerReindex X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (by push_cast; ring)

private noncomputable def powerMulIso (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (n : ℕ) : (k : ℕ) →
      Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
        (Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)) (k : ℤ) ≅
      Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L ((n * k : ℕ) : ℤ)
  | 0 => Iso.refl _
  | k + 1 =>
      (Invertible.tensorPowerSuccIso X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (Invertible.tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) (k : ℤ)).symm ≪≫
        Invertible.tensorProductIso X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (powerMulIso X L n k) (Iso.refl _) ≪≫
        powerAddIso X L (n * k) n ≪≫
        Invertible.tensorPowerReindex X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (by
            rw [Nat.mul_succ, Int.natCast_add])

private theorem ample_of_power_isAmple {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (n : ℕ) (hn : 1 ≤ n)
    (h : Scheme.Modules.IsAmple X
      (Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ))) :
    Scheme.Modules.IsAmple X L :=
  isAmple_of_exists_section_nonvanishingOpen_eq _ L h fun k hk s =>
    ⟨n * k, Nat.mul_pos hn hk, SheafOfModules.sectionsMap (powerMulIso X L n k).hom s,
      nonvanishingOpen_sectionsMap_iso _ s⟩

private theorem tensorPowerSection_nonvanishingLocus {X : Scheme.{u}} {L : X.Modules}
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (s : L.sections) (n : ℕ) (x : X) :
    x ∈ nonvanishingLocus (X := X.toRingedSpace)
        (Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L ((n + 1 : ℕ) : ℤ))
        (tensorPowerSection s n) ↔
      x ∈ nonvanishingLocus (X := X.toRingedSpace) L s := by
  induction n with
  | zero =>
      exact nonvanishingLocus_iso
        (Invertible.tensorPowerOneIso X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L).symm s x
  | succ n ih =>
      let Ln := Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L ((n + 1 : ℕ) : ℤ)
      let e := Invertible.tensorPowerSuccIso X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L ((n + 1 : ℕ) : ℤ)
      exact (nonvanishingLocus_iso e (tensorSections Ln L (tensorPowerSection s n) s) x).trans <|
        (tensorSections_nonvanishing_iff (tensorPowerSection s n) s x).trans
          (and_iff_right_of_imp ih.mpr)

/-- The `(n + 1)`st tensor power of a section has the same nonvanishing open as the section. -/
private theorem nonvanishingOpen_tensorPowerSection {X : Scheme.{u}} {L : X.Modules}
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (s : L.sections) (n : ℕ) :
    nonvanishingOpen (X := X.toRingedSpace) _ (tensorPowerSection s n) =
      nonvanishingOpen (X := X.toRingedSpace) L s := by
  ext x
  exact tensorPowerSection_nonvanishingLocus s n x

/-- **A section of a tensor power has, in every higher multiple of that power, a section with the
same nonvanishing open.**  Given `s ∈ Γ(X, L^{⊗ n})` and `m ≥ 1`, the `m`th tensor power
`s^{⊗ m}` is a section of `(L^{⊗ n})^{⊗ m} ≅ L^{⊗ nm}`, and a tensor product of sections
vanishes exactly where one of its factors does, so transporting it along that isomorphism gives
a section of `L^{⊗ nm}` with nonvanishing open `X_s`.

This is what lets two nonvanishing opens coming from sections of *different* powers be compared
inside a single common power. -/
theorem exists_section_power_nonvanishingOpen_eq {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (n : ℕ) (s : (Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ t : (Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L ((n * m : ℕ) : ℤ)).sections,
      nonvanishingOpen (X := X.toRingedSpace) _ t =
        nonvanishingOpen (X := X.toRingedSpace) _ s := by
  cases m with
  | zero => omega
  | succ m =>
      exact ⟨_, (nonvanishingOpen_sectionsMap_iso (powerMulIso X L n (m + 1)) _).trans
        (nonvanishingOpen_tensorPowerSection s m)⟩

/-- An invertible sheaf is ample if and only if any of its positive tensor
powers is ample. -/
@[stacks 01PT, ega "II 4.5.6" "(i)"]
theorem isAmple_iff_tensorPower_isAmple (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (n : ℕ) (hn : 1 ≤ n) :
    Scheme.Modules.IsAmple X L ↔
    Scheme.Modules.IsAmple X
        (Invertible.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)) := by
  refine ⟨fun hL => isAmple_of_exists_section_nonvanishingOpen_eq L _ hL fun k hk s => ?_,
    ample_of_power_isAmple L n hn⟩
  have hsub : (((n - 1 + 1 : ℕ) : ℤ)) = (n : ℤ) := by omega
  have hcomm : ((k * n : ℕ) : ℤ) = ((n * k : ℕ) : ℤ) := by rw [Nat.mul_comm]
  let e := Invertible.tensorPowerReindex X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Invertible.tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (k : ℤ)) hsub ≪≫
    powerMulIso X L k n ≪≫
    Invertible.tensorPowerReindex X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L hcomm ≪≫
    (powerMulIso X L n k).symm
  exact ⟨k, hk, SheafOfModules.sectionsMap e.hom (tensorPowerSection s (n - 1)),
    (nonvanishingOpen_sectionsMap_iso e _).trans (nonvanishingOpen_tensorPowerSection s _)⟩

/-- **A global section of a positive tensor power has, in every further positive power, a
section with the same nonvanishing open.** Replacing `L^{⊗ n}` by `L^{⊗ nm}` therefore does not
change the open on which the section is invertible, which is what lets two sections of different
powers be compared after passing to a common power. -/
theorem exists_sections_tensorPower_nonvanishingOpen_eq (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (n : ℕ) (s : (Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ t : (Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L ((n * m : ℕ) : ℤ)).sections,
      nonvanishingOpen (X := X.toRingedSpace)
          (Invertible.tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L ((n * m : ℕ) : ℤ)) t =
        nonvanishingOpen (X := X.toRingedSpace)
          (Invertible.tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s :=
  exists_section_power_nonvanishingOpen_eq L n s m hm

end AlgebraicGeometry
