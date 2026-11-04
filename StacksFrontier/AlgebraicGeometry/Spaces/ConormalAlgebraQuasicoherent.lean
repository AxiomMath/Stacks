module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraIsCommutative
public import StacksFrontier.AlgebraicGeometry.Spaces.GradedAlgebraSheafCoprod
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence

/-!
# Quasi-coherence of the conormal algebra of an immersion of algebraic spaces

Let `i : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S`, with conormal algebra
`𝒞_{Z/X,*}` of Stacks 09RN (`AlgebraicGeometry.Space.conormalAlgebraOfImmersion`): the inverse
image along the closed factorisation `Z ⟶ X ∖ ∂Z` of the graded algebra `⨁_{n ≥ 0} 𝓘ⁿ` of the
powers of the ideal sheaf `𝓘` of `Z` in `X ∖ ∂Z`.  Stacks 09RN asserts that `𝒞_{Z/X,*}` is a
quasi-coherent sheaf of graded `𝒪_Z`-algebras.  This file proves it, degree by degree and for
the ungraded realization whose relative spectrum Stacks 09RU takes:

* `𝓘` is quasi-coherent, being the defining ideal sheaf of a closed subspace (Stacks 03MB), so
  every power `𝓘ⁿ` is quasi-coherent;
* the inverse image along a closed immersion of a quasi-coherent module is quasi-coherent
  (Stacks 03GA along a closed immersion), so every piece `𝒞_{Z/X,n} = i^*(𝓘ⁿ)` is;
* the pieces vanish in negative degrees, so the ungraded realization is the coproduct of the
  pieces and is quasi-coherent (Stacks 03M1).

## Main results

* `AlgebraicGeometry.Space.idealSheafPow_eq_idealPowSubmodule_ringSheaf`: the `n`-th power of a
  sheaf of ideals in the sense of `SheafOfModules.idealSheafPow` is its product with the structure
  sheaf in the sense of `AlgebraicGeometry.Space.idealPowSubmodule`; both are the local-membership
  closure of the sectionwise powers.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_kernelIdealSheafZPow_natCast`: the powers of the
  kernel ideal sheaf of a closed immersion are quasi-coherent.
* `AlgebraicGeometry.Space.isZero_conormalAlgebra_piece_of_neg`: the conormal algebra vanishes in
  negative degrees.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalAlgebraOfImmersion_piece`: **every
  homogeneous piece of the conormal algebra of an immersion is quasi-coherent.**
* `AlgebraicGeometry.Space.isQuasicoherent_conormalAlgebraSheafOfImmersion`: **the ungraded
  conormal algebra `𝒞_{Z/X,*}` of an immersion is a quasi-coherent sheaf of commutative
  `𝒪_Z`-algebras.**

## References

* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u


namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The two powers of a sheaf of ideals of `𝒪_Y` agree**: `SheafOfModules.idealSheafPow`,
defined by local membership in the sectionwise powers, is the product
`AlgebraicGeometry.Space.idealPowSubmodule` of the power with the structure sheaf.  Both are the
local-membership closure of `U ↦ 𝓘(U)ⁿ`. -/
theorem idealSheafPow_eq_idealPowSubmodule_ringSheaf (Y : AlgebraicSpaces B S hS)
    (I : IdealSheaves B S hS Y.1 Y.2) (n : ℕ) :
    SheafOfModules.idealSheafPow I n = idealPowSubmodule I n (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) := by
  refine le_antisymm (SheafOfModules.Submodule.le_iff.2 fun X x hx => ?_)
    (idealPowSubmodule_le I n fun X a ha z => ?_)
  · have hS' := (SheafOfModules.mem_idealSheafPow_iff I n x).1 hx
    refine (idealPowSubmodule I n _).isSheaf x
      ((SmallEtale.topology B S hS Y.1).superset_covering (fun W f hf => ?_) hS')
    have h := smul_mem_idealPowSubmodule_of_mem_pow I n
      (M := SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
      (X := op W) hf (SheafOfModules.unitOf 1)
    rw [SheafOfModules.unit_smul, mul_one] at h
    exact h
  · obtain ⟨T, hT, hTa⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule ha
    refine (SheafOfModules.mem_idealSheafPow_iff I n _).2
      ((SmallEtale.topology B S hS Y.1).superset_covering (fun W f hf => ?_) hT)
    have h1 := hTa f hf
    change _ ∈ Stacks.Sites.sectionIdeal I _ ^ n at h1
    show (((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.map f.op).hom (a * SheafOfModules.unitVal z) ∈ _
    have h2 := Ideal.mul_mem_right (α := (smallEtaleRingedSite B S hS Y.1 Y.2).O.obj.obj (op W))
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.map f.op).hom (SheafOfModules.unitVal z)) _ h1
    have h3 : (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.map f.op).hom (a * SheafOfModules.unitVal z) =
        (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.map f.op).hom a *
        (((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Y.1 Y.2).O)).obj.map f.op).hom (SheafOfModules.unitVal z) :=
      RingHom.map_mul _ _ _
    rw [h3]
    exact h2

variable {X Z : AlgebraicSpaces B S hS}

/-- **The powers of a quasi-coherent kernel ideal sheaf are quasi-coherent**, in every
nonnegative degree.  The `n`-th power in the sense of `SheafOfModules.idealSheafZPow` is
`Stacks.Sites.idealPow`, which is the product of itself with the structure sheaf, and that
product is quasi-coherent by `AlgebraicGeometry.Space.isQuasicoherentOnSite_idealPowSubmodule`. -/
theorem isQuasicoherentOnSite_kernelIdealSheafZPow_natCast (i : Z ⟶ X)
    (hI : (kernelIdealSheaf B S hS i).toSheafOfModules.IsQuasicoherentOnSite) (n : ℕ) :
    (kernelIdealSheafZPow B S hS i (n : ℤ)).toSheafOfModules.IsQuasicoherentOnSite := by
  have hpow : kernelIdealSheafZPow B S hS i (n : ℤ) =
      idealPowSubmodule (kernelIdealSheaf B S hS i) n (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) := by
    have h := SheafOfModules.idealSheafZPow_of_nonneg (kernelIdealSheaf B S hS i)
      (Int.natCast_nonneg n)
    rw [Int.toNat_natCast] at h
    exact h.trans (idealSheafPow_eq_idealPowSubmodule_ringSheaf B S hS X _ n)
  rw [hpow]
  exact isQuasicoherentOnSite_idealPowSubmodule B S hS X.1 X.2 (kernelIdealSheaf B S hS i)
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (SheafOfModules.isQuasicoherentOnSite_unit _) hI n

/-- The zero sheaf of ideals is a zero object of the sheaves of modules. -/
theorem isZero_zeroIdealSheaf_toSheafOfModules (Y : AlgebraicSpaces B S hS) :
    IsZero (SheafOfModules.zeroIdealSheaf (R := structureRingSheaf B S hS Y)).toSheafOfModules :=
  have hsub : ∀ U, Subsingleton ((SheafOfModules.zeroIdealSheaf
      (R := structureRingSheaf B S hS Y)).toSheafOfModules.val.obj U) := fun U =>
    ⟨fun a b => by
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      have ha' : a = 0 := ha
      have hb' : b = 0 := hb
      subst ha' hb'
      rfl⟩
  (IsZero.iff_id_eq_zero _).2 ((SheafOfModules.forget _).map_injective
    (PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun _x =>
      (hsub U).elim _ _)))

/-- **The conormal algebra vanishes in negative degrees**: its piece in a negative degree is the
inverse image of the zero sheaf of ideals, and inverse image, a left adjoint, preserves zero
objects. -/
theorem isZero_conormalAlgebra_piece_of_neg (i : Z ⟶ X) {n : ℤ} (hn : n < 0) :
    IsZero ((conormalAlgebra B S hS i).piece n) := by
  rw [conormalAlgebra_piece_neg B S hS i hn]
  have := (modulePullbackAdjunction B S hS i).leftAdjoint_preservesColimits
  exact ((isZero_zeroIdealSheaf_toSheafOfModules B S hS X).isInitial.isInitialObj
    (modulePullback B S hS i) _).isZero

attribute [local instance] pointTopology

variable {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Every homogeneous piece of the conormal algebra of an immersion is quasi-coherent**, in
every nonnegative degree: it is the inverse image along the closed factorisation of a power of
the ideal sheaf of the image, which is quasi-coherent, and inverse image along a closed
immersion preserves quasi-coherence. -/
theorem isQuasicoherentOnSite_conormalAlgebraOfImmersion_piece (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) (n : ℕ) :
    ((conormalAlgebraOfImmersion B S hS hX hZ i hi).piece (n : ℤ)).IsQuasicoherentOnSite := by
  rw [conormalAlgebraOfImmersion_piece]
  refine isQuasicoherentOnSite_modulePullback_of_isClosedImmersion B S hS _
    (isClosedImmersion_boundaryComplementLift B S hS hX hZ i hi) _ ?_
  refine isQuasicoherentOnSite_kernelIdealSheafZPow_natCast B S hS _ ?_ n
  rw [kernelIdealSheaf_immersionClosedFactorization]
  exact isQuasicoherentOnSite_definingIdealSheaf B S hS _ _

/-- **The conormal algebra of an immersion vanishes in negative degrees.** -/
theorem isZero_conormalAlgebraOfImmersion_piece_of_neg (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) {n : ℤ}
    (hn : n < 0) : IsZero ((conormalAlgebraOfImmersion B S hS hX hZ i hi).piece n) :=
  isZero_conormalAlgebra_piece_of_neg B S hS _ hn

/-- **The conormal algebra `𝒞_{Z/X,*}` of an immersion, as a sheaf of commutative
`𝒪_Z`-algebras**: its ungraded realization, which is commutative because the conormal algebra is
commutative in every pair of integer degrees
(`AlgebraicGeometry.Space.isCommutative_conormalAlgebra`). -/
abbrev conormalAlgebraSheafOfImmersion (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    AlgebraSheaf.{u, u} B S hS Z₀ hZ :=
  conormalAlgebraSheaf B S hS (immersionClosedFactorization B S hS hX hZ i hi)
    (isCommutative_conormalAlgebra B S hS (immersionClosedFactorization B S hS hX hZ i hi)).mul_comm

/-- **The conormal algebra `𝒞_{Z/X,*}` of an immersion is a quasi-coherent sheaf of commutative
`𝒪_Z`-algebras.**  Its module is the coproduct of the homogeneous pieces, which are
quasi-coherent and vanish in negative degrees. -/
theorem isQuasicoherent_conormalAlgebraSheafOfImmersion (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    (conormalAlgebraSheafOfImmersion B S hS hX hZ i hi).IsQuasicoherent :=
  isQuasicoherent_gradedAlgebraSheaf B S hS _ _ _
    (fun _ hn => isZero_conormalAlgebraOfImmersion_piece_of_neg B S hS hX hZ i hi hn)
    (isQuasicoherentOnSite_conormalAlgebraOfImmersion_piece B S hS hX hZ i hi)

end AlgebraicGeometry.Space

end
