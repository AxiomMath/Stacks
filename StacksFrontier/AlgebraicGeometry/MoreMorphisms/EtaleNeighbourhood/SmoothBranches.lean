module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.RingHom.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.RingTheory.Branches.Miscellaneous

/-!
# Branches of a scheme under a smooth morphism

A smooth morphism of schemes does not change the number of geometric branches at a point, and
does not change the number of branches at a point whose residue-field extension over the image
point is purely inseparable.

## Main results

* `AlgebraicGeometry.numberOfGeometricBranches_eq_of_smooth`: the number of geometric branches
  of the source at `x` equals that of the target at the image of `x`.
* `AlgebraicGeometry.numberOfBranches_eq_of_smooth_of_isPurelyInseparable`: the same for the
  number of branches, under the assumption that the residue-field extension is purely
  inseparable.

## Implementation notes

Both statements come from the ring-theoretic invariance
`numberOfBranches_eq_of_isLocalization_smooth`, which compares the branch counts of two local
rings `A → B` whenever `B` is a localization of a smooth `A`-algebra. The work is to exhibit the
stalk map `𝒪_{S, f x} → 𝒪_{X, x}` of a smooth morphism in that shape. Choosing affine opens
`V ∋ f x` and `U ∋ x` with `U ⊆ f⁻¹(V)`, the ring map `Γ(S, V) → Γ(X, U)` is smooth, the two
stalks are localizations of `Γ(S, V)` and `Γ(X, U)` at the corresponding primes, and the smooth
`𝒪_{S, f x}`-algebra `Γ(X, U) ⊗_{Γ(S, V)} 𝒪_{S, f x}` has `𝒪_{X, x}` as a localization: the
localization of a tensor product along one factor is the tensor product of the localizations, and
tensoring the localization `𝒪_{S, f x}` of `Γ(S, V)` with `𝒪_{X, x}` over `Γ(S, V)` returns
`𝒪_{X, x}`, because every element of the prime complement is already invertible there.

Both conclusions of the source lemma are proved at once, as the conjunction
`AlgebraicGeometry.numberOfBranchesOfLocalRing_stalk_eq_and_of_smooth`, since the construction of
the smooth presentation of the stalk map is shared.

The number of branches and of geometric branches of a *local ring* is written
`_root_.numberOfBranchesOfLocalRing`, respectively
`_root_.numberOfGeometricBranchesOfLocalRing`, to distinguish it from the scheme invariants of
the same stem.

## References

* [Stacks Project, Tag 0DQ2](https://stacks.math.columbia.edu/tag/0DQ2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The scalar tower induced by the right unitor of a tensor product. -/
private lemma tensorProduct_rid_isScalarTower {R B : Type u} [CommSemiring R]
    [CommSemiring B] [Algebra R B] (e : TensorProduct R B R ≃ₐ[B] B) :
    let : Algebra (TensorProduct R B R) B := e.toRingEquiv.toRingHom.toAlgebra
    IsScalarTower B (TensorProduct R B R) B := by
  intro _
  exact IsScalarTower.of_algebraMap_eq fun b => by
    change (algebraMap B B) b =
      (e.toRingEquiv.toRingHom) ((algebraMap B (TensorProduct R B R)) b)
    exact (e.commutes b).symm

/-- If `A` is a localization of `R` and `B` is an `A`-algebra, then `B ⊗[R] A ≃ₐ[B] B` by an
isomorphism restricting to `algebraMap A B` on the right factor. -/
private theorem exists_tensorProduct_algEquiv_comp_includeRight {R A B : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (M : Submonoid R) [IsLocalization M A] :
    ∃ e : TensorProduct R B A ≃ₐ[B] B, e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := B)).toRingHom = algebraMap A B := by
  let M₀ := M.map (Algebra.TensorProduct.includeRight (R := R) (A := B))
  let e₀ : TensorProduct R B R ≃ₐ[B] B := Algebra.TensorProduct.rid (R := R) (S := B) (A := B)
  let : Algebra (TensorProduct R B R) B := e₀.toRingEquiv.toRingHom.toAlgebra
  let : IsScalarTower B (TensorProduct R B R) B := tensorProduct_rid_isScalarTower e₀
  have hUnits₀ : Algebra.algebraMapSubmonoid B M₀ ≤ IsUnit.submonoid B := by
    rintro _ ⟨z, ⟨r, hr, rfl⟩, rfl⟩
    have hu : IsUnit (algebraMap A B (algebraMap R A r)) :=
      IsUnit.map (algebraMap A B) (IsLocalization.map_units A ⟨r, hr⟩)
    rw [← IsScalarTower.algebraMap_apply R A B] at hu
    change IsUnit (e₀ (Algebra.TensorProduct.includeRight r))
    simpa [e₀, Algebra.TensorProduct.rid_tmul, Algebra.smul_def] using hu
  let : IsLocalization M₀ B := IsLocalization.of_le_isUnit_of_bijective hUnits₀ e₀.bijective
  let e : TensorProduct R B A ≃ₐ[B] B :=
    IsLocalization.tensorProductEquivOfMapIncludeRight (R := R) (S := B) (M := M) (B := A) (C := B)
  refine ⟨e, IsLocalization.ringHom_ext M <| RingHom.ext fun r => ?_⟩
  change e (Algebra.TensorProduct.includeRight (algebraMap R A r)) =
    algebraMap A B (algebraMap R A r)
  calc
    e (Algebra.TensorProduct.includeRight (algebraMap R A r)) =
        e (algebraMap B (TensorProduct R B A) (algebraMap R B r)) := by
      congr 1
      calc
        Algebra.TensorProduct.includeRight (algebraMap R A r) =
            algebraMap R (TensorProduct R B A) r :=
          Algebra.TensorProduct.includeRight.commutes r
        _ = Algebra.TensorProduct.includeLeft (algebraMap R B r) :=
          (Algebra.TensorProduct.includeLeft.commutes r).symm
        _ = algebraMap B (TensorProduct R B A) (algebraMap R B r) := rfl
    _ = algebraMap R B r := e.commutes _
    _ = algebraMap A B (algebraMap R A r) := IsScalarTower.algebraMap_apply R A B r

/-- Let `A` be a localization of `R` and `B` a localization of a smooth `R`-algebra `T`, with
compatible maps `A → B` and `T → B`. Then `B` is a localization of a smooth `A`-algebra. -/
private theorem exists_smooth_isLocalization_of_smooth {R T A B : Type u} [CommRing R]
    [CommRing T] [CommRing A] [CommRing B] [Algebra R T] [Algebra R A] [Algebra T B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R T B]
    (M : Submonoid R) [IsLocalization M A] (N : Submonoid T) [IsLocalization N B]
    [Algebra.Smooth R T] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (N' : Submonoid C),
      Algebra.Smooth A C ∧ IsLocalization N' B := by
  obtain ⟨e, he⟩ := exists_tensorProduct_algEquiv_comp_includeRight (R := R) (A := A) (B := B) M
  let C := TensorProduct R T A
  let : Algebra A (TensorProduct R B A) :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := B) (B := A)
  let : SMul A (TensorProduct R B A) :=
    (Algebra.TensorProduct.rightAlgebra (R := R) (A := B) (B := A)).toSMul
  let : IsScalarTower R A (TensorProduct R B A) :=
    Algebra.TensorProduct.right_isScalarTower (R := R) (A := B) (B := A)
  let D := TensorProduct R B A
  let : Algebra A C := Algebra.TensorProduct.rightAlgebra (R := R) (A := T) (B := A)
  let : IsScalarTower R A C :=
    Algebra.TensorProduct.right_isScalarTower (R := R) (A := T) (B := A)
  let gTB : T →ₐ[R] B := IsScalarTower.toAlgHom R T B
  let gMap : C →ₐ[R] D := Algebra.TensorProduct.map gTB (AlgHom.id R A)
  let : Algebra C D := gMap.toRingHom.toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun a => by
    simp [C, D, RingHom.algebraMap_toAlgebra, gMap]
  let : IsScalarTower T C D := IsScalarTower.of_algebraMap_eq fun t => by
    change algebraMap T B t ⊗ₜ[R] (1 : A) = gMap (t ⊗ₜ[R] (1 : A))
    rw [Algebra.TensorProduct.map_tmul]
    simp [gTB]
  have hCD :
      (algebraMap C D).comp Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom := by
    ext a
    simp [C, D, RingHom.algebraMap_toAlgebra, gTB, gMap]
  let : IsLocalization (Algebra.algebraMapSubmonoid C N) D :=
    IsLocalization.tensorProduct_tensorProduct R A N B hCD
  let : Algebra C B := (e.toRingEquiv.toRingHom.comp (algebraMap C D)).toAlgebra
  have : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A B a = e (gMap (1 ⊗ₜ[R] a))
    rw [Algebra.TensorProduct.map_tmul]
    simp only [AlgHom.id_apply, map_one]
    exact (RingHom.congr_fun he a).symm
  let eC : D ≃ₐ[C] B := { e with commutes' := fun _ => rfl }
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.algebraMapSubmonoid C N, ?_, IsLocalization.isLocalization_of_algEquiv _ eC⟩
  let eSmooth : (TensorProduct R A T) ≃ₐ[A] C :=
    { toRingEquiv := (Algebra.TensorProduct.comm R A T).toRingEquiv
      commutes' := fun _ => rfl }
  exact RingHom.Smooth.respectsIso.left (algebraMap A (TensorProduct R A T))
    eSmooth.toRingEquiv (RingHom.smooth_algebraMap.mpr (Algebra.Smooth.baseChange R T A))

/-- **Stacks Project, Tag 0DQ2.** For a smooth morphism of schemes the local rings at a point and
at its image have the same number of geometric branches, and the same number of branches as soon
as the induced extension of residue fields is purely inseparable. -/
private theorem numberOfBranchesOfLocalRing_stalk_eq_and_of_smooth {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] (x : X) :
    _root_.numberOfGeometricBranchesOfLocalRing (X.presheaf.stalk x) =
        _root_.numberOfGeometricBranchesOfLocalRing (S.presheaf.stalk (f.base x)) ∧
      ((f.residueFieldMap x).hom.IsPurelyInseparable →
        _root_.numberOfBranchesOfLocalRing (X.presheaf.stalk x) =
          _root_.numberOfBranchesOfLocalRing (S.presheaf.stalk (f.base x))) := by
  classical
  let s : S := f.base x
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hsV (f ⁻¹ᵁ V).isOpen
  let R := Γ(S, V)
  let T := Γ(X, U)
  let A := S.presheaf.stalk s
  let B := X.presheaf.stalk x
  let p : Ideal R := (hV.primeIdealOf ⟨s, hsV⟩).asIdeal
  let q : Ideal T := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : Algebra R A := S.presheaf.algebra_section_stalk ⟨s, hsV⟩
  let : Algebra T B := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsLocalization.AtPrime A p := hV.isLocalization_stalk ⟨s, hsV⟩
  let : IsLocalization.AtPrime B q := hU.isLocalization_stalk ⟨x, hxU⟩
  let : Algebra R T := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (f.stalkMap x).hom
    infer_instance
  let : Algebra R B := ((algebraMap A B).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hRT : (algebraMap R B) = (algebraMap T B).comp (f.appLE V U hUV).hom := by
    ext r
    change (f.stalkMap x).hom ((S.presheaf.germ V s hsV).hom r) =
      (X.presheaf.germ U x hxU).hom ((f.appLE V U hUV).hom r)
    calc
      _ = (X.presheaf.germ (f ⁻¹ᵁ V) x (hUV hxU)).hom ((f.app V).hom r) :=
        Scheme.Hom.germ_stalkMap_apply f V x hsV r
      _ = (X.presheaf.germ U x hxU).hom ((f.appLE V U hUV).hom r) := by
        simp only [Scheme.Hom.appLE, CategoryTheory.homOfLE_leOfHom,
          CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          X.presheaf.germ_res_apply]
  let : IsScalarTower R T B := IsScalarTower.of_algebraMap_eq' hRT
  let : Algebra.Smooth R T := f.smooth_appLE hV hU hUV
  have hres := _root_.numberOfBranches_eq_of_isLocalization_smooth A
    (henselizationData A).carrier (strictHenselizationData A).carrier B
    (henselizationData B).carrier (strictHenselizationData B).carrier
    (SeparableClosure (ResidueField A)) (SeparableClosure (ResidueField B))
    (exists_smooth_isLocalization_of_smooth (R := R) (T := T) (A := A) (B := B)
      p.primeCompl q.primeCompl)
  exact ⟨hres.1.symm, fun h => (hres.2 h).symm⟩

/-- **Stacks Project, Tag 0DQ2.** A smooth morphism of schemes preserves the number of geometric
branches at a point. -/
@[stacks 0DQ2 "geometric_branches"]
public theorem numberOfGeometricBranches_eq_of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (x : X) :
    numberOfGeometricBranches X x = numberOfGeometricBranches S (f.base x) :=
  (numberOfBranchesOfLocalRing_stalk_eq_and_of_smooth f x).1

/-- **Stacks Project, Tag 0DQ2.** A smooth morphism of schemes preserves the number of branches
at a point whose residue field is a purely inseparable extension of the residue field of its
image. -/
@[stacks 0DQ2 "branches_purely_inseparable"]
public theorem numberOfBranches_eq_of_smooth_of_isPurelyInseparable {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] (x : X)
    (h : (f.residueFieldMap x).hom.IsPurelyInseparable) :
    numberOfBranches X x = numberOfBranches S (f.base x) :=
  (numberOfBranchesOfLocalRing_stalk_eq_and_of_smooth f x).2 h

end AlgebraicGeometry
