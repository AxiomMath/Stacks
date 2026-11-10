module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.Norm.Transitivity
public import StacksCore.RingTheory.NormTrace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# A norm of the function-field degree for a finite surjective morphism onto a normal scheme

Let `f : X ⟶ Y` be a finite surjective morphism of integral schemes with `Y` normal. Then `f`
carries a norm (`Stacks.Norm.MorphismNorm`) of degree `[R(X) : R(Y)]`, the degree of the
induced extension of function fields.

The construction is the source's. Over a nonempty affine open `V ⊆ Y` the ring `A = Γ(Y, V)`
is a normal domain with fraction field `K = R(Y)`, the ring `B = Γ(X, f⁻¹V)` is a finite
`A`-algebra with fraction field `L = R(X)`, and for `s ∈ B` the field norm
`N_{L/K}(s) ∈ K` is integral over `A` — so, `A` being integrally closed, it *is* an element
of `A`. That assignment is multiplicative, and because it is characterized inside `K` by a
formula that does not mention `V`, the values on two affine opens agree on the overlap; the
sheaf condition then glues them to a norm on an arbitrary open. Vanishing is preserved
because the constant coefficient of the minimal polynomial of `s` over `A` is, up to sign and
a power, the norm, and it is killed by any ring map killing `s`.

## Main results

* `Stacks.Divisors.exists_norm_of_finite_surjective_of_normal`: **Tag 0BD3.**

## Implementation notes

The function-field homomorphism `φ : R(Y) →+* R(X)` is returned alongside the norm rather than
being taken as given, and it is pinned down by the compatibility clause: on every open `U` of
`Y` meeting the image, `φ` carries the germ at the generic point of a section of `𝒪_Y(U)` to
the germ of its pullback. Without that clause the statement would only assert the existence of
*some* field extension of the stated degree, which is weaker than the source.

A section of `𝒪_Y(U)` on an integral scheme is determined by its germ at the generic point,
which is what `Stacks.Divisors.sections_ext` records (with the empty open handled separately,
where the section ring is trivial). Every identity below about the glued norm is proved that
way, in `R(Y)`, rather than by a computation with the gluing data.

## References

* [Stacks Project, Tag 0BD3](https://stacks.math.columbia.edu/tag/0BD3)
* [Stacks Project, Tag 033L](https://stacks.math.columbia.edu/tag/033L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IntermediateField

universe u

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)


private theorem map_genericPoint_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [Surjective f] :
    f (genericPoint X) = genericPoint Y := by
  have hη := (genericPoint_spec X).image f.continuous
  have himage : f '' (Set.univ : Set X) = (Set.univ : Set Y) := by
    rw [Set.image_univ, range_eq_univ]
  have hη' : IsGenericPoint (f (genericPoint X)) (Set.univ : Set Y) := by
    simpa only [himage, closure_univ] using hη
  exact ((genericPoint_spec Y).eq hη').symm

private theorem normal_affine {Y : Scheme.{u}} [IsIntegral Y] [IsNormal Y]
    (U : Y.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(Y, U) := by
  let V : Y.affineOpens := ⟨U, hU⟩
  let : IsDomain Γ(Y, V.1) := IsIntegral.component_integral V.1
  exact (isNormal_iff_forall_affineOpen_normal Y).mp
    (inferInstance : IsNormal Y) V ‹Nonempty U›

private instance preimage_nonempty
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    (U : Y.Opens) [Nonempty U] : Nonempty (f ⁻¹ᵁ U) := by
  obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty U›
  obtain ⟨x, rfl⟩ := f.surjective y
  exact ⟨⟨x, hy⟩⟩

private theorem genericPoint_mem {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [Nonempty U] :
    genericPoint X ∈ U :=
  (genericPoint_spec X).mem_open_set_iff U.isOpen |>.2 (by simpa using ‹Nonempty U›)

/-- The field norm of the image of an element of a finite `A`-algebra `B` is integral over `A`. -/
private theorem isIntegral_norm_algebraMap {A B K L : Type*} [CommRing A] [CommRing B]
    [Field K] [Field L] [Algebra A B] [Algebra B L] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B] (s : B) :
    IsIntegral A (Algebra.norm K (algebraMap B L s)) :=
  Algebra.isIntegral_norm K
    (IsIntegral.map (IsScalarTower.toAlgHom A B L) (IsIntegral.of_finite A s))

private abbrev FunctionFieldHomCompatible {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] (φ : Y.functionField →+* X.functionField) : Prop :=
  ∀ (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : Γ(Y, U)),
    φ (Y.germToFunctionField U s) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s)

private noncomputable def normOnAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    (U : Y.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    Γ(X, f ⁻¹ᵁ U) →* Γ(Y, U) := by
  classical
  letI : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let A := Γ(Y, U)
  let B := Γ(X, f ⁻¹ᵁ U)
  letI : IsDomain A := IsIntegral.component_integral U
  letI : IsDomain B := IsIntegral.component_integral (f ⁻¹ᵁ U)
  letI : IsIntegrallyClosed A := normal_affine U hU
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI : Module.Finite A B := f.finite_app U hU
  let K := Y.functionField
  let L := X.functionField
  letI : Algebra A K := inferInstance
  letI : Algebra B L := inferInstance
  letI : Algebra K L := φ.toAlgebra
  letI : Algebra A L := (φ.comp (Y.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  letI : IsScalarTower A B L :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact hcompat U a)
  letI : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen Y U hU
  letI : IsIntegralClosure A A K := inferInstance
  have hint (s : B) : IsIntegral A (Algebra.norm K (algebraMap B L s)) :=
    isIntegral_norm_algebraMap s
  exact {
    toFun := fun s => IsIntegralClosure.mk' A (Algebra.norm K (algebraMap B L s)) (hint s)
    map_one' := by simp
    map_mul' := fun a b => by
      simpa using IsIntegralClosure.mk'_mul A
        (Algebra.norm K (algebraMap B L a)) (Algebra.norm K (algebraMap B L b))
        (hint a) (hint b)
  }

private theorem normOnAffine_germ
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (hU : IsAffineOpen U)
    (s : Γ(X, f ⁻¹ᵁ U)) :
    letI : Algebra Y.functionField X.functionField := φ.toAlgebra
    Y.germToFunctionField U (normOnAffine f φ hcompat U hU s) =
      Algebra.norm Y.functionField (X.germToFunctionField (f ⁻¹ᵁ U) s) := by
  classical
  let : Algebra Y.functionField X.functionField := φ.toAlgebra
  let : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let A := Γ(Y, U)
  let B := Γ(X, f ⁻¹ᵁ U)
  let K := Y.functionField
  let L := X.functionField
  let : IsDomain A := IsIntegral.component_integral U
  let : IsDomain B := IsIntegral.component_integral (f ⁻¹ᵁ U)
  let : Algebra A B := (f.app U).hom.toAlgebra
  let : Module.Finite A B := f.finite_app U hU
  let : IsIntegrallyClosed A := normal_affine U hU
  let : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen Y U hU
  let : IsIntegralClosure A A K := inferInstance
  let : Algebra A L := (φ.comp (Y.germToFunctionField U).hom).toAlgebra
  let : Algebra B L := inferInstance
  let : Algebra K L := φ.toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  let : IsScalarTower A B L :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact hcompat U a)
  change algebraMap A K
    (IsIntegralClosure.mk' (R := A) (B := K) A
      (Algebra.norm K (algebraMap B L s)) (isIntegral_norm_algebraMap s)) = _
  rw [IsIntegralClosure.algebraMap_mk']
  rfl

private theorem affineOpenCover {Y : Scheme.{u}} (U : Y.Opens) :
    U ≤ ⨆ V : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V}, (V : Y.Opens) := by
  intro y hy
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hy
  let i : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V} :=
    ⟨V, hV, hVU, ⟨⟨y, hyV⟩⟩⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hyV⟩

private noncomputable def affineNormFamily
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    {U : Y.Opens} (s : Γ(X, f ⁻¹ᵁ U))
    (V : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V}) : Γ(Y, V.1) := by
  letI : Nonempty V.1 := V.2.2.2
  exact normOnAffine f φ hcompat V.1 V.2.1
    (X.presheaf.map (homOfLE (f.preimage_mono V.2.2.1)).op s)

private theorem germToFunctionField_res_hom
    {X : Scheme.{u}} [IsIntegral X] {U V : X.Opens} (i : V ⟶ U)
    [Nonempty U] [Nonempty V] (s : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map i.op s) =
      X.germToFunctionField U s := by
  rw [← X.presheaf.germ_res_apply i (genericPoint X) (genericPoint_mem V) s]

private theorem sections_ext {Y : Scheme.{u}} [IsIntegral Y] (U : Y.Opens)
    (s t : Γ(Y, U))
    (h : ∀ [Nonempty U], Y.germToFunctionField U s = Y.germToFunctionField U t) :
    s = t := by
  by_cases hU : Nonempty U
  · let := hU
    exact Y.germToFunctionField_injective U (h)
  · have hbot : U = ⊥ := SetLike.ext' (Set.eq_empty_iff_forall_notMem.2 fun x hx =>
      hU ⟨⟨x, hx⟩⟩)
    have : Subsingleton Γ(Y, U) := by rw [hbot]; infer_instance
    exact Subsingleton.elim _ _

/-- The germ of `affineNormFamily` at an affine open is the norm of the germ of `s`. -/
private theorem germToFunctionField_affineNormFamily
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    {U : Y.Opens} [Nonempty U] (s : Γ(X, f ⁻¹ᵁ U))
    (V : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V}) :
    letI : Algebra Y.functionField X.functionField := φ.toAlgebra
    letI : Nonempty V.1 := V.2.2.2
    Y.germToFunctionField V.1 (affineNormFamily f φ hcompat s V) =
      Algebra.norm Y.functionField (X.germToFunctionField (f ⁻¹ᵁ U) s) := by
  let : Algebra Y.functionField X.functionField := φ.toAlgebra
  let : Nonempty V.1 := V.2.2.2
  dsimp [affineNormFamily]
  rw [normOnAffine_germ, germToFunctionField_res_hom (homOfLE (f.preimage_mono V.2.2.1)) s]

private theorem affineNormFamily_compatible
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) :
    TopCat.Presheaf.IsCompatible Y.ringCatSheaf.obj
      (fun i : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V} => i.1)
      (affineNormFamily f φ hcompat s) := by
  classical
  let V : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V} → Y.Opens := fun i => i.1
  let sf := affineNormFamily f φ hcompat s
  intro i j
  change Y.presheaf.map (TopologicalSpace.Opens.infLELeft (V i) (V j)).op (sf i) =
    Y.presheaf.map (TopologicalSpace.Opens.infLERight (V i) (V j)).op (sf j)
  let I : Y.Opens := V i ⊓ V j
  apply sections_ext I
  intro hI
  let : Algebra Y.functionField X.functionField := φ.toAlgebra
  let : Nonempty U := by
    rcases i.2.2.2 with ⟨y, hy⟩
    exact ⟨⟨y, i.2.2.1 hy⟩⟩
  have hcommon (k : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V})
      (p : I ⟶ V k) :
      Y.germToFunctionField I (Y.presheaf.map p.op (sf k)) =
        Algebra.norm Y.functionField (X.germToFunctionField (f ⁻¹ᵁ U) s) := by
    let : Nonempty (V k) := k.2.2.2
    rw [germToFunctionField_res_hom p (sf k)]
    exact germToFunctionField_affineNormFamily f φ hcompat s k
  rw [hcommon i (TopologicalSpace.Opens.infLELeft _ _),
    hcommon j (TopologicalSpace.Opens.infLERight _ _)]

private noncomputable def normOnOpenData
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) :
    {t : Γ(Y, U) // ∀ i : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V},
      (Y.ringCatSheaf.obj.map (homOfLE i.2.2.1).op).hom t =
        affineNormFamily f φ hcompat s i} := by
  classical
  let ι := {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V}
  let V : ι → Y.Opens := fun i => i.1
  let sf : ∀ i, Γ(Y, V i) := affineNormFamily f φ hcompat s
  have hc := affineNormFamily_compatible f φ hcompat U s
  let hg := TopCat.Sheaf.existsUnique_gluing' Y.ringCatSheaf
    V U (fun i => homOfLE i.2.2.1) (affineOpenCover U) sf hc
  exact ⟨hg.exists.choose, hg.exists.choose_spec⟩

private noncomputable def normOnOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) : Γ(Y, U) :=
  (normOnOpenData f φ hcompat U s).1

private theorem normOnOpen_restrict_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U))
    (V : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V}) :
    (Y.ringCatSheaf.obj.map (homOfLE V.2.2.1).op).hom
        (normOnOpen f φ hcompat U s) =
      affineNormFamily f φ hcompat s V :=
  (normOnOpenData f φ hcompat U s).2 V

private theorem normOnOpen_germ
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (s : Γ(X, f ⁻¹ᵁ U)) :
    letI : Algebra Y.functionField X.functionField := φ.toAlgebra
    Y.germToFunctionField U (normOnOpen f φ hcompat U s) =
      Algebra.norm Y.functionField (X.germToFunctionField (f ⁻¹ᵁ U) s) := by
  classical
  let : Algebra Y.functionField X.functionField := φ.toAlgebra
  let η := genericPoint Y
  obtain ⟨V, hV, hηV, hVU⟩ := exists_isAffineOpen_mem_and_subset (genericPoint_mem U)
  replace hVU : V ≤ U := hVU
  let : Nonempty V := ⟨⟨η, hηV⟩⟩
  let v : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V} :=
    ⟨V, hV, hVU, ‹Nonempty V›⟩
  have hloc' : Y.presheaf.map (homOfLE hVU).op (normOnOpen f φ hcompat U s) =
      affineNormFamily f φ hcompat s v :=
    normOnOpen_restrict_affine f φ hcompat U s v
  rw [← germToFunctionField_res_hom (homOfLE hVU), hloc']
  exact germToFunctionField_affineNormFamily f φ hcompat s v

private noncomputable def normOnOpenHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    (U : Y.Opens) : Γ(X, f ⁻¹ᵁ U) →* Γ(Y, U) where
  toFun := normOnOpen f φ hcompat U
  map_one' := by
    apply sections_ext U
    intro hU
    rw [normOnOpen_germ f φ hcompat U 1]
    simp

  map_mul' s t := by
    apply sections_ext U
    intro hU
    rw [normOnOpen_germ f φ hcompat U (s * t)]
    simp only [map_mul]
    rw [normOnOpen_germ f φ hcompat U s, normOnOpen_germ f φ hcompat U t]

private theorem normOnOpen_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    {U V : Y.Opens} (i : V ⟶ U) (s : Γ(X, f ⁻¹ᵁ U)) :
    normOnOpen f φ hcompat V
      (X.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op s) =
    Y.presheaf.map i.op (normOnOpen f φ hcompat U s) := by
  apply sections_ext V
  intro hV
  let : Nonempty U := by
    rcases hV with ⟨⟨y, hy⟩⟩
    exact ⟨⟨y, i.le hy⟩⟩
  let : Algebra Y.functionField X.functionField := φ.toAlgebra
  rw [normOnOpen_germ f φ hcompat V
      (X.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op s),
    germToFunctionField_res_hom i (normOnOpen f φ hcompat U s), normOnOpen_germ f φ hcompat U s,
    germToFunctionField_res_hom ((TopologicalSpace.Opens.map f.base).map i) s]

private theorem normOnOpenHom_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    (U : Y.Opens) (g : Γ(Y, U)) :
    letI : Algebra Y.functionField X.functionField := φ.toAlgebra
    normOnOpenHom f φ hcompat U (f.app U g) =
      g ^ Module.finrank Y.functionField X.functionField := by
  classical
  apply sections_ext U
  intro hU
  let : Algebra Y.functionField X.functionField := φ.toAlgebra
  change Y.germToFunctionField U
    (normOnOpen f φ hcompat U (f.app U g)) =
    Y.germToFunctionField U (g ^ Module.finrank Y.functionField X.functionField)
  rw [normOnOpen_germ f φ hcompat U (f.app U g), ← hcompat U g]
  change Algebra.norm Y.functionField
    (algebraMap Y.functionField X.functionField (Y.germToFunctionField U g)) = _
  rw [Algebra.norm_algebraMap]
  simp

private theorem functionField_finiteDimensional
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ) :
    letI : Algebra Y.functionField X.functionField := φ.toAlgebra
    Module.Finite Y.functionField X.functionField := by
  classical
  let : Algebra Y.functionField X.functionField := φ.toAlgebra
  let η := genericPoint Y
  let i := Y.affineCover.idx η
  let U := (Y.affineCover.f i).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (Y.affineCover.f i)
  let : Nonempty U := ⟨⟨η, Y.affineCover.covers η⟩⟩
  let : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let A := Γ(Y, U)
  let B := Γ(X, f ⁻¹ᵁ U)
  let : IsDomain A := IsIntegral.component_integral U
  let : IsDomain B := IsIntegral.component_integral (f ⁻¹ᵁ U)
  let : Algebra A B := (f.app U).hom.toAlgebra
  let : Module.Finite A B := f.finite_app U hU
  have hmap : Function.Injective (f.app U).hom := by
    intro a b hab
    apply Y.germToFunctionField_injective U
    apply φ.injective
    rw [hcompat U a, hcompat U b, hab]
  let : FaithfulSMul A B := faithfulSMul_iff_algebraMap_injective A B |>.2 hmap
  let K := Y.functionField
  let L := X.functionField
  let : Algebra A K := inferInstance
  let : Algebra B L := inferInstance
  let : Algebra K L := φ.toAlgebra
  let : Algebra A L := (φ.comp (Y.germToFunctionField U).hom).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  let : IsScalarTower A B L :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact hcompat U a)
  let : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen Y U hU
  let : IsFractionRing B L :=
    functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U) (hU.preimage f)
  let : Algebra.IsAlgebraic A B := inferInstance
  have hrank : Module.rank K L = Module.rank A B :=
    Algebra.IsAlgebraic.rank_of_isFractionRing A K B L
  exact Module.rank_lt_aleph0_iff.mp (hrank ▸ Module.rank_lt_aleph0 A B)

private theorem norm_eq_minpoly_coeff {A B K L : Type*}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    (s : B) (hs : IsIntegral A s) :
    Algebra.norm K (algebraMap B L s) =
      ((-1 : K) ^ (minpoly A s).natDegree *
        algebraMap A K ((minpoly A s).coeff 0)) ^ Module.finrank K⟮algebraMap B L s⟯ L := by
  have hL : IsIntegral A (algebraMap B L s) := IsIntegral.map (Algebra.ofId B L) hs
  have hx : IsIntegral K (algebraMap B L s) := IsIntegral.tower_top hL
  have hgen : Algebra.norm K (AdjoinSimple.gen K (algebraMap B L s)) =
      (-1 : K) ^ (minpoly K (algebraMap B L s)).natDegree *
        (minpoly K (algebraMap B L s)).coeff 0 := by
    rw [← adjoin.powerBasis_gen hx, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    simp [adjoin.powerBasis_gen, adjoin.powerBasis_dim, IntermediateField.minpoly_gen]
  rw [Algebra.norm_eq_norm_adjoin, hgen,
    minpoly.isIntegrallyClosed_eq_field_fractions K L hs]
  rw [← (minpoly.monic hs).natDegree_map (algebraMap A K)]
  simp only [Polynomial.coeff_map]

private theorem norm_zero_of_eval_zero {A B K L E F : Type*}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Field E] [Field F]
    (α : A →+* E) (β : B →+* F) (ψ : E →+* F)
    (hcompat : ψ.comp α = β.comp (algebraMap A B))
    (s : B) (hIntegral : IsIntegral A s) (t : A)
    (hfield : algebraMap A K t = Algebra.norm K (algebraMap B L s))
    (hs : β s = 0) : α t = 0 := by
  let c := (minpoly A s).coeff 0
  have hmap : (algebraMap F F).comp (ψ.comp α) = β.comp (algebraMap A B) := by
    ext a
    simpa using congrArg (fun g : A →+* F => g a) hcompat
  have hpoly := Polynomial.map_aeval_eq_aeval_map hmap (minpoly A s) s
  have hroot : Polynomial.aeval (β s)
      ((minpoly A s).map (ψ.comp α)) = 0 := by
    rw [← hpoly, minpoly.aeval, map_zero]
  have hcF : (ψ.comp α) c = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_at_zero, hs, c] using hroot
  have hc : α c = 0 := ψ.injective (by simpa using hcF)
  let n := Module.finrank K⟮algebraMap B L s⟯ L
  have hfield' : algebraMap A K t =
      algebraMap A K (((-1 : A) ^ (minpoly A s).natDegree * c) ^ n) := by
    rw [hfield, norm_eq_minpoly_coeff (A := A) (B := B) (K := K) (L := L) s hIntegral]
    simp [c, n, map_pow, map_mul]
  have ht : t = ((-1 : A) ^ (minpoly A s).natDegree * c) ^ n :=
    IsFractionRing.injective A K hfield'
  rw [ht]
  have hn : 0 < n := Module.finrank_pos
  simp [hc, c, hn.ne']

private theorem normOnAffine_eq_zero_at
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (φ : Y.functionField →+* X.functionField)
    (hcompat : FunctionFieldHomCompatible f φ)
    (U : Y.Opens) [Nonempty U] (hU : IsAffineOpen U) (s : Γ(X, f ⁻¹ᵁ U))
    (x : X) (hx : f x ∈ U)
    (hs : X.evaluation (f ⁻¹ᵁ U) x hx s = 0) :
    Y.evaluation U (f x) hx (normOnAffine f φ hcompat U hU s) = 0 := by
  classical
  let : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
  let : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let A := Γ(Y, U)
  let B := Γ(X, f ⁻¹ᵁ U)
  let K := Y.functionField
  let L := X.functionField
  let : IsDomain A := IsIntegral.component_integral U
  let : IsDomain B := IsIntegral.component_integral (f ⁻¹ᵁ U)
  let : Algebra A B := (f.app U).hom.toAlgebra
  let : Module.Finite A B := f.finite_app U hU
  let : IsIntegrallyClosed A := normal_affine U hU
  let : Algebra A K := inferInstance
  let : Algebra B L := inferInstance
  let : Algebra K L := φ.toAlgebra
  let : Algebra A L := (φ.comp (Y.germToFunctionField U).hom).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  let : IsScalarTower A B L :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact hcompat U a)
  let : IsFractionRing A K := functionField_isFractionRing_of_isAffineOpen Y U hU
  let : IsFractionRing B L :=
    functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U) (hU.preimage f)
  have hfinite := functionField_finiteDimensional f φ hcompat
  let : FiniteDimensional K L := hfinite
  have hfield : algebraMap A K (normOnAffine f φ hcompat U hU s) =
      Algebra.norm K (algebraMap B L s) := by
    simpa only [RingHom.algebraMap_toAlgebra] using normOnAffine_germ f φ hcompat U hU s
  exact norm_zero_of_eval_zero
    (Y.evaluation U (f x) hx).hom
    (X.evaluation (f ⁻¹ᵁ U) x hx).hom
    (f.residueFieldMap x).hom
    (by
      ext a
      exact AlgebraicGeometry.Scheme.evaluation_naturality_apply f x hx a)
    s (IsIntegral.of_finite A s) (normOnAffine f φ hcompat U hU s) hfield hs

private theorem evaluation_res_apply
    {Z : Scheme.{u}} {U V : Z.Opens} (hVU : V ≤ U)
    (x : Z) (hxV : x ∈ V) (s : Γ(Z, U)) :
    Z.evaluation V x hxV (Z.presheaf.map (homOfLE hVU).op s) =
      Z.evaluation U x (hVU hxV) s := by
  change (Z.presheaf.germ V x hxV ≫ Z.residue x)
      (Z.presheaf.map (homOfLE hVU).op s) =
    (Z.presheaf.germ U x (hVU hxV) ≫ Z.residue x) s
  exact congrArg (fun t => Z.residue x t)
    (Z.presheaf.germ_res_apply (homOfLE hVU) x hxV s)

/-- **Stacks Project, Tag 0BD3.** A finite surjective morphism of integral schemes with
normal target carries a norm of the function-field extension degree. -/
@[stacks 0BD3]
theorem exists_norm_of_finite_surjective_of_normal
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral X] [IsIntegral Y] [IsNormal Y] :
    ∃ φ : Y.functionField →+* X.functionField,
      (∀ (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
        (s : Γ(Y, U)),
        φ (Y.germToFunctionField U s) =
          X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s)) ∧
      (letI : Algebra Y.functionField X.functionField := φ.toAlgebra
       HasNormOfDegree f (Module.finrank Y.functionField X.functionField)) := by
  let ηX := genericPoint X
  have hη : f ηX = genericPoint Y := map_genericPoint_of_surjective f
  have hspec : f ηX ⤳ genericPoint Y := by rw [hη]
  let φ : Y.functionField →+* X.functionField :=
    (Y.presheaf.stalkSpecializes hspec ≫ f.stalkMap ηX).hom
  have hcompat : FunctionFieldHomCompatible f φ := by
    intro U hU hX s
    have hηU : genericPoint Y ∈ U := genericPoint_mem U
    change (((Y.presheaf.germ U (genericPoint Y) hηU) ≫
      Y.presheaf.stalkSpecializes hspec) ≫ f.stalkMap ηX) s = _
    rw [Y.presheaf.germ_stalkSpecializes hηU hspec]
    have hx : f ηX ∈ U := hη ▸ hηU
    change f.stalkMap ηX (Y.presheaf.germ U (f ηX) hx s) = _
    rw [f.germ_stalkMap_apply U ηX hx s]
  refine ⟨φ, hcompat, ?_⟩
  · let : Algebra Y.functionField X.functionField := φ.toAlgebra
    let N : MorphismNormMap f := {
      app := fun U => normOnOpenHom f φ hcompat U
      naturality := by intro U V i s; exact normOnOpen_naturality f φ hcompat i s
      app_eq_zero_at_image := by
        intro U s x hx hs
        classical
        obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
        let : Nonempty V := ⟨⟨f x, hyV⟩⟩
        let i : V ⟶ U := homOfLE hVU
        let iX := (TopologicalSpace.Opens.map f.base).map i
        have hpre := f.preimage_mono hVU
        have hiX : iX = homOfLE hpre := Subsingleton.elim _ _
        have hxV : x ∈ f ⁻¹ᵁ V := hyV
        let sV := X.presheaf.map iX.op s
        have hsV : X.evaluation (f ⁻¹ᵁ V) x hxV sV = 0 := by
          change X.evaluation (f ⁻¹ᵁ V) x hxV
            (X.presheaf.map iX.op s) = 0
          rwa [hiX, evaluation_res_apply hpre x hyV s]
        let v : {V : Y.Opens // IsAffineOpen V ∧ V ≤ U ∧ Nonempty V} :=
          ⟨V, hV, hVU, ‹Nonempty V›⟩
        have hlocal' : Y.evaluation V (f x) hyV (normOnOpenHom f φ hcompat V sV) = 0 := by
          let : Nonempty (f ⁻¹ᵁ V) := ⟨⟨x, hxV⟩⟩
          let : Algebra Y.functionField X.functionField := φ.toAlgebra
          have heq : normOnOpenHom f φ hcompat V sV =
              normOnAffine f φ hcompat V v.2.1 sV := by
            change normOnOpen f φ hcompat V sV = normOnAffine f φ hcompat V v.2.1 sV
            apply Y.germToFunctionField_injective V
            rw [normOnOpen_germ f φ hcompat V sV,
              normOnAffine_germ f φ hcompat V v.2.1 sV]
          rw [heq]
          exact normOnAffine_eq_zero_at f φ hcompat V v.2.1 sV x hyV hsV
        have hn : normOnOpenHom f φ hcompat V sV =
            Y.presheaf.map i.op (normOnOpenHom f φ hcompat U s) :=
          normOnOpen_naturality f φ hcompat i s
        calc
          Y.evaluation U (f x) hx (normOnOpenHom f φ hcompat U s) =
              Y.evaluation V (f x) hyV
                (Y.presheaf.map i.op (normOnOpenHom f φ hcompat U s)) :=
            (evaluation_res_apply hVU (f x) hyV _).symm
          _ = Y.evaluation V (f x) hyV (normOnOpenHom f φ hcompat V sV) := by rw [← hn]
          _ = 0 := hlocal'
    }
    exact ⟨{
      toMorphismNormMap := N
      app_pullback := fun U g => normOnOpenHom_pullback f φ hcompat U g
    }⟩

end Stacks.Divisors

end
