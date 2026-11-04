module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Jacobson.Ring
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import StacksCore.Tactic.StacksAttribute

/-!
# Divisibility by the degree of the ring of global sections

Let `k` be a field and let `X` be a proper scheme over `k` which is reduced and connected. Then
`κ = Γ(X, 𝒪_X)` is a finite field extension of `k`, and `w = [κ : k]` divides the degree of every
finite locally free sheaf on `X`, the degree of every residue field of `X`, and the degree of
every zero-dimensional closed subscheme of `X`.

## Main results

* `AlgebraicGeometry.isField_globalSections_of_isReduced_of_connectedSpace`: the global sections
  of a reduced connected proper scheme over a field form a field.
* `AlgebraicGeometry.finite_appTop_of_universallyClosed_of_isField`: a universally closed
  morphism of finite type to the spectrum of a field whose source is nonempty and whose global
  sections form a field has finite global sections.
* `AlgebraicGeometry.isField_and_finite_globalSections`: `κ/k` is a finite field extension.
* `AlgebraicGeometry.finrank_globalSections_dvd_finrank_cohomologyOverField`: when `Γ(X, ⊤)` is a
  field, `[Γ(X, ⊤) : k]` divides the dimension over `k` of every cohomology group.
* `AlgebraicGeometry.finrank_globalSections_dvd_curveDegree`: `w` divides the degree of every
  finite locally free sheaf of constant rank, when `X` has dimension at most one.
* `AlgebraicGeometry.finrank_globalSections_dvd_finrank_residueField`: `w` divides the degree of
  every residue field.
* `AlgebraicGeometry.finrank_globalSections_dvd_finrank_globalSections_of_dimension_zero`: a
  zero-dimensional closed subscheme `D` is finite locally free over `k` of rank
  `dim_k Γ(D, 𝒪_D)`, and `w` divides this rank.

## References

* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-! ### The ring of global sections as a finite field extension -/

/-- **The global sections of a reduced connected proper scheme over a field form a field.** -/
theorem isField_globalSections_of_isReduced_of_connectedSpace (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X] [ConnectedSpace X] :
    IsField Γ(X, ⊤) := by
  let alg : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hint : Algebra.IsIntegral k Γ(X, ⊤) := ⟨fun x => by
    rw [_root_.IsIntegral, RingHom.algebraMap_toAlgebra]
    exact Stacks.AlgebraicGeometry.ProperGeomConnected.isIntegral_toSpecΓ_algebraMap f x⟩
  have hred : _root_.IsReduced Γ(X, ⊤) := AlgebraicGeometry.IsReduced.component_reduced ⊤
  have hne : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have hidem : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he =>
    Stacks.AlgebraicGeometry.ProperGeomConnected.isIdempotentElem_eq_zero_or_one
      (U := (⊤ : X.Opens)) (by rw [TopologicalSpace.Opens.coe_top]; exact isPreconnected_univ) he
  have hsub : Subsingleton (PrimeSpectrum (Γ(X, ⊤) : Type u)) :=
    Stacks.RingTheory.IntegralOverField.subsingleton_primeSpectrum_of_isIntegral _
      (Stacks.AlgebraicGeometry.ProperGeomConnected.isIntegral_toSpecΓ_algebraMap f) hidem
  have hredSpec : IsReduced (Spec Γ(X, ⊤)) := (affine_isReduced_iff _).mpr hred
  have hirrSpec : IrreducibleSpace (Spec Γ(X, ⊤)) :=
    (⟨inferInstance⟩ : IrreducibleSpace (PrimeSpectrum (Γ(X, ⊤) : Type u)))
  have hdom : IsDomain Γ(X, ⊤) :=
    (affine_isIntegral_iff _).mp (isIntegral_of_irreducibleSpace_of_isReduced _)
  exact isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)

/-- **A universally closed morphism of finite type to the spectrum of a field whose source is
nonempty and whose ring of global sections is a field has finite global sections.** -/
theorem finite_appTop_of_universallyClosed_of_isField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [UniversallyClosed f] [LocallyOfFiniteType f] [Nonempty X]
    (hΓ : IsField Γ(X, ⊤)) : f.appTop.hom.Finite := by
  have x : X := Nonempty.some inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let fieldSpec : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  let fieldΓ : Field Γ(X, ⊤) := hΓ.toField
  have hUne : Nonempty U := ⟨⟨x, hxU⟩⟩
  apply RingHom.finite_of_algHom_finiteType_of_isJacobsonRing (A := Γ(X, U))
    (g := (X.presheaf.map (homOfLE le_top).op).hom)
  exact f.finiteType_appLE (isAffineOpen_top _) hU (by simp)

/-- For a proper scheme over a field which is reduced and connected, the ring of global sections
is a finite field extension of the base field. -/
@[stacks 0C6P "the global sections are a finite field extension"]
theorem isField_and_finite_globalSections (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X] [ConnectedSpace X] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    IsField Γ(X, ⊤) ∧ Module.Finite k Γ(X, ⊤) :=
  ⟨isField_globalSections_of_isReduced_of_connectedSpace k f,
    module_finite_globalSections f (finite_appTop_of_universallyClosed_of_isField k f
      (isField_globalSections_of_isReduced_of_connectedSpace k f))⟩

/-! ### The divisibilities -/

/-- For a field extension `φ = ψ : k →+* S` and an `S`-module `M`, the degree `[S : k]` (taken
along `φ`) divides the dimension over `k` of `M` with scalars restricted along `ψ`. -/
private theorem finrank_dvd_finrank_restrictScalars {k S : Type u} [Field k] [CommRing S]
    (φ ψ : k →+* S) (hφψ : φ = ψ) (hS : IsField S) (M : ModuleCat.{u} S) :
    letI : Algebra k S := φ.toAlgebra
    Module.finrank k S ∣ Module.finrank k ((ModuleCat.restrictScalars ψ).obj M) := by
  subst hφψ
  let algS : Algebra k S := φ.toAlgebra
  let fieldS : Field S := hS.toField
  have htower : IsScalarTower k S ((ModuleCat.restrictScalars φ).obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.finrank_dvd_finrank_right k S ((ModuleCat.restrictScalars φ).obj M)

/-- If `S` is a field extension of `k` and `T` is an `S`-algebra, then `[S : k] ∣ [T : k]`. -/
private theorem finrank_dvd_finrank_of_comp {k S T : Type u} [Field k] [CommRing S] [CommRing T]
    (φ : k →+* S) (ψ : S →+* T) (hS : IsField S) :
    letI : Algebra k S := φ.toAlgebra
    letI : Algebra k T := (ψ.comp φ).toAlgebra
    Module.finrank k S ∣ Module.finrank k T := by
  let algS : Algebra k S := φ.toAlgebra
  let algT : Algebra k T := (ψ.comp φ).toAlgebra
  let fieldS : Field S := hS.toField
  let algST : Algebra S T := ψ.toAlgebra
  have htower : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.finrank_dvd_finrank_right k S T

/-- **The dimension of cohomology is a multiple of the degree of the ring of global sections**:
when `Γ(X, ⊤)` is a field, `[Γ(X, ⊤) : k]` divides `dim_k Hⁿ(X, F)` for every `𝒪_X`-module `F`
and every `n`. -/
theorem finrank_globalSections_dvd_finrank_cohomologyOverField (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hΓ : IsField Γ(X, ⊤)) (F : X.Modules) (n : ℕ) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Module.finrank k Γ(X, ⊤) ∣ Module.finrank k (cohomologyOverField k f F n) :=
  have hhom : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
      = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom :=
    congrArg CommRingCat.Hom.hom (congrArg (fun t => (Scheme.ΓSpecIso (.of k)).inv ≫ t)
      (Stacks.AffineAlgebraEquivalence.appLE_top_top f (by simp)).symm)
  finrank_dvd_finrank_restrictScalars _ _ hhom hΓ _

/-- For a proper scheme over a field which is reduced and connected and of dimension at most one,
the degree of the extension `Γ(X, 𝒪_X)/k` divides the degree of every finite locally free sheaf
of constant rank on `X`. -/
@[stacks 0C6P "w divides the degree of a finite locally free sheaf"]
theorem finrank_globalSections_dvd_curveDegree (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    (Module.finrank k Γ(X, ⊤) : ℤ) ∣ curveDegree k f hdim E rank := by
  let alg : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have hΓ : IsField Γ(X, ⊤) := isField_globalSections_of_isReduced_of_connectedSpace k f
  have hsum : ∀ F : X.Modules, (Module.finrank k Γ(X, ⊤) : ℤ) ∣
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f F n) : ℤ) := fun F =>
    finsum_induction _ (dvd_zero _) (fun _ _ => dvd_add) fun n => (Int.natCast_dvd_natCast.mpr
      (finrank_globalSections_dvd_finrank_cohomologyOverField k f hΓ F n)).mul_left _
  exact dvd_sub (hsum E) (Dvd.dvd.mul_left (hsum _) _)

/-- For a proper scheme over a field which is reduced and connected, the degree of the extension
`Γ(X, 𝒪_X)/k` divides the degree over `k` of the residue field at every point. -/
@[stacks 0C6P "w divides the degree of a residue field"]
theorem finrank_globalSections_dvd_finrank_residueField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X] [ConnectedSpace X] (x : X) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Module.finrank k Γ(X, ⊤) ∣ Module.finrank k (X.residueField x) := by
  exact finrank_dvd_finrank_of_comp _ (X.Γevaluation x).hom
    (isField_globalSections_of_isReduced_of_connectedSpace k f)

/-- Let `X` be a proper scheme over a field which is reduced and connected and let `D ⊆ X` be a
closed subscheme of dimension zero. Then `D` is finite locally free over `k` of rank
`dim_k Γ(D, 𝒪_D)`, and the degree of the extension `Γ(X, 𝒪_X)/k` divides it. -/
@[stacks 0C6P "w divides the degree of a zero-dimensional closed subscheme"]
theorem finrank_globalSections_dvd_finrank_globalSections_of_dimension_zero (k : Type u)
    [Field k] {X D : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X]
    [ConnectedSpace X] (i : D ⟶ X) [IsClosedImmersion i] (hdimD : topologicalKrullDim D = 0) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra k Γ(D, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop).hom.toAlgebra
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (i ≫ f) (Module.finrank k Γ(D, ⊤)) ∧
      Module.finrank k Γ(X, ⊤) ∣ Module.finrank k Γ(D, ⊤) := by
  let algΓ : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let algD : Algebra k Γ(D, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop).hom.toAlgebra
  have hfin : IsFinite (i ≫ f) := isFinite_of_finiteType_of_dimension_zero k (i ≫ f) hdimD
  refine ⟨(Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq (i ≫ f)
    (Module.finrank k Γ(D, ⊤))).mpr ⟨inferInstance, ?_, rfl⟩, ?_⟩
  · rw [← RingHom.finite_algebraMap]
    exact (Scheme.Hom.finite_appTop (i ≫ f)).comp (RingHom.Finite.of_surjective
      ((Scheme.ΓSpecIso (.of k)).inv.hom)
      fun y => ⟨(Scheme.ΓSpecIso (.of k)).hom.hom y, by simp⟩)
  · exact finrank_dvd_finrank_of_comp _ i.appTop.hom
      (isField_globalSections_of_isReduced_of_connectedSpace k f)

end AlgebraicGeometry

end
