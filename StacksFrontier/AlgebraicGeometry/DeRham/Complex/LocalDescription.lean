module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.AlgebraicGeometry.Duality.FunnyMap
public import StacksFrontier.RingTheory.CompleteIntersection.RelativeConormal
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# A local description of the canonical maps on differential forms

Let `B` be an `A`-algebra presented as a quotient `A[x₁, …, xₙ]/(f₁, …, fₙ)` of a polynomial
algebra by as many equations as there are variables, and suppose the presentation is a relative
global complete intersection. Its conormal module is then free on the classes of the equations,
so the two-term complex `NL_{B/A}` has free terms of the same rank `n` and the construction of
Tag 0FL8 applies. It produces canonical `B`-module maps
`Ω^p_{B/ℤ} → Ω^p_{A/ℤ} ⊗_A det(NL_{B/A})` for every `p`.

## Main definitions

* `Stacks.DeRham.CotangentDiagram` packages the diagram of Tag 0FL9: the split short exact
  sequence of absolute differentials base changed to `B`, the two-term conormal complex mapping
  into it, and the identification of the cokernel of the conormal map with `Ω_{B⁄ℤ}`.
* `Stacks.DeRham.cotangentDiagram` is the canonical such diagram attached to the presentation.
* `Stacks.DeRham.cotangentDeterminantElement` is the determinant element of the relative naive
  cotangent complex of the presentation.
* `Stacks.DeRham.presentationFunnyMap` is the resulting canonical family of maps on absolute
  differential forms.

## Main results

* `Stacks.DeRham.presentationFunnyMap_zero` evaluates the degree-zero map.
* `Stacks.DeRham.presentationFunnyMap_wedge` is multiplicativity against base-changed forms
  on `A`.
* `Stacks.DeRham.presentationFunnyMap_comp` says that composing with pullback from `A` is
  multiplication by the determinant element.

## Implementation notes

The determinant of the naive cotangent complex is represented by the determinant line of the
presentation's two-term conormal complex. Base-changed absolute forms on `A` are written as
exterior powers of `B ⊗[A] Ω[A⁄ℤ]`, which is the canonical form of the tensor product occurring
in the source.

The source states the construction for a *quasi-finite* `A`-algebra `B`; quasi-finiteness enters
only to make a presentation with equally many variables and relations a relative global complete
intersection, which is the hypothesis imposed here.

## References

* [Stacks Project, Tag 0FL9](https://stacks.math.columbia.edu/tag/0FL9)
-/

@[expose] public section

namespace Stacks.DeRham

open scoped TensorProduct

add_to_stacks 0FL9 "conormal basis" Algebra.Presentation.exists_basis_cotangent_relation

/-!
### Transporting the canonical maps along an identification of the cokernel

The maps of Tag 0FL8 are attached to the cokernel `L ⧸ range d` of the two-term complex. This
section transports the maps and their three properties across an identification `e` of that
cokernel with a module `H`, pinned by what it does to the image of `K`.
-/

section Transport

variable {R : Type*} [CommRing R] {K L Mzero Mneg H : Type*}
  [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
  [AddCommGroup Mzero] [Module R Mzero] [AddCommGroup Mneg] [Module R Mneg]
  [AddCommGroup H] [Module R H]
  (n : ℕ) (i : K →ₗ[R] L) (π : L →ₗ[R] Mzero) (d : Mneg →ₗ[R] L) (dM : Mneg →ₗ[R] Mzero)
  (hi : Function.Injective i) (hexact : Function.Exact i π) (hπ : Function.Surjective π)
  (hsquare : π.comp d = dM) (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
  (hneg : Nonempty (Module.Basis (Fin n) R Mneg))
  (e : (L ⧸ LinearMap.range d) ≃ₗ[R] H) (ι : K →ₗ[R] H)

/-- The canonical maps of Tag 0FL8, read through an identification `e` of the cokernel of the
two-term complex with `H`. -/
noncomputable def funnyMapOfEquiv (p : ℕ) :
    (⋀[R]^p H) →ₗ[R] (⋀[R]^p K) ⊗[R] twoTermDeterminant R n Mneg Mzero :=
  funnyMap n i π d dM hi hexact hπ hsquare hzero hneg p ∘ₗ
    exteriorPower.map p e.symm.toLinearMap

/-- The transported map applied to `η` is the canonical map of Tag 0FL8 applied to the image of
`η` under the inverse identification. -/
theorem funnyMapOfEquiv_apply (p : ℕ) (η : ⋀[R]^p H) :
    funnyMapOfEquiv n i π d dM hi hexact hπ hsquare hzero hneg e p η =
      funnyMap n i π d dM hi hexact hπ hsquare hzero hneg p
        (exteriorPower.map p e.symm.toLinearMap η) := rfl

/-- The identification carries the image of `K` in `H` to the image of `K` in the cokernel, on
every exterior power. -/
theorem exteriorPower_map_symm_comp
    (he : e.symm.toLinearMap.comp ι = (LinearMap.range d).mkQ.comp i) (p : ℕ) (ω : ⋀[R]^p K) :
    exteriorPower.map p e.symm.toLinearMap (exteriorPower.map p ι ω) =
      exteriorPower.map p ((LinearMap.range d).mkQ.comp i) ω := by
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, he]

/-- In degree zero the transported map takes the unit to the determinant element. -/
theorem funnyMapOfEquiv_zero :
    funnyMapOfEquiv n i π d dM hi hexact hπ hsquare hzero hneg e 0
        (exteriorPower.ιMulti R 0 (fun j ↦ Fin.elim0 j)) =
      (exteriorPower.ιMulti R 0 (fun j ↦ Fin.elim0 j)) ⊗ₜ[R]
        twoTermDeterminantElement R dM hneg := by
  have hunit : (e.symm.toLinearMap ∘ fun j : Fin 0 ↦ Fin.elim0 j) =
      (fun j : Fin 0 ↦ Fin.elim0 j) := funext fun j ↦ Fin.elim0 j
  rw [funnyMapOfEquiv_apply, exteriorPower.map_apply_ιMulti, hunit]
  exact funnyMap_zero n i π d dM hi hexact hπ hsquare hzero hneg

/-- The transported maps commute with wedging on the left by an exterior power of `K`. -/
theorem funnyMapOfEquiv_wedge
    (he : e.symm.toLinearMap.comp ι = (LinearMap.range d).mkQ.comp i)
    (q p : ℕ) (ω : ⋀[R]^q K) (η : ⋀[R]^p H) :
    funnyMapOfEquiv n i π d dM hi hexact hπ hsquare hzero hneg e (q + p)
        (exteriorPower.wedgeMul (R := R) q p (exteriorPower.map q ι ω) η) =
      (exteriorPower.wedgeMul (R := R) q p ω).rTensor (twoTermDeterminant R n Mneg Mzero)
        (funnyMapOfEquiv n i π d dM hi hexact hπ hsquare hzero hneg e p η) := by
  rw [funnyMapOfEquiv_apply, funnyMapOfEquiv_apply, exteriorPower.wedgeMul_map,
    exteriorPower_map_symm_comp (i := i) (d := d) (e := e) (ι := ι) he q ω]
  exact funnyMap_wedge n q p i π d dM hi hexact hπ hsquare hzero hneg ω
    (exteriorPower.map p e.symm.toLinearMap η)

/-- Composing the transported map with the map `⋀ᵖK → ⋀ᵖH` is multiplication by the determinant
element. -/
theorem funnyMapOfEquiv_comp
    (he : e.symm.toLinearMap.comp ι = (LinearMap.range d).mkQ.comp i)
    (p : ℕ) (ω : ⋀[R]^p K) :
    funnyMapOfEquiv n i π d dM hi hexact hπ hsquare hzero hneg e p
        (exteriorPower.map p ι ω) =
      ω ⊗ₜ[R] twoTermDeterminantElement R dM hneg := by
  rw [funnyMapOfEquiv_apply,
    exteriorPower_map_symm_comp (i := i) (d := d) (e := e) (ι := ι) he p ω]
  exact funnyMap_comp n p i π d dM hi hexact hπ hsquare hzero hneg ω

end Transport

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {n : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin n))

/-- The determinant element of the relative naive cotangent complex of a square presentation,
computed from the basis of the conormal module given by the classes of the relations. -/
noncomputable def cotangentDeterminantElement
    [P.IsRelativeGlobalCompleteIntersection] :
    twoTermDeterminant B n P.toExtension.Cotangent P.toExtension.CotangentSpace :=
  twoTermDeterminantElement B P.toExtension.cotangentComplex
    ⟨(Algebra.Presentation.exists_basis_cotangent_relation P).choose⟩

/-- The diagram of Tag 0FL9 attached to a square presentation of `B` over `A`: a short exact
sequence `0 → B ⊗[A] Ω[A⁄ℤ] → B ⊗[P] Ω[P⁄ℤ] → Ω[P⁄A] ⊗[P] B → 0` of `B`-modules whose outer
terms are free of rank `n`, a two-term complex out of the conormal module into it, and an
identification of the cokernel of that complex with `Ω[B⁄ℤ]` under which the base-change map
from `Ω[A⁄ℤ]` becomes the quotient map. -/
structure CotangentDiagram where
  /-- The base-change map from the absolute differentials of `A`. -/
  i : (B ⊗[A] Ω[A⁄ℤ]) →ₗ[B] B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ]
  /-- The map to the relative differentials of the presentation. -/
  π : (B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ]) →ₗ[B] P.toExtension.CotangentSpace
  /-- The conormal map into the absolute differentials of the polynomial algebra. -/
  d : P.toExtension.Cotangent →ₗ[B] B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ]
  /-- The identification of the cokernel of `d` with the absolute differentials of `B`. -/
  quotientEquiv :
    (B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ] ⧸ LinearMap.range d) ≃ₗ[B] Ω[B⁄ℤ]
  /-- The base-change map is injective. -/
  hi : Function.Injective i
  /-- The row is exact in the middle. -/
  hexact : Function.Exact i π
  /-- The row is surjective on the right. -/
  hπ : Function.Surjective π
  /-- The square commutes: the conormal map into the relative differentials is the cotangent
  complex of the presentation. -/
  hsquare : π.comp d = P.toExtension.cotangentComplex
  /-- The right-hand term of the row is free of rank `n`. -/
  hzero : Nonempty (Module.Basis (Fin n) B P.toExtension.CotangentSpace)
  /-- The conormal module is free of rank `n`. -/
  hneg : Nonempty (Module.Basis (Fin n) B P.toExtension.Cotangent)
  /-- Under the identification of the cokernel, the base-change map from `Ω[A⁄ℤ]` to `Ω[B⁄ℤ]`
  is the composite of `i` with the quotient map. -/
  pullback : quotientEquiv.symm.toLinearMap.comp (KaehlerDifferential.mapBaseChange ℤ A B) =
    (LinearMap.range d).mkQ.comp i

/-- The canonical diagram of Tag 0FL9 attached to a square presentation which is a relative
global complete intersection. -/
noncomputable def cotangentDiagram [P.IsRelativeGlobalCompleteIntersection] :
    CotangentDiagram P := by
  classical
  let hsurj := P.toExtension.algebraMap_surjective
  letI : Module B (P.toExtension.ker.Cotangent) := ConormalSeq.cotangentModule hsurj
  letI : IsScalarTower P.toExtension.Ring B P.toExtension.ker.Cotangent :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      let e := RingHom.quotientKerEquivOfSurjective hsurj
      have he : e.symm (algebraMap P.toExtension.Ring B r) = Ideal.Quotient.mk _ r :=
        RingHom.quotientKerEquivOfSurjective_symm_apply hsurj r
      change e.symm (algebraMap P.toExtension.Ring B r) • x = r • x
      rw [he]
      rfl
  let c : B ⊗[P.toExtension.Ring]
      (P.toExtension.Ring ⊗[A] Ω[A⁄ℤ]) ≃ₗ[B] B ⊗[A] Ω[A⁄ℤ] :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A P.toExtension.Ring B B Ω[A⁄ℤ]
  let e : P.Ring ≃ₐ[A] P.toExtension.Ring :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  letI : Algebra.FormallySmooth A P.toExtension.Ring := by
    let _ : Algebra.FormallySmooth A P.Ring := inferInstance
    exact Algebra.FormallySmooth.of_equiv e
  let i₀ := KaehlerDifferential.mapBaseChange ℤ A P.toExtension.Ring
  let π₀ := KaehlerDifferential.map ℤ A P.toExtension.Ring P.toExtension.Ring
  let i : (B ⊗[A] Ω[A⁄ℤ]) →ₗ[B] B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ] :=
    i₀.baseChange B ∘ₗ c.symm.toLinearMap
  let π : (B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ]) →ₗ[B]
      P.toExtension.CotangentSpace :=
    π₀.baseChange B
  let cotEquiv : P.toExtension.Cotangent →ₗ[B] P.toExtension.ker.Cotangent :=
    P.toExtension.cotangentEquivCotangentKer.toLinearMap.extendScalarsOfSurjective hsurj
  let d : P.toExtension.Cotangent →ₗ[B]
      B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ] :=
    (ConormalSeq.conormalMap ℤ hsurj).comp cotEquiv
  have hrow₀ : Function.Exact i₀ π₀ :=
    KaehlerDifferential.exact_mapBaseChange_map ℤ A P.toExtension.Ring
  have hπ₀ : Function.Surjective π₀ :=
    KaehlerDifferential.map_surjective_of_surjective ℤ A _ _ Function.surjective_id
  have hrowBC : Function.Exact (i₀.baseChange B) (π₀.baseChange B) :=
    lTensor_exact B hrow₀ hπ₀
  have hi : Function.Injective i := by
    obtain ⟨r, hr⟩ := KaehlerDifferential.exists_retraction_mapBaseChange ℤ A P.toExtension.Ring
    let l : (B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ]) →ₗ[B] B ⊗[A] Ω[A⁄ℤ] :=
      c.toLinearMap ∘ₗ r.baseChange B
    have hl : l.comp i = LinearMap.id := by
      change c.toLinearMap ∘ₗ (r.baseChange B ∘ₗ i₀.baseChange B) ∘ₗ
        c.symm.toLinearMap = LinearMap.id
      rw [← LinearMap.baseChange_comp, hr]
      simp
    exact Function.LeftInverse.injective (g := l) fun x ↦ by simpa using LinearMap.congr_fun hl x
  have hexact : Function.Exact i π :=
    LinearMap.exact_iff.mpr (hrowBC.linearMap_ker_eq.trans
      (LinearMap.range_comp_of_range_eq_top (f := c.symm.toLinearMap) _ c.symm.range).symm)
  have hπ : Function.Surjective π := LinearMap.baseChange_surjective B hπ₀
  have hsquare : π.comp d = P.toExtension.cotangentComplex := by
    ext x
    obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := P.toExtension) x
    simp [d, cotEquiv, π, π₀, ConormalSeq.conormalMap_toCotangent,
      Algebra.Extension.cotangentComplex_mk, KaehlerDifferential.map_D]
  have hzero : Nonempty (Module.Basis (Fin n) B P.toExtension.CotangentSpace) :=
    ⟨Algebra.Generators.cotangentSpaceBasis P.toGenerators⟩
  have hneg : Nonempty (Module.Basis (Fin n) B P.toExtension.Cotangent) :=
    ⟨(Algebra.Presentation.exists_basis_cotangent_relation P).choose⟩
  let q : (B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ]) →ₗ[B] Ω[B⁄ℤ] :=
    KaehlerDifferential.mapBaseChange ℤ P.toExtension.Ring B
  have hker : LinearMap.ker q = LinearMap.range d := by
    rw [LinearMap.range_comp_of_range_eq_top (f := cotEquiv) _
      (LinearMap.range_eq_top.mpr P.toExtension.cotangentEquivCotangentKer.surjective)]
    exact (ConormalSeq.conormalMap_range_eq_ker_mapBaseChange ℤ P.toExtension.Ring B
      hsurj).symm
  let quotientEquiv :
      (B ⊗[P.toExtension.Ring] Ω[P.toExtension.Ring⁄ℤ] ⧸ LinearMap.range d) ≃ₗ[B] Ω[B⁄ℤ] :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (LinearMap.quotKerEquivOfSurjective q
        (KaehlerDifferential.mapBaseChange_surjective ℤ P.toExtension.Ring B
          P.toExtension.algebraMap_surjective))
  have hmap : KaehlerDifferential.mapBaseChange ℤ A B = q.comp i := by
    ext a
    simp [q, i, c, i₀, KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply]
  have hpullback : quotientEquiv.symm.toLinearMap.comp
      (KaehlerDifferential.mapBaseChange ℤ A B) = (LinearMap.range d).mkQ.comp i :=
    LinearMap.ext fun x ↦ quotientEquiv.injective <| by
      simpa [quotientEquiv, LinearMap.quotKerEquivOfSurjective_apply_mk] using
        LinearMap.congr_fun hmap x
  exact ⟨i, π, d, quotientEquiv, hi, hexact, hπ, hsquare, hzero, hneg, hpullback⟩

namespace CotangentDiagram

variable {P} (D : CotangentDiagram P)

/-- The canonical family of maps on absolute differential forms attached to a diagram as in
Tag 0FL9: read the canonical maps of Tag 0FL8 through the identification of the cokernel of the
conormal map with `Ω[B⁄ℤ]`. -/
noncomputable def formsMap (p : ℕ) :
    (⋀[B]^p Ω[B⁄ℤ]) →ₗ[B]
      (⋀[B]^p (B ⊗[A] Ω[A⁄ℤ])) ⊗[B]
        twoTermDeterminant B n P.toExtension.Cotangent P.toExtension.CotangentSpace :=
  funnyMapOfEquiv n D.i D.π D.d P.toExtension.cotangentComplex D.hi D.hexact D.hπ D.hsquare
    D.hzero D.hneg D.quotientEquiv p

/-- In degree zero the canonical map takes the unit to the determinant element of the
two-term conormal complex. -/
theorem formsMap_zero :
    D.formsMap 0 (exteriorPower.ιMulti B 0 (fun j ↦ Fin.elim0 j)) =
      (exteriorPower.ιMulti B 0 (fun j ↦ Fin.elim0 j)) ⊗ₜ[B]
        twoTermDeterminantElement B P.toExtension.cotangentComplex D.hneg :=
  funnyMapOfEquiv_zero n D.i D.π D.d P.toExtension.cotangentComplex D.hi D.hexact D.hπ
    D.hsquare D.hzero D.hneg D.quotientEquiv

/-- The canonical maps commute with wedging by a base-changed absolute differential form
on `A`. -/
theorem formsMap_wedge (q p : ℕ) (ω : ⋀[B]^q (B ⊗[A] Ω[A⁄ℤ])) (η : ⋀[B]^p Ω[B⁄ℤ]) :
    D.formsMap (q + p)
        (exteriorPower.wedgeMul (R := B) q p
          (exteriorPower.map q (KaehlerDifferential.mapBaseChange ℤ A B) ω) η) =
      (exteriorPower.wedgeMul (R := B) q p ω).rTensor
        (twoTermDeterminant B n P.toExtension.Cotangent P.toExtension.CotangentSpace)
        (D.formsMap p η) :=
  funnyMapOfEquiv_wedge n D.i D.π D.d P.toExtension.cotangentComplex D.hi D.hexact D.hπ
    D.hsquare D.hzero D.hneg D.quotientEquiv (KaehlerDifferential.mapBaseChange ℤ A B)
    D.pullback q p ω η

/-- Composing the canonical map on forms with pullback from `A` is multiplication by the
determinant element of the two-term conormal complex. -/
theorem formsMap_comp (p : ℕ) (ω : ⋀[B]^p (B ⊗[A] Ω[A⁄ℤ])) :
    D.formsMap p (exteriorPower.map p (KaehlerDifferential.mapBaseChange ℤ A B) ω) =
      ω ⊗ₜ[B] twoTermDeterminantElement B P.toExtension.cotangentComplex D.hneg :=
  funnyMapOfEquiv_comp n D.i D.π D.d P.toExtension.cotangentComplex D.hi D.hexact D.hπ
    D.hsquare D.hzero D.hneg D.quotientEquiv (KaehlerDifferential.mapBaseChange ℤ A B)
    D.pullback p ω

end CotangentDiagram

variable [P.IsRelativeGlobalCompleteIntersection]

/-- The canonical maps on absolute differential forms associated to a square presentation of `B`
over `A` which is a relative global complete intersection:
`Ω^p_{B⁄ℤ} → Ω^p_{A⁄ℤ} ⊗ det(NL_{B/A})`. -/
@[stacks 0FL9 "canonical maps"]
noncomputable def presentationFunnyMap (p : ℕ) :
    (⋀[B]^p Ω[B⁄ℤ]) →ₗ[B]
      (⋀[B]^p (B ⊗[A] Ω[A⁄ℤ])) ⊗[B]
        twoTermDeterminant B n P.toExtension.Cotangent P.toExtension.CotangentSpace :=
  (cotangentDiagram P).formsMap p

/-- In degree zero the canonical map takes the unit to the determinant element of the relative
naive cotangent complex. -/
@[stacks 0FL9 "degree zero"]
theorem presentationFunnyMap_zero :
    presentationFunnyMap P 0 (exteriorPower.ιMulti B 0 (fun j ↦ Fin.elim0 j)) =
      (exteriorPower.ιMulti B 0 (fun j ↦ Fin.elim0 j)) ⊗ₜ[B]
        cotangentDeterminantElement P :=
  (cotangentDiagram P).formsMap_zero

/-- The canonical maps commute with wedging by a base-changed absolute differential form
on `A`. -/
@[stacks 0FL9 "wedge compatibility"]
theorem presentationFunnyMap_wedge (q p : ℕ) (ω : ⋀[B]^q (B ⊗[A] Ω[A⁄ℤ]))
    (η : ⋀[B]^p Ω[B⁄ℤ]) :
    presentationFunnyMap P (q + p)
        (exteriorPower.wedgeMul (R := B) q p
          (exteriorPower.map q (KaehlerDifferential.mapBaseChange ℤ A B) ω) η) =
      (exteriorPower.wedgeMul (R := B) q p ω).rTensor
        (twoTermDeterminant B n P.toExtension.Cotangent P.toExtension.CotangentSpace)
        (presentationFunnyMap P p η) :=
  (cotangentDiagram P).formsMap_wedge q p ω η

/-- Composing the canonical map on forms with pullback from `A` is multiplication by the
determinant element of the relative naive cotangent complex. -/
@[stacks 0FL9 "composition with pullback"]
theorem presentationFunnyMap_comp (p : ℕ) (ω : ⋀[B]^p (B ⊗[A] Ω[A⁄ℤ])) :
    presentationFunnyMap P p
        (exteriorPower.map p (KaehlerDifferential.mapBaseChange ℤ A B) ω) =
      ω ⊗ₜ[B] cotangentDeterminantElement P :=
  (cotangentDiagram P).formsMap_comp p ω

end Stacks.DeRham
