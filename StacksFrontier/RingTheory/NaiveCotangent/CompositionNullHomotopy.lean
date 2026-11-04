module

public import StacksFrontier.RingTheory.NaiveCotangent.Defs

/-!
# The composition of the two functoriality maps of `NL` is null-homotopic

Let `A → B` be a ring map and let `φ : B → C` be a second ring map.  The naive cotangent
complex is functorial for commutative squares of ring maps, so the square
```
B ──φ──▸ C
▲         ▲
│         │
A ──────▸ B
```
gives a chain map `NL_{B/A} ⟶ NL_{C/B}`, and it is the composition of the two maps
`NL_{B/A} ⟶ NL_{C/A} ⟶ NL_{C/B}`.  This file proves that this composition is homotopic to
the zero chain map, and exhibits the homotopy of the source: writing `J` for the kernel of
the canonical presentation `B[C] → C`, it is the map
`Ω_{A[B]/A} ⊗_{A[B]} B → J/J²` sending the basis element `d[b]` to the class of
`[φ(b)] - b`.

The proof is the one the source gives: the composition is the map of naive cotangent
complexes attached to the morphism of canonical presentations `A[B] → B[C]`, `[b] ↦ [φ(b)]`,
and the *second* morphism of presentations `A[B] → B[C]`, `[b] ↦ b`, which sends a variable
to a coefficient, induces the zero chain map, because it factors through the evaluation
`A[B] → B` and therefore kills both the presentation ideal and all differentials.  Two
morphisms of presentations induce homotopic chain maps (Stacks 00S1 (2),
`NaiveCotangent.nlMapBase_homotopic`), and the homotopy that lemma produces is the
difference of the two morphisms, which is exactly `d[b] ↦ [φ(b)] - b`.

## Main definitions

* `NaiveCotangent.ChainMap.zero`: the zero chain map of two-term complexes.
* `NaiveCotangent.towerMidHom`, `NaiveCotangent.towerTopHom`: the morphisms of canonical
  presentations `A[B] → A[C]` and `A[C] → B[C]` inducing `NL_{B/A} ⟶ NL_{C/A}` and
  `NL_{C/A} ⟶ NL_{C/B}`.
* `NaiveCotangent.towerConstHom`: the morphism of canonical presentations `A[B] → B[C]`
  sending the variable `[b]` to the coefficient `b`.
* `NaiveCotangent.towerChainMap`: the composition `NL_{B/A} ⟶ NL_{C/A} ⟶ NL_{C/B}`.
* `NaiveCotangent.towerNullHomotopy`: the homotopy `Ω_{A[B]/A} ⊗_{A[B]} B → J/J²`.

## Main results

* `NaiveCotangent.towerChainMap_homotopic_zero`: **Stacks 07VC**, the composition
  `NL_{B/A} ⟶ NL_{C/A} ⟶ NL_{C/B}` is homotopic to zero.
* `NaiveCotangent.towerNullHomotopy_one_tmul_D_X`: **Stacks 07VC**, the homotopy sends the
  basis element `d[b]` to the class of `[φ(b)] - b` in `J/J²`.
* `NaiveCotangent.nlMapBase_towerConstHom_eq_zero`: the morphism of presentations sending a
  variable to a coefficient induces the zero chain map.

## References

* [Stacks Project, Tag 07VC](https://stacks.math.columbia.edu/tag/07VC), Remark 10.134.5.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1), Lemma 10.134.2, whose
  part (2) supplies the homotopy.
-/

@[expose] public section

universe u₁ u₂ u₃

open Algebra MvPolynomial

namespace NaiveCotangent

-- `Algebra.Generators.toExtension` is a plain definition, so the elaborator will not identify
-- `P.toExtension.Ring` with `P.Ring` at `implicit` transparency; the two spellings occur side
-- by side in Mathlib's cotangent API.
attribute [local implicit_reducible] Algebra.Generators.toExtension

variable {S : Type*} [CommRing S]

/-- The zero chain map between two two-term complexes of `S`-modules. -/
public def ChainMap.zero (X Y : TwoTerm S) : ChainMap X Y where
  f₁ := 0
  f₀ := 0
  comm := by ext x; simp

/-- The degree-one component of the zero chain map is zero. -/
@[simp] public theorem ChainMap.zero_f₁ (X Y : TwoTerm S) : (ChainMap.zero X Y).f₁ = 0 := rfl

/-- The degree-zero component of the zero chain map is zero. -/
@[simp] public theorem ChainMap.zero_f₀ (X Y : TwoTerm S) : (ChainMap.zero X Y).f₀ = 0 := rfl

section Tower

variable (A : Type u₁) (B : Type u₂) (C : Type u₃) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The morphism of canonical presentations `A[B] ⟶ A[C]` sending the variable `[b]` to the
variable `[φ(b)]`.  It induces the functoriality map `NL_{B/A} ⟶ NL_{C/A}`. -/
@[simps] public noncomputable def towerMidHom :
    (Generators.self A B).Hom (Generators.self A C) where
  val b := X (algebraMap B C b)
  aeval_val b := by simp

/-- The morphism of canonical presentations `A[C] ⟶ B[C]` sending the variable `[c]` to the
variable `[c]`.  It induces the functoriality map `NL_{C/A} ⟶ NL_{C/B}`. -/
@[simps] public noncomputable def towerTopHom :
    (Generators.self A C).Hom (Generators.self B C) where
  val c := X c
  aeval_val c := by simp

/-- The morphism of canonical presentations `A[B] ⟶ B[C]` sending the variable `[b]` to the
*coefficient* `b`.  It is the composition of the evaluation `A[B] → B` with the inclusion of
coefficients `B → B[C]`, so it induces the zero chain map on naive cotangent complexes. -/
@[simps] public noncomputable def towerConstHom :
    (Generators.self A B).Hom (Generators.self B C) where
  val b := MvPolynomial.C b
  aeval_val b := by simp

omit [Algebra A C] [IsScalarTower A B C] in
/-- The algebra map `A[B] ⟶ B[C]` underlying `towerConstHom` is the evaluation `A[B] → B`
followed by the inclusion of coefficients `B → B[C]`. -/
public theorem towerConstHom_toAlgHom_eq :
    (towerConstHom A B C).toAlgHom =
      (IsScalarTower.toAlgHom A B (MvPolynomial C B)).comp
        (aeval (R := A) (_root_.id : B → B)) := by
  apply MvPolynomial.algHom_ext
  intro b
  simp [towerConstHom, Generators.Hom.toAlgHom, MvPolynomial.algebraMap_eq]

omit [Algebra A C] [IsScalarTower A B C] in
/-- `towerConstHom` carries the presentation ideal of `A[B] → B` to zero. -/
public theorem towerConstHom_toAlgHom_eq_zero_of_mem_ker
    (x : (Generators.self A B).Ring)
    (hx : x ∈ (Generators.self A B).toExtension.ker) :
    (towerConstHom A B C).toAlgHom x = 0 := by
  rw [towerConstHom_toAlgHom_eq]
  have hx' : aeval (R := A) (_root_.id : B → B) x = 0 := hx
  simp [hx']

omit [Algebra A C] [IsScalarTower A B C] in
/-- The differential of the image under `towerConstHom` of any element vanishes, since that
image is a coefficient. -/
public theorem towerConstHom_D_toAlgHom_eq_zero (x : (Generators.self A B).Ring) :
    KaehlerDifferential.D B (MvPolynomial C B) ((towerConstHom A B C).toAlgHom x) = 0 := by
  rw [towerConstHom_toAlgHom_eq]
  simpa using
    (KaehlerDifferential.D B (MvPolynomial C B)).map_algebraMap
      (aeval (R := A) (_root_.id : B → B) x)

/-- `Algebra.Generators.cotangentSpaceBasis_apply` for the canonical presentation, stated over
the `toExtension.Ring` spelling of the polynomial ring. -/
private theorem cotangentSpaceBasis_self_apply (b : B) :
    (Generators.self A B).cotangentSpaceBasis b =
      (1 : B) ⊗ₜ[(Generators.self A B).toExtension.Ring]
        KaehlerDifferential.D A (Generators.self A B).toExtension.Ring (X b) :=
  Generators.cotangentSpaceBasis_apply _ b

/-- The chain map induced by `towerConstHom` is zero in degree `1`. -/
public theorem cotangentMap_towerConstHom_eq_zero :
    Extension.Cotangent.map (towerConstHom A B C).toExtensionHom = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Extension.Cotangent.mk_surjective x
  have hy : ((towerConstHom A B C).toExtensionHom).toAlgHom y.1 = 0 := by
    simpa [Generators.Hom.toExtensionHom_toAlgHom_apply] using
      towerConstHom_toAlgHom_eq_zero_of_mem_ker A B C y.1 y.2
  rw [LinearMap.zero_apply, Extension.Cotangent.map_mk, Extension.Cotangent.mk_eq_zero_iff]
  show (towerConstHom A B C).toExtensionHom.toAlgHom y.1 ∈
    (Generators.self B C).toExtension.ker ^ 2
  rw [hy]
  exact Ideal.zero_mem _

/-- The chain map induced by `towerConstHom` is zero in degree `0`. -/
public theorem cotangentSpaceMap_towerConstHom_eq_zero :
    Extension.CotangentSpace.map (towerConstHom A B C).toExtensionHom = 0 := by
  refine (Generators.self A B).cotangentSpaceBasis.ext fun b => ?_
  have hzero : KaehlerDifferential.D B (Generators.self B C).toExtension.Ring
      ((towerConstHom A B C).toAlgHom (X b)) = 0 :=
    towerConstHom_D_toAlgHom_eq_zero A B C (X b)
  rw [cotangentSpaceBasis_self_apply, Extension.CotangentSpace.map_tmul, LinearMap.zero_apply,
    Generators.Hom.toExtensionHom_toAlgHom_apply, hzero, TensorProduct.tmul_zero]

/-- The chain map that `towerConstHom` induces on naive cotangent complexes is the zero chain
map. -/
public theorem nlMapBase_towerConstHom_eq_zero :
    nlMapBase B (Generators.self A B) (Generators.self B C) (towerConstHom A B C) =
      ChainMap.zero (nlRestrict B (Generators.self A B))
        (nlRestrict B (Generators.self B C)) := by
  refine ChainMap.ext ?_ ?_
  · rw [nlMapBase_f₁, ChainMap.zero_f₁, cotangentMap_towerConstHom_eq_zero]
    rfl
  · rw [nlMapBase_f₀, ChainMap.zero_f₀, cotangentSpaceMap_towerConstHom_eq_zero]
    rfl

/-- The composition `NL_{B/A} ⟶ NL_{C/A} ⟶ NL_{C/B}` of the two functoriality maps, viewed
over the source ring `B`. -/
public noncomputable def towerChainMap :
    ChainMap (nlRestrict B (Generators.self A B)) (nlRestrict B (Generators.self B C)) :=
  (nlMapBase B (Generators.self A C) (Generators.self B C) (towerTopHom A B C)).comp
    (nlMapBase B (Generators.self A B) (Generators.self A C) (towerMidHom A B C))

/-- The composition is the chain map attached to the morphism of presentations
`A[B] ⟶ B[C]`, `[b] ↦ [φ(b)]`. -/
public theorem towerChainMap_eq :
    towerChainMap A B C =
      nlMapBase B (Generators.self A B) (Generators.self B C)
        ((towerTopHom A B C).comp (towerMidHom A B C)) :=
  nlMapBase_comp_nlMapBase (Generators.self A B) (Generators.self A C)
    (Generators.self B C) (towerMidHom A B C) (towerTopHom A B C)

/-- The homotopy of Stacks 07VC: the `B`-linear map
`Ω_{A[B]/A} ⊗_{A[B]} B ⟶ J/J²`, where `J = Ker(B[C] → C)`, given by the difference of the
two morphisms of presentations `A[B] ⟶ B[C]`, `[b] ↦ [φ(b)]` and `[b] ↦ b`. -/
public noncomputable def towerNullHomotopy :
    (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self B C).toExtension.Cotangent :=
  (Extension.Hom.sub ((towerTopHom A B C).comp (towerMidHom A B C)).toExtensionHom
    (towerConstHom A B C).toExtensionHom).restrictScalars B

/-- **Stacks 07VC.** The composition `NL_{B/A} ⟶ NL_{C/A} ⟶ NL_{C/B}` of the two
functoriality maps of the naive cotangent complex is homotopic to the zero chain map. -/
@[stacks 07VC "the composition is homotopy equivalent to zero"]
public theorem towerChainMap_homotopic_zero :
    Homotopic (towerChainMap A B C)
      (ChainMap.zero (nlRestrict B (Generators.self A B))
        (nlRestrict B (Generators.self B C))) := by
  rw [towerChainMap_eq, ← nlMapBase_towerConstHom_eq_zero]
  exact nlMapBase_homotopic B (Generators.self A B) (Generators.self B C)
    ((towerTopHom A B C).comp (towerMidHom A B C)) (towerConstHom A B C)

/-- The two homotopy relations satisfied by `towerNullHomotopy`: it is a null homotopy of the
composition `NL_{B/A} ⟶ NL_{C/A} ⟶ NL_{C/B}`. -/
@[stacks 07VC "the displayed map is an explicit homotopy"]
public theorem towerNullHomotopy_spec :
    (towerChainMap A B C).f₁ = towerNullHomotopy A B C ∘ₗ
        (nlRestrict B (Generators.self A B)).d ∧
      (towerChainMap A B C).f₀ =
        (nlRestrict B (Generators.self B C)).d ∘ₗ towerNullHomotopy A B C := by
  rw [towerChainMap_eq]
  refine ⟨LinearMap.ext fun x => ?_, LinearMap.ext fun x => ?_⟩
  · have hx := LinearMap.congr_fun (Extension.Cotangent.map_sub_map
      ((towerTopHom A B C).comp (towerMidHom A B C)).toExtensionHom
      (towerConstHom A B C).toExtensionHom) x
    simp only [cotangentMap_towerConstHom_eq_zero, sub_zero, LinearMap.coe_comp,
      Function.comp_apply] at hx
    simpa only [nlMapBase_f₁, LinearMap.coe_restrictScalars, towerNullHomotopy, nlRestrict,
      LinearMap.coe_comp, Function.comp_apply] using hx
  · have hx := LinearMap.congr_fun (Extension.CotangentSpace.map_sub_map
      ((towerTopHom A B C).comp (towerMidHom A B C)).toExtensionHom
      (towerConstHom A B C).toExtensionHom) x
    simp only [cotangentSpaceMap_towerConstHom_eq_zero, sub_zero, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_restrictScalars] at hx
    simpa only [nlMapBase_f₀, LinearMap.coe_restrictScalars, towerNullHomotopy, nlRestrict,
      LinearMap.coe_comp, Function.comp_apply] using hx

/-- The element `[φ(b)] - b` lies in the presentation ideal `J = Ker(B[C] → C)`. -/
public theorem X_sub_C_mem_ker (b : B) :
    (X (algebraMap B C b) - MvPolynomial.C b : (Generators.self B C).Ring) ∈
      (Generators.self B C).ker := by
  rw [Generators.ker_eq_ker_aeval_val, RingHom.mem_ker, map_sub]
  simp [Generators.self]

/-- **Stacks 07VC.** The homotopy sends the basis element `d[b]` of
`Ω_{A[B]/A} ⊗_{A[B]} B` to the class of `[φ(b)] - b` in `J/J²`. -/
@[stacks 07VC "the value of the homotopy on the basis element d[b]"]
public theorem towerNullHomotopy_cotangentSpaceBasis (b : B) :
    towerNullHomotopy A B C ((Generators.self A B).cotangentSpaceBasis b) =
      Extension.Cotangent.mk
        ⟨X (algebraMap B C b) - MvPolynomial.C b, X_sub_C_mem_ker B C b⟩ := by
  rw [cotangentSpaceBasis_self_apply, towerNullHomotopy, LinearMap.coe_restrictScalars,
    Extension.Hom.sub_one_tmul]
  refine congrArg _ (Subtype.ext ?_)
  simp only [Extension.Hom.subToKer_apply_coe, Generators.Hom.toExtensionHom_toRingHom,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [Generators.Hom.toAlgHom_X, Generators.Hom.toAlgHom_X, Generators.Hom.comp_val,
    towerMidHom_val, MvPolynomial.aeval_X, towerTopHom_val, towerConstHom_val]

end Tower

end NaiveCotangent

end
