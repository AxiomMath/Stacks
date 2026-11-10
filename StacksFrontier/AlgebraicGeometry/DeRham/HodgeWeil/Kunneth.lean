module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.AxiomsBasic
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DegreeZero
public import StacksFrontier.AlgebraicGeometry.DeRham.CechCupProduct
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethOfIsPullback

/-!
# The axiom (A5) for Hodge cohomology: the point, and the reduction to bidegrees

The axiom (A5) of Weil cohomology theories (Section 0FID),
`Stacks.WeilCohomology.FirstChernClassData.KunnethAxiom`, asks that `H^*(Spec k) = F` and that,
for smooth projective `X` and `Y` with projections `p` and `q` of `X × Y`, the map
`H^*(X) ⊗_F H^*(Y) ⟶ H^*(X × Y)`, `a ⊗ b ↦ p^*a ∪ q^*b`, be bijective; it then holds for every
fibre product `P` of `X` and `Y` over `Spec k`
(`Stacks.WeilDeRham.bijective_kunneth_of_isPullback`). For Hodge cohomology over a field `k`
(Remark 0FWE) this file proves the first half and reduces the second half, for every such fibre
product `P`, to one bidegree at a time.

*The point.* `H^*_{Hodge}(Spec(k)/k) = k`: the structure map `k ⟶ H^*_{Hodge}(Spec(k)/k)`,
`c ↦ c · 1`, is bijective. Indeed `H^q(Spec k, Ω^p) = 0` unless `p = q = 0`, and
`H^0(Spec k, Ω^0) = Γ(Spec k, 𝒪) = k`, the unit class being the class of the function `1`.

*The reduction.* `H^*_{Hodge}(X/k)` is the direct sum of the `H^b(X, Ω^a_{X/k})` over all
bidegrees `(a, b)`, and on a pair of classes of bidegrees `(a, b)` and `(c, d)` the Künneth map
is the external cup product `ξ ⊗ ζ ↦ p^*ξ ∪ q^*ζ`, of bidegree `(a + c, b + d)`. A map of direct
sums which is homogeneous for a map of index sets is bijective exactly when it is bijective on
each fibre of that map, so the Künneth map is bijective exactly when, for every `(r, s)`,

`⨁_{a + c = r, b + d = s} H^b(X, Ω^a_{X/k}) ⊗_k H^d(Y, Ω^c_{Y/k}) ⟶ H^s(P, Ω^r_{P/k})`

is bijective. That bidegree statement is the coherent Künneth formula (Tag 0BED) applied to the
decomposition `Ω^r_{P/k} = ⨁_{a + c = r} pr₁^*Ω^a_{X/k} ⊗ pr₂^*Ω^c_{Y/k}`.

## Main definitions

* `Stacks.HodgeWeil.hodgeComponentModule`: `H^q(X, Ω^p_{X/k})` as a `k`-vector space.
* `Stacks.HodgeWeil.hodgeBigradedEquiv`: `H^*_{Hodge}(X/k) = ⨁_{(p, q)} H^q(X, Ω^p_{X/k})`.
* `Stacks.HodgeWeil.hodgeComponentPullback`: the pullback on `H^q(-, Ω^p)`, `k`-linearly.
* `Stacks.HodgeWeil.hodgeExternalCup`: the external cup product `(ξ, ζ) ↦ p^*ξ ∪ q^*ζ`.
* `Stacks.HodgeWeil.hodgeKunnethMap`: the Künneth map of axiom (A5).
* `Stacks.HodgeWeil.hodgeKunnethBidegreeMap`: the Künneth map in bidegree `(r, s)`.

## Main results

* `Stacks.HodgeWeil.bijective_iff_forall_bijective_of_lof`: a map of direct sums homogeneous
  for `d : ι ⟶ κ` is bijective iff it is bijective on each fibre of `d`.
* `Stacks.HodgeWeil.hodgeOne_eq_hodgeSectionClass`: the unit class `1 ∈ H^0(X, Ω^0)` is the class
  of the global function `1`.
* `Stacks.HodgeWeil.bijective_algebraMap_hodgeAlgebraOf_of_isIso`: for `X` smooth projective
  over `k` with structure morphism an isomorphism, `k ⟶ H^*_{Hodge}(X/k)` is bijective.
* `Stacks.HodgeWeil.bijective_algebraMap_hodgeAlgebraOf_point`: **`H^*_{Hodge}(Spec(k)/k) = k`**,
  the first half of axiom (A5) for Hodge cohomology.
* `Stacks.HodgeWeil.bijective_hodgeKunnethMap_iff`: the Künneth map is bijective iff it is
  bijective in every bidegree.
* `Stacks.HodgeWeil.hodge_kunnethAxiom_iff`: **axiom (A5) for Hodge cohomology is equivalent to
  the Künneth formula in every bidegree.**

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open scoped TensorProduct
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent deRhamTerm baseRingedSpace
  reindexHodgeDeg hodgeCohomologyCup hodgeCupProduct_add_left hodgeCupProduct_add_right
  reindexHodgeDeg_add)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

/-! ### Bijectivity of a map of direct sums, fibre by fibre -/

section Fibres

variable {R : Type*} [Semiring R] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {M : ι → Type*} {N : κ → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ c, AddCommMonoid (N c)] [∀ c, Module R (N c)] (d : ι → κ)

/-- Regrouping a direct sum along the fibres of a map `d : ι ⟶ κ`:
`⨁_{i} M i ≅ ⨁_{c} ⨁_{d i = c} M i`. -/
def directSumFibreEquiv :
    (DirectSum ι M) ≃ₗ[R] DirectSum κ fun c => DirectSum {i // d i = c} fun i => M i.1 :=
  (DirectSum.lequivCongrLeft R (Equiv.sigmaFiberEquiv d).symm).trans
    (DirectSum.sigmaLcurryEquiv R (δ := fun c (i : {i // d i = c}) => M i.1))

/-- The regrouping along the fibres on a single summand. -/
theorem directSumFibreEquiv_lof (i : ι) (x : M i) :
    directSumFibreEquiv (R := R) d (DirectSum.lof R ι M i x) =
      DirectSum.lof R κ _ (d i)
        (DirectSum.lof R {j // d j = d i} (fun j => M j.1) ⟨i, rfl⟩ x) := by
  change DirectSum.sigmaLcurryEquiv R (δ := fun c (i : {i // d i = c}) => M i.1)
    (DirectSum.lequivCongrLeft R (Equiv.sigmaFiberEquiv d).symm (DirectSum.lof R ι M i x)) = _
  refine (congrArg (DirectSum.sigmaLcurryEquiv R (δ := fun c (i : {i // d i = c}) => M i.1))
    (DirectSum.lequivCongrLeft_lof R (e := (Equiv.sigmaFiberEquiv d).symm)
      (k := ⟨d i, ⟨i, rfl⟩⟩) rfl x x rfl)).trans ?_
  exact DirectSum.sigmaCurry_of (δ := fun c (i : {i // d i = c}) => M i.1) ⟨d i, ⟨i, rfl⟩⟩ x

variable {d}

/-- **A map of direct sums homogeneous for `d : ι ⟶ κ` is bijective iff it is bijective on every
fibre.** Let `F : ⨁_{i} M i ⟶ ⨁_{c} N c` carry the summand `M i` into the summand `N (d i)`, and
let `G c : ⨁_{d i = c} M i ⟶ N c` be its restriction to the fibre over `c`. Then `F` is bijective
if and only if every `G c` is. -/
theorem bijective_iff_forall_bijective_of_lof (F : DirectSum ι M →ₗ[R] DirectSum κ N)
    (G : ∀ c, (DirectSum {i // d i = c} fun i => M i.1) →ₗ[R] N c)
    (hFG : ∀ (i : ι) (x : M i), F (DirectSum.lof R ι M i x) =
      DirectSum.lof R κ N (d i)
        (G (d i) (DirectSum.lof R {j // d j = d i} (fun j => M j.1) ⟨i, rfl⟩ x))) :
    Function.Bijective F ↔ ∀ c, Function.Bijective (G c) := by
  have hF : F = DirectSum.lmap G ∘ₗ (directSumFibreEquiv (R := R) d).toLinearMap := by
    refine DirectSum.linearMap_ext R fun i => LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, directSumFibreEquiv_lof,
      DirectSum.lmap_lof]
    exact hFG i x
  rw [hF, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.Bijective.of_comp_iff _ (directSumFibreEquiv (R := R) d).bijective]
  exact ⟨fun h c => ⟨(DirectSum.lmap_injective G).1 h.1 c, (DirectSum.lmap_surjective G).1 h.2 c⟩,
    fun h => ⟨(DirectSum.lmap_injective G).2 fun c => (h c).1,
      (DirectSum.lmap_surjective G).2 fun c => (h c).2⟩⟩

end Fibres

/-! ### The unit class is the class of the global function `1` -/

section RingedSpace

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier)
    (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u, u, u} φ))

/-- **The unit class is the class of the global function `1`**: `hodgeOne` is the image of the
global section `1` of `Ω^0` under `hodgeSectionClass`. -/
theorem hodgeOne_eq_hodgeSectionClass :
    hodgeOne B = hodgeSectionClass B 0 (show globalForms B 0 from B.exterior.one.eval (op ⊤)) := by
  have hcyc : formsOneCycle B = (sectionCycle (baseRingedSpace A) (deRhamTerm (X := X) B 0)).hom
      (show globalForms B 0 from B.exterior.one.eval (op ⊤)) := by
    apply (ModuleCat.mono_iff_injective _).1 (inferInstance : Mono
      ((Stacks.Cohomology.DerivedGlobalCupProduct.sectionsComplex (baseRingedSpace A)
        (singleInt (X := X) (A := A) (@deRhamTerm X A φ B 0))).iCycles 0))
    refine (iCycles_formsOneCycle B).trans ?_
    exact (iCycles_sectionCycle (baseRingedSpace A) (deRhamTerm (X := X) B 0) _).symm
  have h1 := hodgeOne_eq_globalClass B
  have h2 := Stacks.Cohomology.DerivedGlobalCupProduct.globalCycleClass_apply
    (X := baseRingedSpace A) (sectionCycle (baseRingedSpace A) (deRhamTerm (X := X) B 0))
    (show globalForms B 0 from B.exterior.one.eval (op ⊤))
  have h3 := congrArg (fun g => g.hom (show globalForms B 0 from B.exterior.one.eval (op ⊤)))
    (hodgeSectionClass_eq_globalCycleClass B 0)
  rw [hcyc] at h1
  exact h1.trans (h2.symm.trans h3.symm)

end RingedSpace

/-! ### The point -/

section Point

variable {k : Type u} [Field k]

/-- The scalar `c ∈ k` acts on the global function `1` of a `k`-scheme `f : X ⟶ Spec k` as the
function `f^♯(c)`. -/
theorem hodgeScalarsOverField_smul_one {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (c : k) :
    hodgeScalarsOverField f c •
        (show globalForms (formsAlgebras f) 0 from (formsAlgebras f).exterior.one.eval (op ⊤)) =
      (show globalForms (formsAlgebras f) 0 from
        (show X.sheaf.obj.obj (op ⊤) from
          (f.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) •
          (formsAlgebras f).exterior.one.eval (op ⊤)) := by
  have h := ConcreteCategory.congr_hom
    (Scheme.Hom.inverseImageGlobalSections_comp_inverseImageStructureMap_app f)
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
  exact congrArg (fun r : X.sheaf.obj.obj (op ⊤) =>
    (show globalForms (formsAlgebras f) 0 from
      r • (formsAlgebras f).exterior.one.eval (op ⊤))) h

/-- **`k = H^0(X, Ω^0_{X/k})` through the unit class** for `f : X ⟶ Spec k` an isomorphism: the
map `c ↦ c · 1` is bijective. -/
theorem bijective_hodgeScalarsOverField_smul_hodgeOne {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsIso f] :
    Function.Bijective (fun c : k => hodgeScalarsOverField f c • hodgeOne (formsAlgebras f)) := by
  convert bijective_hodgeSectionClass_of_isIso f using 2 with c
  rw [hodgeOne_eq_hodgeSectionClass, ← map_smul]
  exact congrArg _ (hodgeScalarsOverField_smul_one f c)

end Point

/-! ### Hodge cohomology of the point -/

section Algebra

variable {k : Type u} [Field k]

/-- The bidegree `(0, 0)`, the only bidegree of total degree `0`. -/
def bidegreeZeroZero : HodgeBidegreeInt 0 := ⟨(0, 0), rfl⟩

/-- The inclusion `H^0(X, Ω^0) ⟶ H^*_{Hodge}(X/k)` of the summand of bidegree `(0, 0)`. -/
def hodgeZeroZeroIncl (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (hodgeCohomologyComponent (formsAlgebras X.obj.hom) 0 0 : Type u) →+ hodgeAlgebraOf X :=
  (DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) 0).comp
    (DirectSum.of (fun i : HodgeBidegreeInt 0 =>
      (hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ) : Type u))
      bidegreeZeroZero)

/-- The inclusion of the summand of bidegree `(0, 0)` is injective. -/
theorem injective_hodgeZeroZeroIncl (X : (SmoothProjectiveScheme k).FullSubcategory) :
    Function.Injective (hodgeZeroZeroIncl X) :=
  (DirectSum.of_injective (β := hodgePiece (formsAlgebras X.obj.hom)) 0).comp
    (DirectSum.of_injective (β := fun i : HodgeBidegreeInt 0 =>
      (hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ) : Type u))
      bidegreeZeroZero)

/-- **`H^*_{Hodge}(X/k) = H^0(X, Ω^0_{X/k})`** when the structure morphism of `X` is an
isomorphism: every other summand vanishes. -/
theorem surjective_hodgeZeroZeroIncl_of_isIso (X : (SmoothProjectiveScheme k).FullSubcategory)
    [IsIso X.obj.hom] : Function.Surjective (hodgeZeroZeroIncl X) := by
  intro a
  change a ∈ (hodgeZeroZeroIncl X).range
  induction a using DirectSum.induction_on with
  | zero => exact zero_mem _
  | add a a' ha ha' => exact add_mem ha ha'
  | of n x =>
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add x x' hx hx' => rw [map_add]; exact add_mem hx hx'
    | of i ξ =>
      obtain ⟨⟨p, q⟩, hpq⟩ := i
      by_cases h : p = 0 ∧ q = 0
      · obtain ⟨rfl, rfl⟩ := h
        subst hpq
        exact ⟨ξ, rfl⟩
      · have hz := isZero_hodgeCohomologyComponent_of_isIso X.obj.hom (p := p) (q := (q : ℤ))
          (by lia)
        have := ModuleCat.subsingleton_of_isZero hz
        rw [Subsingleton.elim ξ 0, map_zero, map_zero]
        exact zero_mem _

/-- The structure map `k ⟶ H^*_{Hodge}(X/k)` is `c ↦ c · 1` in the summand of bidegree
`(0, 0)`. -/
theorem algebraMap_hodgeAlgebraOf (X : (SmoothProjectiveScheme k).FullSubcategory) (c : k) :
    algebraMap k (hodgeAlgebraOf X) c =
      hodgeZeroZeroIncl X
        (hodgeScalarsOverField X.obj.hom c • hodgeOne (formsAlgebras X.obj.hom)) := by
  change DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) 0
      (hodgeScalarsOverField X.obj.hom c • hodgePieceOne (formsAlgebras X.obj.hom)) = _
  rw [hodgePieceOne, ← DirectSum.of_smul]
  rfl

/-- **`H^*_{Hodge}(X/k) = k`** for `X` smooth projective over `k` with structure morphism an
isomorphism: the structure map `k ⟶ H^*_{Hodge}(X/k)` is bijective. -/
theorem bijective_algebraMap_hodgeAlgebraOf_of_isIso
    (X : (SmoothProjectiveScheme k).FullSubcategory) [IsIso X.obj.hom] :
    Function.Bijective (algebraMap k (hodgeAlgebraOf X)) := by
  have h : (algebraMap k (hodgeAlgebraOf X) : k → hodgeAlgebraOf X) =
      hodgeZeroZeroIncl X ∘
        fun c => hodgeScalarsOverField X.obj.hom c • hodgeOne (formsAlgebras X.obj.hom) :=
    funext (algebraMap_hodgeAlgebraOf X)
  rw [h]
  exact Function.Bijective.comp
    ⟨injective_hodgeZeroZeroIncl X, surjective_hodgeZeroZeroIncl_of_isIso X⟩
    (bijective_hodgeScalarsOverField_smul_hodgeOne X.obj.hom)

/-- The structure morphism of `Spec k`, the identity, is an isomorphism. -/
instance isIso_point_hom : IsIso (point k).obj.hom :=
  inferInstanceAs (IsIso (𝟙 (Spec (CommRingCat.of k))))

variable (k) in
/-- **`H^*_{Hodge}(Spec(k)/k) = k`** (Remark 0FWE): the structure map
`k ⟶ H^*_{Hodge}(Spec(k)/k)` is bijective. This is the first half of axiom (A5) of Section 0FID
for Hodge cohomology. -/
theorem bijective_algebraMap_hodgeAlgebraOf_point :
    Function.Bijective (Algebra.linearMap k ((hodgeFirstChernClassData k).H (point k))) :=
  bijective_algebraMap_hodgeAlgebraOf_of_isIso (point k)

end Algebra

/-! ### Hodge cohomology as a bigraded vector space -/

section Bigraded

variable {k : Type u} [Field k]

/-- **`k` acts on `H^q(X, Ω^p_{X/k})`** of a `k`-scheme `f : X ⟶ Spec k` through the ring map
`k ⟶ Γ(X, f⁻¹𝒪_{Spec k})` over whose target the group is a module. -/
instance hodgeComponentModule {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) (q : ℤ) :
    Module k (hodgeCohomologyComponent (formsAlgebras f) p q) :=
  Module.compHom _ (hodgeScalarsOverField f)

/-- `c ∈ k` acts on `H^q(X, Ω^p_{X/k})` as its image in `Γ(X, f⁻¹𝒪_{Spec k})`. -/
theorem hodgeComponent_smul_def {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ)
    (q : ℤ) (c : k) (x : hodgeCohomologyComponent (formsAlgebras f) p q) :
    c • x = hodgeScalarsOverField f c • x :=
  rfl

/-- The summand `H^q(X, Ω^p_{X/k})` of `H^*_{Hodge}(X/k)` in bidegree `(p, q) ∈ ℕ × ℕ`. -/
abbrev hodgeComponentOf (X : (SmoothProjectiveScheme k).FullSubcategory) (pq : ℕ × ℕ) :
    Type u :=
  hodgeCohomologyComponent (formsAlgebras X.obj.hom) pq.1 (pq.2 : ℤ)

/-- The bidegrees of all total degrees are the pairs of natural numbers. -/
def hodgeBidegreeSigmaEquiv : (Σ n : ℤ, HodgeBidegreeInt n) ≃ ℕ × ℕ where
  toFun x := x.2.1
  invFun pq := ⟨((pq.1 + pq.2 : ℕ) : ℤ), ⟨pq, rfl⟩⟩
  left_inv := by
    rintro ⟨n, ⟨pq, rfl⟩⟩
    rfl
  right_inv _ := rfl

variable (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- `H^*_{Hodge}(X/k) = ⨁_{(p, q)} H^q(X, Ω^p_{X/k})`, linearly over the global sections of the
base ring sheaf. -/
def hodgeBigradedEquivBase :
    hodgeAlgebraOf X ≃ₗ[hodgeBaseRing X.obj.hom] DirectSum (ℕ × ℕ) (hodgeComponentOf X) :=
  (DirectSum.sigmaLcurryEquiv (hodgeBaseRing X.obj.hom)
      (δ := fun n (i : HodgeBidegreeInt n) =>
        (hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ) : Type u))).symm.trans
    (DirectSum.lequivCongrLeft (hodgeBaseRing X.obj.hom) hodgeBidegreeSigmaEquiv)

/-- **`H^*_{Hodge}(X/k) = ⨁_{(p, q)} H^q(X, Ω^p_{X/k})`** as `k`-vector spaces. -/
def hodgeBigradedEquiv : hodgeAlgebraOf X ≃ₗ[k] DirectSum (ℕ × ℕ) (hodgeComponentOf X) where
  toAddEquiv := (hodgeBigradedEquivBase X).toAddEquiv
  map_smul' c x := (hodgeBigradedEquivBase X).map_smul (hodgeScalarsOverField X.obj.hom c) x

/-- `hodgeBigradedEquiv` on a class of pure bidegree. -/
theorem hodgeBigradedEquiv_of (n : ℤ) (i : HodgeBidegreeInt n)
    (x : hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ)) :
    hodgeBigradedEquiv X (DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) n
        (DirectSum.of (fun j : HodgeBidegreeInt n =>
          (hodgeCohomologyComponent (formsAlgebras X.obj.hom) j.1.1 (j.1.2 : ℤ) : Type u)) i x)) =
      DirectSum.lof k (ℕ × ℕ) (hodgeComponentOf X) i.1 x := by
  change DirectSum.lequivCongrLeft (hodgeBaseRing X.obj.hom) hodgeBidegreeSigmaEquiv
      ((DirectSum.sigmaLcurryEquiv (hodgeBaseRing X.obj.hom)
        (δ := fun n (i : HodgeBidegreeInt n) =>
          (hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ) : Type u))).symm
        (DirectSum.of _ n (DirectSum.of _ i x))) = _
  have h1 : (DirectSum.sigmaLcurryEquiv (hodgeBaseRing X.obj.hom)
        (δ := fun n (i : HodgeBidegreeInt n) =>
          (hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ) : Type u))).symm
        (DirectSum.of _ n (DirectSum.of _ i x)) =
      DirectSum.lof (hodgeBaseRing X.obj.hom) (Σ n : ℤ, HodgeBidegreeInt n)
        (fun j => (hodgeCohomologyComponent (formsAlgebras X.obj.hom) j.2.1.1
          (j.2.1.2 : ℤ) : Type u)) ⟨n, i⟩ x := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DirectSum.sigmaCurry_of (δ := fun n (i : HodgeBidegreeInt n) =>
      (hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ) : Type u))
        ⟨n, i⟩ x).symm
  rw [h1]
  exact DirectSum.lequivCongrLeft_lof (hodgeBaseRing X.obj.hom)
    (M := fun j : Σ n : ℤ, HodgeBidegreeInt n =>
      (hodgeCohomologyComponent (formsAlgebras X.obj.hom) j.2.1.1 (j.2.1.2 : ℤ) : Type u))
    (e := hodgeBidegreeSigmaEquiv) (k := i.1) (hodgeBidegreeSigmaEquiv.symm_apply_apply ⟨n, i⟩).symm
    x x (by exact cast_eq _ x)

end Bigraded

/-! ### The Künneth map in each bidegree -/

section KunnethBidegree

variable {k : Type u} [Field k] {X Y P : (SmoothProjectiveScheme k).FullSubcategory}

/-- **The pullback `f^* : H^q(Y, Ω^p_{Y/k}) ⟶ H^q(X, Ω^p_{X/k})`** along a morphism of smooth
projective `k`-schemes, as a `k`-linear map. -/
def hodgeComponentPullback (f : X ⟶ Y) (pq : ℕ × ℕ) :
    hodgeComponentOf Y pq →ₗ[k] hodgeComponentOf X pq where
  toFun := hodgePullback f.hom.left X.obj.hom Y.obj.hom (𝟙 _) (hodgeSquare_w f) pq.1 (pq.2 : ℤ)
  map_add' := map_add _
  map_smul' c x := by
    refine ((hodgePullback f.hom.left X.obj.hom Y.obj.hom (𝟙 _) (hodgeSquare_w f) pq.1
      (pq.2 : ℤ)).map_smulₛₗ (hodgeScalarsOverField Y.obj.hom c) x).trans ?_
    exact congrArg (· • _) (RingHom.congr_fun (hodgeBaseRingHom_comp_hodgeScalars f.hom.left
      (specScalars k) Y.obj.hom X.obj.hom (hodgeSquare_w f)) c)

/-- `hodgeComponentPullback f pq` is the pullback `f^*` on `H^q(Y, Ω^p)` for `pq = (p, q)`. -/
theorem hodgeComponentPullback_apply (f : X ⟶ Y) (pq : ℕ × ℕ) (x : hodgeComponentOf Y pq) :
    hodgeComponentPullback f pq x =
      hodgePullback f.hom.left X.obj.hom Y.obj.hom (𝟙 _) (hodgeSquare_w f) pq.1 (pq.2 : ℤ) x :=
  rfl

/-- The pullback `f^*` on `H^*_{Hodge}` of a class of pure bidegree. -/
theorem hodgePullbackOf_of_of (f : X ⟶ Y) (n : ℤ) (i : HodgeBidegreeInt n)
    (x : hodgeCohomologyComponent (formsAlgebras Y.obj.hom) i.1.1 (i.1.2 : ℤ)) :
    hodgePullbackOf f (DirectSum.of (hodgePiece (formsAlgebras Y.obj.hom)) n
        (DirectSum.of (fun j : HodgeBidegreeInt n =>
          (hodgeCohomologyComponent (formsAlgebras Y.obj.hom) j.1.1 (j.1.2 : ℤ) : Type u)) i x)) =
      DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) n
        (DirectSum.of (fun j : HodgeBidegreeInt n =>
          (hodgeCohomologyComponent (formsAlgebras X.obj.hom) j.1.1 (j.1.2 : ℤ) : Type u)) i
          (hodgeComponentPullback f i.1 x)) := by
  rw [hodgePullbackOf_of, hodgePiecePullback_of]
  rfl

variable (p : P ⟶ X) (q : P ⟶ Y)

/-- **The external cup product** `H^b(X, Ω^a) × H^d(Y, Ω^c) ⟶ H^{b + d}(P, Ω^{a + c})`,
`(ξ, ζ) ↦ p^*ξ ∪ q^*ζ`, for morphisms `p : P ⟶ X` and `q : P ⟶ Y` of smooth projective
`k`-schemes, as a `k`-bilinear map. -/
def hodgeExternalCup (ab cd : ℕ × ℕ) :
    hodgeComponentOf X ab →ₗ[k] hodgeComponentOf Y cd →ₗ[k]
      hodgeComponentOf P (ab.1 + cd.1, ab.2 + cd.2) :=
  LinearMap.mk₂ k
    (fun ξ ζ => reindexHodgeDeg (formsAlgebras P.obj.hom) (Nat.cast_add ab.2 cd.2).symm
      (hodgeCohomologyCup (formsAlgebras P.obj.hom) ab.1 cd.1 (ab.2 : ℤ) (cd.2 : ℤ)
        (hodgeComponentPullback p ab ξ) (hodgeComponentPullback q cd ζ)))
    (fun ξ ξ' ζ => by
      rw [map_add, hodgeCupProduct_add_left, reindexHodgeDeg_add])
    (fun c ξ ζ => by
      rw [map_smul, hodgeComponent_smul_def, hodgeCohomologyCup_smul_left, reindexHodgeDeg_smul]
      rfl)
    (fun ξ ζ ζ' => by
      rw [map_add, hodgeCupProduct_add_right, reindexHodgeDeg_add])
    (fun c ξ ζ => by
      rw [map_smul, hodgeComponent_smul_def, hodgeCohomologyCup_smul_right, reindexHodgeDeg_smul]
      rfl)

/-- The external cup product of `ξ` and `ζ` is the cup product of `p^*ξ` and `q^*ζ`, read in the
bidegree `(a + c, b + d)`. -/
theorem hodgeExternalCup_apply (ab cd : ℕ × ℕ) (ξ : hodgeComponentOf X ab)
    (ζ : hodgeComponentOf Y cd) :
    hodgeExternalCup p q ab cd ξ ζ =
      reindexHodgeDeg (formsAlgebras P.obj.hom) (Nat.cast_add ab.2 cd.2).symm
        (hodgeCohomologyCup (formsAlgebras P.obj.hom) ab.1 cd.1 (ab.2 : ℤ) (cd.2 : ℤ)
          (hodgeComponentPullback p ab ξ) (hodgeComponentPullback q cd ζ)) :=
  rfl

end KunnethBidegree

/-! ### Reduction of the Künneth map to bidegrees -/

section KunnethReduction

variable {k : Type u} [Field k] {X Y P : (SmoothProjectiveScheme k).FullSubcategory}

/-- The bidegree `(a + c, b + d)` of the external cup product of classes of bidegrees `(a, b)`
and `(c, d)`. -/
def hodgeBidegreeAdd (x : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  (x.1.1 + x.2.1, x.1.2 + x.2.2)

/-- A class of `H^q(Z, Ω^p)` read in an equal bidegree. -/
def hodgeComponentCast (Z : (SmoothProjectiveScheme k).FullSubcategory) {pq rs : ℕ × ℕ}
    (h : pq = rs) : hodgeComponentOf Z pq →ₗ[k] hodgeComponentOf Z rs := by
  subst h
  exact LinearMap.id

/-- Reading a class in its own bidegree is the identity. -/
@[simp]
theorem hodgeComponentCast_rfl (Z : (SmoothProjectiveScheme k).FullSubcategory) (pq : ℕ × ℕ) :
    hodgeComponentCast Z (rfl : pq = pq) = LinearMap.id :=
  rfl

variable (p : P ⟶ X) (q : P ⟶ Y)

/-- **The Künneth map in bidegree `(r, s)`**:
`⨁_{a + c = r, b + d = s} H^b(X, Ω^a_{X/k}) ⊗_k H^d(Y, Ω^c_{Y/k}) ⟶ H^s(P, Ω^r_{P/k})`,
`ξ ⊗ ζ ↦ p^*ξ ∪ q^*ζ`. -/
def hodgeKunnethBidegreeMap (rs : ℕ × ℕ) :
    (DirectSum {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = rs}
      fun x => hodgeComponentOf X x.1.1 ⊗[k] hodgeComponentOf Y x.1.2) →ₗ[k]
        hodgeComponentOf P rs :=
  DirectSum.toModule k _ _ fun x =>
    hodgeComponentCast P x.2 ∘ₗ TensorProduct.lift (hodgeExternalCup p q x.1.1 x.1.2)

/-- The Künneth map in bidegree `(a + c, b + d)` on a pure tensor of the summand of
bidegrees `(a, b)` and `(c, d)` is the external cup product. -/
theorem hodgeKunnethBidegreeMap_lof_tmul (ab cd : ℕ × ℕ) (ξ : hodgeComponentOf X ab)
    (ζ : hodgeComponentOf Y cd) :
    hodgeKunnethBidegreeMap p q (hodgeBidegreeAdd (ab, cd))
        (DirectSum.lof k {x : (ℕ × ℕ) × (ℕ × ℕ) // hodgeBidegreeAdd x = hodgeBidegreeAdd (ab, cd)}
          (fun x => hodgeComponentOf X x.1.1 ⊗[k] hodgeComponentOf Y x.1.2) ⟨(ab, cd), rfl⟩
          (ξ ⊗ₜ ζ)) =
      hodgeExternalCup p q ab cd ξ ζ := by
  rw [hodgeKunnethBidegreeMap, DirectSum.toModule_lof]
  rfl

/-- **The Künneth map** `H^*_{Hodge}(X/k) ⊗_k H^*_{Hodge}(Y/k) ⟶ H^*_{Hodge}(P/k)`,
`a ⊗ b ↦ p^*a ∪ q^*b`, of axiom (A5). -/
abbrev hodgeKunnethMap : hodgeAlgebraOf X ⊗[k] hodgeAlgebraOf Y →ₗ[k] hodgeAlgebraOf P :=
  TensorProduct.lift ((LinearMap.mul k (hodgeAlgebraOf P)).compl₁₂ (hodgePullbackOf p).toLinearMap
    (hodgePullbackOf q).toLinearMap)

/-- The Künneth map on classes of pure bidegree is the external cup product. -/
theorem hodgeKunnethMap_of_tmul_of {n m : ℤ} (i : HodgeBidegreeInt n) (j : HodgeBidegreeInt m)
    (ξ : hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ))
    (ζ : hodgeCohomologyComponent (formsAlgebras Y.obj.hom) j.1.1 (j.1.2 : ℤ)) :
    hodgeKunnethMap p q
        (DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) n
            (DirectSum.of (fun l : HodgeBidegreeInt n =>
              (hodgeCohomologyComponent (formsAlgebras X.obj.hom) l.1.1 (l.1.2 : ℤ) : Type u)) i
              ξ) ⊗ₜ
          DirectSum.of (hodgePiece (formsAlgebras Y.obj.hom)) m
            (DirectSum.of (fun l : HodgeBidegreeInt m =>
              (hodgeCohomologyComponent (formsAlgebras Y.obj.hom) l.1.1 (l.1.2 : ℤ) : Type u)) j
              ζ)) =
      DirectSum.of (hodgePiece (formsAlgebras P.obj.hom)) (n + m)
        (DirectSum.of (fun l : HodgeBidegreeInt (n + m) =>
          (hodgeCohomologyComponent (formsAlgebras P.obj.hom) l.1.1 (l.1.2 : ℤ) : Type u))
          ⟨(i.1.1 + j.1.1, i.1.2 + j.1.2), hodgeBidegreeInt_add i j⟩
          (hodgeExternalCup p q i.1 j.1 ξ ζ)) := by
  rw [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
    AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, hodgePullbackOf_of_of,
    hodgePullbackOf_of_of, hodgeAlgebra_of_mul_of, hodgePieceMul_of]
  rfl

variable (X Y) in
/-- `H^*_{Hodge}(X/k) ⊗_k H^*_{Hodge}(Y/k) = ⨁_{(a, b), (c, d)} H^b(X, Ω^a) ⊗_k H^d(Y, Ω^c)`. -/
def hodgeTensorBigradedEquiv :
    hodgeAlgebraOf X ⊗[k] hodgeAlgebraOf Y ≃ₗ[k]
      DirectSum ((ℕ × ℕ) × (ℕ × ℕ)) fun x => hodgeComponentOf X x.1 ⊗[k] hodgeComponentOf Y x.2 :=
  (TensorProduct.congr (hodgeBigradedEquiv X) (hodgeBigradedEquiv Y)).trans
    (TensorProduct.directSum k k (hodgeComponentOf X) (hodgeComponentOf Y))

/-- The inverse of `hodgeBigradedEquiv` on a single summand. -/
theorem hodgeBigradedEquiv_symm_lof (Z : (SmoothProjectiveScheme k).FullSubcategory)
    (ab : ℕ × ℕ) (x : hodgeComponentOf Z ab) :
    (hodgeBigradedEquiv Z).symm (DirectSum.lof k (ℕ × ℕ) (hodgeComponentOf Z) ab x) =
      DirectSum.of (hodgePiece (formsAlgebras Z.obj.hom)) ((ab.1 + ab.2 : ℕ) : ℤ)
        (DirectSum.of (fun l : HodgeBidegreeInt ((ab.1 + ab.2 : ℕ) : ℤ) =>
          (hodgeCohomologyComponent (formsAlgebras Z.obj.hom) l.1.1 (l.1.2 : ℤ) : Type u))
          ⟨ab, rfl⟩ x) := by
  rw [LinearEquiv.symm_apply_eq]
  exact (hodgeBigradedEquiv_of Z _ ⟨ab, rfl⟩ x).symm

/-- **The axiom (A5) for Hodge cohomology reduces to bidegrees**: the Künneth map
`H^*_{Hodge}(X/k) ⊗_k H^*_{Hodge}(Y/k) ⟶ H^*_{Hodge}(P/k)`, `a ⊗ b ↦ p^*a ∪ q^*b`, is bijective
if and only if, for every bidegree `(r, s)`, the map
`⨁_{a + c = r, b + d = s} H^b(X, Ω^a) ⊗_k H^d(Y, Ω^c) ⟶ H^s(P, Ω^r)`,
`ξ ⊗ ζ ↦ p^*ξ ∪ q^*ζ`, is bijective. -/
theorem bijective_hodgeKunnethMap_iff :
    Function.Bijective (hodgeKunnethMap p q) ↔
      ∀ rs, Function.Bijective (hodgeKunnethBidegreeMap p q rs) := by
  let F := (hodgeBigradedEquiv P).toLinearMap ∘ₗ hodgeKunnethMap p q ∘ₗ
    (hodgeTensorBigradedEquiv X Y).symm.toLinearMap
  have hF : Function.Bijective (hodgeKunnethMap p q) ↔ Function.Bijective F := by
    simp only [F, LinearMap.coe_comp, LinearEquiv.coe_coe]
    rw [Function.Bijective.of_comp_iff' (hodgeBigradedEquiv P).bijective,
      Function.Bijective.of_comp_iff _ (hodgeTensorBigradedEquiv X Y).symm.bijective]
  rw [hF]
  refine bijective_iff_forall_bijective_of_lof (d := hodgeBidegreeAdd) F _ fun x t => ?_
  obtain ⟨ab, cd⟩ := x
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul ξ ζ =>
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hodgeKunnethBidegreeMap_lof_tmul]
    have hT : (hodgeTensorBigradedEquiv X Y).symm
        (DirectSum.lof k ((ℕ × ℕ) × (ℕ × ℕ))
          (fun x => hodgeComponentOf X x.1 ⊗[k] hodgeComponentOf Y x.2) (ab, cd) (ξ ⊗ₜ ζ)) =
        (hodgeBigradedEquiv X).symm (DirectSum.lof k (ℕ × ℕ) (hodgeComponentOf X) ab ξ) ⊗ₜ
          (hodgeBigradedEquiv Y).symm (DirectSum.lof k (ℕ × ℕ) (hodgeComponentOf Y) cd ζ) := by
      rw [hodgeTensorBigradedEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
        TensorProduct.directSum_symm_lof_tmul, TensorProduct.congr_symm_tmul]
    rw [hT]
    exact (congrArg (fun t => hodgeBigradedEquiv P (hodgeKunnethMap p q t))
      (congrArg₂ (TensorProduct.tmul k) (hodgeBigradedEquiv_symm_lof X ab ξ)
        (hodgeBigradedEquiv_symm_lof Y cd ζ))).trans
      ((congrArg (hodgeBigradedEquiv P)
        (hodgeKunnethMap_of_tmul_of p q ⟨ab, rfl⟩ ⟨cd, rfl⟩ ξ ζ)).trans
        (hodgeBigradedEquiv_of P _ _ _))

end KunnethReduction

/-! ### The axiom (A5) -/

variable (k : Type u) [Field k] in
/-- **The axiom (A5) for Hodge cohomology, reduced to bidegrees.** Since
`H^*_{Hodge}(Spec(k)/k) = k` (`bijective_algebraMap_hodgeAlgebraOf_point`), axiom (A5) of
Section 0FID, `Stacks.WeilCohomology.FirstChernClassData.KunnethAxiom`, holds for Hodge
cohomology if and only if, for every fibre product `P` of smooth projective `X` and `Y` over
`Spec k` with projections `p` and `q` and every bidegree `(r, s)`, the map
`⨁_{a + c = r, b + d = s} H^b(X, Ω^a_{X/k}) ⊗_k H^d(Y, Ω^c_{Y/k}) ⟶ H^s(P, Ω^r_{P/k})`,
`ξ ⊗ ζ ↦ p^*ξ ∪ q^*ζ`, is bijective. The axiom is about `P = X × Y`; it gives the Künneth
isomorphism for every fibre product by `Stacks.WeilDeRham.bijective_kunneth_of_isPullback`. -/
theorem hodge_kunnethAxiom_iff :
    (hodgeFirstChernClassData k).KunnethAxiom ↔
      ∀ (X Y P : (SmoothProjectiveScheme k).FullSubcategory) (p : P ⟶ X) (q : P ⟶ Y),
        IsPullback ((toScheme k).map p) ((toScheme k).map q) X.obj.hom Y.obj.hom →
          ∀ rs, Function.Bijective (hodgeKunnethBidegreeMap p q rs) :=
  ⟨fun h _ _ _ p q hP => (bijective_hodgeKunnethMap_iff p q).1
      (Stacks.WeilDeRham.bijective_kunneth_of_isPullback p q hP h),
    fun h => ⟨bijective_algebraMap_hodgeAlgebraOf_point k, fun X Y =>
      (bijective_hodgeKunnethMap_iff (SmoothProjectiveScheme.fst X Y)
        (SmoothProjectiveScheme.snd X Y)).2
        (h X Y _ _ _ (Stacks.WeilDeRham.isPullback_fst_snd X Y))⟩⟩

end Stacks.HodgeWeil

end
