module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.SymmetricToLaurentEpi
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePowers.ModuleStalk

/-!
# Charts of an invertible module in its Laurent ring of local sections

Let `L` be an invertible module on a scheme `X`. Over each open `W` of `X` the homogeneous local
sections of the integer tensor powers `L^{⊗ k}` form a commutative `ℤ`-graded ring
`⨁_{k ∈ ℤ} L^{⊗ k}(W)`: the ungraded realization, over `W`, of the Laurent algebra
`Stacks.LineBundle.Situation.laurentAlgebra` of `L`, before sheafification. This file develops the
elementary calculus of that ring:

* homogeneous elements multiply by adding degrees, restrict to smaller opens, and the degree-zero
  ones are exactly the functions;
* a **chart** is an open `U` with a homogeneous unit `ε` of degree one (its inverse homogeneous of
  degree `-1`); over every open `W ⊆ U`, every homogeneous element of degree `k ≥ 0` is uniquely a
  function times `ε^k`;
* the nonvanishing locus of a section `f · ε^k` of `L^{⊗ k}` over `W ⊆ U` is the basic open of the
  function `f`;
* every point of `X` lies in an affine chart.

## Main definitions

* `Stacks.TwistedThickeningLift.laurent`: the Laurent algebra of `L`, as a graded algebra of
  presheaves of modules.
* `Stacks.TwistedThickeningLift.LRing`: its ring of sections over an open, a commutative ring.
* `Stacks.TwistedThickeningLift.IsHom`: homogeneity of a given degree.
* `Stacks.TwistedThickeningLift.IsChart`: a homogeneous unit of degree one over an open.

## Main results

* `Stacks.TwistedThickeningLift.IsChart.exists_eq`: every homogeneous element of degree `k ≥ 0`
  over an open inside a chart is a function times the `k`th power of the chart unit, and
  `IsChart.eq_of_eq` makes the function unique.
* `Stacks.TwistedThickeningLift.IsChart.nonvanishingLocusOn_eq`: the nonvanishing locus of
  `f · ε^k` is the basic open of `f`.
* `Stacks.TwistedThickeningLift.exists_isAffineOpen_isChart`: every point lies in an affine chart.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped Stacks.ModuleStalk
open Stacks.Ample (IsInvertibleModule)

universe u

namespace Stacks.TwistedThickeningLift

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- The line-bundle situation of `L` over `X` itself, with structure morphism the identity. -/
abbrev situation : Stacks.LineBundle.Situation.{u} where
  X := X
  S := X
  f := 𝟙 X
  L := L
  invertible := ‹IsInvertibleModule X L›

/-- The `k`th integer tensor power of `L` as a piece of its Laurent algebra. -/
abbrev pow (k : ℤ) : X.Modules := (situation L).tensorPower k

/-- **The Laurent algebra `⨁_{k ∈ ℤ} L^{⊗ k}` of `L`**, as a graded algebra of presheaves of
modules. -/
abbrev laurent : Stacks.GradedAlgebra fun k : ℤ => (pow L k).val :=
  (situation L).laurentAlgebra.toPresheafGradedAlgebra

/-- **The ring `⨁_{k ∈ ℤ} L^{⊗ k}(W)` of homogeneous local sections over `W`.** -/
abbrev LRing (W : X.Opens) : Type u := (laurent L).Total (op W)

/-- The Laurent ring of `L` over `W` is a commutative ring. -/
instance (W : X.Opens) : CommRing (LRing L W) :=
  (laurent L).commRingTotal (situation L).laurentAlgebra_mul_comm (op W)

variable {L}

/-- A homogeneous local section of degree `k`, in the Laurent ring. -/
abbrev incl {W : X.Opens} (k : ℤ) (y : Γ(pow L k, W)) : LRing L W :=
  (laurent L).incl k y

/-- Restriction of a local section of a tensor power to a smaller open. -/
abbrev pres {W W' : X.Opens} (h : W' ≤ W) {k : ℤ} (y : Γ(pow L k, W)) : Γ(pow L k, W') :=
  Stacks.sectionRestrict (pow L k).val (homOfLE h).op y

/-- Restriction of the Laurent ring to a smaller open, as a ring homomorphism. -/
def res {W W' : X.Opens} (h : W' ≤ W) : LRing L W →+* LRing L W' :=
  (laurent L).totalRestrictRingHom (homOfLE h).op

variable (L) in
/-- A function, in the Laurent ring: the structure map `f ↦ f • 1`. -/
def alg (W : X.Opens) : Γ(X, W) →+* LRing L W :=
  (laurent L).structureMap (op W)

variable (L) in
/-- **Homogeneity of degree `k`** of an element of the Laurent ring. -/
def IsHom {W : X.Opens} (k : ℤ) (a : LRing L W) : Prop :=
  ∃ y : Γ(pow L k, W), incl k y = a

/-- The inclusion of the degree-`k` sections into the Laurent ring is injective. -/
theorem incl_injective {W : X.Opens} (k : ℤ) :
    Function.Injective (incl (L := L) (W := W) k) :=
  DirectSum.of_injective (β := fun i => ((pow L i).val.obj (op W) : Type u)) k

/-- The product of homogeneous elements of degrees `i` and `j` is the homogeneous element of
degree `i + j` given by the multiplication `L^{⊗ i} ⊗ L^{⊗ j} → L^{⊗ (i + j)}`. -/
theorem incl_mul {W : X.Opens} (i j : ℤ) (x : Γ(pow L i, W)) (y : Γ(pow L j, W)) :
    incl i x * incl j y = incl (i + j) (((situation L).laurentAlgebra.mul i j).app (op W) x y) :=
  (laurent L).incl_mul_incl i j x y

/-- The inclusion of the degree-`k` sections is additive. -/
theorem incl_add {W : X.Opens} (k : ℤ) (x y : Γ(pow L k, W)) :
    incl k (x + y) = incl k x + incl k y :=
  (laurent L).incl_add k x y

/-- The inclusion of the degree-`k` sections commutes with subtraction. -/
theorem incl_sub {W : X.Opens} (k : ℤ) (x y : Γ(pow L k, W)) :
    incl k (x - y) = incl k x - incl k y :=
  map_sub (DirectSum.of (fun i => ((pow L i).val.obj (op W) : Type u)) k) x y

/-- The zero section of degree `k` maps to zero in the Laurent ring. -/
theorem incl_zero' {W : X.Opens} (k : ℤ) : incl (L := L) (W := W) k 0 = 0 :=
  (laurent L).incl_zero k

/-- The image of `f • y` is the product of the function `f` with the image of `y`. -/
theorem incl_smul {W : X.Opens} (k : ℤ) (f : Γ(X, W)) (y : Γ(pow L k, W)) :
    incl k (f • y) = alg L W f * incl k y := by
  have h := (laurent L).smul_mul_eq (X := op W) f 1 ((laurent L).incl k y)
  rw [one_mul] at h
  exact ((laurent L).incl_smul (X := op W) k f y).trans h.symm

/-- Restricting a homogeneous element is restricting the underlying section. -/
theorem res_incl {W W' : X.Opens} (h : W' ≤ W) (k : ℤ) (y : Γ(pow L k, W)) :
    res h (incl k y) = incl k (pres h y) :=
  (laurent L).totalRestrict_incl (homOfLE h).op k y

/-- Restricting a function in the Laurent ring is restricting the function. -/
theorem res_alg {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) :
    res h (alg L W f) = alg L W' (TopCat.Presheaf.restrictOpen f W' h) :=
  (laurent L).structureMap_naturality _ f

/-- Restriction commutes with natural powers. -/
theorem res_pow {W W' : X.Opens} (h : W' ≤ W) (a : LRing L W) (k : ℕ) :
    res h (a ^ k) = res h a ^ k :=
  map_pow (res h) a k

/-- The restriction of `f · a^k` is the restriction of `f` times the `k`th power of the
restriction of `a`. -/
theorem res_alg_mul_pow {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) (a : LRing L W) (k : ℕ) :
    res h (alg L W f * a ^ k) = alg L W' (TopCat.Presheaf.restrictOpen f W' h) * res h a ^ k := by
  rw [map_mul, res_pow, res_alg]

/-- Restricting twice is restricting once, to the smallest open. -/
theorem res_res {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') (a : LRing L W) :
    res h' (res h a) = res (h'.trans h) a :=
  ((laurent L).totalRestrict_comp _ _ a).symm

/-- A degree-zero section is a function: the zeroth tensor power is the structure sheaf. -/
theorem incl_zero_eq_alg {W : X.Opens} (y : Γ(X, W)) :
    incl (L := L) 0 (show Γ(pow L 0, W) from y) = alg L W y := by
  have h1 : (show Γ(pow L 0, W) from y) =
      y • (show Γ(pow L 0, W) from (situation L).laurentAlgebra.one.eval (op W)) := by
    change y = y * (1 : Γ(X, W))
    rw [mul_one]
  exact (congrArg _ h1).trans ((laurent L).incl_smul 0 y _)

/-- The structure map from functions to the Laurent ring is injective. -/
theorem alg_injective (W : X.Opens) : Function.Injective (alg L W) := by
  intro f g h
  rw [← incl_zero_eq_alg, ← incl_zero_eq_alg] at h
  exact incl_injective 0 h

namespace IsHom

/-- The product of homogeneous elements of degrees `i` and `j` is homogeneous of degree
`i + j`. -/
theorem mul {W : X.Opens} {i j : ℤ} {a b : LRing L W} (ha : IsHom L i a) (hb : IsHom L j b) :
    IsHom L (i + j) (a * b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨_, (incl_mul i j x y).symm⟩

/-- Homogeneity of degree `i` is homogeneity of any degree equal to `i`. -/
theorem of_eq {W : X.Opens} {i j : ℤ} {a : LRing L W} (ha : IsHom L i a) (h : i = j) :
    IsHom L j a := h ▸ ha

/-- The restriction of a homogeneous element of degree `k` is homogeneous of degree `k`. -/
theorem res {W W' : X.Opens} (h : W' ≤ W) {k : ℤ} {a : LRing L W} (ha : IsHom L k a) :
    IsHom L k (TwistedThickeningLift.res h a) := by
  obtain ⟨y, rfl⟩ := ha
  exact ⟨_, (res_incl h k y).symm⟩

/-- A function times a homogeneous element of degree `k` is homogeneous of degree `k`. -/
theorem alg_mul {W : X.Opens} {k : ℤ} {a : LRing L W} (ha : IsHom L k a) (f : Γ(X, W)) :
    IsHom L k (alg L W f * a) := by
  obtain ⟨y, rfl⟩ := ha
  exact ⟨f • y, incl_smul k f y⟩

/-- The unit of the Laurent ring is homogeneous of degree zero. -/
theorem one (W : X.Opens) : IsHom L 0 (1 : LRing L W) :=
  ⟨_, ((laurent L).one_eq_incl (op W)).symm⟩

/-- A function is homogeneous of degree zero. -/
theorem alg' (W : X.Opens) (f : Γ(X, W)) : IsHom L 0 (TwistedThickeningLift.alg L W f) := by
  simpa using (one W).alg_mul f

/-- The sum of homogeneous elements of degree `k` is homogeneous of degree `k`. -/
theorem add {W : X.Opens} {k : ℤ} {a b : LRing L W} (ha : IsHom L k a) (hb : IsHom L k b) :
    IsHom L k (a + b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, incl_add k x y⟩

/-- The negative of a homogeneous element of degree `k` is homogeneous of degree `k`. -/
theorem neg {W : X.Opens} {k : ℤ} {a : LRing L W} (ha : IsHom L k a) : IsHom L k (-a) := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨-x, map_neg (DirectSum.of (fun i => ((pow L i).val.obj (op W) : Type u)) k) x⟩

/-- The difference of homogeneous elements of degree `k` is homogeneous of degree `k`. -/
theorem sub {W : X.Opens} {k : ℤ} {a b : LRing L W} (ha : IsHom L k a) (hb : IsHom L k b) :
    IsHom L k (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

/-- The `n`th power of a homogeneous element of degree `k` is homogeneous of degree `n * k`. -/
theorem pow {W : X.Opens} {k : ℤ} {a : LRing L W} (ha : IsHom L k a) (n : ℕ) :
    IsHom L (n * k) (a ^ n) := by
  induction n with
  | zero => simpa using one W
  | succ n ih => exact (ih.mul ha).of_eq (by push_cast; ring)

/-- A degree-zero element is a function. -/
theorem exists_alg {W : X.Opens} {a : LRing L W} (ha : IsHom L 0 a) :
    ∃ f : Γ(X, W), a = TwistedThickeningLift.alg L W f := by
  obtain ⟨y, rfl⟩ := ha
  exact ⟨y, incl_zero_eq_alg (L := L) y⟩

end IsHom

/-! ### Charts -/

variable (L) in
/-- **A chart of `L` over `U`**: a homogeneous unit of degree one of the Laurent ring over `U`
whose inverse is homogeneous of degree `-1`. -/
def IsChart {U : X.Opens} (ε : LRing L U) : Prop :=
  IsHom L 1 ε ∧ ∃ ε' : LRing L U, IsHom L (-1) ε' ∧ ε * ε' = 1

namespace IsChart

/-- The restriction of a chart of `L` over `U` to an open `W ⊆ U` is a chart over `W`. -/
theorem res {U W : X.Opens} (h : W ≤ U) {ε : LRing L U} (hε : IsChart L ε) :
    IsChart L (TwistedThickeningLift.res h ε) := by
  obtain ⟨h1, ε', h2, h3⟩ := hε
  refine ⟨h1.res h, _, h2.res h, ?_⟩
  rw [← map_mul, h3, map_one]

/-- **Every homogeneous element of degree `k ≥ 0` over a chart is a function times `ε^k`.** -/
theorem exists_eq {U : X.Opens} {ε : LRing L U} (hε : IsChart L ε) {k : ℕ} {a : LRing L U}
    (ha : IsHom L k a) : ∃ f : Γ(X, U), a = alg L U f * ε ^ k := by
  obtain ⟨-, ε', h2, h3⟩ := hε
  obtain ⟨f, hf⟩ := ((ha.mul (h2.pow k)).of_eq (by ring)).exists_alg
  refine ⟨f, ?_⟩
  rw [← hf, mul_assoc, ← mul_pow, mul_comm ε' ε, h3, one_pow, mul_one]

/-- **The function of a chart decomposition is unique.** -/
theorem eq_of_eq {U : X.Opens} {ε : LRing L U} (hε : IsChart L ε) {k : ℕ} {f g : Γ(X, U)}
    (h : alg L U f * ε ^ k = alg L U g * ε ^ k) : f = g := by
  obtain ⟨-, ε', -, h3⟩ := hε
  apply alg_injective (L := L) U
  simpa only [mul_assoc, ← mul_pow, h3, one_pow, mul_one] using congrArg (· * ε' ^ k) h

/-- If `f · ε^k = 0` for a chart `ε`, then `f = 0`. -/
theorem alg_mul_pow_eq_zero {U : X.Opens} {ε : LRing L U} (hε : IsChart L ε) {k : ℕ}
    {f : Γ(X, U)} (h : alg L U f * ε ^ k = 0) : f = 0 :=
  hε.eq_of_eq (k := k) (by rw [h, map_zero, zero_mul])

/-- For a chart `ε`, some section of `L^{⊗ k}` has image `ε^k` in the Laurent ring. -/
theorem exists_pow_section {U : X.Opens} {ε : LRing L U} (hε : IsChart L ε) (k : ℕ) :
    ∃ E : Γ(pow L k, U), incl k E = ε ^ k :=
  (hε.1.pow k).of_eq (by ring)

end IsChart

/-! ### The nonvanishing locus in a chart -/

/-- Every integer tensor power of an invertible module is invertible. -/
instance isInvertibleModule_pow (k : ℤ) : IsInvertibleModule X (pow L k) :=
  (situation L).isInvertible_tensorPower k

/-- In a chart, every homogeneous section of degree `k ≥ 0` is a function times the section
representing `ε^k`. -/
theorem IsChart.eq_smul {U : X.Opens} {ε : LRing L U} (hε : IsChart L ε) {k : ℕ}
    {E : Γ(pow L k, U)} (hE : incl k E = ε ^ k) (y : Γ(pow L k, U)) :
    ∃ g : Γ(X, U), y = g • E := by
  obtain ⟨g, hg⟩ := hε.exists_eq (k := k) ⟨y, rfl⟩
  refine ⟨g, incl_injective (L := L) k ?_⟩
  rw [incl_smul, hE, hg]

/-- **The nonvanishing locus of `f · ε^k` is the basic open of `f`**, for a chart `ε` of `L`
over `U`. -/
theorem IsChart.nonvanishingLocusOn_eq {U : X.Opens} {ε : LRing L U} (hε : IsChart L ε) (k : ℕ)
    {y : Γ(pow L k, U)} {f : Γ(X, U)} (hy : incl k y = alg L U f * ε ^ k) :
    Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn (pow L k) U y =
      (X.basicOpen f : Set X) := by
  obtain ⟨E, hE⟩ := hε.exists_pow_section k
  have hyE : y = f • E := incl_injective (L := L) k (by rw [incl_smul, hE, hy])
  ext p
  constructor
  · rintro ⟨hp, hnot⟩
    refine (Scheme.mem_basicOpen X f p hp).mpr ?_
    by_contra hunit
    apply hnot
    rw [hyE, Stacks.ModuleStalk.germ_smul]
    exact (Stacks.ModuleStalk.smul_mem_maximalSmul_iff _ _).mpr (Or.inl hunit)
  · intro hp
    have hpU : p ∈ U := X.basicOpen_le f hp
    refine ⟨hpU, ?_⟩
    have hgen : ∀ w : TopCat.Presheaf.stalk (C := Ab.{u}) (pow L k).presheaf p,
        ∃ r : X.presheaf.stalk p, w = r • ((pow L k).presheaf.germ U p hpU).hom E := by
      intro w
      obtain ⟨V, hVU, hpV, z, hz⟩ := TopCat.Presheaf.exists_le_germ_eq (pow L k).presheaf w hpU
      have hEV : incl k (pres hVU E) = (TwistedThickeningLift.res hVU ε) ^ k := by
        rw [← res_incl, hE, map_pow]
      obtain ⟨g, hg⟩ := (hε.res hVU).eq_smul hEV z
      refine ⟨(X.presheaf.germ V p hpV).hom g, ?_⟩
      rw [← hz, hg, Stacks.ModuleStalk.germ_smul]
      congr 1
      exact TopCat.Presheaf.germ_res_apply (pow L k).presheaf (homOfLE hVU) p hpV E
    have hE' := Stacks.SectionProduct.notMem_maximalSmul_of_generates (pow L k) p hgen
    rw [hyE, Stacks.ModuleStalk.germ_smul]
    exact fun hmem => ((Stacks.ModuleStalk.smul_mem_maximalSmul_iff _ _).mp hmem).elim
      (· ((Scheme.mem_basicOpen X f p hpU).mp hp)) hE'

/-! ### Every point lies in an affine chart -/

/-- **Every point of `X` lies in an affine open carrying a chart of `L`.** -/
theorem exists_isAffineOpen_isChart (p : X) :
    ∃ U : X.Opens, p ∈ U ∧ IsAffineOpen U ∧ ∃ ε : LRing L U, IsChart L ε := by
  classical
  let D := situation L
  let μ := D.laurentMulPresheaf 1 (-1)
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map μ) := D.isLocallySurjective_laurentMulPresheaf 1 (-1)
  let s : ToType (((PresheafOfModules.toPresheaf _).obj (D.laurentAlgebra.piece (1 + -1)).val).obj
      (op ⊤)) := ((1 : Γ(X, ⊤)) : (D.laurentAlgebra.piece (1 + -1)).val.obj (op ⊤))
  obtain ⟨V, g, ⟨t, ht⟩, hpV⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map μ) s p trivial
  let F : (PresheafOfModules.tensorObj (D.laurentAlgebra.piece 1).val
      (D.laurentAlgebra.piece (-1)).val).obj (op V) →+ X.presheaf.stalk p :=
    { toFun := fun t' => (X.presheaf.germ V p hpV).hom
        (PresheafOfModules.Hom.app μ (op V) t' : Γ(X, V))
      map_zero' := by
        rw [map_zero]
        exact map_zero (X.presheaf.germ V p hpV).hom
      map_add' := fun x y => by
        rw [map_add]
        exact map_add (X.presheaf.germ V p hpV).hom _ _ }
  have key : ∀ t', IsUnit (F t') →
      ∃ (a : Γ(pow L 1, V)) (b : Γ(pow L (-1), V)),
        IsUnit ((X.presheaf.germ V p hpV).hom
          ((D.laurentAlgebra.mul 1 (-1)).app (op V) a b : Γ(X, V))) := by
    intro t'
    induction t' using TensorProduct.inductionOn with
    | tmul a b => exact fun h => ⟨a, b, h⟩
    | add x y hx hy =>
      intro h
      have h' : IsUnit (F x + F y) := by
        convert h using 1
        exact (F.map_add x y).symm
      exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add h').elim hx hy
  have h1 : IsUnit (F t) := by
    have : (PresheafOfModules.Hom.app μ (op V) t : Γ(X, V)) = (1 : Γ(X, V)) :=
      ht.trans (map_one (X.presheaf.map g.op).hom)
    change IsUnit ((X.presheaf.germ V p hpV).hom (PresheafOfModules.Hom.app μ (op V) t : Γ(X, V)))
    rw [this, map_one]
    exact isUnit_one
  obtain ⟨a, b, hab⟩ := key t h1
  let c : Γ(X, V) := ((D.laurentAlgebra.mul 1 (-1)).app (op V) a b : Γ(X, V))
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, hUc⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    ((Scheme.mem_basicOpen X c p hpV).mpr hab) (X.basicOpen c).isOpen
  have hUc' : U ≤ X.basicOpen c := hUc
  have hUV : U ≤ V := hUc'.trans (X.basicOpen_le c)
  have hcU : IsUnit ((X.presheaf.map (homOfLE hUV).op).hom c) := by
    have h4 : (X.presheaf.map (homOfLE hUV).op).hom c = (X.presheaf.map (homOfLE hUc').op).hom
        ((X.presheaf.map (homOfLE (X.basicOpen_le c)).op).hom c) := by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [h4]
    exact (X.toRingedSpace.isUnit_res_basicOpen c).map (X.presheaf.map (homOfLE hUc').op).hom
  obtain ⟨cu, hcu⟩ := hcU
  refine ⟨U, hpU, hU, TwistedThickeningLift.res hUV (incl 1 a), ⟨_, (res_incl hUV 1 a).symm⟩,
    alg L U (↑cu⁻¹ : Γ(X, U)) * TwistedThickeningLift.res hUV (incl (-1) b),
    ((IsHom.res hUV ⟨b, rfl⟩).alg_mul _), ?_⟩
  rw [mul_left_comm, ← map_mul, incl_mul]
  have h4 : incl (L := L) (W := V) (1 + -1) ((D.laurentAlgebra.mul 1 (-1)).app (op V) a b) =
      alg L V c := incl_zero_eq_alg (L := L) c
  rw [h4, res_alg]
  change alg L U (↑cu⁻¹ : Γ(X, U)) * alg L U ((X.presheaf.map (homOfLE hUV).op).hom c) = 1
  rw [← map_mul, ← hcu, Units.inv_mul, map_one]

end Stacks.TwistedThickeningLift

end
