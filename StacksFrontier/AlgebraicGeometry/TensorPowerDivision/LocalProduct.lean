module

public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.IntegerLaurent

/-!
# The product of two local sections of integer tensor powers, over one open

Let `X` be a scheme and `L` an invertible `𝒪_X`-module. The multiplication
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)` is an isomorphism of `𝒪_X`-modules, so it acts on the sections
over one open `W`:

`Γ(L ^⊗ n, W) × Γ(L ^⊗ m, W) ⟶ Γ(L ^⊗ (n + m), W)`.

This file studies that product: its compatibility with restriction, its associativity,
commutativity and interchange law, and its behaviour on quotients `a / t` of global sections.

## Main definitions

* `Stacks.TensorPowerDivision.localMulBilinear`: the multiplication
  `L ^⊗ n ⊗ L ^⊗ m ⟶ L ^⊗ (n + m)` as an `𝒪_X`-bilinear map of sheaves of modules.
* `Stacks.TensorPowerDivision.localMul`: the product of two sections of integer tensor powers
  over one open.

## Main results

* `Stacks.TensorPowerDivision.localValue_eq_resTop`: the local section named over `W` by a
  morphism out of the monoidal unit is the restriction of the global section it names.
* `Stacks.TensorPowerDivision.intMulMap_app_localMul`: multiplication by a global section is the
  product with its restriction.
* `Stacks.TensorPowerDivision.map_localMul` and `Stacks.TensorPowerDivision.resTop_localMul`:
  the product commutes with restriction.
* `Stacks.TensorPowerDivision.localMul_assoc_heq` and
  `Stacks.TensorPowerDivision.localMul_comm_heq`: associativity and commutativity, as
  heterogeneous equalities.
* `Stacks.TensorPowerDivision.reindex_eq_of_heq`: a heterogeneous equality between sections of
  two powers of equal degree, read as an equality after the reindexing isomorphism.
* `Stacks.TensorPowerDivision.localMul_interchange_heq`: the interchange law
  `(x y)(z w) = (x z)(y w)`.
* `Stacks.TensorPowerDivision.localMul_intDivTop`: the product of two quotients is the quotient
  of the products.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (unitIso)
open Stacks.SheafOfModules.TensorSheafification (structureSheaf structureRingPresheaf)
open Stacks.SheafOfModules.TensorPower (tensorPower mulBilinear mulBilinear_app mulBilinear_assoc
  mulBilinear_comm)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.SectionProduct (globalSection)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerTrivialize (resTop)

universe u

namespace Stacks.TensorPowerDivision

section Scheme

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- An invertible `𝒪_X`-module in the sense of `Stacks.Ample.IsInvertibleModule` is invertible
in the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
local instance schemeStacksIsInvertibleLocalProduct :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (hStruct X) L :=
  Stacks.PowerFamilyBridge.instIsInvertible X.presheaf (hStruct X) L

/-! ### The product -/

/-- The multiplication `L ^⊗ n ⊗ L ^⊗ m ⟶ L ^⊗ (n + m)` as an `𝒪_X`-bilinear map of sheaves of
modules. -/
def localMulBilinear (n m : ℤ) :
    SheafOfModules.BilinearMap (tensorPowerModule X L n) (tensorPowerModule X L m)
      (tensorPowerModule X L (n + m)) :=
  mulBilinear X.presheaf (hStruct X) L n m

/-- The product of a section of `L ^⊗ n` over `W` with a section of `L ^⊗ m` over the same open
`W`, a section of `L ^⊗ (n + m)` over `W`. -/
def localMul {n m : ℤ} {W : X.Opens} (y : Γ(tensorPowerModule X L n, W))
    (z : Γ(tensorPowerModule X L m, W)) : Γ(tensorPowerModule X L (n + m), W) :=
  (localMulBilinear L n m).app (op W) y z

/-- `localMul` is the multiplication `Stacks.SheafOfModules.TensorPower.mulBilinear` evaluated
at `W`. -/
theorem localMul_eq_mulBilinear {n m : ℤ} {W : X.Opens} (y : Γ(tensorPowerModule X L n, W))
    (z : Γ(tensorPowerModule X L m, W)) :
    localMul L y z = (mulBilinear X.presheaf (hStruct X) L n m).app (op W) y z := rfl

/-! ### Restriction -/

/-- The product commutes with restriction to a smaller open, in both factors at once. -/
theorem map_localMul {n m : ℤ} {W W' : X.Opens} (i : W' ⟶ W)
    (y : Γ(tensorPowerModule X L n, W)) (z : Γ(tensorPowerModule X L m, W)) :
    (tensorPowerModule X L (n + m)).presheaf.map i.op (localMul L y z)
      = localMul L ((tensorPowerModule X L n).presheaf.map i.op y)
          ((tensorPowerModule X L m).presheaf.map i.op z) :=
  (localMulBilinear L n m).naturality i.op y z

/-- The restriction of the product of two global sections is the product of their
restrictions. -/
theorem resTop_localMul {n m : ℤ} (y : Γ(tensorPowerModule X L n, ⊤))
    (z : Γ(tensorPowerModule X L m, ⊤)) (W : X.Opens) :
    resTop (tensorPowerModule X L (n + m)) (localMul L y z) W
      = localMul L (resTop (tensorPowerModule X L n) y W)
          (resTop (tensorPowerModule X L m) z W) :=
  map_localMul L (homOfLE (le_top : W ≤ ⊤)) y z

/-! ### Multiplication by a global section is the product with its restriction -/

/-- The local section named over `W` by a morphism out of the monoidal unit is the restriction of
the global section it names. -/
theorem localValue_eq_resTop {k : ℤ} (τ : 𝟙_ X.Modules ⟶ tensorPowerModule X L k)
    (W : X.Opens) :
    ((unitIso X.presheaf (hStruct X)).inv ≫ τ).val.app (op W)
        (1 : X.presheaf.obj (op W))
      = resTop (tensorPowerModule X L k) (globalSection X _ τ) W :=
  (PresheafOfModules.sections_property
    ((tensorPowerModule X L k).val.unitHomEquiv
      ((unitIso X.presheaf (hStruct X)).inv ≫ τ).val)
    (homOfLE (le_top : W ≤ ⊤)).op).symm

/-- Multiplication `Stacks.TensorPowerDivision.intMulMap` by a global section `t` of `L ^⊗ k`,
read on a section over an arbitrary open `W`, is the product with the restriction of `t`. -/
theorem intMulMap_app_localMul {k : ℤ} (t : Γ(tensorPowerModule X L k, ⊤)) (n : ℤ)
    (W : X.Opens) (c : Γ(tensorPowerModule X L n, W)) :
    (intMulMap L (intSecOf L t) n).app W c
      = localMul L (resTop (tensorPowerModule X L k) t W) c :=
  (intMulMap_val_app L (intSecOf L t) n (op W) c).trans
    (congrArg
      (fun v => (mulBilinear X.presheaf (hStruct X) L k n).app (op W) v c)
      ((localValue_eq_resTop L (intSecOf L t) W).trans
        (congrArg (fun v => resTop (tensorPowerModule X L k) v W)
          (globalSection_intSecOf L t))))

/-! ### The coherence laws, and the transport that reads them as equalities -/

/-- Reindexing a tensor power along an equality of degrees does not move a local section, up to
heterogeneous equality. -/
theorem heq_intPowReindex {a b : ℤ} (h : a = b) {W : X.Opens}
    (x : Γ(tensorPowerModule X L a, W)) :
    HEq ((intPowReindex L h).hom.app W x) x := by
  subst h; rfl

/-- A heterogeneous equality between sections of two tensor powers of equal degree, read as an
equality after reindexing. -/
theorem reindex_eq_of_heq {a b : ℤ} (h : a = b) {W : X.Opens}
    {x : Γ(tensorPowerModule X L a, W)} {y : Γ(tensorPowerModule X L b, W)} (hxy : HEq x y) :
    (intPowReindex L h).hom.app W x = y :=
  eq_of_heq ((heq_intPowReindex L h x).trans hxy)

/-- The product is associative, as a heterogeneous equality: the two sides sit in the degrees
`(n + m) + k` and `n + (m + k)`. -/
theorem localMul_assoc_heq {n m k : ℤ} {W : X.Opens} (x : Γ(tensorPowerModule X L n, W))
    (y : Γ(tensorPowerModule X L m, W)) (z : Γ(tensorPowerModule X L k, W)) :
    HEq (localMul L (localMul L x y) z) (localMul L x (localMul L y z)) :=
  mulBilinear_assoc X.presheaf (hStruct X) L n m k (op W) x y z

/-- The product is commutative, as a heterogeneous equality: the two sides sit in the degrees
`n + m` and `m + n`. -/
theorem localMul_comm_heq {n m : ℤ} {W : X.Opens} (x : Γ(tensorPowerModule X L n, W))
    (y : Γ(tensorPowerModule X L m, W)) : HEq (localMul L x y) (localMul L y x) :=
  mulBilinear_comm X.presheaf (hStruct X) L n m (op W) x y

/-- The product respects heterogeneous equalities of both factors whose degrees are equal. -/
private theorem localMul_congr_heq {a a' b b' : ℤ} (ha : a = a') (hb : b = b') {W : X.Opens}
    {x : Γ(tensorPowerModule X L a, W)} {x' : Γ(tensorPowerModule X L a', W)}
    {z : Γ(tensorPowerModule X L b, W)} {z' : Γ(tensorPowerModule X L b', W)}
    (hx : HEq x x') (hz : HEq z z') : HEq (localMul L x z) (localMul L x' z') := by
  subst ha hb
  rw [eq_of_heq hx, eq_of_heq hz]

/-- Congruence of the product in its first variable, for a heterogeneous equality whose two
degrees are given to be equal. -/
theorem localMul_congr_heq_left {a a' b : ℤ} (hd : a = a') {W : X.Opens}
    {x : Γ(tensorPowerModule X L a, W)} {x' : Γ(tensorPowerModule X L a', W)} (hx : HEq x x')
    (z : Γ(tensorPowerModule X L b, W)) :
    HEq (localMul L x z) (localMul L x' z) :=
  localMul_congr_heq L hd rfl hx (HEq.refl z)

/-- Congruence of the product in its second variable, for a heterogeneous equality whose two
degrees are given to be equal. -/
theorem localMul_congr_heq_right {a b b' : ℤ} (hd : b = b') {W : X.Opens}
    (x : Γ(tensorPowerModule X L a, W)) {z : Γ(tensorPowerModule X L b, W)}
    {z' : Γ(tensorPowerModule X L b', W)} (hz : HEq z z') :
    HEq (localMul L x z) (localMul L x z') :=
  localMul_congr_heq L rfl hd (HEq.refl x) hz

/-- The interchange law `(x y)(z w) = (x z)(y w)`, as a heterogeneous equality: the two sides
sit in the degrees `(a + b) + (c + e)` and `(a + c) + (b + e)`. -/
theorem localMul_interchange_heq {a b c e : ℤ} {W : X.Opens}
    (x : Γ(tensorPowerModule X L a, W)) (y : Γ(tensorPowerModule X L b, W))
    (z : Γ(tensorPowerModule X L c, W)) (w : Γ(tensorPowerModule X L e, W)) :
    HEq (localMul L (localMul L x y) (localMul L z w))
      (localMul L (localMul L x z) (localMul L y w)) :=
  (localMul_assoc_heq L x y (localMul L z w)).trans <|
    (localMul_congr_heq_right L (add_assoc b c e).symm x (localMul_assoc_heq L y z w).symm).trans <|
    (localMul_congr_heq_right L (congrArg (fun v => v + e) (add_comm b c)) x
      (localMul_congr_heq_left L (add_comm b c) (localMul_comm_heq L y z) w)).trans <|
    (localMul_congr_heq_right L (add_assoc c b e) x (localMul_assoc_heq L z y w)).trans
      (localMul_assoc_heq L x z (localMul L y w)).symm

/-! ### Reindexing -/

/-- Reindexing the first factor reindexes the product. -/
theorem localMul_intPowReindex_left {a a' b : ℤ} (h : a = a') {W : X.Opens}
    (x : Γ(tensorPowerModule X L a, W)) (z : Γ(tensorPowerModule X L b, W)) :
    localMul L ((intPowReindex L h).hom.app W x) z
      = (intPowReindex L (congrArg (fun v => v + b) h)).hom.app W (localMul L x z) := by
  subst h; rfl

/-- Reindexing the second factor reindexes the product. -/
theorem localMul_intPowReindex_right {a b b' : ℤ} (h : b = b') {W : X.Opens}
    (x : Γ(tensorPowerModule X L a, W)) (z : Γ(tensorPowerModule X L b, W)) :
    localMul L x ((intPowReindex L h).hom.app W z)
      = (intPowReindex L (congrArg (fun v => a + v) h)).hom.app W (localMul L x z) := by
  subst h; rfl

/-! ### The product of two quotients -/

/-- The product `Stacks.TensorPowerDivision.intMulSections` of two global sections is their
`localMul` over the terminal open. -/
theorem localMul_top_eq_intMulSections {k n : ℤ} (t : Γ(tensorPowerModule X L k, ⊤))
    (b : Γ(tensorPowerModule X L n, ⊤)) :
    localMul L t b = intMulSections L t b :=
  (intMulSections_eq_mulBilinear L t b).symm

/-- The product of the restriction of `t` with the quotient `a / t` is the restriction of
`a`. -/
theorem localMul_resTop_intDivTop {k : ℤ} {V : X.Opens} (t : Γ(tensorPowerModule X L k, ⊤))
    (hVt : V ≤ nonvanishingOpen X (tensorPowerModule X L k) t) (n : ℤ)
    (a : Γ(tensorPowerModule X L (k + n), ⊤)) :
    localMul L (resTop (tensorPowerModule X L k) t V) (intDivTop L t hVt n a)
      = resTop (tensorPowerModule X L (k + n)) a V :=
  (intMulMap_app_localMul L t n V (intDivTop L t hVt n a)).symm.trans
    (mul_intDivTop L t hVt n a)

/-- The product of two quotients is the quotient of the products: `(a / t) · (b / s)` is
`(a b) / (t s)`, up to the reindexing `(k + n) + (k' + m) = (k + k') + (n + m)`. -/
theorem localMul_intDivTop {k k' : ℤ} {V : X.Opens} (t : Γ(tensorPowerModule X L k, ⊤))
    (hVt : V ≤ nonvanishingOpen X (tensorPowerModule X L k) t)
    (s : Γ(tensorPowerModule X L k', ⊤))
    (hVs : V ≤ nonvanishingOpen X (tensorPowerModule X L k') s)
    (hVts : V ≤ nonvanishingOpen X (tensorPowerModule X L (k + k')) (intMulSections L t s))
    (n m : ℤ) (a : Γ(tensorPowerModule X L (k + n), ⊤))
    (b : Γ(tensorPowerModule X L (k' + m), ⊤)) :
    localMul L (intDivTop L t hVt n a) (intDivTop L s hVs m b)
      = intDivTop L (intMulSections L t s) hVts (n + m)
          ((intPowReindex L
              (show (k + n) + (k' + m) = (k + k') + (n + m) by ring)).hom.app ⊤
            (intMulSections L a b)) := by
  have hshuffle : (k + n) + (k' + m) = (k + k') + (n + m) := by ring
  have hinter : (intPowReindex L hshuffle).hom.app V
        (localMul L (localMul L (resTop (tensorPowerModule X L k) t V)
            (intDivTop L t hVt n a))
          (localMul L (resTop (tensorPowerModule X L k') s V)
            (intDivTop L s hVs m b)))
      = localMul L (localMul L (resTop (tensorPowerModule X L k) t V)
            (resTop (tensorPowerModule X L k') s V))
          (localMul L (intDivTop L t hVt n a) (intDivTop L s hVs m b)) :=
    reindex_eq_of_heq L hshuffle
      (localMul_interchange_heq L (resTop (tensorPowerModule X L k) t V)
        (intDivTop L t hVt n a) (resTop (tensorPowerModule X L k') s V)
        (intDivTop L s hVs m b))
  have key : (intMulMap L (intSecOf L (intMulSections L t s)) (n + m)).app V
        (localMul L (intDivTop L t hVt n a) (intDivTop L s hVs m b))
      = resTop (tensorPowerModule X L ((k + k') + (n + m)))
          ((intPowReindex L hshuffle).hom.app ⊤ (intMulSections L a b)) V := by
    rw [intMulMap_app_localMul L (intMulSections L t s) (n + m) V _,
      ← localMul_top_eq_intMulSections L t s, resTop_localMul L t s V, ← hinter,
      localMul_resTop_intDivTop L t hVt n a, localMul_resTop_intDivTop L s hVs m b,
      ← resTop_localMul L a b V, ← Stacks.TensorPowerTrivialize.resTop_app,
      localMul_top_eq_intMulSections L a b]
  exact (intDivOf_eq_of_mul_eq L (intMulSections L t s) hVts (n + m) le_rfl key).symm

end Scheme

end Stacks.TensorPowerDivision

end
