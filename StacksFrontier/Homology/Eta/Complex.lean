module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.Algebra.Homology.Eta
public import StacksFrontier.Homology.Eta.Cohomology
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.LaurentAway
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Berthelot--Ogus eta complex

For an element `f` of a commutative ring and a cochain complex whose terms are
`f`-torsion-free, this file defines the degreewise submodules

`(η_f C)^i = {x ∈ f^i C^i | d x ∈ f^(i+1) C^(i+1)}`

inside the localization at the powers of `f`.  It also records the coherent complex,
map, homotopy, and quotient-by-`f` constructions.

## Main definitions

* `EtaPow.Loc`: the localization `M_f`.
* `EtaComplex.term`: the degree-`i` term of `η_f C`.
* `EtaComplex.etaObject`: the eta complex.
* `EtaComplex.etaMap`: the induced map of eta complexes.
* `EtaComplex.etaHomotopy`: the induced homotopy.
* `EtaComplex.etaFunctor`: the endofunctor on complexes with `f`-torsion-free terms.
* `EtaComplex.etaHomotopyFunctor`: the induced endofunctor on their homotopy category.
* `EtaComplex.quotientObject`: the complex `η_f C / f η_f C`.

## Main results

The differential and map equations, the identity and composition laws, and the
homotopy restriction characterize the constructions. The quotient differential is
induced by the eta differential.

## Implementation notes

All powers, including negative powers, are taken after localization, where `f` is a
unit. The localized-power terms reuse `EtaPow.fpowSub` and `EtaPow.fetaTerm`. The
construction itself works for any `f` and any complex; when the source complex has
`f`-torsion-free terms, its terms embed in the localization as in the source. The
homotopy category of these complexes is realized as a full subcategory of the
homotopy category of all complexes of `A`-modules.

## References

* [Berthelot--Ogus, *Notes on crystalline cohomology*, Section 8][Berthelot-Ogus]
* [Bhatt--Morrow--Scholze, *Integral p-adic Hodge theory*, Section 6][BMS]
* [Stacks, Section 15.95 (tag 0F7N)]
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped nonZeroDivisors

namespace EtaPow

/-! ## Supporting vocabulary for the décalage at the powers of one element

Further API for `EtaPow.fpowSub` and `EtaPow.fetaTerm`: the localization `EtaPow.Loc`, the
cancellation of multiplication by `f^i`, the conversion of the plain "no nonzero `f`-torsion"
hypothesis into `IsSMulRegular` (the form `EtaPow.toLoc_injective_of_isSMulRegular` takes), and
the description of the degree-`i` décalage term of a map `d : M → N` through the pairs `(m, n)`
with `d m = f • n`. -/

variable {A : Type*} [CommRing A]

/-- The localization `M_f` of an `A`-module `M` at the powers of `f`. -/
abbrev Loc (f : A) (M : Type*) [AddCommGroup M] [Module A M] :=
  LocalizedModule (Submonoid.powers f) M

variable {f : A} {M : Type*} [AddCommGroup M] [Module A M]

/-- The unit `f` of `A_f` acts on `M_f` by the `A`-scalar `f`. -/
theorem fUnit_units_smul (x : Loc f M) : (Stacks.GradedLaurent.awayUnit f) • x = f • x := by
  rw [Units.smul_def]
  exact fUnit_smul x

/-- Multiplication by `f^i` is injective on `M_f`; it is the automorphism
`Eta.zpowEquiv`. -/
theorem fUnit_zpow_smul_injective (i : ℤ) {x y : Loc f M}
    (h : (Stacks.GradedLaurent.awayUnit f ^ i) • x = (Stacks.GradedLaurent.awayUnit f ^ i) • y) :
    x = y :=
  Eta.zpowEquiv_injective (Submonoid.powers f) (Stacks.GradedLaurent.awayUnit f) i h

/-- On a module over a commutative ring, `f` acts regularly as soon as it kills no
nonzero element. -/
theorem isSMulRegular_of_smul_eq_zero (h : ∀ x : M, f • x = 0 → x = 0) :
    IsSMulRegular M f := fun x y hxy => by
  have hxy' : f • x = f • y := hxy
  rw [← sub_eq_zero]
  exact h _ (by rw [smul_sub, hxy', sub_self])

/-- If `f` acts regularly on `M`, then `m ↦ f^i • ι m` is injective. -/
lemma fpowMap_injective
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (f : A) (hf : IsSMulRegular M f) (i : ℤ) :
    Function.Injective (fpowMap f M i) :=
  (Eta.zpowEquiv (Submonoid.powers f) M (Stacks.GradedLaurent.awayUnit f) i).injective.comp
    (toLoc_injective_of_isSMulRegular hf)

/-- If `f` acts regularly on `M`, then `m ↦ f^i • ι m` identifies `M` with the submodule
`f^i M ⊆ M_f`. -/
def fpowEquiv
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (f : A) (hf : IsSMulRegular M f) (i : ℤ) : M ≃ₗ[A] fpowSub f M i :=
  (LinearEquiv.ofInjective (fpowMap f M i) (fpowMap_injective f hf i)).trans
    (LinearEquiv.ofEq _ _ (fpowSub_eq_range i).symm)

/-- `fpowEquiv f hf i` sends `m` to `f^i • ι m`. -/
lemma fpowEquiv_apply
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (f : A) (hf : IsSMulRegular M f) (i : ℤ) (m : M) :
    (fpowEquiv f hf i m : Loc f M) = fpowMap f M i m := rfl

/-- `f^{i+1} • ι m = f^i • ι (f • m)`. -/
lemma fpowMap_succ
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (f : A) (i : ℤ) (m : M) :
    fpowMap f M (i + 1) m = fpowMap f M i (f • m) := by
  simp only [fpowMap_apply, ← fUnit_zpow_one_smul_toLoc, fUnit_zpow_smul_smul]

/-- The `A`-linear map `(m, n) ↦ d m - f • n` on `M × N`; its kernel consists of the pairs
with `d m = f • n`. -/
abbrev graphMap
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : A) (d : M →ₗ[A] N) : M × N →ₗ[A] N :=
  d.comp (LinearMap.fst A M N) - f • LinearMap.snd A M N

/-- If `f` acts regularly on `N`, then `f^i • ι m` lies in the degree-`i` décalage term of `d`
if and only if `d m` is divisible by `f`. -/
lemma fpowMap_mem_fetaTerm_iff
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : A) (hN : IsSMulRegular N f)
    (d : M →ₗ[A] N) (i : ℤ) (m : M) :
    fpowMap f M i m ∈ fetaTerm f d i ↔ ∃ n, d m = f • n := by
  constructor
  · intro hm
    obtain ⟨n, hn⟩ := (mem_fpowSub.mp hm.2)
    refine ⟨n, fpowMap_injective f hN i ?_⟩
    rw [← fpowMap_succ]
    simpa only [fpowMap_apply, fLoc_zpow_smul, fLoc_toLoc] using hn.symm
  · rintro ⟨n, hn⟩
    refine ⟨mem_fpowSub.mpr ⟨m, rfl⟩, mem_fpowSub.mpr ⟨n, ?_⟩⟩
    change fpowMap f N (i + 1) n = fLoc f d (fpowMap f M i m)
    simp only [fpowMap_apply, fLoc_zpow_smul, fLoc_toLoc, hn]
    rw [← fUnit_zpow_one_smul_toLoc, fUnit_zpow_smul_smul]

/-- The map `(m, n) ↦ f^i • ι m` from the pairs with `d m = f • n` to the degree-`i` décalage
term of `d`. -/
def graphToEta
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : A)
    (d : M →ₗ[A] N) (i : ℤ) : LinearMap.ker (graphMap f d) →ₗ[A] fetaTerm f d i :=
  ((fpowMap f M i).comp ((LinearMap.fst A M N).comp
    (LinearMap.ker (graphMap f d)).subtype)).codRestrict _ (by
      intro x
      have hx : d x.1.1 = f • x.1.2 := sub_eq_zero.mp x.2
      refine ⟨mem_fpowSub.mpr ⟨x.1.1, rfl⟩, mem_fpowSub.mpr ⟨x.1.2, ?_⟩⟩
      change fpowMap f N (i + 1) x.1.2 = fLoc f d (fpowMap f M i x.1.1)
      rw [fpowMap_succ]
      simp only [fpowMap_apply, fLoc_zpow_smul, fLoc_toLoc, hx])

/-- If `f` acts regularly on `N`, then `graphToEta f d i` is surjective. -/
lemma graphToEta_surjective
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : A) (hN : IsSMulRegular N f)
    (d : M →ₗ[A] N) (i : ℤ) : Function.Surjective (graphToEta f d i) := by
  intro x
  obtain ⟨m, hm⟩ := mem_fpowSub.mp x.2.1
  have hm' : fpowMap f M i m = x := hm
  obtain ⟨n, hn⟩ := (fpowMap_mem_fetaTerm_iff f hN d i m).mp (hm' ▸ x.2)
  refine ⟨⟨(m, n), sub_eq_zero.mpr hn⟩, Subtype.ext hm'⟩

/-- If `f` acts regularly on `M` and on `N`, then `graphToEta f d i` is injective. -/
lemma graphToEta_injective
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : A) (hM : IsSMulRegular M f)
    (hN : IsSMulRegular N f) (d : M →ₗ[A] N) (i : ℤ) :
    Function.Injective (graphToEta f d i) := by
  intro x y hxy
  have hm : x.1.1 = y.1.1 := fpowMap_injective f hM i (congrArg Subtype.val hxy)
  apply Subtype.ext
  apply Prod.ext hm
  apply hN
  change f • x.1.2 = f • y.1.2
  have hx : d x.1.1 = f • x.1.2 := sub_eq_zero.mp x.2
  have hy : d y.1.1 = f • y.1.2 := sub_eq_zero.mp y.2
  rw [← hx, ← hy, hm]

end EtaPow

namespace EtaComplex

universe u v

variable {A : Type u} [CommRing A]

/-! ## The eta terms and their differential -/

/-- A cochain complex of `A`-modules indexed by the integers. -/
@[ega "0 13.2.3"]
abbrev Complex (A : Type u) [CommRing A] := CochainComplex (ModuleCat.{max u v} A) ℤ

/-- The assertion that every term of `C` is `f`-torsion-free. -/
def IsTorsionFree (f : A) (C : Complex A) : Prop :=
  ∀ i (x : C.X i), f • x = 0 → x = 0

/-- The degree-`i` localized-power submodule of the Berthelot--Ogus eta complex. -/
abbrev term (f : A) (C : Complex A) (i : ℤ) :
    Submodule A (EtaPow.Loc f (C.X i)) :=
  EtaPow.fetaTerm f (C.d i (i + 1)).hom i

/-- Membership in the degree-`i` term is the localized-power condition and its
differential counterpart. -/
theorem mem_term (f : A) (C : Complex A) (i : ℤ)
    (x : EtaPow.Loc f (C.X i)) :
    x ∈ term f C i ↔
      x ∈ EtaPow.fpowSub f (C.X i) i ∧
        EtaPow.fLoc f (C.d i (i + 1)).hom x ∈
          EtaPow.fpowSub f (C.X (i + 1)) (i + 1) :=
  EtaPow.mem_fetaTerm

/-- Scalar multiplication by `f`, as an endomorphism of an `A`-module. -/
def scalarMap (f : A) (M : Type*) [AddCommGroup M] [Module A M] : M →ₗ[A] M where
  toFun x := f • x
  map_add' x y := smul_add f x y
  map_smul' a x := by simp only [RingHom.id_apply, smul_comm a f]

/-- The quotient of the degree-`i` eta term by its submodule of `f`-multiples. -/
abbrev QuotientTerm (f : A) (C : Complex A) (i : ℤ) :=
  (term f C i) ⧸ LinearMap.range (scalarMap f (term f C i))

/-- Two consecutive differentials of `C`, as linear maps, compose to zero. -/
private theorem hom_d_comp_hom_d (C : Complex A) (i : ℤ) :
    (C.d (i + 1) (i + 1 + 1)).hom ∘ₗ (C.d i (i + 1)).hom = 0 := by
  rw [← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero]

/-- The differential on the degreewise eta terms, obtained by restricting the localized
differential of `C`. Use `etaDifferential_val` to evaluate it in the localization. -/
def etaDifferential (f : A) (C : Complex A) (i : ℤ) :
    term f C i →ₗ[A] term f C (i + 1) :=
  ((EtaPow.fLoc f (C.d i (i + 1)).hom).domRestrict (term f C i)).codRestrict _ fun x ↦ by
    refine ⟨x.2.2, ?_⟩
    change EtaPow.fLoc f (C.d (i + 1) (i + 1 + 1)).hom
      (EtaPow.fLoc f (C.d i (i + 1)).hom x) ∈ EtaPow.fpowSub f (C.X (i + 1 + 1)) (i + 1 + 1)
    rw [Eta.locMap_locMap_eq_zero (Submonoid.powers f) _ _ (hom_d_comp_hom_d C i)]
    exact Submodule.zero_mem _

/-- The eta differential is the restriction of the localized differential of `C`. -/
@[simp] theorem etaDifferential_val (f : A) (C : Complex A) (i : ℤ)
    (x : term f C i) :
    ((etaDifferential f C i x : term f C (i + 1)) : EtaPow.Loc f (C.X (i + 1))) =
      EtaPow.fLoc f (C.d i (i + 1)).hom x := rfl

/-- The eta differential squares to zero. -/
theorem etaDifferential_comp (f : A) (C : Complex A) (i : ℤ)
    (x : term f C i) :
    etaDifferential f C (i + 1) (etaDifferential f C i x) = 0 :=
  Subtype.ext <| Eta.locMap_locMap_eq_zero (Submonoid.powers f)
    (C.d i (i + 1)).hom (C.d (i + 1) (i + 1 + 1)).hom (hom_d_comp_hom_d C i) x

/-- The eta complex with degree-`i` term `term f C i` and differential
`etaDifferential f C i`. Use `etaObject_d` for its adjacent differential. -/
def etaObject (f : A) (C : Complex A) : Complex A where
  X i := ModuleCat.of A (term f C i)
  d i j := if h : i + 1 = j then
      ModuleCat.ofHom (etaDifferential f C i) ≫
        eqToHom (congrArg (fun n => ModuleCat.of A (term f C n)) h)
    else 0
  shape i j hij := by
    change ¬i + 1 = j at hij
    simp [hij]
  d_comp_d' i j k hij hjk := by
    subst j
    subst k
    rw [dite_eq_left (by trivial), dite_eq_left (by trivial)]
    simp only [eqToHom_refl, Category.comp_id]
    apply ModuleCat.hom_ext
    ext x
    exact congrArg Subtype.val (etaDifferential_comp f C i x)

/-- The differential of `etaObject f C` from degree `i` to degree `i + 1`. -/
@[simp] theorem etaObject_d (f : A) (C : Complex A) (i : ℤ) :
    (etaObject f C).d i (i + 1) = ModuleCat.ofHom (etaDifferential f C i) := by
  simp [etaObject]

/-! ## Localized maps -/

/-- Localizing linear maps at the powers of `f` is compatible with composition. -/
theorem localizedMap_comp_apply (f : A) {M N P : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (g : M →ₗ[A] N) (k : N →ₗ[A] P)
    (x : EtaPow.Loc f M) :
    EtaPow.fLoc f k (EtaPow.fLoc f g x) = EtaPow.fLoc f (k ∘ₗ g) x := by
  induction x using LocalizedModule.induction_on with
  | h m s => simp only [Eta.locMap_mk, LinearMap.coe_comp, Function.comp_apply]

/-- The localization of the identity is the identity. -/
theorem localizedMap_id_apply (f : A) {M : Type*}
    [AddCommGroup M] [Module A M] (x : EtaPow.Loc f M) :
    EtaPow.fLoc f LinearMap.id x = x := by
  induction x using LocalizedModule.induction_on with
  | h m s => simp only [Eta.locMap_mk, LinearMap.id_coe, id_eq]

/-- The localization of a linear map `g : M → N` carries `f^i M` into `f^i N`. -/
theorem localizedMap_mem_power (f : A) {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (g : M →ₗ[A] N) (i : ℤ) {x : EtaPow.Loc f M}
    (hx : x ∈ EtaPow.fpowSub f M i) :
    EtaPow.fLoc f g x ∈ EtaPow.fpowSub f N i := by
  rw [EtaPow.mem_fpowSub] at hx ⊢
  obtain ⟨m, rfl⟩ := hx
  refine ⟨g m, ?_⟩
  rw [Eta.locMap_units_smul, EtaPow.fLoc_toLoc]

/-! ## Maps of eta complexes -/

/-- The degree-`i` map on eta terms induced by a complex map `g`.
Use `etaMapLinear_val` to evaluate it in the localization. -/
def etaMapLinear (f : A) {C D : Complex A} (g : C ⟶ D) (i : ℤ) :
    term f C i →ₗ[A] term f D i :=
  ((EtaPow.fLoc f (g.f i).hom).domRestrict (term f C i)).codRestrict _ fun x ↦ by
    refine ⟨localizedMap_mem_power f _ i x.2.1, ?_⟩
    have comm := g.comm i (i + 1)
    have comm' : (D.d i (i + 1)).hom ∘ₗ (g.f i).hom =
        (g.f (i + 1)).hom ∘ₗ (C.d i (i + 1)).hom := by
      ext y
      simpa only [ModuleCat.hom_comp] using ConcreteCategory.congr_hom comm y
    change EtaPow.fLoc f (D.d i (i + 1)).hom
      (EtaPow.fLoc f (g.f i).hom x) ∈ EtaPow.fpowSub f (D.X (i + 1)) (i + 1)
    rw [localizedMap_comp_apply, comm', ← localizedMap_comp_apply]
    exact localizedMap_mem_power f _ (i + 1) x.2.2

/-- The degree-`i` eta map is the restriction of the localized `g.f i`. -/
@[simp] theorem etaMapLinear_val (f : A) {C D : Complex A} (g : C ⟶ D)
    (i : ℤ) (x : term f C i) :
    ((etaMapLinear f g i x : term f D i) : EtaPow.Loc f (D.X i)) =
      EtaPow.fLoc f (g.f i).hom x := rfl

/-- The map of eta complexes induced by `g`. Its components are given by
`etaMap_f`; identity and composition are `etaMap_id` and `etaMap_comp`. -/
def etaMap (f : A) {C D : Complex A} (g : C ⟶ D) :
    etaObject f C ⟶ etaObject f D where
  f i := ModuleCat.ofHom (etaMapLinear f g i)
  comm' i j hij := by
    subst j
    rw [etaObject_d, etaObject_d]
    apply ModuleCat.hom_ext
    ext x
    change term f C i at x
    change etaDifferential f D i (etaMapLinear f g i x) =
      etaMapLinear f g (i + 1) (etaDifferential f C i x)
    apply Subtype.ext
    rw [etaMapLinear_val, etaDifferential_val, etaDifferential_val, etaMapLinear_val,
      localizedMap_comp_apply, localizedMap_comp_apply]
    congr 2
    ext y
    exact ConcreteCategory.congr_hom (g.comm i (i + 1)) y

/-- The degree-`i` component of `etaMap f g`. -/
@[simp] theorem etaMap_f (f : A) {C D : Complex A} (g : C ⟶ D) (i : ℤ) :
    (etaMap f g).f i = ModuleCat.ofHom (etaMapLinear f g i) := rfl

/-- The terms of the eta complex are `f`-torsion-free, since they lie in localizations at the
powers of `f`. -/
theorem etaObject_torsionFree (f : A) (C : Complex A) :
    IsTorsionFree f (etaObject f C) := fun _ _ hx =>
  Subtype.ext <| LocalizedModule.eq_zero_of_smul_eq_zero f (Submonoid.mem_powers f) _
    (congrArg Subtype.val hx)

/-- The eta construction preserves identities. -/
theorem etaMap_id (f : A) (C : Complex A) :
    etaMap f (𝟙 C) = 𝟙 (etaObject f C) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext x
  change term f C i at x
  apply Subtype.ext
  change EtaPow.fLoc f (LinearMap.id : (C.X i) →ₗ[A] (C.X i)) (x : term f C i) = x
  simpa only [HomologicalComplex.id_f, ModuleCat.hom_id] using
    localizedMap_id_apply f (x : EtaPow.Loc f (C.X i))

/-- The eta construction preserves composition. -/
theorem etaMap_comp (f : A) {C D E : Complex A} (g : C ⟶ D) (k : D ⟶ E) :
    etaMap f (g ≫ k) = etaMap f g ≫ etaMap f k := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext x
  change term f C i at x
  apply Subtype.ext
  change EtaPow.fLoc f ((g ≫ k).f i).hom (x : term f C i) =
    EtaPow.fLoc f (k.f i).hom (EtaPow.fLoc f (g.f i).hom x)
  rw [localizedMap_comp_apply]
  rfl

/-- An isomorphism of complexes of modules induces one of their décalages. -/
def etaObjectIso (f : A) {C E : Complex.{u, v} A} (e : C ≅ E) :
    etaObject f C ≅ etaObject f E where
  hom := etaMap f e.hom
  inv := etaMap f e.inv
  hom_inv_id := by rw [← etaMap_comp, e.hom_inv_id, etaMap_id]
  inv_hom_id := by rw [← etaMap_comp, e.inv_hom_id, etaMap_id]

/-- The full subcategory of complexes whose terms are `f`-torsion-free. -/
def torsionFreeComplex (f : A) : ObjectProperty (Complex.{u,v} A) :=
  fun C => IsTorsionFree f C

/-- Eta is an endofunctor on complexes with `f`-torsion-free terms. -/
def etaFunctor (f : A) : (torsionFreeComplex.{u,v} f).FullSubcategory ⥤
    (torsionFreeComplex.{u,v} f).FullSubcategory where
  obj C := ⟨etaObject f C.obj, etaObject_torsionFree f C.obj⟩
  map g := ObjectProperty.homMk (etaMap f g.hom)
  map_id C := ObjectProperty.hom_ext _ (etaMap_id f C.obj)
  map_comp g k := ObjectProperty.hom_ext _ (etaMap_comp f g.hom k.hom)

/-! ## Homotopies -/

/-- `f^{i+1} M ⊆ f^i M` inside `M_f`. -/
theorem powerSubmodule_step (f : A) {M : Type*} [AddCommGroup M] [Module A M]
    (i : ℤ) {x : EtaPow.Loc f M} (hx : x ∈ EtaPow.fpowSub f M (i + 1)) :
    x ∈ EtaPow.fpowSub f M i := by
  obtain ⟨m, rfl⟩ := EtaPow.mem_fpowSub.mp hx
  apply EtaPow.mem_fpowSub.mpr
  refine ⟨f • m, ?_⟩
  rw [map_smul, ← EtaPow.fUnit_units_smul, smul_smul, zpow_add, zpow_one]

/-- Localizing linear maps at the powers of `f` is additive. -/
theorem localizedMap_add_apply (f : A) {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (g k : M →ₗ[A] N) (x : EtaPow.Loc f M) :
    EtaPow.fLoc f (g + k) x = EtaPow.fLoc f g x + EtaPow.fLoc f k x := by
  simp [EtaPow.fLoc, Eta.locMap, LocalizedModule.map, map_add, LinearMap.add_apply]

/-- The localization of the zero map is zero. -/
theorem localizedMap_zero_apply (f : A) {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (x : EtaPow.Loc f M) :
    EtaPow.fLoc f (0 : M →ₗ[A] N) x = 0 := by
  induction x using LocalizedModule.induction_on with
  | h m s => simp [Eta.locMap_mk]

/-- The homotopy equation `g = h ∘ d + d ∘ h + k` in degree `i`, after localization. -/
theorem localizedMap_homotopy (f : A) {C D : Complex A} {g k : C ⟶ D}
    (h : Homotopy g k) (i : ℤ) (x : EtaPow.Loc f (C.X i)) :
    EtaPow.fLoc f (g.f i).hom x =
      EtaPow.fLoc f (h.hom (i + 1) i).hom
        (EtaPow.fLoc f (C.d i (i + 1)).hom x) +
      EtaPow.fLoc f (D.d (i - 1) i).hom
        (EtaPow.fLoc f (h.hom i (i - 1)).hom x) +
      EtaPow.fLoc f (k.f i).hom x := by
  have heq : (g.f i).hom =
      (h.hom (i + 1) i).hom ∘ₗ (C.d i (i + 1)).hom +
      (D.d (i - 1) i).hom ∘ₗ (h.hom i (i - 1)).hom + (k.f i).hom := by
    ext y
    have hh := ConcreteCategory.congr_hom (h.comm i) y
    have hn : (ComplexShape.up ℤ).next i = i + 1 := CochainComplex.next ℤ i
    have hp : (ComplexShape.up ℤ).prev i = i - 1 := CochainComplex.prev ℤ i
    simp only [dNext, prevD, AddMonoidHom.mk'_apply] at hh
    rw [hn, hp] at hh
    simpa only [ModuleCat.hom_add, ModuleCat.hom_comp,
      LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply] using hh
  rw [heq, localizedMap_add_apply, localizedMap_add_apply,
    ← localizedMap_comp_apply, ← localizedMap_comp_apply]

/-- The homotopy equation of `localizedMap_homotopy` in degree `j + 1`. -/
private theorem localizedMap_homotopy_succ (f : A) {C D : Complex A} {g k : C ⟶ D}
    (h : Homotopy g k) (j : ℤ) (x : EtaPow.Loc f (C.X (j + 1))) :
    EtaPow.fLoc f (g.f (j + 1)).hom x =
      EtaPow.fLoc f (h.hom (j + 1 + 1) (j + 1)).hom
        (EtaPow.fLoc f (C.d (j + 1) (j + 1 + 1)).hom x) +
      EtaPow.fLoc f (D.d j (j + 1)).hom
        (EtaPow.fLoc f (h.hom (j + 1) j).hom x) +
      EtaPow.fLoc f (k.f (j + 1)).hom x := by
  have heq := localizedMap_homotopy f h (j + 1) x
  rwa [add_sub_cancel_right] at heq

/-- The localized homotopy component `h (j + 1) j` carries the degree-`(j + 1)` eta term of `C`
into the degree-`j` eta term of `D`. -/
theorem etaHomotopy_mem (f : A) {C D : Complex A} {g k : C ⟶ D}
    (h : Homotopy g k) (j : ℤ) (x : term f C (j + 1)) :
    EtaPow.fLoc f (h.hom (j + 1) j).hom x ∈ term f D j := by
  refine ⟨powerSubmodule_step f j (localizedMap_mem_power f _ (j + 1) x.2.1), ?_⟩
  have hmem : ∀ u : C ⟶ D, EtaPow.fLoc f (u.f (j + 1)).hom x ∈
      EtaPow.fpowSub f (D.X (j + 1)) (j + 1) := fun u => localizedMap_mem_power f _ _ x.2.1
  have hd : EtaPow.fLoc f (h.hom (j + 1 + 1) (j + 1)).hom
      (EtaPow.fLoc f (C.d (j + 1) (j + 1 + 1)).hom x) ∈
      EtaPow.fpowSub f (D.X (j + 1)) (j + 1) :=
    powerSubmodule_step f (j + 1)
      (localizedMap_mem_power f _ _ x.2.2)
  change EtaPow.fLoc f (D.d j (j + 1)).hom
    (EtaPow.fLoc f (h.hom (j + 1) j).hom x) ∈
      EtaPow.fpowSub f (D.X (j + 1)) (j + 1)
  convert (Submodule.sub_mem _ (Submodule.sub_mem _ (hmem g) hd) (hmem k)) using 1
  rw [localizedMap_homotopy_succ]
  abel

/-- The degreewise restriction of a homotopy to eta terms.
Use `etaHomotopyLinear_val` for its action and `etaHomotopyLinear_comm` for the
homotopy equation. -/
def etaHomotopyLinear (f : A) {C D : Complex A} {g k : C ⟶ D}
    (h : Homotopy g k) (i j : ℤ) : term f C i →ₗ[A] term f D j := by
  by_cases hij : j + 1 = i
  · subst i
    exact ((EtaPow.fLoc f (h.hom (j + 1) j).hom).domRestrict
      (term f C (j + 1))).codRestrict _ (etaHomotopy_mem f h j)
  · exact 0

/-- The restricted homotopy is the localized homotopy component. -/
theorem etaHomotopyLinear_val (f : A) {C D : Complex A} {g k : C ⟶ D}
    (h : Homotopy g k) (i j : ℤ) (x : term f C i) :
    ((etaHomotopyLinear f h i j x : term f D j) : EtaPow.Loc f (D.X j)) =
      EtaPow.fLoc f (h.hom i j).hom x := by
  by_cases hij : j + 1 = i
  · subst i
    simp only [etaHomotopyLinear]
    rfl
  · have hz : h.hom i j = 0 := h.zero i j hij
    simp [etaHomotopyLinear, hij, hz, localizedMap_zero_apply]

/-- The degreewise restrictions of a homotopy satisfy the homotopy equation. -/
theorem etaHomotopyLinear_comm (f : A) {C D : Complex A} {g k : C ⟶ D}
    (h : Homotopy g k) (i : ℤ) :
    (etaMap f g).f i =
      dNext i (fun p q => ModuleCat.ofHom (etaHomotopyLinear f h p q)) +
      prevD i (fun p q => ModuleCat.ofHom (etaHomotopyLinear f h p q)) +
      (etaMap f k).f i := by
  generalize hj : i - 1 = j
  have hi : i = j + 1 := by omega
  subst i
  clear hj
  rw [etaMap_f, etaMap_f]
  have hn : (ComplexShape.up ℤ).next (j + 1) = j + 1 + 1 :=
    CochainComplex.next ℤ (j + 1)
  have hp : (ComplexShape.up ℤ).prev (j + 1) = j := by
    simpa only [add_sub_cancel_right] using CochainComplex.prev ℤ (j + 1)
  simp only [dNext, prevD, AddMonoidHom.mk'_apply]
  rw [hn, hp]
  rw [etaObject_d, etaObject_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change term f C (j + 1) at x
  change etaMapLinear f g (j + 1) x =
    etaHomotopyLinear f h (j + 1 + 1) (j + 1)
        (etaDifferential f C (j + 1) x) +
      etaDifferential f D j (etaHomotopyLinear f h (j + 1) j x) +
      etaMapLinear f k (j + 1) x
  apply Subtype.ext
  change ((etaMapLinear f g (j + 1) x : term f D (j + 1)) :
      EtaPow.Loc f (D.X (j + 1))) =
    (etaHomotopyLinear f h (j + 1 + 1) (j + 1)
          (etaDifferential f C (j + 1) x) : term f D (j + 1)) +
      (etaDifferential f D j (etaHomotopyLinear f h (j + 1) j x) :
        term f D (j + 1)) +
      (etaMapLinear f k (j + 1) x : term f D (j + 1))
  rw [etaMapLinear_val, etaHomotopyLinear_val, etaDifferential_val,
    etaDifferential_val, etaHomotopyLinear_val, etaMapLinear_val]
  exact localizedMap_homotopy_succ f h j x

/-- A homotopy between eta maps induced by a homotopy between the original maps.
Its components are `etaHomotopyLinear`; their equation is
`etaHomotopyLinear_comm`. -/
def etaHomotopy (f : A) {C D : Complex A} {g k : C ⟶ D}
    (h : Homotopy g k) : Homotopy (etaMap f g) (etaMap f k) where
  hom i j := ModuleCat.ofHom (etaHomotopyLinear f h i j)
  zero i j hij := by
    change ¬j + 1 = i at hij
    change ModuleCat.ofHom (etaHomotopyLinear f h i j) = 0
    simp [etaHomotopyLinear, hij]
  comm i := etaHomotopyLinear_comm f h i

/-- Eta descends to the homotopy category of cochain complexes. The construction
does not require torsion-freeness because its terms already lie in localizations. -/
def etaHomotopyFunctorAll (f : A) :
    HomotopyCategory (ModuleCat.{max u v} A) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (ModuleCat.{max u v} A) (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _
    ({ obj := etaObject f
       map := fun g => etaMap f g
       map_id := etaMap_id f
       map_comp := fun g k => etaMap_comp f g k } ⋙
      HomotopyCategory.quotient _ _) (by
        rintro C D g k ⟨h⟩
        exact HomotopyCategory.eq_of_homotopy _ _ (etaHomotopy f h))

/-- The full subcategory of the homotopy category represented by complexes
whose terms are `f`-torsion-free. Its morphisms are maps up to homotopy. -/
def torsionFreeHomotopyComplex (f : A) :
    ObjectProperty (HomotopyCategory (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) :=
  fun C => IsTorsionFree f C.as

/-- The Berthelot--Ogus eta endofunctor on the homotopy category of complexes
with `f`-torsion-free terms. -/
def etaHomotopyFunctor (f : A) :
    (torsionFreeHomotopyComplex.{u,v} f).FullSubcategory ⥤
      (torsionFreeHomotopyComplex.{u,v} f).FullSubcategory :=
  ObjectProperty.lift _
    ((torsionFreeHomotopyComplex.{u,v} f).ι ⋙ etaHomotopyFunctorAll f) (by
      rintro ⟨C, _⟩
      exact etaObject_torsionFree f C.as)

/-! ## Reduction modulo `f` -/

/-- The differential on eta terms modulo multiplication by `f`.
Use `quotientDifferential_mk` to evaluate it on a quotient class. -/
def quotientDifferential (f : A) (C : Complex A) (i : ℤ) :
    QuotientTerm f C i →ₗ[A] QuotientTerm f C (i + 1) :=
  Submodule.mapQ _ _ (etaDifferential f C i) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨etaDifferential f C i x, by
      change scalarMap f (term f C (i + 1)) (etaDifferential f C i x) =
        etaDifferential f C i (scalarMap f (term f C i) x)
      exact (map_smul _ _ _).symm⟩)

/-- The quotient differential sends the class of `x` to the class of its eta differential. -/
@[simp] theorem quotientDifferential_mk (f : A) (C : Complex A) (i : ℤ)
    (x : term f C i) :
    quotientDifferential f C i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (etaDifferential f C i x) := by
  simp [quotientDifferential]

/-- The quotient complex `η_f C / f η_f C`, with terms `QuotientTerm f C i`.
Use `quotientObject_d` for its adjacent differential and `quotientMap` for the
canonical projection from the eta complex. -/
def quotientObject (f : A) (C : Complex A) : Complex A where
  X i := ModuleCat.of A (QuotientTerm f C i)
  d i j := if h : i + 1 = j then
      ModuleCat.ofHom (quotientDifferential f C i) ≫
        eqToHom (congrArg (fun n => ModuleCat.of A (QuotientTerm f C n)) h)
    else 0
  shape i j hij := by
    change ¬i + 1 = j at hij
    simp [hij]
  d_comp_d' i j k hij hjk := by
    subst j
    subst k
    rw [dite_eq_left (by trivial), dite_eq_left (by trivial)]
    simp only [eqToHom_refl, Category.comp_id]
    apply ModuleCat.hom_ext
    ext x
    change quotientDifferential f C (i + 1) (quotientDifferential f C i
      (Submodule.Quotient.mk x)) = 0
    simp only [quotientDifferential, Submodule.mapQ_apply]
    rw [etaDifferential_comp]
    rfl

/-- The differential of `quotientObject f C` from degree `i` to degree `i + 1`. -/
@[simp] theorem quotientObject_d (f : A) (C : Complex A) (i : ℤ) :
    (quotientObject f C).d i (i + 1) =
      ModuleCat.ofHom (quotientDifferential f C i) := by
  simp [quotientObject]

/-- The canonical degreewise quotient map from `η_f C` to `η_f C / f η_f C`. -/
def quotientMap (f : A) (C : Complex A) :
    etaObject f C ⟶ quotientObject f C where
  f i := ModuleCat.ofHom (Submodule.mkQ _)
  comm' i j hij := by
    subst j
    rw [etaObject_d, quotientObject_d]
    apply ModuleCat.hom_ext
    ext x
    exact (quotientDifferential_mk f C i x).symm

/-- The degree-`i` component of `quotientMap f C` sends `x` to its class. -/
@[simp] theorem quotientMap_f_apply (f : A) (C : Complex A) (i : ℤ)
    (x : term f C i) :
    (quotientMap f C).f i x = Submodule.Quotient.mk x := rfl

end EtaComplex
