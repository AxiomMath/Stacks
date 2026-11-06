module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCoproductSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.CechAmitsur
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sections of a presented module as a base change

Let a sheaf of modules `N` on a ringed site be presented, over an object `T`, as the cokernel of
a map `a : Q ⟶ P` between coproducts of copies of the structure sheaf, and let `h : W ⟶ T` be a
morphism to `T`.  Write `A` for the sections of the structure sheaf over `T` and `B` for those
over `W`.  This file proves that the sections of `N` over `W` are the base change along `A → B`
of its sections over `T`, from two inputs and nothing else:

* the same statement for `P` and for `Q`, which is
  `SheafOfModules.sectionsEquivFinsupp` — the sections of a coproduct of copies of the structure
  sheaf over an object with the finite subcovering property are the finitely supported families
  of sections of the structure sheaf;
* exactness of the *sections* of the presentation at `T` and at `W`: the presenting morphism is
  surjective on sections there, and over `W` a section killed by it is a value of `a`.

The second input says that the presheaf cokernel of `a` already computes the sections of `N`.
It is a statement about one presentation at one object; it mentions no base change and compares
no two objects, so it is not the conclusion in disguise.  For a covering of affines by a single
faithfully flat morphism it is degree-zero exactness of the Amitsur complex.

The proof is a diagram chase and uses from the theory of the tensor product only that a
surjection stays surjective after tensoring.  Writing `L(f)` for `LinearMap.liftBaseChange`, the
two squares

```
B ⊗[A] Q(T) → B ⊗[A] P(T) → B ⊗[A] N(T)
     ↓ L(rQ)       ↓ L(rP)        ↓ L(rN)
     Q(W)    →     P(W)    →      N(W)
```

commute, the first two verticals are bijective by the first input, and the rows are exact
enough by the second: surjectivity of `L(rN)` lifts a section of `N` over `W` to `P(W)`, pulls it
back through `L(rP)` and pushes it down; injectivity writes an element of the kernel as
`1 ⊗ b(T)` of something, moves that something into the image of `Q`, and kills it there.

No first cohomology of any complex is computed, and no flatness of `B` over `A` is used: the
presentation does the work that flat base change would otherwise be needed for.

## Main definitions

* `Module.BaseChange.baseChangeEquivOfBasis`: the base change of a module with a basis, along a
  map matching that basis with a basis of the target.
* `Module.BaseChange.baseChangeEquivOfPresentation`: **the sections of a presented module as a
  base change**, the main construction of the file.
* `SheafOfModules.tautBasis`: the tautological generators of a coproduct of copies of the
  structure sheaf as a basis of its sections over an object with the finite subcovering property.

## Main results

* `Module.BaseChange.liftBaseChange_eq_of_basis` and
  `Module.BaseChange.bijective_liftBaseChange_of_basis`: a map matching a basis of the source
  with a basis of the target exhibits the target as a base change.
* `Module.BaseChange.bijective_liftBaseChange_of_presentation`: **the base change property passes
  from the two terms of a presentation to the module it presents**, given exactness of the
  sections of the presentation.
* `Module.BaseChange.baseChangeEquivOfPresentation_one_tmul`: the equivalence carries `1 ⊗ n` to
  the restriction of `n`, which is the compatibility
  `SheafOfModules.detectsRange_of_baseChangeEquiv` asks of it.
* `Module.BaseChange.comp_baseChangeEquivOfBasis`: the equivalence for `N` and the one for `P`
  intertwine the presenting morphism with its base change, which is the remaining hypothesis of
  `SheafOfModules.detectsRange_of_baseChangeEquiv`.
* `Module.BaseChange.finsuppBaseChange_one_tmul` and
  `Module.BaseChange.mapRange_finsuppBaseChange`: **the coordinatewise form of the index-shape
  adapter.**  Restricting a combination of tautological generators acts on the coefficients
  through `Finsupp.mapRange`
  (`SheafOfModules.restrict_linearCombination_tautGen`), whereas the identification hypotheses of
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.CechAmitsur` are stated with
  `LinearMap.rTensor` against `Module.Descent.finsuppBaseChange`; these two lemmas are the
  translation, for the augmentation and for an arbitrary algebra map respectively.

## Implementation notes

The commutative rings, the module structures on the sections and the readings of the morphisms
of sheaves as maps of those modules are all taken as explicit data, as in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.H1Vanishing`: a
`SheafOfModules.{m} R` has `R : Sheaf J RingCat`, so its sections carry a ring and nothing more,
while a base change needs a commutative ring and an algebra, and on a big site of schemes those
are present only through `CategoryTheory.forget₂ CommRingCat RingCat`, which instance search does
not unfold.  Consequently the statements of this file are statements about modules, and the
identification with the sections of the structure sheaf is made once, by the caller.

`SheafOfModules.tautBasis` is the bridge from
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCoproductSections`: it
produces the basis over the ring of sections of the structure sheaf itself, and
`Module.Basis.mapCoeffs` transports it along a ring equivalence to whichever commutative ring the
caller has identified that ring with.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe w u v r t

namespace Module.BaseChange

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

section Basis

variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module B M']
  {I : Type*} (bM : Module.Basis I A M) (bM' : Module.Basis I B M')

/-- **The base change of a module with a basis.**  If `M` has an `A`-basis and `M'` a `B`-basis
on the same index type, then `M'` is the base change of `M` along `A → B`. -/
noncomputable def baseChangeEquivOfBasis : B ⊗[A] M ≃ₗ[B] M' :=
  (Algebra.TensorProduct.basis B bM).equiv bM' (Equiv.refl I)

/-- `Module.BaseChange.baseChangeEquivOfBasis` carries a basis vector to the corresponding basis
vector. -/
@[simp]
lemma baseChangeEquivOfBasis_one_tmul (i : I) :
    baseChangeEquivOfBasis bM bM' ((1 : B) ⊗ₜ[A] bM i) = bM' i := by
  rw [← Algebra.TensorProduct.basis_apply bM i]
  exact Module.Basis.equiv_apply (Algebra.TensorProduct.basis B bM) i bM' (Equiv.refl I)

variable [Module A M'] [IsScalarTower A B M']

/-- **A map matching a basis of the source with a basis of the target exhibits the target as a
base change.**  Both maps out of `B ⊗[A] M` are `B`-linear, so it is enough to compare them on
the basis `Algebra.TensorProduct.basis`. -/
@[sga "3 V 4.2" "more general"]
lemma liftBaseChange_eq_of_basis (f : M →ₗ[A] M') (hf : ∀ i, f (bM i) = bM' i) :
    f.liftBaseChange B = (baseChangeEquivOfBasis bM bM').toLinearMap :=
  (Algebra.TensorProduct.basis B bM).ext fun i ↦ by
    rw [Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul, hf i]
    exact (baseChangeEquivOfBasis_one_tmul bM bM' i).symm

/-- A map matching a basis of the source with a basis of the target has bijective base change. -/
lemma bijective_liftBaseChange_of_basis (f : M →ₗ[A] M') (hf : ∀ i, f (bM i) = bM' i) :
    Function.Bijective (f.liftBaseChange B) := by
  rw [liftBaseChange_eq_of_basis bM bM' f hf]
  exact (baseChangeEquivOfBasis bM bM').bijective

end Basis

section Presentation

variable {QT PT NT QW PW NW : Type*}
  [AddCommGroup QT] [Module A QT] [AddCommGroup PT] [Module A PT]
  [AddCommGroup NT] [Module A NT]
  [AddCommGroup QW] [Module A QW] [Module B QW] [IsScalarTower A B QW]
  [AddCommGroup PW] [Module A PW] [Module B PW] [IsScalarTower A B PW]
  [AddCommGroup NW] [Module A NW] [Module B NW] [IsScalarTower A B NW]
  (aT : QT →ₗ[A] PT) (bT : PT →ₗ[A] NT) (aW : QW →ₗ[B] PW) (bW : PW →ₗ[B] NW)
  (rQ : QT →ₗ[A] QW) (rP : PT →ₗ[A] PW) (rN : NT →ₗ[A] NW)

/-- A square of modules commuting on elements commutes after base change: the base change of a
map is determined on the pure tensors. -/
lemma liftBaseChange_comp_lTensor {M M' MW M'W : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [AddCommGroup MW] [Module A MW] [Module B MW]
    [IsScalarTower A B MW] [AddCommGroup M'W] [Module A M'W] [Module B M'W]
    [IsScalarTower A B M'W] (f : M →ₗ[A] M') (fW : MW →ₗ[B] M'W) (rM : M →ₗ[A] MW)
    (rM' : M' →ₗ[A] M'W) (hsq : ∀ m, rM' (f m) = fW (rM m)) (x : B ⊗[A] M) :
    rM'.liftBaseChange B (LinearMap.lTensor B f x) = fW (rM.liftBaseChange B x) := by
  induction x with
  | tmul b m =>
    rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
      map_smul, hsq m]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **The base change property passes from the two terms of a presentation to the module it
presents.**  The hypotheses are: the two squares commute; the base changes of the restriction
maps of the two coproducts are bijective; the presenting map is surjective on the sections over
both objects; it kills the composite with `a`; and over `W` a section it kills is a value of
`a`. -/
theorem bijective_liftBaseChange_of_presentation
    (hsqa : ∀ q, rP (aT q) = aW (rQ q)) (hsqb : ∀ p, rN (bT p) = bW (rP p))
    (hQ : Function.Bijective (rQ.liftBaseChange B))
    (hP : Function.Bijective (rP.liftBaseChange B))
    (hbT : Function.Surjective bT) (hbW : Function.Surjective bW)
    (hzero : ∀ q, bT (aT q) = 0)
    (hexW : ∀ p, bW p = 0 → p ∈ LinearMap.range aW) :
    Function.Bijective (rN.liftBaseChange B) := by
  have hcb := liftBaseChange_comp_lTensor (A := A) (B := B) bT bW rP rN hsqb
  have hca := liftBaseChange_comp_lTensor (A := A) (B := B) aT aW rQ rP hsqa
  refine ⟨?_, fun n ↦ ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective B hbT y
    obtain ⟨q, hq⟩ := hexW _ (by rw [← hcb x, hy])
    obtain ⟨z, hz⟩ := hQ.2 q
    have hx : LinearMap.lTensor B aT z = x := by
      refine hP.1 ?_
      rw [hca z, hz, hq]
    have hzero' : LinearMap.lTensor B bT (LinearMap.lTensor B aT z) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        show bT ∘ₗ aT = 0 from LinearMap.ext hzero, LinearMap.lTensor_zero]
      rfl
    rw [← hx, hzero']
  · obtain ⟨p, hp⟩ := hbW n
    obtain ⟨x, hx⟩ := hP.2 p
    exact ⟨LinearMap.lTensor B bT x, by rw [hcb x, hx, hp]⟩

/-- **The sections of a presented module as a base change.**  This is
`Module.BaseChange.bijective_liftBaseChange_of_presentation` bundled as a linear equivalence; it
is the `eN` that `SheafOfModules.detectsRange_of_baseChangeEquiv` asks for. -/
noncomputable def baseChangeEquivOfPresentation
    (hsqa : ∀ q, rP (aT q) = aW (rQ q)) (hsqb : ∀ p, rN (bT p) = bW (rP p))
    (hQ : Function.Bijective (rQ.liftBaseChange B))
    (hP : Function.Bijective (rP.liftBaseChange B))
    (hbT : Function.Surjective bT) (hbW : Function.Surjective bW)
    (hzero : ∀ q, bT (aT q) = 0)
    (hexW : ∀ p, bW p = 0 → p ∈ LinearMap.range aW) :
    B ⊗[A] NT ≃ₗ[B] NW :=
  LinearEquiv.ofBijective _ (bijective_liftBaseChange_of_presentation aT bT aW bW rQ rP rN
    hsqa hsqb hQ hP hbT hbW hzero hexW)

/-- `Module.BaseChange.baseChangeEquivOfPresentation` carries `1 ⊗ n` to the restriction of `n`,
which is the `hres` compatibility of
`SheafOfModules.detectsRange_of_baseChangeEquiv`. -/
lemma baseChangeEquivOfPresentation_one_tmul
    (hsqa : ∀ q, rP (aT q) = aW (rQ q)) (hsqb : ∀ p, rN (bT p) = bW (rP p))
    (hQ : Function.Bijective (rQ.liftBaseChange B))
    (hP : Function.Bijective (rP.liftBaseChange B))
    (hbT : Function.Surjective bT) (hbW : Function.Surjective bW)
    (hzero : ∀ q, bT (aT q) = 0)
    (hexW : ∀ p, bW p = 0 → p ∈ LinearMap.range aW) (n : NT) :
    baseChangeEquivOfPresentation aT bT aW bW rQ rP rN hsqa hsqb hQ hP hbT hbW hzero hexW
        ((1 : B) ⊗ₜ[A] n) = rN n := by
  show rN.liftBaseChange B ((1 : B) ⊗ₜ[A] n) = rN n
  rw [LinearMap.liftBaseChange_tmul, one_smul]

/-- **The equivalence for the presented module and the one for the presenting coproduct
intertwine the presenting morphism with its base change**, which is the `hsq` hypothesis of
`SheafOfModules.detectsRange_of_baseChangeEquiv`. -/
lemma comp_baseChangeEquivOfBasis
    (hsqb : ∀ p, rN (bT p) = bW (rP p)) (eP : B ⊗[A] PT ≃ₗ[B] PW)
    (heP : ∀ x, eP x = rP.liftBaseChange B x)
    (hsqa : ∀ q, rP (aT q) = aW (rQ q))
    (hQ : Function.Bijective (rQ.liftBaseChange B))
    (hP : Function.Bijective (rP.liftBaseChange B))
    (hbT : Function.Surjective bT) (hbW : Function.Surjective bW)
    (hzero : ∀ q, bT (aT q) = 0)
    (hexW : ∀ p, bW p = 0 → p ∈ LinearMap.range aW) (x : B ⊗[A] PT) :
    bW (eP x) =
      baseChangeEquivOfPresentation aT bT aW bW rQ rP rN hsqa hsqb hQ hP hbT hbW hzero hexW
        (LinearMap.lTensor B bT x) := by
  rw [heP x]
  exact (liftBaseChange_comp_lTensor (A := A) (B := B) bT bW rP rN hsqb x).symm

end Presentation

section FinsuppAdapter

variable (A B) (I : Type*) [DecidableEq I]

/-- **The augmentation in coordinates.**  The index-shape adapter carries `1 ⊗ p` to the family
`p` with its coefficients pushed along `A → B`.  This is the coordinatewise form of
`Module.Descent.amitsurAug`, and it is what
`PresheafOfModules.exists_restrictₛₗ_eq_of_cechDiff₀_eq_zero` asks of its augmentation
hypothesis once the sections of a coproduct of copies of the structure sheaf are read through
`SheafOfModules.sectionsEquivFinsupp`. -/
lemma finsuppBaseChange_one_tmul (p : I →₀ A) :
    Module.Descent.finsuppBaseChange A B I ((1 : B) ⊗ₜ[A] p) =
      p.mapRange (algebraMap A B) (map_zero _) :=
  Finsupp.ext fun i ↦ by
    rw [Module.Descent.finsuppBaseChange_tmul_apply, Finsupp.mapRange_apply, Algebra.smul_def,
      mul_one]

/-- **An algebra map in coordinates.**  Pushing the coefficients of a base-changed family along
an algebra map is the same as base changing along it first.  For `σ` the two inclusions
`Algebra.TensorProduct.includeLeft` and `Algebra.TensorProduct.includeRight` this is the
translation between the coefficientwise restriction of
`SheafOfModules.restrict_linearCombination_tautGen` and the `LinearMap.rTensor` form of the
identification hypotheses of
`PresheafOfModules.cechDiff₀_eq_amitsurDiff₀`. -/
lemma mapRange_finsuppBaseChange {B₂ : Type*} [CommRing B₂] [Algebra A B₂] (σ : B →ₐ[A] B₂)
    (y : B ⊗[A] (I →₀ A)) :
    (Module.Descent.finsuppBaseChange A B I y).mapRange σ (map_zero _) =
      Module.Descent.finsuppBaseChange A B₂ I
        (LinearMap.rTensor (I →₀ A) σ.toLinearMap y) := by
  induction y with
  | tmul b p =>
    refine Finsupp.ext fun i ↦ ?_
    rw [Finsupp.mapRange_apply, Module.Descent.finsuppBaseChange_tmul_apply,
      LinearMap.rTensor_tmul, Module.Descent.finsuppBaseChange_tmul_apply]
    exact map_smul σ.toLinearMap (p i) b
  | add y y' hy hy' =>
    rw [map_add, map_add, map_add, ← hy, ← hy']
    exact Finsupp.ext fun i ↦ map_add σ _ _

end FinsuppAdapter

end Module.BaseChange

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  {I : Type w} {N : SheafOfModules.{max t r} R}
  (ι : ∀ _ : I, uliftForPresentation.{u, v, r, r, t} (unit R) ⟶ N)

/-- **The tautological generators of a coproduct of copies of the universe lift of the structure
sheaf form a basis of its sections** over an object with the finite subcovering property.  This
is `SheafOfModules.sectionsEquivFinsupp` read as a basis; `Module.Basis.mapCoeffs` transports it
along a ring equivalence identifying the sections of the structure sheaf with a commutative
ring. -/
noncomputable def tautBasis (hN : IsColimit (Cofan.mk N ι)) {V : C}
    (hV : J.HasFiniteSubcovering V) :
    Module.Basis I (R.obj.obj (op V)) (N.val.obj (op V)) :=
  Module.Basis.ofRepr (sectionsEquivFinsupp ι hN hV).symm

/-- `SheafOfModules.tautBasis` is the family of tautological generators. -/
@[simp]
lemma tautBasis_apply (hN : IsColimit (Cofan.mk N ι)) {V : C}
    (hV : J.HasFiniteSubcovering V) (i : I) :
    tautBasis ι hN hV i = tautGen ι i (op V) := by
  have h : (sectionsEquivFinsupp ι hN hV) (Finsupp.single i 1) = tautGen ι i (op V) := by
    rw [sectionsEquivFinsupp_apply, Finsupp.linearCombination_single, one_smul]
  exact h

end SheafOfModules

end
