module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction

/-!
# Being cartesian over a morphism descends from a faithfully flat family over its source

Let `R` be a presheaf of commutative rings on a category `C`, let `M` be a presheaf of modules
over it, and let `f : U ⟶ V` be a morphism.  Suppose `U` carries a finite family `T i ⟶ U` whose
rings of sections are jointly faithfully flat over `R U`, and that `M` is cartesian both over
each `T i ⟶ U` and over each composite `T i ⟶ U ⟶ V`.  Then `M` is cartesian over `f` itself.

Unlike `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover` this asks **nothing about
the ring map along `f`** — in particular not that it be flat.  Flatness is replaced by
cartesianness over the composites, and the mechanism is different: there the base-change
comparison at `f` is assembled out of two equalizer descriptions of the sections, here it is
*reflected* along a faithfully flat base change.  In the triangle

`R (T i) ⊗_{R U} (R U ⊗_{R V} M V) ⟶ R (T i) ⊗_{R U} M U ⟶ M (T i)`

the second map and the composite are the comparisons at `q i` and at `q i ≫ f`; when both are
isomorphisms the first map, which is the comparison at `f` tensored with `R (T i)`, is one too,
and a faithfully flat module reflects that.

## Main results

* `Module.Descent.bijective_of_cancellation`: the ring-theoretic statement — a map out of
  `B ⊗[A] P` whose base changes to a jointly faithfully flat finite family of `B`-algebras are
  bijective is bijective.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_faithfullyFlat_family`: **being
  cartesian over `f` descends from a finite faithfully flat family over the source of `f`.**

## Implementation notes

`Module.Descent.bijective_of_cancellation` takes the two comparisons on a member of the family
as bare functions together with their additivity rather than as linear maps: only that,
their bijectivity and their values on pure tensors are used, so a consumer may hand over the
underlying function of a base-change comparison with no coherence work.  The identification of
the two sources is `TensorProduct.AlgebraTensorModule.cancelBaseChange`, whose value on a pure
tensor is exactly the normalisation the hypothesis `hgh` states.

Passing from the members of the family to their product is `TensorProduct.piLeft`, which needs
the index type finite; that is the only place finiteness is used, and it is what makes
`Module.FaithfullyFlat.lTensor_bijective_iff_bijective` applicable to the product ring.

The algebra structures at the site level are `RingHom.toAlgebra` of the restriction maps, as in
`Stacks.PresheafOfModules.algebraOfRingHom`; the base-change comparison of a presheaf of modules
has the resulting tensor product as its source up to definitional equality, which is why it can
be handed to the ring-theoretic statement directly.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
-/

@[expose] public section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

universe u v r m

namespace Module.Descent

/-- **The triangle of base-change comparisons over a tower `A → B → Cc` commutes.**

`θ` is a map out of `B ⊗[A] P`, and `g`, `h` present the two ways of base-changing further to
`Cc` — through `B` and directly.  Given their additivity and their agreement on pure tensors,
the composite `g ∘ (Cc ⊗ θ)` is `h` read through
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
theorem lTensor_eq_of_cancellation
    {A B Cc : Type*} [CommRing A] [CommRing B] [CommRing Cc] [Algebra A B] [Algebra B Cc]
    [Algebra A Cc] [IsScalarTower A B Cc]
    {P : Type*} [AddCommGroup P] [Module A P]
    {MU : Type*} [AddCommGroup MU] [Module B MU]
    {MT : Type*} [AddCommGroup MT]
    (θ : B ⊗[A] P →ₗ[B] MU)
    (g : (Cc ⊗[B] MU) → MT) (hgadd : ∀ x y : Cc ⊗[B] MU, g (x + y) = g x + g y)
    (h : (Cc ⊗[A] P) → MT) (hhadd : ∀ x y : Cc ⊗[A] P, h (x + y) = h x + h y)
    (hgh : ∀ (c : Cc) (b : B) (p : P), g (c ⊗ₜ[B] θ (b ⊗ₜ[A] p)) = h ((b • c) ⊗ₜ[A] p))
    (x : Cc ⊗[B] (B ⊗[A] P)) :
    g (θ.lTensor Cc x) =
      h (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B Cc P x) := by
  have hg0 : g 0 = 0 := by simpa using (hgadd 0 0).symm
  have hh0 : h 0 = 0 := by simpa using (hhadd 0 0).symm
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, hg0, hh0]
  | add x y hx hy => rw [map_add, map_add, hgadd, hhadd, hx, hy]
  | tmul c z =>
    induction z using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, hg0, hh0]
    | add z w hz hw => rw [TensorProduct.tmul_add, map_add, map_add, hgadd, hhadd, hz, hw]
    | tmul b p => exact hgh c b p

/-- **Base change along a tower: the comparison at the composite is bijective.**  With the data
of `Module.Descent.lTensor_eq_of_cancellation`, if `θ` and `g` are bijective then so is `h`,
which is their composite read through a linear equivalence. -/
theorem bijective_comp_of_cancellation
    {A B Cc : Type*} [CommRing A] [CommRing B] [CommRing Cc] [Algebra A B] [Algebra B Cc]
    [Algebra A Cc] [IsScalarTower A B Cc]
    {P : Type*} [AddCommGroup P] [Module A P]
    {MU : Type*} [AddCommGroup MU] [Module B MU]
    {MT : Type*} [AddCommGroup MT]
    (θ : B ⊗[A] P →ₗ[B] MU) (hθ : Function.Bijective θ)
    (g : (Cc ⊗[B] MU) → MT) (hgadd : ∀ x y : Cc ⊗[B] MU, g (x + y) = g x + g y)
    (hg : Function.Bijective g)
    (h : (Cc ⊗[A] P) → MT) (hhadd : ∀ x y : Cc ⊗[A] P, h (x + y) = h x + h y)
    (hgh : ∀ (c : Cc) (b : B) (p : P), g (c ⊗ₜ[B] θ (b ⊗ₜ[A] p)) = h ((b • c) ⊗ₜ[A] p)) :
    Function.Bijective h := by
  set κ := TensorProduct.AlgebraTensorModule.cancelBaseChange A B B Cc P with hκ
  have key := lTensor_eq_of_cancellation θ g hgadd h hhadd hgh
  have hLbij : Function.Bijective (θ.lTensor Cc) :=
    (TensorProduct.congr (LinearEquiv.refl B Cc) (LinearEquiv.ofBijective θ hθ)).bijective
  have hfun : (h : Cc ⊗[A] P → MT) = (g ∘ (θ.lTensor Cc)) ∘ κ.symm := by
    funext y
    rw [Function.comp_apply, Function.comp_apply, key, hκ, κ.apply_symm_apply]
  rw [hfun]
  exact (hg.comp hLbij).comp κ.symm.bijective

/-- **The base change of `θ` to one member of the family is bijective.**  With the data of
`Module.Descent.lTensor_eq_of_cancellation`, if `g` is injective and `h` bijective then
`Cc ⊗ θ` is bijective. -/
theorem lTensor_bijective_of_cancellation
    {A B Cc : Type*} [CommRing A] [CommRing B] [CommRing Cc] [Algebra A B] [Algebra B Cc]
    [Algebra A Cc] [IsScalarTower A B Cc]
    {P : Type*} [AddCommGroup P] [Module A P]
    {MU : Type*} [AddCommGroup MU] [Module B MU]
    {MT : Type*} [AddCommGroup MT]
    (θ : B ⊗[A] P →ₗ[B] MU)
    (g : (Cc ⊗[B] MU) → MT) (hgadd : ∀ x y : Cc ⊗[B] MU, g (x + y) = g x + g y)
    (hg : Function.Injective g)
    (h : (Cc ⊗[A] P) → MT) (hhadd : ∀ x y : Cc ⊗[A] P, h (x + y) = h x + h y)
    (hh : Function.Bijective h)
    (hgh : ∀ (c : Cc) (b : B) (p : P), g (c ⊗ₜ[B] θ (b ⊗ₜ[A] p)) = h ((b • c) ⊗ₜ[A] p)) :
    Function.Bijective (θ.lTensor Cc) := by
  let κ : (Cc ⊗[B] (B ⊗[A] P)) ≃ₗ[B] (Cc ⊗[A] P) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B B Cc P
  have key : ∀ x, g (θ.lTensor Cc x) = h (κ x) :=
    lTensor_eq_of_cancellation θ g hgadd h hhadd hgh
  refine ⟨fun x y hxy => κ.injective (hh.1 ?_), fun y => ?_⟩
  · rw [← key, ← key, hxy]
  · obtain ⟨z, hz⟩ := hh.2 (g y)
    exact ⟨κ.symm z, hg (by rw [key, κ.apply_symm_apply, hz])⟩

/-- **Base change to a finite product is bijective if it is bijective on each factor.** -/
theorem lTensor_pi_bijective {R : Type*} [CommSemiring R] {ι : Type*} [Finite ι]
    {Cs : ι → Type*} [∀ i, AddCommMonoid (Cs i)] [∀ i, Module R (Cs i)]
    {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (hf : ∀ i, Function.Bijective (f.lTensor (Cs i))) :
    Function.Bijective (f.lTensor (∀ i, Cs i)) := by
  classical
  let _ := Fintype.ofFinite ι
  let e₁ : ((∀ i, Cs i) ⊗[R] M) ≃ₗ[R] ∀ i, Cs i ⊗[R] M := TensorProduct.piLeft R M Cs
  let e₂ : ((∀ i, Cs i) ⊗[R] N) ≃ₗ[R] ∀ i, Cs i ⊗[R] N := TensorProduct.piLeft R N Cs
  have hsq : ∀ (x : (∀ i, Cs i) ⊗[R] M) (i : ι),
      e₂ (f.lTensor (∀ i, Cs i) x) i = f.lTensor (Cs i) (e₁ x i) := by
    intro x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
    | tmul c z => simp [e₁, e₂]
  have he : (fun x => e₂ (f.lTensor (∀ i, Cs i) x)) =
      (fun (y : ∀ i, Cs i ⊗[R] M) i => f.lTensor (Cs i) (y i)) ∘ e₁ :=
    funext fun x => funext (hsq x)
  have h1 : Function.Bijective (fun x => e₂ (f.lTensor (∀ i, Cs i) x)) := by
    rw [he]
    exact (Function.Bijective.piMap hf).comp e₁.bijective
  simpa [Function.comp_def] using e₂.symm.bijective.comp h1

/-- **Bijectivity of a base-change comparison is reflected by a finite faithfully flat family.**

`θ` is a map out of the base change `B ⊗[A] P` of an `A`-module along `A → B`, and the `Cs i`
form a finite family of `B`-algebras, each an `A`-algebra compatibly, whose product is
faithfully flat over `B`.  The maps `g i` and `h i` present the two ways of base-changing to
`Cs i` — through `B` and directly — and agree on pure tensors by `hgh`.  Then `θ` is bijective
as soon as each `h i` is bijective and each `g i` injective. -/
theorem bijective_of_cancellation
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type*} [Finite ι]
    {Cs : ι → Type*} [∀ i, CommRing (Cs i)] [∀ i, Algebra B (Cs i)] [∀ i, Algebra A (Cs i)]
    [∀ i, IsScalarTower A B (Cs i)] [Module.FaithfullyFlat B (∀ i, Cs i)]
    {P : Type*} [AddCommGroup P] [Module A P]
    {MU : Type*} [AddCommGroup MU] [Module B MU]
    {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)]
    (θ : B ⊗[A] P →ₗ[B] MU)
    (g : ∀ i, (Cs i ⊗[B] MU) → Mi i)
    (hgadd : ∀ (i : ι) (x y : Cs i ⊗[B] MU), g i (x + y) = g i x + g i y)
    (hg : ∀ i, Function.Injective (g i))
    (h : ∀ i, (Cs i ⊗[A] P) → Mi i)
    (hhadd : ∀ (i : ι) (x y : Cs i ⊗[A] P), h i (x + y) = h i x + h i y)
    (hh : ∀ i, Function.Bijective (h i))
    (hgh : ∀ (i : ι) (c : Cs i) (b : B) (p : P),
      g i (c ⊗ₜ[B] θ (b ⊗ₜ[A] p)) = h i ((b • c) ⊗ₜ[A] p)) :
    Function.Bijective θ :=
  (Module.FaithfullyFlat.lTensor_bijective_iff_bijective B (∀ i, Cs i) θ).mp <|
    lTensor_pi_bijective θ fun i =>
      lTensor_bijective_of_cancellation θ (g i) (hgadd i) (hg i) (h i) (hhadd i) (hh i) (hgh i)

end Module.Descent

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))

/-- **Being cartesian over `f : U ⟶ V` descends from a finite faithfully flat family over `U`.**

The family `q i : T i ⟶ U` is required to be jointly faithfully flat on rings of sections, and
`M` to be cartesian over each `q i` and over each composite `q i ≫ f`.  Nothing is required of
the ring map along `f`.

This is the reflection step: the comparison at `f` is an isomorphism after tensoring with each
`R (T i)`, because the comparisons at `q i` and at `q i ≫ f` are, and faithful flatness of the
product of the `R (T i)` over `R U` reflects that. -/
theorem isIso_restrictionBaseChange_of_faithfullyFlat_family
    {U V : C} (f : U ⟶ V) {I : Type*} [Finite I]
    (T : I → C) (q : ∀ i, T i ⟶ U)
    (hff : (RingHom.pi (fun i => (R.map (q i).op).hom)).FaithfullyFlat)
    (hq : ∀ i, IsIso (restrictionBaseChange M (q i).op))
    (hc : ∀ i, IsIso (restrictionBaseChange M (q i ≫ f).op)) :
    IsIso (restrictionBaseChange M f.op) := by
  classical
  let algB : Algebra (R.obj (.op V)) (R.obj (.op U)) := (R.map f.op).hom.toAlgebra
  let algC : ∀ i, Algebra (R.obj (.op U)) (R.obj (.op (T i))) :=
    fun i => (R.map (q i).op).hom.toAlgebra
  let algAC : ∀ i, Algebra (R.obj (.op V)) (R.obj (.op (T i))) :=
    fun i => (R.map (q i ≫ f).op).hom.toAlgebra
  let towC : ∀ i, IsScalarTower (R.obj (.op V)) (R.obj (.op U)) (R.obj (.op (T i))) := by
    refine fun i => IsScalarTower.of_algebraMap_eq (fun x => ?_)
    show (R.map (q i ≫ f).op).hom x = ((R.map f.op) ≫ (R.map (q i).op)).hom x
    rw [← R.map_comp, ← op_comp]
  let : Module.FaithfullyFlat (R.obj (.op U)) (∀ i, R.obj (.op (T i))) := hff
  let instIso : ∀ i, IsIso (restrictionBaseChange M (q i).op) := hq
  let instIsoC : ∀ i, IsIso (restrictionBaseChange M (q i ≫ f).op) := hc
  rw [ConcreteCategory.isIso_iff_bijective]
  refine Module.Descent.bijective_of_cancellation
    (Cs := fun i => R.obj (.op (T i))) (Mi := fun i => M.obj (.op (T i)))
    (restrictionBaseChange M f.op).hom
    (fun i => (restrictionBaseChange M (q i).op).hom) (fun i => map_add _)
    (fun i => (ConcreteCategory.bijective_of_isIso (restrictionBaseChange M (q i).op)).1)
    (fun i => (restrictionBaseChange M (q i ≫ f).op).hom) (fun i => map_add _)
    (fun i => ConcreteCategory.bijective_of_isIso (restrictionBaseChange M (q i ≫ f).op))
    (fun i c b p => ?_)
  show (restrictionBaseChange M (q i).op)
      (c ⊗ₜ[R.obj (.op U), (R.map (q i).op).hom] ((restrictionBaseChange M f.op)
        (b ⊗ₜ[R.obj (.op V), (R.map f.op).hom] p))) =
    (restrictionBaseChange M (q i ≫ f).op)
      ((b • c) ⊗ₜ[R.obj (.op V), (R.map (q i ≫ f).op).hom] p)
  rw [restrictionBaseChange_tmul M f.op b p]
  refine Eq.trans (restrictionBaseChange_tmul M (q i).op c
    (b • (M.map f.op p : M.obj (.op U)))) ?_
  refine Eq.trans ?_ (restrictionBaseChange_tmul M (q i ≫ f).op (b • c) p).symm
  have hms : (M.map (q i).op) (b • (M.map f.op p : M.obj (.op U))) =
      (R.map (q i).op).hom b • ((M.map (q i).op) (M.map f.op p) : M.obj (.op (T i))) :=
    M.map_smul (q i).op b _
  refine Eq.trans (congrArg (fun z => c • z) hms) ?_
  refine Eq.trans (smul_smul c ((R.map (q i).op).hom b)
    ((M.map (q i).op) (M.map f.op p) : M.obj (.op (T i)))) ?_
  have hcomp : ((M.map (q i).op) (M.map f.op p) : M.obj (.op (T i))) =
      M.map (q i ≫ f).op p := by
    rw [← M.map_comp_apply, ← op_comp]
  have hbc : (b • c : R.obj (.op (T i))) = c * (R.map (q i).op).hom b := mul_comm _ _
  rw [hbc, hcomp]
  rfl

end Stacks.PresheafOfModules

end
