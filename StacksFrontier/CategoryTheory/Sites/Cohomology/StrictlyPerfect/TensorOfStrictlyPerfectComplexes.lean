module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectComplexes
import StacksCore.Tactic.StacksAttribute

/-!
# The total tensor complex of two strictly perfect complexes on a ringed site

Let `(C, O)` be a ringed site. The total tensor complex `Tot(K ⊗_O L)` of two complexes of
`O`-modules has as its degree-`c` term the coproduct, over the pairs `t + r = c`, of the sheaf
tensor products `K^t ⊗_O L^r`. This file proves that `Tot(K ⊗_O L)` is strictly perfect as soon
as `K` and `L` are: only finitely many of those summands are nonzero, and each of them is a
direct summand of a finite free `O`-module because the tensor product of two finite free
`O`-modules is finite free.

## Main definitions

* `Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoLeft`: tensoring the structure sheaf with a
  sheaf of `O`-modules returns the sheaf itself, together with
  `Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoLeft_hom_unit_tmul`, its effect on the local
  pure tensor of the unit section.
* `Stacks.SheafOfModules.Tensor.sheafTensorUnitIso`: tensoring a sheaf of `O`-modules with the
  structure sheaf returns the sheaf itself.
* `Stacks.SheafOfModules.Tensor.freeIsoBiproductFin`: the finite free `O`-module `O^{⊕n}` is
  the direct sum of `n` copies of the structure sheaf.

## Main results

* `Stacks.SheafOfModules.Tensor.isDirectSummandOfFiniteFree_biproduct`: a finite direct sum of
  direct summands of finite free `O`-modules is one.
* `Stacks.SheafOfModules.Tensor.isDirectSummandOfFiniteFree_tensor`: the tensor product of two
  direct summands of finite free `O`-modules is one.
* `Stacks.SheafOfModules.Tensor.isStrictlyPerfect_tensorComplex`: **Stacks 09J8.** The total
  tensor complex of two strictly perfect complexes of `O`-modules is strictly perfect.

## Implementation notes

Strict perfectness is `IsStrictlyPerfect`, the predicate carrying Stacks 08FL, and the total
tensor complex is `Stacks.SheafOfModules.Tensor.tensorComplex`, the one built from the sheaf
tensor product of Stacks 06YM; neither notion is reintroduced here, and in particular the
finite free `O`-modules are the `SheafOfModules.free (ULift (Fin n))` of Stacks 08FL and not a
second copy of them.

Those free modules are coproducts of copies of the structure sheaf, and `freeIsoBiproductFin`
identifies them with the corresponding direct sums indexed by `Fin n`. Every manipulation below
is then a manipulation of finite direct sums over index types in `Type`, which is what both
`biproductBiproductIso` — collapsing an iterated finite direct sum into a single one indexed by
a sigma type — and `biproduct.reindex` ask for. The index of the coproduct defining the free
module, on the other hand, must live in the universe of the sections of the structure sheaf,
whence the `ULift`.

The only analytic ingredient is `sheafTensorUnitIso`. The sheaf tensor product of Stacks 06YM
is the sheafification of the objectwise tensor product of the underlying presheaves of modules,
so tensoring with the structure sheaf is the sheafification of the right unitor of that
objectwise tensor product, followed by the counit of the sheafification adjunction, which is an
isomorphism on a sheaf. No distributivity of the tensor product over infinite direct sums is
needed: the two additivity hypotheses which `tensorComplex` carries anyway give its
distributivity over the finite ones, and that is all the finite free modules require.

The three universes are free and independent: the objects and the morphisms of the site, and
the sections. The sections of the modules are taken in the same universe as the sections of the
structure sheaf, as they must be for a module to be comparable with a finite free one.

## References

* [Stacks Project, Tag 09J8](https://stacks.math.columbia.edu/tag/09J8)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

namespace Stacks.SheafOfModules.Tensor

section Biproducts

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteBiproducts A]

/-- A finite direct sum of finite direct sums of copies of one object is again a finite direct
sum of copies of it: the iterated direct sum is indexed by a finite sigma type, which is
reindexed by `Fin N`.

Applied to the structure sheaf of a ringed site, this says that a finite direct sum of finite
free `O`-modules is a finite free `O`-module. -/
theorem exists_iteratedBiproduct_iso (X : A) {ι : Type} [Finite ι] (n : ι → ℕ) :
    ∃ N : ℕ, Nonempty ((⨁ fun i => ⨁ (fun _ : Fin (n i) => X)) ≅ ⨁ (fun _ : Fin N => X)) := by
  classical
  let _ := Fintype.ofFinite ι
  exact ⟨Fintype.card (Σ i, Fin (n i)),
    ⟨biproductBiproductIso (fun i => Fin (n i)) (fun _ _ => X) ≪≫
      (biproduct.reindex (Fintype.equivFin (Σ i, Fin (n i))).symm (fun _ => X)).symm⟩⟩

end Biproducts

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Sheaves of `O`-modules have finite direct sums: they form an abelian category, hence have
finite products, and a preadditive category with finite products has finite biproducts. -/
local instance hasFiniteBiproducts_sheafOfModules :
    HasFiniteBiproducts (SheafOfModules.{w} (ringSheaf R)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Tensoring a sheaf of `O`-modules with the structure sheaf returns the sheaf itself: the
sheaf tensor product is the sheafification of the objectwise tensor product, the right unitor
identifies that objectwise tensor product of the underlying presheaves with the underlying
presheaf, and the counit of the sheafification adjunction is an isomorphism on a sheaf. -/
def sheafTensorUnitIso (M : SheafOfModules.{w} (ringSheaf R)) :
    ((sheafTensor R).obj M).obj (SheafOfModules.unit (ringSheaf R)) ≅ M :=
  let : MonoidalCategory (PresheafOfModules.{w} (ringSheaf R).obj) :=
    inferInstanceAs (MonoidalCategory
      (PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat)))
  (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).mapIso
      (ρ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).counit).app M

/-! ### The left unit constraint, and its effect on sections -/

section LeftUnitor

omit [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A composite of morphisms of sheaves of modules acts on sections by composition. -/
private lemma comp_val_app_apply {P Q S : SheafOfModules.{w} (ringSheaf R)} (φ : P ⟶ Q)
    (ψ : Q ⟶ S) (U : Cᵒᵖ) (x : P.val.obj U) :
    ((φ ≫ ψ).val.app U) x = (ψ.val.app U) ((φ.val.app U) x) := rfl

/-- **The sheafification counit undoes the sheafification unit on the sections of a sheaf.**
This is the triangle identity of the sheafification adjunction, read on sections. -/
private lemma counit_unit_apply (M : SheafOfModules.{w} (ringSheaf R)) (U : Cᵒᵖ)
    (y : M.val.obj U) :
    ((PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
        (𝟙 (ringSheaf R).obj)).counit.app M).val.app U
      (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
        (𝟙 (ringSheaf R).obj)).unit.app M.val).app U y) = y := by
  have h := (PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
    (𝟙 (ringSheaf R).obj)).right_triangle_components (Y := M)
  exact (_root_.PresheafOfModules.comp_app_apply _ _ U y).symm.trans
    (congrArg (fun z => z.app U y) h)

/-- **Sheafifying a morphism commutes with the sheafification unit, on sections.** This is the
naturality of the unit of the sheafification adjunction. -/
private lemma sheafification_map_unit_apply
    {P Q : PresheafOfModules.{w} (ringSheaf R).obj} (h : P ⟶ Q) (U : Cᵒᵖ) (x : P.obj U) :
    ((PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map h).val.app U
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
          (𝟙 (ringSheaf R).obj)).unit.app P).app U x) =
      ((PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
        (𝟙 (ringSheaf R).obj)).unit.app Q).app U (h.app U x) :=
  (congrArg (fun z ↦ z.app U x)
    ((PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
      (𝟙 (ringSheaf R).obj)).unit.naturality h)).symm

/-- The monoidal structure on presheaves of modules over the underlying ring presheaf, which is
the one the sheaf tensor product is the sheafification of. It is introduced as a local instance
rather than inside the definitions below, so that the definitions are plain composites and the
section computations can see through them. -/
local instance monoidalPresheavesOfModules :
    MonoidalCategory (PresheafOfModules.{w} (ringSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory
    (PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat)))

/-- **Tensoring the structure sheaf with a sheaf of `O`-modules returns the sheaf itself.** This
is the left-hand companion of `Stacks.SheafOfModules.Tensor.sheafTensorUnitIso`, built the same
way: the sheaf tensor product is the sheafification of the objectwise tensor product, the
presheaf left unitor identifies that with the underlying presheaf, and the counit of the
sheafification adjunction is an isomorphism on a sheaf. -/
def sheafTensorUnitIsoLeft (M : SheafOfModules.{w} (ringSheaf R)) :
    ((sheafTensor R).obj (SheafOfModules.unit (ringSheaf R))).obj M ≅ M :=
  (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).mapIso
      (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).counit).app M

/-- **The left unit constraint sends the local pure tensor of the unit section with `t` back to
`t`.** A local section of the sheaf tensor product of the structure sheaf with `M` which is the
pure tensor of the section `1` and a section `t` of `M` is carried to `t`.

This is what makes the left unit constraint usable in a computation with local sections, and is
the reason it is preferred to the right one together with a braiding: the braiding has no
description on sections anywhere, so going through it would leave the composite opaque. -/
lemma sheafTensorUnitIsoLeft_hom_unit_tmul (M : SheafOfModules.{w} (ringSheaf R)) (U : Cᵒᵖ)
    (t : M.val.obj U) :
    (sheafTensorUnitIsoLeft R M).hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
            (𝟙 (ringSheaf R).obj)).unit.app
          ((SheafOfModules.unit (ringSheaf R)).val ⊗ M.val)).app U
            ((1 : (ringSheaf R).obj.obj U) ⊗ₜ t)) = t := by
  have hcomp : (sheafTensorUnitIsoLeft R M).hom =
      (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
          (λ_ M.val).hom ≫
        (PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
          (𝟙 (ringSheaf R).obj)).counit.app M := rfl
  rw [hcomp]
  refine Eq.trans (comp_val_app_apply R _ _ U _) ?_
  refine Eq.trans (congrArg (fun y => ((PresheafOfModules.sheafificationAdjunction
    (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).counit.app M).val.app U y)
    (sheafification_map_unit_apply R (λ_ M.val).hom U _)) ?_
  refine Eq.trans (counit_unit_apply R M U _) ?_
  let _i : CommRing ↑((ringSheaf R).obj.obj U) := inferInstanceAs (CommRing ↑(R.obj.obj U))
  change (ConcreteCategory.hom (λ_ (M.val.obj U)).hom)
    ((1 : ↑((ringSheaf R).obj.obj U)) ⊗ₜ t) = t
  rw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
  exact one_smul _ _

/-- **Tensoring a sheaf of `O`-modules with the structure sheaf on the right returns the sheaf
itself.** This is `sheafTensorUnitIso` again, but built as a plain composite rather than with the
monoidal structure introduced by a `letI` in the body. A `letI` leaves a `let` in the term, which
blocks every rewrite through the definition, so the form with the instance in scope is the one a
computation can use. -/
def sheafTensorUnitIsoRight (M : SheafOfModules.{w} (ringSheaf R)) :
    ((sheafTensor R).obj M).obj (SheafOfModules.unit (ringSheaf R)) ≅ M :=
  (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).mapIso
      (ρ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).counit).app M

/-- **The right unit constraint is natural.** Both of its factors are: the presheaf right unitor
is a monoidal structure constraint, and the counit of the sheafification adjunction is a natural
transformation. -/
@[reassoc (attr := simp)]
theorem sheafTensorUnitIsoRight_naturality {M M' : SheafOfModules.{w} (ringSheaf R)}
    (f : M ⟶ M') :
    ((sheafTensor R).map f).app (SheafOfModules.unit (ringSheaf R)) ≫
        (sheafTensorUnitIsoRight R M').hom =
      (sheafTensorUnitIsoRight R M).hom ≫ f := by
  have hM (N : SheafOfModules.{w} (ringSheaf R)) : (sheafTensorUnitIsoRight R N).hom =
      (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
          (ρ_ N.val).hom ≫
        (PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
          (𝟙 (ringSheaf R).obj)).counit.app N := rfl
  have hT : ((sheafTensor R).map f).app (SheafOfModules.unit (ringSheaf R)) =
      (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).map
        (f.val ▷ (SheafOfModules.unit (ringSheaf R)).val) := rfl
  rw [hM, hM, hT]
  set SH := (PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj))
  set EP := (PresheafOfModules.sheafificationAdjunction (R := ringSheaf R)
    (𝟙 (ringSheaf R).obj)).counit
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ EP.app M')
      ((SH.map_comp _ _).symm.trans
        (congrArg (fun z => SH.map z)
          (MonoidalCategory.rightUnitor_naturality f.val)))).trans
      ((congrArg (fun z => z ≫ EP.app M') (SH.map_comp _ _)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => SH.map (ρ_ M.val).hom ≫ z) (EP.naturality f)).trans
            (Category.assoc _ _ _).symm))))

end LeftUnitor

/-- The finite free `O`-module `O^{⊕n}` is the direct sum of `n` copies of the structure sheaf:
it is their coproduct by definition, and a finite coproduct in an additive category is a direct
sum. The index of the coproduct lives in the universe of the sections, so the comparison also
reindexes along `ULift (Fin n) ≃ Fin n`. -/
def freeIsoBiproductFin (n : ℕ) :
    SheafOfModules.free (R := ringSheaf R) (ULift.{w} (Fin n)) ≅
      ⨁ (fun _ : Fin n => SheafOfModules.unit (ringSheaf R)) :=
  Sigma.whiskerEquiv (f := fun _ : ULift.{w} (Fin n) => SheafOfModules.unit (ringSheaf R))
      (g := fun _ : Fin n => SheafOfModules.unit (ringSheaf R)) Equiv.ulift
      (fun _ => Iso.refl _) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin n => SheafOfModules.unit (ringSheaf R))).symm

/-- Being a direct summand of a finite free `O`-module is being a retract of a finite direct
sum of copies of the structure sheaf. -/
theorem isDirectSummandOfFiniteFree_iff_retract_biproduct
    (F : SheafOfModules.{w} (ringSheaf R)) :
    IsDirectSummandOfFiniteFree (ringSheaf R) F ↔
      ∃ n : ℕ, Nonempty (Retract F
        (⨁ (fun _ : Fin n => SheafOfModules.unit (ringSheaf R)))) := by
  rw [isDirectSummandOfFiniteFree_iff_free]
  constructor
  · rintro ⟨n, i, r, hir⟩
    exact ⟨n, ⟨(⟨i, r, hir⟩ : Retract _ _).trans (freeIsoBiproductFin R n).retract⟩⟩
  · rintro ⟨n, ⟨ret⟩⟩
    obtain ⟨i, r, h⟩ := ret.trans (freeIsoBiproductFin R n).symm.retract
    exact ⟨n, i, r, h⟩

/-- A finite direct sum of direct summands of finite free `O`-modules is a direct summand of a
finite free `O`-module: the direct sum of the retractions is a retraction off the direct sum of
the finite free modules, which is again finite free. -/
theorem isDirectSummandOfFiniteFree_biproduct {ι : Type} [Finite ι]
    (M : ι → SheafOfModules.{w} (ringSheaf R)) [HasBiproduct M]
    (hM : ∀ i, IsDirectSummandOfFiniteFree (ringSheaf R) (M i)) :
    IsDirectSummandOfFiniteFree (ringSheaf R) (⨁ M) := by
  classical
  choose n ret using fun i =>
    (isDirectSummandOfFiniteFree_iff_retract_biproduct R (M i)).mp (hM i)
  let r : ∀ i, Retract (M i) (⨁ fun _ : Fin (n i) => SheafOfModules.unit (ringSheaf R)) :=
    fun i => (ret i).some
  have hr : Retract (⨁ M)
      (⨁ fun i => ⨁ (fun _ : Fin (n i) => SheafOfModules.unit (ringSheaf R))) :=
    ⟨biproduct.map (fun i => (r i).i), biproduct.map (fun i => (r i).r), by
      ext i
      simp [Retract.retract]⟩
  obtain ⟨N, ⟨e⟩⟩ := exists_iteratedBiproduct_iso (SheafOfModules.unit (ringSheaf R)) n
  exact (isDirectSummandOfFiniteFree_iff_retract_biproduct R _).mpr
    ⟨N, ⟨hr.trans e.retract⟩⟩

/-- A colimit of a family of `O`-modules which are direct summands of finite free `O`-modules
and all but finitely many of which are zero is itself a direct summand of a finite free
`O`-module: the nonzero members form a finite direct sum with the same universal property. -/
theorem isDirectSummandOfFiniteFree_of_cofan {ι : Type}
    (M : ι → SheafOfModules.{w} (ringSheaf R)) (c : Cofan M) (hc : IsColimit c)
    (hfin : {i | ¬ IsZero (M i)}.Finite)
    (hM : ∀ i, IsDirectSummandOfFiniteFree (ringSheaf R) (M i)) :
    IsDirectSummandOfFiniteFree (ringSheaf R) c.pt := by
  classical
  let s := {i | ¬ IsZero (M i)}
  let _ : Fintype s := hfin.fintype
  let N : s → SheafOfModules.{w} (ringSheaf R) := fun i => M i.1
  let t : Cofan M := Cofan.mk (⨁ N)
    (fun i => if hi : i ∈ s then biproduct.ι N ⟨i, hi⟩ else 0)
  have ht : IsColimit t := by
    refine Cofan.IsColimit.mk t (fun d => biproduct.desc (fun i => d.inj i.1)) ?_ ?_
    · intro d i
      by_cases hi : i ∈ s
      · simp [t, hi]
      · have hzero : IsZero (M i) := by simpa [s] using hi
        exact hzero.eq_of_src _ _
    · intro d f hf
      refine biproduct.hom_ext' _ _ fun i => ?_
      simpa [t, i.2] using hf i.1
  exact IsDirectSummandOfFiniteFree.of_iso (ringSheaf R) (hc.coconePointUniqueUpToIso ht)
    (isDirectSummandOfFiniteFree_biproduct R N (fun i => hM i.1))

variable [∀ M, ((sheafTensor.{u, v, w, w, w} R).obj M).Additive]

/-- The tensor product of two finite free `O`-modules is finite free: tensoring with a fixed
`O`-module is additive, so it carries the direct sum of the copies of the structure sheaf in
the second factor to the direct sum of copies of the first factor. -/
theorem exists_biproductUnit_tensor_iso (a b : ℕ) :
    ∃ N : ℕ, Nonempty
      (((sheafTensor R).obj (⨁ fun _ : Fin a => SheafOfModules.unit (ringSheaf R))).obj
        (⨁ fun _ : Fin b => SheafOfModules.unit (ringSheaf R)) ≅
          ⨁ (fun _ : Fin N => SheafOfModules.unit (ringSheaf R))) := by
  classical
  let A := ⨁ fun _ : Fin a => SheafOfModules.unit (ringSheaf R)
  let T := (sheafTensor R).obj A
  obtain ⟨N, ⟨e⟩⟩ := exists_iteratedBiproduct_iso (SheafOfModules.unit (ringSheaf R))
    (fun _ : Fin b => a)
  exact ⟨N, ⟨T.mapBiproduct (fun _ : Fin b => SheafOfModules.unit (ringSheaf R)) ≪≫
    biproduct.mapIso (fun _ : Fin b => sheafTensorUnitIso R A) ≪≫ e⟩⟩

/-- The tensor product of two direct summands of finite free `O`-modules is a direct summand of
a finite free `O`-module: a retraction in either variable is carried along by the tensor
product, and the tensor product of the two finite free modules is finite free. -/
theorem isDirectSummandOfFiniteFree_tensor
    (M N : SheafOfModules.{w} (ringSheaf R))
    (hM : IsDirectSummandOfFiniteFree (ringSheaf R) M)
    (hN : IsDirectSummandOfFiniteFree (ringSheaf R) N) :
    IsDirectSummandOfFiniteFree (ringSheaf R) (((sheafTensor R).obj M).obj N) := by
  obtain ⟨a, ⟨rM⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract_biproduct R M).mp hM
  obtain ⟨b, ⟨rN⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract_biproduct R N).mp hN
  obtain ⟨P, ⟨e⟩⟩ := exists_biproductUnit_tensor_iso R a b
  have h₁ : Retract (((sheafTensor R).obj M).obj N)
      (((sheafTensor R).obj M).obj
        (⨁ fun _ : Fin b => SheafOfModules.unit (ringSheaf R))) :=
    rN.map ((sheafTensor R).obj M)
  have h₂ : Retract
      (((sheafTensor R).obj M).obj (⨁ fun _ : Fin b => SheafOfModules.unit (ringSheaf R)))
      (((sheafTensor R).obj (⨁ fun _ : Fin a => SheafOfModules.unit (ringSheaf R))).obj
        (⨁ fun _ : Fin b => SheafOfModules.unit (ringSheaf R))) :=
    rM.map ((sheafTensor R).flip.obj (⨁ fun _ : Fin b => SheafOfModules.unit (ringSheaf R)))
  exact (isDirectSummandOfFiniteFree_iff_retract_biproduct R _).mpr
    ⟨P, ⟨(h₁.trans h₂).trans e.retract⟩⟩

variable [(sheafTensor.{_, _, _, w, w} R).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{w} (ringSheaf R)) (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (sheafTensor R) (ComplexShape.up ℤ)]

/-- The bicomplex of sheaf tensor products of the terms of `K` and `L`, whose total complex is
the total tensor complex of Stacks 06YM. It is an abbreviation, so that the coproduct
decomposition of its total complex is matched by instance search. -/
abbrev tensorBicomplex (K L : CochainComplex (SheafOfModules.{w} (ringSheaf R)) ℤ) :
    HomologicalComplex₂ (SheafOfModules.{w} (ringSheaf R))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((sheafTensor R).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L

/-- **Stacks 09J8.** The total tensor complex `Tot(K ⊗_O L)` of two strictly perfect complexes
of `O`-modules on a ringed site is strictly perfect.

Each degree of `Tot(K ⊗_O L)` is the coproduct of the `K^t ⊗_O L^r` with `t + r` that degree.
Such a summand vanishes unless both `K^t` and `L^r` are nonzero, which happens for finitely
many pairs only, so the degree vanishes outside the sum of the two ranges of nonvanishing; and
each surviving summand is a direct summand of a finite free `O`-module because both of its
factors are. -/
@[stacks 09J8]
theorem isStrictlyPerfect_tensorComplex
    (K L : CochainComplex (SheafOfModules.{w} (ringSheaf R)) ℤ)
    (hK : IsStrictlyPerfect (ringSheaf R) K) (hL : IsStrictlyPerfect (ringSheaf R) L) :
    IsStrictlyPerfect (ringSheaf R) (((tensorComplex R).obj K).obj L) := by
  classical
  let Z := tensorBicomplex R K L
  let s := {i : ℤ | ¬ IsZero (K.X i)}
  let t := {i : ℤ | ¬ IsZero (L.X i)}
  have hz (p q : ℤ) (h : ¬ (p ∈ s ∧ q ∈ t)) : IsZero ((Z.X p).X q) := by
    rcases not_and_or.mp h with hp | hq
    · have hp : IsZero (K.X p) := by simpa [s] using hp
      exact ((sheafTensor R).flip.obj (L.X q)).map_isZero hp
    · have hq : IsZero (L.X q) := by simpa [t] using hq
      exact ((sheafTensor R).obj (K.X p)).map_isZero hq
  refine ⟨?_, ?_⟩
  · apply (hK.bounded.image2 (· + ·) hL.bounded).subset
    intro n hn
    by_contra hnot
    refine hn (StacksDraft.TotalComplexQuasiIso.isZero_cofan_pt _
      (Z.toGradedObject.isColimitCofanMapObj _ n) ?_)
    rintro ⟨⟨p, q⟩, hpq⟩
    exact hz p q fun h => hnot ⟨p, h.1, q, h.2, hpq⟩
  · intro n
    apply isDirectSummandOfFiniteFree_of_cofan R _ _
      (Z.toGradedObject.isColimitCofanMapObj _ n)
    · apply ((hK.bounded.prod hL.bounded).preimage
        (f := fun i : {pq : ℤ × ℤ | pq.1 + pq.2 = n} => i.1) Subtype.val_injective.injOn).subset
      rintro ⟨⟨p, q⟩, hpq⟩ h
      change p ∈ s ∧ q ∈ t
      by_contra hh
      exact h (hz p q hh)
    · rintro ⟨⟨p, q⟩, hpq⟩
      exact isDirectSummandOfFiniteFree_tensor R (K.X p) (L.X q)
        (hK.termDirectSummand p) (hL.termDirectSummand q)

end Stacks.SheafOfModules.Tensor

end
