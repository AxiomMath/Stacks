module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexes
import StacksCore.Tactic.StacksAttribute

/-!
# Locally constant cohomology of a derived tensor product with the powers of an ideal

Let `(C, J)` be a site, let `Λ` be a Noetherian commutative ring and let `I ⊆ Λ` be an ideal.
Stacks Tag 094I asserts that for `K` in `D^-(C, Λ)` whose cohomology sheaves after reduction
modulo `I` are locally constant sheaves of finite type, the same holds after reduction modulo
`Iⁿ` for every `n ≥ 1`.

The source's proof is an induction on `n` along the distinguished triangles

`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ ⟶ (K ⊗^L_Λ Iⁿ/Iⁿ⁺¹)[1]`,

whose outer vertices are known: the right one by the inductive hypothesis, the left one because
`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹` is the base change of `K ⊗^L_Λ Λ/I` along `Λ/I ⟶ Iⁿ/Iⁿ⁺¹`, which is a finite
`Λ/I`-module, so Tag 094H applies to it. The locally constant sheaves of finite type form a weak
Serre subcategory by Tag 093U, hence the objects of `D(C, Λ)` with locally constant cohomology
sheaves of finite type form a strictly full, saturated, triangulated subcategory by Tag 06UQ, and
in particular the middle vertex of such a triangle is again in it.

This file proves **the induction in full**, carrying the two inputs the source supplies from
outside the induction — the triangles, and the conclusion of the base change step — as explicit
hypotheses. See "What is not proved".

## Main results

* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow`:
  **the induction on `n` of Tag 094I**, for a derived tensor product supplied as a bifunctor,
  with the triangles of the source's proof and the conclusion of its base change step carried as
  hypotheses. Both are theorems downstream, so the tag is *not* registered here; it is
  registered on the `Stacks.ConstantSheaf` declaration
  `isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_isLE`
  in `StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces`, where both
  hypotheses are discharged.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_homology_derivedConstantSheaf`:
  the constant sheaf on a finitely generated `Λ`-module, placed in degree zero, has locally
  constant cohomology sheaves of finite type.
* `Stacks.ConstantSheaf.isFG_idealPowSuccQuot`: over a Noetherian ring `Iⁿ/Iⁿ⁺¹` is a finitely
  generated `Λ`-module.
* `Stacks.ConstantSheaf.module_finite_iff_finite_quotient`: a module over `Λ` and over `Λ/I`
  compatibly is finitely generated over one exactly when it is over the other.

## Implementation notes

**The derived tensor product enters as a bifunctor**, as in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove`: it enters as a
bifunctor `T` on `D(Sheaf J (ModuleCat Λ))` and `K ⊗^L_Λ M̲` is
`Stacks.ConstantSheaf.derivedTensorConstant`, the value of `T` at `K` and at the constant sheaf
on `M` placed in degree zero.

**Where one is constructed.** Every derived tensor product the library has is on sheaves of
modules over a sheaf of rings: `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`
for a sheaf of commutative rings on a `SmallCategory.{u}` site with all universes `u`, and
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` over an
`AlgebraicGeometry.RingedSite.{c, u, u}`, whose site objects live in a universe of their own
while its morphisms, structure sheaf and modules share one. Taking the structure sheaf to be the
constant sheaf of commutative rings on `Λ` and transporting along
`Stacks.ConstantRingModules.moduleSheafEquivalence` of
`StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheavesAsConstantRingModules` -- sheaves of
`Λ`-modules *are* the modules over the constant sheaf of rings on `Λ` -- gives a bifunctor on
`D(Sheaf J (ModuleCat.{u} Λ))`, and the two properties used below come with it: exactness in each
variable from the `exact_left` and `exact_right` fields of the derived tensor product data, and
the estimate from `Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor`, which is
right t-exactness in both variables. That is
`Stacks.ConstantRingModules.constantDerivedTensor` of
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantRingDerivedTensor`, where Tag 094I is
also registered with nothing assumed of the derived tensor product. What the route costs is the
universe convention: `Λ` and the modules lie in the morphism universe of the site, where the
statements here keep `max u v w` free.

**No exactness hypothesis on `T` is needed.** Tag 094H's reduction needs `T` to be exact in each
variable and to carry bounds above to their sum; the induction below needs neither, because the
only thing it asks of `T` is that the triangles exist, and those are hypotheses. The statement is
therefore weaker in its hypotheses than Tag 094H's, and no `CommShift` or `IsTriangulated`
instance appears.

**The base change step is carried in its conclusion form.** The source's step 4 is the
identification `K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ = (K ⊗^L_Λ Λ/I) ⊗^L_{Λ/I} Iⁿ/Iⁿ⁺¹`, which mentions a second
derived tensor product, over `Λ/I`, and so a second derived category
`D(Sheaf J (ModuleCat (Λ/I)))` together with a comparison between local constancy of finite type
over `Λ` and over `Λ/I`. Neither exists here. What the step is *for* is the single conclusion
that `K ⊗^L_Λ Iⁿ/Iⁿ⁺¹` has locally constant cohomology sheaves of finite type, and that is what
is carried: a hypothesis in the vocabulary of this file alone, implied by the identification plus
Tag 094H, hence weaker than the identification.

**The conclusion is stated over `Λ`, not over `Λ/Iⁿ`.** The source phrases it as a statement
about sheaves of `Λ/Iⁿ`-modules, but the derived tensor products live in
`D(Sheaf J (ModuleCat Λ))` and the source's own argument runs entirely inside the weak Serre
subcategory of `Mod(C, Λ)` of Tag 093U; a `Λ`-module killed by `Iⁿ` carries a unique compatible
`Λ/Iⁿ`-module structure, under which it is finitely generated over `Λ` exactly when it is over
`Λ/Iⁿ` (`Stacks.ConstantSheaf.module_finite_iff_finite_quotient`) and constant for one ring
exactly when constant for the other, so the two readings of the conclusion agree.

**Universes.** The module universe is `max u v w` and the coefficient ring is taken in
`Type (max u v w)`, as in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove`: at that universe
every sheafification hypothesis on `C` and on its slices is automatic, and the universe is stable
under slicing.

**The bridge between the two forms of "weak Serre subcategory"** — the closure form
`CategoryTheory.ObjectProperty.IsWeakSerreClass`, in which Tag 093U is stated, and the five term
exactness form `Stacks.WeakSerre.IsWeakSerre`, in which Tag 06UQ is stated — is
`Stacks.WeakSerre.isWeakSerre_of_isWeakSerreClass`, proved in
`StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage` and used here rather than
re-proved.

## What is proved elsewhere

Both hypotheses carried here are now theorems — not in this file, but downstream of it, so that
every step of the source's proof of Tag 094I is a theorem for an arbitrary `T` with the two
properties of a derived tensor product named above. The triangles are
`Stacks.ConstantSheaf.exists_distTriang_derivedTensorConstant` of
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.IdealPowerTriangles`, and the local constancy
of the graded pieces is proved in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces`, which is where the
094I registration sits. Each asks something more of `T` than this file does — the first
exactness in the second variable, the second also the estimate taking bounds above to their sum
— which is why the induction is stated here with them as hypotheses. A `T` with those properties
is `Stacks.ConstantRingModules.constantDerivedTensor`: see "Where one is constructed" above.

The rest of this section describes what those two steps are and why they are not available
*here*.

Tag 094I is not proved in this file, because two of the source's five steps are hypotheses
rather than theorems, and both are statements about the derived tensor product, which this file
does not fix.

* **The triangles.** `K ⊗^L_Λ -` applied to the short exact sequence
  `0 ⟶ Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ ⟶ 0` of constant sheaves yields a distinguished triangle; this
  is a property of the construction of the derived tensor product (Tag 06YU) and of the exactness
  of the constant sheaf functor on that sequence.
* **The base change identification**, discussed in the implementation notes. Beyond a derived
  tensor product over `Λ/I` it needs a change of rings comparison for local constancy of finite
  type, of which only the case of a ring *isomorphism* is available here.

What is proved is everything between them: the passage from Tag 093U to Tag 06UQ, the
triangulated closure that supplies the middle vertex, the finite generation of `Iⁿ/Iⁿ⁺¹` over a
Noetherian `Λ`, and the induction on `n` itself.

## References

* [Stacks Project, Tag 094I](https://stacks.math.columbia.edu/tag/094I)
* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.ConstantSheaf

universe w v u s

/-! ### The graded pieces of the `I`-adic filtration -/

section Modules

variable (Λ : Type s) [CommRing Λ]

/-- **The `Λ`-module `Iⁿ/Iⁿ⁺¹`**, as the quotient of the ideal `Iⁿ` by the submodule of those of
its elements that lie in `Iⁿ⁺¹`. -/
def idealPowSuccQuot (I : Ideal Λ) (n : ℕ) : ModuleCat.{s} Λ :=
  ModuleCat.of Λ (↥(I ^ n) ⧸ Submodule.comap (I ^ n).subtype (I ^ (n + 1)))

/-- **Over a Noetherian ring `Iⁿ/Iⁿ⁺¹` is a finitely generated `Λ`-module**: the ideal `Iⁿ` is
finitely generated, and finite generation passes to quotients. -/
theorem isFG_idealPowSuccQuot [IsNoetherianRing Λ] (I : Ideal Λ) (n : ℕ) :
    ModuleCat.isFG Λ (idealPowSuccQuot Λ I n) := by
  have : Module.Finite Λ ↥(I ^ n) := Module.Finite.of_fg (IsNoetherian.noetherian (I ^ n))
  rw [ModuleCat.isFG_iff]
  exact inferInstanceAs
    (Module.Finite Λ (↥(I ^ n) ⧸ Submodule.comap (I ^ n).subtype (I ^ (n + 1))))

/-- **Finite generation over `Λ` and over `Λ/I` agree** for a module carrying compatible
structures over both: `Λ/I` is a finitely generated `Λ`-module, and a module finitely generated
over `Λ` stays so after restricting the scalars to a quotient.

A `Λ`-module killed by `I` carries a unique such pair of structures, so this is the statement
that for such a module the two readings of "of finite type" coincide. -/
theorem module_finite_iff_finite_quotient (I : Ideal Λ) (M : Type*) [AddCommGroup M]
    [Module Λ M] [Module (Λ ⧸ I) M] [IsScalarTower Λ (Λ ⧸ I) M] :
    Module.Finite Λ M ↔ Module.Finite (Λ ⧸ I) M := by
  refine ⟨fun _ => Module.Finite.of_restrictScalars_finite Λ (Λ ⧸ I) M, fun _ => ?_⟩
  have : Module.Finite Λ (Λ ⧸ I) :=
    Module.Finite.of_surjective (Submodule.mkQ I) (Submodule.mkQ_surjective I)
  exact Module.Finite.trans (Λ ⧸ I) M

end Modules

/-! ### The derived tensor product with a constant sheaf -/

section Sheaves

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type (max u v w)) [CommRing Λ]

attribute [local instance] HasDerivedCategory.standard

/-- **The constant sheaf of `Λ`-modules in degree zero**, as a functor from `Λ`-modules to the
derived category of sheaves of `Λ`-modules. This is the object the source writes `M̲` and tensors
`K` with. -/
def derivedConstantSheaf :
    ModuleCat.{max u v w} Λ ⥤ DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) :=
  constantSheaf J (ModuleCat.{max u v w} Λ) ⋙
    DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) 0

/-- **`K ⊗^L_Λ M̲`**, for a bifunctor `T` on the derived category of sheaves of `Λ`-modules
standing for the derived tensor product: the value of `T` at `K` and at the constant sheaf on the
`Λ`-module `M`, placed in degree zero. -/
def derivedTensorConstant
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    (M : ModuleCat.{max u v w} Λ) : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) :=
  (T.obj K).obj ((derivedConstantSheaf J Λ).obj M)

section Noetherian

variable [IsNoetherianRing Λ]

/-- **The constant sheaf on a finitely generated `Λ`-module, placed in degree zero, has locally
constant cohomology sheaves of finite type.** Its cohomology is the constant sheaf itself in
degree zero and zero elsewhere, and a sheaf isomorphic to the constant sheaf on a finitely
generated module is locally constant of finite type. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedConstantSheaf
    (M : ModuleCat.{max u v w} Λ) (hM : ModuleCat.isFG Λ M) (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedConstantSheaf J Λ).obj M)) :=
  (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj
    (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ)
    (WeakSerre.isWeakSerre_of_isWeakSerreClass _) _
    (isFiniteTypeLocallyConstantModuleSheaf_of_constant J Λ hM (Iso.refl _))).2 i

/-- **The constant sheaf on `Iⁿ/Iⁿ⁺¹`, placed in degree zero, has locally constant cohomology
sheaves of finite type**, since `Iⁿ/Iⁿ⁺¹` is a finitely generated `Λ`-module. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedConstantSheaf_idealPowSuccQuot
    (I : Ideal Λ) (n : ℕ) (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        ((derivedConstantSheaf J Λ).obj (idealPowSuccQuot Λ I n))) :=
  isFiniteTypeLocallyConstantModuleSheaf_homology_derivedConstantSheaf J Λ _
    (isFG_idealPowSuccQuot Λ I n) i

/-- **Stacks Tag 094I, the induction on `n`.** Let `T` be a bifunctor on the derived category of
sheaves of `Λ`-modules standing for the derived tensor product over the Noetherian ring `Λ`, let
`K` be an object of that derived category and let `I ⊆ Λ` be an ideal. Suppose given, for every
`n ≥ 1`, a distinguished triangle

`K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ⁺¹ ⟶ K ⊗^L_Λ Λ/Iⁿ ⟶ (K ⊗^L_Λ Iⁿ/Iⁿ⁺¹)[1]`,

and suppose that each `K ⊗^L_Λ Iⁿ/Iⁿ⁺¹` has locally constant cohomology sheaves of finite type —
which is what the source's base change identification `K ⊗^L_Λ Iⁿ/Iⁿ⁺¹ =
(K ⊗^L_Λ Λ/I) ⊗^L_{Λ/I} Iⁿ/Iⁿ⁺¹` gives through Tag 094H. If `K ⊗^L_Λ Λ/I` has locally constant
cohomology sheaves of finite type, then so does `K ⊗^L_Λ Λ/Iⁿ` for every `n ≥ 1`.

The locally constant sheaves of finite type are a weak Serre subcategory by Tag 093U, so the
objects of the derived category all of whose cohomology sheaves are such form a triangulated
subcategory by Tag 06UQ; the inductive step is that subcategory containing the middle vertex of
the triangle at `n`, whose outer vertices are the inductive hypothesis and the base change
hypothesis. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow
    (T : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))) (I : Ideal Λ)
    (htriangle : ∀ n : ℕ, 1 ≤ n →
      ∃ (f : derivedTensorConstant J Λ T K (idealPowSuccQuot Λ I n) ⟶
          derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ (n + 1))))
        (g : derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ (n + 1))) ⟶
          derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ n)))
        (h : derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ n)) ⟶
          (derivedTensorConstant J Λ T K (idealPowSuccQuot Λ I n))⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈
          distTriang (DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ))))
    (hgraded : ∀ n : ℕ, 1 ≤ n → ∀ i : ℤ,
      IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
        ((DerivedCategory.homologyFunctor _ i).obj
          (derivedTensorConstant J Λ T K (idealPowSuccQuot Λ I n))))
    (hbase : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I)))))
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ n)))) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have e : derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I)) ≅
        derivedTensorConstant J Λ T K (ModuleCat.of Λ (Λ ⧸ I ^ 1)) :=
      (T.obj K).mapIso ((derivedConstantSheaf J Λ).mapIso
        (Submodule.quotEquivOfEq (I ^ 1) I (pow_one I)).symm.toModuleIso)
    exact fun i => ObjectProperty.prop_of_iso _
      ((DerivedCategory.homologyFunctor _ i).mapIso e) (hbase i)
  | succ n hn ih =>
    obtain ⟨f, g, h, hdist⟩ := htriangle n hn
    exact DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished
      (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ)
      (WeakSerre.isWeakSerre_of_isWeakSerreClass _)
      (Triangle.mk f g h) hdist (hgraded n hn) ih

end Noetherian

end Sheaves

end Stacks.ConstantSheaf

end
