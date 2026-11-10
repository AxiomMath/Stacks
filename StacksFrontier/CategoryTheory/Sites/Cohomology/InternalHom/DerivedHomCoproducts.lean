module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomProducts
public import StacksFrontier.CategoryTheory.Sites.Modules.DerivedCountableCoproducts
import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasiIso
import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.KFlatIntoKInjectiveIsKInjective

/-!
# Derived internal Hom out of a direct sum is the product of the derived internal Homs

Let `(𝒞, 𝒪)` be a ringed site, let `(Kₙ)` be a countable family of objects of `D(𝒪)` and let
`E ∈ D(𝒪)`. This file proves that the canonical map

`R𝑆heafHom_𝒪(⊕ₙ Kₙ, E) ⟶ ∏ₙ R𝑆heafHom_𝒪(Kₙ, E)`

induced by the coprojections is an isomorphism. This is the comparison that the last step of the
proof of [Stacks, Tag 0A0A] uses and that
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit` carries as its
hypothesis `hcomp`; the section "What this file does not contain" of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit` records
that no declaration of the library asserted it. The *covariant* counterpart —
`R𝑆heafHom_𝒪(K, -)` preserves countable powers — is
`AlgebraicGeometry.RingedSite.preservesLimit_derivedSheafHom`, and the argument below is that
argument run in the other variable.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_homSigmaComparison` — at the level of complexes, the
  internal Hom complex out of a direct sum is the product of the internal Hom complexes out of
  the summands. This is the contravariant companion of
  `AlgebraicGeometry.RingedSite.isIso_homPiComparison`.
* `AlgebraicGeometry.RingedSite.preservesLimit_derivedSheafHom_flip` — for a countable family
  `(Kₙ)` in `D(𝒪)`, the functor `R𝑆heafHom_𝒪(-, E) : D(𝒪)ᵒᵖ ⥤ D(𝒪)` preserves the product of
  the family `(op Kₙ)`, which is the opposite of the direct sum of the `Kₙ`.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison` — the comparison map
  `R𝑆heafHom_𝒪(⊕ Kₙ, E) ⟶ ∏ R𝑆heafHom_𝒪(Kₙ, E)` is an isomorphism, in exactly the shape of the
  hypothesis `hcomp` of
  `AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit`.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit'` and
  `AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit'` — the two
  consumers with `hcomp` discharged.
* `AlgebraicGeometry.RingedSite.isZero_obj_op_biproduct` and
  `AlgebraicGeometry.RingedSite.isZero_obj_op_pi` — the finite counterpart, for an arbitrary
  additive functor out of an opposite category: it annihilates a finite biproduct, equivalently a
  finite product, whose factors it annihilates. No limit is preserved here, so these are
  independent of everything above.
* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_single_pi` — the instance of that at the
  derived internal Hom for a finite product of sheaves placed in a single degree, which is what a
  dévissage along the stupid filtration of the extended alternating Čech complex consumes, the
  degree-`p` term of that complex being a product over the subsets of cardinality `p`. The
  instance for a finite product of objects of `D(𝒪)` is
  `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_pi` of
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/CompletionUnitIso.lean`.

## Implementation notes

**The shape of the argument.** It is the one of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomProducts.lean`, with the
variances exchanged. Write each `Kₙ` as the class of a K-flat complex `Aₙ`
(`AlgebraicGeometry.RingedSite.kFlatModel`) and `E` as the class of a K-injective complex `B`
(`AlgebraicGeometry.RingedSite.kInjectiveModel`). Then:

* the termwise direct sum `∐ A` of the complexes `Aₙ`, with the images under `Q` of the
  canonical injections, is the direct sum of the `Kₙ` in `D(𝒪)` ([Stacks, Tag 0A5L], via
  `derivedCategory_Q_preservesCoproductsOfShape`), sheaves of modules on a small site being
  Grothendieck abelian and therefore having exact countable direct sums;
* `SheafHom(∐ A, B)` is the termwise product of the complexes `SheafHom(Aₙ, B)`, which is
  `AlgebraicGeometry.RingedSite.isIso_homSigmaComparison`;
* `SheafHom(Aₙ, B)` is K-injective by [Stacks, Tag 0A96], `Aₙ` being K-flat and `B`
  K-injective, so the class of `SheafHom(∐ A, B)` is in turn the product of the classes of the
  `SheafHom(Aₙ, B)` ([Stacks, Tag 0BK6], via
  `AlgebraicGeometry.RingedSite.isLimit_fan_Q_pi`);
* and on a K-injective target the derived internal Hom is the class of the internal Hom complex,
  by `AlgebraicGeometry.RingedSite.derivedSheafHomComparison` and its naturality in the source,
  `AlgebraicGeometry.RingedSite.derivedSheafHomComparison_naturality_id_target`.

So the image of a direct-sum cofan is a product fan, which is the assertion. Note that `∐ A` is
*not* required to be K-flat: the model comparison needs K-injectivity of the target only, and
K-flatness of the summands enters solely through Tag 0A96 for the factors `SheafHom(Aₙ, B)`.

**Why the internal Hom complex turns a direct sum in its source into a product.** Dually to the
covariant case, the internal Hom complex is characterised by its sections
(`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv`) and
`AlgebraicGeometry.RingedSite.homMap` acts on them by `AlgebraicGeometry.RingedSite.cochainConj`,
that is by composition. So it suffices that, over every object `U` of the site and in every
degree, precomposition with the injections identifies the cochains out of `(∐ A)|_U` with
families of cochains out of the `Aₙ|_U`; and that holds because the value groups of a cochain are
morphism groups out of `((∐ A).X p)|_U`, which is a coproduct — coproducts of complexes are
formed degreewise (`CategoryTheory.Limits.PreservesColimit` of `HomologicalComplex.eval`) and
restriction to a slice site preserves them, being a left adjoint
(`Stacks.SheafOfModules.overFunctor_preservesColimits`). This is the one asymmetry with the
covariant file, which could appeal to the right adjointness of restriction instead; both are
available for a ringed site with no hypothesis on the slices.

**What Mathlib supplies.** The passage between the direct sum in `D(𝒪)` and the product in
`D(𝒪)ᵒᵖ` is `CategoryTheory.Limits.Cofan.IsColimit.op`, and the passage from a limit fan to
invertibility of the induced map into the product is
`CategoryTheory.Limits.Fan.nonempty_isLimit_iff_isIso_piLift`; neither is restated here. What
Mathlib does *not* have is the statement itself in any form that could be instantiated: the
internal hom of a monoidal closed category is known there to preserve colimits in its covariant
variable only (`CategoryTheory.MonoidalClosed`, via `ihom.adjunction`), and `D(𝒪)` carries no
monoidal closed structure in this development anyway.

**Countability.** The covariant statement is proved for powers indexed by `ℕ` because its input,
[Stacks, Tag 0BK6], is about countable products of K-injective complexes. Here countability is
needed for a second, independent reason: that `Q` carries the termwise direct sum to the direct
sum in `D(𝒪)` is [Stacks, Tag 0A5L], which the library has for countable families only
(`derivedCategory_Q_preservesCoproductsOfShape`). The complex-level statement
`isIso_homSigmaComparison` is free of both restrictions and is proved for an arbitrary index type
in `Type`.

**Tagging.** Nothing here carries a Stacks tag. The statement is a step inside the proof of
[Stacks, Tag 0A0A] — the Stacks text asserts it in the course of that proof and gives it no tag
of its own — and 0A0A is already carried, with this input assumed, by
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit`; the
complex-level half is not any of the assertions of Tags 0A8X, 0A90 or 0A96. So no tag matches
and none is attached.

## References

* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.RingedSite

/-! ### Generalities on coproduct cofans -/

/-- A functor which preserves a coproduct carries a coproduct cofan to a coproduct cofan. This is
the colimit dual of `AlgebraicGeometry.RingedSite.isLimit_fan_map`. -/
def isColimit_cofan_map {C D : Type*} [Category C] [Category D] {J : Type} {Y : J → C}
    (F : C ⥤ D) {t : Cofan Y} (ht : IsColimit t) [PreservesColimit (Discrete.functor Y) F] :
    IsColimit (Cofan.mk (F.obj t.pt) (fun j => F.map (t.inj j))) :=
  Cofan.isColimitMapCoconeEquiv F Y t (isColimitOfPreserves F ht)

/-! ### Generalities on finite biproducts -/

/-- **An additive contravariant functor annihilates a finite biproduct whose factors it
annihilates.** The identity of a finite biproduct is the sum `∑ j, π j ≫ ι j` of the idempotents
cutting out the factors, so the identity of its image is a finite sum of morphisms, each of which
factors through the image of one factor and therefore vanishes.

Unlike the coproduct statements of this file, no limit or colimit is preserved and no
countability enters: the finiteness of the index type is what turns the decomposition of the
identity into a *finite* sum, which additivity of the functor can carry across. -/
theorem isZero_obj_op_biproduct {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (G : Cᵒᵖ ⥤ D) [G.Additive]
    {J : Type} [Finite J] (A : J → C) [HasBiproduct A]
    (hA : ∀ j, IsZero (G.obj (op (A j)))) : IsZero (G.obj (op (⨁ A))) := by
  have := Fintype.ofFinite J
  rw [IsZero.iff_id_eq_zero, ← G.map_id]
  have hid : 𝟙 (op (⨁ A)) = (∑ j : J, biproduct.π A j ≫ biproduct.ι A j).op := by
    rw [biproduct.total]
    rfl
  rw [hid, op_sum, G.map_sum]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [op_comp, G.map_comp, (hA j).eq_of_tgt (G.map (biproduct.ι A j).op) 0, zero_comp]

/-- **An additive contravariant functor annihilates a finite product whose factors it
annihilates.** This is `AlgebraicGeometry.RingedSite.isZero_obj_op_biproduct` read through
`CategoryTheory.Limits.biproduct.isoProduct`, a finite product in a preadditive category being a
biproduct. -/
theorem isZero_obj_op_pi {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (G : Cᵒᵖ ⥤ D) [G.Additive]
    {J : Type} [Finite J] (A : J → C) [HasProduct A]
    (hA : ∀ j, IsZero (G.obj (op (A j)))) : IsZero (G.obj (op (∏ᶜ A))) := by
  have : HasBiproduct A := HasBiproduct.of_hasProduct A
  exact (isZero_obj_op_biproduct G A hA).of_iso (G.mapIso (biproduct.isoProduct A).op)

variable (X : RingedSite.{u, u, u})

attribute [local instance] hasMapBifunctor_sheafTensor

/-- A coproduct of complexes is a coproduct in every degree. -/
def isColimit_cofan_eval {J : Type}
    (A : J → CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [HasCoproduct A] (p : ℤ) :
    IsColimit (Cofan.mk ((∐ A).X p) (fun j => (Sigma.ι A j).f p)) :=
  isColimit_cofan_map (HomologicalComplex.eval _ _ p) (coproductIsCoproduct A)

/-- Restriction of sheaves of modules to a slice site preserves coproducts: it is a left adjoint,
pushforward along `CategoryTheory.Over.forget` being its right adjoint. -/
instance preservesColimit_overFunctor (U : X.C) {J : Type}
    (Y : J → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesColimit (Discrete.functor Y)
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) := by
  have h : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    Stacks.SheafOfModules.overFunctor_preservesColimits.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  have : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    preservesColimitsOfSize_shrink _
  infer_instance

/-- A coproduct of complexes is a coproduct in every degree after restriction to a slice site. -/
def isColimit_cofan_eval_over {J : Type}
    (A : J → CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [HasCoproduct A] (U : X.C) (p : ℤ) :
    IsColimit (Cofan.mk (((∐ A).X p).over U) (fun j => ((Sigma.ι A j).f p).over U)) :=
  isColimit_cofan_map
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (isColimit_cofan_eval X A p)

/-! ### The internal Hom complex turns a direct sum in its source into a product -/

section Sigma

variable {J : Type}
  (A : J → CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  [HasCoproduct A]
  (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **Precomposition with the injections identifies the cochains out of a direct sum with
families of cochains.** The value groups of a cochain are morphism groups out of a degree of the
direct sum complex restricted to the slice site, and that is a coproduct. -/
theorem bijective_cochainConj_sigma (U : X.C) (n : ℤ) :
    Function.Bijective (fun (c : Cochain (restrictComplex X (∐ A) U) (restrictComplex X B U) n)
      (j : J) => cochainConj X U (Sigma.ι A j) (𝟙 B) c) := by
  have key (c : Cochain (restrictComplex X (∐ A) U) (restrictComplex X B U) n) (j : J)
      (p q : ℤ) (hpq : p + n = q) :
      (cochainConj X U (Sigma.ι A j) (𝟙 B) c).v p q hpq =
        ((Sigma.ι A j).f p).over U ≫ c.v p q hpq := by
    rw [cochainConj_v, HomologicalComplex.id_f]
    have hid : SheafOfModules.Hom.over (𝟙 (B.X q)) U = 𝟙 ((B.X q).over U) := rfl
    rw [hid]
    exact congrArg (fun z => ((Sigma.ι A j).f p).over U ≫ z) (Category.comp_id (c.v p q hpq))
  refine ⟨fun c c' h => ?_, fun w => ?_⟩
  · refine Cochain.ext _ _ fun p q hpq => ?_
    refine Cofan.IsColimit.hom_ext (isColimit_cofan_eval_over X A U p) _ _ fun j => ?_
    have h1 : (cochainConj X U (Sigma.ι A j) (𝟙 B) c).v p q hpq =
        (cochainConj X U (Sigma.ι A j) (𝟙 B) c').v p q hpq :=
      congrArg (fun z : Cochain (restrictComplex X (A j) U) (restrictComplex X B U) n =>
        z.v p q hpq) (congrFun h j)
    rwa [key c j p q hpq, key c' j p q hpq] at h1
  · refine ⟨Cochain.mk fun p q hpq =>
      Cofan.IsColimit.desc (isColimit_cofan_eval_over X A U p) fun j => (w j).v p q hpq, ?_⟩
    funext j
    refine Cochain.ext _ _ fun p q hpq => ?_
    rw [key _ j p q hpq, Cochain.mk_v]
    exact Cofan.IsColimit.fac (isColimit_cofan_eval_over X A U p) _ j

variable [HasProduct fun j => (sheafHomComplex X (A j) B).obj]

/-- The comparison morphism from the internal Hom complex out of a direct sum to the product of
the internal Hom complexes out of the summands, induced by the injections. -/
def homSigmaComparison :
    (sheafHomComplex X (∐ A) B).obj ⟶ ∏ᶜ fun j => (sheafHomComplex X (A j) B).obj :=
  Pi.lift fun j => homMap X (Sigma.ι A j) (𝟙 B)

/-- The defining property of `AlgebraicGeometry.RingedSite.homSigmaComparison`. -/
theorem homSigmaComparison_π (j : J) :
    homSigmaComparison X A B ≫ Pi.π (fun j => (sheafHomComplex X (A j) B).obj) j =
      homMap X (Sigma.ι A j) (𝟙 B) := Pi.lift_comp_π _ _

omit [HasProduct fun j => (sheafHomComplex X (A j) B).obj] in
/-- **The induced maps of internal Hom complexes identify the sections of the internal Hom
complex out of a direct sum with families of sections.** This is
`AlgebraicGeometry.RingedSite.bijective_cochainConj_sigma` read through
`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv`. -/
theorem bijective_homMap_sections_sigma (U : X.C) (n : ℤ) :
    Function.Bijective (fun (s : ((sheafHomComplex X (∐ A) B).obj.X n).val.obj (op U))
      (j : J) => ((homMap X (Sigma.ι A j) (𝟙 B)).f n).val.app (op U) s) := by
  have hfac : (fun (s : ((sheafHomComplex X (∐ A) B).obj.X n).val.obj (op U)) (j : J) =>
      ((homMap X (Sigma.ι A j) (𝟙 B)).f n).val.app (op U) s) =
      (Equiv.piCongrRight fun j =>
          ((sheafHomComplex X (A j) B).sectionsEquiv U n).symm.toEquiv) ∘
        ((fun c (j : J) => cochainConj X U (Sigma.ι A j) (𝟙 B) c) ∘
          (sheafHomComplex X (∐ A) B).sectionsEquiv U n) :=
    rfl
  rw [hfac]
  exact (Equiv.piCongrRight _).bijective.comp
    ((bijective_cochainConj_sigma X A B U n).comp
      ((sheafHomComplex X (∐ A) B).sectionsEquiv U n).bijective)

/-- The comparison morphism is an isomorphism in every degree. -/
theorem isIso_f_homSigmaComparison (n : ℤ) : IsIso ((homSigmaComparison X A B).f n) := by
  have hsec : ∀ V : X.Cᵒᵖ, IsIso (((homSigmaComparison X A B).f n).val.app V) := by
    rintro ⟨U⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    refine bijective_of_comp_bijective
      (f := fun s => ((homSigmaComparison X A B).f n).val.app (op U) s)
      (g := fun (x : ((∏ᶜ fun j => (sheafHomComplex X (A j) B).obj).X n).val.obj (op U))
        (j : J) => ((Pi.π (fun j => (sheafHomComplex X (A j) B).obj) j).f n).val.app (op U) x)
      (bijective_fan_proj (isLimit_fan_sections X _
        (isLimit_fan_eval X (fun j => (sheafHomComplex X (A j) B).obj) n) U)) ?_
    convert bijective_homMap_sections_sigma X A B U n using 1
    funext s j
    simp only [Function.comp_apply]
    rw [← sections_comp_apply X ((homSigmaComparison X A B).f n)
      ((Pi.π (fun j => (sheafHomComplex X (A j) B).obj) j).f n) (op U) s,
      ← HomologicalComplex.comp_f, homSigmaComparison_π]
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ hsec

/-- **The internal Hom complex out of a direct sum is the product of the internal Hom complexes
out of the summands.** The comparison morphism induced by the injections is an isomorphism of
complexes. This is the contravariant companion of
`AlgebraicGeometry.RingedSite.isIso_homPiComparison`. -/
theorem isIso_homSigmaComparison : IsIso (homSigmaComparison X A B) := by
  have : ∀ n, IsIso ((homSigmaComparison X A B).f n) := isIso_f_homSigmaComparison X A B
  exact HomologicalComplex.Hom.isIso_of_components _

end Sigma

/-! ### Derived internal Hom out of a countable direct sum -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-! #### Derived internal Hom out of a finite product -/

/-- **Vanishing of the derived internal Hom into `K` is stable under finite products of sheaves
placed in a single degree.** For a family of sheaves of `𝒪`-modules indexed by a finite type, if
`R𝑆heafHom_𝒪((A j)[-i], K)` vanishes for every `j` then so does
`R𝑆heafHom_𝒪((∏ A j)[-i], K)`.

This is the analogue of `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_pi` with the product
formed in the abelian category of sheaves of modules rather than in `D(𝒪)`, which is where the
terms of a complex live; the single functor `(-)[-i]` need not be known to preserve the product,
because it is additive and the proof only uses the decomposition of the identity of a finite
biproduct. -/
theorem isZero_derivedSheafHom_single_pi
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (i : ℤ) {J : Type} [Finite J]
    (A : J → SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [HasProduct A]
    (hA : ∀ j, IsZero (((derivedSheafHomBifunctor X).obj
      (op ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj (A j)))).obj K)) :
    IsZero (((derivedSheafHomBifunctor X).obj
      (op ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj (∏ᶜ A)))).obj K) :=
  isZero_obj_op_pi
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).op ⋙
      (derivedSheafHomBifunctor X).flip.obj K) A hA

/-- Sheaves of modules on a small site have exact countable direct sums, being Grothendieck
abelian. This is the hypothesis of [Stacks, Tag 0A5L]. -/
theorem hasExactCountableDirectSums_sheafOfModules :
    HasExactCountableDirectSums (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  hasExactCountableDirectSums_of_isGrothendieckAbelian.{u} _

/-- **`Q` carries the termwise direct sum of a countable family of complexes of `𝒪`-modules to
the direct sum in `D(𝒪)`.** This is [Stacks, Tag 0A5L]. -/
instance preservesColimitsOfShape_discrete_Q (J : Type) [Countable J] :
    PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  derivedCategory_Q_preservesCoproductsOfShape _
    (hasExactCountableDirectSums_sheafOfModules X) J

/-- **Derived internal Hom into the class of a K-injective complex turns the direct sum of the
classes of K-flat complexes into a product.** -/
theorem preservesLimit_derivedSheafHom_flip_model
    (A : ℕ → CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [HasCoproduct A] (hA : ∀ j, Stacks.SheafOfModules.IsKFlat X.O (A j))
    (B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    PreservesLimit (Discrete.functor fun j : ℕ => op (DerivedCategory.Q.obj (A j)))
      ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj B)) := by
  set F := (derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj B)
  set C : ℕ → CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
    fun j => (sheafHomComplex X (A j) B).obj
  have hfan : IsLimit (Fan.mk (op (DerivedCategory.Q.obj (∐ A)))
      (fun j : ℕ => (DerivedCategory.Q.map (Sigma.ι A j)).op)) :=
    Cofan.IsColimit.op (isColimit_cofan_map DerivedCategory.Q (coproductIsCoproduct A))
  refine preservesLimit_of_preserves_limit_cone hfan ?_
  refine (Fan.isLimitMapConeEquiv F
    (fun j : ℕ => op (DerivedCategory.Q.obj (A j))) _).symm ?_
  have hiso := isIso_homSigmaComparison X A B
  refine isLimit_fan_of_iso (isLimit_fan_Q_pi C
    fun j => isKInjective_sheafHomComplex_of_isKFlat X (A j) B (hA j)) _
    (derivedSheafHomComparison X (∐ A) B ≪≫
      DerivedCategory.Q.mapIso (asIso (homSigmaComparison X A B)))
    (fun j => (derivedSheafHomComparison X (A j) B).symm) _ (fun j => ?_)
  have hnat := derivedSheafHomComparison_naturality_id_target X B (Sigma.ι A j)
  have hθ : DerivedCategory.Q.map (homSigmaComparison X A B) ≫
      DerivedCategory.Q.map (Pi.π C j) =
      DerivedCategory.Q.map (homMap X (Sigma.ι A j) (𝟙 B)) := by
    rw [← DerivedCategory.Q.map_comp, homSigmaComparison_π]
  rw [← Iso.eq_comp_inv] at hnat
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom, fan_mk_proj]
  rw [Category.assoc, ← Category.assoc (DerivedCategory.Q.map (homSigmaComparison X A B)), hθ,
    ← Category.assoc]
  exact hnat

/-- **Derived internal Hom into a fixed object turns a countable direct sum into a product.** For
every `E ∈ D(𝒪)` and every countable family `(Kₙ)` of objects of `D(𝒪)`, the functor
`R𝑆heafHom_𝒪(-, E) : D(𝒪)ᵒᵖ ⥤ D(𝒪)` preserves the product of the family `(op Kₙ)` in `D(𝒪)ᵒᵖ`,
that is it carries the direct sum of the `Kₙ` to the product of the `R𝑆heafHom_𝒪(Kₙ, E)`. -/
theorem preservesLimit_derivedSheafHom_flip
    (K : ℕ → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    PreservesLimit (Discrete.functor fun n : ℕ => op (K n))
      ((derivedSheafHomBifunctor X).flip.obj E) := by
  have hmodel : PreservesLimit
      (Discrete.functor fun n : ℕ => op (DerivedCategory.Q.obj (kFlatModel X (K n))))
      ((derivedSheafHomBifunctor X).flip.obj
        (DerivedCategory.Q.obj (kInjectiveModel X E))) := by
    have : (kInjectiveModel X E).IsKInjective := isKInjective_kInjectiveModel X E
    exact preservesLimit_derivedSheafHom_flip_model X (fun n => kFlatModel X (K n))
      (fun n => isKFlat_kFlatModel X (K n)) (kInjectiveModel X E)
  have hK : PreservesLimit (Discrete.functor fun n : ℕ => op (K n))
      ((derivedSheafHomBifunctor X).flip.obj
        (DerivedCategory.Q.obj (kInjectiveModel X E))) :=
    preservesLimit_of_iso_diagram _
      (Discrete.natIso (F := Discrete.functor fun n : ℕ =>
          op (DerivedCategory.Q.obj (kFlatModel X (K n))))
        (G := Discrete.functor fun n : ℕ => op (K n))
        (fun n => (kFlatModelIso X (K n.as)).symm.op))
  exact preservesLimit_of_natIso _
    ((derivedSheafHomBifunctor X).flip.mapIso (kInjectiveModelIso X E))

/-- **Derived internal Hom out of a countable direct sum is the product of the derived internal
Homs out of the summands.** The canonical map
`R𝑆heafHom_𝒪(⊕ Kₙ, E) ⟶ ∏ R𝑆heafHom_𝒪(Kₙ, E)` induced by the coprojections is an
isomorphism. -/
theorem isIso_pi_lift_derivedSheafHom_sigma
    (K : ℕ → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (Pi.lift (fun n : ℕ ↦
        ((derivedSheafHomBifunctor X).flip.obj E).map (Sigma.ι K n).op) :
      ((derivedSheafHomBifunctor X).flip.obj E).obj (op (∐ K)) ⟶
        ∏ᶜ fun n : ℕ ↦ ((derivedSheafHomBifunctor X).flip.obj E).obj (op (K n))) := by
  have := preservesLimit_derivedSheafHom_flip X K E
  exact (Fan.nonempty_isLimit_iff_isIso_piLift
      (Fan.mk (((derivedSheafHomBifunctor X).flip.obj E).obj (op (∐ K)))
        (fun n : ℕ ↦ ((derivedSheafHomBifunctor X).flip.obj E).map (Sigma.ι K n).op))).mp
    ⟨isLimit_fan_map ((derivedSheafHomBifunctor X).flip.obj E)
      (Cofan.IsColimit.op (coproductIsCoproduct K))⟩

variable
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The direct sum comparison of Stacks 0A0A**, in the shape of the hypothesis `hcomp` of
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit`: for a system
`F : ℕ ⥤ D(𝒪)` and an object `E` of `D(𝒪)`, the canonical map
`R𝑆heafHom_𝒪(⊕ Fₙ, E) ⟶ ∏ R𝑆heafHom_𝒪(Fₙ, E)` is an isomorphism. -/
theorem isIso_derivedSheafHomSigmaComparison
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (Pi.lift (fun n : ℕ ↦
        ((derivedSheafHomBifunctor X).flip.obj E).map (Sigma.ι F.obj n).op) :
      ((derivedSheafHomBifunctor X).flip.obj E).obj (op (∐ F.obj)) ⟶
        ∏ᶜ fun n : ℕ ↦ (derivedSheafHomSystem X F E).obj (op n)) :=
  isIso_pi_lift_derivedSheafHom_sigma X F.obj E

/-- **Derived internal Hom out of a derived colimit is the derived limit of the derived internal
Homs out of the terms**, unconditionally: if `K = hocolim Fₙ` then
`R𝑆heafHom_𝒪(K, E) = R lim R𝑆heafHom_𝒪(Fₙ, E)`.

This is `AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit` with
its hypothesis `hcomp` discharged by
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomSigmaComparison`. -/
theorem isDerivedLimit_derivedSheafHom_of_isHomotopyColimit'
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (derivedSheafHomSystem X F E)
      (((derivedSheafHomBifunctor X).flip.obj E).obj (op K)) :=
  isDerivedLimit_derivedSheafHom_of_isHomotopyColimit X F E
    (isIso_derivedSheafHomSigmaComparison X F E) hK

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **Stacks 0A0A with its direct-sum comparison discharged.** Only clause 3 of Stacks 08JJ
remains as a hypothesis: for a system `(Fₙ)` of objects of `D(𝒪)` and `K = hocolim Fₙ`,

`R𝑆heafHom_𝒪(K, E) = R lim (E ⊗^𝐋_𝒪 Fₙ^∨)`,

granted that the canonical map `E ⊗^𝐋_𝒪 Fₙ^∨ ⟶ R𝑆heafHom_𝒪(Fₙ, E)` of Stacks 08JD is an
isomorphism for every `n`.

No tag is attached: this is
`AlgebraicGeometry.RingedSite.isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit`, which
carries the tag 0A0A, with one of its two hypotheses supplied. -/
theorem isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit'
    (T : Stacks.SheafOfModules.DerivedTensorProduct X)
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hdual : ∀ n : ℕ, IsIso (derivedTensorDualToSheafHom X T (F.obj n) E))
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (tensorDerivedDualSystem X T F E)
      (((derivedSheafHomBifunctor X).flip.obj E).obj (op K)) :=
  isDerivedLimit_tensorDerivedDual_of_isHomotopyColimit X T F E
    (isIso_derivedSheafHomSigmaComparison X F E) hdual hK

end Derived

end AlgebraicGeometry.RingedSite

end
