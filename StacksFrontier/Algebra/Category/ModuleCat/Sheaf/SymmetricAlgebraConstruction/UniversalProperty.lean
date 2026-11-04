module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sheafify

/-!
# The universal property of the sectionwise symmetric algebra

`PresheafOfModules.symPowIntGradedAlgebra F` is the sectionwise symmetric algebra of a presheaf
of modules `F`. This file proves that it is *universal*: a degreewise morphism out of it into any
graded algebra of presheaves of modules carrying a pairwise-commuting degree-one generator exists
and is unique, as a unital homomorphism of graded algebras. Through
`Stacks.GradedAlgebra.isSymmetricAlgebra_sheafify` that is the missing half of
`SheafOfModules.GradedAlgebra.IsSymmetricAlgebra` for the sheafified algebra, so the headline
result is `PresheafOfModules.isSymmetricAlgebra_symmetricAlgebraSheafify`: the sheafification of
the sectionwise symmetric algebra **is** the symmetric algebra of the sheafified module, in the
sense of Stacks Section 17.21.

## Main definitions

* `Stacks.GradedAlgebra.cmpSectionsInt`: the comparison map on sections in an integer degree —
  lift a section of the symmetric algebra of the sections of `F` into the ungraded realization of
  the target, then project onto the degree-`n` summand. For a nonnegative degree it is
  `Stacks.GradedAlgebra.cmpSections` on the nose, and in a negative degree it is zero because its
  source is.
* `Stacks.GradedAlgebra.cmpInt`: the resulting morphism `symPowInt n F ⟶ Pc n` of presheaves of
  modules.
* `Stacks.GradedAlgebra.unitalHomInt`: the two bundled together — the unital homomorphism
  `symPowIntGradedAlgebra F ⟶ A` extending a pairwise-commuting degree-one generator of `A`.

## Main results

* `Stacks.GradedAlgebra.incl_cmpSectionsInt`: **the lift of a degree-`n` section is homogeneous
  of degree `n`.** This is what makes the comparison multiplicative, and it is the one fact that
  needs an induction: by `SymmetricAlgebra.symmetricPower_eq_span_prod_ι` it is enough to check
  it on a product of `n` degree-one generators, where
  `SymmetricAlgebra.liftComm_prod_ι` and `Stacks.GradedAlgebra.incl_homogeneousProd` identify the
  lift with `Stacks.GradedAlgebra.incl n` of an ordered product.
* `Stacks.GradedAlgebra.unitalHom_app_prod_ι`: **a unital homomorphism out of the sectionwise
  symmetric algebra is determined on products of degree-one generators** by its degree-one
  component. With `SymPow.ext_of_prod_ι` this is the uniqueness half.
* `Stacks.GradedAlgebra.existsUnique_unitalHom_symPowInt`: **the universal property**, in exactly
  the shape `Stacks.GradedAlgebra.isUniversal_sheafify` consumes.
* `PresheafOfModules.isSymmetricAlgebra_symmetricAlgebraSheafify`:
  `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra (symmetricAlgebraSheafify α F)
  (symmetricAlgebraSheafifyGen α F)`.

## Implementation notes

**Why the comparison is defined uniformly in the degree.** `Stacks.GradedAlgebra.cmpSections` is
indexed by `ℕ`, and a graded algebra in the sense of `SheafOfModules.GradedAlgebra` is indexed by
`ℤ`. Rather than extend the `ℕ`-indexed map by zero in negative degrees — which puts a case
analysis into the statement of every lemma about it — `cmpSectionsInt` is defined by the same
formula for *every* integer degree, with `SymPow.symmetricPowerInt` as its source. In a negative
degree that source is the zero submodule, so the map is zero automatically, and the identity
`cmpSectionsInt (k : ℤ) = cmpSections k` holds by `rfl`, which is what lets
`cmpSections_prod_ι` and `cmpSections_naturality` be reused verbatim. The only two places a case
analysis on the sign of the degree survives are `cmpSectionsInt_naturality` and
`incl_cmpSectionsInt`, where it is genuinely needed.

**Degrees of ordered products.** `Stacks.GradedAlgebra.homogeneousProd` multiplies on the right,
so a product of `k + 1` degree-one sections has degree `(k : ℤ) + 1`, which is *definitionally*
`((k + 1 : ℕ) : ℤ)`. That is what makes the induction in `unitalHom_app_prod_ι` transport-free:
the `map_mul` law of a unital homomorphism is applied at `(i, j) = ((k : ℤ), 1)` and its
conclusion lands in the degree the inductive statement asks for, with no `cast`.

**Universes.** Unchanged from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification`: the ring universe
`w` and the module universe `max w a` are tied together because `SymmetricAlgebra R M` for
`R : Type w` and `M : Type a` lives in `Type (max w a)`.

**No `@[stacks]` tag.** Tag 01CG is the assertion that the comparison map from the presheaf of
sectionwise symmetric powers into `Symⁿ F` becomes an isomorphism after sheafification. That is
*not* what is proved here: what is proved is the universal property of the sheafified algebra,
and deducing 01CG from it additionally needs the identification of
`PresheafOfModules.symPowInt (n : ℤ) F` with `PresheafOfModules.symPow n F`, against which
`SheafOfModules.GradedAlgebra.symPowCmp` is stated. So nothing below is tagged.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w a

namespace Stacks.GradedAlgebra

section Comparison

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (A : Stacks.GradedAlgebra Pc) {F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (gen : F ⟶ Pc 1)

/-- **The comparison map on sections, in an integer degree.** A section of the degree-`n`
symmetric power of the sections of `F` is lifted into the ungraded realization of the graded
algebra and projected onto the degree-`n` summand.

The formula is the same for every integer degree: in a negative degree the source is the zero
submodule, so the map is zero, and in a nonnegative degree this is
`Stacks.GradedAlgebra.cmpSections` on the nose (`cmpSectionsInt_natCast`). -/
noncomputable def cmpSectionsInt (hc : A.GenCommutes gen) (n : ℤ) (X : Cᵒᵖ) :
    SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →ₗ[(O ⋙ forget₂ _
      RingCat).obj X] (Pc n).obj X :=
  (A.proj X n).comp
    (({ toFun := fun x => A.liftTotal gen hc X x
        map_add' := fun x y => map_add (A.liftTotal gen hc X) x y
        map_smul' := fun r x => SymmetricAlgebra.liftComm_smul r x } :
          SymmetricAlgebra ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) →ₗ[(O ⋙ forget₂ _
            RingCat).obj X] A.Total X).comp
      (SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)).subtype)

/-- The integer-degree comparison map sends a section to the degree-`n` component of its lift
into the ungraded realization. -/
theorem cmpSectionsInt_apply (hc : A.GenCommutes gen) (n : ℤ) (X : Cᵒᵖ)
    (x : SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    A.cmpSectionsInt gen hc n X x = A.proj X n (A.liftTotal gen hc X x) := rfl

/-- In a nonnegative degree the integer-degree comparison map is
`Stacks.GradedAlgebra.cmpSections`. -/
theorem cmpSectionsInt_natCast (hc : A.GenCommutes gen) (k : ℕ) (X : Cᵒᵖ) :
    A.cmpSectionsInt gen hc (k : ℤ) X = A.cmpSections gen hc k X := rfl

/-- **The lift of a degree-`n` section is homogeneous of degree `n`.** This is the fact that
makes the comparison map multiplicative: the lift of a section of `Symⁿ` into the ungraded
realization is `Stacks.GradedAlgebra.incl n` of its image under the comparison map.

For a nonnegative degree the products of `n` degree-one generators span `Symⁿ`
(`SymmetricAlgebra.symmetricPower_eq_span_prod_ι`) and on such a product the lift is an ordered
product of degree-one sections (`SymmetricAlgebra.liftComm_prod_ι`), hence homogeneous by
`Stacks.GradedAlgebra.incl_homogeneousProd`; the property is preserved by sums and scalars. In a
negative degree the section is zero. -/
theorem incl_cmpSectionsInt (hc : A.GenCommutes gen) (n : ℤ) (X : Cᵒᵖ)
    (x : SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    A.incl n (A.cmpSectionsInt gen hc n X x) = A.liftTotal gen hc X x := by
  obtain k | k := n
  · obtain ⟨z, hz⟩ := x
    have key : ∀ z ∈ SymPow.symmetricPower k ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X),
        A.incl (k : ℤ) (A.proj X (k : ℤ) (A.liftTotal gen hc X z)) =
          A.liftTotal gen hc X z := by
      intro z hz
      rw [SymmetricAlgebra.symmetricPower_eq_span_prod_ι] at hz
      induction hz using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨s, rfl⟩ := hy
          have hprod : A.liftTotal gen hc X
              (∏ i : Fin k, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i)) =
              A.incl (k : ℤ) (A.homogeneousProd X k fun i => gen.app X (s i)) := by
            rw [liftTotal, SymmetricAlgebra.liftComm_prod_ι,
              A.incl_homogeneousProd X k fun i => gen.app X (s i)]
            rfl
          rw [hprod, A.proj_incl]
      | zero =>
          rw [map_zero, map_zero]
          exact A.incl_zero _
      | add y z _ _ hy hz => rw [map_add, map_add, A.incl_add, hy, hz]
      | smul r y _ hy =>
          rw [show A.liftTotal gen hc X (r • y) = r • A.liftTotal gen hc X y from
              SymmetricAlgebra.liftComm_smul r y, map_smul, A.incl_smul, hy]
    exact key z hz
  · have hx : x = 0 :=
      SymPow.eq_zero_of_neg_of_mem_symmetricPowerInt _ _ (Int.negSucc_lt_zero k) x
    rw [hx, map_zero, A.incl_zero]
    exact (map_zero (A.liftTotal gen hc X)).symm

/-- The integer-degree comparison map commutes with restriction. In a nonnegative degree this is
`Stacks.GradedAlgebra.cmpSections_naturality`; in a negative degree both sides vanish. -/
theorem cmpSectionsInt_naturality (hc : A.GenCommutes gen) (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : SymPow.symmetricPowerInt n ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)) :
    (Pc n).map f (A.cmpSectionsInt gen hc n X x) =
      A.cmpSectionsInt gen hc n Y
        (SymPow.symMapIntₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ f) x) := by
  obtain k | k := n
  · exact A.cmpSections_naturality gen hc k f x
  · have hx : x = 0 :=
      SymPow.eq_zero_of_neg_of_mem_symmetricPowerInt _ _ (Int.negSucc_lt_zero k) x
    rw [hx, map_zero, map_zero, map_zero, map_zero]
    rfl

/-- **The comparison morphism in an integer degree.** The presheaf of sectionwise symmetric
powers in degree `n` maps to the degree-`n` piece of a graded algebra of presheaves of modules
carrying a pairwise-commuting degree-one generator. -/
noncomputable def cmpInt (hc : A.GenCommutes gen) (n : ℤ) :
    PresheafOfModules.symPowInt n F ⟶ Pc n where
  app X := ModuleCat.ofHom (A.cmpSectionsInt gen hc n X)
  naturality f := ModuleCat.hom_ext (LinearMap.ext fun x =>
    (A.cmpSectionsInt_naturality gen hc n f x).symm)

/-- **The lift of a local section of `symPowInt n F` is homogeneous of degree `n`**, in the
spelling the multiplicativity proof below is written in: `incl_cmpSectionsInt` with the local
section read through `PresheafOfModules.symPowIntVal`. -/
theorem incl_cmpInt (hc : A.GenCommutes gen) (n : ℤ) (X : Cᵒᵖ)
    (x : (PresheafOfModules.symPowInt n F).obj X) :
    A.incl n (PresheafOfModules.Hom.app (A.cmpInt gen hc n) X x) =
      A.liftTotal gen hc X (PresheafOfModules.symPowIntVal x) :=
  A.incl_cmpSectionsInt gen hc n X x

/-- **The comparison morphism is multiplicative on homogeneous local sections.** Both sides
become `Stacks.GradedAlgebra.incl` of the same element of the ungraded realization, by
`incl_cmpSectionsInt` and `Stacks.GradedAlgebra.incl_mul_incl`, and
`Stacks.GradedAlgebra.proj_incl` recovers them from it. -/
theorem cmpInt_map_mul (hc : A.GenCommutes gen) (i j : ℤ) (X : Cᵒᵖ)
    (x : (PresheafOfModules.symPowInt i F).obj X)
    (y : (PresheafOfModules.symPowInt j F).obj X) :
    PresheafOfModules.Hom.app (A.cmpInt gen hc (i + j)) X
        ((PresheafOfModules.symPowIntMul F i j).app X x y) =
      (A.mul i j).app X (PresheafOfModules.Hom.app (A.cmpInt gen hc i) X x)
        (PresheafOfModules.Hom.app (A.cmpInt gen hc j) X y) := by
  have key : A.incl (i + j) (PresheafOfModules.Hom.app (A.cmpInt gen hc (i + j)) X
        ((PresheafOfModules.symPowIntMul F i j).app X x y)) =
      A.incl (i + j) ((A.mul i j).app X
        (PresheafOfModules.Hom.app (A.cmpInt gen hc i) X x)
        (PresheafOfModules.Hom.app (A.cmpInt gen hc j) X y)) := by
    rw [← A.incl_mul_incl]
    simp only [A.incl_cmpInt]
    rw [PresheafOfModules.symPowIntVal_mul F i j X x y, map_mul]
  exact (A.proj_incl X (i + j) _).symm.trans
    ((congrArg (A.proj X (i + j)) key).trans (A.proj_incl X (i + j) _))

/-- **The comparison morphism carries the unit to the unit.** -/
theorem cmpInt_map_one (hc : A.GenCommutes gen) (X : Cᵒᵖ) :
    PresheafOfModules.Hom.app (A.cmpInt gen hc 0) X
        ((PresheafOfModules.symPowIntOne F).eval X) = A.one.eval X := by
  have key : A.incl 0 (PresheafOfModules.Hom.app (A.cmpInt gen hc 0) X
        ((PresheafOfModules.symPowIntOne F).eval X)) = A.incl 0 (A.one.eval X) := by
    rw [A.incl_cmpInt, PresheafOfModules.symPowIntVal_one, map_one, ← A.one_eq_incl X]
  exact (A.proj_incl X 0 _).symm.trans ((congrArg (A.proj X 0) key).trans (A.proj_incl X 0 _))

/-- **The comparison morphism carries the degree-one generator of the sectionwise symmetric
algebra to the given generator.** -/
theorem cmpInt_app_gen (hc : A.GenCommutes gen) (X : Cᵒᵖ) (s : F.obj X) :
    PresheafOfModules.Hom.app (A.cmpInt gen hc 1) X
        (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen F) X s) =
      PresheafOfModules.Hom.app gen X s := by
  have key : A.incl 1 (PresheafOfModules.Hom.app (A.cmpInt gen hc 1) X
        (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen F) X s)) =
      A.incl 1 (PresheafOfModules.Hom.app gen X s) := by
    rw [A.incl_cmpInt, PresheafOfModules.symPowIntVal_gen, liftTotal,
      SymmetricAlgebra.liftComm_ι]
    rfl
  exact (A.proj_incl X 1 _).symm.trans ((congrArg (A.proj X 1) key).trans (A.proj_incl X 1 _))

/-- **The unital homomorphism out of the sectionwise symmetric algebra** determined by a
pairwise-commuting degree-one generator of a graded algebra of presheaves of modules. -/
noncomputable def unitalHomInt (hc : A.GenCommutes gen) :
    UnitalHom (PresheafOfModules.symPowIntGradedAlgebra F) A where
  app := A.cmpInt gen hc
  map_mul := A.cmpInt_map_mul gen hc
  map_one := A.cmpInt_map_one gen hc

/-- The degree-`n` component of `Stacks.GradedAlgebra.unitalHomInt` is the comparison
morphism `Stacks.GradedAlgebra.cmpInt` in degree `n`. -/
theorem unitalHomInt_app (hc : A.GenCommutes gen) (n : ℤ) :
    (A.unitalHomInt gen hc).app n = A.cmpInt gen hc n := rfl

/-! ### Uniqueness -/

/-- **A unital homomorphism out of the sectionwise symmetric algebra is determined on products of
degree-one generators by its degree-one component.** The induction is on the number of factors,
with the inductive step the `map_mul` law at degrees `((k : ℤ), 1)`; because
`Stacks.GradedAlgebra.homogeneousProd` multiplies on the right, that law lands in degree
`(k : ℤ) + 1`, which is definitionally `((k + 1 : ℕ) : ℤ)`, so no transport appears. -/
theorem unitalHom_app_prod_ι
    (g : UnitalHom (PresheafOfModules.symPowIntGradedAlgebra F) A)
    (hg : ∀ (X : Cᵒᵖ) (s : F.obj X),
      PresheafOfModules.Hom.app (g.app 1) X
          (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen F) X s) =
        PresheafOfModules.Hom.app gen X s)
    (k : ℕ) (X : Cᵒᵖ) (s : Fin k → F.obj X)
    (x : (PresheafOfModules.symPowInt (k : ℤ) F).obj X)
    (hx : PresheafOfModules.symPowIntVal x =
      ∏ i : Fin k, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i)) :
    PresheafOfModules.Hom.app (g.app (k : ℤ)) X x =
      A.homogeneousProd X k fun i => PresheafOfModules.Hom.app gen X (s i) := by
  induction k with
  | zero =>
      obtain rfl : x = (PresheafOfModules.symPowIntOne F).eval X :=
        PresheafOfModules.symPowIntVal_injective 0 F (by
          rw [hx, PresheafOfModules.symPowIntVal_one, Finset.univ_eq_empty, Finset.prod_empty])
      exact g.map_one X
  | succ k ih =>
      have hmem : ∏ i : Fin k, SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X)
            (s i.castSucc) ∈
          SymPow.symmetricPowerInt (k : ℤ) ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) :=
        SymmetricAlgebra.prod_ι_mem _ _
      have hdecomp : x =
          ((PresheafOfModules.symPowIntGradedAlgebra F).mul (k : ℤ) 1).app X
            (⟨_, hmem⟩ : (PresheafOfModules.symPowInt (k : ℤ) F).obj X)
            (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen F) X (s (Fin.last k))) :=
        PresheafOfModules.symPowIntVal_injective _ F
          (hx.trans (Fin.prod_univ_castSucc fun i =>
            SymmetricAlgebra.ι ((O ⋙ forget₂ _ RingCat).obj X) (F.obj X) (s i)))
      rw [hdecomp]
      exact (g.map_mul (k : ℤ) 1 X _ _).trans (by
        rw [ih (fun i => s i.castSucc) ⟨_, hmem⟩ rfl, hg]
        rfl)

/-- **The universal property of the sectionwise symmetric algebra.** A pairwise-commuting
degree-one generator of a graded algebra of presheaves of modules is extended by a *unique*
unital homomorphism out of the sectionwise symmetric algebra.

Existence is `unitalHomInt`, built from the degreewise comparison map `cmpInt`. Uniqueness is
`unitalHom_app_prod_ι` together with `SymPow.ext_of_prod_ι` in a nonnegative degree, and the
vanishing of `PresheafOfModules.symPowInt` in a negative degree.

This is the shape `Stacks.GradedAlgebra.isUniversal_sheafify` and
`Stacks.GradedAlgebra.isSymmetricAlgebra_sheafify` consume. -/
theorem existsUnique_unitalHom_symPowInt (hc : A.GenCommutes gen) :
    ∃! g : UnitalHom (PresheafOfModules.symPowIntGradedAlgebra F) A,
      ∀ (X : Cᵒᵖ) (s : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X
            (PresheafOfModules.Hom.app (PresheafOfModules.symPowIntGen F) X s) =
          PresheafOfModules.Hom.app gen X s := by
  refine ⟨A.unitalHomInt gen hc, A.cmpInt_app_gen gen hc, fun g hg => UnitalHom.ext fun n => ?_⟩
  obtain k | k := n
  · refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (SymPow.ext_of_prod_ι fun s => ?_)
    rw [A.unitalHomInt_app gen hc]
    refine (A.unitalHom_app_prod_ι gen g hg k X s _ rfl).trans
      (A.unitalHom_app_prod_ι gen (A.unitalHomInt gen hc) (A.cmpInt_app_gen gen hc) k X s _
        rfl).symm
  · refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rw [PresheafOfModules.symPowInt_eq_zero_of_neg _ F (Int.negSucc_lt_zero k) X x,
      map_zero, map_zero]

end Comparison

end Stacks.GradedAlgebra

namespace PresheafOfModules

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {R : Sheaf J RingCat.{w}}
  (α : (O ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  [HasWeakSheafify J AddCommGrpCat.{max w a}]
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ CommRingCat RingCat))

/-- **The symmetric algebra of a sheaf of modules, with its universal property.** The
degreewise sheafification of the sectionwise symmetric algebra of `F`, with its sheafified
degree-one generator, is universal among sheaves of graded algebras with a pairwise-commuting
degree-one generator of the sheafification of `F`.

This is the `symmetric_isSymmetricAlgebra` field of
`SheafOfModules.TensorExteriorSymmetricAlgebras` and the `isSymmetricAlgebra` field of
`Stacks.ProjectiveBundle.Situation`. The first component is
`pairwiseCommutes_symmetricAlgebraSheafifyGen`; the second is
`Stacks.GradedAlgebra.existsUnique_unitalHom_symPowInt`, transported along the sheafification
units by
`Stacks.GradedAlgebra.isSymmetricAlgebra_sheafify`. -/
theorem isSymmetricAlgebra_symmetricAlgebraSheafify :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra (symmetricAlgebraSheafify α F)
      (symmetricAlgebraSheafifyGen α F) :=
  (symPowIntGradedAlgebra F).isSymmetricAlgebra_sheafify α (symPowIntGen F)
    (symPowIntGradedAlgebra_genCommutes F) fun B κ hκ =>
      (B.restrictScalars α).existsUnique_unitalHom_symPowInt
        (sheafifyUnit α F ≫ (SheafOfModules.forget R ⋙ restrictScalars α).map κ)
        fun X x y => hκ X (Hom.app (sheafifyUnit α F) X x) (Hom.app (sheafifyUnit α F) X y)

end Sheafify

end PresheafOfModules
