module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandNoSliceSheafify
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.LocallyStrictlyPerfectDualComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import StacksFrontier.Homology.DerivedCategory.ZeroDifferentialCoproduct
import StacksCore.Tactic.StacksAttribute

/-!
# Invertible objects of the derived category of a ringed site

Let `(C, O)` be a ringed site. An object of `D(O)` which is the direct sum `⨁ ℋ^n[-n]` of
invertible modules over the factors of a locally finite direct product decomposition
`O = ∏_{n ∈ ℤ} O_n` of the structure sheaf is a perfect object of `D(O)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.InvertibleDerived.ProductDecomposition`: a locally finite direct
  product decomposition `O = ∏_{n ∈ ℤ} O_n` of the structure sheaf of a ringed site.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.HasInvertibleModuleDecomposition`: that such a
  decomposition exists together with invertible `O_n`-modules `ℋ^n` and an identification
  `M = ⨁ ℋ^n[-n]` in `D(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfect_of_hasInvertibleModuleDecomposition`:
  an object of `D(O)` admitting such a decomposition is perfect.

## Implementation notes

A direct product decomposition is carried by
`Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation`, the family of projections
`O ⟶ O_n` whose joint evaluation on the sections over every object of the site is bijective;
this says `O = ∏ O_n` without asking the category of sheaves of commutative rings for
`ℤ`-indexed products. Local finiteness is read on the rings of sections: `O_n|_V` is the zero
sheaf exactly when `O_n(V)` is the zero ring, since a ring map out of the zero ring forces its
target to be zero.

The direct sum `⨁ ℋ^n[-n]` is spelled as the object represented by the complex with `ℋ^n` in
degree `n` and zero differentials. `CochainComplex.derivedCoproductIso` identifies it with the
coproduct `∐ ℋ^n[-n]` whenever the derived category has `ℤ`-indexed coproducts, so no such
coproduct is required to state the hypothesis or to run the argument.

Above an object `V` of the site only finitely many factors survive, each `ℋ^n` is locally a
direct summand of a finite free `O_n`-module (Stacks 0B8N) and `O_n` is a direct summand of `O`,
so the representing complex is, on a covering of every object, strictly perfect. The covering is
assembled as the sieve of those arrows whose source carries the required local structure: that
set of arrows is a sieve because restriction along an arrow of the site preserves both
vanishing and the property of being a direct summand of a finite free module.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.DerivedMonoidal

universe u v w d

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

/-! ### Transport of strict perfectness along an isomorphism -/

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Strict perfectness transported along an isomorphism of complexes.

The universes of the objects, of the morphisms and of the sections of the structure sheaf are
independent, as they are for `AlgebraicGeometry.RingedSite.IsPerfectComplex`: neither condition
of strict perfectness refers to the size of the site. -/
theorem isStrictlyPerfect_of_iso {P Q : CochainComplex (SheafOfModules.{w} R) ℤ} (e : P ≅ Q)
    (hP : IsStrictlyPerfect R P) : IsStrictlyPerfect R Q where
  bounded := hP.bounded.subset fun i hi hz =>
    hi (((HomologicalComplex.eval _ _ i).mapIso e).isZero_iff.mp hz)
  termDirectSummand i :=
    IsDirectSummandOfFiniteFree.of_iso R ((HomologicalComplex.eval _ _ i).mapIso e).symm
      (hP.termDirectSummand i)

end Transport

/-! ### Finite free modules as finite direct sums of copies of the structure sheaf -/

section FiniteFree

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sheaves of `O`-modules have finite direct sums: they form an abelian category, hence have
finite products, and a preadditive category with finite products has finite biproducts. -/
local instance hasFiniteBiproducts_sheafOfModules :
    HasFiniteBiproducts (SheafOfModules.{u} R) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The free module on `n` generators is the direct sum of `n` copies of the structure sheaf. -/
def freeIsoBiproductFin (n : ℕ) :
    SheafOfModules.free (R := R) (ULift.{u} (Fin n)) ≅
      ⨁ (fun _ : Fin n => SheafOfModules.unit R) :=
  Sigma.whiskerEquiv (f := fun _ : ULift.{u} (Fin n) => SheafOfModules.unit R)
      (g := fun _ : Fin n => SheafOfModules.unit R) Equiv.ulift (fun _ => Iso.refl _) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin n => SheafOfModules.unit R)).symm

/-- A retract of a finite direct sum of copies of the structure sheaf is a direct summand of a
finite free module. -/
theorem isDirectSummandOfFiniteFree_of_retract_biproduct {F : SheafOfModules.{u} R} {n : ℕ}
    (ret : Retract F (⨁ (fun _ : Fin n => SheafOfModules.unit R))) :
    IsDirectSummandOfFiniteFree R F := by
  have r := ret.trans (freeIsoBiproductFin R n).symm.retract
  exact (isDirectSummandOfFiniteFree_iff_free R F).mpr ⟨n, r.i, r.r, r.retract⟩

/-- A family of retracts gives a retract of the direct sums. -/
def retractBiproduct {A : Type*} [Category* A] [Preadditive A] {ι : Type*} {f g : ι → A}
    [HasBiproduct f] [HasBiproduct g] (ρ : ∀ j, Retract (f j) (g j)) : Retract (⨁ f) (⨁ g) where
  i := biproduct.map fun j => (ρ j).i
  r := biproduct.map fun j => (ρ j).r
  retract := biproduct.hom_ext _ _ fun j => by simp [(ρ j).retract]

end FiniteFree

/-! ### Locally finite direct product decompositions of the structure sheaf -/

section Decomposition

variable (X : RingedSite.{u, u, u})

/-- A **locally finite direct product decomposition** `O = ∏_{n ∈ ℤ} O_n` of the structure sheaf
of a ringed site: a family of sheaves of commutative rings indexed by the integers, a
presentation of `O` as their product, and the condition that every object of the site has a
covering on whose members all but finitely many factors are the zero ring. -/
structure ProductDecomposition where
  /-- The factors `O_n` of the decomposition. -/
  factor : ℤ → Sheaf X.J CommRingCat.{u}
  /-- The presentation of the structure sheaf as the product of the factors. -/
  presentation : Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation X.O factor
  /-- Local finiteness: every object has a covering on whose members only finitely many factors
  are nonzero. -/
  locallyFinite : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
    ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      {n : ℤ | ¬ Subsingleton ((factor n).obj.obj (op V))}.Finite

namespace ProductDecomposition

variable {X}

/-- The projection `O ⟶ O_n` onto the `n`-th factor, as a morphism of the sheaves of (not
necessarily commutative) rings over which modules are taken. -/
def proj (D : ProductDecomposition X) (n : ℤ) :
    Stacks.SheafOfModules.Tensor.ringSheaf X.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n) :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (D.presentation.π n)

/-- An `O_n`-module viewed as an `O`-module, by restriction of scalars along the projection onto
the `n`-th factor. -/
abbrev toOMod (D : ProductDecomposition X) (n : ℤ) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  SheafOfModules.restrictScalars (D.proj n)

/-- Each factor `O_n`, viewed as an `O`-module, is a direct summand of `O`: the projection onto
the factor is split by the inclusion of the factor into the product. -/
theorem nonempty_retract_toOMod_unit (D : ProductDecomposition X) (n : ℤ) :
    Nonempty (Retract ((D.toOMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  Stacks.SheafOfModules.RingSheafProductFactor.nonempty_retract D.presentation n

/-- The projection `O ⟶ O_n` of the sheaves of rings of the slice sites over an object. -/
def projOver (D : ProductDecomposition X) (n : ℤ) (V : X.C) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).over V :=
  (X.J.overPullback RingCat.{u} V).map (D.proj n)

/-- An `O_n`-module on the slice site over `V`, viewed as an `O|_V`-module. -/
abbrev toOModOver (D : ProductDecomposition X) (n : ℤ) (V : X.C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).over V) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) :=
  SheafOfModules.restrictScalars (D.projOver n V)

/-- A factor which is the zero ring over an object contributes nothing there: a module over it,
viewed as an `O`-module and restricted to the slice site, is a zero object. -/
theorem isZero_over_toOMod (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    {V : X.C} (hV : Subsingleton ((D.factor n).obj.obj (op V))) :
    IsZero ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).obj
      ((D.toOMod n).obj L)) := by
  refine Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections _ fun W => ?_
  exact Stacks.SheafOfModules.subsingleton_sections L
    (Stacks.SheafOfModules.subsingleton_of_subsingleton_of_le (W.unop).hom hV)

/-- The sieve of arrows over whose source only finitely many factors of the decomposition are
nonzero. -/
def finiteSupportSieve (D : ProductDecomposition X) (U : X.C) : Sieve U where
  arrows V _ := {n : ℤ | ¬ Subsingleton ((D.factor n).obj.obj (op V))}.Finite
  downward_closed hf g := hf.subset fun n hn hsub => hn
    (Stacks.SheafOfModules.subsingleton_of_subsingleton_of_le
      (T := Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)) g hsub)

/-- The sieve of local finiteness is a covering sieve of every object. -/
theorem finiteSupportSieve_mem (D : ProductDecomposition X) (U : X.C) :
    D.finiteSupportSieve U ∈ X.J U := by
  obtain ⟨S, hS, hfin⟩ := D.locallyFinite U
  refine X.J.superset_covering ?_ hS
  rintro W g ⟨Z, a, b, hb, rfl⟩
  exact (D.finiteSupportSieve U).downward_closed (hfin b hb) a

end ProductDecomposition

end Decomposition

/-! ### Clause (2) of the source -/

section Clause

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Mod X.O)]

/-- **Clause (2) of Stacks 0FPY.** There is a locally finite direct product decomposition
`O = ∏_{n ∈ ℤ} O_n` of the structure sheaf and for each `n` an invertible `O_n`-module `ℋ^n`
such that `M = ⨁_{n ∈ ℤ} ℋ^n[-n]` in `D(O)`, the direct sum being the object represented by
the complex carrying `ℋ^n`, viewed as an `O`-module, in degree `n` with zero differentials. -/
def HasInvertibleModuleDecomposition (M : DerivedModules X.O) : Prop :=
  ∃ (D : ProductDecomposition X)
      (H : ∀ n : ℤ, SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))),
    (∀ n : ℤ, Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) (H n)) ∧
      Nonempty (M ≅ DerivedCategory.Q.obj
        (CochainComplex.zeroDifferentialComplex fun n => (D.toOMod n).obj (H n)))

/-- The representing complex of clause (2) is the direct sum `∐ ℋ^n[-n]` of the modules `ℋ^n`
placed in degree `n`, whenever those coproducts exist in `D(O)`. -/
theorem iso_coproduct_zeroDifferentialComplex
    [PreservesColimitsOfShape (Discrete ℤ) (DerivedCategory.Q (C := Mod X.O))]
    (D : ProductDecomposition X)
    (H : ∀ n : ℤ, SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    [HasCoproduct fun n : ℤ =>
      (DerivedCategory.singleFunctor (Mod X.O) n).obj ((D.toOMod n).obj (H n))] :
    Nonempty ((∐ fun n : ℤ =>
        (DerivedCategory.singleFunctor (Mod X.O) n).obj ((D.toOMod n).obj (H n))) ≅
      DerivedCategory.Q.obj
        (CochainComplex.zeroDifferentialComplex fun n => (D.toOMod n).obj (H n))) :=
  ⟨CochainComplex.derivedCoproductIso fun n : ℤ => (D.toOMod n).obj (H n)⟩

end Clause

/-! ### Perfectness -/

section Perfect

variable {X : RingedSite.{u, v, w}}
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The category of sheaves of modules over the restriction of a sheaf of rings to an object of
the site has finite biproducts. -/
local instance hasFiniteBiproductsOver (R : Sheaf X.J RingCat.{w}) (V : X.C) :
    HasFiniteBiproducts (SheafOfModules.{w} (R.over V)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Restriction of sheaves of `O`-modules along an arrow of the site preserves finite colimits. -/
local instance preservesFiniteColimitsOverMap {V W : X.C} (g : W ⟶ V) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

/-- Restriction along an arrow of the site carries the restriction of a complex of `O`-modules
to the restriction of the same complex further down. -/
def restrictComplexOverIso {V W : X.C} (g : W ⟶ V)
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (X.restrictComplex E V) ≅
      X.restrictComplex E W :=
  (Functor.mapHomologicalComplexCompIso
    (SheafOfModules.overFunctorMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
    (ComplexShape.up ℤ)).app E

/-- Being a direct summand of a finite free module passes from the restriction of an `O`-module
to an object of the site to its restriction along any arrow into that object. -/
theorem isDirectSummandOfFiniteFree_over {V W : X.C} (g : W ⟶ V)
    {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
      ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).obj M)) :
    IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
      ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).obj M) :=
  IsDirectSummandOfFiniteFree.of_iso _
    (((SheafOfModules.overFunctorMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).app
      M).symm)
    (SheafOfModules.isDirectSummandOfFiniteFree_map
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
      (SheafOfModules.overMapUnitIso g) _ hM)

/-- Strict perfectness of the restriction of a complex of `O`-modules passes to the restriction
along any arrow of the site. -/
theorem isStrictlyPerfect_restrictComplex {V W : X.C} (g : W ⟶ V)
    {E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
      (X.restrictComplex E V)) :
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
      (X.restrictComplex E W) :=
  isStrictlyPerfect_of_iso _ (restrictComplexOverIso g E)
    (SheafOfModules.isStrictlyPerfect_map
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
      (SheafOfModules.overMapUnitIso g) hE)

/-- The sieve of arrows over whose source the restriction of a complex of `O`-modules is strictly
perfect. -/
def strictlyPerfectSieve
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (U : X.C) :
    Sieve U where
  arrows W _ := IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
    (X.restrictComplex E W)
  downward_closed hf g := isStrictlyPerfect_restrictComplex g hf

/-- A complex of `O`-modules whose restriction is strictly perfect on a covering of every object
is a perfect complex. -/
theorem isPerfectComplex_of_strictlyPerfectSieve
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (h : ∀ U : X.C, strictlyPerfectSieve E U ∈ X.J U) :
    X.IsPerfectComplex E := by
  intro U
  refine ⟨(strictlyPerfectSieve E U).arrows, ?_,
    fun V f hf => ⟨X.restrictComplex E V, hf, 𝟙 _, inferInstance⟩⟩
  rw [Sieve.generate_sieve]
  exact h U

variable {X : RingedSite.{u, u, u}}
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The local structure of a factor module -/

section Summand

/-- **The transport step.** If an `O_n`-module `ℒ` is, over an object `V` of the site, a split
subobject of a finite product of copies of `O_n`, and if `O_n` is a direct summand of `O` as an
`O`-module, then `ℒ` viewed as an `O`-module restricts to a direct summand of a finite free
`O|_V`-module. -/
theorem isDirectSummandOfFiniteFree_over_toOMod (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (ret : Retract ((D.toOMod n).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))))
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (V : X.C) (k : ℕ)
    (s : L.over V ⟶ ∏ᶜ fun _ : Fin k =>
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).over V))
    (hs : IsSplitMono s) :
    IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).obj
        ((D.toOMod n).obj L)) := by
  have := hs
  have ρ₀ : Retract (L.over V) (⨁ fun _ : Fin k =>
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).over V)) :=
    (⟨s, retraction s, IsSplitMono.id s⟩ : Retract (L.over V) (∏ᶜ _)).trans
      (Retract.ofIso (biproduct.isoProduct _).symm)
  have ρᵤ : Retract ((D.toOModOver n V).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).over V)))
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
    ret.map (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)
  have ρ : Retract ((D.toOModOver n V).obj (L.over V))
      (⨁ fun _ : Fin k =>
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
    (ρ₀.map (D.toOModOver n V)).trans
      ((Retract.ofIso ((D.toOModOver n V).mapBiproduct _)).trans
        (retractBiproduct fun _ : Fin k => ρᵤ))
  exact isDirectSummandOfFiniteFree_of_retract_biproduct _ ρ

/-- The sieve of arrows over whose source a factor module, viewed as an `O`-module, is a direct
summand of a finite free `O`-module. -/
def summandSieve (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) (U : X.C) :
    Sieve U where
  arrows W _ := IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).obj
      ((D.toOMod n).obj L))
  downward_closed hf g := isDirectSummandOfFiniteFree_over g hf

/-- **Stacks 0B8N on a factor of a product decomposition.** An invertible `O_n`-module, viewed as
an `O`-module, is a direct summand of a finite free `O`-module on a covering of every object of
the site. -/
theorem summandSieve_mem (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hL : Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) L) (U : X.C) :
    summandSieve D n L U ∈ X.J U := by
  obtain ⟨ret⟩ := D.nonempty_retract_toOMod_unit n
  obtain ⟨I, V, f, hcov, hsplit⟩ :=
    @Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree
      _ _ _ _ _ _ (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).property L hL U
  refine X.J.superset_covering ?_ hcov
  rintro W g ⟨Z, a, b, hb, rfl⟩
  cases hb with
  | mk i =>
    obtain ⟨k, t, ht⟩ := hsplit i
    exact (summandSieve D n L U).downward_closed
      (isDirectSummandOfFiniteFree_over_toOMod D n L ret (V i) k t ht) a

end Summand

/-! ### Clause (2) implies perfectness -/

section Main

/-- **Stacks 0FPY, the perfectness conclusion, at the level of complexes.** The complex carrying
an invertible `O_n`-module in degree `n` for the factors of a locally finite direct product
decomposition of the structure sheaf, with zero differentials, is a perfect complex. -/
theorem isPerfectComplex_zeroDifferentialComplex (D : ProductDecomposition X)
    (H : ∀ n : ℤ, SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hinv : ∀ n : ℤ, Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) (H n)) :
    X.IsPerfectComplex
      (CochainComplex.zeroDifferentialComplex fun n => (D.toOMod n).obj (H n)) := by
  classical
  refine isPerfectComplex_of_strictlyPerfectSieve _ fun U => ?_
  refine X.J.transitive (D.finiteSupportSieve_mem U) _ fun {V} f hf => ?_
  refine X.J.superset_covering ?_
    (Stacks.SheafOfModules.FiniteTypeKernel.finsetInf_mem X.J hf.toFinset
      (fun n => summandSieve D n (H n) V)
      fun n _ => summandSieve_mem D n (H n) (hinv n) V)
  intro W g hg
  have hzero : ∀ i : ℤ, Subsingleton ((D.factor i).obj.obj (op V)) →
      IsZero ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).obj
        ((D.toOMod i).obj (H i))) := fun i hsub =>
    D.isZero_over_toOMod i (H i)
      (Stacks.SheafOfModules.subsingleton_of_subsingleton_of_le
        (T := Stacks.SheafOfModules.Tensor.ringSheaf (D.factor i)) g hsub)
  refine ⟨hf.subset fun i hi hsub => hi (hzero i hsub), fun i => ?_⟩
  by_cases hi : i ∈ hf.toFinset
  · exact (Finset.inf_le hi : _ ≤ summandSieve D i (H i) V) g hg
  · exact Stacks.SheafOfModules.Strict.isDirectSummandOfFiniteFree_of_isZero _
      (hzero i (by simpa using (Set.Finite.mem_toFinset hf).not.mp hi))

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (Mod X.O)]

/-- **Stacks 0FPY, the perfectness conclusion.** Let `(C, O)` be a ringed site and let `M` be an
object of `D(O)`. If there is a locally finite direct product decomposition
`O = ∏_{n ∈ ℤ} O_n` of the structure sheaf and for each `n` an invertible `O_n`-module `ℋ^n`
with `M = ⨁ ℋ^n[-n]` in `D(O)`, then `M` is a perfect object of `D(O)`.

On a covering of every object only finitely many factors survive, each `ℋ^n` is there a direct
summand of a finite free `O_n`-module and `O_n` is a direct summand of `O`, so the complex with
`ℋ^n` in degree `n` and zero differentials — which represents `⨁ ℋ^n[-n]` — is locally
strictly perfect. -/
@[stacks 0FPY "clause (2) implies that M is a perfect object of D(O)"]
theorem isPerfect_of_hasInvertibleModuleDecomposition (M : DerivedModules X.O)
    (hM : HasInvertibleModuleDecomposition X M) : X.IsPerfect M := by
  obtain ⟨D, H, hinv, ⟨e⟩⟩ := hM
  exact ⟨_, isPerfectComplex_zeroDifferentialComplex D H hinv, ⟨e.symm⟩⟩

end Main

end Perfect

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
