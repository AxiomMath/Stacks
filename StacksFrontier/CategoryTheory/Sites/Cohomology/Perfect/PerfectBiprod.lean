module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor

/-!
# A direct sum of perfect objects is perfect

Let `(C, O)` be a ringed site, with objects, morphisms and sections of the structure sheaf in
independent universes. A direct sum of two strictly perfect complexes is strictly perfect, and a
direct sum of two perfect objects of `D(O)` is perfect: on the intersection of two coverings
carrying strictly perfect local models of the summands, the direct sum of the models is a
strictly perfect local model of the direct sum.

## Main results

* `AlgebraicGeometry.RingedSite.isStrictlyPerfect_biprod`: the direct sum of two strictly perfect
  complexes is strictly perfect.
* `AlgebraicGeometry.RingedSite.quasiIso_biprod_map`: a direct sum of quasi-isomorphisms is a
  quasi-isomorphism.
* `AlgebraicGeometry.RingedSite.isPerfectComplex_biprod`: the direct sum of two perfect complexes
  is perfect.
* `AlgebraicGeometry.RingedSite.isPerfect_biprod`: the direct sum of two perfect objects of
  `D(O)` is perfect.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

/-- **A direct sum of strictly perfect complexes is strictly perfect**: it is bounded, its terms
being the direct sums of the terms, and a direct sum of direct summands of finite free modules
is one. -/
theorem isStrictlyPerfect_biprod {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {P₁ P₂ : CochainComplex (SheafOfModules.{w} R) ℤ} (h₁ : IsStrictlyPerfect R P₁)
    (h₂ : IsStrictlyPerfect R P₂) : IsStrictlyPerfect R (P₁ ⊞ P₂) where
  bounded := (h₁.bounded.union h₂.bounded).subset fun i hi => by
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hi ((HomologicalComplex.biprodXIso P₁ P₂ i).isZero_iff.2
      ((IsZero.iff_id_eq_zero _).2
        (biprod.hom_ext _ _ (h.1.eq_of_tgt _ _) (h.2.eq_of_tgt _ _))))
  termDirectSummand i :=
    IsDirectSummandOfFiniteFree.of_iso R (HomologicalComplex.biprodXIso P₁ P₂ i)
      (IsDirectSummandOfFiniteFree.biprod R (h₁.termDirectSummand i) (h₂.termDirectSummand i))

/-- A direct sum of quasi-isomorphisms of cochain complexes is a quasi-isomorphism. -/
theorem quasiIso_biprod_map {C : Type*} [Category* C] [Abelian C]
    {K₁ K₂ L₁ L₂ : CochainComplex C ℤ} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    [QuasiIso f] [QuasiIso g] : QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have {A B : CochainComplex C ℤ} (f : A ⟶ B) [QuasiIso f] :
      IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).map f) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap f i))
  exact MappingCoconeAux.isIso_map_biprod_map
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) f g

variable (X : RingedSite.{u, v, w})
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A direct sum of perfect complexes is perfect.** Over the intersection of two coverings on
which the summands have strictly perfect local models, the direct sum of the models is a
strictly perfect local model of the direct sum. -/
theorem isPerfectComplex_biprod
    (E₁ E₂ : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (h₁ : X.IsPerfectComplex E₁) (h₂ : X.IsPerfectComplex E₂) : X.IsPerfectComplex (E₁ ⊞ E₂) := by
  intro U
  obtain ⟨S₁, hS₁, m₁⟩ := h₁ U
  obtain ⟨S₂, hS₂, m₂⟩ := h₂ U
  refine ⟨(Sieve.generate S₁ ⊓ Sieve.generate S₂).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact X.J.intersection_covering hS₁ hS₂
  · rintro V g ⟨⟨W₁, a₁, f₁, hf₁, rfl⟩, ⟨W₂, a₂, f₂, hf₂, -⟩⟩
    obtain ⟨P₁, hP₁, q₁, hq₁⟩ := X.hasStrictlyPerfectQuasiIso_of_hom E₁ a₁ (m₁ f₁ hf₁)
    obtain ⟨P₂, hP₂, q₂, hq₂⟩ := X.hasStrictlyPerfectQuasiIso_of_hom E₂ a₂ (m₂ f₂ hf₂)
    let F := (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapHomologicalComplex (ComplexShape.up ℤ)
    have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
    refine ⟨P₁ ⊞ P₂, isStrictlyPerfect_biprod _ hP₁ hP₂,
      biprod.map q₁ q₂ ≫ (F.mapBiprod E₁ E₂).inv, ?_⟩
    have := quasiIso_biprod_map q₁ q₂
    infer_instance

/-- **A direct sum of perfect objects of `D(O)` is perfect.** -/
theorem isPerfect_biprod
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K₁ K₂ : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h₁ : X.IsPerfect K₁) (h₂ : X.IsPerfect K₂) : X.IsPerfect (K₁ ⊞ K₂) := by
  obtain ⟨E₁, hE₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨E₂, hE₂, ⟨e₂⟩⟩ := h₂
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact ⟨E₁ ⊞ E₂, isPerfectComplex_biprod X E₁ E₂ hE₁ hE₂,
    ⟨DerivedCategory.Q.mapBiprod E₁ E₂ ≪≫ biprod.mapIso e₁ e₂⟩⟩

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **A shift of a perfect complex is perfect**: the shifts of strictly perfect local models are
strictly perfect local models of the shift, restriction commuting with the shift. -/
theorem isPerfectComplex_shift
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (h : X.IsPerfectComplex E) (n : ℤ) : X.IsPerfectComplex (E⟦n⟧) := by
  intro U
  obtain ⟨S, hS, m⟩ := h U
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := m g hg
  let F := (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    V).mapHomologicalComplex (ComplexShape.up ℤ)
  exact ⟨P⟦n⟧, _root_.SheafOfModules.isStrictlyPerfect_shift _ hP n,
    q⟦n⟧' ≫ ((F.commShiftIso n).app E).inv, inferInstance⟩

/-- **A shift of a perfect object of `D(O)` is perfect.** -/
theorem isPerfect_shift_general_of_hasDerivedCategory
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : X.IsPerfect K) (n : ℤ) : X.IsPerfect (K⟦n⟧) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := h
  exact ⟨E⟦n⟧, isPerfectComplex_shift X E hE n,
    ⟨(DerivedCategory.Q.commShiftIso n).app E ≪≫ (shiftFunctor _ n).mapIso e⟩⟩

end AlgebraicGeometry.RingedSite

end
