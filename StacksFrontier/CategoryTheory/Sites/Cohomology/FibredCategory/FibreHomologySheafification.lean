module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ExplicitChainMapOnHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.FibreHomologyPresheaf
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Slice

/-!
# Sheafifying the coefficients does not change the sheaf of fibre homology

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site `(D, O_D)`, as in
Stacks 08P8, with small fibres, and give `C` the inherited topology. For an abelian presheaf `F` on
`C` write `L_{n,p}(F)` for the presheaf of fibre homology `V ↦ H_n(C_V, F|_{C_V})` of
`Stacks.Sites.FibredCategory.fiberHomologyPresheafFunctor` and `L_n(F)` for its associated sheaf.
This file proves

```
L_n(F) = L_n(F^#),
```

that is, the canonical map `L_n(F) ⟶ L_n(F^#)` induced by the unit `F ⟶ F^#` of sheafification on
the total category is an isomorphism of sheaves on the base.

## Main results

* `Stacks.Sites.FibredCategory.fiberHomologySheaf_sheafify`: the canonical map of sheaves is an
  isomorphism.
* `Stacks.Sites.FibredCategory.fiberHomologySheafSheafifyIso`: the resulting identification
  `L_n(F) ≅ L_n(F^#)`.

## Implementation notes

The proof is the one of the source. Both `L_{n,p}(F)(V)` and `L_{n,p}(F^#)(V)` are computed by the
simplicial replacement complex `K_•` of Stacks 08PG, whose terms are direct sums over strings of
composable arrows of the fibre, and the comparison map is the explicit chain map of Stacks 08PH. A
section of a term of `K_•(F^#)` has finite support, so it is a finite sum of generators, and a
covering of the base over which every one of the finitely many coefficients lifts through
`F ⟶ F^#` is obtained by intersecting finitely many coverings. The passage from a covering of an
object of `C` to a covering of its image in `D` is the heart of the matter: a covering sieve for
the inherited topology is refined by a presieve of strongly cartesian arrows, whose image generates
a covering sieve of the base, by `CategoryTheory.Functor.inheritedCoverage` and the saturation
argument of `exists_mem_coverage_generate_le_of_saturate`. This makes the comparison locally
surjective and locally injective over the base, hence an isomorphism after sheafification.

Surjectivity of the comparison on homology needs the lifted chain to be a cycle, which it is only
after refining the covering once more, so a lift is produced over a sieve obtained by composing a
covering with a covering chosen for each of its members; that is `exists_covering_sieve_factoring`.

The pullback functors of the chosen cartesian lifts are those of
`CategoryTheory.Functor.chosenPullbacks`, and the restriction maps of `L_{n,p}` are the ones
`Stacks.Sites.FibredCategory.fiberHomologyPresheaf_map` describes.

`CategoryTheory.Functor.Fiber` and `CategoryTheory.Functor.Fiber.fiberInclusion` are plain `def`s,
so goals about the structure arrow of an object of a fibre are not type-correct at `implicit`
transparency; they are therefore made locally `implicit_reducible`.

## References

* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory

universe uD vD uC v w usmall

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

private theorem coverage_refine_saturate {C : Type*} [Category C]
    (K : Coverage C) [Precoverage.HasIsos K.toPrecoverage]
    [Precoverage.IsStableUnderComposition K.toPrecoverage]
    {X : C} {S : Sieve X} (hS : K.Saturate X S) :
    ∃ R : Presieve X, R ∈ K X ∧ Sieve.generate R ≤ S := by
  classical
  induction hS with
  | of X R hR => exact ⟨R, hR, le_rfl⟩
  | top X =>
      refine ⟨Presieve.singleton (𝟙 X), ?_, ?_⟩
      · exact Precoverage.mem_coverings_of_isIso (J := K.toPrecoverage) (𝟙 X)
      · rw [Sieve.generate_le_iff]
        intro Y f hf
        rcases hf with ⟨⟨⟩⟩
        simp
  | transitive X R S hR hS ihR ihS =>
      obtain ⟨P, hP, hPle⟩ := ihR
      obtain ⟨ι, Y, f, hPdef⟩ := P.exists_eq_ofArrows
      let I := ι
      choose Q hQ hQle using fun i : I => ihS
        (hPle (f i) (Sieve.le_generate P (Y i) (f i) (by rw [hPdef]; exact ⟨i⟩)))
      choose κ Z g hg using fun i => (Q i).exists_eq_ofArrows
      have hPfam : Presieve.ofArrows Y f ∈ K.toPrecoverage X := by
        simpa [hPdef] using hP
      have hQfam (i : I) : Presieve.ofArrows (Z i) (g i) ∈ K.toPrecoverage (Y i) := by
        simpa [hg i] using hQ i
      have hcomp : Presieve.ofArrows
          (fun ij : Σ i : I, κ i => Z ij.1 ij.2)
          (fun ij => g ij.1 ij.2 ≫ f ij.1) ∈ K.toPrecoverage X :=
        Precoverage.comp_mem_coverings (J := K.toPrecoverage) f hPfam g hQfam
      refine ⟨_, hcomp, ?_⟩
      rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      intro ij
      have hqi : Q ij.1 (g ij.1 ij.2) := by
        rw [hg ij.1]
        exact Presieve.ofArrows.mk ij.2
      simpa [Sieve.pullback_apply] using
        hQle ij.1 (g ij.1 ij.2) (Sieve.le_generate _ _ _ hqi)

private theorem inheritedTopology_refine {X : s.C} {S : Sieve X}
    (hS : S ∈ s.topology X) :
    ∃ R : Presieve X,
      R ∈ s.p.inheritedPrecoverage s.base.J.toPrecoverage X ∧ Sieve.generate R ≤ S := by
  let K := s.p.inheritedCoverage s.base.J
  have : Precoverage.HasIsos K.toPrecoverage := by
    show Precoverage.HasIsos (s.p.inheritedPrecoverage s.base.J.toPrecoverage)
    infer_instance
  have : Precoverage.IsStableUnderComposition K.toPrecoverage := by
    show Precoverage.IsStableUnderComposition
      (s.p.inheritedPrecoverage s.base.J.toPrecoverage)
    infer_instance
  have hK : S ∈ K.toGrothendieck X := by
    rw [← Coverage.toGrothendieck_toPrecoverage K]
    simpa [K, Functor.inheritedCoverage, FibredCategorySituation.topology,
      Functor.inheritedTopology_eq] using hS
  obtain ⟨R, hR, hle⟩ := coverage_refine_saturate K (Coverage.mem_toGrothendieck.mp hK)
  exact ⟨R, by simpa [K, Functor.inheritedCoverage] using hR, hle⟩

private theorem inheritedPrecoverage_pullback_le_sieve {X : s.C}
    (R : Presieve X)
    (hR : R ∈ s.p.inheritedPrecoverage s.base.J.toPrecoverage X)
    {S : Sieve X} (hRS : Sieve.generate R ≤ S) :
    (Sieve.generate (R.map s.p)).functorPullback s.p ≤ S := by
  intro Z g hg
  change (Sieve.generate (R.map s.p)) (s.p.map g) at hg
  obtain ⟨W, i, a, ha, hcomp⟩ := hg
  obtain ⟨W', e0, e, heR, hmapE⟩ := Presieve.map_iff.mp ha
  let i' : s.p.obj Z ⟶ s.p.obj W' := i ≫ eqToHom e0.symm
  have hbase : s.p.map g = i' ≫ s.p.map e := by
    calc
      s.p.map g = i ≫ a := hcomp.symm
      _ = i' ≫ s.p.map e := by
        dsimp [i']
        rw [hmapE]
        simp [Category.assoc]
  have : s.p.IsStronglyCartesian (s.p.map e) e := hR.1 e heR
  obtain ⟨θ, ⟨_, hθ⟩, _⟩ :=
    Functor.IsStronglyCartesian.universal_property s.p (s.p.map e) e i'
      (s.p.map g) hbase g
  rw [← hθ]
  exact S.downward_closed (hRS e (Sieve.le_generate R _ _ heR)) θ

private theorem inheritedTopology_base_refinement {X : s.C} {S : Sieve X}
    (hS : S ∈ s.topology X) :
    ∃ B : Sieve (s.p.obj X), B ∈ s.base.J (s.p.obj X) ∧
      B.functorPullback s.p ≤ S := by
  obtain ⟨R, hR, hRS⟩ := inheritedTopology_refine (s := s) hS
  exact ⟨_, (GrothendieckTopology.mem_toPrecoverage_iff s.base.J (R.map s.p)).mp hR.2,
    inheritedPrecoverage_pullback_le_sieve (s := s) R hR hRS⟩

private theorem coefficient_unit_locally_surjective_over_base
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    {F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}}
    [Presheaf.IsLocallySurjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)]
    {X : s.C} (z : (((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F).obj).obj
      (.op X)) :
    ∃ B : Sieve (s.p.obj X), B ∈ s.base.J (s.p.obj X) ∧
      ∀ ⦃Z : s.C⦄ (g : Z ⟶ X), B (s.p.map g) →
        ∃ a : F.obj (.op Z),
          ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F).app
            (.op Z) a =
            (((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F).obj).map
              (Opposite.op g) z := by
  let η := (sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F
  obtain ⟨B, hB, hle⟩ := inheritedTopology_base_refinement (s := s)
    (Presheaf.imageSieve_mem s.topology η z)
  exact ⟨B, hB, fun Z g hg => ⟨Presheaf.localPreimage η z g (hle g hg),
    Presheaf.app_localPreimage η z g (hle g hg)⟩⟩

private theorem coefficient_unit_locally_injective_over_base
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    {F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}}
    [Presheaf.IsLocallyInjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)]
    {X : s.C} (a b : F.obj (.op X))
    (hab : ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F).app
      (.op X) a =
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F).app
      (.op X) b) :
    ∃ B : Sieve (s.p.obj X), B ∈ s.base.J (s.p.obj X) ∧
      ∀ ⦃Z : s.C⦄ (g : Z ⟶ X), B (s.p.map g) →
        F.map (Opposite.op g) a = F.map (Opposite.op g) b := by
  let η := (sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F
  obtain ⟨B, hB, hle⟩ := inheritedTopology_base_refinement (s := s)
    (Presheaf.equalizerSieve_mem s.topology η a b hab)
  exact ⟨B, hB, fun {Z} g hg => hle g hg⟩

private theorem finite_intersection_covering {C : Type*} [Category C]
    (J : GrothendieckTopology C) {X : C} {ι : Type*}
    (I : Finset ι) (B : ι → Sieve X)
    (hB : ∀ i ∈ I, B i ∈ J X) : I.inf B ∈ J X := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (hB i (Finset.mem_insert_self _ _))
        (ih fun j hj => hB j (Finset.mem_insert_of_mem hj))

private theorem covering_sieve_compose
    {C : Type*} [Category C] (J : GrothendieckTopology C) {X : C}
    (B : Sieve X) (hB : B ∈ J X)
    (D : ∀ ⦃Y : C⦄ (h : Y ⟶ X), B h → Sieve Y)
    (hD : ∀ ⦃Y : C⦄ (h : Y ⟶ X) (hh : B h), D h hh ∈ J Y) :
    ∃ R : Sieve X, R ∈ J X ∧
      ∀ ⦃Z : C⦄ (f : Z ⟶ X), R f →
        ∃ (Y : C) (h : Y ⟶ X) (hh : B h) (k : Z ⟶ Y),
          D h hh k ∧ f = k ≫ h := by
  classical
  let R : Sieve X := {
    arrows := fun Z f => ∃ (Y : C) (h : Y ⟶ X) (hh : B h) (k : Z ⟶ Y),
      D h hh k ∧ f = k ≫ h
    downward_closed := by
      intro Z Z' f hf l
      obtain ⟨Y, h, hh, k, hk, rfl⟩ := hf
      exact ⟨Y, h, hh, l ≫ k, (D h hh).downward_closed hk l, by simp [Category.assoc]⟩ }
  exact ⟨R, J.transitive hB R fun Y h hh =>
    J.superset_covering (fun Z k hk => ⟨Y, h, hh, k, hk, rfl⟩) (hD h hh), fun _ _ hf => hf⟩

/-- Finitely many coverings of the images of `X i` pull back to one covering of `V`
whose members stay inside each of them after applying `s.p` to the maps `g h i`. -/
private theorem finite_covering_pullback_mem {V : s.base.C} {ι : Type*} (I : Finset ι)
    (X : ι → s.C) (hX : ∀ i, s.p.obj (X i) = V)
    (B : ∀ i, Sieve (s.p.obj (X i))) (hB : ∀ i, B i ∈ s.base.J (s.p.obj (X i)))
    (Y : ∀ {W : s.base.C}, (h : W ⟶ V) → ι → s.C)
    (hY : ∀ {W : s.base.C} (h : W ⟶ V) (i : ι), s.p.obj (Y h i) = W)
    (g : ∀ {W : s.base.C} (h : W ⟶ V) (i : ι), Y h i ⟶ X i)
    (hg : ∀ {W : s.base.C} (h : W ⟶ V) (i : ι),
      s.p.map (g h i) = eqToHom (hY h i) ≫ h ≫ eqToHom (hX i).symm) :
    ∃ B' : Sieve V, B' ∈ s.base.J V ∧
      ∀ ⦃W : s.base.C⦄ (h : W ⟶ V), B' h → ∀ i ∈ I, B i (s.p.map (g h i)) := by
  classical
  let B' : ι → Sieve V := fun i => (B i).pullback (eqToHom (hX i).symm)
  refine ⟨I.inf B', finite_intersection_covering s.base.J I B' fun i _ =>
    s.base.J.pullback_stable _ (hB i), ?_⟩
  intro W h hh i hi
  have hBh : B' i h := (Finset.inf_le (f := B') hi) h hh
  rw [Sieve.pullback_apply] at hBh
  rw [hg h i]
  exact Sieve.downward_closed (B i) hBh (eqToHom (hY h i))

private theorem coefficient_unit_finite_locally_surjective_over_base
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    {F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}}
    [Presheaf.IsLocallySurjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)]
    {V : s.base.C} {ι : Type*} (I : Finset ι)
    (X : ι → s.C) (hX : ∀ i, s.p.obj (X i) = V)
    (z : ∀ i, (((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F).obj).obj
      (.op (X i)))
    (Y : ∀ {W : s.base.C}, (h : W ⟶ V) → ι → s.C)
    (hY : ∀ {W : s.base.C} (h : W ⟶ V) (i : ι), s.p.obj (Y h i) = W)
    (g : ∀ {W : s.base.C} (h : W ⟶ V) (i : ι), Y h i ⟶ X i)
    (hg : ∀ {W : s.base.C} (h : W ⟶ V) (i : ι),
      s.p.map (g h i) = eqToHom (hY h i) ≫ h ≫ eqToHom (hX i).symm) :
    ∃ B : Sieve V, B ∈ s.base.J V ∧
      ∀ ⦃W : s.base.C⦄ (h : W ⟶ V), B h → ∀ i ∈ I,
        ∃ a : F.obj (.op (Y h i)),
          ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F).app
              (.op (Y h i)) a =
            (((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F).obj).map
              (Opposite.op (g h i)) (z i) := by
  choose B hB hpre using fun i =>
    coefficient_unit_locally_surjective_over_base (s := s) (F := F) (z i)
  obtain ⟨B', hB', hmem⟩ := finite_covering_pullback_mem s I X hX B hB Y hY g hg
  exact ⟨B', hB', fun W h hh i hi => hpre i (g h i) (hmem h hh i hi)⟩

private theorem coefficient_unit_finite_locally_injective_over_base
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    {F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}}
    [Presheaf.IsLocallyInjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)]
    {V : s.base.C} {ι : Type*} (I : Finset ι)
    (X : ι → s.C) (hX : ∀ i, s.p.obj (X i) = V)
    (a b : ∀ i, F.obj (.op (X i)))
    (hab : ∀ i,
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F).app
      (.op (X i)) (a i) =
        ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F).app
          (.op (X i)) (b i))
    (Y : ∀ {W : s.base.C}, (h : W ⟶ V) → ι → s.C)
    (hY : ∀ {W : s.base.C} (h : W ⟶ V) (i : ι), s.p.obj (Y h i) = W)
    (g : ∀ {W : s.base.C} (h : W ⟶ V) (i : ι), Y h i ⟶ X i)
    (hg : ∀ {W : s.base.C} (h : W ⟶ V) (i : ι),
      s.p.map (g h i) = eqToHom (hY h i) ≫ h ≫ eqToHom (hX i).symm) :
    ∃ B : Sieve V, B ∈ s.base.J V ∧
      ∀ ⦃W : s.base.C⦄ (h : W ⟶ V), B h → ∀ i ∈ I,
        F.map (Opposite.op (g h i)) (a i) = F.map (Opposite.op (g h i)) (b i) := by
  choose B hB hpre using fun i =>
    coefficient_unit_locally_injective_over_base (s := s) (F := F) (a i) (b i) (hab i)
  obtain ⟨B', hB', hmem⟩ := finite_covering_pullback_mem s I X hX B hB Y hY g hg
  exact ⟨B', hB', fun W h hh i hi => hpre i (g h i) (hmem h hh i hi)⟩

private noncomputable def fiberSheafificationUnit
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (V : s.base.C) :
    (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F ⟶
      (𝟭 (s.p.Fiber V)).op ⋙
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙
        (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
          ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)) :=
  Functor.whiskerLeft (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F) ≫
    (Functor.leftUnitor
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙
        (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
          ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F))).inv

private theorem replacementChainMap_id_eq_directSumMap
    {C : Type uC} [SmallCategory C]
    (F G : Cᵒᵖ ⥤ AddCommGrpCat.{max uC v})
    (η : F ⟶ (𝟭 C).op ⋙ G) (n : ℕ) :
    ((CategoryHomology.replacementChainMap (𝟭 C) η).f n).hom =
      DirectSum.map (fun x : ComposableArrows C n => (η.app (.op x.right)).hom) := by
  classical
  apply DirectSum.addHom_ext
  intro x a
  show ((CategoryHomology.replacementChainMap (𝟭 C) η).f n).hom
      (CategoryHomology.replacementSummand F n x a) = _
  rw [CategoryHomology.replacementChainMap_on_summand]
  simp only [AlgebraicTopology.alternatingFaceMapComplex_obj_X,
    CategoryHomology.replacementSummand, Functor.mapComposableArrows,
    Functor.whiskeringRight_obj_obj, Functor.comp_id, Functor.comp_obj, Functor.op_obj,
    Functor.id_obj]
  rw [DirectSum.map_of]

private theorem replacementChainMap_pullback_unit_square
    {C D : Type uC} [SmallCategory C] [SmallCategory D]
    (p : C ⥤ D)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max uC v}}
    {F' : Dᵒᵖ ⥤ AddCommGrpCat.{max uC v}}
    {G : Cᵒᵖ ⥤ AddCommGrpCat.{max uC v}}
    {G' : Dᵒᵖ ⥤ AddCommGrpCat.{max uC v}}
    (tF : F ⟶ p.op ⋙ F') (tG : G ⟶ p.op ⋙ G')
    (η : F ⟶ G) (η' : F' ⟶ G')
    (hsquare : η ≫ tG = tF ≫ Functor.whiskerLeft p.op η') :
    CategoryHomology.replacementChainMap p tF ≫
        CategoryHomology.replacementChainMap (𝟭 D) η' =
      CategoryHomology.replacementChainMap (𝟭 C) η ≫
        CategoryHomology.replacementChainMap p tG := by
  classical
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.hom_ext
  apply DirectSum.addHom_ext
  intro i a
  show (ConcreteCategory.hom
      ((CategoryHomology.replacementChainMap p tF).f n ≫
        (CategoryHomology.replacementChainMap (𝟭 D) η').f n))
      (CategoryHomology.replacementSummand F n i a) =
    (ConcreteCategory.hom
      ((CategoryHomology.replacementChainMap (𝟭 C) η).f n ≫
        (CategoryHomology.replacementChainMap p tG).f n))
      (CategoryHomology.replacementSummand F n i a)
  conv_lhs =>
    rw [ConcreteCategory.comp_apply,
      CategoryHomology.replacementChainMap_on_summand,
      CategoryHomology.replacementChainMap_on_summand]
  conv_rhs =>
    rw [ConcreteCategory.comp_apply,
      CategoryHomology.replacementChainMap_on_summand,
      CategoryHomology.replacementChainMap_on_summand]
  have hcoeff := congrArg (fun θ => (θ.app (.op i.right)).hom a) hsquare
  simpa [Functor.mapComposableArrows, CategoryHomology.replacementSummand,
    Functor.comp_id, Functor.whiskerLeft_app] using
      congrArg (CategoryHomology.replacementSummand G' n
        ((p.mapComposableArrows n).obj i)) hcoeff.symm

private theorem fiberUnit_pullback_square
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})
    {V W : s.base.C} (h : W ⟶ V) :
    fiberSheafificationUnit s F V ≫
        fiberCartesianRestriction s
          ((sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
            ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)) h =
      fiberCartesianRestriction s F h ≫
        Functor.whiskerLeft ((Functor.chosenPullbacks s.p).pullbackFunctor h).op
          (fiberSheafificationUnit s F W) := by
  apply NatTrans.ext
  funext x
  simp [fiberSheafificationUnit, fiberCartesianRestriction, Functor.leftUnitor]

open Classical in
/-- An element of a replacement group is the sum of its summands over its support. -/
theorem replacementSummand_sum_support (P : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC})
    {V : s.base.C} (n : ℕ)
    (x : CategoryHomology.replacementGroup.{uC, max w uD vD uC}
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ P) n) :
    (∑ i : DFinsupp.support x,
      CategoryHomology.replacementSummand
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ P) n i.1 (x i.1)) = x := by
  show (∑ i : DFinsupp.support x, DirectSum.of
    (fun y : ComposableArrows (s.p.Fiber V) n =>
      P.obj (.op ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).obj y.right)))
    i.1 (x i.1)) = x
  rw [Finset.sum_coe_sort (s := DFinsupp.support x) (f := fun i => DirectSum.of
    (fun y : ComposableArrows (s.p.Fiber V) n =>
      P.obj (.op ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).obj y.right)))
    i (x i))]
  simpa using DirectSum.sum_support_of x

private theorem replacementChainMap_pullback_locally_surjective
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    {F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}}
    [Presheaf.IsLocallySurjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)]
    {V : s.base.C} (n : ℕ)
    (x : CategoryHomology.replacementGroup.{uC,
      max w uD vD uC}
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙
        (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
          ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)) n) :
    ∃ B : Sieve V, B ∈ s.base.J V ∧
      ∀ ⦃W : s.base.C⦄ (h : W ⟶ V), B h →
        ∃ y : CategoryHomology.replacementGroup.{uC,
            max w uD vD uC}
            ((Functor.Fiber.fiberInclusion (p := s.p) (S := W)).op ⋙ F) n,
          ((CategoryHomology.replacementChainMap.{uC, uC,
            max w uD vD uC}
            (𝟭 (s.p.Fiber W)) (fiberSheafificationUnit s F W)).f n).hom y =
            ((CategoryHomology.replacementChainMap.{uC, uC,
              max w uD vD uC}
              ((Functor.chosenPullbacks s.p).pullbackFunctor h)
              (fiberCartesianRestriction s
                ((sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
                  ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)) h)).f
              n).hom x := by
  classical
  let c := Functor.chosenPullbacks s.p
  let G := (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
    ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)
  let I : Finset (ComposableArrows (s.p.Fiber V) n) := DFinsupp.support x
  let X : ComposableArrows (s.p.Fiber V) n → s.C := fun i =>
    (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).obj i.right
  let hX : ∀ i : ComposableArrows (s.p.Fiber V) n, s.p.obj (X i) = V :=
    fun i => i.right.2
  let z : ∀ i : ComposableArrows (s.p.Fiber V) n, G.obj (.op (X i)) :=
    fun i => x i
  let Y : ∀ {W : s.base.C}, (h : W ⟶ V) →
      ComposableArrows (s.p.Fiber V) n → s.C := fun h i =>
    (Functor.Fiber.fiberInclusion (p := s.p) (S := _)).obj (c.obj h i.right)
  let hY : ∀ {W : s.base.C} (h : W ⟶ V)
      (i : ComposableArrows (s.p.Fiber V) n), s.p.obj (Y h i) = _ :=
    fun h i => (c.obj h i.right).2
  let g : ∀ {W : s.base.C} (h : W ⟶ V)
      (i : ComposableArrows (s.p.Fiber V) n), Y h i ⟶ X i :=
    fun h i => c.map h i.right
  have hg : ∀ {W : s.base.C} (h : W ⟶ V)
      (i : ComposableArrows (s.p.Fiber V) n),
      s.p.map (g h i) = eqToHom (hY h i) ≫ h ≫ eqToHom (hX i).symm := by
    intro W h i
    exact IsHomLift.fac' s.p h (c.map h i.right)
  obtain ⟨B, hB, hpre⟩ := coefficient_unit_finite_locally_surjective_over_base
    (s := s) (F := F) (I := I) X hX z Y hY g hg
  refine ⟨B, hB, ?_⟩
  intro W h hh
  let τ : ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ G) ⟶
      (c.pullbackFunctor h).op ⋙
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := W)).op ⋙ G) :=
    fiberCartesianRestriction s G h
  let ηW := fiberSheafificationUnit s F W
  let J := (c.pullbackFunctor h).mapComposableArrows n
  have hobj (i : I) : Y h i.1 =
      (Functor.Fiber.fiberInclusion (p := s.p) (S := W)).obj (J.obj i.1).right := by
    simp [Y, J, Functor.mapComposableArrows]
  let a (i : I) : F.obj (.op (Y h i.1)) :=
    Classical.choose (hpre h hh i.1 i.2)
  let a' (i : I) : F.obj (.op ((Functor.Fiber.fiberInclusion (p := s.p)
      (S := W)).obj ((J.obj i.1).right))) := hobj i ▸ a i
  let y : CategoryHomology.replacementGroup.{uC,
      max w uD vD uC}
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := W)).op ⋙ F) n :=
    ∑ i : I, CategoryHomology.replacementSummand
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := W)).op ⋙ F) n
      (J.obj i.1) (a' i)
  have hsum := replacementSummand_sum_support s G n x
  refine ⟨y, ?_⟩
  rw [replacementChainMap_id_eq_directSumMap.{uC, max w uD vD uC}]
  rw [← hsum]
  simp only [y, map_sum]
  show (∑ i ∈ Finset.univ, _) = ∑ i ∈ Finset.univ, _
  apply Finset.sum_congr rfl
  intro i hi
  have hcoeff := Classical.choose_spec (hpre h hh i.1 i.2)
  rw [CategoryHomology.replacementChainMap_on_summand]
  show DirectSum.map
      (fun q : ComposableArrows (s.p.Fiber W) n =>
        (ηW.app (.op q.right)).hom)
      (DirectSum.of
        (fun q : ComposableArrows (s.p.Fiber W) n =>
          F.obj (.op ((Functor.Fiber.fiberInclusion (p := s.p) (S := W)).obj q.right)))
        (J.obj i.1) (a' i)) =
    DirectSum.of
      (fun q : ComposableArrows (s.p.Fiber W) n =>
        G.obj (.op ((Functor.Fiber.fiberInclusion (p := s.p) (S := W)).obj q.right)))
      (J.obj i.1) ((τ.app (.op i.1.right)).hom (x i.1))
  apply DFinsupp.ext
  intro q
  by_cases hq : q = J.obj i.1
  · subst q
    simp only [DirectSum.map_apply, DirectSum.of_eq_same]
    cases hobj i
    show (ConcreteCategory.hom
      (((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F).app
        (.op (Y h i.1)))) (a i) =
      (ConcreteCategory.hom
        (((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F).obj.map
        (.op (g h i.1)))) (z i)
    exact hcoeff
  · have hne : J.obj i.1 ≠ q := fun h => hq h.symm
    simp [DirectSum.of_apply, hne]

private theorem replacementChainMap_pullback_locally_injective
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    {F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}}
    [Presheaf.IsLocallyInjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)]
    {V : s.base.C} (n : ℕ)
    (x : CategoryHomology.replacementGroup.{uC,
      max w uD vD uC}
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F) n)
    (hx : ((CategoryHomology.replacementChainMap.{uC, uC,
      max w uD vD uC} (𝟭 (s.p.Fiber V))
      (fiberSheafificationUnit s F V)).f n).hom x = 0) :
    ∃ B : Sieve V, B ∈ s.base.J V ∧
      ∀ ⦃W : s.base.C⦄ (h : W ⟶ V), B h →
        ((CategoryHomology.replacementChainMap.{uC, uC,
          max w uD vD uC} ((Functor.chosenPullbacks s.p).pullbackFunctor h)
          (fiberCartesianRestriction s F h)).f n).hom x = 0 := by
  classical
  let c := Functor.chosenPullbacks s.p
  let ηV := fiberSheafificationUnit s F V
  let I : Finset (ComposableArrows (s.p.Fiber V) n) := DFinsupp.support x
  let X : ComposableArrows (s.p.Fiber V) n → s.C := fun i =>
    (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).obj i.right
  let hX : ∀ i : ComposableArrows (s.p.Fiber V) n, s.p.obj (X i) = V :=
    fun i => i.right.2
  have hxmap : DirectSum.map
      (fun i : ComposableArrows (s.p.Fiber V) n => (ηV.app (.op i.right)).hom) x = 0 := by
    rw [← replacementChainMap_id_eq_directSumMap.{uC, max w uD vD uC}]
    exact hx
  have hxcoeff (i : ComposableArrows (s.p.Fiber V) n) :
      (ηV.app (.op i.right)).hom (x i) = 0 := by
    have h := congrArg (fun z : CategoryHomology.replacementGroup
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙
          (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
            ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)) n => z i) hxmap
    simpa only [DirectSum.map_apply, DFinsupp.zero_apply] using h
  let Y : ∀ {W : s.base.C}, (h : W ⟶ V) →
      ComposableArrows (s.p.Fiber V) n → s.C := fun h i =>
    (Functor.Fiber.fiberInclusion (p := s.p) (S := _)).obj (c.obj h i.right)
  let hY : ∀ {W : s.base.C} (h : W ⟶ V)
      (i : ComposableArrows (s.p.Fiber V) n), s.p.obj (Y h i) = _ :=
    fun h i => (c.obj h i.right).2
  let g : ∀ {W : s.base.C} (h : W ⟶ V)
      (i : ComposableArrows (s.p.Fiber V) n), Y h i ⟶ X i :=
    fun h i => c.map h i.right
  have hg : ∀ {W : s.base.C} (h : W ⟶ V)
      (i : ComposableArrows (s.p.Fiber V) n),
      s.p.map (g h i) = eqToHom (hY h i) ≫ h ≫ eqToHom (hX i).symm := by
    intro W h i
    exact IsHomLift.fac' s.p h (c.map h i.right)
  obtain ⟨B, hB, hpre⟩ := coefficient_unit_finite_locally_injective_over_base
    (s := s) (F := F) (I := I) X hX
    (fun i => x i) (fun _ => 0)
    (fun i => by simpa [ηV, X, fiberSheafificationUnit, Functor.leftUnitor] using hxcoeff i)
    Y hY g hg
  refine ⟨B, hB, ?_⟩
  intro W h hh
  rw [← replacementSummand_sum_support s F n x, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hcoeff : ((fiberCartesianRestriction s F h).app (.op i.1.right)).hom (x i.1) = 0 :=
    (hpre h hh i.1 i.2).trans (map_zero _)
  rw [CategoryHomology.replacementChainMap_on_summand, hcoeff]
  simp [CategoryHomology.replacementSummand]

private theorem replacementChainMap_pullback_locally_surjective_cycle
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    {F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}}
    [Presheaf.IsLocallySurjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)]
    [Presheaf.IsLocallyInjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)]
    {V : s.base.C} (n : ℕ)
    (x : CategoryHomology.replacementGroup.{uC,
      max w uD vD uC}
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙
        (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
          ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)) n)
    (hx : ((CategoryHomology.simplicialReplacementComplex
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙
        (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
          ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F))).d n
            ((ComplexShape.down ℕ).next n)).hom x = 0) :
    ∃ B : Sieve V, B ∈ s.base.J V ∧
      ∀ ⦃Z : s.base.C⦄ (f : Z ⟶ V), B f →
        ∃ (T : s.base.C) (h : T ⟶ V) (k : Z ⟶ T)
          (y : CategoryHomology.replacementGroup.{uC,
            max w uD vD uC}
            ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ F) n),
          ((CategoryHomology.simplicialReplacementComplex
            ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ F)).d n
              ((ComplexShape.down ℕ).next n)).hom y = 0 ∧
          ((CategoryHomology.replacementChainMap.{uC, uC,
            max w uD vD uC} (𝟭 (s.p.Fiber Z))
            (fiberSheafificationUnit s F Z)).f n).hom y =
            ((CategoryHomology.replacementChainMap.{uC, uC,
              max w uD vD uC} ((Functor.chosenPullbacks s.p).pullbackFunctor k)
              (fiberCartesianRestriction s
                ((sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
                  ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)) k)).f n).hom
              (((CategoryHomology.replacementChainMap.{uC, uC,
                max w uD vD uC} ((Functor.chosenPullbacks s.p).pullbackFunctor h)
                (fiberCartesianRestriction s
                  ((sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
                    ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F))
                  h)).f n).hom x) ∧
          f = k ≫ h := by
  classical
  let G := (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
    ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)
  let j := (ComplexShape.down ℕ).next n
  obtain ⟨B, hB, hpre⟩ := replacementChainMap_pullback_locally_surjective
    (s := s) (F := F) n x
  have hzero : ∀ ⦃T : s.base.C⦄ (h : T ⟶ V) (hh : B h),
      ((CategoryHomology.replacementChainMap.{uC, uC,
        max w uD vD uC} (𝟭 (s.p.Fiber T))
        (fiberSheafificationUnit s F T)).f j).hom
        (((CategoryHomology.simplicialReplacementComplex
          ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ F)).d n j).hom
            (Classical.choose (hpre (W := T) h hh))) = 0 := by
    intro T h hh
    let y := Classical.choose (hpre (W := T) h hh)
    have hy := Classical.choose_spec (hpre (W := T) h hh)
    let m := CategoryHomology.replacementChainMap.{uC, uC,
      max w uD vD uC}
      (𝟭 (s.p.Fiber T)) (fiberSheafificationUnit s F T)
    let r := CategoryHomology.replacementChainMap.{uC, uC,
      max w uD vD uC}
      ((Functor.chosenPullbacks s.p).pullbackFunctor h)
      (fiberCartesianRestriction s G h)
    have hm := congrArg (fun q => (ConcreteCategory.hom q) y) (m.comm n j)
    have hr := congrArg (fun q => (ConcreteCategory.hom q) x) (r.comm n j)
    simp only [ConcreteCategory.comp_apply] at hm hr
    calc
      _ = ((CategoryHomology.simplicialReplacementComplex
          ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ G)).d n j).hom
            ((m.f n).hom y) := hm.symm
      _ = ((CategoryHomology.simplicialReplacementComplex
          ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ G)).d n j).hom
            ((r.f n).hom x) :=
        congrArg
          (((CategoryHomology.simplicialReplacementComplex
            ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ G)).d n j).hom) hy
      _ = (r.f j).hom
            (((CategoryHomology.simplicialReplacementComplex
              ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ G)).d n j).hom x) := hr
      _ = 0 := by
        rw [hx]
        simp
  let injCover {T : s.base.C} (h : T ⟶ V) (hh : B h) :=
    replacementChainMap_pullback_locally_injective
      (s := s) (F := F) j
      (((CategoryHomology.simplicialReplacementComplex
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ F)).d n j).hom
          (Classical.choose (hpre (W := T) h hh))) (hzero h hh)
  let D : ∀ ⦃T : s.base.C⦄ (h : T ⟶ V), B h → Sieve T := fun {T} h hh =>
    Classical.choose (injCover h hh)
  have hD : ∀ ⦃T : s.base.C⦄ (h : T ⟶ V) (hh : B h), D h hh ∈ s.base.J T :=
    fun _ h hh => (Classical.choose_spec (injCover h hh)).1
  obtain ⟨B', hB', hfactor⟩ := covering_sieve_compose s.base.J B hB D hD
  refine ⟨B', hB', ?_⟩
  intro Z f hf
  obtain ⟨T, h, hh, k, hk, hfk⟩ := hfactor f hf
  let y := Classical.choose (hpre h hh)
  have hy := Classical.choose_spec (hpre h hh)
  let mF := CategoryHomology.replacementChainMap.{uC, uC,
    max w uD vD uC}
    ((Functor.chosenPullbacks s.p).pullbackFunctor k)
    (fiberCartesianRestriction s F k)
  let mG := CategoryHomology.replacementChainMap.{uC, uC,
    max w uD vD uC}
    ((Functor.chosenPullbacks s.p).pullbackFunctor k)
    (fiberCartesianRestriction s G k)
  let uT := CategoryHomology.replacementChainMap.{uC, uC,
    max w uD vD uC}
    (𝟭 (s.p.Fiber T)) (fiberSheafificationUnit s F T)
  let uZ := CategoryHomology.replacementChainMap.{uC, uC,
    max w uD vD uC}
    (𝟭 (s.p.Fiber Z)) (fiberSheafificationUnit s F Z)
  have hdiff := (Classical.choose_spec (injCover h hh)).2 k hk
  let y' := (mF.f n).hom y
  have hcycle : ((CategoryHomology.simplicialReplacementComplex
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ F)).d n j).hom y' = 0 := by
    have hm := congrArg (fun q => (ConcreteCategory.hom q) y) (mF.comm n j)
    simp only [ConcreteCategory.comp_apply] at hm
    rw [hm, hdiff]
  let mGh := CategoryHomology.replacementChainMap.{uC, uC,
    max w uD vD uC}
    ((Functor.chosenPullbacks s.p).pullbackFunctor h)
    (fiberCartesianRestriction s G h)
  let p := (Functor.chosenPullbacks s.p).pullbackFunctor k
  let tF : (Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ F ⟶
      p.op ⋙ ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ F) :=
    fiberCartesianRestriction s F k
  let tG : (Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ G ⟶
      p.op ⋙ ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ G) :=
    fiberCartesianRestriction s G k
  let eT : (Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ F ⟶
      (𝟭 (s.p.Fiber T)).op ⋙
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ G) :=
    fiberSheafificationUnit s F T
  let eZ : (Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ F ⟶
      (𝟭 (s.p.Fiber Z)).op ⋙
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ G) :=
    fiberSheafificationUnit s F Z
  have hsquare := fiberUnit_pullback_square (s := s) F k
  have hsquare' := replacementChainMap_pullback_unit_square.{uC,
    max w uD vD uC} p tF tG eT eZ hsquare
  have hmaps := congrArg (fun q => (ConcreteCategory.hom (q.f n)) y) hsquare'
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hmaps
  have himage : (uZ.f n).hom y' = (mG.f n).hom ((uT.f n).hom y) := hmaps
  have hy' : (uT.f n).hom y = (mGh.f n).hom x := by
    simpa [y, uT, mGh, G, fiberSheafificationUnit, fiberCartesianRestriction,
      Functor.leftUnitor] using hy
  rw [hy'] at himage
  refine ⟨T, h, k, y', hcycle, ?_, hfk⟩
  simpa [y', mF, mG, uT, uZ, mGh, G, fiberCartesianRestriction,
    fiberSheafificationUnit] using himage

private theorem chainComplex_homology_has_cycle
    {K : ChainComplex AddCommGrpCat.{v} ℕ} (n : ℕ)
    (z : K.homology n) :
    ∃ a : K.cycles n, (K.homologyπ n) a = z := by
  have hsurj : Function.Surjective (K.homologyπ n) := by
    rw [← AddCommGrpCat.epi_iff_surjective]
    infer_instance
  exact hsurj z

private theorem chainComplex_iCycles_isCycle
    {K : ChainComplex AddCommGrpCat.{v} ℕ} (n : ℕ) (a : K.cycles n) :
    (K.d n ((ComplexShape.down ℕ).next n)) ((K.iCycles n) a) = 0 := by
  have h : ((K.iCycles n ≫ K.d n ((ComplexShape.down ℕ).next n)) a) =
      (0 : K.cycles n ⟶ K.X ((ComplexShape.down ℕ).next n)) a :=
    congrArg (fun f : K.cycles n ⟶ K.X ((ComplexShape.down ℕ).next n) => f a)
      (K.iCycles_d n ((ComplexShape.down ℕ).next n))
  exact h

/-- `iCycles` is natural with respect to `cyclesMap`, as an equation of elements. -/
private theorem chainComplex_iCycles_cyclesMap
    {K L : ChainComplex AddCommGrpCat.{v} ℕ} (f : K ⟶ L) (n : ℕ) (a : K.cycles n) :
    (L.iCycles n).hom ((HomologicalComplex.cyclesMap f n) a) = (f.f n).hom ((K.iCycles n).hom a) :=
  congrArg (fun q => q a) (HomologicalComplex.cyclesMap_i f n)

private theorem chainComplex_cyclesMap_eq_of_chain_eq
    {K L : ChainComplex AddCommGrpCat.{v} ℕ} (f : K ⟶ L) (n : ℕ)
    (a : K.cycles n) (b : L.cycles n)
    (hab : (f.f n) ((K.iCycles n) a) = (L.iCycles n) b) :
    (HomologicalComplex.cyclesMap f n) a = b := by
  apply (AddCommGrpCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  exact (chainComplex_iCycles_cyclesMap f n a).trans hab

private theorem chainComplex_homologyMap_eq_of_cycles_eq
    {K L : ChainComplex AddCommGrpCat.{v} ℕ} (f : K ⟶ L) (n : ℕ)
    (a : K.cycles n) (b : L.cycles n)
    (hab : (HomologicalComplex.cyclesMap f n) a = b) :
    (HomologicalComplex.homologyMap f n) ((K.homologyπ n) a) =
      (L.homologyπ n) b := by
  have h := congrArg (fun q => q a)
    (HomologicalComplex.homologyπ_naturality (φ := f) (i := n))
  change (HomologicalComplex.homologyMap f n) ((K.homologyπ n) a) =
    (L.homologyπ n) ((HomologicalComplex.cyclesMap f n) a) at h
  rwa [hab] at h

private theorem chainComplex_homology_zero_is_boundary
    {K : ChainComplex AddCommGrpCat.{v} ℕ} (n : ℕ) (a : K.cycles n)
    (ha : (K.homologyπ n) a = 0) :
    ∃ b : K.X (n + 1), (K.d (n + 1) n) b = (K.iCycles n) a := by
  let S : ShortComplex AddCommGrpCat := ShortComplex.mk
    (K.toCycles (n + 1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n + 1) n)
  have hS : S.Exact := by
    apply S.exact_of_g_is_cokernel
    simpa [S] using K.homologyIsCokernel (i := n + 1) (j := n) (by simp)
  have hmem : (a : S.X₂) ∈ S.g.hom.ker := by
    show (S.g.hom) a = 0
    simpa [S] using ha
  obtain ⟨b, hb⟩ :=
    (ShortComplex.ab_exact_iff_ker_le_range (S := S)).mp hS hmem
  have hb' : (K.toCycles (n + 1) n) b = a := by
    simpa [S] using hb
  refine ⟨b, ?_⟩
  simpa only [← ConcreteCategory.comp_apply, K.toCycles_i] using congrArg (K.iCycles n) hb'

private noncomputable def chainComplex_cyclesOfElement
    {K : ChainComplex AddCommGrpCat.{v} ℕ} (n : ℕ)
    (x : (K.X n)) (hx : (K.d n ((ComplexShape.down ℕ).next n)).hom x = 0) :
    K.cycles n :=
  ((K.sc n).cyclesIsoKernel).inv.hom
    ((AddCommGrpCat.kernelIsoKer (K.d n ((ComplexShape.down ℕ).next n))).inv.hom
      ⟨x, hx⟩)

private theorem chainComplex_iCycles_cyclesOfElement
    {K : ChainComplex AddCommGrpCat.{v} ℕ} (n : ℕ)
    (x : K.X n) (hx : (K.d n ((ComplexShape.down ℕ).next n)).hom x = 0) :
  (K.iCycles n).hom (chainComplex_cyclesOfElement n x hx) = x := by
  let S := K.sc n
  let d := K.d n ((ComplexShape.down ℕ).next n)
  have hcyc : S.cyclesIsoKernel.inv ≫ S.iCycles = kernel.ι S.g := by
    simp [S, ShortComplex.cyclesIsoKernel]
  have h2 := congrArg (fun q => (ConcreteCategory.hom q) ⟨x, hx⟩)
    (AddCommGrpCat.kernelIsoKer_inv_comp_ι d)
  simp only [ConcreteCategory.comp_apply] at h2
  have hinc := congrArg (fun q => (ConcreteCategory.hom q)
      ((AddCommGrpCat.kernelIsoKer d).inv.hom ⟨x, hx⟩)) hcyc
  change (K.iCycles n).hom (chainComplex_cyclesOfElement n x hx) =
    (kernel.ι S.g).hom ((AddCommGrpCat.kernelIsoKer d).inv.hom ⟨x, hx⟩) at hinc
  exact hinc.trans h2

private theorem categoryHomologyMap_replacement_apply
    {C C' : Type uC} [SmallCategory C] [SmallCategory C']
    (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max uC v}}
    {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max uC v}}
    (t : F' ⟶ f.op ⋙ F) (n : ℕ)
    (a : (CategoryHomology.simplicialReplacementComplex F').cycles n)
    (b : (CategoryHomology.simplicialReplacementComplex F).cycles n)
    (hab : HomologicalComplex.cyclesMap
      (CategoryHomology.replacementChainMap f t) n a = b) :
    (CategoryHomology.categoryHomologyMap f t n).hom
        ((CategoryHomology.categoryHomologyReplacementIso F' n).inv.hom
          (((CategoryHomology.simplicialReplacementComplex F').homologyπ n).hom a)) =
      (CategoryHomology.categoryHomologyReplacementIso F n).inv.hom
        (((CategoryHomology.simplicialReplacementComplex F).homologyπ n).hom b) := by
  let K' := CategoryHomology.simplicialReplacementComplex F'
  let K := CategoryHomology.simplicialReplacementComplex F
  let I' := CategoryHomology.categoryHomologyReplacementIso F' n
  let I := CategoryHomology.categoryHomologyReplacementIso F n
  have hhom := chainComplex_homologyMap_eq_of_cycles_eq
    (CategoryHomology.replacementChainMap f t) n a b hab
  have hmap := congrArg (fun q => (ConcreteCategory.hom q)
      (I'.inv.hom ((K'.homologyπ n).hom a)))
    (CategoryHomology.replacementChainMap_homologyMap f t n)
  simp only [ConcreteCategory.comp_apply] at hmap
  apply (AddCommGrpCat.mono_iff_injective I.hom).mp inferInstance
  show I.hom.hom ((CategoryHomology.categoryHomologyMap f t n).hom
      (I'.inv.hom ((K'.homologyπ n).hom a))) =
    I.hom.hom (I.inv.hom ((K.homologyπ n).hom b))
  calc
    _ = (HomologicalComplex.homologyMap
          (CategoryHomology.replacementChainMap f t) n).hom
        (I'.hom.hom (I'.inv.hom ((K'.homologyπ n).hom a))) := hmap.symm
    _ = (K.homologyπ n).hom b := by simpa [I', K', K] using hhom
    _ = I.hom.hom (I.inv.hom ((K.homologyπ n).hom b)) := by simp

private theorem fiberHomology_map_unit_app
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ) (V : s.base.C) :
    ((fiberHomologyPresheafFunctor s n).map
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)).app
      (.op V) =
      CategoryHomology.categoryHomologyMap.{uC, uC, max w uD vD uC}
        (𝟭 (s.p.Fiber V)) (fiberSheafificationUnit s F V) n :=
  rfl

/-- The unit map on fibre homology sends the class of a cycle to the class of its image. -/
private theorem fiberHomology_map_unit_replacement
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ) (V : s.base.C)
    (c : (CategoryHomology.simplicialReplacementComplex
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F)).cycles n) :
    (((fiberHomologyPresheafFunctor s n).map
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)).app
        (.op V)).hom
      ((CategoryHomology.categoryHomologyReplacementIso.{uC, max w uD vD uC}
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F) n).inv.hom
        (((CategoryHomology.simplicialReplacementComplex
          ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F)).homologyπ n).hom c)) =
      (CategoryHomology.categoryHomologyReplacementIso.{uC, max w uD vD uC}
        ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙
          (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
            ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)) n).inv.hom
        (((CategoryHomology.simplicialReplacementComplex
          ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙
            (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
              ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F))).homologyπ
            n).hom
          (HomologicalComplex.cyclesMap (CategoryHomology.replacementChainMap.{uC, uC,
            max w uD vD uC} (𝟭 (s.p.Fiber V)) (fiberSheafificationUnit s F V)) n c)) := by
  rw [fiberHomology_map_unit_app]
  exact categoryHomologyMap_replacement_apply.{uC, max w uD vD uC}
    (𝟭 (s.p.Fiber V)) (fiberSheafificationUnit s F V) n c _ rfl

private theorem fiberHomology_unit_locally_surjective
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ)
    [Presheaf.IsLocallySurjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)]
    [Presheaf.IsLocallyInjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)] :
    Presheaf.IsLocallySurjective s.base.J
      ((fiberHomologyPresheafFunctor s n).map
        ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)) := by
  classical
  let η := (sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F
  let G := (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
    ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)
  let φ := (fiberHomologyPresheafFunctor s n).map η
  refine ⟨?_⟩
  intro V z
  let I_V := CategoryHomology.categoryHomologyReplacementIso.{uC,
    max w uD vD uC}
    ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ G) n
  let K_V := CategoryHomology.simplicialReplacementComplex
    ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ G)
  obtain ⟨a, ha⟩ := chainComplex_homology_has_cycle (K := K_V) n (I_V.hom.hom z)
  let x := (K_V.iCycles n).hom a
  have hx := chainComplex_iCycles_isCycle (K := K_V) n a
  obtain ⟨B, hB, hlift⟩ := replacementChainMap_pullback_locally_surjective_cycle
    (s := s) (F := F) n x hx
  have hle : B ≤ Presheaf.imageSieve φ z := by
    intro Z f hf
    obtain ⟨T, h, k, y, hcycle, himage, rfl⟩ := hlift f hf
    let K_FZ := CategoryHomology.simplicialReplacementComplex
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ F)
    let K_GZ := CategoryHomology.simplicialReplacementComplex
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ G)
    let mU := CategoryHomology.replacementChainMap.{uC, uC,
      max w uD vD uC} (𝟭 (s.p.Fiber Z)) (fiberSheafificationUnit s F Z)
    let mGh := CategoryHomology.replacementChainMap.{uC, uC,
      max w uD vD uC} ((Functor.chosenPullbacks s.p).pullbackFunctor h)
        (fiberCartesianRestriction s G h)
    let mGk := CategoryHomology.replacementChainMap.{uC, uC,
      max w uD vD uC} ((Functor.chosenPullbacks s.p).pullbackFunctor k)
        (fiberCartesianRestriction s G k)
    let bF := chainComplex_cyclesOfElement (K := K_FZ) n y hcycle
    let bG := HomologicalComplex.cyclesMap mU n bF
    let aT := HomologicalComplex.cyclesMap mGh n a
    let aZ := HomologicalComplex.cyclesMap mGk n aT
    let I_FZ := CategoryHomology.categoryHomologyReplacementIso.{uC,
      max w uD vD uC}
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ F) n
    let I_GZ := CategoryHomology.categoryHomologyReplacementIso.{uC,
      max w uD vD uC}
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ G) n
    let K_GT := CategoryHomology.simplicialReplacementComplex
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ G)
    let I_GT := CategoryHomology.categoryHomologyReplacementIso.{uC,
      max w uD vD uC}
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ G) n
    have hbF : (K_FZ.iCycles n).hom bF = y :=
      chainComplex_iCycles_cyclesOfElement (K := K_FZ) n y hcycle
    have hbG : (K_GZ.iCycles n).hom bG = (mU.f n).hom y := by
      rw [chainComplex_iCycles_cyclesMap, hbF]
    have haZchain : (K_GZ.iCycles n).hom aZ =
        (mGk.f n).hom ((mGh.f n).hom ((K_V.iCycles n).hom a)) := by
      rw [chainComplex_iCycles_cyclesMap mGk n aT, chainComplex_iCycles_cyclesMap mGh n a]
    have hcyc : aZ = bG := by
      apply (AddCommGrpCat.mono_iff_injective (K_GZ.iCycles n)).mp inferInstance
      rw [haZchain, hbG, himage]
    have hφ : (φ.app (.op Z)).hom
        (I_FZ.inv.hom ((K_FZ.homologyπ n).hom bF)) =
        I_GZ.inv.hom ((K_GZ.homologyπ n).hom bG) :=
      fiberHomology_map_unit_replacement s F n Z bF
    have hresH :
        ((fiberHomologyPresheaf s G n).map (.op k)).hom
          (((fiberHomologyPresheaf s G n).map (.op h)).hom
            (I_V.inv.hom ((K_V.homologyπ n).hom a))) =
        I_GZ.inv.hom ((K_GZ.homologyπ n).hom aZ) := by
      show (CategoryHomology.categoryHomologyMap.{uC, uC,
        max w uD vD uC}
          ((Functor.chosenPullbacks s.p).pullbackFunctor k)
          (fiberCartesianRestriction s G k) n).hom
          ((CategoryHomology.categoryHomologyMap.{uC, uC,
            max w uD vD uC}
            ((Functor.chosenPullbacks s.p).pullbackFunctor h)
            (fiberCartesianRestriction s G h) n).hom
              (I_V.inv.hom ((K_V.homologyπ n).hom a))) = _
      calc
        _ = (CategoryHomology.categoryHomologyMap.{uC, uC,
          max w uD vD uC}
              ((Functor.chosenPullbacks s.p).pullbackFunctor k)
              (fiberCartesianRestriction s G k) n).hom
              (I_GT.inv.hom ((K_GT.homologyπ n).hom aT)) :=
            congrArg (fun q =>
              (CategoryHomology.categoryHomologyMap.{uC, uC,
                max w uD vD uC}
                ((Functor.chosenPullbacks s.p).pullbackFunctor k)
                (fiberCartesianRestriction s G k) n).hom q)
              (categoryHomologyMap_replacement_apply.{uC, max w uD vD uC}
                ((Functor.chosenPullbacks s.p).pullbackFunctor h)
                (fiberCartesianRestriction s G h) n a aT (by simp [aT, mGh]))
        _ = I_GZ.inv.hom ((K_GZ.homologyπ n).hom aZ) :=
            categoryHomologyMap_replacement_apply.{uC, max w uD vD uC}
              ((Functor.chosenPullbacks s.p).pullbackFunctor k)
              (fiberCartesianRestriction s G k) n aT aZ (by simp [aZ, mGk])
    have hz : I_V.inv.hom ((K_V.homologyπ n).hom a) = z := by
      apply (AddCommGrpCat.mono_iff_injective I_V.hom).mp inferInstance
      simp [I_V, ha]
    refine ⟨I_FZ.inv.hom ((K_FZ.homologyπ n).hom bF), ?_⟩
    show (φ.app (.op Z)).hom
        (I_FZ.inv.hom ((K_FZ.homologyπ n).hom bF)) =
      ((fiberHomologyPresheaf s G n).map (.op (k ≫ h))).hom z
    rw [hφ, ← hcyc, ← hresH, hz]
    show ((fiberHomologyPresheaf s G n).map (.op k)).hom
        (((fiberHomologyPresheaf s G n).map (.op h)).hom z) =
      ((fiberHomologyPresheaf s G n).map (.op (k ≫ h))).hom z
    simp only [CategoryTheory.op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact s.base.J.superset_covering hle hB

private theorem fiberHomology_unit_locally_injective
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ)
    [Presheaf.IsLocallySurjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)]
    [Presheaf.IsLocallyInjective s.topology
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)] :
    Presheaf.IsLocallyInjective s.base.J
      ((fiberHomologyPresheafFunctor s n).map
        ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)) := by
  classical
  let η := (sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F
  let G := (sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
    ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)
  let φ := (fiberHomologyPresheafFunctor s n).map η
  let H := fiberHomologyPresheaf s F n
  refine ⟨?_⟩
  intro Vop a b hab
  let V := Vop.unop
  let z := a - b
  dsimp [fiberHomologyPresheafFunctor] at z
  have hφz : (φ.app (.op V)).hom z = 0 := by
    dsimp [z]
    rw [map_sub, hab, sub_self]
  let I_FV := CategoryHomology.categoryHomologyReplacementIso.{uC,
    max w uD vD uC} ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F) n
  let I_GV := CategoryHomology.categoryHomologyReplacementIso.{uC,
    max w uD vD uC} ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ G) n
  let K_FV := CategoryHomology.simplicialReplacementComplex
    ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F)
  let K_GV := CategoryHomology.simplicialReplacementComplex
    ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ G)
  obtain ⟨cV, hcV⟩ := chainComplex_homology_has_cycle (K := K_FV) n (I_FV.hom.hom z)
  let uV := CategoryHomology.replacementChainMap.{uC, uC,
    max w uD vD uC} (𝟭 (s.p.Fiber V)) (fiberSheafificationUnit s F V)
  let bG := HomologicalComplex.cyclesMap uV n cV
  have hz : I_FV.inv.hom ((K_FV.homologyπ n).hom cV) = z := by
    apply (AddCommGrpCat.mono_iff_injective I_FV.hom).mp inferInstance
    simp [I_FV, hcV]
  have hφrep : (φ.app (.op V)).hom z = I_GV.inv.hom ((K_GV.homologyπ n).hom bG) := by
    rw [← hz]
    exact fiberHomology_map_unit_replacement s F n V cV
  have hπbG : (K_GV.homologyπ n).hom bG = 0 := by
    apply (AddCommGrpCat.mono_iff_injective I_GV.inv).mp inferInstance
    rw [map_zero, ← hφrep]
    exact hφz
  obtain ⟨q, hboundary⟩ := chainComplex_homology_zero_is_boundary (K := K_GV) n bG hπbG
  have hunitV : (uV.f n).hom ((K_FV.iCycles n).hom cV) =
      (K_GV.d (n + 1) n).hom q := by
    exact (chainComplex_iCycles_cyclesMap uV n cV).symm.trans hboundary.symm
  obtain ⟨B, hB, hlift⟩ := replacementChainMap_pullback_locally_surjective
    (s := s) (F := F) (n + 1) q
  let mF (T : s.base.C) (h : T ⟶ V) :=
    CategoryHomology.replacementChainMap.{uC, uC,
      max w uD vD uC} ((Functor.chosenPullbacks s.p).pullbackFunctor h)
      (fiberCartesianRestriction s F h)
  let mG (T : s.base.C) (h : T ⟶ V) :=
    CategoryHomology.replacementChainMap.{uC, uC,
      max w uD vD uC} ((Functor.chosenPullbacks s.p).pullbackFunctor h)
      (fiberCartesianRestriction s G h)
  let uT (T : s.base.C) := CategoryHomology.replacementChainMap.{uC, uC,
    max w uD vD uC} (𝟭 (s.p.Fiber T)) (fiberSheafificationUnit s F T)
  let vchain {T : s.base.C} (h : T ⟶ V) (hh : B h) :=
      ((mF T h).f n).hom ((K_FV.iCycles n).hom cV) -
        ((CategoryHomology.simplicialReplacementComplex
          ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ F)).d (n + 1) n).hom
          (Classical.choose (hlift h hh))
  have hzero : ∀ ⦃T : s.base.C⦄ (h : T ⟶ V) (hh : B h),
      ((uT T).f n).hom (vchain h hh) = 0 := by
    intro T h hh
    let qlift := Classical.choose (hlift h hh)
    have hq := Classical.choose_spec (hlift h hh)
    let p := (Functor.chosenPullbacks s.p).pullbackFunctor h
    let tF : (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F ⟶
        p.op ⋙ ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ F) :=
      fiberCartesianRestriction s F h
    let tG : (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ G ⟶
        p.op ⋙ ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ G) :=
      fiberCartesianRestriction s G h
    let eV : (Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F ⟶
        (𝟭 (s.p.Fiber V)).op ⋙ ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ G) :=
      fiberSheafificationUnit s F V
    let eT : (Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ F ⟶
        (𝟭 (s.p.Fiber T)).op ⋙ ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ G) :=
      fiberSheafificationUnit s F T
    have hsquare := replacementChainMap_pullback_unit_square.{uC,
      max w uD vD uC} p tF tG eV eT (fiberUnit_pullback_square (s := s) F h)
    have hs := congrArg (fun r => (ConcreteCategory.hom (r.f n))
        ((K_FV.iCycles n).hom cV)) hsquare
    simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hs
    have hq' : ((uT T).f (n + 1)).hom qlift = ((mG T h).f (n + 1)).hom q := by
      simpa [qlift, uT, mG, G, fiberSheafificationUnit, fiberCartesianRestriction,
        Functor.leftUnitor] using hq
    let K_FT := CategoryHomology.simplicialReplacementComplex
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ F)
    let K_GT := CategoryHomology.simplicialReplacementComplex
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ G)
    have hcomm := congrArg (fun r => (ConcreteCategory.hom r) q)
      ((mG T h).comm (n + 1) n)
    simp only [ConcreteCategory.comp_apply] at hcomm
    have hcomm' : (K_GT.d (n + 1) n).hom (((mG T h).f (n + 1)).hom q) =
        ((mG T h).f n).hom ((K_GV.d (n + 1) n).hom q) := hcomm
    have hdiff := congrArg (fun r => (ConcreteCategory.hom r) qlift)
      ((uT T).comm (n + 1) n)
    simp only [ConcreteCategory.comp_apply] at hdiff
    show ((uT T).f n).hom
        (((mF T h).f n).hom ((K_FV.iCycles n).hom cV) -
          ((CategoryHomology.simplicialReplacementComplex
            ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ F)).d (n + 1) n).hom qlift) = 0
    rw [map_sub, hs, hunitV, ← hdiff, hq', hcomm']
    show ((mG T h).f n).hom ((K_GV.d (n + 1) n).hom q) -
      ((mG T h).f n).hom ((K_GV.d (n + 1) n).hom q) = 0
    simp
  let injCover {T : s.base.C} (h : T ⟶ V) (hh : B h) :=
    replacementChainMap_pullback_locally_injective (s := s) (F := F) n
      (vchain h hh) (hzero h hh)
  let D : ∀ ⦃T : s.base.C⦄ (h : T ⟶ V), B h → Sieve T := fun {T} h hh =>
    Classical.choose (injCover h hh)
  have hD : ∀ ⦃T : s.base.C⦄ (h : T ⟶ V) (hh : B h), D h hh ∈ s.base.J T :=
    fun _ h hh => (Classical.choose_spec (injCover h hh)).1
  obtain ⟨B', hB', hfactor⟩ := covering_sieve_compose s.base.J B hB D hD
  have hle : B' ≤ Presheaf.equalizerSieve a b := by
    intro Z f hf
    obtain ⟨T, h, hh, k, hk, hfk⟩ := hfactor f hf
    let qlift := Classical.choose (hlift h hh)
    let mFh := mF T h
    let mFk := CategoryHomology.replacementChainMap.{uC, uC,
      max w uD vD uC} ((Functor.chosenPullbacks s.p).pullbackFunctor k)
        (fiberCartesianRestriction s F k)
    let K_FT := CategoryHomology.simplicialReplacementComplex
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := T)).op ⋙ F)
    let K_FZ := CategoryHomology.simplicialReplacementComplex
      ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ F)
    let aT := HomologicalComplex.cyclesMap mFh n cV
    let aZ := HomologicalComplex.cyclesMap mFk n aT
    have hdiff0 := (Classical.choose_spec (injCover h hh)).2 k hk
    have hbd : (mFk.f n).hom ((mFh.f n).hom ((K_FV.iCycles n).hom cV)) =
        (K_FZ.d (n + 1) n).hom ((mFk.f (n + 1)).hom qlift) := by
      dsimp [vchain] at hdiff0
      change (mFk.f n).hom
        ((mFh.f n).hom ((K_FV.iCycles n).hom cV) -
          (K_FT.d (n + 1) n).hom qlift) = 0 at hdiff0
      have hsub := map_sub (mFk.f n).hom
        ((mFh.f n).hom ((K_FV.iCycles n).hom cV))
        ((K_FT.d (n + 1) n).hom qlift)
      rw [hsub, sub_eq_zero] at hdiff0
      have hcomm := congrArg (fun r => (ConcreteCategory.hom r) qlift)
        (mFk.comm (n + 1) n)
      simpa only [ConcreteCategory.comp_apply] using hdiff0.trans hcomm.symm
    have haZchain : (K_FZ.iCycles n).hom aZ =
        (K_FZ.d (n + 1) n).hom ((mFk.f (n + 1)).hom qlift) := by
      rw [chainComplex_iCycles_cyclesMap mFk n aT, chainComplex_iCycles_cyclesMap mFh n cV, hbd]
    have hπaZ : (K_FZ.homologyπ n).hom aZ = 0 := by
      have hcyc : aZ = (K_FZ.toCycles (n + 1) n).hom
          ((mFk.f (n + 1)).hom qlift) := by
        apply (AddCommGrpCat.mono_iff_injective (K_FZ.iCycles n)).mp inferInstance
        have ht := congrArg (fun q => (ConcreteCategory.hom q)
            ((mFk.f (n + 1)).hom qlift)) (K_FZ.toCycles_i (n + 1) n)
        simp only [ConcreteCategory.comp_apply] at ht
        exact haZchain.trans ht.symm
      rw [hcyc]
      have ht := congrArg (fun q => (ConcreteCategory.hom q)
          ((mFk.f (n + 1)).hom qlift)) (K_FZ.toCycles_comp_homologyπ (n + 1) n)
      show (K_FZ.homologyπ n).hom
        ((K_FZ.toCycles (n + 1) n).hom ((mFk.f (n + 1)).hom qlift)) = 0
      exact ht
    let I_FZ := CategoryHomology.categoryHomologyReplacementIso.{uC,
      max w uD vD uC} ((Functor.Fiber.fiberInclusion (p := s.p) (S := Z)).op ⋙ F) n
    let I_FV := CategoryHomology.categoryHomologyReplacementIso.{uC,
      max w uD vD uC} ((Functor.Fiber.fiberInclusion (p := s.p) (S := V)).op ⋙ F) n
    have hres : (H.map (.op k)).hom ((H.map (.op h)).hom z) = 0 := by
      have hrep := categoryHomologyMap_replacement_apply.{uC, max w uD vD uC}
        ((Functor.chosenPullbacks s.p).pullbackFunctor h)
        (fiberCartesianRestriction s F h) n cV aT (by simp [aT, mFh, mF])
      have hrep' := categoryHomologyMap_replacement_apply.{uC, max w uD vD uC}
        ((Functor.chosenPullbacks s.p).pullbackFunctor k)
        (fiberCartesianRestriction s F k) n aT aZ rfl
      have hz : I_FV.inv.hom ((K_FV.homologyπ n).hom cV) = z := by
        have hcV' := hcV
        change (K_FV.homologyπ n).hom cV = I_FV.hom.hom z at hcV'
        rw [hcV']
        simp
      rw [← hz]
      rw [fiberHomologyPresheaf_map s F n k,
        fiberHomologyPresheaf_map s F n h]
      show (CategoryHomology.categoryHomologyMap.{uC, uC,
          max w uD vD uC}
          ((Functor.chosenPullbacks s.p).pullbackFunctor k)
          (fiberCartesianRestriction s F k) n).hom
          ((CategoryHomology.categoryHomologyMap.{uC, uC,
            max w uD vD uC}
            ((Functor.chosenPullbacks s.p).pullbackFunctor h)
            (fiberCartesianRestriction s F h) n).hom
              (I_FV.inv.hom ((K_FV.homologyπ n).hom cV))) = 0
      rw [hrep, hrep', hπaZ]
      simp
    have hcomp : (H.map (.op f)).hom z = (H.map (.op k)).hom ((H.map (.op h)).hom z) := by
      rw [hfk]
      rw [fiberHomologyPresheaf_map s F n (k ≫ h),
        fiberHomologyPresheaf_map s F n k,
        fiberHomologyPresheaf_map s F n h]
      have hmap := CategoryHomology.categoryHomologyMap_pullbackFunctor_comp.{uD, vD, uC, w}
        s.p F (fun {_ _} h => fiberCartesianRestriction s F h) (fun {_ _} _ _ => rfl) n k h
      exact congrArg (fun q => q.hom z) hmap
    have hzf : (H.map (.op f)).hom z = 0 := hcomp.trans hres
    have hxy : (H.map (.op f)).hom a = (H.map (.op f)).hom b := by
      simpa [z, map_sub, sub_eq_zero] using hzf
    rw [Presheaf.equalizerSieve_apply]
    show (H.map (.op f)).hom a = (H.map (.op f)).hom b
    exact hxy
  exact s.base.J.superset_covering hle hB'

/-- Sheafifying the coefficients on the total category does not change the
associated sheaf of fibre homology. -/
@[stacks 08PI]
theorem fiberHomologySheaf_sheafify
    [HasWeakSheafify s.base.J AddCommGrpCat.{max w uD vD uC}]
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ) :
    IsIso ((presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC}).map
      ((fiberHomologyPresheafFunctor s n).map
        ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F))) := by
  have : EssentiallySmall.{max w uD vD uC} s.C :=
    CategoryTheory.essentiallySmallSelf.{max w uD vD uC, uC, uC} s.C
  have : EssentiallySmall.{max w uD vD uC} s.base.C :=
    CategoryTheory.essentiallySmallSelf.{max w uD vD uC, vD, uD} s.base.C
  have : ((equivSmallModel.{max w uD vD uC} s.C).inverse.inducedTopology
      s.topology).WEqualsLocallyBijective AddCommGrpCat.{max w uD vD uC} :=
    inferInstance
  have : ((equivSmallModel.{max w uD vD uC} s.base.C).inverse.inducedTopology
      s.base.J).WEqualsLocallyBijective AddCommGrpCat.{max w uD vD uC} :=
    inferInstance
  have : s.topology.WEqualsLocallyBijective AddCommGrpCat.{max w uD vD uC} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{uC,
      max w uD vD uC, uC, (max w uD vD uC) + 1, max w uD vD uC}
      (C := s.C) (A := AddCommGrpCat.{max w uD vD uC}) s.topology
  have : s.base.J.WEqualsLocallyBijective AddCommGrpCat.{max w uD vD uC} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{vD,
      max w uD vD uC, uD, (max w uD vD uC) + 1, max w uD vD uC}
      (C := s.base.C) (A := AddCommGrpCat.{max w uD vD uC}) s.base.J
  let η := (sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F
  have : Presheaf.IsLocallySurjective s.topology η := by
    simpa [η, sheafificationAdjunction_unit_app] using
      (s.topology.W_toSheafify F).isLocallySurjective
  have : Presheaf.IsLocallyInjective s.topology η := by
    simpa [η, sheafificationAdjunction_unit_app] using
      (s.topology.W_toSheafify F).isLocallyInjective
  let φ := (fiberHomologyPresheafFunctor s n).map η
  show IsIso ((presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC}).map φ)
  exact (Sheaf.isLocallyBijective_iff_isIso
    ((presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC}).map φ)).1
      ⟨(Presheaf.isLocallyInjective_presheafToSheaf_map_iff s.base.J φ).2
        (fiberHomology_unit_locally_injective (s := s) F n),
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff s.base.J φ).2
        (fiberHomology_unit_locally_surjective (s := s) F n)⟩

/-- **Stacks 08PI.** The sheaf `L_n(F)` of fibre homology is unchanged when the coefficient
presheaf is replaced by its sheafification on the total category: the canonical map
`L_n(F) ⟶ L_n(F^#)` of `fiberHomologySheaf_sheafify` is an isomorphism. -/
@[stacks 08PI "the sheaf of fibre homology is unchanged by sheafifying the coefficients"]
def fiberHomologySheafSheafifyIso
    [HasWeakSheafify s.base.J AddCommGrpCat.{max w uD vD uC}]
    [HasWeakSheafify s.topology AddCommGrpCat.{max w uD vD uC}]
    (F : s.Cᵒᵖ ⥤ AddCommGrpCat.{max w uD vD uC}) (n : ℕ) :
    fiberHomologySheaf s F n ≅
      fiberHomologySheaf s
        ((sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj
          ((presheafToSheaf s.topology AddCommGrpCat.{max w uD vD uC}).obj F)) n :=
  have := fiberHomologySheaf_sheafify s F n
  asIso ((presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC}).map
    ((fiberHomologyPresheafFunctor s n).map
      ((sheafificationAdjunction s.topology AddCommGrpCat.{max w uD vD uC}).unit.app F)))

end Stacks.Sites.FibredCategory

end
