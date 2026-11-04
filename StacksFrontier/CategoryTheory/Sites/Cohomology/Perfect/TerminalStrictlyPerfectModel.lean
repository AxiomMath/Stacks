module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor

/-!
# A strictly perfect local model over a terminal object is a global one

Let `(C, O)` be a ringed site with a terminal object `t`. The slice of the site at `t` is the
site itself, so restriction of modules to the slice over `t` is an equivalence. Hence a strictly
perfect complex on the slice over `t`, with a quasi-isomorphism to the restriction of a complex
`K`, comes from a strictly perfect complex of `O`-modules with a quasi-isomorphism to `K`.

This is how the local models of Stacks 08G5 over the members of a covering become global models
on the members, when each member is itself the terminal object of a ringed site (for instance
the identity chart of a representable algebraic space, Stacks 04M0).

## Main definitions

* `AlgebraicGeometry.RingedSite.overTerminalModuleEquivalence`: restriction of modules to the
  slice at a terminal object, as an equivalence.

## Main results

* `AlgebraicGeometry.RingedSite.exists_isStrictlyPerfect_quasiIso_of_isTerminal`: a strictly
  perfect local model over a terminal object gives a global strictly perfect model.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse of the slice equivalence at a terminal object is cocontinuous. -/
theorem isCocontinuous_equivalenceOfIsTerminal_inverse {t : X.C} (ht : IsTerminal t) :
    (Over.equivalenceOfIsTerminal ht).inverse.IsCocontinuous X.J (X.J.over t) := by
  let eCat := Over.equivalenceOfIsTerminal ht
  refine ⟨fun {Y} S hS => ?_⟩
  rw [GrothendieckTopology.mem_over_iff] at hS
  have hEq : S.functorPullback eCat.inverse = Sieve.overEquiv (eCat.inverse.obj Y) S := by
    ext Z f
    let f' : Z ⟶ (eCat.inverse.obj Y).left := (eCat.inverse.map f).left
    change S (eCat.inverse.map f) ↔ (Sieve.overEquiv (eCat.inverse.obj Y) S) f'
    rw [Sieve.overEquiv_iff]
    let a : Over.mk (f' ≫ (eCat.inverse.obj Y).hom) ≅ eCat.inverse.obj Z :=
      Over.isoMk (Iso.refl Z) (ht.hom_ext _ _)
    refine ⟨fun hf => ?_, fun hf => ?_⟩ <;>
      [convert S.downward_closed hf a.hom using 1; convert S.downward_closed hf a.inv using 1] <;>
      (ext; exact (Category.id_comp _).symm)
  rwa [hEq]

omit [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse of the slice equivalence at a terminal object is continuous. -/
theorem isContinuous_equivalenceOfIsTerminal_inverse {t : X.C} (ht : IsTerminal t) :
    (Over.equivalenceOfIsTerminal ht).inverse.IsContinuous X.J (X.J.over t) := by
  let eCat := Over.equivalenceOfIsTerminal ht
  have := isCocontinuous_equivalenceOfIsTerminal_inverse X ht
  have : (Over.forget t).IsContinuous (X.J.over t) X.J := inferInstance
  have : eCat.functor.IsCocontinuous (X.J.over t) X.J :=
    inferInstanceAs ((Over.forget t).IsCocontinuous _ _)
  have : eCat.inverse.IsLeftAdjoint := eCat.symm.isLeftAdjoint_functor
  exact eCat.toAdjunction.isContinuous_of_isCocontinuous (X.J.over t) X.J

/-- **Restriction of modules to the slice at a terminal object is an equivalence.** The slice at
a terminal object `t` is the site itself (`Over.equivalenceOfIsTerminal`), and the two
restrictions of the structure sheaf along that equivalence are the structure sheaf. -/
def overTerminalModuleEquivalence {t : X.C} (ht : IsTerminal t) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over t) :=
  haveI := isContinuous_equivalenceOfIsTerminal_inverse X ht
  haveI : (Over.equivalenceOfIsTerminal ht).functor.IsContinuous (X.J.over t) X.J :=
    inferInstanceAs ((Over.forget t).IsContinuous (X.J.over t) X.J)
  SheafOfModules.pushforwardPushforwardEquivalence (Over.equivalenceOfIsTerminal ht)
    (S := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over t)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝟙 _) (𝟙 _)
    (by ext : 2; exact (Stacks.SheafOfModules.Tensor.ringSheaf X.O).1.map_id _)
    (by ext : 2; exact ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over t).1.map_id _)

omit [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The functor of `AlgebraicGeometry.RingedSite.overTerminalModuleEquivalence` is restriction
to the slice. -/
theorem overTerminalModuleEquivalence_functor {t : X.C} (ht : IsTerminal t) :
    (overTerminalModuleEquivalence X ht).functor =
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) t :=
  rfl

/-- **A strictly perfect local model over a terminal object is a global model.** Let `t` be a
terminal object of the site and `K` a complex of `O`-modules carrying a strictly perfect complex
`P` on the slice over `t` with a quasi-isomorphism `P ⟶ K|_t`. Then `K` receives a
quasi-isomorphism from a strictly perfect complex of `O`-modules: apply the inverse of the slice
equivalence, which is exact and carries the unit of the slice to the unit. -/
theorem exists_isStrictlyPerfect_quasiIso_of_isTerminal {t : X.C} (ht : IsTerminal t)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (h : X.HasStrictlyPerfectQuasiIso K t) :
    ∃ P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P ∧
        ∃ q : P ⟶ K, QuasiIso q := by
  obtain ⟨P, hP, q, hq⟩ := h
  let e := overTerminalModuleEquivalence X ht
  let G := e.inverse
  have : G.Additive := G.additive_of_preserves_binary_products
  have : e.functor.Additive := e.functor.additive_of_preserves_binary_products
  let eG : G.obj (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over t)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    G.mapIso (Iso.refl _ :
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over t) ≅
          e.functor.obj (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≪≫
      (e.unitIso.app (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).symm
  let c : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (X.restrictComplex K t) ≅ K :=
    ((Functor.mapHomologicalComplexCompIso (F := e.functor) (G := G) (Iso.refl _)
        (ComplexShape.up ℤ)).app K) ≪≫
      (NatIso.mapHomologicalComplex e.unitIso.symm (ComplexShape.up ℤ)).app K ≪≫
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app K
  exact ⟨_, SheafOfModules.isStrictlyPerfect_map G eG hP,
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ c.hom, inferInstance⟩

end AlgebraicGeometry.RingedSite
