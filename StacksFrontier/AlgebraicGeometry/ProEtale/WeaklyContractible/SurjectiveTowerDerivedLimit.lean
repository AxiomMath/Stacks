module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SurjectiveTower
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EpimorphicDifferenceLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.SurjectiveTowerDifference

/-!
# Derived limits of surjective towers on a weakly contractible site

Let `C` be a site with a covering collection of weakly contractible objects and `O` a sheaf of
rings on it. Stacks 0947 says that a countable inverse system of sheaves of `O`-modules with
surjective transition maps has `R¹ lim = 0`. This file proves it in the form of the Milnor
difference, and deduces that the termwise limit of a degreewise surjective tower of complexes of
sheaves of modules is its derived limit.

## Main results

* `Stacks.WeaklyContractible.epi_milnorDifference_of_epi_map_succ`: the Milnor difference
  `1 - shift` of a surjective tower of sheaves of modules is an epimorphism, i.e. `R¹ lim = 0`.
* `Stacks.WeaklyContractible.isDerivedLimitWithProjections_Q_limit_of_epi_f`: the termwise limit
  of a degreewise surjective tower of complexes of sheaves of modules is its derived limit.

## Implementation notes

Over a weakly contractible object the transition maps are surjective on sections and sections
commute with products, so a preimage under `1 - shift` is built one stage at a time
(`Stacks.InverseSystem.surjective_pi_sub_shift`); local surjectivity on the covering collection
gives the epimorphism. The tower conventions are those of
`StacksFrontier/AlgebraicGeometry/ProEtale/WeaklyContractible/SurjectiveTower.lean`.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u t

namespace Stacks.WeaklyContractible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

open Stacks.SheafOfModules.WeaklyContractible in
/-- **The Milnor difference of a surjective tower is surjective** (Stacks 0947). On a ringed site
with a covering collection of weakly contractible objects, if every transition map `Gₙ₊₁ ⟶ Gₙ`
of a countable inverse system of sheaves of modules is an epimorphism, so is
`1 - shift : ∏ Gₙ ⟶ ∏ Gₙ`; that is, `R¹ lim Gₙ = 0`.

Over a weakly contractible object the transition maps are surjective on sections and sections
commute with products, so a preimage is built one stage at a time
(`Stacks.InverseSystem.surjective_pi_sub_shift`). -/
theorem epi_milnorDifference_of_epi_map_succ
    (S : WeaklyContractibleObjectsSituation.{w, v, u, t} C J)
    (G : ℕᵒᵖ ⥤ SheafOfModules.{t} S.O)
    (hG : ∀ n : ℕ, Epi (G.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (Stacks.InverseSystem.milnorDifference (fun n : ℕ ↦ G.obj ⟨n⟩)
      (fun n : ℕ ↦ G.map (homOfLE (Nat.le_succ n)).op)) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (isLocallySurjective_of_surjective_of_hasEnoughObjects J _ S.B S.hasEnoughObjects
      fun U hU ↦ ?_)
  let Γ := sectionsOver.{t} S.O U
  let T : SheafOfModules.{t} S.O ⥤ Type t := Γ ⋙ forget AddCommGrpCat.{t}
  let X := fun n : ℕ ↦ G.obj ⟨n⟩
  have hT : IsLimit (T.mapCone (limit.cone (Discrete.functor X))) :=
    isLimitOfPreserves T (limit.isLimit _)
  have hsucc : ∀ n : ℕ, Function.Surjective (Γ.map (G.map (homOfLE (Nat.le_succ n)).op)) :=
    fun n ↦ by
      have := hG n
      exact surjective_sections_of_epi (G.map (homOfLE (Nat.le_succ n)).op) U
        fun _ _ _ h ↦ S.isWeaklyContractible hU _ _ _ h
  intro y
  obtain ⟨x, hx⟩ := Stacks.InverseSystem.surjective_pi_sub_shift
    (M := fun n : ℕ ↦ Γ.obj (X n)) (fun n ↦ Γ.map (G.map (homOfLE (Nat.le_succ n)).op))
    hsucc (fun n ↦ Γ.map (Pi.π X n) y)
  let d := Stacks.InverseSystem.milnorDifference X (fun n : ℕ ↦ G.map (homOfLE (Nat.le_succ n)).op)
  have key (a : Γ.obj (∏ᶜ X)) (n : ℕ) : Γ.map (Pi.π X n) (Γ.map d a) =
      Γ.map (Pi.π X n) a -
        Γ.map (G.map (homOfLE (Nat.le_succ n)).op) (Γ.map (Pi.π X (n + 1)) a) := by
    rw [← ConcreteCategory.comp_apply, ← Γ.map_comp, Stacks.InverseSystem.milnorDifference_π,
      Functor.map_sub, Functor.map_comp]
    rfl
  let e := Types.isLimitEquivSections hT
  have hπ (a : Γ.obj (∏ᶜ X)) (n : ℕ) : (e a).1 ⟨n⟩ = Γ.map (Pi.π X n) a := rfl
  let s : (Discrete.functor X ⋙ T).sections := ⟨fun j ↦ x j.as, fun {j k} f ↦ by
    obtain rfl : j = k := Discrete.ext (Discrete.eq_of_hom f)
    rw [Subsingleton.elim f (𝟙 j), CategoryTheory.Functor.map_id]
    rfl⟩
  have hx' (m : ℕ) : Γ.map (Pi.π X m) (e.symm s) = x m :=
    (hπ _ m).symm.trans (by rw [Equiv.apply_symm_apply])
  refine ⟨e.symm s, e.injective (Subtype.ext ?_)⟩
  funext ⟨n⟩
  refine (hπ _ n).trans ((key _ n).trans ?_)
  rw [hx', hx']
  exact (congrFun hx n).trans (hπ y n).symm

open Stacks.SheafOfModules.WeaklyContractible in
/-- **The limit of a surjective tower of complexes is its derived limit** (Stacks 0947). On a
ringed site with a covering collection of weakly contractible objects, if the transition maps of
a countable inverse system `F` of complexes of sheaves of modules are degreewise epimorphisms,
then the termwise limit `lim Fₙ` is a derived limit `R lim Fₙ` in `D(O)`, the images of the
limit projections being its projections. -/
theorem isDerivedLimitWithProjections_Q_limit_of_epi_f
    (S : WeaklyContractibleObjectsSituation.{w, v, u, t} C J)
    [HasDerivedCategory (SheafOfModules.{t} S.O)]
    (F : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{t} S.O) ℤ)
    (hF : ∀ (n : ℕ) (i : ℤ), Epi ((F.map (homOfLE (Nat.le_succ n)).op).f i)) :
    letI := hasExactLimitsOfShape_discrete_nat (R := S.O) S.B S.hasEnoughObjects
      S.isWeaklyContractible
    letI := Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
      (A := SheafOfModules.{t} S.O) (I := ℕ)
    NoetherianAdicCompletion.IsDerivedLimitWithProjections (F ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (limit F)) (fun n => DerivedCategory.Q.map (limit.π F ⟨n⟩)) := by
  let := hasExactLimitsOfShape_discrete_nat (R := S.O) S.B S.hasEnoughObjects
    S.isWeaklyContractible
  have : Epi (Stacks.InverseSystem.milnorDifference (fun n : ℕ ↦ F.obj ⟨n⟩)
      (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op)) :=
    HomologicalComplex.epi_milnorDifference_of_epi_eval (V := SheafOfModules.{t} S.O) F fun i =>
      epi_milnorDifference_of_epi_map_succ S
        (F ⋙ HomologicalComplex.eval (SheafOfModules.{t} S.O) (ComplexShape.up ℤ) i)
        fun n => hF n i
  exact DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi_milnorDifference F

end Stacks.WeaklyContractible

end
