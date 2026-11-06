module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceCoheratorLimit

/-!
# The canonical maps from the object `K` of Grothendieck existence to the levels

In Situation [Stacks, Tag 0CTC], let `K` be the object of [Stacks, Tag 0CTD], recorded as
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.DerivedLimitQCoh`: a derived limit
`L = R lim (iₙ,* ℱₙ)` in `D(𝒪_X)` and a map `ε : K ⟶ L` universal among maps from objects with
quasi-coherent cohomology sheaves. A derived-limit cone `p : L ⟶ ∏ iₙ,* ℱₙ`, that is a map whose
difference triangle is distinguished, provides maps `L ⟶ iₙ,* ℱₙ`, and composing with `ε` gives the
canonical maps `K ⟶ iₙ,* ℱₙ` the source refers to in the proof of [Stacks, Tag 0CTH]. This file
records them, their compatibility with the transition maps of the system, and the induced maps
`H⁰(K) ⟶ iₙ,* ℱₙ` of quasi-coherent sheaves.

## Main definitions

* `ExistenceSituation.IsDerivedLimitCone`: `p` exhibits
  `L` as a derived limit of the system.
* `ExistenceSituation.levelMap`: the map `K ⟶ iₙ,* ℱₙ`.
* `ExistenceSituation.zerothLevelMap`: the induced map
  `H⁰(K) ⟶ iₙ,* ℱₙ`.

## Main results

* `...levelMap_comp_map`: the maps `K ⟶ iₙ,* ℱₙ` are compatible with the transition maps.
* `...zerothLevelMap_comp_pushforwardTransition`: so are the maps `H⁰(K) ⟶ iₙ,* ℱₙ`.

## Implementation notes

Everything here is stated at a free `HasDerivedCategory` binder.

## References

* [Stacks Project, Tag 0CTH](https://stacks.math.columbia.edu/tag/0CTH)
* [Stacks Project, Tag 0CTD](https://stacks.math.columbia.edu/tag/0CTD)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe w u

namespace AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

variable (S : ExistenceSituation.{u}) [HasDerivedCategory.{w} S.X.left.Modules]

/-- `p : L ⟶ ∏ iₙ,* ℱₙ` exhibits `L` as a derived limit of the system `(iₙ,* ℱₙ)`: its difference
triangle is distinguished. This is the body of `CategoryTheory.Pretriangulated.IsDerivedLimit`
with the map `p` fixed. -/
def IsDerivedLimitCone {L : DerivedCategory S.X.left.Modules}
    (p : L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) : Prop :=
  ∃ δ, Triangle.mk p (Pi.lift fun n : ℕ =>
      Pi.π (fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n + 1) ≫
          S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op) δ ∈
    distTriang (DerivedCategory S.X.left.Modules)

/-- Every derived limit has a derived-limit cone. -/
theorem DerivedLimitQCoh.exists_isDerivedLimitCone (d : S.DerivedLimitQCoh) :
    ∃ p, S.IsDerivedLimitCone (L := d.L) p := by
  obtain ⟨p, δ, h⟩ := d.isDerivedLimit
  exact ⟨p, δ, h⟩

/-- The canonical map `K ⟶ iₙ,* ℱₙ`: the universal map `ε : K ⟶ L` followed by the `n`-th
projection of the derived-limit cone `p`. -/
def levelMap (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n : ℕ) :
    d.K ⟶ S.derivedPushforwardSystemOfModel.obj ⟨n⟩ :=
  d.ε ≫ p ≫ Pi.π _ n

/-- The canonical maps `K ⟶ iₙ,* ℱₙ` are compatible with the transition maps of the system,
because the first two maps of a distinguished triangle compose to zero. -/
theorem levelMap_comp_map (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : S.IsDerivedLimitCone p) (n : ℕ) :
    S.levelMap d p (n + 1) ≫ S.derivedPushforwardSystemOfModel.map (homOfLE (Nat.le_succ n)).op =
      S.levelMap d p n := by
  obtain ⟨δ, h⟩ := hp
  have h0 := comp_distTriang_mor_zero₁₂ _ h
  have h1 := congrArg (fun g => g ≫ Pi.π _ n) h0
  simp only [Triangle.mk_obj₁, Triangle.mk_mor₁, Triangle.mk_mor₂, Category.assoc,
    Pi.lift_comp_π, Preadditive.comp_sub, zero_comp] at h1
  simp only [levelMap, Category.assoc]
  rw [sub_eq_zero] at h1
  rw [h1]

/-- The canonical map `H⁰(K) ⟶ iₙ,* ℱₙ` of sheaves of modules, induced on zeroth cohomology by
`AlgebraicGeometry.GrothendieckExistence.ExistenceSituation.levelMap`. -/
def zerothLevelMap (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩) (n : ℕ) :
    (DerivedCategory.homologyFunctor S.X.left.Modules 0).obj d.K ⟶
      S.pushforwardSystem.obj (op n) :=
  (DerivedCategory.homologyFunctor S.X.left.Modules 0).map (S.levelMap d p n) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso S.X.left.Modules 0).hom.app _

/-- The canonical maps `H⁰(K) ⟶ iₙ,* ℱₙ` are compatible with the transition maps of the system
`(iₙ,* ℱₙ)`. -/
theorem zerothLevelMap_comp_pushforwardTransition (d : S.DerivedLimitQCoh)
    (p : d.L ⟶ ∏ᶜ fun n : ℕ => S.derivedPushforwardSystemOfModel.obj ⟨n⟩)
    (hp : S.IsDerivedLimitCone p) (n : ℕ) :
    S.zerothLevelMap d p (n + 1) ≫ S.pushforwardTransition n = S.zerothLevelMap d p n := by
  have hnat := (DerivedCategory.singleFunctorCompHomologyFunctorIso S.X.left.Modules
      0).hom.naturality
    (S.pushforwardTransition n)
  simp only [Functor.comp_map, Functor.id_map] at hnat
  have h2 : S.levelMap d p (n + 1) ≫
      (DerivedCategory.singleFunctor S.X.left.Modules 0).map (S.pushforwardTransition n) =
      S.levelMap d p n := by
    have := S.levelMap_comp_map d p hp n
    simp only [derivedPushforwardSystemOfModel, Functor.comp_map, pushforwardSystem_map_succ]
      at this
    exact this
  unfold zerothLevelMap
  exact (Category.assoc _ _ _).trans ((congrArg _ hnat.symm).trans
    ((Functor.map_comp_assoc _ _ _ _).symm.trans
      (congrArg (fun g => (DerivedCategory.homologyFunctor S.X.left.Modules 0).map g ≫ _) h2)))

end AlgebraicGeometry.GrothendieckExistence.ExistenceSituation

end
