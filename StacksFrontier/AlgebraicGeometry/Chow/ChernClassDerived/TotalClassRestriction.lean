module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBase
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ChernFamily

/-!
# Restriction of total Chow cohomology classes

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project and let
`h : Y' ⟶ Y` be locally of finite type. The restriction maps `res : A^p(Y) ⟶ A^p(Y')` of
[Stacks, Tag 0B7F] assemble, degree by degree, into a map

  `res : ∏_{p ≥ 0} A^p(Y) ⟶ ∏_{p ≥ 0} A^p(Y')`

of total Chow cohomology classes (`Stacks.Chow.TotalChowClass`). On a test scheme
`g : T ⟶ Y'` the restriction of `c` operates as `c` does on `g ≫ h`
(`Stacks.Chow.TotalChowClass.op_res`), by the cap formula of [Stacks, Tag 0F9Z]. Since a total
class is determined by its operations and the ring operations are computed on the operations,
the restriction is a ring homomorphism, it is functorial, and it carries the total Chern class
`c(ℰ)` of a finite locally free module to `c(h^*ℰ)`.

The structure morphism of `Y'` is an argument of the restriction, presented by an equality
`h ≫ sY = sY'`: the composite of two restrictions is then literally a restriction, with no
transport between the rings of total classes for the equal structure morphisms
`h' ≫ (h ≫ sY)` and `(h' ≫ h) ≫ sY`.

## Main definitions

* `Stacks.Chow.TotalChowClass.res` — the restriction of total classes along `h : Y' ⟶ Y`, as a
  ring homomorphism.

## Main results

* `Stacks.Chow.BivariantClass.idRule_chowCohomologyRestriction_heq` — the operation of the
  restriction of `c ∈ A^p(Y)` on `g : T ⟶ Y'` is the operation of `c` on `g ≫ h`.
* `Stacks.Chow.TotalChowClass.op_res` — the same for total classes.
* `Stacks.Chow.TotalChowClass.res_id`, `Stacks.Chow.TotalChowClass.res_res` — functoriality.
* `Stacks.Chow.op_totalChern` — the total Chern class `c(ℰ)` operates on `g : T ⟶ Y` as the total
  Chern class `c(g^*ℰ)` in the ring of graded cap families.
* `Stacks.Chow.TotalChowClass.res_totalChern` — `res_h c(ℰ) = c(h^*ℰ)`.

## References

* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Heq

variable (C : ChowSituation.{u}) {T : Scheme.{u}}

/-- Two graded cap families on the Chow groups of `T` for equal structure morphisms are
heterogeneously equal as soon as they take heterogeneously equal arguments to heterogeneously
equal values. -/
theorem gradedCapFamily_heq_of_heq {s s' : T ⟶ C.S} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s'] (hs : s = s') {F : GradedCapFamily (fun k ↦ chowGroup C s k)}
    {F' : GradedCapFamily (fun k ↦ chowGroup C s' k)}
    (h : ∀ (k : ℤ) (p : ℕ) (α : chowGroup C s k) (α' : chowGroup C s' k), α ≍ α' →
      F k p α ≍ F' k p α') : F ≍ F' := by
  subst hs
  exact heq_of_eq (funext fun k ↦ funext fun p ↦
    AddMonoidHom.ext fun α ↦ eq_of_heq (h k p α α HEq.rfl))

/-- Products of heterogeneously equal graded cap families over equal structure morphisms are
heterogeneously equal. -/
theorem gradedCapFamily_mul_heq {s s' : T ⟶ C.S} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s'] (hs : s = s') {F G : GradedCapFamily (fun k ↦ chowGroup C s k)}
    {F' G' : GradedCapFamily (fun k ↦ chowGroup C s' k)} (hF : F ≍ F') (hG : G ≍ G') :
    F * G ≍ F' * G' := by
  subst hs
  cases hF
  cases hG
  rfl

/-- The units of the rings of graded cap families over equal structure morphisms are
heterogeneously equal. -/
theorem gradedCapFamily_one_heq {s s' : T ⟶ C.S} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s'] (hs : s = s') :
    (1 : GradedCapFamily (fun k ↦ chowGroup C s k)) ≍
      (1 : GradedCapFamily (fun k ↦ chowGroup C s' k)) := by
  subst hs
  rfl

end Heq

section Restriction

variable {C : ChowSituation.{u}} {Y Y' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- **The operation of a restricted Chow cohomology class.** For `c ∈ A^p(Y)` and
`h : Y' ⟶ Y`, the operation of the restriction `res(c) ∈ A^p(Y')` of Stacks 0B7F on a test
scheme `g : T ⟶ Y'` is the operation of `c` on `g ≫ h`, the two Chow groups of `T` being those
of the equal structure morphisms `g ≫ (h ≫ sY)` and `(g ≫ h) ≫ sY`. -/
theorem BivariantClass.idRule_chowCohomologyRestriction_heq {p : ℤ} (h : Y' ⟶ Y)
    [LocallyOfFiniteType h] (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sY p)
    {T : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ (h ≫ sY)) k) (β : chowGroup C ((g ≫ h) ≫ sY) k) (hαβ : α ≍ β) :
    (chowCohomologyRestriction C (gysinSystemOfInvertible C) sY h p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c).idRule C (h ≫ sY)
        (gysinSystemOfInvertible C) g k α ≍
      c.idRule C sY (gysinSystemOfInvertible C) (g ≫ h) k β := by
  have key := chowCohomologyRestriction_cap C (gysinSystemOfInvertible C) sY h p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c g k α
  have hβ : chowGroupCongr C (Category.assoc g h sY).symm k α = β :=
    eq_of_heq ((chowGroupCongr_heq C _ k α).trans hαβ)
  rw [hβ] at key
  refine (heq_of_eq key).trans ?_
  exact chowPushforwardOfIso_heq _ _ _ rfl (Category.assoc g h sY).symm rfl HEq.rfl

end Restriction

namespace TotalChowClass

variable {C : ChowSituation.{u}} {Y Y' Y'' : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY'] {sY'' : Y'' ⟶ C.S} [LocallyOfFiniteType sY'']

/-- The operations of a total class on equal test morphisms are heterogeneously equal. -/
theorem op_heq_congr (c : TotalChowClass C sY) {T : Scheme.{u}} {g g' : T ⟶ Y}
    [LocallyOfFiniteType g] [LocallyOfFiniteType g'] (hg : g = g') : c.op g ≍ c.op g' := by
  subst hg
  rfl

/-- The restriction of total classes along `h : Y' ⟶ Y`, as an additive map: the restriction
map of Stacks 0B7F in every degree. The structure morphism of `Y'` is an argument presented by
an equality with `h ≫ sY`, so that restrictions compose without transport. -/
def resHom (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') :
    TotalChowClass C sY →+ TotalChowClass C sY' := by
  subst hs
  exact AddMonoidHom.pi fun p ↦
    (chowCohomologyRestriction C (gysinSystemOfInvertible C) sY h (p : ℤ)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)).comp
      (Pi.evalAddMonoidHom _ p)

/-- **The operation of a restricted class.** On a test scheme `g : T ⟶ Y'` the operation of the
restriction of `c` along `h` is the operation of `c` on `g ≫ h`, read through the equality of
structure morphisms `g ≫ sY' = (g ≫ h) ≫ sY`. -/
theorem op_resHom_apply_heq (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g] (k : ℤ)
    (p : ℕ) (α : chowGroup C (g ≫ sY') k) (β : chowGroup C ((g ≫ h) ≫ sY) k) (hαβ : α ≍ β) :
    (resHom h hs c).op g k p α ≍ c.op (g ≫ h) k p β := by
  subst hs
  exact BivariantClass.idRule_chowCohomologyRestriction_heq h (c p) g k α β hαβ

/-- **The operation of a restricted class**, as a graded cap family: on a test scheme
`g : T ⟶ Y'` the restriction of `c` along `h` operates as `c` does on `g ≫ h`. -/
theorem op_resHom_heq (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g] :
    (resHom h hs c).op g ≍ c.op (g ≫ h) :=
  gradedCapFamily_heq_of_heq C (by rw [← hs, Category.assoc])
    fun k p α β hαβ ↦ op_resHom_apply_heq h hs c g k p α β hαβ

/-- **The restriction of total classes** along `h : Y' ⟶ Y`, Stacks 0B7F in every degree, as a
homomorphism of rings. The structure morphism of `Y'` is an argument presented by an equality
with `h ≫ sY`. -/
def res (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') :
    TotalChowClass C sY →+* TotalChowClass C sY' where
  toFun := resHom h hs
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := ext_op fun g _ ↦ eq_of_heq <| (op_resHom_heq h hs 1 g).trans <| by
    rw [op_one, op_one]
    exact gradedCapFamily_one_heq C (by rw [← hs, Category.assoc])
  map_mul' c d := ext_op fun g _ ↦ eq_of_heq <| (op_resHom_heq h hs (c * d) g).trans <| by
    rw [op_mul, op_mul]
    exact gradedCapFamily_mul_heq C (by rw [← hs, Category.assoc])
      (op_resHom_heq h hs c g).symm (op_resHom_heq h hs d g).symm

/-- The ring homomorphism `Stacks.Chow.TotalChowClass.res` is the additive restriction map. -/
theorem res_apply (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (c : TotalChowClass C sY) : res h hs c = resHom h hs c :=
  rfl

/-- **The operation of a restricted class**: on a test scheme `g : T ⟶ Y'` the restriction of
`c` along `h` operates as `c` does on `g ≫ h`, the two graded cap families living on the Chow
groups of `T` for the equal structure morphisms `g ≫ sY'` and `(g ≫ h) ≫ sY`. -/
theorem op_res (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g] :
    (res h hs c).op g ≍ c.op (g ≫ h) :=
  op_resHom_heq h hs c g

/-- The components of the operation of a restricted class, on heterogeneously equal arguments. -/
theorem op_res_apply (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY')
    (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g] (k : ℤ)
    (p : ℕ) (α : chowGroup C (g ≫ sY') k) (β : chowGroup C ((g ≫ h) ≫ sY) k) (hαβ : α ≍ β) :
    (res h hs c).op g k p α ≍ c.op (g ≫ h) k p β :=
  op_resHom_apply_heq h hs c g k p α β hαβ

/-- **Restriction along the identity is the identity.** -/
theorem res_id (c : TotalChowClass C sY) : res (𝟙 Y) (Category.id_comp sY) c = c :=
  ext_op fun g _ ↦ eq_of_heq <| (op_res _ _ c g).trans (op_heq_congr c (Category.comp_id g))

/-- **Restriction is functorial**: restricting along `h` and then along `h'` is restricting along
`h' ≫ h`. -/
theorem res_res (h : Y' ⟶ Y) [LocallyOfFiniteType h] (hs : h ≫ sY = sY') (h' : Y'' ⟶ Y')
    [LocallyOfFiniteType h'] (hs' : h' ≫ sY' = sY'') (c : TotalChowClass C sY) :
    res h' hs' (res h hs c) = res (h' ≫ h) (by rw [Category.assoc, hs, hs']) c :=
  ext_op fun g _ ↦ eq_of_heq <| ((op_res h' hs' _ g).trans (op_res h hs c (g ≫ h'))).trans
    ((op_heq_congr c (Category.assoc g h' h)).trans (op_res (h' ≫ h) _ c g).symm)

/-- Restricting along two equal morphisms gives the same class. -/
theorem res_congr {h h' : Y' ⟶ Y} [LocallyOfFiniteType h] [LocallyOfFiniteType h'] (e : h = h')
    (hs : h ≫ sY = sY') (hs' : h' ≫ sY = sY') (c : TotalChowClass C sY) :
    res h hs c = res h' hs' c := by
  subst e
  rfl

end TotalChowClass

/-! ### The operation and the restriction of the total Chern class -/

section TotalChern

variable (C : ChowSituation.{u}) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']

/-- Total Chern classes of isomorphic modules of equal ranks, over equal structure morphisms,
are heterogeneously equal graded cap families. -/
theorem GenuineChern.chernFamily_heq {T : Scheme.{u}} {q q' : T ⟶ C.S} [LocallyOfFiniteType q]
    [LocallyOfFiniteType q'] (hq : q = q') {F F' : T.Modules} {r r' : ℕ}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r']
    (e : F ≅ F') (hr : r = r') :
    GenuineChern.chernFamily C q F r ≍ GenuineChern.chernFamily C q' F' r' := by
  subst hq
  exact heq_of_eq (GenuineChern.chernFamily_congr C q F' r' e hr)

variable (F : Y.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]

/-- **The operation of the total Chern class**, as a graded cap family: on a test scheme
`g : T ⟶ Y`, the total class `c(ℰ)` operates as the total Chern class `c(g^*ℰ)` of the pulled
back module in the ring of graded cap families. -/
theorem op_totalChern {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] :
    letI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
    (totalChern C sY F r).op g =
      GenuineChern.chernFamily C (g ≫ sY) ((Scheme.Modules.pullback g).obj F) r := by
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  funext k j
  refine AddMonoidHom.ext fun α ↦ ?_
  by_cases hj : j ≤ r
  · rw [GenuineChern.chernFamily, chernCapFamilyOnChow_of_le _ _ _ _ _ _ hj]
    exact op_totalChern_apply C sY F r g k ⟨j, Nat.lt_succ_of_le hj⟩ α
  · rw [GenuineChern.chernFamily, chernCapFamilyOnChow_of_gt _ _ _ _ _ _ hj,
      op_totalChern_of_lt C sY F r g k (by omega)]

/-- **Restriction of the total Chern class**: for `h : Y' ⟶ Y` the restriction of `c(ℰ)` is
`c(h^*ℰ)`. -/
theorem TotalChowClass.res_totalChern (h : Y' ⟶ Y) [LocallyOfFiniteType h]
    (hs : h ≫ sY = sY') :
    letI := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r h
    TotalChowClass.res h hs (totalChern C sY F r) =
      totalChern C sY' ((Scheme.Modules.pullback h).obj F) r := by
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r h
  refine TotalChowClass.ext_op fun g _ ↦ eq_of_heq ?_
  refine (TotalChowClass.op_res h hs _ g).trans ?_
  rw [op_totalChern, op_totalChern]
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r (g ≫ h)
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank ((Scheme.Modules.pullback h).obj F)
    r g
  exact GenuineChern.chernFamily_heq C (by rw [← hs, Category.assoc])
    ((Scheme.Modules.pullbackComp g h).app F).symm rfl

end TotalChern

end Stacks.Chow

end
