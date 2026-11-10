module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechCompatibility.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Logic.Small.Set

/-!
# A level of a Čech nerve is a base change of the morphism

Let `f : X ⟶ Y` be a morphism of schemes and let `cechScheme f n = X ×_Y ⋯ ×_Y X` be the
degree-`n` term of its Čech nerve, the wide pullback of `n + 1` copies of `f`, with structure
map `cechProjection f n : cechScheme f n ⟶ Y`.

Forgetting the last of the `n + 2` factors of `cechScheme f (n + 1)` is the Čech face map
`cechFaceProjection f n (Fin.last (n + 1))`, here named `cechLastFace f n`, and the forgotten
factor is the last leg `cechLastLeg f n : cechScheme f (n + 1) ⟶ X` of the wide pullback. The
first result of this file is that the resulting square is cartesian:
`cechScheme f (n + 1) = cechScheme f n ×_Y X`, the base change of `f` along
`cechProjection f n`. Since the structure map of level `n + 1` is the composite of
`cechLastFace f n` with the structure map of level `n`, this is a recursion carrying any
property of `f` stable under base change and composition up the whole Čech nerve; it is applied
here to finiteness and to surjectivity.

The point of the recursion is Stacks 09Z2, cohomological descent along a finite surjection: the
descent argument needs the finite base change theorem at every Čech level. The repository's
abelian finite base change theorem,
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite`, is stated for four objects of
one given big étale site, so the last two results of this file discharge that hypothesis — a
single big étale site holds `X`, `Y` and every `cechScheme f n`, because that is a set of
schemes indexed by `ℕ` plus two points and hence small — and conclude that the base change
comparison at each Čech level is an isomorphism, with no site appearing in the statement.

## Main definitions

* `Stacks.EtaleCohomology.cechLastFace` — the Čech face map `cechScheme f (n + 1) ⟶
  cechScheme f n` forgetting the last factor.
* `Stacks.EtaleCohomology.cechLastLeg` — the forgotten factor,
  `cechScheme f (n + 1) ⟶ X`.

## Main results

* `Stacks.EtaleCohomology.isPullback_cechScheme_succ` — the square formed by `cechLastFace`,
  `cechLastLeg`, `cechProjection` and `f` is cartesian.
* `Stacks.EtaleCohomology.isFinite_cechProjection` — every level of the Čech nerve of a finite
  morphism is finite over the base.
* `Stacks.EtaleCohomology.surjective_cechProjection` — every level of the Čech nerve of a
  surjective morphism is surjective over the base.
* `Stacks.EtaleCohomology.exists_bigEtaleSite_contains_cechScheme` — one big étale site holds
  the base and every level of the Čech nerve.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_cechScheme_succ` — the abelian base
  change comparison at a Čech level of a finite morphism is an isomorphism.

## References

* [Stacks Project, Tag 09Z2](https://stacks.math.columbia.edu/tag/09Z2)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)

/-- The last face projection of the Čech nerve of `f`: the map `cechScheme f (n + 1) ⟶
cechScheme f n` which forgets the final factor of the fibre product. -/
abbrev cechLastFace : cechScheme f (n + 1) ⟶ cechScheme f n :=
  cechFaceProjection f n (Fin.last (n + 1))

/-- The factor of `cechScheme f (n + 1)` forgotten by `Stacks.EtaleCohomology.cechLastFace`:
the final leg `cechScheme f (n + 1) ⟶ X` of the wide pullback. -/
abbrev cechLastLeg : cechScheme f (n + 1) ⟶ X :=
  WidePullback.π (fun _ : Fin (n + 1 + 1) => f) (Fin.last (n + 1))

/-- Following the last face projection by the `j`-th leg of `cechScheme f n` is the leg of
`cechScheme f (n + 1)` indexed by `j.castSucc`. -/
theorem cechLastFace_comp_π (j : Fin (n + 1)) :
    cechLastFace f n ≫ WidePullback.π (fun _ : Fin (n + 1) => f) j
      = WidePullback.π (fun _ : Fin (n + 1 + 1) => f) j.castSucc := by
  have : (Arrow.mk f).HasCechPullbacks := ⟨fun _ => inferInstance⟩
  have h := Arrow.cechNerve_map_π (Arrow.mk f) (SimplexCategory.δ (Fin.last (n + 1))).op j
  simp [SimplexCategory.δ]

/-- The structure map of a level of the Čech nerve is the base map of the wide pullback of the
`n + 1` copies of `f`. -/
theorem cechProjection_eq_base :
    cechProjection f n = WidePullback.base (fun _ : Fin (n + 1) => f) :=
  rfl

/-- The last face projection lies over the base: it is a morphism of `Y`-schemes. -/
theorem cechLastFace_comp_cechProjection :
    cechLastFace f n ≫ cechProjection f n = cechProjection f (n + 1) :=
  cechFaceProjection_comp f n (Fin.last (n + 1))

/-- The forgotten leg lies over the base: composing it with `f` is the structure map of
`cechScheme f (n + 1)`. -/
theorem cechLastLeg_comp :
    cechLastLeg f n ≫ f = cechProjection f (n + 1) :=
  WidePullback.π_arrow (fun _ : Fin (n + 1 + 1) => f) (Fin.last (n + 1))

/-- **One level of a Čech nerve is the base change of `f` along the previous level.** The square

```
cechScheme f (n+1) --cechLastLeg--> X
  |cechLastFace                     |f
  v                                 v
cechScheme f n  --cechProjection--> Y
```

is cartesian, i.e. `cechScheme f (n + 1) = cechScheme f n ×_Y X`. This is the recursion that
makes every level of the Čech nerve of `f` inherit the properties of `f` that are stable under
base change and composition. -/
theorem isPullback_cechScheme_succ :
    IsPullback (cechLastFace f n) (cechLastLeg f n) (cechProjection f n) f := by
  have hw : cechLastFace f n ≫ cechProjection f n = cechLastLeg f n ≫ f := by
    rw [cechLastFace_comp_cechProjection, cechLastLeg_comp]
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => WidePullback.lift (arrows := fun _ : Fin (n + 1 + 1) => f)
      (s.fst ≫ cechProjection f n)
      (Fin.lastCases s.snd (fun j => s.fst ≫ WidePullback.π (fun _ : Fin (n + 1) => f) j))
      ?_) ?_ ?_ ?_)
  · refine Fin.lastCases ?_ ?_
    · simpa using s.condition.symm
    · intro j
      rw [Fin.lastCases_castSucc, Category.assoc, WidePullback.π_arrow]
      exact congrArg (s.fst ≫ ·) (cechProjection_eq_base f n).symm
  · intro s
    refine WidePullback.hom_ext_of_π (arrows := fun _ : Fin (n + 1) => f) _ _ fun j => ?_
    rw [Category.assoc, cechLastFace_comp_π, WidePullback.lift_π, Fin.lastCases_castSucc]
  · intro s
    simp only [cechLastLeg, WidePullback.lift_π, Fin.lastCases_last]
  · intro s m hfst hsnd
    refine WidePullback.hom_ext_of_π (arrows := fun _ : Fin (n + 1 + 1) => f) _ _ fun j => ?_
    rw [WidePullback.lift_π]
    induction j using Fin.lastCases with
    | last => rw [Fin.lastCases_last]; exact hsnd
    | cast j => rw [Fin.lastCases_castSucc, ← hfst, Category.assoc, cechLastFace_comp_π]

/-- **The degree-zero level of the Čech nerve of `f` is `X` itself.** Its single leg, the wide
pullback projection indexed by `0 : Fin 1`, is an isomorphism. -/
instance isIso_cechLeg_zero : IsIso (WidePullback.π (fun _ : Fin 1 => f) 0) := by
  refine ⟨⟨WidePullback.lift f (fun _ => 𝟙 X) (fun _ => by simp), ?_, ?_⟩⟩
  · refine WidePullback.hom_ext_of_π (arrows := fun _ : Fin 1 => f) _ _ fun j => ?_
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
  · rw [WidePullback.lift_π]

/-- The single leg of the degree-zero level of the Čech nerve of `f`, followed by `f`, is the
structure map of that level. -/
theorem cechLeg_zero_comp :
    WidePullback.π (fun _ : Fin 1 => f) 0 ≫ f = cechProjection f 0 :=
  WidePullback.π_arrow (fun _ : Fin 1 => f) 0

/-- **Every level of the Čech nerve of a finite morphism is finite over the base.** By induction
on `n`: level `0` is `X` itself, and `Stacks.EtaleCohomology.isPullback_cechScheme_succ` exhibits
the structure map of level `n + 1` as the composite of a base change of `f` with the structure
map of level `n`, both of which are finite. -/
instance isFinite_cechProjection [IsFinite f] : IsFinite (cechProjection f n) := by
  induction n with
  | zero =>
    rw [← cechLeg_zero_comp f]
    infer_instance
  | succ n ih =>
    have hbc : IsFinite (cechLastFace f n) :=
      MorphismProperty.of_isPullback (P := @IsFinite)
        (isPullback_cechScheme_succ f n).flip ‹IsFinite f›
    rw [← cechLastFace_comp_cechProjection f n]
    infer_instance

/-- **Every level of the Čech nerve of a surjective morphism is surjective over the base.** The
induction is the one of `Stacks.EtaleCohomology.isFinite_cechProjection`: surjectivity of
morphisms of schemes is stable under base change and under composition. No finiteness of `f` is
needed. -/
instance surjective_cechProjection [Surjective f] : Surjective (cechProjection f n) := by
  induction n with
  | zero =>
    rw [← cechLeg_zero_comp f]
    infer_instance
  | succ n ih =>
    have hbc : Surjective (cechLastFace f n) :=
      MorphismProperty.of_isPullback (P := @Surjective)
        (isPullback_cechScheme_succ f n).flip ‹Surjective f›
    rw [← cechLastFace_comp_cechProjection f n]
    infer_instance

/-- **A single big étale site contains `X`, `Y` and every level of the Čech nerve of `f`.** The
schemes involved form the set `{X, Y} ∪ Set.range (cechScheme f)`, indexed by two points together
with `ℕ`, hence `Small.{u}`; so
`AlgebraicGeometry.BigEtaleSite.exists_contains_of_small` applies. -/
theorem exists_bigEtaleSite_contains_cechScheme_and_source :
    ∃ B : BigEtaleSite.{u}, B.Contains X ∧ B.Contains Y ∧ ∀ n, B.Contains (cechScheme f n) := by
  obtain ⟨B, hB⟩ :=
    BigEtaleSite.exists_contains_of_small (insert X (insert Y (Set.range (cechScheme f))))
  exact ⟨B, hB _ (Set.mem_insert _ _),
    hB _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)),
    fun n => hB _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨n, rfl⟩))⟩

/-- **A big étale site containing the base of `f` and every level of its Čech nerve.** -/
theorem exists_bigEtaleSite_contains_cechScheme :
    ∃ B : BigEtaleSite.{u}, B.Contains Y ∧ ∀ n, B.Contains (cechScheme f n) :=
  have ⟨B, _, hY, hlevel⟩ := exists_bigEtaleSite_contains_cechScheme_and_source f
  ⟨B, hY, hlevel⟩

/-- **Stacks 0959 at a Čech level.** For `f : X ⟶ Y` finite, the underived base change
comparison `(cechProjection f n)^{-1} f_* ⟶ (cechLastFace f n)_* (cechLastLeg f n)^{-1}` of
abelian sheaves on the small étale sites is an isomorphism.

This combines the cartesian square `Stacks.EtaleCohomology.isPullback_cechScheme_succ` with
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite`; the hypothesis of the latter
that the four corners of the square be objects of one big étale site is discharged by
`Stacks.EtaleCohomology.exists_bigEtaleSite_contains_cechScheme_and_source`, which is why no
site appears in the statement. -/
theorem isIso_etaleAbelianBaseChange_cechScheme_succ [IsFinite f] :
    IsIso (etaleAbelianBaseChange.{u, 0} f (cechProjection f n) (cechLastLeg f n)
      (cechLastFace f n) (isPullback_cechScheme_succ f n).flip.w) := by
  obtain ⟨B, hX, hY, hlevel⟩ := exists_bigEtaleSite_contains_cechScheme_and_source f
  have : IsFinite
      (B.inclusion.map (ObjectProperty.homMk (X := B.obj X hX) (Y := B.obj Y hY) f)) :=
    ‹IsFinite f›
  exact isIso_etaleAbelianBaseChange_of_isFinite B
    (ObjectProperty.homMk (X := B.obj X hX) (Y := B.obj Y hY) f)
    (ObjectProperty.homMk (X := B.obj (cechScheme f n) (hlevel n)) (Y := B.obj Y hY)
      (cechProjection f n))
    (ObjectProperty.homMk (X := B.obj (cechScheme f (n + 1)) (hlevel (n + 1)))
      (Y := B.obj X hX) (cechLastLeg f n))
    (ObjectProperty.homMk (X := B.obj (cechScheme f (n + 1)) (hlevel (n + 1)))
      (Y := B.obj (cechScheme f n) (hlevel n)) (cechLastFace f n))
    (isPullback_cechScheme_succ f n).flip

/-- The direct image appearing in
`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_cechScheme_succ` is the direct image
`Stacks.EtaleCohomology.smallEtalePushforwardAb` of the higher base-change development: both
are restriction of sheaves along `Stacks.EtaleCohomology.smallEtaleBaseChange f`, so they are
the same functor and not merely isomorphic ones. -/
theorem etaleAbelianDirectImage_eq_smallEtalePushforwardAb :
    etaleAbelianDirectImage.{u, 0} f = smallEtalePushforwardAb f :=
  rfl

end Stacks.EtaleCohomology

end
