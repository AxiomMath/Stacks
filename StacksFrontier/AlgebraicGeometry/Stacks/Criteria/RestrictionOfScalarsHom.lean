module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalars

/-!
# Morphisms into a restriction of scalars

Let `S` be a scheme contained in a big fppf site `B`, let `x : X ⟶ Z` and `z : Z ⟶ Q` be
morphisms of algebraic spaces over `S`, and let `Res_{Z/Q}(X)` be the restriction of scalars of
Stacks 05YA. This file identifies the morphisms into `Res_{Z/Q}(X)` from an algebraic space `T`
with the pairs `(a, b)` of Stacks 05Y9 at `T`:

```text
Hom(T, Res_{Z/Q}(X)) ≃ {(a, b) | a : T ⟶ Q, b : T ×_{a, Q} Z ⟶ X over Z}.
```

This is part (2) of Stacks 05YB, the half that describes the functor of points of the
restriction of scalars. Part (1), that the presheaf is an fppf sheaf, is
`AlgebraicGeometry.Space.isSheaf_restrictionOfScalars`; with it the bijection below is one of
morphisms of fppf sheaves, as the source states it, the category of sheaves being a full
subcategory of presheaves.

## Main definitions

* `AlgebraicGeometry.Space.restrictionOfScalarsHomEquiv`: **Stacks 05YB**, the bijection above,
  together with its two characterizing properties — compatibility with the identification of
  Stacks 05YA at every scheme-valued point of `T`, and naturality in `T`.
* `AlgebraicGeometry.Space.homOfRestrictionPair`: the morphism attached to a pair, which is the
  inverse of that bijection.
* `AlgebraicGeometry.Space.restrictionOfScalarsMap`: the morphism
  `Res_{Z/Q}(X') ⟶ Res_{Z/Q}(X)` induced by a morphism `X' ⟶ X` over `Z`, characterized on
  pairs by `AlgebraicGeometry.Space.RestrictionPair.postcomp`.

## Main results

* `AlgebraicGeometry.Space.RestrictionPair.restrict_postcomp`: postcomposing the second
  component of a pair commutes with base change of the pair.
* `AlgebraicGeometry.Space.exists_hom_of_yoneda`: a compatible assignment of a morphism
  `yoneda.obj U ⟶ G` to every morphism `yoneda.obj U ⟶ F` comes from a morphism `F ⟶ G`. This
  is the existence statement dual to `CategoryTheory.hom_ext_yoneda`.
* `AlgebraicGeometry.Space.restrictionPair_ext_of_points`: two pairs over `T` with a common base
  change at every scheme-valued point of `T` are equal.

## Implementation notes

A morphism `v : T ⟶ Res_{Z/Q}(X)` has an evident first component, `a = v ≫ p` with `p` the
projection of Stacks 05YA. Its second component is built one scheme-valued point at a time: a
point of `T ×_{a, Q} Z` is a point `i` of `T` together with a factorization of `i ≫ a` through
`z`, and the pair at `i` supplied by Stacks 05YA then evaluates on it
(`AlgebraicGeometry.Space.pointLift`). Those values are compatible, so
`AlgebraicGeometry.Space.exists_hom_of_yoneda` assembles them.

Injectivity is the same argument read backwards, and is
`AlgebraicGeometry.Space.restrictionPair_ext_of_points`. Both halves are stated through
`AlgebraicGeometry.Space.RestrictionPair.IsPullbackAlong` rather than through an equality of
pairs, for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/Criteria/RestrictionOfScalars.lean`: the comparison of
fibre products is available before the equality of base morphisms is.

Note that the composition of presheaves of types is associative on the nose, which is what lets
the comparison lemmas below be applied to goals whose two sides are bracketed differently.

## References

* [Stacks Project, Tag 05YB](https://stacks.math.columbia.edu/tag/05YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### A morphism of presheaves from its values on representables -/

/-- **A morphism of presheaves of types from compatible values on representables.** If to every
morphism `yoneda.obj U ⟶ F` there is assigned a morphism `yoneda.obj U ⟶ G`, compatibly with
precomposition by maps of representables, then the assignment is precomposition with a morphism
`F ⟶ G`.

This is the existence statement whose uniqueness counterpart is
`CategoryTheory.hom_ext_yoneda`. -/
theorem exists_hom_of_yoneda {C : Type*} [Category.{u} C] {F G : Cᵒᵖ ⥤ Type u}
    (a : ∀ U, (yoneda.obj U ⟶ F) → (yoneda.obj U ⟶ G))
    (ha : ∀ {U V} (f : V ⟶ U) (i : yoneda.obj U ⟶ F),
      a V (yoneda.map f ≫ i) = yoneda.map f ≫ a U i) :
    ∃ g : F ⟶ G, ∀ U (i : yoneda.obj U ⟶ F), i ≫ g = a U i := by
  refine ⟨{ app := fun U => ↾fun t => yonedaEquiv (a U.unop (yonedaEquiv.symm t))
            naturality := ?_ }, fun U i => ?_⟩
  · intro U V f
    ext t
    show yonedaEquiv (a V.unop (yonedaEquiv.symm (F.map f t))) =
      G.map f (yonedaEquiv (a U.unop (yonedaEquiv.symm t)))
    rw [yonedaEquiv_symm_map, ha, ← yonedaEquiv_naturality']
  · apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    show yonedaEquiv (a U (yonedaEquiv.symm (yonedaEquiv i))) = _
    rw [Equiv.symm_apply_apply]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The two projections of a point of a pullback satisfy the pullback condition. -/
private theorem comp_pullback_condition {C : Type*} [Category C] {P X Y W : C}
    {f : X ⟶ W} {g : Y ⟶ W} [HasPullback f g] (i : P ⟶ pullback f g) :
    (i ≫ pullback.fst f g) ≫ f = (i ≫ pullback.snd f g) ≫ g := by
  rw [Category.assoc, pullback.condition, Category.assoc]

/-! ### Base change and postcomposition -/

/-- **Being a base change is preserved by postcomposing the second components.** -/
theorem RestrictionPair.isPullbackAlong_postcomp {X' X Z Q : AlgebraicSpaces B S hS}
    {x' : X' ⟶ Z} {x : X ⟶ Z} (g : X' ⟶ X) (hg : g ≫ x = x') {z : Z ⟶ Q}
    {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : T' ⟶ T}
    {p : RestrictionPair B S hS x' z T} {p' : RestrictionPair B S hS x' z T'}
    (h : RestrictionPair.IsPullbackAlong f p p') :
    RestrictionPair.IsPullbackAlong f (RestrictionPair.postcomp g hg p)
      (RestrictionPair.postcomp g hg p') := by
  obtain ⟨hbase, q, hfst, hsnd, hlift⟩ := h
  refine ⟨hbase, q, hfst, hsnd, ?_⟩
  show p'.lift ≫ g.hom = q ≫ p.lift ≫ g.hom
  rw [hlift, Category.assoc]

/-- **Postcomposing the second component of a pair commutes with base change of the pair.** -/
theorem RestrictionPair.restrict_postcomp {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Z}
    {x : X ⟶ Z} (g : X' ⟶ X) (hg : g ≫ x = x') {z : Z ⟶ Q}
    {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : T' ⟶ T)
    (p : RestrictionPair B S hS x' z T) :
    RestrictionPair.restrict f (RestrictionPair.postcomp g hg p) =
      RestrictionPair.postcomp g hg (RestrictionPair.restrict f p) :=
  (RestrictionPair.eq_restrict_of_isPullbackAlong
    (RestrictionPair.isPullbackAlong_postcomp g hg
      (RestrictionPair.isPullbackAlong_restrict f p))).symm

/-! ### Pairs of a morphism, point by point -/

section Points

variable {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z) (z : Z ⟶ Q)
  {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The first component of the pair at a scheme-valued point `i` of `T` attached to a morphism
`v : T ⟶ Res_{Z/Q}(X)` is `i` composed with the projection of `v`. -/
theorem base_pairEquiv_yonedaEquiv_comp
    (v : T ⟶ (restrictionOfScalars B S hS x z).presheaf)
    (U : BigFppfOver B S hS) (i : yoneda.obj U ⟶ T) :
    ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv (i ≫ v))).base =
      i ≫ v ≫ (restrictionOfScalars B S hS x z).projection := by
  apply yonedaEquiv.injective
  rw [← (restrictionOfScalars B S hS x z).projection_pairEquiv U (yonedaEquiv (i ≫ v)),
    ← yonedaEquiv_comp, Category.assoc]

/-- **Evaluating the second components of two pairs related by a base change.** If `p'` is the
base change of `p` along `f` and two points of the two fibre products agree on both
projections, then they agree after evaluating the second components. -/
theorem lift_eq_of_isPullbackAlong {T' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : T' ⟶ T}
    {p : RestrictionPair B S hS x z T} {p' : RestrictionPair B S hS x z T'}
    (h : RestrictionPair.IsPullbackAlong f p p')
    (l : Y ⟶ pullback p.base z.hom) (l' : Y ⟶ pullback p'.base z.hom)
    (hf : l' ≫ pullback.fst p'.base z.hom ≫ f = l ≫ pullback.fst p.base z.hom)
    (hs : l' ≫ pullback.snd p'.base z.hom = l ≫ pullback.snd p.base z.hom) :
    l' ≫ p'.lift = l ≫ p.lift := by
  obtain ⟨-, q, hqf, hqs, hl⟩ := h
  have hq : l' ≫ q = l := by
    refine pullback.hom_ext ?_ ?_
    · simpa only [Category.assoc, hqf] using hf
    · simpa only [Category.assoc, hqs] using hs
  rw [hl, ← Category.assoc, hq]

/-- The pairs attached to the scheme-valued points of `T` by a morphism
`v : T ⟶ Res_{Z/Q}(X)` are compatible with base change along maps of representables. -/
theorem isPullbackAlong_pairEquiv_yonedaEquiv_comp
    (v : T ⟶ (restrictionOfScalars B S hS x z).presheaf)
    {U V : BigFppfOver B S hS} (f : yoneda.obj V ⟶ yoneda.obj U) (i : yoneda.obj U ⟶ T) :
    RestrictionPair.IsPullbackAlong f
      ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv (i ≫ v)))
      ((restrictionOfScalars B S hS x z).pairEquiv V (yonedaEquiv ((f ≫ i) ≫ v))) := by
  obtain ⟨g, rfl⟩ := yoneda.map_surjective f
  have h := (restrictionOfScalars B S hS x z).natural g (yonedaEquiv (i ≫ v))
  simpa only [yonedaEquiv_naturality, Category.assoc] using h

/-- The second component of the pair a morphism `v : T ⟶ Res_{Z/Q}(X)` should have, evaluated at
a scheme-valued point of `T ×_{a, Q} Z`: such a point is a point `i` of `T` together with a
factorization `k` of `i ≫ a` through `z`, and the value is the second component of the pair of
Stacks 05YA at `i`, read at that factorization. -/
noncomputable def pointLift (v : T ⟶ (restrictionOfScalars B S hS x z).presheaf)
    (U : BigFppfOver B S hS) (i : yoneda.obj U ⟶ T) (k : yoneda.obj U ⟶ Z.obj)
    (h : i ≫ v ≫ (restrictionOfScalars B S hS x z).projection = k ≫ z.hom) :
    yoneda.obj U ⟶ X.obj :=
  pullback.lift (𝟙 _) k
      (by simpa only [Category.id_comp, base_pairEquiv_yonedaEquiv_comp] using h) ≫
    ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv (i ≫ v))).lift

/-- `AlgebraicGeometry.Space.pointLift` is computed by the pair at *any* scheme-valued point of
`T` that the given point of the fibre product factors through. -/
theorem pointLift_eq (v : T ⟶ (restrictionOfScalars B S hS x z).presheaf)
    {U V : BigFppfOver B S hS} (i : yoneda.obj U ⟶ T)
    (l : yoneda.obj V ⟶ pullback
      ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv (i ≫ v))).base z.hom)
    (j : yoneda.obj V ⟶ T) (k : yoneda.obj V ⟶ Z.obj)
    (hj : j = l ≫ pullback.fst _ _ ≫ i) (hk : k = l ≫ pullback.snd _ _)
    (h : j ≫ v ≫ (restrictionOfScalars B S hS x z).projection = k ≫ z.hom) :
    pointLift x z v V j k h =
      l ≫ ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv (i ≫ v))).lift := by
  subst hj
  unfold pointLift
  apply lift_eq_of_isPullbackAlong x z (f := l ≫ pullback.fst _ _)
    (by simpa only [Category.assoc] using
      isPullbackAlong_pairEquiv_yonedaEquiv_comp x z v (l ≫ pullback.fst _ _) i)
  · simp only [pullback.lift_fst_assoc, Category.id_comp]
  · simpa only [pullback.lift_snd] using hk

/-- `AlgebraicGeometry.Space.pointLift` is natural in the scheme-valued point. -/
theorem pointLift_natural (v : T ⟶ (restrictionOfScalars B S hS x z).presheaf)
    {U V : BigFppfOver B S hS} (f : V ⟶ U) (i : yoneda.obj U ⟶ T) (k : yoneda.obj U ⟶ Z.obj)
    (h : i ≫ v ≫ (restrictionOfScalars B S hS x z).projection = k ≫ z.hom) :
    pointLift x z v V (yoneda.map f ≫ i) (yoneda.map f ≫ k)
        (by simpa only [Category.assoc] using congrArg (yoneda.map f ≫ ·) h) =
      yoneda.map f ≫ pointLift x z v U i k h := by
  unfold pointLift
  apply lift_eq_of_isPullbackAlong x z
    (isPullbackAlong_pairEquiv_yonedaEquiv_comp x z v (yoneda.map f) i)
    (yoneda.map f ≫ pullback.lift (𝟙 _) k _)
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp,
      Category.comp_id]
  · simp only [Category.assoc, pullback.lift_snd]

/-- **Every morphism into the restriction of scalars comes from a pair**, whose base changes to
the scheme-valued points of `T` are the pairs of Stacks 05YA. -/
theorem exists_restrictionPair_of_hom
    (v : T ⟶ (restrictionOfScalars B S hS x z).presheaf) :
    ∃ p : RestrictionPair B S hS x z T, ∀ U (i : yoneda.obj U ⟶ T),
      RestrictionPair.IsPullbackAlong i p
        ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv (i ≫ v))) := by
  obtain ⟨l, hl⟩ := exists_hom_of_yoneda
    (fun U i => pointLift x z v U (i ≫ pullback.fst _ z.hom) (i ≫ pullback.snd _ z.hom)
      (comp_pullback_condition i))
    (by
      intro U V f i
      simpa only [Category.assoc] using pointLift_natural x z v f
        (i ≫ pullback.fst _ z.hom) (i ≫ pullback.snd _ z.hom) (comp_pullback_condition i))
  have ho : l ≫ x.hom =
      pullback.snd (v ≫ (restrictionOfScalars B S hS x z).projection) z.hom := by
    refine hom_ext_yoneda fun U i => ?_
    rw [← Category.assoc, hl]
    unfold pointLift
    rw [Category.assoc, RestrictionPair.over, pullback.lift_snd]
  refine ⟨⟨v ≫ (restrictionOfScalars B S hS x z).projection, l, ho⟩, fun U i => ?_⟩
  have hbase := base_pairEquiv_yonedaEquiv_comp x z v U i
  refine ⟨hbase, pullback.lift (pullback.fst _ z.hom ≫ i) (pullback.snd _ z.hom)
      (by rw [Category.assoc, ← hbase]; exact pullback.condition),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  refine hom_ext_yoneda fun V j => ?_
  rw [← Category.assoc, hl]
  exact (pointLift_eq x z v i j _ _ (by simp only [Category.assoc, pullback.lift_fst])
    (by simp only [Category.assoc, pullback.lift_snd]) _).symm

/-- **Two pairs over `T` with a common base change at every scheme-valued point of `T` are
equal.** -/
theorem restrictionPair_ext_of_points (p q : RestrictionPair B S hS x z T)
    (h : ∀ U (i : yoneda.obj U ⟶ T), ∃ r : RestrictionPair B S hS x z (yoneda.obj U),
      RestrictionPair.IsPullbackAlong i p r ∧ RestrictionPair.IsPullbackAlong i q r) :
    p = q := by
  obtain ⟨b, l, hol⟩ := p
  obtain ⟨b', l', hol'⟩ := q
  have hbase : b = b' := by
    refine hom_ext_yoneda fun U i => ?_
    obtain ⟨r, hr, hs⟩ := h U i
    exact hr.1.symm.trans hs.1
  subst hbase
  congr 1
  refine hom_ext_yoneda fun U i => ?_
  obtain ⟨r, hr, hs⟩ := h U (i ≫ pullback.fst b z.hom)
  have hcond : (𝟙 (yoneda.obj U) : yoneda.obj U ⟶ _) ≫ r.base =
      (i ≫ pullback.snd b z.hom) ≫ z.hom := by
    rw [Category.id_comp, hr.1]
    exact comp_pullback_condition i
  exact (lift_eq_of_isPullbackAlong x z hr i (pullback.lift _ _ hcond)
      (by simp only [pullback.lift_fst_assoc, Category.id_comp])
      (by simp only [pullback.lift_snd])).symm.trans
    (lift_eq_of_isPullbackAlong x z hs i (pullback.lift _ _ hcond)
      (by simp only [pullback.lift_fst_assoc, Category.id_comp])
      (by simp only [pullback.lift_snd]))

/-- The morphism into the restriction of scalars determined by a pair over `T`: at a
scheme-valued point of `T` it is the base change of the pair along that point. -/
noncomputable def homOfRestrictionPair (p : RestrictionPair B S hS x z T) :
    T ⟶ (restrictionOfScalars B S hS x z).presheaf where
  app U := ↾fun t => ((restrictionOfScalars B S hS x z).pairEquiv U.unop).symm
    (RestrictionPair.restrict (yonedaEquiv.symm t) p)
  naturality := by
    intro U V f
    ext t
    refine ((restrictionOfScalars B S hS x z).pairEquiv V.unop).injective ?_
    have hn := (restrictionOfScalars B S hS x z).natural f.unop
      (((restrictionOfScalars B S hS x z).pairEquiv U.unop).symm
        (RestrictionPair.restrict (yonedaEquiv.symm t) p))
    simp only [Equiv.apply_symm_apply, Quiver.Hom.op_unop] at hn
    change ((restrictionOfScalars B S hS x z).pairEquiv V.unop)
        (((restrictionOfScalars B S hS x z).pairEquiv V.unop).symm
          (RestrictionPair.restrict (yonedaEquiv.symm (T.map f t)) p)) =
      ((restrictionOfScalars B S hS x z).pairEquiv V.unop)
        ((restrictionOfScalars B S hS x z).presheaf.map f
          (((restrictionOfScalars B S hS x z).pairEquiv U.unop).symm
            (RestrictionPair.restrict (yonedaEquiv.symm t) p)))
    rw [Equiv.apply_symm_apply, RestrictionPair.eq_restrict_of_isPullbackAlong hn,
      RestrictionPair.restrict_comp,
      show yoneda.map f.unop ≫ yonedaEquiv.symm t = yonedaEquiv.symm (T.map f t) by
        simpa only [Quiver.Hom.op_unop] using yonedaEquiv_symm_naturality_left f.unop T t]

/-- The pair at a scheme-valued point of the morphism attached to a pair `p` is the base change
of `p` along that point. -/
theorem pairEquiv_homOfRestrictionPair (p : RestrictionPair B S hS x z T)
    (U : BigFppfOver B S hS) (i : yoneda.obj U ⟶ T) :
    (restrictionOfScalars B S hS x z).pairEquiv U
        (yonedaEquiv (i ≫ homOfRestrictionPair x z p)) =
      RestrictionPair.restrict i p := by
  rw [yonedaEquiv_comp]
  show (restrictionOfScalars B S hS x z).pairEquiv U
    (((restrictionOfScalars B S hS x z).pairEquiv U).symm
      (RestrictionPair.restrict (yonedaEquiv.symm (yonedaEquiv i)) p)) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

end Points

/-! ### The functor of points of the restriction of scalars -/

variable {X Z Q : AlgebraicSpaces B S hS}

/-- **Stacks 05YB.** Morphisms from an algebraic space `T` into the restriction of scalars
`Res_{Z/Q}(X)` of `x : X ⟶ Z` along `z : Z ⟶ Q` are the pairs `(a, b)` of Stacks 05Y9 at `T`:
a morphism `a : T ⟶ Q` together with a morphism `b : T ×_{a, Q} Z ⟶ X` over `Z`.

The bijection is characterized by the two properties recorded with it: its value at `v` base
changes, along every scheme-valued point `i` of `T`, to the pair that Stacks 05YA attaches to
`i ≫ v`; and it is natural in `T`. -/
@[stacks 05YB "the functor of points"]
noncomputable def restrictionOfScalarsHomEquiv (x : X ⟶ Z) (z : Z ⟶ Q) :
    {e : ∀ T : AlgebraicSpaces B S hS,
        (T.obj ⟶ (restrictionOfScalars B S hS x z).presheaf) ≃
          RestrictionPair B S hS x z T.obj //
      (∀ (T : AlgebraicSpaces B S hS) (U : BigFppfOver B S hS) (i : yoneda.obj U ⟶ T.obj)
          (v : T.obj ⟶ (restrictionOfScalars B S hS x z).presheaf),
        RestrictionPair.IsPullbackAlong i (e T v)
          ((restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv (i ≫ v)))) ∧
      (∀ (T T' : AlgebraicSpaces B S hS) (f : T' ⟶ T)
          (v : T.obj ⟶ (restrictionOfScalars B S hS x z).presheaf),
        RestrictionPair.IsPullbackAlong f.hom (e T v) (e T' (f.hom ≫ v)))} := by
  classical
  choose p hp using fun (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (v : T ⟶ (restrictionOfScalars B S hS x z).presheaf) =>
      exists_restrictionPair_of_hom x z v
  have hleft (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (v : T ⟶ (restrictionOfScalars B S hS x z).presheaf) :
      homOfRestrictionPair x z (p T v) = v := by
    refine hom_ext_yoneda fun U i => yonedaEquiv.injective
      (((restrictionOfScalars B S hS x z).pairEquiv U).injective ?_)
    rw [pairEquiv_homOfRestrictionPair]
    exact (RestrictionPair.eq_restrict_of_isPullbackAlong (hp T v U i)).symm
  have hright (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : RestrictionPair B S hS x z T) :
      p T (homOfRestrictionPair x z q) = q := by
    refine restrictionPair_ext_of_points x z _ _ fun U i =>
      ⟨RestrictionPair.restrict i q, ?_, RestrictionPair.isPullbackAlong_restrict i q⟩
    simpa only [pairEquiv_homOfRestrictionPair] using hp T (homOfRestrictionPair x z q) U i
  refine ⟨fun T =>
    { toFun := p T.obj
      invFun := homOfRestrictionPair x z
      left_inv := hleft T.obj
      right_inv := hright T.obj },
    fun T U i v => hp T.obj v U i, fun T T' f v => ?_⟩
  have heq : p T'.obj (f.hom ≫ v) = RestrictionPair.restrict f.hom (p T.obj v) := by
    refine restrictionPair_ext_of_points x z _ _ fun U i =>
      ⟨(restrictionOfScalars B S hS x z).pairEquiv U (yonedaEquiv ((i ≫ f.hom) ≫ v)), ?_, ?_⟩
    · simpa only [Category.assoc] using hp T'.obj (f.hom ≫ v) U i
    · rw [RestrictionPair.eq_restrict_of_isPullbackAlong (hp T.obj v U (i ≫ f.hom)),
        ← RestrictionPair.restrict_comp f.hom i]
      exact RestrictionPair.isPullbackAlong_restrict i _
  change RestrictionPair.IsPullbackAlong f.hom (p T.obj v) (p T'.obj (f.hom ≫ v))
  rw [heq]
  exact RestrictionPair.isPullbackAlong_restrict f.hom _

/-! ### Functoriality in the upper space -/

/-- The morphism of restrictions of scalars `Res_{Z/Q}(X') ⟶ Res_{Z/Q}(X)` induced by a
morphism `g : X' ⟶ X` over `Z`, together with its characterization: on the pairs of Stacks 05YA
it is postcomposition of the second component with `g`. -/
noncomputable def restrictionOfScalarsMap {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    {x' : X' ⟶ Z} {x : X ⟶ Z} (hg : g ≫ x = x') (z : Z ⟶ Q) :
    {m : (restrictionOfScalars B S hS x' z).presheaf ⟶
        (restrictionOfScalars B S hS x z).presheaf //
      ∀ T (v : (restrictionOfScalars B S hS x' z).presheaf.obj (op T)),
        (restrictionOfScalars B S hS x z).pairEquiv T (m.app (op T) v) =
          RestrictionPair.postcomp g hg
            ((restrictionOfScalars B S hS x' z).pairEquiv T v)} :=
  ⟨{ app := fun U => ↾fun v => ((restrictionOfScalars B S hS x z).pairEquiv U.unop).symm
        (RestrictionPair.postcomp g hg
          ((restrictionOfScalars B S hS x' z).pairEquiv U.unop v))
     naturality := by
       intro U V f
       ext v
       refine ((restrictionOfScalars B S hS x z).pairEquiv V.unop).injective ?_
       have hp := (restrictionOfScalars B S hS x' z).natural f.unop v
       have hr := (restrictionOfScalars B S hS x z).natural f.unop
         (((restrictionOfScalars B S hS x z).pairEquiv U.unop).symm
           (RestrictionPair.postcomp g hg
             ((restrictionOfScalars B S hS x' z).pairEquiv U.unop v)))
       simp only [Equiv.apply_symm_apply, Quiver.Hom.op_unop] at hp hr
       change ((restrictionOfScalars B S hS x z).pairEquiv V.unop)
           (((restrictionOfScalars B S hS x z).pairEquiv V.unop).symm
             (RestrictionPair.postcomp g hg
               ((restrictionOfScalars B S hS x' z).pairEquiv V.unop
                 ((restrictionOfScalars B S hS x' z).presheaf.map f v)))) =
         ((restrictionOfScalars B S hS x z).pairEquiv V.unop)
           ((restrictionOfScalars B S hS x z).presheaf.map f
             (((restrictionOfScalars B S hS x z).pairEquiv U.unop).symm
               (RestrictionPair.postcomp g hg
                 ((restrictionOfScalars B S hS x' z).pairEquiv U.unop v))))
       rw [Equiv.apply_symm_apply, RestrictionPair.eq_restrict_of_isPullbackAlong hr,
         RestrictionPair.eq_restrict_of_isPullbackAlong hp,
         RestrictionPair.restrict_postcomp] },
    fun _ _ => Equiv.apply_symm_apply _ _⟩

end AlgebraicGeometry.Space

end
