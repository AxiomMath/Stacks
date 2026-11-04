module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Diagonal

/-!
# The diagonal criterion along an arbitrary embedding

`AlgebraicGeometry.Space.presheaf_diagonal` is **Stacks 0CB7** for a presheaf of `Type u` on
the big fppf site of `S` and the Yoneda embedding. The sheaves carrying formal algebraic
spaces take values in `Type (u + 1)` and are tested against the *sheafified* Yoneda embedding,
so that form of the criterion does not apply to them.

Nothing in the argument is about Yoneda, however. What it uses is that the embedding is fully
faithful and preserves fibre products and binary products, and that is as true of the
sheafified Yoneda embedding of a subcanonical site as it is of Yoneda. This file therefore
restates the criterion for an arbitrary such functor, and instantiates it at the sheafified
Yoneda embedding of the big fppf site over `S`.

## Main results

* `CategoryTheory.MorphismProperty.relative_diag_of_forall_isPullback`: if every pair of
  `F`-represented points of an object `G` has a fibre product which is again `F`-represented,
  by an object whose canonical morphism to the product of the two sources has `Q`, then the
  diagonal of `G` has `Q` relative to `F`.
* `CategoryTheory.MorphismProperty.isPullback_diag_prodMap`: the fibre product of two
  morphisms with a common target is the base change of the diagonal of that target along the
  product of the two morphisms.
* `CategoryTheory.MorphismProperty.isPullback_pullbackBaseChangeComparison`: the base change
  of a fibre product along a morphism of the common target is the fibre product of the two
  base changes.
* `CategoryTheory.MorphismProperty.isPullback_of_isPullback_comp_mono` and
  `…isPullback_map_pullback_of_mono`: a cartesian square whose two legs are composed with a
  common monomorphism is cartesian for the legs themselves; consequently a fibre product of two
  `F`-represented points of a subobject of `F.obj Z` is computed in `Z`.
* `CategoryTheory.MorphismProperty.mono_prodLift_pullback` and
  `…mono_prodLift_pullback_comp_inv_prodComparison`: the canonical morphism from a fibre
  product to the product of its two factors, and to `F.obj (U ⨯ V)`, is a monomorphism.
* `CategoryTheory.MorphismProperty.exists_isPullback_of_relative_diag`: the converse of the
  criterion — from `Q` relative to `F` at the diagonal of `G` back to the fibre products of
  pairs of `F`-represented points of `G`.
* `AlgebraicGeometry.Space.sheaf_diagonal`: the same criterion for the sheafified Yoneda
  embedding of the big fppf site over `S`, which is the form the diagonal of a formal
  algebraic space is stated in.

## Implementation notes

The hypothesis is phrased with morphisms `F.obj U ⟶ G` rather than with sections of a
presheaf, which is what makes it independent of Yoneda; for `F = yoneda` the two are matched
by `CategoryTheory.yonedaEquiv`, so the statement below specializes to
`AlgebraicGeometry.Space.presheaf_diagonal`.

The one step of the argument that was genuinely about Yoneda is the verification that a
morphism into `F.obj (U ⨯ U)` is determined by its two components. For a general `F` this is
exactly the statement that `CategoryTheory.Limits.prodComparison F U U` is an isomorphism,
which is the hypothesis that `F` preserves binary products.

`Q` is assumed stable under base change rather than merely monotone, because the representing
object produced for the diagonal is cut out of the one produced for the pairwise fibre product
by a further base change along the diagonal of the test object. The converse direction needs no
hypothesis on `Q` at all, and none on `F` beyond preservation of binary products: the fibre
product of two points is literally a base change of the diagonal, so the object the relative
property hands back over the test object `U ⨯ V` represents it.

## References

* [Stacks Project, Tag 0CB7](https://stacks.math.columbia.edu/tag/0CB7)
* [Stacks Project, Tag 025W](https://stacks.math.columbia.edu/tag/025W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]


/-- The fibre product of two morphisms with a common target is the base change of the
diagonal of that target along the product of the two morphisms. -/
theorem isPullback_diag_prodMap {X Y Z : D} [HasPullbacks D] [HasBinaryProducts D]
    (α : X ⟶ Z) (β : Y ⟶ Z) :
    IsPullback (pullback.fst α β ≫ α)
      (Limits.prod.lift (pullback.fst α β) (pullback.snd α β)) (diag Z)
      (Limits.prod.map α β) := by
  have hcomm : (pullback.fst α β ≫ α) ≫ diag Z =
      Limits.prod.lift (pullback.fst α β) (pullback.snd α β) ≫ Limits.prod.map α β := by
    apply Limits.prod.hom_ext
    · simp
    · simp [pullback.condition]
  have key : ∀ s : PullbackCone (diag Z) (Limits.prod.map α β),
      (s.snd ≫ Limits.prod.fst) ≫ α = (s.snd ≫ Limits.prod.snd) ≫ β := by
    intro s
    have h₁ := congrArg (fun k => k ≫ Limits.prod.fst) s.condition
    have h₂ := congrArg (fun k => k ≫ Limits.prod.snd) s.condition
    simp only [Category.assoc, Limits.prod.map_fst, Limits.prod.map_snd, diag,
      Limits.prod.lift_fst, Limits.prod.lift_snd] at h₁ h₂
    rw [Category.assoc, Category.assoc, ← h₁, ← h₂]
  have hfst : ∀ s : PullbackCone (diag Z) (Limits.prod.map α β),
      s.snd ≫ Limits.prod.fst ≫ α = s.fst := by
    intro s
    have h₁ := congrArg (fun k => k ≫ Limits.prod.fst) s.condition
    simp only [Category.assoc, Limits.prod.map_fst, diag, Limits.prod.lift_fst] at h₁
    simpa using h₁.symm
  refine ⟨⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk hcomm
    (fun s => pullback.lift (s.snd ≫ Limits.prod.fst) (s.snd ≫ Limits.prod.snd) (key s))
    (fun s => ?_) (fun s => ?_) (fun s m _ hm₂ => ?_)⟩⟩
  · rw [← Category.assoc, pullback.lift_fst, Category.assoc]
    exact hfst s
  · apply Limits.prod.hom_ext
    · rw [Category.assoc, Limits.prod.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, Limits.prod.lift_snd, pullback.lift_snd]
  · apply pullback.hom_ext
    · rw [pullback.lift_fst]
      simpa using congrArg (fun k => k ≫ Limits.prod.fst) hm₂
    · rw [pullback.lift_snd]
      simpa using congrArg (fun k => k ≫ Limits.prod.snd) hm₂

/-- The canonical morphism from a fibre product to the product of its two factors is a
monomorphism: it is a base change of the diagonal of the common target, and a diagonal is a
split monomorphism. -/
theorem mono_prodLift_pullback {X Y Z : D} [HasPullbacks D] [HasBinaryProducts D]
    (α : X ⟶ Z) (β : Y ⟶ Z) :
    Mono (Limits.prod.lift (pullback.fst α β) (pullback.snd α β)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := MorphismProperty.monomorphisms D) (isPullback_diag_prodMap α β)
    (show Mono (diag Z) from inferInstance)


/-- **The fibre product of two `F`-represented points of `G` is a subobject of `F.obj (U ⨯ V)`,
provided `F` preserves binary products.** -/
theorem mono_prodLift_pullback_comp_inv_prodComparison (F : C ⥤ D) [HasBinaryProducts C]
    [HasPullbacks D] [HasBinaryProducts D]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    {G : D} {U V : C} (α : F.obj U ⟶ G) (β : F.obj V ⟶ G) :
    Mono (Limits.prod.lift (pullback.fst α β) (pullback.snd α β) ≫
      inv (prodComparison F U V)) :=
  have _ := mono_prodLift_pullback α β
  mono_comp _ _

/-- The monomorphism exhibiting the fibre product of two `F`-represented points of `G` as a
subobject of `F.obj (U ⨯ V)`, for an `F` preserving binary products. -/
noncomputable def monoPullbackToProd (F : C ⥤ D) [HasBinaryProducts C] [HasPullbacks D]
    [HasBinaryProducts D] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    {G : D} {U V : C} (α : F.obj U ⟶ G) (β : F.obj V ⟶ G) :
    pullback α β ⟶ F.obj (U ⨯ V) :=
  Limits.prod.lift (pullback.fst α β) (pullback.snd α β) ≫ inv (prodComparison F U V)

/-- `monoPullbackToProd F α β` is the product lift of the two projections of `pullback α β`
followed by the inverse of the comparison `F.obj (U ⨯ V) ⟶ F.obj U ⨯ F.obj V`. -/
lemma monoPullbackToProd_def (F : C ⥤ D) [HasBinaryProducts C] [HasPullbacks D]
    [HasBinaryProducts D] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    {G : D} {U V : C} (α : F.obj U ⟶ G) (β : F.obj V ⟶ G) :
    monoPullbackToProd F α β =
      Limits.prod.lift (pullback.fst α β) (pullback.snd α β) ≫ inv (prodComparison F U V) :=
  rfl

/-- Composing `monoPullbackToProd F α β` with `F.map prod.fst` gives the first projection of
`pullback α β`. -/
@[simp]
lemma monoPullbackToProd_comp_map_fst (F : C ⥤ D) [HasBinaryProducts C] [HasPullbacks D]
    [HasBinaryProducts D] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    {G : D} {U V : C} (α : F.obj U ⟶ G) (β : F.obj V ⟶ G) :
    monoPullbackToProd F α β ≫ F.map Limits.prod.fst = pullback.fst α β := by
  rw [monoPullbackToProd_def, Category.assoc, ← prodComparison_fst F U V,
    IsIso.inv_hom_id_assoc, Limits.prod.lift_fst]

/-- Composing `monoPullbackToProd F α β` with `F.map prod.snd` gives the second projection of
`pullback α β`. -/
@[simp]
lemma monoPullbackToProd_comp_map_snd (F : C ⥤ D) [HasBinaryProducts C] [HasPullbacks D]
    [HasBinaryProducts D] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    {G : D} {U V : C} (α : F.obj U ⟶ G) (β : F.obj V ⟶ G) :
    monoPullbackToProd F α β ≫ F.map Limits.prod.snd = pullback.snd α β := by
  rw [monoPullbackToProd_def, Category.assoc, ← prodComparison_snd F U V,
    IsIso.inv_hom_id_assoc, Limits.prod.lift_snd]

/-- `monoPullbackToProd F α β` is a monomorphism. -/
instance mono_monoPullbackToProd (F : C ⥤ D) [HasBinaryProducts C] [HasPullbacks D]
    [HasBinaryProducts D] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    {G : D} {U V : C} (α : F.obj U ⟶ G) (β : F.obj V ⟶ G) :
    Mono (monoPullbackToProd F α β) :=
  mono_prodLift_pullback_comp_inv_prodComparison F α β

/-- A point of the fibre product recorded by a morphism of `C` to `U ⨯ V` with the expected two
components does land in the subobject by that morphism. -/
theorem map_eq_comp_monoPullbackToProd (F : C ⥤ D) [HasBinaryProducts C] [HasPullbacks D]
    [HasBinaryProducts D] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    {G : D} {U V : C} (α : F.obj U ⟶ G) (β : F.obj V ⟶ G)
    {A : C} (ι : F.obj A ⟶ pullback α β) (c : A ⟶ U ⨯ V)
    (h₁ : F.map (c ≫ Limits.prod.fst) = ι ≫ pullback.fst α β)
    (h₂ : F.map (c ≫ Limits.prod.snd) = ι ≫ pullback.snd α β) :
    F.map c = ι ≫ monoPullbackToProd F α β := by
  rw [monoPullbackToProd_def, ← Category.assoc, IsIso.eq_comp_inv]
  apply Limits.prod.hom_ext
  · rwa [Category.assoc, prodComparison_fst, Category.assoc, Limits.prod.lift_fst, ← F.map_comp]
  · rwa [Category.assoc, prodComparison_snd, Category.assoc, Limits.prod.lift_snd, ← F.map_comp]

section CancelMono

/-- **A cartesian square whose two legs are composed with a common monomorphism is cartesian
for the legs themselves.** Composing with a monomorphism neither adds nor removes commuting
squares, so the two cospans have the same cones and the same limit.

For a fibre product of two points of a subobject `G ⟶ Q` this says the fibre product may be
computed in `Q`: the condition that two maps agree in `G` is the condition that they agree in
`Q`, once both are known to land in `G`. -/
@[ega "I 3.2.4" "Direction", sga "3 IV 2.5" "converse"]
theorem isPullback_of_isPullback_comp_mono {P A T G Q : D} {p : P ⟶ A} {q : P ⟶ T}
    {u : A ⟶ G} {v : T ⟶ G} {m : G ⟶ Q} [Mono m]
    (h : IsPullback p q (u ≫ m) (v ≫ m)) : IsPullback p q u v := by
  have hw : p ≫ u = q ≫ v := by
    rw [← cancel_mono m, Category.assoc, Category.assoc]
    exact h.w
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun s => h.lift s.fst s.snd
      (by rw [← Category.assoc, ← Category.assoc, s.condition]))
    (fun s => h.lift_fst _ _ _) (fun s => h.lift_snd _ _ _)
    (fun s n h₁ h₂ => h.hom_ext (by rwa [h.lift_fst]) (by rwa [h.lift_snd]))⟩⟩

/-- **The fibre product of two `F`-represented points of a subobject of `F.obj Z` is
`F`-represented, by the fibre product over `Z`.** If `ρ : G ⟶ F.obj Z` is a monomorphism and
two points `ι : F.obj A ⟶ G`, `x : F.obj T ⟶ G` are induced by morphisms `a : A ⟶ Z`,
`b : T ⟶ Z`, then `F` carries the fibre product `A ×_Z T` to the fibre product of `ι` and `x`
over `G`. -/
theorem isPullback_map_pullback_of_mono (F : C ⥤ D) [HasPullbacks C] [HasPullbacks D]
    [PreservesLimitsOfShape WalkingCospan F] {G : D} {Z : C} (ρ : G ⟶ F.obj Z) [Mono ρ]
    {A T : C} (ι : F.obj A ⟶ G) (x : F.obj T ⟶ G) (a : A ⟶ Z) (b : T ⟶ Z)
    (ha : F.map a = ι ≫ ρ) (hb : F.map b = x ≫ ρ) :
    IsPullback (F.map (pullback.fst a b)) (F.map (pullback.snd a b)) ι x := by
  refine isPullback_of_isPullback_comp_mono (m := ρ) ?_
  rw [← ha, ← hb]
  exact (IsPullback.of_hasPullback a b).map F

end CancelMono

section BaseChangeOfPullback

variable [HasPullbacks D] {A C X Y : D} (α : A ⟶ X) (β : C ⟶ X) (f : Y ⟶ X)

/-- The canonical morphism to `A ×_X C` from the fibre product over `Y` of the two base
changes `A ×_X Y` and `C ×_X Y`. -/
noncomputable def pullbackBaseChangeComparison :
    pullback (pullback.snd α f) (pullback.snd β f) ⟶ pullback α β :=
  pullback.lift
    (pullback.fst (pullback.snd α f) (pullback.snd β f) ≫ pullback.fst α f)
    (pullback.snd (pullback.snd α f) (pullback.snd β f) ≫ pullback.fst β f)
    (by
      rw [Category.assoc, Category.assoc, pullback.condition (f := α) (g := f),
        pullback.condition (f := β) (g := f), ← Category.assoc, ← Category.assoc,
        pullback.condition (f := pullback.snd α f) (g := pullback.snd β f)])

/-- The first component of `pullbackBaseChangeComparison α β f` is the composite of the first
projection with `A ×_X Y ⟶ A`. -/
@[simp]
lemma pullbackBaseChangeComparison_fst :
    pullbackBaseChangeComparison α β f ≫ pullback.fst α β =
      pullback.fst (pullback.snd α f) (pullback.snd β f) ≫ pullback.fst α f :=
  pullback.lift_fst _ _ _

/-- The second component of `pullbackBaseChangeComparison α β f` is the composite of the second
projection with `C ×_X Y ⟶ C`. -/
@[simp]
lemma pullbackBaseChangeComparison_snd :
    pullbackBaseChangeComparison α β f ≫ pullback.snd α β =
      pullback.snd (pullback.snd α f) (pullback.snd β f) ≫ pullback.fst β f :=
  pullback.lift_snd _ _ _

/-- **The base change of a fibre product along a morphism of the common target is the fibre
product of the two base changes.** For `α : A ⟶ X`, `β : C ⟶ X` and `f : Y ⟶ X`, the fibre
product over `Y` of `A ×_X Y` with `C ×_X Y` is the base change of `A ×_X C ⟶ X` along `f`. -/
theorem isPullback_pullbackBaseChangeComparison :
    IsPullback (pullbackBaseChangeComparison α β f)
      (pullback.fst (pullback.snd α f) (pullback.snd β f) ≫ pullback.snd α f)
      (pullback.fst α β ≫ α) f := by
  have hcomm : pullbackBaseChangeComparison α β f ≫ pullback.fst α β ≫ α =
      (pullback.fst (pullback.snd α f) (pullback.snd β f) ≫ pullback.snd α f) ≫ f := by
    rw [← Category.assoc, pullbackBaseChangeComparison_fst, Category.assoc, Category.assoc,
      pullback.condition (f := α) (g := f)]
  refine ⟨⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk hcomm (fun s => ?_) (fun s => ?_) (fun s => ?_)
    (fun s m hm₁ hm₂ => ?_)⟩⟩
  · have h₂ : (s.fst ≫ pullback.snd α β) ≫ β = s.snd ≫ f := by
      rw [Category.assoc, ← pullback.condition (f := α) (g := β)]
      exact s.condition
    exact pullback.lift (pullback.lift (s.fst ≫ pullback.fst α β) s.snd
        ((Category.assoc _ _ _).trans s.condition))
      (pullback.lift (s.fst ≫ pullback.snd α β) s.snd h₂)
      (by rw [pullback.lift_snd, pullback.lift_snd])
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullbackBaseChangeComparison_fst]
      rw [pullback.lift_fst_assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullbackBaseChangeComparison_snd]
      rw [pullback.lift_snd_assoc, pullback.lift_fst]
  · rw [pullback.lift_fst_assoc, pullback.lift_snd]
  · have e₁ : m ≫ pullback.fst (pullback.snd α f) (pullback.snd β f) ≫ pullback.fst α f =
        s.fst ≫ pullback.fst α β := by
      rw [← pullbackBaseChangeComparison_fst, ← Category.assoc, hm₁]
    have e₂ : m ≫ pullback.snd (pullback.snd α f) (pullback.snd β f) ≫ pullback.fst β f =
        s.fst ≫ pullback.snd α β := by
      rw [← pullbackBaseChangeComparison_snd, ← Category.assoc, hm₁]
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst]
        simpa only [Category.assoc] using e₁
      · rw [pullback.lift_snd]
        simpa only [Category.assoc] using hm₂
    · rw [pullback.lift_snd]
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst]
        simpa only [Category.assoc] using e₂
      · rw [pullback.lift_snd]
        simp only [Category.assoc]
        rw [← pullback.condition (f := pullback.snd α f) (g := pullback.snd β f)]
        exact hm₂

end BaseChangeOfPullback

/-- A morphism into `F.obj (U ⨯ V)` is determined by its two components, for an `F` preserving
binary products. -/
theorem map_prod_hom_ext (F : C ⥤ D) [HasBinaryProducts C] [HasBinaryProducts D]
    [PreservesLimitsOfShape (Discrete WalkingPair) F] {T : D} {U V : C}
    {a b : T ⟶ F.obj (U ⨯ V)} (h₁ : a ≫ F.map Limits.prod.fst = b ≫ F.map Limits.prod.fst)
    (h₂ : a ≫ F.map Limits.prod.snd = b ≫ F.map Limits.prod.snd) : a = b := by
  rw [← cancel_mono (prodComparison F U V)]
  apply Limits.prod.hom_ext
  · simpa only [Category.assoc, prodComparison_fst] using h₁
  · simpa only [Category.assoc, prodComparison_snd] using h₂

/-- **The base change of the diagonal of `G` along a point `g : F.obj U ⟶ G ⨯ G` is
`F`-represented.** If `F.obj W` is the fibre product of the two components of `g`, by a morphism
`f : W ⟶ U ⨯ U` with those components, then `F` carries the base change of `f` along the
diagonal of `U` to the base change of the diagonal of `G` along `g`. -/
theorem isPullback_map_of_isPullback_diag (F : C ⥤ D) [HasBinaryProducts C]
    [HasBinaryProducts D] [HasPullbacks D] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesLimitsOfShape (Discrete WalkingPair) F] {G : D} {U W X : C}
    (g : F.obj U ⟶ G ⨯ G) (i : F.obj W ≅ pullback (g ≫ Limits.prod.fst) (g ≫ Limits.prod.snd))
    {f : W ⟶ U ⨯ U}
    (hf₁ : F.map (f ≫ Limits.prod.fst) = i.hom ≫ pullback.fst _ _)
    (hf₂ : F.map (f ≫ Limits.prod.snd) = i.hom ≫ pullback.snd _ _)
    {p : X ⟶ W} {q : X ⟶ U} (hpq : IsPullback p q f (Limits.diag U)) :
    IsPullback (F.map q ≫ g ≫ Limits.prod.fst) (F.map q) (diag G) g := by
  have hW : IsPullback (i.hom ≫ pullback.fst (g ≫ Limits.prod.fst) (g ≫ Limits.prod.snd))
      (i.hom ≫ pullback.snd (g ≫ Limits.prod.fst) (g ≫ Limits.prod.snd))
      (g ≫ Limits.prod.fst) (g ≫ Limits.prod.snd) :=
    IsPullback.of_iso_pullback
      ⟨by simpa using congrArg (fun k => i.hom ≫ k) pullback.condition⟩ i rfl rfl
  have hX := hpq.map F
  have hp₁ : F.map p ≫ i.hom ≫ pullback.fst (g ≫ Limits.prod.fst) (g ≫ Limits.prod.snd) =
      F.map q := by
    rw [← hf₁, ← F.map_comp, ← Category.assoc, hpq.w]
    simp
  have hp₂ : F.map p ≫ i.hom ≫ pullback.snd (g ≫ Limits.prod.fst) (g ≫ Limits.prod.snd) =
      F.map q := by
    rw [← hf₂, ← F.map_comp, ← Category.assoc, hpq.w]
    simp
  have hq : F.map q ≫ g ≫ Limits.prod.fst = F.map q ≫ g ≫ Limits.prod.snd := by
    conv_lhs => rw [← hp₁]
    conv_rhs => rw [← hp₂]
    simpa using F.map p ≫= hW.w
  refine IsPullback.mk' (Limits.prod.hom_ext (by simp) (by simpa using hq)) ?_ ?_
  · intro Z k l _ hk₂
    refine hX.hom_ext (hW.hom_ext ?_ ?_) hk₂
    · simpa only [Category.assoc, hp₁] using hk₂
    · simpa only [Category.assoc, hp₂] using hk₂
  · intro Z z t hzt
    have hz₁ : z = t ≫ g ≫ Limits.prod.fst := by
      simpa using congrArg (fun k => k ≫ Limits.prod.fst) hzt
    have hz₂ : z = t ≫ g ≫ Limits.prod.snd := by
      simpa using congrArg (fun k => k ≫ Limits.prod.snd) hzt
    obtain ⟨w, hw₁, hw₂⟩ := hW.exists_lift t t (hz₁.symm.trans hz₂)
    have hw : w ≫ F.map f = t ≫ F.map (Limits.diag U) :=
      map_prod_hom_ext F (by simpa [← F.map_comp, hf₁] using hw₁)
        (by simpa [← F.map_comp, hf₂] using hw₂)
    exact ⟨hX.lift w t hw, by rw [← Category.assoc, hX.lift_snd, hz₁], hX.lift_snd w t hw⟩

/-- **Stacks 0CB7** for an arbitrary fully faithful embedding `F` preserving fibre products
and binary products: if for every pair of `F`-represented points `α`, `β` of `G` the fibre
product `F.obj U ×_G F.obj V` is `F`-represented by an object `W` whose canonical morphism to
`U ⨯ V` has `Q`, then the diagonal of `G` has `Q` relative to `F`. -/
theorem relative_diag_of_forall_isPullback (F : C ⥤ D) [F.Full] [F.Faithful]
    [HasBinaryProducts C] [HasPullbacks C] [HasBinaryProducts D] [HasPullbacks D]
    [PreservesLimitsOfShape WalkingCospan F]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    (Q : MorphismProperty C) [Q.IsStableUnderBaseChange] {G : D}
    (h : ∀ (U V : C) (α : F.obj U ⟶ G) (β : F.obj V ⟶ G),
      ∃ (W : C) (i : F.obj W ≅ pullback α β) (f : W ⟶ U ⨯ V),
        F.map (f ≫ Limits.prod.fst) = i.hom ≫ pullback.fst α β ∧
        F.map (f ≫ Limits.prod.snd) = i.hom ≫ pullback.snd α β ∧
        Q f) :
    Q.relative F (diag G) := by
  have _ : Q.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply MorphismProperty.relative.of_exists
  intro U g
  obtain ⟨W, i, f, hf₁, hf₂, hQf⟩ := h U U (g ≫ Limits.prod.fst) (g ≫ Limits.prod.snd)
  have hpq := IsPullback.of_hasPullback f (Limits.diag U)
  exact ⟨_, _, _, isPullback_map_of_isPullback_diag F g i hf₁ hf₂ hpq,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpq hQf⟩

/-- The converse of `CategoryTheory.MorphismProperty.relative_diag_of_forall_isPullback`: if
the diagonal of `G` has `Q` relative to `F` then every pair of `F`-represented points of `G`
has a fibre product which is again `F`-represented, by an object whose canonical morphism to
the product of the two sources has `Q`. -/
theorem exists_isPullback_of_relative_diag (F : C ⥤ D)
    [HasBinaryProducts C] [HasPullbacks C] [HasBinaryProducts D] [HasPullbacks D]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    (Q : MorphismProperty C) {G : D} (hQ : Q.relative F (diag G))
    (U V : C) (α : F.obj U ⟶ G) (β : F.obj V ⟶ G) :
    ∃ (W : C) (i : F.obj W ≅ pullback α β) (f : W ⟶ U ⨯ V),
      F.map (f ≫ Limits.prod.fst) = i.hom ≫ pullback.fst α β ∧
      F.map (f ≫ Limits.prod.snd) = i.hom ≫ pullback.snd α β ∧
      Q f := by
  let e : F.obj (U ⨯ V) ≅ F.obj U ⨯ F.obj V := asIso (prodComparison F U V)
  let g : F.obj (U ⨯ V) ⟶ G ⨯ G := e.hom ≫ Limits.prod.map α β
  have hP : IsPullback (pullback.fst α β ≫ α)
      (Limits.prod.lift (pullback.fst α β) (pullback.snd α β) ≫ e.inv) (diag G) g :=
    (isPullback_diag_prodMap α β).of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp [g])
  let i : F.obj (hQ.rep.pullback g) ≅ pullback α β :=
    (hQ.rep.isPullback g).isoIsPullback G (F.obj (U ⨯ V)) hP
  have hsnd : i.hom ≫ monoPullbackToProd F α β = F.map (hQ.rep.snd g) :=
    (hQ.rep.isPullback g).isoIsPullback_hom_snd G (F.obj (U ⨯ V)) hP
  exact ⟨hQ.rep.pullback g, i, hQ.rep.snd g, by simp [← hsnd], by simp [← hsnd],
    hQ.property_snd g⟩

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CB7** for the sheafified Yoneda embedding of the big fppf site over `S`: if
every pair of scheme-valued points of an fppf sheaf `X` of `Type (u + 1)` has a fibre product
represented by an object `W` of the site whose canonical morphism to the product of the two
sources has `Q`, then the diagonal of `X` has `Q` relative to the sheafified Yoneda embedding. -/
@[stacks 0CB7 "for the sheafified Yoneda embedding, which is the one the diagonal of a formal \
algebraic space is tested against"]
theorem sheaf_diagonal (Q : MorphismProperty (BigFppfOver B S hS))
    [Q.IsStableUnderBaseChange]
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (h : ∀ (U V : BigFppfOver B S hS)
      (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
      (β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X),
      ∃ (W : BigFppfOver B S hS)
        (i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ≅ pullback α β)
        (f : W ⟶ U ⨯ V),
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (f ≫ Limits.prod.fst) =
          i.hom ≫ pullback.fst α β ∧
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (f ≫ Limits.prod.snd) =
          i.hom ≫ pullback.snd α β ∧
        Q f) :
    Q.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (diag X) := by
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let _ : (Sheaf.sheafifiedYoneda J).Full :=
    Functor.Full.of_iso (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).symm
  let _ : (Sheaf.sheafifiedYoneda J).Faithful :=
    Functor.Faithful.of_iso (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).symm
  let _ : PreservesLimitsOfShape WalkingCospan (Sheaf.sheafifiedYoneda J) :=
    preservesLimitsOfShape_of_natIso (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).symm
  let _ : PreservesLimitsOfShape (Discrete WalkingPair) (Sheaf.sheafifiedYoneda J) :=
    preservesLimitsOfShape_of_natIso (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).symm
  exact MorphismProperty.relative_diag_of_forall_isPullback _ Q h

end AlgebraicGeometry.Space

end
