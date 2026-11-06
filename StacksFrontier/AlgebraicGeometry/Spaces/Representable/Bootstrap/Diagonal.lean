module

public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapRepresentableCalculus
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineIntersections
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism

/-!
# Bootstrapping the diagonal

For a presheaf `F` on the big fppf site of a scheme `S`, the absolute diagonal
`Δ_F : F ⟶ F × F` is representable by algebraic spaces exactly when every morphism to `F`
from a scheme over `S` is, and exactly when every morphism to `F` from an algebraic space
over `S` is.

If moreover `F` is a *sheaf* and one such morphism is surjective, flat and locally of finite
presentation, then `Δ_F` is representable by *objects of the site* — by schemes over `S`, and
not merely by algebraic spaces.  The two notions are different, and the strengthening is the
content of the main result of this file.

## Main results

* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_diag_iff_forall_yoneda`:
  **Stacks 03Y2**, the equivalence of its conditions (1) and (2).
* `AlgebraicGeometry.Space.forall_yoneda_isRepresentableByAlgebraicSpaces_iff_isAlgebraicSpace`:
  **Stacks 03Y2**, the equivalence of its conditions (2) and (3).
* `AlgebraicGeometry.Space.relativelyRepresentable_diag_of_flat_presentation`: **Stacks 046K**,
  representability of the diagonal of an fppf sheaf by objects of the site, from a surjective,
  flat and locally finitely presented morphism to it from an algebraic space.
* `CategoryTheory.Limits.pullbackProdMapDiagIso`,
  `CategoryTheory.Limits.isPullback_pullbackProdMapDiag`,
  `CategoryTheory.Limits.mono_pullback_fst_prodMap_diag` and
  `CategoryTheory.Limits.pullbackProdLiftDiagIso`: the identifications of fibre products with
  the absolute diagonal on which the equivalences and the main result rest.
* `CategoryTheory.Limits.exists_isPullback_pullback_fst_pullback_fst`: the cartesian square
  that carries the descent step of Stacks 046K.

## Implementation notes

Both equivalences of Stacks 03Y2 rest on Stacks 03XY, that a fibre product of an algebraic
space with the source of a morphism representable by algebraic spaces is an algebraic space,
together with two identifications of fibre products with the absolute diagonal, proved here for
an arbitrary category with binary products and fibre products:

* `CategoryTheory.Limits.pullbackProdMapDiagIso` identifies the fibre product of `Δ_F` with
  `f × g : A × B ⟶ F × F` with the fibre product `A ×_F B`.  It gives (1) ⇒ (2), since the
  base change of a morphism `f : h_T ⟶ F` along `ξ : h_U ⟶ F` is the fibre product of `Δ_F`
  with the morphism `h_U × h_T ⟶ F × F` built from `ξ` and `f`, and `h_U × h_T` is an
  algebraic space because the Yoneda embedding preserves binary products.
* `CategoryTheory.Limits.pullbackProdLiftDiagIso` identifies the fibre product of `Δ_F` with
  a morphism `⟨a, b⟩ : T ⟶ F × F` — the locus in `T` on which `a` and `b` agree — with the
  fibre product of `Δ_T` and the canonical morphism `T ×_F T ⟶ T × T`.  It gives (2) ⇒ (1):
  the first factor is an algebraic space by hypothesis, the absolute diagonal of a
  representable presheaf is representable by algebraic spaces because each of its base
  changes is representable, and Stacks 03XY applies.

For (3) ⇒ (2) a scheme over `S` is an algebraic space over `S`, and (2) ⇒ (3) is Stacks
03XY again, after exchanging the two factors of the fibre product.

*Stacks 046K.* The source reduces at once to a scheme atlas `h_U ⟶ X` of the presenting
algebraic space and works with `U ×_S U`; no step of the argument needs `U` to be a scheme, so
the proof here keeps the given algebraic space `X` and works with the presheaf product
`X ⨯ X`, which is `X ×_S X` because the terminal object of the site is `S`.  This removes the
need to convert the surjectivity and étaleness of a chart, which the library carries in the
relative form of Stacks 025V, into the properties of Stacks 03XZ that the argument consumes.

The kernel pair `X ×_F X` appears as the fibre product of `Δ_F` with `f × f`, by
`CategoryTheory.Limits.isPullback_pullbackProdMapDiag`.  In that presentation its projection to
`X ⨯ X` is visibly a base change of `Δ_F`, which is what puts it on the top row of the square
Stacks 046J consumes, and visibly a monomorphism, by
`CategoryTheory.Limits.mono_pullback_fst_prodMap_diag`.

Stacks 046K needs Stacks 046J, which the library proves with exactly the source's hypotheses:
the bottom row of the square is representable by effective fppf descent of schemes, and the two
properties descend by Stacks 0421 and Stacks 0427.  So Stacks 046K is unconditional, and in
particular does not pass through the bootstrap theorem Stacks 04S6.

## References

* [Stacks Project, Tag 03Y2](https://stacks.math.columbia.edu/tag/03Y2)
* [Stacks Project, Tag 046F](https://stacks.math.columbia.edu/tag/046F)
* [Stacks Project, Tag 046H](https://stacks.math.columbia.edu/tag/046H)
* [Stacks Project, Tag 046J](https://stacks.math.columbia.edu/tag/046J)
* [Stacks Project, Tag 046K](https://stacks.math.columbia.edu/tag/046K)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] [HasPullbacks C]

/-- A morphism `p : T ⟶ F ⨯ F` and its fibre product with the diagonal: the first projection of
the fibre product followed by `p ≫ prod.fst` is the second projection. -/
private theorem pullback_fst_comp_prod_fst_diag {T F : C} (p : T ⟶ F ⨯ F) :
    pullback.fst p (diag F) ≫ p ≫ prod.fst = pullback.snd p (diag F) := by
  rw [← Category.assoc, pullback.condition]
  simp

/-- A morphism `p : T ⟶ F ⨯ F` and its fibre product with the diagonal: the first projection of
the fibre product followed by `p ≫ prod.snd` is the second projection. -/
private theorem pullback_fst_comp_prod_snd_diag {T F : C} (p : T ⟶ F ⨯ F) :
    pullback.fst p (diag F) ≫ p ≫ prod.snd = pullback.snd p (diag F) := by
  rw [← Category.assoc, pullback.condition]
  simp

/-- The fibre product of the absolute diagonal of `F` with the product `f × g` of two
morphisms `f : A ⟶ F` and `g : B ⟶ F` is the fibre product `A ×_F B`. -/
noncomputable def pullbackProdMapDiagIso {A B F : C} (f : A ⟶ F) (g : B ⟶ F) :
    pullback (prod.map f g) (diag F) ≅ pullback f g := by
  have hc := pullback.condition (f := prod.map f g) (g := diag F)
  have hfst : pullback.fst (prod.map f g) (diag F) ≫ prod.fst ≫ f =
      pullback.snd (prod.map f g) (diag F) := by
    simpa using congrArg (fun k => k ≫ (prod.fst : F ⨯ F ⟶ F)) hc
  have hsnd : pullback.fst (prod.map f g) (diag F) ≫ prod.snd ≫ g =
      pullback.snd (prod.map f g) (diag F) := by
    simpa using congrArg (fun k => k ≫ (prod.snd : F ⨯ F ⟶ F)) hc
  exact
    { hom := pullback.lift (pullback.fst (prod.map f g) (diag F) ≫ prod.fst)
        (pullback.fst (prod.map f g) (diag F) ≫ prod.snd)
        (by simp only [Category.assoc]; rw [hfst, hsnd])
      inv := pullback.lift (prod.lift (pullback.fst f g) (pullback.snd f g))
        (pullback.fst f g ≫ f) (prod.hom_ext (by simp) (by simp [pullback.condition]))
      hom_inv_id := pullback.hom_ext
        (prod.hom_ext (by simp [pullback.lift_fst])
          (by simp [pullback.lift_fst_assoc, pullback.lift_snd]))
        (by simp [pullback.lift_snd, pullback.lift_fst_assoc, hfst])
      inv_hom_id := pullback.hom_ext
        (by simp [pullback.lift_fst, pullback.lift_fst_assoc])
        (by simp [pullback.lift_snd, pullback.lift_fst_assoc]) }

/-- The isomorphism `pullbackProdMapDiagIso f g` followed by the first projection of `A ×_F B`
is the first component of the projection to `A ⨯ B`. -/
@[simp]
lemma pullbackProdMapDiagIso_hom_fst {A B F : C} (f : A ⟶ F) (g : B ⟶ F) :
    (pullbackProdMapDiagIso f g).hom ≫ pullback.fst f g =
      pullback.fst (prod.map f g) (diag F) ≫ prod.fst := by
  simp only [pullbackProdMapDiagIso]
  rw [pullback.lift_fst]

/-- The isomorphism `pullbackProdMapDiagIso f g` followed by the second projection of `A ×_F B`
is the second component of the projection to `A ⨯ B`. -/
@[simp]
lemma pullbackProdMapDiagIso_hom_snd {A B F : C} (f : A ⟶ F) (g : B ⟶ F) :
    (pullbackProdMapDiagIso f g).hom ≫ pullback.snd f g =
      pullback.fst (prod.map f g) (diag F) ≫ prod.snd := by
  simp only [pullbackProdMapDiagIso]
  rw [pullback.lift_snd]

/-- The fibre product of the absolute diagonal of `F` with `f × g` is a fibre product of `f`
and `g`, with the two components of its projection to `A × B` as the two projections. -/
theorem isPullback_pullbackProdMapDiag {A B F : C} (f : A ⟶ F) (g : B ⟶ F) :
    IsPullback (pullback.fst (prod.map f g) (diag F) ≫ prod.fst)
      (pullback.fst (prod.map f g) (diag F) ≫ prod.snd) f g := by
  have hfst : pullback.fst (prod.map f g) (diag F) ≫ prod.fst ≫ f =
      pullback.snd (prod.map f g) (diag F) := by
    simpa using pullback_fst_comp_prod_fst_diag (prod.map f g)
  have hsnd : pullback.fst (prod.map f g) (diag F) ≫ prod.snd ≫ g =
      pullback.snd (prod.map f g) (diag F) := by
    simpa using pullback_fst_comp_prod_snd_diag (prod.map f g)
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackProdMapDiagIso f g) (by simp) (by simp)
  simp only [Category.assoc]
  rw [hfst, hsnd]

/-- The first projection of the fibre product of `f × g` with the absolute diagonal of `F` is a
monomorphism: the second projection is recovered from it, because the absolute diagonal is
split by either projection of the product. -/
theorem mono_pullback_fst_prodMap_diag {A B F : C} (f : A ⟶ F) (g : B ⟶ F) :
    Mono (pullback.fst (prod.map f g) (diag F)) := by
  have hfst : pullback.fst (prod.map f g) (diag F) ≫ prod.fst ≫ f =
      pullback.snd (prod.map f g) (diag F) := by
    simpa using pullback_fst_comp_prod_fst_diag (prod.map f g)
  refine ⟨fun {Z} u v huv => pullback.hom_ext huv ?_⟩
  rw [← hfst]
  simp only [← Category.assoc, huv]

omit [HasBinaryProducts C] in
/-- For `k : X ⟶ Y`, `d : F ⟶ Y` and `η : T ⟶ Y`, the first projection of
`(T ×_Y X) ×_X (X ×_Y F)` to `T ×_Y X` is the top row of a cartesian square whose bottom row is
the projection `T ×_Y F ⟶ T` and whose right-hand column is the projection `T ×_Y X ⟶ T`.

Both fibre products are `T ×_Y X ×_Y F`.  The square is obtained by pasting the two defining
squares of the left-hand one vertically and cancelling the defining square of `T ×_Y F`. -/
theorem exists_isPullback_pullback_fst_pullback_fst {X Y F T : C}
    (k : X ⟶ Y) (d : F ⟶ Y) (η : T ⟶ Y) :
    ∃ m : pullback (pullback.snd η k) (pullback.fst k d) ⟶ pullback η d,
      IsPullback (pullback.fst (pullback.snd η k) (pullback.fst k d)) m
        (pullback.fst η k) (pullback.fst η d) := by
  have hpaste : IsPullback (pullback.fst (pullback.snd η k) (pullback.fst k d))
      (pullback.snd (pullback.snd η k) (pullback.fst k d) ≫ pullback.snd k d)
      (pullback.fst η k ≫ η) d := by
    rw [pullback.condition (f := η) (g := k)]
    exact (IsPullback.of_hasPullback (pullback.snd η k) (pullback.fst k d)).paste_vert
      (IsPullback.of_hasPullback k d)
  refine ⟨(IsPullback.of_hasPullback η d).lift
    (pullback.fst (pullback.snd η k) (pullback.fst k d) ≫ pullback.fst η k)
    (pullback.snd (pullback.snd η k) (pullback.fst k d) ≫ pullback.snd k d)
    (by rw [Category.assoc]; exact hpaste.w), ?_⟩
  refine IsPullback.of_bot ?_
    ((IsPullback.of_hasPullback η d).lift_fst _ _ _).symm (IsPullback.of_hasPullback η d)
  rw [(IsPullback.of_hasPullback η d).lift_snd]
  exact hpaste

/-- The locus in `T` on which two morphisms `a, b : T ⟶ F` agree, presented as the fibre
product of the absolute diagonal of `F` with `⟨a, b⟩ : T ⟶ F × F`, is the fibre product of
the absolute diagonal of `T` with the canonical morphism `T ×_F T ⟶ T × T`. -/
noncomputable def pullbackProdLiftDiagIso {T F : C} (a b : T ⟶ F) :
    pullback (prod.lift a b) (diag F) ≅
      pullback (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T) := by
  have hc := pullback.condition (f := prod.lift a b) (g := diag F)
  have hla : pullback.fst (prod.lift a b) (diag F) ≫ a =
      pullback.snd (prod.lift a b) (diag F) := by
    simpa using congrArg (fun k => k ≫ (prod.fst : F ⨯ F ⟶ F)) hc
  have hlb : pullback.fst (prod.lift a b) (diag F) ≫ b =
      pullback.snd (prod.lift a b) (diag F) := by
    simpa using congrArg (fun k => k ≫ (prod.snd : F ⨯ F ⟶ F)) hc
  have hc' := pullback.condition
    (f := prod.lift (pullback.fst a b) (pullback.snd a b)) (g := diag T)
  have hr₁ : pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T) ≫
      pullback.fst a b =
      pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T) := by
    simpa using congrArg (fun k => k ≫ (prod.fst : T ⨯ T ⟶ T)) hc'
  have hr₂ : pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T) ≫
      pullback.snd a b =
      pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T) := by
    simpa using congrArg (fun k => k ≫ (prod.snd : T ⨯ T ⟶ T)) hc'
  have hrab : pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T) ≫ a =
      pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T) ≫ b :=
    calc
      _ = (pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T) ≫
            pullback.fst a b) ≫ a := by rw [hr₁]
      _ = (pullback.fst (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T) ≫
            pullback.snd a b) ≫ b := by
          rw [Category.assoc, Category.assoc, pullback.condition]
      _ = _ := by rw [hr₂]
  exact
    { hom := pullback.lift
        (pullback.lift (pullback.fst (prod.lift a b) (diag F))
          (pullback.fst (prod.lift a b) (diag F)) (hla.trans hlb.symm))
        (pullback.fst (prod.lift a b) (diag F))
        (prod.hom_ext (by simp [pullback.lift_fst]) (by simp [pullback.lift_snd]))
      inv := pullback.lift
        (pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T))
        (pullback.snd (prod.lift (pullback.fst a b) (pullback.snd a b)) (diag T) ≫ a)
        (prod.hom_ext (by simp) (by simp [hrab]))
      hom_inv_id := pullback.hom_ext
        (by simp [pullback.lift_fst, pullback.lift_snd])
        (by simp [pullback.lift_snd, pullback.lift_snd_assoc, hla])
      inv_hom_id := pullback.hom_ext
        (pullback.hom_ext
          (by simp [pullback.lift_fst, hr₁])
          (by simp [pullback.lift_snd, pullback.lift_fst, hr₂]))
        (by simp [pullback.lift_snd, pullback.lift_fst]) }

end CategoryTheory.Limits

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_BootstrapDiagonal :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_BootstrapDiagonal
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_BootstrapDiagonal B S hS).has_limit _

/-- A representable presheaf on the big fppf site of `S` is an algebraic space over `S`. -/
theorem isAlgebraicSpace_of_isRepresentable (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    [P.IsRepresentable] : IsAlgebraicSpace B S hS P :=
  (isAlgebraicSpace_yoneda B S hS P.reprX).of_iso (Functor.reprW P)

/-- A binary product of two representable presheaves on the big fppf site of `S` is an
algebraic space over `S`: the site has binary products and the Yoneda embedding preserves
them. -/
theorem isAlgebraicSpace_prod_yoneda (U T : BigFppfOver B S hS) :
    IsAlgebraicSpace B S hS (yoneda.obj U ⨯ yoneda.obj T) :=
  (isAlgebraicSpace_yoneda B S hS (U ⨯ T)).of_iso (PreservesLimitPair.iso yoneda U T)

/-- The absolute diagonal of a representable presheaf on the big fppf site of `S` is
representable by algebraic spaces: each of its base changes is representable, because the
diagonal of an algebraic space is. -/
theorem isRepresentableByAlgebraicSpaces_diag_yoneda (T : BigFppfOver B S hS) :
    IsRepresentableByAlgebraicSpaces B S hS (diag (yoneda.obj T)) := by
  intro U ξ
  have hrepr : (pullback ξ (diag (yoneda.obj T))).IsRepresentable := by
    simpa using (yoneda_relativelyRepresentable_iff_pullback_representable
      (diag (yoneda.obj T))).mp
      (isAlgebraicSpace_yoneda B S hS T).diagonal_representable U (yonedaEquiv ξ)
  exact isAlgebraicSpace_of_isRepresentable B S hS _

/-- **Stacks 03Y2, conditions (1) and (2).** The absolute diagonal of a presheaf on the big
fppf site of `S` is representable by algebraic spaces exactly when every morphism to that
presheaf from a scheme over `S` is representable by algebraic spaces. -/
@[stacks 03Y2 "conditions (1) and (2)"]
theorem isRepresentableByAlgebraicSpaces_diag_iff_forall_yoneda
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    IsRepresentableByAlgebraicSpaces B S hS (diag F) ↔
      ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ F),
        IsRepresentableByAlgebraicSpaces B S hS f := by
  refine ⟨fun h T f U ξ => ?_, fun h T η => ?_⟩
  · exact (isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS (diag F)
      (prod.map ξ f) h (isAlgebraicSpace_prod_yoneda B S hS U T)).of_iso
      (pullbackProdMapDiagIso ξ f)
  · have hη : prod.lift (η ≫ prod.fst) (η ≫ prod.snd) = η := by apply prod.hom_ext <;> simp
    have key := isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS
      (diag (yoneda.obj T))
      (prod.lift (pullback.fst (η ≫ prod.fst) (η ≫ prod.snd))
        (pullback.snd (η ≫ prod.fst) (η ≫ prod.snd)))
      (isRepresentableByAlgebraicSpaces_diag_yoneda B S hS T)
      (h T (η ≫ prod.snd) T (η ≫ prod.fst))
    exact key.of_iso ((pullbackProdLiftDiagIso (η ≫ prod.fst) (η ≫ prod.snd)).symm ≪≫
      pullback.congrHom hη rfl)

/-- **Stacks 03Y2, conditions (2) and (3).** Representability by algebraic spaces of every
morphism to a presheaf on the big fppf site of `S` from a scheme over `S` is equivalent to
representability by algebraic spaces of every morphism to it from an algebraic space over
`S`. -/
@[stacks 03Y2 "conditions (2) and (3)"]
theorem forall_yoneda_isRepresentableByAlgebraicSpaces_iff_isAlgebraicSpace
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ F),
        IsRepresentableByAlgebraicSpaces B S hS f) ↔
      ∀ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS X →
        ∀ (f : X ⟶ F), IsRepresentableByAlgebraicSpaces B S hS f := by
  constructor
  · intro h X hX f T ξ
    exact (isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS ξ f
      (h T ξ) hX).of_iso (pullbackSymmetry f ξ)
  · exact fun h T f => h (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) f

/-! ### Representability of the diagonal from a flat presentation -/

/-- A morphism of algebraic spaces over `S` with a property stable under base change has that
property after every base change along a scheme-valued point of its target, which is what
`AlgebraicGeometry.Space.HasProperty` asks of it. -/
private theorem hasProperty_of_isAlgebraicSpace
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (φ : X ⟶ Y)
    (hφ : P (ObjectProperty.homMk φ :
      (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Y, hY⟩ : AlgebraicSpaces B S hS))) :
    HasProperty B S hS P φ
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS hX hY φ) := fun U ξ =>
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk ξ : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk φ :
        (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).flip hφ

/-- The kernel pair of a morphism `f : X ⟶ F` representable by algebraic spaces and locally of
finite presentation, presented as the fibre product of `Δ_F` with `f × f`, is separated and
locally quasi-finite over `X ⨯ X`.

Its projection to `X ⨯ X` is a monomorphism, hence separated by **Stacks 042N**.  Composed with
the first projection of `X ⨯ X` it is the first projection of `X ×_F X`, which is locally of
finite presentation by **Stacks 046F** and so locally of finite type by **Stacks 0464**; hence
the projection itself is locally of finite type by **Stacks 0462**, and **Stacks 0463** makes it
locally quasi-finite. -/
private theorem isSeparated_isLocallyQuasiFinite_kernelPair
    [(locallyOfFinitePresentationProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, v} B S hS)]
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ F)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hfLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) f hf) :
    IsSeparated B S hS (pullback.fst (prod.map f f) (diag F)) ∧
      IsLocallyQuasiFinite B S hS (pullback.fst (prod.map f f) (diag F)) := by
  have hsq := isPullback_pullbackProdMapDiag f f
  have hmono := mono_pullback_fst_prodMap_diag f f
  have hR : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS f f hf hX
  have hXX : IsAlgebraicSpace B S hS (X ⨯ X) := isAlgebraicSpace_prod B S hS hX hX
  have hW : IsAlgebraicSpace B S hS (pullback (prod.map f f) (diag F)) :=
    hR.of_iso hsq.isoPullback.symm
  have hlft : IsLocallyOfFiniteType B S hS (pullback.fst f f) :=
    isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (hasProperty_pullback_fst_of_isAlgebraicSpace.{v, u} B S hS
        (locallyOfFinitePresentationProperty B S hS) hX f f hf hfLfp)
  have hcomp : IsLocallyOfFiniteType B S hS
      (pullback.fst (prod.map f f) (diag F) ≫ (prod.fst : X ⨯ X ⟶ X)) := by
    let Pl : MorphismProperty (AlgebraicSpaces B S hS) :=
      fun _ _ φ => IsLocallyOfFiniteType B S hS φ.hom
    have : Pl.IsStableUnderBaseChange := isLocallyOfFiniteType_isStableUnderBaseChange B S hS
    have : Pl.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
    have heq : (ObjectProperty.homMk (pullback.fst (prod.map f f) (diag F) ≫ prod.fst) :
        (⟨pullback (prod.map f f) (diag F), hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) =
        (ObjectProperty.isoMk (fun Z => IsAlgebraicSpace B S hS Z)
          (X := ⟨pullback (prod.map f f) (diag F), hW⟩) (Y := ⟨pullback f f, hR⟩)
          hsq.isoPullback).hom ≫ ObjectProperty.homMk (pullback.fst f f) :=
      ObjectProperty.hom_ext _ hsq.isoPullback_hom_fst.symm
    show Pl (ObjectProperty.homMk (pullback.fst (prod.map f f) (diag F) ≫ prod.fst) :
      (⟨pullback (prod.map f f) (diag F), hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
    rw [heq]
    exact MorphismProperty.RespectsIso.precomp Pl _ _ hlft
  have hft : IsLocallyOfFiniteType B S hS (pullback.fst (prod.map f f) (diag F)) :=
    isLocallyOfFiniteType_of_comp B S hS hW hXX hX _ prod.fst hcomp
  exact ⟨isSeparated_of_mono B S hS _ hmono,
    isLocallyQuasiFinite_of_mono B S hS hW hXX _ hmono hft⟩

/-- **Stacks 046K.** Let `F` be a sheaf on the big fppf site of a scheme `S` which admits a
morphism `f : X ⟶ F` from an algebraic space over `S` that is representable by algebraic
spaces, surjective, flat and locally of finite presentation.  Then the absolute diagonal
`Δ_F : F ⟶ F × F` is representable *by objects of the site*, that is, every fibre product of
`Δ_F` with a scheme-valued point of `F × F` is again a scheme over `S` — not merely an
algebraic space, as **Stacks 03Y2** would give.

Let `d = Δ_F` and let `k = f × f : X ⨯ X ⟶ F × F`, which is representable by algebraic spaces,
surjective, flat and locally of finite presentation by **Stacks 046D** and **Stacks 046H**.  The
fibre product `W = (X ⨯ X) ×_{F × F} F` is the kernel pair `X ×_F X` of `f`, so its projection
to `X ⨯ X` is representable by algebraic spaces, separated and locally quasi-finite.  Given a
scheme-valued point `η : h_T ⟶ F × F`, the base change `T' = h_T ×_{F × F} (X ⨯ X) ⟶ h_T` of
`k` inherits the three properties by **Stacks 046F**, and `T' ×_{X ⨯ X} W ⟶ T'` inherits
separatedness and local quasi-finiteness from the projection of `W`; that fibre product is at
the same time the base change of `Z = h_T ×_{F × F} F ⟶ h_T` along `T' ⟶ h_T`.  **Stacks 046J**
applied to the resulting cartesian square makes `Z ⟶ h_T` representable by objects of the site,
and `Z` is the fibre product of `Δ_F` with `η`. -/
@[stacks 046K]
theorem relativelyRepresentable_diag_of_flat_presentation
    {F X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ F)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (hfSurj : HasProperty B S hS (surjectiveMorphismProperty B S hS) f hf)
    (hfFlat : HasProperty B S hS (flatProperty B S hS) f hf)
    (hfLfp : HasProperty B S hS (locallyOfFinitePresentationProperty B S hS) f hf) :
    yoneda.relativelyRepresentable (diag F) := by
  classical
  have : (surjectiveMorphismProperty B S hS).IsStableUnderComposition :=
    ⟨fun _ _ hu hv => isSurjective_comp B S hS hu hv⟩
  have : (flatProperty B S hS).IsStableUnderComposition :=
    { comp_mem := fun {A₁ A₂ A₃} u v hu hv =>
        isFlat_comp B S hS A₁.property A₂.property A₃.property u.hom v.hom hu hv }
  have : (locallyOfFinitePresentationProperty B S hS).IsStableUnderComposition :=
    { comp_mem := fun {A₁ A₂ A₃} u v hu hv =>
        isLocallyOfFinitePresentation_comp B S hS A₁.property A₂.property A₃.property
          u.hom v.hom hu hv }
  have : (flatProperty B S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Topology.fpqc.precoverage.{u, u + 1} B S hS)
      (fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
  have : (surjectiveMorphismProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (flatProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (locallyOfFinitePresentationProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (separatedProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (locallyQuasiFiniteProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- The chart `f × f : X ⨯ X ⟶ F × F` and its properties, by Stacks 046D and Stacks 046H.
  have hXX : IsAlgebraicSpace B S hS (X ⨯ X) := isAlgebraicSpace_prod B S hS hX hX
  have hkRep : IsRepresentableByAlgebraicSpaces B S hS (prod.map f f) :=
    isRepresentableByAlgebraicSpaces_prod_map B S hS f f hf hf
  have hkSurj := hasProperty_prod_map.{u, u + 1} B S hS (surjectiveMorphismProperty B S hS)
    f f hf hf hfSurj hfSurj
  have hkFlat := hasProperty_prod_map.{u, u + 1} B S hS (flatProperty B S hS)
    f f hf hf hfFlat hfFlat
  have hkLfp := hasProperty_prod_map.{u, u + 1} B S hS (locallyOfFinitePresentationProperty B S hS)
    f f hf hf hfLfp hfLfp
  -- The kernel pair of `f`, as the base change of `Δ_F` along the chart.
  have hR : IsAlgebraicSpace B S hS (pullback f f) :=
    isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces B S hS f f hf hX
  have hW : IsAlgebraicSpace B S hS (pullback (prod.map f f) (diag F)) :=
    hR.of_iso (isPullback_pullbackProdMapDiag f f).isoPullback.symm
  obtain ⟨hWSep, hWLqf⟩ :=
    isSeparated_isLocallyQuasiFinite_kernelPair.{u + 1, u} B S hS hX f hf hfLfp
  have hWSep' := hasProperty_of_isAlgebraicSpace B S hS (separatedProperty B S hS) hW hXX
    (pullback.fst (prod.map f f) (diag F)) hWSep
  have hWLqf' := hasProperty_of_isAlgebraicSpace B S hS (locallyQuasiFiniteProperty B S hS)
    hW hXX (pullback.fst (prod.map f f) (diag F)) hWLqf
  -- Fix a scheme-valued point of `F × F`.
  intro T η
  have hTsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj T) :=
    (isAlgebraicSpace_yoneda B S hS T).isSheaf
  have hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback η (diag F)) :=
    Presheaf.isSheaf_pullback _ η (diag F) hTsheaf hF (isSheaf_prod_self B S hS hF)
  -- The base change of the chart along `η`, by Stacks 046F.
  have hηsq : IsPullback (pullback.snd η (prod.map f f)) (pullback.fst η (prod.map f f))
      (prod.map f f) η := (IsPullback.of_hasPullback η (prod.map f f)).flip
  have hgRep : IsRepresentableByAlgebraicSpaces B S hS (pullback.fst η (prod.map f f)) :=
    IsRepresentableByAlgebraicSpaces.of_isPullback hηsq hkRep
  -- The base change of the kernel pair along the chart of `T'`, by Stacks 046F again.
  have hasq : IsPullback
      (pullback.snd (pullback.snd η (prod.map f f)) (pullback.fst (prod.map f f) (diag F)))
      (pullback.fst (pullback.snd η (prod.map f f)) (pullback.fst (prod.map f f) (diag F)))
      (pullback.fst (prod.map f f) (diag F)) (pullback.snd η (prod.map f f)) :=
    (IsPullback.of_hasPullback (pullback.snd η (prod.map f f))
      (pullback.fst (prod.map f f) (diag F))).flip
  have haRep := IsRepresentableByAlgebraicSpaces.of_isPullback hasq
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS hW hXX _)
  -- Stacks 046J, applied to the cartesian square the two base changes sit in.
  obtain ⟨m, hsquare⟩ :=
    exists_isPullback_pullback_fst_pullback_fst (prod.map f f) (diag F) η
  obtain ⟨-, hbRep, -, -⟩ :=
    relativelyRepresentable_separated_locallyQuasiFinite_of_isPullback B S hS
      (pullback.fst (pullback.snd η (prod.map f f)) (pullback.fst (prod.map f f) (diag F)))
      m (pullback.fst η (prod.map f f)) (pullback.fst η (diag F)) hsquare hZ hTsheaf
      hgRep (HasProperty.of_isPullback hηsq hkRep hkSurj)
      (HasProperty.of_isPullback hηsq hkRep hkFlat)
      (HasProperty.of_isPullback hηsq hkRep hkLfp) haRep
      (HasProperty.of_isPullback hasq _ hWSep') (HasProperty.of_isPullback hasq _ hWLqf')
  -- The fibre product of `Δ_F` with `η` is therefore represented by an object of the site.
  obtain ⟨V, s, p, hpb⟩ := hbRep (𝟙 (yoneda.obj T))
  exact ⟨V, s, p ≫ pullback.snd η (diag F),
    by simpa using hpb.paste_horiz (IsPullback.of_hasPullback η (diag F)).flip⟩

end AlgebraicGeometry.Space

end
