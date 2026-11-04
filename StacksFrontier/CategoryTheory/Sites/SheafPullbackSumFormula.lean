module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCoproduct
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.SheafFanOfSections

/-!
# Lower shriek restricted to another site is a coproduct

Let `(C_n, J_n)`, `(C_m, J_m)` and `(E, L)` be sites and let `v_n : C_n ⥤ E`, `v_m : C_m ⥤ E` be
functors. Assume `v_n` is continuous, so that it has a lower-shriek functor
`g_{n!} : Sh(C_n) ⥤ Sh(E)` left adjoint to restriction along `v_n`, and assume `v_m` is
continuous and cocontinuous, so that restriction along `v_m` is itself a left adjoint. This file
gives two criteria for the composite `g_{n!}` followed by restriction along `v_m` to be a
coproduct of functors `Sh(C_n) ⥤ Sh(C_m)` indexed by a family of comparison transformations
between `v_n` and `v_m`.

The two criteria are not formal duals of one another; they are the two halves one gets depending
on which of the two Kan extensions involved decomposes.

* The **ran criterion** takes a family of functors `t i : C_n ⥤ C_m`, each continuous, together
  with transformations `τ i : t i ⋙ v_m ⟶ v_n`, and asks that the right Kan extension along
  `v_m.op`, evaluated at any object in the image of `v_n`, be the product of the values at the
  `t i`. The composite is then the coproduct of the lower-shriek functors of the `t i`. The proof
  passes the product formula for the right adjoints across all the adjunctions at once, using
  `CategoryTheory.Adjunction.coproductIsoOfIsLimitFan`; no sheafification is manipulated
  anywhere.
* The **lan criterion** takes a family of functors `t i : C_m ⥤ C_n` together with
  transformations `σ i : v_m ⟶ t i ⋙ v_n`, and asks that the left Kan extension along `v_n.op`,
  evaluated at any object in the image of `v_m`, be the coproduct of the values at the `t i`. The
  composite is then the coproduct of the sheaf pullbacks along the `t i`. Here the formula is
  established on presheaves and then pushed through sheafification, which is possible because
  sheafification is a left adjoint and because it commutes with restriction along the continuous
  and cocontinuous `v_m`.

## Main results

* `CategoryTheory.Limits.isColimitCofanOfEvaluation`: a cofan in a functor category is a colimit
  as soon as it is one at every object.
* `CategoryTheory.Limits.isColimitCofanMapOfPreserves`: a functor preserving coproducts of a
  given shape takes a colimit cofan to a colimit cofan.
* `CategoryTheory.Functor.sheafificationCompPushforwardContinuousIso`: for a continuous and
  cocontinuous functor, sheafifying and then restricting agrees with restricting presheaves and
  then sheafifying.
* `CategoryTheory.Functor.sheafPullbackCompPushforwardIsoCoproductOfRan`: the ran criterion.
* `CategoryTheory.Functor.sheafPullbackCompPushforwardIsoCoproductOfLan`: the lan criterion.

## Implementation notes

The hypotheses of both criteria are phrased as `CategoryTheory.Limits.IsLimit` of an explicit
`Fan.mk`, resp. `CategoryTheory.Limits.IsColimit` of an explicit `Cofan.mk`, whose legs are
written out in terms of the Kan extension unit or counit and the given comparison
transformations. That is the shape in which such a decomposition arises from a comma category
with a distinguished object in each piece, and it avoids having to build and then discard an
isomorphism with a chosen (co)product.

The comparison transformations on presheaves are assembled by whiskering rather than by giving
components and proving naturality: `ranRestrictComparison` whiskers the image of `τ i` under
`CategoryTheory.Functor.whiskeringLeft` into the right Kan extension and then postcomposes the
Kan extension counit, and `lanRestrictComparison` is the same construction with the unit first.
Their components are then definitionally the legs appearing in the two hypotheses, which is what
makes the two criteria usable by `exact`.

Colimits in a functor category are computed pointwise, but the two diagrams
`Discrete.functor f ⋙ G` and `Discrete.functor fun i => G.obj (f i)` are only isomorphic and not
definitionally equal — they differ on the morphisms of the discrete index category — so the two
cofan lemmas go through `CategoryTheory.Limits.IsColimit.equivOfNatIsoOfIso` rather than
`IsColimit.ofIsoColimit`.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

variable {I : Type w} {K : Type u₁} [Category.{v₁} K] {A : Type u₂} [Category.{v₂} A]

/-- A cofan in a functor category is a colimit as soon as it is one at every object of the
source, because colimits in a functor category are computed pointwise. -/
noncomputable def isColimitCofanOfEvaluation {f : I → (K ⥤ A)} {P : K ⥤ A} (p : ∀ i, f i ⟶ P)
    (h : ∀ X : K, IsColimit (Cofan.mk (P.obj X) fun i => (p i).app X)) :
    IsColimit (Cofan.mk P p) := by
  refine evaluationJointlyReflectsColimits _ fun X => ?_
  refine (IsColimit.equivOfNatIsoOfIso
    ((Discrete.natIso fun _ => Iso.refl _ :
        (Discrete.functor fun i => (f i).obj X) ≅ Discrete.functor f ⋙ (evaluation K A).obj X))
    (Cofan.mk (P.obj X) fun i => (p i).app X)
    (((evaluation K A).obj X).mapCocone (Cofan.mk P p))
    (Cocone.ext (Iso.refl _) ?_)) (h X)
  intro j
  obtain ⟨j⟩ := j
  simp

variable {B : Type u₁} [Category.{v₁} B]

/-- A functor preserving coproducts of shape `I` takes a colimit cofan to a colimit cofan. -/
noncomputable def isColimitCofanMapOfPreserves (G : A ⥤ B)
    [PreservesColimitsOfShape (Discrete I) G] {f : I → A} {P : A} (p : ∀ i, f i ⟶ P)
    (h : IsColimit (Cofan.mk P p)) :
    IsColimit (Cofan.mk (G.obj P) fun i => G.map (p i)) := by
  refine (IsColimit.equivOfNatIsoOfIso
    ((Discrete.natIso fun _ => Iso.refl _ :
        Discrete.functor f ⋙ G ≅ Discrete.functor fun i => G.obj (f i)))
    (G.mapCocone (Cofan.mk P p)) (Cofan.mk (G.obj P) fun i => G.map (p i))
    (Cocone.ext (Iso.refl _) ?_)) (isColimitOfPreserves G h)
  intro j
  obtain ⟨j⟩ := j
  simp

end CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w v₁ u₁ v₂ u₂ v₃ u₃ v u

section Sheafification

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (w : C ⥤ D) (A : Type u) [Category.{v} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [w.IsContinuous J K] [w.IsCocontinuous J K] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ F : Cᵒᵖ ⥤ A, w.op.HasPointwiseRightKanExtension F]

/-- Sheafifying a presheaf on `D` and then restricting along a continuous and cocontinuous
`w : C ⥤ D` is the same as restricting the presheaf along `w.op` and then sheafifying.

Both composites are left adjoints to `w.sheafPushforwardCocontinuous A J K` followed by the
inclusion of sheaves into presheaves: on the left because sheafification is left adjoint to that
inclusion and restriction of sheaves is left adjoint to the cocontinuous pushforward, and on the
right because restriction of presheaves is left adjoint to the right Kan extension, whose
restriction to sheaves is that same pushforward. -/
noncomputable def sheafificationCompPushforwardContinuousIso :
    presheafToSheaf K A ⋙ w.sheafPushforwardContinuous A J K ≅
      (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj w.op ⋙ presheafToSheaf J A :=
  Adjunction.leftAdjointUniq
    ((sheafificationAdjunction K A).comp (w.sheafAdjunctionCocontinuous A J K))
    ((w.op.ranAdjunction A).comp (sheafificationAdjunction J A))

end Sheafification

variable {I : Type w} {Cn : Type u₁} [Category.{v₁} Cn] {Cm : Type u₂} [Category.{v₂} Cm]
  {E : Type u₃} [Category.{v₃} E]
  (A : Type u) [Category.{v} A]
  (Jn : GrothendieckTopology Cn) (Jm : GrothendieckTopology Cm) (L : GrothendieckTopology E)

section Ran

/-- The comparison of presheaves attached to a transformation `τ i : t i ⋙ v_m ⟶ v_n`: restrict
the right Kan extension along `v_m.op` to `C_n` along `v_n.op`, transport along `τ i`, and apply
the Kan extension counit. Its component over an object `U` is the leg, at `τ i` applied to `U`,
of the pointwise limit cone computing the Kan extension at `v_n U`. -/
noncomputable def ranRestrictComparison (vn : Cn ⥤ E) (vm : Cm ⥤ E) (t : I → (Cn ⥤ Cm))
    (τ : ∀ i, t i ⋙ vm ⟶ vn) [∀ F : Cmᵒᵖ ⥤ A, vm.op.HasPointwiseRightKanExtension F] (i : I) :
    vm.op.ran ⋙ (whiskeringLeft Cnᵒᵖ Eᵒᵖ A).obj vn.op ⟶
      (whiskeringLeft Cnᵒᵖ Cmᵒᵖ A).obj (t i).op :=
  whiskerLeft vm.op.ran ((whiskeringLeft Cnᵒᵖ Eᵒᵖ A).map (NatTrans.op (τ i))) ≫
    whiskerRight vm.op.ranCounit ((whiskeringLeft Cnᵒᵖ Cmᵒᵖ A).obj (t i).op)

variable (vn : Cn ⥤ E) (vm : Cm ⥤ E) (t : I → (Cn ⥤ Cm)) (τ : ∀ i, t i ⋙ vm ⟶ vn)
  [∀ F : Cmᵒᵖ ⥤ A, vm.op.HasPointwiseRightKanExtension F]
  [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  [ht : ∀ i, (t i).IsContinuous Jn Jm]

/-- On sections, the comparison of presheaves is transport along `τ i` followed by the Kan
extension counit. -/
@[simp] lemma ranRestrictComparison_app_app (i : I) (P : Cmᵒᵖ ⥤ A) (U : Cn) :
    ((ranRestrictComparison A vn vm t τ i).app P).app (op U) =
      (vm.op.ran.obj P).map ((τ i).app U).op ≫
        (vm.op.ranCounit.app P).app (op ((t i).obj U)) := rfl

/-- The comparison of sheaves attached to a transformation `τ i : t i ⋙ v_m ⟶ v_n`: the
cocontinuous pushforward along `v_m` followed by restriction along `v_n` maps to restriction
along `t i`. It is `ranRestrictComparison` on underlying presheaves. -/
noncomputable def ranRestrictSheafComparison (i : I) :
    vm.sheafPushforwardCocontinuous A Jm L ⋙ vn.sheafPushforwardContinuous A Jn L ⟶
      (t i).sheafPushforwardContinuous A Jn Jm where
  app T := ⟨(ranRestrictComparison A vn vm t τ i).app T.obj⟩
  naturality _ _ f := Sheaf.hom_ext ((ranRestrictComparison A vn vm t τ i).naturality f.hom)

variable [HasWeakSheafify L A] [HasWeakSheafify Jm A]
  [∀ F : Cnᵒᵖ ⥤ A, vn.op.HasLeftKanExtension F]
  [∀ i, ∀ F : Cnᵒᵖ ⥤ A, (t i).op.HasLeftKanExtension F]
  [HasLimitsOfShape (Discrete I) A]
  [HasCoproduct fun i => sheafPullbackConstruction.sheafPullback (t i) A Jn Jm]

/-- **The ran criterion.** If the right Kan extension along `v_m.op`, evaluated at `v_n U` for an
object `U` of `C_n`, is the product over `i` of the values at `t i U`, with the transports along
the `τ i` followed by the Kan extension counit as projections, then lower shriek along `v_n`
followed by restriction along `v_m` is the coproduct of the lower shriek functors along the
`t i`.

The hypothesis is a statement about presheaves and about one object of the site at a time; it is
promoted to the product formula for the right adjoints by
`CategoryTheory.isLimitFanOfSections` and then conjugated into the coproduct formula for the
left adjoints by `CategoryTheory.Adjunction.coproductIsoOfIsLimitFan`. No sheafification is
manipulated. -/
noncomputable def sheafPullbackCompPushforwardIsoCoproductOfRan
    (hfan : ∀ (P : Cmᵒᵖ ⥤ A) (U : Cn),
      IsLimit (Fan.mk ((vm.op.ran.obj P).obj (op (vn.obj U)))
        fun i => (vm.op.ran.obj P).map ((τ i).app U).op ≫
          (vm.op.ranCounit.app P).app (op ((t i).obj U)))) :
    sheafPullbackConstruction.sheafPullback vn A Jn L ⋙
        vm.sheafPushforwardContinuous A Jm L ≅
      ∐ fun i => sheafPullbackConstruction.sheafPullback (t i) A Jn Jm :=
  (Adjunction.coproductIsoOfIsLimitFan
    ((sheafPullbackConstruction.sheafAdjunctionContinuous vn A Jn L).comp
      (vm.sheafAdjunctionCocontinuous A Jm L))
    (fun i => sheafPullbackConstruction.sheafAdjunctionContinuous (t i) A Jn Jm)
    (ranRestrictSheafComparison A Jn Jm L vn vm t τ)
    (fun T => isLimitFanOfSections Jn _ (fun X => by
      obtain ⟨U⟩ := X
      exact hfan T.obj U))).symm

end Ran

section Lan

/-- The comparison of presheaves attached to a transformation `σ i : v_m ⟶ t i ⋙ v_n`: apply the
unit of the left Kan extension along `v_n.op`, then transport along `σ i`. Its component over an
object `V` is the leg, at `σ i` applied to `V`, of the pointwise colimit cocone computing the Kan
extension at `v_m V`. -/
noncomputable def lanRestrictComparison (vn : Cn ⥤ E) (vm : Cm ⥤ E) (t : I → (Cm ⥤ Cn))
    (σ : ∀ i, vm ⟶ t i ⋙ vn) [∀ F : Cnᵒᵖ ⥤ A, vn.op.HasLeftKanExtension F] (i : I) :
    (whiskeringLeft Cmᵒᵖ Cnᵒᵖ A).obj (t i).op ⟶
      vn.op.lan ⋙ (whiskeringLeft Cmᵒᵖ Eᵒᵖ A).obj vm.op :=
  whiskerRight vn.op.lanUnit ((whiskeringLeft Cmᵒᵖ Cnᵒᵖ A).obj (t i).op) ≫
    whiskerLeft vn.op.lan ((whiskeringLeft Cmᵒᵖ Eᵒᵖ A).map (NatTrans.op (σ i)))

variable (vn : Cn ⥤ E) (vm : Cm ⥤ E) (t : I → (Cm ⥤ Cn)) (σ : ∀ i, vm ⟶ t i ⋙ vn)
  [∀ F : Cnᵒᵖ ⥤ A, vn.op.HasLeftKanExtension F]

/-- On sections, the comparison of presheaves is the Kan extension unit followed by transport
along `σ i`. -/
@[simp] lemma lanRestrictComparison_app_app (i : I) (P : Cnᵒᵖ ⥤ A) (V : Cm) :
    ((lanRestrictComparison A vn vm t σ i).app P).app (op V) =
      (vn.op.lanUnit.app P).app (op ((t i).obj V)) ≫
        (vn.op.lan.obj P).map ((σ i).app V).op := rfl

variable [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  [HasWeakSheafify L A] [HasWeakSheafify Jm A]
  [∀ F : Cmᵒᵖ ⥤ A, vm.op.HasPointwiseRightKanExtension F]
  [HasCoproduct fun i => (t i).sheafPullbackCocontinuous A Jm Jn]

/-- **The lan criterion.** If the left Kan extension along `v_n.op`, evaluated at `v_m V` for an
object `V` of `C_m`, is the coproduct over `i` of the values at `t i V`, with the Kan extension
unit followed by the transports along the `σ i` as injections, then lower shriek along `v_n`
followed by restriction along `v_m` is the coproduct of the sheaf pullbacks along the `t i`.

Unlike the ran criterion this goes through presheaves: the hypothesis is promoted to a colimit
cofan of presheaves on `C_m` by `CategoryTheory.Limits.isColimitCofanOfEvaluation`, pushed through
sheafification — a left adjoint, hence preserving coproducts — and then transported along
`sheafificationCompPushforwardContinuousIso`, which is what identifies the result with the
composite in the statement. -/
noncomputable def sheafPullbackCompPushforwardIsoCoproductOfLan
    (hcofan : ∀ (P : Cnᵒᵖ ⥤ A) (V : Cm),
      IsColimit (Cofan.mk ((vn.op.lan.obj P).obj (op (vm.obj V)))
        fun i => (vn.op.lanUnit.app P).app (op ((t i).obj V)) ≫
          (vn.op.lan.obj P).map ((σ i).app V).op)) :
    sheafPullbackConstruction.sheafPullback vn A Jn L ⋙
        vm.sheafPushforwardContinuous A Jm L ≅
      ∐ fun i => (t i).sheafPullbackCocontinuous A Jm Jn := by
  set Θ := isoWhiskerLeft (sheafToPresheaf Jn A ⋙ vn.op.lan)
    (sheafificationCompPushforwardContinuousIso vm A Jm L) with hΘ
  refine (colimit.isoColimitCocone
    (F := Discrete.functor fun i => (t i).sheafPullbackCocontinuous A Jm Jn)
    ⟨Cofan.mk (f := fun i => (t i).sheafPullbackCocontinuous A Jm Jn) _ (fun i =>
      whiskerLeft (sheafToPresheaf Jn A)
        (whiskerRight (lanRestrictComparison A vn vm t σ i) (presheafToSheaf Jm A)) ≫ Θ.inv),
    ?_⟩).symm
  refine isColimitCofanOfEvaluation _ fun T => ?_
  refine IsColimit.ofIsoColimit
    (isColimitCofanMapOfPreserves (presheafToSheaf Jm A) _
      (isColimitCofanOfEvaluation (fun i => (lanRestrictComparison A vn vm t σ i).app T.obj)
        (fun X => by obtain ⟨V⟩ := X; exact hcofan T.obj V)))
    (Cocone.ext (Θ.symm.app T) ?_)
  intro j
  obtain ⟨i⟩ := j
  rfl

end Lan

end CategoryTheory.Functor

end
