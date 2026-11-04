module

public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A morphism of topoi computed by a cocontinuous lift between subsites

Consider four sites `(C₁, J₁)`, `(C₂, J₂)`, `(D₁, K₁)`, `(D₂, K₂)` and functors

* `u₁ : C₁ ⥤ D₁` and `u₂ : C₂ ⥤ D₂`, continuous, whose induced restriction functors `u₁^s`
  and `u₂^s` on categories of sheaves are *equivalences* — so `C₁` and `C₂` are, up to
  equivalence of topoi, subsites of `D₁` and `D₂`;
* `q : D₂ ⥤ D₁`, continuous, whose induced restriction `q^s` on sheaves is the direct image
  of a morphism of topoi, i.e. has a left adjoint;
* `b : C₂ ⥤ C₁`, continuous, and `l : C₁ ⥤ C₂`, cocontinuous, with `l ⊣ b`;

subject to the commutativity `u₂ ⋙ q ≅ b ⋙ u₁` of the square
```
C₂ --u₂--> D₂
|          |
b          q
v          v
C₁ --u₁--> D₁
```

Then the morphism of topoi attached to `q` is the one attached to the cocontinuous functor
`l`: its direct image is `{}_s l` and its inverse image is the sheafified restriction along
`l ⋙ u₂`.  If moreover `l` is fully faithful, the direct image is fully faithful and the
counit of the morphism of topoi is invertible.

## Main results

* `CategoryTheory.Functor.fullyFaithfulSheafPushforwardCocontinuous`: for a fully faithful
  cocontinuous `l`, the pushforward `{}_s l` on sheaves is fully faithful.
* `CategoryTheory.sheafPushforwardContinuousIsoOfCocontinuousLift`: the direct image `q^s`
  of the square, restricted along `u₂`, is restriction along `u₁` followed by `{}_s l`.
* `CategoryTheory.sheafPullbackIsoOfCocontinuousLift`: the inverse image of the morphism of
  topoi, restricted along `u₁`, is the sheafified restriction along `l ⋙ u₂`, i.e.
  `(l ⋙ u₂).sheafPullbackCocontinuous`.
* `CategoryTheory.fullyFaithfulSheafPushforwardContinuousOfCocontinuousLift` and
  `CategoryTheory.isIso_counit_of_cocontinuousLift`: if `l` is fully faithful then so is
  `q^s`, and the counit of the morphism of topoi is a natural isomorphism.

## Relation to the Stacks project

These are the three purely site-theoretic steps of Stacks Tag 09BL, the statement that for a
closed immersion of affine schemes `i : Z ⟶ X` the direct image on small pro-étale sheaves of
sets is fully faithful.  There `D₁`, `D₂` are the small pro-étale sites of `Z` and `X`, `C₁`,
`C₂` their subsites of affine ind-étale objects (Stacks 098X, whose content is exactly that
`u₁^s` and `u₂^s` are equivalences), `q` is pro-étale base change along `i` (Stacks 098T) and
`l ⊣ b` is the affine ind-étale lift and its base change (Stacks 09BK), `l` being fully
faithful and cocontinuous.  The geometric input of 09BL is entirely contained in those
hypotheses; what is proved here is everything that remains.  No `stacks` attribute is
attached, because 09BL itself is not available: neither Stacks 098X nor Stacks 09BK is
formalized in this library, so the instantiation of this file that would prove 09BL cannot be
written yet.  The obstruction is 098X, whose proof needs the bounded w-contractible covers of
Stacks 0984 and hence the characterisation of w-contractible rings of Stacks 0982, which is
not in the library either.

## Implementation notes

`CategoryTheory.Functor.sheafPullbackCocontinuous` is restriction along a functor followed by
sheafification, so the inverse-image formula is stated as an isomorphism of functors with
`(l ⋙ u₂).sheafPullbackCocontinuous`, which is naturality in the sheaf.  It is obtained from
uniqueness of left adjoints: both sides are left adjoint to the same functor, the right-hand
side by `CategoryTheory.Functor.sheafAdjunctionPullbackCocontinuous` composed with the
equivalence `u₂^s`, and the left-hand side by the given adjunction composed with the
equivalence `u₁^s`.

Full faithfulness of `{}_s l` for fully faithful `l` is proved on underlying presheaves: there
`{}_s l` becomes the right Kan extension `l.op.ran`, whose adjunction has invertible counit
because `l.op` is fully faithful.

## References

* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ w w' u₁' u₂' u₃' u₄'

section FullyFaithfulPushforward

variable {C : Type u₁'} [Category.{v₁} C] {D : Type u₂'} [Category.{v₂} D]

/-- For a fully faithful cocontinuous functor `l : C ⥤ D` between sites, the pushforward
`{}_s l : Sh(C) ⥤ Sh(D)` is fully faithful.

On underlying presheaves `{}_s l` is the right Kan extension `l.op.ran`
(`CategoryTheory.Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`), and the counit
of the adjunction between restriction along `l.op` and `l.op.ran` is invertible because `l.op`
is fully faithful; so `l.op.ran` is fully faithful, hence so is `{}_s l` composed with the
fully faithful inclusion of sheaves into presheaves, hence so is `{}_s l`. -/
@[sga "4 I 5.6" "i⇒iv", sga "4 I 5.7" "more general", sga "4 V 7.1.0" "partial"]
noncomputable def Functor.fullyFaithfulSheafPushforwardCocontinuous (l : C ⥤ D)
    (A : Type w) [Category.{w'} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [l.IsCocontinuous J K] [l.Full] [l.Faithful]
    [∀ F : Cᵒᵖ ⥤ A, l.op.HasPointwiseRightKanExtension F] :
    (l.sheafPushforwardCocontinuous A J K).FullyFaithful := by
  letI := (fullyFaithfulSheafToPresheaf K A).faithful
  exact (((fullyFaithfulSheafToPresheaf J A).comp
    (l.op.ranAdjunction A).fullyFaithfulROfIsIsoCounit).ofIso
      (l.sheafPushforwardCocontinuousCompSheafToPresheafIso A J K).symm).ofCompFaithful

end FullyFaithfulPushforward

section Square

variable {C₁ : Type u₁'} [Category.{v₁} C₁] {C₂ : Type u₂'} [Category.{v₂} C₂]
  {D₁ : Type u₃'} [Category.{v₃} D₁] {D₂ : Type u₄'} [Category.{v₄} D₂]
  (A : Type w) [Category.{w'} A]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  (K₁ : GrothendieckTopology D₁) (K₂ : GrothendieckTopology D₂)
  {u₁ : C₁ ⥤ D₁} {u₂ : C₂ ⥤ D₂} {q : D₂ ⥤ D₁} {l : C₁ ⥤ C₂} {b : C₂ ⥤ C₁}
  [u₁.IsContinuous J₁ K₁] [u₂.IsContinuous J₂ K₂] [q.IsContinuous K₂ K₁]
  [b.IsContinuous J₂ J₁] [l.IsCocontinuous J₁ J₂]
  [∀ F : C₁ᵒᵖ ⥤ A, l.op.HasPointwiseRightKanExtension F]

/-- **The direct image of the square.** Restriction along `q` followed by restriction along
`u₂` is restriction along `u₁` followed by the pushforward `{}_s l` of the cocontinuous lift.

The two sides are restriction along `u₂ ⋙ q` and along `b ⋙ u₁` respectively — for the
right-hand side because `{}_s l ≅ b^s` by
`CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso` — so the commutativity
`u₂ ⋙ q ≅ b ⋙ u₁` of the square of sites gives the isomorphism. -/
noncomputable def sheafPushforwardContinuousIsoOfCocontinuousLift
    (adj : l ⊣ b) (e : u₂ ⋙ q ≅ b ⋙ u₁) :
    q.sheafPushforwardContinuous A K₂ K₁ ⋙ u₂.sheafPushforwardContinuous A J₂ K₂ ≅
      u₁.sheafPushforwardContinuous A J₁ K₁ ⋙ l.sheafPushforwardCocontinuous A J₁ J₂ := by
  letI : (u₂ ⋙ q).IsContinuous J₂ K₁ := Functor.isContinuous_comp u₂ q J₂ K₂ K₁
  letI : (b ⋙ u₁).IsContinuous J₂ K₁ := Functor.isContinuous_comp b u₁ J₂ J₁ K₁
  exact Functor.sheafPushforwardContinuousComp u₂ q A J₂ K₂ K₁ ≪≫
    Functor.sheafPushforwardContinuousIso e A J₂ K₁ ≪≫
    (Functor.sheafPushforwardContinuousComp b u₁ A J₂ J₁ K₁).symm ≪≫
    Functor.isoWhiskerLeft _ (adj.sheafPushforwardCocontinuousIso A).symm

/-- **Full faithfulness of the direct image.** If the cocontinuous lift `l` is fully faithful
and the two subsite restrictions are equivalences, then restriction along `q` is fully
faithful.

Restriction along `q`, followed by the equivalence `u₂^s`, is the equivalence `u₁^s` followed
by `{}_s l`, which is fully faithful; a functor whose composite with a faithful functor is
fully faithful is itself fully faithful. -/
noncomputable def fullyFaithfulSheafPushforwardContinuousOfCocontinuousLift
    (adj : l ⊣ b) (e : u₂ ⋙ q ≅ b ⋙ u₁) [l.Full] [l.Faithful]
    [(u₁.sheafPushforwardContinuous A J₁ K₁).IsEquivalence]
    [(u₂.sheafPushforwardContinuous A J₂ K₂).IsEquivalence] :
    (q.sheafPushforwardContinuous A K₂ K₁).FullyFaithful :=
  (((Functor.FullyFaithful.ofFullyFaithful _).comp
    (l.fullyFaithfulSheafPushforwardCocontinuous A J₁ J₂)).ofIso
      (sheafPushforwardContinuousIsoOfCocontinuousLift A J₁ J₂ K₁ K₂ adj e).symm).ofCompFaithful

/-- **Invertibility of the counit.** In the situation of
`CategoryTheory.fullyFaithfulSheafPushforwardContinuousOfCocontinuousLift`, the counit of any
adjunction exhibiting restriction along `q` as a right adjoint — that is, of the morphism of
topoi attached to `q` — is a natural isomorphism. -/
theorem isIso_counit_of_cocontinuousLift {P : Sheaf K₂ A ⥤ Sheaf K₁ A}
    (adjM : P ⊣ q.sheafPushforwardContinuous A K₂ K₁)
    (adj : l ⊣ b) (e : u₂ ⋙ q ≅ b ⋙ u₁) [l.Full] [l.Faithful]
    [(u₁.sheafPushforwardContinuous A J₁ K₁).IsEquivalence]
    [(u₂.sheafPushforwardContinuous A J₂ K₂).IsEquivalence] :
    IsIso adjM.counit := by
  have h := fullyFaithfulSheafPushforwardContinuousOfCocontinuousLift A J₁ J₂ K₁ K₂ adj e
  have := h.full
  have := h.faithful
  exact adjM.counit_isIso_of_R_fully_faithful

/-- **The inverse-image formula.** Let `P` be the inverse image of the morphism of topoi
attached to `q`, so `P ⊣ q^s`. Then `P`, followed by restriction along `u₁`, is the sheafified
restriction along `l ⋙ u₂`.

Both functors are left adjoint to the same functor `(u₁^s)⁻¹ ⋙ q^s`: the left-hand side by
composing `adjM` with the equivalence `u₁^s`, and the right-hand side because, after
rewriting `(l ⋙ u₂).sheafPullbackCocontinuous` as `u₂^s` followed by
`l.sheafPullbackCocontinuous`, it is the composite of the equivalence `u₂^s` with
`CategoryTheory.Functor.sheafAdjunctionPullbackCocontinuous`, whose right adjoint `{}_s l`
is identified with `(u₁^s)⁻¹ ⋙ q^s` by
`CategoryTheory.sheafPushforwardContinuousIsoOfCocontinuousLift`. -/
@[sga "4 III 2.5" "v^* ≅ u^s"]
noncomputable def sheafPullbackIsoOfCocontinuousLift [HasWeakSheafify J₁ A]
    {P : Sheaf K₂ A ⥤ Sheaf K₁ A} (adjM : P ⊣ q.sheafPushforwardContinuous A K₂ K₁)
    (adj : l ⊣ b) (e : u₂ ⋙ q ≅ b ⋙ u₁)
    [(u₁.sheafPushforwardContinuous A J₁ K₁).IsEquivalence]
    [(u₂.sheafPushforwardContinuous A J₂ K₂).IsEquivalence] :
    P ⋙ u₁.sheafPushforwardContinuous A J₁ K₁ ≅
      (l ⋙ u₂).sheafPullbackCocontinuous A J₁ K₂ := by
  let e₁ := (u₁.sheafPushforwardContinuous A J₁ K₁).asEquivalence
  let e₂ := (u₂.sheafPushforwardContinuous A J₂ K₂).asEquivalence
  let hRight : e₁.inverse ⋙ q.sheafPushforwardContinuous A K₂ K₁ ≅
      l.sheafPushforwardCocontinuous A J₁ J₂ ⋙ e₂.inverse :=
    Iso.inverseCompIso (Iso.isoCompInverse (H := e₂)
      (sheafPushforwardContinuousIsoOfCocontinuousLift A J₁ J₂ K₁ K₂ adj e) ≪≫
      Functor.associator _ _ _)
  exact (adjM.comp e₁.toAdjunction).leftAdjointUniq
    ((e₂.toAdjunction.comp (l.sheafAdjunctionPullbackCocontinuous A J₁ J₂)).ofNatIsoRight
      hRight.symm)

end Square

end CategoryTheory
