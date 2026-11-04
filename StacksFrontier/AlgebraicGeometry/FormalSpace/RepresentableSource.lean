module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffine
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Formal algebraic spaces along morphisms representable by algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf
sheaves on the big fppf site of `S` which is representable by algebraic spaces. **Stacks 0AJI**
says that `X` is a formal algebraic space over `S` whenever `Y` is one. Specialising to the
second projection of a fibre product gives the fibre product assertion of **Stacks 0AJ3**: the
fibre product of a formal algebraic space with a morphism representable by algebraic spaces is
again a formal algebraic space.

## Main results

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_representable_over_formal`:
  Stacks 0AJI with Stacks 0AIU and the set-theoretic condition of Stacks 0AIS as hypotheses;
  the unconditional statement is
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isRepresentableByAlgebraicSpacesULift`.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representable`:
  the fibre product assertion of Stacks 0AJ3 for a fibre product one of whose legs is
  representable by algebraic spaces, with the inputs of the previous result as hypotheses.
* `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal`:
  Stacks 0ANG, condition (1) implies condition (2), with the fibre products supplied by the
  previous result instead of by hypothesis, and so with its hypotheses; the unconditional
  statement is
  `AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal'`.

## Implementation notes

The proof of Stacks 0AJI is the proof of the source: an affine étale atlas `{Vᵢ ⟶ Y}` of the
target base changes to a family `{Vᵢ ×_Y X ⟶ X}` which is again representable étale and jointly
surjective, each member of which has an affine formal algebraic space as its target under the
other projection, so is a formal algebraic space by Stacks 0AJH; Stacks 0AJ1 then assembles `X`.
Joint surjectivity of the base changed family is
`CategoryTheory.Sheaf.isLocallySurjective_sigmaDesc_pullback_snd`.

Two inputs are explicit hypotheses here, exactly as they are in the two results used. Stacks
0AIU — a directed colimit of algebraic spaces along thickenings is a formal algebraic space —
is `h0AIU`, in the shape Stacks 0AJH consumes. The set-theoretic
condition of Stacks 0AIS is `hXset` for `X` and `hstageset` for the base changed atlas members;
it is a hypothesis of Stacks 0AJ1 and of Stacks 0AJH for the same reason, namely that it does
not follow from the corresponding conditions on the members of a covering family. Both inputs
are proved downstream, by
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isRepresentableByAlgebraicSpacesULift`,
which supplies them to the result here.

The fibre product `V ×_Y X` has `pullback.snd` a base change of `V ⟶ Y`, so the fibre product
assertion needs only the leg `V ⟶ Y` to be representable by algebraic spaces, not étale. The
fibre product of two formal algebraic spaces over a third, with neither leg representable, is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace`, and
Stacks 0AJ3 is registered at `AlgebraicGeometry.FormalSpace.hasPullbacks_formalAlgebraicSpaces`.

## References

* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJH](https://stacks.math.columbia.edu/tag/0AJH)
* [Stacks Project, Tag 0AJI](https://stacks.math.columbia.edu/tag/0AJI)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The underlying presheaf maps of a pullback of fppf sheaves form a pullback square. -/
private theorem isPullback_pullback_hom {X Y V : FppfSheaf B S hS} (v : V ⟶ Y) (f : X ⟶ Y) :
    IsPullback (pullback.fst v f).hom (pullback.snd v f).hom v.hom f.hom :=
  (IsPullback.of_hasPullback v f).map
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-- Stacks 0AJI with its inputs as hypotheses. If `Y` is a formal algebraic space over `S` and
`f : X ⟶ Y` is a map of fppf sheaves representable by algebraic spaces, then `X` is a formal
algebraic space over `S`, granting Stacks 0AIU as `h0AIU` and the set-theoretic condition of
Stacks 0AIS on the source and on the base changed atlas members as `hXset` and `hstageset`.
The unconditional statement, which proves these three hypotheses, is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isRepresentableByAlgebraicSpacesULift`.

The affine étale atlas of `Y` base changes to an affine étale atlas of `X`, each member of
which is a formal algebraic space by Stacks 0AJH. -/
theorem isFormalAlgebraicSpace_of_representable_over_formal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hXset : SatisfiesSetTheoreticCondition B S hS X)
    (hstageset : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y),
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS v →
      SatisfiesSetTheoreticCondition B S hS (pullback v f))
    (h0AIU : ∀ (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
      (E : Λ ⥤ FppfSheaf B S hS),
      (∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj) →
      (∀ ⦃i j : Λ⦄ (g : i ⟶ j),
        Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom) →
      ∀ Z : FppfSheaf B S hS, SatisfiesSetTheoreticCondition B S hS Z →
        Nonempty (Z ≅ colimit E) → IsFormalAlgebraicSpace B S hS Z) :
    IsFormalAlgebraicSpace B S hS X := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, I, V, v, hVaffine, hVetale, hVsurj⟩ := hY
  refine isFormalAlgebraicSpace_of_etaleCover B S hS X (fun i ↦ pullback (v i) f)
    (fun i ↦ pullback.snd (v i) f) (fun i ↦ ?_)
    (fun i ↦ isRepresentableEtale_pullback_snd B S hS (v i) f (hVetale i))
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hVsurj) hXset
  exact isFormalAlgebraicSpace_of_representable_over_affineFormal B S hS
    (pullback.fst (v i) f) (hVaffine i)
    (Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
      (isPullback_pullback_hom B S hS (v i) f).flip hf)
    (hstageset (V i) (v i) (hVaffine i) (hVetale i)) h0AIU

/-- The fibre product assertion of Stacks 0AJ3 for a fibre product one of whose legs is
representable by algebraic spaces, granting Stacks 0AIU as `h0AIU` and the set-theoretic
condition of Stacks 0AIS as `hset` and `hstageset`. The fibre product `V ×_Y X` of a formal
algebraic space `X` over `Y` with a morphism `v : V ⟶ Y` representable by algebraic spaces is a
formal algebraic space over `S`: the projection to `X` is a base change of `v`, so the previous
result applies. Applied to that projection, the unconditional Stacks 0AJI,
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isRepresentableByAlgebraicSpacesULift`,
gives the same conclusion with none of the three hypotheses; Stacks 0AJ3 itself is registered at
`AlgebraicGeometry.FormalSpace.hasPullbacks_formalAlgebraicSpaces`. -/
theorem isFormalAlgebraicSpace_pullback_of_representable
    {X Y V : FppfSheaf B S hS} (v : V ⟶ Y) (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hv : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS v.hom)
    (hset : SatisfiesSetTheoreticCondition B S hS (pullback v f))
    (hstageset : ∀ (W : FppfSheaf B S hS) (w : W ⟶ X),
      IsAffineFormalAlgebraicSpace B S hS W → IsRepresentableEtale B S hS w →
      SatisfiesSetTheoreticCondition B S hS (pullback w (pullback.snd v f)))
    (h0AIU : ∀ (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
      (E : Λ ⥤ FppfSheaf B S hS),
      (∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj) →
      (∀ ⦃i j : Λ⦄ (g : i ⟶ j),
        Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom) →
      ∀ Z : FppfSheaf B S hS, SatisfiesSetTheoreticCondition B S hS Z →
        Nonempty (Z ≅ colimit E) → IsFormalAlgebraicSpace B S hS Z) :
    IsFormalAlgebraicSpace B S hS (pullback v f) :=
  isFormalAlgebraicSpace_of_representable_over_formal B S hS (pullback.snd v f) hX
    (Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
      (isPullback_pullback_hom B S hS v f) hv)
    hset hstageset h0AIU

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- Stacks 0ANG, condition (1) implies condition (2), granting Stacks 0AIU as `h0AIU` and the
set-theoretic condition of Stacks 0AIS for the fibre products as `hset` and `hstageset`. If `P`
holds on every affine étale diagram over a morphism `f : X ⟶ Y` of formal algebraic spaces,
then the atlas of the target and the atlases of the fibre products of its members with the
source witness condition (2). The unconditional statement is
`AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal'`.

The fibre products are formal algebraic spaces by the previous result, which here replaces the
hypothesis `hpb` of
`AlgebraicGeometry.FormalSpace.hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram`. -/
theorem hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram_of_formal
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hset : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y),
      IsAffineFormalAlgebraicSpace B S hS V → IsRepresentableEtale B S hS v →
      SatisfiesSetTheoreticCondition B S hS (pullback v f))
    (hstageset : ∀ (V : FppfSheaf B S hS) (v : V ⟶ Y) (W : FppfSheaf B S hS) (w : W ⟶ X),
      IsAffineFormalAlgebraicSpace B S hS W → IsRepresentableEtale B S hS w →
      SatisfiesSetTheoreticCondition B S hS (pullback w (pullback.snd v f)))
    (h0AIU : ∀ (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
      (E : Λ ⥤ FppfSheaf B S hS),
      (∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj) →
      (∀ ⦃i j : Λ⦄ (g : i ⟶ j),
        Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom) →
      ∀ Z : FppfSheaf B S hS, SatisfiesSetTheoreticCondition B S hS Z →
        Nonempty (Z ≅ colimit E) → IsFormalAlgebraicSpace B S hS Z)
    (hf : HasPropertyOnEveryAffineEtaleDiagram B S hS C P f) :
    HasPropertyAfterTargetCover B S hS C P f :=
  hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS C P f hY
    (fun V' v' hV' hv' ↦ isFormalAlgebraicSpace_pullback_of_representable B S hS v' f hX hv'.1
      (hset V' v' hV' hv') (fun W w hW hw ↦ hstageset V' v' W w hW hw) h0AIU) hf

end AlgebraicGeometry.FormalSpace

end
