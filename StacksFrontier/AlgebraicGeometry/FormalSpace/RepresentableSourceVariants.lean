module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticDescentRepresentable

/-!
# Variants of the results of `StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSource`

The declarations below extend `StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSource` and
are kept in a module of their own so that that module stays unchanged. A primed name `X'` is a
variant of the declaration `X` there.

## Main declarations

* `isFormalAlgebraicSpace_of_representable_over_formal'`
* `isFormalAlgebraicSpace_pullback_of_representable'`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The pullback square of fppf sheaves stays a pullback square after passing to the underlying
presheaves. -/
private theorem isPullback_pullback_hom {X Y V : FppfSheaf B S hS} (v : V ⟶ Y) (f : X ⟶ Y) :
    IsPullback (pullback.fst v f).hom (pullback.snd v f).hom v.hom f.hom :=
  (IsPullback.of_hasPullback v f).map
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-- **Stacks 0AJI**, granting Stacks 0AIU. If `Y` is a formal algebraic space over `S` and
`f : X ⟶ Y` is a map of fppf sheaves representable by algebraic spaces, then `X` is a formal
algebraic space over `S`.

The affine étale atlas of `Y` base changes to an affine étale atlas of `X`, each member of
which is a formal algebraic space by Stacks 0AJH. The set-theoretic condition of Stacks 0AIS
that Stacks 0AJH needs for each base changed member is proved rather than assumed: the
projection `V ×_Y X ⟶ X` is a base change of `V ⟶ Y`, hence representable by algebraic spaces,
and the condition descends along such a morphism from `hXset`. -/
theorem isFormalAlgebraicSpace_of_representable_over_formal'
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hXset : SatisfiesSetTheoreticCondition B S hS X)
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
  have het := isRepresentableEtale_pullback_snd B S hS (v i) f (hVetale i)
  exact isFormalAlgebraicSpace_of_representable_over_affineFormal B S hS
    (pullback.fst (v i) f) (hVaffine i)
    (Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
      (isPullback_pullback_hom B S hS (v i) f).flip hf)
    (SetTheoreticDescent.satisfiesSetTheoreticCondition_of_representable_over B S hS
      (pullback.snd (v i) f)
      het.1 hXset) h0AIU

/-- **Stacks 0AJ3**, granting Stacks 0AIU, for a fibre product one of whose legs is
representable by algebraic spaces. The fibre product `V ×_Y X` of a formal algebraic space `X`
over `Y` with a morphism `v : V ⟶ Y` representable by algebraic spaces is a formal algebraic
space over `S`: the projection to `X` is a base change of `v`, so Stacks 0AJI applies. -/
theorem isFormalAlgebraicSpace_pullback_of_representable'
    {X Y V : FppfSheaf B S hS} (v : V ⟶ Y) (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hv : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS v.hom)
    (hset : SatisfiesSetTheoreticCondition B S hS (pullback v f))
    (h0AIU : ∀ (Λ : Type (u + 1)) [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
      (E : Λ ⥤ FppfSheaf B S hS),
      (∀ i : Λ, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj i).obj) →
      (∀ ⦃i j : Λ⦄ (g : i ⟶ j),
        Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom) →
      ∀ Z : FppfSheaf B S hS, SatisfiesSetTheoreticCondition B S hS Z →
        Nonempty (Z ≅ colimit E) → IsFormalAlgebraicSpace B S hS Z) :
    IsFormalAlgebraicSpace B S hS (pullback v f) :=
  isFormalAlgebraicSpace_of_representable_over_formal' B S hS (pullback.snd v f) hX
    (Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _
      (isPullback_pullback_hom B S hS v f) hv)
    hset h0AIU

variable (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

end AlgebraicGeometry.FormalSpace

end
