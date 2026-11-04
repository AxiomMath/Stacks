module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.CategoryTheory.Galois.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Cancellation

/-!
# Connected objects of the category of finite étale covers

For a finite étale cover `V` of a scheme `X`, the categorical notion of connectedness used in the
theory of Galois categories — `CategoryTheory.PreGaloisCategory.IsConnected`, which asks that `V`
be non-initial and have no non-trivial subobjects — agrees with connectedness of the underlying
topological space of `V`. This is the dictionary that lets the criteria of Stacks 0BN6, 0BS9 and
their relatives, all phrased with categorical connectedness, be fed with geometric input.

Both directions go through the fact that a subobject of `V` in `FÉt_X` is a clopen piece of `V`.
For the forward direction a proper nonempty clopen subset of `V` is itself a finite étale cover
of `X` with a monomorphism to `V` which is not an isomorphism. For the converse one has to see
that a monomorphism `i : A ⟶ V` of finite étale covers is a monomorphism of the underlying
schemes; that is not automatic, because the test objects in `FÉt_X` are only the finite étale
covers, but the scheme-theoretic fibre square of `i` is again a finite étale cover of `X`
(`AlgebraicGeometry.finiteEtaleOverPullbackSelf`), and its two projections are morphisms of
covers equalized by `i`. Granted that, `i.left` is étale and a monomorphism, hence an open
immersion, and finite, hence closed; so its range is clopen and nonempty, therefore everything,
and `i.left` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.finiteEtaleOverEmpty` — the empty scheme as a finite étale cover.
* `AlgebraicGeometry.finiteEtaleOverPullbackSelf` — the scheme-theoretic fibre square of a
  morphism of finite étale covers, as a finite étale cover of the base.

## Main results

* `AlgebraicGeometry.isInitial_finiteEtaleOver_of_isEmpty_left` and
  `AlgebraicGeometry.isEmpty_left_of_isInitial_finiteEtaleOver` — a finite étale cover is initial
  exactly when its underlying scheme is empty.
* `AlgebraicGeometry.etale_hom_left` and `AlgebraicGeometry.isFinite_hom_left` — a morphism of
  finite étale covers is finite étale on underlying schemes.
* `AlgebraicGeometry.mono_left_of_mono` — a monomorphism of finite étale covers is a
  monomorphism of underlying schemes.
* `AlgebraicGeometry.connectedSpace_left_of_isConnected` and
  `AlgebraicGeometry.isConnected_of_connectedSpace_left`, packaged as
  `AlgebraicGeometry.isConnected_iff_connectedSpace_left` — the dictionary itself.

## Implementation notes

Nothing here is a Stacks tag: these are the structural facts about `FÉt_X` that the tags of the
fundamental-group chapter are stated against, so they carry no attribute.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Initial objects -/

/-- The empty scheme, as a finite étale cover of `X`. -/
def finiteEtaleOverEmpty (X : Scheme.{u}) : FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (Scheme.emptyTo X) ⟨inferInstance, inferInstance⟩

/-- A finite étale cover with empty source is an initial object. -/
def isInitial_finiteEtaleOver_of_isEmpty_left {X : Scheme.{u}} (A : FiniteEtaleOver X)
    [IsEmpty A.left] : IsInitial A :=
  let hA : IsInitial A.left := AlgebraicGeometry.isInitialOfIsEmpty
  IsInitial.ofUniqueHom (fun B ↦ MorphismProperty.Over.homMk (hA.to B.left) (hA.hom_ext _ _))
    fun _ _ ↦ MorphismProperty.Over.Hom.ext (hA.hom_ext _ _)

/-- An initial finite étale cover has empty source. -/
theorem isEmpty_left_of_isInitial_finiteEtaleOver {X : Scheme.{u}} (A : FiniteEtaleOver X)
    (h : IsInitial A) : IsEmpty A.left := by
  have h0 : IsEmpty (finiteEtaleOverEmpty X).left := by
    show IsEmpty ↥(∅ : Scheme.{u})
    infer_instance
  let i : A ≅ finiteEtaleOverEmpty X :=
    h.uniqueUpToIso (isInitial_finiteEtaleOver_of_isEmpty_left (finiteEtaleOverEmpty X))
  exact Function.isEmpty (fun a ↦ i.hom.left a)

/-! ### Morphisms of covers on underlying schemes -/

/-- A morphism of finite étale covers of `X` is étale on underlying schemes: it is a morphism
between two schemes étale over `X` commuting with the structure morphisms. -/
theorem etale_hom_left {X : Scheme.{u}} {A V : FiniteEtaleOver X} (i : A ⟶ V) : Etale i.left :=
  have : Etale A.hom := A.prop.2
  have : Etale V.hom := V.prop.2
  etale_of_etale_over i.left (MorphismProperty.Over.w i)

/-- A morphism of finite étale covers of `X` is finite on underlying schemes: its composite with
the structure morphism of the target is the structure morphism of the source, which is finite,
and the structure morphism of the target is separated. -/
theorem isFinite_hom_left {X : Scheme.{u}} {A V : FiniteEtaleOver X} (i : A ⟶ V) :
    IsFinite i.left := by
  have hA : IsFinite A.hom := A.prop.1
  have hV : IsFinite V.hom := V.prop.1
  have : IsFinite (i.left ≫ V.hom) := (MorphismProperty.Over.w i) ▸ hA
  exact IsFinite.of_comp i.left V.hom

/-- The scheme-theoretic fibre square of a morphism of finite étale covers, as a finite étale
cover of the base: both projections to the source of the morphism are finite étale, being base
changes of it, and the source is finite étale over the base. -/
def finiteEtaleOverPullbackSelf {X : Scheme.{u}} {A V : FiniteEtaleOver X}
    (i : A ⟶ V) : FiniteEtaleOver X :=
  have : IsFinite A.hom := A.prop.1
  have : Etale A.hom := A.prop.2
  have : IsFinite i.left := isFinite_hom_left i
  have : Etale i.left := etale_hom_left i
  MorphismProperty.Over.mk ⊤ (pullback.fst i.left i.left ≫ A.hom)
    ⟨inferInstance, inferInstance⟩

/-- **A monomorphism of finite étale covers is a monomorphism of the underlying schemes.** This
needs an argument, because the test objects for a monomorphism in `FÉt_X` are only the finite
étale covers of `X`: the point is that the scheme-theoretic fibre square of the morphism is
itself such a cover, so its two projections are morphisms of covers equalized by the given
monomorphism and therefore equal. -/
theorem mono_left_of_mono {X : Scheme.{u}} {A V : FiniteEtaleOver X} (i : A ⟶ V) [Mono i] :
    Mono i.left := by
  have : Etale i.left := etale_hom_left i
  have : IsFinite i.left := isFinite_hom_left i
  have hw : i.left ≫ V.hom = A.hom := MorphismProperty.Over.w i
  let P : FiniteEtaleOver X := finiteEtaleOverPullbackSelf i
  have hPhom : P.hom = pullback.fst i.left i.left ≫ A.hom := rfl
  let pf : P ⟶ A := MorphismProperty.Over.homMk (pullback.fst i.left i.left) hPhom.symm
  have hps : pullback.snd i.left i.left ≫ A.hom = pullback.fst i.left i.left ≫ A.hom := by
    rw [← hw, pullback.condition_assoc]
  let ps : P ⟶ A := MorphismProperty.Over.homMk (pullback.snd i.left i.left)
    (hps.trans hPhom.symm)
  have hcomp : pf ≫ i = ps ≫ i := MorphismProperty.Over.Hom.ext pullback.condition
  have heq : pullback.fst i.left i.left = pullback.snd i.left i.left :=
    congrArg (fun k : P ⟶ A ↦ k.left) ((cancel_mono i).mp hcomp)
  exact ⟨fun {W} g h hgh ↦ (pullback.lift_fst g h hgh).symm.trans
    ((congrArg (pullback.lift g h hgh ≫ ·) heq).trans (pullback.lift_snd g h hgh))⟩

/-! ### The dictionary -/

/-- **A categorically connected finite étale cover has connected underlying space.** A proper
nonempty clopen subset would be a finite étale cover of the base with a monomorphism to the given
one which is not an isomorphism. -/
theorem connectedSpace_left_of_isConnected {X : Scheme.{u}} (V : FiniteEtaleOver X)
    (hV : PreGaloisCategory.IsConnected V) : ConnectedSpace V.left := by
  have hVfin : IsFinite V.hom := V.prop.1
  have hVet : Etale V.hom := V.prop.2
  rw [connectedSpace_iff_clopen]
  refine ⟨?_, ?_⟩
  · exact not_isEmpty_iff.mp fun _ ↦ hV.notInitial (isInitial_finiteEtaleOver_of_isEmpty_left V)
  · intro s hs
    rcases Set.eq_empty_or_nonempty s with hempty | ⟨z, hz⟩
    · exact Or.inl hempty
    refine Or.inr ?_
    let U : V.left.Opens := ⟨s, hs.isOpen⟩
    have hUs : (U : Set V.left) = s := rfl
    have : IsClosedImmersion U.ι :=
      IsClosedImmersion.of_isPreimmersion _ (by
        rw [Scheme.Opens.range_ι, hUs]
        exact hs.isClosed)
    let A : FiniteEtaleOver X :=
      MorphismProperty.Over.mk ⊤ (U.ι ≫ V.hom) ⟨inferInstance, inferInstance⟩
    let f : A ⟶ V := MorphismProperty.Over.homMk U.ι rfl
    have hmono : Mono f := ⟨fun {W} g h hgh ↦ MorphismProperty.Over.Hom.ext
      ((cancel_mono U.ι).mp (congrArg (fun k : W ⟶ V ↦ k.left) hgh))⟩
    have hiso : IsIso f := hV.noTrivialComponent A f fun hi ↦
      (isEmpty_left_of_isInitial_finiteEtaleOver A hi).elim (⟨z, hz⟩ : U)
    have hinv : (CategoryTheory.inv f).left ≫ U.ι = 𝟙 V.left :=
      congrArg (fun k : V ⟶ V ↦ k.left) (IsIso.inv_hom_id f)
    refine Set.eq_univ_of_forall fun y ↦ ?_
    have hy : y ∈ Set.range U.ι.base :=
      ⟨(CategoryTheory.inv f).left.base y, congrArg (fun k : V.left ⟶ V.left ↦ k.base y) hinv⟩
    rwa [Scheme.Opens.range_ι, hUs] at hy

/-- **A finite étale cover with connected underlying space is categorically connected.** A
monomorphism into it from a non-initial cover is a monomorphism of schemes by
`AlgebraicGeometry.mono_left_of_mono`, hence an open immersion because it is also étale, and a
closed map because it is finite; its range is therefore a nonempty clopen subset, so all of the
target, and the monomorphism is an isomorphism. -/
theorem isConnected_of_connectedSpace_left {X : Scheme.{u}} (V : FiniteEtaleOver X)
    [ConnectedSpace V.left] : PreGaloisCategory.IsConnected V where
  notInitial h :=
    (isEmpty_left_of_isInitial_finiteEtaleOver V h).elim (Classical.arbitrary V.left)
  noTrivialComponent A i hmi hA := by
    have hAne : Nonempty A.left :=
      not_isEmpty_iff.mp fun _ ↦ hA (isInitial_finiteEtaleOver_of_isEmpty_left A)
    have hmono : Mono i.left := mono_left_of_mono i
    have het : Etale i.left := etale_hom_left i
    have hfin : IsFinite i.left := isFinite_hom_left i
    have hoi : IsOpenImmersion i.left := IsOpenImmersion.of_flat_of_mono i.left
    have hopen : IsOpen (Set.range i.left.base) := hoi.base_open.isOpen_range
    have hclosed : IsClosed (Set.range i.left.base) := by
      simpa using (i.left.isClosedMap).isClosed_range
    have hrange : Set.range i.left.base = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩
      ⟨_, hAne.some, rfl⟩
    have hepi : Epi i.left.base := (TopCat.epi_iff_surjective _).mpr
      (Set.range_eq_univ.mp hrange)
    have hisol : IsIso i.left := (isIso_iff_isOpenImmersion_and_epi_base _).mpr ⟨hoi, hepi⟩
    have hw : i.left ≫ V.hom = A.hom := MorphismProperty.Over.w i
    let j : V ⟶ A := MorphismProperty.Over.homMk (CategoryTheory.inv i.left) (by
      rw [← hw, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp])
    exact ⟨⟨j, MorphismProperty.Over.Hom.ext (IsIso.hom_inv_id i.left),
      MorphismProperty.Over.Hom.ext (IsIso.inv_hom_id i.left)⟩⟩

/-- **Categorical and topological connectedness agree for finite étale covers.** -/
theorem isConnected_iff_connectedSpace_left {X : Scheme.{u}} (V : FiniteEtaleOver X) :
    PreGaloisCategory.IsConnected V ↔ ConnectedSpace V.left :=
  ⟨connectedSpace_left_of_isConnected V,
    fun _ ↦ isConnected_of_connectedSpace_left V⟩

end AlgebraicGeometry

end
