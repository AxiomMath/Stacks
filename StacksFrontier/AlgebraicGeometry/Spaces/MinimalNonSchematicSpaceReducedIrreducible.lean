module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedUnionPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfSchemeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Scheme

/-!
# Minimal non-schematic algebraic spaces are reduced and irreducible (Stacks 0B7Z)

Let `X` be an algebraic space over a scheme `S` which is not a scheme, and assume every closed
subspace of `X` other than `X` itself is a scheme. Then `X` is reduced and `|X|` is irreducible.

Being a scheme is `CategoryTheory.Functor.IsRepresentable` of the presheaf underlying the space.
A *proper* closed subspace is a closed subspace `Z` with `Z ≠ ⊤` as a subfunctor, which is the
meaning of "proper closed subspace `Z ⊂ X`" in the source (it has nothing to do with the
morphism property of being proper).

## Main results

* `AlgebraicGeometry.Space.isRepresentable_schemeTheoreticUnion`: the scheme-theoretic union of
  two closed subspaces which are schemes is a scheme.
* `hasEtaleLocalProperty_isReduced_and_irreducibleSpace_of_forall_ne_top_isRepresentable`:
  **Stacks 0B7Z.** An algebraic space which is not a scheme, all of whose proper closed
  subspaces are schemes, is reduced and has irreducible underlying space.

## Implementation notes

Both halves rest on one consequence of Stacks 07VU in its closed-immersion form,
`AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective`, which is proved in
the library with no hypotheses: a closed subspace of `X` carrying every point of `X` is not a
scheme, since otherwise `X` would be one.

*Reducedness* is the first sentence of the source proof. If the reduction of `X` is not the
whole of `X` it is a proper closed subspace, hence a scheme, which the previous paragraph
excludes; so the reduction is `⊤`, its inclusion is an isomorphism, and `X` inherits its
reducedness.

*Irreducibility* follows the first route of the source proof, through the later theory of
pushouts. `|X|` is nonempty, because an algebraic space without points is its own schematic
locus (Stacks 03JH). If `|X| = T₁ ∪ T₂` with `T₁, T₂` proper closed subsets, the reduced induced
closed subspaces `Z₁, Z₂` (Stacks 047X, 03IQ) are proper, hence schemes. Their scheme-theoretic
union is the pushout in algebraic spaces of `Z₁ ← Z₁ ∩ Z₂ → Z₂` (Stacks 0CZ1), and that pushout
is the scheme `Z₁ ⨿_{Z₁ ∩ Z₂} Z₂` of Stacks 0B7M, because a scheme pushout along closed
immersions is a pushout of algebraic spaces (Stacks 0EDP). So the union is a scheme with every
point of `X`, contradicting the first paragraph. The source instead identifies the union with
`X` using reducedness; that identification is not needed here.

The source assumes `X` quasi-compact and quasi-separated. Neither assumption is used by either
route of its proof that is formalized here, so they are omitted: the statement below is the
source statement with two hypotheses fewer.

## References

* [Stacks Project, Tag 0B7Z](https://stacks.math.columbia.edu/tag/0B7Z)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 0B7M](https://stacks.math.columbia.edu/tag/0B7M)
* [Stacks Project, Tag 0CZ1](https://stacks.math.columbia.edu/tag/0CZ1)
* [Stacks Project, Tag 0EDP](https://stacks.math.columbia.edu/tag/0EDP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The scheme-theoretic union of two schemes -/

/-- A morphism of presheaves between two representable presheaves which is a closed immersion
is, through chosen representations, a closed immersion of the underlying schemes. -/
private theorem isClosedImmersion_toScheme_preimage {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    [F.IsRepresentable] [G.IsRepresentable] (f : F ⟶ G) (hf : IsClosedImmersion B S hS f) :
    _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (Yoneda.fullyFaithful.preimage (F.reprW.hom ≫ f ≫ G.reprW.inv))) := by
  refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) _).1 ?_
  rw [Functor.FullyFaithful.map_preimage]
  exact MorphismProperty.RespectsIso.precomp _ F.reprW.hom _
    (MorphismProperty.RespectsIso.postcomp _ G.reprW.inv f hf)

/-- **The scheme-theoretic union of two closed subspaces which are schemes is a scheme.**

The intersection is a closed subspace of a scheme, hence a scheme. The union is the pushout of
the two subspaces over their intersection in algebraic spaces (Stacks 0CZ1), and after choosing
representing objects that span is a span of closed immersions of schemes, whose scheme pushout
(Stacks 0B7M) is a pushout of algebraic spaces (Stacks 0EDP). Two pushouts of isomorphic spans
have isomorphic apexes. -/
theorem isRepresentable_schemeTheoreticUnion (X : AlgebraicSpaces B S hS)
    (Y Z : ClosedSubspaces B S hS X.1) (hY : Y.1.toFunctor.IsRepresentable)
    (hZ : Z.1.toFunctor.IsRepresentable) :
    (schemeTheoreticUnion B S hS X.1 X.2 Y Z).1.toFunctor.IsRepresentable := by
  classical
  let I := schemeTheoreticIntersection B S hS X.1 X.2 Y Z
  have hI : I.1.toFunctor.IsRepresentable :=
    isRepresentable_of_isClosedImmersion B S hS _
      (isClosedImmersion_schemeTheoreticIntersection_le_left B S hS X.2 Y Z) hY
  have := hY
  have := hZ
  have := hI
  have hle₁ : I.1 ≤ Y.1 := inf_le_left
  have hle₂ : I.1 ≤ Z.1 := inf_le_right
  let a₁ : I.1.toFunctor.reprX ⟶ Y.1.toFunctor.reprX := Yoneda.fullyFaithful.preimage
    (I.1.toFunctor.reprW.hom ≫ Subfunctor.homOfLe hle₁ ≫ Y.1.toFunctor.reprW.inv)
  let a₂ : I.1.toFunctor.reprX ⟶ Z.1.toFunctor.reprX := Yoneda.fullyFaithful.preimage
    (I.1.toFunctor.reprW.hom ≫ Subfunctor.homOfLe hle₂ ≫ Z.1.toFunctor.reprW.inv)
  have hA₁ : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map a₁) :=
    isClosedImmersion_toScheme_preimage B S hS _
      (isClosedImmersion_schemeTheoreticIntersection_le_left B S hS X.2 Y Z)
  have hA₂ : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map a₂) :=
    isClosedImmersion_toScheme_preimage B S hS _
      (isClosedImmersion_schemeTheoreticIntersection_le_right B S hS X.2 Y Z)
  let s := closedImmersionSpanSituation B S hS a₁ a₂ hA₁ hA₂
  have hP : B.Contains (pushoutScheme s) :=
    lt_of_le_of_lt (pushoutScheme_size_le _)
      (max_lt Y.1.toFunctor.reprX.left.2 Z.1.toFunctor.reprX.left.2)
  let e₁ : (⟨yoneda.obj I.1.toFunctor.reprX, isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ≅ closedSubspaceToSpace B S hS X I :=
    ObjectProperty.isoMk _ I.1.toFunctor.reprW
  let e₂ : (⟨yoneda.obj Y.1.toFunctor.reprX, isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ≅ closedSubspaceToSpace B S hS X Y :=
    ObjectProperty.isoMk _ Y.1.toFunctor.reprW
  let e₃ : (⟨yoneda.obj Z.1.toFunctor.reprX, isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ≅ closedSubspaceToSpace B S hS X Z :=
    ObjectProperty.isoMk _ Z.1.toFunctor.reprW
  have hpo := (isPushout_schemeTheoreticUnion B S hS X Y Z).of_iso e₁.symm e₂.symm e₃.symm
    (Iso.refl _) (f' := ObjectProperty.homMk (yoneda.map a₁))
    (g' := ObjectProperty.homMk (yoneda.map a₂))
    (inl' := e₂.hom ≫ ObjectProperty.homMk
      (Subfunctor.homOfLe (le_schemeTheoreticUnion_left B S hS X.2 Y Z)))
    (inr' := e₃.hom ≫ ObjectProperty.homMk
      (Subfunctor.homOfLe (le_schemeTheoreticUnion_right B S hS X.2 Y Z)))
    (ObjectProperty.hom_ext _ (by simp [e₁, e₂, a₁]))
    (ObjectProperty.hom_ext _ (by simp [e₁, e₃, a₂])) (by simp) (by simp)
  exact isRepresentable_of_natIso (yoneda.obj (fppfOverPushout s B hS hP))
    ((ObjectProperty.ι _).mapIso ((pushout_isPushout_algebraicSpaces s B hS
      Y.1.toFunctor.reprX.left.2 Z.1.toFunctor.reprX.left.2 I.1.toFunctor.reprX.left.2
      hP).isoIsPushout _ _ hpo))

/-! ### Stacks 0B7Z -/

/-- If `X` is not a scheme, no closed subspace of `X` carrying every point of `X` is a scheme. -/
private theorem not_isRepresentable_of_surjective_pointsMap_ι {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXnotScheme : ¬ X.IsRepresentable) {Z : Subfunctor X}
    (hZ : IsClosedSubspace B S hS Z)
    (hsurj : Function.Surjective (pointsMap B S hS Z.toFunctor Z.ι)) :
    ¬ Z.toFunctor.IsRepresentable := fun hrep =>
  hXnotScheme (isRepresentable_of_isClosedImmersion_of_bijective B S hS hZ.1 hX Z.ι hZ.2
    ⟨pointsMap_injective_of_mono B S hS _, hsurj⟩ hrep)

/-- An algebraic space which is not a scheme, all of whose proper closed subspaces are schemes,
is reduced. -/
private theorem hasEtaleLocalProperty_isReduced_of_forall_ne_top_isRepresentable
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hproper : ∀ Z : Subfunctor X, IsClosedSubspace B S hS Z → Z ≠ ⊤ →
      Z.toFunctor.IsRepresentable)
    (hXnotScheme : ¬ X.IsRepresentable) :
    HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsReduced Y) := by
  have hred := isClosedSubspace_reducedClosedSubspace B S hS X hX Set.univ isClosed_univ
  have htop : reduction B S hS X hX = ⊤ := by
    by_contra htop
    exact not_isRepresentable_of_surjective_pointsMap_ι B S hS hX hXnotScheme hred
      (surjective_pointsMap_ι_reduction B S hS X hX) (hproper _ hred htop)
  have hiso : IsIso (reduction B S hS X hX).ι := (Subfunctor.eq_top_iff_isIso _).mp htop
  obtain ⟨U, f, hsurj, hetale, hU⟩ := hasEtaleLocalProperty_isReduced_reduction B S hS X hX
  exact ⟨U, f ≫ (reduction B S hS X hX).ι,
    MorphismProperty.RespectsIso.postcomp _ (reduction B S hS X hX).ι f hsurj,
    MorphismProperty.RespectsIso.postcomp _ (reduction B S hS X hX).ι f hetale, hU⟩

/-- An algebraic space which is not a scheme, all of whose proper closed subspaces are schemes,
has irreducible underlying space. -/
private theorem irreducibleSpace_of_forall_ne_top_isRepresentable
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hproper : ∀ Z : Subfunctor X, IsClosedSubspace B S hS Z → Z ≠ ⊤ →
      Z.toFunctor.IsRepresentable)
    (hXnotScheme : ¬ X.IsRepresentable) :
    IrreducibleSpace (points B S hS X) := by
  classical
  have hnonempty : Nonempty (points B S hS X) := by
    by_contra h
    exact hXnotScheme (isRepresentable_of_surjective_pointsMap_schematicLocus B S hS hX
      fun x => (h ⟨x⟩).elim)
  refine { isPreirreducible_univ := ?_, toNonempty := hnonempty }
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro T₁ T₂ hT₁ hT₂ hcov
  by_contra hcon
  rw [not_or] at hcon
  have hrep : ∀ (T : Set (points B S hS X)) (hT : IsClosed T), ¬ Set.univ ⊆ T →
      (reducedClosedSubspace B S hS X hX T hT).toFunctor.IsRepresentable := fun T hT hc =>
    hproper _ (isClosedSubspace_reducedClosedSubspace B S hS X hX T hT) fun htop => by
      have := (Subfunctor.eq_top_iff_isIso _).mp htop
      exact hc fun x _ => range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT ▸
        pointsMap_surjective_of_isIso B S hS _ x
  have hsub : ∀ (T : Set (points B S hS X)) (hT : IsClosed T) (W : Subfunctor X),
      reducedClosedSubspace B S hS X hX T hT ≤ W →
        T ⊆ Set.range (pointsMap B S hS W.toFunctor W.ι) :=
    fun T hT W h => (range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT).symm ▸
      range_pointsMap_ι_subset_of_le B S hS h
  have hZ₁ := isClosedSubspace_reducedClosedSubspace B S hS X hX T₁ hT₁
  have hZ₂ := isClosedSubspace_reducedClosedSubspace B S hS X hX T₂ hT₂
  let W := schemeTheoreticUnion B S hS X hX ⟨_, hZ₁⟩ ⟨_, hZ₂⟩
  refine not_isRepresentable_of_surjective_pointsMap_ι B S hS hX hXnotScheme W.2 (fun x => ?_)
    (isRepresentable_schemeTheoreticUnion B S hS ⟨X, hX⟩ ⟨_, hZ₁⟩ ⟨_, hZ₂⟩ (hrep T₁ hT₁ hcon.1)
      (hrep T₂ hT₂ hcon.2))
  rcases hcov (Set.mem_univ x) with hx | hx
  · exact hsub T₁ hT₁ _ (le_schemeTheoreticUnion_left B S hS hX ⟨_, hZ₁⟩ ⟨_, hZ₂⟩) hx
  · exact hsub T₂ hT₂ _ (le_schemeTheoreticUnion_right B S hS hX ⟨_, hZ₁⟩ ⟨_, hZ₂⟩) hx

/-- **Stacks 0B7Z.** Let `X` be an algebraic space over `S` which is not a scheme, and assume
that every closed subspace `Z` of `X` with `Z ≠ ⊤` — that is, every *proper* closed subspace of
`X` — is a scheme. Then `X` is reduced and `|X|` is irreducible.

A closed subspace with every point of `X` cannot be a scheme, by the closed-immersion form of
Stacks 07VU. Applied to the reduction of `X` this makes the reduction the whole of `X`, which is
therefore reduced. Applied to the scheme-theoretic union of the reduced induced subspaces on two
proper closed subsets covering `|X|`, which is a scheme by Stacks 0CZ1 and Stacks 0EDP, it shows
that no such cover exists; and `|X|` is nonempty since a space without points is a scheme.

The source also assumes `X` quasi-compact and quasi-separated; the proof does not use either
assumption, so they are omitted. -/
@[stacks 0B7Z]
theorem hasEtaleLocalProperty_isReduced_and_irreducibleSpace_of_forall_ne_top_isRepresentable
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hproper : ∀ Z : Subfunctor X, IsClosedSubspace B S hS Z → Z ≠ ⊤ →
      Z.toFunctor.IsRepresentable)
    (hXnotScheme : ¬ X.IsRepresentable) :
    HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsReduced Y) ∧
      IrreducibleSpace (points B S hS X) :=
  ⟨hasEtaleLocalProperty_isReduced_of_forall_ne_top_isRepresentable B S hS hX hproper hXnotScheme,
    irreducibleSpace_of_forall_ne_top_isRepresentable B S hS hX hproper hXnotScheme⟩

end AlgebraicGeometry.Space

end
