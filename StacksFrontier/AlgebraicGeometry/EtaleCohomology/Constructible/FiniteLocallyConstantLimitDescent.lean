module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage

/-!
# Finite local constancy descends along a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of schemes with affine transition
morphisms. Stacks Tag 0GL2 asserts that the category of finite locally constant sheaves on
`X_étale` is the colimit of the categories of finite locally constant sheaves on the
`(X_i)_étale`, and likewise for finite locally constant abelian sheaves and, over a Noetherian
ring `Λ`, for finite type locally constant sheaves of `Λ`-modules.

The source deduces all three from Tag 09YU, the same assertion for *constructible* sheaves: full
faithfulness is inherited outright, and essential surjectivity needs the one geometric statement
that a constructible sheaf at a stage whose inverse image to `X` is finite locally constant is
already finite locally constant at a later stage. This file proves that statement, from the two
results the source invokes for it: Tag 0EYL, that an étale covering of `X` is refined by the
inverse image of a finite étale covering of some stage, and Tag 09YU over a member of that
covering, that two constructible sheaves on it with isomorphic inverse images to the
corresponding member over `X` become isomorphic at a later stage.

Combined with the reductions of the companion file
`Constructible/FiniteLocallyConstantLimitCategory.lean`
this gives the three clauses of Tag 0GL2 with Tags 0EYL and 09YU — results the source cites and
this library does not prove — as the only remaining hypotheses.

## Main definitions

* `AlgebraicGeometry.coneStageHom` and `AlgebraicGeometry.systemStageHom` — the projection from
  the vertex of a cone to a stage, and the transition morphism between two stages.
* `AlgebraicGeometry.IsTrivializedSmallEtaleSheaf` — a sheaf which becomes constant, with values
  satisfying a prescribed property, on a covering of every object of the small étale site. For
  finiteness of the value this is finite local constancy, and for finite generation it is local
  constancy of finite type.
* `AlgebraicGeometry.SmallEtaleStagesCoveringsRefine` — the form of Tag 0EYL used here: every
  covering of `X` in the small étale site is refined by the inverse image of a finite covering at
  a stage.
* `AlgebraicGeometry.SmallEtaleStagesMemberIso` — the form of Tag 09YU used here: over a member of
  a covering at a stage, two sheaves with the given property whose inverse images to the
  corresponding member over `X` are isomorphic have isomorphic inverse images at all later
  stages.

## Main results

* `AlgebraicGeometry.nonempty_constantSheafIso_baseChange_member_iff` — a trivialization over the
  base change of a member, read on the small étale site of that member as a scheme.
* `AlgebraicGeometry.smallEtaleStagesMemberDescend` — the trivialization of a sheaf at a stage
  over one member descends to all sufficiently late stages.
* `AlgebraicGeometry.smallEtaleStagesDescend_isTrivialized` — the geometric statement of Tag
  0GL2: trivializability descends to a finite stage.

## Implementation notes

The descent is proved for an arbitrary property of the constant values, so that one argument
covers finiteness — clauses (1) and (2) — and finite generation, clause (3).

A trivialization over a member of a covering is a condition on a *localized* site, where inverse
image along a morphism of the ambient site is not available. It is transported to the small étale
site of the member as a scheme by the slice equivalence, through
`AlgebraicGeometry.nonempty_constantSheafIso_over_iff`; there inverse image along a morphism of
schemes is available and the base change square can be used. This is the same device as in
`AlgebraicGeometry.nonempty_constantSheafIso_baseChange_over`.

Tag 09YU is used in the "eventually" form: once two sheaves become isomorphic at a stage they are
isomorphic at every later stage, since the later inverse image factors through the earlier one.
That form is what lets a finite covering be handled at a single stage, by directedness.

## References

* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t v u iu r

namespace AlgebraicGeometry

section Coverings

variable (B : BigEtaleSite.{u})

/-- The inverse image of a covering of the final object of the small étale site of `S` is a
covering of the final object of the small étale site of `T`, for `f : T ⟶ S`. -/
public theorem smallEtale_sieve_ofArrows_final_baseChange {S T : B.Scheme} (f : T ⟶ S)
    {K : Type (u + 1)} (V : K → SmallEtale B S.obj S.property)
    (g : ∀ k, V k ⟶ SmallEtale.final B S.obj S.property)
    (hg : Sieve.ofArrows V g ∈ SmallEtale.topology B S.obj S.property
      (SmallEtale.final B S.obj S.property)) :
    Sieve.ofArrows (fun k => (smallEtaleBaseChange B f).obj (V k))
        (fun k => (SmallEtale.finalIsTerminal B T.obj T.property).from
          ((smallEtaleBaseChange B f).obj (V k))) ∈
      SmallEtale.topology B T.obj T.property (SmallEtale.final B T.obj T.property) := by
  have hT := SmallEtale.finalIsTerminal B T.obj T.property
  have hcp : CoverPreserving (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property) (smallEtaleBaseChange B f) :=
    CoverPreserving.of_isContinuous _ _ _
  have hpush := hcp.cover_preserve hg
  rw [Sieve.functorPushforward_ofArrows] at hpush
  refine (SmallEtale.topology B T.obj T.property).superset_covering ?_
    ((SmallEtale.topology B T.obj T.property).pullback_stable
      (smallEtaleFinalBaseChangeIso B f).inv hpush)
  intro Z k hk
  have hk' : (Sieve.ofArrows (fun i => (smallEtaleBaseChange B f).obj (V i))
      (fun i => (smallEtaleBaseChange B f).map (g i))).arrows
        (k ≫ (smallEtaleFinalBaseChangeIso B f).inv) := hk
  obtain ⟨i, d, hd⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hk'
  refine (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i, d, ?_⟩
  calc k = (k ≫ (smallEtaleFinalBaseChangeIso B f).inv) ≫
        (smallEtaleFinalBaseChangeIso B f).hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = d ≫ ((smallEtaleBaseChange B f).map (g i) ≫
        (smallEtaleFinalBaseChangeIso B f).hom) := by rw [hd, Category.assoc]
    _ = d ≫ (SmallEtale.finalIsTerminal B T.obj T.property).from
          ((smallEtaleBaseChange B f).obj (V i)) := by
        rw [hT.hom_ext ((smallEtaleBaseChange B f).map (g i) ≫
          (smallEtaleFinalBaseChangeIso B f).hom)
          ((SmallEtale.finalIsTerminal B T.obj T.property).from
            ((smallEtaleBaseChange B f).obj (V i)))]

end Coverings

section Stages

/-- The projection from the vertex of a cone over an inverse system of schemes to its `i`-th
stage, as a morphism of the big étale site. -/
public abbrev coneStageHom (B : BigEtaleSite.{u}) {I : Type iu} [Preorder I]
    (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt) (i : I) :
    B.obj c.pt hX ⟶ Dg.obj (op i) :=
  ObjectProperty.homMk (c.π.app (op i))

/-- The transition morphism from the `j`-th to the `i`-th stage of an inverse system of schemes
indexed by a preorder, for `i ≤ j`. -/
public abbrev systemStageHom (B : BigEtaleSite.{u}) {I : Type iu} [Preorder I]
    (Dg : Iᵒᵖ ⥤ B.Scheme) {i j : I} (h : i ≤ j) : Dg.obj (op j) ⟶ Dg.obj (op i) :=
  Dg.map (homOfLE h).op

/-- The projection to a stage factors through the projection to any later stage. -/
public theorem coneStageHom_comp (B : BigEtaleSite.{u}) {I : Type iu} [Preorder I]
    (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)
    {i j : I} (h : i ≤ j) :
    coneStageHom B Dg c hX j ≫ systemStageHom B Dg h = coneStageHom B Dg c hX i :=
  B.inclusion.map_injective (c.w (homOfLE h).op)

/-- The transition morphisms of an inverse system compose. -/
public theorem systemStageHom_comp (B : BigEtaleSite.{u}) {I : Type iu} [Preorder I]
    (Dg : Iᵒᵖ ⥤ B.Scheme) {i j k : I} (h₁ : i ≤ j) (h₂ : j ≤ k) :
    systemStageHom B Dg h₂ ≫ systemStageHom B Dg h₁ = systemStageHom B Dg (h₁.trans h₂) := by
  rw [← Dg.map_comp]
  rfl

end Stages

section Trivialized

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [hra : ∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) A]

/-- Weak sheafification on the small étale site of an object of a big étale site, from weak
sheafification on the localizations of those sites: the site is the localization at its own final
object. -/
public instance hasWeakSheafify_smallEtale_of_scheme (X : B.Scheme) :
    HasWeakSheafify (SmallEtale.topology B X.obj X.property) A :=
  hasWeakSheafify_smallEtale_of_over B X.obj X.property
    (SmallEtale.final B X.obj X.property) A

/-- Weak sheafification on the localization of the small étale site of a scheme presented
together with a proof that the site contains it. Instance search cannot match this spelling
against the one for an object of the site, since that would require solving `?X.obj ≡ S` for a
metavariable `?X`; a cone over a diagram of schemes presents its vertex in this second way. -/
public instance hasWeakSheafify_over_of_contains {S : Scheme.{u}} (hS : B.Contains S)
    (V : SmallEtale B S hS) :
    HasWeakSheafify ((SmallEtale.topology B S hS).over V) A :=
  (inferInstance : HasWeakSheafify
    ((SmallEtale.topology B (B.obj S hS).obj (B.obj S hS).property).over V) A)

/-- A sheaf on the small étale site of `X` is *trivialized with values satisfying `Q`* when every
object of the site has a covering on each member of which the sheaf restricts to a constant sheaf
whose value satisfies `Q`.

For `Q` finiteness of the underlying type this is
`Stacks.ConstantSheaf.IsFiniteLocallyConstant`, and for `Q` finite generation of a module it is
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant`. -/
public def IsTrivializedSmallEtaleSheaf (Q : A → Prop) : SmallEtaleSheafProperty B A :=
  fun X F => ∀ U : SmallEtale B X.obj X.property,
    ∃ (K : Type (u + 1)) (V : K → SmallEtale B X.obj X.property) (g : ∀ k, V k ⟶ U),
      Sieve.ofArrows V g ∈ SmallEtale.topology B X.obj X.property U ∧ ∀ k,
        ∃ E : A, Q E ∧ Nonempty
          ((constantSheaf ((SmallEtale.topology B X.obj X.property).over (V k)) A).obj E ≅
            ((SmallEtale.topology B X.obj X.property).overPullback A (V k)).obj F)

/-- Inverse image along `g` followed by inverse image along `f` is inverse image along any `h`
equal to `f ≫ g`. -/
private def pullbackCompIsoOfEq {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h) (F : Sheaf (SmallEtale.topology B Z.obj Z.property) A) :
    (smallEtaleSheafPullback B A f).obj ((smallEtaleSheafPullback B A g).obj F) ≅
      (smallEtaleSheafPullback B A h).obj F :=
  ((smallEtaleSheafPullbackCompIso B X Y Z f g A).app F) ≪≫
    eqToIso (congrArg (fun m => (smallEtaleSheafPullback B A m).obj F) e)

/-- **A trivialization over the base change of a member, read on the small étale site of that
member as a scheme.** The restriction of the inverse image of `G` along `f` to the localization at
the base change of `W` is the constant sheaf on `E` exactly when the inverse images of the
constant sheaf on `E` and of the restriction of `G` to `W` along the base change projection are
isomorphic.

Both sides are the same trivialization: the slice equivalence
`AlgebraicGeometry.nonempty_constantSheafIso_over_iff` replaces the localized site by the small
étale site of the base-changed member, and there the two ways around the base change square agree
by the composition law `AlgebraicGeometry.smallEtaleSheafPullbackCompIso`. -/
public theorem nonempty_constantSheafIso_baseChange_member_iff {S T : B.Scheme} (f : T ⟶ S)
    (W : SmallEtale B S.obj S.property)
    (G : Sheaf (SmallEtale.topology B S.obj S.property) A) (E : A) :
    Nonempty ((constantSheaf ((SmallEtale.topology B T.obj T.property).over
          ((smallEtaleBaseChange B f).obj W)) A).obj E ≅
        ((SmallEtale.topology B T.obj T.property).overPullback A
          ((smallEtaleBaseChange B f).obj W)).obj
          ((smallEtaleSheafPullback B A f).obj G)) ↔
      Nonempty ((smallEtaleSheafPullback B A (pullback.fst W.obj.hom f)).obj
            ((constantSheaf
              (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).obj E) ≅
          (smallEtaleSheafPullback B A (pullback.fst W.obj.hom f)).obj
            ((smallEtaleSheafPullback B A W.obj.hom).obj G)) := by
  have hadj := hra W.obj.left ((smallEtaleBaseChange B f).obj W).obj.left
    (pullback.fst W.obj.hom f)
  have hsq : ((smallEtaleBaseChange B f).obj W).obj.hom ≫ f =
      pullback.fst W.obj.hom f ≫ (W.obj.hom : W.obj.left ⟶ S) :=
    (pullback.condition (f := (W.obj.hom : W.obj.left ⟶ S)) (g := f)).symm
  have chain :
      (smallEtaleSheafPullback B A ((smallEtaleBaseChange B f).obj W).obj.hom).obj
          ((smallEtaleSheafPullback B A f).obj G) ≅
        (smallEtaleSheafPullback B A (pullback.fst W.obj.hom f)).obj
          ((smallEtaleSheafPullback B A W.obj.hom).obj G) :=
    pullbackCompIsoOfEq B A _ f _ hsq G ≪≫
      (pullbackCompIsoOfEq B A (pullback.fst W.obj.hom f) W.obj.hom _ rfl G).symm
  have constIso :
      (smallEtaleSheafPullback B A (pullback.fst W.obj.hom f)).obj
          ((constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).obj E) ≅
        (constantSheaf (SmallEtale.topology B ((smallEtaleBaseChange B f).obj W).obj.left.obj
          ((smallEtaleBaseChange B f).obj W).obj.left.property) A).obj E :=
    (smallEtaleSheafPullbackConstantSheafIso B
      (T := ((smallEtaleBaseChange B f).obj W).obj.left) (pullback.fst W.obj.hom f) A).app E
  rw [nonempty_constantSheafIso_over_iff B T.obj T.property
    ((smallEtaleBaseChange B f).obj W) A _ E]
  exact ⟨fun ⟨e⟩ => ⟨constIso ≪≫ e ≪≫ chain⟩,
    fun ⟨e⟩ => ⟨constIso.symm ≪≫ e ≪≫ chain.symm⟩⟩

end Trivialized

section Descent

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [hra : ∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) A]
  {I : Type iu} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- **Stacks 0EYL, in the form the proof of Tag 0GL2 uses it.** Every covering of the final
object of the small étale site of the vertex is refined by the inverse image of a finite covering
of the final object at some stage beyond a prescribed one. -/
public def SmallEtaleStagesCoveringsRefine : Prop :=
  ∀ (i : I) (K : Type (u + 1)) (V : K → SmallEtale B c.pt hX)
    (g : ∀ k, V k ⟶ SmallEtale.final B c.pt hX),
    Sieve.ofArrows V g ∈ SmallEtale.topology B c.pt hX (SmallEtale.final B c.pt hX) →
    ∃ (j : I) (_ : i ≤ j) (K' : Type (u + 1)) (_ : Finite K')
      (W : K' → SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
      (g' : ∀ k, W k ⟶ SmallEtale.final B (Dg.obj (op j)).obj (Dg.obj (op j)).property),
      Sieve.ofArrows W g' ∈
        SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property
          (SmallEtale.final B (Dg.obj (op j)).obj (Dg.obj (op j)).property) ∧
      ∀ k, ∃ m : K, Nonempty
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj (W k) ⟶ V m)

/-- **Stacks 09YU over a member of a covering, in the form the proof of Tag 0GL2 uses it.** For a
member `W` of the small étale site at a stage, two sheaves on the small étale site of `W` with the
property `P` whose inverse images to the base change of `W` over the vertex are isomorphic have
isomorphic inverse images to the base change of `W` at every sufficiently late stage.

The conclusion is stated for all later stages rather than for one: an isomorphism at a stage
pulls back to one at every stage beyond it, and it is that form which lets finitely many members
be handled at a single stage. -/
public def SmallEtaleStagesMemberIso (P : SmallEtaleSheafProperty B A) : Prop :=
  ∀ (j : I) (W : SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
    (F G : Sheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A),
    P W.obj.left F → P W.obj.left G →
    Nonempty
      ((smallEtaleSheafPullback B A
          (pullback.fst W.obj.hom (coneStageHom B Dg c hX j))).obj F ≅
        (smallEtaleSheafPullback B A
          (pullback.fst W.obj.hom (coneStageHom B Dg c hX j))).obj G) →
    ∃ (j' : I) (hjj' : j ≤ j'), ∀ (j'' : I) (h' : j' ≤ j''), Nonempty
      ((smallEtaleSheafPullback B A
          (pullback.fst W.obj.hom (systemStageHom B Dg (hjj'.trans h')))).obj F ≅
        (smallEtaleSheafPullback B A
          (pullback.fst W.obj.hom (systemStageHom B Dg (hjj'.trans h')))).obj G)

variable {B A Dg c hX}

/-- **The trivialization over one member descends.** If the inverse image to the vertex of a
`P`-sheaf `G` at the stage `j` restricts to the constant sheaf on `E` over the base change of the
member `W`, and the constant sheaf on `E` has the property `P`, then the same holds at every
sufficiently late stage.

This is the application of Tag 09YU the source makes: the two sheaves compared on the small étale
site of `W` are the restriction of `G` and the constant sheaf on `E`. -/
public theorem smallEtaleStagesMemberDescend {P : SmallEtaleSheafProperty B A}
    (hPpb : ∀ (S T : B.Scheme) (f : T ⟶ S)
      (F : Sheaf (SmallEtale.topology B S.obj S.property) A),
      P S F → P T ((smallEtaleSheafPullback B A f).obj F))
    (h2 : SmallEtaleStagesMemberIso B A Dg c hX P) (j : I)
    (W : SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
    (G : Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj (Dg.obj (op j)).property) A)
    (hPG : P (Dg.obj (op j)) G) (E : A)
    (hPE : P W.obj.left
      ((constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).obj E))
    (hiso : Nonempty ((constantSheaf ((SmallEtale.topology B c.pt hX).over
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj W)) A).obj E ≅
      ((SmallEtale.topology B c.pt hX).overPullback A
        ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj W)).obj
        ((smallEtaleSheafPullback B A (coneStageHom B Dg c hX j)).obj G))) :
    ∃ (j' : I) (hjj' : j ≤ j'), ∀ (j'' : I) (h' : j' ≤ j''), Nonempty
      ((constantSheaf ((SmallEtale.topology B (Dg.obj (op j'')).obj
            (Dg.obj (op j'')).property).over
          ((smallEtaleBaseChange B (systemStageHom B Dg (hjj'.trans h'))).obj W)) A).obj E ≅
        ((SmallEtale.topology B (Dg.obj (op j'')).obj (Dg.obj (op j'')).property).overPullback A
            ((smallEtaleBaseChange B (systemStageHom B Dg (hjj'.trans h'))).obj W)).obj
          ((smallEtaleSheafPullback B A (systemStageHom B Dg (hjj'.trans h'))).obj G)) := by
  obtain ⟨j', hjj', hj'⟩ := h2 j W
    ((constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).obj E)
    ((smallEtaleSheafPullback B A W.obj.hom).obj G)
    hPE (hPpb _ _ W.obj.hom G hPG)
    ((nonempty_constantSheafIso_baseChange_member_iff B A
      (coneStageHom B Dg c hX j) W G E).mp hiso)
  refine ⟨j', hjj', fun j'' h' => ?_⟩
  exact (nonempty_constantSheafIso_baseChange_member_iff B A
    (systemStageHom B Dg (hjj'.trans h')) W G E).mpr (hj' j'' h')

/-- **The geometric statement of Tag 0GL2.** A sheaf with the property `P` at a stage whose
inverse image to the vertex is trivialized with values satisfying `Q` is trivialized with values
satisfying `Q` at some later stage.

The proof is the source's: a trivializing covering of the vertex is refined by the inverse image
of a finite covering at a stage, over each of its members the trivialization descends to all
sufficiently late stages by Tag 09YU, a single stage serves all members by directedness and
finiteness, and the inverse image of the covering there is a covering of the final object, which
trivializes over every object. -/
public theorem smallEtaleStagesDescend_isTrivialized [Nonempty I] [IsDirected I (· ≤ ·)]
    {P : SmallEtaleSheafProperty B A} {Q : A → Prop}
    (hPpb : ∀ (S T : B.Scheme) (f : T ⟶ S)
      (F : Sheaf (SmallEtale.topology B S.obj S.property) A),
      P S F → P T ((smallEtaleSheafPullback B A f).obj F))
    (hPconst : ∀ (S : B.Scheme) (E : A), Q E →
      P S ((constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E))
    (h1 : SmallEtaleStagesCoveringsRefine B Dg c hX)
    (h2 : SmallEtaleStagesMemberIso B A Dg c hX P) :
    SmallEtaleStagesDescend B A Dg c hX P (IsTrivializedSmallEtaleSheaf B A Q) := by
  classical
  intro i F hPF hQF
  obtain ⟨K, V, fV, hfV, hcV⟩ := hQF (SmallEtale.final B c.pt hX)
  obtain ⟨j, hij, K', hK', W, gW, hgW, href⟩ := h1 i K V fV hfV
  have := Fintype.ofFinite K'
  -- the sheaf at the stage `j`, and the identification of its inverse image to the vertex
  set G := (smallEtaleSheafPullback B A (systemStageHom B Dg hij)).obj F with hGdef
  have hGproj : (smallEtaleSheafPullback B A (coneStageHom B Dg c hX j)).obj G ≅
      (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).obj F :=
    pullbackCompIsoOfEq B A _ _ _ (coneStageHom_comp B Dg c hX hij) F
  -- over each member of the descended covering the trivialization descends
  have step : ∀ k : K', ∃ (E : A) (_ : Q E) (j' : I) (hjj' : j ≤ j'),
      ∀ (j'' : I) (h' : j' ≤ j''), Nonempty
        ((constantSheaf ((SmallEtale.topology B (Dg.obj (op j'')).obj
              (Dg.obj (op j'')).property).over
            ((smallEtaleBaseChange B (systemStageHom B Dg (hjj'.trans h'))).obj (W k))) A).obj E ≅
          ((SmallEtale.topology B (Dg.obj (op j'')).obj
              (Dg.obj (op j'')).property).overPullback A
              ((smallEtaleBaseChange B (systemStageHom B Dg (hjj'.trans h'))).obj (W k))).obj
            ((smallEtaleSheafPullback B A (systemStageHom B Dg (hjj'.trans h'))).obj G)) := by
    intro k
    obtain ⟨m, ⟨φ⟩⟩ := href k
    obtain ⟨E, hE, ⟨e⟩⟩ := hcV m
    refine ⟨E, hE, ?_⟩
    refine smallEtaleStagesMemberDescend hPpb h2 j (W k) G
      (hPpb _ _ (systemStageHom B Dg hij) F hPF) E (hPconst _ E hE) ⟨?_⟩
    refine Stacks.ConstantSheaf.Localization.overPullbackIsoOfMap
      (SmallEtale.topology B c.pt hX) A φ _ E e ≪≫ ?_
    exact ((SmallEtale.topology B c.pt hX).overPullback A
      ((smallEtaleBaseChange B (coneStageHom B Dg c hX j)).obj (W k))).mapIso hGproj.symm
  choose E hE jj hjj hcone using step
  -- one stage serves every member
  obtain ⟨M, hM⟩ := Finset.exists_le (insert j (Finset.univ.image jj))
  have hjM : j ≤ M := hM j (Finset.mem_insert_self _ _)
  refine ⟨M, hij.trans hjM, ?_⟩
  have hGM : (smallEtaleSheafPullback B A (systemStageHom B Dg hjM)).obj G ≅
      (smallEtaleSheafPullback B A (systemStageHom B Dg (hij.trans hjM))).obj F :=
    pullbackCompIsoOfEq B A _ _ _ (systemStageHom_comp B Dg hij hjM) F
  have hcov := smallEtale_sieve_ofArrows_final_baseChange B (systemStageHom B Dg hjM) W gW hgW
  intro U
  refine Stacks.ConstantSheaf.Localization.exists_trivializing_cover
    (SmallEtale.topology B (Dg.obj (op M)).obj (Dg.obj (op M)).property) A
    (SmallEtale.finalIsTerminal B (Dg.obj (op M)).obj (Dg.obj (op M)).property) _ Q
    (X := fun k => (smallEtaleBaseChange B (systemStageHom B Dg hjM)).obj (W k))
    (f := fun k => (SmallEtale.finalIsTerminal B (Dg.obj (op M)).obj
      (Dg.obj (op M)).property).from _) hcov (fun k => ?_) U
  obtain ⟨e⟩ := hcone k M (hM (jj k)
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k))))
  exact ⟨E k, hE k, ⟨e ≪≫ ((SmallEtale.topology B (Dg.obj (op M)).obj
    (Dg.obj (op M)).property).overPullback A
    ((smallEtaleBaseChange B (systemStageHom B Dg hjM)).obj (W k))).mapIso hGM⟩⟩

end Descent

section ConstantSheaves

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [hra : ∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) A]

/-- **A constant sheaf is trivialized with its own value.** The inverse image of a constant sheaf
along the structure morphism of an object of the small étale site is constant with the same value,
so the one-member covering of an object by its identity already trivializes it. -/
public theorem isTrivialized_constantSheaf (Q : A → Prop) (X : B.Scheme) (E : A) (hQ : Q E) :
    IsTrivializedSmallEtaleSheaf B A Q X
      ((constantSheaf (SmallEtale.topology B X.obj X.property) A).obj E) := by
  intro U
  refine ⟨PUnit.{u + 2}, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ⟨E, hQ, ?_⟩⟩
  · have htop : Sieve.ofArrows (fun _ : PUnit.{u + 2} => U) (fun _ => 𝟙 U) = ⊤ :=
      Sieve.id_mem_iff_eq_top.mp
        ((Sieve.mem_ofArrows_iff _ _ _).mpr ⟨PUnit.unit, 𝟙 U, by simp⟩)
    rw [htop]
    exact (SmallEtale.topology B X.obj X.property).top_mem U
  · exact (nonempty_constantSheafIso_over_iff B X.obj X.property U A _ E).mpr
      ⟨((smallEtaleSheafPullbackConstantSheafIso B U.obj.hom A).app E).symm⟩

end ConstantSheaves

section Clauses

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  {FA : A → A → Type*} {CA : A → Type w} [∀ E E', FunLike (FA E E') (CA E) (CA E')]
  [ConcreteCategory.{w} A FA]
  [hra : ∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) A]

omit hra in
/-- Trivializability with finite values is finite local constancy. -/
public theorem isTrivialized_iff_isFiniteLocallyConstant (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) A) :
    IsTrivializedSmallEtaleSheaf B A (fun E => Finite (CA E)) X F ↔
      Stacks.ConstantSheaf.IsFiniteLocallyConstant (FD := FA) (CD := CA)
        (SmallEtale.topology B X.obj X.property) F :=
  ⟨fun h => ⟨h⟩, fun h => h.exists_finite_cover⟩

variable {I : Type iu} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

end Clauses

section ModuleClause

variable (B : BigEtaleSite.{u}) (R : Type r) [CommRing R] [IsNoetherianRing R]
  [hra : ∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) (ModuleCat.{w} R)]
  {I : Type iu} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

end ModuleClause

end AlgebraicGeometry

end
