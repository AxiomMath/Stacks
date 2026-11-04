module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.UnramifiedEtaleDescent

/-!
# The converse half of Stacks 04CY is false for arbitrary set-valued functors

Stacks 04CY states its parts (5) and (6) for arbitrary functors
`F, G, H : (Sch/S)^{opp}_{fppf} → Sets`: if `a : F → G` is representable, surjective and étale
and `b ∘ a` is formally unramified (resp. formally étale), then so is `b`. The tag's own proof of
(5) ends "and hence `f = g` as `W' → T'` is an étale covering", which is étale descent for `G`
along the cover `W' → T'`; an arbitrary set-valued functor does not satisfy it.

This file shows that no proof can avoid that step: the arbitrary-functor form of parts (5) and
(6) is **false**. Given, in a big fppf site over `S`, a square-zero closed immersion
`i : T ⟶ T'` of affines admitting no retraction, and an étale surjection `π : X ⟶ T'` admitting
no section, `AlgebraicGeometry.Space.DoubledSection.doubled` is the presheaf obtained from the
functor of points of `T'` by doubling every section that factors through neither `X` nor `T`. It
receives a representable, surjective, étale transformation from the functor of points of `X`
whose composite with the projection to the functor of points of `T'` is `yoneda.map π`, hence
formally étale; the projection itself is not even formally unramified, because the two labels of
`𝟙 T'` restrict to the same section over `T` and have the same image in the functor of points of
`T'`.

So the separatedness hypothesis of
`AlgebraicGeometry.Space.formallyUnramified_of_comp_of_isSeparated` and the
sheaf hypothesis on the intermediate presheaf in
`AlgebraicGeometry.Space.formallyEtale_of_comp_of_isSeparated` cannot be dropped. The target
presheaf of the counterexample is representable, hence a sheaf, so the counterexample leaves the
narrowing of the hypothesis on the target presheaf untouched.

## Main definitions

* `AlgebraicGeometry.Space.DoubledSection.Factored` is the subfunctor of the functor of points
  of `T'` cut out by factoring through `X` or through `T`.
* `AlgebraicGeometry.Space.DoubledSection.doubled` is the functor of points of `T'` with every
  section outside that subfunctor doubled.
* `AlgebraicGeometry.Space.DoubledSection.situation` packages the counterexample as a
  representable, surjective, étale situation.

## Main results

* `AlgebraicGeometry.Space.DoubledSection.isPullback_fromSource`: every base change of the
  transformation from the functor of points of `X` along a section of `doubled` is represented
  by a fibre product in the site, so that transformation is representable, and its represented
  base changes are the base changes of `π`.
* `AlgebraicGeometry.Space.DoubledSection.formallyEtale_fromSource_comp_toTarget`: the composite
  transformation is formally étale.
* `AlgebraicGeometry.Space.DoubledSection.not_formallyUnramified_toTarget`: the second
  transformation is not formally unramified.
* `AlgebraicGeometry.Space.DoubledSection.exists_not_formallyUnramified_of_comp`: parts (5) and
  (6) of Stacks 04CY fail for arbitrary set-valued functors.

## Implementation notes

The doubling is implemented as a subtype of pairs: a section of `doubled` over `V` is a morphism
`f : V ⟶ T'` together with a proposition, required to be false whenever `f` factors through `X`
or through `T`. Restricting along `u : W ⟶ V` conjoins the proposition with the requirement that
`u ≫ f` still factor through neither, which is what makes the assignment functorial — the two
functor laws use that `Factored` is closed under precomposition, and nothing else. Equality of
sections is equality of the underlying pairs, by proof irrelevance, so the functor laws and the
naturality squares reduce to one equality of morphisms and one equality of propositions.

Representability of the transformation from the functor of points of `X` is where the choice of
`Factored` is forced. The base change along a section `(f, c)` of `doubled` over `V` is computed
pointwise: a pair consisting of `ξ : W ⟶ X` and `u : W ⟶ V` lies in it when `ξ ≫ π = u ≫ f` and
the label of `u ≫ f` is false, and the first of those conditions already puts `u ≫ f` in
`Factored`, hence forces the second. So the base change is the fibre product `X ×_{T'} V`
whatever the label is, and the represented base changes of the transformation are exactly the
base changes of `π`. Had `Factored` not contained the image of the functor of points of `X`, the
base change along a doubled section would have been a subfunctor of that fibre product cut out
by a condition that is not local, hence not representable.

The two no-retraction hypotheses are what make the doubled label available over `T'` itself:
they say exactly that `𝟙 T'` lies outside `Factored`. The one for `i` follows from `i` not being
an isomorphism of schemes, which is `AlgebraicGeometry.Space.DoubledSection.ne_id_of_retraction`;
the one for `π` is the statement that the étale covering `π` is not split, which is the
nontriviality of the étale topology on `T'` that the descent step in the tag's proof consumes.

## References

* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace DoubledSection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {T T' X : BigFppfOver B S hS} (i : T ⟶ T') (π : X ⟶ T')

/-- The sections of the functor of points of `T'` over `V` that factor through `X` or
through `T`. -/
public def Factored (V : BigFppfOver B S hS) : Set (V ⟶ T') :=
  {f | (∃ ξ : V ⟶ X, ξ ≫ π = f) ∨ (∃ g : V ⟶ T, g ≫ i = f)}

/-- `Factored` is a subfunctor: it is closed under precomposition. -/
public theorem factored_comp {V W : BigFppfOver B S hS} (u : W ⟶ V) {f : V ⟶ T'}
    (hf : f ∈ Factored i π V) : u ≫ f ∈ Factored i π W := by
  rcases hf with ⟨ξ, hξ⟩ | ⟨g, hg⟩
  · exact Or.inl ⟨u ≫ ξ, by rw [Category.assoc, hξ]⟩
  · exact Or.inr ⟨u ≫ g, by rw [Category.assoc, hg]⟩

/-- Any section factoring through `π` lies in `Factored`. -/
public theorem factored_of_comp_pi {V : BigFppfOver B S hS} (ξ : V ⟶ X) :
    ξ ≫ π ∈ Factored i π V := Or.inl ⟨ξ, rfl⟩

/-- Any section factoring through `i` lies in `Factored`. -/
public theorem factored_of_comp_i {V : BigFppfOver B S hS} (g : V ⟶ T) :
    g ≫ i ∈ Factored i π V := Or.inr ⟨g, rfl⟩

/-- A section over `V` of the doubled functor of points of `T'`: a morphism `V ⟶ T'` together
with a label, a proposition required to be false on the sections that do factor through `X` or
through `T`. -/
public abbrev Doubled (V : BigFppfOver B S hS) : Type u :=
  {p : (V ⟶ T') × Prop // p.2 → p.1 ∉ Factored i π V}

/-- Restriction of a section of `Doubled` along a morphism: the label is conjoined with the
requirement that the restricted section still factor through neither `X` nor `T`. -/
public def Doubled.restrict {V W : BigFppfOver B S hS} (u : W ⟶ V) (p : Doubled i π V) :
    Doubled i π W :=
  ⟨(u ≫ p.1.1, p.1.2 ∧ u ≫ p.1.1 ∉ Factored i π W), fun h => h.2⟩

/-- The underlying morphism of a restricted section is the composite with the restriction map. -/
@[simp]
public theorem Doubled.restrict_fst {V W : BigFppfOver B S hS} (u : W ⟶ V)
    (p : Doubled i π V) : (Doubled.restrict i π u p).1.1 = u ≫ p.1.1 := rfl

/-- Restriction along the identity is the identity. -/
public theorem Doubled.restrict_id {V : BigFppfOver B S hS} (p : Doubled i π V) :
    Doubled.restrict i π (𝟙 V) p = p := by
  refine Subtype.ext (Prod.ext (Category.id_comp _) ?_)
  refine propext ⟨And.left, fun h => ⟨h, ?_⟩⟩
  rw [Category.id_comp]
  exact p.2 h

/-- Restriction along a composite is the composite of the restrictions. -/
public theorem Doubled.restrict_comp {V W Z : BigFppfOver B S hS} (u : W ⟶ V) (v : Z ⟶ W)
    (p : Doubled i π V) :
    Doubled.restrict i π v (Doubled.restrict i π u p) = Doubled.restrict i π (v ≫ u) p := by
  have hassoc : (v ≫ u) ≫ p.1.1 = v ≫ u ≫ p.1.1 := Category.assoc _ _ _
  refine Subtype.ext (Prod.ext hassoc.symm ?_)
  change ((p.1.2 ∧ u ≫ p.1.1 ∉ Factored i π W) ∧ v ≫ u ≫ p.1.1 ∉ Factored i π Z) =
      (p.1.2 ∧ (v ≫ u) ≫ p.1.1 ∉ Factored i π Z)
  rw [hassoc]
  refine propext ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
  exact fun hmem => h.2 (factored_comp i π v hmem)

/-- The functor of points of `T'` with every section outside `Factored` doubled. -/
public def doubled : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj V := Doubled i π V.unop
  map u := ↾Doubled.restrict i π u.unop
  map_id V := by
    refine TypeCat.homEquiv.injective (funext fun p => ?_)
    exact Doubled.restrict_id i π p
  map_comp u v := by
    refine TypeCat.homEquiv.injective (funext fun p => ?_)
    exact (Doubled.restrict_comp i π u.unop v.unop p).symm

/-- The action of `doubled` on a morphism is `Doubled.restrict`. -/
@[simp]
public theorem doubled_map {V W : BigFppfOver B S hS} (u : W ⟶ V)
    (p : (doubled i π).obj (op V)) :
    (doubled i π).map u.op p = Doubled.restrict i π u p := rfl

/-- The underlying section of `T'` of a restricted section of `doubled`. -/
public theorem doubled_map_fst {V W : BigFppfOver B S hS} (u : W ⟶ V)
    (p : (doubled i π).obj (op V)) :
    ((doubled i π).map u.op p).1.1 = u ≫ p.1.1 := rfl

/-- The transformation from the functor of points of `X`, carrying a morphism to `X` to its
composite with `π`, labelled false. -/
public def fromSource : yoneda.obj X ⟶ doubled i π where
  app V := ↾fun ξ : V.unop ⟶ X => (⟨(ξ ≫ π, False), fun h => h.elim⟩ : Doubled i π V.unop)
  naturality {V W} u := by
    refine TypeCat.homEquiv.injective (funext fun ξ => ?_)
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Category.assoc _ _ _
    · exact propext ⟨fun h => h.elim, fun h => h.1⟩

/-- The transformation to the functor of points of `T'`, forgetting the label. -/
public def toTarget : doubled i π ⟶ yoneda.obj T' where
  app V := ↾fun p : Doubled i π V.unop => p.1.1
  naturality {V W} u := by
    refine TypeCat.homEquiv.injective (funext fun p => ?_)
    rfl

/-- `fromSource` carries `ξ : V ⟶ X` to the composite `ξ ≫ π`, labelled false. -/
@[simp]
public theorem fromSource_app {V : BigFppfOver B S hS} (ξ : V ⟶ X) :
    (fromSource i π).app (op V) ξ =
      (⟨(ξ ≫ π, False), fun h => h.elim⟩ : Doubled i π V) := rfl

/-- `toTarget` forgets the label of a section of `doubled`. -/
@[simp]
public theorem toTarget_app {V : BigFppfOver B S hS} (p : (doubled i π).obj (op V)) :
    (toTarget i π).app (op V) p = p.1.1 := rfl

/-- The composite of the two transformations is the morphism of functors of points
induced by `π`. -/
public theorem fromSource_comp_toTarget :
    fromSource i π ≫ toTarget i π = yoneda.map π := by
  ext V ξ
  rfl

/-- The section of `T'` underlying a section of `doubled` over `V`. -/
public def baseSection {V : BigFppfOver B S hS} (g : yoneda.obj V ⟶ doubled i π) : V ⟶ T' :=
  (g.app (op V) (𝟙 V)).1.1

/-- A section of `doubled` over `V` has, over any `W ⟶ V`, the restriction of its underlying
section of `T'`. -/
public theorem app_fst {V W : BigFppfOver B S hS} (g : yoneda.obj V ⟶ doubled i π)
    (u : W ⟶ V) : (g.app (op W) u).1.1 = u ≫ baseSection i π g := by
  have h := g.naturality_apply u.op (𝟙 V)
  have hid : (yoneda.obj V).map u.op (𝟙 V) = u := by simp
  rw [hid] at h
  rw [h, doubled_map_fst]
  rfl

/-- Pulling a base-change-stable property of schemes back along the underlying-scheme functor
gives a base-change-stable property of the site. -/
private theorem isStableUnderBaseChange_inverseImage
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  let := hpres
  ⟨fun hsq hb =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := P) (hsq.map (BigFppfOver.toScheme B S hS)) hb⟩

variable [HasPullbacks (BigFppfOver B S hS)]

/-- Every base change of `fromSource` along a section of `doubled` whose underlying section of
`T'` is `f` is represented by the fibre product of `π` with `f`: the label plays no role, because
a pair whose two components agree over `T'` already lies in `Factored`. -/
public theorem isPullback_fromSource_of_baseSection {V : BigFppfOver B S hS}
    (g : yoneda.obj V ⟶ doubled i π) (f : V ⟶ T')
    (hf : ∀ {W : BigFppfOver B S hS} (u : W ⟶ V), (g.app (op W) u).1.1 = u ≫ f) :
    IsPullback (yoneda.map (pullback.fst π f)) (yoneda.map (pullback.snd π f))
      (fromSource i π) g := by
  refine IsPullback.of_forall_isPullback_app fun W => ?_
  obtain ⟨W⟩ := W
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · refine TypeCat.homEquiv.injective (funext fun w => ?_)
    have hcomm : (w ≫ pullback.fst π f) ≫ π = (w ≫ pullback.snd π f) ≫ f := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (fromSource i π).app (op W) (w ≫ pullback.fst π f) =
      g.app (op W) (w ≫ pullback.snd π f)
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change (w ≫ pullback.fst π f) ≫ π = (g.app (op W) (w ≫ pullback.snd π f)).1.1
      rw [hf]
      exact hcomm
    · change (False : Prop) = (g.app (op W) (w ≫ pullback.snd π f)).1.2
      refine propext ⟨fun h => h.elim, fun h => ?_⟩
      refine absurd ?_ ((g.app (op W) (w ≫ pullback.snd π f)).2 h)
      rw [hf, ← hcomm]
      exact factored_of_comp_pi i π _
  · intro w₁ w₂ h
    exact pullback.hom_ext h.1 h.2
  · intro ξ u h
    have h1 : ((fromSource i π).app (op W) ξ).1.1 = (g.app (op W) u).1.1 := by rw [h]
    have hcomm : ξ ≫ π = u ≫ f := by rw [hf] at h1; exact h1
    exact ⟨pullback.lift ξ u hcomm, pullback.lift_fst ξ u hcomm, pullback.lift_snd ξ u hcomm⟩

/-- Every base change of `fromSource` along a section of `doubled` is represented by the fibre
product of `π` with the underlying section of `T'`. -/
public theorem isPullback_fromSource {V : BigFppfOver B S hS}
    (g : yoneda.obj V ⟶ doubled i π) :
    IsPullback (yoneda.map (pullback.fst π (baseSection i π g)))
      (yoneda.map (pullback.snd π (baseSection i π g))) (fromSource i π) g :=
  isPullback_fromSource_of_baseSection i π g _ (app_fst i π g)

/-- `fromSource` is representable, with every represented base change a base change of `π`. -/
public theorem relative_fromSource (P : MorphismProperty (BigFppfOver B S hS))
    (hiso : P.RespectsIso)
    (hP : ∀ (V : BigFppfOver B S hS) (f : V ⟶ T'), P (pullback.snd π f)) :
    P.relative yoneda (fromSource i π) := by
  let := hiso
  exact MorphismProperty.relative.of_exists fun V g =>
    ⟨_, _, _, isPullback_fromSource i π g, hP V _⟩

omit [HasPullbacks (BigFppfOver B S hS)] in
/-- Étaleness of underlying morphisms of schemes respects isomorphisms of the site. -/
public theorem respectsIso_inverseImage_etale :
    (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
  let : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  MorphismProperty.RespectsIso.inverseImage _ _

omit [HasPullbacks (BigFppfOver B S hS)] in
/-- Surjectivity of underlying morphisms of schemes respects isomorphisms of the site. -/
public theorem respectsIso_inverseImage_surjective :
    (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
  MorphismProperty.RespectsIso.inverseImage _ _

/-- Base changes in the site of a morphism with an étale underlying morphism of schemes again
have an étale underlying morphism of schemes. -/
public theorem etale_pullback_snd
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
    (hπ : Etale ((BigFppfOver.toScheme B S hS).map π))
    (V : BigFppfOver B S hS) (f : V ⟶ T') :
    Etale ((BigFppfOver.toScheme B S hS).map (pullback.snd π f)) :=
  let := isStableUnderBaseChange_inverseImage hpres (@Etale.{u})
  MorphismProperty.pullback_snd (P := MorphismProperty.inverseImage (@Etale.{u})
    (BigFppfOver.toScheme B S hS)) π f hπ

/-- Base changes in the site of a morphism with a surjective underlying morphism of schemes
again have a surjective underlying morphism of schemes. -/
public theorem surjective_pullback_snd
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
    (hπ : Surjective ((BigFppfOver.toScheme B S hS).map π))
    (V : BigFppfOver B S hS) (f : V ⟶ T') :
    Surjective ((BigFppfOver.toScheme B S hS).map (pullback.snd π f)) :=
  let := isStableUnderBaseChange_inverseImage hpres (@Surjective.{u})
  MorphismProperty.pullback_snd (P := MorphismProperty.inverseImage (@Surjective.{u})
    (BigFppfOver.toScheme B S hS)) π f hπ

/-- The counterexample as a representable, surjective, étale situation: the functor of points of
`X`, the doubled functor of points of `T'`, and the functor of points of `T'`. -/
public def situation
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
    (hπet : Etale ((BigFppfOver.toScheme B S hS).map π))
    (hπsurj : Surjective ((BigFppfOver.toScheme B S hS).map π)) :
    RepresentableSurjectiveEtaleSituation.{u} where
  B := B
  S := S
  hS := hS
  F := yoneda.obj X
  G := doubled i π
  H := yoneda.obj T'
  a := fromSource i π
  b := toTarget i π
  representable_a :=
    (relative_fromSource i π _ respectsIso_inverseImage_etale
      (etale_pullback_snd π hpres hπet)).1
  surjective_a :=
    relative_fromSource i π _ respectsIso_inverseImage_surjective
      (surjective_pullback_snd π hpres hπsurj)
  etale_a :=
    relative_fromSource i π _ respectsIso_inverseImage_etale
      (etale_pullback_snd π hpres hπet)

/-- The composite transformation of the counterexample is formally étale: it is the morphism of
functors of points induced by the étale morphism `π`. -/
public theorem formallyEtale_fromSource_comp_toTarget
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
    (hπet : Etale ((BigFppfOver.toScheme B S hS).map π)) :
    FormallyEtale (fromSource i π ≫ toTarget i π) := by
  have := isStableUnderBaseChange_inverseImage hpres (@Etale.{u})
  rw [fromSource_comp_toTarget]
  exact formallyEtale_of_etale B S hS _ (MorphismProperty.relative_map
    (P := MorphismProperty.inverseImage (@Etale.{u}) (BigFppfOver.toScheme B S hS)) hπet)

omit [HasPullbacks (BigFppfOver B S hS)] in
/-- A square-zero closed immersion that is not an isomorphism of schemes admits no
retraction. -/
public theorem ne_id_of_retraction (hi : IsSquareZeroClosedImmersion B S hS i)
    (hiso : ¬ IsIso ((BigFppfOver.toScheme B S hS).map i)) (g : T' ⟶ T) :
    g ≫ i ≠ 𝟙 T' := by
  intro hg
  refine hiso ?_
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map i) := hi.1
  have h1 : (BigFppfOver.toScheme B S hS).map g ≫ (BigFppfOver.toScheme B S hS).map i =
      𝟙 _ := by
    rw [← Functor.map_comp, hg]
    simp
  have h2 : (BigFppfOver.toScheme B S hS).map i ≫ (BigFppfOver.toScheme B S hS).map g =
      𝟙 _ := by
    refine (cancel_mono ((BigFppfOver.toScheme B S hS).map i)).mp ?_
    rw [Category.assoc, h1, Category.comp_id, Category.id_comp]
  exact ⟨⟨(BigFppfOver.toScheme B S hS).map g, h2, h1⟩⟩

omit [HasPullbacks (BigFppfOver B S hS)] in
/-- The two labels of `𝟙 T'` are two distinct sections of `doubled` over `T'` which restrict to
the same section over `T` and have the same image in the functor of points of `T'`: the
transformation `toTarget` is not formally unramified. -/
public theorem not_formallyUnramified_toTarget
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hi : IsSquareZeroClosedImmersion B S hS i)
    (hπ : ∀ ξ : T' ⟶ X, ξ ≫ π ≠ 𝟙 T')
    (hret : ∀ g : T' ⟶ T, g ≫ i ≠ 𝟙 T') :
    ¬ FormallyUnramified (toTarget i π) := by
  intro h
  have hid : (𝟙 T' : T' ⟶ T') ∉ Factored i π T' := by
    rintro (⟨ξ, hξ⟩ | ⟨g, hg⟩)
    · exact hπ ξ hξ
    · exact hret g hg
  have hiFact : (i ≫ 𝟙 T') ∈ Factored i π T := by
    rw [Category.comp_id]
    simpa using factored_of_comp_i i π (𝟙 T)
  have hrestr : (doubled i π).map i.op
        (⟨(𝟙 T', True), fun _ => hid⟩ : Doubled i π T') =
      (doubled i π).map i.op (⟨(𝟙 T', False), fun hh => hh.elim⟩ : Doubled i π T') := by
    refine Subtype.ext (Prod.ext rfl ?_)
    exact propext ⟨fun hh => absurd hiFact hh.2, fun hh => hh.1.elim⟩
  have heq := h T T' hT hT' i hi
    ((doubled i π).map i.op (⟨(𝟙 T', False), fun hh => hh.elim⟩ : Doubled i π T'))
    (𝟙 T') rfl
    (⟨(𝟙 T', False), fun hh => hh.elim⟩ : Doubled i π T')
    (⟨(𝟙 T', True), fun _ => hid⟩ : Doubled i π T')
    ⟨rfl, rfl⟩ ⟨hrestr, rfl⟩
  have hFT : (False : Prop) = True := congrArg (fun q => q.1.2) heq
  exact (hFT ▸ trivial : False)

/-- **Parts (5) and (6) of Stacks 04CY are false for arbitrary set-valued functors.** In a big
fppf site over `S` containing a square-zero closed immersion `i : T ⟶ T'` of affines with no
retraction and an étale surjection `π : X ⟶ T'` with no section, there is a representable,
surjective, étale situation whose composite transformation is formally étale — hence also
formally unramified — while its second transformation is not formally unramified, hence not
formally étale either.

So neither the separatedness hypothesis of
`AlgebraicGeometry.Space.formallyUnramified_of_comp_of_isSeparated` nor the sheaf hypothesis on
the intermediate presheaf in `AlgebraicGeometry.Space.formallyEtale_of_comp_of_isSeparated` can
be removed. -/
public theorem exists_not_formallyUnramified_of_comp
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hi : IsSquareZeroClosedImmersion B S hS i)
    (hπet : Etale ((BigFppfOver.toScheme B S hS).map π))
    (hπsurj : Surjective ((BigFppfOver.toScheme B S hS).map π))
    (hπ : ∀ ξ : T' ⟶ X, ξ ≫ π ≠ 𝟙 T')
    (hret : ∀ g : T' ⟶ T, g ≫ i ≠ 𝟙 T') :
    ∃ s : RepresentableSurjectiveEtaleSituation.{u},
      s.B = B ∧ s.S = S ∧ FormallyEtale (s.a ≫ s.b) ∧ ¬ FormallyUnramified s.b ∧
        ¬ FormallyEtale s.b :=
  ⟨situation i π hpres hπet hπsurj, rfl, rfl,
    formallyEtale_fromSource_comp_toTarget i π hpres hπet,
    not_formallyUnramified_toTarget i π hT hT' hi hπ hret,
    fun hb => not_formallyUnramified_toTarget i π hT hT' hi hπ hret
      fun T₀ T₀' hT₀ hT₀' i₀ hi₀ x y hxy _ _ h₁ h₂ =>
        ((hb T₀ T₀' hT₀ hT₀' i₀ hi₀ x y hxy).unique h₁ h₂)⟩

end DoubledSection

end AlgebraicGeometry.Space

end
