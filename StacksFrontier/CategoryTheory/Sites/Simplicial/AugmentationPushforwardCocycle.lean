module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationPushforward

/-!
# Coherence of the augmentations of the simplicial degrees

Let `S` be a simplicial-site situation and `a` an augmentation of `S` towards a site `(D, K)`.
Every simplicial degree `n` carries a morphism of topoi `a_n` from the sheaves on the component
of degree `n` to the sheaves on `(D, K)`, and for a simplex map `φ : m ⟶ n` the direct image of
`a_m` precomposed with the direct image of the transition `f_φ` is canonically the direct image
of `a_n`. This file proves that this family of comparisons is coherent: the comparison attached
to a composite `φ ≫ ψ` is the composite of the comparisons attached to `φ` and to `ψ`,
conjugated by the compositor of the direct images of the transitions. Together with the unit law
this makes `n ↦ a_n` a pseudofunctorial family, which is the force of the universal quantifier
over `φ` in the source. The same comparison is then transported to inverse images, where it is a
comparison of two left adjoints of one right adjoint and inherits both laws from the
direct-image ones.

The mathematical content of the cocycle law is a naturality property of the comparison of two
vertices of a single simplicial degree: composing both vertices with a further simplex map and
comparing the two resulting vertices of the target degree recovers the original comparison,
conjugated by the compositor. In both cases of the situation this rests on the compatibility
condition of an augmentation being an equality of composite site functors, so that the
comparison it induces is a transport along an equality of direct images.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.transitionInverseImageIso`: the inverse
  image of the augmentation of a degree, compared with the inverse image of the augmentation of
  the source of a simplicial transition.

## Main results

* `CategoryTheory.Functor.sheafPushforwardContinuousCompIsoOfEq_trans` and
  `CategoryTheory.sheafPushforwardCocontinuousCompIsoOfEq_trans`: the transports of direct
  images induced by two equalities of composite site functors compose to the transport induced
  by the composite equality.
* `CategoryTheory.Functor.sheafPushforwardContinuousCompIsoOfEq_whiskerLeft` and
  `CategoryTheory.sheafPushforwardCocontinuousCompIsoOfEq_whiskerLeft`: such a transport is
  natural for a further composition of site functors, through the composition comparisons of
  the direct images.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.vertexPushforwardIso_trans` and
  `CategoryTheory.SimplicialSiteSituation.Augmentation.vertexPushforwardIso_whiskerLeft`: the
  two preceding results for the vertex comparison of an augmentation.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.transitionPushforwardIso_whiskerLeft`
  and `CategoryTheory.SimplicialSiteSituation.Augmentation.transitionPushforwardIso_comp`: the
  cocycle law for the transition comparison, in the shape the pseudofunctor axiom takes and
  solved for the comparison at the composite.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.transitionInverseImageIso_id` and
  `CategoryTheory.SimplicialSiteSituation.Augmentation.transitionInverseImageIso_comp`: the unit
  and cocycle laws for the inverse-image comparison.

## Implementation notes

Both compatibility conditions of an augmentation are equalities of composite site functors, and
both continuity conditions are propositions, so a transport of direct images along such an
equality exists for any pair of continuity instances; `Functor.sheafPushforwardContinuous_congr`
and `Functor.sheafPushforwardCocontinuous_congr` record that. In the continuous case the direct
image along a composite site functor *is* the composite of the direct images, so every
comparison occurring there is a transport, and both laws reduce to transitivity of transports.
In the cocontinuous case the compositor is a genuine comparison of right Kan extensions; the
naturality law is deduced from its cocycle law together with the fact that a transport along an
equality of the outer functor commutes with it.

The arguments of the generic lemmas that are equalities of direct images are hypotheses rather
than terms built inside the statement: equality being a subsingleton, the caller may supply
whichever proof its goal already carries, which keeps each goal in one spelling.

Rewriting inside a chain of `Iso.trans` requires the pattern to start at the head of the chain,
since the notation is right associative. The proofs therefore either rewrite at the head, or
pass to the underlying natural transformations, where `reassoc_of%` produces the reassociated
form of an identity on the spot.

The inverse-image comparison is `Adjunction.leftAdjointCompIso`, the mate of the direct-image
comparison under the two adjunctions; `Adjunction.leftAdjointCompIso_comp_id` and
`Adjunction.leftAdjointCompIso_assoc` carry the unit and cocycle laws over from the direct
images, which is why the cocycle law is also recorded in the whiskered shape those lemmas take.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-! ### Transports of direct images along equalities of site functors -/

/-- Equal continuous site functors have equal direct images. Continuity being a proposition,
the two continuity instances are not required to agree. -/
public theorem Functor.sheafPushforwardContinuous_congr {X Y : Type u} [SmallCategory X]
    [SmallCategory Y] (J : GrothendieckTopology X) (M : GrothendieckTopology Y) {F F' : X ⥤ Y}
    [F.IsContinuous J M] [F'.IsContinuous J M] (e : F = F') :
    F.sheafPushforwardContinuous (Type u) J M = F'.sheafPushforwardContinuous (Type u) J M := by
  cases e
  rfl

/-- Equal cocontinuous site functors have equal direct images. -/
public theorem Functor.sheafPushforwardCocontinuous_congr {X Y : Type u} [SmallCategory X]
    [SmallCategory Y] (J : GrothendieckTopology X) (M : GrothendieckTopology Y) {F F' : X ⥤ Y}
    [F.IsCocontinuous J M] [F'.IsCocontinuous J M] (e : F = F') :
    F.sheafPushforwardCocontinuous (Type u) J M =
      F'.sheafPushforwardCocontinuous (Type u) J M := by
  cases e
  rfl

/-- Equal composites of continuous site functors, with a common first factor, have equal
composites of direct images. This is `Functor.sheafPushforwardContinuous_congr` spelled as a
composite of two direct images, which is the shape the comparisons below are stated in. -/
public theorem Functor.sheafPushforwardContinuousCompLeft_congr {W X Y : Type u}
    [SmallCategory W] [SmallCategory X] [SmallCategory Y] (L : GrothendieckTopology W)
    (J : GrothendieckTopology X) (M : GrothendieckTopology Y) (f : W ⥤ X) (g h : X ⥤ Y)
    [f.IsContinuous L J] [g.IsContinuous J M] [h.IsContinuous J M]
    [(f ⋙ g).IsContinuous L M] [(f ⋙ h).IsContinuous L M] (e : f ⋙ g = f ⋙ h) :
    g.sheafPushforwardContinuous (Type u) J M ⋙ f.sheafPushforwardContinuous (Type u) L J =
      h.sheafPushforwardContinuous (Type u) J M ⋙ f.sheafPushforwardContinuous (Type u) L J :=
  Functor.sheafPushforwardContinuous_congr L M e

/-- The equality of composites of direct images carried by an equality of a composite of
continuous site functors with a third functor. -/
public theorem Functor.sheafPushforwardContinuousCompRight_congr {X Y Z : Type u}
    [SmallCategory X] [SmallCategory Y] [SmallCategory Z] (J : GrothendieckTopology X)
    (M : GrothendieckTopology Y) (N : GrothendieckTopology Z) (F : X ⥤ Y) (G : Y ⥤ Z)
    (FG : X ⥤ Z) [F.IsContinuous J M] [G.IsContinuous M N] [FG.IsContinuous J N]
    [(F ⋙ G).IsContinuous J N] (h : F ⋙ G = FG) :
    G.sheafPushforwardContinuous (Type u) M N ⋙ F.sheafPushforwardContinuous (Type u) J M =
      FG.sheafPushforwardContinuous (Type u) J N :=
  Functor.sheafPushforwardContinuous_congr J N h

/-- The comparison of the direct images of two equal continuous site functors is a transport
along an equality of direct images. -/
public theorem Functor.sheafPushforwardContinuousIso_eqToIso {X Y : Type u} [SmallCategory X]
    [SmallCategory Y] (J : GrothendieckTopology X) (M : GrothendieckTopology Y) {F F' : X ⥤ Y}
    [F.IsContinuous J M] [F'.IsContinuous J M] (e : F = F')
    (e' : F.sheafPushforwardContinuous (Type u) J M =
      F'.sheafPushforwardContinuous (Type u) J M) :
    Functor.sheafPushforwardContinuousIso (eqToIso e) (Type u) J M = eqToIso e' := by
  cases e
  simp only [eqToIso_refl]
  ext : 3
  simp [Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]
  rfl

/-- The transport of direct images attached to an equality of a composite of continuous site
functors with a third functor is a transport along an equality of direct images. -/
public theorem Functor.sheafPushforwardContinuousComp'_eqToIso {X Y Z : Type u}
    [SmallCategory X] [SmallCategory Y] [SmallCategory Z] (J : GrothendieckTopology X)
    (M : GrothendieckTopology Y) (N : GrothendieckTopology Z) {F : X ⥤ Y} {G : Y ⥤ Z}
    {FG : X ⥤ Z} [F.IsContinuous J M] [G.IsContinuous M N] [FG.IsContinuous J N]
    (h : F ⋙ G = FG)
    (h' : G.sheafPushforwardContinuous (Type u) M N ⋙ F.sheafPushforwardContinuous (Type u) J M =
      FG.sheafPushforwardContinuous (Type u) J N) :
    Functor.sheafPushforwardContinuousComp' (eqToIso h) (Type u) J M N = eqToIso h' := by
  have := Functor.isContinuous_comp F G J M N
  dsimp only [Functor.sheafPushforwardContinuousComp',
    Functor.sheafPushforwardContinuousComp]
  rw [Functor.sheafPushforwardContinuousIso_eqToIso J N h h']
  exact Iso.refl_trans _

/-- In the continuous case the comparison attached to an equality of composite site functors is
a transport along an equality of composites of direct images. -/
public theorem Functor.sheafPushforwardContinuousCompIsoOfEq_eqToIso {W X Y : Type u}
    [SmallCategory W] [SmallCategory X] [SmallCategory Y] (L : GrothendieckTopology W)
    (J : GrothendieckTopology X) (M : GrothendieckTopology Y) (f : W ⥤ X) (g h : X ⥤ Y)
    [f.IsContinuous L J] [g.IsContinuous J M] [h.IsContinuous J M]
    [(f ⋙ g).IsContinuous L M] [(f ⋙ h).IsContinuous L M] (e : f ⋙ g = f ⋙ h)
    (e' : g.sheafPushforwardContinuous (Type u) J M ⋙
        f.sheafPushforwardContinuous (Type u) L J =
      h.sheafPushforwardContinuous (Type u) J M ⋙
        f.sheafPushforwardContinuous (Type u) L J) :
    Functor.sheafPushforwardContinuousCompIsoOfEq L J M f g h e = eqToIso e' := by
  dsimp only [Functor.sheafPushforwardContinuousCompIsoOfEq,
    Functor.sheafPushforwardContinuousComp]
  rw [Functor.sheafPushforwardContinuousIso_eqToIso L M e e']
  exact (Iso.refl_trans _).trans (Iso.trans_refl _)

/-- In the cocontinuous case the transport of a direct image along an equality of site functors
is a transport along an equality of direct images. -/
public theorem SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_eqToIso {X Y : Type u}
    [SmallCategory X] [SmallCategory Y] (J : GrothendieckTopology X)
    (M : GrothendieckTopology Y) {F F' : X ⥤ Y} [F.IsCocontinuous J M] [F'.IsCocontinuous J M]
    (e : F = F')
    (e' : F.sheafPushforwardCocontinuous (Type u) J M =
      F'.sheafPushforwardCocontinuous (Type u) J M) :
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J M e = eqToIso e' := by
  cases e
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl]
  simp

/-- The compositor of direct images along cocontinuous site functors commutes with a transport
along an equality of the outer functor. -/
public theorem sheafPushforwardCocontinuousCompIso_eqToIso {V W X : Type u} [SmallCategory V]
    [SmallCategory W] [SmallCategory X] (L : GrothendieckTopology V) (J : GrothendieckTopology W)
    (N : GrothendieckTopology X) (k : V ⥤ W) {P Q : W ⥤ X} [k.IsCocontinuous L J]
    [P.IsCocontinuous J N] [Q.IsCocontinuous J N] [(k ⋙ P).IsCocontinuous L N]
    [(k ⋙ Q).IsCocontinuous L N] (e : P = Q)
    (e₁ : P.sheafPushforwardCocontinuous (Type u) J N =
      Q.sheafPushforwardCocontinuous (Type u) J N)
    (e₂ : (k ⋙ P).sheafPushforwardCocontinuous (Type u) L N =
      (k ⋙ Q).sheafPushforwardCocontinuous (Type u) L N) :
    sheafPushforwardCocontinuousCompIso L J N k P ≪≫
        Functor.isoWhiskerLeft (k.sheafPushforwardCocontinuous (Type u) L J) (eqToIso e₁) =
      eqToIso e₂ ≪≫ sheafPushforwardCocontinuousCompIso L J N k Q := by
  cases e
  simp only [eqToIso_refl, Functor.isoWhiskerLeft_refl, Iso.trans_refl, Iso.refl_trans]

/-! ### Transitivity of the two comparisons -/

/-- Two transports of composites of direct images along continuous site functors compose to the
transport along the composite equality. -/
public theorem Functor.sheafPushforwardContinuousCompIsoOfEq_trans {W X Y : Type u}
    [SmallCategory W] [SmallCategory X] [SmallCategory Y] (L : GrothendieckTopology W)
    (J : GrothendieckTopology X) (M : GrothendieckTopology Y) (f : W ⥤ X) (g h k : X ⥤ Y)
    [f.IsContinuous L J] [g.IsContinuous J M] [h.IsContinuous J M] [k.IsContinuous J M]
    [(f ⋙ g).IsContinuous L M] [(f ⋙ h).IsContinuous L M] [(f ⋙ k).IsContinuous L M]
    (e : f ⋙ g = f ⋙ h) (e' : f ⋙ h = f ⋙ k) :
    Functor.sheafPushforwardContinuousCompIsoOfEq L J M f g h e ≪≫
        Functor.sheafPushforwardContinuousCompIsoOfEq L J M f h k e' =
      Functor.sheafPushforwardContinuousCompIsoOfEq L J M f g k (e.trans e') := by
  rw [Functor.sheafPushforwardContinuousCompIsoOfEq_eqToIso L J M f g h e
      (Functor.sheafPushforwardContinuousCompLeft_congr L J M f g h e),
    Functor.sheafPushforwardContinuousCompIsoOfEq_eqToIso L J M f h k e'
      (Functor.sheafPushforwardContinuousCompLeft_congr L J M f h k e'),
    Functor.sheafPushforwardContinuousCompIsoOfEq_eqToIso L J M f g k (e.trans e')
      (Functor.sheafPushforwardContinuousCompLeft_congr L J M f g k (e.trans e')),
    eqToIso_trans]

/-- Two transports of composites of direct images along cocontinuous site functors compose to
the transport along the composite equality. -/
public theorem sheafPushforwardCocontinuousCompIsoOfEq_trans {X Y Z : Type u} [SmallCategory X]
    [SmallCategory Y] [SmallCategory Z] (J : GrothendieckTopology X)
    (M : GrothendieckTopology Y) (N : GrothendieckTopology Z) (g h k : X ⥤ Y) (f : Y ⥤ Z)
    [g.IsCocontinuous J M] [h.IsCocontinuous J M] [k.IsCocontinuous J M] [f.IsCocontinuous M N]
    [(g ⋙ f).IsCocontinuous J N] [(h ⋙ f).IsCocontinuous J N] [(k ⋙ f).IsCocontinuous J N]
    (e : g ⋙ f = h ⋙ f) (e' : h ⋙ f = k ⋙ f) :
    sheafPushforwardCocontinuousCompIsoOfEq J M N g h f e ≪≫
        sheafPushforwardCocontinuousCompIsoOfEq J M N h k f e' =
      sheafPushforwardCocontinuousCompIsoOfEq J M N g k f (e.trans e') := by
  dsimp only [sheafPushforwardCocontinuousCompIsoOfEq]
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_eqToIso J N e
      (Functor.sheafPushforwardCocontinuous_congr J N e),
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_eqToIso J N e'
      (Functor.sheafPushforwardCocontinuous_congr J N e'),
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_eqToIso J N (e.trans e')
      (Functor.sheafPushforwardCocontinuous_congr J N (e.trans e'))]
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  simp

/-! ### Naturality of the two comparisons under a further composition -/

/-- The comparison attached to an equality of composite continuous site functors is natural for
a further composition on the outside: composing the two inner functors with a third one and
transporting along the resulting equality recovers the original comparison, conjugated by the
composition comparisons of the direct images. -/
public theorem Functor.sheafPushforwardContinuousCompIsoOfEq_whiskerLeft {V W X Y : Type u}
    [SmallCategory V] [SmallCategory W] [SmallCategory X] [SmallCategory Y]
    (L : GrothendieckTopology V) (J : GrothendieckTopology W) (M : GrothendieckTopology X)
    (N : GrothendieckTopology Y) (f : V ⥤ W) (g h : W ⥤ X) (k : X ⥤ Y) (gk hk : W ⥤ Y)
    [f.IsContinuous L J] [g.IsContinuous J M] [h.IsContinuous J M] [k.IsContinuous M N]
    [gk.IsContinuous J N] [hk.IsContinuous J N]
    [(f ⋙ g).IsContinuous L M] [(f ⋙ h).IsContinuous L M]
    [(f ⋙ gk).IsContinuous L N] [(f ⋙ hk).IsContinuous L N]
    (e : f ⋙ g = f ⋙ h) (hgk : g ⋙ k = gk) (hhk : h ⋙ k = hk) (e₂ : f ⋙ gk = f ⋙ hk) :
    Functor.isoWhiskerLeft (k.sheafPushforwardContinuous (Type u) M N)
        (Functor.sheafPushforwardContinuousCompIsoOfEq L J M f g h e) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
            (Functor.sheafPushforwardContinuousComp' (eqToIso hgk) (Type u) J M N)
            (f.sheafPushforwardContinuous (Type u) L J) ≪≫
          Functor.sheafPushforwardContinuousCompIsoOfEq L J N f gk hk e₂ ≪≫
            (Functor.isoWhiskerRight
                (Functor.sheafPushforwardContinuousComp' (eqToIso hhk) (Type u) J M N)
                (f.sheafPushforwardContinuous (Type u) L J)).symm ≪≫
              Functor.associator _ _ _ := by
  have := Functor.isContinuous_comp g k J M N
  have := Functor.isContinuous_comp h k J M N
  rw [Functor.sheafPushforwardContinuousCompIsoOfEq_eqToIso L J M f g h e
      (Functor.sheafPushforwardContinuousCompLeft_congr L J M f g h e),
    Functor.sheafPushforwardContinuousCompIsoOfEq_eqToIso L J N f gk hk e₂
      (Functor.sheafPushforwardContinuousCompLeft_congr L J N f gk hk e₂),
    Functor.sheafPushforwardContinuousComp'_eqToIso J M N hgk
      (Functor.sheafPushforwardContinuousCompRight_congr J M N g k gk hgk),
    Functor.sheafPushforwardContinuousComp'_eqToIso J M N hhk
      (Functor.sheafPushforwardContinuousCompRight_congr J M N h k hk hhk)]
  apply Iso.ext
  apply NatTrans.ext
  funext Z
  simp [eqToHom_map]

/-- The comparison attached to an equality of composite cocontinuous site functors is natural
for a further composition on the inside: composing the two outer functors with a third one and
transporting along the resulting equality recovers the original comparison, conjugated by the
composition comparisons of the direct images. -/
public theorem sheafPushforwardCocontinuousCompIsoOfEq_whiskerLeft {V W X Y : Type u}
    [SmallCategory V] [SmallCategory W] [SmallCategory X] [SmallCategory Y]
    (L : GrothendieckTopology V) (J : GrothendieckTopology W) (M : GrothendieckTopology X)
    (N : GrothendieckTopology Y) (k : V ⥤ W) (g h : W ⥤ X) (f : X ⥤ Y) (kg kh : V ⥤ X)
    [k.IsCocontinuous L J] [g.IsCocontinuous J M] [h.IsCocontinuous J M] [f.IsCocontinuous M N]
    [kg.IsCocontinuous L M] [kh.IsCocontinuous L M]
    [(g ⋙ f).IsCocontinuous J N] [(h ⋙ f).IsCocontinuous J N]
    [(kg ⋙ f).IsCocontinuous L N] [(kh ⋙ f).IsCocontinuous L N]
    [(k ⋙ g).IsCocontinuous L M] [(k ⋙ h).IsCocontinuous L M]
    (e : g ⋙ f = h ⋙ f) (hkg : k ⋙ g = kg) (hkh : k ⋙ h = kh) (e₂ : kg ⋙ f = kh ⋙ f) :
    Functor.isoWhiskerLeft (k.sheafPushforwardCocontinuous (Type u) L J)
        (sheafPushforwardCocontinuousCompIsoOfEq J M N g h f e) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
            ((sheafPushforwardCocontinuousCompIso L J M k g).symm ≪≫
              SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq L M hkg)
            (f.sheafPushforwardCocontinuous (Type u) M N) ≪≫
          sheafPushforwardCocontinuousCompIsoOfEq L M N kg kh f e₂ ≪≫
            (Functor.isoWhiskerRight
                ((sheafPushforwardCocontinuousCompIso L J M k h).symm ≪≫
                  SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq L M hkh)
                (f.sheafPushforwardCocontinuous (Type u) M N)).symm ≪≫
              Functor.associator _ _ _ := by
  subst hkg
  subst hkh
  have i1 := CategoryTheory.isCocontinuous_comp k (g ⋙ f) L J (L := N)
  have i2 := CategoryTheory.isCocontinuous_comp k (h ⋙ f) L J (L := N)
  have hg := sheafPushforwardCocontinuousCompIso_assoc N M J L (a := k) (b := g) (c := f)
    (BC := g ⋙ f) (AB := k ⋙ g) (T := k ⋙ (g ⋙ f)) (T' := (k ⋙ g) ⋙ f) rfl rfl rfl rfl rfl
  have hh := sheafPushforwardCocontinuousCompIso_assoc N M J L (a := k) (b := h) (c := f)
    (BC := h ⋙ f) (AB := k ⋙ h) (T := k ⋙ (h ⋙ f)) (T' := (k ⋙ h) ⋙ f) rfl rfl rfl rfl rfl
  have hl2 := sheafPushforwardCocontinuousCompIso_eqToIso L J N k (P := g ⋙ f) (Q := h ⋙ f) e
    (Functor.sheafPushforwardCocontinuous_congr J N e)
    (Functor.sheafPushforwardCocontinuous_congr L N e₂)
  simp only [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl, eqToIso_refl,
    Iso.trans_refl] at hg hh
  dsimp only [sheafPushforwardCocontinuousCompIsoOfEq]
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_eqToIso J N e
      (Functor.sheafPushforwardCocontinuous_congr J N e),
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_eqToIso L N e₂
      (Functor.sheafPushforwardCocontinuous_congr L N e₂),
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl,
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl]
  apply Iso.ext
  have hgh := congrArg Iso.hom hg
  have hhi := congrArg Iso.inv hh
  have hl2h := congrArg Iso.hom hl2
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.trans_refl,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_comp,
    Category.assoc] at hgh hhi hl2h ⊢
  rw [← reassoc_of% hgh, ← hhi, ← reassoc_of% hl2h]
  simp

namespace SimplicialSiteSituation

/-- The transport of a direct image along a proof of reflexivity of a simplex map is the
identity. -/
public theorem pushforwardCongr_refl (S : SimplicialSiteSituation.{u}) {m n : SimplexCategory}
    {φ : m ⟶ n} (h : φ = φ) : S.pushforwardCongr h = Iso.refl _ :=
  rfl

namespace Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- The vertex functors of a continuous simplicial site are continuous. -/
private theorem isContinuous_vertex_functor (C : SimplicialSite.{u}) {m q : SimplexCategory}
    (ρ : m ⟶ q) :
    (C.underlying.map ρ).toFunctor.IsContinuous (C.coverage m).toGrothendieck
      (C.coverage q).toGrothendieck :=
  (C.isMorphismOfSites ρ).isContinuous

/-- The composite of the functor of an augmentation with a vertex functor is continuous. -/
private theorem isContinuous_augmentation_comp_vertex (C : SimplicialSite.{u}) (D : Cat.{u, u})
    (K : GrothendieckTopology D) (a : C.ContinuousAugmentation D K) {q : SimplexCategory}
    (ρ : SimplexCategory.mk 0 ⟶ q) :
    (a.functor ⋙ (C.underlying.map ρ).toFunctor).IsContinuous K (C.coverage q).toGrothendieck :=
  have := isContinuous_vertex_functor C ρ
  have := a.isMorphismOfSites.isContinuous
  Functor.isContinuous_comp a.functor (C.underlying.map ρ).toFunctor K
    (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage q).toGrothendieck

/-- The vertex functors of a cocontinuous simplicial site are cocontinuous. -/
private theorem isCocontinuous_vertex_functor (C : CocontinuousSimplicialSite.{u})
    {m q : SimplexCategory} (ρ : m ⟶ q) :
    (C.underlying.map ρ.op).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (Opposite.op q)))
      (topologyOfCoverings (C.coverage (Opposite.op m))) :=
  C.isCocontinuous ρ.op

/-- The composite of a vertex functor with the functor of an augmentation is cocontinuous. -/
private theorem isCocontinuous_vertex_functor_comp_augmentation
    (C : CocontinuousSimplicialSite.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
    (a : C.Augmentation D K) {q : SimplexCategory} (ρ : SimplexCategory.mk 0 ⟶ q) :
    ((C.underlying.map ρ.op).toFunctor ⋙ a.functor).IsCocontinuous
      (topologyOfCoverings (C.coverage (Opposite.op q))) K :=
  have := isCocontinuous_vertex_functor C ρ
  have := a.isCocontinuous
  CategoryTheory.isCocontinuous_comp (C.underlying.map ρ.op).toFunctor a.functor
    (topologyOfCoverings (C.coverage (Opposite.op q)))
    (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) (L := K)

/-- The vertex comparisons of an augmentation are transitive: comparing a first vertex with a
second and the second with a third is comparing the first with the third. -/
public theorem vertexPushforwardIso_trans {n : SimplexCategory}
    (ρ σ τ : SimplexCategory.mk 0 ⟶ n) :
    vertexPushforwardIso S D K a ρ σ ≪≫ vertexPushforwardIso S D K a σ τ =
      vertexPushforwardIso S D K a ρ τ := by
  rcases S with ⟨C | C⟩
  · have := @isContinuous_vertex_functor C
    have := (a : C.ContinuousAugmentation D K).isMorphismOfSites.isContinuous
    have := @isContinuous_augmentation_comp_vertex C D K a
    exact Functor.sheafPushforwardContinuousCompIsoOfEq_trans K
      (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck
      (a : C.ContinuousAugmentation D K).functor (C.underlying.map ρ).toFunctor
      (C.underlying.map σ).toFunctor (C.underlying.map τ).toFunctor
      ((a : C.ContinuousAugmentation D K).compatibility n ρ σ)
      ((a : C.ContinuousAugmentation D K).compatibility n σ τ)
  · have := @isCocontinuous_vertex_functor C
    have := (a : C.Augmentation D K).isCocontinuous
    have := @isCocontinuous_vertex_functor_comp_augmentation C D K a
    exact sheafPushforwardCocontinuousCompIsoOfEq_trans
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K
      (C.underlying.map ρ.op).toFunctor (C.underlying.map σ.op).toFunctor
      (C.underlying.map τ.op).toFunctor (a : C.Augmentation D K).functor
      ((a : C.Augmentation D K).compatibility n ρ σ)
      ((a : C.Augmentation D K).compatibility n σ τ)

/-- The vertex comparisons of an augmentation are natural for a further simplex map: comparing
two vertices of a degree and then composing with a transition is comparing the two composed
vertices of the target degree, conjugated by the simplicial compositor. -/
public theorem vertexPushforwardIso_whiskerLeft {n p : SimplexCategory}
    (ρ σ : SimplexCategory.mk 0 ⟶ n) (ψ : n ⟶ p) :
    Functor.isoWhiskerLeft (S.transitionMorphism ψ).pushforward
        (vertexPushforwardIso S D K a ρ σ) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (S.pushforwardCompSymm ρ ψ)
            (Augmentation.morphismOfTopoi S D K a).pushforward ≪≫
          vertexPushforwardIso S D K a (ρ ≫ ψ) (σ ≫ ψ) ≪≫
            (Functor.isoWhiskerRight (S.pushforwardCompSymm σ ψ)
                (Augmentation.morphismOfTopoi S D K a).pushforward).symm ≪≫
              Functor.associator _ _ _ := by
  rcases S with ⟨C | C⟩
  · have := @isContinuous_vertex_functor C
    have := (a : C.ContinuousAugmentation D K).isMorphismOfSites.isContinuous
    have := @isContinuous_augmentation_comp_vertex C D K a
    dsimp only [SimplicialSiteSituation.pushforwardCompSymm, id]
    exact Functor.sheafPushforwardContinuousCompIsoOfEq_whiskerLeft K
      (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck
      (C.coverage p).toGrothendieck (a : C.ContinuousAugmentation D K).functor
      (C.underlying.map ρ).toFunctor (C.underlying.map σ).toFunctor
      (C.underlying.map ψ).toFunctor (C.underlying.map (ρ ≫ ψ)).toFunctor
      (C.underlying.map (σ ≫ ψ)).toFunctor
      ((a : C.ContinuousAugmentation D K).compatibility n ρ σ)
      (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ρ ψ)).symm
      (congrArg Cat.Hom.toFunctor (C.underlying.map_comp σ ψ)).symm
      ((a : C.ContinuousAugmentation D K).compatibility p (ρ ≫ ψ) (σ ≫ ψ))
  · have := @isCocontinuous_vertex_functor C
    have := (a : C.Augmentation D K).isCocontinuous
    have := @isCocontinuous_vertex_functor_comp_augmentation C D K a
    have := CategoryTheory.isCocontinuous_comp (C.underlying.map ψ.op).toFunctor
      (C.underlying.map ρ.op).toFunctor (topologyOfCoverings (C.coverage (Opposite.op p)))
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (L := (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))))
    have := CategoryTheory.isCocontinuous_comp (C.underlying.map ψ.op).toFunctor
      (C.underlying.map σ.op).toFunctor (topologyOfCoverings (C.coverage (Opposite.op p)))
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (L := (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))))
    dsimp only [SimplicialSiteSituation.pushforwardCompSymm, id,
      SimplicialSiteSituation.transitionMorphism, gStar]
    exact sheafPushforwardCocontinuousCompIsoOfEq_whiskerLeft
      (topologyOfCoverings (C.coverage (Opposite.op p)))
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K
      (C.underlying.map ψ.op).toFunctor (C.underlying.map ρ.op).toFunctor
      (C.underlying.map σ.op).toFunctor (a : C.Augmentation D K).functor
      (C.underlying.map (ρ ≫ ψ).op).toFunctor (C.underlying.map (σ ≫ ψ).op).toFunctor
      ((a : C.Augmentation D K).compatibility n ρ σ)
      (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ.op ρ.op)).symm
      (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ.op σ.op)).symm
      ((a : C.Augmentation D K).compatibility p (ρ ≫ ψ) (σ ≫ ψ))

/-- **Stacks 0D70, compatibility (1).** The cocycle law: the transition comparison of the
component augmentations along a composite of simplex maps is the composite of the two transition
comparisons, conjugated by the compositor of the direct images of the transitions. -/
public theorem transitionPushforwardIso_whiskerLeft {m n p : SimplexCategory} (φ : m ⟶ n)
    (ψ : n ⟶ p) :
    Functor.isoWhiskerLeft (S.transitionMorphism ψ).pushforward
          (transitionPushforwardIso S D K a φ) ≪≫
        transitionPushforwardIso S D K a ψ =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (S.pushforwardCompSymm φ ψ)
            (componentAugmentation S D K a m).pushforward ≪≫
          transitionPushforwardIso S D K a (φ ≫ ψ) := by
  have hassoc : SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ (φ ≫ ψ) =
      (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ) ≫ ψ :=
    (Category.assoc _ _ _).symm
  dsimp only [transitionPushforwardIso, componentAugmentation_pushforward]
  rw [Functor.isoWhiskerLeft_trans, Functor.isoWhiskerLeft_trans,
    vertexPushforwardIso_whiskerLeft S D K a
      (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ)
      (SimplexCategory.const (SimplexCategory.mk 0) n 0) ψ]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc]
  rw [vertexPushforwardIso_trans S D K a
      ((SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ) ≫ ψ)
      (SimplexCategory.const (SimplexCategory.mk 0) n 0 ≫ ψ)
      (SimplexCategory.const (SimplexCategory.mk 0) p 0),
    ← vertexPushforwardIso_congr S D K a hassoc]
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  have hP := NatTrans.congr_app (congrArg Iso.hom (S.pushforwardCompSymm_assoc
    (SimplexCategory.const (SimplexCategory.mk 0) m 0) φ ψ)) Y
  have hz : (S.pushforwardCongr (Category.assoc
          (SimplexCategory.const (SimplexCategory.mk 0) m 0) φ ψ)).hom.app Y ≫
      (S.pushforwardCongr hassoc).hom.app Y = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← Iso.trans_hom, S.pushforwardCongr_trans, S.pushforwardCongr_refl,
      Iso.refl_hom, NatTrans.id_app]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.comp_map, Category.id_comp] at hP ⊢
  have hPA := congrArg (fun t => (Augmentation.morphismOfTopoi S D K a).pushforward.map t) hP
  have hzA := congrArg (fun t => (Augmentation.morphismOfTopoi S D K a).pushforward.map t) hz
  simp only [Functor.map_comp, Functor.map_id] at hPA hzA
  rw [← reassoc_of% hPA, reassoc_of% hzA]
  simp

/-- **Stacks 0D70, compatibility (1).** The transition comparison at a composite of simplex
maps, expressed through the two transition comparisons of the factors. -/
public theorem transitionPushforwardIso_comp {m n p : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ p) :
    transitionPushforwardIso S D K a (φ ≫ ψ) =
      Functor.isoWhiskerRight (S.pushforwardComp ψ φ)
          (componentAugmentation S D K a m).pushforward ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (S.transitionMorphism ψ).pushforward
              (transitionPushforwardIso S D K a φ) ≪≫
            transitionPushforwardIso S D K a ψ := by
  rw [transitionPushforwardIso_whiskerLeft S D K a φ ψ]
  dsimp only [SimplicialSiteSituation.pushforwardComp]
  rw [← Functor.isoWhiskerRight_symm]
  simp only [Iso.self_symm_id_assoc, Iso.symm_self_id_assoc]

/-! ### The comparison in inverse images -/

/-- **Stacks 0D70, compatibility (1), in inverse images.** The inverse image of the component
augmentation of a degree, followed by the inverse image of a simplicial transition out of that
degree, is the inverse image of the component augmentation of the target degree. These are the
left adjoints of the two direct images compared by `transitionPushforwardIso`, so this is the
mate of that comparison. -/
public noncomputable def transitionInverseImageIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentAugmentation S D K a m).inverseImage ⋙ (S.transitionMorphism φ).inverseImage ≅
      (componentAugmentation S D K a n).inverseImage :=
  Adjunction.leftAdjointCompIso (componentAugmentation S D K a m).adj
    (S.transitionMorphism φ).adj (componentAugmentation S D K a n).adj
    (transitionPushforwardIso S D K a φ)

/-- **Stacks 0D70.** The inverse-image comparison satisfies the unit law. -/
public theorem transitionInverseImageIso_id (n : SimplexCategory) :
    transitionInverseImageIso S D K a (𝟙 n) =
      Functor.isoWhiskerLeft (componentAugmentation S D K a n).inverseImage
          (Adjunction.leftAdjointIdIso (S.transitionMorphism (𝟙 n)).adj (S.pushforwardId n)) ≪≫
        Functor.rightUnitor _ :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (transitionPushforwardIso_id S D K a n)

/-- **Stacks 0D70.** The inverse-image comparison satisfies the cocycle law, with the
inverse-image compositor of the simplicial transitions in place of the direct-image one. -/
public theorem transitionInverseImageIso_comp {m n p : SimplexCategory} (φ : m ⟶ n)
    (ψ : n ⟶ p) :
    Functor.isoWhiskerLeft (componentAugmentation S D K a m).inverseImage
          (Adjunction.leftAdjointCompIso (S.transitionMorphism φ).adj
            (S.transitionMorphism ψ).adj (S.transitionMorphism (φ ≫ ψ)).adj
            (S.pushforwardCompSymm φ ψ)) ≪≫
        transitionInverseImageIso S D K a (φ ≫ ψ) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (transitionInverseImageIso S D K a φ)
            (S.transitionMorphism ψ).inverseImage ≪≫
          transitionInverseImageIso S D K a ψ :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _
    (transitionPushforwardIso_whiskerLeft S D K a φ ψ)

end Augmentation

end SimplicialSiteSituation

end CategoryTheory

end
