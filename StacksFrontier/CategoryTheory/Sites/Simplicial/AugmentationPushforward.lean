module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.Augmentation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.PushforwardCoherence

/-!
# Direct images of the component augmentations of a simplicial site

Let `S` be a simplicial-site situation and `a` an augmentation of `S` towards a site `(D, K)`.
Composing the degree-zero morphism of topoi of `a` with the transition morphism of a vertex of
simplicial degree `n` gives a morphism of topoi from the sheaves on the degree-`n` component to
the sheaves on `(D, K)`. This file constructs those morphisms and the canonical comparison of
their direct images along a simplicial transition.

## Main definitions

* `CategoryTheory.Functor.sheafPushforwardContinuousCompIsoOfEq` and
  `CategoryTheory.sheafPushforwardCocontinuousCompIsoOfEq`: the comparison of two composites of
  direct images arising from an equality of the two composite site functors, in the continuous
  and the cocontinuous case.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.componentAugmentation`: the morphism of
  topoi attached to a simplicial degree.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.vertexPushforwardIso`: the comparison of
  the direct images of two vertices of one simplicial degree.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.degreeZeroPushforwardIso`: the
  identification of the degree-zero component augmentation with the given augmentation.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.transitionPushforwardIso`: the comparison
  of the direct image of a component augmentation with that of the component augmentation of the
  source of a simplicial transition.

## Main results

* `..._eq_canonical`: the transition comparison is the composite of the simplicial compositor
  with the comparison induced by the augmentation site functor.

## Implementation notes

The equalities of morphisms of topoi in the source are expressed as natural isomorphisms of
direct-image functors, since the functors obtained by composing adjunctions are not
definitionally equal.

`vertexPushforwardIso` is the only place where the compatibility field of an augmentation is
used, and it is stated for an arbitrary ordered pair of vertices rather than only against the
constant vertex, which is what makes it reflexive. In both cases of the situation it is an
instance of one of the two generic comparisons above: a composition comparison, a transport
along an equality of composite site functors, and the inverse of a second composition
comparison. The transport is an `eqToIso`, which is why it is reflexive.

Those two generic comparisons are stated purely in terms of site data and carry no simplicial
site, deliberately. A per-case statement written over
`CategoryTheory.SimplicialSiteSituation.mk (Sum.inl C)` has to apply the augmentation of a
situation to an augmentation of `C`, and the resulting type is then not type-correct at the
`implicit` transparency level, which makes `simp` refuse to run on it. For a related reason
neither `change` nor `change ... at` may be used inside the body of a definition whose value one
later wants to `dsimp` through: both insert an `id` into that value, and `id_eq` does not remove
it.

The unit and cocycle laws for the simplicial compositors are
`CategoryTheory.SimplicialSiteSituation.pushforwardCompSymm_comp_id`, `_id_comp` and `_assoc`.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

namespace SimplicialSiteSituation

/-- The transport of a direct image along a cocontinuous site functor along an equality of a
functor with itself is the identity. This is
`CategoryTheory.SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl` for an arbitrary
proof of reflexivity. -/
public theorem cocontinuousPushforwardIsoOfEq_self {C : Type u} [SmallCategory C] {E : Type u}
    [SmallCategory E] (J : GrothendieckTopology C) (L : GrothendieckTopology E) {F : C ⥤ E}
    [F.IsCocontinuous J L] (h : F = F) :
    cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J L h = Iso.refl _ := rfl

/-- The transport of a direct image along an equality of simplex maps is multiplicative. -/
public theorem pushforwardCongr_trans (S : SimplicialSiteSituation.{u}) {m n : SimplexCategory}
    {φ₁ φ₂ φ₃ : m ⟶ n} (h : φ₁ = φ₂) (h' : φ₂ = φ₃) :
    S.pushforwardCongr h ≪≫ S.pushforwardCongr h' = S.pushforwardCongr (h.trans h') := by
  subst h; subst h'; rfl

/-- The compositor is natural in its first argument along an equality of simplex maps. -/
public theorem pushforwardCompSymm_congr_left (S : SimplicialSiteSituation.{u})
    {l m n : SimplexCategory} {ψ ψ' : l ⟶ m} (φ : m ⟶ n) (h : ψ = ψ')
    (h' : ψ ≫ φ = ψ' ≫ φ) :
    S.pushforwardCompSymm ψ φ ≪≫ S.pushforwardCongr h' =
      Functor.isoWhiskerLeft (S.transitionMorphism φ).pushforward (S.pushforwardCongr h) ≪≫
        S.pushforwardCompSymm ψ' φ := by
  subst h
  simp [SimplicialSiteSituation.pushforwardCongr]

end SimplicialSiteSituation

/-! ### Comparisons of direct images induced by an equality of composite site functors -/

/-- For continuous site functors `f : E ⥤ C` and `g, h : C ⥤ F` with `f ⋙ g = f ⋙ h`, the
comparison of the two composites of direct images. -/
public noncomputable def Functor.sheafPushforwardContinuousCompIsoOfEq {E C F : Type u}
    [SmallCategory E] [SmallCategory C] [SmallCategory F] (L : GrothendieckTopology E)
    (J : GrothendieckTopology C) (M : GrothendieckTopology F) (f : E ⥤ C) (g h : C ⥤ F)
    [f.IsContinuous L J] [g.IsContinuous J M] [h.IsContinuous J M] [(f ⋙ g).IsContinuous L M]
    [(f ⋙ h).IsContinuous L M] (e : f ⋙ g = f ⋙ h) :
    g.sheafPushforwardContinuous (Type u) J M ⋙ f.sheafPushforwardContinuous (Type u) L J ≅
      h.sheafPushforwardContinuous (Type u) J M ⋙ f.sheafPushforwardContinuous (Type u) L J :=
  Functor.sheafPushforwardContinuousComp f g (Type u) L J M ≪≫
    Functor.sheafPushforwardContinuousIso (eqToIso e) (Type u) L M ≪≫
    (Functor.sheafPushforwardContinuousComp f h (Type u) L J M).symm

/-- The comparison of `CategoryTheory.Functor.sheafPushforwardContinuousCompIsoOfEq` along an
equality of a composite with itself is the identity. -/
public theorem Functor.sheafPushforwardContinuousCompIsoOfEq_self {E C F : Type u}
    [SmallCategory E] [SmallCategory C] [SmallCategory F] (L : GrothendieckTopology E)
    (J : GrothendieckTopology C) (M : GrothendieckTopology F) (f : E ⥤ C) (g : C ⥤ F)
    [f.IsContinuous L J] [g.IsContinuous J M] [(f ⋙ g).IsContinuous L M]
    (e : f ⋙ g = f ⋙ g) :
    Functor.sheafPushforwardContinuousCompIsoOfEq L J M f g g e = Iso.refl _ := by
  dsimp only [Functor.sheafPushforwardContinuousCompIsoOfEq,
    Functor.sheafPushforwardContinuousComp]
  ext : 3
  simp [Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans]
  rfl

/-- For cocontinuous site functors `g, h : C ⥤ E` and `f : E ⥤ F` with `g ⋙ f = h ⋙ f`, the
comparison of the two composites of direct images. -/
public noncomputable def sheafPushforwardCocontinuousCompIsoOfEq {C E F : Type u}
    [SmallCategory C] [SmallCategory E] [SmallCategory F] (J : GrothendieckTopology C)
    (L : GrothendieckTopology E) (M : GrothendieckTopology F) (g h : C ⥤ E) (f : E ⥤ F)
    [g.IsCocontinuous J L] [h.IsCocontinuous J L] [f.IsCocontinuous L M]
    [(g ⋙ f).IsCocontinuous J M] [(h ⋙ f).IsCocontinuous J M] (e : g ⋙ f = h ⋙ f) :
    g.sheafPushforwardCocontinuous (Type u) J L ⋙ f.sheafPushforwardCocontinuous (Type u) L M ≅
      h.sheafPushforwardCocontinuous (Type u) J L ⋙
        f.sheafPushforwardCocontinuous (Type u) L M :=
  (sheafPushforwardCocontinuousCompIso J L M g f).symm ≪≫
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq J M e ≪≫
    sheafPushforwardCocontinuousCompIso J L M h f

/-- The comparison of `CategoryTheory.sheafPushforwardCocontinuousCompIsoOfEq` along an equality
of a composite with itself is the identity. -/
public theorem sheafPushforwardCocontinuousCompIsoOfEq_self {C E F : Type u} [SmallCategory C]
    [SmallCategory E] [SmallCategory F] (J : GrothendieckTopology C) (L : GrothendieckTopology E)
    (M : GrothendieckTopology F) (g : C ⥤ E) (f : E ⥤ F) [g.IsCocontinuous J L]
    [f.IsCocontinuous L M] [(g ⋙ f).IsCocontinuous J M] (e : g ⋙ f = g ⋙ f) :
    sheafPushforwardCocontinuousCompIsoOfEq J L M g g f e = Iso.refl _ := by
  dsimp only [sheafPushforwardCocontinuousCompIsoOfEq]
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_self]
  simp

namespace SimplicialSiteSituation

namespace Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **Stacks 0D70, part (1).** The morphism of topoi from the sheaves on the component in
simplicial degree `n` to the sheaves on the augmentation site, obtained by composing the
degree-zero morphism of the augmentation with the transition morphism of a vertex. -/
@[stacks 0D70 "part (1): the morphisms of topoi of the components"]
public noncomputable def componentAugmentation (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf (S.componentTopology n) (Type u)) (Sheaf K (Type u)) :=
  (Augmentation.morphismOfTopoi S D K a).comp
    (S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0) n 0))

/-- The direct image of a component augmentation is the composite of the direct image of the
vertex transition with the direct image of the augmentation. -/
public theorem componentAugmentation_pushforward (n : SimplexCategory) :
    (componentAugmentation S D K a n).pushforward =
      (S.transitionMorphism (SimplexCategory.const (SimplexCategory.mk 0) n 0)).pushforward ⋙
        (Augmentation.morphismOfTopoi S D K a).pushforward :=
  rfl

/-- The comparison of the direct images of two vertices of one simplicial degree, induced by the
compatibility field of the augmentation. -/
public noncomputable def vertexPushforwardIso {n : SimplexCategory}
    (ρ σ : SimplexCategory.mk 0 ⟶ n) :
    (S.transitionMorphism ρ).pushforward ⋙
        (Augmentation.morphismOfTopoi S D K a).pushforward ≅
      (S.transitionMorphism σ).pushforward ⋙
        (Augmentation.morphismOfTopoi S D K a).pushforward := by
  rcases S with ⟨C | C⟩
  · letI : (C.underlying.map ρ).toFunctor.IsContinuous
        (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck :=
      (C.isMorphismOfSites ρ).isContinuous
    letI : (C.underlying.map σ).toFunctor.IsContinuous
        (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck :=
      (C.isMorphismOfSites σ).isContinuous
    letI : (a : C.ContinuousAugmentation D K).functor.IsContinuous K
        (C.coverage (SimplexCategory.mk 0)).toGrothendieck :=
      (a : C.ContinuousAugmentation D K).isMorphismOfSites.isContinuous
    letI : ((a : C.ContinuousAugmentation D K).functor ⋙
        (C.underlying.map ρ).toFunctor).IsContinuous K (C.coverage n).toGrothendieck :=
      Functor.isContinuous_comp (a : C.ContinuousAugmentation D K).functor
        (C.underlying.map ρ).toFunctor K
        (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck
    letI : ((a : C.ContinuousAugmentation D K).functor ⋙
        (C.underlying.map σ).toFunctor).IsContinuous K (C.coverage n).toGrothendieck :=
      Functor.isContinuous_comp (a : C.ContinuousAugmentation D K).functor
        (C.underlying.map σ).toFunctor K
        (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck
    exact Functor.sheafPushforwardContinuousCompIsoOfEq K
      (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck
      (a : C.ContinuousAugmentation D K).functor (C.underlying.map ρ).toFunctor
      (C.underlying.map σ).toFunctor ((a : C.ContinuousAugmentation D K).compatibility n ρ σ)
  · letI : (C.underlying.map ρ.op).toFunctor.IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op n)))
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) :=
      C.isCocontinuous ρ.op
    letI : (C.underlying.map σ.op).toFunctor.IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op n)))
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) :=
      C.isCocontinuous σ.op
    letI : (a : C.Augmentation D K).functor.IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K :=
      (a : C.Augmentation D K).isCocontinuous
    letI : ((C.underlying.map ρ.op).toFunctor ⋙
        (a : C.Augmentation D K).functor).IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op n))) K :=
      CategoryTheory.isCocontinuous_comp (C.underlying.map ρ.op).toFunctor
        (a : C.Augmentation D K).functor (topologyOfCoverings (C.coverage (Opposite.op n)))
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0))))
    letI : ((C.underlying.map σ.op).toFunctor ⋙
        (a : C.Augmentation D K).functor).IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op n))) K :=
      CategoryTheory.isCocontinuous_comp (C.underlying.map σ.op).toFunctor
        (a : C.Augmentation D K).functor (topologyOfCoverings (C.coverage (Opposite.op n)))
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0))))
    exact sheafPushforwardCocontinuousCompIsoOfEq
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K
      (C.underlying.map ρ.op).toFunctor (C.underlying.map σ.op).toFunctor
      (a : C.Augmentation D K).functor ((a : C.Augmentation D K).compatibility n ρ σ)

/-- The comparison of a vertex with itself is the identity. -/
public theorem vertexPushforwardIso_self {n : SimplexCategory}
    (ρ : SimplexCategory.mk 0 ⟶ n) :
    vertexPushforwardIso S D K a ρ ρ = Iso.refl _ := by
  rcases S with ⟨C | C⟩
  · let : (C.underlying.map ρ).toFunctor.IsContinuous
        (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck :=
      (C.isMorphismOfSites ρ).isContinuous
    let : (a : C.ContinuousAugmentation D K).functor.IsContinuous K
        (C.coverage (SimplexCategory.mk 0)).toGrothendieck :=
      (a : C.ContinuousAugmentation D K).isMorphismOfSites.isContinuous
    let : ((a : C.ContinuousAugmentation D K).functor ⋙
        (C.underlying.map ρ).toFunctor).IsContinuous K (C.coverage n).toGrothendieck :=
      Functor.isContinuous_comp (a : C.ContinuousAugmentation D K).functor
        (C.underlying.map ρ).toFunctor K
        (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck
    exact Functor.sheafPushforwardContinuousCompIsoOfEq_self K _ _ _ _ _
  · let : (C.underlying.map ρ.op).toFunctor.IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op n)))
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) :=
      C.isCocontinuous ρ.op
    let : (a : C.Augmentation D K).functor.IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K :=
      (a : C.Augmentation D K).isCocontinuous
    let : ((C.underlying.map ρ.op).toFunctor ⋙
        (a : C.Augmentation D K).functor).IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op n))) K :=
      CategoryTheory.isCocontinuous_comp (C.underlying.map ρ.op).toFunctor
        (a : C.Augmentation D K).functor (topologyOfCoverings (C.coverage (Opposite.op n)))
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0))))
    exact sheafPushforwardCocontinuousCompIsoOfEq_self _ _ K _ _ _

/-- The comparison of two vertices is unchanged by transporting the first vertex along an
equality of simplex maps. -/
public theorem vertexPushforwardIso_congr {n : SimplexCategory}
    {ρ ρ' σ : SimplexCategory.mk 0 ⟶ n} (h : ρ = ρ') :
    Functor.isoWhiskerRight (S.pushforwardCongr h)
          (Augmentation.morphismOfTopoi S D K a).pushforward ≪≫
        vertexPushforwardIso S D K a ρ' σ =
      vertexPushforwardIso S D K a ρ σ := by
  subst h
  simp [SimplicialSiteSituation.pushforwardCongr]

/-- The degree-zero component augmentation is the given augmentation. -/
public noncomputable def degreeZeroPushforwardIso :
    (componentAugmentation S D K a (SimplexCategory.mk 0)).pushforward ≅
      (Augmentation.morphismOfTopoi S D K a).pushforward :=
  Functor.isoWhiskerRight
        (S.pushforwardCongr (Subsingleton.elim
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0)
          (𝟙 (SimplexCategory.mk 0))))
        (Augmentation.morphismOfTopoi S D K a).pushforward ≪≫
      Functor.isoWhiskerRight (S.pushforwardId (SimplexCategory.mk 0))
        (Augmentation.morphismOfTopoi S D K a).pushforward ≪≫
    (Augmentation.morphismOfTopoi S D K a).pushforward.leftUnitor

/-- **Stacks 0D70, compatibility (1).** Composing the direct image of a simplicial transition
with the direct image of the component augmentation of its target agrees canonically with the
direct image of the component augmentation of its source. -/
@[stacks 0D70 "compatibility (1): composition with a simplicial transition"]
public noncomputable def transitionPushforwardIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionMorphism φ).pushforward ⋙
        (componentAugmentation S D K a m).pushforward ≅
      (componentAugmentation S D K a n).pushforward :=
  (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (S.pushforwardCompSymm (SimplexCategory.const (SimplexCategory.mk 0) m 0) φ)
        (Augmentation.morphismOfTopoi S D K a).pushforward ≪≫
    vertexPushforwardIso S D K a
      (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ)
      (SimplexCategory.const (SimplexCategory.mk 0) n 0)

/-- Every transition comparison is the composite of the simplicial compositor with the
comparison induced by the augmentation site functor. This fixes its value in every degree, not
only after restriction to degree zero. -/
public theorem transitionPushforwardIso_eq_canonical {m n : SimplexCategory} (φ : m ⟶ n) :
    transitionPushforwardIso S D K a φ =
      (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (S.pushforwardCompSymm (SimplexCategory.const (SimplexCategory.mk 0) m 0) φ)
            (Augmentation.morphismOfTopoi S D K a).pushforward ≪≫
        vertexPushforwardIso S D K a
          (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ)
          (SimplexCategory.const (SimplexCategory.mk 0) n 0) :=
  rfl

/-- **Stacks 0D70.** The transition comparison of the component augmentations satisfies the unit
law. -/
public theorem transitionPushforwardIso_id (n : SimplexCategory) :
    transitionPushforwardIso S D K a (𝟙 n) =
      Functor.isoWhiskerRight (S.pushforwardId n)
          (componentAugmentation S D K a n).pushforward ≪≫
        (componentAugmentation S D K a n).pushforward.leftUnitor := by
  have hc : SimplexCategory.const (SimplexCategory.mk 0) n 0 ≫ 𝟙 n =
      SimplexCategory.const (SimplexCategory.mk 0) n 0 := Category.comp_id _
  dsimp only [transitionPushforwardIso, componentAugmentation_pushforward]
  rw [← vertexPushforwardIso_congr S D K a hc, vertexPushforwardIso_self, Iso.trans_refl,
    ← Functor.isoWhiskerRight_trans, S.pushforwardCompSymm_comp_id,
    Functor.isoWhiskerRight_trans]
  apply Iso.ext
  ext X
  simp

/-- **Stacks 0D70.** On a vertex the transition comparison is normalized by the given
degree-zero augmentation. -/
public theorem transitionPushforwardIso_vertex {n : SimplexCategory}
    (φ : SimplexCategory.mk 0 ⟶ n) :
    transitionPushforwardIso S D K a φ =
      Functor.isoWhiskerLeft (S.transitionMorphism φ).pushforward
          (degreeZeroPushforwardIso S D K a) ≪≫
        vertexPushforwardIso S D K a φ
          (SimplexCategory.const (SimplexCategory.mk 0) n 0) := by
  have h : SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0 =
      𝟙 (SimplexCategory.mk 0) := Subsingleton.elim _ _
  have h2 : SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0 ≫ φ =
      𝟙 (SimplexCategory.mk 0) ≫ φ := by rw [h]
  have h3 : 𝟙 (SimplexCategory.mk 0) ≫ φ = φ := Category.id_comp φ
  have key : S.pushforwardCompSymm
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0) φ ≪≫
        S.pushforwardCongr (h2.trans h3) =
      Functor.isoWhiskerLeft (S.transitionMorphism φ).pushforward (S.pushforwardCongr h) ≪≫
        Functor.isoWhiskerLeft (S.transitionMorphism φ).pushforward
            (S.pushforwardId (SimplexCategory.mk 0)) ≪≫
          Functor.rightUnitor (S.transitionMorphism φ).pushforward := by
    rw [← S.pushforwardCongr_trans h2 h3, ← Iso.trans_assoc,
      S.pushforwardCompSymm_congr_left φ h h2, Iso.trans_assoc, S.pushforwardCompSymm_id_comp]
  dsimp only [transitionPushforwardIso, degreeZeroPushforwardIso,
    componentAugmentation_pushforward]
  rw [← vertexPushforwardIso_congr S D K a (h2.trans h3)]
  simp only [← Functor.isoWhiskerRight_trans, ← Iso.trans_assoc,
    Functor.isoWhiskerLeft_trans]
  rw [key]
  apply Iso.ext
  ext X
  simp

end Augmentation

end SimplicialSiteSituation

end CategoryTheory

end
