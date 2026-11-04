module

public import StacksFrontier.Deformation.Groupoid.Internal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.SitePullbackContainment

/-!
# The groupoid scheme of a groupoid represented on the big fppf site

Let `U` and `R` be objects of the big fppf site of a scheme `S`, let `s, t : R ⟶ U` be morphisms
of the site, and let `c` be a composition law on the presheaf of composable pairs of sections of
`R` which makes the sections over every test object a groupoid. This is the datum of a groupoid
whose object and arrow spaces are the representable algebraic spaces of `U` and `R`, the shape in
which condition (2) of Stacks 0DUM is stated
(`AlgebraicGeometry.Stack.representedGroupoid`). This file shows that it is a groupoid scheme
over `S` in the sense of Stacks 0231, with object scheme `U`, arrow scheme `R` and source and
target `s` and `t`. It is the converse of
`Stacks.Groupoids.GroupoidScheme.realization`.

## Main definitions

* `Deformation.GroupoidObject.toGroupoidScheme`: a groupoid object of the category of schemes
  over `S`, as a groupoid scheme over `S`.
* `AlgebraicGeometry.Space.representedGroupoidObject`: the groupoid object of the big fppf site
  determined by a represented groupoid.
* `AlgebraicGeometry.Space.representedGroupoidScheme`: the groupoid scheme over `S` it defines.

## Implementation notes

The pointwise groupoid structures of a represented groupoid are separate witnesses, one for each
test object, chosen by `Classical.choice`; the identity and the inverse they determine are
nevertheless natural in the test object, because in a groupoid the identity of an object is its
only idempotent arrow and the inverse of an arrow is its only left inverse
(`Deformation.PointwiseGroupoid.SetData.eq_identity_of_comp_self_eq` and
`Deformation.PointwiseGroupoid.SetData.eq_inverse_of_comp_eq_identity`), and composition is
natural. The identity and the inverse of the groupoid object are their values on the universal
sections, and every law of a groupoid object, which is stated on generalized elements over an
object of the site, is the corresponding law of the pointwise groupoid over that object.

The groupoid object is then transported to schemes over `S` along
`AlgebraicGeometry.Space.siteToOver`, with its object of composable pairs chosen so that its image
*is* the fibre product of schemes over `S` (`AlgebraicGeometry.BigFppfSite.contains_pullback_left`
places that fibre product in the site), which makes the two cartesian squares the transport asks
for hold by construction.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 0DUM](https://stacks.math.columbia.edu/tag/0DUM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

/-! ### Uniqueness of identities and inverses in internal groupoid data -/

namespace Deformation.PointwiseGroupoid.SetData

variable {U R : Type w} (D : SetData U R)

/-- Composition of internal groupoid data depends only on the two arrows, not on the proof that
they are composable. -/
theorem comp_congr {a a' b b' : R} (ha : a = a') (hb : b = b') (h : D.source a = D.target b)
    (h' : D.source a' = D.target b') : D.comp ⟨(a, b), h⟩ = D.comp ⟨(a', b'), h'⟩ := by
  subst ha hb
  rfl

/-- **An idempotent arrow is an identity.** -/
theorem eq_identity_of_comp_self_eq (x : U) (a : R) (hs : D.source a = x) (ht : D.target a = x)
    (h : D.source a = D.target a) (ha : D.comp ⟨(a, a), h⟩ = a) : a = D.identity x := by
  subst hs
  have e3 : D.comp ⟨(D.inverse a, a), D.source_inverse a⟩ = D.identity (D.source a) :=
    D.comp_inverse_left a
  calc a = D.comp ⟨(D.identity (D.target a), a), D.source_identity _⟩ :=
        (D.comp_identity_left a).symm
    _ = D.comp ⟨(D.comp ⟨(D.inverse a, a), D.source_inverse a⟩, a),
          (D.source_comp _).trans h⟩ :=
        D.comp_congr ((congrArg D.identity ht).trans e3.symm) rfl _ _
    _ = D.comp ⟨(D.inverse a, D.comp ⟨(a, a), h⟩),
          (D.source_inverse a).trans (D.target_comp ⟨(a, a), h⟩).symm⟩ :=
        D.comp_assoc (D.inverse a) a a (D.source_inverse a) h
    _ = D.comp ⟨(D.inverse a, a), D.source_inverse a⟩ := D.comp_congr rfl ha _ _
    _ = D.identity (D.source a) := e3

/-- **A left inverse is the inverse.** -/
theorem eq_inverse_of_comp_eq_identity (a b : R) (h : D.source b = D.target a)
    (hb : D.comp ⟨(b, a), h⟩ = D.identity (D.source a)) : b = D.inverse a := by
  calc b = D.comp ⟨(b, D.identity (D.source b)), (D.target_identity _).symm⟩ :=
        (D.comp_identity_right b).symm
    _ = D.comp ⟨(b, D.comp ⟨(a, D.inverse a), (D.target_inverse a).symm⟩),
          h.trans (D.target_comp ⟨(a, D.inverse a), (D.target_inverse a).symm⟩).symm⟩ :=
        D.comp_congr rfl ((congrArg D.identity h).trans (D.comp_inverse_right a).symm) _ _
    _ = D.comp ⟨(D.comp ⟨(b, a), h⟩, D.inverse a),
          (D.source_comp _).trans (D.target_inverse a).symm⟩ :=
        (D.comp_assoc b a (D.inverse a) h (D.target_inverse a).symm).symm
    _ = D.comp ⟨(D.identity (D.target (D.inverse a)), D.inverse a), D.source_identity _⟩ :=
        D.comp_congr (hb.trans (congrArg D.identity (D.target_inverse a).symm)) rfl _ _
    _ = D.inverse a := D.comp_identity_left (D.inverse a)

end Deformation.PointwiseGroupoid.SetData

/-! ### Groupoid objects of schemes over `S` are groupoid schemes -/

namespace Deformation.GroupoidObject

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- **A groupoid object of the category of schemes over `S` is a groupoid scheme over `S`.** The
composition is read on the chosen fibre product of the source and the target through the
comparison with the object of composable pairs. -/
noncomputable def toGroupoidScheme (G : GroupoidObject (Over S)) :
    Stacks.Groupoids.GroupoidScheme S where
  objects := G.objects
  arrows := G.arrows
  source := G.source
  target := G.target
  comp := G.isPullback_pairs.isoPullback.inv ≫ G.comp
  identity := G.identity
  inverse := G.inverse
  source_identity := G.identity_source
  target_identity := G.identity_target
  source_inverse := G.inverse_source
  target_inverse := G.inverse_target
  source_comp := by
    rw [Category.assoc, G.comp_source, ← Category.assoc, IsPullback.isoPullback_inv_snd]
  target_comp := by
    rw [Category.assoc, G.comp_target, ← Category.assoc, IsPullback.isoPullback_inv_fst]
  left_identity := fun T f w => by
    rw [← Category.assoc]
    exact G.comp_identity_left f _
      (by rw [Category.assoc, IsPullback.isoPullback_inv_fst, pullback.lift_fst])
      (by rw [Category.assoc, IsPullback.isoPullback_inv_snd, pullback.lift_snd])
  right_identity := fun T f w => by
    rw [← Category.assoc]
    exact G.comp_identity_right f _
      (by rw [Category.assoc, IsPullback.isoPullback_inv_fst, pullback.lift_fst])
      (by rw [Category.assoc, IsPullback.isoPullback_inv_snd, pullback.lift_snd])
  left_inverse := fun T f w => by
    rw [← Category.assoc]
    exact G.comp_inverse_left f _
      (by rw [Category.assoc, IsPullback.isoPullback_inv_fst, pullback.lift_fst])
      (by rw [Category.assoc, IsPullback.isoPullback_inv_snd, pullback.lift_snd])
  right_inverse := fun T f w => by
    rw [← Category.assoc]
    exact G.comp_inverse_right f _
      (by rw [Category.assoc, IsPullback.isoPullback_inv_fst, pullback.lift_fst])
      (by rw [Category.assoc, IsPullback.isoPullback_inv_snd, pullback.lift_snd])
  assoc := fun T f g h wfg wgh w₁ w₂ => by
    simpa only [Category.assoc] using
      G.comp_assoc (pullback.lift f g wfg ≫ G.isPullback_pairs.isoPullback.inv)
        (pullback.lift g h wgh ≫ G.isPullback_pairs.isoPullback.inv)
        (pullback.lift _ h w₁ ≫ G.isPullback_pairs.isoPullback.inv)
        (pullback.lift f _ w₂ ≫ G.isPullback_pairs.isoPullback.inv)
        (by simp only [Category.assoc, IsPullback.isoPullback_inv_fst,
          IsPullback.isoPullback_inv_snd, pullback.lift_fst, pullback.lift_snd])
        (by simp only [Category.assoc, IsPullback.isoPullback_inv_fst, pullback.lift_fst])
        (by simp only [Category.assoc, IsPullback.isoPullback_inv_snd, pullback.lift_snd])
        (by simp only [Category.assoc, IsPullback.isoPullback_inv_fst, pullback.lift_fst])
        (by simp only [Category.assoc, IsPullback.isoPullback_inv_snd, pullback.lift_snd])

end Deformation.GroupoidObject

/-! ### The groupoid object of a represented groupoid -/

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U R : BigFppfOver B S hS} (s t : R ⟶ U)
  (c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj R)
    (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj R)
  (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
    ((yoneda.map t).app T) fun p => c.app T p))

/-- The internal groupoid data on the sections over a test object. -/
noncomputable abbrev representedSetData (T : (BigFppfOver B S hS)ᵒᵖ) :
    Deformation.PointwiseGroupoid.SetData ((yoneda.obj U).obj T) ((yoneda.obj R).obj T) :=
  (Classical.choice (hG T)).toSetData

/-- The composite of two composable sections over a test object. -/
noncomputable abbrev representedComp {X : BigFppfOver B S hS} (a b : X ⟶ R)
    (h : a ≫ s = b ≫ t) : X ⟶ R :=
  c.app (op X) ⟨(a, b), h⟩

/-- Composition of sections is natural in the test object. -/
theorem representedComp_naturality {X X' : BigFppfOver B S hS} (g : X' ⟶ X) (a b : X ⟶ R)
    (h : a ≫ s = b ≫ t) (h' : (g ≫ a) ≫ s = (g ≫ b) ≫ t) :
    representedComp s t c (g ≫ a) (g ≫ b) h' = g ≫ representedComp s t c a b h :=
  NatTrans.naturality_apply c g.op (⟨(a, b), h⟩ : (Deformation.composableArrows (yoneda.obj U)
    (yoneda.obj R) (yoneda.map s) (yoneda.map t)).obj (op X))

/-- Composition of sections depends only on the two sections. -/
theorem representedComp_congr {X : BigFppfOver B S hS} {a a' b b' : X ⟶ R} (ha : a = a')
    (hb : b = b') (h : a ≫ s = b ≫ t) (h' : a' ≫ s = b' ≫ t) :
    representedComp s t c a b h = representedComp s t c a' b' h' := by
  subst ha hb
  rfl

/-- **The identity sections are natural in the test object.** -/
theorem representedSetData_identity_naturality {X X' : BigFppfOver B S hS} (g : X' ⟶ X)
    (x : X ⟶ U) :
    (representedSetData s t c hG (op X')).identity (g ≫ x) =
      g ≫ (representedSetData s t c hG (op X)).identity x := by
  have hsx : (representedSetData s t c hG (op X)).identity x ≫ s = x :=
    (representedSetData s t c hG (op X)).source_identity x
  have htx : (representedSetData s t c hG (op X)).identity x ≫ t = x :=
    (representedSetData s t c hG (op X)).target_identity x
  have hidem : representedComp s t c ((representedSetData s t c hG (op X)).identity x)
      ((representedSetData s t c hG (op X)).identity x) (hsx.trans htx.symm) =
        (representedSetData s t c hG (op X)).identity x :=
    ((representedSetData s t c hG (op X)).comp_congr
      (congrArg (representedSetData s t c hG (op X)).identity htx.symm) rfl _
      ((representedSetData s t c hG (op X)).source_identity _)).trans
      ((representedSetData s t c hG (op X)).comp_identity_left _)
  refine ((representedSetData s t c hG (op X')).eq_identity_of_comp_self_eq (g ≫ x)
    (g ≫ (representedSetData s t c hG (op X)).identity x)
    ((Category.assoc _ _ _).trans (congrArg (g ≫ ·) hsx))
    ((Category.assoc _ _ _).trans (congrArg (g ≫ ·) htx))
    (((Category.assoc _ _ _).trans (congrArg (g ≫ ·) (hsx.trans htx.symm))).trans
      (Category.assoc _ _ _).symm) ?_).symm
  exact (representedComp_naturality s t c g _ _ (hsx.trans htx.symm) _).trans
    (congrArg (g ≫ ·) hidem)

/-- **The inverse sections are natural in the test object.** -/
theorem representedSetData_inverse_naturality {X X' : BigFppfOver B S hS} (g : X' ⟶ X)
    (a : X ⟶ R) :
    (representedSetData s t c hG (op X')).inverse (g ≫ a) =
      g ≫ (representedSetData s t c hG (op X)).inverse a := by
  have hsv : (representedSetData s t c hG (op X)).inverse a ≫ s = a ≫ t :=
    (representedSetData s t c hG (op X)).source_inverse a
  refine ((representedSetData s t c hG (op X')).eq_inverse_of_comp_eq_identity (g ≫ a)
    (g ≫ (representedSetData s t c hG (op X)).inverse a)
    (((Category.assoc _ _ _).trans (congrArg (g ≫ ·) hsv)).trans (Category.assoc _ _ _).symm)
    ?_).symm
  refine (representedComp_naturality s t c g _ a hsv _).trans ?_
  refine (congrArg (g ≫ ·) ((representedSetData s t c hG (op X)).comp_inverse_left a)).trans ?_
  exact (representedSetData_identity_naturality s t c hG g (a ≫ s)).symm.trans
    (congrArg (representedSetData s t c hG (op X')).identity (Category.assoc g a s).symm)

/-- The identity section at a section `x : X ⟶ U` is `x` followed by the universal identity. -/
theorem representedSetData_identity_eq {X : BigFppfOver B S hS} (x : X ⟶ U) :
    (representedSetData s t c hG (op X)).identity x =
      x ≫ (representedSetData s t c hG (op U)).identity (𝟙 U) := by
  rw [← representedSetData_identity_naturality s t c hG x (𝟙 U), Category.comp_id]

/-- The inverse of a section `a : X ⟶ R` is `a` followed by the universal inverse. -/
theorem representedSetData_inverse_eq {X : BigFppfOver B S hS} (a : X ⟶ R) :
    (representedSetData s t c hG (op X)).inverse a =
      a ≫ (representedSetData s t c hG (op R)).inverse (𝟙 R) := by
  rw [← representedSetData_inverse_naturality s t c hG a (𝟙 R), Category.comp_id]

/-- The universal identity arrow `U ⟶ R`. -/
noncomputable abbrev representedIdentity : U ⟶ R :=
  (representedSetData s t c hG (op U)).identity (𝟙 U)

/-- The universal inverse `R ⟶ R`. -/
noncomputable abbrev representedInverse : R ⟶ R :=
  (representedSetData s t c hG (op R)).inverse (𝟙 R)

/-- The universal identity followed by the source is the identity of `U`. -/
theorem representedIdentity_source : representedIdentity s t c hG ≫ s = 𝟙 U :=
  (representedSetData s t c hG (op U)).source_identity (𝟙 U)

/-- The universal identity followed by the target is the identity of `U`. -/
theorem representedIdentity_target : representedIdentity s t c hG ≫ t = 𝟙 U :=
  (representedSetData s t c hG (op U)).target_identity (𝟙 U)

/-- The universal inverse followed by the source is the target. -/
theorem representedInverse_source : representedInverse s t c hG ≫ s = t :=
  ((representedSetData s t c hG (op R)).source_inverse (𝟙 R)).trans (Category.id_comp t)

/-- The universal inverse followed by the target is the source. -/
theorem representedInverse_target : representedInverse s t c hG ≫ t = s :=
  ((representedSetData s t c hG (op R)).target_inverse (𝟙 R)).trans (Category.id_comp s)

/-- The site object of composable pairs: the fibre product of schemes over `S` of `s` and `t`,
regarded in the site. -/
noncomputable abbrev representedPairs : BigFppfOver B S hS :=
  schemeSiteObject B hS (BigFppfSite.contains_pullback_left B ((siteToOver B hS).map s)
    ((siteToOver B hS).map t) R.left.2 R.left.2)

/-- The first projection from the composable pairs. -/
noncomputable abbrev representedFst : representedPairs s t ⟶ R :=
  (siteToOver B hS).preimage (pullback.fst ((siteToOver B hS).map s) ((siteToOver B hS).map t))

/-- The second projection from the composable pairs. -/
noncomputable abbrev representedSnd : representedPairs s t ⟶ R :=
  (siteToOver B hS).preimage (pullback.snd ((siteToOver B hS).map s) ((siteToOver B hS).map t))

/-- The image in schemes over `S` of `representedFst` is the first projection of the fibre
product. -/
theorem map_representedFst :
    (siteToOver B hS).map (representedFst s t) =
      pullback.fst ((siteToOver B hS).map s) ((siteToOver B hS).map t) :=
  Functor.map_preimage _ _

/-- The image in schemes over `S` of `representedSnd` is the second projection of the fibre
product. -/
theorem map_representedSnd :
    (siteToOver B hS).map (representedSnd s t) =
      pullback.snd ((siteToOver B hS).map s) ((siteToOver B hS).map t) :=
  Functor.map_preimage _ _

/-- The square of composable pairs commutes: the source of the first arrow is the target of the
second. -/
theorem representedFst_comp : representedFst s t ≫ s = representedSnd s t ≫ t := by
  apply (siteToOver B hS).map_injective
  rw [Functor.map_comp, Functor.map_comp, map_representedFst, map_representedSnd]
  exact pullback.condition

/-- The image of the square of composable pairs is the fibre product square of schemes over
`S`. -/
theorem isPullback_map_representedPairs :
    IsPullback ((siteToOver B hS).map (representedFst s t))
      ((siteToOver B hS).map (representedSnd s t)) ((siteToOver B hS).map s)
      ((siteToOver B hS).map t) := by
  rw [map_representedFst, map_representedSnd]
  exact IsPullback.of_hasPullback _ _

/-- The square of composable pairs is a pullback square of the site. -/
theorem isPullback_representedPairs :
    IsPullback (representedFst s t) (representedSnd s t) s t :=
  IsPullback.of_map (siteToOver B hS) (representedFst_comp s t)
    (isPullback_map_representedPairs s t)

/-- The site object of composable triples. -/
noncomputable abbrev representedTriples : BigFppfOver B S hS :=
  schemeSiteObject B hS (BigFppfSite.contains_pullback_left B
    ((siteToOver B hS).map (representedSnd s t)) ((siteToOver B hS).map (representedFst s t))
    (representedPairs s t).left.2 (representedPairs s t).left.2)

/-- The first projection from the composable triples to the composable pairs. -/
noncomputable abbrev representedFst₃ : representedTriples s t ⟶ representedPairs s t :=
  (siteToOver B hS).preimage (pullback.fst ((siteToOver B hS).map (representedSnd s t))
    ((siteToOver B hS).map (representedFst s t)))

/-- The second projection from the composable triples to the composable pairs. -/
noncomputable abbrev representedSnd₃ : representedTriples s t ⟶ representedPairs s t :=
  (siteToOver B hS).preimage (pullback.snd ((siteToOver B hS).map (representedSnd s t))
    ((siteToOver B hS).map (representedFst s t)))

/-- The image in schemes over `S` of `representedFst₃` is the first projection of the fibre
product. -/
theorem map_representedFst₃ :
    (siteToOver B hS).map (representedFst₃ s t) =
      pullback.fst ((siteToOver B hS).map (representedSnd s t))
        ((siteToOver B hS).map (representedFst s t)) :=
  Functor.map_preimage _ _

/-- The image in schemes over `S` of `representedSnd₃` is the second projection of the fibre
product. -/
theorem map_representedSnd₃ :
    (siteToOver B hS).map (representedSnd₃ s t) =
      pullback.snd ((siteToOver B hS).map (representedSnd s t))
        ((siteToOver B hS).map (representedFst s t)) :=
  Functor.map_preimage _ _

/-- The image of the square of composable triples is the fibre product square of schemes over
`S`. -/
theorem isPullback_map_representedTriples :
    IsPullback ((siteToOver B hS).map (representedFst₃ s t))
      ((siteToOver B hS).map (representedSnd₃ s t))
      ((siteToOver B hS).map (representedSnd s t))
      ((siteToOver B hS).map (representedFst s t)) := by
  rw [map_representedFst₃, map_representedSnd₃]
  exact IsPullback.of_hasPullback _ _

/-- The square of composable triples is a pullback square of the site. -/
theorem isPullback_representedTriples :
    IsPullback (representedFst₃ s t) (representedSnd₃ s t) (representedSnd s t)
      (representedFst s t) :=
  IsPullback.of_map (siteToOver B hS)
    ((siteToOver B hS).map_injective (by
      simpa only [Functor.map_comp] using (isPullback_map_representedTriples s t).w))
    (isPullback_map_representedTriples s t)

/-- The universal composition on composable pairs. -/
noncomputable abbrev representedCompMap : representedPairs s t ⟶ R :=
  representedComp s t c (representedFst s t) (representedSnd s t) (representedFst_comp s t)

/-- A generalized composable pair composed with the universal composition is the composite of
its two sections. -/
theorem comp_representedCompMap {X : BigFppfOver B S hS} (k : X ⟶ representedPairs s t) :
    k ≫ representedCompMap s t c = representedComp s t c (k ≫ representedFst s t)
      (k ≫ representedSnd s t) (by rw [Category.assoc, Category.assoc, representedFst_comp]) :=
  (representedComp_naturality s t c k _ _ _ _).symm

include hG in
/-- **Associativity of the universal composition**, on generalized composable triples presented
by four generalized composable pairs. -/
theorem representedComp_assoc {X : BigFppfOver B S hS} (k l m n : X ⟶ representedPairs s t)
    (hkl : k ≫ representedSnd s t = l ≫ representedFst s t)
    (hm₁ : m ≫ representedFst s t = k ≫ representedCompMap s t c)
    (hm₂ : m ≫ representedSnd s t = l ≫ representedSnd s t)
    (hn₁ : n ≫ representedFst s t = k ≫ representedFst s t)
    (hn₂ : n ≫ representedSnd s t = l ≫ representedCompMap s t c) :
    m ≫ representedCompMap s t c = n ≫ representedCompMap s t c := by
  have hab : (k ≫ representedFst s t) ≫ s = (k ≫ representedSnd s t) ≫ t := by
    rw [Category.assoc, Category.assoc, representedFst_comp]
  have hbd : (k ≫ representedSnd s t) ≫ s = (l ≫ representedSnd s t) ≫ t := by
    rw [hkl, Category.assoc, Category.assoc, representedFst_comp]
  have hm₁' : m ≫ representedFst s t = representedComp s t c (k ≫ representedFst s t)
      (k ≫ representedSnd s t) hab :=
    hm₁.trans (comp_representedCompMap s t c k)
  have hn₂' : n ≫ representedSnd s t = representedComp s t c (k ≫ representedSnd s t)
      (l ≫ representedSnd s t) hbd :=
    hn₂.trans ((comp_representedCompMap s t c l).trans
      (representedComp_congr s t c hkl.symm rfl _ _))
  refine (comp_representedCompMap s t c m).trans ?_
  refine Eq.trans ?_ (comp_representedCompMap s t c n).symm
  refine (representedComp_congr s t c hm₁' hm₂ _
    ((((representedSetData s t c hG (op X)).source_comp
      ⟨(k ≫ representedFst s t, k ≫ representedSnd s t), hab⟩).trans hbd))).trans ?_
  refine Eq.trans ?_ (representedComp_congr s t c hn₁.symm hn₂'.symm
    (hab.trans ((representedSetData s t c hG (op X)).target_comp
      ⟨(k ≫ representedSnd s t, l ≫ representedSnd s t), hbd⟩).symm) _)
  exact (representedSetData s t c hG (op X)).comp_assoc _ _ _ hab hbd

/-- **The groupoid object of the site determined by a represented groupoid.** -/
noncomputable def representedGroupoidObject : Deformation.GroupoidObject (BigFppfOver B S hS) where
  objects := U
  arrows := R
  pairs := representedPairs s t
  triples := representedTriples s t
  source := s
  target := t
  identity := representedIdentity s t c hG
  inverse := representedInverse s t c hG
  fst := representedFst s t
  snd := representedSnd s t
  isPullback_pairs := isPullback_representedPairs s t
  comp := representedCompMap s t c
  fst₃ := representedFst₃ s t
  snd₃ := representedSnd₃ s t
  isPullback_triples := isPullback_representedTriples s t
  identity_source := representedIdentity_source s t c hG
  identity_target := representedIdentity_target s t c hG
  inverse_source := representedInverse_source s t c hG
  inverse_target := representedInverse_target s t c hG
  comp_source := (representedSetData s t c hG (op (representedPairs s t))).source_comp
    ⟨(representedFst s t, representedSnd s t), representedFst_comp s t⟩
  comp_target := (representedSetData s t c hG (op (representedPairs s t))).target_comp
    ⟨(representedFst s t, representedSnd s t), representedFst_comp s t⟩
  comp_identity_left := by
    intro X a k h₁ h₂
    have h₁' : k ≫ representedFst s t = (representedSetData s t c hG (op X)).identity (a ≫ t) :=
      (h₁.trans (Category.assoc _ _ _).symm).trans
        (representedSetData_identity_eq s t c hG (a ≫ t)).symm
    exact (comp_representedCompMap s t c k).trans
      ((representedComp_congr s t c h₁' h₂ _
        ((representedSetData s t c hG (op X)).source_identity _)).trans
        ((representedSetData s t c hG (op X)).comp_identity_left a))
  comp_identity_right := by
    intro X a k h₁ h₂
    have h₂' : k ≫ representedSnd s t = (representedSetData s t c hG (op X)).identity (a ≫ s) :=
      (h₂.trans (Category.assoc _ _ _).symm).trans
        (representedSetData_identity_eq s t c hG (a ≫ s)).symm
    exact (comp_representedCompMap s t c k).trans
      ((representedComp_congr s t c h₁ h₂' _
        ((representedSetData s t c hG (op X)).target_identity _).symm).trans
        ((representedSetData s t c hG (op X)).comp_identity_right a))
  comp_inverse_left := by
    intro X a k h₁ h₂
    have h₁' : k ≫ representedFst s t = (representedSetData s t c hG (op X)).inverse a :=
      h₁.trans (representedSetData_inverse_eq s t c hG a).symm
    exact (comp_representedCompMap s t c k).trans
      ((representedComp_congr s t c h₁' h₂ _
        ((representedSetData s t c hG (op X)).source_inverse a)).trans
        (((representedSetData s t c hG (op X)).comp_inverse_left a).trans
          ((representedSetData_identity_eq s t c hG (a ≫ s)).trans (Category.assoc _ _ _))))
  comp_inverse_right := by
    intro X a k h₁ h₂
    have h₂' : k ≫ representedSnd s t = (representedSetData s t c hG (op X)).inverse a :=
      h₂.trans (representedSetData_inverse_eq s t c hG a).symm
    exact (comp_representedCompMap s t c k).trans
      ((representedComp_congr s t c h₁ h₂' _
        ((representedSetData s t c hG (op X)).target_inverse a).symm).trans
        (((representedSetData s t c hG (op X)).comp_inverse_right a).trans
          ((representedSetData_identity_eq s t c hG (a ≫ t)).trans (Category.assoc _ _ _))))
  comp_assoc := fun k l m n hkl hm₁ hm₂ hn₁ hn₂ =>
    representedComp_assoc s t c hG k l m n hkl hm₁ hm₂ hn₁ hn₂

/-- **The groupoid scheme over `S` of a represented groupoid.** Its object scheme, arrow scheme,
source and target are those of `U`, `R`, `s` and `t`, read as schemes and morphisms of schemes
over `S`. -/
noncomputable def representedGroupoidScheme : Stacks.Groupoids.GroupoidScheme S :=
  ((representedGroupoidObject s t c hG).mapOfIsPullback (siteToOver B hS)
    (isPullback_map_representedPairs s t) (isPullback_map_representedTriples s t)).toGroupoidScheme

/-- The object scheme of `representedGroupoidScheme` is the scheme of `U`. -/
@[simp]
theorem representedGroupoidScheme_objects :
    (representedGroupoidScheme s t c hG).objects = (siteToOver B hS).obj U := rfl

/-- The arrow scheme of `representedGroupoidScheme` is the scheme of `R`. -/
@[simp]
theorem representedGroupoidScheme_arrows :
    (representedGroupoidScheme s t c hG).arrows = (siteToOver B hS).obj R := rfl

/-- The source of `representedGroupoidScheme` is the morphism of schemes of `s`. -/
@[simp]
theorem representedGroupoidScheme_source :
    (representedGroupoidScheme s t c hG).source = (siteToOver B hS).map s := rfl

/-- The target of `representedGroupoidScheme` is the morphism of schemes of `t`. -/
@[simp]
theorem representedGroupoidScheme_target :
    (representedGroupoidScheme s t c hG).target = (siteToOver B hS).map t := rfl

end AlgebraicGeometry.Space

end
