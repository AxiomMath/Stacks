module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FpqcLocalColimit
public import StacksFrontier.AlgebraicGeometry.Pushout.Coproduct
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Pushout.QuasiFiniteFunctoriality
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.Colimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# A pushout of schemes is a pushout of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion and `j : Z ⟶ Y` an integral morphism of schemes over a
base scheme `S`, subject to the fibrewise affineness condition of [Stacks Project, Tag 0ECI], so
that the pushout `Y ⨿_Z X` exists as a scheme by [Stacks Project, Tag 0E25].  Regarding the four
schemes and the four canonical morphisms as objects and morphisms of a big fppf site over `S`,
and then as algebraic spaces over `S` through the Yoneda embedding, the resulting square is a
pushout square in the category of algebraic spaces over `S`.

## Main definitions

* `AlgebraicGeometry.Space.fppfOverX`, `AlgebraicGeometry.Space.fppfOverY`,
  `AlgebraicGeometry.Space.fppfOverZ` and `AlgebraicGeometry.Space.fppfOverPushout`: the four
  schemes of the pushout square as objects of a big fppf site over `S`.
* `AlgebraicGeometry.Space.fppfOverI`, `AlgebraicGeometry.Space.fppfOverJ`,
  `AlgebraicGeometry.Space.fppfOverInl` and `AlgebraicGeometry.Space.fppfOverInr`: the four
  canonical morphisms of the pushout square as morphisms of that site.

## Main results

* `AlgebraicGeometry.Space.pushout_isPushout_algebraicSpaces`: **Stacks 0EDP**, the square is a
  pushout square of algebraic spaces over `S`.

## Implementation notes

The big fppf site is required to contain the five schemes `S`, `X`, `Y`, `Z` and `Y ⨿_Z X`; for
the last of these the hypothesis is not an extra assumption in disguise, since the size of the
pushout is bounded by the sizes of `X` and `Y` (`pushoutScheme_size_le` below).

The universal property is obtained from
`AlgebraicGeometry.Space.isColimit_algebraicSpaces_of_scheme` of [Stacks Project, Tag 07SX],
whose three hypotheses are discharged as follows.  The cocone is a colimit of schemes because
the pushout square is one; it covers the pushout on points because the coproduct `Y ⨿ X` already
does ([Stacks Project, Tag 0E25]); and a cartesian family of separated étale objects over the
span descends because `AlgebraicGeometry.CartesianDiagram` assembles such a family into a
cartesian diagram over the situation, whose pushout maps étale to `Y ⨿_Z X`
([Stacks Project, Tag 0ECK], [Stacks Project, Tag 0ECL]).  Conversely every separated étale
scheme over `Y ⨿_Z X` *is* such a pushout, by the equivalence of [Stacks Project, Tag 0ECL];
étale base change therefore preserves the colimit, first for separated étale morphisms and then
in general by the fpqc-local criterion of [Stacks Project, Tag 0BMP] applied to an affine open
cover.

Tag 07SX is stated for a diagram indexed by a `Type u` category, so the walking span — which
lives in `Type 0` — is replaced throughout by the equivalent `ULiftHom (ULift WalkingSpan)`.

## References

* [Stacks Project, Tag 0EDP](https://stacks.math.columbia.edu/tag/0EDP)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECK](https://stacks.math.columbia.edu/tag/0ECK)
* [Stacks Project, Tag 0ECL](https://stacks.math.columbia.edu/tag/0ECL)
* [Stacks Project, Tag 07SX](https://stacks.math.columbia.edu/tag/07SX)
* [Stacks Project, Tag 0BMP](https://stacks.math.columbia.edu/tag/0BMP)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
variable (B : BigFppfSite.{u})
variable (hS : B.Contains s.S) (hX : B.Contains s.X)
variable (hY : B.Contains s.Y) (hZ : B.Contains s.Z)
variable (hP : B.Contains (pushoutScheme s))

/-! ### Fibre products in the big fppf site -/

attribute [local instance] schemeCutoff_hasPullbacks

/-! ### The walking span, lifted to the universe of the site -/

private abbrev LiftedWalkingSpan := ULiftHom.{u} (ULift.{u} WalkingSpan)

private def liftedWalkingSpanEquiv : WalkingSpan ≌ LiftedWalkingSpan.{u} :=
  ULiftHomULiftCategory.equiv WalkingSpan

private def liftedWalkingSpanDown : LiftedWalkingSpan.{u} ⥤ WalkingSpan :=
  liftedWalkingSpanEquiv.symm.functor

/-! ### Elementary properties of the scheme pushout -/

/-- The two canonical morphisms to the pushout along a closed immersion and an integral
morphism are jointly surjective on points. -/
lemma pushoutScheme_jointly_surjective (p : pushoutScheme s) :
    (∃ y : s.Y, pushoutInr s y = p) ∨ (∃ x : s.X, pushoutInl s x = p) := by
  obtain ⟨w, hw⟩ := (pushoutCoprodDesc_surjective s).surj p
  obtain ⟨(y | x), rfl⟩ := (AlgebraicGeometry.coprodMk s.Y s.X).surjective w
  · exact Or.inl ⟨y, by
      simpa [pushoutCoprodDesc, ← Scheme.Hom.comp_apply, coprod.inl_desc] using hw⟩
  · exact Or.inr ⟨x, by
      simpa [pushoutCoprodDesc, ← Scheme.Hom.comp_apply, coprod.inr_desc] using hw⟩

/-- The affine opens of the pushout are no more numerous than the two schemes being glued are
large. -/
private lemma mk_affineOpens_pushoutScheme_le :
    #(pushoutScheme s).affineOpens ≤ max s.X.size s.Y.size := by
  let f : (pushoutScheme s).affineOpens → s.X.affineOpens × s.Y.affineOpens := fun U =>
    (⟨pushoutInl s ⁻¹ᵁ U.1, U.2.preimage (pushoutInl s)⟩,
      ⟨pushoutInr s ⁻¹ᵁ U.1, U.2.preimage (pushoutInr s)⟩)
  have hf : Function.Injective f := by
    intro U V h
    apply Subtype.ext
    ext p
    rcases pushoutScheme_jointly_surjective s p with ⟨y, hy⟩ | ⟨x, hx⟩
    · have hpre : pushoutInr s ⁻¹ᵁ U.1 = pushoutInr s ⁻¹ᵁ V.1 :=
        congrArg (fun q : s.X.affineOpens × s.Y.affineOpens => q.2.1) h
      rw [← hy]
      show y ∈ (pushoutInr s ⁻¹ᵁ U.1).1 ↔ y ∈ (pushoutInr s ⁻¹ᵁ V.1).1
      rw [hpre]
    · have hpre : pushoutInl s ⁻¹ᵁ U.1 = pushoutInl s ⁻¹ᵁ V.1 :=
        congrArg (fun q : s.X.affineOpens × s.Y.affineOpens => q.1.1) h
      rw [← hx]
      show x ∈ (pushoutInl s ⁻¹ᵁ U.1).1 ↔ x ∈ (pushoutInl s ⁻¹ᵁ V.1).1
      rw [hpre]
  calc
    #((pushoutScheme s).affineOpens) ≤ #(s.X.affineOpens × s.Y.affineOpens) :=
      Cardinal.mk_le_of_injective hf
    _ = #(s.X.affineOpens) * #(s.Y.affineOpens) := by simp [Cardinal.mk_prod]
    _ ≤ max (max #(s.X.affineOpens) #(s.Y.affineOpens)) ℵ₀ := Cardinal.mul_le_max _ _
    _ ≤ max s.X.size s.Y.size := max_le
      (max_le_max (Scheme.mk_affineOpens_le_size s.X)
        (Scheme.mk_affineOpens_le_size s.Y))
      ((Scheme.aleph0_le_size s.X).trans (le_max_left _ _))

/-- The sections of the pushout over an affine open are no more numerous than the two schemes
being glued are large. -/
private lemma mk_sections_pushoutScheme_le (U : (pushoutScheme s).affineOpens) :
    #Γ(pushoutScheme s, U.1) ≤ max s.X.size s.Y.size := by
  let hPB := (pushoutStructureSheaf_isPullback s U.1).map (forget CommRingCat)
  let f : Γ(pushoutScheme s, U.1) → Γ(s.Y, pushoutInr s ⁻¹ᵁ U.1) ×
      Γ(s.X, pushoutInl s ⁻¹ᵁ U.1) := fun a =>
    ((pushoutInr s).app U.1 a, (pushoutInl s).app U.1 a)
  have hf : Function.Injective f := fun a b hab =>
    PullbackCone.IsLimit.type_ext hPB.isLimit (congrArg Prod.fst hab) (congrArg Prod.snd hab)
  have hY : #Γ(s.Y, pushoutInr s ⁻¹ᵁ U.1) ≤ max s.X.size s.Y.size :=
    le_trans (Scheme.mk_sections_le_size s.Y
      ⟨pushoutInr s ⁻¹ᵁ U.1, U.2.preimage (pushoutInr s)⟩)
      (le_max_right s.X.size s.Y.size)
  have hX : #Γ(s.X, pushoutInl s ⁻¹ᵁ U.1) ≤ max s.X.size s.Y.size :=
    le_trans (Scheme.mk_sections_le_size s.X
      ⟨pushoutInl s ⁻¹ᵁ U.1, U.2.preimage (pushoutInl s)⟩)
      (le_max_left s.X.size s.Y.size)
  calc
    #(Γ(pushoutScheme s, U.1)) ≤
        #(Γ(s.Y, pushoutInr s ⁻¹ᵁ U.1) × Γ(s.X, pushoutInl s ⁻¹ᵁ U.1)) :=
      Cardinal.mk_le_of_injective hf
    _ = #Γ(s.Y, pushoutInr s ⁻¹ᵁ U.1) * #Γ(s.X, pushoutInl s ⁻¹ᵁ U.1) := by
      simp [Cardinal.mk_prod]
    _ ≤ max (max #Γ(s.Y, pushoutInr s ⁻¹ᵁ U.1)
        #Γ(s.X, pushoutInl s ⁻¹ᵁ U.1)) ℵ₀ := Cardinal.mul_le_max _ _
    _ ≤ max s.X.size s.Y.size :=
      max_le (max_le hY hX) ((Scheme.aleph0_le_size s.X).trans (le_max_left _ _))

/-- The pushout along a closed immersion and an integral morphism is no bigger than the two
schemes being glued: a big site containing `X` and `Y` contains the pushout. -/
lemma pushoutScheme_size_le :
    (pushoutScheme s).size ≤ max s.X.size s.Y.size :=
  Scheme.size_le_of_bounds ((Scheme.aleph0_le_size s.X).trans (le_max_left _ _))
    (mk_affineOpens_pushoutScheme_le s) (mk_sections_pushoutScheme_le s)

/-- The canonical morphism `X ⟶ Y ⨿_Z X` is a morphism over the base scheme `S`. -/
lemma pushoutToBase_inl : pushoutInl s ≫ pushoutToBase s = s.pX :=
  (pushoutAlongClosedImmersionAndIntegral s).isPushout.inl_desc
    s.pX s.pY (s.i_over.trans s.j_over.symm)

/-- The canonical morphism `Y ⟶ Y ⨿_Z X` is a morphism over the base scheme `S`. -/
lemma pushoutToBase_inr : pushoutInr s ≫ pushoutToBase s = s.pY :=
  (pushoutAlongClosedImmersionAndIntegral s).isPushout.inr_desc
    s.pX s.pY (s.i_over.trans s.j_over.symm)

private lemma inducedPushout_contains (d : CartesianDiagram s)
    (hX' : B.Contains d.X') (hY' : B.Contains d.Y') :
    B.Contains (pushoutScheme (inducedSituation s d)) :=
  (pushoutScheme_size_le (inducedSituation s d)).trans_lt (max_lt hX' hY')

/-! ### The pushout square in the big fppf site -/

/-- `X` as an object of a chosen big fppf site over `S`. -/
def fppfOverX : BigFppfOver B s.S hS := BigFppfOver.mk B s.S hS hX s.pX

/-- `Y` as an object of a chosen big fppf site over `S`. -/
def fppfOverY : BigFppfOver B s.S hS := BigFppfOver.mk B s.S hS hY s.pY

/-- `Z` as an object of a chosen big fppf site over `S`. -/
def fppfOverZ : BigFppfOver B s.S hS := BigFppfOver.mk B s.S hS hZ s.pZ

/-- The scheme pushout `Y ⨿_Z X` as an object of a chosen big fppf site over `S`. -/
noncomputable def fppfOverPushout : BigFppfOver B s.S hS :=
  BigFppfOver.mk B s.S hS hP (pushoutToBase s)

/-- The closed immersion `Z ⟶ X` as a morphism of a chosen big fppf site over `S`. -/
def fppfOverI : fppfOverZ s B hS hZ ⟶ fppfOverX s B hS hX :=
  BigFppfOver.homMk B s.S hS hX s.pX s.i s.i_over

/-- The integral morphism `Z ⟶ Y` as a morphism of a chosen big fppf site over `S`. -/
def fppfOverJ : fppfOverZ s B hS hZ ⟶ fppfOverY s B hS hY :=
  BigFppfOver.homMk B s.S hS hY s.pY s.j s.j_over

/-- The canonical morphism `X ⟶ Y ⨿_Z X` as a morphism of a chosen big fppf site over `S`. -/
noncomputable def fppfOverInl : fppfOverX s B hS hX ⟶ fppfOverPushout s B hS hP :=
  BigFppfOver.homMk B s.S hS hP (pushoutToBase s) (pushoutInl s) (pushoutToBase_inl s)

/-- The canonical morphism `Y ⟶ Y ⨿_Z X` as a morphism of a chosen big fppf site over `S`. -/
noncomputable def fppfOverInr : fppfOverY s B hS hY ⟶ fppfOverPushout s B hS hP :=
  BigFppfOver.homMk B s.S hS hP (pushoutToBase s) (pushoutInr s) (pushoutToBase_inr s)

private def liftedPushoutDiagram : LiftedWalkingSpan.{u} ⥤ BigFppfOver B s.S hS :=
  liftedWalkingSpanDown ⋙ span (fppfOverI s B hS hX hZ) (fppfOverJ s B hS hY hZ)

private noncomputable def pushoutSpanCocone :
    PushoutCocone (fppfOverI s B hS hX hZ) (fppfOverJ s B hS hY hZ) :=
  PushoutCocone.mk (fppfOverInl s B hS hX hP) (fppfOverInr s B hS hY hP) (by
    ext
    exact (pushoutAlongClosedImmersionAndIntegral s).isPushout.w)

private noncomputable def liftedPushoutCocone :
    Cocone (liftedPushoutDiagram s B hS hX hY hZ) :=
  (pushoutSpanCocone s B hS hX hY hZ hP).whisker liftedWalkingSpanEquiv.symm.functor

private lemma liftedPushoutCocone_ι_right :
    (liftedPushoutCocone s B hS hX hY hZ hP).ι.app (ULift.up WalkingSpan.right) =
      fppfOverInr s B hS hY hP := rfl

private lemma liftedPushoutCocone_ι_left :
    (liftedPushoutCocone s B hS hX hY hZ hP).ι.app (ULift.up WalkingSpan.left) =
      fppfOverInl s B hS hX hP := rfl

private noncomputable def liftedPushoutCocone_isColimit :
    IsColimit ((BigFppfOver.toScheme B s.S hS).mapCocone
      (liftedPushoutCocone s B hS hX hY hZ hP)) := by
  let G := BigFppfOver.toScheme B s.S hS
  have hBase : IsColimit (G.mapCocone (pushoutSpanCocone s B hS hX hY hZ hP)) := by
    have hi : G.map (fppfOverI s B hS hX hZ) = s.i := rfl
    have hj : G.map (fppfOverJ s B hS hY hZ) = s.j := rfl
    let α : ((span (fppfOverI s B hS hX hZ) (fppfOverJ s B hS hY hZ)) ⋙ G) ≅ span s.i s.j :=
      (spanCompIso G (fppfOverI s B hS hX hZ) (fppfOverJ s B hS hY hZ)).trans
        (spanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simpa [hi]) (by simpa [hj]))
    let c := (pushoutAlongClosedImmersionAndIntegral s).isPushout.cocone
    have hc : IsColimit ((Cocone.precompose α.hom).obj c) :=
      (IsColimit.precomposeInvEquiv α.symm c).symm
        (pushoutAlongClosedImmersionAndIntegral s).isPushout.isColimit
    have e : (Cocone.precompose α.hom).obj c ≅
        G.mapCocone (pushoutSpanCocone s B hS hX hY hZ hP) := by
      refine Cocone.ext (c := (Cocone.precompose α.hom).obj c)
        (c' := G.mapCocone (pushoutSpanCocone s B hS hX hY hZ hP)) (Iso.refl _) ?_
      rintro (_ | (_ | _)) <;> rfl
    exact IsColimit.ofIsoColimit hc e
  exact IsColimit.ofIsoColimit (hBase.whiskerEquivalence liftedWalkingSpanEquiv.symm)
    (Functor.mapCoconeWhisker G).symm

private lemma liftedPushoutCocone_covers :
    ∀ x : (BigFppfOver.toScheme B s.S hS).obj
        (liftedPushoutCocone s B hS hX hY hZ hP).pt,
      ∃ (i : LiftedWalkingSpan.{u})
        (y : (BigFppfOver.toScheme B s.S hS).obj
          ((liftedPushoutDiagram s B hS hX hY hZ).obj i)),
        (BigFppfOver.toScheme B s.S hS).map
          ((liftedPushoutCocone s B hS hX hY hZ hP).ι.app i) y = x := by
  intro x
  rcases pushoutScheme_jointly_surjective s x with ⟨y, hy⟩ | ⟨x, hx⟩
  · exact ⟨ULift.up WalkingSpan.right, y, hy⟩
  · exact ⟨ULift.up WalkingSpan.left, x, hx⟩

/-! ### Étale descent along the pushout square -/

/-- A cartesian family of separated étale objects over the span, read off as a cartesian diagram
over the pushout situation in the sense of [Stacks Project, Tag 0ECK]. -/
private noncomputable def cartesianDiagramOfSpanMap
    (E : WalkingSpan ⥤ BigFppfOver B s.S hS)
    (p : E ⟶ span (fppfOverI s B hS hX hZ) (fppfOverJ s B hS hY hZ))
    (hCart : ∀ {i j : WalkingSpan} (f : i ⟶ j),
      IsPullback (E.map f) (p.app i) (p.app j)
        ((span (fppfOverI s B hS hX hZ) (fppfOverJ s B hS hY hZ)).map f))
    (hEtale : ∀ i, Etale ((BigFppfOver.toScheme B s.S hS).map (p.app i)))
    (hSep : ∀ i, _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B s.S hS).map (p.app i))) :
    CartesianDiagram s := by
  let Q := BigFppfOver.toScheme B s.S hS
  let : HasPullbacks (BigFppfOver B s.S hS) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan Q := by apply comp_preservesLimitsOfShape
  have := hEtale WalkingSpan.left
  have := hEtale WalkingSpan.right
  have := hEtale WalkingSpan.zero
  exact {
    X' := Q.obj (E.obj WalkingSpan.left)
    Y' := Q.obj (E.obj WalkingSpan.right)
    Z' := Q.obj (E.obj WalkingSpan.zero)
    i' := Q.map (E.map WalkingSpan.Hom.fst)
    j' := Q.map (E.map WalkingSpan.Hom.snd)
    f := Q.map (p.app WalkingSpan.left)
    g := Q.map (p.app WalkingSpan.right)
    h := Q.map (p.app WalkingSpan.zero)
    left_isPullback := (hCart WalkingSpan.Hom.fst).map Q
    right_isPullback := (hCart WalkingSpan.Hom.snd).map Q
    f_isSeparated := hSep WalkingSpan.left
    g_isSeparated := hSep WalkingSpan.right
    h_isSeparated := hSep WalkingSpan.zero
    f_locallyOfFiniteType :=
      (locallyQuasiFinite_of_etale (Q.map (p.app WalkingSpan.left))).1
    g_locallyOfFiniteType :=
      (locallyQuasiFinite_of_etale (Q.map (p.app WalkingSpan.right))).1
    h_locallyOfFiniteType :=
      (locallyQuasiFinite_of_etale (Q.map (p.app WalkingSpan.zero))).1
    f_locallyQuasiFinite :=
      (locallyQuasiFinite_of_etale (Q.map (p.app WalkingSpan.left))).2
    g_locallyQuasiFinite :=
      (locallyQuasiFinite_of_etale (Q.map (p.app WalkingSpan.right))).2
    h_locallyQuasiFinite :=
      (locallyQuasiFinite_of_etale (Q.map (p.app WalkingSpan.zero))).2
  }

/-- The pushout map induced by a cartesian diagram is a morphism over the base scheme `S`. -/
private lemma pushoutMap_comp_pushoutToBase (d : CartesianDiagram s) :
    pushoutMap s d ≫ pushoutToBase s = pushoutToBase (inducedSituation s d) := by
  let t := inducedSituation s d
  apply (pushoutAlongClosedImmersionAndIntegral t).isPushout.hom_ext
  · have hm : pushoutInl t ≫ pushoutMap s d = d.f ≫ pushoutInl s :=
      (pushoutAlongClosedImmersionAndIntegral t).isPushout.inl_desc
        (d.f ≫ pushoutInl s) (d.g ≫ pushoutInr s) _
    rw [reassoc_of% hm, pushoutToBase_inl, pushoutToBase_inl]
  · have hm : pushoutInr t ≫ pushoutMap s d = d.g ≫ pushoutInr s :=
      (pushoutAlongClosedImmersionAndIntegral t).isPushout.inr_desc
        (d.f ≫ pushoutInl s) (d.g ≫ pushoutInr s) _
    rw [reassoc_of% hm, pushoutToBase_inr, pushoutToBase_inr]

private theorem exists_etaleDescent_span
    (E : WalkingSpan ⥤ BigFppfOver B s.S hS)
    (p : E ⟶ span (fppfOverI s B hS hX hZ) (fppfOverJ s B hS hY hZ))
    (hCart : ∀ {i j : WalkingSpan} (f : i ⟶ j),
      IsPullback (E.map f) (p.app i) (p.app j)
        ((span (fppfOverI s B hS hX hZ) (fppfOverJ s B hS hY hZ)).map f))
    (hEtale : ∀ i, Etale ((BigFppfOver.toScheme B s.S hS).map (p.app i)))
    (hSep : ∀ i, _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B s.S hS).map (p.app i))) :
    ∃ (U : BigFppfOver B s.S hS) (v : U ⟶ fppfOverPushout s B hS hP)
      (q : E ⟶ (Functor.const WalkingSpan).obj U),
      Etale ((BigFppfOver.toScheme B s.S hS).map v) ∧
        ∀ i, IsPullback (p.app i) (q.app i)
          ((pushoutSpanCocone s B hS hX hY hZ hP).ι.app i) v := by
  classical
  let Q := BigFppfOver.toScheme B s.S hS
  let d := cartesianDiagramOfSpanMap s B hS hX hY hZ E p hCart hEtale hSep
  let : Etale d.f := hEtale WalkingSpan.left
  let : Etale d.g := hEtale WalkingSpan.right
  let : Etale d.h := hEtale WalkingSpan.zero
  let t := inducedSituation s d
  have hDX : B.Contains d.X' := (E.obj WalkingSpan.left).left.property
  have hDY : B.Contains d.Y' := (E.obj WalkingSpan.right).left.property
  have hT : B.Contains (pushoutScheme t) := inducedPushout_contains s B d hDX hDY
  let U := fppfOverPushout t B hS hT
  let v : U ⟶ fppfOverPushout s B hS hP :=
    BigFppfOver.homMk B s.S hS hP (pushoutToBase s) (pushoutMap s d)
      (pushoutMap_comp_pushoutToBase s d)
  have hBase : ∀ {A A' : BigFppfOver B s.S hS} (g : A ⟶ A'),
      Q.map g ≫ B.inclusion.map A'.hom = B.inclusion.map A.hom :=
    fun g => congrArg B.inclusion.map g.w
  let qL : E.obj WalkingSpan.left ⟶ U :=
    BigFppfOver.homMk B s.S hS hT (pushoutToBase t) (pushoutInl t)
      ((pushoutToBase_inl t).trans (hBase (p.app WalkingSpan.left)))
  let qR : E.obj WalkingSpan.right ⟶ U :=
    BigFppfOver.homMk B s.S hS hT (pushoutToBase t) (pushoutInr t)
      ((pushoutToBase_inr t).trans (hBase (p.app WalkingSpan.right)))
  have hCompat : E.map WalkingSpan.Hom.fst ≫ qL = E.map WalkingSpan.Hom.snd ≫ qR := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    show Q.map (E.map WalkingSpan.Hom.fst) ≫ pushoutInl t =
      Q.map (E.map WalkingSpan.Hom.snd) ≫ pushoutInr t
    exact (pushoutAlongClosedImmersionAndIntegral t).isPushout.w
  let qBase : PushoutCocone (E.map WalkingSpan.Hom.fst) (E.map WalkingSpan.Hom.snd) :=
    PushoutCocone.mk qL qR hCompat
  let q : E ⟶ (Functor.const WalkingSpan).obj U :=
    ((Cocone.precompose (diagramIsoSpan E).hom).obj qBase).ι
  refine ⟨U, v, q, etale_pushoutMap s d, ?_⟩
  let : ReflectsLimitsOfShape WalkingCospan Q := by apply comp_reflectsLimitsOfShape
  suffices H : ∀ i, IsPullback (Q.map (p.app i)) (Q.map (q.app i))
      (Q.map ((pushoutSpanCocone s B hS hX hY hZ hP).ι.app i)) (Q.map v) from
    fun i => IsPullback.of_map Q (BigFppfOver.map_toScheme_injective B s.S hS
      ((Q.map_comp _ _).trans ((H i).w.trans (Q.map_comp _ _).symm))) (H i)
  rintro (_ | (_ | _))
  · exact (((hCart WalkingSpan.Hom.fst).map Q).paste_horiz
      (pushoutMap_left_isPullback s d)).flip
  · exact (pushoutMap_left_isPullback s d).flip
  · exact (pushoutMap_right_isPullback s d).flip

private theorem exists_etaleDescent
    (E : LiftedWalkingSpan.{u} ⥤ BigFppfOver B s.S hS)
    (p : E ⟶ liftedPushoutDiagram s B hS hX hY hZ)
    (hEtale : ∀ i, Etale ((BigFppfOver.toScheme B s.S hS).map (p.app i)))
    (hSep : ∀ i, _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B s.S hS).map (p.app i)))
    (hCart : ∀ {i j} (f : i ⟶ j), IsPullback (E.map f) (p.app i) (p.app j)
      ((liftedPushoutDiagram s B hS hX hY hZ).map f)) :
    ∃ (U : BigFppfOver B s.S hS)
      (v : U ⟶ (liftedPushoutCocone s B hS hX hY hZ hP).pt)
      (q : E ⟶ (Functor.const LiftedWalkingSpan.{u}).obj U),
      Etale ((BigFppfOver.toScheme B s.S hS).map v) ∧
        ∀ i, IsPullback (p.app i) (q.app i)
          ((liftedPushoutCocone s B hS hX hY hZ hP).ι.app i) v := by
  let E' := liftedWalkingSpanEquiv.functor ⋙ E
  let p' : E' ⟶ span (fppfOverI s B hS hX hZ) (fppfOverJ s B hS hY hZ) :=
    Functor.whiskerLeft liftedWalkingSpanEquiv.functor p
  obtain ⟨U, v, q, hv, hq⟩ := exists_etaleDescent_span s B hS hX hY hZ hP E' p'
    (fun f => hCart (liftedWalkingSpanEquiv.functor.map f))
    (fun i => hEtale (liftedWalkingSpanEquiv.functor.obj i))
    (fun i => hSep (liftedWalkingSpanEquiv.functor.obj i))
  let q' : E ⟶ (Functor.const LiftedWalkingSpan.{u}).obj U :=
    { app := fun i => q.app (liftedWalkingSpanDown.obj i)
      naturality := fun i j f => q.naturality (liftedWalkingSpanDown.map f) }
  exact ⟨U, v, q', hv, fun i => hq (liftedWalkingSpanDown.obj i)⟩

/-! ### Étale base change preserves the colimit -/

private noncomputable def isColimit_of_pointwise_pullback
    {J : Type*} [Category J] {C : Type*} [Category C]
    {D E E' : J ⥤ C} (c : Cocone D) (p : E ⟶ D) (p' : E' ⟶ D)
    {U : C} (v : U ⟶ c.pt)
    (q : E ⟶ (Functor.const J).obj U) (q' : E' ⟶ (Functor.const J).obj U)
    (h : ∀ i, IsPullback (p.app i) (q.app i) (c.ι.app i) v)
    (h' : ∀ i, IsPullback (p'.app i) (q'.app i) (c.ι.app i) v)
    (hc : IsColimit (Cocone.mk U q')) : IsColimit (Cocone.mk U q) := by
  let e : E ≅ E' := NatIso.ofComponents
    (fun i => (h i).isoIsPullback _ _ (h' i)) (by
      intro i j f
      apply (h' j).hom_ext
      · simp only [Category.assoc, IsPullback.isoIsPullback_hom_fst]
        rw [p'.naturality, ← Category.assoc, IsPullback.isoIsPullback_hom_fst, p.naturality]
      · simp only [Category.assoc, IsPullback.isoIsPullback_hom_snd]
        simp [q'.naturality])
  apply IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv e _).symm hc)
  refine Cocone.ext (Iso.refl _) (fun i => ?_)
  simp [e]

private noncomputable abbrev schemePushoutCocone : Cocone (span s.i s.j) :=
  PushoutCocone.mk (pushoutInl s) (pushoutInr s)
    (pushoutAlongClosedImmersionAndIntegral s).isPushout.w

/-- A cocone over the span whose legs are pullbacks of the pushout square along a separated étale
morphism is a colimit: by [Stacks Project, Tag 0ECL] its vertex is itself a pushout. -/
private noncomputable def isColimit_of_etale_isSeparated
    {E : WalkingSpan ⥤ Scheme.{u}} (c : Cocone E)
    (p : E ⟶ span s.i s.j) (v : c.pt ⟶ pushoutScheme s)
    [Etale v] [_root_.AlgebraicGeometry.IsSeparated v]
    (h : ∀ i, IsPullback (p.app i) (c.ι.app i) ((schemePushoutCocone s).ι.app i) v) :
    IsColimit c := by
  classical
  apply Classical.choice
  let W : etaleSchemesOver s :=
    ⟨Over.mk v, (show Etale v from inferInstance),
      (show _root_.AlgebraicGeometry.IsSeparated v from inferInstance),
      (locallyQuasiFinite_of_etale v).1, (locallyQuasiFinite_of_etale v).2⟩
  obtain ⟨F, hF, hobj, _⟩ := etaleTriple_pushout_equivalence s
  let := hF
  let d := (F.objPreimage W).1
  let t := inducedSituation s d
  let k : Over.mk (pushoutMap s d) ≅ Over.mk v :=
    (eqToIso (hobj (F.objPreimage W)).symm) ≪≫
      (ObjectProperty.ι _).mapIso (F.objObjPreimageIso W)
  let e : pushoutScheme t ≅ c.pt := (Over.forget _).mapIso k
  have he : e.hom ≫ v = pushoutMap s d := k.hom.w
  let c' : PushoutCocone d.i' d.j' :=
    PushoutCocone.mk (pushoutInl t ≫ e.hom) (pushoutInr t ≫ e.hom)
      (by
        simpa only [Category.assoc] using congrArg (fun a => a ≫ e.hom)
          (pushoutAlongClosedImmersionAndIntegral t).isPushout.w)
  have hc' : IsColimit c' := IsColimit.ofIsoColimit
    (pushoutAlongClosedImmersionAndIntegral t).isPushout.isColimit
    (PushoutCocone.ext e (by rfl) (by rfl))
  let p' : span d.i' d.j' ⟶ span s.i s.j :=
    spanHomMk d.h d.f d.g d.left_isPullback.w d.right_isPullback.w
  have hx : IsPullback d.f (pushoutInl t ≫ e.hom) (pushoutInl s) v := by
    apply (pushoutMap_left_isPullback s d).flip.of_iso
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    all_goals simp [he, t]
  have hy : IsPullback d.g (pushoutInr t ≫ e.hom) (pushoutInr s) v := by
    apply (pushoutMap_right_isPullback s d).flip.of_iso
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    all_goals simp [he, t]
  have h' : ∀ i, IsPullback (p'.app i) (c'.ι.app i)
      ((schemePushoutCocone s).ι.app i) v := by
    rintro (_ | (_ | _))
    · exact (d.left_isPullback.paste_horiz hx.flip).flip
    · exact hx
    · exact hy
  exact ⟨isColimit_of_pointwise_pullback (schemePushoutCocone s) p p' v c.ι c'.ι h h' hc'⟩

-- `CategoryTheory.Over.pullback`, which `AlgebraicGeometry.baseChangeCocone` is built from, is
-- tagged `implicit_reducible` in Mathlib, and that attribute is only honoured under
-- `backward.defeqAttrib.useBackward`; Mathlib's own
-- `Mathlib/CategoryTheory/Comma/Over/Pullback.lean` sets both options on every declaration that
-- unfolds it.  Without them the pulled-back diagram's objects are not recognised as fibre products
-- and no rewrite along a projection fires.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def isColimit_baseChange_of_etale_isSeparated
    {E : WalkingSpan ⥤ Scheme.{u}} (c : Cocone E)
    (p : E ⟶ span s.i s.j) (v : c.pt ⟶ pushoutScheme s)
    (h : ∀ i, IsPullback (p.app i) (c.ι.app i) ((schemePushoutCocone s).ι.app i) v)
    {V : Scheme.{u}} (f : V ⟶ c.pt) [Etale (f ≫ v)]
    [_root_.AlgebraicGeometry.IsSeparated (f ≫ v)] :
    IsColimit (baseChangeCocone c f) := by
  let E' := c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙
    Over.pullback f ⋙ Over.forget V
  let c' := baseChangeCocone c f
  let p' : E' ⟶ span s.i s.j :=
    { app := fun i => pullback.fst (c.ι.app i) f ≫ p.app i
      naturality := by
        intro i j g
        dsimp [E', Over.pullback]
        simp only [Category.assoc, pullback.lift_fst_assoc]
        rw [p.naturality] }
  let v' : c'.pt ⟶ pushoutScheme s := pullback.fst (𝟙 c.pt) f ≫ v
  have hv' : v' = pullback.snd (𝟙 c.pt) f ≫ (f ≫ v) := by
    dsimp [v']
    rw [← Category.assoc, ← pullback.condition]
    simp
  let : Etale v' := by rw [hv']; infer_instance
  let : _root_.AlgebraicGeometry.IsSeparated v' := by rw [hv']; infer_instance
  apply isColimit_of_etale_isSeparated s c' p' v'
  intro i
  have hsmall : IsPullback (pullback.fst (c.ι.app i) f) (c'.ι.app i)
      (c.ι.app i) (pullback.fst (𝟙 c.pt) f) := by
    apply IsPullback.flip
    apply IsPullback.of_right (h₁₂ := pullback.snd (𝟙 c.pt) f)
      (h₂₂ := 𝟙 c.pt) (v₁₃ := f)
    · simpa [c', baseChangeCocone, Over.pullback_map_left] using
        (IsPullback.of_hasPullback (c.ι.app i) f).flip
    · dsimp [c', baseChangeCocone]
      simp
    · exact (IsPullback.of_hasPullback (𝟙 c.pt) f).flip
  exact hsmall.paste_horiz (h i)

private noncomputable def isColimit_of_etale
    {E : WalkingSpan ⥤ Scheme.{u}} (c : Cocone E)
    (p : E ⟶ span s.i s.j) (v : c.pt ⟶ pushoutScheme s) [Etale v]
    (h : ∀ i, IsPullback (p.app i) (c.ι.app i) ((schemePushoutCocone s).ι.app i) v) :
    IsColimit c := by
  let C := c.pt.affineCover
  apply Classical.choice
  apply isColimit_of_fpqc c C.X C.f
    (Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ C.mem₀)
  · exact fun i => ⟨isColimit_baseChange_of_etale_isSeparated s c p v h (C.f i)⟩
  · intro i j
    let f := pullback.fst (C.f i) (C.f j)
    have : _root_.AlgebraicGeometry.IsSeparated ((f ≫ C.f i) ≫ v) := by
      rw [Category.assoc]
      infer_instance
    exact ⟨isColimit_baseChange_of_etale_isSeparated s c p v h (f ≫ C.f i)⟩

private noncomputable def isColimit_liftedPushoutCocone_of_etale
    (U : BigFppfOver B s.S hS)
    (v : U ⟶ (liftedPushoutCocone s B hS hX hY hZ hP).pt)
    (hv : Etale ((BigFppfOver.toScheme B s.S hS).map v))
    (E : LiftedWalkingSpan.{u} ⥤ BigFppfOver B s.S hS)
    (p : E ⟶ liftedPushoutDiagram s B hS hX hY hZ)
    (q : E ⟶ (Functor.const LiftedWalkingSpan.{u}).obj U)
    (h : ∀ i, IsPullback (p.app i) (q.app i)
      ((liftedPushoutCocone s B hS hX hY hZ hP).ι.app i) v) :
    IsColimit ((BigFppfOver.toScheme B s.S hS).mapCocone (Cocone.mk U q)) := by
  let Q := BigFppfOver.toScheme B s.S hS
  let : PreservesLimitsOfShape WalkingCospan Q := by apply comp_preservesLimitsOfShape
  let c := (Q.mapCocone (Cocone.mk U q)).whisker liftedWalkingSpanEquiv.functor
  have hn : ∀ {a b : WalkingSpan} (g : a ⟶ b),
      Q.map (E.map (liftedWalkingSpanEquiv.functor.map g)) ≫
          Q.map (p.app (liftedWalkingSpanEquiv.functor.obj b)) =
        Q.map (p.app (liftedWalkingSpanEquiv.functor.obj a)) ≫
          Q.map ((liftedPushoutDiagram s B hS hX hY hZ).map
            (liftedWalkingSpanEquiv.functor.map g)) := by
    intro a b g
    have hn := congrArg Q.map (p.naturality (liftedWalkingSpanEquiv.functor.map g))
    simp only [Q.map_comp] at hn
    convert hn using 1
  let p' : (liftedWalkingSpanEquiv.functor ⋙ (E ⋙ Q)) ⟶ span s.i s.j :=
    spanHomMk (Q.map (p.app (ULift.up WalkingSpan.zero)))
      (Q.map (p.app (ULift.up WalkingSpan.left)))
      (Q.map (p.app (ULift.up WalkingSpan.right))) (hn WalkingSpan.Hom.fst)
      (hn WalkingSpan.Hom.snd)
  apply IsColimit.ofWhiskerEquivalence liftedWalkingSpanEquiv
  refine @isColimit_of_etale s _ c p' (Q.map v) hv ?_
  rintro (_ | (_ | _))
  · exact (h (ULift.up WalkingSpan.zero)).map Q
  · exact (h (ULift.up WalkingSpan.left)).map Q
  · exact (h (ULift.up WalkingSpan.right)).map Q

/-! ### The universal property -/

private theorem existsUnique_algebraicSpace_desc
    (F : (BigFppfOver B s.S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B s.S hS F)
    (a : yoneda.obj (fppfOverX s B hS hX) ⟶ F)
    (b : yoneda.obj (fppfOverY s B hS hY) ⟶ F)
    (hab : yoneda.map (fppfOverI s B hS hX hZ) ≫ a =
      yoneda.map (fppfOverJ s B hS hY hZ) ≫ b) :
    ∃! f : yoneda.obj (fppfOverPushout s B hS hP) ⟶ F,
      yoneda.map (fppfOverInl s B hS hX hP) ≫ f = a ∧
        yoneda.map (fppfOverInr s B hS hY hP) ≫ f = b := by
  let cA := PushoutCocone.mk a b hab
  let cP := (Cocone.precompose
    (spanCompIso yoneda (fppfOverI s B hS hX hZ) (fppfOverJ s B hS hY hZ)).hom).obj cA
  obtain ⟨f, hf, hu⟩ := isColimit_algebraicSpaces_of_scheme B s.S hS
    (liftedPushoutDiagram s B hS hX hY hZ) (liftedPushoutCocone s B hS hX hY hZ hP)
    (liftedPushoutCocone_isColimit s B hS hX hY hZ hP)
    (liftedPushoutCocone_covers s B hS hX hY hZ hP)
    (isColimit_liftedPushoutCocone_of_etale s B hS hX hY hZ hP)
    (exists_etaleDescent s B hS hX hY hZ hP)
    F hF (fun i => cP.ι.app (liftedWalkingSpanDown.obj i))
    (fun g => cP.w (liftedWalkingSpanDown.map g))
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · have h := hf (ULift.up WalkingSpan.left)
    change yoneda.map (fppfOverInl s B hS hX hP) ≫ f = (𝟙 _) ≫ a at h
    simpa only [Category.id_comp] using h
  · have h := hf (ULift.up WalkingSpan.right)
    change yoneda.map (fppfOverInr s B hS hY hP) ≫ f = (𝟙 _) ≫ b at h
    simpa only [Category.id_comp] using h
  · intro g hg
    apply hu g
    rintro ⟨(_ | (_ | _))⟩
    · show yoneda.map (fppfOverI s B hS hX hZ ≫ fppfOverInl s B hS hX hP) ≫ g =
        (𝟙 _) ≫ (yoneda.map (fppfOverI s B hS hX hZ) ≫ a)
      rw [yoneda.map_comp, Category.assoc, hg.1, Category.id_comp]
    · show yoneda.map (fppfOverInl s B hS hX hP) ≫ g = (𝟙 _) ≫ a
      simpa only [Category.id_comp] using hg.1
    · show yoneda.map (fppfOverInr s B hS hY hP) ≫ g = (𝟙 _) ≫ b
      simpa only [Category.id_comp] using hg.2

/-- **Stacks 0EDP.** In the standing situation of [Stacks Project, Tag 0ECI], the scheme pushout
`Y ⨿_Z X` of [Stacks Project, Tag 0E25] is also a pushout in the category of algebraic spaces
over `S`: the square formed by the four schemes and the four canonical morphisms, regarded
through the Yoneda embedding as a square of algebraic spaces over `S`, is a pushout square. -/
@[stacks 0EDP]
theorem pushout_isPushout_algebraicSpaces :
    IsPushout
      (ObjectProperty.homMk (yoneda.map (fppfOverI s B hS hX hZ)) :
        (⟨yoneda.obj (fppfOverZ s B hS hZ),
          isAlgebraicSpace_yoneda B s.S hS (fppfOverZ s B hS hZ)⟩ :
          AlgebraicSpaces B s.S hS) ⟶
        (⟨yoneda.obj (fppfOverX s B hS hX),
          isAlgebraicSpace_yoneda B s.S hS (fppfOverX s B hS hX)⟩ :
          AlgebraicSpaces B s.S hS))
      (ObjectProperty.homMk (yoneda.map (fppfOverJ s B hS hY hZ)) :
        (⟨yoneda.obj (fppfOverZ s B hS hZ),
          isAlgebraicSpace_yoneda B s.S hS (fppfOverZ s B hS hZ)⟩ :
          AlgebraicSpaces B s.S hS) ⟶
        (⟨yoneda.obj (fppfOverY s B hS hY),
          isAlgebraicSpace_yoneda B s.S hS (fppfOverY s B hS hY)⟩ :
          AlgebraicSpaces B s.S hS))
      (ObjectProperty.homMk (yoneda.map (fppfOverInl s B hS hX hP)) :
        (⟨yoneda.obj (fppfOverX s B hS hX),
          isAlgebraicSpace_yoneda B s.S hS (fppfOverX s B hS hX)⟩ :
          AlgebraicSpaces B s.S hS) ⟶
        (⟨yoneda.obj (fppfOverPushout s B hS hP),
          isAlgebraicSpace_yoneda B s.S hS (fppfOverPushout s B hS hP)⟩ :
          AlgebraicSpaces B s.S hS))
      (ObjectProperty.homMk (yoneda.map (fppfOverInr s B hS hY hP)) :
        (⟨yoneda.obj (fppfOverY s B hS hY),
          isAlgebraicSpace_yoneda B s.S hS (fppfOverY s B hS hY)⟩ :
          AlgebraicSpaces B s.S hS) ⟶
        (⟨yoneda.obj (fppfOverPushout s B hS hP),
          isAlgebraicSpace_yoneda B s.S hS (fppfOverPushout s B hS hP)⟩ :
          AlgebraicSpaces B s.S hS)) := by
  classical
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk ?_ (fun t => ?_) ?_ ?_ ?_)
  · apply ObjectProperty.hom_ext
    show yoneda.map (fppfOverI s B hS hX hZ) ≫ yoneda.map (fppfOverInl s B hS hX hP) =
      yoneda.map (fppfOverJ s B hS hY hZ) ≫ yoneda.map (fppfOverInr s B hS hY hP)
    rw [← yoneda.map_comp, ← yoneda.map_comp]
    congr 1
    ext
    exact (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
  · exact ObjectProperty.homMk (existsUnique_algebraicSpace_desc s B hS hX hY hZ hP
      t.pt.obj t.pt.property t.inl.hom t.inr.hom
      (congrArg (fun f => f.hom) t.condition)).choose
  · intro t
    apply ObjectProperty.hom_ext
    exact (existsUnique_algebraicSpace_desc s B hS hX hY hZ hP
      t.pt.obj t.pt.property t.inl.hom t.inr.hom
      (congrArg (fun f => f.hom) t.condition)).choose_spec.1.1
  · intro t
    apply ObjectProperty.hom_ext
    exact (existsUnique_algebraicSpace_desc s B hS hX hY hZ hP
      t.pt.obj t.pt.property t.inl.hom t.inr.hom
      (congrArg (fun f => f.hom) t.condition)).choose_spec.1.2
  · intro t m h₁ h₂
    apply ObjectProperty.hom_ext
    exact (existsUnique_algebraicSpace_desc s B hS hX hY hZ hP
      t.pt.obj t.pt.property t.inl.hom t.inr.hom
      (congrArg (fun f => f.hom) t.condition)).choose_spec.2 m.hom
      ⟨congrArg (fun f => f.hom) h₁, congrArg (fun f => f.hom) h₂⟩

end AlgebraicGeometry.Space

end
