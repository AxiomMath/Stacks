module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.OfIsSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# Openness of versality for Artin's contraction functor at a point of `Z`

In the situation of Stacks 0GH8 let `F` be Artin's contraction functor of Stacks 0GHA and
`ξ = (Z, u', x̂) ∈ F(V)`. This file proves the second case of the proof of Stacks 0GIA, from the
output of Lemma 0GI9 in the form in which it is used: if `x̂` is formally smooth over an open
neighbourhood `O` of a point `v₀ ∈ Z`, then `ξ` is versal at every finite type point of an open
neighbourhood of `v₀`.

The source's argument is followed. Points of `Z ∩ O` are handled by the formal smoothness of `x̂`.
For a compatibility witness `V' ⟶ V`, `x̂'`, `x'`, the morphism `x'` is smooth at every point of
`V'` over `Z ∩ O` (Stacks 0APN); the set `B ⊆ |V'|` where `x'` is not smooth is closed, so its
image in `|V|` under the proper morphism `V' ⟶ V` is a closed set missing `Z ∩ O`, and on the
complement of that image `ξ` is versal at the points outside `Z` too, `u'` being `x'` there.

## Main results

* `AlgebraicGeometry.Space.isClosedMap_pointsMap_of_universallyClosed`: a universally closed
  morphism of algebraic spaces is closed on points.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_isVersalAt_of_mem_of_formallySmooth`: the
  second case of the proof of Stacks 0GIA.

## References

* [Stacks Project, Tag 0APN](https://stacks.math.columbia.edu/tag/0APN)
* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
* [Stacks Project, Tag 0GIA](https://stacks.math.columbia.edu/tag/0GIA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- A universally closed morphism of algebraic spaces is closed on points: its base change along
the identity is closed, and differs from it by an isomorphism of the source. -/
theorem isClosedMap_pointsMap_of_universallyClosed {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : UniversallyClosed B S hS f) :
    IsClosedMap (pointsMap B S hS F f) := by
  have hc : IsClosedMap (pointsMap B S hS _ (pullback.fst (𝟙 G) f)) := hf G hG (𝟙 G)
  have hfst : pullback.fst (𝟙 G) f = pullback.snd (𝟙 G) f ≫ f := by
    rw [← pullback.condition, Category.comp_id]
  let e := asIso (pullback.snd (𝟙 G) f)
  intro C hC
  have himg : pointsMap B S hS F f '' C =
      pointsMap B S hS _ (pullback.fst (𝟙 G) f) '' (pointsMap B S hS _ e.hom ⁻¹' C) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨pointsMap B S hS _ e.inv a, ?_, ?_⟩
      · change pointsMap B S hS _ e.hom (pointsMap B S hS _ e.inv a) ∈ C
        rwa [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id]
      · rw [hfst, ← pointsMap_comp_apply]
        change pointsMap B S hS _ (e.inv ≫ e.hom ≫ f) a = _
        rw [e.inv_hom_id_assoc]
    · rintro ⟨b, hb, rfl⟩
      refine ⟨pointsMap B S hS _ e.hom b, hb, ?_⟩
      rw [hfst, pointsMap_comp_apply]
      rfl
  rw [himg]
  exact hc _ (hC.preimage (continuous_pointsMap B S hS e.hom))

end Space

namespace Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

attribute [local instance] Space.pointTopology

/-- **Lifting of `u'` from smoothness of the witness.** Let `V' ⟶ V`, `x̂'`, `x'` witness the
compatibility of `ξ = (Z, u', x̂)` and let `v` be a point of `V` such that `x'` is smooth at every
point of `V'` over `v`. Then sections of `V ∖ Z` over a one-point affine object all of whose
points go to `v` extend along closed immersions with nilpotent kernel over every prescribed
section of `U'`: over `V ∖ Z` the morphism `V' ⟶ V` is an isomorphism and `u' = x'`, so the
problem is one for the smooth, hence formally smooth, restriction of `x'` to an open subspace. -/
theorem CompatibilityWitness.lift_openPart_of_isSmoothAt {V : BigFppfOver B S hS}
    {t : Triple c V} (w : CompatibilityWitness c V t.Z t.u t.xhat)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hsm : ∀ y : Space.points B S hS w.V',
      Space.pointsToScheme B S hS V (Space.pointsMap B S hS w.V' w.p y) = v →
        Space.IsSmoothAt B S hS w.x' y)
    (T₀ T₁ : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T₁)]
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj T₀)]
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj T₁)]
    (t₀ : (BigFppfOver.toScheme B S hS).obj T₀) (i : T₀ ⟶ T₁)
    (hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hnil : IsNilpotent (RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom))
    (φ : T₀ ⟶ V)
    (hφ : φ ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).obj (op T₀))
    (hφv : ∀ t', (BigFppfOver.toScheme B S hS).map φ t' = v)
    (s : c.U'.toFunctor.obj (op T₁)) (hs : c.U'.toFunctor.map i.op s = t.u.app (op T₀) ⟨φ, hφ⟩) :
    ∃ (φ' : T₁ ⟶ V)
      (hφ' : φ' ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).obj (op T₁)),
      i ≫ φ' = φ ∧ t.u.app (op T₁) ⟨φ', hφ'⟩ = s := by
  let α₀ := w.j.app (op T₀) ⟨φ, hφ⟩
  have hjp : ∀ (T : BigFppfOver B S hS) (e), w.p.app (op T) (w.j.app (op T) e) = e.1 :=
    fun T e => (congrArg (fun m => m.app (op T) e) w.isPullback_j.w).symm
  have hux : ∀ (T : BigFppfOver B S hS) (e), w.x'.app (op T) (w.j.app (op T) e) =
      (t.u.app (op T) e).1 :=
    fun T e => congrArg (fun m => m.app (op T) e) w.restrict_x'
  have hpα : w.p.app (op T₀) α₀ = φ := hjp T₀ _
  let pt₀ := (Space.pointsEquivScheme B S hS T₀).symm t₀
  let y := Space.pointsMap B S hS _ (yonedaEquiv.symm α₀) pt₀
  have hpy : Space.pointsToScheme B S hS V (Space.pointsMap B S hS w.V' w.p y) = v := by
    have h1 : yonedaEquiv.symm α₀ ≫ w.p = yoneda.map φ := by
      rw [yonedaEquiv_symm_naturality_right, hpα]
      ext; rfl
    change Space.pointsToScheme B S hS V (Space.pointsMap B S hS w.V' w.p
      (Space.pointsMap B S hS _ (yonedaEquiv.symm α₀) pt₀)) = v
    rw [← Space.pointsMap_comp_apply, h1, Space.pointsToScheme_pointsMap_yoneda]
    rw [show Space.pointsToScheme B S hS T₀ pt₀ = t₀ from
      (Space.pointsEquivScheme B S hS T₀).apply_symm_apply t₀]
    exact hφv t₀
  obtain ⟨U, hU, hUsm, hyU⟩ := (hsm y hpy).exists_mem_range_pointsMap
  have hFS := Space.formallySmooth_of_isSmooth' hU.1 c.isAlgebraicSpace_X' hUsm
  have hmem : α₀ ∈ U.obj (op T₀) := by
    have hle : Space.openSubspaceOfPoints B S hS w.V'
        (Set.range (Space.pointsMap B S hS U.toFunctor U.ι)) ≤ U :=
      Space.le_of_range_pointsMap_ι_subset B S hS hU
        (Space.range_pointsMap_ι_openSubspaceOfPoints B S hS _).subset
    refine hle _ ?_
    rw [Space.mem_openSubspaceOfPoints_iff]
    rintro _ ⟨q, rfl⟩
    obtain rfl : q = pt₀ := (Space.pointsEquivScheme B S hS T₀).injective (Subsingleton.elim _ _)
    exact hyU
  have hxy : (U.ι ≫ w.x').app (op T₀) ⟨α₀, hmem⟩ = c.X'.map i.op s.1 := by
    change w.x'.app (op T₀) α₀ = (c.U'.toFunctor.map i.op s).1
    rw [hs]
    exact hux T₀ _
  obtain ⟨z, hz₁, hz₂⟩ := Space.FormallySmooth.exists_isLift_of_isNilpotent hFS i hci hnil
    ⟨α₀, hmem⟩ s.1 hxy
  have hz₁' : w.V'.map i.op z.1 = α₀ := congrArg Subtype.val hz₁
  let φ' := w.p.app (op T₁) z.1
  have hcomp : i ≫ φ' = φ := by
    have := NatTrans.naturality_apply w.p i.op z.1
    rw [hz₁', hpα] at this
    exact this.symm
  have hφ' : φ' ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).obj (op T₁) := by
    refine (Space.mem_openSubspaceOfPoints_iff_of_subsingleton φ'
      ((BigFppfOver.toScheme B S hS).map i t₀) _).2 ?_
    have h1 : (BigFppfOver.toScheme B S hS).map φ' ((BigFppfOver.toScheme B S hS).map i t₀) =
        (BigFppfOver.toScheme B S hS).map φ t₀ := by
      rw [← hcomp, Functor.map_comp, Scheme.Hom.comp_apply]
    rw [h1]
    exact (Space.mem_openSubspaceOfPoints_iff_of_subsingleton φ t₀ _).1 hφ
  obtain ⟨a, ha₁, ha₂⟩ := Types.exists_of_isPullback
    (w.isPullback_j.map ((evaluation _ (Type u)).obj (op T₁)))
    (⟨φ', hφ'⟩ : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).toFunctor.obj (op T₁))
    z.1 rfl
  obtain rfl : a = ⟨φ', hφ'⟩ := ha₁
  exact ⟨φ', hφ', hcomp,
    Subtype.ext ((hux T₁ _).symm.trans ((congrArg (w.x'.app (op T₁)) ha₂).trans hz₂))⟩

/-- **Stacks 0GIA, second case of the proof.** Let `ξ = (Z, u', x̂) ∈ F(V)` with `V` locally of
finite type over `S`, and let `v₀ ∈ Z` lie in the image of an open immersion `V₀ ⟶ V` over which
`x̂` is formally smooth, that is, such that the restriction `V₀_{/Z₀} ⟶ V_{/Z} ⟶ W` of `x̂` is
formally smooth (the output of Lemma 0GI9). Then there is an open neighbourhood of `v₀` at every
finite type point of which `ξ` is versal.

At points of `Z ∩ O` versality is the formal smoothness of `x̂`. For a compatibility witness
`V' ⟶ V`, `x̂'`, `x'`, the morphism `x'` is smooth at the points of `V'` over `Z ∩ O`; the image in
`|V|` of the closed set of points where `x'` is not smooth is closed, the morphism `V' ⟶ V` being
proper, and it misses `Z ∩ O`. Off that image and off `Z`, `ξ` is the point `u' = x'` of `X'`,
which lifts by smoothness of `x'`. -/
theorem exists_isVersalAt_of_mem_of_formallySmooth (x : (contractionFunctor c).Elementsᵒᵖ)
    (hU : LocallyOfFiniteType
      ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x).hom)
    (v₀ : ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x).left)
    (hZ : (Space.pointsEquivScheme B S hS x.unop.1.unop.obj).symm v₀ ∈
      (x.unop.2 : Triple c x.unop.1.unop.obj).Z)
    (V₀ : BigFppfOver B S hS) (ι₀ : V₀ ⟶ x.unop.1.unop.obj)
    (hι₀ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι₀))
    (hv₀O : v₀ ∈ Set.range ((BigFppfOver.toScheme B S hS).map ι₀))
    (hFS : Space.FormallySmooth (Space.completionSheafMap B S hS (yoneda.map ι₀)
        (x.unop.2 : Triple c x.unop.1.unop.obj).Z ≫
      (x.unop.2 : Triple c x.unop.1.unop.obj).xhat).hom) :
    ∃ W : ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x).left.Opens,
      v₀ ∈ W ∧ ∀ v ∈ W, IsFiniteTypePoint v →
        Deformation.Artin.IsVersalAt
          ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x)
          (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) v x rfl := by
  let V := x.unop.1.unop.obj
  let ξ : Triple c V := x.unop.2
  let O : Set V.left.obj := Set.range ((BigFppfOver.toScheme B S hS).map ι₀)
  have hO : IsOpen O := hι₀.base_open.isOpen_range
  have hliftZ := FormalSpace.lift_of_formallySmooth_of_isOpenImmersion ξ.Z ξ.xhat ι₀ hι₀ hFS
  obtain ⟨w⟩ := ξ.compatible
  -- the smooth locus of `x'`
  let Ω : Set (Space.points B S hS w.V') := {y | Space.IsSmoothAt B S hS w.x' y}
  have hΩ : IsOpen Ω := by
    refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
    obtain ⟨U, hU, hsm, hyU⟩ := Space.IsSmoothAt.exists_mem_range_pointsMap B S hS hy
    refine ⟨Set.range (Space.pointsMap B S hS U.toFunctor U.ι), ?_,
      Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2, hyU⟩
    rintro _ ⟨y', rfl⟩
    exact Space.isSmoothAt_of_isOpenSubspace B S hS U hU hsm y'
  let C := Space.pointsMap B S hS w.V' w.p '' Ωᶜ
  have hC : IsClosed C := Space.isClosedMap_pointsMap_of_universallyClosed
    (isAlgebraicSpace_yoneda B S hS V) w.p w.isProper_p.2.2 _ hΩ.isClosed_compl
  let Cs := Space.pointsToScheme B S hS V '' C
  have hCs : IsClosed Cs := (Space.isClosed_pointTopology_yoneda_iff_isClosed_image B S hS V C).1 hC
  have hsmZ : ∀ y : Space.points B S hS w.V', Space.pointsMap B S hS w.V' w.p y ∈ ξ.Z →
      Space.pointsToScheme B S hS V (Space.pointsMap B S hS w.V' w.p y) ∈
        (O : Set V.left.obj) → y ∈ Ω :=
    w.isSmoothAt_x' c hU O hliftZ
  refine ⟨⟨O ∩ Csᶜ, hO.inter hCs.isOpen_compl⟩, ⟨hv₀O, ?_⟩, ?_⟩
  · rintro ⟨_, ⟨y, hyΩ, rfl⟩, hy⟩
    refine hyΩ (hsmZ y ?_ (hy ▸ hv₀O))
    rwa [(Space.pointsEquivScheme B S hS V).eq_symm_apply.2 hy]
  · rintro v ⟨hvO, hvC⟩ -
    by_cases hvZ : (Space.pointsEquivScheme B S hS V).symm v ∈ ξ.Z
    · exact (isVersalAt_iff_isVersalAtCompletion c x v hvZ).2
        (FormalSpace.isVersalAtCompletion_of_lift ξ.Z ξ.xhat O v hvO
          fun T₀ T₁ _ i hci hnil φ hφ hrange w' hw' =>
            hliftZ T₀ T₁ i hci hnil φ hφ hrange w' hw')
    · refine isVersalAt_of_lift_openPart c x v hvZ ?_
      intro T₀ T₁ _ _ _ t₀ i hci hnil φ hφ hφv s hs
      refine w.lift_openPart_of_isSmoothAt c v (fun y hy => ?_) T₀ T₁ t₀ i hci hnil φ hφ hφv s hs
      by_contra hyΩ
      exact hvC ⟨_, ⟨y, hyΩ, rfl⟩, hy⟩

end Artin.ContractionSituation

end AlgebraicGeometry

end
