module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversalHomeomorphism

/-!
# Universal homeomorphisms among representable morphisms of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Two notions of universal homeomorphism are available for
such an `f`: the one obtained by testing universal homeomorphy of scheme morphisms on all of its
represented base changes, and the one of Stacks 05Z5, that every base change of it by an
algebraic space over `S` induces a homeomorphism on the spaces of points. This file shows that
the two agree.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_of_bounded_isHomeomorph_baseChanges`: a homeomorphism
  of schemes inside the site whose base changes along schemes inside the site are homeomorphisms
  is a universal homeomorphism.
* `AlgebraicGeometry.Space.isHomeomorph_pointsMap_yonedaMap_iff`: a morphism of the site is a
  homeomorphism on the points of the represented presheaves exactly when the underlying morphism
  of schemes is a homeomorphism.
* `AlgebraicGeometry.Space.presheaf_universalHomeomorphism_of_universalHomeomorphism`: the
  implication from the point-set condition.
* `AlgebraicGeometry.Space.universalHomeomorphism_of_presheaf_universalHomeomorphism`: the
  converse.
* `AlgebraicGeometry.Space.presheaf_universalHomeomorphism_iff`: the two notions agree.

## References

* [Stacks Project, Tag 05Z4](https://stacks.math.columbia.edu/tag/05Z4)
* [Stacks Project, Tag 05Z5](https://stacks.math.columbia.edu/tag/05Z5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The underlying map of an isomorphism of schemes is a homeomorphism. -/
theorem isHomeomorph_of_isIso {X Y : Scheme.{u}} (i : X ⟶ Y) [IsIso i] :
    IsHomeomorph i := by
  simpa [Scheme.coe_homeoOfIso] using (Scheme.homeoOfIso (asIso i)).isHomeomorph

/-- Precomposing a homeomorphism of schemes with an isomorphism gives a homeomorphism. -/
private theorem isHomeomorph_of_isIso_comp {X Y Z : Scheme.{u}} (i : X ⟶ Y) [IsIso i] {f : Y ⟶ Z}
    (hf : IsHomeomorph f) : IsHomeomorph (i ≫ f) :=
  hf.comp (isHomeomorph_of_isIso i)

/-- A universal homeomorphism of schemes is universally closed. -/
theorem UniversalHomeomorphism.universallyClosed {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : UniversalHomeomorphism f) : UniversallyClosed f :=
  ⟨fun _ _ _ _ _ H ↦ (hf.universally_isHomeomorph _ _ _ H).isClosedMap⟩

/-- A homeomorphism of schemes inside a big fppf site is a universal homeomorphism as soon as its
base changes along morphisms from schemes inside that site are homeomorphisms. -/
theorem universalHomeomorphism_of_bounded_isHomeomorph_baseChanges
    (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : B.Contains X) (hY : B.Contains Y) (hself : IsHomeomorph f)
    (hbase : ∀ (Z : Scheme.{u}) (_ : B.Contains Z) (g : Z ⟶ Y),
      IsHomeomorph (pullback.snd f g)) : UniversalHomeomorphism f := by
  have huc : UniversallyClosed f :=
    universallyClosed_of_bounded_closed_baseChanges B f hX hY
      fun Z hZ g ↦ (hbase Z hZ g).isClosedMap
  have hui : UniversallyInjective f := by
    refine (UniversallyInjective.iff_diagonal f).mpr
      ⟨fun z ↦ ⟨pullback.snd f f z, (hbase X hX f).bijective.1 ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]
    rfl
  have hsurj : Surjective f := ⟨hself.bijective.2⟩
  refine ⟨fun _ _ _ _ f' H ↦ ?_⟩
  have : Surjective f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback H.flip inferInstance
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨Scheme.Hom.continuous _, UniversallyClosed.universally_isClosedMap _ _ _ H,
      ⟨UniversallyInjective.universally_injective _ _ _ H, f'.surjective⟩⟩

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Homeomorphy on the points of represented presheaves -/

/-- A morphism of the big fppf site over `S` is a homeomorphism on the points of the represented
presheaves exactly when the underlying morphism of schemes is a homeomorphism. -/
theorem isHomeomorph_pointsMap_yonedaMap_iff {U V : BigFppfOver B S hS} (f : U ⟶ V) :
    IsHomeomorph (pointsMap B S hS (yoneda.obj U) (yoneda.map f)) ↔
      IsHomeomorph ((BigFppfOver.toScheme B S hS).map f) := by
  let eU := schemePointsHomeomorph B S hS U
  let eV := schemePointsHomeomorph B S hS V
  have hnat : ∀ x, eV (pointsMap B S hS (yoneda.obj U) (yoneda.map f) x) =
      (BigFppfOver.toScheme B S hS).map f (eU x) := fun x ↦
    pointsToScheme_pointsMap B S hS f x
  have hscheme : ⇑((BigFppfOver.toScheme B S hS).map f) =
      eV ∘ pointsMap B S hS (yoneda.obj U) (yoneda.map f) ∘ eU.symm := by
    funext y
    rw [Function.comp_apply, Function.comp_apply, hnat (eU.symm y),
      Homeomorph.apply_symm_apply]
  have hpoints : pointsMap B S hS (yoneda.obj U) (yoneda.map f) =
      eV.symm ∘ ⇑((BigFppfOver.toScheme B S hS).map f) ∘ eU := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, ← hnat x, Homeomorph.symm_apply_apply]
  exact ⟨fun h ↦ hscheme ▸ (eV.isHomeomorph.comp h).comp eU.symm.isHomeomorph,
    fun h ↦ hpoints ▸ (eV.symm.isHomeomorph.comp h).comp eU.isHomeomorph⟩

/-- Precomposing a map that is a homeomorphism on points with an isomorphism of presheaves gives a
map that is a homeomorphism on points. -/
private theorem isHomeomorph_pointsMap_iso_hom_comp {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : P ≅ Q) {k : Q ⟶ R} (hk : IsHomeomorph (pointsMap B S hS Q k)) :
    IsHomeomorph (pointsMap B S hS P (e.hom ≫ k)) := by
  rw [pointsMap_comp]
  exact hk.comp (pointsHomeomorphOfIso B S hS e).isHomeomorph

/-- Homeomorphy on the points of the presheaf fibre product `h_U ×_Y X` gives homeomorphy of the
morphism of schemes representing that base change. -/
theorem isHomeomorph_map_relativelyRepresentable_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) {U : BigFppfOver B S hS}
    (g : yoneda.obj U ⟶ Y)
    (hhomeo : IsHomeomorph (pointsMap B S hS (pullback g f) (pullback.fst g f))) :
    IsHomeomorph ((BigFppfOver.toScheme B S hS).map (hf.snd g)) := by
  let e : yoneda.obj (hf.pullback g) ≅ pullback g f :=
    (hf.isPullback g).isoPullback ≪≫ pullbackSymmetry f g
  have he : e.hom ≫ pullback.fst g f = yoneda.map (hf.snd g) := by
    simp only [e, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
      IsPullback.isoPullback_hom_snd]
  refine (isHomeomorph_pointsMap_yonedaMap_iff B S hS (hf.snd g)).1 ?_
  rw [← he]
  exact isHomeomorph_pointsMap_iso_hom_comp B S hS e hhomeo

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### From the point-set condition -/

/-- If every base change of a representable morphism `f` of presheaves by an algebraic space over
`S` is a homeomorphism on points, then every represented base change of `f` is a universal
homeomorphism of schemes. -/
theorem presheaf_universalHomeomorphism_of_universalHomeomorphism {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : UniversalHomeomorphism B S hS f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  refine ⟨hf, fun U V g fst snd sq ↦ ?_⟩
  let T := BigFppfOver.toScheme B S hS
  have hrepresented : ∀ (W : BigFppfOver B S hS) (k : yoneda.obj W ⟶ Y),
      IsHomeomorph (T.map (hf.snd k)) := fun W k ↦
    isHomeomorph_map_relativelyRepresentable_snd B S hS hf k
      (h (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) k)
  have hcan : IsPullback (hf.fst g) (yoneda.map (hf.snd g)) f g := hf.isPullback g
  let e : hf.pullback g ≅ V := yoneda.preimageIso (hcan.isoIsPullback _ _ sq)
  have he : e.hom ≫ snd = hf.snd g := by
    apply yoneda.map_injective
    simp [e, hcan.isoIsPullback_hom_snd _ _ sq]
  have hfactor : T.map e.inv ≫ T.map (hf.snd g) = T.map snd := by
    rw [← T.map_comp, ← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hhomeo : IsHomeomorph (T.map snd) := by
    rw [← hfactor]
    exact isHomeomorph_of_isIso_comp _ (hrepresented U g)
  have hhomeoBounded : ∀ (W : Scheme.{u}) (_ : B.Contains W) (k : W ⟶ T.obj U),
      IsHomeomorph (pullback.snd (T.map snd) k) := by
    intro W hW k
    let k' : B.inclusion.obj (B.obj hW) ⟶ B.inclusion.obj U.left := k
    let kSite : B.obj hW ⟶ U.left := B.inclusion.preimage k'
    let Wov : BigFppfOver B S hS := Over.mk (kSite ≫ U.hom)
    let kOver : Wov ⟶ U := Over.homMk kSite
    have hk : T.map kOver = k := B.inclusion.map_preimage k'
    rw [← hk]
    let lNat : yoneda.obj (hf.pullback (yoneda.map kOver ≫ g)) ⟶ yoneda.obj V :=
      sq.lift (hf.fst (yoneda.map kOver ≫ g))
        (yoneda.map (hf.snd (yoneda.map kOver ≫ g)) ≫ yoneda.map kOver)
        (by simpa [Category.assoc] using (hf.isPullback (yoneda.map kOver ≫ g)).w)
    have hpaste : IsPullback (lNat ≫ fst)
        (yoneda.map (hf.snd (yoneda.map kOver ≫ g))) f (yoneda.map kOver ≫ g) := by
      rw [show lNat ≫ fst = hf.fst (yoneda.map kOver ≫ g) from by simp [lNat]]
      exact hf.isPullback (yoneda.map kOver ≫ g)
    have hpbNat : IsPullback lNat (yoneda.map (hf.snd (yoneda.map kOver ≫ g)))
        (yoneda.map snd) (yoneda.map kOver) :=
      (IsPullback.paste_horiz_iff sq (by simp [lNat])).mp hpaste
    have hpbOver : IsPullback (yoneda.preimage lNat)
        (hf.snd (yoneda.map kOver ≫ g)) snd kOver := by
      apply IsPullback.of_map_of_faithful (F := yoneda)
      simpa using hpbNat
    have hpbScheme : IsPullback (T.map (yoneda.preimage lNat))
        (T.map (hf.snd (yoneda.map kOver ≫ g))) (T.map snd) (T.map kOver) := hpbOver.map T
    let eScheme := hpbScheme.isoIsPullback _ _
      (IsPullback.of_hasPullback (T.map snd) (T.map kOver))
    have heScheme : eScheme.inv ≫ T.map (hf.snd (yoneda.map kOver ≫ g)) =
        pullback.snd (T.map snd) (T.map kOver) :=
      hpbScheme.isoIsPullback_inv_snd _ _
        (IsPullback.of_hasPullback (T.map snd) (T.map kOver))
    rw [← heScheme]
    exact isHomeomorph_of_isIso_comp _ (hrepresented Wov (yoneda.map kOver ≫ g))
  exact universalHomeomorphism_of_bounded_isHomeomorph_baseChanges B (T.map snd)
    V.left.property U.left.property hhomeo hhomeoBounded

/-! ### To the point-set condition -/

/-- If every represented base change
of a representable morphism of algebraic spaces over `S` is a universal homeomorphism of schemes,
then every base change of it by an algebraic space over `S` is a homeomorphism on points. -/
theorem universalHomeomorphism_of_presheaf_universalHomeomorphism
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    UniversalHomeomorphism B S hS f := by
  intro Z hZ g
  let T := BigFppfOver.toScheme B S hS
  have hclosedProp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
    MorphismProperty.relative_monotone (F := yoneda)
      (fun _ _ k hk ↦ AlgebraicGeometry.UniversalHomeomorphism.universallyClosed
        (T.map k) hk) _ h
  have hclosed : IsClosedMap (pointsMap B S hS (pullback g f) (pullback.fst g f)) :=
    universallyClosed_of_presheaf_universallyClosed B S hS hX hY hf hclosedProp Z hZ g
  obtain ⟨U, a, haSurj, haEtale⟩ := hZ.exists_atlas
  have hC : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f hZ hX hY
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hD : IsAlgebraicSpace B S hS (pullback a (pullback.fst g f)) :=
    isAlgebraicSpace_pullback B S hS a (pullback.fst g f) hU hC hZ
  have sqD : IsPullback (pullback.fst a (pullback.fst g f))
      (pullback.snd a (pullback.fst g f)) a (pullback.fst g f) := IsPullback.of_hasPullback _ _
  have hAtlasSurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (surjective_iff_surjective_pointsMap B S hS Z hZ U a).mp haSurj
  have hcart : ∀ (c : points B S hS (pullback g f)) (z : points B S hS (yoneda.obj U)),
      pointsMap B S hS (pullback g f) (pullback.fst g f) c =
        pointsMap B S hS (yoneda.obj U) a z →
      ∃ d : points B S hS (pullback a (pullback.fst g f)),
        pointsMap B S hS _ (pullback.snd a (pullback.fst g f)) d = c ∧
          pointsMap B S hS _ (pullback.fst a (pullback.fst g f)) d = z := by
    intro c z hcz
    have sq' : IsPullback
        (ObjectProperty.homMk (pullback.fst a (pullback.fst g f)) :
          (⟨_, hD⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hU⟩)
        (ObjectProperty.homMk (pullback.snd a (pullback.fst g f)) :
          (⟨_, hD⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hC⟩)
        (ObjectProperty.homMk a : (⟨_, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
        (ObjectProperty.homMk (pullback.fst g f) :
          (⟨_, hC⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _) sqD
    exact (exists_point_of_isPullback B S hS sq' z c hcz.symm).imp fun _ ↦ And.symm
  have hQhomeo : IsHomeomorph
      (pointsMap B S hS (yoneda.obj (hf.pullback (a ≫ g)))
        (yoneda.map (hf.snd (a ≫ g)))) := by
    refine (isHomeomorph_pointsMap_yonedaMap_iff B S hS (hf.snd (a ≫ g))).2 ?_
    have hUH : AlgebraicGeometry.UniversalHomeomorphism (T.map (hf.snd (a ≫ g))) :=
      h.property_snd (a ≫ g)
    exact hUH.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  let eAssoc := pullbackRightPullbackFstIso g f a
  let eRep := (hf.isPullback (a ≫ g)).isoPullback ≪≫ pullbackSymmetry f (a ≫ g)
  let e : pullback a (pullback.fst g f) ≅ yoneda.obj (hf.pullback (a ≫ g)) :=
    eAssoc ≪≫ eRep.symm
  have he : e.hom ≫ yoneda.map (hf.snd (a ≫ g)) = pullback.fst a (pullback.fst g f) := by
    simp only [e, eRep, eAssoc, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
      pullbackSymmetry_inv_comp_snd, IsPullback.isoPullback_inv_snd]
    exact pullbackRightPullbackFstIso_hom_fst g f a
  have hrHomeo : IsHomeomorph
      (pointsMap B S hS (pullback a (pullback.fst g f))
        (pullback.fst a (pullback.fst g f))) := by
    rw [← he]
    exact isHomeomorph_pointsMap_iso_hom_comp B S hS e hQhomeo
  have hcomm : pointsMap B S hS (yoneda.obj U) a ∘
      pointsMap B S hS (pullback a (pullback.fst g f))
        (pullback.fst a (pullback.fst g f)) =
      pointsMap B S hS (pullback g f) (pullback.fst g f) ∘
        pointsMap B S hS (pullback a (pullback.fst g f))
          (pullback.snd a (pullback.fst g f)) := by
    rw [← pointsMap_comp, ← pointsMap_comp, sqD.w]
  have hsurj : Function.Surjective
      (pointsMap B S hS (pullback g f) (pullback.fst g f)) := by
    have hcompSurj := hAtlasSurj.comp hrHomeo.bijective.2
    rw [hcomm] at hcompSurj
    exact hcompSurj.of_comp
  have hinj : Function.Injective
      (pointsMap B S hS (pullback g f) (pullback.fst g f)) := by
    intro c₁ c₂ hc
    obtain ⟨w, hw⟩ :=
      hAtlasSurj (pointsMap B S hS (pullback g f) (pullback.fst g f) c₁)
    obtain ⟨d₁, hd₁c, hd₁w⟩ := hcart c₁ w hw.symm
    obtain ⟨d₂, hd₂c, hd₂w⟩ := hcart c₂ w (hc ▸ hw.symm)
    have hd : d₁ = d₂ := hrHomeo.bijective.1 (hd₁w.trans hd₂w.symm)
    rw [← hd₁c, ← hd₂c, hd]
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨continuous_pointsMap B S hS _, hclosed, ⟨hinj, hsurj⟩⟩

/-! ### The two notions agree -/

/-- A representable morphism of algebraic spaces over `S` has universal
homeomorphy of every one of its represented base changes, which is what being a universal
homeomorphism means for a representable morphism, exactly when it is a universal homeomorphism in
the sense of Stacks 05Z5: every base change of it by an algebraic space over `S` induces a
homeomorphism on the spaces of points. -/
@[stacks 05Z4]
theorem presheaf_universalHomeomorphism_iff
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f ↔ UniversalHomeomorphism B S hS f :=
  ⟨universalHomeomorphism_of_presheaf_universalHomeomorphism B S hS hX hY hf,
    presheaf_universalHomeomorphism_of_universalHomeomorphism B S hS hf⟩

end Space

end AlgebraicGeometry

end
