module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.RelationQuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraicGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafFppfOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace

/-!
# An algebraic space étale over the spectrum of a field is a scheme

Let `F` be an algebraic space over `S` and let `F ⟶ h_V` be an étale morphism to an object `V`
of the big fppf site over `S` whose underlying scheme is the spectrum of a field `k`. Then `F`
is representable.

Take a surjective étale atlas `h_U ⟶ F` with `U` a disjoint union of affine schemes `Y i`.
Each `Y i` is affine and étale over `Spec k`, hence finite over it, and the self-intersection
`R_i = Y i ×_F Y i` is a monomorphism into the affine scheme `Y i ×_{Spec k} Y i`, which is
again étale over `Spec k`; so `R_i` is affine and both of its maps to `Y i` are finite étale,
hence finite locally free. The quotient of the restricted relation is therefore a scheme, and
it is an open subspace of `F`; these open subspaces cover `F`, so `F` is a scheme.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_etale_over_field`: **Stacks 03KX**, an
  algebraic space étale over the spectrum of a field is representable.

## Implementation notes

The quotient of the relation restricted to a chart is a scheme by
`Stacks.Groupoids.isRepresentable_quotientSheaf_of_isFiniteLocallyFree`, and its map to the
quotient of the whole relation is an open immersion by Stacks 02WU
(`AlgebraicGeometry.isOpenImmersion_restrictedQuotientMap`). Identifying the quotient of the
whole relation with `F` is `exists_quotientSheafIso_of_atlas` below, which is the universal
property of a surjective étale atlas (Stacks 0262, part (3)) read against the universal
property of the quotient sheaf.

Comparing the relation scheme of a chart with the restriction of the whole relation along the
chart is `exists_iso_restriction_of_kernel_pairs`: the two kernel pairs are related by the
universal property of the larger one, and the comparison is an isomorphism because both
squares are cartesian. It is stated for an arbitrary functor preserving fibre products and
binary products, since the comparison has to be read in schemes over `S` rather than in the
site.

## References

* [Stacks Project, Tag 03KX](https://stacks.math.columbia.edu/tag/03KX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

universe u v

namespace AlgebraicGeometry.Space

/-! ### Comparing the kernel pairs of a morphism and of its restriction -/

/-- The kernel pair of the restriction of `a : h_U ⟶ F` along `m : U' ⟶ U` maps to the kernel
pair of `a`, cartesianly over the square `U' ×_S U' ⟶ U ×_S U`. -/
private theorem exists_isPullback_of_kernel_pairs {C : Type*} [Category.{u} C]
    [HasBinaryProducts C] {R U R' U' : C} {F : Cᵒᵖ ⥤ Type u}
    (a : yoneda.obj U ⟶ F) (s t : R ⟶ U) (m : U' ⟶ U) (s' t' : R' ⟶ U')
    (hp : IsPullback (yoneda.map s) (yoneda.map t) a a)
    (hp' : IsPullback (yoneda.map s') (yoneda.map t')
      (yoneda.map m ≫ a) (yoneda.map m ≫ a)) :
    ∃ r : R' ⟶ R, IsPullback (prod.lift s' t') r (prod.map m m) (prod.lift s t) := by
  let r := yoneda.preimage (hp.lift (yoneda.map (s' ≫ m))
    (yoneda.map (t' ≫ m)) (by simpa using hp'.w))
  have hrs : r ≫ s = s' ≫ m := by
    apply yoneda.map_injective
    simp [r]
  have hrt : r ≫ t = t' ≫ m := by
    apply yoneda.map_injective
    simp [r]
  have hw : prod.lift s' t' ≫ prod.map m m = r ≫ prod.lift s t := by
    apply prod.hom_ext <;> simp [hrs, hrt]
  refine ⟨r, ⟨⟨hw⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩⟩
  intro c
  change {l : c.pt ⟶ R' // l ≫ prod.lift s' t' = c.fst ∧ l ≫ r = c.snd ∧
    ∀ {m' : c.pt ⟶ R'}, m' ≫ prod.lift s' t' = c.fst → m' ≫ r = c.snd → m' = l}
  have hcs : c.fst ≫ prod.fst ≫ m = c.snd ≫ s := by
    simpa using congrArg (· ≫ prod.fst) c.condition
  have hct : c.fst ≫ prod.snd ≫ m = c.snd ≫ t := by
    simpa using congrArg (· ≫ prod.snd) c.condition
  have hc : yoneda.map (c.fst ≫ prod.fst) ≫ (yoneda.map m ≫ a) =
      yoneda.map (c.fst ≫ prod.snd) ≫ (yoneda.map m ≫ a) := by
    rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    simp only [Category.assoc, hcs, hct, Functor.map_comp]
    rw [hp.w]
  let l := yoneda.preimage (hp'.lift (yoneda.map (c.fst ≫ prod.fst))
    (yoneda.map (c.fst ≫ prod.snd)) hc)
  have hls : l ≫ s' = c.fst ≫ prod.fst := by
    apply yoneda.map_injective
    simp [l]
  have hlt : l ≫ t' = c.fst ≫ prod.snd := by
    apply yoneda.map_injective
    simp [l]
  refine ⟨l, ?_, ?_, ?_⟩
  · apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using hls
    · simpa only [Category.assoc, prod.lift_snd] using hlt
  · apply yoneda.map_injective
    apply hp.hom_ext
    · rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      rw [Category.assoc, hrs, ← Category.assoc, hls, Category.assoc, hcs]
    · rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      rw [Category.assoc, hrt, ← Category.assoc, hlt, Category.assoc, hct]
  · intro l' hl₁ hl₂
    apply yoneda.map_injective
    apply hp'.hom_ext
    · have h := congrArg (· ≫ prod.fst) hl₁
      rw [← Functor.map_comp, ← Functor.map_comp, hls]
      apply congrArg yoneda.map
      simpa only [Category.assoc, prod.lift_fst] using h
    · have h := congrArg (· ≫ prod.snd) hl₁
      rw [← Functor.map_comp, ← Functor.map_comp, hlt]
      apply congrArg yoneda.map
      simpa only [Category.assoc, prod.lift_snd] using h

/-- The image under a functor preserving fibre products and binary products of the kernel pair
of the restriction of `a : h_U ⟶ F` along `m : U' ⟶ U` is the restriction, along the image of
`m`, of the image of the kernel pair of `a`. -/
private theorem exists_iso_restriction_of_kernel_pairs {C D : Type*} [Category.{u} C]
    [Category.{u} D] [HasBinaryProducts C] [HasBinaryProducts D] [HasPullbacks D]
    (G : C ⥤ D) [PreservesLimitsOfShape WalkingCospan G]
    [PreservesLimitsOfShape (Discrete WalkingPair) G]
    {R U R' U' : C} {F : Cᵒᵖ ⥤ Type u}
    (a : yoneda.obj U ⟶ F) (s t : R ⟶ U) (m : U' ⟶ U) (s' t' : R' ⟶ U')
    (hp : IsPullback (yoneda.map s) (yoneda.map t) a a)
    (hp' : IsPullback (yoneda.map s') (yoneda.map t')
      (yoneda.map m ≫ a) (yoneda.map m ≫ a)) :
    ∃ e : G.obj R' ≅ pullback (prod.map (G.map m) (G.map m))
        (prod.lift (G.map s) (G.map t)),
      e.hom ≫ pullback.fst _ _ = prod.lift (G.map s') (G.map t') := by
  obtain ⟨r, hr⟩ := exists_isPullback_of_kernel_pairs a s t m s' t' hp hp'
  have h : IsPullback (prod.lift (G.map s') (G.map t')) (G.map r)
      (prod.map (G.map m) (G.map m)) (prod.lift (G.map s) (G.map t)) := by
    apply (hr.map G).of_iso (Iso.refl _) (asIso (prodComparison G U' U'))
      (Iso.refl _) (asIso (prodComparison G U U))
    · apply prod.hom_ext <;> simp [← Functor.map_comp]
    · simp
    · exact prodComparison_natural G m m
    · apply prod.hom_ext <;> simp [← Functor.map_comp]
  exact ⟨h.isoPullback, h.isoPullback_hom_fst⟩

/-! ### Naturality of the comparison with the restricted functor of points -/

/-- `AlgebraicGeometry.Space.pointsYonedaIso` is natural: its inverses carry a map of
represented presheaves to the map of restricted functors of points of its image. -/
private theorem pointsYonedaIso_inv_naturality {C : Type v} [Category.{u} C] {S : Scheme.{u}}
    (Φ : C ⥤ Over S) [Φ.Full] [Φ.Faithful] {X Y : C} (φ : X ⟶ Y) :
    (pointsYonedaIso Φ X).inv ≫ Φ.op.whiskerLeft (yoneda.map (Φ.map φ)) =
      yoneda.map φ ≫ (pointsYonedaIso Φ Y).inv := by
  have h := pointsYonedaIso_inv_comp Φ (Φ.map φ)
  rw [Φ.preimage_map] at h
  rw [← h]
  simp

/-- `AlgebraicGeometry.Space.pointsYonedaIso` is natural: it carries the map of restricted
functors of points of an image to the map of represented presheaves. -/
private theorem pointsYonedaIso_hom_naturality {C : Type v} [Category.{u} C] {S : Scheme.{u}}
    (Φ : C ⥤ Over S) [Φ.Full] [Φ.Faithful] {X Y : C} (φ : X ⟶ Y) :
    Φ.op.whiskerLeft (yoneda.map (Φ.map φ)) ≫ (pointsYonedaIso Φ Y).hom =
      (pointsYonedaIso Φ X).hom ≫ yoneda.map φ := by
  have h := pointsYonedaIso_inv_comp Φ (Φ.map φ)
  rw [Φ.preimage_map] at h
  rw [← h]
  simp

/-! ### An algebraic space is the quotient sheaf of its kernel pair -/

/-- **A surjective étale atlas identifies an algebraic space with the quotient sheaf of its
kernel pair.** The isomorphism carries the canonical projection of the chart onto the quotient
sheaf to the atlas. -/
private theorem exists_quotientSheafIso_of_atlas
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R U : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : yoneda.obj U ⟶ F) (s t : R ⟶ U)
    (hp : IsPullback (yoneda.map s) (yoneda.map t) a a)
    (hF : IsAlgebraicSpace B S hS F)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∃ e : (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
        (prod.lift ((Over.post B.inclusion).map s)
          ((Over.post B.inclusion).map t))).obj ≅ F,
      (pointsYonedaIso (Over.post B.inclusion) U).inv ≫
        toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
          (prod.lift ((Over.post B.inclusion).map s)
            ((Over.post B.inclusion).map t)) ≫ e.hom = a := by
  let J := BigFppfOver.topology B S hS
  let G : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  have _ : G.Full := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Full
  have _ : G.Faithful := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Faithful
  let j : PreRelation (G.obj R) (G.obj U) := prod.lift (G.map s) (G.map t)
  let Q := quotientSheaf J G j
  let p := toQuotientSheaf J G j
  let q : yoneda.obj U ⟶ Q.obj := (pointsYonedaIso G U).inv ≫ p
  let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  have hw : Stacks.Groupoids.sourceMap G j ≫ ((pointsYonedaIso G U).hom ≫ a) =
      Stacks.Groupoids.targetMap G j ≫ ((pointsYonedaIso G U).hom ≫ a) := by
    simp only [Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap,
      PreRelation.source, PreRelation.target, j,
      prod.lift_fst, prod.lift_snd, ← Category.assoc, pointsYonedaIso_hom_naturality]
    simp only [Category.assoc, hp.w]
  let d : Q ⟶ FF := quotientSheafDesc J G j FF ((pointsYonedaIso G U).hom ≫ a) hw
  have hd : p ≫ d.hom = (pointsYonedaIso G U).hom ≫ a :=
    toQuotientSheaf_quotientSheafDesc J G j FF _ hw
  have hqd : q ≫ d.hom = a := by
    dsimp only [q]
    rw [Category.assoc, hd]
    simp
  have hq : yoneda.map s ≫ q = yoneda.map t ≫ q := by
    dsimp only [q]
    rw [← Category.assoc, ← pointsYonedaIso_inv_naturality, Category.assoc,
      ← Category.assoc (yoneda.map t), ← pointsYonedaIso_inv_naturality, Category.assoc]
    apply congrArg ((pointsYonedaIso G R).inv ≫ ·)
    simpa only [Stacks.Groupoids.sourceMap, Stacks.Groupoids.targetMap,
      PreRelation.source, PreRelation.target, j,
      prod.lift_fst, prod.lift_snd] using (sourceMap_toQuotientSheaf J G j).symm
  obtain ⟨hR, hU, ⟨hc⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS a s t hp hF hsurj hetale
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hU⟩
  let qf : UF ⟶ Q := ⟨q⟩
  let c : FF ⟶ Q := Cofork.IsColimit.desc hc qf (by apply Sheaf.hom_ext; exact hq)
  have hac : a ≫ c.hom = q :=
    congrArg (fun z => z.hom) (Cofork.IsColimit.π_desc' hc qf _)
  have hcd : c ≫ d = 𝟙 FF := by
    apply Cofork.IsColimit.hom_ext hc
    apply Sheaf.hom_ext
    change a ≫ c.hom ≫ d.hom = a ≫ 𝟙 F
    rw [← Category.assoc, hac, hqd, Category.comp_id]
  have hdc : d ≫ c = 𝟙 Q := by
    apply quotientSheaf_hom_ext J G j Q
    change p ≫ d.hom ≫ c.hom = p ≫ 𝟙 Q.obj
    rw [← Category.assoc, hd, Category.assoc, hac]
    simp only [q, Iso.hom_inv_id_assoc]
    exact (Category.comp_id p).symm
  exact ⟨(sheafToPresheaf J (Type u)).mapIso ⟨d, c, hdc, hcd⟩, hqd⟩

/-! ### Charts of an algebraic space étale over a field -/

/-- A finite étale morphism of schemes is finite locally free. -/
@[ega "IV 18.2.7"]
private theorem isFiniteLocallyFree_of_isFinite_of_etale {X Y : Scheme.{u}} (g : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsFinite g] [Etale g] :
    Stacks.Morphisms.IsFiniteLocallyFree g :=
  (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).2
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- An étale morphism from an affine scheme to a scheme finite étale over a field is finite
locally free. -/
private theorem isFiniteLocallyFree_of_etale_of_isAffine_over_field (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsAffine X] (g : X ⟶ Y) (h : Y ⟶ Spec (.of k)) [Etale g] [Etale h]
    [_root_.AlgebraicGeometry.IsFinite h] : Stacks.Morphisms.IsFiniteLocallyFree g := by
  have : _root_.AlgebraicGeometry.IsFinite (g ≫ h) :=
    isFinite_of_isAffine_of_etale_over_field k _
  have := _root_.AlgebraicGeometry.IsFinite.of_comp g h
  exact isFiniteLocallyFree_of_isFinite_of_etale g

/-- If two maps `s t : R ⟶ U` of the big fppf site are jointly monic in schemes over `S`, the
induced map from `R` into a fibre product of schemes over a map equalising them is a
monomorphism. -/
private theorem mono_pullbackLift_of_mono_prodLift (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {R U : BigFppfOver B S hS} (s t : R ⟶ U) {Z : Scheme.{u}}
    (g : (BigFppfOver.toScheme B S hS).obj U ⟶ Z)
    (hst : (BigFppfOver.toScheme B S hS).map s ≫ g = (BigFppfOver.toScheme B S hS).map t ≫ g)
    (hmono : Mono (prod.lift ((Over.post B.inclusion : BigFppfOver B S hS ⥤ Over S).map s)
      ((Over.post B.inclusion : BigFppfOver B S hS ⥤ Over S).map t))) :
    Mono (pullback.lift _ _ hst) := by
  let T := BigFppfOver.toScheme B S hS
  let G : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  refine ⟨fun {W} x y hxy => ?_⟩
  have hfst : x ≫ T.map s = y ≫ T.map s := by
    simpa [T, pullback.lift_fst] using congrArg (fun h => h ≫ pullback.fst g g) hxy
  have hsnd : x ≫ T.map t = y ≫ T.map t := by
    simpa [T, pullback.lift_snd] using congrArg (fun h => h ≫ pullback.snd g g) hxy
  have hstructure (p : R ⟶ U) :
      T.map p ≫ B.inclusion.map (Over.hom U) = B.inclusion.map (Over.hom R) := by
    dsimp [T, BigFppfOver.toScheme, BigFppfOver.forget]
    exact congrArg B.inclusion.map (Over.w p)
  have hbase : y ≫ B.inclusion.map (Over.hom R) = x ≫ B.inclusion.map (Over.hom R) := by
    rw [← hstructure s, ← Category.assoc, ← hfst, Category.assoc, hstructure s]
  let W' : Over ((B.obj hS).obj) := Over.mk (x ≫ B.inclusion.map (Over.hom R))
  let x' : W' ⟶ G.obj R := Over.homMk x (by simp [W', G, Over.post])
  let y' : W' ⟶ G.obj R := Over.homMk y (by simpa [W', G, Over.post] using hbase)
  have hpair : x' ≫ prod.lift (G.map s) (G.map t) = y' ≫ prod.lift (G.map s) (G.map t) := by
    refine prod.hom_ext ?_ ?_
    · simpa [Category.assoc] using
        Over.OverMorphism.ext (show x ≫ T.map s = y ≫ T.map s from hfst)
    · simpa [Category.assoc] using
        Over.OverMorphism.ext (show x ≫ T.map t = y ≫ T.map t from hsnd)
  exact congrArg Over.Hom.left (hmono.right_cancellation x' y' hpair)

/-- **Stacks 03KX.** An algebraic space over `S` admitting an étale morphism to an object of the
big fppf site over `S` whose underlying scheme is the spectrum of a field is representable. -/
@[stacks 03KX]
theorem isRepresentable_of_etale_over_field
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (k : Type u) [Field k]
    (V : BigFppfOver B S hS)
    (eV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (f : F ⟶ yoneda.obj V) (hf : IsEtale B S hS f) :
    F.IsRepresentable := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let J := BigFppfOver.topology B S hS
  let G : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  have _ : G.Full := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Full
  have _ : G.Faithful := inferInstanceAs (Over.post (X := B.obj hS) B.inclusion).Faithful
  let _ : HasFiniteLimits B.Schemes := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let _ : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  let _ : PreservesFiniteLimits G :=
    PreservesFiniteLimits.overPost (F := B.inclusion) (X := B.obj hS)
  let _ : PreservesLimitsOfShape WalkingCospan G := inferInstance
  let _ : PreservesLimitsOfShape (Discrete WalkingPair) G := inferInstance
  obtain ⟨U, atlas, I, Y, e, hAtlasSurj, hAtlasEtale, hYaffine, -⟩ :=
    exists_etale_surjective_coproduct_affine_cover B S hS F hF
  -- the affine pieces of the atlas, as objects of the site
  have hYiSize (i : I) : (Y i).size < B.cutoff := by
    let e' : Y i ⟶ T.obj U := Sigma.ι Y i ≫ e.hom
    have _ : _root_.AlgebraicGeometry.IsOpenImmersion e' := by
      dsimp [e']
      infer_instance
    exact Scheme.size_lt_of_isOpenImmersion e' U.left.property
  let Ui (i : I) : BigFppfOver B S hS :=
    Over.mk ((B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hYiSize i)) ⟶ B.inclusion.obj U.left from
        Sigma.ι Y i ≫ e.hom)) ≫ U.hom)
  let mi (i : I) : Ui i ⟶ U :=
    Over.homMk (B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hYiSize i)) ⟶ B.inclusion.obj U.left from
        Sigma.ι Y i ≫ e.hom))
  have hmi (i : I) : T.map (mi i) = Sigma.ι Y i ≫ e.hom :=
    B.inclusion.map_preimage
      (show B.inclusion.obj (B.obj (hYiSize i)) ⟶ B.inclusion.obj U.left from
        Sigma.ι Y i ≫ e.hom)
  have hmiOpen (i : I) : _root_.AlgebraicGeometry.IsOpenImmersion (T.map (mi i)) := by
    rw [hmi]
    infer_instance
  let atlasI (i : I) : yoneda.obj (Ui i) ⟶ F := yoneda.map (mi i) ≫ atlas
  have hatlasIEtale (i : I) :
      (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf (atlasI i) := by
    have hmiEtale : Etale (T.map (mi i)) := by
      have _ := hmiOpen i
      infer_instance
    let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
    have _ : P.IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage _
    have _ : P.IsStableUnderBaseChange := ⟨by
      intro X₁ X₂ X₃ X₄ f₁ g₁ f₂ g₂ hpb hg
      change Etale (T.map g₂)
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Etale) (hpb.map T) hg⟩
    have _ : P.presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    exact MorphismProperty.comp_mem _ _ _
      (MorphismProperty.relative_map_iff (P := P) |>.2 hmiEtale) hAtlasEtale
  -- each chart is étale over the field
  let chartMap (i : I) : Ui i ⟶ V := yoneda.preimage (atlasI i ≫ f)
  have hchartMap (i : I) : yoneda.map (chartMap i) = atlasI i ≫ f := yoneda.map_preimage _
  have hchartMapEtale (i : I) : Etale (T.map (chartMap i)) := by
    refine MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@Etale.{u}) T) (F := yoneda) ?_
    rw [hchartMap]
    exact hf (Ui i) (atlasI i) (hatlasIEtale i)
  let fieldMap (i : I) : T.obj (Ui i) ⟶ Spec (.of k) := T.map (chartMap i) ≫ eV.hom
  have hUiAffine (i : I) : IsAffine (T.obj (Ui i)) := hYaffine i
  have hFieldMapEtale (i : I) : Etale (fieldMap i) := by
    have _ : Etale (T.map (chartMap i)) := hchartMapEtale i
    infer_instance
  have hFieldMapFinite (i : I) : _root_.AlgebraicGeometry.IsFinite (fieldMap i) := by
    have _ := hUiAffine i
    have _ := hFieldMapEtale i
    exact isFinite_of_isAffine_of_etale_over_field k (fieldMap i)
  -- the kernel pair of the whole atlas
  have hAtlasDiag := hF.diagonal_representable.of_diag atlas
  let globalR := hAtlasDiag.pullback atlas
  let globalS : globalR ⟶ U := yoneda.preimage (hAtlasDiag.fst atlas)
  let globalT : globalR ⟶ U := hAtlasDiag.snd atlas
  have hGlobalKernel :
      IsPullback (yoneda.map globalS) (yoneda.map globalT) atlas atlas := by
    simpa [globalS, globalT] using hAtlasDiag.isPullback atlas
  let globalRel : PreRelation (G.obj globalR) (G.obj U) :=
    prod.lift (G.map globalS) (G.map globalT)
  have hGlobalEquiv : IsEquivalenceRelation globalRel.target globalRel.source := by
    have ht : globalRel.target = G.map globalS := by
      dsimp [globalRel, PreRelation.target]
      simp
    have hs : globalRel.source = G.map globalT := by
      dsimp [globalRel, PreRelation.source]
      simp
    rw [ht, hs]
    exact isEquivalenceRelation_of_isPullback B S hS atlas globalS globalT hGlobalKernel
  -- the kernel pairs of the charts
  have hLocalKernel (i : I) :
      ∃ (Rᵢ : BigFppfOver B S hS) (sᵢ tᵢ : Rᵢ ⟶ Ui i),
        IsPullback (yoneda.map sᵢ) (yoneda.map tᵢ) (atlasI i) (atlasI i) := by
    have hdiag := hF.diagonal_representable.of_diag (atlasI i)
    exact ⟨hdiag.pullback (atlasI i), yoneda.preimage (hdiag.fst (atlasI i)),
      hdiag.snd (atlasI i), by simpa using hdiag.isPullback (atlasI i)⟩
  choose Rchart schart tchart hChartKernel using hLocalKernel
  have hChartSourceEtale (i : I) : Etale (T.map (schart i)) :=
    (hatlasIEtale i).property (atlasI i) (yoneda.map (tchart i))
      (schart i) (hChartKernel i).flip
  have hChartTargetEtale (i : I) : Etale (T.map (tchart i)) :=
    (hatlasIEtale i).property (atlasI i) (yoneda.map (schart i))
      (tchart i) (hChartKernel i)
  have hChartEquiv (i : I) :
      IsEquivalenceRelation (G.map (schart i)) (G.map (tchart i)) :=
    isEquivalenceRelation_of_isPullback B S hS (atlasI i) (schart i) (tchart i)
      (hChartKernel i)
  have hChartMapsAgree (i : I) : schart i ≫ chartMap i = tchart i ≫ chartMap i := by
    apply yoneda.map_injective
    calc
      yoneda.map (schart i ≫ chartMap i)
          = yoneda.map (schart i) ≫ yoneda.map (chartMap i) := by simp
      _ = yoneda.map (schart i) ≫ atlasI i ≫ f := by rw [hchartMap]
      _ = yoneda.map (tchart i) ≫ atlasI i ≫ f := by
        simpa [Category.assoc] using congrArg (fun g => g ≫ f) (hChartKernel i).w
      _ = yoneda.map (tchart i ≫ chartMap i) := by rw [Functor.map_comp, hchartMap]
  have hChartMapsAgreeScheme (i : I) :
      T.map (schart i) ≫ fieldMap i = T.map (tchart i) ≫ fieldMap i := by
    calc
      _ = T.map (schart i ≫ chartMap i) ≫ eV.hom := by simp [fieldMap, Category.assoc]
      _ = T.map (tchart i ≫ chartMap i) ≫ eV.hom :=
        congrArg (fun g => g ≫ eV.hom) (congrArg T.map (hChartMapsAgree i))
      _ = _ := by simp [fieldMap, Category.assoc]
  -- the relation scheme of a chart is affine, by a monomorphism into a field-étale affine
  let fieldPair (i : I) := pullback (fieldMap i) (fieldMap i)
  let chartPairMap (i : I) : T.obj (Rchart i) ⟶ fieldPair i :=
    pullback.lift (T.map (schart i)) (T.map (tchart i)) (hChartMapsAgreeScheme i)
  have hFieldPairAffine (i : I) : IsAffine (fieldPair i) := by
    have _ := hUiAffine i
    have _ := hFieldMapFinite i
    have _ : _root_.AlgebraicGeometry.IsAffineHom (fieldMap i) := inferInstance
    infer_instance
  have hFieldPairEtale (i : I) :
      Etale (pullback.fst (fieldMap i) (fieldMap i) ≫ fieldMap i) := by
    have hfst : Etale (pullback.fst (fieldMap i) (fieldMap i)) :=
      Etale.etale_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback (fieldMap i) (fieldMap i)).flip (hFieldMapEtale i)
    exact Etale.etale_comp _ _
  have hChartPairMonoOver (i : I) : Mono (prod.lift (G.map (schart i)) (G.map (tchart i))) := by
    let r : EquivalenceRelation (G.map (schart i)) (G.map (tchart i)) :=
      Classical.choice (hChartEquiv i).nonempty_equivalenceRelation
    refine ⟨fun {W} x y hxy => r.right_cancellation x y ?_ ?_⟩
    · simpa using congrArg (fun g => g ≫ prod.fst) hxy
    · simpa using congrArg (fun g => g ≫ prod.snd) hxy
  have hChartPairMapMono (i : I) : Mono (chartPairMap i) :=
    mono_pullbackLift_of_mono_prodLift B S hS (schart i) (tchart i) (fieldMap i)
      (hChartMapsAgreeScheme i) (hChartPairMonoOver i)
  have hChartArrowAffine (i : I) : IsAffine (T.obj (Rchart i)) := by
    have _ := hFieldPairAffine i
    have _ := hFieldPairEtale i
    have _ := hChartPairMapMono i
    exact isAffine_of_mono_of_etale_over_field k
      (pullback.fst (fieldMap i) (fieldMap i) ≫ fieldMap i) (chartPairMap i)
  -- hence both of its maps are finite étale, hence finite locally free
  have hChartFree (i : I) (p : Rchart i ⟶ Ui i) (hp : Etale (T.map p)) :
      Stacks.Morphisms.IsFiniteLocallyFree (T.map p) := by
    have _ := hChartArrowAffine i
    have _ := hFieldMapEtale i
    have _ := hFieldMapFinite i
    exact isFiniteLocallyFree_of_etale_of_isAffine_over_field k _ (fieldMap i)
  -- the quotient of the relation restricted to a chart is a scheme
  let restrictedRel (i : I) := AlgebraicGeometry.PreRelation.restrict globalRel (G.map (mi i))
  have hRestrictedRep (i : I) : (quotientSheaf J G (restrictedRel i)).obj.IsRepresentable := by
    obtain ⟨eR, heR⟩ := exists_iso_restriction_of_kernel_pairs G atlas
      globalS globalT (mi i) (schart i) (tchart i) hGlobalKernel (hChartKernel i)
    have _ : IsIso eR.hom.left := inferInstanceAs (IsIso ((Over.forget S).map eR.hom))
    have _ : IsIso eR.inv.left := inferInstanceAs (IsIso ((Over.forget S).map eR.inv))
    have hfree (p : Rchart i ⟶ Ui i) (hp : Stacks.Morphisms.IsFiniteLocallyFree (T.map p))
        (x : _ ⟶ G.obj (Ui i)) (hx : eR.hom ≫ x = G.map p) :
        Stacks.Morphisms.IsFiniteLocallyFree x.left := by
      have hx' : x.left = eR.inv.left ≫ T.map p :=
        congrArg Over.Hom.left (by rw [← hx]; simp : x = eR.inv ≫ G.map p)
      rw [hx']
      exact MorphismProperty.RespectsIso.precomp
        (@Stacks.Morphisms.IsFiniteLocallyFree.{u}) _ _ hp
    have _ : IsAffine (G.obj (Ui i)).left := hUiAffine i
    have _ : IsAffine (G.obj (Rchart i)).left := hChartArrowAffine i
    have _ : IsAffine (AlgebraicGeometry.PreRelation.restriction globalRel
        (G.map (mi i))).left := IsAffine.of_isIso eR.inv.left
    have _ : Stacks.Morphisms.IsFiniteLocallyFree (restrictedRel i).source.left :=
      hfree (tchart i) (hChartFree i _ (hChartTargetEtale i)) _ (by
        change eR.hom ≫ pullback.fst _ _ ≫ prod.snd = _
        rw [← Category.assoc, heR, prod.lift_snd])
    have _ : Stacks.Morphisms.IsFiniteLocallyFree (restrictedRel i).target.left :=
      hfree (schart i) (hChartFree i _ (hChartSourceEtale i)) _ (by
        change eR.hom ≫ pullback.fst _ _ ≫ prod.fst = _
        rw [← Category.assoc, heR, prod.lift_fst])
    exact isRepresentable_quotientSheaf_of_isFiniteLocallyFree B S hS (restrictedRel i)
      (hYiSize i)
  -- the quotient of the whole relation is `F`
  obtain ⟨eGlobal, heGlobal⟩ :
      ∃ eg : (quotientSheaf J G globalRel).obj ≅ F,
        (pointsYonedaIso G U).inv ≫ toQuotientSheaf J G globalRel ≫ eg.hom = atlas :=
    exists_quotientSheafIso_of_atlas B S hS atlas globalS globalT hGlobalKernel hF
      hAtlasSurj hAtlasEtale
  have hglobal {P : MorphismProperty Scheme.{u}}
      (h : (MorphismProperty.inverseImage P T).presheaf atlas) :
      P globalRel.source.left ∧ P globalRel.target.left := by
    constructor
    · simp only [globalRel, PreRelation.source, prod.lift_snd]
      exact h.property atlas (yoneda.map globalS) globalT hGlobalKernel
    · simp only [globalRel, PreRelation.target, prod.lift_fst]
      exact h.property atlas (yoneda.map globalT) globalS hGlobalKernel.flip
  obtain ⟨hgs, hgt⟩ := hglobal hAtlasEtale
  obtain ⟨hgss, hgts⟩ := hglobal hAtlasSurj
  -- the open subspaces of `F` cut out by the charts
  let Q (i : I) := quotientSheaf J G (restrictedRel i)
  let b (i : I) : yoneda.obj (Q i).obj.reprX ⟶ F :=
    (Q i).obj.reprW.hom ≫
      (restrictQuotientSheafMap J G globalRel (G.map (mi i))).hom ≫ eGlobal.hom
  have hb (i : I) : IsOpenImmersion B S hS (b i) := by
    have _ : _root_.AlgebraicGeometry.IsOpenImmersion (G.map (mi i)).left := hmiOpen i
    have h := isOpenImmersion_restrictedQuotientMap B hS globalRel (G.map (mi i))
      hgss hgts inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
    exact MorphismProperty.RespectsIso.precomp _ (Q i).obj.reprW.hom _
      (MorphismProperty.RespectsIso.postcomp _ eGlobal.hom _ h)
  have hfactor (i : I) : ∃ z : yoneda.obj (Ui i) ⟶ yoneda.obj (Q i).obj.reprX,
      z ≫ b i = atlasI i := by
    refine ⟨(pointsYonedaIso G (Ui i)).inv ≫
      toQuotientSheaf J G (restrictedRel i) ≫ (Q i).obj.reprW.inv, ?_⟩
    dsimp only [b]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change (pointsYonedaIso G (Ui i)).inv ≫
      (toQuotientSheaf J G (restrictedRel i) ≫
        (restrictQuotientSheafMap J G globalRel (G.map (mi i))).hom) ≫ eGlobal.hom = atlasI i
    rw [restrictQuotientSheafMap, toQuotientSheaf_comp_quotientSheafMap,
      ← Category.assoc (pointsYonedaIso G (Ui i)).inv,
      ← Category.assoc _ _ (toQuotientSheaf J G globalRel), pointsYonedaIso_inv_naturality]
    simpa only [Category.assoc] using congrArg (yoneda.map (mi i) ≫ ·) heGlobal
  let images (i : I) := Subfunctor.range (b i)
  apply isRepresentable_of_isZariskiCover B S hS F hF I images
    ⟨fun i => isOpenSubspace_range_of_isOpenImmersion _ (b i) (hb i), ?_⟩
    (fun i => isRepresentable_range_of_isOpenImmersion _ (b i) (hb i))
  -- the charts cover `F`
  have hcover : Sieve.ofArrows Ui mi ∈ J U := by
    refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS mi (fun i => ?_)
      (fun x => ?_)
    · exact hmiOpen i
    · obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk Y).surjective (e.inv x)
      refine ⟨i, y, ?_⟩
      change T.map (mi i) y = x
      rw [hmi]
      rw [sigmaMk_mk] at hy
      rw [Scheme.Hom.comp_apply, hy]
      exact Scheme.Hom.comp_apply e.inv e.hom x |>.symm.trans (by simp)
  have hlocal : Presheaf.IsLocallySurjective J atlas :=
    isLocallySurjective_of_surjective_etale B S hS atlas hAtlasSurj hAtlasEtale
  have hlocalCharts : Presheaf.IsLocallySurjective J (Sigma.desc (fun i => atlasI i)) := by
    have _ : Presheaf.IsLocallySurjective J (Sigma.desc (fun i => yoneda.map (mi i))) :=
      locallySurjective_sigmaDesc_yoneda_map J mi hcover
    have hcomp : Sigma.desc (fun i => yoneda.map (mi i)) ≫ atlas =
        Sigma.desc (fun i => atlasI i) := by
      refine Sigma.hom_ext _ _ fun i => ?_
      simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, atlasI]
    rw [← hcomp]
    infer_instance
  choose z hz using hfactor
  refine Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (f₁ := Sigma.desc (fun i => z i ≫ Subfunctor.toRange (b i) ≫
      Sigma.ι (fun i => (images i).toFunctor) i))
    (f₃ := Sigma.desc (fun i => atlasI i)) ?_
  refine Sigma.hom_ext _ _ fun i => ?_
  simp only [Sigma.ι_comp_desc_assoc, Category.assoc, Sigma.ι_comp_desc, images,
    Subfunctor.toRange_ι, hz]

end AlgebraicGeometry.Space

end
