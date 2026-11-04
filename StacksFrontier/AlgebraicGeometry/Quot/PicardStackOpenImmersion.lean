module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RingedSite
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCanonical
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkFree
public import StacksFrontier.AlgebraicGeometry.Stacks.FullSubcategoryBaseChangeOpen
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenImmersion

/-!
# The Picard stack is an open substack of the stack of coherent sheaves (Stacks 0D03)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
flat, of finite presentation and proper.  The natural map `Pic_{X/B} ⟶ Coh_{X/B}` is representable
by open immersions.

## Main definitions

* `AlgebraicGeometry.Space.coherentCFG`: `Coh_{X/B}` at its canonical category structure, as a
  category fibred in groupoids over the big fppf site of `S` (Stacks 08W5).
* `AlgebraicGeometry.Space.picardToCoherent`: **the natural map `Pic_{X/B} ⟶ Coh_{X/B}`**, a
  1-morphism of categories fibred in groupoids, sending `(T, g, L)` to `(T, g, L)`.

## Main results

* `AlgebraicGeometry.Space.picardToCoherentBasedFullyFaithful`: the natural map is fully
  faithful.
* `AlgebraicGeometry.Space.range_subset_fibrewiseEtaleRankOneFreeLocus_of_isInvertibleModule`:
  if the pullback `F_{T'}` of an object `F` of `Coh_{X/B}` over `T` along `g : T' ⟶ T` is
  invertible, then `|T'|` maps into `U = T ∖ f_T(|X_T| ∖ W₁)`.
* `AlgebraicGeometry.Space.hasOpenLocus_picardToCoherent`: over every scheme-valued point of
  `Coh_{X/B}` the image of the natural map is cut out by an open subscheme of the base.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_and_isOpenImmersion_picardToCoherent`:
  the natural map is representable by open immersions.

## References

* [Stacks Project, Tag 0D03](https://stacks.math.columbia.edu/tag/0D03)
* [Stacks Project, Tag 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The natural map as a 1-morphism of categories fibred in groupoids -/

/-- `Coh_{X/Y}` at its canonical category structure (Stacks 08W5), as an object of the
2-category of categories fibred in groupoids over the big fppf site of `S`. -/
def coherentCFG (D : CoherentSituation B S hS) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (coherentBasedCategory D.categoryData) (by
    have h := D.projection_isFiberedInGroupoids
    rw [coherentSiteProjection_eq D.categoryData] at h
    exact h)

/-- The unit comparison of Stacks 03LU along the morphisms of base changes of a coherent
situation is the one of its Picard situation, at the level of isomorphisms. -/
theorem CoherentSituation.idComparison_eq_baseChangeIdComparison (D : CoherentSituation B S hS)
    (hc : ModulePushforwardCoherence B S hS) (T : SchemesOver D.Y) :
    D.idComparison hc T = baseChangeIdComparison hc D.f T :=
  rfl

/-- The composition comparison of Stacks 03LU along the morphisms of base changes of a coherent
situation is the one of its Picard situation, at the level of isomorphisms. -/
theorem CoherentSituation.compComparison_eq_baseChangeCompComparison
    (D : CoherentSituation B S hS) {T T' T'' : SchemesOver D.Y} (h : T ⟶ T') (h' : T' ⟶ T'') :
    D.compComparison h h' = baseChangeCompComparison D.f h h' :=
  rfl

/-- The unit comparison of the Picard situation of a coherent situation is the one of the
coherent situation's morphism, at the level of isomorphisms. -/
theorem CoherentSituation.baseChangeIdComparison_toPicardSituation (D : CoherentSituation B S hS)
    (hc : ModulePushforwardCoherence B S hS) (T : D.toPicardSituation.SchemesOver) :
    baseChangeIdComparison hc D.toPicardSituation.f T = baseChangeIdComparison hc D.f T :=
  rfl

/-- The composition comparison of the Picard situation of a coherent situation is the one of the
coherent situation's morphism, at the level of isomorphisms. -/
theorem CoherentSituation.baseChangeCompComparison_toPicardSituation
    (D : CoherentSituation B S hS) {T T' T'' : D.toPicardSituation.SchemesOver} (h : T ⟶ T')
    (h' : T' ⟶ T'') :
    baseChangeCompComparison D.toPicardSituation.f h h' = baseChangeCompComparison D.f h h' :=
  rfl

/-- The module comparison of the identity of an object of `Coh_{X/Y}`, transported to any test
scheme and module the object is equal to. -/
theorem CoherentHom.id_fibre_heq {D : CoherentSituation B S hS}
    (hc : ModulePushforwardCoherence B S hS) (A : CoherentObject D) (T : SchemesOver D.Y)
    (L : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) (hT : A.T = T) (hF : HEq A.F L) :
    HEq (CoherentHom.id hc A).fibre ((baseChangeIdComparison hc D.f T).hom.app L) := by
  subst hT
  subst hF
  rw [← CoherentSituation.idComparison_eq_baseChangeIdComparison]
  rfl

/-- The module comparison of a composite in `Coh_{X/Y}` is built from the composition
comparison of the Picard situation. -/
theorem CoherentHom.comp_fibre_eq_baseChangeCompComparison {D : CoherentSituation B S hS}
    {A C E : CoherentObject D} (m : CoherentHom A C) (n : CoherentHom C E) :
    (CoherentHom.comp m n).fibre =
      Functor.fibreComp (baseChangeCompComparison D.f m.base n.base) m.fibre n.fibre := by
  rewrite [show (CoherentHom.comp m n).fibre =
      Functor.fibreComp (D.compComparison m.base n.base) m.fibre n.fibre from rfl,
    CoherentSituation.compComparison_eq_baseChangeCompComparison]
  exact rfl

/-- The module comparison of a composite in `Coh_{X/Y}`, transported to any test schemes,
modules, base maps and comparisons its constituents are equal to. -/
theorem CoherentHom.comp_fibre_heq {D : CoherentSituation B S hS} {A C E : CoherentObject D}
    (m : CoherentHom A C) (n : CoherentHom C E) {T T' T'' : SchemesOver D.Y}
    (h : T ⟶ T') (h' : T' ⟶ T'')
    (L : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (L' : Modules.{u, u} B S hS (D.space T').1 (D.space T').2)
    (L'' : Modules.{u, u} B S hS (D.space T'').1 (D.space T'').2)
    (a : (modulePullback B S hS (D.relativeMap h)).obj L' ⟶ L)
    (b : (modulePullback B S hS (D.relativeMap h')).obj L'' ⟶ L')
    (hA : A.T = T) (hC : C.T = T') (hE : E.T = T'') (hAF : HEq A.F L) (hCF : HEq C.F L')
    (hEF : HEq E.F L'') (hm : HEq m.base h) (hn : HEq n.base h') (hmf : HEq m.fibre a)
    (hnf : HEq n.fibre b) :
    HEq (CoherentHom.comp m n).fibre
      (Functor.fibreComp (baseChangeCompComparison D.f h h') a b) := by
  subst hA hC hE hAF hCF hEF
  obtain rfl := eq_of_heq hm
  obtain rfl := eq_of_heq hn
  obtain rfl := eq_of_heq hmf
  obtain rfl := eq_of_heq hnf
  exact heq_of_eq (CoherentHom.comp_fibre_eq_baseChangeCompComparison m n)

/-- The module comparison of the image of an identity of `Pic_{X/B}` is that of the identity of
`Coh_{X/B}`. -/
theorem picardToCoherentHom_id_fibre (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    (A : PicardObject D.toPicardSituation) :
    HEq (picardToCoherentHom D hflat hproper
        (PicardHom.id (modulePushforwardCoherence B S hS) A)).fibre
      (CoherentHom.id (modulePushforwardCoherence B S hS)
        (picardObjectToCoherent D hflat hproper A)).fibre := by
  have h₁ : (PicardHom.id (modulePushforwardCoherence B S hS) A).fibre =
      (baseChangeIdComparison (modulePushforwardCoherence B S hS) D.f A.T).hom.app
        A.lineBundle :=
    NatTrans.congr_app (congrArg Iso.hom
      (CoherentSituation.baseChangeIdComparison_toPicardSituation D _ A.T)) A.lineBundle
  exact (heq_of_eq h₁).trans (CoherentHom.id_fibre_heq _
    (picardObjectToCoherent D hflat hproper A) A.T A.lineBundle rfl HEq.rfl).symm

/-- The identity of `Pic_{X/B}` goes to the identity of `Coh_{X/B}`. -/
theorem picardToCoherentHom_id (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) (A : PicardObject D.toPicardSituation) :
    picardToCoherentHom D hflat hproper (PicardHom.id (modulePushforwardCoherence B S hS) A) =
      CoherentHom.id (modulePushforwardCoherence B S hS)
        (picardObjectToCoherent D hflat hproper A) :=
  CoherentHom.ext rfl ((Category.id_comp _).trans
    (eq_of_heq (picardToCoherentHom_id_fibre D hflat hproper A)))

/-- The module comparison of the image of a composite of `Pic_{X/B}` is that of the composite of
the images in `Coh_{X/B}`. -/
theorem picardToCoherentHom_comp_fibre (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    {A C E : PicardObject D.toPicardSituation} (m : PicardHom A C) (n : PicardHom C E) :
    HEq (picardToCoherentHom D hflat hproper (PicardHom.comp m n)).fibre
      (CoherentHom.comp (picardToCoherentHom D hflat hproper m)
        (picardToCoherentHom D hflat hproper n)).fibre := by
  have h₁ : (PicardHom.comp m n).fibre =
      Functor.fibreComp (baseChangeCompComparison D.f m.base n.base) m.fibre n.fibre :=
    congrArg (fun τ => Functor.fibreComp τ m.fibre n.fibre)
      (CoherentSituation.baseChangeCompComparison_toPicardSituation D m.base n.base)
  exact (heq_of_eq h₁).trans (CoherentHom.comp_fibre_heq (picardToCoherentHom D hflat hproper m)
    (picardToCoherentHom D hflat hproper n) m.base n.base A.lineBundle
    C.lineBundle E.lineBundle m.fibre n.fibre rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    HEq.rfl HEq.rfl HEq.rfl).symm

/-- The composite in `Pic_{X/B}` goes to the composite in `Coh_{X/B}`. -/
theorem picardToCoherentHom_comp (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) {A C E : PicardObject D.toPicardSituation}
    (m : PicardHom A C) (n : PicardHom C E) :
    picardToCoherentHom D hflat hproper (PicardHom.comp m n) =
      CoherentHom.comp (picardToCoherentHom D hflat hproper m)
        (picardToCoherentHom D hflat hproper n) :=
  CoherentHom.ext rfl ((Category.id_comp _).trans
    (eq_of_heq (picardToCoherentHom_comp_fibre D hflat hproper m n)))

/-- The natural map `Pic_{X/B} ⟶ Coh_{X/B}` as a functor over the big fppf site of `S`: a triple
`(T, g, L)` goes to the same triple and a morphism `(h, α)` to the same pair. -/
def picardToCoherentBased (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) :
    picardBasedCategory (modulePushforwardCoherence B S hS) D.toPicardSituation ⥤ᵇ
      coherentBasedCategory D.categoryData where
  toFunctor :=
    letI : Category.{u + 1} (PicardObject D.toPicardSituation) :=
      picardCategory (modulePushforwardCoherence B S hS) D.toPicardSituation
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    { obj := fun A => picardObjectToCoherent D hflat hproper A
      map := fun m => picardToCoherentHom D hflat hproper m
      map_id := fun A => picardToCoherentHom_id D hflat hproper A
      map_comp := fun m n => picardToCoherentHom_comp D hflat hproper m n }
  w := rfl

/-- The natural map is fully faithful: on hom-sets it is the bijection
`AlgebraicGeometry.Space.picardToCoherentHomEquiv`. -/
def picardToCoherentBasedFullyFaithful (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom) :
    (picardToCoherentBased D hflat hproper).toFunctor.FullyFaithful where
  preimage {A C} m := (picardToCoherentHomEquiv D hflat hproper A C).symm m
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- The natural map `Pic_{X/B} ⟶ Coh_{X/B}` as a 1-morphism of categories fibred in groupoids
over the big fppf site of `S`. -/
@[stacks 0D03 "the natural map Picardstack_{X/B} -> Cohstack_{X/B} as a 1-morphism of categories \
fibred in groupoids, (T, g, L) going to (T, g, L), for f flat and proper, f of finite presentation \
being part of the standing data D of Situation 08KB"]
def picardToCoherent (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) :
    picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation ⟶ coherentCFG D :=
  Bicategory.InducedBicategory.mkHom (picardToCoherentBased D hflat hproper)

/-! ### The hard inclusion of the base-change clause of Stacks 0CZT at rank one -/

/-- A module isomorphic to an invertible module is invertible. -/
theorem isInvertibleModule_of_iso {Z : AlgebraicSpaces B S hS}
    {L L' : Modules.{u, u} B S hS Z.1 Z.2} (e : L ≅ L') (hL : IsInvertibleModule Z L) :
    IsInvertibleModule Z L' := by
  refine (isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one L').2
    (isFiniteLocallyFreeOfRank_one_of_forall_mem_etaleRankOneFreeLocus B S hS L' fun x => ?_)
  obtain ⟨V, a, hae, hx, ⟨f⟩⟩ := mem_etaleRankOneFreeLocus_of_isInvertibleModule Z L hL x
  exact ⟨V, a, hae, hx, ⟨(modulePullback B S hS a).mapIso e.symm ≪≫ f⟩⟩

/-- **A free module on the small étale site with an invertible inverse image near a point has
rank one there.**  Let `a : V ⟶ X` and `b : V₁ ⟶ X` be morphisms of algebraic spaces whose images
on points meet, with `a^* F` free on some index type `I` and `b^* F` invertible.  Then `I` has
exactly one element, so that `a^* F ≅ 𝒪_V`. -/
theorem nonempty_iso_unit_of_iso_free_of_isInvertibleModule {X V V₁ : AlgebraicSpaces B S hS}
    (a : V ⟶ X) (b : V₁ ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2) (I : Type u)
    (e : (modulePullback B S hS a).obj F ≅ SheafOfModules.free
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O) I)
    (hb : IsInvertibleModule V₁ ((modulePullback B S hS b).obj F))
    (v : points B S hS V.1) (v₁ : points B S hS V₁.1)
    (hv : pointsMap B S hS V.1 a.hom v = pointsMap B S hS V₁.1 b.hom v₁) :
    Nonempty ((modulePullback B S hS a).obj F ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O)) := by
  classical
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS a b
  obtain ⟨w, -, -⟩ := exists_points_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS sq) v v₁ hv
  obtain ⟨wbar, -⟩ := exists_geometricRepresentative B S hS
    (AlgebraicSpaces.fiberProduct B S hS a b).1 w
  have hP := modulePullbackInvertible
    (ObjectProperty.homMk (pullback.snd a.hom b.hom) :
      AlgebraicSpaces.fiberProduct B S hS a b ⟶ V₁) _ hb
  obtain ⟨ι, ⟨hι⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofan_of_iso_free
    (modulePullbackFiberProductFreeIso B S hS b a F I e).symm
  obtain ⟨hI⟩ := nonempty_unique_of_isColimit_cofan_of_isInvertibleModule B S hS
    (AlgebraicSpaces.fiberProduct B S hS a b) wbar _ I ι hι hP
  obtain ⟨κ, ⟨hκ⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofan_of_iso_free e.symm
  have hc : IsColimit (Cofan.mk (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O))
      (fun _ : I => 𝟙 _)) := by
    refine Cofan.IsColimit.mk _ (fun s => s.inj default) ?_ ?_
    · intro s j
      obtain rfl : j = default := Subsingleton.elim _ _
      exact Category.id_comp _
    · intro s m hm
      exact (Category.id_comp m).symm.trans (hm default)
  exact ⟨hκ.coconePointUniqueUpToIso hc⟩


/-- **The base-change clause of Stacks 0CZT, at rank one.**  If the pullback `F_{T'}` of an
object `F` of `Coh_{X/Y}` along `X_g : X_{T'} ⟶ X_T` is invertible, then `X_g` maps every point of
`|X_{T'}|` into the rank-one étale free locus of `F`. -/
theorem mem_etaleRankOneFreeLocus_of_isInvertibleModule_modulePullback
    (D : CoherentSituation B S hS) {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hqc : F.IsQuasicoherentOnSite) (hfp : F.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (D.space T).2 (D.projection T).hom F)
    (hF : IsInvertibleModule (D.space T') ((modulePullback B S hS (D.relativeMap g)).obj F))
    (x' : points B S hS (D.space T').1) :
    pointsMap B S hS (D.space T').1 (D.relativeMap g).hom x' ∈
      etaleRankOneFreeLocus B S hS F := by
  obtain ⟨V, a, hae, ⟨v, hv⟩, hfree⟩ :=
    range_pointsMap_relativeMap_subset_etaleFreeLocus_of_isInvertibleModule D g F hqc hfp hflat hF
      ⟨x', rfl⟩
  obtain ⟨I, ⟨e⟩⟩ := exists_iso_free_of_isFreeModule B S hS V _ hfree
  obtain ⟨V₁, b, -, ⟨v₁, hv₁⟩, -⟩ :=
    mem_etaleRankOneFreeLocus_of_isInvertibleModule (D.space T') _ hF x'
  have hb : IsInvertibleModule V₁ ((modulePullback B S hS (b ≫ D.relativeMap g)).obj F) :=
    isInvertibleModule_of_iso ((modulePullbackCompIso B S hS b (D.relativeMap g)).app F)
      (modulePullbackInvertible b _ hF)
  have hv' : pointsMap B S hS V.1 a.hom v =
      pointsMap B S hS V₁.1 (b ≫ D.relativeMap g).hom v₁ := by
    rw [hv, ObjectProperty.FullSubcategory.comp_hom, pointsMap_comp, Function.comp_apply, hv₁]
  obtain ⟨e'⟩ := nonempty_iso_unit_of_iso_free_of_isInvertibleModule a (b ≫ D.relativeMap g) F I
    e hb v v₁ hv'
  exact ⟨V, a, hae, ⟨v, hv⟩, ⟨e'⟩⟩

/-- If the pullback `F_{T'}` of an object `F` of `Coh_{X/Y}` along `X_g : X_{T'} ⟶ X_T` is
invertible, then `|T'|` maps into `U = T ∖ f_T(|X_T| ∖ W₁)`. -/
@[stacks 0D03 "part two of the proof, the implication (b) => (a) complete, at the source's own U = \
T \\ f_T(|X_T| \\ W_1) and the source's own condition (b): if F_T' is invertible then |T'| maps \
into U. The hypotheses on F are 0CZT's own three conditions, which an object of Coh_{X/Y} has."]
theorem range_subset_fibrewiseEtaleRankOneFreeLocus_of_isInvertibleModule
    (D : CoherentSituation B S hS) {T' T : SchemesOver D.Y} (g : T' ⟶ T)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hqc : F.IsQuasicoherentOnSite) (hfp : F.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS (D.space T).2 (D.projection T).hom F)
    (hF : IsInvertibleModule (D.space T') ((modulePullback B S hS (D.relativeMap g)).obj F)) :
    Set.range (pointsMap B S hS ((schemeSpaceFunctor B S hS).obj T'.left).1
        ((schemeSpaceFunctor B S hS).map g.left).hom) ⊆
      fibrewiseEtaleRankOneFreeLocus D T F := by
  rintro t ⟨t', rfl⟩
  rw [mem_fibrewiseEtaleRankOneFreeLocus_iff]
  intro x hx
  obtain ⟨x', hx', -⟩ := exists_point_of_isPullback B S hS (isPullback_baseChangeMap D.f g)
    x t' hx
  rw [← hx']
  exact mem_etaleRankOneFreeLocus_of_isInvertibleModule_modulePullback D g F hqc hfp hflat hF x'

/-! ### The open locus -/

/-- **A morphism into an open subscheme of the base is a factorization on points.**  An object
`T` of the big fppf site of a scheme `S` maps to the open subscheme `O ⊆ S`, as an object of
that site, exactly when the image of its structure morphism lies in `O`. -/
theorem nonempty_hom_opensObj_iff {S : Scheme.{u}} (hS : B.Contains S)
    (T : BigFppfOver B S hS) (O : S.Opens) :
    Nonempty (T ⟶ BigFppfOver.opensObj B S hS O) ↔ Set.range T.hom.hom ⊆ (O : Set S) := by
  constructor
  · rintro ⟨g⟩
    have hw : T.hom.hom = g.left.hom ≫ O.ι := by
      rw [← BigFppfOver.opensObj_hom_hom B S hS O, ← ObjectProperty.FullSubcategory.comp_hom,
        Over.w g]
    rw [hw, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (Set.image_subset_range _ _).trans (by rw [Scheme.Opens.range_ι])
  · intro h
    have h' : Set.range T.hom.hom ⊆ Set.range O.ι := by rwa [Scheme.Opens.range_ι]
    exact ⟨Over.homMk (ObjectProperty.homMk (IsOpenImmersion.lift O.ι T.hom.hom h'))
      (ObjectProperty.hom_ext _ (IsOpenImmersion.lift_fac O.ι T.hom.hom h'))⟩

/-- Along a morphism of `Coh_{X/Y}`, the module of the source is invertible exactly when the
pullback of the module of the target is. -/
private theorem isInvertibleModule_iff_pullback_of_coherentHom {D : CoherentSituation B S hS}
    {A C : CoherentObject D} (m : CoherentHom A C) :
    IsInvertibleModule (D.space A.T) A.F ↔
      IsInvertibleModule (D.space A.T) ((modulePullback B S hS (D.relativeMap m.base)).obj C.F) :=
  haveI := m.isIso_fibre
  ⟨fun h => isInvertibleModule_of_iso (asIso m.fibre).symm h,
    fun h => isInvertibleModule_of_iso (asIso m.fibre) h⟩

/-- **The image of the base change of the natural map along a point of `Coh_{X/Y}`.**  An object
`T` of the big fppf site of `U` is in the image of the first projection of the 2-fibre product of
`Pic_{X/Y} ⟶ Coh_{X/Y}` with a scheme-valued point `y` exactly when the module of `y(T)` is
invertible. -/
theorem exists_twoFibreProductFst_picardToCoherent_iff (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ (coherentBasedCategory D.categoryData).obj)
    (hy : y ⋙ (coherentBasedCategory D.categoryData).p = Over.map U.hom)
    (T : BigFppfOver B U.left.1 U.left.2) :
    (∃ a, (TwoFibreProductOver.fst (Over.map U.hom)
        (picardBasedCategory (modulePushforwardCoherence B S hS) D.toPicardSituation).p
        (coherentBasedCategory D.categoryData).p y
        (picardToCoherentBased D hflat hproper).toFunctor).obj a = T) ↔
      IsInvertibleModule (D.space (CoherentObject.T (y.obj T))) (CoherentObject.F (y.obj T)) := by
  constructor
  · rintro ⟨a, rfl⟩
    let m : CoherentHom (D := D) (y.obj a.x) (picardObjectToCoherent D hflat hproper a.y) :=
      a.iso.hom
    exact (isInvertibleModule_iff_pullback_of_coherentHom m).2
      (modulePullbackInvertible (D.relativeMap m.base) _ a.y.invertible)
  · intro hT
    let P : PicardObject D.toPicardSituation :=
      ⟨CoherentObject.T (y.obj T), CoherentObject.F (y.obj T), hT⟩
    exact ⟨{ base := (coherentBasedCategory D.categoryData).p.obj (y.obj T)
             x := T
             y := P
             hx := (Functor.congr_obj hy T).symm
             hy := rfl
             iso := Iso.refl (y.obj T)
             vertical := IsHomLift.id rfl }, rfl⟩

/-- Transporting a morphism of schemes along equalities of its source and target does not change
which subsets its image lies in, up to the transport of the subset. -/
theorem range_subset_iff_of_eq_eqToHom {X X' Y Y' : Scheme.{u}} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (f' : X' ⟶ Y') (hf : f = eqToHom hX ≫ f' ≫ eqToHom hY.symm) (O : Set Y) :
    Set.range f ⊆ O ↔ Set.range f' ⊆ (eqToHom hY.symm).base ⁻¹' O := by
  subst hX hY
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst hf
  rfl

/-- **The open locus of the natural map.**  For every scheme-valued point `y` of `Coh_{X/Y}`
over an object `U` of the big fppf site of `S`, there is an open subscheme `V ⊆ U` through which
an object `T` of the big fppf site of `U` factors exactly when `y(T)` comes from `Pic_{X/Y}`. -/
@[stacks 0D03 "part two of the proof, the open subscheme U of every object (T, g, F) of \
Cohstack_{X/B}, read on scheme-valued points: an object over the base factors through U exactly \
when its image comes from Picardstack_{X/B}"]
theorem hasOpenLocus_picardToCoherent (D : CoherentSituation B S hS)
    (hflat : IsFlat B S hS D.f.hom) (hproper : IsProper B S hS D.f.hom) :
    Stack.HasOpenLocus B S hS (picardToCoherentBased D hflat hproper) := by
  intro U y hy
  let U₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 _)
  let A : CoherentObject D := y.obj U₀
  let Ω := fibrewiseEtaleRankOneFreeLocus D A.T A.F
  have hΩ : IsOpen Ω := isOpen_fibrewiseEtaleRankOneFreeLocus D hproper A.T A.F
  let O : Set ((BigFppfOver.toScheme B S hS).obj A.T.left) :=
    pointsToScheme B S hS A.T.left '' Ω
  have hO : IsOpen O := (schemePointsHomeomorph B S hS A.T.left).isOpenMap Ω hΩ
  have hA : (BigFppfOver.toScheme B S hS).obj A.T.left =
      (BigFppfOver.toScheme B S hS).obj ((Over.map U.hom).obj U₀) :=
    congrArg (BigFppfOver.toScheme B S hS).obj (Functor.congr_obj hy U₀)
  let e₀ : (BigFppfOver.toScheme B S hS).obj ((Over.map U.hom).obj U₀) ⟶
      (BigFppfOver.toScheme B S hS).obj A.T.left := eqToHom hA.symm
  let O' : U.left.1.Opens := ⟨e₀.base ⁻¹' O, hO.preimage e₀.base.hom.continuous⟩
  refine ⟨BigFppfOver.opensObj B U.left.1 U.left.2 O', ?_, fun T => ?_⟩
  · rw [BigFppfOver.opensObj_hom_hom]
    infer_instance
  · rw [nonempty_hom_opensObj_iff, exists_twoFibreProductFst_picardToCoherent_iff D hflat hproper
      U y hy T]
    let t : T ⟶ U₀ := Over.homMk T.hom (Category.comp_id _)
    let m : CoherentHom (D := D) (y.obj T) A := y.map t
    rw [isInvertibleModule_iff_pullback_of_coherentHom m]
    have h₂ : IsInvertibleModule (D.space (CoherentObject.T (y.obj T)))
          ((modulePullback B S hS (D.relativeMap m.base)).obj A.F) ↔
        Set.range (pointsMap B S hS
          ((schemeSpaceFunctor B S hS).obj (CoherentObject.T (y.obj T)).left).1
          ((schemeSpaceFunctor B S hS).map m.base.left).hom) ⊆ Ω :=
      ⟨range_subset_fibrewiseEtaleRankOneFreeLocus_of_isInvertibleModule D m.base A.F
        A.quasicoherent A.finitePresentation A.flat,
        isInvertibleModule_modulePullback_relativeMap_of_subset_fibrewiseEtaleRankOneFreeLocus D
          m.base A.F⟩
    rw [h₂]
    show _ ↔ Set.range (pointsMap B S hS (yoneda.obj (CoherentObject.T (y.obj T)).left)
      (yoneda.map m.base.left)) ⊆ Ω
    rw [range_pointsMap_yoneda_subset_iff B S hS m.base.left Ω]
    have h₃ := congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) (Functor.congr_hom hy t)
    simp only [Functor.map_comp, eqToHom_map] at h₃
    exact (range_subset_iff_of_eq_eqToHom _ hA _ _ h₃ O).symm

/-! ### Stacks 0D03 -/

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is flat, of finite
presentation and proper, given by the data `D` of Situation 08KB with `hflat` and `hproper`.  The
natural map `Pic_{X/B} ⟶ Coh_{X/B}` is representable by open immersions: it is representable by
algebraic spaces (Stacks 02ZW), and every algebraic space representing its base change along a
scheme-valued point of `Coh_{X/B}` is an open subspace of that scheme (Stacks 04XB at open
immersions). -/
@[stacks 0D03 "the whole statement: the natural map Picardstack_{X/B} -> Cohstack_{X/B}, for f \
flat, of finite presentation (the standing data D of Situation 08KB) and proper, is representable \
by algebraic spaces and an open immersion in the sense of Tag 04XB, which together are \
representability by open immersions (Tag 04YL (1))"]
theorem isRepresentableByAlgebraicSpaces_and_isOpenImmersion_picardToCoherent
    (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS (picardToCoherent D hflat hproper).hom ∧
      Stack.IsOpenImmersion B S hS (picardToCoherent D hflat hproper) :=
  (Stack.isOpenImmersion_and_isRepresentableByAlgebraicSpaces_of_hasOpenLocus B S hS
    (picardToCoherent D hflat hproper)
    (picardToCoherentBasedFullyFaithful D hflat hproper).full
    (picardToCoherentBasedFullyFaithful D hflat hproper).faithful
    (hasOpenLocus_picardToCoherent D hflat hproper)).symm

end AlgebraicGeometry.Space

end
