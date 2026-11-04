module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.QuasiFiniteRepresentableULift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.InvariantOpen
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAmalgamation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtlasCriterionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.CategoryTheory.Sites.FamilyImageSieve
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedRefinable

/-!
# The covering of a fibre product of two points of a formal algebraic space by its atlas

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` with atlas `{X_i ⟶ X}`, and let `α : h_U^# ⟶ X` and `β : h_V^# ⟶ X` be two scheme-valued
points of it. The base change of `h_U^# ×_X h_V^#` along an arrow of the atlas is
`(h_U^# ×_X X_i) ×_{X_i} (h_V^# ×_X X_i)`, an object of the site. Affine charts of these base
changes glue to one object of the site, and from it the fibre product `h_U^# ×_X h_V^#` is
represented by an object of the site with a locally quasi-finite monomorphism to `U ⨯ V`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.FibreProductChart`: an affine chart of `h_U^# ×_X h_V^#` over
  `U ⨯ V`.

## Main results

* `AlgebraicGeometry.FormalSpace.etale_snd_of_relativelyRepresentable_atlas`: the projection
  `h_U^# ×_X X_i ⟶ h_U^#` is étale as a morphism of schemes.
* `AlgebraicGeometry.FormalSpace.etale_prodMap`: a product of two étale morphisms of the site
  is étale on underlying schemes.
* `AlgebraicGeometry.FormalSpace.exists_isPullback_locallyQuasiFinite_of_atlas`: the base
  change of `h_U^# ×_X h_V^# ⟶ X` along an arrow of the atlas is represented by an object `W`
  of the site, and `W ⟶ U ⨯ V` is locally of finite type and locally quasi-finite.
* `AlgebraicGeometry.FormalSpace.exists_mem_sieve_point`: a covering sieve of the big fppf
  site over `S` contains a morphism hitting a given point of its target.
* `AlgebraicGeometry.FormalSpace.exists_factorization_through_point_sheafifiedYoneda`: every
  point of a site object carrying a scheme-valued point of `X` lies in the image of a site
  object over which that point factors through one member of the atlas.
* `AlgebraicGeometry.FormalSpace.exists_affineOpen_site_object`: an affine open neighbourhood
  of a point of an object of the site is again an object of the site, of no larger size.
* `AlgebraicGeometry.FormalSpace.exists_affine_chart_of_covering_member`: the affine chart of
  the covering at a point of one of its members, with its morphism to `U ⨯ V` locally of
  finite type and locally quasi-finite and of size at most that of `U ⨯ V`.
* `AlgebraicGeometry.FormalSpace.mem_range_toScheme_pullback_snd_iff`: the base change of a
  morphism of the site is surjective exactly over the points whose image the morphism hits.
* `AlgebraicGeometry.FormalSpace.exists_covering_member_point_of_isFormalAlgebraicSpace`: the
  members of the covering jointly hit every point of `U ⨯ V` that carries a point of
  `h_U^# ×_X h_V^#`.
* `AlgebraicGeometry.FormalSpace.exists_isPullback_etale_of_covering_member`,
  `…exists_isPullback_etale_of_openImmersion_comp` and `…exists_isPullback_etale_of_affine_chart`:
  the base change of a member of the covering, or of an affine chart inside one, along a point
  of the fibre product is étale on schemes.
* `AlgebraicGeometry.FormalSpace.exists_fibreProductChart`: there is a chart through every
  point of `U ⨯ V` that carries a point of the fibre product.
* `AlgebraicGeometry.FormalSpace.contains_sigma_fibreProductChart`: the coproduct of a family
  of charts indexed injectively by the points of `U ⨯ V` is an object of the site.
* `AlgebraicGeometry.FormalSpace.sheaf_hom_ext_of_openCover`: two morphisms of fppf sheaves out
  of a sheafified representable agreeing on each member of a jointly surjective family of open
  immersions are equal.
* `AlgebraicGeometry.FormalSpace.exists_glued_atlas_of_fibreProductCharts`: the charts glue to
  one object of the site, with one point of the fibre product and one morphism to `U ⨯ V`.
* `AlgebraicGeometry.FormalSpace.exists_toProd_of_point` and
  `…isPullback_glued_baseChange`: a point of the fibre product comes from a morphism of the
  site to `U ⨯ V`, and the base change of the glued point along it is computed in `U ⨯ V`.
* `AlgebraicGeometry.FormalSpace.surjective_toScheme_pullback_snd_of_mem_range` and
  `…etale_toScheme_pullback_snd_of_glued_atlas`: the base change of the glued point is
  surjective and étale.
* `AlgebraicGeometry.FormalSpace.locallyQuasiFinite_toScheme_map_glued`: the glued morphism to
  `U ⨯ V` is locally of finite type and locally quasi-finite.
* `AlgebraicGeometry.FormalSpace.relative_surjective_etale_of_glued`: the glued point is
  surjective and étale relative to the sheafified Yoneda embedding.
* `AlgebraicGeometry.FormalSpace.small_pullback_of_points`: the fibre product of two
  scheme-valued points of an fppf sheaf has pointwise `u`-small sections.
* `AlgebraicGeometry.FormalSpace.exists_representing_object_of_glued`: given the glued atlas,
  the fibre product is represented by an object of the site, by a locally quasi-finite
  monomorphism to `U ⨯ V`.
* `AlgebraicGeometry.FormalSpace.exists_fibreProduct_representing_object`: the fibre product
  of two scheme-valued points of a formal algebraic space is represented by an object of the
  site, by a locally quasi-finite monomorphism to the product of the two sources.

## References

* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AI8](https://stacks.math.columbia.edu/tag/0AI8)
* [Stacks Project, Tag 0BGQ](https://stacks.math.columbia.edu/tag/0BGQ)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
* [Stacks Project, Tag 0CB7](https://stacks.math.columbia.edu/tag/0CB7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The forgetful functor from the site to schemes preserves pullbacks. -/
private instance preservesLimitsOfShape_toScheme_walkingCospan :
    PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
  dsimp [BigFppfOver.toScheme]
  infer_instance

/-- The topology of the site is subcanonical. -/
private instance subcanonical_topology_bigFppfOver : (BigFppfOver.topology B S hS).Subcanonical :=
  bigFppfOver_subcanonical B S hS

/-- The sheafified Yoneda embedding of the site is full. -/
private instance full_sheafifiedYoneda :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Full :=
  (sheafifiedYonedaFF B S hS).full

/-- The sheafified Yoneda embedding of the site is faithful. -/
private instance faithful_sheafifiedYoneda :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Faithful :=
  (sheafifiedYonedaFF B S hS).faithful

/-- The sheafified Yoneda embedding of the site preserves limits of every shape. -/
private instance preservesLimitsOfShape_sheafifiedYoneda {K : Type} [Category.{0} K] :
    PreservesLimitsOfShape K (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
  preservesLimitsOfShape_of_natIso
    (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS)).symm

/-- If an arrow `fi : Xi ⟶ X` of fppf sheaves is representable by algebraic spaces,
étale in the sense of `AlgebraicGeometry.Space.HasPropertyULift`, and representable by objects
of the site, then for every point `α` of `X` over an object `U` the object of the site
representing `h_U^# ×_X Xi` is étale over `U`. -/
theorem etale_snd_of_relativelyRepresentable_atlas
    {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) fi.hom hrep)
    (hR : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable fi)
    (U : BigFppfOver B S hS)
    (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (hR.snd α)) := by
  let J := BigFppfOver.topology B S hS
  let L := sheafToPresheaf J (Type (u + 1))
  let e := sheafifiedYonedaCompForgetIso' B S hS
  let ξ : (uliftYoneda.{u + 1}).obj U ⟶ X.obj := (e.app U).inv ≫ α.hom
  have hsq : IsPullback ((e.app (hR.pullback α)).inv ≫ (hR.fst α).hom)
      ((uliftYoneda.{u + 1}).map (hR.snd α)) fi.hom ξ := by
    refine ((hR.isPullback α).map L).of_iso (e.app (hR.pullback α)) (Iso.refl _) (e.app U)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [L, Iso.refl_hom, Category.comp_id]
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rfl
    · exact e.hom.naturality (hR.snd α)
    · simp only [L, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simp only [L, ξ, Iso.refl_hom, Category.comp_id]
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rfl
  let i : (uliftYoneda.{u + 1}).obj (hR.pullback α) ≅ pullback ξ fi.hom :=
    hsq.flip.isoIsPullback _ _ (IsPullback.of_hasPullback ξ fi.hom)
  rw [← Space.isEtaleULift_uliftYoneda_map_iff.{u + 1} B S hS (hR.snd α)]
  exact isEtaleULift_of_iso_source B S hS i (hsq.flip.isoIsPullback_hom_fst _ _ _) (het U ξ)

/-- A product of two morphisms of the site which are étale on underlying schemes is étale on
underlying schemes. -/
theorem etale_prodMap {U U' V V' : BigFppfOver B S hS} (g : U' ⟶ U) (h : V' ⟶ V)
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g))
    (hh : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h)) :
    letI : HasBinaryProducts (BigFppfOver B S hS) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (Limits.prod.map g h)) := by
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  have hsplit : Limits.prod.map g h =
      Limits.prod.map g (𝟙 V') ≫ Limits.prod.map (𝟙 U) h := by simp
  have h1 : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (Limits.prod.map g (𝟙 V'))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Etale.{u})
      ((Limits.isPullback_prodMap_id g V').flip.map (BigFppfOver.toScheme B S hS)) hg
  have h2 : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (Limits.prod.map (𝟙 U) h)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Etale.{u})
      ((Limits.isPullback_id_prodMap h U).flip.map (BigFppfOver.toScheme B S hS)) hh
  rw [hsplit, Functor.map_comp]
  have _ := h1
  have _ := h2
  infer_instance


/-- Let `fi : Xi ⟶ X` be an arrow of fppf sheaves with `Xi` an affine formal algebraic space,
representable by algebraic spaces, étale, and representable by objects of the site, and let
`α`, `β` be two scheme-valued points of `X`. Then the base change of `h_U^# ×_X h_V^# ⟶ X`
along `fi` is represented by an object `W` of the site, and the induced morphism
`W ⟶ U ⨯ V` is locally of finite type and locally quasi-finite. -/
theorem exists_isPullback_locallyQuasiFinite_of_atlas
    {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hXi : IsAffineFormalAlgebraicSpace B S hS Xi)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) fi.hom hrep)
    (hR : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable fi)
    (U V : BigFppfOver B S hS)
    (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
    (β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X) :
    ∃ (W : BigFppfOver B S hS) (q : W ⟶ U ⨯ V)
      (ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ pullback α β)
      (σ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ Xi),
      IsPullback ι σ (pullback.fst α β ≫ α) fi ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (q ≫ Limits.prod.fst) =
        ι ≫ pullback.fst α β ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (q ≫ Limits.prod.snd) =
        ι ≫ pullback.snd α β ∧
      AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q) ∧
      AlgebraicGeometry.LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map q) := by
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let sU : hR.pullback α ⟶ U := hR.snd α
  let sV : hR.pullback β ⟶ V := hR.snd β
  let tU : F.obj (hR.pullback α) ⟶ Xi := hR.fst α
  let tV : F.obj (hR.pullback β) ⟶ Xi := hR.fst β
  let jU : F.obj (hR.pullback α) ≅ pullback α fi :=
    (hR.isPullback α).flip.isoIsPullback _ _ (IsPullback.of_hasPullback α fi)
  let jV : F.obj (hR.pullback β) ≅ pullback β fi :=
    (hR.isPullback β).flip.isoIsPullback _ _ (IsPullback.of_hasPullback β fi)
  have hjU1 : jU.hom ≫ pullback.fst α fi = F.map sU :=
    (hR.isPullback α).flip.isoIsPullback_hom_fst _ _ _
  have hjU2 : jU.hom ≫ pullback.snd α fi = tU :=
    (hR.isPullback α).flip.isoIsPullback_hom_snd _ _ _
  have hjV1 : jV.hom ≫ pullback.fst β fi = F.map sV :=
    (hR.isPullback β).flip.isoIsPullback_hom_fst _ _ _
  have hjV2 : jV.hom ≫ pullback.snd β fi = tV :=
    (hR.isPullback β).flip.isoIsPullback_hom_snd _ _ _
  obtain ⟨W, iW, w, hw1, hw2, hwci⟩ :=
    exists_isPullback_isClosedImmersion_of_isAffineFormal B S hS hXi
      (hR.pullback α) (hR.pullback β) tU tV
  have hk : IsPullback (pullback.fst tU tV ≫ jU.hom) (pullback.snd tU tV ≫ jV.hom)
      (pullback.snd α fi) (pullback.snd β fi) :=
    (IsPullback.of_hasPullback tU tV).of_iso (Iso.refl _) jU jV (Iso.refl _)
      (by simp) (by simp) (by simpa using hjU2.symm) (by simpa using hjV2.symm)
  let k : pullback tU tV ≅ pullback (pullback.snd α fi) (pullback.snd β fi) :=
    hk.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)
  have hk1 : k.hom ≫ pullback.fst (pullback.snd α fi) (pullback.snd β fi) =
      pullback.fst tU tV ≫ jU.hom := hk.isoIsPullback_hom_fst _ _ _
  have hk2 : k.hom ≫ pullback.snd (pullback.snd α fi) (pullback.snd β fi) =
      pullback.snd tU tV ≫ jV.hom := hk.isoIsPullback_hom_snd _ _ _
  have _ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map w) := hwci
  have _ : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (Limits.prod.map sU sV)) :=
    etale_prodMap B S hS sU sV
      (etale_snd_of_relativelyRepresentable_atlas B S hS fi hrep het hR U α)
      (etale_snd_of_relativelyRepresentable_atlas B S hS fi hrep het hR V β)
  refine ⟨W, w ≫ Limits.prod.map sU sV,
    iW.hom ≫ k.hom ≫ MorphismProperty.pullbackBaseChangeComparison α β fi,
    iW.hom ≫ k.hom ≫ pullback.fst (pullback.snd α fi) (pullback.snd β fi) ≫
      pullback.snd α fi, ?_, ?_, ?_, ?_, ?_⟩
  · refine (MorphismProperty.isPullback_pullbackBaseChangeComparison α β fi).of_iso
      (iW ≪≫ k).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp) <;>
    simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.trans_inv, Category.assoc,
      Iso.inv_hom_id_assoc]
  · have hA : k.hom ≫ MorphismProperty.pullbackBaseChangeComparison α β fi ≫
        pullback.fst α β = pullback.fst tU tV ≫ F.map sU := by
      rw [MorphismProperty.pullbackBaseChangeComparison_fst, ← Category.assoc, hk1,
        Category.assoc, hjU1]
    have hB : F.map ((w ≫ Limits.prod.map sU sV) ≫ Limits.prod.fst) =
        iW.hom ≫ pullback.fst tU tV ≫ F.map sU := by
      rw [Category.assoc, Limits.prod.map_fst, ← Category.assoc, F.map_comp, hw1,
        Category.assoc]
    rw [hB, Category.assoc, Category.assoc, hA]
  · have hA : k.hom ≫ MorphismProperty.pullbackBaseChangeComparison α β fi ≫
        pullback.snd α β = pullback.snd tU tV ≫ F.map sV := by
      rw [MorphismProperty.pullbackBaseChangeComparison_snd, ← Category.assoc, hk2,
        Category.assoc, hjV1]
    have hB : F.map ((w ≫ Limits.prod.map sU sV) ≫ Limits.prod.snd) =
        iW.hom ≫ pullback.snd tU tV ≫ F.map sV := by
      rw [Category.assoc, Limits.prod.map_snd, ← Category.assoc, F.map_comp, hw2,
        Category.assoc]
    rw [hB, Category.assoc, Category.assoc, hA]
  all_goals rw [Functor.map_comp]; infer_instance

/-! ### Local factorization of a scheme-valued point of `X` through the atlas -/

/-- A covering sieve of the big fppf site over `S` contains a morphism hitting a given point of
its target. -/
theorem exists_mem_sieve_point {a : BigFppfOver B S hS} {R : Sieve a}
    (hR : R ∈ BigFppfOver.topology B S hS a)
    (x : (BigFppfOver.toScheme B S hS).obj a) :
    ∃ (T : BigFppfOver B S hS) (b : T ⟶ a) (y : (BigFppfOver.toScheme B S hS).obj T),
      R b ∧ (BigFppfOver.toScheme B S hS).map b y = x := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨E, hE, hER⟩ := CategoryTheory.exists_covering_refining_sieve B.IsCovering
    B.precoverage (fun ⟨E, hEq, hE⟩ => ⟨E, hE, hEq⟩) B.coverings_isSite hR
  have hEF := B.isFppfCovering_of_isCovering hE
  rw [IsFppfCovering, Precoverage.mem_comap_iff, PreZeroHypercover.presieve₀,
    Presieve.map_ofArrows, Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
  obtain ⟨j, y, hy⟩ := hEF.1 x
  exact ⟨Over.mk (E.f j ≫ a.hom), Over.homMk (E.f j), y,
    (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨j⟩), hy⟩

/-- Every point of a site object carrying a scheme-valued point of `X` lies in the image of a
site object over which that point factors through one member `f i` of a locally surjective
family `f`. -/
theorem exists_factorization_through_point_sheafifiedYoneda
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X : FppfSheaf B S hS} {I : Type (u + 1)} (Xi : I → FppfSheaf B S hS)
    (f : ∀ i, Xi i ⟶ X)
    (hcover : Sheaf.IsLocallySurjective (Limits.Sigma.desc f))
    (a : BigFppfOver B S hS)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj a ⟶ X)
    (x : (BigFppfOver.toScheme B S hS).obj a) :
    ∃ (i : I) (T : BigFppfOver B S hS) (b : T ⟶ a)
      (m : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ Xi i)
      (y : (BigFppfOver.toScheme B S hS).obj T),
      m ≫ f i = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b ≫ g ∧
        (BigFppfOver.toScheme B S hS).map b y = x := by
  classical
  let J := BigFppfOver.topology B S hS
  let e := sheafifiedYonedaCompForgetIso' B S hS
  let k : (uliftYoneda.{u + 1}).obj a ⟶ X.obj := (e.app a).inv ≫ g.hom
  have hmem := Sheaf.iSup_imageSieve_mem_of_isLocallySurjective_sigmaDesc J Xi X f hcover a
    (uliftYonedaEquiv k)
  obtain ⟨T, b, y, hb, hy⟩ := exists_mem_sieve_point B S hS hmem x
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
  obtain ⟨-, ⟨i, rfl⟩, z, hz⟩ := hb
  have hm' : uliftYonedaEquiv.symm z ≫ (f i).hom = (uliftYoneda.{u + 1}).map b ≫ k := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} k b.op)
  refine ⟨i, T, b, ⟨(e.app T).hom ≫ uliftYonedaEquiv.symm z⟩, y, ?_, hy⟩
  apply Sheaf.hom_ext
  show ((e.app T).hom ≫ uliftYonedaEquiv.symm z) ≫ (f i).hom =
    ((Sheaf.sheafifiedYoneda J).map b).hom ≫ g.hom
  rw [Category.assoc, hm', ← Category.assoc]
  have hnat : (e.app T).hom ≫ (uliftYoneda.{u + 1}).map b =
      ((Sheaf.sheafifiedYoneda J).map b).hom ≫ (e.app a).hom := (e.hom.naturality b).symm
  rw [hnat, Category.assoc]
  simp only [k]
  rw [Iso.hom_inv_id_assoc]

/-! ### Affine charts of an object of the site -/

/-- A point of an object `W` of the site has an affine open neighbourhood which is again an
object of the site, of size at most that of `W`. -/
theorem exists_affineOpen_site_object (W : BigFppfOver B S hS)
    (t : (BigFppfOver.toScheme B S hS).obj W) :
    ∃ (A : BigFppfOver B S hS) (j : A ⟶ W),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      t ∈ Set.range ((BigFppfOver.toScheme B S hS).map j) ∧
      ((BigFppfOver.toScheme B S hS).obj A).size ≤
        ((BigFppfOver.toScheme B S hS).obj W).size := by
  obtain ⟨O, hOaff, htO, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (X := (BigFppfOver.toScheme B S hS).obj W) (x := t) (U := ⊤) trivial
  have hsize : (↑O : Scheme.{u}).size ≤ ((BigFppfOver.toScheme B S hS).obj W).size :=
    Scheme.size_coe_opens_le _ O
  refine ⟨BigFppfOver.mk B S hS (hsize.trans_lt W.left.property)
      (O.ι ≫ B.inclusion.map W.hom),
    Over.homMk (ObjectProperty.homMk O.ι) (by apply ObjectProperty.hom_ext; rfl),
    hOaff, ?_, ⟨⟨t, htO⟩, rfl⟩, hsize⟩
  show AlgebraicGeometry.IsOpenImmersion O.ι
  infer_instance

/-- Given a member `W` of the covering of `h_U^# ×_X h_V^#`, as produced by
`AlgebraicGeometry.FormalSpace.exists_isPullback_locallyQuasiFinite_of_atlas`, and a point `t`
of `W`, there is an affine open neighbourhood `C` of `t` in `W` which is an object of the site
whose morphism to `U ⨯ V` is locally of finite type and locally quasi-finite, hits the image of
`t`, and has size at most that of `U ⨯ V`. -/
theorem exists_affine_chart_of_covering_member
    {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    {α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X}
    {β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    (W : BigFppfOver B S hS) (q : W ⟶ U ⨯ V)
    (ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ pullback α β)
    (hq₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (q ≫ Limits.prod.fst) =
      ι ≫ pullback.fst α β)
    (hq₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (q ≫ Limits.prod.snd) =
      ι ≫ pullback.snd α β)
    (hlft : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q))
    (hlqf : AlgebraicGeometry.LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map q))
    (t : (BigFppfOver.toScheme B S hS).obj W) :
    ∃ (C : BigFppfOver B S hS) (c : C ⟶ U ⨯ V) (j : C ⟶ W),
      IsAffine ((BigFppfOver.toScheme B S hS).obj C) ∧
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      j ≫ q = c ∧
      (BigFppfOver.toScheme B S hS).map q t ∈
        Set.range ((BigFppfOver.toScheme B S hS).map c) ∧
      ((BigFppfOver.toScheme B S hS).obj C).size ≤
        ((BigFppfOver.toScheme B S hS).obj (U ⨯ V)).size ∧
      AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c) ∧
      AlgebraicGeometry.LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map c) ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (c ≫ Limits.prod.fst) =
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map j ≫ ι) ≫
          pullback.fst α β ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (c ≫ Limits.prod.snd) =
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map j ≫ ι) ≫
          pullback.snd α β := by
  obtain ⟨C, j, hCaff, hjoi, htj, -⟩ := exists_affineOpen_site_object B S hS W t
  have _ := hCaff
  have _ : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) := hjoi
  have _ : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q) := hlft
  have hclft : AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (j ≫ q)) := by
    rw [Functor.map_comp]
    infer_instance
  have _ := hclft
  have _ : AlgebraicGeometry.LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map q) := hlqf
  have hclqf : AlgebraicGeometry.LocallyQuasiFinite
      ((BigFppfOver.toScheme B S hS).map (j ≫ q)) := by
    rw [Functor.map_comp]
    infer_instance
  have _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj C) := inferInstance
  refine ⟨C, j ≫ q, j, hCaff, hjoi, rfl, ?_, ?_, hclft, hclqf, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := htj
    refine ⟨s, ?_⟩
    rw [Functor.map_comp]
    show (BigFppfOver.toScheme B S hS).map q
      ((BigFppfOver.toScheme B S hS).map j s) = _
    rw [hs]
  · exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (j ≫ q))
  · rw [Category.assoc j, Functor.map_comp, hq₁, Category.assoc]
  · rw [Category.assoc j, Functor.map_comp, hq₂, Category.assoc]

/-! ### Base change of a chart along a point of the site -/

/-- A point `t` of `T` lies in the image of the base change of `c` along `b` if and only if
its image under `b` lies in the image of `c`. -/
theorem mem_range_toScheme_pullback_snd_iff {A T Z : BigFppfOver B S hS}
    (c : A ⟶ Z) (b : T ⟶ Z) (t : (BigFppfOver.toScheme B S hS).obj T) :
    t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (pullback.snd c b)) ↔
      (BigFppfOver.toScheme B S hS).map b t ∈
        Set.range ((BigFppfOver.toScheme B S hS).map c) := by
  have hpb := (IsPullback.of_hasPullback c b).map (BigFppfOver.toScheme B S hS)
  have hsnd : hpb.isoPullback.hom ≫
      pullback.snd ((BigFppfOver.toScheme B S hS).map c)
        ((BigFppfOver.toScheme B S hS).map b) =
      (BigFppfOver.toScheme B S hS).map (pullback.snd c b) := hpb.isoPullback_hom_snd
  have hsndapp : ∀ y, pullback.snd ((BigFppfOver.toScheme B S hS).map c)
      ((BigFppfOver.toScheme B S hS).map b) (hpb.isoPullback.hom y) =
      (BigFppfOver.toScheme B S hS).map (pullback.snd c b) y := by
    intro y
    rw [← Scheme.Hom.comp_apply, hsnd]
  have hr : Set.range ((BigFppfOver.toScheme B S hS).map (pullback.snd c b)) =
      Set.range (pullback.snd ((BigFppfOver.toScheme B S hS).map c)
        ((BigFppfOver.toScheme B S hS).map b)) := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro _ ⟨s, rfl⟩
      exact ⟨hpb.isoPullback.hom s, hsndapp s⟩
    · rintro _ ⟨s, rfl⟩
      refine ⟨hpb.isoPullback.inv s, ?_⟩
      have hid : hpb.isoPullback.hom (hpb.isoPullback.inv s) = s := by
        rw [← Scheme.Hom.comp_apply, hpb.isoPullback.inv_hom_id]
        rfl
      rw [← hsndapp (hpb.isoPullback.inv s), hid]
  rw [hr, Scheme.Pullback.range_snd]
  rfl

/-- If `ι : h_W^# ⟶ P` is a base change of an atlas arrow `fi : Xi ⟶ X` along a morphism
`h : P ⟶ X`, then for every point `x : h_T^# ⟶ P` the base change of `ι` along `x` is
represented by an object of the site which is étale over `T`. -/
theorem exists_isPullback_etale_of_covering_member
    {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) fi.hom hrep)
    (hR : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable fi)
    {P : FppfSheaf B S hS} (h : P ⟶ X) {W : BigFppfOver B S hS}
    {ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ P}
    {σ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ Xi}
    (hsq : IsPullback ι σ h fi) (T : BigFppfOver B S hS)
    (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ P) :
    ∃ (Vb : BigFppfOver B S hS) (p : Vb ⟶ T)
      (r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Vb ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W),
      IsPullback r ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p) ι x ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p) := by
  have hcomm : (((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (hR.snd (x ≫ h))) ≫ x) ≫ h = hR.fst (x ≫ h) ≫ fi := by
    rw [Category.assoc]
    exact (hR.isPullback (x ≫ h)).w.symm
  refine ⟨hR.pullback (x ≫ h), hR.snd (x ≫ h),
    hsq.lift (((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      (hR.snd (x ≫ h))) ≫ x) (hR.fst (x ≫ h)) hcomm, ?_,
    etale_snd_of_relativelyRepresentable_atlas B S hS fi hrep het hR T (x ≫ h)⟩
  refine IsPullback.of_right ?_ (hsq.lift_fst _ _ _) hsq.flip
  rw [hsq.lift_snd]
  exact hR.isPullback (x ≫ h)

/-- If the base change of `ι : h_W^# ⟶ P` along every point of `P` is represented by an
object of the site étale over the test object, then so is the base change of `h_C^# ⟶ h_W^# ⟶ P`
for an open immersion `j : C ⟶ W` of the site. -/
theorem exists_isPullback_etale_of_openImmersion_comp
    {P : FppfSheaf B S hS} {W C : BigFppfOver B S hS}
    {ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ P} (j : C ⟶ W)
    (hj : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (hetι : ∀ (T : BigFppfOver B S hS)
      (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ P),
      ∃ (Vb : BigFppfOver B S hS) (p : Vb ⟶ T)
        (r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Vb ⟶
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W),
        IsPullback r ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p) ι x ∧
        AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p))
    (T : BigFppfOver B S hS)
    (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ P) :
    ∃ (Vb : BigFppfOver B S hS) (p : Vb ⟶ T)
      (r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Vb ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj C),
      IsPullback r ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map j ≫ ι) x ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p) := by
  let J := BigFppfOver.topology B S hS
  obtain ⟨Vb₀, p₀, r₀, hpb₀, hp₀⟩ := hetι T x
  let F := Sheaf.sheafifiedYoneda J
  let r₀' : Vb₀ ⟶ W := F.preimage r₀
  have hr₀' : F.map r₀' = r₀ := F.map_preimage r₀
  have hupper : IsPullback (F.map (pullback.fst j r₀')) (F.map (pullback.snd j r₀'))
      (F.map j) r₀ := by
    rw [← hr₀']
    exact (IsPullback.of_hasPullback j r₀').map F
  refine ⟨pullback j r₀', pullback.snd j r₀' ≫ p₀, F.map (pullback.fst j r₀'), ?_, ?_⟩
  · rw [F.map_comp]
    exact hupper.paste_vert hpb₀
  · rw [Functor.map_comp]
    have _ : AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (pullback.snd j r₀')) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @AlgebraicGeometry.IsOpenImmersion.{u})
        ((IsPullback.of_hasPullback j r₀').map (BigFppfOver.toScheme B S hS)) hj
    have _ := hp₀
    infer_instance

/-- If `ι : h_W^# ⟶ P` is a base change of an atlas arrow `fi : Xi ⟶ X` and `j : C ⟶ W` is
an open immersion of the site, then for every point `x : h_T^# ⟶ P` the base change of
`h_C^# ⟶ h_W^# ⟶ P` along `x` is represented by an object of the site which is étale over
`T`. -/
theorem exists_isPullback_etale_of_affine_chart
    {X Xi : FppfSheaf B S hS} (fi : Xi ⟶ X)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS fi.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) fi.hom hrep)
    (hR : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable fi)
    {P : FppfSheaf B S hS} (h : P ⟶ X) {W : BigFppfOver B S hS}
    {ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ P}
    {σ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ Xi}
    (hsq : IsPullback ι σ h fi) {C : BigFppfOver B S hS} (j : C ⟶ W)
    (hj : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (T : BigFppfOver B S hS)
    (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ P) :
    ∃ (Vb : BigFppfOver B S hS) (p : Vb ⟶ T)
      (r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Vb ⟶
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj C),
      IsPullback r ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map j ≫ ι) x ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p) :=
  exists_isPullback_etale_of_openImmersion_comp B S hS j hj
    (fun T' x' => exists_isPullback_etale_of_covering_member B S hS fi hrep het hR h hsq T' x')
    T x

/-- For a site object `T`, a point `x` of `h_U^# ×_X h_V^#` over `T` recorded by
`b : T ⟶ U ⨯ V`, and a point `t` of `T`, some member `W` of the covering of the fibre product
by the atlas has a point over the image of `t` in `U ⨯ V`. -/
theorem exists_covering_member_point_of_isFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (U V : BigFppfOver B S hS)
    (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
    (β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X)
    (T : BigFppfOver B S hS)
    (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ pullback α β)
    (b : T ⟶ U ⨯ V)
    (hb₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.fst) =
      x ≫ pullback.fst α β)
    (hb₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.snd) =
      x ≫ pullback.snd α β)
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (W : BigFppfOver B S hS) (q : W ⟶ U ⨯ V)
      (ι : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ pullback α β)
      (w : (BigFppfOver.toScheme B S hS).obj W),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (q ≫ Limits.prod.fst) =
        ι ≫ pullback.fst α β ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (q ≫ Limits.prod.snd) =
        ι ≫ pullback.snd α β ∧
      AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q) ∧
      AlgebraicGeometry.LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map q) ∧
      (BigFppfOver.toScheme B S hS).map q w = (BigFppfOver.toScheme B S hS).map b t ∧
      (∀ (T' : BigFppfOver B S hS)
        (x' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T' ⟶ pullback α β),
        ∃ (Vb : BigFppfOver B S hS) (p : Vb ⟶ T')
          (r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Vb ⟶
            (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W),
          IsPullback r ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p) ι x' ∧
          AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p)) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let ρ := MorphismProperty.monoPullbackToProd F α β
  have hb : F.map b = x ≫ ρ :=
    MorphismProperty.map_eq_comp_monoPullbackToProd F α β x b hb₁ hb₂
  obtain ⟨-, I, Xi, f, hXiaff, hfi, hcover⟩ := id hX
  obtain ⟨i, T', b', m, t', hm, hy⟩ :=
    exists_factorization_through_point_sheafifiedYoneda B S hS Xi f hcover T
      (x ≫ (pullback.fst α β ≫ α)) t
  obtain ⟨hrep, het⟩ := hfi i
  have hRi := relativelyRepresentable_atlas_of_isFormalAlgebraicSpace B S hS hX Xi f hXiaff hfi i
  obtain ⟨W, q, ι, σ, hsq, hq₁, hq₂, hlft, hlqf⟩ :=
    exists_isPullback_locallyQuasiFinite_of_atlas B S hS (f i) (hXiaff i) hrep het hRi U V α β
  have hqρ : F.map q = ι ≫ ρ :=
    MorphismProperty.map_eq_comp_monoPullbackToProd F α β ι q hq₁ hq₂
  have hcomm : (F.map b' ≫ x) ≫ (pullback.fst α β ≫ α) = m ≫ f i := by
    rw [Category.assoc]
    exact hm.symm
  let k : T' ⟶ W := F.preimage (hsq.lift (F.map b' ≫ x) m hcomm)
  have hk : F.map k ≫ ι = F.map b' ≫ x := by
    rw [F.map_preimage]
    exact hsq.lift_fst _ _ _
  have hkq : k ≫ q = b' ≫ b := by
    apply F.map_injective
    rw [F.map_comp, F.map_comp, hqρ, ← Category.assoc, hk, Category.assoc, hb,
      ← Category.assoc]
  refine ⟨W, q, ι, (BigFppfOver.toScheme B S hS).map k t', hq₁, hq₂, hlft, hlqf, ?_,
    fun T' x' => exists_isPullback_etale_of_covering_member B S hS (f i) hrep het hRi
      (pullback.fst α β ≫ α) hsq T' x'⟩
  have h₁ : (BigFppfOver.toScheme B S hS).map (k ≫ q) t' =
      (BigFppfOver.toScheme B S hS).map (b' ≫ b) t' := by rw [hkq]
  rw [Functor.map_comp, Functor.map_comp] at h₁
  rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply, hy]


/-! ### The chart data and its coproduct -/

/-- An affine chart of the fibre product `h_U^# ×_X h_V^#` over `U ⨯ V`: an affine object of
the site with a morphism to `U ⨯ V` and a point of the fibre product, compatible with the two
projections, locally of finite type and locally quasi-finite over `U ⨯ V`, of size at most
that of `U ⨯ V`, and whose base changes along points of the site are étale. -/
structure FibreProductChart {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
    (β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X) where
  /-- The underlying object of the site. -/
  obj : BigFppfOver B S hS
  /-- Its morphism to the product of the two test objects. -/
  toProd : obj ⟶ U ⨯ V
  /-- Its point of the fibre product. -/
  point : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj obj ⟶ pullback α β
  /-- The chart is affine. -/
  isAffine : IsAffine ((BigFppfOver.toScheme B S hS).obj obj)
  /-- The first component of `toProd` is the first projection of the point. -/
  fst_eq : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
    (toProd ≫ Limits.prod.fst) = point ≫ pullback.fst α β
  /-- The second component of `toProd` is the second projection of the point. -/
  snd_eq : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
    (toProd ≫ Limits.prod.snd) = point ≫ pullback.snd α β
  /-- `toProd` is locally of finite type. -/
  locallyOfFiniteType : AlgebraicGeometry.LocallyOfFiniteType
    ((BigFppfOver.toScheme B S hS).map toProd)
  /-- `toProd` is locally quasi-finite. -/
  locallyQuasiFinite : AlgebraicGeometry.LocallyQuasiFinite
    ((BigFppfOver.toScheme B S hS).map toProd)
  /-- The chart is no larger than `U ⨯ V`. -/
  size_le : ((BigFppfOver.toScheme B S hS).obj obj).size ≤
    ((BigFppfOver.toScheme B S hS).obj (U ⨯ V)).size
  /-- Every base change of the point along a point of the site is étale. -/
  etale_baseChange : ∀ (T : BigFppfOver B S hS)
      (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ pullback α β),
      ∃ (Vb : BigFppfOver B S hS) (p : Vb ⟶ T)
        (r : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Vb ⟶
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj obj),
        IsPullback r ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p) point x ∧
        AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p)

/-- There is a chart of the fibre product through every point of `U ⨯ V` that carries a point
of the fibre product. -/
theorem exists_fibreProductChart
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {U V : BigFppfOver B S hS}
    (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
    (β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X)
    (T : BigFppfOver B S hS)
    (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ pullback α β)
    (b : T ⟶ U ⨯ V)
    (hb₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.fst) =
      x ≫ pullback.fst α β)
    (hb₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.snd) =
      x ≫ pullback.snd α β)
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ ch : FibreProductChart B S hS α β,
      (BigFppfOver.toScheme B S hS).map b t ∈
        Set.range ((BigFppfOver.toScheme B S hS).map ch.toProd) := by
  obtain ⟨W, q, ι, w, hq₁, hq₂, hlft, hlqf, hqw, hetι⟩ :=
    exists_covering_member_point_of_isFormalAlgebraicSpace B S hS hX U V α β T x b hb₁ hb₂ t
  obtain ⟨C, c, j, hCaff, hjoi, hjq, hmem, hsize, hclft, hclqf, hc₁, hc₂⟩ :=
    exists_affine_chart_of_covering_member B S hS W q ι hq₁ hq₂ hlft hlqf w
  refine ⟨⟨C, c, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map j ≫ ι, hCaff, hc₁,
    hc₂, hclft, hclqf, hsize, ?_⟩, ?_⟩
  · exact exists_isPullback_etale_of_openImmersion_comp B S hS j hjoi hetι
  · rw [← hqw]
    exact hmem

/-- The coproduct of a family of charts indexed injectively by the points of `U ⨯ V` is an
object of the site. -/
theorem contains_sigma_fibreProductChart
    {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    {α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X}
    {β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    {K : Type u} (e : K → (BigFppfOver.toScheme B S hS).obj (U ⨯ V))
    (he : Function.Injective e) (ch : K → FibreProductChart B S hS α β) :
    B.Contains (∐ fun k => (BigFppfOver.toScheme B S hS).obj (ch k).obj) := by
  refine lt_of_le_of_lt (schemeSize_coproduct_le _
    (2 ^ ((BigFppfOver.toScheme B S hS).obj (U ⨯ V)).size)
    ((Scheme.aleph0_le_size _).trans (Cardinal.cantor _).le)
    ((Cardinal.mk_le_of_injective he).trans (Scheme.mk_le_two_pow_size _))
    (fun k => ((ch k).size_le).trans (Cardinal.cantor _).le)) ?_
  exact B.cutoff_isStrongPrelimit (U ⨯ V).left.property

/-! ### Glueing the charts -/

/-- Two morphisms of fppf sheaves out of a sheafified representable agreeing on each member of
a jointly surjective family of open immersions are equal. -/
theorem sheaf_hom_ext_of_openCover {Y : FppfSheaf B S hS} {W : BigFppfOver B S hS}
    {K : Type u} (Vk : K → BigFppfOver B S hS) (kk : ∀ k, Vk k ⟶ W)
    (hk : ∀ k, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (kk k)))
    (hcov : ∀ z : (BigFppfOver.toScheme B S hS).obj W,
      ∃ k, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (kk k)))
    {g g' : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ Y}
    (h : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (kk k) ≫ g =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (kk k) ≫ g') :
    g = g' := by
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let e := sheafifiedYonedaCompForgetIso' B S hS
  apply Sheaf.hom_ext
  have hcancel : ∀ p q : (F.obj W).obj ⟶ Y.obj,
      (e.app W).inv ≫ p = (e.app W).inv ≫ q → p = q := fun p q hpq =>
    (cancel_epi (e.app W).inv).mp hpq
  refine hcancel _ _ (Space.hom_ext_of_openCover B S hS Y Vk kk hk hcov (fun k => ?_))
  have hnat0 : (F.map (kk k)).hom ≫ (e.app W).hom =
      (e.app (Vk k)).hom ≫ (uliftYoneda.{u + 1}).map (kk k) := e.hom.naturality (kk k)
  have hnat : (uliftYoneda.{u + 1}).map (kk k) ≫ (e.app W).inv =
      (e.app (Vk k)).inv ≫ (F.map (kk k)).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hnat0, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hstep : ∀ z : F.obj W ⟶ Y, (uliftYoneda.{u + 1}).map (kk k) ≫ (e.app W).inv ≫ z.hom =
      (e.app (Vk k)).inv ≫ (F.map (kk k) ≫ z).hom := by
    intro z
    rw [← Category.assoc, hnat, Category.assoc]
    rfl
  rw [hstep g, hstep g', h k]

/-- A family of charts indexed injectively by the points of `U ⨯ V` glues to one object `W'`
of the site, covered by the charts through a jointly surjective family of open immersions, with
one point `Q` of the fibre product and one morphism `w'` to `U ⨯ V` restricting to the chart
points and the chart morphisms. -/
theorem exists_glued_atlas_of_fibreProductCharts
    {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    {α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X}
    {β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    {K : Type u} (e₀ : K → (BigFppfOver.toScheme B S hS).obj (U ⨯ V))
    (he₀ : Function.Injective e₀) (ch : K → FibreProductChart B S hS α β) :
    ∃ (W' : BigFppfOver B S hS) (kk : ∀ k, (ch k).obj ⟶ W')
      (Q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W' ⟶ pullback α β)
      (w' : W' ⟶ U ⨯ V),
      (∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (kk k) ≫ Q =
        (ch k).point) ∧
      (∀ k, kk k ≫ w' = (ch k).toProd) ∧
      (∀ k, AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (kk k))) ∧
      (∀ z : (BigFppfOver.toScheme B S hS).obj W',
        ∃ k, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (kk k))) ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (w' ≫ Limits.prod.fst) =
        Q ≫ pullback.fst α β ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (w' ≫ Limits.prod.snd) =
        Q ≫ pullback.snd α β := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let e := sheafifiedYonedaCompForgetIso' B S hS
  let : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).Full :=
    (ULiftYoneda.fullyFaithful _).full
  let : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).Faithful :=
    (ULiftYoneda.fullyFaithful _).faithful
  obtain ⟨W', kk, qP, hqP, hkOI, hkcov, hkdisj⟩ :=
    Space.exists_map_from_coproduct B S hS (pullback α β) (fun k => (ch k).obj)
      (fun k => (e.app (ch k).obj).inv ≫ ((ch k).point).hom)
      (contains_sigma_fibreProductChart B S hS e₀ he₀ ch)
  let Q : F.obj W' ⟶ pullback α β := ⟨(e.app W').hom ≫ qP⟩
  have hQ : ∀ k, F.map (kk k) ≫ Q = (ch k).point := by
    intro k
    apply Sheaf.hom_ext
    show (F.map (kk k)).hom ≫ (e.app W').hom ≫ qP = ((ch k).point).hom
    have hnat0 : (F.map (kk k)).hom ≫ (e.app W').hom =
        (e.app (ch k).obj).hom ≫ (uliftYoneda.{u + 1}).map (kk k) := e.hom.naturality (kk k)
    rw [← Category.assoc, hnat0, Category.assoc, hqP k, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  obtain ⟨wq, hwq⟩ := Space.exists_amalgamation_of_disjoint_openCover B S hS
    ⟨(uliftYoneda.{u + 1}).obj (U ⨯ V),
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS (U ⨯ V)).isSheaf⟩
    (fun k => (ch k).obj) kk hkOI hkcov hkdisj
    (fun k => (uliftYoneda.{u + 1}).map ((ch k).toProd))
  let w' : W' ⟶ U ⨯ V := (uliftYoneda.{u + 1}).preimage wq
  have hw' : ∀ k, kk k ≫ w' = (ch k).toProd := by
    intro k
    apply (uliftYoneda.{u + 1}).map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact hwq k
  refine ⟨W', kk, Q, w', hQ, hw', hkOI, hkcov, ?_, ?_⟩
  · refine sheaf_hom_ext_of_openCover B S hS (fun k => (ch k).obj) kk hkOI hkcov (fun k => ?_)
    rw [← Functor.map_comp, ← Category.assoc (kk k), hw' k, (ch k).fst_eq, ← Category.assoc,
      hQ k]
  · refine sheaf_hom_ext_of_openCover B S hS (fun k => (ch k).obj) kk hkOI hkcov (fun k => ?_)
    rw [← Functor.map_comp, ← Category.assoc (kk k), hw' k, (ch k).snd_eq, ← Category.assoc,
      hQ k]

/-! ### The base change of the glued atlas -/

/-- A point of the fibre product `h_U^# ×_X h_V^#` over a site object `T` is recorded by a
morphism of the site `T ⟶ U ⨯ V`. -/
theorem exists_toProd_of_point {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
    (β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X)
    (T : BigFppfOver B S hS)
    (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ pullback α β) :
    ∃ b : T ⟶ U ⨯ V,
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.fst) =
        x ≫ pullback.fst α β ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.snd) =
        x ≫ pullback.snd α β := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let ρ := MorphismProperty.monoPullbackToProd F α β
  refine ⟨F.preimage (x ≫ ρ), ?_, ?_⟩
  · rw [F.map_comp, F.map_preimage, Category.assoc,
      MorphismProperty.monoPullbackToProd_comp_map_fst]
  · rw [F.map_comp, F.map_preimage, Category.assoc,
      MorphismProperty.monoPullbackToProd_comp_map_snd]

/-- The fibre product of the glued point `Q` with a point `x` of the fibre product is the
fibre product over `U ⨯ V` of the two morphisms of the site recording them. -/
theorem isPullback_glued_baseChange {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    {α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X}
    {β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    {W' : BigFppfOver B S hS}
    {Q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W' ⟶ pullback α β}
    (w' : W' ⟶ U ⨯ V)
    (hw₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (w' ≫ Limits.prod.fst) =
      Q ≫ pullback.fst α β)
    (hw₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (w' ≫ Limits.prod.snd) =
      Q ≫ pullback.snd α β)
    {T : BigFppfOver B S hS}
    {x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ pullback α β}
    (b : T ⟶ U ⨯ V)
    (hb₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.fst) =
      x ≫ pullback.fst α β)
    (hb₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.snd) =
      x ≫ pullback.snd α β) :
    IsPullback ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (pullback.fst w' b))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (pullback.snd w' b)) Q x := by
  let J := BigFppfOver.topology B S hS
  exact MorphismProperty.isPullback_map_pullback_of_mono (Sheaf.sheafifiedYoneda J)
    (MorphismProperty.monoPullbackToProd (Sheaf.sheafifiedYoneda J) α β) Q x w' b
    (MorphismProperty.map_eq_comp_monoPullbackToProd _ α β Q w' hw₁ hw₂)
    (MorphismProperty.map_eq_comp_monoPullbackToProd _ α β x b hb₁ hb₂)

/-! ### Surjectivity and étaleness of the glued atlas -/

/-- The base change of `c` along `b` is surjective if `b` maps every point into the image of
`c`. -/
theorem surjective_toScheme_pullback_snd_of_mem_range {A T Z : BigFppfOver B S hS}
    (c : A ⟶ Z) (b : T ⟶ Z)
    (h : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      (BigFppfOver.toScheme B S hS).map b t ∈
        Set.range ((BigFppfOver.toScheme B S hS).map c)) :
    AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map (pullback.snd c b)) :=
  ⟨fun t => (mem_range_toScheme_pullback_snd_iff B S hS c b t).mpr (h t)⟩

/-- The base change of the glued point along a point of the fibre product is étale. -/
theorem etale_toScheme_pullback_snd_of_glued_atlas
    {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    {α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X}
    {β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    {K : Type u} (ch : K → FibreProductChart B S hS α β)
    {W' : BigFppfOver B S hS} (kk : ∀ k, (ch k).obj ⟶ W')
    {Q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W' ⟶ pullback α β}
    (w' : W' ⟶ U ⨯ V)
    (hQ : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (kk k) ≫ Q =
      (ch k).point)
    (hkOI : ∀ k, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (kk k)))
    (hkcov : ∀ z : (BigFppfOver.toScheme B S hS).obj W',
      ∃ k, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (kk k)))
    {T : BigFppfOver B S hS}
    {x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ pullback α β}
    (b : T ⟶ U ⨯ V)
    (hbig : IsPullback
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (pullback.fst w' b))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (pullback.snd w' b)) Q x) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (pullback.snd w' b)) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let pf : pullback w' b ⟶ W' := pullback.fst w' b
  have hjOI : ∀ k, AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (pullback.snd (kk k) pf)) := fun k =>
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.IsOpenImmersion.{u})
      ((IsPullback.of_hasPullback (kk k) pf).map (BigFppfOver.toScheme B S hS)) (hkOI k)
  have hjcov : ∀ z : (BigFppfOver.toScheme B S hS).obj (pullback w' b),
      ∃ k, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (pullback.snd (kk k) pf)) := by
    intro z
    obtain ⟨k, hk⟩ := hkcov ((BigFppfOver.toScheme B S hS).map pf z)
    exact ⟨k, (mem_range_toScheme_pullback_snd_iff B S hS (kk k) pf z).mpr hk⟩
  have hetale : ∀ k, AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (kk k) pf ≫ pullback.snd w' b)) := by
    intro k
    have hupper : IsPullback (F.map (pullback.fst (kk k) pf)) (F.map (pullback.snd (kk k) pf))
        (F.map (kk k)) (F.map pf) := (IsPullback.of_hasPullback (kk k) pf).map F
    have hpaste : IsPullback (F.map (pullback.fst (kk k) pf))
        (F.map (pullback.snd (kk k) pf ≫ pullback.snd w' b)) (ch k).point x := by
      rw [F.map_comp, ← hQ k]
      exact hupper.paste_vert hbig
    obtain ⟨Vb, p₀, r₀, hpb₀, het₀⟩ := (ch k).etale_baseChange T x
    let ε := hpaste.isoIsPullback _ _ hpb₀
    have hε : ε.hom ≫ F.map p₀ =
        F.map (pullback.snd (kk k) pf ≫ pullback.snd w' b) :=
      hpaste.isoIsPullback_hom_snd _ _ hpb₀
    let εs : pullback (kk k) pf ⟶ Vb := F.preimage ε.hom
    have hεs : F.map εs = ε.hom := F.map_preimage _
    have _ : IsIso (F.map εs) := by
      rw [hεs]
      infer_instance
    have _ : IsIso εs := (sheafifiedYonedaFF B S hS).isIso_of_isIso_map εs
    have hfac : pullback.snd (kk k) pf ≫ pullback.snd w' b = εs ≫ p₀ := by
      apply F.map_injective
      rw [F.map_comp εs p₀, hεs, hε]
    rw [hfac, Functor.map_comp]
    have _ : IsIso ((BigFppfOver.toScheme B S hS).map εs) := inferInstance
    have _ := het₀
    infer_instance
  have _ : IsZariskiLocalAtSource (@AlgebraicGeometry.Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Etale.{u})
  let DW : ((BigFppfOver.toScheme B S hS).obj (pullback w' b)).OpenCover :=
    { I₀ := K
      X := fun k => (BigFppfOver.toScheme B S hS).obj (pullback (kk k) pf)
      f := fun k => (BigFppfOver.toScheme B S hS).map (pullback.snd (kk k) pf)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hjcov, hjOI⟩ }
  refine IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.Etale.{u}) DW (fun k => ?_)
  rw [show DW.f k = (BigFppfOver.toScheme B S hS).map (pullback.snd (kk k) pf) from rfl,
    ← Functor.map_comp]
  exact hetale k

/-- The glued morphism to `U ⨯ V` is locally of finite type and locally quasi-finite. -/
theorem locallyQuasiFinite_toScheme_map_glued
    {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    {α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X}
    {β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    {K : Type u} (ch : K → FibreProductChart B S hS α β)
    {W' : BigFppfOver B S hS} (kk : ∀ k, (ch k).obj ⟶ W') (w' : W' ⟶ U ⨯ V)
    (hw' : ∀ k, kk k ≫ w' = (ch k).toProd)
    (hkOI : ∀ k, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (kk k)))
    (hkcov : ∀ z : (BigFppfOver.toScheme B S hS).obj W',
      ∃ k, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (kk k))) :
    AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w') ∧
      AlgebraicGeometry.LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map w') := by
  let DW : ((BigFppfOver.toScheme B S hS).obj W').OpenCover :=
    { I₀ := K
      X := fun k => (BigFppfOver.toScheme B S hS).obj (ch k).obj
      f := fun k => (BigFppfOver.toScheme B S hS).map (kk k)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hkcov, hkOI⟩ }
  have : IsZariskiLocalAtSource (@AlgebraicGeometry.LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @AlgebraicGeometry.LocallyOfFiniteType.{u})
  have : IsZariskiLocalAtSource (@AlgebraicGeometry.LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @AlgebraicGeometry.LocallyQuasiFinite.{u})
  constructor
  · refine IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.LocallyOfFiniteType.{u})
      DW (fun k => ?_)
    rw [show DW.f k = (BigFppfOver.toScheme B S hS).map (kk k) from rfl, ← Functor.map_comp,
      hw' k]
    exact (ch k).locallyOfFiniteType
  · refine IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.LocallyQuasiFinite.{u})
      DW (fun k => ?_)
    rw [show DW.f k = (BigFppfOver.toScheme B S hS).map (kk k) from rfl, ← Functor.map_comp,
      hw' k]
    exact (ch k).locallyQuasiFinite

/-- The glued point is surjective and étale relative to the sheafified Yoneda embedding. -/
theorem relative_surjective_etale_of_glued
    {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    {α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X}
    {β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    {K : Type u} (ch : K → FibreProductChart B S hS α β)
    {W' : BigFppfOver B S hS} (kk : ∀ k, (ch k).obj ⟶ W')
    {Q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W' ⟶ pullback α β}
    (w' : W' ⟶ U ⨯ V)
    (hQ : ∀ k, (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (kk k) ≫ Q =
      (ch k).point)
    (hw₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (w' ≫ Limits.prod.fst) =
      Q ≫ pullback.fst α β)
    (hw₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (w' ≫ Limits.prod.snd) =
      Q ≫ pullback.snd α β)
    (hkOI : ∀ k, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (kk k)))
    (hkcov : ∀ z : (BigFppfOver.toScheme B S hS).obj W',
      ∃ k, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (kk k)))
    (hhit : ∀ (T : BigFppfOver B S hS)
      (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ pullback α β)
      (b : T ⟶ U ⨯ V),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.fst) =
        x ≫ pullback.fst α β →
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.snd) =
        x ≫ pullback.snd α β →
      ∀ t : (BigFppfOver.toScheme B S hS).obj T,
        (BigFppfOver.toScheme B S hS).map b t ∈
          Set.range ((BigFppfOver.toScheme B S hS).map w')) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
        (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) Q ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
        (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) Q := by
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  constructor
  · refine MorphismProperty.relative.of_exists fun T x => ?_
    obtain ⟨b, hb₁, hb₂⟩ := exists_toProd_of_point B S hS α β T x
    exact ⟨pullback w' b,
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (pullback.fst w' b),
      pullback.snd w' b,
      isPullback_glued_baseChange B S hS w' hw₁ hw₂ b hb₁ hb₂,
      surjective_toScheme_pullback_snd_of_mem_range B S hS w' b (hhit T x b hb₁ hb₂)⟩
  · refine MorphismProperty.relative.of_exists fun T x => ?_
    obtain ⟨b, hb₁, hb₂⟩ := exists_toProd_of_point B S hS α β T x
    exact ⟨pullback w' b,
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (pullback.fst w' b),
      pullback.snd w' b,
      isPullback_glued_baseChange B S hS w' hw₁ hw₂ b hb₁ hb₂,
      etale_toScheme_pullback_snd_of_glued_atlas B S hS ch kk w' hQ hkOI hkcov b
        (isPullback_glued_baseChange B S hS w' hw₁ hw₂ b hb₁ hb₂)⟩

/-! ### Descent of the fibre product to the value universe of the site -/

/-- The fibre product of two scheme-valued points of an fppf sheaf has pointwise `u`-small
sections. -/
theorem small_pullback_of_points {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
    (β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X) :
    FunctorToTypes.Small.{u} (pullback α β).obj := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let ρ := MorphismProperty.monoPullbackToProd F α β
  let e := sheafifiedYonedaCompForgetIso' B S hS
  have _ : Mono ρ := MorphismProperty.mono_monoPullbackToProd F α β
  have hmono : Mono ρ.hom :=
    (sheafToPresheaf J (Type (u + 1))).map_mono ρ
  intro T
  have h1 : Small.{u} (((uliftYoneda.{u + 1}).obj (U ⨯ V)).obj T) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (T.unop ⟶ U ⨯ V)))
  have h2 : Small.{u} ((F.obj (U ⨯ V)).obj.obj T) :=
    small_of_injective (CategoryTheory.injective_of_mono ((e.app (U ⨯ V)).hom.app T))
  have : Mono (ρ.hom.app T) := (NatTrans.mono_iff_mono_app _).mp hmono T
  exact small_of_injective (CategoryTheory.injective_of_mono (ρ.hom.app T))

/-- Given a point `Q` of the fibre product of two scheme-valued points of a formal algebraic
space over `W'` which is surjective and étale, and a morphism `w' : W' ⟶ U ⨯ V` compatible with
`Q` and locally of finite type, the fibre product is represented by an object of the site, by a
locally quasi-finite monomorphism to `U ⨯ V`. -/
theorem exists_representing_object_of_glued
    {X : FppfSheaf B S hS} {U V : BigFppfOver B S hS}
    {α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X}
    {β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    {W' : BigFppfOver B S hS}
    {Q : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W' ⟶ pullback α β}
    (w' : W' ⟶ U ⨯ V)
    (hw₁ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (w' ≫ Limits.prod.fst) =
      Q ≫ pullback.fst α β)
    (hw₂ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (w' ≫ Limits.prod.snd) =
      Q ≫ pullback.snd α β)
    (hsurjQ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) Q)
    (hetaleQ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) Q)
    (hlftw : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map w')) :
    ∃ (W : BigFppfOver B S hS)
      (i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ≅ pullback α β)
      (f : W ⟶ U ⨯ V),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (f ≫ Limits.prod.fst) =
        i.hom ≫ pullback.fst α β ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (f ≫ Limits.prod.snd) =
        i.hom ≫ pullback.snd α β ∧
      AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f) ∧
      AlgebraicGeometry.LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map f) ∧
      Mono ((BigFppfOver.toScheme B S hS).map f) := by
  classical
  let J := BigFppfOver.topology B S hS
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
    ⟨fun Z => by
      show AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (𝟙 Z))
      rw [CategoryTheory.Functor.map_id]
      infer_instance⟩
  let F := Sheaf.sheafifiedYoneda J
  let e := sheafifiedYonedaCompForgetIso' B S hS
  let ρ := MorphismProperty.monoPullbackToProd F α β
  let H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1, u}
  obtain ⟨P₀, hP₀, ⟨eP⟩⟩ := exists_comp_uliftFunctor_iso_of_small B S hS
    (small_pullback_of_points B S hS α β)
  let a : yoneda.obj W' ⟶ P₀ := H.preimage ((e.app W').inv ≫ Q.hom ≫ eP.inv)
  have ha : H.map a = (e.app W').inv ≫ Q.hom ≫ eP.inv := H.map_preimage _
  let m : P₀ ⟶ yoneda.obj (U ⨯ V) := H.preimage (eP.hom ≫ ρ.hom ≫ (e.app (U ⨯ V)).hom)
  have hm : H.map m = eP.hom ≫ ρ.hom ≫ (e.app (U ⨯ V)).hom := H.map_preimage _
  have hQhom : Q.hom = (e.app W').hom ≫ H.map a ≫ eP.hom := by
    rw [← Iso.inv_comp_eq, ha, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hcarry : ∀ (P : MorphismProperty (BigFppfOver B S hS)) (_ : P.RespectsIso),
      P.relative F Q → P.presheaf a := by
    intro P hP hPQ
    have := hP
    have h1 : P.relative (uliftYoneda.{u + 1}) Q.hom :=
      (relative_sheafifiedYoneda_iff_uliftYoneda' B S hS P Q).mp hPQ
    rw [hQhom] at h1
    have h2 := (MorphismProperty.cancel_left_of_respectsIso
      (P := P.relative (uliftYoneda.{u + 1} (C := BigFppfOver B S hS))) (e.app W').hom
      (H.map a ≫ eP.hom)).mp h1
    have h3 := (MorphismProperty.cancel_right_of_respectsIso
      (P := P.relative (uliftYoneda.{u + 1} (C := BigFppfOver B S hS))) (H.map a)
      eP.hom).mp h2
    exact (Space.relative_comp_map_iff yoneda H P a).mp h3
  have hsurj := hcarry _ inferInstance hsurjQ
  have hetale := hcarry _ inferInstance hetaleQ
  have hmonoρ : Mono ρ.hom := (sheafToPresheaf J (Type (u + 1))).map_mono ρ
  have hmonoH : Mono (H.map m) := by
    rw [hm]
    have h1 : (MorphismProperty.monomorphisms
        ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1))) ρ.hom := hmonoρ
    exact MorphismProperty.RespectsIso.precomp _ eP.hom _
      (MorphismProperty.RespectsIso.postcomp _ (e.app (U ⨯ V)).hom _ h1)
  have hmono : Mono m := H.mono_of_mono_map hmonoH
  have hQρ : Q ≫ ρ = F.map w' :=
    (MorphismProperty.map_eq_comp_monoPullbackToProd F α β Q w' hw₁ hw₂).symm
  have ham : a ≫ m = yoneda.map w' := by
    apply H.map_injective
    rw [H.map_comp, ha, hm, show H.map (yoneda.map w') = (uliftYoneda.{u + 1}).map w' from rfl]
    have hnatw : (F.map w').hom ≫ (e.app (U ⨯ V)).hom =
        (e.app W').hom ≫ (uliftYoneda.{u + 1}).map w' := e.hom.naturality w'
    calc ((e.app W').inv ≫ Q.hom ≫ eP.inv) ≫ eP.hom ≫ ρ.hom ≫ (e.app (U ⨯ V)).hom
        = (e.app W').inv ≫ (Q ≫ ρ).hom ≫ (e.app (U ⨯ V)).hom := by
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            rfl
      _ = (e.app W').inv ≫ (F.map w').hom ≫ (e.app (U ⨯ V)).hom := by rw [hQρ]
      _ = (e.app W').inv ≫ (e.app W').hom ≫ (uliftYoneda.{u + 1}).map w' := by rw [hnatw]
      _ = (uliftYoneda.{u + 1}).map w' := by rw [Iso.inv_hom_id_assoc]
  have hP₀alg : IsAlgebraicSpace B S hS P₀ :=
    isAlgebraicSpace_of_surjective_etale_atlas B S hS hP₀ W' a hsurj hetale
  have hlftm : Space.IsLocallyOfFiniteType B S hS m :=
    Space.holdsOnEveryEtaleChart_of_surjectiveChart B S hS _
      isEtaleLocalOnSourceAndTarget_locallyOfFiniteType
      ⟨W', U ⨯ V, a, 𝟙 _, w', hetale, MorphismProperty.presheaf_id _ _, hsurj,
        by rw [Category.comp_id, ham], hlftw⟩
  have hlqfm : Space.IsLocallyQuasiFinite B S hS m :=
    Space.isLocallyQuasiFinite_of_mono B S hS hP₀alg (isAlgebraicSpace_yoneda B S hS (U ⨯ V))
      m hmono hlftm
  obtain ⟨W, ⟨r₀⟩⟩ := Space.isRepresentable_of_locallyQuasiFinite_separated B S hS P₀
    (yoneda.obj (U ⨯ V)) hP₀alg (isAlgebraicSpace_yoneda B S hS (U ⨯ V)) m inferInstance
    hlqfm (Space.isSeparated_of_mono m hmono)
  let iso : yoneda.obj W ≅ P₀ := r₀.toIso
  let ipre : (F.obj W).obj ≅ (pullback α β).obj := e.app W ≪≫ H.mapIso iso ≪≫ eP
  let i : F.obj W ≅ pullback α β :=
    { hom := ⟨ipre.hom⟩
      inv := ⟨ipre.inv⟩
      hom_inv_id := Sheaf.hom_ext ipre.hom_inv_id
      inv_hom_id := Sheaf.hom_ext ipre.inv_hom_id }
  have hi : i.hom.hom = (e.app W).hom ≫ H.map iso.hom ≫ eP.hom := rfl
  obtain ⟨f, hf₁, hf₂⟩ := exists_toProd_of_point B S hS α β W i.hom
  have hfρ : F.map f = i.hom ≫ ρ :=
    MorphismProperty.map_eq_comp_monoPullbackToProd F α β i.hom f hf₁ hf₂
  have hyf : yoneda.map f = iso.hom ≫ m := by
    apply H.map_injective
    have hnat : (F.map f).hom ≫ (e.app (U ⨯ V)).hom =
        (e.app W).hom ≫ (uliftYoneda.{u + 1}).map f := e.hom.naturality f
    have hfh : (F.map f).hom = i.hom.hom ≫ ρ.hom := by
      rw [hfρ]
      rfl
    have h0 : (e.app W).inv ≫ ((F.map f).hom ≫ (e.app (U ⨯ V)).hom) =
        H.map iso.hom ≫ eP.hom ≫ ρ.hom ≫ (e.app (U ⨯ V)).hom := by
      rw [hfh, hi]
      simp only [Category.assoc]
      rw [Iso.inv_hom_id_assoc]
      exact Category.assoc _ _ _
    have key : H.map iso.hom ≫ eP.hom ≫ ρ.hom ≫ (e.app (U ⨯ V)).hom =
        (uliftYoneda.{u + 1}).map f := by
      rw [← h0, hnat, Iso.inv_hom_id_assoc]
    rw [H.map_comp, hm]
    exact key.symm
  have hchart := hlqfm W (U ⨯ V) iso.hom (𝟙 _) f
    (MorphismProperty.presheaf_of_isIso _ iso.hom) (MorphismProperty.presheaf_id _ _)
    (by rw [Category.comp_id, hyf])
  have hmonoF : Mono (F.map f) := by
    rw [hfρ]
    have h1 : (MorphismProperty.monomorphisms (FppfSheaf B S hS)) ρ :=
      MorphismProperty.mono_monoPullbackToProd F α β
    have : IsIso i.hom := i.isIso_hom
    exact MorphismProperty.RespectsIso.precomp _ i.hom _ h1
  have : Mono f := F.mono_of_mono_map hmonoF
  exact ⟨W, i, f, hf₁, hf₂, hchart.1, hchart.2, inferInstance⟩

/-! ### The geometric input of Stacks 0AIP in general -/

/-- The fibre product of two scheme-valued points of a formal algebraic space is represented
by an object of the site, by a locally of finite type, locally quasi-finite monomorphism to the
product of the two sources. -/
theorem exists_fibreProduct_representing_object
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (U V : BigFppfOver B S hS)
    (α : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
    (β : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X) :
    ∃ (W : BigFppfOver B S hS)
      (i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ≅ pullback α β)
      (f : W ⟶ U ⨯ V),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (f ≫ Limits.prod.fst) =
        i.hom ≫ pullback.fst α β ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (f ≫ Limits.prod.snd) =
        i.hom ≫ pullback.snd α β ∧
      AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f) ∧
      AlgebraicGeometry.LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map f) ∧
      Mono ((BigFppfOver.toScheme B S hS).map f) := by
  classical
  have hch : ∀ k : {z : (BigFppfOver.toScheme B S hS).obj (U ⨯ V) //
      ∃ c : FibreProductChart B S hS α β,
        z ∈ Set.range ((BigFppfOver.toScheme B S hS).map c.toProd)},
      ∃ c : FibreProductChart B S hS α β,
        (k : (BigFppfOver.toScheme B S hS).obj (U ⨯ V)) ∈
          Set.range ((BigFppfOver.toScheme B S hS).map c.toProd) := fun k => k.2
  choose ch hchmem using hch
  obtain ⟨W', kk, Q, w', hQ, hw', hkOI, hkcov, hw₁, hw₂⟩ :=
    exists_glued_atlas_of_fibreProductCharts B S hS (fun k => k.val)
      Subtype.val_injective ch
  have hhit : ∀ (T : BigFppfOver B S hS)
      (x : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ pullback α β)
      (b : T ⟶ U ⨯ V),
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.fst) =
        x ≫ pullback.fst α β →
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (b ≫ Limits.prod.snd) =
        x ≫ pullback.snd α β →
      ∀ t : (BigFppfOver.toScheme B S hS).obj T,
        (BigFppfOver.toScheme B S hS).map b t ∈
          Set.range ((BigFppfOver.toScheme B S hS).map w') := by
    intro T x b hb₁ hb₂ t
    obtain ⟨c, hcmem⟩ := exists_fibreProductChart B S hS hX α β T x b hb₁ hb₂ t
    have hk : ∃ c' : FibreProductChart B S hS α β,
        (BigFppfOver.toScheme B S hS).map b t ∈
          Set.range ((BigFppfOver.toScheme B S hS).map c'.toProd) := ⟨c, hcmem⟩
    obtain ⟨s, hs⟩ := hchmem ⟨_, hk⟩
    refine ⟨(BigFppfOver.toScheme B S hS).map (kk ⟨_, hk⟩) s, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hw' ⟨_, hk⟩, hs]
  obtain ⟨hlftw, hlqfw⟩ :=
    locallyQuasiFinite_toScheme_map_glued B S hS ch kk w' hw' hkOI hkcov
  obtain ⟨hsurjQ, hetaleQ⟩ :=
    relative_surjective_etale_of_glued B S hS ch kk w' hQ hw₁ hw₂ hkOI hkcov hhit
  exact exists_representing_object_of_glued B S hS w' hw₁ hw₂ hsurjQ hetaleQ hlftw

end AlgebraicGeometry.FormalSpace

end
