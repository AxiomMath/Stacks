module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationFibers

/-!
# Monomorphic field-valued representatives of points

Let `F` be an algebraic space over a scheme `S` and let `x` be a point of `|F|` with a
field-valued representative `Spec k ⟶ F` whose two self-intersection projections are étale and
quasi-compact. Then `x` has a *monomorphic* field-valued representative.

## Main results

* `AlgebraicGeometry.Space.isSheaf_yoneda_obj`: a represented presheaf on the big fppf site is a
  sheaf.
* `AlgebraicGeometry.Space.exists_mono_yoneda_of_isPullback`: a morphism from a represented
  presheaf into a sheaf descends along any faithfully flat morphism of finite presentation
  with the same kernel pair, and the descended morphism is a monomorphism.
* `hasMonomorphicFieldRepresentative_of_hasEtaleQuasiCompactFieldRepresentative`: a point with a
  field-valued representative whose self-intersection projections are étale and quasi-compact has
  a monomorphic field-valued representative, and
  `hasEtaleQuasiCompactFieldRepresentative_iff_hasMonomorphicFieldRepresentative` is the
  resulting equivalence; both are in the namespace `AlgebraicGeometry.Space`.

## References

* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Descending a morphism along the quotient of its kernel pair -/

/-- The presheaf represented by an object of the big fppf site of `S` is a sheaf. -/
theorem isSheaf_yoneda_obj (U : BigFppfOver B S hS) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj U) := by
  have _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  have _ : (BigFppfOver.topology B S hS).Subcanonical := inferInstance
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

/-- If `G` is fully faithful and `G t, G s` is the kernel pair of `f`, then two maps `x, y` with
`G x ≫ f = G y ≫ f` factor through the kernel pair `(t, s)`. -/
private theorem exists_comp_eq_of_isPullback_map {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) [G.Full] [G.Faithful] {R U V : C} {Z : D} (t s : R ⟶ U) {f : G.obj U ⟶ Z}
    (hR : IsPullback (G.map t) (G.map s) f f) (x y : V ⟶ U) (h : G.map x ≫ f = G.map y ≫ f) :
    ∃ r : V ⟶ R, r ≫ t = x ∧ r ≫ s = y :=
  ⟨G.preimage (hR.lift _ _ h), G.map_injective (by simp [hR.lift_fst _ _ h]),
    G.map_injective (by simp [hR.lift_snd _ _ h])⟩

/-- Let `f : h_U ⟶ F` be a morphism from a represented presheaf to a sheaf on the big fppf
site of `S`, with kernel pair represented by `t, s : R ⟶ U`, and let `π` be a morphism of
`S`-schemes out of `U` which is flat, locally of finite presentation and surjective and whose
kernel pair is again `t, s`. Then `π` comes from a morphism `m` of the site, and `f` factors
through `h_m` by a monomorphism out of `h_{U'}`. -/
theorem exists_mono_yoneda_of_isPullback
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hFsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {U R U' : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F) (t s : R ⟶ U)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) f f)
    (π : (Over.post B.inclusion).obj U ⟶ (Over.post B.inclusion).obj U')
    (hflat : Flat π.left) (hlfp : LocallyOfFinitePresentation π.left)
    (hsurjπ : Surjective π.left)
    (hπ : IsPullback ((Over.post B.inclusion).map t) ((Over.post B.inclusion).map s) π π) :
    ∃ (m : U ⟶ U') (d : yoneda.obj U' ⟶ F),
      (Over.post B.inclusion).map m = π ∧ Mono d ∧ yoneda.map m ≫ d = f := by
  classical
  let J := BigFppfOver.topology B S hS
  let H : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  have hHfull : H.Full := by change (Over.post (X := B.obj hS) B.inclusion).Full; infer_instance
  have hHfaith : H.Faithful := by
    change (Over.post (X := B.obj hS) B.inclusion).Faithful; infer_instance
  let m : U ⟶ U' := H.preimage π
  have hmπ : H.map m = π := Functor.map_preimage H π
  have hts : t ≫ m = s ≫ m := by
    refine H.map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hmπ]
    exact hπ.w
  have hp1 : Presheaf.IsLocallySurjective J (H.op.whiskerLeft (yoneda.map π)) :=
    isLocallySurjective_pointsMap_of_flat_locallyOfFinitePresentation_surjective B S hS π
  have hlocm : Presheaf.IsLocallySurjective J (yoneda.map m) := by
    rw [show m = H.preimage π from rfl, ← pointsYonedaIso_inv_comp H π]
    infer_instance
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, isSheaf_yoneda_obj B S hS R⟩
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, isSheaf_yoneda_obj B S hS U⟩
  let U'F : Sheaf J (Type u) := ⟨yoneda.obj U', isSheaf_yoneda_obj B S hS U'⟩
  let FF : Sheaf J (Type u) := ⟨F, hFsh⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let mf : UF ⟶ U'F := ⟨yoneda.map m⟩
  let ff : UF ⟶ FF := ⟨f⟩
  have hwm : tf ≫ mf = sf ≫ mf := by
    apply Sheaf.hom_ext
    change yoneda.map t ≫ yoneda.map m = yoneda.map s ≫ yoneda.map m
    rw [← Functor.map_comp, ← Functor.map_comp, hts]
  have hwf : tf ≫ ff = sf ≫ ff := Sheaf.hom_ext_iff.mpr hR.w
  have hkerf : ∀ ⦃V : BigFppfOver B S hS⦄ (x y : V ⟶ U),
      f.app (op V) (yonedaEquiv (yoneda.map x)) = f.app (op V) (yonedaEquiv (yoneda.map y)) →
      ∃ r : V ⟶ R, r ≫ t = x ∧ r ≫ s = y := fun _ x y hxy ↦
    exists_comp_eq_of_isPullback_map yoneda t s hR x y
      (yonedaEquiv.injective (by rwa [yonedaEquiv_comp, yonedaEquiv_comp]))
  have hkerm : ∀ ⦃V : BigFppfOver B S hS⦄ (x y : UF.obj.obj (op V)),
      mf.hom.app (op V) x = mf.hom.app (op V) y →
      ∃ r : RF.obj.obj (op V), tf.hom.app (op V) r = x ∧ sf.hom.app (op V) r = y := by
    intro V x y hxy
    refine exists_comp_eq_of_isPullback_map H t s hπ x y ?_
    rw [← hmπ, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg H.map (show x ≫ m = y ≫ m from hxy)
  obtain ⟨hcolim⟩ := Sheaf.nonempty_isColimitCoforkOfKernelPair tf sf mf hwm hkerm hlocm
  let d : U'F ⟶ FF := hcolim.desc (Cofork.ofπ ff hwf)
  have hfac : mf ≫ d = ff := by
    simpa only [Cofork.π_ofπ] using Cofork.IsColimit.π_desc hcolim (t := Cofork.ofπ ff hwf)
  have hfac' : yoneda.map m ≫ d.hom = f := by
    simpa using Sheaf.hom_ext_iff.mp hfac
  refine ⟨m, d.hom, hmπ, ?_, hfac'⟩
  refine (NatTrans.mono_iff_mono_app _).2 fun V ↦ (CategoryTheory.mono_iff_injective _).2 ?_
  obtain ⟨T⟩ := V
  intro a b hab
  refine Sheaf.eq_of_eq_on_sieve (X := U'F)
    (J.intersection_covering (Presheaf.imageSieve_mem J (yoneda.map m) a)
      (Presheaf.imageSieve_mem J (yoneda.map m) b)) a b ?_
  rintro W k ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩
  change a' ≫ m = k ≫ a at ha'
  change b' ≫ m = k ≫ b at hb'
  have hdk : d.hom.app (op W) (k ≫ a) = d.hom.app (op W) (k ≫ b) := by
    have hna := NatTrans.naturality_apply d.hom k.op a
    have hnb := NatTrans.naturality_apply d.hom k.op b
    change d.hom.app (op W) (k ≫ a) = F.map k.op (d.hom.app (op T) a) at hna
    change d.hom.app (op W) (k ≫ b) = F.map k.op (d.hom.app (op T) b) at hnb
    rw [hna, hnb, hab]
  have hfab : f.app (op W) (yonedaEquiv (yoneda.map a')) =
      f.app (op W) (yonedaEquiv (yoneda.map b')) := by
    have hcomp : ∀ c : W ⟶ U, f.app (op W) (yonedaEquiv (yoneda.map c)) =
        d.hom.app (op W) (c ≫ m) := by
      intro c
      rw [← hfac', yonedaEquiv_yoneda_map]
      rfl
    rw [hcomp, hcomp, ha', hb', hdk]
  obtain ⟨r, hrt, hrs⟩ := hkerf a' b' hfab
  change k ≫ a = k ≫ b
  rw [← ha', ← hb', ← hrt, ← hrs, Category.assoc, Category.assoc, hts]

/-! ### Monomorphic field-valued representatives -/

/-- If `yoneda.map a` is a base change of `g` along `f` and `pullback.fst f g` is étale and
quasi-compact after every representable base change, then `a` is étale and quasi-compact. -/
private theorem etale_and_quasiCompact_of_isPullback_fst
    {G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U R : BigFppfOver B S hS}
    {f : yoneda.obj U ⟶ K} {g : G ⟶ K} (a : R ⟶ U) (b : yoneda.obj R ⟶ G)
    (sq : IsPullback (yoneda.map a) b f g)
    (h : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((@Etale.{u} : MorphismProperty Scheme.{u}) ⊓
        (@QuasiCompact.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS))) (pullback.fst f g)) :
    Etale ((BigFppfOver.toScheme B S hS).map a) ∧
      QuasiCompact ((BigFppfOver.toScheme B S hS).map a) :=
  h.property (𝟙 _) sq.isoPullback.hom a
    (IsPullback.of_horiz_isIso ⟨by simp [sq.isoPullback_hom_fst]⟩)

/-- If a point of an algebraic space over `S` has a field-valued representative whose two
self-intersection projections are étale and quasi-compact, then it has a monomorphic
field-valued representative. -/
theorem hasMonomorphicFieldRepresentative_of_hasEtaleQuasiCompactFieldRepresentative
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) (h : HasEtaleQuasiCompactFieldRepresentative B S hS F x) :
    HasMonomorphicFieldRepresentative B S hS F x := by
  classical
  obtain ⟨p, hp, hfst, -⟩ := h
  let Q := BigFppfOver.toScheme B S hS
  let H : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let f := fieldMorphism B S hS F p
  let rep := hF.diagonal_representable.of_diag f
  let R := rep.pullback f
  let t : R ⟶ p.siteObject := rep.fst' f
  let s : R ⟶ p.siteObject := rep.snd f
  have hR : IsPullback (yoneda.map t) (yoneda.map s) f f := rep.isPullback' f
  obtain ⟨htE, htQ⟩ :=
    etale_and_quasiCompact_of_isPullback_fst B S hS t (yoneda.map s) hR hfst
  obtain ⟨hsE, hsQ⟩ :=
    etale_and_quasiCompact_of_isPullback_fst B S hS s (yoneda.map t) hR.flip hfst
  have _ : IsAffine (Q.obj p.siteObject) := inferInstanceAs (IsAffine (Spec (.of p.carrier)))
  have hRaff : IsAffine (Q.obj R) := by
    obtain ⟨hft, hur⟩ := (etale_iff_unramified_over_field p.carrier (Q.map t)).mp htE
    exact isAffine_of_unramified_quasiCompact p.carrier (Q.map t)
  have hfl : ∀ u : R ⟶ p.siteObject, Etale (Q.map u) → QuasiCompact (Q.map u) →
      Stacks.Morphisms.IsFiniteLocallyFree (Q.map u) := fun u hE hQ ↦
    (Stacks.Morphisms.isFiniteLocallyFree_iff_of_specTarget (Q.map u)).mpr
      ⟨isFinite_of_isAffine_of_etale_over_field p.carrier (Q.map u), inferInstance,
        inferInstance⟩
  have hflft := hfl t htE htQ
  have hflfs := hfl s hsE hsQ
  have _ : IsAffine (H.obj p.siteObject).left := ‹IsAffine (Q.obj p.siteObject)›
  have _ : IsAffine (H.obj R).left := hRaff
  have _ : Stacks.Morphisms.IsFiniteLocallyFree (H.map t).left := hflft
  have _ : Stacks.Morphisms.IsFiniteLocallyFree (H.map s).left := hflfs
  have _ : IsEquivalenceRelation (H.map t) (H.map s) :=
    isEquivalenceRelation_of_isPullback B S hS f t s hR
  obtain ⟨A, _, g, π, hsize, hflf, hsurjπ, hpb⟩ :=
    exists_quotient_of_isFiniteLocallyFree_relation S (H.map t) (H.map s)
  have hk' : B.Contains (Spec (CommRingCat.of A)) :=
    lt_of_le_of_lt hsize p.siteObject.left.2
  obtain ⟨m, d, hmπ, hmono, hfd⟩ :=
    exists_mono_yoneda_of_isPullback B S hS hF.isSheaf f t s hR
      (U' := Over.mk (⟨g⟩ : B.obj hk' ⟶ B.obj hS)) π
      (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left)
      (Stacks.Morphisms.IsFiniteLocallyFree.locallyOfFinitePresentation π.left) hsurjπ hpb
  obtain ⟨instAlg, instFinite, hAfield, -⟩ :=
    exists_algebra_isField_of_isFinite_flat_surjective (A := A) p.carrier π.left
      (Stacks.Morphisms.IsFiniteLocallyFree.isFinite π.left)
      (Stacks.Morphisms.IsFiniteLocallyFree.flat π.left) hsurjπ
  let instFieldA : Field A := hAfield.toField
  let p' : FieldValuedPoint B S hS F :=
    { carrier := A, field := instFieldA, contained := hk', toBase := g, value := yonedaEquiv d }
  have hfield : fieldMorphism B S hS F p' = d := Equiv.symm_apply_apply _ _
  refine ⟨p', ?_, by rwa [hfield]⟩
  rw [← hp]
  refine ((FieldValuedPoint.class_eq_class_iff B S hS F p p').mpr
    ⟨p, FieldValuedPoint.dominates_refl B S hS F p,
      (show p.siteObject ⟶ p'.siteObject from m), ?_⟩).symm
  change F.map m.op (yonedaEquiv d) = p.value
  rw [yonedaEquiv_naturality, hfd]
  exact yonedaEquiv_fieldMorphism B S hS F p

/-- For a point of an algebraic space over `S`, having a field-valued representative with étale
quasi-compact self-intersection projections is equivalent to having a monomorphic field-valued
representative. -/
@[stacks 03JU "conditions (3) and (4)"]
theorem hasEtaleQuasiCompactFieldRepresentative_iff_hasMonomorphicFieldRepresentative
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) :
    HasEtaleQuasiCompactFieldRepresentative B S hS F x ↔
      HasMonomorphicFieldRepresentative B S hS F x :=
  ⟨hasMonomorphicFieldRepresentative_of_hasEtaleQuasiCompactFieldRepresentative B S hS hF x,
    hasEtaleQuasiCompactFieldRepresentative_of_hasMonomorphicFieldRepresentative B S hS F x⟩

end AlgebraicGeometry.Space

end
