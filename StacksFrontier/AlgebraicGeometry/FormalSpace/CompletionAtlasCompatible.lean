module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Compatible étale atlases of a morphism of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S`. The source's reduction of **Stacks 0GDH** and **Stacks 0AR2** to the
affine case begins: "Choose a surjective étale morphism `W → X` with `W = ∐ W_i` a disjoint union
of affine schemes. For each `i` choose a surjective étale morphism `W'_i → W_i ×_X X'` where
`W'_i = ∐ W'_{ij}` is a disjoint union of affines." This file carries out that step, starting from
the affine étale atlas of a single algebraic space (Properties of Spaces, Lemma 03FX, in the form
`AlgebraicGeometry.FormalSpace.HasAffineEtaleAtlasPresheaf`), and then assembles **Stacks 0AR2**.

It produces the charts in the shape the reduction consumes
(`AlgebraicGeometry.FormalSpace.correspondsToNoetherianMapAfterSourceCover_completionSheafMap`):
spectra `Spec A_i ⟶ X` and `Spec A'_{ij} ⟶ X'` presented by
`AlgebraicGeometry.FormalSpace.affineOver`, each `Spec A'_{ij}` mapping to `Spec A_i` by the
spectrum of a ring map compatibly with `f`, with the joint surjectivity read in the sheafified
universe lift.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasAffineEtaleAtlasPresheaf`: an affine étale atlas of a
  presheaf by objects of the site, with joint surjectivity given by covering sieves.

## Main results

* `AlgebraicGeometry.FormalSpace.hasAffineEtaleAtlasPresheaf_of_isAlgebraicSpace`: every
  algebraic space has an affine étale atlas by objects of the site (Properties of Spaces,
  Lemma 03FX).
* `AlgebraicGeometry.FormalSpace.exists_affineOver_atlas_of_hasAffineEtaleAtlasPresheaf`: the
  atlas presented by spectra of rings.
* `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_sheafifiedULiftMap_of_cover`: the
  covering-sieve form of joint surjectivity gives joint surjectivity in the sheafified universe
  lift.
* `AlgebraicGeometry.FormalSpace.exists_compatible_affineOver_atlases`: compatible atlases of
  `X` and `X'`.
* `AlgebraicGeometry.FormalSpace.isRigEtale_completionSheafMap_of_isLocallyNoetherian`:
  **Stacks 0AR2**.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 0GDH](https://stacks.math.columbia.edu/tag/0GDH)
* [Stacks Project, Tag 0AR2](https://stacks.math.columbia.edu/tag/0AR2)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An affine étale atlas by objects of the site** (Properties of Spaces, Lemma 03FX): a family
of affine objects `V i` of the big fppf site with étale morphisms `V i ⟶ X`, jointly surjective
in the sense that every section of `X` restricts, along the arrows of a covering sieve, to a
section coming from one of the charts. -/
abbrev HasAffineEtaleAtlasPresheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (I : Type u) (V : I → BigFppfOver B S hS),
    (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
    ∃ a : ∀ i, yoneda.obj (V i) ⟶ X,
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (a i)) ∧
      ∀ (U : BigFppfOver B S hS) (s : X.obj (op U)),
        ∃ R : Sieve U, R ∈ BigFppfOver.topology B S hS U ∧
          ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ U), R g →
            ∃ (i : I) (t : W ⟶ V i), (a i).app (op W) t = X.map g.op s

/-- The covering-sieve form of joint surjectivity of a family of morphisms into a presheaf. -/
abbrev IsJointlySurjectiveBySieves {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type*}
    {V : I → BigFppfOver B S hS} (a : ∀ i, yoneda.obj (V i) ⟶ X) : Prop :=
  ∀ (U : BigFppfOver B S hS) (s : X.obj (op U)),
    ∃ R : Sieve U, R ∈ BigFppfOver.topology B S hS U ∧
      ∀ ⦃W : BigFppfOver B S hS⦄ (g : W ⟶ U), R g →
        ∃ (i : I) (t : W ⟶ V i), (a i).app (op W) t = X.map g.op s

variable {B S hS}

attribute [local instance] MorphismProperty.IsMultiplicative.toIsStableUnderComposition in
/-- **Every algebraic space over `S` has an affine étale atlas by objects of the site**
(Properties of Spaces, Lemma 03FX). The étale scheme atlas `U ⟶ X` of Definition 025Y is refined
by the affine open covering of `U`; every section of `X` lifts to `U` on a covering sieve, because
the atlas is surjective and étale, and then to one of the affine opens on a finer one. -/
theorem hasAffineEtaleAtlasPresheaf_of_isAlgebraicSpace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) : HasAffineEtaleAtlasPresheaf B S hS X := by
  classical
  let J := BigFppfOver.topology B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  obtain ⟨U₀, f, hfsurj, hfet⟩ := hX.exists_atlas
  obtain ⟨I, V, π, hVaff, hπ, hcovU⟩ := BigFppfOver.exists_affine_open_cover B S hS U₀
  refine ⟨I, V, hVaff, fun i ↦ yoneda.map (π i) ≫ f, fun i ↦ ?_, ?_⟩
  · have := hπ i
    exact MorphismProperty.comp_mem P.presheaf _ _
      ((Space.presheaf_yoneda_map_etale_iff B S hS (π i)).2 inferInstance) hfet
  intro U s
  let R : Sieve U :=
    { arrows := fun W g ↦ (∃ (i : I) (t : W ⟶ V i),
        (yoneda.map (π i) ≫ f).app (op W) t = X.map g.op s)
      downward_closed := by
        rintro W W' g ⟨i, t, ht⟩ k
        refine ⟨i, k ≫ t, ?_⟩
        have hnat := NatTrans.naturality_apply (yoneda.map (π i) ≫ f) k.op t
        change (yoneda.map (π i) ≫ f).app (op W') (k ≫ t) = _ at hnat
        rw [hnat, ht, op_comp, X.map_comp]
        rfl }
  refine ⟨R, ?_, fun _ _ hg ↦ hg⟩
  apply J.transitive
    ((Space.isLocallySurjective_of_surjective_etale B S hS f hfsurj hfet).imageSieve_mem s)
  rintro W g ⟨t₀, ht₀⟩
  refine J.superset_covering ?_ (J.pullback_stable t₀ hcovU)
  rintro W' k ⟨Z, c, d, ⟨i⟩, hfac⟩
  refine ⟨i, c, ?_⟩
  change f.app (op W') (c ≫ π i) = X.map (k ≫ g).op s
  rw [show c ≫ π i = k ≫ t₀ from hfac]
  have hnat := NatTrans.naturality_apply f k.op t₀
  change f.app (op W') (k ≫ t₀) = X.map k.op (f.app (op W) t₀) at hnat
  rw [hnat, ht₀, op_comp, X.map_comp]
  rfl

/-- Joint surjectivity by sieves is preserved by precomposing each chart with an isomorphism. -/
private theorem IsJointlySurjectiveBySieves.of_iso_comp {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {I : Type*} {V V' : I → BigFppfOver B S hS} {a : ∀ i, yoneda.obj (V i) ⟶ X}
    (ha : IsJointlySurjectiveBySieves B S hS a) (e : ∀ i, V' i ⟶ V i) [∀ i, IsIso (e i)] :
    IsJointlySurjectiveBySieves B S hS (fun i ↦ yoneda.map (e i) ≫ a i) := by
  intro U s
  obtain ⟨R, hR, hfac⟩ := ha U s
  refine ⟨R, hR, fun W q hq ↦ ?_⟩
  obtain ⟨i, t, ht⟩ := hfac q hq
  refine ⟨i, t ≫ inv (e i), ?_⟩
  change (a i).app (op W) ((t ≫ inv (e i)) ≫ e i) = _
  rwa [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **The atlas presented by spectra of rings.** An affine étale atlas by objects of the site
can be presented by the spectra `Spec Γ(V i, 𝒪)` of the rings of global sections, as objects
`AlgebraicGeometry.FormalSpace.affineOver` of the site. -/
theorem exists_affineOver_atlas_of_hasAffineEtaleAtlasPresheaf
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : HasAffineEtaleAtlasPresheaf B S hS X) :
    ∃ (I : Type u) (A : I → Type u) (_ : ∀ i, CommRing (A i))
      (hA : ∀ i, B.Contains (Spec (.of (A i)))) (str : ∀ i, Spec (.of (A i)) ⟶ S)
      (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X),
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (a i)) ∧
      IsJointlySurjectiveBySieves B S hS a := by
  obtain ⟨I, V, hVaff, a, haet, hcov⟩ := h
  let P := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let A : I → Type u := fun i ↦ ↥Γ((BigFppfOver.toScheme B S hS).obj (V i), ⊤)
  have hA : ∀ i, B.Contains (Spec (.of (A i))) := fun i ↦
    have := hVaff i
    contains_spec_globalSections B S hS (V i)
  let str : ∀ i, Spec (.of (A i)) ⟶ S := fun i ↦
    ((BigFppfOver.toScheme B S hS).obj (V i)).isoSpec.inv ≫ B.inclusion.map (V i).hom
  let ε : ∀ i, affineOver B S hS (hA i) (str i) ≅ V i := fun i ↦
    have := hVaff i
    Over.isoMk
      { hom := ObjectProperty.homMk
          (show Spec Γ((BigFppfOver.toScheme B S hS).obj (V i), ⊤) ⟶
            B.inclusion.obj (V i).left from ((BigFppfOver.toScheme B S hS).obj (V i)).isoSpec.inv)
        inv := ObjectProperty.homMk
          (show B.inclusion.obj (V i).left ⟶
            Spec Γ((BigFppfOver.toScheme B S hS).obj (V i), ⊤) from
            ((BigFppfOver.toScheme B S hS).obj (V i)).isoSpec.hom)
        hom_inv_id := by
          apply ObjectProperty.hom_ext
          exact ((BigFppfOver.toScheme B S hS).obj (V i)).isoSpec.inv_hom_id
        inv_hom_id := by
          apply ObjectProperty.hom_ext
          exact ((BigFppfOver.toScheme B S hS).obj (V i)).isoSpec.hom_inv_id }
      (by apply ObjectProperty.hom_ext; rfl)
  refine ⟨I, A, fun i ↦ inferInstance, hA, str, fun i ↦ yoneda.map (ε i).hom ≫ a i,
    fun i ↦ ?_, IsJointlySurjectiveBySieves.of_iso_comp hcov fun i ↦ (ε i).hom⟩
  refine MorphismProperty.comp_mem P.presheaf _ _
    ((Space.presheaf_yoneda_map_etale_iff B S hS (ε i).hom).2 ?_) (haet i)
  have : IsIso ((BigFppfOver.toScheme B S hS).map (ε i).hom) :=
    inferInstanceAs (IsIso ((BigFppfOver.toScheme B S hS).mapIso (ε i)).hom)
  infer_instance

/-- **Joint surjectivity in the sheafified universe lift.** A family of morphisms from
represented presheaves into an fppf sheaf `X` of `Type u` which is jointly surjective in the
covering-sieve sense is jointly surjective after the sheafified universe lift. -/
theorem isLocallySurjective_sigmaDesc_sheafifiedULiftMap_of_cover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {I : Type u} {V : I → BigFppfOver B S hS} (a : ∀ i, yoneda.obj (V i) ⟶ X)
    (hcov : IsJointlySurjectiveBySieves B S hS a) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective
      (Sigma.desc fun i : ULift.{u + 1} I ↦ Space.sheafifiedULiftMap B S hS (a i.down)) := by
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  have hsheafX : Presheaf.IsSheaf J (X ⋙ uliftFunctor.{u + 1}) := by
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff]
    exact (isSheaf_iff_isSheaf_of_type J X).mp hX
  have hisoX : IsIso (J.toSheafify (X ⋙ uliftFunctor.{u + 1})) := J.isIso_toSheafify hsheafX
  refine (Sheaf.isLocallySurjective_sigmaDesc_iff _).2 fun U s ↦ ?_
  obtain ⟨s₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((J.toSheafify (X ⋙ uliftFunctor.{u + 1})).app (op U))).surjective s
  obtain ⟨R, hR, hfac⟩ := hcov U s₀.down
  refine ⟨R, hR, fun {W} g hg ↦ ?_⟩
  obtain ⟨i, t, ht⟩ := hfac g hg
  set k : ULift.{u + 1} I := ULift.up i
  set m := Functor.whiskerRight (a k.down) uliftFunctor.{u + 1}
  refine ⟨k, (J.toSheafify (yoneda.obj (V k.down) ⋙ uliftFunctor.{u + 1})).app (op W)
    (ULift.up t), ?_⟩
  have hn : (J.toSheafify (X ⋙ uliftFunctor.{u + 1})).app (op W)
        (m.app (op W) (ULift.up t)) =
      (J.sheafifyMap m).app (op W)
        ((J.toSheafify (yoneda.obj (V k.down) ⋙ uliftFunctor.{u + 1})).app (op W)
          (ULift.up t)) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (J.toSheafify_naturality m) (op W)) _
  change (J.sheafifyMap m).app (op W)
      ((J.toSheafify (yoneda.obj (V k.down) ⋙ uliftFunctor.{u + 1})).app (op W)
        (ULift.up t)) = _
  rw [← hn, show m.app (op W) (ULift.up t) = ULift.up ((a i).app (op W) t) from rfl, ht]
  exact NatTrans.naturality_apply (J.toSheafify (X ⋙ uliftFunctor.{u + 1})) g.op s₀

/-- The site morphism between two `affineOver` presentations of one ring, along an equality of
the structure morphisms, has the identity for underlying morphism of schemes. -/
theorem toScheme_map_eqToHom_affineOver {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A))) {s₁ s₂ : Spec (.of A) ⟶ S} (p : s₁ = s₂) :
    (BigFppfOver.toScheme B S hS).map (eqToHom (congrArg (affineOver B S hS hA) p)) =
      𝟙 (Spec (.of A)) := by
  subst p
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

/-- A section of `X'` whose image in `X` comes from a chart `a` lifts to the fibre product of
`f` and `a`. -/
private theorem exists_pullback_fst_app_eq {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    {V W : BigFppfOver B S hS} (a : yoneda.obj V ⟶ X) (t : W ⟶ V) (s : X'.obj (op W))
    (ht : a.app (op W) t = f.app (op W) s) :
    ∃ σ : (pullback f a).obj (op W), (pullback.fst f a).app (op W) σ = s := by
  have hc : yonedaEquiv.symm s ≫ f = yoneda.map t ≫ a := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map, ht]
  refine ⟨yonedaEquiv (pullback.lift _ _ hc), ?_⟩
  rw [← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]

/-- Jointly surjective charts of the fibre products `X' ×_X V i`, for jointly surjective charts
`V i` of `X`, give jointly surjective charts of `X'`. -/
private theorem IsJointlySurjectiveBySieves.sigma_pullback_fst
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) {I : Type*}
    {V : I → BigFppfOver B S hS} {a : ∀ i, yoneda.obj (V i) ⟶ X}
    (ha : IsJointlySurjectiveBySieves B S hS a) {J : I → Type*}
    {V' : ∀ i, J i → BigFppfOver B S hS} {b : ∀ i j, yoneda.obj (V' i j) ⟶ pullback f (a i)}
    (hb : ∀ i, IsJointlySurjectiveBySieves B S hS (b i)) :
    IsJointlySurjectiveBySieves B S hS
      (fun k : Σ i, J i ↦ b k.1 k.2 ≫ pullback.fst f (a k.1)) := by
  intro U s
  obtain ⟨R, hR, hfac⟩ := ha U (f.app (op U) s)
  have hsec : ∀ ⦃W : BigFppfOver B S hS⦄ (q : W ⟶ U), R q →
      ∃ (i : I) (σ : (pullback f (a i)).obj (op W)),
        (pullback.fst f (a i)).app (op W) σ = X'.map q.op s := fun W q hq ↦ by
    obtain ⟨i, t, ht⟩ := hfac q hq
    obtain ⟨σ, hσ⟩ := exists_pullback_fst_app_eq f (a i) t (X'.map q.op s)
      (ht.trans (NatTrans.naturality_apply f q.op s).symm)
    exact ⟨i, σ, hσ⟩
  choose i σ hσ using hsec
  choose R' hR' hfac' using
    fun (W : BigFppfOver B S hS) (q : W ⟶ U) (hq : R q) ↦ hb (i q hq) W (σ q hq)
  refine ⟨Sieve.bind (R : Presieve U) (fun _ q hq ↦ R' _ q hq),
    (BigFppfOver.topology B S hS).bind_covering hR (fun _ q hq ↦ hR' _ q hq), ?_⟩
  rintro W' _ ⟨W, q', q, hq, hq', rfl⟩
  obtain ⟨j, t, ht⟩ := hfac' _ q hq q' hq'
  refine ⟨⟨i q hq, j⟩, t, ?_⟩
  change (pullback.fst f (a (i q hq))).app (op W') ((b (i q hq) j).app (op W') t) = _
  rw [ht, NatTrans.naturality_apply (pullback.fst f (a (i q hq))) q'.op (σ q hq), hσ, op_comp,
    FunctorToTypes.map_comp_apply]

/-- A morphism between `affineOver` presentations is the spectrum of a ring map, compatibly with
the structure morphisms. -/
private theorem exists_ringHom_of_affineOver_hom {A A' : Type u} [CommRing A] [CommRing A']
    {hA : B.Contains (Spec (.of A))} {hA' : B.Contains (Spec (.of A'))}
    {str : Spec (.of A) ⟶ S} {str' : Spec (.of A') ⟶ S}
    (g : affineOver B S hS hA' str' ⟶ affineOver B S hS hA str) :
    ∃ φ : A →+* A', Spec.map (CommRingCat.ofHom φ) = (BigFppfOver.toScheme B S hS).map g ∧
      str' = Spec.map (CommRingCat.ofHom φ) ≫ str := by
  let φ : A →+* A' := (Spec.preimage (show Spec (.of A') ⟶ Spec (.of A) from
    (BigFppfOver.toScheme B S hS).map g)).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = (BigFppfOver.toScheme B S hS).map g := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage _).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨φ, hφ, ?_⟩
  rw [hφ]
  exact (toScheme_map_comp_hom B S hS g).symm

attribute [local instance] MorphismProperty.IsMultiplicative.toIsStableUnderComposition in
/-- **Compatible étale atlases** (the first step of the source's proofs of Stacks 0GDH and Stacks
0AR2). Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S`. Then there are étale
atlases `{Spec A_i ⟶ X}` and `{Spec A'_k ⟶ X'}` by spectra of
rings, jointly surjective in the covering-sieve sense, with each `Spec A'_k` mapping to
`Spec A_{ι k}` by the spectrum of a ring map `φ k` compatibly with `f`: the atlas of `X'` is
assembled from atlases of the fibre products `X' ×_X Spec A_i`. -/
theorem exists_compatible_affineOver_atlases
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) :
    ∃ (Ix : Type u) (A : Ix → Type u) (_ : ∀ i, CommRing (A i))
      (hA : ∀ i, B.Contains (Spec (.of (A i)))) (str : ∀ i, Spec (.of (A i)) ⟶ S)
      (a : ∀ i, yoneda.obj (affineOver B S hS (hA i) (str i)) ⟶ X),
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (a i)) ∧
      IsJointlySurjectiveBySieves B S hS a ∧
      ∃ (Ik : Type u) (A' : Ik → Type u) (_ : ∀ k, CommRing (A' k)) (ι : Ik → Ix)
        (φ : ∀ k, A (ι k) →+* A' k) (hA' : ∀ k, B.Contains (Spec (.of (A' k))))
        (a' : ∀ k, yoneda.obj (affineOver B S hS (hA' k)
          (Spec.map (CommRingCat.ofHom (φ k)) ≫ str (ι k))) ⟶ X'),
        (∀ k, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (a' k)) ∧
        IsJointlySurjectiveBySieves B S hS a' ∧
        ∀ k, yoneda.map (Space.specSiteObjectMap (φ k) (hA (ι k)) (hA' k) (str (ι k))) ≫
          a (ι k) = a' k ≫ f := by
  classical
  obtain ⟨Ix, A, instA, hA, str, a, ha, hcov⟩ :=
    exists_affineOver_atlas_of_hasAffineEtaleAtlasPresheaf
      (hasAffineEtaleAtlasPresheaf_of_isAlgebraicSpace hX)
  let := instA
  choose J A'' instA'' hA'' str'' b hb hcovZ using fun i ↦
    exists_affineOver_atlas_of_hasAffineEtaleAtlasPresheaf
      (hasAffineEtaleAtlasPresheaf_of_isAlgebraicSpace (isAlgebraicSpace_pullback B S hS f (a i)
        hX' (isAlgebraicSpace_yoneda B S hS _) hX))
  let Ik : Type u := Σ i, J i
  let A' : Ik → Type u := fun k ↦ A'' k.1 k.2
  let instA' : ∀ k, CommRing (A' k) := fun k ↦ instA'' k.1 k.2
  let hA' : ∀ k, B.Contains (Spec (.of (A' k))) := fun k ↦ hA'' k.1 k.2
  let g : ∀ k : Ik, affineOver B S hS (hA' k) (str'' k.1 k.2) ⟶
      affineOver B S hS (hA k.1) (str k.1) := fun k ↦
    yoneda.preimage (b k.1 k.2 ≫ pullback.snd f (a k.1))
  choose φ hφ hstr using fun k : Ik ↦ exists_ringHom_of_affineOver_hom (g k)
  let e : ∀ k : Ik, affineOver B S hS (hA' k) (Spec.map (CommRingCat.ofHom (φ k)) ≫ str k.1) ⟶
      affineOver B S hS (hA' k) (str'' k.1 k.2) := fun k ↦
    eqToHom (congrArg (affineOver B S hS (hA' k)) (hstr k).symm)
  have : ∀ k, IsIso (e k) := fun k ↦ by dsimp only [e]; infer_instance
  let a' : ∀ k : Ik, yoneda.obj (affineOver B S hS (hA' k)
      (Spec.map (CommRingCat.ofHom (φ k)) ≫ str k.1)) ⟶ X' := fun k ↦
    yoneda.map (e k) ≫ b k.1 k.2 ≫ pullback.fst f (a k.1)
  have hgk : ∀ k : Ik, yoneda.map (g k) = b k.1 k.2 ≫ pullback.snd f (a k.1) := fun k ↦
    yoneda.map_preimage _
  refine ⟨Ix, A, instA, hA, str, a, ha, hcov, Ik, A', instA', Sigma.fst, φ, hA', a', ?_,
    (IsJointlySurjectiveBySieves.sigma_pullback_fst f hcov hcovZ).of_iso_comp e, ?_⟩
  · intro k
    refine (Space.isEtale_iff_presheaf_of_yoneda B S hS _).mp ?_
    refine Space.isEtale_comp B S hS (Space.isEtale_of_isIso B S hS _)
      (Space.isEtale_comp B S hS ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).mpr
        (hb k.1 k.2)) ?_)
    exact Space.isEtale_pullback_fst B S hS hX' hX (isAlgebraicSpace_yoneda B S hS _) f (a k.1)
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).mpr (ha k.1))
  · intro k
    have hh : Space.specSiteObjectMap (φ k) (hA k.1) (hA' k) (str k.1) = e k ≫ g k := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (φ k)) =
        (BigFppfOver.toScheme B S hS).map (e k) ≫ (BigFppfOver.toScheme B S hS).map (g k)
      have h1 : (BigFppfOver.toScheme B S hS).map (e k) = 𝟙 (Spec (.of (A' k))) :=
        toScheme_map_eqToHom_affineOver (hA' k) (hstr k).symm
      exact (hφ k).trans ((Category.id_comp _).symm.trans (congrArg (· ≫ _) h1.symm))
    refine (congrArg (fun m ↦ yoneda.map m ≫ a k.1) hh).trans ?_
    change yoneda.map (e k) ≫ yoneda.map (g k) ≫ a k.1 = _
    rw [hgk, Category.assoc, ← pullback.condition]
    rfl

/-- **Stacks 0AR2.** Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S`, let
`T ⊆ |X|` be closed, and let `U ⊆ X` be the open complement of `T` and `U' = f⁻¹U` (the
situation of Stacks 0GDB). If `X` is locally Noetherian, `f` is locally of finite type and
`U' → U` is étale, then the completion `f_{/T} : X'_{/T'} ⟶ X_{/T}` is rig-étale.

The proof is the source's: compatible étale atlases of `X` and `X'` by spectra of rings
(Properties of Spaces, Lemma 03FX; `exists_compatible_affineOver_atlases`), condition (4) of
Stacks 0GCZ for `f_{/T}` from them (`correspondsToRigEtaleMapAfterSourceCover_completionSheafMap`:
the reduction to the affine case and the affine case by part (1) of Stacks 0ALQ), and the
implication (4) ⟹ (1) of Stacks 0GCZ. -/
@[stacks 0AR2]
theorem isRigEtale_completionSheafMap_of_isLocallyNoetherian
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hT : @IsClosed _ (Space.pointTopology B S hS X) T)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (het : Space.IsEtale B S hS (Space.openComplementRestriction B S hS f T)) :
    IsRigEtale B S hS (Space.completionSheafMap B S hS f T) := by
  obtain ⟨Ix, A, instA, hA, str, a, ha, hcov, Ik, A', instA', ι, φ, hA', a', ha', hcov', hsq⟩ :=
    exists_compatible_affineOver_atlases hX' hX f
  let := instA
  let := instA'
  exact isRigEtale_completionSheafMap_of_atlases hX' hX f T hT hXN hf het
    (A := fun i : ULift.{u + 1} Ix ↦ A i.down) (fun i ↦ hA i.down) (fun i ↦ str i.down)
    (fun i ↦ a i.down) (fun i ↦ ha i.down)
    (isLocallySurjective_sigmaDesc_sheafifiedULiftMap_of_cover hX.isSheaf a hcov)
    (A' := fun k : ULift.{u + 1} Ik ↦ A' k.down) (fun k ↦ ULift.up (ι k.down))
    (fun k ↦ φ k.down) (fun k ↦ hA' k.down) (fun k ↦ a' k.down) (fun k ↦ ha' k.down)
    (isLocallySurjective_sigmaDesc_sheafifiedULiftMap_of_cover hX'.isSheaf a' hcov')
    (fun k ↦ Space.specSiteObjectMap (φ k.down) (hA (ι k.down)) (hA' k.down) (str (ι k.down)))
    (fun _ ↦ rfl) (fun k ↦ hsq k.down)

end AlgebraicGeometry.FormalSpace

end
