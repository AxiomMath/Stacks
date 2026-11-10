module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity.Density
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chart criterion for scheme-theoretic density, and flat inverse images

The equivalent conditions of Stacks 0833 for scheme-theoretic density of an open subspace of an
algebraic space, tested on one surjective étale scheme chart, and their application: the inverse
image of a scheme-theoretically dense open subspace along a flat morphism locally of finite
presentation is scheme-theoretically dense (Stacks 0832, with the quasi-finiteness hypothesis
removed by Stacks 05IE). See
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity` for an overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Density

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The equivalent conditions of Stacks 0833 -/

/-- An étale morphism of schemes is locally quasi-finite: over affine opens it is an étale ring
map, hence essentially of finite type and formally unramified, hence quasi-finite. -/
@[ega "IV 17.4.3" "étale morphisms"]
private lemma locallyQuasiFinite_of_etale {A A' : Scheme.{u}} (f : A ⟶ A') (hf : Etale f) :
    LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff]
  intro P hP Q hQ e
  have hring : (f.appLE P Q e).hom.Etale := hf.etale_appLE hP hQ e
  algebraize [(f.appLE P Q e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

/-- **The inverse image of an open subspace is compatible with change of chart.** For an open
subspace `U ⊆ X`, a scheme chart `φ : V ⟶ X` and a morphism `p : T ⟶ V` of the site, the image
of the morphism of schemes representing `U ×_X T` is the inverse image along `p` of the image of
the one representing `U ×_X V`.

Both are open subschemes of `T` through which the same morphisms of the site factor, namely
those landing in `U` after composition with `p` and then the chart, so
`AlgebraicGeometry.Space.opensRange_eq_of_factors_iff` identifies them. This is
`AlgebraicGeometry.Space.opensRange_snd_chartOpenRestriction` with the inclusion of an open
subscheme replaced by an arbitrary morphism of the site. -/
private lemma opensRange_snd_comp {U : Subfunctor X} (hU : IsOpenImmersion B S hS U.ι)
    {V T : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ X) (p : T ⟶ V)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (hU.rep.snd (yoneda.map p ≫ φ)))]
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ))] :
    ((BigFppfOver.toScheme B S hS).map (hU.rep.snd (yoneda.map p ≫ φ))).opensRange =
      ((BigFppfOver.toScheme B S hS).map p) ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ)).opensRange := by
  refine opensRange_eq_of_factors_iff B S hS (hU.rep.snd (yoneda.map p ≫ φ)) _ fun Q k => ?_
  have h1 : k ∈ (U.preimage (yoneda.map p ≫ φ)).obj (op Q) ↔
      (k ≫ p) ∈ (U.preimage φ).obj (op Q) := Iff.rfl
  have h2 : ((BigFppfOver.toScheme B S hS).map (k ≫ p)) ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ)).opensRange =
      ((BigFppfOver.toScheme B S hS).map k) ⁻¹ᵁ
        (((BigFppfOver.toScheme B S hS).map p) ⁻¹ᵁ
          ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ)).opensRange) := by
    rw [(BigFppfOver.toScheme B S hS).map_comp, Scheme.Hom.comp_preimage]
  exact (mem_preimage_iff_factors B S hS U hU.rep (yoneda.map p ≫ φ) Q k).symm.trans
    (h1.trans ((mem_preimage_iff_factors B S hS U hU.rep φ Q (k ≫ p)).trans
      ((siteMap_factors_openImmersion_iff B S hS Q (hU.rep.pullback φ) V
        (hU.rep.snd φ) (k ≫ p)).trans (by rw [h2]))))

/-- If the closure of `U ×_X V` in every open subscheme of the chart `V` is everything, then the
open subscheme of `V` representing `U ×_X V` is scheme-theoretically dense. -/
private theorem isSchemeTheoreticallyDense_opensRange_snd_of_forall
    {U : Subfunctor X} (hU : IsOpenImmersion B S hS U.ι) {V : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ X)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ))]
    (h : ∀ P : ((BigFppfOver.toScheme B S hS).obj V).Opens,
      schemeTheoreticImageSubfunctor B S hS
        (U.preimage (yoneda.map (siteOpenObject_ι B S hS V P) ≫ φ)).ι = ⊤) :
    Scheme.Opens.IsSchemeTheoreticallyDense
      ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ)).opensRange := by
  intro P
  have hsndP := isOpenImmersion_snd B S hS hU (yoneda.map (siteOpenObject_ι B S hS V P) ≫ φ)
  have hr := opensRange_snd_comp B S hS hU φ (siteOpenObject_ι B S hS V P)
  rw [siteOpenObject_ι_map] at hr
  exact isSchemeTheoreticallyDominant_of_opensRange_eq _ _
    (by rw [hr, Scheme.Opens.opensRange_ι])
    ((schemeTheoreticImageSubfunctor_preimage_eq_top_iff B S hS hU _).1 (h P))

/-- **Descent of density along a chart.** Let `φ : V ⟶ X` be a surjective étale chart whose
open subscheme `U ×_X V` is scheme-theoretically dense, and `T = V ×_X C` its base change along a
chart `g : C ⟶ X`. If the inverse image of that open subscheme in `T` is dense, then the closure
of `U ×_X C` in `C` is everything. -/
private theorem schemeTheoreticImageSubfunctor_preimage_eq_top_of_isPullback
    {U : Subfunctor X} (hU : IsOpenImmersion B S hS U.ι) {V C T : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ X) (g : yoneda.obj C ⟶ X) (q : T ⟶ C) (p : T ⟶ V)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ))]
    (hpb : IsPullback (yoneda.map p) (yoneda.map q) φ g)
    (hqE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q))
    (hqS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q))
    (hTdense : Scheme.Opens.IsSchemeTheoreticallyDense
      (((BigFppfOver.toScheme B S hS).map p) ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ)).opensRange)) :
    schemeTheoreticImageSubfunctor B S hS (U.preimage g).ι = ⊤ := by
  have hsndp := isOpenImmersion_snd B S hS hU (yoneda.map p ≫ φ)
  have hrp := opensRange_snd_comp B S hS hU φ p
  have hdomp := isSchemeTheoreticallyDominant_of_opensRange_eq
    (((BigFppfOver.toScheme B S hS).map p ⁻¹ᵁ
      ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ)).opensRange).ι)
    ((BigFppfOver.toScheme B S hS).map (hU.rep.snd (yoneda.map p ≫ φ)))
    (by rw [Scheme.Opens.opensRange_ι]; exact hrp.symm)
    (Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense _ hTdense)
  have hchart : schemeTheoreticImageSubfunctor B S hS
      ((U.preimage g).preimage (yoneda.map q)).ι = ⊤ := by
    rw [← Subfunctor.preimage_comp U (yoneda.map q) g, ← hpb.w]
    exact (schemeTheoreticImageSubfunctor_preimage_eq_top_iff B S hS hU
      (yoneda.map p ≫ φ)).2 hdomp
  have hsq : ((U.preimage g).preimage (yoneda.map q)).ι ≫ yoneda.map q =
      (U.preimage g).fromPreimage (yoneda.map q) ≫ (U.preimage g).ι :=
    (Subfunctor.isPullback_preimage (yoneda.map q) (U.preimage g)).w.symm
  have hle := schemeTheoreticImageSubfunctor_le_preimage B S hS
    (isAlgebraicSpace_yoneda B S hS T) (isAlgebraicSpace_yoneda B S hS C) hsq
  rw [hchart] at hle
  exact subfunctor_eq_top_of_isSurjective_isEtale_preimage B S hS
    (isAlgebraicSpace_yoneda B S hS C) _
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (U.preimage g).ι
      (isAlgebraicSpace_yoneda B S hS C)).1.isSheaf
    T (yoneda.map q) hqS hqE (le_antisymm le_top hle)

/-- **Stacks 0833.** Let `U` be an open subspace of an algebraic space `X` over a scheme `S`
contained in a big fppf site `B`. Then `U` is scheme-theoretically dense in `X` -- the
scheme-theoretic closure of `U ×_X V` in `V` is all of `V` for every étale morphism `V ⟶ X` of
algebraic spaces over `S` -- if and only if there are a scheme `V` and a surjective étale
morphism `φ : V ⟶ X` for which that holds over the open subschemes of `V` alone: the
scheme-theoretic closure of `U ×_X W` in `W` is all of `W` for every open subscheme `W` of `V`.
The second condition says exactly that the open subscheme `U ×_X V` of `V` is
scheme-theoretically dense in the sense of Stacks 01RB.

The first condition trivially implies the second, since the composite of an open immersion with
an étale morphism is étale. For the converse let `C` be an étale scheme chart of `X`; by
`AlgebraicGeometry.Space.isSchemeTheoreticallyDense_iff_forall_chart` it suffices to make the
scheme-theoretic closure of `U ×_X C` in `C` everything, and the two conditions are compared
over `T = V ×_X C`. The projection `T ⟶ V` is a base change of the étale chart `C`, hence étale
and so flat, locally of finite presentation and locally quasi-finite, so Stacks 0832 carries
scheme-theoretic density of `U ×_X V` in `V` to scheme-theoretic density of `U ×_X T` in `T`;
chartwise this is read through
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_preimage_eq_top_iff`, which identifies
closures of inverse images with scheme-theoretic dominance of the representing morphisms of
schemes. The projection `T ⟶ C` is a base change of `φ`, hence surjective étale, and
`AlgebraicGeometry.Space.subfunctor_eq_top_of_isSurjective_isEtale_preimage` descends the
closure over `T` to the closure over `C`.

Scheme-theoretic density of `U ×_X V` in `V`, rather than merely the equality of the
scheme-theoretic closure of `U ×_X V` with `V`, is what the second condition has to say, and
the source's literal reading of it is false. Take for `X` a scheme and for `φ` the identity,
which is a surjective étale morphism from a scheme: the literal reading of condition (2) is
then exactly that the scheme-theoretic closure of `U` in `X` is `X`, whereas condition (1),
applied to the open immersions `W ⟶ X` -- which are étale -- is exactly that `U` is a
scheme-theoretically dense open subscheme of `X` in the sense of Stacks 01RB. Stacks 01RC
exhibits an affine scheme `X = Spec(k[x, z₁, z₂, …]/(xⁿzₙ))` and an open `U = X ∖ V(z₁, z₂, …)`
with the former but not the latter: the closure is `X` because `A ⟶ ∏ₙ A_{zₙ}` is injective,
while `U` is not even topologically dense in `X`, hence not scheme-theoretically dense. The
literal reading would moreover make the quasi-compactness hypothesis of Stacks 0835
superfluous, and contradict the remark that follows Stacks 0834. By Stacks 01RD the two
readings agree exactly when the inclusion is quasi-compact, and it is the density form that
Stacks 0832 transports.

The part of the source's argument for (2) implies (1) that does hold for the bare equality is
`AlgebraicGeometry.Space.schemeTheoreticClosure_eq_top_of_isSurjective_isEtale`: a surjective
étale chart over which the scheme-theoretic closure of the inverse image is everything already
forces the scheme-theoretic closure of `U` in `X` to be everything. -/
@[stacks 0833]
theorem isSchemeTheoreticallyDense_iff_exists_surjective_etale_chart
    (hX : IsAlgebraicSpace B S hS X) (U : Subfunctor X) (hU : IsOpenSubspace B S hS U) :
    IsSchemeTheoreticallyDense B S hS U ↔
      ∃ (V : BigFppfOver B S hS) (φ : yoneda.obj V ⟶ X),
        IsSurjective B S hS φ ∧ IsEtale B S hS φ ∧
          ∀ (W : BigFppfOver B S hS) (ψ : W ⟶ V),
            AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ψ) →
              schemeTheoreticClosure B S hS (U.preimage (yoneda.map ψ ≫ φ)) = ⊤ := by
  constructor
  · intro hdense
    obtain ⟨V, φ, hsurj, hetale⟩ := hX.exists_atlas
    refine ⟨V, φ, (presheafSurjective_iff_isSurjective_yoneda B S hS X hX V φ).1 hsurj,
      isEtale_of_presheafEtale B S hS φ hetale, fun W ψ hψ => ?_⟩
    have hψE : Etale ((BigFppfOver.toScheme B S hS).map ψ) :=
      @AlgebraicGeometry.Etale.instOfIsOpenImmersion _ _ _ hψ
    exact hdense (isAlgebraicSpace_yoneda B S hS W) (yoneda.map ψ ≫ φ)
      (isEtale_of_presheafEtale B S hS _
        (isEtale_of_presheafEtale B S hS φ hetale W (yoneda.map ψ)
          (presheaf_yoneda_map_of_property B S hS (@Etale.{u}) ψ hψE)))
  · rintro ⟨V, φ, hsurj, hφetale, hdense⟩
    have hφps : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf φ :=
      presheafEtale_of_isEtale_chart B S hS φ hφetale
    have hφsurj : (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf φ :=
      (presheafSurjective_iff_isSurjective_yoneda B S hS X hX V φ).2 hsurj
    have hsndφ := isOpenImmersion_snd B S hS hU.2 φ
    have hVdense := isSchemeTheoreticallyDense_opensRange_snd_of_forall B S hS hU.2 φ
      fun P => hdense (siteOpenObject B S hS V P) (siteOpenObject_ι B S hS V P)
        (isOpenImmersion_siteOpenObject_ι B S hS V P)
    rw [isSchemeTheoreticallyDense_iff_forall_chart]
    intro C
    obtain ⟨T, q, pfst, hpb⟩ := hφps.rep C.1.hom
    obtain ⟨p, rfl⟩ := yoneda.map_surjective pfst
    have hbase := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))
    have hpE₀ := MorphismProperty.of_relative_map (hbase.of_isPullback hpb.flip C.2)
    have hpE : Etale ((BigFppfOver.toScheme B S hS).map p) := hpE₀
    have hqE := hbase.of_isPullback hpb hφps
    have hqS := (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback hpb hφsurj
    have hpQF : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map p) :=
      locallyQuasiFinite_of_etale _ hpE
    have hTdense := isSchemeTheoreticallyDense_preimage
      ((BigFppfOver.toScheme B S hS).map p) hVdense
    exact schemeTheoreticImageSubfunctor_preimage_eq_top_of_isPullback B S hS hU.2 φ _ q p hpb
      hqE hqS hTdense

/-! ### The inverse image of a dense open subspace along a flat morphism

Stacks 0832 pulls a scheme-theoretically dense open subscheme back along a morphism of schemes
which is flat, locally of finite presentation **and locally quasi-finite**. The quasi-finiteness
is not needed: Stacks 05IE makes the regular functions upstairs a projective module over the
regular functions downstairs after an affine elementary etale localization of source and target,
and a global function vanishing on the inverse image of the dense open is then killed, coordinate
by coordinate in a free module containing that projective module, by a power of every function
whose basic open lies in the dense open. That is
`AlgebraicGeometry.Space.scheme_dense_preimage_flat_lfp`, and the chart criterion of Stacks 0833
carries it to algebraic spaces exactly as in the proof of Stacks 0833 itself. -/

/-- Restriction of regular functions to a scheme-theoretically dense open subscheme is
injective. -/
public lemma dense_restrict_injective {A : Scheme.{u}} (U : A.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) :
    Function.Injective (A.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  have hmono : Mono U.ι.c :=
    (isSchemeTheoreticallyDense_opensRange_iff_mono U.ι).mp (by simpa using hU)
  have : Mono (U.ι.c.app (op ⊤)) := inferInstance
  have hi : Function.Injective (U.ι.appTop) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp (by assumption)
  let q := A.presheaf.map (eqToHom (U.ι_image_top)).op
  have hc : U.ι.appTop = A.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ q := by
    dsimp [q]
    rw [← Functor.map_comp]
    rfl
  intro a b hab
  apply hi
  rw [hc]
  exact congrArg (fun z => q z) hab

/-- An element of a projective module killed by a power of each of a family of scalars which
only kills zero is itself zero: read the element off in a free module containing the projective
one and apply the hypothesis to each coordinate. -/
public lemma eq_zero_of_forall_pow_smul_eq_zero
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Projective R M] {ι : Type*} (s : ι → R)
    (hR : ∀ r : R, (∀ i, ∃ n : ℕ, s i ^ n * r = 0) → r = 0)
    (m : M) (hm : ∀ i, ∃ n : ℕ, s i ^ n • m = 0) : m = 0 := by
  obtain ⟨σ, hσ⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  have heq : σ m = 0 := by
    ext k
    apply hR
    intro i
    obtain ⟨n, hn⟩ := hm i
    refine ⟨n, ?_⟩
    have h := congrArg (fun x => σ x k) hn
    simpa using h
  have h := LinearMap.congr_fun hσ m
  simpa [heq] using h.symm

/-- A regular function on an affine scheme killed by a power of every function whose basic open
is contained in a scheme-theoretically dense open subscheme is zero: its restriction to that
open subscheme has vanishing germ at every point, and restriction there is injective. -/
public lemma eq_zero_of_dense_basicOpen_pow {A : Scheme.{u}} [IsAffine A]
    (U : A.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) (r : Γ(A, ⊤))
    (hr : ∀ s : {s : Γ(A, ⊤) // A.basicOpen s ≤ U}, ∃ n : ℕ, s.val ^ n * r = 0) :
    r = 0 := by
  apply dense_restrict_injective U hU
  rw [map_zero]
  apply TopCat.Presheaf.section_ext A.sheaf U _ 0
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (isAffineOpen_top A).exists_basicOpen_le ⟨x, hx⟩ trivial
  obtain ⟨n, hn⟩ := hr ⟨s, hs⟩
  have hu : IsUnit (A.presheaf.germ ⊤ x trivial s) := (A.mem_basicOpen s x trivial).mp hxs
  have hz := congrArg (fun z => A.presheaf.germ ⊤ x trivial z) hn
  simp only [map_mul, map_pow, map_zero] at hz
  have hr0 : A.presheaf.germ ⊤ x trivial r = 0 := (hu.pow n).mul_right_eq_zero.mp hz
  change A.presheaf.germ U x hx
    (A.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) = A.presheaf.germ U x hx 0
  rw [TopCat.Presheaf.germ_res_apply, map_zero]
  exact hr0

/-- A regular function on an affine scheme whose regular functions are projective over those of
an affine base, vanishing on the inverse image of a scheme-theoretically dense open subscheme of
the base, is zero. -/
public lemma eq_zero_of_restrict_preimage_eq_zero
    {A A' : Scheme.{u}} [IsAffine A] [IsAffine A'] (f : A ⟶ A')
    (U : A'.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hproj : letI : Module Γ(A', ⊤) Γ(A, ⊤) := Module.compHom _ f.appTop.hom
      Module.Projective Γ(A', ⊤) Γ(A, ⊤))
    (m : Γ(A, ⊤))
    (hm : A.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op m = 0) : m = 0 := by
  let : Module Γ(A', ⊤) Γ(A, ⊤) := Module.compHom _ f.appTop.hom
  let : Module.Projective Γ(A', ⊤) Γ(A, ⊤) := hproj
  apply eq_zero_of_forall_pow_smul_eq_zero
    (fun s : {s : Γ(A', ⊤) // A'.basicOpen s ≤ U} => s.val)
    (fun r hr => eq_zero_of_dense_basicOpen_pow U hU r hr) m
  intro s
  have hle : A.basicOpen (f.appTop s.val) ≤ f ⁻¹ᵁ U := by
    rw [← f.preimage_basicOpen_top]
    exact (TopologicalSpace.Opens.map f.base).monotone s.property
  have hz : A.presheaf.map (homOfLE (A.basicOpen_le (f.appTop s.val))).op m = 0 := by
    have hh := congrArg (fun z => A.presheaf.map (homOfLE hle).op z) hm
    simpa only [← CommRingCat.comp_apply, ← Functor.map_comp,
      ← op_comp, map_zero, homOfLE_comp] using hh
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen A
    (isAffineOpen_top A) m (f.appTop s.val) hz
  refine ⟨n, ?_⟩
  change f.appTop.hom (s.val ^ n) * m = 0
  simpa only [map_pow] using hn

/-- The pullback of a regular function vanishing on an open subscheme vanishes on the inverse
image of that open subscheme: this is naturality of the structure-sheaf map. -/
public lemma restriction_pullback_eq_zero {A A' : Scheme.{u}}
    (f : A ⟶ A') (U : A'.Opens) (s : Γ(A', ⊤))
    (hs : A'.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0) :
    A.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op (f.appTop s) = 0 := by
  have he : f.appTop ≫ A.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op =
      A'.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ f.app U :=
    (f.c.naturality (homOfLE (show U ≤ ⊤ from le_top)).op).symm
  have h := congrArg (fun k => k s) he
  simpa only [ConcreteCategory.comp_apply, hs, map_zero] using h

/-- The stalk maps of a flat morphism of schemes are injective: a flat local homomorphism of
local rings is faithfully flat. -/
public lemma flat_stalkMap_injective {A A' : Scheme.{u}} (f : A ⟶ A') [Flat f] (x : A) :
    Function.Injective (f.stalkMap x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (A'.presheaf.stalk (f x)) (A.presheaf.stalk x) := Flat.stalkMap f x
  have : IsLocalHom (algebraMap (A'.presheaf.stalk (f x)) (A.presheaf.stalk x)) :=
    show IsLocalHom (f.stalkMap x).hom from inferInstance
  have : Module.FaithfullyFlat (A'.presheaf.stalk (f x)) (A.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective _ _

/-- A global regular function on the source of a flat morphism locally of finite presentation
which vanishes on the inverse image of a scheme-theoretically dense open subscheme of the target
is zero.

Around a point of the source, Stacks 05IE provides affine elementary etale neighbourhoods
`W ⟶ A` and `V ⟶ A'` fitting in a commuting square with `h : W ⟶ V` whose regular functions are
projective over those of `V`. The inverse image of the dense open in `V` is again dense, by
Stacks 0832 applied to the etale -- hence locally quasi-finite -- morphism `V ⟶ A'`, so the
pullback of the function to `W` vanishes; injectivity of the stalk map of the flat morphism
`W ⟶ A` then kills the germ at the point. -/
public lemma eq_zero_of_restrict_flat_lfp_preimage
    {A A' : Scheme.{u}} (f : A ⟶ A') [Flat f] [LocallyOfFinitePresentation f]
    (U : A'.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) (m : Γ(A, ⊤))
    (hm : A.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op m = 0) : m = 0 := by
  apply TopCat.Presheaf.section_ext A.sheaf ⊤ m 0
  intro x hx
  obtain ⟨V, W, h, _, _, hc, _, hW, hV, hproj⟩ :=
    exists_elementaryEtaleNeighborhood_projective_structureSheafSections_of_isFlatAt
      f x ((Flat.iff_flat_stalkMap f).mp inferInstance x)
  let := hW
  let := hV
  let := locallyQuasiFinite_of_etale V.toBase inferInstance
  have hdense := isSchemeTheoreticallyDense_preimage V.toBase hU
  have hp : h ⁻¹ᵁ (V.toBase ⁻¹ᵁ U) = W.toBase ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hc, Scheme.Hom.comp_preimage]
  have hm' := restriction_pullback_eq_zero W.toBase (f ⁻¹ᵁ U) m hm
  rw [← hp] at hm'
  have hz := eq_zero_of_restrict_preimage_eq_zero h _ hdense hproj (W.toBase.appTop m) hm'
  have hzero : ∀ (y : A) (hy : y ∈ (⊤ : A.Opens)), y = W.toBase W.point →
      A.presheaf.germ ⊤ y hy m = 0 := by
    intro y hy hyeq
    subst hyeq
    apply flat_stalkMap_injective W.toBase W.point
    rw [map_zero, Scheme.Hom.germ_stalkMap_apply]
    change W.scheme.presheaf.germ ⊤ W.point (TopologicalSpace.Opens.mem_top W.point)
      (W.toBase.appTop m) = 0
    rw [hz, map_zero]
  have hx' := W.map_point
  change W.toBase W.point = x at hx'
  change A.presheaf.germ ⊤ x hx m = A.presheaf.germ ⊤ x hx 0
  rw [map_zero]
  exact hzero x hx hx'.symm

/-- **Stacks 0832 without the quasi-finiteness hypothesis.** The inverse image of a
scheme-theoretically dense open subscheme under a flat morphism of schemes locally of finite
presentation is scheme-theoretically dense.

Density of the inverse image is injectivity of the structure-sheaf map of its inclusion, which
is tested on sections over an arbitrary open subscheme of the source; transporting such a
section to the global sections of that open subscheme reduces the claim to
`AlgebraicGeometry.Space.eq_zero_of_restrict_flat_lfp_preimage` for the composite of its
inclusion with the given morphism. -/
@[ega "IV 20.5.7" "more general"]
public lemma scheme_dense_preimage_flat_lfp
    {A A' : Scheme.{u}} (f : A ⟶ A') [Flat f] [LocallyOfFinitePresentation f]
    (U : A'.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) :
    Scheme.Opens.IsSchemeTheoreticallyDense (f ⁻¹ᵁ U) := by
  let P := f ⁻¹ᵁ U
  suffices Mono P.ι.c from by
    simpa only [Scheme.Opens.opensRange_ι] using
      (isSchemeTheoreticallyDense_opensRange_iff_mono P.ι).mpr this
  rw [NatTrans.mono_iff_mono_app]
  intro W
  apply (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr
  change Function.Injective (P.ι.app W.unop)
  rw [injective_iff_map_eq_zero]
  intro s hs
  let O : A.Opens := W.unop
  let D := O.ι ⁻¹ᵁ P
  have heq : O.ι ''ᵁ D = P.ι ''ᵁ (P.ι ⁻¹ᵁ O) := by
    simp only [D, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_comm]
  let n := O.topIso.inv s
  have hn : O.toScheme.presheaf.map
      (homOfLE (show (O.ι ≫ f) ⁻¹ᵁ U ≤ ⊤ from le_top)).op n = 0 := by
    have hs' : A.presheaf.map (homOfLE (P.ι.image_preimage_le O)).op s = 0 := hs
    have hcast : A.presheaf.map (eqToHom heq).op
        (A.presheaf.map (homOfLE (P.ι.image_preimage_le O)).op s) = 0 := by
      rw [hs', map_zero]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at hcast
    rw [Scheme.Hom.comp_preimage]
    change (ConcreteCategory.hom (A.presheaf.map
        ((Scheme.Hom.opensFunctor O.ι).map (homOfLE (show D ≤ ⊤ from le_top))).op))
      ((ConcreteCategory.hom (A.presheaf.map (eqToHom O.ι_image_top).op)) s) = 0
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    exact hcast
  have hn0 := eq_zero_of_restrict_flat_lfp_preimage (O.ι ≫ f) U hU n hn
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback O.topIso.inv).mp
    inferInstance (by simpa [n] using hn0)

/-- **The inverse image of a scheme-theoretically dense open subspace along a flat morphism of
algebraic spaces locally of finite presentation is scheme-theoretically dense.**

This is the transport of Stacks 0832 to algebraic spaces, with the quasi-finiteness hypothesis
of that lemma removed, and it is proved exactly like the hard direction of Stacks 0833 above.
Fix a surjective etale scheme chart `φ : V ⟶ Y` of the target. Density of `U` applied to the
open subschemes of `V`, read through
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_preimage_eq_top_iff`, says that the open
subscheme of `V` representing `U ×_Y V` is scheme-theoretically dense. For a chart `C` of the
source the two are compared over `T = V ×_Y C`: the projection `T ⟶ V` is a base change of
`C ⟶ X ⟶ Y`, so it is flat and locally of finite presentation -- but *not* quasi-finite, which
is why Stacks 0832 itself does not suffice and
`AlgebraicGeometry.Space.scheme_dense_preimage_flat_lfp` is used in its place -- and it carries
that density to `T`. The projection `T ⟶ C` is a base change of `φ`, hence surjective etale, and
`AlgebraicGeometry.Space.subfunctor_eq_top_of_isSurjective_isEtale_preimage` descends the closure
over `T` to the closure over `C`. -/
theorem isSchemeTheoreticallyDense_preimage_of_isFlat
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (U : Subfunctor Y) (hU : IsOpenSubspace B S hS U)
    (hdense : IsSchemeTheoreticallyDense B S hS U) :
    IsSchemeTheoreticallyDense B S hS (U.preimage f) := by
  obtain ⟨V, φ, hφsurj, hφps⟩ := hY.exists_atlas
  have hφE : IsEtale B S hS φ := isEtale_of_presheafEtale B S hS φ hφps
  have hsndφ := isOpenImmersion_snd B S hS hU.2 φ
  have hVdense := isSchemeTheoreticallyDense_opensRange_snd_of_forall B S hS hU.2 φ
    fun P => hdense (isAlgebraicSpace_yoneda B S hS (siteOpenObject B S hS V P))
      (yoneda.map (siteOpenObject_ι B S hS V P) ≫ φ)
      (isEtale_of_presheafEtale B S hS _
        (hφE _ (yoneda.map (siteOpenObject_ι B S hS V P))
          (presheaf_yoneda_map_of_property B S hS (@Etale.{u}) _
            (@AlgebraicGeometry.Etale.instOfIsOpenImmersion _ _ _
              (isOpenImmersion_siteOpenObject_ι B S hS V P)))))
  rw [isSchemeTheoreticallyDense_iff_forall_chart]
  intro C
  rw [← Subfunctor.preimage_comp U C.1.hom f]
  obtain ⟨T, q, pfst, hpb⟩ := hφps.rep (C.1.hom ≫ f)
  obtain ⟨p, rfl⟩ := yoneda.map_surjective pfst
  have hbase := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have hqE := hbase.of_isPullback hpb hφps
  have hqS := (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback hpb hφsurj
  have ha' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ C.1.hom) := by
    have := etale_isStableUnderComposition.{u}
    have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
      MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
    have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    exact MorphismProperty.comp_mem _ (yoneda.map q) C.1.hom hqE C.2
  have hcomm : yoneda.map p ≫ φ = (yoneda.map q ≫ C.1.hom) ≫ f :=
    hpb.w.trans (Category.assoc _ _ _).symm
  have hpFlat : Flat ((BigFppfOver.toScheme B S hS).map p) :=
    hflat T V (yoneda.map q ≫ C.1.hom) φ p ha' hφps hcomm
  have hpLFP : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p) :=
    hlfp T V (yoneda.map q ≫ C.1.hom) φ p ha' hφps hcomm
  have := hpFlat
  have := hpLFP
  have hTdense := scheme_dense_preimage_flat_lfp ((BigFppfOver.toScheme B S hS).map p)
    ((BigFppfOver.toScheme B S hS).map (hU.2.rep.snd φ)).opensRange hVdense
  exact schemeTheoreticImageSubfunctor_preimage_eq_top_of_isPullback B S hS hU.2 φ _ q p hpb
    hqE hqS hTdense

end Density

end Space

end AlgebraicGeometry

end
