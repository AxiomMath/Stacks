module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeAffineDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FaithfullyFlatSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleHomLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Charts for the affineness of a space carrying a lifted étale presentation

* Morphisms of schemes into a spectrum attached to ring homomorphisms into global sections
  (`AlgebraicGeometry.Space.toSpecOfRingHom`), and their cancellation along surjective flat
  morphisms.
* Objects of the big fppf site of the terminal scheme given by spectra of countable rings, and the
  restrictions of their representable presheaves to the big fppf site of `S`: a morphism of
  schemes `W ⟶ Spec P` from an object over `S` is a morphism `h_W ⟶ j⁻¹ h_{Spec P}`
  (`AlgebraicGeometry.Space.eltInt`), and a cartesian square of schemes is a cartesian square of
  these presheaves (`AlgebraicGeometry.Space.isPullback_eltInt`).
* Two étale spaces over `X` whose base changes to a thickening `G ⊂ X` are identified are
  isomorphic over `X` (`AlgebraicGeometry.Space.exists_iso_of_isPullback_of_isThickening`), the
  full faithfulness of Stacks 05ZH in the form of
  `AlgebraicGeometry.Space.existsUnique_hom_presheaf_of_isThickening`.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

universe u

/-! ### Morphisms of schemes into a spectrum, read through a ring homomorphism -/

/-- The morphism `X ⟶ Spec P` attached to a ring homomorphism `P →+* Γ(X, ⊤)`. -/
noncomputable abbrev toSpecOfRingHom {X : Scheme.{u}} {P : Type u} [CommRing P]
    (γ : P →+* Γ(X, ⊤)) : X ⟶ Spec (.of P) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom γ)

/-- Precomposing `toSpecOfRingHom γ` with `k` is `toSpecOfRingHom` of `γ` followed by the map of
global sections of `k`. -/
theorem comp_toSpecOfRingHom {X Y : Scheme.{u}} {P : Type u} [CommRing P] (k : X ⟶ Y)
    (γ : P →+* Γ(Y, ⊤)) :
    k ≫ toSpecOfRingHom γ = toSpecOfRingHom (k.appTop.hom.comp γ) := by
  rw [toSpecOfRingHom, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ← Spec.map_comp]
  rfl

/-- Two morphisms into a spectrum which agree after a surjective flat morphism agree. -/
theorem eq_of_comp_eq_of_flat_of_surjective {X Y Z : Scheme.{u}} [IsAffine Z] (p : X ⟶ Y)
    [Flat p] [Surjective p] {f₁ f₂ : Y ⟶ Z} (h : p ≫ f₁ = p ≫ f₂) : f₁ = f₂ := by
  refine ext_of_isAffine ?_
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h'
  ext x
  exact Scheme.Hom.appTop_injective_of_flat_of_surjective p (ConcreteCategory.congr_hom h' x)

/-! ### Objects of the big fppf site of the terminal scheme -/

variable (B : BigFppfSite.{u})

/-- The big fppf category over the terminal scheme `Spec ℤ`. -/
abbrev IntOver := BigFppfOver B (⊤_ Scheme.{u}) (BigFppfSite.contains_terminal B)

/-- The spectrum of a countable ring is an object of the site. -/
theorem contains_spec_of_countable (R : Type u) [CommRing R] [Countable R] :
    B.Contains (Spec (.of R)) :=
  BigFppfSite.contains_spec_of_mk_lt_cutoff B
    ((Cardinal.mk_le_aleph0 (α := R)).trans_lt B.aleph0_lt_cutoff)

/-- The spectrum of a countable ring as an object of the big fppf site of `Spec ℤ`. -/
noncomputable abbrev specInt (R : Type u) [CommRing R] [Countable R] : IntOver B :=
  BigFppfOver.mk B _ _ (contains_spec_of_countable B R) (terminal.from _)

/-- A morphism of schemes between objects of the site over `Spec ℤ`, read in the site. -/
noncomputable abbrev intHom {W Y : IntOver B}
    (t : (BigFppfOver.toScheme B _ _).obj W ⟶ (BigFppfOver.toScheme B _ _).obj Y) : W ⟶ Y :=
  overMapOfSchemeHom B _ _ terminalIsTerminal W Y t

/-- The morphism of schemes underlying `intHom B t` is `t`. -/
theorem toScheme_map_intHom {W Y : IntOver B}
    (t : (BigFppfOver.toScheme B _ _).obj W ⟶ (BigFppfOver.toScheme B _ _).obj Y) :
    (BigFppfOver.toScheme B _ _).map (intHom B t) = t :=
  B.inclusion.map_preimage t

/-- A morphism of the site over `Spec ℤ` is `intHom` of its underlying morphism of schemes. -/
theorem intHom_toScheme_map {W Y : IntOver B} (k : W ⟶ Y) :
    intHom B ((BigFppfOver.toScheme B _ _).map k) = k :=
  BigFppfOver.map_toScheme_injective B _ _ (toScheme_map_intHom B _)

/-! ### Elements of a restricted representable presheaf -/

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism `S ⟶ Spec ℤ` in the site. -/
noncomputable abbrev toInt : B.obj hS ⟶ B.obj (BigFppfSite.contains_terminal B) :=
  ObjectProperty.homMk (terminal.from S)

variable {B S hS}

/-- A morphism of schemes `W ⟶ Y` from an object over `S` to an object over `Spec ℤ`, read as a
morphism from `h_W` to the restriction of `h_Y` to the site of `S`. -/
noncomputable def eltInt {W : BigFppfOver B S hS} {Y : IntOver B}
    (t : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B _ _).obj Y) :
    yoneda.obj W ⟶ (relocalizeRestrict (toInt B S hS)).obj (yoneda.obj Y) :=
  yonedaEquiv.symm (intHom B (W := (Over.map (toInt B S hS)).obj W) t)

/-- The morphism of schemes underlying the element of the restricted presheaf corresponding to
`eltInt t` is `t`. -/
theorem toScheme_map_yonedaEquiv_eltInt {W : BigFppfOver B S hS} {Y : IntOver B}
    (t : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B _ _).obj Y) :
    (BigFppfOver.toScheme B _ _).map (yonedaEquiv (eltInt t)) = t := by
  rw [eltInt, Equiv.apply_symm_apply]
  exact toScheme_map_intHom B (W := (Over.map (toInt B S hS)).obj W) t

/-- `eltInt` is injective. -/
theorem eltInt_injective {W : BigFppfOver B S hS} {Y : IntOver B}
    {t₁ t₂ : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B _ _).obj Y}
    (h : eltInt t₁ = eltInt t₂) : t₁ = t₂ := by
  rw [← toScheme_map_yonedaEquiv_eltInt t₁, ← toScheme_map_yonedaEquiv_eltInt t₂, h]

/-- Every morphism from `h_W` to the restriction of `h_Y` is `eltInt t` for some morphism of
schemes `t`. -/
theorem exists_eq_eltInt {W : BigFppfOver B S hS} {Y : IntOver B}
    (m : yoneda.obj W ⟶ (relocalizeRestrict (toInt B S hS)).obj (yoneda.obj Y)) :
    ∃ t, m = eltInt t :=
  ⟨(BigFppfOver.toScheme B _ _).map (yonedaEquiv m), by
    rw [eltInt, intHom_toScheme_map, Equiv.symm_apply_apply]⟩

/-- Precomposing `eltInt t` with `h_k` is `eltInt` of the composite of `k` and `t`. -/
theorem yoneda_map_comp_eltInt {W W' : BigFppfOver B S hS} {Y : IntOver B} (k : W' ⟶ W)
    (t : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B _ _).obj Y) :
    yoneda.map k ≫ eltInt t = eltInt ((BigFppfOver.toScheme B S hS).map k ≫ t) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  apply (BigFppfOver.toScheme B _ _).map_injective
  show (BigFppfOver.toScheme B _ _).map ((Over.map (toInt B S hS)).map k ≫ yonedaEquiv (eltInt t))
    = _
  rw [Functor.map_comp, toScheme_map_yonedaEquiv_eltInt, toScheme_map_yonedaEquiv_eltInt]
  rfl

/-- Postcomposing `eltInt t` with the restriction of `h_e` is `eltInt` of the composite of `t` and
`e`. -/
theorem eltInt_comp_map {W : BigFppfOver B S hS} {Y Y' : IntOver B} (e : Y ⟶ Y')
    (t : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B _ _).obj Y) :
    eltInt t ≫ (relocalizeRestrict (toInt B S hS)).map (yoneda.map e) =
      eltInt (t ≫ (BigFppfOver.toScheme B _ _).map e) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  apply (BigFppfOver.toScheme B _ _).map_injective
  show (BigFppfOver.toScheme B _ _).map (yonedaEquiv (eltInt t) ≫ e) = _
  rw [Functor.map_comp, toScheme_map_yonedaEquiv_eltInt, toScheme_map_yonedaEquiv_eltInt]

/-- The component of `eltInt t` at `W'` sends `k : W' ⟶ W` to the composite of `k` and `t`. -/
theorem eltInt_app {W W' : BigFppfOver B S hS} {Y : IntOver B} (k : W' ⟶ W)
    (t : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B _ _).obj Y) :
    (BigFppfOver.toScheme B _ _).map ((eltInt t).app (op W') k) =
      (BigFppfOver.toScheme B S hS).map k ≫ t := by
  have h := congrArg (fun m => (BigFppfOver.toScheme B _ _).map (yonedaEquiv m))
    (yoneda_map_comp_eltInt k t)
  simp only [toScheme_map_yonedaEquiv_eltInt] at h
  rw [← h, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- **A cartesian square of schemes from an object over `S` to objects over `Spec ℤ` is a cartesian
square of presheaves on the site of `S`.** The two right-hand corners are the restrictions of
the representable presheaves of the objects over `Spec ℤ`. -/
theorem isPullback_eltInt {U' T' : BigFppfOver B S hS} {E Y : IntOver B} (π : U' ⟶ T')
    (e : E ⟶ Y) (a : (BigFppfOver.toScheme B S hS).obj U' ⟶ (BigFppfOver.toScheme B _ _).obj E)
    (τ : (BigFppfOver.toScheme B S hS).obj T' ⟶ (BigFppfOver.toScheme B _ _).obj Y)
    (sq : IsPullback a ((BigFppfOver.toScheme B S hS).map π)
      ((BigFppfOver.toScheme B _ _).map e) τ) :
    IsPullback (eltInt a) (yoneda.map π) ((relocalizeRestrict (toInt B S hS)).map (yoneda.map e))
      (eltInt τ) := by
  have hw : eltInt a ≫ (relocalizeRestrict (toInt B S hS)).map (yoneda.map e) =
      yoneda.map π ≫ eltInt τ := by
    rw [eltInt_comp_map, yoneda_map_comp_eltInt, sq.w]
  refine IsPullback.of_forall_isPullback_app fun W => ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun m => m.app W) hw, ?_, ?_⟩
  · rintro (k₁ : W.unop ⟶ U') (k₂ : W.unop ⟶ U') ⟨h₁, h₂⟩
    have h₁' := congrArg (BigFppfOver.toScheme B _ _).map h₁
    rw [eltInt_app, eltInt_app] at h₁'
    have h₂' : (BigFppfOver.toScheme B S hS).map k₁ ≫ (BigFppfOver.toScheme B S hS).map π =
        (BigFppfOver.toScheme B S hS).map k₂ ≫ (BigFppfOver.toScheme B S hS).map π := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (BigFppfOver.toScheme B S hS).map h₂
    exact (BigFppfOver.toScheme B S hS).map_injective (sq.hom_ext h₁' h₂')
  · rintro (x : (Over.map (toInt B S hS)).obj W.unop ⟶ E) (t : W.unop ⟶ T') hxt
    have hxt' : (BigFppfOver.toScheme B _ _).map x ≫ (BigFppfOver.toScheme B _ _).map e =
        (BigFppfOver.toScheme B S hS).map t ≫ τ := by
      rw [← Functor.map_comp, ← eltInt_app]
      exact congrArg (BigFppfOver.toScheme B _ _).map hxt
    let ℓ := sq.lift _ _ hxt'
    let k : W.unop ⟶ U' := Over.homMk (ObjectProperty.homMk ℓ) (by
      apply ObjectProperty.hom_ext
      show ℓ ≫ B.inclusion.map U'.hom = B.inclusion.map W.unop.hom
      rw [← Over.w π, Functor.map_comp, ← Category.assoc]
      show (ℓ ≫ (BigFppfOver.toScheme B S hS).map π) ≫ _ = _
      rw [sq.lift_snd]
      show B.inclusion.map t.left ≫ _ = _
      rw [← Functor.map_comp, Over.w t])
    have hk : (BigFppfOver.toScheme B S hS).map k = ℓ := rfl
    refine ⟨k, ?_, ?_⟩
    · apply (BigFppfOver.toScheme B _ _).map_injective
      rw [eltInt_app, hk, sq.lift_fst]
    · apply (BigFppfOver.toScheme B S hS).map_injective
      show (BigFppfOver.toScheme B S hS).map (k ≫ π) = _
      rw [Functor.map_comp, hk, sq.lift_snd]

/-- The restriction to the site of `S` of an étale morphism of the site of `Spec ℤ` is étale after
every representable base change. -/
theorem presheaf_etale_relocalizeRestrict_map {E Y : IntOver B} (e : E ⟶ Y)
    (he : Etale ((BigFppfOver.toScheme B _ _).map e)) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        ((relocalizeRestrict (toInt B S hS)).map (yoneda.map e)) := by
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  exact relative_relocalizeRestrict_map (toInt B S hS) (fun _ hs => hs)
    ((presheaf_yoneda_map_etale_iff B _ _ e).2 he)

/-- **Two étale spaces over `X` with the same base change to a thickening are isomorphic.** Let
`G ⊂ X` be a thickening, `φ : h_V ⟶ X` étale with base change `h_U` to `G`, and `w : E ⟶ X` étale
with `E` an algebraic space and the same base change `h_U` to `G`. Then `h_V ≅ E` over `X`,
compatibly with the two maps from `h_U`. This is the full faithfulness half of Stacks 05ZH, in
the form of `AlgebraicGeometry.Space.existsUnique_hom_presheaf_of_isThickening`. -/
theorem exists_iso_of_isPullback_of_isThickening {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (hG : IsThickening B S hS X G) {V U : BigFppfOver B S hS}
    {φ : yoneda.obj V ⟶ X.1} (hφ : IsEtale B S hS φ) (ιU : U ⟶ V)
    (q : yoneda.obj U ⟶ G.toFunctor) (sqU : IsPullback (yoneda.map ιU) q φ G.ι)
    {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hE : IsAlgebraicSpace B S hS E) {w : E ⟶ X.1}
    (hw : IsEtale B S hS w) (d : yoneda.obj U ⟶ E) (sqE : IsPullback d q w G.ι) :
    ∃ i : yoneda.obj V ≅ E, i.hom ≫ w = φ ∧ yoneda.map ιU ≫ i.hom = d := by
  let f := IsThickening.inclusion B S hS hG
  have _ : Mono f.hom := inferInstanceAs (Mono G.ι)
  have hT : IsThickening B S hS X (Subfunctor.range f.hom) := by
    show IsThickening B S hS X (Subfunctor.range G.ι)
    rwa [Subfunctor.range_ι]
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  obtain ⟨α, ⟨hα₁, hα₂⟩, -⟩ := existsUnique_hom_presheaf_of_isThickening B S hS f hT hV hE
    sqU w hw d (sqE.w.trans sqU.w.symm)
  obtain ⟨β, ⟨hβ₁, hβ₂⟩, -⟩ := existsUnique_hom_presheaf_of_isThickening B S hS f hT hE hV
    sqE φ hφ (yoneda.map ιU) (sqU.w.trans sqE.w.symm)
  have h₁ : α ≫ β = 𝟙 _ := hom_ext_presheaf_of_isThickening_range B S hS f hT hV hV sqU φ hφ _ _
    (by rw [Category.assoc, hβ₂, hα₂]) (Category.id_comp _)
    (by rw [← Category.assoc, hα₁, hβ₁, Category.comp_id])
  have h₂ : β ≫ α = 𝟙 _ := hom_ext_presheaf_of_isThickening_range B S hS f hT hE hE sqE w hw _ _
    (by rw [Category.assoc, hα₂, hβ₂]) (Category.id_comp _)
    (by rw [← Category.assoc, hβ₁, hα₁, Category.comp_id])
  exact ⟨⟨α, β, h₁, h₂⟩, hα₂, hα₁⟩

/-- **The kernel of a surjective morphism of affine schemes on global sections is nil.** -/
theorem ker_appTop_le_nilradical_of_surjective {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [Surjective f] : RingHom.ker f.appTop.hom ≤ nilradical Γ(Y, ⊤) := by
  have hSpec : Spec.map f.appTop = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  have _ : Surjective (Spec.map f.appTop) := by
    rw [hSpec]
    infer_instance
  have hc : Function.Surjective (PrimeSpectrum.comap f.appTop.hom) :=
    (surjective_iff (Spec.map f.appTop)).mp inferInstance
  intro x hx
  rw [nilradical_eq_sInf, Submodule.mem_sInf]
  intro p hp
  obtain ⟨q, hq⟩ := hc ⟨p, hp⟩
  have : x ∈ (PrimeSpectrum.comap f.appTop.hom q).asIdeal := by
    show f.appTop.hom x ∈ q.asIdeal
    rw [RingHom.mem_ker.mp hx]
    exact q.asIdeal.zero_mem
  rwa [hq] at this

/-- The base change to the chart `V` of the inclusion of a thickening `G ⊂ X` is a surjective
morphism of schemes. -/
theorem surjective_of_isPullback_of_isThickening {X : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (hG : IsThickening B S hS X G) {V U : BigFppfOver B S hS}
    {φ : yoneda.obj V ⟶ X.1} (ιU : U ⟶ V) (q : yoneda.obj U ⟶ G.toFunctor)
    (sqU : IsPullback (yoneda.map ιU) q φ G.ι) :
    Surjective ((BigFppfOver.toScheme B S hS).map ιU) := by
  let W : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  have sq : IsPullback (ObjectProperty.homMk q : W ⟶ IsThickening.space B S hS hG)
      (ObjectProperty.homMk (yoneda.map ιU) : W ⟶ Y) (IsThickening.inclusion B S hS hG)
      (ObjectProperty.homMk φ : Y ⟶ X) :=
    IsPullback.of_map (F := ObjectProperty.ι _) (ObjectProperty.hom_ext _ sqU.w.symm) sqU.flip
  exact (presheaf_yoneda_map_iff B S hS inferInstance ιU).mp
    ((surjective_yonedaMap_iff_surjective_pointsMap B S hS ιU).mpr
      (isSurjective_of_isPullback B S hS sq hG.2))

end AlgebraicGeometry.Space

end
