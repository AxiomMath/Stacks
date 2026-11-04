module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorQuotient
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorSupportedSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.PrincipalCenterHDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSheafCriterion

/-!
# Recognizing the almost blowup squares of More on Flatness, Examples 0EVG and 0EVH

More on Flatness, Example 0EVG is the almost blowup square with base `Spec A`, centre cut out by
an element `f ∈ A`, and modification the closed immersion `Spec (A/J) ⟶ Spec A` for a finitely
generated ideal `J` annihilated by a power of `f`. This file recognizes that shape intrinsically:
over an affine base `V` whose centre is cut out by a single global section `t`, a closed immersion
of finite presentation which is an isomorphism away from the centre has the shape of Example 0EVG.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_isoSpec_hom_ofIdealTop`: on an affine scheme
  `V`, the ideal sheaf attached to an ideal `𝔞` of `Γ(V, ⊤)` is the inverse image along
  `V ≅ Spec Γ(V, ⊤)` of the ideal sheaf `𝔞` defines on `Spec Γ(V, ⊤)`.
* `AlgebraicGeometry.exists_pow_mul_eq_zero_of_comap_eq_bot`: a closed immersion of finite
  presentation into an affine scheme which is an isomorphism away from the zero locus of a global
  section `t` has its ideal annihilated by a power of `t`.
* `AlgebraicGeometry.isOneGeneratorAlmostBlowUpModel_of_isClosedImmersion`: the recognition of
  the shape of Example 0EVG.
* `AlgebraicGeometry.exists_isAlmostBlowUpSquare_of_isOneGeneratorAlmostBlowUpModel` and
  `AlgebraicGeometry.exists_isAlmostBlowUpSquare_of_isTwoGeneratorAlmostBlowUpModel`: a pair of
  morphisms of the shape of Example 0EVG, respectively of Example 0EVH, is the modification and
  the centre of an almost blowup square.
* `AlgebraicGeometry.Spec.overIsoQuotientSubschemeι`: `Spec (A ⧸ I) ⟶ Spec A` is the closed
  subscheme cut out by `I`, as a scheme over `Spec A`.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EV7](https://stacks.math.columbia.edu/tag/0EV7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Ideal sheaves on an affine scheme and on the spectrum of its global sections -/

/-- On an affine scheme, global sections of the canonical isomorphism to the spectrum of the
global sections undo the identification of the global sections of that spectrum with the ring. -/
theorem isoSpec_hom_appTop_ΓSpecIso_inv (V : Scheme.{u}) [IsAffine V] (a : Γ(V, ⊤)) :
    V.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(V, ⊤)).inv.hom a) = a := by
  show V.toSpecΓ.appTop.hom ((Scheme.ΓSpecIso Γ(V, ⊤)).inv.hom a) = a
  rw [Scheme.toSpecΓ_appTop, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

/-- On an affine scheme `V`, the ideal sheaf attached to an ideal `𝔞` of `Γ(V, ⊤)` is the inverse
image along `V ≅ Spec Γ(V, ⊤)` of the ideal sheaf `𝔞` defines on the spectrum. -/
theorem Scheme.IdealSheafData.comap_isoSpec_hom_ofIdealTop (V : Scheme.{u}) [IsAffine V]
    (𝔞 : Ideal Γ(V, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop (𝔞.map (Scheme.ΓSpecIso Γ(V, ⊤)).inv.hom)).comap
      V.isoSpec.hom = Scheme.IdealSheafData.ofIdealTop 𝔞 := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Stacks.IdealSheaf.ideal_comap_top_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal,
    Scheme.IdealSheafData.ofIdealTop_ideal]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id,
    Ideal.map_id, Ideal.map_map]
  conv_rhs => rw [← Ideal.map_id 𝔞]
  congr 1
  ext a
  exact isoSpec_hom_appTop_ΓSpecIso_inv V a

/-- The closed subscheme cut out by the inverse image of an ideal sheaf along an isomorphism,
composed with that isomorphism, is the closed subscheme cut out by the ideal sheaf. -/
def overIsoComapSubschemeι {V V₀ : Scheme.{u}} (e : V ≅ V₀) (K : V₀.IdealSheafData) :
    Over.mk ((K.comap e.hom).subschemeι ≫ e.hom) ≅ Over.mk K.subschemeι :=
  Over.isoMk (K.comapIso e.hom ≪≫ asIso (pullback.snd e.hom K.subschemeι)) (by
    simp only [Over.mk_hom, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [← pullback.condition, ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst])

/-- A closed immersion is, over its target, the closed subscheme cut out by its kernel. -/
def overIsoKerSubschemeι {W V : Scheme.{u}} (c : W ⟶ V) [IsClosedImmersion c] :
    Over.mk c ≅ Over.mk c.ker.subschemeι :=
  Over.isoMk (asIso c.toImage) (by simp)

/-- Two ideal sheaves whose closed subschemes are isomorphic over the ambient scheme are equal. -/
theorem Scheme.IdealSheafData.eq_of_nonempty_overIso {V : Scheme.{u}} {I I' : V.IdealSheafData}
    (h : Nonempty (Over.mk I.subschemeι ≅ Over.mk I'.subschemeι)) : I = I' := by
  obtain ⟨e⟩ := h
  have hw : e.hom.left ≫ I'.subschemeι = I.subschemeι := Over.w e.hom
  have : IsIso e.hom.left := (Over.forget V).map_isIso e.hom
  rw [← I.ker_subschemeι, ← I'.ker_subschemeι, ← hw, Scheme.Hom.ker_comp_of_isIso]

/-- **`Spec (A ⧸ I) ⟶ Spec A` is the closed subscheme cut out by `I`, as a scheme over
`Spec A`.** -/
def Spec.overIsoQuotientSubschemeι {A : Type u} [CommRing A] (I : Ideal A) :
    Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      Over.mk (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I)).subschemeι :=
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI e : Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.subschemeι :=
    Over.isoMk (asIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toImage) (by simp)
  e ≪≫ eqToIso (by rw [ker_Spec_map_quotient_mk])

/-! ### The annihilation condition -/

/-- An ideal contained in the kernel of the localization away from `t` and finitely generated is
annihilated by a single power of `t`. -/
theorem exists_pow_mul_eq_zero_of_fg_of_le_ker {A : Type*} [CommRing A] (t : A) {J : Ideal A}
    (hJ : J.FG) (hle : J ≤ RingHom.ker (algebraMap A (Localization.Away t))) :
    ∃ n : ℕ, ∀ x ∈ J, t ^ n * x = 0 := by
  classical
  obtain ⟨s, rfl⟩ := hJ
  have hs : ∀ x ∈ s, ∃ n : ℕ, t ^ n * x = 0 := fun x hx ↦
    (IsLocalization.Away.algebraMap_eq_zero_iff (S := Localization.Away t) t x).mp
      (RingHom.mem_ker.mp (hle (Ideal.subset_span hx)))
  choose! n hn using hs
  refine ⟨∑ x ∈ s, n x, fun x hx ↦ ?_⟩
  refine Submodule.span_induction (fun y hy ↦ ?_) (by simp) (fun y z _ _ hy hz ↦ ?_)
    (fun a y _ hy ↦ ?_) hx
  · obtain ⟨m, hm⟩ : ∃ m, ∑ x ∈ s, n x = n y + m :=
      ⟨_, (Finset.add_sum_erase s n hy).symm⟩
    rw [hm, pow_add, mul_comm (t ^ n y), mul_assoc, hn y hy, mul_zero]
  · rw [mul_add, hy, hz, add_zero]
  · rw [smul_eq_mul, mul_left_comm, hy, mul_zero]

/-- The ideal of global sections of a closed immersion of finite presentation into an affine scheme
is finitely generated. -/
private theorem fg_ker_ideal_top_of_locallyOfFinitePresentation {W V : Scheme.{u}} [IsAffine V]
    (c : W ⟶ V) [IsClosedImmersion c] [LocallyOfFinitePresentation c] :
    (c.ker.ideal ⟨⊤, isAffineOpen_top V⟩).FG := by
  have hc : LocallyOfFinitePresentation c.ker.subschemeι := by
    have he : c.ker.subschemeι = inv c.toImage ≫ c := by
      rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
    rw [he]
    infer_instance
  exact (Stacks.Flatness.finitePresentation_subschemeι_iff _).mp
    ⟨hc, inferInstance, inferInstance⟩ _

/-- **The annihilation condition of Example 0EVG.** Let `c : W ⟶ V` be a closed immersion of
finite presentation into an affine scheme, and let `I` be an ideal sheaf on `V` whose global
sections are generated by a single section `t`. If the ideal of `c` restricts to zero on the
complement of the zero locus of `I`, that is if `c` is an isomorphism away from it, then the
ideal of global sections of `c` is annihilated by a power of `t`. -/
theorem exists_pow_mul_eq_zero_of_comap_eq_bot {W V : Scheme.{u}} [IsAffine V] (c : W ⟶ V)
    [IsClosedImmersion c] [LocallyOfFinitePresentation c] (I : V.IdealSheafData)
    (t : Γ(V, ⊤)) (ht : I.ideal ⟨⊤, isAffineOpen_top V⟩ = Ideal.span {t})
    (hker : c.ker.comap (Scheme.Opens.ι (X := V)
      ⟨(I.support : Set V)ᶜ, I.support.isClosed.isOpen_compl⟩) = ⊥) :
    ∃ n : ℕ, ∀ x ∈ c.ker.ideal ⟨⊤, isAffineOpen_top V⟩, t ^ n * x = 0 := by
  have hle : c.ker ≤ supportedSectionsIdeal (I.support : Set V) := by
    rw [supportedSectionsIdeal_eq_complementKernel _ I.support.isClosed]
    exact (le_ker_iff_comap_eq_bot _ _).mpr hker
  have hfg := fg_ker_ideal_top_of_locallyOfFinitePresentation c
  refine exists_pow_mul_eq_zero_of_fg_of_le_ker t hfg ?_
  rw [← supportedSectionsIdeal_ideal_top_eq_ker I t ht]
  exact hle _

/-! ### The recognition -/

/-- On an affine scheme, an ideal sheaf is the inverse image along `V ≅ Spec Γ(V, ⊤)` of the ideal
sheaf defined by its ideal of global sections. -/
private theorem eq_comap_isoSpec_hom_ofIdealTop_map {V : Scheme.{u}} [IsAffine V]
    (K : V.IdealSheafData) :
    K = (Scheme.IdealSheafData.ofIdealTop
      ((K.ideal ⟨⊤, isAffineOpen_top V⟩).map (Scheme.ΓSpecIso Γ(V, ⊤)).inv.hom)).comap
        V.isoSpec.hom := by
  rw [Scheme.IdealSheafData.comap_isoSpec_hom_ofIdealTop]
  exact (Scheme.IdealSheafData.equivOfIsAffine.symm_apply_apply K).symm


/-- **Recognizing the shape of More on Flatness, Example 0EVG.** Let `V` be an affine scheme,
`I` an ideal sheaf on `V` whose global sections are generated by a single section `t`, and
`z : D ⟶ V` the closed subscheme cut out by `I`. A closed immersion `c : W ⟶ V` of finite
presentation which is an isomorphism away from the zero locus of `I` forms, with `z`, a pair of
the shape of Example 0EVG: `V ≅ Spec Γ(V, ⊤)` carries `z` to the closed subscheme cut out by `t`
and `c` to `Spec (Γ(V, ⊤)/J) ⟶ Spec Γ(V, ⊤)`, where `J` is the ideal of `c`, which is finitely
generated and annihilated by a power of `t`. -/
theorem isOneGeneratorAlmostBlowUpModel_of_isClosedImmersion {W V D : Scheme.{u}} [IsAffine V]
    (c : W ⟶ V) [IsClosedImmersion c] [LocallyOfFinitePresentation c] (z : D ⟶ V)
    (I : V.IdealSheafData) (hz : Nonempty (Over.mk z ≅ Over.mk I.subschemeι))
    (t : Γ(V, ⊤)) (ht : I.ideal ⟨⊤, isAffineOpen_top V⟩ = Ideal.span {t})
    (hker : c.ker.comap (Scheme.Opens.ι (X := V)
      ⟨(I.support : Set V)ᶜ, I.support.isClosed.isOpen_compl⟩) = ⊥) :
    IsOneGeneratorAlmostBlowUpModel c z := by
  set J := c.ker.ideal ⟨⊤, isAffineOpen_top V⟩ with hJdef
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_comap_eq_bot c I t ht hker
  have hfg : J.FG := fg_ker_ideal_top_of_locallyOfFinitePresentation c
  let iX := V.isoSpec
  have hc : c.ker = (Scheme.IdealSheafData.ofIdealTop
      (J.map (Scheme.ΓSpecIso Γ(V, ⊤)).inv.hom)).comap iX.hom := by
    exact (eq_comap_isoSpec_hom_ofIdealTop_map c.ker)
  let Kc := Scheme.IdealSheafData.ofIdealTop (J.map (Scheme.ΓSpecIso Γ(V, ⊤)).inv.hom)
  let ec₁ : Over.mk c ≅ Over.mk (Kc.comap iX.hom).subschemeι :=
    overIsoKerSubschemeι c ≪≫ eqToIso (by rw [hc])
  let ec₂ : Over.mk (c ≫ iX.hom) ≅ Over.mk ((Kc.comap iX.hom).subschemeι ≫ iX.hom) :=
    (Over.map iX.hom).mapIso ec₁
  let ec : Over.mk (c ≫ iX.hom) ≅ Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    ec₂ ≪≫ overIsoComapSubschemeι iX Kc ≪≫ (Spec.overIsoQuotientSubschemeι J).symm
  have hI : I = (Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {t}).map (Scheme.ΓSpecIso Γ(V, ⊤)).inv.hom)).comap iX.hom := by
    simpa only [ht] using eq_comap_isoSpec_hom_ofIdealTop_map I
  let Kz := Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span {t}).map (Scheme.ΓSpecIso Γ(V, ⊤)).inv.hom)
  let ez₁ : Over.mk z ≅ Over.mk (Kz.comap iX.hom).subschemeι :=
    hz.some ≪≫ eqToIso (by rw [hI])
  let ez₂ : Over.mk (z ≫ iX.hom) ≅ Over.mk ((Kz.comap iX.hom).subschemeι ≫ iX.hom) :=
    (Over.map iX.hom).mapIso ez₁
  let ez : Over.mk (z ≫ iX.hom) ≅ Over.mk Kz.subschemeι :=
    ez₂ ≪≫ overIsoComapSubschemeι iX Kz
  refine ⟨Γ(V, ⊤), inferInstance, t, J, hfg, ⟨n, hn⟩, iX,
    (Over.forget _).mapIso ec, (Over.forget _).mapIso ez, ?_, ?_⟩
  · exact (Over.w ec.hom).symm
  · exact (Over.w ez.hom).symm

/-- The shape of More on Flatness, Example 0EVG, recorded by three isomorphisms, gives the shape
recorded by an isomorphism of bases and two isomorphisms over the base. -/
theorem IsOneGeneratorAlmostBlowUpModel.isPrincipalCenterModelPair {X X' Z : Scheme.{u}}
    {b : X' ⟶ X} {z : Z ⟶ X} (h : IsOneGeneratorAlmostBlowUpModel b z) :
    IsPrincipalCenterModelPair b z := by
  obtain ⟨A, hA, f, J, hJ, hann, iX, iX', iZ, hb, hz⟩ := h
  exact ⟨A, hA, f, J, hJ, hann, iX, ⟨Over.isoMk iX' hb.symm⟩, ⟨Over.isoMk iZ hz.symm⟩⟩

/-- A pair of morphisms with the shape of More on Flatness, Example 0EVG is the modification and
the centre of an almost blowup square. -/
theorem exists_isAlmostBlowUpSquare_of_isOneGeneratorAlmostBlowUpModel {X X' Z : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) (h : IsOneGeneratorAlmostBlowUpModel b z) :
    ∃ I : X.IdealSheafData,
      IsAlmostBlowUpSquare I b ∧ Nonempty (Over.mk z ≅ Over.mk I.subschemeι) :=
  exists_isAlmostBlowUpSquare_of_isPrincipalCenterModelPair b z h.isPrincipalCenterModelPair

/-! ### The shape of Example 0EVH -/

/-- A pair of morphisms with the shape of More on Flatness, Example 0EVH is the modification and
the centre of an almost blowup square. -/
theorem exists_isAlmostBlowUpSquare_of_isTwoGeneratorAlmostBlowUpModel {X X' Z : Scheme.{u}}
    (b : X' ⟶ X) (z : Z ⟶ X) (h : IsTwoGeneratorAlmostBlowUpModel b z) :
    ∃ I : X.IdealSheafData,
      IsAlmostBlowUpSquare I b ∧ Nonempty (Over.mk z ≅ Over.mk I.subschemeι) := by
  obtain ⟨A, hA, f₁, f₂, iX, iX', iZ, hb, hz⟩ := h
  let := hA
  let := (Stacks.AlmostBlowUp.twoGeneratorSquare A f₁ f₂).modificationGraded
  set Im : (Spec (.of A)).IdealSheafData := Stacks.AlmostBlowUp.centerIdealSheaf A f₁ f₂
  set bm := Stacks.AlmostBlowUp.modificationToBase A f₁ f₂
  have hmodel : IsAlmostBlowUpSquare Im bm :=
    Stacks.AlmostBlowUp.isAlmostBlowUpSquare_modificationToBase A f₁ f₂
  have hpb : IsPullback b iX'.hom iX.hom bm := IsPullback.of_vert_isIso ⟨hb⟩
  let ecz : Over.mk (Stacks.AlmostBlowUp.centerToBase A f₁ f₂) ≅ Over.mk Im.subschemeι :=
    Spec.overIsoQuotientSubschemeι (Stacks.AlmostBlowUp.centerIdeal A f₁ f₂)
  have hwz : (iZ.hom ≫ ecz.hom.left) ≫ Im.subschemeι = z ≫ iX.hom := by
    have hw := Over.w ecz.hom
    simp only [Over.mk_left, Over.mk_hom] at hw
    rw [Category.assoc, hw, ← hz]
  have : IsIso (iZ.hom ≫ ecz.hom.left) := by
    have : IsIso ecz.hom.left := (Over.forget (Spec (.of A))).map_isIso ecz.hom
    infer_instance
  have hpz : IsPullback z (iZ.hom ≫ ecz.hom.left) iX.hom Im.subschemeι :=
    IsPullback.of_vert_isIso ⟨hwz.symm⟩
  refine ⟨Im.comap iX.hom, ?_, ?_⟩
  · have h0 : IsAlmostBlowUpSquare (Im.comap iX.hom) (pullback.fst iX.hom bm) :=
      isAlmostBlowUpSquare_baseChange Im bm iX.hom hmodel
    have h1 : IsAlmostBlowUpSquare (Im.comap iX.hom)
        (hpb.isoPullback.hom ≫ pullback.fst iX.hom bm) :=
      isAlmostBlowUpSquare_isIso_comp _ h0 hpb.isoPullback.hom
    rwa [hpb.isoPullback_hom_fst] at h1
  · let ez' : Over.mk z ≅ Over.mk (pullback.fst iX.hom Im.subschemeι) :=
      Over.isoMk hpz.isoPullback (by simp)
    let ec : Over.mk (Im.comap iX.hom).subschemeι ≅
        Over.mk (pullback.fst iX.hom Im.subschemeι) :=
      Over.isoMk (Im.comapIso iX.hom)
        (by simp [Scheme.IdealSheafData.comapIso_hom_fst Im iX.hom])
    exact ⟨ez' ≪≫ ec.symm⟩

end AlgebraicGeometry

end
