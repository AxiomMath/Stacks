module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleOverLimit
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.SpecLimitOfIndSmooth
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.RingTheory.Smoothing.IndSmooth

/-!
# Finite étale covers over an ind-smooth local algebra come from a smooth model

Let `A → B` be a local homomorphism of Noetherian local rings such that `B` is a filtered colimit
of smooth `A`-algebras, and let `V ⊆ Spec B` be an open containing every prime not lying over
`𝔪_A` and at least one prime lying over `𝔪_A`. This file proves the descent step in the proof
of [Stacks, Tag 0EYC]: there is a smooth affine `A`-scheme `X` with an open `U ⊆ X` such that

* `U` contains every point of `X` not lying over the closed point of `Spec A`,
* `U` is dense in every fibre of `X → Spec A`,
* if every finite étale cover of `U` extends to `X`, then every finite étale cover of `V`
  extends to `Spec B`.

These are exactly the hypotheses of [Stacks, Tag 0EYB] for `X → Spec A` and `U`.

Writing `Spec B = lim Xᵢ` with `Xᵢ` smooth and affine over `A`, a finite étale cover of `V`
descends to a finite étale cover of an open `Vᵢ ⊆ Xᵢ` which can be chosen to contain the
preimage of the punctured spectrum of `A` ([Stacks, Tag 01Z4], [Stacks, Tag 0BTV]). The closed
fibre of `Xᵢ` is smooth over the residue field of `A`, hence normal, so the image of the closed
point of `Spec B` has an affine open neighbourhood `X ⊆ Xᵢ` meeting the closed fibre in an
irreducible set. The open `U = X ∩ Vᵢ` then meets the closed fibre of `X` in a nonempty open
subset, hence a dense one.

## Main results

* `Stacks.FundamentalGroup.exists_smooth_affine_model_of_indSmooth`: the descent step of
  [Stacks, Tag 0EYC].

## References

* [Stacks Project, Tag 0EYC](https://stacks.math.columbia.edu/tag/0EYC)
* [Stacks Project, Tag 0EYB](https://stacks.math.columbia.edu/tag/0EYB)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 0BTV](https://stacks.math.columbia.edu/tag/0BTV)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

namespace Stacks.FundamentalGroup

/-- A finite étale cover of a quasi-compact open `V` of a cofiltered limit comes from a finite
étale cover of an open `Vᵢ` of some stage, and if the limit and the stages map compatibly to a
scheme `S` and `V` contains the preimage of a quasi-compact open `W ⊆ S`, then `Vᵢ` can be
chosen to contain the preimage of `W` as well. -/
private lemma exists_finiteEtale_model_over_open_of_preimage_le
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [∀ {i j : I} (t : i ⟶ j), IsAffineHom (D.map t)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {S : Scheme.{u}} (f : D ⟶ (Functor.const I).obj S) (g : c.pt ⟶ S)
    [∀ i : I, QuasiCompact (f.app i)] (hcomm : ∀ i, c.π.app i ≫ f.app i = g)
    (W : S.Opens) (hW : IsCompact (W : Set S)) (V : c.pt.Opens)
    (hV : IsCompact (V : Set c.pt)) (hle : g ⁻¹ᵁ W ≤ V) (Y : FiniteEtaleOver V.toScheme) :
    ∃ (i : I) (Vi : (D.obj i).Opens) (gV : V.toScheme ⟶ Vi.toScheme),
      gV ≫ Vi.ι = V.ι ≫ c.π.app i ∧ f.app i ⁻¹ᵁ W ≤ Vi ∧
      ∃ Bi : FiniteEtaleOver Vi.toScheme, Nonempty (Y ≅ (finiteEtaleBaseChange gV).obj Bi) := by
  obtain ⟨i, Vi, hVi, hpre⟩ := exists_preimage_eq D c hc V hV
  have hpre' : c.π.app i ⁻¹ᵁ (Vi ⊔ f.app i ⁻¹ᵁ W) = V := by
    rw [Scheme.Hom.preimage_sup, hpre, ← Scheme.Hom.comp_preimage, hcomm,
      sup_eq_left.mpr hle]
  have hcompact : IsCompact ((Vi ⊔ f.app i ⁻¹ᵁ W : (D.obj i).Opens) : Set (D.obj i)) :=
    hVi.union (QuasiCompact.isCompact_preimage (f := f.app i) _ W.2 hW)
  clear hpre
  subst hpre'
  have (j : Over i) : CompactSpace ((opensDiagram D i (Vi ⊔ f.app i ⁻¹ᵁ W)).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ (Vi ⊔ _).2 hcompact)
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i (Vi ⊔ f.app i ⁻¹ᵁ W)).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ (Vi ⊔ f.app i ⁻¹ᵁ W)).2).mp
      (.of_quasiSeparatedSpace _)
  obtain ⟨j, Bj, hBj⟩ := exists_finiteEtale_model (opensDiagram D i (Vi ⊔ f.app i ⁻¹ᵁ W))
    (opensCone D c i (Vi ⊔ f.app i ⁻¹ᵁ W)) (isLimitOpensCone D c hc i _) Y
  refine ⟨j.left, D.map j.hom ⁻¹ᵁ (Vi ⊔ f.app i ⁻¹ᵁ W),
    (opensCone D c i (Vi ⊔ f.app i ⁻¹ᵁ W)).π.app j, ?_, ?_, Bj, hBj⟩
  · simp [opensCone]
  · have hnat : D.map j.hom ≫ f.app i = f.app j.left := by simp
    rw [← hnat, Scheme.Hom.comp_preimage]
    exact (Opens.map (D.map j.hom).base).monotone le_sup_right

/-- Every point of a Noetherian normal scheme has an irreducible open neighbourhood: the scheme
is a finite disjoint union of integral schemes. -/
private lemma exists_isIrreducible_nhds_of_isNormal (X : Scheme.{u}) [IsNoetherian X]
    [IsNormal X] (x : X) : ∃ U : X.Opens, x ∈ U ∧ IsIrreducible (U : Set X) := by
  classical
  obtain ⟨indices, hfinite, components, hnormalComponents, hintegral, ⟨iso⟩⟩ :=
    (isNormal_iff_exists_iso_finite_coproduct_integral_normal X).mp inferInstance
  let point := (sigmaMk components).symm (iso.hom x)
  let inclusion := Sigma.ι components point.1 ≫ iso.inv
  have : IsIntegral (components point.1) := hintegral point.1
  refine ⟨inclusion.opensRange, ⟨point.2, ?_⟩, ?_⟩
  · change iso.inv (Sigma.ι components point.1 point.2) = x
    rw [← sigmaMk_mk]
    change iso.inv ((sigmaMk components) ((sigmaMk components).symm (iso.hom x))) = x
    simp
  · change IsIrreducible (Set.range inclusion)
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image inclusion
      inclusion.continuous.continuousOn

/-- For a smooth affine morphism `f : X ⟶ S`, every point `x` of `X` has an affine open
neighbourhood meeting the fibre `f⁻¹(f(x))` in a preirreducible set. The fibre is smooth over a
field, hence regular ([Stacks, Tag 056S]) and normal. -/
private lemma exists_isAffineOpen_isPreirreducible_fiber_inter {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsAffineHom f] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      IsPreirreducible (f ⁻¹' {f x} ∩ (U : Set X)) := by
  have hsmooth : Smooth (f.fiberToSpecResidueField (f x)) := by
    change Smooth (pullback.snd f (S.fromSpecResidueField (f x)))
    infer_instance
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  have : IsNoetherian (f.fiber (f x)) := ⟨⟩
  have : IsNormal (f.fiber (f x)) := isNormal_of_isRegular _
    (@isRegular_of_smooth_over_field _ _ _ (f.fiberToSpecResidueField (f x)) hsmooth)
  obtain ⟨W, hxW, hW⟩ := exists_isIrreducible_nhds_of_isNormal _ (f.asFiber x)
  obtain ⟨O, hO, hOW⟩ := (f.fiberι (f x)).isEmbedding.isInducing.isOpen_iff.mp W.2
  have hxO : x ∈ O := by
    have hmem : f.asFiber x ∈ (f.fiberι (f x)).base ⁻¹' O := by rwa [hOW]
    simpa [Scheme.Hom.fiberι_asFiber] using hmem
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxO hO
  refine ⟨U, hU, hxU, ?_⟩
  have himage : f ⁻¹' {f x} ∩ (U : Set X) =
      (f.fiberι (f x)).base '' ((f.fiberι (f x)).base ⁻¹' U) := by
    rw [Set.image_preimage_eq_inter_range, Scheme.Hom.range_fiberι, Set.inter_comm]
  rw [himage]
  refine (hW.2.open_subset ((f.fiberι _).continuous.isOpen_preimage _ U.2) ?_).image _
    (f.fiberι _).continuous.continuousOn
  change _ ⊆ W.carrier
  rw [← hOW]
  exact Set.preimage_mono hUO

/-- If `gU` and `gV` cover `p` over opens `U`, `Vi` of `X`, then `gU` maps `V` into `U.ι ⁻¹ᵁ Vi`. -/
private lemma map_mem_preimage_of_comp_eq {T X : Scheme.{u}} {p : T ⟶ X} {U Vi : X.Opens}
    {V : T.Opens} {gU : T ⟶ U.toScheme} (hgU : gU ≫ U.ι = p) {gV : V.toScheme ⟶ Vi.toScheme}
    (hgV : gV ≫ Vi.ι = V.ι ≫ p) (x : V.toScheme) : gU (V.ι x) ∈ U.ι ⁻¹ᵁ Vi := by
  change U.ι (gU (V.ι x)) ∈ Vi
  rw [← Scheme.Hom.comp_apply, hgU, ← Scheme.Hom.comp_apply, ← hgV, Scheme.Hom.comp_apply]
  exact (gV x).2

/-- Let `f : X ⟶ S` and let `U ⊆ X` be open with `f⁻¹(s₀) ∩ U` preirreducible. An open `VU ⊆ U`
containing every point of `U` off the fibre over `s₀` and meeting that fibre is dense in every
fibre of `U → S`. -/
private lemma subset_closure_inter_fiber_of_isPreirreducible {X S : Scheme.{u}} (f : X ⟶ S)
    (s₀ : S) (U : X.Opens) (hU : IsPreirreducible (f ⁻¹' {s₀} ∩ (U : Set X)))
    (VU : U.toScheme.Opens)
    (hopen : ∀ x : U.toScheme, (U.ι ≫ f) x ≠ s₀ → x ∈ VU)
    (hne : ∃ x : U.toScheme, (U.ι ≫ f) x = s₀ ∧ x ∈ VU) (s : S) :
    (U.ι ≫ f).base ⁻¹' {s} ⊆ closure ((VU : Set U.toScheme) ∩ (U.ι ≫ f).base ⁻¹' {s}) := by
  intro y hy
  by_cases hs : s = s₀
  · rw [hs] at hy ⊢
    have hirr : IsPreirreducible ((U.ι ≫ f).base ⁻¹' {s₀}) := by
      convert hU.preimage U.ι.isOpenEmbedding using 1
      ext z
      exact ⟨fun h ↦ ⟨h, z.2⟩, fun h ↦ h.1⟩
    rw [Set.inter_comm]
    exact subset_closure_inter_of_isPreirreducible_of_isOpen hirr VU.2 hne hy
  · exact subset_closure ⟨hopen y (fun h ↦ hs (hy.symm.trans h)), hy⟩

/-- Let `p : T ⟶ X` factor through an open `U ⊆ X` and let `gV : V ⟶ Vi` cover `p` on opens
`V ⊆ T`, `Vi ⊆ X`. If every finite étale cover of `U ∩ Vi` extends to `U`, then the pullback
along `gV` of every finite étale cover of `Vi` extends to `T`. -/
private lemma mem_essImage_finiteEtaleBaseChange_of_fac {T X : Scheme.{u}} {p : T ⟶ X}
    {U Vi : X.Opens} {V : T.Opens} {gU : T ⟶ U.toScheme} (hgU : gU ≫ U.ι = p)
    {gV : V.toScheme ⟶ Vi.toScheme} (hgV : gV ≫ Vi.ι = V.ι ≫ p)
    [(finiteEtaleBaseChange (U.ι ⁻¹ᵁ Vi).ι).EssSurj] (Bi : FiniteEtaleOver Vi.toScheme) :
    (finiteEtaleBaseChange V.ι).essImage ((finiteEtaleBaseChange gV).obj Bi) := by
  let gVU : V.toScheme ⟶ (U.ι ⁻¹ᵁ Vi).toScheme :=
    IsOpenImmersion.lift (U.ι ⁻¹ᵁ Vi).ι (V.ι ≫ gU) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact map_mem_preimage_of_comp_eq hgU hgV x)
  have hgVU : gVU ≫ (U.ι ⁻¹ᵁ Vi).ι = V.ι ≫ gU := IsOpenImmersion.lift_fac _ _ _
  let t : (U.ι ⁻¹ᵁ Vi).toScheme ⟶ Vi.toScheme := U.ι ∣_ Vi
  have ht : t ≫ Vi.ι = (U.ι ⁻¹ᵁ Vi).ι ≫ U.ι := morphismRestrict_ι U.ι Vi
  have hfactor : gV = gVU ≫ t := by
    apply (cancel_mono Vi.ι).mp
    rw [Category.assoc, ht, ← Category.assoc, hgVU, Category.assoc, hgU, hgV]
  obtain ⟨Y, ⟨eY⟩⟩ := Functor.EssSurj.mem_essImage (finiteEtaleBaseChange (U.ι ⁻¹ᵁ Vi).ι)
    ((finiteEtaleBaseChange t).obj Bi)
  exact ⟨(finiteEtaleBaseChange gU).obj Y,
    ⟨(finiteEtaleBaseChangeComp V.ι gU (gVU ≫ (U.ι ⁻¹ᵁ Vi).ι) hgVU).symm.app Y ≪≫
      (finiteEtaleBaseChangeComp gVU (U.ι ⁻¹ᵁ Vi).ι).app Y ≪≫
      (finiteEtaleBaseChange gVU).mapIso eY ≪≫
      (finiteEtaleBaseChangeComp gVU t gV hfactor).symm.app Bi⟩⟩

/-- **The descent step of [Stacks, Tag 0EYC].** Let `A → B` be a local homomorphism of Noetherian
local rings with `B` a filtered colimit of smooth `A`-algebras, and let `V ⊆ Spec B` be an open
containing every prime not lying over `𝔪_A` and some prime lying over `𝔪_A`. For every finite
étale cover `W` of `V` there are a smooth morphism `f : X ⟶ Spec A` with `X` affine and an open
`U ⊆ X` such that `U` contains every point of `X` not over the closed point, `U` is dense in every
fibre of `f`, and `W` extends to `Spec B` as soon as every finite étale cover of `U` extends to
`X`. The pair `(f, U)` satisfies the hypotheses of [Stacks, Tag 0EYB]. -/
public theorem exists_smooth_affine_model_of_indSmooth (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hind : Stacks.Smoothing.IndSmooth A B)
    (V : (Spec (.of B)).Opens)
    (hV : ∀ q : PrimeSpectrum B,
      q.asIdeal.comap (algebraMap A B) ≠ IsLocalRing.maximalIdeal A → q ∈ V)
    (hpoint : ∃ q : PrimeSpectrum B,
      q ∈ V ∧ q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (W : FiniteEtaleOver V.toScheme) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : X.Opens), Smooth f ∧ IsAffine X ∧
      (∀ x : X, f.base x ≠ IsLocalRing.closedPoint A → x ∈ U) ∧
      (∀ s : Spec (.of A), f.base ⁻¹' {s} ⊆ closure ((U : Set X) ∩ f.base ⁻¹' {s})) ∧
      ((finiteEtaleBaseChange U.ι).EssSurj → (finiteEtaleBaseChange V.ι).essImage W) := by
  classical
  obtain ⟨I, _, _, pres, f, haffine, hsmooth, hcomm⟩ :=
    exists_limitPresentation_spec_of_indSmooth A B hind
  let D := pres.diag
  let π := pres.π
  have hlimit : IsLimit (Cone.mk _ π) := pres.isLimit
  have (i : I) : IsAffine (D.obj i) := haffine i
  have (i : I) : Smooth (f.app i) := hsmooth i
  have (i : I) : IsAffine (((Functor.const I).obj (Spec (.of A))).obj i) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  have {i j : I} (t : i ⟶ j) : IsAffineHom (D.map t) := isAffineHom_of_isAffine _
  have (i : I) : IsAffineHom (f.app i) := isAffineHom_of_isAffine _
  let g : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  obtain ⟨i, Vi, gV, hgV, hcontains, Bi, ⟨e⟩⟩ :=
    exists_finiteEtale_model_over_open_of_preimage_le D (Cone.mk _ π) hlimit f g hcomm
      (puncturedSpectrum A) (NoetherianSpace.isCompact _) V (NoetherianSpace.isCompact _)
      (fun q hq ↦ hV q fun heq ↦ hq (PrimeSpectrum.ext heq)) W
  let p : Spec (.of B) ⟶ D.obj i := π.app i
  have hp : p ≫ f.app i = g := hcomm i
  replace hgV : gV ≫ Vi.ι = V.ι ≫ p := hgV
  let b : Spec (.of B) := closedPoint B
  have hclosed : f.app i (p b) = closedPoint A := by
    rw [← Scheme.Hom.comp_apply, hp]
    exact comap_closedPoint (algebraMap A B)
  obtain ⟨U, hUaffine, hUclosed, hUirreducible⟩ :=
    exists_isAffineOpen_isPreirreducible_fiber_inter (f.app i) (p b)
  rw [hclosed] at hUirreducible
  have : IsAffine U.toScheme := hUaffine
  have hpreimage : p ⁻¹ᵁ U = ⊤ := (closedPoint_mem_iff (R := B) (p ⁻¹ᵁ U)).mp hUclosed
  let gU : Spec (.of B) ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι p (by
      rintro _ ⟨point, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (hpreimage.symm ▸ trivial : point ∈ p ⁻¹ᵁ U))
  have hgU : gU ≫ U.ι = p := IsOpenImmersion.lift_fac _ _ _
  have hopen : ∀ x : U.toScheme, (U.ι ≫ f.app i) x ≠ closedPoint A → x ∈ U.ι ⁻¹ᵁ Vi :=
    fun _ hx ↦ hcontains hx
  refine ⟨U.toScheme, U.ι ≫ f.app i, U.ι ⁻¹ᵁ Vi, inferInstance, inferInstance, hopen,
    subset_closure_inter_fiber_of_isPreirreducible (f.app i) (closedPoint A) U hUirreducible _
      hopen ?_, ?_⟩
  · obtain ⟨q, hqV, hq⟩ : ∃ x : Spec (.of B), x ∈ V ∧ g x = closedPoint A :=
      hpoint.imp fun _ h ↦ ⟨h.1, PrimeSpectrum.ext h.2⟩
    refine ⟨gU q, ?_, ?_⟩
    · rwa [← Scheme.Hom.comp_apply, ← Category.assoc, hgU, hp]
    · exact map_mem_preimage_of_comp_eq hgU hgV ⟨q, hqV⟩
  · intro _
    exact (mem_essImage_finiteEtaleBaseChange_of_fac hgU hgV Bi).ofIso e.symm

end Stacks.FundamentalGroup

end
