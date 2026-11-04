module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.GlobalSectionsCriterion
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
import StacksFrontier.RingTheory.Depth.RingEquiv

/-!
# Finite etale covers of the punctured spectrum of a normal local ring

Let `A` be a Noetherian normal local ring of dimension at least two, let `X = Spec A` and let
`U = X \ {m}` be the punctured spectrum. Taking global sections sends a finite etale cover of
`U` to a finite normal `A`-algebra whose spectrum is etale over `U`, and this is an equivalence
of categories. Such a cover is the restriction of a finite etale cover of `X` exactly when its
ring of global sections is finite etale over `A`.

Normality of `A` gives `depth A >= 2` by Serre's criterion, which is what reduces the second
statement to the corresponding criterion over a local ring of depth at least two. For the
equivalence, global sections of a cover `V` are computed by decomposing `V` into its integral
components, whose function fields are finite separable over the fraction field of `A`; the
integral closure of `A` in such a field is finite and reflexive, hence of depth at least two,
and agrees with the sections of `V` away from the closed point.

## Implementation notes

The algebras in the target category are required to be torsion-free over `A`. This condition is
not stated in the source, but without it the target is strictly too large and the functor is not
essentially surjective: the residue field `A / m` is a finite normal `A`-algebra whose spectrum
meets `U` in the empty scheme, hence is etale over `U`, yet it is not the ring of sections of any
finite etale cover of `U`. Torsion-freeness cuts the target down to the algebras that do arise,
and holds automatically for `Γ(V, ⊤)`.

## Main definitions

* `AlgebraicGeometry.NormalPurity.NormalFiniteEtaleAwayAlgebra` is the category of finite normal
  `A`-algebras, torsion-free over `A`, whose spectra are etale over the punctured spectrum.
* `AlgebraicGeometry.NormalPurity.globalSections` is the global-sections functor, before its
  codomain is cut down to those algebras.

## Main results

* `AlgebraicGeometry.NormalPurity.globalSections_isEquivalence_normalFiniteEtaleAwayAlgebra` is
  the equivalence of categories.
* `AlgebraicGeometry.NormalPurity.exists_finiteEtale_extension_iff_globalSections_finiteEtale`
  is the criterion for a cover to extend over the whole spectrum.

## References

* [Stacks Project, Tag 0BM9](https://stacks.math.columbia.edu/tag/0BM9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.NormalPurity

private lemma normalSpec_of_normalRing
    (A : Type u) [CommRing A] (hA : IsNormalRing A) :
    IsNormal (Spec (.of A)) := by
  apply (isNormal_iff_stalk_normal (Spec (.of A))).mpr
  intro x
  let p := x.asIdeal
  obtain ⟨hd, hi⟩ := @hA p x.2
  let e := (Spec.stalkIso (.of A) x).commRingCatIsoToRingEquiv
  let : p.IsPrime := x.2
  have : IsDomain (Localization.AtPrime p) := hd
  have : IsDomain ((Spec (.of A)).presheaf.stalk x) := e.isDomain_iff.mpr hd
  refine ⟨inferInstance, ?_⟩
  have : IsIntegrallyClosed (Localization.AtPrime p) := hi
  exact IsIntegrallyClosed.of_equiv e.symm

private lemma normal_of_etale_over_puncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hA : IsNormalRing A)
    {V : Scheme.{u}} (π : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    [Etale π] : IsNormal V := by
  let U := Stacks.Divisors.puncturedSpectrum A
  have : IsNormal (Spec (.of A)) := normalSpec_of_normalRing A hA
  exact AlgebraicGeometry.isNormal_of_etale (π ≫ U.ι)

private noncomputable def affineNormalizationIsoSpec
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsAffine Y] :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    f.normalization ≅ Spec (.of (integralClosure Γ(Y, ⊤) Γ(X, ⊤))) := by
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  have : IsOpenImmersion (f.normalizationOpenCover.f U) :=
    f.normalizationOpenCover.map_prop U
  let : IsIso (f.normalizationOpenCover.f U) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
      rw [← f.fromNormalization_preimage U]
      rfl)
  exact (asIso (f.normalizationOpenCover.f U)).symm

private lemma affineNormalizationIsoSpec_comp_fromNormalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsAffine Y] :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    let C := integralClosure Γ(Y, ⊤) Γ(X, ⊤)
    (affineNormalizationIsoSpec f).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) C)) ≫ Y.isoSpec.inv =
        f.fromNormalization := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let C := integralClosure Γ(Y, ⊤) Γ(X, ⊤)
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let r := f.normalizationOpenCover.f U
  have : IsOpenImmersion r := f.normalizationOpenCover.map_prop U
  have hr : IsIso r := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top r
    rw [← f.fromNormalization_preimage U]
    rfl
  have he : r ≫ f.fromNormalization =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) C)) ≫ Y.isoSpec.inv := by
    rw [f.ι_fromNormalization U,
      show U.2.fromSpec = Y.isoSpec.inv by simpa [U] using IsAffineOpen.fromSpec_top (X := Y)]
    rfl
  change (asIso r).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) C)) ≫ Y.isoSpec.inv =
    f.fromNormalization
  calc
    (asIso r).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) C)) ≫ Y.isoSpec.inv) =
      (asIso r).inv ≫ (r ≫ f.fromNormalization) :=
        congrArg (fun k => (asIso r).inv ≫ k) he.symm
    _ = f.fromNormalization := by simp

private lemma finite_map_normalization_restrict_isIso
    {X U Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (π : Y ⟶ U) [IsIntegralHom π] :
    IsIso ((pullback.snd (π ≫ j) j).toNormalization ≫
      (π ≫ j).normalizationPullback j) := by
  let f : Y ⟶ X := π ≫ j
  have hsq : IsPullback (𝟙 Y) π f j :=
    IsPullback.of_horiz_isIso_mono (CommSq.mk (by simp [f]))
  let e := hsq.isoPullback
  have heπ : e.hom ≫ pullback.snd f j = π := hsq.isoPullback_hom_snd
  have : IsIntegralHom (e.hom ≫ pullback.snd f j) := by
    rw [heπ]
    infer_instance
  have : MorphismProperty.RespectsIso @IsIntegralHom :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsIntegralHom (pullback.snd f j) :=
    (MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom e.hom
      (pullback.snd f j)).mp inferInstance
  have : IsIso ((pullback.snd f j).toNormalization) := inferInstance
  have : Smooth j := inferInstance
  have : IsIso (f.normalizationPullback j) := inferInstance
  infer_instance

private lemma finiteCover_isPullback_normalization
    {X U Y : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (π : Y ⟶ U) [IsIntegralHom π] :
    IsPullback (π ≫ j).toNormalization π (π ≫ j).fromNormalization j := by
  let f := π ≫ j
  let sq : IsPullback (𝟙 Y) π f j :=
    IsPullback.of_horiz_isIso_mono (CommSq.mk (by simp [f]))
  let c := (pullback.snd f j).toNormalization ≫ f.normalizationPullback j
  have : IsIso c := finite_map_normalization_restrict_isIso j π
  let e := sq.isoPullback ≪≫ asIso c
  apply IsPullback.of_iso_pullback (CommSq.mk (by simp [f])) e
  · simp only [e, Iso.trans_hom, asIso_hom, c, Category.assoc,
      Scheme.Hom.toNormalization_normalizationPullback_fst,
      sq.isoPullback_hom_fst_assoc, Category.id_comp]
    rfl
  · simp only [e, Iso.trans_hom, asIso_hom, c, Category.assoc,
      Scheme.Hom.normalizationPullback_snd,
      Scheme.Hom.toNormalization_fromNormalization, sq.isoPullback_hom_snd]

private lemma compactSpace_puncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    CompactSpace (Stacks.Divisors.puncturedSpectrum A).toScheme :=
  @TopologicalSpace.NoetherianSpace.compactSpace _ _
    (TopologicalSpace.NoetherianSpace.set
      ((Stacks.Divisors.puncturedSpectrum A : Set (Spec (.of A)))))

private lemma finiteEtaleOver_puncturedSpectrum_components
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A)
    (V : FiniteEtaleOver (Stacks.Divisors.puncturedSpectrum A).toScheme) :
    ∃ (ι : Type u) (_ : Finite ι) (Y : ι → Scheme.{u})
      (_ : ∀ i, IsNormal (Y i)) (_ : ∀ i, IsIntegral (Y i)),
      Nonempty (V.left ≅ ∐ Y) := by
  let U := Stacks.Divisors.puncturedSpectrum A
  have : Etale V.hom := V.prop.2
  have hnormal : IsNormal V.left := normal_of_etale_over_puncturedSpectrum A hA V.hom
  have : IsFinite V.hom := V.prop.1
  have : IsLocallyNoetherian ((Functor.fromPUnit U.toScheme).obj V.right) := by
    change IsLocallyNoetherian U.toScheme
    exact LocallyOfFiniteType.isLocallyNoetherian U.ι
  have : QuasiSeparatedSpace ((Functor.fromPUnit U.toScheme).obj V.right) := inferInstance
  have : LocallyOfFiniteType V.hom := inferInstance
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : CompactSpace ((Functor.fromPUnit U.toScheme).obj V.right) :=
    compactSpace_puncturedSpectrum A
  have : CompactSpace V.left :=
    (quasiCompact_iff_compactSpace V.hom).mp inferInstance
  have : IsNoetherian V.left := {}
  exact (AlgebraicGeometry.isNormal_iff_exists_iso_finite_coproduct_integral_normal
    V.left).mp hnormal

private lemma compl_range_sigmaι {ι : Type u} (Y : ι → Scheme.{u}) (i : ι) :
    (Set.range (Sigma.ι Y i).base)ᶜ =
      ⋃ j : ι, ⋃ (_ : j ≠ i), Set.range (Sigma.ι Y j).base := by
  ext z
  constructor
  · intro hz
    obtain ⟨⟨j, y⟩, rfl⟩ := (sigmaMk Y).surjective z
    refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · rintro rfl
      exact hz ⟨y, by simp⟩
    · exact ⟨y, by simp⟩
  · rintro hz ⟨y, hy⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hz
    obtain ⟨hji, y', hy'⟩ := Set.mem_iUnion.1 hj
    apply hji
    have hEq : Sigma.ι Y i y = Sigma.ι Y j y' := by
      rw [hy, ← hy']
    have hpair := (sigmaι_eq_iff Y i j y y').mp (by
      simpa only [← Scheme.Hom.comp_apply] using hEq)
    exact (congrArg Sigma.fst hpair).symm

private lemma isOpen_compl_range_sigmaι {ι : Type u} (Y : ι → Scheme.{u}) (i : ι) :
    IsOpen (Set.range (Sigma.ι Y i).base)ᶜ := by
  rw [compl_range_sigmaι]
  exact isOpen_iUnion fun j ↦ isOpen_iUnion fun _ ↦ (Sigma.ι Y j).opensRange.2

private lemma finiteEtaleOver_component_map
    {U : Scheme.{u}} (V : FiniteEtaleOver U)
    {ι : Type u} {Y : ι → Scheme.{u}}
    (e : V.left ≅ ∐ Y) (i : ι) :
    IsFinite (Sigma.ι Y i ≫ e.inv ≫ V.hom) ∧
      Etale (Sigma.ι Y i ≫ e.inv ≫ V.hom) := by
  have : IsFinite V.hom := V.prop.1
  have : Etale V.hom := V.prop.2
  have : IsFinite (e.inv ≫ V.hom) := inferInstance
  have : Etale (e.inv ≫ V.hom) := inferInstance
  have : IsFinite (Sigma.ι Y i) := by
    have hopen := isOpen_compl_range_sigmaι Y i
    have : IsPreimmersion (Sigma.ι Y i) := inferInstance
    have : IsClosedImmersion (Sigma.ι Y i) :=
      IsClosedImmersion.of_isPreimmersion _ (isOpen_compl_iff.mp hopen)
    infer_instance
  exact ⟨inferInstance, inferInstance⟩

private lemma sigmaι_appTop_apply {ι : Type u} (B : ι → Scheme.{u}) (i : ι)
    (s : Γ(∐ B, ⊤)) :
    (Sigma.ι B i).appTop.hom s = ((Sigma.ι B i).appIso ⊤).hom
      ((∐ B).presheaf.map (homOfLE (le_top : Sigma.ι B i ''ᵁ ⊤ ≤ ⊤)).op s) := by
  let f : B i ⟶ ∐ B := Sigma.ι B i
  have hh : f.appTop ≫ (f.appIso ⊤).inv =
      (∐ B).presheaf.map (homOfLE (le_top : f ''ᵁ ⊤ ≤ ⊤)).op := by
    convert f.app_appIso_inv ⊤ using 1 <;> rfl
  calc
    f.appTop.hom s = (f.appIso ⊤).hom ((f.appIso ⊤).inv (f.appTop.hom s)) := by simp
    _ = (f.appIso ⊤).hom ((∐ B).presheaf.map (homOfLE (le_top : f ''ᵁ ⊤ ≤ ⊤)).op s) := by
      congr 1
      exact congrArg (fun q : Γ(∐ B, ⊤) ⟶ Γ(∐ B, f ''ᵁ ⊤) => q.hom s) hh

private lemma sigma_sections_bijective {ι : Type u} (B : ι → Scheme.{u}) :
    Function.Bijective (fun (s : Γ(∐ B, ⊤)) (i : ι) =>
      (Sigma.ι B i).appTop.hom s) := by
  classical
  let T : Scheme.{u} := ∐ B
  let O (i : ι) : T.Opens := Sigma.ι B i ''ᵁ ⊤
  have hO : ⨆ i, O i = ⊤ := by
    simp only [O, Scheme.Hom.image_top_eq_opensRange]
    exact (sigmaOpenCover B).iSup_opensRange
  let G : TopCat.Sheaf CommRingCat T.toTopCat := T.sheaf
  have hcompat (sf : ∀ i, Γ(T, O i)) :
      TopCat.Presheaf.IsCompatible G.1 O sf := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hd : O i ⊓ O j = ⊥ := by
        simpa only [O, Scheme.Hom.image_top_eq_opensRange] using
          (disjoint_iff.mp (disjoint_opensRange_sigmaι B i j hij))
      have : Subsingleton (G.obj.obj (Opposite.op (O i ⊓ O j))) := by
        rw [hd]
        exact CommRingCat.subsingleton_of_isTerminal T.sheaf.isTerminalOfEmpty
      exact Subsingleton.elim _ _
  have hres : Function.Bijective (fun (s : Γ(T, ⊤)) (i : ι) =>
      T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s) := by
    constructor
    · intro s t h
      obtain ⟨gl, _, huniq⟩ := G.existsUnique_gluing' O ⊤
        (fun i => homOfLE le_top) (by rw [hO])
        (fun i => T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s) (hcompat _)
      exact (huniq s fun _ => rfl).trans (huniq t fun i => (congrFun h i).symm).symm
    · intro sf
      obtain ⟨gl, hgl, _⟩ := G.existsUnique_gluing' O ⊤
        (fun i => homOfLE le_top) (by rw [hO]) sf (hcompat sf)
      exact ⟨gl, funext hgl⟩
  have hcomp (i : ι) (s : Γ(T, ⊤)) :
      (Sigma.ι B i).appTop.hom s =
        ((Sigma.ι B i).appIso ⊤).hom
          (T.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op s) :=
    sigmaι_appTop_apply B i s
  constructor
  · intro s t heq
    apply hres.1
    funext i
    have hi := congrArg (fun x => ((Sigma.ι B i).appIso ⊤).inv x) (congrFun heq i)
    simpa only [hcomp, Iso.hom_inv_id_apply] using hi
  · intro sf
    obtain ⟨s, hs⟩ := hres.2 (fun i => ((Sigma.ι B i).appIso ⊤).inv (sf i))
    refine ⟨s, funext (fun i => ?_)⟩
    simp [hcomp, congrFun hs i]

private noncomputable def sigmaSectionsRingEquiv {ι : Type u} (B : ι → Scheme.{u}) :
    Γ(∐ B, ⊤) ≃+* (∀ i, Γ(B i, ⊤)) :=
  RingEquiv.ofBijective (RingHom.pi fun i => (Sigma.ι B i).appTop.hom)
    (sigma_sections_bijective B)

private noncomputable def coproductSectionsRingEquiv
    {V : Scheme.{u}} {ι : Type u} {Y : ι → Scheme.{u}} (e : V ≅ ∐ Y) :
    Γ(V, ⊤) ≃+* (∀ i, Γ(Y i, ⊤)) :=
  (Scheme.Γ.mapIso e.symm.op).commRingCatIsoToRingEquiv.trans (sigmaSectionsRingEquiv Y)

private noncomputable def coproductSectionsAlgEquiv
    (A : Type u) [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    {ι : Type u} {Y : ι → Scheme.{u}} (e : V ≅ ∐ Y) :
    letI : Algebra A Γ(V, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra
    letI : ∀ i, Algebra A Γ(Y i, ⊤) := fun i =>
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (Sigma.ι Y i ≫ e.inv ≫ f).appTop).hom.toAlgebra
    Γ(V, ⊤) ≃ₐ[A] (∀ i, Γ(Y i, ⊤)) := by
  let : Algebra A Γ(V, ⊤) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra
  let : ∀ i, Algebra A Γ(Y i, ⊤) := fun i =>
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (Sigma.ι Y i ≫ e.inv ≫ f).appTop).hom.toAlgebra
  let : Algebra A (∀ i, Γ(Y i, ⊤)) := inferInstance
  let eΓ := coproductSectionsRingEquiv e
  exact AlgEquiv.ofRingEquiv (f := eΓ) fun _ => funext fun _ => rfl

private lemma finite_sections_of_finite_components
    (A : Type u) [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    {ι : Type u} [Finite ι] {Y : ι → Scheme.{u}} (e : V ≅ ∐ Y) :
    letI : Algebra A Γ(V, ⊤) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra
    letI : ∀ i, Algebra A Γ(Y i, ⊤) := fun i =>
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (Sigma.ι Y i ≫ e.inv ≫ f).appTop).hom.toAlgebra
    (∀ i, Module.Finite A Γ(Y i, ⊤)) → Module.Finite A Γ(V, ⊤) := by
  classical
  let : Algebra A Γ(V, ⊤) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom.toAlgebra
  let : ∀ i, Algebra A Γ(Y i, ⊤) := fun i =>
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (Sigma.ι Y i ≫ e.inv ≫ f).appTop).hom.toAlgebra
  intro hfinite
  have : ∀ i, Module.Finite A Γ(Y i, ⊤) := hfinite
  let : Fintype ι := Fintype.ofFinite ι
  have : Module.Finite A (∀ i, Γ(Y i, ⊤)) := inferInstance
  exact Module.Finite.of_surjective
    (coproductSectionsAlgEquiv A f e).symm.toLinearMap
    (coproductSectionsAlgEquiv A f e).symm.surjective

private alias depth_le_of_ringEquiv := Module.depth_le_of_ringEquiv

private alias depth_eq_of_ringEquiv := Module.depth_eq_of_ringEquiv

private noncomputable def localAtMaxEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    A ≃+* Localization.AtPrime (IsLocalRing.maximalIdeal A) :=
  (IsLocalization.atUnits A (IsLocalRing.maximalIdeal A).primeCompl
    (S := Localization.AtPrime (IsLocalRing.maximalIdeal A))
    fun _ hx => IsLocalRing.notMem_maximalIdeal.mp hx).toRingEquiv

private lemma normal_local_ring_domain_integrallyClosed
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hA : IsNormalRing A) : IsDomain A ∧ IsIntegrallyClosed A :=
  hA.of_isLocalRing

private lemma flat_map_genericPoint {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [Flat f] :
    f (genericPoint Y) = genericPoint X := by
  obtain ⟨y, hy, hfy⟩ := Flat.generalizingMap f
    (genericPoint_specializes (f (genericPoint Y)))
  rwa [(inseparable_iff_specializes_and.mpr ⟨hy, genericPoint_specializes y⟩).eq] at hfy

private lemma isField_stalk_of_map_genericPoint {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : Y ⟶ X) (hη : f (genericPoint Y) = genericPoint X) :
    IsField (X.presheaf.stalk (f (genericPoint Y))) := by
  rw [hη]
  exact Field.toIsField X.functionField

private lemma generic_stalk_finite_separable {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X) [Etale f] :
    letI := (f.stalkMap (genericPoint Y)).hom.toAlgebra
    Module.Finite (X.presheaf.stalk (f (genericPoint Y))) Y.functionField ∧
      Algebra.IsSeparable (X.presheaf.stalk (f (genericPoint Y))) Y.functionField := by
  let := (f.stalkMap (genericPoint Y)).hom.toAlgebra
  have hη := flat_map_genericPoint f
  let := (isField_stalk_of_map_genericPoint f hη).toField
  have : Algebra.EssFiniteType (X.presheaf.stalk (f (genericPoint Y))) Y.functionField :=
    RingHom.essFiniteType_algebraMap.mpr (LocallyOfFiniteType.stalkMap f _)
  have : Algebra.FormallyUnramified (X.presheaf.stalk (f (genericPoint Y))) Y.functionField :=
    RingHom.formallyUnramified_algebraMap.mpr (FormallyUnramified.stalkMap f _)
  exact ⟨Algebra.FormallyUnramified.finite_of_free _ _,
    Algebra.FormallyUnramified.isSeparable _ _⟩

private lemma isFractionRing_generic_stalk {X : Scheme.{u}} [IsIntegral X] [IsAffine X]
    (x : X) (hx : x = genericPoint X) :
    letI := (X.presheaf.Γgerm x).hom.toAlgebra
    IsFractionRing Γ(X, ⊤) (X.presheaf.stalk x) := by
  subst x
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)

private lemma finite_integralClosure_sections_of_etale {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsAffine X]
    [IsNoetherianRing Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (f : Y ⟶ X) [Etale f] :
    letI := f.appTop.hom.toAlgebra
    Module.Finite Γ(X, ⊤) (integralClosure Γ(X, ⊤) Γ(Y, ⊤)) := by
  let := f.appTop.hom.toAlgebra
  have hη := flat_map_genericPoint f
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hf := isField_stalk_of_map_genericPoint f hη
  have hfrac := isFractionRing_generic_stalk (f (genericPoint Y)) hη
  let K := X.presheaf.stalk (f (genericPoint Y))
  let L := Y.functionField
  let : Algebra K L := (f.stalkMap (genericPoint Y)).hom.toAlgebra
  let : Algebra Γ(X, ⊤) K := (X.presheaf.Γgerm (f (genericPoint Y))).hom.toAlgebra
  let : Algebra Γ(X, ⊤) L := ((Y.germToFunctionField ⊤).hom.comp f.appTop.hom).toAlgebra
  have : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) L := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X, ⊤) K L := .of_algebraMap_eq' (by
    ext a
    exact ConcreteCategory.congr_hom (f.germ_stalkMap ⊤ (genericPoint Y) trivial).symm a)
  let : Field K := hf.toField
  have : IsFractionRing Γ(X, ⊤) K := hfrac
  have hfin := generic_stalk_finite_separable f
  have : Module.Finite K L := hfin.1
  have : Algebra.IsSeparable K L := hfin.2
  have : Module.Finite Γ(X, ⊤) (integralClosure Γ(X, ⊤) L) :=
    IsIntegralClosure.finite Γ(X, ⊤) K L (integralClosure Γ(X, ⊤) L)
  let g := (IsScalarTower.toAlgHom Γ(X, ⊤) Γ(Y, ⊤) L).mapIntegralClosure
  exact Module.Finite.of_injective g.toLinearMap (fun x y h => Subtype.ext
    (Y.germToFunctionField_injective ⊤ (congrArg Subtype.val h)))

private lemma appTop_injective_of_map_genericPoint {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (hη : f (genericPoint Y) = genericPoint X) : Function.Injective f.appTop := by
  let := (isField_stalk_of_map_genericPoint f hη).toField
  intro a b hab
  apply germ_injective_of_isIntegral X (U := ⊤) (f (genericPoint Y)) trivial
  apply (f.stalkMap (genericPoint Y)).hom.injective
  exact (ConcreteCategory.congr_hom (f.germ_stalkMap ⊤ (genericPoint Y) trivial) a).trans
    ((congrArg (Y.presheaf.Γgerm (genericPoint Y)) hab).trans
      (ConcreteCategory.congr_hom (f.germ_stalkMap ⊤ (genericPoint Y) trivial) b).symm)

private lemma depth_ge_two_of_normal
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hnormal : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) A := by
  let m := IsLocalRing.maximalIdeal A
  have hloc :=
    (isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth
      (R := A)).mp (fun p hp ↦ @hnormal p hp) |>.2 m
  have hdimloc : 2 ≤ ringKrullDim (Localization.AtPrime m) := by
    rwa [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)]
  have hdepthLoc : 2 ≤ Module.depth (Localization.AtPrime m)
      (IsLocalRing.maximalIdeal (Localization.AtPrime m)) (Localization.AtPrime m) := by
    rw [min_eq_left hdimloc] at hloc
    exact WithBot.coe_le_coe.mp hloc
  exact (Module.depth_self_eq_of_ringEquiv (localAtMaxEquiv A)).symm ▸ hdepthLoc

private lemma hasGoingDown_of_torsionFree
    (R S : Type*) [CommRing R] [CommRing S] [IsDomain R]
    [IsIntegrallyClosed R] [Algebra R S] [Algebra.IsIntegral R S]
    [Module.IsTorsionFree R S] : Algebra.HasGoingDown R S := by
  constructor
  intro p hp Q hQ hpQ
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal S) ≤ Q)
  have : P.IsPrime := hP.1.1
  have hinj : Function.Injective (algebraMap R (S ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hn
    have hrP : algebraMap R S r ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hr
    apply notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hrP hP
    rw [mem_nonZeroDivisors_iff_right]
    intro s hs
    exact (smul_eq_zero.mp
      (show r • s = 0 by simpa [Algebra.smul_def, mul_comm] using hs)).resolve_left hn
  have : FaithfulSMul R (S ⧸ P) := (faithfulSMul_iff_algebraMap_injective R (S ⧸ P)).mpr hinj
  have : Algebra.HasGoingDown R (S ⧸ P) := inferInstance
  let Q' := Q.map (Ideal.Quotient.mk P)
  have hcomap : Q'.comap (Ideal.Quotient.mk P) = Q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hPQ]
  have : Q'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hPQ)
  have hpQ' : p < Q'.under R := by
    change p < (Q'.comap (Ideal.Quotient.mk P)).comap (algebraMap R S)
    rwa [hcomap]
  obtain ⟨p', hp'Q', hprime, hover⟩ :=
    Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt Q' hpQ'
  exact ⟨p'.comap (Ideal.Quotient.mk P), (Ideal.comap_mono hp'Q').trans_eq hcomap, inferInstance,
    ⟨hover.over⟩⟩

private lemma finiteNormalTorsionFree_closed_stalk_depth_ge_two
    (A B : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B]
    (hA : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (hB : IsNormalRing B) :
    ∀ y : Spec (.of B), IsClosed ({y} : Set (Spec (.of B))) →
      2 ≤ Module.depth ((Spec (.of B)).presheaf.stalk y)
        (IsLocalRing.maximalIdeal ((Spec (.of B)).presheaf.stalk y))
        ((Spec (.of B)).presheaf.stalk y) := by
  obtain ⟨_, _⟩ := normal_local_ring_domain_integrallyClosed A hA
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  intro y hy
  have hqmax : y.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
  let m := IsLocalRing.maximalIdeal A
  have hmmax : (y.asIdeal.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal y.asIdeal
  have hunder : y.asIdeal.comap (algebraMap A B) = m := IsLocalRing.eq_maximalIdeal hmmax
  have : y.asIdeal.LiesOver m := ⟨hunder.symm⟩
  have : Algebra.HasGoingDown A B := hasGoingDown_of_torsionFree A B
  have hmheight : (2 : ℕ∞) ≤ m.height := WithBot.coe_le_coe.mp
    (hdim.trans_eq (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).symm)
  have hqheight : (2 : ℕ∞) ≤ y.asIdeal.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (R := A) (S := B) m y.asIdeal]
    exact hmheight.trans (le_add_right le_rfl)
  have hdimq : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime y.asIdeal) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal]
    exact WithBot.coe_le_coe.mpr hqheight
  obtain ⟨_, _⟩ := @hB y.asIdeal inferInstance
  have hdepthq := depth_ge_two_of_normal (Localization.AtPrime y.asIdeal)
    (.of_isIntegrallyClosed _) hdimq
  let e := (Spec.stalkIso (.of B) y).commRingCatIsoToRingEquiv
  exact (Module.depth_self_eq_of_ringEquiv e.symm).symm ▸ hdepthq

private lemma finiteNormalSpec_sections_iso
    (A B : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] (hA : IsNormalRing A)
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (hB : IsNormalRing B) :
    ∃ e : Spec (.of B) ≅
        Spec Γ(Spec (.of B),
          (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op) ⁻¹ᵁ
            Stacks.Divisors.puncturedSpectrum A),
      e.hom ≫ Spec.map ((Spec (.of B)).presheaf.map (homOfLE le_top).op) =
        (Spec (.of B)).toSpecΓ := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let f : Spec (.of B) ⟶ Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op
  have : IsFinite f :=
    (IsFinite.SpecMap_iff _).2
      (RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite A B))
  exact AlgebraicGeometry.exists_iso_spec_sections_punctured_spectrum A f
    (finiteNormalTorsionFree_closed_stalk_depth_ge_two A B hA hdim hB)

private lemma finiteNormalSpec_extension_appTop_isIso
    (A B : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (hA : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (hB : IsNormalRing B)
    {V : Scheme.{u}} (π : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    (g : V ⟶ Spec (.of B))
    (hp : IsPullback π g (Stacks.Divisors.puncturedSpectrum A).ι
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))) : IsIso g.appTop := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let U := Stacks.Divisors.puncturedSpectrum A
  let W := f ⁻¹ᵁ U
  obtain ⟨e, he⟩ := finiteNormalSpec_sections_iso A B hA hdim hB
  let r := (Spec (.of B)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
  have : IsIso (Spec.map r) := by
    have : IsIso (e.hom ≫ Spec.map r) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_left e.hom _
  have : IsIso r := (ConcreteCategory.isIso_iff_bijective r).mpr
    ((isIso_SpecMap_iff).mp inferInstance)
  have hi : W.ι.appTop ≫ W.topIso.hom = r := by
    simp only [Scheme.Hom.appTop, Scheme.Opens.ι_app, Scheme.Opens.topIso]
    rfl
  have : IsIso (W.ι.appTop ≫ W.topIso.hom) := hi.symm ▸ inferInstance
  have : IsIso W.ι.appTop := IsIso.of_isIso_comp_right _ W.topIso.hom
  let eV : V ≅ W.toScheme :=
    hp.isoPullback ≪≫ pullbackSymmetry U.ι f ≪≫ pullbackRestrictIsoRestrict f U
  have heg : eV.hom ≫ W.ι = g := by
    change ((hp.isoPullback.hom ≫ (pullbackSymmetry U.ι f).hom) ≫
      (pullbackRestrictIsoRestrict f U).hom) ≫ W.ι = g
    rw [Category.assoc, pullbackRestrictIsoRestrict_hom_ι,
      Category.assoc, pullbackSymmetry_hom_comp_fst, hp.isoPullback_hom_snd]
  have : IsIso eV.hom := inferInstance
  have : IsIso eV.hom.appTop := by
    change IsIso (eV.hom.app ⊤)
    infer_instance
  have h : IsIso (W.ι.appTop ≫ eV.hom.appTop) := inferInstance
  rwa [← Scheme.Hom.comp_appTop, heg] at h

private lemma exists_finite_normal_extension_of_finiteEtale
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A)
    {V : Scheme.{u}} [IsIntegral V]
    (π : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme) [IsFinite π] [Etale π] :
    ∃ (B : CommAlgCat.{u} A) (_ : Module.Finite A B) (_ : IsDomain B)
      (_ : Module.IsTorsionFree A B), IsNormalRing B ∧
      ∃ g : V ⟶ Spec (.of B), IsPullback π g (Stacks.Divisors.puncturedSpectrum A).ι
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  obtain ⟨_, _⟩ := normal_local_ring_domain_integrallyClosed A hA
  let X := Spec (.of A)
  let U := Stacks.Divisors.puncturedSpectrum A
  let f := π ≫ U.ι
  have : QuasiCompact U.ι := inferInstance
  have : IsNormal X := normalSpec_of_normalRing A hA
  have : IsNormal V := AlgebraicGeometry.isNormal_of_etale f
  let eA := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ(X, ⊤) := isNoetherianRing_of_ringEquiv A eA.symm
  have : IsIntegrallyClosed Γ(X, ⊤) := IsIntegrallyClosed.of_equiv eA.symm
  let := f.appTop.hom.toAlgebra
  let C := integralClosure Γ(X, ⊤) Γ(V, ⊤)
  have hf : Function.Injective f.appTop :=
    appTop_injective_of_map_genericPoint f (flat_map_genericPoint f)
  have : FaithfulSMul Γ(X, ⊤) Γ(V, ⊤) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  have : Module.Finite Γ(X, ⊤) C := finite_integralClosure_sections_of_etale f
  have : IsIntegrallyClosed Γ(V, ⊤) := AlgebraicGeometry.normal_globalSections V
  have : IsIntegrallyClosed C :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn C Γ(V, ⊤)
  let : Algebra A Γ(X, ⊤) := eA.symm.toRingHom.toAlgebra
  let : Algebra A C := ((algebraMap Γ(X, ⊤) C).comp eA.symm.toRingHom).toAlgebra
  have : IsScalarTower A Γ(X, ⊤) C := .of_algebraMap_eq' rfl
  have : Module.Finite A Γ(X, ⊤) := eA.symm.finite
  have : Module.Finite A C := Module.Finite.trans Γ(X, ⊤) C
  have : FaithfulSMul Γ(X, ⊤) C :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (fun a b h => hf (congrArg Subtype.val h))
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    ((FaithfulSMul.algebraMap_injective Γ(X, ⊤) C).comp eA.symm.injective)
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  let e := affineNormalizationIsoSpec f
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) =
      f.fromNormalization := by
    rw [← affineNormalizationIsoSpec_comp_fromNormalization f,
      Scheme.isoSpec_Spec_inv]
    change e.hom ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap Γ(X, ⊤) C).comp eA.symm.toRingHom)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  refine ⟨CommAlgCat.of A C, inferInstance, inferInstance, inferInstance,
    .of_isIntegrallyClosed C, f.toNormalization ≫ e.hom, ?_⟩
  apply (finiteCover_isPullback_normalization U.ι π).flip.of_iso
    (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp
  · simp [f]
  · simp [U]
  · simpa using he.symm

private lemma finite_sections_of_integral_finiteEtale
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    {V : Scheme.{u}} [IsIntegral V]
    (π : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme) [IsFinite π] [Etale π] :
    letI : Algebra A Γ(V, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫
      (π ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop).hom.toAlgebra
    Module.Finite A Γ(V, ⊤) := by
  obtain ⟨B, hfinite, hdom, htf, hB, g, hp⟩ :=
    exists_finite_normal_extension_of_finiteEtale A hA π
  have := hfinite
  have := htf
  have : IsIso g.appTop := finiteNormalSpec_extension_appTop_isIso A B hA hdim hB π g hp
  change (((Scheme.ΓSpecIso (.of A)).inv ≫
    (π ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop).hom).Finite
  rw [hp.w, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, CommRingCat.hom_comp]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of B)).inv ≫ g.appTop)).2).comp
    (RingHom.finite_algebraMap.mpr hfinite)

private lemma puncturedSpectrum_baseMap_isIso
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    IsIso ((Scheme.ΓSpecIso (.of A)).inv ≫
      (Stacks.Divisors.puncturedSpectrum A).ι.appTop) := by
  have : IsDomain A := (normal_local_ring_domain_integrallyClosed A hA).1
  let U := Stacks.Divisors.puncturedSpectrum A
  have : Module.IsTorsionFree A A := inferInstance
  have hp : IsPullback (𝟙 U.toScheme) U.ι U.ι
      (Spec.map (CommRingCat.ofHom (algebraMap A A))) := by
    convert (IsPullback.of_id_fst (f := U.ι)) using 1
    simp
  have : IsIso U.ι.appTop :=
    finiteNormalSpec_extension_appTop_isIso A A hA hdim hA (𝟙 _) U.ι hp
  infer_instance

private lemma affineCover_isPullback_toSpecΓ
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (V : Scheme.{u}) (π : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    [IsAffineHom π] :
    IsPullback π V.toSpecΓ (Stacks.Divisors.puncturedSpectrum A).ι
      (Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫
        (π ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop)) := by
  let U := Stacks.Divisors.puncturedSpectrum A
  have := compactSpace_puncturedSpectrum A
  have : U.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion U.ι
  let e := (Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop
  have : IsIso e := puncturedSpectrum_baseMap_isIso A hA hdim
  apply (Scheme.isPullback_toSpecΓ_toSpecΓ π).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso (Spec.map e))
  · simp
  · simp
  · simp only [Iso.refl_hom, asIso_hom, e, Spec.map_comp]
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality U.ι, Category.assoc]
    simp [toSpecΓ_SpecMap_ΓSpecIso_inv, U]
  · simp only [asIso_hom, Iso.refl_hom, Category.id_comp]
    rw [← Spec.map_comp]
    congr 1

/-- Finite normal `A`-algebras, torsion-free over `A`, whose spectra are étale over the
punctured spectrum of `A`. -/
public abbrev NormalFiniteEtaleAwayAlgebra
    (A : Type u) [CommRing A] [IsLocalRing A] :=
  ObjectProperty.FullSubcategory fun B : CommAlgCat.{u} A =>
    Module.Finite A B ∧ IsNormalRing B ∧ Module.IsTorsionFree A B ∧
      Etale (pullback.snd
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)
        (Stacks.Divisors.puncturedSpectrum A).ι)

/-- Global sections of a scheme over the punctured spectrum, with its induced `A`-algebra
structure. -/
@[instance_reducible]
public noncomputable def globalSectionsAlgebra
    (A : Type u) [CommRing A] [IsLocalRing A]
    (V : FiniteEtaleOver (Stacks.Divisors.puncturedSpectrum A).toScheme) :
    Algebra A Γ(V.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫
    (V.hom ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop).hom.toAlgebra

/-- Global sections of a scheme over the punctured spectrum, with its induced `A`-algebra
structure. -/
public noncomputable def globalSections
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (FiniteEtaleOver (Stacks.Divisors.puncturedSpectrum A).toScheme)ᵒᵖ ⥤
      CommAlgCat.{u} A where
  obj V :=
    let := globalSectionsAlgebra A V.unop
    CommAlgCat.of A Γ(V.unop.left, ⊤)
  map {V W} f :=
    let := globalSectionsAlgebra A V.unop
    let := globalSectionsAlgebra A W.unop
    CommAlgCat.ofHom
      { f.unop.left.appTop.hom with
        commutes' := by
          intro a
          change f.unop.left.appTop
              ((V.unop.hom ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop
                ((Scheme.ΓSpecIso (.of A)).inv a)) =
            (W.unop.hom ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop
              ((Scheme.ΓSpecIso (.of A)).inv a)
          have h : f.unop.left ≫ V.unop.hom ≫
              (Stacks.Divisors.puncturedSpectrum A).ι =
              W.unop.hom ≫ (Stacks.Divisors.puncturedSpectrum A).ι := by
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ (Stacks.Divisors.puncturedSpectrum A).ι)
                (MorphismProperty.Over.w f.unop)
          simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
            congrArg (fun q => q.hom ((Scheme.ΓSpecIso (.of A)).inv a))
              (congrArg Scheme.Hom.appTop h) }
  map_id V := by
    let := globalSectionsAlgebra A V.unop
    exact CommAlgCat.Hom.ext <| AlgHom.ext fun _ => rfl
  map_comp {X Y Z} f g := by
    let := globalSectionsAlgebra A X.unop
    let := globalSectionsAlgebra A Y.unop
    let := globalSectionsAlgebra A Z.unop
    apply CommAlgCat.Hom.ext
    apply AlgHom.ext
    intro x
    change (g.unop.left ≫ f.unop.left).appTop x =
      g.unop.left.appTop (f.unop.left.appTop x)
    rw [Scheme.Hom.comp_appTop]
    rfl

private lemma finite_globalSections
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (V : FiniteEtaleOver (Stacks.Divisors.puncturedSpectrum A).toScheme) :
    letI := globalSectionsAlgebra A V
    Module.Finite A Γ(V.left, ⊤) := by
  obtain ⟨ι, hι, Y, hnormal, hintegral, ⟨e⟩⟩ :=
    finiteEtaleOver_puncturedSpectrum_components A hA V
  have := hι
  apply finite_sections_of_finite_components A
    (V.hom ≫ (Stacks.Divisors.puncturedSpectrum A).ι) e
  intro i
  have := hintegral i
  obtain ⟨_, _⟩ := finiteEtaleOver_component_map V e i
  simpa +instances only [Category.assoc] using
    finite_sections_of_integral_finiteEtale A hA hdim (Sigma.ι Y i ≫ e.inv ≫ V.hom)

private lemma normalRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (hS : IsNormalRing S) : IsNormalRing R := by
  intro p hp
  have := hp
  obtain ⟨hd, hi⟩ := @hS (p.comap e.symm.toRingHom) inferInstance
  have := hd
  have := hi
  let f := Localization.localRingEquiv p (p.comap e.symm.toRingHom) e
    (Ideal.comap_of_equiv e).symm
  exact ⟨f.injective.isDomain f.toRingHom, IsIntegrallyClosed.of_equiv f.symm⟩

private lemma normal_globalSections
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A)
    (V : FiniteEtaleOver (Stacks.Divisors.puncturedSpectrum A).toScheme) :
    IsNormalRing Γ(V.left, ⊤) := by
  obtain ⟨ι, hι, Y, hnormal, hintegral, ⟨e⟩⟩ :=
    finiteEtaleOver_puncturedSpectrum_components A hA V
  have := hι
  have hpi := isNormalRing_pi (ι := ι) (R := fun i => Γ(Y i, ⊤)) (fun i => by
    have := hintegral i
    have := hnormal i
    have := AlgebraicGeometry.normal_globalSections (Y i)
    intro p hp
    exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization
      (S := Localization.AtPrime p) p.primeCompl p.primeCompl_le_nonZeroDivisors⟩)
  apply normalRing_of_ringEquiv (coproductSectionsRingEquiv e)
  intro p hp
  have := hp
  exact ⟨(hpi p).1, (hpi p).2⟩

private lemma torsionFree_globalSections
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A)
    (V : FiniteEtaleOver (Stacks.Divisors.puncturedSpectrum A).toScheme) :
    letI : Algebra A Γ(V.left, ⊤) := globalSectionsAlgebra A V
    Module.IsTorsionFree A Γ(V.left, ⊤) := by
  have : IsDomain A := (normal_local_ring_domain_integrallyClosed A hA).1
  obtain ⟨ι, hι, Y, hnormal, hintegral, ⟨e⟩⟩ :=
    finiteEtaleOver_puncturedSpectrum_components A hA V
  let f := V.hom ≫ (Stacks.Divisors.puncturedSpectrum A).ι
  let : Algebra A Γ(V.left, ⊤) := globalSectionsAlgebra A V
  let : ∀ i, Algebra A Γ(Y i, ⊤) := fun i =>
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (Sigma.ι Y i ≫ e.inv ≫ f).appTop).hom.toAlgebra
  have : ∀ i, Module.IsTorsionFree A Γ(Y i, ⊤) := fun i => by
    have := hintegral i
    have := (finiteEtaleOver_component_map V e i).2
    let g := (Sigma.ι Y i ≫ e.inv ≫ V.hom) ≫ (Stacks.Divisors.puncturedSpectrum A).ι
    have : Etale g := inferInstance
    have hg := appTop_injective_of_map_genericPoint g (flat_map_genericPoint g)
    have : FaithfulSMul A Γ(Y i, ⊤) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr
        (hg.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).1)
    exact Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  let eΓ : Γ(V.left, ⊤) ≃ₐ[A] (∀ i, Γ(Y i, ⊤)) :=
    coproductSectionsAlgEquiv A f e
  exact eΓ.injective.moduleIsTorsionFree eΓ (fun a x => map_smul eΓ.toLinearMap a x)

private lemma globalSections_properties
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (V : FiniteEtaleOver (Stacks.Divisors.puncturedSpectrum A).toScheme) :
    letI : Algebra A Γ(V.left, ⊤) := globalSectionsAlgebra A V
    Module.Finite A Γ(V.left, ⊤) ∧ IsNormalRing Γ(V.left, ⊤) ∧
      Module.IsTorsionFree A Γ(V.left, ⊤) ∧
      Etale (pullback.snd (Spec.map (CommRingCat.ofHom
        (algebraMap A Γ(V.left, ⊤)))) (Stacks.Divisors.puncturedSpectrum A).ι) := by
  let : Algebra A Γ(V.left, ⊤) := globalSectionsAlgebra A V
  refine ⟨finite_globalSections A hA hdim V, normal_globalSections A hA V,
    torsionFree_globalSections A hA V, ?_⟩
  have : IsFinite V.hom := V.prop.1
  have : Etale V.hom := V.prop.2
  let hp := (affineCover_isPullback_toSpecΓ A hA hdim V.left V.hom).flip
  have h : Etale (hp.isoPullback.inv ≫ V.hom) := inferInstance
  change Etale (pullback.snd (Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫
    (V.hom ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop))
      (Stacks.Divisors.puncturedSpectrum A).ι)
  simpa only [hp.isoPullback_inv_snd] using h

/-- The global sections of a finite étale cover of the punctured spectrum of a Noetherian normal
local ring of dimension at least two form a finite normal `A`-algebra, torsion-free over `A`,
whose spectrum is étale over the punctured spectrum — that is, they lie in the target category
of [Stacks, Tag 0BM9]. -/
public alias globalSections_finite_normal_torsionFree_etale := globalSections_properties

private noncomputable def normalAlgebraPuncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : NormalFiniteEtaleAwayAlgebra A) :
    FiniteEtaleOver (Stacks.Divisors.puncturedSpectrum A).toScheme := by
  let f : Spec (.of B.obj) ⟶ Spec (.of A) :=
    Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B.obj)).op
  let : IsFinite f := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.mpr B.property.1)
  let p : pullback f (Stacks.Divisors.puncturedSpectrum A).ι ⟶
      (Stacks.Divisors.puncturedSpectrum A).toScheme := pullback.snd f _
  exact MorphismProperty.Over.mk ⊤ p ⟨inferInstance, B.property.2.2.2⟩

private lemma normalAlgebra_iso_globalSections
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (B : NormalFiniteEtaleAwayAlgebra A) :
    Nonempty (B.obj ≅ (globalSections A).obj
      (Opposite.op (normalAlgebraPuncturedSpectrum A B))) := by
  let V := normalAlgebraPuncturedSpectrum A B
  let U := Stacks.Divisors.puncturedSpectrum A
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B.obj))
  let g : V.left ⟶ Spec (.of B.obj) := pullback.fst f U.ι
  have hp : IsPullback V.hom g U.ι f := (IsPullback.of_hasPullback f U.ι).flip
  have : Module.Finite A B.obj := B.property.1
  have : Module.IsTorsionFree A B.obj := B.property.2.2.1
  have : IsIso g.appTop :=
    finiteNormalSpec_extension_appTop_isIso A B.obj hA hdim B.property.2.1 V.hom g hp
  let := globalSectionsAlgebra A V
  let φ : B.obj →ₐ[A] Γ(V.left, ⊤) :=
    { (((Scheme.ΓSpecIso (.of B.obj)).inv ≫ g.appTop).hom) with
      commutes' := by
        intro a
        change (((CommRingCat.ofHom (algebraMap A B.obj)) ≫
          (Scheme.ΓSpecIso (.of B.obj)).inv ≫ g.appTop).hom a) =
          (((Scheme.ΓSpecIso (.of A)).inv ≫ (V.hom ≫ U.ι).appTop).hom a)
        rw [Scheme.ΓSpecIso_inv_naturality_assoc, hp.w, Scheme.Hom.comp_appTop] }
  exact ⟨CommAlgCat.isoMk (AlgEquiv.ofBijective φ
    (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of B.obj)).inv ≫ g.appTop)))⟩

private lemma appTop_eq_of_comp_toSpecΓ_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) (φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤))
    (h : f ≫ Y.toSpecΓ = X.toSpecΓ ≫ Spec.map φ) : f.appTop = φ := by
  have h' := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h'
  rw [Scheme.ΓSpecIso_naturality φ] at h'
  exact (cancel_epi (Scheme.ΓSpecIso Γ(Y, ⊤)).hom).mp h'

private lemma globalSections_full
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    (globalSections A).Full := by
  constructor
  intro V W φ
  let U := Stacks.Divisors.puncturedSpectrum A
  have : IsFinite V.unop.hom := V.unop.prop.1
  have : IsFinite W.unop.hom := W.unop.prop.1
  let pv := affineCover_isPullback_toSpecΓ A hA hdim V.unop.left V.unop.hom
  let pw := affineCover_isPullback_toSpecΓ A hA hdim W.unop.left W.unop.hom
  let φr : Γ(V.unop.left, ⊤) ⟶ Γ(W.unop.left, ⊤) :=
    CommRingCat.ofHom φ.hom.toRingHom
  have hc : ((Scheme.ΓSpecIso (.of A)).inv ≫
      (V.unop.hom ≫ U.ι).appTop) ≫ φr =
        (Scheme.ΓSpecIso (.of A)).inv ≫ (W.unop.hom ≫ U.ι).appTop := by
    ext a
    exact φ.hom.commutes a
  let k := W.unop.left.toSpecΓ ≫ Spec.map φr
  have hk : W.unop.hom ≫ U.ι = k ≫
      Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫
        (V.unop.hom ≫ U.ι).appTop) := by
    rw [show k ≫ _ = W.unop.left.toSpecΓ ≫ Spec.map
      (((Scheme.ΓSpecIso (.of A)).inv ≫ (V.unop.hom ≫ U.ι).appTop) ≫ φr) by
        simp only [k, Spec.map_comp, Category.assoc], hc]
    exact pw.w
  let g := pv.lift W.unop.hom k hk
  let g' : W.unop ⟶ V.unop := MorphismProperty.Over.homMk g
    (pv.lift_fst W.unop.hom k hk)
  exact ⟨g'.op, CommAlgCat.Hom.ext <| AlgHom.ext fun x =>
    congrArg (fun f : Γ(V.unop.left, ⊤) ⟶ Γ(W.unop.left, ⊤) => f.hom x)
      (appTop_eq_of_comp_toSpecΓ_eq g φr (pv.lift_snd W.unop.hom k hk))⟩

private lemma globalSections_faithful
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    (globalSections A).Faithful := by
  constructor
  intro V W f g h
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  have : IsFinite V.unop.hom := V.unop.prop.1
  let pv := affineCover_isPullback_toSpecΓ A hA hdim V.unop.left V.unop.hom
  apply pv.hom_ext
  · exact (MorphismProperty.Over.w f.unop).trans (MorphismProperty.Over.w g.unop).symm
  · rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality]
    congr 2
    ext x
    exact congrArg (fun k => k.hom x) h

/-- **Stacks Project, Tag 0BM9.** On a Noetherian normal local ring of dimension at least two,
global sections give an equivalence from the opposite of the category of finite étale covers of
the punctured spectrum to finite normal torsion-free algebras which are étale there. -/
@[stacks 0BM9 "the equivalence"]
public theorem globalSections_isEquivalence_normalFiniteEtaleAwayAlgebra
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hnormal : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    ∃ F : Functor
        (FiniteEtaleOver (Stacks.Divisors.puncturedSpectrum A).toScheme)ᵒᵖ
        (NormalFiniteEtaleAwayAlgebra A),
      F.IsEquivalence ∧ Nonempty
        (F ⋙ ObjectProperty.ι _ ≅ globalSections A) := by
  let P : ObjectProperty (CommAlgCat.{u} A) := fun B =>
    Module.Finite A B ∧ IsNormalRing B ∧ Module.IsTorsionFree A B ∧
      Etale (pullback.snd
        (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)
        (Stacks.Divisors.puncturedSpectrum A).ι)
  have hP : ∀ V, P ((globalSections A).obj V) := fun V =>
    globalSections_properties A hnormal hdim V.unop
  let F := P.lift (globalSections A) hP
  have : (globalSections A).Full := globalSections_full A hnormal hdim
  have : (globalSections A).Faithful := globalSections_faithful A hnormal hdim
  have : F.EssSurj := ⟨fun B => by
    obtain ⟨e⟩ := normalAlgebra_iso_globalSections A hnormal hdim B
    exact ⟨Opposite.op (normalAlgebraPuncturedSpectrum A B), ⟨P.isoMk e.symm⟩⟩⟩
  exact ⟨F, {}, ⟨P.liftCompιIso (globalSections A) hP⟩⟩

/-- **Stacks Project, Tag 0BM9.** A finite étale cover of the punctured spectrum extends to a
finite étale cover of the whole spectrum exactly when its ring of global sections is finite
étale over the base ring. -/
@[stacks 0BM9 "the extension criterion"]
public theorem exists_finiteEtale_extension_iff_globalSections_finiteEtale
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hnormal : IsNormalRing A) (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    (V : Scheme.{u}) (π : V ⟶ (Stacks.Divisors.puncturedSpectrum A).toScheme)
    [IsFinite π] [Etale π] :
    (∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)) (g : V ⟶ Y),
      IsFinite f ∧ Etale f ∧ IsPullback π g (Stacks.Divisors.puncturedSpectrum A).ι f) ↔
      letI : Algebra A Γ(V, ⊤) :=
        ((Scheme.ΓSpecIso (.of A)).inv ≫
          (π ≫ (Stacks.Divisors.puncturedSpectrum A).ι).appTop).hom.toAlgebra
      Module.Finite A Γ(V, ⊤) ∧ Algebra.Etale A Γ(V, ⊤) :=
  _root_.AlgebraicGeometry.exists_finiteEtale_extension_iff_globalSections_finiteEtale
    A V π (depth_ge_two_of_normal A hnormal hdim)

end AlgebraicGeometry.NormalPurity
