module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraChartIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystemOfSymmetricAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent

/-!
# A finite scheme over an algebraic space is closed in a finite and finitely presented scheme

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, `p : h_V ⟶ X`
an étale morphism from an affine scheme, and `f : h_Y ⟶ X` a finite morphism from a scheme which
factors through `p` Zariski locally on `Y`. Then `f` factors as a closed immersion `h_Y ⟶ h_T`
followed by a finite morphism of finite presentation `h_T ⟶ X`, with `T` a scheme.

## The argument

The direct image `𝒜 = f_* 𝒪_Y` is a finite quasi-coherent `𝒪_X`-algebra, so its underlying module
is of finite type and is a quotient of a module `𝒢` of finite presentation
(`AlgebraicGeometry.Space.exists_epi_of_isFinitePresentationOnSite_of_isFiniteType`). The
morphism of algebras `Sym(𝒢) ⟶ 𝒜` extending it is surjective on affine charts, so the morphism
`g : Y ⟶ P = \underline{Spec}_X(Sym 𝒢)` over `X` is a closed immersion
(`AlgebraicGeometry.Space.isClosedImmersion_of_surjective_pushforwardRingMap_app`), and `P` is
affine and of finite presentation over `X`. Over an affine surjective étale chart `W` of `X` an
ideal of finite type `I` of the functions on `P ×_X W`, killed on `Y ×_X W`, makes the quotient
finite over `W` (monic equations,
`AlgebraicGeometry.Space.exists_ideal_finite_le_ker_smallBaseChangeOverMap`), so every closed
subspace of `P` cut out on `P ×_X W` by an ideal containing `I` is finite over `X`
(`AlgebraicGeometry.Space.isFinite_ι_comp_of_ofIdealTop_le_chartKer`). The closed subspace
`g(Y) ⊆ P` factors locally through `p`; so it lies in a closed subspace `T` of finite
presentation of `P` which is a scheme and satisfies that chart condition
(`exists_isFinitePresentation_factorsZariskiLocallyThrough_of_closedSubspace`).

## Main results

* `AlgebraicGeometry.Space.isFinite_pushforwardAlgebra_of_isFinite`: the direct image of the
  structure sheaf along a finite morphism is a finite algebra.
* `exists_isClosedImmersion_isFinite_isFinitePresentation_of_factorsZariskiLocallyThrough`:
  a finite morphism from a scheme to `X` factoring through `p` Zariski locally factors as a
  closed immersion into a scheme followed by a finite morphism of finite presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- An affine morphism of algebraic spaces is representable by schemes, with affine
base changes. -/
private theorem relativelyRepresentable_and_presheaf_isAffineHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsAffineHom B S hS f) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  ((isAffineHom_tfae_of_isAlgebraicSpace B S hS f hX hY).out 2 1).mp hf

/-- **The direct image of the structure sheaf along a finite morphism is a finite algebra**: on
every affine étale chart of the target its structure-algebra map is finite. -/
theorem isFinite_pushforwardAlgebra_of_isFinite {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsFinite B S hS f.hom) : (pushforwardAlgebra B S hS (Over.mk f)).IsFinite := by
  intro W hW
  have hrep : yoneda.relativelyRepresentable f.hom :=
    (relativelyRepresentable_and_presheaf_isAffineHom B S hS f.hom Y.2 X.2
      (IsFinite.isAffineHom hf)).2.rep
  show RingHom.Finite ((smallEtaleRingedToposHom B S hS (Over.mk f).hom).fSharp.hom.app
    (op W)).hom
  rw [pushforwardAlgebra_algebraMap_eq_comp B S hS f hrep W]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (pushforwardAlgebraSectionsIso B S hS (Over.mk f) hrep W).inv).2
  · rw [← smallBaseChangeChartRingHom_eq B S hS f hrep W]
    exact finite_smallBaseChangeChartRingHom B S hS f hf hrep W hW

/-- **A finite scheme over a quasi-compact quasi-separated algebraic space, factoring Zariski
locally through an affine étale chart, is closed in a finite and finitely presented scheme.**
Let `X` be a quasi-compact and quasi-separated algebraic space, `p : h_V ⟶ X` étale with `V`
affine, and `f : h_Y ⟶ X` finite, factoring through `p` Zariski locally on `Y`. Then there are an
object `T` of the big fppf site, a finite morphism of finite presentation `g : h_T ⟶ X` and a
closed immersion `i : h_Y ⟶ h_T` with `i ≫ g = f`. -/
theorem exists_isClosedImmersion_isFinite_isFinitePresentation_of_factorsZariskiLocallyThrough
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (p : yoneda.obj V ⟶ X) (hp : IsEtale B S hS p) (Y : BigFppfOver B S hS)
    (f : yoneda.obj Y ⟶ X) (hf : IsFinite B S hS f)
    (hfac : FactorsZariskiLocallyThrough B S hS p Y f) :
    ∃ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ X) (i : yoneda.obj Y ⟶ yoneda.obj T),
      IsFinite B S hS g ∧ IsFinitePresentation B S hS g ∧ IsClosedImmersion B S hS i ∧
        i ≫ g = f := by
  classical
  let Tsch := BigFppfOver.toScheme B S hS
  let Xa : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ya : AlgebraicSpaces B S hS := ⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩
  let fa : Ya ⟶ Xa := ObjectProperty.homMk f
  let Yo : Over Xa := Over.mk fa
  have hfaff : IsAffineHom B S hS f := IsFinite.isAffineHom hf
  have hYaff := relativelyRepresentable_and_presheaf_isAffineHom B S hS f Ya.2 hX hfaff
  have hYrep : yoneda.relativelyRepresentable f := hYaff.2.rep
  -- The direct image `𝒜 = f_* 𝒪_Y`, a finite quasi-coherent algebra.
  let 𝒜 := pushforwardAlgebra B S hS Yo
  have h𝒜qc : 𝒜.IsQuasicoherent :=
    isQuasicoherent_pushforwardAlgebra_of_isAffineHom' B S hS Yo hfaff
  have : (AlgebraSheaf.underlyingModule 𝒜).IsFiniteTypeOnSite :=
    isFiniteTypeOnSite_underlyingModule_of_isFinite B S hS (Y := Xa) 𝒜 h𝒜qc
      (isFinite_pushforwardAlgebra_of_isFinite B S hS fa hf)
  -- A module `𝒢` of finite presentation onto it, and `φ : Sym 𝒢 ⟶ 𝒜`.
  obtain ⟨G, hGfp, γ, hγ⟩ := exists_epi_of_isFinitePresentationOnSite_of_isFiniteType B S hS hZ
    hX hXqc hXqs (AlgebraSheaf.underlyingModule 𝒜) h𝒜qc
  have hGqc : G.IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite G
  let 𝒞 : QuasicoherentAlgebra B S hS Xa :=
    ⟨symmetricAlgebraSheaf B S hS Xa G, isQuasicoherent_symmetricAlgebraSheaf B S hS Xa G hGqc⟩
  have h𝒞 := sectionsBelowCutoff_symmetricAlgebraSheaf B S hS Xa G hGqc hGfp
  have hCfp := isFinitePresentation_symmetricAlgebraSheaf B S hS Xa G hGqc hGfp
  let φ := SymAlgSheaf.algebraLift B S hS Xa _ G γ
  have hφ : ∀ W : SmallEtale B S hS X, IsAffine (chartScheme W) →
      Function.Surjective (φ.right.hom.app (op W)) := by
    intro W hW a
    obtain ⟨y, hy⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite γ hγ hGqc h𝒜qc W hW a
    exact ⟨_, (SymAlgSheaf.algebraLift_ungradedIncl_gen B S hS Xa _ G γ (op W) y).trans hy⟩
  -- The relative spectrum `P` of `Sym 𝒢` and the morphism `g : Y ⟶ P` of `φ`.
  let P := boundedRelativeSpec B S hS 𝒞 h𝒞
  let e := pushforwardAlgebraBoundedRelativeSpecIso B S hS 𝒞 h𝒞
  let g : Yo ⟶ P.obj := (overHomEquivPushforwardAlgebraHom B S hS Yo P).symm (e.hom ≫ φ)
  have hgalg : pushforwardAlgebraMap B S hS g = e.hom ≫ φ :=
    pushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm B S hS Yo P _
  have hinvhom : ∀ (W : (SmallEtale B S hS X)ᵒᵖ) (c : 𝒞.obj.right.obj.obj W),
      (e.hom.right.hom.app W) ((e.inv.right.hom.app W) c) = c := fun W c =>
    congrArg (fun k : 𝒞.obj ⟶ 𝒞.obj => (k.right.hom.app W) c) e.inv_hom_id
  have hhominv : ∀ (W : (SmallEtale B S hS X)ᵒᵖ)
      (c : (pushforwardAlgebra B S hS P.obj).right.obj.obj W),
      (e.inv.right.hom.app W) ((e.hom.right.hom.app W) c) = c := fun W c =>
    congrArg (fun k : pushforwardAlgebra B S hS P.obj ⟶ pushforwardAlgebra B S hS P.obj =>
      (k.right.hom.app W) c) e.hom_inv_id
  have hrange : ∀ (W : (SmallEtale B S hS X)ᵒᵖ) (c : 𝒞.obj.right.obj.obj W),
      (pushforwardRingMap B S hS g).hom.app W ((e.inv.right.hom.app W) c) =
        φ.right.hom.app W c := by
    intro W c
    rw [← pushforwardAlgebraMap_right, hgalg]
    show (φ.right.hom.app W) ((e.hom.right.hom.app W) ((e.inv.right.hom.app W) c)) = _
    rw [hinvhom]
  have hPalgfp : (pushforwardAlgebra B S hS P.obj).IsFinitePresentation := by
    intro W hW
    have h1 : RingHom.FinitePresentation (𝒞.obj.algebraMap (op W)) := hCfp W hW
    have hbij : Function.Bijective (e.inv.right.hom.app (op W)).hom :=
      Function.bijective_iff_has_inverse.2 ⟨e.hom.right.hom.app (op W),
        hinvhom (op W), hhominv (op W)⟩
    have h2 : RingHom.FinitePresentation (e.inv.right.hom.app (op W)).hom := by
      refine RingHom.FinitePresentation.of_surjective _ hbij.2 ?_
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hbij.1]
      exact Submodule.fg_bot
    rw [← AlgebraSheaf.comp_algebraMap e.inv (op W)]
    exact h2.comp h1
  have hPfp : IsFinitePresentation B S hS P.obj.hom.hom :=
    isFinitePresentation_of_isFinitePresentation_pushforwardAlgebra B S hS hXqc P hPalgfp
  let qP : P.obj.left.1 ⟶ X := P.obj.hom.hom
  let gY : yoneda.obj Y ⟶ P.obj.left.1 := g.left.hom
  have hgq : gY ≫ qP = f := by
    rw [← ObjectProperty.FullSubcategory.comp_hom]
    exact congrArg (fun m : Yo.left ⟶ Xa => m.hom) (Over.w g)
  -- `g` is a closed immersion.
  have hgcl : IsClosedImmersion B S hS gY :=
    isClosedImmersion_of_surjective_pushforwardRingMap_app B S hS hXqc ⟨Yo, hfaff⟩ P g
      fun W hW c => by
        obtain ⟨c', hc'⟩ := hφ W hW c
        exact ⟨_, (hrange (op W) c').trans hc'⟩
  have hgmono : Mono gY := mono_of_isClosedImmersion B S hS _ hgcl
  -- `P` is quasi-compact, quasi-separated and representable over `X`.
  have hPaff := relativelyRepresentable_and_presheaf_isAffineHom B S hS qP P.obj.left.2 hX
    P.property
  have hPrep : yoneda.relativelyRepresentable qP := hPaff.2.rep
  have hPqc : IsQuasiCompactSpace B S hS P.obj.left.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hX hXqc hPfp.2.1
  have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ P.obj.left.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ P.obj.left.2 hXqs hPfp.2.2
  -- Monic equations over an affine surjective étale chart `W` of `X`.
  obtain ⟨Ws, hWsaff, hWssurj⟩ := exists_smallEtale_isAffine_surjective B S hS (X := Xa) hXqc
  have : IsAffine (Tsch.obj Ws.1.left) := hWsaff
  have hWsurj : IsSurjective B S hS Ws.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX _ Ws.1.hom).1 hWssurj
  have hWet : IsEtale B S hS Ws.1.hom := isEtale_of_presheaf_etale B S hS Ws.2
  have : IsAffine (Tsch.obj (hPrep.pullback Ws.1.hom)) :=
    @isAffine_of_isAffineHom _ _ (Tsch.map (hPrep.snd Ws.1.hom))
      (hPaff.2.property Ws.1.hom (hPrep.fst _) (hPrep.snd _) (hPrep.isPullback _)) hWsaff
  have hint : RingHom.IsIntegral (Tsch.map (hYrep.snd Ws.obj.hom)).appTop.hom := by
    have h := finite_smallBaseChangeChartRingHom B S hS fa hf hYrep Ws hWsaff
    rw [smallBaseChangeChartRingHom_eq B S hS fa hYrep Ws] at h
    exact RingHom.IsIntegral.of_finite h
  obtain ⟨I, hIfg, hI, hIker⟩ := exists_ideal_finite_le_ker_smallBaseChangeOverMap B S hS g hYrep
    hPrep Ws (RingHom.FiniteType.of_finitePresentation (hPalgfp Ws hWsaff)) hint
  let m := smallBaseChangeOverMap B S hS g hYrep hPrep Ws
  have sqW : IsPullback (hYrep.fst Ws.1.hom) (yoneda.map m) gY (hPrep.fst Ws.1.hom) :=
    isPullback_fst_smallBaseChangeOverMap B S hS g hYrep hPrep Ws
  have hle : Scheme.IdealSheafData.ofIdealTop I ≤ (Tsch.map m).ker := by
    rw [Scheme.ker_of_isAffine]
    exact (map_le_map_iff (Scheme.IdealSheafData.equivOfIsAffine
      (X := Tsch.obj (hPrep.pullback Ws.1.hom))).symm).2 hIker
  have hJt : (Scheme.IdealSheafData.ofIdealTop I).IsFiniteType := fun W => by
    rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    exact hIfg.map _
  have hPfst : IsEtale B S hS (hPrep.fst Ws.1.hom) :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS (hPrep.isPullback _)
      (isAlgebraicSpace_yoneda B S hS _) P.obj.left.2 (isAlgebraicSpace_yoneda B S hS _) hX hWet
  -- The closed subspace `C = g(Y)` of `P`.
  let C : ClosedSubspaces B S hS P.obj.left.1 :=
    ⟨Subfunctor.range gY, isClosedSubspace_range_of_isClosedImmersion B S hS gY Ya.2 hgcl⟩
  have hJtC : Scheme.IdealSheafData.ofIdealTop I ≤ chartKer B S hS P.obj.left C
      (hPrep.fst Ws.1.hom) := by
    rw [le_chartKer_iff]
    show (Subfunctor.range gY).preimage _ ≤ _
    rw [← Subfunctor.range_eq_preimage_of_isPullback sqW.flip]
    exact range_yoneda_map_le_idealPoints B S hS m _ hle
  let ε : yoneda.obj Y ≅ (Subfunctor.range gY).toFunctor := asIso (Subfunctor.toRange gY)
  have hCι : (Subfunctor.range gY).ι = ε.inv ≫ gY := (inv_toRange_comp gY).symm
  have hCfac : ∀ x : points B S hS C.1.toFunctor, ∃ W : Subfunctor C.1.toFunctor,
      IsOpenSubspace B S hS W ∧ x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) ∧
      ∃ c : W.toFunctor ⟶ yoneda.obj V, W.ι ≫ C.1.ι ≫ qP = c ≫ p := by
    intro x
    obtain ⟨W', hW', -, hy, c', hc'⟩ := hfac (pointsMap B S hS C.1.toFunctor ε.inv x)
    refine ⟨W'.preimage ε.inv, isOpenSubspace_preimage B S hS ε.inv W'
      (isAlgebraicSpace_yoneda B S hS Y) C.2.1 hW', ?_, W'.fromPreimage ε.inv ≫ c', ?_⟩
    · rw [range_pointsMap_preimage_ι]
      exact hy
    · show (W'.preimage ε.inv).ι ≫ (Subfunctor.range gY).ι ≫ qP = _
      rw [hCι, Category.assoc, Category.assoc, hgq, ← hc',
        ← Category.assoc (W'.fromPreimage ε.inv), Subfunctor.fromPreimage_ι, Category.assoc]
  -- A closed subspace `T ⊇ C` of finite presentation which is a scheme.
  have : ∀ _ : Fin 1, CompactSpace (Tsch.obj (hPrep.pullback Ws.1.hom)) := fun _ =>
    inferInstance
  obtain ⟨Tc, Y', e', hTfp, hCT, hJT, -⟩ :=
    exists_isFinitePresentation_factorsZariskiLocallyThrough_of_closedSubspace B S hS hZ hX
      P.obj.left hPqc hPqs qP p hp ⟨hPrep.pullback p, hPrep.snd p, hPrep.fst p, hPrep.isPullback p⟩
      C hCfac (U := fun _ : Fin 1 => hPrep.pullback Ws.1.hom) (fun _ => hPrep.fst Ws.1.hom)
      (fun _ => (isEtale_iff_presheaf_of_yoneda B S hS _).1 hPfst)
      (fun _ => Scheme.IdealSheafData.ofIdealTop I) (fun _ => hJt) (fun _ => hJtC)
  have hTfin : IsFinite B S hS (Tc.1.ι ≫ qP) :=
    isFinite_ι_comp_of_ofIdealTop_le_chartKer B S hS hX P.obj.left qP Ws.1.hom hWsurj hWet
      (hPrep.fst _) (hPrep.snd _) (hPrep.isPullback _) I hI Tc (hJT 0)
  have hY'alg := isAlgebraicSpace_yoneda B S hS Y'
  let j : yoneda.obj Y ⟶ Tc.1.toFunctor := Subfunctor.lift gY hCT
  have hj : j ≫ Tc.1.ι = gY := Subfunctor.lift_ι gY hCT
  refine ⟨Y', e'.hom ≫ Tc.1.ι ≫ qP, j ≫ e'.inv,
    isFinite_comp B S hS (isFinite_of_isIso B S hS _) hTfin, ?_, ?_, ?_⟩
  · refine isFinitePresentation_comp B S hS hY'alg Tc.2.1 hX _ _
      ⟨isLocallyOfFinitePresentation_of_isOpenImmersion B S hS (isOpenImmersion_of_isIso B S hS _),
        isQuasiCompact_of_isIso B S hS _, isQuasiSeparated_of_mono B S hS _ inferInstance⟩
      (isFinitePresentation_comp B S hS Tc.2.1 P.obj.left.2 hX _ _ hTfp hPfp)
  · refine isClosedImmersion_of_comp_mono B S hS _ (e'.hom ≫ Tc.1.ι) ?_
    rw [Category.assoc, Iso.inv_hom_id_assoc, hj]
    exact hgcl
  · rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hj, hgq]

end AlgebraicGeometry.Space

end
