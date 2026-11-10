module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectEtaleLocalSliceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedKoszulGenerator
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal

/-!
# A perfect generator supported off a quasi-compact open of an affine algebraic space

Let `V` be an affine algebraic space over `S` and `i : Y ⟶ V` an open immersion with `Y`
quasi-compact. There is a perfect object `K` of `D(𝒪_V)` with `K|_Y = 0` such that an object `E`
of `D_QCoh(𝒪_V)` with `E|_Y = 0` and `Hom(K[n], E) = 0` for all `n ∈ ℤ` is zero.

This is the affine input of the proofs of Stacks 09IY and 0AEC: in the source it is
Derived Categories of Schemes, Lemma 36.15.2 (Stacks 09IR) read on `D_QCoh(𝒪_V)` through
Lemma 75.4.2 (Stacks 071Q). The case of the algebraic space represented by `Spec A` is
`AlgebraicGeometry.Space.isPerfect_representedDerivedAssociatedModule_koszulObject`,
`AlgebraicGeometry.Space.isZero_representedDerivedPullback_koszulObject` and
`AlgebraicGeometry.Space.isZero_of_forall_hom_representedKoszulObject_eq_zero`; this file moves it
along an isomorphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isZero_mapDerivedCategory_etaleModulePullback_iff`: an étale pullback
  of a derived object vanishes exactly when the étale pullbacks of its cohomology sheaves do.
* `AlgebraicGeometry.Space.exists_supportedGenerator_of_iso`: the generator moves along an
  isomorphism of algebraic spaces.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- **An étale pullback of a derived object vanishes exactly when the étale pullbacks of its
cohomology sheaves do**: étale pullback is exact and so commutes with cohomology. -/
theorem isZero_mapDerivedCategory_etaleModulePullback_iff {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    IsZero ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.obj E) ↔
      ∀ n : ℤ, IsZero ((etaleModulePullback.{u, u} B S hS f hf).obj
        ((DerivedCategory.homologyFunctor _ n).obj E)) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine forall_congr' fun n => ⟨fun h => h.of_iso ?_, fun h => h.of_iso ?_⟩
  · exact (((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategoryHomologyIso n).app E).symm
  · exact ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategoryHomologyIso n).app E

/-- Étale pullback along the two sides of a commutative square of étale morphisms agree. -/
def etaleModulePullbackSquareIso {X Y Y' Z : AlgebraicSpaces B S hS} {a : X ⟶ Y} {b : Y ⟶ Z}
    {c : X ⟶ Y'} {d : Y' ⟶ Z} (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom)
    (hc : IsEtale B S hS c.hom) (hd : IsEtale B S hS d.hom) (h : a ≫ b = c ≫ d) :
    etaleModulePullback.{u, u} B S hS b hb ⋙ etaleModulePullback.{u, u} B S hS a ha ≅
      etaleModulePullback.{u, u} B S hS d hd ⋙ etaleModulePullback.{u, u} B S hS c hc :=
  etaleModulePullbackCompIso B S hS a b ha hb (isEtale_comp B S hS ha hb) ≪≫
    eqToIso (etaleModulePullback_congr B S hS _ (isEtale_comp B S hS hc hd) h) ≪≫
    (etaleModulePullbackCompIso B S hS c d hc hd (isEtale_comp B S hS hc hd)).symm

/-- If `a ≫ b = c ≫ d` is a square of étale morphisms and the `d`-pullback of a derived object
vanishes, then so does its pullback along `b` and then `a`. -/
private theorem isZero_mapDerivedCategory_etaleModulePullback_comp_of_square
    {X Y Y' Z : AlgebraicSpaces B S hS} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Y'} {d : Y' ⟶ Z}
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hc : IsEtale B S hS c.hom)
    (hd : IsEtale B S hS d.hom) (h : a ≫ b = c ≫ d)
    (E : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (hE : IsZero ((etaleModulePullback.{u, u} B S hS d hd).mapDerivedCategory.obj E)) :
    IsZero ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategory.obj
      ((etaleModulePullback.{u, u} B S hS b hb).mapDerivedCategory.obj E)) := by
  rw [isZero_mapDerivedCategory_etaleModulePullback_iff] at hE ⊢
  intro n
  exact IsZero.of_iso ((etaleModulePullback.{u, u} B S hS c hc).map_isZero (hE n))
    (((etaleModulePullback.{u, u} B S hS a ha).mapIso
      (((etaleModulePullback.{u, u} B S hS b hb).mapDerivedCategoryHomologyIso n).app E)) ≪≫
      (etaleModulePullbackSquareIso B S hS ha hb hc hd h).app
        ((DerivedCategory.homologyFunctor _ n).obj E))

/-- An étale pullback along an isomorphism of algebraic spaces reflects zero objects. -/
theorem isZero_of_isZero_etaleModulePullback_iso {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2)
    (h : IsZero ((etaleModulePullback.{u, u} B S hS e.hom (isEtale_hom_of_iso B S hS e)).obj M)) :
    IsZero M :=
  IsZero.of_iso ((etaleModulePullbackEquivalenceOfIso.{u, u} B S hS e).inverse.map_isZero h)
    ((etaleModulePullbackEquivalenceOfIso.{u, u} B S hS e).unitIso.app M)

/-- **The supported perfect generator moves along an isomorphism of algebraic spaces.** Let
`r : W ≅ V` and `s : Y' ≅ Y` be isomorphisms of algebraic spaces and `i' : Y' ⟶ W`, `i : Y ⟶ V`
étale morphisms with `s ≫ i = i' ≫ r`. If `K'` is a perfect object of `D(𝒪_W)` with `K'|_{Y'} = 0`
which generates the objects of `D_QCoh(𝒪_W)` vanishing on `Y'`, then `V` carries an object with
the same three properties relative to `Y`. -/
theorem exists_supportedGenerator_of_iso {W V Y' Y : AlgebraicSpaces B S hS} (r : W ≅ V)
    (s : Y' ≅ Y) (i' : Y' ⟶ W) (i : Y ⟶ V) (hi' : IsEtale B S hS i'.hom)
    (hi : IsEtale B S hS i.hom) (hsq : s.hom ≫ i = i' ≫ r.hom)
    (K' : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hK'perf : (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect K')
    (hK'Y : IsZero ((etaleModulePullback.{u, u} B S hS i' hi').mapDerivedCategory.obj K'))
    (hK'gen : ∀ E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2), qcohDerivedProp B S hS W E →
      IsZero ((etaleModulePullback.{u, u} B S hS i' hi').mapDerivedCategory.obj E) →
      (∀ (n : ℤ) (g : K'⟦n⟧ ⟶ E), g = 0) → IsZero E) :
    ∃ K : DerivedCategory (Modules.{u, u} B S hS V.1 V.2),
      (smallEtaleRingedSite B S hS V.1 V.2).IsPerfect K ∧
      IsZero ((etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategory.obj K) ∧
      ∀ E : DerivedCategory (Modules.{u, u} B S hS V.1 V.2), qcohDerivedProp B S hS V E →
        IsZero ((etaleModulePullback.{u, u} B S hS i hi).mapDerivedCategory.obj E) →
        (∀ (n : ℤ) (g : K⟦n⟧ ⟶ E), g = 0) → IsZero E := by
  have hr := isEtale_hom_of_iso B S hS r
  have hr' := isEtale_hom_of_iso B S hS r.symm
  have hs := isEtale_hom_of_iso B S hS s
  have hs' := isEtale_hom_of_iso B S hS s.symm
  have : (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS r).functor.Additive :=
    etaleModulePullback_additive B S hS r.hom hr
  have : PreservesFiniteLimits
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS r).functor :=
    preservesFiniteLimits_etaleModulePullback B S hS r.hom hr
  have : PreservesFiniteColimits
      (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS r).functor :=
    preservesFiniteColimits_etaleModulePullback B S hS r.hom hr
  let Φ := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS r)
  -- `Φ.functor = r.hom^*`, `Φ.inverse = r.inv^*`.
  let K := (etaleModulePullback.{u, u} B S hS r.inv hr').mapDerivedCategory.obj K'
  have hΦK : Φ.inverse.obj K' = K := rfl
  have : Φ.functor.PreservesZeroMorphisms := by
    change ((etaleModulePullback.{u, u} B S hS r.hom hr).mapDerivedCategory).PreservesZeroMorphisms
    infer_instance
  have : Φ.inverse.PreservesZeroMorphisms := by
    change ((etaleModulePullback.{u, u} B S hS r.inv hr').mapDerivedCategory).PreservesZeroMorphisms
    infer_instance
  have hsq' : i ≫ r.inv = s.inv ≫ i' := by
    rw [← cancel_epi s.hom, ← Category.assoc, hsq, Category.assoc, r.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  have hsq'' : i' ≫ r.hom = s.hom ≫ i := hsq.symm
  refine ⟨K, ?_, ?_, ?_⟩
  · exact isPerfect_etaleModulePullback_standard B S hS r.inv hr' K' hK'perf
  · exact isZero_mapDerivedCategory_etaleModulePullback_comp_of_square B S hS hi hr' hs' hi' hsq' K'
      hK'Y
  · intro E hE hEY hEK
    let E' := (etaleModulePullback.{u, u} B S hS r.hom hr).mapDerivedCategory.obj E
    have hΦE : Φ.functor.obj E = E' := rfl
    have hE' : qcohDerivedProp B S hS W E' := fun n =>
      SheafOfModules.IsQuasicoherentOnSite.of_iso
        (((etaleModulePullback.{u, u} B S hS r.hom hr).mapDerivedCategoryHomologyIso n).app E).symm
        (isQuasicoherentOnSite_etaleModulePullback B S hS r.hom hr _ (hE n))
    have hE'Y := isZero_mapDerivedCategory_etaleModulePullback_comp_of_square B S hS hi' hr hs hi
      hsq'' E hEY
    have hE'K : ∀ (n : ℤ) (g : K'⟦n⟧ ⟶ E'), g = 0 := by
      intro n g
      have : Φ.functor.CommShift ℤ := by
        change ((etaleModulePullback.{u, u} B S hS r.hom hr).mapDerivedCategory).CommShift ℤ
        infer_instance
      let α : K'⟦n⟧ ≅ Φ.functor.obj (K⟦n⟧) :=
        (shiftFunctor _ n).mapIso (eqToIso (congrArg Φ.functor.obj hΦK.symm) ≪≫
          Φ.counitIso.app K').symm ≪≫
          ((Φ.functor.commShiftIso n).app K).symm
      have hz : α.inv ≫ g ≫ eqToHom hΦE.symm = 0 := by
        simpa only [Functor.FullyFaithful.map_preimage, Functor.map_zero] using
          congrArg Φ.functor.map
            (hEK n (Φ.fullyFaithfulFunctor.preimage (α.inv ≫ g ≫ eqToHom hΦE.symm)))
      exact eq_zero_of_iso_comp_comp_iso_eq_zero α.symm g (eqToIso hΦE.symm) hz
    exact IsZero.of_iso (Φ.inverse.map_isZero (hΦE ▸ hK'gen E' hE' hE'Y hE'K)) (Φ.unitIso.app E)

/-- **The object of the big fppf site with scheme `Spec Γ(T)`.** An object `T` of the big fppf
site with affine underlying scheme is isomorphic to the object whose underlying scheme is
literally `Spec Γ(T, 𝒪_T)`. -/
theorem exists_iso_mk_spec (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    ∃ (A : Type u) (_ : CommRing A) (hA : B.Contains (Spec (CommRingCat.of A)))
      (p : Spec (CommRingCat.of A) ⟶ S), Nonempty (T ≅ BigFppfOver.mk B S hS hA p) := by
  let X := (BigFppfOver.toScheme B S hS).obj T
  let e : X ≅ Spec (CommRingCat.of Γ(X, ⊤)) := X.isoSpec
  have hA : B.Contains (Spec (CommRingCat.of Γ(X, ⊤))) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact e.inv) T.left.property
  let p : Spec (CommRingCat.of Γ(X, ⊤)) ⟶ S := e.inv ≫ B.inclusion.map T.hom
  refine ⟨Γ(X, ⊤), inferInstance, hA, p, ⟨?_⟩⟩
  let f : T ⟶ BigFppfOver.mk B S hS hA p :=
    BigFppfOver.homMk B S hS hA p e.hom (by simp [p])
  have : IsIso ((BigFppfOver.toScheme B S hS).map f) := by
    rw [BigFppfOver.toScheme_map_homMk]
    exact Iso.isIso_hom e
  have : IsIso f := isIso_of_reflects_iso f (BigFppfOver.toScheme B S hS)
  exact asIso f

variable {B S hS} in
/-- **The supported perfect generator on an affine algebraic space.** Let `V` be an affine
algebraic space over `S` and `i : Y ⟶ V` an open immersion with `Y` quasi-compact. There is a
perfect object `K` of `D(𝒪_V)` with `K|_Y = 0` such that an object of `D_QCoh(𝒪_V)` vanishing on
`Y` and receiving only zero maps from the shifts of `K` is zero.

This is the affine input of Stacks 09IY and 0AEC: Derived Categories of Schemes, Lemma 36.15.2
(Stacks 09IR) on `V`, read on `D_QCoh(𝒪_V)` through Stacks 071Q. With `V = h_{Spec A}` and `Y` the
open `⋃ D(f_i)` the generator is the pullback of the Koszul complex on `f₁, …, f_r`
(`AlgebraicGeometry.Space.isZero_of_forall_hom_representedKoszulObject_eq_zero`); the general
case is moved there along isomorphisms. -/
theorem exists_isPerfect_isZero_restrict_generator_of_isAffineSpace {V Y : AlgebraicSpaces B S hS}
    (hV : IsAffineSpace B S hS V.1) (i : Y ⟶ V) (hi : IsOpenImmersion B S hS i.hom)
    (hY : IsQuasiCompactSpace B S hS Y.1) :
    ∃ K : DerivedCategory (Modules.{u, u} B S hS V.1 V.2),
      (smallEtaleRingedSite B S hS V.1 V.2).IsPerfect K ∧
      IsZero ((etaleModulePullback.{u, u} B S hS i
        (isEtale_of_isOpenImmersion B S hS hi)).mapDerivedCategory.obj K) ∧
      ∀ E : DerivedCategory (Modules.{u, u} B S hS V.1 V.2), qcohDerivedProp B S hS V E →
        IsZero ((etaleModulePullback.{u, u} B S hS i
          (isEtale_of_isOpenImmersion B S hS hi)).mapDerivedCategory.obj E) →
        (∀ (n : ℤ) (g : K⟦n⟧ ⟶ E), g = 0) → IsZero E := by
  obtain ⟨T, hT, ⟨eV⟩⟩ := hV
  obtain ⟨A, _, hA, p, ⟨eT⟩⟩ := exists_iso_mk_spec B S hS T hT
  let T₀ := BigFppfOver.mk B S hS hA p
  let W : AlgebraicSpaces B S hS := ⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩
  let r : W ≅ V := ObjectProperty.isoMk _ ((yoneda.mapIso eT).symm ≪≫ eV.symm)
  -- The open immersion `Y ⟶ V ≅ h_{T₀}` is represented by an open immersion `T' ⟶ T₀`.
  have hi₀ : IsOpenImmersion B S hS (i ≫ r.inv).hom :=
    isOpenImmersion_comp B S hS i.hom r.inv.hom hi (isOpenImmersion_of_isIso B S hS r.inv.hom)
  have hpb := hi₀.rep.isPullback (𝟙 (yoneda.obj T₀))
  have : IsIso (hi₀.rep.fst (𝟙 (yoneda.obj T₀))) := hpb.isIso_fst_of_isIso
  let T' := hi₀.rep.pullback (𝟙 (yoneda.obj T₀))
  let j : T' ⟶ T₀ := hi₀.rep.snd (𝟙 (yoneda.obj T₀))
  have hjo : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) :=
    hi₀.property_snd (𝟙 (yoneda.obj T₀))
  let s : (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ≅ Y :=
    ObjectProperty.isoMk _ (asIso (hi₀.rep.fst (𝟙 (yoneda.obj T₀))))
  have hsq : s.hom ≫ i = representedSpaceMap B S hS j ≫ r.hom := by
    apply ObjectProperty.hom_ext
    have hw := hpb.w
    simp only [Category.comp_id] at hw
    change hi₀.rep.fst (𝟙 (yoneda.obj T₀)) ≫ i.hom = yoneda.map j ≫ r.hom.hom
    rw [← hw]
    change hi₀.rep.fst (𝟙 (yoneda.obj T₀)) ≫ i.hom =
      hi₀.rep.fst (𝟙 (yoneda.obj T₀)) ≫ (i.hom ≫ r.inv.hom) ≫ r.hom.hom
    rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, r.inv_hom_id]
    rfl
  have hj : IsEtale B S hS (representedSpaceMap B S hS j).hom :=
    isEtale_of_presheaf_etale B S hS
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) j).2 inferInstance)
  -- The image of `T'` is a quasi-compact open `⋃ D(f_i)` of `Spec A`.
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj T') :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS (IsQuasiCompactSpace.of_iso B S hS hY
      (asIso (hi₀.rep.fst (𝟙 (yoneda.obj T₀)))).symm)
  have hopen : IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map j).base) :=
    ((BigFppfOver.toScheme B S hS).map j).isOpenEmbedding.isOpen_range
  have hcpt : IsCompact (Set.range ((BigFppfOver.toScheme B S hS).map j).base)ᶜᶜ := by
    rw [compl_compl]
    exact isCompact_range ((BigFppfOver.toScheme B S hS).map j).continuous
  obtain ⟨r', f, hf⟩ := Stacks.Duality.Supported.exists_coe_openComplement_eq_compl
    (A := A) (Set.range ((BigFppfOver.toScheme B S hS).map j).base)ᶜ hopen.isClosed_compl hcpt
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map j).base =
      (Stacks.Koszul.Truncation.openComplement f : Set (Spec (CommRingCat.of A))) := by
    rw [hf, compl_compl]
    rfl
  exact exists_supportedGenerator_of_iso B S hS r s (representedSpaceMap B S hS j) i hj _ hsq
    ((representedDerivedAssociatedModule B S hS T₀).obj (Stacks.Koszul.Truncation.koszulObject f))
    (isPerfect_representedDerivedAssociatedModule_koszulObject B S hS hA p f)
    (isZero_representedDerivedPullback_koszulObject B S hS f j hj hrange)
    (isZero_of_forall_hom_representedKoszulObject_eq_zero B S hS f j hj hrange)

end AlgebraicGeometry.Space

end
